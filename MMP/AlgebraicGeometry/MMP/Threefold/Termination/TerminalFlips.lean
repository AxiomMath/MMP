module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Termination.Defs
import MMP.AlgebraicGeometry.Singularities.Terminal.CodimTwoDiscrepancyCriterion
import MMP.AlgebraicGeometry.Singularities.PairClasses
public import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.MMP.MinimalModel.LogCanonicalModelDefs
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolutionExists
import MMP.AlgebraicGeometry.Singularities.Surface.SingularPointMldBound
import MMP.AlgebraicGeometry.Singularities.GenericSurfacePlaces
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.SNC
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
import MMP.AlgebraicGeometry.Cohomology.Duality.AdjunctionSequence
import MMP.AlgebraicGeometry.MMP.Flip.FlipPreservesCanonical
import MMP.AlgebraicGeometry.MMP.Flip.FlippedCurveDiscrepancy
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Contraction.SmallContractionBasics
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.SzaboDifficultyFinite
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.SzaboSetShrinks
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.NoFlippingCurveInDivisor
import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
import MMP.AlgebraicGeometry.Divisor.Principal
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.AlgebraicGeometry.MMP.Basic
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipBoundaryTransform
import MMP.AlgebraicGeometry.MMP.Flip.Defs
import MMP.AlgebraicGeometry.Positivity.RelativelyAmplePullbackIso
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.Singularities.Slc.NodeResidueForm
import MMP.AlgebraicGeometry.MMP.Fourfold.GenericValuation
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import MMP.AlgebraicGeometry.Resolution.Basic
import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
import MMP.AlgebraicGeometry.Divisor.Basic
import MMP.AlgebraicGeometry.Resolution.Blowup
import MMP.AlgebraicGeometry.MMP.Abundance.Defs
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldGraphDivisor
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatPullback
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.Morphisms.Birational.IsoInCodimOne
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafCoherent
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Positivity.AmpleTwistRealPerturbation
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import MMP.AlgebraicGeometry.Resolution.Surface.CastelnuovoContraction
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
import MMP.AlgebraicGeometry.Resolution.CommonNormalModel
import MMP.AlgebraicGeometry.Singularities.KltSmallDiscrepancyCenters
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

/-!
# Termination of flips for terminal threefold pairs

A terminal pair `(Y, D)` is canonical with `⌊D⌋ = 0`, so termination of its flips is Szabó's
termination theorem for canonical threefold pairs (FA 4.14), which needs no `ℚ`-factoriality.
This file proves that theorem over an arbitrary field of characteristic zero.

The argument runs as follows. The generic point of a flipped curve `C` has a regular local ring,
because every exceptional divisor with centre `C` has positive discrepancy. The exceptional
divisor of the blow-up of `C` then has discrepancy `1 - mult_C D⁺`. This divisor is counted in
Szabó's modified difficulty `d_{N,c}(X, D; B)` on `X` but not on `X⁺`, so the difficulty drops
whenever a flipped curve has `c = 0` or lies in a component of coefficient `≥ c`. A descending
induction on the coefficients of `D` shows that eventually no flipping curve lies in a component
of positive coefficient. Taking `c = 0`, eventually there is no flipped curve, and that
contradicts the existence of a nontrivial flip.

## Main results

* `MMP.Flips.SequenceOfFlips.terminates_of_isTerminalPair`: flips of a terminal threefold pair
  terminate. It is deduced from Szabó's theorem for canonical threefold pairs with `⌊D⌋ = 0`
  (FA 4.14), proved here as a private lemma.

## Implementation notes

The ground field is an arbitrary field `k` of characteristic zero rather than `ℂ`; the termination
theorem the proof rests on holds in that generality. The threefold condition is
`topologicalKrullDim Y = 3`, and the canonical divisor `K` is taken of dimension `3`.

The regularity of codimension-two points with positive discrepancies and the finiteness of
Szabó's difficulty are proved here over a field of characteristic zero, using the discrepancy of
the blow-up of a generically regular centre,
`MMP.Mori.isDiscrepancy_blowUp_of_isRegularLocalRing_of_charZero`. No algebraic closedness is
assumed: the generic surface at a codimension-two point lives over a purely transcendental
extension of `k`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.14, 6.9.1.2
-/

universe u

namespace MMP.Mori.Sec24BlowUp

section BlowUp

open CategoryTheory TopologicalSpace
open AlgebraicGeometry hiding IsVariety
open scoped WithZero

/-! ### Smooth loci and blow-up centres -/

/-- Over a perfect field, the smooth points are the points with regular local ring. -/
private theorem mem_smoothLocus_iff_isRegularLocalRing {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] (y : Y) :
    y ∈ smoothLocus s ↔ IsRegularLocalRing (Y.presheaf.stalk y) := by
  rw [MMP.Mori.mem_smoothLocus_iff, ← InfinitesimalLifting.smoothAt_iff_exists_open_smooth_comp]
  exact Set.ext_iff.mp (AlgebraicGeometry.smoothAt_locus_eq_regular_locus k s) y

/-- Over a perfect field, a scheme is smooth when all its local rings are regular. -/
private theorem isSmoothScheme_of_forall_isRegularLocalRing {k : Type u} [Field k]
    [PerfectField k] {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (h : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) : IsSmoothScheme s :=
  eq_top_iff.mpr fun y _ => (mem_smoothLocus_iff_isRegularLocalRing s y).mpr (h y)

/-- **A neighbourhood of `η_Z` in which `Z` is smooth.** If `X` is a variety over a perfect
field, `Z ⊆ X` an irreducible closed subset with generic point `x` and `𝒪_{X,x}` regular, there
is an open `U ∋ x` such that `U` and `Z ∩ U` (with the inverse image of the reduced structure of
`Z`) are smooth over `k`, and `Z ∩ U` has generic point `x` and codimension `coheight x`. -/
private theorem exists_smoothBlowup {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX) (V : IrreducibleCloseds X) (x : X)
    (hx : x = V.isIrreducible.genericPoint)
    (hreg : IsRegularLocalRing (X.presheaf.stalk x)) :
    ∃ (U : X.Opens) (_ : x ∈ U)
      (_ : MMP.Resolution.IsSmoothBlowup (U.ι ≫ sX)
        ((Scheme.IdealSheafData.vanishingIdeal (⟨V, V.isClosed⟩ : Closeds X)).comap U.ι))
      (hirr : IsIrreducible (((Scheme.IdealSheafData.vanishingIdeal
        (⟨V, V.isClosed⟩ : Closeds X)).comap U.ι).support : Set U)),
      U.ι hirr.genericPoint = x ∧
        codimension (⟨_, hirr, ((Scheme.IdealSheafData.vanishingIdeal
          (⟨V, V.isClosed⟩ : Closeds X)).comap U.ι).support.isClosed⟩ : IrreducibleCloseds U) =
          Order.coheight x := by
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  set Z := Scheme.IdealSheafData.vanishingIdeal (⟨V, V.isClosed⟩ : Closeds X) with hZ
  have hZsupp : (Z.support : Set X) = V := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have : IsIntegral Z.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ V.isIrreducible
  set ζ := genericPoint Z.subscheme with hζ
  have hζx : Z.subschemeι ζ = x := by
    have h1 : IsGenericPoint (Z.subschemeι ζ) (V : Set X) := by
      change closure _ = _
      rw [MMP.Resolution.closure_subschemeι_genericPoint, hZsupp]
    have h2 : IsGenericPoint V.isIrreducible.genericPoint (V : Set X) := by
      have := V.isIrreducible.isGenericPoint_genericPoint_closure
      rwa [V.isClosed.closure_eq] at this
    rw [hx]; exact h1.eq h2
  set S := smoothLocus (Z.subschemeι ≫ sX) with hS
  have hζreg : IsRegularLocalRing Z.subscheme.functionField := inferInstance
  have hζS : ζ ∈ S := (mem_smoothLocus_iff_isRegularLocalRing _ ζ).mpr hζreg
  set T : Set X := Z.subschemeι '' (S : Set Z.subscheme)ᶜ with hT
  have hTc : IsClosed T :=
    Z.subschemeι.isClosedEmbedding.isClosedMap _ S.isOpen.isClosed_compl
  have hxT : x ∉ T := by
    rintro ⟨z, hz, hzx⟩
    rw [← hζx] at hzx
    exact hz (Z.subschemeι.isClosedEmbedding.injective hzx ▸ hζS)
  set R := smoothLocus sX with hR
  have hxR : x ∈ R := (mem_smoothLocus_iff_isRegularLocalRing sX x).mpr hreg
  set U : X.Opens := R ⊓ ⟨Tᶜ, hTc.isOpen_compl⟩ with hU
  have hxU : x ∈ U := ⟨hxR, hxT⟩
  set I := Z.comap U.ι with hI
  have hIsupp : (I.support : Set U) = U.ι ⁻¹' V := by
    rw [hI, Scheme.IdealSheafData.support_comap]
    change U.ι ⁻¹' (Z.support : Set X) = _
    rw [hZsupp]
  have hUsm : IsSmoothScheme (U.ι ≫ sX) :=
    isSmoothScheme_of_forall_isRegularLocalRing _ fun u =>
      isRegularLocalRing_of_isOpenImmersion U.ι u
        ((mem_smoothLocus_iff_isRegularLocalRing sX _).mp u.2.1)
  have e : I.subschemeι ≫ U.ι = (Z.comapIso U.ι).hom ≫
      Limits.pullback.snd U.ι Z.subschemeι ≫ Z.subschemeι := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Limits.pullback.condition]
  have hIsm : IsSmoothScheme (I.subschemeι ≫ U.ι ≫ sX) := by
    refine isSmoothScheme_of_forall_isRegularLocalRing _ fun y => ?_
    set j := (Z.comapIso U.ι).hom ≫ Limits.pullback.snd U.ι Z.subschemeι with hj
    have hjy : Z.subschemeι (j y) = U.ι (I.subschemeι y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hj, Category.assoc, ← e]
    refine isRegularLocalRing_of_isOpenImmersion j y
      ((mem_smoothLocus_iff_isRegularLocalRing (Z.subschemeι ≫ sX) _).mp ?_)
    by_contra hns
    exact (I.subschemeι y).2.2 ⟨j y, hns, hjy⟩
  have hxgen : IsGenericPoint x (V : Set X) := by
    have := V.isIrreducible.isGenericPoint_genericPoint_closure
    rwa [V.isClosed.closure_eq, ← hx] at this
  let xU : U.toScheme := ⟨x, hxU⟩
  have hxU' : U.ι xU = x := rfl
  have hpre' : IsGenericPoint xU (I.support : Set U.toScheme) := by
    rw [isGenericPoint_iff_specializes]
    intro y
    rw [← U.ι.isOpenEmbedding.isInducing.specializes_iff, hxU', hxgen.specializes_iff_mem]
    change _ ↔ y ∈ (I.support : Set U.toScheme)
    rw [hIsupp]
    rfl
  have hirr : IsIrreducible (I.support : Set U.toScheme) := hpre'.isIrreducible
  have hgen : hirr.genericPoint = xU := by
    have h1 := hirr.isGenericPoint_genericPoint_closure
    rw [I.support.isClosed.closure_eq] at h1
    exact h1.eq hpre'
  refine ⟨U, hxU, ⟨hUsm, hIsm⟩, hirr, by rw [hgen]; rfl, ?_⟩
  have hcl : (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds U.toScheme) =
      IrreducibleCloseds.closureSingleton xU := by
    ext1
    exact hpre'.symm
  rw [hcl, MMP.Flips.codimension_closureSingleton]
  exact (coheight_eq_of_isOpenImmersion U.ι (x := xU)).symm

/-- Membership in powers of the maximal ideal is read through an isomorphism of local rings. -/
private theorem mem_maximalIdeal_pow_iff_of_bijective {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (a : R) :
    e a ∈ IsLocalRing.maximalIdeal S ^ n ↔ a ∈ IsLocalRing.maximalIdeal R ^ n := by
  have hm : Ideal.map e (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  rw [← hm, ← Ideal.map_pow, Ideal.mem_map_of_equiv]
  exact ⟨fun ⟨b, hb, hba⟩ => e.injective hba ▸ hb, fun ha => ⟨a, ha, rfl⟩⟩

/-- A birational morphism is an open immersion on a dense open. -/
private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{u}}
    {f : X ⟶ Y} (hf : IsBirationalMorphism f) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsOpenImmersion (U.ι ≫ f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  refine ⟨W, hW, ?_⟩
  have : W.ι ≫ f = X.homOfLE hWf ≫ f.toPartialMap.hom := by
    change W.ι ≫ f = (X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom) ≫ f
    simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
  rw [this, ← h]
  infer_instance

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsBirationalMorphism f := by
  have hd : Dense ((U.ι ≫ f).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  let e : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := (U.ι ≫ f).opensRange
      dense_target := hd
      iso := (U.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

end BlowUp

end MMP.Mori.Sec24BlowUp

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

namespace MMP.Mori.TerminalCodimTwo

open MMP MMP.Mori

section BlowUp

open Topology
open MMP.Flips (maximalIdealOrder maximalIdealOrder_spec)
open MMP.Mori.Sec24BlowUp

/-- **The exceptional divisor of the blow-up of a smooth neighbourhood of `η_V`.** Let `Y` be a
normal variety over a perfect field and `V ⊆ Y` an irreducible closed subset of codimension
`≥ 2` with generic point `x` and `𝒪_{Y,x}` regular. On a neighbourhood `U` of `x` on which `Y` and
`V` are smooth, the exceptional prime `F` of `Bl_{V ∩ U} U` is a divisor over `Y`; its model is
an open subscheme of `Bl_V Y` containing every point over `x`, `F` is the only prime of the model
over `x`, and its valuation is the order function of `𝒪_{Y,x}`. -/
public theorem exists_divisorOver_smoothBlowup {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} [IsIntegral Y] {s : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k s)
    (V : IrreducibleCloseds Y) (hV : 2 ≤ codimension V) (x : Y)
    (hx : x = V.isIrreducible.genericPoint) (hreg : IsRegularLocalRing (Y.presheaf.stalk x)) :
    ∃ (D : DivisorOver k s) (h : D.Y ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal
        (⟨V, V.isClosed⟩ : Closeds Y))),
      IsOpenImmersion h ∧ h ≫ blowUpToBase _ = D.f ∧ D.f D.E.genericPoint = x ∧
      (∀ b, blowUpToBase _ b = x → b ∈ Set.range h) ∧
      (∀ a : D.Y, D.f a = x → Order.coheight a = 1 → a = D.E.genericPoint) ∧
      ∀ g : Y.presheaf.stalk x, g ≠ 0 →
        D.valuation (algebraMap _ Y.functionField g) =
          WithZero.exp (-(maximalIdealOrder _ g : ℤ)) := by
  have : LocallyOfFiniteType s := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  set Z := Scheme.IdealSheafData.vanishingIdeal (⟨V, V.isClosed⟩ : Closeds Y) with hZ
  obtain ⟨U, hxU, hsb, hirr, hgen, hcod⟩ := exists_smoothBlowup hY.1 V x hx hreg
  set I := Z.comap U.ι with hI
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨x, hxU⟩)
  have hUnv := isNormalVariety_ι hY U
  have : LocallyOfFiniteType (U.ι ≫ s) := hUnv.1.toLocallyOfFiniteType
  -- the codimension `c` of the centre
  have hcx : codimension V = Order.coheight x := by
    rw [Flips.codimension_eq_coheight_genericPoint, hx]
  have hfin : Order.coheight x ≠ ⊤ := by
    have h1 := ringKrullDim_stalk_eq_coheight x
    have h2 := ringKrullDim_lt_top (R := Y.presheaf.stalk x)
    intro htop
    rw [h1, htop] at h2
    exact lt_irrefl _ h2
  set c := (Order.coheight x).toNat with hcdef
  have hcc : (c : ℕ∞) = Order.coheight x := by rw [hcdef, ENat.coe_toNat hfin]
  have hc : (c : ℕ∞) =
      codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds U) := by
    rw [hcod, hcc]
  have hc2 : 2 ≤ c := by
    have : ((2 : ℕ) : ℕ∞) ≤ (c : ℕ∞) := by rwa [hcc, ← hcx]
    exact_mod_cast this
  have hc1 : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds U) := by
    rw [← hc]; exact_mod_cast (by omega : 1 ≤ c)
  -- the dimension of `U`
  have : QuasiCompact (U.ι ≫ s) := hUnv.1.toQuasiCompact
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ s)
  have : Nonempty (IrreducibleCloseds U) := ⟨IrreducibleCloseds.closureSingleton ⟨x, hxU⟩⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, topologicalKrullDim U = n := by
    have h1 := AlgebraicGeometry.topologicalKrullDim_ne_top_of_locallyOfFiniteType k (U.ι ≫ s)
    have h2 : topologicalKrullDim U ≠ ⊥ := by
      intro h0
      have := Order.krullDim_nonneg (α := IrreducibleCloseds U)
      exact absurd (h0 ▸ this : (0 : WithBot ℕ∞) ≤ ⊥) (by simp)
    generalize topologicalKrullDim U = d at h1 h2
    induction d using WithBot.recBotCoe with
    | bot => exact absurd rfl h2
    | coe d =>
      induction d using ENat.recTopCoe with
      | top => exact absurd rfl h1
      | coe d => exact ⟨d, rfl⟩
  obtain ⟨hvarB, hsmB, -, hbirπ, -⟩ :=
    MMP.Threefold.Resolution.isVariety_smooth_blowUpToBase_divisorOfForm_pullbackRationalPluriForms
      (U.ι ≫ s) hUnv.1 hn I hsb hirr hc hc2
  obtain ⟨hordE, -⟩ :=
    MMP.Threefold.Resolution.ord_exceptionalPrimeDivisor_pullback_and_ordForm_pullback
      (U.ι ≫ s) hUnv.1 I hsb hirr hc hc2 hn
  set π := blowUpToBase I with hπ
  have : IsIntegral (blowUp I) :=
    MMP.Threefold.Resolution.isIntegral_blowUp_of_one_le_codimension I hirr hc1
  have : IsDominant π := MMP.Threefold.Resolution.isDominant_blowUpToBase I hirr hc1
  have : LocallyOfFiniteType (π ≫ U.ι ≫ s) := hvarB.toLocallyOfFiniteType
  have : IsLocallyNoetherian (blowUp I) := LocallyOfFiniteType.isLocallyNoetherian (π ≫ U.ι ≫ s)
  have : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  have := hsmB
  have : IsNormal (blowUp I) := AlgebraicGeometry.isNormal_of_smooth (π ≫ U.ι ≫ s)
  have : IsDominant (π ≫ U.ι) := inferInstance
  set Eex := MMP.Resolution.exceptionalPrimeDivisor (U.ι ≫ s) I hsb hirr hc1 with hEex
  have hnv : IsNormalVariety k ((π ≫ U.ι) ≫ s) := by
    rw [Category.assoc]; exact ⟨hvarB, inferInstance⟩
  have hbir : IsBirationalMorphism (π ≫ U.ι) := by
    obtain ⟨O, hO, hOi⟩ := exists_isOpenImmersion_of_isBirationalMorphism hbirπ
    have : IsOpenImmersion (O.ι ≫ π ≫ U.ι) := by
      rw [← Category.assoc]; infer_instance
    exact isBirationalMorphism_of_isOpenImmersion (π ≫ U.ι) O hO
  let D : DivisorOver k s := ⟨blowUp I, π ≫ U.ι, hnv, hbir, Eex⟩
  -- the generic point of `F` lies over `x`
  obtain ⟨-, F', hF'id, -, hFimg⟩ :=
    MMP.Resolution.isSmoothScheme_blowUp_and_exists_primeDivisor_exceptionalIdeal (U.ι ≫ s) I hsb
      hirr hc1
  have hsuppF : Eex.support = ((exceptionalIdeal I).support : Set (blowUp I)) := rfl
  have hsuppF' : F'.support = ((exceptionalIdeal I).support : Set (blowUp I)) := by
    simp only [AlgebraicGeometry.PrimeDivisor.support, hF'id]
  have hgenπ : IsGenericPoint (π Eex.genericPoint) (I.support : Set U) := by
    change closure {π _} = _
    rw [← Set.image_singleton, π.isClosedMap.closure_image_eq_of_continuous π.continuous,
      ← AlgebraicGeometry.PrimeDivisor.support_eq_closure, hsuppF, ← hsuppF', hFimg]
  have hgenI : IsGenericPoint hirr.genericPoint (I.support : Set U) :=
    hirr.isGenericPoint_genericPoint_closure.trans I.support.isClosed.closure_eq
  have hπη : π Eex.genericPoint = hirr.genericPoint := hgenπ.eq hgenI
  have hDf : D.f D.E.genericPoint = x := by
    change U.ι (π Eex.genericPoint) = x
    rw [hπη]
    exact hgen
  -- the model is an open of `Bl_V Y`
  obtain ⟨h, hP⟩ := AlgebraicGeometry.exists_isPullback_blowUpToBase_comap U.ι Z
  have hh : IsOpenImmersion h := by
    rw [← hP.isoPullback_hom_snd]
    infer_instance
  have hrange : ∀ b, blowUpToBase Z b = x → b ∈ Set.range h := by
    intro b hb
    have hb' : b ∈ Set.range (Limits.pullback.snd U.ι (blowUpToBase Z)) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      change blowUpToBase Z b ∈ Set.range U.ι
      rw [hb]
      exact ⟨⟨x, hxU⟩, rfl⟩
    obtain ⟨p, rfl⟩ := hb'
    refine ⟨hP.isoPullback.inv p, ?_⟩
    rw [← Scheme.Hom.comp_apply, hP.isoPullback_inv_snd]
  -- `F` is the only prime of the model over `x`
  have huniq : ∀ a : D.Y, D.f a = x → Order.coheight a = 1 → a = D.E.genericPoint := by
    intro a ha ha1
    have hπa : π a = hirr.genericPoint :=
      U.ι.isOpenEmbedding.injective (ha.trans hgen.symm)
    have hmem : a ∈ Eex.support := by
      change a ∈ ((I.comap π).support : Set _)
      rw [Scheme.IdealSheafData.support_comap]
      change π a ∈ (I.support : Set U)
      rw [hπa]
      exact hgenI.mem
    have hsp : Eex.genericPoint ⤳ a := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hmem
    by_contra hne
    have hle : a ≤ Eex.genericPoint := hsp
    have hlt : a < Eex.genericPoint := lt_of_le_not_ge hle fun h' =>
      hne ((show a ⤳ Eex.genericPoint from h').antisymm hsp).eq
    have h2 := Order.coheight_add_one_le hlt
    rw [Eex.coheight_genericPoint] at h2
    change Order.coheight a = 1 at ha1
    rw [ha1] at h2
    exact absurd h2 (by decide)
  refine ⟨D, h, hh, hP.w.symm, hDf, hrange, huniq, ?_⟩
  -- the valuation of `F` is the order function
  intro g hg
  set y := hirr.genericPoint with hy
  have hxy : U.ι y = x := hgen
  subst hxy
  have := IsRegularLocalRing.isDomain (Y.presheaf.stalk (U.ι y))
  have : IsIso (U.ι.stalkMap y) := inferInstance
  set e := (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv with he
  set g' := e g with hg'
  have hg'0 : g' ≠ 0 := fun h0 => hg (e.injective (h0.trans (map_zero e).symm))
  have hmem : ∀ s : ℕ, (s : ℤ) ≤ (blowUp I).ord (functionFieldMap π
      (algebraMap _ (U : Scheme).functionField g')) Eex.genericPoint ↔
        g ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (U.ι y)) ^ s := fun s =>
    (hordE g' hg'0 s).trans (mem_maximalIdeal_pow_iff_of_bijective e s g)
  have hffm : functionFieldMap (π ≫ U.ι) (algebraMap _ Y.functionField g) =
      functionFieldMap π (algebraMap _ (U : Scheme).functionField g') := by
    rw [← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Mori.functionFieldMap_algebraMap_stalk]
    rfl
  obtain ⟨hM1, hM2⟩ := maximalIdealOrder_spec hg
  have hord : (blowUp I).ord (functionFieldMap π
      (algebraMap _ (U : Scheme).functionField g')) Eex.genericPoint =
        maximalIdealOrder _ g := by
    have h1 := (hmem _).mpr hM1
    have h2 : ¬ ((maximalIdealOrder _ g + 1 : ℕ) : ℤ) ≤ (blowUp I).ord (functionFieldMap π
        (algebraMap _ (U : Scheme).functionField g')) Eex.genericPoint := fun h =>
      hM2 ((hmem _).mp h)
    push_cast at h2
    omega
  have hne : functionFieldMap (π ≫ U.ι) (algebraMap _ Y.functionField g) ≠ 0 :=
    (map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hg))
  change MMP.Mori.PrimeDivisor.divisorialValuation Eex (functionFieldMap (π ≫ U.ι) _) = _
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord Eex hne, hffm, hord]

/-- The exceptional prime of `Bl_W X` over `η_W`, as a divisor over `X` on an open normal
subscheme of the blow-up. -/
private theorem exists_divisorOver_blowUp {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    (hX : IsNormalVariety k sX)
    (W : IrreducibleCloseds X) (hW : 2 ≤ codimension W)
    (hreg : IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint)) :
    ∃ (D : DivisorOver k sX)
        (j : D.Y ⟶ Stacks.Blowup.blowUp
          (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X))),
        IsOpenImmersion j ∧ j ≫ Stacks.Blowup.blowUpToBase _ = D.f ∧
          D.f D.E.genericPoint = W.isIrreducible.genericPoint := by
  obtain ⟨D, h, hh, hhf, hDf, -, -, -⟩ := exists_divisorOver_smoothBlowup hX W hW _ rfl hreg
  have hinv : (Stacks.Blowup.blowUpIso _).inv ≫ Stacks.Blowup.blowUpToBase _ =
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X)) := by
    rw [Iso.inv_comp_eq, Stacks.Blowup.blowUpIso_hom_comp]
  have := hh
  refine ⟨D, h ≫ (Stacks.Blowup.blowUpIso _).inv, inferInstance, ?_, hDf⟩
  rw [Category.assoc, hinv, hhf]

end BlowUp

end MMP.Mori.TerminalCodimTwo

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

namespace MMP.Flips

open MMP.Mori hiding IsCanonicalPair

/-- Over a normal variety with canonical divisor `K` and `K + D` `ℚ`-Cartier, every proper
divisor `E` over `X` has a discrepancy `a(E, X, D)`, computed from a top form `ω` with
`div(ω) = K`. -/
private theorem exists_isQDiscrepancyWith {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} {K : Divisor X} {D : QDivisor X} (hX : IsNormalVariety k sX)
    (hK : K.IsCanonicalDivisor sX n) (hKD : (Divisor.toQDivisor K + D).IsQCartier)
    (E : ProperDivisorOver k sX) :
    ∃ (ω : RationalPluriForms sX n 1) (a : ℚ), IsQDiscrepancyWith sX n D ω E a := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hdiv : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have := E.isProper
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  have hKD' : (Divisor.toQDivisor (divisorOfForm ω) + D).IsQCartier := hdiv ▸ hKD
  have hB := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' E.f
    (Divisor.toQDivisor (divisorOfForm ω) + D)
  obtain ⟨G, hG, -⟩ := hKD'.existsUnique_isPullback hB
  exact ⟨ω, _, hX, hK.1, hω0, hKD', hB, G, hG, rfl⟩

end MMP.Flips

end

/-! ### Lemmas shared by the termination argument -/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP MMP.Flips MMP.Mori

/-- A discrepancy `a(F, X, D)` of a divisor `F` of `k(X)` is computed on a proper divisor over
`X` with valuation `F`, on which `1 + a` is a log discrepancy. -/
private theorem exists_isLogDiscrepancy_of_isDiscrepancy {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X}
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

/-- If `d + c = 3` with `d > 0`, then `c ≤ 2`. -/
private theorem coheight_le_two_of_add_eq_three {d : WithBot ℕ∞} {c : ℕ∞} (h : d + c = 3)
    (hd : 0 < d) : c ≤ 2 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    have h3 : e + c = 3 := WithBot.coe_injective h
    norm_cast at hd
    by_contra hc
    have h4 := add_le_add (Order.one_le_iff_pos.mpr hd) (Order.add_one_le_of_lt (not_le.mp hc))
    rw [h3] at h4
    exact absurd h4 (by decide)

/-- A flipping curve `C` of a small contraction `φ⁺ : X⁺ ⟶ Z` of a threefold is an irreducible
closed subset of codimension two, whose generic point has coheight two and lies over a closed
point of `Z` of coheight three. -/
private theorem exists_irreducibleCloseds_of_isFlippingCurve {k : Type u} [Field k]
    {X' Z : Scheme.{u}} {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {φp : X' ⟶ Z}
    [IsIntegral X'] [LocallyOfFiniteType sX'] [IsIntegral Z] [LocallyOfFiniteType sZ]
    (hs : IsSmall k sZ sX' φp) (h3 : topologicalKrullDim X' = 3)
    {C : Set X'} (hC : IsFlippingCurve k sX' sZ φp C) :
    ∃ W : IrreducibleCloseds X', (W : Set X') = C ∧ codimension W = 2 ∧
      Order.coheight W.isIrreducible.genericPoint = 2 ∧
      IsClosed ({φp W.isIrreducible.genericPoint} : Set Z) ∧
      Order.coheight (φp W.isIrreducible.genericPoint) = 3 := by
  obtain ⟨-, -, -, -, z, hz, hCmax, hCdim⟩ := hC
  have hF : IsClosed {x : X' | φp x = z} := hz.preimage φp.continuous
  have hCcl : IsClosed C := closure_subset_iff_isClosed.mp
    (hCmax.2 ⟨hCmax.1.1.closure, closure_minimal hCmax.1.2 hF⟩ subset_closure)
  let W : IrreducibleCloseds X' := ⟨C, hCmax.1.1, hCcl⟩
  set ξ := W.isIrreducible.genericPoint with hξdef
  have hξ : IsGenericPoint ξ C := by
    have h := W.isIrreducible.isGenericPoint_genericPoint_closure
    rwa [W.isClosed.closure_eq] at h
  have hcod : codimension W = Order.coheight ξ := by
    have hEq : (irreducibleSetEquivPoints (α := X')).symm ξ = W := IrreducibleCloseds.ext hξ
    rw [codimension_eq_coheight, ← hEq, Order.coheight_orderIso]
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX' ξ
  rw [isGenericPoint_def.mp hξ, h3] at hd
  have hle := coheight_le_two_of_add_eq_three hd hCdim
  have hξz : φp ξ = z := hCmax.1.2 (hξ.mem)
  have hdz := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sZ z
  rw [hz.closure_eq, topologicalKrullDim_eq_zero_of_subsingleton, zero_add,
    ← hs.dim_eq, h3] at hdz
  have h3' : Order.coheight z = 3 :=
    WithBot.coe_injective (hdz.trans (WithBot.coe_ofNat 3).symm)
  obtain ⟨V, Wc, hV, hW, hVW, hρ⟩ := hs.exists_isIso
  have hξV : ξ ∈ V := by
    by_contra hξV
    let Vo : X'.Opens := V.compl
    let Wo : Z.Opens := Wc.compl
    let x' : Vo.toScheme := ⟨ξ, hξV⟩
    have e1 : Order.coheight (Vo.ι x') = Order.coheight x' :=
      Topology.IsOpenEmbedding.coheight_eq _ Vo.ι.isOpenEmbedding
    have e2 : Order.coheight ((φp.resLE Wo Vo hVW) x') = Order.coheight x' :=
      Topology.IsOpenEmbedding.coheight_eq _ (φp.resLE Wo Vo hVW).isOpenEmbedding
    have e3 : Order.coheight (Wo.ι ((φp.resLE Wo Vo hVW) x')) =
        Order.coheight ((φp.resLE Wo Vo hVW) x') :=
      Topology.IsOpenEmbedding.coheight_eq _ Wo.ι.isOpenEmbedding
    have e4 : Wo.ι ((φp.resLE Wo Vo hVW) x') = φp ξ := by
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι]; rfl
    have hco : Order.coheight ξ = Order.coheight z := by
      rw [← hξz, ← e4, e3, e2, ← e1]
      rfl
    rw [hco, h3'] at hle
    exact absurd hle (by decide)
  have hge : 2 ≤ Order.coheight ξ := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV ξ hξV
  have h2 : Order.coheight ξ = 2 := le_antisymm hle hge
  exact ⟨W, rfl, hcod.trans h2, h2, hξz ▸ hz, hξz ▸ h3'⟩

/-- If the transform of prime divisors under `g` is given by a bijection `e`, the transform of a
divisor has coefficient `D.coeff P` at `e P`. -/
private theorem coeff_transformDivisor_apply {X Y : Scheme} {R : Type*} [AddCommMonoid R]
    {g : X.RationalMap Y} (e : Mori.PrimeDivisor X ≃ Mori.PrimeDivisor Y)
    (he : ∀ P, Mori.RationalMap.transformPrimeDivisor g P = some (e P))
    (D : DivisorWithCoeffs R X) (P : Mori.PrimeDivisor X) :
    (Mori.RationalMap.transformDivisor g D).coeff (e P) = D.coeff P := by
  have h : Mori.RationalMap.transformDivisor g D = Finsupp.mapDomain e D := by
    induction D using Finsupp.induction_linear with
    | zero => simp
    | add D D' h h' => rw [map_add, h, h', Finsupp.mapDomain_add]
    | single P r =>
      rw [Mori.RationalMap.transformDivisor_single_of_eq_some (he P), Finsupp.mapDomain_single]
  rw [h]
  exact Finsupp.mapDomain_apply_of_injective e.injective D P

section Flip

variable {k : Type} [Field k] [CharZero k] {X Z X' : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral X'] [IsLocallyNoetherian X']
  [IsNormal X'] [CompactSpace X'] [LocallyOfFiniteType sX']

/-- Under a flip, the transform of prime divisors is a bijection. -/
private theorem exists_equiv_transformPrimeDivisor_eq {E : RDivisor X} {φ : X ⟶ Z}
    {φp : X' ⟶ Z} {g : X.RationalMap X'} (hφ : IsFlip k sX sZ sX' E φ φp g) :
    ∃ e : Mori.PrimeDivisor X ≃ Mori.PrimeDivisor X',
      ∀ P, Mori.RationalMap.transformPrimeDivisor g P = some (e P) := by
  have hφs : IsSmall k sZ sX φ := hφ.isSmall_source
  have hφps : IsSmall k sZ sX' φp := hφ.isSmall
  have hZn : IsNormalVariety k sZ := hφ.isNormalVariety_target
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  have hbφ : IsBirationalMorphism φ := hφs.surjective_and_isBirational.2
  have hbφp : IsBirationalMorphism φp := hφps.surjective_and_isBirational.2
  haveI : IsDominant φ := hbφ.isDominant
  haveI : IsDominant φp := hbφp.isDominant
  have he := (exceptional_hasNonemptyCenter_iff_of_isSmall _ _ sZ φ φp hφs hφps).2 g
    hφ.isModificationOf
  set e := primeDivisorEquivOfModification hφs hφps hφ.isModificationOf
  exact ⟨e, fun P => (he P).1⟩

/-- Under a flip of a canonical pair `(X, D)`, `(X⁺, g_* D)` is a canonical pair with respect to
any canonical divisor `K⁺` of `X⁺`. -/
private theorem isCanonicalPair_transformDivisor {K : Divisor X} {D : QDivisor X}
    {φ : X ⟶ Z} {φp : X' ⟶ Z} {g : X.RationalMap X'} (hD : Flips.IsCanonicalPair sX 3 K D)
    (hφ : IsFlip k sX sZ sX' (logCanonicalDivisor K (QDivisor.toRDivisor D)) φ φp g)
    {K' : Divisor X'} (hK' : K'.IsCanonicalDivisor sX' 3) :
    Flips.IsCanonicalPair sX' 3 K' (Mori.RationalMap.transformDivisor g D) := by
  obtain ⟨hX', hK, hDeff, hKD, hdisc⟩ := hD.of_isFlip hφ
  exact ⟨hX', hK', hDeff, hKD.add_of_linearlyEquivalent
    (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX' hX' hK hK'), hdisc⟩

end Flip

end MMP.Flips

end

/-! ### Flipped curves have regular generic points -/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Flips MMP.Mori

/-- **Positive discrepancies over a codimension-two point force regularity**, over any field of
characteristic zero. Let `X` be a normal variety over `k` with canonical divisor `K`, `B ≥ 0` a
`ℚ`-divisor with `K + B` `ℚ`-Cartier, and `W ⊆ X` an irreducible closed subset of codimension two.
If every exceptional divisor over `X` with centre `W` has positive discrepancy `a(D, X, B)`, then
`𝒪_{X,η_W}` is regular. The generic surface at `η_W` lives over the purely transcendental extension
`k(t₁, …, t_{n-2})`, which is never algebraically closed, so no hypothesis on `k` beyond
characteristic zero enters. -/
private theorem isRegularLocalRing_stalk_genericPoint_of_isDiscrepancy_pos {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {B : QDivisor X} (hB : 0 ≤ B)
    (hKB : (Divisor.toQDivisor K + B).IsQCartier) {W : IrreducibleCloseds X}
    (hW : codimension W = 2)
    (hpos : ∀ E : ProperDivisorOver k sX, E.IsExceptional → (E.center : Set X) = W →
      ∀ a : ℝ, MMP.Flips.IsDiscrepancy sX n K (QDivisor.toRDivisor B) E.valuation a → 0 < a) :
    IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint) := by
  classical
  have hP : IsPair sX B := ⟨hX, n, K, hK, hKB⟩
  have hPair : MMP.Fourfold.IsCharZeroPair sX B := ⟨inferInstance, hP, hB⟩
  set x := W.isIrreducible.genericPoint with hx_def
  have hxW : closure {x} = (W : Set X) := W.isIrreducible.isGenericPoint_genericPoint_closure.trans
    W.isClosed.closure_eq
  have hcx : Order.coheight x = 2 := by
    have hEq : (irreducibleSetEquivPoints (α := X)).symm x = W := IrreducibleCloseds.ext hxW
    rw [← hW, codimension_eq_coheight, ← hEq, Order.coheight_orderIso]
  have hdim := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x
  rw [hxW, hcx, hK.topologicalKrullDim_eq] at hdim
  obtain ⟨d, rfl, hWd⟩ : ∃ d : ℕ, n = d + 2 ∧ topologicalKrullDim (W : Set X) = d := by
    revert hdim
    induction topologicalKrullDim (W : Set X) using WithBot.recBotCoe with
    | bot => simp
    | coe e =>
      induction e using ENat.recTopCoe with
      | top => intro h; norm_cast at h
      | coe m => exact fun h => ⟨m, by exact_mod_cast h.symm, rfl⟩
  obtain ⟨U, -, φ, -, -, S, ι, sS, -, _, _, _, _, hSa, hSft, hSnv, hSdim, p, hp, -, hgen,
    hiso, -, -, BS, hBS, hBS0, -, hbij, hlog⟩ :=
    MMP.Fourfold.exists_genericFibre_bijOn_valuation_center sX hPair hK.topologicalKrullDim_eq
      W hWd
  by_contra hreg
  have hsing : p ∉ smoothLocus sS := by
    intro hps
    apply hreg
    obtain ⟨V, hpV, hV⟩ := mem_smoothLocus_iff.mp hps
    have : Smooth (V.ι ≫ sS) := hV
    have hrV := isRegularLocalRing_stalk_of_smooth_over_field (V.ι ≫ sS) ⟨p, hpV⟩
    have hrS : IsRegularLocalRing (S.presheaf.stalk p) :=
      IsRegularLocalRing.of_ringEquiv (V.stalkIso ⟨p, hpV⟩).commRingCatIsoToRingEquiv
    have hrU : IsRegularLocalRing ((U : Scheme).presheaf.stalk (ι p)) :=
      IsRegularLocalRing.of_ringEquiv (asIso (ι.stalkMap p)).symm.commRingCatIsoToRingEquiv
    have hrX : IsRegularLocalRing (X.presheaf.stalk (U.ι (ι p))) :=
      IsRegularLocalRing.of_ringEquiv (U.stalkIso (ι p)).commRingCatIsoToRingEquiv
    have hxe : U.ι (ι p) = x := hgen.eq hxW
    rwa [hxe] at hrX
  have : IsQuasiProjectiveVariety _ sS := by
    have : AlgebraicGeometry.IsVariety _ sS := hSnv.1
    exact ⟨Stacks.HProjective.isQuasiProjective_of_isQuasiAffineHom sS inferInstance⟩
  have : CharZero (FractionRing (MvPolynomial (Fin d) k)) :=
    charZero_of_injective_algebraMap
      (algebraMap k (FractionRing (MvPolynomial (Fin d) k))).injective
  obtain ⟨D, hDproj, -, hDc, a, ha1, ha⟩ :=
    MMP.Threefold.exists_isLogDiscrepancy_le_one_of_notMem_smoothLocus sS hSdim
      ⟨inferInstance, hBS, hBS0⟩ hp hsing
  have hξ : D.valuation ∈ {ξ | ∃ D : DivisorOver (FractionRing (MvPolynomial (Fin d) k)) sS,
      D.valuation = ξ ∧ (D.center : Set S) = {p}} := ⟨D, rfl, hDc⟩
  obtain ⟨D₂, hD₂v, hD₂c⟩ := hbij.mapsTo hξ
  obtain ⟨n', D₁, hD₁p, hD₁v, hD₁⟩ :=
    (hlog _ hξ a).mp ⟨2, D, isProper_of_isProjectiveMorphism D.f hDproj, rfl, ha⟩
  have hD₁c : D₁.center = W :=
    (MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX.1 (hD₁v.trans hD₂v.symm)).trans hD₂c
  let E : ProperDivisorOver k sX := ⟨D₁, hD₁p⟩
  have hEc : (E.center : Set X) = W := by
    rw [ProperDivisorOver.center_eq_toDivisorOver_center]
    exact congrArg (fun V : IrreducibleCloseds X => (V : Set X)) hD₁c
  have hEe : E.IsExceptional := by
    change topologicalKrullDim (E.center : Set X) + 2 ≤ topologicalKrullDim X
    rw [hEc, hWd, hK.topologicalKrullDim_eq]
    norm_cast
  obtain ⟨_, b, hb⟩ := exists_isQDiscrepancyWith hX hK hKB E
  replace hb := hb.isDiscrepancy hK hKB hEe
  obtain ⟨E₁, hE₁v, hlog₁⟩ := exists_isLogDiscrepancy_of_isDiscrepancy hb
  have h1 := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlog₁ hD₁ hE₁v
  have h2 := hpos E hEe hEc b hb
  linarith

/-- Every exceptional divisor `E` over a canonical pair `(X, D)` has a discrepancy
`a(E, X, D) ≥ 0`: the discrepancy computed from a top form `ω` with `div(ω) = K` bounds
`discrep(X, D)` from above. -/
private theorem exists_isDiscrepancy_nonneg_of_isCanonicalPair {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ}
    {K : Divisor X} {D : QDivisor X} (hD : MMP.Flips.IsCanonicalPair sX n K D)
    {E : ProperDivisorOver k sX} (hE : E.IsExceptional) :
    ∃ a : ℝ, 0 ≤ a ∧ MMP.Flips.IsDiscrepancy sX n K (QDivisor.toRDivisor D) E.valuation a := by
  obtain ⟨hXn, hK, -, hKD, hdisc⟩ := hD
  obtain ⟨ω, a, ha⟩ := exists_isQDiscrepancyWith hXn hK hKD E
  exact ⟨a, EReal.coe_nonneg.mp (hdisc.trans (sInf_le ⟨E, ω, a, hE, ha, rfl⟩)),
    ha.isDiscrepancy hK hKD hE⟩

/-- Every exceptional divisor over `X⁺` whose center is a flipped curve has positive discrepancy
with respect to `(X⁺, g_*D)`: it is exceptional with nonempty center over `X`, where its
discrepancy is `≥ 0`, and discrepancies increase strictly along flipped curves. -/
private theorem discrepancy_pos_of_isFlippedCurveOf {k : Type u} [Field k] [PerfectField k]
    {X Z X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral X'] [IsLocallyNoetherian X']
    [IsNormal X'] [CompactSpace X'] [LocallyOfFiniteType sX'] {n : ℕ} {K : Divisor X}
    {D : QDivisor X} (hD : MMP.Flips.IsCanonicalPair sX n K D) {φ : X ⟶ Z} {φp : X' ⟶ Z}
    {g : X.RationalMap X'} {C : Set X'}
    (hC : IsFlippedCurveOf k sX sZ sX' (logCanonicalDivisor K (QDivisor.toRDivisor D)) φ φp g C)
    {E : ProperDivisorOver k sX'} (hE : E.IsExceptional) (hEC : (E.center : Set X') = C)
    {a : ℝ} (ha : MMP.Flips.IsDiscrepancy sX' n (MMP.Mori.RationalMap.transformDivisor g K)
      (QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor g D)) E.valuation a) :
    0 < a := by
  have hflip := hC.1
  have hφs : IsSmall k sZ sX φ := hflip.isSmall_source
  have hφps : IsSmall k sZ sX' φp := hflip.isSmall
  have hZn : IsNormalVariety k sZ := hflip.isNormalVariety_target
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  have hbφ : IsBirationalMorphism φ := hφs.surjective_and_isBirational.2
  have hbφp : IsBirationalMorphism φp := hφps.surjective_and_isBirational.2
  haveI : IsDominant φ := hbφ.isDominant
  haveI : IsDominant φp := hbφp.isDominant
  obtain ⟨hX, hK, -, hKD, -⟩ := id hD
  let eφ := RingEquiv.ofBijective (functionFieldMap φ) hbφ.functionFieldMap_bijective
  let ν : Valuation X.functionField ℤᵐ⁰ :=
    (E.valuation.comap (functionFieldMap φp)).comap eφ.symm.toRingHom
  have hν : ν.comap (functionFieldMap φ) = E.valuation.comap (functionFieldMap φp) :=
    Valuation.ext fun t => by
      change E.valuation (functionFieldMap φp (eφ.symm (eφ t))) = _
      rw [RingEquiv.symm_apply_apply]
      rfl
  obtain ⟨-, Ex, hExv, hExe⟩ := ((exceptional_hasNonemptyCenter_iff_of_isSmall sX sX' sZ φ φp
    hφs hφps).1 ν E.valuation hν).mpr ⟨ha.2.2.1, E, rfl, hE⟩
  obtain ⟨a₀, h0, ha₀⟩ := exists_isDiscrepancy_nonneg_of_isCanonicalPair hD hExe
  rw [hExv] at ha₀
  exact h0.trans_lt (hC.isDiscrepancy_lt hX hK hKD E hEC hν ha₀ ha)

/-- Let `(X, D)` be a canonical pair, `X` a threefold over a field of characteristic zero with
canonical divisor `K`, and `φ⁺ : X⁺ ⟶ Z` a flip of the small contraction `φ : X ⟶ Z` with respect
to `K_X + D`, with birational map `g`. If `C ⊆ X⁺` is a flipped curve, then the local ring of `X⁺`
at the generic point of `C` is regular. -/
private theorem isRegularLocalRing_stalk_of_isFlippedCurveOf {k : Type} [Field k] [CharZero k]
    {X Z X' : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    (sX' : X' ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] [IsLocallyNoetherian X'] [IsNormal X']
    [CompactSpace X'] {K : Divisor X} {D : QDivisor X} (hD : MMP.Flips.IsCanonicalPair sX 3 K D)
    {φ : X ⟶ Z} {φp : X' ⟶ Z} {g : X.RationalMap X'} {C : Set X'}
    (hC : IsFlippedCurveOf k sX sZ sX' (logCanonicalDivisor K (QDivisor.toRDivisor D)) φ φp g C)
    {ξ : X'} (hξ : IsGenericPoint ξ C) :
    IsRegularLocalRing (X'.presheaf.stalk ξ) := by
  obtain ⟨hflip, hcurve⟩ := id hC
  have hX'n : IsNormalVariety k sX' := hflip.isNormalVariety_flip
  have hZn : IsNormalVariety k sZ := hflip.isNormalVariety_target
  haveI : IsIntegral X' := hX'n.1.toIsIntegral
  haveI : LocallyOfFiniteType sX' := hX'n.1.toLocallyOfFiniteType
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  obtain ⟨-, hK', hD'eff, hKD', -⟩ := MMP.Flips.IsCanonicalPair.of_isFlip hD hflip
  obtain ⟨W, rfl, hW, -⟩ := exists_irreducibleCloseds_of_isFlippingCurve hflip.isSmall
    hK'.topologicalKrullDim_eq hcurve
  rw [hξ.eq (W.isIrreducible.isGenericPoint_genericPoint_closure.trans W.isClosed.closure_eq)]
  refine isRegularLocalRing_stalk_genericPoint_of_isDiscrepancy_pos hX'n hK'
    hD'eff hKD' hW ?_
  intro E hE hEc a ha
  exact discrepancy_pos_of_isFlippedCurveOf hD hC hE hEc ha

end MMP.Flips

end

/-! ### Szabó's difficulty does not increase under a flip -/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

namespace MMP.Flips

open MMP MMP.Flips MMP.Mori

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Discrepancies do not depend on the choice of the canonical divisor -/

section Canonical

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- The log discrepancy of an exceptional divisor does not depend on the canonical divisor used
to compute it: both are `1 + a_ω(E, X, D)` for any top form `ω`. -/
private theorem isLogDiscrepancy_of_isCanonicalDivisor (hX : IsNormalVariety k sX) {n : ℕ}
    {K₁ K₂ : Divisor X} {D : QDivisor X} (hK₁ : K₁.IsCanonicalDivisor sX n)
    (hK₂ : K₂.IsCanonicalDivisor sX n) (hD₁ : (Divisor.toQDivisor K₁ + D).IsQCartier)
    (hD₂ : (Divisor.toQDivisor K₂ + D).IsQCartier) {E : ProperDivisorOver k sX}
    (hE : E.IsExceptional) {b : ℝ}
    (hb : IsLogDiscrepancy sX n K₁ (QDivisor.toRDivisor D) E.valuation b) :
    IsLogDiscrepancy sX n K₂ (QDivisor.toRDivisor D) E.valuation b := by
  obtain ⟨a, ha, rfl⟩ := hb
  obtain ⟨ω, a', h'⟩ := exists_isQDiscrepancyWith hX hK₂ hD₂ E
  exact ⟨a', h'.isDiscrepancy hK₂ hD₂ hE, by rw [ha.eq (h'.isDiscrepancy hK₁ hD₁ hE)]⟩

/-- `𝒮_t(X, D; B)` does not depend on the canonical divisor. -/
private theorem smallLogDiscrepancySetOff_eq_of_isCanonicalDivisor (hX : IsNormalVariety k sX)
    {n : ℕ} {K₁ K₂ : Divisor X} {D : QDivisor X} (hK₁ : K₁.IsCanonicalDivisor sX n)
    (hK₂ : K₂.IsCanonicalDivisor sX n) (hD₁ : (Divisor.toQDivisor K₁ + D).IsQCartier)
    (hD₂ : (Divisor.toQDivisor K₂ + D).IsQCartier) (B : Closeds X) (t : ℚ) :
    smallLogDiscrepancySetOff sX n K₁ D hX hK₁ hD₁ B t =
      smallLogDiscrepancySetOff sX n K₂ D hX hK₂ hD₂ B t := by
  have key : ∀ {K₁ K₂ : Divisor X} (hK₁ : K₁.IsCanonicalDivisor sX n)
      (hK₂ : K₂.IsCanonicalDivisor sX n) (hD₁ : (Divisor.toQDivisor K₁ + D).IsQCartier)
      (hD₂ : (Divisor.toQDivisor K₂ + D).IsQCartier),
      smallLogDiscrepancySetOff sX n K₁ D hX hK₁ hD₁ B t ⊆
        smallLogDiscrepancySetOff sX n K₂ D hX hK₂ hD₂ B t := by
    rintro K₁ K₂ hK₁ hK₂ hD₁ hD₂ ν ⟨⟨hc, ⟨E, hE, rfl⟩, b, hb, hbt⟩, hoff⟩
    exact ⟨⟨hc, ⟨E, hE, rfl⟩, b,
      isLogDiscrepancy_of_isCanonicalDivisor hX hK₁ hK₂ hD₁ hD₂ hE hb, hbt⟩, hoff⟩
  exact (key hK₁ hK₂ hD₁ hD₂).antisymm (key hK₂ hK₁ hD₂ hD₁)

/-- Szabó's difficulty does not depend on the canonical divisor. -/
private theorem szaboDifficulty_eq_of_isCanonicalDivisor (hX : IsNormalVariety k sX)
    {n : ℕ} {K₁ K₂ : Divisor X} {D : QDivisor X} (hK₁ : K₁.IsCanonicalDivisor sX n)
    (hK₂ : K₂.IsCanonicalDivisor sX n) (hD₁ : (Divisor.toQDivisor K₁ + D).IsQCartier)
    (hD₂ : (Divisor.toQDivisor K₂ + D).IsQCartier) (B : Closeds X) (N : ℕ) (hN : 1 ≤ N)
    (c : ℚ) :
    szaboDifficulty sX n K₁ D hX hK₁ hD₁ B N hN c =
      szaboDifficulty sX n K₂ D hX hK₂ hD₂ B N hN c := by
  unfold szaboDifficulty
  simp_rw [smallLogDiscrepancySetOff_eq_of_isCanonicalDivisor hX hK₁ hK₂ hD₁ hD₂ B]

/-- A Kollár–Mori discrepancy depends only on the valuation of the divisor. -/
private theorem isDiscrepancy_of_valuation_eq (hX : IsNormalVariety k sX) {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} {D D' : DivisorOver k sX} {a : ℚ}
    (ha : MMP.Mori.IsDiscrepancy sX n K Δ D a) (hv : D.valuation = D'.valuation) :
    MMP.Mori.IsDiscrepancy sX n K Δ D' a := by
  obtain ⟨-, hK, m, hm, hC, U, hU, τ, hτ, hτa⟩ := ha
  refine ⟨hX, hK, m, hm, hC, U,
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv ▸ hU, τ, hτ, ?_⟩
  rw [hτa, MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX
    hK.topologicalKrullDim_eq hv τ]

end Canonical

/-! ### Centers -/

section Center

/-- If the valuation ring of `w` dominates the local ring of `X` at `x`, the valuation ring of
`w ∘ φ^*` dominates the local ring of `Z` at `φ(x)`, for a dominant `φ : X ⟶ Z`. -/
private theorem dominates_map {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z] (φ : X ⟶ Z)
    [IsDominant φ] (w : Valuation X.functionField ℤᵐ⁰) {x : X}
    (h1 : ∀ a : X.presheaf.stalk x, w (algebraMap _ X.functionField a) ≤ 1)
    (h2 : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      w (algebraMap _ X.functionField a) < 1) :
    (∀ a : Z.presheaf.stalk (φ x),
      w.comap (functionFieldMap φ) (algebraMap _ Z.functionField a) ≤ 1) ∧
    ∀ a ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk (φ x)),
      w.comap (functionFieldMap φ) (algebraMap _ Z.functionField a) < 1 := by
  refine ⟨fun a => ?_, fun a ha => ?_⟩
  · rw [Valuation.comap_apply, functionFieldMap_algebraMap_stalk]
    exact h1 _
  · rw [Valuation.comap_apply, functionFieldMap_algebraMap_stalk]
    exact h2 _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu))

/-- Divisors over `X` and `X'` whose valuations agree on `k(Z)` have centers over the same point
of the separated scheme `Z`. -/
private theorem map_eq_of_comap_eq {k : Type u} [Field k] {X X' Z : Scheme.{u}} [IsIntegral X]
    [IsIntegral X'] [IsIntegral Z] {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    (sZ : Z ⟶ Spec (.of k)) [IsSeparated sZ] (φ : X ⟶ Z)
    (φ' : X' ⟶ Z) [IsDominant φ] [IsDominant φ'] (E : DivisorOver k sX) (E' : DivisorOver k sX')
    (hv : E.valuation.comap (functionFieldMap φ) = E'.valuation.comap (functionFieldMap φ')) :
    φ (E.f E.E.genericPoint) = φ' (E'.f E'.E.genericPoint) := by
  obtain ⟨d1, d2⟩ := dominates_map φ E.valuation
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one E _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one E _ rfl)
  obtain ⟨d1', d2'⟩ := dominates_map φ' E'.valuation
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one E' _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one E' _ rfl)
  rw [← hv] at d1' d2'
  exact MMP.Positivity.DivisorOver.eq_of_dominates sZ _ d1 d2 d1' d2'

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {sX : X ⟶ Spec (.of k)}

/-- The center of a proper divisor over `X` is the closure of the point `f(η_E)`. -/
private theorem coe_center_eq_closure (E : ProperDivisorOver k sX) :
    (E.center : Set X) = closure {E.f E.E.genericPoint} := by
  rw [E.center_eq_toDivisorOver_center]
  exact E.toDivisorOver.center_eq_closure_genericPoint

/-- The codimension of the center of a proper divisor over `X` is the coheight of `f(η_E)`. -/
private theorem codimension_center (E : ProperDivisorOver k sX) :
    codimension E.center = Order.coheight (E.f E.E.genericPoint) := by
  rw [E.center_eq_toDivisorOver_center, MMP.Positivity.DivisorOver.codimension_center]

end Center

/-! ### Flipped curves and multiplicities -/

section Curves

/-- A dimension `d` with `d + 2 = 3` is `1`. -/
private theorem eq_one_of_add_two_eq_three {d : WithBot ℕ∞}
    (h : d + ((2 : ℕ∞) : WithBot ℕ∞) = 3) : d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe n =>
      have h3 : ((3 : ℕ∞) : WithBot ℕ∞) = 3 := rfl
      rw [← h3, ← WithBot.coe_add, WithBot.coe_inj] at h
      have : n + 2 = 3 := by exact_mod_cast h
      obtain rfl : n = 1 := by omega
      rfl

/-- Over a small contraction `φ : X ⟶ Z` of a threefold, the closure of a point `x` of coheight
two lying over a point of coheight three of `Z` is a flipping curve of `φ`. -/
private theorem isFlippingCurve_closure_singleton {k : Type u} [Field k] {X Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX]
    {φ : X ⟶ Z} (hφ : IsSmall k sZ sX φ) (hX : topologicalKrullDim X = 3) {x : X}
    (hx : Order.coheight x = 2) (hφx : Order.coheight (φ x) = 3) :
    IsFlippingCurve k sX sZ φ (closure {x}) := by
  have hxEx : x ∈ MMP.Flips.exceptionalSet φ := by
    by_contra h
    have := MMP.Flips.coheight_map_of_notMem_exceptionalSet h
    rw [hφx, hx] at this
    exact absurd this (by decide)
  refine isFlippingCurve_of_subset_exceptionalSet hφ hX isIrreducible_singleton.closure
    isClosed_closure (eq_one_of_add_two_eq_three ?_)
    ((MMP.Flips.isClosed_exceptionalSet φ).closure_subset_iff.2 (Set.singleton_subset_iff.2 hxEx))
  simpa [hx, hX] using MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x

/-- The ideal of a prime divisor at a point of an integral scheme is nonzero. -/
private theorem stalkIdeal_ne_bot {X : Scheme} [IsIntegral X] (D : MMP.Mori.PrimeDivisor X)
    (x : X) : D.idealSheaf.stalkIdeal x ≠ ⊥ := by
  have hD : D.idealSheaf ≠ ⊥ := by
    intro h0
    have hsupp : D.support = Set.univ := by
      change ((D.idealSheaf.support : Set X)) = _
      rw [h0, Scheme.IdealSheafData.support_bot]; rfl
    have hgen : IsGenericPoint D.genericPoint (Set.univ : Set X) := by
      rw [← hsupp, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isGenericPoint_closure
    have h1 := D.coheight_genericPoint
    have h2 : Order.coheight D.genericPoint = 0 := by
      rw [Order.coheight_eq_zero]
      intro b hb
      have hb' : b ⤳ D.genericPoint := hb
      have hbgen : IsGenericPoint b (Set.univ : Set X) := by
        refine (isGenericPoint_iff_specializes).mpr fun w => ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
        exact hb'.trans (hgen.specializes (Set.mem_univ w))
      exact (hbgen.eq hgen).symm ▸ le_rfl
    rw [h2] at h1
    exact absurd h1 (by decide)
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have hne := Stacks.IdealSheaf.ideal_ne_bot D.idealSheaf hD (U := ⟨V, hV⟩) hxV
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  intro h0
  have h1 := D.idealSheaf.germ_mem_stalkIdeal ⟨V, hV⟩ hxV hg
  rw [h0, Ideal.mem_bot] at h1
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  exact hg0 (germ_injective_of_isIntegral X x hxV (h1.trans (map_zero _).symm))

/-- A prime divisor through the generic point of `W` has finite positive multiplicity along `W`
(Krull's intersection theorem in the noetherian local ring at `η_W`). -/
private theorem one_le_toNat_multiplicityAlong {Y : Scheme} [IsIntegral Y]
    [IsLocallyNoetherian Y] (P : MMP.Mori.PrimeDivisor Y) (W : IrreducibleCloseds Y)
    (h : W.isIrreducible.genericPoint ∈ (P.support : Set Y)) :
    1 ≤ (P.multiplicityAlong W).toNat := by
  set R := Y.presheaf.stalk W.isIrreducible.genericPoint
  set I := P.idealSheaf.stalkIdeal W.isIrreducible.genericPoint
  have hI0 : I ≠ ⊥ := stalkIdeal_ne_bot P _
  have hIm : I ≤ IsLocalRing.maximalIdeal R :=
    P.idealSheaf.stalkIdeal_le_maximalIdeal_of_mem_support h
  obtain ⟨s, hs⟩ : ∃ s : ℕ, ¬ I ≤ IsLocalRing.maximalIdeal R ^ s := by
    by_contra! hall
    apply hI0
    rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top]
    exact le_iInf hall
  have hle : P.multiplicityAlong W ≤ s := iSup₂_le fun t ht => by
    have : t < s := by
      by_contra! hst
      exact hs (ht.trans (Ideal.pow_le_pow_right hst))
    exact_mod_cast this.le
  have h1 : (1 : ℕ∞) ≤ P.multiplicityAlong W :=
    le_iSup₂_of_le (f := fun (s : ℕ) (_ : I ≤ IsLocalRing.maximalIdeal R ^ s) => (s : ℕ∞)) 1
      (by simpa using hIm) le_rfl
  have hne : P.multiplicityAlong W ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top s) hle
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hk] at h1 ⊢
  rw [ENat.toNat_coe]
  exact_mod_cast h1

/-- The multiplicity `mult_W Δ = ∑_Γ Δ_Γ · mult_W Γ` of an effective `ℚ`-divisor along `W` is
nonnegative. -/
private theorem sum_mul_multiplicityAlong_nonneg {Y : Scheme} [IsIntegral Y] {Δ : QDivisor Y}
    (hΔ : ∀ Γ, 0 ≤ Δ.coeff Γ) (W : IrreducibleCloseds Y) :
    0 ≤ Δ.sum fun Γ b => b * ((Γ.multiplicityAlong W).toNat : ℚ) :=
  Finset.sum_nonneg fun Γ _ => mul_nonneg (hΔ Γ) (Nat.cast_nonneg _)

/-- If `W` lies in a prime divisor `Q` with `c ≤ Δ_Q`, for an effective `ℚ`-divisor `Δ` and
`c ≥ 0`, then `c ≤ mult_W Δ`. -/
private theorem le_sum_mul_multiplicityAlong {Y : Scheme} [IsIntegral Y] [IsLocallyNoetherian Y]
    {Δ : QDivisor Y} (hΔ : ∀ Γ, 0 ≤ Δ.coeff Γ) (W : IrreducibleCloseds Y) {c : ℚ} (hc : 0 ≤ c)
    {Q : MMP.Mori.PrimeDivisor Y} (hcQ : c ≤ Δ.coeff Q)
    (hW : W.isIrreducible.genericPoint ∈ (Q.support : Set Y)) :
    c ≤ Δ.sum fun Γ b => b * ((Γ.multiplicityAlong W).toNat : ℚ) := by
  by_cases hQ : Q ∈ Δ.support
  · have h1 : (1 : ℚ) ≤ ((Q.multiplicityAlong W).toNat : ℚ) := by
      exact_mod_cast one_le_toNat_multiplicityAlong Q W hW
    calc c ≤ Δ.coeff Q * 1 := by rwa [mul_one]
      _ ≤ Δ Q * ((Q.multiplicityAlong W).toNat : ℚ) :=
          mul_le_mul_of_nonneg_left h1 (hc.trans hcQ)
      _ ≤ _ := Finset.single_le_sum (f := fun Γ => Δ Γ * ((Γ.multiplicityAlong W).toNat : ℚ))
          (fun Γ _ => mul_nonneg (hΔ Γ) (Nat.cast_nonneg _)) hQ
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.notMem_support_iff.mp hQ] at hcQ
    exact hcQ.trans (sum_mul_multiplicityAlong_nonneg hΔ W)

end Curves

/-! ### Sums in `ℕ∞` -/

/-- Every family in `ℕ∞` is summable, with sum the supremum of its finite partial sums. -/
private theorem summable_enat {ι : Type*} (f : ι → ℕ∞) : Summable f :=
  (hasSum_of_isLUB _ (isLUB_iSup (f := fun s : Finset ι => ∑ i ∈ s, f i))).summable

/-- In `ℕ∞`, a pointwise inequality `f ≤ g` gives `∑ f ≤ ∑ g`. -/
private theorem tsum_le_tsum_enat {ι : Type*} {f g : ι → ℕ∞} (h : ∀ i, f i ≤ g i) :
    ∑' i, f i ≤ ∑' i, g i :=
  Summable.tsum_le_tsum h (summable_enat f) (summable_enat g)

/-- In `ℕ∞`, a pointwise inequality `f ≤ g` which is strict at one index gives a strict
inequality of sums, as soon as `∑ g` is finite. -/
private theorem tsum_lt_tsum_enat {ι : Type*} {f g : ι → ℕ∞} (h : ∀ i, f i ≤ g i) {i : ι}
    (hi : f i < g i) (hg : ∑' j, g j ≠ ⊤) : ∑' j, f j < ∑' j, g j := by
  classical
  rw [Summable.tsum_eq_add_tsum_ite' (f := g) i (summable_enat _)] at hg ⊢
  rw [Summable.tsum_eq_add_tsum_ite' (f := f) i (summable_enat _)]
  have hR : (∑' j, if j = i then 0 else f j) ≤ ∑' j, if j = i then 0 else g j :=
    tsum_le_tsum_enat fun j => by split_ifs <;> simp [h j]
  generalize (∑' j, if j = i then 0 else f j) = r at *
  generalize (∑' j, if j = i then 0 else g j) = s at *
  generalize f i = a at *
  generalize g i = b at *
  have hgi : b ≠ ⊤ := fun h' => hg (by rw [h', top_add])
  have hRg : s ≠ ⊤ := fun h' => hg (by rw [h', add_top])
  have hfi : a ≠ ⊤ := ne_top_of_lt hi
  have hRf : r ≠ ⊤ := ne_top_of_le_ne_top hRg hR
  lift a to ℕ using hfi
  lift b to ℕ using hgi
  lift r to ℕ using hRf
  lift s to ℕ using hRg
  norm_cast at hi hR ⊢
  omega

/-- Termwise injections `F : s_i ↪ t_i` give `∑ #s_i ≤ ∑ #t_i` in `ℕ∞`. -/
private theorem tsum_encard_le_tsum_encard {ι α β : Type*} {s : ι → Set α} {t : ι → Set β}
    {F : α → β} (hF : Function.Injective F) (h : ∀ i, Set.MapsTo F (s i) (t i)) :
    ∑' i, (s i).encard ≤ ∑' i, (t i).encard :=
  tsum_le_tsum_enat fun i => Set.encard_le_encard_of_injOn (h i) hF.injOn

/-- Termwise injections `F : s_i ↪ t_i`, one of which misses a point, give
`∑ #s_i < ∑ #t_i` in `ℕ∞`, as soon as `∑ #t_i` is finite. -/
private theorem tsum_encard_lt_tsum_encard {ι α β : Type*} {s : ι → Set α} {t : ι → Set β}
    {F : α → β} (hF : Function.Injective F) (h : ∀ i, Set.MapsTo F (s i) (t i))
    (hfin : ∑' i, (t i).encard ≠ ⊤) {i : ι} {a : α} (ha : a ∉ s i) (hFa : F a ∈ t i) :
    ∑' i, (s i).encard < ∑' i, (t i).encard := by
  refine tsum_lt_tsum_enat (fun i => Set.encard_le_encard_of_injOn (h i) hF.injOn) (i := i) ?_ hfin
  have hsub : F '' s i ⊂ t i := Set.ssubset_iff_subset_ne.2 ⟨(h i).image_subset, fun he => ha <|
    by obtain ⟨b, hb, hba⟩ : F a ∈ F '' s i := he ▸ hFa; exact hF hba ▸ hb⟩
  have hfinS : (t i).Finite := Set.encard_ne_top_iff.mp
    (ne_top_of_le_ne_top hfin ((summable_enat fun i => (t i).encard).le_tsum i fun _ _ => zero_le'))
  rw [← hF.injOn.encard_image]
  exact (hfinS.subset hsub.subset).encard_lt_encard hsub

/-- Let `(X, D)` be a canonical pair, `X` a threefold over a field of characteristic zero with
canonical divisor `K`, with `⌊D⌋ = 0`; let `N ≥ 1` with `N D` integral, `c ≥ 0` rational, and
`B = ⋃_{P ∈ S} P` a finite union of prime divisors containing every prime divisor `P` with
`D.coeff P > c`. Let `φ⁺ : X⁺ ⟶ Z` be a flip of `φ : X ⟶ Z` with respect to `K_X + D` with
birational map `g`, `D⁺ = g_* D`, `B⁺ = ⋃_{P ∈ S} g_* P`, and `K⁺` a canonical divisor of `X⁺`.
If no flipping curve of `φ` is contained in `B`, then `K_{X⁺} + D⁺` is `ℚ`-Cartier,
`d_{N,c}(X⁺, D⁺; B⁺) ≤ d_{N,c}(X, D; B) < ∞`, and the first inequality is strict as soon as some
flipped curve `C` satisfies `c = 0` or `C ⊆ g_* P` for a prime divisor `P` with `c ≤ D.coeff P`. -/
private theorem szaboDifficulty_flip_le {k : Type} [Field k] [CharZero k]
    {X Z X' : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    (sX' : X' ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral X'] [IsLocallyNoetherian X']
    [IsNormal X'] [CompactSpace X'] [LocallyOfFiniteType sX']
    {K : Divisor X} {D : QDivisor X} (hD : MMP.Flips.IsCanonicalPair sX 3 K D)
    (hDfloor : DivisorWithCoeffs.roundDown D = 0)
    {N : ℕ} (hN : 1 ≤ N) (hND : ∀ P, ∃ m : ℤ, (N : ℚ) * D.coeff P = m)
    {c : ℚ} (hc : 0 ≤ c) {S : Finset (Mori.PrimeDivisor X)} {B : Closeds X}
    (hB : (B : Set X) = ⋃ P ∈ S, (P.support : Set X))
    (hBD : ∀ P : Mori.PrimeDivisor X, c < D.coeff P → (P.support : Set X) ⊆ B)
    {φ : X ⟶ Z} {φp : X' ⟶ Z} {g : X.RationalMap X'}
    (hφ : IsFlip k sX sZ sX' (logCanonicalDivisor K (QDivisor.toRDivisor D)) φ φp g)
    {B' : Closeds X'}
    (hB' : (B' : Set X') =
      ⋃ P ∈ S, ⋃ Q ∈ Mori.RationalMap.transformPrimeDivisor g P, (Q.support : Set X'))
    (hnc : ∀ C : Set X, IsFlippingCurve k sX sZ φ C → ¬ C ⊆ B)
    {K' : Divisor X'} (hK' : K'.IsCanonicalDivisor sX' 3) :
    ∃ hD' : (Divisor.toQDivisor K' + Mori.RationalMap.transformDivisor g D).IsQCartier,
      szaboDifficulty sX' 3 K' (Mori.RationalMap.transformDivisor g D)
          hφ.isNormalVariety_flip hK' hD' B' N hN c ≤
        szaboDifficulty sX 3 K D hD.1 hD.2.1 hD.2.2.2.1 B N hN c ∧
      szaboDifficulty sX 3 K D hD.1 hD.2.1 hD.2.2.2.1 B N hN c < ⊤ ∧
      ((∃ C : Set X', IsFlippedCurveOf k sX sZ sX' (logCanonicalDivisor K (QDivisor.toRDivisor D))
          φ φp g C ∧ (c = 0 ∨ ∃ P : Mori.PrimeDivisor X, c ≤ D.coeff P ∧
            ∃ Q ∈ Mori.RationalMap.transformPrimeDivisor g P, C ⊆ (Q.support : Set X'))) →
        szaboDifficulty sX' 3 K' (Mori.RationalMap.transformDivisor g D)
            hφ.isNormalVariety_flip hK' hD' B' N hN c <
          szaboDifficulty sX 3 K D hD.1 hD.2.1 hD.2.2.2.1 B N hN c) := by
  have hφs : IsSmall k sZ sX φ := hφ.isSmall_source
  have hφps : IsSmall k sZ sX' φp := hφ.isSmall
  have hZn : IsNormalVariety k sZ := hφ.isNormalVariety_target
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : IsSeparated sZ := hZn.1.toIsSeparated
  have hbφ : IsBirationalMorphism φ := hφs.surjective_and_isBirational.2
  have hbφp : IsBirationalMorphism φp := hφps.surjective_and_isBirational.2
  haveI : IsDominant φ := hbφ.isDominant
  haveI : IsDominant φp := hbφp.isDominant
  obtain ⟨hX, hK, -, hKD, -⟩ := id hD
  have hX'n : IsNormalVariety k sX' := hφ.isNormalVariety_flip
  have hB'' : (B' : Set X') = ⋃ P ∈ S, ⋃ (P' : Mori.PrimeDivisor X')
      (_ : Mori.RationalMap.transformPrimeDivisor g P = some P'), (P'.support : Set X') := hB'
  obtain ⟨hKp, hKDp, hmain⟩ :=
    smallLogDiscrepancySetOff_subset_of_isFlip hX hK hKD hφ S B B' hB hB'' hnc
  have hD' := hKDp.add_of_linearlyEquivalent
    (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX' hX'n hKp hK')
  refine ⟨hD', ?_⟩
  rw [szaboDifficulty_eq_of_isCanonicalDivisor hX'n hK' hKp hD' hKDp]
  -- the identification `k(X⁺) = k(X)` of valuations over `k(Z)`
  let eφ := RingEquiv.ofBijective (functionFieldMap φ) hbφ.functionFieldMap_bijective
  let F : Valuation X'.functionField ℤᵐ⁰ → Valuation X.functionField ℤᵐ⁰ := fun ν' =>
    (ν'.comap (functionFieldMap φp)).comap eφ.symm.toRingHom
  have hF : ∀ ν', (F ν').comap (functionFieldMap φ) = ν'.comap (functionFieldMap φp) :=
    fun ν' => Valuation.ext fun t => by
      change ν' (functionFieldMap φp (eφ.symm (eφ t))) = _
      rw [RingEquiv.symm_apply_apply]
      rfl
  have hFinj : Function.Injective F := by
    intro ν₁ ν₂ h
    have h' : ν₁.comap (functionFieldMap φp) = ν₂.comap (functionFieldMap φp) := by
      rw [← hF, ← hF, h]
    ext x
    obtain ⟨y, rfl⟩ := hbφp.functionFieldMap_bijective.2 x
    exact congrArg (fun v : Valuation Z.functionField ℤᵐ⁰ => v y) h'
  let Sp : ℚ → Set (Valuation X'.functionField ℤᵐ⁰) := fun t =>
    smallLogDiscrepancySetOff sX' 3 (Mori.RationalMap.transformDivisor g K)
      (Mori.RationalMap.transformDivisor g D) hX'n hKp hKDp B' t
  let S₀ : ℚ → Set (Valuation X.functionField ℤᵐ⁰) := fun t =>
    smallLogDiscrepancySetOff sX 3 K D hD.1 hD.2.1 hD.2.2.2.1 B t
  have hmaps : ∀ t, Set.MapsTo F (Sp t) (S₀ t) := fun t ν' h => (hmain t ν' h).2 _ (hF ν')
  have hfin : szaboDifficulty sX 3 K D hD.1 hD.2.1 hD.2.2.2.1 B N hN c ≠ ⊤ :=
    hD.szaboDifficulty_ne_top_of_charZero hDfloor hN hc hBD
  unfold szaboDifficulty at hfin ⊢
  refine ⟨tsum_encard_le_tsum_encard hFinj fun _ => hmaps _, hfin.lt_top, ?_⟩
  rintro ⟨C, hC, hcond⟩
  suffices hstrict : ∃ i : {i : ℤ // (N : ℚ) * c ≤ i}, ∃ ν', ν' ∉ Sp (2 - (i : ℚ) / N) ∧
      F ν' ∈ S₀ (2 - (i : ℚ) / N) by
    obtain ⟨i, ν', hν'S, hν'⟩ := hstrict
    exact tsum_encard_lt_tsum_encard hFinj (fun _ => hmaps _) hfin hν'S hν'
  obtain ⟨-, hCcurve⟩ := id hC
  have h3' : topologicalKrullDim X' = 3 := by exact_mod_cast hKp.topologicalKrullDim_eq
  obtain ⟨W, hWC, hW2, hξ2, -, hz3⟩ :=
    exists_irreducibleCloseds_of_isFlippingCurve hφps h3' hCcurve
  set ξ := W.isIrreducible.genericPoint with hξdef
  have hξC : IsGenericPoint ξ C := by
    have h := W.isIrreducible.isGenericPoint_genericPoint_closure
    rw [W.isClosed.closure_eq] at h
    rw [← hWC]
    exact h
  have hreg : IsRegularLocalRing (X'.presheaf.stalk ξ) :=
    MMP.Flips.isRegularLocalRing_stalk_of_isFlippedCurveOf sX sZ sX' hD hC hξC
  set Dp := Mori.RationalMap.transformDivisor g D with hDp
  set μ : ℚ := Dp.sum fun Γ b => b * ((Γ.multiplicityAlong W).toNat : ℚ) with hμ
  -- the blow-up divisor `E_C` of the flipped curve, `a(E_C, X⁺, D⁺) = 1 - mult_C D⁺`
  obtain ⟨D₀, hD₀ξ, hD₀⟩ : ∃ D₀ : DivisorOver k sX', D₀.f D₀.E.genericPoint = ξ ∧
      MMP.Mori.IsDiscrepancy sX' 3 (Mori.RationalMap.transformDivisor g K) Dp D₀
        (((2 : ℕ) : ℚ) - 1 - μ) := by
    obtain ⟨D₀, j, hj, hjf, hD₀E⟩ := MMP.Mori.TerminalCodimTwo.exists_divisorOver_blowUp
      hX'n W (by rw [hW2]) hreg
    haveI := hj
    exact ⟨D₀, hD₀E,
      MMP.Mori.isDiscrepancy_blowUp_of_isRegularLocalRing_of_charZero sX' hX'n hKp
        Dp hKDp W (by rw [hW2]; rfl) le_rfl hreg D₀ j hjf hD₀E⟩
  obtain ⟨E, hEv⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hX'n D₀
  have hEξ : E.f E.E.genericPoint = ξ :=
    (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX'n.1 hEv).trans hD₀ξ
  have hEC : (E.center : Set X') = C := by
    rw [coe_center_eq_closure, hEξ]
    exact isGenericPoint_def.mp hξC
  have hEexc : E.IsExceptional := by
    have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX' ξ
    rw [isGenericPoint_def.mp hξC, hξ2] at hd
    change topologicalKrullDim (E.center : Set X') + 2 ≤ topologicalKrullDim X'
    rw [hEC, ← hd]
    rfl
  -- the discrepancy of `E_C` over `X⁺`
  obtain ⟨ω, a', hq⟩ := exists_isQDiscrepancyWith hX'n hKp hKDp E
  have hdisc' := hq.isDiscrepancy hKp hKDp hEexc
  obtain ⟨E', hE'v, hlog'⟩ := exists_isLogDiscrepancy_of_isDiscrepancy hdisc'
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy
    (isDiscrepancy_of_valuation_eq hX'n hD₀ hEv.symm) E.isProper
  have ha' : ((a' : ℚ) : ℝ) = 1 - μ := by
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlog' hlog hE'v
    push_cast at this
    linarith
  -- the corresponding divisor over `X`, of smaller discrepancy
  obtain ⟨hνc, Ex, hExv, hExe⟩ := ((exceptional_hasNonemptyCenter_iff_of_isSmall sX sX' sZ φ φp
    hφs hφps).1 (F E.valuation) E.valuation (hF _)).mpr ⟨hdisc'.2.2.1, E, rfl, hEexc⟩
  obtain ⟨ω₀, a₀, hq₀⟩ := exists_isQDiscrepancyWith hX hK hKD Ex
  have hdisc₀ := hq₀.isDiscrepancy hK hKD hExe
  rw [hExv] at hdisc₀
  have hlt := hC.isDiscrepancy_lt hX hK hKD E hEC (hF _) hdisc₀ hdisc'
  -- `k = N · mult_C D⁺` is an integer `≥ N c`
  have he := (exceptional_hasNonemptyCenter_iff_of_isSmall sX sX' sZ φ φp hφs
    hφps).2 g hφ.isModificationOf
  set e := primeDivisorEquivOfModification hφs hφps hφ.isModificationOf
  have hcoeff : ∀ P, Dp.coeff (e P) = D.coeff P := fun P => by
    rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply]
    exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq (he P).1
      (fun P' hP' => e.injective (Option.some.inj ((he P').1.symm.trans hP'))) D
  have hDeffp := (MMP.Flips.IsCanonicalPair.of_isFlip hD hφ).2.2.1
  have hNDp : ∀ Γ, ∃ m : ℤ, (N : ℚ) * Dp.coeff Γ = m := fun Γ => by
    obtain ⟨m, hm⟩ := hND (e.symm Γ)
    exact ⟨m, by rw [← e.apply_symm_apply Γ, hcoeff]; exact hm⟩
  choose m hm using hNDp
  set kk : ℤ := Dp.support.sum fun Γ => m Γ * ((Γ.multiplicityAlong W).toNat : ℤ) with hkkdef
  have hkk : (kk : ℚ) = N * μ := by
    rw [hkkdef, hμ, Finsupp.sum, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun Γ _ => ?_
    rw [← hm Γ, DivisorWithCoeffs.coeff_apply]
    ring
  have hcμ : c ≤ μ := by
    rcases hcond with rfl | ⟨P, hcP, Q, hQ, hCQ⟩
    · exact sum_mul_multiplicityAlong_nonneg hDeffp W
    · obtain rfl : Q = e P := Option.some.inj (hQ.symm.trans (he P).1)
      exact le_sum_mul_multiplicityAlong hDeffp W hc (hcoeff P ▸ hcP) (hCQ hξC.mem)
  have hN0 : (0 : ℚ) < N := by exact_mod_cast hN
  have hkkc : (N : ℚ) * c ≤ kk := by
    rw [hkk]
    exact mul_le_mul_of_nonneg_left hcμ hN0.le
  have ht : (2 : ℚ) - (kk : ℚ) / N = 2 - μ := by
    rw [hkk]
    field_simp
  refine ⟨⟨kk, hkkc⟩, E.valuation, ?_, ?_⟩
  · -- `a_ℓ(E_C, X⁺, D⁺) = 2 - mult_C D⁺` is not small
    rintro ⟨⟨-, -, b, ⟨a'', ha'', rfl⟩, hbt⟩, -⟩
    have := ha''.eq hdisc'
    change (1 + a'' : ℝ) < ((2 - (kk : ℚ) / N : ℚ) : ℝ) at hbt
    rw [ht, this, ha'] at hbt
    push_cast at hbt
    linarith
  · refine ⟨⟨hνc, ⟨Ex, hExe, hExv⟩, 1 + (a₀ : ℝ), ⟨a₀, hdisc₀, rfl⟩, ?_⟩, ?_⟩
    · change (1 + a₀ : ℝ) < ((2 - (kk : ℚ) / N : ℚ) : ℝ)
      rw [ht]
      push_cast
      linarith
    · -- the center of `E_C` on `X` is not a curve contained in `B`
      intro E'' hE''v ⟨hcod, hsubB⟩
      have hξξ := map_eq_of_comap_eq sZ φ φp E''.toDivisorOver E.toDivisorOver
        (by change E''.valuation.comap _ = _; rw [hE''v]; exact hF _)
      rw [hEξ] at hξξ
      exact hnc _ (isFlippingCurve_closure_singleton hφs
        (by exact_mod_cast hK.topologicalKrullDim_eq) (codimension_center E'' ▸ hcod)
        (hξξ ▸ hz3)) (coe_center_eq_closure E'' ▸ hsubB)

end

end MMP.Flips

end

/-! ### Eventually no flipped curve lies in a large component -/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Flips

open MMP MMP.Flips MMP.Mori

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A sequence in `ℕ∞`, finite at `i₀` and nonincreasing on the steps `i ≥ i₀` with `i + 1 < L`,
drops strictly only finitely often: from some `i₁ ≥ i₀` on, it never drops. -/
private theorem exists_forall_not_lt_of_le {f : ℕ → ℕ∞} {L : ℕ∞} {i₀ : ℕ} (hfin : f i₀ ≠ ⊤)
    (hle : ∀ i, i₀ ≤ i → ((i + 1 : ℕ) : ℕ∞) < L → f (i + 1) ≤ f i) :
    ∃ i₁, i₀ ≤ i₁ ∧ ∀ i, i₁ ≤ i → ((i + 1 : ℕ) : ℕ∞) < L → ¬ f (i + 1) < f i := by
  by_contra hcon
  push Not at hcon
  have hstep : ∀ j : ℕ, ((j + 1 : ℕ) : ℕ∞) < L → (j : ℕ∞) < L := fun j hj =>
    lt_of_le_of_lt (Nat.cast_le.mpr j.le_succ) hj
  have hmono : ∀ i j, i₀ ≤ i → i ≤ j → (j : ℕ∞) < L → f j ≤ f i := by
    intro i j hi hij hj
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact (hle j (hi.trans hij) hj).trans (ih (hstep j hj))
  -- after `m` strict drops the sequence has lost at least `m`
  have key : ∀ m : ℕ, ∃ i, i₀ ≤ i ∧ f i + m ≤ f i₀ := by
    intro m
    induction m with
    | zero => exact ⟨i₀, le_rfl, by simp⟩
    | succ m ih =>
      obtain ⟨i, hi, him⟩ := ih
      obtain ⟨j, hij, hj, hlt⟩ := hcon i hi
      refine ⟨j + 1, by omega, ?_⟩
      calc f (j + 1) + ((m + 1 : ℕ) : ℕ∞) = (f (j + 1) + 1) + m := by push_cast; ring
        _ ≤ f i + m := by gcongr; exact (Order.add_one_le_of_lt hlt).trans
                            (hmono i j hi hij (hstep j hj))
        _ ≤ f i₀ := him
  obtain ⟨i, -, hi⟩ := key ((f i₀).toNat + 1)
  have h := ENat.toNat_le_toNat (le_add_self.trans hi) hfin
  rw [ENat.toNat_coe] at h
  omega

/-- A `ℚ`-divisor has a common denominator: some `N ≥ 1` with `N D` integral. -/
private theorem exists_nat_mul_coeff_eq_int {X : Scheme} (D : QDivisor X) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ P, ∃ m : ℤ, (N : ℚ) * D.coeff P = m := by
  classical
  refine ⟨∏ P ∈ D.support, (D P).den,
    Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun P _ => (D P).den_nz),
    fun P => ?_⟩
  change ∃ m : ℤ, _ * D P = m
  by_cases hP : P ∈ D.support
  · obtain ⟨a, ha⟩ := Finset.dvd_prod_of_mem (fun P => (D P).den) hP
    refine ⟨a * (D P).num, ?_⟩
    rw [ha]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  · exact ⟨0, by simp [Finsupp.notMem_support_iff.mp hP]⟩

variable {k : Type} [Field k] [CharZero k] {X Z X' : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral X'] [IsLocallyNoetherian X']
  [IsNormal X'] [CompactSpace X'] [LocallyOfFiniteType sX']

/-- Under a flip, every prime divisor `Q` of `X⁺` is the transform of a prime divisor `P` of `X`,
and every divisor `g_* D` has coefficient `D.coeff P` at `Q`. -/
private theorem exists_transformPrimeDivisor_eq_and_coeff {E : RDivisor X} {φ : X ⟶ Z}
    {φp : X' ⟶ Z} {g : X.RationalMap X'} (hφ : IsFlip k sX sZ sX' E φ φp g)
    (Q : Mori.PrimeDivisor X') :
    ∃ P : Mori.PrimeDivisor X, Mori.RationalMap.transformPrimeDivisor g P = some Q ∧
      ∀ D : QDivisor X, (Mori.RationalMap.transformDivisor g D).coeff Q = D.coeff P := by
  obtain ⟨e, he⟩ := exists_equiv_transformPrimeDivisor_eq hφ
  exact ⟨e.symm Q, by simpa using he (e.symm Q), fun D => by
    simpa using coeff_transformDivisor_apply e he D (e.symm Q)⟩

/-- Szabó's difficulty depends on the divisor only, not on the proofs of its hypotheses. -/
private theorem szaboDifficulty_congr {K : Divisor X} {D₁ D₂ : QDivisor X} (h : D₁ = D₂)
    (hX : IsNormalVariety k sX) (hK : K.IsCanonicalDivisor sX 3)
    (hD₁ : (Divisor.toQDivisor K + D₁).IsQCartier) (hD₂ : (Divisor.toQDivisor K + D₂).IsQCartier)
    (B : Closeds X) (N : ℕ) (hN : 1 ≤ N) (c : ℚ) :
    szaboDifficulty sX 3 K D₁ hX hK hD₁ B N hN c =
      szaboDifficulty sX 3 K D₂ hX hK hD₂ B N hN c := by
  subst h; rfl

/-- Let `(X, D)` be a canonical pair, `X` a threefold over a field of characteristic zero, with
`⌊D⌋ = 0`, `c ≥ 0` rational and `S` a sequence of flips for `(X, D)`, and let `B_i = ⋃_{P ∈ T i} P`
be the transforms on `X_i` of a finite union `B` of prime divisors containing every component of
`D` of coefficient `> c`. If no flipping curve of `φ_i` lies in `B_i` for `i ≥ i₀`, then from some
`i₁ ≥ i₀` on no flipped curve `C` of `φ_i⁺` satisfies `c = 0` or `C ⊆ Q` for a prime divisor `Q`
of `X_{i+1}` with `c ≤ D_{i+1}.coeff Q`. -/
private theorem SequenceOfFlips.eventually_not_isFlippedCurveOf {k : Type} [Field k]
    [CharZero k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {K : Divisor X} {D : QDivisor X} (hD : Flips.IsCanonicalPair sX 3 K D)
    (hDfloor : DivisorWithCoeffs.roundDown D = 0) {c : ℚ} (hc : 0 ≤ c)
    (S : SequenceOfFlips sX 3 K D)
    (T : ∀ i, Finset (Mori.PrimeDivisor (S.model i).1))
    (hT0 : ∀ P : Mori.PrimeDivisor (S.model 0).1, c < (S.model 0).2.2.2.coeff P → P ∈ T 0)
    (hT : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < S.length → ∀ Q : Mori.PrimeDivisor (S.model (i + 1)).1,
      Q ∈ T (i + 1) ↔
        ∃ P ∈ T i, Mori.RationalMap.transformPrimeDivisor (S.flipMap i) P = some Q)
    {i₀ : ℕ} (hi₀ : (i₀ : ℕ∞) < S.length)
    (hnc : ∀ i : ℕ, i₀ ≤ i → ((i + 1 : ℕ) : ℕ∞) < S.length → ∀ C : Set (S.model i).1,
      IsFlippingCurve k (S.model i).2.1 (S.baseStr i) (S.contraction i) C →
        ¬ C ⊆ ⋃ P ∈ T i, (P.support : Set (S.model i).1)) :
    ∃ i₁, i₀ ≤ i₁ ∧ ∀ i : ℕ, i₁ ≤ i → ((i + 1 : ℕ) : ℕ∞) < S.length →
      ∀ C : Set (S.model (i + 1)).1,
        haveI := S.isLocallyNoetherian_model i
        haveI := S.isNormal_model i
        haveI := S.compactSpace_model i
        haveI := S.isLocallyNoetherian_model (i + 1)
        haveI := S.isNormal_model (i + 1)
        haveI := S.compactSpace_model (i + 1)
        IsFlippedCurveOf k (S.model i).2.1 (S.baseStr i) (S.model (i + 1)).2.1
            (logCanonicalDivisor (S.model i).2.2.1 (QDivisor.toRDivisor (S.model i).2.2.2))
            (S.contraction i) (S.flip i) (S.flipMap i) C →
          ¬ (c = 0 ∨ ∃ Q : Mori.PrimeDivisor (S.model (i + 1)).1,
            c ≤ (S.model (i + 1)).2.2.2.coeff Q ∧ C ⊆ (Q.support : Set (S.model (i + 1)).1)) := by
  classical
  obtain ⟨N, hN, hND⟩ := exists_nat_mul_coeff_eq_int D
  have hbase : ∀ (M : FlipModel k) (_ : M = ⟨X, sX, K, D⟩) [IsIntegral M.1]
      [IsLocallyNoetherian M.1] [IsNormal M.1] [CompactSpace M.1] [LocallyOfFiniteType M.2.1],
      Flips.IsCanonicalPair M.2.1 3 M.2.2.1 M.2.2.2 ∧ DivisorWithCoeffs.roundDown M.2.2.2 = 0 ∧
        ∀ P, ∃ m : ℤ, (N : ℚ) * M.2.2.2.coeff P = m := by
    rintro M rfl _ _ _ _ _
    exact ⟨hD, hDfloor, hND⟩
  have hlt : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < S.length → (i : ℕ∞) < S.length := fun i hi =>
    lt_of_le_of_lt (Nat.cast_le.mpr i.le_succ) hi
  have hint : ∀ i : ℕ, (i : ℕ∞) < S.length → IsIntegral (S.model i).1 := fun i hi =>
    (S.isNormalVariety_model i hi).1.toIsIntegral
  have hlft : ∀ i : ℕ, (i : ℕ∞) < S.length → LocallyOfFiniteType (S.model i).2.1 := fun i hi =>
    (S.isNormalVariety_model i hi).1.toLocallyOfFiniteType
  -- every model is a canonical pair with the properties of `(X, D; B)`
  have good : ∀ (i : ℕ) (hi : (i : ℕ∞) < S.length) [IsIntegral (S.model i).1]
      [IsLocallyNoetherian (S.model i).1] [IsNormal (S.model i).1] [CompactSpace (S.model i).1]
      [LocallyOfFiniteType (S.model i).2.1],
      Flips.IsCanonicalPair (S.model i).2.1 3 (S.model i).2.2.1 (S.model i).2.2.2 ∧
        DivisorWithCoeffs.roundDown (S.model i).2.2.2 = 0 ∧
        (∀ P, ∃ m : ℤ, (N : ℚ) * (S.model i).2.2.2.coeff P = m) ∧
        ∀ P, c < (S.model i).2.2.2.coeff P → P ∈ T i := by
    intro i
    induction i with
    | zero =>
      intro hi _ _ _ _ _
      obtain ⟨h1, h2, h3⟩ := hbase (S.model 0) S.model_zero
      exact ⟨h1, h2, h3, hT0⟩
    | succ i ih =>
      intro hi1 _ _ _ _ _
      have hi := hlt i hi1
      haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      haveI := S.compactSpace_model i
      haveI := hint i hi
      haveI := hlft i hi
      obtain ⟨hcan, hfl, hNi, hTi⟩ := ih hi
      have hflip := S.isFlip i hi1
      have hcoeff := fun Q => exists_transformPrimeDivisor_eq_and_coeff hflip Q
      rw [S.transform_eq i hi1]
      refine ⟨isCanonicalPair_transformDivisor hcan hflip (S.isCanonicalDivisor_model (i + 1) hi1),
        ?_, ?_, ?_⟩
      · refine Finsupp.ext fun Q => ?_
        obtain ⟨P, -, hP⟩ := hcoeff Q
        have h := DivisorWithCoeffs.coeff_roundDown (S.model i).2.2.2 P
        rw [hfl, ← hP, ← DivisorWithCoeffs.coeff_roundDown] at h
        exact h.symm
      · intro Q
        obtain ⟨P, -, hP⟩ := hcoeff Q
        simpa only [hP] using hNi P
      · intro Q hQ
        obtain ⟨P, hPQ, hP⟩ := hcoeff Q
        rw [hP] at hQ
        exact (hT i hi1 Q).2 ⟨P, hTi P hQ, hPQ⟩
  -- the closed sets `B_i` and the difficulties `n_i = d_{N,c}(X_i, D_i; B_i)`
  let B : ∀ i, Closeds (S.model i).1 := fun i =>
    ⟨⋃ P ∈ T i, (P.support : Set (S.model i).1),
      isClosed_biUnion_finset fun P _ => P.idealSheaf.support.isClosed⟩
  let f : ℕ → ℕ∞ := fun i =>
    if hi : (i : ℕ∞) < S.length then
      haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      haveI := S.compactSpace_model i
      haveI := hint i hi
      haveI := hlft i hi
      szaboDifficulty (S.model i).2.1 3 (S.model i).2.2.1 (S.model i).2.2.2 (good i hi).1.1
        (good i hi).1.2.1 (good i hi).1.2.2.2.1 (B i) N hN c
    else 0
  have hstep : ∀ i, i₀ ≤ i → ((i + 1 : ℕ) : ℕ∞) < S.length →
      f (i + 1) ≤ f i ∧ f i < ⊤ ∧ ∀ C : Set (S.model (i + 1)).1,
        haveI := S.isLocallyNoetherian_model i
        haveI := S.isNormal_model i
        haveI := S.compactSpace_model i
        haveI := S.isLocallyNoetherian_model (i + 1)
        haveI := S.isNormal_model (i + 1)
        haveI := S.compactSpace_model (i + 1)
        IsFlippedCurveOf k (S.model i).2.1 (S.baseStr i) (S.model (i + 1)).2.1
            (logCanonicalDivisor (S.model i).2.2.1 (QDivisor.toRDivisor (S.model i).2.2.2))
            (S.contraction i) (S.flip i) (S.flipMap i) C →
          (c = 0 ∨ ∃ Q : Mori.PrimeDivisor (S.model (i + 1)).1,
            c ≤ (S.model (i + 1)).2.2.2.coeff Q ∧ C ⊆ (Q.support : Set (S.model (i + 1)).1)) →
          f (i + 1) < f i := by
    intro i hii hi1
    have hi := hlt i hi1
    haveI := S.isLocallyNoetherian_model i
    haveI := S.isNormal_model i
    haveI := S.compactSpace_model i
    haveI := hint i hi
    haveI := hlft i hi
    haveI := S.isLocallyNoetherian_model (i + 1)
    haveI := S.isNormal_model (i + 1)
    haveI := S.compactSpace_model (i + 1)
    haveI := hint (i + 1) hi1
    haveI := hlft (i + 1) hi1
    obtain ⟨hcan, hfl, hNi, hTi⟩ := good i hi
    have hflip := S.isFlip i hi1
    have hB' : ((B (i + 1) : Closeds _) : Set (S.model (i + 1)).1) = ⋃ P ∈ T i,
        ⋃ Q ∈ Mori.RationalMap.transformPrimeDivisor (S.flipMap i) P,
          (Q.support : Set (S.model (i + 1)).1) := by
      ext x
      simp only [B, Closeds.coe_mk, Set.mem_iUnion, hT i hi1, exists_prop, Option.mem_def]
      exact ⟨fun ⟨Q, ⟨P, hP, hPQ⟩, hx⟩ => ⟨P, hP, Q, hPQ, hx⟩,
        fun ⟨P, hP, Q, hPQ, hx⟩ => ⟨Q, ⟨P, hP, hPQ⟩, hx⟩⟩
    obtain ⟨hD', hle, hfin, hstrict⟩ := Flips.szaboDifficulty_flip_le (S.model i).2.1
      (S.baseStr i) (S.model (i + 1)).2.1 hcan hfl hN hNi hc (S := T i) (B := B i) rfl
      (fun P hP => Set.subset_biUnion_of_mem (u := fun P => (P.support : Set (S.model i).1))
        (hTi P hP)) hflip hB' (hnc i hii hi1) (S.isCanonicalDivisor_model (i + 1) hi1)
    have hfi : f i = szaboDifficulty (S.model i).2.1 3 (S.model i).2.2.1 (S.model i).2.2.2
        hcan.1 hcan.2.1 hcan.2.2.2.1 (B i) N hN c := dif_pos hi
    have hfi1 : f (i + 1) = szaboDifficulty (S.model (i + 1)).2.1 3 (S.model (i + 1)).2.2.1
        (Mori.RationalMap.transformDivisor (S.flipMap i) (S.model i).2.2.2)
        hflip.isNormalVariety_flip (S.isCanonicalDivisor_model (i + 1) hi1) hD' (B (i + 1))
        N hN c := by
      rw [show f (i + 1) = _ from dif_pos hi1]
      exact szaboDifficulty_congr (S.transform_eq i hi1) _ _ _ _ _ _ _ _
    rw [hfi, hfi1]
    refine ⟨hle, hfin, fun C hC hcond => hstrict ⟨C, hC, ?_⟩⟩
    rcases hcond with h0 | ⟨Q, hQc, hCQ⟩
    · exact Or.inl h0
    · obtain ⟨P, hPQ, hP⟩ := exists_transformPrimeDivisor_eq_and_coeff hflip Q
      rw [S.transform_eq i hi1, hP] at hQc
      exact Or.inr ⟨P, hQc, Q, hPQ, hCQ⟩
  by_cases h0 : ((i₀ + 1 : ℕ) : ℕ∞) < S.length
  · obtain ⟨i₁, hi₁, hnot⟩ := exists_forall_not_lt_of_le (hstep i₀ le_rfl h0).2.1.ne
      fun i hi hi1 => (hstep i hi hi1).1
    exact ⟨i₁, hi₁, fun i hi hi1 C hC hcond =>
      hnot i hi hi1 ((hstep i (hi₁.trans hi) hi1).2.2 C hC hcond)⟩
  · exact ⟨i₀, le_rfl, fun i hi hi1 => absurd
      (lt_of_le_of_lt (Nat.cast_le.mpr (by omega)) hi1) h0⟩

end

end MMP.Flips

/-! ### Termination of flips for canonical threefold pairs -/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Flips

open MMP MMP.Flips MMP.Mori

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- An irreducible set contained in a finite union of closed sets lies in one of them. -/
private theorem exists_mem_subset_of_subset_biUnion {α ι : Type*} [TopologicalSpace α]
    {C : Set α} (hC : IsIrreducible C) {s : Finset ι} {f : ι → Set α}
    (hf : ∀ i ∈ s, IsClosed (f i)) (h : C ⊆ ⋃ i ∈ s, f i) : ∃ i ∈ s, C ⊆ f i := by
  classical
  obtain ⟨z, hz, hCz⟩ := isIrreducible_iff_sUnion_isClosed.mp hC (s.image f)
    (by simpa using hf) (by simpa [Set.sUnion_image] using h)
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨i, hi, hCz⟩

/-- A morphism with relative Picard number one is not an isomorphism: an isomorphism contracts
no curve, so every `ℝ`-Cartier divisor is numerically trivial over the target. -/
private theorem not_isIso_of_relativePicardNumber_eq_one {k : Type*} [Field k] {X Z : Scheme}
    (sX : X ⟶ Spec (.of k)) (f : X ⟶ Z) (h : Flips.relativePicardNumber sX f = 1) : ¬ IsIso f := by
  intro hf
  have hC : ∀ C : ProperCurve sX, ¬ C.IsContractedBy f := by
    intro C hC
    have hcl : closure ({C.point} : Set X) = {C.point} :=
      subset_antisymm (fun x hx => f.isOpenEmbedding.injective (hC x hx)) subset_closure
    have hd := C.dim_eq
    rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, hcl] at hd
    have h0 := topologicalKrullDim_zero_of_discreteTopology (({C.point} : Set X))
    rw [hd] at h0
    exact absurd h0 (by norm_num)
  have htop : relativeNumericallyTrivialDivisors sX f = ⊤ :=
    eq_top_iff.2 fun D _ => (mem_relativeNumericallyTrivialDivisors sX f).2
      fun C hc => absurd hc (hC C)
  haveI : Subsingleton (RelativeNumericalDivisorClasses sX f) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    exact (Submodule.Quotient.eq _).2 (htop ▸ Submodule.mem_top)
  rw [Flips.relativePicardNumber, rank_subsingleton'] at h
  simp at h

end

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral in
/-- Let `X` be a threefold over a field `k` of characteristic zero with canonical divisor `K`, and
`D` an effective `ℚ`-divisor on `X` such that `(X, D)` is a canonical pair and `⌊D⌋ = 0`. Then
every sequence of flips `S` for `(X, D)` terminates; `X` is not assumed `ℚ`-factorial. -/
private theorem SequenceOfFlips.terminates_of_isCanonicalPair {k : Type} [Field k]
    [CharZero k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {K : Divisor X} {D : QDivisor X} (hD : Flips.IsCanonicalPair sX 3 K D)
    (hDfloor : DivisorWithCoeffs.roundDown D = 0)
    (S : SequenceOfFlips sX 3 K D) : S.Terminates := by
  classical
  by_contra hS
  have hL : S.length = ⊤ := not_lt_top_iff.mp hS
  have hlen : ∀ i : ℕ, (i : ℕ∞) < S.length := fun i => hL ▸ ENat.coe_lt_top i
  have hint : ∀ i : ℕ, IsIntegral (S.model i).1 := fun i =>
    (S.isNormalVariety_model i (hlen i)).1.toIsIntegral
  have hlft : ∀ i : ℕ, LocallyOfFiniteType (S.model i).2.1 := fun i =>
    (S.isNormalVariety_model i (hlen i)).1.toLocallyOfFiniteType
  -- the flips identify the prime divisors of consecutive models
  have hex : ∀ i : ℕ, ∃ e : Mori.PrimeDivisor (S.model i).1 ≃ Mori.PrimeDivisor (S.model (i + 1)).1,
      ∀ P, Mori.RationalMap.transformPrimeDivisor (S.flipMap i) P = some (e P) := by
    intro i
    haveI := S.isLocallyNoetherian_model i
    haveI := S.isNormal_model i
    haveI := S.compactSpace_model i
    haveI := hint i
    haveI := hlft i
    haveI := S.isLocallyNoetherian_model (i + 1)
    haveI := S.isNormal_model (i + 1)
    haveI := S.compactSpace_model (i + 1)
    haveI := hint (i + 1)
    haveI := hlft (i + 1)
    exact exists_equiv_transformPrimeDivisor_eq (S.isFlip i (hlen _))
  choose e he using hex
  have hcoeff : ∀ i P, (S.model (i + 1)).2.2.2.coeff (e i P) = (S.model i).2.2.2.coeff P := by
    intro i P
    rw [S.transform_eq i (hlen _)]
    exact coeff_transformDivisor_apply (e i) (he i) _ P
  -- every coefficient of `D_i` is a coefficient of `D_0`
  have hval : ∀ i (Q : Mori.PrimeDivisor (S.model i).1), ∃ P : Mori.PrimeDivisor (S.model 0).1,
      (S.model i).2.2.2.coeff Q = (S.model 0).2.2.2.coeff P := by
    intro i
    induction i with
    | zero => exact fun Q => ⟨Q, rfl⟩
    | succ i ih =>
      intro Q
      obtain ⟨P, hP⟩ := ih ((e i).symm Q)
      exact ⟨P, by rw [← hP, ← hcoeff i ((e i).symm Q), Equiv.apply_symm_apply]⟩
  -- every model is a canonical pair
  have hbase : ∀ (M : FlipModel k) (_ : M = ⟨X, sX, K, D⟩) [IsIntegral M.1]
      [IsLocallyNoetherian M.1] [IsNormal M.1] [CompactSpace M.1] [LocallyOfFiniteType M.2.1],
      Flips.IsCanonicalPair M.2.1 3 M.2.2.1 M.2.2.2 := by
    rintro M rfl _ _ _ _ _
    exact hD
  have hcan : ∀ (i : ℕ) [IsIntegral (S.model i).1]
      [IsLocallyNoetherian (S.model i).1] [IsNormal (S.model i).1] [CompactSpace (S.model i).1]
      [LocallyOfFiniteType (S.model i).2.1],
      Flips.IsCanonicalPair (S.model i).2.1 3 (S.model i).2.2.1 (S.model i).2.2.2 := by
    intro i
    induction i with
    | zero =>
      intro _ _ _ _ _
      exact hbase (S.model 0) S.model_zero
    | succ i ih =>
      intro _ _ _ _ _
      haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      haveI := S.compactSpace_model i
      haveI := hint i
      haveI := hlft i
      rw [S.transform_eq i (hlen _)]
      exact isCanonicalPair_transformDivisor ih (S.isFlip i (hlen _))
        (S.isCanonicalDivisor_model (i + 1) (hlen _))
  have hX : topologicalKrullDim X = 3 := hD.2.1.topologicalKrullDim_eq
  -- the components `T c i` of `D_i` of coefficient `> c`
  let T : ℚ → ∀ i, Finset (Mori.PrimeDivisor (S.model i).1) := fun c i =>
    (S.model i).2.2.2.support.filter fun Q => c < (S.model i).2.2.2.coeff Q
  have hmemT : ∀ c : ℚ, 0 ≤ c → ∀ i Q, Q ∈ T c i ↔ c < (S.model i).2.2.2.coeff Q := by
    intro c hc i Q
    simp only [T, Finset.mem_filter, Finsupp.mem_support_iff, and_iff_right_iff_imp]
    intro h h0
    rw [DivisorWithCoeffs.coeff_apply, h0] at h
    exact absurd h (not_lt.2 hc)
  have hTstep : ∀ c : ℚ, 0 ≤ c → ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < S.length →
      ∀ Q : Mori.PrimeDivisor (S.model (i + 1)).1, Q ∈ T c (i + 1) ↔
        ∃ P ∈ T c i, Mori.RationalMap.transformPrimeDivisor (S.flipMap i) P = some Q := by
    intro c hc i _ Q
    rw [hmemT c hc]
    constructor
    · intro h
      refine ⟨(e i).symm Q, (hmemT c hc i _).2 ?_, by rw [he, Equiv.apply_symm_apply]⟩
      rwa [← hcoeff i, Equiv.apply_symm_apply]
    · rintro ⟨P, hP, hPQ⟩
      rw [he i P, Option.some_inj] at hPQ
      subst hPQ
      rw [hcoeff]
      exact (hmemT c hc i P).1 hP
  -- the reduced divisor `G c i` of the components of `D_i` of coefficient `c`
  let G : ℚ → ∀ i, Divisor (S.model i).1 := fun c i =>
    ∑ Q ∈ (S.model i).2.2.2.support.filter (fun Q => (S.model i).2.2.2.coeff Q = c),
      Finsupp.single Q 1
  have hGcoeff : ∀ c : ℚ, c ≠ 0 → ∀ i Q,
      (G c i).coeff Q = if (S.model i).2.2.2.coeff Q = c then 1 else 0 := by
    intro c hc i Q
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
    simp only [Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_filter]
    by_cases h : (S.model i).2.2.2.coeff Q = c
    · have h' : Q ∈ (S.model i).2.2.2.support := by
        rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, h]
        exact hc
      rw [if_pos ⟨h', h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2), if_neg h]
  have hG0 : ∀ c : ℚ, c ≠ 0 → MMP.Intersection.IsReducedEffective (G c 0) := by
    intro c hc P
    rw [hGcoeff c hc]
    split_ifs <;> simp
  have hGstep : ∀ c : ℚ, c ≠ 0 → ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < S.length →
      G c (i + 1) = Mori.RationalMap.transformDivisor (S.flipMap i) (G c i) := by
    intro c hc i _
    refine Finsupp.ext fun Q => ?_
    obtain ⟨P, rfl⟩ := (e i).surjective Q
    rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply,
      coeff_transformDivisor_apply (e i) (he i), hGcoeff c hc, hGcoeff c hc, hcoeff]
  -- the coefficients of `D`
  let V : Finset ℚ := (S.model 0).2.2.2.support.image (S.model 0).2.2.2.coeff
  have hV : ∀ (c : ℚ), 0 ≤ c → ∀ i (Q : Mori.PrimeDivisor (S.model i).1),
      c < (S.model i).2.2.2.coeff Q → (S.model i).2.2.2.coeff Q ∈ V.filter (c < ·) := by
    intro c hc i Q h
    obtain ⟨P, hP⟩ := hval i Q
    rw [hP] at h ⊢
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨P, Finsupp.mem_support_iff.2 ?_, rfl⟩, h⟩
    rw [← DivisorWithCoeffs.coeff_apply]
    exact (hc.trans_lt h).ne'
  -- Claim: eventually no flipping curve lies in a component of coefficient `> c`
  have hempty : ∀ c : ℚ, 0 ≤ c → V.filter (c < ·) = ∅ → ∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i →
      ((i + 1 : ℕ) : ℕ∞) < S.length → ∀ C : Set (S.model i).1,
        IsFlippingCurve k (S.model i).2.1 (S.baseStr i) (S.contraction i) C →
          ¬ C ⊆ ⋃ P ∈ T c i, (P.support : Set (S.model i).1) := by
    intro c hc h0
    refine ⟨0, fun i _ _ C hC hCsub => ?_⟩
    obtain ⟨-, -, -, -, z, -, hmax, -⟩ := hC
    obtain ⟨P, hP, -⟩ := exists_mem_subset_of_subset_biUnion hmax.1.1
      (fun P _ => P.idealSheaf.support.isClosed) hCsub
    have := hV c hc i P ((hmemT c hc i P).1 hP)
    rw [h0] at this
    simp at this
  have hA : ∀ n : ℕ, ∀ c : ℚ, 0 ≤ c → (V.filter (c < ·)).card ≤ n → ∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i →
      ((i + 1 : ℕ) : ℕ∞) < S.length → ∀ C : Set (S.model i).1,
        IsFlippingCurve k (S.model i).2.1 (S.baseStr i) (S.contraction i) C →
          ¬ C ⊆ ⋃ P ∈ T c i, (P.support : Set (S.model i).1) := by
    intro n
    induction n with
    | zero => exact fun c hc hn => hempty c hc (Finset.card_eq_zero.mp (Nat.le_zero.mp hn))
    | succ n ih =>
      intro c hc hn
      by_cases hne : (V.filter (c < ·)).Nonempty
      swap
      · exact hempty c hc (Finset.not_nonempty_iff_eq_empty.mp hne)
      -- `c'` is the least coefficient of `D` above `c`
      have hc'mem := Finset.min'_mem _ hne
      set c' := (V.filter (c < ·)).min' hne
      have hcc' : c < c' := (Finset.mem_filter.mp hc'mem).2
      have hc' : 0 ≤ c' := hc.trans hcc'.le
      have hc'0 : c' ≠ 0 := (hc.trans_lt hcc').ne'
      have hcard : (V.filter (c' < ·)).card ≤ n := by
        have hss : V.filter (c' < ·) ⊂ V.filter (c < ·) :=
          (Finset.ssubset_iff_of_subset fun x hx => by
            simp only [Finset.mem_filter] at hx ⊢
            exact ⟨hx.1, hcc'.trans hx.2⟩).2 ⟨c', hc'mem, by simp⟩
        have := Finset.card_lt_card hss
        omega
      obtain ⟨i₀, hi₀⟩ := ih c' hc' hcard
      obtain ⟨i₁, hi₁, hno⟩ := SequenceOfFlips.eventually_not_isFlippedCurveOf sX hD hDfloor hc' S
        (T c') (fun P hP => (hmemT c' hc' 0 P).2 hP) (hTstep c' hc') (hlen i₀) hi₀
      obtain ⟨i₂, hi₂, hno₂⟩ := SequenceOfFlips.exists_forall_not_subset_supp_of_isFlippingCurve
        S hX (G c') (hG0 c' hc'0) (hGstep c' hc'0) i₁ (by
          intro i hi hi1 C hC hCsub
          obtain ⟨-, -, -, -, z, -, hmax, -⟩ := hC.2
          rw [DivisorWithCoeffs.coe_supp] at hCsub
          obtain ⟨Q, hQ, hCQ⟩ := exists_mem_subset_of_subset_biUnion hmax.1.1
            (fun P _ => P.idealSheaf.support.isClosed) hCsub
          have hQc : (S.model (i + 1)).2.2.2.coeff Q = c' := by
            have hQ' := Finsupp.mem_support_iff.mp hQ
            rw [← DivisorWithCoeffs.coeff_apply, hGcoeff c' hc'0] at hQ'
            by_contra hne'
            exact hQ' (if_neg hne')
          exact hno i hi hi1 C hC (Or.inr ⟨Q, hQc.ge, hCQ⟩))
      refine ⟨i₂, fun i hi hi1 C hC hCsub => ?_⟩
      obtain ⟨-, -, -, -, z, -, hmax, -⟩ := id hC
      obtain ⟨P, hP, hCP⟩ := exists_mem_subset_of_subset_biUnion hmax.1.1
        (fun P _ => P.idealSheaf.support.isClosed) hCsub
      have hlt := (hmemT c hc i P).1 hP
      have hle : c' ≤ (S.model i).2.2.2.coeff P := Finset.min'_le _ _ (hV c hc i P hlt)
      rcases hle.lt_or_eq with h | h
      · exact hi₀ i (by omega) hi1 C hC (hCP.trans
          (Set.subset_biUnion_of_mem (u := fun P => (P.support : Set (S.model i).1))
            ((hmemT c' hc' i P).2 h)))
      · refine hno₂ i (by omega) hi1 C hC (hCP.trans (DivisorWithCoeffs.support_subset_supp ?_))
        rw [hGcoeff c' hc'0, if_pos h.symm]
        exact one_ne_zero
  -- with `c = 0`: eventually there is no flipped curve at all
  obtain ⟨i₀, hi₀⟩ := hA _ 0 le_rfl le_rfl
  obtain ⟨i₁, -, hno⟩ := SequenceOfFlips.eventually_not_isFlippedCurveOf sX hD hDfloor le_rfl S
    (T 0) (fun P hP => (hmemT 0 le_rfl 0 P).2 hP) (hTstep 0 le_rfl) (hlen i₀) hi₀
  haveI := S.isLocallyNoetherian_model i₁
  haveI := S.isNormal_model i₁
  haveI := S.compactSpace_model i₁
  haveI := hint i₁
  haveI := hlft i₁
  haveI := S.isLocallyNoetherian_model (i₁ + 1)
  haveI := S.isNormal_model (i₁ + 1)
  haveI := S.compactSpace_model (i₁ + 1)
  -- but the nontrivial flip `φ_{i₁}⁺` has a flipped curve
  have hE : logCanonicalDivisor (S.model i₁).2.2.1 (QDivisor.toRDivisor (S.model i₁).2.2.2) =
      QDivisor.toRDivisor (Divisor.toQDivisor (S.model i₁).2.2.1 + (S.model i₁).2.2.2) := by
    rw [map_add, QDivisor.toRDivisor_toQDivisor]
    rfl
  have hflip := S.isFlip i₁ (hlen _)
  rw [hE] at hflip
  obtain ⟨C, hC⟩ := IsFlip.exists_isFlippedCurveOf_of_not_isIso (hcan i₁).2.2.2.1 hflip
    (not_isIso_of_relativePicardNumber_eq_one _ _
      (S.isNegativeExtremalContraction i₁ (hlen _)).relativePicardNumber_eq_one)
  rw [← hE] at hC
  exact hno i₁ le_rfl (hlen _) C hC (Or.inl rfl)

end MMP.Flips

/-! ### Termination of flips for terminal threefold pairs -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips

open MMP.Mori

/-- **Termination of flips for terminal threefold pairs.** If `(Y, D)` is a terminal pair, with
`Y` a threefold over a field of characteristic zero, then every sequence of flips for `(Y, D)`
terminates (FA 6.9.1.2). -/
@[mmp "prop_fa6_terminal_flips_terminate"]
public theorem SequenceOfFlips.terminates_of_isTerminalPair {k : Type} [Field k] [CharZero k]
    {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [LocallyOfFiniteType sY] {K : Divisor Y} {D : QDivisor Y}
    (hY : topologicalKrullDim Y = 3) (hD : IsTerminalPair sY 3 K D)
    (S : SequenceOfFlips sY 3 K D) : S.Terminates := by
  obtain ⟨hX, hK, hDeff, hKD, hdisc⟩ := id hD
  exact S.terminates_of_isCanonicalPair sY ⟨hX, hK, hDeff, hKD, hdisc.le⟩
    (hD.roundDown_eq_zero (by norm_num))

end MMP.Flips

end
