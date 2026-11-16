module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.ScalingProgram.BoundaryRemovalThreshold
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.SupportSandwichFiniteRays
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeExtremalRays
public import MMP.AlgebraicGeometry.MMP.Contraction.DltStepPreserved
public import MMP.AlgebraicGeometry.MMP.Contraction.LineBundleDescent
public import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativeBasepointFree
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Contraction.KltRayContraction
public import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization
public import MMP.AlgebraicGeometry.MMP.Contraction.RayContractionAntiAmple
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
public import MMP.AlgebraicGeometry.Positivity.RelativeBigDecomposition
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
public import MMP.AlgebraicGeometry.MMP.Flip.ProcedureDatumExistence
public import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
public import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
public import MMP.AlgebraicGeometry.Singularities.BoundaryLowering
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.LcVerticalNegativeRay
public import MMP.AlgebraicGeometry.Singularities.DltKltShrinkBoundary
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.JunctionLabels
public import MMP.AlgebraicGeometry.MMP.Abundance.NumericalDimensionOnePencil
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Intersection.PicardNumberFiniteComplex
public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryStepPreserved
public import MMP.AlgebraicGeometry.MMP.Flip.PicardNumber
public import MMP.AlgebraicGeometry.MMP.Contraction.PicardNumberDropDlt
public import MMP.AlgebraicGeometry.Singularities.LogCanonicalOneResolution
public import MMP.AlgebraicGeometry.MMP.Fourfold.MinimalModel.LowerDimDltModel
public import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
public import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
public import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonCommonBase
public import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
public import MMP.AlgebraicGeometry.Resolution.StratumBlowupRelativelyAmple
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
public import MMP.AlgebraicGeometry.MMP.Contraction.NumericallyTrivialDescent
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltNegativeFace
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
public import MMP.AlgebraicGeometry.MMP.Flip.SmallAmpleModel
public import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
public import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
public import MMP.AlgebraicGeometry.Divisor.SectionZeroDivisor
public import MMP.AlgebraicGeometry.MMP.Contraction.SemiampleSupportingDivisor
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
public import MMP.AlgebraicGeometry.MMP.Flip.ProcedureDivisorSpan
public import MMP.AlgebraicGeometry.Singularities.FiniteLowDiscrepancyKlt

section

/-!
# Klt flips from the projective floor-program inputs

Assume the projective floor-program inputs `P(n)`. A small contraction `f : X ⟶ Z` of a
`(K + B)`-negative extremal ray of a `ℚ`-factorial projective klt complex `n`-fold `(X, B)` has a
flip. Following the source, two programs over the projective base `Z` produce a small
`ℚ`-factorial klt model `V ⟶ Z` of `X` on which `K + B` is nef over `Z`. Relative basepoint
freeness makes a Cartier multiple of `K_V + B_V` semiample over `Z`, so the divisorial algebra of
`f_*(r(K + B))` is finitely generated, and the flip is its relative `Proj`
(`MMP.Mori.exists_isFlip_iff_finiteType_divisorialAlgebraSections`).

## References

* [OpenAI, *Termination for projective log canonical fourfolds with rational boundary*][OAI4]
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold

namespace MMP.FourfoldProofs.FourfoldProjectiveKltFlipFromFloorInputsProof

/-- A `ℚ`-divisor has a positive integral multiple which is an integral divisor. -/
private theorem exists_toQDivisor_eq_natCast_smul {X : Scheme.{0}} (B : QDivisor X) :
    ∃ r : ℕ, 0 < r ∧ ∃ Dr : Divisor X, Divisor.toQDivisor Dr = (r : ℚ) • B := by
  classical
  refine ⟨∏ P ∈ B.support, (B P).den, Finset.prod_pos fun P _ => (B P).pos, ?_⟩
  set r := ∏ P ∈ B.support, (B P).den
  have hint : ∀ P, ∃ z : ℤ, (z : ℚ) = (r : ℚ) * B P := by
    intro P
    by_cases hP : P ∈ B.support
    · obtain ⟨c, hc⟩ : (B P).den ∣ r := Finset.dvd_prod_of_mem _ hP
      refine ⟨c * (B P).num, ?_⟩
      rw [hc]
      push_cast
      rw [mul_comm ((B P).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
    · exact ⟨0, by simp [Finsupp.notMem_support_iff.mp hP]⟩
  choose z hz using hint
  refine ⟨Finsupp.onFinset B.support z fun P hP => ?_, ?_⟩
  · by_contra h
    apply hP
    have := hz P
    rw [Finsupp.notMem_support_iff.mp h, mul_zero] at this
    exact_mod_cast this
  · ext P
    change ((Finsupp.onFinset B.support z _ P : ℤ) : ℚ) = _
    rw [Finsupp.onFinset_apply, hz]
    rfl

/-- A divisor regarded as a `ℚ`-divisor commutes with the birational transform `g⁻¹_* f_*`. -/
private theorem flipTransform_toQDivisor {X Y W : Scheme.{0}} (f : X ⟶ Y) (g : W ⟶ Y)
    (K : Divisor X) :
    flipTransform f g (Divisor.toQDivisor K) = Divisor.toQDivisor (flipTransform f g K) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, MMP.Flips.transformDivisor_toQDivisor,
    MMP.Threefold.Resolution.inverseTransformDivisor_toQDivisor]

/-- **The target of the contraction is projective.** The contraction of a `(K + B)`-negative
extremal ray `R` of a projective klt variety is isomorphic to the projective contraction of `R`
given by the contraction theorem: each factors through the other, uniquely. -/
private theorem isProjectiveVariety_target
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {B : QDivisor X} (hklt : IsKltPair sX B)
    {m : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX m)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f) :
    MMP.Mori.IsProjectiveVariety ℂ sZ := by
  obtain ⟨-, V, sV, q, hq, hVp, -, -⟩ := exists_isContractionOfRay_of_isKltPair sX hX hklt hK hR
  obtain ⟨-, hRe, -⟩ := hR
  have hXpm : IsProjectiveMorphism sX := ((MMP.Mori.isProjectiveVariety_iff _ _).mp hX).2
  obtain ⟨a, ha, -⟩ := existsUnique_comp_eq_of_isContractionOfRay hX hf.isProjectiveMorphism
    hf.comp_eq hRe (fun C hC => (hf.isContractedBy_iff C).mpr hC) hq
  obtain ⟨b, hb, -⟩ := existsUnique_comp_eq_of_isContractionOfRay hX hq.isProjectiveMorphism
    hq.comp_eq hRe (fun C hC => (hq.isContractedBy_iff C).mpr hC) hf
  obtain ⟨_, -, hqq⟩ := existsUnique_comp_eq_of_isContractionOfRay hX hq.isProjectiveMorphism
    hq.comp_eq hRe (fun C hC => (hq.isContractedBy_iff C).mpr hC) hq
  obtain ⟨_, -, hff⟩ := existsUnique_comp_eq_of_isContractionOfRay hX hf.isProjectiveMorphism
    hf.comp_eq hRe (fun C hC => (hf.isContractedBy_iff C).mpr hC) hf
  obtain ⟨_, -, hfs⟩ := existsUnique_comp_eq_of_isContractionOfRay hX hXpm (Category.comp_id _)
    hRe (fun C _ x _ => Subsingleton.elim _ _) hf
  have hab : a ≫ b = 𝟙 V :=
    (hqq _ (show q ≫ a ≫ b = q by rw [← Category.assoc, ha, hb])).trans (hqq _ (Category.comp_id q)).symm
  have hba : b ≫ a = 𝟙 Z :=
    (hff _ (show f ≫ b ≫ a = f by rw [← Category.assoc, hb, ha])).trans (hff _ (Category.comp_id f)).symm
  have hsZ : sZ = b ≫ sV :=
    (hfs _ hf.comp_eq).trans (hfs _ (show f ≫ b ≫ sV = sX by rw [← Category.assoc, hb, hq.comp_eq])).symm
  haveI : IsIso b := ⟨⟨a, hba, hab⟩⟩
  rw [hsZ]
  have hV := (MMP.Mori.isProjectiveVariety_iff _ _).mp hVp
  haveI := hV.1
  haveI : IsIntegral Z := hf.isNormalVariety_target.1.toIsIntegral
  exact (MMP.Mori.isProjectiveVariety_iff _ _).mpr
    ⟨(MMP.Mori.isVariety_iff _ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
      IsProjectiveMorphism.of_iso (asIso b).symm (Iso.refl _) (by simp) hV.2⟩

/-- **Relative Kleiman criterion for a ray contraction.** The contraction `c` onto a projective
variety of a `(K + Θ)`-negative extremal ray of a projective variety is `-(K + Θ)`-ample. -/
private theorem hasRelativelyAmpleMultiple_neg_of_isContractionOfRay
    {Y : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    {m : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY m) {Θ : QDivisor Y}
    {R : Set (NumericalCurveClasses sY)}
    (hR : IsNegativeExtremalRayOf sY (Divisor.toQDivisor K + Θ) R)
    {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    {c : Y ⟶ W} (hc : IsContractionOfRay sY sW R c) :
    (-(Divisor.toQDivisor K + Θ)).HasRelativelyAmpleMultiple c := by
  obtain ⟨hKΘ, hRe, hneg⟩ := hR
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  exact hasRelativelyAmpleMultiple_neg_of_isExtremalRay sY sW hc.isNormalVariety_source hY hW
    ⟨m, hK⟩ hKΘ hRe (fun v hv hv0 => by
      simpa [QDivisor.curveForm, Finsupp.sum, LinearMap.sum_apply] using hneg v hv hv0) c
    hc.comp_eq fun C hC => (hc.isContractedBy_iff C).mp hC

/-- **The flipping contraction.** The contraction of a `(K + B)`-negative extremal ray of a
projective klt variety is `-(K + B)`-ample. -/
private theorem hasRelativelyAmpleMultiple_neg
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {B : QDivisor X} (hklt : IsKltPair sX B)
    {m : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX m)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f) :
    (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple f :=
  hasRelativelyAmpleMultiple_neg_of_isContractionOfRay hX hK hR
    (isProjectiveVariety_target sX hX hklt hK hR sZ hf) hf

/-- **A contraction factors over the base.** If the contraction `c : Y ⟶ W` (with `c_* 𝒪_Y = 𝒪_W`)
factors `h = c ≫ d` and `h` lies over the base, then so does `d`: `c` is an epimorphism. -/
private theorem comp_eq_of_isContraction {Y W Z : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {c : Y ⟶ W} [IsProper c]
    (hc : IsContraction sY sW c) {d : W ⟶ Z} {h : Y ⟶ Z} (hcd : c ≫ d = h)
    (hh : h ≫ sZ = sY) : d ≫ sZ = sW := by
  haveI : IsIso c.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ c.c fun U => hc.isIso_app U.unop
  obtain ⟨e, -, he⟩ := MMP.existsUnique_comp_eq_of_isIso_c c (c ≫ sW) fun x x' hx => by
    simp only [Scheme.Hom.comp_apply, hx]
  refine (he _ ?_).trans (he _ rfl).symm
  change c ≫ d ≫ sZ = c ≫ sW
  rw [← Category.assoc, hcd, hh, hc.comp_eq]

/-- **Finite generation from a small model with a free multiple.** Let `g : W ⟶ Y` be a small
proper birational morphism of normal varieties and `B_Y` a divisor on `Y` some multiple of whose
birational transform is a `g`-free Cartier divisor. Then the divisorial algebra of `B_Y` is
finitely generated over every affine open of `Y` (KM 6.2, with a semiample in place of an ample
transform). -/
private theorem finiteType_of_isRelativelyFreeDivisor
    {W Y : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sW : W ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ)) (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (g : W ⟶ Y) (hg : g ≫ sY = sW)
    (hgb : IsBirationalMorphism g) (hEx : 2 ≤ closedsCodimension (exceptionalSet g))
    (BY : Divisor Y) {d : ℕ} (hd : 0 < d) (hL : Divisor.IsCartier (d • inverseTransformDivisor g BY))
    (hfree : IsRelativelyFreeDivisor g (d • inverseTransformDivisor g BY))
    (U : Y.Opens) (hU : IsAffineOpen U) :
    Algebra.FiniteType Γ(Y, U) (BY.divisorialAlgebraSections U) := by
  haveI : IsDominant g := hgb.isDominant
  haveI : IsSeparated sY := hY.toIsSeparated
  have hgp : IsProjectiveMorphism g := IsProjectiveMorphism.of_comp g sY (hg ▸ hW.isProjective)
  exact Divisor.finiteType_divisorialAlgebraSections_of_isRelativelyFreeDivisor g hgp.isProjective
    hEx BY hd hL hfree U hU

/-- A nonnegative rational multiple of a relatively nef `ℚ`-divisor is relatively nef. -/
private theorem isRelativelyNef_smul {V Y : Scheme.{0}} [IsLocallyNoetherian V] [IsNormal V]
    (sV : V ⟶ Spec (.of ℂ)) [QuasiCompact sV] {g : V ⟶ Y} {M : QDivisor V}
    (h : M.IsRelativelyNef sV g) {q : ℚ} (hq : 0 ≤ q) : (q • M).IsRelativelyNef sV g := by
  have hM := h.1
  have hqM := MMP.Flips.isQCartier_smul hM q
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sV hqM fun C hC => ?_
  rw [MMP.Fourfold.intersectionNumber_smul sV C.ι C.dim_le M hM q hqM]
  exact mul_nonneg hq (MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sV h hM C hC)

/-- On an integral proper scheme of dimension zero an invertible sheaf has a nonzero section. -/
private theorem finrank_ne_zero_of_dim_zero {κ : Type} [Field κ] {Z : Scheme.{0}}
    (g : Z ⟶ Spec (.of κ)) [IsProper g] [IsIntegral Z] [IsLocallyNoetherian Z]
    (hd : topologicalKrullDim Z = 0) (P : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 P] :
    Module.finrank κ (cohomologyOverField κ g P 0) ≠ 0 := by
  have hall : ∀ x : Z, x = genericPoint Z := by
    intro x
    have hmin := Order.krullDim_nonpos_iff_forall_isMin.1 (le_of_eq hd)
    let W : TopologicalSpace.IrreducibleCloseds Z :=
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
    let T : TopologicalSpace.IrreducibleCloseds Z :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩
    have hTW : T ≤ W := hmin T fun _ _ => Set.mem_univ _
    have hx : IsGenericPoint x ⊤ := by
      change closure {x} = Set.univ
      exact Set.eq_univ_of_univ_subset hTW
    exact hx.eq (genericPoint_spec Z)
  obtain ⟨U, -, e, hxU, he⟩ := MMP.Intersection.exists_isTrivializingGenerator P
    (show genericPoint Z ∈ (⊤ : Z.Opens) from trivial)
  have hU : U = ⊤ := eq_top_iff.2 fun y _ => by rwa [hall y]
  subst hU
  have he0 : e ≠ 0 := by
    intro h0
    exact one_ne_zero ((he ⊤ le_rfl).1 (a₁ := (1 : Γ(Z, ⊤))) (a₂ := 0) (by
      simp only [MMP.Intersection.modules_map_id, h0, smul_zero]))
  haveI : SheafOfModules.IsCoherent P :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Z P
  haveI := finiteDimensional_cohomologyOverField_of_isProper κ g P 0
  haveI : Nontrivial (cohomologyOverField κ g P 0) :=
    @Equiv.nontrivial _ _ (cohomologyOverFieldZeroIsoSections κ g P).toLinearEquiv.toEquiv
      ⟨⟨e, 0, he0⟩⟩
  exact (Module.finrank_pos (R := κ) (M := cohomologyOverField κ g P 0)).ne'

/-- For a birational morphism of integral schemes, the residue field at the generic point of the
source is algebraic (indeed equal) over that of its image. -/
private theorem residueFieldTranscendenceDegree_genericPoint_eq_zero {Y Z : Scheme.{0}}
    [IsIntegral Y] [IsIntegral Z] (h : Y ⟶ Z) (hb : IsBirationalMorphism h) :
    residueFieldTranscendenceDegree h (genericPoint Y) = 0 := by
  haveI : IsDominant h := hb.isDominant
  have hbij := hb.functionFieldMap_bijective
  have hn := AlgebraicGeometry.residueFieldMap_comp_genericResidueEquivOfDominant h
  have hsurj : Function.Surjective (h.residueFieldMap (genericPoint Y)).hom := by
    intro x
    obtain ⟨y, hy⟩ := hbij.surjective ((AlgebraicGeometry.genericResidueEquiv Y).symm x)
    refine ⟨AlgebraicGeometry.genericResidueEquivOfDominant h y, ?_⟩
    have := congrArg (fun φ => φ y) hn
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [this, hy]
    simp
  letI := (h.residueFieldMap (genericPoint Y)).hom.toAlgebra
  have : Algebra.IsAlgebraic (Z.residueField (h (genericPoint Y)))
      (Y.residueField (genericPoint Y)) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, rfl⟩ := hsurj x
    exact isAlgebraic_algebraMap a
  unfold residueFieldTranscendenceDegree
  rw [_root_.trdeg_eq_zero]
  simp

/-- **Every `ℚ`-Cartier divisor is big over a birational base.** For a birational morphism `h` of
projective varieties the generic fibre is a point, so `dim Y = dim h(Y)` and `h_* 𝒪_Y(D)` has
rank one generically for every Cartier divisor `D`. -/
private theorem isRelativelyBig_of_isBirationalMorphism {Y Z : Scheme.{0}} [IsIntegral Y]
    [IsIntegral Z] [IsLocallyNoetherian Y] [IsNormal Y] (sY : Y ⟶ Spec (.of ℂ))
    (sZ : Z ⟶ Spec (.of ℂ)) (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (h : Y ⟶ Z) (hf : h ≫ sZ = sY)
    (hb : IsBirationalMorphism h) {M : QDivisor Y} (hM : M.IsQCartier) :
    M.IsRelativelyBig h := by
  haveI := hY
  haveI := hZ
  haveI : IsProper (h ≫ sZ) := hf ▸ (inferInstance : IsProper sY)
  haveI : IsProper h := IsProper.of_comp h sZ
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hfib : topologicalKrullDim (h.fiber (h (genericPoint Y))) = 0 := by
    rw [MMP.Flips.topologicalKrullDim_fiber_genericPoint,
      residueFieldTranscendenceDegree_genericPoint_eq_zero h hb]
    rfl
  obtain ⟨a, ha⟩ : ∃ a : ℕ, topologicalKrullDim Y = a := by
    have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType ℂ sY
    have hbot : topologicalKrullDim Y ≠ ⊥ := fun hb =>
      ((Order.krullDim_eq_bot_iff.mp hb).false
        (TopologicalSpace.IrreducibleCloseds.closureSingleton (genericPoint Y))).elim
    induction hX : topologicalKrullDim Y using WithBot.recBotCoe with
    | bot => exact absurd hX hbot
    | coe a' =>
      have ha : a' ≠ ⊤ := by rintro rfl; exact h1 hX
      lift a' to ℕ using ha
      exact ⟨a', rfl⟩
  have hb' : topologicalKrullDim (closure (Set.range h.base)) = a := by
    have := MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range h ℂ sY sZ hf
    rw [hfib, zero_add, ha] at this
    exact this.symm
  obtain ⟨m, hm, E, hE, hEc⟩ := hM.exists_pos
  have hrank : ∀ j : ℤ, relativeGenericRank h (j • E).divisorialSheaf ≠ 0 := by
    intro j
    haveI := (hEc.zsmul j).isInvertibleModule_divisorialSheaf
    haveI : IsProper (h.fiberToSpecResidueField (h (genericPoint Y))) :=
      inferInstanceAs (IsProper (Limits.pullback.snd h (Z.fromSpecResidueField _)))
    haveI : IsIntegral (h.fiber (h (genericPoint Y))) := MMP.Mori.isIntegral_generic_fibre h
    haveI := isLocallyNoetherian_fiber_of_locallyOfFiniteType h (h (genericPoint Y))
    rw [MMP.Mori.relativeGenericRank_eq_finrank_fibre h]
    exact finrank_ne_zero_of_dim_zero _ hfib _
  refine ⟨m, hm, E, by rw [hE, natCast_zsmul, Nat.cast_smul_eq_nsmul], hEc, a, a, ha, hb', 1 / 2,
    by norm_num, 0,
    fun j _ => ?_⟩
  rw [Nat.sub_self, pow_zero, mul_one]
  have : (1 : ℝ) ≤ relativeGenericRank h (j • E).divisorialSheaf := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (hrank j)
  linarith

/-- **Relative basepoint freeness on the small model.** On a projective klt pair `(V, B_V)`
birational over a projective `Z`, with `K_V + B_V` nef over `Z`, every integral divisor `T`
with `T = r(K_V + B_V)` has a multiple which is a `g`-free Cartier divisor. -/
private theorem exists_isRelativelyFreeDivisor_nsmul
    {V Z : Scheme.{0}} [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    (sV : V ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [QuasiCompact sV]
    (hV : MMP.Mori.IsProjectiveVariety ℂ sV)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (g : V ⟶ Z) (hg : g ≫ sZ = sV)
    (hgb : IsBirationalMorphism g) {m : ℕ} {KV : Divisor V} {BV : QDivisor V}
    (hklt : MMP.Mori.IsKltPair sV m KV BV) (hBV : 0 ≤ BV)
    (hnef : (Divisor.toQDivisor KV + BV).IsRelativelyNef sV g)
    {r : ℕ} (hr : 0 < r) {T : Divisor V}
    (hT : Divisor.toQDivisor T = (r : ℚ) • (Divisor.toQDivisor KV + BV)) :
    ∃ d : ℕ, 0 < d ∧ Divisor.IsCartier (d • T) ∧ IsRelativelyFreeDivisor g (d • T) := by
  haveI : IsIntegral Z := ((MMP.Mori.isProjectiveVariety_iff _ _).mp hZ).1.toIsIntegral
  set M := Divisor.toQDivisor KV + BV with hMdef
  have hMq : M.IsQCartier := hklt.1.2.2
  obtain ⟨c, hc, E, hE, hEc⟩ := hMq.exists_pos
  -- `D = cT = rE` is Cartier, and `D = (c r) M`.
  have hcT : c • T = r • E := by
    apply Divisor.toQDivisor_injective
    rw [map_nsmul, map_nsmul, hT, hE, natCast_zsmul, smul_comm, Nat.cast_smul_eq_nsmul]
  have hDc : Divisor.IsCartier (c • T) := hcT ▸ hEc.nsmul r
  have hDM : Divisor.toQDivisor (c • T) = ((c * r : ℕ) : ℚ) • M := by
    rw [map_nsmul, hT, Nat.cast_mul, mul_smul]
    simp only [Nat.cast_smul_eq_nsmul]
  have hcr : (1 : ℚ) ≤ (c * r : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  have hDnef : (Divisor.toQDivisor (c • T)).IsRelativelyNef sV g := by
    rw [hDM]; exact isRelativelyNef_smul sV hnef (by positivity)
  have h2 : (2 : ℚ) • Divisor.toQDivisor (c • T) - Divisor.toQDivisor KV - BV =
      (2 * (c * r : ℕ) - 1 : ℚ) • M := by
    rw [hDM, smul_smul, sub_smul, one_smul, sub_sub, hMdef]
  have hsetting : IsProjectiveSetting ℂ sV sZ g :=
    ⟨Complex.isAlgClosed, inferInstance, hV, hZ, hg⟩
  obtain ⟨b₀, hb₀⟩ := exists_forall_ge_isRelativelyFreeDivisor_of_isKltPair hsetting hklt hBV hDc
    hDnef (a := 2) two_pos
    (by rw [h2]; exact isRelativelyNef_smul sV hnef (by linarith))
    (by
      rw [h2]
      exact isRelativelyBig_of_isBirationalMorphism sV sZ hV hZ g hg hgb
        (MMP.Flips.isQCartier_smul hMq _))
  refine ⟨(b₀ + 1) * c, Nat.mul_pos b₀.succ_pos hc, ?_, ?_⟩
  · rw [mul_smul]; exact hDc.nsmul _
  · have := hb₀ (b₀ + 1) (Nat.le_succ b₀)
    rwa [natCast_zsmul, smul_smul] at this

/-- The coefficients of a klt boundary lie in `[0, 1)`. -/
private theorem coeff_mem_Ico_of_isKltPair {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X} (hklt : IsKltPair sX B)
    (P : MMP.Mori.PrimeDivisor X) : 0 ≤ B.coeff P ∧ B.coeff P < 1 := by
  obtain ⟨-, m, K, hK, -⟩ := hklt.1.isPair
  have hM := (MMP.Fourfold.isKltPair_iff_mori_isKltPair sX hK hklt.1).mp hklt
  exact ⟨hklt.1.nonneg P, MMP.Mori.roundDown_nonpos_iff.mp hM.2.2 P⟩

/-- **A small morphism maps prime divisors onto prime divisors.** If the exceptional set of `f`
has codimension at least two, `f` maps the generic point of every prime divisor of `X` to the
generic point of a prime divisor of `Z`. -/
private theorem exists_map_genericPoint_eq_of_two_le_closedsCodimension {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] {f : X ⟶ Z} (h2 : 2 ≤ closedsCodimension (exceptionalSet f))
    (P : MMP.Mori.PrimeDivisor X) :
    ∃ Q : MMP.Mori.PrimeDivisor Z, f P.genericPoint = Q.genericPoint := by
  have hfx : f P.genericPoint ∈ MMP.Mori.biregularLocus f := by
    by_contra hn
    have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2
      (MMP.Mori.mem_exceptionalSet.mpr hn)
    rw [P.coheight_genericPoint] at this
    exact absurd this (by decide)
  have hco : Order.coheight (f P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hfx, P.coheight_genericPoint]
  exact ⟨_, (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm⟩

/-- **A small contraction is small in the sense of FA.** A proper birational morphism `f` of
normal varieties with `f_* 𝒪_X = 𝒪_Z` whose exceptional set has codimension at least two is an
isomorphism over the biregular locus `U ⊆ Z`, and `Z ∖ U` and `f⁻¹(Z ∖ U)` have codimension at
least two, because every point of codimension at most one of `Z`, and every such point of `X`
maps into `U`. -/
private theorem isSmall_of_isSmallMorphism {X Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {f : X ⟶ Z} (hc : IsContraction sX sZ f) (hsmall : IsSmallMorphism sX sZ f) :
    MMP.Flips.IsSmall ℂ sZ sX f := by
  have hZn := hc.isNormalVariety_target
  have hXn := hc.isNormalVariety_source
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI : IsNormal Z := hZn.2
  haveI := hZn.1
  haveI := hXn.1
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsProper f := hsmall.isProper
  have hfb := hsmall.isBirationalMorphism
  haveI : IsDominant f := hfb.isDominant
  have h2 := hsmall.two_le_codimension
  set U := MMP.Mori.biregularLocus f with hU
  have hUf : ∀ z : Z, Order.coheight z ≤ 1 → z ∈ U := fun z hz =>
    MMP.Positivity.mem_biregularLocus_of_coheight_le_one f hfb.functionFieldMap_bijective h2 hz
  have hcod : ∀ x : X, Order.coheight x ≤ 1 → x ∈ f ⁻¹ᵁ U := by
    intro x hx
    have hfx : f x ∈ MMP.Mori.biregularLocus f := by
      by_contra hn
      have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2
        (MMP.Mori.mem_exceptionalSet.mpr hn)
      exact absurd (this.trans hx) (by decide)
    exact hfx
  refine
    { isVariety_target := hZn.1
      isVariety_source := hXn.1
      comp_eq := hc.comp_eq
      isProper := inferInstance
      isIso_app := hc.isIso_app
      dim_eq := (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX hfb).symm
      exists_isIso := ⟨⟨((f ⁻¹ᵁ U : X.Opens) : Set X)ᶜ, (f ⁻¹ᵁ U).isOpen.isClosed_compl⟩,
        ⟨(U : Set Z)ᶜ, U.isOpen.isClosed_compl⟩,
        MMP.Flips.two_le_closedsCodimension_compl (f ⁻¹ᵁ U).isOpen hcod,
        MMP.Flips.two_le_closedsCodimension_compl U.isOpen hUf, ?_, ?_⟩ }
  · intro x hx
    have hx' : x ∈ ((f ⁻¹ᵁ U : X.Opens) : Set X) := by
      simpa using (show x ∈ ((((f ⁻¹ᵁ U : X.Opens) : Set X)ᶜ)ᶜ) from hx)
    show f x ∈ (((U : Set Z)ᶜ)ᶜ)
    simpa using hx'
  · have e1 : (⟨((f ⁻¹ᵁ U : X.Opens) : Set X)ᶜ, (f ⁻¹ᵁ U).isOpen.isClosed_compl⟩ :
        TopologicalSpace.Closeds X).compl = f ⁻¹ᵁ U := by
      ext x; simp
    have e2 : (⟨(U : Set Z)ᶜ, U.isOpen.isClosed_compl⟩ :
        TopologicalSpace.Closeds Z).compl = U := by
      ext x; simp
    have key : ∀ (A : X.Opens) (B : Z.Opens) (_ : A = f ⁻¹ᵁ U) (_ : B = U)
        (h : A ≤ f ⁻¹ᵁ B), IsIso (f.resLE B A h) := by
      rintro A B rfl rfl h
      rw [Scheme.Hom.resLE_eq_morphismRestrict]
      exact MMP.Mori.isBiregular_biregularLocus f
    exact key _ _ e1 e2 _

/-- **The procedure datum** of the small contraction `f` (FA 18.12.1): it exists because `f` is
a small projective contraction of normal varieties onto the projective `Z`. -/
private theorem nonempty_procedureDatum
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) {B : QDivisor X} (hklt : IsKltPair sX B)
    {R : Set (NumericalCurveClasses sX)}
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) [IsLocallyNoetherian Z] [IsNormal Z]
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f) (hsmall : IsSmallMorphism sX sZ f) :
    Nonempty (MMP.Flips.ProcedureDatum ℂ sZ (QDivisor.toRDivisor B) f) := by
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  haveI := hZ
  refine MMP.Flips.ProcedureDatum.nonempty hf.isNormalVariety_source (fun P => ?_)
    (isSmall_of_isSmallMorphism hf.toIsContraction hsmall) hf.isProjectiveMorphism
    (AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ sZ)
  have := coeff_mem_Ico_of_isKltPair hklt P
  rw [QDivisor.coeff_toRDivisor]
  exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2.le⟩

/-- The push-forward `f_* B` of a klt boundary along a small contraction has coefficients in
`[0, 1)` and no component in common with the divisor `H'` of a procedure datum. -/
private theorem coeff_transformDivisor_of_procedureDatum
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) {B : QDivisor X} (hklt : IsKltPair sX B)
    {R : Set (NumericalCurveClasses sX)}
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) [IsLocallyNoetherian Z] [IsNormal Z]
    {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f) (hsmall : IsSmallMorphism sX sZ f)
    (P : MMP.Flips.ProcedureDatum ℂ sZ (QDivisor.toRDivisor B) f) :
    (∀ Q, 0 ≤ (RationalMap.transformDivisor f.toRationalMap B).coeff Q ∧
      (RationalMap.transformDivisor f.toRationalMap B).coeff Q < 1) ∧
    ∀ Q, P.H'.coeff Q ≠ 0 → (RationalMap.transformDivisor f.toRationalMap B).coeff Q = 0 := by
  haveI : IsIntegral Z := hf.isNormalVariety_target.1.toIsIntegral
  haveI := isSeparated_toTerminal_of_isNormalVariety hf.isNormalVariety_target
  haveI : IsProper f := hsmall.isProper
  have hfb := hsmall.isBirationalMorphism
  -- the coefficient of `f_* B` at `Q` is that of `B` at the prime divisor over `Q`, if any
  have key : ∀ Q : MMP.Mori.PrimeDivisor Z,
      (RationalMap.transformDivisor f.toRationalMap B).coeff Q = 0 ∨
        ∃ E : MMP.Mori.PrimeDivisor X, f E.genericPoint = Q.genericPoint ∧
          (RationalMap.transformDivisor f.toRationalMap B).coeff Q = B.coeff E := by
    intro Q
    by_cases h : ∃ E : MMP.Mori.PrimeDivisor X, f E.genericPoint = Q.genericPoint
    · obtain ⟨E, hE⟩ := h
      exact Or.inr ⟨E, hE, MMP.Fourfold.Oai4C1.transformDivisor_apply_of_map_genericPoint hfb hE B⟩
    · refine Or.inl (MMP.Fourfold.Oai4C1.mapPrimeDivisors_apply_eq_zero (fun E hE => h ⟨E, ?_⟩) B)
      exact (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f E Q).mp hE
  refine ⟨fun Q => ?_, fun Q hQ => ?_⟩
  · rcases key Q with h | ⟨E, -, h⟩
    · rw [h]; exact ⟨le_rfl, one_pos⟩
    · rw [h]; exact coeff_mem_Ico_of_isKltPair hklt E
  · rcases key Q with h | ⟨E, hE, h⟩
    · exact h
    · rw [h]
      by_contra hB
      have hlt := (coeff_mem_Ico_of_isKltPair hklt E).2
      refine P.image_ne_component Q hQ E (by simpa using hB)
        (by rw [QDivisor.coeff_toRDivisor]; exact_mod_cast hlt) ?_
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        ← f.isClosedMap.closure_image_eq_of_continuous f.continuous, Set.image_singleton]
      exact congrArg (fun x => closure {x}) hE

/-- The identity of a normal variety is a small morphism. -/
private theorem isSmallMorphism_id {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)}
    (hW : IsNormalVariety ℂ sW) : IsSmallMorphism sW sW (𝟙 W) := by
  refine ⟨hW, hW, Category.id_comp _, inferInstance, isBirationalMorphism_of_isIso _, ?_⟩
  rw [le_closedsCodimension_iff]
  intro V hV
  exfalso
  obtain ⟨x, hx⟩ := V.isIrreducible.nonempty
  have hx' := hV hx
  rw [SetLike.mem_coe, mem_exceptionalSet] at hx'
  exact hx' (le_biregularLocus ((isBiregular_top_iff _).mpr inferInstance) trivial)

/-- **Every prime divisor of the base has a prime divisor over it.** For a proper birational
morphism `g : A ⟶ Z` onto a normal variety, every prime divisor `Q` of `Z` is the image of a
prime divisor `P` of `A`: `g(η_P) = η_Q`. -/
private theorem exists_primeDivisor_map_genericPoint_eq {A Z : Scheme.{0}} [IsIntegral A]
    [IsLocallyNoetherian A] [IsNormal A] [IsIntegral Z] {sZ : Z ⟶ Spec (.of ℂ)}
    (hZn : IsNormalVariety ℂ sZ) {g : A ⟶ Z} [IsProper g] (hg : IsBirationalMorphism g)
    (Q : MMP.Mori.PrimeDivisor Z) : ∃ P : MMP.Mori.PrimeDivisor A, g P.genericPoint = Q.genericPoint := by
  haveI := hZn.1
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsNormal Z := hZn.2
  obtain ⟨P, Q', -, hP, hQ⟩ :=
    exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hZn hg (isSmallMorphism_id hZn) Q
  refine ⟨P, (map_genericPoint_eq_of_image_eq P Q' hP).trans ?_⟩
  have := map_genericPoint_eq_of_image_eq (f := 𝟙 Z) Q Q' hQ
  exact this.symm

/-- The transform of a prime divisor along a morphism depends only on the image of its generic
point. -/
private theorem transformPrimeDivisor_eq_of_map_genericPoint_eq {A A' Z : Scheme.{0}}
    [IsReduced A] [IsReduced A'] [IsSeparated (Z ↘ Limits.terminal Scheme)] {a : A ⟶ Z}
    {a' : A' ⟶ Z} {P : MMP.Mori.PrimeDivisor A} {P' : MMP.Mori.PrimeDivisor A'}
    (h : a P.genericPoint = a' P'.genericPoint) :
    RationalMap.transformPrimeDivisor a.toRationalMap P =
      RationalMap.transformPrimeDivisor a'.toRationalMap P' := by
  refine Option.ext fun Q => ?_
  rw [MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff,
    MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff, h]

/-- The restriction of an snc divisor to an open subscheme is snc. -/
private theorem isSNC_restrictOpen {R : Type*} [Zero R] {X Y : Scheme.{0}} {g : X ⟶ Y}
    [∀ E : MMP.Mori.PrimeDivisor X, LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ g)]
    {D : DivisorWithCoeffs R X} (hD : D.IsSNC g) (U : X.Opens) :
    (D.restrictOpen U).IsSNC (U.ι ≫ g) := by
  refine ⟨fun E₀ hE₀ => ?_, fun x => ?_⟩
  · have hDE : D (OpenWeilRestriction.primeDivisorMap U.ι E₀) ≠ 0 := by
      have := Finsupp.mem_support_iff.mp hE₀; exact this
    have hsm := hD.1 _ (Finsupp.mem_support_iff.mpr hDE)
    refine (MMP.Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff U.ι g _ E₀.idealSheaf
      (MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap U.ι E₀)).mpr
      fun z _ => ?_
    have : ((OpenWeilRestriction.primeDivisorMap U.ι E₀).idealSheaf.subschemeι ≫ g).smoothLocus
        = ⊤ := by
      rwa [← MMP.Mori.smoothLocus_eq_smoothLocus]
    rw [this]
    trivial
  · exact (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff U.ι D x).mpr (hD.2 (U.ι x))

/-! ### Running programs -/

/-- **Termination by a decreasing invariant and a terminating step relation.** Suppose that at
every good state which is not a stopping state there is a step to a good state which either
lowers a well-founded invariant `ρ` or keeps it and is a `Flip`-step, and that there is no
infinite sequence of good states linked by `Flip`-steps. Then every good state reaches a good
stopping state. -/
private theorem exists_stop_of_step {α : Type*} {good stop : α → Prop} (ρ : α → ℕ∞)
    {Flip : α → α → Prop}
    (hstep : ∀ s, good s → ¬ stop s → ∃ t, good t ∧ (ρ t < ρ s ∨ (ρ t = ρ s ∧ Flip s t)))
    (hterm : ∀ u : ℕ → α, (∀ i, good (u i)) → ¬ ∀ i, Flip (u i) (u (i + 1)))
    (s : α) (hs : good s) : ∃ t, good t ∧ stop t := by
  by_contra hne
  push Not at hne
  have key : ∀ s : {s // good s}, ∃ t : {t // good t},
      ρ t < ρ s ∨ (ρ t = ρ s ∧ Flip s t) := fun s => by
    obtain ⟨t, ht, h⟩ := hstep s.1 s.2 (hne s.1 s.2)
    exact ⟨⟨t, ht⟩, h⟩
  choose next hnext using key
  let u : ℕ → {s // good s} := fun i => next^[i] ⟨s, hs⟩
  have hu : ∀ i, u (i + 1) = next (u i) := fun i => Function.iterate_succ_apply' _ _ _
  have hanti : Antitone (fun i => ρ (u i)) := antitone_nat_of_succ_le fun i => by
    rw [hu]
    rcases hnext (u i) with h | h
    · exact h.le
    · exact h.1.le
  obtain ⟨N, hN⟩ := WellFoundedLT.antitone_chain_condition hanti
  refine hterm (fun i => (u (N + i)).1) (fun i => (u (N + i)).2) fun i => ?_
  have h := hnext (u (N + i))
  rw [← hu] at h
  rcases h with h | h
  · exfalso
    have h1 : ρ (u N).1 = ρ (u (N + i)).1 := hN _ (by omega)
    have h2 : ρ (u N).1 = ρ (u (N + i + 1)).1 := hN _ (by omega)
    rw [← h1, ← h2] at h
    exact lt_irrefl _ h
  · exact h.2

/-- A model of the two programs over `Z`: a variety `Y` with a morphism `h : Y ⟶ Z`, a canonical
divisor `K` and two `ℚ`-divisors `D`, `G`. -/
private structure Stage (Z : Scheme.{0}) where
  Y : Scheme.{0}
  [isIntegral : IsIntegral Y]
  [compactSpace : CompactSpace Y]
  [isLocallyNoetherian : IsLocallyNoetherian Y]
  [isNormal : IsNormal Y]
  sY : Y ⟶ Spec (.of ℂ)
  h : Y ⟶ Z
  K : Divisor Y
  D : QDivisor Y
  G : QDivisor Y

attribute [local instance] Stage.isIntegral Stage.compactSpace Stage.isLocallyNoetherian
  Stage.isNormal

/-- The invariants shared by all models of the two programs, for the divisor `H'` of a
procedure datum on `Z` and the push-forwards `K_Z = f_* K`, `B_Z = f_* B`: `Y` is a projective
`ℚ`-factorial `n`-fold, `h` is projective and birational, every `h`-exceptional prime divisor
lies over `H'`, `h_* K = K_Z`, and `D = h⁻¹_* B_Z + ∑ E`, `G = h⁻¹_* H'`, the sum over the
`h`-exceptional prime divisors `E`. -/
private structure Stage.IsAdmissible {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (n : ℕ)
    [IsLocallyNoetherian Z] [IsNormal Z] (H' KZ : Divisor Z) (BZ : QDivisor Z)
    (s : Stage Z) : Prop where
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety ℂ s.sY
  dim_eq : topologicalKrullDim s.Y = n
  isQFactorial : IsQFactorial s.sY
  isCanonicalDivisor : ∃ m : ℕ, s.K.IsCanonicalDivisor s.sY m
  comp_eq : s.h ≫ sZ = s.sY
  isProjectiveMorphism : IsProjectiveMorphism s.h
  isBirationalMorphism : IsBirationalMorphism s.h
  exceptional_mem : ∀ P : MMP.Mori.PrimeDivisor s.Y,
    RationalMap.transformPrimeDivisor s.h.toRationalMap P = none → s.h P.genericPoint ∈ H'.supp
  transformDivisor_K : RationalMap.transformDivisor s.h.toRationalMap s.K = KZ
  coeff_D : ∀ P, s.D.coeff P =
    (RationalMap.transformPrimeDivisor s.h.toRationalMap P).elim 1 BZ.coeff
  coeff_G : ∀ P, s.G.coeff P =
    (RationalMap.transformPrimeDivisor s.h.toRationalMap P).elim 0 fun Q => (H'.coeff Q : ℚ)

section Admissible

variable {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} {n : ℕ} [IsLocallyNoetherian Z] [IsNormal Z]
  {H' KZ : Divisor Z} {BZ : QDivisor Z} {s : Stage Z}

/-- The boundary `D` of an admissible model is effective when `B_Z` is. -/
private theorem Stage.IsAdmissible.coeff_D_nonneg (hs : s.IsAdmissible sZ n H' KZ BZ)
    (hBZ : ∀ Q, 0 ≤ BZ.coeff Q) (P : MMP.Mori.PrimeDivisor s.Y) : 0 ≤ s.D.coeff P := by
  rw [hs.coeff_D]
  cases RationalMap.transformPrimeDivisor s.h.toRationalMap P with
  | none => exact zero_le_one
  | some Q => exact hBZ Q

/-- The coefficients of `G` on an admissible model are `0` or `1` when `H'` is reduced. -/
private theorem Stage.IsAdmissible.coeff_G_mem (hs : s.IsAdmissible sZ n H' KZ BZ)
    (hH'r : ∀ Q, H'.coeff Q = 0 ∨ H'.coeff Q = 1) (P : MMP.Mori.PrimeDivisor s.Y) :
    s.G.coeff P = 0 ∨ s.G.coeff P = 1 := by
  rw [hs.coeff_G]
  cases RationalMap.transformPrimeDivisor s.h.toRationalMap P with
  | none => exact Or.inl rfl
  | some Q => rcases hH'r Q with h | h <;> simp [h]

/-- `0 ≤ D + t G ≤ D + G` for `0 ≤ t ≤ 1` on an admissible model. -/
private theorem Stage.IsAdmissible.nonneg_and_le_add_smul (hs : s.IsAdmissible sZ n H' KZ BZ)
    (hBZ : ∀ Q, 0 ≤ BZ.coeff Q) (hH'r : ∀ Q, H'.coeff Q = 0 ∨ H'.coeff Q = 1) {t : ℚ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ s.D + t • s.G ∧ s.D + t • s.G ≤ s.D + s.G := by
  refine ⟨fun P => ?_, fun P => ?_⟩
  · have h1 := hs.coeff_D_nonneg hBZ P
    have h2 : 0 ≤ s.G.coeff P := by rcases hs.coeff_G_mem hH'r P with h | h <;> rw [h] <;> norm_num
    change (0 : ℚ) ≤ s.D P + t * s.G P
    exact add_nonneg h1 (mul_nonneg ht0 h2)
  · have h2 : 0 ≤ s.G.coeff P := by rcases hs.coeff_G_mem hH'r P with h | h <;> rw [h] <;> norm_num
    change s.D P + t * s.G P ≤ s.D P + s.G P
    have : t * s.G P ≤ s.G P := mul_le_of_le_one_left h2 ht1
    linarith

end Admissible

/-- **The initial model.** A projective log resolution `g : Y ⟶ X` of `B` and `f^* H'` which is
an isomorphism over `Z ∖ H'`, with `D = g⁻¹_* B + ∑ E` and `G` the strict transform of
`Supp f^* H'`, is an admissible model with `(Y, D + G)` dlt. -/
private theorem exists_initialStage
    {n : ℕ} {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    (hdim : topologicalKrullDim X = n) {B : QDivisor X} (hklt : IsKltPair sX B)
    {m : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX m)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) [IsLocallyNoetherian Z] [IsNormal Z]
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f)
    (hsmall : IsSmallMorphism sX sZ f)
    (P : MMP.Flips.ProcedureDatum ℂ sZ (QDivisor.toRDivisor B) f)
    (hBZ : ∀ Q, 0 ≤ (RationalMap.transformDivisor f.toRationalMap B).coeff Q ∧
      (RationalMap.transformDivisor f.toRationalMap B).coeff Q < 1)
    (hBH : ∀ Q, P.H'.coeff Q ≠ 0 → (RationalMap.transformDivisor f.toRationalMap B).coeff Q = 0) :
    ∃ s : Stage Z, s.IsAdmissible sZ n P.H' (RationalMap.transformDivisor f.toRationalMap K)
        (RationalMap.transformDivisor f.toRationalMap B) ∧
      MMP.Intersection.IsDltPair s.sY (s.D + s.G) := by
  classical
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  have hXn := hf.isNormalVariety_source
  have hZn := hf.isNormalVariety_target
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI := hZn.1
  haveI := hXn.1
  haveI : LocallyOfFiniteType sX := hXn.1.toLocallyOfFiniteType
  haveI : IsProper f := hsmall.isProper
  have hfb := hsmall.isBirationalMorphism
  haveI : IsDominant f := hfb.isDominant
  have hfS := isSmall_of_isSmallMorphism hf.toIsContraction hsmall
  have hB := MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f P.H'
  have hH : P.H'.IsPullback f hB (P.H'.pullback P.isCartier_H' hB) :=
    Divisor.isPullback_pullback P.isCartier_H' hB
  have hlogv : MMP.Flips.IsLogVariety ℂ sX (QDivisor.toRDivisor B) := ⟨hXn, fun Q => by
    have := coeff_mem_Ico_of_isKltPair hklt Q
    rw [QDivisor.coeff_toRDivisor]
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2.le⟩⟩
  haveI := hZ
  obtain ⟨Y, g, hlog, hgp, hiso⟩ := P.exists_isLogResolution_isIso_restrict hlogv hfS
    hf.isProjectiveMorphism (AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ sZ) hH
  obtain ⟨-, hYv, hYsm, hgP, hgb, Gs, hGs01, hGsiff, hGsnc⟩ := hlog
  haveI : IsIntegral Y := hYv.toIsIntegral
  haveI : LocallyOfFiniteType (g ≫ sX) := hYv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  haveI : IsNormal Y :=
    isNormal_of_isRegular Y (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme hYsm)
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  haveI : IsDominant g := hgb.isDominant
  have hYn : IsNormalVariety ℂ (g ≫ sX) := ⟨hYv, inferInstance⟩
  -- the canonical divisor `K_Y` with `g_* K_Y = K`, from one of the smooth variety `Y`
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme
    (g ≫ sX) hYsm (n := m) (by
      rw [← hK.topologicalKrullDim_eq]
      exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (g ≫ sX) hgb).symm)
  obtain ⟨KY, hKY, hKYg⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hXn hYn hgb hK hK₀
  -- the boundaries `D = h⁻¹_* B_Z + ∑ E` and `G = h⁻¹_* H'`
  set h := g ≫ f with hh
  have hsupp : ∀ E : MMP.Mori.PrimeDivisor Y,
      ((RationalMap.transformPrimeDivisor h.toRationalMap E).elim 1
          (RationalMap.transformDivisor f.toRationalMap B).coeff ≠ 0 ∨
        (RationalMap.transformPrimeDivisor h.toRationalMap E).elim 0
          (fun Q => (P.H'.coeff Q : ℚ)) ≠ 0) → E ∈ Gs.support := by
    intro E hE
    haveI : IsProper g := hgP
    haveI := isSeparated_toTerminal_of_isNormalVariety hZn
    rw [Finsupp.mem_support_iff]
    suffices h1 : Gs.coeff E = 1 by
      change Gs.coeff E ≠ 0; rw [h1]; exact one_ne_zero
    rw [hGsiff]
    by_contra hcon
    push Not at hcon
    obtain ⟨hinv, hexc⟩ := hcon
    obtain ⟨PX, hPX, -, -⟩ :=
      MMP.Fourfold.exists_transformDivisor_apply_eq_of_not_isExceptionalPrimeDivisor hXn g hYn hgb
        E hexc
    obtain ⟨Q, hPXQ⟩ :=
      exists_map_genericPoint_eq_of_two_le_closedsCodimension hsmall.two_le_codimension PX
    have hEQ : h E.genericPoint = Q.genericPoint := by
      rw [hh, Scheme.Hom.comp_apply, hPX, hPXQ]
    rw [(MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff h E Q).mpr hEQ] at hE
    simp only [Option.elim] at hE
    rw [DivisorWithCoeffs.coeff_apply,
      MMP.Flips.birationalInverseTransform_apply_of_genericPoint_eq hXn g hYv hgb _ hPX,
      Finsupp.sup_apply] at hinv
    rcases hE with hb | hq
    · rw [DivisorWithCoeffs.coeff_apply,
        MMP.Fourfold.Oai4C1.transformDivisor_apply_of_map_genericPoint hfb hPXQ B] at hb
      have hB0 := (coeff_mem_Ico_of_isKltPair hklt PX).1
      have hpos : (0 : ℝ) < (B.coeff PX : ℝ) := by
        exact_mod_cast lt_of_le_of_ne hB0 (Ne.symm hb)
      have h1 : (QDivisor.toRDivisor B) PX ≤ _ := le_sup_left (b := (Divisor.toRDivisor
        (MMP.Intersection.reducedDivisorOf (P.H'.pullback P.isCartier_H' hB).support)) PX)
      rw [hinv, ← DivisorWithCoeffs.coeff_apply (QDivisor.toRDivisor B),
        QDivisor.coeff_toRDivisor] at h1
      linarith
    · have hq' : P.H'.coeff Q ≠ 0 := by exact_mod_cast hq
      have hHe : DivisorWithCoeffs.IsEffective P.H' := fun E => by
        rcases P.isReduced_H' E with h | h <;> simp [h]
      have hQs : Q.genericPoint ∈ P.H'.supp :=
        DivisorWithCoeffs.mem_supp_iff.mpr ⟨Q, hq', MMP.Positivity.PrimeDivisor.genericPoint_mem_support' Q⟩
      have hPXs : PX.genericPoint ∈ ((P.H'.pullback P.isCartier_H' hB).supp : Set X) := by
        rw [MMP.Flips.supp_eq_preimage_supp_of_isPullback P.isCartier_H' hHe hH]
        change f PX.genericPoint ∈ P.H'.supp
        rwa [hPXQ]
      obtain ⟨E', hE'0, hE'⟩ := DivisorWithCoeffs.mem_supp_iff.mp hPXs
      obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hE'
      have h1 : (Divisor.toRDivisor (MMP.Intersection.reducedDivisorOf
          (P.H'.pullback P.isCartier_H' hB).support)) E' ≤ _ :=
        le_sup_right (a := (QDivisor.toRDivisor B) E')
      rw [hinv, ← DivisorWithCoeffs.coeff_apply (Divisor.toRDivisor _) E',
        Divisor.coeff_toRDivisor, MMP.Intersection.coeff_reducedDivisorOf,
        if_pos (Finsupp.mem_support_iff.mpr hE'0)] at h1
      norm_num at h1
  let D₀ : QDivisor Y := Finsupp.onFinset Gs.support
    (fun E => (RationalMap.transformPrimeDivisor h.toRationalMap E).elim 1
      (RationalMap.transformDivisor f.toRationalMap B).coeff) fun E hE => hsupp E (Or.inl hE)
  let G₀ : QDivisor Y := Finsupp.onFinset Gs.support
    (fun E => (RationalMap.transformPrimeDivisor h.toRationalMap E).elim 0
      fun Q => (P.H'.coeff Q : ℚ)) fun E hE => hsupp E (Or.inr hE)
  haveI := isSeparated_toTerminal_of_isNormalVariety hZn
  haveI : IsProper g := hgP
  have hhb : IsBirationalMorphism h := MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hgb hfb
  have hhp : IsProjectiveMorphism h := hgp.comp hf.isProjectiveMorphism
  haveI : IsProper h := isProper_of_isProjectiveMorphism _ hhp
  haveI : IsDominant h := hhb.isDominant
  -- the prime divisor of `X` under a prime divisor of `Y` over `Q`
  have hunder : ∀ (E : MMP.Mori.PrimeDivisor Y) (Q : MMP.Mori.PrimeDivisor Z),
      h E.genericPoint = Q.genericPoint → ∃ PX : MMP.Mori.PrimeDivisor X,
        g E.genericPoint = PX.genericPoint ∧ f PX.genericPoint = Q.genericPoint := by
    intro E Q hPQ
    obtain ⟨PX, hPX⟩ := exists_primeDivisor_map_genericPoint_eq hZn hfb Q
    have := Q.isDiscreteValuationRing_localRing
    exact ⟨PX, eq_of_map_eq_of_valuationRing hfb.functionFieldMap_bijective hPQ hPX, hPX⟩
  refine ⟨⟨Y, g ≫ sX, h, KY, D₀, G₀⟩,
    { isProjectiveVariety := (MMP.Mori.isProjectiveVariety_iff _ _).mpr
        ⟨hYv, hgp.comp ((MMP.Mori.isProjectiveVariety_iff _ _).mp hX).2⟩
      dim_eq := by
        change topologicalKrullDim Y = n
        rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (g ≫ sX) hgb,
          hdim]
      isQFactorial := ⟨hYn, fun D => ⟨1, one_pos, by
        simpa using MMP.Fourfold.isCartier_of_isSmoothScheme hYsm D⟩⟩
      isCanonicalDivisor := ⟨m, hKY⟩
      comp_eq := by
        change (g ≫ f) ≫ sZ = g ≫ sX
        rw [Category.assoc, hf.comp_eq]
      isProjectiveMorphism := hhp
      isBirationalMorphism := hhb
      exceptional_mem := fun E hE => ?_
      transformDivisor_K := ?_
      coeff_D := fun _ => rfl
      coeff_G := fun _ => rfl }, ?_⟩
  · -- `h` is an isomorphism over `Z ∖ H'`
    by_contra hPH
    have hU : IsBiregular h P.H'.supp.compl := hiso
    have hmem : h E.genericPoint ∈ MMP.Mori.biregularLocus h := le_biregularLocus hU hPH
    have hco : Order.coheight (h E.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus h hmem, E.coheight_genericPoint]
    have := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff h E
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco)).mpr
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm
    change RationalMap.transformPrimeDivisor h.toRationalMap E = none at hE
    rw [hE] at this
    cases this
  · -- `h_* K_Y = f_* K`
    refine Finsupp.ext fun Q => ?_
    obtain ⟨E, hPQ⟩ := exists_primeDivisor_map_genericPoint_eq hZn hhb Q
    obtain ⟨PX, hPX, hPXQ⟩ := hunder E Q hPQ
    change RationalMap.transformDivisor h.toRationalMap KY Q = _
    haveI := isSeparated_toTerminal_of_isNormalVariety hXn
    rw [MMP.Fourfold.Oai4C1.transformDivisor_apply_of_map_genericPoint hhb hPQ,
      MMP.Fourfold.Oai4C1.transformDivisor_apply_of_map_genericPoint hfb hPXQ, ← hKYg,
      MMP.Fourfold.Oai4C1.transformDivisor_apply_of_map_genericPoint hgb hPX]
  · -- `(Y, D + G)` is dlt: `Y` is smooth and `D + G` is supported on the snc divisor `G_s`
    have hΘ01 : ∀ E : MMP.Mori.PrimeDivisor Y,
        0 ≤ (D₀ + G₀).coeff E ∧ (D₀ + G₀).coeff E ≤ 1 := by
      intro E
      change 0 ≤ D₀ E + G₀ E ∧ D₀ E + G₀ E ≤ 1
      simp only [D₀, G₀, Finsupp.onFinset_apply]
      cases RationalMap.transformPrimeDivisor h.toRationalMap E with
      | none => norm_num
      | some Q =>
        simp only [Option.elim]
        obtain ⟨h0, h1⟩ := hBZ Q
        rcases P.isReduced_H' Q with hq | hq
        · rw [hq]; push_cast; constructor <;> linarith
        · rw [hq, hBH Q (by rw [hq]; exact one_ne_zero)]; norm_num
    have hsuppΘ : (D₀ + G₀).support ⊆ Gs.support := by
      intro E hE
      refine hsupp E ?_
      by_contra hne
      push Not at hne
      apply Finsupp.mem_support_iff.mp hE
      change D₀ E + G₀ E = 0
      simp only [D₀, G₀, Finsupp.onFinset_apply, hne.1, hne.2, add_zero]
    have hsncΘ : (D₀ + G₀).IsSNC (g ≫ sX) :=
      (MMP.Flips.IsSNCDivisor.isSNC hYv hYsm hGsnc).of_support_subset hsuppΘ
    have hM : MMP.Mori.IsDltPair (g ≫ sX) m KY (D₀ + G₀) :=
      ⟨⟨hYn, hKY, MMP.Fourfold.isQCartier_of_isSmoothScheme hYsm _⟩, hΘ01, ⊤,
        (show smoothLocus (g ≫ sX) = ⊤ from hYsm) ▸ le_rfl, isSNC_restrictOpen hsncΘ ⊤,
        fun D a hc _ => by
          exfalso
          exact hc D.isGenericPoint_center.mem trivial⟩
    exact (MMP.Threefold.Bridges.isDltPair_iff_isDltPair (g ≫ sX) hKY _).mpr hM

/-- A *floor flip* from the model `s` to the model `t` for the boundary `Θ`: `t` is the
projective `(K + Θ)`-flip of a floor flipping contraction of `s`, with the strict transforms of `K`
and `Θ`. -/
private def IsFloorStep {Z : Scheme.{0}} (Θ : ∀ s : Stage Z, QDivisor s.Y) (s t : Stage Z) : Prop :=
  ∃ (W : Scheme.{0}) (sW : W ⟶ Spec (.of ℂ)) (R : Set (NumericalCurveClasses s.sY))
    (c : s.Y ⟶ W) (c' : t.Y ⟶ W),
    MMP.Mori.IsProjectiveVariety ℂ t.sY ∧ IsFloorFlippingContraction s.sY sW s.K (Θ s) R c ∧
      IsFlip s.sY sW t.sY s.K (Θ s) c c' ∧ t.K = flipTransform c c' s.K ∧
      Θ t = flipTransform c c' (Θ s)

/-- **Termination of floor flips.** By the second clause of `P(n)`, there is no infinite sequence
of floor flips through projective `ℚ`-factorial dlt `n`-folds. -/
private theorem not_forall_isFloorStep {n : ℕ} (hP : ProjectiveFloorProgramInputs n)
    {Z : Scheme.{0}} (Θ : ∀ s : Stage Z, QDivisor s.Y) (u : ℕ → Stage Z)
    (hu : IsFloorPair (u 0).sY n (u 0).K (Θ (u 0))) :
    ¬ ∀ i, IsFloorStep Θ (u i) (u (i + 1)) := by
  intro hall
  choose W sW R c c' hproj hcon hflip hK hΘ using hall
  refine hP.2.2 (u 0).Y (u 0).sY (u 0).K (Θ (u 0)) hu
    ⟨fun i => (u (i + 1)).Y, fun i => (u (i + 1)).sY, fun _ => inferInstance,
      fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
      fun i => (u (i + 1)).K, fun i => Θ (u (i + 1)), W, sW,
      fun i => match i with
        | 0 => R 0
        | i + 1 => R (i + 1),
      fun i => match i with
        | 0 => c 0
        | i + 1 => c (i + 1),
      c', fun i => ?_⟩
  rcases i with _ | i
  · exact ⟨hproj 0, hcon 0, hflip 0, hK 0, hΘ 0⟩
  · exact ⟨hproj (i + 1), hcon (i + 1), hflip (i + 1), hK (i + 1), hΘ (i + 1)⟩

/-- The curve form depends only on the divisor, not on the `ℚ`-Cartier witness. -/
private theorem curveForm_congr {V : Scheme.{0}} [CompactSpace V] [IsLocallyNoetherian V]
    [IsNormal V] (sV : V ⟶ Spec (.of ℂ)) {A A' : QDivisor V} (hAA' : A = A')
    (hA : A.IsQCartier) (hA' : A'.IsQCartier) :
    QDivisor.curveForm sV A hA = QDivisor.curveForm sV A' hA' := by
  subst hAA'; rfl

/-- The curve form of the zero divisor vanishes. -/
private theorem curveForm_zero {V : Scheme.{0}} [CompactSpace V] [IsLocallyNoetherian V]
    [IsNormal V] (sV : V ⟶ Spec (.of ℂ)) [QuasiCompact sV] (h : (0 : QDivisor V).IsQCartier) :
    QDivisor.curveForm sV 0 h = 0 := by
  rw [curveForm_congr sV (zero_smul ℚ (0 : QDivisor V)).symm h (MMP.Flips.isQCartier_smul h 0),
    MMP.Fourfold.QDivisor.curveForm_smul sV 0 0 h, Rat.cast_zero, zero_smul]

/-- **The curve form is linear in the divisor**: `((A + q B) · z) = (A · z) + q (B · z)`. -/
private theorem curveForm_add_smul {V : Scheme.{0}} [CompactSpace V]
    [IsLocallyNoetherian V] [IsNormal V] (sV : V ⟶ Spec (.of ℂ)) [QuasiCompact sV]
    {A B : QDivisor V} (hA : A.IsQCartier) (hB : B.IsQCartier) (q : ℚ)
    (hAB : (A + q • B).IsQCartier) :
    QDivisor.curveForm sV (A + q • B) hAB = QDivisor.curveForm sV A hA +
      (q : ℝ) • QDivisor.curveForm sV B hB := by
  rw [MMP.Fourfold.QDivisor.curveForm_add sV A (q • B) hA (MMP.Flips.isQCartier_smul hB q) hAB,
    MMP.Fourfold.QDivisor.curveForm_smul sV q B hB]

/-- **A klt boundary negative on a dlt-negative ray.** If `(Y, Θ)` is a `ℚ`-factorial projective
dlt pair and `R` a `(K + Θ)`-negative extremal ray, then `(Y, (1 - δ)Θ)` is klt and `R` is still
`(K + (1 - δ)Θ)`-negative for small rational `δ > 0` (KM 3.35). -/
private theorem exists_isKltPair_isNegativeExtremalRayOf {Y : Scheme.{0}} [IsIntegral Y]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hQ : IsQFactorial sY) {m : ℕ} {K : Divisor Y}
    (hK : K.IsCanonicalDivisor sY m) {Θ : QDivisor Y} (hdlt : MMP.Intersection.IsDltPair sY Θ)
    {R : Set (NumericalCurveClasses sY)}
    (hR : IsNegativeExtremalRayOf sY (Divisor.toQDivisor K + Θ) R) :
    ∃ Θ' : QDivisor Y, IsKltPair sY Θ' ∧ IsNegativeExtremalRayOf sY (Divisor.toQDivisor K + Θ') R := by
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  haveI := hY
  haveI : QuasiCompact sY := inferInstance
  have hM := (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sY hK Θ).mp hdlt
  obtain ⟨δ₀, hδ₀, hklt⟩ := hM.exists_forall_isKltPair_one_sub_smul hQ
    (AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ sY).isQuasiProjective
  obtain ⟨hKΘ, hRe, hneg⟩ := hR
  obtain ⟨v, hv0, hRv⟩ := hRe.2
  have hvR : v ∈ R := hRv ▸ ⟨1, zero_le_one, one_smul _ _⟩
  have hΘq := isQCartier_of_isQFactorial sY hQ Θ
  set a := QDivisor.curveForm sY _ hKΘ v
  set b := QDivisor.curveForm sY Θ hΘq v
  have ha : a < 0 := hneg v hvR hv0
  -- a rational `δ ∈ (0, min δ₀ 1)` with `a - δ b < 0`
  have hδ₁ : (0 : ℚ) < min δ₀ 1 := lt_min hδ₀ one_pos
  obtain ⟨δ, hδ0, hδ, hab⟩ : ∃ δ : ℚ, 0 < δ ∧ δ < min δ₀ 1 ∧ a - δ * b < 0 := by
    by_cases hb : b < 0
    · obtain ⟨δ, hδ1, hδ2⟩ := exists_rat_btwn (lt_min
        (show (0 : ℝ) < ((min δ₀ 1 : ℚ) : ℝ) by exact_mod_cast hδ₁)
        (div_pos (neg_pos.mpr ha) (neg_pos.mpr hb)))
      refine ⟨δ, by exact_mod_cast hδ1, by exact_mod_cast (lt_min_iff.mp hδ2).1, ?_⟩
      have h2 := (lt_min_iff.mp hδ2).2
      rw [lt_div_iff₀ (neg_pos.mpr hb)] at h2
      linarith
    · push Not at hb
      refine ⟨min δ₀ 1 / 2, by positivity, by linarith, ?_⟩
      have : (0 : ℝ) ≤ ((min δ₀ 1 / 2 : ℚ) : ℝ) * b := mul_nonneg (by positivity) hb
      linarith
  have hδ1 : δ < 1 := hδ.trans_le (min_le_right _ _)
  have hkltδ := hklt δ hδ0 (hδ.trans_le (min_le_left _ _))
  have hPair : MMP.Fourfold.IsPair sY ((1 - δ) • Θ) :=
    ⟨Complex.isAlgClosed, inferInstance, hkltδ.isPair, fun P => by
      have := hdlt.1.2.1 P
      have h1 : (0 : ℚ) ≤ 1 - δ := by linarith
      simpa using mul_nonneg h1 this⟩
  refine ⟨(1 - δ) • Θ, (MMP.Fourfold.isKltPair_iff_mori_isKltPair sY hK hPair).mpr hkltδ,
    hkltδ.1.2.2, hRe, fun u hu hu0 => ?_⟩
  -- `K + (1 - δ) Θ = (K + Θ) + (-δ) Θ`
  have heq : Divisor.toQDivisor K + (1 - δ) • Θ = (Divisor.toQDivisor K + Θ) + (-δ) • Θ := by
    rw [sub_smul, one_smul, sub_eq_add_neg, ← add_assoc, neg_smul]
  obtain ⟨c, hc0, rfl⟩ := hRv ▸ hu
  have hc : 0 < c := lt_of_le_of_ne hc0 (by rintro rfl; exact hu0 (zero_smul _ _))
  rw [curveForm_congr sY heq _ (heq ▸ hkltδ.1.2.2),
    curveForm_add_smul sY hKΘ hΘq (-δ) (heq ▸ hkltδ.1.2.2), map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  have : a + -(δ : ℝ) * b < 0 := by linarith
  change c * (a + ((-δ : ℚ) : ℝ) • b) < 0
  rw [smul_eq_mul, Rat.cast_neg]
  exact mul_neg_of_pos_of_neg hc this

/-- The curve form of a `ℚ`-linear combination of prime divisors on a `ℚ`-factorial variety is the
combination of their curve forms. -/
private theorem curveForm_sum_smul_single {V : Scheme.{0}} [IsIntegral V] [CompactSpace V]
    [IsLocallyNoetherian V] [IsNormal V] (sV : V ⟶ Spec (.of ℂ)) [QuasiCompact sV]
    (hQ : ∀ M : QDivisor V, M.IsQCartier) (S : Finset (MMP.Mori.PrimeDivisor V))
    (c : MMP.Mori.PrimeDivisor V → ℚ) (v : NumericalCurveClasses sV) :
    QDivisor.curveForm sV (∑ P ∈ S, c P • Divisor.toQDivisor (Finsupp.single P 1)) (hQ _) v =
      ∑ P ∈ S, (c P : ℝ) *
        QDivisor.curveForm sV (Divisor.toQDivisor (Finsupp.single P 1)) (hQ _) v := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, curveForm_zero, LinearMap.zero_apply]
  | insert P S hP ih =>
    rw [Finset.sum_insert hP, Finset.sum_insert hP]
    have e : c P • Divisor.toQDivisor (Finsupp.single P 1) +
        ∑ x ∈ S, c x • Divisor.toQDivisor (Finsupp.single x 1) =
        (∑ x ∈ S, c x • Divisor.toQDivisor (Finsupp.single x 1)) +
          c P • Divisor.toQDivisor (Finsupp.single P 1) := add_comm _ _
    rw [curveForm_congr sV e (hQ _) (hQ _), curveForm_add_smul sV (hQ _) (hQ _) (c P) (hQ _),
      LinearMap.add_apply, LinearMap.smul_apply, ih, smul_eq_mul]
    ring

/-- The `ℝ`-intersection number of `M` with a curve, presented by a Cartier multiple of `M`, is
the intersection number `M · C`. -/
private theorem isRIntersectionNumber_toRDivisor {V : Scheme.{0}} [IsLocallyNoetherian V]
    [IsNormal V] (sV : V ⟶ Spec (.of ℂ)) [QuasiCompact sV] {M : QDivisor V} (hM : M.IsQCartier)
    (C : ProperCurve sV) : ∃ (r : Fin 1 → ℝ) (L : Fin 1 → Divisor V),
      MMP.Flips.IsRIntersectionNumber ℂ sV (QDivisor.toRDivisor M) r L C
        (M.intersectionNumber ℂ sV C.ι C.dim_le hM : ℝ) := by
  have hN := QDivisor.cartierIndex_pos hM
  obtain ⟨F, hF, hFc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hM
  have hN' : (((M.cartierIndex hM : ℕ) : ℤ)) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨fun _ => ((((M.cartierIndex hM : ℕ) : ℤ) : ℝ))⁻¹, fun _ => F, fun _ => hFc,
    fun _ => F.degreeOn ℂ sV C.ι C.dim_le hFc,
    by rw [Fin.sum_univ_one]; exact QDivisor.toRDivisor_eq_inv_smul hN' hF,
    fun _ => MMP.Flips.isCartierIntersectionNumber_degreeOn ℂ sV C F hFc, ?_⟩
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sV C.ι C.dim_le M hM hN F hFc hF, Fin.sum_univ_one]
  push_cast
  rw [div_eq_inv_mul]

/-- The `ℝ`-intersection number of a finite combination `∑ c_E E` of prime divisors of a
`ℚ`-factorial variety with a curve `C` is `∑ c_E (E · C)`. -/
private theorem exists_isRIntersectionNumber_sum_smul_single {V : Scheme.{0}}
    [IsLocallyNoetherian V] [IsNormal V] (sV : V ⟶ Spec (.of ℂ)) [QuasiCompact sV]
    (hQ : ∀ M : QDivisor V, M.IsQCartier) (C : ProperCurve sV)
    (S : Finset (MMP.Mori.PrimeDivisor V)) (c : MMP.Mori.PrimeDivisor V → ℝ) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor V),
      MMP.Flips.IsRIntersectionNumber ℂ sV
        (∑ E ∈ S, c E • QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single E 1))) r L C
        (∑ E ∈ S, c E * ((Divisor.toQDivisor (Finsupp.single E 1)).intersectionNumber ℂ sV C.ι
          C.dim_le (hQ _) : ℝ)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, by simp,
      fun j => j.elim0, by simp⟩
  | insert E S hE ih =>
    obtain ⟨m, r, L, hI⟩ := ih
    obtain ⟨rE, LE, hIE⟩ := isRIntersectionNumber_toRDivisor sV (hQ (Divisor.toQDivisor
      (Finsupp.single E 1))) C
    have h :=
      (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sV C).2 _ _ _ _ _ _ _ _ 1 (c E) hI hIE
    rw [one_smul, one_mul] at h
    refine ⟨m + 1, Fin.append ((1 : ℝ) • r) (c E • rE), Fin.append L LE, ?_⟩
    rw [Finset.sum_insert hE, Finset.sum_insert hE, add_comm (c E • _), add_comm (c E * _)]
    exact h

/-- **Floor negativity in the first program** (FA 18.12). Let `T` be a curve contracted by `h` on
an admissible model on which `K + D + G` is negative. The components of `h⁻¹(H')` span `N¹(Y/Z)`
(the procedure datum), so `K + D + G ≡_h G'` with `G'` supported on them, and some such component
is not numerically trivial on `T`. Their positive combination `h^* H'` has degree zero on `T`, so
one of them, `F₀`, is negative on `T`; lying over `H'`, it has coefficient one in `D + G`. -/
private theorem isComponentNegative_of_procedureDatum {X Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of ℂ)} [IsLocallyNoetherian Z] [IsNormal Z] (hZn : IsNormalVariety ℂ sZ)
    {B : QDivisor X} {f : X ⟶ Z} (P : MMP.Flips.ProcedureDatum ℂ sZ (QDivisor.toRDivisor B) f)
    {n : ℕ} {KZ : Divisor Z} {BZ : QDivisor Z}
    (hBH : ∀ Q, P.H'.coeff Q ≠ 0 → BZ.coeff Q = 0) {s : Stage Z}
    (hs : s.IsAdmissible sZ n P.H' KZ BZ) {R : Set (NumericalCurveClasses s.sY)}
    (hKΘ : (Divisor.toQDivisor s.K + (s.D + s.G)).IsQCartier) (T : ProperCurve s.sY)
    (hT : T.IsContractedBy s.h)
    (hRT : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass s.sY (T.cycle ℝ) = w})
    (hneg : QDivisor.curveForm s.sY (Divisor.toQDivisor s.K + (s.D + s.G)) hKΘ
      (OneCycle.numericalClass s.sY (T.cycle ℝ)) < 0) :
    IsComponentNegative s.sY (s.D + s.G) R := by
  classical
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI := isSeparated_toTerminal_of_isNormalVariety hZn
  haveI : IsSeparated sZ := hZn.1.toIsSeparated
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : QuasiCompact sZ := hZn.1.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have hY := hs.isProjectiveVariety
  haveI := hY
  haveI : QuasiCompact s.sY := inferInstance
  haveI : MMP.Mori.IsVariety ℂ s.sY := hY.toIsVariety
  haveI : IsProper s.h := isProper_of_isProjectiveMorphism _ hs.isProjectiveMorphism
  have hhb := hs.isBirationalMorphism
  haveI : IsDominant s.h := hhb.isDominant
  have hYv : MMP.Mori.IsVariety ℂ (s.h ≫ sZ) := by rw [hs.comp_eq]; exact hY.toIsVariety
  have hYn : IsNormalVariety ℂ (s.h ≫ sZ) := ⟨hYv, inferInstance⟩
  haveI : MMP.Mori.IsVariety ℂ sZ := hZn.1
  have hQ := isQCartier_of_isQFactorial s.sY hs.isQFactorial
  set v := OneCycle.numericalClass s.sY (T.cycle ℝ)
  set x : MMP.Mori.PrimeDivisor s.Y → ℝ := fun E =>
    ((Divisor.toQDivisor (Finsupp.single E 1)).intersectionNumber ℂ s.sY T.ι T.dim_le (hQ _) : ℝ)
  have hxv : ∀ E, QDivisor.curveForm s.sY (Divisor.toQDivisor (Finsupp.single E 1)) (hQ _) v =
      x E := fun E => MMP.ProgramBaseChange.curveForm_numericalClass_cycle _ _ _ T
  -- `K + Θ ≡_h G'`, with `G'` supported on `h⁻¹_* H'` and the `h`-exceptional prime divisors
  have hLc : MMP.Flips.IsCartierCombination
      (QDivisor.toRDivisor (Divisor.toQDivisor s.K + (s.D + s.G))) := by
    obtain ⟨m, hm, L, hL, hLc⟩ := hKΘ
    exact ⟨1, fun _ => (m : ℝ)⁻¹, fun _ => L, fun _ => hLc, by
      rw [Fin.sum_univ_one]; exact QDivisor.toRDivisor_eq_inv_smul hm hL⟩
  obtain ⟨G', hG'comp, hG'eq⟩ := P.exists_isNumericallyEquivalentOver_of_isQFactorial
    hs.isQFactorial hs.comp_eq hhb hLc
  obtain ⟨r₁, L₁, hI₁⟩ := isRIntersectionNumber_toRDivisor s.sY hKΘ T
  have hG'sum : G' = ∑ E ∈ G'.support,
      G' E • QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single E 1)) := by
    conv_lhs => rw [← Finsupp.sum_single G']
    refine Finset.sum_congr rfl fun E _ => ?_
    rw [MMP.Threefold.Resolution.toQDivisor_single]
    ext P
    simp only [DivisorWithCoeffs.coeff_smul, QDivisor.coeff_toRDivisor, smul_eq_mul]
    by_cases hP : E = P
    · subst hP
      rw [DivisorWithCoeffs.coeff_single_self, DivisorWithCoeffs.coeff_single_self]
      simp
    · rw [DivisorWithCoeffs.coeff_single_of_ne hP, DivisorWithCoeffs.coeff_single_of_ne hP]
      simp
  obtain ⟨m₂, r₂, L₂, hI₂⟩ :=
    exists_isRIntersectionNumber_sum_smul_single s.sY hQ T G'.support (fun E => G' E)
  rw [← hG'sum] at hI₂
  have heq := hG'eq.2.2 T hT _ _ _ _ _ _ _ _ hI₁ hI₂
  have hsum_neg : ∑ E ∈ G'.support, G' E * x E < 0 := by
    have h := hneg
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle, heq] at h
    exact h
  obtain ⟨E₀, hE₀, hE₀ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_neg.ne
  rw [mul_ne_zero_iff] at hE₀ne
  -- the pull-back `H = h^* H'`
  have hB := MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant s.h P.H'
  set H := P.H'.pullback P.isCartier_H' hB
  have hHp : P.H'.IsPullback s.h hB H := Divisor.isPullback_pullback P.isCartier_H' hB
  have hHc : H.IsCartier := P.isCartier_H'.isCartier_pullback s.h hB
  have hHe : DivisorWithCoeffs.IsEffective P.H' := fun E => by
    rcases P.isReduced_H' E with h | h <;> simp [h]
  have hsupp := MMP.Flips.supp_eq_preimage_supp_of_isPullback P.isCartier_H' hHe hHp
  have hHnn : ∀ E, (0 : ℚ) ≤ ((H E : ℤ) : ℚ) := fun E => by
    exact_mod_cast MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn P.isCartier_H'
      (V := ⊤) (fun Q _ => hHe Q) hHp E
      ⟨E.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' E, trivial⟩
  -- a prime divisor lying over `Supp H'` has nonzero coefficient in `H`
  have hHpos : ∀ E : MMP.Mori.PrimeDivisor s.Y, s.h E.genericPoint ∈ P.H'.supp → H E ≠ 0 := by
    intro E hE
    have hη : E.genericPoint ∈ (H.supp : Set s.Y) := by rwa [hsupp]
    obtain ⟨E', hE'0, hE'⟩ := DivisorWithCoeffs.mem_supp_iff.mp hη
    obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hE'
    exact hE'0
  -- conversely, a prime divisor with nonzero coefficient in `H` lies over `Supp H'`
  have hHover : ∀ E : MMP.Mori.PrimeDivisor s.Y, H E ≠ 0 → s.h E.genericPoint ∈ P.H'.supp := by
    intro E hE
    have hη : E.genericPoint ∈ (H.supp : Set s.Y) := DivisorWithCoeffs.support_subset_supp hE
      (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' E)
    rw [hsupp] at hη
    exact hη
  have hE₀H : H E₀ ≠ 0 := by
    apply hHpos
    rcases hG'comp E₀ (Finsupp.mem_support_iff.mp hE₀) with hbit | hexc
    · by_cases hQ0 : ∃ Q : MMP.Mori.PrimeDivisor Z, s.h E₀.genericPoint = Q.genericPoint
      · obtain ⟨Q, hQ⟩ := hQ0
        rw [MMP.Flips.birationalInverseTransform_apply_of_genericPoint_eq hZn s.h hYv hhb _ hQ]
          at hbit
        rw [hQ]
        exact DivisorWithCoeffs.mem_supp_iff.mpr
          ⟨Q, hbit, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' Q⟩
      · push Not at hQ0
        exact absurd (MMP.Flips.coeff_birationalInverseTransform_eq_zero hZn.1 hYv hhb _ hQ0) hbit
    · refine hs.exceptional_mem E₀ ?_
      have hn : topologicalKrullDim Z = n := by
        rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ s.sY hhb,
          hs.dim_eq]
      have hmem := (MMP.Flips.isExceptionalPrimeDivisor_iff hZn hn hYn hhb E₀).mp hexc
      rcases hP' : RationalMap.transformPrimeDivisor s.h.toRationalMap E₀ with _ | Q
      · rfl
      · exfalso
        have hPQ :=
          (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff s.h E₀ Q).mp hP'
        apply MMP.Mori.mem_exceptionalSet.mp hmem
        rw [hPQ]
        refine MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hZn s.h hYv hhb ?_
        rw [ringKrullDim_stalk_eq_coheight, Q.coheight_genericPoint]
        norm_num
  -- `(h^* H' · T) = 0`
  have hH0 : QDivisor.curveForm s.sY (Divisor.toQDivisor H) (hQ _) v = 0 := by
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
      QDivisor.intersectionNumber_eq_of_smul ℂ s.sY T.ι T.dim_le _ (hQ _) one_pos H hHc
        (by simp),
      MMP.Mori.Divisor.degreeOn_pullback_eq_zero_of_isContractedBy s.h hs.comp_eq P.isCartier_H'
        hB T hT]
    simp
  have hHsum : Divisor.toQDivisor H = ∑ E ∈ (Divisor.toQDivisor H).support,
      (Divisor.toQDivisor H) E • Divisor.toQDivisor (Finsupp.single E 1) := by
    conv_lhs => rw [← Finsupp.sum_single (Divisor.toQDivisor H)]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [MMP.Threefold.Resolution.toQDivisor_single, Finsupp.smul_single, smul_eq_mul, Int.cast_one,
      mul_one]
  rw [curveForm_congr s.sY hHsum (hQ _) (hQ _), curveForm_sum_smul_single s.sY hQ] at hH0
  simp only [hxv] at hH0
  -- some component `F₀` of `h^* H'` is negative on `T`
  have hcast : ∀ E, (Divisor.toQDivisor H) E = ((H E : ℤ) : ℚ) := fun E => rfl
  obtain ⟨F₀, hF₀H, hF₀x⟩ : ∃ F₀, (H F₀ : ℚ) ≠ 0 ∧ x F₀ < 0 := by
    by_contra hall
    push Not at hall
    have hterm : ∀ E ∈ (Divisor.toQDivisor H).support,
        (0 : ℝ) ≤ (((Divisor.toQDivisor H) E : ℚ) : ℝ) * x E := by
      intro E hE
      have hEH : (H E : ℚ) ≠ 0 := Finsupp.mem_support_iff.mp hE
      exact mul_nonneg (by rw [hcast]; exact_mod_cast hHnn E) (hall E hEH)
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hH0 E₀
      (Finsupp.mem_support_iff.mpr (by rw [hcast]; exact_mod_cast hE₀H))
    rcases mul_eq_zero.mp hzero with h | h
    · rw [hcast] at h
      exact hE₀H (by exact_mod_cast h)
    · exact hE₀ne.2 h
  -- `F₀` lies over `H'`, so it has coefficient one in `D + G`
  have hF₀over := hHover F₀ (by exact_mod_cast hF₀H)
  have hF₀coeff : (s.D + s.G).coeff F₀ = 1 := by
    change s.D.coeff F₀ + s.G.coeff F₀ = 1
    rw [hs.coeff_D, hs.coeff_G]
    rcases hP' : RationalMap.transformPrimeDivisor s.h.toRationalMap F₀ with _ | Q
    · simp
    · have hPQ := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff s.h F₀ Q).mp hP'
      rw [hPQ] at hF₀over
      obtain ⟨Q', hQ'0, hQ'⟩ := DivisorWithCoeffs.mem_supp_iff.mp hF₀over
      obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hQ'
      have hq1 : P.H'.coeff Q' = 1 := (P.isReduced_H' Q').resolve_left hQ'0
      simp only [Option.elim]
      rw [hBH Q' hQ'0, hq1]
      norm_num
  refine ⟨F₀, hF₀coeff, hQ _, fun u hu hu0 => ?_⟩
  rw [hRT] at hu
  obtain ⟨t, ht0, rfl⟩ := hu
  have ht : 0 < t := lt_of_le_of_ne ht0 (by rintro rfl; exact hu0 (zero_smul _ _))
  rw [map_smul, smul_eq_mul, hxv]
  exact mul_neg_of_pos_of_neg ht hF₀x

/-- **A step preserves admissibility.** Let `c : Y ⟶ W` be the birational contraction of an
admissible model over `Z`, with `h = c ≫ h_W`, and `c' : Y' ⟶ W` a small morphism from a
projective `ℚ`-factorial `n`-fold with canonical divisor `c'⁻¹_* c_* K`. Then `Y'` with
`c' ≫ h_W` and the strict transforms of `K`, `D`, `G` is admissible: every prime divisor of `Y'`
has a counterpart on `Y` lying over the same point of `Z`. -/
private theorem Stage.IsAdmissible.of_step {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} {n : ℕ}
    [IsLocallyNoetherian Z] [IsNormal Z] (hZn : IsNormalVariety ℂ sZ) {H' KZ : Divisor Z}
    {BZ : QDivisor Z} {s : Stage Z}
    (hs : s.IsAdmissible sZ n H' KZ BZ) {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)}
    {c : s.Y ⟶ W} (hc : IsContraction s.sY sW c) (hcb : IsBirationalMorphism c) {hW : W ⟶ Z}
    (hch : c ≫ hW = s.h) (hhW : hW ≫ sZ = sW) {Y' : Scheme.{0}} [IsIntegral Y']
    [CompactSpace Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] {sY' : Y' ⟶ Spec (.of ℂ)}
    {c' : Y' ⟶ W} (hc' : IsSmallMorphism sY' sW c')
    (hY' : IsProjectiveQFactorialDltPair sY' (flipTransform c c' s.K) (flipTransform c c' (s.D + s.G)) ∨
      (MMP.Mori.IsProjectiveVariety ℂ sY' ∧ IsQFactorial sY' ∧
        ∃ m : ℕ, Divisor.IsCanonicalDivisor sY' m (flipTransform c c' s.K))) :
    (⟨Y', sY', c' ≫ hW, flipTransform c c' s.K, flipTransform c c' s.D,
      flipTransform c c' s.G⟩ : Stage Z).IsAdmissible sZ n H' KZ BZ := by
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI := isSeparated_toTerminal_of_isNormalVariety hZn
  have hWn := hc.isNormalVariety_target
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI : LocallyOfFiniteType sW := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : IsProper c := isProper_of_isProjectiveMorphism _ hc.isProjectiveMorphism
  have hproj : MMP.Mori.IsProjectiveVariety ℂ sY' ∧ IsQFactorial sY' ∧
      ∃ m : ℕ, Divisor.IsCanonicalDivisor sY' m (flipTransform c c' s.K) := by
    rcases hY' with h | h
    · exact ⟨h.isProjectiveVariety, h.isQFactorial, h.isCanonicalDivisor⟩
    · exact h
  obtain ⟨hY'p, hY'Q, hY'K⟩ := hproj
  haveI := hY'p
  haveI : IsProper c' := hc'.isProper
  -- `h_W` is birational, and so is `h' = c' ≫ h_W`
  haveI : LocallyOfFiniteType (hW ≫ sZ) := hhW ▸ inferInstance
  haveI : LocallyOfFiniteType hW := LocallyOfFiniteType.of_comp (g := sZ) ‹_›
  have hhWb : IsBirationalMorphism hW :=
    MMP.Fourfold.Oai4C1.Main.isBirationalMorphism_of_comp_left c hW hcb
      (hch ▸ hs.isBirationalMorphism)
  have hh'b : IsBirationalMorphism (c' ≫ hW) :=
    MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hc'.isBirationalMorphism hhWb
  have hcomp : (c' ≫ hW) ≫ sZ = sY' := by rw [Category.assoc, hhW, hc'.comp_eq]
  haveI : IsSeparated sZ := hZn.1.toIsSeparated
  have hh'p : IsProjectiveMorphism (c' ≫ hW) :=
    IsProjectiveMorphism.of_comp (c' ≫ hW) sZ (hcomp ▸ hY'p.isProjective)
  haveI : IsProper (c' ≫ hW) := isProper_of_isProjectiveMorphism _ hh'p
  -- the prime divisor of `Y` corresponding to a prime divisor of `Y'`
  have hcorr : ∀ P' : MMP.Mori.PrimeDivisor Y', ∃ P : MMP.Mori.PrimeDivisor s.Y,
      (c' ≫ hW) P'.genericPoint = s.h P.genericPoint ∧
        ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R s.Y),
          flipTransform c c' D P' = D P := by
    intro P'
    obtain ⟨x, hx⟩ := hc.surjective (c' P'.genericPoint)
    obtain ⟨P, rfl, hP⟩ := exists_eq_genericPoint_flipTransform_apply hcb hc' P' x hx
    refine ⟨P, ?_, fun D => hP D⟩
    rw [← hch, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx]
  have htr : ∀ P' : MMP.Mori.PrimeDivisor Y', ∀ P : MMP.Mori.PrimeDivisor s.Y,
      (c' ≫ hW) P'.genericPoint = s.h P.genericPoint →
      RationalMap.transformPrimeDivisor (c' ≫ hW).toRationalMap P' =
        RationalMap.transformPrimeDivisor s.h.toRationalMap P :=
    fun P' P h => transformPrimeDivisor_eq_of_map_genericPoint_eq h
  refine
    { isProjectiveVariety := hY'p
      dim_eq := ?_
      isQFactorial := hY'Q
      isCanonicalDivisor := hY'K
      comp_eq := hcomp
      isProjectiveMorphism := hh'p
      isBirationalMorphism := hh'b
      exceptional_mem := fun P' hP' => ?_
      transformDivisor_K := ?_
      coeff_D := fun P' => ?_
      coeff_G := fun P' => ?_ }
  · haveI : MMP.Mori.IsVariety ℂ sW := hWn.1
    haveI : MMP.Mori.IsVariety ℂ sY' := hY'p.toIsVariety
    haveI : MMP.Mori.IsVariety ℂ s.sY := hs.isProjectiveVariety.toIsVariety
    change topologicalKrullDim Y' = n
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sW sY'
      hc'.isBirationalMorphism,
      MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sW s.sY hcb, hs.dim_eq]
  · obtain ⟨P, hP, -⟩ := hcorr P'
    change (c' ≫ hW) P'.genericPoint ∈ H'.supp
    rw [hP]
    exact hs.exceptional_mem P ((htr P' P hP).symm.trans hP')
  · haveI : IsSeparated s.h := (isProper_of_isProjectiveMorphism _ hs.isProjectiveMorphism).toIsSeparated
    refine Finsupp.ext fun Q => ?_
    obtain ⟨P', hP'⟩ := exists_primeDivisor_map_genericPoint_eq hZn hh'b Q
    obtain ⟨P, hP, hD⟩ := hcorr P'
    change RationalMap.transformDivisor (c' ≫ hW).toRationalMap (flipTransform c c' s.K) Q = KZ Q
    rw [MMP.Fourfold.Oai4C1.transformDivisor_apply_of_map_genericPoint hh'b hP', hD,
      ← hs.transformDivisor_K,
      MMP.Fourfold.Oai4C1.transformDivisor_apply_of_map_genericPoint hs.isBirationalMorphism
        (hP.symm.trans hP')]
  · obtain ⟨P, hP, hD⟩ := hcorr P'
    change flipTransform c c' s.D P' = _
    rw [hD]
    change s.D.coeff P = _
    rw [hs.coeff_D P]
    change _ = (RationalMap.transformPrimeDivisor (c' ≫ hW).toRationalMap P').elim _ _
    rw [htr P' P hP]
  · obtain ⟨P, hP, hD⟩ := hcorr P'
    change flipTransform c c' s.G P' = _
    rw [hD]
    change s.G.coeff P = _
    rw [hs.coeff_G P]
    change _ = (RationalMap.transformPrimeDivisor (c' ≫ hW).toRationalMap P').elim _ _
    rw [htr P' P hP]

/-- **One step of the first program.** At an admissible model with `(Y, Θ)` dlt, `Θ = D + G`,
and `K + Θ` not nef over `Z`, a `(K + Θ)`-negative extremal ray contracted over `Z` is contracted
(by the klt contraction theorem applied to a slightly smaller klt boundary); a divisorial
contraction lowers `ρ`, and a small one is a floor flipping contraction by the procedure datum,
whose flip exists by `P(n)`. -/
private theorem exists_firstStep
    {n : ℕ} (hP : ProjectiveFloorProgramInputs n)
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) [IsLocallyNoetherian Z]
    [IsNormal Z] {f : X ⟶ Z}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    (P : MMP.Flips.ProcedureDatum ℂ sZ (QDivisor.toRDivisor B) f) {KZ : Divisor Z}
    {BZ : QDivisor Z} (hBH : ∀ Q, P.H'.coeff Q ≠ 0 → BZ.coeff Q = 0) (s : Stage Z)
    (hs : s.IsAdmissible sZ n P.H' KZ BZ)
    (hdlt : MMP.Intersection.IsDltPair s.sY (s.D + s.G))
    (hnef : ¬ (Divisor.toQDivisor s.K + (s.D + s.G)).IsRelativelyNef s.sY s.h) :
    ∃ t : Stage Z, (t.IsAdmissible sZ n P.H' KZ BZ ∧
      MMP.Intersection.IsDltPair t.sY (t.D + t.G)) ∧
      (picardNumber t.sY < picardNumber s.sY ∨ (picardNumber t.sY = picardNumber s.sY ∧
        IsFloorStep (fun s => s.D + s.G) s t)) := by
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  obtain ⟨m, hK⟩ := hs.isCanonicalDivisor
  have hY := hs.isProjectiveVariety
  haveI := hY
  have hQ := hs.isQFactorial
  set Θ := s.D + s.G with hΘ
  have hM := (MMP.Threefold.Bridges.isDltPair_iff_isDltPair s.sY hK Θ).mp hdlt
  -- a `(K + Θ)`-negative extremal ray contracted over `Z`, and its contraction `c : Y ⟶ W`
  obtain ⟨R, hR, hRπ⟩ := exists_isNegativeExtremalRayOf_isContractedBy_of_not_isRelativelyNef
    hY hZ ⟨m, hK⟩ hdlt.1 hs.isProjectiveMorphism hs.comp_eq hnef
  obtain ⟨Θ', hklt', hR'⟩ := exists_isKltPair_isNegativeExtremalRayOf hY hQ hK hdlt hR
  obtain ⟨⟨T, -, hRT⟩, W, sW, c, hc, hW, hρ, -⟩ :=
    exists_isContractionOfRay_of_isKltPair s.sY hY hklt' hK hR'
  have hamp := hasRelativelyAmpleMultiple_neg_of_isContractionOfRay hY hK hR hW hc
  obtain ⟨hKΘ, hRe, hRneg⟩ := hR
  obtain ⟨hW', hgh, -⟩ := existsUnique_comp_eq_of_isContractionOfRay hY
    hs.isProjectiveMorphism hs.comp_eq hRe hRπ hc
  have hcb : IsBirationalMorphism c := isBirationalMorphism_of_isContractionOfRay hY
    hs.isProjectiveMorphism hs.isBirationalMorphism hs.comp_eq hRe hRπ hc
  have hWn : IsNormalVariety ℂ sW := hc.isNormalVariety_target
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI : IsProper sW := hW.isProjective.isProjective.isProper
  haveI : LocallyOfFiniteType sW := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : IsSeparated sZ := hZ.toIsSeparated
  haveI : IsSeparated sW := hW.toIsSeparated
  haveI : IsProper c := isProper_of_isProjectiveMorphism _ hc.isProjectiveMorphism
  have hhsZ : hW' ≫ sZ = sW := comp_eq_of_isContraction hc.toIsContraction hgh hs.comp_eq
  have hface : IsContractionOfFace ℂ s.sY sW R c :=
    ⟨hY, hW, hc.comp_eq, hRe.1, hc.isContractedBy_iff, hc.isIso_app⟩
  have hnegface : IsNegativeExtremalFace ℝ (closedConeOfCurves s.sY : Set (NumericalCurveClasses s.sY))
      (QDivisor.curveForm s.sY (Divisor.toQDivisor s.K + Θ) hM.1.2.2) R :=
    ⟨hRe.1, hRe.1.2.2.1, hRneg⟩
  by_cases hsm : IsSmallMorphism s.sY sW c
  · -- the flip, by `P(n)`
    have hneg : IsComponentNegative s.sY Θ R := by
      have hvR : OneCycle.numericalClass s.sY (T.cycle ℝ) ∈ R := by
        rw [hRT]; exact ⟨1, zero_le_one, one_smul _ _⟩
      have hv0 : OneCycle.numericalClass s.sY (T.cycle ℝ) ≠ 0 := by
        obtain ⟨w, hw0, hRw⟩ := hRe.2
        have hwR : w ∈ R := hRw ▸ ⟨1, zero_le_one, one_smul _ _⟩
        rw [hRT] at hwR
        obtain ⟨t, -, rfl⟩ := hwR
        intro h
        exact hw0 (by rw [h, smul_zero])
      exact isComponentNegative_of_procedureDatum hZn P hBH hs hKΘ T (hRπ T hvR) hRT
        (hRneg _ hvR hv0)
    have hfloor : IsFloorFlippingContraction s.sY sW s.K Θ R c := ⟨⟨hKΘ, hRe, hRneg⟩, hc, hsm, hW,
      hamp, hneg⟩
    obtain ⟨Y', _, _, _, sY', fp, hY'p, hflip⟩ :=
      hP.2.1 s.Y s.sY s.K Θ ⟨hY, hs.dim_eq, hQ, ⟨m, hK⟩, hdlt⟩ W sW R c hfloor
    haveI : IsIntegral Y' := hflip.isNormalVariety.1.toIsIntegral
    have hfps : IsSmallMorphism sY' sW fp := ⟨hflip.isNormalVariety, hWn, hflip.comp_eq,
      hflip.isProper, hflip.isBirationalMorphism, hflip.two_le_codimension⟩
    have hfpp : IsProjectiveMorphism fp :=
      IsProjectiveMorphism.of_comp fp sW (hflip.comp_eq ▸ hY'p.isProjective)
    have hampp := hflip.hasRelativelyAmpleMultiple
    have hstep : IsProjectiveElementaryDltStep s.sY sW sY' s.K Θ R c fp (flipTransform c fp Θ) :=
      ⟨⟨hY, hQ, ⟨m, hK⟩, hdlt⟩, ⟨hKΘ, hRe, hRneg⟩, hc, hcb, hflip.comp_eq, rfl,
        Or.inl ⟨hsm, ⟨hKΘ, hc.toIsContraction, hsm, hamp, hfps, hfpp,
          by rw [map_add, flipTransform_toQDivisor]; exact hflip.isQCartier,
          by rw [map_add, flipTransform_toQDivisor]; exact hampp⟩⟩⟩
    have hY' := hstep.isProjectiveQFactorialDltPair_flipTransform hW hρ hamp
    refine ⟨⟨Y', sY', fp ≫ hW', flipTransform c fp s.K, flipTransform c fp s.D,
      flipTransform c fp s.G⟩, ⟨hs.of_step hZn hc.toIsContraction hcb hgh hhsZ hfps (Or.inl hY'),
        by have := hY'.isDltPair; rwa [hΘ, map_add] at this⟩,
      Or.inr ⟨picardNumber_eq_of_isFlip hQ hM hRe hnegface hface hflip,
        W, sW, R, c, fp, hY'p, hfloor, hflip, rfl, (map_add _ _ _).symm⟩⟩
  · -- the divisorial contraction: the next model is `W`
    have hstep : IsProjectiveElementaryDltStep s.sY sW sW s.K Θ R c (𝟙 W)
        (flipTransform c (𝟙 W) Θ) :=
      ⟨⟨hY, hQ, ⟨m, hK⟩, hdlt⟩, ⟨hKΘ, hRe, hRneg⟩, hc, hcb, Category.id_comp _, rfl,
        Or.inr ⟨hsm, inferInstance⟩⟩
    have hWp := hstep.isProjectiveQFactorialDltPair_flipTransform hW hρ hamp
    refine ⟨⟨W, sW, 𝟙 W ≫ hW', flipTransform c (𝟙 W) s.K, flipTransform c (𝟙 W) s.D,
      flipTransform c (𝟙 W) s.G⟩, ⟨hs.of_step hZn hc.toIsContraction hcb hgh hhsZ
        (isSmallMorphism_id hWn) (Or.inl hWp), by have := hWp.isDltPair; rwa [hΘ, map_add] at this⟩,
      Or.inl ?_⟩
    haveI := hW
    change picardNumber sW < picardNumber s.sY
    rw [← IsDltPair.picardNumber_add_one_eq_of_isContractionOfFace hM hQ hRe hRneg hface]
    exact (ENat.lt_add_one_iff (picardNumber_lt_top_of_isProjectiveVariety sW).ne).2 le_rfl

/-- **The first program.** Under `P(n)`, the `(K + D + G)`-program over `Z` from an admissible
model with `(Y, D + G)` dlt terminates with `K + D + G` nef over `Z`. -/
private theorem exists_firstProgram
    {n : ℕ} (hP : ProjectiveFloorProgramInputs n)
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) [IsLocallyNoetherian Z]
    [IsNormal Z] {f : X ⟶ Z}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    (P : MMP.Flips.ProcedureDatum ℂ sZ (QDivisor.toRDivisor B) f) {KZ : Divisor Z}
    {BZ : QDivisor Z} (hBH : ∀ Q, P.H'.coeff Q ≠ 0 → BZ.coeff Q = 0) (s₀ : Stage Z)
    (hs₀ : s₀.IsAdmissible sZ n P.H' KZ BZ)
    (hdlt₀ : MMP.Intersection.IsDltPair s₀.sY (s₀.D + s₀.G)) :
    ∃ s : Stage Z, s.IsAdmissible sZ n P.H' KZ BZ ∧
      MMP.Intersection.IsDltPair s.sY (s.D + s.G) ∧
      (Divisor.toQDivisor s.K + (s.D + s.G)).IsRelativelyNef s.sY s.h := by
  obtain ⟨s, ⟨hs, hdlt⟩, hnef⟩ := exists_stop_of_step
    (good := fun s : Stage Z => s.IsAdmissible sZ n P.H' KZ BZ ∧
      MMP.Intersection.IsDltPair s.sY (s.D + s.G))
    (stop := fun s : Stage Z =>
      (Divisor.toQDivisor s.K + (s.D + s.G)).IsRelativelyNef s.sY s.h)
    (fun s => picardNumber s.sY) (Flip := IsFloorStep fun s => s.D + s.G)
    (fun s hs hnef => exists_firstStep hP sZ hZ hZn P hBH s hs.1 hs.2 hnef)
    (fun u hu => not_forall_isFloorStep hP _ u
      ⟨(hu 0).1.isProjectiveVariety, (hu 0).1.dim_eq, (hu 0).1.isQFactorial,
        (hu 0).1.isCanonicalDivisor, (hu 0).2⟩) s₀ ⟨hs₀, hdlt₀⟩
  exact ⟨s, hs, hdlt, hnef⟩

/-! ### The second program -/

/-- **A negative exceptional component.** On an admissible model over `Z`, let `T` be a curve
contracted by `h` on which `G` is positive. Since `h^* H' = G + A` with `A ≥ 0` supported on the
`h`-exceptional prime divisors, and `(h^* H' · T) = 0`, some `h`-exceptional prime divisor is
negative on `T`. -/
private theorem exists_exceptional_curveForm_neg {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsLocallyNoetherian Z] [IsNormal Z] (hZn : IsNormalVariety ℂ sZ) {n : ℕ}
    {H' KZ : Divisor Z} {BZ : QDivisor Z} (hH'c : H'.IsCartier)
    (hH'r : ∀ Q, H'.coeff Q = 0 ∨ H'.coeff Q = 1) {s : Stage Z}
    (hs : s.IsAdmissible sZ n H' KZ BZ) (T : ProperCurve s.sY) (hT : T.IsContractedBy s.h)
    (hGq : s.G.IsQCartier)
    (hGT : 0 < QDivisor.curveForm s.sY s.G hGq (OneCycle.numericalClass s.sY (T.cycle ℝ))) :
    ∃ E : MMP.Mori.PrimeDivisor s.Y,
      RationalMap.transformPrimeDivisor s.h.toRationalMap E = none ∧
      ∃ hE : (Divisor.toQDivisor (Finsupp.single E 1)).IsQCartier,
        QDivisor.curveForm s.sY _ hE (OneCycle.numericalClass s.sY (T.cycle ℝ)) < 0 := by
  classical
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI := isSeparated_toTerminal_of_isNormalVariety hZn
  haveI : IsSeparated sZ := hZn.1.toIsSeparated
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : QuasiCompact sZ := hZn.1.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have hY := hs.isProjectiveVariety
  haveI := hY
  haveI : QuasiCompact s.sY := inferInstance
  haveI : IsProper s.h := isProper_of_isProjectiveMorphism _ hs.isProjectiveMorphism
  have hhb := hs.isBirationalMorphism
  haveI : IsDominant s.h := hhb.isDominant
  have hQ := isQCartier_of_isQFactorial s.sY hs.isQFactorial
  set v := OneCycle.numericalClass s.sY (T.cycle ℝ)
  have hB := MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant s.h H'
  set H := H'.pullback hH'c hB
  have hHp : H'.IsPullback s.h hB H := Divisor.isPullback_pullback hH'c hB
  have hHc : H.IsCartier := hH'c.isCartier_pullback s.h hB
  -- `(h^* H' · T) = 0`
  have hH0 : QDivisor.curveForm s.sY (Divisor.toQDivisor H) (hQ _) v = 0 := by
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
      QDivisor.intersectionNumber_eq_of_smul ℂ s.sY T.ι T.dim_le _ (hQ _) one_pos H hHc
        (by simp),
      MMP.Mori.Divisor.degreeOn_pullback_eq_zero_of_isContractedBy s.h hs.comp_eq hH'c hB T hT]
    simp
  -- `A = h^* H' - G` is effective and supported on the exceptional prime divisors
  set A := Divisor.toQDivisor H - s.G with hAdef
  have hA : ∀ P, A P ≠ 0 →
      RationalMap.transformPrimeDivisor s.h.toRationalMap P = none ∧ 0 < A P := by
    intro P hP
    rcases hP' : RationalMap.transformPrimeDivisor s.h.toRationalMap P with _ | Q
    · refine ⟨rfl, lt_of_le_of_ne ?_ (Ne.symm hP)⟩
      have h1 : s.G P = 0 := by
        have := hs.coeff_G P
        rw [hP'] at this
        exact this
      change 0 ≤ ((H P : ℤ) : ℚ) - s.G P
      rw [h1, sub_zero]
      exact_mod_cast MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hH'c (V := ⊤)
        (fun Q _ => by rcases hH'r Q with h | h <;> simp [h]) hHp P
        ⟨P.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P, trivial⟩
    · exfalso
      apply hP
      have hPQ := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff s.h P Q).mp hP'
      haveI := isIso_stalkMap_of_map_eq_genericPoint hhb hPQ
      have e1 := MMP.Positivity.coeff_eq_of_isPullback P Q hPQ hH'c hHp
      have e2 := hs.coeff_G P
      rw [hP'] at e2
      change ((H.coeff P : ℤ) : ℚ) - s.G.coeff P = 0
      rw [e1, e2]
      simp
  -- `(A · T) = -(G · T) < 0`
  have hAv : QDivisor.curveForm s.sY A (hQ _) v < 0 := by
    have := LinearMap.congr_fun ((curveForm_congr s.sY
      (show Divisor.toQDivisor H = s.G + A by rw [hAdef]; abel) (hQ _) (hQ _)).trans
      (MMP.Fourfold.QDivisor.curveForm_add s.sY s.G A hGq (hQ A) (hQ _))) v
    rw [LinearMap.add_apply, hH0] at this
    linarith
  have hAsum : A = ∑ P ∈ A.support, A P • Divisor.toQDivisor (Finsupp.single P 1) := by
    conv_lhs => rw [← Finsupp.sum_single A]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [MMP.Threefold.Resolution.toQDivisor_single, Finsupp.smul_single, smul_eq_mul, Int.cast_one,
      mul_one]
  rw [curveForm_congr s.sY hAsum (hQ _) (hQ _), curveForm_sum_smul_single s.sY hQ] at hAv
  obtain ⟨P, hPA, hPneg⟩ := Finset.exists_lt_of_sum_lt (by simpa using hAv :
    ∑ P ∈ A.support, (A P : ℝ) * QDivisor.curveForm s.sY
      (Divisor.toQDivisor (Finsupp.single P 1)) (hQ _) v < ∑ P ∈ A.support, (0 : ℝ))
  obtain ⟨hPexc, hPpos⟩ := hA P (Finsupp.mem_support_iff.mp hPA)
  refine ⟨P, hPexc, hQ _, ?_⟩
  have hPpos' : (0 : ℝ) < A P := by exact_mod_cast hPpos
  by_contra hge
  push Not at hge
  have := mul_nonneg hPpos'.le hge
  linarith

/-- **`ℝ`-nefness is `ℚ`-nefness.** A `ℚ`-Cartier `ℚ`-divisor which is nef over `Y` as an
`ℝ`-divisor is nef over `Y`: its intersection number with a contracted curve is the value of the
`ℝ`-intersection number on the presentation by its Cartier multiple. -/
private theorem isRelativelyNef_of_isRelativelyNef_toRDivisor {V Y : Scheme.{0}}
    [IsLocallyNoetherian V] [IsNormal V] (sV : V ⟶ Spec (.of ℂ)) [QuasiCompact sV] {g : V ⟶ Y}
    {M : QDivisor V} (hM : M.IsQCartier)
    (h : MMP.Flips.IsRelativelyNef ℂ sV g (QDivisor.toRDivisor M)) : M.IsRelativelyNef sV g := by
  obtain ⟨m, r, L, hL, hML, hx⟩ := h
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sV hM fun C hC => ?_
  have hN := QDivisor.cartierIndex_pos hM
  obtain ⟨F, hF, hFc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hM
  have hN' : (((M.cartierIndex hM : ℕ) : ℤ)) ≠ 0 := by exact_mod_cast hN.ne'
  have hI : MMP.Flips.IsRIntersectionNumber ℂ sV (QDivisor.toRDivisor M)
      (fun _ : Fin 1 => ((((M.cartierIndex hM : ℕ) : ℤ) : ℝ))⁻¹) (fun _ => F) C
      (((((M.cartierIndex hM : ℕ) : ℤ) : ℝ))⁻¹ * (F.degreeOn ℂ sV C.ι C.dim_le hFc : ℝ)) :=
    ⟨fun _ => hFc, fun _ => F.degreeOn ℂ sV C.ι C.dim_le hFc,
      by rw [Fin.sum_univ_one]; exact QDivisor.toRDivisor_eq_inv_smul hN' hF,
      fun _ => MMP.Flips.isCartierIntersectionNumber_degreeOn ℂ sV C F hFc, by simp⟩
  have hI' : MMP.Flips.IsRIntersectionNumber ℂ sV (QDivisor.toRDivisor M) r L C
      (∑ j, r j * ((L j).degreeOn ℂ sV C.ι C.dim_le (hL j) : ℝ)) :=
    ⟨hL, fun j => (L j).degreeOn ℂ sV C.ι C.dim_le (hL j), hML,
      fun j => MMP.Flips.isCartierIntersectionNumber_degreeOn ℂ sV C (L j) (hL j), rfl⟩
  have h0 := hx C hC _ hI'
  rw [← (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sV C).1 _ _ _ _ _ _ _ hI hI'] at h0
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sV C.ι C.dim_le M hM hN F hFc hF]
  have hNr : (0 : ℝ) < (((M.cartierIndex hM : ℕ) : ℤ) : ℝ) := by exact_mod_cast hN
  have hdeg : (0 : ℝ) ≤ (F.degreeOn ℂ sV C.ι C.dim_le hFc : ℝ) := by
    have := mul_nonneg hNr.le h0
    rwa [← mul_assoc, mul_inv_cancel₀ hNr.ne', one_mul] at this
  have : (0 : ℚ) ≤ (F.degreeOn ℂ sV C.ι C.dim_le hFc : ℚ) := by exact_mod_cast hdeg
  positivity

/-- The pull-back of a `ℚ`-Cartier `ℚ`-divisor is an `ℝ`-Cartier pull-back of it, presented by
its Cartier multiple. -/
private theorem isRCartierPullback_toRDivisor {V W : Scheme.{0}} [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] [IsLocallyNoetherian W] [IsNormal W] (c : V ⟶ W)
    {N : QDivisor W} (hN : N.IsQCartier)
    (hNc : ∀ Z : irreducibleComponents V, c (componentGenericPoint V Z) ∉ N.supp) :
    MMP.Flips.IsRCartierPullback c (QDivisor.toRDivisor N)
      (QDivisor.toRDivisor (N.pullback hN hNc)) := by
  have hm := QDivisor.cartierIndex_pos hN
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hN
  obtain ⟨D', hD', hp⟩ := QDivisor.isPullback_pullback hN hNc _ hm D₀ hD₀ hD₀c
  have hm' : (((N.cartierIndex hN : ℕ) : ℤ)) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨1, fun _ => ((((N.cartierIndex hN : ℕ) : ℤ) : ℝ))⁻¹, fun _ => D₀, fun _ => D',
    fun _ => hD₀c, ?_, fun _ => ⟨_, hp⟩, ?_⟩
  · rw [Fin.sum_univ_one]; exact QDivisor.toRDivisor_eq_inv_smul hm' hD₀
  · rw [Fin.sum_univ_one]; exact QDivisor.toRDivisor_eq_inv_smul hm' hD'

/-- A proper dominant morphism is surjective. -/
private theorem surjective_of_isProper_of_isDominant {A B : Scheme.{0}} (c : A ⟶ B) [IsProper c]
    [IsDominant c] : Surjective c := ⟨by
  have h1 : Set.range c = Set.univ := by
    rw [← c.isClosedMap.isClosed_range.closure_eq, c.denseRange.closure_range]
  exact fun z => h1.ge (Set.mem_univ z)⟩

/-- **Pull-backs along a flip.** Let `c : Y ⟶ W` be a proper birational morphism and
`f⁺ : Y' ⟶ W` a small morphism of normal varieties. For a `ℚ`-Cartier `ℚ`-divisor `N` on `W`, the
strict transform `f⁺⁻¹_* c_* (c^* N)` is `f⁺^* N`: both have, at a prime divisor of `Y'` over the
prime divisor `Q` of `W`, the coefficient of `N` at `Q`. -/
private theorem flipTransform_pullback {Y Y' W : Scheme.{0}} [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [CompactSpace Y']
    [IsLocallyNoetherian Y'] [IsNormal Y'] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sY' : Y' ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} {c : Y ⟶ W} {fp : Y' ⟶ W} [IsProper c]
    (hcb : IsBirationalMorphism c) (hfp : IsSmallMorphism sY' sW fp)
    {N : QDivisor W} (hN : N.IsQCartier)
    (hNc : ∀ Z : irreducibleComponents Y, c (componentGenericPoint Y Z) ∉ N.supp)
    (hNf : ∀ Z : irreducibleComponents Y', fp (componentGenericPoint Y' Z) ∉ N.supp) :
    flipTransform c fp (N.pullback hN hNc) = N.pullback hN hNf := by
  haveI : IsProper fp := hfp.isProper
  haveI : IsDominant c := hcb.isDominant
  haveI := surjective_of_isProper_of_isDominant c
  refine Finsupp.ext fun P' => ?_
  obtain ⟨Q, hP'Q⟩ :=
    exists_map_genericPoint_eq_of_two_le_closedsCodimension hfp.two_le_codimension P'
  obtain ⟨x, hx⟩ := c.surjective Q.genericPoint
  obtain ⟨P, rfl, hD⟩ :=
    exists_eq_genericPoint_flipTransform_apply hcb hfp P' x (hx.trans hP'Q.symm)
  rw [hD]
  haveI := isIso_stalkMap_of_map_eq_genericPoint hcb hx
  haveI := isIso_stalkMap_of_map_eq_genericPoint hfp.isBirationalMorphism hP'Q
  rw [coeff_eq_of_isPullback_qDivisor P Q hx hN (QDivisor.isPullback_pullback hN hNc),
    coeff_eq_of_isPullback_qDivisor P' Q hP'Q hN (QDivisor.isPullback_pullback hN hNf)]

/-- The principal divisor of a pulled-back rational function, as a `ℚ`-divisor, is the pull-back
of the principal divisor. -/
private theorem toQDivisor_principalDivisor_pullback {A B : Scheme.{0}} [IsLocallyNoetherian A]
    [IsNormal A] [CompactSpace A] [IsLocallyNoetherian B] [IsNormal B] [CompactSpace B]
    (c : A ⟶ B) (ψ : (RationalFunctions B)ˣ)
    (hψ : ∀ Z : irreducibleComponents A, c (componentGenericPoint A Z) ∉ (principalDivisor ψ).supp)
    (hψQ : ∀ Z : irreducibleComponents A,
      c (componentGenericPoint A Z) ∉ (Divisor.toQDivisor (principalDivisor ψ)).supp) :
    Divisor.toQDivisor (principalDivisor (pullbackRationalFunction c ψ hψ)) =
      (Divisor.toQDivisor (principalDivisor ψ)).pullback
        (QDivisor.isQCartier_toQDivisor (Divisor.isCartier_principalDivisor ψ)) hψQ :=
  ((QDivisor.isPullback_toQDivisor (Divisor.isCartier_principalDivisor ψ) hψQ
    (Divisor.isPullback_principalDivisor ψ hψ)).pullback_eq _).symm

/-- **`ℚ`-linear equivalence along a flip.** In the setting of `flipTransform_pullback`, if
`L ∼_ℚ c^* M`, then `f⁺⁻¹_* c_* L ∼_ℚ f⁺^* M`. -/
private theorem qLinearlyEquivalent_flipTransform {Y Y' W : Scheme.{0}} [IsIntegral Y]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [CompactSpace Y']
    [IsLocallyNoetherian Y'] [IsNormal Y'] [IsIntegral W] [CompactSpace W]
    [IsLocallyNoetherian W] [IsNormal W]
    {sY' : Y' ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} {c : Y ⟶ W} {fp : Y' ⟶ W} [IsProper c]
    (hcb : IsBirationalMorphism c) (hfp : IsSmallMorphism sY' sW fp)
    {L : QDivisor Y} {M : QDivisor W} (hM : M.IsQCartier)
    (hMc : ∀ Z : irreducibleComponents Y, c (componentGenericPoint Y Z) ∉ M.supp)
    (hMf : ∀ Z : irreducibleComponents Y', fp (componentGenericPoint Y' Z) ∉ M.supp)
    (hL : L.QLinearlyEquivalent (M.pullback hM hMc)) :
    QDivisor.QLinearlyEquivalent (flipTransform c fp L) (M.pullback hM hMf) := by
  haveI : IsDominant c := hcb.isDominant
  haveI : IsDominant fp := hfp.isBirationalMorphism.isDominant
  obtain ⟨q, hq, φ, hφ⟩ := hL
  obtain ⟨ψ, hψ, rfl⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hcb φ
  have hψf := MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant fp (principalDivisor ψ)
  have hψQc := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' c
    (Divisor.toQDivisor (principalDivisor ψ))
  have hψQf := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' fp
    (Divisor.toQDivisor (principalDivisor ψ))
  refine ⟨q, hq, pullbackRationalFunction fp ψ hψf, ?_⟩
  have h := congrArg (flipTransform c fp) hφ
  rw [map_zsmul, map_sub, flipTransform_pullback hcb hfp hM hMc hMf,
    toQDivisor_principalDivisor_pullback c ψ hψ hψQc,
    flipTransform_pullback hcb hfp _ hψQc hψQf] at h
  rw [h, toQDivisor_principalDivisor_pullback fp ψ hψf hψQf]

/-- **Nefness is invariant under `ℚ`-linear equivalence**: principal divisors have degree zero
on every curve. -/
private theorem isRelativelyNef_of_qLinearlyEquivalent {V Y : Scheme.{0}} [IsIntegral V]
    [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] (sV : V ⟶ Spec (.of ℂ))
    [QuasiCompact sV] {g : V ⟶ Y} {L L₂ : QDivisor V} (hL : L.QLinearlyEquivalent L₂)
    (hL₂ : L₂.IsRelativelyNef sV g) : L.IsRelativelyNef sV g := by
  obtain ⟨q, hq, φ, hφ⟩ := hL
  have hq' : ((q : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hPq := QDivisor.isQCartier_toQDivisor (Divisor.isCartier_principalDivisor φ)
  have hL₂q := hL₂.1
  have heq : L = L₂ + ((q : ℤ) : ℚ)⁻¹ • Divisor.toQDivisor (principalDivisor φ) := by
    rw [← hφ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ hq', one_smul]
    abel
  have hLq : L.IsQCartier := heq ▸ hL₂q.add (MMP.Flips.isQCartier_smul hPq _)
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sV hLq fun C hC => ?_
  have hc : ∀ (D D' : QDivisor V) (hD : D.IsQCartier) (hD' : D'.IsQCartier), D = D' →
      D.intersectionNumber ℂ sV C.ι C.dim_le hD = D'.intersectionNumber ℂ sV C.ι C.dim_le hD' := by
    rintro D _ hD hD' rfl; rfl
  have hsq := MMP.Flips.isQCartier_smul hPq (((q : ℤ) : ℚ)⁻¹)
  rw [hc _ _ hLq (hL₂q.add hsq) heq,
    QDivisor.intersectionNumber_add' ℂ sV C.ι C.dim_le _ _ hL₂q hsq (hL₂q.add hsq),
    MMP.Fourfold.intersectionNumber_smul sV C.ι C.dim_le _ hPq _ hsq,
    QDivisor.intersectionNumber_eq_of_smul ℂ sV C.ι C.dim_le _ hPq one_pos (principalDivisor φ)
      (Divisor.isCartier_principalDivisor φ) (by simp),
    MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sV C.ι C.dim_le
      (Divisor.isCartier_principalDivisor φ) ⟨φ, by simp⟩]
  simpa using MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sV hL₂ hL₂q C hC

/-- The state of the second program: an admissible model with a rational parameter `a < 1`
such that `(Y, D + (1 - c) G)` is dlt for every rational `c ∈ (a, 1]` and `K + D + (1 - a) G` is
nef over `Z`. -/
private def IsSecondProgramStage {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (n : ℕ)
    [IsLocallyNoetherian Z] [IsNormal Z] (H' KZ : Divisor Z) (BZ : QDivisor Z)
    (s : Stage Z) : Prop :=
  s.IsAdmissible sZ n H' KZ BZ ∧ ∃ a : ℚ, 0 ≤ a ∧ a < 1 ∧
    (∀ c : ℚ, a < c → c ≤ 1 → MMP.Intersection.IsDltPair s.sY (s.D + (1 - c) • s.G)) ∧
    (Divisor.toQDivisor s.K + (s.D + (1 - a) • s.G)).IsRelativelyNef s.sY s.h

open RingedSpaceModuleAdjunction in
/-- A positive multiple of an `f`-ample Cartier divisor is `f`-ample: `𝒪_X(nL) ≅ 𝒪_X(L)^{⊗ n}`
and positive tensor powers of ample invertible sheaves are ample. -/
private theorem isRelativelyAmple_nsmul_of_isRelativelyAmple {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {f : X ⟶ Y} {L : Divisor X}
    (hL : L.IsCartier) (h : L.IsRelativelyAmple f hL) (n : ℕ) (hn : 0 < n) :
    (n • L).IsRelativelyAmple f (hL.nsmul n) := by
  have := hL.isInvertibleModule_divisorialSheaf
  have := (hL.nsmul n).isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, hA⟩ := h y
  refine ⟨V, hV, hyV, ?_⟩
  obtain ⟨e0⟩ := MMP.LcBpf.nonempty_tensorPowModule_iso_divisorialSheaf L hL n
  have := Stacks.Ample.isInvertibleModule_tensorPowModule (f ⁻¹ᵁ V).toScheme
    ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L.divisorialSheaf) (n : ℤ)
  let e := (modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e0.symm ≪≫
    Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (f ⁻¹ᵁ V).ι _ n
  rw [Stacks.RelativeVeryAmple.isAmple_congr _ _ e]
  exact (Stacks.AmplePositivePower.isAmple_iff_isAmple_tensorPowModule _ n hn).1 hA

/-- **Ampleness on the flip.** If `A` is `f⁺`-ample and `B ∼_ℚ f⁺^* N`, then `α B + β A` is
`f⁺`-ample for `α ≥ 0`, `β > 0`. -/
private theorem hasRelativelyAmpleMultiple_smul_add_smul {Y' W : Scheme.{0}} [IsIntegral Y']
    [CompactSpace Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] [IsIntegral W] [CompactSpace W]
    [IsLocallyNoetherian W] [IsNormal W] {fp : Y' ⟶ W} (hfpb : IsBirationalMorphism fp)
    {A B : QDivisor Y'} {N : QDivisor W} (hN : N.IsQCartier)
    (hNf : ∀ Z : irreducibleComponents Y', fp (componentGenericPoint Y' Z) ∉ N.supp)
    (hA : A.HasRelativelyAmpleMultiple fp) (hB : B.QLinearlyEquivalent (N.pullback hN hNf))
    {α β : ℚ} (hα : 0 ≤ α) (hβ : 0 < β) : (α • B + β • A).HasRelativelyAmpleMultiple fp := by
  classical
  haveI : IsDominant fp := hfpb.isDominant
  obtain ⟨m₀, hm₀, LA, hLAc, hLA, hLAamp⟩ := hA
  obtain ⟨q, hq, φ, hφ⟩ := hB
  obtain ⟨ψ, hψ, rfl⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hfpb φ
  obtain ⟨j, hj, hjN⟩ := hN.exists_pos
  set E := hjN.toDivisor
  have hEq : Divisor.toQDivisor E = (j : ℤ) • N := hjN.toQDivisor_toDivisor
  have hEc : E.IsCartier := hjN.isCartier_toDivisor
  obtain ⟨E', hE', hpE⟩ := QDivisor.isPullback_pullback hN hNf j hj E hEq hEc
  have hE'c : E'.IsCartier := by
    rw [← Divisor.IsPullback.pullback_eq hEc hpE]; exact hEc.isCartier_pullback fp _
  -- `α = a₁ / a₂`, `β = b₁ / b₂`
  set a₁ : ℕ := α.num.toNat
  set a₂ : ℕ := α.den
  set b₁ : ℕ := β.num.toNat
  set b₂ : ℕ := β.den
  have hαe : α = (a₁ : ℚ) / a₂ := by
    have e : ((a₁ : ℕ) : ℤ) = α.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hα)
    have e' : ((a₁ : ℕ) : ℚ) = ((α.num : ℤ) : ℚ) := by rw [← e, Int.cast_natCast]
    rw [e']
    exact (Rat.num_div_den α).symm
  have hβe : β = (b₁ : ℚ) / b₂ := by
    have e : ((b₁ : ℕ) : ℤ) = β.num := Int.toNat_of_nonneg (Rat.num_pos.mpr hβ).le
    have e' : ((b₁ : ℕ) : ℚ) = ((β.num : ℤ) : ℚ) := by rw [← e, Int.cast_natCast]
    rw [e']
    exact (Rat.num_div_den β).symm
  have hb₁ : 0 < b₁ := by
    have : (0 : ℤ) < β.num := Rat.num_pos.mpr hβ
    omega
  have ha₂ : 0 < a₂ := α.den_pos
  have hb₂ : 0 < b₂ := β.den_pos
  set n₁ : ℕ := q * j * a₂ * b₁
  set n₂ : ℕ := m₀ * b₂ * a₁ * q
  set n₃ : ℕ := m₀ * j * b₂ * a₁
  set M : ℕ := m₀ * q * j * a₂ * b₂
  have hn₁ : 0 < n₁ := by positivity
  have hM : 0 < M := by positivity
  have hψc := Divisor.isCartier_principalDivisor ψ
  set L := (n₁ • LA + (n₂ : ℤ) • E') +
    (n₃ : ℤ) • principalDivisor (pullbackRationalFunction fp ψ hψ)
  have hLc : L.IsCartier :=
    ((hLAc.nsmul n₁).add (hE'c.zsmul n₂)).add
      ((Divisor.isCartier_principalDivisor _).zsmul n₃)
  refine ⟨M, hM, L, hLc, ?_, ?_⟩
  · -- the coefficients: `M (α B + β A) = n₁ L_A + n₂ E' + n₃ div(φ)`
    refine Finsupp.ext fun P => ?_
    have e1 : ((LA P : ℤ) : ℚ) = (m₀ : ℚ) * A P := by
      have h := congrArg (fun G : QDivisor Y' => G P) hLA
      change ((LA P : ℤ) : ℚ) = ((m₀ : ℤ) • A) P at h
      rw [h, Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast]
    have e2 : ((E' P : ℤ) : ℚ) = (j : ℚ) * (N.pullback hN hNf) P := by
      have h := congrArg (fun G : QDivisor Y' => G P) hE'
      change ((E' P : ℤ) : ℚ) = ((j : ℤ) • N.pullback hN hNf) P at h
      rw [h, Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast]
    have e3 : (((principalDivisor (pullbackRationalFunction fp ψ hψ)) P : ℤ) : ℚ) =
        (q : ℚ) * (B P - (N.pullback hN hNf) P) := by
      have h := congrArg (fun G : QDivisor Y' => G P) hφ
      change ((q : ℤ) • (B - N.pullback hN hNf)) P =
        (((principalDivisor (pullbackRationalFunction fp ψ hψ)) P : ℤ) : ℚ) at h
      rw [← h, Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast, Finsupp.sub_apply]
    change ((L P : ℤ) : ℚ) = ((M : ℤ) • (α • B + β • A)) P
    simp only [L, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, nsmul_eq_mul, zsmul_eq_mul,
      Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [e1, e2, e3, hαe, hβe]
    simp only [n₁, n₂, n₃, M]
    push_cast
    field_simp
    ring
  · -- `n₁ L_A` is ample, and adding pull-backs of Cartier divisors keeps it ample
    have hA₁ : (n₁ • LA).IsRelativelyAmple fp (hLAc.nsmul n₁) :=
      isRelativelyAmple_nsmul_of_isRelativelyAmple hLAc hLAamp n₁ hn₁
    have hpE₂ := hpE.zsmul hEc (n₂ : ℤ)
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' fp _)
    have hψp := (Divisor.isPullback_principalDivisor ψ hψ).zsmul hψc (n₃ : ℤ)
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' fp _)
    have hA₂ := MMP.Threefold.Resolution.isRelativelyAmple_add_of_isPullback fp
      (hLAc.nsmul n₁) hA₁ (hEc.zsmul (n₂ : ℤ)) hpE₂ (hE'c.zsmul n₂)
    exact MMP.Threefold.Resolution.isRelativelyAmple_add_of_isPullback fp _ hA₂
      (hψc.zsmul (n₃ : ℤ)) hψp ((Divisor.isCartier_principalDivisor _).zsmul n₃)

/-- **The next model of the second program.** Let `c : Y ⟶ W` be the contraction of a
`(K + D)`-negative extremal ray `R` of an admissible model, factoring `h = c ≫ h_W`, with
`K + D + (1 - e) G = c^* N` up to `ℚ`-linear equivalence for some `N` nef over `Z`, and
`f⁺ : Y' ⟶ W` a small morphism from a projective `ℚ`-factorial variety on which
`(Y', D' + (1 - c) G')` is dlt for `e < c ≤ 1`. Then `Y'` is a model of the second program with
parameter `e`. -/
private theorem isSecondProgramStage_of_step {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} {n : ℕ}
    [IsLocallyNoetherian Z] [IsNormal Z] (hZn : IsNormalVariety ℂ sZ) {H' KZ : Divisor Z}
    {BZ : QDivisor Z} {s : Stage Z} (hs : s.IsAdmissible sZ n H' KZ BZ) {W : Scheme.{0}}
    [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of ℂ)}
    [QuasiCompact sW] [LocallyOfFiniteType sW] [IsSeparated sW]
    {c : s.Y ⟶ W} (hc : IsContraction s.sY sW c) (hcb : IsBirationalMorphism c) {hW : W ⟶ Z}
    (hch : c ≫ hW = s.h) (hhW : hW ≫ sZ = sW) {e : ℚ} (he0 : 0 ≤ e) (he1 : e < 1)
    {N : QDivisor W} (hN : N.IsQCartier)
    (hNc : ∀ Z : irreducibleComponents s.Y, c (componentGenericPoint s.Y Z) ∉ N.supp)
    (hLe : (Divisor.toQDivisor s.K + (s.D + (1 - e) • s.G)).QLinearlyEquivalent
      (N.pullback hN hNc))
    (hNnef : N.IsRelativelyNef sW hW) {Y' : Scheme.{0}} [IsIntegral Y'] [CompactSpace Y']
    [IsLocallyNoetherian Y'] [IsNormal Y'] {sY' : Y' ⟶ Spec (.of ℂ)} {fp : Y' ⟶ W}
    (hfp : IsSmallMorphism sY' sW fp) (hY'p : MMP.Mori.IsProjectiveVariety ℂ sY')
    (hY'Q : IsQFactorial sY')
    (hY'K : ∃ m : ℕ, Divisor.IsCanonicalDivisor sY' m (flipTransform c fp s.K))
    (hdlt : ∀ c' : ℚ, e < c' → c' ≤ 1 → MMP.Intersection.IsDltPair sY'
      (flipTransform c fp s.D + (1 - c') • flipTransform c fp s.G)) :
    IsSecondProgramStage sZ n H' KZ BZ
      ⟨Y', sY', fp ≫ hW, flipTransform c fp s.K, flipTransform c fp s.D, flipTransform c fp s.G⟩ := by
  haveI : IsProper c := isProper_of_isProjectiveMorphism _ hc.isProjectiveMorphism
  haveI : IsProper fp := hfp.isProper
  haveI : IsDominant fp := hfp.isBirationalMorphism.isDominant
  have hcomp := hfp.comp_eq
  subst hcomp
  haveI := hY'p
  haveI : QuasiCompact (fp ≫ sW) := inferInstance
  refine ⟨hs.of_step hZn hc hcb hch hhW hfp (Or.inr ⟨hY'p, hY'Q, hY'K⟩), e, he0, he1, hdlt, ?_⟩
  change (Divisor.toQDivisor (flipTransform c fp s.K) +
    (flipTransform c fp s.D + (1 - e) • flipTransform c fp s.G)).IsRelativelyNef (fp ≫ sW)
      (fp ≫ hW)
  have hNf := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' fp N
  have htr : Divisor.toQDivisor (flipTransform c fp s.K) +
      (flipTransform c fp s.D + (1 - e) • flipTransform c fp s.G) =
      flipTransform c fp (Divisor.toQDivisor s.K + (s.D + (1 - e) • s.G)) := by
    simp only [map_add, map_rat_smul, flipTransform_toQDivisor]
  rw [htr]
  refine isRelativelyNef_of_qLinearlyEquivalent (fp ≫ sW)
    (qLinearlyEquivalent_flipTransform hcb hfp hN hNc hNf hLe) ?_
  -- `f⁺^* N` is nef over `Z`
  have hR := MMP.Fourfold.isRelativelyNef_of_isRCartierPullback (k := ℂ) (sZ := sW) (𝟙 Z) hW
    (fp ≫ hW) fp (by rw [Category.comp_id])
    (MMP.Fourfold.Oai4C1.Negativity.isRelativelyNef_toRDivisor hNnef)
    (isRCartierPullback_toRDivisor fp hN hNf)
  exact isRelativelyNef_of_isRelativelyNef_toRDivisor (fp ≫ sW)
    (QDivisor.IsPullback.isQCartier (QDivisor.isPullback_pullback hN hNf) hN) hR

/-- **One step of the second program, along a threshold ray.** At a model of the second program
with parameter `e`, let `R` be a `(K + D)`-negative extremal ray contracted over `Z` on which
`K + D + (1 - e) G` is trivial and `G` positive. Its contraction is divisorial (lowering `ρ`) or a
floor flipping contraction for `(Y, D)`, some exceptional component of `⌊D⌋` being negative on
`R`; its flip exists by `P(n)`. The next model is a model of the second program with parameter
`e`. -/
private theorem exists_secondStep_of_ray
    {n : ℕ} (hP : ProjectiveFloorProgramInputs n)
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) [IsLocallyNoetherian Z] [IsNormal Z]
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    {H' : Divisor Z} (hH'c : H'.IsCartier) (hH'r : ∀ Q, H'.coeff Q = 0 ∨ H'.coeff Q = 1)
    {KZ : Divisor Z} {BZ : QDivisor Z}
    (s : Stage Z) (hs : s.IsAdmissible sZ n H' KZ BZ) {e : ℚ} (he0 : 0 ≤ e) (he1 : e < 1)
    (hdlt : ∀ c : ℚ, e < c → c ≤ 1 → MMP.Intersection.IsDltPair s.sY (s.D + (1 - c) • s.G))
    (hnefe : (Divisor.toQDivisor s.K + (s.D + (1 - e) • s.G)).IsRelativelyNef s.sY s.h)
    {R : Set (NumericalCurveClasses s.sY)}
    (hR : IsNegativeExtremalRayOf s.sY (Divisor.toQDivisor s.K + s.D) R)
    (hRπ : ∀ C : ProperCurve s.sY, OneCycle.numericalClass s.sY (C.cycle ℝ) ∈ R →
      C.IsContractedBy s.h)
    (hLe : (Divisor.toQDivisor s.K + (s.D + (1 - e) • s.G)).IsQCartier) (hGq : s.G.IsQCartier)
    (hRe : ∀ u ∈ R, u ≠ 0 → QDivisor.curveForm s.sY _ hLe u = 0 ∧
      0 < QDivisor.curveForm s.sY s.G hGq u) :
    ∃ t : Stage Z, IsSecondProgramStage sZ n H' KZ BZ t ∧
      (picardNumber t.sY < picardNumber s.sY ∨ (picardNumber t.sY = picardNumber s.sY ∧
        IsFloorStep (fun s => s.D) s t)) := by
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  obtain ⟨m, hK⟩ := hs.isCanonicalDivisor
  have hY := hs.isProjectiveVariety
  haveI := hY
  have hQ := hs.isQFactorial
  have hQc := isQCartier_of_isQFactorial s.sY hQ
  haveI : QuasiCompact s.sY := inferInstance
  haveI : LocallyOfFiniteType s.sY := hY.toIsVariety.toLocallyOfFiniteType
  have hdltD : MMP.Intersection.IsDltPair s.sY s.D := by simpa using hdlt 1 he1 le_rfl
  have hM := (MMP.Threefold.Bridges.isDltPair_iff_isDltPair s.sY hK s.D).mp hdltD
  -- the contraction `c : Y ⟶ W` of `R`
  obtain ⟨Θ', hklt', hR'⟩ := exists_isKltPair_isNegativeExtremalRayOf hY hQ hK hdltD hR
  obtain ⟨⟨T, -, hRT⟩, W, sW, c, hc, hW, hρ, -⟩ :=
    exists_isContractionOfRay_of_isKltPair s.sY hY hklt' hK hR'
  obtain ⟨hKD, hRe', hRneg⟩ := hR
  obtain ⟨hW', hgh, -⟩ := existsUnique_comp_eq_of_isContractionOfRay hY
    hs.isProjectiveMorphism hs.comp_eq hRe' hRπ hc
  have hcb : IsBirationalMorphism c := isBirationalMorphism_of_isContractionOfRay hY
    hs.isProjectiveMorphism hs.isBirationalMorphism hs.comp_eq hRe' hRπ hc
  have hWn : IsNormalVariety ℂ sW := hc.isNormalVariety_target
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI : IsProper sW := hW.isProjective.isProjective.isProper
  haveI : LocallyOfFiniteType sW := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : IsSeparated sZ := hZ.toIsSeparated
  haveI : IsSeparated sW := hW.toIsSeparated
  haveI : IsProper c := isProper_of_isProjectiveMorphism _ hc.isProjectiveMorphism
  haveI : IsDominant c := hcb.isDominant
  haveI := surjective_of_isProper_of_isDominant c
  have hhsZ : hW' ≫ sZ = sW := comp_eq_of_isContraction hc.toIsContraction hgh hs.comp_eq
  have hface : IsContractionOfFace ℂ s.sY sW R c :=
    ⟨hY, hW, hc.comp_eq, hRe'.1, hc.isContractedBy_iff, hc.isIso_app⟩
  have hnegface : IsNegativeExtremalFace ℝ
      (closedConeOfCurves s.sY : Set (NumericalCurveClasses s.sY))
      (QDivisor.curveForm s.sY (Divisor.toQDivisor s.K + s.D) hM.1.2.2) R :=
    ⟨hRe'.1, hRe'.1.2.2.1, hRneg⟩
  -- the generating curve `T`
  set v := OneCycle.numericalClass s.sY (T.cycle ℝ)
  have hvR : v ∈ R := by rw [hRT]; exact ⟨1, zero_le_one, one_smul _ _⟩
  have hmemR : ∀ u ∈ R, ∃ t : ℝ, 0 ≤ t ∧ t • v = u := fun u hu => by rwa [hRT] at hu
  have hv0 : v ≠ 0 := by
    obtain ⟨w, hw0, hRw⟩ := hRe'.2
    obtain ⟨t, -, rfl⟩ := hmemR w (hRw ▸ ⟨1, zero_le_one, one_smul _ _⟩)
    intro h
    exact hw0 (by rw [h, smul_zero])
  have hTc : T.IsContractedBy s.h := hRπ T hvR
  -- a negative exceptional component of `⌊D⌋`
  obtain ⟨E, hEexc, hEq, hEneg⟩ :=
    exists_exceptional_curveForm_neg hZn hH'c hH'r hs T hTc hGq (hRe v hvR hv0).2
  have hcompneg : IsComponentNegative s.sY s.D R := by
    refine ⟨E, ?_, hEq, fun u hu hu0 => ?_⟩
    · rw [hs.coeff_D, hEexc]; rfl
    · obtain ⟨t, ht0, rfl⟩ := hmemR u hu
      have ht : 0 < t := lt_of_le_of_ne ht0 (by rintro rfl; exact hu0 (zero_smul _ _))
      rw [map_smul, smul_eq_mul]
      exact mul_neg_of_pos_of_neg ht hEneg
  -- `K + D + (1 - c) G` is negative on `R` for `c > e`
  have hLc : ∀ c' : ℚ, e < c' → ∀ u ∈ R, u ≠ 0 →
      QDivisor.curveForm s.sY (Divisor.toQDivisor s.K + (s.D + (1 - c') • s.G)) (hQc _) u < 0 := by
    intro c' hc' u hu hu0
    have heq : Divisor.toQDivisor s.K + (s.D + (1 - c') • s.G) =
        (Divisor.toQDivisor s.K + (s.D + (1 - e) • s.G)) + (e - c') • s.G := by
      rw [show (1 - c') = (1 - e) + (e - c') by ring, add_smul]
      abel
    rw [curveForm_congr s.sY heq _ (hLe.add (MMP.Flips.isQCartier_smul hGq _)),
      curveForm_add_smul s.sY hLe hGq (e - c') _, LinearMap.add_apply, LinearMap.smul_apply,
      (hRe u hu hu0).1, zero_add, smul_eq_mul]
    exact mul_neg_of_neg_of_pos (by exact_mod_cast sub_neg.mpr hc') (hRe u hu hu0).2
  have hampc : ∀ c' : ℚ, e < c' →
      (-(Divisor.toQDivisor s.K + (s.D + (1 - c') • s.G))).HasRelativelyAmpleMultiple c :=
    fun c' hc' => hasRelativelyAmpleMultiple_neg_of_isContractionOfRay hY hK
      ⟨hQc _, hRe', hLc c' hc'⟩ hW hc
  have hamp : (-(Divisor.toQDivisor s.K + s.D)).HasRelativelyAmpleMultiple c := by
    simpa using hampc 1 he1
  -- descent of `K + D + (1 - e) G` to `W`
  obtain ⟨N, hN, hNc, hLeN⟩ :=
    MMP.Fourfold.IsKltPair.exists_qLinearlyEquivalent_pullback_of_isContractionOfRay hklt' hY
    ⟨m, hK⟩ hR' hc hW ⟨hLe, fun C hC => by
      have hCR := (hc.isContractedBy_iff C).mp hC
      by_cases h0 : OneCycle.numericalClass s.sY (C.cycle ℝ) = 0
      · rw [h0, map_zero]
      · exact (hRe _ hCR h0).1⟩
  -- `N` is nef over `Z`
  have hNnef : N.IsRelativelyNef sW hW' := by
    have hpb : (N.pullback hN hNc).IsRelativelyNef s.sY s.h :=
      isRelativelyNef_of_qLinearlyEquivalent s.sY hLeN.symm hnefe
    have hR := MMP.Fourfold.IsRelativelyNef.of_isRCartierPullback_of_surjective (k := ℂ) c
      hc.comp_eq hW' (isRCartierPullback_toRDivisor c hN hNc)
      (by rw [hgh]; exact MMP.Fourfold.Oai4C1.Negativity.isRelativelyNef_toRDivisor hpb)
    exact isRelativelyNef_of_isRelativelyNef_toRDivisor sW hN hR
  by_cases hsm : IsSmallMorphism s.sY sW c
  · -- the flip, by `P(n)`
    have hfloor : IsFloorFlippingContraction s.sY sW s.K s.D R c :=
      ⟨⟨hKD, hRe', hRneg⟩, hc, hsm, hW, hamp, hcompneg⟩
    obtain ⟨Y', _, _, _, sY', fp, hY'p, hflip⟩ :=
      hP.2.1 s.Y s.sY s.K s.D ⟨hY, hs.dim_eq, hQ, ⟨m, hK⟩, hdltD⟩ W sW R c hfloor
    haveI : IsIntegral Y' := hflip.isNormalVariety.1.toIsIntegral
    have hfps : IsSmallMorphism sY' sW fp := ⟨hflip.isNormalVariety, hWn, hflip.comp_eq,
      hflip.isProper, hflip.isBirationalMorphism, hflip.two_le_codimension⟩
    have hfpp : IsProjectiveMorphism fp :=
      IsProjectiveMorphism.of_comp fp sW (hflip.comp_eq ▸ hY'p.isProjective)
    haveI : IsDominant fp := hfps.isBirationalMorphism.isDominant
    have hNf := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' fp N
    have hLe' : QDivisor.QLinearlyEquivalent
        (flipTransform c fp (Divisor.toQDivisor s.K + (s.D + (1 - e) • s.G)))
        (N.pullback hN hNf) := qLinearlyEquivalent_flipTransform hcb hfps hN hNc hNf hLeN
    have hampD' : (Divisor.toQDivisor (flipTransform c fp s.K) +
        flipTransform c fp s.D).HasRelativelyAmpleMultiple fp :=
      hflip.hasRelativelyAmpleMultiple
    -- the step for `D`
    have hstepD : IsProjectiveElementaryDltStep s.sY sW sY' s.K s.D R c fp
        (flipTransform c fp s.D) :=
      ⟨⟨hY, hQ, ⟨m, hK⟩, hdltD⟩, ⟨hKD, hRe', hRneg⟩, hc, hcb, hflip.comp_eq, rfl,
        Or.inl ⟨hsm, ⟨hKD, hc.toIsContraction, hsm, hamp, hfps, hfpp,
          by rw [map_add, flipTransform_toQDivisor]; exact hflip.isQCartier,
          by rw [map_add, flipTransform_toQDivisor]; exact hflip.hasRelativelyAmpleMultiple⟩⟩⟩
    have hY'D := hstepD.isProjectiveQFactorialDltPair_flipTransform hW hρ hamp
    have hQc' := isQCartier_of_isQFactorial sY' hY'D.isQFactorial
    -- the step for `D + (1 - c') G`, `e < c' ≤ 1`: the flip of `K + D` is a flip of
    -- `K + D + (1 - c') G = α (K + D + (1 - e) G) + β (K + D)`
    have hstepc : ∀ c' : ℚ, e < c' → c' ≤ 1 →
        IsProjectiveQFactorialDltPair sY' (flipTransform c fp s.K)
          (flipTransform c fp (s.D + (1 - c') • s.G)) := by
      intro c' hc' hc'1
      have he1' : (1 - e) ≠ 0 := by linarith
      have hid : Divisor.toQDivisor s.K + (s.D + (1 - c') • s.G) =
          ((1 - c') / (1 - e)) • (Divisor.toQDivisor s.K + (s.D + (1 - e) • s.G)) +
            ((c' - e) / (1 - e)) • (Divisor.toQDivisor s.K + s.D) := by
        refine Finsupp.ext fun P => ?_
        simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
        ring
      have hampc' : QDivisor.HasRelativelyAmpleMultiple (flipTransform c fp
          (Divisor.toQDivisor s.K + (s.D + (1 - c') • s.G))) fp := by
        have hflipid : flipTransform c fp (Divisor.toQDivisor s.K + (s.D + (1 - c') • s.G)) =
            ((1 - c') / (1 - e)) •
                flipTransform c fp (Divisor.toQDivisor s.K + (s.D + (1 - e) • s.G)) +
              ((c' - e) / (1 - e)) •
                (Divisor.toQDivisor (flipTransform c fp s.K) + flipTransform c fp s.D) := by
          rw [hid]
          simp only [map_add, map_rat_smul, flipTransform_toQDivisor]
        rw [hflipid]
        exact hasRelativelyAmpleMultiple_smul_add_smul hfps.isBirationalMorphism hN hNf hampD' hLe'
          (div_nonneg (by linarith) (by linarith)) (div_pos (by linarith) (by linarith))
      have hst : IsProjectiveElementaryDltStep s.sY sW sY' s.K (s.D + (1 - c') • s.G) R c fp
          (flipTransform c fp (s.D + (1 - c') • s.G)) :=
        ⟨⟨hY, hQ, ⟨m, hK⟩, hdlt c' hc' hc'1⟩, ⟨hQc _, hRe', hLc c' hc'⟩, hc, hcb, hflip.comp_eq,
          rfl, Or.inl ⟨hsm, ⟨hQc _, hc.toIsContraction, hsm, hampc c' hc', hfps, hfpp,
            hQc' _, hampc'⟩⟩⟩
      exact hst.isProjectiveQFactorialDltPair_flipTransform hW hρ (hampc c' hc')
    refine ⟨⟨Y', sY', fp ≫ hW', flipTransform c fp s.K, flipTransform c fp s.D,
      flipTransform c fp s.G⟩, isSecondProgramStage_of_step hZn hs hc.toIsContraction hcb hgh hhsZ
        he0 he1 hN hNc hLeN hNnef hfps hY'p hY'D.isQFactorial hY'D.isCanonicalDivisor
        (fun c' hc' hc'1 => by
          have := (hstepc c' hc' hc'1).isDltPair
          rwa [map_add, map_rat_smul] at this),
      Or.inr ⟨picardNumber_eq_of_isFlip hQ hM hRe' hnegface hface hflip,
        W, sW, R, c, fp, hY'p, hfloor, hflip, rfl, rfl⟩⟩
  · -- the divisorial contraction: the next model is `W`
    have hstepc : ∀ c' : ℚ, e < c' → c' ≤ 1 →
        IsProjectiveQFactorialDltPair sW (flipTransform c (𝟙 W) s.K)
          (flipTransform c (𝟙 W) (s.D + (1 - c') • s.G)) := by
      intro c' hc' hc'1
      have hst : IsProjectiveElementaryDltStep s.sY sW sW s.K (s.D + (1 - c') • s.G) R c (𝟙 W)
          (flipTransform c (𝟙 W) (s.D + (1 - c') • s.G)) :=
        ⟨⟨hY, hQ, ⟨m, hK⟩, hdlt c' hc' hc'1⟩, ⟨hQc _, hRe', hLc c' hc'⟩, hc, hcb,
          Category.id_comp _, rfl, Or.inr ⟨hsm, inferInstance⟩⟩
      exact hst.isProjectiveQFactorialDltPair_flipTransform hW hρ (hampc c' hc')
    have hW1 := hstepc 1 he1 le_rfl
    refine ⟨⟨W, sW, 𝟙 W ≫ hW', flipTransform c (𝟙 W) s.K, flipTransform c (𝟙 W) s.D,
      flipTransform c (𝟙 W) s.G⟩, isSecondProgramStage_of_step hZn hs hc.toIsContraction hcb hgh
        hhsZ he0 he1 hN hNc hLeN hNnef (isSmallMorphism_id hWn) hW hW1.isQFactorial
        hW1.isCanonicalDivisor
        (fun c' hc' hc'1 => by
          have := (hstepc c' hc' hc'1).isDltPair
          rwa [map_add, map_rat_smul] at this), Or.inl ?_⟩
    haveI := hW
    change picardNumber sW < picardNumber s.sY
    rw [← IsDltPair.picardNumber_add_one_eq_of_isContractionOfFace hM hQ hRe' hRneg hface]
    exact (ENat.lt_add_one_iff (picardNumber_lt_top_of_isProjectiveVariety sW).ne).2 le_rfl

/-- On a curve contracted by `g`, an `ℝ`-divisor `A + c B` nef over `Y` has nonnegative
intersection number `(A · C) + c (B · C)`. -/
private theorem le_of_isRelativelyNef_toRDivisor_add_smul {V Y : Scheme.{0}}
    [IsLocallyNoetherian V] [IsNormal V] (sV : V ⟶ Spec (.of ℂ)) [QuasiCompact sV] {g : V ⟶ Y}
    {A B : QDivisor V} (hA : A.IsQCartier) (hB : B.IsQCartier) {c : ℝ}
    (h : MMP.Flips.IsRelativelyNef ℂ sV g (QDivisor.toRDivisor A + c • QDivisor.toRDivisor B))
    (C : ProperCurve sV) (hC : C.IsContractedBy g) :
    (0 : ℝ) ≤ (A.intersectionNumber ℂ sV C.ι C.dim_le hA : ℝ) +
      c * (B.intersectionNumber ℂ sV C.ι C.dim_le hB : ℝ) := by
  obtain ⟨m, r, L, hL, hD, hx⟩ := h
  have hI' : MMP.Flips.IsRIntersectionNumber ℂ sV
      (QDivisor.toRDivisor A + c • QDivisor.toRDivisor B) r L C
      (∑ j, r j * ((L j).degreeOn ℂ sV C.ι C.dim_le (hL j) : ℝ)) :=
    ⟨hL, fun j => (L j).degreeOn ℂ sV C.ι C.dim_le (hL j), hD,
      fun j => MMP.Flips.isCartierIntersectionNumber_degreeOn ℂ sV C (L j) (hL j), rfl⟩
  obtain ⟨rA, LA, hIA⟩ := isRIntersectionNumber_toRDivisor sV hA C
  obtain ⟨rB, LB, hIB⟩ := isRIntersectionNumber_toRDivisor sV hB C
  have hIAB := (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sV C).2 _ _ _ _ _ _ _ _ 1 c hIA hIB
  rw [one_smul, one_mul] at hIAB
  rw [(MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sV C).1 _ _ _ _ _ _ _ hIAB hI']
  exact hx C hC _ hI'

/-- **Relative classes come from contracted curves.** For a morphism `h : Y ⟶ Z` of projective
varieties, a curve whose class lies in the image of `N₁(Y/Z)` is contracted by `h`: its
push-forward vanishes, so an ample invertible sheaf of `Z` pulls back to degree zero on it. -/
private theorem isContractedBy_of_numericalClass_mem_range {Y Z : Scheme.{0}} [IsIntegral Y]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    (sZ : Z ⟶ Spec (.of ℂ)) [MMP.Mori.IsProjectiveVariety ℂ sY]
    [MMP.Mori.IsProjectiveVariety ℂ sZ] (h : Y ⟶ Z) (hh : h ≫ sZ = sY) (C : ProperCurve sY)
    (hC : OneCycle.numericalClass sY (C.cycle ℝ) ∈ LinearMap.range (relativeToAbsolute sY h)) :
    C.IsContractedBy h := by
  have hZp : MMP.Mori.IsProjectiveVariety ℂ sZ := ‹_›
  haveI : IsSeparated sZ := hZp.toIsSeparated
  haveI : LocallyOfFiniteType sZ := hZp.toIsVariety.toLocallyOfFiniteType
  haveI : QuasiCompact sZ := inferInstance
  haveI : LocallyOfFiniteType sY :=
    (‹MMP.Mori.IsProjectiveVariety ℂ sY›).toIsVariety.toLocallyOfFiniteType
  obtain ⟨H, hH, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hZp
  refine MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero h hh H hHa C ?_
  have h0 : NumericalCurveClasses.pushforward h hh (OneCycle.numericalClass sY (C.cycle ℝ)) = 0 :=
    MMP.Mori.range_relativeToAbsolute_le_ker_pushforward h hh hC
  have := NumericalCurveClasses.degree_pushforward h hh H (OneCycle.numericalClass sY (C.cycle ℝ))
  rw [h0, map_zero, NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle] at this
  exact_mod_cast this.symm

/-- **The support sandwich.** On an admissible model, for `0 < t < 1`, the reduced part of
`D + t G` is supported on the exceptional prime divisors, which lie over `H'`, and every prime
divisor over `H'` has positive coefficient in `D + t G`:
`Supp ⌊D + t G⌋ ⊆ Supp h^* H' ⊆ Supp (D + t G)`. -/
private theorem supp_roundDown_le_supp_pullback {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsLocallyNoetherian Z] [IsNormal Z] (hZn : IsNormalVariety ℂ sZ) {n : ℕ}
    {H' KZ : Divisor Z} {BZ : QDivisor Z} (hH'c : H'.IsCartier)
    (hH'r : ∀ Q, H'.coeff Q = 0 ∨ H'.coeff Q = 1) (hBZ : ∀ Q, 0 ≤ BZ.coeff Q ∧ BZ.coeff Q < 1)
    (hBH : ∀ Q, H'.coeff Q ≠ 0 → BZ.coeff Q = 0) {s : Stage Z}
    (hs : s.IsAdmissible sZ n H' KZ BZ)
    (hHf : ∀ W : irreducibleComponents s.Y, s.h (componentGenericPoint s.Y W) ∉ H'.supp)
    {t : ℚ} (ht0 : 0 < t) (ht1 : t < 1) :
    (s.D + t • s.G).roundDown.supp ≤ (H'.pullback hH'c hHf).supp ∧
      (H'.pullback hH'c hHf).supp ≤ (s.D + t • s.G).supp := by
  classical
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI := isSeparated_toTerminal_of_isNormalVariety hZn
  have hHe : DivisorWithCoeffs.IsEffective H' := fun E => by
    rcases hH'r E with h | h <;> simp [h]
  have hHp : H'.IsPullback s.h hHf (H'.pullback hH'c hHf) := Divisor.isPullback_pullback hH'c hHf
  have hsupp := MMP.Flips.supp_eq_preimage_supp_of_isPullback hH'c hHe hHp
  have hcoeff : ∀ P, (s.D + t • s.G).coeff P = s.D.coeff P + t * s.G.coeff P := fun P => rfl
  -- a prime divisor whose generic point lies over `Supp H'` lies in `Supp h^* H'`
  have hsub : ∀ P : MMP.Mori.PrimeDivisor s.Y, s.h P.genericPoint ∈ H'.supp →
      (P.support : Set s.Y) ⊆ (H'.pullback hH'c hHf).supp := by
    intro P hP
    have hη : P.genericPoint ∈ ((H'.pullback hH'c hHf).supp : Set s.Y) := by
      rwa [hsupp]
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.mpr hη) (H'.pullback hH'c hHf).supp.isClosed
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨P, hP0, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    rw [DivisorWithCoeffs.coeff_roundDown, hcoeff] at hP0
    refine hsub P ?_ hxP
    rcases hP' : RationalMap.transformPrimeDivisor s.h.toRationalMap P with _ | Q
    · exact hs.exceptional_mem P hP'
    · exfalso
      apply hP0
      have hD := hs.coeff_D P
      have hG := hs.coeff_G P
      rw [hP'] at hD hG
      simp only [Option.elim] at hD hG
      rw [hD, hG, Int.floor_eq_zero_iff]
      obtain ⟨h0, h1⟩ := hBZ Q
      rcases hH'r Q with hq | hq
      · rw [hq]; push_cast; constructor <;> linarith
      · rw [hq, hBH Q (by rw [hq]; exact one_ne_zero)]; push_cast; constructor <;> linarith
  · obtain ⟨P, hP0, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    refine DivisorWithCoeffs.support_subset_supp ?_ hxP
    have hPs : P.genericPoint ∈ ((H'.pullback hH'c hHf).supp : Set s.Y) :=
      DivisorWithCoeffs.support_subset_supp hP0
        (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P)
    rw [hsupp] at hPs
    rw [hcoeff]
    rcases hP' : RationalMap.transformPrimeDivisor s.h.toRationalMap P with _ | Q
    · have hD := hs.coeff_D P
      have hG := hs.coeff_G P
      rw [hP'] at hD hG
      simp only [Option.elim] at hD hG
      rw [hD, hG]
      norm_num
    · have hPQ := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff s.h P Q).mp hP'
      have hQs : Q.genericPoint ∈ H'.supp := by rwa [← hPQ]
      obtain ⟨Q', hQ'0, hQ'⟩ := DivisorWithCoeffs.mem_supp_iff.mp hQs
      obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hQ'
      have hq1 : H'.coeff Q' = 1 := (hH'r Q').resolve_left hQ'0
      have hD := hs.coeff_D P
      have hG := hs.coeff_G P
      rw [hP'] at hD hG
      simp only [Option.elim] at hD hG
      rw [hD, hG, hq1, hBH Q' hQ'0]
      push_cast
      positivity

/-! ### The boundary-removal threshold

The threshold ray is found from the finiteness of the negative extremal rays of `NE̅(Y/Z)` for
the boundaries `D + (1 - c₀) G`, `0 < c₀ < 1`, which are dlt on a model of the second program;
the boundary `D + G` itself need not be. -/

/-- On curves contracted by `g`, nonnegativity of `(A · C) + c (B · C)` makes the `ℝ`-divisor
`A + c B` nef over `Y`. -/
private theorem isRelativelyNef_toRDivisor_add_smul_of_le {V Y : Scheme.{0}}
    [IsLocallyNoetherian V] [IsNormal V] (sV : V ⟶ Spec (.of ℂ)) [QuasiCompact sV] {g : V ⟶ Y}
    {A B : QDivisor V} (hA : A.IsQCartier) (hB : B.IsQCartier) {c : ℝ}
    (h : ∀ C : ProperCurve sV, C.IsContractedBy g →
      (0 : ℝ) ≤ (A.intersectionNumber ℂ sV C.ι C.dim_le hA : ℝ) +
        c * (B.intersectionNumber ℂ sV C.ι C.dim_le hB : ℝ)) :
    MMP.Flips.IsRelativelyNef ℂ sV g (QDivisor.toRDivisor A + c • QDivisor.toRDivisor B) := by
  obtain ⟨FA, hFA, hFAc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hA
  obtain ⟨FB, hFB, hFBc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hB
  have hNA : (((A.cartierIndex hA : ℕ) : ℤ)) ≠ 0 := by
    exact_mod_cast (QDivisor.cartierIndex_pos hA).ne'
  have hNB : (((B.cartierIndex hB : ℕ) : ℤ)) ≠ 0 := by
    exact_mod_cast (QDivisor.cartierIndex_pos hB).ne'
  refine ⟨2, ![((((A.cartierIndex hA : ℕ) : ℤ) : ℝ))⁻¹,
    c * ((((B.cartierIndex hB : ℕ) : ℤ) : ℝ))⁻¹], ![FA, FB],
    Fin.forall_fin_two.2 ⟨hFAc, hFBc⟩, ?_, fun C hC x hx => ?_⟩
  · rw [Fin.sum_univ_two, QDivisor.toRDivisor_eq_inv_smul hNA hFA,
      QDivisor.toRDivisor_eq_inv_smul hNB hFB, smul_smul]
    rfl
  · obtain ⟨rA, LA, hIA⟩ := isRIntersectionNumber_toRDivisor sV hA C
    obtain ⟨rB, LB, hIB⟩ := isRIntersectionNumber_toRDivisor sV hB C
    have hIAB :=
      (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sV C).2 _ _ _ _ _ _ _ _ 1 c hIA hIB
    rw [one_smul, one_mul] at hIAB
    rw [← (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sV C).1 _ _ _ _ _ _ _ hIAB hx]
    exact h C hC

/-- **Nefness on curves.** For `ℚ`-Cartier `A, B` and `c ∈ ℝ`, the `ℝ`-divisor `A + c B` is nef
over `Y` if and only if `(A · C) + c (B · C) ≥ 0` for every curve `C` contracted by `g`. -/
private theorem isRelativelyNef_toRDivisor_add_smul_iff {V Y : Scheme.{0}} [CompactSpace V]
    [IsLocallyNoetherian V] [IsNormal V] (sV : V ⟶ Spec (.of ℂ)) [QuasiCompact sV] (g : V ⟶ Y)
    {A B : QDivisor V} (hA : A.IsQCartier) (hB : B.IsQCartier) (c : ℝ) :
    MMP.Flips.IsRelativelyNef ℂ sV g (QDivisor.toRDivisor A + c • QDivisor.toRDivisor B) ↔
      ∀ (C : ProperCurve sV) (hC : C.IsContractedBy g),
        0 ≤ QDivisor.curveForm sV A hA (relativeToAbsolute sV g (C.relativeClass g hC)) +
          c * QDivisor.curveForm sV B hB (relativeToAbsolute sV g (C.relativeClass g hC)) := by
  have hcyc : ∀ (C : ProperCurve sV) (hC : C.IsContractedBy g),
      relativeToAbsolute sV g (C.relativeClass g hC) = OneCycle.numericalClass sV (C.cycle ℝ) :=
    fun _ _ => rfl
  constructor
  · intro h C hC
    rw [hcyc, MMP.ProgramBaseChange.curveForm_numericalClass_cycle sV A hA C,
      MMP.ProgramBaseChange.curveForm_numericalClass_cycle sV B hB C]
    exact le_of_isRelativelyNef_toRDivisor_add_smul sV hA hB h C hC
  · intro h
    refine isRelativelyNef_toRDivisor_add_smul_of_le sV hA hB fun C hC => ?_
    have := h C hC
    rwa [hcyc, MMP.ProgramBaseChange.curveForm_numericalClass_cycle sV A hA C,
      MMP.ProgramBaseChange.curveForm_numericalClass_cycle sV B hB C] at this

/-- The curve form of a `ℚ`-Cartier divisor is continuous on `N₁(X/Z)`. -/
private theorem continuous_curveForm_relativeToAbsolute {V Y : Scheme.{0}} [CompactSpace V]
    [IsLocallyNoetherian V] [IsNormal V] {sV : V ⟶ Spec (.of ℂ)} {g : V ⟶ Y} (A : QDivisor V)
    (hA : A.IsQCartier) :
    Continuous fun z : RelativeNumericalCurveClasses sV g =>
      QDivisor.curveForm sV A hA (relativeToAbsolute sV g z) := by
  have hdeg : ∀ (L : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 L]
      (z : RelativeNumericalCurveClasses sV g),
      NumericalCurveClasses.degree sV L (relativeToAbsolute sV g z) =
        RelativeNumericalCurveClasses.degree sV g L z := by
    intro L _ z
    obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sV g z
    rfl
  simp only [QDivisor.curveForm, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]
  apply continuous_finset_sum
  intro E _
  have := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
  simp only [hdeg]
  exact continuous_const.mul (RelativeNumericalCurveClasses.continuous_degree sV g _)

/-- A continuous linear form on `N₁(X/Z)` which is nonnegative on the classes of the contracted
curves is nonnegative on the closed relative cone `NE̅(X/Z)`. -/
private theorem nonneg_of_mem_relativeClosedConeOfCurves {V Y : Scheme.{0}}
    {sV : V ⟶ Spec (.of ℂ)} {g : V ⟶ Y} (ψ : RelativeNumericalCurveClasses sV g →ₗ[ℝ] ℝ)
    (hψ : Continuous ψ) (h : ∀ (C : ProperCurve sV) (hC : C.IsContractedBy g),
      0 ≤ ψ (C.relativeClass g hC))
    {z : RelativeNumericalCurveClasses sV g} (hz : z ∈ relativeClosedConeOfCurves sV g) :
    0 ≤ ψ z := by
  have hcl : z ∈ closure (relativeConeOfCurves sV g : Set _) := by
    rwa [← coe_relativeClosedConeOfCurves]
  refine closure_minimal (fun z hz => ?_) (isClosed_le continuous_const hψ) hcl
  change z ∈ PointedCone.hull ℝ _ at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨C, hC⟩, rfl⟩ := hx
    exact h C hC
  | zero => simp
  | add x y _ _ hx hy =>
    change 0 ≤ ψ (x + y)
    rw [map_add]; exact add_nonneg hx hy
  | smul a x _ hx =>
    change 0 ≤ ψ (a • x)
    rw [LinearMap.map_smul_of_tower]
    change 0 ≤ (a : ℝ) * ψ x
    exact mul_nonneg a.2 hx

/-- **A negative ray.** For a morphism of projective varieties, a linear form on `N₁(X/Z)`
negative on the class of some contracted curve is negative on the nonzero elements of some
extremal ray of `NE̅(X/Z)`. -/
private theorem exists_isExtremalRay_neg {V Y : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)}
    (sY : Y ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsProjectiveVariety ℂ sV]
    [AlgebraicGeometry.IsProjectiveVariety ℂ sY] {g : V ⟶ Y} (hg : g ≫ sY = sV)
    (ψ : RelativeNumericalCurveClasses sV g →ₗ[ℝ] ℝ) {C : ProperCurve sV}
    (hC : C.IsContractedBy g) (hneg : ψ (C.relativeClass g hC) < 0) :
    ∃ R : Set (RelativeNumericalCurveClasses sV g),
      IsExtremalRay ℝ (relativeClosedConeOfCurves sV g : Set _) R ∧
        ∀ u ∈ R, u ≠ 0 → ψ u < 0 := by
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  have hz : C.relativeClass g hC ∈ relativeClosedConeOfCurves sV g := by
    rw [← SetLike.mem_coe, coe_relativeClosedConeOfCurves]
    exact subset_closure (relativeClass_mem_relativeConeOfCurves hC)
  obtain ⟨s, R, w, hRw, hsum⟩ :=
    exists_sum_mem_isExtremalRay_relativeClosedConeOfCurves sV sY g hg hz
  rw [hsum, map_sum] at hneg
  have hneg' : ∑ i, ψ (w i) < ∑ _i : Fin s, (0 : ℝ) := by simpa using hneg
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt hneg'
  refine ⟨R i, (hRw i).1, ?_⟩
  obtain ⟨-, v, -, hRv⟩ := (hRw i).1
  obtain ⟨c, hc, hcv⟩ : w i ∈ {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} := hRv ▸ (hRw i).2
  have hψv : ψ v < 0 := by
    by_contra hv
    push Not at hv
    rw [← hcv, map_smul, smul_eq_mul] at hi
    exact absurd hi (not_lt.mpr (mul_nonneg hc hv))
  intro u hu hu0
  rw [hRv] at hu
  obtain ⟨c', hc', rfl⟩ := hu
  have hc'0 : c' ≠ 0 := by rintro rfl; simp at hu0
  rw [map_smul, smul_eq_mul]
  exact mul_neg_of_pos_of_neg (lt_of_le_of_ne hc' (Ne.symm hc'0)) hψv

/-- **The attained boundary-removal threshold.** Let `h : Y ⟶ Z` be a projective birational
morphism of normal projective varieties, `Y` `ℚ`-factorial, `D, G ≥ 0` with `(Y, D + (1 - c) G)`
dlt for every rational `0 < c < 1`, `K + D + G` nef over `Z` and `K + D` not, and `H ≥ 0`
Cartier on `Z` with `Supp ⌊D + (1 - c) G⌋ ⊆ Supp h^*H ⊆ Supp (D + (1 - c) G)` for `0 < c < 1`.
Then `e = sup {c ∈ [0, 1] | K + D + (1 - c) G nef over Z}` is a rational number `e < 1`, and
there is a `(K + D)`-negative extremal ray of `NE̅(Y/Z)` on which `K + D + (1 - e) G` has degree
`0` and `G` positive degree.

Write `φ = (K + D) · -` and `γ = G · -`. Fix a rational `c₀ ∈ (e, 1)`; the
`(K + D + (1 - c₀) G)`-negative extremal rays form a finite set `𝓡`, each spanned by a contracted
curve. If no ray of `𝓡` with `γ > 0` had `φ + (1 - e) γ = 0`, all of them would stay
`(φ + (1 - c) γ)`-positive for `c > e` near `e`; but `K + D + (1 - c) G` is not nef, so some
extremal ray is `(φ + (1 - c) γ)`-negative, it has `γ > 0` by nefness at `e`, hence lies in `𝓡`.
On the curve spanning the ray found, `φ` and `γ` are rational, so `e = 1 + φ / γ` is rational. -/
private theorem exists_isNegativeRelativeExtremalRayOf_of_forall_isDltPair {Y Z : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [AlgebraicGeometry.IsProjectiveVariety ℂ sY] [AlgebraicGeometry.IsProjectiveVariety ℂ sZ]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian Z] [IsNormal Z]
    (hY : IsQFactorial sY) (hZ : IsNormalVariety ℂ sZ)
    {h : Y ⟶ Z} (hh : h ≫ sZ = sY) (hhp : IsProjectiveMorphism h)
    (hhb : IsBirationalMorphism h)
    {K : Divisor Y} (hK : ∃ n : ℕ, K.IsCanonicalDivisor sY n)
    {D G : QDivisor Y}
    (hDG : ∀ c : ℚ, 0 < c → c < 1 → MMP.Intersection.IsDltPair sY (D + (1 - c) • G))
    (hnef : MMP.Flips.IsRelativelyNef ℂ sY h
      (QDivisor.toRDivisor (Divisor.toQDivisor K + D + G)))
    (hnotnef : ¬ MMP.Flips.IsRelativelyNef ℂ sY h
      (QDivisor.toRDivisor (Divisor.toQDivisor K + D)))
    {H : Divisor Z} (hH : H.IsCartier) (hHe : H.IsEffective)
    (hHf : ∀ W : irreducibleComponents Y, h (componentGenericPoint Y W) ∉ H.supp)
    (hsand : ∀ c : ℚ, 0 < c → c < 1 →
      (D + (1 - c) • G).roundDown.supp ≤ (H.pullback hH hHf).supp ∧
        (H.pullback hH hHf).supp ≤ (D + (1 - c) • G).supp) :
    ∃ e : ℚ, (e : ℝ) = sSup {c : ℝ | c ∈ Set.Icc 0 1 ∧ MMP.Flips.IsRelativelyNef ℂ sY h
        (QDivisor.toRDivisor (Divisor.toQDivisor K + D) + (1 - c) • QDivisor.toRDivisor G)} ∧
      e < 1 ∧ ∃ R : Set (RelativeNumericalCurveClasses sY h),
        IsNegativeRelativeExtremalRayOf sY h (Divisor.toQDivisor K + D) R ∧
        ∃ (he : (Divisor.toQDivisor K + D + (1 - e) • G).IsQCartier) (hGq : G.IsQCartier),
          ∀ u ∈ R, u ≠ 0 →
            QDivisor.relativeCurveForm sY h (Divisor.toQDivisor K + D + (1 - e) • G) he u = 0 ∧
              0 < QDivisor.relativeCurveForm sY h G hGq u := by
  classical
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  have hq : ∀ M : QDivisor Y, M.IsQCartier := isQCartier_of_isQFactorial sY hY
  set A : QDivisor Y := Divisor.toQDivisor K + D with hA
  set φ : RelativeNumericalCurveClasses sY h →ₗ[ℝ] ℝ :=
    QDivisor.curveForm sY A (hq A) ∘ₗ relativeToAbsolute sY h with hφ
  set γ : RelativeNumericalCurveClasses sY h →ₗ[ℝ] ℝ :=
    QDivisor.curveForm sY G (hq G) ∘ₗ relativeToAbsolute sY h with hγ
  have hφc : Continuous φ := continuous_curveForm_relativeToAbsolute A (hq A)
  have hγc : Continuous γ := continuous_curveForm_relativeToAbsolute G (hq G)
  -- the nef parameters
  set P : ℝ → Prop := fun c => ∀ (C : ProperCurve sY) (hC : C.IsContractedBy h),
    0 ≤ φ (C.relativeClass h hC) + (1 - c) * γ (C.relativeClass h hC) with hP
  have hnefiff : ∀ s : ℝ, MMP.Flips.IsRelativelyNef ℂ sY h
      (QDivisor.toRDivisor A + s • QDivisor.toRDivisor G) ↔
        ∀ (C : ProperCurve sY) (hC : C.IsContractedBy h),
          0 ≤ φ (C.relativeClass h hC) + s * γ (C.relativeClass h hC) := fun s =>
    isRelativelyNef_toRDivisor_add_smul_iff sY h (hq A) (hq G) s
  set S : Set ℝ := {c : ℝ | c ∈ Set.Icc 0 1 ∧ MMP.Flips.IsRelativelyNef ℂ sY h
    (QDivisor.toRDivisor A + (1 - c) • QDivisor.toRDivisor G)} with hS
  have hSP : ∀ c, c ∈ S ↔ c ∈ Set.Icc 0 1 ∧ P c := fun c => and_congr_right' (hnefiff _)
  have h0 : P 0 := fun C hC => by
    have := (hnefiff 1).1 (by simpa [map_add] using hnef)
    simpa using this C hC
  have h1 : ¬ P 1 := by
    intro hP1
    exact hnotnef (by simpa using (hnefiff 0).2 fun C hC => by simpa using hP1 C hC)
  have h0S : (0 : ℝ) ∈ S := (hSP 0).2 ⟨⟨le_rfl, zero_le_one⟩, h0⟩
  have hSbdd : BddAbove S := ⟨1, fun c hc => hc.1.2⟩
  set e : ℝ := sSup S with he
  have he0 : 0 ≤ e := le_csSup hSbdd h0S
  have he1 : e ≤ 1 := csSup_le ⟨0, h0S⟩ fun c hc => hc.1.2
  have hPe : P e := by
    intro C hC
    set x := φ (C.relativeClass h hC)
    set y := γ (C.relativeClass h hC)
    have hx0 : 0 ≤ x + (1 - 0) * y := h0 C hC
    by_cases hy : y ≤ 0
    · nlinarith
    · push Not at hy
      have hle : e ≤ (x + y) / y := csSup_le ⟨0, h0S⟩ fun c hc => by
        have := ((hSP c).1 hc).2 C hC
        rw [le_div_iff₀ hy]; nlinarith
      rw [le_div_iff₀ hy] at hle
      nlinarith
  have hnotP : ∀ c, e < c → c ≤ 1 → ¬ P c := fun c hec hc1 hPc =>
    absurd (le_csSup hSbdd ((hSP c).2 ⟨⟨by linarith, hc1⟩, hPc⟩)) (not_le.2 hec)
  have he_lt : e < 1 := lt_of_le_of_ne he1 fun h1e => h1 (h1e ▸ hPe)
  -- nefness at `e` on the closed cone
  have hψe : ∀ z ∈ relativeClosedConeOfCurves sY h, 0 ≤ φ z + (1 - e) * γ z := by
    intro z hz
    have := nonneg_of_mem_relativeClosedConeOfCurves (φ + (1 - e) • γ)
      (by rw [LinearMap.coe_add, LinearMap.coe_smul]; exact hφc.add (hγc.const_smul _))
      (fun C hC => by simpa using hPe C hC) hz
    simpa using this
  -- a fixed rational `c₀ ∈ (e, 1)` and the finite set of rays
  obtain ⟨c₀, hec₀, hc₀1⟩ := exists_rat_btwn he_lt
  have hc₀pos : (0 : ℚ) < c₀ := by exact_mod_cast he0.trans_lt hec₀
  have hc₀1' : c₀ < 1 := by exact_mod_cast hc₀1
  have hs : IsProjectiveSetting ℂ sY sZ h := ⟨inferInstance, inferInstance, inferInstance,
    inferInstance, hh⟩
  obtain ⟨hKB, 𝓡, hfin, hmem, hgen, -⟩ :=
    exists_finite_isExtremalRay_of_support_roundDown_subset_pullback sY sZ h hs hhp hhb hZ hY hK
      (hDG c₀ hc₀pos hc₀1') hH hHe hHf (hsand c₀ hc₀pos hc₀1').1 (hsand c₀ hc₀pos hc₀1').2
  have hform : ∀ u, QDivisor.curveForm sY (Divisor.toQDivisor K + (D + (1 - c₀) • G)) hKB
      (relativeToAbsolute sY h u) = φ u + (1 - (c₀ : ℝ)) * γ u := by
    intro u
    rw [curveForm_congr sY (show Divisor.toQDivisor K + (D + (1 - c₀) • G) = A + (1 - c₀) • G by
      rw [hA, add_assoc]) hKB (hq _),
      curveForm_add_smul sY (hq A) (hq G) (1 - c₀) (hq _)]
    simp [φ, γ]
  -- some ray of `𝓡` is `G`-positive and `(K + D + (1 - e) G)`-trivial
  have hclaim : ∃ R ∈ 𝓡, ∀ u ∈ R, u ≠ 0 → 0 < γ u ∧ φ u + (1 - e) * γ u ≤ 0 := by
    by_contra hcon
    push Not at hcon
    choose! w hwR hw0 hwpos using hcon
    have hev : ∀ᶠ c in nhds e, ∀ R ∈ 𝓡, 0 < γ (w R) → 0 < φ (w R) + (1 - c) * γ (w R) := by
      refine (Filter.eventually_all_finite hfin).2 fun R hR => ?_
      by_cases hγR : 0 < γ (w R)
      · have hpos := hwpos R hR hγR
        have ht : Filter.Tendsto (fun c : ℝ => φ (w R) + (1 - c) * γ (w R)) (nhds e)
            (nhds (φ (w R) + (1 - e) * γ (w R))) :=
          ((continuous_const.add ((continuous_const.sub continuous_id).mul
            continuous_const)).tendsto e)
        exact (ht.eventually (lt_mem_nhds hpos)).mono fun c hc _ => hc
      · exact Filter.Eventually.of_forall fun c hc => absurd hc hγR
    obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨c, hec, hcc⟩ := exists_rat_btwn (lt_min (lt_add_of_pos_right e hε) hec₀)
    have hcε : (c : ℝ) < e + ε := hcc.trans_le (min_le_left _ _)
    have hcc₀ : (c : ℝ) < c₀ := hcc.trans_le (min_le_right _ _)
    have hnPc := hnotP c hec (hcc₀.trans hc₀1).le
    simp only [hP, not_forall, not_le] at hnPc
    obtain ⟨C, hC, hCneg⟩ := hnPc
    obtain ⟨R', hR', hR'neg⟩ := exists_isExtremalRay_neg sZ hh (φ + (1 - (c : ℝ)) • γ) hC
      (by simpa using hCneg)
    have hR'neg' : ∀ u ∈ R', u ≠ 0 → φ u + (1 - (c : ℝ)) * γ u < 0 := fun u hu hu0 => by
      simpa using hR'neg u hu hu0
    have hγR' : ∀ u ∈ R', u ≠ 0 → 0 < γ u := fun u hu hu0 => by
      have h1 := hR'neg' u hu hu0
      have h2 := hψe u (hR'.1.1 hu)
      nlinarith
    have hR'𝓡 : R' ∈ 𝓡 := (hmem R').2 ⟨hR', fun u hu hu0 => by
      rw [hform]
      have h1 := hR'neg' u hu hu0
      have h2 := hγR' u hu hu0
      nlinarith⟩
    have hdist : dist (c : ℝ) e < ε := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith
    have := hεP hdist R' hR'𝓡 (hγR' _ (hwR R' hR'𝓡) (hw0 R' hR'𝓡))
    exact absurd (hR'neg' _ (hwR R' hR'𝓡) (hw0 R' hR'𝓡)) (not_lt.2 this.le)
  obtain ⟨R, hR𝓡, hRgood⟩ := hclaim
  obtain ⟨hRext, hRneg₀⟩ := (hmem R).1 hR𝓡
  obtain ⟨C, hC, -, hRC⟩ := hgen R hR𝓡
  set ξ := C.relativeClass h hC with hξ
  have hξR : ξ ∈ R := by rw [hRC]; exact ⟨1, zero_le_one, one_smul _ _⟩
  have hξ0 : ξ ≠ 0 := by
    intro hξ0
    obtain ⟨-, v, hv0, hRv⟩ := hRext
    have hvR : v ∈ R := by rw [hRv]; exact ⟨1, zero_le_one, one_smul _ _⟩
    rw [hRC] at hvR
    obtain ⟨t, -, ht⟩ := hvR
    rw [hξ0, smul_zero] at ht
    exact hv0 ht.symm
  obtain ⟨hγξ, hψξ⟩ := hRgood ξ hξR hξ0
  have hψξ0 : φ ξ + (1 - e) * γ ξ = 0 :=
    le_antisymm hψξ (hψe ξ (hRext.1.1 hξR))
  have hφξ : φ ξ = (A.intersectionNumber ℂ sY C.ι C.dim_le (hq A) : ℚ) :=
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle sY A (hq A) C
  have hγξ' : γ ξ = (G.intersectionNumber ℂ sY C.ι C.dim_le (hq G) : ℚ) :=
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle sY G (hq G) C
  set q₁ : ℚ := A.intersectionNumber ℂ sY C.ι C.dim_le (hq A)
  set q₂ : ℚ := G.intersectionNumber ℂ sY C.ι C.dim_le (hq G)
  have hq₂pos : (0 : ℝ) < q₂ := hγξ' ▸ hγξ
  set e' : ℚ := 1 + q₁ / q₂ with he'
  have he'e : (e' : ℝ) = e := by
    rw [he']; push_cast
    rw [hφξ, hγξ'] at hψξ0
    field_simp
    linarith
  have hgen' : ∀ u ∈ R, ∃ t : ℝ, 0 ≤ t ∧ t • ξ = u := fun u hu => by rwa [hRC] at hu
  refine ⟨e', he'e, by exact_mod_cast (he'e ▸ he_lt : (e' : ℝ) < 1), R,
    ⟨hq A, hRext, fun u hu hu0 => ?_⟩, hq _, hq G, fun u hu hu0 => ?_⟩
  · obtain ⟨t, ht, rfl⟩ := hgen' u hu
    have ht0 : 0 < t := lt_of_le_of_ne ht fun h0 => hu0 (by rw [← h0, zero_smul])
    rw [QDivisor.relativeCurveForm_eq_comp]
    change φ (t • ξ) < 0
    rw [map_smul, smul_eq_mul]
    have : φ ξ < 0 := by nlinarith
    exact mul_neg_of_pos_of_neg ht0 this
  · obtain ⟨t, ht, rfl⟩ := hgen' u hu
    have ht0 : 0 < t := lt_of_le_of_ne ht fun h0 => hu0 (by rw [← h0, zero_smul])
    rw [QDivisor.relativeCurveForm_eq_comp, QDivisor.relativeCurveForm_eq_comp,
      LinearMap.comp_apply, LinearMap.comp_apply,
      curveForm_add_smul sY (hq A) (hq G) (1 - e') (hq _)]
    change (QDivisor.curveForm sY A (hq A) + _) (relativeToAbsolute sY h (t • ξ)) = 0 ∧
      0 < γ (t • ξ)
    rw [LinearMap.add_apply, LinearMap.smul_apply]
    change φ (t • ξ) + _ • γ (t • ξ) = 0 ∧ 0 < γ (t • ξ)
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    push_cast
    rw [he'e]
    exact ⟨by linear_combination t * hψξ0, mul_pos ht0 hγξ⟩

/-- **The threshold ray.** At a model of the second program with parameter `a` on which `K + D` is
not nef over `Z`, the threshold `e = sup {c | K + D + (1 - c) G nef over Z} ≥ a` is rational,
`< 1`, attained, and there is a `(K + D)`-negative extremal ray contracted over `Z` on which
`K + D + (1 - e) G` is trivial and `G` positive. -/
private theorem exists_thresholdRay {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))
    [IsLocallyNoetherian Z] [IsNormal Z] (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hZn : IsNormalVariety ℂ sZ) {H' : Divisor Z} (hH'c : H'.IsCartier)
    (hH'r : ∀ Q, H'.coeff Q = 0 ∨ H'.coeff Q = 1) {KZ : Divisor Z} {BZ : QDivisor Z}
    (hBZ : ∀ Q, 0 ≤ BZ.coeff Q ∧ BZ.coeff Q < 1) (hBH : ∀ Q, H'.coeff Q ≠ 0 → BZ.coeff Q = 0)
    {n : ℕ} (s : Stage Z) (hs : s.IsAdmissible sZ n H' KZ BZ) {a : ℚ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hdlt : ∀ c : ℚ, a < c → c ≤ 1 → MMP.Intersection.IsDltPair s.sY (s.D + (1 - c) • s.G))
    (hnefa : (Divisor.toQDivisor s.K + (s.D + (1 - a) • s.G)).IsRelativelyNef s.sY s.h)
    (hnef : ¬ (Divisor.toQDivisor s.K + s.D).IsRelativelyNef s.sY s.h) :
    ∃ e : ℚ, a ≤ e ∧ e < 1 ∧
      (Divisor.toQDivisor s.K + (s.D + (1 - e) • s.G)).IsRelativelyNef s.sY s.h ∧
      ∃ R : Set (NumericalCurveClasses s.sY),
        IsNegativeExtremalRayOf s.sY (Divisor.toQDivisor s.K + s.D) R ∧
        (∀ C : ProperCurve s.sY, OneCycle.numericalClass s.sY (C.cycle ℝ) ∈ R →
          C.IsContractedBy s.h) ∧
        ∃ (hLe : (Divisor.toQDivisor s.K + (s.D + (1 - e) • s.G)).IsQCartier)
          (hGq : s.G.IsQCartier), ∀ u ∈ R, u ≠ 0 →
            QDivisor.curveForm s.sY _ hLe u = 0 ∧ 0 < QDivisor.curveForm s.sY s.G hGq u := by
  classical
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  have hY := hs.isProjectiveVariety
  haveI := hY
  haveI := hZ
  haveI : QuasiCompact s.sY := inferInstance
  have hQ := hs.isQFactorial
  have hQc := isQCartier_of_isQFactorial s.sY hQ
  set G₁ : QDivisor s.Y := (1 - a) • s.G with hG₁
  have ha1' : (0 : ℚ) < 1 - a := by linarith
  set S : Set ℝ := {c : ℝ | c ∈ Set.Icc 0 1 ∧ MMP.Flips.IsRelativelyNef ℂ s.sY s.h
      (QDivisor.toRDivisor (Divisor.toQDivisor s.K + s.D) + (1 - c) • QDivisor.toRDivisor G₁)}
    with hS
  -- the boundary-removal lemma, for `D` and `G₁ = (1 - a) G`
  obtain ⟨e', he', he'1, Rrel, hRrel, he, hG₁q, hRrele⟩ : ∃ e' : ℚ, (e' : ℝ) = sSup S ∧
      e' < 1 ∧ ∃ R : Set (RelativeNumericalCurveClasses s.sY s.h),
        IsNegativeRelativeExtremalRayOf s.sY s.h (Divisor.toQDivisor s.K + s.D) R ∧
        ∃ (he : (Divisor.toQDivisor s.K + s.D + (1 - e') • G₁).IsQCartier)
          (hGq : G₁.IsQCartier), ∀ u ∈ R, u ≠ 0 →
            QDivisor.relativeCurveForm s.sY s.h (Divisor.toQDivisor s.K + s.D + (1 - e') • G₁)
              he u = 0 ∧ 0 < QDivisor.relativeCurveForm s.sY s.h G₁ hGq u := by
    haveI : IsDominant s.h := hs.isBirationalMorphism.isDominant
    have hHf := MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant s.h H'
    have hHe : DivisorWithCoeffs.IsEffective H' := fun E => by
      rcases hH'r E with h | h <;> simp [h]
    refine exists_isNegativeRelativeExtremalRayOf_of_forall_isDltPair
      hQ hZn hs.comp_eq hs.isProjectiveMorphism hs.isBirationalMorphism
      hs.isCanonicalDivisor ?_ ?_ ?_ hH'c hHe hHf ?_
    · -- the boundaries `D + (1 - c) G₁`, `0 < c < 1`, are dlt
      intro c hc0 hc1
      have heq : s.D + (1 - c) • G₁ = s.D + (1 - (1 - (1 - c) * (1 - a))) • s.G := by
        rw [hG₁, smul_smul]; congr 2; ring
      rw [heq]
      exact hdlt _ (by nlinarith [ha1', hc0, hc1]) (by nlinarith [ha1', hc0, hc1])
    · have := MMP.Fourfold.Oai4C1.Negativity.isRelativelyNef_toRDivisor hnefa
      rw [hG₁, add_assoc]
      exact this
    · exact fun h => hnef (isRelativelyNef_of_isRelativelyNef_toRDivisor s.sY (hQc _) h)
    · intro c hc0 hc1
      have heq : s.D + (1 - c) • G₁ = s.D + ((1 - c) * (1 - a)) • s.G := by
        rw [hG₁, smul_smul]
      rw [heq]
      exact supp_roundDown_le_supp_pullback hZn hH'c hH'r hBZ hBH hs hHf
        (mul_pos (by linarith) ha1') (by nlinarith [ha0, hc0, hc1, ha1])
  -- `0 ≤ e'`, as `K + D + G₁` is nef over `Z`
  have h0S : (0 : ℝ) ∈ S := by
    refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
    have := MMP.Fourfold.Oai4C1.Negativity.isRelativelyNef_toRDivisor hnefa
    convert this using 1
    rw [sub_zero, one_smul, ← map_add, hG₁, add_assoc]
  have hSbdd : BddAbove S := ⟨1, fun c hc => hc.1.2⟩
  have he'0 : (0 : ℚ) ≤ e' := by
    have := le_csSup hSbdd h0S
    rw [← he'] at this
    exact_mod_cast this
  set e : ℚ := 1 - (1 - e') * (1 - a) with he_def
  have hee : (1 - e) = (1 - e') * (1 - a) := by rw [he_def]; ring
  have hLeq : Divisor.toQDivisor s.K + s.D + (1 - e') • G₁ =
      Divisor.toQDivisor s.K + (s.D + (1 - e) • s.G) := by
    rw [hG₁, smul_smul, ← hee, add_assoc]
  -- nefness at the threshold: the nef parameters accumulate at `e'`
  have hnefe : (Divisor.toQDivisor s.K + (s.D + (1 - e) • s.G)).IsRelativelyNef s.sY s.h := by
    rw [← hLeq]
    refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg s.sY (hQc _)
      fun C hC => ?_
    set xA := (Divisor.toQDivisor s.K + s.D).intersectionNumber ℂ s.sY C.ι C.dim_le (hQc _)
    set xB := G₁.intersectionNumber ℂ s.sY C.ι C.dim_le (hQc _)
    have hx : (Divisor.toQDivisor s.K + s.D + (1 - e') • G₁).intersectionNumber ℂ s.sY C.ι
        C.dim_le (hQc _) = xA + (1 - e') * xB := by
      rw [QDivisor.intersectionNumber_add' ℂ s.sY C.ι C.dim_le _ _ (hQc _) (hQc _) (hQc _),
        MMP.Fourfold.intersectionNumber_smul s.sY C.ι C.dim_le _ (hQc _) _ (hQc _)]
    rw [hx]
    have hmem : ∀ c ∈ S, (0 : ℝ) ≤ (xA : ℝ) + (1 - c) * (xB : ℝ) := fun c hc =>
      le_of_isRelativelyNef_toRDivisor_add_smul s.sY (hQc _) (hQc _) hc.2 C hC
    by_contra hneg
    push Not at hneg
    have hneg' : (xA : ℝ) + (1 - e') * (xB : ℝ) < 0 := by exact_mod_cast hneg
    obtain ⟨ε, hε, h5⟩ : ∃ ε : ℝ, 0 < ε ∧
        ε * (|(xB : ℝ)| + 1) = -((xA : ℝ) + (1 - e') * (xB : ℝ)) :=
      ⟨_, div_pos (by linarith) (by positivity), div_mul_cancel₀ _ (by positivity)⟩
    obtain ⟨c, hcS, hc⟩ := exists_lt_of_lt_csSup ⟨0, h0S⟩
      (show (e' : ℝ) - ε < sSup S by rw [← he']; linarith)
    have hce : c ≤ (e' : ℝ) := by rw [he']; exact le_csSup hSbdd hcS
    have h1 := hmem c hcS
    have h2 : (xA : ℝ) + (1 - c) * (xB : ℝ) =
        ((xA : ℝ) + (1 - e') * (xB : ℝ)) + ((e' : ℝ) - c) * xB := by ring
    have h3 : ((e' : ℝ) - c) * xB ≤ ((e' : ℝ) - c) * |(xB : ℝ)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
    have h4 : ((e' : ℝ) - c) * |(xB : ℝ)| < ε * (|(xB : ℝ)| + 1) := by
      have : ((e' : ℝ) - c) < ε := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr this.le) (abs_nonneg (xB : ℝ)), hε]
    linarith
  obtain ⟨hKDq, hext, hneg⟩ := hRrel
  refine ⟨e, by nlinarith [he'0, ha1'], by nlinarith [he'1, ha1'], hnefe,
    relativeToAbsolute s.sY s.h '' Rrel,
    ⟨hQc _, isExtremalRay_image_relativeToAbsolute s.sY sZ s.h hs.comp_eq hext, ?_⟩, ?_,
    hQc _, hQc _, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩ hw0
    have hw0' : w ≠ 0 := by rintro rfl; exact hw0 (map_zero _)
    have := hneg w hw hw0'
    rwa [MMP.Mori.QDivisor.relativeCurveForm_eq_comp, LinearMap.comp_apply] at this
  · rintro C ⟨w, -, hw⟩
    exact isContractedBy_of_numericalClass_mem_range sZ s.h hs.comp_eq C ⟨w, hw⟩
  · rintro _ ⟨w, hw, rfl⟩ hw0
    have hw0' : w ≠ 0 := by rintro rfl; exact hw0 (map_zero _)
    obtain ⟨h1, h2⟩ := hRrele w hw hw0'
    rw [MMP.Mori.QDivisor.relativeCurveForm_eq_comp, LinearMap.comp_apply] at h1 h2
    refine ⟨by rwa [curveForm_congr s.sY hLeq.symm _ he], ?_⟩
    rw [curveForm_congr s.sY hG₁ _ (hQc _),
      MMP.Fourfold.QDivisor.curveForm_smul s.sY (1 - a) s.G (hQc _) (hQc _),
      LinearMap.smul_apply, smul_eq_mul] at h2
    have ha' : (0 : ℝ) < ((1 - a : ℚ) : ℝ) := by exact_mod_cast ha1'
    exact pos_of_mul_pos_right h2 ha'.le

/-- **One step of the second program.** At a stage of the second program with `K + D` not nef
over `Z`, the attained threshold `e ≥ a` and its ray `R` (`(K + D + (1 - e) G) · R = 0`,
`G · R > 0`) are given by the boundary-removal lemma; `R` is `(K + D)`-negative and some
exceptional component of `⌊D⌋` is negative on it, so its contraction is divisorial (lowering `ρ`)
or a floor flipping contraction for `(Y, D)`, whose flip exists by `P(n)`. The new model is a
stage with parameter `e`. -/
private theorem exists_secondStep
    {n : ℕ} (hP : ProjectiveFloorProgramInputs n)
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) [IsLocallyNoetherian Z] [IsNormal Z]
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    {H' : Divisor Z} (hH'c : H'.IsCartier) (hH'r : ∀ Q, H'.coeff Q = 0 ∨ H'.coeff Q = 1)
    {KZ : Divisor Z} {BZ : QDivisor Z} (hBZ : ∀ Q, 0 ≤ BZ.coeff Q ∧ BZ.coeff Q < 1)
    (hBH : ∀ Q, H'.coeff Q ≠ 0 → BZ.coeff Q = 0)
    (s : Stage Z) (hs : IsSecondProgramStage sZ n H' KZ BZ s)
    (hnef : ¬ (Divisor.toQDivisor s.K + s.D).IsRelativelyNef s.sY s.h) :
    ∃ t : Stage Z, IsSecondProgramStage sZ n H' KZ BZ t ∧
      (picardNumber t.sY < picardNumber s.sY ∨ (picardNumber t.sY = picardNumber s.sY ∧
        IsFloorStep (fun s => s.D) s t)) := by
  obtain ⟨hs, a, ha0, ha1, hdlt, hnefa⟩ := hs
  obtain ⟨e, hae, he1, hnefe, R, hR, hRπ, hLe, hGq, hRe⟩ :=
    exists_thresholdRay sZ hZ hZn hH'c hH'r hBZ hBH s hs ha0 ha1 hdlt hnefa hnef
  exact exists_secondStep_of_ray hP sZ hZ hZn hH'c hH'r s hs (ha0.trans hae) he1
    (fun c hc hc1 => hdlt c (hae.trans_lt hc) hc1) hnefe hR hRπ hLe hGq hRe

/-- **The second program.** Under `P(n)`, starting from an admissible model with `(Y, D + G)`
dlt and `K + D + G` nef over `Z`, the `(K + D)`-program over `Z` with nef thresholds
`K + D + (1 - e) G` terminates with `(Y, D)` dlt and `K + D` nef over `Z`. -/
private theorem exists_secondProgram
    {n : ℕ} (hP : ProjectiveFloorProgramInputs n)
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) [IsLocallyNoetherian Z] [IsNormal Z]
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    {H' : Divisor Z} (hH'c : H'.IsCartier) (hH'r : ∀ Q, H'.coeff Q = 0 ∨ H'.coeff Q = 1)
    {KZ : Divisor Z} {BZ : QDivisor Z} (hBZ : ∀ Q, 0 ≤ BZ.coeff Q ∧ BZ.coeff Q < 1)
    (hBH : ∀ Q, H'.coeff Q ≠ 0 → BZ.coeff Q = 0)
    (s₁ : Stage Z) (hs₁ : s₁.IsAdmissible sZ n H' KZ BZ)
    (hdlt₁ : MMP.Intersection.IsDltPair s₁.sY (s₁.D + s₁.G))
    (hnef₁ : (Divisor.toQDivisor s₁.K + (s₁.D + s₁.G)).IsRelativelyNef s₁.sY s₁.h) :
    ∃ s : Stage Z, s.IsAdmissible sZ n H' KZ BZ ∧ MMP.Intersection.IsDltPair s.sY s.D ∧
      (Divisor.toQDivisor s.K + s.D).IsRelativelyNef s.sY s.h := by
  have hdltc : ∀ (s : Stage Z), IsSecondProgramStage sZ n H' KZ BZ s →
      MMP.Intersection.IsDltPair s.sY s.D := by
    rintro s ⟨-, a, -, ha1, hdlt, -⟩
    simpa using hdlt 1 ha1 le_rfl
  have h₁ : IsSecondProgramStage sZ n H' KZ BZ s₁ := by
    refine ⟨hs₁, 0, le_rfl, one_pos, fun c hc hc1 => ?_, by simpa using hnef₁⟩
    have hQ := isQCartier_of_isQFactorial s₁.sY hs₁.isQFactorial
    obtain ⟨h0, hle⟩ := hs₁.nonneg_and_le_add_smul (fun Q => (hBZ Q).1) hH'r
      (t := 1 - c) (by linarith) (by linarith)
    exact MMP.Intersection.IsDltPair.of_le s₁.sY hdlt₁ h0 hle (hQ _)
  obtain ⟨s, hs, hnef⟩ := exists_stop_of_step
    (good := IsSecondProgramStage sZ n H' KZ BZ)
    (stop := fun s : Stage Z => (Divisor.toQDivisor s.K + s.D).IsRelativelyNef s.sY s.h)
    (fun s => picardNumber s.sY) (Flip := IsFloorStep fun s => s.D)
    (fun s hs hnef => exists_secondStep hP sZ hZ hZn hH'c hH'r hBZ hBH s hs hnef)
    (fun u hu => not_forall_isFloorStep hP _ u
      ⟨(hu 0).1.isProjectiveVariety, (hu 0).1.dim_eq, (hu 0).1.isQFactorial,
        (hu 0).1.isCanonicalDivisor, hdltc _ (hu 0)⟩) s₁ h₁
  exact ⟨s, hs.1, hdltc s hs, hnef⟩

/-! ### No extracted divisors -/

/-- A prime divisor which a proper birational morphism `h` onto a normal variety does not map onto
a prime divisor lies over a point of coheight at least two. -/
private theorem two_le_coheight_of_transformPrimeDivisor_eq_none {Y Z : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Z]
    {sZ : Z ⟶ Spec (.of ℂ)} (hZn : IsNormalVariety ℂ sZ) {h : Y ⟶ Z} [IsProper h]
    (hYv : MMP.Mori.IsVariety ℂ (h ≫ sZ)) (hhb : IsBirationalMorphism h)
    {P : MMP.Mori.PrimeDivisor Y}
    (hP : RationalMap.transformPrimeDivisor h.toRationalMap P = none) :
    2 ≤ Order.coheight (h P.genericPoint) := by
  haveI := isSeparated_toTerminal_of_isNormalVariety hZn
  haveI : IsDominant h := hhb.isDominant
  haveI : IsNormal Z := hZn.2
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  by_contra hlt
  have hle : Order.coheight (h P.genericPoint) ≤ 1 := by
    by_contra h1
    exact hlt (Order.add_one_le_of_lt (not_le.mp h1))
  have hmem := MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hZn h hYv hhb
    (by rw [ringKrullDim_stalk_eq_coheight]; exact_mod_cast hle)
  have hco : Order.coheight (h P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus h hmem, P.coheight_genericPoint]
  have := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff h P
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco)).mpr
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm
  rw [hP] at this
  cases this

/-- A proper birational morphism onto a normal variety which maps every prime divisor onto a prime
divisor has exceptional set of codimension at least two. -/
private theorem two_le_closedsCodimension_exceptionalSet_of_forall_ne_none {Y Z : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Z]
    {sZ : Z ⟶ Spec (.of ℂ)} (hZn : IsNormalVariety ℂ sZ) {h : Y ⟶ Z} [IsProper h]
    (hYv : MMP.Mori.IsVariety ℂ (h ≫ sZ)) (hhb : IsBirationalMorphism h)
    (hne : ∀ P : MMP.Mori.PrimeDivisor Y,
      RationalMap.transformPrimeDivisor h.toRationalMap P ≠ none) :
    2 ≤ closedsCodimension (exceptionalSet h) := by
  haveI := isSeparated_toTerminal_of_isNormalVariety hZn
  haveI : IsDominant h := hhb.isDominant
  haveI : IsNormal Z := hZn.2
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
  intro y hy
  have hyb : h y ∉ MMP.Mori.biregularLocus h := MMP.Mori.mem_exceptionalSet.mp hy
  by_contra hlt
  push Not at hlt
  rcases lt_or_eq_of_le (Order.le_of_lt_succ (show Order.coheight y < Order.succ 1 from hlt))
    with h0 | h1
  · have hmax : IsMax y := Order.coheight_eq_zero.mp (Order.lt_one_iff.mp h0)
    have hgy : y = genericPoint Y :=
      (Specializes.antisymm (hmax (genericPoint_specializes y)) (genericPoint_specializes y)).eq
    apply hyb
    rw [hgy, MMP.Positivity.map_genericPoint_eq_of_isDominant]
    refine MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hZn h hYv hhb ?_
    rw [ringKrullDim_stalk_eq_coheight,
      Order.coheight_eq_zero.mpr (fun z _ => genericPoint_specializes z)]
    norm_num
  · set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y h1
    have hPy : P.genericPoint = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    obtain ⟨Q, hQ⟩ := Option.ne_none_iff_exists'.mp (hne P)
    have hPQ := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff h P Q).mp hQ
    apply hyb
    rw [← hPy, hPQ]
    refine MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hZn h hYv hhb ?_
    rw [ringKrullDim_stalk_eq_coheight, Q.coheight_genericPoint]
    norm_num

/-- **No extracted divisors** (KM 3.38). Let `f : X ⟶ Z` be a proper birational morphism with
exceptional set of codimension at least two, `(X, B)` klt with `-(K_X + B)` nef over `Z`, and
`h : Y ⟶ Z` a proper birational morphism with `K_Y + D` nef over `Z` and `f_* B = h_* D`, the
canonical divisors being of the same dimension. Then every prime divisor `P` of `Y` with
coefficient one in `D` maps onto a prime divisor of `Z`: otherwise `a(P, Y, D) = -1` would bound
`a(P, X, B) > -1` from above. -/
private theorem transformPrimeDivisor_ne_none_of_isRelativelyNef {X Y Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Z]
    {sZ : Z ⟶ Spec (.of ℂ)} (hZn : IsNormalVariety ℂ sZ) {f : X ⟶ Z} {h : Y ⟶ Z}
    [IsProper f] [IsProper h] {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] [QuasiCompact sY] (hsX : f ≫ sZ = sX) (hsY : h ≫ sZ = sY)
    (hXn : IsNormalVariety ℂ sX) (hYn : IsNormalVariety ℂ sY) (hfb : IsBirationalMorphism f)
    (hhb : IsBirationalMorphism h) (hf2 : 2 ≤ closedsCodimension (exceptionalSet f))
    {m : ℕ} {K : Divisor X} {B : QDivisor X} (hK : K.IsCanonicalDivisor sX m)
    (hklt : MMP.Mori.IsKltPair sX m K B)
    (hN : (-(Divisor.toQDivisor K + B)).IsRelativelyNef sX f)
    {KY : Divisor Y} {D : QDivisor Y} (hKY : KY.IsCanonicalDivisor sY m)
    (hDq : (Divisor.toQDivisor KY + D).IsQCartier)
    (hN' : (Divisor.toQDivisor KY + D).IsRelativelyNef sY h)
    (hΔ : RationalMap.transformDivisor (X := X) f.toRationalMap B =
      RationalMap.transformDivisor (X := Y) h.toRationalMap D)
    {P : MMP.Mori.PrimeDivisor Y} (hP : D.coeff P = 1) :
    RationalMap.transformPrimeDivisor h.toRationalMap P ≠ none := by
  subst hsX hsY
  intro hnone
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  haveI : IsSeparated sZ := hZn.1.toIsSeparated
  haveI : IsDominant f := hfb.isDominant
  haveI : IsDominant h := hhb.isDominant
  haveI : IsNormal Z := hZn.2
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  set D' := MMP.Mori.DivisorOver.ofPrimeDivisor ℂ hYn P
  obtain ⟨D₀, hv⟩ := MMP.Mori.exists_divisorOver_valuation_comap_eq hXn hfb hhb D'
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy
    (show MMP.Mori.IsPair (h ≫ sZ) D from ⟨hYn, m, KY, hKY, hDq⟩) hKY D'
  have ha'1 : a' = -1 := by
    rw [MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hYn ha', hP]
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hklt.1.isPair hK D₀
  have hcen : f (D₀.f D₀.E.genericPoint) = h P.genericPoint :=
    MMP.Mori.map_genericPoint_eq_of_valuation_comap_eq sZ f h D₀ D' hv
  have h2 := two_le_coheight_of_transformPrimeDivisor_eq_none hZn hYn.1 hhb hnone
  -- `D₀` is exceptional over `Z`
  haveI : IsIntegral D₀.Y := D₀.isIntegral
  let D₀Z : MMP.Mori.DivisorOver ℂ sZ :=
    ⟨D₀.Y, D₀.f ≫ f, by rw [Category.assoc]; exact D₀.isNormalVariety,
      MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp D₀.isBirationalMorphism hfb, D₀.E⟩
  have hEZ : RationalMap.IsExceptional (X := D₀.Y) (D₀.f ≫ f).toRationalMap D₀.E :=
    (MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight
      hZn D₀Z).mpr (by
        change 2 ≤ Order.coheight ((D₀.f ≫ f) D₀.E.genericPoint)
        rw [Scheme.Hom.comp_apply, hcen]
        exact h2)
  -- `D₀` is exceptional over `X`, as `f` is small
  have hEX : D₀.IsExceptional := by
    rw [MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight
      hXn D₀]
    by_contra hlt
    have hle : Order.coheight (D₀.f D₀.E.genericPoint) ≤ 1 := by
      by_contra h1
      exact hlt (Order.add_one_le_of_lt (not_le.mp h1))
    have hfx : f (D₀.f D₀.E.genericPoint) ∈ MMP.Mori.biregularLocus f := by
      by_contra hn
      have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hf2
        (MMP.Mori.mem_exceptionalSet.mpr hn)
      exact absurd (this.trans hle) (by decide)
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus f hfx, hcen] at hle
    exact absurd (h2.trans hle) (by decide)
  have hle := MMP.Mori.isDiscrepancy_le_of_isRelativelyNef hXn hYn hZn rfl rfl hfb hhb hK hKY hΔ
    hN hN' D₀ D' hv hEZ ha ha'
  have hlt : ((-1 : ℝ) : EReal) < ((a : ℝ) : EReal) := by
    simpa using hklt.2.1.trans_le (MMP.Mori.discrep_le hEX ha)
  have : (-1 : ℝ) < a := EReal.coe_lt_coe_iff.mp hlt
  have : (-1 : ℚ) < a := by exact_mod_cast this
  linarith

/-- **No extracted divisors.** An admissible model with `(Y, D)` dlt and `K + D` nef over `Z`
extracts no divisor over `Z`, by comparison of discrepancies with the klt pair `(X, B)`; it is
therefore a small model `V ⟶ Z` with `D = g⁻¹_* f_* B`, `K = g⁻¹_* f_* K`, and `(V, D)` is klt. -/
private theorem exists_smallNefModel_of_stage
    {n : ℕ} {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = n) {B : QDivisor X} (hklt : IsKltPair sX B)
    {m : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX m)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) [IsLocallyNoetherian Z] [IsNormal Z]
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f) (hsmall : IsSmallMorphism sX sZ f)
    {H' : Divisor Z} (s : Stage Z)
    (hs : s.IsAdmissible sZ n H' (RationalMap.transformDivisor f.toRationalMap K)
      (RationalMap.transformDivisor f.toRationalMap B))
    (hdlt : MMP.Intersection.IsDltPair s.sY s.D)
    (hnef : (Divisor.toQDivisor s.K + s.D).IsRelativelyNef s.sY s.h) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : CompactSpace V) (_ : IsLocallyNoetherian V)
      (_ : IsNormal V) (sV : V ⟶ Spec (.of ℂ)) (_ : QuasiCompact sV) (g : V ⟶ Z) (mV : ℕ),
      MMP.Mori.IsProjectiveVariety ℂ sV ∧ g ≫ sZ = sV ∧ IsBirationalMorphism g ∧
        2 ≤ closedsCodimension (exceptionalSet g) ∧
        MMP.Mori.IsKltPair sV mV (flipTransform f g K) (flipTransform f g B) ∧
        0 ≤ flipTransform f g B ∧
        (Divisor.toQDivisor (flipTransform f g K) + flipTransform f g B).IsRelativelyNef sV g := by
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  have hXn := hf.isNormalVariety_source
  have hZn := hf.isNormalVariety_target
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI : IsProper f := hsmall.isProper
  have hfb := hsmall.isBirationalMorphism
  haveI := isSeparated_toTerminal_of_isNormalVariety hZn
  haveI : IsProper s.h := isProper_of_isProjectiveMorphism _ hs.isProjectiveMorphism
  have hhb := hs.isBirationalMorphism
  have hYp := hs.isProjectiveVariety
  haveI := hYp
  haveI : QuasiCompact s.sY := inferInstance
  haveI : QuasiCompact sX := inferInstance
  have hYv : MMP.Mori.IsVariety ℂ (s.h ≫ sZ) := by rw [hs.comp_eq]; exact hYp.toIsVariety
  have hYn : IsNormalVariety ℂ s.sY := ⟨hYp.toIsVariety, inferInstance⟩
  obtain ⟨m', hK'⟩ := hs.isCanonicalDivisor
  have hmm : m' = m := by
    have e : ((m' : ℕ) : WithBot ℕ∞) = ((m : ℕ) : WithBot ℕ∞) := by
      rw [← hK'.topologicalKrullDim_eq, hs.dim_eq, ← hdim, hK.topologicalKrullDim_eq]
    exact_mod_cast e
  subst hmm
  have hkltM : MMP.Mori.IsKltPair sX m' K B :=
    (MMP.Fourfold.isKltPair_iff_mori_isKltPair sX hK hklt.1).mp hklt
  have hN : (-(Divisor.toQDivisor K + B)).IsRelativelyNef sX f :=
    MMP.Mori.isRelativelyNef_of_hasRelativelyAmpleMultiple
      (hasRelativelyAmpleMultiple_neg sX hX hklt hK hR sZ hf)
  have hΔ : RationalMap.transformDivisor (X := X) f.toRationalMap B =
      RationalMap.transformDivisor (X := s.Y) s.h.toRationalMap s.D := by
    refine Finsupp.ext fun Q => ?_
    obtain ⟨P, hPQ⟩ := exists_primeDivisor_map_genericPoint_eq hZn hhb Q
    rw [MMP.Fourfold.Oai4C1.transformDivisor_apply_of_map_genericPoint hhb hPQ]
    change _ = s.D.coeff P
    rw [hs.coeff_D,
      (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff s.h P Q).mpr hPQ]
    rfl
  -- no prime divisor of `Y` is extracted
  have hne : ∀ P : MMP.Mori.PrimeDivisor s.Y,
      RationalMap.transformPrimeDivisor s.h.toRationalMap P ≠ none := by
    intro P hP
    have hP1 : s.D.coeff P = 1 := by rw [hs.coeff_D, hP]; rfl
    exact transformPrimeDivisor_ne_none_of_isRelativelyNef hZn hf.comp_eq hs.comp_eq hXn hYn hfb
      hhb hsmall.two_le_codimension hK hkltM hN hK' hnef.1 hnef hΔ hP1 hP
  have h2 := two_le_closedsCodimension_exceptionalSet_of_forall_ne_none hZn hYv hhb hne
  have hsm : IsSmallMorphism s.sY sZ s.h := ⟨hYn, hZn, hs.comp_eq, inferInstance, hhb, h2⟩
  -- the strict transforms of `K` and `B` are `K_Y` and `D`
  have hcorr : ∀ P' : MMP.Mori.PrimeDivisor s.Y, ∃ (Pm : MMP.Mori.PrimeDivisor X)
      (Q : MMP.Mori.PrimeDivisor Z), f Pm.genericPoint = Q.genericPoint ∧
        s.h P'.genericPoint = Q.genericPoint ∧
        ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
          flipTransform f s.h D P' = D Pm := by
    intro P'
    obtain ⟨Q, hQ⟩ := Option.ne_none_iff_exists'.mp (hne P')
    have hPQ := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff s.h P' Q).mp hQ
    obtain ⟨x, hx⟩ := hf.toIsContraction.surjective (s.h P'.genericPoint)
    obtain ⟨Pm, rfl, hD⟩ := exists_eq_genericPoint_flipTransform_apply hfb hsm P' x hx
    exact ⟨Pm, Q, hx.trans hPQ, hPQ, fun D => hD D⟩
  have hKV : flipTransform f s.h K = s.K := by
    refine Finsupp.ext fun P' => ?_
    obtain ⟨Pm, Q, hPmQ, hP'Q, hD⟩ := hcorr P'
    rw [hD]
    have e1 := MMP.Fourfold.Oai4C1.transformDivisor_apply_of_map_genericPoint hfb hPmQ K
    have e2 := MMP.Fourfold.Oai4C1.transformDivisor_apply_of_map_genericPoint hhb hP'Q s.K
    rw [hs.transformDivisor_K] at e2
    rw [← e1, e2]
  have hBV : flipTransform f s.h B = s.D := by
    refine Finsupp.ext fun P' => ?_
    obtain ⟨Pm, Q, hPmQ, hP'Q, hD⟩ := hcorr P'
    rw [hD]
    change B Pm = s.D.coeff P'
    rw [hs.coeff_D,
      (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff s.h P' Q).mpr hP'Q]
    change B Pm = RationalMap.transformDivisor (X := X) f.toRationalMap B Q
    rw [MMP.Fourfold.Oai4C1.transformDivisor_apply_of_map_genericPoint hfb hPmQ B]
  have hD01 : ∀ P : MMP.Mori.PrimeDivisor s.Y, 0 ≤ s.D.coeff P ∧ s.D.coeff P < 1 := by
    intro P
    obtain ⟨Pm, -, -, -, hD⟩ := hcorr P
    rw [← hBV]
    change 0 ≤ flipTransform f s.h B P ∧ flipTransform f s.h B P < 1
    rw [hD]
    exact coeff_mem_Ico_of_isKltPair hklt Pm
  have hkltY := MMP.Intersection.IsDltPair.isKltPair_of_forall_coeff_lt_one hdlt fun P => (hD01 P).2
  refine ⟨s.Y, inferInstance, inferInstance, inferInstance, inferInstance, s.sY, inferInstance, s.h,
    m', hYp, hs.comp_eq, hhb, h2, ?_, ?_, ?_⟩
  · rw [hKV, hBV]
    exact (MMP.Fourfold.isKltPair_iff_mori_isKltPair s.sY hK' hkltY.1).mp hkltY
  · rw [hBV]
    exact fun P => (hD01 P).1
  · rw [hKV, hBV]
    exact hnef

/-- **The two programs.** Under `P(n)`, a small contraction `f : X ⟶ Z` of a `(K + B)`-negative
extremal ray of a `ℚ`-factorial projective klt `n`-fold has a small projective model
`g : V ⟶ Z` on which `(V, B_V)`, with `B_V = g⁻¹_* f_* B` and `K_V = g⁻¹_* f_* K`, is klt and
`K_V + B_V` is nef over `Z`. -/
private theorem exists_smallNefModel
    {n : ℕ} (hP : ProjectiveFloorProgramInputs n)
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    (hdim : topologicalKrullDim X = n) {B : QDivisor X} (hklt : IsKltPair sX B)
    {m : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX m)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) [IsLocallyNoetherian Z] [IsNormal Z]
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f)
    (hsmall : IsSmallMorphism sX sZ f) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : CompactSpace V) (_ : IsLocallyNoetherian V)
      (_ : IsNormal V) (sV : V ⟶ Spec (.of ℂ)) (_ : QuasiCompact sV) (g : V ⟶ Z) (mV : ℕ),
      MMP.Mori.IsProjectiveVariety ℂ sV ∧ g ≫ sZ = sV ∧ IsBirationalMorphism g ∧
        2 ≤ closedsCodimension (exceptionalSet g) ∧
        MMP.Mori.IsKltPair sV mV (flipTransform f g K) (flipTransform f g B) ∧
        0 ≤ flipTransform f g B ∧
        (Divisor.toQDivisor (flipTransform f g K) + flipTransform f g B).IsRelativelyNef sV g := by
  haveI := hf.isNormalVariety_target.1
  have hZn : IsNormalVariety ℂ sZ := hf.isNormalVariety_target
  obtain ⟨P⟩ := nonempty_procedureDatum sX hklt sZ hZ hf hsmall
  obtain ⟨hBZ, hBH⟩ := coeff_transformDivisor_of_procedureDatum sX hklt sZ hf hsmall P
  obtain ⟨s₀, hs₀, hdlt₀⟩ := exists_initialStage sX hX hQ hdim hklt hK hR sZ hZ hf hsmall P hBZ hBH
  obtain ⟨s₁, hs₁, hdlt₁, hnef₁⟩ := exists_firstProgram hP sZ hZ hZn P hBH s₀ hs₀ hdlt₀
  obtain ⟨s₂, hs₂, hdlt₂, hnef₂⟩ := exists_secondProgram hP sZ hZ hZn P.isCartier_H'
    P.isReduced_H' hBZ hBH s₁ hs₁ hdlt₁ hnef₁
  exact exists_smallNefModel_of_stage sX hX hdim hklt hK hR sZ hZ hf hsmall s₂ hs₂ hdlt₂ hnef₂

/-- **The core of the reduction.** Under `P(n)`, the divisorial algebra of `f_*(r(K + B))` is
finitely generated over every affine open of `Z`. -/
private theorem finiteType_divisorialAlgebraSections
    {n : ℕ} (hP : ProjectiveFloorProgramInputs n)
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    (hdim : topologicalKrullDim X = n) {B : QDivisor X} (hklt : IsKltPair sX B)
    {m : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX m)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) [IsLocallyNoetherian Z] [IsNormal Z]
    {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f)
    (hsmall : IsSmallMorphism sX sZ f) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {r : ℕ} (hr : 0 < r) {Dr : Divisor X} (hDr : Divisor.toQDivisor Dr = (r : ℚ) • B)
    (U : Z.Opens) (hU : IsAffineOpen U) :
    Algebra.FiniteType Γ(Z, U)
      (Divisor.divisorialAlgebraSections
        (RationalMap.transformDivisor f.toRationalMap (r • K + Dr)) U) := by
  obtain ⟨V, _, _, _, _, sV, _, g, mV, hV, hgZ, hgb, hgEx, hkltV, hBV, hnefV⟩ :=
    exists_smallNefModel hP sX hX hQ hdim hklt hK hR sZ hZ hf hsmall
  have hT : Divisor.toQDivisor (inverseTransformDivisor g
      (RationalMap.transformDivisor f.toRationalMap (r • K + Dr))) =
      (r : ℚ) • (Divisor.toQDivisor (flipTransform f g K) + flipTransform f g B) := by
    change Divisor.toQDivisor (flipTransform f g (r • K + Dr)) = _
    rw [← flipTransform_toQDivisor, ← flipTransform_toQDivisor, map_add, map_add, hDr,
      Nat.cast_smul_eq_nsmul, map_nsmul, map_nsmul, map_nsmul, smul_add]
    simp only [Nat.cast_smul_eq_nsmul]
  haveI : IsIntegral Z := hf.isNormalVariety_target.1.toIsIntegral
  obtain ⟨d, hd, hdc, hfree⟩ := exists_isRelativelyFreeDivisor_nsmul sV sZ hV hZ g hgZ hgb hkltV
    hBV hnefV hr hT
  exact finiteType_of_isRelativelyFreeDivisor sV sZ hV hZ g hgZ hgb hgEx _ hd hdc hfree U hU

end MMP.FourfoldProofs.FourfoldProjectiveKltFlipFromFloorInputsProof

end

section

/-!
# Klt flips from the projective floor-program inputs

Assume the projective floor-program inputs `P(n)` (`MMP.Fourfold.ProjectiveFloorProgramInputs n`),
which include `n ≥ 3`. Let `(X, B)` be a klt pair, with `B` an effective `ℚ`-divisor, on a
`ℚ`-factorial projective complex variety `X` of dimension `n`, and let `K` be a canonical divisor
of `X`. If `f : X ⟶ Z` is the contraction of a `(K + B)`-negative extremal ray `R` of `NE̅(X)` and
`f` is small, then the `(K + B)`-flip `f⁺ : X⁺ ⟶ Z` of `f` exists.

The proof runs two programs globally over the projective base `Z`, starting from a log resolution
of `X`. The first is a `(K + Θ)`-program for a dlt boundary `Θ = D + G`. The second removes `G`
by raising a nef threshold. Each small step of both programs has a negative reduced component, so
the existence clause of `P(n)` supplies it, and the termination clause of `P(n)` makes both
programs finite. The output is a small `ℚ`-factorial klt model over `Z`, with `K + D` nef over
`Z`. By relative basepoint freeness the adjoint section algebra of `X` over `Z` is then finitely
generated, and this gives the flip.

## Main results

* `MMP.Fourfold.exists_isFlip_of_projectiveFloorProgramInputs_of_isContractionOfRay`: the
  statement above.

## Implementation notes

* The klt condition is `MMP.Fourfold.IsKltPair`. Its underlying pair `MMP.Fourfold.IsPair`
  records that `B` is effective. "Rational" means that `B` is a `ℚ`-divisor.
* The contraction is `MMP.Fourfold.IsContractionOfRay`, and smallness is
  `MMP.Fourfold.IsSmallMorphism`. The flip is `MMP.Mori.IsFlip`. The boundary and the canonical
  divisor on `X⁺` are the strict transforms `(f⁺)⁻¹_* f_* B` and `(f⁺)⁻¹_* f_* K`.
* The bound `n ≥ 3` is not a separate hypothesis, because it is the first clause of
  `MMP.Fourfold.ProjectiveFloorProgramInputs n`.

## References

* [OpenAI, *Termination for projective log canonical fourfolds with rational boundary*][OAI4]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.FourfoldProofs.FourfoldProjectiveKltFlipFromFloorInputsProof in
/-- **Klt flips from the projective floor-program inputs.** Assume `P(n)`
(`MMP.Fourfold.ProjectiveFloorProgramInputs n`, so in particular `n ≥ 3`). Let `(X, B)` be a klt
pair on a `ℚ`-factorial projective complex `n`-fold, with `B ≥ 0` a `ℚ`-divisor and `K` a
canonical divisor. Let `f : X ⟶ Z` be the contraction of a `(K + B)`-negative extremal ray `R`
of `NE̅(X)`, and suppose `f` is small. Then the `(K + B)`-flip of `f` exists: there is a normal
variety `X⁺` with a morphism `f⁺ : X⁺ ⟶ Z` such that `MMP.Mori.IsFlip` holds for `K`, `B`, `f`
and `f⁺`. -/
@[mmp "thm_fourfold_projective_klt_flip_from_floor_inputs"]
public theorem exists_isFlip_of_projectiveFloorProgramInputs_of_isContractionOfRay
    {n : ℕ} (hP : ProjectiveFloorProgramInputs n)
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    (hdim : topologicalKrullDim X = n) {B : QDivisor X} (hklt : IsKltPair sX B)
    {m : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX m)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f)
    (hsmall : IsSmallMorphism sX sZ f) :
    ∃ (Xp : Scheme.{0}) (_ : CompactSpace Xp) (_ : IsLocallyNoetherian Xp) (_ : IsNormal Xp)
      (sXp : Xp ⟶ Spec (.of ℂ)) (fp : Xp ⟶ Z), IsFlip sX sZ sXp K B f fp := by
  haveI := hf.isNormalVariety_target.1
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsNormal Z := hf.isNormalVariety_target.2
  haveI : IsIntegral Z := hf.isNormalVariety_target.1.toIsIntegral
  have hfl : IsFlippingContraction sX sZ K B f :=
    { isNormalVariety_source := hf.isNormalVariety_source
      isNormalVariety_target := hf.isNormalVariety_target
      comp_eq := hf.comp_eq
      isCanonicalDivisor := ⟨m, hK⟩
      isQCartier := hR.1
      isProper := hsmall.isProper
      isBirationalMorphism := hsmall.isBirationalMorphism
      two_le_codimension := hsmall.two_le_codimension
      hasRelativelyAmpleMultiple := hasRelativelyAmpleMultiple_neg sX hX hklt hK hR sZ hf }
  obtain ⟨r, hr, Dr, hDr⟩ := exists_toQDivisor_eq_natCast_smul B
  obtain ⟨Xp, sXp, h₁, h₂, h₃, fp, h⟩ :=
    (exists_isFlip_iff_finiteType_divisorialAlgebraSections sX sZ K B f hfl r hr Dr hDr).2
      (finiteType_divisorialAlgebraSections hP sX hX hQ hdim hklt hK hR sZ hf hsmall
        (isProjectiveVariety_target sX hX hklt hK hR sZ hf) hr hDr)
  exact ⟨Xp, h₁, h₂, h₃, sXp, fp, h⟩

end MMP.Fourfold

end
