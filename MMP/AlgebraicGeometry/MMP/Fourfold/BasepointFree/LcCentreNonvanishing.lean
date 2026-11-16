module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Intersection.Nef
public import MMP.AlgebraicGeometry.Vanishing.MinimalLcCentreFourfold
public import MMP.AlgebraicGeometry.Singularities.LcCentres
public import MMP.AlgebraicGeometry.Vanishing.LcCentreUnionExtension
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
public import MMP.AlgebraicGeometry.MMP.Abundance.NumericalDimensionOnePencil
public import MMP.AlgebraicGeometry.Positivity.AmpleNumerical
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafTensor
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import MMP.AlgebraicGeometry.MMP.Threefold.Basic
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
public import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
public import MMP.AlgebraicGeometry.Positivity.Kleiman.AbsoluteCartier
public import MMP.AlgebraicGeometry.Positivity.CartierTwistEulerPolynomial
public import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Singularities.BoundaryLowering
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Curves.Maps.ScalarAutomorphisms
public import MMP.AlgebraicGeometry.Positivity.AmplePointConcentration
public import MMP.AlgebraicGeometry.Resolution.DivisorTupleRestrictionLift
public import MMP.AlgebraicGeometry.Singularities.LcCentreHighMultiplicity
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
public import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
public import MMP.AlgebraicGeometry.Positivity.RelativeNefBigSurface
public import MMP.AlgebraicGeometry.Singularities.Bertini.GeneralMemberSNC
public import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.GenericFibreDegree
public import MMP.AlgebraicGeometry.ChowForm.FibreKoszulBase
public import MMP.AlgebraicGeometry.Intersection.CurveCartierLocal
public import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
public import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

/-!
# Nonvanishing along lc centres for projective lc fourfolds

Let `(X, B)` be a log canonical pair with rational boundary on a normal projective complex
fourfold, with canonical divisor `K_X`, and let `L` be a nef Cartier divisor such that
`aL - (K_X + B)` is ample for some rational `a > 0`. Then for every sufficiently large integer
`m` the base locus `Bs|mL|` contains no lc centre of `(X, B)`: no centre on `X` of a divisor `E`
over `X` with log discrepancy `a(E, X, B) = 0`.

## Main results

* `MMP.Fourfold.not_center_subset_baseLocusOfMultiple`: for all large `m`, no lc centre of
  `(X, B)` lies in `Bs|mL|`.

## Implementation notes

An *lc centre* of `(X, B)` is the centre `MMP.Mori.DivisorOver.center` of a divisor `E` over `X`
whose log discrepancy (`MMP.Intersection.IsLogDiscrepancy`) is `0`; the statement quantifies over
all such `E`. The base locus of `|mL|` is `MMP.Mori.Divisor.baseLocusOfMultiple L m`, which is all
of `X` when `H⁰(X, mL) = 0`, so the conclusion includes the nonvanishing `H⁰(X, mL) ≠ 0` as soon
as `(X, B)` has an lc centre.

## References

* [OAI4] the fourfold source, *Projective fourfold nonvanishing along every lc centre*.
-/

@[expose] public section

section

namespace Proof_thm_mmp_lc_bpf_fourfold_centre_nonvanishing

open CategoryTheory AlgebraicGeometry Filter TopologicalSpace MonoidalCategory
open MMP.Mori (Divisor QDivisor DivisorOver)
open MMP.Intersection (IsLogCanonicalPair IsLogDiscrepancy)

section KollarMori222

open MMP.Mori

universe v

/-- **Nagata compactification**: a separated morphism of finite type `f : Y ⟶ Z` to a
quasi-compact quasi-separated scheme factors as a quasi-compact open immersion followed by a
proper morphism. -/
private theorem exists_isOpenImmersion_isProper_comp_eq {Y Z : Scheme.{v}} (f : Y ⟶ Z)
    [CompactSpace Z] [QuasiSeparatedSpace Z] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] :
    ∃ (P : Scheme.{v}) (j : Y ⟶ P) (p : P ⟶ Z), IsOpenImmersion j ∧ QuasiCompact j ∧
      IsProper p ∧ j ≫ p = f := by
  obtain ⟨c, hc⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace f
  exact ⟨c.space, c.immersion, c.toBase, inferInstance, hc, inferInstance, Over.w c.obj.hom⟩

/-- The normalization of `P` in a normal integral locally Noetherian scheme `Y`, along a
quasi-compact open immersion `j : Y ⟶ P` with `P` locally of finite type over a field, is normal
and finite over `P`, and `Y` is open in it. -/
private theorem isOpenImmersion_toNormalization_and_isNormal_and_isFinite {k : Type v} [Field k]
    {Y P : Scheme.{v}} {sP : P ⟶ Spec (.of k)} [LocallyOfFiniteType sP] (j : Y ⟶ P)
    [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j] [IsNormal Y] [IsLocallyNoetherian Y] :
    IsOpenImmersion (Scheme.Hom.toNormalization j) ∧
      IsNormal (Scheme.Hom.normalization j) ∧ IsFinite (Scheme.Hom.fromNormalization j) := by
  refine ⟨?_, AlgebraicGeometry.isNormal_normalization j fun V hV => ?_,
    isFinite_fromNormalization_of_locallyOfFiniteType j
    (isNagataScheme_of_locallyOfFiniteType_over_field k sP)⟩
  · have : IsOpenImmersion ((Limits.pullback.snd j j).toNormalization ≫ j.normalizationPullback j ≫
        Limits.pullback.fst _ _) := inferInstance
    rw [Scheme.Hom.toNormalization_normalizationPullback_fst j j] at this
    exact (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion
      (Limits.pullback.fst j j) _).mp this
  · have : IsNoetherian V :=
      { toIsLocallyNoetherian := inferInstance
        toCompactSpace := isCompact_iff_compactSpace.mp hV }
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/-- If `t ≫ g` is birational and `t` is an open immersion of integral schemes, `g` is
birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion_comp {Y P Z : Scheme.{v}} [IsIntegral Y]
    [IsIntegral P] [IsIntegral Z] (t : Y ⟶ P) [IsOpenImmersion t] (g : P ⟶ Z)
    (h : IsBirationalMorphism (t ≫ g)) : IsBirationalMorphism g := by
  obtain ⟨W, hW, hWo⟩ := h.exists_isOpenImmersion
  let U : P.Opens := t ''ᵁ W
  let V : Z.Opens := (W.ι ≫ t ≫ g).opensRange
  have hUV : U ≤ g ⁻¹ᵁ V := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩
  have hU : U.ι ≫ g = (t.isoImage W).inv ≫ W.ι ≫ t ≫ g := by
    rw [← Scheme.Hom.isoImage_inv_ι_assoc]
  have hc : g.resLE V U hUV ≫ V.ι = (t.isoImage W).inv ≫ W.ι ≫ t ≫ g := by
    rw [Scheme.Hom.resLE_comp_ι, hU]
  have : IsOpenImmersion (g.resLE V U hUV ≫ V.ι) := by rw [hc]; infer_instance
  have : IsOpenImmersion (g.resLE V U hUV) := IsOpenImmersion.of_comp _ V.ι
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g U V ?_ ?_ hUV ?_
  · obtain ⟨w, hw⟩ := hW
    exact ⟨t w, w, hw, rfl⟩
  · obtain ⟨w, hw⟩ := hW
    exact ⟨_, ⟨w, hw⟩, rfl⟩
  · rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun ⟨z, hz⟩ => ?_⟩⟩
    obtain ⟨w, rfl⟩ := hz
    refine ⟨(t.isoImage W).hom w, ?_⟩
    apply V.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hc, ← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
    rfl

/-- **Kollár–Mori 2.22 for the identity model.** Every divisor `(Y, f, E)` over a normal variety
`X` (with `f` not necessarily proper) has the valuation of a divisor over `X` whose morphism is
proper: compactify `f` by Nagata's theorem, `Y ⊆ P → X`, and replace `P` by the normalization of
`P` in `Y`, which is finite over `P`, normal, and contains `Y` as an open subscheme. -/
private theorem DivisorOver.exists_isProper_valuation_eq {k : Type v} [Field k] {X : Scheme.{v}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    ∃ E : DivisorOver k sX, IsProper E.f ∧ E.valuation = D.valuation := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have hYv := D.isNormalVariety.1
  have hXv := hX.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsSeparated sX := hXv.toIsSeparated
  have : IsSeparated (D.f ≫ sX) := hYv.toIsSeparated
  have : LocallyOfFiniteType (D.f ≫ sX) := hYv.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  have : QuasiCompact (D.f ≫ sX) := hYv.toQuasiCompact
  have : IsSeparated D.f := IsSeparated.of_comp D.f sX
  have : LocallyOfFiniteType D.f := locallyOfFiniteType_of_comp D.f sX
  have : QuasiCompact D.f := QuasiCompact.of_comp D.f sX
  have : IsNoetherian X := {}
  have : QuasiSeparatedSpace X := inferInstance
  obtain ⟨P, j, p, hj, hjq, hp, hjp⟩ := exists_isOpenImmersion_isProper_comp_eq D.f
  have : IsSeparated j := by
    have : IsSeparated (j ≫ p) := by rw [hjp]; infer_instance
    exact IsSeparated.of_comp j p
  have : LocallyOfFiniteType (p ≫ sX) := inferInstance
  have : QuasiSeparated j := IsSeparated.instQuasiSeparated j
  obtain ⟨ht, hnorm, hfin⟩ :=
    isOpenImmersion_toNormalization_and_isNormal_and_isFinite (sP := p ≫ sX) j
  set t := j.toNormalization
  let g := j.fromNormalization ≫ p
  have htg : t ≫ g = D.f := by
    simp only [g, t, Scheme.Hom.toNormalization_fromNormalization_assoc, hjp]
  have hgv : IsNormalVariety k (g ≫ sX) :=
    ⟨(isVariety_iff k _).2 ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hnorm⟩
  have hgb : IsBirationalMorphism g :=
    isBirationalMorphism_of_isOpenImmersion_comp t g (htg ▸ D.isBirationalMorphism)
  let D' : DivisorOver k sX :=
    ⟨_, g, hgv, hgb, OpenWeilRestriction.primeDivisorMap t D.E⟩
  refine ⟨D', (inferInstance : IsProper g), (MMP.Positivity.DivisorOver.valuation_eq_of_iso D D' ⊤
    t.opensRange trivial ⟨D.E.genericPoint, ?_⟩ (D.Y.topIso ≪≫ t.isoOpensRange) ?_ ?_).symm⟩
  · exact (OpenWeilRestriction.genericPoint_primeDivisorMap t D.E).symm
  · simp [D', htg]
  · apply Subtype.ext
    change (D.Y.topIso.hom ≫ t.isoOpensRange.hom ≫ t.opensRange.ι) ⟨D.E.genericPoint, trivial⟩ = _
    rw [Scheme.Hom.isoOpensRange_hom_ι]
    exact (OpenWeilRestriction.genericPoint_primeDivisorMap t D.E).symm

end KollarMori222

open MMP.Mori in
private theorem isLcPair_of_isLogCanonicalPair {X : Scheme.{0}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    (hB : MMP.Intersection.IsLogCanonicalPair sX B) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) : IsLcPair sX n K B := by
  obtain ⟨⟨hX, n', K', hK', hQ'⟩, -, hlc⟩ := hB
  haveI : CompactSpace X := haveI := hX.1; QuasiCompact.compactSpace_of_compactSpace sX
  have hlin : K'.LinearlyEquivalent K :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hK' hK
  have hP : IsPairWith sX n K B := ⟨hX, hK, hQ'.add_of_linearlyEquivalent hlin⟩
  refine ⟨hP, le_discrep_iff.mpr fun D a hD ha => ?_⟩
  obtain ⟨E, hEp, hEv⟩ := DivisorOver.exists_isProper_valuation_eq hX D
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hK E
  have haa : a' = a := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hP hEv ha' ha
  have h0 := hlc n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha' hEp)
  have : (-1 : ℝ) ≤ a := by rw [← haa]; linarith
  have h2 := EReal.coe_le_coe_iff.mpr this
  simpa using h2

/-- The zero divisor `div σ + M` of a nonzero section of `𝒪_X(M)`, `M` Cartier, is Cartier. -/
private theorem isCartier_zeroDivisor {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {M : Divisor X} (hM : M.IsCartier) (σ : M.divisorialSubmodule ⊤)
    (hσ : σ ≠ 0) : (M.zeroDivisor σ hσ).IsCartier :=
  (MMP.Mori.Divisor.isCartier_principalDivisor _).add hM

section Restriction

variable {W : Scheme.{0}} [IsIntegral W]

/-- Linear equivalence of Cartier divisors on an integral scheme: `C' - C` is principal. -/
private def CLinEquiv (C C' : W.CartierDivisor) : Prop :=
  MMP.Intersection.LinearlyEquivalent C' C

private theorem cLinEquiv_iff (C C' : W.CartierDivisor) :
    CLinEquiv C C' ↔ Nonempty (MMP.CartierDivisor.sheaf C ≅
      MMP.CartierDivisor.sheaf C') := by
  rw [CLinEquiv, ← MMP.CartierDivisor.nonempty_sheaf_iso_iff]
  exact ⟨fun ⟨e⟩ => ⟨e.symm ≪≫
      Iso.refl (MMP.CartierDivisor.sheaf C')⟩,
    fun ⟨e⟩ => ⟨e.symm ≪≫
      (Iso.refl (MMP.CartierDivisor.sheaf C)).symm⟩⟩

private theorem CLinEquiv.refl (C : W.CartierDivisor) : CLinEquiv C C :=
  MMP.Intersection.LinearlyEquivalent.refl C

private theorem CLinEquiv.symm {C C' : W.CartierDivisor} (h : CLinEquiv C C') : CLinEquiv C' C :=
  MMP.Intersection.linearlyEquivalent_equivalence.symm h

private theorem CLinEquiv.trans {C C' C'' : W.CartierDivisor} (h : CLinEquiv C C')
    (h' : CLinEquiv C' C'') : CLinEquiv C C'' :=
  MMP.Intersection.linearlyEquivalent_equivalence.trans h' h

private theorem CLinEquiv.add {C₁ C₁' C₂ C₂' : W.CartierDivisor} (h₁ : CLinEquiv C₁ C₁')
    (h₂ : CLinEquiv C₂ C₂') : CLinEquiv (C₁ + C₂) (C₁' + C₂') :=
  MMP.Intersection.LinearlyEquivalent.add h₁ h₂

private theorem CLinEquiv.neg {C C' : W.CartierDivisor} (h : CLinEquiv C C') :
    CLinEquiv (-C) (-C') := by
  have := (MMP.Intersection.principalSubgroup W).neg_mem h
  show -C' - -C ∈ _
  convert this using 1
  abel

private theorem CLinEquiv.nsmul {C C' : W.CartierDivisor} (h : CLinEquiv C C') (n : ℕ) :
    CLinEquiv (n • C) (n • C') := by
  induction n with
  | zero => simpa using CLinEquiv.refl (0 : W.CartierDivisor)
  | succ n ih => simpa [succ_nsmul] using ih.add h

private theorem CLinEquiv.zsmul {C C' : W.CartierDivisor} (h : CLinEquiv C C') (n : ℤ) :
    CLinEquiv (n • C) (n • C') := by
  cases n with
  | ofNat n => simpa using h.nsmul n
  | negSucc n => simpa [negSucc_zsmul] using (h.nsmul (n + 1)).neg

/-- `𝒪(C + C') ≅ 𝒪(C) ⊗ 𝒪(C')`. -/
private noncomputable def sheafAddIso (C C' : W.CartierDivisor) :
    MMP.CartierDivisor.sheaf (C + C') ≅
      MMP.CartierDivisor.sheaf C ⊗ MMP.CartierDivisor.sheaf C' :=
  (MMP.CartierDivisorSheaf.sheafMulIso C C').symm ≪≫
    tensorIso (Iso.refl (MMP.CartierDivisor.sheaf C)) (Iso.refl (MMP.CartierDivisor.sheaf C'))

end Restriction

section Restrict

variable {X W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral W] (ι : W ⟶ X)

/-- A Cartier divisor on `W` whose sheaf is the restriction `ι^* 𝒪_X(D)`. -/
private noncomputable def restrictDivisor {D : Divisor X} (hD : D.IsCartier) : W.CartierDivisor :=
  haveI := hD.isInvertibleModule_divisorialSheaf
  (MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf
    ((Scheme.Modules.pullback ι).obj D.divisorialSheaf)).choose

private theorem nonempty_iso_restrictDivisor {D : Divisor X} (hD : D.IsCartier) :
    Nonempty ((Scheme.Modules.pullback ι).obj D.divisorialSheaf ≅
      MMP.CartierDivisor.sheaf (restrictDivisor ι hD)) :=
  haveI := hD.isInvertibleModule_divisorialSheaf
  (MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf
    ((Scheme.Modules.pullback ι).obj D.divisorialSheaf)).choose_spec

private theorem restrictDivisor_add {D D' : Divisor X} (hD : D.IsCartier) (hD' : D'.IsCartier) :
    CLinEquiv (restrictDivisor ι (hD.add hD')) (restrictDivisor ι hD + restrictDivisor ι hD') := by
  rw [cLinEquiv_iff]
  obtain ⟨e⟩ := nonempty_iso_restrictDivisor ι (hD.add hD')
  obtain ⟨e₁⟩ := nonempty_iso_restrictDivisor ι hD
  obtain ⟨e₂⟩ := nonempty_iso_restrictDivisor ι hD'
  exact ⟨e.symm ≪≫ (Scheme.Modules.pullback ι).mapIso (hD.divisorialSheafTensorIso hD').symm ≪≫
    Stacks.ProjectiveBundleConormal.pullbackTensorComparisonIso ι _ _ ≪≫ tensorIso e₁ e₂ ≪≫
    (sheafAddIso _ _).symm⟩

private theorem restrictDivisor_congr {D D' : Divisor X} (hD : D.IsCartier) (h : D = D')
    (hD' : D'.IsCartier) : restrictDivisor ι hD = restrictDivisor ι hD' := by
  subst h; rfl

private theorem restrictDivisor_zero :
    CLinEquiv (restrictDivisor ι (Divisor.isCartier_zero (X := X))) 0 := by
  have h := restrictDivisor_add ι (Divisor.isCartier_zero (X := X)) Divisor.isCartier_zero
  rw [restrictDivisor_congr ι _ (add_zero (0 : Divisor X)) Divisor.isCartier_zero] at h
  have := (MMP.Intersection.principalSubgroup _).neg_mem h
  simpa [CLinEquiv, MMP.Intersection.LinearlyEquivalent] using this

private theorem restrictDivisor_nsmul {D : Divisor X} (hD : D.IsCartier) (n : ℕ) :
    CLinEquiv (restrictDivisor ι (hD.nsmul n)) (n • restrictDivisor ι hD) := by
  induction n with
  | zero =>
    rw [restrictDivisor_congr ι _ (zero_nsmul D) Divisor.isCartier_zero, zero_nsmul]
    exact restrictDivisor_zero ι
  | succ n ih =>
    rw [restrictDivisor_congr ι _ (succ_nsmul D n) ((hD.nsmul n).add hD), succ_nsmul]
    exact (restrictDivisor_add ι (hD.nsmul n) hD).trans (ih.add (CLinEquiv.refl _))

private theorem restrictDivisor_neg {D : Divisor X} (hD : D.IsCartier) :
    CLinEquiv (restrictDivisor ι hD.neg) (-restrictDivisor ι hD) := by
  have h := restrictDivisor_add ι hD.neg hD
  rw [restrictDivisor_congr ι _ (neg_add_cancel D) Divisor.isCartier_zero] at h
  have h0 := (restrictDivisor_zero ι).symm.trans h
  have h1 : restrictDivisor ι hD.neg + restrictDivisor ι hD - 0 ∈
      MMP.Intersection.principalSubgroup _ := h0
  have := (MMP.Intersection.principalSubgroup _).neg_mem h1
  show -restrictDivisor ι hD - restrictDivisor ι hD.neg ∈ _
  convert this using 1
  abel

end Restrict

section Setup

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX]

/-- The lc centres of `(X, B)`: the centres of the divisors over `X` of log discrepancy `0`. -/
private def lcCentres (B : QDivisor X) : Set (IrreducibleCloseds X) :=
  {Z | ∃ E : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) E 0 ∧ E.center = Z}

/-- A minimal lc centre: an lc centre containing no other lc centre. -/
private def IsMinimalLcCentre (B : QDivisor X) (W : IrreducibleCloseds X) : Prop :=
  W ∈ lcCentres sX B ∧ ∀ Z ∈ lcCentres sX B, Z ≤ W → Z = W

/-- An lc place, a divisor over `X` of log discrepancy `0` over `(X, B)`, has discrepancy `-1`. -/
private theorem isDiscrepancy_neg_one_of_isLogDiscrepancy_zero {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X} (hB : IsLogCanonicalPair sX B)
    {E : DivisorOver ℂ sX} (hE : IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) E 0) :
    MMP.Mori.IsDiscrepancy sX 4 K B E (-1) := by
  obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy
    (isLcPair_of_isLogCanonicalPair hB hK).1.isPair hK E
  have h := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hb hE
  have hb1 : b = -1 := by exact_mod_cast (show ((b : ℚ) : ℝ) = -1 by linarith)
  exact hb1 ▸ hb

/-- **Finiteness of lc centres.** -/
private theorem lcCentres_finite (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X}
    (hB : IsLogCanonicalPair sX B) : (lcCentres sX B).Finite := by
  have hlc := isLcPair_of_isLogCanonicalPair hB hK
  have hproj : IsProjectiveMorphism sX :=
    (show AlgebraicGeometry.IsProjectiveVariety ℂ sX from hX).isProjective
  obtain ⟨hfin, -, -⟩ := MMP.Mori.IsLcPair.finite_lcCentres_and_isNormal_of_minimal hproj hlc hB.2.1
  refine hfin.subset ?_
  rintro Z ⟨E, hE, rfl⟩
  exact ⟨E, rfl, isDiscrepancy_neg_one_of_isLogDiscrepancy_zero sX hK hB hE⟩

/-- Every lc centre contains a minimal lc centre. -/
private theorem exists_isMinimalLcCentre_le (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X}
    (hB : IsLogCanonicalPair sX B) {Z : IrreducibleCloseds X} (hZ : Z ∈ lcCentres sX B) :
    ∃ W, IsMinimalLcCentre sX B W ∧ W ≤ Z := by
  obtain ⟨W, hWZ, hWmin⟩ := (lcCentres_finite sX hX hK hB).exists_le_minimal hZ
  exact ⟨W, ⟨hWmin.prop, fun Z' hZ' hZ'W => le_antisymm hZ'W (hWmin.2 hZ' hZ'W)⟩, hWZ⟩

/-- `L` is numerically trivial on `W ⊆ X`: it has degree zero on every proper curve in `W`. -/
private def IsNumTrivialOn {L : Divisor X} (hL : L.IsCartier) (W : Set X) : Prop :=
  ∀ (C : Scheme.{0}) (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sX)]
    (hC : topologicalKrullDim C = 1), Set.range i ⊆ W → L.degreeOn ℂ sX i hC.le hL = 0

/-- The reduced closed subscheme structure on an irreducible closed subset. -/
private noncomputable abbrev centreι (W : IrreducibleCloseds X) :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subschemeι

/-- A nonnegative rational multiple of a nef Cartier divisor is a nef `ℚ`-divisor. -/
private theorem isNef_smul_toQDivisor {L : Divisor X} (hL : L.IsNef ℂ sX) {t : ℚ} (ht : 0 ≤ t) :
    (t • Divisor.toQDivisor L).IsNef ℂ sX := by
  have hnum : 0 ≤ t.num := Rat.num_nonneg.mpr ht
  have hden : 0 < t.den := t.den_pos
  have hE : Divisor.toQDivisor (t.num.toNat • L) =
      ((t.den : ℕ) : ℤ) • (t • Divisor.toQDivisor L) := by
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    congr 1
    push_cast
    rw [Rat.den_mul_eq_num]
    exact_mod_cast Int.toNat_of_nonneg hnum
  have hEc : (t.num.toNat • L).IsCartier := hL.1.nsmul _
  have hq : (t • Divisor.toQDivisor L).IsQCartier :=
    ⟨t.den, by exact_mod_cast hden.ne', by rw [← hE]; exact QDivisor.isCartierDivisor_toQDivisor.mpr hEc⟩
  refine ⟨hq, fun C i _ _ _ hC => ?_⟩
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sX i hC.le _ hq hden _ hEc hE,
    Divisor.degreeOn_nsmul' ℂ sX i hC.le L hL.1]
  have := hL.2 C i hC
  positivity

/-- **Ample plus a nonnegative multiple of a nef divisor is ample.** -/
private theorem isAmple_add_smul_of_isNef (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {A : QDivisor X} (hA : A.IsAmple) {L : Divisor X} (hL : L.IsNef ℂ sX) {t : ℚ} (ht : 0 ≤ t) :
    (A + t • Divisor.toQDivisor L).IsAmple := by
  haveI := hX
  obtain ⟨mA, hmA, DA, hDA, hDAc, hDAamp⟩ := hA
  have hN := isNef_smul_toQDivisor sX hL ht
  have hden : 0 < t.den := t.den_pos
  set D' : Divisor X := t.den • DA + (mA * t.num) • L
  have hD' : Divisor.toQDivisor D' = ((mA * t.den : ℕ) : ℚ) • (A + t • Divisor.toQDivisor L) := by
    have key : (((mA : ℤ) * t.num : ℤ) : ℚ) = (mA : ℚ) * t.den * t := by
      rw [mul_assoc, Rat.den_mul_eq_num]; push_cast; ring
    simp only [D', map_add, map_nsmul, map_zsmul, hDA]
    rw [← Int.cast_smul_eq_zsmul ℚ, key, ← Nat.cast_smul_eq_nsmul ℚ]
    push_cast
    module
  have hD'c : D'.IsCartier := (hDAc.nsmul _).add (hL.1.zsmul _)
  have hAq : A.IsQCartier := ⟨mA, by exact_mod_cast hmA.ne', by
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ, ← hDA]
    exact QDivisor.isCartierDivisor_toQDivisor.mpr hDAc⟩
  refine ⟨mA * t.den, Nat.mul_pos hmA hden, D', hD', hD'c, ?_⟩
  exact MMP.Mori.QDivisor.isAmple_of_numericallyEquivalent_add_of_isNef sX
    ⟨mA, hmA, DA, hDA, hDAc, hDAamp⟩ hN (MMP.Mori.QDivisor.NumericallyEquivalent.refl (hAq.add hN.1))
    _ (Nat.mul_pos hmA hden) D' hD' hD'c

/-- **A section nonzero on `W` does not vanish at the generic point of `W`.** If the pull-back
of a global section `σ` of `𝒪_X(M)`, `M` Cartier, to the reduced subscheme on an irreducible
closed `W` is nonzero, then `W ⊄ Bs|M|`. -/
private theorem not_subset_supp_zeroDivisor_of_pullback_ne_zero {M : Divisor X}
    (hM : M.IsCartier) (W : IrreducibleCloseds X) (σ : Γ(M.divisorialSheaf, ⊤)) (hσ0 : σ ≠ 0)
    (hσ : AlgebraicGeometry.pullbackGlobalSections (centreι W) M.divisorialSheaf σ ≠ 0) :
    ¬ (W : Set X) ⊆ ((M.zeroDivisor σ hσ0).supp : Set X) := by
  haveI := hM.isInvertibleModule_divisorialSheaf
  set Wc : Closeds X := ⟨(W : Set X), W.isClosed⟩
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Wc).subscheme :=
    MMP.Fourfold.isIntegral_subscheme_vanishingIdeal Wc W.isIrreducible
  haveI : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal Wc).subscheme :=
    isLocallyNoetherian_of_isClosedImmersion (centreι W)
  have hgerm := Stacks.AlgebraicGeometry.ReflexiveModules.Γgerm_genericPoint_ne_zero_of_ne_zero _ hσ
  have hnv := Stacks.ProjectiveFromSections.mem_nvOpen_genericPoint_of_germ_ne_zero _ hgerm
  rw [Stacks.ProjectiveFromSections.nvOpen,
    Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.nonvanishingOpen_pullbackGlobalSections]
    at hnv
  have hx : centreι W (genericPoint _) ∈ Stacks.Ample.nonvanishingLocus M.divisorialSheaf σ := hnv
  rw [MMP.Mori.Divisor.nonvanishingLocus_eq_compl_supp_zeroDivisor hM σ hσ0] at hx
  intro hW
  have hxW : centreι W (genericPoint _) ∈ (W : Set X) := by
    have : centreι W (genericPoint _) ∈ Set.range (centreι W) := ⟨_, rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
  exact hx (hW hxW)

/-- **A section nonzero on `W` keeps `W` out of the base locus.** -/
private theorem not_subset_baseLocus_of_pullback_ne_zero {M : Divisor X} (hM : M.IsCartier)
    (W : IrreducibleCloseds X) (σ : Γ(M.divisorialSheaf, ⊤))
    (hσ : AlgebraicGeometry.pullbackGlobalSections (centreι W) M.divisorialSheaf σ ≠ 0) :
    ¬ (W : Set X) ⊆ (M.baseLocus : Set X) := by
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    exact hσ (map_zero _)
  exact fun hW => not_subset_supp_zeroDivisor_of_pullback_ne_zero hM W σ hσ0 hσ
    (hW.trans (M.baseLocus_le_supp σ hσ0))

/-- For all large `m`, `mL - (K_X + B)` is ample. -/
private theorem eventually_isAmple_nsmul_sub (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {K : Divisor X} {L : Divisor X} (hL : L.IsNef ℂ sX) {B : QDivisor X} {a : ℚ}
    (hample : (a • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsAmple) :
    ∀ᶠ m : ℕ in atTop, (Divisor.toQDivisor (m • L) - (Divisor.toQDivisor K + B)).IsAmple := by
  filter_upwards [eventually_ge_atTop ⌈a⌉₊] with m hm
  have hma : a ≤ m := Nat.ceil_le.mp hm
  have := isAmple_add_smul_of_isNef sX hX hample hL (t := (m : ℚ) - a) (by linarith)
  convert this using 1
  rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, sub_smul]
  abel

/-- **Lifting sections from an lc centre** (lc-centre ideal vanishing). If `M - (K_X + B)` is
ample, every section of `M|_W` on an lc centre `W` lifts to a section of `𝒪_X(M)`. -/
private theorem exists_pullbackGlobalSections_eq (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X} (hB : IsLogCanonicalPair sX B)
    {W : IrreducibleCloseds X} (hW : W ∈ lcCentres sX B) {M : Divisor X} (hMc : M.IsCartier)
    (hgap : (Divisor.toQDivisor M - (Divisor.toQDivisor K + B)).IsAmple)
    (τ : ((Scheme.Modules.pullback (centreι W)).obj M.divisorialSheaf).val.obj (Opposite.op ⊤)) :
    ∃ σ : M.divisorialSheaf.val.obj (Opposite.op ⊤),
      AlgebraicGeometry.pullbackGlobalSections (centreι W) M.divisorialSheaf σ = τ := by
  obtain ⟨E, hE, hEW⟩ := hW
  obtain ⟨σ, hσ⟩ := (MMP.Mori.isZero_Hgroup_kernel_unit_and_surjective_of_isAmple_sub sX
    (show AlgebraicGeometry.IsProjectiveVariety ℂ sX from hX).isProjective
    (isLcPair_of_isLogCanonicalPair hB hK) hB.2.1 ⟨(W : Set X), W.isClosed⟩ {W}
    (by rintro Z rfl; exact ⟨E, hEW, isDiscrepancy_neg_one_of_isLogDiscrepancy_zero sX hK hB hE⟩)
    (by simp) hMc hgap).2.2 τ
  exact ⟨σ, by rw [AlgebraicGeometry.pullbackGlobalSections_eq_unit]; exact hσ⟩

/-- **Lifting sections from an lc centre.** If `H⁰(W, mL|_W) ≠ 0` for all large `m`, then
`W ⊄ Bs|mL|` for all large `m`: for `mL - (K_X + B)` ample, lc-centre ideal vanishing lifts a
nonzero section of `mL|_W` to `X`, and the lift does not vanish at the generic point of `W`. -/
private theorem eventually_not_subset_of_eventually_sections
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {L : Divisor X} (hL : L.IsNef ℂ sX)
    {B : QDivisor X} {a : ℚ} (hB : IsLogCanonicalPair sX B)
    (hample : (a • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsAmple)
    {W : IrreducibleCloseds X} (hW : W ∈ lcCentres sX B)
    (hsec : ∀ᶠ m : ℕ in atTop, ∃ s : ((Scheme.Modules.pullback (centreι W)).obj
      (m • L).divisorialSheaf).val.obj (Opposite.op ⊤), s ≠ 0) :
    ∀ᶠ m : ℕ in atTop, ¬ (W : Set X) ⊆ (L.baseLocusOfMultiple m : Set X) := by
  filter_upwards [hsec, eventually_isAmple_nsmul_sub sX hX hL hample] with m ⟨s, hs⟩ hm
  obtain ⟨σ, hσ⟩ := exists_pullbackGlobalSections_eq sX hX hK hB hW (hL.1.nsmul m) hm s
  exact not_subset_baseLocus_of_pullback_ne_zero (hL.1.nsmul m) W σ (hσ ▸ hs)

/-- The reduced subscheme on an irreducible closed subset is integral. -/
private theorem isIntegral_centre (W : IrreducibleCloseds X) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme :=
  MMP.Fourfold.isIntegral_subscheme_vanishingIdeal _ W.isIrreducible

attribute [local instance 1100] isIntegral_centre

/-- The reduced subscheme on a closed subset of a locally Noetherian scheme is locally
Noetherian. -/
private theorem isLocallyNoetherian_centre (W : IrreducibleCloseds X) :
    IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme :=
  isLocallyNoetherian_of_isClosedImmersion (Scheme.IdealSheafData.vanishingIdeal _).subschemeι

attribute [local instance 1100] isLocallyNoetherian_centre

/-- The image of the reduced subscheme on `W` is `W`. -/
private theorem range_centreι (W : IrreducibleCloseds X) :
    Set.range (centreι W) = (W : Set X) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- **Vanishing on a minimal lc centre, for restrictions of Cartier divisors.** If `M` is a
Cartier divisor on `X` and some multiple `m'(M - (K_X + B))` is a Cartier divisor `G` whose
restriction to the minimal lc centre `W` is ample, then `Hⁱ(W, M|_W) = 0` for `i > 0`. -/
private theorem isZero_Hgroup_restrictDivisor (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : IsLogCanonicalPair sX B) {W : IrreducibleCloseds X}
    (hW : IsMinimalLcCentre sX B W) {M : Divisor X} (hM : M.IsCartier)
    (hgap : ∃ m' : ℕ, 0 < m' ∧ ∃ (G : Divisor X) (hG : G.IsCartier),
      Divisor.toQDivisor G = (m' : ℚ) • (Divisor.toQDivisor M - (Divisor.toQDivisor K + B)) ∧
      Stacks.Ample.IsAmple _
        (MMP.CartierDivisor.sheaf (restrictDivisor (centreι W) hG))) :
    ∀ i : ℕ, 0 < i → Limits.IsZero (Hgroup (Scheme.IdealSheafData.vanishingIdeal
      ⟨(W : Set X), W.isClosed⟩).subscheme.ringCatSheaf ⊤ i
      (MMP.CartierDivisor.sheaf (restrictDivisor (centreι W) hM))) := by
  haveI := hX
  obtain ⟨m', hm', G, hG, hGq, hamp⟩ := hgap
  set ι := centreι W
  have hE : (m' • M - G).IsCartier := (hM.nsmul m').add hG.neg
  have hlin : CLinEquiv (restrictDivisor ι hE)
      (m' • restrictDivisor ι hM - restrictDivisor ι hG) := by
    rw [restrictDivisor_congr ι hE (sub_eq_add_neg _ _) ((hM.nsmul m').add hG.neg), sub_eq_add_neg]
    exact (restrictDivisor_add ι (hM.nsmul m') hG.neg).trans
      ((restrictDivisor_nsmul ι hM m').add (restrictDivisor_neg ι hG))
  obtain ⟨e⟩ := (cLinEquiv_iff _ _).mp hlin
  obtain ⟨eE⟩ := nonempty_iso_restrictDivisor ι hE
  refine MMP.Fourfold.isZero_Hgroup_lineBundle_of_minimal_lcCentre (X := X) sX hdim hK hB ι ?_ ?_ _
    ⟨m', hm', m' • M - G, ?_, hE, restrictDivisor ι hG, ?_,
      ⟨e.symm ≪≫ eE.symm⟩⟩
  · obtain ⟨⟨F, hF, hFW⟩, -⟩ := hW
    exact ⟨F, hF, by rw [range_centreι, ← hFW]⟩
  · intro F hF hsub
    rw [range_centreι] at hsub ⊢
    have := hW.2 F.center ⟨F, hF, rfl⟩ hsub
    rw [this]
  · rw [map_sub, map_nsmul, hGq, ← Nat.cast_smul_eq_nsmul ℚ, smul_sub, sub_sub_cancel]
  · exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
      (Iso.refl _)).2 hamp

/-- **The restriction of an ample divisor to an lc centre is ample** (Stacks 01PU). -/
private theorem isAmple_sheaf_restrictDivisor {G : Divisor X} (hG : G.IsCartier)
    (hamp : G.IsAmple hG) (W : IrreducibleCloseds X) :
    Stacks.Ample.IsAmple _
      (MMP.CartierDivisor.sheaf (restrictDivisor (centreι W) hG)) := by
  haveI := hG.isInvertibleModule_divisorialSheaf
  obtain ⟨e⟩ := nonempty_iso_restrictDivisor (centreι W) hG
  have h1 : Scheme.Modules.IsAmple X G.divisorialSheaf :=
    (Stacks.AmpleBridge.isAmple_iff_isAmple X _).1 hamp
  have h2 := Scheme.Modules.isAmple_pullback_of_isClosedImmersion (centreι W) _ h1
  have h3 := (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).2 h2
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).1 h3

/-- The reduced subscheme on an irreducible closed subset of a projective complex variety is a
projective complex variety. -/
private theorem isProjectiveVariety_centre (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (W : IrreducibleCloseds X) : MMP.Mori.IsProjectiveVariety ℂ (centreι W ≫ sX) := by
  haveI : IsReduced (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hX' : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI := hX'.toIsVariety
  refine { toIsIntegral := inferInstance, isProjective := ?_ }
  obtain ⟨n, i, hi, hisX⟩ := hX'.isProjective
  exact ⟨n, centreι W ≫ i, inferInstance, by rw [Category.assoc, hisX]⟩

/-- The degree of the restriction `D|_W` along a curve `j : C ⟶ W` is the degree of `D` along
`j ≫ ι`. -/
private theorem degreeOn_sheaf_restrictDivisor (W : IrreducibleCloseds X) {D : Divisor X}
    (hD : D.IsCartier) {C : Scheme.{0}} (j : C ⟶ _) [IsProper (j ≫ centreι W ≫ sX)]
    [IsProper ((j ≫ centreι W) ≫ sX)] (hC : topologicalKrullDim C ≤ 1) :
    MMP.Mori.degreeOn ℂ (centreι W ≫ sX) j hC
        (MMP.CartierDivisor.sheaf (restrictDivisor (centreι W) hD)) =
      D.degreeOn ℂ sX (j ≫ centreι W) hC hD := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  obtain ⟨e⟩ := nonempty_iso_restrictDivisor (centreι W) hD
  rw [← MMP.Mori.degreeOn_eq_of_iso ℂ _ j hC e]
  exact MMP.Mori.degreeOn_pullback_eq_degreeOn_comp (centreι W ≫ sX) sX (centreι W) j rfl hC _

/-- The degree of the restriction `D|_W` along a proper curve of `W` is the degree of `D` along
that curve in `X`. -/
private theorem degree_sheaf_restrictDivisor (W : IrreducibleCloseds X) {D : Divisor X}
    (hD : D.IsCartier) (C : MMP.Mori.ProperCurve (centreι W ≫ sX))
    [IsProper ((C.ι ≫ centreι W) ≫ sX)] :
    C.degree ℂ (MMP.CartierDivisor.sheaf (restrictDivisor (centreι W) hD)) =
      D.degreeOn ℂ sX (C.ι ≫ centreι W) C.dim_le hD := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  obtain ⟨e⟩ := nonempty_iso_restrictDivisor (centreι W) hD
  rw [MMP.Mori.ProperCurve.degree, ← MMP.Mori.degreeOn_eq_of_iso ℂ _ C.ι C.dim_le e]
  exact MMP.Mori.degreeOn_pullback_eq_degreeOn_comp (centreι W ≫ sX) sX (centreι W) C.ι rfl
    C.dim_le _

/-- The degree of a negated Cartier divisor along a curve. -/
private theorem degreeOn_neg {C : Scheme.{0}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hC : topologicalKrullDim C ≤ 1) {D : Divisor X} (hD : D.IsCartier) :
    (-D).degreeOn ℂ sX i hC hD.neg = -D.degreeOn ℂ sX i hC hD := by
  have h := MMP.Mori.Divisor.degreeOn_add ℂ sX i hC D (-D) hD hD.neg
  rw [MMP.Mori.Divisor.degreeOn_congr (add_neg_cancel D) _ Divisor.isCartier_zero,
    MMP.Mori.Divisor.degreeOn_zero'] at h
  omega

/-- **The anticanonical restriction is ample in the numerically trivial case.** If `L` is
numerically trivial on the lc centre `W`, then some multiple `m'(-(K_X + B))` is a Cartier
divisor `G` whose restriction to `W` is ample: on `W` it is numerically a multiple of the
restriction of the ample `aL - (K_X + B)`, and ampleness on the projective `W` is numerical
(Kleiman). -/
private theorem exists_isAmple_restrict_neg_of_isNumTrivialOn
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {K : Divisor X} {L : Divisor X} (hL : L.IsNef ℂ sX) {B : QDivisor X} {a : ℚ} (ha : 0 < a)
    (hample : (a • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsAmple)
    (W : IrreducibleCloseds X) (htriv : IsNumTrivialOn sX hL.1 (W : Set X)) :
    ∃ m' : ℕ, 0 < m' ∧ ∃ (G : Divisor X) (hG : G.IsCartier),
      Divisor.toQDivisor G = (m' : ℚ) • (Divisor.toQDivisor (0 • L) - (Divisor.toQDivisor K + B)) ∧
      Stacks.Ample.IsAmple _
        (MMP.CartierDivisor.sheaf (restrictDivisor (centreι W) hG)) := by
  haveI := hX
  obtain ⟨n₀, hn₀, D₀, hD₀, hD₀c, hD₀amp⟩ := hample
  have hnum : 0 < a.num := Rat.num_pos.mpr ha
  set c : ℕ := n₀ * a.num.toNat
  set G : Divisor X := a.den • D₀ + -(c • L)
  have hGc : G.IsCartier := (hD₀c.nsmul _).add (hL.1.nsmul c).neg
  refine ⟨n₀ * a.den, Nat.mul_pos hn₀ a.den_pos, G, hGc, ?_, ?_⟩
  · have hc : (c : ℚ) = n₀ * a.den * a := by
      rw [mul_assoc, Rat.den_mul_eq_num]
      simp only [c, Nat.cast_mul]
      congr 1
      exact_mod_cast Int.toNat_of_nonneg hnum.le
    simp only [G, map_add, map_neg, map_nsmul, hD₀, zero_smul, map_zero, zero_sub]
    rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, hc]
    push_cast
    module
  · set W' := (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme
    haveI : IsReduced W' := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
    haveI := isProjectiveVariety_centre sX hX W
    have hA := isAmple_sheaf_restrictDivisor hD₀c hD₀amp W
    rw [MMP.Mori.isAmple_cartierSheaf_iff_forall_closedConeOfCurves_pos (centreι W ≫ sX)] at hA ⊢
    intro z hz hz0
    have key : MMP.Mori.NumericalCurveClasses.intersectionNumber
        (MMP.Mori.KCartierDivisor.ofCartier ℝ (restrictDivisor (centreι W) hGc)) z =
        (a.den : ℝ) * MMP.Mori.NumericalCurveClasses.intersectionNumber
          (MMP.Mori.KCartierDivisor.ofCartier ℝ (restrictDivisor (centreι W) hD₀c)) z := by
      rw [MMP.Mori.NumericalCurveClasses.intersectionNumber_ofCartier,
        MMP.Mori.NumericalCurveClasses.intersectionNumber_ofCartier]
      obtain ⟨Z, rfl⟩ := MMP.Mori.OneCycle.numericalClass_surjective _ z
      rw [MMP.Mori.NumericalCurveClasses.degree_numericalClass,
        MMP.Mori.NumericalCurveClasses.degree_numericalClass,
        MMP.Mori.OneCycle.degree_apply, MMP.Mori.OneCycle.degree_apply, Finsupp.sum,
        Finsupp.sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun C _ => ?_
      haveI : IsProper ((C.ι ≫ centreι W) ≫ sX) := by rw [Category.assoc]; infer_instance
      rw [degree_sheaf_restrictDivisor sX W hGc C, degree_sheaf_restrictDivisor sX W hD₀c C]
      have h0 : L.degreeOn ℂ sX (C.ι ≫ centreι W) C.dim_le hL.1 = 0 :=
        htriv C.scheme (C.ι ≫ centreι W) C.dim_eq (by
          rintro y ⟨c, rfl⟩
          have hmem : centreι W (C.ι c) ∈ Set.range (centreι W) := ⟨_, rfl⟩
          rw [range_centreι] at hmem
          simpa [Scheme.Hom.comp_apply] using hmem)
      simp only [G]
      rw [MMP.Mori.Divisor.degreeOn_add ℂ sX _ C.dim_le _ _ (hD₀c.nsmul _) (hL.1.nsmul c).neg,
        degreeOn_neg sX _ C.dim_le (hL.1.nsmul c),
        MMP.Mori.Divisor.degreeOn_nsmul' ℂ sX _ C.dim_le D₀ hD₀c,
        MMP.Mori.Divisor.degreeOn_nsmul' ℂ sX _ C.dim_le L hL.1, h0]
      push_cast
      ring
    rw [key]
    exact mul_pos (by exact_mod_cast a.den_pos) (hA z hz hz0)

/-- `k`-linear cohomology of isomorphic modules is `k`-linearly isomorphic. -/
private noncomputable def cohomologyOverFieldLinearEquivOfIso {Y : Scheme.{0}}
    (f : Y ⟶ Spec (.of ℂ)) {F G : Y.Modules} (e : F ≅ G) (n : ℕ) :
    cohomologyOverField ℂ f F n ≃ₗ[ℂ] cohomologyOverField ℂ f G n :=
  ((ModuleCat.restrictScalars _).mapIso
    (((SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op (⊤ : Y.Opens))).rightDerived n).mapIso
      e)).toLinearEquiv

/-- Vanishing cohomology has dimension zero. -/
private theorem finrank_cohomologyOverField_eq_zero {Y : Scheme.{0}} (f : Y ⟶ Spec (.of ℂ))
    (F : Y.Modules) (n : ℕ) (h : Limits.IsZero (Hgroup Y.ringCatSheaf ⊤ n F)) :
    Module.finrank ℂ (cohomologyOverField ℂ f F n) = 0 := by
  have h0 : ∀ x : Hgroup Y.ringCatSheaf ⊤ n F, x = 0 := fun x => by
    simpa using ConcreteCategory.congr_hom (h.eq_of_src (𝟙 _) 0) x
  haveI : Subsingleton (Hgroup Y.ringCatSheaf ⊤ n F) := ⟨fun x y => (h0 x).trans (h0 y).symm⟩
  haveI := (cohomologyOverFieldAddEquivHgroup ℂ f F n).injective.subsingleton
  exact Module.finrank_zero_of_subsingleton

/-- A rational polynomial in one variable with nonzero value at `0` is nonzero at all large
natural numbers. -/
private theorem eventually_eval_ne_zero (P : MvPolynomial (Fin 1) ℚ)
    (h0 : MvPolynomial.eval (fun _ => (0 : ℚ)) P ≠ 0) :
    ∀ᶠ m : ℕ in atTop, MvPolynomial.eval (fun _ => (m : ℚ)) P ≠ 0 := by
  have hp' : ∀ (Q : MvPolynomial (Fin 1) ℚ) (x : ℚ),
      (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) Q).eval x =
        MvPolynomial.eval (fun _ => x) Q := by
    intro Q x
    induction Q using MvPolynomial.induction_on with
    | C r => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  set p : Polynomial ℚ := MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) P
  have hp : ∀ x : ℚ, p.eval x = MvPolynomial.eval (fun _ => x) P := hp' P
  have hp0 : p ≠ 0 := fun h => h0 (by rw [← hp, h, Polynomial.eval_zero])
  have hfin : {m : ℕ | p.eval (m : ℚ) = 0}.Finite :=
    ((p.roots.toFinset : Set ℚ).toFinite.preimage Nat.cast_injective.injOn).subset
      fun m hm => by simpa [Polynomial.mem_roots hp0] using hm
  have := hfin.compl_mem_cofinite
  rw [Nat.cofinite_eq_atTop] at this
  filter_upwards [this] with m hm
  rw [← hp]
  exact hm

/-- **The numerically trivial case.** If `L|_W` is numerically trivial on a minimal lc centre
`W`, then `H⁰(W, mL|_W) ≠ 0` for all large `m`. -/
private theorem eventually_sections_of_isNumTrivialOn
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {L : Divisor X} (hL : L.IsNef ℂ sX)
    {B : QDivisor X} {a : ℚ} (hB : IsLogCanonicalPair sX B) (ha : 0 < a)
    (hample : (a • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsAmple)
    {W : IrreducibleCloseds X} (hW : IsMinimalLcCentre sX B W)
    (htriv : IsNumTrivialOn sX hL.1 (W : Set X)) :
    ∀ᶠ m : ℕ in atTop, ∃ s : ((Scheme.Modules.pullback (centreι W)).obj
      (m • L).divisorialSheaf).val.obj (Opposite.op ⊤), s ≠ 0 := by
  haveI := hX
  set Ws := (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme
  set ι := centreι W
  haveI hWp := isProjectiveVariety_centre sX hX W
  have hWp' : AlgebraicGeometry.IsProjectiveVariety ℂ (ι ≫ sX) := hWp
  haveI := hWp'.toIsVariety
  haveI : IsProper (ι ≫ sX) := (IsProjectiveMorphism.isProjective hWp'.isProjective).isProper
  obtain ⟨n, hn⟩ := AlgebraicGeometry.exists_topologicalKrullDim_eq_natCast_of_isVariety ℂ (ι ≫ sX)
  set N₁ := restrictDivisor ι hL.1
  obtain ⟨P, -, hP⟩ :=
    MMP.Resolution.Bridges.exists_polynomial_eulerChar_cartierSheaf_sum ℂ (ι ≫ sX) n hn ![N₁]
  -- the sheaf of the `m`-th twist is the restriction of `mL`
  have hsum : ∀ m : ℕ, (∑ i : Fin 1, ((fun _ => (m : ℤ)) i) • ![N₁] i) = m • N₁ := by
    intro m; simp
  have hiso : ∀ m : ℕ, Nonempty (MMP.CartierDivisor.sheaf
      (∑ i : Fin 1, ((fun _ => (m : ℤ)) i) • ![N₁] i) ≅
      MMP.CartierDivisor.sheaf (restrictDivisor ι (hL.1.nsmul m))) := by
    intro m
    obtain ⟨e⟩ := (cLinEquiv_iff _ _).mp (restrictDivisor_nsmul ι hL.1 m).symm
    exact ⟨eqToIso (by rw [hsum m]) ≪≫ e⟩
  -- the Euler characteristic is `h⁰` when the gap is ample on `W`
  have hχ : ∀ m : ℕ, (∃ m' : ℕ, 0 < m' ∧ ∃ (G : Divisor X) (hG : G.IsCartier),
      Divisor.toQDivisor G = (m' : ℚ) • (Divisor.toQDivisor (m • L) - (Divisor.toQDivisor K + B)) ∧
      Stacks.Ample.IsAmple _
        (MMP.CartierDivisor.sheaf (restrictDivisor (centreι W) hG))) →
      MvPolynomial.eval (fun _ => (m : ℚ)) P = (Module.finrank ℂ (cohomologyOverField ℂ (ι ≫ sX)
        (MMP.CartierDivisor.sheaf (∑ i : Fin 1, ((fun _ => (m : ℤ)) i) • ![N₁] i))
        0) : ℚ) := by
    intro m hgap
    have hvan := isZero_Hgroup_restrictDivisor sX hX hdim hK hB hW (hL.1.nsmul m) hgap
    obtain ⟨e⟩ := hiso m
    have h := hP (fun _ => (m : ℤ))
    simp only [Int.cast_natCast] at h
    rw [h, finsum_eq_single _ 0 fun j hj => by
      rw [(cohomologyOverFieldLinearEquivOfIso (ι ≫ sX) e j).finrank_eq,
        finrank_cohomologyOverField_eq_zero _ _ j (hvan j (Nat.pos_of_ne_zero hj))]
      simp]
    simp
  -- at `m = 0` the Euler characteristic is `h⁰(W, 𝒪_W) = 1`
  have h0 : MvPolynomial.eval (fun _ => ((0 : ℕ) : ℚ)) P = 1 := by
    rw [hχ 0 (exists_isAmple_restrict_neg_of_isNumTrivialOn sX hX hL ha hample W htriv)]
    obtain ⟨e⟩ := MMP.Resolution.Bridges.cartierSheaf_sum_iso_twistedSheaf (X := Ws)
      (Fin.elim0 : Fin 0 → Ws.CartierDivisor) (Fin.elim0 : Fin 0 → ℤ)
    have hz : (∑ i : Fin 1, ((fun _ => ((0 : ℕ) : ℤ)) i) • ![N₁] i) =
        ∑ i : Fin 0, (Fin.elim0 i : ℤ) • (Fin.elim0 i : Ws.CartierDivisor) := by
      simp
    rw [hz, (cohomologyOverFieldLinearEquivOfIso (ι ≫ sX) e 0).finrank_eq]
    have := (Stacks.AlgebraicGeometry.ProperSectionsGeom.finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections
      ℂ (ι ≫ sX)).trans (AlgebraicGeometry.finrank_globalSections_eq_one ℂ (ι ≫ sX))
    exact_mod_cast this
  filter_upwards [eventually_isAmple_nsmul_sub sX hX hL hample,
    eventually_eval_ne_zero P (by
      rw [show (fun _ : Fin 1 => (0 : ℚ)) = fun _ => ((0 : ℕ) : ℚ) by simp, h0]
      exact one_ne_zero)] with m hm hne
  obtain ⟨m', hm', G, hGq, hGc, hGamp⟩ := hm
  rw [hχ m ⟨m', hm', G, hGc, hGq, isAmple_sheaf_restrictDivisor hGc hGamp W⟩] at hne
  have hpos : 0 < Module.finrank ℂ (cohomologyOverField ℂ (ι ≫ sX)
      (MMP.CartierDivisor.sheaf (∑ i : Fin 1, ((fun _ => (m : ℤ)) i) • ![N₁] i))
      0) := Nat.pos_of_ne_zero (by exact_mod_cast hne)
  haveI := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨x, hx⟩ := exists_ne (0 : cohomologyOverField ℂ (ι ≫ sX)
    (MMP.CartierDivisor.sheaf (∑ i : Fin 1, ((fun _ => (m : ℤ)) i) • ![N₁] i)) 0)
  obtain ⟨e⟩ := hiso m
  obtain ⟨e'⟩ := nonempty_iso_restrictDivisor ι (hL.1.nsmul m)
  set F := e ≪≫ e'.symm
  refine ⟨F.hom.app ⊤ ((cohomologyOverFieldZeroLinearIso ℂ (ι ≫ sX) _).hom x), fun h => hx ?_⟩
  have h1 : (cohomologyOverFieldZeroLinearIso ℂ (ι ≫ sX) _).hom x = 0 :=
    Scheme.Modules.injective_app_of_mono F.hom ⊤ (h.trans (map_zero _).symm)
  have := congrArg (cohomologyOverFieldZeroLinearIso ℂ (ι ≫ sX) _).inv h1
  rwa [map_zero, Iso.hom_inv_id_apply] at this

/-- A rational multiple of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_smul' {D : QDivisor X} (h : D.IsQCartier) (t : ℚ) :
    (t • D).IsQCartier := by
  obtain ⟨m, hm, D', hD', hc⟩ := h
  refine ⟨m * t.den, mul_ne_zero hm (by exact_mod_cast t.den_pos.ne'), t.num • D', ?_,
    hc.zsmul _⟩
  rw [map_zsmul, hD', ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ,
    ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul]
  congr 1
  push_cast
  rw [mul_assoc, Rat.den_mul_eq_num]
  ring

/-- An ample Cartier divisor is nef: it has positive degree on every proper curve. -/
private theorem isNef_of_isAmple {D : Divisor X} (hD : D.IsCartier) (h : D.IsAmple hD) :
    D.IsNef ℂ sX := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  refine ⟨hD, fun C i _ _ _ hC => ?_⟩
  have h' : Scheme.Modules.IsAmple X D.divisorialSheaf :=
    (Stacks.AmpleBridge.isAmple_iff_isAmple X _).1 h
  exact (invertibleCurveDegree_pullback_pos_of_isAmple_of_isAffineHom ℂ (i ≫ sX) hC i _ h').le

/-- **Positive multiples of ample divisors are ample**: `pD ≡ D + (p - 1) D` with `D` nef. -/
private theorem isAmple_nsmul_of_isAmple (hX : MMP.Mori.IsProjectiveVariety ℂ sX) {D : Divisor X}
    (hD : D.IsCartier) (h : D.IsAmple hD) {p : ℕ} (hp : 0 < p) : (p • D).IsAmple (hD.nsmul p) := by
  haveI := hX
  have hN := isNef_smul_toQDivisor sX (isNef_of_isAmple sX hD h) (t := ((p - 1 : ℕ) : ℚ))
    (by positivity)
  refine MMP.Mori.QDivisor.isAmple_of_numericallyEquivalent_add_of_isNef sX
    ⟨1, one_pos, D, by simp, hD, h⟩ hN (MMP.Mori.QDivisor.NumericallyEquivalent.refl
      ((QDivisor.isQCartier_toQDivisor hD).add hN.1)) 1 one_pos (p • D) ?_ (hD.nsmul p)
  rw [map_nsmul, Nat.cast_one, one_smul, ← Nat.cast_smul_eq_nsmul ℚ]
  have : (p : ℚ) = 1 + ((p - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hp, Nat.cast_one]; ring
  rw [this, add_smul, one_smul]

/-- Ampleness of a Cartier divisor depends only on its linear equivalence class. -/
private theorem isAmple_of_linearlyEquivalent' {D D' : Divisor X} (hD : D.IsCartier)
    (h : D.IsAmple hD) (hD' : D'.IsCartier) (he : D'.LinearlyEquivalent D) : D'.IsAmple hD' := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  haveI := hD'.isInvertibleModule_divisorialSheaf
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ he.divisorialSheafIso).2 h

/-- **A positive multiple of an ample `ℚ`-divisor, moved by a principal `ℚ`-divisor, is
ample.** -/
private theorem isAmple_smul_add_principal (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {A : QDivisor X} (hA : A.IsAmple) {s : ℚ} (hs : 0 < s) (t : ℚ)
    (φ : (MMP.Mori.RationalFunctions X)ˣ) :
    (s • A + t • Divisor.toQDivisor (MMP.Mori.principalDivisor φ)).IsAmple := by
  obtain ⟨m, hm, D, hD, hDc, hDamp⟩ := hA
  have hsn : 0 < s.num := Rat.num_pos.mpr hs
  set j : ℕ := s.num.toNat * t.den
  set P := MMP.Mori.principalDivisor φ
  set D' : Divisor X := j • D + ((m : ℤ) * s.den * t.num) • P
  have hD'c : D'.IsCartier :=
    (hDc.nsmul j).add ((MMP.Mori.Divisor.isCartier_principalDivisor φ).zsmul _)
  refine ⟨m * s.den * t.den, by positivity, D', ?_, hD'c, ?_⟩
  · have h1 : ((s.num.toNat : ℕ) : ℚ) = s.den * s := by
      rw [Rat.den_mul_eq_num]; exact_mod_cast Int.toNat_of_nonneg hsn.le
    have h2 : (((m : ℤ) * s.den * t.num : ℤ) : ℚ) = m * s.den * (t.den * t) := by
      rw [Rat.den_mul_eq_num]; push_cast; ring
    simp only [D', j, map_add, map_nsmul, map_zsmul, hD]
    rw [← Int.cast_smul_eq_zsmul ℚ, h2, ← Nat.cast_smul_eq_nsmul ℚ]
    push_cast
    rw [h1]
    module
  · have hj : 0 < j := Nat.mul_pos (by omega) t.den_pos
    refine isAmple_of_linearlyEquivalent' (hDc.nsmul j) (isAmple_nsmul_of_isAmple sX hX hDc hDamp hj)
      hD'c ?_
    rw [MMP.Mori.Divisor.linearlyEquivalent_iff_sub_mem_range]
    simp only [D', add_sub_cancel_left]
    exact AddSubgroup.zsmul_mem _ (AddMonoidHom.mem_range.mpr ⟨Additive.ofMul φ, rfl⟩) _

/-- The realization of an integral multiple `c · 1 · D` of a Cartier divisor is `c D`. -/
private theorem realization_eq_zsmul {Y : Scheme.{0}} (D : Y.CartierDivisor)
    (N : MMP.Mori.KCartierDivisor ℚ Y) {z : ℤ}
    (hN : N = (z : ℚ) • MMP.Mori.KCartierDivisor.ofCartier ℚ D) (h : ∀ E, ∃ n : ℤ, N E = n) :
    MMP.Mori.KCartierDivisor.realization N h = z • D := by
  classical
  subst hN
  unfold MMP.Mori.KCartierDivisor.realization
  have hval : ((z : ℚ) • MMP.Mori.KCartierDivisor.ofCartier ℚ D) D = z := by
    simp [MMP.Mori.KCartierDivisor.ofCartier]
  by_cases hz : z = 0
  · have hsupp : ((z : ℚ) • MMP.Mori.KCartierDivisor.ofCartier ℚ D).support = ∅ := by
      subst hz; simp
    rw [Finsupp.sum, hsupp, Finset.sum_empty, hz, zero_smul]
  · have hz' : (z : ℚ) ≠ 0 := by exact_mod_cast hz
    have hsupp : ((z : ℚ) • MMP.Mori.KCartierDivisor.ofCartier ℚ D).support = {D} := by
      simp [MMP.Mori.KCartierDivisor.ofCartier, Finsupp.smul_single, hz']
    rw [Finsupp.sum, hsupp, Finset.sum_singleton]
    congr 1
    have h2 : ((Classical.choose (h D) : ℤ) : ℚ) = z := (Classical.choose_spec (h D)).symm.trans hval
    exact_mod_cast h2

/-- **Curves in the centre.** If `L` is not numerically trivial on `W`, then `W` has positive
dimension, and the restriction of `L` to `W` is nef and not numerically trivial on the curves of
`W`. -/
private theorem centre_curve_data (hX : MMP.Mori.IsProjectiveVariety ℂ sX) {L : Divisor X}
    (hL : L.IsNef ℂ sX) (W : IrreducibleCloseds X) (hntriv : ¬ IsNumTrivialOn sX hL.1 (W : Set X)) :
    ∃ d : ℕ, 0 < d ∧ topologicalKrullDim
        (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme = d ∧
      MMP.Mori.IsNef ℂ (centreι W ≫ sX)
        (MMP.CartierDivisor.sheaf (restrictDivisor (centreι W) hL.1)) ∧
      ¬ ∀ (C : Scheme.{0}) (i : C ⟶ _) [IsClosedImmersion i] [IsIntegral C]
        [IsProper (i ≫ centreι W ≫ sX)] (hC : topologicalKrullDim C = 1),
        MMP.Mori.degreeOn ℂ (centreι W ≫ sX) i hC.le
          (MMP.CartierDivisor.sheaf (restrictDivisor (centreι W) hL.1)) = 0 := by
  haveI := isProjectiveVariety_centre sX hX W
  have hWp' : AlgebraicGeometry.IsProjectiveVariety ℂ (centreι W ≫ sX) := ‹_›
  haveI := hWp'.toIsVariety
  -- a curve of `X` inside `W` on which `L` has nonzero degree
  have hcurve : ∃ (C : Scheme.{0}) (i : C ⟶ X) (_ : IsClosedImmersion i) (_ : IsIntegral C)
      (_ : IsProper (i ≫ sX)) (hC : topologicalKrullDim C = 1),
      Set.range i ⊆ (W : Set X) ∧ L.degreeOn ℂ sX i hC.le hL.1 ≠ 0 := by
    by_contra h
    refine hntriv fun C i _ _ _ hC hsub => ?_
    by_contra h'
    exact h ⟨C, i, ‹_›, ‹_›, ‹_›, hC, hsub, h'⟩
  obtain ⟨C, i, _, _, _, hC, hsub, hdeg⟩ := hcurve
  -- it lifts to `W`
  have hker : (centreι W).ker ≤ i.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono
      (closure_minimal hsub W.isClosed)
  set i' := IsClosedImmersion.lift (centreι W) i hker
  have hi' : i' ≫ centreι W = i := IsClosedImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion (i' ≫ centreι W) := by rw [hi']; infer_instance
  haveI : IsClosedImmersion i' := IsClosedImmersion.of_comp_isClosedImmersion i' (centreι W)
  haveI : IsProper ((i' ≫ centreι W) ≫ sX) := by rw [hi']; infer_instance
  haveI : IsProper (i' ≫ centreι W ≫ sX) := by rw [← Category.assoc]; infer_instance
  obtain ⟨d, hd⟩ := AlgebraicGeometry.exists_topologicalKrullDim_eq_natCast_of_isVariety ℂ
    (centreι W ≫ sX)
  refine ⟨d, ?_, hd, ?_, ?_⟩
  · have hle := i'.isClosedEmbedding.isInducing.topologicalKrullDim_le
    rw [hC, hd] at hle
    by_contra h0
    push Not at h0
    interval_cases d
    exact absurd hle (by decide)
  · intro C' j _ _ _ hC'
    haveI : IsProper ((j ≫ centreι W) ≫ sX) := by rw [Category.assoc]; infer_instance
    rw [degreeOn_sheaf_restrictDivisor sX W hL.1 j hC'.le]
    exact hL.2 C' (j ≫ centreι W) hC'
  · intro h
    apply hdeg
    have := h C i' hC
    rw [degreeOn_sheaf_restrictDivisor sX W hL.1 i' hC.le] at this
    rw [← this]
    have key : ∀ (i₁ i₂ : C ⟶ X) (_ : i₁ = i₂) [IsProper (i₁ ≫ sX)] [IsProper (i₂ ≫ sX)],
        L.degreeOn ℂ sX i₁ hC.le hL.1 = L.degreeOn ℂ sX i₂ hC.le hL.1 := by
      intro i₁ i₂ h _ _
      subst h
      rfl
    exact key _ _ hi'.symm

section Expansion

variable {Z : Scheme.{0}} (f : Z ⟶ Spec (.of ℂ)) [IsProper f] {d : ℕ}
  (hd : topologicalKrullDim Z ≤ d)

attribute [local instance] AlgebraicGeometry.isInvertible_update

/-- **Additivity in one slot** of `(A + jB)`: `(⋯ (A + jB) ⋯) = (⋯ A ⋯) + j (⋯ B ⋯)`. -/
private theorem intersectionNumber_update_lineBundle_add_nsmul (F : Fin d → Z.Modules)
    [∀ q, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 (F q)] (s : Fin d)
    (A B : Z.CartierDivisor) (j : ℕ) :
    AlgebraicGeometry.intersectionNumber ℂ f (𝟙 Z) d hd
        (Function.update F s (MMP.CartierDivisor.sheaf (A + j • B))) =
      AlgebraicGeometry.intersectionNumber ℂ f (𝟙 Z) d hd
          (Function.update F s (MMP.CartierDivisor.sheaf A)) +
        j * AlgebraicGeometry.intersectionNumber ℂ f (𝟙 Z) d hd
          (Function.update F s (MMP.CartierDivisor.sheaf B)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    refine (AlgebraicGeometry.intersectionNumber_tensor ℂ f (𝟙 Z) d hd s _
      (Function.update F s (MMP.CartierDivisor.sheaf (A + j • B)))
      (Function.update F s (MMP.CartierDivisor.sheaf B))
      (fun q hq => by rw [Function.update_of_ne hq, Function.update_of_ne hq])
      (fun q hq => by rw [Function.update_of_ne hq, Function.update_of_ne hq]) ?_).trans ?_
    · exact eqToIso (by rw [Function.update_self]; congr 1; rw [succ_nsmul, add_assoc]) ≪≫
        (MMP.CartierDivisorSheaf.sheafMulIso (A + j • B) B).symm ≪≫
        eqToIso (by rw [Function.update_self, Function.update_self]; rfl)
    · rw [ih]
      push_cast
      ring

/-- The intersection number depends only on the family (with any invertibility proofs). -/
private theorem intersectionNumber_congr_family (F F' : Fin d → Z.Modules)
    [∀ q, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 (F q)]
    [∀ q, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 (F' q)] (h : F = F') :
    AlgebraicGeometry.intersectionNumber ℂ f (𝟙 Z) d hd F =
      AlgebraicGeometry.intersectionNumber ℂ f (𝟙 Z) d hd F' := by
  subst h; rfl

/-- The family whose first `m` slots follow `J` (`0 ↦ B`, `1 ↦ A`) and whose other slots are
`A + jB`. -/
private noncomputable def prefixFamily (A B : Z.CartierDivisor) (j : ℕ) {m : ℕ}
    (J : Fin m → Fin 2) : Fin d → Z.Modules := fun t =>
  if h : t.val < m then ![MMP.CartierDivisor.sheaf B, MMP.CartierDivisor.sheaf A] (J ⟨t, h⟩)
  else MMP.CartierDivisor.sheaf (A + j • B)

private theorem isInvertible_prefixFamily (A B : Z.CartierDivisor) (j : ℕ) {m : ℕ}
    (J : Fin m → Fin 2) (t : Fin d) :
    SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 (prefixFamily A B j J t) := by
  unfold prefixFamily
  split_ifs
  · generalize J _ = b
    fin_cases b
    · exact (inferInstance : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
        (MMP.CartierDivisor.sheaf B))
    · exact (inferInstance : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
        (MMP.CartierDivisor.sheaf A))
  · infer_instance

attribute [local instance] isInvertible_prefixFamily

/-- **The expansion of `((A + jB)^d)` along the first `m` slots.** -/
private theorem intersectionNumber_eq_sum_prefixFamily (A B : Z.CartierDivisor) (j : ℕ) :
    ∀ m : ℕ, m ≤ d → AlgebraicGeometry.intersectionNumber ℂ f (𝟙 Z) d hd
        (fun _ => MMP.CartierDivisor.sheaf (A + j • B)) =
      ∑ J : Fin m → Fin 2, (∏ t, (![(j : ℤ), 1] (J t))) *
        AlgebraicGeometry.intersectionNumber ℂ f (𝟙 Z) d hd (prefixFamily A B j J) := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    exact intersectionNumber_congr_family f hd _ _ (funext fun t => by simp [prefixFamily])
  | succ m ih =>
    intro hm
    rw [ih (by omega)]
    have hslot : ∀ J : Fin m → Fin 2, AlgebraicGeometry.intersectionNumber ℂ f (𝟙 Z) d hd
        (prefixFamily A B j J) = ∑ b : Fin 2, (![(j : ℤ), 1] b) *
          AlgebraicGeometry.intersectionNumber ℂ f (𝟙 Z) d hd
            (prefixFamily A B j (Fin.snoc J b)) := by
      intro J
      set s : Fin d := ⟨m, by omega⟩
      have h1 : prefixFamily A B j J = Function.update (prefixFamily A B j J) s
          (MMP.CartierDivisor.sheaf (A + j • B)) := by
        funext t
        by_cases ht : t = s
        · subst ht; simp [prefixFamily, s]
        · rw [Function.update_of_ne ht]
      have h2 : ∀ b : Fin 2, prefixFamily A B j (Fin.snoc J b) = Function.update
          (prefixFamily A B j J) s
          (![MMP.CartierDivisor.sheaf B, MMP.CartierDivisor.sheaf A] b) := by
        intro b
        funext t
        by_cases ht : t = s
        · subst ht
          simp [prefixFamily, s, Fin.snoc]
        · rw [Function.update_of_ne ht]
          have ht' : t.val ≠ m := fun h => ht (Fin.ext h)
          unfold prefixFamily
          by_cases hlt : t.val < m
          · rw [dif_pos (by omega), dif_pos hlt]
            simp [Fin.snoc, hlt]
          · rw [dif_neg (by omega), dif_neg hlt]
      have h20 : prefixFamily A B j (Fin.snoc J 0) = Function.update
          (prefixFamily A B j J) s (MMP.CartierDivisor.sheaf B) := h2 0
      have h21 : prefixFamily A B j (Fin.snoc J 1) = Function.update
          (prefixFamily A B j J) s (MMP.CartierDivisor.sheaf A) := h2 1
      rw [Fin.sum_univ_two, intersectionNumber_congr_family f hd _ _ h20,
        intersectionNumber_congr_family f hd _ _ h21, intersectionNumber_congr_family f hd _ _ h1,
        intersectionNumber_update_lineBundle_add_nsmul]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      ring
    simp_rw [hslot, Finset.mul_sum]
    rw [← Finset.sum_product']
    refine Fintype.sum_equiv ((Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ => Fin 2)) _ _
      fun ⟨J, b⟩ => ?_
    show _ = (∏ t, (![(j : ℤ), 1] (Fin.snoc (α := fun _ => Fin 2) J b t))) *
      AlgebraicGeometry.intersectionNumber ℂ f (𝟙 Z) d hd (prefixFamily A B j (Fin.snoc J b))
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring

/-- **The multilinear expansion of a self-intersection**: `((A + jB)^d)` is the combination
`∑_J ∏ c_J (L_{J_1} ⋯ L_{J_d})` with `L = (𝒪(B), 𝒪(A))` and `c = (j, 1)`. -/
private theorem sheafSelfIntersectionNumber_add_nsmul (A B : Z.CartierDivisor) (j : ℕ) :
    haveI : ∀ i, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
        (![MMP.CartierDivisor.sheaf B, MMP.CartierDivisor.sheaf A] i) := by
      intro i
      fin_cases i
      · exact (inferInstance : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
          (MMP.CartierDivisor.sheaf B))
      · exact (inferInstance : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
          (MMP.CartierDivisor.sheaf A))
    haveI : ∀ i : Fin 0, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
        ((![] : Fin 0 → Z.Modules) i) := fun i => i.elim0
    (MMP.Mori.sheafSelfIntersectionNumber ℂ f (𝟙 Z) d hd
        (MMP.CartierDivisor.sheaf (A + j • B)) : ℝ) =
      MMP.Mori.sheafCombinationIntersectionNumber ℂ f (𝟙 Z) ℝ ![(j : ℝ), 1]
        ![MMP.CartierDivisor.sheaf B, MMP.CartierDivisor.sheaf A] d ![]
        (by simpa using hd) := by
  unfold MMP.Mori.sheafSelfIntersectionNumber MMP.Mori.sheafCombinationIntersectionNumber
  rw [MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    intersectionNumber_eq_sum_prefixFamily f hd A B j d le_rfl]
  push_cast
  refine Finset.sum_congr rfl fun J _ => ?_
  congr 1
  · refine Finset.prod_congr rfl fun t _ => ?_
    generalize J t = b
    fin_cases b <;> simp
  · haveI hJ : ∀ t, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
        ((fun t => ![MMP.CartierDivisor.sheaf B, MMP.CartierDivisor.sheaf A] (J t)) t) := by
      intro t
      beta_reduce
      generalize J t = b
      fin_cases b
      · exact (inferInstance : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
          (MMP.CartierDivisor.sheaf B))
      · exact (inferInstance : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
          (MMP.CartierDivisor.sheaf A))
    haveI h0 : ∀ i : Fin 0, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
        ((![] : Fin 0 → Z.Modules) i) := fun i => i.elim0
    have hinst := MMP.Mori.isInvertible_finAppend
      (fun t => ![MMP.CartierDivisor.sheaf B, MMP.CartierDivisor.sheaf A] (J t))
      (![] : Fin 0 → Z.Modules)
    refine congrArg _ (Eq.trans ?_
      (@MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber ℂ _ Z Z f _ (𝟙 Z) _ (d + 0)
        (by simpa using hd) (Fin.append (fun t =>
          ![MMP.CartierDivisor.sheaf B, MMP.CartierDivisor.sheaf A] (J t)) ![])
        hinst).symm)
    refine @intersectionNumber_congr_family Z f _ d hd _ _ (isInvertible_prefixFamily A B j J)
      hinst (funext fun t => ?_)
    show _ = Fin.append _ _ (Fin.castAdd 0 t)
    rw [Fin.append_left]
    unfold prefixFamily
    rw [dif_pos t.isLt]

end Expansion

/-- **Large volume** (the volume lemma). If `L|_W` is nef and not numerically trivial, then for an
ample Cartier `D₀` and every bound `c`, `(D₀ + jL)|_W` has self-intersection larger than `c` for
some `j ≥ c`. -/
private theorem exists_large_volume (hX : MMP.Mori.IsProjectiveVariety ℂ sX) {L : Divisor X}
    (hL : L.IsNef ℂ sX) (W : IrreducibleCloseds X) {D₀ : Divisor X} (hD₀c : D₀.IsCartier)
    (hD₀ : D₀.IsAmple hD₀c) {d : ℕ} (hd0 : 0 < d)
    (hd : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme = d)
    (hnef : MMP.Mori.IsNef ℂ (centreι W ≫ sX)
        (MMP.CartierDivisor.sheaf (restrictDivisor (centreι W) hL.1)))
    (hnt : ¬ ∀ (C : Scheme.{0}) (i : C ⟶ _) [IsClosedImmersion i] [IsIntegral C]
        [IsProper (i ≫ centreι W ≫ sX)] (hC : topologicalKrullDim C = 1),
        MMP.Mori.degreeOn ℂ (centreι W ≫ sX) i hC.le
          (MMP.CartierDivisor.sheaf (restrictDivisor (centreι W) hL.1)) = 0)
    (c : ℕ) :
    ∃ j : ℕ, c ≤ j ∧ ((c : ℤ) < MMP.Mori.sheafSelfIntersectionNumber ℂ (centreι W ≫ sX) (𝟙 _) d
      hd.le (MMP.CartierDivisor.sheaf
        (restrictDivisor (centreι W) hD₀c + j • restrictDivisor (centreι W) hL.1))) := by
  haveI := isProjectiveVariety_centre sX hX W
  have hWp' : AlgebraicGeometry.IsProjectiveVariety ℂ (centreι W ≫ sX) := ‹_›
  haveI : IsProper (centreι W ≫ sX) :=
    (IsProjectiveMorphism.isProjective hWp'.isProjective).isProper
  have hM := (Stacks.RelativeVeryAmple.isAmple_congr _ _
    (Iso.refl (MMP.CartierDivisor.sheaf (restrictDivisor (centreι W) hD₀c)))).2
    (isAmple_sheaf_restrictDivisor hD₀c hD₀ W)
  have hnef' : MMP.Mori.IsNef ℂ (centreι W ≫ sX)
      (MMP.CartierDivisor.sheaf (restrictDivisor (centreι W) hL.1)) := by
    intro C i _ _ _ hC
    rw [MMP.Mori.degreeOn_eq_of_iso ℂ _ i hC.le
      (Iso.refl (MMP.CartierDivisor.sheaf (restrictDivisor (centreι W) hL.1)))]
    exact hnef C i hC
  have hnt' : ¬ ∀ (C : Scheme.{0}) (i : C ⟶ _) [IsClosedImmersion i] [IsIntegral C]
      [IsProper (i ≫ centreι W ≫ sX)] (hC : topologicalKrullDim C = 1),
      MMP.Mori.degreeOn ℂ (centreι W ≫ sX) i hC.le
        (MMP.CartierDivisor.sheaf (restrictDivisor (centreι W) hL.1)) = 0 := by
    intro h
    refine hnt fun C i _ _ _ hC => ?_
    rw [← MMP.Mori.degreeOn_eq_of_iso ℂ _ i hC.le
      (Iso.refl (MMP.CartierDivisor.sheaf (restrictDivisor (centreι W) hL.1)))]
    exact h C i hC
  have ht := MMP.Mori.tendsto_sheafCombinationIntersectionNumber_atTop_of_isNef ℂ
    (centreι W ≫ sX) ‹_› hd hd0 _ _ hM hnef' hnt' one_pos
  obtain ⟨T, hT⟩ := Filter.tendsto_atTop_atTop.mp ht ((c : ℝ) + 1)
  refine ⟨max c ⌈T⌉₊, le_max_left _ _, ?_⟩
  have h1 := hT ((max c ⌈T⌉₊ : ℕ) : ℝ)
    (le_trans (Nat.le_ceil T) (by exact_mod_cast le_max_right _ _))
  have h2 := sheafSelfIntersectionNumber_add_nsmul (centreι W ≫ sX) hd.le
    (restrictDivisor (centreι W) hD₀c) (restrictDivisor (centreι W) hL.1) (max c ⌈T⌉₊)
  have : ((c : ℤ) : ℝ) < (MMP.Mori.sheafSelfIntersectionNumber ℂ (centreι W ≫ sX) (𝟙 _) d
      hd.le (MMP.CartierDivisor.sheaf (restrictDivisor (centreι W) hD₀c +
        (max c ⌈T⌉₊) • restrictDivisor (centreι W) hL.1)) : ℝ) := by
    have h3 := lt_of_lt_of_le (show ((c : ℤ) : ℝ) < (c : ℝ) + 1 by push_cast; linarith) h1
    rw [h2]
    convert h3 using 2
  exact_mod_cast this

/-- **A general smooth closed point of the centre** in a given open set meeting it. -/
private theorem exists_good_point (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (W : IrreducibleCloseds X)
    (V : X.Opens) (hV : ((W : Set X) ∩ V).Nonempty) :
    ∃ x : (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme,
      centreι W x ∈ V ∧ IsClosed ({centreι W x} : Set X) ∧ IsClosed ({x} : Set _) ∧
      x ∈ MMP.Mori.smoothLocus (centreι W ≫ sX) ∧
      IsRegularLocalRing (X.presheaf.stalk (centreι W x) ⧸
        (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).stalkIdeal
          (centreι W x)) := by
  haveI := isProjectiveVariety_centre sX hX W
  have hWp' : AlgebraicGeometry.IsProjectiveVariety ℂ (centreι W ≫ sX) := ‹_›
  haveI := hWp'.toIsVariety
  set O := centreι W ⁻¹ᵁ V ⊓ MMP.Mori.smoothLocus (centreι W ≫ sX)
  have hO : (O : Set (Scheme.IdealSheafData.vanishingIdeal
      ⟨(W : Set X), W.isClosed⟩).subscheme).Nonempty := by
    refine ⟨genericPoint _, ?_, ?_⟩
    · obtain ⟨y, hyW, hyV⟩ := hV
      rw [← range_centreι W] at hyW
      obtain ⟨z, rfl⟩ := hyW
      exact ((genericPoint_spec _).mem_open_set_iff (centreι W ⁻¹ᵁ V).isOpen).mpr
        ⟨z, trivial, hyV⟩
    · rw [MMP.Mori.smoothLocus_eq_smoothLocus]
      exact (centreι W ≫ sX).genericPoint_mem_smoothLocus_of_perfectField
  haveI : JacobsonSpace (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme :=
    LocallyOfFiniteType.jacobsonSpace (centreι W ≫ sX)
  obtain ⟨x, hxO, hxc⟩ := nonempty_inter_closedPoints hO O.isOpen.isLocallyClosed
  have hxcl : IsClosed ({x} : Set _) := hxc
  refine ⟨x, hxO.1, ?_, hxcl, hxO.2, ?_⟩
  · have := (centreι W).isClosedEmbedding.isClosedMap _ hxcl
    rwa [Set.image_singleton] at this
  · obtain ⟨U, hxU, hU⟩ := MMP.Mori.mem_smoothLocus_iff.mp hxO.2
    have : Smooth (U.ι ≫ centreι W ≫ sX) := hU
    have h1 := isRegularLocalRing_stalk_of_smooth_over_field (U.ι ≫ centreι W ≫ sX) ⟨x, hxU⟩
    have h2 : IsRegularLocalRing ((Scheme.IdealSheafData.vanishingIdeal
        ⟨(W : Set X), W.isClosed⟩).subscheme.presheaf.stalk x) :=
      IsRegularLocalRing.of_ringEquiv (U.stalkIso ⟨x, hxU⟩).commRingCatIsoToRingEquiv
    exact IsRegularLocalRing.of_ringEquiv
      (Scheme.IdealSheafData.subschemeStalkRingEquiv _ x).symm

/-- Positive multiples of effective Cartier divisors are effective. -/
private theorem isEffective_nsmul_of_pos {Y : Scheme.{0}} {D : Y.CartierDivisor}
    (hD : MMP.Intersection.IsEffective D) {n : ℕ} (hn : 1 ≤ n) :
    MMP.Intersection.IsEffective (n • D) := by
  induction n, hn using Nat.le_induction with
  | base => simpa using hD
  | succ n _ ih => rw [succ_nsmul]; exact ih.add hD

/-- A local equation of `nD`, `n ≥ 1`, is the `n`-th power of a local equation of `D`. -/
private theorem isLocalEquationAt_nsmul_of_pos {Y : Scheme.{0}} {D : Y.CartierDivisor} {y : Y}
    {f : Y.totalQuotientSheaf.presheaf.stalk y} (h : MMP.Intersection.IsLocalEquationAt D y f)
    {n : ℕ} (hn : 1 ≤ n) : MMP.Intersection.IsLocalEquationAt (n • D) y (f ^ n) := by
  induction n, hn using Nat.le_induction with
  | base => simpa using h
  | succ n _ ih => rw [succ_nsmul, pow_succ]; exact ih.add h

open MMP.Intersection Opposite in
/-- The stalk at `x` of the zero scheme of the canonical section of an effective Cartier
divisor is generated by a local equation at `x`. -/
private theorem stalk_zeroScheme_canonicalSection' {Y : Scheme.{0}} (D : Y.CartierDivisor)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      (MMP.CartierDivisor.sheaf D)]
    (hD : MMP.Intersection.IsEffective D) (x : Y) (g : Y.presheaf.stalk x)
    (hg : MMP.Intersection.IsLocalEquationAt D x (MMP.Intersection.stalkToTotalQuotient x g)) :
    IdealSheafData.stalk (Stacks.Divisors.zeroScheme Y (MMP.CartierDivisor.sheaf D)
      (MMP.CartierDivisor.canonicalSection D hD)) x = Ideal.span {g} := by
  obtain ⟨U, hxU, s, hs, hsD⟩ := hD x
  obtain ⟨W, hWa, hxW, hWU⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) hxU
  let i : W ⟶ U := homOfLE hWU
  let W' : Y.affineOpens := ⟨W, hWa⟩
  have hg' := isLocalEquationOn_resUnit i hsD
  let r : Γ(Y, W'.1) := Y.presheaf.map i.op s
  have hr : ((resUnit i hs.unit : (Y.totalQuotientSheaf.obj.obj (op W'.1))ˣ) : _) =
      toTotalQuotient W'.1 r := (toTotalQuotient_map i s).symm
  have hbij := MMP.CartierDivisor.isTrivializingGenerator_invSection hg' W'.1 le_rfl
  have hid : (MMP.CartierDivisor.sheaf D).presheaf.map (homOfLE (le_refl W'.1)).op
      (MMP.CartierDivisor.invSection hg') =
      MMP.CartierDivisor.invSection hg' := by
    apply MMP.CartierDivisorSheaf.sectionVal_injective
    erw [MMP.CartierDivisorSheaf.sectionVal_map]
    change Y.totalQuotientSheaf.obj.map (𝟙 _) _ = _
    rw [CategoryTheory.Functor.map_id]; rfl
  rw [hid] at hbij
  let e := (LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(Y, W'.1) _
    (MMP.CartierDivisor.invSection hg')) hbij).symm
  have he : e ((MMP.CartierDivisor.sheaf D).presheaf.map (homOfLE le_top).op
      (MMP.CartierDivisor.canonicalSection D hD)) = r := by
    rw [LinearEquiv.symm_apply_eq]
    apply MMP.CartierDivisorSheaf.sectionVal_injective
    change _ = MMP.CartierDivisorSheaf.sectionVal (r • MMP.CartierDivisor.invSection hg')
    erw [MMP.CartierDivisor.sectionVal_smul,
        MMP.CartierDivisor.sectionVal_canonicalSection_res,
      ← hr]
    exact (Units.mul_inv _).symm
  rw [Stacks.Divisors.stalk_zeroScheme_eq_span_germ _ _ W' e r he x hxW]
  obtain ⟨a, ha, hfa⟩ := IsLocalEquationOn.exists_isUnit_eq_mul_germ hg' hxW hg
  rw [hr, germ_toTotalQuotient, ← map_mul] at hfa
  rw [stalkToTotalQuotient_injective x hfa, Ideal.span_singleton_mul_left_unit ha]

/-- A local equation of the zero divisor of a section whose germ generates the zero scheme. -/
private theorem exists_isLocalEquation_stalk_zeroScheme {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {M : Divisor X} (hM : M.IsCartier) (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) (y : X) :
    haveI := hM.isInvertibleModule_divisorialSheaf
    ∃ U : X.Opens, y ∈ U ∧ ∃ φ : (MMP.Mori.RationalFunctions X)ˣ,
      (M.zeroDivisor σ hσ).IsLocalEquation U φ ∧ ∃ g : X.presheaf.stalk y,
        (∀ (Z : irreducibleComponents X) (hZ : y ∈ Z.1),
          (φ : MMP.Mori.RationalFunctions X) Z = (MMP.Mori.stalkToRationalFunctions X hZ).hom g) ∧
        IdealSheafData.stalk (Stacks.Divisors.zeroScheme X M.divisorialSheaf σ) y =
          Ideal.span {g} := by
  haveI := hM.isInvertibleModule_divisorialSheaf
  obtain ⟨V, hyV, a, ha, hideal, hcoeff⟩ :=
    MMP.Mori.exists_affine_zeroScheme_ideal_eq_span M hM σ hσ y
  refine ⟨V, hyV, MMP.Threefold.Resolution.sectionUnit a ha, ?_,
    (X.presheaf.germ (V : X.Opens) y hyV).hom a, ?_, ?_⟩
  · rintro E ⟨z, hzE, hzV⟩
    have hsp : E.genericPoint ⤳ z := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hzE
    exact hcoeff E (hsp.mem_open (V : X.Opens).isOpen hzV)
  · intro Z hZ
    have hsp := (MMP.Mori.isGenericPoint_componentGenericPoint X Z).specializes hZ
    have hZV : MMP.Mori.componentGenericPoint X Z ∈ (V : X.Opens) :=
      hsp.mem_open (V : X.Opens).isOpen hyV
    rw [MMP.Threefold.Resolution.sectionUnit_apply a ha Z hZV]
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hyV hsp a).symm
  · change IdealSheafData.stalk (Stacks.Divisors.zeroScheme X M.divisorialSheaf σ) y = _
    rw [IdealSheafData.stalk_eq_map_germ _ y V hyV]
    erw [hideal]
    rw [Ideal.map_span, Set.image_singleton]

/-- An element of the local ring at a point of a closed subscheme whose image lies in `𝔪^e`
lies in `𝔪^e` plus the stalk of the ideal. -/
private theorem mem_pow_sup_of_stalkMap_mem {X : Scheme.{0}} (I : X.IdealSheafData)
    (z : I.subscheme) {e : ℕ} (h : X.presheaf.stalk (I.subschemeι z))
    (hh : (I.subschemeι.stalkMap z).hom h ∈ IsLocalRing.maximalIdeal _ ^ e) :
    h ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (I.subschemeι z)) ^ e ⊔
      I.stalkIdeal (I.subschemeι z) := by
  set φ := (I.subschemeι.stalkMap z).hom
  have hsurj : Function.Surjective φ := I.subschemeι.stalkMap_surjective z
  have hmax : (IsLocalRing.maximalIdeal _).map φ = IsLocalRing.maximalIdeal _ :=
    IsLocalRing.map_maximalIdeal_of_surjective φ hsurj
  rw [← hmax, ← Ideal.map_pow] at hh
  obtain ⟨h', hh', hφ⟩ := (Ideal.mem_map_iff_of_surjective φ hsurj).1 hh
  have hker : h - h' ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_sub, hφ, sub_self]
  rw [Stacks.Chow.ker_stalkMap_subschemeι_eq_stalk,
    ← Scheme.IdealSheafData.stalkIdeal_eq_stalk] at hker
  have := Submodule.add_mem_sup hh' hker
  rwa [add_sub_cancel] at this

/-- **The concentrated local equation of a lift.** -/
private theorem exists_concentrated_core {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (I : X.IdealSheafData) {M : Divisor X} (hM : M.IsCartier)
    {DW : I.subscheme.CartierDivisor} (hDW : MMP.Intersection.IsEffective DW)
    (Φ : MMP.CartierDivisor.sheaf DW ≅
      (Scheme.Modules.pullback I.subschemeι).obj M.divisorialSheaf)
    (x : I.subscheme) {e : ℕ} (a : I.subscheme.presheaf.stalk x)
    (ha : a ∈ IsLocalRing.maximalIdeal _ ^ e)
    (hloc : MMP.Intersection.IsLocalEquationAt DW x (MMP.Intersection.stalkToTotalQuotient x a))
    (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) (r : Γ(I.subscheme, ⊤)) (hr : IsUnit r)
    (h : AlgebraicGeometry.pullbackGlobalSections I.subschemeι M.divisorialSheaf σ =
      r • Φ.hom.app ⊤ (MMP.CartierDivisor.canonicalSection DW hDW)) :
    ∃ U : X.Opens, I.subschemeι x ∈ U ∧ ∃ φ : (MMP.Mori.RationalFunctions X)ˣ,
      (M.zeroDivisor σ hσ).IsLocalEquation U φ ∧ ∃ g : X.presheaf.stalk (I.subschemeι x),
        (∀ (Z : irreducibleComponents X) (hZ : I.subschemeι x ∈ Z.1),
          (φ : MMP.Mori.RationalFunctions X) Z = (MMP.Mori.stalkToRationalFunctions X hZ).hom g) ∧
        g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (I.subschemeι x)) ^ e ⊔
          I.stalkIdeal (I.subschemeι x) := by
  haveI := hM.isInvertibleModule_divisorialSheaf
  haveI hinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      M.divisorialSheaf := hM.isInvertibleModule_divisorialSheaf
  obtain ⟨U, hyU, φ, hφ, g, hg, hstalk⟩ :=
    exists_isLocalEquation_stalk_zeroScheme hM σ hσ (I.subschemeι x)
  refine ⟨U, hyU, φ, hφ, g, hg, mem_pow_sup_of_stalkMap_mem I x g ?_⟩
  have h1 : (I.subschemeι.stalkMap x).hom g ∈ IdealSheafData.stalk
      ((Stacks.Divisors.zeroScheme X M.divisorialSheaf σ).comap I.subschemeι) x :=
    (AlgebraicGeometry.IdealSheafData.stalk_comap _ _ x).ge
      (Ideal.mem_map_of_mem _ (by rw [hstalk]; exact Ideal.mem_span_singleton_self g))
  have h1' : (I.subschemeι.stalkMap x).hom g ∈ IdealSheafData.stalk
      (Stacks.Divisors.zeroScheme I.subscheme
        ((Scheme.Modules.pullback I.subschemeι).obj M.divisorialSheaf)
        (AlgebraicGeometry.pullbackGlobalSections I.subschemeι M.divisorialSheaf σ)) x := by
    erw [Stacks.Divisors.zeroScheme_pullback]
    exact h1
  rw [h] at h1'
  clear h1
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible I.subscheme.sheaf.obj
      I.subscheme.ringCatSheaf.property (MMP.CartierDivisor.sheaf DW) :=
    MMP.CartierDivisor.isInvertibleModule_sheaf DW
  have e2 : Stacks.Divisors.zeroScheme I.subscheme
      ((Scheme.Modules.pullback I.subschemeι).obj M.divisorialSheaf)
      (Φ.hom.app ⊤ (MMP.CartierDivisor.canonicalSection DW hDW)) =
      Stacks.Divisors.zeroScheme I.subscheme (MMP.CartierDivisor.sheaf DW)
        (MMP.CartierDivisor.canonicalSection DW hDW) :=
    (AlgebraicGeometry.zeroScheme_eq_of_iso Φ rfl).symm
  erw [Stacks.Divisors.zeroScheme_smul_of_isUnit _ _ hr, e2,
    stalk_zeroScheme_canonicalSection' DW hDW x a hloc] at h1'
  exact (Ideal.span_singleton_le_iff_mem _).2 ha h1'

/-- The local-equation condition of the concentration lemma: `H` has a local equation at `y`
whose germ lies in `𝔪_y^N + ℐ_W`. -/
private def HasConcentratedEquation (W : IrreducibleCloseds X) (H : Divisor X) (y : X) (N : ℕ) :
    Prop :=
  ∃ U : X.Opens, y ∈ U ∧ ∃ φ : (MMP.Mori.RationalFunctions X)ˣ,
    H.IsLocalEquation U φ ∧ ∃ g : X.presheaf.stalk y,
      (∀ (Z : irreducibleComponents X) (hZ : y ∈ Z.1),
        (φ : MMP.Mori.RationalFunctions X) Z = (MMP.Mori.stalkToRationalFunctions X hZ).hom g) ∧
      g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) ^ N ⊔
        (Scheme.IdealSheafData.vanishingIdeal ⟨W, W.isClosed⟩).stalkIdeal y

/-- `𝒪_X(nM) ≅ 𝒪_X(M)^{⊗ n}` for a Cartier divisor `M` and `n ≥ 1`. -/
private theorem nonempty_divisorialSheaf_nsmul_iso_tensorPowModule {M : Divisor X}
    (hM : M.IsCartier) {n : ℕ} (hn : 1 ≤ n) :
    haveI := hM.isInvertibleModule_divisorialSheaf
    Nonempty ((n • M).divisorialSheaf ≅
      Stacks.Ample.tensorPowModule X M.divisorialSheaf (n : ℤ)) := by
  haveI := hM.isInvertibleModule_divisorialSheaf
  obtain ⟨C, ⟨e⟩⟩ := MMP.Mori.exists_sheaf_iso_divisorialSheaf hM
  obtain ⟨en⟩ := MMP.Mori.nonempty_divisorialSheaf_nsmul_iso hM e n hn
  obtain ⟨el⟩ := MMP.Fourfold.nonempty_lineBundle_nat_smul_iso C n
  exact ⟨en ≪≫ el ≪≫
    Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso X _ _
      e.symm n⟩

/-- **Sections vanishing on the centre, free off it** (Serre). For an ample Cartier `M` and all
large `s`, finitely many sections of `𝒪_X(sM)` vanishing on `W` have no common zero off `W`. -/
private theorem eventually_exists_sections_free_off_centre (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {M : Divisor X} (hMc : M.IsCartier) (hM : M.IsAmple hMc) (W : IrreducibleCloseds X) :
    ∀ᶠ s : ℕ in atTop, ∃ (r : ℕ) (τ : Fin r → (s • M).divisorialSubmodule ⊤),
      (∀ i, AlgebraicGeometry.pullbackGlobalSections (centreι W) (s • M).divisorialSheaf
        (τ i) = 0) ∧
      ∀ y : X, y ∉ (W : Set X) → ∃ (i : Fin r) (hi : τ i ≠ 0),
        y ∉ ((s • M).zeroDivisor (τ i) hi).supp := by
  haveI := hMc.isInvertibleModule_divisorialSheaf
  have hX' : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI : IsProper sX := (IsProjectiveMorphism.isProjective hX'.isProjective).isProper
  set I := Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩ with hI
  obtain ⟨n₀, hn₀⟩ := Stacks.SectionsVanishingOnSubscheme.exists_bound_generatesOffSupport ℂ sX I
    M.divisorialSheaf hM
  rw [Filter.eventually_atTop]
  refine ⟨max n₀.toNat 1, fun s hs => ?_⟩
  have hs1 : 1 ≤ s := le_of_max_le_right hs
  have hgen := hn₀ (s : ℤ) (by omega)
  obtain ⟨e⟩ := nonempty_divisorialSheaf_nsmul_iso_tensorPowModule hMc hs1
  haveI := (hMc.nsmul s).isInvertibleModule_divisorialSheaf
  set V := Stacks.SectionsVanishingOnSubscheme.vanishingSections ℂ sX I M.divisorialSheaf (s : ℤ)
  let t : V → Γ(Stacks.Ample.tensorPowModule X M.divisorialSheaf (s : ℤ), ⊤) := fun v =>
    ((v : Stacks.Bertini.globalSections ℂ sX
      (Stacks.Ample.tensorPowModule X M.divisorialSheaf (s : ℤ))) :
        Γ(Stacks.Ample.tensorPowModule X M.divisorialSheaf (s : ℤ), ⊤))
  let σ : V → (s • M).divisorialSubmodule ⊤ := fun v => e.inv.app ⊤ (t v)
  have hnv : ∀ v, Stacks.Ample.nonvanishingLocus (s • M).divisorialSheaf (σ v) =
      Stacks.Ample.nonvanishingLocus _ (t v) := fun v =>
    Stacks.CokernelSupport.nonvanishingLocus_iso_app e.symm (t v)
  have hsupp : (I.support : Set X) = W := by
    rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have hW : ∀ v, ∀ x ∈ (W : Set X), x ∉ Stacks.Ample.nonvanishingLocus _ (t v) := by
    intro v x hx h
    refine h (Stacks.SectionsVanishingOnSubscheme.Γgerm_mem_maximalSmul_of_mem_vanishingSections
      ℂ sX I M.divisorialSheaf _ x ?_ v)
    show x ∈ (I.support : Set X)
    rw [hsupp]
    exact hx
  have hcover : ∀ y : X, y ∉ (W : Set X) → ∃ v, y ∈ Stacks.Ample.nonvanishingLocus _ (t v) := by
    intro y hy
    have hy' : y ∈ I.support.compl := by
      show y ∈ ((I.support : Set X)ᶜ)
      rw [hsupp]
      exact hy
    obtain ⟨v, hv⟩ := Stacks.StalkwiseGeneration.exists_mem_nvOpen_of_span_eq_top _ t y (hgen y hy')
    refine ⟨v, fun h => ?_⟩
    exact ((Stacks.Chow.BertiniChain.notMem_nvOpen_iff _ _ _).2 h) hv
  have hpull : ∀ v, AlgebraicGeometry.pullbackGlobalSections I.subschemeι
      (s • M).divisorialSheaf (σ v) = 0 := by
    intro v
    have h0 : AlgebraicGeometry.pullbackGlobalSections I.subschemeι _ (t v) = 0 :=
      (Stacks.SectionsVanishingOnSubscheme.mem_vanishingSections_iff ℂ sX I M.divisorialSheaf
        _ _).1 v.2
    show AlgebraicGeometry.pullbackGlobalSections _ _ (e.inv.app ⊤ (t v)) = 0
    rw [AlgebraicGeometry.pullbackGlobalSections_natural, h0, map_zero]
  haveI : IsNoetherian X := {}
  have hK : IsCompact ((W : Set X)ᶜ) := NoetherianSpace.isCompact _
  let U : V → Set X := fun v => Stacks.Ample.nonvanishingLocus _ (t v)
  have hU : ∀ v, IsOpen (U v) := fun v =>
    Stacks.NonvanishingOpen.isOpen_nonvanishingLocus _ _ (t v)
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover U hU (fun y hy => Set.mem_iUnion.2 (hcover y hy))
  refine ⟨F.card, fun i => σ (F.equivFin.symm i), fun i => hpull _, fun y hy => ?_⟩
  obtain ⟨v, hvF, hyv⟩ := Set.mem_iUnion₂.1 (hF hy)
  have hyσ : y ∈ Stacks.Ample.nonvanishingLocus (s • M).divisorialSheaf (σ v) := by
    rw [hnv]; exact hyv
  set i := F.equivFin ⟨v, hvF⟩
  have hi' : ((F.equivFin.symm i : F) : V) = v := by simp [i]
  have h1 : σ ((F.equivFin.symm i : F) : V) ≠ 0 := by
    rw [hi']
    intro h0
    rw [h0] at hyσ
    exact (Set.ext_iff.1 (Stacks.Ample.nonvanishingLocus_zero (s • M).divisorialSheaf) y).1 hyσ
  refine ⟨i, h1, ?_⟩
  have hmem : y ∈ Stacks.Ample.nonvanishingLocus (s • M).divisorialSheaf
      (σ ((F.equivFin.symm i : F) : V)) := by
    rw [hi']; exact hyσ
  rw [MMP.Mori.Divisor.nonvanishingLocus_eq_compl_supp_zeroDivisor (hMc.nsmul s) _ h1] at hmem
  exact hmem

/-- **Lifting a concentrated divisor of the centre.** If `D_W` is an effective Cartier divisor on
the minimal lc centre `W` with `D_W ∼ C` and `C ≈ M|_W`, `M - (K_X + B)` ample, with a local
equation at `x` in `𝔪_x^e`, then some section `σ₀` of `𝒪_X(M)` restricts to a nonzero section of
`M|_W`, and every section whose restriction to `W` is a nonzero multiple of that of `σ₀` has a
local equation at `x` in `𝔪_x^e + ℐ_W` (as do sums with sections vanishing on `W`). -/
private theorem exists_lift_concentrated (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : IsLogCanonicalPair sX B) {W : IrreducibleCloseds X}
    (hW : IsMinimalLcCentre sX B W) {M : Divisor X} (hMc : M.IsCartier)
    (hgap : (Divisor.toQDivisor M - (Divisor.toQDivisor K + B)).IsAmple)
    {DW : (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme.CartierDivisor}
    (hDW : MMP.Intersection.IsEffective DW)
    {C : (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme.CartierDivisor}
    (hC : CLinEquiv (restrictDivisor (centreι W) hMc) C)
    (hlin : MMP.Intersection.LinearlyEquivalent DW C)
    (x : (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme) {e : ℕ}
    (a : (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme.presheaf.stalk x)
    (ha : a ∈ IsLocalRing.maximalIdeal _ ^ e)
    (hloc : MMP.Intersection.IsLocalEquationAt DW x (MMP.Intersection.stalkToTotalQuotient x a)) :
    ∃ σ₀ : M.divisorialSubmodule ⊤,
      AlgebraicGeometry.pullbackGlobalSections (centreι W) M.divisorialSheaf σ₀ ≠ 0 ∧
      ∀ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) (c : ℂ),
        AlgebraicGeometry.pullbackGlobalSections (centreι W) M.divisorialSheaf σ ≠ 0 →
        AlgebraicGeometry.pullbackGlobalSections (centreι W) M.divisorialSheaf σ =
          AlgebraicGeometry.pullbackGlobalSections (centreι W) M.divisorialSheaf
            (MMP.Mori.scalarsToGlobalSections ℂ sX c • σ₀) →
        HasConcentratedEquation W (M.zeroDivisor σ hσ) (centreι W x) e := by
  haveI := hX
  set ι := centreι W
  haveI := hMc.isInvertibleModule_divisorialSheaf
  -- `𝒪_W(D_W) ≅ ι^*𝒪_X(M)`
  obtain ⟨e1⟩ := (cLinEquiv_iff _ _).1 hC
  obtain ⟨e0⟩ := nonempty_iso_restrictDivisor ι hMc
  obtain ⟨u, hu⟩ := MMP.Intersection.mem_principalSubgroup_iff.1 hlin
  have hDWC : DW = C + MMP.Intersection.principalDivisor u := by rw [hu]; abel
  let Φ : MMP.CartierDivisor.sheaf DW ≅ (Scheme.Modules.pullback ι).obj M.divisorialSheaf :=
    eqToIso (congrArg MMP.CartierDivisor.sheaf hDWC) ≪≫
      (MMP.CartierDivisor.sheafAddPrincipalIso C u).symm ≪≫
      e1.symm ≪≫ e0.symm
  set τ₀ := Φ.hom.app ⊤ (MMP.CartierDivisor.canonicalSection DW hDW)
  -- the lift of `τ₀`
  obtain ⟨σ₀, hpull₀⟩ := exists_pullbackGlobalSections_eq sX hX hK hB hW.1 hMc hgap τ₀
  have hτ₀ : τ₀ ≠ 0 := by
    intro h0
    have hcan : MMP.CartierDivisor.canonicalSection DW hDW = 0 := by
      have := congrArg (Φ.inv.app ⊤) h0
      rwa [Scheme.Modules.app_inv_app, map_zero] at this
    have h1 := congrArg MMP.CartierDivisorSheaf.sectionVal hcan
    rw [MMP.CartierDivisor.sectionVal_canonicalSection] at h1
    haveI := MMP.Threefold.Resolution.nontrivial_totalQuotient
      (C := (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme)
      (V := ⊤) trivial
    exact one_ne_zero (α := ((Scheme.IdealSheafData.vanishingIdeal
      ⟨(W : Set X), W.isClosed⟩).subscheme.totalQuotientSheaf.obj.obj (Opposite.op ⊤)))
      (h1.trans rfl)
  refine ⟨σ₀, hpull₀ ▸ hτ₀, fun σ hσ c hσW0 hσW => ?_⟩
  erw [MMP.Chow.DeterminantCurveForm.pullbackGlobalSections_smul, hpull₀] at hσW
  have hc : c ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero, zero_smul] at hσW
    exact hσW0 hσW
  have hr : IsUnit (ι.appTop (MMP.Mori.scalarsToGlobalSections ℂ sX c)) :=
    ((isUnit_iff_ne_zero.2 hc).map _).map _
  exact exists_concentrated_core _ hMc hDW Φ x a ha hloc σ hσ _ hr hσW

section GeneralMemberLc

open MMP.Mori MMP.Resolution

universe u

section Hironaka

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

variable {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- The support of the reduced divisor on a finite set of prime divisors is that set. -/
private theorem support_sum_single (s : Finset (MMP.Mori.PrimeDivisor Y)) :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor Y).support = s := by
  classical
  ext E
  simp [Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- A prime divisor whose generic point lies on finitely many prime divisors is one of them. -/
private theorem mem_of_genericPoint_mem_iUnion {Y : Scheme.{u}}
    {s : Finset (MMP.Mori.PrimeDivisor Y)} {C : Set Y}
    (hs : (⋃ E ∈ s, (E.support : Set Y)) = C) {F : MMP.Mori.PrimeDivisor Y}
    (hF : F.genericPoint ∈ C) : F ∈ s := by
  rw [← hs] at hF
  obtain ⟨E, hE, hgen⟩ := Set.mem_iUnion₂.mp hF
  rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen] at hE

/-- The exceptional prime divisors of a log resolution are finitely many. -/
private theorem exists_finset_isExceptional {D : RDivisor X} {Y : Scheme.{u}} {f : Y ⟶ X}
    (hf : MMP.Mori.IsLogResolution sX D f) :
    ∃ Ex : Finset (MMP.Mori.PrimeDivisor Y),
      ∀ F : MMP.Mori.PrimeDivisor Y, F ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap F := by
  classical
  have hmem : ∀ F : MMP.Mori.PrimeDivisor Y, RationalMap.IsExceptional f.toRationalMap F →
      F.genericPoint ∈ ((exceptionalSet f ⊔ D.supp.preimage f.continuous : Closeds Y) : Set Y) :=
    fun F hF => Or.inl (MMP.Positivity.support_subset_exceptionalSet F hF
      (MMP.Flips.primeDivisor_genericPoint_mem_support F))
  rcases hf.isSNCSubset with h0 | ⟨s, hs, -⟩
  · refine ⟨∅, fun F => ⟨fun h => absurd h (Finset.notMem_empty _), fun hF => ?_⟩⟩
    have := hmem F hF
    rw [h0] at this
    exact absurd this (by simp)
  · refine ⟨s.filter (fun F => RationalMap.IsExceptional f.toRationalMap F), fun F => ?_⟩
    rw [Finset.mem_filter]
    refine ⟨fun h => h.2, fun hF => ⟨?_, hF⟩⟩
    exact mem_of_genericPoint_mem_iUnion hs (hmem F hF)

end Hironaka

/-! ### Proper birational morphisms over prime divisors -/

section CodimOne

/-- Two points of `X` over the generic point of a prime divisor `Q` of the normal scheme `Y` are
equal, for `f : X ⟶ Y` separated, dominant and birational. -/
private theorem eq_of_map_eq_genericPoint {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsSeparated f] [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) (Q : MMP.Mori.PrimeDivisor Y) {x₁ x₂ : X}
    (h₁ : f x₁ = Q.genericPoint) (h₂ : f x₂ = Q.genericPoint) : x₁ = x₂ := by
  have := Q.isDiscreteValuationRing_localRing
  haveI : ValuationRing (Y.presheaf.stalk (f x₁)) := by rw [h₁]; infer_instance
  haveI : ValuationRing (Y.presheaf.stalk (f x₂)) := by rw [h₂]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x₁
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x₂
  exact MMP.Positivity.eq_of_isIso_stalkMap f hf (h₂.trans h₁.symm)

/-- A proper birational morphism onto a normal integral scheme is an isomorphism over every point
with finite fibre. -/
private theorem mem_biregularLocus_of_finite {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    [IsNormal Z] (f : X ⟶ Z) [IsProper f] (hb : IsBirationalMorphism f) {z : Z}
    (hz : (f ⁻¹' {z}).Finite) : z ∈ biregularLocus f := by
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)).1 inferInstance
  exact le_biregularLocus (V := ⟨_, hU⟩) hiso hz

/-- A proper birational morphism onto a normal integral scheme is an isomorphism over the generic
point of every prime divisor. -/
private theorem genericPoint_mem_biregularLocus {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsProper f]
    (hf : IsBirationalMorphism f) (P : MMP.Mori.PrimeDivisor Y) :
    P.genericPoint ∈ biregularLocus f :=
  haveI := hf.isDominant
  mem_biregularLocus_of_finite f hf (Set.Subsingleton.finite fun _ ha _ hb =>
    eq_of_map_eq_genericPoint f hf.functionFieldMap_bijective P ha hb)

variable {k : Type u} [Field k] [PerfectField k] {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W]

/-- **A non-exceptional prime divisor of a proper birational model is a strict transform.** If
`F` is a prime divisor of `W` which is not exceptional over `X`, then `π` maps the generic point
of `F` to that of a prime divisor `P` of `X`, `F = π⁻¹_* P`, and the discrepancy of `F` over a
pair `(X, Δ)` is `-coeff_P Δ`. -/
private theorem exists_inverseTransformPrimeDivisor_eq_some {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (hP : IsPairWith sX n K Δ) {π : W ⟶ X} [IsProper π]
    (hW : IsNormalVariety k (π ≫ sX)) (hbir : IsBirationalMorphism π)
    (F : MMP.Mori.PrimeDivisor W) (hF : ¬ RationalMap.IsExceptional π.toRationalMap F) :
    ∃ P : MMP.Mori.PrimeDivisor X, π F.genericPoint = P.genericPoint ∧
      inverseTransformPrimeDivisor π P = some F ∧
      IsDiscrepancy sX n K Δ ⟨W, π, hW, hbir, F⟩ (-Δ.coeff P) := by
  obtain ⟨P, hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hP
    ⟨W, π, hW, hbir, F⟩ hF
  have hη : π F.genericPoint = P.genericPoint := by
    rw [DivisorOver.center_eq_closure_genericPoint,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hc
    exact (inseparable_iff_closure_eq.2 hc).eq
  refine ⟨P, hη, ?_, hd⟩
  exact MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hη
    (hη ▸ genericPoint_mem_biregularLocus π hbir P)

/-- The coefficient of `π⁻¹_* B` along `π⁻¹_* P` is the coefficient of `B` along `P`. -/
private theorem coeff_inverseTransformDivisor_of_eq_some {R : Type*} [AddCommMonoid R]
    {g : W ⟶ X} {P : MMP.Mori.PrimeDivisor X} {F : MMP.Mori.PrimeDivisor W}
    (hP : inverseTransformPrimeDivisor g P = some F) (B : DivisorWithCoeffs R X) :
    (inverseTransformDivisor g B).coeff F = B.coeff P :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hP (fun _ hP' =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hP').1.symm.trans
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hP).1) B

/-- A strict transform `π⁻¹_* P` of a component `P` of `B` is a component of `π⁻¹_* B`. -/
private theorem mem_support_inverseTransformDivisor {π : W ⟶ X} {B : QDivisor X}
    {P : MMP.Mori.PrimeDivisor X} {F : MMP.Mori.PrimeDivisor W}
    (hinv : inverseTransformPrimeDivisor π P = some F) (hP : B.coeff P ≠ 0) :
    F ∈ (inverseTransformDivisor π B).support := by
  rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply,
    coeff_inverseTransformDivisor_of_eq_some hinv]
  exact hP

open Classical in
/-- **The snc boundary of a log resolution.** The snc divisor `Ex(π) ∪ π⁻¹ Supp B` of a log
resolution `π` of `(X, B)` is the union of finitely many prime divisors, each a component of
`π⁻¹_* B` or exceptional. -/
private theorem exists_finset_subset_support_union {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hPW : IsPairWith sX n K B) {π : W ⟶ X} [IsProper π] (hπ : MMP.Fourfold.IsLogResolution sX B π)
    (hW : IsNormalVariety k (π ≫ sX)) (hbir : IsBirationalMorphism π)
    (Ex : Finset (MMP.Mori.PrimeDivisor W))
    (hEx : ∀ F : MMP.Mori.PrimeDivisor W, F ∈ Ex ↔ RationalMap.IsExceptional π.toRationalMap F) :
    ∃ s : Finset (MMP.Mori.PrimeDivisor W), (⋃ E ∈ s, (E.support : Set W)) =
      ((exceptionalSet π ⊔ (QDivisor.toRDivisor B).supp.preimage π.continuous : Closeds W) :
        Set W) ∧ s ⊆ (inverseTransformDivisor π B).support ∪ Ex := by
  rcases hπ.isSNCSubset with h0 | ⟨s, hs, -⟩
  · exact ⟨∅, by rw [h0]; simp, Finset.empty_subset _⟩
  refine ⟨s, hs, fun E hE => ?_⟩
  by_cases hEE : E ∈ Ex
  · exact Finset.mem_union_right _ hEE
  obtain ⟨P, hη, hinv, -⟩ :=
    exists_inverseTransformPrimeDivisor_eq_some hPW hW hbir E (fun h => hEE ((hEx E).mpr h))
  refine Finset.mem_union_left _ (mem_support_inverseTransformDivisor hinv ?_)
  have hmem : E.genericPoint ∈ ((exceptionalSet π ⊔
      (QDivisor.toRDivisor B).supp.preimage π.continuous : Closeds W) : Set W) := by
    rw [← hs]
    exact Set.mem_iUnion₂.mpr ⟨E, hE, MMP.Flips.primeDivisor_genericPoint_mem_support E⟩
  rcases hmem with hx | hx
  · exfalso
    rw [SetLike.mem_coe, mem_exceptionalSet, hη] at hx
    exact hx (genericPoint_mem_biregularLocus π hbir P)
  · change π E.genericPoint ∈ (QDivisor.toRDivisor B).supp at hx
    rw [QDivisor.supp_toRDivisor, hη, DivisorWithCoeffs.mem_supp_iff] at hx
    obtain ⟨Q, hQ, hPQ⟩ := hx
    obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hPQ
    exact hQ

end CodimOne

/-! ### Rescaling an integral divisor -/

section InvSmul

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {r : ℕ}

/-- An integral divisor `D` is `r • (D / r)`. -/
private theorem toQDivisor_eq_zsmul_inv_smul (hr : r ≠ 0) (D : Divisor X) :
    Divisor.toQDivisor D = (r : ℤ) • ((r : ℚ)⁻¹ • Divisor.toQDivisor D) := by
  rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hr), one_smul]

private theorem coeff_inv_smul_toQDivisor (D : Divisor X) (P : MMP.Mori.PrimeDivisor X) :
    ((r : ℚ)⁻¹ • Divisor.toQDivisor D).coeff P = (r : ℚ)⁻¹ * D.coeff P := by
  rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, smul_eq_mul]

/-- `D / r` is `ℚ`-Cartier for a Cartier divisor `D`. -/
private theorem isQCartier_inv_smul_toQDivisor (hr : r ≠ 0) {D : Divisor X} (hD : D.IsCartier) :
    ((r : ℚ)⁻¹ • Divisor.toQDivisor D).IsQCartier :=
  ⟨r, by exact_mod_cast hr, ⟨D, toQDivisor_eq_zsmul_inv_smul hr D, hD⟩⟩

private theorem inv_smul_toQDivisor_nonneg {D : Divisor X} (hD : 0 ≤ D) :
    0 ≤ (r : ℚ)⁻¹ • Divisor.toQDivisor D := fun P => by
  change (0 : ℚ) ≤ DivisorWithCoeffs.coeff ((r : ℚ)⁻¹ • Divisor.toQDivisor D) P
  rw [coeff_inv_smul_toQDivisor]
  have : (0 : ℚ) ≤ D.coeff P := by exact_mod_cast hD P
  positivity

/-- For `B ≥ 0` and `D ≥ 0`, the support of `B + D / r` is the union of the supports. -/
private theorem mem_supp_add_inv_smul_iff {B : QDivisor X} (hB : ∀ P, 0 ≤ B.coeff P)
    {D : Divisor X} (hD : 0 ≤ D) (hr : r ≠ 0) (x : X) :
    x ∈ (QDivisor.toRDivisor (B + (r : ℚ)⁻¹ • Divisor.toQDivisor D)).supp ↔
      x ∈ D.supp ∨ x ∈ (QDivisor.toRDivisor B).supp := by
  have hc : ∀ P, (B + (r : ℚ)⁻¹ • Divisor.toQDivisor D).coeff P ≠ 0 ↔
      D.coeff P ≠ 0 ∨ B.coeff P ≠ 0 := fun P => by
    have : (0 : ℚ) ≤ D.coeff P := by exact_mod_cast hD P
    rw [DivisorWithCoeffs.coeff_add, coeff_inv_smul_toQDivisor, ne_eq,
      add_eq_zero_iff_of_nonneg (hB P) (by positivity)]
    simp [hr]
    tauto
  simp only [QDivisor.supp_toRDivisor, DivisorWithCoeffs.mem_supp_iff, hc, or_and_right,
    exists_or]

end InvSmul

/-! ### Adding a general member to an lc pair -/

section LogCanonical

variable {k : Type u} [Field k] {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

open Classical in
/-- The coefficient of the reduced divisor `∑_{E ∈ S} E` at `F` is `1` or `0`. -/
private theorem coeff_sum_single {Y : Scheme.{u}} (S : Finset (MMP.Mori.PrimeDivisor Y))
    (F : MMP.Mori.PrimeDivisor Y) :
    DivisorWithCoeffs.coeff (∑ E ∈ S, Finsupp.single E (1 : ℤ) : Divisor Y) F =
      if F ∈ S then 1 else 0 := by
  change (∑ E ∈ S, Finsupp.single E (1 : ℤ)) F = _
  rw [Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply]

open Classical in
/-- **A general member keeps a pair log canonical** (Kollár–Mori, proof of 5.17). Let `(X, B)` be
an lc pair, `π : W ⟶ X` a log resolution of `(X, B)` with exceptional prime divisors `Ex`, and
`G` an effective Cartier divisor whose pull-back `H' = π^*G` is such that
`H' + ∑ π⁻¹_* B_j + ∑ E_i` is a reduced snc divisor. Then `(X, B + G / r)` is lc for every
integer `r > 0`. -/
private theorem isLogCanonicalPair_add_inv_smul [IsLocallyNoetherian W] [IsNormal W]
    {B : QDivisor X} (hBp : MMP.Fourfold.IsPair sX B)
    (hB : MMP.Intersection.IsLogCanonicalPair sX B) {π : W ⟶ X}
    (hπ : MMP.Fourfold.IsLogResolution sX B π) (Ex : Finset (MMP.Mori.PrimeDivisor W))
    (hEx : ∀ F : MMP.Mori.PrimeDivisor W, F ∈ Ex ↔ RationalMap.IsExceptional π.toRationalMap F)
    {G : Divisor X} (hG0 : 0 ≤ G) (hGc : G.IsCartier)
    {hBG : ∀ Z : irreducibleComponents W, π (componentGenericPoint W Z) ∉ G.supp}
    {H' : Divisor W} (hH' : G.IsPullback π hBG H')
    (hcoef : ∀ F : MMP.Mori.PrimeDivisor W,
      (H' + ∑ F ∈ (inverseTransformDivisor π B).support ∪ Ex,
        Finsupp.single F (1 : ℤ)).coeff F = 0 ∨
      (H' + ∑ F ∈ (inverseTransformDivisor π B).support ∪ Ex,
        Finsupp.single F (1 : ℤ)).coeff F = 1)
    (hsnc : DivisorWithCoeffs.IsSNC (π ≫ sX)
      (H' + ∑ F ∈ (inverseTransformDivisor π B).support ∪ Ex, Finsupp.single F (1 : ℤ)))
    {r : ℕ} (hr : 0 < r) :
    MMP.Intersection.IsLogCanonicalPair sX (B + (r : ℚ)⁻¹ • Divisor.toQDivisor G) := by
  haveI : IsAlgClosed k := hBp.isAlgClosed
  haveI : CharZero k := hBp.charZero
  obtain ⟨hXn, n, K, hK, hKq⟩ := hB.1
  have hPW : IsPairWith sX n K B := ⟨hXn, hK, hKq⟩
  set A : QDivisor X := (r : ℚ)⁻¹ • Divisor.toQDivisor G
  have hAq : A.IsQCartier := isQCartier_inv_smul_toQDivisor hr.ne' hGc
  -- the log resolution and its source
  have hbir : IsBirationalMorphism π := hπ.isBirationalMorphism
  have hW : IsNormalVariety k (π ≫ sX) :=
    (hπ.toIsSmoothResolution.isNormalVariety hXn).1
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsDominant π := hbir.isDominant
  haveI : IsProper π := hπ.toIsSmoothResolution.isProper
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace π
  -- the crepant boundary of `(X, B)` and the pull-back of `A`
  obtain ⟨BW, hBW, -⟩ := (MMP.Mori.IsPair.existsUnique_isCrepantBoundary hB.1 hK π hW hbir).1
  have hle1 : ∀ F, BW.coeff F ≤ 1 :=
    (MMP.Fourfold.isLogCanonicalPair_iff_forall_coeff_le_one sX hBp hπ hW hBW).mp hB
  have hBA : ∀ Z : irreducibleComponents W, π (componentGenericPoint W Z) ∉ A.supp := by
    intro Z
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
    exact MMP.Fourfold.genericPoint_notMem_supp A
  set B' := A.pullback hAq hBA with hB'def
  have hB' : A.IsPullback π hBA B' := QDivisor.isPullback_pullback hAq hBA
  have hB'H : ∀ F, B'.coeff F = (r : ℚ)⁻¹ * H'.coeff F := by
    obtain ⟨D', hD', hpD'⟩ := hB' r hr G (toQDivisor_eq_zsmul_inv_smul hr.ne' G) hGc
    obtain rfl := hpD'.eq hGc hH'
    intro F
    have := congrArg (fun E : QDivisor W => E.coeff F) hD'
    simp only [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, Divisor.coeff_toQDivisor] at this
    rw [this]
    push_cast
    field_simp
  -- the crepant boundary of `(X, B + A)`
  have hBW' : IsCrepantBoundary sX n K (B + A) π hW hbir (BW + B') := by
    intro F
    obtain ⟨-, hB'', hiff⟩ := IsPairWith.isDiscrepancy_add_smul_iff hPW hAq ⟨W, π, hW, hbir, F⟩
    have h := ((hiff B' hB').1 (-BW.coeff F)).mpr (hBW F)
    convert h using 1
    rw [DivisorWithCoeffs.coeff_add]
    ring
  -- `(X, B + A)` is a pair
  have hpairBA : MMP.Fourfold.IsPair sX (B + A) := by
    refine ⟨hBp.isAlgClosed, hBp.charZero, ⟨hXn, n, K, hK, add_assoc _ B A ▸ hKq.add hAq⟩,
      fun P => ?_⟩
    rw [DivisorWithCoeffs.coeff_add]
    exact add_nonneg (hBp.nonneg P) (inv_smul_toQDivisor_nonneg hG0 P)
  set S₀ := (inverseTransformDivisor π B).support ∪ Ex with hS₀
  -- the coefficients of `H'`
  have hH'0 : ∀ F, 0 ≤ H'.coeff F := fun F =>
    MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (V := ⊤) hGc (fun P _ => hG0 P) hH'
      F ⟨F.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support F, trivial⟩
  have hH'01 : ∀ F, H'.coeff F = 0 ∨ (H'.coeff F = 1 ∧ F ∉ S₀) := by
    intro F
    have h := hcoef F
    rw [DivisorWithCoeffs.coeff_add, coeff_sum_single] at h
    have h0 := hH'0 F
    split_ifs at h with hF
    · left; omega
    · rcases h with h | h
      · left; omega
      · right; exact ⟨by omega, hF⟩
  -- off the snc boundary, the crepant boundary of `(X, B)` vanishes
  have hzero : ∀ F, F ∉ S₀ → BW.coeff F = 0 := by
    intro F hF
    obtain ⟨P, -, hinv, hd⟩ := exists_inverseTransformPrimeDivisor_eq_some hPW hW hbir F
      fun h => hF (Finset.mem_union_right _ ((hEx F).mpr h))
    rw [show BW.coeff F = B.coeff P by linarith [(hBW F).eq hd]]
    by_contra hP
    exact hF (Finset.mem_union_left _ (mem_support_inverseTransformDivisor hinv hP))
  -- `π` is a log resolution of `(X, B + A)`
  obtain ⟨s, hs, hsS₀⟩ := exists_finset_subset_support_union hPW hπ hW hbir Ex hEx
  have hsuppH' : (H'.supp : Set W) = π ⁻¹' (G.supp : Set X) :=
    MMP.Flips.supp_eq_preimage_supp_of_isPullback hGc hG0 hH'
  have hSNCsub : IsSNCSubset (π ≫ sX)
      (exceptionalSet π ⊔ (QDivisor.toRDivisor (B + A)).supp.preimage π.continuous) := by
    refine Or.inr ⟨H'.support ∪ s, ?_, ?_⟩
    · rw [Finset.set_biUnion_union, hs, ← DivisorWithCoeffs.coe_supp, hsuppH']
      ext x
      simp only [Closeds.coe_sup, Set.mem_union, Set.mem_preimage, SetLike.mem_coe]
      change π x ∈ G.supp ∨ x ∈ exceptionalSet π ∨ π x ∈ (QDivisor.toRDivisor B).supp ↔
        x ∈ exceptionalSet π ∨ π x ∈ (QDivisor.toRDivisor (B + A)).supp
      rw [mem_supp_add_inv_smul_iff hBp.nonneg hG0 hr.ne']
      tauto
    · refine hsnc.of_support_subset ?_
      rw [support_sum_single]
      intro F hF
      rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply,
        DivisorWithCoeffs.coeff_add, coeff_sum_single]
      rcases Finset.mem_union.mp hF with hF | hF
      · have hF' : H'.coeff F ≠ 0 := by
          rwa [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply] at hF
        rcases hH'01 F with h | ⟨h, hFS⟩
        · exact absurd h hF'
        · rw [if_neg hFS, h]; norm_num
      · rw [if_pos (hsS₀ hF)]
        have := hH'0 F
        omega
  have hπ' : MMP.Fourfold.IsLogResolution sX (B + A) π :=
    ⟨⟨hπ.toIsSmoothResolution, hπ.isPureCodimOne_exceptionalSet, hSNCsub⟩,
      hπ.isProjectiveMorphism⟩
  refine (MMP.Fourfold.isLogCanonicalPair_iff_forall_coeff_le_one sX hpairBA hπ' hW hBW').mpr fun F => ?_
  rw [DivisorWithCoeffs.coeff_add, hB'H]
  rcases hH'01 F with h | ⟨h, hFS⟩
  · rw [h]
    simpa using hle1 F
  · rw [h, hzero F hFS]
    push_cast
    rw [zero_add, mul_one]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hr)

end LogCanonical

end GeneralMemberLc

/-- **Restricting sections to an open subscheme.** For a Cartier `M` and a dense open `U`, the
divisorial sections of `𝒪_X(M)` restrict to those of `𝒪_U(M|_U)`, compatibly with the scalars,
and the zero divisor of the restriction is the restriction of the zero divisor. -/
private theorem exists_restrict_sections {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (U : X.Opens) [Nonempty U] [IsIntegral U]
    [IsLocallyNoetherian U] [IsNormal U] [CompactSpace U] [IsDominant U.ι]
    {M : Divisor X} (hMc : M.IsCartier) :
    ∃ ρ : M.divisorialSubmodule ⊤ →+
        MMP.Mori.Divisor.divisorialSubmodule (M.restrictOpen U) ⊤,
      (∀ (r : Γ(X, ⊤)) (s : M.divisorialSubmodule ⊤), ρ (r • s) = U.ι.appTop r • ρ s) ∧
      ∀ (s : M.divisorialSubmodule ⊤) (hs : s ≠ 0), ∃ h : ρ s ≠ 0,
        MMP.Mori.Divisor.zeroDivisor (M.restrictOpen U) (ρ s) h =
          (M.zeroDivisor s hs).restrictOpen U := by
  have hM' := MMP.Flips.isPullback_restrictOpen U hMc
  refine ⟨MMP.Mori.pullSec U.ι hMc hM', fun r s => MMP.Mori.pullSec_smul U.ι hMc hM' r s,
    fun s hs => ?_⟩
  have hZc := isCartier_zeroDivisor hMc s hs
  obtain ⟨h, hpb⟩ := MMP.Mori.isPullback_zeroDivisor_pullSec U.ι hMc hM' s hs
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant U.ι _)
  exact ⟨h, hpb.eq hZc (MMP.Flips.isPullback_restrictOpen U hZc)⟩

/-- A non-exceptional divisor over a pair has discrepancy minus the coefficient of the prime
divisor of `X` with the same valuation. -/
private theorem exists_coeff_eq_of_not_isExceptional {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor Y}
    {Δ : QDivisor Y} (hP : MMP.Mori.IsPairWith sY n K Δ) {D : DivisorOver ℂ sY}
    (hD : ¬ D.IsExceptional) {a : ℚ} (ha : MMP.Mori.IsDiscrepancy sY n K Δ D a) :
    ∃ P : MMP.Mori.PrimeDivisor Y, a = -Δ.coeff P := by
  obtain ⟨P, hv⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hP.1 D hD
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hP.2.1
    (DivisorOver.ofPrimeDivisor ℂ hP.1 P)
  refine ⟨P, ?_⟩
  rw [MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hP hv ha hc]
  exact MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hP.1 hc

/-- The coefficients of the boundary of an lc pair are at most one. -/
private theorem coeff_le_one_of_isLogCanonicalPair' {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor Y}
    {Δ : QDivisor Y} (hP : MMP.Mori.IsPairWith sY n K Δ) (hlc : IsLogCanonicalPair sY Δ)
    (P : MMP.Mori.PrimeDivisor Y) : Δ.coeff P ≤ 1 := by
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hP.2.1
    (DivisorOver.ofPrimeDivisor ℂ hP.1 P)
  have h0 := hlc.2.2 n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
    (show IsProper (𝟙 Y) from inferInstance))
  rw [MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hP.1 hc] at h0
  have : ((Δ.coeff P : ℚ) : ℝ) ≤ 1 := by push_cast at h0; linarith
  exact_mod_cast this

/-- **Log canonical pairs restrict to open subschemes.** -/
private theorem isLogCanonicalPair_restrictOpen' {B : QDivisor X} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 4) (hB : IsLogCanonicalPair sX B) (U : X.Opens) [Nonempty U] :
    IsLogCanonicalPair (U.ι ≫ sX) (B.restrictOpen U) := by
  have hlc := isLcPair_of_isLogCanonicalPair hB hK
  have hPU := hlc.1.restrictOpen U
  refine ⟨hPU.isPair, fun P => hB.2.1 _, fun n' D a ha => ?_⟩
  have hn' : n' = 4 := by
    have h1 := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
    rw [hPU.2.1.topologicalKrullDim_eq] at h1
    exact_mod_cast h1.symm
  subst hn'
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPU.isPair hPU.2.1 D
  rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha]
  suffices hc1 : (-1 : ℚ) ≤ c by
    have : (-1 : ℝ) ≤ c := by exact_mod_cast hc1
    linarith
  by_cases hD : D.IsExceptional
  · obtain ⟨D₁, hE₁, -, -, hb⟩ := hlc.1.exists_isDiscrepancy_of_restrictOpen U hD hc
    have h2 := hlc.2.trans (MMP.Mori.discrep_le hE₁ hb)
    have : ((-1 : ℝ) : EReal) ≤ ((c : ℝ) : EReal) := by simpa using h2
    exact_mod_cast EReal.coe_le_coe_iff.mp this
  · obtain ⟨P, hP⟩ := exists_coeff_eq_of_not_isExceptional hPU hD hc
    rw [hP, MMP.Mori.DivisorWithCoeffs.coeff_restrictOpen]
    linarith [coeff_le_one_of_isLogCanonicalPair' hlc.1 hB
      (OpenWeilRestriction.primeDivisorMap U.ι P)]

/-- Log canonicity on an open subscheme bounds the log discrepancies of the divisors over `X`
whose centre meets it. -/
private theorem nonneg_of_isLogDiscrepancy_of_restrictOpen {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (hP : MMP.Mori.IsPairWith sX n K Δ) (U : X.Opens) [Nonempty U]
    (hlc : IsLogCanonicalPair (U.ι ≫ sX) (Δ.restrictOpen U)) {E : DivisorOver ℂ sX}
    (hE : ((E.center : Set X) ∩ U).Nonempty) {t : ℝ}
    (ht : IsLogDiscrepancy sX n (QDivisor.toRDivisor Δ) E t) : 0 ≤ t := by
  obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hP.2.1 E
  rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hb ht]
  obtain ⟨hY, hf, E', -, -, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hP E U hE
  haveI : IsProper E.f := ht.2.1
  have hb' := (hiff b).1 hb
  have hl := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hb'
    (inferInstance : IsProper (E.f ∣_ U))
  exact hlc.2.2 n _ _ hl

/-- **Bertini off a closed subset.** For an lc pair `(X, B)` and finitely many sections of a
Cartier `𝒪_X(M)` without common zero off a closed `W`, a general member `H` of their span makes
`(X, B + H/ρ)` lc outside `W` for every `ρ > 0`. -/
private theorem exists_polynomial_lc_off (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X}
    (hB : IsLogCanonicalPair sX B) (W : Set X) (hW : IsClosed W) {M : Divisor X}
    (hMc : M.IsCartier) {ι : Type} [Fintype ι] (s : ι → M.divisorialSubmodule ⊤)
    (hs : ∀ y : X, y ∉ W → ∃ (i : ι) (hi : s i ≠ 0), y ∉ (M.zeroDivisor (s i) hi).supp) :
    ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ c : ι → ℂ, MvPolynomial.eval c Q ≠ 0 →
      ∀ hσ : (∑ i, MMP.Mori.scalarsToGlobalSections ℂ sX (c i) • s i) ≠ 0,
      ∀ ρ : ℕ, 0 < ρ → ∀ (E : DivisorOver ℂ sX) (t : ℝ), ¬ (E.center : Set X) ⊆ W →
        IsLogDiscrepancy sX 4 (QDivisor.toRDivisor (B + (ρ : ℚ)⁻¹ •
          Divisor.toQDivisor (M.zeroDivisor _ hσ))) E t → 0 ≤ t := by
  classical
  by_cases hWu : W = Set.univ
  · exact ⟨1, one_ne_zero, fun c _ hσ ρ _ E t hE _ => absurd (hWu ▸ Set.subset_univ _) hE⟩
  set U : X.Opens := ⟨Wᶜ, hW.isOpen_compl⟩ with hUdef
  obtain ⟨y₀, hy₀⟩ : ∃ y, y ∉ W := by
    by_contra h
    push Not at h
    exact hWu (Set.eq_univ_iff_forall.2 h)
  haveI : Nonempty U := ⟨⟨y₀, hy₀⟩⟩
  have hXn : MMP.Mori.IsNormalVariety ℂ sX := hB.1.1
  have hUn : MMP.Mori.IsNormalVariety ℂ (U.ι ≫ sX) := hXn.restrictOpen U
  haveI : IsDominant U.ι := AlgebraicGeometry.Opens.isDominant_ι (U.isOpen.dense ⟨y₀, hy₀⟩)
  haveI : IsIntegral U := hUn.1.toIsIntegral
  haveI : IsLocallyNoetherian U := hUn.isLocallyNoetherian
  haveI : IsNormal U := hUn.2
  haveI : CompactSpace U := haveI := hUn.1.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ sX)
  -- the sections on `U`
  obtain ⟨ρU, hρs, hρz⟩ := exists_restrict_sections U hMc
  set t : ι → MMP.Mori.Divisor.divisorialSubmodule (M.restrictOpen U) ⊤ := fun i => ρU (s i)
  have ht : ∀ x : U, ∃ (i : ι) (hi : t i ≠ 0),
      x ∉ (MMP.Mori.Divisor.zeroDivisor (M.restrictOpen U) (t i) hi).supp := by
    intro x
    obtain ⟨i, hi, hx⟩ := hs (U.ι x) x.2
    obtain ⟨h, heq⟩ := hρz (s i) hi
    refine ⟨i, h, fun hmem => hx ?_⟩
    have hmem' : x ∈ ((M.zeroDivisor (s i) hi).restrictOpen U).supp := heq ▸ hmem
    obtain ⟨P, hP, hxP⟩ := MMP.Mori.DivisorWithCoeffs.mem_supp_iff.1 hmem'
    exact MMP.Mori.DivisorWithCoeffs.mem_supp_iff.2 ⟨_, hP,
      (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι P x).2 hxP⟩
  -- the pair on `U` and a log resolution of it
  set BU := B.restrictOpen U
  have hBU : IsLogCanonicalPair (U.ι ≫ sX) BU := isLogCanonicalPair_restrictOpen' sX hK hB U
  have hBUp : MMP.Fourfold.IsPair (U.ι ≫ sX) BU := ⟨inferInstance, inferInstance, hBU.1, hBU.2.1⟩
  obtain ⟨Y, π, hπ, hπp⟩ := MMP.Mori.exists_isLogResolution_isProjectiveMorphism (U.ι ≫ sX) hUn
    (QDivisor.toRDivisor BU)
  obtain ⟨Ex, hEx⟩ := exists_finset_isExceptional hπ
  have hYn : MMP.Mori.IsNormalVariety ℂ (π ≫ U.ι ≫ sX) :=
    (hπ.toIsSmoothResolution.isNormalVariety hUn).1
  haveI : IsLocallyNoetherian Y := hYn.isLocallyNoetherian
  haveI : IsNormal Y := hYn.2
  obtain ⟨Q, hQ0, hQ⟩ :=
    MMP.Mori.IsLogResolution.exists_polynomial_isSNC_pullback_zeroDivisor_add' hBU.1 hπ Ex hEx t ht
  refine ⟨Q, hQ0, fun c hc hσ ρ hρ E t' hE ht' => ?_⟩
  obtain ⟨hσU, hBG, H', hH', hcoef, hsnc, -⟩ := hQ c hc
  set σ := ∑ i, MMP.Mori.scalarsToGlobalSections ℂ sX (c i) • s i with hσdef
  have hρσ : ρU σ = ∑ i, MMP.Mori.scalarsToGlobalSections ℂ (U.ι ≫ sX) (c i) • t i := by
    rw [hσdef, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hρs]; rfl
  obtain ⟨h0, hzero⟩ := hρz σ hσ
  have hzcongr : ∀ {a b : MMP.Mori.Divisor.divisorialSubmodule (M.restrictOpen U) ⊤} (e : a = b)
      (ha : a ≠ 0) (hb : b ≠ 0), MMP.Mori.Divisor.zeroDivisor (M.restrictOpen U) a ha =
        MMP.Mori.Divisor.zeroDivisor (M.restrictOpen U) b hb := by
    intro a b e ha hb; subst e; rfl
  have hG : MMP.Mori.Divisor.zeroDivisor (M.restrictOpen U) _ hσU =
      (M.zeroDivisor σ hσ).restrictOpen U := (hzcongr hρσ.symm hσU h0).trans hzero
  have hMUc : MMP.Mori.Divisor.IsCartier (M.restrictOpen U) :=
    MMP.Fourfold.isCartier_of_isPullback U.ι hMc (MMP.Flips.isPullback_restrictOpen U hMc)
  have hlcU := isLogCanonicalPair_add_inv_smul hBUp hBU ⟨hπ, hπp⟩ Ex hEx
    (MMP.Mori.Divisor.zeroDivisor_nonneg _ _ hσU)
    (isCartier_zeroDivisor hMUc _ hσU)
    hH' hcoef hsnc hρ
  rw [hG] at hlcU
  have hres : BU + (ρ : ℚ)⁻¹ • Divisor.toQDivisor ((M.zeroDivisor σ hσ).restrictOpen U) =
      (B + (ρ : ℚ)⁻¹ • Divisor.toQDivisor (M.zeroDivisor σ hσ)).restrictOpen U := by
    ext P
    rfl
  rw [hres] at hlcU
  have hlc := isLcPair_of_isLogCanonicalPair hB hK
  have hHc := isCartier_zeroDivisor hMc σ hσ
  have hPW : MMP.Mori.IsPairWith sX 4 K (B + (ρ : ℚ)⁻¹ • Divisor.toQDivisor (M.zeroDivisor σ hσ)) :=
    ⟨hXn, hK, by rw [← add_assoc]; exact hlc.1.2.2.add (isQCartier_smul'
      (MMP.Mori.QDivisor.isQCartier_toQDivisor hHc) _)⟩
  have hcen : ((E.center : Set X) ∩ U).Nonempty := by
    obtain ⟨z, hz, hzW⟩ := Set.not_subset.1 hE
    exact ⟨z, hz, hzW⟩
  exact nonneg_of_isLogDiscrepancy_of_restrictOpen hPW U hlcU hcen ht'

/-- **A general member** of a linear system of `𝒪_X(M)` free off the minimal lc centre `W` and
containing a section `σ₀` nonzero on `W`: it does not contain any lc centre, `(X, B + H/r)` is lc
off `W` for every `r > 0`, and it restricts to `W` as a nonzero multiple of `σ₀`. -/
private theorem exists_general_member (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : IsLogCanonicalPair sX B) {W : IrreducibleCloseds X}
    (hW : IsMinimalLcCentre sX B W) {M : Divisor X} (hMc : M.IsCartier) {r : ℕ}
    (σ₀ : M.divisorialSubmodule ⊤)
    (hσ₀ : AlgebraicGeometry.pullbackGlobalSections (centreι W) M.divisorialSheaf σ₀ ≠ 0)
    (τ : Fin r → M.divisorialSubmodule ⊤)
    (hτW : ∀ i, AlgebraicGeometry.pullbackGlobalSections (centreι W) M.divisorialSheaf (τ i) = 0)
    (hτ : ∀ y : X, y ∉ (W : Set X) → ∃ (i : Fin r) (hi : τ i ≠ 0),
      y ∉ (M.zeroDivisor (τ i) hi).supp) :
    ∃ σ : M.divisorialSubmodule ⊤, ∃ hσ : σ ≠ 0, ∃ c : ℂ,
      AlgebraicGeometry.pullbackGlobalSections (centreι W) M.divisorialSheaf σ ≠ 0 ∧
      AlgebraicGeometry.pullbackGlobalSections (centreι W) M.divisorialSheaf σ =
        AlgebraicGeometry.pullbackGlobalSections (centreι W) M.divisorialSheaf
          (MMP.Mori.scalarsToGlobalSections ℂ sX c • σ₀) ∧
      (∀ Z ∈ lcCentres sX B, ¬ (Z : Set X) ⊆ ((M.zeroDivisor σ hσ).supp : Set X)) ∧
      ∀ ρ : ℕ, 0 < ρ → ∀ (E : DivisorOver ℂ sX) (t : ℝ), ¬ (E.center : Set X) ⊆ W →
        IsLogDiscrepancy sX 4
          (QDivisor.toRDivisor (B + (ρ : ℚ)⁻¹ • Divisor.toQDivisor (M.zeroDivisor σ hσ))) E t →
          0 ≤ t := by
  classical
  set ι := centreι W
  let s : Option (Fin r) → M.divisorialSubmodule ⊤ := fun o => o.elim σ₀ τ
  have hs : ∀ y : X, y ∉ (W : Set X) → ∃ (i : Option (Fin r)) (hi : s i ≠ 0),
      y ∉ (M.zeroDivisor (s i) hi).supp := fun y hy =>
    let ⟨i, hi, h⟩ := hτ y hy
    ⟨some i, hi, h⟩
  obtain ⟨Q₁, hQ₁0, hQ₁⟩ := exists_polynomial_lc_off sX hX hK hB (W : Set X) W.isClosed hMc s hs
  obtain ⟨c, hc⟩ : ∃ c : Option (Fin r) → ℂ, MvPolynomial.eval c (Q₁ * MvPolynomial.X none) ≠ 0 := by
    by_contra h
    push Not at h
    exact mul_ne_zero hQ₁0 (MvPolynomial.X_ne_zero none)
      (MvPolynomial.funext fun x => by rw [h x, map_zero])
  rw [map_mul, MvPolynomial.eval_X] at hc
  have hc₁ := left_ne_zero_of_mul hc
  have hcn : c none ≠ 0 := right_ne_zero_of_mul hc
  set σ := ∑ i, MMP.Mori.scalarsToGlobalSections ℂ sX (c i) • s i with hσdef
  let P : M.divisorialSubmodule ⊤ →+ Γ((Scheme.Modules.pullback ι).obj M.divisorialSheaf, ⊤) :=
    { toFun := fun σ' => AlgebraicGeometry.pullbackGlobalSections ι M.divisorialSheaf σ'
      map_zero' := map_zero _
      map_add' := fun a b => map_add _ (a : Γ(M.divisorialSheaf, ⊤)) b }
  have hPs : ∀ (r : Γ(X, ⊤)) (σ' : M.divisorialSubmodule ⊤), P (r • σ') = ι.appTop r • P σ' :=
    fun r σ' => MMP.Chow.DeterminantCurveForm.pullbackGlobalSections_smul ι M.divisorialSheaf r σ'
  have hpull : P σ = P (MMP.Mori.scalarsToGlobalSections ℂ sX (c none) • σ₀) := by
    rw [hσdef, map_sum, Fintype.sum_option]
    have hz : ∑ a : Fin r, P (MMP.Mori.scalarsToGlobalSections ℂ sX (c (some a)) • s (some a)) =
        0 := Finset.sum_eq_zero fun a _ => by
      rw [hPs]
      exact (congrArg _ (hτW a)).trans (smul_zero _)
    rw [hz, add_zero]
    rfl
  have hunit : IsUnit (ι.appTop (MMP.Mori.scalarsToGlobalSections ℂ sX (c none))) :=
    ((isUnit_iff_ne_zero.2 hcn).map _).map _
  have hpull0 : P σ ≠ 0 := by
    rw [hpull, hPs]
    exact fun h => hσ₀ ((hunit.smul_eq_zero).1 h)
  have hσ : σ ≠ 0 := by
    rintro h
    rw [h, map_zero] at hpull0
    exact hpull0 rfl
  have hlcW := hQ₁ c hc₁ hσ
  refine ⟨σ, hσ, c none, hpull0, hpull, fun Z hZ hZH => ?_, hlcW⟩
  -- an lc centre other than `W` is not contained in `W`, and lc outside `W` keeps it out of `H`
  have hZW : ¬ (Z : Set X) ⊆ W := by
    intro hsub
    have hZeq := hW.2 Z hZ hsub
    subst hZeq
    exact not_subset_supp_zeroDivisor_of_pullback_ne_zero hMc Z σ hσ hpull0 hZH
  obtain ⟨E, hE0, hEZ⟩ := hZ
  have hlc := isLcPair_of_isLogCanonicalPair hB hK
  have hHc := isCartier_zeroDivisor hMc σ hσ
  have hHq := MMP.Mori.QDivisor.isQCartier_toQDivisor hHc
  have hb := isDiscrepancy_neg_one_of_isLogDiscrepancy_zero sX hK hB hE0
  obtain ⟨-, hBH, hiff⟩ := hlc.1.isDiscrepancy_add_smul_iff hHq E
  haveI := E.isLocallyNoetherian
  haveI := E.isNormal
  haveI := E.isIntegral
  haveI := E.isDominant
  haveI : CompactSpace E.Y := haveI := hE0.2.1
    QuasiCompact.compactSpace_of_compactSpace E.f
  obtain ⟨B', hB', huniq⟩ := hHq.existsUnique_isPullback (f := E.f) hBH
  -- the coefficient of `E` in `E^*H` is positive
  have hpos : 0 < B'.coeff E.E := by
    have hBH' : ∀ Z' : irreducibleComponents E.Y,
        E.f (MMP.Mori.componentGenericPoint E.Y Z') ∉ (M.zeroDivisor σ hσ).supp :=
      fun Z' => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant E.f _ Z'
    obtain ⟨H', hH'⟩ := hHc.exists_isPullback hBH'
    have hB'eq : B' = Divisor.toQDivisor H' :=
      (huniq _ (MMP.Mori.QDivisor.isPullback_toQDivisor hHc hBH hH')).symm
    have hsupp := MMP.Flips.supp_eq_preimage_supp_of_isPullback hHc
      (MMP.Mori.Divisor.zeroDivisor_nonneg M σ hσ) hH'
    have hηc : E.f E.E.genericPoint ∈ (E.center : Set X) := by
      rw [E.center_eq_closure_genericPoint]; exact subset_closure rfl
    have hη : E.E.genericPoint ∈ (H'.supp : Set E.Y) := by
      rw [hsupp]; exact hZH (hEZ ▸ hηc)
    obtain ⟨P, hP, hηP⟩ := MMP.Mori.DivisorWithCoeffs.mem_supp_iff.1 hη
    have hPE : P = E.E := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hηP
    subst hPE
    have hnn := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hHc (V := ⊤)
      (fun Q _ => MMP.Mori.Divisor.zeroDivisor_nonneg M σ hσ Q) hH' E.E
      ⟨E.E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support E.E, trivial⟩
    rw [hB'eq, MMP.Mori.Divisor.coeff_toQDivisor]
    exact_mod_cast lt_of_le_of_ne hnn (Ne.symm hP)
  have hdisc := ((hiff B' hB').2 ((1 : ℕ) : ℚ)⁻¹ (-1)).2 hb
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hdisc hE0.2.1
  have h0 := hlcW 1 one_pos E _ (fun h => hZW (hEZ ▸ h)) hlog
  have hpos' : (0 : ℝ) < (B'.coeff E.E : ℝ) := by exact_mod_cast hpos
  norm_num at h0
  linarith

/-- **Lifting a concentrated divisor of the centre to a general member on `X`.** Let `M` be an
ample Cartier divisor on `X` with `(sk)M - (K_X + B)` ample for all `s > 0`, and `D_W` an
effective Cartier divisor on the minimal lc centre `W`, linearly equivalent to `k M|_W`, with a
local equation at a closed point `x` in `𝔪_x^e`. Then for some `s > 0` there is an effective
Cartier divisor `H ∼ (sk)M` on `X`, not containing `W` nor any lc centre, such that every
`(X, B + H/r)`, `r > 0`, is lc outside `W`, with a local equation at `x` in `𝔪_x^{se} + ℐ_W`. -/
private theorem exists_general_lift (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : IsLogCanonicalPair sX B) {W : IrreducibleCloseds X}
    (hW : IsMinimalLcCentre sX B W) {M : Divisor X} (hMc : M.IsCartier) (hM : M.IsAmple hMc)
    {k : ℕ} (hk : 0 < k)
    (hgap : ∀ s : ℕ, 0 < s →
      (Divisor.toQDivisor ((s * k) • M) - (Divisor.toQDivisor K + B)).IsAmple)
    {DW : (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme.CartierDivisor}
    (hDW : MMP.Intersection.IsEffective DW)
    {C : (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme.CartierDivisor}
    (hC : CLinEquiv (restrictDivisor (centreι W) hMc) C)
    (hlin : MMP.Intersection.LinearlyEquivalent DW (k • C))
    (x : (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme)
    (hx : IsClosed ({x} : Set _)) {e : ℕ}
    (a : (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme.presheaf.stalk x)
    (ha : a ∈ IsLocalRing.maximalIdeal _ ^ e)
    (hloc : MMP.Intersection.IsLocalEquationAt DW x (MMP.Intersection.stalkToTotalQuotient x a)) :
    ∃ (s : ℕ) (H : Divisor X), 0 < s ∧ H.IsCartier ∧ 0 ≤ H ∧
      H.LinearlyEquivalent ((s * k) • M) ∧ ¬ ((W : Set X) ⊆ (H.supp : Set X)) ∧
      (∀ Z ∈ lcCentres sX B, ¬ (Z : Set X) ⊆ (H.supp : Set X)) ∧
      (∀ r : ℕ, 0 < r → ∀ (E : DivisorOver ℂ sX) (t : ℝ), ¬ (E.center : Set X) ⊆ W →
        IsLogDiscrepancy sX 4 (QDivisor.toRDivisor (B + (r : ℚ)⁻¹ • Divisor.toQDivisor H)) E t →
          0 ≤ t) ∧
      ∃ U : X.Opens, centreι W x ∈ U ∧ ∃ φ : (MMP.Mori.RationalFunctions X)ˣ,
        H.IsLocalEquation U φ ∧ ∃ g : X.presheaf.stalk (centreι W x),
          (∀ (Z : irreducibleComponents X) (hZ : centreι W x ∈ Z.1),
            (φ : MMP.Mori.RationalFunctions X) Z = (MMP.Mori.stalkToRationalFunctions X hZ).hom g) ∧
          g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (centreι W x)) ^ (s * e) ⊔
            (Scheme.IdealSheafData.vanishingIdeal ⟨W, W.isClosed⟩).stalkIdeal (centreι W x) := by
  haveI := hX
  set ι := centreι W
  obtain ⟨s, hs1, r, τ, hτW, hτ⟩ : ∃ s : ℕ, 1 ≤ s ∧ ∃ (r : ℕ)
      (τ : Fin r → ((s * k) • M).divisorialSubmodule ⊤),
      (∀ i, AlgebraicGeometry.pullbackGlobalSections ι ((s * k) • M).divisorialSheaf (τ i) = 0) ∧
      ∀ y : X, y ∉ (W : Set X) → ∃ (i : Fin r) (hi : τ i ≠ 0),
        y ∉ (((s * k) • M).zeroDivisor (τ i) hi).supp := by
    have h := eventually_exists_sections_free_off_centre sX hX (hMc.nsmul k)
      (isAmple_nsmul_of_isAmple sX hX hMc hM hk) W
    obtain ⟨s, hs, hs1⟩ := (h.and (eventually_ge_atTop 1)).exists
    refine ⟨s, hs1, ?_⟩
    rw [show (s * k) • M = s • (k • M) by rw [mul_smul]]
    exact hs
  have hsk : 0 < s * k := Nat.mul_pos hs1 hk
  have hM'c : ((s * k) • M).IsCartier := hMc.nsmul _
  have hC' : CLinEquiv (restrictDivisor ι hM'c) (s • (k • C)) := by
    rw [smul_smul]
    exact (restrictDivisor_nsmul ι hMc (s * k)).trans (hC.nsmul _)
  have hlin' : MMP.Intersection.LinearlyEquivalent (s • DW) (s • (k • C)) := by
    unfold MMP.Intersection.LinearlyEquivalent at hlin ⊢
    rw [← smul_sub]
    exact AddSubgroup.nsmul_mem _ hlin _
  have hDW' : MMP.Intersection.IsEffective (s • DW) := isEffective_nsmul_of_pos hDW hs1
  have hloc' : MMP.Intersection.IsLocalEquationAt (s • DW) x
      (MMP.Intersection.stalkToTotalQuotient x (a ^ s)) := by
    rw [map_pow]
    exact isLocalEquationAt_nsmul_of_pos hloc hs1
  have ha' : a ^ s ∈ IsLocalRing.maximalIdeal _ ^ (s * e) := by
    rw [mul_comm, pow_mul]
    exact Ideal.pow_mem_pow ha s
  obtain ⟨σ₀, hσ₀, hσ₀loc⟩ := exists_lift_concentrated sX hX hdim hK hB hW hM'c (hgap s hs1) hDW'
    hC' hlin' x (a ^ s) ha' hloc'
  obtain ⟨σ, hσ, c, hσW0, hσW, hZ, hlc⟩ :=
    exists_general_member sX hX hdim hK hB hW hM'c σ₀ hσ₀ τ hτW hτ
  refine ⟨s, ((s * k) • M).zeroDivisor σ hσ, hs1, ?_, Divisor.zeroDivisor_nonneg _ σ hσ, ?_,
    not_subset_supp_zeroDivisor_of_pullback_ne_zero hM'c W σ hσ hσW0, hZ, hlc,
    hσ₀loc σ hσ c hσW0 hσW⟩
  · exact isCartier_zeroDivisor hM'c σ hσ
  · exact ⟨(Divisor.isUnit_sectionToRationalFunctions hσ).unit, by
      rw [Divisor.zeroDivisor_eq]; abel⟩

/-- **A concentrated boundary.** If `L|_W` is not numerically trivial on a minimal lc centre `W`,
there are a rational `u ≥ a` and an effective `ℚ`-divisor `G ∼_ℚ uL - (K_X + B)` containing no
lc centre of `(X, B)`, such that `(X, B + G)` is lc outside `W` but not lc. -/
private theorem exists_concentrated_boundary
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {L : Divisor X} (hL : L.IsNef ℂ sX)
    {B : QDivisor X} {a : ℚ} (hB : IsLogCanonicalPair sX B) (ha : 0 < a)
    (hample : (a • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsAmple)
    {W : IrreducibleCloseds X} (hW : IsMinimalLcCentre sX B W)
    (hntriv : ¬ IsNumTrivialOn sX hL.1 (W : Set X)) :
    ∃ (u : ℚ) (G : QDivisor X), a ≤ u ∧ (∀ P, 0 ≤ G.coeff P) ∧
      (∃ β : ℕ, 0 < β ∧ ∃ φ : (MMP.Mori.RationalFunctions X)ˣ,
        Divisor.toQDivisor (MMP.Mori.principalDivisor φ) =
          (β : ℚ) • (G - (u • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)))) ∧
      (∀ Z ∈ lcCentres sX B, ¬ (Z : Set X) ⊆ (G.supp : Set X)) ∧
      (∀ (E : DivisorOver ℂ sX) (r : ℝ), ¬ (E.center : Set X) ⊆ W →
        IsLogDiscrepancy sX 4 (QDivisor.toRDivisor (B + G)) E r → 0 ≤ r) ∧
      ¬ IsLogCanonicalPair sX (B + G) := by
  haveI := hX
  have hlc := isLcPair_of_isLogCanonicalPair hB hK
  obtain ⟨⟨E, hE, hEW⟩, -⟩ := id hW
  have hEdisc := isDiscrepancy_neg_one_of_isLogDiscrepancy_zero sX hK hB hE
  set Ws := (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme
  set ι := centreι W
  haveI hWp := isProjectiveVariety_centre sX hX W
  have hWp' : AlgebraicGeometry.IsProjectiveVariety ℂ (ι ≫ sX) := hWp
  haveI : IsProper (ι ≫ sX) := (IsProjectiveMorphism.isProjective hWp'.isProjective).isProper
  obtain ⟨d, hd0, hd, hnef, hnt⟩ := centre_curve_data sX hX hL W hntriv
  have hdW : topologicalKrullDim (W : Set X) = d := by
    rw [← hd]
    have hr : Set.range ι = (W : Set X) := range_centreι W
    have e := (ι.isClosedEmbedding.isEmbedding.toHomeomorph).trans (Homeomorph.setCongr hr)
    exact (IsHomeomorph.topologicalKrullDim_eq e.symm e.symm.isHomeomorph)
  obtain ⟨V, hVne, hV⟩ :=
    MMP.Mori.not_isAt_isLcPair_add_of_mem_maximalIdeal_pow_sup sX hlc W ⟨E, hEW, hEdisc⟩ hd0 hdW
  obtain ⟨n₀, hn₀, D₀, hD₀, hD₀c, hD₀amp⟩ := hample
  obtain ⟨j, hjc, hvol⟩ := exists_large_volume sX hX hL W hD₀c hD₀amp hd0 hd hnef hnt
    ((n₀ * d) ^ d + n₀ * ⌈a⌉₊)
  set M := D₀ + j • L
  have hMc : M.IsCartier := hD₀c.add (hL.1.nsmul j)
  have hMamp : M.IsAmple hMc := by
    have hN := isNef_smul_toQDivisor sX hL (t := (j : ℚ)) (by positivity)
    refine MMP.Mori.QDivisor.isAmple_of_numericallyEquivalent_add_of_isNef sX
      ⟨1, one_pos, D₀, by simp, hD₀c, hD₀amp⟩ hN (MMP.Mori.QDivisor.NumericallyEquivalent.refl
        ((QDivisor.isQCartier_toQDivisor hD₀c).add hN.1)) 1 one_pos M ?_ hMc
    simp only [M, map_add, map_nsmul, Nat.cast_one, one_smul, ← Nat.cast_smul_eq_nsmul ℚ]
  set u : ℚ := a + j / n₀
  have hn₀q : (0 : ℚ) < n₀ := by exact_mod_cast hn₀
  have hnj : (n₀ : ℚ) * u = n₀ * a + j := by
    simp only [u]; field_simp
  have hMq : Divisor.toQDivisor M =
      (n₀ : ℚ) • (u • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)) := by
    simp only [M, map_add, map_nsmul, hD₀, ← Nat.cast_smul_eq_nsmul ℚ]
    rw [smul_sub (n₀ : ℚ) (u • _), smul_smul, hnj]
    module
  obtain ⟨x, hxV, hxcl, hxcl', hxsm, hxreg⟩ := exists_good_point sX hX W V
    (by simpa using hVne)
  -- the concentrated divisor of the centre
  set C := restrictDivisor ι hD₀c + j • restrictDivisor ι hL.1
  have hCM : CLinEquiv (restrictDivisor ι hMc) C :=
    (restrictDivisor_add ι hD₀c (hL.1.nsmul j)).trans
      ((CLinEquiv.refl _).add (restrictDivisor_nsmul ι hL.1 j))
  set N : MMP.Mori.KCartierDivisor ℚ Ws :=
    (n₀ : ℚ)⁻¹ • MMP.Mori.KCartierDivisor.ofCartier ℚ C
  have hnNeq : (n₀ : ℚ) • N = ((1 : ℤ) : ℚ) • MMP.Mori.KCartierDivisor.ofCartier ℚ C := by
    rw [smul_inv_smul₀ hn₀q.ne', Int.cast_one, one_smul]
  have hnN : ∀ P, ∃ z : ℤ, ((n₀ : ℚ) • N) P = z := by
    intro P
    rw [hnNeq, Int.cast_one, one_smul]
    by_cases hP : P = C
    · exact ⟨1, by simp [MMP.Mori.KCartierDivisor.ofCartier, hP]⟩
    · exact ⟨0, by simp [MMP.Mori.KCartierDivisor.ofCartier, Finsupp.single_apply, Ne.symm hP]⟩
  have hreal : MMP.Mori.KCartierDivisor.realization ((n₀ : ℚ) • N) hnN = C := by
    rw [realization_eq_zsmul _ _ hnNeq hnN, one_zsmul]
  have hNamp : MMP.Fourfold.KCartierDivisor.IsRelativelyAmpleQ (ι ≫ sX) N := by
    refine ⟨n₀, hn₀, hnN, ?_⟩
    suffices hall : ∀ C' : Ws.CartierDivisor, C' = C →
        MMP.Mori.IsRelativelyAmple (ι ≫ sX) (MMP.CartierDivisor.sheaf C') from hall _ hreal
    rintro _ rfl
    have h1 := isAmple_sheaf_restrictDivisor hMc hMamp W
    obtain ⟨eC⟩ := (cLinEquiv_iff _ _).mp hCM
    have h2 := (Stacks.RelativeVeryAmple.isAmple_congr _ _
      eC.symm).2 h1
    exact MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple (ι ≫ sX) _ h2
  have hvol' : ((n₀ * d : ℕ) : ℤ) ^ d < MMP.Mori.sheafSelfIntersectionNumber ℂ (ι ≫ sX) (𝟙 Ws) d
      hd.le (MMP.CartierDivisor.sheaf (MMP.Mori.KCartierDivisor.realization ((n₀ : ℚ) • N) hnN)) :=
          by
    rw [hreal]
    refine lt_of_le_of_lt ?_ hvol
    push_cast
    linarith [Nat.zero_le (n₀ * ⌈a⌉₊)]
  obtain ⟨q, hq, hqi, DW, hDWe, hDWlin, a', ha', hDWloc⟩ :=
    MMP.Mori.KCartierDivisor.exists_isEffective_linearlyEquivalent_mem_maximalIdeal_pow ℂ (ι ≫ sX)
      hWp d hd0 hd N hNamp n₀ hn₀ hnN hvol' x hxcl' hxsm
  -- `q = k n₀` and the realization of `qN` is `k M|_W`
  obtain ⟨k, hk, hqk, hrealq⟩ : ∃ k : ℕ, 0 < k ∧ q = k * n₀ ∧
      MMP.Mori.KCartierDivisor.realization ((q : ℚ) • N) hqi = k • C := by
    obtain ⟨z, hz⟩ := hqi C
    have hz' : (q : ℚ) / n₀ = z := by
      simpa [N, MMP.Mori.KCartierDivisor.ofCartier, div_eq_mul_inv] using hz
    have hzpos : 0 < z := by
      have : (0 : ℚ) < q / n₀ := by positivity
      exact_mod_cast hz' ▸ this
    refine ⟨z.toNat, by omega, ?_, ?_⟩
    · have : (q : ℚ) = z * n₀ := by rw [← hz']; field_simp
      have h2 : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hzpos.le
      have : ((q : ℕ) : ℤ) = (z.toNat : ℤ) * n₀ := by rw [h2]; exact_mod_cast this
      exact_mod_cast this
    · have hNq : (q : ℚ) • N = (z : ℚ) • MMP.Mori.KCartierDivisor.ofCartier ℚ C := by
        rw [← hz', smul_smul, div_eq_mul_inv]
      rw [realization_eq_zsmul _ _ hNq hqi, ← natCast_zsmul, Int.toNat_of_nonneg hzpos.le]
  rw [hrealq] at hDWlin
  have hgap : ∀ s : ℕ, 0 < s →
      (Divisor.toQDivisor ((s * k) • M) - (Divisor.toQDivisor K + B)).IsAmple := by
    intro s hs
    have hA : (a • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsAmple :=
      ⟨n₀, hn₀, D₀, hD₀, hD₀c, hD₀amp⟩
    have h1 := isAmple_smul_add_principal sX hX hA (s := ((s * k * n₀ : ℕ) : ℚ) + 1)
      (by positivity) 0 1
    rw [zero_smul, add_zero] at h1
    have hja : a ≤ j := by
      have := Nat.le_ceil a
      have h2 : (⌈a⌉₊ : ℚ) ≤ j := by
        have : n₀ * ⌈a⌉₊ ≤ j := le_trans (Nat.le_add_left _ _) hjc
        exact_mod_cast le_trans (Nat.le_mul_of_pos_left _ hn₀) this
      linarith
    have h2 := isAmple_add_smul_of_isNef sX hX h1 hL
      (t := (s * k : ℕ) * (j : ℚ) - a) (by
        have : (1 : ℚ) ≤ (s * k : ℕ) := by exact_mod_cast Nat.mul_pos hs hk
        nlinarith)
    convert h2 using 1
    rw [map_nsmul, hMq, ← Nat.cast_smul_eq_nsmul ℚ, smul_sub (n₀ : ℚ) (u • _), smul_smul, hnj]
    push_cast
    module
  obtain ⟨s, H, hs, hHc, hH0, hHlin, hWH, hZH, hlcout, U, hxU, φ, hφ, g, hg, hgmem⟩ :=
    exists_general_lift sX hX hdim hK hB hW hMc hMamp hk hgap hDWe hCM hDWlin x hxcl' a' ha' hDWloc
  -- the boundary `G = H / (s k n₀)`
  have hsk : 0 < s * k * n₀ := Nat.mul_pos (Nat.mul_pos hs hk) hn₀
  set G : QDivisor X := ((s * k * n₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor H
  have hskq : ((s * k * n₀ : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hsk.ne'
  have hHG : Divisor.toQDivisor H = ((s * k * n₀ : ℕ) : ℤ) • G := by
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_inv_smul₀ hskq]
  have hG0 : ∀ P, 0 ≤ G.coeff P := fun P => by
    simp only [G, MMP.Mori.DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, smul_eq_mul]
    exact mul_nonneg (by positivity) (by exact_mod_cast hH0 P)
  have hGsupp : (G.supp : Set X) = (H.supp : Set X) := by
    rw [← QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hsk.ne') hHG]
  have hGq : G.IsQCartier := ⟨(s * k * n₀ : ℕ), by exact_mod_cast hsk.ne', H, hHG, hHc⟩
  refine ⟨u, G, by
      have : (0 : ℚ) ≤ j / n₀ := by positivity
      linarith, hG0, ?_, ?_, ?_, ?_⟩
  · -- `G ∼_ℚ uL - (K + B)`
    obtain ⟨ψ, hψ⟩ := hHlin
    refine ⟨s * k * n₀, hsk, ψ, ?_⟩
    have hGH : ((s * k * n₀ : ℕ) : ℚ) • G = Divisor.toQDivisor H := smul_inv_smul₀ hskq _
    rw [← hψ, map_sub, map_nsmul, hMq, smul_sub ((s * k * n₀ : ℕ) : ℚ) G, hGH,
      ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
    congr 2
    push_cast
    ring
  · intro Z hZ hsub
    exact hZH Z hZ (hGsupp ▸ hsub)
  · intro E' t hE' ht
    exact hlcout (s * k * n₀) hsk E' t hE' ht
  · intro hlcG
    have hlcG' := isLcPair_of_isLogCanonicalPair hlcG hK
    refine hV (centreι W x) ⟨?_, hxV⟩ hxcl hxreg G (fun P => hG0 P) hGq
      (fun h => hWH (hGsupp ▸ h)) ⟨s * k * n₀, hsk, H, hHG, U, hxU, φ, hφ, g, hg, ?_⟩ ?_
    · exact (range_centreι W).le ⟨x, rfl⟩
    · have hle : s * k * n₀ * d + 1 ≤ s * (q * d + 1) := by
        rw [hqk]
        have : 1 ≤ s := hs
        calc s * k * n₀ * d + 1 ≤ s * k * n₀ * d + s := by omega
          _ = s * (k * n₀ * d + 1) := by ring
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hgmem
      exact hyz ▸ Submodule.mem_sup.mpr ⟨y, Ideal.pow_le_pow_right hle hy, z, hz, rfl⟩
    · haveI : Nonempty (⊤ : X.Opens) := ⟨⟨centreι W x, trivial⟩⟩
      exact ⟨⊤, Set.subset_univ _, inferInstance, MMP.Mori.IsLcPair.restrictOpen ⊤ hlcG'⟩

/-- If the pull-back of an effective `ℚ`-Cartier `G` along a proper birational `π` has positive
coefficient along a prime divisor `F`, then the centre of `F` lies in `Supp G`. -/
private theorem centre_subset_supp_of_pos {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {π : Y ⟶ X}
    (hY : MMP.Mori.IsNormalVariety ℂ (π ≫ sX)) (hbir : MMP.Mori.IsBirationalMorphism π)
    {G : QDivisor X} (hGq : G.IsQCartier)
    (hGsupp : ∀ Z : irreducibleComponents Y, π (MMP.Mori.componentGenericPoint Y Z) ∉ G.supp)
    {Gπ : QDivisor Y} (hGπ : G.IsPullback π hGsupp Gπ) (F : MMP.Mori.PrimeDivisor Y)
    (hF : 0 < Gπ.coeff F) :
    ((⟨Y, π, hY, hbir, F⟩ : DivisorOver ℂ sX).center : Set X) ⊆ (G.supp : Set X) := by
  rw [DivisorOver.center_eq_closure_genericPoint]
  refine closure_minimal ?_ (G.supp).isClosed
  rintro _ rfl
  obtain ⟨m, hm, D, hD, hDc⟩ := hGq.exists_pos
  obtain ⟨D', hD', hpb⟩ := hGπ m hm D hD hDc
  have hFD' : F.genericPoint ∈ (D'.supp : Set Y) := by
    refine MMP.Mori.DivisorWithCoeffs.mem_supp_iff.mpr ⟨F, fun h0 => ?_, ?_⟩
    · have := congrArg (fun Q : QDivisor Y => Q.coeff F) hD'
      simp only [Divisor.coeff_toQDivisor, h0, MMP.Mori.DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
      push_cast at this
      have hm' : (0 : ℚ) < m := by exact_mod_cast hm
      nlinarith
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have := MMP.Flips.supp_subset_preimage_supp_of_isPullback hDc hpb hFD'
  rw [Set.mem_preimage, QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hD] at this
  exact this

/-- **The log canonical threshold of a concentrated boundary.** For an lc pair `(X, B)` and an
effective `ℚ`-Cartier `G` containing no lc centre, with `(X, B + G)` lc outside the minimal lc
centre `W` but not lc, the log canonical threshold `c` of `G` is rational with `0 < c < 1`, and
`(X, B + cG)` has an lc centre properly contained in `W`. -/
private theorem exists_lct_lt_one
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : IsLogCanonicalPair sX B)
    {W : IrreducibleCloseds X} (hW : IsMinimalLcCentre sX B W)
    {G : QDivisor X} (hG0 : ∀ P, 0 ≤ G.coeff P) (hGq : G.IsQCartier)
    (hGc : ∀ Z ∈ lcCentres sX B, ¬ (Z : Set X) ⊆ (G.supp : Set X))
    (hGW : ∀ (E : DivisorOver ℂ sX) (r : ℝ), ¬ (E.center : Set X) ⊆ W →
        IsLogDiscrepancy sX 4 (QDivisor.toRDivisor (B + G)) E r → 0 ≤ r)
    (hGnlc : ¬ IsLogCanonicalPair sX (B + G)) :
    ∃ c : ℚ, 0 < c ∧ c < 1 ∧ IsLogCanonicalPair sX (B + c • G) ∧
      ∃ Z ∈ lcCentres sX (B + c • G), Z < W := by
  haveI := hX
  have hlc := isLcPair_of_isLogCanonicalPair hB hK
  have hPW := hlc.1
  have hXn : MMP.Mori.IsNormalVariety ℂ sX := hPW.1
  obtain ⟨Y, π, hπ, hπp⟩ := MMP.Mori.exists_isLogResolution_isProjectiveMorphism sX hXn
    (QDivisor.toRDivisor (B + G))
  obtain ⟨hY, -, -⟩ := MMP.Mori.IsSmoothResolution.isNormalVariety hXn hπ.toIsSmoothResolution
  have hbir := hπ.isBirationalMorphism
  haveI := hπ.isProper
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI : IsLocallyNoetherian Y :=
    haveI := hY.1.toLocallyOfFiniteType; LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX)
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace π
  haveI : IsDominant π := hbir.isDominant
  -- the crepant boundary of `(X, B)` and the pull-back of `G`
  obtain ⟨⟨B₀, hB₀, -⟩, -⟩ := MMP.Mori.IsPair.existsUnique_isCrepantBoundary hPW.isPair hK π hY hbir
  have hGsupp : ∀ Z : irreducibleComponents Y, π (MMP.Mori.componentGenericPoint Y Z) ∉ G.supp := by
    intro Z
    obtain ⟨m, hm, D, hD, -⟩ := hGq.exists_pos
    rw [← QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hD]
    exact MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant π D Z
  obtain ⟨Gπ, hGπ, -⟩ := hGq.existsUnique_isPullback (f := π) hGsupp
  set E : MMP.Mori.PrimeDivisor Y → DivisorOver ℂ sX := fun F => ⟨Y, π, hY, hbir, F⟩
  -- the discrepancies of `(X, B + tG)` along the prime divisors of `Y` are affine in `t`
  have hdisc : ∀ (t : ℚ) (F : MMP.Mori.PrimeDivisor Y),
      MMP.Mori.IsDiscrepancy sX 4 K (B + t • G) (E F) (-B₀.coeff F - t * Gπ.coeff F) := by
    intro t F
    obtain ⟨-, hB', h⟩ := hPW.isDiscrepancy_add_smul_iff hGq (E F)
    exact ((h Gπ hGπ).2 t (-B₀.coeff F)).2 (hB₀ F)
  have hlog : ∀ (t : ℚ) (F : MMP.Mori.PrimeDivisor Y),
      IsLogDiscrepancy sX 4 (QDivisor.toRDivisor (B + t • G)) (E F)
        (((1 - B₀.coeff F - t * Gπ.coeff F : ℚ) : ℝ)) := by
    intro t F
    have := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hdisc t F) hπ.isProper
    convert this using 2; push_cast; ring
  -- `(X, B)` is lc and `(X, B + G)` is lc outside `W`
  have hd1 : ∀ F, B₀.coeff F ≤ 1 := by
    intro F
    have := hB.2.2 4 (E F) _ (by simpa using hlog 0 F)
    have : (0 : ℝ) ≤ ((1 - B₀.coeff F : ℚ) : ℝ) := by simpa using this
    exact_mod_cast (sub_nonneg.mp (by exact_mod_cast this))
  have hcentre : ∀ F, ¬ ((E F).center : Set X) ⊆ W → B₀.coeff F + Gπ.coeff F ≤ 1 := by
    intro F hF
    have := hGW (E F) _ hF (by simpa using hlog 1 F)
    have : (0 : ℝ) ≤ ((1 - B₀.coeff F - Gπ.coeff F : ℚ) : ℝ) := by simpa using this
    have := (show (0 : ℚ) ≤ 1 - B₀.coeff F - Gπ.coeff F by exact_mod_cast this)
    linarith
  -- the crepant boundaries and the log canonical criterion on `Y`
  have hcrep : ∀ t : ℚ, MMP.Mori.IsCrepantBoundary sX 4 K (B + t • G) π hY hbir (B₀ + t • Gπ) := by
    intro t F
    convert hdisc t F using 1
    simp only [MMP.Mori.DivisorWithCoeffs.coeff_add, MMP.Mori.DivisorWithCoeffs.coeff_smul,
      smul_eq_mul]
    ring
  have hres : ∀ t : ℚ, 0 < t →
      MMP.Fourfold.IsLogResolution sX (B + t • G) π := by
    intro t ht
    have hsupp : (QDivisor.toRDivisor (B + t • G)).supp = (QDivisor.toRDivisor (B + G)).supp := by
      ext x
      simp only [SetLike.mem_coe, MMP.Mori.DivisorWithCoeffs.mem_supp_iff]
      refine exists_congr fun P => and_congr_left fun _ => ?_
      have h1 := hB.2.1 P
      have h2 := hG0 P
      rw [QDivisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor, MMP.Mori.DivisorWithCoeffs.coeff_add,
        MMP.Mori.DivisorWithCoeffs.coeff_add, MMP.Mori.DivisorWithCoeffs.coeff_smul, smul_eq_mul, ne_eq, ne_eq,
        Rat.cast_eq_zero, Rat.cast_eq_zero]
      constructor
      · intro h h'
        apply h
        have hb : B.coeff P = 0 := by linarith [mul_nonneg ht.le h2]
        have hg : G.coeff P = 0 := by linarith
        rw [hb, hg]; ring
      · intro h h'
        apply h
        have hb : B.coeff P = 0 := by nlinarith [mul_nonneg ht.le h2]
        have hg : G.coeff P = 0 := by
          by_contra hg
          have : 0 < t * G.coeff P := mul_pos ht (lt_of_le_of_ne h2 (Ne.symm hg))
          linarith
        rw [hb, hg]; ring
    exact ⟨⟨hπ.toIsSmoothResolution, hπ.isPureCodimOne_exceptionalSet,
      hsupp ▸ hπ.isSNCSubset⟩, hπp⟩
  have hcrit : ∀ t : ℚ, 0 < t → (IsLogCanonicalPair sX (B + t • G) ↔
      ∀ F, B₀.coeff F + t * Gπ.coeff F ≤ 1) := by
    intro t ht
    have hpair : MMP.Mori.IsPairWith sX 4 K (B + t • G) :=
      ⟨hPW.1, hPW.2.1, by rw [← add_assoc]; exact hPW.2.2.add (isQCartier_smul' hGq t)⟩
    have hpair' : MMP.Fourfold.IsPair sX (B + t • G) :=
      ⟨inferInstance, inferInstance, hpair.isPair, fun P => by
        rw [MMP.Mori.DivisorWithCoeffs.coeff_add, MMP.Mori.DivisorWithCoeffs.coeff_smul,
          smul_eq_mul]
        exact add_nonneg (hB.2.1 P) (mul_nonneg ht.le (hG0 P))⟩
    rw [MMP.Fourfold.isLogCanonicalPair_iff_forall_coeff_le_one sX hpair' (hres t ht) hY
      (hcrep t)]
    simp [MMP.Mori.DivisorWithCoeffs.coeff_add, MMP.Mori.DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  -- `(X, B + G)` is not lc
  have hbad : ∃ F, 1 < B₀.coeff F + Gπ.coeff F := by
    by_contra h
    push Not at h
    exact hGnlc (by simpa using (hcrit 1 one_pos).2 (fun F => by simpa using h F))
  classical
  set T := Gπ.support.filter fun F => 0 < Gπ.coeff F
  obtain ⟨F₁, hF₁⟩ := hbad
  have hF₁T : F₁ ∈ T := by
    have h1 := hd1 F₁
    simp only [T, Finset.mem_filter, Finsupp.mem_support_iff]
    refine ⟨fun h => ?_, by linarith⟩
    rw [MMP.Mori.DivisorWithCoeffs.coeff_apply Gπ F₁, h] at hF₁
    linarith
  -- the threshold
  set r : MMP.Mori.PrimeDivisor Y → ℚ := fun F => (1 - B₀.coeff F) / Gπ.coeff F
  set c := T.inf' ⟨F₁, hF₁T⟩ r
  have hTpos : ∀ F ∈ T, 0 < Gπ.coeff F := fun F hF => (Finset.mem_filter.mp hF).2
  have hcle : ∀ F ∈ T, c ≤ r F := fun F hF => Finset.inf'_le _ hF
  obtain ⟨F₀, hF₀T, hcF₀⟩ := Finset.exists_mem_eq_inf' ⟨F₁, hF₁T⟩ r
  have hg₀ := hTpos F₀ hF₀T
  -- no place of `T` is an lc place of `(X, B)`: `G` contains no lc centre
  have hT1 : ∀ F ∈ T, B₀.coeff F < 1 := by
    intro F hF
    refine lt_of_le_of_ne (hd1 F) fun h1 => ?_
    have hlc0 : IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) (E F) 0 := by
      have := hlog 0 F
      rw [h1] at this
      simpa using this
    refine hGc (E F).center ⟨E F, hlc0, rfl⟩ ?_
    exact centre_subset_supp_of_pos sX hY hbir hGq hGsupp hGπ F (hTpos F hF)
  have hc0 : 0 < c := by
    rw [show c = r F₀ from hcF₀]
    exact div_pos (by linarith [hT1 F₀ hF₀T]) hg₀
  have hc1 : c < 1 := by
    refine lt_of_le_of_lt (hcle F₁ hF₁T) ?_
    rw [div_lt_one (hTpos F₁ hF₁T)]
    linarith
  have hlcc : IsLogCanonicalPair sX (B + c • G) := by
    refine (hcrit c hc0).2 fun F => ?_
    by_cases hF : F ∈ T
    · have := hcle F hF
      rw [le_div_iff₀ (hTpos F hF)] at this
      linarith
    · have hg : Gπ.coeff F ≤ 0 := by
        by_contra hg
        push Not at hg
        exact hF (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hg.ne', hg⟩)
      have := hd1 F
      nlinarith
  have hF₀eq : B₀.coeff F₀ + c * Gπ.coeff F₀ = 1 := by
    rw [show c = r F₀ from hcF₀]
    simp only [r]
    field_simp
    ring
  refine ⟨c, hc0, hc1, hlcc, (E F₀).center, ⟨E F₀, ?_, rfl⟩, ?_⟩
  · have := hlog c F₀
    rw [show (1 - B₀.coeff F₀ - c * Gπ.coeff F₀ : ℚ) = 0 by linarith] at this
    simpa using this
  · have hsub : ((E F₀).center : Set X) ⊆ W := by
      by_contra h
      have := hcentre F₀ h
      nlinarith
    refine lt_of_le_of_ne hsub fun heq => ?_
    have hW' := hGc W hW.1
    exact hW' (heq ▸ centre_subset_supp_of_pos sX hY hbir hGq hGsupp hGπ F₀ hg₀)

/-- **The descent step.** If `L|_W` is not numerically trivial on a minimal lc centre `W`, there
is an lc pair `(X, B')` with an ample gap `a'L - (K_X + B')` and a minimal lc centre properly
contained in `W`. -/
private theorem exists_lt_of_not_isNumTrivialOn
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {L : Divisor X} (hL : L.IsNef ℂ sX)
    {B : QDivisor X} {a : ℚ} (hB : IsLogCanonicalPair sX B) (ha : 0 < a)
    (hample : (a • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsAmple)
    {W : IrreducibleCloseds X} (hW : IsMinimalLcCentre sX B W)
    (hntriv : ¬ IsNumTrivialOn sX hL.1 (W : Set X)) :
    ∃ (B' : QDivisor X) (a' : ℚ), IsLogCanonicalPair sX B' ∧ 0 < a' ∧
      (a' • Divisor.toQDivisor L - (Divisor.toQDivisor K + B')).IsAmple ∧
      ∃ W' : IrreducibleCloseds X, IsMinimalLcCentre sX B' W' ∧ W' < W := by
  obtain ⟨u, G, hau, hG0, ⟨β, hβ, φ, hφ⟩, hGc, hGW, hGnlc⟩ :=
    exists_concentrated_boundary sX hX hdim hK hL hB ha hample hW hntriv
  have hβ0 : (β : ℚ) ≠ 0 := by exact_mod_cast hβ.ne'
  have hG : G = (u • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)) +
      (β : ℚ)⁻¹ • Divisor.toQDivisor (MMP.Mori.principalDivisor φ) := by
    rw [hφ, inv_smul_smul₀ hβ0]; abel
  -- `G` is `ℚ`-Cartier: it is `uL - (K_X + B)` up to a principal `ℚ`-divisor
  have hGq : G.IsQCartier := by
    have hAq : (u • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsQCartier := by
      have h := isAmple_add_smul_of_isNef sX hX hample hL (t := u - a) (by linarith)
      obtain ⟨m, hm, D, hD, hDc, -⟩ := h
      refine ⟨m, by exact_mod_cast hm.ne', ?_⟩
      have : (u • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)) =
          a • Divisor.toQDivisor L - (Divisor.toQDivisor K + B) + (u - a) • Divisor.toQDivisor L := by
        rw [sub_smul]; abel
      rw [this, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ, ← hD]
      exact QDivisor.isCartierDivisor_toQDivisor.mpr hDc
    have hPq : ((β : ℚ)⁻¹ • Divisor.toQDivisor (MMP.Mori.principalDivisor φ)).IsQCartier :=
      ⟨β, by exact_mod_cast hβ.ne', by
        rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_inv_smul₀ hβ0]
        exact QDivisor.isCartierDivisor_toQDivisor.mpr
          (MMP.Mori.Divisor.isCartier_principalDivisor φ)⟩
    rw [hG]; exact hAq.add hPq
  obtain ⟨c, hc0, hc1, hBc, Z, hZ, hZW⟩ :=
    exists_lct_lt_one sX hX hdim hK hB hW hG0 hGq hGc hGW hGnlc
  refine ⟨B + c • G, a * (1 - c) + c * u, hBc, by nlinarith, ?_, ?_⟩
  · have h := isAmple_smul_add_principal sX hX hample (s := 1 - c) (by linarith) (-(c / β)) φ
    convert h using 1
    rw [hG]
    module
  · obtain ⟨W', hW', hW'Z⟩ := exists_isMinimalLcCentre_le sX hX hK hBc hZ
    exact ⟨W', hW', lt_of_le_of_lt hW'Z hZW⟩

/-- **The induction.** For every lc pair `(X, B)` with an ample gap `aL - (K_X + B)` and every
minimal lc centre `W`, `W ⊄ Bs|mL|` for all large `m`; by well-founded induction on `W`. -/
private theorem eventually_not_subset_baseLocus_of_minimal
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {L : Divisor X} (hL : L.IsNef ℂ sX)
    (W : IrreducibleCloseds X) : ∀ (B : QDivisor X) (a : ℚ), IsLogCanonicalPair sX B → 0 < a →
      (a • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsAmple →
      IsMinimalLcCentre sX B W →
        ∀ᶠ m : ℕ in atTop, ¬ (W : Set X) ⊆ (L.baseLocusOfMultiple m : Set X) := by
  have : IsNoetherian X := ⟨⟩
  have hwf : WellFounded ((· < ·) : IrreducibleCloseds X → IrreducibleCloseds X → Prop) :=
    (InvImage.wf (fun Z : IrreducibleCloseds X => (⟨Z, Z.isClosed⟩ : Closeds X))
      wellFounded_lt).mono fun a b h => by
        change (⟨a, a.isClosed⟩ : Closeds X) < ⟨b, b.isClosed⟩
        exact h
  induction W using hwf.induction with
  | _ W ih =>
  intro B a hB ha hample hW
  by_cases htriv : IsNumTrivialOn sX hL.1 (W : Set X)
  · exact eventually_not_subset_of_eventually_sections sX hX hK hL hB hample hW.1
      (eventually_sections_of_isNumTrivialOn sX hX hdim hK hL hB ha hample hW htriv)
  · obtain ⟨B', a', hB', ha', hample', W', hW', hlt⟩ :=
      exists_lt_of_not_isNumTrivialOn sX hX hdim hK hL hB ha hample hW htriv
    filter_upwards [ih W' hlt B' a' hB' ha' hample' hW'] with m hm hsub
    exact hm ((show (W' : Set X) ⊆ W from hlt.le).trans hsub)

end Setup

private theorem solution : ∀ {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X]
    (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    {L : Divisor X} (hL : L.IsNef ℂ sX) {a : ℚ} (ha : 0 < a)
    (hample : (a • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsAmple),
    ∀ᶠ m : ℕ in atTop, ∀ (n : ℕ) (E : DivisorOver ℂ sX),
      MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) E 0 →
        ¬ (E.center : Set X) ⊆ (L.baseLocusOfMultiple m : Set X) := by
  intro X _ _ _ _ sX _ hX hdim K hK B hB L hL a ha hample
  have hev : ∀ᶠ m : ℕ in atTop, ∀ W ∈ {W | IsMinimalLcCentre sX B W},
      ¬ (W : Set X) ⊆ (L.baseLocusOfMultiple m : Set X) :=
    (((lcCentres_finite sX hX hK hB).subset fun W hW => hW.1).eventually_all).2 fun W hW =>
      eventually_not_subset_baseLocus_of_minimal sX hX hdim hK hL W B a hB ha hample hW
  filter_upwards [hev] with m hm n E hE hsub
  obtain rfl : n = 4 := by
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hE
    rw [hdim] at this
    exact_mod_cast this.symm
  obtain ⟨W, hW, hWZ⟩ := exists_isMinimalLcCentre_le sX hX hK hB ⟨E, hE, rfl⟩
  exact hm W hW ((show (W : Set X) ⊆ E.center from hWZ).trans hsub)

end Proof_thm_mmp_lc_bpf_fourfold_centre_nonvanishing

end

@[expose] public section

open CategoryTheory AlgebraicGeometry Filter

namespace MMP.Fourfold

open MMP.Mori

/-- **Nonvanishing along lc centres for projective lc fourfolds.** Let `X` be a normal projective
complex fourfold with canonical divisor `K`, `(X, B)` a log canonical pair with `B` a
`ℚ`-divisor, and `L` a nef Cartier divisor with `aL - (K + B)` ample for some rational `a > 0`.
Then for every sufficiently large `m`, no lc centre of `(X, B)` (the centre of a divisor `E` over
`X` with `a(E, X, B) = 0`) is contained in the base locus of `|mL|`. -/
@[mmp "thm_mmp_lc_bpf_fourfold_centre_nonvanishing"]
public theorem not_center_subset_baseLocusOfMultiple
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    {L : Divisor X} (hL : L.IsNef ℂ sX) {a : ℚ} (ha : 0 < a)
    (hample : (a • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsAmple) :
    ∀ᶠ m : ℕ in atTop, ∀ (n : ℕ) (E : DivisorOver ℂ sX),
      MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) E 0 →
        ¬ (E.center : Set X) ⊆ (L.baseLocusOfMultiple m : Set X) :=
          by revert X sX hX hdim K hK B hB L hL a ha hample; first | exact Proof_thm_mmp_lc_bpf_fourfold_centre_nonvanishing.solution | exact Proof_thm_mmp_lc_bpf_fourfold_centre_nonvanishing.solution _ | exact Proof_thm_mmp_lc_bpf_fourfold_centre_nonvanishing.solution _ _ | exact Proof_thm_mmp_lc_bpf_fourfold_centre_nonvanishing.solution _ _ _ | exact Proof_thm_mmp_lc_bpf_fourfold_centre_nonvanishing.solution _ _ _ _

end MMP.Fourfold
