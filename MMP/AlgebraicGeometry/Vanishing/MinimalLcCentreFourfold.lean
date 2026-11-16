module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
public import MMP.AlgebraicGeometry.Positivity.SerreAmpleCartier
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltModification
public import MMP.AlgebraicGeometry.Vanishing.SncDirectImageCohomology
public import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
public import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStratum
public import MMP.AlgebraicGeometry.SubschemeOver
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceZero
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Projective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
public import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
public import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
public import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ForwardDiscrepancy
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Modules.ProjectionFormulaInvertible
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafTensor
public import MMP.AlgebraicGeometry.Positivity.SemiampleSections
public import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
public import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.DivisorOverRealization
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
public import MMP.AlgebraicGeometry.Resolution.Principalization.ResolutionPrincipalization
public import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
public import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Singularities.LcCentres
public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
public import MMP.AlgebraicGeometry.Morphisms.HProjective
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# Vanishing on a minimal lc centre of a projective lc fourfold

Let `(X, B)` be a log canonical pair, with `B` a `ℚ`-divisor, on a normal projective complex
fourfold, and put `D = K_X + B`. An *lc centre* of `(X, B)` is the centre on `X` of a divisor `E`
over `X` with log discrepancy `a(E, X, B) = 0`; it is *minimal* if it contains no other lc centre.
Let `W` be a minimal lc centre, with its reduced subscheme structure, and let `N` be a Cartier
divisor on `W` such that `N - D|_W` is ample as a `ℚ`-Cartier class. Then
`Hⁱ(W, 𝒪_W(N)) = 0` for every `i > 0`.

The ample gap is required only on `W`: the proof passes to a crepant dlt modification, a dlt
stratum `V` dominating `W` and a log resolution of `(V, B_V)`, applies the logarithmic
direct-image vanishing theorem there, and splits `𝒪_W → (p|_V)_* 𝒪_V` by a trace, using the
normality of `W`.

## Main results

* `MMP.Fourfold.isZero_Hgroup_lineBundle_of_minimal_lcCentre`

## Implementation notes

* The pair is `MMP.Intersection.IsLogCanonicalPair`; log discrepancies are
  `MMP.Intersection.IsLogDiscrepancy`, computed with forms of degree `4 = dim X`, and the centre
  of a divisor over `X` is `MMP.Mori.DivisorOver.center`.
* `W` is given abstractly: a reduced scheme with a closed immersion `ι : W ⟶ X` whose image is
  the centre. This determines `W` up to unique isomorphism over `X`.
* `D = K_X + B` is a `ℚ`-Cartier `ℚ`-divisor for the canonical divisor `K`, so its restriction
  to `W` is the rational class `(1/m) ι^* 𝒪_X(E)` for any Cartier divisor `E` with `E = m D`.
  "`N - D|_W` is ample as a rational class" is written: for some `m > 0`, some such `E` and some
  ample Cartier divisor `A` on `W`, `𝒪_W(mN - A) ≅ ι^* 𝒪_X(E)`, so that
  `m (N - D|_W) = A`. Ampleness is `Stacks.Ample.IsAmple` of `𝒪_W(A)` (Stacks 01PS), which agrees
  with Lazarsfeld's on the projective scheme `W`.
* `𝒪_W(N)` is `MMP.CartierDivisor.sheaf N` and cohomology is the derived-functor cohomology
  `Hgroup W.ringCatSheaf ⊤ i`.

## References

* [KollarMori] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, §2.3 (log
  discrepancies and lc pairs).
-/

@[expose] public section

section

namespace Proof_lem_mmp_lc_bpf_minimal_centre_vanishing_fourfold

open CategoryTheory AlgebraicGeometry
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

/-- Positive-degree cohomology vanishes as soon as its `k`-linear version does. -/
private theorem isZero_Hgroup_of_subsingleton {X : Scheme.{0}} {k : Type} [Field k]
    (f : X ⟶ Spec (.of k)) (F : X.Modules) (n : ℕ)
    (h : Subsingleton (cohomologyOverField k f F n)) :
    Limits.IsZero (Hgroup X.ringCatSheaf ⊤ n F) := by
  have := (cohomologyOverFieldAddEquivHgroup k f F n).symm.injective.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- A retract of an object with zero cohomology has zero cohomology. -/
private theorem isZero_Hgroup_of_retract {X : Scheme.{0}} {F G : X.Modules} (r : Retract F G)
    (n : ℕ) (h : Limits.IsZero (Hgroup X.ringCatSheaf ⊤ n G)) :
    Limits.IsZero (Hgroup X.ringCatSheaf ⊤ n F) :=
  by
  rw [Limits.IsZero.iff_id_eq_zero]
  have hr := (r.map (Hfunctor X.ringCatSheaf ⊤ n)).retract
  rw [← hr, h.eq_of_src ((r.map (Hfunctor X.ringCatSheaf ⊤ n)).r) 0, Limits.comp_zero]

/-- The zeroth right derived functor of the push-forward of modules is the push-forward. -/
private noncomputable def rightDerivedZeroPushforwardIso {X Y : Scheme.{0}} (f : X ⟶ Y)
    (F : X.Modules) :
    ((Scheme.Modules.pushforward f).rightDerived 0).obj F ≅ (Scheme.Modules.pushforward f).obj F :=
  haveI : (Scheme.Modules.pushforward f).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  haveI : (Scheme.Modules.pushforward f).Additive := Functor.additive_of_preserves_binary_products _
  (Functor.rightDerivedZeroIsoSelf _).app F

/-- `k`-linear cohomology of isomorphic modules is `k`-linearly isomorphic. -/
private noncomputable def cohomologyOverFieldLinearEquivOfIso {X : Scheme.{0}} {k : Type}
    [Field k] (f : X ⟶ Spec (.of k)) {F G : X.Modules} (e : F ≅ G) (n : ℕ) :
    cohomologyOverField k f F n ≃ₗ[k] cohomologyOverField k f G n :=
  ((ModuleCat.restrictScalars _).mapIso
    (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens))).rightDerived n).mapIso
      e)).toLinearEquiv

/-- A closed subscheme of a projective complex variety, irreducible and reduced, is a projective
complex variety. -/
private theorem isProjectiveVariety_comp_of_isClosedImmersion {X W : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [MMP.Mori.IsProjectiveVariety ℂ sX] [IsReduced W] [IrreducibleSpace W]
    (ι : W ⟶ X) [IsClosedImmersion ι] :
    MMP.Mori.IsProjectiveVariety ℂ (ι ≫ sX) := by
  have hX : AlgebraicGeometry.IsProjectiveVariety ℂ sX := ‹_›
  haveI : IsIntegral W := isIntegral_of_irreducibleSpace_of_isReduced W
  haveI := hX.toIsVariety
  refine { toIsIntegral := inferInstance, isProjective := ?_ }
  obtain ⟨n, i, hi, hisX⟩ := hX.isProjective
  exact ⟨n, ι ≫ i, inferInstance, by rw [Category.assoc, hisX]⟩

open MonoidalCategory MMP.Intersection.Scheme.Modules

/-- If `𝒪_W` is a retract of `G`, then a module `L` is a retract of `G ⊗ L`. -/
private noncomputable def retractTensorOfRetractUnit {W : Scheme.{0}} (L G : W.Modules)
    (r : Retract (𝟙_ W.Modules) G) : Retract L (G ⊗ L) :=
  (Retract.ofIso (λ_ L).symm).trans (r.map (tensorRight L))

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

open MMP.Mori in
/-- **Step 0 (normality).** A minimal lc centre of a projective lc complex fourfold is normal. -/
private theorem isNormal_of_minimal_lcCentre {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [MMP.Mori.IsProjectiveVariety ℂ sX] (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X}
    (hB : IsLogCanonicalPair sX B)
    {W : Scheme.{0}} [IsReduced W] (ι : W ⟶ X) [IsClosedImmersion ι]
    (hW : ∃ F : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) F 0 ∧
      Set.range ι = (F.center : Set X))
    (hmin : ∀ F : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) F 0 →
      (F.center : Set X) ⊆ Set.range ι → (F.center : Set X) = Set.range ι) :
    IsNormal W := by
  obtain ⟨F, hF0, hF⟩ := hW
  have hX : MMP.Mori.IsNormalVariety ℂ sX := hF0.1
  have hlc := isLcPair_of_isLogCanonicalPair hB hK
  have hBeff : B.IsEffective := hB.2.1
  have hproj : IsProjectiveMorphism sX :=
    (inferInstance : AlgebraicGeometry.IsProjectiveVariety ℂ sX).isProjective
  -- the discrepancy of a divisor over `X` with log discrepancy `0` is `-1`
  have hdisc : ∀ E : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) E 0 →
      MMP.Mori.IsDiscrepancy sX 4 K B E (-1) := by
    intro E hE
    obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hlc.1.isPair hK E
    have := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha hE
    have ha1 : a = -1 := by
      have : ((a : ℚ) : ℝ) = -1 := by linarith
      exact_mod_cast this
    exact ha1 ▸ ha
  obtain ⟨-, -, hnorm⟩ := MMP.Mori.IsLcPair.finite_lcCentres_and_isNormal_of_minimal hproj hlc hBeff
  have hmem : F.center ∈ {Z : TopologicalSpace.IrreducibleCloseds X |
      ∃ E : DivisorOver ℂ sX, E.center = Z ∧
      MMP.Mori.IsDiscrepancy sX 4 K B E (-1)} := ⟨F, rfl, hdisc F hF0⟩
  have hN := hnorm F.center hmem (by
    rintro Z ⟨E, rfl, hE⟩ hZ
    obtain ⟨E', hE'p, hE'v⟩ := DivisorOver.exists_isProper_valuation_eq hX E
    have hc : E'.center = E.center := by
      apply SetLike.coe_injective
      rw [DivisorOver.center_eq_closure_genericPoint, DivisorOver.center_eq_closure_genericPoint,
        MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hE'v]
    obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hlc.1.isPair hK E'
    have haa : a' = -1 := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hlc.1 hE'v ha' hE
    have hl := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha' hE'p
    rw [haa] at hl
    have hl0 : IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) E' 0 := by
      convert hl using 1; push_cast; ring
    have := hmin E' hl0 (by rw [hc, hF]; exact hZ)
    apply SetLike.coe_injective
    rw [← hc, this, hF])
  -- `W` is the reduced induced subscheme on its image
  have hker :
      ι.ker = Scheme.IdealSheafData.vanishingIdeal ⟨(F.center : Set X), F.center.isClosed⟩ := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    congr 1
    apply TopologicalSpace.Closeds.ext
    change closure (Set.range ι) = (F.center : Set X)
    rw [ι.isClosedEmbedding.isClosed_range.closure_eq, hF]
  set I := Scheme.IdealSheafData.vanishingIdeal ⟨(F.center : Set X), F.center.isClosed⟩
  have hle : I.subschemeι.ker ≤ ι.ker := by rw [Scheme.IdealSheafData.ker_subschemeι, hker]
  haveI : IsIso (IsClosedImmersion.lift I.subschemeι ι hle) :=
    IsClosedImmersion.isIso_lift I.subschemeι ι (by rw [Scheme.IdealSheafData.ker_subschemeι, hker])
  haveI := hN
  exact isNormal_of_isOpenImmersion (IsClosedImmersion.lift I.subschemeι ι hle)

open MMP.Mori in
/-- **Step 1a (the crepant identity on the dlt model, in Cartier form).** On a crepant dlt lift
`p : (Y, Δ) ⟶ (X, B)` with `E = m (K + B)` Cartier, the pull-back `p^* E` is
`m (K_Y + Δ)` for a canonical divisor `K_Y` of `Y`, and `𝒪_Y(p^* E) ≅ p^* 𝒪_X(E)`. -/
private theorem exists_cartier_crepant_identity {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X} {p : Y ⟶ X}
    {Δ : QDivisor Y} (hp : MMP.Fourfold.IsCrepantDltLift sX K B p Δ)
    (m : ℕ) (hm : 0 < m) (E : Divisor X)
    (hE : Divisor.toQDivisor E = (m : ℚ) • (Divisor.toQDivisor K + B)) (hEC : E.IsCartier) :
    ∃ (KY EY : Divisor Y), KY.IsCanonicalDivisor (p ≫ sX) 4 ∧
      Divisor.toQDivisor EY = (m : ℚ) • (Divisor.toQDivisor KY + Δ) ∧ EY.IsCartier ∧
      Nonempty (EY.divisorialSheaf ≅ (Scheme.Modules.pullback p).obj E.divisorialSheaf) := by
  classical
  have hlc := hp.isLogCanonicalPair
  have hX : MMP.Mori.IsNormalVariety ℂ sX := hlc.1.1
  have hY : MMP.Mori.IsNormalVariety ℂ (p ≫ sX) := hp.isDltPair.1.1.1
  have hbir : IsBirationalMorphism p := hp.isBirationalMorphism
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hp.isProjectiveMorphism
  haveI : IsDominant p := hbir.isDominant
  haveI : CompactSpace X := haveI := hX.1; QuasiCompact.compactSpace_of_compactSpace sX
  haveI : CompactSpace Y := haveI := hY.1; QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (p ≫ sX) := hY.1.toLocallyOfFiniteType
  have hn := hK.topologicalKrullDim_eq
  have hnY : topologicalKrullDim Y = (4 : ℕ) := by
    haveI := hX.1; haveI := hY.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hbir, hn]
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hσ0 := MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' p
    hbir.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn) hω0
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (p ≫ sX) hY hnY
  have hKY : (divisorOfForm (pullbackRationalPluriForms sX p ω)).IsCanonicalDivisor (p ≫ sX) 4 :=
    hK₀.of_linearlyEquivalent <| by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK₀ hσ0
  have hgen := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp p E
  set EY := E.pullback hEC hgen with hEYdef
  have hEYp : E.IsPullback p hgen EY := Divisor.isPullback_pullback hEC hgen
  obtain ⟨n, hcr⟩ := hp.isCrepantBoundary
  refine ⟨divisorOfForm (pullbackRationalPluriForms sX p ω), EY, hKY, ?_,
    Divisor.IsCartier.isCartier_pullback hEC p hgen,
    Divisor.nonempty_divisorialSheaf_pullback_iso hEC p hgen⟩
  ext P
  -- the discrepancy of `P` over `(X, B)` is `-Δ_P`, so its log discrepancy is `1 - Δ_P`
  let D : DivisorOver ℂ sX := ⟨Y, p, hY, hbir, P⟩
  have hdisc := hcr P
  have hn4 : n = 4 := by
    have h1 := hdisc.2.1.topologicalKrullDim_eq
    rw [hn] at h1
    exact_mod_cast h1.symm
  subst hn4
  have h1 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hdisc
    (show IsProper D.f from inferInstance)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have h2 : MMP.Intersection.IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) D
      (1 + (D.ordPullback ω : ℝ) - ∑ _i : Fin 1, (1 / (m : ℝ)) * (EY.coeff P : ℝ)) := by
    refine ⟨hX, inferInstance, ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, 1, fun _ => 1 / (m : ℝ),
      fun _ => E, fun _ => EY, fun _ => hEC, fun Γ => ?_, fun _ => ⟨hgen, hEYp⟩, rfl⟩
    have hEΓ : (E.coeff Γ : ℚ) = m * (K.coeff Γ + B.coeff Γ) := by
      have := congrArg (fun G : QDivisor X => G.coeff Γ) hE
      simp at this
      linear_combination this
    have hEΓ' : (E.coeff Γ : ℝ) = m * (K.coeff Γ + B.coeff Γ) := by exact_mod_cast hEΓ
    rw [QDivisor.coeff_toRDivisor, Fin.sum_univ_one, hEΓ', hω Γ]
    field_simp
  have heq := MMP.Threefold.Bridges.IsLogDiscrepancy.unique h1 h2
  have hord : (D.ordPullback ω : ℝ) =
      ((divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff P : ℝ) := by
    rw [coeff_divisorOfForm]
    rfl
  rw [hord, Fin.sum_univ_one] at heq
  have key : (EY.coeff P : ℝ) = m * ((divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff P
      + Δ.coeff P) := by
    field_simp at heq
    push_cast at heq
    linear_combination heq
  have key' : (EY.coeff P : ℚ) = m * ((divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff P
      + Δ.coeff P) := by exact_mod_cast key
  simpa [mul_add] using key'

open MMP.Mori in
/-- A `ℚ`-divisor whose components have their generic points in an snc subset `S` is snc: each
such component is one of the prime divisors whose union is `S`. -/
private theorem isSNC_of_forall_genericPoint_mem {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsLocallyNoetherian Y] [IsNormal Y] [LocallyOfFinitePresentation sY]
    (hsm : IsSmoothScheme sY) {S : TopologicalSpace.Closeds Y} (hS : IsSNCSubset sY S)
    (D : QDivisor Y) (hD : ∀ E, D E ≠ 0 → E.genericPoint ∈ S) : D.IsSNC sY := by
  classical
  rcases hS with rfl | ⟨s, hs, hsnc⟩
  · refine (DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℚ) sY hsm).of_support_subset
      fun E hE => ?_
    have h := hD E (Finsupp.mem_support_iff.1 hE)
    rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_bot] at h
    exact h.elim
  · refine hsnc.of_support_subset fun E hE => ?_
    have h := hD E (Finsupp.mem_support_iff.1 hE)
    rw [← SetLike.mem_coe, ← hs, Set.mem_iUnion₂] at h
    obtain ⟨E', hE', hm⟩ := h
    obtain rfl := MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hm
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply, hE']

open MMP.Mori in
/-- The discrepancy of a non-exceptional divisor `(Y, f, E)` over a pair `(X, Δ)` is
`-coeff_P(Δ)`, where `P` is the prime divisor of `X` with generic point `f(η_E)`. -/
private theorem exists_eq_neg_coeff_of_not_isExceptional {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {D : DivisorOver ℂ sX} {a : ℚ} (ha : IsDiscrepancy sX n K Δ D a) (hE : ¬ D.IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint = P.genericPoint ∧ a = -Δ.coeff P := by
  obtain ⟨hX, hK, m, hm, -, U, hU, τ, hτ, hmτ⟩ := ha
  obtain ⟨P, hv⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hE
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  rw [MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX hn hv τ,
    DivisorOver.ordPullback_ofPrimeDivisor hX hn P τ] at hmτ
  have hx : D.f D.E.genericPoint = P.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
  have hPU : (P.support ∩ (U : Set X)).Nonempty := by
    refine ⟨P.genericPoint, ?_, hx ▸ hU⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have e := hτ.2 P hPU
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  refine ⟨P, hx, mul_left_cancel₀ hm0 ?_⟩
  linear_combination hmτ + e

open MMP.Mori in
/-- A divisor over `(X, Δ)` with nonzero discrepancy is exceptional or lies over `Supp Δ`. -/
private theorem genericPoint_mem_of_isDiscrepancy_ne_zero {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {Y : Scheme.{0}} {f : Y ⟶ X} {hY : IsNormalVariety ℂ (f ≫ sX)} {hf : IsBirationalMorphism f}
    {E : MMP.Mori.PrimeDivisor Y} {a : ℚ} (ha : IsDiscrepancy sX n K Δ ⟨Y, f, hY, hf, E⟩ a)
    (ha0 : a ≠ 0) :
    E.genericPoint ∈ exceptionalSet f ⊔ (QDivisor.toRDivisor Δ).supp.preimage f.continuous := by
  by_cases hex : (⟨Y, f, hY, hf, E⟩ : DivisorOver ℂ sX).IsExceptional
  · exact Or.inl (MMP.Positivity.support_subset_exceptionalSet E hex
      (MMP.Flips.primeDivisor_genericPoint_mem_support E))
  obtain ⟨Q, hfE, hQ⟩ := exists_eq_neg_coeff_of_not_isExceptional ha hex
  refine Or.inr (DivisorWithCoeffs.mem_supp_iff.2 ⟨Q, ?_, ?_⟩)
  · rw [QDivisor.coeff_toRDivisor, Rat.cast_ne_zero]
    rintro h
    exact ha0 (by rw [hQ, h, neg_zero])
  · exact hfE ▸ MMP.Flips.primeDivisor_genericPoint_mem_support Q

open MMP.Mori in
/-- **An lc centre in the snc locus of a dlt pair is a boundary stratum.** Let `(Y, Δ)` be a dlt
pair whose boundary is snc on the smooth open complement `U` of a closed subset `Z`, and let `G`
be a divisor over `Y` with discrepancy `-1` whose centre has its generic point `y₀` in `U`. On
`U`, either `G` is a prime divisor, of coefficient one, or by the snc lower bound
`a(G) ≥ -1 + ∑_{y₀ ∈ D_i} (1 - a_i) + (codim y₀ - #{i : y₀ ∈ D_i})` the components through `y₀`
all have coefficient one and are `codim y₀` in number; a point of their intersection
generalizing `y₀` lies on as many components, hence has codimension at least `codim y₀`, and is
`y₀`. So `closure {y₀}` is an irreducible component of the intersection. -/
private theorem isDltStratum_closure_of_isDiscrepancy_eq_neg_one {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {Δ : QDivisor Y} (hdlt : MMP.Intersection.IsDltPair sY Δ) {n : ℕ} {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor sY n) (Z : TopologicalSpace.Closeds Y)
    (hZsm : IsSmoothScheme (Scheme.Opens.ι (Z.compl : Y.Opens) ≫ sY))
    (hZsnc : DivisorWithCoeffs.IsSNC (Scheme.Opens.ι (Z.compl : Y.Opens) ≫ sY)
      (MMP.Mori.inverseTransformDivisor (Scheme.Opens.ι (Z.compl : Y.Opens)) Δ))
    (G : DivisorOver ℂ sY) (hG : IsDiscrepancy sY n KY Δ G (-1))
    (hGZ : G.f G.E.genericPoint ∉ (Z : Set Y)) :
    MMP.Fourfold.IsDltStratum sY Δ (closure {G.f G.E.genericPoint}) := by
  classical
  have hY : IsNormalVariety ℂ sY := hdlt.1.1.1
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : CompactSpace Y := haveI := hY.1; QuasiCompact.compactSpace_of_compactSpace sY
  set U : Y.Opens := (Z.compl : Y.Opens) with hUdef
  set y₀ := G.f G.E.genericPoint with hy₀
  have hyU : y₀ ∈ U := hGZ
  haveI : Nonempty U := ⟨⟨y₀, hyU⟩⟩
  -- `(Y, Δ)` is a pair for `K_Y`
  have hPW : IsPairWith sY n KY Δ := by
    obtain ⟨hX, n', K', hK', hQ'⟩ := hdlt.1.1
    have hlin : K'.LinearlyEquivalent KY :=
      MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sY hX hK' hKY
    exact ⟨hX, hKY, hQ'.add_of_linearlyEquivalent hlin⟩
  have hcen : ((G.center : Set Y) ∩ U).Nonempty :=
    ⟨y₀, by rw [G.center_eq_closure_genericPoint]; exact subset_closure rfl, hyU⟩
  obtain ⟨hGUv, hGUb, E', hE', -, hiff⟩ :=
    DivisorOver.exists_restrict_isDiscrepancy_iff hPW G U hcen
  set GU : DivisorOver ℂ (U.ι ≫ sY) := ⟨_, G.f ∣_ U, hGUv, hGUb, E'⟩ with hGU
  have hGUd : IsDiscrepancy (U.ι ≫ sY) n (KY.restrictOpen U) (Δ.restrictOpen U) GU (-1) :=
    (hiff (-1)).mp hG
  set y₁ := GU.f GU.E.genericPoint with hy₁
  have hy₁₀ : U.ι y₁ = y₀ := by
    rw [hy₁, hy₀, ← hE', ← Scheme.Hom.comp_apply]
    change ((G.f ∣_ U) ≫ U.ι) E'.genericPoint = _
    rw [morphismRestrict_ι, Scheme.Hom.comp_apply]
    exact congrArg G.f (OpenWeilRestriction.genericPoint_primeDivisorMap _ E').symm
  have hUv : IsNormalVariety ℂ (U.ι ≫ sY) := hY.restrictOpen U
  have hKU : Divisor.IsCanonicalDivisor (U.ι ≫ sY) n (KY.restrictOpen U) :=
    hKY.restrictOpen hY U
  haveI : LocallyOfFiniteType (U.ι ≫ sY) := hUv.1.toLocallyOfFiniteType
  haveI : IsNoetherian Y := {}
  haveI : CompactSpace U :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have hsncU : (Δ.restrictOpen U).IsSNC (U.ι ≫ sY) := by
    rw [← MMP.Mori.inverseTransformDivisor_ι_eq_restrictOpen]
    exact hZsnc
  have hcl : closure {y₀} = (closure {y₀} : Set Y) := rfl
  by_cases hex : GU.IsExceptional
  · set S := (Δ.restrictOpen U).support with hS
    have hsncS : DivisorWithCoeffs.IsSNC (U.ι ≫ sY) (∑ E ∈ S, Finsupp.single E (1 : ℤ)) :=
      hsncU.of_support_subset fun E hE => by
        rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply] at hE
        by_contra hES
        apply hE
        exact Finset.sum_eq_zero fun E' hE' => by
          rw [Finsupp.single_apply, if_neg]
          rintro rfl
          exact hES hE'
    have hcoeff : ∀ E ∈ S, (Δ.restrictOpen U).coeff E ≤ 1 := fun E _ => by
      rw [DivisorWithCoeffs.coeff_restrictOpen]; exact hdlt.2.1 _
    obtain ⟨c, T, hc, hT, hc2, hTc, hTS, hTy, hbound⟩ :=
      MMP.Mori.le_isDiscrepancy_of_isSNC hUv hZsm hKU (S := S) subset_rfl hsncS hcoeff GU hex
        hGUd
    -- the bound forces every component through `y₁` to have coefficient one, and `#T = c`
    have hterm : ∀ E ∈ T, 0 ≤ 1 - (Δ.restrictOpen U).coeff E := fun E hE => by
      linarith [hcoeff E (hTS hE)]
    have hsum0 := Finset.sum_nonneg hterm
    have hTc' : (T.card : ℚ) ≤ c := by exact_mod_cast hTc
    have hsum : ∑ E ∈ T, (1 - (Δ.restrictOpen U).coeff E) = 0 := by linarith
    have hT1 : ∀ E ∈ T, (Δ.restrictOpen U).coeff E = 1 := fun E hE => by
      have := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum E hE
      linarith
    have hcard : T.card = c := by
      have : (c : ℚ) ≤ T.card := by linarith
      exact_mod_cast le_antisymm hTc (by exact_mod_cast this)
    set J := T.image (OpenWeilRestriction.primeDivisorMap U.ι) with hJ
    have hmemJ : ∀ y : U.toScheme, (∀ P ∈ J, U.ι y ∈ P.support) ↔ ∀ E ∈ T, y ∈ E.support := by
      intro y
      constructor
      · intro h E hE
        exact (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι E y).mp
          (h _ (Finset.mem_image_of_mem _ hE))
      · intro h P hP
        obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hP
        exact (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι E y).mpr
          (h E hE)
    have hy₀J : y₀ ∈ ⋂ P ∈ J, (P.support : Set Y) := by
      rw [Set.mem_iInter₂]
      intro P hP
      rw [← hy₁₀]
      exact (hmemJ y₁).mpr (fun E hE => hTy E hE) P hP
    have hJclosed : IsClosed (⋂ P ∈ J, (P.support : Set Y)) :=
      isClosed_biInter fun P _ => by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
    refine ⟨hdlt, J, ?_, ?_, ⟨y₀, hy₀J⟩, ⟨isIrreducible_singleton.closure,
      closure_minimal (Set.singleton_subset_iff.mpr hy₀J) hJclosed⟩, ?_⟩
    · rw [Finset.image_nonempty, ← Finset.card_pos, hcard]; omega
    · intro P hP
      obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hP
      rw [← DivisorWithCoeffs.coeff_restrictOpen, hT1 E hE]
    · rintro T' ⟨hT'irr, hT'J⟩ hle
      -- the generic point of `closure T'` is `y₀`
      have hT'cl : IsIrreducible (closure T') := hT'irr.closure
      set y' := hT'cl.genericPoint with hy'
      have hy'gen : closure {y'} = closure T' := by
        rw [hy', hT'cl.isGenericPoint_genericPoint_closure.def, closure_closure]
      have hsp : y' ⤳ y₀ := by
        rw [specializes_iff_mem_closure, hy'gen]
        exact subset_closure (hle (subset_closure rfl))
      have hy'U : y' ∈ U := hsp.mem_open U.isOpen hyU
      let y₂ : U.toScheme := ⟨y', hy'U⟩
      have hy₂ : U.ι y₂ = y' := rfl
      have hy'J : y' ∈ ⋂ P ∈ J, (P.support : Set Y) :=
        (closure_minimal hT'J hJclosed) (hy'gen ▸ subset_closure rfl)
      have hy₂T : ∀ E ∈ T, y₂ ∈ E.support := (hmemJ y₂).mp (fun P hP => by
        rw [hy₂]; exact Set.mem_iInter₂.mp hy'J P hP)
      -- `#T ≤ codim y₂`
      obtain ⟨N, z, j, hz, hj, -⟩ := MMP.Mori.exists_at_of_isSNC hsncS y₂
      have hN := MMP.Mori.coheight_eq_of_isRegularSystemOfParameters hz
      have hTN : T.card ≤ N := by
        let e : T → {G : MMP.Mori.PrimeDivisor U // G ∈ S ∧ y₂ ∈ G.support} :=
          fun E => ⟨E.1, hTS E.2, hy₂T E.1 E.2⟩
        have he : Function.Injective e := fun a b h => by
          have h' := congrArg (fun x => x.1) h
          exact Subtype.ext h'
        have := Fintype.card_le_of_injective (j ∘ e) (hj.comp he)
        simpa using this
      -- `y₂` generalizes `y₁`
      have hsp' : y₂ ⤳ y₁ := by
        rw [← U.ι.isOpenEmbedding.toIsInducing.specializes_iff, hy₂, hy₁₀]
        exact hsp
      have hy₂₁ : y₂ = y₁ := by
        by_contra hne
        have hle : y₁ ≤ y₂ := hsp'
        have hlt : y₁ < y₂ := lt_of_le_not_ge hle fun h => hne (hsp'.antisymm h).eq
        have hfin : Order.coheight y₂ < ⊤ := by rw [hN]; exact ENat.coe_lt_top N
        have := Order.coheight_strictAnti hlt hfin
        rw [hN, hy₁, ← hc, ← hcard] at this
        exact absurd (by exact_mod_cast this) (not_lt.mpr hTN)
      have hyy : y' = y₀ := by rw [← hy₂, hy₂₁, hy₁₀]
      rw [← hyy, hy'gen]
      exact subset_closure
  · obtain ⟨Q, hQy, hQa⟩ := exists_eq_neg_coeff_of_not_isExceptional hGUd hex
    have hQ1 : (Δ.restrictOpen U).coeff Q = 1 := by linarith
    set P := OpenWeilRestriction.primeDivisorMap U.ι Q with hP
    have hPgen : P.genericPoint = y₀ := by
      rw [hP, OpenWeilRestriction.genericPoint_primeDivisorMap, ← hy₁₀, hy₁, hQy]
    have hPsupp : (P.support : Set Y) = closure {y₀} := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hPgen]
    refine ⟨hdlt, {P}, Finset.singleton_nonempty _, ?_, ⟨y₀, ?_⟩, ⟨isIrreducible_singleton.closure,
      ?_⟩, ?_⟩
    · intro P' hP'
      rw [Finset.mem_singleton] at hP'
      subst hP'
      rw [hP, ← DivisorWithCoeffs.coeff_restrictOpen, hQ1]
    · simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left, hPsupp]
      exact subset_closure rfl
    · simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left, hPsupp]
      exact le_rfl
    · rintro T' ⟨-, hT'⟩ -
      simpa [hPsupp] using hT'

open MMP.Mori in
/-- **Step 1b (an lc centre is the image of a dlt stratum).** On a crepant dlt lift
`p : (Y, Δ) ⟶ (X, B)`, the centre on `X` of a divisor `F` over `X` with log discrepancy `0` is the
image of a boundary stratum of the dlt pair `(Y, Δ)`: the centre of `F` on `Y` is an lc centre of
`(Y, Δ)`, which lies in the snc locus of the dlt pair, where lc centres are strata. -/
private theorem exists_isDltStratum_image_eq {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X} {p : Y ⟶ X}
    {Δ : QDivisor Y} (hp : MMP.Fourfold.IsCrepantDltLift sX K B p Δ)
    (F : DivisorOver ℂ sX) (hF : IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) F 0) :
    ∃ S : Set Y, MMP.Fourfold.IsDltStratum (p ≫ sX) Δ S ∧ p.base '' S = (F.center : Set X) := by
  classical
  have hlc := hp.isLogCanonicalPair
  have hX : IsNormalVariety ℂ sX := hlc.1.1
  have hdltY := hp.isDltPair
  have hY : IsNormalVariety ℂ (p ≫ sX) := hdltY.1.1.1
  have hbir : IsBirationalMorphism p := hp.isBirationalMorphism
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hp.isProjectiveMorphism
  haveI : IsDominant p := hbir.isDominant
  haveI : CompactSpace X := haveI := hX.1; QuasiCompact.compactSpace_of_compactSpace sX
  haveI : CompactSpace Y := haveI := hY.1; QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (p ≫ sX) := hY.1.toLocallyOfFiniteType
  have hn := hK.topologicalKrullDim_eq
  have hnY : topologicalKrullDim Y = (4 : ℕ) := by
    haveI := hX.1; haveI := hY.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hbir, hn]
  obtain ⟨KY, hKY⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (p ≫ sX) hY hnY
  obtain ⟨n, hcr⟩ := hp.isCrepantBoundary
  have hn4 : n = 4 := by
    obtain ⟨P⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hnY (by norm_num)
    have h1 := (hcr P).2.1.topologicalKrullDim_eq
    rw [hn] at h1
    exact_mod_cast h1.symm
  subst hn4
  -- realize `F` over `Y`
  let F' : MMP.Flips.ProperDivisorOver ℂ sX := ⟨F, hF.2.1⟩
  obtain ⟨G, hGv, hGn, hGb, hGp, hGv'⟩ :=
    MMP.Flips.ProperDivisorOver.exists_comap_functionFieldMap_valuation_eq hX.1 p hY.1 hbir F'
  -- the discrepancy of `F` is `-1`, and so is that of `G` over `(Y, Δ)`
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hlc.1 hK F
  have ha1 : a = -1 := by
    have := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha hF
    have : ((a : ℚ) : ℝ) = -1 := by linarith
    exact_mod_cast this
  subst ha1
  obtain ⟨-, htr⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hlc.1 p hY hbir hK hKY
    (Or.inl hcr)
  have hGd : IsDiscrepancy (p ≫ sX) 4 KY Δ G.toDivisorOver (-1) :=
    (htr G.toDivisorOver F hGv.symm (-1)).mpr ha
  -- the centre of `G` lies in the snc locus
  obtain ⟨-, -, Z, hZsm, hZsnc, hZ⟩ := id hdltY
  have hGZ : G.f G.E.genericPoint ∉ (Z : Set Y) := by
    intro hy
    have hl := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hGd G.isProper
    have hc : (G.toDivisorOver.center : Set Y) ⊆ Z := by
      rw [DivisorOver.center_eq_closure_genericPoint]
      exact closure_minimal (Set.singleton_subset_iff.mpr hy) Z.isClosed
    have := hZ 4 G.toDivisorOver hc _ hl
    norm_num at this
  have hS := isDltStratum_closure_of_isDiscrepancy_eq_neg_one hdltY hKY Z hZsm hZsnc
    G.toDivisorOver hGd hGZ
  refine ⟨_, hS, ?_⟩
  -- `p(y₀)` is the generic point of the centre of `F`
  have hpy : p (G.f G.E.genericPoint) = F.f F.E.genericPoint := by
    have := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hGv'
    exact this
  rw [DivisorOver.center_eq_closure_genericPoint, ← hpy,
    ← p.isClosedMap.closure_image_eq_of_continuous p.continuous, Set.image_singleton]

/-- `div(φ^n) = n div(φ)`. -/
private theorem principalDivisor_pow {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X]
    (φ : (MMP.Mori.RationalFunctions X)ˣ) (n : ℕ) :
    MMP.Mori.principalDivisor (φ ^ n) = n • MMP.Mori.principalDivisor φ := by
  induction n with
  | zero => simp [MMP.Mori.principalDivisor_one]
  | succ n ih => rw [pow_succ, MMP.Mori.principalDivisor_mul, ih, succ_nsmul]

/-- A scheme of dimension zero has no prime divisor. -/
private theorem isEmpty_primeDivisor_of_topologicalKrullDim_eq_zero {X : Scheme.{0}}
    (h : topologicalKrullDim X = 0) : IsEmpty (MMP.Mori.PrimeDivisor X) := by
  refine ⟨fun P => ?_⟩
  let _ : PartialOrder X := specializationOrder X
  have hn : Order.krullDim X = 0 := by
    rw [← h]
    exact (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))).symm
  have h1 := Order.coheight_le_krullDim P.genericPoint
  rw [MMP.Mori.PrimeDivisor.coheight_genericPoint P, hn] at h1
  exact absurd h1 (by decide)

open MMP.Mori MMP.Fourfold in
/-- **One adjunction step in Cartier form.** If `(T, B_T)` is obtained from the normal variety
`(M, B_M)` by an adjunction step and `E_M = m (K_M + B_M)` is Cartier, then
`E_T = m (K_T + B_T)` is Cartier for a canonical divisor `K_T` of `T`, with
`𝒪_T(E_T) ≅ j^* 𝒪_M(E_M)`. In positive dimension, for a form `σ` with a simple pole along `T` and
Poincaré residue `ρ`, the divisor `E_M + m div(σ / ω)` is `m (div σ + B_M)`, whose pull-back is
`m (div ρ + B_T)`; in dimension zero every divisor on `T` vanishes, and a divisor linearly
equivalent to `E_M` avoiding the point `T` pulls back to `0`. -/
private theorem exists_cartier_adjunctionStep {M T : Scheme.{0}}
    {sM : M ⟶ Spec (.of ℂ)} [IsIntegral M] [IsLocallyNoetherian M] [IsNormal M]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    {BM : QDivisor M} {j : T ⟶ M} {BT : QDivisor T} (hj : IsAdjunctionStep sM BM j BT)
    (hM : IsNormalVariety ℂ sM)
    {e : ℕ} {KM : Divisor M} (hKM : KM.IsCanonicalDivisor sM e) (m : ℕ) (hm : 0 < m)
    (EM : Divisor M) (hEM : Divisor.toQDivisor EM = (m : ℚ) • (Divisor.toQDivisor KM + BM))
    (hEMC : EM.IsCartier) :
    ∃ (nT : ℕ) (KT ET : Divisor T), KT.IsCanonicalDivisor (j ≫ sM) nT ∧
      Divisor.toQDivisor ET = (m : ℚ) • (Divisor.toQDivisor KT + BT) ∧ ET.IsCartier ∧
      Nonempty (ET.divisorialSheaf ≅ (Scheme.Modules.pullback j).obj EM.divisorialSheaf) := by
  classical
  obtain ⟨hTv, P, -, hP, hci, -⟩ := id hj
  haveI := hci
  haveI : LocallyOfFiniteType sM := hM.1.toLocallyOfFiniteType
  haveI : CompactSpace M := haveI := hM.1; QuasiCompact.compactSpace_of_compactSpace sM
  haveI : LocallyOfFiniteType (j ≫ sM) := hTv.1.toLocallyOfFiniteType
  haveI : CompactSpace T := haveI := hTv.1; QuasiCompact.compactSpace_of_compactSpace (j ≫ sM)
  have hdimM := hKM.topologicalKrullDim_eq
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := by
    rcases e with _ | d
    · exact ((isEmpty_primeDivisor_of_topologicalKrullDim_eq_zero (by exact_mod_cast hdimM)).false
        P).elim
    · exact ⟨d, rfl⟩
  have hdim : topologicalKrullDim M = (d : WithBot ℕ∞) + 1 := by rw [hdimM]; push_cast; rfl
  have hdimT := MMP.Fourfold.topologicalKrullDim_eq_of_range_eq_support sM hdim j P hP
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (j ≫ sM) hTv hdimT
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- dimension zero: every divisor on `T` is zero
    haveI := isEmpty_primeDivisor_of_topologicalKrullDim_eq_zero (X := T) (by exact_mod_cast hdimT)
    have hsub : ∀ D D' : QDivisor T, D = D' := fun D D' => Finsupp.ext fun Q => isEmptyElim Q
    obtain ⟨U, hxU, φ, hφ⟩ := hEMC (j (genericPoint T))
    set E'' := EM - principalDivisor φ with hE''
    have hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ E''.supp := by
      intro Z hZ
      rw [MMP.Threefold.Mori.CanonUniq.componentGenericPoint_eq] at hZ
      obtain ⟨Γ, hΓ, hxΓ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
      apply hΓ
      rw [hE'', DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ ⟨_, hxΓ, hxU⟩, sub_self]
    have hE''C : E''.IsCartier := hEMC.sub (Divisor.isCartier_principalDivisor φ)
    have hlin : E''.LinearlyEquivalent EM :=
      ⟨φ⁻¹, by rw [hE'', MMP.Mori.principalDivisor_inv]; abel⟩
    refine ⟨0, KT, E''.pullback hE''C hgen, hKT, hsub _ _,
      Divisor.IsCartier.isCartier_pullback hE''C j hgen, ?_⟩
    obtain ⟨e⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hE''C j hgen
    exact ⟨e ≪≫ (Scheme.Modules.pullback j).mapIso hlin.divisorialSheafIso⟩
  · -- positive dimension: the residue different
    obtain ⟨Q⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdimT hd.ne'
    obtain ⟨σ, hσ0, hσP, -, ρ, hρ, hρ0, -⟩ :=
      MMP.Fourfold.exists_form_of_residue_order sM hM hdim j hTv P hP Q
    obtain ⟨φ, hφ⟩ : (divisorOfForm σ).LinearlyEquivalent KM := by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hM hKM (m := 1) hσ0
    set E' := EM + principalDivisor (φ ^ m) with hE'
    have hE'C : E'.IsCartier := hEMC.add (Divisor.isCartier_principalDivisor _)
    have hE'q : Divisor.toQDivisor E' = (m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + BM) := by
      have h1 : principalDivisor (φ ^ m) = m • (divisorOfForm σ - KM) := by
        rw [principalDivisor_pow, hφ]
      rw [hE', map_add, hEM, h1, map_nsmul, map_sub, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ,
        ← smul_add]
      congr 1
      abel
    have hD : (Divisor.toQDivisor (divisorOfForm σ) + BM).IsQCartier :=
      ⟨m, by exact_mod_cast hm.ne', E', hE'q, hE'C⟩
    obtain ⟨hgen, hpb⟩ :=
      hj.isPullback_divisorOfForm_add_of_isPoincareResidue hdim P hP σ hσ0 hσP ρ hρ hD
    obtain ⟨ET, hET, hETpb⟩ := hpb m hm E' hE'q hE'C
    have hKρ : (divisorOfForm ρ).IsCanonicalDivisor (j ≫ sM) d :=
      hKT.of_linearlyEquivalent <| by
        simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hTv hKT (m := 1) hρ0
    have hgen' : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ E'.supp :=
      fun Z hZ => hgen Z (by
        rwa [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hE'q] at hZ)
    have hETeq : ET = E'.pullback hE'C hgen' := (hETpb.pullback_eq hE'C).symm
    have hlin : E'.LinearlyEquivalent EM := ⟨φ ^ m, by rw [hE']; abel⟩
    refine ⟨d, divisorOfForm ρ, ET, hKρ, ?_, ?_, ?_⟩
    · rw [hET, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ]
    · rw [hETeq]; exact Divisor.IsCartier.isCartier_pullback hE'C j hgen'
    · obtain ⟨e⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hE'C j hgen'
      rw [hETeq]
      exact ⟨e ≪≫ (Scheme.Modules.pullback j).mapIso hlin.divisorialSheafIso⟩

open MMP.Mori in
/-- **Step 1c (iterated adjunction in Cartier form).** Along a flag of iterated adjunction data
ending at `(T, B_T)`, a Cartier divisor `E_Y = m (K_Y + Δ)` restricts to a Cartier divisor
`E_T = m (K_T + B_T)` for a canonical divisor `K_T` of `T`, with `𝒪_T(E_T) ≅ ι^* 𝒪_Y(E_Y)`: at
each step a rational top form with a simple pole along the component has a Poincaré residue, and
the different is the residue different. -/
private theorem exists_cartier_adjunction {Y T : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    {Δ : QDivisor Y} {ιT : T ⟶ Y} {BT : QDivisor T}
    (F : MMP.Fourfold.StratumAdjunctionData sY Δ ιT BT)
    {nY : ℕ} {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY nY) (m : ℕ) (hm : 0 < m)
    (EY : Divisor Y) (hEY : Divisor.toQDivisor EY = (m : ℚ) • (Divisor.toQDivisor KY + Δ))
    (hEYC : EY.IsCartier) :
    ∃ (nT : ℕ) (KT ET : Divisor T), KT.IsCanonicalDivisor (ιT ≫ sY) nT ∧
      Divisor.toQDivisor ET = (m : ℚ) • (Divisor.toQDivisor KT + BT) ∧ ET.IsCartier ∧
      Nonempty (ET.divisorialSheaf ≅ (Scheme.Modules.pullback ιT).obj EY.divisorialSheaf) := by
  suffices key : ∀ {S : Scheme.{0}} {ι : S ⟶ Y} {BS : QDivisor S}
      (G : MMP.Fourfold.StratumAdjunctionData sY Δ ι BS) [IsIntegral S] [IsLocallyNoetherian S]
      [IsNormal S], ∃ (nS : ℕ) (KS ES : Divisor S), KS.IsCanonicalDivisor (ι ≫ sY) nS ∧
        Divisor.toQDivisor ES = (m : ℚ) • (Divisor.toQDivisor KS + BS) ∧ ES.IsCartier ∧
        Nonempty (ES.divisorialSheaf ≅ (Scheme.Modules.pullback ι).obj EY.divisorialSheaf) from
    key F
  intro S ι BS G
  induction G with
  | refl h =>
    intro _ _ _
    refine ⟨nY, KY, EY, by rwa [Category.id_comp], hEY, hEYC,
      ⟨((Scheme.Modules.pullbackId (X := Y)).app _).symm⟩⟩
  | @step S T ι BS G j BT h ih =>
    intro _ _ _
    haveI : IsIntegral S := G.isNormalVariety.1.toIsIntegral
    haveI : IsNormal S := G.isNormalVariety.2
    haveI : IsLocallyNoetherian S := by
      have := G.isNormalVariety.1
      exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sY)
    obtain ⟨nS, KS, ES, hKS, hES, hESC, ⟨eS⟩⟩ := ih
    obtain ⟨nT, KT, ET, hKT, hET, hETC, ⟨eT⟩⟩ :=
      exists_cartier_adjunctionStep h G.isNormalVariety hKS m hm ES hES hESC
    refine ⟨nT, KT, ET, by rwa [Category.assoc], hET, hETC, ⟨eT ≪≫ ?_⟩⟩
    exact (Scheme.Modules.pullback j).mapIso eS ≪≫ (Scheme.Modules.pullbackComp j ι).app _

open MMP.Mori in
/-- **Step 1 (a dlt stratum over the centre, and adjunction).** Pass to the crepant dlt
modification `p : (Y, B_Y) ⟶ (X, B)` and a dlt stratum `V` of `(Y, B_Y)` dominating `W`.
Adjunction makes `(V, B_V)` a projective dlt pair with `K_V + B_V = (p|_V)^*(D|_W)`, recorded as
a Cartier divisor `E_V = m (K_V + B_V)` with `𝒪_V(E_V) ≅ g^* ι^* 𝒪_X(E)`. -/
private theorem exists_dltStratum_over_centre {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [MMP.Mori.IsProjectiveVariety ℂ sX] (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X}
    (hB : IsLogCanonicalPair sX B)
    {W : Scheme.{0}} [IsReduced W] (ι : W ⟶ X) [IsClosedImmersion ι]
    (hW : ∃ F : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) F 0 ∧
      Set.range ι = (F.center : Set X))
    (hmin : ∀ F : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) F 0 →
      (F.center : Set X) ⊆ Set.range ι → (F.center : Set X) = Set.range ι)
    (m : ℕ) (hm : 0 < m) (E : Divisor X)
    (hE : Divisor.toQDivisor E = (m : ℚ) • (Divisor.toQDivisor K + B)) (hEC : E.IsCartier) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (g : V ⟶ W) (_ : MMP.Mori.IsProjectiveVariety ℂ (g ≫ ι ≫ sX))
      (_ : IsProjectiveMorphism g) (_ : Function.Surjective g)
      (n : ℕ) (KV : Divisor V) (_ : KV.IsCanonicalDivisor (g ≫ ι ≫ sX) n) (BV : QDivisor V)
      (_ : MMP.Intersection.IsDltPair (g ≫ ι ≫ sX) BV) (EV : Divisor V),
      Divisor.toQDivisor EV = (m : ℚ) • (Divisor.toQDivisor KV + BV) ∧ EV.IsCartier ∧
      Nonempty (EV.divisorialSheaf ≅
        (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback ι).obj E.divisorialSheaf)) := by
  obtain ⟨F, hF0, hF⟩ := hW
  have hXp : AlgebraicGeometry.IsProjectiveVariety ℂ sX := inferInstance
  obtain ⟨Y, _, _, _, p, Δ, hp⟩ :=
    MMP.Fourfold.exists_isCrepantDltLift sX hXp hdim hK hB
  obtain ⟨KY, EY, hKY, hEY, hEYC, ⟨eY⟩⟩ :=
    exists_cartier_crepant_identity sX hK hp m hm E hE hEC
  obtain ⟨S, hS, hSim⟩ := exists_isDltStratum_image_eq sX hK hp F hF0
  obtain ⟨⟨⟨T, ιT, BT, hTr, ⟨FT⟩⟩, hdlt⟩, -⟩ :=
    MMP.Fourfold.IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair hS
  haveI : IsIntegral T := FT.isNormalVariety.1.toIsIntegral
  haveI : IsNormal T := FT.isNormalVariety.2
  haveI : IsLocallyNoetherian T := by
    have := FT.isNormalVariety.1
    exact LocallyOfFiniteType.isLocallyNoetherian (ιT ≫ p ≫ sX)
  haveI : IsClosedImmersion ιT := FT.isClosedImmersion
  have hdltT := hdlt FT hTr
  obtain ⟨nT, KT, ET, hKT, hET, hETC, ⟨eT⟩⟩ :=
    exists_cartier_adjunction (p ≫ sX) FT hKY m hm EY hEY hEYC
  -- the factorization `g : T ⟶ W` of `ιT ≫ p` through `ι`
  have hrange : Set.range (ιT ≫ p) = Set.range ι := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hF, ← hSim, hTr]
  have hker : ι.ker ≤ (ιT ≫ p).ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range ι,
      Scheme.Hom.ker_eq_vanishingIdeal_closure_range (ιT ≫ p)]
    apply le_of_eq
    congr 2
    exact hrange.symm
  let g : T ⟶ W := IsClosedImmersion.lift ι (ιT ≫ p) hker
  have hg : g ≫ ι = ιT ≫ p := IsClosedImmersion.lift_fac ι (ιT ≫ p) hker
  have hpp : IsProjectiveMorphism p := hp.isProjectiveMorphism
  have hgp : IsProjectiveMorphism (g ≫ ι) := by
    rw [hg]
    exact (MMP.isProjectiveMorphism_of_isClosedImmersion ιT).comp hpp
  have hgproj : IsProjectiveMorphism g := IsProjectiveMorphism.of_comp g ι hgp
  have hgs : Function.Surjective g := by
    intro w
    obtain ⟨t, ht⟩ : ι w ∈ Set.range (ιT ≫ p) := hrange ▸ ⟨w, rfl⟩
    refine ⟨t, ι.isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hg]
    exact ht
  have hVproj : MMP.Mori.IsProjectiveVariety ℂ (g ≫ ι ≫ sX) := by
    have hcomp : g ≫ ι ≫ sX = ιT ≫ p ≫ sX := by rw [← Category.assoc, hg, Category.assoc]
    rw [hcomp]
    haveI : MMP.Mori.IsProjectiveVariety ℂ (p ≫ sX) :=
      (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).2
        ⟨hp.isDltPair.1.1.1.1, hpp.comp hXp.isProjective⟩
    haveI : IrreducibleSpace T := inferInstance
    exact isProjectiveVariety_comp_of_isClosedImmersion (p ≫ sX) ιT
  have hcomp : g ≫ ι ≫ sX = ιT ≫ p ≫ sX := by rw [← Category.assoc, hg, Category.assoc]
  refine ⟨T, inferInstance, inferInstance, inferInstance, g, hVproj, hgproj, hgs, nT, KT,
    hcomp ▸ hKT, BT, hcomp ▸ hdltT, ET, hET, hETC, ⟨eT ≪≫ ?_⟩⟩
  exact (Scheme.Modules.pullback ιT).mapIso eY ≪≫
    ((Scheme.Modules.pullbackComp ιT p).app _) ≪≫
    (Scheme.Modules.pullbackCongr hg.symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp g ι).app _).symm

open MMP.Mori in
/-- **Step 2a (a projective log resolution and the crepant boundary).** A projective dlt pair
`(V, B_V)` with `E_V = m (K_V + B_V)` Cartier has a projective log resolution `q : Z ⟶ V`, with
`Z` a smooth projective variety, a canonical divisor `K_Z` and the crepant boundary `B_Z`,
`K_Z + B_Z = q^*(K_V + B_V)`: `B_Z` has snc support, coefficients at most one (log canonicity),
its negative part is `q`-exceptional (`B_V` is effective), and `q^* E_V = m (K_Z + B_Z)`. -/
private theorem exists_crepant_logResolution {V : Scheme.{0}}
    (sV : V ⟶ Spec (.of ℂ)) [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [MMP.Mori.IsProjectiveVariety ℂ sV]
    {n : ℕ} {KV : Divisor V} (hKV : KV.IsCanonicalDivisor sV n) {BV : QDivisor V}
    (hBV : MMP.Intersection.IsDltPair sV BV) (m : ℕ) (hm : 0 < m) (EV : Divisor V)
    (hEV : Divisor.toQDivisor EV = (m : ℚ) • (Divisor.toQDivisor KV + BV)) (hEVC : EV.IsCartier) :
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (_ : IsLocallyNoetherian Z) (_ : IsNormal Z)
      (q : Z ⟶ V), MMP.Mori.IsProjectiveVariety ℂ (q ≫ sV) ∧ IsSmoothScheme (q ≫ sV) ∧
      IsProper q ∧ IsBirationalMorphism q ∧
      ∃ (nZ : ℕ) (KZ : Divisor Z) (BZ : QDivisor Z) (EZ : Divisor Z),
        KZ.IsCanonicalDivisor (q ≫ sV) nZ ∧ BZ.IsSNC (q ≫ sV) ∧ (∀ P, BZ P ≤ 1) ∧
        (∀ P, BZ P < 0 → RationalMap.IsExceptional q.toRationalMap P) ∧
        Divisor.toQDivisor EZ = (m : ℚ) • (Divisor.toQDivisor KZ + BZ) ∧
        Nonempty (EZ.divisorialSheaf ≅ (Scheme.Modules.pullback q).obj EV.divisorialSheaf) := by
  classical
  have hVp : AlgebraicGeometry.IsProjectiveVariety ℂ sV := inferInstance
  have hlc := hBV.1
  have hV : MMP.Mori.IsNormalVariety ℂ sV := hlc.1.1
  haveI : LocallyOfFiniteType sV := hV.1.toLocallyOfFiniteType
  haveI : CompactSpace V := haveI := hV.1; QuasiCompact.compactSpace_of_compactSpace sV
  -- a projective log resolution of `(V, B_V)`
  set D := QDivisor.toRDivisor BV with hD
  have hI : D.suppIdeal ≠ ⊥ := fun h ↦ MMP.Fourfold.genericPoint_notMem_supp D <| by
    rw [← SetLike.mem_coe, ← D.coe_support_suppIdeal, h]
    simp
  obtain ⟨Z, q, hZv, hproj, hqb, hsm, -, -, hsnc0, -⟩ :=
    MMP.Resolution.exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap sV hV.1 _ hI
  have hsnc : IsSNCSubset (q ≫ sV) (exceptionalSet q ⊔ D.supp.preimage q.continuous) := by
    convert hsnc0 using 2
    rw [Scheme.IdealSheafData.support_comap]
    congr 1
  haveI : IsIntegral Z := hZv.toIsIntegral
  haveI : Smooth (q ≫ sV) := (isSmoothScheme_iff _).mp hsm
  haveI : IsNormal Z := isNormal_of_smooth_over_field (q ≫ sV)
  haveI : LocallyOfFiniteType (q ≫ sV) := hZv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (q ≫ sV)
  haveI : CompactSpace Z := haveI := hZv; QuasiCompact.compactSpace_of_compactSpace (q ≫ sV)
  haveI : IsProper q := IsProjective.isProper hproj
  haveI : IsDominant q := hqb.isDominant
  have hZn : MMP.Mori.IsNormalVariety ℂ (q ≫ sV) := ⟨hZv, inferInstance⟩
  -- `Z` is projective
  haveI := Stacks.Ample.isInvertibleModule_unit (Spec (.of ℂ))
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective sV _
    (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    (isQuasiProjective_of_isHQuasiProjective _
      (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.1 hVp.isProjective).1)
  haveI := hL
  have hqP : IsProjectiveMorphism q := isProjectiveMorphism_of_isProjective q L hLa hproj
  have hZp : MMP.Mori.IsProjectiveVariety ℂ (q ≫ sV) :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).2 ⟨hZv, hqP.comp hVp.isProjective⟩
  -- `K_V = div ω` and `K_Z = div q^* ω`
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hV hKV
  obtain rfl : divisorOfForm ω = KV := DivisorWithCoeffs.ext' hωK
  have hn := hKV.topologicalKrullDim_eq
  have hnZ : topologicalKrullDim Z = n := by
    haveI := hV.1; haveI := hZv
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV (q ≫ sV) hqb, hn]
  have hσ0 := MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' q
    hqb.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn) hω0
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (q ≫ sV) hZn hnZ
  have hKZ : (divisorOfForm (pullbackRationalPluriForms sV q ω)).IsCanonicalDivisor (q ≫ sV) n :=
    hK₀.of_linearlyEquivalent <| by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hZn hK₀ hσ0
  -- the crepant boundary
  have hEV' : Divisor.toQDivisor EV = (m : ℤ) • (Divisor.toQDivisor (divisorOfForm ω) + BV) := by
    rw [hEV, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ]
  have hQ : (Divisor.toQDivisor (divisorOfForm ω) + BV).IsQCartier :=
    ⟨m, by exact_mod_cast hm.ne', EV, hEV', hEVC⟩
  have hsupp := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier q hQ
  set PB := QDivisor.pullback (f := q) (Divisor.toQDivisor (divisorOfForm ω) + BV) hQ hsupp
    with hPB
  set KZ := divisorOfForm (pullbackRationalPluriForms sV q ω) with hKZdef
  set BZ := PB - Divisor.toQDivisor KZ with hBZ
  have hdisc : ∀ E, IsDiscrepancy sV n (divisorOfForm ω) BV ⟨Z, q, hZn, hqb, E⟩ (-BZ.coeff E) := by
    intro E
    have := MMP.Mori.isDiscrepancy_coeff_divisorOfForm_sub_pullback hV ω hω0 hKV BV hQ q hZn hqb E
    convert this using 1
    rw [hBZ, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_sub]
    ring
  obtain ⟨EZ, hEZ, hEZpb⟩ := QDivisor.isPullback_pullback (f := q) hQ hsupp m hm EV hEV' hEVC
  refine ⟨Z, inferInstance, inferInstance, inferInstance, q, hZp, hsm, inferInstance, hqb, n, KZ,
    BZ, EZ, hKZ, ?_, fun E => ?_, fun E hE => ?_, ?_,
    ⟨Divisor.IsPullback.divisorialSheafIso (hBc := hEVC) hEZpb⟩⟩
  · refine isSNC_of_forall_genericPoint_mem hsm hsnc BZ fun E hE => ?_
    exact genericPoint_mem_of_isDiscrepancy_ne_zero (hdisc E) (neg_ne_zero.mpr hE)
  · have hl := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hdisc E)
      (show IsProper q from inferInstance)
    have h0 := hlc.2.2 n _ _ hl
    have : ((BZ.coeff E : ℚ) : ℝ) ≤ 1 := by push_cast at h0 ⊢; linarith
    exact_mod_cast this
  · by_contra hex
    obtain ⟨Q, -, hQa⟩ := exists_eq_neg_coeff_of_not_isExceptional (hdisc E) hex
    have h1 : BZ.coeff E = BV.coeff Q := by linarith
    have h2 := hlc.2.1 Q
    change BZ.coeff E < 0 at hE
    linarith
  · rw [hEZ, hBZ, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ]
    congr 1
    abel

open MMP.Mori in
/-- **Step 2b (the round-up of the negative part).** For a `ℚ`-divisor `B` with coefficients at
most one, `C = {B} + B^{=1}` has coefficients in `[0, 1]` and support inside that of `B`, and
`A = ⌈-(B^{<1})⌉` is an effective divisor, supported where `B` is negative, with `A = C - B`. -/
private theorem exists_roundUp_decomposition {Z : Scheme.{0}} (B : QDivisor Z)
    (hB : ∀ P, B P ≤ 1) :
    ∃ (C : QDivisor Z) (A : Divisor Z), (∀ P, 0 ≤ C P) ∧ (∀ P, C P ≤ 1) ∧
      (∀ P, C P ≠ 0 → B P ≠ 0) ∧ (∀ P, 0 ≤ A P) ∧ (∀ P, A P ≠ 0 → B P < 0) ∧
      Divisor.toQDivisor A = C - B := by
  classical
  refine ⟨B.mapCoeffs (fun c => if c = 1 then 1 else Int.fract c) (by simp),
    B.mapCoeffs (fun c => if c = 1 then 0 else -⌊c⌋) (by simp), fun P => ?_, fun P => ?_,
    fun P hP => ?_, fun P => ?_, fun P hP => ?_, ?_⟩
  · change 0 ≤ (if B P = 1 then (1 : ℚ) else Int.fract (B P))
    split_ifs
    exacts [zero_le_one, Int.fract_nonneg _]
  · change (if B P = 1 then (1 : ℚ) else Int.fract (B P)) ≤ 1
    split_ifs
    exacts [le_rfl, (Int.fract_lt_one _).le]
  · change (if B P = 1 then (1 : ℚ) else Int.fract (B P)) ≠ 0 at hP
    intro h0
    rw [h0] at hP
    simp at hP
  · change (0 : ℤ) ≤ (if B P = 1 then (0 : ℤ) else -⌊B P⌋)
    split_ifs with h1
    · exact le_rfl
    · have : B P < 1 := lt_of_le_of_ne (hB P) h1
      have : ⌊B P⌋ ≤ 0 := Int.floor_le_iff.mpr (by simpa using this)
      omega
  · change (if B P = 1 then (0 : ℤ) else -⌊B P⌋) ≠ 0 at hP
    split_ifs at hP with h1
    · exact absurd rfl hP
    · by_contra hneg
      push Not at hneg
      have hlt : B P < 1 := lt_of_le_of_ne (hB P) h1
      have : ⌊B P⌋ = 0 := Int.floor_eq_iff.mpr ⟨by simpa using hneg, by simpa using hlt⟩
      exact hP (by rw [this, neg_zero])
  · ext P
    change ((if B P = 1 then (0 : ℤ) else -⌊B P⌋ : ℤ) : ℚ) =
      (if B P = 1 then (1 : ℚ) else Int.fract (B P)) - B P
    split_ifs with h1
    · rw [h1]; simp
    · rw [Int.fract]; push_cast; ring

open MMP.Mori in
/-- **Step 2c (Hartogs).** For a proper birational morphism `q : Z ⟶ V` of normal varieties and
an effective Cartier divisor `A` on `Z` all of whose components are `q`-exceptional,
`q_* 𝒪_Z(A) = 𝒪_V`: this is the push-forward of `𝒪_Z(q^* 0 + A)`. -/
private theorem nonempty_pushforward_divisorialSheaf_iso_unit {Z V : Scheme.{0}}
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral V] [IsLocallyNoetherian V]
    [IsNormal V] (sV : V ⟶ Spec (.of ℂ)) (hV : MMP.Mori.IsVariety ℂ sV) (q : Z ⟶ V)
    (hZ : MMP.Mori.IsVariety ℂ (q ≫ sV)) [IsProper q] (hq : IsBirationalMorphism q)
    (A : Divisor Z) (hAC : A.IsCartier) (hA0 : ∀ P, 0 ≤ A P)
    (hAexc : ∀ P, A P ≠ 0 → RationalMap.IsExceptional q.toRationalMap P) :
    Nonempty ((Scheme.Modules.pushforward q).obj A.divisorialSheaf ≅ 𝟙_ V.Modules) := by
  haveI : IsDominant q := hq.isDominant
  have hgen0 := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp q (0 : Divisor V)
  obtain ⟨e, -⟩ := MMP.Mori.Divisor.exists_iso_pushforward_divisorialSheaf_add_of_isExceptional
    sV q hV hZ hq 0 Divisor.isCartier_zero hgen0 0 (Divisor.isPullback_zero hgen0) A hAC
    (fun P => hA0 P) (fun P hP => hAexc P hP)
  exact ⟨(Scheme.Modules.pushforward q).mapIso
    (eqToIso (congrArg Divisor.divisorialSheaf (zero_add A).symm)) ≪≫ e.symm ≪≫
      Divisor.divisorialSheafZeroIso⟩

open MMP.Mori in
/-- **An invertible module is `𝒪(D)` for a Cartier divisor `D`**: the divisor of a local frame
has the inverse transition functions as local equations. -/
private theorem exists_isCartier_divisorialSheaf_iso_of_isInvertible {Y : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    ∃ D : Divisor Y, D.IsCartier ∧ Nonempty (D.divisorialSheaf ≅ L) := by
  have := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := Y.toRingedSpace) L
  have : ∀ z : Y.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace z) :=
    fun z => Y.isLocalRing z
  choose W hW a ha using fun y : Y =>
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := Y.toRingedSpace) L y
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  let F : MMP.Mori.LocalFrame L :=
    { W := W, mem := hW, a := a, isLocalGenerator := fun y V hV => ha y V hV, base := y₀ }
  exact ⟨F.divisor, fun y => ⟨F.W y, F.mem y, _, F.isLocalEquation_divisor y⟩,
    ⟨(@asIso _ _ _ _ F.toDivisorialSheaf F.isIso_toDivisorialSheaf).symm⟩⟩

open MMP.Mori in
/-- **Step 2d (a Cartier divisor for a pulled-back line bundle).** On a quasi-compact normal
integral Noetherian scheme `Z`, the pull-back of the line bundle of a Cartier divisor `N` along
any morphism `h : Z ⟶ W` is `𝒪_Z(D)` for a Cartier divisor `D`. -/
private theorem exists_isCartier_divisorialSheaf_iso_pullback_lineBundle {Z W : Scheme.{0}}
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] (h : Z ⟶ W)
    (N : W.CartierDivisor) :
    ∃ D : Divisor Z, D.IsCartier ∧
      Nonempty (D.divisorialSheaf ≅ (Scheme.Modules.pullback h).obj (MMP.CartierDivisor.sheaf N)) :=
          by
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible W.toRingedSpace.presheaf
      (structureSheafRing W.toRingedSpace).property (MMP.CartierDivisor.sheaf N) :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
      (MMP.CartierDivisor.isInvertibleModule_sheaf N)
  exact exists_isCartier_divisorialSheaf_iso_of_isInvertible _

open MMP.Mori in
/-- The pull-back along a dominant morphism of linearly equivalent Cartier divisors are linearly
equivalent: `f^*(D + div φ) = f^* D + div(f^* φ)`. -/
private theorem linearlyEquivalent_pullback {Z W : Scheme.{0}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [CompactSpace W] (h : Z ⟶ W) [IsDominant h] {D₁ D₂ : Divisor W}
    (hD₁ : D₁.IsCartier) (hD₂ : D₂.IsCartier) (hlin : D₁.LinearlyEquivalent D₂) :
    Divisor.LinearlyEquivalent
      (D₁.pullback hD₁ (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp h D₁))
      (D₂.pullback hD₂ (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp h D₂)) := by
  obtain ⟨φ, hφ⟩ := hlin
  have hgen := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp h
  have h1 := (Divisor.isPullback_pullback hD₂ (hgen D₂)).add hD₂
    (Divisor.isCartier_principalDivisor φ) (hgen _)
    (Divisor.isPullback_principalDivisor (f := h) φ (hgen _))
  have hD : D₁ = D₂ + principalDivisor φ := by rw [← hφ]; abel
  have h2 := h1.of_eq hD.symm (hB₂ := hgen D₁)
  have h3 := h2.eq hD₁ (Divisor.isPullback_pullback hD₁ (hgen D₁))
  exact ⟨_, by rw [← h3]; abel⟩

open MMP.Mori in
/-- On a quasi-compact normal integral Noetherian scheme every line bundle of a Cartier divisor is
`𝒪(D)` for a Cartier divisor `D`. -/
private theorem exists_isCartier_divisorialSheaf_iso_lineBundle {W : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] (N : W.CartierDivisor) :
    ∃ D : Divisor W, D.IsCartier ∧ Nonempty (D.divisorialSheaf ≅ MMP.CartierDivisor.sheaf N) := by
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible W.toRingedSpace.presheaf
      (structureSheafRing W.toRingedSpace).property (MMP.CartierDivisor.sheaf N) :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
      (MMP.CartierDivisor.isInvertibleModule_sheaf N)
  exact exists_isCartier_divisorialSheaf_iso_of_isInvertible _

open MMP.Mori in
/-- `𝒪_W(k D_N) ≅ 𝒪_W(k N)` for `k ≥ 1` when `𝒪_W(D_N) ≅ 𝒪_W(N)`. -/
private theorem nonempty_divisorialSheaf_nsmul_iso {W : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] (N : W.CartierDivisor) {D : Divisor W}
    (hD : D.IsCartier) (e : D.divisorialSheaf ≅ MMP.CartierDivisor.sheaf N) (k : ℕ) (hk : 0 < k) :
    Nonempty ((k • D).divisorialSheaf ≅ MMP.CartierDivisor.sheaf (k • N)) := by
  induction k, hk using Nat.le_induction with
  | base =>
    exact ⟨eqToIso (congrArg Divisor.divisorialSheaf (show Nat.succ 0 • D = D by simp)) ≪≫ e ≪≫
      eqToIso (congrArg MMP.CartierDivisor.sheaf (show N = Nat.succ 0 • N by simp))⟩
  | succ k hk ih =>
    obtain ⟨ek⟩ := ih
    exact ⟨eqToIso (congrArg Divisor.divisorialSheaf (succ_nsmul D k)) ≪≫
      ((hD.nsmul k).divisorialSheafTensorIso hD).symm ≪≫
      tensorIso ek e ≪≫ MMP.CartierDivisorSheaf.sheafMulIso _ _ ≪≫
      eqToIso (congrArg MMP.CartierDivisor.sheaf (succ_nsmul N k).symm)⟩

open MMP.Mori in
/-- **Step 2e (the class computation).** If `𝒪_Z(E) ≅ h^* 𝒪_W(mN - A)`, `𝒪_Z(N') ≅ h^* 𝒪_W(N)`
and `𝒪_Z(A') ≅ h^* 𝒪_W(A)` for Cartier divisors `E`, `N'`, `A'` on `Z` and `h` dominant onto a
normal `W`, then `E + A' ∼ m N'`: realize `𝒪_W(N)`, `𝒪_W(A)`, `𝒪_W(mN - A)` by Cartier divisors
`N_W`, `A_W`, `G_W` of `W`, for which `G_W + A_W ∼ m N_W` since both have divisorial sheaf
`𝒪_W(mN)`, and pull back along `h`. -/
private theorem linearlyEquivalent_add_of_iso_pullback {Z W : Scheme.{0}}
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] (h : Z ⟶ W) [IsDominant h]
    (N A : W.CartierDivisor) (m : ℕ) (hm : 0 < m) {E N' A' : Divisor Z}
    (hE : Nonempty (E.divisorialSheaf ≅ (Scheme.Modules.pullback h).obj (MMP.CartierDivisor.sheaf (m
        • N - A))))
    (hN' : Nonempty (N'.divisorialSheaf ≅ (Scheme.Modules.pullback h).obj (MMP.CartierDivisor.sheaf
        N)))
    (hA' : Nonempty (A'.divisorialSheaf ≅ (Scheme.Modules.pullback h).obj (MMP.CartierDivisor.sheaf
        A))) :
    (E + A').LinearlyEquivalent (m • N') := by
  have hgen := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp h
  obtain ⟨NW, hNW, ⟨eN⟩⟩ := exists_isCartier_divisorialSheaf_iso_lineBundle N
  obtain ⟨AW, hAW, ⟨eA⟩⟩ := exists_isCartier_divisorialSheaf_iso_lineBundle A
  obtain ⟨GW, hGW, ⟨eG⟩⟩ := exists_isCartier_divisorialSheaf_iso_lineBundle (m • N - A)
  -- the relation on `W`
  obtain ⟨emN⟩ := nonempty_divisorialSheaf_nsmul_iso N hNW eN m hm
  have hW : (GW + AW).LinearlyEquivalent (m • NW) :=
    MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
      ((hGW.divisorialSheafTensorIso hAW).symm ≪≫ tensorIso eG eA ≪≫
        MMP.CartierDivisorSheaf.sheafMulIso _ _ ≪≫
        eqToIso (congrArg MMP.CartierDivisor.sheaf (sub_add_cancel (m • N) A)) ≪≫ emN.symm)
  -- comparison of the divisors on `Z` with the pull-backs
  have hcmp : ∀ {D : Divisor W} (hD : D.IsCartier) {D' : Divisor Z} (L : W.Modules)
      (_ : Nonempty (D.divisorialSheaf ≅ L))
      (_ : Nonempty (D'.divisorialSheaf ≅ (Scheme.Modules.pullback h).obj L)),
      D'.LinearlyEquivalent (D.pullback hD (hgen D)) := by
    intro D hD D' L ⟨e₁⟩ ⟨e₂⟩
    obtain ⟨e₃⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hD h (hgen D)
    exact MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
      (e₂ ≪≫ (Scheme.Modules.pullback h).mapIso e₁.symm ≪≫ e₃.symm)
  have hE1 := hcmp hGW _ ⟨eG⟩ hE
  have hA1 := hcmp hAW _ ⟨eA⟩ hA'
  have hN1 := hcmp hNW _ ⟨eN⟩ hN'
  -- pull back the relation on `W`
  have hpb := linearlyEquivalent_pullback h (hGW.add hAW) (hNW.nsmul m) hW
  have hadd : (GW + AW).pullback (hGW.add hAW) (hgen _) =
      GW.pullback hGW (hgen _) + AW.pullback hAW (hgen _) :=
    (((Divisor.isPullback_pullback hGW (hgen GW)).add hGW hAW (hgen _)
      (Divisor.isPullback_pullback hAW (hgen AW))).eq (hGW.add hAW)
      (Divisor.isPullback_pullback _ _)).symm
  have hsmul : (m • NW).pullback (hNW.nsmul m) (hgen _) = m • NW.pullback hNW (hgen _) := by
    have h1 := (Divisor.isPullback_pullback hNW (hgen NW)).zsmul hNW (m : ℤ) (hgen _)
    have h2 := h1.of_eq (natCast_zsmul NW m) (hB₂ := hgen _)
    have h3 := h2.eq (hNW.nsmul m) (Divisor.isPullback_pullback (hNW.nsmul m) (hgen _))
    rw [← h3, natCast_zsmul]
  rw [hadd, hsmul] at hpb
  obtain ⟨φ, hφ⟩ := hN1
  have hNm : (m • N').LinearlyEquivalent (m • NW.pullback hNW (hgen _)) :=
    ⟨φ ^ m, by rw [principalDivisor_pow, ← hφ, smul_sub]⟩
  exact ((hE1.add hA1).trans hpb).trans hNm.symm

/-- **Step 2f (the projection formula).** For a morphism `h : Z ⟶ W`, an `𝒪_Z`-module `F` and
an invertible `𝒪_W`-module `L`, `h_*(F ⊗ h^* L) ≅ h_* F ⊗ L`. -/
private theorem nonempty_pushforward_tensor_pullback_iso {Z W : Scheme.{0}} (h : Z ⟶ W)
    (F : Z.Modules) (L : W.Modules) [Stacks.Ample.IsInvertibleModule W L] :
    Nonempty ((Scheme.Modules.pushforward h).obj (F ⊗ (Scheme.Modules.pullback h).obj L) ≅
      (Scheme.Modules.pushforward h).obj F ⊗ L) := by
  haveI := MMP.SemiampleSections.isIso_projectionFormulaNatTrans h L
  exact ⟨(asIso ((MMP.SemiampleSections.projectionFormulaNatTrans h L).app F)).symm⟩

open MMP.Mori in
/-- **Step 2 (log resolution, Hartogs and the projection formula).** Let `(V, B_V)` be a
projective dlt pair over the projective variety `W`, through a projective morphism `g`, with
`m (K_V + B_V) = E_V` Cartier, `𝒪_V(E_V) ≅ g^* 𝓔`, and let `𝒪_W(mN - A) ≅ 𝓔` with `A` ample.
On a projective log resolution `q : Z ⟶ V`, with `K_Z + B_Z = q^*(K_V + B_V)`,
`A_Z = ⌈-(B_Z^{<1})⌉`, `C = {B_Z} + B_Z^{=1}` and `M = h^* N + A_Z` for `h = q ≫ g`, the
boundary `C` is snc, `m (M - (K_Z + C)) ∼ h^* A`, and `h_* 𝒪_Z(M) ≅ g_* 𝒪_V ⊗ 𝒪_W(N)`. -/
private theorem exists_logResolution_pushforward_iso {W : Scheme.{0}}
    (sW : W ⟶ Spec (.of ℂ)) [MMP.Mori.IsProjectiveVariety ℂ sW]
    {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] (g : V ⟶ W)
    [MMP.Mori.IsProjectiveVariety ℂ (g ≫ sW)] (hg : IsProjectiveMorphism g)
    {n : ℕ} {KV : Divisor V} (hKV : KV.IsCanonicalDivisor (g ≫ sW) n) {BV : QDivisor V}
    (hBV : MMP.Intersection.IsDltPair (g ≫ sW) BV) (m : ℕ) (hm : 0 < m) (EV : Divisor V)
    (hEV : Divisor.toQDivisor EV = (m : ℚ) • (Divisor.toQDivisor KV + BV)) (hEVC : EV.IsCartier)
    (𝓔 : W.Modules) (heV : Nonempty (EV.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj 𝓔))
    (N A : W.CartierDivisor) (hNA : Nonempty (MMP.CartierDivisor.sheaf (m • N - A) ≅ 𝓔))
    [IsNormal W] (hgs : Function.Surjective g) :
    ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of ℂ)) (_ : MMP.Mori.IsProjectiveVariety ℂ sZ)
      (_ : IsSmoothScheme sZ) (_ : IsLocallyNoetherian Z) (_ : IsNormal Z) (h : Z ⟶ W)
      (_ : h ≫ sW = sZ) (_ : IsProjective h) (n : ℕ) (KZ : Divisor Z)
      (_ : KZ.IsCanonicalDivisor sZ n) (C : QDivisor Z) (_ : C.IsSNC sZ) (_ : ∀ P, 0 ≤ C P)
      (_ : ∀ P, C P ≤ 1) (M : Divisor Z) (_ : M.IsCartier),
      (∃ m' : ℕ, 0 < m' ∧ ∃ D : Divisor Z,
        Divisor.toQDivisor D = (m' : ℚ) • (Divisor.toQDivisor M - (Divisor.toQDivisor KZ + C)) ∧
        Nonempty (D.divisorialSheaf ≅ (Scheme.Modules.pullback h).obj (MMP.CartierDivisor.sheaf A)))
            ∧
      Nonempty ((Scheme.Modules.pushforward h).obj M.divisorialSheaf ≅
        (Scheme.Modules.pushforward g).obj (𝟙_ V.Modules) ⊗ MMP.CartierDivisor.sheaf N) := by
  classical
  obtain ⟨Z, _, _, _, q, hZp, hZs, hqp, hqb, nZ, KZ, BZ, EZ, hKZ, hBZ, hB1, hBexc, hEZ, ⟨eZ⟩⟩ :=
    exists_crepant_logResolution (g ≫ sW) hKV hBV m hm EV hEV hEVC
  obtain ⟨C, A₀, hC0, hC1, hCB, hA0, hAneg, hAC⟩ := exists_roundUp_decomposition BZ hB1
  haveI : IsProper q := hqp
  have hWv : AlgebraicGeometry.IsProjectiveVariety ℂ sW := inferInstance
  haveI : IsIntegral W := hWv.toIsIntegral
  haveI : LocallyOfFiniteType sW := hWv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : CompactSpace W := haveI := hWv.toIsVariety; QuasiCompact.compactSpace_of_compactSpace sW
  have hZv : AlgebraicGeometry.IsProjectiveVariety ℂ (q ≫ g ≫ sW) := hZp
  haveI : CompactSpace Z := haveI := hZv.toIsVariety;
    QuasiCompact.compactSpace_of_compactSpace (q ≫ g ≫ sW)
  set h : Z ⟶ W := q ≫ g with hh
  have hqs : Function.Surjective q := by
    haveI : IsDominant q := hqb.isDominant
    have := q.isClosedMap.isClosed_range
    have hd := q.denseRange
    intro v
    have h2 : Set.range q = Set.univ := by rw [← this.closure_eq, hd.closure_range]
    have h3 : v ∈ Set.range q := by rw [h2]; trivial
    exact h3
  have hhs : Function.Surjective h := hgs.comp hqs
  haveI : IsDominant h := ⟨hhs.denseRange⟩
  have hcart : ∀ D : Divisor Z, D.IsCartier :=
    MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hZs
  obtain ⟨N', -, ⟨eN⟩⟩ := exists_isCartier_divisorialSheaf_iso_pullback_lineBundle h N
  obtain ⟨A', -, ⟨eA⟩⟩ := exists_isCartier_divisorialSheaf_iso_pullback_lineBundle h A
  -- `𝒪_Z(E_Z) ≅ h^* 𝒪_W(mN - A)`
  obtain ⟨eV⟩ := heV
  obtain ⟨eNA⟩ := hNA
  have hEZ' : Nonempty (EZ.divisorialSheaf ≅
      (Scheme.Modules.pullback h).obj (MMP.CartierDivisor.sheaf (m • N - A))) :=
    ⟨eZ ≪≫ (Scheme.Modules.pullback q).mapIso (eV ≪≫ (Scheme.Modules.pullback g).mapIso eNA.symm)
      ≪≫ (Scheme.Modules.pullbackComp q g).app _⟩
  have hlin := linearlyEquivalent_add_of_iso_pullback h N A m hm hEZ' ⟨eN⟩ ⟨eA⟩
  obtain ⟨φ, hφ⟩ := hlin
  have hDA : (m • N' - EZ).LinearlyEquivalent A' := ⟨φ⁻¹, by
    rw [MMP.Mori.principalDivisor_inv, ← hφ]; abel⟩
  -- the pushforward
  have hVv : AlgebraicGeometry.IsProjectiveVariety ℂ (g ≫ sW) := inferInstance
  obtain ⟨eHart⟩ := nonempty_pushforward_divisorialSheaf_iso_unit (g ≫ sW) hVv.toIsVariety q
    hZv.toIsVariety hqb A₀ (hcart A₀) hA0 (fun P hP => hBexc P (hAneg P hP))
  have hLinv : Stacks.Ample.IsInvertibleModule W (MMP.CartierDivisor.sheaf N) :=
    MMP.CartierDivisor.isInvertibleModule_sheaf N
  obtain ⟨ePF⟩ := nonempty_pushforward_tensor_pullback_iso h A₀.divisorialSheaf
      (MMP.CartierDivisor.sheaf N)
  have hhproj : IsProjectiveMorphism h :=
    IsProjectiveMorphism.of_comp h sW (by rw [hh, Category.assoc]; exact hZv.isProjective)
  refine ⟨Z, q ≫ g ≫ sW, hZp, hZs, inferInstance, inferInstance, h, by rw [hh, Category.assoc],
    hhproj.isProjective, nZ, KZ, hKZ, C, hBZ.of_support_subset ?_, hC0, hC1, A₀ + N',
    hcart _, ⟨m, hm, m • N' - EZ, ?_, ⟨hDA.divisorialSheafIso ≪≫ eA⟩⟩, ⟨?_⟩⟩
  · intro P hP
    simp only [Finsupp.mem_support_iff] at hP ⊢
    exact hCB P hP
  · rw [map_sub, map_nsmul, hEZ, map_add, hAC, ← Nat.cast_smul_eq_nsmul ℚ]
    module
  · exact (Scheme.Modules.pushforward h).mapIso
        (((hcart A₀).divisorialSheafTensorIso (hcart N')).symm ≪≫ whiskerLeftIso _ eN) ≪≫ ePF ≪≫
      whiskerRightIso (((Scheme.Modules.pushforwardComp q g).app _).symm ≪≫
        (Scheme.Modules.pushforward g).mapIso eHart) _

/-- If every `f.app U` is an isomorphism, the structure map `𝒪_Y ⟶ f_* 𝒪_X` is an
isomorphism. -/
private theorem isIso_unitToPushforwardObjUnit {X Y : Scheme.{0}} (f : X ⟶ Y)
    (hf : ∀ U : Y.Opens, IsIso (f.app U)) :
    @IsIso Y.Modules _ (SheafOfModules.unit Y.ringCatSheaf)
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  refine Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun U => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (ConcreteCategory.isIso_iff_bijective (f.app U)).1 (hf U)

/-- **Step 3 (the trace splitting).** For a proper surjective morphism `g : V ⟶ W` from a normal
complex variety onto a normal complex variety, the structure map `𝒪_W ⟶ g_* 𝒪_V` is split: the
Stein factor `κ` of `g` is finite with `g_* 𝒪_V = κ_* 𝒪_{W'}`, and the normalized trace of `κ`
splits `𝒪_W ⟶ κ_* 𝒪_{W'}`. -/
private theorem nonempty_retract_unit_pushforward {W : Scheme.{0}}
    (sW : W ⟶ Spec (.of ℂ)) [MMP.Mori.IsProjectiveVariety ℂ sW] [IsNormal W]
    {V : Scheme.{0}} [IsIntegral V] [IsNormal V] (g : V ⟶ W)
    [MMP.Mori.IsProjectiveVariety ℂ (g ≫ sW)]
    (hg : IsProjectiveMorphism g) (hgs : Function.Surjective g) :
    Nonempty (Retract (𝟙_ W.Modules) ((Scheme.Modules.pushforward g).obj (𝟙_ V.Modules))) := by
  haveI : IsProper g := isProper_of_isProjectiveMorphism g hg
  have hV : MMP.Mori.IsNormalVariety ℂ (g ≫ sW) := ⟨inferInstance, inferInstance⟩
  obtain ⟨W', h', κ, ⟨hS⟩, -, hh's, hiso, -, hκ, hW'⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isNormalVariety (g ≫ sW) sW hV
      inferInstance g rfl
  have hcomp : h' ≫ κ = g := hS.comp
  haveI : IsIntegral W' := hW'.1.toIsIntegral
  haveI : IsNormal W' := hW'.2
  haveI : Surjective κ := ⟨fun w => by
    obtain ⟨v, rfl⟩ := hgs w
    exact ⟨h' v, by rw [← Scheme.Hom.comp_apply, hcomp]⟩⟩
  haveI : MMP.Mori.IsVariety ℂ sW :=
    (inferInstance : AlgebraicGeometry.IsProjectiveVariety ℂ sW).toIsVariety
  haveI : MMP.Mori.IsVariety ℂ (κ ≫ sW) := hW'.1
  obtain ⟨τ, hτ⟩ := MMP.Mori.exists_unitToPushforwardObjUnit_comp_eq_id sW (κ ≫ sW) κ rfl
  let e := @asIso W'.Modules _ _ _ _ (isIso_unitToPushforwardObjUnit h' hiso)
  subst hcomp
  exact ⟨(Retract.mk (SheafOfModules.unitToPushforwardObjUnit κ.toRingCatSheafHom) τ hτ).trans
    ((Retract.ofIso ((Scheme.Modules.pushforward κ).mapIso e)).trans
      (Retract.ofIso ((Scheme.Modules.pushforwardComp h' κ).app _)))⟩

open MMP.Mori in
/-- **The geometric core.** On a minimal lc centre `W` with an ample gap `m (N - D|_W) = A`,
there is a projective morphism `h : Z ⟶ W` from a smooth projective variety, a canonical divisor
`K_Z`, an snc boundary `C` with coefficients in `[0, 1]` and a Cartier divisor `M` on `Z` with
`m (M - (K_Z + C)) ∼ h^*A`, such that `𝒪_W(N)` is a retract of `h_* 𝒪_Z(M)`. -/
private theorem exists_sncModel_retract {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [MMP.Mori.IsProjectiveVariety ℂ sX] (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X}
    (hB : IsLogCanonicalPair sX B)
    {W : Scheme.{0}} [IsReduced W] (ι : W ⟶ X) [IsClosedImmersion ι]
    (hW : ∃ F : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) F 0 ∧
      Set.range ι = (F.center : Set X))
    (hmin : ∀ F : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) F 0 →
      (F.center : Set X) ⊆ Set.range ι → (F.center : Set X) = Set.range ι)
    (N : W.CartierDivisor) (m : ℕ) (hm : 0 < m) (E : Divisor X)
    (hE : Divisor.toQDivisor E = (m : ℚ) • (Divisor.toQDivisor K + B)) (hEC : E.IsCartier)
    (A : W.CartierDivisor) (hA : Stacks.Ample.IsAmple W (MMP.CartierDivisor.sheaf A))
    (hNA : Nonempty (MMP.CartierDivisor.sheaf (m • N - A) ≅ (Scheme.Modules.pullback ι).obj
        E.divisorialSheaf))
    [MMP.Mori.IsProjectiveVariety ℂ (ι ≫ sX)] :
    ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of ℂ)) (_ : MMP.Mori.IsProjectiveVariety ℂ sZ)
      (_ : IsSmoothScheme sZ) (_ : IsLocallyNoetherian Z) (_ : IsNormal Z) (h : Z ⟶ W)
      (_ : h ≫ ι ≫ sX = sZ) (_ : IsProjective h) (n : ℕ) (KZ : Divisor Z)
      (_ : KZ.IsCanonicalDivisor sZ n) (C : QDivisor Z) (_ : C.IsSNC sZ) (_ : ∀ P, 0 ≤ C P)
      (_ : ∀ P, C P ≤ 1) (M : Divisor Z) (_ : M.IsCartier),
      (∃ m' : ℕ, 0 < m' ∧ ∃ D : Divisor Z,
        Divisor.toQDivisor D = (m' : ℚ) • (Divisor.toQDivisor M - (Divisor.toQDivisor KZ + C)) ∧
        Nonempty (D.divisorialSheaf ≅ (Scheme.Modules.pullback h).obj (MMP.CartierDivisor.sheaf A)))
            ∧
      Nonempty (Retract (MMP.CartierDivisor.sheaf N) ((Scheme.Modules.pushforward h).obj
          M.divisorialSheaf)) := by
  haveI : IsNormal W := isNormal_of_minimal_lcCentre sX hdim hK hB ι hW hmin
  obtain ⟨V, _, _, _, g, _, hg, hgs, n, KV, hKV, BV, hBV, EV, hEV, hEVC, heV⟩ :=
    exists_dltStratum_over_centre sX hdim hK hB ι hW hmin m hm E hE hEC
  obtain ⟨Z, sZ, hZ, hZs, hZn, hZN, h, hhs, hhp, nZ, KZ, hKZ, C, hC, hC0, hC1, M, hM, hlin, ⟨e⟩⟩ :=
    exists_logResolution_pushforward_iso (ι ≫ sX) g hg hKV hBV m hm EV hEV hEVC _ heV N A
      (hNA.map fun e => e) hgs
  obtain ⟨r⟩ := nonempty_retract_unit_pushforward (ι ≫ sX) g hg hgs
  exact ⟨Z, sZ, hZ, hZs, hZn, hZN, h, hhs, hhp, nZ, KZ, hKZ, C, hC, hC0, hC1, M, hM, hlin,
    ⟨(retractTensorOfRetractUnit _ _ r).trans (Retract.ofIso e.symm)⟩⟩

private theorem solution : ∀ {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [MMP.Mori.IsProjectiveVariety ℂ sX] (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X}
    (hB : IsLogCanonicalPair sX B)
    {W : Scheme.{0}} [IsReduced W] (ι : W ⟶ X) [IsClosedImmersion ι]
    (hW : ∃ F : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) F 0 ∧
      Set.range ι = (F.center : Set X))
    (hmin : ∀ F : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) F 0 →
      (F.center : Set X) ⊆ Set.range ι → (F.center : Set X) = Set.range ι)
    (N : W.CartierDivisor)
    (hgap : ∃ m : ℕ, 0 < m ∧ ∃ E : Divisor X,
      Divisor.toQDivisor E = (m : ℚ) • (Divisor.toQDivisor K + B) ∧ E.IsCartier ∧
      ∃ A : W.CartierDivisor, Stacks.Ample.IsAmple W (MMP.CartierDivisor.sheaf A) ∧
        Nonempty (MMP.CartierDivisor.sheaf (m • N - A) ≅ (Scheme.Modules.pullback ι).obj
            E.divisorialSheaf)),
    ∀ i : ℕ, 0 < i → Limits.IsZero (Hgroup W.ringCatSheaf ⊤ i (MMP.CartierDivisor.sheaf N)) := by
  intro X sX _ _ _ _ hdim K hK B hB W _ ι _ hW hmin N hgap i hi
  obtain ⟨m, hm, E, hE, hEC, A, hA, hNA⟩ := hgap
  obtain ⟨F, hF0, hF⟩ := hW
  haveI : IrreducibleSpace W := by
    have h : IsIrreducible (Set.range ι) := hF ▸ F.center.isIrreducible
    haveI := Subtype.irreducibleSpace h
    haveI : Nonempty W := by obtain ⟨_, y, -⟩ := h.nonempty; exact ⟨y⟩
    exact ι.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph.isOpenEmbedding.irreducibleSpace
  haveI := isProjectiveVariety_comp_of_isClosedImmersion sX ι
  obtain ⟨Z, sZ, _, hZs, _, _, h, hhs, hhp, n, KZ, hKZ, C, hC, hC0, hC1, M, hM, hlin, ⟨r⟩⟩ :=
    exists_sncModel_retract sX hdim hK hB ι ⟨F, hF0, hF⟩ hmin N m hm E hE hEC A hA hNA
  haveI := MMP.CartierDivisor.isInvertibleModule_sheaf A
  have := MMP.Mori.subsingleton_cohomologyOverField_rightDerived_pushforward_divisorialSheaf
    (ι ≫ sX) sZ hZs h hhs hhp KZ hKZ C hC hC0 hC1 M hM (MMP.CartierDivisor.sheaf A) hA hlin i 0 hi
  refine isZero_Hgroup_of_retract r i (isZero_Hgroup_of_subsingleton (ι ≫ sX) _ i ?_)
  exact (cohomologyOverFieldLinearEquivOfIso (ι ≫ sX)
    (rightDerivedZeroPushforwardIso h M.divisorialSheaf) i).symm.injective.subsingleton

end Proof_lem_mmp_lc_bpf_minimal_centre_vanishing_fourfold

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori (Divisor QDivisor DivisorOver)
open MMP.Intersection (IsLogCanonicalPair IsLogDiscrepancy)

/-- **Vanishing on a minimal lc centre.** Let `X` be a normal projective complex fourfold, `K` a
canonical divisor and `(X, B)` a log canonical pair with `B` a `ℚ`-divisor; put `D = K + B`. Let
`ι : W ⟶ X` be a closed immersion of a reduced scheme onto a minimal lc centre of `(X, B)`: the
centre of a divisor over `X` of log discrepancy `0` containing no other such centre. If `N` is a
Cartier divisor on `W` with `N - D|_W` ample as a rational class (for some `m > 0`, a Cartier
divisor `E = m D` on `X` and an ample Cartier divisor `A` on `W`,
`𝒪_W(mN - A) ≅ ι^*𝒪_X(E)`), then `Hⁱ(W, 𝒪_W(N)) = 0` for all `i > 0`. -/
@[mmp "lem_mmp_lc_bpf_minimal_centre_vanishing_fourfold"]
public theorem isZero_Hgroup_lineBundle_of_minimal_lcCentre {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [MMP.Mori.IsProjectiveVariety ℂ sX] (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X}
    (hB : IsLogCanonicalPair sX B)
    {W : Scheme.{0}} [IsReduced W] (ι : W ⟶ X) [IsClosedImmersion ι]
    (hW : ∃ F : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) F 0 ∧
      Set.range ι = (F.center : Set X))
    (hmin : ∀ F : DivisorOver ℂ sX, IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) F 0 →
      (F.center : Set X) ⊆ Set.range ι → (F.center : Set X) = Set.range ι)
    (N : W.CartierDivisor)
    (hgap : ∃ m : ℕ, 0 < m ∧ ∃ E : Divisor X,
      Divisor.toQDivisor E = (m : ℚ) • (Divisor.toQDivisor K + B) ∧ E.IsCartier ∧
      ∃ A : W.CartierDivisor, Stacks.Ample.IsAmple W (MMP.CartierDivisor.sheaf A) ∧
        Nonempty (MMP.CartierDivisor.sheaf (m • N - A) ≅ (Scheme.Modules.pullback ι).obj
            E.divisorialSheaf)) :
    ∀ i : ℕ, 0 < i → Limits.IsZero (Hgroup W.ringCatSheaf ⊤ i (MMP.CartierDivisor.sheaf N)) :=
      by revert X sX hdim K hK B hB W ι hW hmin N hgap; first | exact Proof_lem_mmp_lc_bpf_minimal_centre_vanishing_fourfold.solution | exact Proof_lem_mmp_lc_bpf_minimal_centre_vanishing_fourfold.solution _ | exact Proof_lem_mmp_lc_bpf_minimal_centre_vanishing_fourfold.solution _ _ | exact Proof_lem_mmp_lc_bpf_minimal_centre_vanishing_fourfold.solution _ _ _ | exact Proof_lem_mmp_lc_bpf_minimal_centre_vanishing_fourfold.solution _ _ _ _

end MMP.Fourfold

