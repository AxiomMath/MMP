module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Semismooth.Normalization
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
public import MMP.AlgebraicGeometry.Positivity.OrbitInvariantGeneration
import MMP.AlgebraicGeometry.MMP.Surface.AffineLcCompletion
import MMP.AlgebraicGeometry.Singularities.Surface.LcCentreSeminormal
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerFunctorial
import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsTopGeneratorFibres
import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertFunctionComparison
import StacksFrontier.AlgebraicGeometry.InvertibleOnClosedCover.Basic
import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.RestrictOpen
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayShortExactSequenceDimTwo
import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianProperBaseChange
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelIso
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupDescent
import StacksFrontier.AlgebraicGeometry.FormsTrace.RelativeSections
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeSmooth
import StacksFrontier.AlgebraicGeometry.Chow.NormalConeZeroSectionGysin
import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentChartZeroCycleGrouping
import StacksFrontier.AlgebraicGeometry.Modules.PushforwardUnitHomEquiv
import StacksFrontier.AlgebraicGeometry.HigherDirectImageBaseChange.Basic
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleCycleClassBridge
import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupProperPushforwardDerived
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveDisjointUnion
import StacksFrontier.Topology.Dimension.UnionDimension
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsEtaleReduction
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Curves.NormalizationLiftInvertible
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
public import MMP.AlgebraicGeometry.Chow.FieldSituation
import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.NormalizationIsoRegularLocus

/-!
# Sections of line bundles on the reduced boundary of an lc surface

Let `(S, B)` be a log canonical pair with rational boundary on a normal complex surface, let
`C = ⌊B⌋` with its reduced structure and let `ν : Cᵛ ⟶ C` be its normalization. For every
invertible sheaf `L` on `C` and every open `U ⊆ C`, pulling back along `ν` identifies `Γ(U, L)`
with the sections `t` of `ν^*L` over `ν⁻¹U` whose values at the points over each closed point
`c ∈ U` all agree in the fibre `L(c)`. In other words `C` is seminormal: `𝒪_C` is the subsheaf
of `ν_*𝒪_{Cᵛ}` of functions taking equal values over every closed point, and the same holds
after twisting by any line bundle.

The assertion is local on `C`. Near a point of `C`, choose an affine open `U` of `S`; the pair
`(U, B|_U)` is log canonical and has a projective log canonical completion `(V, B_V)`. The
components of `⌊B_V⌋` are lc centres of `(V, B_V)`, so sections descend along the normalization
of their union `W`; and `C` and `W` contain a common open subscheme, over which the
normalizations of `C` and `W` agree, since normalization commutes with open immersions.

## Main results

* `MMP.Threefold.injective_and_mem_range_iff_unit_app_roundDown_suppScheme`: the description of
  `Γ(U, L)` inside `Γ(ν⁻¹U, ν^*L)`.

## Implementation notes

* `C` is `(roundDown B).suppScheme`, the reduced closed subscheme on the support of `⌊B⌋`, and
  `Cᵛ` is `Stacks.AlgebraicGeometry.Normalization.normalizationScheme C hC`; the finiteness of
  irreducible components `hC` only serves to form the normalization.
* The map `Γ(U, L) → Γ(ν⁻¹U, ν^*L)` is the unit of the adjunction `ν^* ⊣ ν_*`.
* A section `u` of a module `M` *vanishes at* `x` when its germ lies in `𝔪_x M_x`, written
  without stalks: near `x`, `u = ∑ fᵢ mᵢ` with every `fᵢ` vanishing at `x`.
* "The values of `t` over `c` agree in `L(c)`" is the existence of a section `s` of `L` near `c`
  such that `t - ν^*s` vanishes at every point over `c`: a common value `λ ∈ L(c)` lifts to such
  an `s`, and conversely `s(c)` is a common value. (At a closed point `c` of the complex curve
  `C` and any `x` over it, `κ(c) = κ(x) = ℂ`, so `L(c) → (ν^*L)(x)` is an isomorphism.)
* Two formalizations of log canonical pairs meet in the proof:
  `MMP.Intersection.IsLogCanonicalPair` (log discrepancies of divisors with proper morphisms are
  `≥ 0`) and `MMP.Mori.IsLcPair` (Kollár–Mori discrepancies of all exceptional divisors are
  `≥ -1`). They agree for effective boundaries with coefficients at most one, by the dictionary
  `MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy` and the existence of proper
  models with a given divisorial valuation (Nagata compactification followed by normalization).

## References

* [OAI] *Threefold slc surface bridges*, sections on the reduced boundary of an lc surface.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori Stacks.AlgebraicGeometry.Normalization Opposite

namespace MMP.Threefold

universe u

section LogCanonical

/-- **Nagata compactification**: a separated morphism of finite type `f : Y ⟶ Z` to a
quasi-compact quasi-separated scheme factors as a quasi-compact open immersion followed by a
proper morphism. -/
private theorem exists_isOpenImmersion_isProper_comp_eq {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [CompactSpace Z] [QuasiSeparatedSpace Z] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] :
    ∃ (P : Scheme.{u}) (j : Y ⟶ P) (p : P ⟶ Z), IsOpenImmersion j ∧ QuasiCompact j ∧
      IsProper p ∧ j ≫ p = f := by
  obtain ⟨c, hc⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace f
  exact ⟨c.space, c.immersion, c.toBase, inferInstance, hc, inferInstance, Over.w c.obj.hom⟩

/-- The normalization of `P` in a normal locally Noetherian scheme `Y`, along a quasi-compact
open immersion `j : Y ⟶ P` with `P` locally of finite type over a field, is normal and finite
over `P`, and `Y` is open in it. -/
private theorem isOpenImmersion_toNormalization_and_isNormal_and_isFinite {k : Type u} [Field k]
    {Y P : Scheme.{u}} {sP : P ⟶ Spec (.of k)} [LocallyOfFiniteType sP] (j : Y ⟶ P)
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
private theorem isBirationalMorphism_of_isOpenImmersion_comp {Y P Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral P] [IsIntegral Z] (t : Y ⟶ P) [IsOpenImmersion t] (g : P ⟶ Z)
    (h : IsBirationalMorphism (t ≫ g)) : IsBirationalMorphism g := by
  obtain ⟨W, ⟨w, hw⟩, hWo⟩ := h.exists_isOpenImmersion
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
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g U V ⟨t w, w, hw, rfl⟩ ⟨_, ⟨w, hw⟩, rfl⟩
    hUV ?_
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun ⟨z, hz⟩ => ?_⟩⟩
  obtain ⟨w, rfl⟩ := hz
  refine ⟨(t.isoImage W).hom w, ?_⟩
  apply V.ι.isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, hc, ← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
  rfl

/-- **Kollár–Mori 2.22 for the identity model.** Every divisor `(Y, f, E)` over a normal variety
`X` has the valuation of a divisor over `X` whose morphism is proper: compactify `f` by Nagata's
theorem, `Y ⊆ P → X`, and replace `P` by the normalization of `P` in `Y`. -/
private theorem exists_isProper_valuation_eq {k : Type u} [Field k] {X : Scheme.{u}}
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

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}

omit [IsAlgClosed k] [CharZero k] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- A prime divisor meets every open containing its generic point. -/
private theorem support_inter_nonempty {P : MMP.Mori.PrimeDivisor X} {V : Set X}
    (hV : P.genericPoint ∈ V) : (P.support ∩ V).Nonempty :=
  ⟨P.genericPoint, by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl, hV⟩

/-- A prime divisor `P` of `X`, as a divisor over `X` through the identity, has discrepancy
`-coeff_P(B)`. -/
private theorem isDiscrepancy_ofPrimeDivisor {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hP : IsPairWith sX n K B) (P : MMP.Mori.PrimeDivisor X) :
    IsDiscrepancy sX n K B (DivisorOver.ofPrimeDivisor k hP.1 P) (-B.coeff P) := by
  obtain ⟨hX, hK, hQ⟩ := hP
  obtain ⟨m, hm, hmC⟩ := hQ.exists_pos
  obtain ⟨-, V, hV, τ, hτ⟩ :=
    MMP.Positivity.IsPair.exists_generatesOn ⟨hX, n, K, hK, hQ⟩ hK hmC P.genericPoint
  refine ⟨hX, hK, m, hm, hmC, V, hV, τ, hτ, ?_⟩
  rw [DivisorOver.ordPullback_ofPrimeDivisor hX hK.topologicalKrullDim_eq P τ]
  linear_combination -hτ.2 P (support_inter_nonempty hV)

/-- On a log canonical pair every coefficient of the boundary is at most one: the log
discrepancy of a prime divisor `P` is `1 - coeff_P`. -/
private theorem coeff_le_one_of_isLogCanonicalPair {B : QDivisor X}
    (hB : MMP.Intersection.IsLogCanonicalPair sX B) (P : MMP.Mori.PrimeDivisor X) :
    B.coeff P ≤ 1 := by
  obtain ⟨⟨hX, n, K, hK, hQ⟩, -, hlc⟩ := hB
  have h0 := hlc n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy
    (isDiscrepancy_ofPrimeDivisor (k := k) ⟨hX, hK, hQ⟩ P) (show IsProper (𝟙 X) from inferInstance))
  have h1 : ((B.coeff P : ℚ) : ℝ) ≤ 1 := by push_cast at h0; linarith
  exact_mod_cast h1

/-- A divisor over `X` that is not exceptional has discrepancy `-coeff_P(Δ)` for the prime
divisor `P` of `X` with the same valuation; so if every coefficient of `Δ` is `≤ 1`, it is
`≥ -1`. -/
private theorem neg_one_le_of_not_isExceptional {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hcoeff : ∀ P : MMP.Mori.PrimeDivisor X, Δ.coeff P ≤ 1) {D : DivisorOver k sX}
    (hD : ¬ D.IsExceptional) {a : ℚ} (ha : IsDiscrepancy sX n K Δ D a) : -1 ≤ a := by
  obtain ⟨hX, hK, m, hm, -, V, hV, τ, hτ, hmτ⟩ := ha
  obtain ⟨P, hv⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hD
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  rw [MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX hn hv τ,
    DivisorOver.ordPullback_ofPrimeDivisor hX hn P τ] at hmτ
  have hx : D.f D.E.genericPoint = P.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
  have e := hτ.2 P (support_inter_nonempty (hx ▸ hV))
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  have : a = -Δ.coeff P := by
    apply mul_left_cancel₀ hm0
    linear_combination hmτ + e
  rw [this]
  linarith [hcoeff P]

/-- **Log canonical pairs are Kollár–Mori lc**, for every canonical divisor: every discrepancy
`a(E, X, B)` of an exceptional divisor over `X` is the log discrepancy, minus one, of a divisor
with proper morphism and the same valuation, hence is `≥ -1`. -/
private theorem isLcPair_of_isLogCanonicalPair {B : QDivisor X}
    (hB : MMP.Intersection.IsLogCanonicalPair sX B) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) : IsLcPair sX n K B := by
  obtain ⟨⟨hX, n', K', hK', hQ'⟩, -, hlc⟩ := hB
  haveI : CompactSpace X := haveI := hX.1; QuasiCompact.compactSpace_of_compactSpace sX
  have hlin : K'.LinearlyEquivalent K :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hK' hK
  have hP : IsPairWith sX n K B := ⟨hX, hK, hQ'.add_of_linearlyEquivalent hlin⟩
  refine ⟨hP, le_discrep_iff.mpr fun D a hD ha => ?_⟩
  obtain ⟨E, hEp, hEv⟩ := exists_isProper_valuation_eq hX D
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hK E
  have haa : a' = a := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hP hEv ha' ha
  have h0 := hlc n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha' hEp)
  have : (-1 : ℝ) ≤ a := by rw [← haa]; linarith
  have h2 := EReal.coe_le_coe_iff.mpr this
  simpa using h2

/-- **Kollár–Mori lc pairs with coefficients in `[0, 1]` are log canonical.** Every log
discrepancy is `1 + a(E, X, B)`, and `a(E, X, B) ≥ -1`: by the lc bound for exceptional `E`,
and as `-coeff ≥ -1` otherwise. -/
private theorem isLogCanonicalPair_of_isLcPair {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (h : IsLcPair sX n K B) (hnn : ∀ P, 0 ≤ B.coeff P) (hle : ∀ P, B.coeff P ≤ 1) :
    MMP.Intersection.IsLogCanonicalPair sX B := by
  refine ⟨h.1.isPair, hnn, fun n' D a ha => ?_⟩
  have hn' : n' = n := by
    have h1 := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
    rw [h.1.2.1.topologicalKrullDim_eq] at h1
    exact_mod_cast h1.symm
  subst hn'
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy h.1.isPair h.1.2.1 D
  rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha]
  suffices hc1 : (-1 : ℚ) ≤ c by
    have : (-1 : ℝ) ≤ c := by exact_mod_cast hc1
    linarith
  by_cases hD : D.IsExceptional
  · have h2 := h.2.trans (discrep_le hD hc)
    have : ((-1 : ℝ) : EReal) ≤ ((c : ℝ) : EReal) := by simpa using h2
    exact_mod_cast EReal.coe_le_coe_iff.mp this
  · exact neg_one_le_of_not_isExceptional hle hD hc

/-- **Log canonical pairs restrict to open subschemes.** -/
private theorem isLogCanonicalPair_restrictOpen {B : QDivisor X}
    (hB : MMP.Intersection.IsLogCanonicalPair sX B) (U : X.Opens) [Nonempty U] :
    MMP.Intersection.IsLogCanonicalPair (U.ι ≫ sX) (B.restrictOpen U) := by
  obtain ⟨⟨hX, n, K, hK, hQ⟩, hnn, -⟩ := id hB
  have hlc := (isLcPair_of_isLogCanonicalPair hB hK).restrictOpen U
  exact isLogCanonicalPair_of_isLcPair hlc
    (fun P => by rw [DivisorWithCoeffs.coeff_restrictOpen]; exact hnn _)
    (fun P => by rw [DivisorWithCoeffs.coeff_restrictOpen];
                 exact coeff_le_one_of_isLogCanonicalPair hB _)

/-- An element of `WithBot ℕ∞` below `2` is at most `1`. -/
private theorem withBot_le_one_of_lt_two {d : WithBot ℕ∞} (h : d < 2) : d ≤ 1 := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe m =>
      have h2 : ((m : ℕ∞) : WithBot ℕ∞) < ((2 : ℕ) : ℕ∞) := h
      have : m < 2 := by exact_mod_cast h2
      have h3 : m ≤ 1 := by omega
      exact_mod_cast h3

omit [IsAlgClosed k] [CharZero k] [IsLocallyNoetherian X] [IsNormal X] in
/-- The centre of a prime divisor `P` of `X`, through the identity, is its support. -/
private theorem coe_center_ofPrimeDivisor (hX : IsNormalVariety k sX)
    (P : MMP.Mori.PrimeDivisor X) :
    ((DivisorOver.ofPrimeDivisor k hX P).center : Set X) = P.support := by
  rw [DivisorOver.coe_center]
  change closure ((𝟙 X : X ⟶ X) '' P.support) = _
  rw [show ((𝟙 X : X ⟶ X) : X → X) = id from rfl, Set.image_id,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact closure_closure

omit [IsAlgClosed k] [CharZero k] [IsLocallyNoetherian X] [IsNormal X] in
/-- On a surface, a prime divisor has dimension at most one. -/
private theorem topologicalKrullDim_support_le_one (hdim : topologicalKrullDim X = 2)
    (P : MMP.Mori.PrimeDivisor X) : topologicalKrullDim (P.support : Set X) ≤ 1 := by
  have hne : (P.support : Set X) ≠ Set.univ := by
    intro h
    have hg : genericPoint X ∈ (P.support : Set X) := h ▸ Set.mem_univ _
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hg
    have h1 : AlgebraicGeometry.PrimeDivisor.genericPoint P ⤳ genericPoint X :=
      specializes_iff_mem_closure.mpr hg
    have h2 : genericPoint X ⤳ AlgebraicGeometry.PrimeDivisor.genericPoint P :=
      (genericPoint_spec X).specializes (Set.mem_univ _)
    have heq := (h1.antisymm h2).eq
    have hc := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
    rw [heq, Order.coheight_eq_zero.mpr fun b _ =>
      (genericPoint_spec X).specializes (Set.mem_univ b)] at hc
    exact absurd hc (by decide)
  have hcl : IsClosed (P.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  have hlt := topologicalKrullDim_lt_of_isClosed_ne_univ hcl hne (by rw [hdim]; decide)
  rw [hdim] at hlt
  exact withBot_le_one_of_lt_two hlt

end LogCanonical

section Descent

variable {X X' : Scheme.{u}}

/-- A section `u` of an `𝒪_{X'}`-module `M` over `W` *vanishes at* `x ∈ W` if near `x` it is a
combination `∑ fᵢ mᵢ` of sections `mᵢ` of `M` with coefficients `fᵢ` vanishing at `x`, that is,
its germ lies in `𝔪_x M_x`. -/
private def VanishesAt (M : X'.Modules) {W : X'.Opens} (u : Γ(M, W)) (x : X') : Prop :=
  ∃ (W' : X'.Opens) (hW' : W' ≤ W) (n : ℕ) (f : Fin n → Γ(X', W')) (m : Fin n → Γ(M, W')),
    x ∈ W' ∧ (∀ i, x ∉ X'.basicOpen (f i)) ∧ M.presheaf.map (homOfLE hW').op u = ∑ i, f i • m i

/-- The pull-back map on sections, `Γ(U, L) → Γ(ν⁻¹ U, ν^* L)`. -/
private noncomputable abbrev pullbackSection (ν : X' ⟶ X) (L : X.Modules) (U : X.Opens) :
    Γ(L, U) ⟶ Γ((Scheme.Modules.pullback ν).obj L, ν ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).app U

/-- A section `t` of `ν^* L` over `ν⁻¹ U` *has a common value at* `c ∈ U` if near `c` there is a
section `s` of `L` with `t - ν^* s` vanishing at every point over `c`. -/
private def HasCommonValueAt (ν : X' ⟶ X) (L : X.Modules) {U : X.Opens}
    (t : Γ((Scheme.Modules.pullback ν).obj L, ν ⁻¹ᵁ U)) (c : X) : Prop :=
  ∃ (V : X.Opens) (hVU : V ≤ U), c ∈ V ∧ ∃ s : Γ(L, V), ∀ x : X', ν x = c →
    VanishesAt ((Scheme.Modules.pullback ν).obj L)
      (((Scheme.Modules.pullback ν).obj L).presheaf.map (homOfLE (ν.preimage_mono hVU)).op t -
        pullbackSection ν L V s) x

/-- **Descent of sections along `ν` over `U`**: the pull-back map `Γ(U, L) → Γ(ν⁻¹ U, ν^* L)` is
injective, with image the sections having a common value at every closed point of `U`. -/
private def Descends (ν : X' ⟶ X) (L : X.Modules) (U : X.Opens) : Prop :=
  Function.Injective (pullbackSection ν L U) ∧
    ∀ t : Γ((Scheme.Modules.pullback ν).obj L, ν ⁻¹ᵁ U),
      t ∈ Set.range (pullbackSection ν L U) ↔
        ∀ c ∈ U, IsClosed ({c} : Set X) → HasCommonValueAt ν L t c

variable {ν : X' ⟶ X} {L : X.Modules}

/-- Naturality of the pull-back map on sections. -/
private theorem pullbackSection_map {U V : X.Opens} (h : V ≤ U) (s : Γ(L, U)) :
    pullbackSection ν L V (L.presheaf.map (homOfLE h).op s) =
      ((Scheme.Modules.pullback ν).obj L).presheaf.map (homOfLE (ν.preimage_mono h)).op
        (pullbackSection ν L U s) :=
  congr($((((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).mapPresheaf
    ).naturality (homOfLE h).op) s)

/-- Vanishing at `x` survives restriction to a smaller open containing `x`. -/
private theorem VanishesAt.restrict {M : X'.Modules} {W W₀ : X'.Opens} (h : W₀ ≤ W)
    {u : Γ(M, W)} {x : X'} (hx : x ∈ W₀) (hu : VanishesAt M u x) :
    VanishesAt M (M.presheaf.map (homOfLE h).op u) x := by
  obtain ⟨W', hW', n, f, m, hxW', hf, hu⟩ := hu
  refine ⟨W' ⊓ W₀, inf_le_right, n, fun i => X'.presheaf.map (homOfLE inf_le_left).op (f i),
    fun i => M.presheaf.map (homOfLE inf_le_left).op (m i), ⟨hxW', hx⟩, fun i hi => hf i ?_, ?_⟩
  · rw [Scheme.basicOpen_res] at hi
    exact hi.2
  · rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rw [show ((homOfLE h).op ≫ (homOfLE (inf_le_right : W' ⊓ W₀ ≤ W₀)).op : _) =
        (homOfLE hW').op ≫ (homOfLE (inf_le_left : W' ⊓ W₀ ≤ W')).op from rfl, Functor.map_comp,
      ConcreteCategory.comp_apply, hu, map_sum]
    simp only [Scheme.Modules.map_smul]

/-- The zero section vanishes everywhere. -/
private theorem vanishesAt_zero (M : X'.Modules) {W : X'.Opens} {x : X'} (hx : x ∈ W) :
    VanishesAt M (0 : Γ(M, W)) x :=
  ⟨W, le_rfl, 0, Fin.elim0, Fin.elim0, hx, fun i => i.elim0, by simp⟩

/-- A pulled-back section has a common value at every point of `U`. -/
private theorem hasCommonValueAt_pullbackSection {U : X.Opens} (s : Γ(L, U)) {c : X}
    (hc : c ∈ U) : HasCommonValueAt ν L (pullbackSection ν L U s) c := by
  refine ⟨U, le_rfl, hc, s, fun x hx => ?_⟩
  have : ((Scheme.Modules.pullback ν).obj L).presheaf.map
      (homOfLE (ν.preimage_mono (le_refl U))).op (pullbackSection ν L U s) -
      pullbackSection ν L U s = 0 := by
    rw [sub_eq_zero]
    exact congr($(((Scheme.Modules.pullback ν).obj L).presheaf.map_id _) _)
  rw [this]
  exact vanishesAt_zero _ (show ν x ∈ U by rw [hx]; exact hc)

/-- An `𝒪_X`-module as a sheaf of abelian groups. -/
private noncomputable abbrev toSheaf (M : X.Modules) : TopCat.Sheaf Ab X :=
  ⟨M.presheaf, M.isSheaf⟩

/-- A section of the pull-back has a common value at `c` after restriction to any smaller open
containing `c`. -/
private theorem HasCommonValueAt.restrict {U U₀ : X.Opens} (h : U₀ ≤ U)
    {t : Γ((Scheme.Modules.pullback ν).obj L, ν ⁻¹ᵁ U)} {c : X} (hc : c ∈ U₀)
    (ht : HasCommonValueAt ν L t c) :
    HasCommonValueAt ν L
      (((Scheme.Modules.pullback ν).obj L).presheaf.map (homOfLE (ν.preimage_mono h)).op t) c := by
  obtain ⟨V, hVU, hcV, s, hs⟩ := ht
  refine ⟨V ⊓ U₀, inf_le_right, ⟨hcV, hc⟩, L.presheaf.map (homOfLE inf_le_left).op s,
    fun x hx => ?_⟩
  have h1 := (hs x hx).restrict (ν.preimage_mono (inf_le_left : V ⊓ U₀ ≤ V))
    (show ν x ∈ V ⊓ U₀ by rw [hx]; exact ⟨hcV, hc⟩)
  convert h1 using 1
  rw [pullbackSection_map, map_sub]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp]
  rfl

/-- **Descent is local on `X`.** If every point has an open neighbourhood over whose opens
sections descend, they descend over every open. -/
private theorem descends_of_forall_mem
    (H : ∀ x : X, ∃ O : X.Opens, x ∈ O ∧ ∀ U ≤ O, Descends ν L U) (U : X.Opens) :
    Descends ν L U := by
  choose O hxO hO using H
  set P := (Scheme.Modules.pullback ν).obj L
  let V : U → X.Opens := fun x => U ⊓ O x
  have hcov : U ≤ iSup V := fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hx, hxO x⟩
  have hcov' : ν ⁻¹ᵁ U ≤ iSup fun x => ν ⁻¹ᵁ V x := by
    intro y hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨ν y, hy⟩, hy, hxO _⟩
  have hDV : ∀ x, Descends ν L (V x) := fun x => hO x _ inf_le_right
  have inj : Function.Injective (pullbackSection ν L U) := by
    intro s₁ s₂ h12
    refine (toSheaf L).eq_of_locally_eq' V U (fun x => homOfLE inf_le_left) hcov s₁ s₂ fun x => ?_
    apply (hDV x).1
    change pullbackSection ν L (V x) (L.presheaf.map (homOfLE inf_le_left).op s₁) =
      pullbackSection ν L (V x) (L.presheaf.map (homOfLE inf_le_left).op s₂)
    rw [pullbackSection_map, pullbackSection_map, h12]
  refine ⟨inj, fun t => ⟨?_, fun ht => ?_⟩⟩
  · rintro ⟨s, rfl⟩ c hc -
    exact hasCommonValueAt_pullbackSection s hc
  · have hloc : ∀ x, ∃ s : Γ(L, V x), pullbackSection ν L (V x) s =
        P.presheaf.map (homOfLE (ν.preimage_mono inf_le_left)).op t := fun x =>
      ((hDV x).2 _).mpr fun c hc hcl => (ht c hc.1 hcl).restrict inf_le_left hc
    choose sf hsf using hloc
    have hcomp : TopCat.Presheaf.IsCompatible (toSheaf L).1 V sf := by
      intro x y
      apply (hO x _ (inf_le_left.trans inf_le_right)).1
      change pullbackSection ν L _ (L.presheaf.map (homOfLE inf_le_left).op (sf x)) =
        pullbackSection ν L _ (L.presheaf.map (homOfLE inf_le_right).op (sf y))
      rw [pullbackSection_map, pullbackSection_map, hsf, hsf, ← ConcreteCategory.comp_apply,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
      rfl
    obtain ⟨s, hs, -⟩ := (toSheaf L).existsUnique_gluing' V U (fun x => homOfLE inf_le_left)
      hcov sf hcomp
    refine ⟨s, (toSheaf P).eq_of_locally_eq' (fun x => ν ⁻¹ᵁ V x) (ν ⁻¹ᵁ U)
      (fun x => homOfLE (ν.preimage_mono inf_le_left)) hcov' _ _ fun x => ?_⟩
    change P.presheaf.map _ (pullbackSection ν L U s) = P.presheaf.map _ t
    rw [← pullbackSection_map]
    exact (congrArg (pullbackSection ν L (V x)) (hs x)).trans (hsf x)

/-- Restriction commutes with module morphisms on sections. -/
private theorem app_map {M N : X'.Modules} (g : M ⟶ N) {W W' : X'.Opens} (h : W' ≤ W)
    (u : Γ(M, W)) :
    g.app W' (M.presheaf.map (homOfLE h).op u) = N.presheaf.map (homOfLE h).op (g.app W u) :=
  congr($((g.mapPresheaf).naturality (homOfLE h).op) u)

/-- Module morphisms preserve vanishing at a point. -/
private theorem VanishesAt.map {M N : X'.Modules} (g : M ⟶ N) {W : X'.Opens} {u : Γ(M, W)}
    {x : X'} (hu : VanishesAt M u x) : VanishesAt N (g.app W u) x := by
  obtain ⟨W', hW', n, f, m, hxW', hf, hu⟩ := hu
  refine ⟨W', hW', n, f, fun i => g.app W' (m i), hxW', hf, ?_⟩
  rw [← app_map g hW' u, hu, map_sum]
  simp only [Scheme.Modules.Hom.app_smul]

/-- Naturality of the pull-back map on sections in the module. -/
private theorem pullbackSection_naturality {L' : X.Modules} (g : L ⟶ L') (V : X.Opens)
    (s : Γ(L, V)) :
    pullbackSection ν L' V (g.app V s) =
      ((Scheme.Modules.pullback ν).map g).app (ν ⁻¹ᵁ V) (pullbackSection ν L V s) := by
  have h := congr($(((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.naturality g)).app V s)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, Functor.id_map,
    Functor.comp_map, Scheme.Modules.pushforward_map_app] at h
  exact (h.trans (ConcreteCategory.comp_apply _ _ _)).symm.trans rfl |>.symm

/-- Module morphisms preserve having a common value. -/
private theorem HasCommonValueAt.map {L' : X.Modules} (g : L ⟶ L') {U : X.Opens}
    {t : Γ((Scheme.Modules.pullback ν).obj L, ν ⁻¹ᵁ U)} {c : X} (ht : HasCommonValueAt ν L t c) :
    HasCommonValueAt ν L' (((Scheme.Modules.pullback ν).map g).app _ t) c := by
  obtain ⟨V, hVU, hcV, s, hs⟩ := ht
  refine ⟨V, hVU, hcV, g.app V s, fun x hx => ?_⟩
  have := (hs x hx).map ((Scheme.Modules.pullback ν).map g)
  rw [map_sub, app_map, ← pullbackSection_naturality] at this
  exact this

/-- **Descent is invariant under isomorphisms of modules.** -/
private theorem Descends.of_iso {L' : X.Modules} (e : L ≅ L') {U : X.Opens}
    (h : Descends ν L U) : Descends ν L' U := by
  set φ := fun W => ((Scheme.Modules.pullback ν).map e.hom).app W
  set ψ := fun W => ((Scheme.Modules.pullback ν).map e.inv).app W
  have hψφ : ∀ W (u : Γ((Scheme.Modules.pullback ν).obj L, W)), ψ W (φ W u) = u := by
    intro W u
    change (((Scheme.Modules.pullback ν).map e.hom ≫ (Scheme.Modules.pullback ν).map e.inv).app
      W) u = u
    rw [← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id]
    rfl
  have hφψ : ∀ W (u : Γ((Scheme.Modules.pullback ν).obj L', W)), φ W (ψ W u) = u := by
    intro W u
    change (((Scheme.Modules.pullback ν).map e.inv ≫ (Scheme.Modules.pullback ν).map e.hom).app
      W) u = u
    rw [← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id]
    rfl
  have hee : ∀ V (s : Γ(L', V)), e.hom.app V (e.inv.app V s) = s := by
    intro V s
    change ((e.inv ≫ e.hom).app V) s = s
    rw [e.inv_hom_id]
    rfl
  refine ⟨fun s₁ s₂ h12 => ?_, fun t => ⟨?_, fun ht => ?_⟩⟩
  · have key : ∀ s, pullbackSection ν L' U s =
        φ _ (pullbackSection ν L U (e.inv.app U s)) := by
      intro s
      conv_lhs => rw [← hee U s]
      exact pullbackSection_naturality _ _ _
    rw [key, key] at h12
    have h' := congrArg (ψ _) h12
    rw [hψφ, hψφ] at h'
    rw [← hee U s₁, ← hee U s₂, h.1 h']
  · rintro ⟨s, rfl⟩ c hc hcl
    obtain ⟨-, hr⟩ := h
    have := (((hr _).mp ⟨e.inv.app U s, rfl⟩) c hc hcl).map e.hom
    rwa [← pullbackSection_naturality, hee] at this
  · have hψt : ψ _ t ∈ Set.range (pullbackSection ν L U) := (h.2 _).mpr fun c hc hcl =>
      (ht c hc hcl).map e.inv
    obtain ⟨s, hs⟩ := hψt
    refine ⟨e.hom.app U s, ?_⟩
    rw [pullbackSection_naturality, hs]
    exact hφψ _ t

/-- `Descends ν L U` and `Descends ν L' U` are equivalent for isomorphic modules `L ≅ L'`. -/
private theorem descends_iff_of_iso {L' : X.Modules} (e : L ≅ L') {U : X.Opens} :
    Descends ν L U ↔ Descends ν L' U :=
  ⟨Descends.of_iso e, Descends.of_iso e.symm⟩

end Descent

section BaseChange

variable {X X' Y Y' : Scheme.{u}} (o : Y ⟶ X) [IsOpenImmersion o] (ν : X' ⟶ X) (νY : Y' ⟶ Y)
  (o' : Y' ⟶ X') [IsOpenImmersion o'] (h : o' ≫ ν = νY ≫ o)

/-- Two successive restrictions of a section of a module are one restriction. -/
private theorem map_homOfLE_map_homOfLE {Z : Scheme.{u}} (F : Z.Modules) {A B C : Z.Opens}
    (h₁ : A ≤ B) (h₂ : B ≤ C) (x : Γ(F, C)) :
    F.presheaf.map (homOfLE h₁).op (F.presheaf.map (homOfLE h₂).op x) =
      F.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The pushforwards along the two sides of a commutative square agree. -/
private noncomputable def pushforwardSquareIso :
    Scheme.Modules.pushforward o' ⋙ Scheme.Modules.pushforward ν ≅
      Scheme.Modules.pushforward νY ⋙ Scheme.Modules.pushforward o :=
  Scheme.Modules.pushforwardComp o' ν ≪≫ Scheme.Modules.pushforwardCongr h ≪≫
    (Scheme.Modules.pushforwardComp νY o).symm

/-- **Base change for restriction along an open immersion**: `νY^* (M|_Y) ≅ (ν^* M)|_{Y'}`, the
conjugate of `pushforwardSquareIso`. -/
private noncomputable def restrictPullbackIso :
    Scheme.Modules.restrictFunctor o ⋙ Scheme.Modules.pullback νY ≅
      Scheme.Modules.pullback ν ⋙ Scheme.Modules.restrictFunctor o' :=
  (conjugateIsoEquiv ((Scheme.Modules.pullbackPushforwardAdjunction ν).comp
      (Scheme.Modules.restrictAdjunction o'))
    ((Scheme.Modules.restrictAdjunction o).comp
      (Scheme.Modules.pullbackPushforwardAdjunction νY))).symm (pushforwardSquareIso o ν νY o' h)

/-- The base change isomorphism is compatible with the units of the adjunctions. -/
private theorem restrictPullbackIso_unit (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) :
    ((restrictPullbackIso o ν νY o' h).hom.app M).app (νY ⁻¹ᵁ (o ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction νY).unit.app (M.restrict o)).app (o ⁻¹ᵁ U)
        (M.presheaf.map (homOfLE (o.image_preimage_le U)).op s)) =
    ((Scheme.Modules.pullback ν).obj M).presheaf.map
      (homOfLE (show o' ''ᵁ (νY ⁻¹ᵁ (o ⁻¹ᵁ U)) ≤ ν ⁻¹ᵁ U by
        rintro _ ⟨y, hy, rfl⟩
        change (o' ≫ ν) y ∈ U
        rw [h]
        exact hy)).op
      (((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app M).app U s) := by
  have key := CategoryTheory.unit_conjugateEquiv_symm
    ((Scheme.Modules.pullbackPushforwardAdjunction ν).comp (Scheme.Modules.restrictAdjunction o'))
    ((Scheme.Modules.restrictAdjunction o).comp (Scheme.Modules.pullbackPushforwardAdjunction νY))
    (pushforwardSquareIso o ν νY o' h).hom M
  have key' := congr($(key).app U s)
  simp only [Adjunction.comp_unit_app, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Functor.comp_map, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app] at key'
  have e1 : (restrictPullbackIso o ν νY o' h).hom.app M =
      ((conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction ν).comp
        (Scheme.Modules.restrictAdjunction o'))
        ((Scheme.Modules.restrictAdjunction o).comp
          (Scheme.Modules.pullbackPushforwardAdjunction νY))).symm
          (pushforwardSquareIso o ν νY o' h).hom).app M := rfl
  rw [e1]
  refine key'.symm.trans ?_
  have hle : o' ''ᵁ (νY ⁻¹ᵁ (o ⁻¹ᵁ U)) ≤ o' ''ᵁ (o' ⁻¹ᵁ (ν ⁻¹ᵁ U)) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y, ?_, rfl⟩
    change (o' ≫ ν) y ∈ U
    rw [h]
    exact hy
  have e2 : ∀ y, ((pushforwardSquareIso o ν νY o' h).hom.app
      ((Scheme.Modules.pullback ν ⋙ Scheme.Modules.restrictFunctor o').obj M)).app U y =
      ((Scheme.Modules.pullback ν).obj M).presheaf.map (homOfLE hle).op y := by
    intro y
    simp only [pushforwardSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardComp_hom_app_app,
      Scheme.Modules.pushforwardCongr_hom_app_app, Scheme.Modules.pushforwardComp_inv_app_app,
      Category.id_comp, Category.comp_id]
    rfl
  rw [e2]
  exact map_homOfLE_map_homOfLE ((Scheme.Modules.pullback ν).obj M) hle
    (o'.image_preimage_le (ν ⁻¹ᵁ U)) _

end BaseChange

section OpenImmersion

variable {X' : Scheme.{u}}

variable {Y' : Scheme.{u}} (o' : Y' ⟶ X') [IsOpenImmersion o'] {P : X'.Modules}

/-- A point lies on a basic open of a function on `Y'` exactly when its image lies on the basic
open of the corresponding function on the image. -/
private theorem mem_basicOpen_iff_of_isOpenImmersion {W : Y'.Opens} (r : Γ(Y', W)) (y : Y') :
    y ∈ Y'.basicOpen r ↔ o' y ∈ X'.basicOpen ((o'.appIso W).inv r) := by
  rw [← Scheme.image_basicOpen]
  refine ⟨fun hy => ⟨y, hy, rfl⟩, ?_⟩
  rintro ⟨z, hz, hzy⟩
  rwa [o'.isOpenEmbedding.injective hzy] at hz

/-- Vanishing of a section of a restriction `P|_{Y'}` at `y` is vanishing of the corresponding
section of `P` at `o' y`. -/
private theorem VanishesAt.of_restrict {W : Y'.Opens} {u : Γ(P.restrict o', W)} {y : Y'}
    (h : VanishesAt (P.restrict o') u y) : VanishesAt P (W := o' ''ᵁ W) u (o' y) := by
  obtain ⟨W', hW', n, f, m, hx, hf, hu⟩ := h
  refine ⟨o' ''ᵁ W', o'.image_mono hW', n, fun i => (o'.appIso W').inv (f i), m, ⟨y, hx, rfl⟩,
    fun i hi => hf i ((mem_basicOpen_iff_of_isOpenImmersion o' _ y).mpr hi), ?_⟩
  exact hu

/-- Conversely, vanishing of a section of `P` over `o' W` at `o' y` is vanishing of the
corresponding section of `P|_{Y'}` at `y`. -/
private theorem VanishesAt.restrict_of {W : Y'.Opens} {u : Γ(P, o' ''ᵁ W)} {y : Y'}
    (h : VanishesAt P u (o' y)) : VanishesAt (P.restrict o') (W := W) u y := by
  obtain ⟨W', hW', n, f, m, hx, hf, hu⟩ := h
  have hle : o' ''ᵁ (o' ⁻¹ᵁ W') ≤ W' := o'.image_preimage_le W'
  have hW'' : o' ⁻¹ᵁ W' ≤ W := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hW' hz
    rwa [o'.isOpenEmbedding.injective hwz] at hw
  refine ⟨o' ⁻¹ᵁ W', hW'', n,
    fun i => (o'.appIso (o' ⁻¹ᵁ W')).hom (X'.presheaf.map (homOfLE hle).op (f i)),
    fun i => P.presheaf.map (homOfLE hle).op (m i), hx, fun i hi => hf i ?_, ?_⟩
  · rw [mem_basicOpen_iff_of_isOpenImmersion o', Iso.hom_inv_id_apply, Scheme.basicOpen_res] at hi
    exact hi.2
  · change P.presheaf.map (homOfLE (o'.image_mono hW'')).op u = _
    have : (homOfLE (o'.image_mono hW'') : o' ''ᵁ (o' ⁻¹ᵁ W') ⟶ o' ''ᵁ W) =
        homOfLE hle ≫ homOfLE hW' := rfl
    rw [this, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hu, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Scheme.Modules.map_smul]
    show _ = ((o'.appIso (o' ⁻¹ᵁ W')).inv ((o'.appIso (o' ⁻¹ᵁ W')).hom
      (X'.presheaf.map (homOfLE hle).op (f i)))) •
        (P.presheaf.map (homOfLE hle).op (m i) : Γ(P, o' ''ᵁ (o' ⁻¹ᵁ W')))
    rw [Iso.hom_inv_id_apply]

end OpenImmersion

section Transport

variable {X X' Y Y' : Scheme.{u}} (o : Y ⟶ X) [IsOpenImmersion o] (ν : X' ⟶ X) (νY : Y' ⟶ Y)
  (o' : Y' ⟶ X') [IsOpenImmersion o'] (h : o' ≫ ν = νY ≫ o)

/-- Restricting to the same open does nothing. -/
private theorem map_homOfLE_self {Z : Scheme.{u}} (F : Z.Modules) {A : Z.Opens} (x : Γ(F, A)) :
    F.presheaf.map (homOfLE (le_refl A)).op x = x := by
  rw [show (homOfLE (le_refl A)).op = 𝟙 (op A) from rfl, CategoryTheory.Functor.map_id]
  rfl

/-- A section vanishes at `x` if its restriction to a smaller open containing `x` does. -/
private theorem VanishesAt.of_map {Z : Scheme.{u}} {P : Z.Modules} {A B : Z.Opens} (hAB : A ≤ B)
    {u : Γ(P, B)} {x : Z} (h : VanishesAt P (P.presheaf.map (homOfLE hAB).op u) x) :
    VanishesAt P u x := by
  obtain ⟨W', hW', n, f, m, hx, hf, hu⟩ := h
  exact ⟨W', hW'.trans hAB, n, f, m, hx, hf, by rw [← hu, map_homOfLE_map_homOfLE]⟩

include h in
private theorem image_preimage_le_preimage_image (V : Y.Opens) :
    o' ''ᵁ (νY ⁻¹ᵁ V) ≤ ν ⁻¹ᵁ (o ''ᵁ V) := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨νY y, hy, ?_⟩
  change (νY ≫ o) y = (o' ≫ ν) y
  rw [h]

/-- The base change isomorphism on sections over `νY⁻¹ V`, compared with the pull-back map. -/
private theorem restrictPullbackIso_pullbackSection (M : X.Modules) (V : Y.Opens)
    (s : Γ(M, o ''ᵁ V)) :
    ((restrictPullbackIso o ν νY o' h).hom.app M).app (νY ⁻¹ᵁ V)
        (pullbackSection νY (M.restrict o) V s) =
      ((Scheme.Modules.pullback ν).obj M).presheaf.map
        (homOfLE (image_preimage_le_preimage_image o ν νY o' h V)).op
        (pullbackSection ν M (o ''ᵁ V) s) := by
  have hV : V ≤ o ⁻¹ᵁ (o ''ᵁ V) := (o.preimage_image_eq V).ge
  set s₂ : Γ(M.restrict o, o ⁻¹ᵁ (o ''ᵁ V)) :=
    M.presheaf.map (homOfLE (o.image_preimage_le (o ''ᵁ V))).op s
  have hs : (M.restrict o).presheaf.map (homOfLE hV).op s₂ = s := by
    change M.presheaf.map (homOfLE (o.image_mono hV)).op s₂ = s
    rw [map_homOfLE_map_homOfLE, map_homOfLE_self]
  have hu := restrictPullbackIso_unit o ν νY o' h M (o ''ᵁ V) s
  conv_lhs => rw [← hs, pullbackSection_map]
  refine (app_map ((restrictPullbackIso o ν νY o' h).hom.app M) (νY.preimage_mono hV) _).trans ?_
  refine (congrArg (((Scheme.Modules.pullback ν).obj M).presheaf.map
    (homOfLE (o'.image_mono (νY.preimage_mono hV))).op) hu).trans ?_
  exact map_homOfLE_map_homOfLE _ _ _ _

include h in
/-- **Descent along a base change by an open immersion.** For a commutative square
`o' ≫ ν = νY ≫ o` with `o`, `o'` open immersions, in which every point of `X'` over `o y` comes
from `Y'`, and `o` preserves and reflects closed points, sections of `M|_Y` descend along `νY` over `V`
exactly when sections of `M` descend along `ν` over `o(V)`. -/
private theorem descends_restrict_iff
    (hfib : ∀ (x : X') (y : Y), ν x = o y → ∃ y' : Y', o' y' = x ∧ νY y' = y)
    (hcl : ∀ y : Y, IsClosed ({o y} : Set X) ↔ IsClosed ({y} : Set Y)) (M : X.Modules)
    (V : Y.Opens) :
    Descends νY (M.restrict o) V ↔ Descends ν M (o ''ᵁ V) := by
  set P := (Scheme.Modules.pullback ν).obj M
  set Q := (Scheme.Modules.pullback νY).obj (M.restrict o)
  set β := (restrictPullbackIso o ν νY o' h).hom.app M
  set γ := (restrictPullbackIso o ν νY o' h).inv.app M
  have eA := image_preimage_le_preimage_image o ν νY o' h
  have eB : ∀ V : Y.Opens, ν ⁻¹ᵁ (o ''ᵁ V) ≤ o' ''ᵁ (νY ⁻¹ᵁ V) := by
    rintro V x ⟨y, hy, hxy⟩
    obtain ⟨y', rfl, rfl⟩ := hfib x y hxy.symm
    exact ⟨y', hy, rfl⟩
  have hγβ : ∀ W (u : Γ(Q, W)), γ.app W (β.app W u) = u := by
    intro W u
    change ((β ≫ γ).app W) u = u
    rw [show β ≫ γ = 𝟙 _ from (restrictPullbackIso o ν νY o' h).hom_inv_id_app M]
    rfl
  have hβγ : ∀ W (u : Γ(P.restrict o', W)), β.app W (γ.app W u) = u := by
    intro W u
    change ((γ ≫ β).app W) u = u
    rw [show γ ≫ β = 𝟙 _ from (restrictPullbackIso o ν νY o' h).inv_hom_id_app M]
    rfl
  have hrr : ∀ V : Y.Opens, ∀ u : Γ(P, ν ⁻¹ᵁ (o ''ᵁ V)),
      P.presheaf.map (homOfLE (eB V)).op (P.presheaf.map (homOfLE (eA V)).op u) = u := by
    intro V u
    rw [map_homOfLE_map_homOfLE, map_homOfLE_self]
  have hrr' : ∀ V : Y.Opens, ∀ u : Γ(P, o' ''ᵁ (νY ⁻¹ᵁ V)),
      P.presheaf.map (homOfLE (eA V)).op (P.presheaf.map (homOfLE (eB V)).op u) = u := by
    intro V u
    rw [map_homOfLE_map_homOfLE, map_homOfLE_self]
  have UC : ∀ V : Y.Opens, ∀ s : Γ(M.restrict o, V),
      β.app (νY ⁻¹ᵁ V) (pullbackSection νY (M.restrict o) V s) =
        P.presheaf.map (homOfLE (eA V)).op (pullbackSection ν M (o ''ᵁ V) s) :=
    fun V s => restrictPullbackIso_pullbackSection o ν νY o' h M V s
  -- injectivity
  have Einj : Function.Injective (pullbackSection νY (M.restrict o) V) ↔
      Function.Injective (pullbackSection ν M (o ''ᵁ V)) := by
    constructor
    · intro hi s₁ s₂ h12
      apply hi
      refine (hγβ _ _).symm.trans (Eq.trans ?_ (hγβ _ _))
      refine congrArg (γ.app _) ((UC V s₁).trans (Eq.trans ?_ (UC V s₂).symm))
      exact congrArg (P.presheaf.map (homOfLE (eA V)).op) h12
    · intro hi s₁ s₂ h12
      apply hi
      have h' : P.presheaf.map (homOfLE (eA V)).op (pullbackSection ν M (o ''ᵁ V) s₁) =
          P.presheaf.map (homOfLE (eA V)).op (pullbackSection ν M (o ''ᵁ V) s₂) :=
        (UC V s₁).symm.trans ((congrArg (β.app _) h12).trans (UC V s₂))
      exact (hrr V _).symm.trans ((congrArg (P.presheaf.map (homOfLE (eB V)).op) h').trans
        (hrr V _))
  -- range
  have E1 : ∀ (t : Γ(Q, νY ⁻¹ᵁ V)) (t' : Γ(P, ν ⁻¹ᵁ (o ''ᵁ V))),
      β.app _ t = P.presheaf.map (homOfLE (eA V)).op t' →
      (t ∈ Set.range (pullbackSection νY (M.restrict o) V) ↔
        t' ∈ Set.range (pullbackSection ν M (o ''ᵁ V))) := by
    intro t t' htt
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨s, ?_⟩
      exact (hrr V _).symm.trans ((congrArg (P.presheaf.map (homOfLE (eB V)).op)
        ((UC V s).symm.trans htt)).trans (hrr V t'))
    · rintro ⟨s, rfl⟩
      refine ⟨s, ?_⟩
      exact (hγβ _ _).symm.trans ((congrArg (γ.app _) ((UC V s).trans htt.symm)).trans
        (hγβ _ t))
  have H1 : ∀ (t : Γ(Q, νY ⁻¹ᵁ V)) (t' : Γ(P, ν ⁻¹ᵁ (o ''ᵁ V))),
      β.app _ t = P.presheaf.map (homOfLE (eA V)).op t' → ∀ y : Y,
      HasCommonValueAt νY (M.restrict o) t y → HasCommonValueAt ν M t' (o y) := by
    intro t t' htt y ⟨V₁, hV₁V, hyV₁, s, hs⟩
    refine ⟨o ''ᵁ V₁, o.image_mono hV₁V, ⟨y, hyV₁, rfl⟩, s, fun x hx => ?_⟩
    obtain ⟨y', rfl, rfl⟩ := hfib x y hx
    have hv := ((hs y' rfl).map β).of_restrict o'
    have key : β.app (νY ⁻¹ᵁ V₁) (Q.presheaf.map (homOfLE (νY.preimage_mono hV₁V)).op t -
        pullbackSection νY (M.restrict o) V₁ s) =
        P.presheaf.map (homOfLE (eA V₁)).op
          (P.presheaf.map (homOfLE (ν.preimage_mono (o.image_mono hV₁V))).op t' -
            pullbackSection ν M (o ''ᵁ V₁) s) := by
      rw [map_sub, map_sub]
      congr 1
      · exact (app_map β _ t).trans ((congrArg ((P.restrict o').presheaf.map
          (homOfLE (νY.preimage_mono hV₁V)).op) htt).trans ((map_homOfLE_map_homOfLE P _ _ t').trans
            (map_homOfLE_map_homOfLE P _ _ t').symm))
      · exact UC V₁ s
    exact VanishesAt.of_map (eA V₁) (key ▸ hv)
  have H2 : ∀ (t : Γ(Q, νY ⁻¹ᵁ V)) (t' : Γ(P, ν ⁻¹ᵁ (o ''ᵁ V))),
      β.app _ t = P.presheaf.map (homOfLE (eA V)).op t' → ∀ y : Y,
      HasCommonValueAt ν M t' (o y) → HasCommonValueAt νY (M.restrict o) t y := by
    intro t t' htt y ⟨V₁', hV₁'V, hyV₁', s, hs⟩
    have hV₁V : o ⁻¹ᵁ V₁' ≤ V := by
      intro z hz
      obtain ⟨w, hw, hwz⟩ := hV₁'V hz
      rwa [o.isOpenEmbedding.injective hwz] at hw
    refine ⟨o ⁻¹ᵁ V₁', hV₁V, hyV₁',
      M.presheaf.map (homOfLE (o.image_preimage_le V₁')).op s, fun y' hy' => ?_⟩
    have hx : ν (o' y') = o y := by
      rw [← hy']
      change (o' ≫ ν) y' = (νY ≫ o) y'
      rw [h]
    have hle : o' ''ᵁ (νY ⁻¹ᵁ (o ⁻¹ᵁ V₁')) ≤ ν ⁻¹ᵁ V₁' :=
      (eA _).trans (ν.preimage_mono (o.image_preimage_le V₁'))
    have hv := (hs (o' y') hx).restrict hle ⟨y', show νY y' ∈ o ⁻¹ᵁ V₁' from hy' ▸ hyV₁', rfl⟩
    have key : P.presheaf.map (homOfLE hle).op
        (P.presheaf.map (homOfLE (ν.preimage_mono hV₁'V)).op t' -
          pullbackSection ν M V₁' s) =
        β.app (νY ⁻¹ᵁ (o ⁻¹ᵁ V₁')) (Q.presheaf.map (homOfLE (νY.preimage_mono hV₁V)).op t -
          pullbackSection νY (M.restrict o) (o ⁻¹ᵁ V₁')
            (M.presheaf.map (homOfLE (o.image_preimage_le V₁')).op s)) := by
      rw [map_sub, map_sub]
      congr 1
      · exact (map_homOfLE_map_homOfLE P _ _ t').trans
          ((map_homOfLE_map_homOfLE P _ _ t').symm.trans
          ((congrArg ((P.restrict o').presheaf.map (homOfLE (νY.preimage_mono hV₁V)).op)
            htt).symm.trans (app_map β _ t).symm))
      · exact ((map_homOfLE_map_homOfLE P (eA _) (ν.preimage_mono (o.image_preimage_le V₁'))
          _).symm.trans (congrArg (P.presheaf.map (homOfLE (eA _)).op)
            (pullbackSection_map _ s).symm)).trans (UC _ _).symm
    have hv3 := ((key ▸ hv).restrict_of o').map γ
    rwa [hγβ] at hv3
  have E2 : ∀ (t : Γ(Q, νY ⁻¹ᵁ V)) (t' : Γ(P, ν ⁻¹ᵁ (o ''ᵁ V))),
      β.app _ t = P.presheaf.map (homOfLE (eA V)).op t' →
      ((∀ y ∈ V, IsClosed ({y} : Set Y) → HasCommonValueAt νY (M.restrict o) t y) ↔
        ∀ c ∈ o ''ᵁ V, IsClosed ({c} : Set X) → HasCommonValueAt ν M t' c) := by
    intro t t' htt
    constructor
    · rintro hY c ⟨y, hyV, rfl⟩ hc
      exact H1 t t' htt y (hY y hyV ((hcl y).mp hc))
    · intro hX y hyV hy
      exact H2 t t' htt y (hX (o y) ⟨y, hyV, rfl⟩ ((hcl y).mpr hy))
  constructor
  · rintro ⟨hi, hr⟩
    refine ⟨Einj.mp hi, fun t' => ?_⟩
    have htt : β.app _ (γ.app _ (P.presheaf.map (homOfLE (eA V)).op t')) =
        P.presheaf.map (homOfLE (eA V)).op t' := hβγ _ _
    rw [← E1 _ t' htt, hr, E2 _ t' htt]
  · rintro ⟨hi, hr⟩
    refine ⟨Einj.mpr hi, fun t => ?_⟩
    have htt : β.app _ t = P.presheaf.map (homOfLE (eA V)).op
        (P.presheaf.map (homOfLE (eB V)).op (β.app _ t)) := (hrr' V _).symm
    rw [E1 t _ htt, hr, E2 t _ htt]

end Transport

section NormalizationLocal

/-- **Descent along normalizations is local for open immersions**: for an open immersion
`φ : Y ⟶ X` of a Jacobson scheme, sections of `M|_Y` descend along the normalization of `Y`
over `V` exactly when sections of `M` descend along the normalization of `X` over `φ(V)`. -/
private theorem descends_normalization_restrict_iff {X Y : Scheme.{u}} (φ : Y ⟶ X)
    [IsOpenImmersion φ] [JacobsonSpace X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite)
    (M : X.Modules) (V : Y.Opens) :
    Descends (normalization Y hY) (M.restrict φ) V ↔ Descends (normalization X hX) M (φ ''ᵁ V) := by
  have sq := isPullback_normalizationSchemeMap_of_etale φ hX
  have hi : IsOpenImmersion (normalizationSchemeMap φ (finite_irreducibleComponents_of_smooth φ hX)
      hX) := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq.flip inferInstance
  exact @descends_restrict_iff _ _ _ _ φ _ (normalization X hX) (normalization Y hY)
    (normalizationSchemeMap φ (finite_irreducibleComponents_of_smooth φ hX) hX) hi sq.w
    (Scheme.exists_preimage_of_isPullback sq)
    (fun y => Set.ext_iff.mp φ.isOpenEmbedding.preimage_closedPoints y) M V

end NormalizationLocal

section Statement

variable {X X' : Scheme.{u}} {ν : X' ⟶ X} {L : X.Modules}

/-- Restricting a difference in two steps is restricting it in one. -/
private theorem map_sub_map {M : X'.Modules} {A B C : X'.Opens} (h₁ : A ≤ B) (h₂ : B ≤ C)
    (t : Γ(M, C)) (u : Γ(M, B)) :
    M.presheaf.map (homOfLE h₁).op (M.presheaf.map (homOfLE h₂).op t - u) =
      M.presheaf.map (homOfLE (h₁.trans h₂)).op t - M.presheaf.map (homOfLE h₁).op u := by
  rw [map_sub, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- `HasCommonValueAt` spelled out, as in the statement. -/
private theorem hasCommonValueAt_iff {U : X.Opens}
    (t : Γ((Scheme.Modules.pullback ν).obj L, ν ⁻¹ᵁ U)) (c : X) :
    HasCommonValueAt ν L t c ↔
      ∃ (V : X.Opens) (hVU : V ≤ U), c ∈ V ∧ ∃ s : Γ(L, V), ∀ x : X', ν x = c →
        ∃ (W : X'.Opens) (hW : W ≤ ν ⁻¹ᵁ V) (n : ℕ) (f : Fin n → Γ(X', W))
          (m : Fin n → Γ((Scheme.Modules.pullback ν).obj L, W)),
          x ∈ W ∧ (∀ i, x ∉ X'.basicOpen (f i)) ∧
          ((Scheme.Modules.pullback ν).obj L).presheaf.map
              (homOfLE (hW.trans (ν.preimage_mono hVU))).op t -
            ((Scheme.Modules.pullback ν).obj L).presheaf.map (homOfLE hW).op
              ((((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).app V).hom s) =
            ∑ i, f i • m i := by
  unfold HasCommonValueAt VanishesAt
  simp only [map_sub_map]
  rfl

end Statement

section Criterion

variable {X X' : Scheme.{u}} (ν : X' ⟶ X)

/-- A point outside the basic opens of finitely many functions is outside that of their sum. -/
private theorem notMem_basicOpen_sum {W : X'.Opens} {n : ℕ} (a : Fin n → Γ(X', W)) {x : X'}
    (h : ∀ i, x ∉ X'.basicOpen (a i)) : x ∉ X'.basicOpen (∑ i, a i) :=
  Finset.sum_induction _ (fun g => x ∉ X'.basicOpen g)
    (fun a b ha hb hab => (X'.basicOpen_add_le a b hab).elim ha hb)
    (by rw [Scheme.basicOpen_zero]; exact fun h => h) fun i _ => h i

/-- On the pull-back of `𝒪_X`, a combination `∑ fᵢ mᵢ` with all `fᵢ` vanishing at `x` is a single
`f • τ` with `f` vanishing at `x`. -/
private theorem exists_eq_smul_of_eq_sum {W : X'.Opens} {n : ℕ} (f : Fin n → Γ(X', W))
    (m : Fin n → Γ((Scheme.Modules.pullback ν).obj (SheafOfModules.unit X.ringCatSheaf), W))
    {x : X'} (hf : ∀ i, x ∉ X'.basicOpen (f i)) :
    ∃ (g : Γ(X', W))
      (τ : Γ((Scheme.Modules.pullback ν).obj (SheafOfModules.unit X.ringCatSheaf), W)),
      x ∉ X'.basicOpen g ∧ ∑ i, f i • m i = g • τ := by
  let O : X'.Modules := SheafOfModules.unit X'.ringCatSheaf
  let φ : (Scheme.Modules.pullback ν).obj (SheafOfModules.unit X.ringCatSheaf) ≅ O :=
    Stacks.PullbackAlgebra.pullbackUnitIso ν.toLRSHom.toShHom
  let c : Γ(O, W) → Γ(X', W) := fun a => a
  let c' : Γ(X', W) → Γ(O, W) := fun a => a
  have hm : ∀ u : Γ((Scheme.Modules.pullback ν).obj (SheafOfModules.unit X.ringCatSheaf), W),
      u = c (φ.hom.app W u) • φ.inv.app W (c' 1) := by
    intro u
    have h1 : c (φ.hom.app W u) • c' 1 = φ.hom.app W u := mul_one (c (φ.hom.app W u))
    have h2 : φ.inv.app W (φ.hom.app W u) = u := by
      change ((φ.hom ≫ φ.inv).app W) u = u
      rw [show φ.hom ≫ φ.inv = 𝟙 _ from φ.hom_inv_id]
      rfl
    exact h2.symm.trans ((congrArg (φ.inv.app W) h1.symm).trans
      (Scheme.Modules.Hom.app_smul φ.inv _ _))
  refine ⟨∑ i, f i * c (φ.hom.app W (m i)), φ.inv.app W (c' 1),
    notMem_basicOpen_sum _ fun i hi => hf i ?_, ?_⟩
  · rw [Scheme.basicOpen_mul] at hi
    exact hi.1
  · rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul, ← hm]

/-- **Descent of functions from the ∃!-form of the descent criterion.** -/
private theorem descends_unit_of_existsUnique {U : X.Opens}
    (crit : ∀ s : Γ((Scheme.Modules.pullback ν).obj (SheafOfModules.unit X.ringCatSheaf),
        ν ⁻¹ᵁ U),
      (∃! t : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U),
        pullbackSection ν (SheafOfModules.unit X.ringCatSheaf) U t = s) ↔
      ∀ w ∈ U, IsClosed ({w} : Set X) →
        ∃ (V : X.Opens) (hVU : V ≤ U) (t : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), V)),
          w ∈ V ∧ ∀ w' : X', ν w' = w →
            ∃ (V' : X'.Opens) (hV' : V' ≤ ν ⁻¹ᵁ V) (f : Γ(X', V'))
              (τ : Γ((Scheme.Modules.pullback ν).obj (SheafOfModules.unit X.ringCatSheaf), V')),
              w' ∈ V' ∧ w' ∉ X'.basicOpen f ∧
              ((Scheme.Modules.pullback ν).obj (SheafOfModules.unit X.ringCatSheaf)).presheaf.map
                  (homOfLE (hV'.trans (ν.preimage_mono hVU))).op s -
                ((Scheme.Modules.pullback ν).obj (SheafOfModules.unit X.ringCatSheaf)).presheaf.map
                  (homOfLE hV').op
                  (pullbackSection ν (SheafOfModules.unit X.ringCatSheaf) V t) = f • τ) :
    Descends ν (SheafOfModules.unit X.ringCatSheaf) U := by
  set L : X.Modules := SheafOfModules.unit X.ringCatSheaf
  set P := (Scheme.Modules.pullback ν).obj L
  have triv : ∀ t : Γ(L, U), ∀ w ∈ U, IsClosed ({w} : Set X) →
      ∃ (V : X.Opens) (hVU : V ≤ U) (t' : Γ(L, V)), w ∈ V ∧ ∀ w' : X', ν w' = w →
        ∃ (V' : X'.Opens) (hV' : V' ≤ ν ⁻¹ᵁ V) (f : Γ(X', V')) (τ : Γ(P, V')),
          w' ∈ V' ∧ w' ∉ X'.basicOpen f ∧
          P.presheaf.map (homOfLE (hV'.trans (ν.preimage_mono hVU))).op
              (pullbackSection ν L U t) -
            P.presheaf.map (homOfLE hV').op (pullbackSection ν L V t') = f • τ := by
    intro t w hw _
    refine ⟨U, le_rfl, t, hw, fun w' hw' => ⟨ν ⁻¹ᵁ U, le_rfl, 0, 0,
      show ν w' ∈ U by rw [hw']; exact hw, by rw [Scheme.basicOpen_zero]; exact id, ?_⟩⟩
    rw [zero_smul, sub_eq_zero]
  refine ⟨fun t₁ t₂ h => ?_, fun t => ⟨?_, fun h => ?_⟩⟩
  · obtain ⟨t, -, ht⟩ := (crit _).mpr (triv t₁)
    exact (ht t₁ rfl).trans (ht t₂ h.symm).symm
  · rintro ⟨s, rfl⟩ c hc -
    exact hasCommonValueAt_pullbackSection s hc
  · refine ((crit t).mpr fun w hw hcl => ?_).exists
    obtain ⟨V, hVU, hwV, s₀, hs⟩ := h w hw hcl
    refine ⟨V, hVU, s₀, hwV, fun w' hw' => ?_⟩
    obtain ⟨W', hW', n, f, m, hxW', hf, heq⟩ := hs w' hw'
    obtain ⟨g, τ, hg, hgτ⟩ := exists_eq_smul_of_eq_sum ν f m hf
    refine ⟨W', hW', g, τ, hxW', hg, ?_⟩
    rw [← map_sub_map hW' (ν.preimage_mono hVU), heq, hgτ]

end Criterion

section Local

/-- The structure sheaf is a line bundle. -/
private theorem isLineBundle_unit (X : Scheme.{u}) :
    MMP.Intersection.Scheme.Modules.IsLineBundle (SheafOfModules.unit X.ringCatSheaf) :=
  fun _ => ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι ≪≫
    (Limits.coproductUniqueIso (fun (_ : ULift.{u} (Fin 1)) =>
      SheafOfModules.unit (⊤ : X.Opens).toScheme.ringCatSheaf)).symm⟩⟩

/-- **The normalization of a reduced curve is an isomorphism over a dense open with dense
preimage**: over the regular locus, whose complement is finite and contains no generic point. -/
private theorem exists_isIso_resLE_normalization {X : Scheme.{u}} [IsReduced X] [CompactSpace X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hNag : IsNagataScheme X) (hdim : topologicalKrullDim X ≤ 1) :
    ∃ U₀ : X.Opens, Dense U₀.carrier ∧ Dense (normalization X hX ⁻¹ᵁ U₀).carrier ∧
      IsIso ((normalization X hX).resLE U₀ (normalization X hX ⁻¹ᵁ U₀) le_rfl) := by
  have hgen : genericPoints X ⊆ regularLocus X := fun x hx =>
    mem_regularLocus_of_closure_mem_irreducibleComponents X x hx
  let U₀ : X.Opens := ⟨regularLocus X, isOpen_regularLocus_of_isNagataScheme X hNag hdim⟩
  refine ⟨U₀, (dense_iff_closure_eq.mpr genericPoints.closure).mono hgen,
    (dense_iff_closure_eq.mpr genericPoints.closure).mono
      fun z hz => hgen (Scheme.normalization_mem_genericPoints X hX hz), ?_⟩
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact isIso_morphismRestrict_normalization_of_subset_regularLocus hX U₀ le_rfl

/-- A finite union of closed sets of dimension at most one has dimension at most one. -/
private theorem topologicalKrullDim_vanishingIdeal_subscheme_le {X : Scheme.{u}}
    (S : Finset (TopologicalSpace.IrreducibleCloseds X))
    (hS : ∀ Z ∈ S, topologicalKrullDim (Z : Set X) ≤ 1) :
    topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
      ⟨⋃ Z ∈ S, (Z : Set X), S.finite_toSet.isClosed_biUnion fun Z _ => Z.isClosed⟩).subscheme ≤
      1 := by
  set I := Scheme.IdealSheafData.vanishingIdeal
      ⟨⋃ Z ∈ S, (Z : Set X), S.finite_toSet.isClosed_biUnion fun Z _ => Z.isClosed⟩
  have hrange : Set.range I.subschemeι = ⋃ Z ∈ S, (Z : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  have hmem : ∀ y, I.subschemeι y ∈ ⋃ Z ∈ S, (Z : Set X) := fun y => hrange ▸ ⟨y, rfl⟩
  exact ((I.subschemeι.isEmbedding.isInducing).codRestrict hmem).topologicalKrullDim_le.trans
    (topologicalKrullDim_biUnion_le S (fun Z => Z.isClosed) hS)

/-- **Functions on the reduced boundary of a projective lc surface descend**: on a normal
projective complex surface with an lc boundary `B`, functions on the normalization of `⌊B⌋`
descend to `⌊B⌋` exactly when their values over each closed point agree. The components of
`⌊B⌋` are lc centres, and this is
`MMP.Mori.IsLcPair.existsUnique_unit_app_eq_iff_of_isNormalization`
for the structure sheaf. -/
private theorem descends_unit_roundDown {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V]
    [IsNormal V] {sV : V ⟶ Spec (.of ℂ)} (hproj : MMP.Mori.IsProjectiveVariety ℂ sV)
    (hdim : topologicalKrullDim V = 2) {B : QDivisor V}
    (hB : MMP.Intersection.IsLogCanonicalPair sV B)
    (hW : ∀ U : (DivisorWithCoeffs.roundDown B).suppScheme.Opens,
      IsCompact (U : Set (DivisorWithCoeffs.roundDown B).suppScheme) →
      (irreducibleComponents U).Finite)
    (U : (DivisorWithCoeffs.roundDown B).suppScheme.Opens) :
    Descends (normalization (DivisorWithCoeffs.roundDown B).suppScheme hW)
      (SheafOfModules.unit (DivisorWithCoeffs.roundDown B).suppScheme.ringCatSheaf) U := by
  classical
  obtain ⟨⟨hX, n, K, hK, hQ⟩, hnn, -⟩ := id hB
  have hn : n = 2 := by
    have h := hK.topologicalKrullDim_eq
    rw [hdim] at h
    exact_mod_cast h.symm
  subst hn
  have hlc := isLcPair_of_isLogCanonicalPair hB hK
  set S₀ : Finset (TopologicalSpace.IrreducibleCloseds V) :=
    (DivisorWithCoeffs.roundDown B).support.image fun P =>
      (DivisorOver.ofPrimeDivisor ℂ hX P).center
  have hS : ∀ Z ∈ S₀, ∃ E : DivisorOver ℂ sV, E.center = Z ∧ IsDiscrepancy sV 2 K B E (-1) := by
    intro Z hZ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hZ
    have h0 : ⌊B.coeff P⌋ ≠ 0 := by
      have := Finsupp.mem_support_iff.mp hP
      rwa [← DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_roundDown] at this
    have h1 : B.coeff P = 1 := by
      by_contra hne
      exact h0 (Int.floor_eq_zero_iff.mpr
        ⟨hnn P, (coeff_le_one_of_isLogCanonicalPair hB P).lt_of_ne hne⟩)
    have hd := isDiscrepancy_ofPrimeDivisor hlc.1 P
    rw [h1] at hd
    exact ⟨_, rfl, hd⟩
  have hSdim : ∀ Z ∈ S₀, topologicalKrullDim (Z : Set V) ≤ 1 := by
    intro Z hZ
    obtain ⟨P, -, rfl⟩ := Finset.mem_image.mp hZ
    rw [coe_center_ofPrimeDivisor]
    exact topologicalKrullDim_support_le_one hdim P
  have hI : (DivisorWithCoeffs.roundDown B).suppIdeal = Scheme.IdealSheafData.vanishingIdeal
      ⟨⋃ Z ∈ S₀, (Z : Set V), S₀.finite_toSet.isClosed_biUnion fun Z _ => Z.isClosed⟩ := by
    refine congrArg Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.ext ?_)
    rw [DivisorWithCoeffs.coe_supp]
    ext x
    change x ∈ ⋃ E ∈ (DivisorWithCoeffs.roundDown B).support, (E.support : Set V) ↔
      x ∈ ⋃ Z ∈ S₀, (Z : Set V)
    rw [Set.mem_iUnion₂, Set.mem_iUnion₂]
    constructor
    · rintro ⟨P, hP, hx⟩
      refine ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hP), ?_⟩
      rw [coe_center_ofPrimeDivisor]
      exact hx
    · rintro ⟨Z, hZ, hx⟩
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hZ)
      refine ⟨P, hP, ?_⟩
      rwa [coe_center_ofPrimeDivisor] at hx
  haveI : LocallyOfFiniteType sV := hX.1.toLocallyOfFiniteType
  haveI : CompactSpace V := haveI := hX.1; QuasiCompact.compactSpace_of_compactSpace sV
  suffices H : ∀ (I : V.IdealSheafData), I = Scheme.IdealSheafData.vanishingIdeal
      ⟨⋃ Z ∈ S₀, (Z : Set V), S₀.finite_toSet.isClosed_biUnion fun Z _ => Z.isClosed⟩ →
      ∀ (hW : ∀ U : I.subscheme.Opens, IsCompact (U : Set I.subscheme) →
        (irreducibleComponents U).Finite) (U : I.subscheme.Opens),
      Descends (normalization I.subscheme hW) (SheafOfModules.unit I.subscheme.ringCatSheaf) U from
    H _ hI hW U
  intro I hI hW U
  subst hI
  haveI : IsNormal (normalizationScheme _ hW) := Scheme.isNormal_normalizationScheme _ hW
  haveI : CompactSpace (Scheme.IdealSheafData.vanishingIdeal
      ⟨⋃ Z ∈ S₀, (Z : Set V), S₀.finite_toSet.isClosed_biUnion fun Z _ => Z.isClosed⟩).subscheme :=
    (Scheme.IdealSheafData.subschemeι _).isClosedEmbedding.compactSpace
  have hν := exists_isIso_resLE_normalization hW
    (isNagataScheme_of_locallyOfFiniteType_over_field ℂ (Scheme.IdealSheafData.subschemeι _ ≫ sV))
    (topologicalKrullDim_vanishingIdeal_subscheme_le S₀ hSdim)
  exact descends_unit_of_existsUnique _ fun s =>
    IsLcPair.existsUnique_unit_app_eq_iff_of_isNormalization hproj hdim hlc hnn S₀ hS hSdim
      (normalization _ hW) hν _ (isLineBundle_unit _) U s

section InverseTransform

variable {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- An open immersion is biregular over its image. -/
private theorem opensRange_le_biregularLocus : j.opensRange ≤ biregularLocus j := by
  refine MMP.Mori.le_biregularLocus ?_
  change IsIso (j ∣_ j.opensRange)
  rw [isIso_iff_isOpenImmersion_and_epi_base]
  refine ⟨inferInstance, (TopCat.epi_iff_surjective _).mpr ?_⟩
  rintro ⟨v, u, rfl⟩
  have hv : u ∈ j ⁻¹ᵁ j.opensRange := ⟨u, rfl⟩
  refine ⟨⟨u, hv⟩, Subtype.ext ?_⟩
  change (j ∣_ j.opensRange ≫ j.opensRange.ι) ⟨u, hv⟩ = j u
  rw [morphismRestrict_ι]
  rfl

/-- Along an open immersion, the inverse transform of a prime divisor `Q` is `P` exactly when `Q`
is the closure of `P`. -/
private theorem inverseTransformPrimeDivisor_eq_some_iff_of_isOpenImmersion [IsIntegral X]
    [IsIntegral U] (Q : MMP.Mori.PrimeDivisor X) (P : MMP.Mori.PrimeDivisor U) :
    inverseTransformPrimeDivisor j Q = some P ↔ Q = OpenWeilRestriction.primeDivisorMap j P := by
  constructor
  · intro h
    obtain ⟨h1, -⟩ :=
      MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some h
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    rw [OpenWeilRestriction.genericPoint_primeDivisorMap]
    exact h1.symm
  · rintro rfl
    exact MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      (OpenWeilRestriction.genericPoint_primeDivisorMap j P).symm
      (opensRange_le_biregularLocus j ⟨_, rfl⟩)

/-- Along an open immersion, the coefficients of the inverse transform are those of the
closures. -/
private theorem coeff_inverseTransformDivisor_of_isOpenImmersion [IsIntegral X] [IsIntegral U]
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R X) (P : MMP.Mori.PrimeDivisor U) :
    (inverseTransformDivisor j D).coeff P = D.coeff (OpenWeilRestriction.primeDivisorMap j P) := by
  change DivisorWithCoeffs.mapPrimeDivisors _ D P = _
  rw [MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    ((inverseTransformPrimeDivisor_eq_some_iff_of_isOpenImmersion j _ P).2 rfl)
    (fun E' h => (inverseTransformPrimeDivisor_eq_some_iff_of_isOpenImmersion j E' P).1 h)]
  rfl

/-- The support of `⌊D⌋` pulls back along an open immersion to that of `⌊j⁻¹_* D⌋`. -/
private theorem preimage_supp_roundDown [IsIntegral X] [IsIntegral U] (D : QDivisor X) :
    j ⁻¹' (DivisorWithCoeffs.roundDown D).supp =
      (DivisorWithCoeffs.roundDown (inverseTransformDivisor j D)).supp := by
  ext x
  simp only [Set.mem_preimage, SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff,
    DivisorWithCoeffs.coeff_roundDown, coeff_inverseTransformDivisor_of_isOpenImmersion]
  constructor
  · rintro ⟨P, hP, hx⟩
    have hx' : j x ∈ (P.support : Set X) := hx
    have hgen : P.genericPoint ∈ Set.range j := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hx'
      exact hx'.mem_open j.isOpenEmbedding.isOpen_range ⟨x, rfl⟩
    obtain ⟨E, rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff j P).2 hgen
    exact ⟨E, hP, (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff j E x).1 hx'⟩
  · rintro ⟨E, hE, hx⟩
    exact ⟨_, hE, (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff j E x).2 hx⟩

end InverseTransform

/-- **Reduced closed subschemes restrict along open immersions**: if `j⁻¹ Z = Z'`, the reduced
subscheme on `Z'` is an open subscheme of the reduced subscheme on `Z`, namely its part over the
image of `j`: both are reduced closed subschemes of `U` with support `Z'`. -/
private theorem exists_isOpenImmersion_vanishingIdeal {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (Z : TopologicalSpace.Closeds X) (Z' : TopologicalSpace.Closeds U)
    (hZ : j ⁻¹' (Z : Set X) = Z') :
    ∃ φ : (Scheme.IdealSheafData.vanishingIdeal Z').subscheme ⟶
        (Scheme.IdealSheafData.vanishingIdeal Z).subscheme,
      IsOpenImmersion φ ∧ Set.range φ =
        (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ⁻¹' Set.range j := by
  set ιZ := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  have hrange : Set.range ιZ = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp
  have hsnd : Set.range (Limits.pullback.snd ιZ j) = Z' := by
    rw [Scheme.Pullback.range_snd, hrange, hZ]
  haveI : IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal Z
  haveI : IsReduced (Limits.pullback ιZ j) :=
    isReduced_of_isOpenImmersion (Limits.pullback.fst ιZ j)
  have hker : (Limits.pullback.snd ιZ j).ker = Scheme.IdealSheafData.vanishingIdeal Z' := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    congr 1
    ext1
    change closure (Set.range (Limits.pullback.snd ιZ j)) = (Z' : Set U)
    rw [hsnd]
    exact Z'.isClosed.closure_eq
  obtain ⟨e', -⟩ : ∃ e' : Limits.pullback ιZ j ≅
      (Scheme.IdealSheafData.vanishingIdeal Z').subscheme, True :=
    ⟨hker ▸ asIso (Limits.pullback.snd ιZ j).toImage, trivial⟩
  haveI : IsOpenImmersion e'.inv := IsOpenImmersion.of_isIso e'.inv
  refine ⟨e'.inv ≫ Limits.pullback.fst ιZ j, inferInstance, ?_⟩
  ext y
  rw [← Scheme.Pullback.range_fst]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨e'.inv z, rfl⟩
  · rintro ⟨z, rfl⟩
    refine ⟨e'.hom z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, e'.hom_inv_id, Category.id_comp]

/-- A nonempty dominant open subscheme of a normal variety has the dimension of the variety: both are the
transcendence degree of the common function field. -/
private theorem topologicalKrullDim_opens_eq {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hbij : Function.Bijective (functionFieldMap U.ι) :=
    functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤ ⟨Classical.arbitrary U, trivial⟩
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-- **A common open of `⌊B⌋` and of the boundary of a projective completion.** Near every point
of `C = ⌊B⌋`, inside any given open, `C` has an open subscheme which is also an open subscheme of
`⌊B_V⌋` for a normal projective lc surface `(V, B_V)`: restrict `(S, B)` to an affine open, which
stays lc, and complete it by `MMP.Threefold.exists_isOpenImmersion_isLogCanonicalPair_of_isAffine`;
the two reduced boundaries have the same support over the affine open. -/
private theorem exists_common_open_roundDown
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hdim : topologicalKrullDim S = 2) {B : QDivisor S}
    (hB : MMP.Intersection.IsLogCanonicalPair sS B)
    (O₁ : (DivisorWithCoeffs.roundDown B).suppScheme.Opens)
    {x : (DivisorWithCoeffs.roundDown B).suppScheme} (hx : x ∈ O₁) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (sV : V ⟶ Spec (.of ℂ)) (BV : QDivisor V) (C' : Scheme.{0})
      (φ₁ : C' ⟶ (DivisorWithCoeffs.roundDown B).suppScheme)
      (φ₂ : C' ⟶ (DivisorWithCoeffs.roundDown BV).suppScheme),
      IsOpenImmersion φ₁ ∧ IsOpenImmersion φ₂ ∧ MMP.Mori.IsProjectiveVariety ℂ sV ∧
      topologicalKrullDim V = 2 ∧ MMP.Intersection.IsLogCanonicalPair sV BV ∧
      x ∈ Set.range φ₁ ∧ Set.range φ₁ ⊆ O₁ := by
  classical
  set ιC := (DivisorWithCoeffs.roundDown B).suppIdeal.subschemeι
  obtain ⟨G, hG, hGO⟩ := ιC.isEmbedding.isInducing.isOpen_iff.mp O₁.isOpen
  have hxG : ιC x ∈ G := by
    change x ∈ ιC ⁻¹' G
    rw [hGO]
    exact hx
  obtain ⟨_, ⟨US, hUS, rfl⟩, hxUS, hUSG⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hxG hG
  haveI : Nonempty US := ⟨⟨_, hxUS⟩⟩
  haveI : IsAffine US := hUS
  have hX : IsNormalVariety ℂ sS := hB.1.1
  have hBU := isLogCanonicalPair_restrictOpen hB US
  haveI : IsDominant (Scheme.Opens.ι US) := Opens.isDominant_ι (US.isOpen.dense ⟨_, hxUS⟩)
  have hdimU : topologicalKrullDim US = 2 := (topologicalKrullDim_opens_eq hX US).trans hdim
  obtain ⟨V, hVi, hVl, hVn, sV, j, BV, hj, -, hproj, hdimV, hBV, hinv⟩ :=
    MMP.Threefold.exists_isOpenImmersion_isLogCanonicalPair_of_isAffine (Scheme.Opens.ι US ≫ sS)
      hdimU hBU
  haveI := hj
  have h1 : Scheme.Opens.ι US ⁻¹' ((DivisorWithCoeffs.roundDown B).supp : Set S) =
      (DivisorWithCoeffs.roundDown (B.restrictOpen US)).supp := by
    rw [preimage_supp_roundDown, MMP.Mori.inverseTransformDivisor_ι_eq_restrictOpen]
  have h2 : j ⁻¹' ((DivisorWithCoeffs.roundDown BV).supp : Set V) =
      (DivisorWithCoeffs.roundDown (B.restrictOpen US)).supp := by
    rw [preimage_supp_roundDown, hinv]
  obtain ⟨φ₁, hφ₁, hr₁⟩ := exists_isOpenImmersion_vanishingIdeal (Scheme.Opens.ι US) _ _ h1
  obtain ⟨φ₂, hφ₂, -⟩ := exists_isOpenImmersion_vanishingIdeal j _ _ h2
  refine ⟨V, hVi, hVl, hVn, sV, BV, _, φ₁, φ₂, hφ₁, hφ₂, hproj, hdimV, hBV, ?_, ?_⟩
  · exact (Set.ext_iff.mp hr₁ x).mpr
      (show ιC x ∈ Set.range (Scheme.Opens.ι US) from (Scheme.Opens.range_ι US).symm ▸ hxUS)
  · intro y hy
    have hy' : ιC y ∈ Set.range (Scheme.Opens.ι US) := (Set.ext_iff.mp hr₁ y).mp hy
    rw [Scheme.Opens.range_ι] at hy'
    exact hGO ▸ (show y ∈ ιC ⁻¹' G from hUSG hy')

/-- **The local step.** Every point of `C = ⌊B⌋` has an open neighbourhood over whose opens
sections of `L` descend along the normalization of `C`. -/
private theorem exists_descends_nhds
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hdim : topologicalKrullDim S = 2) {B : QDivisor S}
    (hB : MMP.Intersection.IsLogCanonicalPair sS B)
    (hC : ∀ U : (DivisorWithCoeffs.roundDown B).suppScheme.Opens,
      IsCompact (U : Set (DivisorWithCoeffs.roundDown B).suppScheme) →
      (irreducibleComponents U).Finite)
    (L : (DivisorWithCoeffs.roundDown B).suppScheme.Modules)
    [Stacks.Ample.IsInvertibleModule (DivisorWithCoeffs.roundDown B).suppScheme L]
    (x : (DivisorWithCoeffs.roundDown B).suppScheme) :
    ∃ O : (DivisorWithCoeffs.roundDown B).suppScheme.Opens, x ∈ O ∧
      ∀ U ≤ O, Descends (normalization (DivisorWithCoeffs.roundDown B).suppScheme hC) L U := by
  haveI : LocallyOfFiniteType sS := hB.1.1.1.toLocallyOfFiniteType
  haveI : JacobsonSpace (DivisorWithCoeffs.roundDown B).suppScheme :=
    LocallyOfFiniteType.jacobsonSpace ((DivisorWithCoeffs.roundDown B).suppIdeal.subschemeι ≫ sS)
  obtain ⟨O₁, hxO₁, ⟨e⟩⟩ := (isInvertible_iff_exists_restrict_iso_unit _ L).mp ‹_› x
  obtain ⟨V, _, _, _, sV, BV, C', φ₁, φ₂, h₁, h₂, hproj, hdimV, hBV, hx, hsub⟩ :=
    exists_common_open_roundDown sS hdim hB O₁ hxO₁
  haveI := h₁
  haveI := h₂
  haveI : LocallyOfFiniteType sV := hBV.1.1.1.toLocallyOfFiniteType
  haveI : JacobsonSpace (DivisorWithCoeffs.roundDown BV).suppScheme :=
    LocallyOfFiniteType.jacobsonSpace ((DivisorWithCoeffs.roundDown BV).suppIdeal.subschemeι ≫ sV)
  have hW := finite_irreducibleComponents_of_isNagataScheme _
    (isNagataScheme_of_locallyOfFiniteType_over_field ℂ
      ((DivisorWithCoeffs.roundDown BV).suppIdeal.subschemeι ≫ sV))
  have hC' := finite_irreducibleComponents_of_smooth φ₁ hC
  let ψ := IsOpenImmersion.lift O₁.ι φ₁ (by rw [Scheme.Opens.range_ι]; exact hsub)
  have hψ : ψ ≫ O₁.ι = φ₁ := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion (ψ ≫ O₁.ι) := hψ ▸ h₁
  haveI : IsOpenImmersion ψ := IsOpenImmersion.of_comp ψ O₁.ι
  let e₁ : L.restrict φ₁ ≅ SheafOfModules.unit C'.ringCatSheaf :=
    (Scheme.Modules.restrictFunctorCongr hψ.symm).app L ≪≫
      (Scheme.Modules.restrictFunctorComp ψ O₁.ι).app L ≪≫
      (Scheme.Modules.restrictFunctor ψ).mapIso e ≪≫ Scheme.Modules.restrictUnitIso ψ
  refine ⟨φ₁.opensRange, hx, fun U hU => ?_⟩
  have hUe : φ₁ ''ᵁ (φ₁ ⁻¹ᵁ U) = U := by
    rw [φ₁.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hU]
  rw [← hUe, ← descends_normalization_restrict_iff φ₁ hC hC' L, descends_iff_of_iso e₁,
    descends_iff_of_iso (Scheme.Modules.restrictUnitIso φ₂).symm]
  exact (descends_normalization_restrict_iff φ₂ hW hC' _ _).mpr
    (descends_unit_roundDown hproj hdimV hBV hW _)

end Local

/-- **Sections of a line bundle on the reduced boundary of an lc surface.** Let `(S, B)` be a
log canonical pair with `B` a `ℚ`-divisor on a normal complex surface `S`, let `C` be `⌊B⌋`
with its reduced structure, `ν : Cᵛ ⟶ C` its normalization and `L` an invertible sheaf on `C`.
For every open `U ⊆ C`, the map `Γ(U, L) → Γ(ν⁻¹U, ν^*L)` given by the unit of `ν^* ⊣ ν_*` is
injective, and a section `t` of `ν^*L` over `ν⁻¹U` lies in its image if and only if, for every
closed point `c ∈ U`, there are an open `c ∈ V ⊆ U` and `s ∈ Γ(V, L)` such that `t - ν^*s`
vanishes at every point of `Cᵛ` over `c`, i.e. the values of `t` over `c` agree in `L(c)`. -/
@[mmp "lem_mmp_surface_lc_boundary_seminormal_functions"]
public theorem injective_and_mem_range_iff_unit_app_roundDown_suppScheme
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hdim : topologicalKrullDim S = 2) {B : QDivisor S}
    (hB : MMP.Intersection.IsLogCanonicalPair sS B)
    (hC : ∀ U : (DivisorWithCoeffs.roundDown B).suppScheme.Opens,
      IsCompact (U : Set (DivisorWithCoeffs.roundDown B).suppScheme) →
      (irreducibleComponents U).Finite)
    (L : (DivisorWithCoeffs.roundDown B).suppScheme.Modules)
    [Stacks.Ample.IsInvertibleModule (DivisorWithCoeffs.roundDown B).suppScheme L]
    (U : (DivisorWithCoeffs.roundDown B).suppScheme.Opens) :
    Function.Injective
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (normalization (DivisorWithCoeffs.roundDown B).suppScheme hC)).unit.app L).app
          U).hom ∧
      ∀ t : Γ((Scheme.Modules.pullback
          (normalization (DivisorWithCoeffs.roundDown B).suppScheme hC)).obj L,
          normalization (DivisorWithCoeffs.roundDown B).suppScheme hC ⁻¹ᵁ U),
        t ∈ Set.range
            (((Scheme.Modules.pullbackPushforwardAdjunction
              (normalization (DivisorWithCoeffs.roundDown B).suppScheme hC)).unit.app
              L).app U).hom ↔
          ∀ c ∈ U, IsClosed ({c} : Set (DivisorWithCoeffs.roundDown B).suppScheme) →
            ∃ (V : (DivisorWithCoeffs.roundDown B).suppScheme.Opens) (hVU : V ≤ U),
              c ∈ V ∧ ∃ s : Γ(L, V),
                ∀ x : normalizationScheme (DivisorWithCoeffs.roundDown B).suppScheme hC,
                  normalization (DivisorWithCoeffs.roundDown B).suppScheme hC x = c →
                  ∃ (W : (normalizationScheme (DivisorWithCoeffs.roundDown B).suppScheme hC).Opens)
                    (hW : W ≤ normalization (DivisorWithCoeffs.roundDown B).suppScheme hC ⁻¹ᵁ V)
                    (n : ℕ)
                    (f : Fin n → Γ(normalizationScheme
                      (DivisorWithCoeffs.roundDown B).suppScheme hC, W))
                    (m : Fin n → Γ((Scheme.Modules.pullback
                      (normalization (DivisorWithCoeffs.roundDown B).suppScheme hC)).obj L, W)),
                    x ∈ W ∧ (∀ i, x ∉ (normalizationScheme
                      (DivisorWithCoeffs.roundDown B).suppScheme hC).basicOpen (f i)) ∧
                    ((Scheme.Modules.pullback
                      (normalization (DivisorWithCoeffs.roundDown B).suppScheme hC)).obj
                        L).presheaf.map
                        (homOfLE (hW.trans
                          ((normalization (DivisorWithCoeffs.roundDown B).suppScheme
                            hC).preimage_mono hVU))).op t -
                      ((Scheme.Modules.pullback
                        (normalization (DivisorWithCoeffs.roundDown B).suppScheme hC)).obj
                          L).presheaf.map
                        (homOfLE hW).op
                        ((((Scheme.Modules.pullbackPushforwardAdjunction
                          (normalization (DivisorWithCoeffs.roundDown B).suppScheme hC)).unit.app
                            L).app V).hom s) =
                      ∑ i, f i • m i := by
  obtain ⟨hinj, hrange⟩ := descends_of_forall_mem (exists_descends_nhds sS hdim hB hC L) U
  exact ⟨hinj, fun t => (hrange t).trans
    (forall₂_congr fun c _ => imp_congr_right fun _ => hasCommonValueAt_iff t c)⟩

end MMP.Threefold
