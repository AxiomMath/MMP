module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldTerminalChain
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
import MMP.AlgebraicGeometry.MMP.Threefold.StepDiagram.BadLociTerminalChain
import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldTerminalChainLabel
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagramBranches
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoMonomialValuation
import MMP.AlgebraicGeometry.RegularEmbedding.ExceptionalBundle
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.RingTheory.RegularLocalRing.FiniteFreeResolution
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Singularities.DiscrepancyCommonModel
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Morphisms.ChowLemma
import MMP.AlgebraicGeometry.Resolution.CommonNormalModel
import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero
import MMP.AlgebraicGeometry.ProjectiveBundle.UniversalProperty
import MMP.AlgebraicGeometry.MMP.Contraction.CurveFactorization
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.BridgeLabels

/-!
# Terminal bridges over a stabilized tail: the comparison and the nef end

Let `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` be a stabilized tail with common low-discrepancy set
`I_∞`, let `(p_i, Θ_i)`, `p_i : Y_i ⟶ X_i`, be a crepant junction of `(X_i, B_i)` extracting
`I_∞`, and let `Θ_i'` be its decreased boundary.

*Comparison.* For birational morphisms `q : W ⟶ Y_i`, `r : W ⟶ X_{i+1}` from a smooth projective
variety with `q ≫ p_i ≫ f_i = r ≫ f_i⁺`, the divisor
`F = q^*(K_{Y_i} + Θ_i') - r^*(K_{X_{i+1}} + B_{i+1})` is effective and `r_* F = 0`. At a prime
divisor of `W` over a prime divisor of `X_{i+1}`, or over a non-extracted prime divisor of `Y_i`,
every map of the diagram is a local isomorphism and the coefficients agree, the boundaries being
strict transforms; at a prime divisor over an extracted `E_{i,s}` both coefficients are
`ord_E(K_W) + 1 - a_{i+1}(s)`, for a top form cutting out both canonical divisors. Effectivity is
then the negativity lemma for `q`: `-F` is `q`-nef, since a curve contracted by `q` maps to a
point of `Z_i` and `K_{i+1} + B_{i+1}` is `f_i⁺`-ample.

*The nef end.* Let `(V_m, Θ_m)` be the end of a finite relative threefold programme over `Z_i`
from `(Y_i, Θ_i')` with `K_{V_m} + Θ_m` nef over `Z_i`. On a smooth projective common model `W`
of the `V_k` and `X_{i+1}`, `F₁ = q_0^*(K_{V_0} + Θ_0) - q_m^*(K_{V_m} + Θ_m)` is effective (the
negativity lemma across each step) and `q_m`-exceptional, and `F₂` is the comparison divisor
above. The two-ends argument gives `q_m^*(K_{V_m} + Θ_m) = r^*(K_{X_{i+1}} + B_{i+1})`, then
`r = p̂ ∘ q_m` for a birational `p̂ : V_m ⟶ X_{i+1}` with `p̂ ≫ f_i⁺ = π_m` and
`K_{V_m} + Θ_m = p̂^*(K_{X_{i+1}} + B_{i+1})`. Finally `(p̂, Θ_m)` is a crepant junction of
`(X_{i+1}, B_{i+1})` extracting `I(X_{i+1}, B_{i+1})`: the strict transforms identify the prime
divisors of `Y_i` and `V_m`, the extracted ones carry the labels of `I(X_{i+1}, B_{i+1})`, and
log discrepancies fix the coefficients of `Θ_m`.

## Main results

* `IsDecreasedBoundary.zero_le_pullback_sub_pullback_and_transformDivisor_eq_zero`
  (in `MMP.Fourfold.StabilizedTail`): `0 ≤ F` and `r_* F = 0`.
* `MMP.Fourfold.StabilizedTail.IsDecreasedBoundary.exists_comp_eq_modelMap_and_isPullback`:
  the crepant morphism `p̂ : V_m ⟶ X_{i+1}` from the nef end.
* `MMP.Fourfold.StabilizedTail.IsDecreasedBoundary.exists_crepantJunction_of_isPullback`:
  `(V_m, p̂, Θ_m)` underlies a crepant junction of `(X_{i+1}, B_{i+1})`.

## Implementation notes

* The canonical divisors are cut out by one rational top form: `K_{i+1}` is the tail's
  `(f_i⁺)⁻¹_* (f_i)_* K_i`, and on `Y_i` the programme is run with a canonical divisor `K` with
  `(p_i)_* K = K_i`, which determines it. So the crepant identities are equalities of
  `ℚ`-divisors, not of classes.
* Compatibility with the birational map `Y_i ⇢ X_{i+1}` (resp. `V_m ⇢ X_{i+1}`) is stated as
  `q ≫ p_i ≫ f_i = r ≫ f_i⁺` (resp. `p̂ ≫ f_i⁺ = π_m`), equivalent since `f_i⁺` is birational.
* Pull-backs are `MMP.Mori.QDivisor.pullback` and `MMP.Mori.QDivisor.IsPullback`; push-forward
  along `r` is the birational transform `MMP.Mori.RationalMap.transformDivisor`.
* A crepant junction is data with its own source `Y`, so the junction at the end is given up to
  an isomorphism `e : V_m ≅ J'.Y`, as a `MMP.Fourfold.StabilizedTail.TerminalBridge` records it.
* The common model is built by iterating the common normal model of two proper birational
  morphisms to a separated base, then Chow's lemma and a strong resolution.

## References

* [OpenAI, *Projective lc fourfolds*][OAI4], terminal bridges over a stabilized tail
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori
open MMP.Fourfold.Oai4C1 (isQCartier_neg isPullback_neg not_exists_range_eq_singleton
  isContractedBy_map intersectionNumber_isPullback_eq_zero intersectionNumber_isPullback_nonneg)
open MMP.Fourfold.Oai4C1.CommonModel (isBirationalMorphism_comp
  isBirationalMorphism_of_isBirational exists_partialIso_isOver compHom_toRationalMap_of_isOver)
open MMP.Fourfold.Oai4C1.TwoEnds (intersectionNumber_pos_of_hasRelativelyAmpleMultiple
  qDivisor_isPullback_comp)
open MMP.Threefold.Resolution (map_componentGenericPoint_notMem_supp_of_isDominant')

namespace StabilizedTail

/-! ## The decreased junction lies above the next model -/

section IntersectionNumbers

section Intersection

open MMP.Flips

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`: every proper curve has a normalization, which is
birational, so of degree one. -/
private theorem isCartierIntersectionNumber_degreeOn (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    IsCartierIntersectionNumber k sX C L hL (L.degreeOn k sX C.ι C.dim_le hL) := by
  let p := C.ι ≫ sX
  have : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  have hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  have : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  have : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        have : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        have : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  have hdim := (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le
  refine ⟨_, _, hν, hdim, ?_⟩
  have : IsProper ((normalizationOverField k p ≫ C.ι) ≫ sX) := by
    rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (MMP.Fourfold.Oai4C1.Negativity.degreeOn_normalization C hν hdim _).symm

end Intersection

section Curves

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Intersection numbers are unchanged by an isomorphism of curves over `X`. -/
private theorem intersectionNumber_eq_of_iso_comp [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] {C C' : Scheme.{u}} (i : C ⟶ X) (i' : C' ⟶ X)
    [IsProper (i ≫ sX)] [IsProper (i' ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (e : C ≅ C') (he : e.hom ≫ i' = i) (D : QDivisor X)
    (hD : D.IsQCartier) :
    D.intersectionNumber k sX i hdim hD = D.intersectionNumber k sX i' hdim' hD := by
  have := QuasiCompact.compactSpace_of_compactSpace sX
  unfold QDivisor.intersectionNumber Divisor.degreeOn
  have := (QDivisor.isCartierDivisor_cartierIndex_smul hD).isCartier_toDivisor
    |>.isInvertibleModule_divisorialSheaf
  rw [MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX i i' hdim hdim' e he]

/-- Two closed subschemes cut out by equal ideal sheaves are isomorphic over `X`. -/
private theorem exists_iso_subscheme_of_eq {I J : X.IdealSheafData} (h : I = J) :
    ∃ e : I.subscheme ≅ J.subscheme, e.hom ≫ J.subschemeι = I.subschemeι := by
  subst h
  exact ⟨Iso.refl _, by simp⟩

end Curves

/-- `((-D) · C) = -(D · C)`. -/
private theorem intersectionNumber_neg (k : Type u) [Field k] {X C : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
    (i : C ⟶ X) [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) {D : QDivisor X}
    (hD : D.IsQCartier) (hD' : (-D).IsQCartier) :
    (-D).intersectionNumber k sX i hdim hD' = -(D.intersectionNumber k sX i hdim hD) := by
  have hadd := QDivisor.intersectionNumber_add' k sX i hdim D (-D) hD hD'
    (by rw [add_neg_cancel]; exact QDivisor.isQCartier_zero)
  rw [MMP.Fourfold.intersectionNumber_congr sX i hdim _ QDivisor.isQCartier_zero (add_neg_cancel D),
    MMP.Fourfold.intersectionNumber_zero sX i hdim] at hadd
  linarith

/-- **Projection onto the image curve.** Let `L' = u^*L` be the pull-back of a `ℚ`-Cartier
`ℚ`-divisor along a proper morphism `u : V ⟶ W` of normal varieties and `C ⊆ V` a proper curve
whose image `u(C)` is not a point. Then `u(C)` is a proper curve `C''` of `W` with generic point
`u(η_C)`, and `(L' · C) = d (L · C'')` with `d = [k(C) : k(C'')] > 0`. -/
private theorem exists_intersectionNumber_pullback_eq_mul {k : Type u} [Field k]
    {V W : Scheme.{u}} {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsVariety k sV] [AlgebraicGeometry.IsVariety k sW]
    [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian W] [IsNormal W]
    (u : V ⟶ W) [IsProper u] (hu : u ≫ sW = sV) {L : QDivisor W} (hL : L.IsQCartier)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') (hL' : L'.IsQCartier) (C : ProperCurve sV)
    (hpt : ¬ ∃ w : W, Set.range (C.ι ≫ u) = {w}) :
    ∃ C'' : ProperCurve sW, C''.point = u C.point ∧ ∃ d : ℚ, 0 < d ∧
      L'.intersectionNumber k sV C.ι C.dim_le hL' =
        d * L.intersectionNumber k sW C''.ι C''.dim_le hL := by
  have := C.isCurve
  set φ := C.ι ≫ u with hφ
  have : AlgebraicGeometry.IsCurve k (φ ≫ sW) := by rw [hφ, Category.assoc, hu]; infer_instance
  have : IsProper (φ ≫ sW) := by rw [hφ, Category.assoc, hu]; infer_instance
  have hcurve := isCurve_imageι_comp sW φ hpt
  have key := intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu C.ι hL h hcurve
  obtain ⟨e, he⟩ := exists_iso_subscheme_of_eq (C.ker_comp (f := u))
  have : IsProper φ := IsProper.of_comp φ sW
  have : IsProper (φ.imageι ≫ sW) := isProper_imageι_comp φ sW
  have hdim : topologicalKrullDim (curveSubschemeAt (u C.point)) = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph).symm.trans
      hcurve.topologicalKrullDim_eq_one
  have hι : curveSubschemeAtι (u C.point) = e.inv ≫ φ.imageι := by
    rw [Iso.eq_inv_comp]; exact he
  have hprop : IsProper (curveSubschemeAtι (u C.point) ≫ sW) := by
    rw [hι, Category.assoc]; infer_instance
  let C'' : ProperCurve sW := ⟨u C.point, ⟨hdim, hprop⟩⟩
  have hφs : φ.toImage ≫ φ.imageι ≫ sW = C.ι ≫ sV := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hφ, Category.assoc, hu]
  have : LocallyOfFiniteType φ.toImage := by
    have : LocallyOfFiniteType (φ.toImage ≫ φ.imageι ≫ sW) := by
      rw [hφs]; infer_instance
    exact locallyOfFiniteType_of_comp φ.toImage (φ.imageι ≫ sW)
  have hnc : ¬ ∃ y : φ.image, ∀ x : C.scheme, φ.toImage.base x = y := by
    rintro ⟨y, hy⟩
    have hφy : ∀ x, φ x = φ.imageι y := fun x => by
      calc φ x = (φ.toImage ≫ φ.imageι) x := by rw [Scheme.Hom.toImage_imageι]
        _ = φ.imageι y := by rw [Scheme.Hom.comp_apply, hy x]
    obtain ⟨x⟩ : Nonempty C.scheme := inferInstance
    exact hpt ⟨φ.imageι y, Set.eq_singleton_iff_unique_mem.mpr
      ⟨⟨x, hφy x⟩, by rintro _ ⟨x, rfl⟩; exact hφy x⟩⟩
  have hdeg : 0 < degreeOver φ.toImage :=
    degreeOver_pos_of_not_constant k (C.ι ≫ sV) (φ.imageι ≫ sW) φ.toImage hφs hnc
  refine ⟨C'', rfl, (degreeOver φ.toImage : ℚ), by exact_mod_cast hdeg, key.trans ?_⟩
  rw [intersectionNumber_eq_of_iso_comp sW φ.imageι C''.ι _ C''.dim_le e he _ hL]

/-- **Projection of a contracted curve.** With `L' = u^*L` as in
`exists_intersectionNumber_pullback_eq_mul` and `C ⊆ V` a proper curve contracted by `u ≫ f`,
either `(L' · C) = 0` (when `u(C)` is a point), or `(L' · C) = d (L · u(C))` with `d ≥ 0`, where
`u(C)` is a proper curve of `W` contracted by `f`. -/
private theorem intersectionNumber_pullback_eq_zero_or {k : Type u} [Field k]
    {V W Y : Scheme.{u}} {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsVariety k sV] [AlgebraicGeometry.IsVariety k sW]
    [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian W] [IsNormal W]
    (u : V ⟶ W) [IsProper u] (hu : u ≫ sW = sV) (f : W ⟶ Y) {L : QDivisor W}
    (hL : L.IsQCartier)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') (hL' : L'.IsQCartier) (C : ProperCurve sV)
    (hC : C.IsContractedBy (u ≫ f)) :
    L'.intersectionNumber k sV C.ι C.dim_le hL' = 0 ∨
      ∃ d : ℚ, 0 ≤ d ∧ ∃ C'' : ProperCurve sW, C''.IsContractedBy f ∧
        L'.intersectionNumber k sV C.ι C.dim_le hL' =
          d * L.intersectionNumber k sW C''.ι C''.dim_le hL := by
  have := C.isCurve
  by_cases hpt : ∃ w : W, Set.range (C.ι ≫ u) = {w}
  · exact .inl (intersectionNumber_pullback_eq_zero k sV sW u hu C.ι hL h hpt)
  obtain ⟨C'', hC''u, d, hd, heq⟩ :=
    exists_intersectionNumber_pullback_eq_mul u hu hL h hL' C hpt
  refine .inr ⟨d, hd.le, C'', fun x hx => ?_, heq⟩
  have hsub : closure ({u C.point} : Set W) ⊆ u '' closure ({C.point} : Set V) :=
    (u.isClosedMap _ isClosed_closure).closure_subset_iff.mpr (by
      rintro _ rfl; exact ⟨C.point, subset_closure rfl, rfl⟩)
  rw [hC''u] at hx ⊢
  obtain ⟨z, hz, rfl⟩ := hsub hx
  simpa only [Scheme.Hom.comp_apply] using hC z hz

/-- An exceptional prime divisor of a morphism maps its generic point to a point of coheight at
least two. -/
private theorem two_le_coheight_of_isExceptional {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : Y ⟶ X} (E : MMP.Mori.PrimeDivisor Y)
    (hE : RationalMap.IsExceptional (X := Y) f.toRationalMap E) :
    2 ≤ Order.coheight (f E.genericPoint) := by
  set η := E.genericPoint
  have hdef : RationalMap.DefinedAt (X := Y) f.toRationalMap η := by
    rw [RationalMap.DefinedAt, RationalMap.dom_toRationalMap_hom]
    trivial
  have h2 := (RationalMap.isExceptional_iff.mp hE) hdef
  have hsub : (TopologicalSpace.IrreducibleCloseds.closureSingleton (f η) : Set X) ⊆
      (RationalMap.transform (X := Y) f.toRationalMap E.idealSheaf.support : Set X) := by
    rw [TopologicalSpace.IrreducibleCloseds.coe_closureSingleton]
    refine (TopologicalSpace.Closeds.isClosed _).closure_subset_iff.mpr ?_
    rintro _ rfl
    refine RationalMap.image_subset_transform f.toPartialMap rfl _ ?_
    rw [MMP.Positivity.image_toPartialMap_hom]
    refine ⟨η, ?_, rfl⟩
    change η ∈ E.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hle := le_closedsCodimension_iff.mp h2 _ hsub
  have hcodim : codimension (TopologicalSpace.IrreducibleCloseds.closureSingleton (f η)) =
      Order.coheight (f η) := by
    have h : TopologicalSpace.IrreducibleCloseds.closureSingleton (f η) =
        irreducibleSetEquivPoints.symm (f η) :=
      TopologicalSpace.IrreducibleCloseds.ext (by
        rw [TopologicalSpace.IrreducibleCloseds.coe_closureSingleton,
          coe_irreducibleEquivPoints_symm_apply])
    rw [codimension_eq_coheight, h]
    exact Order.coheight_orderIso irreducibleSetEquivPoints.symm (f η)
  rwa [hcodim] at hle

end IntersectionNumbers

section Negativity

/-- A prime divisor exceptional over `X` is exceptional in the sense of the dimension of its
centre: `dim c_X(E) + 2 ≤ dim X`. -/
private theorem isExceptionalPrimeDivisor_of_isExceptional {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    {f : Y ⟶ X} (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) [hp : IsProper f]
    (E : MMP.Mori.PrimeDivisor Y)
    (hE : MMP.Mori.RationalMap.IsExceptional (X := Y) f.toRationalMap E) :
    MMP.Flips.IsExceptionalPrimeDivisor sX f E := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  refine ⟨hY, hf, hp, ?_⟩
  have h2 := two_le_coheight_of_isExceptional E hE
  unfold MMP.Flips.ProperDivisorOver.IsExceptional
  rw [MMP.Flips.ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint]
  rw [← MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (f E.genericPoint)]
  gcongr
  have h2' : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (Order.coheight (f E.genericPoint) : WithBot ℕ∞) :=
    WithBot.coe_le_coe.mpr h2
  exact le_of_eq_of_le (by norm_cast) h2'

/-- **The negativity lemma for `ℚ`-Cartier divisors.** Let `f : Y ⟶ X` be a proper birational
morphism of normal varieties and `B` a `ℚ`-Cartier divisor on `Y` with `(B · C) ≤ 0` on every
curve contracted by `f`, whose coefficients along the prime divisors not exceptional over `X` are
nonnegative. Then `B` is effective. -/
private theorem nonneg_of_intersectionNumber_nonpos {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] (hX : IsNormalVariety k sX)
    (hY : IsNormalVariety k sY) (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f]
    (hfb : IsBirationalMorphism f) {B : QDivisor Y} (hB : B.IsQCartier)
    (hnef : ∀ C : ProperCurve sY, C.IsContractedBy f →
      B.intersectionNumber k sY C.ι C.dim_le hB ≤ 0)
    (hBG : ∀ P : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.IsExceptionalPrimeDivisor sX f P →
      0 ≤ B.coeff P) :
    0 ≤ B := by
  obtain ⟨E, hEB, hEc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hB
  have hm : 0 < B.cartierIndex hB := QDivisor.cartierIndex_pos hB
  set m := B.cartierIndex hB with hm_def
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  set BR := QDivisor.toRDivisor B with hBR
  have hBRE : BR = ((1 : ℝ) / m) • Divisor.toRDivisor E := by
    ext P
    have h1 := congrArg (fun D : QDivisor Y => D.coeff P) hEB
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast] at h1
    change (QDivisor.toRDivisor B).coeff P = (((1 : ℝ) / m) • Divisor.toRDivisor E).coeff P
    rw [DivisorWithCoeffs.coeff_smul, QDivisor.coeff_toRDivisor, Divisor.coeff_toRDivisor,
      smul_eq_mul]
    have h2 : ((E.coeff P : ℚ) : ℝ) = ((m * B.coeff P : ℚ) : ℝ) := by rw [h1]
    push_cast at h2
    rw [h2]
    field_simp
  have hL0 : MMP.Flips.IsCartierCombination (0 : RDivisor X) :=
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  have hpb0 : MMP.Flips.IsRCartierPullback f (0 : RDivisor X) 0 :=
    ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
  have hBRc : MMP.Flips.IsCartierCombination BR :=
    ⟨1, fun _ => 1 / (m : ℝ), fun _ => E, fun _ => hEc, by
      rw [Fin.sum_univ_one, ← MMP.Flips.toRDivisor_eq_mapCoeffs]
      exact hBRE⟩
  have hMc : MMP.Flips.IsCartierCombination (-BR) :=
    ⟨1, fun _ => -(1 / (m : ℝ)), fun _ => E, fun _ => hEc, by
      rw [Fin.sum_univ_one, ← MMP.Flips.toRDivisor_eq_mapCoeffs, hBRE, neg_smul]⟩
  have hpres : -BR = ∑ j : Fin 1, (fun _ => -(1 / (m : ℝ))) j •
      Divisor.toRDivisor ((fun _ => E) j) := by
    rw [Fin.sum_univ_one, hBRE, neg_smul]
  have hMnef : MMP.Flips.IsRelativelyNef k sY f (-BR) := by
    refine ⟨1, fun _ => -(1 / (m : ℝ)), fun _ => E, fun _ => hEc, hpres, fun C hC x hx => ?_⟩
    have hx₀ : MMP.Flips.IsRIntersectionNumber k sY (-BR) (fun _ => -(1 / (m : ℝ)))
        (fun _ => E) C (∑ j : Fin 1, (fun _ => -(1 / (m : ℝ))) j *
          ((E.degreeOn k sY C.ι C.dim_le hEc : ℤ) : ℝ)) :=
      ⟨fun _ => hEc, fun _ => E.degreeOn k sY C.ι C.dim_le hEc, hpres,
        fun _ => isCartierIntersectionNumber_degreeOn k sY C E hEc, rfl⟩
    rw [(MMP.Flips.IsRIntersectionNumber.eq_and_linear k sY C).1 _ _ _ _ _ _ _ hx hx₀,
      Fin.sum_univ_one]
    have hI := hnef C hC
    rw [QDivisor.intersectionNumber_eq_of_smul k sY C.ι C.dim_le B hB hm E hEc hEB] at hI
    have hmq : (0 : ℚ) < m := by exact_mod_cast hm
    have hdeg : (E.degreeOn k sY C.ι C.dim_le hEc : ℚ) ≤ 0 := by
      have := mul_nonpos_of_nonneg_of_nonpos hmq.le hI
      rwa [mul_div_cancel₀ _ hmq.ne'] at this
    have hdeg' : ((E.degreeOn k sY C.ι C.dim_le hEc : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hdeg
    have hmr : (0 : ℝ) < m := by exact_mod_cast hm
    have : 0 ≤ -(1 / (m : ℝ)) * ((E.degreeOn k sY C.ι C.dim_le hEc : ℤ) : ℝ) := by
      rw [neg_mul]
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) hdeg')
    exact this
  have hBG' : ∀ P : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.IsExceptionalPrimeDivisor sX f P →
      0 ≤ BR.coeff P := fun P hP => by
    rw [hBR, QDivisor.coeff_toRDivisor]
    exact_mod_cast hBG P hP
  have hnum : MMP.Flips.IsNumericallyEquivalentOver k sY f (0 : RDivisor Y) (-BR + BR) := by
    refine ⟨⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩, by
      rw [neg_add_cancel]; exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
      fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
    rw [neg_add_cancel] at h₂
    exact (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sY C).1 _ _ _ _ _ _ _ h₁ h₂
  have heff := MMP.Flips.isEffective_of_isNumericallyEquivalentOver_pullback k sX sY hX hY f hf
    hfb hL0 hpb0 hMc hMnef hBRc hBG' hnum
  refine Finsupp.le_def.mpr fun P => ?_
  have hP := heff P
  rw [hBR, QDivisor.coeff_toRDivisor] at hP
  change (0 : ℚ) ≤ B.coeff P
  exact_mod_cast hP

end Negativity

/-! ### Inverse transforms along a junction -/

section Junction

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
  {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}

/-- No prime divisor of `X` has an exceptional prime divisor `E_s` of a junction as its inverse
transform: `η_{E_s}` maps to a point of codimension `≥ 2`. -/
private theorem inverseTransformPrimeDivisor_ne_E (J : CrepantJunction sX B I) (s : I)
    (P : MMP.Mori.PrimeDivisor X) : inverseTransformPrimeDivisor J.p P ≠ some (J.E s) := by
  intro hP
  have hX : IsSeparated (X ↘ ⊤_ Scheme) := by
    have := J.isKltPair.1.isPair.1.1
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
    infer_instance
  have hη := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
    hP).1
  have hexc := (J.isExceptional_iff (J.E s)).mpr ⟨s, rfl⟩
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight] at hexc
  have h2 := hexc (J.p (J.E s).genericPoint)
    (subset_closure ⟨_, (by
      change _ ∈ (J.E s).support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl), rfl⟩)
  rw [hη, P.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

end Junction

/-! ### Strict transforms across the step -/

section Coefficients

variable {T : StabilizedTail} {i : ℕ}
  {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
  {J : CrepantJunction (T.sX i) (T.B i) I}

/-- The coefficient of the decreased boundary `Θ'` at the strict transform `P_Y` of a prime
divisor `P₀` of `X_i` is the coefficient of `B_i` at `P₀`. -/
private theorem decreasedBoundary_apply_of_map_genericPoint {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ') {PY : MMP.Mori.PrimeDivisor J.Y}
    {P₀ : MMP.Mori.PrimeDivisor (T.X i)} (hpPY : J.p PY.genericPoint = P₀.genericPoint) :
    Θ' PY = T.B i P₀ := by
  classical
  have : IsProper J.p := isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism
  have hne : ∀ s, J.E s ≠ PY := by
    intro s hs
    have hX : IsSeparated (T.X i ↘ ⊤_ Scheme) :=
      isSeparated_toTerminal_of_isNormalVariety (T.isThreefoldStepDiagram i).isNormalVariety_minus
    have hexc := (J.isExceptional_iff PY).mpr ⟨s, hs⟩
    rw [MMP.Positivity.isExceptional_toRationalMap_iff,
      MMP.Flips.le_closedsCodimension_iff_le_coheight] at hexc
    have h2 := hexc (J.p PY.genericPoint)
      (subset_closure ⟨_, (by
        change _ ∈ PY.support
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl), rfl⟩)
    rw [hpPY, P₀.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  have hV := MMP.Fourfold.Oai4C1.genericPoint_mem_biregularLocus J.p J.isBirationalMorphism P₀
  have hinv : inverseTransformPrimeDivisor J.p P₀ = some PY :=
    MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hpPY
      (hpPY ▸ hV)
  obtain ⟨a, -, rfl⟩ := hΘ'
  rw [Finsupp.add_apply, Finsupp.finsetSum_apply, Finset.sum_eq_zero fun s _ =>
    Finsupp.single_eq_of_ne (hne s).symm, add_zero]
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hinv (fun _ hD' =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hD').1.symm.trans hpPY) _

/-- The coefficient of the decreased boundary `Θ' = p⁻¹_* B_i + ∑ (1 - a_s) E_s` at `E_s` is
`1 - a_s`. -/
private theorem decreasedBoundary_apply_E {a : I → ℚ} {Θ' : QDivisor J.Y}
    (hΘ' : Θ' = inverseTransformDivisor J.p (T.B i) + ∑ s : I, Finsupp.single (J.E s) (1 - a s))
    (s : I) : Θ' (J.E s) = 1 - a s := by
  classical
  have h0 : (inverseTransformDivisor J.p (T.B i)).coeff (J.E s) = 0 :=
    MMP.Fourfold.Oai4C1.mapPrimeDivisors_apply_eq_zero (inverseTransformPrimeDivisor_ne_E J s) _
  rw [hΘ', Finsupp.add_apply, Finsupp.finsetSum_apply]
  change (inverseTransformDivisor J.p (T.B i)).coeff (J.E s) + _ = _
  rw [h0, zero_add, Finset.sum_eq_single s (fun t _ hts => Finsupp.single_eq_of_ne
      (J.injective.ne hts.symm)) (by simp)]
  simp

end Coefficients

/-! ### Prime divisors of a common model -/

section CommonModel

variable {T : StabilizedTail} {i : ℕ}
  {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
  {J : CrepantJunction (T.sX i) (T.B i) I} {W : Scheme.{0}} [IsIntegral W]
  [IsLocallyNoetherian W] [IsNormal W] {q : W ⟶ J.Y} {r : W ⟶ T.X (i + 1)}

omit [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] in
/-- The compatibility `q ≫ p_i ≫ f_i = r ≫ f_i⁺`, pointwise. -/
private theorem comp_apply_eq (hcomp : q ≫ J.p ≫ T.f i = r ≫ T.fp i) (x : W) :
    T.f i (J.p (q x)) = T.fp i (r x) := by
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun g : W ⟶ T.Z i => g x) hcomp

omit [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] in
/-- **Prime divisors over `X_{i+1}`.** If `r(η_E) = η_{P₁}` for a prime divisor `P₁` of
`X_{i+1}`, then `q(η_E)` is the generic point of the strict transform `P_Y` of a prime divisor
`P₀` of `X_i`, and `P₁` is the strict transform of `P₀` across the step. -/
private theorem exists_of_map_genericPoint_eq_right (hcomp : q ≫ J.p ≫ T.f i = r ≫ T.fp i)
    (E : MMP.Mori.PrimeDivisor W) {P₁ : MMP.Mori.PrimeDivisor (T.X (i + 1))}
    (hrE : r E.genericPoint = P₁.genericPoint) :
    ∃ (PY : MMP.Mori.PrimeDivisor J.Y) (P₀ : MMP.Mori.PrimeDivisor (T.X i)),
      q E.genericPoint = PY.genericPoint ∧ J.p PY.genericPoint = P₀.genericPoint ∧
        ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R (T.X i)),
          flipTransform (T.f i) (T.fp i) D P₁ = D P₀ := by
  have hst := T.isThreefoldStepDiagram i
  have : IsProper (T.f i) := isProper_of_isProjectiveMorphism _ hst.isProjectiveMorphism_minus
  have : IsProper J.p := isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism
  have hx : T.f i (J.p (q E.genericPoint)) = T.fp i P₁.genericPoint := by
    rw [comp_apply_eq hcomp, hrE]
  obtain ⟨P₀, hP₀, hfl⟩ := exists_eq_genericPoint_flipTransform_apply
    hst.isBirationalMorphism_minus hst.isSmallMorphism_plus P₁ _ hx
  have hY : IsNormalVariety ℂ (J.p ≫ T.sX i) := J.isQFactorial.1
  obtain ⟨PY, hPY, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0}
    hst.isNormalVariety_minus hY J.isBirationalMorphism P₀
  have := P₀.isDiscreteValuationRing_localRing
  have := J.isBirationalMorphism.isDominant
  exact ⟨PY, P₀, eq_of_map_eq_of_valuationRing J.isBirationalMorphism.functionFieldMap_bijective
    hP₀ hPY, hPY, hfl⟩

omit [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] in
/-- **Prime divisors over `Y_i` that are not extracted.** If `q(η_E) = η_{P_Y}` for a prime
divisor `P_Y` of `Y_i` other than the `E_s`, then `P_Y` is the strict transform of a prime
divisor `P₀` of `X_i`, and `r(η_E)` is the generic point of the strict transform `P₁` of `P₀`
across the step. -/
private theorem exists_of_map_genericPoint_eq_left (hcomp : q ≫ J.p ≫ T.f i = r ≫ T.fp i)
    (E : MMP.Mori.PrimeDivisor W) {PY : MMP.Mori.PrimeDivisor J.Y}
    (hqE : q E.genericPoint = PY.genericPoint) (hPY : PY ∉ Set.range J.E) :
    ∃ (P₀ : MMP.Mori.PrimeDivisor (T.X i)) (P₁ : MMP.Mori.PrimeDivisor (T.X (i + 1))),
      J.p PY.genericPoint = P₀.genericPoint ∧ r E.genericPoint = P₁.genericPoint ∧
        ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R (T.X i)),
          flipTransform (T.f i) (T.fp i) D P₁ = D P₀ := by
  have hst := T.isThreefoldStepDiagram i
  have hX := hst.isNormalVariety_minus
  have hY : IsNormalVariety ℂ (J.p ≫ T.sX i) := J.isQFactorial.1
  have : IsProper (T.f i) := isProper_of_isProjectiveMorphism _ hst.isProjectiveMorphism_minus
  have : IsProper (T.fp i) := hst.isSmallMorphism_plus.isProper
  have hZ := hst.isNormalVariety_target
  have : IsIntegral (T.Z i) := hZ.1.toIsIntegral
  have : IsNormal (T.Z i) := hZ.2
  have : LocallyOfFiniteType (T.sZ i) := hZ.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian (T.Z i) := LocallyOfFiniteType.isLocallyNoetherian (T.sZ i)
  have hnex :
      ¬ (⟨J.Y, J.p, hY, J.isBirationalMorphism, PY⟩ : DivisorOver ℂ (T.sX i)).IsExceptional :=
    fun hex => hPY ((J.isExceptional_iff PY).mp hex)
  obtain ⟨P₀, hv⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX _
    hnex
  have hpPY : J.p PY.genericPoint = P₀.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
  have hfpb := hst.isSmallMorphism_plus.isBirationalMorphism
  have := hfpb.isDominant
  have := hst.isBirationalMorphism_minus.isDominant
  obtain ⟨P₁, Q, -, hP₁Q, hP₀Q⟩ := exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hZ
    hfpb (T.isSmallMorphism i) P₀
  have hfpP₁ := map_genericPoint_eq_of_image_eq P₁ Q hP₁Q
  have hfP₀ := map_genericPoint_eq_of_image_eq P₀ Q hP₀Q
  have := Q.isDiscreteValuationRing_localRing
  have hrE : r E.genericPoint = P₁.genericPoint :=
    eq_of_map_eq_of_valuationRing hfpb.functionFieldMap_bijective
      (by rw [← comp_apply_eq hcomp, hqE, hpPY, hfP₀]) hfpP₁
  obtain ⟨Pm, hPm, hfl⟩ := exists_eq_genericPoint_flipTransform_apply
    hst.isBirationalMorphism_minus hst.isSmallMorphism_plus P₁ P₀.genericPoint
    (hfP₀.trans hfpP₁.symm)
  obtain rfl := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hPm
  exact ⟨P₀, P₁, hpPY, hrE, hfl⟩

/-- The canonical divisor `K` of `Y_i` with `(p_i)_* K = K_i` has, at the strict transform `P_Y`
of `P₀`, the coefficient of `K_{i+1}` at the strict transform `P₁` of `P₀` across the step. -/
private theorem coeff_canonical_eq (K : Divisor J.Y)
    (hpK : RationalMap.transformDivisor (X := J.Y) J.p.toRationalMap K = T.K i)
    {PY : MMP.Mori.PrimeDivisor J.Y} {P₀ : MMP.Mori.PrimeDivisor (T.X i)}
    {P₁ : MMP.Mori.PrimeDivisor (T.X (i + 1))} (hpY : J.p PY.genericPoint = P₀.genericPoint)
    (hfl : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R (T.X i)),
      flipTransform (T.f i) (T.fp i) D P₁ = D P₀) :
    K PY = T.K (i + 1) P₁ := by
  have hst := T.isThreefoldStepDiagram i
  have hY : IsNormalVariety ℂ (J.p ≫ T.sX i) := J.isQFactorial.1
  have : IsProper J.p := isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism
  obtain ⟨E', hE', -, htr⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply
    hst.isNormalVariety_minus hY J.isBirationalMorphism P₀
  have := P₀.isDiscreteValuationRing_localRing
  have := J.isBirationalMorphism.isDominant
  obtain rfl := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_map_eq_of_valuationRing J.isBirationalMorphism.functionFieldMap_bijective hE' hpY)
  rw [T.K_eq i, hfl, ← hpK, htr]

/-- **The comparison divisor vanishes over divisors of the base.** At a prime divisor `E` of `W`
over the strict transforms `P_Y ⊆ Y_i`, `P₁ ⊆ X_{i+1}` of a prime divisor `P₀` of `X_i`, the
pull-backs `q^*(K + Θ')` and `r^*(K_{i+1} + B_{i+1})` have the same coefficient. -/
private theorem pullback_apply_eq [CompactSpace W] {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ') (K : Divisor J.Y)
    (hpK : RationalMap.transformDivisor (X := J.Y) J.p.toRationalMap K = T.K i)
    (hq : IsBirationalMorphism q) (hr : IsBirationalMorphism r)
    (hD : (Divisor.toQDivisor K + Θ').IsQCartier)
    (hD' : (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).IsQCartier)
    (h : ∀ Z : irreducibleComponents W,
      q (componentGenericPoint W Z) ∉ (Divisor.toQDivisor K + Θ').supp)
    (h' : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).supp)
    (E : MMP.Mori.PrimeDivisor W) {PY : MMP.Mori.PrimeDivisor J.Y}
    {P₀ : MMP.Mori.PrimeDivisor (T.X i)} {P₁ : MMP.Mori.PrimeDivisor (T.X (i + 1))}
    (hqE : q E.genericPoint = PY.genericPoint) (hpY : J.p PY.genericPoint = P₀.genericPoint)
    (hrE : r E.genericPoint = P₁.genericPoint)
    (hfl : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R (T.X i)),
      flipTransform (T.f i) (T.fp i) D P₁ = D P₀) :
    (Divisor.toQDivisor K + Θ').pullback hD h E =
      (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).pullback hD' h' E := by
  have := isIso_stalkMap_of_map_eq_genericPoint hq hqE
  have := isIso_stalkMap_of_map_eq_genericPoint hr hrE
  rw [coeff_eq_of_isPullback_qDivisor E PY hqE hD (QDivisor.isPullback_pullback hD h),
    coeff_eq_of_isPullback_qDivisor E P₁ hrE hD' (QDivisor.isPullback_pullback hD' h')]
  change ((K PY : ℤ) : ℚ) + Θ' PY = ((T.K (i + 1) P₁ : ℤ) : ℚ) + T.B (i + 1) P₁
  rw [coeff_canonical_eq K hpK hpY hfl, decreasedBoundary_apply_of_map_genericPoint hΘ' hpY,
    T.B_eq i, hfl]

end CommonModel

/-! ### Rational top forms and valuations along the common model -/

section Forms

/-- Along a morphism `f` inducing an isomorphism of function fields, every rational pluri-form
is a pull-back: `τ = f^*σ`, with `σ ≠ 0` when `τ ≠ 0`. -/
private theorem exists_pullbackRationalPluriForms_eq {k : Type} [Field k] [PerfectField k]
    {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = d) {m : ℤ}
    (τ : RationalPluriForms (f ≫ sY) d m) :
    ∃ σ : RationalPluriForms sY d m, pullbackRationalPluriForms sY f σ = τ ∧
      (τ ≠ 0 → σ ≠ 0) := by
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (f ≫ sY)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sY f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sY f hf hd
  set bY := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m with hbY
  set bX := ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m with hbX
  obtain ⟨c, hc⟩ := hf.2 (bX.repr τ ())
  have hpull : pullbackRationalPluriForms sY f (c • bY ()) = τ := by
    change pullbackForms m (c • bY ()) = τ
    rw [pullbackForms_eq hω m]
    apply bX.ext_elem
    intro i
    obtain rfl : i = () := rfl
    rw [repr_pullbackFormsAlong hω m]
    simp only [bY, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
    exact hc
  refine ⟨c • bY (), hpull, fun hτ hσ => hτ ?_⟩
  rw [← hpull, hσ]
  change pullbackForms m 0 = 0
  rw [pullbackForms_eq hω m]
  simp [pullbackFormsAlong]

/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {p : U ⟶ X} [IsDominant p] (hp : IsBirationalMorphism p) {n : ℕ}
    (hn : topologicalKrullDim X = n) {m : ℤ} {τ : RationalPluriForms sX n m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX p τ ≠ 0 := by
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := hp.functionFieldMap_bijective
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX p hbij hd
  let := functionFieldAlgebra (p ≫ sX)
  let := functionFieldMapAlgebra p
  have := isScalarTower_functionFieldMap sX p
  have hpull : pullbackRationalPluriForms sX p τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField U.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- A valuation is determined by its restriction along a surjective ring map. -/
private theorem eq_of_comap_eq_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    {φ : R →+* S} (hφ : Function.Surjective φ) {v w : Valuation S (WithZero (Multiplicative ℤ))}
    (h : v.comap φ = w.comap φ) : v = w := by
  ext x
  obtain ⟨y, rfl⟩ := hφ x
  exact congrArg (fun u : Valuation R (WithZero (Multiplicative ℤ)) => u y) h

/-- If a birational morphism `f : X ⟶ Y` onto a normal scheme maps the generic point of a prime
divisor `E` to that of a prime divisor `Q`, then `ord_E`, read in `k(Y)`, is `ord_Q`. -/
private theorem valuationOver_eq_of_map_genericPoint {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : X ⟶ Y} (hf : IsBirationalMorphism f) (E : MMP.Mori.PrimeDivisor X)
    (Q : MMP.Mori.PrimeDivisor Y) (heq : f E.genericPoint = Q.genericPoint) :
    have := hf.isDominant
    E.valuationOver f = Q.divisorialValuation := by
  have := hf.isDominant
  have := Q.isDiscreteValuationRing_localRing
  have : ValuationRing (Y.presheaf.stalk (f E.genericPoint)) := by rw [heq]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective
    E.genericPoint
  refine Valuation.ext fun t => ?_
  rw [PrimeDivisor.valuationOver_apply]
  by_cases ht : t = 0
  · rw [ht, map_zero, map_zero, map_zero]
  rw [PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso f E Q heq t]

end Forms

section Extracted

variable {T : StabilizedTail} {i : ℕ}
  {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
  {J : CrepantJunction (T.sX i) (T.B i) I} {W : Scheme.{0}} [IsIntegral W]
  [IsLocallyNoetherian W] [IsNormal W] {q : W ⟶ J.Y} {r : W ⟶ T.X (i + 1)}

/-- **A top form cutting out both canonical divisors.** If `K` is a canonical divisor of `Y_i`
with `(p_i)_* K = K_i`, there is a nonzero rational top form `ω'` on `X_{i+1}` with
`div(ω') = K_{i+1}` whose pull-back to `W` agrees with that of the form cutting out `K`: at every
prime divisor `E` of `W` over a prime divisor `P_Y` of `Y_i`, `ord_E(r^*ω') = coeff_{P_Y} K`. -/
private theorem exists_ordForm_pullback_eq [CompactSpace W] (K : Divisor J.Y)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor (J.p ≫ T.sX i) n)
    (hpK : RationalMap.transformDivisor (X := J.Y) J.p.toRationalMap K = T.K i)
    {sW : W ⟶ Spec (.of ℂ)} (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hq : IsBirationalMorphism q) (hr : IsBirationalMorphism r)
    (hqs : q ≫ J.p ≫ T.sX i = sW) (hrs : r ≫ T.sX (i + 1) = sW)
    (hcomp : q ≫ J.p ≫ T.f i = r ≫ T.fp i) :
    have := hr.isDominant
    ∃ ω' : RationalPluriForms (T.sX (i + 1)) 3 1, ω' ≠ 0 ∧
      (∀ Γ : MMP.Mori.PrimeDivisor (T.X (i + 1)), (T.K (i + 1)).coeff Γ = Γ.ordForm ω') ∧
      ∀ (E : MMP.Mori.PrimeDivisor W) (PY : MMP.Mori.PrimeDivisor J.Y),
        q E.genericPoint = PY.genericPoint →
          E.ordForm (pullbackRationalPluriForms (T.sX (i + 1)) r ω') = K PY := by
  have hst := T.isThreefoldStepDiagram i
  have hX := hst.isNormalVariety_minus
  have hX' := hst.isNormalVariety_plus
  have hY : IsNormalVariety ℂ (J.p ≫ T.sX i) := J.isQFactorial.1
  have : LocallyOfFiniteType (T.sX i) := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (J.p ≫ T.sX i) := hY.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (T.sX (i + 1)) := hX'.1.toLocallyOfFiniteType
  have : IsProper J.p := isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism
  have := J.isBirationalMorphism.isDominant
  have := hq.isDominant
  have := hr.isDominant
  obtain ⟨n, hKn⟩ := hK
  obtain ⟨n₀, hK₀⟩ := hst.isCanonicalDivisor
  obtain rfl : n = 3 := by
    have := hKn.topologicalKrullDim_eq.symm.trans J.dim_eq
    exact_mod_cast this
  obtain rfl : n₀ = 3 := by
    have := hK₀.topologicalKrullDim_eq.symm.trans hst.dim_minus
    exact_mod_cast this
  obtain ⟨ω, hω0, -, hωK⟩ := MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hX hY
    J.isBirationalMorphism hK₀ hKn hpK
  set ωY := pullbackRationalPluriForms (T.sX i) J.p ω with hωY
  set ωW := pullbackRationalPluriForms (J.p ≫ T.sX i) q ωY with hωW
  have hωY0 : ωY ≠ 0 := pullbackRationalPluriForms_ne_zero hX J.isBirationalMorphism
    hst.dim_minus hω0
  have hωW0 : ωW ≠ 0 := pullbackRationalPluriForms_ne_zero hY hq J.dim_eq hωY0
  have hd' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := T.sX (i + 1)) hst.dim_plus
  have hdY := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := J.p ≫ T.sX i) J.dim_eq
  have key : ∀ (s : W ⟶ Spec (.of ℂ)) (_ : s = r ≫ T.sX (i + 1))
      (τ : RationalPluriForms s 3 1), τ ≠ 0 → ∃ σ : RationalPluriForms (T.sX (i + 1)) 3 1,
        σ ≠ 0 ∧ ∀ E : MMP.Mori.PrimeDivisor W,
          E.ordForm (pullbackRationalPluriForms (T.sX (i + 1)) r σ) = E.ordForm τ := by
    rintro s rfl τ hτ
    obtain ⟨σ, hσ, hσ0⟩ := exists_pullbackRationalPluriForms_eq r hr.functionFieldMap_bijective
      hd' τ
    exact ⟨σ, hσ0 hτ, fun E => by rw [hσ]⟩
  obtain ⟨ω', hω'0, hω'⟩ := key _ (hqs.trans hrs.symm) ωW hωW0
  have hord : ∀ (E : MMP.Mori.PrimeDivisor W) (PY : MMP.Mori.PrimeDivisor J.Y),
      q E.genericPoint = PY.genericPoint →
        E.ordForm (pullbackRationalPluriForms (T.sX (i + 1)) r ω') = K PY := by
    intro E PY hqE
    have := isIso_stalkMap_of_map_eq_genericPoint hq hqE
    rw [hω', hωW, MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso q
      hq.functionFieldMap_bijective hdY E PY hqE ωY, ← hωK]
    rfl
  refine ⟨ω', hω'0, fun Γ => ?_, hord⟩
  have hWr : IsNormalVariety ℂ (r ≫ T.sX (i + 1)) := by
    rw [hrs]; exact ⟨hW.toIsVariety, inferInstance⟩
  have : IsProper sW := isProper_of_isProjectiveMorphism _ hW.isProjective
  have : IsSeparated (T.sX (i + 1)) := hX'.1.toIsSeparated
  have : IsProper r := by
    have : IsProper (r ≫ T.sX (i + 1)) := hrs ▸ inferInstance
    exact IsProper.of_comp r (T.sX (i + 1))
  obtain ⟨E, hrE, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX' hWr hr Γ
  obtain ⟨PY, P₀, hqE, hpY, hfl⟩ := exists_of_map_genericPoint_eq_right hcomp E hrE
  rw [← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso r hr.functionFieldMap_bijective
    hd' E Γ hrE ω', hord E PY hqE, coeff_canonical_eq K hpK hpY hfl]
  rfl

/-- **The valuation of a prime over an extracted divisor.** If `q(η_E) = η_{E_s}`, then `ord_E`,
read in `k(X_{i+1})` through `r`, is the transport `s'` of `s` across the step. -/
private theorem valuation_eq_of_isTransportedValuation (hq : IsBirationalMorphism q)
    (hr : IsBirationalMorphism r) (hcomp : q ≫ J.p ≫ T.f i = r ≫ T.fp i)
    (hWr : IsNormalVariety ℂ (r ≫ T.sX (i + 1))) (E : MMP.Mori.PrimeDivisor W) (s : I)
    (hqE : q E.genericPoint = (J.E s).genericPoint)
    {s' : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))}
    (hss' : T.IsTransportedValuation i s s') :
    (⟨W, r, hWr, hr, E⟩ : DivisorOver ℂ (T.sX (i + 1))).valuation = s' := by
  have hst := T.isThreefoldStepDiagram i
  have : IsIntegral (T.Z i) := hst.isNormalVariety_target.1.toIsIntegral
  have hfpb := hst.isSmallMorphism_plus.isBirationalMorphism
  have := hfpb.isDominant
  have := hst.isBirationalMorphism_minus.isDominant
  have := J.isBirationalMorphism.isDominant
  have := hq.isDominant
  have := hr.isDominant
  have : IsDominant (J.p ≫ T.f i) := inferInstance
  have : IsDominant (q ≫ J.p ≫ T.f i) := inferInstance
  have hs := J.valuation_eq s
  have hss : (s : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))) =
      (J.E s).valuationOver J.p := hs.symm
  have hvE := valuationOver_eq_of_map_genericPoint hq E (J.E s) hqE
  refine eq_of_comap_eq_of_surjective hfpb.functionFieldMap_bijective.2 ?_
  have hss'' : s'.comap (functionFieldMap (T.fp i)) =
      (s : Valuation (T.X i).functionField _).comap (functionFieldMap (T.f i)) := hss'
  rw [hss'', hss]
  ext t
  change E.divisorialValuation (functionFieldMap r (functionFieldMap (T.fp i) t)) =
    (J.E s).divisorialValuation (functionFieldMap J.p (functionFieldMap (T.f i) t))
  rw [MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply r (T.fp i) hcomp.symm,
    MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply J.p (T.f i) rfl,
    ← MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply q (J.p ≫ T.f i) rfl]
  change E.valuationOver q _ = _
  rw [hvE]

end Extracted

/-- **The comparison divisor vanishes at the extracted divisors.** At a prime divisor `E` of `W`
over the extracted divisor `E_s` of `Y_i`, the pull-backs `q^*(K + Θ')` and
`r^*(K_{i+1} + B_{i+1})` have the same coefficient: both are `ord_E(K_W) + 1 - a_{i+1}(s)`, for
the canonical divisor `K_W` cut out by the top form defining `K` and `K_{i+1}`. -/
private theorem pullback_apply_eq_of_map_genericPoint_eq_E {T : StabilizedTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {J : CrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ')
    (K : Divisor J.Y) (hK : ∃ n : ℕ, K.IsCanonicalDivisor (J.p ≫ T.sX i) n)
    (hpK : RationalMap.transformDivisor (X := J.Y) J.p.toRationalMap K = T.K i)
    {W : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    {sW : W ⟶ Spec (.of ℂ)} (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    {q : W ⟶ J.Y} {r : W ⟶ T.X (i + 1)}
    (hq : IsBirationalMorphism q) (hr : IsBirationalMorphism r)
    (hqs : q ≫ J.p ≫ T.sX i = sW) (hrs : r ≫ T.sX (i + 1) = sW)
    (hcomp : q ≫ J.p ≫ T.f i = r ≫ T.fp i)
    (hD : (Divisor.toQDivisor K + Θ').IsQCartier)
    (hD' : (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).IsQCartier)
    (h : ∀ Z : irreducibleComponents W,
      q (componentGenericPoint W Z) ∉ (Divisor.toQDivisor K + Θ').supp)
    (h' : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).supp)
    (E : MMP.Mori.PrimeDivisor W) (s : I) (hqE : q E.genericPoint = (J.E s).genericPoint) :
    (Divisor.toQDivisor K + Θ').pullback hD h E =
      (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).pullback hD' h' E := by
  have hst := T.isThreefoldStepDiagram i
  have hX' := hst.isNormalVariety_plus
  have hWr : IsNormalVariety ℂ (r ≫ T.sX (i + 1)) := by
    rw [hrs]; exact ⟨hW.toIsVariety, inferInstance⟩
  have : IsProper sW := isProper_of_isProjectiveMorphism _ hW.isProjective
  have : IsSeparated (T.sX (i + 1)) := hX'.1.toIsSeparated
  have : IsProper r := by
    have : IsProper (r ≫ T.sX (i + 1)) := hrs ▸ inferInstance
    exact IsProper.of_comp r (T.sX (i + 1))
  have := hr.isDominant
  set G' := (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).pullback hD' h' with hG'
  obtain ⟨ω', hω'0, hω'K, hord⟩ := exists_ordForm_pullback_eq K hK hpK hW hq hr hqs hrs hcomp
  obtain ⟨a, ha, hΘ'eq⟩ := id hΘ'
  obtain ⟨s', hss', n, D₀, -, hv₀, hlog₀⟩ := ha s
  have hDv := valuation_eq_of_isTransportedValuation hq hr hcomp hWr E s hqE hss'
  -- a Cartier multiple `N (K_{i+1} + B_{i+1})` and its pull-back `N G'`
  obtain ⟨C, C', hCc, hCB, hC, hC', hCp⟩ :=
    (QDivisor.isPullback_pullback hD' h').exists_cartierIndex hD'
  set N := (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).cartierIndex hD' with hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast QDivisor.cartierIndex_pos hD'
  obtain ⟨n', hK'⟩ := hst.isCanonicalDivisor_plus
  rw [← T.K_eq i] at hK'
  obtain rfl : n' = 3 := by
    have := hK'.topologicalKrullDim_eq.symm.trans hst.dim_plus
    exact_mod_cast this
  -- the log discrepancy of `ord_E` over `(X_{i+1}, B_{i+1})`, computed on `W`
  have hlog : MMP.Intersection.IsLogDiscrepancy (T.sX (i + 1)) 3
      (QDivisor.toRDivisor (T.B (i + 1))) (⟨W, r, hWr, hr, E⟩ : DivisorOver ℂ (T.sX (i + 1)))
      (1 + (E.ordForm (pullbackRationalPluriForms (T.sX (i + 1)) r ω') : ℝ) -
        ((G' E : ℚ) : ℝ)) := by
    refine ⟨hX', inferInstance, ω', hω'0, ⟨T.K (i + 1), hK', hω'K⟩, 1, fun _ => 1 / (N : ℝ),
      fun _ => C, fun _ => C', fun _ => hCc, fun Γ => ?_, fun _ => ⟨hCB, hCp⟩, ?_⟩
    · have h1 := congrArg (fun D : QDivisor (T.X (i + 1)) => ((D Γ : ℚ) : ℝ)) hC
      simp only [Finsupp.smul_apply, zsmul_eq_mul, Finsupp.add_apply, Int.cast_natCast] at h1
      rw [Fin.sum_univ_one, QDivisor.coeff_toRDivisor, ← hω'K Γ]
      change ((C Γ : ℤ) : ℝ) = _ at h1
      change (((T.K (i + 1) Γ : ℤ) : ℝ)) + ((T.B (i + 1) Γ : ℚ) : ℝ) = 1 / (N : ℝ) * ((C Γ : ℤ) : ℝ)
      rw [h1]
      push_cast
      field_simp
      rfl
    · have h1 := congrArg (fun D : QDivisor W => ((D E : ℚ) : ℝ)) hC'
      simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h1
      change ((C' E : ℤ) : ℝ) = _ at h1
      rw [Fin.sum_univ_one]
      change _ = 1 + (E.ordForm (pullbackRationalPluriForms (T.sX (i + 1)) r ω') : ℝ) -
        1 / (N : ℝ) * ((C' E : ℤ) : ℝ)
      rw [h1]
      push_cast
      field_simp
      rfl
  have heq := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlog₀ hlog
    (hv₀.trans hDv.symm)
  rw [hord E (J.E s) hqE] at heq
  have := isIso_stalkMap_of_map_eq_genericPoint hq hqE
  rw [coeff_eq_of_isPullback_qDivisor E (J.E s) hqE hD (QDivisor.isPullback_pullback hD h)]
  change ((K (J.E s) : ℤ) : ℚ) + Θ' (J.E s) = G' E
  rw [decreasedBoundary_apply_E hΘ'eq s]
  have : (((((K (J.E s) : ℤ) : ℚ) + (1 - a s) : ℚ)) : ℝ) = ((G' E : ℚ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast this

/-- **The comparison divisor vanishes over the divisors of `Y_i`.** At every prime divisor `E` of
`W` over a prime divisor `P_Y` of `Y_i`, the pull-backs `q^*(K + Θ')` and `r^*(K_{i+1} + B_{i+1})`
have the same coefficient. -/
private theorem pullback_apply_eq_of_map_genericPoint_eq_left {T : StabilizedTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {J : CrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ')
    (K : Divisor J.Y) (hK : ∃ n : ℕ, K.IsCanonicalDivisor (J.p ≫ T.sX i) n)
    (hpK : RationalMap.transformDivisor (X := J.Y) J.p.toRationalMap K = T.K i)
    {W : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    {sW : W ⟶ Spec (.of ℂ)} (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    {q : W ⟶ J.Y} {r : W ⟶ T.X (i + 1)}
    (hq : IsBirationalMorphism q) (hr : IsBirationalMorphism r)
    (hqs : q ≫ J.p ≫ T.sX i = sW) (hrs : r ≫ T.sX (i + 1) = sW)
    (hcomp : q ≫ J.p ≫ T.f i = r ≫ T.fp i)
    (hD : (Divisor.toQDivisor K + Θ').IsQCartier)
    (hD' : (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).IsQCartier)
    (h : ∀ Z : irreducibleComponents W,
      q (componentGenericPoint W Z) ∉ (Divisor.toQDivisor K + Θ').supp)
    (h' : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).supp)
    (E : MMP.Mori.PrimeDivisor W) {PY : MMP.Mori.PrimeDivisor J.Y}
    (hqE : q E.genericPoint = PY.genericPoint) :
    (Divisor.toQDivisor K + Θ').pullback hD h E =
      (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).pullback hD' h' E := by
  by_cases hPY : PY ∈ Set.range J.E
  · obtain ⟨s, rfl⟩ := hPY
    exact pullback_apply_eq_of_map_genericPoint_eq_E hΘ' K hK hpK hW hq hr hqs hrs hcomp hD hD'
      h h' E s hqE
  · obtain ⟨P₀, P₁, hpY, hrE, hfl⟩ := exists_of_map_genericPoint_eq_left hcomp E hqE hPY
    exact pullback_apply_eq hΘ' K hpK hq hr hD hD' h h' E hqE hpY hrE hfl

/-- **`-r^*(K_{i+1} + B_{i+1})` is `q`-nef.** A curve `C` contracted by `q` maps to a point of
`Z_i`, so `r_* C` is zero or a nonnegative multiple of a curve contracted by `f_i⁺`, on which the
`f_i⁺`-ample `K_{i+1} + B_{i+1}` is positive. -/
private theorem intersectionNumber_pullback_nonneg {T : StabilizedTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {J : CrepantJunction (T.sX i) (T.B i) I}
    {W : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    {sW : W ⟶ Spec (.of ℂ)} [AlgebraicGeometry.IsVariety ℂ sW]
    {q : W ⟶ J.Y} {r : W ⟶ T.X (i + 1)} [IsProper r] (hrs : r ≫ T.sX (i + 1) = sW)
    (hcomp : q ≫ J.p ≫ T.f i = r ≫ T.fp i)
    (hD' : (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).IsQCartier)
    (h' : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).supp)
    (hG' : ((Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).pullback hD' h').IsQCartier)
    (C : ProperCurve sW) (hC : C.IsContractedBy q) :
    0 ≤ ((Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).pullback hD' h').intersectionNumber ℂ sW
      C.ι C.dim_le hG' := by
  have hst := T.isThreefoldStepDiagram i
  have hX' := hst.isNormalVariety_plus
  have : AlgebraicGeometry.IsVariety ℂ (T.sX (i + 1)) := hX'.1
  have : QuasiCompact (T.sX (i + 1)) := hX'.1.toQuasiCompact
  have hCr : C.IsContractedBy (r ≫ T.fp i) := fun x hx => by
    simp only [Scheme.Hom.comp_apply]
    rw [← comp_apply_eq hcomp, ← comp_apply_eq hcomp, hC x hx]
  rcases intersectionNumber_pullback_eq_zero_or r hrs (T.fp i) hD'
      (QDivisor.isPullback_pullback hD' h') hG' C hCr with h0 | ⟨d, hd, C'', hC'', heq⟩
  · exact h0.ge
  have hA := hst.hasRelativelyAmpleMultiple_plus
  rw [← T.K_eq i, ← T.B_eq i] at hA
  rw [heq]
  exact mul_nonneg hd (intersectionNumber_pos_of_hasRelativelyAmpleMultiple _ hD' hA C'' hC'').le

/-- **The decreased junction lies above the next model of the tail.** Let `(p_i, Θ_i)` be a
crepant junction of `(X_i, B_i)` extracting `I_∞ = I(X_i, B_i)`, `Θ_i'` its decreased boundary,
and `K` the canonical divisor of `Y_i` with `(p_i)_* K = K_i`. For birational morphisms
`q : W ⟶ Y_i`, `r : W ⟶ X_{i+1}` over `ℂ` from a smooth projective complex variety with
`q ≫ p_i ≫ f_i = r ≫ f_i⁺`, the divisor `F = q^*(K + Θ_i') - r^*(K_{i+1} + B_{i+1})` is
effective and its push-forward along `r` vanishes. -/
@[mmp "lem_mmp_indexc_bridge_comparison"]
public theorem IsDecreasedBoundary.zero_le_pullback_sub_pullback_and_transformDivisor_eq_zero
    {T : StabilizedTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (_hI : (I : Set _) = lowDiscrepancySet (T.sX i) (T.B i))
    {J : CrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ')
    (K : Divisor J.Y) (hK : ∃ n : ℕ, K.IsCanonicalDivisor (J.p ≫ T.sX i) n)
    (hpK : RationalMap.transformDivisor (X := J.Y) J.p.toRationalMap K = T.K i)
    {W : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    (sW : W ⟶ Spec (.of ℂ)) (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (_hWs : MMP.Mori.IsSmoothScheme sW) (q : W ⟶ J.Y) (r : W ⟶ T.X (i + 1))
    (hq : IsBirationalMorphism q) (hr : IsBirationalMorphism r)
    (hqs : q ≫ J.p ≫ T.sX i = sW) (hrs : r ≫ T.sX (i + 1) = sW)
    (hcomp : q ≫ J.p ≫ T.f i = r ≫ T.fp i)
    (hD : (Divisor.toQDivisor K + Θ').IsQCartier)
    (hD' : (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).IsQCartier)
    (h : ∀ Z : irreducibleComponents W,
      q (componentGenericPoint W Z) ∉ (Divisor.toQDivisor K + Θ').supp)
    (h' : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).supp) :
    0 ≤ (Divisor.toQDivisor K + Θ').pullback hD h -
        (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).pullback hD' h' ∧
      RationalMap.transformDivisor (X := W) r.toRationalMap
        ((Divisor.toQDivisor K + Θ').pullback hD h -
          (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).pullback hD' h') = 0 := by
  have hY : IsNormalVariety ℂ (J.p ≫ T.sX i) := J.isQFactorial.1
  have hWv : IsNormalVariety ℂ sW := ⟨hW.toIsVariety, inferInstance⟩
  have : AlgebraicGeometry.IsVariety ℂ sW := hW.toIsVariety
  have : AlgebraicGeometry.IsVariety ℂ (J.p ≫ T.sX i) := hY.1
  have : IsProper sW := isProper_of_isProjectiveMorphism _ hW.isProjective
  have : IsProper q := @IsProper.of_comp _ _ _ q (J.p ≫ T.sX i) (hqs ▸ inferInstance) _
  have : IsProper r := @IsProper.of_comp _ _ _ r (T.sX (i + 1)) (hrs ▸ inferInstance)
    (T.isThreefoldStepDiagram i).isNormalVariety_plus.1.toIsSeparated
  have :=
    isSeparated_toTerminal_of_isNormalVariety (T.isThreefoldStepDiagram i).isNormalVariety_plus
  set G := (Divisor.toQDivisor K + Θ').pullback hD h
  set G' := (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).pullback hD' h'
  have hGq : G.IsQCartier := (QDivisor.isPullback_pullback hD h).isQCartier hD
  have hG'q : G'.IsQCartier := (QDivisor.isPullback_pullback hD' h').isQCartier hD'
  have hG'n : (-G').IsQCartier := isQCartier_neg hG'q
  refine ⟨?_, ?_⟩
  · -- the negativity lemma for `q`
    rw [sub_eq_add_neg]
    have hWq : IsNormalVariety ℂ (q ≫ J.p ≫ T.sX i) := hqs ▸ hWv
    refine nonneg_of_intersectionNumber_nonpos hY hWv q hqs hq (hGq.add hG'n) (fun C hC => ?_)
      (fun P hP => ?_)
    · have := C.isCurve
      have h0 := intersectionNumber_pullback_eq_zero ℂ sW (J.p ≫ T.sX i) q hqs C.ι hD
        (QDivisor.isPullback_pullback hD h) ⟨q C.point, by
          rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, C.range_ι]
          exact Set.eq_singleton_iff_unique_mem.mpr ⟨⟨C.point, subset_closure rfl, rfl⟩,
            by rintro _ ⟨x, hx, rfl⟩; exact hC x hx⟩⟩
      have h1 := intersectionNumber_pullback_nonneg hrs hcomp hD' h' hG'q C hC
      rw [QDivisor.intersectionNumber_add' ℂ sW C.ι C.dim_le _ _ hGq hG'n,
        intersectionNumber_neg ℂ sW C.ι C.dim_le hG'q hG'n]
      change G.intersectionNumber ℂ sW C.ι C.dim_le hGq = 0 at h0
      linarith
    · have hex : ¬ MMP.Mori.RationalMap.IsExceptional (X := W) q.toRationalMap P :=
        fun hex => hP (isExceptionalPrimeDivisor_of_isExceptional hY hWq hq P hex)
      obtain ⟨PY, hv⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional
        hY (⟨W, q, hWq, hq, P⟩ : DivisorOver ℂ (J.p ≫ T.sX i)) hex
      change 0 ≤ G P + -G' P
      rw [pullback_apply_eq_of_map_genericPoint_eq_left hΘ' K hK hpK hW hq hr hqs hrs hcomp hD hD'
        h h' P (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1 hv),
        add_neg_cancel]
  · rw [RationalMap.transformDivisor]
    refine mapPrimeDivisors_eq_zero_of_forall _ fun E P hEP => ?_
    have hrE := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff r E P).mp hEP
    obtain ⟨PY, P₀, hqE, hpY, hfl⟩ := exists_of_map_genericPoint_eq_right hcomp E hrE
    rw [Finsupp.sub_apply, pullback_apply_eq hΘ' K hpK hq hr hD hD' h h' E hqE hpY hrE hfl,
      sub_self]

/-! ## The nef end of a bridge programme maps crepantly to the next model -/

/-! ### Birational morphisms -/

section Birational

/-- If `f` and `f ≫ g` are birational in the sense of [Stacks, Tag 01RO], so is `g`. -/
private theorem isBirational_of_isBirational_comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsBirational f) (hfg : IsBirational (f ≫ g)) : IsBirational g := by
  refine ⟨⟨fun y hy => ?_, fun y₁ hy₁ y₂ hy₂ he => ?_, fun z hz => ?_⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := hf.bijOn.surjOn hy
    exact hfg.bijOn.mapsTo hx
  · obtain ⟨x₁, hx₁, rfl⟩ := hf.bijOn.surjOn hy₁
    obtain ⟨x₂, hx₂, rfl⟩ := hf.bijOn.surjOn hy₂
    exact congrArg f (hfg.bijOn.injOn hx₁ hx₂ he)
  · obtain ⟨x, hx, rfl⟩ := hfg.bijOn.surjOn hz
    exact ⟨f x, hf.bijOn.mapsTo hx, rfl⟩
  · obtain ⟨x, hx, rfl⟩ := hf.bijOn.surjOn hy
    have h1 := hfg.isIso_stalkMap x hx
    have h2 := hf.isIso_stalkMap x hx
    rw [Scheme.Hom.stalkMap_comp] at h1
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (g.stalkMap (f x)) (f.stalkMap x) h2 h1

/-- A proper morphism `q` with `q_* 𝒪 = 𝒪` can be cancelled on the left. -/
private theorem eq_of_comp_eq_of_isIso_c {X Y Z : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    [IsIso q.c] {a b : Y ⟶ Z} (h : q ≫ a = q ≫ b) : a = b := by
  obtain ⟨c, -, hc⟩ := MMP.existsUnique_comp_eq_of_isIso_c q (q ≫ a) fun x x' hx => by
    simp only [Scheme.Hom.comp_apply, hx]
  exact (hc a rfl).trans (hc b h.symm).symm

/-- A morphism of projective varieties over `ℂ` is H-projective. -/
private theorem isProjectiveMorphism_of_isProjectiveVariety {W V : Scheme.{0}}
    {sW : W ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hV : MMP.Mori.IsProjectiveVariety ℂ sV) (q : W ⟶ V) (hq : q ≫ sV = sW) :
    IsProjectiveMorphism q :=
  have : IsSeparated sV := hV.toIsSeparated
  IsProjectiveMorphism.of_comp q sV (hq ▸ hW.isProjective)

end Birational

/-! ### Exceptional prime divisors -/

section Exceptional

/-- If the push-forward along a separated birational morphism `r : W ⟶ X` onto a normal scheme
vanishes, then so does the coefficient of every prime divisor of `W` lying over a prime divisor of
`X`. -/
private theorem apply_eq_zero_of_transformDivisor_eq_zero {W X : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (r : W ⟶ X) [IsSeparated r] (hr : IsBirationalMorphism r)
    {F : QDivisor W}
    (hF : RationalMap.transformDivisor (X := W) r.toRationalMap F = 0)
    (E : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X)
    (hE : r E.genericPoint = Q.genericPoint) : F E = 0 := by
  have := hr.isDominant
  have := Q.isDiscreteValuationRing_localRing
  have h := congrArg (fun G : QDivisor X => G Q) hF
  rw [RationalMap.transformDivisor, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff r E Q).mpr hE)
    (fun E' hE' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      eq_of_map_eq_of_valuationRing hr.functionFieldMap_bijective
        ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff r E' Q).mp hE') hE)] at h
  simpa using h

/-- **The negativity lemma, along prime divisors over prime divisors.** Let `f : Y ⟶ X` be a
proper birational morphism of normal varieties and `B` a `ℚ`-Cartier divisor on `Y` with
`(B · C) ≤ 0` on every curve contracted by `f`, whose coefficient along every prime divisor lying
over a prime divisor of `X` is nonnegative. Then `B` is effective. -/
private theorem nonneg_of_intersectionNumber_nonpos' {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} [QuasiCompact sY] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety ℂ sX) (hY : IsNormalVariety ℂ sY) (f : Y ⟶ X) (hf : f ≫ sX = sY)
    [IsProper f] (hfb : IsBirationalMorphism f) {B : QDivisor Y} (hB : B.IsQCartier)
    (hnef : ∀ C : ProperCurve sY, C.IsContractedBy f →
      B.intersectionNumber ℂ sY C.ι C.dim_le hB ≤ 0)
    (hBG : ∀ (P : MMP.Mori.PrimeDivisor Y) (Q : MMP.Mori.PrimeDivisor X),
      f P.genericPoint = Q.genericPoint → 0 ≤ B P) :
    0 ≤ B := by
  have hBn := isQCartier_neg hB
  refine MMP.Fourfold.Oai4C1.Negativity.nonneg_of_transformDivisor_nonneg ℂ sX sY hX hY f hf hfb
    (QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sY hBn fun C hC => ?_) fun Q => ?_
  · rw [intersectionNumber_neg ℂ sY C.ι C.dim_le hB hBn]
    exact neg_nonneg.mpr (hnef C hC)
  · obtain ⟨E, hE, -, hc⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX (hf ▸ hY) hfb Q
    change (0 : ℚ) ≤ _
    rw [hc]
    exact hBG E Q hE

end Exceptional

/-- A `ℚ`-divisor with a relatively ample multiple is relatively nef. -/
private theorem isRelativelyNef_of_hasRelativelyAmpleMultiple {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y} {D : QDivisor X} (hD : D.IsQCartier)
    (ha : D.HasRelativelyAmpleMultiple f) : D.IsRelativelyNef sX f :=
  QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hD fun C hC =>
    (intersectionNumber_pos_of_hasRelativelyAmpleMultiple
      sX hD ha C hC).le

/-! ### A step of the programme -/

section Step

variable {Xm Xp Z W : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]

/-- **The comparison across one step is effective.** Let `(X⁻, B⁻) → Z ← (X⁺, B⁺)` be a threefold
step diagram and `u : W ⟶ X⁻`, `v : W ⟶ X⁺` birational morphisms of a normal projective variety
with `u ≫ f⁻ = v ≫ f⁺`. Then `u^*(K⁻ + B⁻) - v^*(K⁺ + B⁺)` is effective, by the negativity lemma
for `u ≫ f⁻`: it is anti-nef over `Z`, since `-(K⁻ + B⁻)` is `f⁻`-ample and `K⁺ + B⁺` is
`f⁺`-ample, and it vanishes along every prime divisor of `W` over a prime divisor of `Z`. -/
private theorem zero_le_pullback_sub_pullback_of_isThreefoldStepDiagram
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) {Kp : Divisor Xp} {Bp : QDivisor Xp}
    (hKp : Kp = flipTransform fm fp K) (hBp : Bp = flipTransform fm fp B)
    {sW : W ⟶ Spec (.of ℂ)} (hW : MMP.Mori.IsProjectiveVariety ℂ sW) (u : W ⟶ Xm) (v : W ⟶ Xp)
    (hu : IsBirationalMorphism u) (hv : IsBirationalMorphism v) (hus : u ≫ sXm = sW)
    (hvs : v ≫ sXp = sW) (hc : u ≫ fm = v ≫ fp)
    (hDm : (Divisor.toQDivisor K + B).IsQCartier) (hDp : (Divisor.toQDivisor Kp + Bp).IsQCartier)
    (hm : ∀ Z : irreducibleComponents W, u (componentGenericPoint W Z) ∉
      (Divisor.toQDivisor K + B).supp)
    (hp : ∀ Z : irreducibleComponents W, v (componentGenericPoint W Z) ∉
      (Divisor.toQDivisor Kp + Bp).supp) :
    0 ≤ (Divisor.toQDivisor K + B).pullback hDm hm -
      (Divisor.toQDivisor Kp + Bp).pullback hDp hp := by
  subst hKp hBp
  have hXm := h.isNormalVariety_minus
  have hXp := h.isNormalVariety_plus
  have hZ := h.isNormalVariety_target
  have : IsIntegral Z := hZ.1.toIsIntegral
  have : IsNormal Z := hZ.2
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have := isSeparated_toTerminal_of_isNormalVariety hZ
  have : AlgebraicGeometry.IsVariety ℂ sW := hW.toIsVariety
  have : AlgebraicGeometry.IsVariety ℂ sXm := hXm.1
  have : AlgebraicGeometry.IsVariety ℂ sXp := hXp.1
  have : IsProper sW := isProper_of_isProjectiveMorphism _ hW.isProjective
  have : IsProper u := @IsProper.of_comp _ _ _ u sXm (hus ▸ inferInstance) _
  have : IsProper v := @IsProper.of_comp _ _ _ v sXp (hvs ▸ inferInstance) _
  have : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  have : IsProper fp := h.isSmallMorphism_plus.isProper
  have hfmb := h.isBirationalMorphism_minus
  have hfpb := h.isSmallMorphism_plus.isBirationalMorphism
  have := hfmb.isDominant
  have := hfpb.isDominant
  have := hu.isDominant
  have hWv : IsNormalVariety ℂ sW := ⟨hW.toIsVariety, inferInstance⟩
  set Gm := (Divisor.toQDivisor K + B).pullback hDm hm
  set Gp := (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B).pullback hDp hp
  have hGm : Gm.IsQCartier := (QDivisor.isPullback_pullback hDm hm).isQCartier hDm
  have hGp : Gp.IsQCartier := (QDivisor.isPullback_pullback hDp hp).isQCartier hDp
  have hGpn : (-Gp).IsQCartier := isQCartier_neg hGp
  have hws : (u ≫ fm) ≫ sZ = sW := by rw [Category.assoc, h.comp_eq_minus, hus]
  rw [sub_eq_add_neg]
  refine nonneg_of_intersectionNumber_nonpos' hZ hWv (u ≫ fm) hws
    (isBirationalMorphism_comp hu hfmb) (hGm.add hGpn) (fun C hC => ?_) (fun P Q hPQ => ?_)
  · have := C.isCurve
    rw [QDivisor.intersectionNumber_add' ℂ sW C.ι C.dim_le _ _ hGm hGpn,
      intersectionNumber_neg ℂ sW C.ι C.dim_le hGp hGpn]
    have hneg := isQCartier_neg hDm
    have h1 := intersectionNumber_isPullback_nonneg u hus fm hneg
      (isRelativelyNef_of_hasRelativelyAmpleMultiple sXm hneg h.hasRelativelyAmpleMultiple_minus)
      (isPullback_neg (QDivisor.isPullback_pullback hDm hm)
        (map_componentGenericPoint_notMem_supp_of_isDominant' u _)) C hC
    rw [intersectionNumber_neg ℂ sW C.ι C.dim_le hGm] at h1
    have h2 := intersectionNumber_isPullback_nonneg v hvs fp hDp
      (isRelativelyNef_of_hasRelativelyAmpleMultiple sXp hDp h.hasRelativelyAmpleMultiple_plus)
      (QDivisor.isPullback_pullback hDp hp) C (hc ▸ hC)
    linarith
  · -- the coefficients agree along a prime divisor over a prime divisor of `Z`
    have := Q.isDiscreteValuationRing_localRing
    obtain ⟨Γp, hΓp, -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hZ
        (h.comp_eq_plus ▸ hXp) hfpb Q
    have hvP : v P.genericPoint = Γp.genericPoint :=
      eq_of_map_eq_of_valuationRing hfpb.functionFieldMap_bijective (by
        rw [← Scheme.Hom.comp_apply, ← hc]; exact hPQ) hΓp
    obtain ⟨Pm, huP, hfl⟩ := exists_eq_genericPoint_flipTransform_apply hfmb
      h.isSmallMorphism_plus Γp (u P.genericPoint) (by
        rw [← Scheme.Hom.comp_apply, hPQ, hΓp])
    have := isIso_stalkMap_of_map_eq_genericPoint hu huP
    have := isIso_stalkMap_of_map_eq_genericPoint hv hvP
    change 0 ≤ Gm P + -Gp P
    rw [coeff_eq_of_isPullback_qDivisor P Pm huP hDm (QDivisor.isPullback_pullback hDm hm),
      coeff_eq_of_isPullback_qDivisor P Γp hvP hDp (QDivisor.isPullback_pullback hDp hp)]
    change 0 ≤ ((K Pm : ℤ) : ℚ) + B Pm + -(((flipTransform fm fp K Γp : ℤ) : ℚ) +
      flipTransform fm fp B Γp)
    rw [hfl K, hfl B, add_neg_cancel]

end Step

/-! ### Two ends of a programme -/

section TwoEnds

variable {W V₁ V₂ Z : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W]
  [IsNormal W] [IsIntegral V₁] [CompactSpace V₁] [IsLocallyNoetherian V₁] [IsNormal V₁]
  [IsIntegral V₂] [CompactSpace V₂] [IsLocallyNoetherian V₂] [IsNormal V₂]

omit [CompactSpace V₁] in
/-- **One end of the two-ends argument.** Let `q : W ⟶ V` be a birational morphism of normal
projective varieties and `G'` a `ℚ`-Cartier divisor on `W` with `(G' · C) ≥ 0` on every curve
contracted by `q`. If `G' ≤ q^* D` along every prime divisor of `W` over a prime divisor of `V`,
then `G' ≤ q^* D`: this is the negativity lemma for `q^* D - G'`, as `(q^* D · C) = 0`. -/
private theorem le_pullback_of_intersectionNumber_nonneg {sW : W ⟶ Spec (.of ℂ)}
    {sV₁ : V₁ ⟶ Spec (.of ℂ)} (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hV₁ : MMP.Mori.IsProjectiveVariety ℂ sV₁) (q : W ⟶ V₁) (hq : IsBirationalMorphism q)
    (hqs : q ≫ sV₁ = sW) {D : QDivisor V₁} (hD : D.IsQCartier)
    (h : ∀ Z : irreducibleComponents W, q (componentGenericPoint W Z) ∉ D.supp)
    {G' : QDivisor W} (hG' : G'.IsQCartier)
    (hnn : ∀ C : ProperCurve sW, C.IsContractedBy q →
      0 ≤ G'.intersectionNumber ℂ sW C.ι C.dim_le hG')
    (hcoeff : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor V₁),
      q P.genericPoint = Q.genericPoint → G' P ≤ D.pullback hD h P) :
    G' ≤ D.pullback hD h := by
  have : AlgebraicGeometry.IsVariety ℂ sW := hW.toIsVariety
  have : AlgebraicGeometry.IsVariety ℂ sV₁ := hV₁.toIsVariety
  have : IsProper sW := isProper_of_isProjectiveMorphism _ hW.isProjective
  have : IsProper q := @IsProper.of_comp _ _ _ q sV₁ (hqs ▸ inferInstance) _
  have hp := QDivisor.isPullback_pullback hD h
  have hG := hp.isQCartier hD
  have hG'n := isQCartier_neg hG'
  rw [← sub_nonneg, sub_eq_add_neg]
  refine nonneg_of_intersectionNumber_nonpos' ⟨hV₁.toIsVariety, inferInstance⟩
    ⟨hW.toIsVariety, inferInstance⟩ q hqs hq (hG.add hG'n) (fun C hC => ?_)
    fun P Q hPQ => by simpa [sub_nonneg] using hcoeff P Q hPQ
  have := C.isCurve
  rw [QDivisor.intersectionNumber_add' ℂ sW C.ι C.dim_le _ _ hG hG'n,
    intersectionNumber_neg ℂ sW C.ι C.dim_le hG' hG'n,
    intersectionNumber_isPullback_eq_zero q hqs hD hp C hC]
  linarith [hnn C hC]

/-- **A prescribed ample end is a morphic image.** Let `q_j : W ⟶ V_j` be birational morphisms
of normal projective varieties with `q₁ ≫ π₁ = q₂ ≫ π₂` for `π_j : V_j ⟶ Z`, `D₁` a `π₁`-nef and
`D₂` a `π₂`-ample `ℚ`-Cartier divisor, and `q₁^* D₁ + F₁ = q₂^* D₂ + F₂` with `F_j ≥ 0`
vanishing along the prime divisors of `W` over prime divisors of `V_j`. Then `q₂ = h ∘ q₁` for a
morphism `h : V₁ ⟶ V₂` with `D₁ = h^* D₂`. -/
private theorem exists_comp_eq_and_isPullback {sW : W ⟶ Spec (.of ℂ)}
    {sV₁ : V₁ ⟶ Spec (.of ℂ)} {sV₂ : V₂ ⟶ Spec (.of ℂ)} (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hV₁ : MMP.Mori.IsProjectiveVariety ℂ sV₁) (hV₂ : MMP.Mori.IsProjectiveVariety ℂ sV₂)
    (q₁ : W ⟶ V₁) (q₂ : W ⟶ V₂) (hq₁ : IsBirationalMorphism q₁) (hq₂ : IsBirationalMorphism q₂)
    (hq₁s : q₁ ≫ sV₁ = sW) (hq₂s : q₂ ≫ sV₂ = sW) (π₁ : V₁ ⟶ Z) (π₂ : V₂ ⟶ Z)
    (hπ : q₁ ≫ π₁ = q₂ ≫ π₂) {D₁ : QDivisor V₁} {D₂ : QDivisor V₂} (hD₁ : D₁.IsQCartier)
    (hD₂ : D₂.IsQCartier) (hnef : D₁.IsRelativelyNef sV₁ π₁)
    (hamp : D₂.HasRelativelyAmpleMultiple π₂)
    (h₁ : ∀ Z : irreducibleComponents W, q₁ (componentGenericPoint W Z) ∉ D₁.supp)
    (h₂ : ∀ Z : irreducibleComponents W, q₂ (componentGenericPoint W Z) ∉ D₂.supp)
    {F₁ F₂ : QDivisor W} (hF₁ : 0 ≤ F₁) (hF₂ : 0 ≤ F₂)
    (hF₁e : ∀ (E : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor V₁),
      q₁ E.genericPoint = Q.genericPoint → F₁ E = 0)
    (hF₂e : ∀ (E : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor V₂),
      q₂ E.genericPoint = Q.genericPoint → F₂ E = 0)
    (hsum : D₁.pullback hD₁ h₁ + F₁ = D₂.pullback hD₂ h₂ + F₂) :
    ∃ (h : V₁ ⟶ V₂) (hh : ∀ Z : irreducibleComponents V₁, h (componentGenericPoint V₁ Z) ∉
      D₂.supp), q₁ ≫ h = q₂ ∧ D₂.IsPullback h hh D₁ := by
  have : AlgebraicGeometry.IsVariety ℂ sW := hW.toIsVariety
  have : AlgebraicGeometry.IsVariety ℂ sV₁ := hV₁.toIsVariety
  have : AlgebraicGeometry.IsVariety ℂ sV₂ := hV₂.toIsVariety
  have : IsProper sW := isProper_of_isProjectiveMorphism _ hW.isProjective
  have : IsProper q₁ := @IsProper.of_comp _ _ _ q₁ sV₁ (hq₁s ▸ inferInstance) _
  have : IsProper q₂ := @IsProper.of_comp _ _ _ q₂ sV₂ (hq₂s ▸ inferInstance) _
  have := hq₁.isDominant
  have := hq₂.isDominant
  have hWv : IsNormalVariety ℂ sW := ⟨hW.toIsVariety, inferInstance⟩
  have hV₁v : IsNormalVariety ℂ sV₁ := ⟨hV₁.toIsVariety, inferInstance⟩
  have hV₂v : IsNormalVariety ℂ sV₂ := ⟨hV₂.toIsVariety, inferInstance⟩
  set G₁ := D₁.pullback hD₁ h₁ with hG₁def
  set G₂ := D₂.pullback hD₂ h₂ with hG₂def
  have hp₁ := QDivisor.isPullback_pullback hD₁ h₁
  have hp₂ := QDivisor.isPullback_pullback hD₂ h₂
  have hG₁ : G₁.IsQCartier := hp₁.isQCartier hD₁
  have hG₂ : G₂.IsQCartier := hp₂.isQCartier hD₂
  have hE : G₁ - G₂ = F₂ - F₁ := by
    rw [sub_eq_sub_iff_add_eq_add, hsum, add_comm]
  have hcomp₁ : ∀ C : ProperCurve sW, C.IsContractedBy q₁ → C.IsContractedBy (q₂ ≫ π₂) :=
    fun C hC x hx => by rw [← hπ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]
  have hcomp₂ : ∀ C : ProperCurve sW, C.IsContractedBy q₂ → C.IsContractedBy (q₁ ≫ π₁) :=
    fun C hC x hx => by rw [hπ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]
  -- the negativity lemma, for `q₁` and for `q₂`
  have hG : G₁ = G₂ := by
    refine le_antisymm (le_pullback_of_intersectionNumber_nonneg hW hV₂ q₂ hq₂ hq₂s hD₂ h₂ hG₁
      (fun C hC => intersectionNumber_isPullback_nonneg q₁ hq₁s π₁ hD₁ hnef
        hp₁ C (hcomp₂ C hC)) fun P Q hPQ => ?_)
      (le_pullback_of_intersectionNumber_nonneg hW hV₁ q₁ hq₁ hq₁s hD₁ h₁ hG₂
      (fun C hC => intersectionNumber_isPullback_nonneg q₂ hq₂s π₂ hD₂
        (isRelativelyNef_of_hasRelativelyAmpleMultiple sV₂ hD₂ hamp) hp₂ C (hcomp₁ C hC))
      fun P Q hPQ => ?_)
    · rw [← sub_nonneg, ← Finsupp.sub_apply, ← neg_sub, hE, neg_sub, Finsupp.sub_apply,
        hF₂e P Q hPQ, sub_zero]
      exact hF₁ P
    · rw [← sub_nonneg, ← Finsupp.sub_apply, hE, Finsupp.sub_apply, hF₁e P Q hPQ, sub_zero]
      exact hF₂ P
  -- a curve contracted by `q₁` is contracted by `q₂`
  have hcurve : ∀ C : ProperCurve sW, C.IsContractedBy q₁ → C.IsContractedBy q₂ := by
    intro C hC
    by_contra hC₂
    have := C.isCurve
    obtain ⟨⟨_, hC''⟩, rfl, d, hd, heq⟩ := exists_intersectionNumber_pullback_eq_mul q₂ hq₂s hD₂
      hp₂ hG₂ C (not_exists_range_eq_singleton q₂ C hC₂)
    have hpos := intersectionNumber_pos_of_hasRelativelyAmpleMultiple
      sV₂ hD₂ hamp _ (isContractedBy_map q₂ hq₂s π₂ C hC₂ (hcomp₁ C hC))
    have h0 := intersectionNumber_isPullback_eq_zero q₁ hq₁s hD₁ hp₁ C hC
    rw [MMP.Fourfold.intersectionNumber_congr sW C.ι C.dim_le hG₁ hG₂ hG] at h0
    rw [h0] at heq
    nlinarith
  -- the factorization
  have hO := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism sW sV₁
    hW.toIsVariety hV₁v q₁ hq₁).1
  have : IsIso q₁.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ q₁.c fun U => hO U.unop
  have : Surjective q₁ := ⟨fun t => by
    rw [← Set.mem_range, ← q₁.isClosedMap.isClosed_range.closure_eq, q₁.denseRange.closure_range]
    trivial⟩
  obtain ⟨h, hh, -⟩ := MMP.Mori.existsUnique_comp_eq_of_isContractedBy hW hV₁ hV₂
    (isProjectiveMorphism_of_isProjectiveVariety hW hV₁ q₁ hq₁s) hq₁s hq₂s hcurve
  subst hh
  have : IsDominant h := IsDominant.of_comp q₁ h
  have hh : ∀ Z : irreducibleComponents V₁, h (componentGenericPoint V₁ Z) ∉ D₂.supp :=
    map_componentGenericPoint_notMem_supp_of_isDominant' h D₂
  refine ⟨h, hh, rfl, ?_⟩
  -- `D₁ = h^* D₂`, comparing coefficients along the strict transforms on `W`
  set G := D₂.pullback hD₂ hh
  have hpG := QDivisor.isPullback_pullback hD₂ hh
  have hGq : G.IsQCartier := hpG.isQCartier hD₂
  have hgen : ∀ Z : irreducibleComponents W, q₁ (componentGenericPoint W Z) ∉ G.supp :=
    map_componentGenericPoint_notMem_supp_of_isDominant' q₁ G
  have hcompeq : G₂ = G.pullback hGq hgen :=
    (qDivisor_isPullback_comp h q₁ hpG
      (QDivisor.isPullback_pullback hGq hgen)).2.pullback_eq hD₂
  suffices hD : G = D₁ from hD ▸ hpG
  refine Finsupp.ext fun P => ?_
  obtain ⟨E, hE₁, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0}
    hV₁v (hq₁s ▸ hWv) hq₁ P
  have := hiso
  have c₁ := coeff_eq_of_isPullback_qDivisor E P hE₁ hD₁ hp₁
  have c₂ := coeff_eq_of_isPullback_qDivisor E P hE₁ hGq (QDivisor.isPullback_pullback hGq hgen)
  rw [← c₁, ← c₂, ← hcompeq, ← hG]

end TwoEnds

/-! ### Common models -/

section CommonModel

/-- **A common normal model of two models.** For proper birational morphisms `a : A ⟶ S`,
`b : B ⟶ S` of normal varieties to a separated scheme there is a normal variety `N` with proper
birational morphisms `c : N ⟶ A`, `d : N ⟶ B` and `c ≫ a = d ≫ b`. -/
private theorem exists_common_model {A B S : Scheme.{0}} {sA : A ⟶ Spec (.of ℂ)}
    {sB : B ⟶ Spec (.of ℂ)} (hA : IsNormalVariety ℂ sA) (hB : IsNormalVariety ℂ sB)
    [IsSeparated (S ↘ ⊤_ Scheme)] (a : A ⟶ S) (b : B ⟶ S) [IsProper a] [IsProper b]
    (ha : IsBirationalMorphism a) (hb : IsBirationalMorphism b) :
    ∃ (N : Scheme.{0}) (c : N ⟶ A) (d : N ⟶ B), IsNormalVariety ℂ (c ≫ sA) ∧ IsProper c ∧
      IsProper d ∧ IsBirationalMorphism c ∧ IsBirationalMorphism d ∧ c ≫ a = d ≫ b := by
  obtain ⟨e₁, he₁⟩ := exists_partialIso_isOver ha
  obtain ⟨e₂, he₂⟩ := exists_partialIso_isOver hb
  obtain ⟨N, c, d, hN, hc, hd, hcb, hdb, -, hcomm⟩ :=
    MMP.Mori.exists_isNormalVariety_isProper_isBirationalMorphism hA hB a b
      (e₁.trans e₂.symm).toRationalMap (RationalMap.isBirational_toRationalMap _)
      (compHom_toRationalMap_of_isOver _ (he₁.trans he₂.symm))
  exact ⟨N, c, d, hN, hc, hd, hcb, hdb, hcomm⟩

end CommonModel

/-! ### The programme -/

section Programme

variable {T : StabilizedTail} {i : ℕ}
  {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
  {J : CrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y} {K : Divisor J.Y}
  (P : RelativeThreefoldProgram (J.p ≫ T.sX i) (T.sZ i) (J.p ≫ T.f i) K Θ')

include P in
/-- The models of the programme are projective varieties. -/
private theorem isProjectiveVariety_modelStr {k : ℕ} (hk : k ≤ P.m) :
    MMP.Mori.IsProjectiveVariety ℂ (modelStr (J.p ≫ T.sX i) P.sY k) := by
  rcases k with _ | k
  · exact P.isProjectiveVariety
  · exact (P.isThreefoldStepDiagram k (by omega)).isProjectiveVariety_plus

/-- Reassociation of a composite of five morphisms. -/
private theorem comp_assoc₅ {A B C D E F : Scheme.{0}} (g : A ⟶ B) (π : B ⟶ C) (c : C ⟶ D)
    (x : D ⟶ E) (y : E ⟶ F) : (g ≫ π ≫ c ≫ x) ≫ y = g ≫ π ≫ c ≫ x ≫ y := by
  simp only [Category.assoc]

include P in
/-- **A common normal model of the first models.** For `j ≤ m` there is a normal variety `N`
with proper birational morphisms `q_k : N ⟶ V_k`, `k ≤ j`, compatible with the steps. -/
private theorem exists_normal_model : ∀ (j : ℕ), j ≤ P.m →
    ∃ (N : Scheme.{0}) (sN : N ⟶ Spec (.of ℂ)) (q : ∀ k : Fin (j + 1), N ⟶ modelSeq J.Y P.Y k),
      IsNormalVariety ℂ sN ∧ (∀ k, IsProper (q k)) ∧ (∀ k, IsBirationalMorphism (q k)) ∧
      (∀ k, q k ≫ modelStr (J.p ≫ T.sX i) P.sY k = sN) ∧
      (∀ (k : ℕ) (hk : k < j), q ⟨k, by omega⟩ ≫ P.g k = q ⟨k + 1, by omega⟩ ≫ P.gp k)
  | 0, _ => by
    refine ⟨J.Y, J.p ≫ T.sX i, fun k => Fin.snoc (α := fun k : Fin 1 => J.Y ⟶ modelSeq J.Y P.Y k)
      (fun k => k.elim0) (𝟙 J.Y) k, J.isQFactorial.1, ?_, ?_, ?_, fun k hk => absurd hk (by omega)⟩
    all_goals
      intro k
      obtain rfl : k = Fin.last 0 := Fin.ext (by have := k.isLt; simp only [Fin.val_last]; omega)
      simp only
    · exact inferInstanceAs (IsProper (𝟙 J.Y))
    · exact MMP.Mori.isBirationalMorphism_of_isIso (𝟙 J.Y)
    · exact Category.id_comp _
  | j + 1, hj => by
    obtain ⟨N, sN, q, hN, hqp, hqb, hqs, hqc⟩ := exists_normal_model j (by omega)
    have hst := P.isThreefoldStepDiagram j (by omega)
    have hT := hst.isNormalVariety_target
    have := isSeparated_toTerminal_of_isNormalVariety hT
    have : IsIntegral N := hN.1.toIsIntegral
    have : IsProper (P.g j) := isProper_of_isProjectiveMorphism _ hst.isProjectiveMorphism_minus
    have : IsProper (P.gp j) := hst.isSmallMorphism_plus.isProper
    set qj : N ⟶ modelSeq J.Y P.Y j := q ⟨j, by omega⟩ with hqj
    have : IsProper qj := hqp _
    have hqjs : qj ≫ modelStr (J.p ≫ T.sX i) P.sY j = sN := hqs _
    obtain ⟨N', c, d, hN', hc, hd, hcb, hdb, hcd⟩ := exists_common_model hN
      hst.isNormalVariety_plus (qj ≫ P.g j) (P.gp j)
      (isBirationalMorphism_comp (hqb _) hst.isBirationalMorphism_minus)
      hst.isSmallMorphism_plus.isBirationalMorphism
    have : IsIntegral N' := hN'.1.toIsIntegral
    let q' : ∀ k : Fin (j + 2), N' ⟶ modelSeq J.Y P.Y k :=
      Fin.snoc (α := fun k : Fin (j + 2) => N' ⟶ modelSeq J.Y P.Y k) (fun k => c ≫ q k) d
    have hq'c : ∀ k : Fin (j + 1), q' k.castSucc = c ≫ q k := fun k => Fin.snoc_castSucc ..
    have hq'l : q' (Fin.last (j + 1)) = d := Fin.snoc_last ..
    have hq'lt : ∀ (k : ℕ) (hk : k < j + 1), q' ⟨k, by omega⟩ = c ≫ q ⟨k, hk⟩ :=
      fun k hk => hq'c ⟨k, hk⟩
    have hq'e : q' ⟨j + 1, by omega⟩ = d := hq'l
    refine ⟨N', c ≫ sN, q', hN', ?_, ?_, ?_, ?_⟩
    · refine Fin.lastCases ?_ (fun k => ?_)
      · rw [hq'l]; exact hd
      · rw [hq'c]; have := hqp k; infer_instance
    · refine Fin.lastCases ?_ (fun k => ?_)
      · rw [hq'l]; exact hdb
      · rw [hq'c]; exact isBirationalMorphism_comp hcb (hqb k)
    · refine Fin.lastCases ?_ (fun k => ?_)
      · rw [hq'l]
        change d ≫ P.sY j = c ≫ sN
        calc d ≫ P.sY j = d ≫ P.gp j ≫ P.sT j := by rw [hst.comp_eq_plus]
          _ = c ≫ qj ≫ P.g j ≫ P.sT j := by
            rw [← Category.assoc, ← hcd]; simp only [Category.assoc]
          _ = c ≫ qj ≫ modelStr (J.p ≫ T.sX i) P.sY j := by rw [hst.comp_eq_minus]
          _ = c ≫ sN := by rw [hqjs]
      · rw [hq'c]
        exact (Category.assoc _ _ _).trans (congrArg (c ≫ ·) (hqs k))
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
      · rw [hq'lt k (by omega), hq'lt (k + 1) (by omega)]
        calc (c ≫ q ⟨k, by omega⟩) ≫ P.g k = c ≫ (q ⟨k, by omega⟩ ≫ P.g k) :=
              Category.assoc _ _ _
          _ = c ≫ (q ⟨k + 1, by omega⟩ ≫ P.gp k) := congrArg _ (hqc k hk')
          _ = (c ≫ q ⟨k + 1, by omega⟩) ≫ P.gp k := (Category.assoc _ _ _).symm
      · rw [hq'lt k (by omega), hq'e]
        exact (Category.assoc _ _ _).trans hcd

/-- **A smooth projective common model.** There is a smooth projective variety `W` with
birational morphisms `q_k : W ⟶ V_k`, `k ≤ m`, compatible with the steps of the programme, and
`r : W ⟶ X_{i+1}` with `q_0 ≫ p_i ≫ f_i = r ≫ f_i⁺`. -/
private theorem exists_model :
    ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : CompactSpace W) (_ : IsLocallyNoetherian W)
      (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ))
      (q : ∀ k : Fin (P.m + 1), W ⟶ modelSeq J.Y P.Y k) (r : W ⟶ T.X (i + 1)),
      MMP.Mori.IsProjectiveVariety ℂ sW ∧ IsSmoothScheme sW ∧ (∀ k, IsBirationalMorphism (q k)) ∧
      (∀ k, q k ≫ modelStr (J.p ≫ T.sX i) P.sY k = sW) ∧
      (∀ (k : ℕ) (hk : k < P.m), q ⟨k, by omega⟩ ≫ P.g k = q ⟨k + 1, by omega⟩ ≫ P.gp k) ∧
      IsBirationalMorphism r ∧ r ≫ T.sX (i + 1) = sW ∧
      q ⟨0, by omega⟩ ≫ J.p ≫ T.f i = r ≫ T.fp i := by
  obtain ⟨N, sN, q, hN, hqp, hqb, hqs, hqc⟩ := exists_normal_model P P.m le_rfl
  have : IsIntegral N := hN.1.toIsIntegral
  have : IsNormal N := hN.2
  -- the model of `X_{i+1}`
  have hst := T.isThreefoldStepDiagram i
  have hZ := hst.isNormalVariety_target
  have := isSeparated_toTerminal_of_isNormalVariety hZ
  have : IsProper (T.f i) := isProper_of_isProjectiveMorphism _ hst.isProjectiveMorphism_minus
  have : IsProper (T.fp i) := hst.isSmallMorphism_plus.isProper
  have : IsProper J.p := isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism
  set q0 : N ⟶ J.Y := q ⟨0, by omega⟩ with hq0
  have : IsProper q0 := hqp _
  have hq0s : q0 ≫ J.p ≫ T.sX i = sN := hqs ⟨0, by omega⟩
  have hab : IsBirationalMorphism (q0 ≫ J.p ≫ T.f i) :=
    isBirationalMorphism_comp (hqb _) (isBirationalMorphism_comp J.isBirationalMorphism
      hst.isBirationalMorphism_minus)
  obtain ⟨N', c, r₀, hN', hc, hr₀, hcb, hr₀b, hcr⟩ :=
    exists_common_model hN hst.isNormalVariety_plus
    (q0 ≫ J.p ≫ T.f i) (T.fp i) hab hst.isSmallMorphism_plus.isBirationalMorphism
  -- Chow's lemma
  have : AlgebraicGeometry.IsVariety ℂ (c ≫ sN) := hN'.1
  have : IsIntegral N' := hN'.1.toIsIntegral
  have : IsNormal N' := hN'.2
  have : IsProper (J.p ≫ T.sX i) :=
    isProper_of_isProjectiveMorphism _ J.isProjectiveVariety.isProjective
  have : IsProper sN := by rw [← hq0s]; infer_instance
  obtain ⟨Z', π, hZ'v, hZ'p, -, hπb⟩ :=
    (MMP.Resolution.Bridges.exists_isProjectiveMorphism_isBirational_chowModification ℂ).2
      (sZ := c ≫ sN) hN'.1 inferInstance
  have := hZ'v
  have : IsIntegral Z' := hZ'v.toIsIntegral
  have : IsSeparated (c ≫ sN) := hN'.1.toIsSeparated
  have : IsProper (π ≫ c ≫ sN) := isProper_of_isProjectiveMorphism _ hZ'p
  have : IsProper π := IsProper.of_comp π (c ≫ sN)
  -- a strong resolution
  obtain ⟨W, g, hWv, hgp, hgb, hWs, -, -⟩ := MMP.Resolution.exists_isStrongResolution _ hZ'v
  have := hWv
  have : IsIntegral W := hWv.toIsIntegral
  have : LocallyOfFiniteType (g ≫ π ≫ c ≫ sN) := hWv.toLocallyOfFiniteType
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (g ≫ π ≫ c ≫ sN)
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (g ≫ π ≫ c ≫ sN)
  have : IsNormal W :=
    isNormal_of_isRegular W (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme hWs)
  have : IsProper g := hgp.isProper
  have hWp : MMP.Mori.IsProjectiveVariety ℂ (g ≫ π ≫ c ≫ sN) := by
    refine (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr ⟨hWv, ?_⟩
    exact (isProjective_iff_isProjectiveMorphism_of_isAffine _).mp
      (IsProjective.comp hgp hZ'p.isProjective)
  -- birationality of the composites
  have hgB := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hgb
  have hcB := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hcb
  have hB : ∀ {Y : Scheme.{0}} [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y] (u : N ⟶ Y)
      [IsProper u], IsBirationalMorphism u → IsBirationalMorphism (g ≫ π ≫ c ≫ u) := by
    intro Y _ _ _ u _ hu
    exact isBirationalMorphism_of_isBirational _ (hgB.comp (hπb.comp (hcB.comp
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hu))))
  have hB' : ∀ {Y : Scheme.{0}} [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y] (u : N' ⟶ Y)
      [IsProper u], IsBirationalMorphism u → IsBirationalMorphism (g ≫ π ≫ u) := by
    intro Y _ _ _ u _ hu
    exact isBirationalMorphism_of_isBirational _ (hgB.comp (hπb.comp
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hu)))
  have h1 : r₀ ≫ T.sX (i + 1) = c ≫ sN := by
    calc r₀ ≫ T.sX (i + 1) = r₀ ≫ T.fp i ≫ T.sZ i := by rw [hst.comp_eq_plus]
      _ = c ≫ q0 ≫ J.p ≫ T.f i ≫ T.sZ i := by
        rw [← Category.assoc r₀, ← hcr]; simp only [Category.assoc]
      _ = c ≫ q0 ≫ J.p ≫ T.sX i := by rw [hst.comp_eq_minus]
      _ = c ≫ sN := by rw [hq0s]
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, g ≫ π ≫ c ≫ sN,
    fun k => g ≫ π ≫ c ≫ q k, g ≫ π ≫ r₀, hWp, hWs, fun k => ?_, fun k => ?_, fun k hk => ?_,
    hB' r₀ hr₀b, by simp only [Category.assoc, h1], ?_⟩
  · have := hqp k
    have hVk : IsNormalVariety ℂ (modelStr (J.p ≫ T.sX i) P.sY k) :=
      (P.isQFactorial k (by omega)).1
    have : IsIntegral (modelSeq J.Y P.Y k) := hVk.1.toIsIntegral
    exact hB (q k) (hqb k)
  · simp only [Category.assoc, hqs]
  · rw [comp_assoc₅, hqc k hk]
    exact (comp_assoc₅ _ _ _ _ _).symm
  · calc (g ≫ π ≫ c ≫ q0) ≫ J.p ≫ T.f i = g ≫ π ≫ c ≫ q0 ≫ J.p ≫ T.f i := by
          simp only [Category.assoc]
      _ = g ≫ π ≫ r₀ ≫ T.fp i := by rw [hcr]
      _ = (g ≫ π ≫ r₀) ≫ T.fp i := by simp only [Category.assoc]

variable {P}

include P in
/-- The morphisms `q_k` commute with the maps `π_k` to `Z_i`. -/
private theorem comp_modelMap_eq {W : Scheme.{0}}
    {q : ∀ k : Fin (P.m + 1), W ⟶ modelSeq J.Y P.Y k}
    (hqc : ∀ (k : ℕ) (hk : k < P.m), q ⟨k, by omega⟩ ≫ P.g k = q ⟨k + 1, by omega⟩ ≫ P.gp k) :
    ∀ (k : ℕ) (hk : k ≤ P.m), q ⟨k, by omega⟩ ≫ modelMap (J.p ≫ T.f i) P.πY k =
      q ⟨0, by omega⟩ ≫ J.p ≫ T.f i
  | 0, _ => rfl
  | k + 1, hk => by
    calc q ⟨k + 1, by omega⟩ ≫ modelMap (J.p ≫ T.f i) P.πY (k + 1)
        = q ⟨k + 1, by omega⟩ ≫ (P.gp k ≫ P.h k) :=
          congrArg _ (P.modelMap_succ_eq (k := k) (by omega))
      _ = (q ⟨k + 1, by omega⟩ ≫ P.gp k) ≫ P.h k := (Category.assoc _ _ _).symm
      _ = (q ⟨k, by omega⟩ ≫ P.g k) ≫ P.h k := congrArg (· ≫ P.h k) (hqc k (by omega)).symm
      _ = q ⟨k, by omega⟩ ≫ (P.g k ≫ P.h k) := Category.assoc _ _ _
      _ = q ⟨k, by omega⟩ ≫ modelMap (J.p ≫ T.f i) P.πY k :=
        congrArg _ (P.modelMap_eq k (by omega)).symm
      _ = _ := comp_modelMap_eq hqc k (by omega)

/-- **Descending the programme.** A prime divisor `E` of `W` over a prime divisor `Q` of `V_k`
lies over a prime divisor `P₀` of `V_0 = Y_i`, and `K_k + Θ_k` has the same coefficient at `Q`
as `K + Θ_i'` at `P₀`. -/
private theorem exists_primeDivisor_zero_coeff_eq {W : Scheme.{0}}
    {q : ∀ k : Fin (P.m + 1), W ⟶ modelSeq J.Y P.Y k}
    (hqc : ∀ (k : ℕ) (hk : k < P.m), q ⟨k, by omega⟩ ≫ P.g k = q ⟨k + 1, by omega⟩ ≫ P.gp k)
    (E : MMP.Mori.PrimeDivisor W) :
    ∀ (k : ℕ) (hk : k ≤ P.m) (Q : MMP.Mori.PrimeDivisor (modelSeq J.Y P.Y k)),
      q ⟨k, by omega⟩ E.genericPoint = Q.genericPoint →
      ∃ P₀ : MMP.Mori.PrimeDivisor J.Y, q ⟨0, by omega⟩ E.genericPoint = P₀.genericPoint ∧
        (Divisor.toQDivisor (divisorSeq K P.KY k) + P.boundary k) Q =
          (Divisor.toQDivisor K + Θ') P₀
  | 0, _, Q, hQ => ⟨Q, hQ, rfl⟩
  | k + 1, hk, Q, hQ => by
    have hst := P.isThreefoldStepDiagram k (by omega)
    have : IsProper (P.g k) := isProper_of_isProjectiveMorphism _ hst.isProjectiveMorphism_minus
    obtain ⟨Pm, hx, hfl⟩ := exists_eq_genericPoint_flipTransform_apply
      hst.isBirationalMorphism_minus hst.isSmallMorphism_plus Q (q ⟨k, by omega⟩ E.genericPoint)
      (by
        calc (P.g k) (q ⟨k, by omega⟩ E.genericPoint)
            = (q ⟨k, by omega⟩ ≫ P.g k) E.genericPoint := rfl
          _ = (q ⟨k + 1, by omega⟩ ≫ P.gp k) E.genericPoint := by rw [hqc k (by omega)]
          _ = P.gp k (q ⟨k + 1, by omega⟩ E.genericPoint) := rfl
          _ = P.gp k Q.genericPoint := congrArg (fun x => P.gp k x) hQ)
    obtain ⟨P₀, h0, hc⟩ := exists_primeDivisor_zero_coeff_eq hqc E k (by omega) Pm hx
    refine ⟨P₀, h0, ?_⟩
    rw [← hc]
    change ((P.KY k Q : ℤ) : ℚ) + P.ΘY k Q = ((divisorSeq K P.KY k Pm : ℤ) : ℚ) +
      divisorSeq Θ' P.ΘY k Pm
    rw [P.KY_eq k (by omega), P.ΘY_eq k (by omega), hfl, hfl]

include P in
/-- **`F₁` is effective.** `q_0^*(K_0 + Θ_0) - q_j^*(K_j + Θ_j) ≥ 0` for every `j ≤ m`, as the
sum of the effective comparisons across the steps. -/
private theorem zero_le_pullback_sub_pullback_modelSeq {W : Scheme.{0}} [IsIntegral W]
    [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of ℂ)}
    (hW : MMP.Mori.IsProjectiveVariety ℂ sW) {q : ∀ k : Fin (P.m + 1), W ⟶ modelSeq J.Y P.Y k}
    (hq : ∀ k, IsBirationalMorphism (q k))
    (hqs : ∀ k, q k ≫ modelStr (J.p ≫ T.sX i) P.sY k = sW)
    (hqc : ∀ (k : ℕ) (hk : k < P.m), q ⟨k, by omega⟩ ≫ P.g k = q ⟨k + 1, by omega⟩ ≫ P.gp k)
    (hDq : ∀ (k : ℕ) (_ : k ≤ P.m),
      (Divisor.toQDivisor (divisorSeq K P.KY k) + P.boundary k).IsQCartier)
    (hgen : ∀ (k : Fin (P.m + 1)) (Z : irreducibleComponents W),
      q k (componentGenericPoint W Z) ∉
        (Divisor.toQDivisor (divisorSeq K P.KY k) + P.boundary k).supp) :
    ∀ (j : ℕ) (hj : j ≤ P.m),
      0 ≤ (Divisor.toQDivisor K + Θ').pullback (hDq 0 (Nat.zero_le _)) (hgen ⟨0, by omega⟩) -
        (Divisor.toQDivisor (divisorSeq K P.KY j) + P.boundary j).pullback (hDq j hj)
          (hgen ⟨j, by omega⟩)
  | 0, _ => sub_nonneg.mpr le_rfl
  | j + 1, hj => by
    have h1 := zero_le_pullback_sub_pullback_modelSeq hW hq hqs hqc hDq hgen j (by omega)
    have h2 : 0 ≤ (Divisor.toQDivisor (divisorSeq K P.KY j) + P.boundary j).pullback
          (hDq j (by omega)) (hgen ⟨j, by omega⟩) -
        (Divisor.toQDivisor (P.KY j) + P.ΘY j).pullback (hDq (j + 1) hj)
          (hgen ⟨j + 1, by omega⟩) :=
      zero_le_pullback_sub_pullback_of_isThreefoldStepDiagram
        (P.isThreefoldStepDiagram j (by omega)) (P.KY_eq j (by omega)) (P.ΘY_eq j (by omega)) hW
        (q ⟨j, by omega⟩) (q ⟨j + 1, by omega⟩) (hq _) (hq _) (hqs _) (hqs _)
        (hqc j (by omega)) _ _ _ _
    exact (add_nonneg h1 h2).trans_eq (sub_add_sub_cancel _ _ _)

end Programme

/-- **The nef end of a bridge programme maps crepantly to the next model.** Let `(p_i, Θ_i)` be a
crepant junction of `(X_i, B_i)` extracting `I_∞ = I(X_i, B_i)`, and let `Θ_i'` be its decreased
boundary. Let `P` be a finite relative threefold programme over `Z_i` (by `f_i ∘ p_i`) from
`(Y_i, Θ_i')`, run with the canonical divisor `K` of `Y_i` satisfying `(p_i)_* K = K_i`. Suppose
`K_{V_m} + Θ_m` is nef over `Z_i` at its end. Then there is a birational morphism
`p̂ : V_m ⟶ X_{i+1}` with `p̂ ≫ f_i⁺ = π_m` such that `K_{V_m} + Θ_m` is the pull-back
`p̂^*(K_{i+1} + B_{i+1})`. -/
@[mmp "lem_mmp_indexc_bridge_end_morphism"]
public theorem IsDecreasedBoundary.exists_comp_eq_modelMap_and_isPullback {T : StabilizedTail}
    {i : ℕ} {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (hI : (I : Set _) = lowDiscrepancySet (T.sX i) (T.B i))
    {J : CrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ') {K : Divisor J.Y}
    (hpK : RationalMap.transformDivisor (X := J.Y) J.p.toRationalMap K = T.K i)
    (P : RelativeThreefoldProgram (J.p ≫ T.sX i) (T.sZ i) (J.p ≫ T.f i) K Θ')
    (hnef : QDivisor.IsRelativelyNef (modelStr (J.p ≫ T.sX i) P.sY P.m)
      (modelMap (J.p ≫ T.f i) P.πY P.m)
      (Divisor.toQDivisor (divisorSeq K P.KY P.m) + P.boundary P.m)) :
    ∃ (p : modelSeq J.Y P.Y P.m ⟶ T.X (i + 1))
      (hp : ∀ Z : irreducibleComponents (modelSeq J.Y P.Y P.m),
        p (componentGenericPoint _ Z) ∉ (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).supp),
      IsBirationalMorphism p ∧
      p ≫ T.fp i = modelMap (J.p ≫ T.f i) P.πY P.m ∧
      (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).IsPullback p hp
        (Divisor.toQDivisor (divisorSeq K P.KY P.m) + P.boundary P.m) := by
  obtain ⟨W, _, _, _, _, sW, q, r, hW, hWs, hq, hqs, hqc, hr, hrs, hcomp⟩ := exists_model P
  have hX' := (T.isThreefoldStepDiagram i).isNormalVariety_plus
  have := isSeparated_toTerminal_of_isNormalVariety hX'
  have : IsProper sW := isProper_of_isProjectiveMorphism _ hW.isProjective
  have : IsProper r := @IsProper.of_comp _ _ _ r (T.sX (i + 1)) (hrs ▸ inferInstance)
    hX'.1.toIsSeparated
  have := fun k => (hq k).isDominant
  have := hr.isDominant
  have hDq : ∀ (k : ℕ) (hk : k ≤ P.m),
      (Divisor.toQDivisor (divisorSeq K P.KY k) + P.boundary k).IsQCartier :=
    fun k hk => isQCartier_of_isQFactorial _ (P.isQFactorial k hk) _
  have hD' : (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).IsQCartier :=
    isQCartier_of_isQFactorial _ (T.isQFactorial (i + 1)) _
  have hgen : ∀ (k : Fin (P.m + 1)) (Z : irreducibleComponents W), q k (componentGenericPoint W Z) ∉
      (Divisor.toQDivisor (divisorSeq K P.KY k) + P.boundary k).supp :=
    fun k => map_componentGenericPoint_notMem_supp_of_isDominant' (q k) _
  have hgen' : ∀ Z : irreducibleComponents W, r (componentGenericPoint W Z) ∉
      (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).supp :=
    map_componentGenericPoint_notMem_supp_of_isDominant' r _
  -- `F₁ = q_0^*(K_0 + Θ_0) - q_m^*(K_m + Θ_m)` is effective
  have hF₁ := zero_le_pullback_sub_pullback_modelSeq hW hq hqs hqc hDq hgen P.m le_rfl
  -- `F₁` is `q_m`-exceptional
  have hF₁e : ∀ (E : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor (modelSeq J.Y P.Y P.m)),
      q ⟨P.m, by omega⟩ E.genericPoint = Q.genericPoint →
      ((Divisor.toQDivisor K + Θ').pullback (hDq 0 (Nat.zero_le _)) (hgen ⟨0, by omega⟩) -
        (Divisor.toQDivisor (divisorSeq K P.KY P.m) + P.boundary P.m).pullback (hDq P.m le_rfl)
          (hgen ⟨P.m, by omega⟩)) E = 0 := by
    intro E Q hEQ
    obtain ⟨P₀, h0, hc⟩ := exists_primeDivisor_zero_coeff_eq hqc E P.m le_rfl Q hEQ
    have : IsIso (Scheme.Hom.stalkMap (X := W) (Y := J.Y) (q ⟨0, by omega⟩) E.genericPoint) :=
      isIso_stalkMap_of_map_eq_genericPoint (hq ⟨0, by omega⟩) h0
    have : IsIso ((q ⟨P.m, by omega⟩ : W ⟶ modelSeq J.Y P.Y P.m).stalkMap E.genericPoint) :=
      isIso_stalkMap_of_map_eq_genericPoint (hq ⟨P.m, by omega⟩) hEQ
    have c₀ := coeff_eq_of_isPullback_qDivisor E P₀ h0 (hDq 0 (Nat.zero_le _))
      (QDivisor.isPullback_pullback (hDq 0 (Nat.zero_le _)) (hgen ⟨0, by omega⟩))
    have cₘ := coeff_eq_of_isPullback_qDivisor E Q hEQ (hDq P.m le_rfl)
      (QDivisor.isPullback_pullback (hDq P.m le_rfl) (hgen ⟨P.m, by omega⟩))
    rw [Finsupp.sub_apply, sub_eq_zero]
    exact c₀.trans (hc.symm.trans cₘ.symm)
  -- `F₂ = q_0^*(K + Θ_i') - r^*(K_{i+1} + B_{i+1})` is effective and `r`-exceptional
  obtain ⟨hF₂, hF₂e⟩ :=
    IsDecreasedBoundary.zero_le_pullback_sub_pullback_and_transformDivisor_eq_zero hI hΘ' K
      P.isCanonicalDivisor hpK sW hW hWs (q ⟨0, by omega⟩) r (hq _) hr (hqs _) hrs hcomp
      (hDq 0 (Nat.zero_le _)) hD' (hgen ⟨0, by omega⟩) hgen'
  have hF₂e' := apply_eq_zero_of_transformDivisor_eq_zero r hr hF₂e
  -- the two ends
  have hπ : q ⟨P.m, by omega⟩ ≫ modelMap (J.p ≫ T.f i) P.πY P.m = r ≫ T.fp i :=
    (comp_modelMap_eq hqc P.m le_rfl).trans hcomp
  have hamp := (T.isThreefoldStepDiagram i).hasRelativelyAmpleMultiple_plus
  rw [← T.K_eq i, ← T.B_eq i] at hamp
  obtain ⟨p, hp, hqp, hpb⟩ :=
    exists_comp_eq_and_isPullback hW (isProjectiveVariety_modelStr P le_rfl)
    (T.isProjectiveVariety (i + 1)) (q ⟨P.m, by omega⟩) r (hq _) hr (hqs _) hrs
    (modelMap (J.p ≫ T.f i) P.πY P.m) (T.fp i) hπ (hDq P.m le_rfl) hD' hnef hamp
    (hgen ⟨P.m, by omega⟩) hgen' hF₁ hF₂ hF₁e hF₂e'
    (by rw [add_sub_cancel, add_sub_cancel])
  -- `q_m` is a contraction
  have hVm : IsNormalVariety ℂ (modelStr (J.p ≫ T.sX i) P.sY P.m) := (P.isQFactorial _ le_rfl).1
  set qm : W ⟶ modelSeq J.Y P.Y P.m := q ⟨P.m, by omega⟩ with hqm
  have hqms : qm ≫ modelStr (J.p ≫ T.sX i) P.sY P.m = sW := hqs _
  have : IsSeparated (modelStr (J.p ≫ T.sX i) P.sY P.m) := hVm.1.toIsSeparated
  have : IsProper (qm ≫ modelStr (J.p ≫ T.sX i) P.sY P.m) := by rw [hqms]; infer_instance
  have : IsProper qm := IsProper.of_comp qm (modelStr (J.p ≫ T.sX i) P.sY P.m)
  have hO := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism sW
    (modelStr (J.p ≫ T.sX i) P.sY P.m) hW.toIsVariety hVm qm (hq _)).1
  have : IsIso qm.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun U => hO U.unop
  refine ⟨p, hp, ?_, ?_, hpb⟩
  · -- `p̂` is birational
    have hps : p ≫ T.sX (i + 1) = modelStr (J.p ≫ T.sX i) P.sY P.m :=
      eq_of_comp_eq_of_isIso_c qm (by rw [← Category.assoc, hqp, hrs, hqms])
    have : IsSeparated (T.sX (i + 1)) := hX'.1.toIsSeparated
    have : IsProper (modelStr (J.p ≫ T.sX i) P.sY P.m) :=
      isProper_of_isProjectiveMorphism _ (isProjectiveVariety_modelStr P le_rfl).isProjective
    have : IsProper (p ≫ T.sX (i + 1)) := by rw [hps]; infer_instance
    have : IsProper p := IsProper.of_comp p (T.sX (i + 1))
    refine isBirationalMorphism_of_isBirational p (isBirational_of_isBirational_comp
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism (hq ⟨P.m, by omega⟩)) ?_)
    rw [hqp]
    exact MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hr
  · -- `f_i⁺ ∘ p̂ = π_m`
    exact eq_of_comp_eq_of_isIso_c qm (by rw [← Category.assoc, hqp, hπ])

/-! ## The nef end of a bridge programme is the next crepant junction -/

/-! ### Valuations transported along birational morphisms -/

section Transport

/-- Pulling valuations back along the function field map of a birational morphism is
injective. -/
private theorem comap_functionFieldMap_injective {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    {f : X ⟶ Y} [IsDominant f] (hf : IsBirationalMorphism f) :
    Function.Injective
      (Valuation.comap (Γ₀ := WithZero (Multiplicative ℤ)) (functionFieldMap f)) :=
  fun _ _ => eq_of_comap_eq_of_surjective hf.functionFieldMap_bijective.2

/-- Restriction of valuations along the function field map of a composite. -/
private theorem comap_functionFieldMap_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] (a : X ⟶ Y) (b : Y ⟶ Z) [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)]
    (v : Valuation X.functionField (WithZero (Multiplicative ℤ))) :
    v.comap (functionFieldMap (a ≫ b)) =
      (v.comap (functionFieldMap a)).comap (functionFieldMap b) :=
  Valuation.ext fun t => by
    simp only [Valuation.comap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- The valuation of a prime divisor seen through a morphism `a = g ≫ h`. -/
private theorem valuationOver_eq_comap_of_eq {X T Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral T] [IsIntegral Z]
    (P : MMP.Mori.PrimeDivisor X) {a : X ⟶ Z} {g : X ⟶ T} {h : T ⟶ Z} (hda : IsDominant a)
    (hg : IsDominant g) (hh : IsDominant h) (ha : a = g ≫ h) :
    P.valuationOver a = (P.valuationOver g).comap (functionFieldMap h) := by
  subst ha
  exact comap_functionFieldMap_comp g h P.divisorialValuation

/-- Two prime divisors with the same valuation over `T` (through `g` and `g⁺`) have the same
valuation over `Z` (through `a = g ≫ h` and `b = g⁺ ≫ h`). -/
private theorem valuationOver_eq_of_eq {Xm Xp T Z : Scheme.{0}} [IsIntegral Xm]
    [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    [IsIntegral T] [IsIntegral Z] {g : Xm ⟶ T} {gp : Xp ⟶ T} {h : T ⟶ Z}
    {a : Xm ⟶ Z} {b : Xp ⟶ Z} (hg : IsDominant g) (hgp : IsDominant gp) (hh : IsDominant h)
    (hda : IsDominant a) (hdb : IsDominant b) (ha : a = g ≫ h) (hb : b = gp ≫ h)
    {Pm : MMP.Mori.PrimeDivisor Xm} {Q : MMP.Mori.PrimeDivisor Xp}
    (hPm : Pm.valuationOver g = Q.valuationOver gp) :
    Pm.valuationOver a = Q.valuationOver b := by
  rw [valuationOver_eq_comap_of_eq Pm hda hg hh ha, valuationOver_eq_comap_of_eq Q hdb hgp hh hb,
    hPm]

end Transport

/-! ### Exceptional prime divisors and inverse transforms -/

section Exceptional

/-- The coefficient of `E_t` in `∑_s c_s E_s`, for an injective family `E` of prime divisors,
is `c_t`. -/
private theorem sum_single_apply_self {Y : Scheme.{0}} {ι : Type*} [Fintype ι]
    {E : ι → MMP.Mori.PrimeDivisor Y} (hE : Function.Injective E) (c : ι → ℚ) (t : ι) :
    (∑ s, Finsupp.single (E s) (c s) : QDivisor Y) (E t) = c t := by
  classical
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    exact Finsupp.single_eq_of_ne (hE.ne hb.symm)
  · simp

/-- The coefficient in `∑_s c_s E_s` of a prime divisor off the range of `E` is `0`. -/
private theorem sum_single_apply_of_notMem_range {Y : Scheme.{0}} {ι : Type*} [Fintype ι]
    {E : ι → MMP.Mori.PrimeDivisor Y} (c : ι → ℚ) {P : MMP.Mori.PrimeDivisor Y}
    (hP : P ∉ Set.range E) : (∑ s, Finsupp.single (E s) (c s) : QDivisor Y) P = 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun t _ => Finsupp.single_eq_of_ne fun h' => hP ⟨t, h'.symm⟩

/-- A prime divisor whose generic point maps to the generic point of a prime divisor is not
exceptional. -/
private theorem not_isExceptional_of_map_genericPoint_eq {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : Y ⟶ X} {E : MMP.Mori.PrimeDivisor Y} {Q : MMP.Mori.PrimeDivisor X}
    (h : f E.genericPoint = Q.genericPoint) :
    ¬ RationalMap.IsExceptional (X := Y) f.toRationalMap E := fun hE => by
  have h2 := two_le_coheight_of_isExceptional E hE
  rw [h, Q.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- The inverse transform `f⁻¹_* B` of a proper birational morphism onto a normal scheme has
coefficient `coeff_Q B` at a prime divisor `P` with `f(η_P) = η_Q`. -/
private theorem inverseTransformDivisor_apply_of_map_genericPoint_eq {X Y : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {R : Type*}
    [AddCommMonoid R] {f : X ⟶ Y} [IsProper f] (hf : IsBirationalMorphism f)
    {P : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (he : f P.genericPoint = Q.genericPoint) (B : DivisorWithCoeffs R Y) :
    inverseTransformDivisor f B P = B Q :=
  MMP.Fourfold.Oai4C1.inverseTransformDivisor_apply_of_map_genericPoint he
    (MMP.Fourfold.Oai4C1.genericPoint_mem_biregularLocus f hf Q) B

/-- The inverse transform `f⁻¹_* B` vanishes at an `f`-exceptional prime divisor. -/
private theorem inverseTransformDivisor_apply_eq_zero_of_isExceptional {X Y : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {R : Type*} [AddCommMonoid R] {f : X ⟶ Y} {E : MMP.Mori.PrimeDivisor X}
    (hE : RationalMap.IsExceptional (X := X) f.toRationalMap E) (B : DivisorWithCoeffs R Y) :
    inverseTransformDivisor f B E = 0 :=
  MMP.Fourfold.Oai4C1.mapPrimeDivisors_apply_eq_zero (fun _ hQ =>
    not_isExceptional_of_map_genericPoint_eq
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hQ).1 hE) B

end Exceptional

/-! ### Log discrepancies of valuations -/

section LogDiscrepancy

/-- A log discrepancy `a(ξ; X, B)` of a valuation is unique. -/
private theorem isValuationLogDiscrepancy_unique {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    {ξ : Valuation X.functionField (WithZero (Multiplicative ℤ))} {a a' : ℝ}
    (h : IsValuationLogDiscrepancy sX B ξ a) (h' : IsValuationLogDiscrepancy sX B ξ a') :
    a = a' := by
  obtain ⟨n, D, -, hD, ha⟩ := h
  obtain ⟨n', D', -, hD', ha'⟩ := h'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha ha' (hD.trans hD'.symm)

/-- The divisor `(X, 𝟙, P)` over `X` has valuation `ord_P`. -/
private theorem valuation_ofPrimeDivisor {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    (P : MMP.Mori.PrimeDivisor X) :
    (DivisorOver.ofPrimeDivisor ℂ hX P).valuation = P.divisorialValuation := by
  ext g
  change P.divisorialValuation (functionFieldMap (𝟙 X) g) = _
  rw [MMP.Mori.functionFieldMap_id_apply]

/-- The log discrepancy of `ord_Q` for a prime divisor `Q` of `X` is `1 - coeff_Q B`. -/
private theorem isValuationLogDiscrepancy_divisorialValuation {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    (hB : MMP.Mori.IsPair sX B) (Q : MMP.Mori.PrimeDivisor X) :
    IsValuationLogDiscrepancy sX B Q.divisorialValuation (1 - (B.coeff Q : ℝ)) := by
  obtain ⟨hX, n, K, hK, -⟩ := id hB
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB hK
    (DivisorOver.ofPrimeDivisor ℂ hX Q)
  have h1 := ha.eq_neg_coeff_of_ofPrimeDivisor hX
  have hp : IsProper (DivisorOver.ofPrimeDivisor ℂ hX Q).f := (inferInstance : IsProper (𝟙 X))
  refine ⟨n, DivisorOver.ofPrimeDivisor ℂ hX Q, hp, valuation_ofPrimeDivisor hX Q, ?_⟩
  · have h2 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha hp
    rw [h1] at h2
    convert h2 using 1
    push_cast
    ring

/-- The centre on `X` of a prime divisor `E` of a normal variety birational over `X` whose
valuation is `ord_Q` is the generic point of `Q`. -/
private theorem map_genericPoint_eq_of_divisorialValuation_eq {V X : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) {p : V ⟶ X}
    (hV : IsNormalVariety ℂ (p ≫ sX)) (hp : IsBirationalMorphism p) [IsDominant p]
    {E : MMP.Mori.PrimeDivisor V} {Q : MMP.Mori.PrimeDivisor X}
    (h : Q.divisorialValuation = E.valuationOver p) :
    p E.genericPoint = Q.genericPoint :=
  MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq (D := ⟨V, p, hV, hp, E⟩)
    (D' := DivisorOver.ofPrimeDivisor ℂ hX Q) hX.1
    (by rw [valuation_ofPrimeDivisor, h]; rfl)

end LogDiscrepancy

/-! ### The morphisms `π_k` of a relative programme -/

section Program

variable {V Z : Scheme.{0}} [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
  [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] {sV : V ⟶ Spec (.of ℂ)}
  {sZ : Z ⟶ Spec (.of ℂ)} {π : V ⟶ Z} {K : Divisor V} {Θ : QDivisor V}
  (P : RelativeThreefoldProgram sV sZ π K Θ)

omit [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] in
/-- Each `π_k : V_k ⟶ Z` is a morphism over `ℂ`. -/
private theorem modelMap_comp_eq : ∀ k ≤ P.m, modelMap π P.πY k ≫ sZ = modelStr sV P.sY k
  | 0, _ => P.comp_eq
  | k + 1, hk => by
    change P.πY k ≫ _ = P.sY k
    rw [P.πY_eq k hk, Category.assoc, P.comp_eq_base k hk,
      (P.isThreefoldStepDiagram k hk).comp_eq_plus]

omit [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] in
/-- Each `π_k`, `k ≤ m`, is proper when the models are projective. -/
private theorem isProper_modelMap [IsSeparated sZ]
    (hproj : ∀ k ≤ P.m, MMP.Mori.IsProjectiveVariety ℂ (modelStr sV P.sY k)) {k : ℕ}
    (hk : k ≤ P.m) : IsProper (modelMap π P.πY k) :=
  have : IsProper (modelMap π P.πY k ≫ sZ) := by
    rw [modelMap_comp_eq P k hk]; exact isProper_of_isProjectiveMorphism _ (hproj k hk).isProjective
  IsProper.of_comp _ sZ

omit [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] in
/-- Each `π_k`, `k ≤ m`, is birational when `π` is. -/
private theorem isBirational_modelMap (hπ : IsBirational π) :
    ∀ k ≤ P.m, IsBirational (modelMap π P.πY k)
  | 0, _ => hπ
  | k + 1, hk => by
    have hD := P.isThreefoldStepDiagram k hk
    have : IsIntegral (P.T k) := hD.isNormalVariety_target.1.toIsIntegral
    rw [P.modelMap_succ_eq hk]
    refine (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
      hD.isSmallMorphism_plus.isBirationalMorphism).comp (isBirational_of_isBirational_comp
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hD.isBirationalMorphism_minus)
        ?_)
    rw [← P.modelMap_eq k hk]
    exact isBirational_modelMap hπ k (Nat.le_of_succ_le hk)

/-- Each `π_k`, `k ≤ m`, is a birational morphism when `π` is birational and the models are
projective. -/
private theorem isBirationalMorphism_modelMap [IsSeparated sZ]
    (hproj : ∀ k ≤ P.m, MMP.Mori.IsProjectiveVariety ℂ (modelStr sV P.sY k))
    (hπ : IsBirational π) {k : ℕ} (hk : k ≤ P.m) : IsBirationalMorphism (modelMap π P.πY k) := by
  have := isProper_modelMap P hproj hk
  simpa using MMP.Mori.isBirationalMorphism_comp_of_isBirational (𝟙 Z) (modelMap π P.πY k)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
      (isBirationalMorphism_of_isIso _)) (isBirational_modelMap P hπ k hk)

/-- **Strict transforms along small steps keep valuations over the base.** If every contraction
`g_k` of a relative programme over `Z` is small and `e k` sends a prime divisor `Γ` of `V` to its
strict transform on `V_k`, then `e k Γ` and `Γ` define the same valuation of `k(Z)`. -/
private theorem valuationOver_modelMap [IsSeparated sZ] [IsDominant π]
    (hproj : ∀ k ≤ P.m, MMP.Mori.IsProjectiveVariety ℂ (modelStr sV P.sY k))
    (hπ : IsBirational π)
    (hsmall : ∀ k < P.m, IsSmallMorphism (modelStr sV P.sY k) (P.sT k) (P.g k))
    (e : ∀ k ≤ P.m, MMP.Mori.PrimeDivisor V → MMP.Mori.PrimeDivisor (modelSeq V P.Y k))
    (he0 : ∀ Γ, e 0 (Nat.zero_le _) Γ = Γ)
    (hstep : ∀ (k : ℕ) (hk : k < P.m) (Γ : MMP.Mori.PrimeDivisor V),
      flipTransformPrimeDivisor (P.g k) (P.gp k) (e k hk.le Γ) = some (e (k + 1) hk Γ))
    {k : ℕ} (hk : k ≤ P.m) (Γ : MMP.Mori.PrimeDivisor V) :
    have := (isBirationalMorphism_modelMap P hproj hπ hk).isDominant
    (e k hk Γ).valuationOver (modelMap π P.πY k) = Γ.valuationOver π := by
  induction k with
  | zero => rw [he0]; rfl
  | succ k ih =>
    have hk' : k < P.m := hk
    have hD := P.isThreefoldStepDiagram k hk'
    have : IsIntegral (P.T k) := hD.isNormalVariety_target.1.toIsIntegral
    have hdk := (isBirationalMorphism_modelMap P hproj hπ hk'.le).isDominant
    have : IsDominant (P.g k ≫ P.h k) := P.modelMap_eq k hk' ▸ hdk
    obtain ⟨-, e', he'⟩ := hD.isExceptionalValuation_iff_of_isSmallMorphism (hsmall k hk')
    obtain ⟨h1, h2, -⟩ := he' (e k hk'.le Γ)
    rw [← ih hk'.le]
    refine (valuationOver_eq_of_eq hD.isBirationalMorphism_minus.isDominant
      hD.isSmallMorphism_plus.isBirationalMorphism.isDominant (IsDominant.of_comp (P.g k) (P.h k))
      hdk (isBirationalMorphism_modelMap P hproj hπ hk).isDominant (P.modelMap_eq k hk')
      (P.modelMap_succ_eq hk') ?_).symm
    rw [Option.some.inj ((hstep k hk' Γ).symm.trans h1)]
    exact h2.symm

end Program

/-- **The nef end of a bridge programme is the next crepant junction.** In the setting of
`MMP.Fourfold.StabilizedTail.IsDecreasedBoundary.exists_comp_eq_modelMap_and_isPullback`, let
`p̂ : V_m ⟶ X_{i+1}` be a birational morphism with `p̂ ≫ f_i⁺ = π_m` and
`K_{V_m} + Θ_m = p̂^*(K_{i+1} + B_{i+1})`. Then for every finite set `I'` with
`I' = I(X_{i+1}, B_{i+1})`, `(p̂, Θ_m)` is a crepant junction of `(X_{i+1}, B_{i+1})` extracting
`I'`. That is, there are a crepant junction `J'` and an isomorphism `e : V_m ≅ J'.Y` with
`e ≫ J'.p = p̂` and `Θ_m = e⁻¹_* J'.Θ`. -/
@[mmp "lem_mmp_indexc_bridge_end_junction"]
public theorem IsDecreasedBoundary.exists_crepantJunction_of_isPullback {T : StabilizedTail}
    {i : ℕ} {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (hI : (I : Set _) = lowDiscrepancySet (T.sX i) (T.B i))
    {J : CrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ') {K : Divisor J.Y}
    (_hpK : RationalMap.transformDivisor (X := J.Y) J.p.toRationalMap K = T.K i)
    (P : RelativeThreefoldProgram (J.p ≫ T.sX i) (T.sZ i) (J.p ≫ T.f i) K Θ')
    (_hnef : QDivisor.IsRelativelyNef (modelStr (J.p ≫ T.sX i) P.sY P.m)
      (modelMap (J.p ≫ T.f i) P.πY P.m)
      (Divisor.toQDivisor (divisorSeq K P.KY P.m) + P.boundary P.m))
    (p : modelSeq J.Y P.Y P.m ⟶ T.X (i + 1))
    (hp : ∀ Z : irreducibleComponents (modelSeq J.Y P.Y P.m),
      p (componentGenericPoint _ Z) ∉ (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).supp)
    (hpb : IsBirationalMorphism p)
    (hcomp : p ≫ T.fp i = modelMap (J.p ≫ T.f i) P.πY P.m)
    (_hpull : (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).IsPullback p hp
      (Divisor.toQDivisor (divisorSeq K P.KY P.m) + P.boundary P.m))
    {I' : Finset (Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ)))}
    (hI' : (I' : Set _) = lowDiscrepancySet (T.sX (i + 1)) (T.B (i + 1))) :
    ∃ (J' : CrepantJunction (T.sX (i + 1)) (T.B (i + 1)) I')
      (e : modelSeq J.Y P.Y P.m ≅ J'.Y),
      e.hom ≫ J'.p = p ∧ P.boundary P.m = inverseTransformDivisor e.hom J'.Θ := by
  obtain ⟨hsmall, e, he0, hstep, hcoeff, hmodel⟩ :=
    IsDecreasedBoundary.isSmallMorphism_relativeThreefoldProgram hI hΘ' P
  -- the `i`-th step of the tail and its base `Z_i`
  have hT := T.isThreefoldStepDiagram i
  have hZ : IsNormalVariety ℂ (T.sZ i) := hT.isNormalVariety_target
  have : IsIntegral (T.Z i) := hZ.1.toIsIntegral
  have : IsSeparated (T.sZ i) := hT.isProjectiveVariety_target.1.toIsSeparated
  have : IsNormal (T.Z i) := hZ.2
  have : LocallyOfFiniteType (T.sZ i) := hZ.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian (T.Z i) := LocallyOfFiniteType.isLocallyNoetherian (T.sZ i)
  have hfb : IsBirationalMorphism (T.f i) := hT.isBirationalMorphism_minus
  have hfpb : IsBirationalMorphism (T.fp i) := hT.isSmallMorphism_plus.isBirationalMorphism
  have := hfb.isDominant
  have := hfpb.isDominant
  have := J.isBirationalMorphism.isDominant
  have := hpb.isDominant
  have hX1 : IsNormalVariety ℂ (T.sX (i + 1)) := (T.isKltPair (i + 1)).1.isPair.1
  -- the morphisms `π_k : V_k ⟶ Z_i`, the end `V_m` and the morphism `p̂`
  have hproj := fun k hk => (hmodel k hk).1
  have hπ : IsBirational (J.p ≫ T.f i) :=
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism J.isBirationalMorphism).comp
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb)
  have hm : P.m ≤ P.m := le_rfl
  have := (isBirationalMorphism_modelMap P hproj hπ hm).isDominant
  have hsV : p ≫ T.sX (i + 1) = modelStr (J.p ≫ T.sX i) P.sY P.m := by
    rw [← hT.comp_eq_plus, ← Category.assoc, hcomp, modelMap_comp_eq P P.m hm]
  have hVn : IsNormalVariety ℂ (p ≫ T.sX (i + 1)) := hsV ▸ (P.isQFactorial P.m hm).1
  have hpproj : IsProjectiveMorphism p :=
    isProjectiveMorphism_of_isProjectiveVariety (hmodel P.m hm).1 (T.isProjectiveVariety (i + 1))
      p hsV
  have : IsProper p := isProper_of_isProjectiveMorphism p hpproj
  -- the trace of a prime divisor of `Y_i` on `V_m` and on `X_{i+1}`
  have hfact : ∀ Γ : MMP.Mori.PrimeDivisor J.Y,
      ((e P.m hm Γ).valuationOver p).comap (functionFieldMap (T.fp i)) =
          (Γ.valuationOver J.p).comap (functionFieldMap (T.f i)) ∧
        IsValuationLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1)) ((e P.m hm Γ).valuationOver p)
          (1 - ((P.boundary P.m).coeff (e P.m hm Γ) : ℝ)) ∧
        (¬ RationalMap.IsExceptional (X := J.Y) J.p.toRationalMap Γ →
          ∃ Q' : MMP.Mori.PrimeDivisor (T.X (i + 1)),
            Q'.divisorialValuation = (e P.m hm Γ).valuationOver p) := by
    intro Γ
    have h1 : ((e P.m hm Γ).valuationOver p).comap (functionFieldMap (T.fp i)) =
        (Γ.valuationOver J.p).comap (functionFieldMap (T.f i)) := by
      rw [← valuationOver_eq_comap_of_eq _ inferInstance hpb.isDominant hfpb.isDominant
        hcomp.symm, valuationOver_modelMap P hproj hπ hsmall (fun k hk => e k hk) he0 hstep hm Γ]
      exact valuationOver_eq_comap_of_eq Γ inferInstance J.isBirationalMorphism.isDominant
        hfb.isDominant rfl
    obtain ⟨s', hs', hlog, hne⟩ :=
      IsDecreasedBoundary.isValuationLogDiscrepancy_one_sub_coeff hI hΘ' Γ
    obtain rfl : s' = (e P.m hm Γ).valuationOver p :=
      comap_functionFieldMap_injective hfpb (hs'.trans h1.symm)
    exact ⟨h1, hcoeff P.m hm Γ ▸ hlog, hne⟩
  -- the labels of `I` and of `I'` correspond
  have hlow := T.lowDiscrepancySet_eq i
  have hmatch : ∀ t : I', ∃ s : I,
      (s : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))).comap
        (functionFieldMap (T.f i)) =
      (t : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))).comap
        (functionFieldMap (T.fp i)) := by
    intro t
    have ht : (t : Valuation _ _) ∈ lowDiscrepancySet (T.sX (i + 1)) (T.B (i + 1)) := by
      rw [← hI']; exact t.2
    have : (t : Valuation _ _).comap (functionFieldMap (T.fp i)) ∈
        valuationsOver (T.f i) (lowDiscrepancySet (T.sX i) (T.B i)) := by
      rw [hlow]; exact ⟨_, ht, rfl⟩
    obtain ⟨s, hs, hst⟩ := this
    rw [← hI] at hs
    exact ⟨⟨s, hs⟩, hst⟩
  have hmatch' : ∀ s : I, ∃ t : I',
      (t : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))).comap
        (functionFieldMap (T.fp i)) =
      (s : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))).comap
        (functionFieldMap (T.f i)) := by
    intro s
    have hs : (s : Valuation _ _) ∈ lowDiscrepancySet (T.sX i) (T.B i) := by
      rw [← hI]; exact s.2
    have : (s : Valuation _ _).comap (functionFieldMap (T.f i)) ∈
        valuationsOver (T.fp i) (lowDiscrepancySet (T.sX (i + 1)) (T.B (i + 1))) := by
      rw [← hlow]; exact ⟨_, hs, rfl⟩
    obtain ⟨t, ht, hts⟩ := this
    rw [← hI'] at ht
    exact ⟨⟨t, ht⟩, hts⟩
  -- the centres `c_{V_m}(t)` of the labels `t ∈ I'`
  have hvalE : ∀ (s : I) (t : I'),
      (t : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))).comap
          (functionFieldMap (T.fp i)) =
        (s : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))).comap
          (functionFieldMap (T.f i)) →
      (e P.m hm (J.E s)).valuationOver p = t := by
    intro s t hts
    have h := (hfact (J.E s)).1
    rw [show (J.E s).valuationOver J.p = s from J.valuation_eq s] at h
    exact comap_functionFieldMap_injective hfpb (h.trans hts.symm)
  have hsinj : ∀ s₁ s₂ : I,
      (s₁ : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))).comap
          (functionFieldMap (T.f i)) =
        (s₂ : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))).comap
          (functionFieldMap (T.f i)) → s₁ = s₂ :=
    fun s₁ s₂ h => Subtype.ext (comap_functionFieldMap_injective hfb h)
  choose sOf hsOf using hmatch
  obtain ⟨E', hE'def⟩ : ∃ E' : I' → MMP.Mori.PrimeDivisor (modelSeq J.Y P.Y P.m),
      ∀ t, E' t = e P.m hm (J.E (sOf t)) := ⟨_, fun _ => rfl⟩
  have hE'v : ∀ t : I', (E' t).valuationOver p = t := fun t => by
    rw [hE'def]; exact hvalE _ _ (hsOf t).symm
  have hE'inj : Function.Injective E' := fun t₁ t₂ h =>
    Subtype.ext (by simpa only [hE'v] using congrArg (fun Q => Q.valuationOver p) h)
  -- exceptional prime divisors of `p̂`
  have hnotexc : ∀ Γ : MMP.Mori.PrimeDivisor J.Y,
      ¬ RationalMap.IsExceptional (X := J.Y) J.p.toRationalMap Γ →
        ¬ RationalMap.IsExceptional (X := modelSeq J.Y P.Y P.m) p.toRationalMap (e P.m hm Γ) := by
    intro Γ hΓ
    obtain ⟨Q', hQ'⟩ := (hfact Γ).2.2 hΓ
    exact not_isExceptional_of_map_genericPoint_eq
      (map_genericPoint_eq_of_divisorialValuation_eq hX1 hVn hpb hQ')
  have hexcE : ∀ s : I,
      RationalMap.IsExceptional (X := modelSeq J.Y P.Y P.m) p.toRationalMap (e P.m hm (J.E s)) := by
    intro s
    by_contra h
    obtain ⟨t, ht⟩ := hmatch' s
    have hv := hvalE s t ht
    obtain ⟨P', hP'⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional
      hX1 ⟨_, p, hVn, hpb, e P.m hm (J.E s)⟩ h
    have htlow : (t : Valuation _ _) ∈ lowDiscrepancySet (T.sX (i + 1)) (T.B (i + 1)) := by
      rw [← hI']; exact t.2
    obtain ⟨⟨D₁, -, hD₁v, hD₁c⟩, -⟩ := htlow
    exact (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX1 D₁).mp hD₁c P'
      (hD₁v.symm.trans (hv.symm.trans hP'))
  have hrange : ∀ Q : MMP.Mori.PrimeDivisor (modelSeq J.Y P.Y P.m),
      RationalMap.IsExceptional (X := modelSeq J.Y P.Y P.m) p.toRationalMap Q ↔
        Q ∈ Set.range E' := by
    intro Q
    obtain ⟨Γ, rfl⟩ := (e P.m hm).surjective Q
    constructor
    · intro hQ
      by_cases hΓ : RationalMap.IsExceptional (X := J.Y) J.p.toRationalMap Γ
      · obtain ⟨s, rfl⟩ := (J.isExceptional_iff Γ).mp hΓ
        obtain ⟨t, ht⟩ := hmatch' s
        exact ⟨t, by rw [hE'def, hsinj (sOf t) s ((hsOf t).trans ht)]⟩
      · exact absurd hQ (hnotexc Γ hΓ)
    · rintro ⟨t, ht⟩
      rw [← ht, hE'def]
      exact hexcE (sOf t)
  -- the boundary `Θ_m`
  have hΘeq : ∃ a : I' → ℚ,
      (∀ t : I', IsValuationLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1)) t (a t)) ∧
      P.boundary P.m = inverseTransformDivisor p (T.B (i + 1)) +
        ∑ t : I', Finsupp.single (E' t) (1 - a t) := by
    refine ⟨fun t => 1 - (P.boundary P.m).coeff (E' t), fun t => ?_, ?_⟩
    · have h := (hfact (J.E (sOf t))).2.1
      rw [← hE'def, hE'v t] at h
      push_cast
      exact h
    · refine Finsupp.ext fun Q => ?_
      rw [Finsupp.add_apply]
      obtain ⟨Γ, rfl⟩ := (e P.m hm).surjective Q
      by_cases hΓ : RationalMap.IsExceptional (X := J.Y) J.p.toRationalMap Γ
      · obtain ⟨s, rfl⟩ := (J.isExceptional_iff Γ).mp hΓ
        obtain ⟨t, ht⟩ := hmatch' s
        have hQ : e P.m hm (J.E s) = E' t := by
          rw [hE'def, hsinj (sOf t) s ((hsOf t).trans ht)]
        have hzero : inverseTransformDivisor p (T.B (i + 1)) (E' t) = 0 :=
          inverseTransformDivisor_apply_eq_zero_of_isExceptional ((hrange _).mpr ⟨t, rfl⟩) _
        rw [hQ, hzero, zero_add, sum_single_apply_self hE'inj]
        change _ = 1 - (1 - (P.boundary P.m).coeff (E' t))
        rw [sub_sub_cancel]
        rfl
      · have hnot : e P.m hm Γ ∉ Set.range E' := fun h => hnotexc Γ hΓ ((hrange _).mpr h)
        rw [sum_single_apply_of_notMem_range _ hnot, add_zero]
        obtain ⟨Q', hQ'⟩ := (hfact Γ).2.2 hΓ
        rw [inverseTransformDivisor_apply_of_map_genericPoint_eq hpb
          (map_genericPoint_eq_of_divisorialValuation_eq hX1 hVn hpb hQ')]
        have h2 := isValuationLogDiscrepancy_divisorialValuation (T.isKltPair (i + 1)).1.isPair Q'
        rw [hQ'] at h2
        have h3 := isValuationLogDiscrepancy_unique (hfact Γ).2.1 h2
        exact_mod_cast (by linarith :
          ((P.boundary P.m).coeff (e P.m hm Γ) : ℝ) = ((T.B (i + 1)).coeff Q' : ℝ))
  refine ⟨{ Y := modelSeq J.Y P.Y P.m
            p := p
            E := E'
            Θ := P.boundary P.m
            isProjectiveVariety_base := T.isProjectiveVariety (i + 1)
            dim_base := T.dim_eq (i + 1)
            isKltPair := T.isKltPair (i + 1)
            subset_lowDiscrepancySet := hI'.le
            isProjectiveVariety := by rw [hsV]; exact (hmodel P.m hm).1
            isQFactorial := by rw [hsV]; exact P.isQFactorial P.m hm
            dim_eq := (hmodel P.m hm).2.1
            isProjectiveMorphism := hpproj
            isBirationalMorphism := hpb
            valuation_eq := hE'v
            injective := hE'inj
            isExceptional_iff := hrange
            Θ_eq := hΘeq }, Iso.refl _, Category.id_comp _, (inverseTransformDivisor_id _).symm⟩

end StabilizedTail

end MMP.Fourfold
