module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltModification
public import MMP.AlgebraicGeometry.MMP.Contraction.DltRelativeContractionExists
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip.DltFlip
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.ElementaryDltTermination
public import MMP.AlgebraicGeometry.MMP.Contraction.DltStepPreserved
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConvexGeography
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
public import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonCommonBase
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import MMP.AlgebraicGeometry.Resolution.SncPairStratumBlowup
public import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
public import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltNegativeFace
public import MMP.AlgebraicGeometry.Intersection.N1CartierCoordinates
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeInAbsolute
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.AmpleStrictlyPositive
public import MMP.AlgebraicGeometry.MMP.Contraction.ExceptionalDivisorNegativeOnRay
public import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
public import MMP.AlgebraicGeometry.MMP.Flip.SmallAmpleModel
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
public import MMP.AlgebraicGeometry.Morphisms.HProjective

/-!
# Log minimal models of projective lc fourfolds over a birational base

Let `(X, B)` be an effective rational log canonical pair on a normal projective complex fourfold
and `f : X ⟶ Z` a projective birational morphism onto a normal projective variety. Then
`(X/Z, B)` has a log minimal model `(M/Z, B_M)` in the sense of Birkar, and `M` is a projective
variety; by definition, `(M, B_M)` is `ℚ`-factorial and dlt.

## Main results

* `MMP.Fourfold.IsLogCanonicalPair.exists_isLogMinimalModel_of_isBirationalMorphism`.

## Implementation notes

The log minimal model is `MMP.Fourfold.IsLogMinimalModel`, which already contains the
`ℚ`-factoriality and the dlt property of `(M, B_M)`, the projectivity of `M ⟶ Z`, and the
condition that `B_M` is the birational transform of `B` plus the reduced exceptional divisor.
The projectivity of `M` over `ℂ` is stated as a separate conclusion.

## References

* [C. Birkar, *Existence of log canonical flips and a special LMMP*][BirkarLC], Section 2
-/

@[expose] public section

section

open CategoryTheory MMP.Fourfold MMP.Mori
open AlgebraicGeometry hiding PrimeDivisor

namespace Proof_thm_fourfold_projective_lc_birational_log_model

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

/-! ### Models over the base -/

/-- A model over `Z`: a normal integral scheme `U` over `ℂ` with a canonical divisor `K`, a
boundary `Δ` and a morphism `h : U ⟶ Z`. -/
private structure Stage (Z : Scheme.{0}) where
  U : Scheme.{0}
  [isIntegral : IsIntegral U]
  [compactSpace : CompactSpace U]
  [isLocallyNoetherian : IsLocallyNoetherian U]
  [isNormal : IsNormal U]
  sU : U ⟶ Spec (.of ℂ)
  [locallyOfFiniteType : LocallyOfFiniteType sU]
  [quasiCompact : QuasiCompact sU]
  K : Divisor U
  Δ : QDivisor U
  h : U ⟶ Z

attribute [local instance] Stage.isIntegral Stage.compactSpace Stage.isLocallyNoetherian
  Stage.isNormal Stage.locallyOfFiniteType Stage.quasiCompact

section Good

variable {X Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Z]
  (sZ : Z ⟶ Spec (.of ℂ)) (B : QDivisor X) (f : X ⟶ Z) [IsDominant f]

/-- The invariants of a model `S` of the program over `Z`, relative to `(X, B)`: `S` is a
projective `ℚ`-factorial dlt fourfold, birational and projective over `Z`, whose boundary
coefficients and discrepancies are those dictated by `(X, B)` through the valuations of
`k(Z)`. -/
private structure Stage.Good (S : Stage Z) : Prop where
  pair : IsProjectiveQFactorialDltPair S.sU S.K S.Δ
  canonical : S.K.IsCanonicalDivisor S.sU 4
  comp : S.h ≫ sZ = S.sU
  proj : IsProjectiveMorphism S.h
  bir : IsBirationalMorphism S.h
  coeff_eq : haveI := bir.isDominant
    ∀ (F : PrimeDivisor S.U) (D : PrimeDivisor X), F.valuationOver S.h = D.valuationOver f →
      S.Δ.coeff F = B.coeff D
  coeff_one : haveI := bir.isDominant
    ∀ F : PrimeDivisor S.U, (∀ D : PrimeDivisor X, F.valuationOver S.h ≠ D.valuationOver f) →
      S.Δ.coeff F = 1
  discrep : haveI := bir.isDominant
    ∀ (D : PrimeDivisor X) (E : DivisorOver ℂ S.sU), IsProper E.f →
      E.valuation.comap (functionFieldMap S.h) = D.valuationOver f → ∀ c : ℚ,
      IsDiscrepancy S.sU 4 S.K S.Δ E c →
        -B.coeff D ≤ c ∧
          ((∀ F : PrimeDivisor S.U, F.valuationOver S.h ≠ D.valuationOver f) → -B.coeff D < c)

end Good

/-! ### Transforms of prime divisors through valuations -/

section CenterTransform

/-- A scheme separated over a field is separated. -/
private theorem isSeparated_terminal_from {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- Reading a valuation of `k(U)` in `k(W)` along `h = ψ ≫ g` is reading it in `k(V)` along `ψ`
and then in `k(W)` along `g`. -/
private theorem comap_functionFieldMap_of_comp_eq {U V W : Scheme.{u}} [IsIntegral U]
    [IsIntegral V] [IsIntegral W] {ψ : U ⟶ V} {g : V ⟶ W} {h : U ⟶ W} [IsDominant ψ]
    [IsDominant g] [IsDominant h] (e : ψ ≫ g = h) {Γ : Type*} [LinearOrderedCommMonoidWithZero Γ]
    (v : Valuation U.functionField Γ) :
    v.comap (functionFieldMap h) = (v.comap (functionFieldMap ψ)).comap (functionFieldMap g) := by
  ext t
  simp only [Valuation.comap_apply, MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply ψ g e]

/-- The valuation of a prime divisor along `h = ψ ≫ g` is its valuation along `ψ` read through
`g`. -/
private theorem valuationOver_of_comp_eq {U V W : Scheme.{u}} [IsIntegral U]
    [IsLocallyNoetherian U] [IsNormal U] [IsIntegral V] [IsIntegral W] (F : PrimeDivisor U)
    {ψ : U ⟶ V} {g : V ⟶ W} {h : U ⟶ W} [IsDominant ψ] [IsDominant g] [IsDominant h]
    (e : ψ ≫ g = h) :
    F.valuationOver h = (F.valuationOver ψ).comap (functionFieldMap g) :=
  comap_functionFieldMap_of_comp_eq e F.divisorialValuation

/-- If a representative `g'` of `φ` sends the generic point of `P` to that of `E`, the strict
transform of `P` under `φ` is `E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq' {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : MMP.Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [MMP.Flips.coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [MMP.Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

set_option backward.isDefEq.respectTransparency.types false in
/-- The closed point of `Spec 𝒪_{W,x}` maps to `g(x)` under a partial map `g` defined at `x`. -/
private theorem fromSpecStalkOfMem_closedPoint {W Y : Scheme.{u}} (g : W.PartialMap Y) {x : W}
    (hx : x ∈ g.domain) :
    g.fromSpecStalkOfMem hx (IsLocalRing.closedPoint (W.presheaf.stalk x)) = g.hom ⟨x, hx⟩ := by
  change g.hom (g.domain.fromSpecStalkOfMem x hx (IsLocalRing.closedPoint _)) = _
  congr 1
  apply g.domain.ι.isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.fromSpecStalk_closedPoint]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- At a point `x` of the domain of a partial map `g : W ⇢ Y` inducing `θ : k(Y) → k(W)` at the
generic point, `θ` restricted to the local ring of `Y` at the image of `x` is the local map to
`𝒪_{W,x}` followed by `𝒪_{W,x} → k(W)`. -/
private theorem stalkClosedPointTo_comp_stalkSpecializes_eq {W Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral Y] (g : W.PartialMap Y) (θ : Y.functionField →+* W.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = g.fromFunctionField)
    {x : W} (hx : x ∈ g.domain) :
    Scheme.stalkClosedPointTo (g.fromSpecStalkOfMem hx) ≫
        W.presheaf.stalkSpecializes (genericPoint_specializes x) =
      Y.presheaf.stalkSpecializes (genericPoint_specializes _) ≫ CommRingCat.ofHom θ := by
  have hη : genericPoint W ∈ g.domain :=
    (genericPoint_specializes _).mem_open g.domain.2 g.dense_domain.nonempty.choose_spec
  apply Spec.map_injective
  rw [← cancel_mono (Y.fromSpecStalk _)]
  have h2 : Spec.map (W.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫
      g.domain.fromSpecStalkOfMem x hx = g.domain.fromSpecStalkOfMem (genericPoint W) hη := by
    rw [← cancel_mono g.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, Spec.map_comp,
    Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  refine Eq.trans ?_ hθ.symm
  change Spec.map _ ≫ g.domain.fromSpecStalkOfMem x hx ≫ g.hom = _
  rw [← Category.assoc, h2]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- **The valuation of a prime divisor dominates the local ring at its image.** If a partial map
`g : W ⇢ Y` induces `θ : k(Y) → k(W)` and is defined at the generic point of a prime divisor `P`
of `W`, then `ord_P ∘ θ` is at most one on `𝒪_{Y, g(η_P)}` and less than one on its maximal
ideal. -/
private theorem divisorialValuation_comap_dominates {W Y : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [IsIntegral Y] (g : W.PartialMap Y)
    (θ : Y.functionField →+* W.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = g.fromFunctionField)
    (P : MMP.Mori.PrimeDivisor W) (hP : P.genericPoint ∈ g.domain) :
    (∀ a : Y.presheaf.stalk (g.hom ⟨P.genericPoint, hP⟩),
      (P.divisorialValuation.comap θ) (algebraMap _ Y.functionField a) ≤ 1) ∧
    ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (g.hom ⟨P.genericPoint, hP⟩)),
      (P.divisorialValuation.comap θ) (algebraMap _ Y.functionField a) < 1 := by
  have key := stalkClosedPointTo_comp_stalkSpecializes_eq g θ hθ hP
  have hval : ∀ a : Y.presheaf.stalk
      (g.fromSpecStalkOfMem hP (IsLocalRing.closedPoint (W.presheaf.stalk P.genericPoint))),
      θ (algebraMap _ Y.functionField a) = algebraMap P.localRing W.functionField
        ((Scheme.stalkClosedPointTo (g.fromSpecStalkOfMem hP)).hom a) := fun a => by
    have := congrArg (fun φ => φ.hom a) key
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this.symm
  have hdom : (∀ a : Y.presheaf.stalk
      (g.fromSpecStalkOfMem hP (IsLocalRing.closedPoint (W.presheaf.stalk P.genericPoint))),
      (P.divisorialValuation.comap θ) (algebraMap _ Y.functionField a) ≤ 1) ∧
    ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk
      (g.fromSpecStalkOfMem hP (IsLocalRing.closedPoint (W.presheaf.stalk P.genericPoint)))),
      (P.divisorialValuation.comap θ) (algebraMap _ Y.functionField a) < 1 := by
    refine ⟨fun a => ?_, fun a ha => ?_⟩
    · rw [Valuation.comap_apply, hval, MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
      exact ⟨_, rfl⟩
    · rw [Valuation.comap_apply, hval]
      refine (P.divisorialValuation_algebraMap_lt_one_iff _).2 ?_
      exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)
  rw [fromSpecStalkOfMem_closedPoint g hP] at hdom
  exact hdom

/-- **Transforms of prime divisors through valuations.** Let `ψ : W ⤏ Y` be a rational map of
normal integral schemes, `Y` separated over a field, inducing the surjection
`θ : k(Y) → k(W)` at the generic point, and defined at the generic point of a prime divisor `P` of
`W`. Then `ψ_* P = G` if and only if `ord_P ∘ θ = ord_G`: both say that `ord_P ∘ θ` dominates
`𝒪_{Y, η_G}`. -/
private theorem transformPrimeDivisor_eq_some_iff_comap_eq {k : Type u} [Field k]
    {W Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsSeparated sY]
    (ψ : W.RationalMap Y) (θ : Y.functionField →+* W.functionField)
    (hθs : Function.Surjective θ)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = ψ.fromFunctionField)
    (P : MMP.Mori.PrimeDivisor W) (hP : P.genericPoint ∈ ψ.domain) (G : MMP.Mori.PrimeDivisor Y) :
    RationalMap.transformPrimeDivisor ψ P = some G ↔
      P.divisorialValuation.comap θ = G.divisorialValuation := by
  have := isSeparated_terminal_from sY
  obtain ⟨g, hgP, hg⟩ := Scheme.RationalMap.mem_domain.mp hP
  have hθg : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) =
      g.fromFunctionField := by
    rw [hθ, ← hg, Scheme.RationalMap.fromFunctionField_toRationalMap]
  obtain ⟨hD1, hD2⟩ := divisorialValuation_comap_dominates g θ hθg P hgP
  haveI := G.isDiscreteValuationRing_localRing
  have hG1 : ∀ a : G.localRing, G.divisorialValuation (algebraMap _ Y.functionField a) ≤ 1 :=
    fun a => (MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff _ _).2 ⟨a, rfl⟩
  have hG2 : ∀ a ∈ IsLocalRing.maximalIdeal G.localRing,
      G.divisorialValuation (algebraMap _ Y.functionField a) < 1 :=
    fun a ha => (G.divisorialValuation_algebraMap_lt_one_iff a).2 ha
  constructor
  · intro h
    have hy : G.genericPoint = g.hom ⟨P.genericPoint, hgP⟩ :=
      MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h g hg hgP
    haveI := P.isDiscreteValuationRing_localRing
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
    obtain ⟨ϖ', hϖ'⟩ := hθs (algebraMap P.localRing W.functionField ϖ)
    obtain ⟨ϖG, hϖG⟩ := IsDiscreteValuationRing.exists_irreducible G.localRing
    rw [← hy] at hD1 hD2
    refine MMP.Positivity.DivisorOver.valuation_eq_of_isDiscreteValuationRing (R := G.localRing)
      (fun r => hD1 r) (fun r hr => hD2 r hr) ⟨ϖ', ?_⟩ hG1 hG2
      ⟨_, G.divisorialValuation_algebraMap_of_irreducible hϖG⟩
    · rw [Valuation.comap_apply, hϖ', P.divisorialValuation_algebraMap_of_irreducible hϖ]
  · intro h
    refine transformPrimeDivisor_eq_some_of_genericPoint_eq' g hg hgP ?_
    rw [h] at hD1 hD2
    exact MMP.Positivity.DivisorOver.eq_of_dominates sY G.divisorialValuation hG1 hG2 hD1 hD2

/-- Two morphisms `Spec R ⟶ U` from a local ring, one of which sends the closed point to the
generic point of `U`, agree once composed with a separated birational morphism `h : U ⟶ Z`: both
factor through `Spec k(U)`, and `k(Z) ≅ k(U)`. -/
private theorem eq_of_comp_eq_of_isBirationalMorphism {U Z : Scheme.{u}} [IsIntegral U]
    [IsIntegral Z] {h : U ⟶ Z} [IsSeparated h] (hh : IsBirationalMorphism h) {R : CommRingCat}
    [IsLocalRing R] {a b : Spec R ⟶ U} (hb : b (IsLocalRing.closedPoint R) = genericPoint U)
    (hab : a ≫ h = b ≫ h) : a = b := by
  haveI := hh.isDominant
  have hbij := hh.functionFieldMap_bijective
  have hη : h (genericPoint U) = genericPoint Z := map_genericPoint_of_isDominant h
  have ha : a (IsLocalRing.closedPoint R) = genericPoint U := by
    have h1 : h (a (IsLocalRing.closedPoint R)) = h (b (IsLocalRing.closedPoint R)) :=
      congrArg (fun g : Spec R ⟶ Z => g.base (IsLocalRing.closedPoint R)) hab
    rw [hb, hη] at h1
    exact MMP.Fourfold.eq_of_map_eq_of_valuationRing hbij h1 hη
  have key : ∀ c : Spec R ⟶ U, c (IsLocalRing.closedPoint R) = genericPoint U →
      ∃ γ : U.presheaf.stalk (genericPoint U) ⟶ R,
        c = Spec.map γ ≫ U.fromSpecStalk (genericPoint U) := by
    intro c hc
    have hsp : c (IsLocalRing.closedPoint R) ⤳ genericPoint U := hc ▸ specializes_rfl
    refine ⟨U.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo c, ?_⟩
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  obtain ⟨α, rfl⟩ := key a ha
  obtain ⟨β, rfl⟩ := key b hb
  have e : ∀ γ : U.presheaf.stalk (genericPoint U) ⟶ R,
      (Spec.map γ ≫ U.fromSpecStalk (genericPoint U)) ≫ h =
        Spec.map (CommRingCat.ofHom (functionFieldMap h) ≫ γ) ≫
          Z.fromSpecStalk (genericPoint Z) := by
    intro γ
    rw [Spec.map_comp, Category.assoc, Category.assoc, functionFieldMap_fromSpecStalk]
  rw [e, e] at hab
  have h2 := Spec.map_injective ((cancel_mono _).mp hab)
  have hαβ : α = β := by
    ext x
    obtain ⟨y, rfl⟩ := hbij.2 x
    exact congrArg (fun φ => φ.hom y) h2
  rw [hαβ]

/-- **The birational map of two birational models over `Z`.** For birational morphisms
`f : X ⟶ Z` and `h : U ⟶ Z` of integral schemes, `h` separated, there is a birational map
`φ : X ⤏ U` over `Z`, induced at the generic point by the isomorphism
`θ = f^* ∘ (h^*)⁻¹ : k(U) ≅ k(X)`. -/
private theorem exists_isBirational_compHom_eq_fromFunctionField {X U Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral U] [IsIntegral Z] {f : X ⟶ Z} {h : U ⟶ Z} [IsSeparated h]
    (hf : IsBirationalMorphism f) (hh : IsBirationalMorphism h) :
    haveI := hf.isDominant
    haveI := hh.isDominant
    ∃ (φ : X.RationalMap U) (θ : U.functionField →+* X.functionField),
      RationalMap.IsBirational φ ∧ φ.compHom h = f.toRationalMap ∧ Function.Surjective θ ∧
        θ.comp (functionFieldMap h) = functionFieldMap f ∧
        Spec.map (CommRingCat.ofHom θ) ≫ U.fromSpecStalk (genericPoint U) = φ.fromFunctionField := by
  haveI := hf.isDominant
  haveI := hh.isDominant
  obtain ⟨eX, heX⟩ := MMP.Fourfold.Oai4C1.CommonModel.exists_partialIso_isOver hf
  obtain ⟨eh, heh⟩ := MMP.Fourfold.Oai4C1.CommonModel.exists_partialIso_isOver hh
  set e := eX.trans eh.symm
  have he : e.IsOver f h := heX.trans heh.symm
  have hφ := MMP.Fourfold.Oai4C1.CommonModel.compHom_toRationalMap_of_isOver e he
  let ef := RingEquiv.ofBijective (functionFieldMap f) hf.functionFieldMap_bijective
  let eh' := RingEquiv.ofBijective (functionFieldMap h) hh.functionFieldMap_bijective
  let θ : U.functionField →+* X.functionField := ef.toRingHom.comp eh'.symm.toRingHom
  have hθh : θ.comp (functionFieldMap h) = functionFieldMap f := by
    ext t
    change ef (eh'.symm (eh' t)) = functionFieldMap f t
    rw [RingEquiv.symm_apply_apply]
    rfl
  refine ⟨e.toRationalMap, θ, ⟨e, rfl⟩, hφ, ef.surjective.comp eh'.symm.surjective, hθh, ?_⟩
  symm
  refine eq_of_comp_eq_of_isBirationalMorphism hh ?_ ?_
  · have hpt : (Spec.map (CommRingCat.ofHom θ)) (IsLocalRing.closedPoint X.functionField) =
        IsLocalRing.closedPoint U.functionField :=
      IsLocalRing.comap_closedPoint (CommRingCat.ofHom θ).hom
    change U.fromSpecStalk _ ((Spec.map (CommRingCat.ofHom θ))
      (IsLocalRing.closedPoint X.functionField)) = _
    rw [hpt, Scheme.fromSpecStalk_closedPoint]
  · rw [← MMP.Flips.RationalMap.fromFunctionField_compHom, hφ,
      MMP.Flips.RationalMap.fromFunctionField_hom, ← functionFieldMap_fromSpecStalk f,
      Category.assoc, ← functionFieldMap_fromSpecStalk h, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hθh]

/-- **Transforms of prime divisors through valuations of the base.** For the birational map
`φ : X ⤏ U` over `Z` induced by `θ`, with `h : U ⟶ Z` proper, `φ_* D = F` if and only if `ord_D`
and `ord_F` are the same valuation of `k(Z)`. -/
private theorem transformPrimeDivisor_eq_some_iff_valuationOver_eq {k : Type u} [Field k]
    {X U Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral U]
    [IsLocallyNoetherian U] [IsNormal U] [IsIntegral Z] {sU : U ⟶ Spec (.of k)} [IsSeparated sU]
    {f : X ⟶ Z} {h : U ⟶ Z} [IsProper h] [IsDominant f] [IsDominant h]
    (hh : Function.Surjective (functionFieldMap h)) {φ : X.RationalMap U}
    {θ : U.functionField →+* X.functionField} (hφ : φ.compHom h = f.toRationalMap)
    (hθs : Function.Surjective θ) (hθh : θ.comp (functionFieldMap h) = functionFieldMap f)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ U.fromSpecStalk (genericPoint U) = φ.fromFunctionField)
    (D : PrimeDivisor X) (F : PrimeDivisor U) :
    RationalMap.transformPrimeDivisor φ D = some F ↔ D.valuationOver f = F.valuationOver h := by
  have hD : D.genericPoint ∈ φ.domain :=
    MMP.Flips.RationalMap.mem_domain_of_coheight_le_one f h φ hφ D.coheight_genericPoint.le
  rw [transformPrimeDivisor_eq_some_iff_comap_eq (sY := sU) φ θ hθs hθ D hD F]
  have e : D.valuationOver f = (D.divisorialValuation.comap θ).comap (functionFieldMap h) := by
    ext t
    rw [PrimeDivisor.valuationOver_apply, Valuation.comap_apply, Valuation.comap_apply, ← hθh]
    rfl
  constructor
  · intro h1
    rw [e, h1]
    rfl
  · intro h1
    rw [e] at h1
    exact MMP.Fourfold.Oai4C1.valuation_eq_of_comap_eq hh h1

/-- A prime divisor of a normal variety is determined by its valuation read in `k(B)` through a
dominant morphism inducing a surjection of function fields. -/
private theorem primeDivisor_eq_of_valuationOver_eq {k : Type u} [Field k] {Y B : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral B] {sY : Y ⟶ Spec (.of k)}
    (hY : IsNormalVariety k sY) (f : Y ⟶ B) [IsDominant f]
    (hf : Function.Surjective (functionFieldMap f)) {P P' : PrimeDivisor Y}
    (h : P.valuationOver f = P'.valuationOver f) : P = P' := by
  have hv : P.divisorialValuation = P'.divisorialValuation :=
    MMP.Fourfold.Oai4C1.valuation_eq_of_comap_eq hf h
  have := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1
    (D := DivisorOver.ofPrimeDivisor k hY P)
    (D' := DivisorOver.ofPrimeDivisor k hY P') (by
      change P.divisorialValuation.comap _ = P'.divisorialValuation.comap _
      rw [hv]
      rfl)
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective this

/-- A prime divisor with a strict transform is not exceptional. -/
private theorem not_isExceptional_of_transformPrimeDivisor_eq_some {X U : Scheme.{u}}
    {φ : X.RationalMap U} {D : PrimeDivisor X} {F : PrimeDivisor U}
    (h : RationalMap.transformPrimeDivisor φ D = some F) : ¬ RationalMap.IsExceptional φ D := by
  rw [RationalMap.isExceptional_iff]
  intro hex
  have h2 := hex (RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  have hsupp := RationalMap.support_transformPrimeDivisor h
  have hF : F.genericPoint ∈ (RationalMap.transform φ D.idealSheaf.support : Set U) := by
    rw [← hsupp, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h2 _ hF
  rw [F.coheight_genericPoint] at this
  exact absurd this (by decide)

/-- An inverse of a birational map over `Z` is a map over `Z`. -/
private theorem compHom_eq_of_isInverse {X U Z : Scheme.{u}} [IsReduced X] [IsReduced U]
    [IsSeparated (Z ↘ ⊤_ Scheme)] [IsSeparated (X ↘ ⊤_ Scheme)] {f : X ⟶ Z} {h : U ⟶ Z}
    {φ : X.RationalMap U} {ψ : U.RationalMap X} (hφ : φ.compHom h = f.toRationalMap)
    (hψ : RationalMap.IsInverse φ ψ) : ψ.compHom f = h.toRationalMap := by
  obtain ⟨e, he, rfl⟩ := hψ
  have h1 : (e.toPartialMap.compHom h).toRationalMap = f.toPartialMap.toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap]
    change e.toRationalMap.compHom h = _
    rw [he, hφ]
  have h2 := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h1)
  have hover : e.IsOver f h := (Category.assoc _ _ _).symm.trans h2
  exact MMP.Fourfold.Oai4C1.CommonModel.compHom_toRationalMap_of_isOver e.symm hover.symm

/-- The log discrepancy of a prime divisor `D` of `X` with respect to a pair `(X, B)` is
`1 - coeff_D(B)`. -/
private theorem eq_of_isLogDiscrepancy_ofPrimeDivisor {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {B : QDivisor X} (hP : MMP.Mori.IsPair sX B)
    (hX : IsNormalVariety k sX) {n : ℕ} {D : PrimeDivisor X} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B)
      (DivisorOver.ofPrimeDivisor k hX D) a) : a = 1 - B.coeff D := by
  obtain ⟨-, -, -, -, ⟨K, hK, -⟩, -⟩ := id ha
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK
    (DivisorOver.ofPrimeDivisor k hX D)
  rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha,
    IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX hc]
  push_cast
  ring

/-- A divisor `E` over `M` realizing a prime divisor `D` of `X` through a map `ψ : M ⤏ X` over
`Z` induces the valuation `ord_D` of `k(Z)`. -/
private theorem valuation_comap_eq_of_isRealizedOver {k : Type u} [Field k] {X M Z : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral M] [IsIntegral Z]
    [Z.IsSeparated] [IsSeparated (Z ↘ ⊤_ Scheme)] {sM : M ⟶ Spec (.of k)} {f : X ⟶ Z}
    {h : M ⟶ Z} [IsDominant f] [IsDominant h] {ψ : M.RationalMap X}
    (hψ : ψ.compHom f = h.toRationalMap) {D : PrimeDivisor X}
    {E : MMP.Flips.ProperDivisorOver k sM} (hE : MMP.Flips.IsRealizedOver sM ψ D E) :
    E.valuation.comap (functionFieldMap h) = D.valuationOver f := by
  obtain ⟨g, p, hp, hg, hcomm, hv⟩ := hE
  haveI := E.toDivisorOver.isIntegral
  haveI := E.toDivisorOver.isNormal
  haveI := E.toDivisorOver.isLocallyNoetherian
  haveI := E.toDivisorOver.isDominant
  haveI := hp.isDominant
  have hgf : g.hom ≫ f = g.domain.ι ≫ h := by
    have h1 : (g.compHom f).toRationalMap = h.toPartialMap.toRationalMap := by
      rw [Scheme.RationalMap.compHom_toRationalMap, hg, hψ]
    exact (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp h1)
  have hne : ((E.f ⁻¹ᵁ g.domain : E.Y.Opens) : Set E.Y).Nonempty := by
    refine ⟨genericPoint E.Y, ?_⟩
    change E.f (genericPoint E.Y) ∈ g.domain
    rw [map_genericPoint_of_isDominant]
    exact (genericPoint_specializes _).mem_open g.domain.2 g.dense_domain.nonempty.choose_spec
  haveI : IsDominant (E.f ⁻¹ᵁ g.domain).ι := by
    rw [isDominant_iff, DenseRange, Scheme.Opens.range_ι]
    exact (E.f ⁻¹ᵁ g.domain).2.dense hne
  have hpe : p ≫ f = E.f ≫ h := by
    refine ext_of_isDominant (E.f ⁻¹ᵁ g.domain).ι ?_
    rw [← Category.assoc, hcomm, Category.assoc, hgf, ← Category.assoc, morphismRestrict_ι,
      Category.assoc]
  haveI : IsDominant (p ≫ f) := inferInstance
  ext t
  rw [Valuation.comap_apply, PrimeDivisor.valuationOver_apply]
  change E.E.divisorialValuation (functionFieldMap E.f (functionFieldMap h t)) = _
  rw [MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply E.f h hpe.symm,
    ← MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply p f rfl, ← Valuation.comap_apply, hv]

end CenterTransform

/-! ### Strict transforms under the inverse of a birational morphism -/

section InverseTransform

variable {X Y : Scheme.{u}}

private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- If `e` is a partial isomorphism representing a morphism `f : Y ⟶ X` and `g'` a partial map
representing `e⁻¹`, then `f ∘ g'` is the identity where `g'` is defined. -/
private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{u}} [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- If the strict transform of a prime divisor `P` of `X` under the inverse of a birational
morphism `f : Y ⟶ X` is `E`, then `f` sends the generic point of `E` to that of `P`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some [IsReduced X] [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : Y ⟶ X}
    (hf : IsBirationalMorphism f) {P : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor (MMP.Mori.RationalMap.IsBirational.inverse hf) P =
      some E) :
    f E.genericPoint = P.genericPoint := by
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  obtain ⟨g', hP, hg'⟩ :=
    MMP.Mori.RationalMap.definedAt_iff.mp (MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hP]
  exact apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP

private theorem isSeparated_terminal_of_isVariety {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX) : IsSeparated (X ↘ ⊤_ Scheme) :=
  have : IsSeparated sX := hX.toIsSeparated
  isSeparated_terminal_from sX

/-- The coefficient of `μ⁻¹_* D` along a prime divisor `E` lying over no prime divisor of `X`
vanishes. -/
private theorem coeff_birationalInverseTransform_eq_zero {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {R : Type*} [AddCommMonoid R]
    (hX : MMP.Mori.IsVariety k sX) {μ : Y ⟶ X} (hY : MMP.Mori.IsVariety k (μ ≫ sX))
    (hμ : IsBirationalMorphism μ) (D : DivisorWithCoeffs R X) {E : MMP.Mori.PrimeDivisor Y}
    (h : ∀ P : MMP.Mori.PrimeDivisor X, μ E.genericPoint ≠ P.genericPoint) :
    MMP.Flips.birationalInverseTransform μ hμ D E = 0 := by
  have : IsIntegral X := hX.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have := isSeparated_terminal_of_isVariety hX
  have := isSeparated_terminal_of_isVariety hY
  exact MMP.Fourfold.Oai4C1.mapPrimeDivisors_apply_eq_zero (fun P hP =>
    h P (genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hμ hP)) D

/-- A discrepancy `a(E, X, Δ)` of a divisor `(Y, f, E)` over `X` whose centre is the generic point
of a prime divisor `P` of `X` is `-coeff_P(Δ)`. -/
private theorem eq_neg_coeff_of_map_genericPoint_eq {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (hX : MMP.Mori.IsNormalVariety k sX)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : MMP.Mori.DivisorOver k sX}
    {P : MMP.Mori.PrimeDivisor X} (hP : D.f D.E.genericPoint = P.genericPoint) {a : ℚ}
    (h : MMP.Mori.IsDiscrepancy sX n K Δ D a) : a = -Δ.coeff P := by
  obtain ⟨hX', hK, m, hm, hC, U, hU, τ, hτ, hτa⟩ := h
  refine MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX (P := P)
    ⟨hX', hK, m, hm, hC, U, ?_, τ, hτ, ?_⟩
  · convert hU using 2
    exact hP.symm
  · rw [hτa, MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX
      hK.topologicalKrullDim_eq
      (MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hX D P hP)]

/-- A prime divisor `F` of `Y` contained in the exceptional locus of a proper birational morphism
`μ : Y ⟶ X` of varieties onto a normal variety does not lie over a prime divisor `P` of `X`: if
`μ(η_F) = η_P`, the fibre over `η_P` is the single point `η_F` (`𝒪_{X,P}` is a discrete
valuation ring dominated by the local rings of its preimages), so `μ` is an isomorphism over a
neighbourhood of `η_P`, and an open immersion near `η_F`. -/
private theorem map_genericPoint_ne_of_subset_exceptionalLocus {Y X : Scheme.{0}}
    [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) {μ : Y ⟶ X}
    [IsProper μ] (hY : MMP.Mori.IsVariety ℂ (μ ≫ sX)) (hμ : IsBirationalMorphism μ)
    {F : MMP.Mori.PrimeDivisor Y} (hF : F.support ⊆ MMP.Intersection.exceptionalLocus μ)
    (P : MMP.Mori.PrimeDivisor X) : μ F.genericPoint ≠ P.genericPoint := by
  intro h
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsNormal X := hX.2
  have : IsDominant μ := hμ.isDominant
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (μ ≫ sX) := hY.toIsSeparated
  have : IsSeparated μ := IsSeparated.of_comp μ sX
  have hbij := hμ.functionFieldMap_bijective
  have := P.isDiscreteValuationRing_localRing
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso μ
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hμ)).1 inferInstance
  let V : X.Opens := ⟨_, hU⟩
  have hPV : P.genericPoint ∈ V := by
    change (μ ⁻¹' {P.genericPoint}).Finite
    refine Set.Subsingleton.finite fun a ha b hb => ?_
    have ha' : μ a = P.genericPoint := ha
    have hb' : μ b = P.genericPoint := hb
    have : ValuationRing (X.presheaf.stalk (μ a)) := by rw [ha']; infer_instance
    have : ValuationRing (X.presheaf.stalk (μ b)) := by rw [hb']; infer_instance
    have := MMP.Positivity.isIso_stalkMap_of_valuationRing μ hbij a
    have := MMP.Positivity.isIso_stalkMap_of_valuationRing μ hbij b
    exact MMP.Positivity.eq_of_isIso_stalkMap μ hbij (hb'.trans ha'.symm)
  have hW : IsOpenImmersion ((μ ⁻¹ᵁ V).ι ≫ μ) := by
    have : IsIso (μ ∣_ V) := hiso
    rw [← morphismRestrict_ι]
    infer_instance
  have hη : F.genericPoint ∈ F.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  exact MMP.Intersection.mem_exceptionalLocus_iff.mp (hF hη) (μ ⁻¹ᵁ V)
    (show μ F.genericPoint ∈ V by rw [h]; exact hPV) hW

/-- The birational transform `μ⁻¹_* D` of a divisor under the inverse of a birational morphism
`μ` has no `μ`-exceptional component. -/
private theorem coeff_birationalInverseTransform_eq_zero_of_subset {Y X : Scheme.{0}}
    [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) {μ : Y ⟶ X}
    [IsProper μ] (hY : MMP.Mori.IsVariety ℂ (μ ≫ sX)) (hμ : IsBirationalMorphism μ)
    (D : QDivisor X) (F : MMP.Mori.PrimeDivisor Y)
    (hF : F.support ⊆ MMP.Intersection.exceptionalLocus μ) :
    (MMP.Flips.birationalInverseTransform μ hμ D).coeff F = 0 :=
  coeff_birationalInverseTransform_eq_zero hX.1 hY hμ D
    (map_genericPoint_ne_of_subset_exceptionalLocus hX hY hμ hF)

/-- The valuation of a prime divisor `D`, regarded as the divisor `(X, 𝟙_X, D)` over `X`, is
`ord_D`. -/
private theorem valuation_ofPrimeDivisor {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (D : PrimeDivisor X) : (DivisorOver.ofPrimeDivisor k hX D).valuation = D.divisorialValuation := by
  ext t
  change D.divisorialValuation (functionFieldMap (𝟙 X) t) = _
  rw [MMP.Mori.functionFieldMap_id_apply]

end InverseTransform

/-! ### A negative extremal ray of the relative cone -/

section Ray

/-- The value of `z ↦ (D · z)` on the class of a curve is the degree of the associated
`ℚ`-Cartier divisor on that curve. -/
private theorem curveForm_numericalClass_eq_sum {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [QuasiCompact sX] (D : QDivisor X) (h : D.IsQCartier) (C : ProperCurve sX) :
    MMP.Fourfold.QDivisor.curveForm sX D h (OneCycle.numericalClass sX (C.cycle ℝ)) =
      (D.associatedCartier h).sum fun E c =>
        (c : ℝ) * ((E : Divisor X).degreeOn k sX C.ι C.dim_le E.2 : ℝ) := by
  simp only [MMP.Fourfold.QDivisor.curveForm, Finsupp.sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [LinearMap.smul_apply, NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle,
    smul_eq_mul]
  rfl

/-- On `N₁(X/S)` the curve form is the absolute one composed with the natural map
`N₁(X/S) → N₁(X)`. -/
private theorem relativeCurveForm_eq_comp {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [QuasiCompact sX] {S : Scheme.{0}} (f : X ⟶ S) (D : QDivisor X) (h : D.IsQCartier) :
    QDivisor.relativeCurveForm sX f D h =
      QDivisor.curveForm sX D h ∘ₗ relativeToAbsolute sX f := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun Z => ?_)
  simp only [QDivisor.relativeCurveForm, QDivisor.curveForm, Finsupp.sum, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun _ _ => rfl

/-- The natural map `N₁(X/S) → N₁(X)` is injective. -/
private theorem relativeToAbsolute_injective {k : Type} [Field k] {X S : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (f : X ⟶ S) : Function.Injective (relativeToAbsolute sX f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (mem_relativeNumericallyTrivial.mpr ((Submodule.Quotient.mk_eq_zero _).mp hz))

/-- A projective variety carries a Cartier divisor whose invertible sheaf is ample. -/
private theorem exists_isAmple_sheaf {k : Type*} [Field k] {X : Scheme} {sX : X ⟶ Spec (.of k)}
    [h : AlgebraicGeometry.IsProjectiveVariety k sX] :
    ∃ D : X.CartierDivisor, Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf D) := by
  obtain ⟨⟨L, hL, hrel, hA⟩, -⟩ :=
    MMP.Foundations.IsProjective.exists_isRelativelyAmple h.isProjective.isProjective
  obtain ⟨A, ⟨e⟩⟩ := hA h.toIsIntegral
  exact ⟨A, (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr
    (Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sX L hrel)⟩

/-- **Coordinates for the relative cone.** The natural map `N₁(X/S) → N₁(X)` followed by a
Cartier coordinate system `N₁(X) ≃ ℝ^ι` is an injective linear map `j` carrying `NE̅(X/S)` onto a
closed cone of `ℝ^ι`, on which some linear form (an ample divisor) is positive off `0`. -/
private theorem exists_coordinates_relativeClosedConeOfCurves {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X S : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    [MMP.Mori.IsProjectiveVariety k sX] [MMP.Mori.IsProjectiveVariety k sS] (f : X ⟶ S)
    (hf : f ≫ sS = sX) :
    ∃ (ι : Type) (_ : Fintype ι) (Φ : NumericalCurveClasses sX ≃L[ℝ] (ι → ℝ))
      (A : (ι → ℝ) →ₗ[ℝ] ℝ),
      Function.Injective (Φ.toLinearMap ∘ₗ relativeToAbsolute sX f) ∧
      IsCone ℝ ((Φ.toLinearMap ∘ₗ relativeToAbsolute sX f) ''
        (relativeClosedConeOfCurves sX f : Set _)) ∧
      IsClosed ((Φ.toLinearMap ∘ₗ relativeToAbsolute sX f) ''
        (relativeClosedConeOfCurves sX f : Set _)) ∧
      ∀ z ∈ (Φ.toLinearMap ∘ₗ relativeToAbsolute sX f) ''
        (relativeClosedConeOfCurves sX f : Set _), z ≠ 0 → 0 < A z := by
  obtain ⟨hfd, -, hext, hcoord, -⟩ :=
    NumericalCurveClasses.exists_cartier_coordinates_of_isProperVariety sX
  obtain ⟨t, -, ht, htspan⟩ := hext ∅ (linearIndepOn_empty _ _)
  rw [Set.image_eq_range] at htspan
  obtain ⟨⟨Φ, -⟩, -⟩ := hcoord (fun E : t => (E : X.CartierDivisor)) ht htspan
  haveI := hfd
  haveI : Fintype t := @Fintype.ofFinite _ ht.finite
  set ι := relativeToAbsolute sX f
  set j := Φ.toLinearMap ∘ₗ ι
  have hNimg := image_relativeClosedConeOfCurves_eq_inter_range sX sS f hf
  obtain ⟨H, hH⟩ := exists_isAmple_sheaf (sX := sX)
  set Aform := NumericalCurveClasses.intersectionNumber (sX := sX) (KCartierDivisor.ofCartier ℝ H)
  refine ⟨t, inferInstance, Φ, Aform ∘ₗ Φ.symm.toLinearMap,
    Φ.injective.comp (relativeToAbsolute_injective sX f), ?_, ?_, ?_⟩
  · exact isCone_coe ((relativeClosedConeOfCurves sX f).map j)
  · rw [show (j : _ → _) = Φ ∘ ι from rfl, Set.image_comp, hNimg, Set.image_inter Φ.injective,
      ← Set.range_comp]
    refine (Φ.toHomeomorph.isClosedMap _ isClosed_closure).inter ?_
    rw [show (Φ ∘ ι) = (j : _ → _) from rfl, ← LinearMap.coe_range]
    exact (LinearMap.range j).closed_of_finiteDimensional
  · rintro _ ⟨w, hw, rfl⟩ hw0
    have hιw : ι w ∈ closedConeOfCurves sX := (hNimg.subset ⟨w, hw, rfl⟩).1
    obtain ⟨Z, hZ⟩ := OneCycle.numericalClass_surjective sX (ι w)
    change 0 < Aform (Φ.symm (Φ (ι w)))
    rw [Φ.symm_apply_apply, ← hZ, NumericalCurveClasses.intersectionNumber_numericalClass]
    exact closedConeOfCurves_diff_zero_subset_posHalfspace sX H hH
      ⟨hιw, fun h => hw0 (by simp [j, Set.mem_singleton_iff.mp h])⟩ Z hZ

/-- The preimage of an extremal ray of `j(N)` under an injective linear map `j` is an extremal
ray of `N`. -/
private theorem isExtremalRay_preimage {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {N : Set V} {R' : Set W} {j : V →ₗ[ℝ] W}
    (hj : Function.Injective j) (hR' : IsExtremalRay ℝ (j '' N) R') :
    IsExtremalRay ℝ N (j ⁻¹' R') := by
  obtain ⟨⟨hsub, ⟨h0, hs⟩, hadd, hext⟩, v, hv0, hRv⟩ := hR'
  have hmem : ∀ x, j x ∈ R' → x ∈ N := fun x hx => by
    obtain ⟨y, hy, hyx⟩ := hsub hx
    rwa [← hj hyx]
  have hvR : v ∈ R' := by rw [hRv]; exact ⟨1, zero_le_one, one_smul _ _⟩
  obtain ⟨v₀, -, rfl⟩ := hsub hvR
  refine ⟨⟨fun x hx => hmem x hx, ⟨by simpa using h0, fun x hx c hc => by
      change j (c • x) ∈ R'
      rw [map_smul]
      exact hs _ hx c hc⟩, fun u hu w hw => by
      change j (u + w) ∈ R'
      rw [map_add]
      exact hadd _ hu _ hw, fun u hu w hw huw => by
      have := hext (j u) ⟨u, hu, rfl⟩ (j w) ⟨w, hw, rfl⟩ (by simpa using huw)
      exact this⟩, v₀, fun h => hv0 (by rw [h, map_zero]), ?_⟩
  ext x
  change j x ∈ R' ↔ _
  rw [hRv]
  constructor
  · rintro ⟨c, hc, hcx⟩
    exact ⟨c, hc, hj (by rw [map_smul, hcx])⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, by rw [map_smul]⟩

/-- **A negative extremal ray of the relative cone.** If `D` is not nef over `S`, then `D` is
negative on (the nonzero elements of) some extremal ray of `NE̅(X/S)`: in coordinates the cone
is closed with an ample form positive off `0`, so the compact slice argument applies. -/
private theorem exists_isExtremalRay_relativeCurveForm_neg {X S : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ))
    (sS : S ⟶ Spec (.of ℂ)) [MMP.Mori.IsProjectiveVariety ℂ sX] [MMP.Mori.IsProjectiveVariety ℂ sS]
    (f : X ⟶ S) (hf : f ≫ sS = sX) {D : QDivisor X} (hD : D.IsQCartier)
    (hnef : ¬ QDivisor.IsRelativelyNef sX f D) :
    ∃ R : Set (RelativeNumericalCurveClasses sX f),
      IsExtremalRay ℝ (relativeClosedConeOfCurves sX f : Set _) R ∧
        ∀ z ∈ R, z ≠ 0 → QDivisor.relativeCurveForm sX f D hD z < 0 := by
  haveI : QuasiCompact sX := (inferInstance : MMP.Mori.IsProjectiveVariety ℂ sX).toQuasiCompact
  obtain ⟨C, hC, hneg⟩ : ∃ C : ProperCurve sX, C.IsContractedBy f ∧
      QDivisor.curveForm sX D hD (OneCycle.numericalClass sX (C.cycle ℝ)) < 0 := by
    simp only [MMP.Mori.QDivisor.IsRelativelyNef, not_exists, not_forall, not_le] at hnef
    obtain ⟨C, hC, hlt⟩ := hnef hD
    exact ⟨C, hC, by rw [curveForm_numericalClass_eq_sum]; exact hlt⟩
  obtain ⟨ι, _, Φ, A, hj, -, hCcl, hA⟩ :=
    exists_coordinates_relativeClosedConeOfCurves sX sS f hf
  set j := Φ.toLinearMap ∘ₗ relativeToAbsolute sX f with hjdef
  set P : PointedCone ℝ (ι → ℝ) := (relativeClosedConeOfCurves sX f).map j
  have hP : (P : Set (ι → ℝ)) = j '' (relativeClosedConeOfCurves sX f : Set _) :=
    Submodule.map_coe _ _
  set d := QDivisor.curveForm sX D hD ∘ₗ Φ.symm.toLinearMap
  have hCmem : C.relativeClass f hC ∈ relativeClosedConeOfCurves sX f := by
    rw [← SetLike.mem_coe, coe_relativeClosedConeOfCurves]
    exact subset_closure (relativeClass_mem_relativeConeOfCurves hC)
  obtain ⟨R', hR', hR'neg⟩ := MMP.Fourfold.exists_isExtremalRay_neg_of_exists_neg P
    (by rw [hP]; exact hCcl) A (fun x hx hx0 => hA x (by rw [← hP]; exact hx) hx0) d
    ⟨j (C.relativeClass f hC), by rw [← SetLike.mem_coe, hP]; exact ⟨_, hCmem, rfl⟩, by
      change QDivisor.curveForm sX D hD (Φ.symm (Φ (relativeToAbsolute sX f
        (C.relativeClass f hC)))) < 0
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact hneg⟩
  rw [hP] at hR'
  refine ⟨j ⁻¹' R', isExtremalRay_preimage hj hR', fun z hz hz0 => ?_⟩
  have := hR'neg (j z) hz fun h => hz0 (hj (by rw [h, map_zero]))
  rw [relativeCurveForm_eq_comp]
  change QDivisor.curveForm sX D hD (Φ.symm (Φ (relativeToAbsolute sX f z))) < 0 at this
  rwa [ContinuousLinearEquiv.symm_apply_apply] at this

end Ray

/-! ### Contractions of negative extremal rays over the base -/

section Contraction

/-- A morphism with closed range whose comorphism `𝒪_Z ⟶ f_* 𝒪_X` is an isomorphism is
surjective. -/
private lemma surjective_of_isIso_c {X Z : Scheme.{u}} (f : X ⟶ Z)
    (hf : IsClosed (Set.range f)) [IsIso f.c] : Function.Surjective f := by
  intro z
  by_contra hz
  let U : Z.Opens := ⟨(Set.range f)ᶜ, hf.isOpen_compl⟩
  have hU : f ⁻¹ᵁ U = ⊥ := le_bot_iff.mp fun x hx => (hx ⟨x, rfl⟩).elim
  have : Subsingleton Γ(X, f ⁻¹ᵁ U) := by rw [hU]; infer_instance
  have : IsIso (f.app U) := inferInstanceAs (IsIso (f.c.app _))
  have hinj : Function.Injective (f.app U) :=
    (ConcreteCategory.bijective_of_isIso (f.app U)).1
  have h10 : (1 : Γ(Z, U)) = 0 := hinj (Subsingleton.elim _ _)
  have hzU : z ∈ U := fun ⟨x, hx⟩ => hz ⟨x, hx⟩
  have := congrArg (Z.presheaf.germ U z hzU) h10
  simp at this

/-- A morphism of projective `k`-varieties is projective: it is the graph, a closed immersion,
followed by a base change of the structure morphism of the source. -/
private theorem isProjectiveMorphism_of_comp_eq {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hY : MMP.Mori.IsProjectiveVariety k sY)
    {f : X ⟶ Y} (hf : f ≫ sY = sX) : IsProjectiveMorphism f := by
  have : IsSeparated sY := hY.toIsVariety.toIsSeparated
  let γ : X ⟶ Limits.pullback sX sY := Limits.pullback.lift (𝟙 X) f (by simp [hf])
  have : IsClosedImmersion γ :=
    MorphismProperty.of_postcomp (W := @IsClosedImmersion) (W' := @IsSeparated) γ
      (Limits.pullback.fst sX sY) inferInstance
      (by simp only [γ, Limits.pullback.lift_fst]; infer_instance)
  have hγ : γ ≫ Limits.pullback.snd sX sY = f := Limits.pullback.lift_snd _ _ _
  rw [← hγ]
  exact (MMP.isProjectiveMorphism_of_isClosedImmersion γ).comp
    (hX.isProjective.baseChange sY)

/-- On a projective variety the class `[C] ∈ N₁(X)` of a proper curve is nonzero: an ample
invertible sheaf has positive degree on `C`. -/
private theorem numericalClass_cycle_ne_zero {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (hX : MMP.Mori.IsProjectiveVariety k sX)
    (C : ProperCurve sX) : OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0 := by
  have hproj : IsProjectiveMorphism sX := hX.isProjective
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective sX
    (Stacks.Ample.unitModule (Spec (.of k)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    (isQuasiProjective_of_isHQuasiProjective sX hproj.isHQuasiProjective)
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := inferInstance
  have hpos := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy sX L
    (MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple sX L hLa) C
    (fun _ _ => Subsingleton.elim _ _)
  intro h0
  have h := OneCycle.mem_numericallyTrivial.mp ((Submodule.Quotient.mk_eq_zero _).mp h0) L
  rw [OneCycle.degree_cycle] at h
  unfold ProperCurve.degree at h
  have : (0 : ℝ) < (degreeOn k sX C.ι C.dim_le L : ℝ) := by exact_mod_cast hpos
  linarith

/-- A curve whose class lies in the image of `N₁(X/Z) → N₁(X)` is contracted by `h : X ⟶ Z`, for
`Z` projective: its push-forward is numerically trivial, so an ample sheaf of `Z` pulls back to a
sheaf of degree zero on it. -/
private theorem isContractedBy_of_mem_range_relativeToAbsolute {X Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {h : X ⟶ Z} (hh : h ≫ sZ = sX) (C : ProperCurve sX)
    (hC : OneCycle.numericalClass sX (C.cycle ℝ) ∈ LinearMap.range (relativeToAbsolute sX h)) :
    C.IsContractedBy h := by
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  haveI : LocallyOfFiniteType sZ := hZ.toIsVariety.toLocallyOfFiniteType
  obtain ⟨A, hAinv, hA⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hZ
  have hker := MMP.Mori.range_relativeToAbsolute_le_ker_pushforward h hh hC
  rw [LinearMap.mem_ker] at hker
  have hdeg := NumericalCurveClasses.degree_pushforward h hh A
    (OneCycle.numericalClass sX (C.cycle ℝ))
  rw [hker, map_zero, NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle] at hdeg
  exact MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero h hh A hA C
    (by exact_mod_cast hdeg.symm)

/-- A curve contracted by `ψ` is contracted by `ψ ≫ g`. -/
private theorem isContractedBy_comp {k : Type} [Field k] {X V Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {C : ProperCurve sX} {ψ : X ⟶ V} (hC : C.IsContractedBy ψ)
    (g : V ⟶ Z) : C.IsContractedBy (ψ ≫ g) := fun x hx => by
  simp only [Scheme.Hom.comp_apply, hC x hx]

/-- A factor `ψ` of a birational morphism `ψ ≫ g` of integral schemes, `ψ` dominant, is birational:
its stalk map at the generic point is surjective, as a factor of an isomorphism, and injective, its
source being a field. -/
private theorem isBirational_of_comp {U V Z : Scheme.{u}} [IsIntegral U] [IsIntegral V]
    [IsIntegral Z] (ψ : U ⟶ V) (g : V ⟶ Z) [IsDominant ψ] (hh : IsBirational (ψ ≫ g)) :
    IsBirational ψ ∧ IsBirational g := by
  have hgen : ψ (genericPoint U) = genericPoint V := map_genericPoint_of_isDominant ψ
  have hiso : IsIso ((ψ ≫ g).stalkMap (genericPoint U)) := by
    refine hh.2 _ ?_
    rw [genericPoints_eq_singleton]
    rfl
  have hgen' : g (genericPoint V) = genericPoint Z := by
    have := hh.1.surjOn
    rw [genericPoints_eq_singleton, genericPoints_eq_singleton] at this
    obtain ⟨x, hx, hx'⟩ := this (Set.mem_singleton _)
    rw [Set.mem_singleton_iff] at hx
    rw [hx, Scheme.Hom.comp_apply, hgen] at hx'
    exact hx'
  set η := genericPoint U
  have e1 : ∀ x, (ψ ≫ g).stalkMap η x = ψ.stalkMap η (g.stalkMap (ψ η) x) := fun x =>
    DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (Scheme.Hom.stalkMap_comp ψ g η)) x
  have hfield : IsField (V.presheaf.stalk (ψ η)) :=
    (V.presheaf.stalkCongr (.of_eq hgen)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField V.functionField)
  letI := hfield.toField
  have hinj : Function.Injective (ψ.stalkMap η) := RingHom.injective (ψ.stalkMap η).hom
  have hsurj : Function.Surjective (ψ.stalkMap η) := by
    intro b
    obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso ((ψ ≫ g).stalkMap η)).2 b
    exact ⟨g.stalkMap (ψ η) a, by rw [← e1, ha]⟩
  have hψiso : IsIso (ψ.stalkMap η) := (ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj, hsurj⟩
  have hgiso : IsIso (g.stalkMap (ψ η)) := by
    have hfield' : IsField (Z.presheaf.stalk (g (ψ η))) :=
      (Z.presheaf.stalkCongr (.of_eq (by rw [hgen, hgen']))).commRingCatIsoToRingEquiv.toMulEquiv.isField
        (Field.toIsField Z.functionField)
    letI := hfield'.toField
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨RingHom.injective (g.stalkMap (ψ η)).hom,
      fun b => ?_⟩
    obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso ((ψ ≫ g).stalkMap η)).2
      (ψ.stalkMap η b)
    exact ⟨a, hinj (by rw [← e1, ha])⟩
  refine ⟨⟨?_, fun x hx => ?_⟩, ⟨?_, fun x hx => ?_⟩⟩
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton, ← hgen]
    exact Set.bijOn_singleton.mpr rfl
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    exact hψiso
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton, ← hgen']
    exact Set.bijOn_singleton.mpr rfl
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    exact hgen ▸ hgiso

/-- **The contraction of a negative extremal ray over `Z`.** Let `(U, Δ)` be a projective
`ℚ`-factorial dlt pair, birational over the projective variety `Z` by `h`, with `K + Δ` not nef
over `Z`. Then there are a `(K + Δ)`-negative extremal ray `R` of `NE̅(U)` contained in
`NE̅(U/Z)` and its contraction `ψ : U ⟶ V` over `Z`, onto a normal projective variety; `ψ` and
`V ⟶ Z` are birational, and `K + Δ` is negative on every curve contracted by `ψ`. -/
private theorem exists_isContractionOfRay_comp_eq {U Z : Scheme.{0}} [IsIntegral U]
    [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U] {sU : U ⟶ Spec (.of ℂ)}
    [QuasiCompact sU] [LocallyOfFiniteType sU] [IsIntegral Z] {sZ : Z ⟶ Spec (.of ℂ)}
    (hU : MMP.Mori.IsProjectiveVariety ℂ sU) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hQ : IsQFactorial sU) {K : Divisor U} (hK : K.IsCanonicalDivisor sU 4) {Δ : QDivisor U}
    (hΔ : MMP.Intersection.IsDltPair sU Δ) {h : U ⟶ Z} (hh : h ≫ sZ = sU)
    (hbir : IsBirationalMorphism h)
    (hnef : ¬ QDivisor.IsRelativelyNef sU h (Divisor.toQDivisor K + Δ)) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : CompactSpace V) (_ : IsLocallyNoetherian V)
      (_ : IsNormal V) (sV : V ⟶ Spec (.of ℂ)) (R : Set (NumericalCurveClasses sU)) (ψ : U ⟶ V)
      (g : V ⟶ Z),
      IsNegativeExtremalRayOf sU (Divisor.toQDivisor K + Δ) R ∧ IsContractionOfRay sU sV R ψ ∧
        IsBirationalMorphism ψ ∧ ψ ≫ g = h ∧ g ≫ sZ = sV ∧ IsProjectiveMorphism g ∧
        IsBirationalMorphism g ∧ MMP.Mori.IsProjectiveVariety ℂ sV ∧
        ∀ C : ProperCurve sU, C.IsContractedBy ψ → ∀ hQ' : (Divisor.toQDivisor K + Δ).IsQCartier,
          (Divisor.toQDivisor K + Δ).intersectionNumber ℂ sU C.ι C.dim_le hQ' < 0 := by
  haveI : MMP.Mori.IsProjectiveVariety ℂ sU := hU
  haveI : MMP.Mori.IsProjectiveVariety ℂ sZ := hZ
  have hQD : (Divisor.toQDivisor K + Δ).IsQCartier := isQCartier_of_isQFactorial sU hQ _
  have hΔM := (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sU hK Δ).mp hΔ
  obtain ⟨Rr, hRr, hRrneg⟩ := exists_isExtremalRay_relativeCurveForm_neg sU sZ h hh hQD hnef
  obtain ⟨V, ψ, g, hcon⟩ := MMP.Mori.IsDltPair.exists_isRelativeContractionOfFace sZ h hh hΔM hQ
    hRr.1 hRr.1.2.2.1 fun z hz hz0 => hRrneg z hz hz0
  set R := relativeToAbsolute sU h '' Rr with hRdef
  have hRabs : IsExtremalRay ℝ (closedConeOfCurves sU : Set (NumericalCurveClasses sU)) R :=
    MMP.Mori.isExtremalRay_image_relativeToAbsolute sU sZ h hh hRr
  have hinj := relativeToAbsolute_injective sU h
  have hRneg : IsNegativeExtremalRayOf sU (Divisor.toQDivisor K + Δ) R := by
    refine ⟨hQD, hRabs, ?_⟩
    rintro _ ⟨z, hz, rfl⟩ hu0
    have hz0 : z ≠ 0 := fun h0 => hu0 (by rw [h0, map_zero])
    have := hRrneg z hz hz0
    rwa [relativeCurveForm_eq_comp] at this
  have hψg : ψ ≫ g = h := hcon.comp_eq
  haveI : ∀ W, IsIso (ψ.c.app W) := fun W => hcon.isIso_app W.unop
  haveI : IsIso ψ.c := NatIso.isIso_of_isIso_app _
  haveI : IsProper g := isProper_of_isProjectiveMorphism g hcon.isProjectiveMorphism
  haveI : IsProper h := isProper_of_isProjectiveMorphism h (by
    rw [← hh] at hU
    exact (isProjectiveMorphism_of_comp_eq hU hZ rfl))
  haveI : IsProper (ψ ≫ g) := by rw [hψg]; infer_instance
  haveI : IsProper ψ := IsProper.of_comp ψ g
  have hsurj : Function.Surjective ψ := surjective_of_isIso_c ψ ψ.isClosedMap.isClosed_range
  haveI : Surjective ψ := ⟨hsurj⟩
  haveI : IsDominant ψ := inferInstance
  haveI : IrreducibleSpace V := hsurj.irreducibleSpace ψ.continuous
  haveI : IsReduced V := ⟨fun W => by
    have : IsIso (ψ.app W) := inferInstanceAs (IsIso (ψ.c.app _))
    exact isReduced_of_injective (ψ.app W).hom
      (ConcreteCategory.bijective_of_isIso (ψ.app W)).1⟩
  haveI : IsIntegral V := isIntegral_of_irreducibleSpace_of_isReduced V
  set sV := g ≫ sZ with hsVdef
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  haveI : LocallyOfFiniteType sZ := hZ.toIsVariety.toLocallyOfFiniteType
  haveI : QuasiCompact sZ := hZ.toIsVariety.toQuasiCompact
  haveI hVvar : AlgebraicGeometry.IsVariety ℂ sV := AlgebraicGeometry.IsVariety.mk
  have hψV : ψ ≫ sV = sU := by rw [hsVdef, ← Category.assoc, hψg, hh]
  have hUvar : AlgebraicGeometry.IsVariety ℂ (ψ ≫ sV) := by rw [hψV]; exact hU.toIsVariety
  haveI : IsNormal V := MMP.Mori.isNormal_of_isIso_c sV ψ hVvar hUvar
  have hVn : IsNormalVariety ℂ sV := ⟨hVvar, inferInstance⟩
  have hVp : MMP.Mori.IsProjectiveVariety ℂ sV := ⟨hcon.isProjectiveMorphism.comp hZ.isProjective⟩
  have hψp : IsProjectiveMorphism ψ := isProjectiveMorphism_of_comp_eq hU hVp hψV
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have hbir' := isBirational_of_comp ψ g
    (by rw [hψg]; exact MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbir)
  have hψb := MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_of_isBirational ψ hbir'.1
  have hgb := MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_of_isBirational g hbir'.2
  have hiff : ∀ C : ProperCurve sU,
      C.IsContractedBy ψ ↔ OneCycle.numericalClass sU (C.cycle ℝ) ∈ R := by
    intro C
    constructor
    · intro hC
      have hCh : C.IsContractedBy h := hψg ▸ isContractedBy_comp hC g
      exact ⟨C.relativeClass h hCh, ((hcon.isContractedBy_iff C hCh).mp hC), rfl⟩
    · rintro ⟨z, hz, hzC⟩
      have hCh : C.IsContractedBy h :=
        isContractedBy_of_mem_range_relativeToAbsolute hZ hh C ⟨z, hzC⟩
      refine (hcon.isContractedBy_iff C hCh).mpr ?_
      have : C.relativeClass h hCh = z := hinj (by rw [hzC]; rfl)
      rwa [this]
  have hcontr : IsContractionOfRay sU sV R ψ :=
    { isNormalVariety_source := hΔ.1.1.1
      isNormalVariety_target := hVn
      comp_eq := hψV
      isProjectiveMorphism := hψp
      surjective := hsurj
      isIso_app := hcon.isIso_app
      isContractedBy_iff := hiff }
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, sV, R, ψ, g, hRneg, hcontr,
    hψb, hψg, rfl, hcon.isProjectiveMorphism, hgb, hVp, fun C hC hQ' => ?_⟩
  have hmem := (hiff C).mp hC
  have := hRneg.2.2 _ hmem (numericalClass_cycle_ne_zero hU C)
  rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle] at this
  exact_mod_cast this

end Contraction

/-! ### Prime divisors and divisors over the models of a step -/

section StepTransport

variable {U U' V : Scheme.{0}} [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
  [IsIntegral U'] [IsLocallyNoetherian U'] [IsNormal U'] [IsIntegral V] [IsLocallyNoetherian V]
  [IsNormal V]

/-- The valuation of a divisor `(Y, p, E)` over `U`, read in `k(V)` through `ψ : U ⟶ V`, is that of
`E` along `p ≫ ψ`. -/
private theorem valuation_comap_eq_valuationOver {k : Type} [Field k] {sU : U ⟶ Spec (.of k)}
    (E : DivisorOver k sU) (ψ : U ⟶ V) [IsDominant ψ] :
    haveI := E.isIntegral
    haveI := E.isNormal
    haveI := E.isLocallyNoetherian
    haveI := E.isDominant
    E.valuation.comap (functionFieldMap ψ) = E.E.valuationOver (E.f ≫ ψ) := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  exact (valuationOver_of_comp_eq E.E rfl).symm

/-- A proper dominant morphism is surjective. -/
private theorem surjective_of_isProper {X Y : Scheme.{0}} (f : X ⟶ Y) [IsProper f]
    [IsDominant f] : Function.Surjective f := by
  have h := f.denseRange.closure_range
  rw [f.isClosedMap.isClosed_range.closure_eq] at h
  exact Set.range_eq_univ.mp h

/-- **Prime divisors across a step.** For a proper birational `ψ : U ⟶ V` and a small
`f⁺ : U' ⟶ V` onto a normal variety, every prime divisor `F'` of `U'` corresponds to a prime
divisor `F` of `U` with the same valuation of `k(V)`, and the strict transform
`(f⁺)⁻¹_* ψ_* Δ` has at `F'` the coefficient of `Δ` at `F`. -/
private theorem exists_primeDivisor_valuationOver_eq_and_flipTransform_apply
    {sV : V ⟶ Spec (.of ℂ)} {sU' : U' ⟶ Spec (.of ℂ)} (hV : IsNormalVariety ℂ sV) {ψ : U ⟶ V}
    [IsProper ψ] (hψ : IsBirationalMorphism ψ) {fp : U' ⟶ V} (hfp : IsSmallMorphism sU' sV fp)
    (F' : PrimeDivisor U') (Δ : QDivisor U) :
    haveI := hψ.isDominant
    haveI := hfp.isBirationalMorphism.isDominant
    ∃ F : PrimeDivisor U, F.valuationOver ψ = F'.valuationOver fp ∧
      (flipTransform ψ fp Δ).coeff F' = Δ.coeff F := by
  haveI := hψ.isDominant
  haveI := hfp.isBirationalMorphism.isDominant
  haveI : IsProper fp := hfp.isProper
  haveI := isSeparated_toTerminal_of_isNormalVariety hV
  obtain ⟨F, Q, hval, hFQ, hF'Q⟩ :=
    exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hV hψ hfp F'
  refine ⟨F, hval, ?_⟩
  haveI := Q.isDiscreteValuationRing_localRing
  have hPQ := map_genericPoint_eq_of_image_eq F Q hFQ
  have hPpQ := map_genericPoint_eq_of_image_eq F' Q hF'Q
  have hreg := MMP.Fourfold.Oai4C1.map_genericPoint_mem_biregularLocus
    hfp.two_le_codimension F'
  rw [hPpQ] at hreg
  exact flipTransform_apply_of_map_genericPoint hψ.functionFieldMap_bijective
    (surjective_of_isProper fp) hPQ hPpQ hreg Δ

/-- **Prime divisors over a small morphism.** Over a prime divisor `Q` of the normal variety `V`,
a small morphism `f⁺ : U' ⟶ V` has a prime divisor `F'` with `ord_{F'} = ord_Q`. -/
private theorem exists_primeDivisor_valuationOver_eq_of_small {sV : V ⟶ Spec (.of ℂ)}
    {sU' : U' ⟶ Spec (.of ℂ)} {fp : U' ⟶ V} (hfp : IsSmallMorphism sU' sV fp)
    (Q : PrimeDivisor V) :
    haveI := hfp.isBirationalMorphism.isDominant
    ∃ F' : PrimeDivisor U', F'.valuationOver fp = Q.divisorialValuation := by
  haveI := hfp.isBirationalMorphism.isDominant
  haveI : IsProper fp := hfp.isProper
  have hbij := hfp.isBirationalMorphism.functionFieldMap_bijective
  have hreg := MMP.Positivity.mem_biregularLocus_of_coheight_le_one fp hbij
    hfp.two_le_codimension (y := Q.genericPoint) (by rw [Q.coheight_genericPoint])
  obtain ⟨x, hx⟩ := surjective_of_isProper fp Q.genericPoint
  rw [← hx] at hreg
  have hcoh : Order.coheight x = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp hreg, hx, Q.coheight_genericPoint]
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hcoh, ?_⟩
  refine MMP.Fourfold.Oai4C1.CommonModel.valuationOver_eq_of_map_genericPoint fp hbij.2 _ Q ?_
  exact (congrArg (fun y => fp y)
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hcoh)).trans hx

/-- A prime divisor `F` of `U` at whose generic point `ψ` is biregular has the valuation of a
prime divisor of `V`. -/
private theorem exists_primeDivisor_of_mem_biregularLocus {ψ : U ⟶ V} [IsDominant ψ]
    (hψ : IsBirationalMorphism ψ) (F : PrimeDivisor U)
    (hF : ψ F.genericPoint ∈ biregularLocus ψ) :
    ∃ Q : PrimeDivisor V, F.valuationOver ψ = Q.divisorialValuation := by
  have hcoh : Order.coheight (ψ F.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus ψ hF, F.coheight_genericPoint]
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh,
    MMP.Fourfold.Oai4C1.CommonModel.valuationOver_eq_of_map_genericPoint ψ
      hψ.functionFieldMap_bijective.2 F _
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh).symm⟩

/-- **Divisors not exceptional over `V`.** A divisor `(Y, p, E)` over `U` which is not exceptional
for `p ≫ ψ` has the valuation, in `k(V)`, of a prime divisor of the normal variety `V`. -/
private theorem exists_primeDivisor_of_not_isExceptional {sU : U ⟶ Spec (.of ℂ)}
    {sV : V ⟶ Spec (.of ℂ)} (hV : IsNormalVariety ℂ sV) {ψ : U ⟶ V} (hψV : ψ ≫ sV = sU)
    (hψ : IsBirationalMorphism ψ) (E : DivisorOver ℂ sU)
    (hE : ¬ RationalMap.IsExceptional (X := E.Y) (E.f ≫ ψ).toRationalMap E.E) :
    haveI := hψ.isDominant
    ∃ Q : PrimeDivisor V, E.valuation.comap (functionFieldMap ψ) = Q.divisorialValuation := by
  haveI := hψ.isDominant
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  haveI := isSeparated_toTerminal_of_isNormalVariety hV
  have hEV : IsNormalVariety ℂ ((E.f ≫ ψ) ≫ sV) := by
    rw [Category.assoc, hψV]; exact E.isNormalVariety
  let D : DivisorOver ℂ sV :=
    ⟨E.Y, E.f ≫ ψ, hEV, MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp
      E.isBirationalMorphism hψ, E.E⟩
  have hD : ¬ 2 ≤ codimension D.center := by
    rw [MMP.Positivity.DivisorOver.codimension_center]
    intro h2
    apply hE
    rw [MMP.Positivity.isExceptional_toRationalMap_iff, MMP.Flips.le_closedsCodimension_iff_le_coheight]
    intro x hx
    refine h2.trans (Order.coheight_anti ?_)
    have hsub : ((E.f ≫ ψ) '' (E.E.idealSheaf.support : Set E.Y)) ⊆
        closure {(E.f ≫ ψ) E.E.genericPoint} := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : E.E.genericPoint ⤳ y := by
        change y ∈ E.E.support at hy
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy
        exact specializes_iff_mem_closure.mpr hy
      exact specializes_iff_mem_closure.mp (hy'.map (E.f ≫ ψ).continuous)
    rw [TopologicalSpace.Closeds.coe_closure] at hx
    exact specializes_iff_mem_closure.mpr (closure_minimal hsub isClosed_closure hx)
  rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hV] at hD
  push Not at hD
  obtain ⟨Q, hQ⟩ := hD
  refine ⟨Q, ?_⟩
  rw [valuation_comap_eq_valuationOver]
  have e : D.valuation = E.E.valuationOver (E.f ≫ ψ) := rfl
  rw [← e, hQ, valuation_ofPrimeDivisor]

/-- **Prime divisors over a proper birational morphism.** Over a prime divisor `Q` of a normal
scheme `V`, a proper birational morphism `p : U ⟶ V` has a prime divisor `F` with
`p(η_F) = η_Q`. -/
private theorem exists_primeDivisor_map_genericPoint_eq (p : U ⟶ V) [IsProper p]
    (hp : IsBirationalMorphism p) (Q : PrimeDivisor V) :
    ∃ F : PrimeDivisor U, p F.genericPoint = Q.genericPoint := by
  haveI := hp.isDominant
  have hreg := MMP.Fourfold.Oai4C1.genericPoint_mem_biregularLocus p hp Q
  obtain ⟨x, hx⟩ := surjective_of_isProper p Q.genericPoint
  rw [← hx] at hreg
  have hcoh : Order.coheight x = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus p hreg, hx, Q.coheight_genericPoint]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hcoh,
    (congrArg (fun y => p y) (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hcoh)).trans hx⟩

/-- **Push-forward of a strict transform.** For a proper birational morphism `p : U ⟶ V` onto a
normal separated scheme, `p_* p⁻¹_* G = G`. -/
private theorem transformDivisor_inverseTransformDivisor [IsSeparated (V ↘ Limits.terminal Scheme)]
    (p : U ⟶ V) [IsProper p] (hp : IsBirationalMorphism p) (G : QDivisor V) :
    RationalMap.transformDivisor (X := U) p.toRationalMap (inverseTransformDivisor p G) = G := by
  ext Q
  obtain ⟨F, hF⟩ := exists_primeDivisor_map_genericPoint_eq p hp Q
  change RationalMap.transformDivisor (X := U) p.toRationalMap (inverseTransformDivisor p G) Q = G Q
  rw [MMP.Fourfold.Oai4C1.transformDivisor_apply_of_map_genericPoint hp hF,
    MMP.Fourfold.Oai4C1.inverseTransformDivisor_apply_of_map_genericPoint hF
      (MMP.Fourfold.Oai4C1.genericPoint_mem_biregularLocus p hp Q)]

/-- `((-D) · C) = -(D · C)`. -/
private theorem intersectionNumber_neg {X C : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX]
    (i : C ⟶ X) [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) {D : QDivisor X}
    (hD : D.IsQCartier) (hD' : (-D).IsQCartier) :
    (-D).intersectionNumber ℂ sX i hdim hD' = -(D.intersectionNumber ℂ sX i hdim hD) := by
  have hadd := QDivisor.intersectionNumber_add' ℂ sX i hdim D (-D) hD hD'
    (by rw [add_neg_cancel]; exact QDivisor.isQCartier_zero)
  have h00 : (0 : QDivisor X).intersectionNumber ℂ sX i hdim QDivisor.isQCartier_zero = 0 := by
    have := QDivisor.intersectionNumber_add' ℂ sX i hdim (0 : QDivisor X) 0
      QDivisor.isQCartier_zero QDivisor.isQCartier_zero (by simpa using QDivisor.isQCartier_zero)
    simp only [add_zero] at this
    linarith
  rw [MMP.Fourfold.intersectionNumber_congr sX i hdim _ QDivisor.isQCartier_zero (add_neg_cancel D),
    h00] at hadd
  linarith

/-- The relative nefness sum of a `ℚ`-Cartier `ℚ`-divisor on a curve is its intersection
number. -/
private theorem sum_degreeOn_eq_intersectionNumber {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX] (D : QDivisor X)
    (h : D.IsQCartier) (C : ProperCurve sX) :
    ((D.associatedCartier h).sum fun E c =>
        (c : ℝ) * ((E : Divisor X).degreeOn ℂ sX C.ι C.dim_le E.2 : ℝ)) =
      (D.intersectionNumber ℂ sX C.ι C.dim_le h : ℝ) := by
  rw [← curveForm_numericalClass_eq_sum, MMP.ProgramBaseChange.curveForm_numericalClass_cycle]

/-- `-D` is nef over `f` when `D` is negative on every curve contracted by `f`. -/
private theorem isRelativelyNef_neg_of_forall_intersectionNumber_neg {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [QuasiCompact sX] {f : X ⟶ Y} {D : QDivisor X} (hD : D.IsQCartier)
    (hneg : ∀ C : ProperCurve sX, C.IsContractedBy f → ∀ hQ : D.IsQCartier,
      D.intersectionNumber ℂ sX C.ι C.dim_le hQ < 0) :
    QDivisor.IsRelativelyNef sX f (-D) := by
  refine ⟨MMP.Fourfold.Oai4C1.isQCartier_neg hD, fun C hC => ?_⟩
  rw [sum_degreeOn_eq_intersectionNumber, intersectionNumber_neg sX C.ι C.dim_le hD]
  have := hneg C hC hD
  have : (0 : ℝ) < -((D.intersectionNumber ℂ sX C.ι C.dim_le hD : ℚ) : ℝ) := by
    exact_mod_cast neg_pos.mpr this
  push_cast
  linarith

/-- An adjoint relatively ample over `f` is relatively nef over `f`. -/
private theorem isRelativelyNef_of_hasRelativelyAmpleMultiple {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [QuasiCompact sX] {f : X ⟶ Y} {D : QDivisor X} (hD : D.IsQCartier)
    (ha : D.HasRelativelyAmpleMultiple f) : QDivisor.IsRelativelyNef sX f D := by
  refine ⟨hD, fun C hC => ?_⟩
  rw [sum_degreeOn_eq_intersectionNumber]
  have := MMP.Fourfold.Oai4C1.TwoEnds.intersectionNumber_pos_of_hasRelativelyAmpleMultiple sX hD
    ha C hC
  exact_mod_cast this.le

/-- No proper curve is contracted by the identity. -/
private theorem not_isContractedBy_id {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) : ¬ C.IsContractedBy (𝟙 X) := by
  intro h
  haveI : Subsingleton C.scheme := by
    constructor
    intro a b
    apply C.ι.isClosedEmbedding.injective
    have ha : C.ι a ∈ closure ({C.point} : Set X) := C.range_ι ▸ ⟨a, rfl⟩
    have hb : C.ι b ∈ closure ({C.point} : Set X) := C.range_ι ▸ ⟨b, rfl⟩
    exact (h _ ha).trans (h _ hb).symm
  have hdim := C.isProperCurve.dim_eq
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [hdim] at h0
  exact absurd h0 (by decide)

/-- Every adjoint is nef over an isomorphism: no curve is contracted. -/
private theorem isRelativelyNef_id {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX] {D : QDivisor X} (hD : D.IsQCartier) :
    QDivisor.IsRelativelyNef sX (𝟙 X) D :=
  ⟨hD, fun C hC => absurd hC (not_isContractedBy_id C)⟩

/-- A discrepancy of a divisor over `U` with the valuation of a prime divisor `F` of `U` is
`-coeff_F(Δ)`. -/
private theorem eq_neg_coeff_of_valuation_eq {sU : U ⟶ Spec (.of ℂ)} (hU : IsNormalVariety ℂ sU)
    {n : ℕ} {K : Divisor U} {Δ : QDivisor U} {E : DivisorOver ℂ sU} {F : PrimeDivisor U}
    (hv : E.valuation = F.divisorialValuation) {c : ℚ} (hc : IsDiscrepancy sU n K Δ E c) :
    c = -Δ.coeff F := by
  have hη := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hU.1 (D := E)
    (D' := DivisorOver.ofPrimeDivisor ℂ hU F) (by rw [valuation_ofPrimeDivisor]; exact hv)
  exact eq_neg_coeff_of_map_genericPoint_eq hU hη hc

/-- **A divisor over the previous model.** A divisor `E'` over `U'`, proper, has the same
valuation of `k(V)` as some proper divisor `E` over `U`: realize `E'` on a common model of
`E'.Y` and `U` over `V`. -/
private theorem exists_divisorOver_valuation_comap_eq {sU : U ⟶ Spec (.of ℂ)}
    {sU' : U' ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} (hUn : IsNormalVariety ℂ sU) {ψ : U ⟶ V}
    [IsProper ψ] (hψ : IsBirationalMorphism ψ) (hψV : ψ ≫ sV = sU) {fp : U' ⟶ V} [IsProper fp]
    (hfp : IsBirationalMorphism fp) (hfpV : fp ≫ sV = sU') (E' : DivisorOver ℂ sU')
    (hE' : IsProper E'.f) :
    haveI := hψ.isDominant
    haveI := hfp.isDominant
    ∃ E : DivisorOver ℂ sU, IsProper E.f ∧
      E.valuation.comap (functionFieldMap ψ) = E'.valuation.comap (functionFieldMap fp) := by
  haveI := hψ.isDominant
  haveI := hfp.isDominant
  haveI := E'.isIntegral
  haveI := E'.isNormal
  haveI := E'.isLocallyNoetherian
  haveI := E'.isDominant
  haveI : IsProper (E'.f ≫ fp) := inferInstance
  have hm : IsNormalVariety ℂ ((E'.f ≫ fp) ≫ sV) := by
    rw [Category.assoc, hfpV]; exact E'.isNormalVariety
  have hXn : IsNormalVariety ℂ (ψ ≫ sV) := by rw [hψV]; exact hUn
  obtain ⟨W, g₁, g₂, hW, hg₁, hg₂, hb₁, hb₂, hc⟩ :=
    MMP.Fourfold.Oai4C1.CommonModel.exists_common_model_two sV (E'.f ≫ fp)
      (MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp E'.isBirationalMorphism hfp) hm ψ
      hψ hXn
  haveI := hW.1.toIsIntegral
  haveI := hW.2
  haveI := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (g₁ ≫ (E'.f ≫ fp) ≫ sV)
  haveI := hb₁.isDominant
  haveI := hb₂.isDominant
  have hW' : IsNormalVariety ℂ ((g₁ ≫ E'.f) ≫ sU') := by
    have e : (g₁ ≫ E'.f) ≫ sU' = g₁ ≫ (E'.f ≫ fp) ≫ sV := by
      rw [congrArg (fun s => (g₁ ≫ E'.f) ≫ s) hfpV.symm]
      simp only [Category.assoc]
    rw [e]; exact hW
  obtain ⟨EW, hEW⟩ := MMP.Fourfold.Oai4C1.CommonModel.exists_primeDivisor_valuation_eq E'
    (g₁ ≫ E'.f) hW' (MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hb₁
      E'.isBirationalMorphism) g₁ hb₁ rfl
  have hW2 : IsNormalVariety ℂ (g₂ ≫ sU) := by
    have e : g₂ ≫ sU = g₁ ≫ (E'.f ≫ fp) ≫ sV := by
      rw [congrArg (fun s => g₂ ≫ s) hψV.symm, ← Category.assoc, ← hc]
      simp only [Category.assoc]
    rw [e]; exact hW
  refine ⟨⟨W, g₂, hW2, hb₂, EW⟩, hg₂, ?_⟩
  rw [valuation_comap_eq_valuationOver, valuation_comap_eq_valuationOver]
  change EW.valuationOver (g₂ ≫ ψ) = E'.E.valuationOver (E'.f ≫ fp)
  have h1 : EW.valuationOver (g₁ ≫ E'.f) = E'.E.valuationOver E'.f := hEW
  rw [valuationOver_of_comp_eq EW (show (g₁ ≫ E'.f) ≫ fp = g₂ ≫ ψ by rw [← hc, Category.assoc]),
    h1]
  exact (valuationOver_of_comp_eq E'.E rfl).symm

end StepTransport

/-! ### The steps of the program -/

section Step

variable {X Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Z]
  {sZ : Z ⟶ Spec (.of ℂ)} {B : QDivisor X} {f : X ⟶ Z} [IsDominant f]

/-- The flip transform commutes with regarding a divisor as a `ℚ`-divisor. -/
private theorem flipTransform_toQDivisor {X Y X' : Scheme.{0}} (f : X ⟶ Y) (fp : X' ⟶ Y)
    (D : Divisor X) :
    flipTransform f fp (Divisor.toQDivisor D) = Divisor.toQDivisor (flipTransform f fp D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, MMP.Flips.transformDivisor_toQDivisor,
    MMP.Threefold.Resolution.inverseTransformDivisor_toQDivisor]

/-- A flip `f⁺ : X⁺ ⟶ Z` onto a projective variety is a projective morphism: it is proper and
carries a relatively ample Cartier divisor. -/
private theorem isProjectiveMorphism_of_isFlip {X Z Xp : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z}
    {fp : Xp ⟶ Z} (hfl : IsFlip sX sZ sXp K B f fp) : IsProjectiveMorphism fp := by
  haveI : AlgebraicGeometry.IsVariety ℂ sXp := hfl.isNormalVariety.1
  haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZ.toIsVariety
  haveI : IsProper fp := hfl.isProper
  obtain ⟨m, -, L, hL, -, hamp⟩ := hfl.hasRelativelyAmpleMultiple
  have hproj : IsProjective fp :=
    MMP.isProjective_of_isProper_of_divisor_isRelativelyAmple ℂ sXp sZ fp hfl.comp_eq L hL hamp
  obtain ⟨M, hM, hMa⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of ℂ))
  obtain ⟨H, hH, hHa⟩ := exists_isAmple_of_isProjectiveMorphism sZ M hMa hZ.isProjective
  exact ((isProjective_tfae_seven_of_exists_isAmple fp ⟨H, hH, hHa⟩).out 1 2).mp hproj

/-- The identity of a normal variety is a small morphism. -/
private theorem isSmallMorphism_id {k : Type} [Field k] {V : Scheme.{0}}
    {sV : V ⟶ Spec (.of k)} (hV : IsNormalVariety k sV) : IsSmallMorphism sV sV (𝟙 V) where
  isNormalVariety_source := hV
  isNormalVariety_target := hV
  comp_eq := Category.id_comp _
  isProper := inferInstance
  isBirationalMorphism := isBirationalMorphism_of_isIso _
  two_le_codimension := by
    rw [(exceptionalSet_eq_bot_iff (𝟙 V)).mpr inferInstance, le_closedsCodimension_iff]
    intro W hW
    obtain ⟨x, hx⟩ := W.isIrreducible.nonempty
    exact absurd (hW hx) (by simp)

/-- **The invariants survive a step.** Let `ψ : U ⟶ V` be a proper birational contraction over `Z`
of a model `S` with the invariants, `K + Δ` negative on the curves it contracts, and
`f⁺ : U' ⟶ V` a small morphism over `Z` (a flip, or an isomorphism) from a projective
`ℚ`-factorial dlt fourfold `(U', Δ')`, `Δ' = (f⁺)⁻¹_* ψ_* Δ`, with `K' + Δ'` nef over `V`. Then
the model `S'` has the invariants. -/
private theorem Stage.good_of_step (hZn : IsNormalVariety ℂ sZ) {S : Stage Z}
    (hS : S.Good sZ B f) (S' : Stage Z) {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V]
    [IsNormal V] {sV : V ⟶ Spec (.of ℂ)} (hVn : IsNormalVariety ℂ sV) {ψ : S.U ⟶ V} {g : V ⟶ Z}
    {fp : S'.U ⟶ V} [IsProper ψ] (hψb : IsBirationalMorphism ψ) (hψV : ψ ≫ sV = S.sU)
    (hψg : ψ ≫ g = S.h) (hgb : IsBirationalMorphism g) (hfp : IsSmallMorphism S'.sU sV fp)
    (hfpg : fp ≫ g = S'.h) (hΔ' : S'.Δ = flipTransform ψ fp S.Δ)
    (hpair' : IsProjectiveQFactorialDltPair S'.sU S'.K S'.Δ)
    (hcan' : S'.K.IsCanonicalDivisor S'.sU 4) (hcomp' : S'.h ≫ sZ = S'.sU)
    (hproj' : IsProjectiveMorphism S'.h)
    (hneg : ∀ C : ProperCurve S.sU, C.IsContractedBy ψ →
      ∀ hQ : (Divisor.toQDivisor S.K + S.Δ).IsQCartier,
        (Divisor.toQDivisor S.K + S.Δ).intersectionNumber ℂ S.sU C.ι C.dim_le hQ < 0)
    (hnef' : QDivisor.IsRelativelyNef S'.sU fp (Divisor.toQDivisor S'.K + S'.Δ)) :
    S'.Good sZ B f := by
  haveI := hψb.isDominant
  haveI := hfp.isBirationalMorphism.isDominant
  haveI : IsProper fp := hfp.isProper
  haveI := hgb.isDominant
  haveI := isSeparated_toTerminal_of_isNormalVariety hVn
  have hfpb := hfp.isBirationalMorphism
  have hfpV : fp ≫ sV = S'.sU := hfp.comp_eq
  have hb' : IsBirationalMorphism S'.h :=
    hfpg ▸ MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hfpb hgb
  haveI := hS.bir.isDominant
  haveI := hb'.isDominant
  have hUn : IsNormalVariety ℂ S.sU := hS.pair.isDltPair.1.1.1
  have hU'n : IsNormalVariety ℂ S'.sU := hpair'.isDltPair.1.1.1
  have htrans : ∀ F' : PrimeDivisor S'.U, ∃ F : PrimeDivisor S.U,
      F.valuationOver S.h = F'.valuationOver S'.h ∧ S'.Δ.coeff F' = S.Δ.coeff F := by
    intro F'
    obtain ⟨F, hFv, hco⟩ :=
      exists_primeDivisor_valuationOver_eq_and_flipTransform_apply hVn hψb hfp F' S.Δ
    exact ⟨F, by rw [valuationOver_of_comp_eq F hψg, valuationOver_of_comp_eq F' hfpg, hFv], by rw [hΔ', hco]⟩
  have hcoeff_eq : ∀ (F' : PrimeDivisor S'.U) (D : PrimeDivisor X),
      F'.valuationOver S'.h = D.valuationOver f → S'.Δ.coeff F' = B.coeff D := by
    intro F' D h
    obtain ⟨F, hFv, hco⟩ := htrans F'
    rw [hco]
    exact hS.coeff_eq F D (hFv.trans h)
  refine
    { pair := hpair'
      canonical := hcan'
      comp := hcomp'
      proj := hproj'
      bir := hb'
      coeff_eq := hcoeff_eq
      coeff_one := ?_
      discrep := ?_ }
  · intro F' hF'
    obtain ⟨F, hFv, hco⟩ := htrans F'
    rw [hco]
    exact hS.coeff_one F fun D h => hF' D (hFv.symm.trans h)
  · intro D E' hE'p hE'v c' hc'
    by_cases hA : ∃ F' : PrimeDivisor S'.U, F'.valuationOver S'.h = D.valuationOver f
    · obtain ⟨F', hF'⟩ := hA
      have hv : E'.valuation = F'.divisorialValuation :=
        MMP.Fourfold.Oai4C1.valuation_eq_of_comap_eq hb'.functionFieldMap_bijective.2
          (hE'v.trans hF'.symm)
      have e := eq_neg_coeff_of_valuation_eq hU'n hv hc'
      rw [e, hcoeff_eq F' D hF']
      exact ⟨le_rfl, fun h => absurd hF' (h F')⟩
    · push Not at hA
      obtain ⟨E, hEp, hEv⟩ :=
        exists_divisorOver_valuation_comap_eq hUn hψb hψV hfpb hfpV E' hE'p
      have hEZ : E.valuation.comap (functionFieldMap S.h) = D.valuationOver f := by
        rw [comap_functionFieldMap_of_comp_eq hψg, hEv, ← comap_functionFieldMap_of_comp_eq hfpg]
        exact hE'v
      obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hS.pair.isDltPair.1.1
        hS.canonical E
      obtain ⟨hle, hlt⟩ := hS.discrep D E hEp hEZ c hc
      have hexc : RationalMap.IsExceptional (X := E.Y) (E.f ≫ ψ).toRationalMap E.E := by
        by_contra hne
        obtain ⟨Q, hQ⟩ := exists_primeDivisor_of_not_isExceptional hVn hψV hψb E hne
        obtain ⟨F', hF'⟩ := exists_primeDivisor_valuationOver_eq_of_small hfp Q
        apply hA F'
        rw [valuationOver_of_comp_eq F' hfpg, hF', ← hQ, ← comap_functionFieldMap_of_comp_eq hψg]
        exact hEZ
      have hQD : (Divisor.toQDivisor S.K + S.Δ).IsQCartier :=
        isQCartier_of_isQFactorial S.sU hS.pair.isQFactorial _
      have hΔeq : RationalMap.transformDivisor (X := S.U) ψ.toRationalMap S.Δ =
          RationalMap.transformDivisor (X := S'.U) fp.toRationalMap S'.Δ := by
        rw [hΔ']
        exact (transformDivisor_inverseTransformDivisor fp hfpb _).symm
      have hN := isRelativelyNef_neg_of_forall_intersectionNumber_neg (f := ψ) hQD hneg
      have hle' : c ≤ c' := MMP.Mori.isDiscrepancy_le_of_isRelativelyNef hUn hU'n hVn hψV hfpV
        hψb hfpb hS.canonical hcan' hΔeq hN hnef' E E' hEv hexc hc hc'
      have hstrict : -B.coeff D < c' := by
        by_cases hFex : ∃ F : PrimeDivisor S.U, F.valuationOver S.h = D.valuationOver f
        · obtain ⟨F, hF⟩ := hFex
          have hEF : E.valuation = F.divisorialValuation :=
            MMP.Fourfold.Oai4C1.valuation_eq_of_comap_eq hS.bir.functionFieldMap_bijective.2
              (hEZ.trans hF.symm)
          have hηE : E.f E.E.genericPoint = F.genericPoint :=
            MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hUn.1 (D := E)
              (D' := DivisorOver.ofPrimeDivisor ℂ hUn F)
              (by rw [valuation_ofPrimeDivisor]; exact hEF)
          have hW : ψ (E.f E.E.genericPoint) ∉ biregularLocus ψ := by
            rw [hηE]
            intro hreg
            obtain ⟨Q, hQ⟩ := exists_primeDivisor_of_mem_biregularLocus hψb F hreg
            obtain ⟨F', hF'⟩ := exists_primeDivisor_valuationOver_eq_of_small hfp Q
            apply hA F'
            rw [valuationOver_of_comp_eq F' hfpg, hF', ← hQ, ← valuationOver_of_comp_eq F hψg, hF]
          have := MMP.Mori.isDiscrepancy_lt_of_forall_intersectionNumber_neg hUn hU'n hVn hψV
            hfpV hψb hfpb hS.canonical hcan' hΔeq hN hnef' hneg E E' hEv hexc hW hc hc'
          linarith
        · push Not at hFex
          exact lt_of_lt_of_le (hlt hFex) hle'
      exact ⟨hstrict.le, fun _ => hstrict⟩

/-- **One step of the program over `Z`.** A model whose adjoint is not nef over `Z` has an
elementary dlt step, whose output is again a model with the same invariants. -/
private theorem Stage.exists_step (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hZn : IsNormalVariety ℂ sZ) (hZd : topologicalKrullDim Z = 4) (S : Stage Z)
    (hS : S.Good sZ B f)
    (hnef : ¬ QDivisor.IsRelativelyNef S.sU S.h (Divisor.toQDivisor S.K + S.Δ)) :
    ∃ S' : Stage Z, S'.Good sZ B f ∧
      ∃ (V : Scheme.{0}) (sV : V ⟶ Spec (.of ℂ)) (R : Set (NumericalCurveClasses S.sU))
        (g : S.U ⟶ V) (gp : S'.U ⟶ V),
        IsProjectiveElementaryDltStep S.sU sV S'.sU S.K S.Δ R g gp S'.Δ := by
  have hU := hS.pair.isProjectiveVariety
  obtain ⟨V, _, _, _, _, sV, R, ψ, g, hR, hcon, hψb, hψg, hgV, hgp, hgb, hVp, hneg⟩ :=
    exists_isContractionOfRay_comp_eq hU hZ hS.pair.isQFactorial hS.canonical hS.pair.isDltPair
      hS.comp hS.bir hnef
  haveI : IsProper ψ := isProper_of_isProjectiveMorphism ψ hcon.isProjectiveMorphism
  have hVn := hcon.isNormalVariety_target
  haveI : QuasiCompact sV := hVp.toIsVariety.toQuasiCompact
  haveI : LocallyOfFiniteType sV := hVp.toIsVariety.toLocallyOfFiniteType
  have hUd : topologicalKrullDim S.U = 4 := hS.canonical.topologicalKrullDim_eq
  by_cases hsm : IsSmallMorphism S.sU sV ψ
  · -- a small contraction: the flip
    obtain ⟨Xp, _, _, _, sXp, fp, hfl⟩ := exists_isFlip_of_isDltPair_of_isContractionOfRay S.sU hU
      hS.pair.isQFactorial hUd hS.pair.isDltPair hS.canonical hR sV hcon hsm
    haveI : IsIntegral Xp := hfl.isNormalVariety.1.toIsIntegral
    haveI : LocallyOfFiniteType sXp := hfl.isNormalVariety.1.toLocallyOfFiniteType
    haveI : QuasiCompact sXp := hfl.isNormalVariety.1.toQuasiCompact
    have hfpp : IsProjectiveMorphism fp := isProjectiveMorphism_of_isFlip hVp hfl
    have hXpp : MMP.Mori.IsProjectiveVariety ℂ sXp := by
      haveI := hfl.isNormalVariety.1
      exact ⟨by rw [← hfl.comp_eq]; exact hfpp.comp hVp.isProjective⟩
    have hsmp : IsSmallMorphism sXp sV fp := ⟨hfl.isNormalVariety, hVn, hfl.comp_eq,
      hfl.isProper, hfl.isBirationalMorphism, hfl.two_le_codimension⟩
    have hflipOf : IsFlipOf S.sU sV sXp (Divisor.toQDivisor S.K + S.Δ) ψ fp :=
      { isQCartier := hR.1
        isContraction := hcon.toIsContraction
        isSmallMorphism := hsm
        hasRelativelyAmpleMultiple := hfl.isFlippingContraction.hasRelativelyAmpleMultiple
        isSmallMorphism_flip := hsmp
        isProjectiveMorphism_flip := hfpp
        isQCartier_flip := by rw [map_add, flipTransform_toQDivisor]; exact hfl.isQCartier
        hasRelativelyAmpleMultiple_flip := by
          rw [map_add, flipTransform_toQDivisor]; exact hfl.hasRelativelyAmpleMultiple }
    have hstep : IsProjectiveElementaryDltStep S.sU sV sXp S.K S.Δ R ψ fp
        (flipTransform ψ fp S.Δ) :=
      { isProjectiveQFactorialDltPair := hS.pair
        isNegativeExtremalRayOf := hR
        isContractionOfRay := hcon
        isBirationalMorphism := hψb
        comp_eq := hfl.comp_eq
        eq_flipTransform := rfl
        flip_or_divisorial := Or.inl ⟨hsm, hflipOf⟩ }
    obtain ⟨hQ', hdlt'⟩ := hstep.isQFactorial_and_isDltPair
    have hK' : Divisor.IsCanonicalDivisor sXp 4 (flipTransform ψ fp S.K) :=
      MMP.Mori.IsFlip.isCanonicalDivisor_flipTransform hS.canonical hfl
    let S' : Stage Z :=
      { U := Xp, sU := sXp, K := flipTransform ψ fp S.K, Δ := flipTransform ψ fp S.Δ,
        h := fp ≫ g }
    refine ⟨S', ?_, V, sV, R, ψ, fp, hstep⟩
    exact Stage.good_of_step hZn hS S' hVn hψb hcon.comp_eq hψg hgb hsmp rfl rfl
      ⟨hXpp, hQ', ⟨4, hK'⟩, hdlt'⟩ hK'
      (by simp only [S', Category.assoc, hgV, hfl.comp_eq]) (hfpp.comp hgp) hneg
      (isRelativelyNef_of_hasRelativelyAmpleMultiple hfl.isQCartier hfl.hasRelativelyAmpleMultiple)
  · -- a divisorial contraction: the target itself
    have hstep : IsProjectiveElementaryDltStep S.sU sV sV S.K S.Δ R ψ (𝟙 V)
        (flipTransform ψ (𝟙 V) S.Δ) :=
      { isProjectiveQFactorialDltPair := hS.pair
        isNegativeExtremalRayOf := hR
        isContractionOfRay := hcon
        isBirationalMorphism := hψb
        comp_eq := Category.id_comp _
        eq_flipTransform := rfl
        flip_or_divisorial := Or.inr ⟨hsm, inferInstance⟩ }
    obtain ⟨hQ', hdlt'⟩ := hstep.isQFactorial_and_isDltPair
    haveI := hψb.isDominant
    obtain ⟨-, n₁, KV, hKV, -⟩ := hdlt'.1.1
    have hVd : topologicalKrullDim V = 4 := by
      haveI := hVp.toIsVariety
      haveI := hU.toIsVariety
      rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV S.sU hψb, hUd]
    have hn₁ : n₁ = 4 := by
      have e := hKV.topologicalKrullDim_eq.symm.trans hVd
      exact_mod_cast e
    subst hn₁
    let S' : Stage Z :=
      { U := V, sU := sV, K := KV, Δ := flipTransform ψ (𝟙 V) S.Δ, h := g }
    refine ⟨S', ?_, V, sV, R, ψ, 𝟙 V, hstep⟩
    exact Stage.good_of_step hZn hS S' hVn hψb hcon.comp_eq hψg hgb (isSmallMorphism_id hVn)
      (Category.id_comp _) rfl ⟨hVp, hQ', ⟨4, hKV⟩, hdlt'⟩ hKV hgV hgp hneg
      (isRelativelyNef_id (isQCartier_of_isQFactorial sV hQ' _))

/-- **Termination.** Starting from a model with the invariants, the program over `Z` reaches a
model with the invariants whose adjoint is nef over `Z`. -/
private theorem Stage.exists_good_isRelativelyNef (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hZn : IsNormalVariety ℂ sZ) (hZd : topologicalKrullDim Z = 4) (S₀ : Stage Z)
    (hS₀ : S₀.Good sZ B f) :
    ∃ S : Stage Z, S.Good sZ B f ∧
      QDivisor.IsRelativelyNef S.sU S.h (Divisor.toQDivisor S.K + S.Δ) := by
  classical
  by_contra hcon
  push Not at hcon
  have hstep : ∀ S : {S : Stage Z // S.Good sZ B f}, ∃ S' : {S' : Stage Z // S'.Good sZ B f},
      ∃ (V : Scheme.{0}) (sV : V ⟶ Spec (.of ℂ)) (R : Set (NumericalCurveClasses S.1.sU))
        (g : S.1.U ⟶ V) (gp : S'.1.U ⟶ V),
        IsProjectiveElementaryDltStep S.1.sU sV S'.1.sU S.1.K S.1.Δ R g gp S'.1.Δ := by
    intro S
    obtain ⟨S', hS', h⟩ := S.1.exists_step hZ hZn hZd S.2 (hcon S.1 S.2)
    exact ⟨⟨S', hS'⟩, h⟩
  choose nxt V sV R g gp hst using hstep
  let seq : ℕ → {S : Stage Z // S.Good sZ B f} := fun n => Nat.rec ⟨S₀, hS₀⟩ (fun _ s => nxt s) n
  let s0 := (seq 0).1
  let Y : ℕ → Scheme.{0} := fun j => (seq (j + 1)).1.U
  let sY : ∀ j, Y j ⟶ Spec (.of ℂ) := fun j => (seq (j + 1)).1.sU
  let P : ElementaryDltProgram s0.sU s0.K s0.Δ :=
    { n := ⊤
      Y := Y
      sY := sY
      isIntegral := fun j => inferInstanceAs (IsIntegral (seq (j + 1)).1.U)
      compactSpace := fun j => inferInstanceAs (CompactSpace (seq (j + 1)).1.U)
      isLocallyNoetherian := fun j => inferInstanceAs (IsLocallyNoetherian (seq (j + 1)).1.U)
      isNormal := fun j => inferInstanceAs (IsNormal (seq (j + 1)).1.U)
      KY := fun j => (seq (j + 1)).1.K
      ΔY := fun j => (seq (j + 1)).1.Δ
      R := fun j => Nat.casesOn (motive := fun j => Set (NumericalCurveClasses (modelStr s0.sU sY j)))
        j (R (seq 0)) (fun j => R (seq (j + 1)))
      V := fun j => V (seq j)
      sV := fun j => sV (seq j)
      f := fun j => Nat.casesOn (motive := fun j => modelSeq s0.U Y j ⟶ V (seq j))
        j (g (seq 0)) (fun j => g (seq (j + 1)))
      fp := fun j => gp (seq j)
      isProjectiveQFactorialDltPair := fun j _ => Nat.casesOn (motive := fun j =>
          IsProjectiveQFactorialDltPair (modelStr s0.sU sY j)
            (divisorSeq s0.K (fun j => (seq (j + 1)).1.K) j)
            (divisorSeq s0.Δ (fun j => (seq (j + 1)).1.Δ) j))
        j (seq 0).2.pair (fun j => (seq (j + 1)).2.pair)
      isProjectiveElementaryDltStep := fun j _ => Nat.casesOn (motive := fun j =>
          IsProjectiveElementaryDltStep (modelStr s0.sU sY j) (sV (seq j)) (sY j)
            (divisorSeq s0.K (fun j => (seq (j + 1)).1.K) j)
            (divisorSeq s0.Δ (fun j => (seq (j + 1)).1.Δ) j)
            (Nat.casesOn (motive := fun j => Set (NumericalCurveClasses (modelStr s0.sU sY j)))
              j (R (seq 0)) (fun j => R (seq (j + 1))))
            (Nat.casesOn (motive := fun j => modelSeq s0.U Y j ⟶ V (seq j))
              j (g (seq 0)) (fun j => g (seq (j + 1))))
            (gp (seq j)) ((seq (j + 1)).1.Δ))
        j (hst (seq 0)) (fun j => hst (seq (j + 1))) }
  exact ElementaryDltProgram.n_ne_top (seq 0).2.canonical.topologicalKrullDim_eq P rfl

end Step

/-! ### The first model and the last -/

section Ends

variable {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral Z]
  {B : QDivisor X} {f : X ⟶ Z} [IsDominant f]

/-- **The first model.** The crepant `ℚ`-factorial dlt modification of `(X, B)` is a model over
`Z` with the invariants. -/
private theorem exists_good_stage (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ) (hf : f ≫ sZ = sX)
    (hfp : IsProjectiveMorphism f) (hfb : IsBirationalMorphism f) :
    ∃ S : Stage Z, S.Good sZ B f := by
  have hXn : IsNormalVariety ℂ sX := hB.1.1
  obtain ⟨-, n₀, K, hK₀, -⟩ := hB.1
  have hn₀ : n₀ = 4 := by
    have e := hK₀.topologicalKrullDim_eq.symm.trans hdim
    exact_mod_cast e
  subst hn₀
  obtain ⟨U, _, _, _, p, Δ, hl⟩ := exists_isCrepantDltLift sX hX hdim hK₀ hB
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hl.isProjectiveMorphism
  have hUn : IsNormalVariety ℂ (p ≫ sX) := hl.isQFactorial.1
  haveI : LocallyOfFiniteType (p ≫ sX) := hUn.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  haveI : QuasiCompact (p ≫ sX) := inferInstance
  haveI : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  have hpb := hl.isBirationalMorphism
  have hUd : topologicalKrullDim U = 4 := by
    haveI := hUn.1
    haveI := hX.toIsVariety
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hpb, hdim]
  obtain ⟨-, n₁, KU, hKU, -⟩ := hl.isDltPair.1.1
  have hn₁ : n₁ = 4 := by
    have e := hKU.topologicalKrullDim_eq.symm.trans hUd
    exact_mod_cast e
  subst hn₁
  have hbS : IsBirationalMorphism (p ≫ f) := MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hpb hfb
  haveI := hbS.isDominant
  haveI := hpb.isDominant
  have hval (F : PrimeDivisor U) := valuationOver_of_comp_eq F (rfl : p ≫ f = _)
  have hvalD : ∀ (F : PrimeDivisor U) (D : PrimeDivisor X),
      F.valuationOver (p ≫ f) = D.valuationOver f →
        F.valuationOver p = D.divisorialValuation := by
    intro F D h
    rw [hval] at h
    exact MMP.Fourfold.Oai4C1.valuation_eq_of_comap_eq hfb.functionFieldMap_bijective.2 h
  obtain ⟨n, hcrep⟩ := hl.isCrepantBoundary
  refine ⟨{ U := U, sU := p ≫ sX, K := KU, Δ := Δ, h := p ≫ f }, ?_⟩
  refine
    { pair := ⟨?_, hl.isQFactorial, ⟨4, hKU⟩, hl.isDltPair⟩
      canonical := hKU
      comp := by simp only [Category.assoc, hf]
      proj := hl.isProjectiveMorphism.comp hfp
      bir := hbS
      coeff_eq := ?_
      coeff_one := ?_
      discrep := ?_ }
  · haveI := hUn.1
    exact ⟨hl.isProjectiveMorphism.comp hX.isProjective⟩
  · intro F D hFD
    change Δ.coeff F = B.coeff D
    have hv := hvalD F D hFD
    have hη : p F.genericPoint = D.genericPoint :=
      MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hXn.1
        (D := ⟨U, p, hUn, hpb, F⟩) (D' := DivisorOver.ofPrimeDivisor ℂ hXn D) (by
          change F.valuationOver p = _
          rw [hv, valuation_ofPrimeDivisor])
    have e := eq_neg_coeff_of_map_genericPoint_eq hXn (D := ⟨U, p, hUn, hpb, F⟩) hη (hcrep F)
    linarith
  · intro F hF
    change Δ.coeff F = 1
    obtain ⟨E, hE, hΔ⟩ := hl.boundary_eq
    have hsub : F.support ⊆ MMP.Intersection.exceptionalLocus p := by
      by_contra hn
      obtain ⟨Q, hQ, -⟩ := MMP.Intersection.exists_primeDivisor_genericPoint_eq_of_not_subset hn
      apply hF Q
      rw [hval, MMP.Fourfold.Oai4C1.CommonModel.valuationOver_eq_of_map_genericPoint p
        hpb.functionFieldMap_bijective.2 F Q hQ.symm]
      rfl
    rw [hΔ, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, hE F, if_pos hsub,
      coeff_birationalInverseTransform_eq_zero_of_subset hXn hUn.1 hpb B F hsub]
    simp
  · intro D E hEp hED c hc
    change IsDiscrepancy (p ≫ sX) 4 KU Δ E c at hc
    -- the strict transform of `D` on `U`
    haveI : IsProper (show U ⟶ (DivisorOver.ofPrimeDivisor ℂ hXn D).Y from p) := ‹IsProper p›
    obtain ⟨F, hF⟩ := MMP.Fourfold.Oai4C1.CommonModel.exists_primeDivisor_valuation_eq
      (DivisorOver.ofPrimeDivisor ℂ hXn D) p hUn hpb p hpb (Category.comp_id p)
    have hFv : F.valuationOver (p ≫ f) = D.valuationOver f := by
      rw [hval]
      change (F.valuationOver p).comap _ = D.divisorialValuation.comap _
      congr 1
      rw [show F.valuationOver p = (⟨U, p, hUn, hpb, F⟩ : DivisorOver ℂ sX).valuation from rfl, hF,
        valuation_ofPrimeDivisor]
    have hn : n = 4 := by
      obtain ⟨-, hKn, -⟩ := hcrep F
      have e := hKn.topologicalKrullDim_eq.symm.trans hdim
      exact_mod_cast e
    subst hn
    have hEv : (DivisorOver.ofPrimeDivisor ℂ hXn D).valuation =
        E.valuation.comap (functionFieldMap p) := by
      have h1 : (E.valuation.comap (functionFieldMap p)).comap (functionFieldMap f) =
          D.divisorialValuation.comap (functionFieldMap f) :=
        (comap_functionFieldMap_of_comp_eq (h := p ≫ f) rfl E.valuation).symm.trans hED
      rw [valuation_ofPrimeDivisor]
      exact (MMP.Fourfold.Oai4C1.valuation_eq_of_comap_eq hfb.functionFieldMap_bijective.2 h1).symm
    obtain ⟨-, hiff⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hB.1 p hUn hpb hK₀ hKU
      (Or.inl (hcrep))
    have hc' := (hiff E (DivisorOver.ofPrimeDivisor ℂ hXn D) hEv c).mp hc
    have e := IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hXn hc'
    refine ⟨e.symm.le, fun hno => absurd hFv (hno F)⟩

/-- **The last model.** A model with the invariants whose adjoint is nef over `Z` is a log
minimal model of `(X/Z, B)`. -/
private theorem Stage.isLogMinimalModel (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ) (hf : f ≫ sZ = sX)
    (hfp : IsProjectiveMorphism f) (hfb : IsBirationalMorphism f) (S : Stage Z)
    (hS : S.Good sZ B f)
    (hnef : QDivisor.IsRelativelyNef S.sU S.h (Divisor.toQDivisor S.K + S.Δ)) :
    ∃ φ : X.RationalMap S.U, IsLogMinimalModel sX sZ S.sU f S.h B S.K S.Δ φ := by
  classical
  haveI : IsSeparated S.sU := hS.pair.isProjectiveVariety.toIsVariety.toIsSeparated
  haveI : IsProper S.h := isProper_of_isProjectiveMorphism _ hS.proj
  have hbS := hS.bir
  haveI := hbS.isDominant
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  haveI := isSeparated_terminal_from sZ
  haveI : Z.IsSeparated := ⟨by rw [← Limits.terminal.comp_from sZ]; infer_instance⟩
  haveI : IsSeparated sX := hX.toIsVariety.toIsSeparated
  haveI := isSeparated_terminal_from sX
  obtain ⟨φ, θ, hφb, hφ, hθs, hθh, hθ⟩ := exists_isBirational_compHom_eq_fromFunctionField hfb hbS
  have hT : ∀ (D : PrimeDivisor X) (F : PrimeDivisor S.U),
      RationalMap.transformPrimeDivisor φ D = some F ↔ D.valuationOver f = F.valuationOver S.h :=
    fun D F => transformPrimeDivisor_eq_some_iff_valuationOver_eq (sU := S.sU)
      hbS.functionFieldMap_bijective.2 hφ hθs hθh hθ D F
  have hXn : IsNormalVariety ℂ sX := hB.1.1
  refine ⟨φ,
    { isNormalVariety := hXn
      isLogCanonicalPair := hB
      comp_eq := hf
      isProjectiveMorphism := hfp
      comp_eq_model := hS.comp
      isProjectiveMorphism_model := hS.proj
      isBirational := hφb
      isOver := hφ
      coeff_boundary := ?_
      isQFactorial := hS.pair.isQFactorial
      isDltPair := hS.pair.isDltPair
      isCanonicalDivisor := ⟨4, hS.canonical⟩
      logDiscrepancy_lt := ?_
      isRelativelyNef := hnef }⟩
  · intro F
    by_cases hex : ∃ D : PrimeDivisor X, D.valuationOver f = F.valuationOver S.h
    · obtain ⟨D, hD⟩ := hex
      have h1 : RationalMap.transformPrimeDivisor φ D = some F := (hT D F).mpr hD
      have hnot : ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F := fun h => h D h1
      rw [if_neg hnot, add_zero, hS.coeff_eq F D hD.symm]
      change B D = DivisorWithCoeffs.mapPrimeDivisors (RationalMap.transformPrimeDivisor φ) B F
      rw [MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq h1 fun E' hE' =>
        primeDivisor_eq_of_valuationOver_eq hXn f hfb.functionFieldMap_bijective.2
          (((hT E' F).mp hE').trans hD.symm)]
    · push Not at hex
      have hnone : ∀ D, RationalMap.transformPrimeDivisor φ D ≠ some F :=
        fun D h => hex D ((hT D F).mp h)
      have hinv : MMP.Flips.RationalMap.IsInverseExceptional φ F := hnone
      rw [if_pos hinv, hS.coeff_one F (fun D h => hex D h.symm)]
      change (1 : ℚ) = DivisorWithCoeffs.mapPrimeDivisors _ B F + 1
      rw [MMP.Fourfold.Oai4C1.mapPrimeDivisors_apply_eq_zero hnone, zero_add]
  · intro D hDex ψ hψ E hE n a a' ha ha'
    have hnone : ∀ F : PrimeDivisor S.U, F.valuationOver S.h ≠ D.valuationOver f := fun F hF =>
      not_isExceptional_of_transformPrimeDivisor_eq_some ((hT D F).mpr hF.symm) hDex
    have hψ' := compHom_eq_of_isInverse hφ hψ
    have hval := valuation_comap_eq_of_isRealizedOver hψ' hE
    have ha1 := eq_of_isLogDiscrepancy_ofPrimeDivisor hB.1 hXn ha
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hS.pair.isDltPair.1.1
      hS.canonical E.toDivisorOver
    have hn : n = 4 := by
      have e := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha').symm.trans
        hS.canonical.topologicalKrullDim_eq
      exact_mod_cast e
    subst hn
    have ha2 := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha'
    have hlt := (hS.discrep D E.toDivisorOver E.isProper hval c hc).2 hnone
    rw [ha1, ha2]
    have : ((-B.coeff D : ℚ) : ℝ) < (c : ℝ) := by exact_mod_cast hlt
    push_cast at this
    linarith

end Ends

private theorem solution :
    ∀ {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    {f : X ⟶ Z} (hf : f ≫ sZ = sX) (hfp : IsProjectiveMorphism f)
    (hfb : IsBirationalMorphism f),
    ∃ (M : Scheme.{0}) (_ : IsIntegral M) (_ : CompactSpace M) (_ : IsLocallyNoetherian M)
      (_ : IsNormal M) (sM : M ⟶ Spec (.of ℂ)) (_ : LocallyOfFiniteType sM)
      (_ : QuasiCompact sM) (πM : M ⟶ Z) (KM : Divisor M) (BM : QDivisor M)
      (φ : X.RationalMap M),
      MMP.Mori.IsProjectiveVariety ℂ sM ∧ IsLogMinimalModel sX sZ sM f πM B KM BM φ := by
  intro X Z _ _ _ _ sX _ sZ hX hdim B hB hZ hZn f hf hfp hfb
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI : IsDominant f := hfb.isDominant
  have hZd : topologicalKrullDim Z = 4 := by
    haveI := hZ.toIsVariety
    haveI := hX.toIsVariety
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX hfb, hdim]
  obtain ⟨S₀, hS₀⟩ := exists_good_stage hX hdim hB hZ hZn hf hfp hfb
  obtain ⟨S, hS, hnef⟩ := Stage.exists_good_isRelativelyNef hZ hZn hZd S₀ hS₀
  obtain ⟨φ, hφ⟩ := Stage.isLogMinimalModel hX hB hZ hZn hf hfp hfb S hS hnef
  exact ⟨S.U, inferInstance, inferInstance, inferInstance, inferInstance, S.sU, inferInstance,
    inferInstance, S.h, S.K, S.Δ, φ, hS.pair.isProjectiveVariety, hφ⟩

end Proof_thm_fourfold_projective_lc_birational_log_model

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Log minimal models of projective lc fourfolds over a birational base.** Let `X` be a
projective fourfold over `ℂ` (`MMP.Mori.IsProjectiveVariety`), `B` a `ℚ`-divisor with `(X, B)`
log canonical (`MMP.Intersection.IsLogCanonicalPair`), and `f : X ⟶ Z` a projective birational
morphism (`MMP.Mori.IsBirationalMorphism`) over `ℂ` onto a normal projective variety `Z`. Then
there is a projective variety `M` over `ℂ` with a projective morphism `π_M : M ⟶ Z`, a canonical
divisor `K_M`, a `ℚ`-divisor `B_M` and a birational map `φ : X ⤏ M` over `Z` such that
`(M/Z, B_M)` is a log minimal model of `(X/Z, B)` (`MMP.Fourfold.IsLogMinimalModel`); in
particular `(M, B_M)` is `ℚ`-factorial and dlt. -/
@[mmp "thm_fourfold_projective_lc_birational_log_model"]
public theorem IsLogCanonicalPair.exists_isLogMinimalModel_of_isBirationalMorphism
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    {f : X ⟶ Z} (hf : f ≫ sZ = sX) (hfp : IsProjectiveMorphism f)
    (hfb : IsBirationalMorphism f) :
    ∃ (M : Scheme.{0}) (_ : IsIntegral M) (_ : CompactSpace M) (_ : IsLocallyNoetherian M)
      (_ : IsNormal M) (sM : M ⟶ Spec (.of ℂ)) (_ : LocallyOfFiniteType sM)
      (_ : QuasiCompact sM) (πM : M ⟶ Z) (KM : Divisor M) (BM : QDivisor M)
      (φ : X.RationalMap M),
      MMP.Mori.IsProjectiveVariety ℂ sM ∧ IsLogMinimalModel sX sZ sM f πM B KM BM φ :=
        by revert X Z sX sZ hX hdim B hB hZ hZn f hf hfp hfb; first | exact Proof_thm_fourfold_projective_lc_birational_log_model.solution | exact Proof_thm_fourfold_projective_lc_birational_log_model.solution _ | exact Proof_thm_fourfold_projective_lc_birational_log_model.solution _ _ | exact Proof_thm_fourfold_projective_lc_birational_log_model.solution _ _ _ | exact Proof_thm_fourfold_projective_lc_birational_log_model.solution _ _ _ _

end MMP.Fourfold

