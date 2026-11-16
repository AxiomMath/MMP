module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
public import MMP.AlgebraicGeometry.Positivity.RelativeEffectiveAdjoint
public import MMP.AlgebraicGeometry.Intersection.NumericallyTrivialTrace
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
public import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
public import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
public import MMP.AlgebraicGeometry.MMP.Fourfold.MinimalModel.RealSncEffective
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Resolution.LogResolutionAmpleSubtraction
public import MMP.AlgebraicGeometry.Positivity.AmpleNefBig
public import MMP.AlgebraicGeometry.Singularities.RealKltPolytope
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
public import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
public import MMP.AlgebraicGeometry.MMP.MinimalModel.RealKltCompactification
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
public import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.MMP.MinimalModel.NefModelEquivalence
public import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
public import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
public import MMP.AlgebraicGeometry.MMP.MinimalModel.CommonModelNefWeakModels
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.MinimalModel.LcModelNoExtractedDivisor
public import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
public import MMP.AlgebraicGeometry.Morphisms.HProjective

/-!
# Real klt fourfolds over a birational projective base have log minimal models

Let `π : X ⟶ Z` be a projective birational morphism of normal projective complex varieties, with
`X` a `ℚ`-factorial fourfold, and let `K_X` be a canonical divisor of `X`. Every effective real
klt pair `(X, B)` has a log minimal model `(Y/Z, B_Y)` over `Z`: a normal projective
`ℚ`-factorial pair with a birational map `φ : X ⤏ Y` over `Z` such that `K_Y + B_Y` is nef over
`Z` and the comparison of adjoints on a common resolution is effective, exceptional over `Y` and
positive along every prime divisor of `X` contracted on `Y`. Moreover `(Y, B_Y)` is klt and `φ`
extracts no prime divisor, so that `B_Y = φ_* B`.

## Main results

* `MMP.Fourfold.exists_isRealLogMinimalModel_of_isBirationalMorphism`: the existence of the
  klt log minimal model with no extracted divisor.

## Implementation notes

* The log minimal model is `MMP.Fourfold.IsRealLogMinimalModel`, which carries the projectivity
  and `ℚ`-factoriality of the model. The klt condition on the model is
  `MMP.Fourfold.IsRealKltPair`, and "extracts no prime divisor" says that no prime divisor of `Y`
  is exceptional over `X` (`MMP.Flips.RationalMap.IsInverseExceptional`).

## References

* [C. Birkar, *Existence of log canonical flips and a special LMMP*][BirkarLC]
-/

@[expose] public section

section

namespace Proof_thm_fourfold_real_birational_fourfold_log_model

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold MMP.Mori MMP.Flips

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section StrictTransforms

open MMP.Mori

variable {X W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W]

/-- A dominant morphism inducing an isomorphism of function fields induces an isomorphism of
local rings at every point lying over the generic point of a prime divisor. -/
private theorem isIso_stalkMap_of_map_eq_genericPoint (p : W ⟶ X) [IsDominant p]
    (hp : Function.Bijective (functionFieldMap p)) {w : W} {P : MMP.Mori.PrimeDivisor X}
    (hw : p w = P.genericPoint) : IsIso (p.stalkMap w) := by
  haveI : ValuationRing (X.presheaf.stalk P.genericPoint) := by
    haveI := P.isDiscreteValuationRing_localRing
    exact inferInstanceAs (ValuationRing P.localRing)
  haveI : ValuationRing (X.presheaf.stalk (p w)) := by rw [hw]; infer_instance
  exact MMP.Positivity.isIso_stalkMap_of_valuationRing p hp w

/-- For a separated dominant morphism inducing an isomorphism of function fields, at most one
point lies over the generic point of a prime divisor. -/
private theorem eq_of_map_eq_genericPoint (p : W ⟶ X) [IsSeparated p] [IsDominant p]
    (hp : Function.Bijective (functionFieldMap p)) {w w' : W} {P : MMP.Mori.PrimeDivisor X}
    (hw : p w = P.genericPoint) (hw' : p w' = P.genericPoint) : w = w' := by
  haveI := isIso_stalkMap_of_map_eq_genericPoint p hp hw
  haveI := isIso_stalkMap_of_map_eq_genericPoint p hp hw'
  haveI : ValuationRing (X.presheaf.stalk P.genericPoint) := by
    haveI := P.isDiscreteValuationRing_localRing
    exact inferInstanceAs (ValuationRing P.localRing)
  haveI : ValuationRing (X.presheaf.stalk (p w)) := by rw [hw]; infer_instance
  exact MMP.Positivity.eq_of_isIso_stalkMap p hp (hw'.trans hw.symm)

variable [IsSeparated (X ↘ ⊤_ Scheme)]

/-- An inverse `h` of a birational morphism `p`, evaluated at the generic point and followed by
`p`, is the canonical map `Spec k(X) ⟶ X`. -/
private theorem fromFunctionField_comp_of_isInverse [IsReduced W] {p : W ⟶ X}
    {h : X.RationalMap W} (hinv : RationalMap.IsInverse p.toRationalMap h) :
    h.fromFunctionField ≫ p = X.fromSpecStalk (genericPoint X) := by
  obtain ⟨ep, hep, rfl⟩ := hinv
  have hp1 : ep.source.ι ≫ p = ep.iso.hom ≫ ep.target.ι :=
    ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp hep)).symm
  have hηt : genericPoint X ∈ ep.target :=
    (genericPoint_specializes _).mem_open ep.target.2 ep.dense_target.nonempty.choose_spec
  change (ep.target.fromSpecStalkOfMem (genericPoint X) hηt ≫ ep.iso.inv ≫ ep.source.ι) ≫ p = _
  rw [Category.assoc, Category.assoc, hp1, Iso.inv_hom_id_assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- An inverse `h` of a birational morphism `p` satisfies `p ∘ h = id`. -/
private theorem compHom_eq_of_isInverse [IsReduced W] {p : W ⟶ X} {h : X.RationalMap W}
    (hinv : RationalMap.IsInverse p.toRationalMap h) :
    h.compHom p = Scheme.Hom.toRationalMap (𝟙 X) := by
  refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
  rw [MMP.Flips.RationalMap.fromFunctionField_compHom, fromFunctionField_comp_of_isInverse hinv,
    MMP.Flips.RationalMap.fromFunctionField_hom, Category.comp_id]

/-- Every representative `g` of an inverse of a birational morphism `p` satisfies
`g ≫ p = ι`. -/
private theorem hom_comp_eq_of_isInverse [IsReduced W] {p : W ⟶ X} {h : X.RationalMap W}
    (hinv : RationalMap.IsInverse p.toRationalMap h) (g : X.PartialMap W)
    (hg : g.toRationalMap = h) : g.hom ≫ p = g.domain.ι := by
  have h1 : (g.compHom p).toRationalMap = (Scheme.Hom.toPartialMap (𝟙 X)).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg]
    exact compHom_eq_of_isInverse hinv
  have h2 := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h1)
  exact h2.trans (Category.comp_id _)

/-- **The strict transform under the inverse of a resolution.** If `p : W ⟶ X` is a proper
birational morphism with inverse `h`, and the prime divisor `P_W` of `W` lies over the prime
divisor `P` of `X`, then `h` sends `P` to `P_W`. -/
private theorem transformPrimeDivisor_eq_some_of_isInverse [IsNormal W] [IsLocallyNoetherian W]
    [IsSeparated (W ↘ ⊤_ Scheme)]
    {p : W ⟶ X} [IsProper p] [IsDominant p] (hp : Function.Bijective (functionFieldMap p))
    {h : X.RationalMap W} (hinv : RationalMap.IsInverse p.toRationalMap h)
    {P : MMP.Mori.PrimeDivisor X} {PW : MMP.Mori.PrimeDivisor W}
    (hPW : p PW.genericPoint = P.genericPoint) :
    RationalMap.transformPrimeDivisor h P = some PW := by
  have := IsSeparated.of_comp p (X ↘ ⊤_ Scheme)
  have hdom : P.genericPoint ∈ h.domain :=
    MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 X) p h
      (compHom_eq_of_isInverse hinv) P.coheight_genericPoint.le
  obtain ⟨g, hgP, hg⟩ := RationalMap.definedAt_iff.mp hdom
  have hgp := hom_comp_eq_of_isInverse hinv g hg
  have hw : p (g.hom ⟨P.genericPoint, hgP⟩) = P.genericPoint := by
    change (g.hom ≫ p) ⟨P.genericPoint, hgP⟩ = _
    rw [hgp]; rfl
  exact MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq g hg hgP
    (eq_of_map_eq_genericPoint p hp hPW hw)

/-- If the inverse `h` of a birational morphism `p` sends `P` to `P'`, then `p` sends the
generic point of `P'` to that of `P`. -/
private theorem map_genericPoint_of_transformPrimeDivisor_eq_some [IsReduced W]
    [IsSeparated (W ↘ ⊤_ Scheme)] {p : W ⟶ X} {h : X.RationalMap W}
    (hinv : RationalMap.IsInverse p.toRationalMap h) {P : MMP.Mori.PrimeDivisor X}
    {P' : MMP.Mori.PrimeDivisor W} (hP : RationalMap.transformPrimeDivisor h P = some P') :
    p P'.genericPoint = P.genericPoint := by
  obtain ⟨hdef, -⟩ := RationalMap.transformPrimeDivisor_eq_some_iff.mp hP
  obtain ⟨g, hgP, hg⟩ := RationalMap.definedAt_iff.mp hdef
  rw [MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hP g hg hgP]
  change (g.hom ≫ p) ⟨P.genericPoint, hgP⟩ = _
  rw [hom_comp_eq_of_isInverse hinv g hg]; rfl

/-- If `h : X ⤏ W` sends the prime divisor `P` to `P'`, then `q ∘ h` sends `P` where the
morphism `q` sends `P'`. -/
private theorem transformPrimeDivisor_compHom {Y : Scheme.{0}} [IsReduced W]
    [IsSeparated (W ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] {h : X.RationalMap W}
    {P : MMP.Mori.PrimeDivisor X} {P' : MMP.Mori.PrimeDivisor W}
    (hP : RationalMap.transformPrimeDivisor h P = some P') (q : W ⟶ Y) :
    RationalMap.transformPrimeDivisor (h.compHom q) P =
      RationalMap.transformPrimeDivisor (X := W) q.toRationalMap P' := by
  obtain ⟨hdef, -⟩ := RationalMap.transformPrimeDivisor_eq_some_iff.mp hP
  obtain ⟨g', hg'P, hg'⟩ := RationalMap.definedAt_iff.mp hdef
  have hη := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hP g' hg' hg'P
  have hrep : (g'.compHom q).toRationalMap = h.compHom q := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg']
  refine Option.ext fun F => ?_
  rw [MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff]
  constructor
  · intro h1
    have h2 := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h1 (g'.compHom q) hrep
      hg'P
    rw [h2, hη]
    rfl
  · intro h1
    refine MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq (g'.compHom q) hrep hg'P ?_
    rw [← h1, hη]
    rfl

/-- If `h : X ⤏ W` sends the prime divisor `P` to `P'`, then `P` is exceptional for `q ∘ h`
exactly when `P'` is exceptional for the morphism `q`. -/
private theorem isExceptional_compHom_iff {Y : Scheme.{0}} [IsReduced W]
    [IsSeparated (W ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] {h : X.RationalMap W}
    {P : MMP.Mori.PrimeDivisor X} {P' : MMP.Mori.PrimeDivisor W}
    (hP : RationalMap.transformPrimeDivisor h P = some P') (q : W ⟶ Y) :
    RationalMap.IsExceptional (h.compHom q) P ↔
      RationalMap.IsExceptional (X := W) q.toRationalMap P' := by
  obtain ⟨hdef, -⟩ := RationalMap.transformPrimeDivisor_eq_some_iff.mp hP
  obtain ⟨g', hg'P, hg'⟩ := RationalMap.definedAt_iff.mp hdef
  have hη := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hP g' hg' hg'P
  have hrep : (g'.compHom q).toRationalMap = h.compHom q := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg']
  have hdef1 : RationalMap.DefinedAt (h.compHom q) P.genericPoint :=
    RationalMap.definedAt_iff.mpr ⟨g'.compHom q, hg'P, hrep⟩
  have hdef2 : RationalMap.DefinedAt (X := W) q.toRationalMap P'.genericPoint := by
    rw [RationalMap.DefinedAt, RationalMap.dom_toRationalMap_hom]
    trivial
  have htr : RationalMap.transform (h.compHom q) P.idealSheaf.support =
      RationalMap.transform (X := W) q.toRationalMap P'.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [MMP.Flips.coe_transform_eq_closure_singleton (g'.compHom q) hrep P hg'P,
      MMP.Flips.coe_transform_eq_closure_singleton q.toPartialMap rfl P' trivial]
    congr 2
    change q (g'.hom ⟨P.genericPoint, hg'P⟩) = q P'.genericPoint
    rw [hη]
  rw [RationalMap.isExceptional_iff, RationalMap.isExceptional_iff, htr]
  exact ⟨fun h1 _ => h1 hdef1, fun h1 _ => h1 hdef2⟩

/-- The coefficient of `f_* D` along `Q` is that of `D` along a prime divisor `P` over `Q`, for a
separated birational morphism. -/
private theorem coeff_transformDivisor_hom [IsNormal W] [IsLocallyNoetherian W]
    [IsSeparated (X ↘ ⊤_ Scheme)] {p : W ⟶ X} [IsSeparated p] [IsDominant p]
    (hp : Function.Bijective (functionFieldMap p)) (D : RDivisor W)
    {P : MMP.Mori.PrimeDivisor W} {Q : MMP.Mori.PrimeDivisor X}
    (hPQ : p P.genericPoint = Q.genericPoint) :
    (MMP.Mori.RationalMap.transformDivisor (X := W) p.toRationalMap D).coeff Q = D.coeff P := by
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p P Q).mpr hPQ)
    (fun P' hP' => ?_) D
  have h := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p P' Q).mp hP'
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_map_eq_genericPoint p hp h hPQ)

end StrictTransforms

section Exceptional

/-- A prime divisor `E` is exceptional for a morphism `q` exactly when `q(η_E)` has coheight at
least two. -/
private theorem isExceptional_toRationalMap_iff_two_le_coheight {W Y : Scheme.{0}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsSeparated (Y ↘ ⊤_ Scheme)] (q : W ⟶ Y) (E : MMP.Mori.PrimeDivisor W) :
    RationalMap.IsExceptional (X := W) q.toRationalMap E ↔ 2 ≤ Order.coheight (q E.genericPoint) := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff, MMP.Flips.le_closedsCodimension_iff_le_coheight]
  have hcl : (TopologicalSpace.Closeds.closure (q '' (E.idealSheaf.support : Set W)) : Set Y) =
      closure {q E.genericPoint} := by
    rw [TopologicalSpace.Closeds.coe_closure]
    have hs : (E.idealSheaf.support : Set W) = closure {E.genericPoint} :=
      AlgebraicGeometry.PrimeDivisor.support_eq_closure E
    rw [hs]
    refine le_antisymm ?_ ?_
    · refine closure_minimal ?_ isClosed_closure
      refine (image_closure_subset_closure_image q.continuous).trans ?_
      rw [Set.image_singleton]
    · refine closure_mono ?_
      rw [Set.singleton_subset_iff]
      exact ⟨E.genericPoint, subset_closure rfl, rfl⟩
  rw [hcl]
  refine ⟨fun h => h _ (subset_closure rfl), fun h x hx => ?_⟩
  have hsp : q E.genericPoint ⤳ x := specializes_iff_mem_closure.mpr hx
  exact h.trans (Order.coheight_anti (show x ≤ q E.genericPoint from hsp))

/-- The image of the generic point of an exceptional divisor over `Y` has coheight at least
two. -/
private theorem two_le_coheight_of_isExceptional {k : Type} [Field k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [LocallyOfFiniteType sY] [QuasiCompact sY]
    (D : ProperDivisorOver k sY) (hD : D.IsExceptional) {m : ℕ}
    (hdim : topologicalKrullDim Y = m) :
    2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  unfold ProperDivisorOver.IsExceptional at hD
  rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint,
    hdim] at hD
  set y := D.f D.E.genericPoint
  have hsum := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY y
  rw [hdim] at hsum
  obtain ⟨d, hd⟩ : ∃ d : ℕ∞, topologicalKrullDim (closure {y} : Set Y) = d := by
    refine WithBot.ne_bot_iff_exists.mp (fun h => ?_) |>.imp fun d hd => hd.symm
    rw [h, WithBot.bot_add] at hsum
    exact WithBot.bot_ne_coe hsum
  rw [hd] at hsum hD
  have hsum' : d + Order.coheight y = (m : ℕ∞) := by exact_mod_cast hsum
  have hD' : d + 2 ≤ (m : ℕ∞) := by
    exact_mod_cast (show ((d + 2 : ℕ∞) : WithBot ℕ∞) ≤ ((m : ℕ∞) : WithBot ℕ∞) by
      push_cast; exact hD)
  have hdtop : d ≠ ⊤ := fun h => by
    rw [h, top_add] at hsum'
    exact ENat.top_ne_coe _ hsum'
  rw [← hsum'] at hD'
  exact (ENat.add_le_add_iff_left hdtop).mp hD'

/-- A prime divisor which is not exceptional for a proper birational morphism onto a normal
scheme maps to the generic point of a prime divisor. -/
private theorem exists_primeDivisor_of_not_isExceptional_toRationalMap {W Y : Scheme.{0}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsSeparated (Y ↘ ⊤_ Scheme)] (q : W ⟶ Y) [IsProper q]
    (hq : IsBirationalMorphism q) (E : MMP.Mori.PrimeDivisor W)
    (hE : ¬ RationalMap.IsExceptional (X := W) q.toRationalMap E) :
    ∃ F : MMP.Mori.PrimeDivisor Y, q E.genericPoint = F.genericPoint := by
  rw [isExceptional_toRationalMap_iff_two_le_coheight, not_le] at hE
  have h1 : Order.coheight (q E.genericPoint) ≤ 1 := Order.le_of_lt_succ hE
  have hbir := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal q hq h1
  have hc : Order.coheight (q E.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus q hbir, E.coheight_genericPoint]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc).symm⟩

/-- A morphism out of a scheme separated over the terminal scheme is separated. -/
private theorem isSeparated_of_isSeparated_toTerminal {A B : Scheme.{0}} (f : A ⟶ B)
    [IsSeparated (A ↘ ⊤_ Scheme)] : IsSeparated f := by
  have h : f ≫ (B ↘ ⊤_ Scheme) = (A ↘ ⊤_ Scheme) := Limits.terminal.hom_ext _ _
  haveI : IsSeparated (f ≫ (B ↘ ⊤_ Scheme)) := by rw [h]; infer_instance
  exact IsSeparated.of_comp f (B ↘ ⊤_ Scheme)

end Exceptional

section KltTransfer

/-- The rational map of a morphism, composed with a morphism. -/
private theorem toRationalMap_compHom {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f.toRationalMap.compHom g = (f ≫ g).toRationalMap := by
  rw [Scheme.Hom.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.Hom.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨⊤, dense_univ, le_rfl, le_rfl, ?_⟩
  simp [Scheme.PartialMap.restrict, Scheme.PartialMap.compHom, Scheme.Hom.toPartialMap]

/-- A scheme separated over a field is separated over the terminal scheme. -/
private theorem isSeparated_terminal_of {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ Limits.terminal.from (Spec (.of k)) from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-- **Transforms through a common model.** Let `r : W ⟶ X₁` and `q : W ⟶ X₂` be proper birational
morphisms of normal varieties, `h` an inverse of `r` and `φ = q ∘ h`. If `φ⁻¹` contracts no prime
divisor, then `φ_* r_* D = q_* D` for every divisor `D` on `W`: at a prime divisor `F` of `X₂`,
both sides are the coefficient of `D` along the strict transform of `F` in `W`. -/
private theorem transformDivisor_transformDivisor_of_isInverse
    {X₁ X₂ W : Scheme.{0}} [IsIntegral X₁] [IsLocallyNoetherian X₁] [IsNormal X₁]
    [IsIntegral X₂] [IsLocallyNoetherian X₂] [IsNormal X₂]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {s₁ : X₁ ⟶ Spec (.of ℂ)} {s₂ : X₂ ⟶ Spec (.of ℂ)}
    (hX₁ : IsNormalVariety ℂ s₁) (hX₂ : IsNormalVariety ℂ s₂) {r : W ⟶ X₁} {q : W ⟶ X₂}
    (hW : IsNormalVariety ℂ (r ≫ s₁)) (hrq : r ≫ s₁ = q ≫ s₂) [IsProper r] [IsProper q]
    (hrb : IsBirationalMorphism r) (hqb : IsBirationalMorphism q) {h : X₁.RationalMap W}
    (hinv : MMP.Mori.RationalMap.IsInverse r.toRationalMap h) {φ : X₁.RationalMap X₂}
    (hφ : h.compHom q = φ)
    (hφE : ∀ F : MMP.Mori.PrimeDivisor X₂,
      ∃ R : MMP.Mori.PrimeDivisor X₁, MMP.Mori.RationalMap.transformPrimeDivisor φ R = some F)
    {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R W) :
    MMP.Mori.RationalMap.transformDivisor φ
        (MMP.Mori.RationalMap.transformDivisor r.toRationalMap D) =
      MMP.Mori.RationalMap.transformDivisor q.toRationalMap D := by
  haveI := hX₁.1.toIsSeparated
  haveI := hX₂.1.toIsSeparated
  haveI := isSeparated_terminal_of s₁
  haveI := isSeparated_terminal_of s₂
  haveI : IsSeparated r := IsSeparated.of_comp r s₁
  haveI : IsSeparated q := IsSeparated.of_comp q s₂
  haveI := hqb.isDominant
  have hW₂ : IsNormalVariety ℂ (q ≫ s₂) := hrq ▸ hW
  refine Finsupp.ext fun F => ?_
  obtain ⟨R₀, hR₀⟩ := hφE F
  obtain ⟨RW, hRW, -, hRWc⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX₁ hW hrb R₀
  obtain ⟨FW, hFW, -, hFWc⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX₂ hW₂ hqb F
  have := F.isDiscreteValuationRing_localRing
  -- every prime divisor of `X₁` with transform `F` has strict transform `F_W`
  have hkey : ∀ R' : MMP.Mori.PrimeDivisor X₁,
      MMP.Mori.RationalMap.transformPrimeDivisor φ R' = some F → R' = R₀ := by
    intro R' hR'
    obtain ⟨R'W, hR'W, -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX₁ hW hrb R'
    have h1 := (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse r hrb hinv q hφ R'
      R'W hR'W F).mp hR'
    have h2 := (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse r hrb hinv q hφ R₀
      RW hRW F).mp hR₀
    have h3 : R'W.genericPoint = RW.genericPoint :=
      MMP.Fourfold.eq_of_map_eq_of_valuationRing hqb.functionFieldMap_bijective h1 h2
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (hR'W.symm.trans ((congrArg r h3).trans hRW))
  have hRF : RW = FW := by
    have h2 := (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse r hrb hinv q hφ R₀
      RW hRW F).mp hR₀
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (MMP.Fourfold.eq_of_map_eq_of_valuationRing hqb.functionFieldMap_bijective h2 hFW)
  change DivisorWithCoeffs.mapPrimeDivisors _ _ F = _
  rw [MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hR₀ hkey, hRWc, hFWc, hRF]

/-- **Strict transforms through a common model are unique.** In the setting of
`transformDivisor_transformDivisor_of_isInverse`, two prime divisors of `X₁` with the same
transform `F` coincide: their strict transforms on `W` both map to the generic point of `F`. -/
private theorem eq_of_transformPrimeDivisor_eq_some_of_isInverse
    {X₁ X₂ W : Scheme.{0}} [IsIntegral X₁] [IsLocallyNoetherian X₁] [IsNormal X₁]
    [IsIntegral X₂] [IsLocallyNoetherian X₂] [IsNormal X₂]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {s₁ : X₁ ⟶ Spec (.of ℂ)} {s₂ : X₂ ⟶ Spec (.of ℂ)}
    (hX₁ : IsNormalVariety ℂ s₁) (hX₂ : IsNormalVariety ℂ s₂) {r : W ⟶ X₁} {q : W ⟶ X₂}
    (hW : IsNormalVariety ℂ (r ≫ s₁)) (hrq : r ≫ s₁ = q ≫ s₂) [IsProper r]
    (hrb : IsBirationalMorphism r) (hqb : IsBirationalMorphism q) {h : X₁.RationalMap W}
    (hinv : MMP.Mori.RationalMap.IsInverse r.toRationalMap h) {φ : X₁.RationalMap X₂}
    (hφ : h.compHom q = φ) {F : MMP.Mori.PrimeDivisor X₂} {R R' : MMP.Mori.PrimeDivisor X₁}
    (hR : MMP.Mori.RationalMap.transformPrimeDivisor φ R = some F)
    (hR' : MMP.Mori.RationalMap.transformPrimeDivisor φ R' = some F) : R = R' := by
  haveI := hX₁.1.toIsSeparated
  haveI := hX₂.1.toIsSeparated
  haveI := isSeparated_terminal_of s₁
  haveI := isSeparated_terminal_of s₂
  haveI : IsSeparated r := IsSeparated.of_comp r s₁
  haveI : IsSeparated (q ≫ s₂) := by rw [← hrq]; infer_instance
  haveI : IsSeparated q := IsSeparated.of_comp q s₂
  haveI := hqb.isDominant
  obtain ⟨RW, hRW, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX₁ hW hrb R
  obtain ⟨R'W, hR'W, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX₁ hW hrb R'
  have := F.isDiscreteValuationRing_localRing
  have h1 := (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse r hrb hinv q hφ R
    RW hRW F).mp hR
  have h2 := (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse r hrb hinv q hφ R'
    R'W hR'W F).mp hR'
  have h3 : RW.genericPoint = R'W.genericPoint :=
    MMP.Fourfold.eq_of_map_eq_of_valuationRing hqb.functionFieldMap_bijective h1 h2
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (hRW.symm.trans ((congrArg r h3).trans hR'W))

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is an `ℝ`-linear combination of Cartier
divisors. -/
private theorem isCartierCombination_of_isQFactorial {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsQFactorial sX) (D : RDivisor X) : IsCartierCombination D := by
  obtain ⟨m, r, L, hL, hD⟩ := MMP.Fourfold.IsQFactorial.isRCartier hX D
  refine ⟨m, r, L, hL, Finsupp.ext fun P => ?_⟩
  rw [Finset.sum_apply']
  refine (hD P).trans (Finset.sum_congr rfl fun j _ => ?_)
  simp [DivisorWithCoeffs.mapCoeffs, DivisorWithCoeffs.coeff]

/-- A rational map `φ⁻¹` contracts no prime divisor of the target exactly when every prime divisor
of the target is the transform of a prime divisor of the source. -/
private theorem exists_transformPrimeDivisor_eq_some_of_not_isInverseExceptional
    {X Y : Scheme.{0}} {φ : X.RationalMap Y}
    (hφE : ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    (F : MMP.Mori.PrimeDivisor Y) :
    ∃ R : MMP.Mori.PrimeDivisor X, MMP.Mori.RationalMap.transformPrimeDivisor φ R = some F := by
  by_contra h
  push Not at h
  exact hφE F h

/-- **Pull-backs along a composite.** If `G = f^*D` and `G'` is the pull-back of `D` along
`r ≫ f`, then `G'` is the pull-back of `G` along `r`. -/
private theorem isRCartierPullback_of_isRCartierPullback_comp {X Y W : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {f : Y ⟶ X} {r : W ⟶ Y} [IsDominant r] [IsDominant (r ≫ f)] {D : RDivisor X}
    {G' : RDivisor W} {G₀ : RDivisor Y} (hG : MMP.Flips.IsRCartierPullback f D G₀)
    (hG' : MMP.Flips.IsRCartierPullback (r ≫ f) D G') :
    MMP.Flips.IsRCartierPullback r G₀ G' := by
  obtain ⟨m, c, L, L', hL, hD, hpb, rfl⟩ := hG
  choose hB hp using hpb
  have hL'c : ∀ j, (L' j).IsCartier := fun j => (hp j).isCartier (hL j)
  let L'' : Fin m → Divisor W := fun j => (L' j).pullback (hL'c j)
    (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant r (L' j))
  have hp'' : ∀ j, (L' j).IsPullback r
      (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant r (L' j)) (L'' j) :=
    fun j => Divisor.isPullback_pullback (hL'c j) _
  have hcomp : MMP.Flips.IsRCartierPullback (r ≫ f) D (∑ j, c j • Divisor.toRDivisor (L'' j)) :=
    ⟨m, c, L, L'', hL, hD, fun j =>
      ⟨MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant (r ≫ f) (L j),
        MMP.ProgramBaseChange.divisor_isPullback_comp rfl (hp j) (hp'' j) _⟩, rfl⟩
  rw [MMP.Flips.IsRCartierPullback.eq (r ≫ f) hG' hcomp]
  exact ⟨m, c, L', L'', hL'c, rfl, fun j => ⟨_, hp'' j⟩, rfl⟩

/-- The push-forward along a composite of proper birational morphisms is the composite of the
push-forwards. -/
private theorem transformDivisor_comp_of_isBirationalMorphism {X W V : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) {p : W ⟶ X} {r : V ⟶ W}
    (hW : IsNormalVariety ℂ (p ≫ sX)) (hV : IsNormalVariety ℂ (r ≫ p ≫ sX)) [IsProper p]
    [IsProper r] (hpb : IsBirationalMorphism p) (hrb : IsBirationalMorphism r)
    {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R V) :
    MMP.Mori.RationalMap.transformDivisor p.toRationalMap
        (MMP.Mori.RationalMap.transformDivisor r.toRationalMap D) =
      MMP.Mori.RationalMap.transformDivisor (r ≫ p).toRationalMap D := by
  haveI := hX.1.toIsSeparated
  haveI := isSeparated_terminal_of sX
  haveI := hW.1.toIsSeparated
  haveI := isSeparated_terminal_of (p ≫ sX)
  haveI : IsProper (r ≫ p) := inferInstance
  have hrpb : IsBirationalMorphism (r ≫ p) :=
    MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hrb hpb
  set h := hrb.inverse
  have hinv : MMP.Mori.RationalMap.IsInverse r.toRationalMap h := hrb.isInverse_inverse
  have hψ : h.compHom (r ≫ p) = p.toRationalMap := by
    rw [← MMP.Fourfold.Oai4C1.Main.compHom_compHom, MMP.Fourfold.Crepant.compHom_eq_of_isInverse
        hinv,
      toRationalMap_compHom, Category.id_comp]
  have hE : ∀ F : MMP.Mori.PrimeDivisor X,
      ∃ P : MMP.Mori.PrimeDivisor W, MMP.Mori.RationalMap.transformPrimeDivisor p.toRationalMap P =
        some F := by
    intro F
    obtain ⟨P, hP, -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX hW hpb F
    exact ⟨P, (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p P F).mpr hP⟩
  have hV' : IsNormalVariety ℂ (r ≫ p ≫ sX) := hV
  exact transformDivisor_transformDivisor_of_isInverse hW hX (by rwa [← Category.assoc] at hV' ⊢)
    (by rw [Category.assoc]) hrb hrpb hinv hψ hE D

/-- **The log discrepancy of a prime divisor of a model.** If `K_M = div(ω)` and `K_W = div(f^*ω)`
on a model `f : W ⟶ M`, the log discrepancy of a prime divisor `E` of `W` with respect to
`(M, Δ)` is `1 + coeff_E K_W - coeff_E f^*(K_M + Δ)`. -/
private theorem isLogDiscrepancy_of_isRCartierPullback {M W : Scheme.{0}} [IsIntegral M]
    [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [CompactSpace W] {sM : M ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sM]
    {KM : Divisor M} {ΔM : RDivisor M} {f : W ⟶ M} [IsProper f] [IsDominant f] {G : RDivisor W}
    {e : ℕ} (hMn : IsNormalVariety ℂ sM) (hKM : KM.IsCanonicalDivisor sM e)
    (hWnf : IsNormalVariety ℂ (f ≫ sM)) (hfb : IsBirationalMorphism f) {KW : Divisor W}
    (ω : MMP.Mori.RationalPluriForms sM e 1) (hω0 : ω ≠ 0) (hωK : MMP.Mori.divisorOfForm ω = KM)
    (hωW : MMP.Mori.divisorOfForm (MMP.Mori.pullbackRationalPluriForms sM f ω) = KW)
    (hG : MMP.Flips.IsRCartierPullback f (logCanonicalDivisor KM ΔM) G)
    (E' : MMP.Mori.PrimeDivisor W) :
    MMP.Intersection.IsLogDiscrepancy sM e ΔM ⟨W, f, hWnf, hfb, E'⟩
      (1 + (KW.coeff E' : ℝ) - G.coeff E') := by
  obtain ⟨m, r, L, L', hLc, hD, hpbL, rfl⟩ := hG
  refine ⟨hMn, inferInstanceAs (IsProper f), ω, hω0, ⟨KM, hKM, fun Γ => by
    rw [← hωK]; exact MMP.Mori.coeff_divisorOfForm ω Γ⟩, m, r, L, L', hLc, fun Γ => ?_, hpbL, ?_⟩
  · have := congrArg (fun D : RDivisor M => D.coeff Γ) hD
    simp only [logCanonicalDivisor, DivisorWithCoeffs.coeff_add,
      Divisor.coeff_toRDivisor, MMP.Flips.coeff_sum_smul_toRDivisor] at this
    rw [← this, ← hωK, MMP.Mori.coeff_divisorOfForm]
  · rw [MMP.Flips.coeff_sum_smul_toRDivisor, ← hωW, MMP.Mori.coeff_divisorOfForm]
    rfl

/-- **A nef weak model of a klt pair is klt.** Let `φ : X ⤏ Y` be a nef weak model over `Z` of
the klt pair `(X, Δ)`, with `Y` `ℚ`-factorial. Then `(Y, φ_* Δ)` is klt: a divisor `E` over `Y`
is realized on a common smooth model `V` of its own model and of the resolution `W` of `φ`, and
with compatible canonical divisors `K_V` there,
`a(E; Y, φ_* Δ) - a(E; X, Δ) = coeff_E (p^*(K_X + Δ) - q^*(K_Y + φ_* Δ)) ≥ 0`. -/
private theorem isRealKltPair_transformDivisor_of_isNefWeakModel
    {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] [QuasiCompact sY] [IsSeparated sZ]
    {π : X ⟶ Z} {πY : Y ⟶ Z} {K : Divisor X} {Δ : RDivisor X} {φ : X.RationalMap Y}
    (N : IsNefWeakModel sX sY sZ π πY K Δ φ) (hYq : IsQFactorial sY)
    {KY : Divisor Y} {m : ℕ} (hKY : KY.IsCanonicalDivisor sY m) (hklt : IsRealKltPair sX Δ) :
    IsRealKltPair sY (MMP.Mori.RationalMap.transformDivisor φ Δ) := by
  classical
  have hXn : IsNormalVariety ℂ sX := N.isNormalVariety_source
  have hYn : IsNormalVariety ℂ sY := N.isNormalVariety_target
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  haveI := hXn.1.toIsSeparated
  haveI := hYn.1.toIsSeparated
  haveI := isSeparated_terminal_of sX
  haveI := isSeparated_terminal_of sY
  haveI := hYn.1
  obtain ⟨W, iW, lW, nW, sW, p, q, h, hWv, hWsm, hp, hq, hpp, hqp, hpb, hqb, hinv, hcomp, GY, GZ,
    hGY, hGZ, heff, -⟩ := N.exists_resolution
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqp
  haveI := hpb.isDominant
  haveI := hqb.isDominant
  haveI : QuasiCompact sW := hWv.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have hWnp : IsNormalVariety ℂ (p ≫ sX) := by rw [hp]; exact ⟨hWv, inferInstance⟩
  have hWnq : IsNormalVariety ℂ (q ≫ sY) := by rw [hq]; exact ⟨hWv, inferInstance⟩
  have hφE := exists_transformPrimeDivisor_eq_some_of_not_isInverseExceptional
    N.not_isInverseExceptional
  refine ⟨hYn, fun F => ?_, ⟨m, KY, hKY, MMP.Fourfold.IsQFactorial.isRCartier hYq _⟩,
    fun e E a ha => ?_⟩
  · -- coefficients below one
    obtain ⟨R, hR⟩ := hφE F
    have hc : (MMP.Mori.RationalMap.transformDivisor φ Δ).coeff F = Δ.coeff R :=
      MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hR (fun R' hR' =>
        eq_of_transformPrimeDivisor_eq_some_of_isInverse hXn hYn hWnp (hp.trans hq.symm) hpb hqb
          hinv hcomp hR' hR) Δ
    rw [hc]
    exact hklt.2.1 R
  · -- log discrepancies
    haveI := E.isIntegral
    haveI := E.isLocallyNoetherian
    haveI := E.isNormal
    haveI : IsProper E.f := ha.2.1
    obtain ⟨V, r, p', hVn, hVsm, hcomm, hrp, hrb, hp'p, hp'b⟩ :=
      MMP.Fourfold.exists_common_model_over sY E.f q E.isBirationalMorphism hqb E.isNormalVariety
        hWnq
    haveI := hVn.1.toIsIntegral
    haveI := hVn.2
    haveI : LocallyOfFiniteType (p' ≫ q ≫ sY) := hVn.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (p' ≫ q ≫ sY)
    haveI : QuasiCompact (p' ≫ q ≫ sY) := hVn.1.toQuasiCompact
    haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (p' ≫ q ≫ sY)
    haveI : IsProper r := isProper_of_isProjectiveMorphism r hrp
    haveI : IsProper p' := isProper_of_isProjectiveMorphism p' hp'p
    haveI := hp'b.isDominant
    haveI := hrb.isDominant
    set α : V ⟶ X := p' ≫ p with hαdef
    set β : V ⟶ Y := p' ≫ q with hβdef
    have hαb : IsBirationalMorphism α := MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp
        hp'b hpb
    have hβb : IsBirationalMorphism β := MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp
        hp'b hqb
    haveI := hαb.isDominant
    haveI := hβb.isDominant
    have hαs : α ≫ sX = p' ≫ q ≫ sY := by
      simp only [hαdef, Category.assoc, hp, hq]
    have hVα : IsNormalVariety ℂ (α ≫ sX) := by rw [hαs]; exact hVn
    have hVβ : IsNormalVariety ℂ (β ≫ sY) := by rw [hβdef, Category.assoc]; exact hVn
    haveI : LocallyOfFiniteType (α ≫ sX) := hVα.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (β ≫ sY) := hVβ.1.toLocallyOfFiniteType
    -- the strict transform of `E` on `V`
    obtain ⟨E'', hE''⟩ := MMP.Fourfold.Oai4C1.CommonModel.exists_primeDivisor_valuation_eq E β hVβ
      hβb r hrb (by rw [hcomm])
    -- compatible canonical divisors on `V`
    obtain ⟨n₀, hK⟩ := N.isCanonicalDivisor
    haveI := hXn.1
    haveI : MMP.Mori.IsVariety ℂ (α ≫ sX) := hVα.1
    have hdV : topologicalKrullDim V = n₀ :=
      (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (α ≫ sX) hαb).symm.trans
        hK.1
    have hsmα : IsSmoothScheme (α ≫ sX) := by rw [hαs]; exact hVsm
    obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (α ≫ sX) hsmα hdV
    obtain ⟨KV, hKV, hKVα⟩ :=
      MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hXn hVα hαb hK hK₀
    -- `β_* K_V = φ_* K`
    have hp'n : IsNormalVariety ℂ (p' ≫ p ≫ sX) := by rw [← Category.assoc]; exact hVα
    have hp'q : IsNormalVariety ℂ (p' ≫ q ≫ sY) := hVn
    have hKVβ : MMP.Mori.RationalMap.transformDivisor β.toRationalMap KV =
        MMP.Mori.RationalMap.transformDivisor φ K := by
      rw [← transformDivisor_comp_of_isBirationalMorphism hYn hWnq hp'q hqb hp'b,
        ← transformDivisor_transformDivisor_of_isInverse hXn hYn hWnp (hp.trans hq.symm) hpb hqb
          hinv hcomp hφE, transformDivisor_comp_of_isBirationalMorphism hXn hWnp hp'n hpb hp'b]
      change MMP.Mori.RationalMap.transformDivisor φ
        (MMP.Mori.RationalMap.transformDivisor α.toRationalMap KV) = _
      rw [hKVα]
    -- canonical forms
    obtain ⟨ω, hω0, hωK, hωV⟩ := MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hXn
      hVα hαb hK hKV hKVα
    haveI : MMP.Mori.IsVariety ℂ (β ≫ sY) := hVβ.1
    have hdY : topologicalKrullDim Y = n₀ :=
      (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (β ≫ sY) hβb).trans hdV
    obtain rfl : m = n₀ := by exact_mod_cast hKY.1.symm.trans hdY
    have hKV' : KV.IsCanonicalDivisor (β ≫ sY) m := by
      have e : β ≫ sY = α ≫ sX := by rw [hαs, hβdef, Category.assoc]
      rw [e]; exact hKV
    have hKYc := MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hYn hVβ hβb hKY hKV'
    obtain ⟨ωY, hωY0, hωYK, hωYV⟩ := MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq
      hYn hVβ hβb hKYc hKV' rfl
    -- pull-backs of the adjoints to `V`
    obtain ⟨Gα, hGα, -⟩ := MMP.Flips.existsUnique_isRCartierPullback α N.isCartierCombination
    have hGZc : IsCartierCombination (logCanonicalDivisor
        (MMP.Mori.RationalMap.transformDivisor β.toRationalMap KV)
        (MMP.Mori.RationalMap.transformDivisor φ Δ)) :=
      isCartierCombination_of_isQFactorial hYq _
    obtain ⟨Gβ, hGβ, -⟩ := MMP.Flips.existsUnique_isRCartierPullback β hGZc
    have hGα' : MMP.Flips.IsRCartierPullback p' GY Gα :=
      isRCartierPullback_of_isRCartierPullback_comp hGY hGα
    have hGβ' : MMP.Flips.IsRCartierPullback p' GZ Gβ :=
      isRCartierPullback_of_isRCartierPullback_comp (by rw [hKVβ]; exact hGZ) hGβ
    have hWq : IsQFactorial sW :=
      ⟨⟨hWv, inferInstance⟩, fun D => ⟨1, one_pos, by
        simpa using MMP.Fourfold.isCartier_of_isSmoothScheme hWsm D⟩⟩
    have hdiff : MMP.Flips.IsRCartierPullback p' (GY - GZ) (Gα - Gβ) := by
      have h1 := MMP.Fourfold.isRCartierPullback_smul (-1) hGβ'
      simp only [neg_one_smul] at h1
      have := MMP.Fourfold.isRCartierPullback_add hGα' h1
      simpa only [← sub_eq_add_neg] using this
    have hpos : 0 ≤ Gα - Gβ := (MMP.Fourfold.isEffective_of_isRCartierPullback p'
      (MMP.Fourfold.IsQFactorial.isRCartier hWq _) (fun P => heff P)).2 _ hdiff
    -- the two log discrepancies
    have hDY := isLogDiscrepancy_of_isRCartierPullback hYn hKYc hVβ hβb ωY hωY0 hωYK hωYV hGβ E''
    have hDX := isLogDiscrepancy_of_isRCartierPullback hXn hK hVα hαb ω hω0 hωK hωV hGα E''
    have ha' := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha hDY hE''.symm
    have hX0 := hklt.2.2.2 _ _ _ hDX
    have hE : 0 ≤ (Gα - Gβ).coeff E'' := hpos E''
    rw [DivisorWithCoeffs.coeff_sub] at hE
    rw [ha']
    linarith

/-- An effective klt pair is dlt: take the empty open set as the snc locus. -/
private theorem isRealDltPair_of_isRealKltPair {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {B : RDivisor X}
    (hB : ∀ P, 0 ≤ B.coeff P) (h : IsRealKltPair sX B) : IsRealDltPair sX B := by
  have hempty : IsEmpty ((⊤ : TopologicalSpace.Closeds X).compl : X.Opens) :=
    ⟨fun x => x.2 (by trivial)⟩
  refine ⟨⟨h.1, hB, h.2.2.1, fun n E a ha => (h.2.2.2 n E a ha).le⟩, fun P => (h.2.1 P).le, ⊤,
    ?_, ?_, fun n D _ a ha => h.2.2.2 n D a ha⟩
  · refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun x => ?_)
    exact isEmptyElim (α := ((⊤ : TopologicalSpace.Closeds X).compl : X.Opens)) x
  · refine ⟨fun E _ => ?_, fun x => ?_⟩
    · exact isEmptyElim (α := ((⊤ : TopologicalSpace.Closeds X).compl : X.Opens))
        (AlgebraicGeometry.PrimeDivisor.genericPoint E)
    · exact isEmptyElim (α := ((⊤ : TopologicalSpace.Closeds X).compl : X.Opens)) x

end KltTransfer

section NumericalTriviality

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {f : X ⟶ Y}

/-- An `ℝ`-Cartier divisor has an intersection number with every proper curve. -/
private theorem exists_isRIntersectionNumber' {N : RDivisor X} (hN : IsCartierCombination N)
    (C : ProperCurve sX) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber k sX N r L C x := by
  obtain ⟨m, r, L, hL, hNe⟩ := hN
  have hNe' : N = ∑ j, r j • Divisor.toRDivisor (L j) := by
    rw [hNe]; simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs]
  have := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r L hL
  rw [← hNe'] at this
  exact ⟨m, r, L, _, this⟩

/-- The intersection number of the zero divisor with a proper curve is zero. -/
private theorem isRIntersectionNumber_zero' (C : ProperCurve sX) :
    IsRIntersectionNumber k sX 0 (fun _ : Fin 0 => (0 : ℝ)) (fun _ => 0) C 0 := by
  have h0 := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C (fun _ : Fin 0 => (0 : ℝ))
    (fun _ => 0) (fun i => i.elim0)
  simpa using h0

/-- An `ℝ`-Cartier divisor all of whose intersection numbers with contracted curves vanish is
numerically trivial. -/
private theorem isNumericallyTrivialOver_of_forall {N : RDivisor X}
    (hN : IsCartierCombination N)
    (h : ∀ C : ProperCurve sX, C.IsContractedBy f → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor X) (x : ℝ), IsRIntersectionNumber k sX N r L C x → x = 0) :
    IsNumericallyTrivialOver k sX f N :=
  ⟨hN, ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun C hC _ _ _ x₁ _ _ _ x₂ hx₁ hx₂ => by
      rw [h C hC _ _ _ _ hx₁, (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _
        hx₂ (isRIntersectionNumber_zero' C)]⟩

/-- The intersection numbers of a numerically trivial divisor with contracted curves vanish. -/
private theorem eq_zero_of_isNumericallyTrivialOver {N : RDivisor X}
    (hN : IsNumericallyTrivialOver k sX f N) {C : ProperCurve sX} (hC : C.IsContractedBy f)
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber k sX N r L C x) : x = 0 :=
  hN.2.2 C hC _ _ _ _ _ _ _ _ hx (isRIntersectionNumber_zero' C)

/-- Linear combinations of numerically trivial divisors are numerically trivial. -/
private theorem isNumericallyTrivialOver_smul_add {N₁ N₂ : RDivisor X}
    (h₁ : IsNumericallyTrivialOver k sX f N₁) (h₂ : IsNumericallyTrivialOver k sX f N₂)
    (a b : ℝ) (hc : IsCartierCombination (a • N₁ + b • N₂)) :
    IsNumericallyTrivialOver k sX f (a • N₁ + b • N₂) := by
  refine isNumericallyTrivialOver_of_forall hc fun C hC m r L x hx => ?_
  obtain ⟨_, r₁, L₁, x₁, hx₁⟩ := exists_isRIntersectionNumber' h₁.1 C
  obtain ⟨_, r₂, L₂, x₂, hx₂⟩ := exists_isRIntersectionNumber' h₂.1 C
  have hlin := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).2 _ _ _ _ _ _ _ _ a b
    hx₁ hx₂
  rw [(MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx hlin,
    eq_zero_of_isNumericallyTrivialOver h₁ hC hx₁, eq_zero_of_isNumericallyTrivialOver h₂ hC hx₂]
  ring

/-- A principal divisor is numerically trivial. -/
private theorem isNumericallyTrivialOver_principalDivisor (φ : (RationalFunctions X)ˣ) :
    IsNumericallyTrivialOver k sX f (Divisor.toRDivisor (principalDivisor φ)) := by
  refine isNumericallyTrivialOver_of_forall
    ⟨1, fun _ => 1, fun _ => principalDivisor φ, fun _ => Divisor.isCartier_principalDivisor φ,
      by simp [← MMP.Flips.toRDivisor_eq_mapCoeffs]⟩ fun C hC m r L x hx => ?_
  exact MMP.Flips.eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent
    (Divisor.linearlyEquivalent_principalDivisor_zero φ) C hx

/-- Two `ℝ`-Cartier divisors whose difference is numerically trivial are numerically
equivalent. -/
private theorem isNumericallyEquivalentOver_of_sub {D₁ D₂ : RDivisor X}
    (h₁ : IsCartierCombination D₁) (h₂ : IsCartierCombination D₂)
    (h : IsNumericallyTrivialOver k sX f (D₁ - D₂)) : IsNumericallyEquivalentOver k sX f D₁ D₂ := by
  refine ⟨h₁, h₂, fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ hx₁ hx₂ => ?_⟩
  have hlin := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).2 _ _ _ _ _ _ _ _ 1 (-1)
    hx₁ hx₂
  have e : (1 : ℝ) • D₁ + (-1 : ℝ) • D₂ = D₁ - D₂ := by
    rw [one_smul, neg_one_smul, sub_eq_add_neg]
  rw [e] at hlin
  have := eq_zero_of_isNumericallyTrivialOver h hC hlin
  linarith

/-- The difference of two numerically equivalent divisors is numerically trivial. -/
private theorem isNumericallyTrivialOver_sub {D₁ D₂ : RDivisor X}
    (h : IsNumericallyEquivalentOver k sX f D₁ D₂) (hc : IsCartierCombination (D₁ - D₂)) :
    IsNumericallyTrivialOver k sX f (D₁ - D₂) := by
  refine isNumericallyTrivialOver_of_forall hc fun C hC m r L x hx => ?_
  obtain ⟨_, r₁, L₁, x₁, hx₁⟩ := exists_isRIntersectionNumber' h.1 C
  obtain ⟨_, r₂, L₂, x₂, hx₂⟩ := exists_isRIntersectionNumber' h.2.1 C
  have hlin := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).2 _ _ _ _ _ _ _ _ 1 (-1)
    hx₁ hx₂
  have e : (1 : ℝ) • D₁ + (-1 : ℝ) • D₂ = D₁ - D₂ := by
    rw [one_smul, neg_one_smul, sub_eq_add_neg]
  rw [e] at hlin
  rw [(MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx hlin,
    h.2.2 C hC _ _ _ _ _ _ _ _ hx₁ hx₂]
  ring

/-- A numerically trivial divisor is nef. -/
private theorem isRelativelyNef_of_isNumericallyTrivialOver' {N : RDivisor X}
    (h : IsNumericallyTrivialOver k sX f N) : IsRelativelyNef k sX f N := by
  obtain ⟨m, r, L, hL, hNe⟩ := h.1
  exact ⟨m, r, L, hL, by rw [hNe]; simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs],
    fun C hC x hx => (eq_zero_of_isNumericallyTrivialOver h hC hx).ge⟩

/-- A divisor which is nef together with its negative is numerically trivial. -/
private theorem isNumericallyTrivialOver_of_isRelativelyNef_neg'' {N : RDivisor X}
    (h₁ : IsRelativelyNef k sX f N) (h₂ : IsRelativelyNef k sX f (-N))
    (hc : IsCartierCombination N) : IsNumericallyTrivialOver k sX f N := by
  refine isNumericallyTrivialOver_of_forall hc fun C hC m r L x hx => ?_
  obtain ⟨m₁, r₁, L₁, hL₁, he₁, hn₁⟩ := h₁
  obtain ⟨m₂, r₂, L₂, hL₂, he₂, hn₂⟩ := h₂
  have hx₁ := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r₁ L₁ hL₁
  rw [← he₁] at hx₁
  have hx₂ := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r₂ L₂ hL₂
  rw [← he₂] at hx₂
  have a := hn₁ C hC _ hx₁
  have b := hn₂ C hC _ hx₂
  have hlin := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).2 _ _ _ _ _ _ _ _ (-1) 0
    hx₁ hx₁
  have e : (-1 : ℝ) • N + (0 : ℝ) • N = -N := by rw [neg_one_smul, zero_smul, add_zero]
  rw [e] at hlin
  have c := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx₂ hlin
  have d := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx hx₁
  linarith

/-- The pull-back of a divisor numerically trivial over `S` is numerically trivial over `S`. -/
private theorem isNumericallyTrivialOver_of_isRCartierPullback' [IsSeparated sX]
    [LocallyOfFiniteType sX] {W S : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [CompactSpace W] (p : W ⟶ X) [IsProper p] [QuasiCompact (p ≫ sX)]
    (π : X ⟶ S) {N : RDivisor X} {G : RDivisor W} (hN : IsNumericallyTrivialOver k sX π N)
    (hG : IsRCartierPullback p N G) : IsNumericallyTrivialOver k (p ≫ sX) (p ≫ π) G := by
  have hpq : (p ≫ π) ≫ 𝟙 S = p ≫ π := Category.comp_id _
  have h1 := MMP.Fourfold.isRelativelyNef_of_isRCartierPullback (𝟙 S) π (p ≫ π) p hpq
    (isRelativelyNef_of_isNumericallyTrivialOver' hN) hG
  have hN' : IsNumericallyTrivialOver k sX π (-N) := by
    have := isNumericallyTrivialOver_smul_add hN hN (-1) 0 (by
      rw [neg_one_smul, zero_smul, add_zero]
      obtain ⟨m, r, L, hL, hNe⟩ := hN.1
      exact ⟨m, -r, L, hL, by rw [hNe]; simp [Finset.sum_neg_distrib, neg_smul]⟩)
    rwa [neg_one_smul, zero_smul, add_zero] at this
  have hG' : IsRCartierPullback p (-N) (-G) := by
    have := MMP.Fourfold.isRCartierPullback_smul (-1) hG
    simpa only [neg_one_smul] using this
  have h2 := MMP.Fourfold.isRelativelyNef_of_isRCartierPullback (𝟙 S) π (p ≫ π) p hpq
    (isRelativelyNef_of_isNumericallyTrivialOver' hN') hG'
  obtain ⟨m, r, L, L', hL, -, hpb, he⟩ := hG
  refine isNumericallyTrivialOver_of_isRelativelyNef_neg'' h1 h2
    ⟨m, r, L', fun j => (hpb j).2.isCartier (hL j), ?_⟩
  rw [he]; simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs]

end NumericalTriviality

section LogSmoothHelpers

open MMP.Mori

open Classical in
/-- The coefficients of a finite sum of prime divisors with prescribed coefficients. -/
private theorem coeff_finsetSum_single {X : Scheme.{0}} {R : Type*} [AddCommMonoid R]
    (S : Finset (MMP.Mori.PrimeDivisor X)) (c : MMP.Mori.PrimeDivisor X → R)
    (P : MMP.Mori.PrimeDivisor X) :
    (∑ E ∈ S, Finsupp.single E (c E) : DivisorWithCoeffs R X).coeff P =
      if P ∈ S then c P else 0 := by
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

/-- **Prime divisors off an snc cover.** If `Ex(p) ∪ p⁻¹(Δ)` is covered by the finitely many
prime divisors in `F`, a prime divisor `P ∉ F` maps to the generic point of a prime divisor `Q`
outside `Δ`. -/
private theorem exists_primeDivisor_of_notMem_cover {X W : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [IsIntegral X] (p : W ⟶ X)
    (F : Finset (MMP.Mori.PrimeDivisor W)) (Δ : TopologicalSpace.Closeds X)
    (hcover : (MMP.Mori.exceptionalSet p : Set W) ∪ p ⁻¹' (Δ : Set X) ⊆ ⋃ E ∈ F, E.support)
    (P : MMP.Mori.PrimeDivisor W) (hP : P ∉ F) :
    ∃ Q : MMP.Mori.PrimeDivisor X, p P.genericPoint = Q.genericPoint ∧
      Q.genericPoint ∉ (Δ : Set X) := by
  have hPgen : P.genericPoint ∉ ⋃ E ∈ F, E.support := by
    intro h
    obtain ⟨E, hE, hPE⟩ := Set.mem_iUnion₂.mp h
    obtain rfl := MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hPE
    exact hP hE
  have h1 : P.genericPoint ∉ (MMP.Mori.exceptionalSet p : Set W) := fun h =>
    hPgen (hcover (Or.inl h))
  have h2 : p P.genericPoint ∉ (Δ : Set X) := fun h => hPgen (hcover (Or.inr h))
  have hbir : p P.genericPoint ∈ biregularLocus p := by
    by_contra h
    exact h1 (MMP.Mori.mem_exceptionalSet.mpr h)
  have hc : Order.coheight (p P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus p hbir, P.coheight_genericPoint]
  have e := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc, e.symm, ?_⟩
  change (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc).genericPoint ∉ (Δ : Set X)
  rw [e]
  exact h2

/-- On a nonempty scheme the unit ideal sheaf is not the zero ideal sheaf. -/
private theorem top_ne_bot_idealSheafData (X : Scheme.{0}) [Nonempty X] :
    (⊤ : X.IdealSheafData) ≠ ⊥ := by
  intro h
  have h1 := congrArg Scheme.IdealSheafData.support h
  rw [Scheme.IdealSheafData.support_top, Scheme.IdealSheafData.support_bot] at h1
  obtain ⟨x⟩ := ‹Nonempty X›
  have : x ∈ (⊤ : TopologicalSpace.Closeds X) := trivial
  rw [← h1] at this
  exact this

/-- A positive rational multiple `H / N` of an ample `ℚ`-divisor is ample. -/
private theorem isAmple_inv_natCast_smul' {X : Scheme.{0}} [IsLocallyNoetherian X]
    [CompactSpace X] [IsNormal X] {H : QDivisor X} (hH : H.IsAmple) {N : ℕ} (hN : 0 < N) :
    (((N : ℚ)⁻¹) • H).IsAmple := by
  obtain ⟨m, hm, D, hD, hDc, hDa⟩ := hH
  refine ⟨m * N, Nat.mul_pos hm hN, D, ?_, hDc, hDa⟩
  rw [hD, smul_smul]
  congr 1
  have : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp

/-- A positive lower bound for finitely many positive reals. -/
private theorem exists_pos_forall_le_of_finset {ι : Type*} (S : Finset ι) (τ : ι → ℝ)
    (hτ : ∀ i ∈ S, 0 < τ i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ S, δ ≤ τ i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a S ha ih =>
    obtain ⟨δ, hδ, hδS⟩ := ih fun i hi => hτ i (Finset.mem_insert_of_mem hi)
    refine ⟨min δ (τ a), lt_min hδ (hτ a (Finset.mem_insert_self a S)), fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hδS i hi)

end LogSmoothHelpers

section LogResolutionIdentity

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

open Classical in
/-- The coefficients of a sum of prime divisors with coefficient one. -/
private theorem coeff_sum_single_one (S : Finset (MMP.Mori.PrimeDivisor X))
    (P : MMP.Mori.PrimeDivisor X) :
    (∑ E ∈ S, Finsupp.single E (1 : ℤ) : Divisor X).coeff P = if P ∈ S then 1 else 0 := by
  classical
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

/-- **The identity is a log resolution of an snc divisor** on a smooth variety. -/
private theorem isLogResolution_id_of_isSNC (hXsm : IsSmoothScheme sX) {R : RDivisor X}
    (hR : DivisorWithCoeffs.IsSNC sX R) : MMP.Mori.IsLogResolution sX R (𝟙 X) := by
  classical
  have hexc : MMP.Mori.exceptionalSet (𝟙 X) = ⊥ := by
    refine TopologicalSpace.Closeds.ext (Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_)
    have hx' := MMP.Mori.mem_exceptionalSet.mp hx
    apply hx'
    have : MMP.Mori.IsBiregular (𝟙 X) ⊤ := by
      unfold MMP.Mori.IsBiregular
      infer_instance
    exact MMP.Mori.le_biregularLocus this trivial
  refine ⟨⟨inferInstance, MMP.Mori.isBirationalMorphism_of_isIso _, by
    rw [Category.id_comp]; exact hXsm⟩, ?_, ?_⟩
  · rw [hexc]
    intro W hW
    obtain ⟨x, hx⟩ := W.isIrreducible.nonempty
    exact absurd (hW.1 hx) (by simp)
  · rw [hexc, bot_sup_eq]
    refine Or.inr ⟨R.support, ?_, hR.of_support_subset fun P hP => ?_⟩
    · ext x
      simp only [Set.mem_iUnion, exists_prop, TopologicalSpace.Closeds.coe_preimage,
        Set.mem_preimage]
      rw [show (𝟙 X : X ⟶ X) x = x from rfl, SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff]
      simp only [Finsupp.mem_support_iff, DivisorWithCoeffs.coeff_apply]
    · rw [Finsupp.mem_support_iff] at hP ⊢
      have := coeff_sum_single_one R.support P
      rw [DivisorWithCoeffs.coeff_apply] at this
      rw [this] at hP
      split_ifs at hP with h
      · exact Finsupp.mem_support_iff.mp h
      · exact absurd rfl hP

/-- **An snc divisor from a log resolution by the identity.** If the identity is a log resolution
of `D`, then `D` is snc (for `X` carrying some snc divisor `R`, e.g. `0`). -/
private theorem isSNC_of_isLogResolution_id {R D : RDivisor X}
    (hR : DivisorWithCoeffs.IsSNC sX R) (h : MMP.Mori.IsLogResolution sX D (𝟙 X)) :
    DivisorWithCoeffs.IsSNC sX D := by
  classical
  obtain ⟨-, -, hsnc⟩ := h
  have hgen : ∀ P, D.coeff P ≠ 0 → P.genericPoint ∈
      ((MMP.Mori.exceptionalSet (𝟙 X) ⊔ D.supp.preimage (Scheme.Hom.continuous (𝟙 X)) :
        TopologicalSpace.Closeds X) : Set X) := fun P hP => by
    rw [TopologicalSpace.Closeds.coe_sup]
    refine Or.inr ?_
    change P.genericPoint ∈ D.supp
    exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, hP,
      MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
  rcases hsnc with h0 | ⟨s, hs, hsnc⟩
  · refine hR.of_support_subset fun P hP => ?_
    have := hgen P (Finsupp.mem_support_iff.mp hP)
    rw [h0] at this
    exact absurd this (by simp)
  · refine hsnc.of_support_subset fun P hP => ?_
    have hmem := hgen P (Finsupp.mem_support_iff.mp hP)
    rw [← hs] at hmem
    obtain ⟨E, hE, hPE⟩ := Set.mem_iUnion₂.mp hmem
    obtain rfl := MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hPE
    rw [Finsupp.mem_support_iff]
    have := coeff_sum_single_one s P
    rw [DivisorWithCoeffs.coeff_apply] at this
    rw [this, if_pos hE]
    exact one_ne_zero

end LogResolutionIdentity

/-- A morphism of projective `k`-varieties is a projective morphism. -/
private theorem isProjectiveMorphism_of_comp_eq' {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : AlgebraicGeometry.IsProjectiveVariety k sX)
    (hY : AlgebraicGeometry.IsProjectiveVariety k sY)
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

section LogSmoothModel

/-- The inverse of a natural number `N > 2 / δ + 2` is smaller than `δ`. -/
private theorem natCast_inv_lt_of_two_div_add_two_lt {δ : ℝ} (hδ : 0 < δ) {N : ℕ}
    (hN : 2 / δ + 2 < N) : (N : ℝ)⁻¹ < δ := by
  have hN0 : (0 : ℝ) < N := by have := div_pos two_pos hδ; linarith
  have h1 : 2 / δ < N := by linarith
  have h2 : δ / 2 * N > 1 := by
    have := (div_lt_iff₀ hδ).mp h1
    nlinarith
  rw [inv_lt_comm₀ hN0 hδ]
  calc δ⁻¹ < δ⁻¹ * (δ / 2 * N) := by nlinarith [inv_pos.mpr hδ]
    _ = N / 2 := by field_simp
    _ ≤ N := by linarith

/-- A perturbation `s (a - b)` with `s < ε / (|a| + |b| + 1)` has absolute value below `ε`. -/
private theorem abs_mul_sub_lt_of_lt_div {s ε a b : ℝ} (hs0 : 0 < s)
    (h : s < ε / (|a| + |b| + 1)) : |s * (a - b)| < ε := by
  rw [lt_div_iff₀ (by positivity)] at h
  rw [abs_mul, abs_of_pos hs0]
  have habs : |a - b| ≤ |a| + |b| := abs_sub _ _
  have := abs_nonneg a
  have := abs_nonneg b
  nlinarith

/-- If `s < (1 - c) / (|e| + 1)` with `s > 0`, then `c + s e < 1`. -/
private theorem add_mul_lt_one_of_lt_div {s c e : ℝ} (hs0 : 0 < s)
    (h : s < (1 - c) / (|e| + 1)) : c + s * e < 1 := by
  rw [lt_div_iff₀ (by positivity)] at h
  have := le_abs_self e
  nlinarith

/-- The coefficient `1 - ε + x` with `|x| < ε ≤ 1 / 2` lies in `[0, 1)`. -/
private theorem one_sub_add_mem_Ico {ε x : ℝ} (hε1 : ε ≤ 1 / 2) (hx : |x| < ε) :
    0 ≤ 1 - ε + x ∧ 1 - ε + x < 1 := by
  have := neg_abs_le x
  have := le_abs_self x
  constructor <;> linarith

/-- The coefficient `b + s (e - a)` along a strict transform lies in `[0, 1)`. -/
private theorem add_mul_sub_mem_Ico {b s e a : ℝ} (hs0 : 0 < s) (hs1 : s < 1 / 2)
    (ha0 : 0 ≤ a) (hab : a ≤ b) (he : 0 < e) (hb : b + s * e < 1) :
    0 ≤ b + s * (e - a) ∧ b + s * (e - a) < 1 := by
  have h2 := mul_nonneg hs0.le ha0
  have h3 := mul_pos hs0 he
  have h4 : s * a ≤ a := mul_le_of_le_one_left ha0 (by linarith)
  rw [mul_sub]
  constructor <;> linarith

/-- The coefficient `s h` with `0 < s < 1 / 2` and `0 ≤ h ≤ 1` lies in `[0, 1)`. -/
private theorem mul_mem_Ico_of_le_one {s h : ℝ} (hs0 : 0 < s) (hs1 : s < 1 / 2)
    (h0 : 0 ≤ h) (h1 : h ≤ 1) : 0 ≤ s * h ∧ s * h < 1 :=
  ⟨mul_nonneg hs0.le h0, by nlinarith⟩

/-- On a smooth `ℚ`-factorial complex variety, a real boundary with coefficients in `[0, 1)`
supported on the components of an snc divisor is klt. -/
private theorem isRealKltPair_of_isSNC_of_coeff_lt_one {W : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of ℂ)}
    (hWn : IsNormalVariety ℂ sW) (hWsm : IsSmoothScheme sW) (hWq : IsQFactorial sW)
    {n : ℕ} {KW : Divisor W} (hKW : KW.IsCanonicalDivisor sW n)
    {Γ E : RDivisor W} (S : Finset (MMP.Mori.PrimeDivisor W))
    (hΓS : ∀ P ∉ S, Γ.coeff P = 0) (hΓlt : ∀ P, Γ.coeff P < 1)
    (hE : DivisorWithCoeffs.IsSNC sW E) (hSE : ∀ P ∈ S, E.coeff P ≠ 0) :
    IsRealKltPair sW Γ := by
  classical
  obtain ⟨δ', hδ', hδ'τ⟩ := exists_pos_forall_le_of_finset S (fun P => 1 - Γ.coeff P)
    (fun P _ => by have := hΓlt P; linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (1 - δ') < 1 from
    max_lt one_pos (by linarith))
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (le_max_left _ _) hq1
  have hqδ : 1 - δ' < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hq1
  have hq1' : q < 1 := by exact_mod_cast hq2
  set Δq : QDivisor W := ∑ E ∈ S, Finsupp.single E q with hΔqdef
  have hΔqc : ∀ P, Δq.coeff P = if P ∈ S then q else 0 := fun P =>
    coeff_finsetSum_single S (fun _ => q) P
  have hle : ∀ P, Γ.coeff P ≤ (QDivisor.toRDivisor Δq).coeff P := by
    intro P
    rw [QDivisor.coeff_toRDivisor, hΔqc]
    by_cases hP : P ∈ S
    · rw [if_pos hP]; have := hδ'τ P hP; linarith
    · rw [if_neg hP, hΓS P hP, Rat.cast_zero]
  have hsncq : DivisorWithCoeffs.IsSNC sW Δq := by
    refine hE.of_support_subset fun P hP => ?_
    rw [Finsupp.mem_support_iff] at hP ⊢
    have h1 : Δq.coeff P ≠ 0 := by rwa [DivisorWithCoeffs.coeff_apply]
    rw [hΔqc] at h1
    have hPS : P ∈ S := by
      by_contra h
      rw [if_neg h] at h1
      exact h1 rfl
    have := hSE P hPS
    rwa [DivisorWithCoeffs.coeff_apply] at this
  have hcoef : ∀ E, Δq.coeff E < 1 := fun E => by
    rw [hΔqc]
    split_ifs
    · exact hq1'
    · exact one_pos
  have hmori := MMP.Mori.isKltPair_of_isSNC sW hWn hWsm hKW hsncq hcoef
  have hpair : MMP.Fourfold.IsPair sW Δq :=
    ⟨inferInstance, inferInstance,
      ⟨hWn, n, KW, hKW, MMP.Fourfold.isQCartier_of_isSmoothScheme hWsm _⟩, fun P => by
        rw [hΔqc]
        split_ifs
        · exact_mod_cast hq0.le
        · exact le_rfl⟩
  have hfour := (MMP.Fourfold.isKltPair_iff_mori_isKltPair sW hKW hpair).mpr hmori
  exact ⟨hWn, hΓlt, ⟨n, KW, hKW, MMP.Fourfold.IsQFactorial.isRCartier hWq _⟩,
    MMP.Fourfold.pos_of_isLogDiscrepancy_of_le hWq hle hfour.2⟩

/-- **A log smooth model with an ample component.** -/
private theorem exists_logSmoothModel
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXq : IsQFactorial sX)
    (hπ : π ≫ sZ = sX) (hdim : topologicalKrullDim X = 4)
    {n : ℕ} {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n)
    {B T M : RDivisor X} (hB : ∀ P, 0 ≤ B.coeff P) (hT : ∀ P, 0 ≤ T.coeff P)
    (hBT : IsRealKltPair sX (B + T)) (hTtriv : IsNumericallyTrivialOver ℂ sX π T)
    (hM : ∀ P, 0 ≤ M.coeff P)
    (hnum : IsNumericallyEquivalentOver ℂ sX π (Divisor.toRDivisor KX + B + T) M)
    {A : QDivisor X} (hA : A.IsAmple) (hA0 : ∀ P, 0 ≤ A.coeff P)
    (hAB : ∀ P, (QDivisor.toRDivisor A).coeff P ≤ (B + T).coeff P)
    (hAM : ∀ P, A.coeff P ≠ 0 → M.coeff P = 0) :
    ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : CompactSpace W) (_ : IsLocallyNoetherian W)
      (_ : IsNormal W) (p : W ⟶ X) (_ : LocallyOfFiniteType (p ≫ sX)),
      MMP.Mori.IsProjectiveVariety ℂ (p ≫ sX) ∧ IsSmoothScheme (p ≫ sX) ∧
      topologicalKrullDim W = 4 ∧ IsProjectiveMorphism p ∧ IsBirationalMorphism p ∧
      ∃ KW : Divisor W, KW.IsCanonicalDivisor (p ≫ sX) n ∧
        RationalMap.transformDivisor (X := W) p.toRationalMap KW = KX ∧
      ∃ (Γ MW F₀ G CW : RDivisor W) (AW : QDivisor W),
        (∀ P, 0 ≤ Γ.coeff P) ∧ (∀ P, Γ.coeff P ≤ 1) ∧ (∀ P, 0 ≤ MW.coeff P) ∧
        DivisorWithCoeffs.IsSNC (p ≫ sX) (Γ + MW) ∧
        IsNumericallyEquivalentOver ℂ (p ≫ sX) (p ≫ π) (logCanonicalDivisor KW Γ) MW ∧
        AW.IsAmple ∧ (∀ P, 0 ≤ AW.coeff P) ∧
        (∀ P, (QDivisor.toRDivisor AW).coeff P ≤ Γ.coeff P) ∧
        (∀ P, AW.coeff P ≠ 0 → Γ.coeff P < 1) ∧ (∀ P, AW.coeff P ≠ 0 → MW.coeff P = 0) ∧
        IsRealKltPair (p ≫ sX) Γ ∧
        IsRCartierPullback p (logCanonicalDivisor KX B) G ∧
        logCanonicalDivisor KW Γ = G + F₀ + CW ∧
        IsNumericallyTrivialOver ℂ (p ≫ sX) (p ≫ π) CW ∧
        (∀ P, 0 ≤ F₀.coeff P) ∧
        (∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X),
          p P.genericPoint = Q.genericPoint → F₀.coeff P = 0) ∧
        (∀ P : MMP.Mori.PrimeDivisor W,
          (∀ Q : MMP.Mori.PrimeDivisor X, p P.genericPoint ≠ Q.genericPoint) → 0 < F₀.coeff P) := by
  classical
  have hXn : IsNormalVariety ℂ sX := hBT.1
  haveI := hX
  haveI : IsSeparated sX := hXn.1.toIsSeparated
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  haveI := isSeparated_terminal_of sX
  -- the reduced divisor on the supports of the data
  set S : Finset (MMP.Mori.PrimeDivisor X) := B.support ∪ T.support ∪ M.support ∪ A.support
    with hSdef
  set Δ : QDivisor X := ∑ Q ∈ S, Finsupp.single Q (1 : ℚ) with hΔdef
  have hΔ : ∀ Q, Δ.coeff Q = 0 →
      B.coeff Q = 0 ∧ T.coeff Q = 0 ∧ M.coeff Q = 0 ∧ A.coeff Q = 0 := by
    intro Q hQ
    rw [hΔdef, coeff_finsetSum_single] at hQ
    have hQS : Q ∉ S := fun h => by rw [if_pos h] at hQ; exact one_ne_zero hQ
    simp only [hSdef, Finset.mem_union, Finsupp.mem_support_iff, not_or, not_not] at hQS
    exact ⟨hQS.1.1.1, hQS.1.1.2, hQS.1.2, hQS.2⟩
  obtain ⟨hnef, hbig⟩ := MMP.Mori.QDivisor.isNef_and_isBig_of_isAmple sX hA
  obtain ⟨W, p, hlog, hWpv, lW, nW, cW, D, -, -, -, F, hFsnc, hcover, hBp, fB, pE, hfB, hpE,
    hamp⟩ := MMP.Mori.exists_isLogResolution_isAmple_pullback_sub_sum sX Δ ⊤
      (top_ne_bot_idealSheafData X) A hnef hbig
  -- the resolution `W`
  have hWv : MMP.Mori.IsVariety ℂ (p ≫ sX) := hWpv.toIsVariety
  haveI : IsIntegral W := hWv.toIsIntegral
  haveI : LocallyOfFiniteType (p ≫ sX) := hWv.toLocallyOfFiniteType
  haveI : QuasiCompact (p ≫ sX) := hWv.toQuasiCompact
  haveI : IsSeparated (p ≫ sX) := hWv.toIsSeparated
  haveI := isSeparated_terminal_of (p ≫ sX)
  have hWsm : IsSmoothScheme (p ≫ sX) := hlog.isSmoothScheme
  haveI : IsProper p := hlog.isProper
  have hpb : IsBirationalMorphism p := hlog.isBirationalMorphism
  haveI : IsDominant p := hpb.isDominant
  haveI : IsSeparated p := IsSeparated.of_comp p sX
  have hpbij := hpb.functionFieldMap_bijective
  have hWn : IsNormalVariety ℂ (p ≫ sX) := ⟨hWv, inferInstance⟩
  have hpp : IsProjectiveMorphism p := isProjectiveMorphism_of_comp_eq' hWpv hX rfl
  have hdimW' : topologicalKrullDim W = topologicalKrullDim X := by
    haveI := hXn.1
    haveI := hWv
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hpb).symm
  have hdimW : topologicalKrullDim W = 4 := hdimW'.trans hdim
  -- canonical divisors
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (p ≫ sX) hWn
    (hdimW'.trans hKX.topologicalKrullDim_eq)
  obtain ⟨KW, hKW, hKWX⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hXn hWn hpb hKX hK₀
  obtain ⟨ω, hω0, hωX, hωW⟩ :=
    MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hXn hWn hpb hKX hKW hKWX
  -- the pull-backs
  have hcX := isCartierCombination_of_isQFactorial hXq
  obtain ⟨Gt, hGt, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p
    (hcX (logCanonicalDivisor KX (B + T)))
  obtain ⟨G, hG, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p
    (hcX (logCanonicalDivisor KX B))
  obtain ⟨PT, hPT, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p (hcX T)
  obtain ⟨PM, hPM, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p (hcX M)
  have hGteq : Gt = G + PT := by
    refine MMP.Flips.IsRCartierPullback.eq p hGt ?_
    have := MMP.Fourfold.isRCartierPullback_add hG hPT
    have e : logCanonicalDivisor KX B + T = logCanonicalDivisor KX (B + T) := by
      simp only [logCanonicalDivisor, add_assoc]
    rwa [e] at this
  have hPM0 : ∀ P, 0 ≤ PM.coeff P := by
    have := (MMP.Fourfold.isEffective_of_isRCartierPullback p
      (MMP.Fourfold.IsQFactorial.isRCartier hXq M)
      (Finsupp.le_def.mpr fun P => by simpa [DivisorWithCoeffs.coeff_apply] using hM P)).2 _ hPM
    intro P
    simpa [DivisorWithCoeffs.coeff_apply] using Finsupp.le_def.mp this P
  -- coefficients along strict transforms
  have hover : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X),
      p P.genericPoint = Q.genericPoint →
        Gt.coeff P - (KW.coeff P : ℝ) = (B + T).coeff Q ∧ PM.coeff P = M.coeff Q ∧
          fB.coeff P = A.coeff Q := by
    intro P Q h
    haveI := isIso_stalkMap_of_map_eq_genericPoint p hpbij h
    have h1 := MMP.Fourfold.coeff_eq_of_isRCartierPullback P Q h hGt
    have h2 := MMP.Fourfold.coeff_eq_of_isRCartierPullback P Q h hPM
    have hK : KW.coeff P = KX.coeff Q := by
      obtain ⟨PW, hPW, -, htr⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXn hWn hpb Q
      obtain rfl : PW = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (eq_of_map_eq_genericPoint p hpbij hPW h)
      rw [← hKWX]
      exact (htr KW).symm
    refine ⟨?_, h2, ?_⟩
    · rw [h1, hK]
      simp only [logCanonicalDivisor, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor]
      ring
    · obtain ⟨mA, hmA, DA, hDA, hDAc, -⟩ := hA
      have hDA' : Divisor.toQDivisor DA = ((mA : ℕ) : ℤ) • A := by
        rw [hDA, ← Int.cast_smul_eq_zsmul ℚ]; norm_cast
      obtain ⟨D', hD', hpbD⟩ := hfB mA hmA DA hDA' hDAc
      have h4 := MMP.Positivity.coeff_eq_of_isPullback P Q h hDAc hpbD
      have e1 := congrArg (fun D => DivisorWithCoeffs.coeff D P) hD'
      have e2 := congrArg (fun D => DivisorWithCoeffs.coeff D Q) hDA'
      simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at e1 e2
      have hm : ((mA : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hmA.ne'
      rw [h4] at e1
      exact mul_left_cancel₀ hm (e1.symm.trans e2)
  -- log discrepancies of the prime divisors of `W`
  set α : MMP.Mori.PrimeDivisor W → ℝ := fun P => 1 + (KW.coeff P : ℝ) - Gt.coeff P with hαdef
  have hαpos : ∀ P, 0 < α P := fun P => by
    have hld := isLogDiscrepancy_of_isRCartierPullback hXn hKX hWn hpb ω hω0 hωX hωW hGt P
    exact hBT.2.2.2 _ _ _ hld
  set ε : MMP.Mori.PrimeDivisor W → ℝ := fun P => min (α P) 1 / 2 with hεdef
  have hε0 : ∀ P, 0 < ε P := fun P => by
    have := hαpos P; simp only [hεdef]; positivity
  have hεα : ∀ P, ε P < α P := fun P => by
    have := hαpos P; have := min_le_left (α P) 1; simp only [hεdef]; linarith
  have hε1 : ∀ P, ε P ≤ 1 / 2 := fun P => by
    have := min_le_right (α P) 1; simp only [hεdef]; linarith
  -- prime divisors off `F`
  have hcover' : (MMP.Mori.exceptionalSet p : Set W) ∪ p ⁻¹' (Δ.supp : Set X) ⊆
      ⋃ E ∈ F, E.support := fun x hx => hcover (Or.inl hx)
  have hnotF : ∀ P ∉ F, ∃ Q : MMP.Mori.PrimeDivisor X, p P.genericPoint = Q.genericPoint ∧
      Δ.coeff Q = 0 := by
    intro P hP
    obtain ⟨Q, hQ, hQΔ⟩ := exists_primeDivisor_of_notMem_cover p F Δ.supp hcover' P hP
    refine ⟨Q, hQ, ?_⟩
    by_contra hne
    exact hQΔ (DivisorWithCoeffs.mem_supp_iff.mpr
      ⟨Q, hne, MMP.Flips.primeDivisor_genericPoint_mem_support Q⟩)
  have hexF : ∀ P : MMP.Mori.PrimeDivisor W,
      (∀ Q : MMP.Mori.PrimeDivisor X, p P.genericPoint ≠ Q.genericPoint) → P ∈ F := by
    intro P hP
    by_contra h
    obtain ⟨Q, hQ, -⟩ := hnotF P h
    exact hP Q hQ
  -- a general member of the ample class on `W`
  set R : RDivisor W := ∑ E ∈ F, Finsupp.single E (1 : ℝ) with hRdef
  have hRc : ∀ P, R.coeff P = if P ∈ F then 1 else 0 := fun P =>
    coeff_finsetSum_single F (fun _ => (1 : ℝ)) P
  have hRsnc : DivisorWithCoeffs.IsSNC (p ≫ sX) R := by
    refine hFsnc.of_support_subset fun P hP => ?_
    rw [Finsupp.mem_support_iff] at hP ⊢
    have h1 := hRc P
    have h2 := coeff_finsetSum_single F (fun _ => (1 : ℤ)) P
    rw [DivisorWithCoeffs.coeff_apply] at h1 h2
    by_cases hPF : P ∈ F
    · rw [if_pos hPF] at h2; rw [h2]; exact one_ne_zero
    · rw [if_neg hPF] at h1; exact absurd h1 hP
  have hRl := isLogResolution_id_of_isSNC hWsm hRsnc
  obtain ⟨H', hH'0, hH'a, hH'lin, hH'R, hl', N₀, Zd, hN₀, hZ0, hZ1, hH'eq⟩ :=
    hRl.exists_isAmple_qLinearlyEquivalent_add hWv hamp
  have hsncRH := isSNC_of_isLogResolution_id hRsnc hl'
  have hH'01 : ∀ P, 0 ≤ ((H'.coeff P : ℚ) : ℝ) ∧ ((H'.coeff P : ℚ) : ℝ) ≤ 1 := fun P => by
    have hc : ((H'.coeff P : ℚ) : ℝ) = (N₀ : ℝ)⁻¹ * (Zd.coeff P : ℝ) := by
      rw [hH'eq, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, smul_eq_mul]
      push_cast; rfl
    rw [hc]
    have hN1 : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
    have h0 : (0 : ℝ) ≤ Zd.coeff P := by exact_mod_cast hZ0 P
    have h1 : (Zd.coeff P : ℝ) ≤ 1 := by exact_mod_cast hZ1 P
    refine ⟨by positivity, ?_⟩
    calc (N₀ : ℝ)⁻¹ * (Zd.coeff P : ℝ) ≤ 1 * 1 :=
          mul_le_mul (inv_le_one_of_one_le₀ hN1) h1 h0 zero_le_one
      _ = 1 := one_mul 1
  have hH'F : ∀ P ∈ F, H'.coeff P = 0 := fun P hP => by
    by_contra h
    have := hH'R P h
    rw [hRc, if_pos hP] at this
    exact one_ne_zero this
  -- the exceptional prime divisors and the size of the perturbation
  set Fex : Finset (MMP.Mori.PrimeDivisor W) :=
    F.filter (fun P => ∀ Q : MMP.Mori.PrimeDivisor X, p P.genericPoint ≠ Q.genericPoint)
    with hFexdef
  have hmemFex : ∀ P, P ∈ Fex ↔ ∀ Q : MMP.Mori.PrimeDivisor X,
      p P.genericPoint ≠ Q.genericPoint := fun P => by
    rw [hFexdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hexF P h, h⟩⟩
  have hnotFex : ∀ P ∈ F, P ∉ Fex → ∃ Q : MMP.Mori.PrimeDivisor X,
      p P.genericPoint = Q.genericPoint := fun P _ h => by
    rw [hmemFex] at h
    push Not at h
    exact h
  set τ : MMP.Mori.PrimeDivisor W → ℝ := fun P =>
    if P ∈ Fex then ε P / (|(pE P : ℝ)| + |((fB.coeff P : ℚ) : ℝ)| + 1)
    else (1 - (Gt.coeff P - KW.coeff P)) / (|(pE P : ℝ)| + 1) with hτdef
  have hτ : ∀ P ∈ F, 0 < τ P := by
    intro P hP
    simp only [hτdef]
    split_ifs with hPex
    · have := hε0 P; positivity
    · obtain ⟨Q, hQ⟩ := hnotFex P hP hPex
      rw [(hover P Q hQ).1]
      have : 0 < 1 - (B + T).coeff Q := by have := hBT.2.1 Q; linarith
      positivity
  obtain ⟨δ, hδ, hδτ⟩ := exists_pos_forall_le_of_finset F τ hτ
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / δ + 2)
  have hN2 : (2 : ℝ) < N := by have := div_pos two_pos hδ; linarith
  have hNpos : 0 < N := by exact_mod_cast (show (0 : ℝ) < N by linarith)
  set s : ℚ := (N : ℚ)⁻¹ with hsdef
  have hs : ((s : ℚ) : ℝ) = (N : ℝ)⁻¹ := by rw [hsdef]; push_cast; rfl
  have hs0 : (0 : ℝ) < (s : ℝ) := by rw [hs]; positivity
  have hs1 : ((s : ℚ) : ℝ) < 1 / 2 := by
    rw [hs, one_div]; exact inv_strictAnti₀ two_pos hN2
  have hsδ : ((s : ℚ) : ℝ) < δ := by
    rw [hs]
    exact natCast_inv_lt_of_two_div_add_two_lt hδ hN
  have hsτ : ∀ P ∈ F, ((s : ℚ) : ℝ) < τ P := fun P hP => hsδ.trans_le (hδτ P hP)
  -- the divisors on `W`
  set HW : QDivisor W := fB - ∑ E ∈ F, Finsupp.single E (pE E) with hHWdef
  set C' : RDivisor W :=
    ((s : ℚ) : ℝ) • (QDivisor.toRDivisor H' - QDivisor.toRDivisor HW) with hC'def
  set F₀ : RDivisor W := ∑ E ∈ Fex, Finsupp.single E (α E - ε E) with hF₀def
  set Γ : RDivisor W := Gt - Divisor.toRDivisor KW + F₀ + C' with hΓdef
  set AW : QDivisor W := s • H' with hAWdef
  set MW : RDivisor W := PM + F₀ with hMWdef
  set CW : RDivisor W := PT + C' with hCWdef
  have hF₀c : ∀ P, F₀.coeff P = if P ∈ Fex then α P - ε P else 0 := fun P =>
    coeff_finsetSum_single Fex (fun E => α E - ε E) P
  have hHWc : ∀ P, ((HW.coeff P : ℚ) : ℝ) =
      ((fB.coeff P : ℚ) : ℝ) - (if P ∈ F then ((pE P : ℚ) : ℝ) else 0) := fun P => by
    rw [hHWdef, DivisorWithCoeffs.coeff_sub, coeff_finsetSum_single]
    split_ifs <;> push_cast <;> ring
  have hΓc : ∀ P, Γ.coeff P = (Gt.coeff P - KW.coeff P) + F₀.coeff P +
      ((s : ℚ) : ℝ) * (((H'.coeff P : ℚ) : ℝ) - ((HW.coeff P : ℚ) : ℝ)) := fun P => by
    simp only [hΓdef, hC'def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_smul, QDivisor.coeff_toRDivisor, Divisor.coeff_toRDivisor,
      smul_eq_mul]
  have hAWc : ∀ P, ((AW.coeff P : ℚ) : ℝ) = ((s : ℚ) : ℝ) * ((H'.coeff P : ℚ) : ℝ) := fun P => by
    rw [hAWdef, DivisorWithCoeffs.coeff_smul, smul_eq_mul]; push_cast; ring
  have hMWc : ∀ P, MW.coeff P = PM.coeff P + F₀.coeff P := fun P =>
    DivisorWithCoeffs.coeff_add _ _ _
  -- the coefficients, case by case
  have hcase1 : ∀ P ∉ F, Γ.coeff P = ((s : ℚ) : ℝ) * ((H'.coeff P : ℚ) : ℝ) ∧
      MW.coeff P = 0 := by
    intro P hP
    obtain ⟨Q, hQ, hΔQ⟩ := hnotF P hP
    obtain ⟨hBQ, hTQ, hMQ, hAQ⟩ := hΔ Q hΔQ
    obtain ⟨h1, h2, h3⟩ := hover P Q hQ
    have hPex : P ∉ Fex := fun h => hP (Finset.mem_filter.mp h).1
    rw [hΓc, hMWc, hF₀c, if_neg hPex, h1, h2, hHWc, if_neg hP, h3, DivisorWithCoeffs.coeff_add,
      hBQ, hTQ, hMQ, hAQ]
    simp
  have hcase2 : ∀ P ∈ F, P ∉ Fex → ∃ Q : MMP.Mori.PrimeDivisor X,
      p P.genericPoint = Q.genericPoint ∧
      Γ.coeff P = (B + T).coeff Q + ((s : ℚ) : ℝ) * (((pE P : ℚ) : ℝ) - ((A.coeff Q : ℚ) : ℝ)) ∧
      MW.coeff P = M.coeff Q := by
    intro P hP hPex
    obtain ⟨Q, hQ⟩ := hnotFex P hP hPex
    obtain ⟨h1, h2, h3⟩ := hover P Q hQ
    refine ⟨Q, hQ, ?_, ?_⟩
    · rw [hΓc, hF₀c, if_neg hPex, h1, hHWc, if_pos hP, h3, hH'F P hP]
      push_cast; ring
    · rw [hMWc, hF₀c, if_neg hPex, h2, add_zero]
  have hcase3 : ∀ P ∈ Fex, Γ.coeff P =
      1 - ε P + ((s : ℚ) : ℝ) * (((pE P : ℚ) : ℝ) - ((fB.coeff P : ℚ) : ℝ)) ∧
      MW.coeff P = PM.coeff P + (α P - ε P) := by
    intro P hPex
    have hP : P ∈ F := (Finset.mem_filter.mp hPex).1
    refine ⟨?_, ?_⟩
    · rw [hΓc, hF₀c, if_pos hPex, hHWc, if_pos hP, hH'F P hP]
      simp only [hαdef]; push_cast; ring
    · rw [hMWc, hF₀c, if_pos hPex]
  -- the bounds
  have hbound3 : ∀ P ∈ Fex,
      |((s : ℚ) : ℝ) * (((pE P : ℚ) : ℝ) - ((fB.coeff P : ℚ) : ℝ))| < ε P := by
    intro P hPex
    have hP : P ∈ F := (Finset.mem_filter.mp hPex).1
    have h := hsτ P hP
    simp only [hτdef, if_pos hPex] at h
    exact abs_mul_sub_lt_of_lt_div hs0 h
  have hbound2 : ∀ P ∈ F, ∀ Q : MMP.Mori.PrimeDivisor X, p P.genericPoint = Q.genericPoint →
      (B + T).coeff Q + ((s : ℚ) : ℝ) * ((pE P : ℚ) : ℝ) < 1 := by
    intro P hP Q hQ
    have hPex : P ∉ Fex := fun h => (hmemFex P).mp h Q hQ
    have h := hsτ P hP
    simp only [hτdef, if_neg hPex] at h
    rw [(hover P Q hQ).1] at h
    exact add_mul_lt_one_of_lt_div hs0 h
  have hΓbd : ∀ P, 0 ≤ Γ.coeff P ∧ Γ.coeff P < 1 := by
    intro P
    by_cases hP : P ∈ F
    · by_cases hPex : P ∈ Fex
      · obtain ⟨h1, -⟩ := hcase3 P hPex
        rw [h1]
        exact one_sub_add_mem_Ico (hε1 P) (hbound3 P hPex)
      · obtain ⟨Q, hQ, h1, -⟩ := hcase2 P hP hPex
        have hb := hbound2 P hP Q hQ
        rw [h1]
        have hAQ := hAB Q
        rw [QDivisor.coeff_toRDivisor] at hAQ
        have hA0Q : (0 : ℝ) ≤ ((A.coeff Q : ℚ) : ℝ) := by exact_mod_cast hA0 Q
        have hpE0 : (0 : ℝ) < ((pE P : ℚ) : ℝ) := by exact_mod_cast hpE P hP
        exact add_mul_sub_mem_Ico hs0 hs1 hA0Q hAQ hpE0 hb
    · obtain ⟨h1, -⟩ := hcase1 P hP
      rw [h1]
      obtain ⟨a, b⟩ := hH'01 P
      exact mul_mem_Ico_of_le_one hs0 hs1 a b
  have hMW0 : ∀ P, 0 ≤ MW.coeff P := by
    intro P
    by_cases hP : P ∈ F
    · by_cases hPex : P ∈ Fex
      · rw [(hcase3 P hPex).2]; have := hPM0 P; have := hεα P; linarith
      · obtain ⟨Q, -, -, h2⟩ := hcase2 P hP hPex; rw [h2]; exact hM Q
    · rw [(hcase1 P hP).2]
  have hF₀0 : ∀ P, 0 ≤ F₀.coeff P := fun P => by
    rw [hF₀c]
    split_ifs
    · have := hεα P; linarith
    · exact le_rfl
  -- the support of `Γ + M_W` is snc
  have hsuppΓ : ∀ P, (Γ + MW).coeff P ≠ 0 → (R + QDivisor.toRDivisor H').coeff P ≠ 0 := by
    intro P hP
    rw [DivisorWithCoeffs.coeff_add, QDivisor.coeff_toRDivisor, hRc]
    by_cases hPF : P ∈ F
    · rw [if_pos hPF]
      exact (by have := (hH'01 P).1; positivity : (0 : ℝ) < 1 + _).ne'
    · rw [if_neg hPF, zero_add]
      obtain ⟨h1, h2⟩ := hcase1 P hPF
      rw [DivisorWithCoeffs.coeff_add, h1, h2, add_zero] at hP
      intro h
      apply hP
      rw [h, mul_zero]
  have hsnc : DivisorWithCoeffs.IsSNC (p ≫ sX) (Γ + MW) := by
    refine hsncRH.of_support_subset fun P hP => ?_
    rw [Finsupp.mem_support_iff] at hP ⊢
    have := hsuppΓ P (by rwa [DivisorWithCoeffs.coeff_apply])
    rwa [DivisorWithCoeffs.coeff_apply] at this
  -- numerical triviality of the corrections
  have hWq : IsQFactorial (p ≫ sX) :=
    ⟨hWn, fun D => ⟨1, one_pos, by simpa using MMP.Fourfold.isCartier_of_isSmoothScheme hWsm D⟩⟩
  have hcW := isCartierCombination_of_isQFactorial hWq
  obtain ⟨mH, hmH, φH, hφH⟩ := hH'lin
  have hC'eq : C' = (((s : ℚ) : ℝ) * (mH : ℝ)⁻¹) •
      Divisor.toRDivisor (principalDivisor φH) := by
    refine Finsupp.ext fun P => ?_
    change C'.coeff P = ((((s : ℚ) : ℝ) * (mH : ℝ)⁻¹) •
      Divisor.toRDivisor (principalDivisor φH)).coeff P
    have h1 := congrArg (fun D : QDivisor W => D.coeff P) hφH
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
      Divisor.coeff_toQDivisor, zsmul_eq_mul] at h1
    rw [hC'def, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
      QDivisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toRDivisor, smul_eq_mul, smul_eq_mul]
    have hm' : (mH : ℝ) ≠ 0 := by exact_mod_cast hmH.ne'
    have h2 := congrArg (fun q : ℚ => (q : ℝ)) h1
    push_cast at h2
    field_simp
    linarith
  have hC'triv : IsNumericallyTrivialOver ℂ (p ≫ sX) (p ≫ π) C' := by
    have h0 := isNumericallyTrivialOver_principalDivisor (sX := p ≫ sX) (f := p ≫ π) φH
    have := isNumericallyTrivialOver_smul_add h0 h0 (((s : ℚ) : ℝ) * (mH : ℝ)⁻¹) 0
      (by rw [zero_smul, add_zero, ← hC'eq]; exact hcW _)
    rwa [zero_smul, add_zero, ← hC'eq] at this
  have hPTtriv : IsNumericallyTrivialOver ℂ (p ≫ sX) (p ≫ π) PT :=
    isNumericallyTrivialOver_of_isRCartierPullback' p π hTtriv hPT
  have hCW : IsNumericallyTrivialOver ℂ (p ≫ sX) (p ≫ π) CW := by
    have := isNumericallyTrivialOver_smul_add hPTtriv hC'triv 1 1
      (by rw [one_smul, one_smul]; exact hcW _)
    rwa [one_smul, one_smul] at this
  have hdiffX : IsNumericallyTrivialOver ℂ sX π (logCanonicalDivisor KX (B + T) - M) := by
    have e : logCanonicalDivisor KX (B + T) = Divisor.toRDivisor KX + B + T := by
      simp only [logCanonicalDivisor, add_assoc]
    rw [e]
    exact isNumericallyTrivialOver_sub hnum (hcX _)
  have hdiffpb : IsRCartierPullback p (logCanonicalDivisor KX (B + T) - M) (Gt - PM) := by
    have := MMP.Fourfold.isRCartierPullback_add hGt (MMP.Fourfold.isRCartierPullback_smul (-1) hPM)
    simpa only [neg_one_smul, ← sub_eq_add_neg] using this
  have hdiffW := isNumericallyTrivialOver_of_isRCartierPullback' p π hdiffX hdiffpb
  have hKBM : IsNumericallyEquivalentOver ℂ (p ≫ sX) (p ≫ π) (logCanonicalDivisor KW Γ) MW := by
    refine isNumericallyEquivalentOver_of_sub (hcW _) (hcW _) ?_
    have e : logCanonicalDivisor KW Γ - MW = (1 : ℝ) • (Gt - PM) + (1 : ℝ) • C' := by
      simp only [logCanonicalDivisor, hΓdef, hMWdef, one_smul]; abel
    rw [e]
    exact isNumericallyTrivialOver_smul_add hdiffW hC'triv 1 1 (by rw [← e]; exact hcW _)
  have hKΓ : logCanonicalDivisor KW Γ = G + F₀ + CW := by
    simp only [logCanonicalDivisor, hΓdef, hCWdef, hGteq]; abel
  -- the log smooth model is klt
  have hΓklt : IsRealKltPair (p ≫ sX) Γ := by
    refine isRealKltPair_of_isSNC_of_coeff_lt_one hWn hWsm hWq hKW (F ∪ H'.support) ?_
      (fun P => (hΓbd P).2) hsncRH ?_
    · intro P hP
      simp only [Finset.mem_union, Finsupp.mem_support_iff, not_or, not_not] at hP
      rw [(hcase1 P hP.1).1]
      have : H'.coeff P = 0 := by rw [DivisorWithCoeffs.coeff_apply]; exact hP.2
      rw [this, Rat.cast_zero, mul_zero]
    · intro P hPS
      rw [DivisorWithCoeffs.coeff_add, QDivisor.coeff_toRDivisor, hRc]
      simp only [Finset.mem_union, Finsupp.mem_support_iff] at hPS
      by_cases hPF : P ∈ F
      · rw [if_pos hPF]
        exact (by have := (hH'01 P).1; positivity : (0 : ℝ) < 1 + _).ne'
      · rw [if_neg hPF, zero_add]
        have hH'P : H'.coeff P ≠ 0 := by
          rw [DivisorWithCoeffs.coeff_apply]; exact hPS.resolve_left hPF
        exact_mod_cast hH'P
  refine ⟨W, inferInstance, cW, lW, nW, p, inferInstance, hWpv, hWsm, hdimW, hpp, hpb, KW, hKW,
    hKWX, Γ, MW, F₀, G, CW, AW, fun P => (hΓbd P).1, fun P => (hΓbd P).2.le, hMW0, hsnc, hKBM,
    ?_, ?_, ?_, ?_, ?_, hΓklt, hG, hKΓ, hCW, hF₀0, ?_, ?_⟩
  · exact isAmple_inv_natCast_smul' hH'a hNpos
  · intro P
    rw [hAWdef, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    exact mul_nonneg (by positivity) (hH'0 P)
  · intro P
    rw [QDivisor.coeff_toRDivisor, hAWc]
    by_cases hP : P ∈ F
    · rw [hH'F P hP, Rat.cast_zero, mul_zero]; exact (hΓbd P).1
    · rw [(hcase1 P hP).1]
  · intro P _
    exact (hΓbd P).2
  · intro P hP
    have hH'P : H'.coeff P ≠ 0 := fun h => hP (by
      rw [hAWdef, DivisorWithCoeffs.coeff_smul, h, smul_zero])
    have hPF : P ∉ F := fun h => hH'P (hH'F P h)
    exact (hcase1 P hPF).2
  · intro P Q hQ
    rw [hF₀c, if_neg]
    intro h
    exact (hmemFex P).mp h Q hQ
  · intro P hP
    have hPex : P ∈ Fex := (hmemFex P).mpr hP
    rw [hF₀c, if_pos hPex]
    have := hεα P
    linarith

end LogSmoothModel

section Numerics

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {f : X ⟶ Y}

/-- Adding a divisor numerically trivial over the base to an `f`-nef divisor keeps it `f`-nef. -/
private theorem isRelativelyNef_add_of_isNumericallyTrivialOver {D N : RDivisor X}
    (hD : IsRelativelyNef k sX f D) (hN : IsNumericallyTrivialOver k sX f N) :
    IsRelativelyNef k sX f (D + N) := by
  obtain ⟨m, r, L, hL, hDe, hDn⟩ := hD
  obtain ⟨m', r', L', hL', hNe⟩ := hN.1
  have hNe' : N = ∑ j, r' j • Divisor.toRDivisor (L' j) := by
    rw [hNe]; simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs]
  refine ⟨m + m', Fin.append ((1 : ℝ) • r) ((1 : ℝ) • r'), Fin.append L L', fun j => ?_, ?_,
    fun C hC x hx => ?_⟩
  · exact Fin.addCases (motive := fun j => (Fin.append L L' j).IsCartier)
      (fun i => by simpa using hL i) (fun i => by simpa using hL' i) j
  · simp [Fin.sum_univ_add, hDe, hNe']
  · have hxD := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r L hL
    rw [← hDe] at hxD
    have hxN := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r' L' hL'
    rw [← hNe'] at hxN
    have h0 := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C (fun _ : Fin 0 => (0 : ℝ))
      (fun _ => 0) (fun i => i.elim0)
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h0
    have hN0 := hN.2.2 C hC _ _ _ _ _ _ _ _ hxN h0
    have hlin := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).2 _ _ _ _ _ _ _ _ 1 1
      hxD hxN
    simp only [one_smul] at hlin
    have h1 := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx
      (by simpa using hlin)
    have h2 := hDn C hC _ hxD
    linarith

/-- The negative of a divisor numerically trivial over the base is numerically trivial. -/
private theorem isNumericallyTrivialOver_neg' {N : RDivisor X}
    (hN : IsNumericallyTrivialOver k sX f N) : IsNumericallyTrivialOver k sX f (-N) := by
  obtain ⟨m', r', L', hL', hNe⟩ := hN.1
  refine ⟨⟨m', -r', L', hL', by rw [hNe]; simp [Finset.sum_neg_distrib, neg_smul]⟩, hN.2.1,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ hx₁ hx₂ => ?_⟩
  have hNe' : N = ∑ j, r' j • Divisor.toRDivisor (L' j) := by
    rw [hNe]; simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs]
  have hy := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r' L' hL'
  rw [← hNe'] at hy
  have hlin := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).2 _ _ _ _ _ _ _ _ (-1) 0
    hy hy
  simp only [neg_one_smul, zero_smul, add_zero, zero_mul] at hlin
  have h1 := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx₁ hlin
  have h0 := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C (fun _ : Fin 0 => (0 : ℝ))
    (fun _ => 0) (fun i => i.elim0)
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at h0
  have h2 := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx₂ h0
  have h3 := hN.2.2 C hC _ _ _ _ _ _ _ _ hy h0
  rw [h1, h2, h3]
  ring

/-- The canonical morphism from the spectrum of the function field is dominant. -/
private theorem isDominant_fromSpecStalk_genericPoint (X : Scheme.{0}) [IsIntegral X] :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  constructor
  rw [DenseRange, Scheme.range_fromSpecStalk]
  refine Dense.mono (s₁ := {genericPoint X}) ?_ ?_
  · rintro _ rfl; exact specializes_rfl
  · rw [dense_iff_closure_eq]; exact genericPoint_spec X

end Numerics

section Transfer

/-- **Transfer of a log minimal model of the log smooth model.** -/
private theorem exists_model_of_logSmoothModel
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hπ : π ≫ sZ = sX) (hXq : IsQFactorial sX)
    {n : ℕ} {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n)
    {B : RDivisor X} (hB : ∀ P, 0 ≤ B.coeff P) (hklt : IsRealKltPair sX B)
    {W : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    {p : W ⟶ X} [LocallyOfFiniteType (p ≫ sX)]
    (hWp : MMP.Mori.IsProjectiveVariety ℂ (p ≫ sX)) (hWsm : IsSmoothScheme (p ≫ sX))
    (hpp : IsProjectiveMorphism p) (hpb : IsBirationalMorphism p)
    {KW : Divisor W} (hKWX : RationalMap.transformDivisor (X := W) p.toRationalMap KW = KX)
    {Γ F₀ G CW : RDivisor W} (hΓ0 : ∀ P, 0 ≤ Γ.coeff P) (hΓklt : IsRealKltPair (p ≫ sX) Γ)
    (hG : IsRCartierPullback p (logCanonicalDivisor KX B) G)
    (hKΓ : logCanonicalDivisor KW Γ = G + F₀ + CW)
    (hCW : IsNumericallyTrivialOver ℂ (p ≫ sX) (p ≫ π) CW)
    (hF₀ : ∀ P, 0 ≤ F₀.coeff P)
    (hF₀Q : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X),
      p P.genericPoint = Q.genericPoint → F₀.coeff P = 0)
    (hF₀E : ∀ P : MMP.Mori.PrimeDivisor W,
      (∀ Q : MMP.Mori.PrimeDivisor X, p P.genericPoint ≠ Q.genericPoint) → 0 < F₀.coeff P)
    {Y : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {πY : Y ⟶ Z} {KY : Divisor Y} {BY : RDivisor Y}
    {φW : W.RationalMap Y}
    (hYW : IsRealLogMinimalModel (p ≫ sX) sY sZ (p ≫ π) πY KW Γ KY BY φW) :
    ∃ (BY' : RDivisor Y) (φ : X.RationalMap Y),
      IsRealLogMinimalModel sX sY sZ π πY KX B KY BY' φ ∧ IsRealKltPair sY BY' ∧
        ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F := by
  classical
  -- the source, the log smooth model and the target
  have hXn : IsNormalVariety ℂ sX := hklt.1
  have hYn : IsNormalVariety ℂ sY := hYW.isNormalVariety_model
  have hYq : IsQFactorial sY := hYW.isQFactorial
  have hYp : MMP.Mori.IsProjectiveVariety ℂ sY := hYW.isProjectiveVariety_model
  have hπY : πY ≫ sZ = sY := hYW.comp_eq_model
  have hWn : IsNormalVariety ℂ (p ≫ sX) := hΓklt.1
  haveI : IsSeparated sX := hXn.1.toIsSeparated
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  haveI : IsSeparated (p ≫ sX) := hWn.1.toIsSeparated
  haveI := isSeparated_terminal_of sX
  haveI := isSeparated_terminal_of sY
  haveI := isSeparated_terminal_of (p ≫ sX)
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  haveI : QuasiCompact sY := hYn.1.toQuasiCompact
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  haveI : QuasiCompact (p ≫ sX) := hWn.1.toQuasiCompact
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  haveI : IsDominant p := hpb.isDominant
  haveI : IsSeparated p := IsSeparated.of_comp p sX
  have hpbij := hpb.functionFieldMap_bijective
  obtain ⟨mY, hKY⟩ := hYW.isCanonicalDivisor_model
  obtain ⟨mW, hKW⟩ := hYW.isCanonicalDivisor
  -- the common resolution of the model of `(W, Γ)`
  obtain ⟨V, _, _, _, sV, r, q, hr, GXW, GY, hR, hpos⟩ := hYW.exists_resolution_pos
  obtain ⟨hVv, hVsm, hrs, hqs, hrp, hqp, hrb, hqb, hrinv, hφW, ⟨mV, KV, hKV, hKVr, hKVq⟩, hGXW,
    hGY, hH0, hHexc⟩ := hR
  subst hrs
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hrp
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqp
  haveI : IsDominant r := hrb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hVn : IsNormalVariety ℂ (r ≫ p ≫ sX) := ⟨hVv, inferInstance⟩
  haveI : QuasiCompact (r ≫ p ≫ sX) := hVv.toQuasiCompact
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (r ≫ p ≫ sX)
  haveI : LocallyOfFiniteType (r ≫ p ≫ sX) := hVv.toLocallyOfFiniteType
  haveI : IsSeparated (r ≫ p ≫ sX) := hVv.toIsSeparated
  haveI := isSeparated_terminal_of (r ≫ p ≫ sX)
  haveI : IsSeparated r := IsSeparated.of_comp r (p ≫ sX)
  haveI : IsSeparated q := isSeparated_of_isSeparated_toTerminal q
  have hrbij := hrb.functionFieldMap_bijective
  have hqbij := hqb.functionFieldMap_bijective
  have hVq : IsNormalVariety ℂ (q ≫ sY) := by rw [hqs]; exact hVn
  have hVp : MMP.Mori.IsProjectiveVariety ℂ (r ≫ p ≫ sX) :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr ⟨hVv, hrp.comp hWp.isProjective⟩
  -- the composite resolution of `X`
  have hpVb : IsBirationalMorphism (r ≫ p) :=
    MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hrb hpb
  have hpVp : IsProjectiveMorphism (r ≫ p) := hrp.comp hpp
  haveI : IsDominant (r ≫ p) := hpVb.isDominant
  have hVnX : IsNormalVariety ℂ ((r ≫ p) ≫ sX) := by rw [Category.assoc]; exact hVn
  have hpVbij := hpVb.functionFieldMap_bijective
  set H : X.RationalMap V := hpVb.inverse with hHdef
  have hH : MMP.Mori.RationalMap.IsInverse (r ≫ p).toRationalMap H := hpVb.isInverse_inverse
  set φ : X.RationalMap Y := H.compHom q with hφdef
  have hφb : MMP.Mori.RationalMap.IsBirational φ := hH.isBirational_compHom hqb
  -- the two routes to `Z` agree
  have hpq : (r ≫ p) ≫ π = q ≫ πY := by
    have h1 : hr.compHom (q ≫ πY) = (p ≫ π).toRationalMap := by
      rw [← MMP.Fourfold.Oai4C1.Main.compHom_compHom, hφW]; exact hYW.isOver
    have h2 : hr.compHom (r ≫ p ≫ π) = (p ≫ π).toRationalMap := by
      rw [← MMP.Fourfold.Oai4C1.Main.compHom_compHom, compHom_eq_of_isInverse hrinv,
        toRationalMap_compHom, Category.id_comp]
    have h3 := hrinv.specFunctionFieldMap_comp_fromFunctionField_compHom (q ≫ πY)
    have h4 := hrinv.specFunctionFieldMap_comp_fromFunctionField_compHom (r ≫ p ≫ π)
    rw [h1] at h3
    rw [h2] at h4
    haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
    haveI := isSeparated_terminal_of sZ
    haveI : Z.IsSeparated := ⟨by
      rw [show Limits.terminal.from Z = (Z ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
      infer_instance⟩
    haveI := isDominant_fromSpecStalk_genericPoint V
    rw [Category.assoc]
    exact ext_of_isDominant (V.fromSpecStalk (genericPoint V)) (h4.symm.trans h3)
  have hpq' : r ≫ p ≫ π = q ≫ πY := by rw [← Category.assoc]; exact hpq
  have hφZ : MMP.Flips.RationalMap.IsOver π πY φ := by
    change (H.compHom q).compHom πY = π.toRationalMap
    rw [MMP.Fourfold.Oai4C1.Main.compHom_compHom, ← hpq, ← MMP.Fourfold.Oai4C1.Main.compHom_compHom,
      compHom_eq_of_isInverse hH, toRationalMap_compHom, Category.id_comp]
  -- pull-backs to `V`
  have hWq : IsQFactorial (p ≫ sX) :=
    ⟨hWn, fun D => ⟨1, one_pos, by simpa using MMP.Fourfold.isCartier_of_isSmoothScheme hWsm D⟩⟩
  obtain ⟨GV, hGV, -⟩ := MMP.Flips.existsUnique_isRCartierPullback r
    (isCartierCombination_of_isQFactorial hWq G)
  obtain ⟨F₀V, hF₀V, -⟩ := MMP.Flips.existsUnique_isRCartierPullback r
    (isCartierCombination_of_isQFactorial hWq F₀)
  obtain ⟨CV, hCV, -⟩ := MMP.Flips.existsUnique_isRCartierPullback r
    (isCartierCombination_of_isQFactorial hWq CW)
  have hGXWeq : GXW = GV + F₀V + CV := by
    refine MMP.Flips.IsRCartierPullback.eq r hGXW ?_
    rw [hKΓ]
    exact MMP.Fourfold.isRCartierPullback_add (MMP.Fourfold.isRCartierPullback_add hGV hF₀V) hCV
  have hGVX : IsRCartierPullback (r ≫ p) (logCanonicalDivisor KX B) GV := hG.comp hGV
  -- the correction on `Y`
  obtain ⟨hCYtriv, hCYpb⟩ := isNumericallyTrivialOver_transformDivisor_and_isRCartierPullback
    (r ≫ p ≫ sX) (p ≫ sX) sY sZ hVn hVp hWn hWp hYq hYp hZ (p ≫ π) πY
    (by rw [Category.assoc, hπ]) hπY r q rfl hqs hpq' hrp hrb hqp hqb hCW hCV
  set CY : RDivisor Y := RationalMap.transformDivisor (X := V) q.toRationalMap CV with hCYdef
  set BY' : RDivisor Y := BY - CY with hBY'def
  have hGZ : IsRCartierPullback q (logCanonicalDivisor KY BY') (GY - CV) := by
    have := MMP.Fourfold.isRCartierPullback_add hGY (MMP.Fourfold.isRCartierPullback_smul (-1) hCYpb)
    have e1 : logCanonicalDivisor KY BY + (-1 : ℝ) • CY = logCanonicalDivisor KY BY' := by
      simp only [logCanonicalDivisor, hBY'def, neg_one_smul]; abel
    have e2 : GY + (-1 : ℝ) • CV = GY - CV := by rw [neg_one_smul]; abel
    rwa [e1, e2] at this
  -- the comparison divisor
  set E : RDivisor V := GV - (GY - CV) with hEdef
  have hE : E = (GXW - GY) - F₀V := by rw [hEdef, hGXWeq]; abel
  -- prime divisors on the models
  have hPX : ∀ P : MMP.Mori.PrimeDivisor X, ∃ PW : MMP.Mori.PrimeDivisor W,
      p PW.genericPoint = P.genericPoint := fun P => by
    obtain ⟨PW, hPW, -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXn hWn hpb P
    exact ⟨PW, hPW⟩
  have hF₀Vc : ∀ (Q : MMP.Mori.PrimeDivisor V) (PW : MMP.Mori.PrimeDivisor W),
      r Q.genericPoint = PW.genericPoint → F₀V.coeff Q = F₀.coeff PW := fun Q PW h => by
    haveI := isIso_stalkMap_of_map_eq_genericPoint r hrbij h
    exact MMP.Fourfold.coeff_eq_of_isRCartierPullback Q PW h hF₀V
  have hdimY : topologicalKrullDim Y = mY := hKY.topologicalKrullDim_eq
  have hHzero : ∀ (Q : MMP.Mori.PrimeDivisor V) (F : MMP.Mori.PrimeDivisor Y),
      q Q.genericPoint = F.genericPoint → (GXW - GY).coeff Q = 0 := by
    intro Q F hQ
    by_contra hne
    obtain ⟨hWnq, hqb', hprop, hexc⟩ := hHexc Q hne
    have h2 := two_le_coheight_of_isExceptional _ hexc hdimY
    change 2 ≤ Order.coheight (q Q.genericPoint) at h2
    rw [hQ, F.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  have hKVX : RationalMap.transformDivisor (X := V) (r ≫ p).toRationalMap KV = KX := by
    rw [← transformDivisor_comp_of_isBirationalMorphism hXn hWn hVn hpb hrb, hKVr, hKWX]
  -- nefness of the corrected adjoint
  have hnefY' : IsRelativelyNef ℂ sY πY (logCanonicalDivisor KY BY') := by
    have e : logCanonicalDivisor KY BY' = logCanonicalDivisor KY BY + (-CY) := by
      simp only [logCanonicalDivisor, hBY'def, sub_eq_add_neg, add_assoc]
    rw [e]
    exact isRelativelyNef_add_of_isNumericallyTrivialOver hYW.isRelativelyNef
      (isNumericallyTrivialOver_neg' hCYtriv)
  -- the comparison is effective
  have hEeff : 0 ≤ E := by
    have hpush : 0 ≤ RationalMap.transformDivisor (X := V) (r ≫ p).toRationalMap E := by
      refine Finsupp.le_def.mpr fun P => ?_
      obtain ⟨PV, hPV, -, htr⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXn hVnX hpVb P
      obtain ⟨PW, hPW⟩ := hPX P
      have hrPV : r PV.genericPoint = PW.genericPoint :=
        eq_of_map_eq_genericPoint p hpbij (by rw [← Scheme.Hom.comp_apply]; exact hPV) hPW
      rw [Finsupp.coe_zero, Pi.zero_apply, htr, hE]
      have h1 := hF₀Vc PV PW hrPV
      rw [hF₀Q PW P hPW] at h1
      have h2 := hH0 PV
      change 0 ≤ ((GXW - GY) - F₀V).coeff PV
      rw [DivisorWithCoeffs.coeff_sub, h1, sub_zero]
      exact h2
    exact MMP.Fourfold.nonneg_sub_of_nonneg_transformDivisor_sub (r ≫ p ≫ sX) sX sY hVn hVp hXn
      hX hYn hYp π πY (r ≫ p) q (Category.assoc _ _ _) hqs hpq hpVp hpVb hqp hqb
      (isCartierCombination_of_isQFactorial hXq _) hnefY' hGVX hGZ hpush
  have hEeff' : ∀ P, 0 ≤ E.coeff P := fun P => by
    have := Finsupp.le_def.mp hEeff P
    simpa [DivisorWithCoeffs.coeff_apply] using this
  -- prime divisors of `Y` and of `X` on `V`
  have hFY : ∀ F : MMP.Mori.PrimeDivisor Y, ∃ FV : MMP.Mori.PrimeDivisor V,
      q FV.genericPoint = F.genericPoint ∧
      (∀ D : Divisor V, RationalMap.transformDivisor (X := V) q.toRationalMap D F = D FV) ∧
      (∀ D : RDivisor V, RationalMap.transformDivisor (X := V) q.toRationalMap D F = D FV) :=
    fun F => by
      obtain ⟨FV, hFV, -, htr⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hYn hVq hqb F
      exact ⟨FV, hFV, fun D => htr D, fun D => htr D⟩
  have hXV : ∀ P : MMP.Mori.PrimeDivisor X, ∃ PV : MMP.Mori.PrimeDivisor V,
      (r ≫ p) PV.genericPoint = P.genericPoint ∧
      (∀ D : Divisor V, RationalMap.transformDivisor (X := V) (r ≫ p).toRationalMap D P = D PV) :=
    fun P => by
      obtain ⟨PV, hPV, -, htr⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXn hVnX hpVb P
      exact ⟨PV, hPV, fun D => htr D⟩
  have hKVY : ∀ (F : MMP.Mori.PrimeDivisor Y) (FV : MMP.Mori.PrimeDivisor V),
      q FV.genericPoint = F.genericPoint → KY.coeff F = KV.coeff FV := by
    intro F FV hFV
    obtain ⟨FV', hFV', htr, -⟩ := hFY F
    obtain rfl : FV' = FV := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_map_eq_genericPoint q hqbij hFV' hFV)
    rw [← hKVq]
    exact htr KV
  have hKVP : ∀ (P : MMP.Mori.PrimeDivisor X) (PV : MMP.Mori.PrimeDivisor V),
      (r ≫ p) PV.genericPoint = P.genericPoint → KX.coeff P = KV.coeff PV := by
    intro P PV hPV
    obtain ⟨PV', hPV', htr⟩ := hXV P
    obtain rfl : PV' = PV := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_map_eq_genericPoint (r ≫ p) hpVbij hPV' hPV)
    rw [← hKVX]
    exact htr KV
  -- the model of `(W, Γ)` extracts no prime divisor: `(W, Γ)` is klt
  have hdimV : topologicalKrullDim V = mV := hKV.topologicalKrullDim_eq
  have hdimW : topologicalKrullDim W = mW := hKW.topologicalKrullDim_eq
  have hmVW : mV = mW := by
    have h1 := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (p ≫ sX)
      (r ≫ p ≫ sX) hrb
    rw [hdimV, hdimW] at h1
    exact_mod_cast h1.symm
  subst hmVW
  obtain ⟨ωW, hωW0, hωWK, hωWV⟩ :=
    MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hWn hVn hrb hKW hKV hKVr
  have hFW : ∀ (F : MMP.Mori.PrimeDivisor Y) (FV : MMP.Mori.PrimeDivisor V),
      q FV.genericPoint = F.genericPoint →
        ∃ PW : MMP.Mori.PrimeDivisor W, r FV.genericPoint = PW.genericPoint := by
    intro F FV hFV
    by_contra hno
    push Not at hno
    have hinvexc : MMP.Flips.RationalMap.IsInverseExceptional φW F := by
      intro PW hPW
      obtain ⟨PV', hPV', -, -⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hWn hVn hrb PW
      have h1 := transformPrimeDivisor_eq_some_of_isInverse hrbij hrinv hPV'
      rw [← hφW, transformPrimeDivisor_compHom h1 q,
        MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff] at hPW
      have h2 := eq_of_map_eq_genericPoint q hqbij hFV hPW
      exact hno PW (by rw [h2]; exact hPV')
    have hBYF : 1 ≤ BY.coeff F := by
      rw [hYW.coeff_boundary F, if_pos hinvexc]
      have := Finsupp.le_def.mp (MMP.Mori.RationalMap.transformDivisor_nonneg φW
        (Finsupp.le_def.mpr fun P => by simpa [DivisorWithCoeffs.coeff_apply] using hΓ0 P)) F
      have h0 : 0 ≤ (RationalMap.transformDivisor φW Γ).coeff F := by
        simpa [DivisorWithCoeffs.coeff_apply] using this
      linarith
    have hld := isLogDiscrepancy_of_isRCartierPullback hWn hKW hVn hrb ωW hωW0 hωWK hωWV hGXW FV
    have hpos' := hΓklt.2.2.2 _ _ _ hld
    have h1 := hHzero FV F hFV
    haveI := isIso_stalkMap_of_map_eq_genericPoint q hqbij hFV
    have h2 := MMP.Fourfold.coeff_eq_of_isRCartierPullback FV F hFV hGY
    have h3 := hKVY F FV hFV
    simp only [logCanonicalDivisor, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor,
      DivisorWithCoeffs.coeff_sub] at h1 h2
    rw [h3] at h2
    linarith
  -- and it extracts no prime divisor exceptional over `X`
  have hFX : ∀ (F : MMP.Mori.PrimeDivisor Y) (FV : MMP.Mori.PrimeDivisor V),
      q FV.genericPoint = F.genericPoint →
        ∃ P : MMP.Mori.PrimeDivisor X, (r ≫ p) FV.genericPoint = P.genericPoint := by
    intro F FV hFV
    obtain ⟨PW, hPW⟩ := hFW F FV hFV
    by_cases hex : ∃ P : MMP.Mori.PrimeDivisor X, p PW.genericPoint = P.genericPoint
    · obtain ⟨P, hP⟩ := hex
      exact ⟨P, by rw [Scheme.Hom.comp_apply, hPW, hP]⟩
    · push Not at hex
      have h0 := hF₀E PW hex
      have h1 := hF₀Vc FV PW hPW
      have h2 := hHzero FV F hFV
      have h3 := hEeff' FV
      rw [hE, DivisorWithCoeffs.coeff_sub, h2, h1] at h3
      linarith
  have hφP : ∀ (P : MMP.Mori.PrimeDivisor X) (PV : MMP.Mori.PrimeDivisor V),
      (r ≫ p) PV.genericPoint = P.genericPoint → RationalMap.transformPrimeDivisor H P = some PV :=
    fun P PV h => transformPrimeDivisor_eq_some_of_isInverse hpVbij hH h
  have hφF : ∀ (F : MMP.Mori.PrimeDivisor Y) (FV : MMP.Mori.PrimeDivisor V)
      (P : MMP.Mori.PrimeDivisor X), q FV.genericPoint = F.genericPoint →
        (r ≫ p) FV.genericPoint = P.genericPoint → RationalMap.transformPrimeDivisor φ P = some F :=
    fun F FV P hFV hP => by
      rw [hφdef, transformPrimeDivisor_compHom (hφP P FV hP) q,
        MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff]
      exact hFV
  have hnoext : ∀ F : MMP.Mori.PrimeDivisor Y,
      ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F := by
    intro F hF
    obtain ⟨FV, hFV, -, -⟩ := hFY F
    obtain ⟨P, hP⟩ := hFX F FV hFV
    exact hF P (hφF F FV P hFV hP)
  have huniq : ∀ (F : MMP.Mori.PrimeDivisor Y) (P P' : MMP.Mori.PrimeDivisor X),
      RationalMap.transformPrimeDivisor φ P = some F →
        RationalMap.transformPrimeDivisor φ P' = some F → P' = P := fun F P P' h h' =>
    eq_of_transformPrimeDivisor_eq_some_of_isInverse hXn hYn hVnX
      (by rw [Category.assoc, hqs]) hpVb hqb hH rfl h' h
  -- the coefficients along the prime divisors of `Y`
  have hcoeffF : ∀ (F : MMP.Mori.PrimeDivisor Y) (FV : MMP.Mori.PrimeDivisor V)
      (P : MMP.Mori.PrimeDivisor X), q FV.genericPoint = F.genericPoint →
        (r ≫ p) FV.genericPoint = P.genericPoint →
          E.coeff FV = 0 ∧ BY'.coeff F = B.coeff P ∧ KY.coeff F = KX.coeff P := by
    intro F FV P hFV hP
    obtain ⟨PW, hPW⟩ := hPX P
    have hrFV : r FV.genericPoint = PW.genericPoint :=
      eq_of_map_eq_genericPoint p hpbij (by rw [← Scheme.Hom.comp_apply]; exact hP) hPW
    have hE0 : E.coeff FV = 0 := by
      rw [hE, DivisorWithCoeffs.coeff_sub, hHzero FV F hFV, hF₀Vc FV PW hrFV, hF₀Q PW P hPW,
        sub_zero]
    haveI := isIso_stalkMap_of_map_eq_genericPoint q hqbij hFV
    haveI := isIso_stalkMap_of_map_eq_genericPoint (r ≫ p) hpVbij hP
    have h1 := MMP.Fourfold.coeff_eq_of_isRCartierPullback FV P hP hGVX
    have h2 := MMP.Fourfold.coeff_eq_of_isRCartierPullback FV F hFV hGZ
    have hKF := hKVY F FV hFV
    have hKP := hKVP P FV hP
    refine ⟨hE0, ?_, by rw [hKF, hKP]⟩
    have h3 := hE0
    rw [hEdef, DivisorWithCoeffs.coeff_sub, h1, h2] at h3
    simp only [logCanonicalDivisor, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor] at h3
    rw [hKF, hKP] at h3
    linarith
  have hBYeq : BY' = RationalMap.transformDivisor φ B := by
    refine Finsupp.ext fun F => ?_
    obtain ⟨FV, hFV, -, -⟩ := hFY F
    obtain ⟨P, hP⟩ := hFX F FV hFV
    have h1 := (hcoeffF F FV P hFV hP).2.1
    rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply] at h1
    rw [h1]
    exact (MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq (hφF F FV P hFV hP)
      (fun P' h => huniq F P P' (hφF F FV P hFV hP) h) B).symm
  have hKYeq : KY = RationalMap.transformDivisor φ KX := by
    refine Finsupp.ext fun F => ?_
    obtain ⟨FV, hFV, -, -⟩ := hFY F
    obtain ⟨P, hP⟩ := hFX F FV hFV
    have h1 := (hcoeffF F FV P hFV hP).2.2
    rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply] at h1
    rw [h1]
    exact (MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq (hφF F FV P hFV hP)
      (fun P' h => huniq F P P' (hφF F FV P hFV hP) h) KX).symm
  -- positivity along the contracted prime divisors of `X`
  have hposX : ∀ P : MMP.Mori.PrimeDivisor X, RationalMap.IsExceptional φ P →
      ∀ P' : MMP.Mori.PrimeDivisor V, RationalMap.transformPrimeDivisor H P = some P' →
        0 < E.coeff P' := by
    intro P hP P' hP'
    have hη := map_genericPoint_of_transformPrimeDivisor_eq_some hH hP'
    obtain ⟨PW, hPW⟩ := hPX P
    have hrP' : r P'.genericPoint = PW.genericPoint :=
      eq_of_map_eq_genericPoint p hpbij (by rw [← Scheme.Hom.comp_apply]; exact hη) hPW
    have h1 := transformPrimeDivisor_eq_some_of_isInverse hrbij hrinv hrP'
    have hexcq : RationalMap.IsExceptional (X := V) q.toRationalMap P' :=
      (isExceptional_compHom_iff hP' q).mp hP
    have hexcW : RationalMap.IsExceptional φW PW := by
      rw [← hφW]; exact (isExceptional_compHom_iff h1 q).mpr hexcq
    have h2 := hpos PW hexcW P' h1
    rw [hE, DivisorWithCoeffs.coeff_sub, hF₀Vc P' PW hrP', hF₀Q PW P hPW, sub_zero]
    exact h2
  -- the comparison is exceptional over `Y`
  have hEexc : ∀ Q, E.coeff Q ≠ 0 → MMP.Flips.IsExceptionalPrimeDivisor sY q Q := by
    intro Q hQ
    by_contra hne
    let EQ : MMP.Flips.ProperDivisorOver ℂ sY :=
      { toDivisorOver := ⟨V, q, hVq, hqb, Q⟩, isProper := inferInstance }
    have hEQ : ¬ EQ.IsExceptional := fun h' => hne ⟨hVq, hqb, inferInstance, h'⟩
    obtain ⟨F, -, hF, -⟩ :=
      MMP.Flips.ProperDivisorOver.exists_primeDivisor_of_not_isExceptional hYn EQ hEQ
    obtain ⟨P, hP⟩ := hFX F Q hF
    exact hQ (hcoeffF F Q P hF hP).1
  -- the target is klt
  have hGZ' : IsRCartierPullback q (logCanonicalDivisor (RationalMap.transformDivisor φ KX)
      (RationalMap.transformDivisor φ B)) (GY - CV) := by
    rw [← hKYeq, ← hBYeq]; exact hGZ
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  have N : IsNefWeakModel sX sY sZ π πY KX B φ :=
    { isNormalVariety_source := hXn
      isProjectiveVariety_source := hX
      comp_eq_source := hπ
      isCanonicalDivisor := ⟨n, hKX⟩
      isCartierCombination := isCartierCombination_of_isQFactorial hXq _
      isNormalVariety_target := hYn
      isProjectiveVariety_target := hYp
      comp_eq_target := hπY
      isBirational := hφb
      isOver := hφZ
      not_isInverseExceptional := hnoext
      isRelativelyNef := by rw [← hKYeq, ← hBYeq]; exact hnefY'
      exists_resolution := ⟨V, inferInstance, inferInstance, inferInstance, r ≫ p ≫ sX, r ≫ p,
        q, H, hVv, hVsm, Category.assoc _ _ _, hqs, hpVp, hqp, hpVb, hqb, hH, rfl, GV, GY - CV,
        hGVX, hGZ', hEeff', hEexc⟩ }
  have hkltY : IsRealKltPair sY BY' := by
    have := isRealKltPair_transformDivisor_of_isNefWeakModel N hYq hKY hklt
    rwa [← hBYeq] at this
  have hBY'0 : ∀ P, 0 ≤ BY'.coeff P := by
    intro P
    have := Finsupp.le_def.mp (MMP.Mori.RationalMap.transformDivisor_nonneg φ
      (Finsupp.le_def.mpr fun Q => by simpa [DivisorWithCoeffs.coeff_apply] using hB Q)) P
    rw [hBYeq]
    simpa [DivisorWithCoeffs.coeff_apply] using this
  -- the log minimal model
  have hres : IsLogComparisonResolution sX sY (r ≫ p ≫ sX) φ KX B KY BY' (r ≫ p) q H GV
      (GY - CV) :=
    { isVariety := hVv
      isSmoothScheme := hVsm
      comp_eq_left := Category.assoc _ _ _
      comp_eq_right := hqs
      isProjectiveMorphism_left := hpVp
      isProjectiveMorphism_right := hqp
      isBirationalMorphism_left := hpVb
      isBirationalMorphism_right := hqb
      isInverse := hH
      compHom_eq := rfl
      exists_canonicalDivisor := ⟨mV, KV, hKV, hKVX, hKVq⟩
      isRCartierPullback_left := hGVX
      isRCartierPullback_right := hGZ
      effective := hEeff'
      isExceptional := hEexc }
  refine ⟨BY', φ,
    { isRealLcPair := ⟨hXn, hB, hklt.2.2.1, fun n E a ha => (hklt.2.2.2 n E a ha).le⟩
      isCanonicalDivisor := ⟨n, hKX⟩
      comp_eq := hπ
      isNormalVariety_model := hYn
      isCanonicalDivisor_model := ⟨mY, hKY⟩
      isProjectiveVariety_model := hYp
      comp_eq_model := hπY
      isQFactorial := hYq
      isRealDltPair := isRealDltPair_of_isRealKltPair hBY'0 hkltY
      isBirational := hφb
      isOver := hφZ
      coeff_boundary := fun F => by rw [if_neg (hnoext F), add_zero, hBYeq]
      isRelativelyNef := hnefY'
      exists_resolution := ⟨V, inferInstance, inferInstance, inferInstance, r ≫ p ≫ sX, r ≫ p, q,
        H, GV, GY - CV, hres⟩
      exists_resolution_pos := ⟨V, inferInstance, inferInstance, inferInstance, r ≫ p ≫ sX,
        r ≫ p, q, H, GV, GY - CV, hres, hposX⟩ }, hkltY, hnoext⟩

end Transfer

private theorem solution
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
    {KX : Divisor X} {B : RDivisor X}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hZn : IsNormalVariety ℂ sZ) (hπ : π ≫ sZ = sX) (hπp : IsProjectiveMorphism π)
    (hπb : IsBirationalMorphism π) (hdim : topologicalKrullDim X = 4) (hXq : IsQFactorial sX)
    (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m)
    (hB : ∀ P, 0 ≤ B.coeff P) (hklt : IsRealKltPair sX B) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : CompactSpace Y) (_ : IsLocallyNoetherian Y)
      (_ : IsNormal Y) (sY : Y ⟶ Spec (.of ℂ)) (πY : Y ⟶ Z) (KY : Divisor Y) (BY : RDivisor Y)
      (φ : X.RationalMap Y),
      IsRealLogMinimalModel sX sY sZ π πY KX B KY BY φ ∧ IsRealKltPair sY BY ∧
        ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F := by
  obtain ⟨n, hKXn⟩ := hKX
  obtain ⟨M, hM0, ⟨TX, A, c, T₀, T₀', w, hT, hw, hTX0, hTXc, hA0, hAamp, hAle, hklt', hnum,
    hAM⟩, -⟩ := exists_isRealKltPair_add_pullback_isAmple_le_of_isBirationalMorphism sX sZ hX hXq
      hZ hZn π hπ hπp hπb KX hKXn B hB hklt
  have hTtriv : IsNumericallyTrivialOver ℂ sX π (QDivisor.toRDivisor TX) :=
    MMP.Fourfold.isNumericallyTrivialOver_of_qLinearlyEquivalent_smul_weilDivisor sX sZ hX hXq hZ
      hZn π hπ hπb hT hw hTXc
  obtain ⟨W, _, _, _, _, p, _, hWp, hWsm, hWdim, hpp, hpb, KW, hKW, hKWX, Γ, MW, F₀, G, CW, AW,
    hΓ0, hΓ1, hMW0, hsnc, hKBM, hAWa, hAW0, hAWΓ, hAWfl, hAWM, hΓklt, hG, hKΓ, hCW, hF₀, hF₀Q,
    hF₀E⟩ := exists_logSmoothModel hX hXq hπ hdim hKXn hB
      (fun P => by simpa using hTX0 P) hklt' hTtriv hM0 hnum hAamp hA0 hAle hAM
  obtain ⟨Y, _, _, _, _, sY, πY, KY, BY, φW, hYW⟩ :=
    exists_isRealLogMinimalModel_of_isSNC (π := p ≫ π) hWp hWsm hWdim hZ
      (by rw [Category.assoc, hπ]) ⟨n, hKW⟩ hΓ0 hΓ1 hMW0 hsnc hKBM hAWa hAW0 hAWΓ hAWfl hAWM
  obtain ⟨BY', φ, h1, h2, h3⟩ := exists_model_of_logSmoothModel hX hZ hπ hXq hKXn hB hklt hWp
    hWsm hpp hpb hKWX hΓ0 hΓklt hG hKΓ hCW hF₀ hF₀Q hF₀E hYW
  exact ⟨Y, inferInstance, inferInstance, inferInstance, inferInstance, sY, πY, KY, BY', φ, h1,
    h2, h3⟩

end Proof_thm_fourfold_real_birational_fourfold_log_model

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Real klt fourfolds over a birational base have log minimal models.** Let `π : X ⟶ Z` be a
projective birational morphism of normal projective complex varieties, with `X` a `ℚ`-factorial
fourfold and `K_X` a canonical divisor of `X`. Every effective real klt pair `(X, B)` has a log
minimal model `(Y/Z, B_Y)` with birational map `φ : X ⤏ Y` over `Z` such that `(Y, B_Y)` is klt
and `φ` extracts no prime divisor. -/
@[mmp "thm_fourfold_real_birational_fourfold_log_model"]
public theorem exists_isRealLogMinimalModel_of_isBirationalMorphism
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
    {KX : Divisor X} {B : RDivisor X}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hZn : IsNormalVariety ℂ sZ) (hπ : π ≫ sZ = sX) (hπp : IsProjectiveMorphism π)
    (hπb : IsBirationalMorphism π) (hdim : topologicalKrullDim X = 4) (hXq : IsQFactorial sX)
    (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m)
    (hB : ∀ P, 0 ≤ B.coeff P) (hklt : IsRealKltPair sX B) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : CompactSpace Y) (_ : IsLocallyNoetherian Y)
      (_ : IsNormal Y) (sY : Y ⟶ Spec (.of ℂ)) (πY : Y ⟶ Z) (KY : Divisor Y) (BY : RDivisor Y)
      (φ : X.RationalMap Y),
      IsRealLogMinimalModel sX sY sZ π πY KX B KY BY φ ∧ IsRealKltPair sY BY ∧
        ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F :=
          by revert X Z sX sZ π KX B hX hZ hZn hπ hπp hπb hdim hXq hKX hB hklt; first | exact Proof_thm_fourfold_real_birational_fourfold_log_model.solution | exact Proof_thm_fourfold_real_birational_fourfold_log_model.solution _ | exact Proof_thm_fourfold_real_birational_fourfold_log_model.solution _ _ | exact Proof_thm_fourfold_real_birational_fourfold_log_model.solution _ _ _ | exact Proof_thm_fourfold_real_birational_fourfold_log_model.solution _ _ _ _

end MMP.Fourfold

