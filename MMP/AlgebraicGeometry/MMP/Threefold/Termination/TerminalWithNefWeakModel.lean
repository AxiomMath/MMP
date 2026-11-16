module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
import MMP.AlgebraicGeometry.MMP.Threefold.Contraction.RealKltElementaryStep
import MMP.AlgebraicGeometry.MMP.Flip.PicardNumber
import MMP.AlgebraicGeometry.MMP.Contraction.PicardNumberDropDlt
import MMP.AlgebraicGeometry.Intersection.PicardNumberFiniteComplex
import MMP.AlgebraicGeometry.MMP.Termination.RealCanonicalThreefoldFlips
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
import MMP.AlgebraicGeometry.MMP.Termination.RealCanonicalDifficulty
import MMP.AlgebraicGeometry.Intersection.SmallModificationPicardNumber
import MMP.AlgebraicGeometry.MMP.Contraction.ExtremalContractionTrichotomy
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleBasics
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonEquality
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DivisorOverRealization
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.MMP.ConeTheorem.SupportingDivisorStein
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
import MMP.AlgebraicGeometry.MMP.Flip.SmallAmpleModel
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.MMP.MinimalModel.RealKltCompactification
import MMP.AlgebraicGeometry.Resolution.StratumBlowupRelativelyAmple
import MMP.AlgebraicGeometry.Singularities.PltTerminalRestriction
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Termination of terminal programs with a crepant nef weak model

Let `π : Y ⟶ S` be a morphism of projective complex varieties, with `Y` a `ℚ`-factorial
threefold, and let `(Y, C)` be a real terminal pair with canonical divisor `K`. Suppose
`φ : Y ⤏ Z` is a `ℚ`-factorial nef weak model of `(Y, C)` over `S` such that the comparison
`p^*(K + C) - q^*(K_Z + φ_* C)` on a common resolution `p : W ⟶ Y`, `q : W ⟶ Z` has coefficient
zero along the strict transform of every prime divisor `P` with positive coefficient in `C`.

Then every `(K + C)`-program over `S` from `(Y, C)` — a sequence of divisorial contractions of
`(K_i + C_i)`-negative extremal rays of `NE̅(Y_i/S)` and of real flips of the small contractions of
such rays, through projective `ℚ`-factorial models over `S`, the boundaries being the successive
birational transforms — has finitely many steps, contracts no prime divisor with positive
coefficient in the boundary, and passes only through real terminal pairs; and there is such a
program which ends with an adjoint `K_n + C_n` nef over `S`.

## Main results

* `MMP.Fourfold.IsRealTerminalPair.terminates_of_isNefWeakModel`.

## Implementation notes

The program is spelled out as data indexed as in `MMP.Fourfold.RelativeDltProgram`: models
`Y₀ = Y`, `Y_{i+1} = Yi i` over `S`, a number `n ∈ ℕ ∪ {∞}` of steps, and for `i < n` a
`(K_i + C_i)`-negative extremal ray `R_i` of `NE̅(Y_i/S)` (negativity through
`MMP.Flips.IsRIntersectionNumber`) with its contraction `f_i : Y_i ⟶ Z_i`, `g_i : Z_i ⟶ S`
over `S` (`MMP.Mori.IsRelativeContractionOfFace`, `MMP.Flips.IsNegativeExtremalContraction`),
followed by `f_i⁺ : Y_{i+1} ⟶ Z_i` over `S` which is an isomorphism when `f_i` is divisorial and
a real flip (`MMP.Fourfold.IsRealFlipStep`) otherwise; in both cases
`C_{i+1} = (f_i⁺)⁻¹_* (f_i)_* C_i`. The comparison coefficient at a prime `P` of `Y` is the
coefficient at its strict transform `h_* P` on `W`, `h : Y ⤏ W` the inverse of `p`; it does not
depend on the resolution, and the hypothesis asks for one resolution on which it vanishes.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Fourfold MMP.Mori MMP.Flips

namespace Proof_lem_fourfold_terminal_comparison_program

section Stages

/-- A model of a program over `S`: a normal integral scheme over `ℂ` and over `S`, with a
canonical divisor and a real boundary. -/
private structure Stage (S : Scheme.{0}) where
  X : Scheme.{0}
  [isIntegral : IsIntegral X]
  [compactSpace : CompactSpace X]
  [isLocallyNoetherian : IsLocallyNoetherian X]
  [isNormal : IsNormal X]
  sX : X ⟶ Spec (.of ℂ)
  πX : X ⟶ S
  K : Divisor X
  B : RDivisor X

attribute [local instance] Stage.isIntegral Stage.compactSpace Stage.isLocallyNoetherian
  Stage.isNormal

/-- The data of one step from a model `s`: the next model, the ray, its contraction and the
morphism from the next model to the contraction target. -/
private structure StepData {S : Scheme.{0}} (s : Stage S) where
  t : Stage S
  R : Set (RelativeNumericalCurveClasses s.sX s.πX)
  Zs : Scheme.{0}
  sZs : Zs ⟶ Spec (.of ℂ)
  f : s.X ⟶ Zs
  g : Zs ⟶ S
  fp : t.X ⟶ Zs

/-- The models obtained from `s0` by iterating a choice of steps. -/
private noncomputable def Stage.seq {S : Scheme.{0}} (s0 : Stage S)
    (next : (s : Stage S) → StepData s) : ℕ → Stage S
  | 0 => s0
  | i + 1 => (next (Stage.seq s0 next i)).t

attribute [local instance] Stage.isIntegral Stage.compactSpace Stage.isLocallyNoetherian
  Stage.isNormal in
/-- The rays of the iterated sequence of steps, indexed as the models of a program. -/
private noncomputable def Stage.progR {S : Scheme.{0}} (s0 : Stage S)
    (next : (s : Stage S) → StepData s) :
    ∀ i, Set (RelativeNumericalCurveClasses
      (modelStr s0.sX (fun j => (Stage.seq s0 next (j + 1)).sX) i)
      (modelMap s0.πX (fun j => (Stage.seq s0 next (j + 1)).πX) i))
  | 0 => (next s0).R
  | i + 1 => (next (Stage.seq s0 next (i + 1))).R

attribute [local instance] Stage.isIntegral Stage.compactSpace Stage.isLocallyNoetherian
  Stage.isNormal in
/-- The contractions of the iterated sequence of steps, indexed as the models of a program. -/
private noncomputable def Stage.progF {S : Scheme.{0}} (s0 : Stage S)
    (next : (s : Stage S) → StepData s) :
    ∀ i, modelSeq s0.X (fun j => (Stage.seq s0 next (j + 1)).X) i ⟶
      (next (Stage.seq s0 next i)).Zs
  | 0 => (next s0).f
  | i + 1 => (next (Stage.seq s0 next (i + 1))).f

end Stages

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

attribute [local instance] Stage.isIntegral Stage.compactSpace Stage.isLocallyNoetherian
  Stage.isNormal

variable {S Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
  (sS : S ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [QuasiCompact sZ] (πZ : Z ⟶ S)

/-- The comparison of a nef weak model vanishes along every prime with positive boundary
coefficient, on some projective common model. -/
private def ComparisonVanishes {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) (Kw : Divisor X) (B : RDivisor X)
    (φ : X.RationalMap Z) : Prop :=
  ∀ G : MMP.Mori.PrimeDivisor X, 0 < B.coeff G →
    ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ X) (q : W ⟶ Z) (h : X.RationalMap W)
      (GY GZ : RDivisor W) (P : MMP.Mori.PrimeDivisor W),
      MMP.Mori.IsVariety ℂ sW ∧ p ≫ sX = sW ∧ q ≫ sZ = sW ∧ IsProjectiveMorphism p ∧
      IsProjectiveMorphism q ∧ IsBirationalMorphism p ∧ IsBirationalMorphism q ∧
      MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧ h.compHom q = φ ∧
      IsRCartierPullback p (logCanonicalDivisor Kw B) GY ∧
      IsRCartierPullback q
        (logCanonicalDivisor (RationalMap.transformDivisor φ Kw)
          (RationalMap.transformDivisor φ B)) GZ ∧
      RationalMap.transformPrimeDivisor p.toRationalMap P = some G ∧
      (GY - GZ).coeff P = 0

/-- A model of the program which is good: projective, `ℚ`-factorial, over `S`, a threefold,
real terminal, with `Z` as a nef weak model whose comparison vanishes along the boundary. -/
private def IsGood {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) (πX : X ⟶ S) (B : RDivisor X) : Prop :=
  MMP.Mori.IsProjectiveVariety ℂ sX ∧ IsQFactorial sX ∧ πX ≫ sS = sX ∧
    topologicalKrullDim X = 3 ∧ IsRealTerminalPair sX B ∧
    ∃ (Kw : Divisor X) (φ : X.RationalMap Z), IsNefWeakModel sX sZ sS πX πZ Kw B φ ∧
      ComparisonVanishes sZ sX Kw B φ

/-- One step of a program over `S`: a negative extremal ray, its contraction, and a divisorial
contraction or a real flip. -/
private def IsStep {X X' Zs : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    (sX : X ⟶ Spec (.of ℂ)) (sX' : X' ⟶ Spec (.of ℂ)) (sZs : Zs ⟶ Spec (.of ℂ))
    (πX : X ⟶ S) (πX' : X' ⟶ S) (K : Divisor X) (B : RDivisor X) (K' : Divisor X')
    (B' : RDivisor X') (R : Set (RelativeNumericalCurveClasses sX πX)) (f : X ⟶ Zs)
    (g : Zs ⟶ S) (fp : X' ⟶ Zs) : Prop :=
  IsExtremalRay ℝ (relativeClosedConeOfCurves sX πX :
      Set (RelativeNumericalCurveClasses sX πX)) R ∧
    (∀ (Γ : ProperCurve sX) (hΓ : Γ.IsContractedBy πX),
      Γ.relativeClass πX hΓ ∈ R →
      ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
        IsRIntersectionNumber ℂ sX (logCanonicalDivisor K B) r L Γ x → x < 0) ∧
    IsRelativeContractionOfFace πX R f g ∧
    IsNegativeExtremalContraction ℂ sX sZs (logCanonicalDivisor K B) f ∧
    fp ≫ g = πX' ∧
    (((IsBirationalMorphism f ∧ ∃ E : MMP.Mori.PrimeDivisor X,
          (MMP.Mori.exceptionalSet f : Set X) = E.support) ∧
        IsIso fp ∧ (∃ m : ℕ, K'.IsCanonicalDivisor sX' m) ∧ B' = flipTransform f fp B) ∨
      IsRealFlipStep sX sZs sX' K B K' B' f fp)

variable {sS sZ πZ}

/-- The contraction target of a step lies over `S` compatibly with the structure morphisms. -/
private theorem comp_eq_of_isStep {X X' Zs : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)}
    {πX : X ⟶ S} {πX' : X' ⟶ S} {K : Divisor X} {B : RDivisor X} {K' : Divisor X'}
    {B' : RDivisor X'} {R : Set (RelativeNumericalCurveClasses sX πX)} {f : X ⟶ Zs}
    {g : Zs ⟶ S} {fp : X' ⟶ Zs} (hstep : IsStep sX sX' sZs πX πX' K B K' B' R f g fp)
    (hπ : πX ≫ sS = sX) : g ≫ sS = sZs := by
  have hneg := hstep.2.2.2.1
  have hc := hneg.isContraction
  have h1 : f ≫ g ≫ sS = f ≫ sZs := by
    rw [← Category.assoc, hstep.2.2.1.comp_eq, hπ, hc.comp_eq]
  have : IsIso f.appTop := hc.isIso_app ⊤
  refine ext_of_isAffine ?_
  have h2 := congrArg Scheme.Hom.appTop h1
  simp only [Scheme.Hom.comp_appTop] at h2
  exact (cancel_mono (f.appTop)).mp h2

/-- The contraction target of a step is a projective variety. -/
private theorem isProjectiveVariety_target_of_isStep (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    {X X' Zs : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)}
    {πX : X ⟶ S} {πX' : X' ⟶ S} {K : Divisor X} {B : RDivisor X} {K' : Divisor X'}
    {B' : RDivisor X'} {R : Set (RelativeNumericalCurveClasses sX πX)} {f : X ⟶ Zs}
    {g : Zs ⟶ S} {fp : X' ⟶ Zs} (hstep : IsStep sX sX' sZs πX πX' K B K' B' R f g fp)
    (hπ : πX ≫ sS = sX) : MMP.Mori.IsProjectiveVariety ℂ sZs := by
  have hv : AlgebraicGeometry.IsVariety ℂ sZs := hstep.2.2.2.1.isNormalVariety_target.1
  rw [← comp_eq_of_isStep hstep hπ] at hv ⊢
  exact { toIsVariety := hv,
          isProjective := hstep.2.2.1.isProjectiveMorphism.comp hS.isProjective }

/-- Both morphisms of a step are birational. -/
private theorem isBirationalMorphism_of_isStep {X X' Zs : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)}
    {πX : X ⟶ S} {πX' : X' ⟶ S} {K : Divisor X} {B : RDivisor X} {K' : Divisor X'}
    {B' : RDivisor X'} {R : Set (RelativeNumericalCurveClasses sX πX)} {f : X ⟶ Zs}
    {g : Zs ⟶ S} {fp : X' ⟶ Zs} (hstep : IsStep sX sX' sZs πX πX' K B K' B' R f g fp) :
    IsBirationalMorphism f ∧ IsBirationalMorphism fp := by
  rcases hstep.2.2.2.2.2 with ⟨⟨hb, -⟩, hiso, -, -⟩ | hfl
  · exact ⟨hb, isBirationalMorphism_of_isIso fp⟩
  · exact ⟨hfl.isBirationalMorphism, hfl.isBirationalMorphism_flip⟩

/-- A step preserves the dimension. -/
private theorem topologicalKrullDim_eq_of_isStep {X X' Zs : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)}
    {πX : X ⟶ S} {πX' : X' ⟶ S} {K : Divisor X} {B : RDivisor X} {K' : Divisor X'}
    {B' : RDivisor X'} {R : Set (RelativeNumericalCurveClasses sX πX)} {f : X ⟶ Zs}
    {g : Zs ⟶ S} {fp : X' ⟶ Zs} (hstep : IsStep sX sX' sZs πX πX' K B K' B' R f g fp)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hX' : MMP.Mori.IsProjectiveVariety ℂ sX') :
    topologicalKrullDim X' = topologicalKrullDim X := by
  have : MMP.Mori.IsVariety ℂ sZs := hstep.2.2.2.1.isNormalVariety_target.1
  have : MMP.Mori.IsVariety ℂ sX := hX.toIsVariety
  have : MMP.Mori.IsVariety ℂ sX' := hX'.toIsVariety
  obtain ⟨hb, hbp⟩ := isBirationalMorphism_of_isStep hstep
  exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZs sX' hbp).symm.trans
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZs sX hb)

private theorem residueFieldDegree_pos_ph {V T : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)}
    {sT : T ⟶ Spec (.of ℂ)} [IsSeparated sT] [LocallyOfFiniteType sT] (u : V ⟶ T)
    (hu : u ≫ sT = sV) (Γ : ProperCurve sV) (h : ¬ Γ.IsContractedBy u) :
    0 < residueFieldDegree u Γ.point := by
  have hnc := Oai4C1.not_exists_range_eq_singleton u Γ h
  set φ := Γ.ι ≫ u with hφdef
  have hφ : φ ≫ sT = Γ.ι ≫ sV := by rw [hφdef, Category.assoc, hu]
  have : IsProper (φ ≫ sT) := hφ ▸ inferInstance
  have hP : IsProper φ := IsProper.of_comp _ sT
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve ℂ (φ ≫ sT) := hφ ▸ inferInstance
  have hc : AlgebraicGeometry.IsCurve ℂ (φ.imageι ≫ sT) := isCurve_imageι_comp sT φ hnc
  have : IsIntegral φ.image := hc.toIsIntegral
  have hLφ : LocallyOfFiniteType φ := hP.toLocallyOfFiniteType
  have : QuasiCompact φ := instQuasiCompactOfUniversallyClosed φ
  have : LocallyOfFiniteType φ.toImage := by
    have : LocallyOfFiniteType (φ.toImage ≫ φ.imageι) := by
      rw [Scheme.Hom.toImage_imageι]; exact hLφ
    exact locallyOfFiniteType_of_comp _ φ.imageι
  have : IsDominant φ.toImage := Scheme.instIsDominantToImageOfQuasiCompact φ
  have hdeg : residueFieldDegree u Γ.point = degreeOver φ.toImage := by
    have h1 := residueDegree_comp Γ.ι u (genericPoint Γ.scheme)
    rw [Γ.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion Γ.ι, mul_one]
      at h1
    have h2 := residueDegree_comp φ.toImage φ.imageι (genericPoint Γ.scheme)
    rw [Scheme.Hom.toImage_imageι,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ.imageι,
      one_mul, residueDegree_genericPoint_eq_degreeOver φ.toImage] at h2
    exact h1.symm.trans h2
  rw [hdeg]
  letI := (functionFieldMap φ.toImage).toAlgebra
  have hfin : Module.Finite φ.image.functionField Γ.scheme.functionField :=
    finite_functionField_image sT φ hnc
  have heq : functionFieldMap φ.toImage = dominantFunctionFieldMap φ.toImage :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target φ.toImage (genericPoint Γ.scheme)
        (map_genericPoint_of_isDominant φ.toImage))).symm
  rw [degreeOver_eq_finrank φ.toImage heq]
  exact Module.finrank_pos

/-- **Push-forward of curve classes.** For a surjective morphism `f : X ⟶ Y` of projective complex
varieties, `f_* : N₁(X) ⟶ N₁(Y)` is surjective, so `ρ(Y) ≤ ρ(X)`; if some curve contracted by `f`
has a nonzero class, then `ρ(Y) < ρ(X)`. -/
private theorem picardNumber_le_of_surjective {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sY : Y ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (f : X ⟶ Y) [Surjective f] (hf : f ≫ sY = sX) :
    picardNumber sY ≤ picardNumber sX ∧
      ∀ Γ : ProperCurve sX, Γ.IsContractedBy f → OneCycle.numericalClass sX (Γ.cycle ℝ) ≠ 0 →
        picardNumber sY < picardNumber sX := by
  haveI : IsSeparated sY := hY.toIsVariety.toIsSeparated
  haveI : LocallyOfFiniteType sY := hY.toIsVariety.toLocallyOfFiniteType
  haveI : QuasiCompact sY := hY.toIsVariety.toQuasiCompact
  haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
  haveI : IsProper f := by subst hf; exact IsProper.of_comp f sY
  set φ := NumericalCurveClasses.pushforward f hf with hφ
  have hspan : ∀ C' : ProperCurve sY,
      OneCycle.numericalClass sY (C'.cycle ℝ) ∈ LinearMap.range φ := by
    intro C'
    obtain ⟨C, hC, -⟩ := ProperCurve.exists_map_eq sX sY f hf C'
    have hnc : ¬ C.IsContractedBy f := by
      intro hc
      subst hf
      refine ProperCurve.not_isProperCurve_of_forall_eq f C (y := f C.point) (fun z => ?_) ?_
      · exact hc _ (C.range_ι ▸ ⟨z, rfl⟩)
      · rw [hC]; exact C'.isProperCurve
    have hd := residueFieldDegree_pos_ph f hf C hnc
    have hC'' : (⟨f C.point, hC ▸ C'.isProperCurve⟩ : ProperCurve sY) = C' := by
      cases C'; simp only [ProperCurve.mk.injEq]; exact hC
    have hpush : φ (OneCycle.numericalClass sX (C.cycle ℝ)) =
        (residueFieldDegree f C.point : ℝ) • OneCycle.numericalClass sY (C'.cycle ℝ) := by
      change OneCycle.numericalClass sY (OneCycle.pushforward ℝ sX sY f (C.cycle ℝ)) = _
      rw [OneCycle.pushforward_cycle, cyclePushforwardOfPoint, dif_pos (hC ▸ C'.isProperCurve),
        hC'', ← map_smul]
      congr 1
      simp [ProperCurve.cycle, Finsupp.smul_single]
    refine ⟨((residueFieldDegree f C.point : ℝ))⁻¹ • OneCycle.numericalClass sX (C.cycle ℝ), ?_⟩
    rw [map_smul, hpush, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨z, rfl⟩ := OneCycle.numericalClass_surjective sY y
    induction z using Finsupp.induction_linear with
    | zero => exact ⟨0, by simp⟩
    | add a b ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨x', hx'⟩ := hb
      exact ⟨x + x', by rw [map_add, hx, hx', map_add]⟩
    | single C' a =>
      obtain ⟨x, hx⟩ := hspan C'
      refine ⟨a • x, ?_⟩
      rw [map_smul, hx, ← map_smul]
      congr 1
      simp [ProperCurve.cycle, Finsupp.smul_single]
  have hle : Module.rank ℝ (NumericalCurveClasses sY) ≤ Module.rank ℝ (NumericalCurveClasses sX) :=
    LinearMap.rank_le_of_surjective φ hsurj
  refine ⟨Cardinal.toENat.monotone' hle, fun Γ hΓ hne => ?_⟩
  have hker : OneCycle.numericalClass sX (Γ.cycle ℝ) ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker]
    change OneCycle.numericalClass sY (OneCycle.pushforward ℝ sX sY f (Γ.cycle ℝ)) = 0
    rw [ProperCurve.pushforward_cycle_eq_zero_of_isContractedBy ℝ f hf Γ hΓ, map_zero]
  have hfin : picardNumber sX < ⊤ := by
    haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
    exact MMP.Mori.picardNumber_lt_top_of_isProjectiveVariety sX
  have hrk := LinearMap.rank_range_add_rank_ker φ
  rw [LinearMap.range_eq_top.mpr hsurj, rank_top] at hrk
  have hker1 : 0 < Module.rank ℝ (LinearMap.ker φ) :=
    rank_pos_iff_exists_ne_zero.mpr ⟨⟨_, hker⟩, fun h => hne (congrArg Subtype.val h)⟩
  have hXfin : Module.rank ℝ (NumericalCurveClasses sX) < Cardinal.aleph0 := by
    unfold picardNumber at hfin
    exact Cardinal.toENat_lt_top.mp hfin
  obtain ⟨a, ha⟩ := Cardinal.lt_aleph0.mp (hle.trans_lt hXfin)
  obtain ⟨b, hb⟩ := Cardinal.lt_aleph0.mp
    (lt_of_le_of_lt (le_add_self.trans_eq hrk) hXfin)
  have hpos : 0 < b := by rw [hb] at hker1; exact_mod_cast hker1
  have hXr : Module.rank ℝ (NumericalCurveClasses sX) = ((a + b : ℕ) : Cardinal) := by
    rw [← hrk, ha, hb, Nat.cast_add]
  unfold picardNumber
  rw [ha, hXr, Cardinal.toENat_nat, Cardinal.toENat_nat]
  exact_mod_cast (by omega : a < a + b)

/-- A curve with numerically trivial class has degree zero against every Cartier divisor. -/
private theorem degreeOn_eq_zero_of_numericalClass_eq_zero {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX]
    (Γ : ProperCurve sX) (hΓ : OneCycle.numericalClass sX (Γ.cycle ℝ) = 0) (L : Divisor X)
    (hL : L.IsCartier) : L.degreeOn ℂ sX Γ.ι Γ.dim_le hL = 0 := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  haveI := hL.isInvertibleModule_divisorialSheaf
  have hmem : Γ.cycle ℝ ∈ OneCycle.numericallyTrivial sX :=
    (Submodule.Quotient.mk_eq_zero _).mp hΓ
  have h := OneCycle.mem_numericallyTrivial.mp hmem L.divisorialSheaf
  rw [OneCycle.degree_cycle, ProperCurve.degree_divisorialSheaf Γ L hL] at h
  exact_mod_cast h

/-- A curve on which an `ℝ`-Cartier divisor is negative has a nonzero numerical class. -/
private theorem numericalClass_ne_zero_of_neg {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX]
    {D : RDivisor X} (hD : IsCartierCombination D) (Γ : ProperCurve sX)
    (hneg : ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber ℂ sX D r L Γ x → x < 0) :
    OneCycle.numericalClass sX (Γ.cycle ℝ) ≠ 0 := by
  intro h0
  obtain ⟨m, r, L, hL, hDL⟩ := hD
  have hDL' : D = ∑ j, r j • Divisor.toRDivisor (L j) := by
    simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using hDL
  have hx := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX Γ r L hL
  rw [← hDL'] at hx
  have := hneg m r L _ hx
  simp only [degreeOn_eq_zero_of_numericalClass_eq_zero Γ h0, Int.cast_zero, mul_zero,
    Finset.sum_const_zero, lt_irrefl] at this

/-- The exceptional prime of a divisorial contraction is covered by contracted curves; in
particular some curve is contracted. -/
private theorem exists_properCurve_isContractedBy_of_divisorial {X Zs : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)} {L : RDivisor X} {f : X ⟶ Zs}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hneg : IsNegativeExtremalContraction ℂ sX sZs L f) (hb : IsBirationalMorphism f)
    {E : MMP.Mori.PrimeDivisor X} (hE : (MMP.Mori.exceptionalSet f : Set X) = E.support) :
    ∃ Γ : ProperCurve sX, Γ.IsContractedBy f := by
  have hXv := hneg.isNormalVariety_source
  have hZv := hneg.isNormalVariety_target
  have : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  have : IsProper f := hneg.isContraction.isProper
  have : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have hGmem : E.genericPoint ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  obtain ⟨y, hyE, hyc⟩ := nonempty_inter_closedPoints (Z := E.support) ⟨_, hGmem⟩
    E.idealSheaf.support.isClosed.isLocallyClosed
  have hyEx : y ∈ (MMP.Mori.exceptionalSet f : Set X) := hE ▸ hyE
  obtain ⟨Cs, hCc, hCi, hCd, -, w, hw⟩ :=
    MMP.Mori.exists_isIrreducible_curve_image_eq_singleton_of_mem_exceptionalSet hXv.1 hZv.1 f
      hneg.isContraction.comp_eq hb hneg.isContraction.isIso_app (mem_closedPoints_iff.mp hyc)
      hyEx
  have hgen := hCi.isGenericPoint_genericPoint_closure
  rw [hCc.closure_eq] at hgen
  have hη1 : topologicalKrullDim (curveSubschemeAt hCi.genericPoint) = 1 := by
    rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, hgen.def, hCd]
  refine ⟨⟨hCi.genericPoint, isProperCurve_of_isProper sX hη1⟩, fun x hx => ?_⟩
  change x ∈ closure {hCi.genericPoint} at hx
  rw [hgen.def] at hx
  have h1 : f x ∈ ({w} : Set Zs) := hw ▸ ⟨x, hx, rfl⟩
  have h2 : f hCi.genericPoint ∈ ({w} : Set Zs) := hw ▸ ⟨_, hgen.mem, rfl⟩
  exact h1.trans h2.symm

/-- A curve contracted by the contraction of a step is negative for `K + B`. -/
private theorem neg_of_isStep {X X' Zs : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)}
    {πX : X ⟶ S} {πX' : X' ⟶ S} {K : Divisor X} {B : RDivisor X} {K' : Divisor X'}
    {B' : RDivisor X'} {R : Set (RelativeNumericalCurveClasses sX πX)} {f : X ⟶ Zs}
    {g : Zs ⟶ S} {fp : X' ⟶ Zs} (hstep : IsStep sX sX' sZs πX πX' K B K' B' R f g fp)
    (Γ : ProperCurve sX) (hΓ : Γ.IsContractedBy f) :
    ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber ℂ sX (logCanonicalDivisor K B) r L Γ x → x < 0 := by
  have hΓS : Γ.IsContractedBy πX := fun z hz => by
    rw [← hstep.2.2.1.comp_eq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hΓ z hz]
  exact hstep.2.1 Γ hΓS ((hstep.2.2.1.isContractedBy_iff Γ hΓS).mp hΓ)

/-- **A divisorial step lowers the Picard number.** -/
private theorem picardNumber_lt_of_isStep (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    {X X' Zs : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)}
    {πX : X ⟶ S} {πX' : X' ⟶ S} {K : Divisor X} {B : RDivisor X} {K' : Divisor X'}
    {B' : RDivisor X'} {R : Set (RelativeNumericalCurveClasses sX πX)} {f : X ⟶ Zs}
    {g : Zs ⟶ S} {fp : X' ⟶ Zs} (hstep : IsStep sX sX' sZs πX πX' K B K' B' R f g fp)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hπ : πX ≫ sS = sX)
    (hX' : MMP.Mori.IsProjectiveVariety ℂ sX') (hπ' : πX' ≫ sS = sX')
    (hdiv : (IsBirationalMorphism f ∧ ∃ E : MMP.Mori.PrimeDivisor X,
      (MMP.Mori.exceptionalSet f : Set X) = E.support) ∧ IsIso fp) :
    picardNumber sX' < picardNumber sX := by
  obtain ⟨⟨hb, E, hE⟩, hiso⟩ := hdiv
  have hneg := hstep.2.2.2.1
  have hc := hneg.isContraction
  have hZp := isProjectiveVariety_target_of_isStep hS hstep hπ
  have hfps : fp ≫ sZs = sX' := by
    rw [← comp_eq_of_isStep hstep hπ, ← Category.assoc, hstep.2.2.2.2.1, hπ']
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  haveI : IsProper f := hc.isProper
  haveI : Surjective f := Scheme.Hom.surjective_of_isIso_app f hc.isIso_app
  have h1 : picardNumber sX' ≤ picardNumber sZs :=
    (picardNumber_le_of_surjective hZp hX' (inv fp) (by rw [IsIso.inv_comp_eq, hfps])).1
  obtain ⟨Γ, hΓ⟩ := exists_properCurve_isContractedBy_of_divisorial hX hneg hb hE
  have h2 := (picardNumber_le_of_surjective hX hZp f hc.comp_eq).2 Γ hΓ
    (numericalClass_ne_zero_of_neg hneg.isCartierCombination Γ (neg_of_isStep hstep Γ hΓ))
  exact h1.trans_lt h2

private theorem exists_closeds_isIso_of_isSmall_ph {X Z : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z}
    (hf : MMP.Flips.IsSmall ℂ sZ sX f) :
    ∃ (V : TopologicalSpace.Closeds X) (W : TopologicalSpace.Closeds Z),
      (∀ x ∈ (V : Set X), 2 ≤ Order.coheight x) ∧
      (∀ z ∈ (W : Set Z), 2 ≤ Order.coheight z) ∧ V.compl ≤ f ⁻¹ᵁ W.compl ∧
      IsIso (f ∣_ W.compl) := by
  obtain ⟨V, W, hV, hW, h, hiso⟩ := hf.exists_isIso
  have hV' := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV
  have hW' := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hW
  refine ⟨V, W, hV', hW', h, ?_⟩
  haveI : IsProper f := hf.isProper
  set U := f ⁻¹ᵁ W.compl
  set g := f ∣_ W.compl
  set j := X.homOfLE h
  have hjg : j ≫ g = f.resLE W.compl V.compl h := rfl
  set s := inv (f.resLE W.compl V.compl h) ≫ j
  have hs : s ≫ g = 𝟙 _ := by simp [s, hjg]
  haveI : IsClosedImmersion (s ≫ g) := by rw [hs]; infer_instance
  haveI : IsClosedImmersion s := IsClosedImmersion.of_comp s g
  have hj : j = f.resLE W.compl V.compl h ≫ s := by simp [s]
  haveI : IsClosedImmersion j := by rw [hj]; infer_instance
  have hgen : genericPoint X ∈ (V.compl : Set X) := by
    intro hgV
    have := hV' (genericPoint X) hgV
    rw [Order.coheight_eq_zero.mpr (fun z _ => genericPoint_specializes z)] at this
    exact absurd this (by decide)
  haveI : Nonempty U := ⟨⟨_, h hgen⟩⟩
  have hclopen : IsClopen (Set.range j) :=
    ⟨j.isClosedEmbedding.isClosed_range, j.isOpenEmbedding.isOpen_range⟩
  have hne : (Set.range j).Nonempty := ⟨_, ⟨⟨_, hgen⟩, rfl⟩⟩
  have hrange : Set.range j = Set.univ := (isClopen_iff.mp hclopen).resolve_left hne.ne_empty
  haveI : Surjective j := ⟨Set.range_eq_univ.mp hrange⟩
  haveI : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨inferInstance, inferInstance⟩
  have hg : g = inv j ≫ f.resLE W.compl V.compl h := by rw [← hjg]; simp
  change IsIso g
  rw [hg]
  infer_instance

private theorem mem_biregularLocus_of_isSmall_ph {X Z : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [IsLocallyNoetherian X] [IsNormal X]
    {f : X ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f) {z : Z} (hz : Order.coheight z ≤ 1) :
    z ∈ biregularLocus f := by
  obtain ⟨V, W, -, hW, -, hiso⟩ := exists_closeds_isIso_of_isSmall_ph hf
  have hzW : z ∈ (W.compl : Set Z) := fun h => absurd ((hW z h).trans hz) (by decide)
  exact le_biregularLocus hiso hzW

/-- A small contraction maps the generic point of a prime divisor to a point of coheight one,
in its biregular locus. -/
private theorem coheight_map_genericPoint_of_isSmall {X Z : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z}
    (hf : MMP.Flips.IsSmall ℂ sZ sX f) (P : MMP.Mori.PrimeDivisor X) :
    Order.coheight (f P.genericPoint) = 1 ∧ f P.genericPoint ∈ biregularLocus f := by
  obtain ⟨V, W, hV, -, h, hiso⟩ := exists_closeds_isIso_of_isSmall_ph hf
  have hPV : P.genericPoint ∈ (V.compl : Set X) := fun hP =>
    absurd (hV _ hP) (by rw [P.coheight_genericPoint]; decide)
  have hb : f P.genericPoint ∈ biregularLocus f := le_biregularLocus hiso (h hPV)
  exact ⟨by rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb,
    P.coheight_genericPoint], hb⟩

/-- **A real flip preserves the Picard number**: `X` and `X⁺` are isomorphic over the open set of
`Z` over which both `f` and `f⁺` are isomorphisms, whose complements have codimension two. -/
private theorem picardNumber_eq_of_isRealFlipStep {X X' Zs : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    {sZs : Zs ⟶ Spec (.of ℂ)} {K : Divisor X} {B : RDivisor X} {K' : Divisor X'}
    {B' : RDivisor X'} {f : X ⟶ Zs} {fp : X' ⟶ Zs}
    (hfl : IsRealFlipStep sX sZs sX' K B K' B' f fp) (hXQ : IsQFactorial sX)
    (hXp : MMP.Mori.IsProjectiveVariety ℂ sX) (hX'Q : IsQFactorial sX')
    (hX'p : MMP.Mori.IsProjectiveVariety ℂ sX') : picardNumber sX' = picardNumber sX := by
  have hsm := hfl.isSmall
  have hsm' := hfl.isSmall_flip
  have hfs : f ≫ sZs = sX := hsm.comp_eq
  have hfps : fp ≫ sZs = sX' := hsm'.comp_eq
  set U : Zs.Opens := biregularLocus f ⊓ biregularLocus fp with hU
  haveI hUf : IsIso (f ∣_ U) := isBiregular_iff_le_biregularLocus.mpr inf_le_left
  haveI hUfp : IsIso (fp ∣_ U) := isBiregular_iff_le_biregularLocus.mpr inf_le_right
  have hmem : ∀ {Y : Scheme.{0}} [IsIntegral Y] {sY : Y ⟶ Spec (.of ℂ)} {u : Y ⟶ Zs},
      MMP.Flips.IsSmall ℂ sZs sY u → ∀ y : Y, Order.coheight y ≤ 1 → u y ∈ U := by
    intro Y _ sY u hu y hy
    obtain ⟨V₁, W₁, hV₁, -, hle, hiso⟩ := exists_closeds_isIso_of_isSmall_ph hu
    have hyV : y ∈ (V₁.compl : Set Y) := fun h => absurd ((hV₁ y h).trans hy) (by decide)
    have hb : u y ∈ biregularLocus u := le_biregularLocus hiso (hle hyV)
    have hco : Order.coheight (u y) ≤ 1 :=
      (MMP.Positivity.coheight_map_of_mem_biregularLocus u hb).trans_le hy
    exact ⟨mem_biregularLocus_of_isSmall_ph hsm hco, mem_biregularLocus_of_isSmall_ph hsm' hco⟩
  set V : TopologicalSpace.Closeds X := (f ⁻¹ᵁ U).compl with hV
  set W : TopologicalSpace.Closeds X' := (fp ⁻¹ᵁ U).compl with hW
  have hVc : V.compl = f ⁻¹ᵁ U := by
    ext x
    simp [V]
  have hWc : W.compl = fp ⁻¹ᵁ U := by
    ext x
    simp [W]
  have hcod : ∀ {Y : Scheme.{0}} [IsIntegral Y] {sY : Y ⟶ Spec (.of ℂ)} {u : Y ⟶ Zs},
      MMP.Flips.IsSmall ℂ sZs sY u →
        2 ≤ closedsCodimension (u ⁻¹ᵁ U).compl := by
    intro Y _ sY u hu
    rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
    intro y hy
    by_contra h
    exact hy (hmem hu y (Order.le_of_lt_add_one (by simpa [one_add_one_eq_two] using h)))
  let e : Scheme.Opens.toScheme (X := X) V.compl ≅ Scheme.Opens.toScheme (X := X') W.compl :=
    X.isoOfEq hVc ≪≫ asIso (f ∣_ U) ≪≫ (asIso (fp ∣_ U)).symm ≪≫ X'.isoOfEq hWc.symm
  have he : e.hom ≫ Scheme.Opens.ι (X := X') W.compl ≫ sX' =
      Scheme.Opens.ι (X := X) V.compl ≫ sX := by
    simp only [e, Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, Category.assoc,
      Scheme.isoOfEq_hom_ι_assoc]
    rw [← hfps, ← hfs, ← morphismRestrict_ι_assoc, IsIso.inv_hom_id_assoc,
      morphismRestrict_ι_assoc, Scheme.isoOfEq_hom_ι_assoc]
  exact (picardNumber_eq_of_isoInCodimOne sX sX' hXQ hXp hX'Q hX'p V W (hcod hsm) (hcod hsm')
    e he).symm

/-- A coefficientwise `ℝ`-Cartier divisor is an `ℝ`-Cartier combination. -/
private theorem isCartierCombination_of_isRCartier {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {D : RDivisor X} (hD : RDivisor.IsRCartier D) : IsCartierCombination D := by
  obtain ⟨m, r, L, hL, hc⟩ := hD
  refine ⟨m, r, L, hL, ?_⟩
  simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs]
  refine DivisorWithCoeffs.ext' fun Γ => ?_
  rw [MMP.Flips.coeff_sum_smul_toRDivisor]
  exact hc Γ

private theorem isCartierCombination_of_isQFactorial_ph {X : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hq : IsQFactorial sX) (G : RDivisor X) : IsCartierCombination G :=
  isCartierCombination_of_isRCartier (hq.isRCartier G)

private theorem exists_primeDivisor_map_eq_of_isSmall_ph {X X' Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hf : MMP.Flips.IsSmall ℂ sZ sX f) (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp)
    (P : MMP.Mori.PrimeDivisor X) :
    ∃ P' : MMP.Mori.PrimeDivisor X', fp P'.genericPoint = f P.genericPoint := by
  obtain ⟨hz, -⟩ := coheight_map_genericPoint_of_isSmall hf P
  have hb := mem_biregularLocus_of_isSmall_ph hfp hz.le
  obtain ⟨x', hx'⟩ :=
    hfp.toIsBirationalContraction.surjective_and_isBirational.1.surj (f P.genericPoint)
  have hc : Order.coheight x' = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hx' ▸ hb), hx', hz]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc,
    (congrArg fp (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x' hc)).trans hx'⟩

private theorem flipTransform_apply_of_isSmall_ph {X X' Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsIntegral Z] (hZ : IsNormalVariety ℂ sZ)
    {f : X ⟶ Z} {fp : X' ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) (hfb : IsBirationalMorphism f)
    {P : MMP.Mori.PrimeDivisor X} {P' : MMP.Mori.PrimeDivisor X'}
    (hPP' : fp P'.genericPoint = f P.genericPoint) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) : flipTransform f fp D P' = D P := by
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI : IsProper f := hf.isProper
  haveI := hfb.isDominant
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  obtain ⟨hz, -⟩ := coheight_map_genericPoint_of_isSmall hf P
  set Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hz
  have hQ : f P.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hz).symm
  have := Q.isDiscreteValuationRing_localRing
  exact flipTransform_apply_of_map_genericPoint hfb.functionFieldMap_bijective
    hfp.toIsBirationalContraction.surjective_and_isBirational.1.surj hQ (hPP'.trans hQ)
    (mem_biregularLocus_of_isSmall_ph hfp (hQ ▸ hz).le) D

/-- An `ℝ`-Cartier combination is `ℝ`-Cartier in the coefficientwise sense. -/
private theorem isRCartier_of_isCartierCombination {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {D : RDivisor X} (hD : IsCartierCombination D) : RDivisor.IsRCartier D := by
  obtain ⟨m, r, L, hL, rfl⟩ := hD
  refine ⟨m, r, L, hL, fun Γ => ?_⟩
  simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs, MMP.Flips.coeff_sum_smul_toRDivisor]

/-- On a `ℚ`-factorial variety, `K + B` is `ℝ`-Cartier for every canonical divisor `K`. -/
private theorem isRCartier_logCanonical_of_isQFactorial {X : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hq : IsQFactorial sX) (K : Divisor X) (B : RDivisor X) :
    RDivisor.IsRCartier (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K + B) :=
  isRCartier_of_isCartierCombination (isCartierCombination_of_isQFactorial_ph hq _)

/-- Adding a Cartier divisor to an `ℝ`-Cartier combination, as an explicit presentation. -/
private theorem exists_presentation_add {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {D : RDivisor X} (hD : IsCartierCombination D) {N : Divisor X} (hN : N.IsCartier) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier),
      D = ∑ j, r j • Divisor.toRDivisor (L j) ∧
      D + Divisor.toRDivisor N = ∑ j : Fin (m + 1), (Fin.snoc r 1 : Fin (m + 1) → ℝ) j •
        Divisor.toRDivisor ((Fin.snoc L N : Fin (m + 1) → Divisor X) j) := by
  obtain ⟨m, r, L, hL, hDL⟩ := hD
  have hDL' : D = ∑ j, r j • Divisor.toRDivisor (L j) := by
    simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using hDL
  refine ⟨m, r, L, hL, hDL', ?_⟩
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, one_smul, hDL']

/-- Adding a Cartier divisor keeps an `ℝ`-Cartier combination. -/
private theorem isCartierCombination_add_divisor {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {D : RDivisor X} (hD : IsCartierCombination D) {N : Divisor X}
    (hN : N.IsCartier) : IsCartierCombination (D + Divisor.toRDivisor N) := by
  obtain ⟨m, r, L, hL, -, h⟩ := exists_presentation_add hD hN
  refine ⟨m + 1, Fin.snoc r 1, Fin.snoc L N, fun j => ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa using hN
    · simpa using hL i
  · simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using h

/-- **Adding a principal divisor does not change intersection numbers**: `D + div(φ) ≡_f D`. -/
private theorem isNumericallyEquivalentOver_add_of_linearlyEquivalent {X Y : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX]
    (f : X ⟶ Y) {D : RDivisor X} (hD : IsCartierCombination D) {N : Divisor X}
    (hNc : N.IsCartier) (hN : N.LinearlyEquivalent 0) :
    IsNumericallyEquivalentOver ℂ sX f (D + Divisor.toRDivisor N) D := by
  obtain ⟨m, r, L, hL, hDL, hDN⟩ := exists_presentation_add hD hNc
  have hL' : ∀ j, ((Fin.snoc L N : Fin (m + 1) → Divisor X) j).IsCartier := fun j => by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa using hNc
    · simpa using hL i
  refine ⟨isCartierCombination_add_divisor hD hNc, hD, fun C _ m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  rw [MMP.Flips.eq_sum_degreeOn_of_isRIntersectionNumber ℂ sX C _ _ hL' hDN h₁,
    MMP.Flips.eq_sum_degreeOn_of_isRIntersectionNumber ℂ sX C r L hL hDL h₂,
    Fin.sum_univ_castSucc]
  have h0 := MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX C.ι C.dim_le hNc hN
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [Divisor.degreeOn_congr (by simp) _ hNc, h0]
  simp only [Int.cast_zero, mul_zero, add_zero]

/-- **Negative extremal contractions do not depend on the canonical divisor**: if `K'` is
linearly equivalent to `K`, a `(K + B)`-negative extremal contraction is `(K' + B)`-negative. -/
private theorem IsNegativeExtremalContraction.of_linearlyEquivalent {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {K K' : Divisor X} {B : RDivisor X}
    {f : X ⟶ Z}
    (h : IsNegativeExtremalContraction ℂ sX sZ (logCanonicalDivisor K B) f)
    (hK : K'.LinearlyEquivalent K) :
    IsNegativeExtremalContraction ℂ sX sZ (logCanonicalDivisor K' B) f := by
  have hXv := h.isNormalVariety_source
  have hZv := h.isNormalVariety_target
  haveI : QuasiCompact sX := hXv.1.toQuasiCompact
  haveI : IsNormal Z := hZv.2
  haveI : LocallyOfFiniteType sZ := hZv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsProper f := h.isContraction.isProper
  obtain ⟨φ, hφ⟩ := hK
  have hNc : (K' - K).IsCartier := hφ ▸ Divisor.isCartier_principalDivisor φ
  have hN : (K' - K).LinearlyEquivalent 0 := ⟨φ, by rwa [sub_zero]⟩
  have hNc' : (K - K').IsCartier := by simpa only [neg_sub] using hNc.neg
  have hN' : (K - K').LinearlyEquivalent 0 := by
    obtain ⟨ψ, hψ⟩ := hN
    exact ⟨ψ⁻¹, by rw [sub_zero, MMP.Mori.principalDivisor_inv, ← hψ, sub_zero, neg_sub]⟩
  have hL : logCanonicalDivisor K' B = logCanonicalDivisor K B + Divisor.toRDivisor (K' - K) := by
    simp only [logCanonicalDivisor, map_sub]
    abel
  have hLneg : -logCanonicalDivisor K' B =
      -logCanonicalDivisor K B + Divisor.toRDivisor (K - K') := by
    rw [hL]
    simp only [map_sub]
    abel
  have hbasics := MMP.Flips.relativelyAmple_basics sX sZ hXv hZv f h.isContraction.comp_eq
  obtain ⟨m, r, L, hm, -, hLa, -⟩ := h.isRelativelyAntiAmple
  have hproj : IsProjective f := hbasics.2.2.2.1 ⟨L ⟨0, hm⟩, hLa ⟨0, hm⟩⟩
  have hAc : IsCartierCombination (-logCanonicalDivisor K B) := by
    obtain ⟨m', r', L', hL', h'⟩ := h.isCartierCombination
    exact ⟨m', -r', L', hL', by rw [h']; simp [Finset.sum_neg_distrib, neg_smul]⟩
  refine
    { isNormalVariety_source := hXv
      isNormalVariety_target := hZv
      isCartierCombination := hL ▸ isCartierCombination_add_divisor h.isCartierCombination hNc
      isContraction := h.isContraction
      isRelativelyAntiAmple := ?_
      relativePicardNumber_eq_one := h.relativePicardNumber_eq_one }
  change IsRelativelyAmple f (-logCanonicalDivisor K' B)
  rw [hLneg]
  exact hbasics.2.2.2.2.2 hproj _ _
    (isNumericallyEquivalentOver_add_of_linearlyEquivalent f hAc hNc' hN')
    h.isRelativelyAntiAmple

/-- The log discrepancy of a prime divisor `Q` of `X` is `1 - coeff_Q B`. -/
private theorem isLogDiscrepancy_ofPrimeDivisor_ph {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] (hX : IsNormalVariety ℂ sX) {n : ℕ}
    {B : RDivisor X} {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKB : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B))
    (Q : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsLogDiscrepancy sX n B (DivisorOver.ofPrimeDivisor ℂ hX Q)
      (1 - B.coeff Q) := by
  have h := MMP.Flips.isDiscrepancy_divisorialValuation hX ω hω hK hKB Q
  have := isLogDiscrepancy_of_isDiscrepancy h (DivisorOver.ofPrimeDivisor ℂ hX Q)
    (inferInstanceAs (IsProper (𝟙 X))) (Valuation.ext fun φ => by
      change Q.divisorialValuation (functionFieldMap (𝟙 X) φ) = _
      rw [MMP.Mori.functionFieldMap_id_apply])
  rwa [← sub_eq_add_neg] at this

private theorem isDiscrepancy_of_isLogDiscrepancy_ph {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] {n : ℕ} {B : RDivisor X}
    {D : DivisorOver ℂ sX} {a : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B D a)
    {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKB : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B)) :
    MMP.Flips.IsDiscrepancy sX n (divisorOfForm ω) B D.valuation (a - 1) :=
  MMP.Fourfold.isDiscrepancy_of_isLogDiscrepancy h.1 hK hKB (E := ⟨D, h.2.1⟩) h

private theorem hasNonemptyCenter_valuation_ph {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] (E : MMP.Flips.ProperDivisorOver ℂ sX) :
    MMP.Flips.HasNonemptyCenter ℂ sX E.valuation := by
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

/-- The pull-back of rational forms along an isomorphism of function fields is surjective. -/
private theorem pullbackForms_surjective {k K K' : Type*} [CommRing k] [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}
    (hbij : Function.Bijective (algebraMap K K')) {ω : ⋀[K]^d Ω[K⁄k]}
    (hω : IsPullbackGenerator K' ω) (m : ℤ) :
    Function.Surjective (pullbackForms (k := k) (K := K) (K' := K') (d := d) m) := by
  intro σ
  set b' := ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m
  set b := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m
  obtain ⟨c, hc⟩ := hbij.2 (b'.repr σ ())
  refine ⟨c • b (), ?_⟩
  have h1 : b.repr (c • b ()) () = c := by
    simp [Module.Basis.repr_self]
  rw [pullbackForms_eq hω, pullbackFormsAlong]
  change algebraMap K K' (b.repr (c • b ()) ()) • b' () = σ
  rw [h1, hc]
  exact basis_unit_repr_smul b' σ

private theorem exists_pullbackRationalPluriForms_eq_ph {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] (g : Y ⟶ X)
    [IsDominant g] (hg : Function.Bijective (functionFieldMap g)) {n : ℕ}
    (hn : topologicalKrullDim X = n) (σ : RationalPluriForms (g ≫ sX) n 1) :
    ∃ ω : RationalPluriForms sX n 1, pullbackRationalPluriForms sX g ω = σ := by
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (g ≫ sX)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sX g
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX g hg hd
  exact pullbackForms_surjective hg hω 1 σ

private theorem isCanonicalDivisor_divisorOfForm_of_isCanonicalDivisor_ph {X : Scheme.{0}}
    [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety ℂ sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {τ : RationalPluriForms sX n 1}
    (hτ : τ ≠ 0) : (divisorOfForm τ).IsCanonicalDivisor sX n :=
  hK.of_linearlyEquivalent <| by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK hτ

/-- An `f`-ample `ℝ`-divisor is `f`-nef. -/
private theorem isRelativelyNef_of_isRelativelyAmple {X Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} [QuasiCompact sX] [IsLocallyNoetherian Z] [IsNormal Z]
    (hXv : IsNormalVariety ℂ sX) (hZv : IsNormalVariety ℂ sZ) (f : X ⟶ Z) [IsProper f]
    (hf : f ≫ sZ = sX) {A : RDivisor X} (hA : IsRelativelyAmple f A) :
    IsRelativelyNef ℂ sX f A := by
  obtain ⟨m, r, L, -, hr, hL, rfl⟩ := hA
  have hc := (MMP.Flips.relativelyAmple_basics sX sZ hXv hZv f hf).2.2.1
  refine ⟨m, r, L, fun j => (hL j).1, rfl, fun C hC x hx => ?_⟩
  obtain ⟨hL', d, -, hd, rfl⟩ := hx
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hr j).le
    (by exact_mod_cast (hc (L j) (hL j) (hL' j) C hC (d j) (hd j)).le)

/-- An `f`-anti-ample `ℝ`-divisor is negative on every curve contracted by `f`. -/
private theorem neg_of_isRelativelyAntiAmple {X Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} [QuasiCompact sX] [IsLocallyNoetherian Z] [IsNormal Z]
    (hXv : IsNormalVariety ℂ sX) (hZv : IsNormalVariety ℂ sZ) (f : X ⟶ Z) [IsProper f]
    (hf : f ≫ sZ = sX) {L : RDivisor X} (hA : IsRelativelyAntiAmple f L) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) :
    ∀ (m : ℕ) (r : Fin m → ℝ) (L' : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber ℂ sX L r L' C x → x < 0 := by
  obtain ⟨m, r, Ls, hm, hr, hL, hLs⟩ := hA
  have hc := (MMP.Flips.relativelyAmple_basics sX sZ hXv hZv f hf).2.2.1
  have hL' : L = ∑ j, (-r j) • Divisor.toRDivisor (Ls j) := by
    rw [← neg_neg L, hLs]
    simp only [neg_smul, Finset.sum_neg_distrib]
  intro m' r' L' x hx
  rw [MMP.Flips.eq_sum_degreeOn_of_isRIntersectionNumber ℂ sX C (fun j => -r j) Ls
    (fun j => (hL j).1) hL' hx]
  have hpos : 0 < ∑ j, r j * ((Ls j).degreeOn ℂ sX C.ι C.dim_le (hL j).1 : ℝ) :=
    Finset.sum_pos (fun j _ => mul_pos (hr j) (by
      exact_mod_cast hc _ (hL j) _ C hC _
        (MMP.Flips.isCartierIntersectionNumber_degreeOn ℂ sX C _ _)))
      ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  simp only [neg_mul, Finset.sum_neg_distrib]
  linarith

private theorem pullbackRationalPluriForms_zero_ph {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {sX : X ⟶ Spec (.of ℂ)} (g : Y ⟶ X) [IsDominant g] {n : ℕ} :
    pullbackRationalPluriForms sX g (0 : RationalPluriForms sX n 1) = 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (g ≫ sX)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sX g
  have h := pullbackForms_smul (K' := Y.functionField) (k := ℂ) (d := n) (m := 1)
    (0 : X.functionField) (0 : RationalPluriForms sX n 1)
  simp only [zero_smul, map_zero] at h
  exact h

/-- A partial isomorphism representing `f` agrees with `f` on its source. -/
private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{0}} [IsReduced Y]
    [IsSeparated (X ↘ CategoryTheory.Limits.terminal Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated
    (S := CategoryTheory.Limits.terminal Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- A representative `g'` of the inverse of a birational morphism `f` is a section of `f` on its
domain. -/
private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{0}} [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ CategoryTheory.Limits.terminal Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated
        (S := CategoryTheory.Limits.terminal Scheme)]
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
private theorem genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some {X Y : Scheme.{0}}
    [IsReduced X] [IsReduced Y] [IsSeparated (X ↘ CategoryTheory.Limits.terminal Scheme)]
    [IsSeparated (Y ↘ CategoryTheory.Limits.terminal Scheme)] {f : Y ⟶ X}
    {g : X.RationalMap Y} (H : MMP.Mori.RationalMap.IsInverse f.toRationalMap g)
    {P : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor g P = some E) :
    f E.genericPoint = P.genericPoint := by
  obtain ⟨e, he, he'⟩ := H
  obtain ⟨g', hP, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp
    (MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hP]
  exact apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP

/-- **An inverse of a proper birational morphism is a morphism in codimension one** (FA 2.4.1):
an inverse `g` of a proper birational morphism `f : Y ⟶ X` onto a normal variety is a map over
`X`, hence defined in codimension one. -/
private theorem isMorphismInCodimOne_of_isInverse {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) (f : Y ⟶ X) (hY : MMP.Mori.IsVariety ℂ (f ≫ sX)) [IsProper f]
    {g : X.RationalMap Y} (H : MMP.Mori.RationalMap.IsInverse f.toRationalMap g) :
    MMP.Flips.RationalMap.IsMorphismInCodimOne g := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : X.IsSeparated := ⟨by rw [← CategoryTheory.Limits.terminal.comp_from sX]; infer_instance⟩
  obtain ⟨e, he, hinv⟩ := H
  have key : e.iso.hom ≫ e.target.ι = e.source.ι ≫ f := by
    obtain ⟨W, hW, hWl, hWr, hEq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp he
    have hWl' : W ≤ e.source := hWl
    have : IsDominant (Y.homOfLE hWl') := AlgebraicGeometry.Opens.isDominant_homOfLE hW _
    refine ext_of_isDominant (Y.homOfLE hWl') ?_
    simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialIso.toPartialMap_hom,
      Scheme.Hom.toPartialMap_hom] at hEq
    refine hEq.trans ?_
    rw [Scheme.topIso_hom, Scheme.homOfLE_ι_assoc]
    exact Scheme.homOfLE_ι_assoc Y (show W ≤ ⊤ from hWr) f
  have hover : MMP.Flips.RationalMap.IsOver (𝟙 X) f g := by
    rw [MMP.Flips.RationalMap.IsOver, ← hinv]
    refine Scheme.PartialMap.toRationalMap_eq_iff.mpr
      ⟨e.target, e.dense_target, le_rfl, le_top, ?_⟩
    change X.homOfLE le_rfl ≫ (e.iso.inv ≫ e.source.ι) ≫ f = X.homOfLE _ ≫ X.topIso.hom ≫ 𝟙 X
    rw [Category.assoc, ← key, Iso.inv_hom_id_assoc]
    simp
  exact MMP.Flips.RationalMap.isMorphismInCodimOne_of_isOver hX (𝟙 X) f _ hover

/-- Let `f : Y ⟶ X` be a proper birational morphism of varieties with `X` normal, and `g` an
inverse of `f`. If `f` sends the generic point of a prime divisor `E` of `Y` to that of a prime
divisor `P` of `X`, then the strict transform of `P` under `g` is `E`. -/
private theorem transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) (f : Y ⟶ X)
    (hY : MMP.Mori.IsVariety ℂ (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f)
    {g : X.RationalMap Y} (H : MMP.Mori.RationalMap.IsInverse f.toRationalMap g)
    {P : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (h : f E.genericPoint = P.genericPoint) :
    MMP.Mori.RationalMap.transformPrimeDivisor g P = some E := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := isSeparated_toTerminal_of_isNormalVariety hX
  have : IsSeparated (Y ↘ CategoryTheory.Limits.terminal Scheme) := by
    rw [show (Y ↘ CategoryTheory.Limits.terminal Scheme) =
      (f ≫ sX) ≫ (Spec (.of ℂ) ↘ CategoryTheory.Limits.terminal Scheme) from
        CategoryTheory.Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsNormal X := hX.2
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsDominant f := hf.isDominant
  have hbij := hf.functionFieldMap_bijective
  have hcod := isMorphismInCodimOne_of_isInverse hX f hY H
  obtain ⟨e, he, he'⟩ := H
  have hdef : MMP.Mori.RationalMap.DefinedAt g P.genericPoint := by
    by_contra hnd
    have h2 := le_closedsCodimension_iff.mp hcod
      (TopologicalSpace.IrreducibleCloseds.closureSingleton P.genericPoint)
      (closure_minimal (Set.singleton_subset_iff.mpr hnd)
        (MMP.Mori.RationalMap.dom g).compl.isClosed)
    rw [codimension_eq_coheight,
      show TopologicalSpace.IrreducibleCloseds.closureSingleton P.genericPoint =
      (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
      Order.coheight_orderIso, P.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  obtain ⟨g', hP, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  refine MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP ?_
  have hy := apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (f E.genericPoint)) := by rw [h]; infer_instance
  have : ValuationRing (X.presheaf.stalk (f (g'.hom ⟨P.genericPoint, hP⟩))) := by
    rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij E.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij (g'.hom ⟨P.genericPoint, hP⟩)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hbij (hy.trans h.symm)

private theorem birationalInverseTransform_apply_of_genericPoint_eq_ph {X Y : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y]
    {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) (f : Y ⟶ X)
    (hY : MMP.Mori.IsVariety ℂ (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (h : f E.genericPoint = P.genericPoint) :
    birationalInverseTransform f hf D E = D P := by
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := isSeparated_toTerminal_of_isNormalVariety hX
  have : IsSeparated (Y ↘ CategoryTheory.Limits.terminal Scheme) := by
    rw [show (Y ↘ CategoryTheory.Limits.terminal Scheme) =
      (f ≫ sX) ≫ (Spec (.of ℂ) ↘ CategoryTheory.Limits.terminal Scheme) from
        CategoryTheory.Limits.terminal.hom_ext _ _]
    infer_instance
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq hX f hY hf hf.isInverse_inverse h)
    (fun P' hP' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hf.isInverse_inverse
        hP').symm.trans h)) D

private theorem birationalInverseTransform_apply_eq_zero_ph {X Y : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of ℂ)} {R : Type*} [AddCommMonoid R]
    (hX : MMP.Mori.IsVariety ℂ sX) {f : Y ⟶ X} (hY : MMP.Mori.IsVariety ℂ (f ≫ sX))
    (hf : IsBirationalMorphism f) (D : DivisorWithCoeffs R X) {E : MMP.Mori.PrimeDivisor Y}
    (h : ∀ P : MMP.Mori.PrimeDivisor X, f E.genericPoint ≠ P.genericPoint) :
    birationalInverseTransform f hf D E = 0 := by
  have : IsSeparated sX := hX.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have : IsSeparated (X ↘ CategoryTheory.Limits.terminal Scheme) := by
    rw [show (X ↘ CategoryTheory.Limits.terminal Scheme) =
      sX ≫ (Spec (.of ℂ) ↘ CategoryTheory.Limits.terminal Scheme) from
        CategoryTheory.Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsSeparated (Y ↘ CategoryTheory.Limits.terminal Scheme) := by
    rw [show (Y ↘ CategoryTheory.Limits.terminal Scheme) =
      (f ≫ sX) ≫ (Spec (.of ℂ) ↘ CategoryTheory.Limits.terminal Scheme) from
        CategoryTheory.Limits.terminal.hom_ext _ _]
    infer_instance
  exact MMP.Flips.mapPrimeDivisors_apply_eq_zero_of_forall_ne (fun P hP =>
    h P (genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hf.isInverse_inverse hP)) D

private theorem map_genericPoint_eq_of_valuation_comap_eq_ph {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} [IsSeparated sY]
    (f : X ⟶ Y) [IsDominant f] (D : DivisorOver ℂ sX) (D' : DivisorOver ℂ sY)
    (hv : D.valuation.comap (functionFieldMap f) = D'.valuation) :
    f (D.f D.E.genericPoint) = D'.f D'.E.genericPoint := by
  refine MMP.Positivity.DivisorOver.eq_of_dominates sY D'.valuation (fun a => ?_) (fun a ha => ?_)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D' _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D' _ rfl) <;>
  rw [← hv, Valuation.comap_apply, functionFieldMap_algebraMap_stalk]
  · exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl _
  · exact MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D _ rfl _
      ((IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ a hu))

/-- A closed point of the exceptional set of a birational contraction lies on a contracted
curve. -/
private theorem exists_properCurve_isContractedBy_of_mem {X Zs : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)} {L : RDivisor X} {f : X ⟶ Zs}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hneg : IsNegativeExtremalContraction ℂ sX sZs L f) (hb : IsBirationalMorphism f)
    {y : X} (hy : y ∈ (MMP.Mori.exceptionalSet f : Set X)) (hyc : IsClosed ({y} : Set X)) :
    ∃ Γ : ProperCurve sX, Γ.IsContractedBy f ∧ y ∈ closure ({Γ.point} : Set X) := by
  have hXv := hneg.isNormalVariety_source
  have hZv := hneg.isNormalVariety_target
  have : IsProper f := hneg.isContraction.isProper
  have : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
  obtain ⟨Cs, hCc, hCi, hCd, hyC, w, hw⟩ :=
    MMP.Mori.exists_isIrreducible_curve_image_eq_singleton_of_mem_exceptionalSet hXv.1 hZv.1 f
      hneg.isContraction.comp_eq hb hneg.isContraction.isIso_app hyc hy
  have hgen := hCi.isGenericPoint_genericPoint_closure
  rw [hCc.closure_eq] at hgen
  have hη1 : topologicalKrullDim (curveSubschemeAt hCi.genericPoint) = 1 := by
    rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, hgen.def, hCd]
  refine ⟨⟨hCi.genericPoint, isProperCurve_of_isProper sX hη1⟩, fun x hx => ?_, ?_⟩
  · change x ∈ closure {hCi.genericPoint} at hx
    rw [hgen.def] at hx
    have h1 : f x ∈ ({w} : Set Zs) := hw ▸ ⟨x, hx, rfl⟩
    have h2 : f hCi.genericPoint ∈ ({w} : Set Zs) := hw ▸ ⟨_, hgen.mem, rfl⟩
    exact h1.trans h2.symm
  · change y ∈ closure {hCi.genericPoint}
    rw [hgen.def]; exact hyC

/-- A morphism that is an isomorphism contracts no curve. -/
private theorem not_isContractedBy_of_isIso {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (f : X ⟶ Y) [IsIso f] (C : ProperCurve sX) : ¬ C.IsContractedBy f := by
  intro hC
  have hinj : Function.Injective f := (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
    (asIso f))).injective
  have hsing : ∀ a b : C.scheme, a = b := fun a b => C.ι.isEmbedding.injective <| by
    have ha : C.ι a ∈ closure ({C.point} : Set X) := C.range_ι ▸ ⟨a, rfl⟩
    have hb : C.ι b ∈ closure ({C.point} : Set X) := C.range_ι ▸ ⟨b, rfl⟩
    exact hinj ((hC _ ha).trans (hC _ hb).symm)
  haveI : Subsingleton C.scheme := ⟨hsing⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- An `ℝ`-Cartier divisor is nef relative to an isomorphism. -/
private theorem isRelativelyNef_of_isIso {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] (f : X ⟶ Y) [IsIso f] {D : RDivisor X}
    (hD : IsCartierCombination D) : IsRelativelyNef ℂ sX f D := by
  obtain ⟨m, r, L, hL, hDL⟩ := hD
  exact ⟨m, r, L, hL, by simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using hDL,
    fun C hC => absurd hC (not_isContractedBy_of_isIso f C)⟩

/-- **A step of a program keeps the pair real terminal.** Let `f : X ⟶ Z` be a `(K + B)`-negative
extremal contraction such that every prime divisor whose generic point lies in `Ex(f)` has
boundary coefficient zero, and `f⁺ : X⁺ ⟶ Z` a proper birational morphism, an isomorphism over
the points of coheight at most one and mapping prime divisors to such points, with `K⁺ + B⁺`
`f⁺`-nef, `B⁺ = (f⁺)⁻¹_* f_* B`. Every exceptional divisor over `X⁺` has log discrepancy at least
that over `X` (FA 2.28, with the forms of `Z` pulled back); if it is exceptional over `X` the
latter exceeds one, and otherwise it is a prime of `X` contracted by `f`, whose log discrepancy `1`
strictly increases since `K + B` is negative on its contracted curves. -/
private theorem isRealTerminalPair_of_step {X X' Zs : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    {sZs : Zs ⟶ Spec (.of ℂ)} {K : Divisor X} {B : RDivisor X} {K' : Divisor X'}
    {f : X ⟶ Zs} {fp : X' ⟶ Zs}
    (hneg : IsNegativeExtremalContraction ℂ sX sZs (logCanonicalDivisor K B) f)
    (hb : IsBirationalMorphism f) [IsProper fp] [Surjective fp] (hbp : IsBirationalMorphism fp)
    (hfp1 : ∀ P' : MMP.Mori.PrimeDivisor X', Order.coheight (fp P'.genericPoint) ≤ 1)
    (hfpU : ∀ z : Zs, Order.coheight z ≤ 1 → z ∈ biregularLocus fp) (hfps : fp ≫ sZs = sX')
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) (hK' : ∃ m : ℕ, K'.IsCanonicalDivisor sX' m)
    (hnef : ∀ K'' : Divisor X', K''.LinearlyEquivalent K' →
      IsRelativelyNef ℂ sX' fp (logCanonicalDivisor K'' (flipTransform f fp B)))
    (hBE : ∀ P : MMP.Mori.PrimeDivisor X,
      P.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set X) → B.coeff P = 0)
    (hT : IsRealTerminalPair sX B) (hXp : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hX'Q : IsQFactorial sX') :
    IsRealTerminalPair sX' (flipTransform f fp B) := by
  classical
  have hXv := hneg.isNormalVariety_source
  have hZv := hneg.isNormalVariety_target
  have hc := hneg.isContraction
  have hfs : f ≫ sZs = sX := hc.comp_eq
  subst hfs hfps
  haveI : IsIntegral Zs := hZv.1.toIsIntegral
  haveI : IsNormal Zs := hZv.2
  haveI : LocallyOfFiniteType sZs := hZv.1.toLocallyOfFiniteType
  haveI : QuasiCompact sZs := hZv.1.toQuasiCompact
  haveI : IsSeparated sZs := hZv.1.toIsSeparated
  haveI : IsLocallyNoetherian Zs := LocallyOfFiniteType.isLocallyNoetherian sZs
  haveI : IsProper f := hc.isProper
  have hX'v : IsNormalVariety ℂ (fp ≫ sZs) := hX'Q.1
  haveI : MMP.Mori.IsVariety ℂ sZs := hZv.1
  haveI : MMP.Mori.IsVariety ℂ (f ≫ sZs) := hXv.1
  haveI : MMP.Mori.IsVariety ℂ (fp ≫ sZs) := hX'v.1
  haveI : CompactSpace Zs := QuasiCompact.compactSpace_of_compactSpace sZs
  haveI : LocallyOfFiniteType (f ≫ sZs) := hXv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fp ≫ sZs) := hX'v.1.toLocallyOfFiniteType
  haveI : QuasiCompact (f ≫ sZs) := hXv.1.toQuasiCompact
  haveI : QuasiCompact (fp ≫ sZs) := hX'v.1.toQuasiCompact
  haveI : IsDominant f := hb.isDominant
  haveI : IsDominant fp := hbp.isDominant
  set B' := flipTransform f fp B with hB'
  -- the forms
  obtain ⟨m, hKm⟩ := hK
  have hdimX : topologicalKrullDim X = m := hKm.topologicalKrullDim_eq
  have hdimZ : topologicalKrullDim Zs = m :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZs (f ≫ sZs) hb).trans
      hdimX
  have hdimX' : topologicalKrullDim X' = m :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZs (fp ≫ sZs)
      hbp).symm.trans hdimZ
  obtain ⟨ωX, hωX0, hωX'⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXv hKm
  have hωX : divisorOfForm ωX = K := DivisorWithCoeffs.ext' hωX'
  obtain ⟨ω, hω⟩ := exists_pullbackRationalPluriForms_eq_ph f hb.functionFieldMap_bijective hdimZ ωX
  have hω0 : ω ≠ 0 := by
    rintro rfl
    exact hωX0 (hω ▸ pullbackRationalPluriForms_zero_ph f)
  set ω' := pullbackRationalPluriForms sZs fp ω with hω'
  have hω'0 : ω' ≠ 0 := MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' fp
    hbp.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hdimZ) hω0
  obtain ⟨m'', hK'm''⟩ := hK'
  have hmm' : m'' = m := by
    have := hK'm''.topologicalKrullDim_eq.symm.trans hdimX'
    exact_mod_cast this
  have hK'm : K'.IsCanonicalDivisor (fp ≫ sZs) m := hmm' ▸ hK'm''
  have hK'c : (divisorOfForm ω').IsCanonicalDivisor (fp ≫ sZs) m :=
    isCanonicalDivisor_divisorOfForm_of_isCanonicalDivisor_ph hX'v hK'm hω'0
  have hKX : divisorOfForm (pullbackRationalPluriForms sZs f ω) = K := by rw [hω, hωX]
  have hKmω : (divisorOfForm ωX).IsCanonicalDivisor (f ≫ sZs) m := hωX ▸ hKm
  have hKBc : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ωX) + B) := by
    rw [hωX]; exact hneg.isCartierCombination
  have hKB'c : IsCartierCombination (logCanonicalDivisor (divisorOfForm ω') B') :=
    isCartierCombination_of_isQFactorial_ph hX'Q _
  -- the boundaries as transforms
  set D : RDivisor Zs := RationalMap.transformDivisor (X := X) f.toRationalMap B with hD
  have hBX : birationalInverseTransform f hb D + (B - birationalInverseTransform f hb D) = B := by
    abel
  have hBY : birationalInverseTransform fp hbp D + (B' - birationalInverseTransform fp hbp D) =
      B' := by abel
  have hZsep := isSeparated_toTerminal_of_isNormalVariety hZv
  have hbrfp : ∀ P' : MMP.Mori.PrimeDivisor X', fp P'.genericPoint ∈ biregularLocus fp :=
    fun P' => hfpU _ (hfp1 P')
  -- every prime divisor of `X⁺` lies over a prime divisor of `Z` and one of `X`
  have hover : ∀ P' : MMP.Mori.PrimeDivisor X', ∃ (Q : MMP.Mori.PrimeDivisor Zs)
      (P : MMP.Mori.PrimeDivisor X), fp P'.genericPoint = Q.genericPoint ∧
        f P.genericPoint = Q.genericPoint ∧ D Q = B P ∧ B' P' = B P := by
    intro P'
    have hco : Order.coheight (fp P'.genericPoint) = 1 :=
      (MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hbrfp _)).trans
        P'.coheight_genericPoint
    set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco with hQdef
    have hQ : Q.genericPoint = fp P'.genericPoint :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
    have hQ' : MMP.Mori.PrimeDivisor.genericPoint Q = fp P'.genericPoint := hQ
    obtain ⟨P₀, hP₀, -, hD₀⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZv hXv hb Q
    refine ⟨Q, P₀, hQ.symm, hP₀, hD₀ B, ?_⟩
    rw [hB']
    haveI := MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing Q
    exact flipTransform_apply_of_map_genericPoint hb.functionFieldMap_bijective fp.surjective
      hP₀ hQ.symm (by rw [hQ']; exact hbrfp _) B
  have hEX : ∀ P : MMP.Mori.PrimeDivisor X, ¬ IsExceptionalPrimeDivisor sZs f P →
      (B - birationalInverseTransform f hb D).coeff P = 0 := by
    intro P _
    rw [DivisorWithCoeffs.coeff_sub, sub_eq_zero]
    simp only [DivisorWithCoeffs.coeff_apply]
    by_cases hQ : ∃ Q : MMP.Mori.PrimeDivisor Zs, f P.genericPoint = Q.genericPoint
    · obtain ⟨Q, hQ⟩ := hQ
      obtain ⟨P₀, hP₀, -, hD₀⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZv hXv hb Q
      haveI := MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing Q
      have hPP₀ : P₀ = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (eq_of_map_eq_of_valuationRing hb.functionFieldMap_bijective hP₀ hQ)
      rw [birationalInverseTransform_apply_of_genericPoint_eq_ph hZv f hXv.1 hb D hQ, hD,
        hD₀ B, hPP₀]
    · rw [birationalInverseTransform_apply_eq_zero_ph hZv.1 hXv.1 hb D
        (fun Q hQ' => hQ ⟨Q, hQ'⟩)]
      have hPE : P.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set X) := by
        rw [SetLike.mem_coe, MMP.Mori.mem_exceptionalSet]
        intro hbr
        have hco := (MMP.Positivity.coheight_map_of_mem_biregularLocus f hbr).trans
          P.coheight_genericPoint
        exact hQ ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
          (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm⟩
      simpa only [DivisorWithCoeffs.coeff_apply] using hBE P hPE
  have hEY : ∀ P : MMP.Mori.PrimeDivisor X', ¬ IsExceptionalPrimeDivisor sZs fp P →
      (B' - birationalInverseTransform fp hbp D).coeff P = 0 := by
    intro P' _
    rw [DivisorWithCoeffs.coeff_sub, sub_eq_zero]
    simp only [DivisorWithCoeffs.coeff_apply]
    obtain ⟨Q, P, hP'Q, -, hDQ, hB'P'⟩ := hover P'
    rw [birationalInverseTransform_apply_of_genericPoint_eq_ph hZv fp hX'v.1 hbp D hP'Q, hDQ,
      hB'P']
  have hAX : IsRelativelyNef ℂ (f ≫ sZs) f (-logCanonicalDivisor K
      (birationalInverseTransform f hb D + (B - birationalInverseTransform f hb D))) := by
    rw [hBX]
    exact isRelativelyNef_of_isRelativelyAmple hXv hZv f rfl hneg.isRelativelyAntiAmple
  have hAY : IsRelativelyNef ℂ (fp ≫ sZs) fp (logCanonicalDivisor (divisorOfForm ω')
      (birationalInverseTransform fp hbp D + (B' - birationalInverseTransform fp hbp D))) := by
    rw [hBY]
    exact hnef _ (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor _ hX'v hK'c hK'm)
  -- the terminality inequality
  have hterm : ∀ (n : ℕ) (E' : DivisorOver ℂ (fp ≫ sZs)) (a' : ℝ), E'.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy (fp ≫ sZs) n B' E' a' → 1 < a' := by
    intro n E' a' hE' ha'
    have hn : m = n := by
      have := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha').symm.trans
        hdimX'
      exact_mod_cast this.symm
    subst hn
    have hE'p : IsProper E'.f := ha'.2.1
    set DZ := MMP.Mori.compDivisorOver fp hX'v hbp E' with hDZ
    have hDZp : IsProper DZ.f := by
      change IsProper (E'.f ≫ fp); infer_instance
    have hvZ : DZ.valuation = E'.valuation.comap (functionFieldMap fp) :=
      MMP.Mori.valuation_compDivisorOver fp hX'v hbp E'
    have hv := hasNonemptyCenter_valuation_ph (⟨DZ, hDZp⟩ : MMP.Flips.ProperDivisorOver ℂ sZs)
    obtain ⟨D₁, hD₁, -⟩ :=
      MMP.Flips.ProperDivisorOver.exists_comap_functionFieldMap_valuation_eq hZv.1 f hXv.1 hb
      (⟨DZ, hDZp⟩ : MMP.Flips.ProperDivisorOver ℂ sZs)
    obtain ⟨a, ha⟩ := exists_isLogDiscrepancy hXv hωX0 hKmω hKBc D₁.toDivisorOver D₁.isProper
    have hdX := isDiscrepancy_of_isLogDiscrepancy_ph ha hωX0 hKmω hKBc
    rw [hωX] at hdX
    have hdY := isDiscrepancy_of_isLogDiscrepancy_ph ha' hω'0 hK'c hKB'c
    have hcmp := isDiscrepancy_le_of_isRelativelyNef hZv hXv hX'v hb hbp hKX rfl hEX hEY hAX hAY
      hv hD₁ hvZ.symm
    have hle : a - 1 ≤ a' - 1 := hcmp.2.2 (a - 1) (a' - 1) (by rw [hBX]; exact hdX)
      (by rw [hBY]; exact hdY)
    by_cases hD₁ex : D₁.toDivisorOver.IsExceptional
    · have := hT.2 m D₁.toDivisorOver a hD₁ex ha
      linarith
    obtain ⟨Q, hQ⟩ := exists_valuation_eq_of_not_isExceptional hXv hD₁ex
    have haQ : a = 1 - B.coeff Q := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha
      (isLogDiscrepancy_ofPrimeDivisor_ph hXv hωX0 hKmω hKBc Q) hQ
    have hc1 : D₁.f D₁.E.genericPoint = Q.genericPoint :=
      MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hXv.1 hQ
    have hc2 : f (D₁.f D₁.E.genericPoint) = DZ.f DZ.E.genericPoint :=
      map_genericPoint_eq_of_valuation_comap_eq_ph f D₁.toDivisorOver DZ hD₁
    rw [hc1] at hc2
    by_cases hQE : Q.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set X)
    · rw [hBE Q hQE, sub_zero] at haQ
      have hbgen : IsGenericPoint (DZ.f DZ.E.genericPoint)
          ((⟨DZ, hDZp⟩ : MMP.Flips.ProperDivisorOver ℂ sZs).center : Set Zs) := by
        change closure {DZ.f DZ.E.genericPoint} = DZ.f '' DZ.E.support
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← Set.image_singleton,
          DZ.f.isClosedMap.closure_image_eq_of_continuous DZ.f.continuous]
      have hiff := isDiscrepancy_eq_iff_isNumericallyTrivialOverPoint hZv hXv hX'v hb hbp hKX rfl
        hEX hEY hAX hAY hv hD₁ hvZ.symm (Bv := ⟨DZ, hDZp⟩) rfl hbgen
        (by rw [hBX]; exact hdX) (by rw [hBY]; exact hdY)
      have hnt : ¬ IsNumericallyTrivialOverPoint ℂ (f ≫ sZs) f
          (logCanonicalDivisor K (birationalInverseTransform f hb D +
            (B - birationalInverseTransform f hb D))) (DZ.f DZ.E.genericPoint) := by
        rw [hBX, ← hc2]
        rintro ⟨-, U, hbU, hU⟩
        haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (f ≫ sZs)
        have hGmem : Q.genericPoint ∈ Q.support := by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
        obtain ⟨y, ⟨hyE, hyU⟩, hyc⟩ := nonempty_inter_closedPoints
          (Z := (Q.support : Set X) ∩ f ⁻¹' (U : Set Zs)) ⟨_, hGmem, hbU⟩
          (Q.idealSheaf.support.isClosed.isLocallyClosed.inter
            (U.isOpen.preimage f.continuous).isLocallyClosed)
        have hyEx : y ∈ (MMP.Mori.exceptionalSet f : Set X) :=
          (MMP.Mori.isClosed_exceptionalSet f).closure_subset_iff.mpr
            (Set.singleton_subset_iff.mpr hQE)
            (by rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact hyE)
        obtain ⟨Γ, hΓ, hyΓ⟩ := exists_properCurve_isContractedBy_of_mem hXp hneg hb hyEx
          (mem_closedPoints_iff.mp hyc)
        have hfy : f Γ.point = f y := (hΓ y hyΓ).symm
        have hyb : f y ∈ closure ({f Q.genericPoint} : Set Zs) := by
          rw [← Set.image_singleton, f.isClosedMap.closure_image_eq_of_continuous f.continuous]
          refine ⟨y, ?_, rfl⟩
          rwa [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        have hyc' : IsClosed ({f y} : Set Zs) := by
          rw [← Set.image_singleton]; exact f.isClosedMap _ (mem_closedPoints_iff.mp hyc)
        obtain ⟨mL, rL, LL, hLL, hLeq⟩ := hneg.isCartierCombination
        have hLeq' : logCanonicalDivisor K B = ∑ j, rL j • Divisor.toRDivisor (LL j) := by
          simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using hLeq
        have hx := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ (f ≫ sZs) Γ rL LL hLL
        rw [← hLeq'] at hx
        have h0 := hU Γ hΓ (hfy ▸ hyU) (hfy ▸ hyb) (hfy ▸ hyc') _ _ _ _ hx
        have hlt := neg_of_isRelativelyAntiAmple hXv hZv f rfl hneg.isRelativelyAntiAmple Γ hΓ _ _ _
          _ hx
        linarith
      have hne : a - 1 ≠ a' - 1 := fun heq => hnt (hiff.mp heq).1
      have hlt : a - 1 < a' - 1 := lt_of_le_of_ne hle hne
      linarith
    · exfalso
      have hηQ : Q.genericPoint ∉ (MMP.Mori.exceptionalSet f : Set X) := hQE
      have hbr : f Q.genericPoint ∈ biregularLocus f := by
        by_contra h; exact hηQ (MMP.Mori.mem_exceptionalSet.mpr h)
      have hco : Order.coheight (f Q.genericPoint) = 1 :=
        (MMP.Positivity.coheight_map_of_mem_biregularLocus f hbr).trans Q.coheight_genericPoint
      have hfx : fp (E'.f E'.E.genericPoint) = f Q.genericPoint := by
        rw [hc2]; rfl
      have hco' : Order.coheight (E'.f E'.E.genericPoint) = 1 := by
        rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp
          (by rw [hfx]; exact hfpU _ hco.le), hfx, hco]
      have h2 := (MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX'v E').mp hE'
      rw [hco'] at h2
      exact absurd h2 (by decide)
  refine ⟨⟨hX'v, fun P' hP' => ?_,
    ⟨m, K', hK'm, isRCartier_logCanonical_of_isQFactorial hX'Q K' B'⟩,
    fun n E' a' hE' ha' => (hterm n E' a' hE' ha').le⟩, hterm⟩
  obtain ⟨Q, P, -, -, -, hB'P'⟩ := hover P'
  simp only [DivisorWithCoeffs.coeff_apply] at hP' ⊢
  rw [hB'P'] at hP' ⊢
  exact hT.1.2.1 P (by simpa only [DivisorWithCoeffs.coeff_apply] using hP')

private theorem exceptionalSet_subset_ph {X Y : Scheme.{0}} (f : Y ⟶ X) :
    MMP.Flips.exceptionalSet f ⊆ (MMP.Mori.exceptionalSet f : Set Y) := by
  intro y hy
  by_contra hyM
  apply hy
  have : IsIso (f ∣_ biregularLocus f) := MMP.Mori.isBiregular_biregularLocus f
  refine ⟨f ⁻¹ᵁ biregularLocus f, ?_, ?_⟩
  · by_contra h
    exact hyM (MMP.Mori.mem_exceptionalSet.mpr h)
  · rw [← morphismRestrict_ι]
    infer_instance

/-- A relative 1-cycle pushes forward to zero. -/
private theorem pushforward_eq_zero_of_mem_relativeOneCycles {X S : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} [IsSeparated sS] (π : X ⟶ S)
    (hπ : π ≫ sS = sX) {Z : OneCycle ℝ sX} (hZ : Z ∈ relativeOneCycles sX π) :
    OneCycle.pushforward ℝ sX sS π Z = 0 := by
  rw [relativeOneCycles, Finsupp.mem_supported] at hZ
  rw [OneCycle.pushforward, Finsupp.linearCombination_apply]
  refine Finset.sum_eq_zero fun C hC => ?_
  have := ProperCurve.pushforward_cycle_eq_zero_of_isContractedBy ℝ π hπ C (hZ hC)
  rw [OneCycle.pushforward_cycle] at this
  simp only [this, smul_zero]

/-- **Curves with relative classes are contracted.** Over a projective base `S`, a curve of `X`
numerically equivalent to a relative 1-cycle is contracted to a point: otherwise an ample divisor
of `S` would have positive degree on its push-forward. -/
private theorem isContractedBy_of_numericalClass_eq {X S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sS : S ⟶ Spec (.of ℂ)} (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (π : X ⟶ S)
    (hπ : π ≫ sS = sX) (C : ProperCurve sX) {Z : OneCycle ℝ sX}
    (hZ : Z ∈ relativeOneCycles sX π)
    (hCZ : OneCycle.numericalClass sX (C.cycle ℝ) = OneCycle.numericalClass sX Z) :
    C.IsContractedBy π := by
  haveI : IsSeparated sS := hS.toIsVariety.toIsSeparated
  haveI : LocallyOfFiniteType sS := hS.toIsVariety.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sS := hS
  by_contra hnc
  obtain ⟨H, hH⟩ := MMP.Mori.IsProjectiveVariety.exists_isAmple_cartierDivisorSheaf (sX := sS)
  have hpos := MMP.Threefold.Mori.degreeOn_cartierSheaf_pos_of_isAmple hS.toIsVariety H hH
    ⟨π C.point, Oai4C1.isProperCurve_map π hπ C hnc⟩
  have heq := (OneCycle.numericalClass_eq_iff.mp hCZ)
    ((Scheme.Modules.pullback π).obj (MMP.CartierDivisor.sheaf H))
  rw [← OneCycle.degree_pushforward π hπ, ← OneCycle.degree_pushforward π hπ,
    pushforward_eq_zero_of_mem_relativeOneCycles π hπ hZ, map_zero, OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos (Oai4C1.isProperCurve_map π hπ C hnc)] at heq
  have hd := residueFieldDegree_pos_ph π hπ C hnc
  have : OneCycle.degree ℝ sS (MMP.CartierDivisor.sheaf H)
      (Finsupp.single ⟨π C.point, Oai4C1.isProperCurve_map π hπ C hnc⟩
        (residueFieldDegree π C.point : ℝ)) =
      (residueFieldDegree π C.point : ℝ) *
        (degreeOn ℂ sS (ProperCurve.ι ⟨π C.point, Oai4C1.isProperCurve_map π hπ C hnc⟩)
          (ProperCurve.dim_le _) (MMP.CartierDivisor.sheaf H) : ℝ) := by
    rw [OneCycle.degree, Finsupp.linearCombination_single, smul_eq_mul]
    rfl
  rw [this] at heq
  have : (0 : ℝ) < (residueFieldDegree π C.point : ℝ) *
      (degreeOn ℂ sS (ProperCurve.ι ⟨π C.point, Oai4C1.isProperCurve_map π hπ C hnc⟩)
        (ProperCurve.dim_le _) (MMP.CartierDivisor.sheaf H) : ℝ) :=
    mul_pos (by exact_mod_cast hd) (by exact_mod_cast hpos)
  linarith

/-- **The relative contraction of a ray is the absolute contraction of its image.** -/
private theorem isContractionOfFace_image_relativeToAbsolute {X S Zs : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hZp : MMP.Mori.IsProjectiveVariety ℂ sZs) {π : X ⟶ S} (hπ : π ≫ sS = sX)
    {R : Set (RelativeNumericalCurveClasses sX π)}
    (hR : IsExtremalRay ℝ (relativeClosedConeOfCurves sX π :
      Set (RelativeNumericalCurveClasses sX π)) R)
    {f : X ⟶ Zs} {g : Zs ⟶ S} (hcont : IsRelativeContractionOfFace π R f g)
    (hfs : f ≫ sZs = sX) :
    IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
        (relativeToAbsolute sX π '' R) ∧
      IsContractionOfFace ℂ sX sZs (relativeToAbsolute sX π '' R) f := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sS := hS
  have hray := isExtremalRay_image_relativeToAbsolute sX sS π hπ hR
  have hinj : Function.Injective (relativeToAbsolute sX π) :=
    (MMP.Mori.existsUnique_isNaturalRelativeMap_and_injective sX π).2 _
      (isNaturalRelativeMap_relativeToAbsolute sX π)
  refine ⟨hray, hX, hZp, hfs, hray.1, fun C => ⟨fun hC => ?_, fun hC => ?_⟩, hcont.isIso_app⟩
  · have hCπ : C.IsContractedBy π := fun z hz => by
      rw [← hcont.comp_eq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC z hz]
    exact ⟨C.relativeClass π hCπ, (hcont.isContractedBy_iff C hCπ).mp hC, rfl⟩
  · obtain ⟨r, hr, hrC⟩ := hC
    obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX π r
    have hCπ : C.IsContractedBy π :=
      isContractedBy_of_numericalClass_eq hS π hπ C Z.2 hrC.symm
    refine (hcont.isContractedBy_iff C hCπ).mpr ?_
    have : C.relativeClass π hCπ = relativeNumericalClass sX π Z :=
      hinj (hrC.symm ▸ rfl)
    rw [this]; exact hr

/-- **Trichotomy for the relative contraction of an extremal ray** of a `ℚ`-factorial projective
variety over a projective base: it is of fibre type, divisorial, or small. -/
private theorem trichotomy_of_isRelativeContractionOfFace {X S Zs : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXQ : IsQFactorial sX)
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hZp : MMP.Mori.IsProjectiveVariety ℂ sZs) {π : X ⟶ S} (hπ : π ≫ sS = sX)
    {R : Set (RelativeNumericalCurveClasses sX π)}
    (hR : IsExtremalRay ℝ (relativeClosedConeOfCurves sX π :
      Set (RelativeNumericalCurveClasses sX π)) R)
    {f : X ⟶ Zs} {g : Zs ⟶ S} (hcont : IsRelativeContractionOfFace π R f g)
    (hfs : f ≫ sZs = sX) (hZv : IsNormalVariety ℂ sZs) :
    topologicalKrullDim Zs < topologicalKrullDim X ∨
      (IsBirationalMorphism f ∧ ∃ E : MMP.Mori.PrimeDivisor X,
        (MMP.Mori.exceptionalSet f : Set X) = E.support) ∨
      MMP.Flips.IsSmall ℂ sZs sX f := by
  obtain ⟨hray, hcf⟩ :=
    isContractionOfFace_image_relativeToAbsolute hX hS hZp hπ hR hcont hfs
  rcases (IsContractionOfFace.trichotomy_of_isExtremalRay hXQ hray hcf).1 with h | h | h
  · exact Or.inl h.dim_lt
  · exact Or.inr (Or.inl ⟨h.isBirationalMorphism, h.exists_primeDivisor⟩)
  · refine Or.inr (Or.inr ?_)
    haveI : IsNormal Zs := hZv.2
    have hb := h.isBirationalMorphism
    haveI : IsProper (f ≫ sZs) := by
      rw [hfs]; exact isProper_of_isProjectiveMorphism sX hX.isProjective
    haveI : IsSeparated sZs := hZv.1.toIsSeparated
    have hfp : IsProper f := IsProper.of_comp f sZs
    have hbc : MMP.Flips.IsBirationalContraction ℂ sZs sX f :=
      { isVariety_target := hZv.1
        isVariety_source := hX.toIsVariety
        comp_eq := hfs
        isProper := hfp
        isIso_app := hcf.isIso_app
        dim_eq := (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (sX := sZs)
          (sX' := sX) (haveI := hZv.1; haveI := hX.toIsVariety; hb)).symm }
    refine (MMP.Flips.isSmall_iff_two_le_closedsCodimension_exceptionalSet hbc).mpr ?_
    refine MMP.Flips.le_closedsCodimension_iff_le_coheight.mpr fun x hx => ?_
    exact MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h.two_le_codimension x
      (exceptionalSet_subset_ph f hx)

/-- The boundary of a real canonical pair is effective. -/
private theorem nonneg_of_isRealCanonicalPair {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : RDivisor X}
    (h : IsRealCanonicalPair sX B) : 0 ≤ B := by
  intro P
  by_cases hP : B.coeff P = 0
  · exact le_of_eq (by simpa [DivisorWithCoeffs.coeff_apply] using hP.symm)
  · exact le_of_lt (by simpa [DivisorWithCoeffs.coeff_apply] using (h.2.1 P hP).1)

/-- **A real terminal pair is real klt**: exceptional divisors have log discrepancy greater than
one, and a prime divisor `Q` has log discrepancy `1 - coeff_Q B > 0`. -/
private theorem isRealKltPair_of_isRealTerminalPair {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    {B : RDivisor X} (hT : IsRealTerminalPair sX B) : IsRealKltPair sX B := by
  obtain ⟨⟨hXv, hcoef, ⟨n₀, K₀, hK₀, hRC⟩, -⟩, hterm⟩ := hT
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  refine ⟨hXv, fun P => ?_, ⟨n₀, K₀, hK₀, hRC⟩, fun n E a ha => ?_⟩
  · by_cases h : B.coeff P = 0
    · rw [h]; norm_num
    · exact (hcoef P h).2
  · by_cases hE : E.IsExceptional
    · exact lt_trans one_pos (hterm n E a hE ha)
    · obtain ⟨Q, hQ⟩ := exists_valuation_eq_of_not_isExceptional hXv hE
      obtain ⟨ω, hω0, hω'⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXv hK₀
      have hω : divisorOfForm ω = K₀ := DivisorWithCoeffs.ext' hω'
      have hKB : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B) := by
        rw [hω]
        refine isCartierCombination_of_isRCartier ?_
        have hmr :
            Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K₀ = Divisor.toRDivisor K₀ := by
          ext Γ
          simp [Divisor.toRDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom]
        rw [hmr] at hRC
        exact hRC
      have haQ := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha
        (isLogDiscrepancy_ofPrimeDivisor_ph hXv hω0 (hω ▸ hK₀) hKB Q) hQ
      have hlt : B.coeff Q < 1 := by
        by_cases h : B.coeff Q = 0
        · rw [h]; norm_num
        · exact (hcoef Q h).2
      linarith

/-- The target of a contraction over `S` lies over `S` compatibly with the structure maps. -/
private theorem comp_eq_of_isRelativeContractionOfFace {X Zs : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)} {πX : X ⟶ S}
    {R : Set (RelativeNumericalCurveClasses sX πX)} {f : X ⟶ Zs} {g : Zs ⟶ S} {L : RDivisor X}
    (hcont : IsRelativeContractionOfFace πX R f g)
    (hneg : IsNegativeExtremalContraction ℂ sX sZs L f) (hπ : πX ≫ sS = sX) :
    g ≫ sS = sZs := by
  have hc := hneg.isContraction
  have h1 : f ≫ g ≫ sS = f ≫ sZs := by
    rw [← Category.assoc, hcont.comp_eq, hπ, hc.comp_eq]
  have : IsIso f.appTop := hc.isIso_app ⊤
  refine ext_of_isAffine ?_
  have h2 := congrArg Scheme.Hom.appTop h1
  simp only [Scheme.Hom.comp_appTop] at h2
  exact (cancel_mono (f.appTop)).mp h2

/-- The partial map underlying a partial isomorphism is dominant. -/
private theorem isDominant_toPartialMap_hom {X Y : Scheme.{0}} (e : X.PartialIso Y) :
    IsDominant e.toPartialMap.hom := by
  change IsDominant (e.iso.hom ≫ e.target.ι)
  haveI : IsDominant e.target.ι := Opens.isDominant_ι e.dense_target
  infer_instance

/-- The partial map given by the inclusion of a dense open `U`, composed with `q`, represents
`q`. -/
private theorem toRationalMap_ι_comp {X Z : Scheme.{0}} {U : X.Opens} (hU : Dense (U : Set X))
    (q : X ⟶ Z) :
    (⟨U, hU, U.ι ≫ q⟩ : X.PartialMap Z).toRationalMap = q.toRationalMap := by
  change _ = q.toPartialMap.toRationalMap
  rw [← Scheme.PartialMap.restrict_toRationalMap q.toPartialMap U hU le_top]
  congr 1
  refine Scheme.PartialMap.ext _ _ rfl ?_
  change U.ι ≫ q = (X.isoOfEq rfl).hom ≫ (X.homOfLE (le_top : U ≤ ⊤) ≫ X.topIso.hom ≫ q)
  simp [Scheme.topIso_hom]

/-- **A representative of a composite.** If `f` maps a dense open `O ⊆ dom f` into `dom g`
through `β`, then `g ∘ f` is represented on `O` by `β` followed by `g`. -/
private theorem comp_toRationalMap_eq {X Y Z : Scheme.{0}} [IsIntegral X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) {O : X.Opens}
    (hO : Dense (O : Set X)) (hOf : O ≤ f.domain) (β : O.toScheme ⟶ g.domain.toScheme)
    (hβ : β ≫ g.domain.ι = X.homOfLE hOf ≫ f.hom) :
    f.toRationalMap.comp g.toRationalMap = (⟨O, hO, β ≫ g.hom⟩ : X.PartialMap Z).toRationalMap := by
  rw [Scheme.RationalMap.toRationalMap_comp, Scheme.PartialMap.toRationalMap_eq_iff]
  have hOc : O ≤ f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain := by
    intro x hx
    let y : O.toScheme := ⟨x, hx⟩
    have h1 : f.hom (X.homOfLE hOf y) = g.domain.ι (β y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hβ]
    refine ⟨X.homOfLE hOf y, ?_, ?_⟩
    · show f.hom (X.homOfLE hOf y) ∈ g.domain
      rw [h1]; exact (β y).2
    · show f.domain.ι (X.homOfLE hOf y) = x
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]; rfl
  have key2 : X.homOfLE hOc ≫ (Scheme.Hom.isoImage f.domain.ι (f.hom ⁻¹ᵁ g.domain)).inv ≫
      (f.hom ⁻¹ᵁ g.domain).ι = X.homOfLE hOf := by
    rw [← cancel_mono f.domain.ι]
    simp only [Category.assoc]
    rw [← Scheme.Hom.isoImage_hom_ι, Iso.inv_hom_id_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι]
  have key : X.homOfLE hOc ≫ (Scheme.Hom.isoImage f.domain.ι (f.hom ⁻¹ᵁ g.domain)).inv ≫
      f.hom ∣_ g.domain = β := by
    rw [← cancel_mono g.domain.ι, hβ, ← key2]
    simp only [Category.assoc, morphismRestrict_ι]
  refine ⟨O, hO, hOc, le_rfl, ?_⟩
  simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.comp_hom, Scheme.homOfLE_rfl,
    Category.id_comp]
  rw [← key]
  rfl

private theorem isDominant_of_isBirational_ph {X Y : Scheme.{0}} {φ : X.RationalMap Y}
    (hφ : MMP.Mori.RationalMap.IsBirational φ) : φ.IsDominant := by
  obtain ⟨e, rfl⟩ := hφ
  have := isDominant_toPartialMap_hom e
  infer_instance

private theorem comp_eq_id_of_isInverse_ph {X Y : Scheme.{0}} [IsIntegral X] [Nonempty Y]
    {f : X.RationalMap Y} [f.IsDominant] {h : Y.RationalMap X}
    (H : MMP.Mori.RationalMap.IsInverse f h) : f.comp h = Scheme.RationalMap.id X := by
  obtain ⟨e, rfl, rfl⟩ := H
  have := isDominant_toPartialMap_hom e
  rw [comp_toRationalMap_eq e.toPartialMap e.symm.toPartialMap (O := e.source) e.dense_source le_rfl
    e.iso.hom (by
      change e.iso.hom ≫ e.target.ι = X.homOfLE le_rfl ≫ e.iso.hom ≫ e.target.ι
      rw [Scheme.homOfLE_rfl, Category.id_comp])]
  have : (⟨e.source, e.dense_source, e.iso.hom ≫ e.symm.toPartialMap.hom⟩ : X.PartialMap X) =
      ⟨e.source, e.dense_source, e.source.ι ≫ 𝟙 X⟩ := by
    congr 1
    change e.iso.hom ≫ e.iso.inv ≫ e.source.ι = _
    simp
  exact (congrArg Scheme.PartialMap.toRationalMap this).trans (toRationalMap_ι_comp _ (𝟙 X))

private theorem not_isExceptional_of_transformPrimeDivisor_eq_some_ph {X Y : Scheme.{0}}
    [IsReduced X] [IsSeparated (Y ↘ CategoryTheory.Limits.terminal Scheme)]
    {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (h : RationalMap.transformPrimeDivisor φ P = some Q) :
    ¬ MMP.Mori.RationalMap.IsExceptional φ P := by
  rw [MMP.Mori.RationalMap.isExceptional_iff]
  intro hex
  have h2 := hex (MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight,
    ← MMP.Mori.RationalMap.support_transformPrimeDivisor h] at h2
  have h3 := h2 Q.genericPoint (by
    change Q.genericPoint ∈ Q.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl)
  rw [Q.coheight_genericPoint] at h3
  exact absurd h3 (by decide)

private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq_ph {X Y : Scheme.{0}}
    [IsReduced X] [IsSeparated (Y ↘ CategoryTheory.Limits.terminal Scheme)]
    {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    RationalMap.transformPrimeDivisor φ P = some E :=
  MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP hE

/-- A prime divisor whose generic point lies in the exceptional set of a proper birational
morphism onto a normal scheme is exceptional: over points of coheight at most one the morphism is
an isomorphism. -/
private theorem isExceptional_of_genericPoint_mem_exceptionalSet {X Zs : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Zs]
    [IsLocallyNoetherian Zs] [IsNormal Zs]
    [IsSeparated (Zs ↘ CategoryTheory.Limits.terminal Scheme)] (f : X ⟶ Zs) [IsProper f]
    (hb : IsBirationalMorphism f) (G : MMP.Mori.PrimeDivisor X)
    (hG : G.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set X)) :
    MMP.Mori.RationalMap.IsExceptional f.toRationalMap G := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight]
  intro z hz
  have hz' : z ∈ f '' (G.idealSheaf.support : Set X) := by
    have hcl := f.isClosedMap _ G.idealSheaf.support.isClosed
    change z ∈ closure (f '' (G.idealSheaf.support : Set X)) at hz
    rwa [hcl.closure_eq] at hz
  obtain ⟨y, hyG, rfl⟩ := hz'
  by_contra hlt
  have hle : Order.coheight (f y) ≤ 1 :=
    Order.le_of_lt_add_one (by simpa [one_add_one_eq_two] using not_le.mp hlt)
  have hbr := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f hb hle
  have hyEx : y ∈ (MMP.Mori.exceptionalSet f : Set X) := by
    have hsub : closure ({G.genericPoint} : Set X) ⊆ (MMP.Mori.exceptionalSet f : Set X) :=
      (MMP.Mori.isClosed_exceptionalSet f).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hG)
    refine hsub ?_
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hyG
  exact (MMP.Mori.mem_exceptionalSet.mp hyEx) hbr

/-- For a divisorial contraction the two notions of exceptional set agree. -/
private theorem flips_exceptionalSet_eq_of_mori {X Zs : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Zs] [IsLocallyNoetherian Zs] [IsNormal Zs]
    (f : X ⟶ Zs) [IsProper f] (hb : IsBirationalMorphism f) {E : MMP.Mori.PrimeDivisor X}
    (hE : (MMP.Mori.exceptionalSet f : Set X) = E.support) :
    MMP.Flips.exceptionalSet f = E.support := by
  refine le_antisymm ((exceptionalSet_subset_ph f).trans hE.le) ?_
  have hη : E.genericPoint ∈ MMP.Flips.exceptionalSet f := by
    by_contra h
    have hco := MMP.Flips.coheight_map_of_notMem_exceptionalSet h
    rw [E.coheight_genericPoint] at hco
    have hbr := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f hb hco.le
    have hmem : E.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set X) := by
      rw [hE, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    exact (MMP.Mori.mem_exceptionalSet.mp hmem) hbr
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact (MMP.Flips.isClosed_exceptionalSet f).closure_subset_iff.mpr
    (Set.singleton_subset_iff.mpr hη)

/-- The exceptional set of a small contraction consists of points of coheight at least two. -/
private theorem two_le_coheight_of_mem_exceptionalSet_of_isSmall {X Zs : Scheme.{0}}
    [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)} {f : X ⟶ Zs}
    (hf : MMP.Flips.IsSmall ℂ sZs sX f) {x : X}
    (hx : x ∈ (MMP.Mori.exceptionalSet f : Set X)) : 2 ≤ Order.coheight x := by
  obtain ⟨V, W, hV, -, hle, hiso⟩ := exists_closeds_isIso_of_isSmall_ph hf
  by_contra hxV
  have hxV' : x ∈ (V.compl : Set X) := fun h => hxV (hV x h)
  exact (MMP.Mori.mem_exceptionalSet.mp hx) (le_biregularLocus hiso (hle hxV'))

/-! ### Steps through an isomorphism of the target -/

/-- Composing with an isomorphism of the target does not change which curves are contracted. -/
private theorem isContractedBy_comp_iso {X Y Y' : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (f : X ⟶ Y) (u : Y ⟶ Y') [IsIso u] (C : ProperCurve sX) :
    C.IsContractedBy (f ≫ u) ↔ C.IsContractedBy f := by
  have hinj : Function.Injective u :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso u))).injective
  refine ⟨fun h x hx => hinj ?_, fun h x hx => ?_⟩
  · have := h x hx
    simpa only [Scheme.Hom.comp_apply] using this
  · simp only [Scheme.Hom.comp_apply, h x hx]

/-- The relative Picard number does not change under an isomorphism of the target. -/
private theorem relativePicardNumber_comp_iso {X Y Y' : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (sX : X ⟶ Spec (.of ℂ)) (f : X ⟶ Y) (u : Y ⟶ Y') [IsIso u] :
    MMP.Flips.relativePicardNumber sX (f ≫ u) = MMP.Flips.relativePicardNumber sX f := by
  have h : relativeNumericallyTrivialDivisors sX (f ≫ u) =
      relativeNumericallyTrivialDivisors sX f := by
    ext D
    simp only [mem_relativeNumericallyTrivialDivisors, isContractedBy_comp_iso]
  unfold MMP.Flips.relativePicardNumber MMP.Flips.RelativeNumericalDivisorClasses
  rw [h]

/-- Relative ampleness is kept under an isomorphism of the target. -/
private theorem isRelativelyAmple_comp_iso {X Y Y' : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (f : X ⟶ Y) (u : Y ⟶ Y') [IsIso u] {A : RDivisor X}
    (h : IsRelativelyAmple f A) : IsRelativelyAmple (f ≫ u) A := by
  obtain ⟨m, r, L, hm, hr, hL, rfl⟩ := h
  refine ⟨m, r, L, hm, hr, fun j => ?_, rfl⟩
  obtain ⟨hc, hA⟩ := hL j
  exact ⟨hc, fun U hU => hA (u ⁻¹ᵁ U) (hU.preimage u)⟩

/-- A negative extremal contraction followed by an isomorphism of its target is a negative
extremal contraction. -/
private theorem isNegativeExtremalContraction_comp_iso {X Y Y' : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    {sY : Y ⟶ Spec (.of ℂ)} {sY' : Y' ⟶ Spec (.of ℂ)} {L : RDivisor X} {f : X ⟶ Y}
    (h : IsNegativeExtremalContraction ℂ sX sY L f) (u : Y ⟶ Y') [IsIso u] (hu : u ≫ sY' = sY)
    (hY' : IsNormalVariety ℂ sY') :
    IsNegativeExtremalContraction ℂ sX sY' L (f ≫ u) := by
  have hc := h.isContraction
  haveI : IsProper f := hc.isProper
  refine
    { isNormalVariety_source := h.isNormalVariety_source
      isNormalVariety_target := hY'
      isCartierCombination := h.isCartierCombination
      isContraction :=
        { isVariety_target := hY'.1
          isVariety_source := hc.isVariety_source
          comp_eq := by rw [Category.assoc, hu, hc.comp_eq]
          isProper := inferInstance
          isIso_app := fun U => by
            rw [Scheme.Hom.comp_app]
            exact @IsIso.comp_isIso _ _ _ _ _ (u.app U) (f.app _) _ (hc.isIso_app _) }
      isRelativelyAntiAmple := isRelativelyAmple_comp_iso f u h.isRelativelyAntiAmple
      relativePicardNumber_eq_one := by
        rw [relativePicardNumber_comp_iso]; exact h.relativePicardNumber_eq_one }

/-- The exceptional set does not change under an isomorphism of the target. -/
private theorem flips_exceptionalSet_comp_iso {X Y Y' : Scheme.{0}} (f : X ⟶ Y) (u : Y ⟶ Y')
    [IsIso u] : MMP.Flips.exceptionalSet (f ≫ u) = MMP.Flips.exceptionalSet f := by
  ext x
  simp only [MMP.Flips.exceptionalSet, Set.mem_setOf_eq]
  refine not_congr (exists_congr fun V => and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩)
  · have : IsOpenImmersion ((V.ι ≫ f ≫ u) ≫ inv u) := inferInstance
    simpa using this
  · rw [← Category.assoc]; infer_instance

/-- Adding a principal Cartier divisor keeps relative ampleness. -/
private theorem isRelativelyAmple_add_of_linearlyEquivalent {X Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} (hXv : IsNormalVariety ℂ sX) (hZv : IsNormalVariety ℂ sZ)
    (f : X ⟶ Z) [IsProper f] (hf : f ≫ sZ = sX) {A : RDivisor X} (hA : IsRelativelyAmple f A)
    {N : Divisor X} (hNc : N.IsCartier) (hN : N.LinearlyEquivalent 0) :
    IsRelativelyAmple f (A + Divisor.toRDivisor N) := by
  haveI : QuasiCompact sX := hXv.1.toQuasiCompact
  haveI : IsNormal Z := hZv.2
  haveI : LocallyOfFiniteType sZ := hZv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hbasics := MMP.Flips.relativelyAmple_basics sX sZ hXv hZv f hf
  obtain ⟨m, r, L, hm, hr, hLa, hAeq⟩ := hA
  have hproj : IsProjective f := hbasics.2.2.2.1 ⟨L ⟨0, hm⟩, hLa ⟨0, hm⟩⟩
  have hAc : IsCartierCombination A :=
    ⟨m, r, L, fun j => (hLa j).1, by
      simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using hAeq⟩
  exact hbasics.2.2.2.2.2 hproj _ _
    (isNumericallyEquivalentOver_add_of_linearlyEquivalent f hAc hNc hN)
    ⟨m, r, L, hm, hr, hLa, hAeq⟩

/-! ### Representatives of rational maps -/

/-- The value of a composite of partial maps at a point. -/
private theorem comp_hom_apply {X Y Z : Scheme.{0}} [PreirreducibleSpace X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) {x : X} (hx : x ∈ f.domain)
    (hfx : f.hom ⟨x, hx⟩ ∈ g.domain) :
    ∃ h : x ∈ (f.comp g).domain, (f.comp g).hom ⟨x, h⟩ = g.hom ⟨f.hom ⟨x, hx⟩, hfx⟩ := by
  have hD : f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain ≤ f.domain := by
    rintro _ ⟨y, -, rfl⟩; exact y.2
  have key : (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫ (f.hom ⁻¹ᵁ g.domain).ι =
      X.homOfLE hD := by
    rw [← cancel_mono f.domain.ι, Category.assoc, Scheme.Hom.isoImage_inv_ι, Scheme.homOfLE_ι]
  have hmem : x ∈ f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain := ⟨⟨x, hx⟩, hfx, rfl⟩
  refine ⟨hmem, ?_⟩
  have hw : (f.hom ⁻¹ᵁ g.domain).ι ((f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ⟨x, hmem⟩) =
      ⟨x, hx⟩ := by
    have h1 := congrArg (fun φ => φ ⟨x, hmem⟩) key
    exact ((Scheme.Hom.comp_apply _ _ _).symm.trans h1).trans (Scheme.homOfLE_apply' hD x hmem)
  have hr : (f.hom ∣_ g.domain) ((f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ⟨x, hmem⟩) =
      ⟨f.hom ⟨x, hx⟩, hfx⟩ := by
    apply Subtype.ext
    have h2 := congrArg (fun φ => φ ((f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ⟨x, hmem⟩))
      (morphismRestrict_ι f.hom g.domain)
    simp only [Scheme.Hom.comp_apply] at h2
    change g.domain.ι ((f.hom ∣_ g.domain)
      ((f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ⟨x, hmem⟩)) = f.hom ⟨x, hx⟩
    rw [h2, hw]
  show ((f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫ f.hom ∣_ g.domain ≫ g.hom)
    (⟨x, hmem⟩ : (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain).toScheme) = _
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  exact congrArg g.hom hr

/-- Two morphisms on a dense open representing the same rational map to a separated scheme are
equal. -/
private theorem hom_eq_of_toRationalMap_eq {X Y : Scheme.{0}} [IsReduced X]
    [IsSeparated (Y ↘ CategoryTheory.Limits.terminal Scheme)] {U : X.Opens} (hU : Dense (U : Set X))
    {f g : U.toScheme ⟶ Y}
    (h : (⟨U, hU, f⟩ : X.PartialMap Y).toRationalMap =
      (⟨U, hU, g⟩ : X.PartialMap Y).toRationalMap) :
    f = g := by
  have := (Scheme.PartialMap.equiv_iff_of_domain_eq_of_isSeparated
    (S := CategoryTheory.Limits.terminal Scheme)
    (f := ⟨U, hU, f⟩) (g := ⟨U, hU, g⟩) rfl).mp (Scheme.PartialMap.toRationalMap_eq_iff.mp h)
  injection this

/-- The restriction of a partial map `g` to a dense open `U`, composed with `q`, represents
`g ∘ q`. -/
private theorem toRationalMap_restrict_comp {X Y Z : Scheme.{0}} (g : X.PartialMap Y)
    {U : X.Opens} (hU : Dense (U : Set X)) (hle : U ≤ g.domain) (q : Y ⟶ Z) :
    (⟨U, hU, (X.homOfLE hle ≫ g.hom) ≫ q⟩ : X.PartialMap Z).toRationalMap =
      g.toRationalMap.compHom q := by
  rw [← Scheme.PartialMap.restrict_toRationalMap g U hU hle,
    ← Scheme.RationalMap.compHom_toRationalMap]
  rfl

/-- Composing partial maps commutes with composing with a morphism. -/
private theorem comp_compHom {X Y Z T : Scheme.{0}} [PreirreducibleSpace X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) (q : Z ⟶ T) :
    (f.comp g).compHom q = f.comp (g.compHom q) := by
  show (⟨f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain, (f.comp g).dense_domain,
      ((f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫ f.hom ∣_ g.domain ≫ g.hom) ≫ q⟩ :
        X.PartialMap T) =
    ⟨f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain, (f.comp g).dense_domain,
      (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫ f.hom ∣_ g.domain ≫ g.hom ≫ q⟩
  simp only [Category.assoc]

/-- If `h` is an inverse of the morphism `p`, then `p ∘ h` is the identity. -/
private theorem compHom_eq_of_isInverse {X Y : Scheme.{0}} [IsReduced X] [IsReduced Y]
    [IsSeparated (X ↘ CategoryTheory.Limits.terminal Scheme)] {p : Y ⟶ X} {h : X.RationalMap Y}
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) :
    h.compHom p = Scheme.Hom.toRationalMap (𝟙 X) := by
  obtain ⟨e, he1, he2⟩ := id hinv
  rw [← he2, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff,
    Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated
      (S := CategoryTheory.Limits.terminal Scheme)]
  change e.iso.inv ≫ e.source.ι ≫ p = e.target.ι ≫ 𝟙 X
  rw [source_ι_comp_eq_of_toRationalMap_eq p e he1, Iso.inv_hom_id_assoc, Category.comp_id]

/-- Transforms of divisors compose: `ψ_* χ_* D` is the transform along the composite of the maps
of prime divisors. -/
private theorem mapPrimeDivisors_mapPrimeDivisors {X Y T : Scheme.{0}} {R : Type*}
    [AddCommMonoid R] (χ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y))
    (ψ : MMP.Mori.PrimeDivisor Y → Option (MMP.Mori.PrimeDivisor T))
    (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors ψ (DivisorWithCoeffs.mapPrimeDivisors χ D) =
      DivisorWithCoeffs.mapPrimeDivisors (fun G => (χ G).bind ψ) D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, map_add, map_add, hD, hD']
  | single G r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases χ G with _ | D'
    · simp
    · simp [DivisorWithCoeffs.mapPrimeDivisors_single]

/-! ### Points of coheight at most one -/

/-- The local ring of a normal locally noetherian integral scheme at a point of coheight at most
one is a valuation ring. -/
private theorem valuationRing_stalk_of_coheight_le_one {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {x : X} (hx : Order.coheight x ≤ 1) :
    ValuationRing (X.presheaf.stalk x) := by
  rcases lt_or_eq_of_le hx with h | h
  · have hmax : IsMax x := Order.coheight_eq_zero.mp (Order.lt_one_iff.mp h)
    have hgen : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
    have hx' : x ⤳ genericPoint X := hmax (show x ≤ genericPoint X from hgen)
    have hgx : genericPoint X = x := (hgen.antisymm hx').eq
    subst hgx
    have : IsField (X.presheaf.stalk (genericPoint X)) := Field.toIsField X.functionField
    letI := this.toField
    infer_instance
  · have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
      rw [ringKrullDim_stalk_eq_coheight, h]; rfl
    have h5 : IsNoetherianRing (X.presheaf.stalk x) ∧ IsLocalRing (X.presheaf.stalk x) ∧
        IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) ∧
        ringKrullDim (X.presheaf.stalk x) = 1 :=
      ⟨inferInstance, inferInstance, inferInstance, IsNormal.stalk_normal x, hdim⟩
    have h1 : ∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing (X.presheaf.stalk x) :=
      ((isDiscreteValuationRing_tfae (X.presheaf.stalk x)).out 5 1).mp h5
    have := h1.choose_spec
    infer_instance

/-- A separated dominant morphism of normal integral schemes inducing an isomorphism of function
fields is injective over points of coheight at most one. -/
private theorem eq_of_apply_eq_of_coheight_le_one {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsSeparated f]
    [IsDominant f] (hf : Function.Bijective (functionFieldMap f)) {x₁ x₂ : X}
    (h : f x₂ = f x₁) (hx : Order.coheight (f x₁) ≤ 1) : x₁ = x₂ := by
  have := valuationRing_stalk_of_coheight_le_one hx
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x₁
  have : ValuationRing (Y.presheaf.stalk (f x₂)) := by rw [h]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x₂
  exact MMP.Positivity.eq_of_isIso_stalkMap f hf h

/-- **Cancelling a local isomorphism at a codimension-one point.** -/
private theorem isIso_stalkMap_of_isIso_comp {X Y Z : Scheme.{0}} [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant g]
    (hg : Function.Bijective (functionFieldMap g)) (x : X) [h : IsIso ((f ≫ g).stalkMap x)]
    (hx : Order.coheight (g (f x)) ≤ 1) : IsIso (f.stalkMap x) := by
  have := valuationRing_stalk_of_coheight_le_one hx
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing g hg (f x)
  rw [Scheme.Hom.stalkMap_comp] at h
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ (g.stalkMap (f x)) (f.stalkMap x) this h

/-- If `a ≫ p` is dominant, with `p` a separated dominant morphism of integral schemes inducing
an isomorphism of function fields onto a normal scheme, then `a` is dominant. -/
private theorem isDominant_of_comp_eq {V W T : Scheme.{0}} [IsIntegral V] [IsIntegral W]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] (a : V ⟶ W) (p : W ⟶ T) [IsSeparated p]
    [IsDominant p] (hp : Function.Bijective (functionFieldMap p)) [IsDominant (a ≫ p)] :
    IsDominant a := by
  have h1 : p (a (genericPoint V)) = genericPoint T := by
    rw [← Scheme.Hom.comp_apply]; exact MMP.Positivity.map_genericPoint_eq_of_isDominant (a ≫ p)
  have h2 : p (genericPoint W) = genericPoint T :=
    MMP.Positivity.map_genericPoint_eq_of_isDominant p
  have h0 : Order.coheight (genericPoint T) ≤ 1 := by
    have : IsMax (genericPoint T) := fun y _ =>
      (genericPoint_spec T).specializes (Set.mem_univ y)
    rw [Order.coheight_eq_zero.mpr this]
    exact zero_le_one
  have h3 : genericPoint W = a (genericPoint V) :=
    eq_of_apply_eq_of_coheight_le_one p hp (h1.trans h2.symm) (by rw [h2]; exact h0)
  rw [isDominant_iff]
  intro w
  have hw : w ∈ closure ({genericPoint W} : Set W) := by
    rw [(genericPoint_spec W).def]; trivial
  rw [h3] at hw
  have hmem : a (genericPoint V) ∈ Set.range (a : V → W) := ⟨genericPoint V, rfl⟩
  exact closure_mono (Set.singleton_subset_iff.mpr hmem) hw

/-! ### Coefficients of pull-backs -/

private theorem mem_irreducibleComponent' {T : Type*} [TopologicalSpace T] [IrreducibleSpace T]
    (W : irreducibleComponents T) (t : T) : t ∈ W.1 := by
  rw [W.2.eq_of_le (IrreducibleSpace.isIrreducible_univ T) (Set.subset_univ _)]
  trivial

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = (g ≫ f)^*L`. -/
private theorem isPullback_comp {X Y Z : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral X] [IsLocallyNoetherian Z] [IsNormal Z]
    {f : Y ⟶ X} {g : Z ⟶ Y} {L : Divisor X} {L' : Divisor Y}
    {L'' : Divisor Z} {hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ L.supp}
    {hB' : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉ L'.supp}
    (h : L.IsPullback f hB L') (h' : L'.IsPullback g hB' L'')
    (hB'' : ∀ W : irreducibleComponents Z, (g ≫ f) (componentGenericPoint Z W) ∉ L.supp) :
    L.IsPullback (g ≫ f) hB'' L'' := by
  intro U φ hφ E hE
  have hψ := h.isLocalEquation hφ
  rw [h' (f ⁻¹ᵁ U) _ hψ E hE]
  congr 1
  set z := componentGenericPoint Z E.component
  have hzU : f (g z) ∈ U := E.map_componentGenericPoint_mem (g ≫ f) hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _) (mem_irreducibleComponent'
    (pointComponent ((g ≫ f) z)) _)
  rw [pullbackComponent_eq hB'' hφ hzU _ a ha]
  set W := pointComponent (g z)
  have hspec : componentGenericPoint Y W ⤳ g z :=
    (isGenericPoint_componentGenericPoint Y W).specializes (mem_pointComponent _)
  have hWU : f (componentGenericPoint Y W) ∈ U :=
    (f.base.hom.map_specializes hspec).mem_open U.isOpen hzU
  have hb : (stalkToRationalFunctions Y (mem_pointComponent (g z))).hom
      (Units.map (f.stalkMap (g z)).hom.toMonoidHom a) =
      ((pullbackLocalEquation f hB hφ : (RationalFunctions Y)ˣ) : RationalFunctions Y) W := by
    have e1 := congrArg Units.val (pullbackLocalEquation_apply f hB hφ W hWU)
    refine Eq.trans ?_ e1.symm
    rw [pullbackComponent_eq hB hφ hWU
      (mem_irreducibleComponent' (pointComponent ((g ≫ f) z)) _)
      (Units.map (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom.toMonoidHom a)
      ?_]
    · change (stalkToRationalFunctions Y _).hom ((f.stalkMap (g z)).hom a.val) =
        (f.stalkMap _).hom ((X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom
          a.val)
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, stalkToRationalFunctions,
        Scheme.Hom.stalkSpecializes_stalkMap]
    · change (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec) ≫
        X.presheaf.stalkSpecializes _).hom a.val = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      exact ha
  rw [pullbackComponent_eq hB' hψ _ (mem_pointComponent (g z)) _ hb]
  ext
  change _ = ((g ≫ f).stalkMap z).hom a.val
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- **Pulling a pull-back back once more.** Let `g^*M = D` be an `ℝ`-Cartier pull-back and
`f : V ⟶ W` dominant from a quasi-compact normal integral scheme. Then `M` has a pull-back `G`
along `f ≫ g` whose coefficient along a prime divisor `E` of `V` dominating a prime divisor `P` of
`W` with an isomorphism of local rings is the coefficient of `D` along `P`. -/
private theorem exists_isRCartierPullback_comp {V W Z : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] (f : V ⟶ W) [IsDominant f]
    (g : W ⟶ Z) [IsDominant g] {M : RDivisor Z} {D : RDivisor W}
    (hD : MMP.Flips.IsRCartierPullback g M D) :
    ∃ G : RDivisor V, MMP.Flips.IsRCartierPullback (f ≫ g) M G ∧
      ∀ (E : MMP.Mori.PrimeDivisor V) (P : MMP.Mori.PrimeDivisor W),
        f E.genericPoint = P.genericPoint → IsIso (f.stalkMap E.genericPoint) →
          G.coeff E = D.coeff P := by
  obtain ⟨m, r, L, L', hLc, hM, hpb, rfl⟩ := hD
  have hL'c : ∀ j, (L' j).IsCartier := fun j => ((hpb j).2).isCartier (hLc j)
  let L'' : Fin m → Divisor V := fun j =>
    (L' j).pullback (hL'c j) (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _)
  have hL'' : ∀ j, (L' j).IsPullback f
      (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _) (L'' j) :=
    fun j => Divisor.isPullback_pullback (hL'c j) _
  refine ⟨∑ j, r j • Divisor.toRDivisor (L'' j), ⟨m, r, L, L'', hLc, hM, fun j =>
    ⟨MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant (f ≫ g) _,
      isPullback_comp (hpb j).2 (hL'' j) _⟩, rfl⟩, fun E P heq hiso => ?_⟩
  rw [MMP.Flips.coeff_sum_smul_toRDivisor, MMP.Flips.coeff_sum_smul_toRDivisor]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact_mod_cast MMP.Positivity.coeff_eq_of_isPullback E P heq (hL'c j) (hL'' j)

/-- The coefficient of a pull-back along a birational morphism at a prime divisor over a prime
divisor `G` is the coefficient of `G`. -/
private theorem coeff_isRCartierPullback_eq {W X : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (p : W ⟶ X) [IsDominant p] (hp : Function.Bijective (functionFieldMap p)) {D : RDivisor X}
    {GY : RDivisor W} (hGY : MMP.Flips.IsRCartierPullback p D GY) (P : MMP.Mori.PrimeDivisor W)
    (G : MMP.Mori.PrimeDivisor X) (hPG : p P.genericPoint = G.genericPoint) :
    GY.coeff P = D.coeff G := by
  obtain ⟨m, r, L, L', hLc, hD, hpb, rfl⟩ := hGY
  have := MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing G
  have : ValuationRing (X.presheaf.stalk (p P.genericPoint)) := by rw [hPG]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing p hp P.genericPoint
  rw [hD, MMP.Flips.coeff_sum_smul_toRDivisor, MMP.Flips.coeff_sum_smul_toRDivisor]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact_mod_cast MMP.Positivity.coeff_eq_of_isPullback P G hPG (hLc j) (hpb j).2

/-- **Comparison of pull-backs across a partial isomorphism.** Let `e : X ⊇ U ≅ U' ⊆ X'` be a
partial isomorphism, `φ : X ⤏ Z` and `φ' : X' ⤏ Z` with `φ = φ' ∘ e`, and let `(W, p, q)`,
`(W', p', q')` be models of `φ` and `φ'` (`p`, `p'` proper birational with inverses `h`, `h'`,
`q ∘ h = φ`, `q' ∘ h' = φ'`). For an `ℝ`-Cartier divisor `M` on `Z`, the pull-backs `q^*M` and
`q'^*M` have the same coefficient along prime divisors `P ⊆ W` and `P' ⊆ W'` over a prime
divisor `G` of `U` and its image `G'`: near `η_G` both pull back to the pull-back of `M` along
one morphism from an open of `X` to `Z`. -/
private theorem coeff_isRCartierPullback_eq_of_partialIso {X X' Z W W' : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsIntegral W'] [IsLocallyNoetherian W'] [IsNormal W']
    [IsSeparated (X ↘ CategoryTheory.Limits.terminal Scheme)]
    [IsSeparated (X' ↘ CategoryTheory.Limits.terminal Scheme)]
    [IsSeparated (Z ↘ CategoryTheory.Limits.terminal Scheme)]
    (e : X.PartialIso X') {φ : X.RationalMap Z} {φ' : X'.RationalMap Z}
    [e.toRationalMap.IsDominant] (hcomp : e.toRationalMap.comp φ' = φ)
    (p : W ⟶ X) (q : W ⟶ Z) (h : X.RationalMap W) [IsProper p] [IsDominant q]
    (hpb : IsBirationalMorphism p) (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h)
    (hh : h.compHom q = φ)
    (p' : W' ⟶ X') (q' : W' ⟶ Z) (h' : X'.RationalMap W') [IsProper p'] [IsDominant q']
    (hp'b : IsBirationalMorphism p') (hinv' : MMP.Mori.RationalMap.IsInverse p'.toRationalMap h')
    (hh' : h'.compHom q' = φ')
    {M : RDivisor Z} {GZ : RDivisor W} {GZ' : RDivisor W'}
    (hGZ : MMP.Flips.IsRCartierPullback q M GZ) (hGZ' : MMP.Flips.IsRCartierPullback q' M GZ')
    (G : MMP.Mori.PrimeDivisor X) (G' : MMP.Mori.PrimeDivisor X')
    (P : MMP.Mori.PrimeDivisor W) (P' : MMP.Mori.PrimeDivisor W')
    (hG : G.genericPoint ∈ e.source) (hGG' : G'.genericPoint = e.toPartialMap.hom ⟨_, hG⟩)
    (hP : p P.genericPoint = G.genericPoint) (hP' : p' P'.genericPoint = G'.genericPoint) :
    GZ.coeff P = GZ'.coeff P' := by
  classical
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant p' := hp'b.isDominant
  have hpbij := hpb.functionFieldMap_bijective
  have hp'bij := hp'b.functionFieldMap_bijective
  haveI : IsDominant e.toPartialMap.hom := isDominant_toPartialMap_hom e
  haveI : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι); infer_instance
  haveI : Nonempty X' := ⟨G'.genericPoint⟩
  have hco : Order.coheight G.genericPoint ≤ 1 := G.coheight_genericPoint.le
  have hco' : Order.coheight G'.genericPoint ≤ 1 := G'.coheight_genericPoint.le
  have hhid : h.compHom p = Scheme.Hom.toRationalMap (𝟙 X) := compHom_eq_of_isInverse hinv
  have hhid' : h'.compHom p' = Scheme.Hom.toRationalMap (𝟙 X') := compHom_eq_of_isInverse hinv'
  obtain ⟨ĥ, hĥ, hĥh⟩ := Scheme.RationalMap.mem_domain.mp
    (MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 X) p h hhid hco)
  obtain ⟨ĥ', hĥ', hĥh'⟩ := Scheme.RationalMap.mem_domain.mp
    (MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 X') p' h' hhid' hco')
  have hx'mem : e.toPartialMap.hom ⟨_, hG⟩ ∈ ĥ'.domain := hGG' ▸ hĥ'
  obtain ⟨hχ, -⟩ := comp_hom_apply e.toPartialMap ĥ' hG hx'mem
  set χ := e.toPartialMap.comp ĥ' with hχdef
  have hχs : χ.domain ≤ e.toPartialMap.domain := by
    rintro _ ⟨y, -, rfl⟩; exact y.2
  let U : X.Opens := ĥ.domain ⊓ χ.domain
  have hU : Dense (U : Set X) := by
    simp only [U, TopologicalSpace.Opens.coe_inf]
    exact ĥ.dense_domain.inter_of_isOpen_left χ.dense_domain ĥ.domain.isOpen
  have hGU : G.genericPoint ∈ U := ⟨hĥ, hχ⟩
  haveI : Nonempty U := ⟨⟨_, hGU⟩⟩
  haveI : IsNoetherian X := {}
  haveI : CompactSpace U :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (U : Set X))
  have hUs : U ≤ e.toPartialMap.domain := inf_le_right.trans hχs
  -- both composites represent `φ` on `U`
  have hab : (X.homOfLE (inf_le_left : U ≤ ĥ.domain) ≫ ĥ.hom) ≫ q =
      (X.homOfLE (inf_le_right : U ≤ χ.domain) ≫ χ.hom) ≫ q' := by
    refine hom_eq_of_toRationalMap_eq hU ?_
    rw [toRationalMap_restrict_comp ĥ hU inf_le_left q,
      toRationalMap_restrict_comp χ hU inf_le_right q', hĥh, hh,
      ← Scheme.RationalMap.compHom_toRationalMap, hχdef, comp_compHom,
      ← Scheme.RationalMap.toRationalMap_comp, Scheme.RationalMap.compHom_toRationalMap, hĥh',
      hh']
    exact hcomp.symm
  have hap : (X.homOfLE (inf_le_left : U ≤ ĥ.domain) ≫ ĥ.hom) ≫ p = U.ι ≫ 𝟙 X := by
    refine hom_eq_of_toRationalMap_eq hU ?_
    rw [toRationalMap_restrict_comp ĥ hU inf_le_left p, hĥh, hhid, toRationalMap_ι_comp hU]
  rw [Category.comp_id] at hap
  have hbp : (X.homOfLE (inf_le_right : U ≤ χ.domain) ≫ χ.hom) ≫ p' =
      (X.homOfLE hUs ≫ e.toPartialMap.hom) ≫ 𝟙 X' := by
    refine hom_eq_of_toRationalMap_eq hU ?_
    rw [toRationalMap_restrict_comp χ hU inf_le_right p',
      toRationalMap_restrict_comp e.toPartialMap hU hUs (𝟙 X'),
      ← Scheme.RationalMap.compHom_toRationalMap, hχdef, comp_compHom,
      ← Scheme.RationalMap.toRationalMap_comp, Scheme.RationalMap.compHom_toRationalMap, hĥh',
      hhid', Scheme.RationalMap.comp_toRationalMap]
  rw [Category.comp_id] at hbp
  set a : U.toScheme ⟶ W := X.homOfLE (inf_le_left : U ≤ ĥ.domain) ≫ ĥ.hom with ha
  set b : U.toScheme ⟶ W' := X.homOfLE (inf_le_right : U ≤ χ.domain) ≫ χ.hom with hb
  -- the prime divisor of `U` over `G`
  obtain ⟨Q, hQ⟩ := MMP.Threefold.Resolution.exists_primeDivisorMap_eq U G hGU
  have hQx : U.ι Q.genericPoint = G.genericPoint := by
    rw [← OpenWeilRestriction.genericPoint_primeDivisorMap, hQ]
  have hpa : p (a Q.genericPoint) = G.genericPoint := by
    rw [← Scheme.Hom.comp_apply, hap, hQx]
  have hax : a Q.genericPoint = P.genericPoint :=
    (eq_of_apply_eq_of_coheight_le_one p hpbij (hpa.trans hP.symm) (by rw [hP]; exact hco)).symm
  have hQs : X.homOfLE hUs Q.genericPoint = ⟨G.genericPoint, hG⟩ :=
    Subtype.ext ((Scheme.homOfLE_apply hUs Q.genericPoint).trans hQx)
  have hpb' : p' (b Q.genericPoint) = G'.genericPoint := by
    rw [← Scheme.Hom.comp_apply, hbp, Scheme.Hom.comp_apply, hGG']
    exact congrArg e.toPartialMap.hom hQs
  have hbx : b Q.genericPoint = P'.genericPoint :=
    (eq_of_apply_eq_of_coheight_le_one p' hp'bij (hpb'.trans hP'.symm)
      (by rw [hP']; exact hco')).symm
  -- local isomorphisms
  have hiso_a : IsIso (a.stalkMap Q.genericPoint) := by
    have : IsIso ((a ≫ p).stalkMap Q.genericPoint) := by rw [hap]; infer_instance
    exact isIso_stalkMap_of_isIso_comp a p hpbij _ (by rw [hpa]; exact hco)
  have hiso_b : IsIso (b.stalkMap Q.genericPoint) := by
    have : IsIso ((b ≫ p').stalkMap Q.genericPoint) := by rw [hbp]; infer_instance
    exact isIso_stalkMap_of_isIso_comp b p' hp'bij _ (by rw [hpb']; exact hco')
  -- dominance
  haveI : IsDominant U.ι := Opens.isDominant_ι hU
  haveI : IsDominant (a ≫ p) := by rw [hap]; infer_instance
  haveI : IsDominant a := isDominant_of_comp_eq a p hpbij
  haveI : IsDominant (X.homOfLE hUs) := Opens.isDominant_homOfLE hU hUs
  haveI : IsDominant (b ≫ p') := by rw [hbp]; infer_instance
  haveI : IsDominant b := isDominant_of_comp_eq b p' hp'bij
  -- the pull-backs to `U`
  obtain ⟨G₁, hG₁, hG₁c⟩ := exists_isRCartierPullback_comp a q hGZ
  obtain ⟨G₂, hG₂, hG₂c⟩ := exists_isRCartierPullback_comp b q' hGZ'
  rw [hab] at hG₁
  have hGeq : G₁ = G₂ := MMP.Flips.IsRCartierPullback.eq (b ≫ q') hG₁ hG₂
  rw [← hG₁c Q P hax hiso_a, ← hG₂c Q P' hbx hiso_b, hGeq]

/-- **The nef weak model and its vanishing comparison survive a step**, and no prime with
positive boundary coefficient is contracted. The step `X ⤏ X⁺` is the isomorphism of the opens
of `X` and `X⁺` over the locus `U ⊆ Z` where both contractions are isomorphisms; through it the
weak model descends (lemma on weak models along a step), the boundary transforms to `B⁺`, and the
comparison coefficients of the primes of positive coefficient are preserved. -/
private theorem weakModel_step (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hZQ : IsQFactorial sZ)
    {X X' Zs : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)}
    {πX : X ⟶ S} {πX' : X' ⟶ S} {K : Divisor X} {B : RDivisor X} {K' : Divisor X'}
    {B' : RDivisor X'} {R : Set (RelativeNumericalCurveClasses sX πX)} {f : X ⟶ Zs}
    {g : Zs ⟶ S} {fp : X' ⟶ Zs}
    (hgood : IsGood sS sZ πZ sX πX B) (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (hX' : MMP.Mori.IsProjectiveVariety ℂ sX' ∧ IsQFactorial sX' ∧ πX' ≫ sS = sX')
    (hstep : IsStep sX sX' sZs πX πX' K B K' B' R f g fp) :
    (∀ E : MMP.Mori.PrimeDivisor X,
        (E.support : Set X) ⊆ MMP.Mori.exceptionalSet f → B.coeff E = 0) ∧
      ∃ (Kw' : Divisor X') (φ' : X'.RationalMap Z),
        IsNefWeakModel sX' sZ sS πX' πZ Kw' B' φ' ∧ ComparisonVanishes sZ sX' Kw' B' φ' := by
  classical
  obtain ⟨hXp, hXQ, hπ, -, hT, Kw, φ, hφ, hCV⟩ := hgood
  obtain ⟨hX'p, hX'Q, hπ'⟩ := hX'
  have hneg := hstep.2.2.2.1
  have hc := hneg.isContraction
  have hXv := hneg.isNormalVariety_source
  have hZsv := hneg.isNormalVariety_target
  have hX'v := hX'Q.1
  haveI : IsSeparated sS := hS.toIsVariety.toIsSeparated
  haveI : IsIntegral Zs := hZsv.1.toIsIntegral
  haveI : IsNormal Zs := hZsv.2
  haveI : LocallyOfFiniteType sZs := hZsv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Zs := LocallyOfFiniteType.isLocallyNoetherian sZs
  haveI : QuasiCompact sZs := hZsv.1.toQuasiCompact
  haveI : CompactSpace Zs := QuasiCompact.compactSpace_of_compactSpace sZs
  haveI : IsSeparated sZs := hZsv.1.toIsSeparated
  have hZsep := isSeparated_toTerminal_of_isNormalVariety hZsv
  have hX'sep := isSeparated_toTerminal_of_isNormalVariety hX'v
  have hXsep := isSeparated_toTerminal_of_isNormalVariety hXv
  haveI : IsProper f := hc.isProper
  obtain ⟨hfb, hfpb⟩ := isBirationalMorphism_of_isStep hstep
  have hgS := comp_eq_of_isStep hstep hπ
  have hfps : fp ≫ sZs = sX' := by rw [← hgS, ← Category.assoc, hstep.2.2.2.2.1, hπ']
  haveI : IsProper fp := by
    haveI : IsProper (fp ≫ sZs) := by
      rw [hfps]; exact isProper_of_isProjectiveMorphism sX' hX'p.isProjective
    exact IsProper.of_comp fp sZs
  haveI : IsDominant f := hfb.isDominant
  haveI : IsDominant fp := hfpb.isDominant
  -- the weak model's canonical divisor and negativity
  obtain ⟨mw, hKw⟩ := hφ.isCanonicalDivisor
  obtain ⟨m, hKm⟩ := hK
  have hlin := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hXv hKw hKm
  have hnegw := IsNegativeExtremalContraction.of_linearlyEquivalent hneg hlin
  -- the target `Z` of the weak model
  haveI : IsSeparated sZ := hφ.isNormalVariety_target.1.toIsSeparated
  have hZsep' := isSeparated_toTerminal_of_isNormalVariety hφ.isNormalVariety_target
  haveI : IsProper πZ := by
    haveI : IsProper (πZ ≫ sS) := by
      rw [hφ.comp_eq_target]
      exact isProper_of_isProjectiveMorphism sZ hφ.isProjectiveVariety_target.isProjective
    exact IsProper.of_comp πZ sS
  -- the open locus of `Z` over which both contractions are isomorphisms
  set U : Zs.Opens := biregularLocus f ⊓ biregularLocus fp with hU
  haveI hUf : IsIso (f ∣_ U) := isBiregular_iff_le_biregularLocus.mpr inf_le_left
  haveI hUfp : IsIso (fp ∣_ U) := isBiregular_iff_le_biregularLocus.mpr inf_le_right
  have hUco : ∀ z : Zs, Order.coheight z ≤ 1 → z ∈ U := fun z hz =>
    ⟨MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f hfb hz,
      MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal fp hfpb hz⟩
  have hdense : ∀ {T : Scheme.{0}} [IsIntegral T] (u : T ⟶ Zs) [IsDominant u],
      Dense ((u ⁻¹ᵁ U : T.Opens) : Set T) := by
    intro T _ u _
    refine (u ⁻¹ᵁ U).isOpen.dense ⟨genericPoint T, ?_⟩
    change u (genericPoint T) ∈ U
    rw [MMP.Positivity.map_genericPoint_eq_of_isDominant u]
    refine hUco _ ?_
    rw [Order.coheight_eq_zero.mpr fun b _ => genericPoint_specializes b]
    exact zero_le_one
  let e : X.PartialIso X' :=
    { source := f ⁻¹ᵁ U
      dense_source := hdense f
      target := fp ⁻¹ᵁ U
      dense_target := hdense fp
      iso := asIso (f ∣_ U) ≪≫ (asIso (fp ∣_ U)).symm }
  have hhom : e.toPartialMap.hom ≫ fp = (f ⁻¹ᵁ U).ι ≫ f := by
    change ((asIso (f ∣_ U)).hom ≫ (asIso (fp ∣_ U)).inv) ≫ (fp ⁻¹ᵁ U).ι ≫ fp = _
    simp only [asIso_hom, asIso_inv, Category.assoc]
    rw [← morphismRestrict_ι fp U, IsIso.inv_hom_id_assoc, morphismRestrict_ι f U]
  have hfy : ∀ (x : X) (hx : x ∈ f ⁻¹ᵁ U), fp (e.toPartialMap.hom ⟨x, hx⟩) = f x := by
    intro x hx
    have h1 := congrArg (fun φ : (f ⁻¹ᵁ U).toScheme ⟶ Zs => φ ⟨x, hx⟩) hhom
    simp only [Scheme.Hom.comp_apply] at h1
    exact h1
  have hinjfp : ∀ (a b : X') (ha : a ∈ fp ⁻¹ᵁ U) (hb : b ∈ fp ⁻¹ᵁ U), fp a = fp b → a = b := by
    intro a b ha hb hab
    have hi : Function.Injective (fp ∣_ U) :=
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (fp ∣_ U)))).injective
    have key : ∀ (c) (hc : c ∈ fp ⁻¹ᵁ U), ((fp ∣_ U) ⟨c, hc⟩).1 = fp c := by
      intro c hc
      have h2 := congrArg (fun φ : (fp ⁻¹ᵁ U).toScheme ⟶ Zs => φ ⟨c, hc⟩)
        (morphismRestrict_ι fp U)
      simp only [Scheme.Hom.comp_apply] at h2
      exact h2
    have h1 : (fp ∣_ U) ⟨a, ha⟩ = (fp ∣_ U) ⟨b, hb⟩ :=
      Subtype.ext (by rw [key, key]; exact hab)
    exact congrArg Subtype.val (hi h1)
  have hinjf : ∀ (a b : X) (ha : a ∈ f ⁻¹ᵁ U) (hb : b ∈ f ⁻¹ᵁ U), f a = f b → a = b := by
    intro a b ha hb hab
    have hi : Function.Injective (f ∣_ U) :=
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (f ∣_ U)))).injective
    have key : ∀ (c) (hc : c ∈ f ⁻¹ᵁ U), ((f ∣_ U) ⟨c, hc⟩).1 = f c := by
      intro c hc
      have h2 := congrArg (fun φ : (f ⁻¹ᵁ U).toScheme ⟶ Zs => φ ⟨c, hc⟩)
        (morphismRestrict_ι f U)
      simp only [Scheme.Hom.comp_apply] at h2
      exact h2
    have h1 : (f ∣_ U) ⟨a, ha⟩ = (f ∣_ U) ⟨b, hb⟩ :=
      Subtype.ext (by rw [key, key]; exact hab)
    exact congrArg Subtype.val (hi h1)
  set g' : X.RationalMap X' := e.toRationalMap with hg'
  have hg'b : MMP.Mori.RationalMap.IsBirational g' :=
    MMP.Mori.RationalMap.isBirational_toRationalMap e
  haveI : g'.IsDominant := isDominant_of_isBirational_ph hg'b
  have hinv : MMP.Mori.RationalMap.IsInverse g' e.symm.toRationalMap :=
    MMP.Mori.RationalMap.isInverse_toRationalMap e
  haveI : e.symm.toRationalMap.IsDominant := isDominant_of_isBirational_ph hinv.isBirational_inverse
  set φ' : X'.RationalMap Z := e.symm.toRationalMap.comp φ with hφ'
  have hcomp : g'.comp φ' = φ := by
    rw [hφ', ← Scheme.RationalMap.comp_assoc]
    convert Scheme.RationalMap.id_comp φ using 2
    exact comp_eq_id_of_isInverse_ph hinv
  have hgu : g'.compHom fp = f.toRationalMap := by
    show (e.toPartialMap.toRationalMap).compHom fp = f.toPartialMap.toRationalMap
    rw [← Scheme.RationalMap.compHom_toRationalMap]
    exact Scheme.PartialMap.toRationalMap_eq_iff.mpr
      ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated
        (S := CategoryTheory.Limits.terminal Scheme)).mpr hhom)
  -- at a divisorial step, `g'` is the morphism `f ≫ (f⁺)⁻¹`
  have hrep : ∀ (_ : IsIso fp), g' = (f ≫ inv fp).toRationalMap := by
    intro hiso
    show e.toPartialMap.toRationalMap = (f ≫ inv fp).toPartialMap.toRationalMap
    refine Scheme.PartialMap.toRationalMap_eq_iff.mpr
      ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated
        (S := CategoryTheory.Limits.terminal Scheme)).mpr ?_)
    refine (cancel_mono fp).mp ?_
    change e.toPartialMap.hom ≫ fp = (e.toPartialMap.domain.ι ≫ f ≫ inv fp) ≫ fp
    rw [hhom, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rfl
  -- the coheight condition on `f⁺`
  have hu1 : ∀ D : MMP.Mori.PrimeDivisor X', Order.coheight (fp D.genericPoint) ≤ 1 := by
    rcases hstep.2.2.2.2.2 with ⟨-, hiso, -, -⟩ | hfl
    · intro D
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fp
        (le_biregularLocus ((isBiregular_top_iff fp).mpr hiso) trivial), D.coheight_genericPoint]
    · intro D
      obtain ⟨V₂, W₂, hV₂, -, hle₂, hiso₂⟩ := exists_closeds_isIso_of_isSmall_ph hfl.isSmall_flip
      have hD : D.genericPoint ∈ (V₂.compl : Set X') := fun h =>
        absurd (hV₂ _ h) (by rw [D.coheight_genericPoint]; decide)
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fp
        (le_biregularLocus hiso₂ (hle₂ hD)), D.coheight_genericPoint]
  -- primes outside `Ex(f)` lie over `U`, and their transforms are prime divisors of `X⁺`
  have hGU : ∀ G : MMP.Mori.PrimeDivisor X,
      G.genericPoint ∉ (MMP.Mori.exceptionalSet f : Set X) → G.genericPoint ∈ f ⁻¹ᵁ U := by
    intro G hG
    have hbr : f G.genericPoint ∈ biregularLocus f :=
      not_not.mp fun h => hG (MMP.Mori.mem_exceptionalSet.mpr h)
    exact hUco _ ((MMP.Positivity.coheight_map_of_mem_biregularLocus f hbr).trans
      G.coheight_genericPoint).le
  have himage : ∀ (G : MMP.Mori.PrimeDivisor X) (hG : G.genericPoint ∈ f ⁻¹ᵁ U),
      ∃ G' : MMP.Mori.PrimeDivisor X', G'.genericPoint = e.toPartialMap.hom ⟨_, hG⟩ ∧
        RationalMap.transformPrimeDivisor g' G = some G' := by
    intro G hG
    have hmem : e.toPartialMap.hom ⟨_, hG⟩ ∈ fp ⁻¹ᵁ U := (e.iso.hom ⟨_, hG⟩).2
    have hco : Order.coheight (e.toPartialMap.hom ⟨_, hG⟩) = 1 := by
      rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp hmem.2, hfy,
        MMP.Positivity.coheight_map_of_mem_biregularLocus f hG.1, G.coheight_genericPoint]
    refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco, ?_⟩
    exact transformPrimeDivisor_eq_some_of_genericPoint_eq_ph e.toPartialMap rfl hG
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco)
  -- the primes of `Ex(f)`: none for a flip, the contracted prime for a divisorial step
  have hEx : ∀ G : MMP.Mori.PrimeDivisor X,
      G.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set X) →
      (MMP.Mori.exceptionalSet f : Set X) = G.support := by
    intro G hG
    rcases hstep.2.2.2.2.2 with ⟨⟨-, E₀, hE₀⟩, -, -, -⟩ | hfl
    · rw [hE₀] at hG ⊢
      rw [MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hG]
    · have := two_le_coheight_of_mem_exceptionalSet_of_isSmall hfl.isSmall hG
      rw [G.coheight_genericPoint] at this
      exact absurd this (by decide)
  -- every prime divisor of `X⁺` lies over one of `X`, through `U`
  have hover : ∀ P' : MMP.Mori.PrimeDivisor X', ∃ (P : MMP.Mori.PrimeDivisor X)
      (hP : P.genericPoint ∈ f ⁻¹ᵁ U), f P.genericPoint = fp P'.genericPoint ∧
        e.toPartialMap.hom ⟨_, hP⟩ = P'.genericPoint := by
    intro P'
    have hco1 := hu1 P'
    have hmem : fp P'.genericPoint ∈ U := hUco _ hco1
    have hco : Order.coheight (fp P'.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fp hmem.2, P'.coheight_genericPoint]
    set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco with hQdef
    have hQ : Q.genericPoint = fp P'.genericPoint :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
    have hQ' : MMP.Mori.PrimeDivisor.genericPoint Q = fp P'.genericPoint := hQ
    obtain ⟨P, hP, -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hZsv
        (by rw [hc.comp_eq]; exact hXv) hfb Q
    have hPU : P.genericPoint ∈ f ⁻¹ᵁ U := by
      change f P.genericPoint ∈ U; rw [hP, hQ']; exact hmem
    refine ⟨P, hPU, hP.trans hQ, ?_⟩
    refine hinjfp _ _ (e.iso.hom ⟨_, hPU⟩).2 ⟨hmem.1, hmem.2⟩ ?_
    rw [hfy, hP, hQ']
  -- the uniqueness of the prime over a prime of `X⁺`
  have huniq : ∀ (G : MMP.Mori.PrimeDivisor X) (P : MMP.Mori.PrimeDivisor X)
      (P' : MMP.Mori.PrimeDivisor X') (hP : P.genericPoint ∈ f ⁻¹ᵁ U),
      e.toPartialMap.hom ⟨_, hP⟩ = P'.genericPoint →
      RationalMap.transformPrimeDivisor g' G = some P' → G = P := by
    intro G P P' hP hPP' hG
    by_cases hGEx : G.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set X)
    · exfalso
      rcases hstep.2.2.2.2.2 with ⟨⟨-, E₀, hE₀⟩, hiso, -, -⟩ | hfl
      · haveI := hiso
        rw [hrep hiso, MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff] at hG
        have h2 : f G.genericPoint = fp P'.genericPoint := by
          rw [← hG, ← Scheme.Hom.comp_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        have hmem : f G.genericPoint ∈ U := h2 ▸ hUco _ (hu1 P')
        exact (MMP.Mori.mem_exceptionalSet.mp hGEx) hmem.1
      · have := two_le_coheight_of_mem_exceptionalSet_of_isSmall hfl.isSmall hGEx
        rw [G.coheight_genericPoint] at this
        exact absurd this (by decide)
    · have hGU' := hGU G hGEx
      have h1 := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hG e.toPartialMap rfl
        hGU'
      have h2 : f G.genericPoint = f P.genericPoint := by
        rw [← hfy _ hGU', ← hfy _ hP, ← h1, hPP']
      exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hinjf _ _ hGU' hP h2)
  -- coefficients of transforms along `g'` and along the flip transform
  have htrans : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X)
      (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor X')
      (hP : P.genericPoint ∈ f ⁻¹ᵁ U), e.toPartialMap.hom ⟨_, hP⟩ = P'.genericPoint →
        RationalMap.transformDivisor g' D P' = D P := by
    intro R _ D P P' hP hhP
    obtain ⟨G', hG', htr⟩ := himage P hP
    have hG'P' : G' = P' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hG'.trans hhP)
    subst hG'P'
    rw [RationalMap.transformDivisor]
    exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq htr
      (fun G hG => huniq G P G' hP hhP hG) D
  have htransC : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X)
      (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor X')
      (hP : P.genericPoint ∈ f ⁻¹ᵁ U), e.toPartialMap.hom ⟨_, hP⟩ = P'.genericPoint →
        (RationalMap.transformDivisor g' D).coeff P' = D.coeff P :=
    fun D P P' hP hhP => htrans D P P' hP hhP
  have hflipT : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X)
      (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor X'),
      f P.genericPoint = fp P'.genericPoint → flipTransform f fp D P' = D P := by
    intro R _ D P P' hPP'
    have hco1 := hu1 P'
    have hmem : fp P'.genericPoint ∈ U := hUco _ hco1
    have hco : Order.coheight (fp P'.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fp hmem.2, P'.coheight_genericPoint]
    set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco with hQdef
    have hQ : Q.genericPoint = fp P'.genericPoint :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
    have hQ' : MMP.Mori.PrimeDivisor.genericPoint Q = fp P'.genericPoint := hQ
    haveI := MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing Q
    exact flipTransform_apply_of_map_genericPoint hfb.functionFieldMap_bijective
      fp.surjective (hPP'.trans hQ.symm) hQ.symm (by rw [hQ']; exact hmem.2) D
  -- the transform of the boundary is `B⁺`
  have hflB : B' = flipTransform f fp B := by
    rcases hstep.2.2.2.2.2 with ⟨-, -, -, h⟩ | hfl
    · exact h
    · exact hfl.eq_flipTransform
  have hcoeffB : ∀ (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor X'),
      f P.genericPoint = fp P'.genericPoint → B' P' = B P := fun P P' hPP' => by
    rw [hflB]; exact hflipT B P P' hPP'
  have hB'eq : RationalMap.transformDivisor g' B = B' := by
    ext P'
    simp only [DivisorWithCoeffs.coeff_apply]
    obtain ⟨P, hP, hPP', hhP⟩ := hover P'
    rw [htrans B P P' hP hhP, hcoeffB P P' hPP']
  have hKgflip : RationalMap.transformDivisor g' Kw = flipTransform f fp Kw := by
    ext P'
    simp only [DivisorWithCoeffs.coeff_apply]
    obtain ⟨P, hP, hPP', hhP⟩ := hover P'
    rw [htrans Kw P P' hP hhP, hflipT Kw P P' hPP']
  -- at a divisorial step, the contracted prime is `g'`-exceptional
  have hgex : ∀ (hiso : IsIso fp) (E₀ : MMP.Mori.PrimeDivisor X),
      (MMP.Mori.exceptionalSet f : Set X) = E₀.support →
        MMP.Mori.RationalMap.IsExceptional g' E₀ := by
    intro hiso E₀ hE₀
    rw [hrep hiso]
    refine isExceptional_of_genericPoint_mem_exceptionalSet (f ≫ inv fp)
      (MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hfb
        (isBirationalMorphism_of_isIso _)) E₀ ?_
    refine exceptionalSet_subset_ph (f ≫ inv fp) ?_
    rw [flips_exceptionalSet_comp_iso, flips_exceptionalSet_eq_of_mori f hfb hE₀,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  -- the step in the form of the lemma on weak models along a step
  have hstep' : (∃ f₀ : X ⟶ X', f₀.toRationalMap = g' ∧ f₀ ≫ πX' = πX ∧
          IsNegativeExtremalContraction ℂ sX sX' (logCanonicalDivisor Kw B) f₀ ∧
          IsBirationalMorphism f₀ ∧
          ∃ E : MMP.Mori.PrimeDivisor X, MMP.Flips.exceptionalSet f₀ = E.support) ∨
        (∃ (V : Scheme.{0}) (sV : V ⟶ Spec (.of ℂ)) (πV : V ⟶ S) (f₁ : X ⟶ V) (fp₁ : X' ⟶ V),
          f₁ ≫ πV = πX ∧ fp₁ ≫ πV = πX' ∧
          IsNegativeExtremalContraction ℂ sX sV (logCanonicalDivisor Kw B) f₁ ∧
          MMP.Flips.IsFlip ℂ sX sV sX' (logCanonicalDivisor Kw B) f₁ fp₁ g') := by
    rcases hstep.2.2.2.2.2 with ⟨⟨-, E₀, hE₀⟩, hiso, -, -⟩ | hfl
    · haveI := hiso
      refine Or.inl ⟨f ≫ inv fp, (hrep hiso).symm, ?_, ?_,
        MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hfb
          (isBirationalMorphism_of_isIso _), E₀, ?_⟩
      · rw [Category.assoc, ← hstep.2.2.2.2.1, IsIso.inv_hom_id_assoc, hstep.2.2.1.comp_eq]
      · exact isNegativeExtremalContraction_comp_iso hnegw (inv fp)
          (by rw [IsIso.inv_comp_eq, hfps]) hX'v
      · rw [flips_exceptionalSet_comp_iso]; exact flips_exceptionalSet_eq_of_mori f hfb hE₀
    · refine Or.inr ⟨Zs, sZs, g, f, fp, hstep.2.2.1.comp_eq, hstep.2.2.2.2.1, hnegw, ?_⟩
      obtain ⟨V₁, W₁, hV₁, -, hle₁, hiso₁⟩ := exists_closeds_isIso_of_isSmall_ph hfl.isSmall
      obtain ⟨V₂, W₂, hV₂, -, hle₂, hiso₂⟩ := exists_closeds_isIso_of_isSmall_ph hfl.isSmall_flip
      have hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ U := fun x hx => by
        have hxV : x ∈ (V₁.compl : Set X) := fun h => absurd ((hV₁ x h).trans hx) (by decide)
        have hb : f x ∈ biregularLocus f := le_biregularLocus hiso₁ (hle₁ hxV)
        exact hUco _ ((MMP.Positivity.coheight_map_of_mem_biregularLocus f hb).trans_le hx)
      have hX'V : ∀ x : X', Order.coheight x ≤ 1 → fp x ∈ U := fun x hx => by
        have hxV : x ∈ (V₂.compl : Set X') := fun h => absurd ((hV₂ x h).trans hx) (by decide)
        have hb : fp x ∈ biregularLocus fp := le_biregularLocus hiso₂ (hle₂ hxV)
        exact hUco _ ((MMP.Positivity.coheight_map_of_mem_biregularLocus fp hb).trans_le hx)
      have hKw' : Kw.IsCanonicalDivisor (f ≫ sZs) mw := by rw [hc.comp_eq]; exact hKw
      have hKgc : Divisor.IsCanonicalDivisor sX' mw (RationalMap.transformDivisor g' Kw) := by
        rw [hKgflip, ← hfps]
        exact MMP.Mori.isCanonicalDivisor_flipTransform_of_isIso_restrict hZsv
          (by rw [hc.comp_eq]; exact hXv) (by rw [hfps]; exact hX'v) hfb hfpb U hXV hX'V hKw'
      obtain ⟨m', hK'm⟩ := hfl.isCanonicalDivisor_flip
      obtain ⟨φ₀, hφ₀⟩ :=
        MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX' hX'v hKgc hK'm
      have hNc : Divisor.IsCartier (RationalMap.transformDivisor g' Kw - K') :=
        hφ₀ ▸ Divisor.isCartier_principalDivisor φ₀
      have hN : Divisor.LinearlyEquivalent (RationalMap.transformDivisor g' Kw - K') 0 :=
        ⟨φ₀, by rw [sub_zero]; exact hφ₀⟩
      have hTK : RationalMap.transformDivisor g' (Divisor.toRDivisor Kw) =
          Divisor.toRDivisor (RationalMap.transformDivisor g' Kw) := by
        refine DivisorWithCoeffs.ext' fun P' => ?_
        obtain ⟨P, hP, -, hhP⟩ := hover P'
        rw [Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
          htrans (Divisor.toRDivisor Kw) P P' hP hhP, htrans Kw P P' hP hhP]
        exact Divisor.coeff_toRDivisor Kw P
      have hTg : RationalMap.transformDivisor g' (logCanonicalDivisor Kw B) =
          logCanonicalDivisor K' B' +
            Divisor.toRDivisor (RationalMap.transformDivisor g' Kw - K') := by
        simp only [logCanonicalDivisor, map_add, map_sub, hTK, hB'eq]
        abel
      have hamp : IsRelativelyAmple fp
          (RationalMap.transformDivisor g' (logCanonicalDivisor Kw B)) := by
        rw [hTg]
        exact isRelativelyAmple_add_of_linearlyEquivalent hX'v hZsv fp hfps
          hfl.isRelativelyAmple_flip hNc hN
      exact
        { isNormalVariety_source := hXv
          isNormalVariety_target := hZsv
          isNormalVariety_flip := hX'v
          isContraction := hnegw.isContraction
          isCartierCombination := hnegw.isCartierCombination
          isRelativelyAntiAmple := hnegw.isRelativelyAntiAmple
          isProper := inferInstance
          isModificationOf := ⟨hg'b, hgu⟩
          isMorphismInCodimOne :=
            MMP.Flips.RationalMap.isMorphismInCodimOne_of_isOver hXv f fp g' hgu
          isSmall := hfl.isSmall_flip
          isCartierCombination_transform := isCartierCombination_of_isQFactorial_ph hX'Q _
          isRelativelyAmple_transform := hamp
          isSmall_source := hfl.isSmall }
  -- the weak model descends along the step
  have hpub := (IsNefWeakModel.isNefWeakModel_of_negativeStep hφ hXQ hZQ).1 sX' πX' g' φ'
    hX'p hX'Q hπ' hstep' hcomp
  have hnew := hpub.1
  -- (a) no prime of positive coefficient is contracted
  have hnc : ∀ E : MMP.Mori.PrimeDivisor X,
      (E.support : Set X) ⊆ MMP.Mori.exceptionalSet f → B.coeff E = 0 := by
    intro E hEx'
    by_contra hne
    have hηE : E.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set X) := by
      refine hEx' ?_
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    rcases hstep.2.2.2.2.2 with ⟨⟨-, E₀, hE₀⟩, hiso, -, -⟩ | hfl
    · have hEE₀ : E₀ = E := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support
        (hE₀ ▸ hηE)
      subst hEE₀
      have hpos : 0 < B.coeff E₀ :=
        lt_of_le_of_ne (nonneg_of_isRealCanonicalPair hT.1 E₀) (Ne.symm hne)
      obtain ⟨W, _, _, _, sW, p, q, h, GY, GZ, P, hW, hpY, hqZ, hp, hq, hpb, hqb, hinv, hhq, hGY,
        hGZ, hPE, h0⟩ := hCV E₀ hpos
      exact hpub.2 sW p q h hW hpY hqZ hp hq hpb hqb hinv hhq hGY hGZ E₀ P hPE h0
        (hgex hiso E₀ hE₀)
    · have := two_le_coheight_of_mem_exceptionalSet_of_isSmall hfl.isSmall hηE
      rw [E.coheight_genericPoint] at this
      exact absurd this (by decide)
  refine ⟨hnc, ?_⟩
  -- the transform to `Z` does not change: `φ⁺_* g'_* = φ_*`
  have hT1 : ∀ (G : MMP.Mori.PrimeDivisor X) (G' : MMP.Mori.PrimeDivisor X')
      (hG : G.genericPoint ∈ f ⁻¹ᵁ U), G'.genericPoint = e.toPartialMap.hom ⟨_, hG⟩ →
        RationalMap.transformPrimeDivisor φ' G' = RationalMap.transformPrimeDivisor φ G := by
    intro G G' hG hG'
    obtain ⟨r, hr, hrφ⟩ := Scheme.RationalMap.mem_domain.mp
      (MMP.Flips.RationalMap.mem_domain_of_coheight_le_one πX' πZ φ' hnew.isOver
        G'.coheight_genericPoint.le)
    have hmem : e.toPartialMap.hom ⟨_, hG⟩ ∈ r.domain := hG' ▸ hr
    haveI : IsDominant e.toPartialMap.hom := isDominant_toPartialMap_hom e
    obtain ⟨hχ, hχv⟩ := comp_hom_apply e.toPartialMap r hG hmem
    have hχφ : (e.toPartialMap.comp r).toRationalMap = φ := by
      rw [← Scheme.RationalMap.toRationalMap_comp, hrφ]; exact hcomp
    have hrv : r.hom ⟨G'.genericPoint, hr⟩ = (e.toPartialMap.comp r).hom ⟨_, hχ⟩ := by
      rw [hχv]; congr 1; exact Subtype.ext hG'
    cases hF : RationalMap.transformPrimeDivisor φ G with
    | none =>
      cases hF' : RationalMap.transformPrimeDivisor φ' G' with
      | none => rfl
      | some F =>
        exfalso
        have h1 := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hF' r hrφ hr
        have h2 := transformPrimeDivisor_eq_some_of_genericPoint_eq_ph (e.toPartialMap.comp r)
          hχφ hχ (h1.trans hrv)
        rw [hF] at h2
        cases h2
    | some F =>
      have h1 := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hF
        (e.toPartialMap.comp r) hχφ hχ
      exact transformPrimeDivisor_eq_some_of_genericPoint_eq_ph r hrφ hr (h1.trans hrv.symm)
  have hT2 : ∀ (_ : IsIso fp) (G : MMP.Mori.PrimeDivisor X),
      (MMP.Mori.exceptionalSet f : Set X) = G.support →
        RationalMap.transformPrimeDivisor φ G = none := by
    intro hiso G hGE
    cases hF : RationalMap.transformPrimeDivisor φ G with
    | none => rfl
    | some F =>
      exfalso
      obtain ⟨W₀, _, _, _, sW₀, p₀, q₀, h₀, hW₀, -, hp₀Y, hq₀Z, hp₀, hq₀, hp₀b, hq₀b, hinv₀,
        hhq₀, GY₀, GZ₀, hGY₀, hGZ₀, -, hA₀q⟩ := hφ.exists_resolution
      haveI : IsProper p₀ := isProper_of_isProjectiveMorphism p₀ hp₀
      haveI : IsDominant p₀ := hp₀b.isDominant
      obtain ⟨P₀, hP₀, -, -⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXv
          (by rw [hp₀Y]; exact ⟨hW₀, inferInstance⟩) hp₀b G
      have hhid₀ : h₀.compHom p₀ = Scheme.Hom.toRationalMap (𝟙 X) := compHom_eq_of_isInverse hinv₀
      obtain ⟨ĥ, hĥ, hĥh⟩ := Scheme.RationalMap.mem_domain.mp
        (MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 X) p₀ h₀ hhid₀
          G.coheight_genericPoint.le)
      obtain ⟨ep, hep, hep'⟩ := id hinv₀
      have hpĥ : p₀ (ĥ.hom ⟨_, hĥ⟩) = G.genericPoint :=
        apply_hom_eq_of_isInverse p₀ ep hep ĥ (hĥh.trans hep'.symm) hĥ
      have hĥP : ĥ.hom ⟨_, hĥ⟩ = P₀.genericPoint :=
        (eq_of_apply_eq_of_coheight_le_one p₀ hp₀b.functionFieldMap_bijective
          (hpĥ.trans hP₀.symm) (by rw [hP₀]; exact G.coheight_genericPoint.le)).symm
      have hrepφ : (ĥ.compHom q₀).toRationalMap = φ := by
        rw [Scheme.RationalMap.compHom_toRationalMap, hĥh, hhq₀]
      have hFη : F.genericPoint = q₀ P₀.genericPoint := by
        rw [MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hF (ĥ.compHom q₀) hrepφ hĥ]
        show (ĥ.hom ≫ q₀) ⟨_, hĥ⟩ = _
        exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg q₀ hĥP)
      have h0 : (GY₀ - GZ₀).coeff P₀ = 0 := by
        by_contra hne
        obtain ⟨hWn, hqb', hqp, hex⟩ := hA₀q P₀ hne
        have hZv := hφ.isNormalVariety_target
        haveI : LocallyOfFiniteType sZ := hZv.1.toLocallyOfFiniteType
        haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
        obtain ⟨n, hZdim⟩ :=
          MMP.Fourfold.Oai4C1.Negativity.exists_topologicalKrullDim_eq_natCast sZ
        unfold MMP.Flips.ProperDivisorOver.IsExceptional at hex
        rw [MMP.Flips.ProperDivisorOver.center_eq_toDivisorOver_center,
          DivisorOver.center_eq_closure_genericPoint, hZdim] at hex
        have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sZ
          (q₀ P₀.genericPoint)
        rw [hZdim] at hd
        have h2 := (MMP.Fourfold.Oai4C1.Negativity.withBot_add_two_le_iff hd).mp hex
        rw [← hFη, F.coheight_genericPoint] at h2
        exact absurd h2 (by decide)
      exact hpub.2 sW₀ p₀ q₀ h₀ hW₀ hp₀Y hq₀Z hp₀ hq₀ hp₀b hq₀b hinv₀ hhq₀ hGY₀ hGZ₀ G P₀
        ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p₀ P₀ G).mpr hP₀) h0
        (hgex hiso G hGE)
  have hTfun : ∀ G : MMP.Mori.PrimeDivisor X,
      (RationalMap.transformPrimeDivisor g' G).bind (RationalMap.transformPrimeDivisor φ') =
        RationalMap.transformPrimeDivisor φ G := by
    intro G
    by_cases hGEx : G.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set X)
    · rcases hstep.2.2.2.2.2 with ⟨-, hiso, -, -⟩ | hfl
      · have hGE := hEx G hGEx
        have hnone : RationalMap.transformPrimeDivisor g' G = none := by
          cases hG : RationalMap.transformPrimeDivisor g' G with
          | none => rfl
          | some G' =>
            exact absurd (hgex hiso G hGE)
              (not_isExceptional_of_transformPrimeDivisor_eq_some_ph hG)
        rw [hnone, Option.bind_none, hT2 hiso G hGE]
      · have := two_le_coheight_of_mem_exceptionalSet_of_isSmall hfl.isSmall hGEx
        rw [G.coheight_genericPoint] at this
        exact absurd this (by decide)
    · obtain ⟨G', hG', htr⟩ := himage G (hGU G hGEx)
      rw [htr, Option.bind_some]
      exact hT1 G G' (hGU G hGEx) hG'
  have hTT : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
      RationalMap.transformDivisor φ' (RationalMap.transformDivisor g' D) =
        RationalMap.transformDivisor φ D := by
    intro R _ D
    simp only [RationalMap.transformDivisor]
    rw [mapPrimeDivisors_mapPrimeDivisors]
    exact congrArg (fun χ => DivisorWithCoeffs.mapPrimeDivisors χ D) (funext hTfun)
  refine ⟨RationalMap.transformDivisor g' Kw, φ', hB'eq ▸ hnew, ?_⟩
  -- the comparison still vanishes along the primes of positive coefficient
  intro G' hG'pos
  obtain ⟨P, hP, hPP', hhP⟩ := hover G'
  obtain ⟨G'', hG'', htr⟩ := himage P hP
  have hG''G' : G'' = G' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hG''.trans hhP)
  subst hG''G'
  have hPpos : 0 < B.coeff P := by
    have := hcoeffB P G'' hPP'
    simp only [DivisorWithCoeffs.coeff_apply] at hG'pos ⊢
    rwa [this] at hG'pos
  obtain ⟨W, _, _, _, sW, p, q, h, GY, GZ, PW, hW, hpY, hqZ, hp, hq, hpb, hqb, hinvW, hhq, hGY,
    hGZ, hPW, h0⟩ := hCV P hPpos
  obtain ⟨W', _, _, _, sW', p', q', h', hW', hW's, hp'Y, hq'Z, hp', hq', hp'b, hq'b, hinv',
    hhq', GY', GZ', hGY', hGZ', -, -⟩ := hnew.exists_resolution
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hp
  haveI : IsProper p' := isProper_of_isProjectiveMorphism p' hp'
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant p' := hp'b.isDominant
  haveI : IsDominant q := hqb.isDominant
  haveI : IsDominant q' := hq'b.isDominant
  obtain ⟨PW', hPW', -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX'v
      (by rw [hp'Y]; exact ⟨hW', inferInstance⟩) hp'b G''
  have hPW'G : RationalMap.transformPrimeDivisor p'.toRationalMap PW' = some G'' :=
    (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p' PW' G'').mpr hPW'
  have hPWG : p PW.genericPoint = P.genericPoint :=
    (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p PW P).mp hPW
  -- the coefficients of the pull-backs of the adjoints of `X` and `X⁺`
  have hY : GY.coeff PW = (logCanonicalDivisor Kw B).coeff P :=
    coeff_isRCartierPullback_eq p hpb.functionFieldMap_bijective hGY PW P hPWG
  have hY' : GY'.coeff PW' = (logCanonicalDivisor (RationalMap.transformDivisor g' Kw)
      (RationalMap.transformDivisor g' B)).coeff G'' :=
    coeff_isRCartierPullback_eq p' hp'b.functionFieldMap_bijective hGY' PW' G'' hPW'
  have hYeq : (logCanonicalDivisor (RationalMap.transformDivisor g' Kw)
      (RationalMap.transformDivisor g' B)).coeff G'' = (logCanonicalDivisor Kw B).coeff P := by
    simp only [logCanonicalDivisor, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor]
    rw [htransC Kw P G'' hP hhP, htransC B P G'' hP hhP]
  -- the coefficients of the pull-backs of the adjoint of `Z`
  have hGZ'' := hGZ'
  rw [hTT, hTT] at hGZ''
  haveI : e.toRationalMap.IsDominant := isDominant_of_isBirational_ph hg'b
  have hZ : GZ.coeff PW = GZ'.coeff PW' :=
    coeff_isRCartierPullback_eq_of_partialIso e hcomp p q h hpb hinvW hhq p' q' h' hp'b hinv'
      hhq' hGZ hGZ'' P G'' PW PW' hP hhP.symm hPWG hPW'
  rw [hB'eq] at hGY' hGZ'
  refine ⟨W', inferInstance, inferInstance, inferInstance, sW', p', q', h', GY', GZ', PW', hW',
    hp'Y, hq'Z, hp', hq', hp'b, hq'b, hinv', hhq', hGY', hGZ', hPW'G, ?_⟩
  rw [DivisorWithCoeffs.coeff_sub, hY', hYeq, ← hY, ← hZ, ← DivisorWithCoeffs.coeff_sub]
  exact h0

/-- **Real flips preserve real terminality**: a small contraction has no exceptional prime, the
flip is an isomorphism in codimension one, and `K⁺ + B⁺` is `f⁺`-ample. -/
private theorem isRealTerminalPair_of_isRealFlipStep {X X' Zs : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    {sZs : Zs ⟶ Spec (.of ℂ)} {K : Divisor X} {B : RDivisor X} {K' : Divisor X'}
    {B' : RDivisor X'} {f : X ⟶ Zs} {fp : X' ⟶ Zs}
    (hfl : IsRealFlipStep sX sZs sX' K B K' B' f fp) (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (hT : IsRealTerminalPair sX B) (hXp : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hX'Q : IsQFactorial sX') :
    IsRealTerminalPair sX' B' := by
  have hZv := hfl.isNegativeExtremalContraction.isNormalVariety_target
  haveI : IsIntegral Zs := hZv.1.toIsIntegral
  haveI : IsProper fp := hfl.isSmall_flip.isProper
  haveI : Surjective fp :=
    hfl.isSmall_flip.toIsBirationalContraction.surjective_and_isBirational.1
  have hfps : fp ≫ sZs = sX' := hfl.isSmall_flip.comp_eq
  have hX'v := hX'Q.1
  have hB' := hfl.eq_flipTransform
  subst hB'
  refine isRealTerminalPair_of_step hfl.isNegativeExtremalContraction hfl.isBirationalMorphism
    hfl.isBirationalMorphism_flip
    (fun P' => (coheight_map_genericPoint_of_isSmall hfl.isSmall_flip P').1.le)
    (fun z hz => mem_biregularLocus_of_isSmall_ph hfl.isSmall_flip hz) hfps hK
    hfl.isCanonicalDivisor_flip (fun K'' hlin => ?_) (fun P hP => ?_) hT hXp hX'Q
  · obtain ⟨φ₀, hφ₀⟩ := hlin
    have hNc : Divisor.IsCartier (K'' - K') := hφ₀ ▸ Divisor.isCartier_principalDivisor φ₀
    have hN : Divisor.LinearlyEquivalent (K'' - K') 0 := ⟨φ₀, by rw [sub_zero]; exact hφ₀⟩
    have hL : logCanonicalDivisor K'' (flipTransform f fp B) =
        logCanonicalDivisor K' (flipTransform f fp B) + Divisor.toRDivisor (K'' - K') := by
      simp only [logCanonicalDivisor, map_sub]
      abel
    haveI : IsNormal Zs := hZv.2
    haveI : LocallyOfFiniteType sZs := hZv.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian Zs := LocallyOfFiniteType.isLocallyNoetherian sZs
    haveI : QuasiCompact sX' := hX'v.1.toQuasiCompact
    rw [hL]
    exact isRelativelyNef_of_isRelativelyAmple hX'v hZv fp hfps
      (isRelativelyAmple_add_of_linearlyEquivalent hX'v hZv fp hfps hfl.isRelativelyAmple_flip
        hNc hN)
  · have := two_le_coheight_of_mem_exceptionalSet_of_isSmall hfl.isSmall hP
    rw [P.coheight_genericPoint] at this
    exact absurd this (by decide)

/-- **One step keeps a model good.** The next model is good, no prime with positive boundary
coefficient is contracted, and the Picard number does not increase, strictly decreasing at a
divisorial contraction. -/
private theorem isGood_step (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hZQ : IsQFactorial sZ)
    {X X' Zs : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)}
    {πX : X ⟶ S} {πX' : X' ⟶ S} {K : Divisor X} {B : RDivisor X} {K' : Divisor X'}
    {B' : RDivisor X'} {R : Set (RelativeNumericalCurveClasses sX πX)} {f : X ⟶ Zs}
    {g : Zs ⟶ S} {fp : X' ⟶ Zs}
    (hgood : IsGood sS sZ πZ sX πX B) (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (hX' : MMP.Mori.IsProjectiveVariety ℂ sX' ∧ IsQFactorial sX' ∧ πX' ≫ sS = sX')
    (hstep : IsStep sX sX' sZs πX πX' K B K' B' R f g fp) :
    IsGood sS sZ πZ sX' πX' B' ∧
      (∀ E : MMP.Mori.PrimeDivisor X,
        (E.support : Set X) ⊆ MMP.Mori.exceptionalSet f → B.coeff E = 0) ∧
      picardNumber sX' ≤ picardNumber sX ∧
      (¬ IsRealFlipStep sX sZs sX' K B K' B' f fp → picardNumber sX' < picardNumber sX) := by
  obtain ⟨hnc, Kw', φ', hφ', hCV'⟩ := weakModel_step hS hZQ hgood hK hX' hstep
  obtain ⟨hXp, hXQ, hπ, hdim, hT, -⟩ := hgood
  obtain ⟨hX'p, hX'Q, hπ'⟩ := hX'
  have hgS := comp_eq_of_isStep hstep hπ
  have hfps : fp ≫ sZs = sX' := by rw [← hgS, ← Category.assoc, hstep.2.2.2.2.1, hπ']
  have hdim' : topologicalKrullDim X' = 3 :=
    (topologicalKrullDim_eq_of_isStep hstep hXp hX'p).trans hdim
  rcases hstep.2.2.2.2.2 with ⟨⟨hb, E, hE⟩, hiso, hK', hB'⟩ | hfl
  · haveI := hiso
    have hBE : B.coeff E = 0 := hnc E hE.ge
    have hT' : IsRealTerminalPair sX' B' := by
      rw [hB']
      have hX'v := hX'Q.1
      haveI : QuasiCompact sX' := hX'v.1.toQuasiCompact
      have hU : ∀ z : Zs, z ∈ biregularLocus fp := fun z =>
        le_biregularLocus ((isBiregular_top_iff fp).mpr inferInstance) trivial
      refine isRealTerminalPair_of_step hstep.2.2.2.1 hb (isBirationalMorphism_of_isIso fp)
        (fun P' => ((MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hU _)).trans
          P'.coheight_genericPoint).le) (fun z _ => hU z) hfps hK hK'
        (fun K'' _ => isRelativelyNef_of_isIso fp (isCartierCombination_of_isQFactorial_ph hX'Q _))
        (fun P hP => ?_) hT hXp hX'Q
      have hEP : E = P := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support
        (hE ▸ hP)
      rw [← hEP]; exact hBE
    have hlt := picardNumber_lt_of_isStep hS hstep hXp hπ hX'p hπ' ⟨⟨hb, E, hE⟩, hiso⟩
    exact ⟨⟨hX'p, hX'Q, hπ', hdim', hT', Kw', φ', hφ', hCV'⟩, hnc, hlt.le, fun _ => hlt⟩
  · have hT' : IsRealTerminalPair sX' B' :=
      isRealTerminalPair_of_isRealFlipStep hfl hK hT hXp hX'Q
    have heq := picardNumber_eq_of_isRealFlipStep hfl hXQ hXp hX'Q hX'p
    exact ⟨⟨hX'p, hX'Q, hπ', hdim', hT', Kw', φ', hφ', hCV'⟩, hnc, heq.le, fun h => absurd hfl h⟩

/-- **A non-nef good model admits a step.** The elementary step lemma contracts a negative
extremal ray; by the trichotomy the contraction is of fibre type, divisorial or small; fibre type
is excluded by the nef weak model; a divisorial contraction is followed by the identity of its
target and a small one by its real flip. -/
private theorem exists_isStep (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hZQ : IsQFactorial sZ)
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {πX : X ⟶ S} {K : Divisor X} {B : RDivisor X}
    (hgood : IsGood sS sZ πZ sX πX B) (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (hnef : ¬ IsRelativelyNef ℂ sX πX (logCanonicalDivisor K B)) :
    ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (_ : CompactSpace X') (_ : IsLocallyNoetherian X')
      (_ : IsNormal X') (sX' : X' ⟶ Spec (.of ℂ)) (πX' : X' ⟶ S) (K' : Divisor X')
      (B' : RDivisor X') (R : Set (RelativeNumericalCurveClasses sX πX)) (Zs : Scheme.{0})
      (sZs : Zs ⟶ Spec (.of ℂ)) (f : X ⟶ Zs) (g : Zs ⟶ S) (fp : X' ⟶ Zs),
      (MMP.Mori.IsProjectiveVariety ℂ sX' ∧ IsQFactorial sX' ∧ πX' ≫ sS = sX') ∧
        IsStep sX sX' sZs πX πX' K B K' B' R f g fp := by
  obtain ⟨hXp, hXQ, hπ, hdim, hT, Kw, φ, hφ, -⟩ := hgood
  have hXv := hXQ.1
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  have hB0 : 0 ≤ B := nonneg_of_isRealCanonicalPair hT.1
  have hklt := isRealKltPair_of_isRealTerminalPair hT
  obtain ⟨R, Zs, _, _, _, sZs, f, g, hR, hRneg, hcont, hZp, hneg, hdivQ, hsmall⟩ :=
    IsRealKltPair.exists_isRelativeContractionOfFace_of_not_isRelativelyNef hXp hS hπ hXQ hdim hK
      hB0 hklt hnef
  have hZv := hneg.isNormalVariety_target
  haveI : QuasiCompact sZs := hZv.1.toQuasiCompact
  haveI : CompactSpace Zs := QuasiCompact.compactSpace_of_compactSpace sZs
  have hfs : f ≫ sZs = sX := hneg.isContraction.comp_eq
  have hgS : g ≫ sS = sZs := comp_eq_of_isRelativeContractionOfFace hcont hneg hπ
  rcases trichotomy_of_isRelativeContractionOfFace hXp hXQ hS hZp hπ hR hcont hfs hZv with
    hfib | hdiv | hsm
  · exfalso
    obtain ⟨mw, hKw⟩ := hφ.isCanonicalDivisor
    obtain ⟨m, hKm⟩ := hK
    have hlin := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hXv hKw hKm
    haveI : IsSeparated sS := hS.toIsVariety.toIsSeparated
    exact (IsNefWeakModel.isNefWeakModel_of_negativeStep hφ hXQ hZQ).2 sZs g f
      (IsNegativeExtremalContraction.of_linearlyEquivalent hneg hlin) hcont.comp_eq hfib
  · obtain ⟨hZQ', -⟩ := hdivQ hdiv
    have hdZ : topologicalKrullDim Zs = 3 := by
      haveI : MMP.Mori.IsVariety ℂ sZs := hZv.1
      haveI : MMP.Mori.IsVariety ℂ sX := hXv.1
      rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZs sX hdiv.1, hdim]
    obtain ⟨K', hK'⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sZs hZv hdZ
    exact ⟨Zs, inferInstance, inferInstance, inferInstance, inferInstance, sZs, g, K',
      flipTransform f (𝟙 Zs) B, R, Zs, sZs, f, g, 𝟙 Zs, ⟨hZp, hZQ', hgS⟩, hR, hRneg, hcont, hneg,
      Category.id_comp g, Or.inl ⟨hdiv, inferInstance, ⟨3, hK'⟩, rfl⟩⟩
  · obtain ⟨X', _, _, _, _, sX', K', fp, hfl, hX'p, hX'Q, -, -⟩ := hsmall hsm
    have hfps : fp ≫ sZs = sX' := hfl.isSmall_flip.comp_eq
    exact ⟨X', inferInstance, inferInstance, inferInstance, inferInstance, sX', fp ≫ g, K',
      flipTransform f fp B, R, Zs, sZs, f, g, fp,
      ⟨hX'p, hX'Q, by rw [Category.assoc, hgS, hfps]⟩, hR, hRneg, hcont, hneg, rfl, Or.inr hfl⟩

/-- **The starting model is good.** -/
private theorem isGood_start (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hZQ : IsQFactorial sZ)
    {Y : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {π : Y ⟶ S} {K : Divisor Y} {C : RDivisor Y} {φ : Y.RationalMap Z}
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hπ : π ≫ sS = sY) (hYQ : IsQFactorial sY)
    (hdim : topologicalKrullDim Y = 3) (hC : IsRealTerminalPair sY C)
    (hZ : IsNefWeakModel sY sZ sS π πZ K C φ)
    (hcomp : ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z) (h : Y.RationalMap W),
      MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧ q ≫ sZ = sW ∧
        IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ IsBirationalMorphism p ∧
        IsBirationalMorphism q ∧ MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧
        h.compHom q = φ ∧
        ∃ GY GZ : RDivisor W,
          IsRCartierPullback p (logCanonicalDivisor K C) GY ∧
          IsRCartierPullback q
            (logCanonicalDivisor (RationalMap.transformDivisor φ K)
              (RationalMap.transformDivisor φ C)) GZ ∧
          ∀ P : MMP.Mori.PrimeDivisor Y, 0 < C.coeff P →
            ∀ P' : MMP.Mori.PrimeDivisor W, RationalMap.transformPrimeDivisor h P = some P' →
              (GY - GZ).coeff P' = 0) :
    IsGood sS sZ πZ sY π C := by
  refine ⟨hY, hYQ, hπ, hdim, hC, K, φ, hZ, fun G hG => ?_⟩
  obtain ⟨W, _, _, _, sW, p, q, h, hW, hWs, hpY, hqZ, hp, hq, hpb, hqb, hinv, hhq, GY, GZ, hGY, hGZ,
    h0⟩ := hcomp
  have hYv := hZ.isNormalVariety_source
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hp
  haveI : IsSeparated sY := hYv.1.toIsSeparated
  haveI : IsSeparated sW := hW.toIsSeparated
  haveI : IsSeparated p := by subst hpY; exact IsSeparated.of_comp p sY
  have hYsep := isSeparated_toTerminal_of_isNormalVariety hYv
  have hWsep : IsSeparated (W ↘ CategoryTheory.Limits.terminal Scheme) := by
    rw [show (W ↘ CategoryTheory.Limits.terminal Scheme) =
      sW ≫ (Spec (.of ℂ) ↘ CategoryTheory.Limits.terminal Scheme) from
        CategoryTheory.Limits.terminal.hom_ext _ _]
    infer_instance
  obtain ⟨P, hP, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hYv
    (by rw [hpY]; exact ⟨hW, inferInstance⟩) hpb G
  refine ⟨W, inferInstance, inferInstance, inferInstance, sW, p, q, h, GY, GZ, P, hW, hpY, hqZ, hp,
    hq, hpb, hqb, hinv, hhq, hGY, hGZ,
    (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p P G).mpr hP, h0 G hG P ?_⟩
  exact transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq hYv p (hpY ▸ hW) hpb hinv hP

/-- **No infinite flip tail.** An infinite sequence of real flip steps through good models over
`S` is impossible. -/
private theorem false_of_forall_isRealFlipStep (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    {Y : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {π : Y ⟶ S} {K : Divisor Y} {C : RDivisor Y}
    (Yi : ℕ → Scheme.{0}) (sYi : ∀ i, Yi i ⟶ Spec (.of ℂ))
    [∀ i, IsIntegral (Yi i)] [∀ i, CompactSpace (Yi i)] [∀ i, IsLocallyNoetherian (Yi i)]
    [∀ i, IsNormal (Yi i)] (πY : ∀ i, Yi i ⟶ S) (KY : ∀ i, Divisor (Yi i))
    (CY : ∀ i, RDivisor (Yi i))
    (R : ∀ i, Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap π πY i)))
    (Zi : ℕ → Scheme.{0}) (sZi : ∀ i, Zi i ⟶ Spec (.of ℂ)) (f : ∀ i, modelSeq Y Yi i ⟶ Zi i)
    (g : ∀ i, Zi i ⟶ S) (fp : ∀ i, Yi i ⟶ Zi i) (N : ℕ)
    (hgood : ∀ i, IsGood sS sZ πZ (modelStr sY sYi i) (modelMap π πY i) (divisorSeq C CY i))
    (hstep : ∀ i, IsStep (modelStr sY sYi i) (sYi i) (sZi i) (modelMap π πY i) (πY i)
      (divisorSeq K KY i) (divisorSeq C CY i) (KY i) (CY i) (R i) (f i) (g i) (fp i))
    (hflip : ∀ i, N ≤ i → IsRealFlipStep (modelStr sY sYi i) (sZi i) (sYi i)
      (divisorSeq K KY i) (divisorSeq C CY i) (KY i) (CY i) (f i) (fp i)) :
    False := by
  have hZp : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sZi i) := fun i =>
    isProjectiveVariety_target_of_isStep hS (hstep i) (hgood i).2.2.1
  let fσ : ∀ i, modelSeq (Yi N) (fun i => Yi (N + 1 + i)) i ⟶ Zi (N + 1 + i) := fun i =>
    match i with
    | 0 => f (N + 1)
    | j + 1 => f (N + 1 + (j + 1))
  let σ : RealFlipSequence (sYi N) (KY N) (CY N) :=
    { n := ⊤
      Y := fun i => Yi (N + 1 + i)
      sY := fun i => sYi (N + 1 + i)
      KY := fun i => KY (N + 1 + i)
      BY := fun i => CY (N + 1 + i)
      Z := fun i => Zi (N + 1 + i)
      sZ := fun i => sZi (N + 1 + i)
      f := fσ
      fp := fun i => fp (N + 1 + i)
      isCanonicalDivisor := (hflip N le_rfl).isCanonicalDivisor_flip
      isQFactorial := fun i _ => by
        cases i with
        | zero => exact (hgood (N + 1)).2.1
        | succ j => exact (hgood (N + 1 + (j + 1))).2.1
      isQuasiProjectiveVariety := fun i _ => by
        cases i with
        | zero =>
          exact @AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ _ _ _
            (hgood (N + 1)).1
        | succ j =>
          exact @AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ _ _ _
            (hgood (N + 1 + (j + 1))).1
      dim_eq := fun i _ => by
        cases i with
        | zero => exact (hgood (N + 1)).2.2.2.1
        | succ j => exact (hgood (N + 1 + (j + 1))).2.2.2.1
      isRealFlipStep := fun i _ => by
        cases i with
        | zero => exact hflip (N + 1) (by omega)
        | succ j => exact hflip (N + 1 + (j + 1)) (by omega) }
  refine RealFlipSequence.n_ne_top_of_isRealCanonicalPair σ (fun i _ => ?_) (fun i _ => ?_)
    (fun i _ => hZp (N + 1 + i)) rfl
  · cases i with
    | zero => exact (hgood (N + 1)).2.2.2.2.1.1
    | succ j => exact (hgood (N + 1 + (j + 1))).2.2.2.2.1.1
  · cases i with
    | zero => exact (hgood (N + 1)).1
    | succ j => exact (hgood (N + 1 + (j + 1))).1

private theorem solution
    {Y S Z : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sY : Y ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [QuasiCompact sZ]
    {π : Y ⟶ S} {πZ : Z ⟶ S} {K : Divisor Y} {C : RDivisor Y} {φ : Y.RationalMap Z}
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hπ : π ≫ sS = sY) (hYQ : IsQFactorial sY) (hdim : topologicalKrullDim Y = 3)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sY n) (hC : IsRealTerminalPair sY C)
    (hZ : IsNefWeakModel sY sZ sS π πZ K C φ) (hZQ : IsQFactorial sZ)
    (hcomp : ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z) (h : Y.RationalMap W),
      MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧ q ≫ sZ = sW ∧
        IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ IsBirationalMorphism p ∧
        IsBirationalMorphism q ∧ MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧
        h.compHom q = φ ∧
        ∃ GY GZ : RDivisor W,
          IsRCartierPullback p (logCanonicalDivisor K C) GY ∧
          IsRCartierPullback q
            (logCanonicalDivisor (RationalMap.transformDivisor φ K)
              (RationalMap.transformDivisor φ C)) GZ ∧
          ∀ P : MMP.Mori.PrimeDivisor Y, 0 < C.coeff P →
            ∀ P' : MMP.Mori.PrimeDivisor W, RationalMap.transformPrimeDivisor h P = some P' →
              (GY - GZ).coeff P' = 0) :
    (∀ (n : ℕ∞) (Yi : ℕ → Scheme.{0}) (sYi : ∀ i, Yi i ⟶ Spec (.of ℂ))
      [∀ i, IsIntegral (Yi i)] [∀ i, CompactSpace (Yi i)] [∀ i, IsLocallyNoetherian (Yi i)]
      [∀ i, IsNormal (Yi i)] (πY : ∀ i, Yi i ⟶ S) (KY : ∀ i, Divisor (Yi i))
      (CY : ∀ i, RDivisor (Yi i))
      (R : ∀ i, Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap π πY i)))
      (Zi : ℕ → Scheme.{0}) (sZi : ∀ i, Zi i ⟶ Spec (.of ℂ)) (f : ∀ i, modelSeq Y Yi i ⟶ Zi i)
      (g : ∀ i, Zi i ⟶ S) (fp : ∀ i, Yi i ⟶ Zi i),
      (∀ i : ℕ, (i : ℕ∞) ≤ n →
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sY sYi i) ∧ IsQFactorial (modelStr sY sYi i) ∧
          modelMap π πY i ≫ sS = modelStr sY sYi i) →
      (∀ i : ℕ, (i : ℕ∞) < n →
        IsExtremalRay ℝ (relativeClosedConeOfCurves (modelStr sY sYi i) (modelMap π πY i) :
            Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap π πY i))) (R i) ∧
          (∀ (Γ : ProperCurve (modelStr sY sYi i)) (hΓ : Γ.IsContractedBy (modelMap π πY i)),
            Γ.relativeClass (modelMap π πY i) hΓ ∈ R i →
            ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor (modelSeq Y Yi i)) (x : ℝ),
              IsRIntersectionNumber ℂ (modelStr sY sYi i)
                (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq C CY i)) r L Γ x → x < 0) ∧
          IsRelativeContractionOfFace (modelMap π πY i) (R i) (f i) (g i) ∧
          IsNegativeExtremalContraction ℂ (modelStr sY sYi i) (sZi i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq C CY i)) (f i) ∧
          fp i ≫ g i = πY i ∧
          (((IsBirationalMorphism (f i) ∧ ∃ E : MMP.Mori.PrimeDivisor (modelSeq Y Yi i),
                (MMP.Mori.exceptionalSet (f i) : Set (modelSeq Y Yi i)) = E.support) ∧
              IsIso (fp i) ∧ (∃ m : ℕ, (KY i).IsCanonicalDivisor (sYi i) m) ∧
              CY i = flipTransform (f i) (fp i) (divisorSeq C CY i)) ∨
            IsRealFlipStep (modelStr sY sYi i) (sZi i) (sYi i) (divisorSeq K KY i)
              (divisorSeq C CY i) (KY i) (CY i) (f i) (fp i))) →
      n ≠ ⊤ ∧
        (∀ i : ℕ, (i : ℕ∞) ≤ n → IsRealTerminalPair (modelStr sY sYi i) (divisorSeq C CY i)) ∧
        ∀ i : ℕ, (i : ℕ∞) < n → ∀ E : MMP.Mori.PrimeDivisor (modelSeq Y Yi i),
          (E.support : Set (modelSeq Y Yi i)) ⊆ MMP.Mori.exceptionalSet (f i) →
            (divisorSeq C CY i).coeff E = 0) ∧
    ∃ (n : ℕ) (Yi : ℕ → Scheme.{0}) (sYi : ∀ i, Yi i ⟶ Spec (.of ℂ))
      (_ : ∀ i, IsIntegral (Yi i)) (_ : ∀ i, CompactSpace (Yi i))
      (_ : ∀ i, IsLocallyNoetherian (Yi i)) (_ : ∀ i, IsNormal (Yi i)) (πY : ∀ i, Yi i ⟶ S)
      (KY : ∀ i, Divisor (Yi i)) (CY : ∀ i, RDivisor (Yi i))
      (R : ∀ i, Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap π πY i)))
      (Zi : ℕ → Scheme.{0}) (sZi : ∀ i, Zi i ⟶ Spec (.of ℂ)) (f : ∀ i, modelSeq Y Yi i ⟶ Zi i)
      (g : ∀ i, Zi i ⟶ S) (fp : ∀ i, Yi i ⟶ Zi i),
      (∀ i ≤ n,
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sY sYi i) ∧ IsQFactorial (modelStr sY sYi i) ∧
          modelMap π πY i ≫ sS = modelStr sY sYi i) ∧
      (∀ i < n,
        IsExtremalRay ℝ (relativeClosedConeOfCurves (modelStr sY sYi i) (modelMap π πY i) :
            Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap π πY i))) (R i) ∧
          (∀ (Γ : ProperCurve (modelStr sY sYi i)) (hΓ : Γ.IsContractedBy (modelMap π πY i)),
            Γ.relativeClass (modelMap π πY i) hΓ ∈ R i →
            ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor (modelSeq Y Yi i)) (x : ℝ),
              IsRIntersectionNumber ℂ (modelStr sY sYi i)
                (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq C CY i)) r L Γ x → x < 0) ∧
          IsRelativeContractionOfFace (modelMap π πY i) (R i) (f i) (g i) ∧
          IsNegativeExtremalContraction ℂ (modelStr sY sYi i) (sZi i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq C CY i)) (f i) ∧
          fp i ≫ g i = πY i ∧
          (((IsBirationalMorphism (f i) ∧ ∃ E : MMP.Mori.PrimeDivisor (modelSeq Y Yi i),
                (MMP.Mori.exceptionalSet (f i) : Set (modelSeq Y Yi i)) = E.support) ∧
              IsIso (fp i) ∧ (∃ m : ℕ, (KY i).IsCanonicalDivisor (sYi i) m) ∧
              CY i = flipTransform (f i) (fp i) (divisorSeq C CY i)) ∨
            IsRealFlipStep (modelStr sY sYi i) (sZi i) (sYi i) (divisorSeq K KY i)
              (divisorSeq C CY i) (KY i) (CY i) (f i) (fp i))) ∧
      IsRelativelyNef ℂ (modelStr sY sYi n) (modelMap π πY n)
        (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq C CY n)) := by
  have hgood0 : IsGood sS sZ πZ sY π C := isGood_start hS hZQ hY hπ hYQ hdim hC hZ hcomp
  have huniv : ∀ (n : ℕ∞) (Yi : ℕ → Scheme.{0}) (sYi : ∀ i, Yi i ⟶ Spec (.of ℂ))
      [∀ i, IsIntegral (Yi i)] [∀ i, CompactSpace (Yi i)] [∀ i, IsLocallyNoetherian (Yi i)]
      [∀ i, IsNormal (Yi i)] (πY : ∀ i, Yi i ⟶ S) (KY : ∀ i, Divisor (Yi i))
      (CY : ∀ i, RDivisor (Yi i))
      (R : ∀ i, Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap π πY i)))
      (Zi : ℕ → Scheme.{0}) (sZi : ∀ i, Zi i ⟶ Spec (.of ℂ)) (f : ∀ i, modelSeq Y Yi i ⟶ Zi i)
      (g : ∀ i, Zi i ⟶ S) (fp : ∀ i, Yi i ⟶ Zi i),
      (∀ i : ℕ, (i : ℕ∞) ≤ n →
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sY sYi i) ∧ IsQFactorial (modelStr sY sYi i) ∧
          modelMap π πY i ≫ sS = modelStr sY sYi i) →
      (∀ i : ℕ, (i : ℕ∞) < n → IsStep (modelStr sY sYi i) (sYi i) (sZi i) (modelMap π πY i)
        (πY i) (divisorSeq K KY i) (divisorSeq C CY i) (KY i) (CY i) (R i) (f i) (g i) (fp i)) →
      n ≠ ⊤ ∧
        (∀ i : ℕ, (i : ℕ∞) ≤ n → IsGood sS sZ πZ (modelStr sY sYi i) (modelMap π πY i)
          (divisorSeq C CY i)) ∧
        ∀ i : ℕ, (i : ℕ∞) < n → ∀ E : MMP.Mori.PrimeDivisor (modelSeq Y Yi i),
          (E.support : Set (modelSeq Y Yi i)) ⊆ MMP.Mori.exceptionalSet (f i) →
            (divisorSeq C CY i).coeff E = 0 := by
    intro n Yi sYi _ _ _ _ πY KY CY R Zi sZi f g fp h1 h2
    have hKi : ∀ i : ℕ, (i : ℕ∞) ≤ n →
        ∃ m, MMP.Mori.Divisor.IsCanonicalDivisor (modelStr sY sYi i) m (divisorSeq K KY i) := by
      intro i hi
      cases i with
      | zero => exact hK
      | succ i =>
        have hlt : (i : ℕ∞) < n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self i) hi
        rcases (h2 i hlt).2.2.2.2.2 with ⟨_, _, hm, _⟩ | hfl
        · exact hm
        · exact hfl.isCanonicalDivisor_flip
    have hgoodi : ∀ i : ℕ, (i : ℕ∞) ≤ n →
        IsGood sS sZ πZ (modelStr sY sYi i) (modelMap π πY i) (divisorSeq C CY i) := by
      intro i
      induction i with
      | zero => intro _; exact hgood0
      | succ i ih =>
        intro hi
        have hlt : (i : ℕ∞) < n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self i) hi
        exact (isGood_step hS hZQ (ih hlt.le) (hKi i hlt.le) (h1 (i + 1) hi) (h2 i hlt)).1
    have hsteps : ∀ i : ℕ, (i : ℕ∞) < n → _ := fun i hi =>
      isGood_step hS hZQ (hgoodi i hi.le) (hKi i hi.le) (h1 (i + 1) (Order.add_one_le_of_lt hi))
        (h2 i hi)
    refine ⟨?_, hgoodi, fun i hi => (hsteps i hi).2.1⟩
    intro hn
    subst hn
    have hlt : ∀ i : ℕ, (i : ℕ∞) < ⊤ := fun i => ENat.coe_lt_top i
    let ρ : ℕ → ℕ∞ := fun i => picardNumber (modelStr sY sYi i)
    have hanti : ∀ i, ρ (i + 1) ≤ ρ i := fun i => (hsteps i (hlt i)).2.2.1
    have hstrict : ∀ i, ¬ IsRealFlipStep (modelStr sY sYi i) (sZi i) (sYi i)
        (divisorSeq K KY i) (divisorSeq C CY i) (KY i) (CY i) (f i) (fp i) → ρ (i + 1) < ρ i :=
      fun i => (hsteps i (hlt i)).2.2.2
    have h0 : ρ 0 < ⊤ := by
      haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sY := hY
      exact MMP.Mori.picardNumber_lt_top_of_isProjectiveVariety sY
    have hle0 : ∀ i, ρ i ≤ ρ 0 := by
      intro i
      induction i with
      | zero => exact le_rfl
      | succ i ih => exact (hanti i).trans ih
    have hfin : ∀ i, ρ i ≠ ⊤ := fun i => ((hle0 i).trans_lt h0).ne
    let d : ℕ → ℕ := fun i => (ρ i).toNat
    have hd : ∀ i, (d i : ℕ∞) = ρ i := fun i => ENat.coe_toNat (hfin i)
    have hdanti : Antitone d := antitone_nat_of_succ_le fun i => by
      have := hanti i
      rw [← hd, ← hd] at this
      exact_mod_cast this
    obtain ⟨N, hN⟩ : ∃ N, ∀ i, d N ≤ d i := ⟨Function.argmin d, fun i => Function.argmin_le d i⟩
    refine false_of_forall_isRealFlipStep hS Yi sYi πY KY CY R Zi sZi f g fp N
      (fun i => hgoodi i le_top) (fun i => h2 i (hlt i)) fun i hi => ?_
    by_contra hnot
    have h := hstrict i hnot
    rw [← hd, ← hd] at h
    have h' : d (i + 1) < d i := by exact_mod_cast h
    have := hN (i + 1)
    have := hdanti hi
    omega
  refine ⟨fun n Yi sYi _ _ _ _ πY KY CY R Zi sZi f g fp h1 h2 => ?_, ?_⟩
  · obtain ⟨hn, hg, hE⟩ := huniv n Yi sYi πY KY CY R Zi sZi f g fp h1 h2
    exact ⟨hn, fun i hi => (hg i hi).2.2.2.2.1, hE⟩
  · classical
    let s0 : Stage S := ⟨Y, sY, π, K, C⟩
    let Pr : Stage S → Prop := fun s =>
      IsGood sS sZ πZ s.sX s.πX s.B ∧ ∃ m : ℕ, s.K.IsCanonicalDivisor s.sX m
    let cond : Stage S → Prop := fun s =>
      Pr s ∧ ¬ IsRelativelyNef ℂ s.sX s.πX (logCanonicalDivisor s.K s.B)
    let Q : (s : Stage S) → StepData s → Prop := fun s d =>
      (MMP.Mori.IsProjectiveVariety ℂ d.t.sX ∧ IsQFactorial d.t.sX ∧ d.t.πX ≫ sS = d.t.sX) ∧
        IsStep s.sX d.t.sX d.sZs s.πX d.t.πX s.K s.B d.t.K d.t.B d.R d.f d.g d.fp
    have hex : ∀ s : Stage S, cond s → ∃ d : StepData s, Q s d := by
      rintro s ⟨hs, hnef⟩
      obtain ⟨X', _, _, _, _, sX', πX', K', B', R, Zs, sZs, f, g, fp, hX', hst⟩ :=
        exists_isStep hS hZQ hs.1 hs.2 hnef
      exact ⟨⟨⟨X', sX', πX', K', B'⟩, R, Zs, sZs, f, g, fp⟩, hX', hst⟩
    let next : (s : Stage S) → StepData s := fun s =>
      if h : cond s then (hex s h).choose else ⟨s, ∅, S, sS, s.πX, 𝟙 S, s.πX⟩
    have hnext : ∀ s : Stage S, cond s → Q s (next s) := by
      intro s h
      simp only [next, dif_pos h]
      exact (hex s h).choose_spec
    have hnext' : ∀ s : Stage S, ¬ cond s → (next s).t = s := by
      intro s h
      simp only [next, dif_neg h]
    have hPr : ∀ i, Pr (Stage.seq s0 next i) := by
      intro i
      induction i with
      | zero => exact ⟨hgood0, hK⟩
      | succ i ih =>
        change Pr (next (Stage.seq s0 next i)).t
        by_cases hc : cond (Stage.seq s0 next i)
        · obtain ⟨hX', hst⟩ := hnext _ hc
          refine ⟨(isGood_step hS hZQ ih.1 ih.2 hX' hst).1, ?_⟩
          rcases hst.2.2.2.2.2 with ⟨_, _, hm, _⟩ | hfl
          · exact hm
          · exact hfl.isCanonicalDivisor_flip
        · rw [hnext' _ hc]
          exact ih
    have hmod : ∀ i : ℕ,
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sY (fun j => (Stage.seq s0 next (j + 1)).sX) i) ∧
        IsQFactorial (modelStr sY (fun j => (Stage.seq s0 next (j + 1)).sX) i) ∧
        modelMap π (fun j => (Stage.seq s0 next (j + 1)).πX) i ≫ sS =
          modelStr sY (fun j => (Stage.seq s0 next (j + 1)).sX) i := by
      intro i
      cases i with
      | zero => exact ⟨hgood0.1, hgood0.2.1, hgood0.2.2.1⟩
      | succ i => exact ⟨(hPr (i + 1)).1.1, (hPr (i + 1)).1.2.1, (hPr (i + 1)).1.2.2.1⟩
    have hstepi : ∀ i : ℕ, cond (Stage.seq s0 next i) →
        IsStep (modelStr sY (fun j => (Stage.seq s0 next (j + 1)).sX) i)
          (Stage.seq s0 next (i + 1)).sX (next (Stage.seq s0 next i)).sZs
          (modelMap π (fun j => (Stage.seq s0 next (j + 1)).πX) i)
          (Stage.seq s0 next (i + 1)).πX
          (divisorSeq K (fun j => (Stage.seq s0 next (j + 1)).K) i)
          (divisorSeq C (fun j => (Stage.seq s0 next (j + 1)).B) i)
          (Stage.seq s0 next (i + 1)).K (Stage.seq s0 next (i + 1)).B
          (Stage.progR s0 next i) (Stage.progF s0 next i) (next (Stage.seq s0 next i)).g
          (next (Stage.seq s0 next i)).fp := by
      intro i hi
      have h := (hnext _ hi).2
      cases i with
      | zero => exact h
      | succ i => exact h
    have hnefi : ∀ i : ℕ, IsRelativelyNef ℂ (Stage.seq s0 next i).sX (Stage.seq s0 next i).πX
        (logCanonicalDivisor (Stage.seq s0 next i).K (Stage.seq s0 next i).B) →
        IsRelativelyNef ℂ (modelStr sY (fun j => (Stage.seq s0 next (j + 1)).sX) i)
          (modelMap π (fun j => (Stage.seq s0 next (j + 1)).πX) i)
          (logCanonicalDivisor (divisorSeq K (fun j => (Stage.seq s0 next (j + 1)).K) i)
            (divisorSeq C (fun j => (Stage.seq s0 next (j + 1)).B) i)) := by
      intro i hi
      cases i with
      | zero => exact hi
      | succ i => exact hi
    have hfin : ∃ i, IsRelativelyNef ℂ (Stage.seq s0 next i).sX (Stage.seq s0 next i).πX
        (logCanonicalDivisor (Stage.seq s0 next i).K (Stage.seq s0 next i).B) := by
      by_contra hno
      simp only [not_exists] at hno
      exact (huniv ⊤ (fun j => (Stage.seq s0 next (j + 1)).X)
        (fun j => (Stage.seq s0 next (j + 1)).sX) (fun j => (Stage.seq s0 next (j + 1)).πX)
        (fun j => (Stage.seq s0 next (j + 1)).K) (fun j => (Stage.seq s0 next (j + 1)).B)
        (Stage.progR s0 next) (fun i => (next (Stage.seq s0 next i)).Zs)
        (fun i => (next (Stage.seq s0 next i)).sZs) (Stage.progF s0 next)
        (fun i => (next (Stage.seq s0 next i)).g) (fun i => (next (Stage.seq s0 next i)).fp)
        (fun i _ => hmod i) (fun i _ => hstepi i ⟨hPr i, hno i⟩)).1 rfl
    refine ⟨Nat.find hfin, fun j => (Stage.seq s0 next (j + 1)).X,
      fun j => (Stage.seq s0 next (j + 1)).sX, fun i => inferInstance, fun i => inferInstance,
      fun i => inferInstance, fun i => inferInstance, fun j => (Stage.seq s0 next (j + 1)).πX,
      fun j => (Stage.seq s0 next (j + 1)).K, fun j => (Stage.seq s0 next (j + 1)).B,
      Stage.progR s0 next, fun i => (next (Stage.seq s0 next i)).Zs,
      fun i => (next (Stage.seq s0 next i)).sZs, Stage.progF s0 next,
      fun i => (next (Stage.seq s0 next i)).g, fun i => (next (Stage.seq s0 next i)).fp,
      fun i _ => hmod i, fun i hi => hstepi i ⟨hPr i, Nat.find_min hfin hi⟩,
      hnefi _ (Nat.find_spec hfin)⟩

end

end Proof_lem_fourfold_terminal_comparison_program

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Terminal comparison programs terminate.** Let `π : Y ⟶ S` be a morphism of projective
complex varieties, `Y` a `ℚ`-factorial threefold with canonical divisor `K`, and `(Y, C)` a real
terminal pair with a `ℚ`-factorial nef weak model `φ : Y ⤏ Z` over `S` whose comparison has
coefficient zero along every prime divisor with positive coefficient in `C`. Then every
`(K + C)`-program over `S` from `(Y, C)` (divisorial contractions and real flips of negative
extremal rays of `NE̅(Y_i/S)`) is finite, contracts no prime with positive boundary coefficient,
and passes only through real terminal pairs; and some such program ends with `K_n + C_n` nef over
`S`. -/
@[mmp "lem_fourfold_terminal_comparison_program"]
public theorem IsRealTerminalPair.terminates_of_isNefWeakModel
    {Y S Z : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sY : Y ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [QuasiCompact sZ]
    {π : Y ⟶ S} {πZ : Z ⟶ S} {K : Divisor Y} {C : RDivisor Y} {φ : Y.RationalMap Z}
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hπ : π ≫ sS = sY) (hYQ : IsQFactorial sY) (hdim : topologicalKrullDim Y = 3)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sY n) (hC : IsRealTerminalPair sY C)
    (hZ : IsNefWeakModel sY sZ sS π πZ K C φ) (hZQ : IsQFactorial sZ)
    (hcomp : ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z) (h : Y.RationalMap W),
      MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧ q ≫ sZ = sW ∧
        IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ IsBirationalMorphism p ∧
        IsBirationalMorphism q ∧ MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧
        h.compHom q = φ ∧
        ∃ GY GZ : RDivisor W,
          IsRCartierPullback p (logCanonicalDivisor K C) GY ∧
          IsRCartierPullback q
            (logCanonicalDivisor (RationalMap.transformDivisor φ K)
              (RationalMap.transformDivisor φ C)) GZ ∧
          ∀ P : MMP.Mori.PrimeDivisor Y, 0 < C.coeff P →
            ∀ P' : MMP.Mori.PrimeDivisor W, RationalMap.transformPrimeDivisor h P = some P' →
              (GY - GZ).coeff P' = 0) :
    (∀ (n : ℕ∞) (Yi : ℕ → Scheme.{0}) (sYi : ∀ i, Yi i ⟶ Spec (.of ℂ))
      [∀ i, IsIntegral (Yi i)] [∀ i, CompactSpace (Yi i)] [∀ i, IsLocallyNoetherian (Yi i)]
      [∀ i, IsNormal (Yi i)] (πY : ∀ i, Yi i ⟶ S) (KY : ∀ i, Divisor (Yi i))
      (CY : ∀ i, RDivisor (Yi i))
      (R : ∀ i, Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap π πY i)))
      (Zi : ℕ → Scheme.{0}) (sZi : ∀ i, Zi i ⟶ Spec (.of ℂ)) (f : ∀ i, modelSeq Y Yi i ⟶ Zi i)
      (g : ∀ i, Zi i ⟶ S) (fp : ∀ i, Yi i ⟶ Zi i),
      (∀ i : ℕ, (i : ℕ∞) ≤ n →
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sY sYi i) ∧ IsQFactorial (modelStr sY sYi i) ∧
          modelMap π πY i ≫ sS = modelStr sY sYi i) →
      (∀ i : ℕ, (i : ℕ∞) < n →
        IsExtremalRay ℝ (relativeClosedConeOfCurves (modelStr sY sYi i) (modelMap π πY i) :
            Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap π πY i))) (R i) ∧
          (∀ (Γ : ProperCurve (modelStr sY sYi i)) (hΓ : Γ.IsContractedBy (modelMap π πY i)),
            Γ.relativeClass (modelMap π πY i) hΓ ∈ R i →
            ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor (modelSeq Y Yi i)) (x : ℝ),
              IsRIntersectionNumber ℂ (modelStr sY sYi i)
                (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq C CY i)) r L Γ x → x < 0) ∧
          IsRelativeContractionOfFace (modelMap π πY i) (R i) (f i) (g i) ∧
          IsNegativeExtremalContraction ℂ (modelStr sY sYi i) (sZi i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq C CY i)) (f i) ∧
          fp i ≫ g i = πY i ∧
          (((IsBirationalMorphism (f i) ∧ ∃ E : MMP.Mori.PrimeDivisor (modelSeq Y Yi i),
                (MMP.Mori.exceptionalSet (f i) : Set (modelSeq Y Yi i)) = E.support) ∧
              IsIso (fp i) ∧ (∃ m : ℕ, (KY i).IsCanonicalDivisor (sYi i) m) ∧
              CY i = flipTransform (f i) (fp i) (divisorSeq C CY i)) ∨
            IsRealFlipStep (modelStr sY sYi i) (sZi i) (sYi i) (divisorSeq K KY i)
              (divisorSeq C CY i) (KY i) (CY i) (f i) (fp i))) →
      n ≠ ⊤ ∧
        (∀ i : ℕ, (i : ℕ∞) ≤ n → IsRealTerminalPair (modelStr sY sYi i) (divisorSeq C CY i)) ∧
        ∀ i : ℕ, (i : ℕ∞) < n → ∀ E : MMP.Mori.PrimeDivisor (modelSeq Y Yi i),
          (E.support : Set (modelSeq Y Yi i)) ⊆ MMP.Mori.exceptionalSet (f i) →
            (divisorSeq C CY i).coeff E = 0) ∧
    ∃ (n : ℕ) (Yi : ℕ → Scheme.{0}) (sYi : ∀ i, Yi i ⟶ Spec (.of ℂ))
      (_ : ∀ i, IsIntegral (Yi i)) (_ : ∀ i, CompactSpace (Yi i))
      (_ : ∀ i, IsLocallyNoetherian (Yi i)) (_ : ∀ i, IsNormal (Yi i)) (πY : ∀ i, Yi i ⟶ S)
      (KY : ∀ i, Divisor (Yi i)) (CY : ∀ i, RDivisor (Yi i))
      (R : ∀ i, Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap π πY i)))
      (Zi : ℕ → Scheme.{0}) (sZi : ∀ i, Zi i ⟶ Spec (.of ℂ)) (f : ∀ i, modelSeq Y Yi i ⟶ Zi i)
      (g : ∀ i, Zi i ⟶ S) (fp : ∀ i, Yi i ⟶ Zi i),
      (∀ i ≤ n,
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sY sYi i) ∧ IsQFactorial (modelStr sY sYi i) ∧
          modelMap π πY i ≫ sS = modelStr sY sYi i) ∧
      (∀ i < n,
        IsExtremalRay ℝ (relativeClosedConeOfCurves (modelStr sY sYi i) (modelMap π πY i) :
            Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap π πY i))) (R i) ∧
          (∀ (Γ : ProperCurve (modelStr sY sYi i)) (hΓ : Γ.IsContractedBy (modelMap π πY i)),
            Γ.relativeClass (modelMap π πY i) hΓ ∈ R i →
            ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor (modelSeq Y Yi i)) (x : ℝ),
              IsRIntersectionNumber ℂ (modelStr sY sYi i)
                (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq C CY i)) r L Γ x → x < 0) ∧
          IsRelativeContractionOfFace (modelMap π πY i) (R i) (f i) (g i) ∧
          IsNegativeExtremalContraction ℂ (modelStr sY sYi i) (sZi i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq C CY i)) (f i) ∧
          fp i ≫ g i = πY i ∧
          (((IsBirationalMorphism (f i) ∧ ∃ E : MMP.Mori.PrimeDivisor (modelSeq Y Yi i),
                (MMP.Mori.exceptionalSet (f i) : Set (modelSeq Y Yi i)) = E.support) ∧
              IsIso (fp i) ∧ (∃ m : ℕ, (KY i).IsCanonicalDivisor (sYi i) m) ∧
              CY i = flipTransform (f i) (fp i) (divisorSeq C CY i)) ∨
            IsRealFlipStep (modelStr sY sYi i) (sZi i) (sYi i) (divisorSeq K KY i)
              (divisorSeq C CY i) (KY i) (CY i) (f i) (fp i))) ∧
      IsRelativelyNef ℂ (modelStr sY sYi n) (modelMap π πY n)
        (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq C CY n)) :=
          by
            revert Y S Z sY sS sZ π πZ K C φ hY hS hπ hYQ hdim hK hC hZ hZQ hcomp
            exact Proof_lem_fourfold_terminal_comparison_program.solution

end MMP.Fourfold
