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
import MMP.AlgebraicGeometry.MMP.Termination.RealCanonicalDifficulty
import MMP.AlgebraicGeometry.MMP.MinimalModel.RealKltCompactification
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.AlgebraicGeometry.MMP.Contraction.ExtremalContractionTrichotomy
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
import MMP.AlgebraicGeometry.Morphisms.VarietyFibreDimension
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Intersection.SmallModificationPicardNumber
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleBasics
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonEquality
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DivisorOverRealization
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.MMP.ConeTheorem.SupportingDivisorStein
import MMP.AlgebraicGeometry.MMP.Flip.SmallAmpleModel
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Resolution.StratumBlowupRelativelyAmple
import MMP.AlgebraicGeometry.Singularities.PltTerminalRestriction
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.MMP.Flip.RealCanonicalRationalWitness
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Making a terminal limit nef without losing its support

Let `π : Y ⟶ S` be a morphism of projective complex varieties, with `Y` a `ℚ`-factorial
threefold with canonical divisor `K`. Let `C_i` be real terminal boundaries on `Y`, all with the
same finite positive support `F`, whose coefficients converge to those of a real terminal
boundary `B`. Suppose each `(Y, C_i)` has a `ℚ`-factorial nef weak model `φ_i : Y ⤏ Z_i` over `S`
whose comparison `p^*(K + C_i) - q^*(K_{Z_i} + (φ_i)_* C_i)` has coefficient zero along every prime
of `F`.

Then there is a finite `(K + B)`-program over `S` from `(Y, B)` — divisorial contractions of
`(K_j + B_j)`-negative extremal rays of `NE̅(Y_j/S)` and real flips of the small contractions of
such rays, through projective `ℚ`-factorial models over `S` — ending with `K_n + B_n` nef over `S`,
and an index `N` such that for every `i ≥ N` all the hypotheses persist on `Y_n`: `B_n` and the
transforms `C_{i,n}` are real terminal, the `C_{i,n}` have one common finite positive support and
converge to `B_n`, and `Z_i` is a nef weak model of `(Y_n, C_{i,n})` through the transported map
`Y_n ⤏ Y ⤏ Z_i` with vanishing comparison coefficients on that support; moreover no step of the
program contracts a prime with positive coefficient in `C_i`, i.e. no prime of `F`.

## Main results

* `MMP.Fourfold.IsRealTerminalPair.exists_isRelativelyNef_of_tendsto_of_isNefWeakModel`.

## Implementation notes

The program is spelled out as data, exactly as in
`MMP.Fourfold.IsRealTerminalPair.terminates_of_isNefWeakModel`: models `Y₀ = Y`, `Y_{j+1} = Yi j`
over `S`, and for `j < n` a negative extremal ray `R_j` with its contraction `f_j : Y_j ⟶ Z'_j`
over `S` followed by `f_j⁺ : Y_{j+1} ⟶ Z'_j`, an isomorphism (divisorial case) or a real flip;
boundaries are transformed by `MMP.Mori.flipTransform`. The transforms `C_{i,j}` of the `C_i` are
given by the same recursion. The step maps `ψ_j : Y_{j+1} ⤏ Y_j` are pinned by
`f_j ∘ ψ_j = f_j⁺` (`(ψ j).compHom (f j) = (fp j).toRationalMap`), which determines them since
`f_j` is birational, and the transported weak-model maps are `Φ_{i,j+1} = Φ_{i,j} ∘ ψ_j`,
`Φ_{i,0} = φ_i`. Convergence of boundaries is coefficientwise convergence, which for boundaries of
a fixed finite support is convergence in the coefficient space.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Filter Topology MMP.Fourfold MMP.Mori MMP.Flips

namespace Proof_lem_fourfold_terminal_limit_nef_reduction

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Stages

/-- A stage of the program: a model over `S` with a canonical divisor, the transform of the
limit boundary, the transforms of all the boundaries `C_i`, the transported weak-model maps, a
threshold and a common support. -/
private structure Stage (S : Scheme.{0}) (Z : ℕ → Scheme.{0}) where
  X : Scheme.{0}
  [isIntegral : IsIntegral X]
  [compactSpace : CompactSpace X]
  [isLocallyNoetherian : IsLocallyNoetherian X]
  [isNormal : IsNormal X]
  sX : X ⟶ Spec (.of ℂ)
  πX : X ⟶ S
  K : Divisor X
  B : RDivisor X
  C : ℕ → RDivisor X
  Φ : ∀ i, X.RationalMap (Z i)
  N : ℕ
  F : Finset (MMP.Mori.PrimeDivisor X)

attribute [local instance] Stage.isIntegral Stage.compactSpace Stage.isLocallyNoetherian
  Stage.isNormal

/-- The data of one step from a stage. -/
private structure StepData {S : Scheme.{0}} {Z : ℕ → Scheme.{0}} (s : Stage S Z) where
  t : Stage S Z
  R : Set (RelativeNumericalCurveClasses s.sX s.πX)
  Zs : Scheme.{0}
  sZs : Zs ⟶ Spec (.of ℂ)
  f : s.X ⟶ Zs
  g : Zs ⟶ S
  fp : t.X ⟶ Zs
  ψ : t.X.RationalMap s.X

/-- The stages obtained from `s0` by iterating a choice of steps. -/
private noncomputable def Stage.seq {S : Scheme.{0}} {Z : ℕ → Scheme.{0}} (s0 : Stage S Z)
    (next : (s : Stage S Z) → StepData s) : ℕ → Stage S Z
  | 0 => s0
  | i + 1 => (next (Stage.seq s0 next i)).t

/-- The rays of the iterated sequence of steps, indexed as the models of a program. -/
private noncomputable def Stage.progR {S : Scheme.{0}} {Z : ℕ → Scheme.{0}} (s0 : Stage S Z)
    (next : (s : Stage S Z) → StepData s) :
    ∀ i, Set (RelativeNumericalCurveClasses
      (modelStr s0.sX (fun j => (Stage.seq s0 next (j + 1)).sX) i)
      (modelMap s0.πX (fun j => (Stage.seq s0 next (j + 1)).πX) i))
  | 0 => (next s0).R
  | i + 1 => (next (Stage.seq s0 next (i + 1))).R

/-- The contractions of the iterated sequence of steps, indexed as the models of a program. -/
private noncomputable def Stage.progF {S : Scheme.{0}} {Z : ℕ → Scheme.{0}} (s0 : Stage S Z)
    (next : (s : Stage S Z) → StepData s) :
    ∀ i, modelSeq s0.X (fun j => (Stage.seq s0 next (j + 1)).X) i ⟶
      (next (Stage.seq s0 next i)).Zs
  | 0 => (next s0).f
  | i + 1 => (next (Stage.seq s0 next (i + 1))).f

/-- The step maps of the iterated sequence of steps, indexed as the models of a program. -/
private noncomputable def Stage.progψ {S : Scheme.{0}} {Z : ℕ → Scheme.{0}} (s0 : Stage S Z)
    (next : (s : Stage S Z) → StepData s) :
    ∀ i, (Stage.seq s0 next (i + 1)).X.RationalMap
      (modelSeq s0.X (fun j => (Stage.seq s0 next (j + 1)).X) i)
  | 0 => (next s0).ψ
  | i + 1 => (next (Stage.seq s0 next (i + 1))).ψ

/-- The transported weak-model maps of the iterated sequence of steps. -/
private noncomputable def Stage.progΦ {S : Scheme.{0}} {Z : ℕ → Scheme.{0}} (s0 : Stage S Z)
    (next : (s : Stage S Z) → StepData s) :
    ∀ i j, (modelSeq s0.X (fun j => (Stage.seq s0 next (j + 1)).X) j).RationalMap (Z i)
  | i, 0 => s0.Φ i
  | i, j + 1 => (Stage.seq s0 next (j + 1)).Φ i

/-- The supports of the iterated sequence of stages, indexed as the models of a program. -/
private noncomputable def Stage.progFin {S : Scheme.{0}} {Z : ℕ → Scheme.{0}} (s0 : Stage S Z)
    (next : (s : Stage S Z) → StepData s) :
    ∀ j, Finset (MMP.Mori.PrimeDivisor (modelSeq s0.X (fun j => (Stage.seq s0 next (j + 1)).X) j))
  | 0 => s0.F
  | j + 1 => (Stage.seq s0 next (j + 1)).F

end Stages

attribute [local instance] Stage.isIntegral Stage.compactSpace Stage.isLocallyNoetherian
  Stage.isNormal

section StepIso

/-- The comparison of a weak model `Φ : X ⤏ Z` of `(X, C)` vanishes along a set `F` of primes,
on some smooth projective common resolution. -/
private def CompVanishesOn {Zt : Scheme.{0}} [IsIntegral Zt] [IsLocallyNoetherian Zt]
    [IsNormal Zt] (sZt : Zt ⟶ Spec (.of ℂ)) {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) (K : Divisor X)
    (C : RDivisor X) (Φ : X.RationalMap Zt) (F : Finset (MMP.Mori.PrimeDivisor X)) : Prop :=
  ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
    (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ X) (q : W ⟶ Zt)
    (h : X.RationalMap W),
    MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧
      p ≫ sX = sW ∧ q ≫ sZt = sW ∧
      IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ IsBirationalMorphism p ∧
      IsBirationalMorphism q ∧ MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧
      h.compHom q = Φ ∧
      ∃ GY GZ : RDivisor W,
        IsRCartierPullback p (logCanonicalDivisor K C) GY ∧
        IsRCartierPullback q
          (logCanonicalDivisor (RationalMap.transformDivisor Φ K)
            (RationalMap.transformDivisor Φ C)) GZ ∧
        ∀ P ∈ F, ∀ P' : MMP.Mori.PrimeDivisor W,
          RationalMap.transformPrimeDivisor h P = some P' → (GY - GZ).coeff P' = 0

/-- The partial isomorphism `X ⤏ X'` of a step `X ⟶ Zs ⟵ X'`: `f` followed by the inverse of
`f⁺` over the open of `Zs` over which both are isomorphisms. -/
private noncomputable def stepIso {X X' Zs : Scheme.{0}} (f : X ⟶ Zs) (fp : X' ⟶ Zs)
    (h1 : Dense ((f ⁻¹ᵁ (biregularLocus f ⊓ biregularLocus fp) : X.Opens) : Set X))
    (h2 : Dense ((fp ⁻¹ᵁ (biregularLocus f ⊓ biregularLocus fp) : X'.Opens) : Set X')) :
    X.PartialIso X' :=
  haveI : IsIso (f ∣_ (biregularLocus f ⊓ biregularLocus fp)) :=
    isBiregular_iff_le_biregularLocus.mpr inf_le_left
  haveI : IsIso (fp ∣_ (biregularLocus f ⊓ biregularLocus fp)) :=
    isBiregular_iff_le_biregularLocus.mpr inf_le_right
  { source := f ⁻¹ᵁ (biregularLocus f ⊓ biregularLocus fp)
    dense_source := h1
    target := fp ⁻¹ᵁ (biregularLocus f ⊓ biregularLocus fp)
    dense_target := h2
    iso := asIso (f ∣_ (biregularLocus f ⊓ biregularLocus fp)) ≪≫
      (asIso (fp ∣_ (biregularLocus f ⊓ biregularLocus fp))).symm }

end StepIso

section

variable {S Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
  (sS : S ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [QuasiCompact sZ] (πZ : Z ⟶ S)

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
  have hVc : V.compl = f ⁻¹ᵁ U := by ext x; simp [V]
  have hWc : W.compl = fp ⁻¹ᵁ U := by ext x; simp [W]
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

/-- A canonical divisor of a normal complex variety is the divisor of a nonzero rational top
form. -/
private theorem exists_divisorOfForm_eq' {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    ∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧ divisorOfForm ω = K := by
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  exact ⟨ω, hω0, DivisorWithCoeffs.ext' hωK⟩

/-- The log discrepancy of a prime divisor `Q` of `X` is `1 - coeff_Q B`, for a real boundary `B`
with `K_X + B` `ℝ`-Cartier. -/
private theorem isLogDiscrepancy_ofPrimeDivisor' {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] (hX : IsNormalVariety ℂ sX) {n : ℕ} {B : RDivisor X}
    {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKB : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B))
    (Q : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsLogDiscrepancy sX n B (DivisorOver.ofPrimeDivisor ℂ hX Q)
      (1 - B.coeff Q) := by
  have h := MMP.Flips.isDiscrepancy_divisorialValuation hX ω hω hK hKB Q
  have hv : (DivisorOver.ofPrimeDivisor ℂ hX Q).valuation = Q.divisorialValuation :=
    Valuation.ext fun φ => by
      change Q.divisorialValuation (functionFieldMap (𝟙 X) φ) = _
      rw [MMP.Mori.functionFieldMap_id_apply]
  have := isLogDiscrepancy_of_isDiscrepancy h (DivisorOver.ofPrimeDivisor ℂ hX Q)
    (inferInstanceAs (IsProper (𝟙 X))) hv
  rwa [← sub_eq_add_neg] at this

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
  have hN : (K' - K).LinearlyEquivalent 0 := ⟨φ, by rw [sub_zero]; exact hφ⟩
  have hNc' : (K - K').IsCartier := by
    have := hNc.neg; rwa [neg_sub] at this
  have hN' : (K - K').LinearlyEquivalent 0 := by
    obtain ⟨ψ, hψ⟩ := hN
    exact ⟨ψ⁻¹, by rw [sub_zero, MMP.Mori.principalDivisor_inv, ← hψ, sub_zero, neg_sub]⟩
  have hL : logCanonicalDivisor K' B = logCanonicalDivisor K B + Divisor.toRDivisor (K' - K) := by
    simp only [logCanonicalDivisor, map_sub]; abel
  have hLneg : -logCanonicalDivisor K' B =
      -logCanonicalDivisor K B + Divisor.toRDivisor (K - K') := by
    rw [hL]; simp only [map_sub]; abel
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

private theorem isExceptional_iff_two_le_coheight_ph {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    (D : DivisorOver ℂ sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) :=
  MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX D

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

/-- **A divisorial contraction of a prime with zero boundary coefficient keeps the pair real
terminal.** Let `f : X ⟶ Z` be a `(K + B)`-negative extremal contraction with exceptional set a
prime divisor `E`, `B.coeff E = 0`, and `f⁺ : X⁺ ⟶ Z` an isomorphism. Every exceptional divisor
over `X⁺` has log discrepancy at least that over `X` (FA 2.28, with the forms of `Z` pulled
back); if it is exceptional over `X` the latter exceeds one, and otherwise it is `E` itself,
whose log discrepancy `1` strictly increases since `K + B` is negative on the curves of `E`. -/
private theorem isRealTerminalPair_of_divisorial {X X' Zs : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    {sZs : Zs ⟶ Spec (.of ℂ)} {K : Divisor X} {B : RDivisor X} {K' : Divisor X'}
    {f : X ⟶ Zs} {fp : X' ⟶ Zs}
    (hneg : IsNegativeExtremalContraction ℂ sX sZs (logCanonicalDivisor K B) f)
    (hb : IsBirationalMorphism f) {E : MMP.Mori.PrimeDivisor X}
    (hE : (MMP.Mori.exceptionalSet f : Set X) = E.support) [IsIso fp] (hfps : fp ≫ sZs = sX')
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) (hK' : ∃ m : ℕ, K'.IsCanonicalDivisor sX' m)
    (hBE : B.coeff E = 0) (hT : IsRealTerminalPair sX B) (hXp : MMP.Mori.IsProjectiveVariety ℂ sX)
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
  have hbp : IsBirationalMorphism fp := isBirationalMorphism_of_isIso fp
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
  obtain ⟨ωX, hωX0, hωX⟩ := exists_divisorOfForm_eq' hXv hKm
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
  have hZsep : IsSeparated (Zs ↘ Limits.terminal Scheme) := by
    rw [show (Zs ↘ Limits.terminal Scheme) = sZs ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hbrfp : ∀ x : X', fp x ∈ biregularLocus fp := fun x =>
    le_biregularLocus ((isBiregular_top_iff fp).mpr inferInstance) trivial
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
      have hPE : P.genericPoint ∈ E.support := by
        rw [← hE, SetLike.mem_coe, MMP.Mori.mem_exceptionalSet]
        intro hbr
        have hco := (MMP.Positivity.coheight_map_of_mem_biregularLocus f hbr).trans
          P.coheight_genericPoint
        exact hQ ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
          (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm⟩
      have hEP := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hPE
      rw [← hEP]
      simpa only [DivisorWithCoeffs.coeff_apply] using hBE
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
    rw [hBY]; exact isRelativelyNef_of_isIso fp hKB'c
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
      (isLogDiscrepancy_ofPrimeDivisor' hXv hωX0 hKmω hKBc Q) hQ
    have hc1 : D₁.f D₁.E.genericPoint = Q.genericPoint :=
      MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hXv.1 hQ
    have hc2 : f (D₁.f D₁.E.genericPoint) = DZ.f DZ.E.genericPoint :=
      map_genericPoint_eq_of_valuation_comap_eq_ph f D₁.toDivisorOver DZ hD₁
    rw [hc1] at hc2
    by_cases hQE : Q = E
    · subst hQE
      rw [hBE, sub_zero] at haQ
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
        have hyEx : y ∈ (MMP.Mori.exceptionalSet f : Set X) := hE ▸ hyE
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
      have hηQ : Q.genericPoint ∉ (MMP.Mori.exceptionalSet f : Set X) := by
        rw [hE]
        intro hmem
        exact hQE (MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hmem).symm
      have hbr : f Q.genericPoint ∈ biregularLocus f := by
        by_contra h; exact hηQ (MMP.Mori.mem_exceptionalSet.mpr h)
      have hco : Order.coheight (f Q.genericPoint) = 1 :=
        (MMP.Positivity.coheight_map_of_mem_biregularLocus f hbr).trans Q.coheight_genericPoint
      have hco' : Order.coheight (E'.f E'.E.genericPoint) = 1 := by
        rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hbrfp _)]
        change Order.coheight ((E'.f ≫ fp) E'.E.genericPoint) = 1
        rw [show (E'.f ≫ fp) E'.E.genericPoint = DZ.f DZ.E.genericPoint from rfl, ← hc2, hco]
      have h2 := (isExceptional_iff_two_le_coheight_ph hX'v E').mp hE'
      rw [hco'] at h2
      exact absurd h2 (by decide)
  refine ⟨⟨hX'v, fun P' hP' => ?_,
    ⟨m, K', hK'm, isRCartier_logCanonical_of_isQFactorial hX'Q K' B'⟩,
    fun n E' a' hE' ha' => (hterm n E' a' hE' ha').le⟩, hterm⟩
  obtain ⟨Q, P, -, -, -, hB'P'⟩ := hover P'
  simp only [DivisorWithCoeffs.coeff_apply] at hP' ⊢
  rw [hB'P'] at hP' ⊢
  exact hT.1.2.1 P (by simpa only [DivisorWithCoeffs.coeff_apply] using hP')

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
  have hZsep : IsSeparated (Zs ↘ Limits.terminal Scheme) := by
    rw [show (Zs ↘ Limits.terminal Scheme) = sZs ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
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
      (isLogDiscrepancy_ofPrimeDivisor' hXv hωX0 hKmω hKBc Q) hQ
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
      have h2 := (isExceptional_iff_two_le_coheight_ph hX'v E').mp hE'
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
      obtain ⟨ω, hω0, hω⟩ := exists_divisorOfForm_eq' hXv hK₀
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
        (isLogDiscrepancy_ofPrimeDivisor' hXv hω0 (hω ▸ hK₀) hKB Q) hQ
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

/-- When `f⁺` is the identity, the step map is `f`. -/
private theorem stepIso_id_toRationalMap {X Zs : Scheme.{0}} [IsIntegral X]
    [IsSeparated (Zs ↘ CategoryTheory.Limits.terminal Scheme)] (f : X ⟶ Zs)
    (h1 : Dense ((f ⁻¹ᵁ (biregularLocus f ⊓ biregularLocus (𝟙 Zs)) : X.Opens) : Set X))
    (h2 : Dense (((𝟙 Zs) ⁻¹ᵁ (biregularLocus f ⊓ biregularLocus (𝟙 Zs)) : Zs.Opens) : Set Zs)) :
    (stepIso f (𝟙 Zs) h1 h2).toRationalMap = f.toRationalMap := by
  set U := biregularLocus f ⊓ biregularLocus (𝟙 Zs) with hU
  haveI : IsIso (f ∣_ U) := isBiregular_iff_le_biregularLocus.mpr inf_le_left
  haveI : IsIso ((𝟙 Zs) ∣_ U) := isBiregular_iff_le_biregularLocus.mpr inf_le_right
  have hhom : (stepIso f (𝟙 Zs) h1 h2).toPartialMap.hom = (f ⁻¹ᵁ U).ι ≫ f := by
    change ((asIso (f ∣_ U)).hom ≫ (asIso ((𝟙 Zs) ∣_ U)).inv) ≫ ((𝟙 Zs) ⁻¹ᵁ U).ι = _
    simp only [asIso_hom, asIso_inv, Category.assoc]
    have h : inv ((𝟙 Zs) ∣_ U) ≫ ((𝟙 Zs) ⁻¹ᵁ U).ι = U.ι := by
      rw [IsIso.inv_comp_eq, morphismRestrict_ι, Category.comp_id]
    rw [h, morphismRestrict_ι]
  show (stepIso f (𝟙 Zs) h1 h2).toPartialMap.toRationalMap = f.toPartialMap.toRationalMap
  exact Scheme.PartialMap.toRationalMap_eq_iff.mpr
    ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated
      (S := CategoryTheory.Limits.terminal Scheme)).mpr hhom)

/-- **Relative ampleness of an adjoint does not depend on the canonical divisor**: if `K'` is
linearly equivalent to `K` and `K + B` is `f`-ample, so is `K' + B`. -/
private theorem isRelativelyAmple_of_linearlyEquivalent {X Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} (hXv : IsNormalVariety ℂ sX) (hZv : IsNormalVariety ℂ sZ)
    {f : X ⟶ Z} [IsProper f] (hf : f ≫ sZ = sX) {K K' : Divisor X} {B : RDivisor X}
    (hKB : IsCartierCombination (logCanonicalDivisor K B))
    (h : IsRelativelyAmple f (logCanonicalDivisor K B)) (hK : K'.LinearlyEquivalent K) :
    IsRelativelyAmple f (logCanonicalDivisor K' B) := by
  haveI : QuasiCompact sX := hXv.1.toQuasiCompact
  haveI : IsNormal Z := hZv.2
  haveI : LocallyOfFiniteType sZ := hZv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  obtain ⟨φ, hφ⟩ := hK
  have hNc : (K' - K).IsCartier := hφ ▸ Divisor.isCartier_principalDivisor φ
  have hN : (K' - K).LinearlyEquivalent 0 := ⟨φ, by rw [sub_zero]; exact hφ⟩
  have hL : logCanonicalDivisor K' B =
      logCanonicalDivisor K B + Divisor.toRDivisor (K' - K) := by
    simp only [logCanonicalDivisor, map_sub]; abel
  have hbasics := MMP.Flips.relativelyAmple_basics sX sZ hXv hZv f hf
  have h' := h
  obtain ⟨m, r, L, hm, -, hLa, -⟩ := h'
  have hproj : IsProjective f := hbasics.2.2.2.1 ⟨L ⟨0, hm⟩, hLa ⟨0, hm⟩⟩
  rw [hL]
  exact hbasics.2.2.2.2.2 hproj _ _
    (isNumericallyEquivalentOver_add_of_linearlyEquivalent f hKB hNc hN) h

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
  · haveI : IsNormal Zs := hZv.2
    haveI : LocallyOfFiniteType sZs := hZv.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian Zs := LocallyOfFiniteType.isLocallyNoetherian sZs
    haveI : QuasiCompact sX' := hX'v.1.toQuasiCompact
    exact isRelativelyNef_of_isRelativelyAmple hX'v hZv fp hfps
      (isRelativelyAmple_of_linearlyEquivalent hX'v hZv hfps
        (isCartierCombination_of_isQFactorial_ph hX'Q _) hfl.isRelativelyAmple_flip hlin)
  · have := two_le_coheight_of_mem_exceptionalSet_of_isSmall hfl.isSmall hP
    rw [P.coheight_genericPoint] at this
    exact absurd this (by decide)

/-- **The transported weak model after one step.** Let `X ⟶ Zs ⟵ X'` be a step of a program
over `S` for `(X, B)` and `φ : X ⤏ Z` a `ℚ`-factorial nef weak model of `(X, B)` whose comparison
vanishes along the positive support `F` of `B`. Then no prime of positive coefficient is
contracted, the transforms of divisors along the step map `X ⤏ X'` are `(f⁺)⁻¹_* f_*`, and the
transported map `X' ⤏ X ⤏ Z` is a nef weak model of `(X', B')` whose comparison vanishes along
every set of primes of positive coefficient. -/
private theorem weakModel_step' (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hZQ : IsQFactorial sZ)
    {X X' Zs : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)}
    {πX : X ⟶ S} {πX' : X' ⟶ S} {K : Divisor X} {B : RDivisor X} {K' : Divisor X'}
    {B' : RDivisor X'} {R : Set (RelativeNumericalCurveClasses sX πX)} {f : X ⟶ Zs}
    {g : Zs ⟶ S} {fp : X' ⟶ Zs} {φ : X.RationalMap Z} {F : Finset (MMP.Mori.PrimeDivisor X)}
    (hXp : MMP.Mori.IsProjectiveVariety ℂ sX) (hXQ : IsQFactorial sX) (hπ : πX ≫ sS = sX)
    (hT : IsRealTerminalPair sX B) (hφ : IsNefWeakModel sX sZ sS πX πZ K B φ)
    (hF : ∀ P, 0 < B.coeff P ↔ P ∈ F) (hCVm : CompVanishesOn sZ sX K B φ F)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (hX' : MMP.Mori.IsProjectiveVariety ℂ sX' ∧ IsQFactorial sX' ∧ πX' ≫ sS = sX')
    (hstep : IsStep sX sX' sZs πX πX' K B K' B' R f g fp)
    (hd1 : Dense ((f ⁻¹ᵁ (biregularLocus f ⊓ biregularLocus fp) : X.Opens) : Set X))
    (hd2 : Dense ((fp ⁻¹ᵁ (biregularLocus f ⊓ biregularLocus fp) : X'.Opens) : Set X'))
    [(stepIso f fp hd1 hd2).symm.toRationalMap.IsDominant]
    (hdivL : IsIso fp → ∃ f' : X ⟶ X', f'.toRationalMap = (stepIso f fp hd1 hd2).toRationalMap ∧
      f' ≫ πX' = πX ∧ IsNegativeExtremalContraction ℂ sX sX' (logCanonicalDivisor K B) f' ∧
      IsBirationalMorphism f' ∧ (∃ E : MMP.Mori.PrimeDivisor X,
        MMP.Flips.exceptionalSet f' = E.support) ∧
      ∀ G : MMP.Mori.PrimeDivisor X, (MMP.Mori.exceptionalSet f : Set X) = G.support →
        MMP.Mori.RationalMap.IsExceptional f'.toRationalMap G) :
    (∀ E : MMP.Mori.PrimeDivisor X,
        (E.support : Set X) ⊆ MMP.Mori.exceptionalSet f → B.coeff E = 0) ∧
      (∀ D : Divisor X,
        RationalMap.transformDivisor (stepIso f fp hd1 hd2).toRationalMap D =
          flipTransform f fp D) ∧
      (∀ D : RDivisor X,
        RationalMap.transformDivisor (stepIso f fp hd1 hd2).toRationalMap D =
          flipTransform f fp D) ∧
      (∀ P' : MMP.Mori.PrimeDivisor X', ∃ P : MMP.Mori.PrimeDivisor X,
        ∀ D : RDivisor X, (flipTransform f fp D).coeff P' = D.coeff P) ∧
      IsNefWeakModel sX' sZ sS πX' πZ
        (RationalMap.transformDivisor (stepIso f fp hd1 hd2).toRationalMap K) B'
        ((stepIso f fp hd1 hd2).symm.toRationalMap.comp φ) ∧
      ∀ F' : Finset (MMP.Mori.PrimeDivisor X'), (∀ P' ∈ F', 0 < B'.coeff P') →
        CompVanishesOn sZ sX'
          (RationalMap.transformDivisor (stepIso f fp hd1 hd2).toRationalMap K) B'
          ((stepIso f fp hd1 hd2).symm.toRationalMap.comp φ) F' := by
  classical
  have hXv0 : IsNormalVariety ℂ sX := hXQ.1
  -- the comparison along each prime of positive coefficient, on the given resolution
  have hCV : ∀ G : MMP.Mori.PrimeDivisor X, 0 < B.coeff G →
      ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
        (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ X) (q : W ⟶ Z) (h : X.RationalMap W)
        (GY GZ : RDivisor W) (P : MMP.Mori.PrimeDivisor W),
        MMP.Mori.IsVariety ℂ sW ∧ p ≫ sX = sW ∧ q ≫ sZ = sW ∧ IsProjectiveMorphism p ∧
        IsProjectiveMorphism q ∧ IsBirationalMorphism p ∧ IsBirationalMorphism q ∧
        MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧ h.compHom q = φ ∧
        IsRCartierPullback p (logCanonicalDivisor K B) GY ∧
        IsRCartierPullback q
          (logCanonicalDivisor (RationalMap.transformDivisor φ K)
            (RationalMap.transformDivisor φ B)) GZ ∧
        RationalMap.transformPrimeDivisor p.toRationalMap P = some G ∧
        (GY - GZ).coeff P = 0 := by
    obtain ⟨W, _, _, _, sW, p, q, h, hW, -, hpY, hqZ, hp, hq, hpb, hqb, hinvW, hhq, GY, GZ, hGY,
      hGZ, h0⟩ := hCVm
    intro G hG
    haveI : IsProper p := isProper_of_isProjectiveMorphism p hp
    haveI : IsSeparated sX := hXv0.1.toIsSeparated
    haveI : IsSeparated (X ↘ CategoryTheory.Limits.terminal Scheme) := by
      rw [show (X ↘ CategoryTheory.Limits.terminal Scheme) =
        sX ≫ (Spec (.of ℂ) ↘ CategoryTheory.Limits.terminal Scheme) from
          CategoryTheory.Limits.terminal.hom_ext _ _]
      infer_instance
    obtain ⟨PW, hPW, -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXv0
        (by rw [hpY]; exact ⟨hW, inferInstance⟩) hpb G
    have h1 : RationalMap.transformPrimeDivisor h G = some PW :=
      transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq hXv0 p (by rw [hpY]; exact hW) hpb
        hinvW hPW
    exact ⟨W, inferInstance, inferInstance, inferInstance, sW, p, q, h, GY, GZ, PW, hW, hpY, hqZ,
      hp, hq, hpb, hqb, hinvW, hhq, hGY, hGZ,
      (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p PW G).mpr hPW,
      h0 G ((hF G).mp hG) PW h1⟩
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
  have hZsep : IsSeparated (Zs ↘ CategoryTheory.Limits.terminal Scheme) := by
    rw [show (Zs ↘ CategoryTheory.Limits.terminal Scheme) =
      sZs ≫ (Spec (.of ℂ) ↘ CategoryTheory.Limits.terminal Scheme) from
        CategoryTheory.Limits.terminal.hom_ext _ _]
    infer_instance
  have hX'sep : IsSeparated (X' ↘ CategoryTheory.Limits.terminal Scheme) := by
    haveI : IsSeparated sX' := hX'v.1.toIsSeparated
    rw [show (X' ↘ CategoryTheory.Limits.terminal Scheme) =
      sX' ≫ (Spec (.of ℂ) ↘ CategoryTheory.Limits.terminal Scheme) from
        CategoryTheory.Limits.terminal.hom_ext _ _]
    infer_instance
  have hXsep : IsSeparated (X ↘ CategoryTheory.Limits.terminal Scheme) := by
    haveI : IsSeparated sX := hXv.1.toIsSeparated
    rw [show (X ↘ CategoryTheory.Limits.terminal Scheme) =
      sX ≫ (Spec (.of ℂ) ↘ CategoryTheory.Limits.terminal Scheme) from
        CategoryTheory.Limits.terminal.hom_ext _ _]
    infer_instance
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
  -- the weak model's resolution
  obtain ⟨W₀, _, _, _, sW₀, p₀, q₀, h₀, hW₀, hW₀s, hp₀Y, hq₀Z, hp₀, hq₀, hp₀b, hq₀b, hinv₀, hhq₀,
    GY₀, GZ₀, hGY₀, hGZ₀, hA₀, hA₀q⟩ := hφ.exists_resolution
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
  let e : X.PartialIso X' := stepIso f fp hd1 hd2
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
        have hrep : g' = (f ≫ inv fp).toRationalMap := by
          show e.toPartialMap.toRationalMap = (f ≫ inv fp).toPartialMap.toRationalMap
          refine Scheme.PartialMap.toRationalMap_eq_iff.mpr
            ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated
              (S := CategoryTheory.Limits.terminal Scheme)).mpr ?_)
          refine (cancel_mono fp).mp ?_
          change e.toPartialMap.hom ≫ fp = (e.toPartialMap.domain.ι ≫ f ≫ inv fp) ≫ fp
          rw [hhom, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
          rfl
        rw [hrep, MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff] at hG
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
  -- the transform of the boundary is `B⁺`
  have hflB : B' = flipTransform f fp B := by
    rcases hstep.2.2.2.2.2 with ⟨-, -, -, h⟩ | hfl
    · exact h
    · exact hfl.eq_flipTransform
  have hcoeffD : ∀ {Rc : Type} [AddCommMonoid Rc] (D : DivisorWithCoeffs Rc X)
      (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor X'),
      f P.genericPoint = fp P'.genericPoint → flipTransform f fp D P' = D P := by
    intro Rc _ D P P' hPP'
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
  have hcoeffB : ∀ (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor X'),
      f P.genericPoint = fp P'.genericPoint → B' P' = B P := by
    intro P P' hPP'
    rw [hflB]
    exact hcoeffD B P P' hPP'
  have hDeq : ∀ {Rc : Type} [AddCommMonoid Rc] (D : DivisorWithCoeffs Rc X),
      RationalMap.transformDivisor g' D = flipTransform f fp D := by
    intro Rc _ D
    ext P'
    simp only [DivisorWithCoeffs.coeff_apply]
    obtain ⟨P, hP, hPP', hhP⟩ := hover P'
    obtain ⟨G', hG', htr⟩ := himage P hP
    have hG'P' : G' = P' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hG'.trans hhP)
    subst hG'P'
    rw [hcoeffD D P G' hPP', RationalMap.transformDivisor]
    exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq htr
      (fun G hG => huniq G P G' hP hhP hG) D
  have hB'eq : RationalMap.transformDivisor g' B = B' := (hDeq B).trans hflB.symm
  -- the canonical divisor commutes with the passage to real coefficients
  have hKR : flipTransform f fp (Divisor.toRDivisor K) =
      Divisor.toRDivisor (flipTransform f fp K) := by
    ext P'
    obtain ⟨P, -, hPP', -⟩ := hover P'
    have h1 := hcoeffD (Divisor.toRDivisor K) P P' hPP'
    have h2 := hcoeffD K P P' hPP'
    change (flipTransform f fp (Divisor.toRDivisor K)).coeff P' =
      (Divisor.toRDivisor (flipTransform f fp K)).coeff P'
    rw [Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply, h1,
      ← DivisorWithCoeffs.coeff_apply, Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply,
      DivisorWithCoeffs.coeff_apply, h2]
  have hT1 : RationalMap.transformDivisor g' (logCanonicalDivisor K B) =
      logCanonicalDivisor (RationalMap.transformDivisor g' K) B' := by
    rw [hDeq, hDeq K]
    simp only [logCanonicalDivisor, map_add, hKR, hflB]
  -- a flip of `f` with the step map, in the form of the weak-model lemma
  have hIsFlip : IsRealFlipStep sX sZs sX' K B K' B' f fp →
      MMP.Flips.IsFlip ℂ sX sZs sX' (logCanonicalDivisor K B) f fp g' := by
    intro hfl
    obtain ⟨V, hVf, hVfp, hXV, hX'V⟩ := hfl.exists_opens_isIso
    haveI := hVf
    haveI := hVfp
    have hKg : Divisor.IsCanonicalDivisor sX' m (RationalMap.transformDivisor g' K) := by
      rw [hDeq K]
      have := MMP.Mori.isCanonicalDivisor_flipTransform_of_isIso_restrict (k := ℂ) hZsv
        (f := f) (fp := fp) (by rw [hc.comp_eq]; exact hXv) (by rw [hfps]; exact hX'v) hfb hfpb V
        hXV hX'V (n := m) (K := K) (by rw [hc.comp_eq]; exact hKm)
      rwa [hfps] at this
    obtain ⟨m', hK'm⟩ := hfl.isCanonicalDivisor_flip
    refine
      { isNormalVariety_source := hXv
        isNormalVariety_target := hZsv
        isNormalVariety_flip := hX'v
        isContraction := hc
        isCartierCombination := hneg.isCartierCombination
        isRelativelyAntiAmple := hneg.isRelativelyAntiAmple
        isProper := inferInstance
        isModificationOf := ⟨hg'b, hgu⟩
        isMorphismInCodimOne := MMP.Flips.RationalMap.isMorphismInCodimOne_of_isOver hXv f fp g' hgu
        isSmall := hfl.isSmall_flip
        isCartierCombination_transform := isCartierCombination_of_isQFactorial_ph hX'Q _
        isRelativelyAmple_transform := ?_
        isSmall_source := hfl.isSmall }
    rw [hT1]
    exact isRelativelyAmple_of_linearlyEquivalent hX'v hZsv hfps
      (isCartierCombination_of_isQFactorial_ph hX'Q _) hfl.isRelativelyAmple_flip
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX' hX'v hKg hK'm)
  have hstepL : (∃ f' : X ⟶ X', f'.toRationalMap = g' ∧ f' ≫ πX' = πX ∧
        IsNegativeExtremalContraction ℂ sX sX' (logCanonicalDivisor K B) f' ∧
        IsBirationalMorphism f' ∧
        ∃ E : MMP.Mori.PrimeDivisor X, MMP.Flips.exceptionalSet f' = E.support) ∨
      (∃ (V : Scheme.{0}) (sV : V ⟶ Spec (.of ℂ)) (πV : V ⟶ S) (f₁ : X ⟶ V) (fp₁ : X' ⟶ V),
        f₁ ≫ πV = πX ∧ fp₁ ≫ πV = πX' ∧
        IsNegativeExtremalContraction ℂ sX sV (logCanonicalDivisor K B) f₁ ∧
        MMP.Flips.IsFlip ℂ sX sV sX' (logCanonicalDivisor K B) f₁ fp₁ g') := by
    rcases hstep.2.2.2.2.2 with ⟨-, hiso, -, -⟩ | hfl
    · obtain ⟨f', hf'g, hf'S, hf'n, hf'b, hf'E, -⟩ := hdivL hiso
      exact Or.inl ⟨f', hf'g, hf'S, hf'n, hf'b, hf'E⟩
    · exact Or.inr ⟨Zs, sZs, g, f, fp, hstep.2.2.1.comp_eq, hstep.2.2.2.2.1, hneg, hIsFlip hfl⟩
  have hLs := (hφ.isNefWeakModel_of_negativeStep hXQ hZQ).1 sX' πX' g' φ' hX'p hX'Q hπ' hstepL
    hcomp
  obtain ⟨hnew, hnex1b⟩ := hLs
  -- in the divisorial case, the contracted prime has nonzero comparison coefficient
  have hEnz : ∀ E : MMP.Mori.PrimeDivisor X,
      (MMP.Mori.exceptionalSet f : Set X) = E.support →
      ∀ (W : Scheme.{0}) [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
        (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ X) (q : W ⟶ Z) (h : X.RationalMap W)
        (GY GZ : RDivisor W) (P : MMP.Mori.PrimeDivisor W),
        MMP.Mori.IsVariety ℂ sW → p ≫ sX = sW → q ≫ sZ = sW → IsProjectiveMorphism p →
        IsProjectiveMorphism q → IsBirationalMorphism p → IsBirationalMorphism q →
        MMP.Mori.RationalMap.IsInverse p.toRationalMap h → h.compHom q = φ →
        IsRCartierPullback p (logCanonicalDivisor K B) GY →
        IsRCartierPullback q (logCanonicalDivisor (RationalMap.transformDivisor φ K)
          (RationalMap.transformDivisor φ B)) GZ →
        RationalMap.transformPrimeDivisor p.toRationalMap P = some E →
        (GY - GZ).coeff P ≠ 0 := by
    intro E hE W _ _ _ sW p q h GY GZ P hW hpY hqZ hp hq hpb hqb hinv hhq hGY hGZ hPE h0
    rcases hstep.2.2.2.2.2 with ⟨-, hiso, -, -⟩ | hfl
    · obtain ⟨f', hf'g, -, -, -, -, hexc⟩ := hdivL hiso
      exact hnex1b sW p q h hW hpY hqZ hp hq hpb hqb hinv hhq hGY hGZ E P hPE h0
        (hf'g ▸ hexc E hE)
    · have hηE : E.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set X) := by
        rw [hE, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      have := two_le_coheight_of_mem_exceptionalSet_of_isSmall hfl.isSmall hηE
      rw [E.coheight_genericPoint] at this
      exact absurd this (by decide)
  -- (a) no prime of positive coefficient is contracted
  have hnc : ∀ E : MMP.Mori.PrimeDivisor X,
      (E.support : Set X) ⊆ MMP.Mori.exceptionalSet f → B.coeff E = 0 := by
    intro E hEx
    by_contra hne
    have hηE : E.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set X) := by
      refine hEx ?_
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    rcases hstep.2.2.2.2.2 with ⟨⟨-, E₀, hE₀⟩, -, -, -⟩ | hfl
    · have hEE₀ : E₀ = E := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support
        (hE₀ ▸ hηE)
      subst hEE₀
      have hpos : 0 < B.coeff E₀ :=
        lt_of_le_of_ne (nonneg_of_isRealCanonicalPair hT.1 E₀) (Ne.symm hne)
      obtain ⟨W, _, _, _, sW, p, q, h, GY, GZ, P, hW, hpY, hqZ, hp, hq, hpb, hqb, hinv, hhq, hGY,
        hGZ, hPE, h0⟩ := hCV E₀ hpos
      exact hEnz E₀ hE₀ W sW p q h GY GZ P hW hpY hqZ hp hq hpb hqb hinv hhq hGY hGZ hPE h0
    · have := two_le_coheight_of_mem_exceptionalSet_of_isSmall hfl.isSmall hηE
      rw [E.coheight_genericPoint] at this
      exact absurd this (by decide)
  refine ⟨hnc, fun D => hDeq D, fun D => hDeq D, fun P' => ?_, hB'eq ▸ hnew, fun F' hF' => ?_⟩
  · obtain ⟨P, -, hPP', -⟩ := hover P'
    exact ⟨P, fun D => hcoeffD D P P' hPP'⟩
  -- the comparison still vanishes along the primes of positive coefficient
  obtain ⟨-, W', _, _, _, sW', p', q', h', hW', hW's, hp'Y, hq'Z, hp', hq', hp'b, hq'b, hinv',
    hhq', GY', GZ', hGY', hGZ', htrans⟩ :=
    hφ.isNefWeakModel_and_exists_model_of_negativeStep sX' πX' g' φ' hX'p hX'Q hπ' hstepL hcomp
  haveI : IsProper p' := isProper_of_isProjectiveMorphism p' hp'
  haveI : IsSeparated sW' := hW'.toIsSeparated
  haveI : IsSeparated (W' ↘ CategoryTheory.Limits.terminal Scheme) := by
    rw [show (W' ↘ CategoryTheory.Limits.terminal Scheme) =
      sW' ≫ (Spec (.of ℂ) ↘ CategoryTheory.Limits.terminal Scheme) from
        CategoryTheory.Limits.terminal.hom_ext _ _]
    infer_instance
  have hcmp : ∀ G' ∈ F', ∀ PW' : MMP.Mori.PrimeDivisor W',
      RationalMap.transformPrimeDivisor h' G' = some PW' → (GY' - GZ').coeff PW' = 0 := by
    intro G' hG'F PW' hPW'h
    have hG'pos := hF' G' hG'F
    obtain ⟨P, hP, hPP', hhP⟩ := hover G'
    obtain ⟨G'', hG'', htr⟩ := himage P hP
    have hG''G' : G'' = G' :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hG''.trans hhP)
    subst hG''G'
    have hPpos : 0 < B.coeff P := by
      have := hcoeffB P G'' hPP'
      simp only [DivisorWithCoeffs.coeff_apply] at hG'pos ⊢
      rwa [this] at hG'pos
    obtain ⟨W, _, _, _, sW, p, q, h, GY, GZ, PW, hW, hpY, hqZ, hp, hq, hpb, hqb, hinvW, hhq, hGY,
      hGZ, hPW, h0⟩ := hCV P hPpos
    have heq : (GY' - GZ').coeff PW' = (GY - GZ).coeff PW :=
      htrans sW p q h hW hpY hqZ hp hq hpb hqb hinvW hhq hGY hGZ P G'' PW PW' htr
        ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p PW P).mp hPW)
        (genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hinv' hPW'h)
    exact heq.trans h0
  rw [hB'eq] at hGY' hGZ'
  exact ⟨W', inferInstance, inferInstance, inferInstance, sW', p', q', h', hW', hW's, hp'Y, hq'Z,
    hp', hq', hp'b, hq'b, hinv', hhq', GY', GZ', hGY', hGZ', hcmp⟩

end

section Good

variable {S : Scheme.{0}} {Z : ℕ → Scheme.{0}} [∀ i, IsIntegral (Z i)]
  [∀ i, IsLocallyNoetherian (Z i)] [∀ i, IsNormal (Z i)]
  (sS : S ⟶ Spec (.of ℂ)) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ)) [∀ i, QuasiCompact (sZ i)]
  (πZ : ∀ i, Z i ⟶ S)

/-- A good stage: a projective `ℚ`-factorial threefold over `S` with a canonical divisor, the
limit boundary real terminal, the boundaries converging to it, and beyond the threshold every
`C_i` real terminal with support `F` and the transported weak model of `(X, C_i)` with vanishing
comparison along `F`. -/
private def IsGood (s : Stage S Z) : Prop :=
  MMP.Mori.IsProjectiveVariety ℂ s.sX ∧ IsQFactorial s.sX ∧ s.πX ≫ sS = s.sX ∧
    topologicalKrullDim s.X = 3 ∧ (∃ m : ℕ, s.K.IsCanonicalDivisor s.sX m) ∧
    IsRealTerminalPair s.sX s.B ∧
    (∀ P, Tendsto (fun i => (s.C i).coeff P) atTop (𝓝 (s.B.coeff P))) ∧
    ∀ i, s.N ≤ i → IsRealTerminalPair s.sX (s.C i) ∧ (∀ P, 0 < (s.C i).coeff P ↔ P ∈ s.F) ∧
      IsNefWeakModel s.sX (sZ i) sS s.πX (πZ i) s.K (s.C i) (s.Φ i) ∧
      CompVanishesOn (sZ i) s.sX s.K (s.C i) (s.Φ i) s.F

/-- A step of the `(K + B)`-program from a stage, in the form of the conclusion. -/
private def IsStageStep (s : Stage S Z) (d : StepData s) : Prop :=
  IsExtremalRay ℝ (relativeClosedConeOfCurves s.sX s.πX :
      Set (RelativeNumericalCurveClasses s.sX s.πX)) d.R ∧
    (∀ (Γ : ProperCurve s.sX) (hΓ : Γ.IsContractedBy s.πX),
      Γ.relativeClass s.πX hΓ ∈ d.R →
      ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor s.X) (x : ℝ),
        IsRIntersectionNumber ℂ s.sX (logCanonicalDivisor s.K s.B) r L Γ x → x < 0) ∧
    IsRelativeContractionOfFace s.πX d.R d.f d.g ∧
    IsNegativeExtremalContraction ℂ s.sX d.sZs (logCanonicalDivisor s.K s.B) d.f ∧
    d.fp ≫ d.g = d.t.πX ∧
    (((IsBirationalMorphism d.f ∧ ∃ E : MMP.Mori.PrimeDivisor s.X,
          (MMP.Mori.exceptionalSet d.f : Set s.X) = E.support) ∧
        IsIso d.fp ∧ (∃ m : ℕ, d.t.K.IsCanonicalDivisor d.t.sX m) ∧
        d.t.B = flipTransform d.f d.fp s.B) ∨
      IsRealFlipStep s.sX d.sZs d.t.sX s.K s.B d.t.K d.t.B d.f d.fp)

/-- The transport of the boundaries and of the weak-model maps along a step. -/
private def IsTransport (s : Stage S Z) (d : StepData s) : Prop :=
  (∀ i, d.t.C i = flipTransform d.f d.fp (s.C i)) ∧ d.ψ.compHom d.f = d.fp.toRationalMap ∧
    ∃ _ : d.ψ.IsDominant, ∀ i, d.t.Φ i = d.ψ.comp (s.Φ i)

/-- Everything one step from a good non-nef stage provides. -/
private def IsGoodStep (s : Stage S Z) (d : StepData s) : Prop :=
  IsStageStep s d ∧ IsTransport s d ∧ IsGood sS sZ πZ d.t ∧ s.N ≤ d.t.N ∧
    MMP.Mori.IsProjectiveVariety ℂ d.sZs ∧
    (∀ i, d.t.N ≤ i → ∀ E : MMP.Mori.PrimeDivisor s.X,
      (E.support : Set s.X) ⊆ MMP.Mori.exceptionalSet d.f → (s.C i).coeff E = 0) ∧
    picardNumber d.t.sX ≤ picardNumber s.sX ∧
    (¬ IsRealFlipStep s.sX d.sZs d.t.sX s.K s.B d.t.K d.t.B d.f d.fp →
      picardNumber d.t.sX < picardNumber s.sX)

end Good

section Singularities

/-- The boundary of a real canonical pair is effective. -/
private theorem coeff_nonneg_of_isRealCanonicalPair {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : RDivisor X}
    (h : IsRealCanonicalPair sX B) (P : MMP.Mori.PrimeDivisor X) : 0 ≤ B.coeff P := by
  by_cases hP : B.coeff P = 0
  · exact hP.ge
  · exact (h.2.1 P hP).1.le

end Singularities

section Perturbation

/-- **Relative ampleness is open along convergent boundaries.** If `A + D₀` is `f`-ample on a
`ℚ`-factorial `X`, and `D_i → D₀` coefficientwise with `D_i` eventually equal to `D₀` outside a
finite set `F` of primes, then `A + D_i` is eventually `f`-ample. -/
private theorem eventually_isRelativelyAmple_add {X Y : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    {sY : Y ⟶ Spec (.of ℂ)} (hXQ : IsQFactorial sX) (hY : IsNormalVariety ℂ sY) (f : X ⟶ Y)
    [IsProper f] (hf : f ≫ sY = sX) (A : RDivisor X) {D : ℕ → RDivisor X} {D₀ : RDivisor X}
    (hA : IsRelativelyAmple f (A + D₀)) (F : Finset (MMP.Mori.PrimeDivisor X))
    (hsupp : ∀ᶠ i in atTop, ∀ P ∉ F, (D i).coeff P = D₀.coeff P)
    (hlim : ∀ P, Tendsto (fun i => (D i).coeff P) atTop (𝓝 (D₀.coeff P))) :
    ∀ᶠ i in atTop, IsRelativelyAmple f (A + D i) := by
  classical
  obtain ⟨δ, hδ, hδA⟩ := MMP.Flips.exists_pos_isRelativelyAmple_add_sum_smul ℂ sX sY hXQ.1 hY f
    hf hA (ι := F) (fun P => Finsupp.single P.1 (1 : ℝ))
    (fun P => isCartierCombination_of_isQFactorial_ph hXQ _)
  have hev : ∀ᶠ i in atTop, ∀ P : F, |(D i).coeff P - D₀.coeff P| < δ := by
    rw [Filter.eventually_all]
    intro P
    have h := ((hlim P).sub_const (D₀.coeff P))
    rw [sub_self] at h
    filter_upwards [h (Metric.ball_mem_nhds 0 hδ)] with i hi
    simpa [Real.dist_eq] using hi
  filter_upwards [hev, hsupp] with i hi hs
  have heq : A + D i = A + D₀ +
      ∑ P : F, ((D i).coeff P - D₀.coeff P) • Finsupp.single P.1 (1 : ℝ) := by
    rw [Finset.sum_coe_sort F
      (fun P => ((D i).coeff P - D₀.coeff P) • Finsupp.single P (1 : ℝ))]
    refine DivisorWithCoeffs.ext' fun Q => ?_
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
      Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
    by_cases hQ : Q ∈ F
    · rw [if_pos hQ]; ring
    · rw [if_neg hQ]
      have := hs Q hQ
      simp only [DivisorWithCoeffs.coeff_apply] at this
      rw [this]; ring
  rw [heq]
  exact hδA _ hi

end Perturbation

section Contractions

/-- **Late boundaries share the negativity of the limit.** If `f` is a `(K + B)`-negative
extremal contraction of a `ℚ`-factorial `X`, and `C_i → B` coefficientwise with `C_i` eventually
equal to `B` outside a finite set of primes, then `f` is `(K + C_i)`-negative for all late `i`. -/
private theorem IsNegativeExtremalContraction.eventually_of_tendsto {X Zs : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)} (hXQ : IsQFactorial sX) {K : Divisor X}
    {B : RDivisor X} {C : ℕ → RDivisor X} {f : X ⟶ Zs}
    (h : IsNegativeExtremalContraction ℂ sX sZs (logCanonicalDivisor K B) f)
    (F : Finset (MMP.Mori.PrimeDivisor X))
    (hsupp : ∀ᶠ i in atTop, ∀ P ∉ F, (C i).coeff P = B.coeff P)
    (hlim : ∀ P, Tendsto (fun i => (C i).coeff P) atTop (𝓝 (B.coeff P))) :
    ∀ᶠ i in atTop, IsNegativeExtremalContraction ℂ sX sZs (logCanonicalDivisor K (C i)) f := by
  have : IsProper f := h.isContraction.isProper
  have hA : IsRelativelyAmple f (-Divisor.toRDivisor K + -B) := by
    have := h.isRelativelyAntiAmple
    rwa [IsRelativelyAntiAmple, logCanonicalDivisor, neg_add] at this
  have hev := eventually_isRelativelyAmple_add hXQ h.isNormalVariety_target f
    h.isContraction.comp_eq (-Divisor.toRDivisor K) (D := fun i => -C i) hA F
    (hsupp.mono fun i hi P hP => by
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_neg, Pi.neg_apply] at hi ⊢
      rw [hi P hP])
    (fun P => by simpa [DivisorWithCoeffs.coeff_apply] using (hlim P).neg)
  filter_upwards [hev] with i hi
  exact
    { isNormalVariety_source := h.isNormalVariety_source
      isNormalVariety_target := h.isNormalVariety_target
      isCartierCombination := isCartierCombination_of_isQFactorial_ph hXQ _
      isContraction := h.isContraction
      isRelativelyAntiAmple := by
        rw [IsRelativelyAntiAmple, logCanonicalDivisor, neg_add]; exact hi
      relativePicardNumber_eq_one := h.relativePicardNumber_eq_one }

end Contractions

section StepHelpers

/-- A negative extremal contraction of a ray is negative on every curve of the ray. -/
private theorem rayNeg_of_isNegativeExtremalContraction {X S Zs : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    {sZs : Zs ⟶ Spec (.of ℂ)} {πX : X ⟶ S} {R : Set (RelativeNumericalCurveClasses sX πX)}
    {f : X ⟶ Zs} {g : Zs ⟶ S} {E : RDivisor X} (hcont : IsRelativeContractionOfFace πX R f g)
    (h : IsNegativeExtremalContraction ℂ sX sZs E f) :
    ∀ (Γ : ProperCurve sX) (hΓ : Γ.IsContractedBy πX), Γ.relativeClass πX hΓ ∈ R →
      ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
        IsRIntersectionNumber ℂ sX E r L Γ x → x < 0 := by
  intro Γ hΓ hRΓ
  have hZv := h.isNormalVariety_target
  haveI : QuasiCompact sX := h.isNormalVariety_source.1.toQuasiCompact
  haveI : IsNormal Zs := hZv.2
  haveI : LocallyOfFiniteType sZs := hZv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Zs := LocallyOfFiniteType.isLocallyNoetherian sZs
  haveI : IsProper f := h.isContraction.isProper
  exact neg_of_isRelativelyAntiAmple h.isNormalVariety_source hZv f h.isContraction.comp_eq
    h.isRelativelyAntiAmple Γ ((hcont.isContractedBy_iff Γ hΓ).mpr hRΓ)

/-- The locus of the base over which both contractions of a step are isomorphisms pulls back to
a dense open along every dominant morphism. -/
private theorem dense_preimage_inf_biregularLocus {X X' Zs T : Scheme.{0}} [IsIntegral Zs]
    [IsLocallyNoetherian Zs] [IsNormal Zs] [IsIntegral X] [IsIntegral X'] [IsIntegral T]
    {f : X ⟶ Zs} {fp : X' ⟶ Zs} [IsProper f] [IsProper fp] (hfb : IsBirationalMorphism f)
    (hfpb : IsBirationalMorphism fp) (u : T ⟶ Zs) [IsDominant u] :
    Dense ((u ⁻¹ᵁ (biregularLocus f ⊓ biregularLocus fp) : T.Opens) : Set T) := by
  refine (u ⁻¹ᵁ (biregularLocus f ⊓ biregularLocus fp)).isOpen.dense ⟨genericPoint T, ?_⟩
  change u (genericPoint T) ∈ biregularLocus f ⊓ biregularLocus fp
  rw [MMP.Positivity.map_genericPoint_eq_of_isDominant u]
  have hz : Order.coheight (genericPoint Zs) ≤ 1 := by
    rw [Order.coheight_eq_zero.mpr fun b _ => genericPoint_specializes b]
    exact zero_le_one
  exact ⟨MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f hfb hz,
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal fp hfpb hz⟩

/-- The inverse of the step map, followed by `f`, is `f⁺`. -/
private theorem stepIso_symm_compHom {X X' Zs : Scheme.{0}} [IsIntegral X']
    [IsSeparated (Zs ↘ CategoryTheory.Limits.terminal Scheme)] (f : X ⟶ Zs) (fp : X' ⟶ Zs)
    (h1 : Dense ((f ⁻¹ᵁ (biregularLocus f ⊓ biregularLocus fp) : X.Opens) : Set X))
    (h2 : Dense ((fp ⁻¹ᵁ (biregularLocus f ⊓ biregularLocus fp) : X'.Opens) : Set X')) :
    (stepIso f fp h1 h2).symm.toRationalMap.compHom f = fp.toRationalMap := by
  set U := biregularLocus f ⊓ biregularLocus fp with hU
  haveI : IsIso (f ∣_ U) := isBiregular_iff_le_biregularLocus.mpr inf_le_left
  haveI : IsIso (fp ∣_ U) := isBiregular_iff_le_biregularLocus.mpr inf_le_right
  have hhom : (stepIso f fp h1 h2).symm.toPartialMap.hom ≫ f = (fp ⁻¹ᵁ U).ι ≫ fp := by
    change ((asIso (fp ∣_ U)).hom ≫ (asIso (f ∣_ U)).inv) ≫ (f ⁻¹ᵁ U).ι ≫ f = _
    simp only [asIso_hom, asIso_inv, Category.assoc]
    rw [← morphismRestrict_ι f U, IsIso.inv_hom_id_assoc, morphismRestrict_ι fp U]
  show ((stepIso f fp h1 h2).symm.toPartialMap.toRationalMap).compHom f =
    fp.toPartialMap.toRationalMap
  rw [← Scheme.RationalMap.compHom_toRationalMap]
  exact Scheme.PartialMap.toRationalMap_eq_iff.mpr
    ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated
      (S := CategoryTheory.Limits.terminal Scheme)).mpr hhom)

open Classical in
/-- The coefficient of the indicator divisor of a finite set of primes. -/
private theorem coeff_sum_single_one {X : Scheme.{0}} (F : Finset (MMP.Mori.PrimeDivisor X))
    (P : MMP.Mori.PrimeDivisor X) :
    (∑ Q ∈ F, Finsupp.single Q (1 : ℝ) : RDivisor X).coeff P = if P ∈ F then 1 else 0 := by
  classical
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.single_apply]
  exact Finset.sum_ite_eq' F P (fun _ => (1 : ℝ))

end StepHelpers

section Step

variable {S : Scheme.{0}} {Z : ℕ → Scheme.{0}} [∀ i, IsIntegral (Z i)]
  [∀ i, IsLocallyNoetherian (Z i)] [∀ i, IsNormal (Z i)]
  {sS : S ⟶ Spec (.of ℂ)} {sZ : ∀ i, Z i ⟶ Spec (.of ℂ)} [∀ i, QuasiCompact (sZ i)]
  {πZ : ∀ i, Z i ⟶ S}

/-- **One step of the program.** A good stage at which `K + B` is not nef over `S` admits a
step of the `(K + B)`-program after which the stage is still good. -/
private theorem exists_isGoodStep (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hZQ : ∀ i, IsQFactorial (sZ i)) {s : Stage S Z} (hs : IsGood sS sZ πZ s)
    (hnef : ¬ IsRelativelyNef ℂ s.sX s.πX (logCanonicalDivisor s.K s.B)) :
    ∃ d : StepData s, IsGoodStep sS sZ πZ s d := by
  obtain ⟨hXp, hXQ, hπ, hdim, hK, hBT, hlim, hlate⟩ := hs
  haveI : IsSeparated sS := hS.toIsVariety.toIsSeparated
  have hklt := isRealKltPair_of_isRealTerminalPair hBT
  have hB0 : 0 ≤ s.B := Finsupp.le_def.mpr fun P => coeff_nonneg_of_isRealCanonicalPair hBT.1 P
  obtain ⟨R, Zs, _, _, _, sZs, f, g, hR, hneg, hcont, hZsp, hnegc, hdivQ, hsmall⟩ :=
    IsRealKltPair.exists_isRelativeContractionOfFace_of_not_isRelativelyNef hXp hS hπ hXQ hdim hK
      hB0 hklt hnef
  -- outside `F` the late boundaries and the limit vanish
  have hCF : ∀ i, s.N ≤ i → ∀ P ∉ s.F, (s.C i).coeff P = 0 := fun i hi P hP =>
    le_antisymm (not_lt.mp fun h => hP (((hlate i hi).2.1 P).mp h))
      (coeff_nonneg_of_isRealCanonicalPair (hlate i hi).1.1 P)
  have hBF : ∀ P ∉ s.F, s.B.coeff P = 0 := fun P hP =>
    tendsto_nhds_unique (hlim P) (tendsto_const_nhds.congr' (eventually_atTop.mpr
      ⟨s.N, fun i hi => (hCF i hi P hP).symm⟩))
  have hsupp : ∀ᶠ i in atTop, ∀ P ∉ s.F, (s.C i).coeff P = s.B.coeff P :=
    eventually_atTop.mpr ⟨s.N, fun i hi P hP => by rw [hCF i hi P hP, hBF P hP]⟩
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    ((IsNegativeExtremalContraction.eventually_of_tendsto hXQ hnegc s.F hsupp hlim).and
      (eventually_ge_atTop s.N))
  -- the common setting of the step
  have hZv := hnegc.isNormalVariety_target
  haveI : QuasiCompact sZs := hZv.1.toQuasiCompact
  haveI : CompactSpace Zs := QuasiCompact.compactSpace_of_compactSpace sZs
  haveI : IsSeparated sZs := hZv.1.toIsSeparated
  haveI hZsep : IsSeparated (Zs ↘ CategoryTheory.Limits.terminal Scheme) := by
    rw [show (Zs ↘ CategoryTheory.Limits.terminal Scheme) =
      sZs ≫ (Spec (.of ℂ) ↘ CategoryTheory.Limits.terminal Scheme) from
        CategoryTheory.Limits.terminal.hom_ext _ _]
    infer_instance
  have hfs : f ≫ sZs = s.sX := hnegc.isContraction.comp_eq
  haveI : IsProper f := hnegc.isContraction.isProper
  have hgS : g ≫ sS = sZs := comp_eq_of_isRelativeContractionOfFace hcont hnegc hπ
  -- the indicator of the common support
  set Ind : RDivisor s.X := ∑ Q ∈ s.F, Finsupp.single Q (1 : ℝ) with hInd
  rcases trichotomy_of_isRelativeContractionOfFace hXp hXQ hS hZsp hπ hR hcont
    hnegc.isContraction.comp_eq hnegc.isNormalVariety_target with hfib | hdiv | hsm
  · exfalso
    obtain ⟨hnegi, hNi⟩ := hN₁ N₁ le_rfl
    exact ((hlate N₁ hNi).2.2.1.isNefWeakModel_of_negativeStep hXQ (hZQ N₁)).2 sZs g f hnegi
      hcont.comp_eq hfib
  · -- a divisorial contraction, followed by the identity of its target
    obtain ⟨hZsQ, -⟩ := hdivQ hdiv
    obtain ⟨hbir, E₀, hE₀⟩ := hdiv
    have hdZ : topologicalKrullDim Zs = 3 := by
      haveI : MMP.Mori.IsVariety ℂ sZs := hZv.1
      haveI : MMP.Mori.IsVariety ℂ s.sX := hXQ.1.1
      rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZs s.sX hbir, hdim]
    obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sZs hZv hdZ
    haveI : IsDominant f := hbir.isDominant
    have hd1 := dense_preimage_inf_biregularLocus hbir (isBirationalMorphism_of_isIso (𝟙 Zs)) f
    have hd2 := dense_preimage_inf_biregularLocus hbir (isBirationalMorphism_of_isIso (𝟙 Zs))
      (𝟙 Zs)
    haveI hψd : (stepIso f (𝟙 Zs) hd1 hd2).symm.toRationalMap.IsDominant :=
      isDominant_of_isBirational_ph (MMP.Mori.RationalMap.isBirational_toRationalMap _)
    have hX' : MMP.Mori.IsProjectiveVariety ℂ sZs ∧ IsQFactorial sZs ∧ g ≫ sS = sZs :=
      ⟨hZsp, hZsQ, hgS⟩
    have hstepC : ∀ i, N₁ ≤ i → IsStep s.sX sZs sZs s.πX g s.K (s.C i) K₀
        (flipTransform f (𝟙 Zs) (s.C i)) R f g (𝟙 Zs) := fun i hi =>
      ⟨hR, rayNeg_of_isNegativeExtremalContraction hcont (hN₁ i hi).1, hcont, (hN₁ i hi).1,
        Category.id_comp g, Or.inl ⟨⟨hbir, E₀, hE₀⟩, inferInstance, ⟨3, hK₀⟩, rfl⟩⟩
    have hEx₀ : ∀ G : MMP.Mori.PrimeDivisor s.X,
        (MMP.Mori.exceptionalSet f : Set s.X) = G.support →
          MMP.Mori.RationalMap.IsExceptional f.toRationalMap G := fun G hG =>
      isExceptional_of_genericPoint_mem_exceptionalSet f hbir G (by
        rw [hG, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
    have hWM := fun i (hi : N₁ ≤ i) =>
      weakModel_step' hS (hZQ i) hXp hXQ hπ (hlate i (hN₁ i hi).2).1
        (hlate i (hN₁ i hi).2).2.2.1 (hlate i (hN₁ i hi).2).2.1 (hlate i (hN₁ i hi).2).2.2.2 hK
        hX' (hstepC i hi) hd1 hd2 fun _ =>
          ⟨f, (stepIso_id_toRationalMap f hd1 hd2).symm, hcont.comp_eq, (hN₁ i hi).1, hbir,
            ⟨E₀, flips_exceptionalSet_eq_of_mori f hbir hE₀⟩, hEx₀⟩
    have hWMN := hWM N₁ le_rfl
    -- the contracted prime is not in the support
    have hE₀F : E₀ ∉ s.F := fun hmem => by
      have h0 := hWMN.1 E₀ hE₀.ge
      have := ((hlate N₁ (hN₁ N₁ le_rfl).2).2.1 E₀).mpr hmem
      rw [h0] at this
      exact lt_irrefl _ this
    have hBE₀ : s.B.coeff E₀ = 0 := hBF E₀ hE₀F
    -- the coefficients of the transforms
    obtain hcorr := hWMN.2.2.2.1
    have hmemF : ∀ (P' : MMP.Mori.PrimeDivisor Zs) (P : MMP.Mori.PrimeDivisor s.X),
        (∀ D : RDivisor s.X, (flipTransform f (𝟙 Zs) D).coeff P' = D.coeff P) →
        (P' ∈ (flipTransform f (𝟙 Zs) Ind).support ↔ P ∈ s.F) := by
      intro P' P hP
      rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, hP, hInd,
        coeff_sum_single_one]
      split_ifs with h <;> simp [h]
    have hKt : ∃ m : ℕ, Divisor.IsCanonicalDivisor sZs m
        (RationalMap.transformDivisor (stepIso f (𝟙 Zs) hd1 hd2).toRationalMap s.K) := by
      obtain ⟨m, hKm⟩ := hK
      have hm : m = 3 := by
        have h1 := hKm.1
        rw [hdim] at h1
        exact_mod_cast h1.symm
      subst hm
      refine ⟨3, ?_⟩
      rw [hWMN.2.1 s.K]
      change Divisor.IsCanonicalDivisor sZs 3 (inverseTransformDivisor (𝟙 Zs)
        (RationalMap.transformDivisor f.toRationalMap s.K))
      rw [MMP.Fourfold.inverseTransformDivisor_id]
      haveI : LocallyOfFiniteType sZs := hZv.1.toLocallyOfFiniteType
      haveI : LocallyOfFiniteType (f ≫ sZs) := by rw [hfs]; exact hXQ.1.1.toLocallyOfFiniteType
      haveI : IsDominant f := hbir.isDominant
      exact MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hZv
        (by rw [hfs]; exact hXQ.1) hbir hK₀ (by rw [hfs]; exact hKm)
    let t : Stage S Z := ⟨Zs, sZs, g,
      RationalMap.transformDivisor (stepIso f (𝟙 Zs) hd1 hd2).toRationalMap s.K,
      flipTransform f (𝟙 Zs) s.B, fun i => flipTransform f (𝟙 Zs) (s.C i),
      fun i => (stepIso f (𝟙 Zs) hd1 hd2).symm.toRationalMap.comp (s.Φ i), N₁,
      (flipTransform f (𝟙 Zs) Ind).support⟩
    let d : StepData s := ⟨t, R, Zs, sZs, f, g, 𝟙 Zs, (stepIso f (𝟙 Zs) hd1 hd2).symm.toRationalMap⟩
    have hρ := picardNumber_lt_of_isStep hS (hstepC N₁ le_rfl) hXp hπ hZsp hgS
      ⟨⟨hbir, E₀, hE₀⟩, inferInstance⟩
    refine ⟨d, ⟨hR, hneg, hcont, hnegc, Category.id_comp g,
      Or.inl ⟨⟨hbir, E₀, hE₀⟩, inferInstance, hKt, rfl⟩⟩,
      ⟨fun i => rfl, stepIso_symm_compHom f (𝟙 Zs) hd1 hd2, hψd, fun i => rfl⟩, ?_,
      (hN₁ N₁ le_rfl).2, hZsp, fun i hi => (hWM i hi).1, hρ.le, fun _ => hρ⟩
    refine ⟨hZsp, hZsQ, hgS, hdZ, hKt,
      isRealTerminalPair_of_divisorial hnegc hbir hE₀ (Category.id_comp sZs) hK ⟨3, hK₀⟩ hBE₀
        hBT hXp hZsQ, fun P' => ?_, fun i hi => ?_⟩
    · obtain ⟨P, hP⟩ := hcorr P'
      change Tendsto (fun i => (flipTransform f (𝟙 Zs) (s.C i)).coeff P') atTop
        (𝓝 ((flipTransform f (𝟙 Zs) s.B).coeff P'))
      simp only [hP]
      exact hlim P
    · have hiN : s.N ≤ i := (hN₁ N₁ le_rfl).2.trans hi
      have hW := hWM i hi
      refine ⟨isRealTerminalPair_of_divisorial (hN₁ i hi).1 hbir hE₀ (Category.id_comp sZs) hK
        ⟨3, hK₀⟩ (hW.1 E₀ hE₀.ge) (hlate i hiN).1 hXp hZsQ, fun P' => ?_, hW.2.2.2.2.1,
        hW.2.2.2.2.2 _ fun P' hP' => ?_⟩
      · obtain ⟨P, hP⟩ := hcorr P'
        change 0 < (flipTransform f (𝟙 Zs) (s.C i)).coeff P' ↔
          P' ∈ (flipTransform f (𝟙 Zs) Ind).support
        rw [hP, hmemF P' P hP]
        exact (hlate i hiN).2.1 P
      · obtain ⟨P, hP⟩ := hcorr P'
        rw [hP]
        exact ((hlate i hiN).2.1 P).mpr ((hmemF P' P hP).mp hP')
  · -- a small contraction, followed by its real flip
    obtain ⟨X', _, _, _, _, sX', K₀, fp, hfl, hX'p, hX'Q, hdim', -⟩ := hsmall hsm
    have hfps : fp ≫ sZs = sX' := hfl.isSmall_flip.comp_eq
    haveI : IsProper fp := hfl.isSmall_flip.isProper
    have hfb : IsBirationalMorphism f := hfl.isBirationalMorphism
    have hfpb : IsBirationalMorphism fp := hfl.isBirationalMorphism_flip
    haveI : IsDominant f := hfb.isDominant
    haveI : IsDominant fp := hfpb.isDominant
    have hd1 := dense_preimage_inf_biregularLocus hfb hfpb f
    have hd2 := dense_preimage_inf_biregularLocus hfb hfpb fp
    haveI hψd : (stepIso f fp hd1 hd2).symm.toRationalMap.IsDominant :=
      isDominant_of_isBirational_ph (MMP.Mori.RationalMap.isBirational_toRationalMap _)
    have hπ' : (fp ≫ g) ≫ sS = sX' := by rw [Category.assoc, hgS, hfps]
    have hX' : MMP.Mori.IsProjectiveVariety ℂ sX' ∧ IsQFactorial sX' ∧ (fp ≫ g) ≫ sS = sX' :=
      ⟨hX'p, hX'Q, hπ'⟩
    -- the coefficients of the transforms
    have hcorr : ∀ P' : MMP.Mori.PrimeDivisor X', ∃ P : MMP.Mori.PrimeDivisor s.X,
        ∀ D : RDivisor s.X, (flipTransform f fp D).coeff P' = D.coeff P := by
      intro P'
      obtain ⟨P, hPP'⟩ := exists_primeDivisor_map_eq_of_isSmall_ph hfl.isSmall_flip hfl.isSmall P'
      exact ⟨P, fun D => flipTransform_apply_of_isSmall_ph hZv hfl.isSmall hfl.isSmall_flip hfb
        hPP'.symm D⟩
    have hmemF : ∀ (P' : MMP.Mori.PrimeDivisor X') (P : MMP.Mori.PrimeDivisor s.X),
        (∀ D : RDivisor s.X, (flipTransform f fp D).coeff P' = D.coeff P) →
        (P' ∈ (flipTransform f fp Ind).support ↔ P ∈ s.F) := by
      intro P' P hP
      rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, hP, hInd,
        coeff_sum_single_one]
      split_ifs with h <;> simp [h]
    -- the late boundaries flip too
    have hsupp' : ∀ᶠ i in atTop, ∀ P' ∉ (flipTransform f fp Ind).support,
        (flipTransform f fp (s.C i)).coeff P' = (flipTransform f fp s.B).coeff P' :=
      eventually_atTop.mpr ⟨s.N, fun i hi P' hP' => by
        obtain ⟨P, hP⟩ := hcorr P'
        have hPF : P ∉ s.F := fun h => hP' ((hmemF P' P hP).mpr h)
        rw [hP, hP, hCF i hi P hPF, hBF P hPF]⟩
    have hlim' : ∀ P', Tendsto (fun i => (flipTransform f fp (s.C i)).coeff P') atTop
        (𝓝 ((flipTransform f fp s.B).coeff P')) := fun P' => by
      obtain ⟨P, hP⟩ := hcorr P'
      simp only [hP]
      exact hlim P
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
      ((eventually_isRelativelyAmple_add hX'Q hZv fp hfps (Divisor.toRDivisor K₀)
        hfl.isRelativelyAmple_flip _ hsupp' hlim').and (eventually_ge_atTop N₁))
    have hflC : ∀ i, N₂ ≤ i → IsRealFlipStep s.sX sZs sX' s.K (s.C i) K₀
        (flipTransform f fp (s.C i)) f fp := fun i hi =>
      { hfl with
        isNegativeExtremalContraction := (hN₁ i (hN₂ i hi).2).1
        isRelativelyAmple_flip := (hN₂ i hi).1
        eq_flipTransform := rfl }
    have hstepC : ∀ i, N₂ ≤ i → IsStep s.sX sX' sZs s.πX (fp ≫ g) s.K (s.C i) K₀
        (flipTransform f fp (s.C i)) R f g fp := fun i hi =>
      ⟨hR, rayNeg_of_isNegativeExtremalContraction hcont (hN₁ i (hN₂ i hi).2).1, hcont,
        (hN₁ i (hN₂ i hi).2).1, rfl, Or.inr (hflC i hi)⟩
    have hNN : ∀ i, N₂ ≤ i → s.N ≤ i := fun i hi => (hN₁ i (hN₂ i hi).2).2
    have hWM := fun i (hi : N₂ ≤ i) =>
      weakModel_step' hS (hZQ i) hXp hXQ hπ (hlate i (hNN i hi)).1
        (hlate i (hNN i hi)).2.2.1 (hlate i (hNN i hi)).2.1 (hlate i (hNN i hi)).2.2.2 hK
        hX' (hstepC i hi) hd1 hd2 fun h => absurd h hfl.not_isIso_flip
    have hWMN := hWM N₂ le_rfl
    -- the canonical divisor of the flip
    have hKt : ∃ m : ℕ, Divisor.IsCanonicalDivisor sX' m
        (RationalMap.transformDivisor (stepIso f fp hd1 hd2).toRationalMap s.K) := by
      obtain ⟨m, hKm⟩ := hK
      obtain ⟨V, hVf, hVfp, hXV, hX'V⟩ := hfl.exists_opens_isIso
      haveI := hVf
      haveI := hVfp
      refine ⟨m, ?_⟩
      rw [hWMN.2.1 s.K]
      have := MMP.Mori.isCanonicalDivisor_flipTransform_of_isIso_restrict (k := ℂ) hZv
        (f := f) (fp := fp) (by rw [hfs]; exact hXQ.1) (by rw [hfps]; exact hX'Q.1) hfb hfpb V
        hXV hX'V (n := m) (K := s.K) (by rw [hfs]; exact hKm)
      rwa [hfps] at this
    have hflB : IsRealFlipStep s.sX sZs sX' s.K s.B
        (RationalMap.transformDivisor (stepIso f fp hd1 hd2).toRationalMap s.K)
        (flipTransform f fp s.B) f fp := by
      obtain ⟨mt, hKtm⟩ := hKt
      obtain ⟨m₀, hK₀m⟩ := hfl.isCanonicalDivisor_flip
      exact
        { hfl with
          isCanonicalDivisor_flip := ⟨mt, hKtm⟩
          isRelativelyAmple_flip := isRelativelyAmple_of_linearlyEquivalent hX'Q.1 hZv hfps
            (isCartierCombination_of_isQFactorial_ph hX'Q _) hfl.isRelativelyAmple_flip
            (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX' hX'Q.1 hKtm hK₀m) }
    let t : Stage S Z := ⟨X', sX', fp ≫ g,
      RationalMap.transformDivisor (stepIso f fp hd1 hd2).toRationalMap s.K,
      flipTransform f fp s.B, fun i => flipTransform f fp (s.C i),
      fun i => (stepIso f fp hd1 hd2).symm.toRationalMap.comp (s.Φ i), N₂,
      (flipTransform f fp Ind).support⟩
    let d : StepData s := ⟨t, R, Zs, sZs, f, g, fp, (stepIso f fp hd1 hd2).symm.toRationalMap⟩
    have hρ := picardNumber_eq_of_isRealFlipStep hflB hXQ hXp hX'Q hX'p
    refine ⟨d, ⟨hR, hneg, hcont, hnegc, rfl, Or.inr hflB⟩,
      ⟨fun i => rfl, stepIso_symm_compHom f fp hd1 hd2, hψd, fun i => rfl⟩, ?_,
      hNN N₂ le_rfl, hZsp, fun i hi => (hWM i hi).1,
      hρ.le, fun h => absurd hflB h⟩
    refine ⟨hX'p, hX'Q, hπ', hdim', hKt,
      isRealTerminalPair_of_isRealFlipStep hflB hK hBT hXp hX'Q,
      hlim', fun i hi => ?_⟩
    have hW := hWM i hi
    refine ⟨isRealTerminalPair_of_isRealFlipStep (hflC i hi) hK (hlate i (hNN i hi)).1 hXp
        hX'Q,
      fun P' => ?_, hW.2.2.2.2.1, hW.2.2.2.2.2 _ fun P' hP' => ?_⟩
    · obtain ⟨P, hP⟩ := hcorr P'
      change 0 < (flipTransform f fp (s.C i)).coeff P' ↔ P' ∈ (flipTransform f fp Ind).support
      rw [hP, hmemF P' P hP]
      exact (hlate i (hNN i hi)).2.1 P
    · obtain ⟨P, hP⟩ := hcorr P'
      rw [hP]
      exact ((hlate i (hNN i hi)).2.1 P).mpr ((hmemF P' P hP).mp hP')

/-- A sequence of natural numbers (in `ℕ∞`, all finite) that never increases and drops whenever
`P` fails is eventually in `P`. -/
private theorem exists_forall_of_antitone {ρ : ℕ → ℕ∞} {P : ℕ → Prop} (hfin : ∀ j, ρ j < ⊤)
    (hle : ∀ j, ρ (j + 1) ≤ ρ j) (hlt : ∀ j, ¬ P j → ρ (j + 1) < ρ j) :
    ∃ M, ∀ j, M ≤ j → P j := by
  have key : ∀ v : ℕ, ∀ j0, ρ j0 ≤ v → ∃ M, ∀ j, M ≤ j → P j := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
      intro j0 hj0
      by_contra hcon
      push Not at hcon
      obtain ⟨j, hj, hPj⟩ := hcon j0
      have hmono : ∀ j', j0 ≤ j' → ρ j' ≤ ρ j0 := by
        intro j' hj'
        induction j', hj' using Nat.le_induction with
        | base => exact le_rfl
        | succ j' _ ih' => exact (hle j').trans ih'
      have h1 : ρ (j + 1) < v := ((hlt j hPj).trans_le (hmono j hj)).trans_le hj0
      obtain ⟨w, hw⟩ : ∃ w : ℕ, ρ (j + 1) = w := ENat.ne_top_iff_exists.mp (hfin _).ne |>.imp
        fun _ h => h.symm
      rw [hw] at h1
      obtain ⟨M, hM⟩ := ih w (by exact_mod_cast h1) (j + 1) hw.le
      exact absurd (hcon M) (by push Not; exact hM)
  obtain ⟨w, hw⟩ : ∃ w : ℕ, ρ 0 = w := ENat.ne_top_iff_exists.mp (hfin 0).ne |>.imp
    fun _ h => h.symm
  exact key w 0 hw.le

/-- **No infinite flip tail.** The steps of an infinite sequence of good stages cannot all be
real flips from some point on: their limit boundaries stay real canonical, and real canonical
flip sequences of projective threefolds terminate. -/
private theorem false_of_forall_isRealFlipStep (s0 : Stage S Z)
    (next : (s : Stage S Z) → StepData s) (M : ℕ)
    (hgood : ∀ j, IsGood sS sZ πZ (Stage.seq s0 next j))
    (hZp : ∀ j, MMP.Mori.IsProjectiveVariety ℂ (next (Stage.seq s0 next j)).sZs)
    (hflip : ∀ j, M ≤ j → IsRealFlipStep (Stage.seq s0 next j).sX
      (next (Stage.seq s0 next j)).sZs (next (Stage.seq s0 next j)).t.sX
      (Stage.seq s0 next j).K (Stage.seq s0 next j).B (next (Stage.seq s0 next j)).t.K
      (next (Stage.seq s0 next j)).t.B (next (Stage.seq s0 next j)).f
      (next (Stage.seq s0 next j)).fp) : False := by
  set σ := Stage.seq s0 next with hσ
  let Y : ℕ → Scheme.{0} := fun i => (next (σ (M + i))).t.X
  let fσ : ∀ i, modelSeq (σ M).X Y i ⟶ (next (σ (M + i))).Zs := fun i =>
    match i with
    | 0 => (next (σ M)).f
    | j + 1 => (next (σ (M + (j + 1)))).f
  let τ : RealFlipSequence (σ M).sX (σ M).K (σ M).B :=
    { n := ⊤
      Y := Y
      sY := fun i => (next (σ (M + i))).t.sX
      KY := fun i => (next (σ (M + i))).t.K
      BY := fun i => (next (σ (M + i))).t.B
      Z := fun i => (next (σ (M + i))).Zs
      sZ := fun i => (next (σ (M + i))).sZs
      f := fσ
      fp := fun i => (next (σ (M + i))).fp
      isCanonicalDivisor := (hgood M).2.2.2.2.1
      isQFactorial := fun i _ => by
        cases i with
        | zero => exact (hgood M).2.1
        | succ j => exact (hgood (M + (j + 1))).2.1
      isQuasiProjectiveVariety := fun i _ => by
        cases i with
        | zero =>
          exact @AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ _ _ _
            (hgood M).1
        | succ j =>
          exact @AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ _ _ _
            (hgood (M + (j + 1))).1
      dim_eq := fun i _ => by
        cases i with
        | zero => exact (hgood M).2.2.2.1
        | succ j => exact (hgood (M + (j + 1))).2.2.2.1
      isRealFlipStep := fun i _ => by
        cases i with
        | zero => exact hflip M le_rfl
        | succ j => exact hflip (M + (j + 1)) (by omega) }
  refine RealFlipSequence.n_ne_top_of_isRealCanonicalPair τ (fun i _ => ?_) (fun i _ => ?_)
    (fun i _ => hZp (M + i)) rfl
  · cases i with
    | zero => exact (hgood M).2.2.2.2.2.1.1
    | succ j => exact (hgood (M + (j + 1))).2.2.2.2.2.1.1
  · cases i with
    | zero => exact (hgood M).1
    | succ j => exact (hgood (M + (j + 1))).1

end Step

private theorem solution
    {Y S : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {Z : ℕ → Scheme.{0}} [∀ i, IsIntegral (Z i)] [∀ i, IsLocallyNoetherian (Z i)]
    [∀ i, IsNormal (Z i)]
    {sY : Y ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {sZ : ∀ i, Z i ⟶ Spec (.of ℂ)}
    [∀ i, QuasiCompact (sZ i)]
    {π : Y ⟶ S} {πZ : ∀ i, Z i ⟶ S} {K : Divisor Y} {C : ℕ → RDivisor Y} {B : RDivisor Y}
    {F : Finset (MMP.Mori.PrimeDivisor Y)} {φ : ∀ i, Y.RationalMap (Z i)}
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hπ : π ≫ sS = sY) (hYQ : IsQFactorial sY) (hdim : topologicalKrullDim Y = 3)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sY n) (hC : ∀ i, IsRealTerminalPair sY (C i))
    (hF : ∀ i P, 0 < (C i).coeff P ↔ P ∈ F) (hB : IsRealTerminalPair sY B)
    (hlim : ∀ P, Tendsto (fun i => (C i).coeff P) atTop (𝓝 (B.coeff P)))
    (hZ : ∀ i, IsNefWeakModel sY (sZ i) sS π (πZ i) K (C i) (φ i))
    (hZQ : ∀ i, IsQFactorial (sZ i))
    (hcomp : ∀ i, ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
      (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z i) (h : Y.RationalMap W),
      MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧ q ≫ sZ i = sW ∧
        IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ IsBirationalMorphism p ∧
        IsBirationalMorphism q ∧ MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧
        h.compHom q = φ i ∧
        ∃ GY GZ : RDivisor W,
          IsRCartierPullback p (logCanonicalDivisor K (C i)) GY ∧
          IsRCartierPullback q
            (logCanonicalDivisor (RationalMap.transformDivisor (φ i) K)
              (RationalMap.transformDivisor (φ i) (C i))) GZ ∧
          ∀ P ∈ F, ∀ P' : MMP.Mori.PrimeDivisor W, RationalMap.transformPrimeDivisor h P = some P' →
            (GY - GZ).coeff P' = 0) :
    ∃ (n : ℕ) (Yi : ℕ → Scheme.{0}) (sYi : ∀ i, Yi i ⟶ Spec (.of ℂ))
      (_ : ∀ i, IsIntegral (Yi i)) (_ : ∀ i, CompactSpace (Yi i))
      (_ : ∀ i, IsLocallyNoetherian (Yi i)) (_ : ∀ i, IsNormal (Yi i)) (πY : ∀ i, Yi i ⟶ S)
      (KY : ∀ i, Divisor (Yi i)) (BY : ∀ i, RDivisor (Yi i))
      (R : ∀ i, Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap π πY i)))
      (Zi : ℕ → Scheme.{0}) (sZi : ∀ i, Zi i ⟶ Spec (.of ℂ)) (f : ∀ i, modelSeq Y Yi i ⟶ Zi i)
      (g : ∀ i, Zi i ⟶ S) (fp : ∀ i, Yi i ⟶ Zi i),
      (∀ j ≤ n,
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sY sYi j) ∧ IsQFactorial (modelStr sY sYi j) ∧
          modelMap π πY j ≫ sS = modelStr sY sYi j) ∧
      (∀ j < n,
        IsExtremalRay ℝ (relativeClosedConeOfCurves (modelStr sY sYi j) (modelMap π πY j) :
            Set (RelativeNumericalCurveClasses (modelStr sY sYi j) (modelMap π πY j))) (R j) ∧
          (∀ (Γ : ProperCurve (modelStr sY sYi j)) (hΓ : Γ.IsContractedBy (modelMap π πY j)),
            Γ.relativeClass (modelMap π πY j) hΓ ∈ R j →
            ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor (modelSeq Y Yi j)) (x : ℝ),
              IsRIntersectionNumber ℂ (modelStr sY sYi j)
                (logCanonicalDivisor (divisorSeq K KY j) (divisorSeq B BY j)) r L Γ x → x < 0) ∧
          IsRelativeContractionOfFace (modelMap π πY j) (R j) (f j) (g j) ∧
          IsNegativeExtremalContraction ℂ (modelStr sY sYi j) (sZi j)
            (logCanonicalDivisor (divisorSeq K KY j) (divisorSeq B BY j)) (f j) ∧
          fp j ≫ g j = πY j ∧
          (((IsBirationalMorphism (f j) ∧ ∃ E : MMP.Mori.PrimeDivisor (modelSeq Y Yi j),
                (MMP.Mori.exceptionalSet (f j) : Set (modelSeq Y Yi j)) = E.support) ∧
              IsIso (fp j) ∧ (∃ m : ℕ, (KY j).IsCanonicalDivisor (sYi j) m) ∧
              BY j = flipTransform (f j) (fp j) (divisorSeq B BY j)) ∨
            IsRealFlipStep (modelStr sY sYi j) (sZi j) (sYi j) (divisorSeq K KY j)
              (divisorSeq B BY j) (KY j) (BY j) (f j) (fp j))) ∧
      IsRelativelyNef ℂ (modelStr sY sYi n) (modelMap π πY n)
        (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq B BY n)) ∧
      topologicalKrullDim (modelSeq Y Yi n) = 3 ∧
      IsRealTerminalPair (modelStr sY sYi n) (divisorSeq B BY n) ∧
      ∃ (CY : ℕ → ∀ j, RDivisor (Yi j)) (ψ : ∀ j, (Yi j).RationalMap (modelSeq Y Yi j))
        (_ : ∀ j, (ψ j).IsDominant) (Φ : ∀ i j, (modelSeq Y Yi j).RationalMap (Z i))
        (N : ℕ) (F' : Finset (MMP.Mori.PrimeDivisor (modelSeq Y Yi n))),
        (∀ i, ∀ j < n, CY i j = flipTransform (f j) (fp j) (divisorSeq (C i) (CY i) j)) ∧
        (∀ j < n, (ψ j).compHom (f j) = (fp j).toRationalMap) ∧
        (∀ i, Φ i 0 = φ i) ∧ (∀ i, ∀ j < n, Φ i (j + 1) = (ψ j).comp (Φ i j)) ∧
        (∀ i, N ≤ i → ∀ j < n, ∀ E : MMP.Mori.PrimeDivisor (modelSeq Y Yi j),
          (E.support : Set (modelSeq Y Yi j)) ⊆ MMP.Mori.exceptionalSet (f j) →
            (divisorSeq (C i) (CY i) j).coeff E = 0) ∧
        (∀ i, N ≤ i → IsRealTerminalPair (modelStr sY sYi n) (divisorSeq (C i) (CY i) n)) ∧
        (∀ i, N ≤ i → ∀ P, 0 < (divisorSeq (C i) (CY i) n).coeff P ↔ P ∈ F') ∧
        (∀ P, Tendsto (fun i => (divisorSeq (C i) (CY i) n).coeff P) atTop
          (𝓝 ((divisorSeq B BY n).coeff P))) ∧
        ∀ i, N ≤ i →
          IsNefWeakModel (modelStr sY sYi n) (sZ i) sS (modelMap π πY n) (πZ i)
            (divisorSeq K KY n) (divisorSeq (C i) (CY i) n) (Φ i n) ∧
          ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
            (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ modelSeq Y Yi n) (q : W ⟶ Z i)
            (h : (modelSeq Y Yi n).RationalMap W),
            MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧
              p ≫ modelStr sY sYi n = sW ∧ q ≫ sZ i = sW ∧
              IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ IsBirationalMorphism p ∧
              IsBirationalMorphism q ∧ MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧
              h.compHom q = Φ i n ∧
              ∃ GY GZ : RDivisor W,
                IsRCartierPullback p
                  (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq (C i) (CY i) n)) GY ∧
                IsRCartierPullback q
                  (logCanonicalDivisor (RationalMap.transformDivisor (Φ i n) (divisorSeq K KY n))
                    (RationalMap.transformDivisor (Φ i n) (divisorSeq (C i) (CY i) n))) GZ ∧
                ∀ P ∈ F', ∀ P' : MMP.Mori.PrimeDivisor W,
                  RationalMap.transformPrimeDivisor h P = some P' → (GY - GZ).coeff P' = 0 := by
  classical
  let s0 : Stage S Z := ⟨Y, sY, π, K, B, C, φ, 0, F⟩
  have hgood0 : IsGood sS sZ πZ s0 :=
    ⟨hY, hYQ, hπ, hdim, hK, hB, hlim, fun i _ => ⟨hC i, hF i, hZ i, hcomp i⟩⟩
  have H : ∀ s : Stage S Z, ∃ d : StepData s, d.ψ.IsDominant ∧ (IsGood sS sZ πZ s →
      ¬ IsRelativelyNef ℂ s.sX s.πX (logCanonicalDivisor s.K s.B) →
        IsGoodStep sS sZ πZ s d) := by
    intro s
    by_cases h : IsGood sS sZ πZ s ∧ ¬ IsRelativelyNef ℂ s.sX s.πX (logCanonicalDivisor s.K s.B)
    · obtain ⟨d, hd⟩ := exists_isGoodStep hS hZQ h.1 h.2
      exact ⟨d, hd.2.1.2.2.1, fun _ _ => hd⟩
    · refine ⟨⟨s, ∅, s.X, s.sX, 𝟙 _, s.πX, 𝟙 _, Scheme.Hom.toRationalMap (𝟙 s.X)⟩, ?_,
        fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
      change (Scheme.Hom.toRationalMap (𝟙 s.X)).IsDominant
      infer_instance
  choose next hdom hnext using H
  set σ := Stage.seq s0 next with hσ
  have hgoodσ : ∀ j, (∀ j' < j, ¬ IsRelativelyNef ℂ (σ j').sX (σ j').πX
      (logCanonicalDivisor (σ j').K (σ j').B)) → IsGood sS sZ πZ (σ j) := by
    intro j
    induction j with
    | zero => intro _; exact hgood0
    | succ j ih =>
      intro hj
      exact (hnext (σ j) (ih fun j' hj' => hj j' (by omega)) (hj j (by omega))).2.2.1
  have hex : ∃ n, IsRelativelyNef ℂ (σ n).sX (σ n).πX
      (logCanonicalDivisor (σ n).K (σ n).B) := by
    by_contra hcon
    push Not at hcon
    have hg : ∀ j, IsGood sS sZ πZ (σ j) := fun j => hgoodσ j fun j' _ => hcon j'
    have hst : ∀ j, IsGoodStep sS sZ πZ (σ j) (next (σ j)) := fun j => hnext _ (hg j) (hcon j)
    obtain ⟨M, hM⟩ := exists_forall_of_antitone (ρ := fun j => picardNumber (σ j).sX)
      (P := fun j => IsRealFlipStep (σ j).sX (next (σ j)).sZs (next (σ j)).t.sX (σ j).K
        (σ j).B (next (σ j)).t.K (next (σ j)).t.B (next (σ j)).f (next (σ j)).fp)
      (fun j => by
        haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (σ j).sX := (hg j).1
        exact MMP.Mori.picardNumber_lt_top_of_isProjectiveVariety _)
      (fun j => (hst j).2.2.2.2.2.2.1) (fun j => (hst j).2.2.2.2.2.2.2)
    exact false_of_forall_isRealFlipStep s0 next M hg (fun j => (hst j).2.2.2.2.1) hM
  obtain ⟨n, hnef, hlt⟩ : ∃ n, IsRelativelyNef ℂ (σ n).sX (σ n).πX
      (logCanonicalDivisor (σ n).K (σ n).B) ∧ ∀ j < n, ¬ IsRelativelyNef ℂ (σ j).sX (σ j).πX
        (logCanonicalDivisor (σ j).K (σ j).B) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hg : ∀ j ≤ n, IsGood sS sZ πZ (σ j) := fun j hj => hgoodσ j fun j' hj' => hlt j' (by omega)
  have hst : ∀ j < n, IsGoodStep sS sZ πZ (σ j) (next (σ j)) := fun j hj =>
    hnext _ (hg j hj.le) (hlt j hj)
  have hN' : ∀ d j, j + d ≤ n → (σ j).N ≤ (σ (j + d)).N := by
    intro d
    induction d with
    | zero => intro j _; exact le_rfl
    | succ d ih =>
      intro j hj
      exact (ih j (by omega)).trans (hst (j + d) (by omega)).2.2.2.1
  have hN : ∀ j ≤ n, (σ j).N ≤ (σ n).N := fun j hj => by
    simpa [Nat.add_sub_cancel' hj] using hN' (n - j) j (by omega)
  refine ⟨n, fun j => (σ (j + 1)).X, fun j => (σ (j + 1)).sX, fun j => inferInstance,
    fun j => inferInstance, fun j => inferInstance, fun j => inferInstance,
    fun j => (σ (j + 1)).πX, fun j => (σ (j + 1)).K, fun j => (σ (j + 1)).B,
    Stage.progR s0 next, fun j => (next (σ j)).Zs, fun j => (next (σ j)).sZs,
    Stage.progF s0 next, fun j => (next (σ j)).g, fun j => (next (σ j)).fp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨h1, h2, h3, -⟩ := hg j hj
    cases j with
    | zero => exact ⟨h1, h2, h3⟩
    | succ j => exact ⟨h1, h2, h3⟩
  · intro j hj
    have h := (hst j hj).1
    cases j with
    | zero => exact h
    | succ j => exact h
  · have h := hnef
    cases n with
    | zero => exact h
    | succ m => exact h
  · have h := (hg n le_rfl).2.2.2.1
    cases n with
    | zero => exact h
    | succ m => exact h
  · have h := (hg n le_rfl).2.2.2.2.2.1
    cases n with
    | zero => exact h
    | succ m => exact h
  refine ⟨fun i j => (σ (j + 1)).C i, Stage.progψ s0 next, fun j => ?_,
    Stage.progΦ s0 next, (σ n).N, Stage.progFin s0 next n, ?_, ?_, fun i => rfl, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · cases j with
    | zero => exact hdom s0
    | succ j => exact hdom (σ (j + 1))
  · intro i j hj
    have h := (hst j hj).2.1.1 i
    cases j with
    | zero => exact h
    | succ j => exact h
  · intro j hj
    have h := (hst j hj).2.1.2.1
    cases j with
    | zero => exact h
    | succ j => exact h
  · intro i j hj
    obtain ⟨_, h⟩ := (hst j hj).2.1.2.2
    cases j with
    | zero => exact h i
    | succ j => exact h i
  · intro i hi j hj E hE
    have hi' := (hN (j + 1) hj).trans hi
    cases j with
    | zero => exact (hst 0 hj).2.2.2.2.2.1 i hi' E hE
    | succ j => exact (hst (j + 1) hj).2.2.2.2.2.1 i hi' E hE
  · intro i hi
    have h := ((hg n le_rfl).2.2.2.2.2.2.2 i hi).1
    cases n with
    | zero => exact h
    | succ m => exact h
  · intro i hi P
    have h := ((hg n le_rfl).2.2.2.2.2.2.2 i hi).2.1
    cases n with
    | zero => exact h P
    | succ m => exact h P
  · intro P
    have h := (hg n le_rfl).2.2.2.2.2.2.1
    cases n with
    | zero => exact h P
    | succ m => exact h P
  · intro i hi
    have h := ((hg n le_rfl).2.2.2.2.2.2.2 i hi).2.2
    cases n with
    | zero => exact h
    | succ m => exact h

end Proof_lem_fourfold_terminal_limit_nef_reduction

end

open CategoryTheory AlgebraicGeometry Filter Topology

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **A convergent terminal sequence can be made nef at its limit.** Let `π : Y ⟶ S` be a morphism
of projective complex varieties, `Y` a `ℚ`-factorial threefold with canonical divisor `K`, and let
`C_i` be real terminal boundaries with common finite positive support `F`, converging
coefficientwise to a real terminal boundary `B`, such that each `(Y, C_i)` has a `ℚ`-factorial nef
weak model `φ_i : Y ⤏ Z_i` over `S` with comparison coefficient zero along every prime of `F`.
Then some finite `(K + B)`-program over `S` ends with `K_n + B_n` nef over `S`, and for all `i`
beyond some `N` the transformed data on `Y_n` satisfy the same hypotheses (with `Z_i` a nef weak
model through the transported map), and no step contracts a prime of positive coefficient in
`C_i`. -/
@[mmp "lem_fourfold_terminal_limit_nef_reduction"]
public theorem IsRealTerminalPair.exists_isRelativelyNef_of_tendsto_of_isNefWeakModel
    {Y S : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {Z : ℕ → Scheme.{0}} [∀ i, IsIntegral (Z i)] [∀ i, IsLocallyNoetherian (Z i)]
    [∀ i, IsNormal (Z i)]
    {sY : Y ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {sZ : ∀ i, Z i ⟶ Spec (.of ℂ)}
    [∀ i, QuasiCompact (sZ i)]
    {π : Y ⟶ S} {πZ : ∀ i, Z i ⟶ S} {K : Divisor Y} {C : ℕ → RDivisor Y} {B : RDivisor Y}
    {F : Finset (MMP.Mori.PrimeDivisor Y)} {φ : ∀ i, Y.RationalMap (Z i)}
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hπ : π ≫ sS = sY) (hYQ : IsQFactorial sY) (hdim : topologicalKrullDim Y = 3)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sY n) (hC : ∀ i, IsRealTerminalPair sY (C i))
    (hF : ∀ i P, 0 < (C i).coeff P ↔ P ∈ F) (hB : IsRealTerminalPair sY B)
    (hlim : ∀ P, Tendsto (fun i => (C i).coeff P) atTop (𝓝 (B.coeff P)))
    (hZ : ∀ i, IsNefWeakModel sY (sZ i) sS π (πZ i) K (C i) (φ i))
    (hZQ : ∀ i, IsQFactorial (sZ i))
    (hcomp : ∀ i, ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
      (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z i) (h : Y.RationalMap W),
      MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧ q ≫ sZ i = sW ∧
        IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ IsBirationalMorphism p ∧
        IsBirationalMorphism q ∧ MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧
        h.compHom q = φ i ∧
        ∃ GY GZ : RDivisor W,
          IsRCartierPullback p (logCanonicalDivisor K (C i)) GY ∧
          IsRCartierPullback q
            (logCanonicalDivisor (RationalMap.transformDivisor (φ i) K)
              (RationalMap.transformDivisor (φ i) (C i))) GZ ∧
          ∀ P ∈ F, ∀ P' : MMP.Mori.PrimeDivisor W, RationalMap.transformPrimeDivisor h P = some P' →
            (GY - GZ).coeff P' = 0) :
    ∃ (n : ℕ) (Yi : ℕ → Scheme.{0}) (sYi : ∀ i, Yi i ⟶ Spec (.of ℂ))
      (_ : ∀ i, IsIntegral (Yi i)) (_ : ∀ i, CompactSpace (Yi i))
      (_ : ∀ i, IsLocallyNoetherian (Yi i)) (_ : ∀ i, IsNormal (Yi i)) (πY : ∀ i, Yi i ⟶ S)
      (KY : ∀ i, Divisor (Yi i)) (BY : ∀ i, RDivisor (Yi i))
      (R : ∀ i, Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap π πY i)))
      (Zi : ℕ → Scheme.{0}) (sZi : ∀ i, Zi i ⟶ Spec (.of ℂ)) (f : ∀ i, modelSeq Y Yi i ⟶ Zi i)
      (g : ∀ i, Zi i ⟶ S) (fp : ∀ i, Yi i ⟶ Zi i),
      (∀ j ≤ n,
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sY sYi j) ∧ IsQFactorial (modelStr sY sYi j) ∧
          modelMap π πY j ≫ sS = modelStr sY sYi j) ∧
      (∀ j < n,
        IsExtremalRay ℝ (relativeClosedConeOfCurves (modelStr sY sYi j) (modelMap π πY j) :
            Set (RelativeNumericalCurveClasses (modelStr sY sYi j) (modelMap π πY j))) (R j) ∧
          (∀ (Γ : ProperCurve (modelStr sY sYi j)) (hΓ : Γ.IsContractedBy (modelMap π πY j)),
            Γ.relativeClass (modelMap π πY j) hΓ ∈ R j →
            ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor (modelSeq Y Yi j)) (x : ℝ),
              IsRIntersectionNumber ℂ (modelStr sY sYi j)
                (logCanonicalDivisor (divisorSeq K KY j) (divisorSeq B BY j)) r L Γ x → x < 0) ∧
          IsRelativeContractionOfFace (modelMap π πY j) (R j) (f j) (g j) ∧
          IsNegativeExtremalContraction ℂ (modelStr sY sYi j) (sZi j)
            (logCanonicalDivisor (divisorSeq K KY j) (divisorSeq B BY j)) (f j) ∧
          fp j ≫ g j = πY j ∧
          (((IsBirationalMorphism (f j) ∧ ∃ E : MMP.Mori.PrimeDivisor (modelSeq Y Yi j),
                (MMP.Mori.exceptionalSet (f j) : Set (modelSeq Y Yi j)) = E.support) ∧
              IsIso (fp j) ∧ (∃ m : ℕ, (KY j).IsCanonicalDivisor (sYi j) m) ∧
              BY j = flipTransform (f j) (fp j) (divisorSeq B BY j)) ∨
            IsRealFlipStep (modelStr sY sYi j) (sZi j) (sYi j) (divisorSeq K KY j)
              (divisorSeq B BY j) (KY j) (BY j) (f j) (fp j))) ∧
      IsRelativelyNef ℂ (modelStr sY sYi n) (modelMap π πY n)
        (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq B BY n)) ∧
      topologicalKrullDim (modelSeq Y Yi n) = 3 ∧
      IsRealTerminalPair (modelStr sY sYi n) (divisorSeq B BY n) ∧
      ∃ (CY : ℕ → ∀ j, RDivisor (Yi j)) (ψ : ∀ j, (Yi j).RationalMap (modelSeq Y Yi j))
        (_ : ∀ j, (ψ j).IsDominant) (Φ : ∀ i j, (modelSeq Y Yi j).RationalMap (Z i))
        (N : ℕ) (F' : Finset (MMP.Mori.PrimeDivisor (modelSeq Y Yi n))),
        (∀ i, ∀ j < n, CY i j = flipTransform (f j) (fp j) (divisorSeq (C i) (CY i) j)) ∧
        (∀ j < n, (ψ j).compHom (f j) = (fp j).toRationalMap) ∧
        (∀ i, Φ i 0 = φ i) ∧ (∀ i, ∀ j < n, Φ i (j + 1) = (ψ j).comp (Φ i j)) ∧
        (∀ i, N ≤ i → ∀ j < n, ∀ E : MMP.Mori.PrimeDivisor (modelSeq Y Yi j),
          (E.support : Set (modelSeq Y Yi j)) ⊆ MMP.Mori.exceptionalSet (f j) →
            (divisorSeq (C i) (CY i) j).coeff E = 0) ∧
        (∀ i, N ≤ i → IsRealTerminalPair (modelStr sY sYi n) (divisorSeq (C i) (CY i) n)) ∧
        (∀ i, N ≤ i → ∀ P, 0 < (divisorSeq (C i) (CY i) n).coeff P ↔ P ∈ F') ∧
        (∀ P, Tendsto (fun i => (divisorSeq (C i) (CY i) n).coeff P) atTop
          (𝓝 ((divisorSeq B BY n).coeff P))) ∧
        ∀ i, N ≤ i →
          IsNefWeakModel (modelStr sY sYi n) (sZ i) sS (modelMap π πY n) (πZ i)
            (divisorSeq K KY n) (divisorSeq (C i) (CY i) n) (Φ i n) ∧
          ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
            (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ modelSeq Y Yi n) (q : W ⟶ Z i)
            (h : (modelSeq Y Yi n).RationalMap W),
            MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧
              p ≫ modelStr sY sYi n = sW ∧ q ≫ sZ i = sW ∧
              IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ IsBirationalMorphism p ∧
              IsBirationalMorphism q ∧ MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧
              h.compHom q = Φ i n ∧
              ∃ GY GZ : RDivisor W,
                IsRCartierPullback p
                  (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq (C i) (CY i) n)) GY ∧
                IsRCartierPullback q
                  (logCanonicalDivisor (RationalMap.transformDivisor (Φ i n) (divisorSeq K KY n))
                    (RationalMap.transformDivisor (Φ i n) (divisorSeq (C i) (CY i) n))) GZ ∧
                ∀ P ∈ F', ∀ P' : MMP.Mori.PrimeDivisor W,
                  RationalMap.transformPrimeDivisor h P = some P' → (GY - GZ).coeff P' = 0 := by
  revert Y S Z sY sS sZ π πZ K C B F φ hY hS hπ hYQ hdim hK hC hF hB hlim hZ hZQ hcomp
  exact Proof_lem_fourfold_terminal_limit_nef_reduction.solution

end MMP.Fourfold
