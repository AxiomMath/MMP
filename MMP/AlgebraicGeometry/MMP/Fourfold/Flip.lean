module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities

/-!
# Flips and the projective floor-program inputs

A `D`-flip of a small birational contraction `f : X ⟶ Z` with `-D` `f`-ample is a small projective
birational `f⁺ : X⁺ ⟶ Z` from a normal variety on which the strict transform of `D` is
`ℚ`-Cartier and `f⁺`-ample. The *projective floor-program inputs* `P(n)` are the two inputs the
fourfold source feeds into its induction: flips exist for small contractions of negative extremal
rays of rational `ℚ`-factorial projective dlt complex `n`-folds on which some component of the
reduced boundary is negative, and sequences of such flips terminate.

## Main definitions

* `MMP.Fourfold.IsFlipOf`: a `D`-flip of a small birational contraction.
* `MMP.Fourfold.IsComponentNegative`: some component of `⌊B⌋` is negative on a ray.
* `MMP.Fourfold.IsFloorFlippingContraction`: the contractions of the floor program.
* `MMP.Fourfold.ProjectiveFloorProgramInputs`: the property `P(n)`.
* `MMP.Fourfold.IsThreefoldStepDiagram`: threefold step diagrams `X⁻ → Z ← X⁺`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

variable {k : Type u} [Field k] {X Z X' : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-! ### Flips -/

section Flip

variable [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X']
  [IsLocallyNoetherian X'] [IsNormal X']

/-- For a normal variety `X`, a `ℚ`-Cartier `ℚ`-divisor `D` on `X` and a small birational
contraction `f : X ⟶ Z` with `-D` `f`-ample, a *`D`-flip* of `f` is a small projective birational
morphism `f⁺ : X⁺ ⟶ Z` from a normal variety such that the strict transform
`D⁺ = (f⁺)⁻¹_* f_* D` is `ℚ`-Cartier and `f⁺`-ample. -/
@[mmp "def_oai4_bg_flip"]
structure IsFlipOf (sZ : Z ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k)) (D : QDivisor X)
    (f : X ⟶ Z) (fp : X' ⟶ Z) : Prop where
  isQCartier : D.IsQCartier
  isContraction : IsContraction sX sZ f
  isSmallMorphism : IsSmallMorphism sX sZ f
  /-- `-D` is `f`-ample. -/
  hasRelativelyAmpleMultiple : (-D).HasRelativelyAmpleMultiple f
  isSmallMorphism_flip : IsSmallMorphism sX' sZ fp
  isProjectiveMorphism_flip : IsProjectiveMorphism fp
  isQCartier_flip : MMP.Mori.QDivisor.IsQCartier (flipTransform f fp D)
  /-- The strict transform `D⁺` is `f⁺`-ample. -/
  hasRelativelyAmpleMultiple_flip :
    MMP.Mori.QDivisor.HasRelativelyAmpleMultiple (flipTransform f fp D) fp

end Flip

/-! ### The projective floor-program inputs -/

section Floor

variable [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

/-- *Some component of the reduced boundary `⌊B⌋` is negative on* `R ⊆ N₁(X)_ℝ`: there is a prime
divisor `S` with coefficient one in `B`, `ℚ`-Cartier, such that `(S · u) < 0` for every
`0 ≠ u ∈ R`. -/
def IsComponentNegative (B : QDivisor X) (R : Set (NumericalCurveClasses sX)) : Prop :=
  ∃ S : MMP.Mori.PrimeDivisor X, B.coeff S = 1 ∧
    ∃ h : (Divisor.toQDivisor (Finsupp.single S 1)).IsQCartier,
      ∀ u ∈ R, u ≠ 0 → QDivisor.curveForm sX (Divisor.toQDivisor (Finsupp.single S 1)) h u < 0

/-- The contractions of the floor program: for a pair `(X, B)` with canonical divisor `K`, a
small contraction `f : X ⟶ Z` onto a projective variety of a `(K + B)`-negative extremal ray `R`
of `NE̅(X)` (so that `-(K + B)` is `f`-ample) on which some component of `⌊B⌋` is negative. -/
structure IsFloorFlippingContraction (sZ : Z ⟶ Spec (.of k)) (K : Divisor X) (B : QDivisor X)
    (R : Set (NumericalCurveClasses sX)) (f : X ⟶ Z) : Prop where
  isNegativeExtremalRayOf : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R
  isContractionOfRay : IsContractionOfRay sX sZ R f
  isSmallMorphism : IsSmallMorphism sX sZ f
  isProjectiveVariety_target : MMP.Mori.IsProjectiveVariety k sZ
  /-- `-(K + B)` is `f`-ample. -/
  hasRelativelyAmpleMultiple : (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple f
  isComponentNegative : IsComponentNegative sX B R

end Floor

/-- A *rational `ℚ`-factorial projective dlt complex `n`-fold*: a projective variety `X` over `ℂ`
of dimension `n` which is `ℚ`-factorial, with canonical divisor `K` and a dlt boundary `B` with
rational coefficients. -/
def IsFloorPair {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) (n : ℕ) (K : Divisor X) (B : QDivisor X) : Prop :=
  MMP.Mori.IsProjectiveVariety ℂ sX ∧ topologicalKrullDim X = n ∧ IsQFactorial sX ∧
    (∃ m : ℕ, K.IsCanonicalDivisor sX m) ∧ MMP.Intersection.IsDltPair sX B

/-- **The projective floor-program inputs** `P(n)`, `n ≥ 3`. First, for every rational
`ℚ`-factorial projective dlt complex `n`-fold `(X, B)` and every small contraction `f : X ⟶ Z`
(onto a projective variety) of a `(K + B)`-negative extremal ray on which some component of `⌊B⌋`
is negative, `f` has a `(K + B)`-flip `f⁺ : X⁺ ⟶ Z` with `X⁺` projective. Second, every sequence
of such flips of one fixed such pair is finite: there is no infinite sequence of models
`X₀ = X, X₁, …`, all projective, with flips `X_i ⟶ Z_i ⟵ X_{i+1}` of floor contractions for the
boundaries `B_{i+1} = (f_i⁺)⁻¹_* (f_i)_* B_i`, the strict transforms of the initial boundary (and
canonical divisors `K_{i+1} = (f_i⁺)⁻¹_* (f_i)_* K_i`). -/
@[mmp "def_fourfold_projective_floor_program_inputs"]
def ProjectiveFloorProgramInputs (n : ℕ) : Prop :=
  3 ≤ n ∧
  (∀ (X : Scheme.{0}) [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (K : Divisor X) (B : QDivisor X), IsFloorPair sX n K B →
    ∀ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of ℂ)) (R : Set (NumericalCurveClasses sX)) (f : X ⟶ Z),
      IsFloorFlippingContraction sX sZ K B R f →
      ∃ (X' : Scheme.{0}) (_ : CompactSpace X') (_ : IsLocallyNoetherian X') (_ : IsNormal X')
        (sX' : X' ⟶ Spec (.of ℂ)) (fp : X' ⟶ Z),
        MMP.Mori.IsProjectiveVariety ℂ sX' ∧ IsFlip sX sZ sX' K B f fp) ∧
  (∀ (X : Scheme.{0}) [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (K : Divisor X) (B : QDivisor X), IsFloorPair sX n K B →
    ¬ ∃ (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ)) (_ : ∀ i, IsIntegral (Y i))
        (_ : ∀ i, CompactSpace (Y i)) (_ : ∀ i, IsLocallyNoetherian (Y i))
        (_ : ∀ i, IsNormal (Y i)) (KY : ∀ i, Divisor (Y i)) (BY : ∀ i, QDivisor (Y i))
        (Z : ℕ → Scheme.{0}) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
        (R : ∀ i, Set (NumericalCurveClasses (modelStr sX sY i)))
        (f : ∀ i, modelSeq X Y i ⟶ Z i) (fp : ∀ i, Y i ⟶ Z i),
      ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sY i) ∧
        IsFloorFlippingContraction (modelStr sX sY i) (sZ i) (divisorSeq K KY i)
          (divisorSeq B BY i) (R i) (f i) ∧
        IsFlip (modelStr sX sY i) (sZ i) (sY i) (divisorSeq K KY i) (divisorSeq B BY i)
          (f i) (fp i) ∧
        KY i = flipTransform (f i) (fp i) (divisorSeq K KY i) ∧
        BY i = flipTransform (f i) (fp i) (divisorSeq B BY i))

/-! ### Threefold step diagrams -/

section StepDiagram

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- A *threefold step diagram* `(X⁻, B⁻) → Z ← (X⁺, B⁺)`: `X^±` are normal projective threefolds
over `ℂ` with canonical divisors `K^±`, `Z` is a normal projective variety, `f^± : X^± ⟶ Z` are
projective birational morphisms over `ℂ` with `f^±_* 𝒪_{X^±} = 𝒪_Z`, `f⁺` is small, `B⁻` is an
effective `ℚ`-divisor, `B⁺ = (f⁺)⁻¹_* f⁻_* B⁻` and `K⁺ = (f⁺)⁻¹_* f⁻_* K⁻`, both canonical
divisors (cut out by one rational top form), `D^± = K^± + B^±` are `ℚ`-Cartier, `-D⁻` is
`f⁻`-ample and `D⁺` is `f⁺`-ample. The positive pair is not required to be lc. -/
@[mmp "def_mmp_indexc_step_diagram"]
structure IsThreefoldStepDiagram (sXm : Xm ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    (sXp : Xp ⟶ Spec (.of ℂ)) (K : Divisor Xm) (B : QDivisor Xm) (fm : Xm ⟶ Z) (fp : Xp ⟶ Z) :
    Prop where
  isProjectiveVariety_minus : MMP.Mori.IsProjectiveVariety ℂ sXm
  isNormalVariety_minus : IsNormalVariety ℂ sXm
  dim_minus : topologicalKrullDim Xm = 3
  isProjectiveVariety_plus : MMP.Mori.IsProjectiveVariety ℂ sXp
  isNormalVariety_plus : IsNormalVariety ℂ sXp
  dim_plus : topologicalKrullDim Xp = 3
  isProjectiveVariety_target : MMP.Mori.IsProjectiveVariety ℂ sZ
  isNormalVariety_target : IsNormalVariety ℂ sZ
  comp_eq_minus : fm ≫ sZ = sXm
  comp_eq_plus : fp ≫ sZ = sXp
  isProjectiveMorphism_minus : IsProjectiveMorphism fm
  isProjectiveMorphism_plus : IsProjectiveMorphism fp
  isBirationalMorphism_minus : IsBirationalMorphism fm
  /-- `f⁻_* 𝒪_{X⁻} = 𝒪_Z`. -/
  isIso_app_minus : ∀ U : Z.Opens, IsIso (fm.app U)
  /-- `f⁺_* 𝒪_{X⁺} = 𝒪_Z`. -/
  isIso_app_plus : ∀ U : Z.Opens, IsIso (fp.app U)
  isSmallMorphism_plus : IsSmallMorphism sXp sZ fp
  isCanonicalDivisor : ∃ m : ℕ, K.IsCanonicalDivisor sXm m
  isCanonicalDivisor_plus :
    ∃ m : ℕ, MMP.Mori.Divisor.IsCanonicalDivisor sXp m (flipTransform fm fp K)
  nonneg : ∀ P, 0 ≤ B.coeff P
  /-- `D⁻ = K⁻ + B⁻` is `ℚ`-Cartier. -/
  isQCartier_minus : (Divisor.toQDivisor K + B).IsQCartier
  /-- `D⁺ = K⁺ + B⁺` is `ℚ`-Cartier. -/
  isQCartier_plus :
    MMP.Mori.QDivisor.IsQCartier
      (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B)
  /-- `-D⁻` is `f⁻`-ample. -/
  hasRelativelyAmpleMultiple_minus : (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple fm
  /-- `D⁺` is `f⁺`-ample. -/
  hasRelativelyAmpleMultiple_plus : MMP.Mori.QDivisor.HasRelativelyAmpleMultiple
    (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B) fp

end StepDiagram

/- The generic minimal log discrepancy `mld_{η_V}(X, B)` at an irreducible closed curve `V` of a
threefold is the minimal log discrepancy `MMP.Fourfold.minimalLogDiscrepancy` at the generic
point `η_V`. -/
attribute [mmp "def_mmp_indexc_generic_mld"] MMP.Fourfold.minimalLogDiscrepancy

end MMP.Fourfold
