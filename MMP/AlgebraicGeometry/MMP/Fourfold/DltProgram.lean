module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
public import MMP.Combinatorics.WeightedGraph.BranchValues
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyCommonModel
public import MMP.AlgebraicGeometry.Singularities.Deminormal.Discrepancy
public import MMP.AlgebraicGeometry.Singularities.CyclicCover.IndexOneCover
public import MMP.LinearAlgebra.QuadraticForm.NegativeDefiniteConfiguration
public import MMP.AlgebraicGeometry.Singularities.Slc.NodeResidueForm
public import MMP.AlgebraicGeometry.Cohomology.Duality.NormalizedDualizingComplex
public import MMP.AlgebraicGeometry.Resolution.Blowup.Charts
public import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
public import MMP.AlgebraicGeometry.Morphisms.Smooth.EtaleCoordinateCharts
public import MMP.RingTheory.RegularLocalRing.FlatRegularParameters
public import MMP.RingTheory.PowerSeries.CompleteLocalRing
public import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
public import MMP.AlgebraicGeometry.Resolution.Blowup.RegularSequenceCharts
public import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
public import MMP.AlgebraicGeometry.Morphisms.Smooth.IrreducibleComponents
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGermTypes
public import MMP.AlgebraicGeometry.Modules.TotalQuotientSheaf
public import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.Group
public import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.S2
public import MMP.AlgebraicGeometry.Cohomology.Duality.CanonicalExtSequence

/-!
# Elementary dlt programs and the lower-dimensional log minimal model program

Let `X ⟶ S` be a projective morphism of complex quasi-projective varieties and `(X, B)` a
`ℚ`-factorial dlt pair with rational boundary. A *relative elementary dlt program* from `(X, B)`
is a finite or infinite sequence of such pairs `(X_i, B_i)` over `S`, `(X₀, B₀) = (X, B)`, whose
transitions are the divisorial contractions of `(K_{X_i} + B_i)`-negative extremal rays of the
closed relative cone `NE̅(X_i/S)` and the flips of the small contractions of such rays, with
`B_{i+1}` the birational transform of `B_i`. A stage may stop when its adjoint `K_{X_i} + B_i` is
nef over `S`, or when a chosen `(K_{X_i} + B_i)`-negative extremal contraction has fibre type.
When `S` and all the models are projective, the program is *projective*. The property `P_n`
asserts, in dimension at most `n` and for projective `X ⟶ S`, the existence of contractions of
negative extremal rays and of flips of the small ones, the termination of every projective
elementary dlt program, and the existence of a maximal one, ending with a relatively nef adjoint
or a Mori fibre space over `S`.

## Main definitions

* `MMP.Fourfold.QDivisor.relativeCurveForm`: the linear form `z ↦ (D · z)` on `N₁(X/S)` of a
  `ℚ`-Cartier `ℚ`-divisor.
* `MMP.Fourfold.IsNegativeRelativeExtremalRayOf`: `D`-negative extremal rays of `NE̅(X/S)`.
* `MMP.Fourfold.IsNegativeRelativeRayContraction`: the contraction over `S` of such a ray.
* `MMP.Fourfold.IsRelativeDltModel`: a `ℚ`-factorial dlt pair with rational boundary, projective
  over a quasi-projective base.
* `MMP.Fourfold.IsElementaryDltStep`: a divisorial contraction or a flip of a negative ray.
* `MMP.Fourfold.RelativeDltProgram`, `MMP.Fourfold.RelativeDltProgram.IsMaximal`: relative
  elementary dlt programs, and maximal ones.
* `MMP.Fourfold.RelativeDltProgram.IsProjective`: projective elementary dlt programs.
* `MMP.Fourfold.ProjectiveLowerLogMMP`: the property `P_n`.

## Implementation notes

The models are indexed as in `MMP.Fourfold.Program`: `X₀ = X`, `X_{i+1} = Y i`, with
`n ∈ ℕ ∪ {∞}` birational steps; only the data indexed by `i ≤ n` (models) and `i < n` (steps)
are constrained. Each step `i` carries a contraction `f_i : X_i ⟶ Z_i` over `S` of an extremal
ray `R_i` of `NE̅(X_i/S)`, a morphism `f_i⁺ : X_{i+1} ⟶ Z_i` and a birational map
`φ_i : X_i ⤏ X_{i+1}` over `Z_i`: for a divisorial contraction `f_i⁺` is an isomorphism (the next
model is the target of the contraction, up to isomorphism), for a small one `(f_i⁺, φ_i)` is a
flip. The boundary `B_{i+1}` is the birational transform `(φ_i)_* B_i`. The canonical divisors
`K_i` are any canonical divisors of the models: negativity, ampleness and nefness of
`K_i + B_i` only depend on its numerical class.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.26
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.31
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-! ### Negative extremal rays of the relative cone -/

section RelativeRay

variable {k : Type u} [Field k] {X S : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (π : X ⟶ S)
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

/-- The linear form `z ↦ (D · z)` on `N₁(X/S)` of a `ℚ`-Cartier `ℚ`-divisor `D` on a normal
scheme: for the associated `ℚ`-Cartier divisor `⟨D⟩ = ∑ cⱼ Dⱼ` (`Dⱼ` Cartier divisors), the form
`∑ cⱼ deg 𝒪_X(Dⱼ)`. -/
def QDivisor.relativeCurveForm (D : QDivisor X) (h : D.IsQCartier) :
    RelativeNumericalCurveClasses sX π →ₗ[ℝ] ℝ :=
  (D.associatedCartier h).sum fun E c =>
    haveI := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
    (c : ℝ) • RelativeNumericalCurveClasses.degree sX π (E : Divisor X).divisorialSheaf

/-- An extremal ray `R` of the closed relative cone `NE̅(X/S)` is *`D`-negative*, for a
`ℚ`-Cartier `ℚ`-divisor `D`, if `(D · u) < 0` for every `0 ≠ u ∈ R`. -/
def IsNegativeRelativeExtremalRayOf (D : QDivisor X)
    (R : Set (RelativeNumericalCurveClasses sX π)) : Prop :=
  ∃ h : D.IsQCartier,
    IsExtremalRay ℝ (relativeClosedConeOfCurves sX π : Set (RelativeNumericalCurveClasses sX π))
        R ∧
      ∀ u ∈ R, u ≠ 0 → QDivisor.relativeCurveForm sX π D h u < 0

variable {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))

/-- `f : X ⟶ Z`, with `g : Z ⟶ S`, is *the contraction over `S` of a `D`-negative extremal ray*
`R` of `NE̅(X/S)`: `R` is a `D`-negative extremal ray, `(f, g)` is the contraction of `R` over `S`
(`g` projective, `g ∘ f = π`, `f_* 𝒪_X = 𝒪_Z`, and a curve contracted by `π` is contracted by `f`
exactly when its class lies in `R`), and `f` is a `D`-negative extremal contraction onto a normal
variety (`-D` is `f`-ample and `ρ(X/Z) = 1`). -/
structure IsNegativeRelativeRayContraction (D : QDivisor X)
    (R : Set (RelativeNumericalCurveClasses sX π)) (f : X ⟶ Z) (g : Z ⟶ S) : Prop where
  isNegativeRelativeExtremalRayOf : IsNegativeRelativeExtremalRayOf sX π D R
  isRelativeContractionOfFace : IsRelativeContractionOfFace π R f g
  /-- `f` is a `D`-negative extremal contraction onto a normal variety. -/
  isNegativeExtremalContraction :
    IsNegativeExtremalContraction k sX sZ (QDivisor.toRDivisor D) f

end RelativeRay

/-! ### Models and steps -/

section Step

variable {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  (sX : X ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ)) (π : X ⟶ S)

/-- A *model* of a relative elementary dlt program over `S`: `S` and `X` are complex
quasi-projective varieties, `π : X ⟶ S` is a projective morphism over `ℂ`, `X` is `ℚ`-factorial,
`K` is a canonical divisor of `X` and `(X, B)` is a dlt pair with rational boundary `B`. -/
structure IsRelativeDltModel (K : Divisor X) (B : QDivisor X) : Prop where
  isQuasiProjectiveVariety_base : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sS
  isQuasiProjectiveVariety : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sX
  comp_eq : π ≫ sS = sX
  isProjectiveMorphism : IsProjectiveMorphism π
  isQFactorial : IsQFactorial sX
  isCanonicalDivisor : ∃ m : ℕ, K.IsCanonicalDivisor sX m
  isDltPair : MMP.Intersection.IsDltPair sX B

variable {Z X' : Scheme.{0}} [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  (sZ : Z ⟶ Spec (.of ℂ)) (sX' : X' ⟶ Spec (.of ℂ)) (π' : X' ⟶ S)

/-- An *elementary dlt step* from `(X, B)` over `S`, with canonical divisor `K`, to `X'` over `S`
(by `π'`): `f : X ⟶ Z`, `g : Z ⟶ S` is the contraction over `S` of a `(K + B)`-negative extremal
ray `R` of `NE̅(X/S)`, `fp : X' ⟶ Z` satisfies `g ∘ fp = π'`, and either

* `f` is a divisorial contraction (birational with exceptional set a prime divisor), `fp` is an
  isomorphism and `φ : X ⤏ X'` is `fp⁻¹ ∘ f`, so that `X'` is the target of `f`; or
* `f` is small and `(fp, φ)` is a flip of `f` with respect to `K + B`. -/
structure IsElementaryDltStep (K : Divisor X) (B : QDivisor X)
    (R : Set (RelativeNumericalCurveClasses sX π)) (f : X ⟶ Z) (g : Z ⟶ S) (fp : X' ⟶ Z)
    (φ : X.RationalMap X') : Prop where
  /-- `(f, g)` is the contraction over `S` of the `(K + B)`-negative extremal ray `R`. -/
  isNegativeRelativeRayContraction :
    IsNegativeRelativeRayContraction sX π sZ (Divisor.toQDivisor K + B) R f g
  comp_eq : fp ≫ g = π'
  divisorial_or_flip :
    (IsBirationalMorphism f ∧
        (∃ E : MMP.Mori.PrimeDivisor X, (MMP.Mori.exceptionalSet f : Set X) = E.support) ∧
        IsIso fp ∧ IsModificationOf f fp φ) ∨
      IsFlip ℂ sX sZ sX' (QDivisor.toRDivisor (Divisor.toQDivisor K + B)) f fp φ

end Step

/-! ### Programs -/

section Program

/-- The morphisms `X_i ⟶ S` of the models of a program over `S`. -/
def modelMap {X S : Scheme.{u}} {Y : ℕ → Scheme.{u}} (π : X ⟶ S) (πY : ∀ i, Y i ⟶ S) :
    ∀ i, modelSeq X Y i ⟶ S
  | 0 => π
  | i + 1 => πY i

variable {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  (sX : X ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ)) (π : X ⟶ S)

/-- A *relative elementary dlt program* from `(X, B)` over `S`, with canonical divisor `K`: a
number `n ∈ ℕ ∪ {∞}` of birational steps and models `(X_i, B_i)` over `S` (by `π_i`),
`X₀ = X`, `X_{i+1} = Y i`, `(B₀, π₀) = (B, π)`, with canonical divisors `K_i` (`K₀ = K`), such
that

* every `(X_i, B_i)`, `i ≤ n`, is a `ℚ`-factorial dlt pair with rational boundary, with `X_i`
  quasi-projective and projective over the quasi-projective `S`;
* for `i < n`, the transition from `X_i` to `X_{i+1}` is an elementary dlt step
  (`MMP.Fourfold.IsElementaryDltStep`) for a `(K_i + B_i)`-negative extremal ray `R_i` of
  `NE̅(X_i/S)`: a divisorial contraction `f_i` of `R_i` over `S` onto `X_{i+1}`, or the flip of the
  small contraction `f_i` of `R_i`, by `φ_i : X_i ⤏ X_{i+1}`;
* `B_{i+1} = (φ_i)_* B_i` is the birational transform of `B_i`;
* when `n < ∞`, optionally (`hasFinal`) a final `(K_n + B_n)`-negative extremal ray of `NE̅(X_n/S)`
  is chosen whose contraction `g : X_n ⟶ T` over `S` is of fibre type, `dim T < dim X_n`.

The data indexed by `i > n` (models) and `i ≥ n` (steps) are unconstrained. -/
@[mmp "def_mmp_relative_dlt_program"]
structure RelativeDltProgram (K : Divisor X) (B : QDivisor X) where
  /-- The number of birational steps. -/
  n : ℕ∞
  /-- The models after the first: `X_{i+1} = Y i`. -/
  Y : ℕ → Scheme.{0}
  /-- The structure morphism `X_{i+1} ⟶ Spec ℂ`. -/
  sY : ∀ i, Y i ⟶ Spec (.of ℂ)
  [isIntegral : ∀ i, IsIntegral (Y i)]
  [compactSpace : ∀ i, CompactSpace (Y i)]
  [isLocallyNoetherian : ∀ i, IsLocallyNoetherian (Y i)]
  [isNormal : ∀ i, IsNormal (Y i)]
  /-- The morphism `π_{i+1} : X_{i+1} ⟶ S`. -/
  πY : ∀ i, Y i ⟶ S
  /-- The canonical divisor `K_{i+1}` of `X_{i+1}`. -/
  KY : ∀ i, Divisor (Y i)
  /-- The boundary `B_{i+1}` on `X_{i+1}`. -/
  BY : ∀ i, QDivisor (Y i)
  /-- The extremal ray `R_i ⊆ N₁(X_i/S)`. -/
  R : ∀ i, Set (RelativeNumericalCurveClasses (modelStr sX sY i) (modelMap π πY i))
  /-- The target `Z_i` of the contraction of `R_i`. -/
  Z : ℕ → Scheme.{0}
  /-- The structure morphism `Z_i ⟶ Spec ℂ`. -/
  sZ : ∀ i, Z i ⟶ Spec (.of ℂ)
  /-- The contraction `f_i : X_i ⟶ Z_i` of `R_i`. -/
  f : ∀ i, modelSeq X Y i ⟶ Z i
  /-- The structure morphism `Z_i ⟶ S`. -/
  gZ : ∀ i, Z i ⟶ S
  /-- The morphism `f_i⁺ : X_{i+1} ⟶ Z_i`. -/
  fp : ∀ i, Y i ⟶ Z i
  /-- The birational transition `φ_i : X_i ⤏ X_{i+1}`. -/
  φ : ∀ i, (modelSeq X Y i).RationalMap (Y i)
  isRelativeDltModel : ∀ i : ℕ, (i : ℕ∞) ≤ n →
    IsRelativeDltModel (modelStr sX sY i) sS (modelMap π πY i) (divisorSeq K KY i)
      (divisorSeq B BY i)
  isElementaryDltStep : ∀ i : ℕ, (i : ℕ∞) < n →
    IsElementaryDltStep (modelStr sX sY i) (modelMap π πY i) (sZ i) (sY i) (πY i)
      (divisorSeq K KY i) (divisorSeq B BY i) (R i) (f i) (gZ i) (fp i) (φ i)
  BY_eq : ∀ i : ℕ, (i : ℕ∞) < n →
    BY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq B BY i)
  /-- Whether the program stops with a fibre-type contraction. -/
  hasFinal : Prop
  /-- The final ray `R_n ⊆ N₁(X_n/S)`, used when `hasFinal`. -/
  finalRay : Set (RelativeNumericalCurveClasses (modelStr sX sY n.toNat) (modelMap π πY n.toNat))
  /-- The target of the final contraction. -/
  T : Scheme.{0}
  /-- The structure morphism `T ⟶ Spec ℂ`. -/
  sT : T ⟶ Spec (.of ℂ)
  /-- The structure morphism `T ⟶ S`. -/
  gT : T ⟶ S
  /-- The final contraction `g : X_n ⟶ T`. -/
  g : modelSeq X Y n.toNat ⟶ T
  final_spec : hasFinal → n ≠ ⊤ ∧
    IsNegativeRelativeRayContraction (modelStr sX sY n.toNat) (modelMap π πY n.toNat) sT
      (Divisor.toQDivisor (divisorSeq K KY n.toNat) + divisorSeq B BY n.toNat) finalRay g gT ∧
    topologicalKrullDim T < topologicalKrullDim (modelSeq X Y n.toNat)

attribute [instance] RelativeDltProgram.isIntegral RelativeDltProgram.compactSpace
  RelativeDltProgram.isLocallyNoetherian RelativeDltProgram.isNormal

variable {sX sS π} {K : Divisor X} {B : QDivisor X}

/-- A relative elementary dlt program with `n` birational steps is *maximal* if `n = ∞`, or
`n < ∞` and the adjoint `K_n + B_n` is nef over `S`, or `n < ∞` and the program stops with a
fibre-type contraction. -/
def RelativeDltProgram.IsMaximal (P : RelativeDltProgram sX sS π K B) : Prop :=
  P.n = ⊤ ∨
    (P.n ≠ ⊤ ∧ IsRelativelyNef ℂ (modelStr sX P.sY P.n.toNat) (modelMap π P.πY P.n.toNat)
      (QDivisor.toRDivisor (Divisor.toQDivisor (divisorSeq K P.KY P.n.toNat) +
        divisorSeq B P.BY P.n.toNat))) ∨
    P.hasFinal

/-- For a morphism `X ⟶ S` of projective complex varieties, a *projective elementary dlt program*
is a relative elementary dlt program over `S` all of whose models `X_i`, `i ≤ n`, are projective
varieties. -/
@[mmp "def_mmp_projective_dlt_program"]
def RelativeDltProgram.IsProjective (P : RelativeDltProgram sX sS π K B) : Prop :=
  MMP.Mori.IsProjectiveVariety ℂ sS ∧
    ∀ i : ℕ, (i : ℕ∞) ≤ P.n → MMP.Mori.IsProjectiveVariety ℂ (modelStr sX P.sY i)

end Program

/-! ### The lower-dimensional projective log minimal model program -/

/-- **The property `P_n`.** For every morphism `π : X ⟶ S` of projective complex varieties and
every `ℚ`-factorial dlt pair `(X, B)` with rational boundary of dimension at most `n`, with
canonical divisor `K`:

* every `(K + B)`-negative extremal ray `R` of `NE̅(X/S)` has a contraction `f : X ⟶ Z` over `S`
  onto a projective variety and, when `f` is small, a flip `f⁺ : X⁺ ⟶ Z` with `X⁺` projective;
* every projective elementary dlt program from `(X, B)` over `S` has finitely many birational
  steps;
* a maximal projective elementary dlt program from `(X, B)` over `S` exists: it has finitely many
  birational steps and ends with a final model `X_n` whose adjoint `K_n + B_n` is nef over `S`,
  or with a Mori fibre space over `S`. -/
@[mmp "def_mmp_projective_lower_log_mmp"]
def ProjectiveLowerLogMMP (n : ℕ) : Prop :=
  0 < n ∧
  ∀ (X S : Scheme.{0}) [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ)) (π : X ⟶ S) (K : Divisor X)
    (B : QDivisor X),
    MMP.Mori.IsProjectiveVariety ℂ sX → MMP.Mori.IsProjectiveVariety ℂ sS → π ≫ sS = sX →
    topologicalKrullDim X ≤ n → IsQFactorial sX → (∃ m : ℕ, K.IsCanonicalDivisor sX m) →
    MMP.Intersection.IsDltPair sX B →
    (∀ R : Set (RelativeNumericalCurveClasses sX π),
      IsNegativeRelativeExtremalRayOf sX π (Divisor.toQDivisor K + B) R →
      ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of ℂ)) (f : X ⟶ Z) (g : Z ⟶ S),
        IsNegativeRelativeRayContraction sX π sZ (Divisor.toQDivisor K + B) R f g ∧
        MMP.Mori.IsProjectiveVariety ℂ sZ ∧
        (IsSmall ℂ sZ sX f →
          ∃ (X' : Scheme.{0}) (_ : CompactSpace X') (_ : IsLocallyNoetherian X')
            (_ : IsNormal X') (sX' : X' ⟶ Spec (.of ℂ)) (fp : X' ⟶ Z) (φ : X.RationalMap X'),
            MMP.Mori.IsProjectiveVariety ℂ sX' ∧
              IsFlip ℂ sX sZ sX' (QDivisor.toRDivisor (Divisor.toQDivisor K + B)) f fp φ)) ∧
    (∀ P : RelativeDltProgram sX sS π K B, P.IsProjective → P.n ≠ ⊤) ∧
    ∃ P : RelativeDltProgram sX sS π K B, P.IsProjective ∧ P.n ≠ ⊤ ∧
      (IsRelativelyNef ℂ (modelStr sX P.sY P.n.toNat) (modelMap π P.πY P.n.toNat)
          (QDivisor.toRDivisor (Divisor.toQDivisor (divisorSeq K P.KY P.n.toNat) +
            divisorSeq B P.BY P.n.toNat)) ∨ P.hasFinal)

end MMP.Fourfold
