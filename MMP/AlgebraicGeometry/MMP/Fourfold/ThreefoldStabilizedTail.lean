module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.Divisor.DivisorialValuation

/-!
# Stabilized tails of threefold flip sequences and crepant junctions

For a threefold step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)`, the *bad locus of the base* is the
complement `Σ` of the largest open `U ⊆ Z` over which both `f⁻` and `f⁺` are isomorphisms, and
the *bad loci* of the two sides are its preimages `W^± = (f^±)⁻¹(Σ)`.

For a klt pair `(X, B)`, the *low-discrepancy set* `I(X, B)` is the set of normalized divisorial
valuations `ξ` of `k(X)` exceptional over `X` with log discrepancy `a(ξ; X, B) ≤ 1`.

A *stabilized tail* is an infinite sequence of small flips of `(K + B)`-negative extremal rays
with relative Picard number one, through effective rational klt pairs on normal projective
`ℚ`-factorial complex threefolds, along which the low-discrepancy set does not change.

For an effective rational klt pair `(X, B)` on a normal projective complex threefold and a finite
set `I ⊆ I(X, B)`, a *crepant junction of `(X, B)` extracting `I`* is a projective birational
`p : Y ⟶ X` from a normal projective `ℚ`-factorial threefold whose exceptional prime divisors
are exactly the centres `E_s = c_Y(s)`, `s ∈ I`, each extracted once, together with the boundary
`Θ = p⁻¹_* B + ∑_{s ∈ I} (1 - a(s; X, B)) E_s`.

## Main definitions

* `MMP.Fourfold.commonBiregularLocus`: the largest open of `Z` over which two morphisms to `Z`
  are both isomorphisms.
* `MMP.Fourfold.badLocusBase`, `MMP.Fourfold.badLocusMinus`, `MMP.Fourfold.badLocusPlus`: the bad
  loci `Σ`, `W⁻`, `W⁺`.
* `MMP.Fourfold.IsValuationLogDiscrepancy`: `a = a(ξ; X, B)` for a valuation `ξ`.
* `MMP.Fourfold.lowDiscrepancySet`: the low-discrepancy set `I(X, B)`.
* `MMP.Fourfold.valuationsOver`: a set of valuations of `k(X)` transported to `k(Z)` along a
  dominant morphism `X ⟶ Z`.
* `MMP.Fourfold.StabilizedTail`: stabilized small klt threefold tails.
* `MMP.Fourfold.CrepantJunction`: crepant junctions.

## Implementation notes

* The bad loci carry their reduced structures, so they are recorded as closed subsets. They are
  defined for any two morphisms with a common target; the source considers them for threefold
  step diagrams. The open `U` is the intersection of the `f^±`-biregular loci
  `MMP.Mori.biregularLocus`, the largest open over which `f^±` is an isomorphism; it is the
  largest open over which both are (`MMP.Fourfold.isBiregular_and_isBiregular_iff`).
* Log discrepancies are a predicate on a divisor over `X` (`MMP.Intersection.IsLogDiscrepancy`).
  The log discrepancy of a valuation `ξ` is that of any divisor `(W, g, E)` over `X` with `g`
  proper and `ord_E = ξ`; the value does not depend on the divisor, so it enters existentially,
  as in `MMP.Fourfold.minimalLogDiscrepancy`. The same holds for exceptionality
  (`MMP.Intersection.IsExceptionalValuation`), which already contains that `ξ` is a normalized
  divisorial valuation.
* The sets `I(X_i, B_i)` of a tail are sets of valuations of different function fields, compared
  through the identifications `k(X_i) ≅ k(Z_i) ≅ k(X_{i+1})` given by the birational morphisms
  of the steps. `I(X_i, B_i) = I(X_0, B_0)` for all `i` (under the composite identifications) is
  stated as `I(X_i, B_i) = I(X_{i+1}, B_{i+1})` in `k(Z_i)` for all `i`, which is equivalent.
* The canonical divisors `K_i` of the models of a tail are cut out by one rational top form:
  `K_{i+1} = (f_i⁺)⁻¹_* (f_i)_* K_i`, the convention of `MMP.Fourfold.IsThreefoldStepDiagram`,
  which also gives `B_{i+1} = (f_i⁺)⁻¹_* (f_i)_* B_i`.
* In a crepant junction, `Y` is a variety over `ℂ` through `p`, and `E_s = c_Y(s)` is stated as
  `ord_{E_s} = s` (as valuations of `k(X)`): a normalized divisorial valuation whose centre on the
  normal variety `Y` is a prime divisor `E` is `ord_E`, and conversely. The log discrepancies
  `a(s; X, B)` are rational because `B` is.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Bad loci -/

section BadLoci

variable {Xm Xp Z : Scheme.{u}} (fm : Xm ⟶ Z) (fp : Xp ⟶ Z)

/-- The largest open `U ⊆ Z` over which both `f⁻ : X⁻ ⟶ Z` and `f⁺ : X⁺ ⟶ Z` are
isomorphisms. -/
@[mmp "def_mmp_indexc_bad_loci"]
def commonBiregularLocus : Z.Opens := biregularLocus fm ⊓ biregularLocus fp

/-- `f⁻` and `f⁺` are both isomorphisms over an open `V ⊆ Z` exactly when `V ⊆ U`. -/
theorem isBiregular_and_isBiregular_iff {V : Z.Opens} :
    IsBiregular fm V ∧ IsBiregular fp V ↔ V ≤ commonBiregularLocus fm fp := by
  rw [isBiregular_iff_le_biregularLocus, isBiregular_iff_le_biregularLocus, commonBiregularLocus,
    le_inf_iff]

/-- `f⁻` is an isomorphism over `U`. -/
theorem isBiregular_commonBiregularLocus_left : IsBiregular fm (commonBiregularLocus fm fp) :=
  ((isBiregular_and_isBiregular_iff fm fp).mpr le_rfl).1

/-- `f⁺` is an isomorphism over `U`. -/
theorem isBiregular_commonBiregularLocus_right : IsBiregular fp (commonBiregularLocus fm fp) :=
  ((isBiregular_and_isBiregular_iff fm fp).mpr le_rfl).2

/-- The *bad locus of the base* `Σ = Z ∖ U`. -/
@[mmp "def_mmp_indexc_bad_loci"]
def badLocusBase : Closeds Z := (commonBiregularLocus fm fp).compl

/-- The *negative-side bad locus* `W⁻ = (f⁻)⁻¹(Σ) ⊆ X⁻`. -/
@[mmp "def_mmp_indexc_bad_loci"]
def badLocusMinus : Closeds Xm := (fm ⁻¹ᵁ commonBiregularLocus fm fp).compl

/-- The *positive-side bad locus* `W⁺ = (f⁺)⁻¹(Σ) ⊆ X⁺`. -/
@[mmp "def_mmp_indexc_bad_loci"]
def badLocusPlus : Closeds Xp := (fp ⁻¹ᵁ commonBiregularLocus fm fp).compl

/-- The underlying set of `Σ` is the complement of `U`. -/
theorem coe_badLocusBase :
    (badLocusBase fm fp : Set Z) = (commonBiregularLocus fm fp : Set Z)ᶜ := rfl

/-- The underlying set of `W⁻` is the preimage `(f⁻)⁻¹(Σ)`. -/
theorem coe_badLocusMinus : (badLocusMinus fm fp : Set Xm) = fm ⁻¹' badLocusBase fm fp := rfl

/-- The underlying set of `W⁺` is the preimage `(f⁺)⁻¹(Σ)`. -/
theorem coe_badLocusPlus : (badLocusPlus fm fp : Set Xp) = fp ⁻¹' badLocusBase fm fp := rfl

end BadLoci

/-! ### The low-discrepancy set -/

section LowSet

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- `a` is the log discrepancy `a(ξ; X, B)` of a valuation `ξ` of `k(X)`: the log discrepancy of
a divisor `(W, g, E)` over `X`, with `g` proper, whose valuation `ord_E` is `ξ`. -/
def IsValuationLogDiscrepancy (B : QDivisor X)
    (ξ : Valuation X.functionField (WithZero (Multiplicative ℤ))) (a : ℝ) : Prop :=
  ∃ (n : ℕ) (D : DivisorOver k sX), IsProper D.f ∧ D.valuation = ξ ∧
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a

/-- The *low-discrepancy set* `I(X, B)` of a (klt) pair `(X, B)`: the normalized divisorial
valuations `ξ` of `k(X)` that are exceptional over `X` and satisfy `a(ξ; X, B) ≤ 1`. -/
@[mmp "def_mmp_indexc_low_set"]
def lowDiscrepancySet (B : QDivisor X) :
    Set (Valuation X.functionField (WithZero (Multiplicative ℤ))) :=
  {ξ | MMP.Intersection.IsExceptionalValuation k sX ξ ∧
    ∃ a : ℝ, IsValuationLogDiscrepancy sX B ξ a ∧ a ≤ 1}

end LowSet

/-- A set `S` of valuations of `k(X)`, transported to valuations of `k(Z)` along the extension
of function fields `k(Z) → k(X)` of a dominant morphism `f : X ⟶ Z` of integral schemes. -/
def valuationsOver {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z] (f : X ⟶ Z) [IsDominant f]
    (S : Set (Valuation X.functionField (WithZero (Multiplicative ℤ)))) :
    Set (Valuation Z.functionField (WithZero (Multiplicative ℤ))) :=
  (fun ξ => ξ.comap (functionFieldMap f)) '' S

/-! ### Stabilized tails -/

/-- A *stabilized small klt threefold tail* `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}`, with canonical
divisors `K_i` of `X_i` and extremal rays `R_i`: every `(X_i, B_i)` is an effective rational klt
pair on a normal projective `ℚ`-factorial complex threefold; every
`(X_i, B_i) → Z_i ← (X_{i+1}, B_{i+1})` by `f_i`, `f_i⁺` is a threefold step diagram
(`MMP.Fourfold.IsThreefoldStepDiagram`) with `K_{i+1}`, `B_{i+1}` the strict transforms of `K_i`,
`B_i`; `f_i` is small and is the contraction of the `(K_i + B_i)`-negative extremal ray `R_i` of
`NE̅(X_i)`, with `ρ(X_i/Z_i) = 1`; and `I(X_i, B_i) = I(X_{i+1}, B_{i+1})` for all `i`, as sets
of valuations of `k(Z_i) ≅ k(X_i) ≅ k(X_{i+1})`, so that every `I(X_i, B_i)` is
`I_∞ = I(X_0, B_0)`. -/
@[mmp "def_mmp_indexc_stabilized_tail"]
structure StabilizedTail where
  /-- The models `X_i`. -/
  X : ℕ → Scheme.{0}
  /-- The structure morphism of `X_i` over `ℂ`. -/
  sX : ∀ i, X i ⟶ Spec (.of ℂ)
  [isIntegral : ∀ i, IsIntegral (X i)]
  [compactSpace : ∀ i, CompactSpace (X i)]
  [isLocallyNoetherian : ∀ i, IsLocallyNoetherian (X i)]
  [isNormal : ∀ i, IsNormal (X i)]
  /-- The canonical divisor `K_i` of `X_i`. -/
  K : ∀ i, Divisor (X i)
  /-- The boundary `B_i` on `X_i`. -/
  B : ∀ i, QDivisor (X i)
  /-- The base `Z_i` of the `i`-th step. -/
  Z : ℕ → Scheme.{0}
  /-- The structure morphism of `Z_i` over `ℂ`. -/
  sZ : ∀ i, Z i ⟶ Spec (.of ℂ)
  /-- The contraction `f_i : X_i ⟶ Z_i`. -/
  f : ∀ i, X i ⟶ Z i
  /-- The morphism `f_i⁺ : X_{i+1} ⟶ Z_i`. -/
  fp : ∀ i, X (i + 1) ⟶ Z i
  /-- The extremal ray `R_i ⊆ N₁(X_i)_ℝ` contracted by `f_i`. -/
  R : ∀ i, Set (NumericalCurveClasses (sX i))
  /-- `(X_i, B_i)` is a klt pair. -/
  isKltPair : ∀ i, IsKltPair (sX i) (B i)
  /-- `X_i` is a projective variety over `ℂ`. -/
  isProjectiveVariety : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i)
  /-- `X_i` is `ℚ`-factorial. -/
  isQFactorial : ∀ i, IsQFactorial (sX i)
  /-- `X_i` is a threefold. -/
  dim_eq : ∀ i, topologicalKrullDim (X i) = 3
  /-- `(X_i, B_i) → Z_i ← (X_{i+1}, B_{i+1})` is a threefold step diagram. -/
  isThreefoldStepDiagram : ∀ i,
    IsThreefoldStepDiagram (sX i) (sZ i) (sX (i + 1)) (K i) (B i) (f i) (fp i)
  /-- `K_{i+1}` is the strict transform of `K_i`. -/
  K_eq : ∀ i, K (i + 1) = flipTransform (f i) (fp i) (K i)
  /-- `B_{i+1}` is the strict transform of `B_i`. -/
  B_eq : ∀ i, B (i + 1) = flipTransform (f i) (fp i) (B i)
  /-- `f_i` is small. -/
  isSmallMorphism : ∀ i, IsSmallMorphism (sX i) (sZ i) (f i)
  /-- `R_i` is a `(K_i + B_i)`-negative extremal ray of `NE̅(X_i)`. -/
  isNegativeExtremalRayOf : ∀ i,
    IsNegativeExtremalRayOf (sX i) (Divisor.toQDivisor (K i) + B i) (R i)
  /-- `f_i` is the contraction of `R_i`. -/
  isContractionOfRay : ∀ i, IsContractionOfRay (sX i) (sZ i) (R i) (f i)
  /-- The relative Picard number `ρ(X_i/Z_i)` is one. -/
  relativePicardNumber_eq_one : ∀ i, relativePicardNumberN1 (sX i) (f i) = 1
  /-- `I(X_i, B_i) = I(X_{i+1}, B_{i+1})` as sets of valuations of `k(Z_i)`. -/
  lowDiscrepancySet_eq : ∀ i,
    haveI := (isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
    haveI := (isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
    valuationsOver (f i) (lowDiscrepancySet (sX i) (B i)) =
      valuationsOver (fp i) (lowDiscrepancySet (sX (i + 1)) (B (i + 1)))

attribute [instance] StabilizedTail.isIntegral StabilizedTail.compactSpace
  StabilizedTail.isLocallyNoetherian StabilizedTail.isNormal

namespace StabilizedTail

variable (T : StabilizedTail)

/-- The common low-discrepancy set `I_∞ = I(X_0, B_0)` of a stabilized tail. -/
abbrev lowDiscrepancySetLimit :
    Set (Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))) :=
  lowDiscrepancySet (T.sX 0) (T.B 0)

/-- `a = a_i(ξ) = a(ξ; X_i, B_i)` for a valuation `ξ` of `k(X_i)`. -/
abbrev IsLogDiscrepancyAt (i : ℕ)
    (ξ : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))) (a : ℝ) : Prop :=
  IsValuationLogDiscrepancy (T.sX i) (T.B i) ξ a

/-- The bad locus `Σ_i ⊆ Z_i` of the `i`-th step. -/
abbrev badLocusBaseAt (i : ℕ) : Closeds (T.Z i) := badLocusBase (T.f i) (T.fp i)

/-- The negative-side bad locus `W_i⁻ ⊆ X_i⁻ = X_i` of the `i`-th step. -/
abbrev badLocusMinusAt (i : ℕ) : Closeds (T.X i) := badLocusMinus (T.f i) (T.fp i)

/-- The positive-side bad locus `W_i⁺ ⊆ X_i⁺ = X_{i+1}` of the `i`-th step. -/
abbrev badLocusPlusAt (i : ℕ) : Closeds (T.X (i + 1)) := badLocusPlus (T.f i) (T.fp i)

end StabilizedTail

/-! ### Crepant junctions -/

section Junction

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  (sX : X ⟶ Spec (.of ℂ))

/-- A *crepant junction of `(X, B)` extracting `I`*. The setting: `(X, B)` is an effective
rational klt pair on a normal projective complex threefold and `I` is a finite set of normalized
divisorial valuations of `k(X)`, exceptional over `X`, with `a(s; X, B) ≤ 1` for `s ∈ I`, that
is, `I ⊆ I(X, B)`. The junction: a projective birational morphism `p : Y ⟶ X` from a normal
projective `ℚ`-factorial threefold (over `ℂ` through `p`) and prime divisors `E_s = c_Y(s)` of
`Y`, `s ∈ I`, such that `s ↦ E_s` is a bijection from `I` onto the `p`-exceptional prime divisors
of `Y`, together with the boundary `Θ = p⁻¹_* B + ∑_{s ∈ I} (1 - a(s; X, B)) E_s`. -/
@[mmp "def_mmp_indexc_junction"]
structure CrepantJunction (B : QDivisor X)
    (I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))) where
  /-- The source `Y` of the extraction. -/
  Y : Scheme.{0}
  [isIntegral : IsIntegral Y]
  [isLocallyNoetherian : IsLocallyNoetherian Y]
  [isNormal : IsNormal Y]
  /-- The projective birational morphism `p : Y ⟶ X`. -/
  p : Y ⟶ X
  /-- The prime divisor `E_s = c_Y(s)` of `Y`. -/
  E : I → MMP.Mori.PrimeDivisor Y
  /-- The boundary `Θ` on `Y`. -/
  Θ : QDivisor Y
  /-- `X` is a projective variety over `ℂ`. -/
  isProjectiveVariety_base : MMP.Mori.IsProjectiveVariety ℂ sX
  /-- `X` is a threefold. -/
  dim_base : topologicalKrullDim X = 3
  /-- `(X, B)` is a klt pair. -/
  isKltPair : IsKltPair sX B
  /-- `I ⊆ I(X, B)`. -/
  subset_lowDiscrepancySet : (I : Set _) ⊆ lowDiscrepancySet sX B
  /-- `Y` is a projective variety over `ℂ` through `p`. -/
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety ℂ (p ≫ sX)
  /-- `Y` is `ℚ`-factorial. -/
  isQFactorial : IsQFactorial (p ≫ sX)
  /-- `Y` is a threefold. -/
  dim_eq : topologicalKrullDim Y = 3
  /-- `p` is projective. -/
  isProjectiveMorphism : IsProjectiveMorphism p
  /-- `p` is birational. -/
  isBirationalMorphism : IsBirationalMorphism p
  /-- `ord_{E_s} = s` as valuations of `k(X)`. -/
  valuation_eq : ∀ s : I,
    (⟨Y, p, isQFactorial.1, isBirationalMorphism, E s⟩ : DivisorOver ℂ sX).valuation = s
  /-- Distinct `s ∈ I` give distinct divisors `E_s`. -/
  injective : Function.Injective E
  /-- The `p`-exceptional prime divisors of `Y` are exactly the `E_s`, `s ∈ I`. -/
  isExceptional_iff : ∀ P : MMP.Mori.PrimeDivisor Y,
    RationalMap.IsExceptional (X := Y) p.toRationalMap P ↔ P ∈ Set.range E
  /-- `Θ = p⁻¹_* B + ∑_{s ∈ I} (1 - a(s; X, B)) E_s`. -/
  Θ_eq : ∃ a : I → ℚ, (∀ s : I, IsValuationLogDiscrepancy sX B s (a s)) ∧
    Θ = inverseTransformDivisor p B + ∑ s : I, Finsupp.single (E s) (1 - a s)

attribute [instance] CrepantJunction.isIntegral CrepantJunction.isLocallyNoetherian
  CrepantJunction.isNormal

end Junction

end MMP.Fourfold
