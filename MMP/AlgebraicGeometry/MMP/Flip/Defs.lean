/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Basic

/-!
# Extremal rays, relative Picard numbers and flips in *Flips and abundance*

The relative cone of curves and its extremal rays (used in FA 2.35), the relative Picard number
(FA 2.26.3), `E`-negative extremal contractions (FA 2.26.3), and generalized flips and flips
(FA 2.26.4).

The relative cone of curves is Kollár–Mori's: `N₁(X/Y)` is
`MMP.Mori.RelativeNumericalCurveClasses` (real relative 1-cycles modulo those with zero
intersection number with every Cartier divisor, equivalently with every `ℝ`-Cartier divisor),
with the coarsest topology making every `γ ↦ D · γ` continuous, and `NE(X/Y)` is
`MMP.Mori.relativeClosedConeOfCurves`; extremal rays are `MMP.Mori.IsExtremalRay`.

## Main definitions

* `MMP.Flips.IsNegativeRelativeExtremalRay`: `A`-negative extremal rays of `NE(X/Y)`.
* `MMP.Flips.RelativeNumericalDivisorClasses`: `N¹(X/Z)`, `ℝ`-Cartier divisors modulo numerical
  equivalence over `Z`, and `MMP.Flips.relativePicardNumber`: `ρ(X/Z) = dim N¹(X/Z)`.
* `MMP.Flips.IsNegativeExtremalContraction`: `E`-negative extremal contractions.
* `MMP.Flips.IsGeneralizedFlip`, `MMP.Flips.IsFlip`.

## Implementation notes

An `ℝ`-Cartier divisor with a presentation `∑ r_j L_j` is an element of
`MMP.Mori.KCartierDivisor ℝ X`, a formal `ℝ`-combination of Cartier divisors. Numerical
equivalence over `Z` only sees intersection numbers with the curves contracted to points, which
are computed from the presentation, so `N¹(X/Z)` is the quotient of these combinations by the
numerically `f`-trivial ones: a combination whose underlying `ℝ`-divisor vanishes has zero
intersection numbers, so the quotient is also that of the `ℝ`-Cartier `ℝ`-divisors.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.26.3, 2.26.4,
  2.35
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 0.4, 1.17
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori

attribute [mmp "def_fa2_relative_cone_of_curves"] MMP.Mori.RelativeNumericalCurveClasses
  MMP.Mori.RelativeNumericalCurveClasses.instTopologicalSpace
  MMP.Mori.relativeClosedConeOfCurves MMP.Mori.IsExtremalRay

section Numerical

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (f : X ⟶ Y)

/-- An extremal ray `R` of `NE(X/Y)` is *`A`-negative*, for an `ℝ`-Cartier divisor `A` (with a
presentation), if `A · γ < 0` for a generator `γ ≠ 0` of `R = ℝ_{≥0} γ`. -/
@[mmp "def_fa2_relative_cone_of_curves"]
def IsNegativeRelativeExtremalRay (A : KCartierDivisor ℝ X)
    (R : Set (RelativeNumericalCurveClasses sX f)) : Prop :=
  IsExtremalRay ℝ (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) R ∧
    ∃ γ ∈ R, γ ≠ 0 ∧ RelativeNumericalCurveClasses.intersectionNumber A γ < 0

/-- The `ℝ`-Cartier divisors `D` (with presentations) that are *numerically `f`-trivial*:
`D · C = 0` for every proper irreducible curve `C ⊆ X` with `f(C)` a point. -/
def relativeNumericallyTrivialDivisors : Submodule ℝ (KCartierDivisor ℝ X) :=
  LinearMap.ker (LinearMap.pi fun C : {C : ProperCurve sX // C.IsContractedBy f} =>
    (OneCycle.intersectionPairing (sX := sX)).flip (C.1.cycle ℝ))

/-- A divisor `D` is numerically `f`-trivial if and only if `C · D = 0` for every proper curve
`C` contracted by `f`. -/
theorem mem_relativeNumericallyTrivialDivisors {D : KCartierDivisor ℝ X} :
    D ∈ relativeNumericallyTrivialDivisors sX f ↔
      ∀ C : ProperCurve sX, C.IsContractedBy f → (C.cycle ℝ).intersectionNumber D = 0 := by
  simp only [relativeNumericallyTrivialDivisors, LinearMap.mem_ker, funext_iff,
    LinearMap.pi_apply, LinearMap.flip_apply, Pi.zero_apply, Subtype.forall]
  rfl

/-- The real vector space `N¹(X/Y)` of `ℝ`-Cartier divisors on `X` modulo numerical equivalence
over `Y`, i.e. modulo the numerically `f`-trivial ones. -/
@[mmp "def_fa2_relative_picard_number"]
abbrev RelativeNumericalDivisorClasses : Type _ :=
  KCartierDivisor ℝ X ⧸ relativeNumericallyTrivialDivisors sX f

/-- The *relative Picard number* `ρ(X/Y) = dim_ℝ N¹(X/Y) ∈ ℕ ∪ {∞}`. -/
@[mmp "def_fa2_relative_picard_number"]
def relativePicardNumber : ℕ∞ :=
  (Module.rank ℝ (RelativeNumericalDivisorClasses sX f)).toENat

end Numerical

/-! ### Extremal contractions and flips -/

section Flips

variable (k : Type u) [Field k] {X Z : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sZ : Z ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- Let `X` be a normal variety and `E` an `ℝ`-Cartier divisor on `X`. A contraction `f : X ⟶ Z`
to a normal variety is an *`E`-negative extremal contraction* if `-E` is `f`-ample and
`ρ(X/Z) = 1`. -/
@[mmp "def_fa2_relative_picard_number_one_contraction"]
structure IsNegativeExtremalContraction (E : RDivisor X) (f : X ⟶ Z) : Prop where
  /-- `X` is a normal variety. -/
  isNormalVariety_source : IsNormalVariety k sX
  /-- `Z` is a normal variety. -/
  isNormalVariety_target : IsNormalVariety k sZ
  /-- `E` is `ℝ`-Cartier. -/
  isCartierCombination : IsCartierCombination E
  /-- `f` is a contraction. -/
  isContraction : IsContraction k sZ sX f
  /-- `-E` is `f`-ample. -/
  isRelativelyAntiAmple : IsRelativelyAntiAmple f E
  /-- `ρ(X/Z) = 1`. -/
  relativePicardNumber_eq_one : relativePicardNumber sX f = 1

variable {X' : Scheme.{u}} (sX' : X' ⟶ Spec (.of k)) [IsLocallyNoetherian X'] [IsNormal X']
  [CompactSpace X']

/-- Let `f : X ⟶ Z` be a contraction of normal varieties and `E` an `ℝ`-Cartier divisor on `X`
with `-E` `f`-ample. A *generalized flip* (*generalized opposite*) of `f` with respect to `E` is a
proper morphism `f⁺ : X⁺ ⟶ Z` from a normal variety together with a modification
`g : X ⤏ X⁺` of `f` into `f⁺` which is a morphism in codimension one, such that `f⁺` is a small
birational contraction and `E⁺ = g_*(E)` is `ℝ`-Cartier and `f⁺`-ample. -/
@[mmp "def_fa2_generalized_flip"]
structure IsGeneralizedFlip (E : RDivisor X) (f : X ⟶ Z) (fp : X' ⟶ Z) (g : X.RationalMap X') :
    Prop where
  /-- `X` is a normal variety. -/
  isNormalVariety_source : IsNormalVariety k sX
  /-- `Z` is a normal variety. -/
  isNormalVariety_target : IsNormalVariety k sZ
  /-- `X⁺` is a normal variety. -/
  isNormalVariety_flip : IsNormalVariety k sX'
  /-- `f` is a contraction. -/
  isContraction : IsContraction k sZ sX f
  /-- `E` is `ℝ`-Cartier. -/
  isCartierCombination : IsCartierCombination E
  /-- `-E` is `f`-ample. -/
  isRelativelyAntiAmple : IsRelativelyAntiAmple f E
  /-- `f⁺` is proper. -/
  isProper : IsProper fp
  /-- `g` is a modification of `f` into `f⁺`. -/
  isModificationOf : IsModificationOf f fp g
  /-- `g` is a morphism in codimension one. -/
  isMorphismInCodimOne : RationalMap.IsMorphismInCodimOne g
  /-- `f⁺` is a small birational contraction. -/
  isSmall : IsSmall k sZ sX' fp
  /-- `E⁺ = g_*(E)` is `ℝ`-Cartier. -/
  isCartierCombination_transform :
    IsCartierCombination (Mori.RationalMap.transformDivisor g E)
  /-- `E⁺ = g_*(E)` is `f⁺`-ample. -/
  isRelativelyAmple_transform : IsRelativelyAmple fp (Mori.RationalMap.transformDivisor g E)

/-- If `f : X ⟶ Z` is itself a small birational contraction, a generalized flip of `f` with respect
to `E` is a *flip* (an *opposite*, an *`E`-flip*) of `f` with respect to `E`. -/
@[mmp "def_fa2_flip"]
structure IsFlip (E : RDivisor X) (f : X ⟶ Z) (fp : X' ⟶ Z) (g : X.RationalMap X') : Prop
    extends IsGeneralizedFlip k sX sZ sX' E f fp g where
  /-- `f` is a small birational contraction. -/
  isSmall_source : IsSmall k sZ sX f

end Flips

end MMP.Flips
