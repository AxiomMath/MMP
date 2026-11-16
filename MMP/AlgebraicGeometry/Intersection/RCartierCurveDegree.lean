/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.MMP.Contraction.Defs
public import MMP.AlgebraicGeometry.Positivity.RelativelyAmple
public import MMP.AlgebraicGeometry.Intersection.Nef
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative

/-!
# Intersection numbers, nefness and relative ampleness in *Flips and abundance*

Intersection numbers `D · C` of `ℝ`-Cartier divisors with proper curves (used in FA 2.11.2),
nefness (FA 1.1.1, 1.28), relative nefness (FA 2.15, 17.4.2), numerical equivalence over a base
(FA 2.16.3), and relative ampleness of Cartier and `ℝ`-Cartier divisors (FA 2.13.4).

FA defines `L · C = deg_{C̃} ν^* 𝒪_X(L)` through the normalization `ν : C̃ ⟶ C` of the curve. A
normalization is recorded by `MMP.Flips.IsCurveNormalization`: a finite birational morphism from a
normal integral scheme. The degree is Kollár–Mori's `MMP.Mori.Divisor.degreeOn` along the
composite `C̃ ⟶ C ⟶ X`.

Nefness of a line bundle or a `ℚ`-Cartier `ℚ`-divisor (FA 1.1.1) is Kollár–Mori's
`MMP.Mori.IsNef` and `MMP.Mori.QDivisor.IsNef`, and relative nefness of a `ℚ`-Cartier
`ℚ`-divisor (FA 17.4.2) is `MMP.Mori.QDivisor.IsRelativelyNef`; they are registered here.

## Main definitions

* `MMP.Flips.IsCurveNormalization`, `MMP.Flips.IsCartierIntersectionNumber`: `L · C`.
* `MMP.Flips.IsRIntersectionNumber`: `D · C = ∑ r_j (L_j · C)` for a presentation
  `D = ∑ r_j L_j`.
* `MMP.Flips.IsRelativelyNef`: `f`-nef `ℝ`-Cartier divisors.
* `MMP.Flips.IsNumericallyEquivalentOver`, `MMP.Flips.IsNumericallyTrivialOver`,
  `MMP.Flips.IsNumericallyTrivialOverOn`.
* `MMP.Flips.IsRelativelyAmpleCartier`, `MMP.Flips.IsRelativelyAmple`,
  `MMP.Flips.IsRelativelyAntiAmple`.

## Implementation notes

`D · C` depends on the presentation `D = ∑ r_j L_j` only through `D` (FA 2.11.2); the notions
built on it quantify over the presentation, existentially (a presentation computing nonnegative
numbers) or universally, as their docstrings say.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (1.1.1), 1.28,
  2.11.2, 2.13.4, 2.15, 2.16.3, 17.4.2
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori

attribute [mmp "def_fa1a_nef"] MMP.Mori.IsNef MMP.Mori.QDivisor.IsNef
attribute [mmp "def_fa17_relatively_nef"] MMP.Mori.QDivisor.IsRelativelyNef

/-! ### Intersection numbers with curves -/

section Intersection

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A morphism `ν : C̃ ⟶ C` is a *normalization* of the integral curve `C`: `C̃` is a normal
integral scheme and `ν` is finite and birational. -/
structure IsCurveNormalization {C C' : Scheme.{u}} (ν : C' ⟶ C) : Prop where
  /-- `C̃` is integral. -/
  isIntegral : IsIntegral C'
  /-- `C̃` is normal. -/
  isNormal : IsNormal C'
  /-- `ν` is finite. -/
  isFinite : IsFinite ν
  /-- `ν` is birational. -/
  isBirationalMorphism : IsBirationalMorphism ν

/-- For a proper irreducible curve `C ⊆ X` with normalization `ν : C̃ ⟶ C` and a Cartier divisor
`L` on the normal variety `X`, the integer `d` is the intersection number
`L · C = deg_{C̃} ν^* 𝒪_X(L)`. -/
@[mmp "def_fa2_r_intersection_number"]
def IsCartierIntersectionNumber (C : ProperCurve sX) (L : Divisor X) (hL : L.IsCartier) (d : ℤ) :
    Prop :=
  ∃ (C' : Scheme.{u}) (ν : C' ⟶ C.scheme) (hν : IsCurveNormalization ν)
    (hdim : topologicalKrullDim C' ≤ 1),
    haveI := hν.isFinite
    haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
    d = L.degreeOn k sX (ν ≫ C.ι) hdim hL

/-- For an `ℝ`-Cartier divisor `D` with a chosen presentation `D = ∑ r_j L_j` (`L_j` Cartier) and a
proper irreducible curve `C`, the real number `x` is the intersection number
`D · C = ∑ r_j (L_j · C)`. -/
@[mmp "def_fa2_r_intersection_number"]
def IsRIntersectionNumber (D : RDivisor X) {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X)
    (C : ProperCurve sX) (x : ℝ) : Prop :=
  ∃ (hL : ∀ j, (L j).IsCartier) (d : Fin m → ℤ),
    D = ∑ j, r j • Divisor.toRDivisor (L j) ∧
    (∀ j, IsCartierIntersectionNumber k sX C (L j) (hL j) (d j)) ∧ x = ∑ j, r j * d j

/-! ### Relative nefness and numerical equivalence over a base -/

variable {Y : Scheme.{u}}

/-- An `ℝ`-Cartier divisor `D` on `X` is *`f`-nef* (*nef over `Y`*), for a proper morphism
`f : X ⟶ Y` of normal varieties, if `D · C ≥ 0` for every irreducible curve `C ⊆ X` with `f(C)` a
point: for a presentation `D = ∑ r_j L_j`, every value of `D · C` is nonnegative. For `Y` a point
(and `X` proper) this is *nef*. -/
@[mmp "def_fa2_relatively_nef"]
def IsRelativelyNef (f : X ⟶ Y) (D : RDivisor X) : Prop :=
  ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X), (∀ j, (L j).IsCartier) ∧
    D = ∑ j, r j • Divisor.toRDivisor (L j) ∧
    ∀ C : ProperCurve sX, C.IsContractedBy f →
      ∀ x : ℝ, IsRIntersectionNumber k sX D r L C x → 0 ≤ x

/-- `ℝ`-Cartier divisors `N₁, N₂` on `X` are *numerically equivalent over `Y`*, `N₁ ≡_f N₂`, for a
proper morphism `f : X ⟶ Y` of normal varieties, if `N₁ · C = N₂ · C` for every irreducible
curve `C ⊆ X` with `f(C)` a point (computed with any presentations of `N₁` and `N₂`). -/
@[mmp "def_fa2_relative_numerical_equivalence"]
def IsNumericallyEquivalentOver (f : X ⟶ Y) (N₁ N₂ : RDivisor X) : Prop :=
  IsCartierCombination N₁ ∧ IsCartierCombination N₂ ∧
    ∀ C : ProperCurve sX, C.IsContractedBy f →
      ∀ (m₁ : ℕ) (r₁ : Fin m₁ → ℝ) (L₁ : Fin m₁ → Divisor X) (x₁ : ℝ)
        (m₂ : ℕ) (r₂ : Fin m₂ → ℝ) (L₂ : Fin m₂ → Divisor X) (x₂ : ℝ),
        IsRIntersectionNumber k sX N₁ r₁ L₁ C x₁ → IsRIntersectionNumber k sX N₂ r₂ L₂ C x₂ →
          x₁ = x₂

/-- An `ℝ`-Cartier divisor `N` is *numerically `f`-trivial* if `N ≡_f 0`. -/
@[mmp "def_fa2_relative_numerical_equivalence"]
def IsNumericallyTrivialOver (f : X ⟶ Y) (N : RDivisor X) : Prop :=
  IsNumericallyEquivalentOver k sX f N 0

/-- An `ℝ`-Cartier divisor `N` is *numerically `f`-trivial on a closed subset `W ⊆ X`* if
`N · C = 0` for every irreducible curve `C ⊆ W` with `f(C)` a point. -/
@[mmp "def_fa2_relative_numerical_equivalence"]
def IsNumericallyTrivialOverOn (f : X ⟶ Y) (N : RDivisor X) (W : Closeds X) : Prop :=
  IsCartierCombination N ∧
    ∀ C : ProperCurve sX, C.IsContractedBy f → C.point ∈ W →
      ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
        IsRIntersectionNumber k sX N r L C x → x = 0

end Intersection

/-! ### Relative ampleness -/

section Ample

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- A Cartier divisor `L` on `Y` is *`f`-ample*, for a proper morphism `f : Y ⟶ X` of varieties,
if for every affine open `U ⊆ X` the restriction `𝒪_Y(L)|_{f⁻¹(U)}` is an ample line bundle on
`f⁻¹(U)`. -/
@[mmp "def_fa2_relatively_ample_cartier"]
def IsRelativelyAmpleCartier (f : Y ⟶ X) (L : Divisor Y) : Prop :=
  ∃ hL : L.IsCartier,
    haveI := hL.isInvertibleModule_divisorialSheaf
    ∀ U : X.Opens, IsAffineOpen U →
      Stacks.Ample.IsAmple (f ⁻¹ᵁ U).toScheme
        ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj
          L.divisorialSheaf)

/-- An `ℝ`-Cartier divisor `A` on `Y` is *`f`-ample* (*ample over `X`*), for a proper morphism
`f : Y ⟶ X` of normal varieties, if `A = ∑_{j=1}^m r_j A_j` with `m ≥ 1`, real `r_j > 0` and
`f`-ample Cartier divisors `A_j`. For `X` a point this is *ample*. -/
@[mmp "def_fa2_relatively_ample"]
def IsRelativelyAmple (f : Y ⟶ X) (A : RDivisor Y) : Prop :=
  ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor Y), 1 ≤ m ∧ (∀ j, 0 < r j) ∧
    (∀ j, IsRelativelyAmpleCartier f (L j)) ∧ A = ∑ j, r j • Divisor.toRDivisor (L j)

/-- An `ℝ`-Cartier divisor `A` is *`f`-anti-ample* if `-A` is `f`-ample. -/
@[mmp "def_fa2_relatively_ample"]
def IsRelativelyAntiAmple (f : Y ⟶ X) (A : RDivisor Y) : Prop :=
  IsRelativelyAmple f (-A)

end Ample

end MMP.Flips
