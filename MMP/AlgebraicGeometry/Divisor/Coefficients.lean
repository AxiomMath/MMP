module

public import MMP.AlgebraicGeometry.Divisor.Cartier
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Basic.Real.Basic

/-!
# `ℚ`- and `ℝ`-divisors (Lazarsfeld §1.3)

For a scheme `X` and a commutative ring `R` (here `ℚ` or `ℝ`), the `R`-divisors are the elements
of `Div_R(X) = Div(X) ⊗_ℤ R`. Everything Lazarsfeld says about them is phrased through a
*representation* `D = ∑ cᵢ Aᵢ` with `cᵢ ∈ R` and `Aᵢ ∈ Div(X)`, i.e. `D = ∑ Aᵢ ⊗ cᵢ`; the
definitions below are stated for an arbitrary coefficient ring and specialized to `ℚ` and `ℝ`.

## Main definitions

* `MMP.Intersection.CartierDivisorWithCoeffs R X`, `MMP.Intersection.QCartierDivisor`,
  `MMP.Intersection.RCartierDivisor`, and `MMP.Intersection.CartierDivisorWithCoeffs.ofDivisor`.
* `MMP.Intersection.CartierDivisorWithCoeffs.IsRepresentation`: `D = ∑ cᵢ Aᵢ`.
* `MMP.Intersection.CartierDivisorWithCoeffs.IsIntegral`,
  `MMP.Intersection.CartierDivisorWithCoeffs.IsEffective`.
* `MMP.Intersection.CartierDivisorWithCoeffs.Supports`: a codimension-one closed set supporting
  `D`.
* `MMP.Intersection.CartierDivisorWithCoeffs.IsPullback`: pull-back relative to a
  representation.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry TensorProduct

namespace MMP.Intersection

variable {X Y : Scheme.{u}}

/-- The group `Div(X) ⊗_ℤ R` of Cartier divisors with coefficients in `R`. -/
@[mmp "def_p01a_q_divisor", mmp "def_p01a_r_divisor"]
abbrev CartierDivisorWithCoeffs (R : Type*) [CommRing R] (X : Scheme.{u}) :=
  X.CartierDivisor ⊗[ℤ] R

/-- `Div_ℚ(X) = Div(X) ⊗_ℤ ℚ`, the `ℚ`-divisors (Lazarsfeld Def. 1.3.1). -/
@[mmp "def_p01a_q_divisor"]
abbrev QCartierDivisor (X : Scheme.{u}) := CartierDivisorWithCoeffs ℚ X

/-- `Div_ℝ(X) = Div(X) ⊗_ℤ ℝ`, the `ℝ`-divisors (Lazarsfeld §1.3.B). -/
@[mmp "def_p01a_r_divisor"]
abbrev RCartierDivisor (X : Scheme.{u}) := CartierDivisorWithCoeffs ℝ X

namespace CartierDivisorWithCoeffs

variable {R : Type*} [CommRing R]

variable (R) in
/-- The map `Div(X) → Div_R(X)`, `A ↦ 1 ⊗ A`. -/
@[mmp "def_p01a_q_divisor", mmp "def_p01a_r_divisor"]
def ofDivisor : X.CartierDivisor →+ CartierDivisorWithCoeffs R X where
  toFun A := A ⊗ₜ (1 : R)
  map_zero' := zero_tmul _ _
  map_add' A B := add_tmul A B 1

/-- `D = ∑ᵢ cᵢ Aᵢ` (Lazarsfeld (1.13)). -/
@[mmp "def_p01a_q_divisor", mmp "def_p01a_r_divisor"]
def IsRepresentation (D : CartierDivisorWithCoeffs R X) {m : ℕ} (c : Fin m → R)
    (A : Fin m → X.CartierDivisor) : Prop :=
  D = ∑ i, A i ⊗ₜ c i

/-- Every `R`-divisor has a representation. -/
theorem exists_isRepresentation (D : CartierDivisorWithCoeffs R X) :
    ∃ (m : ℕ) (c : Fin m → R) (A : Fin m → X.CartierDivisor), IsRepresentation D c A := by
  induction D using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp [IsRepresentation]⟩
  | tmul A r => exact ⟨1, fun _ => r, fun _ => A, by simp [IsRepresentation]⟩
  | add D D' hD hD' =>
    obtain ⟨m, c, A, h⟩ := hD
    obtain ⟨m', c', A', h'⟩ := hD'
    refine ⟨m + m', Fin.append c c', Fin.append A A', ?_⟩
    simp only [IsRepresentation] at h h' ⊢
    rw [Fin.sum_univ_add, h, h']
    simp

/-- An `R`-divisor is *integral* if it lies in the image of `Div(X) → Div_R(X)`. -/
@[mmp "def_p01a_q_divisor"]
def IsIntegral (D : CartierDivisorWithCoeffs R X) : Prop := D ∈ Set.range (ofDivisor R (X := X))

/-- An `R`-divisor is *effective* if it can be written `∑ cᵢ Aᵢ` with all `cᵢ ≥ 0` and all `Aᵢ`
effective. -/
@[mmp "def_p01a_q_divisor", mmp "def_p01a_r_divisor"]
def IsEffective [PartialOrder R] (D : CartierDivisorWithCoeffs R X) : Prop :=
  ∃ (m : ℕ) (c : Fin m → R) (A : Fin m → X.CartierDivisor),
    IsRepresentation D c A ∧ ∀ i, 0 ≤ c i ∧ MMP.Intersection.IsEffective (A i)

/-- A closed subset `E ⊆ X` of codimension one *supports* `D` (Lazarsfeld Def. 1.3.2) if `D`
admits a representation `∑ cᵢ Aᵢ` with `⋃ Supp Aᵢ ⊆ E`. The codimension is that of the reduced
closed subscheme on `E`, in the sense of `MMP.Intersection.Scheme.IdealSheafData.codim`. -/
@[mmp "def_p01a_q_divisor_support", mmp "def_p01a_r_divisor"]
def Supports (E : Closeds X) (D : CartierDivisorWithCoeffs R X) : Prop :=
  Scheme.IdealSheafData.codim (Scheme.IdealSheafData.vanishingIdeal E) = 1 ∧
    ∃ (m : ℕ) (c : Fin m → R) (A : Fin m → X.CartierDivisor),
      IsRepresentation D c A ∧ (⋃ i, cartierSupport (A i)) ⊆ E

/-- An `R`-divisor `D'` on `Y` is *a pull-back* of `D = ∑ cᵢ Aᵢ` along `f : Y ⟶ X`, relative to
that representation (Lazarsfeld Def. 1.3.3(iv)): no associated point of `Y` maps into any
`Supp Aᵢ`, and `D' = ∑ cᵢ A'ᵢ` with each `A'ᵢ` a pull-back of `Aᵢ`. -/
@[mmp "def_p01a_q_divisor_pullback", mmp "def_p01a_r_divisor"]
def IsPullback (f : Y ⟶ X) (D : CartierDivisorWithCoeffs R X) {m : ℕ} (c : Fin m → R)
    (A : Fin m → X.CartierDivisor) (D' : CartierDivisorWithCoeffs R Y) : Prop :=
  IsRepresentation D c A ∧ (∀ i, PullbackCondition f (A i)) ∧
    ∃ A' : Fin m → Y.CartierDivisor, IsRepresentation D' c A' ∧
      ∀ i, MMP.Intersection.IsPullback f (A i) (A' i)

end CartierDivisorWithCoeffs

end MMP.Intersection
