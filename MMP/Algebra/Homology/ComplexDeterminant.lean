module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Length
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# The determinant of a three-term complex of finite free modules

Let `F₂ → F₁ → F₀` be a complex of finite free modules over a commutative ring `R`, given by
matrices `A : Matrix ι₁ ι₂ R`, `B : Matrix ι₀ ι₁ R` with `B * A = 0`, and let
`e : ι₂ ⊕ ι₀ ≃ ι₁` record that the alternating rank is zero.  Over a field `K`, when the complex is
exact the Cayley determinant is `(det [A | S])⁻¹` for any section `S` of `B` (that is
`B * S = 1`); it does not depend on the section.  For a ring `R` with an algebra map to a field `K`
(typically `K = FractionRing R`), `complexDet K A B e` is the Cayley determinant of the base
change.

## Main definitions

* `MMP.Chow.splitMatrix`: the square matrix `[A | S]`, reindexed by `e`.
* `MMP.Chow.IsSplitExact`: `B` has a section `S` with `[A | S]` invertible.
* `MMP.Chow.cayleyDet`: the Cayley determinant of a complex over a field.
* `MMP.Chow.complexDet`: the Cayley determinant of the base change to a field `K` of a complex over
  `R`.

## Main results

* `MMP.Chow.cayleyDet_eq_inv_det`: independence of the section.
* `MMP.Chow.cayleyDet_change`, `MMP.Chow.exists_complexDet_change`: change of bases multiplies the
  determinant by a unit.
* `MMP.Chow.exists_unit_complexDet_of_exact`: for a complex that is exact over `R` the
  determinant is a unit of `R`.
* `MMP.Chow.map_cayleyDet`, `MMP.Chow.complexDet_map`, `MMP.Chow.complexDet_map_of_injective`:
  compatibility with field homomorphisms and with injective homomorphisms of domains.
* `MMP.Chow.exists_unit_complexDet_eq_pow_length`: over a discrete valuation ring the order of the
  determinant is the length of `H₀`.
* `MMP.Chow.exists_algebraMap_complexDet_eq`: over a Noetherian normal domain, if the complex
  localized at each height-one prime is exact at `F₁` with `H₀` of finite length, the determinant
  lies in `R`.

## Implementation notes

The sign convention is that of the determinant of a torsion cokernel: for `F₁ → F₀` injective with
`F₂ = 0` the determinant is `det B`, so its order equals the length of the cokernel.
-/

@[expose] public section

open Matrix

namespace MMP.Chow

section Field

variable {K : Type*} [Field K] {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]
  [DecidableEq ι₂] [DecidableEq ι₁] [DecidableEq ι₀]

/-- The square matrix `[A | S]` whose columns are those of `A : F₂ → F₁` followed by those of
`S : F₀ → F₁`, with its rows reindexed along `e : ι₂ ⊕ ι₀ ≃ ι₁`. -/
def splitMatrix {R : Type*} (e : ι₂ ⊕ ι₀ ≃ ι₁) (A : Matrix ι₁ ι₂ R) (S : Matrix ι₁ ι₀ R) :
    Matrix (ι₂ ⊕ ι₀) (ι₂ ⊕ ι₀) R :=
  Matrix.fromCols (A.submatrix e id) (S.submatrix e id)

/-- A complex `ι₂ → ι₁ → ι₀` over a field is *split exact* if `B` has a section `S` such that
`[A | S]` is invertible; for a complex (`B * A = 0`) this is exactness. -/
def IsSplitExact (e : ι₂ ⊕ ι₀ ≃ ι₁) (A : Matrix ι₁ ι₂ K) (B : Matrix ι₀ ι₁ K) : Prop :=
  ∃ S : Matrix ι₁ ι₀ K, B * S = 1 ∧ (splitMatrix e A S).det ≠ 0

open Classical in
/-- The Cayley determinant of a complex `F₂ → F₁ → F₀` over a field with zero alternating rank:
`(det [A | S])⁻¹` for a section `S` of `B`, and `0` when the complex is not exact. -/
noncomputable def cayleyDet (e : ι₂ ⊕ ι₀ ≃ ι₁) (A : Matrix ι₁ ι₂ K) (B : Matrix ι₀ ι₁ K) : K :=
  if h : IsSplitExact e A B then ((splitMatrix e A h.choose).det)⁻¹ else 0

omit [DecidableEq ι₂] [DecidableEq ι₁] [DecidableEq ι₀] in
/-- Multiplying `[A | S]` on the left by `B`, with columns reindexed along `e`, gives
`[B * A | B * S]`. -/
lemma submatrix_mul_splitMatrix (e : ι₂ ⊕ ι₀ ≃ ι₁) (A : Matrix ι₁ ι₂ K) (B : Matrix ι₀ ι₁ K)
    (S : Matrix ι₁ ι₀ K) :
    B.submatrix id e * splitMatrix e A S = Matrix.fromCols (B * A) (B * S) := by
  rw [splitMatrix, Matrix.mul_fromCols, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  simp

omit [DecidableEq ι₁] in
/-- For a complex with `B * A = 0`, two sections of `B` give the same determinant of `[A | S]`,
provided one of them gives an invertible `[A | S]`. -/
lemma det_splitMatrix_eq {e : ι₂ ⊕ ι₀ ≃ ι₁} {A : Matrix ι₁ ι₂ K} {B : Matrix ι₀ ι₁ K}
    (hBA : B * A = 0) {S₀ S₁ : Matrix ι₁ ι₀ K} (h₀ : B * S₀ = 1)
    (hdet : (splitMatrix e A S₀).det ≠ 0) (h₁ : B * S₁ = 1) :
    (splitMatrix e A S₁).det = (splitMatrix e A S₀).det := by
  set P₀ := splitMatrix e A S₀ with hP₀
  have hP₀u : IsUnit P₀.det := isUnit_iff_ne_zero.2 hdet
  set X : Matrix (ι₂ ⊕ ι₀) ι₀ K := P₀⁻¹ * S₁.submatrix e id with hX
  have hPX : P₀ * X = S₁.submatrix e id := by
    rw [hX, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP₀u, Matrix.one_mul]
  have hBP := submatrix_mul_splitMatrix e A B S₀
  rw [hBA, h₀] at hBP
  have hX2 : X.toRows₂ = 1 := by
    have h1 : B.submatrix id e * (S₁.submatrix e id) = 1 := by
      rw [Matrix.submatrix_mul_equiv, h₁]
      simp
    rw [← hPX, ← Matrix.mul_assoc, hBP] at h1
    have h2 := Matrix.fromCols_mul_fromRows (0 : Matrix ι₀ ι₂ K) (1 : Matrix ι₀ ι₀ K)
      X.toRows₁ X.toRows₂
    rw [Matrix.fromRows_toRows, h1] at h2
    simpa using h2.symm
  have hA : A.submatrix e id = P₀ * Matrix.fromRows (1 : Matrix ι₂ ι₂ K) 0 := by
    rw [hP₀, splitMatrix, Matrix.fromCols_mul_fromRows]
    simp
  have e1 : S₁.submatrix e id = P₀ * Matrix.fromRows X.toRows₁ (1 : Matrix ι₀ ι₀ K) := by
    rw [← hPX]
    congr 1
    rw [← hX2]
    exact (Matrix.fromRows_toRows X).symm
  have hblk : Matrix.fromCols (Matrix.fromRows (1 : Matrix ι₂ ι₂ K) (0 : Matrix ι₀ ι₂ K))
      (Matrix.fromRows X.toRows₁ (1 : Matrix ι₀ ι₀ K)) = Matrix.fromBlocks 1 X.toRows₁ 0 1 := by
    ext (i | i) (j | j) <;> simp [Matrix.fromCols, Matrix.fromRows, Matrix.fromBlocks] <;> rfl
  have : splitMatrix e A S₁ = P₀ * Matrix.fromBlocks 1 X.toRows₁ 0 1 := by
    rw [← hblk, Matrix.mul_fromCols, ← hA, ← e1]
    rfl
  rw [this, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
  simp

omit [DecidableEq ι₁] in
/-- The Cayley determinant equals `(det [A | S])⁻¹` for any section `S` of `B` with
`det [A | S] ≠ 0`. -/
lemma cayleyDet_eq_inv_det {e : ι₂ ⊕ ι₀ ≃ ι₁} {A : Matrix ι₁ ι₂ K} {B : Matrix ι₀ ι₁ K}
    (hBA : B * A = 0) {S : Matrix ι₁ ι₀ K} (hS : B * S = 1)
    (hdet : (splitMatrix e A S).det ≠ 0) :
    cayleyDet e A B = ((splitMatrix e A S).det)⁻¹ := by
  have h : IsSplitExact e A B := ⟨S, hS, hdet⟩
  rw [cayleyDet, dif_pos h]
  congr 1
  exact (det_splitMatrix_eq hBA h.choose_spec.1 h.choose_spec.2 hS).symm

omit [DecidableEq ι₁] in
/-- The Cayley determinant of a complex that is not split exact is `0`. -/
lemma cayleyDet_of_not_isSplitExact {e : ι₂ ⊕ ι₀ ≃ ι₁} {A : Matrix ι₁ ι₂ K}
    {B : Matrix ι₀ ι₁ K} (h : ¬ IsSplitExact e A B) : cayleyDet e A B = 0 := by
  simp [cayleyDet, h]

omit [Fintype ι₂] [Fintype ι₁] [Fintype ι₀] [DecidableEq ι₂] [DecidableEq ι₁] [DecidableEq ι₀] in
/-- Forming `[A | S]` commutes with applying a ring homomorphism entrywise. -/
lemma splitMatrix_map {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
    (e : ι₂ ⊕ ι₀ ≃ ι₁) (A : Matrix ι₁ ι₂ R) (S : Matrix ι₁ ι₀ R) :
    splitMatrix e (A.map φ) (S.map φ) = (splitMatrix e A S).map φ := by
  ext (i | i) (j | j) <;> simp [splitMatrix, Matrix.fromCols]

omit [Fintype ι₁] [DecidableEq ι₁] in
/-- The determinant of `[A | S]` commutes with applying a ring homomorphism entrywise. -/
lemma det_splitMatrix_map {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
    (e : ι₂ ⊕ ι₀ ≃ ι₁) (A : Matrix ι₁ ι₂ R) (S : Matrix ι₁ ι₀ R) :
    (splitMatrix e (A.map φ) (S.map φ)).det = φ (splitMatrix e A S).det := by
  rw [splitMatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

omit [DecidableEq ι₁] in
/-- The base change of a split exact complex along a field homomorphism is split exact. -/
theorem isSplitExact_map {K' : Type*} [Field K'] (φ : K →+* K') {e : ι₂ ⊕ ι₀ ≃ ι₁}
    {A : Matrix ι₁ ι₂ K} {B : Matrix ι₀ ι₁ K} (h : IsSplitExact e A B) :
    IsSplitExact e (A.map φ) (B.map φ) := by
  obtain ⟨S, hS, hd⟩ := h
  refine ⟨S.map φ, ?_, ?_⟩
  · rw [← Matrix.map_mul, hS]
    simp
  · rw [det_splitMatrix_map]
    exact (map_ne_zero φ).2 hd

omit [DecidableEq ι₁] in
/-- The Cayley determinant of a split exact complex commutes with field homomorphisms. -/
theorem map_cayleyDet {K' : Type*} [Field K'] (φ : K →+* K') {e : ι₂ ⊕ ι₀ ≃ ι₁}
    {A : Matrix ι₁ ι₂ K} {B : Matrix ι₀ ι₁ K} (hBA : B * A = 0) (h : IsSplitExact e A B) :
    cayleyDet e (A.map φ) (B.map φ) = φ (cayleyDet e A B) := by
  obtain ⟨S, hS, hd⟩ := h
  have hBA' : B.map φ * A.map φ = 0 := by
    rw [← Matrix.map_mul, hBA]
    simp
  have hS' : B.map φ * S.map φ = 1 := by
    rw [← Matrix.map_mul, hS]
    simp
  rw [cayleyDet_eq_inv_det hBA hS hd,
    cayleyDet_eq_inv_det hBA' hS' (by rw [det_splitMatrix_map]; exact (map_ne_zero φ).2 hd),
    det_splitMatrix_map, map_inv₀]

omit [DecidableEq ι₂] [DecidableEq ι₁] [DecidableEq ι₀] in
/-- Reindexing the rows of `P * X * Y` along `e` gives `P.submatrix e e * X.submatrix e id * Y`. -/
lemma submatrix_mul_mul {R : Type*} [NonUnitalNonAssocSemiring R] {n : Type*} [Fintype n]
    (e : ι₂ ⊕ ι₀ ≃ ι₁) (P : Matrix ι₁ ι₁ R) (X : Matrix ι₁ n R) (Y : Matrix n n R) :
    (P * X * Y).submatrix e id = P.submatrix e e * X.submatrix e id * Y := by
  have a1 := Matrix.submatrix_mul_equiv (P * X) Y e (Equiv.refl _) id
  have a2 := Matrix.submatrix_mul_equiv P X e e id
  simp only [Equiv.coe_refl, Matrix.submatrix_id_id] at a1
  rw [← a1, ← a2]

/-- **Change of bases.** Changing the bases of `F₂`, `F₁`, `F₀` multiplies the Cayley determinant
by the explicit factor `(det P₁ * det P₂ * det P₀')⁻¹`. -/
theorem cayleyDet_change {e : ι₂ ⊕ ι₀ ≃ ι₁} {A : Matrix ι₁ ι₂ K} {B : Matrix ι₀ ι₁ K}
    (hBA : B * A = 0) (h : IsSplitExact e A B) {P₁ P₁' : Matrix ι₁ ι₁ K} (hP₁ : P₁ * P₁' = 1)
    {P₂ P₂' : Matrix ι₂ ι₂ K} (hP₂ : P₂ * P₂' = 1) {P₀ P₀' : Matrix ι₀ ι₀ K}
    (hP₀ : P₀ * P₀' = 1) :
    cayleyDet e (P₁ * A * P₂) (P₀ * B * P₁') =
      (P₁.det * P₂.det * P₀'.det)⁻¹ * cayleyDet e A B := by
  obtain ⟨S, hS, hd⟩ := h
  have hP₁' : P₁' * P₁ = 1 := mul_eq_one_comm.1 hP₁
  have hBA' : (P₀ * B * P₁') * (P₁ * A * P₂) = 0 := by
    calc (P₀ * B * P₁') * (P₁ * A * P₂) = P₀ * B * (P₁' * P₁) * A * P₂ := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by
        rw [hP₁', Matrix.mul_one, Matrix.mul_assoc P₀, hBA]
        simp
  have hS' : (P₀ * B * P₁') * (P₁ * S * P₀') = 1 := by
    calc (P₀ * B * P₁') * (P₁ * S * P₀') = P₀ * (B * ((P₁' * P₁) * S)) * P₀' := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hP₁', Matrix.one_mul, hS, Matrix.mul_one, hP₀]
  have hsplit : splitMatrix e (P₁ * A * P₂) (P₁ * S * P₀') =
      P₁.submatrix e e * splitMatrix e A S * Matrix.fromBlocks P₂ 0 0 P₀' := by
    rw [splitMatrix, splitMatrix, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks,
      submatrix_mul_mul, submatrix_mul_mul]
    simp
  have hd₁ : P₁.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse hP₁
  have hd₂ : P₂.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse hP₂
  have hd₀ : P₀'.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hP₀
  have hdet : (splitMatrix e (P₁ * A * P₂) (P₁ * S * P₀')).det =
      P₁.det * (splitMatrix e A S).det * (P₂.det * P₀'.det) := by
    rw [hsplit, Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self,
      Matrix.det_fromBlocks_zero₂₁]
  have hne : (splitMatrix e (P₁ * A * P₂) (P₁ * S * P₀')).det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (mul_ne_zero hd₁ hd) (mul_ne_zero hd₂ hd₀)
  rw [cayleyDet_eq_inv_det hBA' hS' hne, cayleyDet_eq_inv_det hBA hS hd, hdet]
  field_simp

end Field

section Ring

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
  {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]
  [DecidableEq ι₂] [DecidableEq ι₁] [DecidableEq ι₀]

variable (K) in
/-- The determinant of the complex `R^ι₂ → R^ι₁ → R^ι₀` (matrices `A`, `B`, `e` recording that the
alternating rank is zero), as an element of a field `K` over `R`, typically `FractionRing R`: the
Cayley determinant of the base change to `K`, which is `0` unless the base change is exact. -/
noncomputable def complexDet (e : ι₂ ⊕ ι₀ ≃ ι₁) (A : Matrix ι₁ ι₂ R) (B : Matrix ι₀ ι₁ R) : K :=
  cayleyDet e (A.map (algebraMap R K)) (B.map (algebraMap R K))

omit [Fintype ι₂] [Fintype ι₀] [DecidableEq ι₂] [DecidableEq ι₁] [DecidableEq ι₀] in
/-- If `B * A = 0` over `R`, then the same holds for the base changes of `A` and `B` to `K`. -/
lemma map_mul_eq_zero {K : Type*} [Semiring K] [Algebra R K] {A : Matrix ι₁ ι₂ R}
    {B : Matrix ι₀ ι₁ R} (hBA : B * A = 0) : B.map (algebraMap R K) * A.map (algebraMap R K) = 0 := by
  rw [← Matrix.map_mul, hBA]
  simp

/-- **Change of bases (ring form).** Changing bases of the three free modules multiplies the
determinant by a unit of `R`. -/
theorem exists_complexDet_change {e : ι₂ ⊕ ι₀ ≃ ι₁} {A : Matrix ι₁ ι₂ R} {B : Matrix ι₀ ι₁ R}
    (hBA : B * A = 0) (h : IsSplitExact e (A.map (algebraMap R K)) (B.map (algebraMap R K)))
    (u₁ : (Matrix ι₁ ι₁ R)ˣ) (u₂ : (Matrix ι₂ ι₂ R)ˣ) (u₀ : (Matrix ι₀ ι₀ R)ˣ) :
    ∃ u : Rˣ, complexDet K e ((u₁ : Matrix ι₁ ι₁ R) * A * (u₂ : Matrix ι₂ ι₂ R))
      ((u₀ : Matrix ι₀ ι₀ R) * B * ((u₁⁻¹ : (Matrix ι₁ ι₁ R)ˣ) : Matrix ι₁ ι₁ R)) =
        algebraMap R K u * complexDet K e A B := by
  have hc : IsUnit ((u₁ : Matrix ι₁ ι₁ R).det * (u₂ : Matrix ι₂ ι₂ R).det *
      ((u₀⁻¹ : (Matrix ι₀ ι₀ R)ˣ) : Matrix ι₀ ι₀ R).det) :=
    ((Matrix.isUnits_det_units u₁).mul (Matrix.isUnits_det_units u₂)).mul
      (Matrix.isUnits_det_units _)
  refine ⟨(hc.unit)⁻¹, ?_⟩
  have key := cayleyDet_change (map_mul_eq_zero hBA) h
    (P₁ := (u₁ : Matrix ι₁ ι₁ R).map (algebraMap R K))
    (P₁' := ((u₁⁻¹ : (Matrix ι₁ ι₁ R)ˣ) : Matrix ι₁ ι₁ R).map (algebraMap R K))
    (P₂ := (u₂ : Matrix ι₂ ι₂ R).map (algebraMap R K))
    (P₂' := ((u₂⁻¹ : (Matrix ι₂ ι₂ R)ˣ) : Matrix ι₂ ι₂ R).map (algebraMap R K))
    (P₀ := (u₀ : Matrix ι₀ ι₀ R).map (algebraMap R K))
    (P₀' := ((u₀⁻¹ : (Matrix ι₀ ι₀ R)ˣ) : Matrix ι₀ ι₀ R).map (algebraMap R K))
    (by rw [← Matrix.map_mul, Units.mul_inv]; simp)
    (by rw [← Matrix.map_mul, Units.mul_inv]; simp)
    (by rw [← Matrix.map_mul, Units.mul_inv]; simp)
  simp only [complexDet, Matrix.map_mul]
  rw [key]
  congr 1
  have hcK : ((u₁ : Matrix ι₁ ι₁ R).map (algebraMap R K)).det *
      ((u₂ : Matrix ι₂ ι₂ R).map (algebraMap R K)).det *
      (((u₀⁻¹ : (Matrix ι₀ ι₀ R)ˣ) : Matrix ι₀ ι₀ R).map (algebraMap R K)).det =
      algebraMap R K ((u₁ : Matrix ι₁ ι₁ R).det * (u₂ : Matrix ι₂ ι₂ R).det *
        ((u₀⁻¹ : (Matrix ι₀ ι₀ R)ˣ) : Matrix ι₀ ι₀ R).det) := by
    simp only [← RingHom.mapMatrix_apply, ← RingHom.map_det, map_mul]
  rw [hcK, map_units_inv, hc.unit_spec]

omit [DecidableEq ι₂] [DecidableEq ι₁] [DecidableEq ι₀] in
/-- If `ker B ⊆ im A` and every `B v` is of the form `(B * C) z`, then `[A | C]` is surjective. -/
theorem surjective_splitMatrix_mulVec {e : ι₂ ⊕ ι₀ ≃ ι₁} {A : Matrix ι₁ ι₂ R} {B : Matrix ι₀ ι₁ R}
    (hex : ∀ v, B.mulVec v = 0 → ∃ w, A.mulVec w = v) (C : Matrix ι₁ ι₀ R)
    (hC : ∀ v, ∃ z, B.mulVec v = (B * C).mulVec z) :
    Function.Surjective (splitMatrix e A C).mulVec := by
  intro y
  set v : ι₁ → R := y ∘ e.symm with hv
  obtain ⟨z, hz⟩ := hC v
  obtain ⟨w, hw⟩ := hex (v - C.mulVec z) (by
    rw [Matrix.mulVec_sub, hz, Matrix.mulVec_mulVec, sub_self])
  refine ⟨Sum.elim w z, ?_⟩
  have h1 : (splitMatrix e A C).mulVec (Sum.elim w z) = (A.mulVec w + C.mulVec z) ∘ e := by
    rw [splitMatrix, Matrix.fromCols_mulVec_sumElim]
    have a1 : A.submatrix e id *ᵥ w = (A *ᵥ w) ∘ e := by
      simpa using Matrix.submatrix_mulVec_equiv A w e (Equiv.refl _)
    have a2 : C.submatrix e id *ᵥ z = (C *ᵥ z) ∘ e := by
      simpa using Matrix.submatrix_mulVec_equiv C z e (Equiv.refl _)
    rw [a1, a2]
    rfl
  rw [h1, hw]
  ext i
  simp [hv]

/-- For a commutative square `φ ∘ algebraMap R K = algebraMap R' K' ∘ f`, mapping a matrix along
`f` and then into `K'` agrees with mapping it into `K` and then along `φ`. -/
lemma map_map_algebraMap {R' K' : Type*} [CommRing R'] [Field K'] [Algebra R' K'] (f : R →+* R')
    (φ : K →+* K') (hφ : φ.comp (algebraMap R K) = (algebraMap R' K').comp f)
    {m n : Type*} (M : Matrix m n R) :
    (M.map f).map (algebraMap R' K') = (M.map (algebraMap R K)).map φ := by
  simp only [Matrix.map_map, ← RingHom.coe_comp, hφ]

omit [DecidableEq ι₁] in
/-- **Determinant through a section up to `B`.** Let `C : F₀ → F₁` over `R` be such that
`[A | C]` is surjective (hence invertible, by the rank count) and `D = B * C` has nonzero
determinant in `K`.  Then the complex is exact over `K` and its determinant is `det D` times a
unit of `R`. -/
theorem exists_unit_complexDet_eq_det_mul {e : ι₂ ⊕ ι₀ ≃ ι₁} {A : Matrix ι₁ ι₂ R}
    {B : Matrix ι₀ ι₁ R} (hBA : B * A = 0) (C : Matrix ι₁ ι₀ R)
    (hP : Function.Surjective (splitMatrix e A C).mulVec)
    (hD : algebraMap R K (B * C).det ≠ 0) :
    IsSplitExact e (A.map (algebraMap R K)) (B.map (algebraMap R K)) ∧
      ∃ u : Rˣ, complexDet K e A B = algebraMap R K u * algebraMap R K (B * C).det := by
  set P := splitMatrix e A C with hPdef
  have hunit : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.mulVec_surjective_iff_isUnit.1 hP)
  set D : Matrix ι₀ ι₀ K := (B * C).map (algebraMap R K) with hDdef
  have hDdet : D.det = algebraMap R K (B * C).det := by
    rw [hDdef, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hDu : IsUnit D.det := by
    rw [hDdet]
    exact isUnit_iff_ne_zero.2 hD
  have hDD : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv _ hDu
  have hdD' : D⁻¹.det = (algebraMap R K (B * C).det)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← hDdet, ← Matrix.det_mul, hDD]
    simp
  set S : Matrix ι₁ ι₀ K := C.map (algebraMap R K) * D⁻¹ with hSdef
  have hSK : B.map (algebraMap R K) * S = 1 := by
    rw [hSdef, ← Matrix.mul_assoc, ← Matrix.map_mul, ← hDdef, hDD]
  have hsplit : splitMatrix e (A.map (algebraMap R K)) S =
      (P.map (algebraMap R K)) * Matrix.fromBlocks 1 0 0 D⁻¹ := by
    rw [hPdef, ← splitMatrix_map, splitMatrix, splitMatrix, Matrix.fromCols_mul_fromBlocks, hSdef]
    have : (C.map (algebraMap R K) * D⁻¹).submatrix e id =
        (C.map (algebraMap R K)).submatrix e id * D⁻¹ := by
      have a1 := Matrix.submatrix_mul_equiv (C.map (algebraMap R K)) D⁻¹ e (Equiv.refl _) id
      simpa using a1.symm
    rw [this]
    simp
  have hdet : (splitMatrix e (A.map (algebraMap R K)) S).det =
      algebraMap R K P.det * (algebraMap R K (B * C).det)⁻¹ := by
    rw [hsplit, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, hdD',
      ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simp
  have hne : (splitMatrix e (A.map (algebraMap R K)) S).det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (hunit.map _).ne_zero (inv_ne_zero hD)
  refine ⟨⟨_, hSK, hne⟩, hunit.unit⁻¹, ?_⟩
  rw [complexDet, cayleyDet_eq_inv_det (map_mul_eq_zero hBA) hSK hne, hdet, mul_inv, inv_inv]
  congr 1
  rw [map_units_inv, hunit.unit_spec]

omit [DecidableEq ι₁] in
/-- **Exact complexes.** If the complex of free `R`-modules `R^ι₂ → R^ι₁ → R^ι₀` is exact
(surjective on the right and exact in the middle; injectivity on the left is then automatic by
the rank count `e`), then its base change to `K` is split exact and its determinant is the image
of a unit of `R`; this holds for any field `K` over `R`. -/
theorem exists_unit_complexDet_of_exact (e : ι₂ ⊕ ι₀ ≃ ι₁) {A : Matrix ι₁ ι₂ R}
    {B : Matrix ι₀ ι₁ R} (hBA : B * A = 0) (hB : Function.Surjective B.mulVec)
    (hex : ∀ v, B.mulVec v = 0 → ∃ w, A.mulVec w = v) :
    IsSplitExact e (A.map (algebraMap R K)) (B.map (algebraMap R K)) ∧
      ∃ u : Rˣ, complexDet K e A B = algebraMap R K u := by
  choose c hc using fun j : ι₀ => hB (Pi.single j 1)
  let S : Matrix ι₁ ι₀ R := Matrix.of fun i j => c j i
  have hS : B * S = 1 := by
    ext i j
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, S, Matrix.one_apply,
      Pi.single_apply, eq_comm] using congrFun (hc j) i
  obtain ⟨h, u, hu⟩ := exists_unit_complexDet_eq_det_mul (K := K) (e := e) hBA S
    (surjective_splitMatrix_mulVec hex S fun v => ⟨B.mulVec v, by rw [hS, Matrix.one_mulVec]⟩)
    (by rw [hS, Matrix.det_one, map_one]; exact one_ne_zero)
  exact ⟨h, u, by rw [hu, hS, Matrix.det_one, map_one, mul_one]⟩

omit [DecidableEq ι₁] in
/-- **Compatibility with base change.** A ring homomorphism `f : R → R'` and a field homomorphism
`φ : K → K'` over it carry the determinant of a complex generically exact over `K` to the
determinant of the image complex (which is then again exact). -/
theorem complexDet_map {R' K' : Type*} [CommRing R'] [Field K'] [Algebra R' K'] (f : R →+* R')
    (φ : K →+* K') (hφ : φ.comp (algebraMap R K) = (algebraMap R' K').comp f)
    {e : ι₂ ⊕ ι₀ ≃ ι₁} {A : Matrix ι₁ ι₂ R} {B : Matrix ι₀ ι₁ R} (hBA : B * A = 0)
    (h : IsSplitExact e (A.map (algebraMap R K)) (B.map (algebraMap R K))) :
    IsSplitExact e ((A.map f).map (algebraMap R' K')) ((B.map f).map (algebraMap R' K')) ∧
      complexDet K' e (A.map f) (B.map f) = φ (complexDet K e A B) := by
  refine ⟨?_, ?_⟩
  · rw [map_map_algebraMap f φ hφ A, map_map_algebraMap f φ hφ B]
    exact isSplitExact_map φ h
  · rw [complexDet, complexDet, map_map_algebraMap f φ hφ A, map_map_algebraMap f φ hφ B]
    exact map_cayleyDet φ (map_mul_eq_zero hBA) h

omit [DecidableEq ι₁] in
/-- If `K` is the fraction field of `R` and `algebraMap R' K' ∘ f` is injective, some field
homomorphism `φ : K →+* K'` carries the determinant of a complex split exact over `K` to that of
its image under `f`, and the image complex is again split exact over `K'`. -/
theorem complexDet_map_of_injective {R' K' : Type*} [CommRing R'] [Field K'] [Algebra R' K']
    [IsDomain R] [IsFractionRing R K] (f : R →+* R')
    (hf : Function.Injective ((algebraMap R' K').comp f))
    {e : ι₂ ⊕ ι₀ ≃ ι₁} {A : Matrix ι₁ ι₂ R} {B : Matrix ι₀ ι₁ R} (hBA : B * A = 0)
    (h : IsSplitExact e (A.map (algebraMap R K)) (B.map (algebraMap R K))) :
    IsSplitExact e ((A.map f).map (algebraMap R' K')) ((B.map f).map (algebraMap R' K')) ∧
      ∃ φ : K →+* K', complexDet K' e (A.map f) (B.map f) = φ (complexDet K e A B) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : K →+* K', φ.comp (algebraMap R K) = (algebraMap R' K').comp f :=
    ⟨IsFractionRing.lift hf, by ext x; simp⟩
  obtain ⟨h1, h2⟩ := complexDet_map f φ hφ hBA h
  exact ⟨h1, φ, h2⟩

end Ring

/-- If membership in a submodule `N` of `Rⁱ` is divisibility of the coordinates in a basis `b`
by a family `a`, then `Rⁱ/N` has the length of `∏ j, R/(a j)`. -/
theorem length_quotient_eq_length_pi {R ι : Type*} [CommRing R] [Fintype ι]
    {N : Submodule R (ι → R)} (b : Module.Basis ι R (ι → R)) (a : ι → R)
    (hmem : ∀ x, x ∈ N ↔ ∀ j, a j ∣ b.repr x j) :
    Module.length R ((ι → R) ⧸ N) = Module.length R (∀ j, R ⧸ Ideal.span {a j}) := by
  let T : (ι → R) →ₗ[R] (∀ j, R ⧸ Ideal.span {a j}) :=
    LinearMap.pi fun j => (Submodule.mkQ (Ideal.span {a j})).comp (b.coord j)
  have hTsurj : Function.Surjective T := by
    intro q
    choose r hr using fun j => Submodule.Quotient.mk_surjective _ (q j)
    refine ⟨b.equivFun.symm r, ?_⟩
    ext j
    have h := congrFun (b.equivFun.apply_symm_apply r) j
    simp only [Module.Basis.equivFun_apply] at h
    simp only [T, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
      Module.Basis.coord_apply, h, hr j]
  have hTker : LinearMap.ker T = N := by
    ext x
    rw [LinearMap.mem_ker, hmem]
    constructor
    · intro h j
      simpa [T, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using congrFun h j
    · intro h
      ext j
      simpa [T, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using h j
  exact ((Submodule.quotEquivOfEq _ _ hTker.symm).trans
    (T.quotKerEquivOfSurjective hTsurj)).length_eq

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Over a discrete valuation ring, a Smith normal form of a submodule of `Rⁱ` of finite colength
uses every vector of the ambient basis. -/
theorem surjective_smithNormalForm_f {N : Submodule R (ι → R)} {n : ℕ}
    (snf : Module.Basis.SmithNormalForm N ι n) (hfin : Module.length R ((ι → R) ⧸ N) ≠ ⊤) :
    Function.Surjective snf.f := by
  by_contra hns
  simp only [Function.Surjective, not_forall, not_exists] at hns
  obtain ⟨i, hi⟩ := hns
  have hi' : i ∉ Set.range snf.f := by simpa using hi
  let π : ((ι → R) ⧸ N) →ₗ[R] R :=
    N.liftQ (snf.bM.coord i) (snf.le_ker_coord_of_notMem_range hi')
  have hπ : Function.Surjective π := fun r =>
    ⟨Submodule.Quotient.mk (r • snf.bM i), by simp [π]⟩
  have hR : Module.length R R ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (Module.length_le_of_surjective π hπ)
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hR
  have : IsArtinianRing R := hR.2
  exact IsDiscreteValuationRing.not_isField R (IsArtinianRing.isField_of_isDomain R)

/-- Over a discrete valuation ring, a submodule `N` of `Rⁱ` of finite colength has a basis `b` of
`Rⁱ` and nonzero `a : ι → R` with `a j • b j ∈ N`, such that `x ∈ N` iff each coordinate
`b.repr x j` is divisible by `a j`. -/
theorem exists_basis_mem_iff_forall_dvd (N : Submodule R (ι → R))
    (hfin : Module.length R ((ι → R) ⧸ N) ≠ ⊤) :
    ∃ (b : Module.Basis ι R (ι → R)) (a : ι → R), (∀ j, a j ≠ 0) ∧ (∀ j, a j • b j ∈ N) ∧
      ∀ x, x ∈ N ↔ ∀ j, a j ∣ b.repr x j := by
  obtain ⟨n, snf⟩ := Submodule.smithNormalForm (Pi.basisFun R ι) N
  set g : Fin n ≃ ι :=
    Equiv.ofBijective snf.f ⟨snf.f.injective, surjective_smithNormalForm_f snf hfin⟩
  have hfg : ∀ j, snf.f (g.symm j) = j := g.apply_symm_apply
  set a' : ι → R := fun j => snf.a (g.symm j)
  have hbN : ∀ j, ((snf.bN (g.symm j) : N) : ι → R) = a' j • snf.bM j := fun j => by
    rw [snf.snf, hfg]
  refine ⟨snf.bM, a', fun j h => ?_, fun j => ?_, fun x => ⟨fun hx j => ?_, fun hx => ?_⟩⟩
  · apply snf.bN.ne_zero (g.symm j)
    apply Subtype.ext
    rw [hbN, h, zero_smul]
    rfl
  · rw [← hbN]
    exact (snf.bN (g.symm j)).2
  · have := congrFun (snf.repr_comp_embedding_eq_smul ⟨x, hx⟩) (g.symm j)
    simp only [Function.comp_apply, smul_eq_mul, hfg] at this
    exact ⟨_, this⟩
  · choose c hc using hx
    have : x = ∑ j, c j • ((snf.bN (g.symm j) : N) : ι → R) := by
      simp_rw [hbN, smul_smul, mul_comm (c _) (a' _)]
      conv_lhs => rw [← snf.bM.sum_repr x]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc j]
    rw [this]
    exact N.sum_mem fun j _ => N.smul_mem _ (snf.bN (g.symm j)).2

omit [DecidableEq ι] in
/-- Over a discrete valuation ring with uniformizer `ϖ`, if `a j = u j * ϖ ^ k j` with `u j` units,
then `∏ j, R/(a j)` has length `∑ j, k j`. -/
theorem length_pi_quotient_span_singleton {ϖ : R} (hϖ : Irreducible ϖ) {a : ι → R} {k : ι → ℕ}
    {u : ι → Rˣ} (hk : ∀ j, a j = u j * ϖ ^ k j) :
    Module.length R (∀ j, R ⧸ Ideal.span {a j}) = ((∑ j, k j : ℕ) : ℕ∞) := by
  rw [Module.length_pi_of_fintype, Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : Ideal.span {a j} = IsLocalRing.maximalIdeal R ^ k j := by
    rw [hk j, Ideal.span_singleton_mul_left_unit (Units.isUnit _), ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq]
  rw [(Submodule.quotEquivOfEq _ _ h1).length_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal R (k j)

/-- Over a discrete valuation ring, a submodule `N` of `Rⁱ` of finite colength is the image of a
square matrix `D` whose determinant is a unit times `ϖ ^ (length of Rⁱ/N)`. -/
theorem exists_matrix_range_eq_det_eq_unit_mul_pow {ϖ : R} (hϖ : Irreducible ϖ)
    (N : Submodule R (ι → R)) (hfin : Module.length R ((ι → R) ⧸ N) ≠ ⊤) :
    ∃ (D : Matrix ι ι R) (u : Rˣ), LinearMap.range D.mulVecLin = N ∧
      D.det = u * ϖ ^ (Module.length R ((ι → R) ⧸ N)).toNat := by
  obtain ⟨b, a, ha, hsmul, hmem⟩ := exists_basis_mem_iff_forall_dvd N hfin
  choose k uu hk using fun j => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (ha j) hϖ
  have hlen : Module.length R ((ι → R) ⧸ N) = ((∑ j, k j : ℕ) : ℕ∞) := by
    rw [length_quotient_eq_length_pi b a hmem, length_pi_quotient_span_singleton hϖ hk]
  set Pm : Matrix ι ι R := (Matrix.of fun j i => b j i)ᵀ with hPm
  have hPmunit : IsUnit Pm.det := by
    have := (Pi.basisFun R ι).isUnit_det b
    rwa [Pi.basisFun_det_apply, ← Matrix.det_transpose] at this
  set D : Matrix ι ι R := Pm * Matrix.diagonal a with hD
  have hcol : ∀ j, D.col j = a j • b j := by
    intro j
    ext i
    simp [hD, hPm, Matrix.mul_diagonal, Matrix.col, mul_comm]
  refine ⟨D, hPmunit.unit * ∏ j, uu j, ?_, ?_⟩
  · rw [Matrix.range_mulVecLin]
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      rw [hcol]
      exact hsmul j
    · intro x hx
      choose c hc using (hmem x).1 hx
      have : x = ∑ j, c j • (a j • b j) := by
        conv_lhs => rw [← b.sum_repr x]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hc j, smul_smul, mul_comm]
      rw [this]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range.2 ⟨j, hcol j⟩))
  · rw [hD, Matrix.det_mul, Matrix.det_diagonal, hlen, ENat.toNat_natCast]
    simp_rw [hk]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Units.val_mul, Units.coe_prod]
    simp only [IsUnit.unit_spec]
    ring

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]
  [DecidableEq ι₂] [DecidableEq ι₁] [DecidableEq ι₀]

omit [DecidableEq ι₁] in
/-- **Order of the determinant over a discrete valuation ring.**  Let `R` be a discrete valuation
ring with uniformizer `ϖ` and `F₂ → F₁ → F₀` a complex of finite free `R`-modules with zero
alternating rank (`e`), exact at `F₁` and with `H₀ = F₀ / im B` of finite length.  (Exactness at
`F₂` is then automatic.)  Then the complex is exact over the fraction field and its determinant is
a unit times `ϖ ^ ℓ`, where `ℓ` is the length of `H₀`: its valuation is the length of `H₀`. -/
theorem exists_unit_complexDet_eq_pow_length {ϖ : R} (hϖ : Irreducible ϖ) (e : ι₂ ⊕ ι₀ ≃ ι₁)
    {A : Matrix ι₁ ι₂ R} {B : Matrix ι₀ ι₁ R} (hBA : B * A = 0)
    (hex : ∀ v, B.mulVec v = 0 → ∃ w, A.mulVec w = v)
    (hfin : Module.length R ((ι₀ → R) ⧸ LinearMap.range B.mulVecLin) ≠ ⊤) :
    IsSplitExact e (A.map (algebraMap R K)) (B.map (algebraMap R K)) ∧
      ∃ u : Rˣ, complexDet K e A B = algebraMap R K u * algebraMap R K ϖ ^
        (Module.length R ((ι₀ → R) ⧸ LinearMap.range B.mulVecLin)).toNat := by
  obtain ⟨D, u, hDr, hDdet⟩ := exists_matrix_range_eq_det_eq_unit_mul_pow hϖ
    (LinearMap.range B.mulVecLin) hfin
  have hmem : ∀ j, D.mulVec (Pi.single j 1) ∈ LinearMap.range B.mulVecLin := fun j => by
    rw [← hDr]
    exact ⟨Pi.single j 1, rfl⟩
  choose c hc using fun j => LinearMap.mem_range.1 (hmem j)
  set C : Matrix ι₁ ι₀ R := Matrix.of fun i j => c j i with hCdef
  have hBC : B * C = D := by
    ext i j
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, hCdef, Pi.single_apply] using
      congrFun (hc j) i
  have hsurj := surjective_splitMatrix_mulVec (e := e) hex C fun v => by
    have : B.mulVec v ∈ LinearMap.range D.mulVecLin := by
      rw [hDr]
      exact ⟨v, rfl⟩
    obtain ⟨z, hz⟩ := LinearMap.mem_range.1 this
    exact ⟨z, by rw [hBC]; exact hz.symm⟩
  have hne : algebraMap R K (B * C).det ≠ 0 := by
    rw [hBC, hDdet]
    refine (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (mul_ne_zero (Units.ne_zero u) ?_)
    exact pow_ne_zero _ hϖ.ne_zero
  obtain ⟨h1, v, hv⟩ := exists_unit_complexDet_eq_det_mul (K := K) hBA C hsurj hne
  refine ⟨h1, v * u, ?_⟩
  rw [hv, hBC, hDdet]
  simp [map_mul, mul_assoc]

end DVR

section Normal

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- The localization of a Noetherian normal domain at a height-one prime is a discrete valuation
ring. -/
theorem isDiscreteValuationRing_localization_atPrime_of_height_eq_one (p : Ideal R) [p.IsPrime]
    (hp : p.height = 1) : IsDiscreteValuationRing (Localization.AtPrime p) := by
  have hdim : ringKrullDim (Localization.AtPrime p) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, hp]
    rfl
  have h5 : IsNoetherianRing (Localization.AtPrime p) ∧ IsLocalRing (Localization.AtPrime p) ∧
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) ∧
      ringKrullDim (Localization.AtPrime p) = 1 :=
    ⟨IsLocalization.isNoetherianRing p.primeCompl _ inferInstance, inferInstance, inferInstance,
      isIntegrallyClosed_of_isLocalization (S := Localization.AtPrime p) p.primeCompl
        p.primeCompl_le_nonZeroDivisors, hdim⟩
  obtain ⟨_, h⟩ := ((isDiscreteValuationRing_tfae (Localization.AtPrime p)).out 5 1).mp h5
  exact h

variable {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]
  [DecidableEq ι₂] [DecidableEq ι₁] [DecidableEq ι₀]

omit [DecidableEq ι₁] in
/-- **Regularity of the determinant over a normal Noetherian domain.**  Let `R` be a Noetherian
normal domain with fraction field `K`, and `F₂ → F₁ → F₀` a complex of finite free `R`-modules of
zero alternating rank.  If at every height-one prime `p` the localized complex is exact at `F₁`
with `H₀` of finite length (for instance exact), then its determinant lies in `R`.  Exactness at
`F₂` is automatic from the rank count, and the case of an exact localization is the case
`H₀ = 0`. -/
theorem exists_algebraMap_complexDet_eq (e : ι₂ ⊕ ι₀ ≃ ι₁) {A : Matrix ι₁ ι₂ R}
    {B : Matrix ι₀ ι₁ R} (hBA : B * A = 0)
    (h : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      (∀ v, (B.map (algebraMap R (Localization.AtPrime p))).mulVec v = 0 →
        ∃ w, (A.map (algebraMap R (Localization.AtPrime p))).mulVec w = v) ∧
      Module.length (Localization.AtPrime p) ((ι₀ → Localization.AtPrime p) ⧸
        LinearMap.range (B.map (algebraMap R (Localization.AtPrime p))).mulVecLin) ≠ ⊤) :
    ∃ r : R, algebraMap R K r = complexDet K e A B := by
  refine Stacks.AlgebraicGeometry.UnitsNormalProper.exists_algebraMap_eq_of_forall_height_eq_one
    K fun q hq => ?_
  set p := q.asIdeal
  have hpp : p.IsPrime := q.isPrime
  obtain ⟨hex, hfin⟩ := h p hq
  have hdvr := isDiscreteValuationRing_localization_atPrime_of_height_eq_one p hq
  let _ : Algebra (Localization.AtPrime p) K :=
    (IsLocalization.lift (M := p.primeCompl) (S := Localization.AtPrime p)
      (g := algebraMap R K) (fun y => by
        have hy0 : (y : R) ≠ 0 := fun h0 => y.2 (h0 ▸ p.zero_mem)
        exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hy0))
      ).toAlgebra
  have : IsScalarTower R (Localization.AtPrime p) K :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq _ x).symm
  have : IsFractionRing (Localization.AtPrime p) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl _ K
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
  have hBA' := map_mul_eq_zero (K := Localization.AtPrime p) hBA
  obtain ⟨-, u, hu⟩ := exists_unit_complexDet_eq_pow_length (K := K) (e := e) hϖ hBA' hex hfin
  have hcd : complexDet K e (A.map (algebraMap R (Localization.AtPrime p)))
      (B.map (algebraMap R (Localization.AtPrime p))) = complexDet K e A B := by
    simp only [complexDet, Matrix.map_map, ← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
  rw [hcd] at hu
  set x : Localization.AtPrime p := u * ϖ ^
    (Module.length (Localization.AtPrime p) ((ι₀ → Localization.AtPrime p) ⧸
      LinearMap.range (B.map (algebraMap R (Localization.AtPrime p))).mulVecLin)).toNat with hx
  have hz : complexDet K e A B = algebraMap (Localization.AtPrime p) K x := by
    rw [hu, hx]
    simp
  obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.surj p.primeCompl x
  refine ⟨a, t, t.2, ?_⟩
  have := congrArg (algebraMap (Localization.AtPrime p) K) hat
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
  rw [hz]
  exact this

end Normal

end MMP.Chow
