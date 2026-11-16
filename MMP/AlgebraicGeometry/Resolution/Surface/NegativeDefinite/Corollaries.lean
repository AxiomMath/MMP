/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChartCompactification
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.DominatingBlowup

/-!
# Consequences of the negative definiteness of exceptional curves

Kollár's Theorem 2.12: for a projective generically finite morphism `f : X ⟶ Y` from a smooth
surface to a quasi-projective variety, the intersection matrix `((Cᵢ · Cⱼ))` of distinct
`f`-exceptional curves is negative definite
(`MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isContractedProjectiveCurve`). This
file draws three consequences.

* The quadratic form `(∑ xᵢ Cᵢ · ∑ xᵢ Cᵢ) = ∑ᵢⱼ xᵢ xⱼ (Cᵢ · Cⱼ)` is negative at every nonzero
  `x`, in particular at every nonzero `x ∈ ℝ^m_{≥ 0}` (the cube argument of Kollár's proof).
* For a proper birational morphism `f : Y ⟶ X` from a smooth surface to an affine variety, the
  intersection matrix of distinct curves contracted to points is negative definite, and each such
  curve has negative self-intersection: over an affine base `f` is projective ([Stacks, Tag
  0C5P]), the base is H-quasi-projective, a birational proper morphism is finite over a
  neighbourhood of the generic point ([Stacks, Tag 02UP]), and proper curves over a field are
  projective ([Stacks, Tag 0A26]), so Kollár 2.12 applies.
* For a resolution `g` of a surface germ with boundary `(X, P; B)` there is exactly one log
  discrepancy vector (FA 3.1.0): the defining conditions are the linear system
  `((K_Y + g⁻¹_* B) · E_j) + ∑ᵢ (1 - aᵢ)(E_i · E_j) = 0`, whose matrix `((E_i · E_j))` is
  negative definite, hence nonsingular; the solution is rational since the system is over `ℚ`.

## Main results

* `MMP.Threefold.Resolution.sum_mul_intersectionNumber_mul_neg_of_isContractedProjectiveCurve`:
  `(∑ xᵢ Cᵢ)² < 0` for `x ≠ 0` (Kollár 2.12, proof).
* `MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isAffine`: Kollár 2.12 for a proper
  generically finite morphism from a smooth surface to an affine variety.
* `MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isBirationalMorphism_of_isAffine`,
  `MMP.Threefold.Resolution.intersectionNumber_self_neg_of_isBirationalMorphism_of_isAffine`:
  negative definiteness and negative self-intersection of the curves contracted by a proper
  birational morphism from a smooth surface to an affine variety.
* `MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_forall_fibre`: curves over
  distinct points are disjoint
  (`MMP.Threefold.Resolution.intersectionNumber_single_eq_zero_of_disjoint`), so the
  intersection matrix is block diagonal along the fibres and negative definite when each fibre
  block is (`MMP.MatrixPosDef.posDef_of_eq_zero_of_ne_of_posDef_submatrix`).
* `MMP.Flips.existsUnique_isGermLogDiscrepancyVector_of_posDef`: uniqueness and existence of the
  log discrepancy vector when the intersection matrix of the exceptional curves is negative
  definite and `Y` has a canonical divisor.
* `MMP.Flips.existsUnique_isGermLogDiscrepancyVector_of_isAffine`: the same over an affine germ.
* `MMP.Mori.QDivisor.intersectionNumber_smul`: `((q D) · C) = q (D · C)` for `q ∈ ℚ`.

## Implementation notes

* The matrix `((Cᵢ · Cⱼ))` is encoded as in Kollár 2.12: each curve is a prime divisor `Pᵢ` and a
  proper curve `Cᵢ` with the same generic point, `(Cᵢ · Cⱼ)` being the intersection number of
  `Pᵢ` with `Cⱼ`. "Negative definite" is `Matrix.PosDef` of the negated real matrix.
* The negativity of the quadratic form is stated for every nonzero real `x`; the source states it
  for `x ∈ ℝ^m_{≥ 0} ∖ {0}`, a special case.
* The source states negative definiteness over an arbitrary normal surface `X`, via an affine
  neighbourhood of each image point. The reduction to one fibre is
  `MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_forall_fibre`; the statements for a
  single fibre assume `X` affine, since the comparison of intersection numbers on `Y` with those
  on the preimage of an affine open, which the passage to an affine neighbourhood needs, is not
  available. Normality of `X`, its dimension, and the algebraic closedness of `k`
  are not used.
* The log discrepancy condition is asked of every canonical divisor of `Y`
  (`MMP.Flips.IsGermLogDiscrepancyVector`), so it holds vacuously when `Y` has none; uniqueness
  therefore assumes that `Y` has a canonical divisor `K_Y`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 2.12]
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.1.0)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Threefold.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

section Degree

variable (k : Type u) [Field k] {X C : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (i : C ⟶ X)
  [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

namespace Divisor

/-- `deg_C 𝒪_X(-D) = -deg_C 𝒪_X(D)` for a Cartier divisor `D`. -/
theorem degreeOn_neg' (D : Divisor X) (hD : D.IsCartier) :
    (-D).degreeOn k sX i hdim hD.neg = -D.degreeOn k sX i hdim hD := by
  have h := degreeOn_add k sX i hdim D (-D) hD hD.neg
  rw [degreeOn_congr (add_neg_cancel D) _ isCartier_zero, degreeOn_zero'] at h
  omega

/-- `deg_C 𝒪_X(nD) = n · deg_C 𝒪_X(D)` for a Cartier divisor `D` and `n ∈ ℤ`. -/
theorem degreeOn_zsmul' (D : Divisor X) (hD : D.IsCartier) (n : ℤ) :
    (n • D).degreeOn k sX i hdim (hD.zsmul n) = n * D.degreeOn k sX i hdim hD := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [degreeOn_congr (natCast_zsmul D m) _ (hD.nsmul m), degreeOn_nsmul']
  · rw [degreeOn_congr (show (-(m : ℤ)) • D = -(m • D) by rw [neg_smul, natCast_zsmul]) _
      (hD.nsmul m).neg, degreeOn_neg' k sX i hdim _ (hD.nsmul m),
      degreeOn_nsmul' k sX i hdim D hD]
    ring

end Divisor

namespace QDivisor

/-- **Homogeneity of the intersection number.** `((q D) · C) = q (D · C)` for `q ∈ ℚ`. -/
theorem intersectionNumber_smul (q : ℚ) (D : QDivisor X) (hD : D.IsQCartier)
    (hqD : (q • D).IsQCartier) :
    (q • D).intersectionNumber k sX i hdim hqD = q * D.intersectionNumber k sX i hdim hD := by
  have hF := isCartierDivisor_cartierIndex_smul hD
  have hn := cartierIndex_pos hD
  set n := D.cartierIndex hD
  have hb := q.den_pos
  have hE := hF.isCartier_toDivisor.zsmul q.num
  have hq : (q.num : ℚ) = q * q.den := by rw [Rat.mul_den_eq_num]
  rw [intersectionNumber_eq_of_smul k sX i hdim (q • D) hqD (Nat.mul_pos hb hn)
      (q.num • hF.toDivisor) hE ?_,
    Divisor.degreeOn_zsmul' k sX i hdim _ hF.isCartier_toDivisor,
    intersectionNumber_eq_of_toQDivisor_eq k sX i hdim D hD _
      hF.isCartier_toDivisor hF.toQDivisor_toDivisor]
  · have h1 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have h2 : (q.den : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    push_cast
    rw [hq]
    field_simp
    rw [mul_div_assoc, show ((D.cartierIndex hD : ℕ) : ℚ) = n from rfl, div_self h1, mul_one]
  · rw [map_zsmul, hF.toQDivisor_toDivisor, ← Int.cast_smul_eq_zsmul ℚ,
      ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul]
    congr 1
    push_cast
    rw [hq]
    ring

end QDivisor

end Degree

section Curves

variable {k : Type u} [Field k] {Y : Scheme.{u}}

/-- The reduced closed subscheme on the closure of the generic point of a prime divisor `E` is
`E` itself. -/
theorem vanishingIdeal_closure_genericPoint_eq_idealSheaf [IsLocallyNoetherian Y] [IsNormal Y]
    (E : Mori.PrimeDivisor Y) :
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({E.genericPoint} : Set Y)) =
      E.idealSheaf := by
  have := E.integral
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme E.idealSheaf _ rfl]
  congr 1
  exact Closeds.ext (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm

variable {s : Y ⟶ Spec (.of k)} [QuasiCompact s] [IsLocallyNoetherian Y] [IsNormal Y]

/-- The intersection number with a proper curve `C` is the intersection number with the prime
divisor `E` having the same generic point. -/
theorem isIntersectionNumber_of_properCurve (D : QDivisor Y) (hD : D.IsQCartier)
    (C : ProperCurve s) (E : Mori.PrimeDivisor Y) (hC : C.point = E.genericPoint) :
    IsIntersectionNumber s D E.idealSheaf (D.intersectionNumber k s C.ι C.dim_le hD) := by
  rw [← vanishingIdeal_closure_genericPoint_eq_idealSheaf E, ← hC]
  exact ⟨C.isProper_ι_comp, C.dim_le, hD, rfl⟩

/-- Intersection numbers are homogeneous: `(D · C) = x` gives `((q D) · C) = q x`. -/
theorem IsIntersectionNumber.smul {D : QDivisor Y} {C : Y.IdealSheafData} {x : ℚ}
    (h : IsIntersectionNumber s D C x) (q : ℚ) (hq : (q • D).IsQCartier) :
    IsIntersectionNumber s (q • D) C (q * x) := by
  obtain ⟨hp, hdim, hD, rfl⟩ := h
  exact ⟨hp, hdim, hq, QDivisor.intersectionNumber_smul k s _ hdim q D hD hq⟩

/-- Intersection numbers are additive over finite sums. -/
theorem isIntersectionNumber_sum {ι : Type*} (t : Finset ι) {D : ι → QDivisor Y}
    {C : Y.IdealSheafData} {x : ι → ℚ} (h0 : IsIntersectionNumber s 0 C 0)
    (h : ∀ j ∈ t, IsIntersectionNumber s (D j) C (x j)) :
    IsIntersectionNumber s (∑ j ∈ t, D j) C (∑ j ∈ t, x j) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using h0
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact MMP.Flips.isIntersectionNumber_add (h a (Finset.mem_insert_self a t))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Curves

end MMP.Mori

namespace MMP.MatrixPosDef

open Matrix

open Finset in
/-- If `-A` is positive definite, the quadratic form `∑ᵢⱼ xᵢ xⱼ Aᵢⱼ` of `A` is negative at every
nonzero real vector `x`. -/
theorem sum_mul_mul_neg_of_posDef_neg {n : Type*} [Fintype n] {A : Matrix n n ℝ}
    (hA : (-A).PosDef) {x : n → ℝ} (hx : x ≠ 0) : ∑ i, ∑ j, x i * x j * A i j < 0 := by
  have h := hA.dotProduct_mulVec_pos hx
  have e : star x ⬝ᵥ ((-A) *ᵥ x) = -∑ i, ∑ j, x i * x j * A i j := by
    simp only [dotProduct, mulVec, Matrix.neg_apply, star_trivial, mul_sum, ← sum_neg_distrib]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  linarith

/-- If `M` is a rational matrix whose image in `ℝ` is negative definite, then `det M ≠ 0`. -/
theorem det_ne_zero_of_posDef_neg_map {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℚ) (hM : (-(M.map ((↑) : ℚ → ℝ))).PosDef) : M.det ≠ 0 := by
  intro h0
  have hdet := hM.det_pos
  rw [Matrix.det_neg] at hdet
  have : (M.map ((↑) : ℚ → ℝ)).det = ((M.det : ℚ) : ℝ) :=
    ((Rat.castHom ℝ).map_det M).symm
  rw [this, h0, Rat.cast_zero, mul_zero] at hdet
  exact lt_irrefl _ hdet

/-- **Unique solvability of a nonsingular linear system** over a field: for `M` with
`det M ≠ 0` and every `β`, there is exactly one `c` with `β j + ∑ᵢ cᵢ Mᵢⱼ = 0` for all `j`. -/
theorem existsUnique_add_sum_mul_eq_zero {K n : Type*} [Field K] [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (hM : M.det ≠ 0) (β : n → K) :
    ∃! c : n → K, ∀ j, β j + ∑ i, c i * M i j = 0 := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have key : ∀ c : n → K, (∀ j, β j + ∑ i, c i * M i j = 0) ↔ Matrix.vecMul c M = -β := by
    intro c
    refine ⟨fun h => funext fun j => ?_, fun h j => ?_⟩
    · have := h j
      simp only [Matrix.vecMul, dotProduct, Pi.neg_apply]
      linear_combination this
    · have := congrFun h j
      simp only [Matrix.vecMul, dotProduct, Pi.neg_apply] at this
      linear_combination this
  refine ⟨Matrix.vecMul (-β) M⁻¹, (key _).2 ?_, fun c hc => ?_⟩
  · rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul M hu, Matrix.vecMul_one]
  · rw [← (key c).1 hc, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv M hu, Matrix.vecMul_one]

open Finset in
/-- **A block-diagonal matrix with positive definite blocks is positive definite.** If `A` is a
real matrix with `Aᵢⱼ = 0` whenever `φ i ≠ φ j`, and every block `A|_{φ⁻¹(y)}` is positive
definite, then `A` is positive definite. -/
theorem posDef_of_eq_zero_of_ne_of_posDef_submatrix {n ι : Type*} [Fintype n] [DecidableEq n]
    [DecidableEq ι] (φ : n → ι) (A : Matrix n n ℝ) (hA0 : ∀ i j, φ i ≠ φ j → A i j = 0)
    (hblock : ∀ y, (A.submatrix (Subtype.val : {i // φ i = y} → n) Subtype.val).PosDef) :
    A.PosDef := by
  have hsymm : ∀ i j, A i j = A j i := by
    intro i j
    by_cases h : φ i = φ j
    · have := (hblock (φ j)).isHermitian.apply ⟨i, h⟩ ⟨j, rfl⟩
      simpa [submatrix_apply] using this.symm
    · rw [hA0 i j h, hA0 j i (Ne.symm h)]
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext i j
    simp [conjTranspose_apply, hsymm j i]
  have e : star x ⬝ᵥ (A *ᵥ x) = ∑ y ∈ univ.image φ, ∑ i : {i // φ i = y}, ∑ j : {i // φ i = y},
      x i * A i j * x j := by
    simp only [dotProduct, mulVec, star_trivial, mul_sum]
    rw [← sum_fiberwise_of_maps_to (g := φ) (t := univ.image φ)
      (fun i _ => mem_image_of_mem φ (mem_univ i))]
    refine sum_congr rfl fun y _ => ?_
    refine (sum_subtype (univ.filter fun i => φ i = y) (p := fun i => φ i = y) (by simp) _).trans
      (sum_congr rfl fun i _ => ?_)
    have hiy : φ i.1 = y := i.2
    rw [← sum_filter_add_sum_filter_not univ (fun j => φ j = y)]
    have : ∑ j ∈ univ.filter (fun j => ¬ φ j = y), x i * (A i j * x j) = 0 :=
      sum_eq_zero fun j hj => by
        rw [hA0 i j (by rw [hiy]; exact fun h => (mem_filter.1 hj).2 h.symm)]; ring
    rw [this, add_zero]
    refine (sum_subtype (univ.filter fun j => φ j = y) (p := fun j => φ j = y) (by simp) _).trans
      (sum_congr rfl fun j _ => by ring)
  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  rw [e]
  refine sum_pos' (fun y _ => ?_) ⟨φ i0, mem_image_of_mem φ (mem_univ _), ?_⟩
  · have := (hblock y).posSemidef.dotProduct_mulVec_nonneg (fun i => x i)
    simpa [dotProduct, mulVec, mul_sum, mul_assoc] using this
  · have hne : (fun i : {i // φ i = φ i0} => x i) ≠ 0 := fun h => hi0 (congrFun h ⟨i0, rfl⟩)
    have := (hblock (φ i0)).dotProduct_mulVec_pos hne
    simpa [dotProduct, mulVec, mul_sum, mul_assoc] using this

end MMP.MatrixPosDef

namespace MMP.Threefold.Resolution

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)}

/-- A scheme smooth over a field is regular. -/
theorem isRegular_of_isSmoothScheme (hsm : IsSmoothScheme sY) : IsRegular Y :=
  MMP.Resolution.Bridges.isRegular_of_isSmoothScheme sY hsm

/-- **Curves in disjoint position meet with intersection number zero.** On a smooth `X`, if the
prime divisor `P` does not meet the proper curve `C`, then `(P · C) = 0`. -/
theorem intersectionNumber_single_eq_zero_of_disjoint [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] (hsm : IsSmoothScheme sX) (P : Mori.PrimeDivisor X) (C : ProperCurve sX)
    (h : Disjoint (P.support : Set X) (closure ({C.point} : Set X))) :
    (Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k sX C.ι C.dim_le
      (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm P) = 0 := by
  rw [QDivisor.intersectionNumber_toQDivisor k sX _ _ _ (isCartier_of_isSmoothScheme hsm _)]
  have hnot : ∀ c : C.scheme,
      C.ι c ∉ DivisorWithCoeffs.supp (Finsupp.single P (1 : ℤ) : Divisor X) := by
    intro c hc
    obtain ⟨E, hE, hcE⟩ := DivisorWithCoeffs.mem_supp_iff.1 hc
    have hEP : E = P := by
      by_contra hne
      exact hE (by simp [DivisorWithCoeffs.coeff_apply, Ne.symm hne])
    subst hEP
    have hcC : C.ι c ∈ closure ({C.point} : Set X) := by
      have : C.ι c ∈ Set.range C.ι := ⟨c, rfl⟩
      unfold ProperCurve.ι curveSubschemeAtι at this
      rwa [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
    exact Set.disjoint_left.1 h hcE hcC
  obtain ⟨c, -⟩ := exists_ι_eq_point C.point
  have := degreeOn_nonneg_and_eq_zero_iff sX C.ι C.dim_le _ (isCartier_of_isSmoothScheme hsm _)
    (Finsupp.single_nonneg.2 zero_le_one) ⟨c, hnot c⟩
  exact_mod_cast this.2.2 hnot

/-- **Reduction to one fibre.** Let `f : X ⟶ Y` be a morphism from a smooth `X` and `C₁, …, Cₘ`
curves contracted by `f` (prime divisors `Pᵢ` with proper curves `Cᵢ` of the same generic
points). Curves over distinct points of `Y` are disjoint, so the intersection matrix is block
diagonal along the fibres of `f`, and it is negative definite as soon as each block, formed by
the curves over one point of `Y`, is. -/
theorem posDef_neg_intersectionMatrix_of_forall_fibre [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] (hsm : IsSmoothScheme sX) {f : X ⟶ Y} {m : ℕ}
    (P : Fin m → Mori.PrimeDivisor X) (C : Fin m → ProperCurve sX)
    (hC : ∀ i, (C i).point = (P i).genericPoint) (hexc : ∀ i, (C i).IsContractedBy f)
    (hfib : ∀ y : Y, (-((Matrix.of fun i j : Fin m =>
      ((Divisor.toQDivisor (Finsupp.single (P i) 1)).intersectionNumber k sX (C j).ι
        (C j).dim_le (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm (P i)) :
          ℝ)).submatrix (Subtype.val : {i // f (C i).point = y} → Fin m) Subtype.val)).PosDef) :
    (-(Matrix.of fun i j : Fin m =>
      ((Divisor.toQDivisor (Finsupp.single (P i) 1)).intersectionNumber k sX (C j).ι
        (C j).dim_le (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm (P i)) :
          ℝ))).PosDef := by
  classical
  refine MMP.MatrixPosDef.posDef_of_eq_zero_of_ne_of_posDef_submatrix (fun i => f (C i).point) _
    (fun i j hij => ?_) fun y => by rw [Matrix.submatrix_neg]; exact hfib y
  have hdisj : Disjoint ((P i).support : Set X) (closure ({(C j).point} : Set X)) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      show AlgebraicGeometry.PrimeDivisor.genericPoint (P i) = (C i).point from (hC i).symm]
    refine Set.disjoint_left.2 fun x hxi hxj => hij ?_
    exact (show f x = f (C i).point from hexc i x hxi).symm.trans (hexc j x hxj)
  simp only [Matrix.neg_apply, Matrix.of_apply,
    intersectionNumber_single_eq_zero_of_disjoint hsm (P i) (C j) hdisj, Rat.cast_zero, neg_zero]

/-- **Kollár 2.12, the cube argument.** Under the hypotheses of Kollár 2.12, for every nonzero
`x ∈ ℝ^m` (in particular every nonzero `x ∈ ℝ^m_{≥ 0}`, as in the source),
`(∑ᵢ xᵢ Cᵢ · ∑ᵢ xᵢ Cᵢ) = ∑ᵢⱼ xᵢ xⱼ (Cᵢ · Cⱼ) < 0`. -/
@[mmp "lem_kr2a_negative_on_effective_exceptional_combinations"]
theorem sum_mul_intersectionNumber_mul_neg_of_isContractedProjectiveCurve
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] (hX : Mori.IsVariety k sX)
    (hsm : IsSmoothScheme sX) (hdim : topologicalKrullDim X = 2)
    (hY : Mori.IsVariety k sY) (hYqp : Stacks.HProjective.IsHQuasiProjective sY)
    {f : X ⟶ Y} (hfs : f ≫ sY = sX) (hproj : IsProjectiveMorphism f)
    (hgf : ∃ V : Y.Opens, ((V : Set Y) ∩ Set.range f.base).Nonempty ∧ IsFinite (f ∣_ V))
    {m : ℕ} (P : Fin m → Mori.PrimeDivisor X) (hP : Function.Injective P)
    (C : Fin m → ProperCurve sX) (hC : ∀ i, (C i).point = (P i).genericPoint)
    (hexc : ∀ i, MMP.Resolution.IsContractedProjectiveCurve sX f (C i))
    (x : Fin m → ℝ) (hx : x ≠ 0) :
    ∑ i, ∑ j, x i * x j *
      ((Divisor.toQDivisor (Finsupp.single (P i) 1)).intersectionNumber k sX (C j).ι
        (C j).dim_le (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm (P i)) : ℝ) <
      0 :=
  MMP.MatrixPosDef.sum_mul_mul_neg_of_posDef_neg
    (posDef_neg_intersectionMatrix_of_isContractedProjectiveCurve hX hsm hdim hY hYqp hfs hproj
      hgf P hP C hC hexc) hx

open Stacks.HQuasiProjectiveDimensionOne in
/-- **Kollár 2.12 over an affine base.** Let `f : Y ⟶ X` be a proper generically finite
morphism from a smooth surface `Y` to an affine variety `X`, and `C₁, …, Cₘ` distinct curves
contracted by `f`. Then `((Cᵢ · Cⱼ))` is negative definite: `f` is
projective ([Stacks, Tag 0C5P]), `X` is H-quasi-projective, and the `Cᵢ` are projective over `k`
([Stacks, Tag 0A26]). -/
theorem posDef_neg_intersectionMatrix_of_isAffine [QuasiCompact sY] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : Mori.IsVariety k sY) (hsm : IsSmoothScheme sY)
    (hdim : topologicalKrullDim Y = 2)
    (hX : Mori.IsVariety k sX) [IsAffine X] {f : Y ⟶ X} (hfs : f ≫ sX = sY) [IsProper f]
    (hgf : ∃ V : X.Opens, ((V : Set X) ∩ Set.range f.base).Nonempty ∧ IsFinite (f ∣_ V))
    {m : ℕ} (P : Fin m → Mori.PrimeDivisor Y) (hP : Function.Injective P)
    (C : Fin m → ProperCurve sY) (hC : ∀ i, (C i).point = (P i).genericPoint)
    (hexc : ∀ i, (C i).IsContractedBy f) :
    (-(Matrix.of fun i j : Fin m =>
      ((Divisor.toQDivisor (Finsupp.single (P i) 1)).intersectionNumber k sY (C j).ι
        (C j).dim_le (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm (P i)) :
          ℝ))).PosDef := by
  have : IsNoetherian X := isNoetherian_of_finiteType sX
  have hproj : IsProjectiveMorphism f :=
    isProjectiveMorphism_of_isProjective_of_isAffine f
      (isProjective_of_isRegular_of_topologicalKrullDim_le_two f
        (isRegular_of_isSmoothScheme hsm) hdim.le)
  have hXqp : Stacks.HProjective.IsHQuasiProjective sX := isHQuasiProjective_of_isAffine_toSpec sX
  refine posDef_neg_intersectionMatrix_of_isContractedProjectiveCurve hY hsm hdim hX hXqp hfs
    hproj hgf P hP C hC fun i => ⟨?_, hexc i⟩
  exact isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one _ (C i).dim_le

/-- **A proper birational morphism is generically finite.** For a proper birational morphism
`f : Y ⟶ X` of integral schemes, `X` locally noetherian, the fibre over the generic point of `X`
is the generic point of `Y`, so `f` is finite over an open neighbourhood of it
([Stacks, Tag 02UP]). -/
theorem exists_isFinite_morphismRestrict_of_isBirationalMorphism [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] {f : Y ⟶ X} [IsProper f] (hb : MMP.Mori.IsBirationalMorphism f) :
    ∃ V : X.Opens, ((V : Set X) ∩ Set.range f.base).Nonempty ∧ IsFinite (f ∣_ V) := by
  have hbir := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb
  have hpre := preimage_genericPoint f hbir
  obtain ⟨V, hV, hfin⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f
    (genericPoint X) (by simp [hpre])
  refine ⟨V, ⟨genericPoint X, hV, genericPoint Y, ?_⟩, hfin⟩
  exact (show genericPoint Y ∈ f.base ⁻¹' {genericPoint X} by simp [hpre])

/-- **Negative definiteness of the exceptional curves over an affine base.** Let `f : Y ⟶ X`
be a proper birational morphism from a smooth surface `Y` to an affine variety `X` (for instance
an affine normal surface), and `E₁, …, Eₙ` distinct proper curves on `Y` (prime divisors `Pᵢ`
with proper curves `Cᵢ` having the same generic points) whose images are points. Then the
intersection matrix `((Eᵢ · Eⱼ))` is negative definite. -/
theorem posDef_neg_intersectionMatrix_of_isBirationalMorphism_of_isAffine [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : Mori.IsVariety k sY) (hsm : IsSmoothScheme sY) (hdim : topologicalKrullDim Y = 2)
    (hX : Mori.IsVariety k sX) [IsAffine X]
    {f : Y ⟶ X} (hfs : f ≫ sX = sY) [IsProper f] (hb : MMP.Mori.IsBirationalMorphism f)
    {n : ℕ} (P : Fin n → Mori.PrimeDivisor Y) (hP : Function.Injective P)
    (C : Fin n → ProperCurve sY) (hC : ∀ i, (C i).point = (P i).genericPoint)
    (hexc : ∀ i, (C i).IsContractedBy f) :
    (-(Matrix.of fun i j : Fin n =>
      ((Divisor.toQDivisor (Finsupp.single (P i) 1)).intersectionNumber k sY (C j).ι
        (C j).dim_le (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm (P i)) :
          ℝ))).PosDef := by
  have := hX.toIsIntegral
  have := hY.toIsIntegral
  have : IsNoetherian X := isNoetherian_of_finiteType sX
  exact posDef_neg_intersectionMatrix_of_isAffine hY hsm hdim hX hfs
    (exists_isFinite_morphismRestrict_of_isBirationalMorphism hb) P hP C hC hexc

/-- **Each contracted curve has negative self-intersection** (over an affine base):
under the hypotheses of
`MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isBirationalMorphism_of_isAffine`,
`(Eᵢ · Eᵢ) < 0`. -/
theorem intersectionNumber_self_neg_of_isBirationalMorphism_of_isAffine [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : Mori.IsVariety k sY) (hsm : IsSmoothScheme sY) (hdim : topologicalKrullDim Y = 2)
    (hX : Mori.IsVariety k sX) [IsAffine X]
    {f : Y ⟶ X} (hfs : f ≫ sX = sY) [IsProper f] (hb : MMP.Mori.IsBirationalMorphism f)
    (E : Mori.PrimeDivisor Y) (C : ProperCurve sY) (hC : C.point = E.genericPoint)
    (hexc : C.IsContractedBy f) :
    (Divisor.toQDivisor (Finsupp.single E 1)).intersectionNumber k sY C.ι C.dim_le
      (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm E) < 0 := by
  have h := (posDef_neg_intersectionMatrix_of_isBirationalMorphism_of_isAffine hY hsm hdim hX
    hfs hb (fun _ : Fin 1 => E) (fun a b _ => Subsingleton.elim a b) (fun _ => C)
    (fun _ => hC) fun _ => hexc).diag_pos (i := 0)
  simp only [Matrix.neg_apply, Matrix.of_apply, neg_pos] at h
  exact_mod_cast h

end MMP.Threefold.Resolution

namespace MMP.Flips

open MMP.Mori

section Germ

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X}
  {B : QDivisor X} {g : Y ⟶ X} [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
  {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y}

/-- **Existence and uniqueness of the log discrepancy vector, given negative definiteness**
(FA 3.1.0). Let `g` be a resolution of the surface germ with boundary `(X, P; B)` with
exceptional curves `E_1, …, E_n`, let `Y` carry a canonical divisor, and let the intersection
matrix `((E_i · E_j))` be negative definite. Then there is exactly one log discrepancy vector of
`(X, P; B)` on `g`: the defining conditions are the linear system
`((K_Y + g⁻¹_* B) · E_j) + ∑ᵢ (1 - aᵢ)(E_i · E_j) = 0` with nonsingular matrix. -/
theorem existsUnique_isGermLogDiscrepancyVector_of_posDef
    (hB : IsSurfaceGermWithBoundary sX P B) (hg : IsGermResolution sX P g)
    (hE : IsExceptionalCurveEnumeration g P E) {K₀ : Divisor Y}
    (hK₀ : K₀.IsCanonicalDivisor (g ≫ sX) 2)
    (C : Fin n → ProperCurve (g ≫ sX)) (hC : ∀ i, (C i).point = (E i).genericPoint)
    (hneg : (-(Matrix.of fun i j : Fin n =>
      ((Divisor.toQDivisor (Finsupp.single (E i) 1)).intersectionNumber k (g ≫ sX) (C j).ι
        (C j).dim_le (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme
          hg.isSmoothResolution.isSmoothScheme (E i)) : ℝ))).PosDef) :
    ∃! a : Fin n → ℚ, IsGermLogDiscrepancyVector sX P B g E a := by
  have hsm := hg.isSmoothResolution.isSmoothScheme
  set M : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j : Fin n =>
    (Divisor.toQDivisor (Finsupp.single (E i) 1)).intersectionNumber k (g ≫ sX) (C j).ι
      (C j).dim_le (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm (E i)) with hMdef
  have hM : M.det ≠ 0 := MMP.MatrixPosDef.det_ne_zero_of_posDef_neg_map M hneg
  have hμ : ∀ i j, IsIntersectionNumber (g ≫ sX) (Divisor.toQDivisor (Finsupp.single (E i) 1))
      (E j).idealSheaf (M i j) := fun i j =>
    isIntersectionNumber_of_properCurve _ _ (C j) (E j) (hC j)
  set D₀ : QDivisor Y := Divisor.toQDivisor K₀ + inverseTransformDivisor g B
  set β : Fin n → ℚ := fun j => D₀.intersectionNumber k (g ≫ sX) (C j).ι (C j).dim_le
    (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm D₀)
  have hβ : ∀ j, IsIntersectionNumber (g ≫ sX) D₀ (E j).idealSheaf (β j) := fun j =>
    isIntersectionNumber_of_properCurve _ _ (C j) (E j) (hC j)
  have hsingle : ∀ (i : Fin n) (c : ℚ), (Finsupp.single (E i) c : QDivisor Y) =
      c • Divisor.toQDivisor (Finsupp.single (E i) 1) := by
    intro i c
    ext F
    by_cases hF : E i = F
    · subst hF
      simp [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom]
    · simp [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom]
  have hval : ∀ (c : Fin n → ℚ) j, IsIntersectionNumber (g ≫ sX)
      (D₀ + ∑ i, Finsupp.single (E i) (c i)) (E j).idealSheaf (β j + ∑ i, c i * M i j) := by
    intro c j
    refine isIntersectionNumber_add (hβ j) (isIntersectionNumber_sum _
      (isIntersectionNumber_zero (hβ j)) fun i _ => ?_)
    rw [hsingle]
    exact (hμ i j).smul (c i) (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _)
  have hiff : ∀ a : Fin n → ℚ, IsGermLogDiscrepancyVector sX P B g E a ↔
      ∀ j, β j + ∑ i, (1 - a i) * M i j = 0 := by
    intro a
    rw [isGermLogDiscrepancyVector_iff_of_isCanonicalDivisor hK₀]
    refine ⟨fun h j => ((hval (fun i => 1 - a i) j).unique (h.2.2.2 j)),
      fun h => ⟨hB, hg, hE, fun j => h j ▸ hval (fun i => 1 - a i) j⟩⟩
  obtain ⟨c, hc, huniq⟩ := MMP.MatrixPosDef.existsUnique_add_sum_mul_eq_zero M hM β
  refine ⟨fun i => 1 - c i, (hiff _).2 fun j => by simpa using hc j, fun a ha => ?_⟩
  funext i
  have hi := congrFun (huniq (fun i => 1 - a i) ((hiff a).1 ha)) i
  linarith

omit [QuasiCompact (g ≫ sX)] in
/-- An exceptional curve `E` of a resolution `g` of `(X, P)` is a proper curve of `Y` with the
generic point of `E`, contracted by `g`. -/
theorem IsGermExceptionalCurve.exists_properCurve (hg : IsGermResolution sX P g)
    {F : Mori.PrimeDivisor Y} (hF : IsGermExceptionalCurve g P F) :
    ∃ C : ProperCurve (g ≫ sX), C.point = F.genericPoint ∧ C.IsContractedBy g := by
  obtain ⟨hc, hp⟩ := hF.isProper sX hg
  have h := vanishingIdeal_closure_genericPoint_eq_idealSheaf F
  have hsupp : (F.support : Set Y) ⊆ g.base ⁻¹' {P} := hF.1.prop.2
  have hcl : closure ({F.genericPoint} : Set Y) = F.support :=
    (AlgebraicGeometry.PrimeDivisor.support_eq_closure F).symm
  refine ⟨⟨F.genericPoint, ⟨?_, ?_⟩⟩, rfl, fun x hx => ?_⟩
  · change topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal _).subscheme = 1
    rw [h]
    exact hc.2
  · change IsProper ((Scheme.IdealSheafData.vanishingIdeal _).subschemeι ≫ g ≫ sX)
    rw [h]
    exact hp
  · change x ∈ closure ({F.genericPoint} : Set Y) at hx
    rw [hcl] at hx
    have h1 : g x = P := hsupp hx
    have h2 : g F.genericPoint = P := hsupp (by rw [← hcl]; exact subset_closure rfl)
    exact h1.trans h2.symm

omit [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- A resolution of a surface germ is finite over `X ∖ {P}`, an open subset meeting its image:
it is generically finite. -/
theorem IsGermResolution.exists_isFinite (hg : IsGermResolution sX P g) :
    ∃ V : X.Opens, ((V : Set X) ∩ Set.range g.base).Nonempty ∧ IsFinite (g ∣_ V) := by
  obtain ⟨U, hU, hiso⟩ := hg.isIso_away
  obtain ⟨x, hx⟩ : ∃ x : X, x ≠ P := by
    by_contra hall
    push Not at hall
    have : Subsingleton X := ⟨fun a b => (hall a).trans (hall b).symm⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology X
    rw [hg.isSurfaceGerm.2.1] at h0
    exact absurd h0 (by decide)
  have hxU : x ∈ U := by
    change x ∈ (U : Set X)
    rw [hU]; exact hx
  obtain ⟨y, hy⟩ := (g ∣_ U).surjective ⟨x, hxU⟩
  refine ⟨U, ⟨x, hxU, y.1, ?_⟩, inferInstance⟩
  rw [← morphismRestrict_base_coe g U y, hy]

omit [IsLocallyNoetherian Y] in
/-- The source of a resolution of a surface germ is a variety. -/
theorem IsGermResolution.isVariety (hg : IsGermResolution sX P g) :
    Mori.IsVariety k (g ≫ sX) := by
  have := hg.isIntegral sX
  have := hg.isSmoothResolution.isProper
  have hX := hg.isSurfaceGerm.1.1
  have := hX.toIsSeparated
  have := hX.toLocallyOfFiniteType
  exact { }

/-- **Existence and uniqueness of the log discrepancy vector over an affine germ** (FA 3.1.0).
Let `(X, P; B)` be a surface germ with boundary, `X` affine, and `g` a resolution of `(X, P)`
with exceptional curves `E_1, …, E_n`, `Y` carrying a canonical divisor. Then there is exactly
one log discrepancy vector of `(X, P; B)` on `g`. -/
theorem existsUnique_isGermLogDiscrepancyVector_of_isAffine [IsAffine X]
    (hB : IsSurfaceGermWithBoundary sX P B) (hg : IsGermResolution sX P g)
    (hE : IsExceptionalCurveEnumeration g P E)
    (hK : ∃ K : Divisor Y, K.IsCanonicalDivisor (g ≫ sX) 2) :
    ∃! a : Fin n → ℚ, IsGermLogDiscrepancyVector sX P B g E a := by
  obtain ⟨K₀, hK₀⟩ := hK
  have hX := hB.1.1
  have := hX.1.toQuasiCompact
  have := hX.2
  have := hg.isSmoothResolution.isProper
  choose C hC hCc using fun i => (hE.isGermExceptionalCurve i).exists_properCurve hg
  refine existsUnique_isGermLogDiscrepancyVector_of_posDef hB hg hE hK₀ C hC ?_
  exact MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isAffine hg.isVariety
    hg.isSmoothResolution.isSmoothScheme hg.topologicalKrullDim_eq hX.1 rfl hg.exists_isFinite E
    hE.injective C hC hCc

end Germ

end MMP.Flips
