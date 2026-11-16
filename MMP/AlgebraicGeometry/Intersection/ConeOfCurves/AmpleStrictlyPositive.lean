module
public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Basic
public import MMP.AlgebraicGeometry.Divisor.Basic
public import MMP.AlgebraicGeometry.Positivity.RelativelyAmple
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul

/-!
# Ample divisors are strictly positive on the closed cone of curves

Let `X` be a projective variety over an arbitrary field `k` and `D` an ample Cartier divisor
on `X`. Every nonzero class of the closed cone of curves `NE̅(X) ⊆ N₁(X)` lies in the open
half-space `D_{>0}`: its intersection number with `D` is positive.

The proof is Kleiman's argument. Given a nonzero class `z ∈ NE̅(X)`, Cartier divisors separate
numerical classes, so some Cartier divisor `E` has `(E · z) ≠ 0`. For `m ≫ 0` both `mD + E` and
`mD - E` are ample, hence nef, hence nonnegative on `NE̅(X)`, so `m (D · z) ≥ |(E · z)| > 0`.

## Main results

* `MMP.Mori.closedConeOfCurves_diff_zero_subset_posHalfspace`: `NE̅(X) \ {0} ⊆ D_{>0}`.

## Implementation notes

Ampleness of `D` is ampleness of its invertible sheaf `𝒪_X(D)` on `X`, and `D` enters the
half-space as the `ℝ`-Cartier divisor `1 · D`. No hypothesis on the base field is made.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.18
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- `deg_C 𝒪_X(E + E') = deg_C 𝒪_X(E) + deg_C 𝒪_X(E')` along a proper curve. -/
private theorem degree_cartierSheaf_add {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX)
    (E E' : X.CartierDivisor) :
    C.degree k (MMP.CartierDivisor.sheaf (E + E')) =
      C.degree k (MMP.CartierDivisor.sheaf E) +
        C.degree k (MMP.CartierDivisor.sheaf E') := by
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
          (MMP.CartierDivisor.sheaf E')) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 _ _
  unfold ProperCurve.degree
  rw [← degreeOn_tensorSheaf]
  exact (degreeOn_eq_of_iso k sX C.ι C.dim_le
    (L := ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
          (MMP.CartierDivisor.sheaf E'))
    (MMP.CartierDivisorSheaf.sheafMulIso E E')).symm

/-- The pairing `E ↦ (E · z)` with a fixed numerical class `z`, as an additive map on Cartier
divisors. -/
private noncomputable def pairing {sX : X ⟶ Spec (.of k)} (z : NumericalCurveClasses sX) :
    X.CartierDivisor →+ ℝ :=
  AddMonoidHom.mk' (fun E => NumericalCurveClasses.intersectionNumber
      (KCartierDivisor.ofCartier ℝ E) z) fun E E' => by
    obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
    simp only [NumericalCurveClasses.intersectionNumber_numericalClass,
      OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_apply]
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun C _ => ?_
    rw [degree_cartierSheaf_add]
    push_cast
    ring

/-- An ample Cartier divisor pairs nonnegatively with every class of the closed cone of curves. -/
private theorem pairing_nonneg_of_isAmple {sX : X ⟶ Spec (.of k)} [IsProjectiveVariety k sX]
    {z : NumericalCurveClasses sX} (hz : z ∈ closedConeOfCurves sX) {F : X.CartierDivisor}
    (hF : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf F)) :
    0 ≤ pairing z F := by
  have hX := ((isProjectiveVariety_iff k sX).1 inferInstance).1
  have hnef : KCartierDivisor.IsNef k sX (KCartierDivisor.ofCartier ℝ F) := fun C => by
    rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]
    exact_mod_cast (MMP.Threefold.Mori.degreeOn_cartierSheaf_pos_of_isAmple hX F hF C).le
  exact (KCartierDivisor.mem_nonnegHalfspace_iff sX _ z).1
    ((KCartierDivisor.isNef_iff_closedConeOfCurves_subset_nonnegHalfspace sX _).1 hnef hz)

/-- Cartier divisors separate numerical curve classes: a nonzero class pairs nontrivially with
some Cartier divisor. -/
private theorem exists_pairing_ne_zero {sX : X ⟶ Spec (.of k)} [IsProjectiveVariety k sX]
    {z : NumericalCurveClasses sX} (hz0 : z ≠ 0) :
    ∃ E : X.CartierDivisor, pairing z E ≠ 0 := by
  by_contra! h
  apply hz0
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
  refine (Submodule.Quotient.mk_eq_zero _).mpr
    (OneCycle.mem_numericallyTrivial.mpr fun L _ => ?_)
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
  have h0 := h E
  simp only [pairing, AddMonoidHom.mk'_apply,
    NumericalCurveClasses.intersectionNumber_numericalClass,
    OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree] at h0
  rw [← h0, OneCycle.degree, OneCycle.degree]
  congr 2
  funext C
  exact congrArg _ (degreeOn_eq_of_iso k sX C.ι C.dim_le e)

/-- On a projective variety `X`, an ample Cartier divisor `D` is strictly positive on every
nonzero class of the closed cone of curves: `NE̅(X) \ {0} ⊆ D_{>0}`. -/
@[mmp "lem_mmp_foundation_full_field_ample_strict_closed_cone"]
public theorem closedConeOfCurves_diff_zero_subset_posHalfspace (sX : X ⟶ Spec (.of k))
    [IsProjectiveVariety k sX] (D : X.CartierDivisor)
    (hD : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf D)) :
    (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) \ {0} ⊆
      KCartierDivisor.posHalfspace sX (KCartierDivisor.ofCartier ℝ D) := by
  intro z ⟨hz, hz0⟩ Z hZ
  rw [← NumericalCurveClasses.intersectionNumber_numericalClass, hZ]
  obtain ⟨E, hE⟩ := exists_pairing_ne_zero hz0
  obtain ⟨m, hm₁, hm₂⟩ := ((eventually_isAmple_cartierSheaf_nsmul_add D E hD).and
    (eventually_isAmple_cartierSheaf_nsmul_add D (-E) hD)).exists
  have a := pairing_nonneg_of_isAmple hz hm₁
  have b := pairing_nonneg_of_isAmple hz hm₂
  rw [map_add, map_nsmul, nsmul_eq_mul] at a b
  rw [map_neg] at b
  change 0 < pairing z D
  refine pos_of_mul_pos_right (a := (m : ℝ)) ?_ m.cast_nonneg
  rcases hE.lt_or_gt with h | h <;> linarith

end MMP.Mori
