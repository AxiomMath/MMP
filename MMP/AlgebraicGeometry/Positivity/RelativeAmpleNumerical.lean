module

public import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeCartier

section

/-!
# Relative ampleness is a numerical property

Let `k` be an algebraically closed field of characteristic zero and `f : X ⟶ V` a projective
morphism of `k`-varieties. If two `ℚ`-Cartier divisors `L` and `L'` on `X` are numerically
equivalent over `V`, that is, `(L · C) = (L' · C)` for every proper curve `C ⊆ X` contracted by
`f`, and `L` is `f`-ample, then `L'` is `f`-ample. Choosing `m > 0` with `mL` and `mL'` Cartier,
both define the same linear form on `N₁(X/V)`, and the relative Kleiman criterion
`MMP.Mori.isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos` transfers
ampleness from `mL` to `mL'`.

## Main results

* `MMP.Fourfold.KCartierDivisor.IsRelativelyAmpleQ.of_sub_mem_relativeNumericallyTrivialDivisors`

The relative Kleiman criterion for `ℚ`-Cartier divisors (an `f`-ample `ℚ`-Cartier divisor is
exactly one positive on `NE̅(X/V) ∖ 0`) is proved here as a private lemma, from which the result
is immediate.

## Implementation notes

A rational Cartier divisor is a `ℚ`-Cartier divisor `KCartierDivisor ℚ X`, and `f`-ampleness is
`MMP.Fourfold.KCartierDivisor.IsRelativelyAmpleQ` (some positive multiple is an integral Cartier
divisor whose invertible sheaf is `f`-ample). Numerical equivalence over `V` is the vanishing in
`N¹(X/V)`: the difference of the associated `ℝ`-Cartier divisors lies in
`MMP.Flips.relativeNumericallyTrivialDivisors`, i.e. it has degree zero on every contracted curve.
Projectivity is `AlgebraicGeometry.IsProjective`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.44
-/

open AlgebraicGeometry CategoryTheory MMP.Mori

namespace MMP.FourfoldProofs.MmpRelativeAmplenessNumericalProof

section Degree

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- The degree along a proper curve is additive on Cartier divisors. -/
private theorem degree_sheaf_add (B B' : X.CartierDivisor) (C : ProperCurve sX) :
    C.degree k (MMP.CartierDivisor.sheaf (B + B')) =
      C.degree k (MMP.CartierDivisor.sheaf B) +
        C.degree k (MMP.CartierDivisor.sheaf B') := by
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((MMP.CartierDivisor.sheaf B).tensorObj (MMP.CartierDivisor.sheaf B')) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2
      (MMP.CartierDivisor.sheaf B) (MMP.CartierDivisor.sheaf B')
  unfold ProperCurve.degree
  rw [← degreeOn_tensorSheaf k sX C.ι C.dim_le (hLM := this)]
  exact (degreeOn_eq_of_iso k sX C.ι C.dim_le
    (MMP.CartierDivisorSheaf.sheafMulIso B B')).symm

/-- The degree along a proper curve, as an additive map on Cartier divisors. -/
private noncomputable def degreeSheafHom (C : ProperCurve sX) : X.CartierDivisor →+ ℤ :=
  AddMonoidHom.mk' (fun B => C.degree k (MMP.CartierDivisor.sheaf B))
    fun B B' => degree_sheaf_add B B' C

/-- `(C · c) = (C · ∑ c_B B)` for the realization of an integral `ℚ`-Cartier divisor `c`. -/
private theorem intersectionNumber_ofCartier_realization (C : ProperCurve sX)
    (c : KCartierDivisor ℚ X) (h : ∀ D, ∃ n : ℤ, c D = n) :
    (C.cycle ℝ).intersectionNumber
        (KCartierDivisor.ofCartier ℝ (KCartierDivisor.realization c h)) =
      (C.cycle ℝ).intersectionNumber (MMP.Fourfold.KCartierDivisor.toReal c) := by
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle,
    OneCycle.intersectionNumber_eq_sum]
  simp only [MMP.Fourfold.KCartierDivisor.toReal, Finsupp.mapRange.addMonoidHom_apply]
  rw [Finsupp.sum_mapRange_index (by simp)]
  simp only [ProperCurve.cycle, Finsupp.sum_single_index, zero_mul, one_mul]
  change ((degreeSheafHom C (KCartierDivisor.realization c h) : ℤ) : ℝ) = _
  rw [KCartierDivisor.realization, Finsupp.sum, map_sum, Finsupp.sum]
  push_cast
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [map_zsmul, smul_eq_mul, Int.cast_mul]
  congr 1
  change _ = ((c D : ℚ) : ℝ)
  rw [← Rat.cast_intCast (α := ℝ), ← Classical.choose_spec (h D)]

/-- Two `ℝ`-Cartier divisors with the same degree on every contracted curve define the same
linear form on `N₁(X/V)`. -/
private theorem intersectionNumber_eq_of_forall_isContractedBy {V : Scheme.{0}} {f : X ⟶ V}
    {D D' : KCartierDivisor ℝ X}
    (h : ∀ C : ProperCurve sX, C.IsContractedBy f →
      (C.cycle ℝ).intersectionNumber D = (C.cycle ℝ).intersectionNumber D')
    (z : RelativeNumericalCurveClasses sX f) :
    RelativeNumericalCurveClasses.intersectionNumber D z =
      RelativeNumericalCurveClasses.intersectionNumber D' z := by
  obtain ⟨⟨Z, hZ⟩, rfl⟩ := relativeNumericalClass_surjective sX f z
  rw [RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass,
    RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass]
  change OneCycle.intersectionPairing D Z = OneCycle.intersectionPairing D' Z
  change Z ∈ Finsupp.supported ℝ ℝ _ at hZ
  rw [Finsupp.supported_eq_span_single] at hZ
  induction hZ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨C, hC, rfl⟩ := hx
    exact h C hC
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, map_smul, hx]

/-- The pairing of `N₁(X/V)` with `ℝ`-Cartier divisors is homogeneous in the divisor. -/
private theorem intersectionNumber_smul_left {V : Scheme.{0}} {f : X ⟶ V} (r : ℝ)
    (D : KCartierDivisor ℝ X) (z : RelativeNumericalCurveClasses sX f) :
    RelativeNumericalCurveClasses.intersectionNumber (r • D) z =
      r * RelativeNumericalCurveClasses.intersectionNumber D z := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  rw [RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass,
    RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass]
  change OneCycle.intersectionPairing (r • D) (Z : OneCycle ℝ sX) =
    r * OneCycle.intersectionPairing D (Z : OneCycle ℝ sX)
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

end Degree

/-- Some positive integer multiple of a `ℚ`-Cartier divisor has integral coefficients. -/
private theorem exists_pos_nat_smul_eq_intCast {X : Scheme.{0}} (c : KCartierDivisor ℚ X) :
    ∃ m : ℕ, 0 < m ∧ ∀ E, ∃ n : ℤ, ((m : ℚ) • c) E = n := by
  classical
  refine ⟨∏ D ∈ c.support, (c D).den, Finset.prod_pos fun D _ => (c D).den_pos, fun E => ?_⟩
  by_cases hE : E ∈ c.support
  · obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun D => (c D).den) hE
    refine ⟨q * (c E).num, ?_⟩
    rw [Finsupp.smul_apply, smul_eq_mul, hq]
    push_cast
    rw [mul_comm ((c E).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
  · exact ⟨0, by simp [Finsupp.notMem_support_iff.mp hE]⟩

/-- On `N₁(X/V)`, the Cartier divisor realizing an integral multiple `m • L` of a `ℚ`-Cartier
divisor defines `m` times the linear form of `L`. -/
private theorem intersectionNumber_realization_nsmul {k : Type} [Field k] {X V : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {f : X ⟶ V} (L : KCartierDivisor ℚ X) (m : ℕ)
    (h : ∀ E, ∃ n : ℤ, ((m : ℚ) • L) E = n) (z : RelativeNumericalCurveClasses sX f) :
    RelativeNumericalCurveClasses.intersectionNumber
        (KCartierDivisor.ofCartier ℝ (KCartierDivisor.realization ((m : ℚ) • L) h)) z =
      m * RelativeNumericalCurveClasses.intersectionNumber
        (MMP.Fourfold.KCartierDivisor.toReal L) z := by
  rw [intersectionNumber_eq_of_forall_isContractedBy
    (D' := MMP.Fourfold.KCartierDivisor.toReal ((m : ℚ) • L)) (fun C _ =>
intersectionNumber_ofCartier_realization C _ h) z,
    Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ,
    intersectionNumber_smul_left]

/-- **Relative Kleiman criterion for `ℚ`-Cartier divisors.** For a projective morphism `f` of
varieties over an algebraically closed field of characteristic zero, a `ℚ`-Cartier divisor is
`f`-ample if and only if it is positive on every nonzero class of `NE̅(X/V)`. -/
private theorem isRelativelyAmpleQ_iff_forall_pos
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X V : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sV : V ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k sV]
    (f : X ⟶ V) (hfp : IsProjective f) (hf : f ≫ sV = sX) (L : KCartierDivisor ℚ X) :
    MMP.Fourfold.KCartierDivisor.IsRelativelyAmpleQ f L ↔
      ∀ z ∈ relativeClosedConeOfCurves sX f, z ≠ 0 →
        0 < RelativeNumericalCurveClasses.intersectionNumber
          (MMP.Fourfold.KCartierDivisor.toReal L) z := by
  refine ⟨fun ⟨m, _, h, hamp⟩ z hz hz0 => pos_of_mul_pos_right ?_ m.cast_nonneg, fun hL => ?_⟩
  · rw [← intersectionNumber_realization_nsmul L m h]
    exact (isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos
      sV sX f hfp hf _).1 hamp z hz hz0
  · obtain ⟨m, hm, h⟩ := exists_pos_nat_smul_eq_intCast L
    refine ⟨m, hm, h, (isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos
      sV sX f hfp hf _).2 fun z hz hz0 => ?_⟩
    rw [intersectionNumber_realization_nsmul]
    exact mul_pos (Nat.cast_pos.mpr hm) (hL z hz hz0)

end MMP.FourfoldProofs.MmpRelativeAmplenessNumericalProof

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

open MMP.FourfoldProofs.MmpRelativeAmplenessNumericalProof in
/-- **Relative ampleness is numerical.** Let `f : X ⟶ V` be a projective morphism of varieties
over an algebraically closed field `k` of characteristic zero, and `L, L'` `ℚ`-Cartier divisors
on `X` numerically equivalent over `V`. If `L` is `f`-ample, then so is `L'`. -/
@[mmp "thm_mmp_relative_ampleness_numerical"]
public theorem KCartierDivisor.IsRelativelyAmpleQ.of_sub_mem_relativeNumericallyTrivialDivisors
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X V : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sV : V ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k sV]
    (f : X ⟶ V) (hfp : IsProjective f) (hf : f ≫ sV = sX) {L L' : KCartierDivisor ℚ X}
    (hLL' : KCartierDivisor.toReal L' - KCartierDivisor.toReal L ∈
      MMP.Flips.relativeNumericallyTrivialDivisors sX f)
    (hL : KCartierDivisor.IsRelativelyAmpleQ f L) :
    KCartierDivisor.IsRelativelyAmpleQ f L' := by
  refine (isRelativelyAmpleQ_iff_forall_pos sX sV f hfp hf L').2 fun z hz hz0 => ?_
  rw [intersectionNumber_eq_of_forall_isContractedBy (fun C hC => sub_eq_zero.1 <| by
    simpa [OneCycle.intersectionNumber] using
      (MMP.Flips.mem_relativeNumericallyTrivialDivisors sX f).1 hLL' C hC) z]
  exact (isRelativelyAmpleQ_iff_forall_pos sX sV f hfp hf L).1 hL z hz hz0

end MMP.Fourfold

end
