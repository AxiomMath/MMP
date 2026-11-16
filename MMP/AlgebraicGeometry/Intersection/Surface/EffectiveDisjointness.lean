module

public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity

/-!
# Effective `ℚ`-Cartier intersections on a normal surface detect disjointness

Let `Y` be a normal projective surface over a field `k`, and `A, A'` effective `ℚ`-divisors on
`Y` without common components, with `A` `ℚ`-Cartier. Writing `A' = ∑ b_C C` with prime divisors
`C`, the intersection number `A · A' = ∑ b_C (A · C)` is defined, nonnegative, and vanishes
exactly when `Supp A ∩ Supp A' = ∅`.

The proof chooses `m > 0` with `mA = E` a Cartier divisor; `E` is effective with
`Supp E = Supp A`. Every prime component `C` of `A'` is a proper integral curve not contained in
`Supp A`, so `m (A · C) = deg_C 𝒪_Y(E) ≥ 0`, with equality exactly when `C ∩ Supp A = ∅`
(`MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff`). Summing with the positive coefficients
of `A'` gives the result.

## Main results

* `MMP.Flips.intersectionNumber_nonneg_and_eq_zero_iff_disjoint`

## Implementation notes

`A'` need not be `ℚ`-Cartier, so `A · A'` is the linear extension in the second variable of the
intersection numbers `(A · C)` of the `ℚ`-Cartier `A` with the proper curves `C` underlying the
prime components of `A'`; each `(A · C)` is `MMP.Mori.IsIntersectionNumber`, which asserts that
it is defined (`C` proper of dimension at most one, `A` `ℚ`-Cartier) and gives its value.
"Without common components" is disjointness of the sets of prime components.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 11
-/

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Flips

open MMP.Mori

/-- The dimension of a scheme is the Krull dimension of its specialization order. -/
private theorem topologicalKrullDim_eq_krullDim.{v} (X : Scheme.{v}) :
    topologicalKrullDim X = Order.krullDim X := by
  let _ : PartialOrder X := specializationOrder X
  exact Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))

/-- A prime divisor on a scheme of dimension two has dimension at most one. -/
private theorem topologicalKrullDim_subscheme_le_one.{v} {Y : Scheme.{v}}
    (hdim : topologicalKrullDim Y = 2) (C : Mori.PrimeDivisor Y) :
    topologicalKrullDim C.idealSheaf.subscheme ≤ 1 := by
  set ξ := C.genericPoint
  have hξdim : Order.height ξ ≤ 1 := by
    have hsum : Order.height ξ + Order.coheight ξ ≤ 2 := by
      have : Nonempty Y := ⟨ξ⟩
      have h := Order.krullDim_eq_iSup_height_add_coheight_of_nonempty (α := Y)
      rw [← topologicalKrullDim_eq_krullDim, hdim] at h
      have h' : ((Order.height ξ + Order.coheight ξ : ℕ∞) : WithBot ℕ∞) ≤ 2 := by
        rw [h]
        exact WithBot.coe_le_coe.mpr
          (le_iSup (fun a : Y => Order.height a + Order.coheight a) ξ)
      exact WithBot.coe_le_coe.mp h'
    rw [Mori.PrimeDivisor.coheight_genericPoint] at hsum
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp
      (by simpa [one_add_one_eq_two] using hsum)
  have hmono : StrictMono C.idealSheaf.subschemeι.base := by
    intro a c hac
    refine lt_of_le_not_ge ?_ fun hca => hac.not_ge (Scheme.le_iff_specializes.mpr ?_)
    · exact Scheme.le_iff_specializes.mpr
        ((Scheme.le_iff_specializes.mp hac.le).map C.idealSheaf.subschemeι.continuous)
    · exact C.idealSheaf.subschemeι.isClosedEmbedding.isInducing.specializes_iff.mp
        (Scheme.le_iff_specializes.mp hca)
  rw [topologicalKrullDim_eq_krullDim, Order.krullDim_eq_iSup_height]
  refine iSup_le fun y => ?_
  have hy : C.idealSheaf.subschemeι y ≤ ξ := by
    have hmem : C.idealSheaf.subschemeι y ∈ C.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨y, rfl⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hmem
    exact Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hmem)
  have h1 : Order.height y ≤ Order.height ξ :=
    (Order.height_le_height_apply_of_strictMono _ hmono y).trans (Order.height_mono hy)
  exact_mod_cast h1.trans hξdim

/-- An integral divisor `E` with `E = m • A` for some `m : ℕ` and `A` effective is effective. -/
private theorem nonneg_of_toQDivisor_eq_smul {Y : Scheme.{u}} {A : QDivisor Y}
    (hAe : A.IsEffective) {m : ℕ} {E : Divisor Y} (hE : Divisor.toQDivisor E = (m : ℤ) • A) :
    0 ≤ E := fun P => by
  have h := congrArg (fun G : QDivisor Y => G P) hE
  simp only [Finsupp.smul_apply, zsmul_eq_mul] at h
  exact_mod_cast (show (0 : ℚ) ≤ E P by
    rw [show ((E P : ℤ) : ℚ) = Divisor.toQDivisor E P from (Divisor.coeff_toQDivisor E P).symm,
      h]; exact mul_nonneg (by positivity) (hAe P))

/-- The generic point of a prime divisor `C` that is not a component of `A` lies outside
`Supp A`. -/
private theorem genericPoint_notMem_supp {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    {A : QDivisor Y} {C : Mori.PrimeDivisor Y} (hC : C ∉ A.support) : C.genericPoint ∉ A.supp := by
  rw [DivisorWithCoeffs.mem_supp_iff]
  rintro ⟨P, hP0, hPc⟩
  obtain rfl := Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support P C hPc
  exact hP0 (Finsupp.notMem_support_iff.1 hC)

/-- **Intersection with a curve outside the support.** On a normal proper surface, an
effective `ℚ`-Cartier divisor `A` meets a prime divisor `C` not among its components
nonnegatively, and `A · C = 0` exactly when `C` is disjoint from `Supp A`. -/
private theorem intersectionNumber_nonneg_and_eq_zero_iff (k : Type u) [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsProper sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hdim : topologicalKrullDim Y = 2) {A : QDivisor Y} (hA : A.IsQCartier)
    (hAe : A.IsEffective) {C : Mori.PrimeDivisor Y} (hC : C ∉ A.support) :
    haveI := C.integral
    0 ≤ A.intersectionNumber k sY C.idealSheaf.subschemeι
        (topologicalKrullDim_subscheme_le_one hdim C) hA ∧
      (A.intersectionNumber k sY C.idealSheaf.subschemeι
        (topologicalKrullDim_subscheme_le_one hdim C) hA = 0 ↔
          Disjoint (A.supp : Set Y) C.support) := by
  haveI := C.integral
  obtain ⟨m, hm, E, hE, hEc⟩ := hA.exists_pos
  have hsupp : E.supp = A.supp :=
    QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hE
  have hr : Set.range C.idealSheaf.subschemeι = C.support :=
    Scheme.IdealSheafData.range_subschemeι _
  obtain ⟨c, hc⟩ : C.genericPoint ∈ Set.range C.idealSheaf.subschemeι := by
    rw [hr, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  obtain ⟨hnn, hiff⟩ := MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sY
    C.idealSheaf.subschemeι (topologicalKrullDim_subscheme_le_one hdim C) E hEc
    (nonneg_of_toQDivisor_eq_smul hAe hE) ⟨c, hc ▸ hsupp ▸ genericPoint_notMem_supp hC⟩
  rw [QDivisor.intersectionNumber_eq_of_smul k sY _ _ A hA hm E hEc hE]
  refine ⟨div_nonneg (by exact_mod_cast hnn) (by positivity), ?_⟩
  rw [div_eq_zero_iff, or_iff_left (by positivity), Int.cast_eq_zero, hiff, hsupp, ← hr,
    Set.disjoint_right, Set.forall_mem_range]
  exact Iff.rfl

/-- **Effective `ℚ`-Cartier intersections on a normal surface detect disjointness.** Let `Y` be a
normal projective surface over a field `k` and `A, A'` effective `ℚ`-divisors on `Y` without
common components, `A` being `ℚ`-Cartier. Then the intersection numbers `(A · C)` with the prime
components `C` of `A'` are defined, and `A · A' = ∑_C A'(C) (A · C)` satisfies `A · A' ≥ 0`, with
equality if and only if `Supp A ∩ Supp A' = ∅`. -/
@[mmp "lem_mmp_foundation_fa11_disjoint_effective_intersection"]
public theorem intersectionNumber_nonneg_and_eq_zero_iff_disjoint (k : Type u) [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (hY : Mori.IsProjectiveVariety k sY)
    [IsLocallyNoetherian Y] [IsNormal Y] (hdim : topologicalKrullDim Y = 2)
    {A A' : QDivisor Y} (hA : A.IsQCartier) (hAe : A.IsEffective) (hA'e : A'.IsEffective)
    (hAA' : Disjoint A.support A'.support) :
    haveI : QuasiCompact sY := hY.toIsVariety.toQuasiCompact
    ∃ x : Mori.PrimeDivisor Y → ℚ,
      (∀ C ∈ A'.support, IsIntersectionNumber sY A C.idealSheaf (x C)) ∧
      0 ≤ A'.sum (fun C b => b * x C) ∧
      (A'.sum (fun C b => b * x C) = 0 ↔ Disjoint (A.supp : Set Y) A'.supp) := by
  haveI : QuasiCompact sY := hY.toIsVariety.toQuasiCompact
  haveI := ((Mori.isProjectiveVariety_iff k sY).mp hY).2
  have key C (h : C ∈ A'.support) := intersectionNumber_nonneg_and_eq_zero_iff k sY hdim hA hAe
    (Finset.disjoint_right.mp hAA' h)
  have hterm C (h : C ∈ A'.support) := mul_nonneg (hA'e C) (key C h).1
  refine ⟨fun C => haveI := C.integral; A.intersectionNumber k sY C.idealSheaf.subschemeι
    (topologicalKrullDim_subscheme_le_one hdim C) hA, fun C _ =>
      ⟨inferInstance, _, hA, rfl⟩, Finset.sum_nonneg hterm, ?_⟩
  refine (Finset.sum_eq_zero_iff_of_nonneg hterm).trans ?_
  rw [DivisorWithCoeffs.coe_supp A', Set.disjoint_iUnion₂_right]
  exact forall₂_congr fun C h => mul_eq_zero.trans <|
    (or_iff_right (Finsupp.mem_support_iff.mp h)).trans (key C h).2

end MMP.Flips
