/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.NormalPosition.LocalDimension

/-!
# Surface pairs: curves on a smooth surface

The first results of Kollár–Mori, Notation 4.1 and Theorem 4.5, on curves on a smooth surface.

Throughout, the ground field `k` is algebraically closed of characteristic zero (the standing
convention of Kollár–Mori, Chapter 4). A *surface* is a variety of dimension two, a *smooth
surface* one whose structure morphism is smooth, and a curve on a smooth surface is a prime
divisor.

## Main results

* `MMP.Mori.nonneg_intersectionNumber_of_notMem_support`: for a proper curve `C` and an effective
  `ℚ`-divisor `D` not containing `C` on a smooth surface, `(D · C) ≥ 0`, with equality iff
  `C ∩ Supp D = ∅`.
* `MMP.Mori.multiplicityAt_mul_le_localIntersectionNumber`: `i_q(C, C') ≥ mult_q C · mult_q C'`
  (Kollár–Mori, proof of Theorem 4.5).

## Implementation notes

The source's standing hypotheses that every scheme in sight is locally Noetherian and normal, and
quasi-compact over `k`, enter as instance arguments, which the definitions used need; they hold
for the smooth surfaces and normal surfaces of the statements.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 4.1,
  Theorem 4.5
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]

/-! ### Curves on smooth surfaces -/

section SmoothSurface

variable {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- On a scheme smooth over `k` every local ring is a unique factorization domain. -/
private theorem uniqueFactorizationMonoid_stalk_of_smooth (hsm : IsSmoothScheme sY) (x : Y) :
    UniqueFactorizationMonoid (Y.presheaf.stalk x) := by
  have hx : x ∈ smoothLocus sY := by rw [hsm]; trivial
  obtain ⟨V, hxV, hV⟩ := mem_smoothLocus_iff.1 hx
  haveI : Smooth (V.ι ≫ sY) := hV
  haveI := isRegularLocalRing_stalk_of_smooth_over_field (V.ι ≫ sY) ⟨x, hxV⟩
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid (V.toScheme.presheaf.stalk ⟨x, hxV⟩)
  exact MulEquiv.uniqueFactorizationMonoid
    (V.stalkIso ⟨x, hxV⟩).commRingCatIsoToRingEquiv.toMulEquiv inferInstance

/-- A prime divisor containing the generic point of another one is equal to it. -/
private theorem eq_of_genericPoint_mem_support (P E : PrimeDivisor Y)
    (hE : E.genericPoint ∈ P.support) : P = E := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hE
  have hle : E.genericPoint ≤ P.genericPoint := specializes_iff_mem_closure.mpr hE
  by_contra hne
  have hlt : E.genericPoint < P.genericPoint := lt_of_le_not_ge hle fun h =>
    hne (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (Specializes.antisymm (show E.genericPoint ⤳ P.genericPoint from h)
        (show P.genericPoint ⤳ E.genericPoint from hle)).eq.symm)
  have h2 := Order.coheight_add_one_le hlt
  rw [PrimeDivisor.coheight_genericPoint, PrimeDivisor.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- On a smooth scheme every divisor is Cartier. -/
private theorem isCartier_of_isSmoothScheme (hsm : IsSmoothScheme sY) (D : Divisor Y) :
    D.IsCartier := by
  induction D using Finsupp.induction_linear with
  | zero => exact Divisor.isCartier_zero
  | add f g hf hg => exact hf.add hg
  | single E n =>
    simpa [Finsupp.smul_single] using
      (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm E).zsmul n

/-- On a smooth scheme every `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_of_isSmoothScheme (hsm : IsSmoothScheme sY) (D : QDivisor Y) :
    D.IsQCartier := by
  classical
  set m : ℕ := ∏ E ∈ D.support, (D E).den
  have hint : ∀ E, ∃ n : ℤ, ((m : ℤ) • D).coeff E = n := by
    intro E
    by_cases hE : E ∈ D.support
    · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun E => (D E).den) hE
      refine ⟨(c : ℤ) * (D E).num, ?_⟩
      rw [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, DivisorWithCoeffs.coeff_apply]
      have h1 : ((D E).den : ℚ) * D E = (D E).num := Rat.den_mul_eq_num _
      have h2 : (m : ℚ) = ((D E).den : ℚ) * c := by exact_mod_cast hc
      push_cast
      rw [h2, ← h1]
      ring
    · refine ⟨0, ?_⟩
      rw [Finsupp.notMem_support_iff] at hE
      simp [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_apply, hE]
  have hmpos : 0 < m := Finset.prod_pos fun E _ => (D E).den_pos
  obtain ⟨D', hD'⟩ := (QDivisor.mem_range_toQDivisor_iff _).2 hint
  exact ⟨m, by exact_mod_cast hmpos.ne', ⟨D', hD', isCartier_of_isSmoothScheme sY hsm D'⟩⟩

/-- The coefficients of the integral divisor `cartierIndex • D` are `cartierIndex * D E`. -/
private theorem coeff_toDivisor_cartierIndex_smul {D : QDivisor Y} (hQ : D.IsQCartier)
    (E : PrimeDivisor Y) :
    (((QDivisor.isCartierDivisor_cartierIndex_smul hQ).toDivisor E : ℤ) : ℚ) =
      (D.cartierIndex hQ : ℚ) * D E := by
  have h : Divisor.toQDivisor (QDivisor.isCartierDivisor_cartierIndex_smul hQ).toDivisor =
      (((D.cartierIndex hQ : ℕ) : ℤ)) • D :=
    (QDivisor.isCartierDivisor_cartierIndex_smul hQ).toQDivisor_toDivisor
  have := congrArg (fun F : QDivisor Y => F.coeff E) h
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
  rw [DivisorWithCoeffs.coeff_apply] at this
  simpa [DivisorWithCoeffs.coeff_apply] using this

/-- For an effective `D`, the integral divisor `cartierIndex • D` is effective. -/
private theorem toDivisor_cartierIndex_smul_nonneg {D : QDivisor Y} (hQ : D.IsQCartier)
    (hD : D.IsEffective) : 0 ≤ (QDivisor.isCartierDivisor_cartierIndex_smul hQ).toDivisor := by
  rw [← DivisorWithCoeffs.isEffective_iff_nonneg]
  intro E
  have h0 : (0 : ℚ) ≤ (((QDivisor.isCartierDivisor_cartierIndex_smul hQ).toDivisor.coeff E : ℤ) :
      ℚ) := by
    rw [DivisorWithCoeffs.coeff_apply, coeff_toDivisor_cartierIndex_smul hQ E]
    exact mul_nonneg (Nat.cast_nonneg _) (hD E)
  exact_mod_cast h0

/-- The integral divisor `cartierIndex • D` has the same support as `D`. -/
private theorem mem_supp_toDivisor_cartierIndex_smul_iff {D : QDivisor Y} (hQ : D.IsQCartier)
    (x : Y) : x ∈ (QDivisor.isCartierDivisor_cartierIndex_smul hQ).toDivisor.supp ↔ x ∈ D.supp := by
  rw [DivisorWithCoeffs.mem_supp_iff, DivisorWithCoeffs.mem_supp_iff]
  refine exists_congr fun E => and_congr_left fun _ => ?_
  have hmq : (D.cartierIndex hQ : ℚ) ≠ 0 := by exact_mod_cast (QDivisor.cartierIndex_pos hQ).ne'
  rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply, ne_eq, ne_eq,
    ← @Int.cast_eq_zero ℚ, coeff_toDivisor_cartierIndex_smul hQ E, mul_eq_zero, or_iff_right hmq]

/-- **Distinct curves meet nonnegatively.** On a smooth surface `Y`, let `C` be a proper curve and
`D` an effective `ℚ`-divisor not containing `C`. Then `(D · C)` is defined, `(D · C) ≥ 0`, and
`(D · C) = 0` if and only if `C ∩ Supp D = ∅`. -/
@[mmp "lem_km4a_distinct_curves_nonnegative_intersection"]
theorem nonneg_intersectionNumber_of_notMem_support (hY : IsVariety k sY)
    (hsm : IsSmoothScheme sY) (hdim : topologicalKrullDim Y = 2) (C : PrimeDivisor Y)
    (hC : IsProper (C.idealSheaf.subschemeι ≫ sY)) {D : QDivisor Y}
    (hD : D.IsEffective) (hCD : C ∉ D.support) :
    ∃ n : ℚ, IsIntersectionNumber sY D C.idealSheaf n ∧ 0 ≤ n ∧
      (n = 0 ↔ C.support ∩ (D.supp : Set Y) = ∅) := by
  classical
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI := C.integral
  haveI := hC
  have hUFD := uniqueFactorizationMonoid_stalk_of_smooth sY hsm
  have hQ := isQCartier_of_isSmoothScheme sY hsm D
  have hcd := QDivisor.isCartierDivisor_cartierIndex_smul hQ
  have hmq : (D.cartierIndex hQ : ℚ) ≠ 0 := by exact_mod_cast (QDivisor.cartierIndex_pos hQ).ne'
  have hr : Set.range C.idealSheaf.subschemeι = C.support :=
    Scheme.IdealSheafData.range_subschemeι _
  have hcartC : Stacks.Divisors.IsEffectiveCartierDivisor C.idealSheaf :=
    isEffectiveCartierDivisor_of_codimension_one_of_uniqueFactorizationMonoid C.idealSheaf
      C.codimension_one (fun x _ => hUFD x)
  have hdim1 : topologicalKrullDim C.idealSheaf.subscheme ≤ 1 :=
    Stacks.ResolutionOfSurfaces.topologicalKrullDim_subscheme_le_one hdim C.idealSheaf hcartC
  have hgen : C.genericPoint ∈ Set.range C.idealSheaf.subschemeι := by
    rw [hr, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hne : ∃ c : C.idealSheaf.subscheme, C.idealSheaf.subschemeι c ∉ hcd.toDivisor.supp := by
    obtain ⟨c, hc⟩ := hgen
    refine ⟨c, ?_⟩
    rw [hc, DivisorWithCoeffs.mem_supp_iff]
    rintro ⟨E, hE0, hEc⟩
    obtain rfl := eq_of_genericPoint_mem_support E C hEc
    apply hE0
    rw [DivisorWithCoeffs.coeff_apply]
    have h := coeff_toDivisor_cartierIndex_smul hQ E
    rw [Finsupp.notMem_support_iff.1 hCD, mul_zero] at h
    exact_mod_cast h
  obtain ⟨hnonneg, hzero⟩ := MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sY
    C.idealSheaf.subschemeι hdim1 hcd.toDivisor hcd.isCartier_toDivisor
    (toDivisor_cartierIndex_smul_nonneg hQ hD) hne
  refine ⟨D.intersectionNumber k sY C.idealSheaf.subschemeι hdim1 hQ,
    ⟨hC, hdim1, hQ, rfl⟩, ?_, ?_⟩
  · exact div_nonneg (by exact_mod_cast hnonneg) (Nat.cast_nonneg _)
  · change ((_ : ℤ) : ℚ) / (D.cartierIndex hQ : ℚ) = 0 ↔ _
    rw [div_eq_zero_iff, or_iff_left hmq, Int.cast_eq_zero, hzero, ← hr,
      Set.eq_empty_iff_forall_notMem]
    exact ⟨fun h x ⟨⟨c, hc⟩, hx⟩ => h c ((mem_supp_toDivisor_cartierIndex_smul_iff hQ _).2
        (hc ▸ hx)),
      fun h c hc => h _ ⟨⟨c, rfl⟩, (mem_supp_toDivisor_cartierIndex_smul_iff hQ _).1 hc⟩⟩

/-- **Local intersection numbers bound the product of multiplicities.** For effective divisors
`C`, `C'` on a smooth surface `Y` without common component through a closed point `q`,
`i_q(C, C') ≥ mult_q C · mult_q C'`. -/
@[mmp "lem_km4a_local_intersection_multiplicity_bound"]
theorem multiplicityAt_mul_le_localIntersectionNumber (hY : IsVariety k sY)
    (hsm : IsSmoothScheme sY) (hdim : topologicalKrullDim Y = 2) {q : Y}
    (hq : IsClosed ({q} : Set Y)) {C C' : Divisor Y} (hC : C.IsEffective) (hC' : C'.IsEffective)
    (hCC' : ∀ E ∈ C.support, E ∈ C'.support → q ∉ E.support) :
    C.multiplicityAt q * C'.multiplicityAt q ≤ (localIntersectionNumber sY q C C' : ℤ) :=
  SurfaceAux.multiplicityAt_mul_le sY hY hsm hdim hq hC hC' hCC'

end SmoothSurface

end MMP.Mori
