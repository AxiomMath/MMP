module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyLinear

/-!
# Negative powers of an ample invertible module on a curve have no sections

Let `C` be an integral proper curve over a field `k` and `ℳ` an ample invertible `𝒪_C`-module.
Then `Γ(C, ℳ^{⊗ n}) = 0` for every `n < 0`.

The degree of `ℳ` is positive ([Stacks, Tag 0B5X]), and the degree is additive on tensor
products, so `deg ℳ^{⊗ n} = n · deg ℳ < 0`. An invertible module on an integral proper curve
with a nonzero global section has nonnegative degree ([Stacks, Tag 0B40]).

## Main results

* `MMP.Mori.invertibleCurveDegree_tensorPowModule`: `deg ℳ^{⊗ n} = n · deg ℳ` for `n : ℤ`.
* `MMP.Mori.subsingleton_sections_tensorPowModule_of_isAmple_of_neg`: for `ℳ` ample on an
  integral proper curve, `Γ(C, ℳ^{⊗ n}) = 0` for all `n < 0`.

## Implementation notes

* `ℳ^{⊗ n}` for `n : ℤ` is `Stacks.Ample.tensorPowModule`, and ampleness is
  `Stacks.Ample.IsAmple`.

## References

* [The Stacks project][stacks-project], Tags 0B40 and 0B5X
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsProper f]

/-- **`deg ℳ^{⊗ m} = m · deg ℳ`** for natural `m`, on a proper scheme of dimension at most one
over a field. -/
private theorem invertibleCurveDegree_tensorPowModule_natCast (hdim : topologicalKrullDim C ≤ 1)
    (M : C.Modules) [Stacks.Ample.IsInvertibleModule C M] (m : ℕ) :
    invertibleCurveDegree k f hdim (Stacks.Ample.tensorPowModule C M (m : ℤ)) =
      (m : ℤ) * invertibleCurveDegree k f hdim M := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, zero_mul]
    exact invertibleCurveDegree_eq_zero_of_iso_unit k f hdim _
      (Stacks.Ample.tensorPowModuleZeroIso C M)
  | succ m ih =>
    have h1 := invertibleCurveDegree_eq_of_iso k f hdim
      (Stacks.Ample.tensorPowModuleAddIso C M (m : ℤ) 1)
    have h2 := invertibleCurveDegree_tensorSheaf_eq_add k f hdim
      (Stacks.Ample.tensorPowModule C M (m : ℤ)) (Stacks.Ample.tensorPowModule C M 1)
    have h3 := invertibleCurveDegree_eq_of_iso k f hdim (Stacks.Ample.tensorPowModuleOneIso C M)
    push_cast
    rw [← h1, h2, ih, h3]
    ring

/-- **`deg ℳ^{⊗ n} = n · deg ℳ`** for every integer `n`, on a proper scheme of dimension at most
one over a field. -/
theorem invertibleCurveDegree_tensorPowModule (hdim : topologicalKrullDim C ≤ 1)
    (M : C.Modules) [Stacks.Ample.IsInvertibleModule C M] (n : ℤ) :
    invertibleCurveDegree k f hdim (Stacks.Ample.tensorPowModule C M n) =
      n * invertibleCurveDegree k f hdim M := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact invertibleCurveDegree_tensorPowModule_natCast f hdim M m
  · have h1 := invertibleCurveDegree_eq_of_iso k f hdim
      (Stacks.Ample.tensorPowModuleAddIso C M (-(m : ℤ)) (m : ℤ))
    have h2 := invertibleCurveDegree_tensorSheaf_eq_add k f hdim
      (Stacks.Ample.tensorPowModule C M (-(m : ℤ))) (Stacks.Ample.tensorPowModule C M (m : ℤ))
    have h0 : invertibleCurveDegree k f hdim
        (Stacks.Ample.tensorPowModule C M (-(m : ℤ) + (m : ℤ))) = 0 := by
      rw [neg_add_cancel]
      exact invertibleCurveDegree_eq_zero_of_iso_unit k f hdim _
        (Stacks.Ample.tensorPowModuleZeroIso C M)
    rw [invertibleCurveDegree_tensorPowModule_natCast f hdim M m] at h2
    linarith

/-- **Negative powers of an ample invertible module on a curve have no global sections.** Let `C`
be an integral proper scheme of dimension one over a field and `ℳ` an ample invertible
`𝒪_C`-module. Then `Γ(C, ℳ^{⊗ n}) = 0` for every `n < 0`; in particular the dual `ℳ^{⊗ -1}`
has no nonzero global section. -/
theorem subsingleton_sections_tensorPowModule_of_isAmple_of_neg (f : C ⟶ Spec (.of k))
    [IsProper f] [IsIntegral C] (hdim : topologicalKrullDim C = 1) (M : C.Modules)
    [Stacks.Ample.IsInvertibleModule C M] (hM : Stacks.Ample.IsAmple C M) {n : ℤ} (hn : n < 0) :
    Subsingleton Γ(Stacks.Ample.tensorPowModule C M n, ⊤) := by
  have : IsCurve k f :=
    { toIsIntegral := inferInstance, toIsSeparated := inferInstance,
      toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance,
      topologicalKrullDim_eq_one := hdim }
  have hpos : 0 < invertibleCurveDegree k f hdim.le M :=
    invertibleCurveDegree_pos_of_isAmple_of_isCurve k f hdim.le M
      ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple C M).mpr hM)
  have hdeg := invertibleCurveDegree_tensorPowModule f hdim.le M n
  rw [← not_nontrivial_iff_subsingleton]
  intro hnt
  obtain ⟨t, ht⟩ := exists_ne (0 : Γ(Stacks.Ample.tensorPowModule C M n, ⊤))
  obtain ⟨s, hs⟩ := (bijective_sections_eval_top (Stacks.Ample.tensorPowModule C M n)).2 t
  have h0 : 0 ≤ invertibleCurveDegree k f hdim.le (Stacks.Ample.tensorPowModule C M n) :=
    invertibleCurveDegree_nonneg_of_eval_top_ne_zero k f hdim.le
      (hL := Stacks.Ample.isInvertibleModule_tensorPowModule C M n)
      (Stacks.Ample.tensorPowModule C M n) s (fun h0 => ht (hs.symm.trans h0))
  rw [hdeg] at h0
  exact (mul_neg_of_neg_of_pos hn hpos).not_ge h0

end MMP.Mori
