module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Chow.FieldSituation
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Positivity.NefTopIntersectionPositive
import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.NormalThreefoldSlice

/-!
# Numerical discrepancies of surface resolutions under point blow-ups

Let `f : Y ⟶ X` be a resolution of a normal surface `X` over an algebraically closed field `k`
of characteristic zero, with exceptional curves `E₁, …, E_r`, and let `a = ∑ aᵢ Eᵢ` solve the
numerical pull-back equations `∑ᵢ aᵢ (Eᵢ · Eⱼ) = ((K_Y + f⁻¹_* Δ) · Eⱼ)` of `(X, Δ)` on `f`.

* If every right-hand side `((K_Y + f⁻¹_* Δ) · Eⱼ)` is nonnegative, then every `aᵢ ≤ 0`. The
  exceptional curves are finitely many and their intersection matrix is negative definite with
  nonnegative off-diagonal entries; splitting `a = a⁺ + a⁻` gives `(a⁺)ᵗ b < 0` unless `a⁺ = 0`.
* Let `p ∈ Y` be a closed point, `π : Y' ⟶ Y` the blow-up of `p` and `F` its exceptional curve.
  The only `π`-exceptional curve is `F`: a curve contracted to a point other than `p` would be
  contracted by an isomorphism, and a curve inside `π⁻¹(p) = F` is `F`. Hence the
  `(π ≫ f)`-exceptional curves are the strict transforms `π⁻¹_* Eᵢ` together with `F`, and the
  vector `(a₁, …, a_r, 1 - mult_p Θ_{f,a})`, where `Θ_{f,a} = f⁻¹_* Δ - ∑ aᵢ Eᵢ` is the log
  pull-back, solves the numerical pull-back equations of `(X, Δ)` on `π ≫ f`. This is the step
  by which discrepancies are followed through a sequence of point blow-ups.
* For an effective `ℚ`-divisor `D` on the smooth surface `Y`, the strict transform `π⁻¹_* D` has
  multiplicity at most `mult_p D` at every point `q` of `F`. By linearity it suffices to treat a
  prime divisor `E` with strict transform `E'`; if `q ∈ E'` then `q` is closed and
  `mult_q E' ≤ i_q(F, E') ≤ (E' · F) = mult_p E`, the last equality coming from
  `π^*E = E' + (mult_p E) F`, `(π^*E · F) = 0` and `(F · F) = -1`.

## Main results

* `MMP.Mori.IsNumericalPullbackSolution.nonpos`: a solution of the numerical pull-back equations
  with nonnegative right-hand sides is `≤ 0`.
* `MMP.Mori.IsNumericalPullbackSolution.isNumericalPullbackSolution_blowUpToBase_comp`: the
  exceptional curves and the solution of the numerical pull-back equations after a point
  blow-up.
* `MMP.Threefold.Resolution.multiplicityAt_inverseTransformDivisor_blowUpToBase_le`:
  `mult_q (π⁻¹_* D) ≤ mult_p D` for every `q ∈ F`.

## Implementation notes

The vector `a ∈ ℚ^r` is the `ℚ`-divisor `∑ᵢ aᵢ Eᵢ` supported on the exceptional curves, as in
`MMP.Mori.IsNumericalPullbackSolution`, so `aᵢ ≤ 0` for all `i` is `a ≤ 0`, and the vector
`(a₁, …, a_r, c)` on `π ≫ f` is the `ℚ`-divisor `π⁻¹_* a + c F`. The hypothesis `bⱼ ≥ 0` is
stated for every value `b` that the intersection number `((K + f⁻¹_* Δ) · Eⱼ)` takes.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 4.1
  and the proofs of 4.5 and 4.7
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Mori

open MMP.Threefold.Resolution MMP.Flips

/-! ### Numerical discrepancies after a point blow-up -/

/-- The only curve contracted by the blow-up `π` of a closed point `p` of a surface is the
exceptional curve `F`. -/
private theorem isExceptionalCurve_blowUpToBase_iff {Y : Scheme.{u}} {p : Y}
    (hp : IsClosed ({p} : Set Y))
    [CompactSpace (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))]
    [IrreducibleSpace (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))]
    (hiso : IsIso (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ∣_
        (⟨{p}ᶜ, hp.isOpen_compl⟩ : Y.Opens)))
    (hdim : topologicalKrullDim (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) = 2)
    {F : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    (hFc : IsCurveIn F.idealSheaf)
    (C : (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).IdealSheafData) :
    IsExceptionalCurve (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) C ↔
      C = F.idealSheaf := by
  set π := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
  have hFmem : ∀ q, q ∈ (F.idealSheaf.support : Set _) ↔ π q = p :=
    mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hp hF
  constructor
  · rintro ⟨hC, x, hx⟩
    have := hC.1
    have hfx : ∀ y ∈ (C.support : Set _), π y = x := fun y hy ↦ by
      have : π.base y ∈ π.base '' (C.support : Set _) := ⟨y, hy, rfl⟩
      rw [hx] at this
      exact this
    obtain ⟨e, he, hecl⟩ := hC.exists_isGenericPoint
    obtain ⟨c, hccl, hec, hne⟩ := exists_isClosed_singleton_specializes hecl
    have hcC : c ∈ (C.support : Set _) := he ▸ specializes_iff_mem_closure.mp hec
    have heC : e ∈ (C.support : Set _) := he ▸ subset_closure rfl
    have hxp : x = p := by
      by_contra hxp
      have hV : ∀ y ∈ (C.support : Set _), π y ∈ (⟨{p}ᶜ, hp.isOpen_compl⟩ : Y.Opens) :=
        fun y hy ↦ by
          rw [hfx y hy]
          exact hxp
      have h1 : c ⤳ e := specializes_of_isIso_morphismRestrict π _ (hV c hcC) (hV e heC)
        (by rw [hfx c hcC, hfx e heC])
      exact hne (h1.antisymm hec).symm.eq
    have hsub : (C.support : Set _) ⊆ F.idealSheaf.support := fun y hy ↦
      (hFmem y).mpr ((hfx y hy).trans hxp)
    have := hFc.1
    have hCirr := isIrreducible_support_of_isIntegral C
    have hFirr := isIrreducible_support_of_isIntegral F.idealSheaf
    have heq : C.support = F.idealSheaf.support := by
      by_contra hne'
      have hCF : (C.support : Set _) ⊂ F.idealSheaf.support :=
        ⟨hsub, fun h ↦ hne' (Closeds.ext (Set.Subset.antisymm hsub (by exact h)))⟩
      have hcC' : ({c} : Set _) ⊂ C.support :=
        ⟨Set.singleton_subset_iff.mpr hcC,
          fun h ↦ hC.not_subsingleton (Set.subsingleton_singleton.anti h)⟩
      exact false_of_lt_lt_lt_of_topologicalKrullDim_le_two hdim.le
        (a := ⟨{c}, isIrreducible_singleton, hccl⟩) (b := ⟨C.support, hCirr, C.support.isClosed⟩)
        (c := ⟨F.idealSheaf.support, hFirr, F.idealSheaf.support.isClosed⟩)
        (d := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩) hcC' hCF
        (Set.ssubset_univ_iff.mpr (support_ne_univ_of_isCurveIn hdim hFc))
    rw [← vanishingIdeal_support_eq_self C, ← vanishingIdeal_support_eq_self F.idealSheaf, heq]
  · rintro rfl
    refine ⟨hFc, p, Set.Subset.antisymm ?_ ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact (hFmem y).mp hy
    · rintro _ rfl
      obtain ⟨e, he, -⟩ := hFc.exists_isGenericPoint
      have heF : e ∈ (F.idealSheaf.support : Set _) := he ▸ subset_closure rfl
      exact ⟨e, heF, (hFmem e).mp heF⟩

/-- A divisor whose prime divisors have no transform equal to `P` has a zero coefficient at `P`
in its birational transform. -/
private theorem inverseTransformDivisor_apply_eq_zero {R : Type*} [AddCommMonoid R]
    {Y Y' : Scheme} {g : Y' ⟶ Y} {P : MMP.Mori.PrimeDivisor Y'}
    (hP : ∀ E : MMP.Mori.PrimeDivisor Y, inverseTransformPrimeDivisor g E ≠ some P)
    (D : DivisorWithCoeffs R Y) : inverseTransformDivisor g D P = 0 := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D₁ D₂ h₁ h₂ => rw [map_add, Finsupp.add_apply, h₁, h₂, add_zero]
  | single E r =>
    rw [inverseTransformDivisor_single]
    cases h : inverseTransformPrimeDivisor g E with
    | none => rfl
    | some C =>
      have hCP : C ≠ P := fun hCP => hP E (h.trans (congrArg some hCP))
      simp [hCP]

/-- The coefficient of `h⁻¹_* a` at a prime divisor `P` of `Y'`. -/
private theorem inverseTransformDivisor_apply {R : Type*} [AddCommMonoid R] {Y Y' : Scheme}
    (h : Y' ⟶ Y) (a : DivisorWithCoeffs R Y)
    [DecidableEq (Option (MMP.Mori.PrimeDivisor Y'))] (P : MMP.Mori.PrimeDivisor Y') :
    inverseTransformDivisor h a P =
      ∑ E ∈ a.support, if inverseTransformPrimeDivisor h E = some P then a E else 0 := by
  classical
  conv_lhs => rw [← Finsupp.sum_single a]
  rw [Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [inverseTransformDivisor_single]
  cases inverseTransformPrimeDivisor h E with
  | none => simp
  | some C => simp [Finsupp.single_apply]

/-- `h⁻¹_* E = C` as soon as the ideal sheaf of `C` is that of the birational transform of `E`. -/
private theorem inverseTransformPrimeDivisor_eq_some_of_idealSheaf_eq {Y Y' : Scheme}
    {h : Y' ⟶ Y} {E : MMP.Mori.PrimeDivisor Y} {C : MMP.Mori.PrimeDivisor Y'}
    (hC : C.idealSheaf = inverseTransformIdeal h E.idealSheaf.support) :
    inverseTransformPrimeDivisor h E = some C := by
  refine inverseTransformPrimeDivisor_eq_some_iff.2 ⟨?_, hC⟩
  by_contra hne
  obtain ⟨z⟩ : Nonempty C.idealSheaf.subscheme := C.integral.nonempty
  have hz : C.idealSheaf.subschemeι z ∈ (C.idealSheaf.support : Set Y') := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  have hz' : (C.idealSheaf.support : Set Y').Nonempty := ⟨_, hz⟩
  rw [hC, support_inverseTransformIdeal] at hz'
  obtain ⟨y, hy⟩ := hz'
  have hempty : (E.support ∩ (biregularLocus h : Set Y)) = ∅ :=
    Set.not_nonempty_iff_eq_empty.1 hne
  have : (inverseTransform h E.idealSheaf.support : Set Y') = ∅ := by
    change closure (h.base ⁻¹' (E.support ∩ (biregularLocus h : Set Y))) = ∅
    rw [hempty, Set.preimage_empty, closure_empty]
  rw [this] at hy
  exact hy

/-- The coefficient of `h⁻¹_* a` at the transform of an `f`-exceptional curve `E` is `a E`, when
`a` is supported on `f`-exceptional curves. -/
private theorem inverseTransformDivisor_apply_of_idealSheaf_eq {X Y Y' : Scheme}
    {f : Y ⟶ X} {h : Y' ⟶ Y} {a : QDivisor Y}
    (hinj : ∀ E E' : Y.IdealSheafData, IsExceptionalCurve f E → IsExceptionalCurve f E' →
      inverseTransformIdeal h E.support = inverseTransformIdeal h E'.support → E = E')
    (ha : ∀ E ∈ a.support, IsExceptionalCurve f E.idealSheaf)
    {E : MMP.Mori.PrimeDivisor Y} {C : MMP.Mori.PrimeDivisor Y'}
    (hE : IsExceptionalCurve f E.idealSheaf)
    (hC : C.idealSheaf = inverseTransformIdeal h E.idealSheaf.support) :
    inverseTransformDivisor h a C = a E := by
  classical
  rw [inverseTransformDivisor_apply]
  have key : ∀ E' ∈ a.support, (if inverseTransformPrimeDivisor h E' = some C then a E' else 0) =
      if E' = E then a E' else 0 := by
    intro E' hE'
    by_cases hEE : E' = E
    · subst hEE
      rw [ite_eq_left (inverseTransformPrimeDivisor_eq_some_of_idealSheaf_eq hC), ite_eq_left rfl]
    · rw [ite_eq_right hEE, ite_eq_right]
      exact fun hs ↦ hEE (PrimeDivisor.ext_idealSheaf (hinj _ _ (ha E' hE') hE
        ((inverseTransformPrimeDivisor_eq_some_iff.1 hs).2.symm.trans hC)))
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq']
  by_cases hm : E ∈ a.support
  · rw [ite_eq_left hm]
  · rw [ite_eq_right hm, Finsupp.notMem_support_iff.1 hm]

/-- `h⁻¹_* a` is supported on `(h ≫ f)`-exceptional curves, when `a` is supported on
`f`-exceptional curves. -/
private theorem isExceptionalCurve_of_mem_support_inverseTransformDivisor {X Y Y' : Scheme}
    {f : Y ⟶ X} {h : Y' ⟶ Y} {a : QDivisor Y}
    (htr : ∀ E : Y.IdealSheafData, IsExceptionalCurve f E →
      IsExceptionalCurve (h ≫ f) (inverseTransformIdeal h E.support))
    (ha : ∀ E ∈ a.support, IsExceptionalCurve f E.idealSheaf)
    {P : MMP.Mori.PrimeDivisor Y'} (hP : P ∈ (inverseTransformDivisor h a).support) :
    IsExceptionalCurve (h ≫ f) P.idealSheaf := by
  classical
  rw [Finsupp.mem_support_iff, inverseTransformDivisor_apply] at hP
  obtain ⟨E, hE, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP
  have hs : inverseTransformPrimeDivisor h E = some P := by
    by_contra hs
    exact hne (ite_eq_right hs)
  rw [(inverseTransformPrimeDivisor_eq_some_iff.1 hs).2]
  exact htr _ (ha E hE)

/-- The generic point of a prime divisor lies in its support. -/
private theorem genericPoint_mem_support {Y : Scheme} (P : MMP.Mori.PrimeDivisor Y) :
    P.genericPoint ∈ (P.idealSheaf.support : Set Y) := by
  change P.genericPoint ∈ P.support
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- On a surface, the generic point of a prime divisor is not a closed point. -/
private theorem not_isClosed_singleton_genericPoint {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} (hY : MMP.Mori.IsVariety k sY) (hYd : topologicalKrullDim Y = 2)
    (E : MMP.Mori.PrimeDivisor Y) : ¬ IsClosed ({E.genericPoint} : Set Y) := fun hc ↦
  (isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hY hYd E).not_subsingleton <| by
    change (E.support : Set Y).Subsingleton
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    change (closure {E.genericPoint}).Subsingleton
    rw [hc.closure_eq]
    exact Set.subsingleton_singleton

/-- On a surface, a prime divisor whose generic point lies on a curve `E` is `E`. -/
private theorem idealSheaf_eq_of_genericPoint_mem {k : Type u} [Field k] {Y : Scheme.{u}}
    [CompactSpace Y] {sY : Y ⟶ Spec (.of k)} (hY : MMP.Mori.IsVariety k sY)
    (hYd : topologicalKrullDim Y = 2) (Q : MMP.Mori.PrimeDivisor Y) {E : Y.IdealSheafData}
    (hE : IsCurveIn E) (hQE : Q.genericPoint ∈ (E.support : Set Y)) : Q.idealSheaf = E := by
  have : IsIntegral Y := hY.toIsIntegral
  have := hE.1
  have := Q.integral
  have hsupp : Q.idealSheaf.support = E.support := Closeds.ext <| by
    change (Q.support : Set Y) = _
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_singleton_eq_of_not_isClosed hYd.le
      (not_isClosed_singleton_genericPoint hY hYd Q) (isIrreducible_support_of_isIntegral E)
      E.support.isClosed hQE (support_ne_univ_of_isCurveIn hYd hE)
  rw [← vanishingIdeal_support_eq_self Q.idealSheaf, ← vanishingIdeal_support_eq_self E, hsupp]

/-- Away from the exceptional curve `F`, a prime divisor `P` of the blow-up that is the strict
transform of a curve `E'` of `Y` is the strict transform of a prime divisor of `Y` with ideal
sheaf `E'`. -/
private theorem exists_primeDivisor_of_idealSheaf_eq_inverseTransformIdeal {k : Type u} [Field k]
    {Y : Scheme.{u}} [CompactSpace Y] {sY : Y ⟶ Spec (.of k)} (hYv : MMP.Mori.IsVariety k sY)
    (hYd : topologicalKrullDim Y = 2) {p : Y} (hp : IsClosed ({p} : Set Y))
    (hiso : IsIso (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ∣_
        (⟨{p}ᶜ, hp.isOpen_compl⟩ : Y.Opens)))
    {F : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    {P : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))}
    (hPF : P ≠ F) {E' : Y.IdealSheafData} (hE' : IsCurveIn E')
    (hPE' : P.idealSheaf = inverseTransformIdeal
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) E'.support) :
    ∃ Q : MMP.Mori.PrimeDivisor Y, Q.idealSheaf = E' ∧ P.idealSheaf = inverseTransformIdeal
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) Q.idealSheaf.support := by
  set π := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
  have hFmem : ∀ q, q ∈ (F.idealSheaf.support : Set _) ↔ π q = p :=
    mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hp hF
  have hπp : π P.genericPoint ≠ p := by
    intro h
    have heq := F.eq_genericPoint_of_mem_support ((hFmem _).mpr h) P.coheight_genericPoint
    exact hPF (by
      rw [(PrimeDivisor.eq_ofCoheightOne_iff P P.coheight_genericPoint).mpr rfl,
        (PrimeDivisor.eq_ofCoheightOne_iff F P.coheight_genericPoint).mpr heq])
  have hV : π P.genericPoint ∈ biregularLocus π :=
    le_biregularLocus (V := ⟨{p}ᶜ, hp.isOpen_compl⟩) hiso hπp
  have hcoh : Order.coheight (π P.genericPoint) = 1 :=
    (MMP.Positivity.coheight_map_of_mem_biregularLocus π hV).trans P.coheight_genericPoint
  set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
  have hQg : Q.genericPoint = π P.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hQP : inverseTransformPrimeDivisor π Q = some P :=
    inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hQg.symm hV
  have h1 : P.genericPoint ∈ (inverseTransform π E'.support : Set _) := by
    rw [← support_inverseTransformIdeal, ← hPE']
    exact genericPoint_mem_support P
  have hcl : (inverseTransform π E'.support : Set _) ⊆ π.base ⁻¹' (E'.support : Set Y) :=
    closure_minimal (fun _ hx => hx.1) (E'.support.isClosed.preimage π.continuous)
  exact ⟨Q, idealSheaf_eq_of_genericPoint_mem hYv hYd Q hE'
    (show Q.genericPoint ∈ (E'.support : Set Y) from hQg ▸ hcl h1),
    (inverseTransformPrimeDivisor_eq_some_iff.1 hQP).2⟩

/-- The discrepancy of the exceptional curve `F` of the blow-up of `p` over `(X, Δ)` is
`1 - mult_p Θ`, with `Θ = logPullback f Δ a`. -/
private theorem eq_one_sub_multiplicityAt_of_isDiscrepancy
    {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hf : IsSmoothResolution sX f)
    {K : Divisor Y} {Δ : QDivisor X} {a : QDivisor Y}
    {p : Y} (hp : IsClosed ({p} : Set Y))
    [IsLocallyNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))]
    [IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))]
    [IsIntegral (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))]
    [CompactSpace (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))]
    [LocallyOfFiniteType (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ f ≫ sX)]
    {F : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    (hYv : MMP.Mori.IsVariety k (f ≫ sX)) (hYs : IsSmoothScheme (f ≫ sX))
    (hYd : topologicalKrullDim Y = 2)
    (hh : IsSmoothResolution (f ≫ sX)
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)))
    (hnoF : ∀ E : MMP.Mori.PrimeDivisor Y, inverseTransformPrimeDivisor
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) E ≠ some F)
    {n : ℕ} {q : ℚ}
    (hn : IsDiscrepancy (f ≫ sX) n K (logPullback f Δ a)
      ⟨_, blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩),
        (hh.isNormalVariety (hf.isNormalVariety hX).1).1, hh.isBirationalMorphism, F⟩ q) :
    q = 1 - (logPullback f Δ a).multiplicityAt p := by
  classical
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hf.isIntegral
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : LocallyOfFiniteType (f ≫ sX) := hYv.toLocallyOfFiniteType
  have hK := hn.2.1
  have hn2 : n = 2 := by
    have := hK.topologicalKrullDim_eq
    rw [hYd] at this
    exact_mod_cast this.symm
  subst hn2
  have hYnv : IsNormalVariety k (f ≫ sX) := ⟨hYv, inferInstance⟩
  obtain ⟨σ, hσ0, hσ⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hYnv hK
  obtain rfl : divisorOfForm σ = K := Finsupp.ext hσ
  have hQ := MMP.Fourfold.isQCartier_of_isSmoothScheme hYs
    (Divisor.toQDivisor (divisorOfForm σ) + logPullback f Δ a)
  have h2 := isDiscrepancy_coeff_divisorOfForm_sub_pullback hYnv σ hσ0 hK (logPullback f Δ a)
    hQ (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    (hh.isNormalVariety (hf.isNormalVariety hX).1).1 hh.isBirationalMorphism F
  rw [hn.eq h2]
  have hsm := isSmoothBlowup_vanishingIdeal_singleton (f ≫ sX) hYs hp
  have hirr := isIrreducible_support_vanishingIdeal_singleton hp
  have hEF : ∀ h, MMP.Resolution.exceptionalPrimeDivisor (f ≫ sX)
      (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) hsm hirr h = F := fun h =>
    PrimeDivisor.ext_idealSheaf (by rw [MMP.Resolution.exceptionalPrimeDivisor_idealSheaf, hF])
  rw [divisorOfForm_pullbackRationalPluriForms_blowUpToBase _ (f ≫ sX) hsm hirr (c := 2)
    (codimension_vanishingIdeal_singleton_eq_two hYv hYd hp).symm (by norm_num) (d := 2)
    (by exact_mod_cast hYd) σ hσ0, hEF,
    Divisor.IsPullback.pullback_eq _ (isPullback_blowUp_singleton hYv hYs hYd hp hF _ _),
    pullback_qDivisor_blowUp_singleton hYv hYs hYd hp hF]
  unfold DivisorWithCoeffs.coeff
  simp only [map_add, map_zsmul, ← inverseTransformDivisor_toQDivisor, toQDivisor_single,
    Finsupp.sub_apply, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
    DivisorWithCoeffs.multiplicityAt_add, multiplicityAt_toQDivisor,
    inverseTransformDivisor_apply_eq_zero
      (g := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) hnoF]
  ring

/-- The vector `(a, 1 - mult_p Θ)` solves the numerical pull-back equations on `π ≫ f`. -/
private theorem isNumericalPullbackSolution_comp_blowUpToBase
    {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    {K : Divisor Y} {Δ : QDivisor X} {a : QDivisor Y}
    (ha : IsNumericalPullbackSolution sX f K Δ a)
    {p : Y} (hp : IsClosed ({p} : Set Y))
    [QuasiCompact ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ f) ≫ sX)]
    [IsLocallyNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))]
    [IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))]
    [CompactSpace (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))]
    [IrreducibleSpace (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))]
    {F : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    {K' : Divisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))}
    (hK' : ∃ n : ℕ, K'.IsCanonicalDivisor
      ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ f) ≫ sX) n)
    (hYv : MMP.Mori.IsVariety k (f ≫ sX)) (hYs : IsSmoothScheme (f ≫ sX))
    (hYd : topologicalKrullDim Y = 2)
    (hh : IsSmoothResolution (f ≫ sX)
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)))
    (hiso : IsIso (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ∣_
        (⟨{p}ᶜ, hp.isOpen_compl⟩ : Y.Opens)))
    (hvar : MMP.Mori.IsVariety k
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ f ≫ sX))
    (hπ : ∀ C, IsExceptionalCurve (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
      C ↔ C = F.idealSheaf) :
    IsNumericalPullbackSolution sX
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ f) K' Δ
      (inverseTransformDivisor (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) a +
        Finsupp.single F (1 - (logPullback f Δ a).multiplicityAt p)) := by
  classical
  set π := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
  have hf := ha.1
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hf.isIntegral
  have : IsIntegral (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) := hvar.toIsIntegral
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : LocallyOfFiniteType (f ≫ sX) := hYv.toLocallyOfFiniteType
  have : LocallyOfFiniteType (π ≫ f ≫ sX) := hvar.toLocallyOfFiniteType
  obtain ⟨-, htr, hinj, hiff⟩ :=
    isSmoothResolution_comp_and_isExceptionalCurve_comp_iff hX hdim hf hh
  obtain ⟨b, hb, hbE, hbF⟩ := ha.exists_isNumericalPullbackSolution_comp hX hdim hf hh hK'
  have hFmem : ∀ q, q ∈ (F.idealSheaf.support : Set _) ↔ π q = p :=
    mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hp hF
  have hFπ : IsExceptionalCurve π F.idealSheaf := (hπ _).mpr rfl
  have hnoF : ∀ E : MMP.Mori.PrimeDivisor Y, inverseTransformPrimeDivisor π E ≠ some F := by
    intro E hE
    obtain ⟨hη, -⟩ := map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hE
    rw [(hFmem _).mp (genericPoint_mem_support F)] at hη
    exact not_isClosed_singleton_genericPoint hYv hYd E (hη ▸ hp)
  have hbT : b = inverseTransformDivisor π a +
      Finsupp.single F (1 - (logPullback f Δ a).multiplicityAt p) := by
    ext P
    unfold DivisorWithCoeffs.coeff
    rw [Finsupp.add_apply]
    by_cases hPF : P = F
    · rw [hPF, inverseTransformDivisor_apply_eq_zero hnoF, zero_add, Finsupp.single_eq_same]
      obtain ⟨n, hn⟩ := hbF F hFπ
      exact eq_one_sub_multiplicityAt_of_isDiscrepancy hX hf hp hF hYv hYs hYd hh hnoF hn
    · rw [Finsupp.single_apply, ite_eq_right (Ne.symm hPF), add_zero]
      by_cases hPe : IsExceptionalCurve (π ≫ f) P.idealSheaf
      · obtain ⟨Q, hQe, hQP⟩ : ∃ Q : MMP.Mori.PrimeDivisor Y, IsExceptionalCurve f Q.idealSheaf ∧
            P.idealSheaf = inverseTransformIdeal π Q.idealSheaf.support := by
          rcases (hiff _).1 hPe with ⟨E', hE', hPE'⟩ | hPπ
          · obtain ⟨Q, rfl, hQP⟩ :=
              exists_primeDivisor_of_idealSheaf_eq_inverseTransformIdeal hYv hYd hp hiso hF hPF
                hE'.1 hPE'
            exact ⟨Q, hE', hQP⟩
          · exact absurd (PrimeDivisor.ext_idealSheaf ((hπ _).mp hPπ)) hPF
        rw [hbE Q P hQe hQP, inverseTransformDivisor_apply_of_idealSheaf_eq hinj ha.2.2.1 hQe hQP]
      · rw [Finsupp.notMem_support_iff.mp (fun h => hPe (hb.2.2.1 P h)),
          Finsupp.notMem_support_iff.mp (fun h => hPe
            (isExceptionalCurve_of_mem_support_inverseTransformDivisor (fun E hE => (htr E hE).1)
              ha.2.2.1 h))]
  rwa [← hbT]

/-- **Numerical discrepancies after a point blow-up** (KM, proofs of 4.5, 4.7). Let `f : Y ⟶ X` be
a resolution of a normal surface `X` over an algebraically closed field `k` of characteristic zero,
and `a` a solution of the numerical pull-back equations of `(X, Δ)` on `f` for a canonical divisor
`K` of `Y`. Let `p ∈ Y` be a closed point, `π : Y' ⟶ Y` the blow-up of `p` and `F` the exceptional
curve, the prime divisor of `Y'` with ideal sheaf `exceptionalIdeal`. Then the
`(π ≫ f)`-exceptional curves are exactly the strict transforms `π⁻¹_* E` of the `f`-exceptional
curves `E` and `F`; and for any canonical divisor `K'` of `Y'`, the `ℚ`-divisor
`π⁻¹_* a + (1 - mult_p Θ) F`, with `Θ = logPullback f Δ a`, solves the numerical pull-back
equations of `(X, Δ)` on `π ≫ f`. -/
@[mmp "lem_km4a_numerical_discrepancy_blowup"]
public theorem IsNumericalPullbackSolution.isNumericalPullbackSolution_blowUpToBase_comp
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    {K : Divisor Y} {Δ : QDivisor X} {a : QDivisor Y}
    (ha : IsNumericalPullbackSolution sX f K Δ a)
    {p : Y} (hp : IsClosed ({p} : Set Y)) :
    haveI hYs : IsSmoothScheme (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫
        f ≫ sX) :=
      isSmoothScheme_blowUp_singleton (ha.1.isNormalVariety hX).1.1 ha.1.isSmoothScheme
        ((ha.1.isNormalVariety hX).2.1.trans hdim) hp
    haveI : IsLocallyNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) :=
      (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
    haveI : IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) :=
      (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
    haveI : QuasiCompact
        ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ f) ≫ sX) := by
      rw [Category.assoc]
      exact (isVariety_blowUp_singleton (ha.1.isNormalVariety hX).1.1
        ((ha.1.isNormalVariety hX).2.1.trans hdim) hp).toQuasiCompact
    ∀ {F : PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))},
    F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) →
    ∀ {K' : Divisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))},
    (∃ n : ℕ, K'.IsCanonicalDivisor
      ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ f) ≫ sX) n) →
    (∀ C : (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).IdealSheafData,
      IsExceptionalCurve (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ f) C ↔
        (∃ E : Y.IdealSheafData, IsExceptionalCurve f E ∧
          C = inverseTransformIdeal
            (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) E.support) ∨
          C = F.idealSheaf) ∧
      IsNumericalPullbackSolution sX
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ f) K' Δ
        (inverseTransformDivisor (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) a +
          Finsupp.single F (1 - (logPullback f Δ a).multiplicityAt p)) := by
  intro F hF K' hK'
  have hf := ha.1
  obtain ⟨hYv, hdimY, -⟩ := hf.isNormalVariety hX
  have hYd : topologicalKrullDim Y = 2 := hdimY.trans hdim
  have : LocallyOfFiniteType (f ≫ sX) := hYv.1.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation (f ≫ sX) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr ‹_›
  have : Smooth (f ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).mp hf.isSmoothScheme
  obtain ⟨hvar, -, hdim', -, hbir, hiso, -⟩ :=
    isProjective_blowUpToBase_vanishingIdeal_singleton_and_isMinusOneCurve (f ≫ sX) hYv.1 hYd hp
  have hYs' := isSmoothScheme_blowUp_singleton hYv.1 hf.isSmoothScheme hYd hp
  have hh : IsSmoothResolution (f ≫ sX)
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) :=
    ⟨inferInstance, hbir, hYs'⟩
  have : IsLocallyNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) :=
    (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs').1
  have : IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) :=
    (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs').2
  have : QuasiCompact
      ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ f) ≫ sX) := by
    rw [Category.assoc]
    exact hvar.toQuasiCompact
  have hiff := (isSmoothResolution_comp_and_isExceptionalCurve_comp_iff hX hdim hf hh).2.2.2
  have : CompactSpace (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) :=
    QuasiCompact.compactSpace_of_compactSpace
      ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ f) ≫ sX)
  have : IrreducibleSpace (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) := by
    have := hvar.toIsIntegral
    infer_instance
  have hπ := isExceptionalCurve_blowUpToBase_iff hp hiso hdim' hF
    (isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hvar hdim' F)
  exact ⟨fun C ↦ (hiff C).trans (or_congr Iff.rfl (hπ C)),
    isNumericalPullbackSolution_comp_blowUpToBase hX hdim ha hp hF hK' hYv.1 hf.isSmoothScheme
      hYd hh hiso hvar hπ⟩

/-! ### Nef numerical pull-backs have nonpositive coefficients -/

section Nonpos

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- A resolution of a normal surface has finitely many exceptional curves. -/
private theorem finite_setOf_isExceptionalCurve
    {sX : X ⟶ Spec (.of k)} {f : Y ⟶ X} [IsLocallyNoetherian Y] [CompactSpace Y]
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsSmoothResolution sX f) :
    {E : MMP.Mori.PrimeDivisor Y | IsExceptionalCurve f E.idealSheaf}.Finite := by
  obtain ⟨S, -, -, -, ⟨hT, -⟩, hexc, -⟩ :=
    exists_finite_isIso_and_isExceptionalCurve_iff hX hdim hf
  have : IsNoetherian Y := ⟨⟩
  obtain ⟨𝒮, h𝒮, h𝒮c, h𝒮i, h𝒮eq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  have hmem : ∀ E : MMP.Mori.PrimeDivisor Y,
      IsExceptionalCurve f E.idealSheaf → E.support ∈ 𝒮 := by
    intro E hE
    obtain ⟨-, hmax⟩ := (hexc _).1 hE
    obtain ⟨z, hz, hsub⟩ := (isIrreducible_iff_sUnion_isClosed.1 hmax.prop.1) h𝒮.toFinset
      (fun z hz => h𝒮c z (h𝒮.mem_toFinset.1 hz))
      (by rw [h𝒮.coe_toFinset, ← h𝒮eq]; exact hmax.prop.2)
    have hz' := h𝒮.mem_toFinset.1 hz
    have hle : z ⊆ f.base ⁻¹' S := h𝒮eq ▸ Set.subset_sUnion_of_mem hz'
    have : E.support = z := le_antisymm hsub (hmax.2 ⟨h𝒮i z hz', hle⟩ hsub)
    exact this ▸ hz'
  refine (h𝒮.preimage ?_).subset hmem
  intro E _ E' _ h
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  have h' : closure ({E.genericPoint} : Set Y) = closure {E'.genericPoint} := by
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact h
  exact (inseparable_iff_closure_eq.2 h').eq

/-- An exceptional curve of a resolution of a normal surface is a proper curve of `Y`, with the
generic point of the curve, contracted by `f`. -/
private theorem exists_properCurve
    {sX : X ⟶ Spec (.of k)} {f : Y ⟶ X} [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsSmoothResolution sX f) (E : MMP.Mori.PrimeDivisor Y)
    (hE : IsExceptionalCurve f E.idealSheaf) :
    ∃ C : ProperCurve (f ≫ sX), C.point = E.genericPoint ∧ C.IsContractedBy f := by
  obtain ⟨S, -, -, -, ⟨hT, _⟩, hexc, -⟩ :=
    exists_finite_isIso_and_isExceptionalCurve_iff hX hdim hf
  have h := vanishingIdeal_closure_genericPoint_eq_idealSheaf E
  have hcl : closure ({E.genericPoint} : Set Y) = E.support :=
    (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have hsub : E.support ⊆ f.base ⁻¹' S := ((hexc _).1 hE).2.prop.2
  have hp : IsProper (E.idealSheaf.subschemeι ≫ f ≫ sX) := by
    set T := Scheme.IdealSheafData.vanishingIdeal ⟨f.base ⁻¹' S, hT⟩
    have hle : T.subschemeι.ker ≤ E.idealSheaf.subschemeι.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι, ← h]
      exact Scheme.IdealSheafData.vanishingIdeal_antimono (by
        change closure ({E.genericPoint} : Set Y) ⊆ f.base ⁻¹' S
        rw [hcl]; exact hsub)
    let l := IsClosedImmersion.lift T.subschemeι E.idealSheaf.subschemeι hle
    have hl : l ≫ T.subschemeι = E.idealSheaf.subschemeι := IsClosedImmersion.lift_fac _ _ hle
    have : IsProper (l ≫ T.subschemeι) := by rw [hl]; infer_instance
    have : IsProper l := IsProper.of_comp l T.subschemeι
    rw [← hl, Category.assoc]
    infer_instance
  obtain ⟨x, hx⟩ := hE.2
  refine ⟨⟨E.genericPoint, ⟨?_, ?_⟩⟩, rfl, fun y hy => ?_⟩
  · change topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal _).subscheme = 1
    rw [h]; exact hE.1.2
  · change IsProper ((Scheme.IdealSheafData.vanishingIdeal _).subschemeι ≫ f ≫ sX)
    rw [h]; exact hp
  · change y ∈ closure ({E.genericPoint} : Set Y) at hy
    rw [hcl] at hy
    have h1 : f y ∈ ({x} : Set X) := hx ▸ ⟨y, hy, rfl⟩
    have h2 : f E.genericPoint ∈ ({x} : Set X) :=
      hx ▸ ⟨E.genericPoint, (hcl ▸ subset_closure rfl : E.genericPoint ∈ E.support), rfl⟩
    change f y = f E.genericPoint
    rw [Set.mem_singleton_iff.1 h1, Set.mem_singleton_iff.1 h2]

/-- The numerical pull-back equations in matrix form: if `E₁, …, E_n` enumerate the exceptional
curves and `Cⱼ` is a proper curve with the generic point of `Eⱼ`, then
`∑ᵢ aᵢ (Eᵢ · Cⱼ)` is an intersection number of `K_Y + f⁻¹_* Δ` with `Eⱼ`. -/
private theorem isIntersectionNumber_sum_mul
    {sX : X ⟶ Spec (.of k)} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] {K : Divisor Y} {Δ : QDivisor X} {a : QDivisor Y}
    (ha : IsNumericalPullbackSolution sX f K Δ a) (hsm : IsSmoothScheme (f ≫ sX)) {n : ℕ}
    (E : Fin n ↪ MMP.Mori.PrimeDivisor Y)
    (hexc : ∀ F, IsExceptionalCurve f F.idealSheaf ↔ F ∈ Set.range E)
    (C : Fin n → ProperCurve (f ≫ sX)) (hC : ∀ i, (C i).point = (E i).genericPoint) (j : Fin n) :
    IsIntersectionNumber (f ≫ sX) (Divisor.toQDivisor K + inverseTransformDivisor f Δ)
      (E j).idealSheaf (∑ i, a (E i) *
        (Divisor.toQDivisor (Finsupp.single (E i) 1)).intersectionNumber k (f ≫ sX) (C j).ι
          (C j).dim_le (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm (E i))) := by
  classical
  obtain ⟨-, -, hs, heq⟩ := ha
  obtain ⟨c, b, h1, h2, h3⟩ := heq (E j) ((hexc _).2 ⟨j, rfl⟩)
  convert h2
  rw [← h3, Finset.sum_subset (s₂ := Finset.univ.map E) (fun F hF => ?_) (fun F _ hF => ?_),
    Finset.sum_map]
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : E i ∈ a.support
    · have := isIntersectionNumber_of_properCurve _
        (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm (E i)) (C j) (E j) (hC j)
      nth_rw 1 [show Divisor.toQDivisor (Finsupp.single (E i) 1) = Finsupp.single (E i) 1 by
        simpa using toQDivisor_single (E i) 1] at this
      rw [(h1 _ hi).unique this]
    · simp [Finsupp.notMem_support_iff.1 hi]
  · obtain ⟨i, rfl⟩ := (hexc F).1 (hs F hF)
    exact Finset.mem_map_of_mem _ (Finset.mem_univ i)
  · rw [Finsupp.notMem_support_iff.1 hF, zero_mul]

/-- **Nef numerical pull-backs have nonpositive coefficients.** Let `X` be a normal surface over
an algebraically closed field `k` of characteristic zero, `f : Y ⟶ X` a resolution, `K` a canonical
divisor of `Y` and `Δ` a `ℚ`-divisor on `X`. If `((K + f⁻¹_* Δ) · Eⱼ) ≥ 0` for every
`f`-exceptional curve `Eⱼ`, then the solution `a = ∑ aᵢ Eᵢ` of the numerical pull-back equations
`∑ᵢ aᵢ (Eᵢ · Eⱼ) = ((K + f⁻¹_* Δ) · Eⱼ)` satisfies `a ≤ 0`, i.e. every `aᵢ ≤ 0`. -/
@[mmp "lem_mmp_foundation_algebraic_surface_nef_coefficients_nonpositive"]
public theorem IsNumericalPullbackSolution.nonpos [IsAlgClosed k] [CharZero k]
    {sX : X ⟶ Spec (.of k)} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    {K : Divisor Y} {Δ : QDivisor X} {a : QDivisor Y}
    (ha : IsNumericalPullbackSolution sX f K Δ a)
    (hb : ∀ Ej : PrimeDivisor Y, IsExceptionalCurve f Ej.idealSheaf → ∀ b : ℚ,
      IsIntersectionNumber (f ≫ sX) (Divisor.toQDivisor K + inverseTransformDivisor f Δ)
        Ej.idealSheaf b → 0 ≤ b) :
    a ≤ 0 := by
  have hf := ha.1
  have hsm := hf.isSmoothScheme
  obtain ⟨hYn, hdimY, -⟩ := hf.isNormalVariety hX
  have : IsProper f := hf.isProper
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  obtain ⟨n, E, hErange⟩ := (finite_setOf_isExceptionalCurve hX hdim hf).fin_embedding
  have hexc : ∀ F : MMP.Mori.PrimeDivisor Y, IsExceptionalCurve f F.idealSheaf ↔ F ∈ Set.range E :=
    fun F => by
      rw [hErange]
      rfl
  choose C hC hCc using fun i => exists_properCurve hX hdim hf (E i) ((hexc _).2 ⟨i, rfl⟩)
  have hle := MMP.Threefold.Mori.coeff_nonpos_of_negDef_of_intersectionNumber_nonneg
    hYn.1 hsm (hdimY.trans hdim) E E.injective C hC (fun i => (a (E i) : ℝ))
    (MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isBirationalMorphism
      hYn.1 hsm (hdimY.trans hdim) hX.1 rfl hf.isBirationalMorphism E E.injective C hC hCc)
    fun j => by
      exact_mod_cast hb (E j) ((hexc _).2 ⟨j, rfl⟩) _
        (isIntersectionNumber_sum_mul ha hsm E hexc C hC j)
  intro F
  by_cases hF : F ∈ Set.range E
  · obtain ⟨i, rfl⟩ := hF
    exact_mod_cast hle i
  · simp [Finsupp.notMem_support_iff.1 fun h => hF ((hexc F).1 (ha.2.2.1 F h))]

end Nonpos

end MMP.Mori

namespace MMP.Threefold.Resolution

open MMP.Mori

/-! ### Multiplicities of strict transforms along the exceptional curve -/

/-- In a Jacobson space, every point of a finite closed set is closed. -/
private lemma isClosed_singleton_of_mem_of_finite {X : Type*} [TopologicalSpace X]
    [JacobsonSpace X] {S : Set X} (hS : S.Finite) (hSc : IsClosed S) {q : X} (hq : q ∈ S) :
    IsClosed ({q} : Set X) := by
  have hS' := hSc.isClosedEmbedding_subtypeVal
  have : Finite S := hS.to_subtype
  have : JacobsonSpace S := .of_isClosedEmbedding hS'
  simpa using hS'.isClosedMap _ (isClosed_discrete {(⟨q, hq⟩ : S)})

/-- On a smooth surface, the multiplicity of a prime divisor `E` at a closed point `q` of a
different prime divisor `F` is at most the local intersection number `i_q(F, E)`. -/
private lemma toNat_multiplicityAt_le_localIntersectionNumber {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX)
    (hXs : MMP.Mori.IsSmoothScheme sX) (hXd : topologicalKrullDim X = 2)
    {F E : MMP.Mori.PrimeDivisor X} (hne : F ≠ E) {q : X} (hqc : IsClosed ({q} : Set X))
    (hqF : q ∈ F.support) :
    ((E.multiplicityAt q).toNat : ℚ) ≤
      (localIntersectionNumber sX q (Finsupp.single F 1) (Finsupp.single E 1) : ℚ) := by
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hXs).1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hXs).2
  have : QuasiCompact sX := hX.toQuasiCompact
  have heff : ∀ G : MMP.Mori.PrimeDivisor X,
      DivisorWithCoeffs.IsEffective (Finsupp.single G (1 : ℤ)) := fun G =>
    DivisorWithCoeffs.isEffective_iff_nonneg.2 (Finsupp.single_nonneg.2 zero_le_one)
  have hmul := SurfaceAux.multiplicityAt_mul_le _ hX hXs hXd hqc (heff F) (heff E)
    (fun G hG hG' => by
      rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hG hG'
      exact absurd (hG.symm.trans hG') hne)
  rw [DivisorWithCoeffs.multiplicityAt_single, DivisorWithCoeffs.multiplicityAt_single] at hmul
  simp only [nsmul_eq_mul, mul_one] at hmul
  have hF1 : 1 ≤ (F.multiplicityAt q).toNat := by
    have hle : (1 : ℕ∞) ≤ F.multiplicityAt q := by
      rw [MMP.Mori.PrimeDivisor.multiplicityAt]
      refine le_iSup₂_of_le 1 ?_ (by norm_num)
      rw [pow_one]
      exact Scheme.IdealSheafData.stalkIdeal_le_maximalIdeal_of_mem_support _ hqF
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
      (multiplicityAt_ne_top F (isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hXs F) q)
    rw [← hn] at hle ⊢
    simpa using hle
  have h1 : ((E.multiplicityAt q).toNat : ℤ) ≤
      ((F.multiplicityAt q).toNat : ℤ) * ((E.multiplicityAt q).toNat : ℤ) :=
    le_mul_of_one_le_left (Nat.cast_nonneg _) (by exact_mod_cast hF1)
  exact_mod_cast h1.trans hmul

/-- The exceptional curve is not the strict transform of a prime divisor. -/
private lemma exceptional_ne_of_inverseTransformPrimeDivisor_eq_some {k : Type u} [Field k]
    [IsAlgClosed k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} (hY : MMP.Mori.IsVariety k sY)
    (hYd : topologicalKrullDim Y = 2) {p : Y} (hp : IsClosed ({p} : Set Y))
    {F : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    {E : MMP.Mori.PrimeDivisor Y}
    {E' : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))}
    (hE' : inverseTransformPrimeDivisor
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) E = some E') :
    F ≠ E' := by
  rintro rfl
  obtain ⟨-, hV⟩ := map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hE'
  rw [(mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hp hF _).mp
    (genericPoint_mem_support F)] at hV
  exact notMem_biregularLocus_blowUpToBase_singleton hY hYd hp hF hV

/-- **The intersection with the exceptional curve.** For a prime divisor `E` of `Y` with strict
transform `E'`, `(E' · F) = mult_p E`: the local intersection numbers of `F` and `E'` sum to
`mult_p E`. This is `π^*E = E' + (mult_p E) F`, `(π^*E · F) = 0` and `(F · F) = -1`. -/
private lemma finsum_localIntersectionNumber_eq_multiplicityAt {k : Type u} [Field k]
    [IsAlgClosed k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    (hY : MMP.Mori.IsVariety k sY) (hYs : MMP.Mori.IsSmoothScheme sY)
    (hYd : topologicalKrullDim Y = 2) {p : Y} (hp : IsClosed ({p} : Set Y))
    {F : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    {E : MMP.Mori.PrimeDivisor Y}
    {E' : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))}
    (hE' : inverseTransformPrimeDivisor
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) E = some E') :
    (F.support ∩ E'.support).Finite ∧
      ∑ᶠ y ∈ F.support ∩ E'.support, (localIntersectionNumber
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ sY) y
        (Finsupp.single F 1) (Finsupp.single E' 1) : ℚ) = ((E.multiplicityAt p).toNat : ℚ) := by
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
  have hYs' := isSmoothScheme_blowUp_singleton hY hYs hYd hp
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs').1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs').2
  have := compactSpace_blowUp_singleton hY hYd hp
  have hY' := isVariety_blowUp_singleton hY hYd hp
  have : QuasiCompact (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ sY) :=
    hY'.toQuasiCompact
  have : Smooth sY := (MMP.Mori.isSmoothScheme_iff sY).mp hYs
  obtain ⟨-, -, hYd', -, -, -, F₀, hF₀, -, hFprop, -, hFF⟩ :=
    isProjective_blowUpToBase_vanishingIdeal_singleton_and_isMinusOneCurve sY hY hYd hp
  obtain rfl : F = F₀ := MMP.Mori.PrimeDivisor.ext_idealSheaf (hF.trans hF₀.symm)
  obtain ⟨hfin, hS, -⟩ := isIntersectionNumber_finsum_localIntersectionNumber_of_ne _ hY' hYs'
    hYd' (exceptional_ne_of_inverseTransformPrimeDivisor_eq_some hY hYd hp hF hE') hFprop
  refine ⟨hfin, ?_⟩
  obtain ⟨-, -, -, -, F₁, hF₁, -, hPC, -⟩ :=
    blowUp_singleton_smooth_isProper_isBirational_exceptional_selfIntersection hY hYs hYd hp
  obtain rfl : F = F₁ := MMP.Mori.PrimeDivisor.ext_idealSheaf (hF.trans hF₁.symm)
  let FC : ProperCurve (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ sY) :=
    ⟨F.genericPoint, hPC⟩
  have hFmem := mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hp hF
  have hcon : FC.IsContractedBy
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) := by
    intro x hx
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
    rw [(hFmem x).mp hx, (hFmem _).mp (genericPoint_mem_support F)]
  have : IsIntegral (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) := hY'.toIsIntegral
  have : IsSeparated sY := hY.toIsSeparated
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : QuasiCompact sY := hY.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hDc := MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hYs E
  have hB := blowUpToBase_componentGenericPoint_notMem_supp hY hYd hp (Finsupp.single E (1 : ℤ))
  have h0 := Divisor.degreeOn_pullback_eq_zero_of_isContractedBy (sY := sY)
    (sX := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ sY) _ rfl hDc hB FC hcon
  have hD' := hDc.isCartier_pullback _ hB
  have : IsProper (FC.ι ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ sY) :=
    FC.isProper_ι_comp
  have h := isIntersectionNumber_of_properCurve (Divisor.toQDivisor
    (Divisor.pullback (Finsupp.single E (1 : ℤ)) hDc hB))
    (QDivisor.isQCartier_toQDivisor hD') FC F rfl
  rw [QDivisor.intersectionNumber_toQDivisor k _ _ _ _ hD', h0, Int.cast_zero,
    pullback_single_blowUp_singleton hY hYs hYd hp hF E, map_add, inverseTransformDivisor_single,
    hE'] at h
  simp only [Option.elim, toQDivisor_single, Int.cast_one, Int.cast_natCast] at h
  have hmF := hFF.smul ((E.multiplicityAt p).toNat : ℚ)
    (MMP.Fourfold.isQCartier_of_isSmoothScheme hYs' _)
  rw [Finsupp.smul_single, smul_eq_mul, mul_one] at hmF
  linarith [(MMP.Flips.isIntersectionNumber_add hS hmF).unique h]

/-- **The prime case.** For a prime divisor `E` of `Y` with strict transform `E'` and `q ∈ F`,
`mult_q E' ≤ mult_p E`: if `q ∈ E'` then `q` is a closed point and
`mult_q E' ≤ i_q(F, E') ≤ (E' · F) = mult_p E`. -/
private lemma toNat_multiplicityAt_le {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} (hY : MMP.Mori.IsVariety k sY) (hYs : MMP.Mori.IsSmoothScheme sY)
    (hYd : topologicalKrullDim Y = 2) {p : Y} (hp : IsClosed ({p} : Set Y))
    {F : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    {E : MMP.Mori.PrimeDivisor Y}
    {E' : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))}
    (hE' : inverseTransformPrimeDivisor
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) E = some E')
    {q : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)} (hq : q ∈ F.support) :
    (E'.multiplicityAt q).toNat ≤ (E.multiplicityAt p).toNat := by
  by_cases hqE : q ∉ E'.support
  · rw [E'.multiplicityAt_eq_zero_of_notMem hqE]; simp
  rw [not_not] at hqE
  have hY' := isVariety_blowUp_singleton hY hYd hp
  have : LocallyOfFiniteType (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ sY) :=
    hY'.toLocallyOfFiniteType
  have := LocallyOfFiniteType.jacobsonSpace
    (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ sY)
  obtain ⟨hfin, hsum⟩ := finsum_localIntersectionNumber_eq_multiplicityAt hY hYs hYd hp hF hE'
  have hqc : IsClosed ({q} : Set _) := isClosed_singleton_of_mem_of_finite hfin
    (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isClosed_closure.inter isClosed_closure) ⟨hq, hqE⟩
  have : Smooth sY := (MMP.Mori.isSmoothScheme_iff sY).mp hYs
  obtain ⟨-, -, hYd', -⟩ :=
    isProjective_blowUpToBase_vanishingIdeal_singleton_and_isMinusOneCurve sY hY hYd hp
  have hloc := toNat_multiplicityAt_le_localIntersectionNumber hY'
    (isSmoothScheme_blowUp_singleton hY hYs hYd hp) hYd'
    (exceptional_ne_of_inverseTransformPrimeDivisor_eq_some hY hYd hp hF hE') hqc hq
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
  have := Finset.single_le_sum (f := fun y => (localIntersectionNumber
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ sY) y
      (Finsupp.single F 1) (Finsupp.single E' 1) : ℚ))
    (fun _ _ => Nat.cast_nonneg _) (hfin.mem_toFinset.2 ⟨hq, hqE⟩)
  exact_mod_cast hloc.trans (this.trans hsum.le)

/-- The multiplicity at a point of a finite sum of divisors is the sum of the multiplicities. -/
private lemma multiplicityAt_sum {X : Scheme.{u}} {R : Type*} [AddCommMonoid R] {ι : Type*}
    (s : Finset ι) (f : ι → DivisorWithCoeffs R X) (x : X) :
    (∑ i ∈ s, f i).multiplicityAt x = ∑ i ∈ s, (f i).multiplicityAt x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DivisorWithCoeffs.multiplicityAt]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, DivisorWithCoeffs.multiplicityAt_add, ih]

/-- **Multiplicity of a strict transform along the exceptional curve.** Let `Y` be a surface
smooth over an algebraically closed field `k`, `p ∈ Y` a closed point, `π : Y' ⟶ Y` the blow-up
of the reduced point `p`, and `F` the exceptional curve, the prime divisor of `Y'` with ideal
sheaf `exceptionalIdeal`. Then for every effective `ℚ`-divisor `D` on `Y` and every point `q`
of `F`, `mult_q (π⁻¹_* D) ≤ mult_p D`. -/
@[mmp "lem_km4a_strict_transform_multiplicity_bound"]
public theorem multiplicityAt_inverseTransformDivisor_blowUpToBase_le
    {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    (hY : Mori.IsVariety k sY) (hYs : Mori.IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    {p : Y} (hp : IsClosed ({p} : Set Y))
    {F : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    {D : Mori.QDivisor Y} (hD : 0 ≤ D)
    {q : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)} (hq : q ∈ F.support) :
    (Mori.inverseTransformDivisor
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) D).multiplicityAt q ≤
      D.multiplicityAt p := by
  classical
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, map_sum, multiplicityAt_sum, DivisorWithCoeffs.multiplicityAt,
    Finsupp.sum]
  refine Finset.sum_le_sum fun E _ => ?_
  rw [inverseTransformDivisor_single]
  rcases h : inverseTransformPrimeDivisor
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) E with _ | E'
  · simp only [Option.elim, DivisorWithCoeffs.multiplicityAt, Finsupp.sum_zero_index]
    exact nsmul_nonneg (hD E) _
  · simp only [Option.elim]
    rw [DivisorWithCoeffs.multiplicityAt_single]
    exact nsmul_le_nsmul_left (hD E) (toNat_multiplicityAt_le hY hYs hYd hp hF h hq)

end MMP.Threefold.Resolution
