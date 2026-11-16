module

public import MMP.AlgebraicGeometry.MMP.Flip.ReducedPartRemoval
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.NegativeFaceSupportingDivisor
public import MMP.AlgebraicGeometry.MMP.Contraction.SupportingDivisorFree

section

/-!
# Nonzero negative extremal faces contain the class of a curve

Let `(X, Δ)` be a klt pair, `X` projective over an algebraically closed field `k` of
characteristic zero and `Δ` effective, and `F ≠ {0}` a `(K_X + Δ)`-negative extremal face of
`NE̅(X)`. Let `D` be a supporting divisor of `F` and `b ≥ 1` with `|bD|` basepoint free. The
sections of `𝒪_X(bD)` define a proper morphism `φ : X ⟶ ℙᴺ_k` with `φ^* 𝒪(1) ≅ 𝒪_X(bD)`. If `φ`
is not quasi-finite, some fibre contains a curve `C`, on which `deg_C 𝒪_X(bD) = 0`, so `[C] ∈ F`.
Otherwise `φ` is finite, `𝒪_X(bD)` is ample, `D` is positive on `NE̅(X) \ {0}` by Kleiman's
criterion, and `F = {0}`.

## Main results

* `MMP.Mori.exists_properCurve_numericalClass_mem_of_isNegativeExtremalFace`: `F` contains the
  class `[C]` of a proper curve `C ⊆ X`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.3 Step 8
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.AmpleProjectiveImmersion MMP.Mori

namespace MMP.FourfoldProofs.Km3bNegativeFaceContainsCurveProof

/-- On a proper `k`-scheme, a globally generated invertible sheaf `L` either has degree zero on
some proper curve, or is ample. -/
private theorem exists_degree_eq_zero_or_isAmple {k : Type} [Field k] {X : Scheme.{0}}
    [IsLocallyNoetherian X] (sX : X ⟶ Spec (.of k)) [IsProper sX] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : MMP.Intersection.IsGloballyGenerated L) :
    (∃ C : ProperCurve sX, C.degree k L = 0) ∨ Stacks.Ample.IsAmple X L := by
  obtain ⟨n, t, ht, -⟩ :=
    exists_fin_basis_generatesStalks_of_generatesStalks_id sX L
      hL.generatesStalks_id
  obtain ⟨θ, -⟩ :=
    exists_iso_projectiveSpaceTwistingSheaf_toProjectiveSpaceOver
      t ht sX
  set φ := Stacks.ProjectiveFromSections.toProjectiveSpaceOver t ht sX
  have hφ : φ ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{0} n)) = sX :=
    Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst t ht sX
  haveI : IsProper (pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{0} n))) :=
    isProper_projectiveSpaceOver n (Spec (.of k))
  haveI : IsProper (φ ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{0} n))) := by
    rw [hφ]; infer_instance
  haveI : IsProper φ := IsProper.of_comp _ (pullback.fst (terminal.from (Spec (.of k)))
    (terminal.from (projectiveSpaceAtUniverse.{0} n)))
  by_cases hq : LocallyQuasiFinite φ
  · right
    haveI := IsFinite.of_isProper_of_locallyQuasiFinite φ
    have h1 := isAmple_pullback_of_isFinite φ _
      ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr
        (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf n (Spec (.of k))))
    exact (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mp
      (Scheme.Modules.isAmple_of_iso θ h1)
  · left
    obtain ⟨C, hC⟩ :=
      MMP.Fourfold.exists_properCurve_isContractedBy_of_not_locallyQuasiFinite (sX := sX) hq
    refine ⟨C, ?_⟩
    rw [ProperCurve.degree, ← degreeOn_eq_of_iso k sX C.ι C.dim_le θ]
    exact C.degree_pullback_eq_zero_of_isContractedBy φ hφ hC _

/-- The form `z ↦ (nD · z)` is `n` times `z ↦ (D · z)` on `N₁(X)`, for `n ≥ 1`. -/
private theorem intersectionNumber_ofCartier_nsmul {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (D : X.CartierDivisor) {n : ℕ} (hn : 1 ≤ n)
    (z : NumericalCurveClasses sX) :
    NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ (n • D)) z =
      n * NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ D) z := by
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
  rw [NumericalCurveClasses.intersectionNumber_ofCartier,
    NumericalCurveClasses.intersectionNumber_ofCartier,
    NumericalCurveClasses.degree_numericalClass, NumericalCurveClasses.degree_numericalClass,
    OneCycle.degree_apply, OneCycle.degree_apply, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun C _ => ?_
  rw [C.degree_sheaf_nsmul D hn]
  push_cast
  ring

end MMP.FourfoldProofs.Km3bNegativeFaceContainsCurveProof

end

section

/-!
# Nonzero negative extremal faces contain the class of a curve

Let `X` be a projective variety over an algebraically closed field `k` of characteristic zero
and `(X, Δ)` a klt pair with `Δ` effective. Every `(K_X + Δ)`-negative extremal face `F ≠ {0}`
of the closed cone of curves `NE̅(X)` contains the numerical class `[C]` of an irreducible curve
`C ⊆ X`.

## Main results

* `MMP.Mori.exists_properCurve_numericalClass_mem_of_isNegativeExtremalFace`: the statement
  above.

## Implementation notes

An irreducible curve `C ⊆ X` is a `MMP.Mori.ProperCurve` (an integral closed subscheme of
dimension one, proper over `k`; on projective `X` every irreducible curve is one), and its class
`[C] ∈ N₁(X)` is `OneCycle.numericalClass sX (C.cycle ℝ)`, the class used in
`MMP.Mori.IsContractionOfFace`. The form `z ↦ ((K_X + Δ) · z)` is
`MMP.Fourfold.QDivisor.curveForm` of `K_X + Δ`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.3 Step 8
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Stacks.AmpleProjectiveImmersion
  MMP.FourfoldProofs.Km3bNegativeFaceContainsCurveProof

namespace MMP.Mori

/-- **Nonzero negative extremal faces contain curve classes** (Kollár–Mori 3.3, Step 8). Let `X`
be a projective variety over an algebraically closed field `k` of characteristic zero, `(X, Δ)`
a klt pair with canonical divisor `K` and `Δ` effective, and `F ≠ {0}` a `(K + Δ)`-negative
extremal face of `NE̅(X)`. Then `F` contains the class `[C]` of some irreducible curve
`C ⊆ X`. -/
@[mmp "lem_km3b_negative_face_contains_curve"]
public theorem exists_properCurve_numericalClass_mem_of_isNegativeExtremalFace {k : Type}
    [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective) {F : Set (NumericalCurveClasses sX)}
    (hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) F)
    (hF0 : F ≠ {0}) :
    ∃ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ F := by
  obtain ⟨D, hD⟩ := exists_isSupportingDivisor_of_isNegativeExtremalFace hklt hΔ hF
  obtain ⟨b₀, hb₀⟩ := exists_isGloballyGenerated_sheaf_nsmul_of_isSupportingDivisor hklt hΔ hF hD
  have hb : 1 ≤ b₀ + 1 := Nat.le_add_left 1 b₀
  rcases exists_degree_eq_zero_or_isAmple sX _ (hb₀ (b₀ + 1) (Nat.le_succ b₀)) with
    ⟨C, hC⟩ | hamp
  · refine ⟨C, (hD.numericalClass_mem_iff_degree_eq_zero C).2 ?_⟩
    rw [C.degree_sheaf_nsmul D hb] at hC
    exact (mul_eq_zero.mp hC).resolve_left (by omega)
  · exfalso
    apply hF0
    have hpos := (isAmple_cartierSheaf_iff_forall_closedConeOfCurves_pos sX _).1 hamp
    ext z
    rw [← hD.2, Set.mem_setOf_eq, Set.mem_singleton_iff]
    refine ⟨fun ⟨hz, hz0⟩ => by_contra fun hne => ?_, ?_⟩
    · have h := hpos z hz hne
      rw [intersectionNumber_ofCartier_nsmul D hb, hz0, mul_zero] at h
      exact lt_irrefl _ h
    · rintro rfl
      exact ⟨(closedConeOfCurves sX).zero_mem, map_zero _⟩

end MMP.Mori

end
