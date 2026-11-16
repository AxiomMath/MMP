module

public import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeCartier

section

/-!
# Kleiman's ampleness criterion for Cartier divisors, absolute form

Let `k` be an algebraically closed field of characteristic zero and `X` a projective variety
over `k` with structure morphism `s : X ⟶ Spec k`. The relative Kleiman criterion for `s`
over the one-point base `Spec k` gives the absolute criterion: every curve of `X` is contracted
by `s`, so the natural map `N₁(X/Spec k) → N₁(X)` is a linear homeomorphism carrying the
relative cone of curves onto `NE(X)` and respecting intersection numbers, and `s`-ampleness over
the affine one-point base is ampleness.

## Main results

* `MMP.Mori.isAmple_cartierSheaf_iff_forall_closedConeOfCurves_pos`: Kleiman's criterion.

## Implementation notes

Ampleness of `D` is ampleness of its invertible sheaf `𝒪_X(D)`, and `D(z)` is the value at `z`
of the linear form `NumericalCurveClasses.intersectionNumber` of the `ℝ`-Cartier divisor `1 · D`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.18
* [S. Kleiman, *Toward a numerical theory of ampleness*][Kle66]
-/

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction MMP.Mori

namespace MMP.FourfoldProofs.MmpFoundationCharZeroAbsoluteCartierKleimanProof

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))

/-- Every proper curve of a `k`-scheme is contracted by its structure morphism. -/
private theorem isContractedBy_self (C : ProperCurve sX) : C.IsContractedBy sX :=
  fun _ _ => Subsingleton.elim _ _

private theorem relativeOneCycles_self_eq_top : relativeOneCycles sX sX = ⊤ :=
  eq_top_iff.mpr fun Z _ => (Finsupp.mem_supported ℝ Z).mpr fun C _ => isContractedBy_self sX C

/-- Over the one-point base, `N₁(X/Spec k) → N₁(X)` is bijective: every 1-cycle is relative,
and the relative and absolute numerically trivial cycles agree. -/
private theorem relativeToAbsolute_bijective :
    Function.Bijective (relativeToAbsolute sX sX) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun z hz => ?_, fun w => ?_⟩
  · obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX sX z
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      ((Submodule.Quotient.mk_eq_zero (OneCycle.numericallyTrivial sX)).mp hz)
  · obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX w
    exact ⟨relativeNumericalClass sX sX ⟨Z, relativeOneCycles_self_eq_top sX ▸ trivial⟩, rfl⟩

/-- The natural map `N₁(X/Spec k) → N₁(X)` is a linear equivalence. -/
private noncomputable def relEquiv :
    RelativeNumericalCurveClasses sX sX ≃ₗ[ℝ] NumericalCurveClasses sX :=
  LinearEquiv.ofBijective _ (relativeToAbsolute_bijective sX)

private theorem degree_relEquiv (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (z : RelativeNumericalCurveClasses sX sX) :
    NumericalCurveClasses.degree sX L (relEquiv sX z) =
      RelativeNumericalCurveClasses.degree sX sX L z := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX sX z
  rfl

private theorem intersectionNumber_relEquiv (D : KCartierDivisor ℝ X)
    (z : RelativeNumericalCurveClasses sX sX) :
    NumericalCurveClasses.intersectionNumber D (relEquiv sX z) =
      RelativeNumericalCurveClasses.intersectionNumber D z := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX sX z
  rfl

/-- The relative topology on `N₁(X/Spec k)` is induced from the numerical topology on `N₁(X)`. -/
private theorem isInducing_relEquiv : Topology.IsInducing (relEquiv sX) := by
  refine ⟨?_⟩
  simp only [RelativeNumericalCurveClasses.instTopologicalSpace,
    NumericalCurveClasses.instTopologicalSpace, induced_iInf, induced_compose]
  refine iInf_congr fun L => iInf_congr fun h => ?_
  congr 1
  exact funext fun z => (degree_relEquiv sX L z).symm

/-- The natural map carries `NE(X/Spec k)` onto `NE(X)`. -/
private theorem image_relativeConeOfCurves :
    relEquiv sX '' (relativeConeOfCurves sX sX : Set _) = coneOfCurves sX := by
  have h := congrArg SetLike.coe <| Submodule.map_span
    ((relEquiv sX).toLinearMap.restrictScalars NNReal)
    (Set.range fun C : {C : ProperCurve sX // C.IsContractedBy sX} => C.1.relativeClass sX C.2)
  rw [← Set.range_comp] at h
  refine h.trans ?_
  rw [← (Equiv.subtypeUnivEquiv (isContractedBy_self sX)).symm.surjective.range_comp]
  rfl

/-- A class lies in `NE̅(X/Spec k)` exactly when its image lies in `NE̅(X)`: the natural map is
a topological embedding carrying `NE(X/Spec k)` onto `NE(X)`. -/
private theorem relEquiv_mem_closedConeOfCurves_iff {z : RelativeNumericalCurveClasses sX sX} :
    relEquiv sX z ∈ closedConeOfCurves sX ↔ z ∈ relativeClosedConeOfCurves sX sX := by
  rw [← SetLike.mem_coe, ← SetLike.mem_coe, coe_closedConeOfCurves, coe_relativeClosedConeOfCurves,
    (isInducing_relEquiv sX).closure_eq_preimage_closure_image, image_relativeConeOfCurves]
  rfl

/-- Ampleness relative to the structure morphism to `Spec k` is ampleness. -/
private theorem isRelativelyAmple_iff_isAmple (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    IsRelativelyAmple sX L ↔ Stacks.Ample.IsAmple X L := by
  refine ⟨fun h => ?_, fun h y => ?_⟩
  · obtain ⟨V, -, hyV, hV⟩ := h (Classical.arbitrary _)
    obtain rfl : V = ⊤ := eq_top_iff.mpr fun y _ => (Subsingleton.elim y _ ▸ hyV)
    exact Stacks.HProjective.isAmple_of_isAmple_restrictTop L hV
  · refine ⟨⊤, isAffineOpen_top _, trivial, ?_⟩
    have : IsIso (sX ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso X.topIso.hom)
    have : QuasiCompact (sX ⁻¹ᵁ ⊤).ι := quasiCompact_of_isIso _
    exact Stacks.SectionExtension.isAmple_pullbackModule (sX ⁻¹ᵁ ⊤).ι L h
      (Or.inl ⟨inferInstance, inferInstance⟩)

end MMP.FourfoldProofs.MmpFoundationCharZeroAbsoluteCartierKleimanProof

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MMP.Mori

open MMP.FourfoldProofs.MmpFoundationCharZeroAbsoluteCartierKleimanProof in
/-- **Kleiman's criterion.** On a projective variety `X` over an algebraically closed field of
characteristic zero, a Cartier divisor `D` is ample if and only if `(D · z) > 0` for every
nonzero class `z` of the closed cone of curves `NE̅(X)`. -/
@[mmp "lem_mmp_foundation_char_zero_absolute_cartier_kleiman"]
public theorem isAmple_cartierSheaf_iff_forall_closedConeOfCurves_pos {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsProjectiveVariety k sX] (D : X.CartierDivisor) :
    Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf D) ↔
      ∀ z ∈ closedConeOfCurves sX, z ≠ 0 →
        0 < NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ D) z := by
  have : AlgebraicGeometry.IsVariety k (𝟙 (Spec (.of k))) := by constructor
  rw [← isRelativelyAmple_iff_isAmple sX,
    isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos (𝟙 _) sX sX
      ((isProjective_iff_isProjectiveMorphism_of_isAffine sX).mpr
        (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := k)))
      (Category.comp_id sX) D]
  refine (relEquiv sX).toEquiv.forall_congr fun {z} => ?_
  rw [LinearEquiv.coe_toEquiv, relEquiv_mem_closedConeOfCurves_iff, intersectionNumber_relEquiv,
    ne_eq, ne_eq, LinearEquiv.map_eq_zero_iff]

end MMP.Mori

end
