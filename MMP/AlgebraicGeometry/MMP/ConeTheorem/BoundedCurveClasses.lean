module

public import MMP.AlgebraicGeometry.Intersection.N1CartierCoordinates
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.AmpleStrictlyPositive
public import MMP.Analysis.Convex.Cone.CompactSlices

/-!
# Compact ample slices of the closed cone of curves

Let `k` be an algebraically closed field of characteristic zero, `X` a projective variety over
`k`, `H` an ample Cartier divisor on `X` and `c ∈ ℝ`. The slice
`{z ∈ NE̅(X) | (z · H) ≤ c}` of the closed cone of curves is compact for the numerical topology
of `N₁(X)`, and only finitely many numerical classes of effective integral 1-cycles have
`H`-degree at most `c`.

Choosing Cartier divisors whose evaluations form a basis of `N₁(X)^*` gives a linear
homeomorphism `Φ : N₁(X) ≃ ℝ^r`. Under `Φ` the closed cone `NE̅(X)` is a closed cone on whose
nonzero points `H` is positive, so its slice `{H ≤ c}` is compact. The classes of effective
integral 1-cycles lie in this slice and in the closed discrete lattice `Φ⁻¹(ℤ^r)`; a compact
discrete set is finite.

## Main results

* `MMP.Mori.isCompact_closedConeOfCurves_inter_le_and_finite`: the two statements above.

## Implementation notes

Ampleness of `H` is ampleness of its invertible sheaf `𝒪_X(H)`, and `H` acts on `N₁(X)` through
the `ℝ`-Cartier divisor `1 · H`. An effective integral 1-cycle is an element of
`MMP.Mori.OneCycle ℤ sX` with nonnegative coefficients; its class is that of the real cycle
obtained by casting the coefficients.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, 1.18, 1.19.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MMP.Mori

open MMP.Positivity

/-- **Compact slices, transported.** If `E` is linearly homeomorphic to a finite-dimensional
normed space, `C ⊆ E` is a closed cone and `G` is a linear form positive on `C ∖ {0}`, then every
slice `{z ∈ C : G z ≤ t}` is compact. -/
private lemma isCompact_slice_of_continuousLinearEquiv {E F : Type*} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (Φ : E ≃L[ℝ] F) {C : Set E} (hC : IsCone ℝ C) (hCcl : IsClosed C)
    {G : E →ₗ[ℝ] ℝ} (hG : ∀ z ∈ C, z ≠ 0 → 0 < G z) (t : ℝ) :
    IsCompact {z | z ∈ C ∧ G z ≤ t} := by
  have h := isCompact_slice_of_normed (isCone_preimage hC Φ.symm.toLinearMap)
    (hCcl.preimage Φ.symm.continuous) (G := G ∘ₗ Φ.symm.toLinearMap)
    (fun z hz hz0 => hG _ hz (by simpa using hz0)) t
  rw [← Φ.toHomeomorph.isCompact_preimage] at h
  convert h using 1
  ext z
  simp

/-- On a projective variety `X` over an algebraically closed field of characteristic zero, for
an ample Cartier divisor `H` and any real `c`, the slice `{z ∈ NE̅(X) | (z · H) ≤ c}` is compact in
`N₁(X)`, and the classes of effective integral 1-cycles `Z` with `(Z · H) ≤ c` form a finite
set. -/
@[mmp "lem_mmp_foundation_char_zero_projective_bounded_curve_classes"]
public theorem isCompact_closedConeOfCurves_inter_le_and_finite
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX] (H : X.CartierDivisor)
    (hH : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf H))
    (c : ℝ) :
    IsCompact ((closedConeOfCurves sX : Set (NumericalCurveClasses sX)) ∩
        {z | NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ H) z ≤ c}) ∧
    {z : NumericalCurveClasses sX | ∃ Z : OneCycle ℤ sX, (∀ C, 0 ≤ Z C) ∧
        OneCycle.numericalClass sX (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero Z) = z ∧
        NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ H) z ≤ c}.Finite := by
  obtain ⟨hfd, -, hext, hcoord, -⟩ :=
    NumericalCurveClasses.exists_cartier_coordinates_of_isProperVariety sX
  obtain ⟨t, -, ht, htspan⟩ := hext ∅ (linearIndepOn_empty _ _)
  rw [Set.image_eq_range] at htspan
  obtain ⟨⟨Φ, -⟩, hΛc, hΛd, -, hint⟩ := hcoord (fun E : t => (E : X.CartierDivisor)) ht htspan
  haveI := hfd
  haveI : Fintype t := @Fintype.ofFinite _ ht.finite
  have hS := isCompact_slice_of_continuousLinearEquiv Φ (isCone_coe _) isClosed_closure
    (G := NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ H))
    (fun z hz hz0 => by
      obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
      exact closedConeOfCurves_diff_zero_subset_posHalfspace sX H hH ⟨hz, hz0⟩ Z rfl) c
  refine ⟨hS, ((hS.inter_right hΛc).finite (isDiscrete_iff_discreteTopology.2
    (DiscreteTopology.of_subset hΛd Set.inter_subset_right))).subset ?_⟩
  rintro z ⟨Z, hZ, rfl, hle⟩
  exact ⟨⟨coneOfCurves_le_closedConeOfCurves sX ((mem_coneOfCurves_iff sX _).2
    ⟨_, fun C => by simpa using hZ C, rfl⟩), hle⟩, hint Z⟩

end MMP.Mori
