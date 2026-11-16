module

public import MMP.AlgebraicGeometry.MMP.Contraction.RelativeContraction
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltNegativeFace

/-!
# Existence of contractions of negative faces for dlt pairs

Let `(X, Δ)` be a dlt pair with `X` a `ℚ`-factorial projective variety over an algebraically
closed field `k` of characteristic zero, and let `f : X ⟶ S` be a morphism of projective
varieties. Every convex extremal face `F` of the relative closed cone of curves `NE̅(X/S)` on
which `K_X + Δ` is negative away from `0` has a contraction over `S`: morphisms `ψ : X ⟶ Z` and
`g : Z ⟶ S`, with `g` projective, `g ∘ ψ = f` and `ψ_* 𝒪_X = 𝒪_Z`, contracting exactly the curves
over `S` whose class lies in `F`.

The proof perturbs `Δ` to `(1 - δ)Δ`, which is klt and keeps `F` negative
(`MMP.Mori.IsDltPair.exists_isKltPair_one_sub_smul_of_isExtremalFace`), and applies the
contraction theorem for klt pairs; the notion of a contraction does not involve the boundary.

## Main results

* `MMP.Mori.IsDltPair.exists_isRelativeContractionOfFace`.

## Implementation notes

`MMP.Mori.IsExtremalFace` asks only that `F` be a cone, not that it be convex. The extremal faces
of [KM98] are convex subcones, and the statement assumes this as `F` being closed under addition:
for a union of two extremal rays which is not a face, a morphism contracting the curves of both
rays also contracts curves whose class lies in the face they span, so no contraction in the sense
of `MMP.Mori.IsRelativeContractionOfFace` exists. The pairing with `K_X + Δ` on `N₁(X/S)` is
`MMP.Fourfold.QDivisor.relativeCurveForm`.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Theorem 3.35 (for
  3.25(3)) in case 3.21(0).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MMP.Mori

open MMP.Fourfold

/-- **Contractions of negative faces for dlt pairs.** Let `(X, Δ)` be a dlt pair (canonical
divisor `K`, `n = dim X`) with `X` `ℚ`-factorial, over an algebraically closed field of
characteristic zero, and `f : X ⟶ S` a morphism of projective varieties. If `F` is an extremal
face of `relativeClosedConeOfCurves sX f`, closed under addition, with `((K + Δ) · z) < 0` for
every `z ∈ F`, `z ≠ 0`, then `F` has a contraction over `S`: there are `ψ : X ⟶ Z` and
`g : Z ⟶ S` with `IsRelativeContractionOfFace f F ψ g`. -/
@[mmp "thm_km3c_dlt_relative_contraction_exists"]
public theorem IsDltPair.exists_isRelativeContractionOfFace
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X S : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (sS : S ⟶ Spec (.of k)) [IsProjectiveVariety k sX]
    [IsProjectiveVariety k sS] [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] (f : X ⟶ S) (hf : f ≫ sS = sX)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hΔ : IsDltPair sX n K Δ) (hX : IsQFactorial sX)
    {F : Set (RelativeNumericalCurveClasses sX f)}
    (hF : IsExtremalFace ℝ (relativeClosedConeOfCurves sX f :
      Set (RelativeNumericalCurveClasses sX f)) F)
    (hFadd : ∀ u ∈ F, ∀ v ∈ F, u + v ∈ F)
    (hneg : ∀ z ∈ F, z ≠ 0 →
      QDivisor.relativeCurveForm sX f (Divisor.toQDivisor K + Δ) hΔ.1.2.2 z < 0) :
    ∃ (Z : Scheme.{0}) (ψ : X ⟶ Z) (g : Z ⟶ S), IsRelativeContractionOfFace f F ψ g := by
  obtain ⟨δ, -, hδ1, hδ, hδneg⟩ :=
    hΔ.exists_isKltPair_one_sub_smul_of_isExtremalFace sS f hf hX hF hneg
  refine exists_isRelativeContractionOfFace_of_isNegativeExtremalFace
    ⟨inferInstance, inferInstance, inferInstance, inferInstance, hf⟩ hδ
    (smul_nonneg (sub_nonneg.2 hδ1.le) fun P => (hΔ.2.1 P).1) ⟨hF, hFadd, ?_⟩
  rw [← QDivisor.relativeCurveForm_eq_comp]
  exact hδneg

end MMP.Mori
