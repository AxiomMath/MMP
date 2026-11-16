module

public import MMP.AlgebraicGeometry.MMP.Contraction.RelativeLineBundleDescent
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltNegativeFace

/-!
# Line bundles trivial on a negative face descend along its contraction, for dlt pairs

Let `(X, Δ)` be a dlt pair with `X` a `ℚ`-factorial projective variety over an algebraically
closed field `k` of characteristic zero, and let `f : X ⟶ S` be a morphism of projective
varieties. Let `F` be an extremal face of the relative closed cone of curves `NE̅(X/S)` on which
`K_X + Δ` is negative away from `0`, and let `ψ : X ⟶ Z`, `g : Z ⟶ S` be a contraction of `F`
over `S`. Every invertible sheaf `L` on `X` of degree `0` on each curve `C` contracted by `f`
whose class `[C]` lies in `F` is the pull-back `ψ^* L_Z` of an invertible sheaf `L_Z` on `Z`.

The proof perturbs `Δ` to `(1 - δ)Δ`, which is klt and keeps `F` negative
(`MMP.Mori.IsDltPair.exists_isKltPair_one_sub_smul_of_isExtremalFace`), and applies the
corresponding statement for klt pairs; the notion of a contraction does not involve the boundary.

## Main results

* `MMP.Mori.IsDltPair.exists_isInvertible_nonempty_iso_pullback_of_isRelativeContractionOfFace`.

## Implementation notes

A line bundle is an invertible sheaf of `𝒪_X`-modules (`SheafOfModules.IsInvertible`), and
`(L · C)` is its degree `MMP.Mori.degreeOn` along the curve `C`. The contraction is a pair
`(ψ, g)` with `MMP.Mori.IsRelativeContractionOfFace f F ψ g`; this already contains that `F` is
an extremal face of `NE̅(X/S)`. The pairing of `K_X + Δ` with `N₁(X/S)` is
`MMP.Fourfold.QDivisor.relativeCurveForm`.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Theorem 3.35 (for
  3.25(4)) in case 3.21(0).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MMP.Mori

open MMP.Fourfold

/-- **Descent of line bundles along contractions of negative faces, dlt case.** Let `(X, Δ)` be
a dlt pair (canonical divisor `K`, `n = dim X`) with `X` `ℚ`-factorial, over an algebraically
closed field of characteristic zero, and `f : X ⟶ S` a morphism of projective varieties. Let
`F ⊆ N₁(X/S)` with `((K + Δ) · z) < 0` for every `z ∈ F`, `z ≠ 0`, and let `(ψ, g)` be a
contraction of `F` over `S`. If `L` is an invertible sheaf on `X` with `deg_C L = 0` for every
curve `C` contracted by `f` with `[C] ∈ F`, then `L ≅ ψ^* L_Z` for an invertible sheaf `L_Z` on
`Z`. -/
@[mmp "thm_km3c_dlt_relative_contraction_line_bundle"]
public theorem IsDltPair.exists_isInvertible_nonempty_iso_pullback_of_isRelativeContractionOfFace
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X S Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (sS : S ⟶ Spec (.of k)) [IsProjectiveVariety k sX]
    [IsProjectiveVariety k sS] [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] (f : X ⟶ S) (hf : f ≫ sS = sX)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hΔ : IsDltPair sX n K Δ) (hX : IsQFactorial sX)
    {F : Set (RelativeNumericalCurveClasses sX f)}
    (hneg : ∀ z ∈ F, z ≠ 0 →
      QDivisor.relativeCurveForm sX f (Divisor.toQDivisor K + Δ) hΔ.1.2.2 z < 0)
    {ψ : X ⟶ Z} {g : Z ⟶ S} (hψ : IsRelativeContractionOfFace f F ψ g)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : ∀ (C : ProperCurve sX) (hC : C.IsContractedBy f), C.relativeClass f hC ∈ F →
      degreeOn k sX C.ι C.dim_le L = 0) :
    ∃ LZ : Z.Modules, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 LZ ∧
      Nonempty (L ≅ (Scheme.Modules.pullback ψ).obj LZ) := by
  obtain ⟨δ, -, hδ1, hδ, hδneg⟩ :=
    hΔ.exists_isKltPair_one_sub_smul_of_isExtremalFace sS f hf hX hψ.isExtremalFace hneg
  refine exists_isInvertible_iso_pullback_of_isRelativeContractionOfFace
    ⟨inferInstance, inferInstance, inferInstance, inferInstance, hf⟩ hδ
    (smul_nonneg (sub_nonneg.2 hδ1.le) fun P => (hΔ.2.1 P).1)
    ⟨hψ.isExtremalFace, hψ.isExtremalFace.2.2.1, ?_⟩ hψ L hL
  rw [← QDivisor.relativeCurveForm_eq_comp]
  exact hδneg

end MMP.Mori
