module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.RationalCurves
public import MMP.AlgebraicGeometry.MMP.Contraction.LineBundleDescent

section

/-!
# Cone, contraction and descent for klt pairs over `k`

Let `X` be a projective variety over an algebraically closed field `k` of characteristic zero
and `(X, Δ)` a klt pair with `Δ` effective, of dimension `n`. Then:

1. there is a countable family of rational curves `C_j ⊆ X` with
   `0 < -((K_X + Δ) · C_j) ≤ 2n` and `NE̅(X) = NE̅(X)_{(K_X + Δ) ≥ 0} + ∑_j ℝ_{≥0} [C_j]`;
2. if `F` is a `(K_X + Δ)`-negative extremal face of `NE̅(X)` and `g : X ⟶ Z` a contraction of
   `F`, every line bundle `L` on `X` with `(L · C) = 0` for each irreducible curve `C` with
   `[C] ∈ F` is isomorphic to `g^* L_Z` for a line bundle `L_Z` on `Z`;
3. every `(K_X + Δ)`-negative extremal face of `NE̅(X)` has a contraction, onto a normal
   projective variety.

## Main results

* `MMP.Mori.cone_and_contraction_and_descent_of_isKltPair`: the three statements above.

## Implementation notes

Curves, classes and degrees are as in
`MMP.Mori.exists_countable_isRationalCurve_closedConeOfCurves_eq` and
`MMP.Mori.exists_isInvertible_iso_pullback_of_isContractionOfFace`: an irreducible curve is a
`MMP.Mori.ProperCurve`, its class is `OneCycle.numericalClass sX (C.cycle ℝ)`, the sum of rays is
`PointedCone.hull ℝ`, a line bundle is an invertible sheaf of `𝒪`-modules and `g^*` is
`AlgebraicGeometry.Scheme.Modules.pullback g`. A contraction of a face is
`MMP.Mori.IsContractionOfFace`; in part 3 the target is moreover normal
(`MMP.Mori.IsNormalVariety`).

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 3.7
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Pointwise

namespace MMP.Mori

/-- **Cone and contraction theorems over `k`** (Kollár–Mori 3.7(1),(3),(4)). Let `X` be a
projective variety over an algebraically closed field `k` of characteristic zero and `(X, Δ)` a
klt pair of dimension `n` with canonical divisor `K` and `Δ` effective. Then
1. there is a countable set `S` of rational curves `C` with `0 < -((K + Δ) · C) ≤ 2n` and
   `NE̅(X) = NE̅(X)_{(K + Δ) ≥ 0} + ∑_{C ∈ S} ℝ_{≥0} [C]`;
2. for a `(K + Δ)`-negative extremal face `F` of `NE̅(X)`, a contraction `g : X ⟶ Z` of `F` and
   an invertible sheaf `L` on `X` with `deg_C L = 0` whenever `[C] ∈ F`, `L ≅ g^* L_Z` for an
   invertible sheaf `L_Z` on `Z`;
3. every `(K + Δ)`-negative extremal face `F` of `NE̅(X)` has a contraction `ψ : X ⟶ Z` onto a
   normal projective variety `Z`. -/
@[mmp "lem_km3c_klt_cone_and_pullback_over_k"]
public theorem cone_and_contraction_and_descent_of_isKltPair {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective) :
    (∃ S : Set (ProperCurve sX), S.Countable ∧
      (∀ C ∈ S,
        IsRationalCurve sX
            (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({C.point} : Set X))) ∧
          0 < -MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2
            (OneCycle.numericalClass sX (C.cycle ℝ)) ∧
          -MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2
            (OneCycle.numericalClass sX (C.cycle ℝ)) ≤ 2 * n) ∧
      (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) =
        ((closedConeOfCurves sX : Set (NumericalCurveClasses sX)) ∩
            {z | 0 ≤ MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2 z}) +
          (PointedCone.hull ℝ
              ((fun C : ProperCurve sX => OneCycle.numericalClass sX (C.cycle ℝ)) '' S) :
            Set (NumericalCurveClasses sX))) ∧
    (∀ F : Set (NumericalCurveClasses sX),
      IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
        (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) F →
      ∀ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of k)) (g : X ⟶ Z), IsContractionOfFace k sX sZ F g →
      ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
        (∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ F → C.degree k L = 0) →
        ∃ LZ : Z.Modules, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 LZ ∧
          Nonempty (L ≅ (Scheme.Modules.pullback g).obj LZ)) ∧
    (∀ F : Set (NumericalCurveClasses sX),
      IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
        (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) F →
      ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of k)) (ψ : X ⟶ Z),
        IsContractionOfFace k sX sZ F ψ ∧ IsNormalVariety k sZ) :=
  ⟨exists_countable_isRationalCurve_closedConeOfCurves_eq hklt hΔ,
    fun _ hF _ _ _ hg L _ hL =>
      exists_isInvertible_iso_pullback_of_isContractionOfFace hklt hΔ hF hg L hL,
    fun _ hF => exists_isContractionOfFace_of_isNegativeExtremalFace hklt hΔ hF⟩

end MMP.Mori

end
