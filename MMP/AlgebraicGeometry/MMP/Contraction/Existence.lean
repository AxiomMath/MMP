module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.NegativeFaceSupportingDivisor
public import MMP.AlgebraicGeometry.MMP.Contraction.SupportingDivisorFree
import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafInvertible

/-!
# The contraction theorem

Let `X` be a projective variety over an algebraically closed field `k` of characteristic zero
and `(X, Δ)` a klt pair with `Δ` effective. Every `(K_X + Δ)`-negative extremal face `F` of the
closed cone of curves `NE̅(X)` has a contraction: a morphism `ψ : X ⟶ Z` of `k`-schemes onto a
normal projective variety `Z` with `ψ_* 𝒪_X = 𝒪_Z`, contracting a curve `C ⊆ X` to a point
exactly when `[C] ∈ F`.

The face `F` has a supporting divisor `D`, and `𝒪_X(bD)` is globally generated for some `b ≥ 1`.
A basis of its global sections defines a `k`-morphism `φ : X ⟶ ℙᴺ_k` with
`φ^* 𝒪(1) ≅ 𝒪_X(bD)`. In the Stein factorization `φ = h ∘ ψ`, the first factor `ψ : X ⟶ Z` is a
contraction of `F`; `Z` is normal because `X` is.

## Main results

* `MMP.Mori.exists_isContractionOfFace_of_isNegativeExtremalFace`: the contraction theorem.

## Implementation notes

A contraction of `F` is `MMP.Mori.IsContractionOfFace`, which already records that the target is
a projective variety; normality of the target is the extra conjunct
`MMP.Mori.IsNormalVariety`. A `(K_X + Δ)`-negative extremal face is
`MMP.Mori.IsNegativeExtremalFace` for the form `MMP.Fourfold.QDivisor.curveForm` of `K_X + Δ`,
which is `ℚ`-Cartier by the pair condition; it is in particular a convex cone, which is needed
(on `ℙ¹ × ℙ¹` the union of the two rulings' rays is extremal and `K`-negative but has no
contraction).

The morphism to projective space is `Stacks.ProjectiveFromSections.toProjectiveSpaceOver`, into
the projective space `projectiveSpaceOver N (Spec k)` over the base, with its ample twisting
sheaf; the contraction property of the Stein factor is
`MMP.Mori.isContractionOfFace_of_isSupportingDivisor_of_isAmple`, stated for any ample
invertible sheaf on a proper `k`-scheme.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 3.7(3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MMP.Mori

/-- **Contraction theorem** (Kollár–Mori 3.7(3)). Let `X` be a projective variety over an
algebraically closed field `k` of characteristic zero, `(X, Δ)` a klt pair with canonical
divisor `K` and `Δ` effective, and `F` a `(K + Δ)`-negative extremal face of `NE̅(X)`. Then there
is a contraction `ψ : X ⟶ Z` of `F` onto a normal projective variety `Z` over `k`. -/
@[mmp "thm_km3b_contraction_theorem"]
public theorem exists_isContractionOfFace_of_isNegativeExtremalFace {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective) {F : Set (NumericalCurveClasses sX)}
    (hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) F) :
    ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of k)) (ψ : X ⟶ Z),
      IsContractionOfFace k sX sZ F ψ ∧ IsNormalVariety k sZ := by
  obtain ⟨D, hD⟩ := exists_isSupportingDivisor_of_isNegativeExtremalFace hklt hΔ hF
  obtain ⟨b₀, hb₀⟩ := exists_isGloballyGenerated_sheaf_nsmul_of_isSupportingDivisor hklt hΔ hF hD
  set b := b₀ + 1
  set L := MMP.CartierDivisor.sheaf (b • D)
  have hL : MMP.Intersection.IsGloballyGenerated L := hb₀ b b₀.le_succ
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    MMP.CartierDivisor.isInvertible_sheaf (b • D)
  obtain ⟨N, t, ht, -⟩ :=
    AlgebraicGeometry.exists_fin_basis_generatesStalks_of_generatesStalks_id sX L
      hL.generatesStalks_id
  obtain ⟨θ, -⟩ :=
    AlgebraicGeometry.exists_iso_projectiveSpaceTwistingSheaf_toProjectiveSpaceOver t ht sX
  let φ := Stacks.ProjectiveFromSections.toProjectiveSpaceOver t ht sX
  let sP : projectiveSpaceOver N (Spec (.of k)) ⟶ Spec (.of k) :=
    pullback.fst (terminal.from _) (terminal.from (projectiveSpaceAtUniverse.{0} N))
  have hφ : φ ≫ sP = sX := Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst t ht sX
  have : IsProper sP := isProper_projectiveSpaceOver N _
  have : IsProper (φ ≫ sP) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp φ sP
  let O := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of k))
  have hO : Scheme.Modules.IsAmple _ O :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr
      (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf N (Spec (.of k)))
  obtain ⟨Z, ψ, h, ⟨hS⟩, -, -, hψ, -, hfin, hvar, -, hnorm, -⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isVariety sX sP φ hφ
  exact ⟨Z, h ≫ sP, ψ, isContractionOfFace_of_isSupportingDivisor_of_isAmple k sX inferInstance
    hF.1 hD b₀.succ_pos sP O hO φ hφ θ ψ h hS.comp hvar hψ, hvar, hnorm inferInstance⟩

end MMP.Mori

end
