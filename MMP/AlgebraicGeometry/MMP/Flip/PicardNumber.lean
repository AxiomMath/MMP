module

public import MMP.AlgebraicGeometry.MMP.Flip.QFactorial
public import MMP.AlgebraicGeometry.Intersection.SmallModificationPicardNumber

/-!
# The Picard number is preserved by a flip

Let `(X, Δ)` be a projective `ℚ`-factorial dlt pair over an algebraically closed field `k` of
characteristic zero, `R` a `(K_X + Δ)`-negative extremal ray of `NE̅(X)`, `g : X ⟶ Y` a
contraction of `R`, and `g⁺ : X⁺ ⟶ Y` a `(K + Δ)`-flip of `g`. Then `ρ(X⁺) = ρ(X)`.

The flip `X⁺` is projective (`g⁺` is proper and carries a relatively ample invertible sheaf over
the projective variety `Y`) and `ℚ`-factorial (`MMP.Mori.isQFactorial_of_isFlip`). Over the
complement of the flipping locus `W ⊆ Y` both `g` and `g⁺` are isomorphisms, and `g⁻¹(W)`,
`(g⁺)⁻¹(W)` have codimension at least two
(`MMP.Positivity.IsFlip.exists_isClosed_image_exceptionalSet`). So `X` and `X⁺` are isomorphic
over `k` outside closed subsets of codimension at least two, and small modifications of
`ℚ`-factorial projective varieties preserve the Picard number
(`MMP.Fourfold.picardNumber_eq_of_isoInCodimOne`).

## Main results

* `MMP.Mori.picardNumber_eq_of_isFlip`: `ρ(X⁺) = ρ(X)`.

## Implementation notes

The Picard number is `MMP.Mori.picardNumber`, valued in `ℕ∞`; for projective `X` it is finite,
so the equality in `ℕ∞` is the equality of the source.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori],
  Proposition 3.37(2)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

/-- **The Picard number is preserved by a flip** (Kollár–Mori, Proposition 3.37(2)). Let
`(X, Δ)` be a projective `ℚ`-factorial dlt pair over an algebraically closed field of
characteristic zero with canonical divisor `K`, `R` a `(K + Δ)`-negative extremal ray of
`NE̅(X)`, `g : X ⟶ Y` a contraction of `R`, and `g⁺ : X⁺ ⟶ Y` a `(K + Δ)`-flip of `g`. Then
`ρ(X⁺) = ρ(X)`. -/
@[mmp "lem_mmp_foundation_km_flip_picard_number_via_numerical_duality"]
public theorem picardNumber_eq_of_isFlip
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [hXp : AlgebraicGeometry.IsProjectiveVariety k sX]
    (hQ : MMP.Fourfold.IsQFactorial sX) {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hdlt : IsDltPair sX n K Δ) {R : Set (NumericalCurveClasses sX)}
    (hRay : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    (hR : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hdlt.1.2.2) R)
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)} {g : X ⟶ Y}
    (hg : IsContractionOfFace k sX sY R g)
    {X' : Scheme.{0}} [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX' : X' ⟶ Spec (.of k)} {gp : X' ⟶ Y} (hflip : IsFlip sX sY sX' K Δ g gp) :
    picardNumber sX' = picardNumber sX := by
  have hQ' := isQFactorial_of_isFlip hQ hdlt hRay hR hg hflip
  have hYp : MMP.Mori.IsProjectiveVariety k sY := hg.isProjectiveVariety_target
  have hX'p : MMP.Mori.IsProjectiveVariety k sX' := by
    haveI : AlgebraicGeometry.IsVariety k sX' := hflip.isNormalVariety.1
    haveI : IsProper gp := hflip.isProper
    obtain ⟨-, -, L, hL, -, hLa⟩ := hflip.hasRelativelyAmpleMultiple
    haveI := hL.isInvertibleModule_divisorialSheaf
    have htfY := isProjective_tfae_seven_of_exists_isAmple sY
      ⟨Stacks.Ample.unitModule _, inferInstance, Stacks.Ample.isAmple_unitModule_of_isAffine _⟩
    obtain ⟨-, A, hAi, hAamp⟩ := (htfY.out 2 5).mp hYp.isProjective
    have htf := isProjective_tfae_seven_of_exists_isAmple gp ⟨A, hAi, hAamp⟩
    have hgp : IsProjectiveMorphism gp := by
      refine (htf.out 6 2).mp ?_
      show IsProper gp ∧ _
      exact ⟨hflip.isProper, L.divisorialSheaf, inferInstance,
        Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple gp _
          inferInstance hLa⟩
    refine ⟨?_⟩
    rw [← hflip.comp_eq]
    exact IsProjectiveMorphism.comp hgp hYp.isProjective
  obtain ⟨hW, hbf, hbp, hcf, hcp, -⟩ :=
    MMP.Positivity.IsFlip.exists_isClosed_image_exceptionalSet hflip
  set U : Y.Opens := ⟨_, hW.isOpen_compl⟩
  haveI : IsIso (g ∣_ U) := hbf
  haveI : IsIso (gp ∣_ U) := hbp
  let e : (g ⁻¹ᵁ U).toScheme ≅ (gp ⁻¹ᵁ U).toScheme := asIso (g ∣_ U) ≪≫ (asIso (gp ∣_ U)).symm
  refine (MMP.Fourfold.picardNumber_eq_of_isoInCodimOne sX sX' hQ hXp hQ' hX'p _ _ hcf hcp e
    ?_).symm
  change ((g ∣_ U) ≫ inv (gp ∣_ U)) ≫ (gp ⁻¹ᵁ U).ι ≫ sX' = (g ⁻¹ᵁ U).ι ≫ sX
  rw [← hflip.comp_eq, ← hflip.isFlippingContraction.comp_eq]
  simp only [← morphismRestrict_ι_assoc, Category.assoc, IsIso.inv_hom_id_assoc]

end MMP.Mori

end
