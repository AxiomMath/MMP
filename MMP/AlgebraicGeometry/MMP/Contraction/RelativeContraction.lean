module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.RelativeNegativeFace

section

/-!
# The relative contraction theorem

Let `f : X ⟶ Y` be a morphism of projective varieties over an algebraically closed field `k` of
characteristic zero and `(X, Δ)` a klt pair with `Δ` effective. Every `(K_X + Δ)`-negative
extremal face `F` of the relative closed cone of curves `NE̅(X/Y)` has a contraction over `Y`:
morphisms `ψ : X ⟶ Z` and `g : Z ⟶ Y` with `g` projective, `ψ ≫ g = f` and `ψ_* 𝒪_X = 𝒪_Z`,
such that a curve `C ⊆ X` contracted by `f` is contracted by `ψ` exactly when its class in
`N₁(X/Y)` lies in `F`.

## Main results

* `MMP.Mori.exists_isRelativeContractionOfFace_of_isNegativeExtremalFace`: the statement above.

## Implementation notes

A contraction over `Y` is `MMP.Mori.IsRelativeContractionOfFace`. The form
`w ↦ ((K_X + Δ) · w)` on `N₁(X/Y)` is the absolute form `MMP.Fourfold.QDivisor.curveForm` of
`K_X + Δ` composed with the natural map `MMP.Mori.relativeToAbsolute`, as in
`MMP.Mori.isNegativeExtremalFace_image_relativeToAbsolute`.

The image `ι(F)` of `F` under the natural map `ι : N₁(X/Y) → N₁(X)` is a `(K_X + Δ)`-negative
extremal face of `NE̅(X)`, which has a contraction `ψ : X ⟶ Z`. The degree of the pull-back
`f^* A` of an ample invertible sheaf `A` on `Y` vanishes on `N₁(X/Y)`, so every curve contracted
by `ψ` is contracted by `f`, and `f` factors as `ψ ≫ g` by the rigidity factorization
`MMP.Mori.existsUnique_comp_eq_of_isContractedBy`. A morphism between projective `k`-varieties
is projective, which gives the projectivity of `g` and of `ψ`. Since `ι` is injective, a curve
contracted by `f` is contracted by `ψ` exactly when its relative class lies in `F`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.21, 3.25(3)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

/-- The degree of the pull-back `f^* L` of an invertible sheaf `L` on `Y` vanishes on
`N₁(X/Y)`. -/
theorem RelativeNumericalCurveClasses.degree_pullback_eq_zero {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY]
    [LocallyOfFiniteType sY] (f : X ⟶ Y) (hf : f ≫ sY = sX) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (w : RelativeNumericalCurveClasses sX f) :
    RelativeNumericalCurveClasses.degree sX f ((Scheme.Modules.pullback f).obj L) w = 0 := by
  classical
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f w
  rw [RelativeNumericalCurveClasses.degree_relativeNumericalClass, OneCycle.degree_apply,
    Finsupp.sum]
  refine Finset.sum_eq_zero fun C hC => ?_
  rw [ProperCurve.degree_pullback_eq_zero_of_isContractedBy f hf C
    ((Finsupp.mem_supported ℝ (Z : OneCycle ℝ sX)).mp Z.2 hC) L]
  simp

/-- **Relative contraction theorem** (Kollár–Mori 3.25(3), setting (3.21.0)). Let `f : X ⟶ Y`
be a morphism of projective varieties over an algebraically closed field `k` of characteristic
zero and `(X, Δ)` a klt pair with canonical divisor `K` and `Δ ≥ 0`. If `F` is a
`(K + Δ)`-negative extremal face of `NE̅(X/Y)`, the form being
`w ↦ ((K + Δ) · MMP.Mori.relativeToAbsolute sX f w)`, then `F` has a contraction `(ψ, g)` over
`Y`, with `ψ : X ⟶ Z` and `g : Z ⟶ Y`. -/
@[mmp "thm_km3b_relative_cone_theorem_contraction"]
public theorem exists_isRelativeContractionOfFace_of_isNegativeExtremalFace {k : Type} [Field k]
    {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {sY : Y ⟶ Spec (.of k)}
    {f : X ⟶ Y} (hf : IsProjectiveSetting k sX sY f)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hklt : IsKltPair sX n K Δ) (hΔ : 0 ≤ Δ)
    {F : Set (RelativeNumericalCurveClasses sX f)}
    (hF : IsNegativeExtremalFace ℝ
      (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f))
      ((MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2).comp
        (relativeToAbsolute sX f)) F) :
    ∃ (Z : Scheme.{0}) (ψ : X ⟶ Z) (g : Z ⟶ Y), IsRelativeContractionOfFace f F ψ g := by
  haveI := hf.isAlgClosed
  haveI := hf.charZero
  have hX := hf.isProjectiveVariety_source
  have hY := hf.isProjectiveVariety_target
  haveI : AlgebraicGeometry.IsProjectiveVariety k sX := hX
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hX.isProjective
  haveI : IsProper sY := isProper_of_isProjectiveMorphism _ hY.isProjective
  haveI : IsSeparated sY := hY.toIsSeparated
  have hF' := isNegativeExtremalFace_image_relativeToAbsolute hf hklt hΔ hF
  obtain ⟨Z, sZ, ψ, hψ, -⟩ :=
    exists_isContractionOfFace_of_isNegativeExtremalFace hklt hΔ hF'
  have hZ := hψ.isProjectiveVariety_target
  haveI : IsSeparated sZ := hZ.toIsSeparated
  obtain ⟨A, hAinv, hA⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hY
  have hcurve : ∀ C : ProperCurve sX, C.IsContractedBy ψ → C.IsContractedBy f := by
    intro C hC
    obtain ⟨w, -, hwC⟩ := (hψ.isContractedBy_iff C).mp hC
    refine MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero f hf.comp_eq A hA C ?_
    have h0 := RelativeNumericalCurveClasses.degree_pullback_eq_zero f hf.comp_eq A w
    obtain ⟨W, rfl⟩ := relativeNumericalClass_surjective sX f w
    have h1 : OneCycle.degree ℝ sX ((Scheme.Modules.pullback f).obj A) (C.cycle ℝ) = 0 := by
      rw [← NumericalCurveClasses.degree_numericalClass, ← hwC]
      exact h0
    rw [OneCycle.degree_cycle] at h1
    exact_mod_cast h1
  have hψp : IsProjectiveMorphism ψ := IsProjectiveMorphism.of_comp ψ sZ
    (hψ.comp_eq ▸ hX.isProjective)
  haveI : IsProper ψ := isProper_of_isProjectiveMorphism _ hψp
  haveI : ∀ U, IsIso (ψ.c.app U) := fun U => hψ.isIso_app U.unop
  haveI : IsIso ψ.c := NatIso.isIso_of_isIso_app _
  haveI : Surjective ψ := VectorBundleCodimensionOne.surjective_of_isIso_cMap ψ inferInstance
  obtain ⟨g, hg, -⟩ := existsUnique_comp_eq_of_isContractedBy hX hZ hY hψp hψ.comp_eq
    hf.comp_eq hcurve
  have hgY : g ≫ sY = sZ :=
    (MMP.existsUnique_comp_eq_of_isIso_c ψ sX fun _ _ _ => Subsingleton.elim _ _).unique
      (by rw [← Category.assoc, hg, hf.comp_eq]) hψ.comp_eq
  refine ⟨Z, ψ, g, ⟨hF.1, IsProjectiveMorphism.of_comp g sY (hgY ▸ hZ.isProjective), hg,
    hψ.isIso_app, fun C hC => ?_⟩⟩
  rw [hψ.isContractedBy_iff C]
  exact (isNaturalRelativeMap_relativeToAbsolute sX f).injective.mem_set_image
    (a := C.relativeClass f hC)

end MMP.Mori

end
