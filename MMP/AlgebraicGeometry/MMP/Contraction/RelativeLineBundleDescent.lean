module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.RelativeNegativeFace
public import MMP.AlgebraicGeometry.MMP.Contraction.LineBundleDescent
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Basic
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic

/-!
# Line bundles descend along a relative contraction

Let `f : X ⟶ Y` be a morphism of projective varieties over an algebraically closed field `k` of
characteristic zero, `(X, Δ)` a klt pair with `Δ` effective, `F` a `(K_X + Δ)`-negative extremal
face of the relative closed cone of curves `NE̅(X/Y)`, and `(ψ : X ⟶ Z, g : Z ⟶ Y)` a contraction
of `F` over `Y`. An invertible sheaf `L` on `X` of degree zero on every curve `C` contracted by
`f` with `[C] ∈ F` is isomorphic to `ψ^* L_Z` for an invertible sheaf `L_Z` on `Z`.

## Main results

* `MMP.Mori.exists_isInvertible_iso_pullback_of_isRelativeContractionOfFace`: the statement
  above.

## Implementation notes

A contraction over `Y` is `MMP.Mori.IsRelativeContractionOfFace`. The form
`w ↦ ((K_X + Δ) · w)` on `N₁(X/Y)` is the absolute form `MMP.Fourfold.QDivisor.curveForm` of
`K_X + Δ` composed with the natural map `MMP.Mori.relativeToAbsolute`, as in
`MMP.Mori.exists_isRelativeContractionOfFace_of_isNegativeExtremalFace`. A line bundle is an
invertible sheaf of `𝒪`-modules, `ψ^*` is `AlgebraicGeometry.Scheme.Modules.pullback ψ`, and
`(L · C)` is `MMP.Mori.ProperCurve.degree`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.25(4)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The natural map `N₁(X/Y) → N₁(X)` is injective. -/
private theorem relativeToAbsolute_injective {k : Type} [Field k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (f : X ⟶ Y) : Function.Injective (relativeToAbsolute sX f) := by
  intro a b h
  obtain ⟨W, rfl⟩ := relativeNumericalClass_surjective sX f a
  obtain ⟨W', rfl⟩ := relativeNumericalClass_surjective sX f b
  rw [isNaturalRelativeMap_relativeToAbsolute sX f W,
    isNaturalRelativeMap_relativeToAbsolute sX f W', OneCycle.numericalClass, Submodule.mkQ_apply,
    Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  rwa [relativeNumericalClass, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]

/-- The pull-back of an invertible sheaf on `Y` has degree zero on the image of every relative
class. -/
private theorem degree_relativeToAbsolute_pullback {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    (f : X ⟶ Y) (hf : f ≫ sY = sX) (H : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 H]
    (z : RelativeNumericalCurveClasses sX f) :
    NumericalCurveClasses.degree sX ((Scheme.Modules.pullback f).obj H)
      (relativeToAbsolute sX f z) = 0 := by
  obtain ⟨W, rfl⟩ := relativeNumericalClass_surjective sX f z
  rw [isNaturalRelativeMap_relativeToAbsolute sX f W, NumericalCurveClasses.degree_numericalClass,
    OneCycle.degree_apply]
  refine Finset.sum_eq_zero fun C hC => ?_
  dsimp only
  rw [ProperCurve.degree_pullback_eq_zero_of_isContractedBy f hf C
    ((Finsupp.mem_supported ℝ _).1 W.2 hC) H, Int.cast_zero, mul_zero]

/-- A scheme receiving a morphism `ψ` from an integral scheme with `ψ_* 𝒪_X = 𝒪_Z` is
integral. -/
private theorem isIntegral_of_isIso_app {X Z : Scheme} [IsIntegral X] (ψ : X ⟶ Z)
    (h : ∀ U : Z.Opens, IsIso (ψ.app U)) : IsIntegral Z := by
  obtain ⟨x⟩ := (IsIntegral.nonempty : Nonempty X)
  refine ⟨⟨ψ x⟩, fun U hU => ?_⟩
  have := h U
  let e := asIso (ψ.app U)
  have hne : Nonempty (ψ ⁻¹ᵁ U) := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have hbot : ψ ⁻¹ᵁ U = ⊥ :=
      SetLike.ext' (Set.eq_empty_iff_forall_notMem.2 fun x hx => hemp.false ⟨x, hx⟩)
    have : Subsingleton Γ(X, ψ ⁻¹ᵁ U) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hbot)
    have : Subsingleton Γ(Z, U) := e.commRingCatIsoToRingEquiv.toEquiv.subsingleton
    exact not_subsingleton Γ(Z, U) inferInstance
  exact MulEquiv.isDomain _ e.commRingCatIsoToRingEquiv.toMulEquiv

/-- **Line bundles descend along a relative contraction** (Kollár–Mori 3.25(4), setting
(3.21.0)). Let `f : X ⟶ Y` be a morphism of projective varieties over an algebraically closed
field `k` of characteristic zero, `(X, Δ)` a klt pair with canonical divisor `K` and `Δ ≥ 0`,
`F` a `(K + Δ)`-negative extremal face of `NE̅(X/Y)` (the form being
`w ↦ ((K + Δ) · MMP.Mori.relativeToAbsolute sX f w)`), `(ψ, g)` a contraction of `F` over `Y`,
and `L` an invertible sheaf on `X` with `deg_C L = 0` for every curve `C ⊆ X` with `f(C)` a point
and `[C] ∈ F`. Then `L ≅ ψ^* L_Z` for an invertible sheaf `L_Z` on `Z`. -/
@[mmp "thm_km3b_relative_cone_theorem_line_bundle"]
public theorem exists_isInvertible_iso_pullback_of_isRelativeContractionOfFace {k : Type}
    [Field k] {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {sY : Y ⟶ Spec (.of k)}
    {f : X ⟶ Y} (hf : IsProjectiveSetting k sX sY f)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hklt : IsKltPair sX n K Δ) (hΔ : 0 ≤ Δ)
    {F : Set (RelativeNumericalCurveClasses sX f)}
    (hF : IsNegativeExtremalFace ℝ
      (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f))
      ((MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2).comp
        (relativeToAbsolute sX f)) F)
    {Z : Scheme.{0}} {ψ : X ⟶ Z} {g : Z ⟶ Y} (hψ : IsRelativeContractionOfFace f F ψ g)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : ∀ (C : ProperCurve sX) (hC : C.IsContractedBy f), C.relativeClass f hC ∈ F →
      C.degree k L = 0) :
    ∃ LZ : Z.Modules, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 LZ ∧
      Nonempty (L ≅ (Scheme.Modules.pullback ψ).obj LZ) := by
  have := hf.isAlgClosed
  have := hf.charZero
  have : AlgebraicGeometry.IsProjectiveVariety k sX := hf.isProjectiveVariety_source
  have hY : AlgebraicGeometry.IsProjectiveVariety k sY := hf.isProjectiveVariety_target
  have hface := isNegativeExtremalFace_image_relativeToAbsolute hf hklt hΔ hF
  have hψf : ∀ C : ProperCurve sX, C.IsContractedBy ψ → C.IsContractedBy f := by
    intro C hC x hx
    rw [← hψ.comp_eq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]
  have hcontr : ∀ C : ProperCurve sX, C.IsContractedBy ψ ↔
      OneCycle.numericalClass sX (C.cycle ℝ) ∈ relativeToAbsolute sX f '' F := by
    intro C
    refine ⟨fun hC => ⟨C.relativeClass f (hψf C hC),
      (hψ.isContractedBy_iff C (hψf C hC)).1 hC, rfl⟩, ?_⟩
    rintro ⟨z, hz, hzC⟩
    obtain ⟨H, _, hH⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety
      hf.isProjectiveVariety_target
    have hdeg := degree_relativeToAbsolute_pullback f hf.comp_eq H z
    rw [hzC, NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle] at hdeg
    have hCf : C.IsContractedBy f :=
      MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero f hf.comp_eq H hH C
        (by exact_mod_cast hdeg)
    refine (hψ.isContractedBy_iff C hCf).2 ?_
    have : relativeToAbsolute sX f (C.relativeClass f hCf) = relativeToAbsolute sX f z :=
      hzC.symm ▸ rfl
    rwa [relativeToAbsolute_injective sX f this]
  have hZint : IsIntegral Z := isIntegral_of_isIso_app ψ hψ.isIso_app
  have hcomp : IsProjectiveMorphism (g ≫ sY) := hψ.isProjectiveMorphism.comp hY.isProjective
  have := isProper_of_isProjectiveMorphism _ hcomp
  have : AlgebraicGeometry.IsVariety k (g ≫ sY) := AlgebraicGeometry.IsVariety.mk
  have hψc : IsContractionOfFace k sX (g ≫ sY) (relativeToAbsolute sX f '' F) ψ :=
    { isProjectiveVariety_source := hf.isProjectiveVariety_source
      isProjectiveVariety_target :=
        (AlgebraicGeometry.isProjectiveVariety_iff k _).2 ⟨inferInstance, hcomp⟩
      comp_eq := by rw [← Category.assoc, hψ.comp_eq, hf.comp_eq]
      isExtremalFace := hface.1
      isContractedBy_iff := hcontr
      isIso_app := hψ.isIso_app }
  refine exists_isInvertible_iso_pullback_of_isContractionOfFace hklt
    (DivisorWithCoeffs.isEffective_iff_nonneg.2 hΔ) hface hψc L fun C hC => ?_
  have hCψ := (hcontr C).2 hC
  exact hL C (hψf C hCψ) ((hψ.isContractedBy_iff C (hψf C hCψ)).1 hCψ)

end MMP.Mori

end
