module

public import StacksFrontier.AlgebraicGeometry.CartierAffineLocalConverse.Basic
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.StacksBundleCharts
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.StacksThomClass
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksSection

/-!
# A section with zero scheme everything is the zero section

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.eq_bot_of_support_eq_top'`: on a reduced scheme, an
  ideal sheaf whose support is everything is `⊥`.
* `MMP.Modules.eq_zeroSection_of_zeroLocus_eq_bot`: a section with `Z(σ) = X` is zero.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1 (proof of Lemma 19.1.3).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace MMP.Modules

variable {X : Scheme.{0}} {E : X.Modules} [E.IsQuasicoherent]

/-- On a reduced scheme, an ideal sheaf whose support is everything is `⊥`. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.eq_bot_of_support_eq_top' [IsReduced X]
    (I : X.IdealSheafData) (h : I.support = ⊤) : I = ⊥ := by
  refine le_bot_iff.mp ?_
  calc I ≤ I.radical := Scheme.IdealSheafData.le_radical _
    _ = Scheme.IdealSheafData.vanishingIdeal I.support :=
        Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = ⊥ := by
        rw [h, ← Scheme.IdealSheafData.support_bot, Scheme.IdealSheafData.vanishingIdeal_support,
          Scheme.IdealSheafData.radical_bot]
        exact Scheme.nilradical_eq_bot

/-- **A section whose zero scheme is all of `X` is the zero section.** If `Z(σ) = X`, the
section factors through the zero section `0 : X ⟶ 𝐕(ℰ)`, a closed immersion, and the
factorization is a section of `0 ≫ π = 𝟙`, hence the identity. -/
theorem eq_zeroSection_of_zeroLocus_eq_bot {σ : X ⟶ totalSpace E} (hσ : σ ≫ proj E = 𝟙 X)
    (h : zeroLocus E σ = ⊥) : σ = zeroSection E := by
  have h' : (zeroSection E).ker.comap σ ≤ ⊥ := h.le
  have hle : (zeroSection E).ker ≤ σ.ker := by
    have := (Scheme.IdealSheafData.le_map_iff_comap_le (I := ⊥) (f := σ)
      (J := (zeroSection E).ker)).2 h'
    rwa [Scheme.IdealSheafData.map_bot] at this
  have hτ := IsClosedImmersion.lift_fac (zeroSection E) σ hle
  have h1 : IsClosedImmersion.lift (zeroSection E) σ hle = 𝟙 X := by
    have := congrArg (· ≫ proj E) hτ
    simp only [Category.assoc, hσ] at this
    have hz : zeroSection E ≫ proj E = 𝟙 X :=
      Scheme.Modules.vectorBundleZeroSection_comp_vectorBundleToBase X E
    rwa [hz, Category.comp_id] at this
  rw [← hτ, h1, Category.id_comp]

end MMP.Modules
