module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.RestrictedModelImage
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.ClopenCoverReduction

/-!
# Models of the fractional logarithmic complex restrict to open pieces

The restriction `K|_U` of a model `K` of the fractional logarithmic complex `C^•` on `V` to an
open `U` on which `D|_U` is relative simple normal crossing is a model of the fractional
logarithmic complex of the restricted data, with terms `(Fᵖ)|_U`. So the degeneration at `E₁` on
`V` reduces to the pieces of a decomposition of `V` into open and closed subschemes.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.isCModel_restrict`: a model restricts to a model on `U`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.componentsReduction`: the degeneration on `V` from
  retracts on the pieces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

/-- **A model of `C^•` restricts to a model of the restricted complex on any open `U` on which
`D|_U` is relative simple normal crossing.** -/
theorem isCModel_restrict (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S M : MMP.Mori.Divisor V) (N : ℕ)
    (u : Γ(V, cU' D M)) (U : V.Opens)
    (hDU : MMP.Mori.Divisor.IsRelativeSNC n (U.ι ≫ π) (restrictDivisor U D))
    (K : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ)
    (F : ℕ → V.Modules)
    (e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
      (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p))
    (ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D M W)))
    (hK : IsCModel n π D hD S M N u K F e ι) :
    IsCModel n (U.ι ≫ π) (restrictDivisor U D) hDU (restrictDivisor U S) (restrictDivisor U M) N
      (restrictSection U D M u) (((relRestrict π U).mapHomologicalComplex _).obj K)
      (restrictModelF U F) (restrictModelIso π U K F e) (restrictModelι π U D M F ι) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hK
  exact ⟨restrictModelι_injective π U D M F ι h1, restrictModelι_add π U D M F ι h2,
    restrictModelι_smul π U D M F ι h3, restrictModelι_map π U D M F ι h4,
    restrictModelι_range n π U D hD hDU S M F ι h5, restrictModelι_d π U D M N u K F e ι h6⟩

/-- **The degeneration on `V` from retracts on the pieces.** -/
theorem componentsReduction (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S M : MMP.Mori.Divisor V) (N : ℕ)
    (u : Γ(V, cU' D M)) :
    ComponentsReduction n π D hD S M N u :=
  componentsReduction_of_restrict n π D hD S M N u fun U hDU K F e ι hK =>
    ⟨_, _, _, isCModel_restrict n π D hD S M N u U hDU K F e ι hK⟩

end MMP.FourfoldProofs.FractionalLogComplexProof
