module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Construction

/-!
# The residue of the connection of the model of `C^•`

Let `π : V ⟶ Spec ℂ` carry the data of the fractional logarithmic complex
`C^• = 𝒪_V(-M) · Ω^•_V(log D)(-S)`, and let `u` be the unit `ψ` on `U' = V ∖ (D ∪ Supp M)`,
`c = (N u)⁻¹`. The model of `C^•` is the complex
`MMP.FourfoldProofs.FractionalLogComplexProof.cCx` of the sheaves `C^p` with the connection
`∇ = d - c du ∧`, its terms embedded into the forms on `U'` by
`MMP.FourfoldProofs.FractionalLogComplexProof.tr`. The statement below is the residue clause of
`MMP.Mori.Divisor.finrank_hypercohomology_eq_sum_of_fractionalLogComplex` for this model: along a
component `E` of `Supp Bn`, with local equation `t` on an affine open meeting no other component
of `D`, the form `N ∇a - Bn(E) a dt/t` is a regular `1`-form with coefficients in `𝒪_V(-M)`,
multiplied out by `t`.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.ResidueSpec`: the residue clause for the model.

## Implementation notes

The body is the predicate `HasRes`, with `K`, `F`, `e`, `ι` the model:
`cCx`, `cMod`, the identity of `cX p`, and `tr`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

/-- **The residue of `∇` along a component `E` of `Supp Bn` is `Bn(E)/N`**, for the model
`cCx` of `C^•`. -/
def ResidueSpec (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S Bn M : MMP.Mori.Divisor V) (N : ℕ)
    (uu cc : Γ(V, cU' D M)) (hst : NabStable n π D hD S M uu cc) (hloc : LocMon n π D hD S M)
    (hcu : ∀ W : V.Opens, δ ((cU D).ι ≫ π) (OO D M W) (resU W cc) *
      δ ((cU D).ι ≫ π) (OO D M W) (resU W uu) = 0) : Prop :=
  let K := cCx n π D hD S M uu cc hst hloc hcu
  let F : ℕ → V.Modules := cMod n π D hD S M
  let e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
      (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p) := fun _ => Iso.refl _
  let ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D M W)) := fun p W x => tr π D M (p : ℤ) W x.1
  let U : V.Opens := D.supp.compl
  let U' : V.Opens := (D.supp ⊔ M.supp).compl
  let A := Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ π)
  let B := A.toPresheafGradedAlgebra
  let O : V.Opens → U.toScheme.Opens := fun W => U.ι ⁻¹ᵁ (W ⊓ U')
  let res : ∀ W : V.Opens, Γ(V, W) → Γ(U.toScheme, O W) := fun W a =>
    U.ι.app (W ⊓ U') (V.presheaf.map (homOfLE inf_le_left).op a)
  let dF : ∀ W : U.toScheme.Opens, Γ(U.toScheme, W) → (A.piece 1).val.obj (op W) := fun W a =>
    (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials (U.ι ≫ π))).val.app
      (op W) ((Scheme.Hom.universalRelativeDerivation (U.ι ≫ π)).d (X := op W) a)
  ∀ E : MMP.Mori.PrimeDivisor V, Bn E ≠ 0 → ∀ (W : V.affineOpens) (t : Γ(V, (W : V.Opens))),
    E.idealSheaf.ideal W = Ideal.span {t} →
    (∀ E' ∈ D.support, E' ≠ E → ∀ y ∈ (W : V.Opens), y ∉ E'.support) →
    ∀ (x : (K.X 0).val.obj (op (W : V.Opens))), ∀ y ∈ (W : V.Opens),
      ∃ (W' : V.affineOpens) (h : (W' : V.Opens) ≤ W), y ∈ (W' : V.Opens) ∧
      ∃ (m : ℕ) (g : Fin m → Γ(V, (W' : V.Opens) ⊓ U')) (f h' : Fin m → Γ(V, (W' : V.Opens))),
        (∀ i, ∃ a ∈ (-M).divisorialSubmodule (W' : V.Opens),
          (MMP.Mori.rationalFunctionsPresheaf V).map (homOfLE inf_le_left).op a =
            (MMP.Mori.toRationalFunctionsPresheaf V).app (op ((W' : V.Opens) ⊓ U')) (g i)) ∧
        let r := (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right U' h))).op
        let tW' := res W' (V.presheaf.map (homOfLE h).op t)
        B.structureMap (op (O W')) tW' *
            (N • B.incl ((1 : ℕ) : ℤ) ((A.piece ((1 : ℕ) : ℤ)).val.map r
              (ι 1 W ((e 1).hom.val.app (op W) ((K.d 0 1).val.app (op W) x))))) -
          Bn E • (B.incl ((0 : ℕ) : ℤ) ((A.piece ((0 : ℕ) : ℤ)).val.map r
              (ι 0 W ((e 0).hom.val.app (op W) x))) * B.incl 1 (dF (O W') tW')) =
        B.structureMap (op (O W')) tW' *
          ∑ i, B.structureMap (op (O W')) (U.ι.app ((W' : V.Opens) ⊓ U') (g i) * res W' (f i)) *
            B.incl 1 (dF (O W') (res W' (h' i)))

end MMP.FourfoldProofs.FractionalLogComplexProof
