module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.RestrictedModelForms

/-!
# A model of the fractional logarithmic complex restricts to an open piece: scalars

Let `U` be an open of `V`. A function `r` on an open `W` of `U` acts on the sections of `Fᵖ|_U`
over `W` as the function `(ι_U)_* r` on `ι(W)` acts on the sections of `Fᵖ`, and its restriction
to `W ∩ U'|_U`, read on `U ∖ D|_U`, is the restriction of `(ι_U)_* r` to `ι(W) ∩ U'`, read on
`V ∖ D`. So the restricted embedding of a model is linear over functions.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceRingEquiv_symm_res`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.pieceRingEquiv_symm_uW`:
  functions of the model on `V ∖ D`, read on `U ∖ D|_U`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.restrictModelι_smul`: the restricted embedding is linear
  over functions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

section Functions

variable {V : Scheme.{0}} (U : V.Opens) (D M : MMP.Mori.Divisor V)

/-- The preimage under `U.ι` of `pieceOpen U D M W` is
`W ⊓ cU' (restrictDivisor U D) (restrictDivisor U M)`. -/
theorem preimage_pieceOpen_eq (W : U.toScheme.Opens) :
    U.ι ⁻¹ᵁ pieceOpen U D M W = W ⊓ cU' (restrictDivisor U D) (restrictDivisor U M) := by
  change U.ι ⁻¹ᵁ (U.ι ''ᵁ W) ⊓ U.ι ⁻¹ᵁ cU' D M = _
  rw [cU'_restrictDivisor, U.ι.preimage_image_eq]

/-- Pulling back along `U.ι` the restriction of `(U.ι.appIso W).inv r` to `pieceOpen U D M W`
gives the restriction of `r` to `U.ι ⁻¹ᵁ pieceOpen U D M W`. -/
theorem app_presheaf_map_appIso_inv (W : U.toScheme.Opens) (r : Γ(U.toScheme, W)) :
    (U.ι.app (pieceOpen U D M W)).hom
        (V.presheaf.map (homOfLE inf_le_left).op ((U.ι.appIso W).inv r)) =
      U.toScheme.presheaf.map
        (homOfLE ((preimage_pieceOpen_eq U D M W).le.trans inf_le_left)).op r := by
  have h := congrArg (fun φ => φ.hom r) (U.ι.appIso_inv_appLE (U := W)
    (V := U.ι ⁻¹ᵁ pieceOpen U D M W)
    ((preimage_pieceOpen_eq U D M W).le.trans (inf_le_left.trans (U.ι.preimage_image_eq W).ge)))
  refine Eq.trans ?_ h
  simp only [Scheme.Hom.appLE, CommRingCat.comp_apply]
  exact (presheaf_map_app U.ι inf_le_left _ _).symm

/-- Restricting to `OO (restrictDivisor U D) (restrictDivisor U M) W` the image of a function `r`
on `W` under `(pieceRingEquiv …).symm` gives the restriction of `r` to the model's open. -/
theorem pieceRingEquiv_symm_res (W : U.toScheme.Opens) (r : Γ(U.toScheme, W)) :
    (cU (restrictDivisor U D)).toScheme.presheaf.map (homOfLE (OO_restrictDivisor U D M W).le).op
      ((pieceRingEquiv U D (pieceOpen U D M W) (pieceOpen_le U D M W)).symm
        ((cU D).ι.app (U.ι ''ᵁ W ⊓ cU' D M)
          (V.presheaf.map (homOfLE inf_le_left).op ((U.ι.appIso W).inv r)))) =
      (cU (restrictDivisor U D)).ι.app (W ⊓ cU' (restrictDivisor U D) (restrictDivisor U M))
        (U.toScheme.presheaf.map (homOfLE inf_le_left).op r) := by
  rw [← pieceRingEquiv_app U D (pieceOpen U D M W) (pieceOpen_le U D M W),
    RingEquiv.symm_apply_apply, app_presheaf_map_appIso_inv,
    presheaf_map_app _ (preimage_pieceOpen_eq U D M W).ge,
    MMP.FourfoldProofs.LogDegenerationProof.presheaf_map_comp_apply']

/-- Restricting to `OO (restrictDivisor U D) (restrictDivisor U M) W` the image of a section `u`
of `𝒪_V` on `cU' D M` under `(pieceRingEquiv …).symm` gives the restriction of
`restrictSection U D M u`. -/
theorem pieceRingEquiv_symm_uW (W : U.toScheme.Opens) (u : Γ(V, cU' D M)) :
    (cU (restrictDivisor U D)).toScheme.presheaf.map (homOfLE (OO_restrictDivisor U D M W).le).op
      ((pieceRingEquiv U D (pieceOpen U D M W) (pieceOpen_le U D M W)).symm
        ((cU D).ι.app (U.ι ''ᵁ W ⊓ cU' D M) (V.presheaf.map (homOfLE inf_le_right).op u))) =
      (cU (restrictDivisor U D)).ι.app (W ⊓ cU' (restrictDivisor U D) (restrictDivisor U M))
        (U.toScheme.presheaf.map (homOfLE inf_le_right).op (restrictSection U D M u)) := by
  rw [← pieceRingEquiv_app U D (pieceOpen U D M W) (pieceOpen_le U D M W),
    RingEquiv.symm_apply_apply, ← presheaf_map_app U.ι (inf_le_right : pieceOpen U D M W ≤ _)
      (homOfLE (U.ι.preimage_mono inf_le_right)).op,
    presheaf_map_app _ (preimage_pieceOpen_eq U D M W).ge,
    MMP.FourfoldProofs.LogDegenerationProof.presheaf_map_comp_apply', restrictSection,
    MMP.FourfoldProofs.LogDegenerationProof.presheaf_map_comp_apply' _ _
      (homOfLE (inf_le_right.trans (cU'_restrictDivisor U D M).le)).op]

end Functions

section Smul

variable {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ)) (U : V.Opens)
  (D M : MMP.Mori.Divisor V) (F : ℕ → V.Modules)
  (ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W)))

/-- `pieceTotalRestrict_structureMap`, with the open of `V` spelled as in the model. -/
theorem pieceTotalRestrict_structureMap' (W : U.toScheme.Opens)
    (c : Γ((cU D).toScheme, OO D M (U.ι ''ᵁ W))) :
    pieceTotalRestrict π U D M W
        ((Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU D).ι ≫ π)).toPresheafGradedAlgebra.structureMap (op (OO D M (U.ι ''ᵁ W))) c) =
      (Scheme.Hom.relativeDifferentialFormsAlgebra
        ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.structureMap
          (op (OO (restrictDivisor U D) (restrictDivisor U M) W))
          ((cU (restrictDivisor U D)).toScheme.presheaf.map
            (homOfLE (OO_restrictDivisor U D M W).le).op
            ((pieceRingEquiv U D (pieceOpen U D M W) (pieceOpen_le U D M W)).symm c)) := by
  have e : (Scheme.Hom.relativeDifferentialFormsAlgebra
      ((cU D).ι ≫ π)).toPresheafGradedAlgebra.structureMap (op (OO D M (U.ι ''ᵁ W))) c =
      (Scheme.Hom.relativeDifferentialFormsAlgebra
        ((cU D).ι ≫ π)).toPresheafGradedAlgebra.structureMap
        (op ((cU D).ι ⁻¹ᵁ pieceOpen U D M W)) c := rfl
  exact (congrArg (pieceTotalRestrict π U D M W) e).trans
    (pieceTotalRestrict_structureMap π U D M W c)

/-- If the embedding `ι` of a model is linear over functions, then so is the restricted
embedding `restrictModelι π U D M F ι`. -/
theorem restrictModelι_smul
    (hι : ∀ (p : ℕ) W (r : V.ringCatSheaf.obj.obj (op W)) x,
      (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).toPresheafGradedAlgebra.incl
          (p : ℤ) (ι p W (r • x)) =
        (Scheme.Hom.relativeDifferentialFormsAlgebra
            ((cU D).ι ≫ π)).toPresheafGradedAlgebra.structureMap (op (OO D M W))
            ((cU D).ι.app (W ⊓ cU' D M) (V.presheaf.map (homOfLE inf_le_left).op r)) *
          (Scheme.Hom.relativeDifferentialFormsAlgebra
            ((cU D).ι ≫ π)).toPresheafGradedAlgebra.incl (p : ℤ) (ι p W x))
    (p : ℕ) (W : U.toScheme.Opens) (r : U.toScheme.ringCatSheaf.obj.obj (op W))
    (x : (restrictModelF U F p).val.obj (op W)) :
    (Scheme.Hom.relativeDifferentialFormsAlgebra
        ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.incl (p : ℤ)
        (restrictModelι π U D M F ι p W (r • x)) =
      (Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.structureMap
          (op (OO (restrictDivisor U D) (restrictDivisor U M) W))
          ((cU (restrictDivisor U D)).ι.app
            (W ⊓ cU' (restrictDivisor U D) (restrictDivisor U M))
            (U.toScheme.presheaf.map (homOfLE inf_le_left).op r)) *
        (Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.incl (p : ℤ)
          (restrictModelι π U D M F ι p W x) := by
  have hx : ι p (U.ι ''ᵁ W) (r • x) = ι p (U.ι ''ᵁ W)
      ((show V.ringCatSheaf.obj.obj (op (U.ι ''ᵁ W)) from (U.ι.appIso W).inv r) •
        (show (F p).val.obj (op (U.ι ''ᵁ W)) from x)) :=
    rfl
  have h := (congrArg (fun y => pieceTotalRestrict π U D M W
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).toPresheafGradedAlgebra.incl
      (p : ℤ) y)) hx).trans
    (congrArg (pieceTotalRestrict π U D M W) (hι p (U.ι ''ᵁ W) ((U.ι.appIso W).inv r) x))
  rwa [pieceTotalRestrict_incl, map_mul, pieceTotalRestrict_incl, pieceTotalRestrict_structureMap',
    pieceRingEquiv_symm_res U D M W r] at h

end Smul

end MMP.FourfoldProofs.FractionalLogComplexProof
