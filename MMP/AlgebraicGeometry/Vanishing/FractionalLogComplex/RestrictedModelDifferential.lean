module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.RestrictedModelScalars

/-!
# A model of the fractional logarithmic complex restricts to an open piece: the differential

The comparison of forms on `(V ∖ D) ∩ ι(W) ∩ U'` with forms on `(U ∖ D|_U) ∩ W ∩ U'|_U` commutes
with the de Rham differential and carries `du` to `d(u|_U)`. So the restricted embedding of a
model carries the differential of `K|_U` to the connection `∇ = d - N⁻¹ (du/u) ∧` of the restricted
data, multiplied out by `N u`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceModelForm_d`: the comparison of forms commutes
  with `d`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceTotalRestrict_dOne`: the comparison of total rings
  carries `du` to `du`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.restrictModelι_d`: the differential of `K|_U` is the
  connection.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

section D

variable {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ)) (U : V.Opens)
  (D M : MMP.Mori.Divisor V)

/-- The inverse comparison of forms of the pieces commutes with the de Rham differential. -/
theorem pieceFormsEquiv_symm_d (q : ℕ) (O : V.Opens) (hO : O ≤ U)
    (ω : Γ(((cU D).ι ≫ π).relativeDifferentialForms (q : ℤ), (cU D).ι ⁻¹ᵁ O)) :
    (pieceFormsEquiv π U D ((q + 1 : ℕ) : ℤ) O hO).symm
        ((((cU D).ι ≫ π).deRhamComplex.d q (q + 1)).val.app (op ((cU D).ι ⁻¹ᵁ O)) ω) =
      ((((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).deRhamComplex).d q (q + 1)).val.app
        (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O)))
        ((pieceFormsEquiv π U D q O hO).symm ω) := by
  refine (AddEquiv.symm_apply_eq _).2 ?_
  rw [pieceFormsEquiv_d, AddEquiv.apply_symm_apply]

/-- **The comparison of forms of the model commutes with the de Rham differential.** -/
theorem pieceModelForm_d (q : ℕ) (W : U.toScheme.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (q : ℤ)).val.obj
      (op (OO D M (U.ι ''ᵁ W)))) :
    pieceModelForm π U D M ((q + 1 : ℕ) : ℤ) W
        ((((cU D).ι ≫ π).deRhamComplex.d q (q + 1)).val.app (op (OO D M (U.ι ''ᵁ W))) ω) =
      ((((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).deRhamComplex).d q (q + 1)).val.app
        (op (OO (restrictDivisor U D) (restrictDivisor U M) W))
        (pieceModelForm π U D M q W ω) := by
  have h1 := pieceFormsEquiv_symm_d π U D q (pieceOpen U D M W) (pieceOpen_le U D M W) ω
  have hd : (((cU D).ι ≫ π).deRhamComplex.d q (q + 1)).val.app (op (OO D M (U.ι ''ᵁ W))) ω =
      (((cU D).ι ≫ π).deRhamComplex.d q (q + 1)).val.app
        (op ((cU D).ι ⁻¹ᵁ pieceOpen U D M W)) ω := rfl
  unfold pieceModelForm
  have e1 := pieceFormsEquiv'_symm_apply π U D ((q + 1 : ℕ) : ℤ) (pieceOpen U D M W)
    (pieceOpen_le U D M W)
    ((((cU D).ι ≫ π).deRhamComplex.d q (q + 1)).val.app (op ((cU D).ι ⁻¹ᵁ pieceOpen U D M W)) ω)
  have e2 := pieceFormsEquiv'_symm_apply π U D (q : ℤ) (pieceOpen U D M W)
    (pieceOpen_le U D M W) ω
  rw [hd, e1, e2, h1]
  have j : ∀ z, (((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece ((q + 1 : ℕ) : ℤ)).val.map
        (homOfLE (OO_restrictDivisor U D M W).le).op z) =
      ((((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).deRhamComplex).X (q + 1)).val.map
        (homOfLE (OO_restrictDivisor U D M W).le).op z := fun _ => rfl
  have n := PresheafOfModules.naturality_apply
    ((((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).deRhamComplex).d q (q + 1)).val
    (homOfLE (OO_restrictDivisor U D M W).le).op
    ((pieceFormsEquiv π U D (q : ℤ) (pieceOpen U D M W) (pieceOpen_le U D M W)).symm ω)
  rw [j ((((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).deRhamComplex.d q (q + 1)).val.app
    (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ pieceOpen U D M W)))
    ((pieceFormsEquiv π U D (q : ℤ) (pieceOpen U D M W) (pieceOpen_le U D M W)).symm ω))]
  exact n.symm

/-- `pieceTotalRestrict` is multiplicative. -/
theorem pieceTotalRestrict_mul (W : U.toScheme.Opens)
    (z z' : (Scheme.Hom.relativeDifferentialFormsAlgebra
      ((cU D).ι ≫ π)).toPresheafGradedAlgebra.Total (op (OO D M (U.ι ''ᵁ W)))) :
    pieceTotalRestrict π U D M W (z * z') =
      pieceTotalRestrict π U D M W z * pieceTotalRestrict π U D M W z' :=
  map_mul _ z z'

/-- **The comparison of total rings carries `du` to `du`.** -/
theorem pieceTotalRestrict_dOne (W : U.toScheme.Opens) (u : Γ(V, cU' D M)) :
    pieceTotalRestrict π U D M W
        ((Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU D).ι ≫ π)).toPresheafGradedAlgebra.incl 1
          (dOneOn π (cU D) (OO D M (U.ι ''ᵁ W))
            ((cU D).ι.app (U.ι ''ᵁ W ⊓ cU' D M) (V.presheaf.map (homOfLE inf_le_right).op u)))) =
      (Scheme.Hom.relativeDifferentialFormsAlgebra
        ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.incl 1
        (dOneOn (U.ι ≫ π) (cU (restrictDivisor U D))
          (OO (restrictDivisor U D) (restrictDivisor U M) W)
          ((cU (restrictDivisor U D)).ι.app (W ⊓ cU' (restrictDivisor U D) (restrictDivisor U M))
            (U.toScheme.presheaf.map (homOfLE inf_le_right).op (restrictSection U D M u)))) := by
  have h1 := pieceTotalEquiv_dOne π U D (pieceOpen U D M W) (pieceOpen_le U D M W)
    ((pieceRingEquiv U D (pieceOpen U D M W) (pieceOpen_le U D M W)).symm
      ((cU D).ι.app (U.ι ''ᵁ W ⊓ cU' D M) (V.presheaf.map (homOfLE inf_le_right).op u)))
  rw [RingEquiv.apply_symm_apply] at h1
  have h2 := (RingEquiv.symm_apply_eq _).2 h1.symm
  rw [pieceTotalRestrict_apply, h2]
  exact (G1.totalRestrict_incl_dOne (U.ι ≫ π) (restrictDivisor U D) _ _).trans
    (congrArg _ (congrArg _ (pieceRingEquiv_symm_uW U D M W u)))

end D

section Model

variable {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ)) (U : V.Opens)
  (D M : MMP.Mori.Divisor V) (N : ℕ) (u : Γ(V, cU' D M))
  (K : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ)
  (F : ℕ → V.Modules)
  (e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p))
  (ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W)))

/-- The restricted model on the terms of `K|_U`, read on `K`. -/
theorem restrictModelι_restrictModelIso (p : ℕ) (W : U.toScheme.Opens)
    (x : ((((relRestrict π U).mapHomologicalComplex _).obj K).X p).val.obj (op W)) :
    restrictModelι π U D M F ι p W ((restrictModelIso π U K F e p).hom.val.app (op W) x) =
      pieceModelForm π U D M p W (ι p (U.ι ''ᵁ W) ((e p).hom.val.app (op (U.ι ''ᵁ W)) x)) :=
  rfl

/-- The differential of `K|_U`, read on `K`. -/
theorem restrictModelι_restrictModelIso_d (p : ℕ) (W : U.toScheme.Opens)
    (x : ((((relRestrict π U).mapHomologicalComplex _).obj K).X p).val.obj (op W)) :
    restrictModelι π U D M F ι (p + 1) W ((restrictModelIso π U K F e (p + 1)).hom.val.app (op W)
        (((((relRestrict π U).mapHomologicalComplex _).obj K).d p (p + 1)).val.app (op W) x)) =
      pieceModelForm π U D M ((p + 1 : ℕ) : ℤ) W (ι (p + 1) (U.ι ''ᵁ W)
        ((e (p + 1)).hom.val.app (op (U.ι ''ᵁ W))
          ((K.d p (p + 1)).val.app (op (U.ι ''ᵁ W)) x))) :=
  rfl

/-- **The restricted embedding carries the differential of `K|_U` to the connection.** -/
theorem restrictModelι_d
    (hd : ∀ (p : ℕ) W (x : (K.X p).val.obj (op W)),
      N • ((Scheme.Hom.relativeDifferentialFormsAlgebra
            ((cU D).ι ≫ π)).toPresheafGradedAlgebra.structureMap (op (OO D M W))
            ((cU D).ι.app (W ⊓ cU' D M) (V.presheaf.map (homOfLE inf_le_right).op u)) *
          (Scheme.Hom.relativeDifferentialFormsAlgebra
            ((cU D).ι ≫ π)).toPresheafGradedAlgebra.incl ((p + 1 : ℕ) : ℤ)
            (ι (p + 1) W ((e (p + 1)).hom.val.app (op W) ((K.d p (p + 1)).val.app (op W) x)))) =
        N • ((Scheme.Hom.relativeDifferentialFormsAlgebra
            ((cU D).ι ≫ π)).toPresheafGradedAlgebra.structureMap (op (OO D M W))
            ((cU D).ι.app (W ⊓ cU' D M) (V.presheaf.map (homOfLE inf_le_right).op u)) *
          (Scheme.Hom.relativeDifferentialFormsAlgebra
            ((cU D).ι ≫ π)).toPresheafGradedAlgebra.incl ((p + 1 : ℕ) : ℤ)
            ((((cU D).ι ≫ π).deRhamComplex.d p (p + 1)).val.app (op (OO D M W))
              (ι p W ((e p).hom.val.app (op W) x)))) -
        (Scheme.Hom.relativeDifferentialFormsAlgebra
            ((cU D).ι ≫ π)).toPresheafGradedAlgebra.incl 1
            (dOneOn π (cU D) (OO D M W)
              ((cU D).ι.app (W ⊓ cU' D M) (V.presheaf.map (homOfLE inf_le_right).op u))) *
          (Scheme.Hom.relativeDifferentialFormsAlgebra
            ((cU D).ι ≫ π)).toPresheafGradedAlgebra.incl (p : ℤ)
            (ι p W ((e p).hom.val.app (op W) x)))
    (p : ℕ) (W : U.toScheme.Opens)
    (x : ((((relRestrict π U).mapHomologicalComplex _).obj K).X p).val.obj (op W)) :
    N • ((Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.structureMap
          (op (OO (restrictDivisor U D) (restrictDivisor U M) W))
          ((cU (restrictDivisor U D)).ι.app (W ⊓ cU' (restrictDivisor U D) (restrictDivisor U M))
            (U.toScheme.presheaf.map (homOfLE inf_le_right).op (restrictSection U D M u))) *
        (Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.incl
          ((p + 1 : ℕ) : ℤ)
          (restrictModelι π U D M F ι (p + 1) W
            ((restrictModelIso π U K F e (p + 1)).hom.val.app (op W)
              (((((relRestrict π U).mapHomologicalComplex _).obj K).d p (p + 1)).val.app
                (op W) x)))) =
      N • ((Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.structureMap
          (op (OO (restrictDivisor U D) (restrictDivisor U M) W))
          ((cU (restrictDivisor U D)).ι.app (W ⊓ cU' (restrictDivisor U D) (restrictDivisor U M))
            (U.toScheme.presheaf.map (homOfLE inf_le_right).op (restrictSection U D M u))) *
        (Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.incl
          ((p + 1 : ℕ) : ℤ)
          (((((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).deRhamComplex).d p (p + 1)).val.app
            (op (OO (restrictDivisor U D) (restrictDivisor U M) W))
            (restrictModelι π U D M F ι p W
              ((restrictModelIso π U K F e p).hom.val.app (op W) x)))) -
      (Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.incl 1
          (dOneOn (U.ι ≫ π) (cU (restrictDivisor U D))
            (OO (restrictDivisor U D) (restrictDivisor U M) W)
            ((cU (restrictDivisor U D)).ι.app
              (W ⊓ cU' (restrictDivisor U D) (restrictDivisor U M))
              (U.toScheme.presheaf.map (homOfLE inf_le_right).op (restrictSection U D M u)))) *
        (Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.incl (p : ℤ)
          (restrictModelι π U D M F ι p W
            ((restrictModelIso π U K F e p).hom.val.app (op W) x)) := by
  have hh := hd p (U.ι ''ᵁ W) x
  have hS := (pieceTotalRestrict_structureMap' π U D M W _).trans
    (congrArg ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.structureMap
      (op (OO (restrictDivisor U D) (restrictDivisor U M) W)))
      (pieceRingEquiv_symm_uW U D M W u))
  have hI1 := (pieceTotalRestrict_incl π U D M W ((p + 1 : ℕ) : ℤ) _).trans
    (congrArg ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.incl ((p + 1 : ℕ) : ℤ))
      (restrictModelι_restrictModelIso_d π U D M K F e ι p W x).symm)
  have hI3 := (pieceTotalRestrict_incl π U D M W (p : ℤ) _).trans
    (congrArg ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.incl (p : ℤ))
      (restrictModelι_restrictModelIso π U D M K F e ι p W x).symm)
  have hdF := pieceTotalRestrict_dOne π U D M W u
  have hA := (map_nsmul (pieceTotalRestrict π U D M W) N _).trans
    (congrArg (N • ·) ((pieceTotalRestrict_mul π U D M W _ _).trans
      (congrArg₂ (· * ·) hS hI1)))
  have hC := (pieceTotalRestrict_mul π U D M W _ _).trans (congrArg₂ (· * ·) hdF hI3)
  refine hA.symm.trans ((congrArg (pieceTotalRestrict π U D M W) hh).trans
    ((map_sub (pieceTotalRestrict π U D M W) _ _).trans ?_))
  refine congrArg₂ (· - ·) ?_ ?_
  · refine (map_nsmul (pieceTotalRestrict π U D M W) N _).trans ?_
    refine congrArg (N • ·) ?_
    rw [pieceTotalRestrict_mul]
    refine congrArg₂ (· * ·) hS ?_
    have e4 := pieceTotalRestrict_incl π U D M W ((p + 1 : ℕ) : ℤ)
      ((((cU D).ι ≫ π).deRhamComplex.d p (p + 1)).val.app (op (OO D M (U.ι ''ᵁ W)))
        (ι p (U.ι ''ᵁ W) ((e p).hom.val.app (op (U.ι ''ᵁ W)) x)))
    rw [e4]
    refine congrArg _ ?_
    exact (pieceModelForm_d π U D M p W _).trans (congrArg _
      (restrictModelι_restrictModelIso π U D M K F e ι p W x).symm)
  · exact hC

end Model

end MMP.FourfoldProofs.FractionalLogComplexProof
