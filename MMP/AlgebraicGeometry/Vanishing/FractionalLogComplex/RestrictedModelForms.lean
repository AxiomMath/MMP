module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.InverseImageModuleRestriction
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Restrict.FormsComparison

/-!
# A model of the fractional logarithmic complex restricts to an open piece

Let `π : V ⟶ Spec ℂ` carry the data `D`, `S`, `M`, `N`, `u` of the fractional logarithmic complex
`C^• = 𝒪_V(-M) · Ω^•_V(log D)(-S)`, and let `U` be an open of `V`. A model `K` of `C^•`
(`MMP.FourfoldProofs.FractionalLogComplexProof.IsCModel`) restricts to a model of the fractional
logarithmic complex of the restricted data on `U`: the terms of `K|_U` are the restrictions
`(Fᵖ)|_U`, and a section of `Fᵖ|_U` over an open `W` of `U` is a section of `Fᵖ` over `ι(W)`,
whose form on `(V ∖ D) ∩ ι(W) ∩ U'` is a form on `(U ∖ D|_U) ∩ W ∩ U'|_U`.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceOpen`: the open `ι(W) ∩ U'` of `V`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceModelForm`: forms on `(V ∖ D) ∩ ι(W) ∩ U'` read
  on `(U ∖ D|_U) ∩ W ∩ U'|_U`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceTotalRestrict`: the same for the total rings of
  forms, as a ring homomorphism.
* `MMP.FourfoldProofs.FractionalLogComplexProof.restrictModelF`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.restrictModelIso`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.restrictModelι`: the data of the restricted model.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.restrictModelι_injective`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.restrictModelι_add`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.restrictModelι_map`: the restricted embedding is
  injective, additive and compatible with restriction.
* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceTotalRestrict_incl`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.pieceTotalRestrict_structureMap`: the comparison of
  total rings on forms and on functions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

section Opens

variable {V : Scheme.{0}} (U : V.Opens) (D M : MMP.Mori.Divisor V)

/-- The open `ι(W) ∩ U'` of `V`, for an open `W` of `U`. -/
abbrev pieceOpen (W : U.toScheme.Opens) : V.Opens := U.ι ''ᵁ W ⊓ cU' D M

/-- The open `ι(W) ∩ U'` is contained in `U`. -/
theorem pieceOpen_le (W : U.toScheme.Opens) : pieceOpen U D M W ≤ U :=
  inf_le_left.trans ((U.ι.image_le_opensRange _).trans (Scheme.Opens.opensRange_ι U).le)

/-- **`U ∩ W ∩ U'` of the restricted data** is the trace of `(V ∖ D) ∩ ι(W) ∩ U'`. -/
theorem OO_restrictDivisor (W : U.toScheme.Opens) :
    OO (restrictDivisor U D) (restrictDivisor U M) W =
      (cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ pieceOpen U D M W) := by
  change (cU (restrictDivisor U D)).ι ⁻¹ᵁ (W ⊓ cU' (restrictDivisor U D) (restrictDivisor U M)) =
    (cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ (U.ι ''ᵁ W) ⊓ U.ι ⁻¹ᵁ cU' D M)
  rw [cU'_restrictDivisor, U.ι.preimage_image_eq]

/-- The open `ι(W) ∩ U'` is monotone in `W`. -/
theorem pieceOpen_mono {W W' : U.toScheme.Opens} (h : W' ≤ W) :
    pieceOpen U D M W' ≤ pieceOpen U D M W :=
  inf_le_inf_right _ (U.ι.image_mono h)

end Opens

section Forms

/-- Over a thin index category, restricting along a morphism and back is the identity. -/
theorem presheafOfModules_map_map_eq_self {C : Type*} [Category C] [Quiver.IsThin Cᵒᵖ]
    {R : Cᵒᵖ ⥤ RingCat.{0}} (M : PresheafOfModules.{0} R) {A B : Cᵒᵖ}
    (i : A ⟶ B) (j : B ⟶ A) (x : M.obj A) : M.map j (M.map i x) = x := by
  rw [← PresheafOfModules.map_comp_apply, Subsingleton.elim (i ≫ j) (𝟙 A),
    PresheafOfModules.map_id]
  rfl

variable {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ)) (U : V.Opens)
  (D M : MMP.Mori.Divisor V)

/-- **Forms on `(V ∖ D) ∩ ι(W) ∩ U'`, read on `(U ∖ D|_U) ∩ W ∩ U'|_U`.** -/
noncomputable def pieceModelForm (q : ℤ) (W : U.toScheme.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece q).val.obj
      (op (OO D M (U.ι ''ᵁ W)))) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece q).val.obj
      (op (OO (restrictDivisor U D) (restrictDivisor U M) W)) :=
  ((Scheme.Hom.relativeDifferentialFormsAlgebra
    ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece q).val.map
    (homOfLE (OO_restrictDivisor U D M W).le).op
    ((pieceFormsEquiv' π U D q (pieceOpen U D M W) (pieceOpen_le U D M W)).symm ω)

/-- Reading forms on `(V ∖ D) ∩ ι(W) ∩ U'` on `(U ∖ D|_U) ∩ W ∩ U'|_U` is injective. -/
theorem pieceModelForm_injective (q : ℤ) (W : U.toScheme.Opens) :
    Function.Injective (pieceModelForm π U D M q W) := by
  intro ω ω' h
  apply (pieceFormsEquiv' π U D q (pieceOpen U D M W) (pieceOpen_le U D M W)).symm.injective
  have key := fun y => presheafOfModules_map_map_eq_self
    ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece q).val
    (homOfLE (OO_restrictDivisor U D M W).le).op (homOfLE (OO_restrictDivisor U D M W).ge).op y
  exact (key _).symm.trans ((congrArg (((Scheme.Hom.relativeDifferentialFormsAlgebra
    ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece q).val.map
    (homOfLE (OO_restrictDivisor U D M W).ge).op) h).trans (key _))

/-- Reading forms on `(V ∖ D) ∩ ι(W) ∩ U'` on `(U ∖ D|_U) ∩ W ∩ U'|_U` is additive. -/
theorem pieceModelForm_add (q : ℤ) (W : U.toScheme.Opens) (ω ω') :
    pieceModelForm π U D M q W (ω + ω') =
      pieceModelForm π U D M q W ω + pieceModelForm π U D M q W ω' := by
  unfold pieceModelForm
  rw [map_add, map_add]
  rfl

/-- The comparison `(pieceFormsEquiv' O)⁻¹` commutes with restriction. -/
theorem pieceFormsEquiv'_symm_map (q : ℤ) {O₁ O₂ : V.Opens} (h : O₁ ≤ O₂) (hO₂ : O₂ ≤ U)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece q).val.obj
      (op ((cU D).ι ⁻¹ᵁ O₂))) :
    (pieceFormsEquiv' π U D q O₁ (h.trans hO₂)).symm
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece q).val.map
          (homOfLE ((cU D).ι.preimage_mono h)).op ω) =
      ((Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece q).val.map
        (homOfLE ((cU (restrictDivisor U D)).ι.preimage_mono (U.ι.preimage_mono h))).op
        ((pieceFormsEquiv' π U D q O₂ hO₂).symm ω) := by
  refine (AddEquiv.symm_apply_eq _).2 ?_
  have h1 := pieceFormsEquiv_map_piece π U D q h hO₂ ((pieceFormsEquiv' π U D q O₂ hO₂).symm ω)
  have h2 : pieceFormsEquiv' π U D q O₂ hO₂ ((pieceFormsEquiv' π U D q O₂ hO₂).symm ω) = ω :=
    AddEquiv.apply_symm_apply _ _
  exact (congrArg (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece q).val.map
    (homOfLE ((cU D).ι.preimage_mono h)).op) h2).symm.trans h1.symm

/-- **The comparison of forms of the model commutes with restriction.** -/
theorem pieceModelForm_map (q : ℤ) {W W' : U.toScheme.Opens} (h : W' ≤ W)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece q).val.obj
      (op (OO D M (U.ι ''ᵁ W)))) :
    pieceModelForm π U D M q W'
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece q).val.map
          (homOfLE ((cU D).ι.preimage_mono (pieceOpen_mono U D M h))).op ω) =
      ((Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece q).val.map
        (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right _ h))).op
        (pieceModelForm π U D M q W ω) := by
  unfold pieceModelForm
  rw [pieceFormsEquiv'_symm_map π U D q (pieceOpen_mono U D M h) (pieceOpen_le U D M W) ω]
  exact (presheafOfModules_map_map_eq _ _ _ _ _ _)

end Forms

/-! ### Total rings of forms -/

section Total

variable {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ)) (U : V.Opens)
  (D M : MMP.Mori.Divisor V)

/-- **The comparison of total rings of forms** from `(V ∖ D) ∩ ι(W) ∩ U'` to
`(U ∖ D|_U) ∩ W ∩ U'|_U`. -/
noncomputable def pieceTotalRestrict (W : U.toScheme.Opens) :
    (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).toPresheafGradedAlgebra.Total
        (op (OO D M (U.ι ''ᵁ W))) →+*
      (Scheme.Hom.relativeDifferentialFormsAlgebra
        ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.Total
        (op (OO (restrictDivisor U D) (restrictDivisor U M) W)) :=
  ((Scheme.Hom.relativeDifferentialFormsAlgebra
    ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.totalRestrictRingHom
      (homOfLE (OO_restrictDivisor U D M W).le).op).comp
    (pieceTotalEquiv π U D (pieceOpen U D M W) (pieceOpen_le U D M W)).symm.toRingHom

/-- `pieceTotalRestrict` is the inverse comparison of total rings followed by restriction to
`(U ∖ D|_U) ∩ W ∩ U'|_U`. -/
theorem pieceTotalRestrict_apply (W : U.toScheme.Opens)
    (z : (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).toPresheafGradedAlgebra.Total
        (op ((cU D).ι ⁻¹ᵁ pieceOpen U D M W))) :
    pieceTotalRestrict π U D M W z =
      (Scheme.Hom.relativeDifferentialFormsAlgebra
        ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.totalRestrict
        (homOfLE (OO_restrictDivisor U D M W).le).op
        ((pieceTotalEquiv π U D (pieceOpen U D M W) (pieceOpen_le U D M W)).symm z) := rfl

/-- On a form of degree `q`, `pieceTotalRestrict` is `pieceModelForm` in degree `q`. -/
theorem pieceTotalRestrict_incl (W : U.toScheme.Opens) (q : ℤ)
    (y : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece q).val.obj
      (op (OO D M (U.ι ''ᵁ W)))) :
    pieceTotalRestrict π U D M W
        ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).toPresheafGradedAlgebra.incl
          q y) =
      (Scheme.Hom.relativeDifferentialFormsAlgebra
        ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.incl q
          (pieceModelForm π U D M q W y) := by
  have h1 := pieceTotalEquiv_symm_incl π U D (pieceOpen U D M W) (pieceOpen_le U D M W) q y
  have h2 := (Scheme.Hom.relativeDifferentialFormsAlgebra
    ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.totalRestrict_incl
      (homOfLE (OO_restrictDivisor U D M W).le).op q
      ((pieceFormsEquiv' π U D q (pieceOpen U D M W) (pieceOpen_le U D M W)).symm y)
  rw [pieceTotalRestrict_apply, h1]
  exact h2

/-- On a function, `pieceTotalRestrict` is the comparison of functions followed by restriction to
`(U ∖ D|_U) ∩ W ∩ U'|_U`. -/
theorem pieceTotalRestrict_structureMap (W : U.toScheme.Opens)
    (c : Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ pieceOpen U D M W)) :
    pieceTotalRestrict π U D M W
        ((Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU D).ι ≫ π)).toPresheafGradedAlgebra.structureMap
          (op ((cU D).ι ⁻¹ᵁ pieceOpen U D M W)) c) =
      (Scheme.Hom.relativeDifferentialFormsAlgebra
        ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.structureMap
          (op (OO (restrictDivisor U D) (restrictDivisor U M) W))
          ((cU (restrictDivisor U D)).toScheme.presheaf.map
            (homOfLE (OO_restrictDivisor U D M W).le).op
            ((pieceRingEquiv U D (pieceOpen U D M W) (pieceOpen_le U D M W)).symm c)) := by
  have h1 := pieceTotalEquiv_structureMap π U D (pieceOpen U D M W) (pieceOpen_le U D M W)
    ((pieceRingEquiv U D (pieceOpen U D M W) (pieceOpen_le U D M W)).symm c)
  rw [RingEquiv.apply_symm_apply] at h1
  have h2 := (RingEquiv.symm_apply_eq _).2 h1.symm
  rw [pieceTotalRestrict_apply, h2]
  exact (Scheme.Hom.relativeDifferentialFormsAlgebra
    ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.structureMap_naturality _ _

end Total

/-! ### The data of the restricted model -/

section Data

variable {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ)) (U : V.Opens)
  (D M : MMP.Mori.Divisor V)
  (K : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ)
  (F : ℕ → V.Modules)
  (e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p))
  (ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W)))

/-- The terms `(Fᵖ)|_U` of the restricted model. -/
noncomputable abbrev restrictModelF (p : ℕ) : U.toScheme.Modules := (F p).restrict U.ι

/-- The identification of the terms of `K|_U` with the `(Fᵖ)|_U`. -/
noncomputable def restrictModelIso (p : ℕ) :
    (((relRestrict π U).mapHomologicalComplex _).obj K).X p ≅
      (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap (U.ι ≫ π)))).obj
        (restrictModelF U F p) :=
  (relRestrict π U).mapIso (e p) ≪≫ relRestrictRestrictScalarsIso π U (F p)

/-- The embedding of the terms of the restricted model into forms. -/
noncomputable def restrictModelι (p : ℕ) (W : U.toScheme.Opens)
    (x : (restrictModelF U F p).val.obj (op W)) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO (restrictDivisor U D) (restrictDivisor U M) W)) :=
  pieceModelForm π U D M p W (ι p (U.ι ''ᵁ W) x)

/-- If each embedding `ι p W` is injective, so is the restricted embedding. -/
theorem restrictModelι_injective (hι : ∀ (p : ℕ) W, Function.Injective (ι p W)) (p : ℕ)
    (W : U.toScheme.Opens) : Function.Injective (restrictModelι π U D M F ι p W) :=
  (pieceModelForm_injective π U D M p W).comp (hι p (U.ι ''ᵁ W))

/-- If each embedding `ι p W` is additive, so is the restricted embedding. -/
theorem restrictModelι_add (hι : ∀ (p : ℕ) W x y, ι p W (x + y) = ι p W x + ι p W y)
    (p : ℕ) (W : U.toScheme.Opens) (x y) :
    restrictModelι π U D M F ι p W (x + y) =
      restrictModelι π U D M F ι p W x + restrictModelι π U D M F ι p W y :=
  (congrArg (pieceModelForm π U D M p W) (hι p (U.ι ''ᵁ W) x y)).trans
    (pieceModelForm_add π U D M p W _ _)

/-- If the embeddings `ι p W` commute with restriction, so does the restricted embedding. -/
theorem restrictModelι_map (hι : ∀ (p : ℕ) (W W' : V.Opens) (h : W' ≤ W) x,
      ι p W' ((F p).val.map (homOfLE h).op x) =
        ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.map
          (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) h))).op (ι p W x))
    (p : ℕ) (W W' : U.toScheme.Opens) (h : W' ≤ W) (x) :
    restrictModelι π U D M F ι p W' ((restrictModelF U F p).val.map (homOfLE h).op x) =
      ((Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece (p : ℤ)).val.map
        (homOfLE (Scheme.Hom.preimage_mono _
          (inf_le_inf_right (cU' (restrictDivisor U D) (restrictDivisor U M)) h))).op
        (restrictModelι π U D M F ι p W x) :=
  (congrArg (pieceModelForm π U D M p W')
    (hι p (U.ι ''ᵁ W) (U.ι ''ᵁ W') (U.ι.image_mono h) x)).trans
    (pieceModelForm_map π U D M p h _)

end Data

end MMP.FourfoldProofs.FractionalLogComplexProof
