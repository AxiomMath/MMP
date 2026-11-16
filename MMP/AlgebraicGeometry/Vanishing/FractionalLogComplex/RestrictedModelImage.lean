module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.RestrictedModelDifferential
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Restrict.LogForms
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafRestrictOpen

/-!
# A model of the fractional logarithmic complex restricts to an open piece: the image

A form on `(V ∖ D) ∩ ι(W) ∩ U'` is locally on `ι(W)` a sum `∑ gᵢ ηᵢ` of sections `gᵢ` of
`𝒪_V(-M)` and `ηᵢ` of `Ω^p_V(log D)(-S)` exactly when, read on `(U ∖ D|_U) ∩ W ∩ U'|_U`, it is
locally on `W` such a sum for the restricted data: affine opens of `U` and of `V` inside `U`
correspond under `ι`, and so do the functions, through `ι^*`, and the forms, through the
comparison of forms of the pieces. So the image of the restricted embedding of a model is
`𝒪_U(-M|_U) · Ω^p_U(log D|_U)(-S|_U)`.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceFunction`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.pieceLogForm`: functions and forms over `ι(W)`, read
  over `W`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.localRep_pieceModelForm`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.localRep_of_pieceModelForm`: local representations
  on `ι(W)` and on `W` correspond.
* `MMP.FourfoldProofs.FractionalLogComplexProof.cond_pieceModelForm_iff`: the image condition on `ι(W)`
  and on `W`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.restrictModelι_range`: the image of the restricted
  embedding.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

section Transport

variable {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ)) (U : V.Opens)
  (D M : MMP.Mori.Divisor V)

/-- **Functions on `ι(W) ∩ U'`, read on `W ∩ U'|_U`.** -/
noncomputable def pieceFunction (W : U.toScheme.Opens) (g : Γ(V, U.ι ''ᵁ W ⊓ cU' D M)) :
    Γ(U.toScheme, W ⊓ cU' (restrictDivisor U D) (restrictDivisor U M)) :=
  U.toScheme.presheaf.map (homOfLE (preimage_pieceOpen_eq U D M W).ge).op
    ((U.ι.app (pieceOpen U D M W)).hom g)

/-- The inverse of `pieceFunction`. -/
noncomputable def pieceFunctionInv (W : U.toScheme.Opens)
    (g : Γ(U.toScheme, W ⊓ cU' (restrictDivisor U D) (restrictDivisor U M))) :
    Γ(V, U.ι ''ᵁ W ⊓ cU' D M) :=
  (appRingEquiv U (pieceOpen U D M W) (pieceOpen_le U D M W)).symm
    (U.toScheme.presheaf.map (homOfLE (preimage_pieceOpen_eq U D M W).le).op g)

/-- `pieceFunctionInv` is a right inverse of `pieceFunction`. -/
theorem pieceFunction_pieceFunctionInv (W : U.toScheme.Opens)
    (g : Γ(U.toScheme, W ⊓ cU' (restrictDivisor U D) (restrictDivisor U M))) :
    pieceFunction U D M W (pieceFunctionInv U D M W g) = g := by
  have h : (U.ι.app (pieceOpen U D M W)).hom (pieceFunctionInv U D M W g) =
      U.toScheme.presheaf.map (homOfLE (preimage_pieceOpen_eq U D M W).le).op g :=
    (appRingEquiv U (pieceOpen U D M W) (pieceOpen_le U D M W)).apply_symm_apply _
  unfold pieceFunction
  rw [h, MMP.FourfoldProofs.LogDegenerationProof.presheaf_map_comp_apply' _ _ (𝟙 _),
    CategoryTheory.Functor.map_id]
  rfl

/-- **Forms on `(V ∖ D) ∩ ι(W)`, read on `(U ∖ D|_U) ∩ W`.** -/
noncomputable def pieceLogForm (p : ℤ) (W : U.toScheme.Opens)
    (η : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece p).val.obj
      (op ((cU D).ι ⁻¹ᵁ (U.ι ''ᵁ W)))) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece p).val.obj
      (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ W)) :=
  G1.rs (U.ι ≫ π) (restrictDivisor U D) p (U.ι.preimage_image_eq W).ge
    ((pieceFormsEquiv' π U D p (U.ι ''ᵁ W) (U.ι_image_le W)).symm η)

/-- The inverse of `pieceLogForm`. -/
noncomputable def pieceLogFormInv (p : ℤ) (W : U.toScheme.Opens)
    (η : ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece p).val.obj
      (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ W))) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece p).val.obj
      (op ((cU D).ι ⁻¹ᵁ (U.ι ''ᵁ W))) :=
  pieceFormsEquiv' π U D p (U.ι ''ᵁ W) (U.ι_image_le W)
    (G1.rs (U.ι ≫ π) (restrictDivisor U D) p (U.ι.preimage_image_eq W).le η)

/-- `pieceLogFormInv` is a right inverse of `pieceLogForm`. -/
theorem pieceLogForm_pieceLogFormInv (p : ℤ) (W : U.toScheme.Opens)
    (η : ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece p).val.obj
      (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ W))) :
    pieceLogForm π U D p W (pieceLogFormInv π U D p W η) = η := by
  unfold pieceLogForm pieceLogFormInv
  rw [AddEquiv.symm_apply_apply]
  exact presheafOfModules_map_map_eq_self _ _ _ η

/-- `pieceTotalRestrict` sends the image of a function `g` over `ι(W)` to the image of
`pieceFunction g` over `W`. -/
theorem pieceTotalRestrict_structureMap_app (W : U.toScheme.Opens)
    (g : Γ(V, U.ι ''ᵁ W ⊓ cU' D M)) :
    pieceTotalRestrict π U D M W
        ((TB ((cU D).ι ≫ π)).structureMap (op (OO D M (U.ι ''ᵁ W)))
          ((cU D).ι.app (U.ι ''ᵁ W ⊓ cU' D M) g)) =
      (TB ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).structureMap
          (op (OO (restrictDivisor U D) (restrictDivisor U M) W))
          ((cU (restrictDivisor U D)).ι.app
            (W ⊓ cU' (restrictDivisor U D) (restrictDivisor U M))
            (pieceFunction U D M W g)) := by
  rw [pieceTotalRestrict_structureMap']
  refine congrArg _ ?_
  rw [← pieceRingEquiv_app U D (pieceOpen U D M W) (pieceOpen_le U D M W),
    RingEquiv.symm_apply_apply, presheaf_map_app _ (preimage_pieceOpen_eq U D M W).ge]
  rfl

/-- `pieceTotalRestrict` sends the image of a degree-`p` form `η` over `ι(W)` to the image of
`pieceLogForm η` over `W`. -/
theorem pieceTotalRestrict_incl_map (p : ℕ) (W : U.toScheme.Opens)
    (η : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op ((cU D).ι ⁻¹ᵁ (U.ι ''ᵁ W)))) :
    pieceTotalRestrict π U D M W
        ((TB ((cU D).ι ≫ π)).incl (p : ℤ)
          (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.map
            (homOfLE (Scheme.Hom.preimage_mono _
              (inf_le_left : U.ι ''ᵁ W ⊓ cU' D M ≤ U.ι ''ᵁ W))).op η)) =
      (TB ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).incl (p : ℤ)
        (((Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece (p : ℤ)).val.map
          (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_left :
            W ⊓ cU' (restrictDivisor U D) (restrictDivisor U M) ≤ W))).op
          (pieceLogForm π U D p W η)) := by
  have e0 := pieceTotalRestrict_incl π U D M W (p : ℤ)
    (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.map
      (homOfLE (Scheme.Hom.preimage_mono _
        (inf_le_left : U.ι ''ᵁ W ⊓ cU' D M ≤ U.ι ''ᵁ W))).op η)
  rw [e0]
  refine congrArg _ ?_
  have hle : pieceOpen U D M W ≤ U.ι ''ᵁ W := inf_le_left
  have hm : (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.map
        (homOfLE (Scheme.Hom.preimage_mono _
          (inf_le_left : U.ι ''ᵁ W ⊓ cU' D M ≤ U.ι ''ᵁ W))).op η :
        ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
          (op (OO D M (U.ι ''ᵁ W)))) =
      (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.map
        (homOfLE ((cU D).ι.preimage_mono hle)).op η :
        ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
          (op ((cU D).ι ⁻¹ᵁ pieceOpen U D M W))) := rfl
  have e := pieceFormsEquiv'_symm_map π U D (p : ℤ) hle (U.ι_image_le W) η
  unfold pieceModelForm pieceLogForm
  exact ((congrArg (((Scheme.Hom.relativeDifferentialFormsAlgebra
    ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece (p : ℤ)).val.map
      (homOfLE (OO_restrictDivisor U D M W).le).op)
    ((congrArg (pieceFormsEquiv' π U D (p : ℤ) (pieceOpen U D M W) (pieceOpen_le U D M W)).symm
      hm).trans e)).trans (presheafOfModules_map_map_eq _ _ _ _ _ _))

/-- `DivCond` is invariant under transporting a section along an equality of opens `A = B`. -/
theorem divCond_eq_iff {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {D M : MMP.Mori.Divisor X} {A B : X.Opens} (h : A = B) (g : Γ(X, A ⊓ cU' D M)) :
    DivCond (D := D) (M := M) A g ↔
      DivCond (D := D) (M := M) B (X.presheaf.map (eqToHom (by rw [h])).op g) := by
  subst h
  rw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **Sections of `𝒪(-M)` on `ι(W)` and on `W`.** -/
theorem divCond_pieceFunction_iff [IsLocallyNoetherian V] [IsNormal V] (W : U.toScheme.Opens)
    (g : Γ(V, U.ι ''ᵁ W ⊓ cU' D M)) :
    DivCond (D := D) (M := M) (U.ι ''ᵁ W) g ↔
      DivCond (D := restrictDivisor U D) (M := restrictDivisor U M) W
        (pieceFunction U D M W g) := by
  refine (exists_divisorialSubmodule_restrictDivisor_iff U D M (U.ι ''ᵁ W) (U.ι_image_le W)
    g).trans ?_
  refine (divCond_eq_iff (U.ι.preimage_image_eq W) _).trans ?_
  unfold pieceFunction
  rw [MMP.FourfoldProofs.LogDegenerationProof.presheaf_map_comp_apply' _ _
    (homOfLE (preimage_pieceOpen_eq U D M W).ge).op]

/-- **Logarithmic forms on `ι(W)` and on `W`.** -/
theorem relativeLogForms_pieceLogForm_iff (n : ℕ) [SmoothOfRelativeDimension n π]
    (hD : D.IsRelativeSNC n π)
    (hDU : MMP.Mori.Divisor.IsRelativeSNC n (U.ι ≫ π) (restrictDivisor U D))
    (S : MMP.Mori.Divisor V) (p : ℕ) (W : U.toScheme.Opens)
    (η : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op ((cU D).ι ⁻¹ᵁ (U.ι ''ᵁ W)))) :
    η ∈ MMP.Mori.Divisor.relativeLogForms n π D hD S.suppIdeal p (U.ι ''ᵁ W) ↔
      pieceLogForm π U D p W η ∈ MMP.Mori.Divisor.relativeLogForms n (U.ι ≫ π)
        (restrictDivisor U D) hDU (restrictDivisor U S).suppIdeal p W := by
  have key := relativeLogForms_restrictDivisor_iff n π U D hD hDU S p (U.ι ''ᵁ W)
    (U.ι_image_le W) ((pieceFormsEquiv π U D p (U.ι ''ᵁ W) (U.ι_image_le W)).symm η)
  have hη := congrArg
    (fun z => z ∈ MMP.Mori.Divisor.relativeLogForms n π D hD S.suppIdeal p (U.ι ''ᵁ W))
    (AddEquiv.apply_symm_apply (pieceFormsEquiv π U D (p : ℤ) (U.ι ''ᵁ W) (U.ι_image_le W)) η)
  have e := pieceFormsEquiv'_symm_apply π U D (p : ℤ) (U.ι ''ᵁ W) (U.ι_image_le W) η
  constructor
  · intro h
    unfold pieceLogForm
    rw [e]
    exact G1.relativeLogForms_restrict n (U.ι ≫ π) (restrictDivisor U D) hDU _ (p : ℤ)
      (U.ι.preimage_image_eq W).ge (key.2 (hη.mpr h))
  · intro h
    have h2 := G1.relativeLogForms_restrict n (U.ι ≫ π) (restrictDivisor U D) hDU _ (p : ℤ)
      (U.ι.preimage_image_eq W).le h
    have h3 : G1.rs (U.ι ≫ π) (restrictDivisor U D) (p : ℤ) (U.ι.preimage_image_eq W).le
        (pieceLogForm π U D p W η) =
        (pieceFormsEquiv π U D p (U.ι ''ᵁ W) (U.ι_image_le W)).symm η := by
      unfold pieceLogForm
      rw [e]
      exact presheafOfModules_map_map_eq_self _ _ _ _
    rw [h3] at h2
    exact hη.mp (key.1 h2)

/-- The comparison of total rings is injective. -/
theorem pieceTotalRestrict_injective (W : U.toScheme.Opens) :
    Function.Injective (pieceTotalRestrict π U D M W) := by
  intro a b h
  rw [pieceTotalRestrict_apply, pieceTotalRestrict_apply] at h
  have h2 := congrArg ((TB ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).totalRestrict
    (homOfLE (OO_restrictDivisor U D M W).ge).op) h
  rw [totalRestrict_totalRestrict _ _ (𝟙 _), totalRestrict_totalRestrict _ _ (𝟙 _),
    Stacks.GradedAlgebra.totalRestrict_id, Stacks.GradedAlgebra.totalRestrict_id] at h2
  have h3 := congrArg (pieceTotalEquiv π U D (pieceOpen U D M W) (pieceOpen_le U D M W)) h2
  rwa [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] at h3

end Transport

section LocalRep

variable {V : Scheme.{0}} (n : ℕ) (π : V ⟶ Spec (CommRingCat.of ℂ))
  [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V] (U : V.Opens)
  (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π)
  (hDU : MMP.Mori.Divisor.IsRelativeSNC n (U.ι ≫ π) (restrictDivisor U D))
  (S M : MMP.Mori.Divisor V)

/-- **A local representation on `ι(W)` restricts to one on `W`.** -/
theorem localRep_pieceModelForm (p : ℕ) (W : U.toScheme.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M (U.ι ''ᵁ W))))
    (h : LocalRep n π D hD S M p (U.ι ''ᵁ W) ω) :
    LocalRep n (U.ι ≫ π) (restrictDivisor U D) hDU (restrictDivisor U S) (restrictDivisor U M) p
      W (pieceModelForm π U D M p W ω) := by
  obtain ⟨m, g, η, hg, hη, he⟩ := h
  refine ⟨m, fun i => pieceFunction U D M W (g i), fun i => pieceLogForm π U D p W (η i),
    fun i => (divCond_pieceFunction_iff U D M W (g i)).1 (hg i),
    fun i => (relativeLogForms_pieceLogForm_iff π U D n hD hDU S p W (η i)).1 (hη i), ?_⟩
  have e := congrArg (pieceTotalRestrict π U D M W) he
  rw [← pieceTotalRestrict_incl π U D M W (p : ℤ) ω, e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pieceTotalRestrict_mul, pieceTotalRestrict_structureMap_app π U D M W (g i),
    pieceTotalRestrict_incl_map π U D M p W (η i)]

/-- **A local representation on `W` extends to one on `ι(W)`.** -/
theorem localRep_of_pieceModelForm (p : ℕ) (W : U.toScheme.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M (U.ι ''ᵁ W))))
    (h : LocalRep n (U.ι ≫ π) (restrictDivisor U D) hDU (restrictDivisor U S)
      (restrictDivisor U M) p W (pieceModelForm π U D M p W ω)) :
    LocalRep n π D hD S M p (U.ι ''ᵁ W) ω := by
  obtain ⟨m, g, η, hg, hη, he⟩ := h
  refine ⟨m, fun i => pieceFunctionInv U D M W (g i), fun i => pieceLogFormInv π U D p W (η i),
    fun i => (divCond_pieceFunction_iff U D M W _).2 ?_,
    fun i => (relativeLogForms_pieceLogForm_iff π U D n hD hDU S p W _).2 ?_, ?_⟩
  · rw [pieceFunction_pieceFunctionInv]
    exact hg i
  · rw [pieceLogForm_pieceLogFormInv]
    exact hη i
  apply pieceTotalRestrict_injective π U D M W
  rw [map_sum, pieceTotalRestrict_incl π U D M W (p : ℤ) ω, he]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pieceTotalRestrict_mul,
    pieceTotalRestrict_structureMap_app π U D M W (pieceFunctionInv U D M W (g i)),
    pieceTotalRestrict_incl_map π U D M p W (pieceLogFormInv π U D p W (η i)),
    pieceFunction_pieceFunctionInv, pieceLogForm_pieceLogFormInv]

/-- **The image condition on `ι(W)` and on `W`.** -/
theorem cond_pieceModelForm_iff (p : ℕ) (W : U.toScheme.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M (U.ι ''ᵁ W)))) :
    Cond n π D hD S M p (U.ι ''ᵁ W) ω ↔
      Cond n (U.ι ≫ π) (restrictDivisor U D) hDU (restrictDivisor U S) (restrictDivisor U M) p
        W (pieceModelForm π U D M p W ω) := by
  constructor
  · intro h y hy
    obtain ⟨W', hW', hxW', hL⟩ := h (U.ι y) (U.ι.apply_mem_image_iff.2 hy)
    have hW'U : (W' : V.Opens) ≤ U.ι.opensRange :=
      hW'.trans ((U.ι.image_le_opensRange _))
    have hle : U.ι ''ᵁ (U.ι ⁻¹ᵁ (W' : V.Opens)) ≤ (W' : V.Opens) := U.ι.image_preimage_le _
    have hW'' : U.ι ⁻¹ᵁ (W' : V.Opens) ≤ W :=
      (U.ι.preimage_mono hW').trans (U.ι.preimage_image_eq W).le
    refine ⟨⟨U.ι ⁻¹ᵁ (W' : V.Opens), W'.2.preimage_of_isOpenImmersion U.ι hW'U⟩, hW'', hxW', ?_⟩
    have h1 := localRep_pieceModelForm n π U D hD hDU S M p (U.ι ⁻¹ᵁ (W' : V.Opens))
      _ (LocalRep.restrict n π D hD S M hle hL)
    have h2 := pieceModelForm_map π U D M (p : ℤ) hW'' ω
    have h3 : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.map
        (homOfLE ((cU D).ι.preimage_mono (inf_le_inf_right (cU' D M) hle))).op
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.map
          (homOfLE ((cU D).ι.preimage_mono (inf_le_inf_right (cU' D M) hW'))).op ω) =
        ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.map
          (homOfLE ((cU D).ι.preimage_mono
            (inf_le_inf_right (cU' D M) (U.ι.image_mono hW'')))).op ω := by
      rw [← PresheafOfModules.map_comp_apply]
      rfl
    rwa [h3, h2] at h1
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨W'', hW'', hyW'', hL⟩ := h y hy
    rw [← pieceModelForm_map π U D M (p : ℤ) hW'' ω] at hL
    exact ⟨⟨U.ι ''ᵁ (W'' : U.toScheme.Opens), W''.2.image_of_isOpenImmersion U.ι⟩,
      U.ι.image_mono hW'', U.ι.apply_mem_image_iff.2 hyW'',
      localRep_of_pieceModelForm n π U D hD hDU S M p _ _ hL⟩

omit [IsLocallyNoetherian V] [IsNormal V] in
/-- The map `pieceModelForm` from forms on `ι(W)` to forms on `W` is surjective. -/
theorem pieceModelForm_surjective (q : ℤ) (W : U.toScheme.Opens) :
    Function.Surjective (pieceModelForm π U D M q W) := by
  intro ω
  refine ⟨pieceFormsEquiv' π U D q (pieceOpen U D M W) (pieceOpen_le U D M W)
    (((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece q).val.map
      (homOfLE (OO_restrictDivisor U D M W).ge).op ω), ?_⟩
  have e := AddEquiv.symm_apply_apply
    (pieceFormsEquiv' π U D q (pieceOpen U D M W) (pieceOpen_le U D M W))
    (((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece q).val.map
      (homOfLE (OO_restrictDivisor U D M W).ge).op ω)
  unfold pieceModelForm
  rw [e]
  exact presheafOfModules_map_map_eq_self _ _ _ ω

variable (F : ℕ → V.Modules)
  (ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W)))

/-- **The image of the restricted embedding.** -/
theorem restrictModelι_range
    (hrange : ∀ (p : ℕ) W ω, ω ∈ Set.range (ι p W) ↔ Cond n π D hD S M p W ω)
    (p : ℕ) (W : U.toScheme.Opens) (ω) :
    ω ∈ Set.range (restrictModelι π U D M F ι p W) ↔
      Cond n (U.ι ≫ π) (restrictDivisor U D) hDU (restrictDivisor U S) (restrictDivisor U M) p
        W ω := by
  obtain ⟨ω', rfl⟩ := pieceModelForm_surjective π U D M p W ω
  rw [← cond_pieceModelForm_iff n π U D hD hDU S M p W ω', ← hrange]
  exact ⟨fun ⟨x, hx⟩ => ⟨x, pieceModelForm_injective π U D M p W hx⟩,
    fun ⟨x, hx⟩ => ⟨x, congrArg (pieceModelForm π U D M p W) hx⟩⟩

end LocalRep

end MMP.FourfoldProofs.FractionalLogComplexProof
