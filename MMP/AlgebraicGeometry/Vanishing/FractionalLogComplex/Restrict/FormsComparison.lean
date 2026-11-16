module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.OpenPieceForms
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Restrict.LogGeneratorTransfer

/-!
# Forms on an open subscheme: the comparison of total rings of forms

Let `π : V ⟶ Spec ℂ`, let `U` be an open of `V` and `D` a divisor of `V`. For an open `O ⊆ U` of
`V`, the comparison `MMP.FourfoldProofs.FractionalLogComplexProof.pieceFormsEquiv` of forms on
`(U ∖ D|_U) ∩ O` with forms on `(V ∖ D) ∩ O` is, in all degrees together, an isomorphism of the
total rings of forms. It is compatible with the structure maps from functions, through the
comparison `MMP.FourfoldProofs.FractionalLogComplexProof.pieceRingEquiv` of functions, and with the
differentials of functions.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceFormsEquiv'`: the comparison of forms in degree
  `i`, read on the pieces of the algebras of forms.
* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceTotalEquiv`: the comparison of forms in all
  degrees, as a ring isomorphism of total rings.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceTotalEquiv_incl`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.pieceTotalEquiv_symm_incl`: on homogeneous forms.
* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceTotalEquiv_structureMap`: on functions.
* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceTotalEquiv_dOne`: on differentials of functions.

## Implementation notes

The sections of a sheaf of forms and the sections of the corresponding piece of the algebra of
forms are definitionally equal but spelled differently, and so are the two structure sheaves of
rings that act on them. Statements are written so that the two sides of every equation use the
same spelling; the conversions are proved once, for arbitrary schemes and morphisms
(`MMP.FourfoldProofs.FractionalLogComplexProof.sectionsValEquiv`,
`MMP.FourfoldProofs.FractionalLogComplexProof.piece_smul_of_forms_smul`).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

section Comparison

variable {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ)) (U : V.Opens)
  (D : MMP.Mori.Divisor V)

/-- The restriction `Γ(V, O) → Γ(U, U ∩ O)` for `O ⊆ U`, as a ring isomorphism. -/
noncomputable abbrev appRingEquiv (O : V.Opens) (hO : O ≤ U) :
    Γ(V, O) ≃+* Γ(U.toScheme, U.ι ⁻¹ᵁ O) :=
  haveI := Scheme.Hom.isIso_app U.ι O (by rwa [Scheme.Opens.opensRange_ι])
  RingEquiv.ofBijective (U.ι.app O).hom (ConcreteCategory.bijective_of_isIso (U.ι.app O))

/-- An additive isomorphism of sections of sheaves of modules, read on the underlying
presheaves of modules. -/
noncomputable def sectionsValEquiv {X₁ X₂ : Scheme.{0}} (F₁ : X₁.Modules) (F₂ : X₂.Modules)
    {W₁ : X₁.Opens} {W₂ : X₂.Opens} (e : Γ(F₁, W₁) ≃+ Γ(F₂, W₂)) :
    F₁.val.obj (op W₁) ≃+ F₂.val.obj (op W₂) where
  toFun x := e x
  invFun x := e.symm x
  left_inv x := e.symm_apply_apply x
  right_inv x := e.apply_symm_apply x
  map_add' x y := e.map_add x y

/-- The comparison of forms over `O ⊆ U` in degree `i`, read on the pieces of the graded
algebras of forms. -/
noncomputable def pieceFormsEquiv' (i : ℤ) (O : V.Opens) (hO : O ≤ U) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra
        ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece i).val.obj
        (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) ≃+
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece i).val.obj
        (op ((cU D).ι ⁻¹ᵁ O)) :=
  sectionsValEquiv _ _ (pieceFormsEquiv π U D i O hO)

/-- `pieceFormsEquiv'` agrees with `pieceFormsEquiv` on sections of the piece of degree `i`. -/
theorem pieceFormsEquiv'_apply (i : ℤ) (O : V.Opens) (hO : O ≤ U)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra
        ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece i).val.obj
        (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O)))) :
    pieceFormsEquiv' π U D i O hO x = pieceFormsEquiv π U D i O hO x := rfl

/-- The inverse of `pieceFormsEquiv'` agrees with the inverse of `pieceFormsEquiv`. -/
theorem pieceFormsEquiv'_symm_apply (i : ℤ) (O : V.Opens) (hO : O ≤ U)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece i).val.obj
        (op ((cU D).ι ⁻¹ᵁ O))) :
    (pieceFormsEquiv' π U D i O hO).symm x = (pieceFormsEquiv π U D i O hO).symm x := rfl

/-- `pieceFormsEquiv'` agrees with `pieceFormsEquiv` on sections of the sheaf of forms of degree
`i`. -/
theorem pieceFormsEquiv'_apply_sections (i : ℤ) (O : V.Opens) (hO : O ≤ U)
    (x : Γ(((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).relativeDifferentialForms i,
      (cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) :
    pieceFormsEquiv' π U D i O hO x = pieceFormsEquiv π U D i O hO x := rfl

/-- The comparison of forms in degree `0` sends the unit form to the unit form. -/
theorem pieceFormsEquiv'_one (O : V.Opens) (hO : O ≤ U) :
    pieceFormsEquiv' π U D 0 O hO
        ((Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).one.eval
          (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O)))) =
      (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).one.eval
        (op ((cU D).ι ⁻¹ᵁ O)) :=
  (pieceFormsEquiv'_apply π U D 0 O hO _).trans (pieceFormsEquiv_one π U D O hO)

/-- The comparison of forms is multiplicative: it sends the product of forms of degrees `i` and
`j` to the product of their images. -/
theorem pieceFormsEquiv'_mul (i j : ℤ) (O : V.Opens) (hO : O ≤ U)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra
        ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece i).val.obj
        (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))))
    (y : ((Scheme.Hom.relativeDifferentialFormsAlgebra
        ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece j).val.obj
        (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O)))) :
    pieceFormsEquiv' π U D (i + j) O hO
        (((Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).mul i j).app
          (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) x y) =
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).mul i j).app
        (op ((cU D).ι ⁻¹ᵁ O))
        (pieceFormsEquiv' π U D i O hO x) (pieceFormsEquiv' π U D j O hO y) :=
  (pieceFormsEquiv'_apply π U D (i + j) O hO _).trans (pieceFormsEquiv_mul π U D i j O hO x y)

/-- The comparison of forms over `O ⊆ U` in all degrees, as a ring isomorphism of total rings. -/
noncomputable def pieceTotalEquiv (O : V.Opens) (hO : O ≤ U) :
    (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U D)).ι ≫ U.ι ≫
        π)).toPresheafGradedAlgebra.Total
        (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) ≃+*
      (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).toPresheafGradedAlgebra.Total
          (op ((cU D).ι ⁻¹ᵁ O)) :=
  gradedTotalRingEquivOfMul
    (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π))
    (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π))
    (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) (op ((cU D).ι ⁻¹ᵁ O))
    (fun i => pieceFormsEquiv' π U D i O hO) (pieceFormsEquiv'_one π U D O hO)
    (pieceFormsEquiv'_mul π U D · · O hO)

/-- On a homogeneous form of degree `i`, `pieceTotalEquiv` is the comparison of forms in degree
`i`. -/
theorem pieceTotalEquiv_incl (O : V.Opens) (hO : O ≤ U) (i : ℤ)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra
        ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece i).val.obj
        (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O)))) :
    pieceTotalEquiv π U D O hO ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor
        U D)).ι ≫ U.ι ≫ π)).toPresheafGradedAlgebra.incl i x) =
      (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).toPresheafGradedAlgebra.incl i
          (pieceFormsEquiv' π U D i O hO x) := by
  unfold pieceTotalEquiv
  exact gradedTotalRingEquivOfMul_incl
    (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π))
    (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π))
    (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) (op ((cU D).ι ⁻¹ᵁ O))
    (fun i => pieceFormsEquiv' π U D i O hO) (pieceFormsEquiv'_one π U D O hO)
    (pieceFormsEquiv'_mul π U D · · O hO) i x

/-- On a homogeneous form of degree `i`, the inverse of `pieceTotalEquiv` is the inverse of the
comparison of forms in degree `i`. -/
theorem pieceTotalEquiv_symm_incl (O : V.Opens) (hO : O ≤ U) (i : ℤ)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece i).val.obj
        (op ((cU D).ι ⁻¹ᵁ O))) :
    (pieceTotalEquiv π U D O hO).symm ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫
        π)).toPresheafGradedAlgebra.incl i x) =
      (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U D)).ι ≫ U.ι ≫
          π)).toPresheafGradedAlgebra.incl i
        ((pieceFormsEquiv' π U D i O hO).symm x) := by
  unfold pieceTotalEquiv
  exact gradedTotalRingEquivOfMul_symm_incl
    (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π))
    (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π))
    (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) (op ((cU D).ι ⁻¹ᵁ O))
    (fun i => pieceFormsEquiv' π U D i O hO) (pieceFormsEquiv'_one π U D O hO)
    (pieceFormsEquiv'_mul π U D · · O hO) i x

/-- An additive isomorphism of sections of sheaves of forms that is semilinear along a ring
isomorphism `ψ` stays semilinear when read on the pieces of the algebras of forms. -/
theorem piece_smul_of_forms_smul {X₁ X₂ S₁ S₂ : Scheme.{0}} (g₁ : X₁ ⟶ S₁) (g₂ : X₂ ⟶ S₂) (i : ℤ)
    {W₁ : X₁.Opens} {W₂ : X₂.Opens}
    (e : Γ(g₁.relativeDifferentialForms i, W₁) ≃+ Γ(g₂.relativeDifferentialForms i, W₂))
    (ψ : Γ(X₁, W₁) ≃+* Γ(X₂, W₂)) (he : ∀ c x, e (c • x) = ψ c • e x) (c : Γ(X₁, W₁))
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra g₁).piece i).val.obj (op W₁)) :
    e ((show (Stacks.RingedSpace.structureRingSheaf X₁.toRingedSpace).obj.obj (op W₁) from c) • x) =
      (show (Stacks.RingedSpace.structureRingSheaf X₂.toRingedSpace).obj.obj (op W₂) from ψ c) •
        (show ((Scheme.Hom.relativeDifferentialFormsAlgebra g₂).piece i).val.obj (op W₂) from
          e x) :=
  he c x

/-- `pieceTotalEquiv` sends the image of a function `c` under the structure map to the image of
`pieceRingEquiv U D O hO c`. -/
theorem pieceTotalEquiv_structureMap (O : V.Opens) (hO : O ≤ U)
    (c : Γ((cU (restrictDivisor U D)).toScheme, (cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) :
    pieceTotalEquiv π U D O hO
        ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U D)).ι ≫ U.ι ≫
            π)).toPresheafGradedAlgebra.structureMap (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ
            O))) c) =
      (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫
          π)).toPresheafGradedAlgebra.structureMap (op ((cU D).ι ⁻¹ᵁ O)) (pieceRingEquiv U D O hO
          c) := by
  have h1 : (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U D)).ι ≫ U.ι ≫
      π)).toPresheafGradedAlgebra.structureMap (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O)))
      c =
      (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U D)).ι ≫ U.ι ≫
          π)).toPresheafGradedAlgebra.incl 0
        ((show (Stacks.RingedSpace.structureRingSheaf (cU (restrictDivisor U
            D)).toScheme.toRingedSpace).obj.obj (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O)))
            from c) • (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U D)).ι ≫
            U.ι ≫ π)).one.eval (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O)))) :=
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U D)).ι ≫ U.ι ≫
        π)).toPresheafGradedAlgebra.incl_smul 0 _ _).symm
  have s1 := congrArg (⇑(pieceTotalEquiv π U D O hO)) h1
  have s2 := pieceTotalEquiv_incl π U D O hO 0 ((show (Stacks.RingedSpace.structureRingSheaf (cU
      (restrictDivisor U D)).toScheme.toRingedSpace).obj.obj (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ
      (U.ι ⁻¹ᵁ O))) from c) • (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U
      D)).ι ≫ U.ι ≫ π)).one.eval (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))))
  have s3 := pieceFormsEquiv'_apply π U D 0 O hO ((show (Stacks.RingedSpace.structureRingSheaf (cU
      (restrictDivisor U D)).toScheme.toRingedSpace).obj.obj (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ
      (U.ι ⁻¹ᵁ O))) from c) • (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U
      D)).ι ≫ U.ι ≫ π)).one.eval (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))))
  have s4 := piece_smul_of_forms_smul ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π) ((cU D).ι ≫ π) 0
    (pieceFormsEquiv π U D 0 O hO) (pieceRingEquiv U D O hO) (pieceFormsEquiv_smul π U D 0 O hO) c
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U D)).ι ≫ U.ι ≫
        π)).one.eval (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))))
  have s5 := congrArg (fun z => (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫
      π)).toPresheafGradedAlgebra.incl 0
    ((show (Stacks.RingedSpace.structureRingSheaf (cU D).toScheme.toRingedSpace).obj.obj (op ((cU
        D).ι ⁻¹ᵁ O)) from pieceRingEquiv U D O hO c) • (show
        ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece 0).val.obj (op ((cU
        D).ι ⁻¹ᵁ O)) from z)))
    (pieceFormsEquiv_one π U D O hO)
  have t1 := s3.trans s4
  have t2 := congrArg ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫
      π)).toPresheafGradedAlgebra.incl 0) t1
  have t3 := s2.trans t2
  have t4 := t3.trans s5
  have t5 := s1.trans t4
  have h2' : (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫
      π)).toPresheafGradedAlgebra.structureMap (op ((cU D).ι ⁻¹ᵁ O)) (pieceRingEquiv U D O hO c) =
      (fun z => (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫
          π)).toPresheafGradedAlgebra.incl 0
        ((show (Stacks.RingedSpace.structureRingSheaf (cU D).toScheme.toRingedSpace).obj.obj (op
            ((cU D).ι ⁻¹ᵁ O)) from pieceRingEquiv U D O hO c) • (show
            ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece 0).val.obj (op ((cU
            D).ι ⁻¹ᵁ O)) from z)))
        ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).one.eval (op ((cU D).ι ⁻¹ᵁ
            O))) :=
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).toPresheafGradedAlgebra.incl_smul
        0 _ _).symm
  exact t5.trans h2'.symm

/-- `pieceTotalEquiv` sends the differential of a function `c` to the differential of
`pieceRingEquiv U D O hO c`. -/
theorem pieceTotalEquiv_dOne (O : V.Opens) (hO : O ≤ U)
    (c : Γ((cU (restrictDivisor U D)).toScheme, (cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) :
    pieceTotalEquiv π U D O hO
        ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U D)).ι ≫ U.ι ≫
            π)).toPresheafGradedAlgebra.incl 1
          (dOneOn (U.ι ≫ π) (cU (restrictDivisor U D)) _ c)) =
      (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).toPresheafGradedAlgebra.incl 1
          (dOneOn π (cU D) _ (pieceRingEquiv U D O hO c)) := by
  have e1 : dOneOn (U.ι ≫ π) (cU (restrictDivisor U D))
      ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O)) c =
      AlgebraicGeometry.SheafOfModules.exactOne
        (Scheme.Hom.deRhamAlgebras ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π))
        (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) c := rfl
  have e2 : dOneOn π (cU D) ((cU D).ι ⁻¹ᵁ O) (pieceRingEquiv U D O hO c) =
      AlgebraicGeometry.SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras ((cU D).ι ≫ π))
        (op ((cU D).ι ⁻¹ᵁ O)) (pieceRingEquiv U D O hO c) := rfl
  have e3 : pieceFormsEquiv' π U D 1 O hO
      (AlgebraicGeometry.SheafOfModules.exactOne
        (Scheme.Hom.deRhamAlgebras ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π))
        (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) c) =
      AlgebraicGeometry.SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras ((cU D).ι ≫ π))
        (op ((cU D).ι ⁻¹ᵁ O)) (pieceRingEquiv U D O hO c) :=
    (pieceFormsEquiv'_apply π U D 1 O hO _).trans (pieceFormsEquiv_exactOne π U D O hO c)
  rw [e1, e2, pieceTotalEquiv_incl π U D O hO 1
    (AlgebraicGeometry.SheafOfModules.exactOne
      (Scheme.Hom.deRhamAlgebras ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π))
      (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) c), e3]

end Comparison

end MMP.FourfoldProofs.FractionalLogComplexProof
