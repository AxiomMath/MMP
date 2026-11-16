module

public import MMP.AlgebraicGeometry.DeRham.Logarithmic.DeligneIllusieReduction
public import MMP.AlgebraicGeometry.Divisor.RestrictOpen

/-!
# Forms on an open subscheme and the restricted data

Let `π : V ⟶ Spec ℂ`, let `U` be an open of `V` and `D` a divisor of `V`, with restriction
`D|_U` to `U`. The open `U ∖ D|_U` of `U` is the trace `U ∩ (V ∖ D)`, so for an open `O ⊆ U` of
`V` a differential form on `(U ∖ D|_U) ∩ O`, as a form of the open subscheme `U ∖ D|_U` of `U`
over `ℂ`, is a form on `(V ∖ D) ∩ O`, as a form of the open subscheme `V ∖ D` of `V` over `ℂ`:
both are forms of `V` over `ℂ` on `O ∖ D`.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceFormsEquiv`: forms on `(U ∖ D|_U) ∩ O` are forms
  on `(V ∖ D) ∩ O`, for an open `O ⊆ U` of `V`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceRingEquiv`: the same for functions.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.cU_restrictDivisor`: `U ∖ D|_U = U ∩ (V ∖ D)`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceFormsEquiv_mul`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.pieceFormsEquiv_one`: the comparison of forms is
  multiplicative and unital.
* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceFormsEquiv_smul`: it is semilinear over
  `pieceRingEquiv`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceFormsEquiv_map`: it commutes with restriction.
* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceFormsEquiv_exactOne`: it carries `dc` to `dc`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceFormsEquiv_d`: it commutes with the de Rham
  differential.
* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceFormsEquiv_map_piece`: it commutes with restriction
  on the pieces of the graded algebras of forms.
* `MMP.FourfoldProofs.FractionalLogComplexProof.pieceRingEquiv_app`: `pieceRingEquiv` is the identity
  on functions coming from `V`.

## Implementation notes

The comparison is composed of three instances of the comparison of forms of an open subscheme
with forms of the ambient scheme (`MMP.FourfoldProofs.LogDegenerationProof.ambientFormsEquiv`): for
`U ∖ D|_U` in `U`, for `U` in `V`, and, inverted, for `V ∖ D` in `V`, with transports along the
equalities of opens between them.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open MMP.FourfoldProofs.LogDegenerationProof (ambientFormsEquiv ambientRingHom)

variable {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ)) (U : V.Opens)
  (D : MMP.Mori.Divisor V)

/-- **`U ∖ D|_U` is the trace of `V ∖ D` on `U`.** -/
theorem cU_restrictDivisor : cU (restrictDivisor U D) = U.ι ⁻¹ᵁ cU D := by
  ext x
  change x ∉ ((restrictDivisor U D).supp : Closeds U) ↔ U.ι x ∉ (D.supp : Closeds V)
  exact not_congr (mem_supp_restrictDivisor_iff U D x)

/-- For an open `O` of `V`, `U.ι ⁻¹ᵁ O ∩ (U ∖ D|_U) = U.ι ⁻¹ᵁ (O ∩ (V ∖ D))`. -/
theorem preimage_inf_cU_restrictDivisor (O : V.Opens) :
    U.ι ⁻¹ᵁ O ⊓ cU (restrictDivisor U D) = U.ι ⁻¹ᵁ (O ⊓ cU D) := by
  rw [cU_restrictDivisor]
  rfl

/-- For an open `O ⊆ U`, `(O ∩ (V ∖ D)) ∩ U = O ∩ (V ∖ D)`. -/
theorem inf_cU_inf_eq (O : V.Opens) (hO : O ≤ U) : O ⊓ cU D ⊓ U = O ⊓ cU D :=
  inf_eq_left.2 (inf_le_left.trans hO)

/-- The transport of sections of a sheaf of modules along an equality of opens. -/
noncomputable def sectionsEqEquiv {X : Scheme.{0}} (F : X.Modules) {A B : X.Opens} (h : A = B) :
    Γ(F, A) ≃+ Γ(F, B) :=
  (F.presheaf.mapIso (eqToIso h.symm).op).addCommGroupIsoToAddEquiv

/-- `sectionsEqEquiv` is the restriction map along the equality of opens. -/
theorem sectionsEqEquiv_apply {X : Scheme.{0}} (F : X.Modules) {A B : X.Opens} (h : A = B)
    (x : Γ(F, A)) : sectionsEqEquiv F h x = F.presheaf.map (eqToHom h.symm).op x := rfl

/-- **Forms of `U ∖ D|_U` over `O` are forms of `V ∖ D` over `O`**, for an open `O ⊆ U` of `V`. -/
noncomputable def pieceFormsEquiv (q : ℤ) (O : V.Opens) (hO : O ≤ U) :
    Γ(((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).relativeDifferentialForms q,
        (cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O)) ≃+
      Γ(((cU D).ι ≫ π).relativeDifferentialForms q, (cU D).ι ⁻¹ᵁ O) :=
  (ambientFormsEquiv (U.ι ≫ π) (cU (restrictDivisor U D)) q (U.ι ⁻¹ᵁ O)).trans <|
    (sectionsEqEquiv _ (preimage_inf_cU_restrictDivisor U D O)).trans <|
      (ambientFormsEquiv π U q (O ⊓ cU D)).trans <|
        (sectionsEqEquiv _ (inf_cU_inf_eq U D O hO)).trans
          (ambientFormsEquiv π (cU D) q O).symm

/-- `pieceFormsEquiv` is the composite of the comparisons `ambientFormsEquiv` and the transports
`sectionsEqEquiv` defining it. -/
theorem pieceFormsEquiv_apply (q : ℤ) (O : V.Opens) (hO : O ≤ U)
    (x : Γ(((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).relativeDifferentialForms q,
        (cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) :
    pieceFormsEquiv π U D q O hO x =
      (ambientFormsEquiv π (cU D) q O).symm
        (sectionsEqEquiv _ (inf_cU_inf_eq U D O hO)
          (ambientFormsEquiv π U q (O ⊓ cU D)
            (sectionsEqEquiv _ (preimage_inf_cU_restrictDivisor U D O)
              (ambientFormsEquiv (U.ι ≫ π) (cU (restrictDivisor U D)) q (U.ι ⁻¹ᵁ O) x)))) :=
  rfl

/-! ### Products -/

section Mul

variable {X S : Scheme.{0}} (a : X ⟶ S)

/-- Restriction of forms along an inclusion of opens is multiplicative. -/
theorem formsAlgebra_map_mul (i j : ℤ) {A B : X.Opens} (h : B ⟶ A)
    (x : Γ(a.relativeDifferentialForms i, A)) (y : Γ(a.relativeDifferentialForms j, A)) :
    (a.relativeDifferentialForms (i + j)).presheaf.map h.op
        (((Scheme.Hom.relativeDifferentialFormsAlgebra a).mul i j).app (op A) x y) =
      ((Scheme.Hom.relativeDifferentialFormsAlgebra a).mul i j).app (op B)
        ((a.relativeDifferentialForms i).presheaf.map h.op x)
        ((a.relativeDifferentialForms j).presheaf.map h.op y) :=
  ((Scheme.Hom.relativeDifferentialFormsAlgebra a).mul i j).naturality h.op x y

/-- The transport of forms along an equality of opens is multiplicative. -/
theorem sectionsEqEquiv_mul (i j : ℤ) {A B : X.Opens} (h : A = B)
    (x : Γ(a.relativeDifferentialForms i, A)) (y : Γ(a.relativeDifferentialForms j, A)) :
    sectionsEqEquiv (a.relativeDifferentialForms (i + j)) h
        (((Scheme.Hom.relativeDifferentialFormsAlgebra a).mul i j).app (op A) x y) =
      ((Scheme.Hom.relativeDifferentialFormsAlgebra a).mul i j).app (op B)
        (sectionsEqEquiv (a.relativeDifferentialForms i) h x)
        (sectionsEqEquiv (a.relativeDifferentialForms j) h y) :=
  formsAlgebra_map_mul a i j (eqToHom h.symm) x y

end Mul

section AmbientMul

variable {Y : Scheme.{0}} {k : Type} [Field k] (f : Y ⟶ Spec (CommRingCat.of k)) (W : Y.Opens)

/-- **The inverse of the comparison of forms of an open subscheme with ambient forms is
multiplicative.** -/
theorem ambientFormsEquiv_symm_mul (i j : ℤ) (O : Y.Opens)
    (x : Γ(f.relativeDifferentialForms i, O ⊓ W)) (y : Γ(f.relativeDifferentialForms j, O ⊓ W)) :
    (ambientFormsEquiv f W (i + j) O).symm
        (((Scheme.Hom.relativeDifferentialFormsAlgebra f).mul i j).app (op (O ⊓ W)) x y) =
      ((Scheme.Hom.relativeDifferentialFormsAlgebra (W.ι ≫ f)).mul i j).app (op (W.ι ⁻¹ᵁ O))
        ((ambientFormsEquiv f W i O).symm x) ((ambientFormsEquiv f W j O).symm y) := by
  have hx := MMP.FourfoldProofs.LogDegenerationProof.ambientFormsEquiv_symm_apply f W i O x
  have hy := MMP.FourfoldProofs.LogDegenerationProof.ambientFormsEquiv_symm_apply f W j O y
  refine (MMP.FourfoldProofs.LogDegenerationProof.ambientFormsEquiv_symm_apply f W (i + j) O _).trans ?_
  refine (congrArg _ (formsAlgebra_map_mul f i j _ x y)).trans ?_
  refine (Scheme.Hom.restrictFormsIso_hom_app W f (W.ι ≫ f) (𝟙 _) _ _ (i + j) _ _).trans ?_
  refine (congrArg _
    (Scheme.Hom.relativeDifferentialFormsPullback_mul _ _ _ _ _ i j _ _ _)).trans ?_
  refine (formsAlgebra_map_mul _ i j _ _ _).trans ?_
  rw [hx, hy]
  exact congrArg₂ (fun u v =>
      ((Scheme.Hom.relativeDifferentialFormsAlgebra (W.ι ≫ f)).mul i j).app (op (W.ι ⁻¹ᵁ O)) u v)
    (Scheme.Hom.restrictFormsIso_hom_app W f (W.ι ≫ f) (𝟙 _) _ _ i _ _).symm
    (Scheme.Hom.restrictFormsIso_hom_app W f (W.ι ≫ f) (𝟙 _) _ _ j _ _).symm

/-- The comparison `ambientFormsEquiv` of forms of an open subscheme with ambient forms is
multiplicative. -/
theorem ambientFormsEquiv_mul (i j : ℤ) (O : Y.Opens)
    (x : Γ((W.ι ≫ f).relativeDifferentialForms i, W.ι ⁻¹ᵁ O))
    (y : Γ((W.ι ≫ f).relativeDifferentialForms j, W.ι ⁻¹ᵁ O)) :
    ambientFormsEquiv f W (i + j) O
        (((Scheme.Hom.relativeDifferentialFormsAlgebra (W.ι ≫ f)).mul i j).app (op (W.ι ⁻¹ᵁ O))
          x y) =
      ((Scheme.Hom.relativeDifferentialFormsAlgebra f).mul i j).app (op (O ⊓ W))
        (ambientFormsEquiv f W i O x) (ambientFormsEquiv f W j O y) := by
  refine (ambientFormsEquiv f W (i + j) O).symm.injective
    (((ambientFormsEquiv f W (i + j) O).symm_apply_apply _).trans ?_)
  refine Eq.trans ?_ (ambientFormsEquiv_symm_mul f W i j O _ _).symm
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]

end AmbientMul

/-- **The comparison of forms of the pieces is multiplicative.** -/
theorem pieceFormsEquiv_mul (i j : ℤ) (O : V.Opens) (hO : O ≤ U)
    (x : Γ(((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).relativeDifferentialForms i,
      (cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O)))
    (y : Γ(((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).relativeDifferentialForms j,
      (cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) :
    pieceFormsEquiv π U D (i + j) O hO
        (((Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).mul i j).app
          (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) x y) =
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).mul i j).app
        (op ((cU D).ι ⁻¹ᵁ O)) (pieceFormsEquiv π U D i O hO x)
        (pieceFormsEquiv π U D j O hO y) := by
  have h2 := (congrArg (fun z => sectionsEqEquiv ((U.ι ≫ π).relativeDifferentialForms (i + j))
      (preimage_inf_cU_restrictDivisor U D O) z)
    (ambientFormsEquiv_mul (U.ι ≫ π) (cU (restrictDivisor U D)) i j (U.ι ⁻¹ᵁ O) x y)).trans
    (sectionsEqEquiv_mul (U.ι ≫ π) i j (preimage_inf_cU_restrictDivisor U D O) _ _)
  have h3 := (congrArg (fun z => ambientFormsEquiv π U (i + j) (O ⊓ cU D) z) h2).trans
    (ambientFormsEquiv_mul π U i j (O ⊓ cU D) _ _)
  have h4 := (congrArg (fun z => sectionsEqEquiv (π.relativeDifferentialForms (i + j))
      (inf_cU_inf_eq U D O hO) z) h3).trans
    (sectionsEqEquiv_mul π i j (inf_cU_inf_eq U D O hO) _ _)
  have h5 := (congrArg (fun z => (ambientFormsEquiv π (cU D) (i + j) O).symm z) h4).trans
    (ambientFormsEquiv_symm_mul π (cU D) i j O _ _)
  rw [pieceFormsEquiv_apply π U D i O hO x, pieceFormsEquiv_apply π U D j O hO y]
  refine (pieceFormsEquiv_apply π U D (i + j) O hO _).trans ?_
  convert h5 using 2

/-! ### Functions and semilinearity -/

section Smul

/-- The transport of functions along an equality of opens. -/
noncomputable def ringSectionsEqEquiv (X : Scheme.{0}) {A B : X.Opens} (h : A = B) :
    Γ(X, A) ≃+* Γ(X, B) :=
  (X.presheaf.mapIso (eqToIso h.symm).op).commRingCatIsoToRingEquiv

/-- `ringSectionsEqEquiv` is the restriction map along the equality of opens. -/
theorem ringSectionsEqEquiv_apply (X : Scheme.{0}) {A B : X.Opens} (h : A = B) (r : Γ(X, A)) :
    ringSectionsEqEquiv X h r = X.presheaf.map (eqToHom h.symm).op r := rfl

/-- The transport of sections along an equality of opens is semilinear. -/
theorem sectionsEqEquiv_smul {X : Scheme.{0}} (F : X.Modules) {A B : X.Opens} (h : A = B)
    (r : Γ(X, A)) (x : Γ(F, A)) :
    sectionsEqEquiv F h (r • x) = ringSectionsEqEquiv X h r • sectionsEqEquiv F h x :=
  Scheme.Modules.map_smul F (eqToHom h.symm) r x

/-- **Functions on `W ∩ O` read on the open subscheme `W` or on `Y`**, as a ring isomorphism. -/
noncomputable def ambientRingEquiv {Y : Scheme.{0}} (W O : Y.Opens) :
    Γ(W.toScheme, W.ι ⁻¹ᵁ O) ≃+* Γ(Y, O ⊓ W) :=
  (W.ι.appIso (W.ι ⁻¹ᵁ O)).symm.commRingCatIsoToRingEquiv.trans
    (ringSectionsEqEquiv Y (MMP.FourfoldProofs.LogDegenerationProof.image_preimage_opens_ι W O))

/-- `ambientRingEquiv` agrees with `MMP.FourfoldProofs.LogDegenerationProof.ambientRingHom`. -/
theorem ambientRingEquiv_apply {Y : Scheme.{0}} (W O : Y.Opens) (c : Γ(W.toScheme, W.ι ⁻¹ᵁ O)) :
    ambientRingEquiv W O c = ambientRingHom W O c := rfl

/-- The inverse of `ambientFormsEquiv` is semilinear over `ambientRingEquiv`. -/
theorem ambientFormsEquiv_symm_smul {Y : Scheme.{0}} {k : Type} [Field k]
    (f : Y ⟶ Spec (CommRingCat.of k)) (W : Y.Opens) (q : ℤ) (O : Y.Opens)
    (c : Γ(W.toScheme, W.ι ⁻¹ᵁ O)) (z : Γ(f.relativeDifferentialForms q, O ⊓ W)) :
    (ambientFormsEquiv f W q O).symm (ambientRingEquiv W O c • z) =
      c • (ambientFormsEquiv f W q O).symm z := by
  refine (AddEquiv.symm_apply_eq _).2 ?_
  rw [MMP.FourfoldProofs.LogDegenerationProof.ambientFormsEquiv_smul, AddEquiv.apply_symm_apply]
  rfl

/-- **Functions of `U ∖ D|_U` over `O` are functions of `V ∖ D` over `O`**, for an open
`O ⊆ U` of `V`: the ring isomorphism over which `pieceFormsEquiv` is semilinear. -/
noncomputable def pieceRingEquiv (O : V.Opens) (hO : O ≤ U) :
    Γ((cU (restrictDivisor U D)).toScheme, (cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O)) ≃+*
      Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ O) :=
  (ambientRingEquiv (cU (restrictDivisor U D)) (U.ι ⁻¹ᵁ O)).trans <|
    (ringSectionsEqEquiv _ (preimage_inf_cU_restrictDivisor U D O)).trans <|
      (ambientRingEquiv U (O ⊓ cU D)).trans <|
        (ringSectionsEqEquiv _ (inf_cU_inf_eq U D O hO)).trans
          (ambientRingEquiv (cU D) O).symm

/-- **The comparison of forms of the pieces is semilinear** over `pieceRingEquiv`. -/
theorem pieceFormsEquiv_smul (q : ℤ) (O : V.Opens) (hO : O ≤ U)
    (c : Γ((cU (restrictDivisor U D)).toScheme, (cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O)))
    (x : Γ(((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).relativeDifferentialForms q,
        (cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) :
    pieceFormsEquiv π U D q O hO (c • x) =
      pieceRingEquiv U D O hO c • pieceFormsEquiv π U D q O hO x := by
  rw [pieceFormsEquiv_apply, pieceFormsEquiv_apply,
    MMP.FourfoldProofs.LogDegenerationProof.ambientFormsEquiv_smul, sectionsEqEquiv_smul,
    MMP.FourfoldProofs.LogDegenerationProof.ambientFormsEquiv_smul, sectionsEqEquiv_smul]
  have h := ambientFormsEquiv_symm_smul π (cU D) q O (pieceRingEquiv U D O hO c)
    (sectionsEqEquiv _ (inf_cU_inf_eq U D O hO) (ambientFormsEquiv π U q (O ⊓ cU D)
      (sectionsEqEquiv _ (preimage_inf_cU_restrictDivisor U D O)
        (ambientFormsEquiv (U.ι ≫ π) (cU (restrictDivisor U D)) q (U.ι ⁻¹ᵁ O) x))))
  convert h using 2
  simp only [pieceRingEquiv, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  rfl

end Smul

/-! ### Restriction -/

section Map

/-- The transport of sections along equalities of opens commutes with restriction. -/
theorem sectionsEqEquiv_map {X : Scheme.{0}} (F : X.Modules) {A B A' B' : X.Opens} (h : A = B)
    (h' : A' = B') (hA : A' ≤ A) (hB : B' ≤ B) (x : Γ(F, A)) :
    sectionsEqEquiv F h' (F.presheaf.map (homOfLE hA).op x) =
      F.presheaf.map (homOfLE hB).op (sectionsEqEquiv F h x) :=
  MMP.FourfoldProofs.LogDegenerationProof.modules_map_map_eq_map_map F _ _ _ _ x

/-- The inverse of `ambientFormsEquiv` commutes with restriction. -/
theorem ambientFormsEquiv_symm_map {Y : Scheme.{0}} {k : Type} [Field k]
    (f : Y ⟶ Spec (CommRingCat.of k)) (W : Y.Opens) (q : ℤ) {O₁ O₂ : Y.Opens} (h : O₁ ≤ O₂)
    (z : Γ(f.relativeDifferentialForms q, O₂ ⊓ W)) :
    (ambientFormsEquiv f W q O₁).symm
        ((f.relativeDifferentialForms q).presheaf.map (homOfLE (inf_le_inf_right W h)).op z) =
      ((W.ι ≫ f).relativeDifferentialForms q).presheaf.map (homOfLE (W.ι.preimage_mono h)).op
        ((ambientFormsEquiv f W q O₂).symm z) := by
  refine (AddEquiv.symm_apply_eq _).2 ?_
  rw [MMP.FourfoldProofs.LogDegenerationProof.ambientFormsEquiv_map, AddEquiv.apply_symm_apply]
  all_goals exact h

/-- **The comparison of forms of the pieces commutes with restriction.** -/
theorem pieceFormsEquiv_map (q : ℤ) {O₁ O₂ : V.Opens} (h : O₁ ≤ O₂) (hO₂ : O₂ ≤ U)
    (x : Γ(((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).relativeDifferentialForms q,
        (cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O₂))) :
    pieceFormsEquiv π U D q O₁ (h.trans hO₂)
        ((((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).relativeDifferentialForms q).presheaf.map
          (homOfLE ((cU (restrictDivisor U D)).ι.preimage_mono (U.ι.preimage_mono h))).op x) =
      (((cU D).ι ≫ π).relativeDifferentialForms q).presheaf.map
        (homOfLE ((cU D).ι.preimage_mono h)).op (pieceFormsEquiv π U D q O₂ hO₂ x) := by
  rw [pieceFormsEquiv_apply, pieceFormsEquiv_apply,
    MMP.FourfoldProofs.LogDegenerationProof.ambientFormsEquiv_map,
    sectionsEqEquiv_map _ _ _ _ (U.ι.preimage_mono (inf_le_inf_right (cU D) h)),
    MMP.FourfoldProofs.LogDegenerationProof.ambientFormsEquiv_map,
    sectionsEqEquiv_map _ _ _ _ (inf_le_inf_right (cU D) h), ambientFormsEquiv_symm_map]
  exacts [h, inf_le_inf_right (cU D) h, U.ι.preimage_mono h]

end Map

/-! ### Functions from `V` -/

section App

/-- Restricting the pullback of a function along a morphism is pulling back its restriction. -/
theorem presheaf_map_app {X Y : Scheme.{0}} (f : X ⟶ Y) {A B : Y.Opens} (hBA : B ≤ A)
    (i : op (f ⁻¹ᵁ A) ⟶ op (f ⁻¹ᵁ B)) (g : Γ(Y, A)) :
    X.presheaf.map i ((f.app A).hom g) = (f.app B).hom (Y.presheaf.map (homOfLE hBA).op g) := by
  rw [Subsingleton.elim i ((Opens.map f.base).map (homOfLE hBA)).op]
  exact (congrArg (fun φ => φ.hom g) (f.naturality (homOfLE hBA).op)).symm

/-- **`pieceRingEquiv` on functions coming from `V`.** -/
theorem pieceRingEquiv_app (O : V.Opens) (hO : O ≤ U) (g : Γ(V, O)) :
    pieceRingEquiv U D O hO
        (((cU (restrictDivisor U D)).ι.app (U.ι ⁻¹ᵁ O)).hom ((U.ι.app O).hom g)) =
      ((cU D).ι.app O).hom g := by
  simp only [pieceRingEquiv, RingEquiv.trans_apply]
  rw [RingEquiv.symm_apply_eq, ambientRingEquiv_apply, ambientRingEquiv_apply,
    ambientRingEquiv_apply, MMP.FourfoldProofs.LogDegenerationProof.ambientRingHom_app,
    MMP.FourfoldProofs.LogDegenerationProof.ambientRingHom_app, ringSectionsEqEquiv_apply,
    ringSectionsEqEquiv_apply,
    MMP.FourfoldProofs.LogDegenerationProof.presheaf_map_comp_apply' _ _
      (homOfLE (U.ι.preimage_mono (inf_le_left : O ⊓ cU D ≤ O))).op,
    presheaf_map_app U.ι (inf_le_left : O ⊓ cU D ≤ O),
    MMP.FourfoldProofs.LogDegenerationProof.ambientRingHom_app,
    MMP.FourfoldProofs.LogDegenerationProof.presheaf_map_comp_apply',
    MMP.FourfoldProofs.LogDegenerationProof.presheaf_map_comp_apply' _ _ (homOfLE inf_le_left).op]
  exact 𝟙 _

end App

/-! ### The unit and exact one-forms -/

section OneD

/-- Restriction of forms preserves the unit. -/
theorem formsAlgebra_map_one {X S : Scheme.{0}} (a : X ⟶ S) {A B : X.Opens} (h : B ⟶ A) :
    (a.relativeDifferentialForms 0).presheaf.map h.op
        ((Scheme.Hom.relativeDifferentialFormsAlgebra a).one.eval (op A)) =
      (Scheme.Hom.relativeDifferentialFormsAlgebra a).one.eval (op B) :=
  (Scheme.Hom.relativeDifferentialFormsAlgebra a).one.2 h.op

/-- The inverse of `ambientFormsEquiv` carries the unit to the unit. -/
theorem ambientFormsEquiv_symm_one {Y : Scheme.{0}} {k : Type} [Field k]
    (f : Y ⟶ Spec (CommRingCat.of k)) (W O : Y.Opens) :
    (ambientFormsEquiv f W 0 O).symm
        ((Scheme.Hom.relativeDifferentialFormsAlgebra f).one.eval (op (O ⊓ W))) =
      (Scheme.Hom.relativeDifferentialFormsAlgebra (W.ι ≫ f)).one.eval (op (W.ι ⁻¹ᵁ O)) := by
  refine (MMP.FourfoldProofs.LogDegenerationProof.ambientFormsEquiv_symm_apply f W 0 O _).trans ?_
  refine (congrArg _ (formsAlgebra_map_one f _)).trans ?_
  refine (Scheme.Hom.restrictFormsIso_hom_app W f (W.ι ≫ f) (𝟙 _) _ _ 0 _ _).trans ?_
  refine (congrArg _ (Scheme.Hom.relativeDifferentialFormsPullback_one _ _ _ _ _ _)).trans ?_
  exact formsAlgebra_map_one _ _

/-- `ambientFormsEquiv` carries the unit to the unit. -/
theorem ambientFormsEquiv_one {Y : Scheme.{0}} {k : Type} [Field k]
    (f : Y ⟶ Spec (CommRingCat.of k)) (W O : Y.Opens) :
    ambientFormsEquiv f W 0 O
        ((Scheme.Hom.relativeDifferentialFormsAlgebra (W.ι ≫ f)).one.eval (op (W.ι ⁻¹ᵁ O))) =
      (Scheme.Hom.relativeDifferentialFormsAlgebra f).one.eval (op (O ⊓ W)) := by
  refine ((AddEquiv.symm_apply_eq _).1 ?_).symm
  exact ambientFormsEquiv_symm_one f W O

/-- **The comparison of forms of the pieces preserves the unit.** -/
theorem pieceFormsEquiv_one (O : V.Opens) (hO : O ≤ U) :
    pieceFormsEquiv π U D 0 O hO
        ((Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).one.eval
          (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O)))) =
      (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).one.eval
        (op ((cU D).ι ⁻¹ᵁ O)) := by
  have h2 := (congrArg (fun z => sectionsEqEquiv ((U.ι ≫ π).relativeDifferentialForms 0)
      (preimage_inf_cU_restrictDivisor U D O) z)
    (ambientFormsEquiv_one (U.ι ≫ π) (cU (restrictDivisor U D)) (U.ι ⁻¹ᵁ O))).trans
    (formsAlgebra_map_one (U.ι ≫ π) (eqToHom (preimage_inf_cU_restrictDivisor U D O).symm))
  have h3 := (congrArg (fun z => ambientFormsEquiv π U 0 (O ⊓ cU D) z) h2).trans
    (ambientFormsEquiv_one π U (O ⊓ cU D))
  have h4 := (congrArg (fun z => sectionsEqEquiv (π.relativeDifferentialForms 0)
      (inf_cU_inf_eq U D O hO) z) h3).trans
    (formsAlgebra_map_one π (eqToHom (inf_cU_inf_eq U D O hO).symm))
  have h5 := (congrArg (fun z => (ambientFormsEquiv π (cU D) 0 O).symm z) h4).trans
    (ambientFormsEquiv_symm_one π (cU D) O)
  refine (pieceFormsEquiv_apply π U D 0 O hO _).trans ?_
  convert h5 using 2

/-- Transport of an exact one-form along an equality of opens. -/
theorem sectionsEqEquiv_exactOne {X S : Scheme.{0}} (a : X ⟶ S) {A B : X.Opens} (h : A = B)
    (b : Γ(X, A)) :
    sectionsEqEquiv (a.relativeDifferentialForms 1) h
        (AlgebraicGeometry.SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras a) (op A) b) =
      AlgebraicGeometry.SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras a) (op B)
        (ringSectionsEqEquiv X h b) :=
  AlgebraicGeometry.SheafOfModules.exactOne_map (Scheme.Hom.deRhamAlgebras a) _ b

/-- The inverse of `ambientFormsEquiv` carries `d` of `ambientRingEquiv W O b` to `d b`. -/
theorem ambientFormsEquiv_symm_exactOne {Y : Scheme.{0}} {k : Type} [Field k]
    (f : Y ⟶ Spec (CommRingCat.of k)) (W O : Y.Opens) (b : Γ(W.toScheme, W.ι ⁻¹ᵁ O)) :
    (ambientFormsEquiv f W 1 O).symm
        (AlgebraicGeometry.SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras f) (op (O ⊓ W))
          (ambientRingEquiv W O b)) =
      AlgebraicGeometry.SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras (W.ι ≫ f))
        (op (W.ι ⁻¹ᵁ O)) b := by
  refine (MMP.FourfoldProofs.LogDegenerationProof.ambientFormsEquiv_symm_apply f W 1 O _).trans ?_
  refine (Scheme.Hom.restrictFormsIso_hom_app W f (W.ι ≫ f) (𝟙 _) _ _ 1 _ _).trans ?_
  exact MMP.FourfoldProofs.LogDegenerationProof.ambientFormsEquiv_exactOne_aux f W O b

/-- `ambientFormsEquiv` carries `d b` to `d` of the function `ambientRingEquiv W O b`. -/
theorem ambientFormsEquiv_exactOne {Y : Scheme.{0}} {k : Type} [Field k]
    (f : Y ⟶ Spec (CommRingCat.of k)) (W O : Y.Opens) (b : Γ(W.toScheme, W.ι ⁻¹ᵁ O)) :
    ambientFormsEquiv f W 1 O
        (AlgebraicGeometry.SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras (W.ι ≫ f))
          (op (W.ι ⁻¹ᵁ O)) b) =
      AlgebraicGeometry.SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras f) (op (O ⊓ W))
        (ambientRingEquiv W O b) := by
  refine ((AddEquiv.symm_apply_eq _).1 ?_).symm
  exact ambientFormsEquiv_symm_exactOne f W O b

/-- **The comparison of forms of the pieces carries `dc` to `d` of the corresponding function.** -/
theorem pieceFormsEquiv_exactOne (O : V.Opens) (hO : O ≤ U)
    (c : Γ((cU (restrictDivisor U D)).toScheme, (cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) :
    pieceFormsEquiv π U D 1 O hO
        (AlgebraicGeometry.SheafOfModules.exactOne
          (Scheme.Hom.deRhamAlgebras ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π))
          (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) c) =
      AlgebraicGeometry.SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras ((cU D).ι ≫ π))
        (op ((cU D).ι ⁻¹ᵁ O)) (pieceRingEquiv U D O hO c) := by
  refine (pieceFormsEquiv_apply π U D 1 O hO _).trans ?_
  rw [ambientFormsEquiv_exactOne, sectionsEqEquiv_exactOne, ambientFormsEquiv_exactOne,
    sectionsEqEquiv_exactOne]
  have h := ambientFormsEquiv_symm_exactOne π (cU D) O (pieceRingEquiv U D O hO c)
  convert h using 3
  simp only [pieceRingEquiv, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]

end OneD

/-! ### The de Rham differential -/

section D

/-- The transport of forms along an equality of opens commutes with the de Rham differential. -/
theorem sectionsEqEquiv_d {X : Scheme.{0}} {k : Type} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) (q : ℕ) {A B : X.Opens} (h : A = B)
    (x : Γ(f.relativeDifferentialForms (q : ℤ), A)) :
    sectionsEqEquiv (f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)) h
        ((f.deRhamComplex.d q (q + 1)).val.app (op A) x) =
      (f.deRhamComplex.d q (q + 1)).val.app (op B)
        (sectionsEqEquiv (f.relativeDifferentialForms (q : ℤ)) h x) :=
  (PresheafOfModules.naturality_apply (f.deRhamComplex.d q (q + 1)).val (eqToHom h.symm).op x).symm

/-- The inverse of `ambientFormsEquiv` commutes with the de Rham differential. -/
theorem ambientFormsEquiv_symm_d {Y : Scheme.{0}} {k : Type} [Field k]
    (f : Y ⟶ Spec (CommRingCat.of k)) (W : Y.Opens) (q : ℕ) (O : Y.Opens)
    (z : Γ(f.relativeDifferentialForms (q : ℤ), O ⊓ W)) :
    (ambientFormsEquiv f W ((q + 1 : ℕ) : ℤ) O).symm
        ((f.deRhamComplex.d q (q + 1)).val.app (op (O ⊓ W)) z) =
      ((W.ι ≫ f).deRhamComplex.d q (q + 1)).val.app (op (W.ι ⁻¹ᵁ O))
        ((ambientFormsEquiv f W q O).symm z) := by
  refine (AddEquiv.symm_apply_eq _).2 ?_
  rw [MMP.FourfoldProofs.LogDegenerationProof.ambientFormsEquiv_d, AddEquiv.apply_symm_apply]

/-- **The comparison of forms of the pieces commutes with the de Rham differential.** -/
theorem pieceFormsEquiv_d (q : ℕ) (O : V.Opens) (hO : O ≤ U)
    (x : Γ(((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).relativeDifferentialForms (q : ℤ),
        (cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) :
    pieceFormsEquiv π U D ((q + 1 : ℕ) : ℤ) O hO
        ((((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).deRhamComplex.d q (q + 1)).val.app
          (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) x) =
      ((((cU D).ι ≫ π).deRhamComplex).d q (q + 1)).val.app (op ((cU D).ι ⁻¹ᵁ O))
        (pieceFormsEquiv π U D q O hO x) := by
  have h1 := MMP.FourfoldProofs.LogDegenerationProof.ambientFormsEquiv_d (U.ι ≫ π)
    (cU (restrictDivisor U D)) q (U.ι ⁻¹ᵁ O) x
  have h2 := sectionsEqEquiv_d (U.ι ≫ π) q (preimage_inf_cU_restrictDivisor U D O)
    (ambientFormsEquiv (U.ι ≫ π) (cU (restrictDivisor U D)) q (U.ι ⁻¹ᵁ O) x)
  have h3 := MMP.FourfoldProofs.LogDegenerationProof.ambientFormsEquiv_d π U q (O ⊓ cU D)
    (sectionsEqEquiv _ (preimage_inf_cU_restrictDivisor U D O)
      (ambientFormsEquiv (U.ι ≫ π) (cU (restrictDivisor U D)) q (U.ι ⁻¹ᵁ O) x))
  have h4 := sectionsEqEquiv_d π q (inf_cU_inf_eq U D O hO)
    (ambientFormsEquiv π U q (O ⊓ cU D) (sectionsEqEquiv _ (preimage_inf_cU_restrictDivisor U D O)
      (ambientFormsEquiv (U.ι ≫ π) (cU (restrictDivisor U D)) q (U.ι ⁻¹ᵁ O) x)))
  have h5 := ambientFormsEquiv_symm_d π (cU D) q O
    (sectionsEqEquiv _ (inf_cU_inf_eq U D O hO) (ambientFormsEquiv π U q (O ⊓ cU D)
      (sectionsEqEquiv _ (preimage_inf_cU_restrictDivisor U D O)
        (ambientFormsEquiv (U.ι ≫ π) (cU (restrictDivisor U D)) q (U.ι ⁻¹ᵁ O) x))))
  refine (pieceFormsEquiv_apply π U D _ O hO _).trans ?_
  erw [h1, h2, h3, h4]
  exact h5

end D

/-! ### The comparison on the pieces of the graded algebras -/

section Piece

/-- Restriction on the pieces of the graded algebra of forms is restriction of sections. -/
theorem formsPiece_map_eq {X S : Scheme.{0}} (f : X ⟶ S) (q : ℤ) {A B : X.Opens}
    (i : op A ⟶ op B)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra f).piece q).val.obj (op A)) :
    (((Scheme.Hom.relativeDifferentialFormsAlgebra f).piece q).val.map i x :
      ((Scheme.Hom.relativeDifferentialFormsAlgebra f).piece q).val.obj (op B)) =
      ((f.relativeDifferentialForms q).presheaf.map i
        (show Γ(f.relativeDifferentialForms q, A) from x) :
        Γ(f.relativeDifferentialForms q, B)) := rfl

/-- The comparison of forms of the pieces commutes with restriction, on the pieces of the graded
algebras of forms. -/
theorem pieceFormsEquiv_map_piece (q : ℤ) {O₁ O₂ : V.Opens} (h : O₁ ≤ O₂) (hO₂ : O₂ ≤ U)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece q).val.obj
        (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O₂)))) :
    (pieceFormsEquiv π U D q O₁ (h.trans hO₂)
        (((Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece q).val.map
          (homOfLE ((cU (restrictDivisor U D)).ι.preimage_mono (U.ι.preimage_mono h))).op x) :
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece q).val.obj
        (op ((cU D).ι ⁻¹ᵁ O₁))) =
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece q).val.map
        (homOfLE ((cU D).ι.preimage_mono h)).op (pieceFormsEquiv π U D q O₂ hO₂ x) := by
  have h1 : (((Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece q).val.map
          (homOfLE ((cU (restrictDivisor U D)).ι.preimage_mono (U.ι.preimage_mono h))).op x :
      ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π)).piece q).val.obj
        (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O₁)))) =
      ((((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).relativeDifferentialForms q).presheaf.map
        (homOfLE ((cU (restrictDivisor U D)).ι.preimage_mono (U.ι.preimage_mono h))).op x :
        Γ(((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).relativeDifferentialForms q,
          (cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O₁))) :=
    formsPiece_map_eq _ q _ x
  have h3 : (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece q).val.map
        (homOfLE ((cU D).ι.preimage_mono h)).op (pieceFormsEquiv π U D q O₂ hO₂ x) :
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece q).val.obj
        (op ((cU D).ι ⁻¹ᵁ O₁))) =
      ((((cU D).ι ≫ π).relativeDifferentialForms q).presheaf.map
        (homOfLE ((cU D).ι.preimage_mono h)).op (pieceFormsEquiv π U D q O₂ hO₂ x) :
        Γ(((cU D).ι ≫ π).relativeDifferentialForms q, (cU D).ι ⁻¹ᵁ O₁)) :=
    formsPiece_map_eq _ q _ _
  exact (congrArg (pieceFormsEquiv π U D q O₁ (h.trans hO₂)) h1).trans
    ((pieceFormsEquiv_map π U D q h hO₂ x).trans h3.symm)

end Piece

end MMP.FourfoldProofs.FractionalLogComplexProof
