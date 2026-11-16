module

public import MMP.AlgebraicGeometry.DeRham.Logarithmic.FrobeniusTwistHypercohomology
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RelativeEmbeddingDimensionForms
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.OpenRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.LocallyFreeTwist
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackInclInt
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceGradedForms
public import MMP.AlgebraicGeometry.DeRham.FrobeniusSplittingCocycles

/-!
# Logarithmic Hodge-to-de Rham degeneration: the Deligne-Illusie argument

Let `V` be smooth projective over `ℂ` and `S` a reduced simple normal crossing divisor. Spread
`(V, S)` out to a smooth projective relative SNC pair over a smooth `ℤ`-domain `R ⊆ ℂ` whose
fibres all have the Hodge and logarithmic de Rham dimensions of `(V, S)`
(`MMP.Mori.Divisor.exists_isRelativeSNC_model_finrank_hypercohomology_eq`). Choose a closed
point of `Spec R` with finite residue field `k` of characteristic `p > dim V`, together with a
lift `R → W₂(k)` of the residue map (`MMP.exists_isMaximal_mem_smoothLocus_witt_lift`). The
fibre over that point lifts over `W₂(k)`, so by Deligne–Illusie
(`MMP.DeRham.nonempty_logDeRham_decomposition_of_wittTwoLift`) its de Rham dimension is the sum
of its Hodge dimensions. For the twist by `-S`, tensor the decomposition by the invertible ideal
`I_S` of `S`: the terms become `Ω^q(log S) ⊗ I_S ≅ Ω^q(log S)(-S)`, and the complex becomes
`F_*Ω^•(log S) ⊗ I_S`, the subcomplex `F_*(h^p Ω^•(log S))` of `F_*Ω^•(log S)(-S) =
F_*(h Ω^•(log S))` on a chart where `h = t₁ ⋯ t_r` is the product of the boundary coordinates.
The inclusion is a quasi-isomorphism: with the Euler vector fields `θⱼ = tⱼ ∂/∂tⱼ`, the forms
`h^a Ω^•(log S)` of weight `a` along `tⱼ` are carried by `1 - a⁻¹ L_{θⱼ} = 1 - [d, a⁻¹ ι_{θⱼ}]`
into weight `a + 1`, for `1 ≤ a < p`, and composing these homotopies along all boundary
coordinates carries `h Ω^•(log S)` into `h^p Ω^•(log S)`. The fibre comparison carries the
equalities back to `ℂ`.

## Main results

* `MMP.FourfoldProofs.LogDegenerationProof.solution`: for both logarithmic de Rham complexes,
  `dim_ℂ ℍ^k(V, Ω^•) = ∑_{p+q=k} dim_ℂ H^q(V, Ω^p)`.

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*][DeligneIllusie1987]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

attribute [local instance] HasDerivedCategory.standard

namespace MMP.FourfoldProofs.LogDegenerationProof

open MMP.Mori.Divisor MMP.Mori.Divisor.LogSpreadingProof

attribute [local instance] additive_restrictScalars_underlyingRingSheaf

open Stacks.Frobenius

section AmbientForms

variable {Y : Scheme.{0}} {k : Type} [Field k] (f : Y ⟶ Spec (CommRingCat.of k)) (U : Y.Opens)

/-- `(Ω^q_{Y/k})|_U ≅ Ω^q_{U/k}` for an open subscheme `U`. -/
noncomputable def formsRestrictIso (q : ℤ) :
    (f.relativeDifferentialForms q).restrict U.ι ≅ (U.ι ≫ f).relativeDifferentialForms q :=
  Scheme.Hom.restrictFormsIso U f (U.ι ≫ f) (𝟙 _) (by rw [Category.comp_id])
    (fun n => Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ n) q

theorem image_preimage_opens_ι (O : Y.Opens) : U.ι ''ᵁ (U.ι ⁻¹ᵁ O) = O ⊓ U := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]

/-- **Forms on `U ∩ O`, read on the open subscheme `U` or on `Y`.** -/
noncomputable def ambientFormsEquiv (q : ℤ) (O : Y.Opens) :
    Γ((U.ι ≫ f).relativeDifferentialForms q, U.ι ⁻¹ᵁ O) ≃+
      Γ(f.relativeDifferentialForms q, O ⊓ U) :=
  (((Scheme.Modules.toPresheaf U.toScheme).mapIso (formsRestrictIso f U q).symm).app
      (op (U.ι ⁻¹ᵁ O))).addCommGroupIsoToAddEquiv.trans
    ((f.relativeDifferentialForms q).presheaf.mapIso
      (eqToIso (image_preimage_opens_ι U O).symm).op).addCommGroupIsoToAddEquiv

theorem ambientFormsEquiv_apply (q : ℤ) (O : Y.Opens)
    (x : Γ((U.ι ≫ f).relativeDifferentialForms q, U.ι ⁻¹ᵁ O)) :
    ambientFormsEquiv f U q O x =
      (f.relativeDifferentialForms q).presheaf.map (eqToHom (image_preimage_opens_ι U O).symm).op
        (Scheme.Modules.Hom.app (formsRestrictIso f U q).inv (U.ι ⁻¹ᵁ O) x) := rfl

/-- The comparison commutes with the de Rham differentials. -/
theorem ambientFormsEquiv_d (q : ℕ) (O : Y.Opens)
    (x : Γ((U.ι ≫ f).relativeDifferentialForms (q : ℤ), U.ι ⁻¹ᵁ O)) :
    ambientFormsEquiv f U ((q + 1 : ℕ) : ℤ) O
        (((U.ι ≫ f).deRhamComplex.d q (q + 1)).val.app (op (U.ι ⁻¹ᵁ O)) x) =
      ((f.deRhamComplex).d q (q + 1)).val.app (op (O ⊓ U)) (ambientFormsEquiv f U q O x) := by
  set y := Scheme.Modules.Hom.app (formsRestrictIso f U q).inv (U.ι ⁻¹ᵁ O) x
  have hy : Scheme.Modules.Hom.app (formsRestrictIso f U q).hom (U.ι ⁻¹ᵁ O) y = x :=
    congrArg (fun φ => Scheme.Modules.Hom.app φ (U.ι ⁻¹ᵁ O) x) (formsRestrictIso f U q).inv_hom_id
  have hd := Scheme.Hom.restrictFormsIso_hom_app_deRham_d U f (U.ι ≫ f) (𝟙 _)
    (by rw [Category.comp_id])
    (fun n => Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ n) q
    (U.ι ⁻¹ᵁ O) y
  have hinv : ∀ z, Scheme.Modules.Hom.app (formsRestrictIso f U ((q + 1 : ℕ) : ℤ)).inv
      (U.ι ⁻¹ᵁ O) (Scheme.Modules.Hom.app (formsRestrictIso f U ((q + 1 : ℕ) : ℤ)).hom
        (U.ι ⁻¹ᵁ O) z) = z := fun z =>
    congrArg (fun φ => Scheme.Modules.Hom.app φ (U.ι ⁻¹ᵁ O) z)
      (formsRestrictIso f U ((q + 1 : ℕ) : ℤ)).hom_inv_id
  have hd' : Scheme.Modules.Hom.app (formsRestrictIso f U ((q + 1 : ℕ) : ℤ)).inv (U.ι ⁻¹ᵁ O)
      (((U.ι ≫ f).deRhamComplex.d q (q + 1)).val.app (op (U.ι ⁻¹ᵁ O)) x) =
      ((f.deRhamComplex).d q (q + 1)).val.app (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ O))) y :=
    (congrArg (fun z => Scheme.Modules.Hom.app (formsRestrictIso f U ((q + 1 : ℕ) : ℤ)).inv
      (U.ι ⁻¹ᵁ O) (((U.ι ≫ f).deRhamComplex.d q (q + 1)).val.app (op (U.ι ⁻¹ᵁ O)) z))
      hy.symm).trans ((congrArg _ hd.symm).trans (hinv _))
  exact (congrArg ((f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map
    (eqToHom (image_preimage_opens_ι U O).symm).op) hd').trans
    (PresheafOfModules.naturality_apply ((f.deRhamComplex).d q (q + 1)).val
      (eqToHom (image_preimage_opens_ι U O).symm).op y).symm

/-- Restricting functions twice is restricting once. -/
theorem presheaf_map_comp_apply' {X : Scheme.{0}} {A B C : X.Opens} (i : op A ⟶ op B)
    (j : op B ⟶ op C) (k : op A ⟶ op C) (a : Γ(X, A)) :
    X.presheaf.map j (X.presheaf.map i a) = X.presheaf.map k a := by
  rw [show k = i ≫ j from Subsingleton.elim _ _, Functor.map_comp, CommRingCat.comp_apply]

/-- Restricting twice is restricting once. -/
theorem modules_map_map_apply {X : Scheme.{0}} (M : X.Modules) {A B C : X.Opens}
    (i : op A ⟶ op B) (j : op B ⟶ op C) (k : op A ⟶ op C) (x : Γ(M, A)) :
    M.presheaf.map j (M.presheaf.map i x) = M.presheaf.map k x :=
  (PresheafOfModules.map_comp_apply M.val i j x).symm.trans
    (PresheafOfModules.congr_map_apply M.val (Subsingleton.elim _ _) x)

/-- Two composites of restrictions between the same opens agree. -/
theorem modules_map_map_eq_map_map {X : Scheme.{0}} (M : X.Modules) {A B B' C : X.Opens}
    (i : op A ⟶ op B) (j : op B ⟶ op C) (i' : op A ⟶ op B') (j' : op B' ⟶ op C)
    (x : Γ(M, A)) : M.presheaf.map j (M.presheaf.map i x) = M.presheaf.map j' (M.presheaf.map i' x) :=
  (modules_map_map_apply M i j (i ≫ j) x).trans (modules_map_map_apply M i' j' (i ≫ j) x).symm

/-- The ring map `Γ(U, U ∩ O) → Γ(Y, O ∩ U)` reading functions on the open subscheme in `Y`. -/
noncomputable def ambientRingHom (O : Y.Opens) : Γ(U.toScheme, U.ι ⁻¹ᵁ O) →+* Γ(Y, O ⊓ U) :=
  (Y.presheaf.map (eqToHom (image_preimage_opens_ι U O).symm).op).hom.comp
    (U.ι.appIso (U.ι ⁻¹ᵁ O)).inv.hom

theorem ambientRingHom_app (O : Y.Opens) (a : Γ(Y, O)) :
    ambientRingHom U O ((U.ι.app O).hom a) =
      Y.presheaf.map (homOfLE (inf_le_left : O ⊓ U ≤ O)).op a := by
  have e := congrArg (fun φ => (φ ≫ Y.presheaf.map
    (eqToHom (image_preimage_opens_ι U O).symm).op).hom a) (Scheme.Hom.app_appIso_inv U.ι O)
  exact e.trans (presheaf_map_comp_apply' _ _ _ a)

/-- The comparison of forms is semilinear over `ambientRingHom`. -/
theorem ambientFormsEquiv_smul (q : ℤ) (O : Y.Opens) (c : Γ(U.toScheme, U.ι ⁻¹ᵁ O))
    (x : Γ((U.ι ≫ f).relativeDifferentialForms q, U.ι ⁻¹ᵁ O)) :
    ambientFormsEquiv f U q O (c • x) = ambientRingHom U O c • ambientFormsEquiv f U q O x := by
  rw [ambientFormsEquiv_apply, ambientFormsEquiv_apply, Scheme.Modules.Hom.app_smul]
  exact Scheme.Modules.map_smul (f.relativeDifferentialForms q)
    (eqToHom (image_preimage_opens_ι U O).symm) ((U.ι.appIso (U.ι ⁻¹ᵁ O)).inv c) _

/-- The comparison of forms commutes with restriction. -/
theorem ambientFormsEquiv_map (q : ℤ) {O₁ O₂ : Y.Opens} (h : O₁ ≤ O₂)
    (x : Γ((U.ι ≫ f).relativeDifferentialForms q, U.ι ⁻¹ᵁ O₂)) :
    ambientFormsEquiv f U q O₁
        (((U.ι ≫ f).relativeDifferentialForms q).presheaf.map
          (homOfLE (U.ι.preimage_mono h)).op x) =
      (f.relativeDifferentialForms q).presheaf.map (homOfLE (inf_le_inf_right U h)).op
        (ambientFormsEquiv f U q O₂ x) := by
  rw [ambientFormsEquiv_apply, ambientFormsEquiv_apply]
  have hnat := PresheafOfModules.naturality_apply (formsRestrictIso f U q).inv.val
    (homOfLE (U.ι.preimage_mono h)).op x
  refine (congrArg _ hnat).trans ?_
  have hk : O₁ ⊓ U ≤ U.ι ''ᵁ (U.ι ⁻¹ᵁ O₂) := by
    rw [image_preimage_opens_ι]
    exact inf_le_inf_right U h
  exact (modules_map_map_apply (f.relativeDifferentialForms q) _ _ (homOfLE hk).op _).trans
    (modules_map_map_apply (f.relativeDifferentialForms q) _ _ (homOfLE hk).op _).symm

theorem ambientFormsEquiv_symm_apply (q : ℤ) (O : Y.Opens)
    (z : Γ(f.relativeDifferentialForms q, O ⊓ U)) :
    (ambientFormsEquiv f U q O).symm z =
      Scheme.Modules.Hom.app (formsRestrictIso f U q).hom (U.ι ⁻¹ᵁ O)
        ((f.relativeDifferentialForms q).presheaf.map (eqToHom (image_preimage_opens_ι U O)).op z) := by
  refine (AddEquiv.symm_apply_eq _).2 ?_
  rw [ambientFormsEquiv_apply]
  have h := congrArg (fun φ => Scheme.Modules.Hom.app φ (U.ι ⁻¹ᵁ O)
    ((f.relativeDifferentialForms q).presheaf.map (eqToHom (image_preimage_opens_ι U O)).op z))
    (formsRestrictIso f U q).hom_inv_id
  refine Eq.trans ?_ (congrArg ((f.relativeDifferentialForms q).presheaf.map
    (eqToHom (image_preimage_opens_ι U O).symm).op) h).symm
  refine Eq.trans ?_ (modules_map_map_apply _ _ _ (𝟙 _) z).symm
  exact (congrArg (fun φ => φ z) ((f.relativeDifferentialForms q).presheaf.map_id _)).symm

/-- The comparison of forms on an exact one-form, read back on the open subscheme. -/
theorem ambientFormsEquiv_exactOne_aux (O : Y.Opens) (b : Γ(U.toScheme, U.ι ⁻¹ᵁ O)) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ f)).piece 1).val.map
        (homOfLE (U.ι.preimage_image_eq (U.ι ⁻¹ᵁ O)).ge).op
      (Scheme.Hom.relativeDifferentialFormsPullback U.ι f (U.ι ≫ f) (𝟙 _)
        (by rw [Category.comp_id]) 1 (U.ι ''ᵁ U.ι ⁻¹ᵁ O)
        (((Scheme.Hom.relativeDifferentialFormsAlgebra f).piece 1).val.map
          (eqToHom (image_preimage_opens_ι U O)).op
          (SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras f) (op (O ⊓ U))
            (ambientRingHom U O b)))) =
      SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras (U.ι ≫ f)) (op (U.ι ⁻¹ᵁ O)) b := by
  have h1 := AlgebraicGeometry.SheafOfModules.exactOne_map (Scheme.Hom.deRhamAlgebras f)
    (eqToHom (image_preimage_opens_ι U O)).op (ambientRingHom U O b)
  have h2 := Scheme.Hom.relativeDifferentialFormsPullback_exactOne U.ι f (U.ι ≫ f) (𝟙 _)
    (by rw [Category.comp_id]) (U.ι ''ᵁ U.ι ⁻¹ᵁ O)
    (Y.presheaf.map (eqToHom (image_preimage_opens_ι U O)).op (ambientRingHom U O b))
  have h3 := AlgebraicGeometry.SheafOfModules.exactOne_map
    (Scheme.Hom.deRhamAlgebras (U.ι ≫ f)) (homOfLE (U.ι.preimage_image_eq (U.ι ⁻¹ᵁ O)).ge).op
    ((U.ι.app (U.ι ''ᵁ U.ι ⁻¹ᵁ O)).hom
      (Y.presheaf.map (eqToHom (image_preimage_opens_ι U O)).op (ambientRingHom U O b)))
  have e1 : Y.presheaf.map (eqToHom (image_preimage_opens_ι U O)).op (ambientRingHom U O b) =
      (U.ι.appIso (U.ι ⁻¹ᵁ O)).inv b := by
    change Y.presheaf.map _ (Y.presheaf.map _ _) = _
    rw [presheaf_map_comp_apply' _ _ (𝟙 _), CategoryTheory.Functor.map_id]
    rfl
  have e2 := congrArg (fun φ => φ.hom b) (Scheme.Hom.appIso_inv_app_presheafMap U.ι (U.ι ⁻¹ᵁ O))
  have h4 : U.toScheme.presheaf.map (homOfLE (U.ι.preimage_image_eq (U.ι ⁻¹ᵁ O)).ge).op
      ((U.ι.app (U.ι ''ᵁ U.ι ⁻¹ᵁ O)).hom
        (Y.presheaf.map (eqToHom (image_preimage_opens_ι U O)).op (ambientRingHom U O b))) = b := by
    rw [e1]
    exact e2
  exact (congrArg _ ((congrArg _ h1).trans h2)).trans (h3.trans (congrArg _ h4))

/-- **The comparison of forms carries wedges of exact one-forms to wedges of exact
one-forms.** -/
theorem ambientFormsEquiv_homogeneousProdLeft (O : Y.Opens) (m : ℕ)
    (c : Fin m → Γ(U.toScheme, U.ι ⁻¹ᵁ O)) :
    ambientFormsEquiv f U (m : ℤ) O
        ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ f)).toPresheafGradedAlgebra.homogeneousProdLeft
          (op (U.ι ⁻¹ᵁ O)) m fun i =>
            SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras (U.ι ≫ f)) (op (U.ι ⁻¹ᵁ O)) (c i)) =
      (Scheme.Hom.relativeDifferentialFormsAlgebra f).toPresheafGradedAlgebra.homogeneousProdLeft
        (op (O ⊓ U)) m fun i =>
          SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras f) (op (O ⊓ U))
            (ambientRingHom U O (c i)) := by
  refine ((AddEquiv.symm_apply_eq _).1
    ((ambientFormsEquiv_symm_apply f U _ O _).trans ?_)).symm
  set A := (Scheme.Hom.relativeDifferentialFormsAlgebra f).toPresheafGradedAlgebra
  set A' := (Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ f)).toPresheafGradedAlgebra
  have e1 := A.homogeneousProdLeft_naturality (eqToHom (image_preimage_opens_ι U O)).op m
    fun i => SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras f) (op (O ⊓ U))
      (ambientRingHom U O (c i))
  set z' := fun i => ((Scheme.Hom.relativeDifferentialFormsAlgebra f).piece 1).val.map
    (eqToHom (image_preimage_opens_ι U O)).op
      (SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras f) (op (O ⊓ U)) (ambientRingHom U O (c i)))
  have e2 := Scheme.Hom.restrictFormsIso_hom_app U f (U.ι ≫ f) (𝟙 _) (by rw [Category.comp_id])
    (fun n => Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ n) m (U.ι ⁻¹ᵁ O)
    (A.homogeneousProdLeft (op (U.ι ''ᵁ U.ι ⁻¹ᵁ O)) m z')
  have e3 := A.homogeneousProdLeft_eq_homogeneousProd (op (U.ι ''ᵁ U.ι ⁻¹ᵁ O)) m z'
  have e4 := Scheme.Hom.relativeDifferentialFormsPullback_homogeneousProd U.ι f (U.ι ≫ f) (𝟙 _)
    (by rw [Category.comp_id]) m (U.ι ''ᵁ U.ι ⁻¹ᵁ O) z'
  have e5 := A'.homogeneousProd_naturality (homOfLE (U.ι.preimage_image_eq (U.ι ⁻¹ᵁ O)).ge).op m
    fun j => Scheme.Hom.relativeDifferentialFormsPullback U.ι f (U.ι ≫ f) (𝟙 _)
      (by rw [Category.comp_id]) 1 (U.ι ''ᵁ U.ι ⁻¹ᵁ O) (z' j)
  have e6 := A'.homogeneousProdLeft_eq_homogeneousProd (op (U.ι ⁻¹ᵁ O)) m fun j =>
    ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ f)).piece 1).val.map
      (homOfLE (U.ι.preimage_image_eq (U.ι ⁻¹ᵁ O)).ge).op
      (Scheme.Hom.relativeDifferentialFormsPullback U.ι f (U.ι ≫ f) (𝟙 _)
        (by rw [Category.comp_id]) 1 (U.ι ''ᵁ U.ι ⁻¹ᵁ O) (z' j))
  refine (congrArg _ e1).trans ?_
  refine e2.trans ?_
  refine (congrArg _ ((congrArg _ e3).trans e4)).trans ?_
  refine e5.trans ?_
  refine e6.symm.trans ?_
  exact congrArg _ (funext fun i => ambientFormsEquiv_exactOne_aux f U O (c i))

end AmbientForms

/-! ### Weak charts adapted to a simple normal crossing family -/

section SNCWeakChart

open KaehlerDifferential

/-- **Étale coordinates give a basis of the differentials.** If `k[X] → B`, `Xᵢ ↦ sᵢ`, is
formally étale, the `d sᵢ` are a basis of `Ω[B⁄k]`. -/
theorem exists_basis_D_of_formallyEtale_aeval {k B σ : Type*} [CommRing k] [CommRing B]
    [Algebra k B] (s : σ → B) (hs : (MvPolynomial.aeval (R := k) s).toRingHom.FormallyEtale) :
    ∃ b : Module.Basis σ B Ω[B⁄k], ∀ i, b i = D k B (s i) := by
  let φ := (MvPolynomial.aeval (R := k) s).toRingHom
  let : Algebra (MvPolynomial σ k) B := φ.toAlgebra
  have : IsScalarTower k (MvPolynomial σ k) B := IsScalarTower.of_algebraMap_eq fun r => by
    simp [RingHom.algebraMap_toAlgebra, φ]
  have : Algebra.FormallyEtale (MvPolynomial σ k) B := hs
  refine ⟨(isBaseChange_of_formallyEtale k (MvPolynomial σ k) B).basis (mvPolynomialBasis k σ),
    fun i => ?_⟩
  rw [IsBaseChange.basis_apply, mvPolynomialBasis_apply]
  simp [RingHom.algebraMap_toAlgebra, φ]

/-- **A weak chart adapted to a simple normal crossing family.** Let `V` be smooth of relative
dimension `n` over a field `k` and `J j` ideal sheaves whose intersections are smooth of the
expected dimension. Every point `y` of an open `O` lies in a weak chart `c ⊆ O` of the support
of the family, on which every `J j` is generated by a section `t j`, the boundary coordinates of
`c` are the `t (eB i)` for an injective `eB`, every other `t j` is a unit, and the product of
the boundary coordinates is a non-zero-divisor. -/
theorem exists_weakChart_of_snc {k : Type} [Field k] {V : Scheme.{0}}
    (f : V ⟶ Spec (CommRingCat.of k)) {n : ℕ} [SmoothOfRelativeDimension n f]
    {ι : Type} [Fintype ι] (J : ι → V.IdealSheafData)
    (hJ : ∀ T : Finset ι,
      SmoothOfRelativeDimension (n - T.card) ((⨆ j ∈ T, J j).subschemeι ≫ f) ∧
      (n < T.card → IsEmpty (⨆ j ∈ T, J j).subscheme))
    {O : V.Opens} {y : V} (hy : y ∈ O) :
    ∃ (c : WeakChart f n (((⨅ j, J j).support : Set V))) (t : ι → Γ(V, c.W)),
      (c.W : V.Opens) ≤ O ∧ y ∈ (c.W : V.Opens) ∧
      (∀ j, (J j).ideal c.W = Ideal.span {t j}) ∧
      ∃ eB : Fin c.r → ι, Function.Injective eB ∧
        (∀ i, t (eB i) = c.t (Fin.castLE c.hr i)) ∧ (∀ j, j ∉ Set.range eB → IsUnit (t j)) ∧
      IsSMulRegular Γ(V, c.W) (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) := by
  classical
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨W, t, hWO, hyW, hideal, -, hWU, hS⟩ :=
    MMP.DeRham.exists_affineOpen_snc_chart_le f J hJ _ rfl hy
  let := MMP.Mori.sectionAlgebra f W
  have : Algebra.Smooth k Γ(V, W) := MMP.Flips.ResolutionInputs.smooth_sectionAlgebra f W.2
  set 𝔭 := W.2.primeIdealOf ⟨y, hyW⟩
  have hmem : ∀ a : Γ(V, W), y ∈ V.basicOpen a ↔ a ∉ 𝔭.asIdeal := fun a ↦ by
    rw [← PrimeSpectrum.mem_basicOpen a 𝔭, ← W.2.fromSpec_preimage_basicOpen a]
    change _ ↔ W.2.fromSpec.base 𝔭 ∈ V.basicOpen a
    rw [show W.2.fromSpec.base 𝔭 = y from W.2.fromSpec_primeIdealOf ⟨y, hyW⟩]
  obtain ⟨g, hg, m, s, ε, hsε, het⟩ := MMP.DeRham.exists_etale_mvPolynomial_fin t hS 𝔭
  set g' : Γ(V, W) := g * ∏ j ∈ Finset.univ.filter (fun j => t j ∉ 𝔭.asIdeal), t j
  have hg' : g' ∉ 𝔭.asIdeal := 𝔭.asIdeal.primeCompl.mul_mem hg
    (Submonoid.prod_mem _ fun j hj => (Finset.mem_filter.1 hj).2)
  set W' : V.affineOpens := ⟨V.basicOpen g', W.2.basicOpen g'⟩
  have hW'W : (W' : V.Opens) ≤ W := V.basicOpen_le g'
  have hyW' : y ∈ (W' : V.Opens) := (hmem g').2 hg'
  set ρ : Γ(V, W) →+* Γ(V, W') := (V.presheaf.map (homOfLE hW'W).op).hom with hρ_def
  have hρg' : IsUnit (ρ g') :=
    MMP.DeRham.isUnit_map_of_le_basicOpen hW'W g' le_rfl
  have hρg'' := hρg'
  rw [map_mul, map_prod] at hρg''
  have hρg : IsUnit (ρ g) := isUnit_of_mul_isUnit_left hρg''
  have hρt : ∀ j, t j ∉ 𝔭.asIdeal → IsUnit (ρ (t j)) := fun j hj =>
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => ρ (t j))
      (Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩)) (isUnit_of_mul_isUnit_right hρg'')
  let : Algebra Γ(V, W) Γ(V, W') := ρ.toAlgebra
  have : IsLocalization.Away g' Γ(V, W') := W.2.isLocalization_basicOpen g'
  let := MMP.Mori.sectionAlgebra f W'
  have : IsScalarTower k Γ(V, W) Γ(V, W') :=
    MMP.Flips.ResolutionInputs.isScalarTower_section_res f hW'W
  have hét := MMP.DeRham.formallyEtale_aeval_of_isLocalization (k := k) s g g' hρg het
  obtain ⟨b₀, hb₀⟩ := exists_basis_D_of_formallyEtale_aeval _ hét
  have hreg : ∀ i, IsSMulRegular Γ(V, W') (ρ (s i)) := by
    intro i
    let φ := (MvPolynomial.aeval (R := k) fun i => algebraMap Γ(V, W) Γ(V, W') (s i)).toRingHom
    letI : Algebra (MvPolynomial (Fin m) k) Γ(V, W') := φ.toAlgebra
    haveI : IsScalarTower k (MvPolynomial (Fin m) k) Γ(V, W') :=
      IsScalarTower.of_algebraMap_eq fun r => by simp [RingHom.algebraMap_toAlgebra, φ]
    haveI : Algebra.FormallyEtale (MvPolynomial (Fin m) k) Γ(V, W') := hét
    haveI : Algebra.Smooth k Γ(V, W') := MMP.Flips.ResolutionInputs.smooth_sectionAlgebra f W'.2
    haveI : Algebra.FinitePresentation (MvPolynomial (Fin m) k) Γ(V, W') :=
      Algebra.FinitePresentation.of_restrict_scalars_finitePresentation k _ _
    haveI : Algebra.Etale (MvPolynomial (Fin m) k) Γ(V, W') := ⟨inferInstance, inferInstance⟩
    have h := (MMP.DeRham.isSMulRegular_mvPolynomial_X (k := k) i).of_flat (S := Γ(V, W'))
    have e : algebraMap (MvPolynomial (Fin m) k) Γ(V, W') (MvPolynomial.X i) = ρ (s i) := by
      simp [RingHom.algebraMap_toAlgebra, φ]
    rwa [e] at h
  -- the number of coordinates is the relative dimension
  have hmn : m = n := by
    set 𝔮 := W'.2.primeIdealOf ⟨y, hyW'⟩
    have h := (MMP.DeRham.finite_finrank_tensor_kaehlerDifferential_of_locally
      (MMP.DeRham.locally_isStandardSmoothOfRelativeDimension_sectionAlgebra (m := n) f W'.2)
      𝔮.asIdeal.ResidueField).2
    rwa [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis 𝔮.asIdeal.ResidueField b₀),
      Fintype.card_fin] at h
  subst hmn
  -- order the coordinates so that the boundary ones come first
  let r := Fintype.card {j : ι // t j ∈ 𝔭.asIdeal}
  let eT : Fin r ≃ {j : ι // t j ∈ 𝔭.asIdeal} := (Fintype.equivFin _).symm
  have hr : r ≤ m := by
    simpa [r] using Fintype.card_le_of_injective ε ε.injective
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hr) (fun i => ε (eT i))
    (Fin.castLE_injective hr) (ε.injective.comp eT.injective)
  set tc : Fin m → Γ(V, W') := fun i => ρ (s (σ i))
  have htc : ∀ i : Fin r, tc (Fin.castLE hr i) = ρ (t (eT i)) := fun i => by
    show ρ (s (σ (Fin.castLE hr i))) = _
    rw [hσ]
    exact congrArg ρ (hsε (eT i))
  let b₁ : Module.Basis (Fin m) Γ(V, W') Ω[Γ(V, W')⁄k] := b₀.reindex σ.symm
  have hb₁ : ∀ i, b₁ i = D k Γ(V, W') (tc i) := fun i => by
    simp only [b₁, Module.Basis.reindex_apply, Equiv.symm_symm, hb₀, tc]
    rfl
  have hbasis : letI := (f.appLE ⊤ (W' : V.Opens) (by simp)).hom.toAlgebra
      ∃ b : Module.Basis (Fin m) Γ(V, W') Ω[Γ(V, W')⁄Γ(Spec (CommRingCat.of k), ⊤)],
        ∀ i, b i = KaehlerDifferential.D Γ(Spec (CommRingCat.of k), ⊤) Γ(V, W') (tc i) := by
    refine ⟨b₁.map (MMP.DeRham.kaehlerSpecEquiv f W').symm, fun i => ?_⟩
    change (MMP.DeRham.kaehlerSpecEquiv f W').symm (b₁ i) = _
    rw [hb₁]
    exact (LinearEquiv.symm_apply_eq _).2 (MMP.DeRham.kaehlerBaseEquiv_d _ _ _ (tc i)).symm
  have hprod : ∏ i : Fin r, tc (Fin.castLE hr i) = ρ (∏ j ∈ Finset.univ.filter
      (fun j => t j ∈ 𝔭.asIdeal), t j) := by
    rw [Finset.prod_congr rfl (fun i _ => htc i), ← map_prod]
    congr 1
    rw [Equiv.prod_comp eT (fun j : {j : ι // t j ∈ 𝔭.asIdeal} => t j)]
    exact (Finset.prod_subtype _ (fun j => by simp) _).symm
  have key : ∀ y' ∈ (W' : Set V), (y' ∈ ((⨅ j, J j).support : Set V) ↔
      y' ∉ V.basicOpen (∏ i : Fin r, tc (Fin.castLE hr i))) := by
    intro y' hy'
    have hy'W : y' ∈ (W : V.Opens) := hW'W hy'
    have h1 : y' ∈ ((⨅ j, J j).support : Set V) ↔
        y' ∉ (W : V.Opens) ⊓ (⨅ j, J j).support.compl := by
      simp only [TopologicalSpace.Opens.mem_inf]
      exact ⟨fun h h' => h'.2 h, fun h => by by_contra h'; exact h ⟨hy'W, h'⟩⟩
    have h2 : y' ∈ V.basicOpen (∏ j ∈ Finset.univ.filter (fun j => ¬ t j ∈ 𝔭.asIdeal), t j) := by
      have hle : (W' : V.Opens) ≤
          V.basicOpen (∏ j ∈ Finset.univ.filter (fun j => ¬ t j ∈ 𝔭.asIdeal), t j) := by
        change V.basicOpen g' ≤ _
        rw [Scheme.basicOpen_mul]
        exact inf_le_right
      exact hle hy'
    rw [h1, hWU, hprod, Scheme.basicOpen_res,
      ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => t j ∈ 𝔭.asIdeal),
      Scheme.basicOpen_mul]
    rw [TopologicalSpace.Opens.mem_inf, TopologicalSpace.Opens.mem_inf]
    exact not_congr ⟨fun h => ⟨hy', h.1⟩, fun h => ⟨h.2, h2⟩⟩
  refine ⟨⟨W', tc, r, hr, hbasis, ?_⟩, fun j => ρ (t j), hW'W.trans hWO, hyW', fun j => ?_,
    fun i => (eT i).1, fun i i' h => eT.injective (Subtype.ext h), fun i => (htc i).symm,
    fun j hj => ?_, ?_⟩
  · ext y'
    constructor
    · rintro ⟨hZ, hy'⟩
      exact ⟨(Scheme.mem_zeroLocus_iff _ _ _).2 (by rintro _ rfl; exact (key y' hy').1 hZ), hy'⟩
    · rintro ⟨hz, hy'⟩
      exact ⟨(key y' hy').2 ((Scheme.mem_zeroLocus_iff _ _ _).1 hz _ rfl), hy'⟩
  · rw [← (J j).map_ideal hW'W, hideal j, Ideal.map_span, Set.image_singleton]
    rfl
  · refine hρt j fun hjp => hj ⟨eT.symm ⟨j, hjp⟩, ?_⟩
    change (eT (eT.symm ⟨j, hjp⟩)).1 = j
    rw [Equiv.apply_symm_apply]
  · exact Finset.prod_induction _ (IsSMulRegular Γ(V, W')) (fun a b ha hb => ha.mul hb)
      (isUnit_one.isSMulRegular _) fun i _ => hreg _

end SNCWeakChart

/-! ### Logarithmic bases on weak charts -/

/-! ### Gluing sections of modules, and forms without poles -/

section ModulesGlue

variable {Y : Scheme.{0}} (M : Y.Modules)

/-- Sections of a module agreeing on the members of a cover agree. -/
theorem modules_eq_of_cover {O : Y.Opens} {ι : Type} (V : ι → Y.Opens)
    (hV : ∀ i, V i ≤ O) (hcov : O ≤ ⨆ i, V i) {a b : Γ(M, O)}
    (h : ∀ i, M.presheaf.map (homOfLE (hV i)).op a = M.presheaf.map (homOfLE (hV i)).op b) :
    a = b :=
  let F : TopCat.Sheaf AddCommGrpCat.{0} Y := ⟨M.val.presheaf, M.isSheaf⟩
  F.eq_of_locally_eq' V O (fun i => homOfLE (hV i)) hcov a b h

/-- Compatible sections of a module on the members of a cover glue. -/
theorem modules_exists_glue {O : Y.Opens} {ι : Type} (V : ι → Y.Opens)
    (hV : ∀ i, V i ≤ O) (hcov : O ≤ ⨆ i, V i) (sf : ∀ i, Γ(M, V i))
    (hcomp : ∀ i j, M.presheaf.map (homOfLE inf_le_left : V i ⊓ V j ⟶ V i).op (sf i) =
      M.presheaf.map (homOfLE inf_le_right : V i ⊓ V j ⟶ V j).op (sf j)) :
    ∃ a : Γ(M, O), ∀ i, M.presheaf.map (homOfLE (hV i)).op a = sf i := by
  let F : TopCat.Sheaf AddCommGrpCat.{0} Y := ⟨M.val.presheaf, M.isSheaf⟩
  exact (F.existsUnique_gluing' V O (fun i => homOfLE (hV i)) hcov sf hcomp).exists

end ModulesGlue

section FormsInjective

open KaehlerDifferential

variable {Y : Scheme.{0}} {k : Type} [Field k] (f : Y ⟶ Spec (CommRingCat.of k))

/-- **Forms do not vanish on the complement of a non-zero-divisor.** On an affine open `W` with
free differentials, restricting relative forms from `W` to a basic open `D(h)`, `h` a
non-zero-divisor, is injective. -/
theorem forms_map_injective_of_eq_basicOpen (q : ℕ) (W : Y.affineOpens) (h : Γ(Y, W))
    {O : Y.Opens} (hO : O = Y.basicOpen h) (hle : O ≤ W) (hreg : IsSMulRegular Γ(Y, W) h)
    {m : ℕ} (hfree : letI := MMP.Mori.sectionAlgebra f W;
      Nonempty (Module.Basis (Fin m) Γ(Y, W) Ω[Γ(Y, W)⁄k])) :
    Function.Injective ((f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hle).op) := by
  let := MMP.Mori.sectionAlgebra f W
  let := MMP.Mori.sectionAlgebra f O
  let : Algebra Γ(Y, W) Γ(Y, O) := (Y.presheaf.map (homOfLE hle).op).hom.toAlgebra
  have := MMP.Flips.ResolutionInputs.isScalarTower_section_res f hle
  have : IsLocalization.Away h Γ(Y, O) :=
    MMP.DeRham.isLocalization_away_of_eq_basicOpen h hO hle
  have hOa : IsAffineOpen O := hO ▸ W.2.basicOpen h
  have hloc := MMP.DeRham.isLocalizedModule_mapExteriorPower_of_isLocalization (A := k)
    (Submonoid.powers h) (L' := Γ(Y, O)) q
  intro a b hab
  apply (MMP.DeRham.formsAlgEquiv f q W).injective
  have e : mapExteriorPower k Γ(Y, W) Γ(Y, O) q (MMP.DeRham.formsAlgEquiv f q W a) =
      mapExteriorPower k Γ(Y, W) Γ(Y, O) q (MMP.DeRham.formsAlgEquiv f q W b) := by
    rw [← MMP.DeRham.formsAlgEquiv_restrict f q (W' := ⟨O, hOa⟩) hle,
      ← MMP.DeRham.formsAlgEquiv_restrict f q (W' := ⟨O, hOa⟩) hle]
    exact congrArg _ hab
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers h) _).1 e
  obtain ⟨bΩ⟩ := hfree
  have : Module.Free Γ(Y, W) (⋀[Γ(Y, W)]^q (Ω[Γ(Y, W)⁄k])) :=
    Module.Free.of_basis (bΩ.exteriorPower q)
  have hR : IsRegular (h ^ m) := ⟨hreg.pow m, fun x y hxy => by
    have hxy' : x * h ^ m = y * h ^ m := hxy
    exact hreg.pow m (show h ^ m * x = h ^ m * y by rw [mul_comm, hxy', mul_comm])⟩
  haveI : Module.Flat Γ(Y, W) (⋀[Γ(Y, W)]^q (Ω[Γ(Y, W)⁄k])) := Module.Flat.of_free
  exact Module.Flat.isSMulRegular_of_isRegular hR hm

end FormsInjective

/-! ### Homotopies on the algebraic de Rham complex -/

section DeRhamHomotopy

open KaehlerDifferential KaehlerDifferential.Cartier exteriorPower

variable {A L : Type} [CommRing A] [CommRing L] [Algebra A L]

/-- The degree-preserving operator `d ∘ H` attached to a family `H : Ω^{i+1} → Ω^i`, zero in
degree `0`. -/
noncomputable def dAfter (H : ∀ i, ⋀[L]^(i + 1) (Ω[L⁄A]) →ₗ[A] ⋀[L]^i (Ω[L⁄A])) :
    ∀ i, ⋀[L]^i (Ω[L⁄A]) →ₗ[A] ⋀[L]^i (Ω[L⁄A])
  | 0 => 0
  | i + 1 => deRhamDifferential i ∘ₗ H i

/-- The chain map `1 - (d H + H d)` homotopic to the identity through `H`. -/
noncomputable def homRes (H : ∀ i, ⋀[L]^(i + 1) (Ω[L⁄A]) →ₗ[A] ⋀[L]^i (Ω[L⁄A]))
    (i : ℕ) : ⋀[L]^i (Ω[L⁄A]) →ₗ[A] ⋀[L]^i (Ω[L⁄A]) :=
  LinearMap.id - dAfter H i - H i ∘ₗ deRhamDifferential i

theorem deRhamDifferential_dAfter
    (H : ∀ i, ⋀[L]^(i + 1) (Ω[L⁄A]) →ₗ[A] ⋀[L]^i (Ω[L⁄A])) (i : ℕ) (y : ⋀[L]^i (Ω[L⁄A])) :
    deRhamDifferential (A := A) i (dAfter H i y) = 0 := by
  cases i with
  | zero => simp [dAfter]
  | succ i => exact deRhamDifferential_comp_self i _

theorem deRhamDifferential_homRes
    (H : ∀ i, ⋀[L]^(i + 1) (Ω[L⁄A]) →ₗ[A] ⋀[L]^i (Ω[L⁄A])) (i : ℕ) (y : ⋀[L]^i (Ω[L⁄A])) :
    deRhamDifferential (A := A) i (homRes H i y) = homRes H (i + 1) (deRhamDifferential i y) := by
  simp only [homRes, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub,
    deRhamDifferential_dAfter, deRhamDifferential_comp_self, map_zero, sub_zero]
  rfl

/-- The composite of two homotopies: `1 - [d, H₁ ⋆ H₂] = (1 - [d, H₂]) ∘ (1 - [d, H₁])`. -/
noncomputable def homComp (H₁ H₂ : ∀ i, ⋀[L]^(i + 1) (Ω[L⁄A]) →ₗ[A] ⋀[L]^i (Ω[L⁄A]))
    (i : ℕ) : ⋀[L]^(i + 1) (Ω[L⁄A]) →ₗ[A] ⋀[L]^i (Ω[L⁄A]) :=
  H₁ i + H₂ i ∘ₗ homRes H₁ (i + 1)

theorem homRes_homComp (H₁ H₂ : ∀ i, ⋀[L]^(i + 1) (Ω[L⁄A]) →ₗ[A] ⋀[L]^i (Ω[L⁄A]))
    (i : ℕ) (y : ⋀[L]^i (Ω[L⁄A])) :
    homRes (homComp H₁ H₂) i y = homRes H₂ i (homRes H₁ i y) := by
  have hd : dAfter (homComp H₁ H₂) i y = dAfter H₁ i y + dAfter H₂ i (homRes H₁ i y) := by
    cases i with
    | zero => simp [dAfter]
    | succ i =>
      simp only [dAfter, homComp, LinearMap.comp_apply, LinearMap.add_apply, map_add]
  have h2 : homComp H₁ H₂ i (deRhamDifferential i y) = H₁ i (deRhamDifferential i y) +
      H₂ i (deRhamDifferential i (homRes H₁ i y)) := by
    rw [deRhamDifferential_homRes]
    rfl
  change y - dAfter (homComp H₁ H₂) i y - homComp H₁ H₂ i (deRhamDifferential i y) =
    homRes H₁ i y - dAfter H₂ i (homRes H₁ i y) - H₂ i (deRhamDifferential i (homRes H₁ i y))
  rw [hd, h2]
  change _ = (y - dAfter H₁ i y - H₁ i (deRhamDifferential i y)) - _ - _
  abel

/-- The homotopy `m ι_θ`, contraction against a vector field scaled by `m`. -/
noncomputable def contractionHom (θ : Ω[L⁄A] →ₗ[L] L) (m : ℕ) (i : ℕ) :
    ⋀[L]^(i + 1) (Ω[L⁄A]) →ₗ[A] ⋀[L]^i (Ω[L⁄A]) :=
  m • (contraction θ i).restrictScalars A

theorem homRes_contractionHom (θ : Ω[L⁄A] →ₗ[L] L) (m : ℕ) (i : ℕ)
    (y : ⋀[L]^i (Ω[L⁄A])) : homRes (contractionHom θ m) i y = y - m • lie A θ i y := by
  cases i with
  | zero =>
    simp [homRes, dAfter, contractionHom, lie_zero_apply]
  | succ i =>
    simp only [homRes, dAfter, contractionHom, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.restrictScalars_apply, map_nsmul,
      lie_succ_apply, smul_add]
    abel

end DeRhamHomotopy

/-! ### Forms of given weights along the Euler fields -/

section WeightSpan

open KaehlerDifferential KaehlerDifferential.Cartier exteriorPower

variable {A B L : Type} [CommRing A] [CommRing B] [CommRing L] [Algebra A L] [Algebra B L] {n : ℕ}

/-- An additive map sending all `B`-multiples of generators into a submodule sends their span. -/
theorem map_mem_of_mem_span {M N : Type*} [AddCommGroup M] [Module B M] [AddCommGroup N]
    [Module B N] (f : M →+ N) {G : Set M} {S : Submodule B N}
    (h : ∀ g ∈ G, ∀ b : B, f (b • g) ∈ S) {y : M} (hy : y ∈ Submodule.span B G) : f y ∈ S := by
  have key : ∀ b : B, f (b • y) ∈ S := by
    induction hy using Submodule.span_induction with
    | mem g hg => exact h g hg
    | zero => intro b; rw [smul_zero, map_zero]; exact zero_mem _
    | add y y' _ _ hy hy' => intro b; rw [smul_add, map_add]; exact add_mem (hy b) (hy' b)
    | smul c y _ hy => intro b; rw [smul_smul]; exact hy (b * c)
  simpa using key 1

/-- The weight `αⱼ + #σ⁻¹(j)` of `x^α dx_σ` along the `j`-th Euler field. -/
def wt (α : Fin n → ℕ) {i : ℕ} (σ : Fin i → Fin n) (j : Fin n) : ℕ :=
  α j + ∑ k, if σ k = j then 1 else 0

variable (A L) in
/-- The form `x^α dx_σ`. -/
noncomputable def wtForm (x : Fin n → B) (α : Fin n → ℕ) {i : ℕ} (σ : Fin i → Fin n) :
    ⋀[L]^i (Ω[L⁄A]) :=
  algebraMap B L (monomial x α) • ιMulti L i fun k => D A L (algebraMap B L (x (σ k)))

variable (A L) in
/-- The `B`-span of the forms `x^α dx_σ` of weight at least `eⱼ` along every `j ∈ P`. -/
noncomputable def wtSpan (x : Fin n → B) (P : Finset (Fin n)) (i : ℕ) (e : Fin n → ℕ) :
    Submodule B (⋀[L]^i (Ω[L⁄A])) :=
  Submodule.span B {y | ∃ (α : Fin n → ℕ) (σ : Fin i → Fin n), (∀ j ∈ P, e j ≤ wt α σ j) ∧
    wtForm A L x α σ = y}

variable (x : Fin n → B) (P : Finset (Fin n))

theorem wtForm_mem_wtSpan {i : ℕ} {e : Fin n → ℕ} (α : Fin n → ℕ) (σ : Fin i → Fin n)
    (h : ∀ j ∈ P, e j ≤ wt α σ j) : wtForm A L x α σ ∈ wtSpan A L x P i e :=
  Submodule.subset_span ⟨α, σ, h, rfl⟩

theorem wtSpan_mono {i : ℕ} {e e' : Fin n → ℕ} (h : ∀ j ∈ P, e j ≤ e' j) :
    wtSpan A L x P i e' ≤ wtSpan A L x P i e :=
  Submodule.span_mono fun _ ⟨α, σ, hα, hy⟩ => ⟨α, σ, fun j hj => (h j hj).trans (hα j hj), hy⟩

theorem monomial_update_succ (α : Fin n → ℕ) (j : Fin n) :
    monomial x (Function.update α j (α j + 1)) = x j * monomial x α := by
  classical
  simp only [monomial]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ (fun l => x l ^ α l) (Finset.mem_univ j),
    Function.update_self, pow_succ, ← mul_assoc, mul_comm (x j)]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]

theorem wt_update_succ (α : Fin n → ℕ) {i : ℕ} (σ : Fin i → Fin n) (j l : Fin n) :
    wt (Function.update α j (α j + 1)) σ l = wt α σ l + if l = j then 1 else 0 := by
  unfold wt
  by_cases h : l = j
  · subst h; simp; omega
  · simp [Function.update_of_ne h, h]

/-- Multiplying by `xⱼ` raises the `j`-th weight. -/
theorem algebraMap_smul_mem_wtSpan {i : ℕ} {e : Fin n → ℕ} (j : Fin n)
    {y : ⋀[L]^i (Ω[L⁄A])} (hy : y ∈ wtSpan A L x P i e) :
    algebraMap B L (x j) • y ∈ wtSpan A L x P i (Function.update e j (e j + 1)) := by
  refine map_mem_of_mem_span (B := B) ((DistribSMul.toAddMonoidHom _ (algebraMap B L (x j)))) ?_ hy
  rintro g ⟨α, σ, hα, rfl⟩ b
  change algebraMap B L (x j) • b • wtForm A L x α σ ∈ _
  rw [smul_comm]
  refine Submodule.smul_mem _ b ?_
  have : algebraMap B L (x j) • wtForm A L x α σ =
      wtForm A L x (Function.update α j (α j + 1)) σ := by
    rw [wtForm, wtForm, smul_smul, ← map_mul, monomial_update_succ]
  rw [this]
  refine wtForm_mem_wtSpan x P _ σ fun l hl => ?_
  rw [wt_update_succ]
  by_cases h : l = j
  · subst h; simp only [Function.update_self, if_true]; have := hα l hl; omega
  · rw [Function.update_of_ne h, if_neg h, add_zero]; exact hα l hl

variable {bL : Module.Basis (Fin n) L (Ω[L⁄A])} (hb : ∀ j, bL j = D A L (algebraMap B L (x j)))

include hb

/-- **Contraction against an Euler field preserves the weights.** -/
theorem contraction_mem_wtSpan (j : Fin n) {i : ℕ} {e : Fin n → ℕ}
    {y : ⋀[L]^(i + 1) (Ω[L⁄A])} (hy : y ∈ wtSpan A L x P (i + 1) e) :
    contraction (eulerField A (fun j => algebraMap B L (x j)) bL j) i y ∈ wtSpan A L x P i e := by
  refine map_mem_of_mem_span (B := B)
    (contraction (eulerField A (fun j => algebraMap B L (x j)) bL j) i).toAddMonoidHom ?_ hy
  rintro g ⟨α, σ, hα, rfl⟩ b
  change contraction _ i (b • wtForm A L x α σ) ∈ _
  rw [← algebraMap_smul L b, map_smul, algebraMap_smul]
  refine Submodule.smul_mem _ b ?_
  rw [wtForm, map_smul, contraction_ιMulti, Finset.smul_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  rw [eulerField_D (t := fun j => algebraMap B L (x j)) hb]
  split_ifs with hm
  · have : algebraMap B L (monomial x α) •
        ((-1 : ℤ) ^ (m : ℕ) • algebraMap B L (x (σ m)) •
          ιMulti L i (m.removeNth fun k => D A L (algebraMap B L (x (σ k))))) =
        (-1 : ℤ) ^ (m : ℕ) • wtForm A L x (Function.update α j (α j + 1)) (σ ∘ m.succAbove) := by
      rw [smul_comm, smul_smul, wtForm, monomial_update_succ, map_mul, hm, mul_comm]
      rfl
    rw [this]
    refine Submodule.smul_of_tower_mem _ _ (wtForm_mem_wtSpan x P _ _ fun l hl => ?_)
    have h1 := hα l hl
    rw [wt, Fin.sum_univ_succAbove (fun k => (if σ k = l then 1 else 0 : ℕ)) m] at h1
    simp only [wt, Function.comp_apply]
    by_cases hl' : l = j
    · subst hl'
      rw [Function.update_self, if_pos hm] at *
      omega
    · rw [Function.update_of_ne hl', if_neg (by rw [hm]; exact Ne.symm hl')] at *
      omega
  · rw [zero_smul, smul_zero, smul_zero]
    exact zero_mem _

variable (hcoord : ∀ (b : B) j, bL.repr (D A L (algebraMap B L b)) j ∈ Set.range (algebraMap B L))

include hcoord

theorem eulerField_D_algebraMap (j : Fin n) (b : B) :
    ∃ c : B, eulerField A (fun j => algebraMap B L (x j)) bL j (D A L (algebraMap B L b)) =
      algebraMap B L (x j * c) := by
  obtain ⟨c, hc⟩ := hcoord b j
  exact ⟨c, by rw [eulerField, LinearMap.smul_apply, Module.Basis.coord_apply, ← hc, smul_eq_mul,
    map_mul]⟩

/-- **The forms `x^α dx_σ` are eigenvectors of the Euler fields**, with eigenvalue the weight. -/
theorem lie_wtForm (j : Fin n) (α : Fin n → ℕ) {i : ℕ} (σ : Fin i → Fin n) :
    lie A (eulerField A (fun j => algebraMap B L (x j)) bL j) i (wtForm A L x α σ) =
      wt α σ j • wtForm A L x α σ := by
  rw [wtForm, lie_smul, lie_eulerField_ιMulti_D (t := fun j => algebraMap B L (x j)) hb,
    MMP.DeRham.algebraMap_monomial, eulerField_D_monomial (t := fun j => algebraMap B L (x j)) hb,
    wt, add_nsmul, smul_comm _ (monomial _ α), ← Nat.cast_smul_eq_nsmul L (α j), smul_smul]
  congr 1
  · rw [mul_comm]
  · exact smul_comm _ _ _

/-- **The Lie derivative along an Euler field, minus the weight `eⱼ`, raises the `j`-th weight.** -/
theorem lie_sub_mem_wtSpan (j : Fin n) {i : ℕ} {e : Fin n → ℕ}
    {y : ⋀[L]^i (Ω[L⁄A])} (hy : y ∈ wtSpan A L x P i e) :
    lie A (eulerField A (fun j => algebraMap B L (x j)) bL j) i y - e j • y ∈
      wtSpan A L x P i (Function.update e j (e j + 1)) := by
  refine map_mem_of_mem_span (B := B)
    (lie A (eulerField A (fun j => algebraMap B L (x j)) bL j) i - e j • LinearMap.id).toAddMonoidHom
    ?_ hy
  rintro g ⟨α, σ, hα, rfl⟩ b
  change lie A _ i (b • wtForm A L x α σ) - e j • b • wtForm A L x α σ ∈ _
  rw [← algebraMap_smul L b, lie_smul, lie_wtForm x hb hcoord]
  obtain ⟨c, hc⟩ := eulerField_D_algebraMap x hb hcoord j b
  rw [hc, map_mul, mul_smul, add_sub_assoc, smul_comm (e j), ← smul_sub]
  refine add_mem ?_ ?_
  · rw [smul_comm, algebraMap_smul L c]
    exact Submodule.smul_mem _ c (algebraMap_smul_mem_wtSpan x P j (wtForm_mem_wtSpan x P α σ hα))
  · rw [algebraMap_smul L b]
    refine Submodule.smul_mem _ b ?_
    change (α j + ∑ k, if σ k = j then 1 else 0) • wtForm A L x α σ - e j • wtForm A L x α σ ∈ _
    by_cases hj : j ∈ P
    · have h1 := hα j hj
      rw [wt] at h1
      obtain h2 | h2 := Nat.lt_or_ge (e j) (α j + ∑ k, if σ k = j then 1 else 0)
      · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt h2
        rw [hd, add_assoc, add_nsmul, add_sub_cancel_left]
        refine Submodule.smul_of_tower_mem _ _ (wtForm_mem_wtSpan x P α σ fun l hl => ?_)
        by_cases hl' : l = j
        · subst hl'; rw [Function.update_self, wt]; omega
        · rw [Function.update_of_ne hl']; exact hα l hl
      · rw [show α j + ∑ k, (if σ k = j then 1 else 0) = e j by omega, sub_self]
        exact zero_mem _
    · refine sub_mem (Submodule.smul_of_tower_mem _ _ (wtForm_mem_wtSpan x P α σ fun l hl => ?_))
        (Submodule.smul_of_tower_mem _ _ (wtForm_mem_wtSpan x P α σ fun l hl => ?_)) <;>
      · rw [Function.update_of_ne (fun h => hj (by rwa [← h]))]; exact hα l hl

/-- **The Lie derivative along an Euler field preserves the weights.** -/
theorem lie_mem_wtSpan (j : Fin n) {i : ℕ} {e : Fin n → ℕ}
    {y : ⋀[L]^i (Ω[L⁄A])} (hy : y ∈ wtSpan A L x P i e) :
    lie A (eulerField A (fun j => algebraMap B L (x j)) bL j) i y ∈ wtSpan A L x P i e := by
  have h := wtSpan_mono x P (e := e) (e' := Function.update e j (e j + 1)) (fun l _ => by
    by_cases hl : l = j
    · subst hl; simp
    · rw [Function.update_of_ne hl]) (lie_sub_mem_wtSpan x P hb hcoord j hy)
  simpa using add_mem h (Submodule.smul_of_tower_mem _ (e j) hy)

end WeightSpan

/-! ### The Euler homotopy raising the weights along the boundary -/

section EulerHomotopy

open KaehlerDifferential KaehlerDifferential.Cartier exteriorPower

variable {A B L : Type} [CommRing A] [CommRing B] [CommRing L] [Algebra A L] [Algebra B L] {n : ℕ}
  (x : Fin n → B) (P : Finset (Fin n))
  {bL : Module.Basis (Fin n) L (Ω[L⁄A])} (hb : ∀ j, bL j = D A L (algebraMap B L (x j)))
  (hcoord : ∀ (b : B) j, bL.repr (D A L (algebraMap B L b)) j ∈ Set.range (algebraMap B L))
  (p : ℕ) [Fact p.Prime] (hpL : (p : L) = 0)

variable (A L) in
/-- A homotopy `H` preserving all the weight spans, with `1 - [d, H]` preserving them too and
carrying the forms of weight `1` along `P` to forms of weights `e`. -/
def IsWeightHomotopy (e : Fin n → ℕ)
    (H : ∀ i, ⋀[L]^(i + 1) (Ω[L⁄A]) →ₗ[A] ⋀[L]^i (Ω[L⁄A])) : Prop :=
  (∀ i e' y, y ∈ wtSpan A L x P (i + 1) e' → H i y ∈ wtSpan A L x P i e') ∧
  (∀ i e' y, y ∈ wtSpan A L x P i e' → homRes H i y ∈ wtSpan A L x P i e') ∧
  (∀ i y, y ∈ wtSpan A L x P i (fun _ => 1) → homRes H i y ∈ wtSpan A L x P i e)

theorem isWeightHomotopy_zero :
    IsWeightHomotopy A L x P (fun _ => 1) (fun _ => 0) := by
  have h : ∀ i (y : ⋀[L]^i (Ω[L⁄A])), homRes (fun _ => 0) i y = y := by
    intro i y
    cases i <;> simp [homRes, dAfter]
  refine ⟨fun i e' y _ => zero_mem _, fun i e' y hy => ?_, fun i y hy => ?_⟩ <;> rwa [h]

include hb hcoord hpL in
theorem isWeightHomotopy_step {e : Fin n → ℕ}
    {H : ∀ i, ⋀[L]^(i + 1) (Ω[L⁄A]) →ₗ[A] ⋀[L]^i (Ω[L⁄A])} (hH : IsWeightHomotopy A L x P e H)
    (j : Fin n) (hj1 : 1 ≤ e j) (hjp : e j < p) :
    ∃ H', IsWeightHomotopy A L x P (Function.update e j (e j + 1)) H' := by
  have hz : ((e j : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  set m : ℕ := (((e j : ℕ) : ZMod p)⁻¹).val
  have hm : ((m * e j : ℕ) : L) = 1 := by
    have h1 : ((m * e j : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, inv_mul_cancel₀ hz, Nat.cast_one]
    rw [ZMod.natCast_eq_natCast_iff'] at h1
    have h2 := Nat.div_add_mod (m * e j) p
    rw [h1, Nat.one_mod_eq_one.2 (by have := (Fact.out : p.Prime).two_le; omega)] at h2
    rw [← h2, Nat.cast_add, Nat.cast_mul, hpL, zero_mul, zero_add, Nat.cast_one]
  let θ := eulerField A (fun j => algebraMap B L (x j)) bL j
  refine ⟨homComp H (contractionHom θ m), ⟨fun i e' y hy => ?_, fun i e' y hy => ?_,
    fun i y hy => ?_⟩⟩
  · refine add_mem (hH.1 i e' y hy) ?_
    change m • contraction θ i (homRes H (i + 1) y) ∈ _
    exact Submodule.smul_of_tower_mem _ _
      (contraction_mem_wtSpan x P hb j (hH.2.1 (i + 1) e' y hy))
  · rw [homRes_homComp, homRes_contractionHom]
    have hr := hH.2.1 i e' y hy
    exact sub_mem hr (Submodule.smul_of_tower_mem _ _ (lie_mem_wtSpan x P hb hcoord j hr))
  · rw [homRes_homComp, homRes_contractionHom]
    have hr := hH.2.2 i y hy
    have hl := lie_sub_mem_wtSpan x P hb hcoord j hr
    have : homRes H i y - m • lie A θ i (homRes H i y) =
        -(m • (lie A θ i (homRes H i y) - e j • homRes H i y)) := by
      rw [smul_sub, smul_smul, ← Nat.cast_smul_eq_nsmul L (m * e j), hm, one_smul]
      abel
    rw [this]
    exact neg_mem (Submodule.smul_of_tower_mem _ _ hl)

include hb hcoord hpL in
theorem exists_isWeightHomotopy_of_subset (S : Finset (Fin n)) :
    ∃ H, IsWeightHomotopy A L x P (fun j => if j ∈ S then p else 1) H := by
  classical
  have hp := (Fact.out : p.Prime).two_le
  induction S using Finset.induction_on with
  | empty => simpa using ⟨_, isWeightHomotopy_zero x P⟩
  | insert j S hjS ih =>
    set e₀ : Fin n → ℕ := fun l => if l ∈ S then p else 1
    have key : ∀ b, 1 ≤ b → b ≤ p → ∃ H,
        IsWeightHomotopy A L x P (Function.update e₀ j b) H := by
      intro b hb1
      induction b, hb1 using Nat.le_induction with
      | base =>
        intro _
        obtain ⟨H, hH⟩ := ih
        refine ⟨H, ?_⟩
        convert hH using 2
        funext l
        by_cases hl : l = j
        · subst hl; simp [e₀, hjS]
        · rw [Function.update_of_ne hl]
      | succ b hb1 ihb =>
        intro hbp
        obtain ⟨H, hH⟩ := ihb (by omega)
        obtain ⟨H', hH'⟩ := isWeightHomotopy_step x P hb hcoord p hpL hH j
          (by rw [Function.update_self]; exact hb1) (by rw [Function.update_self]; omega)
        rw [Function.update_self, Function.update_idem] at hH'
        exact ⟨H', hH'⟩
    obtain ⟨H, hH⟩ := key p (by omega) le_rfl
    have he : Function.update e₀ j p = fun l => if l ∈ insert j S then p else 1 := by
      funext l
      by_cases hl : l = j
      · subst hl; simp
      · rw [Function.update_of_ne hl]
        simp [e₀, Finset.mem_insert, hl]
    rw [he] at hH
    exact ⟨H, hH⟩

include hb hcoord hpL in
/-- **The Euler homotopy.** There is a homotopy `H` preserving the weight spans such that
`1 - [d, H]` carries the forms of weight `≥ 1` along `P` into those of weight `≥ p`. -/
theorem exists_eulerHomotopy :
    ∃ H : ∀ i, ⋀[L]^(i + 1) (Ω[L⁄A]) →ₗ[A] ⋀[L]^i (Ω[L⁄A]),
      (∀ i e' y, y ∈ wtSpan A L x P (i + 1) e' → H i y ∈ wtSpan A L x P i e') ∧
      (∀ i y, y ∈ wtSpan A L x P i (fun _ => 1) → homRes H i y ∈ wtSpan A L x P i (fun _ => p)) := by
  obtain ⟨H, hH⟩ := exists_isWeightHomotopy_of_subset x P hb hcoord p hpL P
  refine ⟨H, hH.1, fun i y hy => wtSpan_mono x P (fun j hj => ?_) (hH.2.2 i y hy)⟩
  simp [hj]

end EulerHomotopy

/-! ### Twisted logarithmic forms as weight spans -/

section TwistedLogForms

open KaehlerDifferential KaehlerDifferential.Cartier exteriorPower

variable {A B L : Type} [CommRing A] [CommRing B] [CommRing L] [Algebra A L] [Algebra B L] {n : ℕ}
  {x : Fin n → B} {P : Finset (Fin n)}
  {bL : Module.Basis (Fin n) L (Ω[L⁄A])} (hb : ∀ j, bL j = D A L (algebraMap B L (x j)))
  (hP : ∀ j ∈ P, IsUnit (algebraMap B L (x j))) {ι : Type*} {u : ι → B}

variable (A L x P u) in
/-- The logarithmic forms twisted by `(∏_{j ∈ P} xⱼ)^a`. -/
def IsTwistedLogForm (a i : ℕ) (y : ⋀[L]^i (Ω[L⁄A])) : Prop :=
  ∃ y₀ : ⋀[L]^i (Ω[L⁄A]), (y₀ : ExteriorAlgebra L (Ω[L⁄A])) ∈ MMP.DeRham.logForms A L u i ∧
    y = algebraMap B L (∏ j ∈ P, x j) ^ a • y₀

theorem prod_ite_mem_eq {M : Type*} [CommMonoid M] (S : Finset (Fin n)) (f : Fin n → M) :
    ∏ j ∈ S, f j = ∏ j, if j ∈ S then f j else 1 := by
  rw [Finset.prod_ite_mem, Finset.univ_inter]

include hP in
theorem pow_mul_prod_logScale {a : ℕ} (ha : 1 ≤ a) {i : ℕ} (s : Set.powersetCard (Fin n) i) :
    algebraMap B L (∏ j ∈ P, x j) ^ a * ∏ k, MMP.DeRham.logScale (L := L) P x (enum s k) =
      algebraMap B L (monomial x fun j =>
        if j ∈ P then a - (if j ∈ (s : Finset (Fin n)) then 1 else 0) else 0) := by
  classical
  rw [MMP.DeRham.prod_enum, map_prod, ← Finset.prod_pow, prod_ite_mem_eq P,
    prod_ite_mem_eq (s : Finset (Fin n)), ← Finset.prod_mul_distrib, MMP.DeRham.algebraMap_monomial,
    monomial]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hjP : j ∈ P <;> by_cases hjs : j ∈ (s : Finset (Fin n)) <;>
    simp only [hjP, hjs, if_true, if_false, MMP.DeRham.logScale, one_mul, mul_one, pow_zero,
      Nat.sub_zero]
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ, mul_assoc, Ring.mul_inverse_cancel _ (hP j hjP), mul_one]

variable (hcoord : ∀ (b : B) j, bL.repr (D A L (algebraMap B L b)) j ∈ Set.range (algebraMap B L))
  (hu₁ : ∀ k, ∃ j ∈ P, x j = u k) (hu₂ : ∀ j ∈ P, ∃ k, u k = x j)

include hb hP hcoord hu₁ in
/-- **Twisted logarithmic forms have weight `a` along the boundary.** -/
theorem IsTwistedLogForm.mem_wtSpan {a i : ℕ} (ha : 1 ≤ a) {y : ⋀[L]^i (Ω[L⁄A])}
    (hy : IsTwistedLogForm A L x P u a i y) : y ∈ wtSpan A L x P i (fun _ => a) := by
  classical
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  obtain ⟨c, rfl⟩ := MMP.DeRham.exists_eq_sum_logBasis hP hb hu₁ hcoord y₀ hy₀
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [smul_comm (algebraMap B L (∏ j ∈ P, x j) ^ a) (algebraMap B L (c s)),
    MMP.DeRham.logBasis_exteriorPower_apply hP, smul_smul (algebraMap B L (∏ j ∈ P, x j) ^ a),
    pow_mul_prod_logScale hP ha, exteriorPower_basis_eq (t := fun j => algebraMap B L (x j)) hb,
    algebraMap_smul L (c s)]
  refine Submodule.smul_mem _ _ (wtForm_mem_wtSpan x P _ (enum s) fun j hj => ?_)
  rw [wt, sum_enum_eq, if_pos hj]
  split_ifs <;> omega

include hb hP hu₂ in
/-- **Forms of weight `a` along the boundary are twisted logarithmic forms.** -/
theorem IsTwistedLogForm.of_mem_wtSpan {a i : ℕ} {y : ⋀[L]^i (Ω[L⁄A])}
    (hy : y ∈ wtSpan A L x P i (fun _ => a)) : IsTwistedLogForm A L x P u a i y := by
  classical
  induction hy using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨α, σ, hα, rfl⟩ := hg
    have hbL : ∀ l, D A L (algebraMap B L (x l)) =
        algebraMap B L (MMP.DeRham.poleFactor P x l) • MMP.DeRham.logBasis bL hP l := by
      intro l
      rw [MMP.DeRham.logBasis_apply, smul_smul, mul_comm, MMP.DeRham.logScale_mul_poleFactor hP,
        one_smul, hb]
    let γ : Fin n → ℕ := fun j => if j ∈ P then wt α σ j - a else α j
    refine ⟨algebraMap B L (monomial x γ) •
      ιMulti L i (fun k => MMP.DeRham.logBasis bL hP (σ k)), ?_, ?_⟩
    · rw [Submodule.coe_smul, algebraMap_smul, ιMulti_apply_coe]
      exact Submodule.smul_mem _ _ (MMP.DeRham.ιMulti_mem_logForms _ fun k =>
        MMP.DeRham.logBasis_mem_logGenerators hP hb hu₂ _)
    · rw [wtForm]
      simp_rw [hbL]
      rw [AlternatingMap.map_smul_univ, smul_smul, smul_smul, ← map_prod, ← map_mul, ← map_pow,
        ← map_mul]
      congr 2
      -- the monomial identity
      have hfib : ∏ k, MMP.DeRham.poleFactor P x (σ k) =
          ∏ j, MMP.DeRham.poleFactor P x j ^ (∑ k, if σ k = j then 1 else 0 : ℕ) := by
        rw [← Finset.prod_fiberwise Finset.univ σ (fun k => MMP.DeRham.poleFactor P x (σ k))]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Finset.prod_congr rfl (fun k hk => by rw [(Finset.mem_filter.1 hk).2]),
          Finset.prod_const, Finset.sum_boole, Nat.cast_id]
      rw [hfib, monomial, monomial, prod_ite_mem_eq P, ← Finset.prod_pow,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hjP : j ∈ P
      · have h1 := hα j hjP
        simp only [γ, MMP.DeRham.poleFactor, hjP, if_true, wt] at h1 ⊢
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      · simp [γ, MMP.DeRham.poleFactor, hjP]
  | zero => exact ⟨0, by simp, by simp⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨y₀, h₀, rfl⟩ := hy
    obtain ⟨y₀', h₀', rfl⟩ := hy'
    exact ⟨y₀ + y₀', by rw [Submodule.coe_add]; exact add_mem h₀ h₀', by rw [smul_add]⟩
  | smul b y _ hy =>
    obtain ⟨y₀, h₀, rfl⟩ := hy
    exact ⟨b • y₀, by rw [Submodule.coe_smul_of_tower]; exact Submodule.smul_mem _ b h₀,
      by rw [smul_comm]⟩

end TwistedLogForms

/-! ### The twisted logarithmic complexes `h Ω^•(log)` and `h^p Ω^•(log)` are cohomologous -/

section TwistedLogCohomology

open KaehlerDifferential KaehlerDifferential.Cartier exteriorPower

variable {A B L : Type} [CommRing A] [CommRing B] [CommRing L] [Algebra A L] [Algebra B L] {n : ℕ}
  {x : Fin n → B} {P : Finset (Fin n)} {ι : Type*} {u : ι → B}

theorem IsTwistedLogForm.add {a i : ℕ} {y y' : ⋀[L]^i (Ω[L⁄A])}
    (hy : IsTwistedLogForm A L x P u a i y) (hy' : IsTwistedLogForm A L x P u a i y') :
    IsTwistedLogForm A L x P u a i (y + y') := by
  obtain ⟨y₀, h₀, rfl⟩ := hy
  obtain ⟨y₀', h₀', rfl⟩ := hy'
  exact ⟨y₀ + y₀', by rw [Submodule.coe_add]; exact add_mem h₀ h₀', by rw [smul_add]⟩

variable {bL : Module.Basis (Fin n) L (Ω[L⁄A])} (hb : ∀ j, bL j = D A L (algebraMap B L (x j)))
  (hP : ∀ j ∈ P, IsUnit (algebraMap B L (x j)))
  (hcoord : ∀ (b : B) j, bL.repr (D A L (algebraMap B L b)) j ∈ Set.range (algebraMap B L))
  (hu₁ : ∀ k, ∃ j ∈ P, x j = u k) (hu₂ : ∀ j ∈ P, ∃ k, u k = x j)
  (p : ℕ) [Fact p.Prime] (hpL : (p : L) = 0)

include hb hP hcoord hu₁ hu₂ hpL in
/-- **The Euler homotopy on twisted logarithmic forms**: a homotopy preserving the logarithmic
forms twisted by `h = ∏_{j ∈ P} xⱼ` and by `h^p`, with `1 - [d, H]` carrying the first into the
second. -/
theorem exists_twistedLogForm_homotopy :
    ∃ H : ∀ i, ⋀[L]^(i + 1) (Ω[L⁄A]) →ₗ[A] ⋀[L]^i (Ω[L⁄A]),
      (∀ i y, IsTwistedLogForm A L x P u 1 (i + 1) y → IsTwistedLogForm A L x P u 1 i (H i y)) ∧
      (∀ i y, IsTwistedLogForm A L x P u p (i + 1) y → IsTwistedLogForm A L x P u p i (H i y)) ∧
      (∀ i y, IsTwistedLogForm A L x P u 1 i y →
        IsTwistedLogForm A L x P u p i (homRes H i y)) := by
  have hp := (Fact.out : p.Prime).one_lt
  obtain ⟨H, h1, h2⟩ := exists_eulerHomotopy x P hb hcoord p hpL
  refine ⟨H, fun i y hy => ?_, fun i y hy => ?_, fun i y hy => ?_⟩
  · exact IsTwistedLogForm.of_mem_wtSpan hb hP hu₂
      (h1 i _ y (IsTwistedLogForm.mem_wtSpan hb hP hcoord hu₁ le_rfl hy))
  · exact IsTwistedLogForm.of_mem_wtSpan hb hP hu₂
      (h1 i _ y (IsTwistedLogForm.mem_wtSpan hb hP hcoord hu₁ hp.le hy))
  · exact IsTwistedLogForm.of_mem_wtSpan hb hP hu₂
      (h2 i y (IsTwistedLogForm.mem_wtSpan hb hP hcoord hu₁ le_rfl hy))

include hb hP hcoord hu₁ hu₂ hpL in
/-- A closed function in `h Ω⁰(log)` lies in `h^p Ω⁰(log)`. -/
theorem IsTwistedLogForm.pow_of_closed_zero {z : ⋀[L]^0 (Ω[L⁄A])}
    (hz : IsTwistedLogForm A L x P u 1 0 z) (hdz : deRhamDifferential (A := A) 0 z = 0) :
    IsTwistedLogForm A L x P u p 0 z := by
  obtain ⟨H, -, -, h3⟩ := exists_twistedLogForm_homotopy hb hP hcoord hu₁ hu₂ p hpL
  have := h3 0 z hz
  simpa [homRes, dAfter, hdz] using this

include hb hP hcoord hu₁ hu₂ hpL in
/-- A closed form in `h Ω^{i+1}(log)` differs from a form in `h^p Ω^{i+1}(log)` by the
differential of a form in `h Ω^i(log)`. -/
theorem IsTwistedLogForm.exists_sub_deRhamDifferential {i : ℕ}
    {z : ⋀[L]^(i + 1) (Ω[L⁄A])} (hz : IsTwistedLogForm A L x P u 1 (i + 1) z)
    (hdz : deRhamDifferential (A := A) (i + 1) z = 0) :
    ∃ y, IsTwistedLogForm A L x P u 1 i y ∧
      IsTwistedLogForm A L x P u p (i + 1) (z - deRhamDifferential (A := A) i y) := by
  obtain ⟨H, h1, -, h3⟩ := exists_twistedLogForm_homotopy hb hP hcoord hu₁ hu₂ p hpL
  refine ⟨H i z, h1 i z hz, ?_⟩
  have := h3 (i + 1) z hz
  simpa [homRes, dAfter, hdz] using this

include hb hP hcoord hu₁ hu₂ hpL in
/-- The differential of a form in `h Ω^i(log)` which lies in `h^p Ω^{i+1}(log)` is the
differential of a form in `h^p Ω^i(log)`. -/
theorem IsTwistedLogForm.exists_deRhamDifferential_eq {i : ℕ}
    {y : ⋀[L]^i (Ω[L⁄A])} (hy : IsTwistedLogForm A L x P u 1 i y)
    (hdy : IsTwistedLogForm A L x P u p (i + 1) (deRhamDifferential (A := A) i y)) :
    ∃ y', IsTwistedLogForm A L x P u p i y' ∧
      deRhamDifferential (A := A) i y' = deRhamDifferential (A := A) i y := by
  obtain ⟨H, -, h2, h3⟩ := exists_twistedLogForm_homotopy hb hP hcoord hu₁ hu₂ p hpL
  refine ⟨homRes H i y + H i (deRhamDifferential i y), (h3 i y hy).add (h2 i _ hdy), ?_⟩
  have : homRes H i y + H i (deRhamDifferential i y) = y - dAfter H i y := by
    simp only [homRes, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    abel
  rw [this, map_sub, deRhamDifferential_dAfter, sub_zero]

end TwistedLogCohomology

/-! ### Logarithmic forms on a weak chart, read in algebra -/

section LogBridge

open MMP.Mori.Divisor.LogSpreadingProof.G1 KaehlerDifferential

variable {k : Type} [Field k] {V : Scheme.{0}} (f : V ⟶ Spec (CommRingCat.of k)) {n : ℕ}
  [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor V)

/-- On a weak chart, the complement of the divisor is the basic open of the product of the
boundary coordinates. -/
theorem weakChart_inf_LU (c : WeakChart f n (D.supp : Set V)) :
    (c.W : V.Opens) ⊓ LU D = V.basicOpen (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) := by
  ext y
  change y ∈ (c.W : Set V) ∧ y ∉ (D.supp : Set V) ↔ y ∈ V.basicOpen _
  have hz := Set.ext_iff.1 c.zero y
  simp only [Set.mem_inter_iff] at hz
  constructor
  · rintro ⟨hyW, hyD⟩
    by_contra hb
    exact hyD (hz.2 ⟨(Scheme.mem_zeroLocus_iff _ _ _).2 (by rintro _ rfl; exact hb), hyW⟩).1
  · intro hb
    have hyW : y ∈ (c.W : Set V) := V.basicOpen_le _ hb
    refine ⟨hyW, fun hyD => ?_⟩
    exact (Scheme.mem_zeroLocus_iff _ _ _).1 (hz.1 ⟨hyD, hyW⟩).1 _ rfl hb

set_option maxRecDepth 20000 in
/-- The comparison `formsAlgEquiv` on a wedge of exact one-forms. -/
theorem formsAlgEquiv_homogeneousProdLeft (m : ℕ) (W : V.affineOpens)
    (b : Fin m → Γ(V, W)) :
    letI := MMP.Mori.sectionAlgebra f W
    MMP.DeRham.formsAlgEquiv f m W
        ((Scheme.Hom.relativeDifferentialFormsAlgebra f).toPresheafGradedAlgebra.homogeneousProdLeft
          (op (W : V.Opens)) m fun i =>
            SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras f) (op (W : V.Opens)) (b i)) =
      exteriorPower.ιMulti Γ(V, W) m fun i => KaehlerDifferential.D k Γ(V, W) (b i) := by
  let := MMP.Mori.sectionAlgebra f W
  refine (MMP.DeRham.formsAlgEquiv_apply f m W _).trans ?_
  have h := Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_smul_homogeneousProdLeft
    f W.2 (isAffineOpen_top _) (by simp) m 1 b
  rw [one_smul, one_smul] at h
  refine (congrArg (exteriorPower.map m (MMP.DeRham.kaehlerSpecEquiv f W).toLinearMap) h).trans ?_
  exact (exteriorPower.map_apply_ιMulti _ _).trans
    (congrArg _ (funext fun i => MMP.DeRham.kaehlerBaseEquiv_d _ _ _ (b i)))

set_option maxRecDepth 20000 in
/-- **A monomial in exact one-forms, read in algebra.** For functions `b` and `l` on `U ∩ W'`,
`b · d l₁ ∧ ⋯ ∧ d lₘ` is a homogeneous form, and the comparison carries it to the algebraic form
with the same expression. -/
theorem exists_incl_eq_and_formsAlgEquiv_eq (W' : V.Opens)
    (hA : IsAffineOpen (W' ⊓ LU D)) (b : Γ((LU D).toScheme, (LU D).ι ⁻¹ᵁ W'))
    (l : List Γ((LU D).toScheme, (LU D).ι ⁻¹ᵁ W')) (m : ℕ) (hm : l.length = m) :
    ∃ z : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece (m : ℤ)).val.obj
        (op ((LU D).ι ⁻¹ᵁ W')),
      (TB ((LU D).ι ≫ f)).incl (m : ℤ) z = smU (f := f) (D := D) _ b *
          (l.map fun a => (TB ((LU D).ι ≫ f)).incl 1 (dOne f D _ a)).prod ∧
      letI := MMP.Mori.sectionAlgebra f (W' ⊓ LU D)
      MMP.DeRham.formsAlgEquiv f m ⟨W' ⊓ LU D, hA⟩ (ambientFormsEquiv f (LU D) m W' z) =
        ambientRingHom (LU D) W' b • exteriorPower.ιMulti Γ(V, W' ⊓ LU D) m fun i =>
          KaehlerDifferential.D k Γ(V, W' ⊓ LU D) (ambientRingHom (LU D) W' (l.get (Fin.cast hm.symm i))) := by
  subst hm
  refine ⟨(show (Stacks.RingedSpace.structureRingSheaf (LU D).toScheme.toRingedSpace).obj.obj
      (op ((LU D).ι ⁻¹ᵁ W')) from b) •
    (TB ((LU D).ι ≫ f)).homogeneousProdLeft (op ((LU D).ι ⁻¹ᵁ W')) l.length
    fun i => SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras ((LU D).ι ≫ f))
      (op ((LU D).ι ⁻¹ᵁ W')) (l.get i), ?_, ?_⟩
  · refine (incl_smul_eq f D _ b _).trans (congrArg (smU (f := f) (D := D) _ b * ·) ?_)
    refine ((TB ((LU D).ι ≫ f)).incl_homogeneousProdLeft (op _) l.length _).trans ?_
    conv_rhs => rw [← List.ofFn_get l, List.map_ofFn]
    rfl
  · let := MMP.Mori.sectionAlgebra f (W' ⊓ LU D)
    have h1 := ambientFormsEquiv_smul f (LU D) (l.length : ℤ) W' b
      ((TB ((LU D).ι ≫ f)).homogeneousProdLeft (op ((LU D).ι ⁻¹ᵁ W')) l.length
        fun i => SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras ((LU D).ι ≫ f))
          (op ((LU D).ι ⁻¹ᵁ W')) (l.get i))
    have h2 := ambientFormsEquiv_homogeneousProdLeft f (LU D) W' l.length l.get
    refine (congrArg (MMP.DeRham.formsAlgEquiv f l.length ⟨W' ⊓ LU D, hA⟩)
      (h1.trans (congrArg _ h2))).trans ?_
    refine (map_smul _ _ _).trans ?_
    have h3 := formsAlgEquiv_homogeneousProdLeft f l.length ⟨W' ⊓ LU D, hA⟩
      fun i => ambientRingHom (LU D) W' (l.get i)
    simp only [Fin.cast_eq_self]
    exact congrArg (ambientRingHom (LU D) W' b • ·) h3

/-- **Coordinates off the divisor on a weak chart**: the differentials of the coordinates are a
basis of `Ω[Γ(W ∖ D)⁄k]`, in which the differentials of functions on `W` have coefficients
coming from `W`. -/
theorem exists_basis_inf_LU_of_weakChart (c : WeakChart f n (D.supp : Set V)) :
    letI := MMP.Mori.sectionAlgebra f ((c.W : V.Opens) ⊓ LU D)
    letI : Algebra Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) :=
      (V.presheaf.map (homOfLE (inf_le_left : (c.W : V.Opens) ⊓ LU D ≤ c.W)).op).hom.toAlgebra
    ∃ bL : Module.Basis (Fin n) Γ(V, (c.W : V.Opens) ⊓ LU D) Ω[Γ(V, (c.W : V.Opens) ⊓ LU D)⁄k],
      (∀ i, bL i = KaehlerDifferential.D k Γ(V, (c.W : V.Opens) ⊓ LU D)
        (algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) (c.t i))) ∧
      (∀ (b : Γ(V, c.W)) j, bL.repr (KaehlerDifferential.D k Γ(V, (c.W : V.Opens) ⊓ LU D)
        (algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) b)) j ∈
          Set.range (algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D))) := by
  have hWU := weakChart_inf_LU f D c
  let := MMP.Mori.sectionAlgebra f c.W
  let := MMP.Mori.sectionAlgebra f ((c.W : V.Opens) ⊓ LU D)
  let : Algebra Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) :=
    (V.presheaf.map (homOfLE (inf_le_left : (c.W : V.Opens) ⊓ LU D ≤ c.W)).op).hom.toAlgebra
  have : IsScalarTower k Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) :=
    MMP.Flips.ResolutionInputs.isScalarTower_section_res f inf_le_left
  have : IsLocalization.Away (∏ i : Fin c.r, c.t (Fin.castLE c.hr i))
      Γ(V, (c.W : V.Opens) ⊓ LU D) :=
    MMP.DeRham.isLocalization_away_of_eq_basicOpen _ hWU inf_le_left
  have : Algebra.FormallyEtale Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)))
  obtain ⟨b₀, hb₀⟩ := c.basis
  let bB : Module.Basis (Fin n) Γ(V, c.W) Ω[Γ(V, c.W)⁄k] :=
    b₀.map (MMP.DeRham.kaehlerSpecEquiv f c.W)
  have hbB : ∀ i, bB i = KaehlerDifferential.D k Γ(V, c.W) (c.t i) := fun i => by
    change MMP.DeRham.kaehlerSpecEquiv f c.W (b₀ i) = _
    rw [hb₀]
    exact MMP.DeRham.kaehlerBaseEquiv_d _ _ _ _
  let bL : Module.Basis (Fin n) Γ(V, (c.W : V.Opens) ⊓ LU D)
      Ω[Γ(V, (c.W : V.Opens) ⊓ LU D)⁄k] :=
    (Algebra.TensorProduct.basis Γ(V, (c.W : V.Opens) ⊓ LU D) bB).map
      (tensorKaehlerEquivOfFormallyEtale k Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D))
  have hD' : ∀ b, KaehlerDifferential.D k Γ(V, (c.W : V.Opens) ⊓ LU D)
      (algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) b) =
      tensorKaehlerEquivOfFormallyEtale k Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D)
        ((1 : Γ(V, (c.W : V.Opens) ⊓ LU D)) ⊗ₜ KaehlerDifferential.D k Γ(V, c.W) b) := by
    intro b
    rw [tensorKaehlerEquivOfFormallyEtale_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul,
      KaehlerDifferential.map_D]
  refine ⟨bL, fun i => ?_, fun b j => ?_⟩
  · rw [hD', ← hbB]
    simp only [bL, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
  · refine ⟨bB.repr (KaehlerDifferential.D k Γ(V, c.W) b) j, ?_⟩
    rw [hD']
    simp only [bL, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]

/-- On a weak chart, the scaling factors of the logarithmic coordinate data are the inverses of
the boundary coordinates and `1` on the other coordinates. -/
theorem ambientRingHom_toLogData_σ (c : WeakChart f n (D.supp : Set V)) (i : Fin n) :
    letI : Algebra Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) :=
      (V.presheaf.map (homOfLE (inf_le_left : (c.W : V.Opens) ⊓ LU D ≤ c.W)).op).hom.toAlgebra
    ambientRingHom (LU D) c.W ((c.toLogData f D).σ (le_rfl : (c.W : V.Opens) ≤ (c.toLogData f D).W) i) =
      MMP.DeRham.logScale (L := Γ(V, (c.W : V.Opens) ⊓ LU D))
        (Finset.univ.map (Fin.castLEEmb c.hr)) c.t i := by
  classical
  let : Algebra Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) :=
    (V.presheaf.map (homOfLE (inf_le_left : (c.W : V.Opens) ⊓ LU D ≤ c.W)).op).hom.toAlgebra
  let P : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb c.hr)
  have hmemP : ∀ j : Fin n, j ∈ P ↔ (j : ℕ) < c.r := fun j => by
    simp only [P, Finset.mem_map, Finset.mem_univ, true_and, Fin.castLEEmb_apply]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ i.2, fun h => ⟨⟨j, h⟩, rfl⟩⟩
  have hle : (c.W : V.Opens) ≤ (c.toLogData f D).W := le_rfl
  unfold LogData.σ MMP.DeRham.logScale
  by_cases hi : (i : ℕ) < c.r
  · rw [dif_pos (show (i : ℕ) < (c.toLogData f D).r from hi), if_pos ((hmemP i).2 hi)]
    have hs := c.toLogData_hs f D ⟨i, hi⟩
    have hmap : (LU D).toScheme.presheaf.map ((TopologicalSpace.Opens.map (LU D).ι.base).map (homOfLE hle)).op
        ((c.toLogData f D).s ⟨i, hi⟩) = (c.toLogData f D).s ⟨i, hi⟩ := by
      rw [show ((TopologicalSpace.Opens.map (LU D).ι.base).map (homOfLE hle)).op = 𝟙 _ from
        Subsingleton.elim _ _]
      erw [CategoryTheory.Functor.map_id]
      rfl
    rw [hmap]
    have h2 : ambientRingHom (LU D) c.W ((c.toLogData f D).s ⟨i, hi⟩) *
        algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) (c.t i) = 1 := by
      have h3 := (map_mul (ambientRingHom (LU D) c.W) _ _).symm.trans
        ((congrArg (ambientRingHom (LU D) c.W) hs).trans (map_one _))
      erw [ambientRingHom_app] at h3
      exact h3
    have hu := IsUnit.of_mul_eq_one_right _ h2
    exact ((Ring.eq_mul_inverse_iff_mul_eq _ _ _ hu).2 h2).trans (one_mul _)
  · rw [dif_neg (show ¬ (i : ℕ) < (c.toLogData f D).r from hi),
      if_neg (fun h => hi ((hmemP i).1 h)), map_one]

variable [IsRegularRing (CommRingCat.of k)]

set_option maxRecDepth 40000 in
/-- **Logarithmic forms on a weak chart, read in algebra.** On a weak chart `W` of the support of
a relative snc divisor `D` with boundary coordinates `t₁, …, t_r`, a form on `W ∖ D` is a
logarithmic form exactly when, read in `⋀ Ω[Γ(W ∖ D)⁄k]`, it lies in the logarithmic forms of
the `tᵢ`. -/
theorem mem_relativeLogForms_iff_mem_logForms (hD : D.IsRelativeSNC n f)
    (hcomp : ∀ ξ : V, ξ ∈ (D.supp : Set V) → Order.coheight ξ = 1 →
      ∃ E ∈ D.support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ)
    (c : WeakChart f n (D.supp : Set V)) (p : ℕ)
    (ω : Γ(((LU D).ι ≫ f).relativeDifferentialForms (p : ℤ), (LU D).ι ⁻¹ᵁ (c.W : V.Opens))) :
    ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD ⊤ p c.W ↔
      letI := MMP.Mori.sectionAlgebra f ((c.W : V.Opens) ⊓ LU D)
      letI := MMP.Mori.sectionAlgebra f c.W
      letI : Algebra Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) :=
        (V.presheaf.map (homOfLE (inf_le_left : (c.W : V.Opens) ⊓ LU D ≤ c.W)).op).hom.toAlgebra
      ((MMP.DeRham.formsAlgEquiv f p ⟨(c.W : V.Opens) ⊓ LU D,
          MMP.DeRham.isAffineOpen_of_eq_basicOpen _ (weakChart_inf_LU f D c)⟩
          (ambientFormsEquiv f (LU D) p c.W ω) : ⋀[Γ(V, (c.W : V.Opens) ⊓ LU D)]^p
            (Ω[Γ(V, (c.W : V.Opens) ⊓ LU D)⁄k])) : ExteriorAlgebra _ _) ∈
        MMP.DeRham.logForms k Γ(V, (c.W : V.Opens) ⊓ LU D)
          (fun i : Fin c.r => c.t (Fin.castLE c.hr i)) p := by
  classical
  have hWU := weakChart_inf_LU f D c
  have hA : IsAffineOpen ((c.W : V.Opens) ⊓ LU D) :=
    MMP.DeRham.isAffineOpen_of_eq_basicOpen _ hWU
  let := MMP.Mori.sectionAlgebra f c.W
  let := MMP.Mori.sectionAlgebra f ((c.W : V.Opens) ⊓ LU D)
  let : Algebra Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) :=
    (V.presheaf.map (homOfLE (inf_le_left : (c.W : V.Opens) ⊓ LU D ≤ c.W)).op).hom.toAlgebra
  have : IsScalarTower k Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) :=
    MMP.Flips.ResolutionInputs.isScalarTower_section_res f inf_le_left
  have : IsLocalization.Away (∏ i : Fin c.r, c.t (Fin.castLE c.hr i))
      Γ(V, (c.W : V.Opens) ⊓ LU D) :=
    MMP.DeRham.isLocalization_away_of_eq_basicOpen _ hWU inf_le_left
  have : Algebra.FormallyEtale Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)))
  have hOb14 := exists_basis_inf_LU_of_weakChart f D c
  obtain ⟨bL, hbL, hcoord⟩ := hOb14
  -- the poles
  let P : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb c.hr)
  have hP : ∀ j ∈ P, IsUnit (algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) (c.t j)) := by
    intro j hj
    have hOb15 := Finset.mem_map.1 hj
    obtain ⟨i, -, rfl⟩ := hOb15
    refine isUnit_of_dvd_unit (map_dvd _ ?_)
      (IsLocalization.Away.algebraMap_isUnit (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)))
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hu₁ : ∀ k' : Fin c.r, ∃ j ∈ P, c.t j = c.t (Fin.castLE c.hr k') :=
    fun k' => ⟨_, Finset.mem_map_of_mem _ (Finset.mem_univ k'), rfl⟩
  have hu₂ : ∀ j ∈ P, ∃ k' : Fin c.r, c.t (Fin.castLE c.hr k') = c.t j := by
    intro j hj
    have hOb16 := Finset.mem_map.1 hj
    obtain ⟨i, -, rfl⟩ := hOb16
    exact ⟨i, rfl⟩
  -- the logarithmic coordinate data
  have hle : (c.W : V.Opens) ≤ (c.toLogData f D).W := le_rfl
  have hres : ∀ a : Γ(V, c.W), ambientRingHom (LU D) c.W
      (((LU D).ι.app c.W).hom (V.presheaf.map (homOfLE hle).op a)) =
        algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) a := fun a => by
    simp only [ambientRingHom_app]
    exact MMP.DeRham.FrobeniusSplittingData.structureSheaf_map_map _ _ a
  have hσ : ∀ i, ambientRingHom (LU D) c.W ((c.toLogData f D).σ hle i) =
      MMP.DeRham.logScale (L := Γ(V, (c.W : V.Opens) ⊓ LU D)) P c.t i :=
    fun i => ambientRingHom_toLogData_σ f D c i
  -- the monomials
  have hmon : ∀ (s : Set.powersetCard (Fin n) p) (a : Γ(V, c.W)),
      ∃ z : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece (p : ℤ)).val.obj
          (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens))),
        (TB ((LU D).ι ≫ f)).incl (p : ℤ) z =
            smU (f := f) (D := D) _ (((LU D).ι.app c.W).hom a) *
              (((s : Finset (Fin n)).sort (· ≤ ·)).map fun i =>
                (TB ((LU D).ι ≫ f)).totalRestrict
                  ((TopologicalSpace.Opens.map (LU D).ι.base).map (homOfLE hle)).op ((c.toLogData f D).θ i)).prod ∧
          MMP.DeRham.formsAlgEquiv f p ⟨_, hA⟩ (ambientFormsEquiv f (LU D) p c.W z) =
            algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) a •
              (MMP.DeRham.logBasis bL hP).exteriorPower p s := by
    intro s a
    have hl : (((s : Finset (Fin n)).sort (· ≤ ·)).map fun i =>
        ((LU D).ι.app c.W).hom (V.presheaf.map (homOfLE hle).op (c.t i))).length = p := by
      simp only [List.length_map, Finset.length_sort]
      exact s.2
    have hOb := exists_incl_eq_and_formsAlgEquiv_eq f D c.W hA
      (((LU D).ι.app c.W).hom a * (((s : Finset (Fin n)).sort (· ≤ ·)).map ((c.toLogData f D).σ hle)).prod)
      _ p hl
    obtain ⟨z, hz, hΨ⟩ := hOb
    refine ⟨z, hz.trans ?_, hΨ.trans ?_⟩
    · show smU (f := f) (D := D) _ (_ * _) * _ = smU (f := f) (D := D) _ _ * _
      rw [map_mul, mul_assoc]
      refine congrArg (_ * ·) ?_
      rw [List.map_congr_left (fun i _ => (c.toLogData f D).totalRestrict_θ hle i), List.map_map]
      exact (prod_map_mul_of_commute (smU (f := f) (D := D) _)
        (fun r z => (TB ((LU D).ι ≫ f)).structureMap_commutes _ r z) _ _ _).symm
    · refine (congrArg (· • _)
        (map_mul (ambientRingHom (LU D) c.W) (((LU D).ι.app c.W).hom a) _)).trans ?_
      simp only [ambientRingHom_app (LU D) c.W a]
      simp only [map_list_prod (ambientRingHom (LU D) c.W), List.map_map]
      refine (mul_smul _ _ _).trans ?_
      refine congrArg (algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) a • ·) ?_
      conv_rhs => rw [MMP.DeRham.logBasis_exteriorPower_apply, exteriorPower.basis_apply,
        exteriorPower.ιMulti_family]
      refine congrArg₂ (· • ·) ?_ (congrArg (exteriorPower.ιMulti _ p) (funext fun i => ?_))
      · conv_lhs => rw [← List.ofFn_get ((s : Finset (Fin n)).sort (· ≤ ·)), List.map_ofFn,
          List.prod_ofFn]
        exact Fintype.prod_equiv (finCongr (by rw [Finset.length_sort]; exact s.2)) _ _
          fun k => hσ _
      · simp only [Function.comp_apply, List.get_eq_getElem, List.getElem_map, Fin.coe_cast]
        rw [hres, hbL]
        rfl
  -- sums of monomials
  let eK : {K : Finset (Fin n) // K.card = p} ≃ Set.powersetCard (Fin n) p :=
    Equiv.subtypeEquivRight fun K => Set.powersetCard.mem_iff.symm
  have hcomb : ∀ a : {K : Finset (Fin n) // K.card = p} → Γ(V, c.W),
      ∃ z : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece (p : ℤ)).val.obj
          (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens))),
        (TB ((LU D).ι ≫ f)).incl (p : ℤ) z = logCombo (f := f) (c.toLogData f D).W (c.toLogData f D).t (c.toLogData f D).r (c.toLogData f D).s p hle a ∧
          MMP.DeRham.formsAlgEquiv f p ⟨_, hA⟩ (ambientFormsEquiv f (LU D) p c.W z) =
            ∑ s, algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) (a (eK.symm s)) •
              (MMP.DeRham.logBasis bL hP).exteriorPower p s := by
    intro a
    choose z hz hΨz using fun K : {K : Finset (Fin n) // K.card = p} => hmon (eK K) (a K)
    refine ⟨∑ K, z K, ?_, ?_⟩
    · simp only [show (TB ((LU D).ι ≫ f)).incl (p : ℤ) (∑ K, z K) =
          ∑ K, (TB ((LU D).ι ≫ f)).incl (p : ℤ) (z K) from map_sum (DirectSum.of _ (p : ℤ)) _ _]
      exact Finset.sum_congr rfl fun K _ => hz K
    · exact ((congrArg _ (map_sum (ambientFormsEquiv f (LU D) p c.W) _ _)).trans
        (map_sum _ _ _)).trans (Fintype.sum_equiv eK _ _ fun K => by simp only [hΨz K, eK.symm_apply_apply])
  have hB := (c.hasLogBasis f D hD hcomp p hle).2.1 ω
  constructor
  · intro hω
    have hB1 := hB.1
    have h1 := hB1 hω
    obtain ⟨a, ha⟩ := h1
    have hc := hcomb a
    have hz := hc.choose_spec.1
    have hΨ := hc.choose_spec.2
    have hωz : ω = hc.choose := incl_injective (f := f) (D := D) (p : ℤ) _ (ha.trans hz.symm)
    subst hωz
    simp only [hΨ]
    exact MMP.DeRham.coe_sum_logBasis_mem_logForms hP hbL hu₂ _
  · intro hω
    have hOb17 := MMP.DeRham.exists_eq_sum_logBasis hP hbL hu₁ hcoord _ hω
    obtain ⟨cf, hcf⟩ := hOb17
    obtain ⟨z, hz, hΨ⟩ := hcomb fun K => cf (eK K)
    simp only [Equiv.apply_symm_apply] at hΨ
    have hcz := hcf.trans hΨ.symm
    have hωz : ω = z := (ambientFormsEquiv f (LU D) p c.W).injective
      ((MMP.DeRham.formsAlgEquiv f p ⟨_, hA⟩).injective hcz)
    exact hB.2 ⟨fun K => cf (eK K), hωz ▸ hz⟩

/-- Multiplication of forms on `W ∖ D` by a function on a chart `W`. -/
noncomputable abbrev chartSmul (c : WeakChart f n (D.supp : Set V)) (b : Γ(V, c.W)) {q : ℤ}
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece q).val.obj
      (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece q).val.obj
      (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens))) :=
  (show (Stacks.RingedSpace.structureRingSheaf (LU D).toScheme.toRingedSpace).obj.obj
    (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens))) from ((LU D).ι.app c.W).hom b) • ω

/-- The de Rham differential of forms on `W ∖ D`, for a chart `W`. -/
noncomputable abbrev chartD (c : WeakChart f n (D.supp : Set V)) (q : ℕ)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece (q : ℤ)).val.obj
      (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece ((q + 1 : ℕ) : ℤ)).val.obj
      (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens))) :=
  ((Scheme.Hom.deRhamComplex ((LU D).ι ≫ f)).d q (q + 1)).val.app
    (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens))) ω

/-- **Forms on the complement of the divisor in a weak chart, read in algebra.** -/
noncomputable def chartForms (c : WeakChart f n (D.supp : Set V)) (q : ℕ) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece (q : ℤ)).val.obj
      (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens))) ≃+
      (letI := MMP.Mori.sectionAlgebra f ((c.W : V.Opens) ⊓ LU D)
      ⋀[Γ(V, (c.W : V.Opens) ⊓ LU D)]^q (Ω[Γ(V, (c.W : V.Opens) ⊓ LU D)⁄k])) :=
  letI := MMP.Mori.sectionAlgebra f ((c.W : V.Opens) ⊓ LU D)
  (ambientFormsEquiv f (LU D) q c.W).trans
    (MMP.DeRham.formsAlgEquiv f q ⟨_, MMP.DeRham.isAffineOpen_of_eq_basicOpen _
      (weakChart_inf_LU f D c)⟩).toAddEquiv

/-- The comparison carries the de Rham differential to the algebraic one. -/
theorem chartForms_d (c : WeakChart f n (D.supp : Set V)) (q : ℕ)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece (q : ℤ)).val.obj
      (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))) :
    letI := MMP.Mori.sectionAlgebra f ((c.W : V.Opens) ⊓ LU D)
    chartForms f D c (q + 1) (chartD f D c q ω) =
      KaehlerDifferential.deRhamDifferential (A := k) q (chartForms f D c q ω) := by
  let := MMP.Mori.sectionAlgebra f ((c.W : V.Opens) ⊓ LU D)
  exact (congrArg (MMP.DeRham.formsAlgEquiv f (q + 1) _) (ambientFormsEquiv_d f (LU D) q c.W ω)).trans
    (MMP.DeRham.formsAlgEquiv_d f q _ _)

/-- The comparison is semilinear for the functions on the chart. -/
theorem chartForms_smul (c : WeakChart f n (D.supp : Set V)) (q : ℕ) (b : Γ(V, c.W))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece (q : ℤ)).val.obj
      (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))) :
    letI := MMP.Mori.sectionAlgebra f ((c.W : V.Opens) ⊓ LU D)
    chartForms f D c q (chartSmul f D c b ω) =
      V.presheaf.map (homOfLE (inf_le_left : (c.W : V.Opens) ⊓ LU D ≤ c.W)).op b •
        chartForms f D c q ω := by
  let := MMP.Mori.sectionAlgebra f ((c.W : V.Opens) ⊓ LU D)
  exact (congrArg (MMP.DeRham.formsAlgEquiv f q _)
    ((ambientFormsEquiv_smul f (LU D) (q : ℤ) c.W _ ω).trans
      (congrArg (· • ambientFormsEquiv f (LU D) (q : ℤ) c.W ω) (ambientRingHom_app (LU D) c.W b)))).trans
    (map_smul _ _ _)

set_option maxRecDepth 40000 in
/-- **Logarithmic forms on a weak chart, read in algebra through `chartForms`.** -/
theorem mem_relativeLogForms_iff_chartForms_mem (hD : D.IsRelativeSNC n f)
    (hcomp : ∀ ξ : V, ξ ∈ (D.supp : Set V) → Order.coheight ξ = 1 →
      ∃ E ∈ D.support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ)
    (c : WeakChart f n (D.supp : Set V)) (q : ℕ)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece (q : ℤ)).val.obj
      (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))) :
    letI := MMP.Mori.sectionAlgebra f ((c.W : V.Opens) ⊓ LU D)
    letI : Algebra Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) :=
      (V.presheaf.map (homOfLE (inf_le_left : (c.W : V.Opens) ⊓ LU D ≤ c.W)).op).hom.toAlgebra
    ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD ⊤ q c.W ↔
      ((chartForms f D c q ω : ⋀[Γ(V, (c.W : V.Opens) ⊓ LU D)]^q
          (Ω[Γ(V, (c.W : V.Opens) ⊓ LU D)⁄k])) :
        ExteriorAlgebra Γ(V, (c.W : V.Opens) ⊓ LU D) (Ω[Γ(V, (c.W : V.Opens) ⊓ LU D)⁄k])) ∈
        MMP.DeRham.logForms k Γ(V, (c.W : V.Opens) ⊓ LU D)
          (fun i : Fin c.r => c.t (Fin.castLE c.hr i)) q :=
  mem_relativeLogForms_iff_mem_logForms f D hD hcomp c q ω

/-- **The twisted logarithmic forms on a weak chart** are the multiples of the logarithmic forms
by the product `t₁ ⋯ t_r` of the boundary coordinates. -/
theorem mem_relativeLogForms_suppIdeal_iff (hD : D.IsRelativeSNC n f)
    (hcomp : ∀ ξ : V, ξ ∈ (D.supp : Set V) → Order.coheight ξ = 1 →
      ∃ E ∈ D.support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ)
    (c : WeakChart f n (D.supp : Set V)) (q : ℕ)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece (q : ℤ)).val.obj
      (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))) :
    ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD D.suppIdeal q c.W ↔
      ∃ ω₀ ∈ MMP.Mori.Divisor.relativeLogForms n f D hD ⊤ q c.W,
        ω = (show (Stacks.RingedSpace.structureRingSheaf (LU D).toScheme.toRingedSpace).obj.obj
          (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens))) from
            ((LU D).ι.app c.W).hom (∏ i : Fin c.r, c.t (Fin.castLE c.hr i))) • ω₀ := by
  have hle : (c.W : V.Opens) ≤ (c.toLogData f D).W := le_rfl
  have hB := c.hasLogBasis f D hD hcomp q hle
  have hH : logH (c.toLogData f D).W (c.toLogData f D).t (c.toLogData f D).hr hle =
      ∏ i : Fin c.r, c.t (Fin.castLE c.hr i) := by
    unfold logH
    rw [show (homOfLE hle).op = 𝟙 (op ((c.toLogData f D).W : V.Opens)) from rfl]
    erw [CategoryTheory.Functor.map_id]
    rfl
  have key : ∀ a ω₀, (TB ((LU D).ι ≫ f)).incl (q : ℤ) ω₀ = (c.toLogData f D).combo q hle a →
      (TB ((LU D).ι ≫ f)).incl (q : ℤ)
        ((show (Stacks.RingedSpace.structureRingSheaf (LU D).toScheme.toRingedSpace).obj.obj
          (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens))) from
            ((LU D).ι.app c.W).hom (∏ i : Fin c.r, c.t (Fin.castLE c.hr i))) • ω₀) =
        (c.toLogData f D).combo q hle
          (logH (c.toLogData f D).W (c.toLogData f D).t (c.toLogData f D).hr hle • a) := by
    intro a ω₀ h
    rw [incl_smul_eq, h, LogData.combo_smul, hH]
    rfl
  constructor
  · intro hω
    obtain ⟨a, ha⟩ := (hB.2.2.2 ω).1 hω
    obtain ⟨ω₀, h₀⟩ := (c.toLogData f D).exists_incl_eq_combo q hle a
    exact ⟨ω₀, (hB.2.1 ω₀).2 ⟨a, h₀⟩,
      incl_injective (f := f) (D := D) (q : ℤ) _ (ha.trans (key a ω₀ h₀).symm)⟩
  · rintro ⟨ω₀, h₀, rfl⟩
    obtain ⟨a, ha⟩ := (hB.2.1 ω₀).1 h₀
    exact (hB.2.2.2 _).2 ⟨a, key a ω₀ ha⟩

theorem chartD_chartD (c : WeakChart f n (D.supp : Set V)) (q : ℕ)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece (q : ℤ)).val.obj
      (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))) :
    chartD f D c (q + 1) (chartD f D c q ω) = 0 := by
  have h := congrArg (fun φ => (φ.val.app (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))).hom ω)
    ((Scheme.Hom.deRhamComplex ((LU D).ι ≫ f)).d_comp_d q (q + 1) (q + 1 + 1))
  exact h

/-- In characteristic `p`, the de Rham differential commutes with multiplication by the `p`-th
power of the product of the boundary coordinates of a weak chart. -/
theorem chartD_chartSmul_prod_pow (p : ℕ) [Fact p.Prime] (hV : IsInCharacteristic V p)
    (c : WeakChart f n (D.supp : Set V)) (q : ℕ) (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece
      (q : ℤ)).val.obj (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))) :
    chartD f D c q (chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p) ω) =
      chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p) (chartD f D c q ω) := by
  let := MMP.Mori.sectionAlgebra f ((c.W : V.Opens) ⊓ LU D)
  let : Algebra Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) :=
    (V.presheaf.map (homOfLE (inf_le_left : (c.W : V.Opens) ⊓ LU D ≤ c.W)).op).hom.toAlgebra
  have hpL : (p : Γ(V, (c.W : V.Opens) ⊓ LU D)) = 0 := cast_eq_zero_of_isInCharacteristic hV _
  have hsm : ∀ (q : ℕ) (b : Γ(V, c.W)) (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((LU D).ι ≫ f)).piece (q : ℤ)).val.obj (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))),
      chartForms f D c q (chartSmul f D c b ω) =
        algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) b • chartForms f D c q ω :=
    fun q b ω => chartForms_smul f D c q b ω
  have hd : ∀ (q : ℕ) (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((LU D).ι ≫ f)).piece (q : ℤ)).val.obj (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))),
      chartForms f D c (q + 1) (chartD f D c q ω) =
        KaehlerDifferential.deRhamDifferential (A := k) q (chartForms f D c q ω) :=
    fun q ω => chartForms_d f D c q ω
  apply (chartForms f D c (q + 1)).injective
  rw [hd, hsm, hsm, hd, map_pow]
  exact deRhamDifferential_pow_smul_of_natCast_eq_zero p hpL q _ _

/-- Multiplication by a power of the product of the boundary coordinates of a weak chart is
injective on forms off the divisor. -/
theorem eq_zero_of_chartSmul_prod_pow_eq_zero (p : ℕ) (c : WeakChart f n (D.supp : Set V))
    (q : ℕ) (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece
      (q : ℤ)).val.obj (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))) (hω : chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p) ω = 0) : ω = 0 := by
  have hWU := weakChart_inf_LU f D c
  let := MMP.Mori.sectionAlgebra f ((c.W : V.Opens) ⊓ LU D)
  let : Algebra Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) :=
    (V.presheaf.map (homOfLE (inf_le_left : (c.W : V.Opens) ⊓ LU D ≤ c.W)).op).hom.toAlgebra
  have : IsLocalization.Away (∏ i : Fin c.r, c.t (Fin.castLE c.hr i))
      Γ(V, (c.W : V.Opens) ⊓ LU D) :=
    MMP.DeRham.isLocalization_away_of_eq_basicOpen _ hWU inf_le_left
  have hunit : IsUnit (algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) (∏ i : Fin c.r, c.t (Fin.castLE c.hr i))) :=
    IsLocalization.Away.algebraMap_isUnit (∏ i : Fin c.r, c.t (Fin.castLE c.hr i))
  have hunitp : IsUnit (algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p)) := by
    rw [map_pow]; exact hunit.pow p
  have hsm : ∀ (q : ℕ) (b : Γ(V, c.W)) (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((LU D).ι ≫ f)).piece (q : ℤ)).val.obj (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))),
      chartForms f D c q (chartSmul f D c b ω) =
        algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) b • chartForms f D c q ω :=
    fun q b ω => chartForms_smul f D c q b ω
  apply (chartForms f D c q).injective
  have := congrArg (chartForms f D c q) hω
  rw [hsm, map_zero] at this
  rw [map_zero]
  exact (hunitp.smul_left_cancel).1 (this.trans (smul_zero _).symm)

set_option maxRecDepth 40000 in
/-- **The twisted logarithmic de Rham complexes on a weak chart.** Write `h = t₁ ⋯ t_r` for the
product of the boundary coordinates of a weak chart `W`, `Ω^q(log D)` and `Ω^q(log D)(-D)` for
the logarithmic and twisted logarithmic forms over `W`. In characteristic `p`:
(1) a closed function in `Ω⁰(log D)(-D)` is `h^p` times a closed logarithmic function;
(2) a closed form in `Ω^{q+1}(log D)(-D)` is `h^p ω + dy` for a closed logarithmic `ω` and
`y ∈ Ω^q(log D)(-D)`;
(3) if `dy = h^p ω` with `y ∈ Ω^q(log D)(-D)` and `ω` logarithmic, then `ω = dη` for a
logarithmic `η`;
(4) multiplication by `h^p` is injective and commutes with `d`. -/
theorem twistedLogForms_chart (hD : D.IsRelativeSNC n f)
    (hcomp : ∀ ξ : V, ξ ∈ (D.supp : Set V) → Order.coheight ξ = 1 →
      ∃ E ∈ D.support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ)
    (p : ℕ) [Fact p.Prime] (hV : IsInCharacteristic V p)
    (c : WeakChart f n (D.supp : Set V)) :
    (∀ z : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece ((0 : ℕ) : ℤ)).val.obj
        (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens))),
      z ∈ MMP.Mori.Divisor.relativeLogForms n f D hD D.suppIdeal 0 c.W →
      chartD f D c 0 z = 0 →
      ∃ ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD ⊤ 0 c.W,
        z = chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p) ω ∧
        chartD f D c 0 ω = 0) ∧
    (∀ (q : ℕ) (z : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece
        ((q + 1 : ℕ) : ℤ)).val.obj (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))),
      z ∈ MMP.Mori.Divisor.relativeLogForms n f D hD D.suppIdeal ((q + 1 : ℕ) : ℤ) c.W →
      chartD f D c (q + 1) z = 0 →
      ∃ y ∈ MMP.Mori.Divisor.relativeLogForms n f D hD D.suppIdeal q c.W,
      ∃ ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD ⊤ ((q + 1 : ℕ) : ℤ) c.W,
        z = chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p) ω +
          chartD f D c q y ∧
        chartD f D c (q + 1) ω = 0) ∧
    (∀ (q : ℕ) (y : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece
        (q : ℤ)).val.obj (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens))))
      (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece
        ((q + 1 : ℕ) : ℤ)).val.obj (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))),
      y ∈ MMP.Mori.Divisor.relativeLogForms n f D hD D.suppIdeal q c.W →
      ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD ⊤ ((q + 1 : ℕ) : ℤ) c.W →
      chartD f D c q y =
        chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p) ω →
      ∃ η ∈ MMP.Mori.Divisor.relativeLogForms n f D hD ⊤ q c.W,
        chartD f D c q η = ω) ∧
    (∀ (q : ℕ) (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece
        (q : ℤ)).val.obj (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))),
      chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p) ω = 0 → ω = 0) ∧
    (∀ (q : ℕ) (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece
        (q : ℤ)).val.obj (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))),
      chartD f D c q
          (chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p) ω) =
        chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p)
          (chartD f D c q ω)) := by
  classical
  have hWU := weakChart_inf_LU f D c
  let := MMP.Mori.sectionAlgebra f ((c.W : V.Opens) ⊓ LU D)
  let : Algebra Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) :=
    (V.presheaf.map (homOfLE (inf_le_left : (c.W : V.Opens) ⊓ LU D ≤ c.W)).op).hom.toAlgebra
  have : IsLocalization.Away (∏ i : Fin c.r, c.t (Fin.castLE c.hr i))
      Γ(V, (c.W : V.Opens) ⊓ LU D) :=
    MMP.DeRham.isLocalization_away_of_eq_basicOpen _ hWU inf_le_left
  obtain ⟨bL, hb, hcoord⟩ := exists_basis_inf_LU_of_weakChart f D c
  let P : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb c.hr)
  let u : Fin c.r → Γ(V, c.W) := fun i => c.t (Fin.castLE c.hr i)
  have hP : ∀ j ∈ P, IsUnit (algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) (c.t j)) := by
    intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    refine isUnit_of_dvd_unit (map_dvd _ ?_) (IsLocalization.Away.algebraMap_isUnit (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)))
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hu₁ : ∀ k' : Fin c.r, ∃ j ∈ P, c.t j = u k' :=
    fun k' => ⟨_, Finset.mem_map_of_mem _ (Finset.mem_univ k'), rfl⟩
  have hu₂ : ∀ j ∈ P, ∃ k' : Fin c.r, u k' = c.t j := by
    intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    exact ⟨i, rfl⟩
  have hPh : ∏ j ∈ P, c.t j = (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) := by
    simp only [P, Finset.prod_map, Fin.castLEEmb_apply]
  have hpL : (p : Γ(V, (c.W : V.Opens) ⊓ LU D)) = 0 := cast_eq_zero_of_isInCharacteristic hV _
  -- the comparison with algebra
  have hsm : ∀ (q : ℕ) (b : Γ(V, c.W)) (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((LU D).ι ≫ f)).piece (q : ℤ)).val.obj (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))),
      chartForms f D c q (chartSmul f D c b ω) = algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) b • chartForms f D c q ω :=
    fun q b ω => chartForms_smul f D c q b ω
  have hd : ∀ (q : ℕ) (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((LU D).ι ≫ f)).piece (q : ℤ)).val.obj (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))),
      chartForms f D c (q + 1) (chartD f D c q ω) =
        KaehlerDifferential.deRhamDifferential (A := k) q (chartForms f D c q ω) :=
    fun q ω => chartForms_d f D c q ω
  have hlog := fun (q : ℕ) ω => mem_relativeLogForms_iff_chartForms_mem f D hD hcomp c q ω
  have htw : ∀ (q : ℕ) (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((LU D).ι ≫ f)).piece (q : ℤ)).val.obj (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))),
      ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD D.suppIdeal q c.W ↔
        IsTwistedLogForm k Γ(V, (c.W : V.Opens) ⊓ LU D) c.t P u 1 q (chartForms f D c q ω) := by
    intro q ω
    simp only [mem_relativeLogForms_suppIdeal_iff f D hD hcomp c q ω]
    constructor
    · rintro ⟨ω₀, h₀, rfl⟩
      exact ⟨_, (hlog q ω₀).1 h₀, by simp only [pow_one, hPh]; exact hsm q (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ω₀⟩
    · rintro ⟨y₀, hy₀, hω⟩
      refine ⟨(chartForms f D c q).symm y₀, (hlog q _).2 (by rwa [AddEquiv.apply_symm_apply]),
        (chartForms f D c q).injective ?_⟩
      simp only [hω, pow_one, hPh]
      exact (congrArg (algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ LU D) (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) • ·) ((chartForms f D c q).apply_symm_apply y₀)).symm.trans
        (hsm q (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) _).symm
  have hdpow := fun (q : ℕ) ω => chartD_chartSmul_prod_pow f D p hV c q ω
  have hcancel := fun (q : ℕ) ω => eq_zero_of_chartSmul_prod_pow_eq_zero f D p c q ω
  -- reading twisted logarithmic forms by `(∏ i : Fin c.r, c.t (Fin.castLE c.hr i))^p` back
  have hpow : ∀ (q : ℕ) (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((LU D).ι ≫ f)).piece (q : ℤ)).val.obj (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))),
      IsTwistedLogForm k Γ(V, (c.W : V.Opens) ⊓ LU D) c.t P u p q (chartForms f D c q ω) →
      ∃ ω₀ ∈ MMP.Mori.Divisor.relativeLogForms n f D hD ⊤ q c.W, ω = chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p) ω₀ := by
    rintro q ω ⟨y₀, hy₀, hω⟩
    refine ⟨(chartForms f D c q).symm y₀, (hlog q _).2 (by rwa [AddEquiv.apply_symm_apply]),
      (chartForms f D c q).injective ?_⟩
    simp only [hω, hsm, AddEquiv.apply_symm_apply, hPh, map_pow]
  refine ⟨fun z hz hdz => ?_, fun q z hz hdz => ?_, fun q y ω hy hω hdy => ?_, hcancel, hdpow⟩
  · have h1 := IsTwistedLogForm.pow_of_closed_zero hb hP hcoord hu₁ hu₂ p hpL ((htw 0 z).1 hz)
      (by simp only [← hd, hdz, map_zero])
    obtain ⟨ω, hω, rfl⟩ := hpow 0 z h1
    refine ⟨ω, hω, rfl, hcancel 1 _ ?_⟩
    simpa only [← hdpow] using hdz
  · obtain ⟨y', hy', hzy⟩ := IsTwistedLogForm.exists_sub_deRhamDifferential hb hP hcoord hu₁ hu₂ p
      hpL ((htw (q + 1) z).1 hz) (by simp only [← hd, hdz, map_zero])
    obtain ⟨y, hyy⟩ : ∃ y, chartForms f D c q y = y' := ⟨_, (chartForms f D c q).apply_symm_apply y'⟩
    have hz' : IsTwistedLogForm k Γ(V, (c.W : V.Opens) ⊓ LU D) c.t P u p (q + 1) (chartForms f D c (q + 1)
        (z - chartD f D c q y)) := by
      simpa only [map_sub, hd, hyy] using hzy
    obtain ⟨ω, hω, hωe⟩ := hpow (q + 1) _ hz'
    refine ⟨y, (htw q y).2 (by simpa only [hyy] using hy'), ω, hω, by simp only [← hωe, sub_add_cancel], ?_⟩
    refine hcancel (q + 1 + 1) _ ?_
    have hsub : chartD f D c (q + 1) (z - chartD f D c q y) =
        chartD f D c (q + 1) z - chartD f D c (q + 1) (chartD f D c q y) := map_sub _ _ _
    simp only [← hdpow, ← hωe, hsub, hdz, chartD_chartD, sub_zero]
  · have h1 : IsTwistedLogForm k Γ(V, (c.W : V.Opens) ⊓ LU D) c.t P u p (q + 1)
        (KaehlerDifferential.deRhamDifferential (A := k) q (chartForms f D c q y)) := by
      simp only [← hd, hdy, hsm]
      refine ⟨_, (hlog (q + 1) ω).1 hω, ?_⟩
      simp only [hPh, map_pow]
    obtain ⟨y'', hy'', hdy''⟩ := IsTwistedLogForm.exists_deRhamDifferential_eq hb hP hcoord hu₁
      hu₂ p hpL ((htw q y).1 hy) h1
    obtain ⟨η, hη, hηe⟩ := hpow q ((chartForms f D c q).symm y'')
      (by rwa [AddEquiv.apply_symm_apply])
    refine ⟨η, hη, ?_⟩
    have e1 : y'' = chartForms f D c q (chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p) η) := by
      simp only [← hηe, AddEquiv.apply_symm_apply]
    have e2 : chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p) (chartD f D c q η) = chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p) ω := by
      apply (chartForms f D c (q + 1)).injective
      simp only [← hdpow, hd, ← e1, hdy'', ← hd, hdy]
    have e3 := hcancel (q + 1) (chartD f D c q η - ω) (by
      simp only [show chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p)
          (chartD f D c q η - ω) = chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p)
            (chartD f D c q η) - chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p) ω
          from smul_sub _ _ _, e2, sub_self])
    exact sub_eq_zero.1 e3

end LogBridge

/-! ### The logarithmic forms of a simple normal crossing family -/

section LogEmbedding

open MMP.Mori.Divisor.LogSpreadingProof.G1 KaehlerDifferential

variable {k : Type} [Field k] [IsRegularRing (CommRingCat.of k)] {V : Scheme.{0}}
  (f : V ⟶ Spec (CommRingCat.of k)) {n : ℕ} [SmoothOfRelativeDimension n f]
  (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n f) {ι : Type} [Fintype ι]
  (J : ι → V.IdealSheafData)
  (hJ : ∀ T : Finset ι,
    SmoothOfRelativeDimension (n - T.card) ((⨆ j ∈ T, J j).subschemeι ≫ f) ∧
    (n < T.card → IsEmpty (⨆ j ∈ T, J j).subscheme))
  (hU : LU D = ((⨅ j, J j).support).compl)

include hJ hU in
/-- Weak charts of the divisor adapted to the family `J`, inside any open. -/
theorem exists_weakChart_of_snc' {O : V.Opens} {y : V} (hy : y ∈ O) :
    ∃ (c : WeakChart f n (D.supp : Set V)) (t : ι → Γ(V, c.W)),
      (c.W : V.Opens) ≤ O ∧ y ∈ (c.W : V.Opens) ∧
      (∀ j, (J j).ideal c.W = Ideal.span {t j}) ∧
      (∀ j, IsUnit (t j) ∨ ∃ i : Fin c.r, c.t (Fin.castLE c.hr i) = t j) ∧
      (∀ i : Fin c.r, ∃ j, t j = c.t (Fin.castLE c.hr i)) ∧
      IsSMulRegular Γ(V, c.W) (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) := by
  have hZ : (((⨅ j, J j).support : TopologicalSpace.Closeds V) : Set V) = (D.supp : Set V) := by
    ext x
    have := SetLike.ext_iff.1 hU x
    exact not_iff_not.1 this.symm
  obtain ⟨c, t, h1, h2, h3, eB, -, heB, hunit, h6⟩ := exists_weakChart_of_snc f J hJ hy
  refine ⟨c.ofEq hZ, t, h1, h2, h3, fun j => ?_, fun i => ⟨eB i, heB i⟩, h6⟩
  by_cases hj : j ∈ Set.range eB
  · obtain ⟨i, rfl⟩ := hj
    exact Or.inr ⟨i, (heB i).symm⟩
  · exact Or.inl (hunit j hj)

include hJ hU in
/-- **Forms without poles are determined off the divisor.** -/
theorem forms_map_inf_injective (q : ℕ) (O : V.Opens) :
    Function.Injective ((f.relativeDifferentialForms (q : ℤ)).presheaf.map
      (homOfLE (inf_le_left : O ⊓ LU D ≤ O)).op) := by
  intro a b hab
  choose c t hcO hyc _h1 _h2 _h3 hreg using fun y : O => exists_weakChart_of_snc' f D J hJ hU y.2
  refine modules_eq_of_cover _ (fun y : O => ((c y).W : V.Opens)) hcO
    (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hyc _⟩) fun y => ?_
  obtain ⟨b₀, -⟩ := (c y).basis
  refine forms_map_injective_of_eq_basicOpen f q (c y).W _ (weakChart_inf_LU f D (c y))
    inf_le_left (hreg y) ⟨b₀.map (MMP.DeRham.kaehlerSpecEquiv f (c y).W)⟩ ?_
  have hk : ((c y).W : V.Opens) ⊓ LU D ≤ O := inf_le_left.trans (hcO y)
  have hk' : ((c y).W : V.Opens) ⊓ LU D ≤ O ⊓ LU D := inf_le_inf_right _ (hcO y)
  calc _ = (f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hk).op a :=
        modules_map_map_apply _ _ _ _ _
    _ = (f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hk').op
        ((f.relativeDifferentialForms (q : ℤ)).presheaf.map
          (homOfLE (inf_le_left : O ⊓ LU D ≤ O)).op a) := (modules_map_map_apply _ _ _ _ _).symm
    _ = (f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hk').op
        ((f.relativeDifferentialForms (q : ℤ)).presheaf.map
          (homOfLE (inf_le_left : O ⊓ LU D ≤ O)).op b) := by rw [hab]
    _ = (f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hk).op b :=
        modules_map_map_apply _ _ _ _ _
    _ = _ := (modules_map_map_apply _ _ _ _ _).symm

include hJ hU in
/-- **Extensions over the divisor glue.** A form on `W' ∖ D` that extends over the members of
an open cover of `W'` extends over `W'`. -/
theorem exists_map_eq_of_local (q : ℕ) (W' : V.Opens)
    (θ : Γ(f.relativeDifferentialForms (q : ℤ), W' ⊓ LU D))
    (hloc : ∀ y ∈ W', ∃ (O : V.Opens) (hO : O ≤ W'), y ∈ O ∧
      ∃ η : Γ(f.relativeDifferentialForms (q : ℤ), O),
        (f.relativeDifferentialForms (q : ℤ)).presheaf.map
            (homOfLE (inf_le_left : O ⊓ LU D ≤ O)).op η =
          (f.relativeDifferentialForms (q : ℤ)).presheaf.map
            (homOfLE (inf_le_inf_right (LU D) hO)).op θ) :
    ∃ η : Γ(f.relativeDifferentialForms (q : ℤ), W'),
      (f.relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE (inf_le_left : W' ⊓ LU D ≤ W')).op η = θ := by
  choose O hO hyO η hη using hloc
  obtain ⟨g, hg⟩ := modules_exists_glue (f.relativeDifferentialForms (q : ℤ)) (fun y : W' => O y y.2) (fun y => hO _ _)
    (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hyO _ _⟩)
    (fun y => η y y.2) fun y z => by
      apply forms_map_inf_injective f D J hJ hU q
      have h1 : (O y y.2 ⊓ O z z.2) ⊓ LU D ≤ O y y.2 ⊓ LU D :=
        inf_le_inf_right _ inf_le_left
      have h2 : (O y y.2 ⊓ O z z.2) ⊓ LU D ≤ O z z.2 ⊓ LU D :=
        inf_le_inf_right _ inf_le_right
      have e1 := modules_map_map_eq_map_map (f.relativeDifferentialForms (q : ℤ))
        (homOfLE (inf_le_left : O y y.2 ⊓ O z z.2 ≤ O y y.2)).op
        (homOfLE (inf_le_left : (O y y.2 ⊓ O z z.2) ⊓ LU D ≤ O y y.2 ⊓ O z z.2)).op
        (homOfLE (inf_le_left : O y y.2 ⊓ LU D ≤ O y y.2)).op (homOfLE h1).op (η y y.2)
      have e2 := modules_map_map_eq_map_map (f.relativeDifferentialForms (q : ℤ))
        (homOfLE (inf_le_right : O y y.2 ⊓ O z z.2 ≤ O z z.2)).op
        (homOfLE (inf_le_left : (O y y.2 ⊓ O z z.2) ⊓ LU D ≤ O y y.2 ⊓ O z z.2)).op
        (homOfLE (inf_le_left : O z z.2 ⊓ LU D ≤ O z z.2)).op (homOfLE h2).op (η z z.2)
      rw [hη] at e1
      rw [hη] at e2
      exact e1.trans ((modules_map_map_eq_map_map (f.relativeDifferentialForms (q : ℤ)) _ _ _ _
        θ).trans e2.symm)
  refine ⟨g, modules_eq_of_cover (f.relativeDifferentialForms (q : ℤ)) (fun y : W' => O y y.2 ⊓ LU D)
    (fun y => inf_le_inf_right _ (hO _ _))
    (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx.1⟩, hyO _ _, hx.2⟩) fun y => ?_⟩
  have e3 := modules_map_map_eq_map_map (f.relativeDifferentialForms (q : ℤ))
    (homOfLE (inf_le_left : W' ⊓ LU D ≤ W')).op
    (homOfLE (inf_le_inf_right (LU D) (hO y y.2))).op
    (homOfLE (hO y y.2)).op (homOfLE (inf_le_left : O y y.2 ⊓ LU D ≤ O y y.2)).op g
  rw [hg y, hη] at e3
  exact e3

set_option maxRecDepth 20000 in
include hJ hU in
/-- **Logarithmic forms extend over the divisor after multiplication by the equations of the
family, locally.** -/
theorem exists_extensions_local_of_logForm (hcomp : ∀ ξ : V, ξ ∈ (D.supp : Set V) → Order.coheight ξ = 1 →
      ∃ E ∈ D.support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ) (q : ℕ) (W : V.Opens)
    (x : Γ(G1.logModule n f D hD ⊤ q, W)) (W' : V.affineOpens) (hW' : (W' : V.Opens) ≤ W)
    (c : ι → Γ(V, W')) (hc : ∀ j, c j ∈ (J j).ideal W') {y : V} (hy : y ∈ (W' : V.Opens)) :
    ∃ (O : V.Opens) (hO : O ≤ W'), y ∈ O ∧
      (∃ η : Γ(f.relativeDifferentialForms (q : ℤ), O),
          (f.relativeDifferentialForms (q : ℤ)).presheaf.map
              (homOfLE (inf_le_left : O ⊓ LU D ≤ O)).op η =
            (f.relativeDifferentialForms (q : ℤ)).presheaf.map
              (homOfLE (inf_le_inf_right (LU D) hO)).op
              (V.presheaf.map (homOfLE (inf_le_left : (W' : V.Opens) ⊓ LU D ≤ W')).op (∏ j, c j) •
                (f.relativeDifferentialForms (q : ℤ)).presheaf.map
                  (homOfLE (inf_le_inf_right (LU D) hW')).op (ambientFormsEquiv f (LU D) q W x.1))) ∧
        (∃ η : Γ(f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ), O),
          (f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map
              (homOfLE (inf_le_left : O ⊓ LU D ≤ O)).op η =
            (f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map
              (homOfLE (inf_le_inf_right (LU D) hO)).op
              (V.presheaf.map (homOfLE (inf_le_left : (W' : V.Opens) ⊓ LU D ≤ W')).op (∏ j, c j) •
                (f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map
                  (homOfLE (inf_le_inf_right (LU D) hW')).op
                  (((f.deRhamComplex).d q (q + 1)).val.app (op (W ⊓ LU D)) (ambientFormsEquiv f (LU D) q W x.1)))) := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨cy, ty, hcW', hyc, hid, -, hbd, -⟩ := exists_weakChart_of_snc' f D J hJ hU hy
  have hcW : (cy.W : V.Opens) ≤ W := hcW'.trans hW'
  have hlog := (mem_relativeLogForms_iff_mem_logForms f D hD hcomp cy q
    ((G1.logModule n f D hD ⊤ q).presheaf.map (homOfLE hcW).op x).1).1
    ((G1.logModule n f D hD ⊤ q).presheaf.map (homOfLE hcW).op x).2
  letI := MMP.Mori.sectionAlgebra f ((cy.W : V.Opens) ⊓ LU D)
  letI := MMP.Mori.sectionAlgebra f cy.W
  letI : Algebra Γ(V, cy.W) Γ(V, (cy.W : V.Opens) ⊓ LU D) :=
    (V.presheaf.map (homOfLE (inf_le_left : (cy.W : V.Opens) ⊓ LU D ≤ cy.W)).op).hom.toAlgebra
  have hlog' := MMP.DeRham.logForms_le_logForms (Bf := Γ(V, cy.W)) _ ty
    (fun i => Or.inr (hbd i)) hlog
  have hWU := MMP.DeRham.inf_eq_basicOpen_prod_of_ideal_eq_span J (LU D) hU cy.W ty hid
  have hS := MMP.DeRham.linearIndependent_of_ideal_eq_span f J hJ cy.W ty hid
  have he : ambientFormsEquiv f (LU D) q cy.W
      ((G1.logModule n f D hD ⊤ q).presheaf.map (homOfLE hcW).op x).1 =
      (f.relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE (inf_le_inf_right _ hcW)).op (ambientFormsEquiv f (LU D) q W x.1) :=
    ambientFormsEquiv_map f (LU D) q hcW x.1
  have hext := (MMP.DeRham.forall_exists_extension_iff_mem_logForms f cy.W J
    ty hid (LU D) hWU hS q (ambientFormsEquiv f (LU D) q cy.W
      ((G1.logModule n f D hD ⊤ q).presheaf.map (homOfLE hcW).op x).1)).2 hlog' cy.W le_rfl
    (fun j => V.presheaf.map (homOfLE hcW').op (c j))
    (fun j => (J j).map_ideal (show cy.W ≤ W' from hcW') ▸ Ideal.mem_map_of_mem _ (hc j))
  obtain ⟨⟨η₁, h₁⟩, ⟨η₂, h₂⟩⟩ := hext
  have hprod : V.presheaf.map (homOfLE (inf_le_left : (cy.W : V.Opens) ⊓ LU D ≤ cy.W)).op
      (∏ j, V.presheaf.map (homOfLE hcW').op (c j)) =
      V.presheaf.map (homOfLE (inf_le_inf_right (LU D) hcW')).op
        (V.presheaf.map (homOfLE (inf_le_left : (W' : V.Opens) ⊓ LU D ≤ W')).op
          (∏ j, c j)) := by
    simp only [← map_prod]
    exact (presheaf_map_comp_apply' _ _ (homOfLE (inf_le_left.trans hcW')).op _).trans
      (presheaf_map_comp_apply' _ _ (homOfLE (inf_le_left.trans hcW')).op _).symm
  refine ⟨cy.W, hcW', hyc, ⟨η₁, h₁.trans ?_⟩, ⟨η₂, h₂.trans ?_⟩⟩
  · beta_reduce
    simp only [Scheme.Modules.map_smul, he, hprod]
    congr 1
    exact (modules_map_map_apply _ _ _ (homOfLE (inf_le_inf_right (LU D) hcW)).op _).trans
      (modules_map_map_apply _ _ _ (homOfLE (inf_le_inf_right (LU D) hcW)).op _).symm
  · beta_reduce
    simp only [Scheme.Modules.map_smul, he, hprod]
    congr 1
    exact (congrArg ((f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map _)
      (PresheafOfModules.naturality_apply ((f.deRhamComplex).d q (q + 1)).val _ _)).trans
      ((modules_map_map_apply _ _ _ (homOfLE (inf_le_inf_right (LU D) hcW)).op _).trans
      (modules_map_map_apply _ _ _ (homOfLE (inf_le_inf_right (LU D) hcW)).op _).symm)

set_option maxRecDepth 20000 in
include hJ hU in
/-- **Deligne's criterion, locally.** A form off the divisor which extends over the divisor after
multiplication by the equations of the family is, near every point, a logarithmic form. -/
theorem exists_rs_mem_relativeLogForms_of_extensions (hcomp : ∀ ξ : V, ξ ∈ (D.supp : Set V) → Order.coheight ξ = 1 →
      ∃ E ∈ D.support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ) (q : ℕ) (W : V.Opens)
    (ω : Γ(f.relativeDifferentialForms (q : ℤ), W ⊓ LU D))
    (hdel : ∀ (W' : V.affineOpens) (hW' : (W' : V.Opens) ≤ W) (c : ι → Γ(V, W')),
        (∀ j, c j ∈ (J j).ideal W') →
        (∃ η : Γ(f.relativeDifferentialForms (q : ℤ), W'),
          (f.relativeDifferentialForms (q : ℤ)).presheaf.map
              (homOfLE (inf_le_left : (W' : V.Opens) ⊓ LU D ≤ W')).op η =
            V.presheaf.map (homOfLE (inf_le_left : (W' : V.Opens) ⊓ LU D ≤ W')).op
                (∏ j, c j) •
              (f.relativeDifferentialForms (q : ℤ)).presheaf.map
                (homOfLE (inf_le_inf_right (LU D) hW')).op ω) ∧
        (∃ η : Γ(f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ), W'),
          (f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map
              (homOfLE (inf_le_left : (W' : V.Opens) ⊓ LU D ≤ W')).op η =
            V.presheaf.map (homOfLE (inf_le_left : (W' : V.Opens) ⊓ LU D ≤ W')).op
                (∏ j, c j) •
              (f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map
                (homOfLE (inf_le_inf_right (LU D) hW')).op
                  (((f.deRhamComplex).d q (q + 1)).val.app (op (W ⊓ LU D)) ω)))
    {y : V} (hy : y ∈ W) :
    ∃ (O : V.Opens) (h : O ≤ W), y ∈ O ∧
      rs f D q h ((ambientFormsEquiv f (LU D) q W).symm ω) ∈
        MMP.Mori.Divisor.relativeLogForms n f D hD ⊤ q O := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨cy, ty, hcW, hyc, hid, hun, -, -⟩ := exists_weakChart_of_snc' f D J hJ hU hy
  refine ⟨cy.W, hcW, hyc, ?_⟩
  refine (mem_relativeLogForms_iff_mem_logForms f D hD hcomp cy q _).2 ?_
  have hamb : ambientFormsEquiv f (LU D) q cy.W
      (rs f D q hcW ((ambientFormsEquiv f (LU D) q W).symm ω)) =
      (f.relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE (inf_le_inf_right (LU D) hcW)).op ω :=
    (ambientFormsEquiv_map f (LU D) q hcW _).trans (by simp only [AddEquiv.apply_symm_apply])
  simp only [hamb]
  have hWU := MMP.DeRham.inf_eq_basicOpen_prod_of_ideal_eq_span J (LU D) hU cy.W ty hid
  have hS := MMP.DeRham.linearIndependent_of_ideal_eq_span f J hJ cy.W ty hid
  letI := MMP.Mori.sectionAlgebra f ((cy.W : V.Opens) ⊓ LU D)
  letI := MMP.Mori.sectionAlgebra f cy.W
  letI : Algebra Γ(V, cy.W) Γ(V, (cy.W : V.Opens) ⊓ LU D) :=
    (V.presheaf.map (homOfLE (inf_le_left : (cy.W : V.Opens) ⊓ LU D ≤ cy.W)).op).hom.toAlgebra
  refine MMP.DeRham.logForms_le_logForms (Bf := Γ(V, cy.W)) ty _ hun
    ((MMP.DeRham.forall_exists_extension_iff_mem_logForms f cy.W J ty hid (LU D) hWU hS q
      _).1 fun W'' hW'' c' hc' => ?_)
  have hd := hdel W'' (hW''.trans hcW) c' hc'
  obtain ⟨⟨η₁, h₁⟩, ⟨η₂, h₂⟩⟩ := hd
  refine ⟨⟨η₁, h₁.trans ?_⟩, ⟨η₂, h₂.trans ?_⟩⟩
  · congr 1
    exact (modules_map_map_apply (f.relativeDifferentialForms (q : ℤ))
      (homOfLE (inf_le_inf_right (LU D) hcW)).op (homOfLE (inf_le_inf_right (LU D) hW'')).op _
      ω).symm
  · congr 1
    exact (modules_map_map_apply (f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ))
        (homOfLE (inf_le_inf_right (LU D) hcW)).op
        (homOfLE (inf_le_inf_right (LU D) hW'')).op _ _).symm.trans
      (congrArg ((f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map
          (homOfLE (inf_le_inf_right (LU D) hW'')).op)
        (PresheafOfModules.naturality_apply ((f.deRhamComplex).d q (q + 1)).val
          (homOfLE (inf_le_inf_right (LU D) hcW)).op ω).symm)

include hJ hU in
/-- **The logarithmic forms of a relative snc divisor, embedded in the forms off the divisor.**
Reading a logarithmic form on `W` as a form on `W ∖ D` is injective, linear and natural, and its
image is cut out by Deligne's criterion for the family `J` cutting out the divisor. -/
theorem exists_logForms_embedding
    (hcomp : ∀ ξ : V, ξ ∈ (D.supp : Set V) → Order.coheight ξ = 1 →
      ∃ E ∈ D.support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ) :
    ∃ e : ∀ (q : ℕ) (W : V.Opens), Γ(G1.logModule n f D hD ⊤ q, W) →+
        Γ(f.relativeDifferentialForms (q : ℤ), W ⊓ LU D),
      (∀ q W x, e q W x = ambientFormsEquiv f (LU D) q W x.1) ∧
      (∀ (q : ℕ) W, Function.Injective (e q W)) ∧
      (∀ (q : ℕ) W (a : Γ(V, W)) (x : Γ(G1.logModule n f D hD ⊤ q, W)),
        e q W (a • x) = V.presheaf.map (homOfLE (inf_le_left : W ⊓ LU D ≤ W)).op a • e q W x) ∧
      (∀ (q : ℕ) (W₁ W₂ : V.Opens) (h : W₁ ≤ W₂) (x : Γ(G1.logModule n f D hD ⊤ q, W₂)),
        e q W₁ ((G1.logModule n f D hD ⊤ q).presheaf.map (homOfLE h).op x) =
          (f.relativeDifferentialForms (q : ℤ)).presheaf.map
            (homOfLE (inf_le_inf_right _ h)).op (e q W₂ x)) ∧
      (∀ (q : ℕ) (W : V.Opens) (ω : Γ(f.relativeDifferentialForms (q : ℤ), W ⊓ LU D)),
        ω ∈ Set.range (e q W) ↔
          ∀ (W' : V.affineOpens) (hW' : (W' : V.Opens) ≤ W) (c : ι → Γ(V, W')),
            (∀ j, c j ∈ (J j).ideal W') →
            (∃ η : Γ(f.relativeDifferentialForms (q : ℤ), W'),
              (f.relativeDifferentialForms (q : ℤ)).presheaf.map
                  (homOfLE (inf_le_left : (W' : V.Opens) ⊓ LU D ≤ W')).op η =
                V.presheaf.map (homOfLE (inf_le_left : (W' : V.Opens) ⊓ LU D ≤ W')).op
                    (∏ j, c j) •
                  (f.relativeDifferentialForms (q : ℤ)).presheaf.map
                    (homOfLE (inf_le_inf_right (LU D) hW')).op ω) ∧
            (∃ η : Γ(f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ), W'),
              (f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map
                  (homOfLE (inf_le_left : (W' : V.Opens) ⊓ LU D ≤ W')).op η =
                V.presheaf.map (homOfLE (inf_le_left : (W' : V.Opens) ⊓ LU D ≤ W')).op
                    (∏ j, c j) •
                  (f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map
                    (homOfLE (inf_le_inf_right (LU D) hW')).op
                      (((f.deRhamComplex).d q (q + 1)).val.app (op (W ⊓ LU D)) ω))) := by
  classical
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  let e : ∀ (q : ℕ) (W : V.Opens), Γ(G1.logModule n f D hD ⊤ q, W) →+
      Γ(f.relativeDifferentialForms (q : ℤ), W ⊓ LU D) := fun q W =>
    { toFun := fun x => ambientFormsEquiv f (LU D) q W x.1
      map_zero' := (ambientFormsEquiv f (LU D) q W).map_zero
      map_add' := fun x y => (ambientFormsEquiv f (LU D) q W).map_add x.1 y.1 }
  have hres : ∀ (q : ℕ) (W₁ W₂ : V.Opens) (h : W₁ ≤ W₂) (x : Γ(G1.logModule n f D hD ⊤ q, W₂)),
      e q W₁ ((G1.logModule n f D hD ⊤ q).presheaf.map (homOfLE h).op x) =
        (f.relativeDifferentialForms (q : ℤ)).presheaf.map
          (homOfLE (inf_le_inf_right _ h)).op (e q W₂ x) := fun q W₁ W₂ h x =>
    ambientFormsEquiv_map f (LU D) q h x.1
  refine ⟨e, fun _ _ _ => rfl, fun q W x y hxy => Subtype.ext
    ((ambientFormsEquiv f (LU D) q W).injective hxy), fun q W a x => ?_, hres, ?_⟩
  · change ambientFormsEquiv f (LU D) q W ((((LU D).ι.app W).hom a) •
      (show Γ(((LU D).ι ≫ f).relativeDifferentialForms (q : ℤ), (LU D).ι ⁻¹ᵁ W) from x.1)) = _
    rw [ambientFormsEquiv_smul, ambientRingHom_app]
    rfl
  intro q W ω
  constructor
  · rintro ⟨x, rfl⟩ W' hW' c hc
    have hloc := fun (y : V) (hy : y ∈ (W' : V.Opens)) =>
      exists_extensions_local_of_logForm f D hD J hJ hU hcomp q W x W' hW' c hc hy
    obtain ⟨η₁, hη₁⟩ := exists_map_eq_of_local f D J hJ hU q W' _ fun y hy => by
      obtain ⟨O, hO, hyO, h1, -⟩ := hloc y hy
      exact ⟨O, hO, hyO, h1⟩
    obtain ⟨η₂, hη₂⟩ := exists_map_eq_of_local f D J hJ hU (q + 1) W' _ fun y hy => by
      obtain ⟨O, hO, hyO, -, h2⟩ := hloc y hy
      exact ⟨O, hO, hyO, h2⟩
    exact ⟨⟨η₁, hη₁⟩, ⟨η₂, hη₂⟩⟩
  · intro hdel
    have hx := relativeLogForms_of_local n f D hD ⊤ q fun y hy =>
      exists_rs_mem_relativeLogForms_of_extensions f D hD J hJ hU hcomp q W ω hdel hy
    exact ⟨⟨_, hx⟩, (ambientFormsEquiv f (LU D) q W).apply_symm_apply ω⟩

include hJ hU in
/-- **The ideal of the reduced boundary is invertible**: near every point it is generated on an
affine open by a product of boundary coordinates, a non-zero-divisor. -/
theorem isEffectiveCartierDivisor_suppIdeal
    (hcomp : ∀ ξ : V, ξ ∈ (D.supp : Set V) → Order.coheight ξ = 1 →
      ∃ E ∈ D.support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ) :
    Stacks.Divisors.IsEffectiveCartierDivisor D.suppIdeal := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_dualBasisOne D.suppIdeal
    fun x => ?_
  obtain ⟨c, t, -, hxc, -, -, -, hreg⟩ :=
    exists_weakChart_of_snc' f D J hJ hU (show x ∈ (⊤ : V.Opens) from trivial)
  obtain ⟨g, σ, r'', hr'', j, hxg, hσS, -, -, -, -, hDW⟩ :=
    exists_snc_chart_explicit f D hcomp c x hxc
  refine ⟨V.basicOpen g, hxg, ⟨Stacks.Divisors.dualBasisOneOfPrincipal D.suppIdeal
    ⟨V.basicOpen g, c.W.2.basicOpen g⟩ hDW ?_⟩⟩
  -- the boundary coordinates are non-zero-divisors
  have hcoord : ∀ k : Fin c.r, IsSMulRegular Γ(V, c.W) (c.t (Fin.castLE c.hr k)) := by
    intro k
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)] at hreg
    exact (mul_comm (c.t (Fin.castLE c.hr k)) _ ▸ hreg).of_mul
  let : Algebra Γ(V, c.W) Γ(V, V.basicOpen g) :=
    (V.presheaf.map (homOfLE (V.basicOpen_le g)).op).hom.toAlgebra
  have : IsLocalization.Away g Γ(V, V.basicOpen g) := c.W.2.isLocalization_basicOpen g
  have : Module.Flat Γ(V, c.W) Γ(V, V.basicOpen g) :=
    IsLocalization.flat _ (Submonoid.powers g)
  have hres : ∀ m : Fin r'', IsSMulRegular Γ(V, V.basicOpen g)
      (V.presheaf.map (homOfLE (V.basicOpen_le g)).op (c.t (σ (Fin.castLE hr'' m)))) := by
    intro m
    obtain ⟨k, hk⟩ := hσS m
    rw [hk]
    exact (hcoord k).of_flat
  have hprod : IsSMulRegular Γ(V, V.basicOpen g)
      (∏ m, V.presheaf.map (homOfLE (V.basicOpen_le g)).op (c.t (σ (Fin.castLE hr'' m)))) :=
    Finset.prod_induction _ (IsSMulRegular Γ(V, V.basicOpen g)) (fun a b ha hb => ha.mul hb)
      (isUnit_one.isSMulRegular _) fun m _ => hres m
  refine mem_nonZeroDivisors_iff.2 ⟨fun z hz => hprod (show _ * z = _ * 0 by rw [mul_zero]; exact hz),
    fun z hz => hprod (show _ * z = _ * 0 by rw [mul_zero, mul_comm]; exact hz)⟩

include hJ hU in
/-- **Weak charts on which the reduced boundary is principal**: near every point there is a weak
chart `W` of the support of `D` on which the ideal of the reduced boundary is generated by the
product of the boundary coordinates. -/
theorem exists_weakChart_suppIdeal_eq
    (hcomp : ∀ ξ : V, ξ ∈ (D.supp : Set V) → Order.coheight ξ = 1 →
      ∃ E ∈ D.support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ)
    {O : V.Opens} {y : V} (hy : y ∈ O) :
    ∃ c : WeakChart f n (D.supp : Set V), (c.W : V.Opens) ≤ O ∧ y ∈ (c.W : V.Opens) ∧
      D.suppIdeal.ideal c.W = Ideal.span {∏ i : Fin c.r, c.t (Fin.castLE c.hr i)} := by
  obtain ⟨c, -, hcO, hyc, -, -, -, -⟩ := exists_weakChart_of_snc' f D J hJ hU hy
  obtain ⟨g, σ, r'', hr'', -, hyg, -, -, hbasis, -, -, hDW⟩ :=
    exists_snc_chart_explicit f D hcomp c y hyc
  have hzero : (D.supp : Set V) ∩ (V.basicOpen g : Set V) = V.zeroLocus
      {∏ m : Fin r'', V.presheaf.map (homOfLE (V.basicOpen_le g)).op (c.t (σ (Fin.castLE hr'' m)))} ∩
        (V.basicOpen g : Set V) := by
    have h1 := Scheme.IdealSheafData.coe_support_inter D.suppIdeal ⟨V.basicOpen g, c.W.2.basicOpen g⟩
    have h2 : (D.suppIdeal.support : Set V) = D.supp :=
      Scheme.IdealSheafData.coe_support_vanishingIdeal _
    rw [h2, hDW, Scheme.zeroLocus_span] at h1
    exact h1
  refine ⟨⟨⟨V.basicOpen g, c.W.2.basicOpen g⟩,
    fun i => V.presheaf.map (homOfLE (V.basicOpen_le g)).op (c.t (σ i)), r'', hr'', hbasis, hzero⟩,
    (V.basicOpen_le g).trans hcO, hyg, hDW⟩

end LogEmbedding

/-! ### Sheaves of modules: submodules, epimorphisms, ideal torsion -/

section ModulesAux

open CategoryTheory

/-- A morphism of sheaves of modules whose sections land in a submodule factors through it. -/
noncomputable def liftToSubmodule {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}} [J.HasSheafCompose (forget₂ RingCat.{0} AddCommGrpCat.{0})]
    {A M : SheafOfModules.{0} R} (N : M.Submodule) (φ : A ⟶ M)
    (h : ∀ X (a : A.val.obj X), φ.val.app X a ∈ N.obj X) : A ⟶ N.toSheafOfModules :=
  ⟨PresheafOfModules.homMk
    { app := fun X => AddCommGrpCat.ofHom
        ((φ.val.app X).hom.toAddMonoidHom.codRestrict (N.obj X).toAddSubgroup (h X))
      naturality := fun X Y f => by
        ext a
        exact Subtype.ext (PresheafOfModules.naturality_apply φ.val f a) }
    (fun X r a => Subtype.ext ((φ.val.app X).hom.map_smul r a))⟩

/-- **A locally surjective morphism of sheaves of modules is an epimorphism.** -/
theorem epi_of_locally_surjective {X : Scheme.{0}} {A B : X.Modules} (φ : A ⟶ B)
    (h : ∀ (U : X.Opens) (b : Γ(B, U)) (x : X), x ∈ U → ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧
      ∃ a : Γ(A, V), φ.val.app (op V) a = B.presheaf.map (homOfLE hV).op b) : Epi φ := by
  have h' : TopCat.Presheaf.IsLocallySurjective ((SheafOfModules.toSheaf _).map φ).hom :=
    (TopCat.Presheaf.isLocallySurjective_iff _).2 fun U b x hx => by
      obtain ⟨V, hV, hxV, a, ha⟩ := h U b x hx
      exact ⟨V, hV, ⟨a, ha⟩, hxV⟩
  have hls : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf _).map φ) := h'
  have : Epi ((SheafOfModules.toSheaf _).map φ) := Sheaf.epi_of_isLocallySurjective _
  exact (SheafOfModules.toSheaf _).epi_of_epi_map this

/-- **The twist by an ideal on pure tensors**: `s ⊗ a ↦ a • s`. -/
theorem idealPowerIncl_zero_toTensorSheafSection {X : Scheme.{0}} (I : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor I] (M : X.Modules) (V : X.Opens) (s : Γ(M, V))
    (a : (Stacks.Divisors.Eta.idealSheaf I).val.obj (op V)) :
    (Stacks.IdealTorsion.Eta.idealPowerIncl X.toRingedSpace (Stacks.Divisors.Eta.idealSheaf I)
      (Stacks.Divisors.Eta.idealSheafι I) 0 M).val.app (op V)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace M
        (Stacks.Divisors.Eta.idealSheaf I) (op V) (s ⊗ₜ a)) =
    (show Γ(X, V) from ((Stacks.Divisors.Eta.idealSheafι I).val.app (op V)).hom a) • s := by
  have hc := Stacks.RingedSpace.tensorSheaf_map_unit_tmul X.toRingedSpace (𝟙 M)
    (Stacks.Divisors.Eta.idealSheafι I) (op V) s a
  have hr := Stacks.SheafOfModules.TensorUnit.tensorSheafUnitRightIso_hom_toTensorSheafSection
    X.toRingedSpace M (op V) s (((Stacks.Divisors.Eta.idealSheafι I).val.app (op V)).hom a)
  exact (congrArg _ hc).trans hr

end ModulesAux

/-! ### Quasi-isomorphisms of complexes of sheaves of modules, read on sections -/

section QuasiIsoSections

open HomologicalComplex

variable {V : Scheme.{0}}

theorem modules_hom_app_map {M N : V.Modules} (φ : M ⟶ N) {W W' : V.Opens} (h : W' ≤ W)
    (x : Γ(M, W)) :
    φ.app W' (M.presheaf.map (homOfLE h).op x) = N.presheaf.map (homOfLE h).op (φ.app W x) :=
  PresheafOfModules.naturality_apply φ.val _ x

theorem modules_comp_app_apply {M N K : V.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (W : V.Opens)
    (x : Γ(M, W)) : (φ ≫ ψ).app W x = ψ.app W (φ.app W x) := rfl

/-- A section of the target of an epimorphism of sheaves of modules lifts near every point. -/
theorem exists_app_eq_of_epi {M N : V.Modules} (φ : M ⟶ N) [Epi φ] {W : V.Opens}
    (s : Γ(N, W)) {x : V} (hx : x ∈ W) :
    ∃ (W' : V.Opens) (h : W' ≤ W), x ∈ W' ∧ ∃ t : Γ(M, W'),
      φ.app W' t = N.presheaf.map (homOfLE h).op s := by
  obtain ⟨T, hT, hTs⟩ :=
    @Stacks.SheafOfModules.EpiMono.exists_covering_of_epi _ _ _ _ _ _ M N φ ‹_› W s
  obtain ⟨W', g, hg, hxW'⟩ := (Opens.mem_grothendieckTopology _).1 hT x hx
  obtain ⟨t, ht⟩ := hTs g hg
  exact ⟨W', leOfHom g, hxW', t, ht⟩

variable {X Y : CochainComplex V.Modules ℕ}

/-- **A morphism of complexes of sheaves of modules is a quasi-isomorphism in degree `q`** when
every cycle of the target is, near every point, the image of a cycle up to a boundary, and every
cycle of the source whose image is a boundary is, near every point, a boundary. -/
theorem isIso_homologyMap_of_local (φ : X ⟶ Y) (q : ℕ)
    (ha : ∀ (W : V.Opens) (z : Γ(Y.X q, W)), (Y.d q (q + 1)).app W z = 0 → ∀ x ∈ W,
      ∃ (W' : V.Opens) (h : W' ≤ W), x ∈ W' ∧ ∃ (w : Γ(X.X q, W'))
        (y : Γ(Y.X ((ComplexShape.up ℕ).prev q), W')), (X.d q (q + 1)).app W' w = 0 ∧
          (Y.X q).presheaf.map (homOfLE h).op z = (φ.f q).app W' w + (Y.d _ q).app W' y)
    (hb : ∀ (W : V.Opens) (w : Γ(X.X q, W)) (y : Γ(Y.X ((ComplexShape.up ℕ).prev q), W)),
      (X.d q (q + 1)).app W w = 0 → (φ.f q).app W w = (Y.d _ q).app W y → ∀ x ∈ W,
      ∃ (W' : V.Opens) (h : W' ≤ W), x ∈ W' ∧ ∃ v : Γ(X.X ((ComplexShape.up ℕ).prev q), W'),
        (X.X q).presheaf.map (homOfLE h).op w = (X.d _ q).app W' v) :
    IsIso (homologyMap φ q) := by
  have hiY : ∀ W : V.Opens, Function.Injective ((Y.iCycles q).app W) := fun W =>
    MMP.DeRham.app_injective_of_mono _ W
  have hiX : ∀ W : V.Opens, Function.Injective ((X.iCycles q).app W) := fun W =>
    MMP.DeRham.app_injective_of_mono _ W
  have hcyc : ∀ (W : V.Opens) (w : Γ(X.cycles q, W)),
      (X.d q (q + 1)).app W ((X.iCycles q).app W w) = 0 := fun W w => by
    rw [← modules_comp_app_apply, X.iCycles_d]
    rfl
  refine MMP.DeRham.IsLocalCohomologyRep.isIso (C := Y) (q := q) (c := homologyMap φ q)
    (Rep := fun W s z => ∃ w : Γ(X.cycles q, W), (X.homologyπ q).app W w = s ∧
      z = (φ.f q).app W ((X.iCycles q).app W w)) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro W W' h s z ⟨w, rfl, rfl⟩
    refine ⟨(X.cycles q).presheaf.map (homOfLE h).op w, modules_hom_app_map _ h w, ?_⟩
    exact ((congrArg ((φ.f q).app W') (modules_hom_app_map (X.iCycles q) h w)).trans
      (modules_hom_app_map (φ.f q) h _)).symm
  · rintro W s z ⟨w, rfl, rfl⟩
    have h1 : (Y.d q (q + 1)).app W ((φ.f q).app W ((X.iCycles q).app W w)) =
        (φ.f (q + 1)).app W ((X.d q (q + 1)).app W ((X.iCycles q).app W w)) := by
      change (φ.f q ≫ Y.d q (q + 1)).app W _ = (X.d q (q + 1) ≫ φ.f (q + 1)).app W _
      rw [φ.comm]
    exact h1.trans (by rw [hcyc]; exact map_zero _)
  · rintro W s z ⟨w, rfl, hz⟩
    have hc : (cyclesMap φ q).app W w = z := hiY W (by
      rw [← modules_comp_app_apply, cyclesMap_i, modules_comp_app_apply]
      exact hz.symm)
    change (X.homologyπ q ≫ homologyMap φ q).app W w = (Y.homologyπ q).app W z
    rw [homologyπ_naturality, modules_comp_app_apply, hc]
  · intro W s x hx
    obtain ⟨W', h, hx', w, hw⟩ := exists_app_eq_of_epi (X.homologyπ q) s hx
    exact ⟨W', h, hx', _, w, hw, rfl⟩
  · rintro W s z y ⟨w, rfl, rfl⟩ hy
    refine MMP.DeRham.eq_of_locally_eq_sections _ _ fun x hx => ?_
    obtain ⟨W', h, hx', v, hv⟩ := hb W _ y (hcyc W w) hy.symm x hx
    refine ⟨W', h, hx', ?_⟩
    have hv' : (X.cycles q).presheaf.map (homOfLE h).op w = (X.toCycles _ q).app W' v := hiX W' (by
      rw [modules_hom_app_map, hv, ← modules_comp_app_apply, X.toCycles_i])
    rw [← modules_hom_app_map, hv', ← modules_comp_app_apply, X.toCycles_comp_homologyπ]
    exact (map_zero _).symm
  · intro W z hz x hx
    obtain ⟨W', h, hx', w, y, hw, hzw⟩ := ha W z hz x hx
    obtain ⟨w', rfl⟩ := MMP.DeRham.exists_iCycles_app_eq X q W' w hw
    exact ⟨W', h, hx', _, y, _, ⟨w', rfl, rfl⟩, hzw⟩

end QuasiIsoSections

/-! ### The twist by the reduced boundary -/

section TwistedSplitting

open MMP.Mori.Divisor.LogSpreadingProof.G1

variable {k : Type} [Field k] [IsRegularRing (CommRingCat.of k)] {V : Scheme.{0}}
  (f : V ⟶ Spec (CommRingCat.of k)) {n : ℕ} [SmoothOfRelativeDimension n f]
  (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n f) (p : ℕ) [Fact p.Prime]
  (hV : IsInCharacteristic V p)

/-- `- ⊗ 𝓘` for an invertible module `𝓘`. -/
noncomputable abbrev twistBy (𝓘 : V.Modules) : V.Modules ⥤ V.Modules :=
  Stacks.Duality.LocallyFreeTwist.twist V 𝓘

theorem additive_twistBy (𝓘 : V.Modules)
    [h𝓘 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0} 𝓘] :
    (twistBy 𝓘).Additive :=
  @Stacks.Duality.LocallyFreeTwist.instAdditiveModTwist V 𝓘 h𝓘

theorem preservesFiniteLimits_twistBy (𝓘 : V.Modules)
    [h𝓘 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0} 𝓘] :
    Limits.PreservesFiniteLimits (twistBy 𝓘) :=
  @Stacks.Duality.LocallyFreeTwist.instPreservesFiniteLimitsModTwist V 𝓘 h𝓘

theorem preservesFiniteColimits_twistBy (𝓘 : V.Modules) :
    Limits.PreservesFiniteColimits (twistBy 𝓘) :=
  Stacks.Duality.LocallyFreeTwist.instPreservesFiniteColimitsModTwist (X := V) 𝓘

attribute [local instance] additive_twistBy preservesFiniteLimits_twistBy
  preservesFiniteColimits_twistBy

/-- **Twisting a decomposition.** An isomorphism `⨁_q E_q[-q] ≅ B` in the derived category,
tensored by a finite locally free module, is an isomorphism `⨁_q (E_q ⊗ 𝓘)[-q] ≅ B ⊗ 𝓘`. -/
theorem nonempty_iso_twistBy [HasDerivedCategory.{0} V.Modules] (𝓘 : V.Modules)
    [h𝓘 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0} 𝓘] (m : ℕ)
    (E : Fin (m + 1) → V.Modules) (B : CochainComplex V.Modules ℤ)
    (Φ : (⨁ fun q : Fin (m + 1) ↦ (DerivedCategory.singleFunctor V.Modules (q : ℤ)).obj (E q)) ≅
      DerivedCategory.Q.obj B) :
    Nonempty ((⨁ fun q : Fin (m + 1) ↦
        (DerivedCategory.singleFunctor V.Modules (q : ℤ)).obj ((twistBy 𝓘).obj (E q))) ≅
      DerivedCategory.Q.obj (((twistBy 𝓘).mapHomologicalComplex (ComplexShape.up ℤ)).obj B)) := by
  let tw := twistBy 𝓘
  let eL : tw.mapDerivedCategory.obj
        (⨁ fun q : Fin (m + 1) ↦ (DerivedCategory.singleFunctor V.Modules (q : ℤ)).obj (E q)) ≅
      ⨁ fun q : Fin (m + 1) ↦ (DerivedCategory.singleFunctor V.Modules (q : ℤ)).obj
        (tw.obj (E q)) :=
    tw.mapDerivedCategory.mapBiproduct _ ≪≫
      Limits.biproduct.mapIso fun q => (tw.mapDerivedCategorySingleFunctor (q : ℤ)).app _
  exact ⟨eL.symm ≪≫ tw.mapDerivedCategory.mapIso Φ ≪≫ tw.mapDerivedCategoryFactors.app B⟩

end TwistedSplitting

/-! ### Sections of the twist by the ideal of the reduced boundary -/

section TwistSections

open MMP.Mori.Divisor.LogSpreadingProof.G1 Stacks.SheafOfModules.TensorStalkRingedSpace

variable {V : Scheme.{0}}

/-- The canonical map into the sheaf tensor product commutes with restriction. -/
theorem toTensorSheafSection_map (𝓘 M : V.Modules) {U U' : V.Opens} (h : U' ≤ U)
    (m : Γ(M, U)) (b : Γ(𝓘, U)) :
    ((twistBy 𝓘).obj M).presheaf.map (homOfLE h).op
        (toTensorSheafSection V.toRingedSpace M 𝓘 (op U) (m ⊗ₜ b)) =
      toTensorSheafSection V.toRingedSpace M 𝓘 (op U')
        (M.presheaf.map (homOfLE h).op m ⊗ₜ 𝓘.presheaf.map (homOfLE h).op b) :=
  (PresheafOfModules.naturality_apply
    (sheafifyUnit V.toRingedSpace
      ((PresheafOfModules.tensorObj (O := V.toRingedSpace.presheaf) M.val 𝓘.val))) (homOfLE h).op
    (m ⊗ₜ[V.presheaf.obj (op U)] b)).symm

/-- The canonical map into the sheaf tensor product is additive. -/
theorem toTensorSheafSection_sum (𝓘 M : V.Modules) (U : V.Opens) {ι : Type*}
    (s : Finset ι) (g : ι → TensorProduct (V.presheaf.obj (op U)) Γ(M, U) Γ(𝓘, U)) :
    toTensorSheafSection V.toRingedSpace M 𝓘 (op U) (∑ i ∈ s, g i) =
      ∑ i ∈ s, toTensorSheafSection V.toRingedSpace M 𝓘 (op U) (g i) :=
  map_sum ((sheafifyUnit V.toRingedSpace
    ((PresheafOfModules.tensorObj (O := V.toRingedSpace.presheaf) M.val 𝓘.val))).app (op U)).hom g s

theorem toTensorSheafSection_zero_tmul (𝓘 M : V.Modules) (U : V.Opens) (b : Γ(𝓘, U)) :
    toTensorSheafSection V.toRingedSpace M 𝓘 (op U) ((0 : Γ(M, U)) ⊗ₜ b) = 0 :=
  (congrArg _ (TensorProduct.zero_tmul _ b)).trans <| map_zero ((sheafifyUnit V.toRingedSpace
    ((PresheafOfModules.tensorObj (O := V.toRingedSpace.presheaf) M.val 𝓘.val))).app (op U)).hom

/-- Twisting a morphism acts on the first factor of a pure tensor. -/
theorem twistBy_map_toTensorSheafSection (𝓘 : V.Modules) {M N : V.Modules} (g : M ⟶ N)
    (U : V.Opens) (m : Γ(M, U)) (b : Γ(𝓘, U)) :
    ((twistBy 𝓘).map g).app U (toTensorSheafSection V.toRingedSpace M 𝓘 (op U) (m ⊗ₜ b)) =
      toTensorSheafSection V.toRingedSpace N 𝓘 (op U) (g.app U m ⊗ₜ b) :=
  Stacks.IdealTorsion.Eta.tensorRightFunctor_map_toTensorSheafSection V.toRingedSpace 𝓘 g (op U) m b

/-- A section of the ideal sheaf over `U` which is a multiple of a given one. -/
theorem toTensorSheafSection_smul_right (I : V.IdealSheafData) (M : V.Modules)
    (U : V.Opens) (m : Γ(M, U)) (y : (Stacks.Divisors.idealSheafOfModules I).val.obj (op U))
    (c : Γ(V, U)) :
    toTensorSheafSection V.toRingedSpace M (Stacks.Divisors.idealSheafOfModules I) (op U)
      (m ⊗ₜ Stacks.SheafOfModules.smulSectionMap (𝒪 := V.sheaf.obj)
        (h𝒪 := (structureSheafRing V.toRingedSpace).property) y c) =
    toTensorSheafSection V.toRingedSpace M (Stacks.Divisors.idealSheafOfModules I) (op U)
      ((c • m) ⊗ₜ y) :=
  congrArg _ (TensorProduct.smul_tmul (R := V.toRingedSpace.presheaf.obj (op U))
    (R' := V.toRingedSpace.presheaf.obj (op U)) c m y).symm

/-- **Sections of the twist by a principal ideal are pure tensors.** Over an affine open `U` on
which `I` is generated by `idealSheafSection I y`, every section of `M ⊗ I` which is a finite
sum of pure tensors is `m ⊗ y` for a section `m` of `M`. -/
theorem exists_sum_toTensorSheafSection_eq (I : V.IdealSheafData) (M : V.Modules)
    (U : V.affineOpens) (y : (Stacks.Divisors.idealSheafOfModules I).val.obj (op (U : V.Opens)))
    (hy : I.ideal U = Ideal.span {Stacks.Divisors.idealSheafSection I y}) {N : ℕ}
    (a : Fin N → Γ(M, U)) (b : Fin N → (Stacks.Divisors.idealSheafOfModules I).val.obj (op (U : V.Opens))) :
    ∃ m : Γ(M, U), ∑ j, toTensorSheafSection V.toRingedSpace M
        (Stacks.Divisors.idealSheafOfModules I) (op (U : V.Opens)) (a j ⊗ₜ b j) =
      toTensorSheafSection V.toRingedSpace M (Stacks.Divisors.idealSheafOfModules I)
        (op (U : V.Opens)) (m ⊗ₜ y) := by
  have he : ∀ j, ∃ e : Γ(V, U), b j = Stacks.SheafOfModules.smulSectionMap (𝒪 := V.sheaf.obj)
      (h𝒪 := (structureSheafRing V.toRingedSpace).property) y e := by
    intro j
    have hmem : Stacks.Divisors.idealSheafSection I (b j) ∈ I.ideal U :=
      (Stacks.Divisors.mem_ideal_iff_exists_idealSheafSection I U _).2 ⟨b j, rfl⟩
    rw [hy] at hmem
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨e, Stacks.Divisors.idealSheafSection_injective I ?_⟩
    rw [Stacks.Divisors.idealSheafSection_smulSectionMap]
    exact he.symm
  choose e he using he
  refine ⟨∑ j, e j • a j, ?_⟩
  calc ∑ j, toTensorSheafSection V.toRingedSpace M (Stacks.Divisors.idealSheafOfModules I)
          (op (U : V.Opens)) (a j ⊗ₜ b j)
      = ∑ j, toTensorSheafSection V.toRingedSpace M (Stacks.Divisors.idealSheafOfModules I)
          (op (U : V.Opens)) ((e j • a j) ⊗ₜ y) :=
        Finset.sum_congr rfl fun j _ => by rw [he j, toTensorSheafSection_smul_right]
    _ = toTensorSheafSection V.toRingedSpace M (Stacks.Divisors.idealSheafOfModules I)
          (op (U : V.Opens)) (∑ j, (e j • a j) ⊗ₜ y) := (toTensorSheafSection_sum _ _ _ _ _).symm
    _ = _ := congrArg _ (TensorProduct.sum_tmul _ _ _).symm

end TwistSections

/-- A morphism into the direct image of a sheaf of modules whose sections land in a submodule
factors through the direct image of the submodule. -/
noncomputable def liftToPushforwardSubmodule {X Y : Scheme.{0}} (g : X ⟶ Y)
    {M : X.Modules} (N : M.Submodule) {A : Y.Modules}
    (φ : A ⟶ (Scheme.Modules.pushforward g).obj M)
    (h : ∀ (U : Y.Opens) (a : Γ(A, U)), (φ.app U a : Γ(M, g ⁻¹ᵁ U)) ∈ N.obj (op (g ⁻¹ᵁ U))) :
    A ⟶ (Scheme.Modules.pushforward g).obj N.toSheafOfModules :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        ((φ.val.app U).hom.toAddMonoidHom.codRestrict (N.obj (op (g ⁻¹ᵁ U.unop))).toAddSubgroup
          (h U.unop))
      naturality := fun U U' i => by
        ext a
        exact Subtype.ext (PresheafOfModules.naturality_apply φ.val i a) }
    (fun U r a => Subtype.ext ((φ.val.app U).hom.map_smul r a))⟩

/-- The ideal sheaf of the reduced boundary, as a sheaf of modules. -/
noncomputable abbrev suppTwist {V : Scheme.{0}} (D : MMP.Mori.Divisor V) : V.Modules :=
  Stacks.Divisors.idealSheafOfModules D.suppIdeal

/-! ### The twisted logarithmic forms as a twist of the logarithmic forms -/

section TwistedComparison

open MMP.Mori.Divisor.LogSpreadingProof.G1 Stacks.SheafOfModules.TensorStalkRingedSpace Stacks.Frobenius

attribute [local instance] additive_twistBy preservesFiniteLimits_twistBy
  preservesFiniteColimits_twistBy

variable {k : Type} [Field k] [IsRegularRing (CommRingCat.of k)] {V : Scheme.{0}}
  (f : V ⟶ Spec (CommRingCat.of k)) {n : ℕ} [SmoothOfRelativeDimension n f]
  (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n f) {ι : Type} [Fintype ι]
  (J : ι → V.IdealSheafData)
  (hJ : ∀ T : Finset ι,
    SmoothOfRelativeDimension (n - T.card) ((⨆ j ∈ T, J j).subschemeι ≫ f) ∧
    (n < T.card → IsEmpty (⨆ j ∈ T, J j).subscheme))
  (hU : LU D = ((⨅ j, J j).support).compl)
  (hcomp : ∀ ξ : V, ξ ∈ (D.supp : Set V) → Order.coheight ξ = 1 →
      ∃ E ∈ D.support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ)

/-- The multiplication `M ⊗ I_D ⟶ M` by the ideal of the reduced boundary. -/
noncomputable abbrev twistIncl [Stacks.Divisors.IsEffectiveCartierDivisor D.suppIdeal]
    (M : V.Modules) :
    (twistBy (suppTwist D)).obj M ⟶ M :=
  Stacks.IdealTorsion.Eta.idealPowerIncl V.toRingedSpace (Stacks.Divisors.Eta.idealSheaf D.suppIdeal)
    (Stacks.Divisors.Eta.idealSheafι D.suppIdeal) 0 M

theorem twistIncl_natural [Stacks.Divisors.IsEffectiveCartierDivisor D.suppIdeal]
    {M N : V.Modules} (g : M ⟶ N) :
    (twistBy (suppTwist D)).map g ≫ twistIncl D N =
      twistIncl D M ≫ g :=
  Stacks.IdealTorsion.Eta.idealPowerIncl_zero_natural V.toRingedSpace _ _ g

theorem twistIncl_toTensorSheafSection [Stacks.Divisors.IsEffectiveCartierDivisor D.suppIdeal]
    (M : V.Modules) (U : V.Opens) (m : Γ(M, U))
    (y : (Stacks.Divisors.idealSheafOfModules D.suppIdeal).val.obj (op U)) :
    (twistIncl D M).app U (toTensorSheafSection V.toRingedSpace M _ (op U) (m ⊗ₜ y)) =
      Stacks.Divisors.idealSheafSection D.suppIdeal y • m :=
  idealPowerIncl_zero_toTensorSheafSection D.suppIdeal M U m y

include hJ hU hcomp in
/-- **Sections of a twist by the reduced boundary are locally pure tensors** `m ⊗ y`, with `y`
the generator `t₁ ⋯ t_r` of the ideal on a weak chart. -/
theorem exists_twist_restrict_eq (M : V.Modules) {W : V.Opens}
    (t : Γ((twistBy (suppTwist D)).obj M, W)) {x : V}
    (hx : x ∈ W) :
    ∃ (c : WeakChart f n (D.supp : Set V)) (hcW : (c.W : V.Opens) ≤ W)
      (y : (Stacks.Divisors.idealSheafOfModules D.suppIdeal).val.obj (op (c.W : V.Opens))),
      x ∈ (c.W : V.Opens) ∧
      Stacks.Divisors.idealSheafSection D.suppIdeal y = ∏ i : Fin c.r, c.t (Fin.castLE c.hr i) ∧
      ∃ m : Γ(M, c.W), ((twistBy (suppTwist D)).obj M).presheaf.map
          (homOfLE hcW).op t =
        toTensorSheafSection V.toRingedSpace M _ (op (c.W : V.Opens)) (m ⊗ₜ y) := by
  obtain ⟨S, hS, hSt⟩ := Stacks.SheafOfModules.TensorUnit.exists_sieve_sum_toTensorSheafSection
    V.toRingedSpace M (Stacks.Divisors.idealSheafOfModules D.suppIdeal) W t
  obtain ⟨W₁, k₁, hk₁, hxW₁⟩ := (Opens.mem_grothendieckTopology _).1 hS x hx
  obtain ⟨N, a, b, hab⟩ := hSt k₁ hk₁
  obtain ⟨c, hcW₁, hxc, hideal⟩ := exists_weakChart_suppIdeal_eq f D J hJ hU hcomp hxW₁
  obtain ⟨y, hy⟩ := (Stacks.Divisors.mem_ideal_iff_exists_idealSheafSection D.suppIdeal c.W _).1
    (by rw [hideal]; exact Ideal.mem_span_singleton_self _)
  obtain ⟨m, hm⟩ := exists_sum_toTensorSheafSection_eq D.suppIdeal M c.W y (by rw [hy]; exact hideal)
    (fun j => M.presheaf.map (homOfLE hcW₁).op (a j))
    (fun j => (Stacks.Divisors.idealSheafOfModules D.suppIdeal).val.map (homOfLE hcW₁).op (b j))
  refine ⟨c, hcW₁.trans (leOfHom k₁), y, hxc, hy, m, ?_⟩
  rw [← hm, ← modules_map_map_apply _ k₁.op (homOfLE hcW₁).op]
  change ((twistBy (suppTwist D)).obj M).presheaf.map
    (homOfLE hcW₁).op (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨V.toRingedSpace.presheaf,
      V.toRingedSpace.IsSheaf⟩).obj M).obj _)).val.map k₁.op t) = _
  rw [hab]
  exact (map_sum _ _ _).trans
    (Finset.sum_congr rfl fun j _ => toTensorSheafSection_map _ M hcW₁ (a j) (b j))

/-- A morphism of sheaves of modules injective on all sections is a monomorphism. -/
theorem mono_of_app_injective {X : Scheme.{0}} {A B : X.Modules} (φ : A ⟶ B)
    (h : ∀ U : X.Opens, Function.Injective (φ.app U)) : Mono φ := by
  have hloc : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ.val) :=
    Presheaf.isLocallyInjective_of_injective _ _ fun W => h W.unop
  have : Sheaf.IsLocallyInjective ((SheafOfModules.toSheaf _).map φ) := hloc
  have := Sheaf.mono_of_isLocallyInjective ((SheafOfModules.toSheaf _).map φ)
  exact (SheafOfModules.toSheaf _).mono_of_mono_map ‹_›

/-- Multiplication by the product of the boundary coordinates is injective on forms off the
divisor. -/
theorem chartSmul_prod_eq_zero {c : WeakChart f n (D.supp : Set V)} {q : ℤ}
    {ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece q).val.obj
      (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens)))}
    (h : chartSmul f D c (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ω = 0) : ω = 0 := by
  have hu : IsUnit (((LU D).ι.app c.W).hom (∏ i : Fin c.r, c.t (Fin.castLE c.hr i))) := by
    rw [map_prod]
    exact IsUnit.prod_iff.2 fun k _ => isUnit_app_weakChart f D c k
  have hu' : IsUnit (show (Stacks.RingedSpace.structureRingSheaf
      (LU D).toScheme.toRingedSpace).obj.obj (op ((LU D).ι ⁻¹ᵁ (c.W : V.Opens))) from
        ((LU D).ι.app c.W).hom (∏ i : Fin c.r, c.t (Fin.castLE c.hr i))) := hu
  exact hu'.smul_left_cancel.1 (h.trans (smul_zero _).symm)

include hJ hU hcomp in
/-- The multiplication `Ω^q(log D) ⊗ I_D ⟶ j_*Ω^q` lands in `Ω^q(log D)(-D)`. -/
theorem twistIncl_logModule_mem [Stacks.Divisors.IsEffectiveCartierDivisor D.suppIdeal]
    (q : ℕ) (W : V.Opens)
    (t : Γ((twistBy (suppTwist D)).obj
      (logModule n f D hD ⊤ q), W)) :
    (show ↥((logModuleSubmodule n f D hD ⊤ q).obj (op W)) from
      (twistIncl D (logModule n f D hD ⊤ q)).app W t).1 ∈
      MMP.Mori.Divisor.relativeLogForms n f D hD D.suppIdeal q W := by
  refine relativeLogForms_of_local n f D hD D.suppIdeal q fun x hx => ?_
  obtain ⟨c, hcW, y, hxc, hy, m, hm⟩ := exists_twist_restrict_eq f D J hJ hU hcomp _ t hx
  refine ⟨c.W, hcW, hxc, ?_⟩
  have e : rs f D q hcW (show ↥((logModuleSubmodule n f D hD ⊤ q).obj (op W)) from
      (twistIncl D (logModule n f D hD ⊤ q)).app W t).1 =
      (show ↥((logModuleSubmodule n f D hD ⊤ q).obj (op (c.W : V.Opens))) from
        (twistIncl D (logModule n f D hD ⊤ q)).app c.W
          (((twistBy (suppTwist D)).obj
            (logModule n f D hD ⊤ q)).presheaf.map (homOfLE hcW).op t)).1 := by
    rw [modules_hom_app_map]
    exact (PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) _).symm
  rw [e, hm, twistIncl_toTensorSheafSection, hy]
  exact (mem_relativeLogForms_suppIdeal_iff f D hD hcomp c q _).2 ⟨m.1, m.2, rfl⟩

/-- **The comparison** `Ω^q(log D) ⊗ I_D ⟶ Ω^q(log D)(-D)`. -/
noncomputable def twistLogIncl [Stacks.Divisors.IsEffectiveCartierDivisor D.suppIdeal]
    (q : ℕ) :
    (twistBy (suppTwist D)).obj (logModule n f D hD ⊤ q) ⟶
      logModule n f D hD D.suppIdeal q :=
  liftToSubmodule (logModuleSubmodule n f D hD D.suppIdeal q)
    (twistIncl D (logModule n f D hD ⊤ q) ≫ (logModuleSubmodule n f D hD ⊤ q).ι)
    (fun X a => twistIncl_logModule_mem f D hD J hJ hU hcomp q X.unop a)

include hJ hU hcomp in
/-- **`Ω^q(log D) ⊗ I_D ≅ Ω^q(log D)(-D)`.** -/
theorem isIso_twistLogIncl [Stacks.Divisors.IsEffectiveCartierDivisor D.suppIdeal]
    (q : ℕ) : IsIso (twistLogIncl f D hD J hJ hU hcomp q) := by
  have hval : ∀ (W : V.Opens) (t : Γ((twistBy (Stacks.Divisors.idealSheafOfModules
      D.suppIdeal)).obj (logModule n f D hD ⊤ q), W)),
      (show ↥((logModuleSubmodule n f D hD D.suppIdeal q).obj (op W)) from
        (twistLogIncl f D hD J hJ hU hcomp q).app W t).1 =
      (show ↥((logModuleSubmodule n f D hD ⊤ q).obj (op W)) from
        (twistIncl D (logModule n f D hD ⊤ q)).app W t).1 := fun _ _ => rfl
  have hinj : ∀ W, Function.Injective ((twistLogIncl f D hD J hJ hU hcomp q).app W) := by
    intro W
    refine (injective_iff_map_eq_zero _).2 fun t ht => ?_
    refine MMP.DeRham.eq_of_locally_eq_sections _ _ fun x hx => ?_
    obtain ⟨c, hcW, y, hxc, hy, m, hm⟩ := exists_twist_restrict_eq f D J hJ hU hcomp _ t hx
    refine ⟨c.W, hcW, hxc, ?_⟩
    rw [hm, map_zero]
    have h0 := congrArg (fun s => (show ↥((logModuleSubmodule n f D hD D.suppIdeal q).obj
      (op (c.W : V.Opens))) from s).1)
      ((modules_hom_app_map (twistLogIncl f D hD J hJ hU hcomp q) hcW t).trans
        (by rw [ht, map_zero]))
    simp only at h0
    rw [hval, hm, twistIncl_toTensorSheafSection, hy] at h0
    have hm0 : m = 0 := Subtype.ext (chartSmul_prod_eq_zero f D h0)
    rw [hm0]
    exact toTensorSheafSection_zero_tmul _ _ _ _
  have hmono := mono_of_app_injective _ hinj
  have hepi : Epi (twistLogIncl f D hD J hJ hU hcomp q) := by
    refine epi_of_locally_surjective _ fun W s x hx => ?_
    obtain ⟨c, hcW, hxc, hideal⟩ := exists_weakChart_suppIdeal_eq f D J hJ hU hcomp hx
    obtain ⟨y, hy⟩ := (Stacks.Divisors.mem_ideal_iff_exists_idealSheafSection D.suppIdeal c.W _).1
      (by rw [hideal]; exact Ideal.mem_span_singleton_self _)
    have hs := ((logModule n f D hD D.suppIdeal q).presheaf.map (homOfLE hcW).op s).2
    obtain ⟨ω₀, h₀, hω₀⟩ := (mem_relativeLogForms_suppIdeal_iff f D hD hcomp c q _).1 hs
    obtain ⟨m₀, hm₀⟩ : ∃ m₀ : Γ(logModule n f D hD ⊤ q, c.W), m₀.1 = ω₀ := ⟨⟨ω₀, h₀⟩, rfl⟩
    refine ⟨c.W, hcW, hxc, toTensorSheafSection V.toRingedSpace _ _ (op (c.W : V.Opens))
      (m₀ ⊗ₜ y), ?_⟩
    refine Subtype.ext ?_
    refine (hval _ _).trans ?_
    dsimp only
    rw [twistIncl_toTensorSheafSection, hy]
    exact (congrArg _ hm₀).trans hω₀.symm
  exact isIso_of_mono_of_epi _

variable (p : ℕ) [Fact p.Prime] (hV : IsInCharacteristic V p)

/-- Functions act on the Frobenius direct image through their `p`-th powers, read on the
sections of the module itself. -/
theorem pushforward_frobenius_smul' (M : V.Modules) (U : V.Opens) (r : Γ(V, U))
    (m : Γ(M, U)) :
    r • (show Γ((Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj M, U) from m) =
      (show Γ(M, U) from (r ^ p) • m) := by
  change (show Γ(V, U) from (absoluteFrobenius V p hV).app U r) • m = _
  rw [absoluteFrobenius_app_apply]

/-- Functions act on the Frobenius direct image through their `p`-th powers. -/
theorem pushforward_frobenius_smul (M : V.Modules) (U : V.Opens) (r : Γ(V, U))
    (m : Γ((Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj M, U)) :
    r • m = (show Γ(M, U) from (r ^ p) • (show Γ(M, U) from m)) := by
  change (show Γ(V, U) from (absoluteFrobenius V p hV).app U r) • (show Γ(M, U) from m) = _
  rw [absoluteFrobenius_app_apply]

include hJ hU hcomp in
/-- The multiplication `F_*Ω^q(log D) ⊗ I_D ⟶ F_*j_*Ω^q` lands in `F_*Ω^q(log D)(-D)`. -/
theorem twistIncl_frobenius_logModule_mem
    [Stacks.Divisors.IsEffectiveCartierDivisor D.suppIdeal] (q : ℕ) (W : V.Opens)
    (t : Γ((twistBy (suppTwist D)).obj
      ((Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj (logModule n f D hD ⊤ q)), W)) :
    (show ↥((logModuleSubmodule n f D hD ⊤ q).obj (op W)) from
      (twistIncl D ((Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj
        (logModule n f D hD ⊤ q))).app W t).1 ∈
      MMP.Mori.Divisor.relativeLogForms n f D hD D.suppIdeal q W := by
  refine relativeLogForms_of_local n f D hD D.suppIdeal q fun x hx => ?_
  obtain ⟨c, hcW, y, hxc, hy, m, hm⟩ := exists_twist_restrict_eq f D J hJ hU hcomp _ t hx
  refine ⟨c.W, hcW, hxc, ?_⟩
  have e : rs f D q hcW (show ↥((logModuleSubmodule n f D hD ⊤ q).obj (op W)) from
      (twistIncl D ((Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj
        (logModule n f D hD ⊤ q))).app W t).1 =
      (show ↥((logModuleSubmodule n f D hD ⊤ q).obj (op (c.W : V.Opens))) from
        (twistIncl D ((Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj
          (logModule n f D hD ⊤ q))).app c.W
          (((twistBy (suppTwist D)).obj
            ((Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj
              (logModule n f D hD ⊤ q))).presheaf.map (homOfLE hcW).op t)).1 := by
    rw [modules_hom_app_map]
    exact (PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) _).symm
  rw [e, hm, twistIncl_toTensorSheafSection, hy, pushforward_frobenius_smul]
  have hp1 : (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p =
      (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) * (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ (p - 1) := by
    rw [← pow_succ']
    congr 1
    have := (Fact.out : p.Prime).one_lt
    omega
  refine (mem_relativeLogForms_suppIdeal_iff f D hD hcomp c q _).2
    ⟨chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ (p - 1)) m.1,
      smul_mem_relativeLogForms n f D hD ⊤ q _ m.2, ?_⟩
  change chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p) m.1 = _
  rw [hp1]
  simp only [chartSmul, map_mul]
  exact mul_smul _ _ _

/-- **The comparison** `F_*Ω^q(log D) ⊗ I_D ⟶ F_*Ω^q(log D)(-D)`, the multiplication. -/
noncomputable def twistFrobLogIncl [Stacks.Divisors.IsEffectiveCartierDivisor D.suppIdeal]
    (q : ℕ) :
    (twistBy (suppTwist D)).obj
        ((Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj (logModule n f D hD ⊤ q)) ⟶
      (Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj
        (logModule n f D hD D.suppIdeal q) :=
  liftToPushforwardSubmodule (absoluteFrobenius V p hV) (logModuleSubmodule n f D hD D.suppIdeal q)
    (twistIncl D ((Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj
        (logModule n f D hD ⊤ q)) ≫
      (Scheme.Modules.pushforward (absoluteFrobenius V p hV)).map (logModuleSubmodule n f D hD ⊤ q).ι)
    (fun U a => twistIncl_frobenius_logModule_mem f D hD J hJ hU hcomp p hV q U a)

theorem twistFrobLogIncl_app [Stacks.Divisors.IsEffectiveCartierDivisor D.suppIdeal]
    (q : ℕ) (U : V.Opens) (t) :
    (show ↥((logModuleSubmodule n f D hD D.suppIdeal q).obj (op U)) from
      (twistFrobLogIncl f D hD J hJ hU hcomp p hV q).app U t).1 =
    (show ↥((logModuleSubmodule n f D hD ⊤ q).obj (op U)) from
      (twistIncl D ((Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj
        (logModule n f D hD ⊤ q))).app U t).1 := rfl

variable
    (d : ∀ q : ℕ, (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n f D hD ⊤ q) ⟶
        (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n f D hD ⊤ (q + 1)))
    (hd : ∀ q, d q ≫ d (q + 1) = 0)
    (d' : ∀ q : ℕ, (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n f D hD D.suppIdeal q) ⟶
        (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n f D hD D.suppIdeal (q + 1)))
    (hd' : ∀ q, d' q ≫ d' (q + 1) = 0)
    (hdR' : ∀ (q : ℕ) (W : V.Opens) (x : Γ(G1.logModule n f D hD D.suppIdeal q, W)),
        (show ↥((G1.logModuleSubmodule n f D hD D.suppIdeal (q + 1)).obj (op W))
          from (d' q).app W x).1 =
        ((Scheme.Hom.deRhamComplex ((G1.LU D).ι ≫ f)).d q (q + 1)).val.app
          (op ((G1.LU D).ι ⁻¹ᵁ W))
          (show ↥((G1.logModuleSubmodule n f D hD D.suppIdeal q).obj (op W)) from x).1)
    (hdR : ∀ (q : ℕ) (W : V.Opens) (x : Γ(G1.logModule n f D hD ⊤ q, W)),
        (show ↥((G1.logModuleSubmodule n f D hD ⊤ (q + 1)).obj (op W))
          from (d q).app W x).1 =
        ((Scheme.Hom.deRhamComplex ((G1.LU D).ι ≫ f)).d q (q + 1)).val.app
          (op ((G1.LU D).ι ⁻¹ᵁ W))
          (show ↥((G1.logModuleSubmodule n f D hD ⊤ q).obj (op W)) from x).1)

include hdR hdR' in
theorem twistFrobLogIncl_comm [Stacks.Divisors.IsEffectiveCartierDivisor D.suppIdeal]
    (q : ℕ) :
    (twistBy (suppTwist D)).map (d q) ≫
        twistFrobLogIncl f D hD J hJ hU hcomp p hV (q + 1) =
      twistFrobLogIncl f D hD J hJ hU hcomp p hV q ≫ d' q := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext t
  refine Subtype.ext ?_
  have n1 := congrArg (fun φ => φ.app U t) (twistIncl_natural D (d q))
  simp only at n1
  change (show ↥((logModuleSubmodule n f D hD ⊤ (q + 1)).obj (op U)) from
      (twistIncl D _).app U (((twistBy _).map (d q)).app U t)).1 =
    (show ↥((logModuleSubmodule n f D hD D.suppIdeal (q + 1)).obj (op U)) from
      (d' q).app U ((twistFrobLogIncl f D hD J hJ hU hcomp p hV q).app U t)).1
  dsimp only
  rw [← modules_comp_app_apply, n1, modules_comp_app_apply]
  exact (hdR q U _).trans (hdR' q U ((twistFrobLogIncl f D hD J hJ hU hcomp p hV q).app U t)).symm

include hdR hdR' in
theorem twistFrobLogIncl_app_tmul [Stacks.Divisors.IsEffectiveCartierDivisor D.suppIdeal]
    (c : WeakChart f n (D.supp : Set V))
    (y : (Stacks.Divisors.idealSheafOfModules D.suppIdeal).val.obj (op (c.W : V.Opens)))
    (hy : Stacks.Divisors.idealSheafSection D.suppIdeal y = ∏ i : Fin c.r, c.t (Fin.castLE c.hr i))
    (q : ℕ) (m : Γ(logModule n f D hD ⊤ q, c.W)) :
    ((twistFrobLogIncl f D hD J hJ hU hcomp p hV q).app c.W
      (toTensorSheafSection V.toRingedSpace _ _ (op (c.W : V.Opens)) (m ⊗ₜ y))).1 =
      chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p) m.1 := by
  have e1 := twistIncl_toTensorSheafSection D ((Scheme.Modules.pushforward
    (absoluteFrobenius V p hV)).obj (logModule n f D hD ⊤ q)) c.W m y
  have e2 := pushforward_frobenius_smul' p hV (logModule n f D hD ⊤ q) c.W
    (Stacks.Divisors.idealSheafSection D.suppIdeal y) m
  refine (twistFrobLogIncl_app f D hD J hJ hU hcomp p hV q c.W _).trans ?_
  refine (congrArg Subtype.val (e1.trans e2)).trans ?_
  exact congrArg (fun r : Γ(V, c.W) => Subtype.val
    ((r • (m : Γ(logModule n f D hD ⊤ q, c.W))) : Γ(logModule n f D hD ⊤ q, c.W)))
    (congrArg (· ^ p) hy)

include hdR hdR' in
/-- A cycle of `F_*Ω⁰(log D)(-D)` is locally the image of a cycle of `F_*Ω⁰(log D) ⊗ I_D`. -/
theorem exists_twistFrob_cycle_zero [Stacks.Divisors.IsEffectiveCartierDivisor D.suppIdeal]
    (W : V.Opens) (z : Γ((Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj
      (logModule n f D hD D.suppIdeal 0), W))
    (hz : (d' 0).app W z = 0) {x : V} (hx : x ∈ W) :
    ∃ (W' : V.Opens) (h : W' ≤ W), x ∈ W' ∧
      ∃ w : Γ((twistBy (suppTwist D)).obj ((Scheme.Modules.pushforward
          (absoluteFrobenius V p hV)).obj (logModule n f D hD ⊤ 0)), W'),
        ((twistBy (suppTwist D)).map (d 0)).app W' w = 0 ∧
        ((Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj
          (logModule n f D hD D.suppIdeal 0)).presheaf.map (homOfLE h).op z =
          (twistFrobLogIncl f D hD J hJ hU hcomp p hV 0).app W' w := by
  obtain ⟨c, hcW, hxc, hideal⟩ := exists_weakChart_suppIdeal_eq f D J hJ hU hcomp hx
  obtain ⟨y, hy⟩ := (Stacks.Divisors.mem_ideal_iff_exists_idealSheafSection D.suppIdeal c.W _).1
    (by rw [hideal]; exact Ideal.mem_span_singleton_self _)
  obtain ⟨G0, -, -, -, -⟩ := twistedLogForms_chart f D hD hcomp p hV c
  obtain ⟨zr, hzr⟩ : ∃ zr : Γ(logModule n f D hD D.suppIdeal 0, c.W),
      zr = (logModule n f D hD D.suppIdeal 0).presheaf.map (homOfLE hcW).op z := ⟨_, rfl⟩
  have e2 : (d' 0).app c.W zr = 0 := by
    rw [hzr]
    exact (modules_hom_app_map (d' 0) hcW z).trans (by rw [hz, map_zero])
  have hdz₀ : chartD f D c 0 zr.1 = 0 := by
    have e1 := hdR' 0 c.W zr
    rw [e2] at e1
    exact e1.symm.trans rfl
  obtain ⟨ω, hω, hzω, hdω⟩ := G0 zr.1 zr.2 hdz₀
  obtain ⟨mω, hmω⟩ : ∃ mω : Γ(logModule n f D hD ⊤ 0, c.W), mω.1 = ω := ⟨⟨ω, hω⟩, rfl⟩
  refine ⟨c.W, hcW, hxc, toTensorSheafSection V.toRingedSpace _ _ (op (c.W : V.Opens))
    (mω ⊗ₜ y), ?_, ?_⟩
  · have h0 : (d 0).app c.W mω = 0 :=
      Subtype.ext ((hdR 0 c.W mω).trans ((congrArg (chartD f D c 0) hmω).trans hdω))
    exact (twistBy_map_toTensorSheafSection (suppTwist D) (d 0) c.W mω y).trans
      ((congrArg (fun a => toTensorSheafSection V.toRingedSpace _ (suppTwist D)
        (op (c.W : V.Opens)) (a ⊗ₜ y)) h0).trans (toTensorSheafSection_zero_tmul _ _ _ _))
  · have hz' : ((Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj
        (logModule n f D hD D.suppIdeal 0)).presheaf.map (homOfLE hcW).op z = zr := hzr.symm
    rw [hz']
    refine Subtype.ext (hzω.trans ?_)
    rw [← hmω]
    exact (twistFrobLogIncl_app_tmul f D hD J hJ hU hcomp p hV d d' hdR' hdR c y hy 0 mω).symm

include hdR hdR' in
/-- A cycle of `F_*Ω^{q+1}(log D)(-D)` is locally the image of a cycle of
`F_*Ω^{q+1}(log D) ⊗ I_D` up to a boundary. -/
theorem exists_twistFrob_cycle_succ [Stacks.Divisors.IsEffectiveCartierDivisor D.suppIdeal]
    (q : ℕ) (W : V.Opens) (z : Γ((Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj
      (logModule n f D hD D.suppIdeal (q + 1)), W))
    (hz : (d' (q + 1)).app W z = 0) {x : V} (hx : x ∈ W) :
    ∃ (W' : V.Opens) (h : W' ≤ W), x ∈ W' ∧
      ∃ (w : Γ((twistBy (suppTwist D)).obj ((Scheme.Modules.pushforward
          (absoluteFrobenius V p hV)).obj (logModule n f D hD ⊤ (q + 1))), W'))
        (y' : Γ((Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj
          (logModule n f D hD D.suppIdeal q), W')),
        ((twistBy (suppTwist D)).map (d (q + 1))).app W' w = 0 ∧
        ((Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj
          (logModule n f D hD D.suppIdeal (q + 1))).presheaf.map (homOfLE h).op z =
          (twistFrobLogIncl f D hD J hJ hU hcomp p hV (q + 1)).app W' w + (d' q).app W' y' := by
  obtain ⟨c, hcW, hxc, hideal⟩ := exists_weakChart_suppIdeal_eq f D J hJ hU hcomp hx
  obtain ⟨y, hy⟩ := (Stacks.Divisors.mem_ideal_iff_exists_idealSheafSection D.suppIdeal c.W _).1
    (by rw [hideal]; exact Ideal.mem_span_singleton_self _)
  obtain ⟨-, G1, -, -, -⟩ := twistedLogForms_chart f D hD hcomp p hV c
  obtain ⟨zr, hzr⟩ : ∃ zr : Γ(logModule n f D hD D.suppIdeal (q + 1), c.W),
      zr = (logModule n f D hD D.suppIdeal (q + 1)).presheaf.map (homOfLE hcW).op z := ⟨_, rfl⟩
  have e2 : (d' (q + 1)).app c.W zr = 0 := by
    rw [hzr]
    exact (modules_hom_app_map (d' (q + 1)) hcW z).trans (by rw [hz, map_zero])
  have hdz₀ : chartD f D c (q + 1) zr.1 = 0 := by
    have e1 := hdR' (q + 1) c.W zr
    rw [e2] at e1
    exact e1.symm.trans rfl
  obtain ⟨y₁, hy₁, ω, hω, hzω, hdω⟩ := G1 q zr.1 zr.2 hdz₀
  obtain ⟨mω, hmω⟩ : ∃ mω : Γ(logModule n f D hD ⊤ (q + 1), c.W), mω.1 = ω := ⟨⟨ω, hω⟩, rfl⟩
  obtain ⟨my, hmy⟩ : ∃ my : Γ(logModule n f D hD D.suppIdeal q, c.W), my.1 = y₁ :=
    ⟨⟨y₁, hy₁⟩, rfl⟩
  refine ⟨c.W, hcW, hxc, toTensorSheafSection V.toRingedSpace _ _ (op (c.W : V.Opens))
    (mω ⊗ₜ y), my, ?_, ?_⟩
  · have h0 : (d (q + 1)).app c.W mω = 0 :=
      Subtype.ext ((hdR (q + 1) c.W mω).trans ((congrArg (chartD f D c (q + 1)) hmω).trans hdω))
    exact (twistBy_map_toTensorSheafSection (suppTwist D) (d (q + 1)) c.W mω y).trans
      ((congrArg (fun a => toTensorSheafSection V.toRingedSpace _ (suppTwist D)
        (op (c.W : V.Opens)) (a ⊗ₜ y)) h0).trans (toTensorSheafSection_zero_tmul _ _ _ _))
  · have hz' : ((Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj
        (logModule n f D hD D.suppIdeal (q + 1))).presheaf.map (homOfLE hcW).op z = zr := hzr.symm
    rw [hz']
    refine Subtype.ext (hzω.trans ?_)
    rw [← hmω, ← hmy]
    exact congrArg₂ (· + ·)
      (twistFrobLogIncl_app_tmul f D hD J hJ hU hcomp p hV d d' hdR' hdR c y hy (q + 1) mω).symm
      (hdR' q c.W my).symm

include hdR hdR' in
/-- A section of `F_*Ω⁰(log D) ⊗ I_D` killed by the comparison vanishes locally. -/
theorem exists_twistFrob_eq_zero [Stacks.Divisors.IsEffectiveCartierDivisor D.suppIdeal]
    (W : V.Opens) (w : Γ((twistBy (suppTwist D)).obj ((Scheme.Modules.pushforward
      (absoluteFrobenius V p hV)).obj (logModule n f D hD ⊤ 0)), W))
    (hψ : (twistFrobLogIncl f D hD J hJ hU hcomp p hV 0).app W w = 0) {x : V} (hx : x ∈ W) :
    ∃ (W' : V.Opens) (h : W' ≤ W), x ∈ W' ∧
      ((twistBy (suppTwist D)).obj ((Scheme.Modules.pushforward
        (absoluteFrobenius V p hV)).obj (logModule n f D hD ⊤ 0))).presheaf.map (homOfLE h).op w = 0 := by
  obtain ⟨c, hcW, yI, hxc, hy, m, hm⟩ := exists_twist_restrict_eq f D J hJ hU hcomp _ w hx
  obtain ⟨-, -, -, G3, -⟩ := twistedLogForms_chart f D hD hcomp p hV c
  have h0 : (twistFrobLogIncl f D hD J hJ hU hcomp p hV 0).app c.W
      (toTensorSheafSection V.toRingedSpace _ _ (op (c.W : V.Opens)) (m ⊗ₜ yI)) = 0 := by
    rw [← hm, modules_hom_app_map, hψ, map_zero]
  have h1 : chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p) m.1 = 0 :=
    (twistFrobLogIncl_app_tmul f D hD J hJ hU hcomp p hV d d' hdR' hdR c yI hy 0 m).symm.trans
      (congrArg Subtype.val h0)
  have hm0 : m = 0 := Subtype.ext (G3 0 _ h1)
  refine ⟨c.W, hcW, hxc, ?_⟩
  rw [hm, hm0]
  exact toTensorSheafSection_zero_tmul _ _ _ _

include hdR hdR' in
/-- A cycle of `F_*Ω^{q+1}(log D) ⊗ I_D` whose image is a boundary is locally a boundary. -/
theorem exists_twistFrob_eq_d [Stacks.Divisors.IsEffectiveCartierDivisor D.suppIdeal]
    (q : ℕ) (W : V.Opens) (w : Γ((twistBy (suppTwist D)).obj ((Scheme.Modules.pushforward
      (absoluteFrobenius V p hV)).obj (logModule n f D hD ⊤ (q + 1))), W))
    (y' : Γ((Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj
      (logModule n f D hD D.suppIdeal q), W))
    (hψ : (twistFrobLogIncl f D hD J hJ hU hcomp p hV (q + 1)).app W w = (d' q).app W y')
    {x : V} (hx : x ∈ W) :
    ∃ (W' : V.Opens) (h : W' ≤ W), x ∈ W' ∧
      ∃ v : Γ((twistBy (suppTwist D)).obj ((Scheme.Modules.pushforward
          (absoluteFrobenius V p hV)).obj (logModule n f D hD ⊤ q)), W'),
        ((twistBy (suppTwist D)).obj ((Scheme.Modules.pushforward
          (absoluteFrobenius V p hV)).obj (logModule n f D hD ⊤ (q + 1)))).presheaf.map
            (homOfLE h).op w = ((twistBy (suppTwist D)).map (d q)).app W' v := by
  obtain ⟨c, hcW, yI, hxc, hy, m, hm⟩ := exists_twist_restrict_eq f D J hJ hU hcomp _ w hx
  obtain ⟨-, -, G2, -, -⟩ := twistedLogForms_chart f D hD hcomp p hV c
  obtain ⟨yr, hyr⟩ : ∃ yr : Γ(logModule n f D hD D.suppIdeal q, c.W),
      yr = (logModule n f D hD D.suppIdeal q).presheaf.map (homOfLE hcW).op y' := ⟨_, rfl⟩
  have h0 : (twistFrobLogIncl f D hD J hJ hU hcomp p hV (q + 1)).app c.W
      (toTensorSheafSection V.toRingedSpace _ _ (op (c.W : V.Opens)) (m ⊗ₜ yI)) =
      (d' q).app c.W yr := by
    rw [← hm, hyr, modules_hom_app_map, hψ, ← modules_hom_app_map]
    rfl
  have h1 : chartSmul f D c ((∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ^ p) m.1 =
      chartD f D c q yr.1 :=
    (twistFrobLogIncl_app_tmul f D hD J hJ hU hcomp p hV d d' hdR' hdR c yI hy (q + 1) m).symm.trans
      ((congrArg Subtype.val h0).trans (hdR' q c.W yr))
  obtain ⟨η, hη, hdη⟩ := G2 q yr.1 m.1 yr.2 m.2 h1.symm
  obtain ⟨mη, hmη⟩ : ∃ mη : Γ(logModule n f D hD ⊤ q, c.W), mη.1 = η := ⟨⟨η, hη⟩, rfl⟩
  refine ⟨c.W, hcW, hxc, toTensorSheafSection V.toRingedSpace _ _ (op (c.W : V.Opens))
    (mη ⊗ₜ yI), ?_⟩
  have h2 : (d q).app c.W mη = m :=
    Subtype.ext ((hdR q c.W mη).trans ((congrArg (chartD f D c q) hmη).trans hdη))
  rw [hm]
  exact ((twistBy_map_toTensorSheafSection (suppTwist D) (d q) c.W mη yI).trans
    (congrArg (fun a => toTensorSheafSection V.toRingedSpace _ (suppTwist D)
      (op (c.W : V.Opens)) (a ⊗ₜ yI)) h2)).symm

include hdR hdR' in
/-- **The comparison of complexes** `F_*Ω^•(log D) ⊗ I_D ⟶ F_*Ω^•(log D)(-D)`. -/
noncomputable def twistFrobLogComplexHom
    [Stacks.Divisors.IsEffectiveCartierDivisor D.suppIdeal]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0} (suppTwist D)] :
    ((twistBy (suppTwist D)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (CochainComplex.of _ d hd) ⟶ CochainComplex.of _ d' hd' where
  f q := twistFrobLogIncl f D hD J hJ hU hcomp p hV q
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    simp only [Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d]
    exact (twistFrobLogIncl_comm f D hD J hJ hU hcomp p hV d d' hdR' hdR i).symm

include hd hd' in
/-- **The comparison of complexes is a quasi-isomorphism**: on a weak chart with boundary
coordinates `t₁, …, t_r`, it is the inclusion of `h^p Ω^•(log D)` into `h Ω^•(log D)`,
`h = t₁ ⋯ t_r`, which the Euler homotopy shows is a quasi-isomorphism. -/
theorem quasiIso_twistFrobLogComplexHom
    [Stacks.Divisors.IsEffectiveCartierDivisor D.suppIdeal]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0} (suppTwist D)] :
    QuasiIso (twistFrobLogComplexHom f D hD J hJ hU hcomp p hV d hd d' hd' hdR' hdR) := by
  refine ⟨fun q => ?_⟩
  rw [quasiIsoAt_iff_isIso_homologyMap]
  refine isIso_homologyMap_of_local _ q ?_ ?_
  · intro W z hz x hx
    simp only [CochainComplex.of_d] at hz
    cases q with
    | zero =>
      obtain ⟨W', h, hx', w, hw, he⟩ :=
        exists_twistFrob_cycle_zero f D hD J hJ hU hcomp p hV d d' hdR' hdR W z hz hx
      refine ⟨W', h, hx', w, 0, ?_, ?_⟩
      · simp only [Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d]
        exact hw
      · rw [map_zero, add_zero]
        exact he
    | succ q =>
      rw [CochainComplex.prev_nat_succ]
      obtain ⟨W', h, hx', w, y', hw, he⟩ :=
        exists_twistFrob_cycle_succ f D hD J hJ hU hcomp p hV d d' hdR' hdR q W z hz hx
      refine ⟨W', h, hx', w, y', ?_, ?_⟩
      · simp only [Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d]
        exact hw
      · simp only [CochainComplex.of_d]
        exact he
  · cases q with
    | zero =>
      intro W w y' hw hψ x hx
      have hY : (CochainComplex.of _ d' hd').d ((ComplexShape.up ℕ).prev 0) 0 = 0 :=
        (CochainComplex.of _ d' hd').shape _ _ (by simp [ComplexShape.up_Rel])
      have hψ0 : (twistFrobLogIncl f D hD J hJ hU hcomp p hV 0).app W w = 0 :=
        hψ.trans (by rw [hY]; rfl)
      obtain ⟨W', h, hx', hw0⟩ :=
        exists_twistFrob_eq_zero f D hD J hJ hU hcomp p hV d d' hdR' hdR W w hψ0 hx
      refine ⟨W', h, hx', 0, ?_⟩
      rw [map_zero]
      exact hw0
    | succ q =>
      rw [CochainComplex.prev_nat_succ]
      intro W w y' hw hψ x hx
      simp only [CochainComplex.of_d] at hψ
      obtain ⟨W', h, hx', v, hv⟩ :=
        exists_twistFrob_eq_d f D hD J hJ hU hcomp p hV d d' hdR' hdR q W w y' hψ hx
      refine ⟨W', h, hx', v, ?_⟩
      simp only [Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d]
      exact hv

end TwistedComparison

section TwistedSplitting2

open MMP.Mori.Divisor.LogSpreadingProof.G1

attribute [local instance] additive_twistBy preservesFiniteLimits_twistBy
  preservesFiniteColimits_twistBy

variable {k : Type} [Field k] [IsRegularRing (CommRingCat.of k)] {V : Scheme.{0}}
  (f : V ⟶ Spec (CommRingCat.of k)) {n : ℕ} [SmoothOfRelativeDimension n f]
  (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n f) (p : ℕ) [Fact p.Prime]
  (hV : IsInCharacteristic V p)

/-- **The Deligne–Illusie decomposition, twisted by the reduced boundary.** A decomposition
`⨁_q Ω^q(log D)[-q] ≅ F_*Ω^•(log D)` gives one of `F_*Ω^•(log D)(-D)`: tensoring by the
invertible ideal `𝓘` of `D` gives `⨁_q (Ω^q(log D) ⊗ 𝓘)[-q] ≅ F_*Ω^•(log D) ⊗ 𝓘`, and
`Ω^q(log D) ⊗ 𝓘 ≅ Ω^q(log D)(-D)`, while `F_*Ω^•(log D) ⊗ 𝓘 = F_*(𝓘^p Ω^•(log D))` is
quasi-isomorphic to `F_*(𝓘 Ω^•(log D))`. -/
theorem nonempty_twisted_decomposition [HasDerivedCategory.{0} V.Modules]
    {ι : Type} [Fintype ι] (J : ι → V.IdealSheafData)
    (hJ : ∀ T : Finset ι,
      SmoothOfRelativeDimension (n - T.card) ((⨆ j ∈ T, J j).subschemeι ≫ f) ∧
      (n < T.card → IsEmpty (⨆ j ∈ T, J j).subscheme))
    (hU : LU D = ((⨅ j, J j).support).compl)
    (hcomp : ∀ ξ : V, ξ ∈ (D.supp : Set V) → Order.coheight ξ = 1 →
      ∃ E ∈ D.support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ)
    (d : ∀ q : ℕ, (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n f D hD ⊤ q) ⟶
        (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n f D hD ⊤ (q + 1)))
    (hd : ∀ q, d q ≫ d (q + 1) = 0)
    (d' : ∀ q : ℕ, (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n f D hD D.suppIdeal q) ⟶
        (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n f D hD D.suppIdeal (q + 1)))
    (hd' : ∀ q, d' q ≫ d' (q + 1) = 0)
    (hdR' : ∀ (q : ℕ) (W : V.Opens) (x : Γ(G1.logModule n f D hD D.suppIdeal q, W)),
        (show ↥((G1.logModuleSubmodule n f D hD D.suppIdeal (q + 1)).obj (op W))
          from (d' q).app W x).1 =
        ((Scheme.Hom.deRhamComplex ((G1.LU D).ι ≫ f)).d q (q + 1)).val.app
          (op ((G1.LU D).ι ⁻¹ᵁ W))
          (show ↥((G1.logModuleSubmodule n f D hD D.suppIdeal q).obj (op W)) from x).1)
    (hdR : ∀ (q : ℕ) (W : V.Opens) (x : Γ(G1.logModule n f D hD ⊤ q, W)),
        (show ↥((G1.logModuleSubmodule n f D hD ⊤ (q + 1)).obj (op W))
          from (d q).app W x).1 =
        ((Scheme.Hom.deRhamComplex ((G1.LU D).ι ≫ f)).d q (q + 1)).val.app
          (op ((G1.LU D).ι ⁻¹ᵁ W))
          (show ↥((G1.logModuleSubmodule n f D hD ⊤ q).obj (op W)) from x).1)
    (Φ : Nonempty ((⨁ fun q : Fin (n + 1) =>
          (DerivedCategory.singleFunctor V.Modules (q : ℤ)).obj (G1.logModule n f D hD ⊤ q)) ≅
        DerivedCategory.Q.obj ((CochainComplex.of _ d hd).extend ComplexShape.embeddingUpNat))) :
    Nonempty ((⨁ fun q : Fin (n + 1) =>
          (DerivedCategory.singleFunctor V.Modules (q : ℤ)).obj
            (G1.logModule n f D hD D.suppIdeal q)) ≅
        DerivedCategory.Q.obj ((CochainComplex.of _ d' hd').extend ComplexShape.embeddingUpNat)) := by
  obtain ⟨Φ⟩ := Φ
  haveI hI : Stacks.Divisors.IsEffectiveCartierDivisor D.suppIdeal :=
    isEffectiveCartierDivisor_suppIdeal f D J hJ hU hcomp
  haveI hinv : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 (suppTwist D) := hI
  haveI h𝓘 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0} (suppTwist D) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (suppTwist D) 1
  obtain ⟨Φ₁⟩ := nonempty_iso_twistBy (suppTwist D) n (fun q => G1.logModule n f D hD ⊤ q) _ Φ
  haveI := fun q => isIso_twistLogIncl f D hD J hJ hU hcomp q
  haveI := quasiIso_twistFrobLogComplexHom f D hD J hJ hU hcomp p hV d hd d' hd' hdR' hdR
  haveI : QuasiIso (HomologicalComplex.extendMap
      (twistFrobLogComplexHom f D hD J hJ hU hcomp p hV d hd d' hd' hdR' hdR)
      ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).2 inferInstance
  exact ⟨(Limits.biproduct.mapIso fun q : Fin (n + 1) =>
    (DerivedCategory.singleFunctor V.Modules (q : ℤ)).mapIso
      (asIso (twistLogIncl f D hD J hJ hU hcomp q))).symm ≪≫ Φ₁ ≪≫
      asIso (DerivedCategory.Q.map ((mapHomologicalComplexExtendIso (twistBy (suppTwist D))
        (CochainComplex.of _ d hd) ComplexShape.embeddingUpNat).hom ≫
        HomologicalComplex.extendMap
          (twistFrobLogComplexHom f D hD J hJ hU hcomp p hV d hd d' hd' hdR' hdR)
          ComplexShape.embeddingUpNat))⟩

end TwistedSplitting2

/-- **The complement of a pulled-back divisor.** If the support of `Ds` on `X'` is the preimage
under `a` of the support of `𝒟`, the complement of `Ds` is the complement of the common zero locus
of the pulled-back ideals of the components of `𝒟`. -/
theorem LU_eq_compl_support_iInf_comap {X X' : Scheme.{0}} (a : X' ⟶ X)
    (𝒟 : MMP.Mori.Divisor X) (Ds : MMP.Mori.Divisor X')
    (hsupp : a.base ⁻¹' (𝒟.supp : Set X) = (Ds.supp : Set X')) :
    G1.LU Ds = ((⨅ j : 𝒟.support,
      (j.1 : MMP.Mori.PrimeDivisor X).idealSheaf.comap a).support).compl := by
  classical
  have hC : (⨅ j : 𝒟.support, (j.1 : MMP.Mori.PrimeDivisor X).idealSheaf.comap a).support =
      Ds.supp := by
    apply SetLike.ext'
    rw [support_iInf_of_finite, ← Finset.sup_univ_eq_iSup,
      TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_eq_iSup, ← hsupp]
    ext x
    simp only [Set.iSup_eq_iUnion, Function.comp_apply, Set.mem_iUnion, Finset.mem_univ,
      exists_true_left, Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
      Set.mem_preimage, SetLike.mem_coe, MMP.Mori.DivisorWithCoeffs.mem_supp_iff]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j.1, Finsupp.mem_support_iff.mp j.2, hj⟩
    · rintro ⟨E, hE, hx⟩
      exact ⟨⟨E, Finsupp.mem_support_iff.mpr hE⟩, hx⟩
  change Ds.supp.compl = _
  rw [hC]

/-- **The Deligne–Illusie data of the fibre.** The fibre `(𝒳_s, 𝒟_s)` over a point with finite
residue field `κ(s)` of characteristic `p > n`, at which the residue map `ρ` lifts to
`φ : R → W₂(κ(s))`, is the closed fibre of `𝒳 ×_R W₂(κ(s))`, lifted with the pulled-back
components of `𝒟`. Its logarithmic forms `Ω^q(log 𝒟_s)` embed in the forms off `𝒟_s`
(`exists_logForms_embedding`), and the differential `d` of `F_*Ω^•(log 𝒟_s)` is carried to the
de Rham differential. -/
noncomputable def fibreFrobeniusSplittingData (n : ℕ) {R : Type} [CommRing R]
    {𝒳 : Scheme.{0}} (g : 𝒳 ⟶ Spec (CommRingCat.of R)) [SmoothOfRelativeDimension n g]
    (hg : IsProjective g) (𝒟 : MMP.Mori.Divisor 𝒳) (h𝒟 : 𝒟.IsRelativeSNC n g)
    (s : Spec (CommRingCat.of R)) (p : ℕ) [Fact p.Prime] (hnp : n < p)
    [Finite ((Spec (CommRingCat.of R)).residueField s)]
    [CharP ((Spec (CommRingCat.of R)).residueField s) p]
    (ρ : R →+* (Spec (CommRingCat.of R)).residueField s)
    (hρ : Spec.map (CommRingCat.ofHom ρ) = (Spec (CommRingCat.of R)).fromSpecResidueField s)
    (φ : R →+* TruncatedWittVector p 2 ((Spec (CommRingCat.of R)).residueField s))
    (hφ : ∀ r, (φ r).coeff 0 = ρ r)
    [SmoothOfRelativeDimension n
      (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))]
    (Ds : MMP.Mori.Divisor (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
    (hDs : Ds.IsRelativeSNC n (pullback.snd _ _))
    (hsupp : (pullback.fst g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base ⁻¹'
      (𝒟.supp : Set 𝒳) = (Ds.supp : Set _))
    [HasDerivedCategory.{0}
      (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules]
    (hV : IsInCharacteristic (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p)
    (d : ∀ q : ℕ, (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs ⊤ q) ⟶
        (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs ⊤ (q + 1)))
    (hd : ∀ q, d q ≫ d (q + 1) = 0)
    (hdR : ∀ (q : ℕ) (W : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Opens)
        (x : Γ(G1.logModule n (pullback.snd _ _) Ds hDs ⊤ q, W)),
        (show ↥((G1.logModuleSubmodule n (pullback.snd _ _) Ds hDs ⊤ (q + 1)).obj (op W))
          from (d q).app W x).1 =
        ((Scheme.Hom.deRhamComplex ((G1.LU Ds).ι ≫ pullback.snd _ _)).d q (q + 1)).val.app
          (op ((G1.LU Ds).ι ⁻¹ᵁ W))
          (show ↥((G1.logModuleSubmodule n (pullback.snd _ _) Ds hDs ⊤ q).obj (op W))
            from x).1) :
    haveI : IsProper g := hg.isProper
    MMP.DeRham.FrobeniusSplittingData p ((Spec (CommRingCat.of R)).residueField s) n
      (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) 𝒟.support :=
  haveI : IsProper g := hg.isProper
  -- the lift over `W₂(κ(s))`
  let π := HodgeSpreadingOut.wittTwoToField p ((Spec (CommRingCat.of R)).residueField s)
  let 𝒱 := pullback g (Spec.map (CommRingCat.ofHom φ))
  have hρπ : Spec.map (CommRingCat.ofHom π) ≫ Spec.map (CommRingCat.ofHom φ) =
      (Spec (CommRingCat.of R)).fromSpecResidueField s := by
    rw [← hρ, ← Spec.map_comp]
    congr 1
    ext r
    exact hφ r
  let i : pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s) ⟶ 𝒱 :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom π))
      (pullback.condition.trans ((congrArg (pullback.snd _ _ ≫ ·) hρπ.symm).trans
        (Category.assoc _ _ _).symm))
  -- the components
  let I : 𝒟.support → 𝒱.IdealSheafData := fun j =>
    (j.1 : MMP.Mori.PrimeDivisor 𝒳).idealSheaf.comap (pullback.fst _ _)
  let J : 𝒟.support →
      (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).IdealSheafData :=
    fun j => (j.1 : MMP.Mori.PrimeDivisor 𝒳).idealSheaf.comap
      (pullback.fst g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
  have hJI : ∀ j, J j = (I j).comap i := fun j => by
    change _ = ((j.1 : MMP.Mori.PrimeDivisor 𝒳).idealSheaf.comap (pullback.fst _ _)).comap i
    rw [← Scheme.IdealSheafData.comap_comp, pullback.lift_fst]
  have hJ : ∀ T : Finset 𝒟.support,
      SmoothOfRelativeDimension (n - T.card) ((⨆ j ∈ T, J j).subschemeι ≫ pullback.snd _ _) ∧
      (n < T.card → IsEmpty (⨆ j ∈ T, J j).subscheme) := fun T =>
    smoothOfRelativeDimension_iSup_comap_of_isPullback (IsPullback.of_hasPullback _ _) _ T _ _
      (smoothOfRelativeDimension_iSup_idealSheaf n g 𝒟 h𝒟 T)
  have hU : G1.LU Ds = ((⨅ j, J j).support).compl :=
    LU_eq_compl_support_iInf_comap _ 𝒟 Ds hsupp
  have he := exists_logForms_embedding (k := (Spec (CommRingCat.of R)).residueField s)
    (pullback.snd _ _) Ds hDs J hJ hU (exists_mem_support_genericPoint_eq Ds)
  { hpn := hnp
    hV := hV
    J := J
    hJ := hJ
    𝒱 := 𝒱
    g := pullback.snd _ _
    I := I
    π := π
    hπ := fun _ => rfl
    i := i
    hi := by
      refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
      rw [pullback.lift_fst]
      exact hρπ ▸ IsPullback.of_hasPullback _ _
    hIJ := fun j =>
      ⟨_, (isPullback_of_isClosedImmersion (J j).subschemeι (I j).subschemeι
        (Scheme.IdealSheafData.subschemeMap _ _ i
          (by rw [hJI]; exact Scheme.IdealSheafData.le_map_comap (I j) i))
        i (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm
        (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
          hJI])).flip⟩
    hI := fun T =>
      smoothOfRelativeDimension_iSup_comap_of_isPullback (IsPullback.of_hasPullback _ _) _ T _ _
        (smoothOfRelativeDimension_iSup_idealSheaf n g 𝒟 h𝒟 T)
    U := G1.LU Ds
    hU := hU
    K := fun q => G1.logModule n (pullback.snd _ _) Ds hDs ⊤ q
    e := he.choose
    he_inj := he.choose_spec.2.1
    he_smul := he.choose_spec.2.2.1
    he_res := he.choose_spec.2.2.2.1
    he_range := he.choose_spec.2.2.2.2
    d := d
    hd := hd
    he_d := fun q W x => by
      refine (he.choose_spec.1 (q + 1) _ ((d q).app W x)).trans ?_
      rw [he.choose_spec.1]
      exact (congrArg (ambientFormsEquiv _ (G1.LU Ds) ((q + 1 : ℕ) : ℤ) _) (hdR q W x)).trans
        (ambientFormsEquiv_d _ (G1.LU Ds) q _ _) }

theorem nonempty_logDeRham_decomposition_fibre (n : ℕ) {R : Type} [CommRing R]
    {𝒳 : Scheme.{0}} (g : 𝒳 ⟶ Spec (CommRingCat.of R)) [SmoothOfRelativeDimension n g]
    (hg : IsProjective g) (𝒟 : MMP.Mori.Divisor 𝒳) (h𝒟 : 𝒟.IsRelativeSNC n g)
    (s : Spec (CommRingCat.of R)) (p : ℕ) [Fact p.Prime] (hnp : n < p)
    [Finite ((Spec (CommRingCat.of R)).residueField s)]
    [CharP ((Spec (CommRingCat.of R)).residueField s) p]
    (ρ : R →+* (Spec (CommRingCat.of R)).residueField s)
    (hρ : Spec.map (CommRingCat.ofHom ρ) = (Spec (CommRingCat.of R)).fromSpecResidueField s)
    (φ : R →+* TruncatedWittVector p 2 ((Spec (CommRingCat.of R)).residueField s))
    (hφ : ∀ r, (φ r).coeff 0 = ρ r)
    [SmoothOfRelativeDimension n
      (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))]
    (Ds : MMP.Mori.Divisor (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
    (hDs : Ds.IsRelativeSNC n (pullback.snd _ _))
    (hsupp : (pullback.fst g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base ⁻¹'
      (𝒟.supp : Set 𝒳) = (Ds.supp : Set _))
    [HasDerivedCategory.{0}
      (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules]
    (hV : IsInCharacteristic (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p)
    (d : ∀ q : ℕ, (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs ⊤ q) ⟶
        (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs ⊤ (q + 1)))
    (hd : ∀ q, d q ≫ d (q + 1) = 0)
    (hdR : ∀ (q : ℕ) (W : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Opens)
        (x : Γ(G1.logModule n (pullback.snd _ _) Ds hDs ⊤ q, W)),
        (show ↥((G1.logModuleSubmodule n (pullback.snd _ _) Ds hDs ⊤ (q + 1)).obj (op W))
          from (d q).app W x).1 =
        ((Scheme.Hom.deRhamComplex ((G1.LU Ds).ι ≫ pullback.snd _ _)).d q (q + 1)).val.app
          (op ((G1.LU Ds).ι ⁻¹ᵁ W))
          (show ↥((G1.logModuleSubmodule n (pullback.snd _ _) Ds hDs ⊤ q).obj (op W))
            from x).1) :
    Nonempty ((⨁ fun q : Fin (n + 1) =>
          (DerivedCategory.singleFunctor
            (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules (q : ℤ)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs ⊤ q)) ≅
        DerivedCategory.Q.obj ((CochainComplex.of _ d hd).extend ComplexShape.embeddingUpNat)) :=
  haveI : IsProper g := hg.isProper
  (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR).nonempty_iso_directSum_singleFunctor

/-- **The Deligne–Illusie decomposition on the fibre.** On the fibre `(𝒳_s, 𝒟_s)` over a point
with finite residue field `κ(s)` of characteristic `p > n` at which the residue map lifts to
`W₂(κ(s))`, the Frobenius pushforward `F_*Ω^•(log 𝒟_s)` of the logarithmic de Rham complex,
whose differential is the de Rham differential, is isomorphic in the derived category of
`𝒪`-modules to `⨁_{q ≤ n} Ω^q(log 𝒟_s)[-q]`. -/
theorem exists_frobenius_logDeRham_decomposition_untwisted (n : ℕ) {R : Type} [CommRing R]
    {𝒳 : Scheme.{0}} (g : 𝒳 ⟶ Spec (CommRingCat.of R)) [SmoothOfRelativeDimension n g]
    (hg : IsProjective g) (𝒟 : MMP.Mori.Divisor 𝒳) (h𝒟 : 𝒟.IsRelativeSNC n g)
    (s : Spec (CommRingCat.of R)) (p : ℕ) [Fact p.Prime] (hnp : n < p)
    [Finite ((Spec (CommRingCat.of R)).residueField s)]
    [CharP ((Spec (CommRingCat.of R)).residueField s) p]
    (ρ : R →+* (Spec (CommRingCat.of R)).residueField s)
    (hρ : Spec.map (CommRingCat.ofHom ρ) = (Spec (CommRingCat.of R)).fromSpecResidueField s)
    (φ : R →+* TruncatedWittVector p 2 ((Spec (CommRingCat.of R)).residueField s))
    (hφ : ∀ r, (φ r).coeff 0 = ρ r)
    [SmoothOfRelativeDimension n
      (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))]
    (Ds : MMP.Mori.Divisor (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
    (hDs : Ds.IsRelativeSNC n (pullback.snd _ _))
    (hsupp : (pullback.fst g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base ⁻¹'
      (𝒟.supp : Set 𝒳) = (Ds.supp : Set _))
    [HasDerivedCategory.{0} (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules] :
    ∃ (hV : IsInCharacteristic (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p)
      (d : ∀ q : ℕ, (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs (bif false then Ds.suppIdeal else ⊤) q) ⟶
        (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs (bif false then Ds.suppIdeal else ⊤) (q + 1)))
      (hd : ∀ q, d q ≫ d (q + 1) = 0),
      (∀ (q : ℕ) (W : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Opens)
        (x : Γ(G1.logModule n (pullback.snd _ _) Ds hDs (bif false then Ds.suppIdeal else ⊤) q, W)),
        (show ↥((G1.logModuleSubmodule n (pullback.snd _ _) Ds hDs (bif false then Ds.suppIdeal else ⊤) (q + 1)).obj (op W))
          from (d q).app W x).1 =
        ((Scheme.Hom.deRhamComplex ((G1.LU Ds).ι ≫ pullback.snd _ _)).d q (q + 1)).val.app
          (op ((G1.LU Ds).ι ⁻¹ᵁ W))
          (show ↥((G1.logModuleSubmodule n (pullback.snd _ _) Ds hDs (bif false then Ds.suppIdeal else ⊤) q).obj (op W))
            from x).1) ∧
      Nonempty ((⨁ fun q : Fin (n + 1) =>
          (DerivedCategory.singleFunctor
            (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules (q : ℤ)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs (bif false then Ds.suppIdeal else ⊤) q)) ≅
        DerivedCategory.Q.obj ((CochainComplex.of _ d hd).extend ComplexShape.embeddingUpNat)) := by
  have hV := isInCharacteristic_pullback_fromSpecResidueField g s p
  obtain ⟨d, hd, hdR⟩ := exists_frobeniusLinear_logDeRham_d
    (k := (Spec (CommRingCat.of R)).residueField s) n (pullback.snd _ _) Ds hDs false p hV
  exact ⟨hV, d, hd, hdR, nonempty_logDeRham_decomposition_fibre n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds
    hDs hsupp hV d hd hdR⟩

/-- **The components of the divisor on the fibre** form a simple normal crossing family of ideal
sheaves whose common zero locus is the support of `𝒟_s`. -/
theorem exists_idealSheafFamily_fibre (n : ℕ) {R : Type} [CommRing R]
    {𝒳 : Scheme.{0}} (g : 𝒳 ⟶ Spec (CommRingCat.of R)) [SmoothOfRelativeDimension n g]
    (𝒟 : MMP.Mori.Divisor 𝒳) (h𝒟 : 𝒟.IsRelativeSNC n g) (s : Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension n
      (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))]
    (Ds : MMP.Mori.Divisor (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
    (hsupp : (pullback.fst g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base ⁻¹'
      (𝒟.supp : Set 𝒳) = (Ds.supp : Set _)) :
    ∃ J : 𝒟.support → (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).IdealSheafData,
      (∀ T : Finset 𝒟.support,
        SmoothOfRelativeDimension (n - T.card) ((⨆ j ∈ T, J j).subschemeι ≫ pullback.snd _ _) ∧
        (n < T.card → IsEmpty (⨆ j ∈ T, J j).subscheme)) ∧
      G1.LU Ds = ((⨅ j, J j).support).compl := by
  classical
  let J : 𝒟.support → (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).IdealSheafData :=
    fun j => (j.1 : MMP.Mori.PrimeDivisor 𝒳).idealSheaf.comap
      (pullback.fst g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
  refine ⟨J, fun T => smoothOfRelativeDimension_iSup_comap_of_isPullback
    (IsPullback.of_hasPullback _ _) _ T _ _ (smoothOfRelativeDimension_iSup_idealSheaf n g 𝒟 h𝒟 T),
    LU_eq_compl_support_iInf_comap _ 𝒟 Ds hsupp⟩

/-- **The Deligne–Illusie decomposition on the fibre, twisted by `-𝒟_s`.** In the situation of
`exists_frobenius_logDeRham_decomposition_untwisted`, the same holds for
`F_*Ω^•(log 𝒟_s)(-𝒟_s)` and `⨁_{q ≤ n} Ω^q(log 𝒟_s)(-𝒟_s)[-q]`. -/
theorem exists_frobenius_logDeRham_decomposition_twisted (n : ℕ) {R : Type} [CommRing R]
    {𝒳 : Scheme.{0}} (g : 𝒳 ⟶ Spec (CommRingCat.of R)) [SmoothOfRelativeDimension n g]
    (hg : IsProjective g) (𝒟 : MMP.Mori.Divisor 𝒳) (h𝒟 : 𝒟.IsRelativeSNC n g)
    (s : Spec (CommRingCat.of R)) (p : ℕ) [Fact p.Prime] (hnp : n < p)
    [Finite ((Spec (CommRingCat.of R)).residueField s)]
    [CharP ((Spec (CommRingCat.of R)).residueField s) p]
    (ρ : R →+* (Spec (CommRingCat.of R)).residueField s)
    (hρ : Spec.map (CommRingCat.ofHom ρ) = (Spec (CommRingCat.of R)).fromSpecResidueField s)
    (φ : R →+* TruncatedWittVector p 2 ((Spec (CommRingCat.of R)).residueField s))
    (hφ : ∀ r, (φ r).coeff 0 = ρ r)
    [SmoothOfRelativeDimension n
      (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))]
    (Ds : MMP.Mori.Divisor (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
    (hDs : Ds.IsRelativeSNC n (pullback.snd _ _))
    (hsupp : (pullback.fst g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base ⁻¹'
      (𝒟.supp : Set 𝒳) = (Ds.supp : Set _))
    [HasDerivedCategory.{0} (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules] :
    ∃ (hV : IsInCharacteristic (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p)
      (d : ∀ q : ℕ, (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs (bif true then Ds.suppIdeal else ⊤) q) ⟶
        (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs (bif true then Ds.suppIdeal else ⊤) (q + 1)))
      (hd : ∀ q, d q ≫ d (q + 1) = 0),
      (∀ (q : ℕ) (W : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Opens)
        (x : Γ(G1.logModule n (pullback.snd _ _) Ds hDs (bif true then Ds.suppIdeal else ⊤) q, W)),
        (show ↥((G1.logModuleSubmodule n (pullback.snd _ _) Ds hDs (bif true then Ds.suppIdeal else ⊤) (q + 1)).obj (op W))
          from (d q).app W x).1 =
        ((Scheme.Hom.deRhamComplex ((G1.LU Ds).ι ≫ pullback.snd _ _)).d q (q + 1)).val.app
          (op ((G1.LU Ds).ι ⁻¹ᵁ W))
          (show ↥((G1.logModuleSubmodule n (pullback.snd _ _) Ds hDs (bif true then Ds.suppIdeal else ⊤) q).obj (op W))
            from x).1) ∧
      Nonempty ((⨁ fun q : Fin (n + 1) =>
          (DerivedCategory.singleFunctor
            (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules (q : ℤ)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs (bif true then Ds.suppIdeal else ⊤) q)) ≅
        DerivedCategory.Q.obj ((CochainComplex.of _ d hd).extend ComplexShape.embeddingUpNat)) := by
  have hV := isInCharacteristic_pullback_fromSpecResidueField g s p
  obtain ⟨d, hd, hdR⟩ := exists_frobeniusLinear_logDeRham_d
    (k := (Spec (CommRingCat.of R)).residueField s) n (pullback.snd _ _) Ds hDs false p hV
  obtain ⟨d', hd', hdR'⟩ := exists_frobeniusLinear_logDeRham_d
    (k := (Spec (CommRingCat.of R)).residueField s) n (pullback.snd _ _) Ds hDs true p hV
  have Φ := nonempty_logDeRham_decomposition_fibre n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds
    hDs hsupp hV d hd hdR
  obtain ⟨J, hJ, hU⟩ := exists_idealSheafFamily_fibre n g 𝒟 h𝒟 s Ds hsupp
  exact ⟨hV, d', hd', hdR', nonempty_twisted_decomposition
    (k := (Spec (CommRingCat.of R)).residueField s)
    (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) Ds hDs p hV J hJ hU
    (exists_mem_support_genericPoint_eq Ds) d hd d' hd' hdR' hdR Φ⟩

theorem exists_frobenius_logDeRham_decomposition (n : ℕ) {R : Type} [CommRing R]
    {𝒳 : Scheme.{0}} (g : 𝒳 ⟶ Spec (CommRingCat.of R)) [SmoothOfRelativeDimension n g]
    (hg : IsProjective g) (𝒟 : MMP.Mori.Divisor 𝒳) (h𝒟 : 𝒟.IsRelativeSNC n g)
    (s : Spec (CommRingCat.of R)) (p : ℕ) [Fact p.Prime] (hnp : n < p)
    [Finite ((Spec (CommRingCat.of R)).residueField s)]
    [CharP ((Spec (CommRingCat.of R)).residueField s) p]
    (ρ : R →+* (Spec (CommRingCat.of R)).residueField s)
    (hρ : Spec.map (CommRingCat.ofHom ρ) = (Spec (CommRingCat.of R)).fromSpecResidueField s)
    (φ : R →+* TruncatedWittVector p 2 ((Spec (CommRingCat.of R)).residueField s))
    (hφ : ∀ r, (φ r).coeff 0 = ρ r)
    [SmoothOfRelativeDimension n
      (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))]
    (Ds : MMP.Mori.Divisor (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
    (hDs : Ds.IsRelativeSNC n (pullback.snd _ _))
    (hsupp : (pullback.fst g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base ⁻¹'
      (𝒟.supp : Set 𝒳) = (Ds.supp : Set _))
    [HasDerivedCategory.{0} (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules]
    (twist : Bool) :
    ∃ (hV : IsInCharacteristic (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p)
      (d : ∀ q : ℕ, (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs (bif twist then Ds.suppIdeal else ⊤) q) ⟶
        (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs (bif twist then Ds.suppIdeal else ⊤) (q + 1)))
      (hd : ∀ q, d q ≫ d (q + 1) = 0),
      (∀ (q : ℕ) (W : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Opens)
        (x : Γ(G1.logModule n (pullback.snd _ _) Ds hDs (bif twist then Ds.suppIdeal else ⊤) q, W)),
        (show ↥((G1.logModuleSubmodule n (pullback.snd _ _) Ds hDs (bif twist then Ds.suppIdeal else ⊤) (q + 1)).obj (op W))
          from (d q).app W x).1 =
        ((Scheme.Hom.deRhamComplex ((G1.LU Ds).ι ≫ pullback.snd _ _)).d q (q + 1)).val.app
          (op ((G1.LU Ds).ι ⁻¹ᵁ W))
          (show ↥((G1.logModuleSubmodule n (pullback.snd _ _) Ds hDs (bif twist then Ds.suppIdeal else ⊤) q).obj (op W))
            from x).1) ∧
      Nonempty ((⨁ fun q : Fin (n + 1) =>
          (DerivedCategory.singleFunctor
            (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules (q : ℤ)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs (bif twist then Ds.suppIdeal else ⊤) q)) ≅
        DerivedCategory.Q.obj ((CochainComplex.of _ d hd).extend ComplexShape.embeddingUpNat)) := by
  cases twist
  · exact exists_frobenius_logDeRham_decomposition_untwisted n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs
      hsupp
  · exact exists_frobenius_logDeRham_decomposition_twisted n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs
      hsupp

/-- **The Deligne–Illusie decomposition on the fibre, read in `π⁻¹𝒪`-modules.** On the fibre
`(𝒳_s, 𝒟_s)` over a point with finite residue field `κ(s)` of characteristic `p > n` carrying a
lift `R → W₂(κ(s))` of the residue map, the logarithmic de Rham complex `K` (with or without the
twist by `-𝒟_s`) has a Frobenius twist `L`, with the same hypercohomology dimensions, which is
isomorphic in the derived category to `⨁_{q ≤ n} K^q[-q]`. -/
theorem exists_frobeniusTwist_decomposition (n : ℕ) {R : Type} [CommRing R]
    {𝒳 : Scheme.{0}} (g : 𝒳 ⟶ Spec (CommRingCat.of R)) [SmoothOfRelativeDimension n g]
    (hg : IsProjective g) (𝒟 : MMP.Mori.Divisor 𝒳) (h𝒟 : 𝒟.IsRelativeSNC n g)
    (s : Spec (CommRingCat.of R)) (p : ℕ) [Fact p.Prime] (hnp : n < p)
    [Finite ((Spec (CommRingCat.of R)).residueField s)]
    [CharP ((Spec (CommRingCat.of R)).residueField s) p]
    (ρ : R →+* (Spec (CommRingCat.of R)).residueField s)
    (hρ : Spec.map (CommRingCat.ofHom ρ) = (Spec (CommRingCat.of R)).fromSpecResidueField s)
    (φ : R →+* TruncatedWittVector p 2 ((Spec (CommRingCat.of R)).residueField s))
    (hφ : ∀ r, (φ r).coeff 0 = ρ r)
    [SmoothOfRelativeDimension n
      (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))]
    (Ds : MMP.Mori.Divisor (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
    (hDs : Ds.IsRelativeSNC n (pullback.snd _ _))
    (hsupp : (pullback.fst g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base ⁻¹'
      (𝒟.supp : Set 𝒳) = (Ds.supp : Set _))
    (twist : Bool) :
    let K := relativeLogDeRhamComplex n (pullback.snd _ _) Ds hDs
      (bif twist then Ds.suppIdeal else ⊤)
    ∃ L : CochainComplex.Plus (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0}
          (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base).obj
            (Spec ((Spec (CommRingCat.of R)).residueField s)).sheaf))),
      (∀ j : ℤ, Module.finrank Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤)
          (Hc (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) L j) =
        Module.finrank Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤)
          (Hc (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
            ⟨K.extend ComplexShape.embeddingUpNat, 0,
              CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ j)) ∧
      Nonempty (DerivedCategory.Plus.Q.obj L ≅
        ⨁ fun q : Fin (n + 1) => (DerivedCategory.Plus.singleFunctor _ (q : ℤ)).obj
          (K.X q)) := by
  letI : HasDerivedCategory.{0}
      (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules :=
    Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian _
  obtain ⟨hV, d, hd, hdR, ⟨Φ⟩⟩ := exists_frobenius_logDeRham_decomposition n g hg 𝒟 h𝒟 s p hnp
    ρ hρ φ hφ Ds hDs hsupp twist
  letI : Fintype ((Spec (CommRingCat.of R)).residueField s) := Fintype.ofFinite _
  obtain ⟨m, -, hcard⟩ := FiniteField.card ((Spec (CommRingCat.of R)).residueField s) p
  have hκ : ∀ x : (Spec (CommRingCat.of R)).residueField s, x ^ p ^ (m : ℕ) = x := fun x => by
    rw [← hcard, FiniteField.pow_card]
  exact exists_hyp_eq_and_iso_of_frobenius_decomposition n (pullback.snd _ _) Ds hDs twist p
    (CharP.cast_eq_zero _ p) (fun a b => Subsingleton.elim a b) m.pos hκ hV d hd hdR Φ

/-- The sections of a zero sheaf of modules vanish. -/
theorem eq_zero_of_isZero {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}} {M : SheafOfModules.{0} R} (hM : IsZero M) {O : Cᵒᵖ}
    (y : M.val.obj O) : y = 0 := by
  have e := hM.eq_of_src (𝟙 M) 0
  have : (𝟙 M : M ⟶ M).val.app O y = (0 : M ⟶ M).val.app O y := by rw [e]
  exact this.trans rfl

/-- The logarithmic forms vanish above the relative dimension. -/
theorem isZero_relativeLogDeRhamComplex_X_of_lt (n : ℕ) {V S : Scheme.{0}}
    (f : V ⟶ S) [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor V)
    (hD : D.IsRelativeSNC n f) (I : V.IdealSheafData) {q : ℕ} (hq : n < q) :
    IsZero ((relativeLogDeRhamComplex n f D hD I).X q) := by
  haveI : SmoothOfRelativeDimension n (Scheme.Opens.ι (D.supp.compl : V.Opens) ≫ f) := by
    simpa using (inferInstance :
      SmoothOfRelativeDimension (0 + n) (Scheme.Opens.ι (D.supp.compl : V.Opens) ≫ f))
  have hZ := Scheme.Hom.isZero_relativeDifferentialForms_of_smoothOfRelativeDimension
    (Scheme.Opens.ι (D.supp.compl : V.Opens) ≫ f) n q hq
  rw [IsZero.iff_id_eq_zero]
  ext W x
  apply Subtype.ext
  exact (eq_zero_of_isZero hZ _).trans (eq_zero_of_isZero hZ _).symm

/-- On a proper scheme over a field, the cohomology of the logarithmic forms is finite
dimensional. -/
theorem finite_hyp_relativeLogDeRhamComplex_X (n : ℕ) {V : Scheme.{0}}
    {κ : CommRingCat.{0}} (hκ : IsField κ) (f : V ⟶ Spec κ) [SmoothOfRelativeDimension n f]
    [IsProper f] (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n f) (ε : Bool)
    (q : ℕ) (j : ℤ) :
    Module.Finite Γ(Spec κ, ⊤) (Hc f (single0 f
      ((relativeLogDeRhamComplex n f D hD (bif ε then D.suppIdeal else ⊤)).X q)) j) := by
  letI := hκ.toField
  haveI : IsLocallyNoetherian (Spec κ) := inferInstance
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian f
  have hK : ∀ k, ∃ M : V.Modules, M.IsCoherent ∧
      Nonempty ((hodgeCx n f D hD ε q).1.X k ≅
        (pushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).obj M) :=
    fun k => let ⟨M, _, h1, h2⟩ := exists_hodgeCx_X f hD ε q k; ⟨M, h1 inferInstance, h2⟩
  haveI := AlgebraicGeometry.DeRhamTypeComplex.moduleFinite_homology_derivedSections f
    (hodgeCx n f D hD ε q) hK j
  exact Module.Finite.equiv
    (nonempty_hcIsoHypercohomology f (hodgeCx n f D hD ε q) j).some.symm.toLinearEquiv

/-- **Degeneration on a fibre in characteristic `p`.** Let `g : 𝒳 ⟶ Spec R` be smooth projective
of relative dimension `n` with a relative SNC divisor `𝒟`, and `s` a point of `Spec R` whose
residue field `κ(s)` is finite of characteristic `p > n`, such that the residue map
`ρ : R → κ(s)` lifts to `φ : R → W₂(κ(s))`. Then on the fibre `(𝒳_s, 𝒟_s)` the logarithmic de
Rham dimension is the sum of the Hodge dimensions, with and without the twist by `-𝒟_s`. -/
theorem finrank_hyp_eq_sum_of_wittTwoLift (n : ℕ) {R : Type} [CommRing R]
    {𝒳 : Scheme.{0}} (g : 𝒳 ⟶ Spec (CommRingCat.of R)) [SmoothOfRelativeDimension n g]
    (hg : IsProjective g) (𝒟 : MMP.Mori.Divisor 𝒳) (h𝒟 : 𝒟.IsRelativeSNC n g)
    (s : Spec (CommRingCat.of R)) (p : ℕ) [Fact p.Prime] (hnp : n < p)
    [Finite ((Spec (CommRingCat.of R)).residueField s)]
    [CharP ((Spec (CommRingCat.of R)).residueField s) p]
    (ρ : R →+* (Spec (CommRingCat.of R)).residueField s)
    (hρ : Spec.map (CommRingCat.ofHom ρ) = (Spec (CommRingCat.of R)).fromSpecResidueField s)
    (φ : R →+* TruncatedWittVector p 2 ((Spec (CommRingCat.of R)).residueField s))
    (hφ : ∀ r, (φ r).coeff 0 = ρ r)
    [SmoothOfRelativeDimension n
      (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))]
    (Ds : MMP.Mori.Divisor (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
    (hDs : Ds.IsRelativeSNC n (pullback.snd _ _))
    (hsupp : (pullback.fst g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base ⁻¹'
      (𝒟.supp : Set 𝒳) = (Ds.supp : Set _))
    (twist : Bool) (k : ℕ) :
    let K := relativeLogDeRhamComplex n (pullback.snd _ _) Ds hDs
      (bif twist then Ds.suppIdeal else ⊤)
    Module.finrank Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤)
        (Hc (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
          ⟨K.extend ComplexShape.embeddingUpNat, 0,
            CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
      ∑ q ∈ Finset.range (k + 1),
        Module.finrank Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤)
          (Hc (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
            (single0 _ (K.X q)) ((k - q : ℕ) : ℤ)) := by
  intro K
  obtain ⟨L, hL, ⟨e⟩⟩ := exists_frobeniusTwist_decomposition n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ
    Ds hDs hsupp twist
  have hF : IsField Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤) :=
    MulEquiv.isField (Field.toIsField ((Spec (CommRingCat.of R)).residueField s))
      (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.toMulEquiv
  haveI : Nontrivial Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤) :=
    ⟨hF.exists_pair_ne⟩
  haveI : StrongRankCondition Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤) :=
    commRing_strongRankCondition _
  haveI : IsProper g := hg.isProper
  haveI : IsProper (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) :=
    inferInstance
  rw [← hL k, finrank_hyp_eq_sum_of_iso _ L (fun q : Fin (n + 1) => K.X q) e
    (fun q j => finite_hyp_relativeLogDeRhamComplex_X n
      (Field.toIsField ((Spec (CommRingCat.of R)).residueField s)) _ Ds hDs twist q j)
    (fun _ _ => by letI := hF.toField; exact Module.Free.of_divisionRing _ _) k]
  rw [Fin.sum_univ_eq_sum_range
    (fun q => Module.finrank Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤)
      (Hc (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
        (single0 _ (K.X q)) ((k : ℤ) - (q : ℤ)))) (n + 1)]
  rw [← Finset.sum_subset (Finset.range_mono (min_le_left (n + 1) (k + 1))) ?_,
    ← Finset.sum_subset (Finset.range_mono (min_le_right (n + 1) (k + 1))) ?_]
  · refine Finset.sum_congr rfl fun q hq => ?_
    simp only [Finset.mem_range, lt_min_iff] at hq
    rw [Nat.cast_sub (by omega : q ≤ k)]
  · intro q hq hq'
    simp only [Finset.mem_range] at hq hq'
    exact finrank_hyp_single0_eq_zero _ _ _
      (Or.inr (isZero_relativeLogDeRhamComplex_X_of_lt n _ Ds hDs _ (by omega)))
  · intro q hq hq'
    simp only [Finset.mem_range] at hq hq'
    exact finrank_hyp_single0_eq_zero _ _ _ (Or.inl (by omega))

/-- Truncated Witt vectors are functorial: a ring map `e : A → B` acts on coefficients. -/
noncomputable def truncatedWittMap {p : ℕ} [Fact p.Prime] {n : ℕ} {A B : Type*}
    [CommRing A] [CommRing B] (e : A →+* B) :
    TruncatedWittVector p n A →+* TruncatedWittVector p n B :=
  have hk : ∀ x : WittVector p A, TruncatedWittVector.mk p
      (fun i => e ((WittVector.truncate n x).coeff i)) =
        WittVector.truncate n (WittVector.map e x) := by
    intro x
    ext i
    simp [TruncatedWittVector.coeff_mk, WittVector.coeff_truncate, WittVector.map_coeff]
  { toFun := fun x => TruncatedWittVector.mk p fun i => e (x.coeff i)
    map_one' := by
      rw [← map_one (WittVector.truncate (p := p) (R := A) n), hk, map_one, map_one]
    map_mul' := by
      intro x y
      obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n A x
      obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p n A y
      simp only [← map_mul, hk]
    map_zero' := by
      rw [← map_zero (WittVector.truncate (p := p) (R := A) n), hk, map_zero, map_zero]
    map_add' := by
      intro x y
      obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n A x
      obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p n A y
      simp only [← map_add, hk] }

/-- A lift `R → W₂(R/𝔪)` of the residue map gives a lift `R → W₂(κ(𝔪))` of the residue map of
the point `𝔪` of `Spec R`. -/
theorem exists_wittTwoLift_residueField {R : Type} [CommRing R] (𝔪 : Ideal R)
    [h𝔪 : 𝔪.IsMaximal] (p : ℕ) [Fact p.Prime]
    (φ : R →+* TruncatedWittVector p 2 (R ⧸ 𝔪))
    (hφ : ∀ r : R, (φ r).coeff 0 = Ideal.Quotient.mk 𝔪 r) [Finite (R ⧸ 𝔪)] [CharP (R ⧸ 𝔪) p] :
    Finite ((Spec (CommRingCat.of R)).residueField ⟨𝔪, h𝔪.isPrime⟩) ∧
    CharP ((Spec (CommRingCat.of R)).residueField ⟨𝔪, h𝔪.isPrime⟩) p ∧
    ∃ (ρ : R →+* (Spec (CommRingCat.of R)).residueField ⟨𝔪, h𝔪.isPrime⟩)
      (_ : Spec.map (CommRingCat.ofHom ρ) =
        (Spec (CommRingCat.of R)).fromSpecResidueField ⟨𝔪, h𝔪.isPrime⟩)
      (φ' : R →+* TruncatedWittVector p 2
        ((Spec (CommRingCat.of R)).residueField ⟨𝔪, h𝔪.isPrime⟩)),
      ∀ r, (φ' r).coeff 0 = ρ r := by
  let iso := Scheme.Spec.residueFieldIso (CommRingCat.of R) ⟨𝔪, h𝔪.isPrime⟩
  let e : R ⧸ 𝔪 ≃+* (Spec (CommRingCat.of R)).residueField ⟨𝔪, h𝔪.isPrime⟩ :=
    (RingEquiv.ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField 𝔪)).trans
      iso.symm.commRingCatIsoToRingEquiv
  have he : ∀ r, e (Ideal.Quotient.mk 𝔪 r) = iso.inv.hom (algebraMap R 𝔪.ResidueField r) :=
    fun r => rfl
  refine ⟨Finite.of_equiv _ e.toEquiv,
    charP_of_injective_ringHom (f := e.toRingHom) e.injective p,
    iso.inv.hom.comp (algebraMap R 𝔪.ResidueField), ?_,
    (truncatedWittMap e.toRingHom).comp φ, fun r => ?_⟩
  · have h := Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (CommRingCat.of R)
      ⟨𝔪, h𝔪.isPrime⟩
    rwa [← Spec.map_comp] at h
  · change e ((φ r).coeff 0) = _
    rw [hφ, he]
    rfl

public theorem solution : ∀ (n : ℕ) {V : Scheme.{0}}
    (π : V ⟶ Spec (CommRingCat.of ℂ)) [SmoothOfRelativeDimension n π] (hπ : IsProjective π)
    (S : MMP.Mori.Divisor V) (hS : S.IsRelativeSNC n π) (twist : Bool) (k : ℕ),
    -- `ℍ^j(V, L)` over `Γ(Spec ℂ, ⊤) = ℂ`, for a bounded below complex of `π⁻¹𝒪`-modules
    let H : CochainComplex.Plus (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) →
        ℤ → ModuleCat.{0} Γ(Spec (CommRingCat.of ℂ), ⊤) := fun L j =>
      let Γd := (SheafOfModules.evaluation.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))
          (op ⊤)).rightDerivedFunctorPlus
      let Mj := (DerivedCategory.homologyFunctor _ j).obj
        (DerivedCategory.Plus.ι.obj (Γd.obj (DerivedCategory.Plus.Q.obj L)))
      (ModuleCat.restrictScalars.{0} (show Γ(Spec (CommRingCat.of ℂ), ⊤) →+*
          ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj
            (Spec (CommRingCat.of ℂ)).sheaf).obj.obj (op ⊤) from
        (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} π.base).unit.app
          (Spec (CommRingCat.of ℂ)).sheaf).hom.app (op ⊤)).hom)).obj Mj
    -- `Ω^•_V(log S)`, resp. `Ω^•_V(log S)(-S)`
    let K := relativeLogDeRhamComplex n π S hS (bif twist then S.suppIdeal else ⊤)
    Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
        (H ⟨K.extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
      ∑ p ∈ Finset.range (k + 1), Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
        (H ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (K.X p), 0,
          (CochainComplex.isStrictlyGE_iff _ 0).2 fun i hi =>
            HomologicalComplex.isZero_single_obj_X _ 0 _ i (by omega)⟩ ((k - p : ℕ) : ℤ)) := by
  intro n V π _ hπ S hS twist k H K
  obtain ⟨R, _, _, _, ι, hι, 𝒳, g, _, hg, 𝒟, h𝒟, e, -, -, hfib⟩ :=
    exists_isRelativeSNC_model_finrank_hypercohomology_eq n π hπ S hS
  obtain ⟨𝔪, h𝔪, -, hfin, p, hp, hnp, hchar, φ, hφ⟩ :=
    MMP.exists_isMaximal_mem_smoothLocus_witt_lift (R := R) Set.univ isOpen_univ
      Set.univ_nonempty
      (fun x _ => by rw [Algebra.smoothLocus_eq_univ_iff.2 inferInstance]; trivial) n
  obtain ⟨_, _, ρ, hρ, φ', hφ'⟩ := exists_wittTwoLift_residueField 𝔪 p φ hφ
  obtain ⟨_, Ds, hDs, hsupp, hdim⟩ := hfib ⟨𝔪, h𝔪.isPrime⟩
  rw [(hdim twist 0 k).2, Finset.sum_congr rfl fun q _ => (hdim twist q ((k - q : ℕ) : ℤ)).1]
  exact finrank_hyp_eq_sum_of_wittTwoLift n g hg 𝒟 h𝒟 _ p hnp ρ hρ φ' hφ' Ds hDs hsupp twist k

end MMP.FourfoldProofs.LogDegenerationProof
