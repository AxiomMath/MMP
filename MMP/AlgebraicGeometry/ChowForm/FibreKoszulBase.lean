module

public import MMP.AlgebraicGeometry.ChowForm.FibreSheafPieces

/-!
# Koszul complex of the fibre, base change matrices and polynomial algebra

For a proper flat morphism `π : Y ⟶ T` and invertible modules on `Y`, this file compares the
two-term Koszul complex of global sections on a fibre of `π` with the matrices of the direct image
sections over an affine open, reduced to the residue field. It also collects the stalkwise facts
about multiplication by sections of an invertible module, matrices of base changed linear maps, and
the factorisation and total degree of polynomials whose zeros lie on given hypersurfaces.

## Main results

* `koszul_glue`: exactness of global sections of a Koszul complex that is stalkwise bijective on
  the two members of an open cover.
* `fibre_koszul`: exactness of the Koszul complex on a fibre gives exactness of the reduced matrix
  complex of direct image sections.
* `exists_eq_C_mul_prod_pow_of_zeroLocus_subset`: a polynomial whose zeros lie on given
  irreducible hypersurfaces is a constant times a product of powers of their equations.
* `mul_totalDegree_eq_sum`: comparison of exponents curve by curve.

## References

* [J. Kollár, *Rational curves on algebraic varieties*][Kollar1996], I.3
-/

@[expose] public section

universe u

namespace MMP.Chow.DeterminantCurveForm

open CategoryTheory AlgebraicGeometry

open MMP CategoryTheory Limits AlgebraicGeometry Stacks.AlgebraicGeometry.ProjPolyChart MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

section FibreKoszul

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

section Glue

/-- A morphism of modules that is bijective on stalks at every point of `V` is bijective on
sections over `V`. -/
theorem app_bijective_of_stalk {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (V : X.Opens)
    (h : ∀ y ∈ V, Function.Bijective ((TopCat.Presheaf.stalkFunctor Ab y).map φ.mapPresheaf)) :
    Function.Bijective (φ.app V) :=
  TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective
    (F := ⟨M.presheaf, M.isSheaf⟩) (G := ⟨N.presheaf, N.isSheaf⟩) ⟨φ.mapPresheaf⟩ V h

/-- Restriction maps commute with the components of a morphism of modules. -/
theorem app_map_homOfLE {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens}
    (i : V ≤ U) (z : Γ(M, U)) :
    φ.app V (M.presheaf.map (homOfLE i).op z) = N.presheaf.map (homOfLE i).op (φ.app U z) := by
  have := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE i).op) z
  simp only [ConcreteCategory.comp_apply] at this
  exact this

/-- Two global sections of a module agreeing on both members of an open cover agree. -/
theorem eq_of_restrict_eq_of_le_sup {X : Scheme.{u}} {M : X.Modules} {Ua Ub : X.Opens}
    (hcov : (⊤ : X.Opens) ≤ Ua ⊔ Ub) (z z' : Γ(M, ⊤))
    (h1 : M.presheaf.map (homOfLE (le_top : Ua ≤ ⊤)).op z =
      M.presheaf.map (homOfLE le_top).op z')
    (h2 : M.presheaf.map (homOfLE (le_top : Ub ≤ ⊤)).op z =
      M.presheaf.map (homOfLE le_top).op z') :
    z = z' :=
  TopCat.Sheaf.eq_of_locally_eq₂ (F := ⟨M.presheaf, M.isSheaf⟩) (homOfLE le_top) (homOfLE le_top)
    hcov z z' h1 h2

/-- If `α` is stalkwise bijective on `Ua` and `β` on `Ub` with `Ua ∪ Ub = X`, then `(α, β)` is
jointly injective on global sections. -/
theorem koszul_glue_injective {X : Scheme.{u}} {M₂ M₁ : X.Modules} (α β : M₂ ⟶ M₁)
    (Ua Ub : X.Opens) (hcov : (⊤ : X.Opens) ≤ Ua ⊔ Ub)
    (hα : ∀ y ∈ Ua, Function.Bijective ((TopCat.Presheaf.stalkFunctor Ab y).map α.mapPresheaf))
    (hβ : ∀ y ∈ Ub, Function.Bijective ((TopCat.Presheaf.stalkFunctor Ab y).map β.mapPresheaf))
    (w : Γ(M₂, ⊤)) (h1 : α.app ⊤ w = 0) (h2 : β.app ⊤ w = 0) : w = 0 := by
  refine eq_of_restrict_eq_of_le_sup hcov w 0 ?_ ?_
  · apply (app_bijective_of_stalk α Ua hα).1
    rw [app_map_homOfLE, h1, map_zero, map_zero, map_zero]
  · apply (app_bijective_of_stalk β Ub hβ).1
    rw [app_map_homOfLE, h2, map_zero, map_zero, map_zero]

/-- For `α, β : M₂ ⟶ M₁` and `α', β' : M₁ ⟶ M₀` with `β ≫ α' = α ≫ β'`, where `α, α'` are
stalkwise bijective on `Ua` and `β, β'` on `Ub` with `Ua ∪ Ub = X`, every pair of global sections
`(s, t)` with `α' s + β' t = 0` is `(-β w, α w)` for some `w`. -/
theorem koszul_glue_exists {X : Scheme.{u}} {M₂ M₁ M₀ : X.Modules}
    (α β : M₂ ⟶ M₁) (α' β' : M₁ ⟶ M₀) (hcomm : β ≫ α' = α ≫ β')
    (Ua Ub : X.Opens) (hcov : (⊤ : X.Opens) ≤ Ua ⊔ Ub)
    (hα : ∀ y ∈ Ua, Function.Bijective ((TopCat.Presheaf.stalkFunctor Ab y).map α.mapPresheaf))
    (hα' : ∀ y ∈ Ua, Function.Bijective ((TopCat.Presheaf.stalkFunctor Ab y).map α'.mapPresheaf))
    (hβ : ∀ y ∈ Ub, Function.Bijective ((TopCat.Presheaf.stalkFunctor Ab y).map β.mapPresheaf))
    (hβ' : ∀ y ∈ Ub, Function.Bijective ((TopCat.Presheaf.stalkFunctor Ab y).map β'.mapPresheaf))
    (s t : Γ(M₁, ⊤)) (hst : α'.app ⊤ s + β'.app ⊤ t = 0) :
    ∃ w, -(β.app ⊤ w) = s ∧ α.app ⊤ w = t := by
  have resres : ∀ {M : X.Modules} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (z : Γ(M, U)),
      M.presheaf.map (homOfLE h2).op (M.presheaf.map (homOfLE h1).op z) =
        M.presheaf.map (homOfLE (h2.trans h1)).op z := fun {M} U V W h1 h2 z => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hcommU : ∀ (V : X.Opens) (z : Γ(M₂, V)), α'.app V (β.app V z) = β'.app V (α.app V z) :=
    fun V z => by
      simpa [Scheme.Modules.Hom.comp_app] using
        congrArg (fun f => ConcreteCategory.hom (Scheme.Modules.Hom.app f V) z) hcomm
  have hst' : α'.app ⊤ s = -(β'.app ⊤ t) := eq_neg_of_add_eq_zero_left hst
  obtain ⟨wa, hwa⟩ := (app_bijective_of_stalk α Ua hα).2
    (M₁.presheaf.map (homOfLE (le_top : Ua ≤ ⊤)).op t)
  obtain ⟨wb', hwb'⟩ := (app_bijective_of_stalk β Ub hβ).2
    (M₁.presheaf.map (homOfLE (le_top : Ub ≤ ⊤)).op s)
  set wb := -wb' with hwb
  have h1 : -(β.app Ua wa) = M₁.presheaf.map (homOfLE (le_top : Ua ≤ ⊤)).op s := by
    apply (app_bijective_of_stalk α' Ua hα').1
    rw [map_neg, hcommU, hwa, app_map_homOfLE, app_map_homOfLE, hst', map_neg]
  have h2 : α.app Ub wb = M₁.presheaf.map (homOfLE (le_top : Ub ≤ ⊤)).op t := by
    apply (app_bijective_of_stalk β' Ub hβ').1
    rw [← hcommU, hwb, map_neg, map_neg, hwb', app_map_homOfLE, app_map_homOfLE, hst']
    simp only [map_neg, neg_neg]
  have hcompat : ∀ (V : X.Opens) (hA : V ≤ Ua) (hB : V ≤ Ub),
      M₂.presheaf.map (homOfLE hA).op wa = M₂.presheaf.map (homOfLE hB).op wb := by
    intro V hA hB
    apply (app_bijective_of_stalk α V fun y hy => hα y (hA hy)).1
    rw [app_map_homOfLE, app_map_homOfLE, hwa, h2, resres, resres]
  let U : Bool → X.Opens := fun b => if b then Ua else Ub
  let sf : ∀ b : Bool, Γ(M₂, U b) := fun b => match b with
    | true => wa
    | false => wb
  have hc : TopCat.Presheaf.IsCompatible M₂.presheaf U sf := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact (hcompat (Ub ⊓ Ua) inf_le_right inf_le_left).symm
    · exact hcompat (Ua ⊓ Ub) inf_le_left inf_le_right
    · rfl
  obtain ⟨w, hw, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := ⟨M₂.presheaf, M₂.isSheaf⟩) U ⊤
    (fun b => homOfLE le_top) (hcov.trans (sup_le (le_iSup U true) (le_iSup U false))) sf hc
  have hwA : M₂.presheaf.map (homOfLE (le_top : Ua ≤ ⊤)).op w = wa := hw true
  have hwB : M₂.presheaf.map (homOfLE (le_top : Ub ≤ ⊤)).op w = wb := hw false
  refine ⟨w, eq_of_restrict_eq_of_le_sup hcov _ _ ?_ ?_,
    eq_of_restrict_eq_of_le_sup hcov _ _ ?_ ?_⟩
  · rw [map_neg, ← app_map_homOfLE, hwA, h1]
  · rw [map_neg, ← app_map_homOfLE, hwB, hwb, map_neg, neg_neg, hwb']
  · rw [← app_map_homOfLE, hwA, hwa]
  · rw [← app_map_homOfLE, hwB, h2]

/-- For two pairs of morphisms `α, β : M₂ ⟶ M₁` and `α', β' : M₁ ⟶ M₀` with `β ≫ α' = α ≫ β'`,
where `α, α'` are stalkwise bijective on `Ua` and `β, β'` on `Ub` with `Ua ∪ Ub = X`, the global
sections satisfy: `(α, β)` is jointly injective, and every `(s, t)` with `α' s + β' t = 0` is
`(-β w, α w)` for some `w`. -/
theorem koszul_glue {X : Scheme.{u}} {M₂ M₁ M₀ : X.Modules}
    (α β : M₂ ⟶ M₁) (α' β' : M₁ ⟶ M₀) (hcomm : β ≫ α' = α ≫ β')
    (Ua Ub : X.Opens) (hcov : (⊤ : X.Opens) ≤ Ua ⊔ Ub)
    (hα : ∀ y ∈ Ua, Function.Bijective ((TopCat.Presheaf.stalkFunctor Ab y).map α.mapPresheaf))
    (hα' : ∀ y ∈ Ua, Function.Bijective ((TopCat.Presheaf.stalkFunctor Ab y).map α'.mapPresheaf))
    (hβ : ∀ y ∈ Ub, Function.Bijective ((TopCat.Presheaf.stalkFunctor Ab y).map β.mapPresheaf))
    (hβ' : ∀ y ∈ Ub, Function.Bijective ((TopCat.Presheaf.stalkFunctor Ab y).map β'.mapPresheaf)) :
    (∀ w : Γ(M₂, ⊤), α.app ⊤ w = 0 → β.app ⊤ w = 0 → w = 0) ∧
    ∀ s t : Γ(M₁, ⊤), α'.app ⊤ s + β'.app ⊤ t = 0 →
      ∃ w, -(β.app ⊤ w) = s ∧ α.app ⊤ w = t :=
  ⟨koszul_glue_injective α β Ua Ub hcov hα hβ,
    koszul_glue_exists α β α' β' hcomm Ua Ub hcov hα hα' hβ hβ'⟩

end Glue

section PullbackStalk

/-- Naturality of the unit of the pullback–pushforward adjunction, evaluated on a section. -/
theorem unit_naturality_apply {X Y : Scheme.{u}} (ρ : X ⟶ Y) {M N : Y.Modules} (f : M ⟶ N)
    (V : Y.Opens) (s : Γ(M, V)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction ρ).unit.app N).val.app (op V)
        (f.val.app (op V) s) =
      ((Scheme.Modules.pullback ρ).map f).val.app (op (ρ ⁻¹ᵁ V))
        (((Scheme.Modules.pullbackPushforwardAdjunction ρ).unit.app M).val.app (op V) s) := by
  have h3 := congrArg
    (fun φ : M ⟶ (Scheme.Modules.pullback ρ ⋙ Scheme.Modules.pushforward ρ).obj N =>
      ConcreteCategory.hom (Scheme.Modules.Hom.app φ V) s)
    ((Scheme.Modules.pullbackPushforwardAdjunction ρ).unit.naturality f)
  simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app, ConcreteCategory.comp_apply] at h3
  exact h3

/-- The stalk map of a morphism `f` of modules, read on the stalks of the topological presheaves
of abelian groups, as a linear map over the local ring. -/
noncomputable def stalkLinearMapAb {Y : Scheme.{u}} {M N : Y.Modules} (f : M ⟶ N)
    (y : Y) :
    TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf y →ₗ[Y.presheaf.stalk y]
      TopCat.Presheaf.stalk (C := Ab.{u}) N.val.presheaf y :=
  { toFun := stalkLinearMap M N f y
    map_add' := (stalkLinearMap M N f y).map_add
    map_smul' := (stalkLinearMap M N f y).map_smul }

/-- **The stalk of a pulled back morphism is the base change of the stalk map.** -/
theorem pullbackStalkEquiv_stalkLinearMap {X Y : Scheme.{u}} (ρ : X ⟶ Y) {M N : Y.Modules}
    (f : M ⟶ N) (x : X) (z : ((Scheme.Modules.pullback ρ).obj M).presheaf.stalk x) :
    letI : Algebra (Y.presheaf.stalk (ρ x)) (X.presheaf.stalk x) := (ρ.stalkMap x).hom.toAlgebra
    Scheme.Modules.pullbackStalkEquiv ρ N x
        (stalkLinearMap _ _ ((Scheme.Modules.pullback ρ).map f) x z) =
      LinearMap.baseChange (X.presheaf.stalk x) (stalkLinearMapAb f (ρ x))
        (Scheme.Modules.pullbackStalkEquiv ρ M x z) := by
  letI : Algebra (Y.presheaf.stalk (ρ x)) (X.presheaf.stalk x) := (ρ.stalkMap x).hom.toAlgebra
  set eM := Scheme.Modules.pullbackStalkEquiv ρ M x
  set eN := Scheme.Modules.pullbackStalkEquiv ρ N x
  let T := LinearMap.baseChange (X.presheaf.stalk x) (stalkLinearMapAb f (ρ x))
  let L1 : TensorProduct (Y.presheaf.stalk (ρ x)) (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf (ρ x)) →ₗ[X.presheaf.stalk x]
      TensorProduct (Y.presheaf.stalk (ρ x)) (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) N.val.presheaf (ρ x)) :=
    eN.toLinearMap ∘ₗ (stalkLinearMap _ _ ((Scheme.Modules.pullback ρ).map f) x) ∘ₗ
      eM.symm.toLinearMap
  have key : L1 = T := by
    refine TensorProduct.AlgebraTensorModule.ext fun a m => ?_
    have e1 : a ⊗ₜ[Y.presheaf.stalk (ρ x)] m =
        a • ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (ρ x)] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e1, map_smul, map_smul]
    congr 1
    obtain ⟨V, hV, s, rfl⟩ := TopCat.Presheaf.germ_exist (C := Ab.{u}) M.val.presheaf m
    have h1 := Scheme.Modules.pullbackStalkEquiv_symm_one_tmul ρ M x V hV s
    have h2 := Scheme.Modules.pullbackStalkEquiv_germ ρ N x V hV (f.val.app (op V) s)
    have h3 := stalkLinearMap_germ _ _ ((Scheme.Modules.pullback ρ).map f) (ρ ⁻¹ᵁ V) x hV
      (((Scheme.Modules.pullbackPushforwardAdjunction ρ).unit.app M).val.app (op V) s)
    have h4 := stalkLinearMap_germ _ _ f V (ρ x) hV s
    have h5 := unit_naturality_apply ρ f V s
    show eN (stalkLinearMap _ _ ((Scheme.Modules.pullback ρ).map f) x (eM.symm _)) = _
    erw [h1, h3, ← h5, h2]
    show _ = (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (ρ x)]
      (stalkLinearMap M N f (ρ x) _)
    erw [h4]
    rfl
  have hk := LinearMap.congr_fun key (eM z)
  have hz : eM.symm (eM z) = z := eM.symm_apply_apply z
  change eN (stalkLinearMap _ _ ((Scheme.Modules.pullback ρ).map f) x (eM.symm (eM z))) =
    T (eM z) at hk
  rw [hz] at hk
  exact hk

/-- If the stalk map of `f` at `ρ x` is bijective, then so is the stalk map of the pullback
of `f` along `ρ` at `x`. -/
theorem bijective_stalk_pullback_map {X Y : Scheme.{u}} (ρ : X ⟶ Y) {M N : Y.Modules}
    (f : M ⟶ N) (x : X) (h : Function.Bijective (stalkLinearMap M N f (ρ x))) :
    Function.Bijective (stalkLinearMap _ _ ((Scheme.Modules.pullback ρ).map f) x) := by
  letI : Algebra (Y.presheaf.stalk (ρ x)) (X.presheaf.stalk x) := (ρ.stalkMap x).hom.toAlgebra
  set eM := Scheme.Modules.pullbackStalkEquiv ρ M x
  set eN := Scheme.Modules.pullbackStalkEquiv ρ N x
  let T := (LinearEquiv.ofBijective (stalkLinearMapAb f (ρ x)) h).baseChange
    (Y.presheaf.stalk (ρ x)) (X.presheaf.stalk x) _ _
  have : (stalkLinearMap _ _ ((Scheme.Modules.pullback ρ).map f) x : _ → _) =
      eN.symm ∘ T ∘ eM := by
    funext z
    refine eN.eq_symm_apply.2 ((pullbackStalkEquiv_stalkLinearMap ρ f x z).trans ?_)
    exact baseChange_toLinearMap_apply _ (LinearEquiv.ofBijective _ h) _
  rw [this]
  exact eN.symm.bijective.comp (T.bijective.comp eM.bijective)

end PullbackStalk

section CoordMulStalk

open MonoidalCategory Stacks.Ample Stacks.RelativeVeryAmple

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

variable {X : Scheme.{u}} (H A : X.Modules) [IsInvertibleModule X H] [IsInvertibleModule X A]

/-- The category of sheaves of modules over the structure sheaf of `X`. -/
abbrev SC (X : Scheme.{u}) := SheafOfModules.{u}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))

/-- Left whiskering in `SC X` is `Scheme.Modules.tensorLeftMap`, conjugated by
`tensorLeftIso`. -/
theorem whiskerLeft_eq (T : SC X) {B B' : SC X} (g : B ⟶ B') :
    T ◁ g =
      (Stacks.SheafInternalHom.tensorLeftIso X.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) T).hom.app B ≫
        Scheme.Modules.tensorLeftMap (X := X) T g ≫
        (Stacks.SheafInternalHom.tensorLeftIso X.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) T).inv.app B' :=
  (NatIso.naturality_2 (Stacks.SheafInternalHom.tensorLeftIso X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) T) g).symm

open Stacks.EnriquesSeveriZariski in
/-- Multiplication `MMP.Chow.coordMulHom H σ m` by a section `σ` factors as the left
whiskering of `sectionHom H σ`, conjugated by the unitor, `tensorLeftIso` and `tensorPowAddIso`. -/
theorem coordMulHom_eq_comp (σ : Γ(H, ⊤)) (m : ℤ) :
    let T : SC X := tensorPowModule X H m
    let θ := Stacks.SheafInternalHom.tensorLeftIso X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) T
    MMP.Chow.coordMulHom H σ m =
      (ρ_ T).inv ≫ (T ◁ (unitModuleIsoTensorUnit X).inv) ≫ θ.hom.app (unitModule X) ≫
        Scheme.Modules.tensorLeftMap (X := X) T (sectionHom H σ) ≫ θ.inv.app (H : SC X) ≫
          (T ◁ (tensorPowModuleOneIso X H).inv) ≫
            (SheafOfModules.tensorPowAddIso X.presheaf
              (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) H m ((1 : ℕ) : ℤ)).hom := by
  intro T θ
  unfold MMP.Chow.coordMulHom MMP.Chow.mulPow MMP.Chow.sectionToPow
  have h1 := (MonoidalCategory.whiskerLeft_comp (C := SC X) T (unitModuleIsoTensorUnit X).inv
    (sectionHom H σ ≫ (tensorPowModuleOneIso X H).inv)).trans
      (congrArg (T ◁ (unitModuleIsoTensorUnit X).inv ≫ ·)
        (MonoidalCategory.whiskerLeft_comp (C := SC X) T (sectionHom H σ)
          (tensorPowModuleOneIso X H).inv))
  erw [h1, whiskerLeft_eq T (sectionHom H σ)]
  simp only [Category.assoc]
  rfl

open Stacks.EnriquesSeveriZariski in
/-- At each stalk, multiplication `MMP.Chow.coordMulHom H σ m` by a section `σ` factors, through
bijections `P` and `Q`, as the tensor of the identity with the stalk map of `sectionHom H σ`. -/
theorem stalk_coordMulHom (m : ℤ) (y : X) :
    ∃ (P : (tensorPowModule X H m).presheaf.stalk y →ₗ[X.presheaf.stalk y]
        TensorProduct (X.presheaf.stalk y) ((tensorPowModule X H m).presheaf.stalk y)
          ((unitModule X).presheaf.stalk y))
      (Q : TensorProduct (X.presheaf.stalk y) ((tensorPowModule X H m).presheaf.stalk y)
          (H.presheaf.stalk y) →ₗ[X.presheaf.stalk y]
          (tensorPowModule X H (m + 1)).presheaf.stalk y),
      Function.Bijective P ∧ Function.Bijective Q ∧
      ∀ (σ : Γ(H, ⊤)) z, stalkLinearMap _ _ (MMP.Chow.coordMulHom H σ m) y z =
        Q (LinearMap.lTensor _ (stalkLinearMap _ _ (sectionHom H σ) y) (P z)) := by
  let T : SC X := tensorPowModule X H m
  let ρi : T ⟶ T ⊗ 𝟙_ (SC X) := (ρ_ T).inv
  let u := unitModuleIsoTensorUnit X
  let o := tensorPowModuleOneIso X H
  let θ := Stacks.SheafInternalHom.tensorLeftIso X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) T
  let ad := SheafOfModules.tensorPowAddIso X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) H m ((1 : ℕ) : ℤ)
  have wiso : ∀ {B B' : SC X} (e : B ≅ B'), (T ◁ e.hom) ≫ (T ◁ e.inv) = 𝟙 _ := fun e => by
    rw [← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id]
  refine ⟨(tensorStalkEquiv (T : X.Modules) (unitModule X) y).toLinearMap ∘ₗ
      stalkLinearMap _ _ (θ.hom.app (unitModule X)) y ∘ₗ stalkLinearMap _ _ (T ◁ u.inv) y ∘ₗ
        stalkLinearMap _ _ ρi y,
    stalkLinearMap _ _ ad.hom y ∘ₗ stalkLinearMap _ _ (T ◁ o.inv) y ∘ₗ
      stalkLinearMap _ _ (θ.inv.app (H : SC X)) y ∘ₗ
        (tensorStalkEquiv (T : X.Modules) H y).symm.toLinearMap, ?_, ?_, ?_⟩
  · have b1 : Function.Bijective (stalkLinearMap _ _ ρi y) :=
      bijective_stalkLinearMap_of_inverse ρi (ρ_ T).hom (Iso.inv_hom_id _) (Iso.hom_inv_id _) y
    have b2 : Function.Bijective (stalkLinearMap _ _ (T ◁ u.inv) y) :=
      bijective_stalkLinearMap_of_inverse (T ◁ u.inv) (T ◁ u.hom) (wiso u.symm) (wiso u) y
    have b3 : Function.Bijective (stalkLinearMap _ _ (θ.hom.app (unitModule X)) y) :=
      bijective_stalkLinearMap_of_inverse (θ.hom.app (unitModule X)) (θ.inv.app (unitModule X))
        (θ.hom_inv_id_app _) (θ.inv_hom_id_app _) y
    exact (tensorStalkEquiv _ _ y).bijective.comp (b3.comp (b2.comp b1))
  · have b1 : Function.Bijective (stalkLinearMap _ _ ad.hom y) :=
      bijective_stalkLinearMap_of_inverse ad.hom ad.inv ad.hom_inv_id ad.inv_hom_id y
    have b2 : Function.Bijective (stalkLinearMap _ _ (T ◁ o.inv) y) :=
      bijective_stalkLinearMap_of_inverse (T ◁ o.inv) (T ◁ o.hom) (wiso o.symm) (wiso o) y
    have b3 : Function.Bijective (stalkLinearMap _ _ (θ.inv.app (H : SC X)) y) :=
      bijective_stalkLinearMap_of_inverse (θ.inv.app (H : SC X)) (θ.hom.app (H : SC X))
        (θ.inv_hom_id_app _) (θ.hom_inv_id_app _) y
    exact b1.comp (b2.comp (b3.comp (tensorStalkEquiv _ _ y).symm.bijective))
  · intro σ z
    have hL : ∀ w,
        stalkLinearMap _ _ (Scheme.Modules.tensorLeftMap (X := X) T (sectionHom H σ)) y w =
        (tensorStalkEquiv (T : X.Modules) H y).symm (LinearMap.lTensor _
          (stalkLinearMap _ _ (sectionHom H σ) y) (tensorStalkEquiv T (unitModule X) y w)) :=
      fun w => (LinearEquiv.eq_symm_apply _).2 (tensorStalkEquiv_tensorLeftMap _ _ y w)
    let M0 : X.Modules := tensorPowModule X H m
    let M1 : X.Modules := (T ⊗ 𝟙_ (SC X) : SC X)
    let M2 : X.Modules := (T ⊗ (unitModule X : SC X) : SC X)
    let M3 : X.Modules := Scheme.Modules.tensorObj (X := X) T (unitModule X)
    let M4 : X.Modules := Scheme.Modules.tensorObj (X := X) T H
    let M5 : X.Modules := (T ⊗ (H : SC X) : SC X)
    let M6 : X.Modules := (T ⊗ (tensorPowModule X H 1 : SC X) : SC X)
    let M7 : X.Modules := tensorPowModule X H (m + 1)
    let f1 : M0 ⟶ M1 := ρi
    let f2 : M1 ⟶ M2 := T ◁ u.inv
    let f3 : M2 ⟶ M3 := θ.hom.app (unitModule X)
    let f4 : M3 ⟶ M4 := Scheme.Modules.tensorLeftMap (X := X) T (sectionHom H σ)
    let f5 : M4 ⟶ M5 := θ.inv.app (H : SC X)
    let f6 : M5 ⟶ M6 := T ◁ o.inv
    let f7 : M6 ⟶ M7 := ad.hom
    have e' : MMP.Chow.coordMulHom H σ m = f1 ≫ f2 ≫ f3 ≫ f4 ≫ f5 ≫ f6 ≫ f7 :=
      coordMulHom_eq_comp H σ m
    rw [e']
    refine (Scheme.Modules.stalkLinearMap_comp f1 _ y z).trans ?_
    refine (Scheme.Modules.stalkLinearMap_comp f2 _ y _).trans ?_
    refine (Scheme.Modules.stalkLinearMap_comp f3 _ y _).trans ?_
    refine (Scheme.Modules.stalkLinearMap_comp f4 _ y _).trans ?_
    refine (Scheme.Modules.stalkLinearMap_comp f5 _ y _).trans ?_
    refine (Scheme.Modules.stalkLinearMap_comp f6 _ y _).trans ?_
    refine congrArg (stalkLinearMap _ _ f7 y) (congrArg (stalkLinearMap _ _ f6 y)
      (congrArg (stalkLinearMap _ _ f5 y) (hL _)))

open Stacks.EnriquesSeveriZariski in
/-- On the stalk at `y`, multiplication `MMP.Chow.coordMul H A σ n m` by a section `σ` is the
image of the stalk map of `sectionHom H σ` under a linear map `F` sending bijections to
bijections. -/
theorem stalk_coordMul (n : ℕ) (m : ℤ) (y : X) :
    ∃ F : ((Stacks.Ample.unitModule X).presheaf.stalk y →ₗ[X.presheaf.stalk y]
        H.presheaf.stalk y) →ₗ[X.presheaf.stalk y]
        ((MMP.Chow.twistMod H A n m).presheaf.stalk y →ₗ[X.presheaf.stalk y]
          (MMP.Chow.twistMod H A n (m + 1)).presheaf.stalk y),
      (∀ ψ : (Stacks.Ample.unitModule X).presheaf.stalk y →ₗ[X.presheaf.stalk y]
        H.presheaf.stalk y, Function.Bijective ψ → Function.Bijective (F ψ)) ∧
      ∀ σ : Γ(H, ⊤), stalkLinearMap _ _ (MMP.Chow.coordMul H A σ n m) y =
        F (stalkLinearMap _ _ (sectionHom H σ) y) := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := stalk_coordMulHom H m y
  let An := (tensorPowModule X A n : X.Modules).presheaf.stalk y
  let e0 := tensorStalkEquiv (tensorPowModule X H m) (tensorPowModule X A n) y
  let e1 := tensorStalkEquiv (tensorPowModule X H (m + 1)) (tensorPowModule X A n) y
  let G : ((Stacks.Ample.unitModule X).presheaf.stalk y →ₗ[X.presheaf.stalk y] H.presheaf.stalk y)
      →ₗ[X.presheaf.stalk y] ((tensorPowModule X H m).presheaf.stalk y →ₗ[X.presheaf.stalk y]
        (tensorPowModule X H (m + 1)).presheaf.stalk y) :=
    (LinearMap.llcomp _ _ _ _ Q).comp (((LinearMap.llcomp _ _ _ _).flip P).comp
      (LinearMap.lTensorHom (M := (tensorPowModule X H m).presheaf.stalk y)))
  let F := (LinearMap.llcomp _ _ _ _ e1.symm.toLinearMap).comp
    (((LinearMap.llcomp _ _ _ _).flip e0.toLinearMap).comp
      ((LinearMap.rTensorHom (M := An)).comp G))
  refine ⟨F, fun ψ hψ => ?_, fun σ => ?_⟩
  · have h2 : Function.Bijective (Q ∘ₗ LinearMap.lTensor _ ψ ∘ₗ P) :=
      hQ.comp ((LinearEquiv.lTensor _ (LinearEquiv.ofBijective ψ hψ)).bijective.comp hP)
    have h3 : Function.Bijective (LinearMap.rTensor An (Q ∘ₗ LinearMap.lTensor _ ψ ∘ₗ P)) :=
      (LinearEquiv.rTensor An (LinearEquiv.ofBijective _ h2)).bijective
    exact e1.symm.bijective.comp (h3.comp e0.bijective)
  · ext z
    have h :=
      tensorStalkEquiv_tensorRightMap (MMP.Chow.coordMulHom H σ m) (tensorPowModule X A n) y z
    rw [← LinearEquiv.eq_symm_apply] at h
    refine h.trans ?_
    have hc : stalkLinearMap _ _ (MMP.Chow.coordMulHom H σ m) y =
        Q ∘ₗ LinearMap.lTensor _ (stalkLinearMap _ _ (sectionHom H σ) y) ∘ₗ P :=
      LinearMap.ext (hPQ σ)
    rw [hc]
    rfl

open Stacks.EnriquesSeveriZariski in
/-- On the nonvanishing locus of `σ`, multiplication by `σ` is bijective on stalks. -/
theorem bijective_stalk_coordMul (σ : Γ(H, ⊤)) (n : ℕ) (m : ℤ) {y : X}
    (hy : y ∈ Stacks.Ample.nonvanishingLocus H σ) :
    Function.Bijective (stalkLinearMap _ _ (MMP.Chow.coordMul H A σ n m) y) := by
  obtain ⟨F, hF, hFσ⟩ := stalk_coordMul H A n m y
  rw [hFσ σ]
  exact hF _ (bijective_stalkLinearMap_sectionHom H σ hy)

open Stacks.EnriquesSeveriZariski in
/-- Multiplication by a linear combination `∑ c j • τ j` of sections is the corresponding
linear combination of the multiplications by the `τ j`. -/
theorem coordMul_app_sum {ι : Type*} [Fintype ι] (c : ι → Γ(X, ⊤)) (τ : ι → Γ(H, ⊤)) (n : ℕ)
    (m : ℤ) (V : X.Opens) (s : Γ(MMP.Chow.twistMod H A n m, V)) :
    (MMP.Chow.coordMul H A (∑ j, c j • τ j) n m).app V s =
      ∑ j, (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (c j) : Γ(X, V)) •
        (MMP.Chow.coordMul H A (τ j) n m).app V s := by
  refine TopCat.Presheaf.section_ext ⟨_, (MMP.Chow.twistMod H A n (m + 1)).isSheaf⟩ V _ _
    fun y hy => ?_
  obtain ⟨F, -, hF⟩ := stalk_coordMul H A n m y
  have hσ : stalkLinearMap _ _ (sectionHom H (∑ j, c j • τ j)) y =
      ∑ j, (X.presheaf.Γgerm y).hom (c j) • stalkLinearMap _ _ (sectionHom H (τ j)) y := by
    ext z
    rw [stalkLinearMap_sectionHom, map_sum, LinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hg : (H.presheaf.Γgerm y).hom (c j • τ j) =
        (X.presheaf.Γgerm y).hom (c j) • (H.presheaf.Γgerm y).hom (τ j) :=
      PresheafOfModules.germ_smul (M := H.val) y ⊤ trivial (c j) (τ j)
    rw [LinearMap.smul_apply, stalkLinearMap_sectionHom, hg, smul_comm]
  have h1 := stalkLinearMap_germ _ _ (MMP.Chow.coordMul H A (∑ j, c j • τ j) n m) V y hy s
  have h2 : ∀ j, (MMP.Chow.twistMod H A n (m + 1)).presheaf.germ V y hy
      ((MMP.Chow.coordMul H A (τ j) n m).app V s) =
      F (stalkLinearMap _ _ (sectionHom H (τ j)) y)
        ((MMP.Chow.twistMod H A n m).presheaf.germ V y hy s) := fun j => by
    rw [← hF, stalkLinearMap_germ]
    rfl
  show _ = (MMP.Chow.twistMod H A n (m + 1)).presheaf.germ V y hy _
  erw [← h1, hF, hσ, map_sum, map_sum]
  simp only [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hg2 : ((MMP.Chow.twistMod H A n (m + 1)).presheaf.germ V y hy).hom
      ((X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (c j) : Γ(X, V)) •
        (MMP.Chow.coordMul H A (τ j) n m).app V s) =
      (X.presheaf.germ V y hy).hom (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (c j)) •
        ((MMP.Chow.twistMod H A n (m + 1)).presheaf.germ V y hy).hom
          ((MMP.Chow.coordMul H A (τ j) n m).app V s) :=
    PresheafOfModules.germ_smul (M := (MMP.Chow.twistMod H A n (m + 1)).val) y V hy _ _
  rw [hg2, X.presheaf.germ_res_apply, map_smul, LinearMap.smul_apply, h2 j]
  rfl

open Stacks.EnriquesSeveriZariski in
/-- Where `τ` does not vanish, multiplication by any `σ` is, on stalks, the coordinate of `σ` in
the stalk basis `τ` times multiplication by `τ`. -/
theorem stalk_coordMul_eq_coord_smul (σ τ : Γ(H, ⊤)) {y : X}
    (hτ : y ∈ Stacks.Ample.nonvanishingLocus H τ) (n : ℕ) (m : ℤ)
    (z : (MMP.Chow.twistMod H A n m).presheaf.stalk y) :
    stalkLinearMap _ _ (MMP.Chow.coordMul H A σ n m) y z =
      (isStalkBasis_Γgerm_of_mem_nonvanishingLocus H τ hτ).coord
          ((H.presheaf.Γgerm y).hom σ) • stalkLinearMap _ _ (MMP.Chow.coordMul H A τ n m) y z := by
  set hb := isStalkBasis_Γgerm_of_mem_nonvanishingLocus H τ hτ
  obtain ⟨F, -, hF⟩ := stalk_coordMul H A n m y
  have hs : stalkLinearMap _ _ (sectionHom H σ) y =
      hb.coord ((H.presheaf.Γgerm y).hom σ) • stalkLinearMap _ _ (sectionHom H τ) y := by
    ext z
    rw [stalkLinearMap_sectionHom, LinearMap.smul_apply, stalkLinearMap_sectionHom]
    conv_lhs => rw [← hb.smul_coord ((H.presheaf.Γgerm y).hom σ)]
    rw [smul_comm]
  rw [hF σ, hF τ, hs, map_smul]
  rfl

end CoordMulStalk

section LinearFormSection

open Stacks.Ample

/-- A point of `Proj` at which a linear form `f` does not vanish lies in the nonvanishing locus
of the degree-one section defined by `f`. -/
theorem mem_nonvanishingLocus_degreeSection_one {k : Type u} [Field k] {N : ℕ}
    (f : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 1)
    (p : AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))
    (hp : (f : MvPolynomial (Fin (N + 1)) k) ∉ p.asHomogeneousIdeal) :
    p ∈ Stacks.Ample.nonvanishingLocus (X := AlgebraicGeometry.Proj _)
      (ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) 1)
      (ProjectiveSpectrum.Proj.degreeSection _ 1 f) := by
  refine (Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) 1 1 f (x := p) ?_).2 hp
  rw [Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.whereInvertible_eq_top _
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (N + 1)) k) one_pos]
  trivial

/-- Pulling back global sections is semilinear along `f.appTop`. -/
theorem pullbackGlobalSections_smul {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules) (r : Γ(Y, ⊤))
    (s : Γ(F, ⊤)) :
    pullbackGlobalSections f F (r • s) = f.appTop r • pullbackGlobalSections f F s := by
  unfold pullbackGlobalSections
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, Scheme.Modules.Hom.app_smul]
  refine (Scheme.Modules.map_smul ((Scheme.Modules.pullback f).obj F) _ (f.app ⊤ r) _).trans ?_
  congr 1
  rw [eqToHom_op, eqToHom_map]
  rfl

/-- Pulling back global sections commutes with finite sums. -/
theorem pullbackGlobalSections_sum {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules) {ι : Type*}
    (t : Finset ι) (s : ι → Γ(F, ⊤)) :
    pullbackGlobalSections f F (∑ j ∈ t, s j) = ∑ j ∈ t, pullbackGlobalSections f F (s j) :=
  map_sum (pullbackGlobalSections f F).hom s t

/-- The linear form `∑ C(aⱼ) Xⱼ` is homogeneous of degree one. -/
theorem linForm_mem {k : Type u} [Field k] {N : ℕ} (a : Fin (N + 1) → k) :
    (∑ j, MvPolynomial.C (a j) * X j : MvPolynomial (Fin (N + 1)) k) ∈
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 1 := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => by
    simpa using (MvPolynomial.isHomogeneous_X k j).C_mul (a j)

/-- The degree-one section of the linear form `∑ aⱼ Xⱼ` is `∑ aⱼ` times the sections of the
coordinates `Xⱼ`. -/
theorem degreeSection_linForm {k : Type u} [Field k] {N : ℕ} (a : Fin (N + 1) → k) :
    Stacks.ProjectiveSpace.Cohomology.degreeSectionCoeff k N 1 ⟨_, linForm_mem a⟩ =
      ∑ j, a j • Stacks.ProjectiveSpace.Cohomology.degreeSectionCoeff k N 1
          ⟨X j, (MvPolynomial.mem_homogeneousSubmodule _ _).2
            (MvPolynomial.isHomogeneous_X k j)⟩ := by
  have e : (⟨_, linForm_mem a⟩ : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 1) =
      ∑ j, a j • ⟨X j, (MvPolynomial.mem_homogeneousSubmodule _ _).2
        (MvPolynomial.isHomogeneous_X k j)⟩ := by
    apply Subtype.ext
    simp [Submodule.coe_sum, MvPolynomial.smul_eq_C_mul]
  show Stacks.ProjectiveSpace.Cohomology.degreeSectionLinear k N 1 ⟨_, linForm_mem a⟩ =
    ∑ j, a j • Stacks.ProjectiveSpace.Cohomology.degreeSectionLinear k N 1 _
  rw [e, map_sum]
  simp only [map_smul]
  rfl

end LinearFormSection

section BaseChangeMatrices

attribute [local instance 10000] HasDerivedCategory.standard

/-- `restrSec` is natural in the module. -/
theorem restrSec_natural {Y T : Scheme.{u}} (π : Y ⟶ T) (V : T.Opens) {L L' : Y.Modules}
    (φ : L ⟶ L') (s : Γ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L, ⊤)) :
    restrSec π V L' (((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).map φ).app ⊤ s) =
      φ.app (π ⁻¹ᵁ V) (restrSec π V L s) := by
  have h1 := (Scheme.Modules.restrictFunctorIsoPullback (π ⁻¹ᵁ V).ι).inv.naturality φ
  have h2 := congrArg (fun f => ConcreteCategory.hom (Scheme.Modules.Hom.app f ⊤) s) h1
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h2
  show L'.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (π ⁻¹ᵁ V)).symm).op
      (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback (π ⁻¹ᵁ V).ι).inv.app L') ⊤
        (((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).map φ).app ⊤ s)) =
    φ.app (π ⁻¹ᵁ V) (L.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (π ⁻¹ᵁ V)).symm).op
      (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback (π ⁻¹ᵁ V).ι).inv.app L)
        ⊤ s))
  rw [h2]
  exact (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality
    (eqToHom (Scheme.Opens.ι_image_top (π ⁻¹ᵁ V)).symm).op) _).symm

/-- The matrix of a base change `ψ` of `φ`, in the base-changed bases, is the matrix of `φ`
with its entries mapped along `algebraMap R S`. -/
theorem toMatrix_isBaseChange {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M M' N N' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [AddCommGroup N'] [Module R N'] [Module S N'] [IsScalarTower R S N']
    {β : M →ₗ[R] N} {β' : M' →ₗ[R] N'} (hβ : IsBaseChange S β) (hβ' : IsBaseChange S β')
    {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    (b : Module.Basis ι R M) (b' : Module.Basis ι' R M') (φ : M →ₗ[R] M') (ψ : N →ₗ[S] N')
    (hcomm : ∀ m, ψ (β m) = β' (φ m)) :
    LinearMap.toMatrix (hβ.basis b) (hβ'.basis b') ψ =
      (LinearMap.toMatrix b b' φ).map (algebraMap R S) := by
  ext i j
  rw [LinearMap.toMatrix_apply, IsBaseChange.basis_apply, hcomm, IsBaseChange.basis_repr_comp_apply,
    Matrix.map_apply, LinearMap.toMatrix_apply]

/-- Multiplying the matrix of `f` by a coordinate vector `v` gives the coordinates of `f`
applied to the vector with coordinates `v`. -/
theorem toMatrix_mulVec_eq {K : Type*} [CommRing K] {r r' : ℕ} {G G' : Type*} [AddCommGroup G]
    [Module K G] [AddCommGroup G'] [Module K G'] (B : Module.Basis (Fin r) K G)
    (B' : Module.Basis (Fin r') K G') (f : G →ₗ[K] G') (v : Fin r → K) :
    (LinearMap.toMatrix B B' f).mulVec v = B'.equivFun (f (B.equivFun.symm v)) := by
  conv_lhs => rw [← B.equivFun.apply_symm_apply v]
  simp only [Module.Basis.equivFun_apply]
  exact LinearMap.toMatrix_mulVec_repr B B' f (B.equivFun.symm v)

/-- If `(αa, αb)` is jointly injective, then the stacked matrix of `(-αb, αa)` is injective. -/
theorem matrix_koszul_injective {K : Type*} [CommRing K] {G₂ G₁ : Type*} [AddCommGroup G₂]
    [Module K G₂] [AddCommGroup G₁] [Module K G₁] {r₂ r₁ : ℕ}
    (B₂ : Module.Basis (Fin r₂) K G₂) (B₁ : Module.Basis (Fin r₁) K G₁) (αa αb : G₂ →ₗ[K] G₁)
    (hinj : ∀ w, αa w = 0 → αb w = 0 → w = 0) :
    Function.Injective (Matrix.fromRows (-(LinearMap.toMatrix B₂ B₁ αb))
      (LinearMap.toMatrix B₂ B₁ αa)).mulVec := by
  intro v v' h
  have h1 := congrFun h
  rw [← sub_eq_zero]
  apply B₂.equivFun.symm.injective
  rw [map_zero, map_sub]
  refine hinj _ ?_ ?_
  · have := funext fun i => h1 (Sum.inr i)
    simp only [Matrix.fromRows_mulVec, Sum.elim_inr] at this
    rw [toMatrix_mulVec_eq, toMatrix_mulVec_eq] at this
    rw [map_sub, sub_eq_zero]
    exact B₁.equivFun.injective this
  · have := funext fun i => h1 (Sum.inl i)
    simp only [Matrix.fromRows_mulVec, Sum.elim_inl, Matrix.neg_mulVec, Pi.neg_apply] at this
    have h2 : (LinearMap.toMatrix B₂ B₁ αb).mulVec v =
        (LinearMap.toMatrix B₂ B₁ αb).mulVec v' :=
      funext fun i => neg_inj.mp (congrFun this i)
    rw [toMatrix_mulVec_eq, toMatrix_mulVec_eq] at h2
    rw [map_sub, sub_eq_zero]
    exact B₁.equivFun.injective h2

/-- If every `(s, t)` with `α'a s + α'b t = 0` is `(-αb w, αa w)`, then the image of the
stacked matrix of `(-αb, αa)` contains the kernel of the matrix of `(α'a, α'b)`. -/
theorem matrix_koszul_exists {K : Type*} [CommRing K] {G₂ G₁ G₀ : Type*} [AddCommGroup G₂]
    [Module K G₂] [AddCommGroup G₁] [Module K G₁] [AddCommGroup G₀] [Module K G₀] {r₂ r₁ r₀ : ℕ}
    (B₂ : Module.Basis (Fin r₂) K G₂) (B₁ : Module.Basis (Fin r₁) K G₁)
    (B₀ : Module.Basis (Fin r₀) K G₀) (αa αb : G₂ →ₗ[K] G₁) (α'a α'b : G₁ →ₗ[K] G₀)
    (hex : ∀ s t, α'a s + α'b t = 0 → ∃ w, -(αb w) = s ∧ αa w = t) (v : Fin r₁ ⊕ Fin r₁ → K)
    (hv : (Matrix.fromCols (LinearMap.toMatrix B₁ B₀ α'a)
      (LinearMap.toMatrix B₁ B₀ α'b)).mulVec v = 0) :
    ∃ w, (Matrix.fromRows (-(LinearMap.toMatrix B₂ B₁ αb))
      (LinearMap.toMatrix B₂ B₁ αa)).mulVec w = v := by
  have hst : α'a (B₁.equivFun.symm (v ∘ Sum.inl)) + α'b (B₁.equivFun.symm (v ∘ Sum.inr)) = 0 := by
    apply B₀.equivFun.injective
    rw [map_add, map_zero, ← toMatrix_mulVec_eq, ← toMatrix_mulVec_eq]
    have : v = Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) := by ext (i | i) <;> rfl
    rwa [this, Matrix.fromCols_mulVec_sumElim] at hv
  obtain ⟨w, hw1, hw2⟩ := hex _ _ hst
  refine ⟨B₂.equivFun w, ?_⟩
  ext (i | i)
  · simp only [Matrix.fromRows_mulVec, Sum.elim_inl, Matrix.neg_mulVec, Pi.neg_apply]
    rw [toMatrix_mulVec_eq, LinearEquiv.symm_apply_apply, ← Pi.neg_apply, ← map_neg, hw1,
      LinearEquiv.apply_symm_apply]
    rfl
  · simp only [Matrix.fromRows_mulVec, Sum.elim_inr]
    rw [toMatrix_mulVec_eq, LinearEquiv.symm_apply_apply, hw2, LinearEquiv.apply_symm_apply]
    rfl

/-- If `(αa, αb)` is jointly injective and every `(s, t)` with `α'a s + α'b t = 0` is
`(-αb w, αa w)`, then the stacked matrix of `(-αb, αa)` is injective and its image is the
kernel of the matrix of `(α'a, α'b)`. -/
theorem matrix_koszul {K : Type*} [CommRing K] {G₂ G₁ G₀ : Type*} [AddCommGroup G₂] [Module K G₂]
    [AddCommGroup G₁] [Module K G₁] [AddCommGroup G₀] [Module K G₀] {r₂ r₁ r₀ : ℕ}
    (B₂ : Module.Basis (Fin r₂) K G₂) (B₁ : Module.Basis (Fin r₁) K G₁)
    (B₀ : Module.Basis (Fin r₀) K G₀) (αa αb : G₂ →ₗ[K] G₁) (α'a α'b : G₁ →ₗ[K] G₀)
    (hinj : ∀ w, αa w = 0 → αb w = 0 → w = 0)
    (hex : ∀ s t, α'a s + α'b t = 0 → ∃ w, -(αb w) = s ∧ αa w = t) :
    Function.Injective (Matrix.fromRows (-(LinearMap.toMatrix B₂ B₁ αb))
      (LinearMap.toMatrix B₂ B₁ αa)).mulVec ∧
    ∀ v, (Matrix.fromCols (LinearMap.toMatrix B₁ B₀ α'a)
        (LinearMap.toMatrix B₁ B₀ α'b)).mulVec v = 0 →
      ∃ w, (Matrix.fromRows (-(LinearMap.toMatrix B₂ B₁ αb))
        (LinearMap.toMatrix B₂ B₁ αa)).mulVec w = v :=
  ⟨matrix_koszul_injective B₂ B₁ αa αb hinj, matrix_koszul_exists B₂ B₁ B₀ αa αb α'a α'b hex⟩

/-- The matrix of `φ` in the bases transported along `ea` and `eb` is the matrix of any `χ`
with `eb ∘ φ = χ ∘ ea`. -/
theorem toMatrix_map_symm {R : Type*} [CommRing R] {Ma Mb Pa Pb : Type*} [AddCommGroup Ma]
    [AddCommGroup Mb] [AddCommGroup Pa] [AddCommGroup Pb] [Module R Ma] [Module R Mb] [Module R Pa]
    [Module R Pb] {ra rb : ℕ} (ea : Ma ≃ₗ[R] Pa) (eb : Mb ≃ₗ[R] Pb)
    (ba : Module.Basis (Fin ra) R Pa) (bb : Module.Basis (Fin rb) R Pb) (φ : Ma →ₗ[R] Mb)
    (χ : Pa →ₗ[R] Pb) (h : ∀ m, eb (φ m) = χ (ea m)) :
    LinearMap.toMatrix (ba.map ea.symm) (bb.map eb.symm) φ = LinearMap.toMatrix ba bb χ := by
  ext i j
  simp [LinearMap.toMatrix_apply, h]

/-- An additive map commuting with scalars, as a linear map. -/
def linOfSmul {K A B : Type*} [CommRing K] [AddCommGroup A] [AddCommGroup B] [Module K A]
    [Module K B] (f : A →+ B) (hf : ∀ (c : K) x, f (c • x) = c • f x) : A →ₗ[K] B :=
  { toFun := f, map_add' := f.map_add, map_smul' := hf }

/-- If the base changes `ψ` to `K` of the maps `φ` form an exact two-term Koszul complex, then
the matrices of the corresponding `χ`, with entries mapped to `K`, are injective and exact. -/
theorem koszul_matrices_of_isBaseChange {R K : Type*} [CommRing R] [Field K] {_ : Algebra R K}
    {M₂ M₁ M₀ P₂ P₁ P₀ N₂ N₁ N₀ : Type*}
    [AddCommGroup M₂] [AddCommGroup M₁] [AddCommGroup M₀]
    [AddCommGroup P₂] [AddCommGroup P₁] [AddCommGroup P₀]
    [AddCommGroup N₂] [AddCommGroup N₁] [AddCommGroup N₀]
    {_ : Module R M₂} {_ : Module R M₁} {_ : Module R M₀}
    {_ : Module R P₂} {_ : Module R P₁} {_ : Module R P₀}
    {_ : Module R N₂} {_ : Module R N₁} {_ : Module R N₀}
    {_ : Module K N₂} {_ : Module K N₁} {_ : Module K N₀}
    {_ : IsScalarTower R K N₂} {_ : IsScalarTower R K N₁} {_ : IsScalarTower R K N₀}
    {β₂ : M₂ →ₗ[R] N₂} {β₁ : M₁ →ₗ[R] N₁} {β₀ : M₀ →ₗ[R] N₀}
    (h₂ : IsBaseChange K β₂) (h₁ : IsBaseChange K β₁) (h₀ : IsBaseChange K β₀)
    (e₂ : M₂ ≃ₗ[R] P₂) (e₁ : M₁ ≃ₗ[R] P₁) (e₀ : M₀ ≃ₗ[R] P₀)
    {r₂ r₁ r₀ : ℕ} (b₂ : Module.Basis (Fin r₂) R P₂) (b₁ : Module.Basis (Fin r₁) R P₁)
    (b₀ : Module.Basis (Fin r₀) R P₀)
    (φa φb : M₂ →ₗ[R] M₁) (φ'a φ'b : M₁ →ₗ[R] M₀)
    (χa χb : P₂ →ₗ[R] P₁) (χ'a χ'b : P₁ →ₗ[R] P₀)
    (hχa : ∀ m, e₁ (φa m) = χa (e₂ m)) (hχb : ∀ m, e₁ (φb m) = χb (e₂ m))
    (hχ'a : ∀ m, e₀ (φ'a m) = χ'a (e₁ m)) (hχ'b : ∀ m, e₀ (φ'b m) = χ'b (e₁ m))
    (ψa ψb : N₂ →+ N₁) (ψ'a ψ'b : N₁ →+ N₀)
    (hsa : ∀ (c : K) x, ψa (c • x) = c • ψa x) (hsb : ∀ (c : K) x, ψb (c • x) = c • ψb x)
    (hs'a : ∀ (c : K) x, ψ'a (c • x) = c • ψ'a x) (hs'b : ∀ (c : K) x, ψ'b (c • x) = c • ψ'b x)
    (hca : ∀ m, ψa (β₂ m) = β₁ (φa m)) (hcb : ∀ m, ψb (β₂ m) = β₁ (φb m))
    (hc'a : ∀ m, ψ'a (β₁ m) = β₀ (φ'a m)) (hc'b : ∀ m, ψ'b (β₁ m) = β₀ (φ'b m))
    (hinj : ∀ w, ψa w = 0 → ψb w = 0 → w = 0)
    (hex : ∀ s t, ψ'a s + ψ'b t = 0 → ∃ w, -(ψb w) = s ∧ ψa w = t) :
    Function.Injective (Matrix.fromRows (-((LinearMap.toMatrix b₂ b₁ χb).map (algebraMap R K)))
      ((LinearMap.toMatrix b₂ b₁ χa).map (algebraMap R K))).mulVec ∧
    ∀ v, (Matrix.fromCols ((LinearMap.toMatrix b₁ b₀ χ'a).map (algebraMap R K))
        ((LinearMap.toMatrix b₁ b₀ χ'b).map (algebraMap R K))).mulVec v = 0 →
      ∃ w, (Matrix.fromRows (-((LinearMap.toMatrix b₂ b₁ χb).map (algebraMap R K)))
        ((LinearMap.toMatrix b₂ b₁ χa).map (algebraMap R K))).mulVec w = v := by
  have hA := toMatrix_isBaseChange h₂ h₁ (b₂.map e₂.symm) (b₁.map e₁.symm) φa (linOfSmul ψa hsa) hca
  have hB := toMatrix_isBaseChange h₂ h₁ (b₂.map e₂.symm) (b₁.map e₁.symm) φb (linOfSmul ψb hsb) hcb
  have hA' := toMatrix_isBaseChange h₁ h₀ (b₁.map e₁.symm) (b₀.map e₀.symm) φ'a
    (linOfSmul ψ'a hs'a) hc'a
  have hB' := toMatrix_isBaseChange h₁ h₀ (b₁.map e₁.symm) (b₀.map e₀.symm) φ'b
    (linOfSmul ψ'b hs'b) hc'b
  rw [toMatrix_map_symm e₂ e₁ b₂ b₁ φa χa hχa] at hA
  rw [toMatrix_map_symm e₂ e₁ b₂ b₁ φb χb hχb] at hB
  rw [toMatrix_map_symm e₁ e₀ b₁ b₀ φ'a χ'a hχ'a] at hA'
  rw [toMatrix_map_symm e₁ e₀ b₁ b₀ φ'b χ'b hχ'b] at hB'
  rw [← hA, ← hB, ← hA', ← hB']
  exact matrix_koszul _ _ _ _ _ _ _ hinj hex

open Stacks.AlgebraicGeometry.ProperFlatGlobalSections
  AlgebraicGeometry.ProperFlatFibreEulerCharacteristic in
/-- On an affine open `V` over which the invertible modules `N₂, N₁, N₀` restricted to
`π ⁻¹ᵁ V` have no higher cohomology, if the two-term Koszul complex on the fibre over
`t ∈ V` is exact, then so is the corresponding matrix complex of direct image sections reduced
to the residue field of `t`. -/
theorem fibre_koszul {Y T : Scheme.{u}} (π : Y ⟶ T) [IsProper π] [Flat π] {V : T.Opens}
    (hV : IsAffineOpen V) (N₂ N₁ N₀ : Y.Modules)
    (hN₂ : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N₂)
    (hN₁ : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N₁)
    (hN₀ : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N₀)
    (hv₂ : ∀ p : ℕ, 0 < p → Subsingleton
      (((AlgebraicGeometry.moduleGlobalSections (π ⁻¹ᵁ V)).rightDerived p).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj N₂)))
    (hv₁ : ∀ p : ℕ, 0 < p → Subsingleton
      (((AlgebraicGeometry.moduleGlobalSections (π ⁻¹ᵁ V)).rightDerived p).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj N₁)))
    (hv₀ : ∀ p : ℕ, 0 < p → Subsingleton
      (((AlgebraicGeometry.moduleGlobalSections (π ⁻¹ᵁ V)).rightDerived p).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj N₀)))
    {r₂ r₁ r₀ : ℕ} (b₂ : Module.Basis (Fin r₂) Γ(T, V) Γ((Scheme.Modules.pushforward π).obj N₂, V))
    (b₁ : Module.Basis (Fin r₁) Γ(T, V) Γ((Scheme.Modules.pushforward π).obj N₁, V))
    (b₀ : Module.Basis (Fin r₀) Γ(T, V) Γ((Scheme.Modules.pushforward π).obj N₀, V))
    (αa αb : N₂ ⟶ N₁) (α'a α'b : N₁ ⟶ N₀) (t : T) (ht : t ∈ V)
    (hinj : ∀ w, ((Scheme.Modules.pullback (fiberιOfMem π t ht)).map
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).map αa)).app ⊤ w = 0 →
      ((Scheme.Modules.pullback (fiberιOfMem π t ht)).map
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).map αb)).app ⊤ w = 0 → w = 0)
    (hex : ∀ s s', ((Scheme.Modules.pullback (fiberιOfMem π t ht)).map
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).map α'a)).app ⊤ s +
      ((Scheme.Modules.pullback (fiberιOfMem π t ht)).map
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).map α'b)).app ⊤ s' = 0 →
      ∃ w, -(((Scheme.Modules.pullback (fiberιOfMem π t ht)).map
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).map αb)).app ⊤ w) = s ∧
        ((Scheme.Modules.pullback (fiberιOfMem π t ht)).map
          ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).map αa)).app ⊤ w = s') :
    Function.Injective (Matrix.fromRows
      (-((LinearMap.toMatrix b₂ b₁ (MMP.Chow.directImageSectionsMap π V αb)).map
        (residueOfMem t ht).hom))
      ((LinearMap.toMatrix b₂ b₁ (MMP.Chow.directImageSectionsMap π V αa)).map
        (residueOfMem t ht).hom)).mulVec ∧
    ∀ v, (Matrix.fromCols
        ((LinearMap.toMatrix b₁ b₀ (MMP.Chow.directImageSectionsMap π V α'a)).map
          (residueOfMem t ht).hom)
        ((LinearMap.toMatrix b₁ b₀ (MMP.Chow.directImageSectionsMap π V α'b)).map
          (residueOfMem t ht).hom)).mulVec v = 0 →
      ∃ w, (Matrix.fromRows
        (-((LinearMap.toMatrix b₂ b₁ (MMP.Chow.directImageSectionsMap π V αb)).map
          (residueOfMem t ht).hom))
        ((LinearMap.toMatrix b₂ b₁ (MMP.Chow.directImageSectionsMap π V αa)).map
          (residueOfMem t ht).hom)).mulVec w = v := by
  set ι := (π ⁻¹ᵁ V).ι
  set f := (π ∣_ V) ≫ hV.isoSpec.hom
  set g := fiberιOfMem π t ht
  haveI : Flat f := inferInstance
  have hflat : ∀ L : Y.Modules, Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L →
      ((Scheme.Modules.pullback ι).obj L).IsQuasicoherent ∧
        IsFlatOver f.toLRSHom.toShHom ((Scheme.Modules.pullback ι).obj L) := fun L hL => by
    have hF : Stacks.SheafOfModules.IsInvertible (π ⁻¹ᵁ V).toScheme.presheaf
        (π ⁻¹ᵁ V).toScheme.ringCatSheaf.2 ((Scheme.Modules.pullback ι).obj L) :=
      Stacks.RingedSpace.modulePullback_isInvertible_of ι.toLRSHom.toShHom L hL
    haveI := Stacks.Picard.isQuasicoherent_of_isInvertible _ hF
    exact ⟨inferInstance, (isFinitePresentation_and_isFlatOver_of_isInvertible f _ hF).2⟩
  obtain ⟨hq₂, hf₂⟩ := hflat N₂ hN₂
  obtain ⟨hq₁, hf₁⟩ := hflat N₁ hN₁
  obtain ⟨hq₀, hf₀⟩ := hflat N₀ hN₀
  obtain ⟨-, h₂⟩ := cohomologyBaseChange_of_vanishing f _ hf₂ hv₂ (residueOfMem t ht).hom
    (isPullback_fiberιOfMem π hV t ht)
  obtain ⟨-, h₁⟩ := cohomologyBaseChange_of_vanishing f _ hf₁ hv₁ (residueOfMem t ht).hom
    (isPullback_fiberιOfMem π hV t ht)
  obtain ⟨-, h₀⟩ := cohomologyBaseChange_of_vanishing f _ hf₀ hv₀ (residueOfMem t ht).hom
    (isPullback_fiberιOfMem π hV t ht)
  letI := Stacks.Cech.sectionsModule f ((Scheme.Modules.pullback ι).obj N₂) ⊤
  letI := Stacks.Cech.sectionsModule f ((Scheme.Modules.pullback ι).obj N₁) ⊤
  letI := Stacks.Cech.sectionsModule f ((Scheme.Modules.pullback ι).obj N₀) ⊤
  let Φa : Γ((Scheme.Modules.pullback ι).obj N₂, ⊤) →ₗ[Γ(T, V)]
      Γ((Scheme.Modules.pullback ι).obj N₁, ⊤) :=
    linOfSmul (((Scheme.Modules.pullback ι).map αa).app ⊤).hom
      (fun c x => Scheme.Modules.Hom.app_smul _ _ _)
  let Φb : Γ((Scheme.Modules.pullback ι).obj N₂, ⊤) →ₗ[Γ(T, V)]
      Γ((Scheme.Modules.pullback ι).obj N₁, ⊤) :=
    linOfSmul (((Scheme.Modules.pullback ι).map αb).app ⊤).hom
      (fun c x => Scheme.Modules.Hom.app_smul _ _ _)
  let Φ'a : Γ((Scheme.Modules.pullback ι).obj N₁, ⊤) →ₗ[Γ(T, V)]
      Γ((Scheme.Modules.pullback ι).obj N₀, ⊤) :=
    linOfSmul (((Scheme.Modules.pullback ι).map α'a).app ⊤).hom
      (fun c x => Scheme.Modules.Hom.app_smul _ _ _)
  let Φ'b : Γ((Scheme.Modules.pullback ι).obj N₁, ⊤) →ₗ[Γ(T, V)]
      Γ((Scheme.Modules.pullback ι).obj N₀, ⊤) :=
    linOfSmul (((Scheme.Modules.pullback ι).map α'b).app ⊤).hom
      (fun c x => Scheme.Modules.Hom.app_smul _ _ _)
  exact koszul_matrices_of_isBaseChange h₂ h₁ h₀ (restrSecₗ π hV N₂) (restrSecₗ π hV N₁)
    (restrSecₗ π hV N₀) b₂ b₁ b₀ Φa Φb Φ'a Φ'b
    (MMP.Chow.directImageSectionsMap π V αa) (MMP.Chow.directImageSectionsMap π V αb)
    (MMP.Chow.directImageSectionsMap π V α'a) (MMP.Chow.directImageSectionsMap π V α'b)
    (fun m => restrSec_natural π V αa m) (fun m => restrSec_natural π V αb m)
    (fun m => restrSec_natural π V α'a m) (fun m => restrSec_natural π V α'b m)
    (((Scheme.Modules.pullback g).map ((Scheme.Modules.pullback ι).map αa)).app (g ⁻¹ᵁ ⊤)).hom
    (((Scheme.Modules.pullback g).map ((Scheme.Modules.pullback ι).map αb)).app (g ⁻¹ᵁ ⊤)).hom
    (((Scheme.Modules.pullback g).map ((Scheme.Modules.pullback ι).map α'a)).app (g ⁻¹ᵁ ⊤)).hom
    (((Scheme.Modules.pullback g).map ((Scheme.Modules.pullback ι).map α'b)).app (g ⁻¹ᵁ ⊤)).hom
    (fun c x => Scheme.Modules.Hom.app_smul _ _ _) (fun c x => Scheme.Modules.Hom.app_smul _ _ _)
    (fun c x => Scheme.Modules.Hom.app_smul _ _ _) (fun c x => Scheme.Modules.Hom.app_smul _ _ _)
    (fun m => (unit_naturality_apply g _ ⊤ m).symm) (fun m => (unit_naturality_apply g _ ⊤ m).symm)
    (fun m => (unit_naturality_apply g _ ⊤ m).symm) (fun m => (unit_naturality_apply g _ ⊤ m).symm)
    hinj hex

end BaseChangeMatrices

end FibreKoszul

section FibrePolyAlgebra

open Matrix

section Complement

variable {κ : Type*} [Field κ] {ι ι' δ : Type*} [Fintype ι] [Fintype ι'] [Fintype δ]
  [DecidableEq ι] [DecidableEq ι'] [DecidableEq δ]

/-- An injective matrix extends to an invertible one. -/
theorem exists_isUnit_det_fromCols (L : Matrix ι' ι κ) (hL : Function.Injective L.mulVec)
    (ρ : ι' ≃ ι ⊕ δ) : ∃ J : Matrix ι' δ κ, IsUnit ((fromCols L J).submatrix id ρ).det := by
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl (LinearMap.range L.mulVecLin)
  have hr : Module.finrank κ (LinearMap.range L.mulVecLin) = Fintype.card ι := by
    rw [LinearMap.finrank_range_of_inj hL, Module.finrank_fintype_fun_eq_card]
  have hsum := Submodule.finrank_add_eq_of_isCompl hW'
  have hcard : Fintype.card ι' = Fintype.card ι + Fintype.card δ := by
    rw [Fintype.card_congr ρ, Fintype.card_sum]
  have hW : Module.finrank κ W' = Fintype.card δ := by
    rw [Module.finrank_fintype_fun_eq_card, hr] at hsum
    omega
  let b : Module.Basis δ κ W' := Module.Basis.reindex (Module.finBasis κ W')
    (Fintype.equivOfCardEq (by rw [Fintype.card_fin, hW]))
  let J : Matrix ι' δ κ := Matrix.of fun i j => (b j : ι' → κ) i
  refine ⟨J, (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_surjective_iff_isUnit.1 ?_)⟩
  intro x
  obtain ⟨_, ⟨y, rfl⟩, w, hw, hxw⟩ :=
    Submodule.mem_sup.1 (hW'.sup_eq_top ▸ Submodule.mem_top : x ∈ _ ⊔ W')
  refine ⟨Sum.elim y (b.repr ⟨w, hw⟩) ∘ ρ, ?_⟩
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id,
    Matrix.fromCols_mulVec_sumElim]
  rw [← hxw]
  congr 1
  have h2 := congrArg (fun z : W' => (z : ι' → κ)) (b.sum_repr ⟨w, hw⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  conv_rhs => rw [← h2]
  funext i
  simp [Matrix.mulVec, dotProduct, J, Finset.sum_apply, mul_comm]

end Complement

section Factor

variable {k σ : Type*} [Field k] [IsAlgClosed k] [Finite σ]

/-- An irreducible polynomial vanishing only where some `g i` vanishes, or where both `h j` and
`h' j` vanish, divides some `g i`, as soon as it divides no pair `(h j, h' j)`. -/
theorem exists_dvd_of_zeroLocus_subset {ι κ : Type*} {H : MvPolynomial σ k} (hH : Irreducible H)
    (s : Finset ι) (g : ι → MvPolynomial σ k) (t : Finset κ) (h h' : κ → MvPolynomial σ k)
    (hc : ∀ j ∈ t, ¬ (H ∣ h j ∧ H ∣ h' j))
    (hZ : ∀ x, eval x H = 0 → (∃ i ∈ s, eval x (g i) = 0) ∨
      ∃ j ∈ t, eval x (h j) = 0 ∧ eval x (h' j) = 0) :
    ∃ i ∈ s, H ∣ g i := by
  classical
  let kk : κ → MvPolynomial σ k := fun j => if H ∣ h j then h' j else h j
  have hk : ∀ j ∈ t, ¬ H ∣ kk j := by
    intro j hj
    simp only [kk]
    split_ifs with h1
    · exact fun h2 => hc j hj ⟨h1, h2⟩
    · exact h1
  set F := (∏ i ∈ s, g i) * ∏ j ∈ t, kk j
  have hF : F ∈ vanishingIdeal k (zeroLocus k (Ideal.span {H})) := by
    rw [mem_vanishingIdeal_iff]
    intro x hx
    rw [mem_zeroLocus_iff] at hx
    have hx' : eval x H = 0 := by simpa using hx H (Ideal.subset_span rfl)
    show eval x F = 0
    simp only [F, map_mul, map_prod]
    rcases hZ x hx' with ⟨i, hi, hgi⟩ | ⟨j, hj, h1, h2⟩
    · rw [Finset.prod_eq_zero hi hgi, zero_mul]
    · refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hj ?_)
      simp only [kk]
      split_ifs <;> assumption
  have hp : (Ideal.span {H}).IsPrime := (Ideal.span_singleton_prime hH.ne_zero).mpr hH.prime
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus, Ideal.mem_span_singleton] at hF
  rcases hH.prime.dvd_or_dvd hF with h1 | h1
  · exact (Prime.dvd_finset_prod_iff hH.prime _).1 h1
  · obtain ⟨j, hj, hd⟩ := (Prime.dvd_finset_prod_iff hH.prime _).1 h1
    exact absurd hd (hk j hj)

/-- **A polynomial whose zeros lie on given irreducible hypersurfaces (and on intersections of
coprime pairs) is a product of their equations.** -/
theorem exists_eq_C_mul_prod_pow_of_zeroLocus_subset {ι κ : Type*} (s : Finset ι)
    (g : ι → MvPolynomial σ k) (hg : ∀ i ∈ s, Irreducible (g i)) (t : Finset κ)
    (h h' : κ → MvPolynomial σ k)
    (hc : ∀ j ∈ t, ∀ H : MvPolynomial σ k, Irreducible H → ¬ (H ∣ h j ∧ H ∣ h' j))
    (P : MvPolynomial σ k) (hP : P ≠ 0)
    (hZ : ∀ x, eval x P = 0 → (∃ i ∈ s, eval x (g i) = 0) ∨
      ∃ j ∈ t, eval x (h j) = 0 ∧ eval x (h' j) = 0) :
    ∃ (l : k) (e : ι → ℕ), l ≠ 0 ∧ P = C l * ∏ i ∈ s, g i ^ e i := by
  classical
  induction P using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hP
  | h₂ x hx =>
    obtain ⟨l, hl, rfl⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 hx
    exact ⟨l, 0, hl.ne_zero, by simp⟩
  | h₃ a p ha hp ih =>
    have hpa : a ≠ 0 := fun h => hP (by rw [h, mul_zero])
    obtain ⟨l, e, hl, rfl⟩ := ih hpa fun x hx => hZ x (by rw [map_mul, hx, mul_zero])
    obtain ⟨i, hi, hdi⟩ := exists_dvd_of_zeroLocus_subset hp.irreducible s g t h h'
      (fun j hj => hc j hj p hp.irreducible)
      (fun x hx => hZ x (by rw [map_mul, hx, zero_mul]))
    obtain ⟨w, hw⟩ : Associated p (g i) := by
      obtain ⟨c, hc'⟩ := hdi
      have := ((hg i hi).isUnit_or_isUnit hc').resolve_left hp.not_unit
      exact ⟨this.unit, hc'.symm ▸ rfl⟩
    obtain ⟨m, hm, hmw⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 (w⁻¹).isUnit
    have hp' : p = C m * g i := by
      rw [← hw, ← hmw, mul_comm, mul_assoc, Units.mul_inv, mul_one]
    refine ⟨m * l, Function.update e i (e i + 1), mul_ne_zero hm.ne_zero hl, ?_⟩
    rw [hp', ← Finset.mul_prod_erase s _ hi, ← Finset.mul_prod_erase s (fun j => g j ^ _) hi]
    have : ∏ j ∈ s.erase i, g j ^ Function.update e i (e i + 1) j = ∏ j ∈ s.erase i, g j ^ e j :=
      Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [this, Function.update_self, map_mul, pow_succ]
    ring

end Factor

section Weight

variable {k σ : Type*} [Field k] [Finite σ]

/-- Associated polynomials have the same total degree. -/
theorem totalDegree_of_associated {f f' : MvPolynomial σ k} (h : Associated f f') :
    f.totalDegree = f'.totalDegree := by
  obtain ⟨u, rfl⟩ := h
  obtain ⟨c, hc, hcu⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 u.isUnit
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rw [hcu, mul_comm, MvPolynomial.totalDegree_mul_of_isDomain (MvPolynomial.C_ne_zero.2 hc.ne_zero)
    hf, MvPolynomial.totalDegree_C, zero_add]

/-- The total degree of a product of nonzero polynomials is the sum of their total degrees. -/
theorem totalDegree_multiset_prod_eq (m : Multiset (MvPolynomial σ k)) (hm : ∀ f ∈ m, f ≠ 0) :
    m.prod.totalDegree = (m.map MvPolynomial.totalDegree).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      MvPolynomial.totalDegree_mul_of_isDomain (hm a (Multiset.mem_cons_self a m))
        (Multiset.prod_ne_zero fun h => hm 0 (Multiset.mem_cons_of_mem h) rfl),
      ih fun f hf => hm f (Multiset.mem_cons_of_mem hf)]

/-- A function to `ℕ` that is additive on products of nonzero elements and vanishes at `1` sends
a finite product of nonzero elements to the sum of its values. -/
theorem map_prod_eq_sum_of_map_mul {R γ : Type*} [CommMonoidWithZero R] [NoZeroDivisors R]
    [Nontrivial R] (W : R → ℕ) (h1 : W 1 = 0)
    (hmul : ∀ x x', x ≠ 0 → x' ≠ 0 → W (x * x') = W x + W x') (s : Finset γ) (f : γ → R)
    (hf : ∀ i ∈ s, f i ≠ 0) : W (∏ i ∈ s, f i) = ∑ i ∈ s, W (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, hmul _ _ (hf a (Finset.mem_insert_self a s))
      (Finset.prod_ne_zero_iff.2 fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- **Comparing exponents curve by curve.** If `∏_C F_C^{e_C}` is a nonzero constant times
`∏_y λ_y^{n_y}` with the `λ_y` irreducible of degree one, every irreducible factor of `F_C` is
associated to some `λ_y` with `y` over `C`, and `λ`'s over distinct `C` are not associated, then
`e_C · deg F_C = ∑_{y over C} n_y`. -/
theorem mul_totalDegree_eq_sum {α β : Type*} [DecidableEq β] (Z : Finset α)
    (lam : α → MvPolynomial σ k) (hlam : ∀ y ∈ Z, Irreducible (lam y))
    (hdeg : ∀ y ∈ Z, (lam y).totalDegree = 1) (n : α → ℕ) (T : Finset β)
    (F : β → MvPolynomial σ k) (hF : ∀ C ∈ T, F C ≠ 0) (e : β → ℕ) (cls : α → β) (c : k)
    (hc : c ≠ 0) (h1 : ∏ C ∈ T, F C ^ e C = MvPolynomial.C c * ∏ y ∈ Z, lam y ^ n y)
    (h2 : ∀ C ∈ T, ∀ H, Irreducible H → H ∣ F C → ∃ y ∈ Z, cls y = C ∧ Associated H (lam y))
    (h3 : ∀ y ∈ Z, ∀ y' ∈ Z, cls y ≠ cls y' → ¬ Associated (lam y) (lam y')) :
    ∀ C ∈ T, e C * (F C).totalDegree = ∑ y ∈ Z with cls y = C, n y := by
  classical
  letI : NormalizationMonoid (MvPolynomial σ k) :=
    UniqueFactorizationMonoid.normalizationMonoid.toNormalizationMonoid
  intro C hC
  let p : MvPolynomial σ k → Prop := fun f => ∃ y ∈ Z, cls y = C ∧ Associated f (lam y)
  let W : MvPolynomial σ k → ℕ := fun x =>
    (((UniqueFactorizationMonoid.normalizedFactors x).filter p).map
      MvPolynomial.totalDegree).sum
  have hWmul : ∀ x x', x ≠ 0 → x' ≠ 0 → W (x * x') = W x + W x' := by
    intro x x' hx hx'
    simp only [W, UniqueFactorizationMonoid.normalizedFactors_mul hx hx', Multiset.filter_add,
      Multiset.map_add, Multiset.sum_add]
  have hWpow : ∀ x (m : ℕ), W (x ^ m) = m * W x := by
    intro x m
    simp only [W, UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.filter_nsmul,
      Multiset.map_nsmul, Multiset.sum_nsmul, smul_eq_mul]
  have hWunit : ∀ x, IsUnit x → W x = 0 := by
    intro x hx
    simp [W, UniqueFactorizationMonoid.normalizedFactors_of_isUnit hx]
  have hWlam : ∀ y ∈ Z, W (lam y) = if cls y = C then 1 else 0 := by
    intro y hy
    simp only [W, UniqueFactorizationMonoid.normalizedFactors_irreducible (hlam y hy)]
    have hpy : p (normalize (lam y)) ↔ cls y = C := by
      refine ⟨fun ⟨y', hy', hcl, hass⟩ => ?_, fun h => ⟨y, hy, h, normalize_associated _⟩⟩
      by_contra hne
      exact h3 y hy y' hy' (fun h => hne (h.trans hcl))
        ((normalize_associated (lam y)).symm.trans hass)
    by_cases h : cls y = C
    · rw [Multiset.filter_singleton, if_pos (hpy.2 h), if_pos h]
      simp [totalDegree_of_associated (normalize_associated (lam y)), hdeg y hy]
    · rw [Multiset.filter_singleton, if_neg (fun h' => h (hpy.1 h')), if_neg h]
      simp
  have hWF : ∀ C' ∈ T, W (F C') = if C' = C then (F C').totalDegree else 0 := by
    intro C' hC'
    have hfac : ∀ f ∈ UniqueFactorizationMonoid.normalizedFactors (F C'),
        ∃ y ∈ Z, cls y = C' ∧ Associated f (lam y) := fun f hf =>
      h2 C' hC' f (UniqueFactorizationMonoid.irreducible_of_normalized_factor f hf)
        (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hf)
    by_cases h : C' = C
    · subst h
      rw [if_pos rfl]
      show (((UniqueFactorizationMonoid.normalizedFactors _).filter p).map _).sum = _
      rw [Multiset.filter_eq_self.2 hfac, ← totalDegree_multiset_prod_eq _ fun f hf =>
        (UniqueFactorizationMonoid.irreducible_of_normalized_factor f hf).ne_zero]
      exact totalDegree_of_associated (UniqueFactorizationMonoid.prod_normalizedFactors (hF _ hC'))
    · rw [if_neg h]
      show (((UniqueFactorizationMonoid.normalizedFactors _).filter p).map _).sum = _
      rw [Multiset.filter_eq_nil.2]
      · simp
      · intro f hf ⟨y', hy', hcl', hass'⟩
        obtain ⟨y, hy, hcl, hass⟩ := hfac f hf
        exact h3 y hy y' hy' (by rwa [hcl, hcl']) (hass.symm.trans hass')
  have key := congrArg W h1
  rw [map_prod_eq_sum_of_map_mul W (hWunit 1 isUnit_one) hWmul T _
      fun C' hC' => pow_ne_zero _ (hF C' hC'),
    hWmul _ _ (MvPolynomial.C_ne_zero.2 hc)
      (Finset.prod_ne_zero_iff.2 fun y hy => pow_ne_zero _ (hlam y hy).ne_zero),
    hWunit _ ((isUnit_iff_ne_zero.2 hc).map MvPolynomial.C), zero_add,
    map_prod_eq_sum_of_map_mul W (hWunit 1 isUnit_one) hWmul Z _
      fun y hy => pow_ne_zero _ (hlam y hy).ne_zero] at key
  simp only [hWpow] at key
  have eL : ∑ i ∈ T, e i * W (F i) = e C * (F C).totalDegree := by
    rw [Finset.sum_congr rfl fun C' hC' => by rw [hWF C' hC']]
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' T C, if_pos hC]
  have eR : ∑ y ∈ Z, n y * W (lam y) = ∑ y ∈ Z with cls y = C, n y := by
    rw [Finset.sum_congr rfl fun y hy => by rw [hWlam y hy], Finset.sum_filter]
    simp only [mul_ite, mul_zero, mul_one]
  rw [← eL, ← eR, key]

end Weight

end FibrePolyAlgebra

end MMP.Chow.DeterminantCurveForm
