module

public import MMP.AlgebraicGeometry.Cohomology.HypercohomologyAffineDirectImage
public import MMP.AlgebraicGeometry.DeRham.Logarithmic.DeligneIllusieReduction

/-!
# Restriction of sheaves of modules over an inverse image to an open subscheme

Let `π : V ⟶ T` be a morphism of schemes and `U` an open of `V`. The inverse image `π⁻¹𝒪_T`
restricts to `U`, and its restriction maps to `(π ∘ ι)⁻¹𝒪_T` and back: on an open `W` of `U`,
sections of `(π ∘ ι)⁻¹𝒪_T` over `W` go to sections of `π⁻¹𝒪_T` over `ι(W)`. Along this ring map
a sheaf `M` of `π⁻¹𝒪_T`-modules restricts to a sheaf `M|_U` of `(π ∘ ι)⁻¹𝒪_T`-modules with
`M|_U(W) = M(ι(W))`.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.invRingRestrictHom`: the ring map
  `(π ∘ ι)⁻¹𝒪_T ⟶ ι^{-1}(π⁻¹𝒪_T)`, the target being the naive restriction.
* `MMP.FourfoldProofs.FractionalLogComplexProof.relRestrict`: the restriction functor
  `Mod(π⁻¹𝒪_T) ⥤ Mod((π ∘ ι)⁻¹𝒪_T)`.

## Implementation notes

The ring map is the transpose along `(π ∘ ι)⁻¹ ⊣ (π ∘ ι)_*` of the unit `𝒪_T ⟶ π_*π⁻¹𝒪_T`
followed by the restriction maps `π⁻¹𝒪_T(Z) ⟶ π⁻¹𝒪_T(ι(ι⁻¹ Z))`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

variable {V T : Scheme.{0}} (π : V ⟶ T) (U : V.Opens)

/-- The inverse image `π⁻¹𝒪_T`, as a sheaf of commutative rings. -/
noncomputable abbrev invRingC : TopCat.Sheaf CommRingCat.{0} V :=
  (TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj T.sheaf

/-- The naive restriction `W ↦ π⁻¹𝒪_T(ι(W))` of `π⁻¹𝒪_T` to `U`. -/
noncomputable abbrev invRingRestrict : TopCat.Sheaf CommRingCat.{0} U :=
  (U.ι.isOpenEmbedding.sheafPullback CommRingCat.{0}).obj (invRingC π)

/-- The restriction maps `π⁻¹𝒪_T(Z) ⟶ π⁻¹𝒪_T(ι(ι⁻¹ Z))`. -/
noncomputable def invRingToRestrict :
    invRingC π ⟶ (TopCat.Sheaf.pushforward CommRingCat.{0} U.ι.base).obj (invRingRestrict π U) :=
  ⟨{ app := fun Z => (invRingC π).obj.map (homOfLE (U.ι.image_preimage_le Z.unop)).op
     naturality := fun _ _ _ => ((invRingC π).obj.map_comp _ _).symm.trans
       (((invRingC π).obj.congr_map (Subsingleton.elim _ _)).trans
         ((invRingC π).obj.map_comp _ _)) }⟩

/-- **The ring map `(π ∘ ι)⁻¹𝒪_T ⟶ ι^{-1}(π⁻¹𝒪_T)`.** -/
noncomputable def invRingRestrictHom : invRingC (U.ι ≫ π) ⟶ invRingRestrict π U :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} (U.ι ≫ π).base).homEquiv
    T.sheaf (invRingRestrict π U)).symm
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} π.base).unit.app T.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat.{0} π.base).map (invRingToRestrict π U))

/-- **Restriction of sheaves of `π⁻¹𝒪_T`-modules to `U`**, as sheaves of
`(π ∘ ι)⁻¹𝒪_T`-modules. -/
noncomputable def relRestrict :
    SheafOfModules.{0} (invRing π) ⥤ SheafOfModules.{0} (invRing (U.ι ≫ π)) :=
  have := U.ι.isOpenEmbedding.functor_isContinuous
  SheafOfModules.pushforward (F := U.ι.isOpenEmbedding.isOpenMap.functor)
    ((sheafCompose _ (forget₂ CommRingCat RingCat)).map (invRingRestrictHom π U))

/-! ### Compatibility with the ring map of the direct image -/

/-- **The ring map of the direct image along `ι`, followed by `invRingRestrictHom`, is the
restriction.** -/
@[reassoc]
theorem inverseImageCompHom_comp_invRingRestrictHom :
    RingedSpace.inverseImageCompHom T.toRingedSpace π.base U.ι.base ≫
        (TopCat.Sheaf.pushforward CommRingCat.{0} U.ι.base).map (invRingRestrictHom π U) =
      invRingToRestrict π U := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} π.base).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, RingedSpace.homEquiv_inverseImageCompHom]
  have h := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} (U.ι ≫ π).base).homEquiv
    T.sheaf (invRingRestrict π U)).apply_symm_apply
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} π.base).unit.app T.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat.{0} π.base).map (invRingToRestrict π U))
  rwa [Adjunction.homEquiv_unit] at h ⊢

/-- On sections over `W`, the ring map of the direct image along `ι` followed by
`invRingRestrictHom` is the restriction map `π⁻¹𝒪_T(W) ⟶ π⁻¹𝒪_T(ι(ι⁻¹ W))`. -/
theorem invRingRestrictHom_app_relRingHom (W : V.Opens) (a : (invRingC π).obj.obj (op W)) :
    ((invRingRestrictHom π U).hom.app (op (U.ι ⁻¹ᵁ W))).hom
        (((relRingHom U.ι π).hom.app (op W)).hom a) =
      ((invRingC π).obj.map (homOfLE (U.ι.image_preimage_le W)).op).hom a :=
  congrArg (fun φ => (φ.hom.app (op W)).hom a) (inverseImageCompHom_comp_invRingRestrictHom π U)

/-- The restriction functor `relRestrict π U` is additive. -/
instance additive_relRestrict : (relRestrict π U).Additive :=
  ⟨fun {_ _ _ _} => rfl⟩

/-! ### Compatibility with the structure maps -/

/-- The isomorphisms `Γ(U, W) ≅ Γ(V, ι(W))`, as a morphism from `𝒪_U` to the naive restriction
of `𝒪_V`. -/
noncomputable def appIsoInvSheafHom :
    U.toScheme.sheaf ⟶ (U.ι.isOpenEmbedding.sheafPullback CommRingCat.{0}).obj V.sheaf :=
  ⟨{ app := fun W => (U.ι.appIso W.unop).inv
     naturality := fun _ _ i => U.ι.appIso_inv_naturality i }⟩

/-- **The structure map of `ι ≫ π` is that of `π` read through `invRingRestrictHom`.** -/
@[reassoc]
theorem invRingRestrictHom_comp_inverseImageStructureMap :
    invRingRestrictHom π U ≫
        (U.ι.isOpenEmbedding.sheafPullback CommRingCat.{0}).map (inverseImageStructureMap π) =
      inverseImageStructureMap (U.ι ≫ π) ≫ appIsoInvSheafHom U := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0}
    (U.ι ≫ π).base).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    show (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} (U.ι ≫ π).base).homEquiv
      _ _ (invRingRestrictHom π U) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} π.base).unit.app T.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat.{0} π.base).map (invRingToRestrict π U) from
      Equiv.apply_symm_apply _ _,
    show (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} (U.ι ≫ π).base).homEquiv
      _ _ (inverseImageStructureMap (U.ι ≫ π)) = ⟨(U.ι ≫ π).c⟩ from Equiv.apply_symm_apply _ _]
  have hφ : (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} π.base).unit.app T.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat.{0} π.base).map (inverseImageStructureMap π) =
        ⟨π.c⟩ :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} π.base).homEquiv_unit
      T.sheaf V.sheaf (inverseImageStructureMap π)).symm.trans (Equiv.apply_symm_apply _ _)
  apply Sheaf.hom_ext
  ext Z : 2
  have hZ : ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} π.base).unit.app
      T.sheaf).hom.app Z ≫ (inverseImageStructureMap π).hom.app (op (π ⁻¹ᵁ Z.unop)) =
        π.c.app Z := congrArg (fun φ => φ.hom.app Z) hφ
  change ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} π.base).unit.app
      T.sheaf).hom.app Z ≫ ((invRingC π).obj.map
        (homOfLE (U.ι.image_preimage_le (π ⁻¹ᵁ Z.unop))).op ≫
      (inverseImageStructureMap π).hom.app (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ (π ⁻¹ᵁ Z.unop))))) =
    π.c.app Z ≫ U.ι.c.app (op (π ⁻¹ᵁ Z.unop)) ≫ (U.ι.appIso (U.ι ⁻¹ᵁ (π ⁻¹ᵁ Z.unop))).inv
  have hn := (inverseImageStructureMap π).hom.naturality
    (homOfLE (U.ι.image_preimage_le (π ⁻¹ᵁ Z.unop))).op
  exact (congrArg (_ ≫ ·) hn).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hZ).trans
      (congrArg (π.c.app Z ≫ ·) (U.ι.app_appIso_inv (π ⁻¹ᵁ Z.unop)).symm)))

/-- On sections over `W`, the structure map of `ι ≫ π` followed by `(U.ι.appIso W).inv` is
`invRingRestrictHom` followed by the structure map of `π` over `ι(W)`. -/
theorem appIso_inv_inverseImageStructureMap_app (W : U.toScheme.Opens)
    (a : (invRingC (U.ι ≫ π)).obj.obj (op W)) :
    (U.ι.appIso W).inv.hom (((inverseImageStructureMap (U.ι ≫ π)).hom.app (op W)).hom a) =
      ((inverseImageStructureMap π).hom.app (op (U.ι ''ᵁ W))).hom
        (((invRingRestrictHom π U).hom.app (op W)).hom a) :=
  (congrArg (fun φ => (φ.hom.app (op W)).hom a)
    (invRingRestrictHom_comp_inverseImageStructureMap π U)).symm

/-- **Restriction commutes with reading an `𝒪_V`-module over `π⁻¹𝒪_T`**: the restriction to `U`
of an `𝒪_V`-module `G` read over `π⁻¹𝒪_T` is the restriction `G|_U` read over `(π ∘ ι)⁻¹𝒪_T`. -/
noncomputable def relRestrictRestrictScalarsIso (G : V.Modules) :
    (relRestrict π U).obj ((SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
        (φ := inverseImageStructureMap π))).obj G) ≅
      (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
        (φ := inverseImageStructureMap (U.ι ≫ π)))).obj (G.restrict U.ι) where
  hom := ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun x => (show G.val.obj (op (U.ι ''ᵁ W.unop)) from x)) (fun _ _ => rfl))
      naturality := fun _ _ _ => rfl }
    (fun W a x => (congrArg (fun b : V.ringCatSheaf.obj.obj (op (U.ι ''ᵁ W.unop)) =>
      b • (show G.val.obj (op (U.ι ''ᵁ W.unop)) from x))
        (appIso_inv_inverseImageStructureMap_app π U W.unop a)).symm)⟩
  inv := ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun x => (show G.val.obj (op (U.ι ''ᵁ W.unop)) from x)) (fun _ _ => rfl))
      naturality := fun _ _ _ => rfl }
    (fun W a x => (congrArg (fun b : V.ringCatSheaf.obj.obj (op (U.ι ''ᵁ W.unop)) =>
      b • (show G.val.obj (op (U.ι ''ᵁ W.unop)) from x))
        (appIso_inv_inverseImageStructureMap_app π U W.unop a)))⟩
  hom_inv_id := SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ => rfl)
  inv_hom_id := SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ => rfl)

/-! ### The unit `M ⟶ ι_*(M|_U)` -/

/-- Restricting twice is restricting once, for a presheaf of modules on a thin category. -/
theorem presheafOfModules_map_map_eq {C : Type*} [Category C] [Quiver.IsThin Cᵒᵖ]
    {R : Cᵒᵖ ⥤ RingCat.{0}} (M : PresheafOfModules.{0} R) {A B B' D : Cᵒᵖ}
    (i : A ⟶ B) (j : B ⟶ D) (i' : A ⟶ B') (j' : B' ⟶ D) (x : M.obj A) :
    M.map j (M.map i x) = M.map j' (M.map i' x) := by
  rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
  exact PresheafOfModules.congr_map_apply M (Subsingleton.elim _ _) x

/-- A restriction is a composite of restrictions. -/
theorem presheafOfModules_map_eq_map_map {C : Type*} [Category C] [Quiver.IsThin Cᵒᵖ]
    {R : Cᵒᵖ ⥤ RingCat.{0}} (M : PresheafOfModules.{0} R) {A B D : Cᵒᵖ}
    (k : A ⟶ D) (i : A ⟶ B) (j : B ⟶ D) (x : M.obj A) :
    M.map k x = M.map j (M.map i x) := by
  rw [← PresheafOfModules.map_comp_apply]
  exact PresheafOfModules.congr_map_apply M (Subsingleton.elim _ _) x

/-- **The unit `M ⟶ ι_*(M|_U)`**: the restriction maps `M(W) ⟶ M(ι(ι⁻¹ W))`. -/
noncomputable def relRestrictUnit (M : SheafOfModules.{0} (invRing π)) :
    M ⟶ (relDirectImage U.ι π).obj ((relRestrict π U).obj M) :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun x => (show M.val.obj (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ W.unop))) from
          M.val.map (homOfLE (U.ι.image_preimage_le W.unop)).op x))
        (fun x y => map_add _ x y))
      naturality := fun {W W'} g => by
        ext x
        exact presheafOfModules_map_map_eq M.val _ _ _ _ x }
    (fun W a x => (M.val.map_smul _ a x).trans
      (congrArg (fun b : (invRing π).obj.obj (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ W.unop))) =>
        b • (show M.val.obj (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ W.unop))) from
          M.val.map (homOfLE (U.ι.image_preimage_le W.unop)).op x))
        (invRingRestrictHom_app_relRingHom π U W.unop a).symm))⟩

/-- The component of `relRestrictUnit` at `W` is the restriction map `M(W) ⟶ M(ι(ι⁻¹ W))`. -/
theorem relRestrictUnit_val_app (M : SheafOfModules.{0} (invRing π)) (W : V.Opens)
    (x : M.val.obj (op W)) :
    (relRestrictUnit π U M).val.app (op W) x =
      (show ((relDirectImage U.ι π).obj ((relRestrict π U).obj M)).val.obj (op W) from
        M.val.map (homOfLE (U.ι.image_preimage_le W)).op x) := rfl

/-- The unit is natural. -/
@[reassoc]
theorem relRestrictUnit_naturality {M N : SheafOfModules.{0} (invRing π)} (f : M ⟶ N) :
    relRestrictUnit π U M ≫ (relDirectImage U.ι π).map ((relRestrict π U).map f) =
      f ≫ relRestrictUnit π U N :=
  SheafOfModules.hom_ext <| PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext <|
    LinearMap.ext fun x =>
      PresheafOfModules.naturality_apply f.val (homOfLE (U.ι.image_preimage_le W.unop)).op x

/-! ### Extension by zero -/

section ExtZero

variable {X : TopCat.{0}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}
  (M : SheafOfModules.{0} R)

/-- Two sections of a sheaf of modules over the empty open agree. -/
theorem sheafOfModules_eq_of_eq_bot {A : Opens X} (hA : A = ⊥) (s t : M.val.obj (op A)) :
    s = t :=
  TopCat.Sheaf.eq_of_locally_eq' ((SheafOfModules.toSheaf R).obj M) A
    (U := (Empty.elim : Empty → Opens X)) (fun i => i.elim)
    (hA.le.trans bot_le) s t (fun i => i.elim)

variable {A B W : Opens X} (hA : A ≤ W) (hB : B ≤ W) (hAB : A ⊓ B = ⊥) (hW : W ≤ A ⊔ B)

include hAB hW in
/-- For disjoint `A`, `B` covering `W`, every section over `A` extends to a section over `W`
vanishing on `B`. -/
theorem exists_sheafOfModules_extZero (t : M.val.obj (op A)) :
    ∃ s : M.val.obj (op W), M.val.map (homOfLE hA).op s = t ∧ M.val.map (homOfLE hB).op s = 0 := by
  let F := (SheafOfModules.toSheaf R).obj M
  let U : Bool → Opens X := fun b => cond b A B
  let sf : ∀ b : Bool, ToType (F.1.obj (op (U b))) := fun b =>
    Bool.casesOn (motive := fun b => ToType (F.1.obj (op (U b)))) b
      (0 : M.val.obj (op B)) t
  have hc : TopCat.Presheaf.IsCompatible F.1 U sf := by
    rintro (_ | _) (_ | _)
    · rfl
    · exact sheafOfModules_eq_of_eq_bot M ((inf_comm B A).trans hAB) _ _
    · exact sheafOfModules_eq_of_eq_bot M hAB _ _
    · rfl
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' F U W
    (fun b => homOfLE (by cases b; exacts [hB, hA]))
    (hW.trans (sup_le (le_iSup U true) (le_iSup U false))) sf hc
  exact ⟨s, hs true, hs false⟩

/-- **The extension by zero** of a section over `A` to `W = A ⊔ B`, for disjoint `A`, `B`: the
section restricting to the given one on `A` and to zero on `B`. -/
noncomputable def sheafOfModulesExtZero (t : M.val.obj (op A)) : M.val.obj (op W) :=
  (exists_sheafOfModules_extZero M hA hB hAB hW t).choose

/-- The extension by zero restricts to the given section on `A`. -/
@[simp] theorem sheafOfModulesExtZero_map_left (t : M.val.obj (op A)) :
    M.val.map (homOfLE hA).op (sheafOfModulesExtZero M hA hB hAB hW t) = t :=
  (exists_sheafOfModules_extZero M hA hB hAB hW t).choose_spec.1

/-- The extension by zero restricts to zero on `B`. -/
@[simp] theorem sheafOfModulesExtZero_map_right (t : M.val.obj (op A)) :
    M.val.map (homOfLE hB).op (sheafOfModulesExtZero M hA hB hAB hW t) = 0 :=
  (exists_sheafOfModules_extZero M hA hB hAB hW t).choose_spec.2

/-- The extension by zero is characterized by its restrictions. -/
theorem sheafOfModulesExtZero_eq (t : M.val.obj (op A)) (s : M.val.obj (op W))
    (h₁ : M.val.map (homOfLE hA).op s = t) (h₂ : M.val.map (homOfLE hB).op s = 0) :
    sheafOfModulesExtZero M hA hB hAB hW t = s :=
  TopCat.Sheaf.eq_of_locally_eq₂ ((SheafOfModules.toSheaf R).obj M) (homOfLE hA) (homOfLE hB) hW
    _ _
    ((sheafOfModulesExtZero_map_left M hA hB hAB hW t).trans h₁.symm)
    ((sheafOfModulesExtZero_map_right M hA hB hAB hW t).trans h₂.symm)

/-- The extension by zero is additive. -/
theorem sheafOfModulesExtZero_add (t t' : M.val.obj (op A)) :
    sheafOfModulesExtZero M hA hB hAB hW (t + t') =
      sheafOfModulesExtZero M hA hB hAB hW t + sheafOfModulesExtZero M hA hB hAB hW t' :=
  sheafOfModulesExtZero_eq M hA hB hAB hW _ _
    (by rw [map_add, sheafOfModulesExtZero_map_left, sheafOfModulesExtZero_map_left]; rfl)
    (by rw [map_add, sheafOfModulesExtZero_map_right, sheafOfModulesExtZero_map_right, add_zero])

/-- The extension by zero of `r|_A • t` is `r •` the extension by zero of `t`. -/
theorem sheafOfModulesExtZero_smul (r : R.obj.obj (op W)) (t : M.val.obj (op A)) :
    sheafOfModulesExtZero M hA hB hAB hW (R.obj.map (homOfLE hA).op r • t) =
      r • sheafOfModulesExtZero M hA hB hAB hW t :=
  sheafOfModulesExtZero_eq M hA hB hAB hW _ _
    (by rw [M.val.map_smul, sheafOfModulesExtZero_map_left]; rfl)
    (by rw [M.val.map_smul, sheafOfModulesExtZero_map_right, smul_zero])

/-- The extension by zero commutes with restriction. -/
theorem sheafOfModulesExtZero_map {A' B' W' : Opens X} (hA' : A' ≤ W') (hB' : B' ≤ W')
    (hAB' : A' ⊓ B' = ⊥) (hW' : W' ≤ A' ⊔ B') (hWW : W' ≤ W) (hAA : A' ≤ A) (hBB : B' ≤ B)
    (t : M.val.obj (op A)) :
    M.val.map (homOfLE hWW).op (sheafOfModulesExtZero M hA hB hAB hW t) =
      sheafOfModulesExtZero M hA' hB' hAB' hW' (M.val.map (homOfLE hAA).op t) := by
  refine (sheafOfModulesExtZero_eq M hA' hB' hAB' hW' _ _ ?_ ?_).symm
  · rw [presheafOfModules_map_map_eq M.val _ _ (homOfLE hA).op (homOfLE hAA).op,
      sheafOfModulesExtZero_map_left]
  · rw [presheafOfModules_map_map_eq M.val _ _ (homOfLE hB).op (homOfLE hBB).op,
      sheafOfModulesExtZero_map_right]
    exact (M.val.map (homOfLE hBB).op).hom.map_zero

end ExtZero

/-! ### Extension by zero from an open and closed piece -/

section Clopen

variable (hU : IsClosed (U : Set V))

/-- The complement of a closed open `U`, as an open. -/
def pieceComplOpens : V.Opens := ⟨(U : Set V)ᶜ, hU.isOpen_compl⟩

/-- The opens `ι(ι⁻¹ W)` and `W ∖ U` are disjoint. -/
theorem image_preimage_inf_pieceComplOpens_eq_bot (W : V.Opens) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ W) ⊓ (W ⊓ pieceComplOpens U hU) = ⊥ := by
  rw [MMP.FourfoldProofs.LogDegenerationProof.image_preimage_opens_ι, eq_bot_iff]
  rintro x ⟨⟨-, hxU⟩, -, hxC⟩
  exact hxC hxU

/-- The opens `ι(ι⁻¹ W)` and `W ∖ U` cover `W`. -/
theorem le_image_preimage_sup_pieceComplOpens (W : V.Opens) :
    W ≤ U.ι ''ᵁ (U.ι ⁻¹ᵁ W) ⊔ (W ⊓ pieceComplOpens U hU) := by
  rw [MMP.FourfoldProofs.LogDegenerationProof.image_preimage_opens_ι]
  intro x hx
  by_cases hxU : x ∈ (U : Set V)
  · exact Or.inl ⟨hx, hxU⟩
  · exact Or.inr ⟨hx, hxU⟩

/-- **The extension by zero `ι_*(M|_U) ⟶ M`** for an open and closed `U`: a section over
`W ∩ U` is extended by zero on `W ∖ U`. -/
noncomputable def relRestrictExt (M : SheafOfModules.{0} (invRing π)) :
    (relDirectImage U.ι π).obj ((relRestrict π U).obj M) ⟶ M :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun t => sheafOfModulesExtZero M (U.ι.image_preimage_le W.unop) inf_le_left
          (image_preimage_inf_pieceComplOpens_eq_bot U hU W.unop)
          (le_image_preimage_sup_pieceComplOpens U hU W.unop)
          (show M.val.obj (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ W.unop))) from t))
        (fun t t' => sheafOfModulesExtZero_add M _ _ _ _ _ _))
      naturality := fun {W W'} g => by
        ext t
        exact (sheafOfModulesExtZero_map M _ _
          (image_preimage_inf_pieceComplOpens_eq_bot U hU W.unop)
          (le_image_preimage_sup_pieceComplOpens U hU W.unop) _ _
          (image_preimage_inf_pieceComplOpens_eq_bot U hU W'.unop)
          (le_image_preimage_sup_pieceComplOpens U hU W'.unop) (leOfHom g.unop)
          (U.ι.image_mono (U.ι.preimage_mono (leOfHom g.unop)))
          (inf_le_inf_right _ (leOfHom g.unop)) t).symm }
    (fun W a t => (congrArg (fun b : (invRing π).obj.obj (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ W.unop))) =>
        sheafOfModulesExtZero M (U.ι.image_preimage_le W.unop) inf_le_left
          (image_preimage_inf_pieceComplOpens_eq_bot U hU W.unop)
          (le_image_preimage_sup_pieceComplOpens U hU W.unop)
          (b • (show M.val.obj (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ W.unop))) from t)))
        (invRingRestrictHom_app_relRingHom π U W.unop a)).trans
      (sheafOfModulesExtZero_smul M _ _ _ _ a _))⟩

/-- The component of `relRestrictExt` at `W` is the extension by zero from `W ∩ U` to `W`. -/
theorem relRestrictExt_val_app (M : SheafOfModules.{0} (invRing π)) (W : V.Opens)
    (t : M.val.obj (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ W)))) :
    (relRestrictExt π U hU M).val.app (op W) t =
      sheafOfModulesExtZero M (U.ι.image_preimage_le W) inf_le_left
        (image_preimage_inf_pieceComplOpens_eq_bot U hU W)
        (le_image_preimage_sup_pieceComplOpens U hU W) t := rfl

/-- The extension by zero is natural. -/
@[reassoc]
theorem relRestrictExt_naturality {M N : SheafOfModules.{0} (invRing π)} (f : M ⟶ N) :
    (relDirectImage U.ι π).map ((relRestrict π U).map f) ≫ relRestrictExt π U hU N =
      relRestrictExt π U hU M ≫ f := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext
    (LinearMap.ext fun t => ?_))
  refine sheafOfModulesExtZero_eq N _ _ (image_preimage_inf_pieceComplOpens_eq_bot U hU W.unop)
    (le_image_preimage_sup_pieceComplOpens U hU W.unop) _ _ ?_ ?_
  · change N.val.map (homOfLE (U.ι.image_preimage_le W.unop)).op (f.val.app W
      (sheafOfModulesExtZero M (U.ι.image_preimage_le W.unop) inf_le_left
        (image_preimage_inf_pieceComplOpens_eq_bot U hU W.unop)
        (le_image_preimage_sup_pieceComplOpens U hU W.unop) t)) =
        f.val.app (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ W.unop))) t
    refine (PresheafOfModules.naturality_apply f.val (homOfLE (U.ι.image_preimage_le W.unop)).op
      (sheafOfModulesExtZero M (U.ι.image_preimage_le W.unop) inf_le_left
        (image_preimage_inf_pieceComplOpens_eq_bot U hU W.unop)
        (le_image_preimage_sup_pieceComplOpens U hU W.unop) t)).symm.trans ?_
    exact congrArg (f.val.app _) (sheafOfModulesExtZero_map_left M _ _
      (image_preimage_inf_pieceComplOpens_eq_bot U hU W.unop)
      (le_image_preimage_sup_pieceComplOpens U hU W.unop)
      (show M.val.obj (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ W.unop))) from t))
  · change N.val.map (homOfLE inf_le_left).op (f.val.app W
      (sheafOfModulesExtZero M (U.ι.image_preimage_le W.unop) inf_le_left
        (image_preimage_inf_pieceComplOpens_eq_bot U hU W.unop)
        (le_image_preimage_sup_pieceComplOpens U hU W.unop) t)) = 0
    refine (PresheafOfModules.naturality_apply f.val (homOfLE inf_le_left).op
      (sheafOfModulesExtZero M (U.ι.image_preimage_le W.unop) inf_le_left
        (image_preimage_inf_pieceComplOpens_eq_bot U hU W.unop)
        (le_image_preimage_sup_pieceComplOpens U hU W.unop) t)).symm.trans ?_
    exact (congrArg (f.val.app _) (sheafOfModulesExtZero_map_right M _ _
      (image_preimage_inf_pieceComplOpens_eq_bot U hU W.unop)
      (le_image_preimage_sup_pieceComplOpens U hU W.unop)
      (show M.val.obj (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ W.unop))) from t))).trans
      (f.val.app _).hom.map_zero

end Clopen

/-! ### The decomposition over a finite clopen cover -/

section Decomposition

variable {ι : Type} [Fintype ι] (U : ι → V.Opens) (hU : ∀ i, IsClosed (U i : Set V))
  (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j)) (hcov : ∀ x : V, ∃ i, x ∈ U i)

include hdisj hcov in
/-- On sections, a section is the sum of the extensions by zero of its restrictions to the
pieces. -/
theorem sum_relRestrictExt_relRestrictUnit_apply (M : SheafOfModules.{0} (invRing π))
    (W : V.Opens) (s : M.val.obj (op W)) :
    ∑ i, (relRestrictExt π (U i) (hU i) M).val.app (op W)
        ((relRestrictUnit π (U i) M).val.app (op W) s) = s := by
  classical
  refine TopCat.Sheaf.eq_of_locally_eq' ((SheafOfModules.toSheaf _).obj M)
    (fun j => (U j).ι ''ᵁ ((U j).ι ⁻¹ᵁ W)) W (fun j => homOfLE ((U j).ι.image_preimage_le W))
    (fun x hx => ?_) _ s (fun j => ?_)
  · obtain ⟨j, hj⟩ := hcov x
    refine Opens.mem_iSup.2 ⟨j, ?_⟩
    rw [MMP.FourfoldProofs.LogDegenerationProof.image_preimage_opens_ι]
    exact ⟨hx, hj⟩
  · change M.val.map _ (∑ i, _) = M.val.map _ s
    rw [map_sum, Finset.sum_eq_single j]
    · exact sheafOfModulesExtZero_map_left M _ _
        (image_preimage_inf_pieceComplOpens_eq_bot (U j) (hU j) W)
        (le_image_preimage_sup_pieceComplOpens (U j) (hU j) W) _
    · intro i _ hij
      have hle : (U j).ι ''ᵁ ((U j).ι ⁻¹ᵁ W) ≤ W ⊓ pieceComplOpens (U i) (hU i) := by
        rw [MMP.FourfoldProofs.LogDegenerationProof.image_preimage_opens_ι]
        rintro x ⟨hxW, hxj⟩
        exact ⟨hxW, fun hxi => by
          simpa using (hdisj i j hij).le_bot (show x ∈ U i ⊓ U j from ⟨hxi, hxj⟩)⟩
      change M.val.map (homOfLE ((U j).ι.image_preimage_le W)).op
        (sheafOfModulesExtZero M ((U i).ι.image_preimage_le W) inf_le_left
          (image_preimage_inf_pieceComplOpens_eq_bot (U i) (hU i) W)
          (le_image_preimage_sup_pieceComplOpens (U i) (hU i) W)
          (M.val.map (homOfLE ((U i).ι.image_preimage_le W)).op s)) = 0
      rw [presheafOfModules_map_eq_map_map M.val _ (homOfLE inf_le_left).op (homOfLE hle).op]
      exact (congrArg (M.val.map (homOfLE hle).op) (sheafOfModulesExtZero_map_right M _ _
        (image_preimage_inf_pieceComplOpens_eq_bot (U i) (hU i) W)
        (le_image_preimage_sup_pieceComplOpens (U i) (hU i) W) _)).trans
        (M.val.map (homOfLE hle).op).hom.map_zero
    · exact fun h => (h (Finset.mem_univ j)).elim

include hdisj hcov in
/-- **A sheaf is the sum of the extensions by zero of its restrictions to the pieces.** -/
theorem sum_relRestrictUnit_comp_relRestrictExt (M : SheafOfModules.{0} (invRing π)) :
    ∑ i, relRestrictUnit π (U i) M ≫ relRestrictExt π (U i) (hU i) M = 𝟙 M := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext
    (LinearMap.ext fun s => ?_))
  change ((SheafOfModules.evaluation _ W).map (∑ i, _)).hom s = s
  rw [Functor.map_sum, ModuleCat.hom_sum]
  refine (LinearMap.sum_apply _ _ (show ((SheafOfModules.evaluation _ W).obj M) from s)).trans ?_
  exact sum_relRestrictExt_relRestrictUnit_apply π U hU hdisj hcov M W.unop s

end Decomposition

/-! ### Complexes -/

section Complexes

/-- The unit `K ⟶ ι_*(K|_U)` of complexes. -/
noncomputable def relRestrictUnitCx (K : CochainComplex (SheafOfModules.{0} (invRing π)) ℕ) :
    K ⟶ ((relDirectImage U.ι π).mapHomologicalComplex _).obj
      (((relRestrict π U).mapHomologicalComplex _).obj K) where
  f p := relRestrictUnit π U (K.X p)
  comm' p q _ := relRestrictUnit_naturality π U (K.d p q)

/-- The extension by zero `ι_*(K|_U) ⟶ K` of complexes, for an open and closed `U`. -/
noncomputable def relRestrictExtCx (hU : IsClosed (U : Set V))
    (K : CochainComplex (SheafOfModules.{0} (invRing π)) ℕ) :
    ((relDirectImage U.ι π).mapHomologicalComplex _).obj
      (((relRestrict π U).mapHomologicalComplex _).obj K) ⟶ K where
  f p := relRestrictExt π U hU (K.X p)
  comm' p q _ := (relRestrictExt_naturality π U hU (K.d p q)).symm

/-- **A complex is the sum of the extensions by zero of its restrictions to the pieces.** -/
theorem sum_relRestrictUnitCx_comp_relRestrictExtCx {ι : Type} [Fintype ι] (U : ι → V.Opens)
    (hU : ∀ i, IsClosed (U i : Set V)) (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcov : ∀ x : V, ∃ i, x ∈ U i) (K : CochainComplex (SheafOfModules.{0} (invRing π)) ℕ) :
    ∑ i, relRestrictUnitCx π (U i) K ≫ relRestrictExtCx π (U i) (hU i) K = 𝟙 K := by
  ext p : 1
  change (HomologicalComplex.eval _ _ p).map (∑ i, _) = 𝟙 (K.X p)
  rw [Functor.map_sum]
  exact sum_relRestrictUnit_comp_relRestrictExt π U hU hdisj hcov (K.X p)

end Complexes

end MMP.FourfoldProofs.FractionalLogComplexProof
