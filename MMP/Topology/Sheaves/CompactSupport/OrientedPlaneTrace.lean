module
public import MMP.Topology.Sheaves.CompactSupport.CSoft
import MMP.AlgebraicGeometry.Analytic.RationalSheafCohomologySingular

/-!
# Compactly supported cohomology of an oriented plane

Let `S` be a Hausdorff surface with an oriented atlas and `E` a finite-dimensional `ℚ`-vector
space, `E_S` the constant sheaf on `S`. For every open `V ⊆ S` homeomorphic to `ℝ²`, the
compactly supported cohomology `H^q_c(V, E_S|_V)` vanishes for `q ≠ 2`, and there are trace
isomorphisms `tr_V : H^2_c(V, E_S|_V) ≅ E`, natural in `E`, compatible with the extension maps:
`tr_V ∘ e = tr_{V'}` for `V' ⊆ V` two such opens.

The proof computes `H^q_c(V, ℚ)` on the one-point compactification `V⁺ ≅ S²`: the inclusion
`j : V → V⁺` gives `H^q_c(V, ℚ) ≅ H^q(V⁺, j_! ℚ) ≅ H^q(V⁺, ℚ)` for `q ≥ 2`, and by the
comparison of constant-sheaf cohomology with singular cohomology this is `H^q(V⁺; ℚ)`, which is
`ℚ` for `q = 2` and vanishes otherwise. The generator of `H^2(V⁺; ℚ)` is the image of the local
orientation class at any point of `V`; it does not depend on the point because the local
orientation classes of nearby points agree on a coordinate ball. For `V' ⊆ V` the extension map
corresponds to the pull-back along the collapse `V⁺ → V'⁺`, which carries local orientation
classes to local orientation classes. The coefficients are reduced to `ℚ` by additivity.

## Main results

* `MMP.Fourfold.compactSupportCohomology_orientedPlane_trace`

## Implementation notes

The orientation of `S` is an oriented atlas, `MMP.IsOrientedAtlas`, modelled on
a real normed plane `H` (for instance `ℂ`, so that a complex curve is covered by
`MMP.isOrientedAtlas_of_isManifold_complex`). The constant sheaf on `V` is the
restriction of the constant sheaf `E_S`, which is what the extension maps
`H^q_c(V', F|_{V'}) ⟶ H^q_c(V, F|_V)` act on. The extension map is the composite
`ι_{V'} ≫ H^2_c(S, m) ≫ ι_V⁻¹` through comparison isomorphisms `ι_U : H^2_c(U, -) ≅
H^2_c(S, j_{U!} -)` and the inclusion `m : j_{V'!}(F|_{V'}) ⟶ j_{V!}(F|_V)` over `F`, as in
`MMP.Fourfold.compactSupportCohomology_extendByZero`; the traces are asserted for every choice
of natural comparison isomorphisms `ι`.

## References

* [Iversen, *Cohomology of sheaves*, III]
-/

open CategoryTheory Limits TopologicalSpace Opposite Topology ZeroObject

namespace MMP.Fourfold

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Functor.commShiftRightDerivedFunctorPlus
  Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  Functor.isTriangulated_rightDerivedFunctorPlus

universe u

/-! ### Additive functors on finite-dimensional `ℚ`-vector spaces -/

section Additive

/-- The object `ℚ` of `FGModuleCat ℚ`. -/
private noncomputable abbrev one : FGModuleCat.{0} ℚ := FGModuleCat.of ℚ ℚ

/-- The morphism `ℚ ⟶ E` sending `1` to `v`. -/
private noncomputable def pt {E : FGModuleCat.{0} ℚ} (v : E.obj) : one ⟶ E :=
  ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ E.obj v))

/-- The morphism `E ⟶ ℚ` of a linear form. -/
private noncomputable def form {E : FGModuleCat.{0} ℚ} (φ : E.obj →ₗ[ℚ] ℚ) : E ⟶ one :=
  ObjectProperty.homMk (ModuleCat.ofHom φ)

private lemma hom_add {E E' : FGModuleCat.{0} ℚ} (f g : E ⟶ E') :
    (f + g).hom = f.hom + g.hom := rfl

private lemma hom_smul {E E' : FGModuleCat.{0} ℚ} (q : ℚ) (f : E ⟶ E') :
    (q • f).hom = q • f.hom := rfl

private lemma hom_sum {E E' : FGModuleCat.{0} ℚ} {ι : Type} (s : Finset ι) (f : ι → (E ⟶ E')) :
    (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom :=
  map_sum ((ModuleCat.isFG ℚ).ι.mapAddHom (X := E) (Y := E')) f s

private lemma pt_add {E : FGModuleCat.{0} ℚ} (v w : E.obj) : pt (v + w) = pt v + pt w := by
  ext
  simp [pt, hom_add]

private lemma pt_smul {E : FGModuleCat.{0} ℚ} (q : ℚ) (v : E.obj) : pt (q • v) = q • pt v := by
  ext
  simp [pt, hom_smul]

private lemma pt_comp {E E' : FGModuleCat.{0} ℚ} (v : E.obj) (f : E ⟶ E') :
    pt v ≫ f = pt (f.hom v) := by
  ext
  simp [pt]

private lemma pt_form {E : FGModuleCat.{0} ℚ} (v : E.obj) (φ : E.obj →ₗ[ℚ] ℚ) :
    pt v ≫ form φ = (φ v) • 𝟙 one := by
  ext
  simp [pt, form, hom_smul]

private lemma sum_form_pt {E : FGModuleCat.{0} ℚ} {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℚ E.obj) : ∑ i, form (b.coord i) ≫ pt (b i) = 𝟙 E := by
  ext v
  simp only [hom_sum]
  simp [pt, form]

variable (F : FGModuleCat.{0} ℚ ⥤ ModuleCat.{0} ℚ) [F.Additive]

private lemma map_apply_eq_sum {E : FGModuleCat.{0} ℚ} (y : F.obj E) :
    y = ∑ i, F.map (pt (Module.finBasis ℚ E.obj i))
      (F.map (form ((Module.finBasis ℚ E.obj).coord i)) y) := by
  conv_lhs => rw [← ModuleCat.id_apply (F.obj E) y, ← F.map_id,
    ← sum_form_pt (Module.finBasis ℚ E.obj)]
  simp [F.map_sum, ModuleCat.hom_sum]

/-- An additive functor vanishing on `ℚ` vanishes. -/
private lemma isZero_obj (h : IsZero (F.obj one)) (E : FGModuleCat.{0} ℚ) : IsZero (F.obj E) := by
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  refine ⟨fun y z => ?_⟩
  rw [map_apply_eq_sum F y, map_apply_eq_sum F z]
  congr 1; funext i; congr 1; exact Subsingleton.elim _ _

variable (x₀ : F.obj one)

/-- `v ↦ F(1 ↦ v)(x₀)`. -/
private noncomputable def evalLin (E : FGModuleCat.{0} ℚ) : E.obj →ₗ[ℚ] F.obj E where
  toFun v := F.map (pt v) x₀
  map_add' v w := by rw [pt_add, F.map_add]; rfl
  map_smul' q v := by rw [pt_smul, F.map_smul]; rfl

private lemma evalLin_apply (E : FGModuleCat.{0} ℚ) (v : E.obj) :
    evalLin F x₀ E v = F.map (pt v) x₀ := rfl

private lemma evalLin_bijective (hx₀ : Function.Bijective fun r : ℚ => r • x₀)
    (E : FGModuleCat.{0} ℚ) : Function.Bijective (evalLin F x₀ E) := by
  have hx0 : x₀ ≠ 0 := by
    intro h
    have := hx₀.1 (a₁ := 0) (a₂ := 1) (by simp [h])
    norm_num at this
  refine ⟨(injective_iff_map_eq_zero _).2 fun v hv => ?_, fun y => ?_⟩
  · refine (Module.forall_dual_apply_eq_zero_iff ℚ v).1 fun φ => ?_
    have h1 : F.map (form φ) (evalLin F x₀ E v) = (φ v) • x₀ := by
      rw [evalLin_apply, ← ModuleCat.comp_apply, ← F.map_comp, pt_form, F.map_smul, F.map_id]
      rfl
    rw [hv, map_zero] at h1
    by_contra hne
    exact hx0 ((smul_eq_zero.1 h1.symm).resolve_left hne)
  · choose r hr using fun i => hx₀.2 (F.map (form ((Module.finBasis ℚ E.obj).coord i)) y)
    refine ⟨∑ i, r i • Module.finBasis ℚ E.obj i, ?_⟩
    rw [map_sum, map_apply_eq_sum F y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, evalLin_apply, ← hr i, map_smul]

private lemma evalLin_naturality {E E' : FGModuleCat.{0} ℚ} (f : E ⟶ E') (v : E.obj) :
    F.map f (evalLin F x₀ E v) = evalLin F x₀ E' (f.hom v) := by
  rw [evalLin_apply, evalLin_apply, ← ModuleCat.comp_apply, ← F.map_comp, pt_comp]

/-- An additive functor `F` with `F(ℚ)` free of rank one on `x₀` is the inclusion. -/
private noncomputable def isoOfGen (hx₀ : Function.Bijective fun r : ℚ => r • x₀) :
    (ModuleCat.isFG ℚ).ι ≅ F :=
  NatIso.ofComponents
    (fun E => (LinearEquiv.ofBijective (evalLin F x₀ E)
      (evalLin_bijective F x₀ hx₀ E)).toModuleIso)
    (fun {E E'} f => by
      ext v
      exact (evalLin_naturality F x₀ f v).symm)

private lemma isoOfGen_hom_app (hx₀ : Function.Bijective fun r : ℚ => r • x₀)
    (E : FGModuleCat.{0} ℚ) (v : E.obj) :
    (isoOfGen F x₀ hx₀).hom.app E v = F.map (pt v) x₀ := rfl

/-- `isoOfGen` is compatible with a natural transformation preserving the generators. -/
private lemma isoOfGen_comp {F' : FGModuleCat.{0} ℚ ⥤ ModuleCat.{0} ℚ} [F'.Additive]
    (x₀' : F'.obj one) (hx₀ : Function.Bijective fun r : ℚ => r • x₀)
    (hx₀' : Function.Bijective fun r : ℚ => r • x₀') (η : F ⟶ F') (hη : η.app one x₀ = x₀')
    (E : FGModuleCat.{0} ℚ) :
    η.app E ≫ (isoOfGen F' x₀' hx₀').inv.app E = (isoOfGen F x₀ hx₀).inv.app E := by
  have key : (isoOfGen F x₀ hx₀).hom.app E ≫ η.app E = (isoOfGen F' x₀' hx₀').hom.app E := by
    ext v
    change η.app E ((isoOfGen F x₀ hx₀).hom.app E v) = (isoOfGen F' x₀' hx₀').hom.app E v
    rw [isoOfGen_hom_app, isoOfGen_hom_app, ← ModuleCat.comp_apply, η.naturality,
      ModuleCat.comp_apply, hη]
  rw [← Iso.inv_hom_id_app_assoc (isoOfGen F x₀ hx₀) E (η.app E ≫ _), reassoc_of% key,
    Iso.hom_inv_id_app, Category.comp_id]

end Additive

/-! ### Restriction to an open subset, extension by zero, and stalks -/

section Open

/-- The stalk functor at `y` on sheaves of `ℚ`-vector spaces. -/
private noncomputable abbrev st {Y : TopCat.{0}} (y : Y) :
    TopCat.Sheaf (ModuleCat.{0} ℚ) Y ⥤ ModuleCat.{0} ℚ :=
  TopCat.Sheaf.forget _ Y ⋙ TopCat.Presheaf.stalkFunctor _ y

/-- A functor between categories of sheaves whose stalk at every point either vanishes or is a
stalk of its argument preserves exact sequences. -/
private lemma exact_map_of_stalk {Y X : TopCat.{0}}
    (Φ : TopCat.Sheaf (ModuleCat.{0} ℚ) Y ⥤ TopCat.Sheaf (ModuleCat.{0} ℚ) X) [Φ.Additive]
    (h : ∀ x : X, (∀ G, IsZero ((st x).obj (Φ.obj G))) ∨ ∃ y : Y, Nonempty (Φ ⋙ st x ≅ st y))
    (S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) Y)) (hS : S.Exact) : (S.map Φ).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rcases h x with h0 | ⟨y, ⟨e⟩⟩
  · exact ShortComplex.exact_of_isZero_X₂ _ (h0 S.X₂)
  · have hy := (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mp hS y
    exact (ShortComplex.exact_iff_of_iso (S.mapNatIso e).symm).mp hy

private lemma preservesHomology_of_stalk {Y X : TopCat.{0}}
    (Φ : TopCat.Sheaf (ModuleCat.{0} ℚ) Y ⥤ TopCat.Sheaf (ModuleCat.{0} ℚ) X) [Φ.Additive]
    (h : ∀ x : X, (∀ G, IsZero ((st x).obj (Φ.obj G))) ∨ ∃ y : Y, Nonempty (Φ ⋙ st x ≅ st y)) :
    PreservesFiniteLimits Φ ∧ PreservesFiniteColimits Φ :=
  (Φ.exact_tfae.out 2 4).mp (exact_map_of_stalk Φ h)

/-- A natural transformation that is invertible on the stalks at `x` gives an isomorphism of the
stalk functors at `x`. -/
private noncomputable def stalkIsoOfIsIso {C : Type*} [Category C] {X : TopCat.{0}}
    {Φ Φ' : C ⥤ TopCat.Sheaf (ModuleCat.{0} ℚ) X} (α : Φ ⟶ Φ') (x : X)
    (h : ∀ G, IsIso ((st x).map (α.app G))) : Φ ⋙ st x ≅ Φ' ⋙ st x :=
  haveI : ∀ G, IsIso ((Functor.whiskerRight α (st x)).app G) := h
  haveI := NatIso.isIso_of_isIso_app (Functor.whiskerRight α (st x))
  asIso (Functor.whiskerRight α (st x))

variable {X : TopCat.{0}} (U : Opens X)

/-- Restriction `j^*` to an open subset. -/
private noncomputable abbrev resF :
    TopCat.Sheaf (ModuleCat.{0} ℚ) X ⥤ TopCat.Sheaf (ModuleCat.{0} ℚ) ((Opens.toTopCat X).obj U) :=
  haveI := U.isOpenEmbedding.functor_isContinuous
  U.isOpenEmbedding.functor.sheafPushforwardContinuous _ _ _

/-- Extension by zero `j_!`. -/
private noncomputable abbrev extF :
    TopCat.Sheaf (ModuleCat.{0} ℚ) ((Opens.toTopCat X).obj U) ⥤ TopCat.Sheaf (ModuleCat.{0} ℚ) X :=
  haveI := U.isOpenEmbedding.functor_isContinuous
  U.isOpenEmbedding.functor.sheafPullback _ _ _

private noncomputable abbrev adjF : extF U ⊣ resF U :=
  haveI := U.isOpenEmbedding.functor_isContinuous
  U.isOpenEmbedding.functor.sheafAdjunctionContinuous _ _ _

private lemma additive_resF : (resF U).Additive := ⟨fun {_ _ _ _} => by apply Sheaf.hom_ext; rfl⟩

private lemma additive_extF : (extF U).Additive := by
  haveI := additive_resF U
  exact (adjF U).left_adjoint_additive

attribute [local instance] additive_resF additive_extF

/-- `j_! j^*`. -/
private noncomputable def PF :
    TopCat.Sheaf (ModuleCat.{0} ℚ) X ⥤ TopCat.Sheaf (ModuleCat.{0} ℚ) X :=
  resF U ⋙ extF U

private lemma additive_PF : (PF U).Additive :=
  inferInstanceAs (resF U ⋙ extF U).Additive

attribute [local instance] additive_PF

variable {U} in
/-- The stalk of `j^* A` at `x ∈ U` is the stalk of `A` at `x`, naturally in `A`. -/
private lemma stalk_resF_naturality {A B : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (f : A ⟶ B)
    (x : (Opens.toTopCat X).obj U) :
    (st x).map ((resF U).map f) ≫
        (AlgebraicGeometry.PresheafedSpace.restrictStalkIso ⟨X, B.presheaf⟩
          U.isOpenEmbedding x).hom =
      (AlgebraicGeometry.PresheafedSpace.restrictStalkIso ⟨X, A.presheaf⟩
          U.isOpenEmbedding x).hom ≫ (st x.1).map f := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun V hV => ?_
  ext s
  have e1 := AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ_apply ⟨X, A.presheaf⟩
    U.isOpenEmbedding V x hV s
  have e2 := AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ_apply ⟨X, B.presheaf⟩
    U.isOpenEmbedding V x hV (((TopCat.Sheaf.forget _ X).map f).app _ s)
  have e3 := TopCat.Presheaf.stalkFunctor_map_germ_apply V x hV ((TopCat.Sheaf.forget _ _).map
    ((resF U).map f)) s
  have e4 := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (U.isOpenEmbedding.functor.obj V) x.1 ⟨x, hV, rfl⟩ ((TopCat.Sheaf.forget _ X).map f) s
  exact (congrArg (AlgebraicGeometry.PresheafedSpace.restrictStalkIso ⟨X, B.presheaf⟩
    U.isOpenEmbedding x).hom e3).trans (e2.trans (e4.symm.trans (congrArg
      ((TopCat.Presheaf.stalkFunctor _ x.1).map ((TopCat.Sheaf.forget _ X).map f)) e1.symm)))

/-- The facts about extension by zero from `MMP.Fourfold.compactSupportCohomology_extendByZero`
used below. -/
private structure ExtHyp {X : TopCat.{0}} (U : Opens X) : Prop where
  unit : ∀ G, IsIso ((adjF U).unit.app G)
  zero : ∀ G, ∀ x ∉ U, IsZero (((extF U).obj G).presheaf.stalk x)
  exact : PreservesFiniteLimits (extF U) ∧ PreservesFiniteColimits (extF U)
  csoftExt : ∀ G : TopCat.Sheaf (ModuleCat.{0} ℚ) ((Opens.toTopCat X).obj U),
    (∀ K : Set ((Opens.toTopCat X).obj U), IsCompact K → ∀ W : Opens ((Opens.toTopCat X).obj U),
      K ⊆ W → ∀ s : ((TopCat.Sheaf.forget _ _).obj G).obj (op W),
        ∃ t : ((TopCat.Sheaf.forget _ _).obj G).obj (op ⊤), ∃ (W' : Opens _) (h : W' ≤ W),
          K ⊆ W' ∧ ((TopCat.Sheaf.forget _ _).obj G).map (homOfLE h).op s =
            ((TopCat.Sheaf.forget _ _).obj G).map (homOfLE le_top).op t) →
    (∀ K : Set X, IsCompact K → ∀ W : Opens X, K ⊆ W →
      ∀ s : ((TopCat.Sheaf.forget _ X).obj ((extF U).obj G)).obj (op W),
        ∃ t : ((TopCat.Sheaf.forget _ X).obj ((extF U).obj G)).obj (op ⊤), ∃ (W' : Opens X)
          (h : W' ≤ W), K ⊆ W' ∧ ((TopCat.Sheaf.forget _ X).obj ((extF U).obj G)).map
            (homOfLE h).op s = ((TopCat.Sheaf.forget _ X).obj ((extF U).obj G)).map
              (homOfLE le_top).op t)
  gamma : ∃ γ : extF U ⋙ compactSupportSectionsFunctor ℚ ≅ compactSupportSectionsFunctor ℚ,
    ∀ G (s : compactSupportSections ℚ G),
      ((TopCat.Sheaf.forget _ X).obj ((extF U).obj G)).map
          (homOfLE (le_top : U.isOpenEmbedding.functor.obj ⊤ ≤ ⊤)).op ((γ.inv.app G) s).1 =
        ((TopCat.Sheaf.forget _ _).map ((adjF U).unit.app G)).app (op ⊤) s.1

variable {U} in
private lemma isIso_stalk_counit (h : ExtHyp U) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) X)
    (x : (Opens.toTopCat X).obj U) : IsIso ((st x.1).map ((adjF U).counit.app G)) := by
  haveI : IsIso ((resF U).map ((adjF U).counit.app G)) := by
    haveI := h.unit ((resF U).obj G)
    haveI : IsIso ((adjF U).unit.app ((resF U).obj G) ≫ (resF U).map ((adjF U).counit.app G)) := by
      rw [(adjF U).right_triangle_components G]; exact IsIso.id _
    exact IsIso.of_isIso_comp_left ((adjF U).unit.app ((resF U).obj G)) _
  rw [← (Iso.inv_comp_eq _).mpr (stalk_resF_naturality ((adjF U).counit.app G) x)]
  exact IsIso.comp_isIso' (Iso.isIso_inv _) (IsIso.comp_isIso' inferInstance (Iso.isIso_hom _))

variable {U} in
private lemma stalk_PF (h : ExtHyp U) (x : X) :
    (∀ G, IsZero ((st x).obj ((PF U).obj G))) ∨ ∃ y : X, Nonempty (PF U ⋙ st x ≅ st y) := by
  by_cases hx : x ∈ U
  · exact Or.inr ⟨x, ⟨stalkIsoOfIsIso _ x fun G => isIso_stalk_counit h G ⟨x, hx⟩⟩⟩
  · exact Or.inl fun G => h.zero _ x hx

variable {U} in
private lemma mono_counit (h : ExtHyp U) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) X) :
    Mono ((adjF U).counit.app G) := by
  have hS : (ShortComplex.mk (0 : 0 ⟶ (PF U).obj G) ((adjF U).counit.app G)
      zero_comp).Exact := by
    rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
    intro x
    rw [ShortComplex.exact_iff_mono _ (((st x).map_isZero (isZero_zero _)).eq_of_src _ _)]
    by_cases hx : x ∈ U
    · exact @IsIso.mono_of_iso _ _ _ _ _ (isIso_stalk_counit h G ⟨x, hx⟩)
    · exact mono_of_source_iso_zero _ (h.zero _ x hx).isoZero
  exact (ShortComplex.exact_iff_mono _ rfl).mp hS

variable {U} in
private lemma exact_PF (h : ExtHyp U) :
    PreservesFiniteLimits (PF U) ∧ PreservesFiniteColimits (PF U) :=
  preservesHomology_of_stalk _ (stalk_PF h)

private lemma extHyp [LocallyCompactSpace X] [T2Space X] : ExtHyp U := by
  obtain ⟨h, -⟩ := compactSupportCohomology_extendByZero ℚ X
  obtain ⟨hex, hu, -, hz, hcs, hg⟩ := h U
  exact ⟨hu, hz, hex, hcs, hg⟩

end Open

attribute [local instance] additive_resF additive_extF additive_PF

/-! ### Computing `H^q_c` by c-soft resolutions -/

section Compute

variable (X : TopCat.{0})

/-- c-softness, in the form of `MMP.Fourfold.compactSupportCohomology_of_isCSoft`. -/
private def CSoft {X : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X) : Prop :=
  ∀ K : Set X, IsCompact K → ∀ (W : Opens X), K ⊆ W →
    ∀ s : ((TopCat.Sheaf.forget _ X).obj F).obj (op W),
      ∃ (t : ((TopCat.Sheaf.forget _ X).obj F).obj (op ⊤)) (V : Opens X) (_ : K ⊆ V)
        (hVW : V ≤ W),
        (((TopCat.Sheaf.forget _ X).obj F).map (homOfLE le_top).op).hom t =
          (((TopCat.Sheaf.forget _ X).obj F).map (homOfLE hVW).op).hom s

/-- Compactly supported cohomology as a functor. -/
private noncomputable abbrev HcF (Y : TopCat.{0}) (q : ℤ) :
    TopCat.Sheaf (ModuleCat.{0} ℚ) Y ⥤ ModuleCat.{0} ℚ :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙
    (compactSupportSectionsFunctor ℚ (X := Y)).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor _ q

/-- `Γ_c` as a functor. -/
private noncomputable abbrev Γc (Y : TopCat.{0}) :
    TopCat.Sheaf (ModuleCat.{0} ℚ) Y ⥤ ModuleCat.{0} ℚ :=
  compactSupportSectionsFunctor ℚ (X := Y)

/-- The complex `G[0]` as a bounded below complex. -/
private noncomputable def singlePlus :
    TopCat.Sheaf (ModuleCat.{0} ℚ) X ⥤ CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} ℚ) X) :=
  ObjectProperty.lift _ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0)
    (fun _ => ⟨0, inferInstance⟩)

/-- `K ↦ H^q(RΓ_c(K))` on bounded below complexes. -/
private noncomputable abbrev Ψ (q : ℤ) :
    CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ⥤ ModuleCat.{0} ℚ :=
  HomotopyCategory.Plus.quotient _ ⋙ DerivedCategory.Plus.Qh ⋙
    (Γc X).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor _ q

/-- `K ↦ H^q(Γ_c(K))` on bounded below complexes. -/
private noncomputable abbrev Src (q : ℤ) :
    CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ⥤ ModuleCat.{0} ℚ :=
  CochainComplex.Plus.ι _ ⋙ (Γc X).mapHomologicalComplex _ ⋙
    HomologicalComplex.homologyFunctor _ _ q

/-- The single functor to `D^+` factors through the bounded below homotopy category. -/
private noncomputable def singleIsoQh (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C] :
    DerivedCategory.Plus.singleFunctor C 0 ≅
      HomotopyCategory.Plus.singleFunctor C 0 ⋙ DerivedCategory.Plus.Qh :=
  ((Functor.FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).whiskeringRight C).preimageIso
    (DerivedCategory.singleFunctorIsoCompQh C 0)

private noncomputable def singleIsoQuot :
    HomotopyCategory.Plus.singleFunctor (TopCat.Sheaf (ModuleCat.{0} ℚ) X) 0 ≅
      singlePlus X ⋙ HomotopyCategory.Plus.quotient _ :=
  ((HomotopyCategory.Plus.fullyFaithfulι _).whiskeringRight _).preimageIso
    (HomotopyCategory.Plus.singleFunctorCompιIso _ 0 ≪≫
      HomotopyCategory.singleFunctorPostcompQuotientIso _ 0 ≪≫
      (Functor.isoWhiskerLeft (singlePlus X) (HomotopyCategory.Plus.quotientCompιIso _)).symm)

/-- `H^q_c(X, G) ≅ H^q(RΓ_c(G[0]))`. -/
private noncomputable def singleIso (q : ℤ) : HcF X q ≅ singlePlus X ⋙ Ψ X q :=
  Functor.isoWhiskerRight (singleIsoQh _ ≪≫
      Functor.isoWhiskerRight (singleIsoQuot X) DerivedCategory.Plus.Qh) _

private noncomputable def srcIso (q : ℤ) :
    Src X q ≅ HomotopyCategory.Plus.quotient _ ⋙
      (Γc X).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.homologyFunctor _ q :=
  Functor.isoWhiskerLeft (CochainComplex.Plus.ι _ ⋙ (Γc X).mapHomologicalComplex _)
    ((HomotopyCategory.homologyFunctorFactors _ _ q).symm ≪≫
      Functor.isoWhiskerLeft (HomotopyCategory.quotient _ _)
        (DerivedCategory.homologyFunctorFactorsh _ q).symm) ≪≫
  Functor.isoWhiskerLeft (CochainComplex.Plus.ι _)
    (Functor.isoWhiskerRight
      ((Γc X).mapHomotopyCategoryFactors _).symm
      (DerivedCategory.Qh ⋙ DerivedCategory.homologyFunctor _ q)) ≪≫
  Iso.refl _

/-- The comparison `H^q(Γ_c(K)) ⟶ H^q(RΓ_c(K))`. -/
private noncomputable def θ (q : ℤ) : Src X q ⟶ Ψ X q :=
  (srcIso X q).hom ≫ Functor.whiskerLeft (HomotopyCategory.Plus.quotient _)
    (Functor.whiskerRight (Γc X).rightDerivedFunctorPlusUnith
      (DerivedCategory.Plus.homologyFunctor _ q))

private lemma isIso_θ_app [LocallyCompactSpace X] [T2Space X] (q : ℤ)
    (K : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} ℚ) X)) (hK : ∀ n, CSoft (K.obj.X n)) :
    IsIso ((θ X q).app K) := by
  have := (compactSupportCohomology_of_isCSoft ℚ X).2.2.2.1 K hK
  simp only [θ, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

variable {X}

private lemma isIso_Ψ_map (q : ℤ) {K L : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} ℚ) X)}
    (g : K ⟶ L) [QuasiIso g.hom] : IsIso ((Ψ X q).map g) := by
  have : IsIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient _).map g)) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
        ((HomologicalComplex.mem_quasiIso_iff _).mpr (show QuasiIso g.hom from inferInstance)))
  simp only [Ψ, Functor.comp_map]
  infer_instance

/-- `H^q_c(X, A) ≅ H^q(Γ_c(K))` for a resolution `A[0] ⟶ K` by c-soft sheaves. -/
private noncomputable def cmp [LocallyCompactSpace X] [T2Space X] (q : ℤ)
    {A : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    {K : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} ℚ) X)}
    (ε : (singlePlus X).obj A ⟶ K) [QuasiIso ε.hom] (hK : ∀ n, CSoft (K.obj.X n)) :
    (HcF X q).obj A ≅ (Src X q).obj K :=
  (singleIso X q).app A ≪≫ @asIso _ _ _ _ ((Ψ X q).map ε) (isIso_Ψ_map q ε) ≪≫
    (@asIso _ _ _ _ ((θ X q).app K) (isIso_θ_app X q K hK)).symm

private lemma cmp_naturality [LocallyCompactSpace X] [T2Space X] (q : ℤ)
    {A A' : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    {K K' : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} ℚ) X)}
    (ε : (singlePlus X).obj A ⟶ K) [QuasiIso ε.hom] (hK : ∀ n, CSoft (K.obj.X n))
    (ε' : (singlePlus X).obj A' ⟶ K') [QuasiIso ε'.hom] (hK' : ∀ n, CSoft (K'.obj.X n))
    (ψ : A ⟶ A') (g : K ⟶ K') (h : ε ≫ g = (singlePlus X).map ψ ≫ ε') :
    (cmp q ε hK).hom ≫ (Src X q).map g = (HcF X q).map ψ ≫ (cmp q ε' hK').hom := by
  have hθ := (θ X q).naturality g
  have hΨ : (Ψ X q).map ε ≫ (Ψ X q).map g =
      (Ψ X q).map ((singlePlus X).map ψ) ≫ (Ψ X q).map ε' := by
    simp only [← Functor.map_comp, h]
  have hs := (singleIso X q).hom.naturality ψ
  haveI := isIso_θ_app X q K hK
  haveI := isIso_θ_app X q K' hK'
  simp only [cmp, Iso.trans_hom, Iso.app_hom, asIso_hom, Iso.symm_hom, asIso_inv,
    Category.assoc]
  have h1 : inv ((θ X q).app K) ≫ (Src X q).map g =
      (Ψ X q).map g ≫ inv ((θ X q).app K') := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← hθ, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [h1, ← Category.assoc ((Ψ X q).map ε), hΨ, ← Category.assoc ((HcF X q).map ψ), hs]
  simp only [Functor.comp_map, Category.assoc]

end Compute

/-! ### `ℕ`-indexed c-soft resolutions -/

section ComputeN

section extend

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B] [HasZeroObject A]
  [HasZeroObject B] (G : A ⥤ B) [G.Additive]

/-- The degreewise comparison between `G` applied to an extension and the extension of `G`
applied to the complex. -/
private noncomputable def mapExtendXIso (K : HomologicalComplex A c) :
    ∀ o : Option ι, G.obj (HomologicalComplex.extend.X K o) ≅
      HomologicalComplex.extend.X ((G.mapHomologicalComplex c).obj K) o
  | some _ => Iso.refl _
  | none => IsZero.iso (G.map_isZero (HomologicalComplex.extend.isZero_X _ rfl))
      (HomologicalComplex.extend.isZero_X _ rfl)

private lemma mapExtendXIso_hom_d (K : HomologicalComplex A c) :
    ∀ o₁ o₂ : Option ι, (mapExtendXIso G K o₁).hom ≫
        HomologicalComplex.extend.d ((G.mapHomologicalComplex c).obj K) o₁ o₂ =
      G.map (HomologicalComplex.extend.d K o₁ o₂) ≫ (mapExtendXIso G K o₂).hom
  | none, _ => by
      simp only [HomologicalComplex.extend.d_none_eq_zero _ _ _ rfl, comp_zero, G.map_zero,
        zero_comp]
  | some a, some b => by
      change 𝟙 _ ≫ ((G.mapHomologicalComplex c).obj K).d a b = G.map (K.d a b) ≫ 𝟙 _
      simp
  | some _, none => by
      simp only [HomologicalComplex.extend.d_none_eq_zero' _ _ _ rfl, comp_zero, G.map_zero,
        zero_comp]

/-- `G` applied to an extension is the extension of `G` applied to the complex. -/
private noncomputable def mapExtendIso (K : HomologicalComplex A c) (e : c.Embedding c') :
    (G.mapHomologicalComplex c').obj (K.extend e) ≅
      ((G.mapHomologicalComplex c).obj K).extend e :=
  HomologicalComplex.Hom.isoOfComponents (fun i' => mapExtendXIso G K (e.r i'))
    (fun i' j' _ => mapExtendXIso_hom_d G K (e.r i') (e.r j'))

private lemma mapExtendXIso_naturality {K L : HomologicalComplex A c} (φ : K ⟶ L) :
    ∀ o : Option ι, G.map (HomologicalComplex.extend.mapX φ o) ≫ (mapExtendXIso G L o).hom =
      (mapExtendXIso G K o).hom ≫
        HomologicalComplex.extend.mapX ((G.mapHomologicalComplex c).map φ) o
  | some i => by
      change G.map (φ.f i) ≫ 𝟙 _ = 𝟙 _ ≫ G.map (φ.f i)
      simp
  | none => (HomologicalComplex.extend.isZero_X _ rfl).eq_of_tgt _ _

private lemma mapExtendIso_naturality {K L : HomologicalComplex A c} (φ : K ⟶ L)
    (e : c.Embedding c') :
    (G.mapHomologicalComplex c').map (HomologicalComplex.extendMap φ e) ≫
        (mapExtendIso G L e).hom =
      (mapExtendIso G K e).hom ≫
        HomologicalComplex.extendMap ((G.mapHomologicalComplex c).map φ) e := by
  ext i'
  exact mapExtendXIso_naturality G φ (e.r i')

end extend

variable {X : TopCat.{0}}

private abbrev eN : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ) := ComplexShape.embeddingUpNat

private lemma eN_f_zero : eN.f 0 = 0 := rfl

private lemma eN_f (n : ℕ) : eN.f n = (n : ℤ) := rfl

private lemma extendSingleIso_inv_nat {C : Type*} [Category C] [Abelian C] {Aa Aa' : C}
    (ψ : Aa ⟶ Aa') :
    (HomologicalComplex.extendSingleIso eN Aa 0 0 eN_f_zero).inv ≫
      HomologicalComplex.extendMap ((CochainComplex.single₀ _).map ψ) eN =
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map ψ ≫
        (HomologicalComplex.extendSingleIso eN Aa' 0 0 eN_f_zero).inv := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.extendSingleIso_inv_f, HomologicalComplex.extendSingleIso_inv_f,
    HomologicalComplex.extendMap_f _ eN eN_f_zero,
    HomologicalComplex.single_map_f_self, HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- An `ℕ`-indexed complex as a bounded below `ℤ`-indexed complex. -/
private noncomputable def plusOf (C : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ) :
    CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} ℚ) X) :=
  ⟨C.extend eN, 0, by dsimp [eN]; infer_instance⟩

private noncomputable def plusMap {C C' : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ}
    (f : C ⟶ C') : plusOf C ⟶ plusOf C' :=
  ObjectProperty.homMk (HomologicalComplex.extendMap f eN)

/-- The resolution `A[0] ⟶ C` as a morphism of bounded below complexes. -/
private noncomputable def εOf {A : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    {C : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ}
    (ι : (CochainComplex.single₀ _).obj A ⟶ C) : (singlePlus X).obj A ⟶ plusOf C :=
  ObjectProperty.homMk ((HomologicalComplex.extendSingleIso eN A 0 0 eN_f_zero).inv ≫
    HomologicalComplex.extendMap ι eN)

private lemma quasiIso_εOf {A : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    {C : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ}
    (ι : (CochainComplex.single₀ _).obj A ⟶ C) [QuasiIso ι] : QuasiIso (εOf ι).hom := by
  have : QuasiIso (HomologicalComplex.extendMap ι eN) := inferInstance
  exact inferInstanceAs
    (QuasiIso ((HomologicalComplex.extendSingleIso eN A 0 0 eN_f_zero).inv ≫
      HomologicalComplex.extendMap ι eN))

private lemma CSoft.of_iso {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (e : F ≅ G) (hF : CSoft F) :
    CSoft G := by
  intro K hK W hKW s
  let α := (TopCat.Sheaf.forget _ X).map e.hom
  let β := (TopCat.Sheaf.forget _ X).map e.inv
  have hαβ : ∀ (U : (Opens X)ᵒᵖ) (x : ((TopCat.Sheaf.forget _ X).obj G).obj U),
      α.app U (β.app U x) = x := fun U x => by
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp,
      e.inv_hom_id, CategoryTheory.Functor.map_id]
    rfl
  have hnat : ∀ {U U' : (Opens X)ᵒᵖ} (i : U ⟶ U') (x : ((TopCat.Sheaf.forget _ X).obj F).obj U),
      ((TopCat.Sheaf.forget _ X).obj G).map i (α.app U x) =
        α.app U' (((TopCat.Sheaf.forget _ X).obj F).map i x) := fun i x => by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, α.naturality]
  obtain ⟨t, V, hKV, hVW, h⟩ := hF K hK W hKW (β.app _ s)
  refine ⟨α.app _ t, V, hKV, hVW, ?_⟩
  change ((TopCat.Sheaf.forget _ X).obj G).map _ (α.app _ t) =
    ((TopCat.Sheaf.forget _ X).obj G).map _ s
  rw [hnat, ← hαβ _ s, hnat]
  exact congrArg (α.app _) h

private lemma CSoft.of_isZero {F : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (hF : IsZero F) :
    CSoft F := by
  intro K _ W hKW s
  have hs : IsZero (((TopCat.Sheaf.forget _ X).obj F).obj (op W)) :=
    ((evaluation _ _).obj (op W)).map_isZero ((TopCat.Sheaf.forget _ X).map_isZero hF)
  refine ⟨0, W, hKW, le_rfl, ?_⟩
  rw [(ModuleCat.isZero_iff_subsingleton.mp hs).elim s 0, map_zero, map_zero]

private lemma csoft_plusOf {C : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ}
    (hC : ∀ n, CSoft (C.X n)) (m : ℤ) : CSoft ((plusOf C).obj.X m) := by
  by_cases hm : 0 ≤ m
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    exact CSoft.of_iso (C.extendXIso eN rfl).symm (hC k)
  · exact CSoft.of_isZero (C.isZero_extend_X eN m fun i hi => hm (by
      rw [← hi]; exact Int.natCast_nonneg i))

/-- `H^n(Γ_c(C⁺)) ≅ H^n(Γ_c(C))` for the extension `C⁺` of an `ℕ`-indexed complex. -/
private noncomputable def isoB (C : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ) (n : ℕ) :
    (((Γc X).mapHomologicalComplex (ComplexShape.up ℤ)).obj (C.extend eN)).homology n ≅
      (((Γc X).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n :=
  HomologicalComplex.homologyMapIso (mapExtendIso (Γc X) C eN) (n : ℤ) ≪≫
    HomologicalComplex.extendHomologyIso _ eN (eN_f n)

private lemma isoB_naturality {C C' : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ}
    (g : C ⟶ C') (n : ℕ) :
    HomologicalComplex.homologyMap (((Γc X).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap g eN)) n ≫ (isoB C' n).hom =
      (isoB C n).hom ≫
        HomologicalComplex.homologyMap ((Γc X).mapHomologicalComplex _ |>.map g) n := by
  have h2 := congrArg (fun f => HomologicalComplex.homologyMap f (n : ℤ))
    (mapExtendIso_naturality (Γc X) g eN)
  simp only [HomologicalComplex.homologyMap_comp] at h2
  have h3 := HomologicalComplex.extendHomologyIso_hom_naturality
    ((Γc X).mapHomologicalComplex (ComplexShape.up ℕ) |>.map g) eN (j := n) (j' := (n : ℤ)) (eN_f n)
  simp only [isoB, Iso.trans_hom, HomologicalComplex.homologyMapIso_hom, Category.assoc]
  rw [← h3, ← reassoc_of% h2]

/-- `isoB`, with the source written as `Src`. -/
private noncomputable def isoB' (C : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ) (n : ℕ) :
    (Src X n).obj (plusOf C) ≅
      (((Γc X).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n :=
  isoB C n

private lemma isoB'_naturality {C C' : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ}
    (g : C ⟶ C') (n : ℕ) :
    (Src X n).map (plusMap g) ≫ (isoB' C' n).hom =
      (isoB' C n).hom ≫
        HomologicalComplex.homologyMap ((Γc X).mapHomologicalComplex _ |>.map g) n :=
  isoB_naturality g n

/-- `H^n_c(X, A) ≅ H^n(Γ_c(C))` for an `ℕ`-indexed resolution `A[0] ⟶ C` by c-soft sheaves. -/
private noncomputable def cmpN [LocallyCompactSpace X] [T2Space X]
    {A : TopCat.Sheaf (ModuleCat.{0} ℚ) X} {C : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ}
    (ι : (CochainComplex.single₀ _).obj A ⟶ C) [QuasiIso ι] (hC : ∀ n, CSoft (C.X n)) (n : ℕ) :
    (HcF X n).obj A ≅ (((Γc X).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n :=
  haveI := quasiIso_εOf ι
  cmp (n : ℤ) (εOf ι) (csoft_plusOf hC) ≪≫ isoB' C n

private lemma εOf_naturality {A A' : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    {C C' : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ}
    (ι : (CochainComplex.single₀ _).obj A ⟶ C) (ι' : (CochainComplex.single₀ _).obj A' ⟶ C')
    (ψ : A ⟶ A') (g : C ⟶ C') (h : ι ≫ g = (CochainComplex.single₀ _).map ψ ≫ ι') :
    εOf ι ≫ plusMap g = (singlePlus X).map ψ ≫ εOf ι' := by
  ext1
  change ((HomologicalComplex.extendSingleIso eN A 0 0 eN_f_zero).inv ≫
      HomologicalComplex.extendMap ι eN) ≫ HomologicalComplex.extendMap g eN =
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map ψ ≫
      ((HomologicalComplex.extendSingleIso eN A' 0 0 eN_f_zero).inv ≫
        HomologicalComplex.extendMap ι' eN)
  rw [Category.assoc, ← HomologicalComplex.extendMap_comp, h, HomologicalComplex.extendMap_comp,
    ← Category.assoc, extendSingleIso_inv_nat, Category.assoc]

private lemma cmpN_naturality [LocallyCompactSpace X] [T2Space X]
    {A A' : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    {C C' : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ}
    (ι : (CochainComplex.single₀ _).obj A ⟶ C) [QuasiIso ι] (hC : ∀ n, CSoft (C.X n))
    (ι' : (CochainComplex.single₀ _).obj A' ⟶ C') [QuasiIso ι'] (hC' : ∀ n, CSoft (C'.X n))
    (ψ : A ⟶ A') (g : C ⟶ C') (h : ι ≫ g = (CochainComplex.single₀ _).map ψ ≫ ι') (n : ℕ) :
    (cmpN ι hC n).hom ≫ HomologicalComplex.homologyMap ((Γc X).mapHomologicalComplex _ |>.map g) n =
      (HcF X n).map ψ ≫ (cmpN ι' hC' n).hom := by
  haveI := quasiIso_εOf ι
  haveI := quasiIso_εOf ι'
  have h1 := cmp_naturality (n : ℤ) (εOf ι) (csoft_plusOf hC) (εOf ι') (csoft_plusOf hC') ψ
    (plusMap g) (εOf_naturality ι ι' ψ g h)
  simp only [cmpN, Iso.trans_hom, Category.assoc]
  rw [← isoB'_naturality, ← Category.assoc, h1, Category.assoc]

private lemma isZero_HcF_neg [LocallyCompactSpace X] [T2Space X]
    {A : TopCat.Sheaf (ModuleCat.{0} ℚ) X} {C : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ}
    (ι : (CochainComplex.single₀ _).obj A ⟶ C) [QuasiIso ι] (hC : ∀ n, CSoft (C.X n)) (q : ℤ)
    (hq : q < 0) : IsZero ((HcF X q).obj A) := by
  haveI := quasiIso_εOf ι
  refine IsZero.of_iso ?_ (cmp q (εOf ι) (csoft_plusOf hC))
  refine (HomologicalComplex.ExactAt.of_isZero ?_).isZero_homology
  exact (Γc X).map_isZero (C.isZero_extend_X eN q fun i hi => by
    rw [eN_f] at hi
    have := Int.natCast_nonneg i; lia)

end ComputeN

/-! ### Maps from an injective resolution to a complex of injectives -/

section Homotopy

variable {C : Type*} [Category C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- A morphism from the resolved object to a complex of injectives, killed by the first
differential, lifts to the resolution. -/
private lemma exists_hom_of_injective {Z : C} (I : InjectiveResolution Z) (K : CochainComplex C ℕ)
    (hK : ∀ n, Injective (K.X n)) (φ : Z ⟶ K.X 0) (hφ : φ ≫ K.d 0 1 = 0) :
    ∃ g : I.cocomplex ⟶ K, I.ι.f 0 ≫ g.f 0 = φ := by
  haveI := hK 0
  haveI := hK 1
  haveI := fun n => hK (n + 2)
  let g0 : I.cocomplex.X 0 ⟶ K.X 0 := Injective.factorThru φ (I.ι.f 0)
  have hg0 : I.ι.f 0 ≫ g0 = φ := Injective.comp_factorThru _ _
  let g1 : I.cocomplex.X 1 ⟶ K.X 1 := I.exact₀.descToInjective (g0 ≫ K.d 0 1) (by
    change I.ι.f 0 ≫ g0 ≫ K.d 0 1 = 0
    rw [reassoc_of% hg0, hφ])
  have hg1 : I.cocomplex.d 0 1 ≫ g1 = g0 ≫ K.d 0 1 := I.exact₀.comp_descToInjective _ _
  refine ⟨CochainComplex.mkHom _ _ g0 g1 hg1.symm fun n ⟨g, g', w⟩ =>
    ⟨(I.exact_succ n).descToInjective (g' ≫ K.d (n + 1) (n + 2))
      (by simp [reassoc_of% w.symm]), ((I.exact_succ n).comp_descToInjective _ _).symm⟩, ?_⟩
  rw [CochainComplex.mkHom_f_0]
  exact hg0

variable {Z : C} (I : InjectiveResolution Z) {K : CochainComplex C ℕ} (hK : ∀ n, Injective (K.X n))

private noncomputable def hZero (f : I.cocomplex ⟶ K) (comm : I.ι.f 0 ≫ f.f 0 = 0) :
    I.cocomplex.X 1 ⟶ K.X 0 :=
  haveI := hK 0
  I.exact₀.descToInjective (f.f 0) comm

private lemma comp_hZero (f : I.cocomplex ⟶ K) (comm : I.ι.f 0 ≫ f.f 0 = 0) :
    I.cocomplex.d 0 1 ≫ hZero I hK f comm = f.f 0 :=
  haveI := hK 0
  I.exact₀.comp_descToInjective _ _

private noncomputable def hOne (f : I.cocomplex ⟶ K) (comm : I.ι.f 0 ≫ f.f 0 = 0) :
    I.cocomplex.X 2 ⟶ K.X 1 :=
  haveI := hK 1
  (I.exact_succ 0).descToInjective (f.f 1 - hZero I hK f comm ≫ K.d 0 1)
    (by rw [Preadditive.comp_sub, ← Category.assoc, comp_hZero, HomologicalComplex.Hom.comm,
      sub_self])

private lemma comp_hOne (f : I.cocomplex ⟶ K) (comm : I.ι.f 0 ≫ f.f 0 = 0) :
    I.cocomplex.d 1 2 ≫ hOne I hK f comm = f.f 1 - hZero I hK f comm ≫ K.d 0 1 :=
  haveI := hK 1
  (I.exact_succ 0).comp_descToInjective _ _

private noncomputable def hSucc (f : I.cocomplex ⟶ K) (n : ℕ) (g : I.cocomplex.X (n + 1) ⟶ K.X n)
    (g' : I.cocomplex.X (n + 2) ⟶ K.X (n + 1))
    (w : f.f (n + 1) = I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ K.d n (n + 1)) :
    I.cocomplex.X (n + 3) ⟶ K.X (n + 2) :=
  haveI := hK (n + 2)
  (I.exact_succ (n + 1)).descToInjective (f.f (n + 2) - g' ≫ K.d _ _) (by
      dsimp
      rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, w, Preadditive.add_comp,
        Category.assoc, Category.assoc, HomologicalComplex.d_comp_d, comp_zero,
        add_zero, sub_self])

private lemma comp_hSucc (f : I.cocomplex ⟶ K) (n : ℕ) (g : I.cocomplex.X (n + 1) ⟶ K.X n)
    (g' : I.cocomplex.X (n + 2) ⟶ K.X (n + 1))
    (w : f.f (n + 1) = I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ K.d n (n + 1)) :
    I.cocomplex.d (n + 2) (n + 3) ≫ hSucc I hK f n g g' w = f.f (n + 2) - g' ≫ K.d _ _ :=
  haveI := hK (n + 2)
  (I.exact_succ (n + 1)).comp_descToInjective _ _

/-- A map from an injective resolution to a complex of injectives vanishing on the resolved
object is homotopic to zero. -/
private noncomputable def homotopyZeroOfInj (f : I.cocomplex ⟶ K) (comm : I.ι.f 0 ≫ f.f 0 = 0) :
    Homotopy f 0 :=
  Homotopy.mkCoinductive _ (hZero I hK f comm) (by simp [comp_hZero])
    (hOne I hK f comm) (by simp [comp_hOne]) (fun n ⟨g, g', w⟩ =>
    ⟨hSucc I hK f n g g' (by simp only [w, add_comm]), by simp [comp_hSucc]⟩)

/-- Two maps from an injective resolution to a complex of injectives which agree on the
resolved object are homotopic. -/
private noncomputable def homotopyOfInj (f g : I.cocomplex ⟶ K)
    (h : I.ι.f 0 ≫ f.f 0 = I.ι.f 0 ≫ g.f 0) : Homotopy f g :=
  Homotopy.equivSubZero.invFun (homotopyZeroOfInj I hK (f - g) (by
    rw [HomologicalComplex.sub_f_apply, Preadditive.comp_sub, h, sub_self]))

end Homotopy

/-! ### Sections with compact support in an open subset -/

section Sections

variable {Y : TopCat.{0}}

/-- A germ vanishes iff the section vanishes on a neighbourhood. -/
private lemma germ_eq_zero_iff (F : TopCat.Presheaf (ModuleCat.{0} ℚ) Y) {W : Opens Y} (x : Y)
    (hx : x ∈ W) (s : F.obj (op W)) :
    F.germ W x hx s = 0 ↔ ∃ (N : Opens Y) (_ : x ∈ N) (h : N ≤ W), F.map (homOfLE h).op s = 0 := by
  constructor
  · intro h0
    have h1 : F.germ W x hx s = F.germ W x hx 0 := by rw [h0, map_zero]
    obtain ⟨N, hN, i₁, i₂, e⟩ := TopCat.Presheaf.germ_eq F x hx hx s 0 h1
    exact ⟨N, hN, i₁.le, by rw [show homOfLE i₁.le = i₁ from rfl, e, map_zero]⟩
  · rintro ⟨N, hN, h, e⟩
    rw [← F.germ_res_apply (homOfLE h) x hN s, e, map_zero]

private lemma eq_zero_of_germ (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Y) {W : Opens Y}
    (s : F.obj.obj (op W)) (h : ∀ x (hx : x ∈ W), F.presheaf.germ W x hx s = 0) : s = 0 :=
  TopCat.Presheaf.section_ext F W s 0 fun x hx => by rw [h x hx, map_zero]

private lemma injective_app {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) Y} (φ : F ⟶ G) (hφ : Mono φ)
    (U : Opens Y) : Function.Injective (φ.hom.app (op U)) := by
  have h1 : Mono ((TopCat.Sheaf.forget (ModuleCat.{0} ℚ) Y).map φ) :=
    (TopCat.Sheaf.forget (ModuleCat.{0} ℚ) Y).map_mono φ
  have : Mono (((TopCat.Sheaf.forget (ModuleCat.{0} ℚ) Y).map φ).app (op U)) :=
    (NatTrans.mono_iff_mono_app _).mp h1 (op U)
  exact (ModuleCat.mono_iff_injective _).mp this

/-- The germ of the image of a section under a morphism of sheaves. -/
private lemma germ_map {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) Y} (φ : F ⟶ G) {W : Opens Y}
    (x : Y) (hx : x ∈ W) (s : F.obj.obj (op W)) :
    G.presheaf.germ W x hx (φ.hom.app (op W) s) =
      (TopCat.Presheaf.stalkFunctor _ x).map φ.hom (F.presheaf.germ W x hx s) :=
  (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hx φ.hom s).symm

/-- A global section has support in a compact subset of the open `U`. -/
private def SuppIn (U : Opens Y) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) Y) (t : G.obj.obj (op ⊤)) :
    Prop :=
  ∃ K : Set Y, IsCompact K ∧ K ⊆ U ∧ ∀ x ∉ K, G.presheaf.germ ⊤ x (Opens.mem_top x) t = 0

/-- Global sections. -/
private noncomputable abbrev ΓF (Y : TopCat.{0}) :
    TopCat.Sheaf (ModuleCat.{0} ℚ) Y ⥤ ModuleCat.{0} ℚ :=
  TopCat.Sheaf.forget _ Y ⋙ (evaluation (Opens Y)ᵒᵖ (ModuleCat.{0} ℚ)).obj (op ⊤)

/-- The inclusion of compactly supported global sections into all global sections. -/
private noncomputable def inclΓ (Y : TopCat.{0}) : Γc Y ⟶ ΓF Y where
  app F := ModuleCat.ofHom (compactSupportSections ℚ F).subtype
  naturality _ _ _ := rfl

variable (U : Opens Y)

/-- The counit `j_! j^* G ⟶ G` on compactly supported global sections. -/
private noncomputable def aU : PF U ⋙ Γc Y ⟶ ΓF Y where
  app G := (Γc Y).map ((adjF U).counit.app G) ≫ (inclΓ Y).app G
  naturality {G G'} f := by
    have := (adjF U).counit.naturality f
    ext s
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun φ => φ.hom) this) (op ⊤))
      s.1

private lemma aU_apply (G : TopCat.Sheaf (ModuleCat.{0} ℚ) Y) (s) :
    (aU U).app G s = ((adjF U).counit.app G).hom.app (op ⊤) s.1 := rfl

variable {U}

private lemma aU_injective (h : ExtHyp U) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) Y) :
    Function.Injective ((aU U).app G) := fun _ _ hss' =>
  Subtype.ext (injective_app _ (mono_counit h G) ⊤ hss')

/-- The counit carries compactly supported sections of `j_! j^* G` to sections of `G` with compact
support in `U`. -/
private lemma suppIn_aU (h : ExtHyp U) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) Y)
    (s : (PF U ⋙ Γc Y).obj G) : SuppIn U G ((aU U).app G s) := by
  rw [aU_apply]
  obtain ⟨K₀, hK₀, hs⟩ := s.2
  let P : TopCat.Presheaf (ModuleCat.{0} ℚ) Y := ((PF U).obj G).presheaf
  let Z : Set Y := {x | P.germ ⊤ x (Opens.mem_top x) s.1 ≠ 0}
  have hZc : IsClosed Z := by
    refine isOpen_compl_iff.mp (isOpen_iff_forall_mem_open.mpr fun x hx => ?_)
    have hx0 : P.germ ⊤ x (Opens.mem_top x) s.1 = 0 := not_not.mp hx
    obtain ⟨N, hxN, hN, hsN⟩ := (germ_eq_zero_iff P x _ s.1).mp hx0
    refine ⟨N, fun x' hx' => ?_, N.2, hxN⟩
    show ¬ ¬ _
    rw [not_not]
    exact (P.germ_res_apply (homOfLE hN) x' hx' s.1).symm.trans
      ((congrArg _ hsN).trans (map_zero _))
  refine ⟨Z, hK₀.of_isClosed_subset hZc fun x hx => by_contra fun h' => hx (hs x h'),
    fun x hx => by_contra fun hxU => hx ?_, fun x hx => ?_⟩
  · exact (ModuleCat.isZero_iff_subsingleton.mp (h.zero _ x hxU)).elim _ _
  · refine (germ_map ((adjF U).counit.app G) x (Opens.mem_top x) s.1).trans ?_
    exact (congrArg _ (not_not.mp hx)).trans (map_zero _)

set_option backward.isDefEq.respectTransparency false in
private lemma exists_aU [T2Space Y] (h : ExtHyp U) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) Y)
    (t : G.obj.obj (op ⊤)) (ht : SuppIn U G t) : ∃ s, (aU U).app G s = t := by
  obtain ⟨K, hK, hKU, htK⟩ := ht
  obtain ⟨γ, hγ⟩ := h.gamma
  let G' := (resF U).obj G
  let iU := homOfLE (le_top : U.isOpenEmbedding.functor.obj ⊤ ≤ ⊤)
  let t' : G'.obj.obj (op ⊤) := G.obj.map iU.op t
  have hgerm : ∀ y : (Opens.toTopCat Y).obj U,
      (AlgebraicGeometry.PresheafedSpace.restrictStalkIso ⟨Y, G.presheaf⟩ U.isOpenEmbedding y).hom
        (G'.presheaf.germ ⊤ y (Opens.mem_top y) t') =
          G.presheaf.germ ⊤ y.1 (Opens.mem_top _) t := by
    intro y
    refine (AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ_apply ⟨Y, G.presheaf⟩
      U.isOpenEmbedding ⊤ y (Opens.mem_top y) t').trans ?_
    exact G.presheaf.germ_res_apply iU y.1 _ t
  have ht' : t' ∈ compactSupportSections ℚ G' := by
    refine ⟨U.inclusion' ⁻¹' K, (U.isOpenEmbedding.isInducing.isCompact_preimage_iff
      (fun x hx => ⟨⟨x, hKU hx⟩, rfl⟩)).mpr hK, fun y hy => ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (AlgebraicGeometry.PresheafedSpace.restrictStalkIso
      ⟨Y, G.presheaf⟩ U.isOpenEmbedding y).hom).1
    rw [map_zero]
    exact (hgerm y).trans (htK _ hy)
  let s := (γ.inv.app G') ⟨t', ht'⟩
  refine ⟨s, ?_⟩
  rw [aU_apply]
  have hs : ((extF U).obj G').obj.map iU.op s.1 = ((adjF U).unit.app G').hom.app (op ⊤) t' :=
    hγ G' ⟨t', ht'⟩
  -- the counit of `s` restricts to `t'` on `U`
  have hres : G.obj.map iU.op (((adjF U).counit.app G).hom.app (op ⊤) s.1) = t' := by
    have nat := NatTrans.naturality_apply ((adjF U).counit.app G).hom iU.op s.1
    refine nat.symm.trans ?_
    change ((adjF U).counit.app G).hom.app (op (U.isOpenEmbedding.functor.obj ⊤))
      (((extF U).obj G').obj.map iU.op s.1) = t'
    rw [hs]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun f => f.hom)
      ((adjF U).right_triangle_components G)) (op ⊤)) t'
  refine TopCat.Presheaf.section_ext G ⊤ _ _ fun x _ => ?_
  by_cases hxU : x ∈ U
  · have hx' : x ∈ U.isOpenEmbedding.functor.obj ⊤ := ⟨⟨x, hxU⟩, Opens.mem_top _, rfl⟩
    rw [← G.presheaf.germ_res_apply iU x hx', ← G.presheaf.germ_res_apply iU x hx' t]
    exact congrArg _ hres
  · refine (germ_map ((adjF U).counit.app G) x (Opens.mem_top x) s.1).trans ?_
    have hsub := ModuleCat.isZero_iff_subsingleton.mp (h.zero ((resF U).obj G) x hxU)
    refine (congrArg _ (@Subsingleton.elim _ hsub _ 0)).trans ((map_zero _).trans ?_)
    exact (htK x fun hxK => hxU (hKU hxK)).symm

end Sections

/-! ### The one-point compactification of an open subset and the collapse maps -/

section Compactification

variable {S : Type} [TopologicalSpace S]

/-- The collapse `S → V⁺` of the complement of `V` to the point at infinity. -/
private noncomputable def κf (V : Opens S) : S → OnePoint V := fun x =>
  open Classical in if h : x ∈ V then ((⟨x, h⟩ : V) : OnePoint V) else OnePoint.infty

private lemma κf_of_mem (V : Opens S) {x : S} (h : x ∈ V) :
    κf V x = ((⟨x, h⟩ : V) : OnePoint V) := by
  simp [κf, h]

private lemma κf_of_notMem (V : Opens S) {x : S} (h : x ∉ V) : κf V x = OnePoint.infty := by
  simp [κf, h]

private lemma κf_preimage_some_image (V : Opens S) (A : Set V) :
    κf V ⁻¹' ((↑) '' A : Set (OnePoint V)) = Subtype.val '' A := by
  ext x
  by_cases hx : x ∈ V
  · rw [Set.mem_preimage, κf_of_mem V hx]
    constructor
    · rintro ⟨a, ha, hax⟩
      exact ⟨a, ha, by rw [OnePoint.coe_eq_coe] at hax; exact hax ▸ rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
  · rw [Set.mem_preimage, κf_of_notMem V hx]
    constructor
    · rintro ⟨a, -, h⟩
      exact absurd h (OnePoint.coe_ne_infty a)
    · rintro ⟨a, -, rfl⟩
      exact absurd a.2 hx

variable [T2Space S]

private lemma continuous_κf (V : Opens S) : Continuous (κf V) := by
  rw [continuous_def]
  intro W hW
  by_cases hinf : OnePoint.infty ∈ W
  · rw [OnePoint.isOpen_iff_of_mem hinf] at hW
    obtain ⟨hcl, hco⟩ := hW
    set C : Set V := (OnePoint.some ⁻¹' W)ᶜ
    have hWC : W = ((↑) '' C : Set (OnePoint V))ᶜ := by
      ext z
      induction z using OnePoint.rec with
      | infty => simp [hinf, C]
      | coe y => simp [C]
    rw [hWC, Set.preimage_compl, κf_preimage_some_image]
    exact (hco.image continuous_subtype_val).isClosed.isOpen_compl
  · rw [OnePoint.isOpen_iff_of_notMem hinf] at hW
    have hWC : W = ((↑) '' (OnePoint.some ⁻¹' W) : Set (OnePoint V)) := by
      ext z
      induction z using OnePoint.rec with
      | infty => simp [hinf]
      | coe y => simp
    rw [hWC, κf_preimage_some_image]
    exact V.2.isOpenMap_subtype_val _ hW

/-- The collapse `V⁺ → V'⁺` for `V' ⊆ V`. -/
private noncomputable def cf {V' V : Opens S} (_ : V' ≤ V) : OnePoint V → OnePoint V' :=
  fun z => Option.elim z OnePoint.infty (fun y => κf V' (y : S))

private lemma cf_infty {V' V : Opens S} (h : V' ≤ V) : cf h OnePoint.infty = OnePoint.infty := rfl

private lemma cf_coe {V' V : Opens S} (h : V' ≤ V) (y : V) : cf h (y : OnePoint V) = κf V' y := rfl

private lemma cf_comp_κf {V' V : Opens S} (h : V' ≤ V) (x : S) : cf h (κf V x) = κf V' x := by
  by_cases hx : x ∈ V
  · rw [κf_of_mem V hx]; rfl
  · rw [κf_of_notMem V hx, cf_infty, κf_of_notMem V' fun h' => hx (h h')]

private lemma continuous_cf {V' V : Opens S} (h : V' ≤ V) : Continuous (cf h) := by
  rw [continuous_iff_continuousAt]
  intro z
  induction z using OnePoint.rec with
  | coe y =>
    rw [OnePoint.continuousAt_coe]
    exact ((continuous_κf V').comp continuous_subtype_val).continuousAt
  | infty =>
    rw [OnePoint.continuousAt_infty']
    refine (OnePoint.hasBasis_nhds_infty.tendsto_right_iff).2 fun C ⟨_, hCco⟩ => ?_
    have hK : IsCompact (Set.inclusion h '' C) := hCco.image (continuous_inclusion h)
    filter_upwards [hK.compl_mem_coclosedCompact_of_isClosed hK.isClosed] with y hy
    by_cases hy' : (y : S) ∈ V'
    · left
      refine ⟨⟨y, hy'⟩, fun hC => hy ⟨⟨y, hy'⟩, hC, rfl⟩, ?_⟩
      change _ = κf V' y
      rw [κf_of_mem V' hy']
    · right
      change κf V' y = _
      rw [κf_of_notMem V' hy']

end Compactification

section CompactificationTop

variable {S : TopCat.{0}} [T2Space S]

/-- The one-point compactification `V⁺` of an open subset `V ⊆ S`. -/
private noncomputable abbrev XV (V : Opens S) : TopCat.{0} := TopCat.of (OnePoint V)

/-- The collapse `S → V⁺`. -/
private noncomputable def κV (V : Opens S) : S ⟶ XV V :=
  TopCat.ofHom ⟨κf V, continuous_κf V⟩

/-- The collapse `V⁺ → V'⁺`. -/
private noncomputable def cV {V' V : Opens S} (h : V' ≤ V) : XV V ⟶ XV V' :=
  TopCat.ofHom ⟨cf h, continuous_cf h⟩

private lemma κV_apply (V : Opens S) (x : S) : κV V x = κf V x := rfl

private lemma cV_apply {V' V : Opens S} (h : V' ≤ V) (z : XV V) : cV h z = cf h z := rfl

private lemma κV_comp_cV {V' V : Opens S} (h : V' ≤ V) : κV V ≫ cV h = κV V' := by
  ext x
  exact cf_comp_κf h x

/-- The open `V ⊆ V⁺`. -/
private noncomputable def UV (V : Opens S) : Opens (XV V) :=
  ⟨Set.range ((↑) : V → OnePoint V), OnePoint.isOpen_range_coe⟩

private lemma infty_notMem_UV (V : Opens S) : (OnePoint.infty : OnePoint V) ∉ UV V :=
  fun ⟨_, h⟩ => OnePoint.coe_ne_infty _ h

private lemma coe_mem_UV (V : Opens S) (y : V) : ((y : OnePoint V) : XV V) ∈ UV V := ⟨y, rfl⟩

end CompactificationTop

/-! ### Comparing sections along the collapse maps -/

section Lift

/-- A natural transformation `F₁ ⟶ F₂` lifting `a₁ : F₁ ⟶ F₀` through an injective `a₂`, when the
image of `a₁` lies in that of `a₂`. -/
private noncomputable def liftOfRange {C : Type*} [Category C] {F₁ F₂ F₀ : C ⥤ ModuleCat.{0} ℚ}
    (a₁ : F₁ ⟶ F₀) (a₂ : F₂ ⟶ F₀) (h₂ : ∀ X, Function.Injective (a₂.app X))
    (h : ∀ X x, ∃ y, a₂.app X y = a₁.app X x) : F₁ ⟶ F₂ where
  app X := ModuleCat.ofHom
    ((LinearEquiv.ofInjective (a₂.app X).hom (h₂ X)).symm.toLinearMap ∘ₗ
      (a₁.app X).hom.codRestrict (LinearMap.range (a₂.app X).hom) fun x => h X x)
  naturality {X Y} f := by
    ext x
    apply h₂ Y
    simp only [ModuleCat.comp_apply, ModuleCat.hom_ofHom, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply]
    rw [← ModuleCat.comp_apply, a₂.naturality, ModuleCat.comp_apply]
    have e1 : ∀ (Z : C) (z : F₁.obj Z),
        a₂.app Z ((LinearEquiv.ofInjective (a₂.app Z).hom (h₂ Z)).symm
        ((a₁.app Z).hom.codRestrict (LinearMap.range (a₂.app Z).hom) (fun x => h Z x) z)) =
          a₁.app Z z := fun Z z =>
      (LinearEquiv.ofInjective_symm_apply (a₂.app Z).hom (h := h₂ Z) _).trans rfl
    rw [e1, e1, ← ModuleCat.comp_apply, a₁.naturality, ModuleCat.comp_apply]

private lemma liftOfRange_comp {C : Type*} [Category C] {F₁ F₂ F₀ : C ⥤ ModuleCat.{0} ℚ}
    (a₁ : F₁ ⟶ F₀) (a₂ : F₂ ⟶ F₀) (h₂ : ∀ X, Function.Injective (a₂.app X))
    (h : ∀ X x, ∃ y, a₂.app X y = a₁.app X x) : liftOfRange a₁ a₂ h₂ h ≫ a₂ = a₁ := by
  ext X x
  exact (LinearEquiv.ofInjective_symm_apply (a₂.app X).hom (h := h₂ X) _).trans rfl

private lemma liftOfRange_app_apply {C : Type*} [Category C] {F₁ F₂ F₀ : C ⥤ ModuleCat.{0} ℚ}
    (a₁ : F₁ ⟶ F₀) (a₂ : F₂ ⟶ F₀) (h₂ : ∀ X, Function.Injective (a₂.app X))
    (h : ∀ X x, ∃ y, a₂.app X y = a₁.app X x) (X : C) (x : F₁.obj X) :
    a₂.app X ((liftOfRange a₁ a₂ h₂ h).app X x) = a₁.app X x := by
  rw [← ModuleCat.comp_apply, ← NatTrans.comp_app, liftOfRange_comp]

end Lift

section Transfer

/-- The germ of a section of a direct image vanishes only if the germ of the section vanishes. -/
private lemma germ_eq_zero_of_push {Y Z : TopCat.{0}} (f : Y ⟶ Z)
    (G : TopCat.Sheaf (ModuleCat.{0} ℚ) Y)
    {W : Opens Z} (t : G.obj.obj (op ((Opens.map f).obj W))) (y : Y) (hy : f y ∈ W)
    (h : ((TopCat.Sheaf.pushforward _ f).obj G).presheaf.germ W (f y) hy t = 0) :
    G.presheaf.germ ((Opens.map f).obj W) y hy t = 0 := by
  rw [← TopCat.Presheaf.stalkPushforward_germ_apply _ f G.presheaf W y hy t]
  erw [h]
  exact map_zero _

variable {S : TopCat.{0}} [T2Space S] [LocallyCompactSpace S]

private lemma t2Space_XV (V : Opens S) : T2Space (XV V) := by
  haveI : LocallyCompactSpace V := V.2.isOpenEmbedding_subtypeVal.locallyCompactSpace
  exact inferInstanceAs (T2Space (OnePoint V))

attribute [local instance] t2Space_XV

/-- A global section of `G` has compact support in `V` iff its pushforward to `V⁺` has compact
support in `V`. -/
private lemma suppIn_push_iff (V : Opens S) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) S)
    (t : G.obj.obj (op ⊤)) :
    SuppIn (UV V) ((TopCat.Sheaf.pushforward _ (κV V)).obj G) t ↔ SuppIn V G t := by
  constructor
  · rintro ⟨K, hK, hKU, hKt⟩
    refine ⟨Subtype.val '' (OnePoint.some ⁻¹' K), ?_, ?_, fun x hx => ?_⟩
    · exact ((OnePoint.isOpenEmbedding_coe.isInducing.isCompact_preimage_iff
        (fun z hz => hKU hz)).mpr hK).image continuous_subtype_val
    · rintro _ ⟨y, -, rfl⟩; exact y.2
    · have hxK : κV V x ∉ K := by
        intro hk
        obtain ⟨y, hy⟩ := hKU hk
        have hxV : x ∈ V := by
          by_contra hxV
          rw [κV_apply, κf_of_notMem V hxV] at hy
          exact OnePoint.coe_ne_infty _ hy
        rw [κV_apply, κf_of_mem V hxV] at hk
        exact hx ⟨⟨x, hxV⟩, hk, rfl⟩
      exact germ_eq_zero_of_push (W := ⊤) (κV V) G t x (Opens.mem_top _) (hKt _ hxK)
  · rintro ⟨K, hK, hKV, hKt⟩
    let K' : Set V := Subtype.val ⁻¹' K
    have hK' : IsCompact K' := (V.2.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage_iff
      (by rwa [Subtype.range_coe])).mpr hK
    let K'' : Set (XV V) := ((↑) : V → OnePoint V) '' K'
    have hK'' : IsCompact K'' := hK'.image OnePoint.continuous_coe
    refine ⟨K'', hK'', ?_, fun z hz => ?_⟩
    · rintro _ ⟨y, -, rfl⟩; exact coe_mem_UV V y
    · let N : Opens (XV V) := ⟨K''ᶜ, hK''.isClosed.isOpen_compl⟩
      refine (germ_eq_zero_iff ((TopCat.Sheaf.pushforward _ (κV V)).obj G).presheaf z
        (Opens.mem_top z) t).mpr
        ⟨N, hz, le_top, ?_⟩
      change G.obj.map (homOfLE (le_top : (Opens.map (κV V)).obj N ≤ ⊤)).op t = 0
      refine eq_zero_of_germ G _ fun x hx => ?_
      have hxK : x ∉ K := by
        intro hxK
        apply hx
        change κf V x ∈ K''
        rw [κf_of_mem V (hKV hxK)]
        exact ⟨⟨x, hKV hxK⟩, hxK, rfl⟩
      refine (G.presheaf.germ_res_apply _ x hx t).trans (hKt x hxK)

/-- Compact support in `V'` for the pushforward along the collapse `V⁺ → V'⁺` gives compact
support in `V`. -/
private lemma suppIn_of_push_cV {V' V : Opens S} (h : V' ≤ V)
    (G : TopCat.Sheaf (ModuleCat.{0} ℚ) (XV V)) (t : G.obj.obj (op ⊤))
    (ht : SuppIn (UV V') ((TopCat.Sheaf.pushforward _ (cV h)).obj G) t) : SuppIn (UV V) G t := by
  obtain ⟨K, hK, hKU, hKt⟩ := ht
  refine ⟨cV h ⁻¹' K, (hK.isClosed.preimage (cV h).hom.continuous).isCompact, fun z hz => ?_,
    fun z hz => germ_eq_zero_of_push (W := ⊤) (cV h) G t z (Opens.mem_top _) (hKt _ hz)⟩
  induction z using OnePoint.rec with
  | infty => exact absurd (hKU hz) (infty_notMem_UV V')
  | coe y => exact coe_mem_UV V y

end Transfer

/-! ### Stalks of direct images along the collapse -/

section CollapseStalks

variable {S : TopCat.{0}} [T2Space S] (V : Opens S)

/-- The image in `V⁺` of an open subset of `S` contained in `V`. -/
private noncomputable def imOpen (N : Opens S) : Opens (XV V) :=
  ⟨((↑) : V → OnePoint V) '' (Subtype.val ⁻¹' (N : Set S)),
    OnePoint.isOpenEmbedding_coe.isOpenMap _ (N.2.preimage continuous_subtype_val)⟩

private lemma preimage_imOpen {N : Opens S} (hN : N ≤ V) :
    (Opens.map (κV V)).obj (imOpen V N) = N := by
  apply Opens.ext
  change κf V ⁻¹' (((↑) : V → OnePoint V) '' (Subtype.val ⁻¹' (N : Set S))) = (N : Set S)
  rw [κf_preimage_some_image]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨⟨x, hN hx⟩, hx, rfl⟩

private lemma mem_imOpen {N : Opens S} {x : S} (hx : x ∈ N) (hxV : x ∈ V) :
    κV V x ∈ imOpen V N := by
  rw [κV_apply, κf_of_mem V hxV]
  exact ⟨⟨x, hxV⟩, hx, rfl⟩

private lemma imOpen_le {N : Opens S} {W : Opens (XV V)} (h : N ≤ (Opens.map (κV V)).obj W) :
    imOpen V N ≤ W := by
  rintro _ ⟨y, hy, rfl⟩
  have := h hy
  change κf V y ∈ W at this
  rwa [κf_of_mem V y.2] at this

variable {V}

set_option backward.isDefEq.respectTransparency false in
private lemma bijective_stalkPushforward_κV (G : TopCat.Sheaf (ModuleCat.{0} ℚ) S) {x : S}
    (hx : x ∈ V) : Function.Bijective (G.presheaf.stalkPushforward _ (κV V) x) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun c hc => ?_, fun c => ?_⟩
  · obtain ⟨W, hxW, s, rfl⟩ :=
      ((TopCat.Sheaf.pushforward _ (κV V)).obj G).presheaf.exists_germ_eq c
    erw [TopCat.Presheaf.stalkPushforward_germ_apply] at hc
    obtain ⟨N, hxN, hNW, hsN⟩ := (germ_eq_zero_iff _ x hxW s).mp hc
    refine (germ_eq_zero_iff _ _ hxW s).mpr ⟨imOpen V (N ⊓ V),
      mem_imOpen V (Opens.mem_inf.2 ⟨hxN, hx⟩) hx,
      imOpen_le V (inf_le_left.trans hNW), ?_⟩
    change G.obj.map (homOfLE _).op s = 0
    have e := preimage_imOpen V (N := N ⊓ V) inf_le_right
    have : G.obj.map (homOfLE (show (Opens.map (κV V)).obj (imOpen V (N ⊓ V)) ≤
        (Opens.map (κV V)).obj W from e.le.trans (inf_le_left.trans hNW))).op s =
        G.obj.map (homOfLE (show (Opens.map (κV V)).obj (imOpen V (N ⊓ V)) ≤ N from
          e.le.trans inf_le_left)).op (G.obj.map (homOfLE hNW).op s) := by
      rw [← ConcreteCategory.comp_apply, ← G.obj.map_comp]; rfl
    refine this.trans ?_
    erw [hsN]
    exact map_zero _
  · obtain ⟨N, hxN, s, rfl⟩ := G.presheaf.exists_germ_eq c
    let N' := N ⊓ V
    have hN' : (Opens.map (κV V)).obj (imOpen V N') ≤ N :=
      (preimage_imOpen V (N := N') inf_le_right).le.trans inf_le_left
    refine ⟨((TopCat.Sheaf.pushforward _ (κV V)).obj G).presheaf.germ (imOpen V N') (κV V x)
      (mem_imOpen V (Opens.mem_inf.2 ⟨hxN, hx⟩) hx) (G.obj.map (homOfLE hN').op s), ?_⟩
    erw [TopCat.Presheaf.stalkPushforward_germ_apply]
    exact G.presheaf.germ_res_apply (homOfLE hN') x _ s

private lemma isIso_stalkPushforward_κV (G : TopCat.Sheaf (ModuleCat.{0} ℚ) S) {x : S}
    (hx : x ∈ V) : IsIso (G.presheaf.stalkPushforward _ (κV V) x) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (bijective_stalkPushforward_κV G hx)

end CollapseStalks

/-! ### Germs of constant sheaves -/

section ConstantSheafGerms

/-- The constant sheaf with value `E`. -/
private noncomputable abbrev cSh (V : TopCat.{0}) (E : ModuleCat.{0} ℚ) :
    TopCat.Sheaf (ModuleCat.{0} ℚ) V :=
  (constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E

variable {V : TopCat.{0}} (E : ModuleCat.{0} ℚ)

/-- The constant section `e` of the constant sheaf with value `E`. -/
private noncomputable def constSection (e : E) : ((cSh V E).obj.obj (op ⊤) : Type) :=
  ((CategoryTheory.toSheafify (Opens.grothendieckTopology V)
    ((Functor.const (Opens V)ᵒᵖ).obj E)).app (op ⊤)).hom e

private theorem constantSheaf_exists_constSection_germ (p : V)
    (c : ToType ((cSh V E).presheaf.stalk p)) :
    ∃ e : E, (cSh V E).presheaf.germ ⊤ p (Opens.mem_top p) (constSection E e) = c := by
  let K : TopCat.Presheaf (ModuleCat.{0} ℚ) V := (Functor.const (Opens V)ᵒᵖ).obj E
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso p (ModuleCat.{0} ℚ) K
  obtain ⟨c', hc'⟩ := (ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) p).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology V) K))).2 c
  obtain ⟨U, hU, e, rfl⟩ := K.exists_germ_eq c'
  refine ⟨e, ?_⟩
  have this : K.germ U p hU e = K.germ ⊤ p (Opens.mem_top p) e :=
    TopCat.Presheaf.germ_res_apply K (homOfLE (le_top : U ≤ ⊤)) p hU e
  rw [← hc', this]
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply (F := K) ⊤ p (Opens.mem_top p)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology V) K) e).symm

private theorem eq_zero_of_germ_constSection {e : E} (p : V)
    (h : (cSh V E).presheaf.germ ⊤ p (Opens.mem_top p) (constSection E e) = 0) : e = 0 := by
  let K : TopCat.Presheaf (ModuleCat.{0} ℚ) V := (Functor.const (Opens V)ᵒᵖ).obj E
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso p (ModuleCat.{0} ℚ) K
  have e1 := TopCat.Presheaf.stalkFunctor_map_germ_apply (F := K) ⊤ p (Opens.mem_top p)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology V) K) e
  have h2 : K.germ ⊤ p (Opens.mem_top p) e = K.germ ⊤ p (Opens.mem_top p) 0 := by
    apply (ConcreteCategory.bijective_of_isIso ((TopCat.Presheaf.stalkFunctor
      (ModuleCat.{0} ℚ) p).map (CategoryTheory.toSheafify (Opens.grothendieckTopology V) K))).1
    refine e1.trans (h.trans ?_)
    exact ((congrArg _ (map_zero _)).trans (map_zero _)).symm
  obtain ⟨W, -, i₁, i₂, he⟩ := K.germ_eq p (Opens.mem_top p) (Opens.mem_top p) e 0 h2
  exact he

/-- The germ at `y` of the constant section with value `e`. -/
private noncomputable def constGerm (y : V) : E →ₗ[ℚ] ToType ((cSh V E).presheaf.stalk y) :=
  ((cSh V E).presheaf.germ ⊤ y (Opens.mem_top y)).hom ∘ₗ
    ((CategoryTheory.toSheafify (Opens.grothendieckTopology V)
      ((Functor.const (Opens V)ᵒᵖ).obj E)).app (op ⊤)).hom

private theorem constGerm_apply (y : V) (e : E) :
    constGerm E y e = (cSh V E).presheaf.germ ⊤ y (Opens.mem_top y) (constSection E e) := rfl

private theorem constGerm_bijective (y : V) : Function.Bijective (constGerm E y) := by
  refine ⟨?_, constantSheaf_exists_constSection_germ E y⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  exact fun e he => eq_zero_of_germ_constSection E y he

/-- The canonical morphism `ℚ_Z ⟶ f_* ℚ_{Z'}` carries constant sections to constant sections. -/
private lemma constUnit_constSection {Z Z' : TopCat.{0}} (f : Z' ⟶ Z) (e : ℚ) :
    (MMP.Analytic.constUnit f).hom.app (op ⊤) (constSection (V := Z) (ModuleCat.of ℚ ℚ) e) =
      constSection (V := Z') (ModuleCat.of ℚ ℚ) e := by
  have h := (Adjunction.homEquiv_unit _ _ _ _).symm.trans (MMP.Analytic.homEquiv_constUnit f)
  have h2 := ConcreteCategory.congr_hom h e
  rwa [ModuleCat.comp_apply] at h2

end ConstantSheafGerms

/-! ### Extension by zero after direct image along the collapse -/

section CollapseExact

variable {S : TopCat.{0}} [T2Space S] [LocallyCompactSpace S] (V : Opens S)

attribute [local instance] t2Space_XV

private lemma additive_pushF {Y Z : TopCat.{0}} (f : Y ⟶ Z) :
    (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).Additive :=
  ⟨fun {_ _ _ _} => by apply Sheaf.hom_ext; rfl⟩

attribute [local instance] additive_pushF

/-- The stalk of a direct image `f_* A` at `f y` maps to the stalk of `A` at `y`, naturally. -/
private lemma stalkPushforward_naturality {Y X : TopCat.{0}} (f : Y ⟶ X)
    {A B : TopCat.Presheaf (ModuleCat.{0} ℚ) Y} (φ : A ⟶ B) (y : Y) :
    (TopCat.Presheaf.stalkFunctor _ (f y)).map ((TopCat.Presheaf.pushforward _ f).map φ) ≫
        B.stalkPushforward _ f y =
      A.stalkPushforward _ f y ≫ (TopCat.Presheaf.stalkFunctor _ y).map φ := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun W hW => ?_
  ext s
  have e1 := TopCat.Presheaf.stalkPushforward_germ_apply _ f A W y hW s
  have e2 := TopCat.Presheaf.stalkPushforward_germ_apply _ f B W y hW (φ.app _ s)
  have e3 := TopCat.Presheaf.stalkFunctor_map_germ_apply W (f y) hW
    ((TopCat.Presheaf.pushforward _ f).map φ) s
  have e4 := TopCat.Presheaf.stalkFunctor_map_germ_apply ((Opens.map f).obj W) y hW φ s
  exact (congrArg (B.stalkPushforward _ f y) e3).trans (e2.trans (e4.symm.trans (congrArg
      ((TopCat.Presheaf.stalkFunctor _ y).map φ) e1.symm)))

variable {V} in
/-- At a point of `V`, the stalk of a direct image along the collapse is the stalk. -/
private noncomputable def pushStalkIsoκ {x : S} (hx : x ∈ V) :
    TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (κV V) ⋙ st (κV V x) ≅ st x :=
  NatIso.ofComponents (fun G =>
      @asIso _ _ _ _ (G.presheaf.stalkPushforward _ (κV V) x) (isIso_stalkPushforward_κV G hx))
    (fun φ => stalkPushforward_naturality (κV V) φ.hom x)

/-- `j_! j^* κ_*`, from sheaves on `S` to sheaves on `V⁺`. -/
private noncomputable abbrev ΦV :
    TopCat.Sheaf (ModuleCat.{0} ℚ) S ⥤ TopCat.Sheaf (ModuleCat.{0} ℚ) (XV V) :=
  TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (κV V) ⋙ PF (UV V)

private lemma extHyp_UV : ExtHyp (UV V) := extHyp (UV V)

private lemma additive_ΦV : (ΦV V).Additive := by
  haveI := additive_pushF (κV V)
  haveI := additive_resF (UV V)
  haveI := additive_extF (UV V)
  exact inferInstanceAs (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (κV V) ⋙
    (resF (UV V) ⋙ extF (UV V))).Additive

attribute [local instance] additive_ΦV

private lemma stalk_ΦV (z : XV V) :
    (∀ G, IsZero ((st z).obj ((ΦV V).obj G))) ∨ ∃ y : S, Nonempty (ΦV V ⋙ st z ≅ st y) := by
  induction z using OnePoint.rec with
  | infty => exact Or.inl fun G => (extHyp_UV V).zero _ _ (infty_notMem_UV V)
  | coe y =>
    refine Or.inr ⟨y, ⟨?_⟩⟩
    have hz : κV V (y : S) = ((y : OnePoint V) : XV V) := by
      rw [κV_apply, κf_of_mem V y.2]
    have e1 : PF (UV V) ⋙ st ((y : OnePoint V) : XV V) ≅ 𝟭 _ ⋙ st ((y : OnePoint V) : XV V) :=
      stalkIsoOfIsIso (adjF (UV V)).counit _ fun G =>
        isIso_stalk_counit (extHyp_UV V) G ⟨(y : OnePoint V), coe_mem_UV V y⟩
    have e2 : TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (κV V) ⋙ st ((y : OnePoint V) : XV V) ≅
        st (y : S) := by
      rw [← hz]
      exact pushStalkIsoκ y.2
    exact Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e1 ≪≫ e2

private lemma exact_ΦV : PreservesFiniteLimits (ΦV V) ∧ PreservesFiniteColimits (ΦV V) :=
  preservesHomology_of_stalk _ (stalk_ΦV V)

set_option backward.isDefEq.respectTransparency false in
/-- At a point of `V`, the canonical morphism `ℚ_{V⁺} ⟶ κ_* ℚ_S` is invertible on stalks. -/
private lemma bijective_stalk_constUnit {x : S} (hx : x ∈ V) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor _ (κV V x)).map
      (MMP.Analytic.constUnit (κV V)).hom) := by
  let f := MMP.Analytic.constUnit (κV V)
  let p := (cSh S (ModuleCat.of ℚ ℚ)).presheaf.stalkPushforward _ (κV V) x
  have hp := bijective_stalkPushforward_κV (cSh S (ModuleCat.of ℚ ℚ)) hx
  have key : ∀ e : ℚ, p ((TopCat.Presheaf.stalkFunctor _ (κV V x)).map f.hom
      (constGerm (V := XV V) (ModuleCat.of ℚ ℚ) (κV V x) e)) =
        constGerm (V := S) (ModuleCat.of ℚ ℚ) x e := by
    intro e
    rw [constGerm_apply, ← germ_map, constUnit_constSection]
    exact TopCat.Presheaf.stalkPushforward_germ_apply _ (κV V) _ ⊤ x (Opens.mem_top _) _
  have hcomp : p ∘ (TopCat.Presheaf.stalkFunctor _ (κV V x)).map f.hom =
      constGerm (V := S) (ModuleCat.of ℚ ℚ) x ∘
        (LinearEquiv.ofBijective _ (constGerm_bijective (V := XV V) (ModuleCat.of ℚ ℚ)
          (κV V x))).symm := by
    funext c
    obtain ⟨e, rfl⟩ := (constGerm_bijective (V := XV V) (ModuleCat.of ℚ ℚ) (κV V x)).2 c
    simp only [Function.comp_apply]
    rw [key]
    congr 1
    exact ((LinearEquiv.ofBijective _ (constGerm_bijective (V := XV V) (ModuleCat.of ℚ ℚ)
      (κV V x))).symm_apply_apply e).symm
  have hb : Function.Bijective (p ∘ (TopCat.Presheaf.stalkFunctor _ (κV V x)).map f.hom) := by
    rw [hcomp]
    exact (constGerm_bijective (V := S) _ x).comp (LinearEquiv.bijective _)
  exact (Function.Bijective.of_comp_iff' hp _).1 hb

set_option backward.isDefEq.respectTransparency false in
/-- `j_! j^*` of the canonical morphism `ℚ_{V⁺} ⟶ κ_* ℚ_S` is invertible. -/
private lemma isIso_PF_constUnit :
    IsIso ((PF (UV V)).map (MMP.Analytic.constUnit (κV V))) := by
  let f := MMP.Analytic.constUnit (κV V)
  suffices h : ∀ z, IsIso ((TopCat.Presheaf.stalkFunctor _ z).map ((PF (UV V)).map f).hom) from
    @TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  intro z
  induction z using OnePoint.rec with
  | infty =>
    exact isIso_of_source_target_iso_zero _
      ((extHyp_UV V).zero _ _ (infty_notMem_UV V)).isoZero
      ((extHyp_UV V).zero _ _ (infty_notMem_UV V)).isoZero
  | coe y =>
    have hz : κV V (y : S) = ((y : OnePoint V) : XV V) := by
      rw [κV_apply, κf_of_mem V y.2]
    let z' : (Opens.toTopCat (XV V)).obj (UV V) := ⟨(y : OnePoint V), coe_mem_UV V y⟩
    have h1 := isIso_stalk_counit (extHyp_UV V) (cSh (XV V) (ModuleCat.of ℚ ℚ)) z'
    have h2 := isIso_stalk_counit (extHyp_UV V)
      ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (κV V)).obj (cSh S (ModuleCat.of ℚ ℚ))) z'
    have h3 : IsIso ((TopCat.Presheaf.stalkFunctor _ ((y : OnePoint V) : XV V)).map f.hom) := by
      rw [← hz]
      exact (ConcreteCategory.isIso_iff_bijective _).2 (bijective_stalk_constUnit V y.2)
    have hnat := (adjF (UV V)).counit.naturality f
    have hst : (st ((y : OnePoint V) : XV V)).map ((PF (UV V)).map f) ≫
        (st ((y : OnePoint V) : XV V)).map ((adjF (UV V)).counit.app
          ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (κV V)).obj (cSh S (ModuleCat.of ℚ ℚ)))) =
        (st ((y : OnePoint V) : XV V)).map
          ((adjF (UV V)).counit.app (cSh (XV V) (ModuleCat.of ℚ ℚ))) ≫
          (st ((y : OnePoint V) : XV V)).map f :=
      ((st _).map_comp _ _).symm.trans
        ((congrArg (st _).map hnat).trans ((st _).map_comp _ _))
    have hcomp : IsIso ((st ((y : OnePoint V) : XV V)).map ((PF (UV V)).map f) ≫
        (st ((y : OnePoint V) : XV V)).map ((adjF (UV V)).counit.app
          ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (κV V)).obj
            (cSh S (ModuleCat.of ℚ ℚ))))) := by
      rw [hst]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h3
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h2 hcomp

end CollapseExact

/-! ### Degree zero, and sections of constant sheaves on connected spaces -/

section DegreeZero

/-- A map of `ℕ`-indexed cochain complexes of `ℚ`-vector spaces which is bijective on degree `0`
cocycles is bijective on `H^0`. -/
private lemma bijective_homologyMap_zero {K L : CochainComplex (ModuleCat.{0} ℚ) ℕ} (φ : K ⟶ L)
    (hinj : ∀ x, K.d 0 1 x = 0 → φ.f 0 x = 0 → x = 0)
    (hsurj : ∀ y, L.d 0 1 y = 0 → ∃ x, K.d 0 1 x = 0 ∧ φ.f 0 x = y) :
    Function.Bijective (HomologicalComplex.homologyMap φ 0) := by
  have hc : Function.Bijective (HomologicalComplex.cyclesMap φ 0) := by
    have hiK : Function.Injective (K.iCycles 0) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    have hiL : Function.Injective (L.iCycles 0) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    have hcomm : ∀ z, L.iCycles 0 (HomologicalComplex.cyclesMap φ 0 z) = φ.f 0 (K.iCycles 0 z) :=
      fun z => by rw [← ModuleCat.comp_apply, HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply]
    have hd : ∀ z, K.d 0 1 (K.iCycles 0 z) = 0 := fun z => by
      rw [← ModuleCat.comp_apply, HomologicalComplex.iCycles_d]; rfl
    refine ⟨(injective_iff_map_eq_zero _).2 fun z hz => hiK ?_, fun z' => ?_⟩
    · rw [map_zero]
      refine hinj _ (hd z) ?_
      rw [← hcomm, hz, map_zero]
    · have hd' : L.d 0 1 (L.iCycles 0 z') = 0 := by
        rw [← ModuleCat.comp_apply, HomologicalComplex.iCycles_d]; rfl
      obtain ⟨x, hx, hφx⟩ := hsurj _ hd'
      let f : ModuleCat.of ℚ ℚ ⟶ K.X 0 := ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ x)
      have hf : f ≫ K.d 0 1 = 0 := by
        ext; simp [f, hx]
      refine ⟨K.liftCycles f 1 (by simp) hf (1 : ℚ), hiL ?_⟩
      rw [hcomm, ← ModuleCat.comp_apply (K.liftCycles f 1 _ hf), HomologicalComplex.liftCycles_i]
      simpa [f] using hφx
  have e := HomologicalComplex.homologyπ_naturality φ 0
  have hπK : IsIso (K.homologyπ 0) := (CochainComplex.isoHomologyπ₀ K).isIso_hom
  have hπL : IsIso (L.homologyπ 0) := (CochainComplex.isoHomologyπ₀ L).isIso_hom
  have : HomologicalComplex.homologyMap φ 0 =
      inv (K.homologyπ 0) ≫ HomologicalComplex.cyclesMap φ 0 ≫ L.homologyπ 0 := by
    rw [← e, IsIso.inv_hom_id_assoc]
  have hb1 := ConcreteCategory.bijective_of_isIso (inv (K.homologyπ 0))
  have hb3 := ConcreteCategory.bijective_of_isIso (L.homologyπ 0)
  rw [this]
  have hcomp := hb3.comp (hc.comp hb1)
  convert hcomp using 1
  funext x
  rfl

end DegreeZero

section ConnectedConstant

variable {X : TopCat.{0}} (E : ModuleCat.{0} ℚ)

set_option backward.isDefEq.respectTransparency false in
/-- On a connected space, a global section of a constant sheaf with one vanishing germ is zero. -/
private lemma eq_zero_of_germ_eq_zero_of_connected [ConnectedSpace X]
    (s : (cSh X E).obj.obj (op ⊤)) (p : X)
    (hp : (cSh X E).presheaf.germ ⊤ p (Opens.mem_top p) s = 0) : s = 0 := by
  let Z : Set X := {x | (cSh X E).presheaf.germ ⊤ x (Opens.mem_top x) s = 0}
  have hZo : IsOpen Z := by
    refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
    obtain ⟨N, hxN, hN, hsN⟩ := (germ_eq_zero_iff _ x _ s).mp hx
    refine ⟨N, fun x' hx' => ?_, N.2, hxN⟩
    change _ = 0
    rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hN) x' hx', hsN, map_zero]
  have hZc : IsClosed Z := by
    refine isOpen_compl_iff.mp (isOpen_iff_forall_mem_open.mpr fun x hx => ?_)
    obtain ⟨e, he⟩ := constantSheaf_exists_constSection_germ E x
      ((cSh X E).presheaf.germ ⊤ x (Opens.mem_top x) s)
    obtain ⟨N, hxN, i₁, i₂, hN⟩ := TopCat.Presheaf.germ_eq _ x (Opens.mem_top x) (Opens.mem_top x)
      s (constSection E e) he.symm
    refine ⟨N, fun x' hx' hx'Z => hx ?_, N.2, hxN⟩
    have h1 : (cSh X E).presheaf.germ ⊤ x' (Opens.mem_top x') (constSection E e) = 0 := by
      rw [← TopCat.Presheaf.germ_res_apply _ i₂ x' hx', ← hN, TopCat.Presheaf.germ_res_apply]
      exact hx'Z
    have he0 : e = 0 := eq_zero_of_germ_constSection E x' h1
    change _ = 0
    rw [← he, he0]
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  have hZ : Z = Set.univ := (isClopen_iff.mp ⟨hZc, hZo⟩).resolve_left
    (Set.nonempty_iff_ne_empty.mp ⟨p, hp⟩)
  exact eq_zero_of_germ _ s fun x _ => (hZ.symm ▸ Set.mem_univ x : x ∈ Z)

end ConnectedConstant

/-! ### Universal coefficients over `ℚ` for singular cochains -/

section RationalUCT

open MMP MMP.SingularChain MMP.SingularCochain Finsupp

variable {Y : Type} [TopologicalSpace Y]

/-- **Detection of relative cohomology by relative cycles over `ℚ`**: a relative `(m + 1)`-cocycle
of `(Y, A)` vanishing on every relative cycle is a relative coboundary. -/
private lemma mem_relCoboundaries_of_eval_eq_zero_rat (A : Set Y) (m : ℕ)
    {ψ : Simplex Y (m + 1) → ℚ} (hψA : ψ ∈ vanishing ℚ (m + 1) A)
    (hψ : ∀ c : Chain ℚ Y (m + 1), bd ℚ m c ∈ inside ℚ m A → eval ψ c = 0) :
    ψ ∈ relCoboundaries ℚ A (m + 1) := by
  let P : ℕ → Type := fun k ↦ Chain ℚ Y k ⧸ inside ℚ k A
  let d : P (m + 1) →ₗ[ℚ] P m := relBd A m
  have hmk0 : ∀ {k} {x : Chain ℚ Y k}, (Submodule.Quotient.mk x : P k) = 0 ↔ x ∈ inside ℚ k A :=
    fun {_ _} ↦ Submodule.Quotient.mk_eq_zero _
  let ψbar : P (m + 1) →ₗ[ℚ] ℚ := (inside ℚ (m + 1) A).liftQ (eval ψ) fun c hc ↦ by
    rw [LinearMap.mem_ker]
    exact eval_eq_zero_of_mem_vanishing hψA hc
  have hψker : LinearMap.ker d ≤ LinearMap.ker ψbar := fun x hx ↦ by
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact hψ c (hmk0.1 hx)
  let lam : LinearMap.range d →ₗ[ℚ] ℚ :=
    ((LinearMap.ker d).liftQ ψbar hψker) ∘ₗ d.quotKerEquivRange.symm.toLinearMap
  have hlam : ∀ x, lam (d.rangeRestrict x) = ψbar x := fun x ↦ by
    simp only [lam, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show d.rangeRestrict x = d.quotKerEquivRange (Submodule.Quotient.mk x) from rfl,
      LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  obtain ⟨μ, hμ⟩ := LinearMap.exists_extend lam
  let β : Chain ℚ Y m →ₗ[ℚ] ℚ := μ ∘ₗ (inside ℚ m A).mkQ
  refine ⟨fun σ ↦ β (single σ 1), fun σ hσ ↦ ?_, ?_⟩
  · change μ (Submodule.Quotient.mk (single σ 1)) = 0
    rw [hmk0.2 (single_mem_supported ℚ _ hσ), map_zero]
  · have heval : eval (fun σ ↦ β (single σ 1)) = β := by
      ext σ
      simp [SingularCochain.eval]
    funext σ
    have h1 := eval_coboundary m (fun σ ↦ β (single σ 1)) (single σ 1)
    rw [heval] at h1
    simp only [SingularCochain.eval, linearCombination_single, one_smul] at h1
    rw [h1]
    change μ (d (Submodule.Quotient.mk (single σ 1))) = ψ σ
    have h2 : μ (d (Submodule.Quotient.mk (single σ 1))) =
        lam (d.rangeRestrict (Submodule.Quotient.mk (single σ 1))) :=
      LinearMap.congr_fun hμ (d.rangeRestrict (Submodule.Quotient.mk (single σ 1)))
    rw [h2, hlam]
    change eval ψ (single σ 1) = ψ σ
    rw [linearCombination_single, one_smul]

/-- A relative cocycle of `(Y, A)` vanishes on a chain which is a boundary modulo `A`. -/
private lemma eval_eq_zero_of_sub_bd_mem_inside {A : Set Y} {m : ℕ}
    {ψ : Simplex Y (m + 1) → ℚ} (hψ : ψ ∈ relCocycles ℚ A (m + 1)) {c : Chain ℚ Y (m + 1)}
    {w : Chain ℚ Y (m + 2)} (hw : c - bd ℚ (m + 1) w ∈ inside ℚ (m + 1) A) : eval ψ c = 0 := by
  have h := eval_eq_zero_of_mem_vanishing hψ.1 hw
  rw [map_sub, ← eval_coboundary, show coboundary ℚ (m + 1) ψ = 0 from hψ.2] at h
  simpa using h

/-- If every relative `(m + 1)`-cycle of `(Y, A)` is a relative boundary, then
`H^{m+1}(Y, A; ℚ) = 0`. -/
private lemma mem_relCoboundaries_of_relVanishing (A : Set Y) (m : ℕ)
    (hv : ∀ c : Chain ℚ Y (m + 1), bd ℚ m c ∈ inside ℚ m A →
      ∃ w : Chain ℚ Y (m + 2), c - bd ℚ (m + 1) w ∈ inside ℚ (m + 1) A)
    {ψ : Simplex Y (m + 1) → ℚ} (hψ : ψ ∈ relCocycles ℚ A (m + 1)) :
    ψ ∈ relCoboundaries ℚ A (m + 1) :=
  mem_relCoboundaries_of_eval_eq_zero_rat A m hψ.1 fun c hc ↦
    eval_eq_zero_of_sub_bd_mem_inside hψ (hv c hc).choose_spec

/-- **Vanishing cohomology of a subset**: if `H_{m+1}(A; ℚ) = 0`, a cochain whose coboundary
vanishes on the simplices of `A` agrees on the simplices of `A` with a coboundary. -/
private lemma exists_coboundary_eq_on (A : Set Y) (m : ℕ) (hA : CycleVanishing ℚ Y m A)
    (ψ : Simplex Y (m + 1) → ℚ) (hψ : coboundary ℚ (m + 1) ψ ∈ vanishing ℚ (m + 2) A) :
    ∃ β : Simplex Y m → ℚ, ∀ σ : Simplex Y (m + 1), Set.range σ ⊆ A →
      ψ σ = coboundary ℚ m β σ := by
  -- `ψ` restricted to chains in `A` vanishes on cycles, so factors through boundaries
  let I : Submodule ℚ (Chain ℚ Y (m + 1)) := inside ℚ (m + 1) A
  let I' : Submodule ℚ (Chain ℚ Y m) := inside ℚ m A
  let dI : I →ₗ[ℚ] I' := (bd ℚ m).restrict fun c hc ↦ bd_mem_inside hc
  let ψI : I →ₗ[ℚ] ℚ := (eval ψ).comp I.subtype
  have hker : LinearMap.ker dI ≤ LinearMap.ker ψI := by
    intro c hc
    have hc0 : bd ℚ m c.1 = 0 := congrArg Subtype.val hc
    obtain ⟨w, hw, hbw⟩ := hA c.1 c.2 hc0
    change eval ψ c.1 = 0
    rw [← hbw, ← eval_coboundary]
    exact eval_eq_zero_of_mem_vanishing hψ hw
  let lam : LinearMap.range dI →ₗ[ℚ] ℚ :=
    ((LinearMap.ker dI).liftQ ψI hker) ∘ₗ dI.quotKerEquivRange.symm.toLinearMap
  have hlam : ∀ x, lam (dI.rangeRestrict x) = ψI x := fun x ↦ by
    simp only [lam, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show dI.rangeRestrict x = dI.quotKerEquivRange (Submodule.Quotient.mk x) from rfl,
      LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  obtain ⟨μ, hμ⟩ := LinearMap.exists_extend lam
  obtain ⟨ν, hν⟩ := LinearMap.exists_extend μ
  refine ⟨fun τ ↦ ν (single τ 1), fun σ hσ ↦ ?_⟩
  have hσI : single σ (1 : ℚ) ∈ I := single_mem_supported ℚ _ hσ
  have heval : eval (fun τ ↦ ν (single τ 1)) = ν := by
    ext τ
    simp [SingularCochain.eval]
  have h1 := eval_coboundary m (fun τ ↦ ν (single τ 1)) (single σ 1)
  rw [heval] at h1
  simp only [SingularCochain.eval, linearCombination_single, one_smul] at h1
  rw [h1]
  have h2 : ν (bd ℚ m (single σ 1)) = μ ⟨bd ℚ m (single σ 1), bd_mem_inside hσI⟩ :=
    LinearMap.congr_fun hν ⟨_, bd_mem_inside hσI⟩
  have h3 : μ ⟨bd ℚ m (single σ 1), bd_mem_inside hσI⟩ = lam (dI.rangeRestrict ⟨_, hσI⟩) :=
    LinearMap.congr_fun hμ (dI.rangeRestrict ⟨_, hσI⟩)
  rw [h2, h3, hlam]
  change ψ σ = eval ψ (single σ 1)
  rw [linearCombination_single, one_smul]

end RationalUCT

/-! ### Cohomology of a space whose point complement is acyclic -/

section PointComplement

open MMP MMP.SingularChain MMP.SingularCochain Finsupp

variable {Y : Type} [TopologicalSpace Y] (y : Y)

private lemma vanishing_compl_univ' (n : ℕ) (φ : Simplex Y n → ℚ) :
    φ ∈ vanishing ℚ n (Set.univᶜ : Set Y) := fun σ hσ ↦
  absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp)

private lemma mem_relCoboundaries_compl_univ {n : ℕ} (β : Simplex Y n → ℚ) :
    coboundary ℚ n β ∈ relCoboundaries ℚ (Set.univᶜ : Set Y) (n + 1) :=
  ⟨β, vanishing_compl_univ' n β, rfl⟩

variable (hCV : ∀ m, CycleVanishing ℚ Y m ({y}ᶜ : Set Y))

include hCV

/-- An absolute cocycle in a degree where the local homology at `y` vanishes is a coboundary. -/
private lemma mem_relCoboundaries_of_point (m : ℕ) (hRV : RelVanishing ℚ Y m {y})
    {φ : Simplex Y (m + 1) → ℚ} (hφ : coboundary ℚ (m + 1) φ = 0) :
    φ ∈ relCoboundaries ℚ (Set.univᶜ : Set Y) (m + 1) := by
  obtain ⟨β, hβ⟩ := exists_coboundary_eq_on ({y}ᶜ : Set Y) m (hCV m) φ
    (by rw [hφ]; exact zero_mem _)
  have hφ' : φ - coboundary ℚ m β ∈ relCocycles ℚ ({y}ᶜ : Set Y) (m + 1) :=
    ⟨fun σ hσ ↦ by simp [hβ σ hσ], by
      show coboundary ℚ (m + 1) (φ - coboundary ℚ m β) = 0
      rw [map_sub, hφ, coboundary_coboundary, sub_zero]⟩
  obtain ⟨γ, -, hγ⟩ := mem_relCoboundaries_of_relVanishing ({y}ᶜ : Set Y) m
    (fun c hc ↦ hRV c (by simpa using hc)) hφ'
  have : φ = coboundary ℚ m (β + γ) := by
    rw [map_add, hγ, add_sub_cancel]
  rw [this]
  exact mem_relCoboundaries_compl_univ _

/-- An absolute `2`-cocycle differs from a relative cocycle of `(Y, Y - y)` by a coboundary. -/
private lemma exists_sub_mem_relCocycles {φ : Simplex Y 2 → ℚ} (hφ : coboundary ℚ 2 φ = 0) :
    ∃ β : Simplex Y 1 → ℚ, φ - coboundary ℚ 1 β ∈ relCocycles ℚ ({y}ᶜ : Set Y) 2 := by
  obtain ⟨β, hβ⟩ := exists_coboundary_eq_on ({y}ᶜ : Set Y) 1 (hCV 1) φ
    (by rw [hφ]; exact zero_mem _)
  exact ⟨β, fun σ hσ ↦ by simp [hβ σ hσ], by
    show coboundary ℚ 2 (φ - coboundary ℚ 1 β) = 0
    rw [map_sub, hφ, coboundary_coboundary, sub_zero]⟩

/-- A relative cocycle of `(Y, Y - y)` which is an absolute coboundary is a relative
coboundary. -/
private lemma mem_relCoboundaries_of_compl_univ {α : Simplex Y 2 → ℚ}
    (hα : α ∈ relCocycles ℚ ({y}ᶜ : Set Y) 2)
    (h : α ∈ relCoboundaries ℚ (Set.univᶜ : Set Y) 2) :
    α ∈ relCoboundaries ℚ ({y}ᶜ : Set Y) 2 := by
  obtain ⟨ψ, -, rfl⟩ := h
  obtain ⟨χ, hχ⟩ := exists_coboundary_eq_on ({y}ᶜ : Set Y) 0 (hCV 0) ψ hα.1
  refine ⟨ψ - coboundary ℚ 0 χ, fun σ hσ ↦ by simp [hχ σ hσ], ?_⟩
  rw [map_sub, coboundary_coboundary, sub_zero]

end PointComplement

/-! ### Charts of `V⁺` from charts of `S` -/

section Charts

variable {S : TopCat.{0}} [T2Space S] (V : Opens S) [Nonempty V]

/-- An inverse of the collapse on `V`. -/
private noncomputable def κInv : OnePoint V → S :=
  fun z => Option.elim z (Classical.arbitrary V).1 Subtype.val

/-- The collapse `S → V⁺` as a partial homeomorphism from `V` onto its image. -/
private noncomputable def κP : OpenPartialHomeomorph S (OnePoint V) where
  toFun := κf V
  invFun := κInv V
  source := V
  target := Set.range ((↑) : V → OnePoint V)
  map_source' x hx := by rw [κf_of_mem V hx]; exact ⟨_, rfl⟩
  map_target' := by rintro _ ⟨y, rfl⟩; exact y.2
  left_inv' x hx := by rw [κf_of_mem V hx]; rfl
  right_inv' := by rintro _ ⟨y, rfl⟩; exact κf_of_mem V y.2
  open_source := V.2
  open_target := OnePoint.isOpen_range_coe
  continuousOn_toFun := (continuous_κf V).continuousOn
  continuousOn_invFun := by
    rintro _ ⟨y, rfl⟩
    exact (OnePoint.continuousAt_coe.2 continuous_subtype_val.continuousAt).continuousWithinAt

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The chart of `V⁺` induced by a chart `e` of `S`. -/
private noncomputable def eX (e : OpenPartialHomeomorph S H) : OpenPartialHomeomorph (XV V) H :=
  (κP V).symm.trans e

private lemma eX_symm_apply (e : OpenPartialHomeomorph S H) (a : H) :
    (eX V e).symm a = κf V (e.symm a) := rfl

private lemma eX_target (e : OpenPartialHomeomorph S H) :
    (eX V e).target = e.target ∩ e.symm ⁻¹' (V : Set S) := by
  simp [eX, OpenPartialHomeomorph.trans_target, κP]

private lemma mem_eX_source {e : OpenPartialHomeomorph S H} {x : S} (hx : x ∈ e.source)
    (hxV : x ∈ V) : κV V x ∈ (eX V e).source := by
  rw [κV_apply, κf_of_mem V hxV]
  simp only [eX, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Set.mem_inter_iff, Set.mem_preimage]
  exact ⟨⟨_, rfl⟩, hx⟩

private lemma eX_κV {e : OpenPartialHomeomorph S H} {x : S} (hxV : x ∈ V) :
    eX V e (κV V x) = e x := by
  rw [κV_apply, κf_of_mem V hxV]
  rfl

end Charts

/-! ### `V⁺` is a sphere -/

section Sphere

open MMP MMP.SingularChain

variable {S : TopCat.{0}} [T2Space S] (V : Opens S)

/-- The two-sphere. -/
private abbrev Sph : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private lemma fact_finrank_three : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by simp⟩

/-- `V⁺ ≅ S²` for a plane `V`. -/
private noncomputable def sphV (h : V ≃ₜ EuclideanSpace ℝ (Fin 2)) : XV V ≃ₜ Sph :=
  (Homeomorph.onePointCongr h).trans (onePointEquivSphereOfFinrankEq (by simp))

private lemma range_stereographic'_symm (v : Sph) :
    haveI := fact_finrank_three
    Set.range (stereographic' 2 v).symm = {v}ᶜ := by
  haveI := fact_finrank_three
  rw [← Set.image_univ, ← stereographic'_target v,
    OpenPartialHomeomorph.symm_image_target_eq_source,
    stereographic'_source]

private lemma isOpenEmbedding_stereographic'_symm (v : Sph) :
    haveI := fact_finrank_three
    IsOpenEmbedding (stereographic' 2 v).symm := by
  haveI := fact_finrank_three
  exact (stereographic' 2 v).symm.to_isOpenEmbedding (by simp [stereographic'_target])

/-- The complement of a point of `V⁺` has no homology in positive degrees. -/
private lemma cycleVanishing_compl_singleton (h : V ≃ₜ EuclideanSpace ℝ (Fin 2)) (z : XV V)
    (m : ℕ) : CycleVanishing ℚ (XV V) m ({z}ᶜ : Set (XV V)) := by
  haveI := fact_finrank_three
  let f : EuclideanSpace ℝ (Fin 2) → XV V := (sphV V h).symm ∘ (stereographic' 2 (sphV V h z)).symm
  have hf : IsEmbedding f :=
    (sphV V h).symm.isEmbedding.comp (isOpenEmbedding_stereographic'_symm _).isEmbedding
  have hrange : Set.range f = {z}ᶜ := by
    rw [Set.range_comp, range_stereographic'_symm, Set.image_compl_eq (sphV V h).symm.bijective,
      Set.image_singleton, Homeomorph.symm_apply_apply]
  rw [← hrange, ← cycleVanishing_univ_iff_range hf]
  exact cycleVanishing_of_starConvex (starConvex_univ (0 : EuclideanSpace ℝ (Fin 2))) m

private lemma metrizableSpace_XV (h : V ≃ₜ EuclideanSpace ℝ (Fin 2)) : MetrizableSpace (XV V) :=
  (sphV V h).isEmbedding.metrizableSpace

private lemma stronglyLocallyContractibleSpace_of_normedSpace (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : StronglyLocallyContractibleSpace E :=
  StronglyLocallyContractibleSpace.of_bases (fun x => Metric.nhds_basis_ball)
    fun x _ hε => (convex_ball x _).contractibleSpace ⟨x, Metric.mem_ball_self hε⟩

private lemma stronglyLocallyContractibleSpace_sph : StronglyLocallyContractibleSpace Sph := by
  haveI := fact_finrank_three
  refine StronglyLocallyContractibleSpace.of_isOpenEmbedding_cover fun v => ?_
  refine ⟨EuclideanSpace ℝ (Fin 2), inferInstance,
    stronglyLocallyContractibleSpace_of_normedSpace _, (stereographic' 2 (-v)).symm,
    isOpenEmbedding_stereographic'_symm (-v), ?_⟩
  rw [range_stereographic'_symm]
  intro hv
  have h1 : (v : EuclideanSpace ℝ (Fin 3)) = -(v : EuclideanSpace ℝ (Fin 3)) := by
    have := congrArg Subtype.val (Set.mem_singleton_iff.mp hv)
    simpa using this
  have h2 : (v : EuclideanSpace ℝ (Fin 3)) = 0 := by
    have : (2 : ℝ) • (v : EuclideanSpace ℝ (Fin 3)) = 0 := by
      rw [two_smul]; nth_rewrite 2 [h1]; exact add_neg_cancel _
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  have h3 := v.2
  rw [mem_sphere_iff_norm, sub_zero, h2, norm_zero] at h3
  exact zero_ne_one h3

private lemma locallyContractibleSpace_XV (h : V ≃ₜ EuclideanSpace ℝ (Fin 2)) :
    LocallyContractibleSpace (XV V) :=
  haveI := stronglyLocallyContractibleSpace_sph
  haveI := (sphV V h).isOpenEmbedding.stronglyLocallyContractibleSpace
  StronglyLocallyContractibleSpace.locallyContractible

end Sphere

/-! ### Local homology in high degrees -/

section LocalHigh

open MMP MMP.SingularChain Set

variable {Y : Type} [TopologicalSpace Y] [T2Space Y] {H : Type*} [NormedAddCommGroup H]
  [NormedSpace ℝ H] [FiniteDimensional ℝ H]

/-- `H_{k+1}(Y, Y - y; ℚ) = 0` for `k ≥ 2`, at a point of the domain of a chart modelled on a
plane. -/
private lemma relVanishing_singleton_high (b : Module.Basis (Fin 2) ℝ H)
    (e : OpenPartialHomeomorph Y H) {y : Y} (hy : y ∈ e.source) {k : ℕ} (hk : 2 ≤ k) :
    RelVanishing ℚ Y k {y} := by
  have h0 : RelVanishing ℚ (Fin 2 → ℝ) k {0} :=
    relVanishing_of_isCompact_euclidean (fun a c k' hk' =>
      relVanishing_Icc (fun n hn => cycleVanishing_compl_zero n hn) 2 a c k' (hk.trans hk'))
      isCompact_singleton
  have h1 := RelVanishing.of_homeomorph (basisTranslateHomeomorph b (e y)) h0
  rw [image_singleton, basisTranslateHomeomorph_zero] at h1
  refine RelVanishing.of_openPartialHomeomorph e isClosed_singleton (singleton_subset_iff.2 hy) ?_
  rw [image_singleton]
  exact RelVanishing.subtype e.open_target isClosed_singleton
    (singleton_subset_iff.2 (e.map_source hy)) h1

end LocalHigh

/-! ### Local orientation classes on `V⁺` -/

section Orientation

open MMP MMP.SingularChain MMP.SingularCochain
  MMP.ThomClass MMP.FundamentalClass Set Finsupp

/-- Push-forward of local homology along a map injective at the point. -/
private lemma IsLocallyHomologous.map {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) {x : Y} (hf : ∀ y, f y = f x → y = x) {n : ℕ} {σ₁ σ₂ : Simplex Y n}
    (h : IsLocallyHomologous x σ₁ σ₂) : IsLocallyHomologous (f x) (f.comp σ₁) (f.comp σ₂) := by
  obtain ⟨c, d, hd, hcd⟩ := h
  refine ⟨postcomp ℤ f (n + 1) c, postcomp ℤ f n d,
    postcomp_mem_inside f (show MapsTo f ({x}ᶜ : Set Y) ({f x}ᶜ : Set Z) from
      fun y hy hfy => hy (hf y hfy)) hd, ?_⟩
  have := congrArg (postcomp ℤ f n) hcd
  rwa [map_sub, postcomp_single, postcomp_single, map_add, postcomp_bd] at this

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {S : TopCat.{0}} [T2Space S] [LocallyCompactSpace S] [ChartedSpace H S]
  (b : Module.Basis (Fin 2) ℝ H) (V : Opens S) [Nonempty V]

attribute [local instance] t2Space_XV

private lemma κV_eq_iff {x : S} (hx : x ∈ V) (y : S) : κV V y = κV V x → y = x := by
  intro h
  rw [κV_apply, κV_apply, κf_of_mem V hx] at h
  by_cases hy : y ∈ V
  · rw [κf_of_mem V hy, OnePoint.coe_eq_coe] at h
    exact congrArg Subtype.val h
  · rw [κf_of_notMem V hy] at h
    exact absurd h.symm (OnePoint.coe_ne_infty _)

/-- The chart simplex of `V⁺` is the collapse of the chart simplex of `S`. -/
private lemma chartSimplexIn_eX (e : OpenPartialHomeomorph S H) (v : Fin 3 → H)
    (hvt : range (affineSimplex v) ⊆ (eX V e).target) (hvt' : range (affineSimplex v) ⊆ e.target) :
    chartSimplexIn (eX V e) v hvt = (κV V).hom.comp (chartSimplexOf e v hvt') := by
  ext t
  rfl

/-- A relative cocycle of `(V⁺, V⁺ - κ x)` taking the value `1` on a chart simplex around `κ x`
coming from an oriented chart of `S`: a local orientation class at `x`. -/
private def IsCOX (x : S) (α : Simplex (XV V) 2 → ℚ) : Prop :=
  α ∈ relCocycles ℚ ({κV V x}ᶜ : Set (XV V)) 2 ∧
  ∃ (e : OpenPartialHomeomorph S H) (_ : e ∈ atlas H S) (_ : x ∈ e.source) (v : Fin 3 → H)
    (_ : IsOrientedSimplexAroundZero b fun k ↦ v k - e x)
    (hvt : range (affineSimplex v) ⊆ (eX V e).target),
    SingularCochain.eval α (single (chartSimplexIn (eX V e) v hvt) 1) = 1

private lemma eX_target_subset (e : OpenPartialHomeomorph S H) :
    (eX V e).target ⊆ e.target := by
  rw [eX_target]; exact inter_subset_left

/-- Local orientation classes exist. -/
private lemma exists_isCOX {x : S} (hx : x ∈ V) : ∃ α, IsCOX b V x α := by
  set e := chartAt H x
  have hxe : x ∈ e.source := mem_chart_source H x
  have hT : e x ∈ (eX V e).target := by
    rw [eX_target]; exact ⟨e.map_source hxe, by simpa [e.left_inv hxe] using hx⟩
  obtain ⟨v, hv, hvt⟩ := exists_isOrientedSimplexAroundZero_subset b (e x)
    ((eX V e).open_target.mem_nhds hT)
  have hv' : IsOrientedSimplexAroundZero b fun k ↦ v k - (eX V e) (κV V x) := by
    rwa [eX_κV V hx]
  obtain ⟨α, hα, h1⟩ := exists_mem_relCocycles_eval_chartSimplexIn (R := ℚ) b (eX V e)
    (mem_eX_source V hxe hx) hv' hvt
  exact ⟨α, hα, e, chart_mem_atlas H x, hxe, v, hv, hvt, h1⟩

/-- Two local orientation classes at the same point agree in `H^2(V⁺, V⁺ - κ x)`. -/
private lemma sub_mem_relCoboundaries_of_isCOX (hS : IsOrientedAtlas H S) {x : S} (hx : x ∈ V)
    {α α' : Simplex (XV V) 2 → ℚ} (h : IsCOX b V x α) (h' : IsCOX b V x α') :
    α - α' ∈ relCoboundaries ℚ ({κV V x}ᶜ : Set (XV V)) 2 := by
  obtain ⟨hα, e, he, hxe, v, hv, hvt, h1⟩ := h
  obtain ⟨hα', e', he', hxe', v', hv', hvt', h1'⟩ := h'
  have hloc := isLocallyHomologous_chartSimplexOf hS b he he' hxe hxe' hv
    ((hvt.trans (eX_target_subset V e))) hv' ((hvt'.trans (eX_target_subset V e')))
  have hlocX := IsLocallyHomologous.map (κV V).hom (κV_eq_iff V hx) hloc
  rw [← chartSimplexIn_eX V e v hvt, ← chartSimplexIn_eX V e' v' hvt'] at hlocX
  have hval : SingularCochain.eval α' (single (chartSimplexIn (eX V e) v hvt) 1) = 1 :=
    (eval_eq_of_isLocallyHomologous hα' hlocX).trans h1'
  have hv'' : IsOrientedSimplexAroundZero b fun k ↦ v k - (eX V e) (κV V x) := by
    rwa [eX_κV V hx]
  refine mem_relCoboundaries_of_eval_chartSimplexOf b (mem_eX_source V hxe hx) hv'' hvt
    (Submodule.sub_mem _ hα hα') ?_
  have e1 : α (chartSimplexIn (eX V e) v hvt) = 1 := by
    simpa [SingularCochain.eval, linearCombination_single] using h1
  have e2 : α' (chartSimplexIn (eX V e) v hvt) = 1 := by
    simpa [SingularCochain.eval, linearCombination_single] using hval
  change linearCombination ℚ (α - α') (single (chartSimplexIn (eX V e) v hvt) 1) = 0
  rw [linearCombination_single, one_smul, Pi.sub_apply, e1, e2, sub_self]

end Orientation

/-! ### The local orientation classes have the same image in `H^2(V⁺)` -/

section Independence

open MMP MMP.SingularChain MMP.SingularCochain
  MMP.ThomClass MMP.FundamentalClass
  MMP.PoincareDuality
  Set Finsupp Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {S : TopCat.{0}} [T2Space S] [LocallyCompactSpace S] [ChartedSpace H S]
  (b : Module.Basis (Fin 2) ℝ H) (V : Opens S) [Nonempty V]

attribute [local instance] t2Space_XV

/-- **Local constancy of the local orientation class.** -/
private lemma exists_nhds_sub_mem_relCoboundaries (hS : IsOrientedAtlas H S) {x₀ : S}
    (hx₀ : x₀ ∈ V) : ∃ N ∈ 𝓝 x₀, ∀ x₁ ∈ N, ∀ x₂ ∈ N, ∀ α₁ α₂, IsCOX b V x₁ α₁ → IsCOX b V x₂ α₂ →
      α₁ - α₂ ∈ relCoboundaries ℚ (Set.univᶜ : Set (XV V)) 2 := by
  set e := chartAt H x₀
  have he : e ∈ atlas H S := chart_mem_atlas H x₀
  have hx₀e : x₀ ∈ e.source := mem_chart_source H x₀
  set E := eX V e
  have hT : e x₀ ∈ E.target := by
    rw [eX_target]; exact ⟨e.map_source hx₀e, by simpa [e.left_inv hx₀e] using hx₀⟩
  obtain ⟨v, hv, hvt⟩ := exists_isOrientedSimplexAroundZero_subset b (e x₀)
    (E.open_target.mem_nhds hT)
  set ψ := basisHomeomorph b
  have hO : {q : H | IsOrientedSimplexAroundZero b fun k ↦ v k - q} ∩ E.target ∈ 𝓝 (e x₀) :=
    Filter.inter_mem (eventually_isOrientedSimplexAroundZero b hv) (E.open_target.mem_nhds hT)
  have hO' : ψ.symm ⁻¹' ({q : H | IsOrientedSimplexAroundZero b fun k ↦ v k - q} ∩ E.target) ∈
      𝓝 (ψ (e x₀)) := by
    apply ψ.symm.continuous.continuousAt.preimage_mem_nhds
    rwa [ψ.symm_apply_apply]
  obtain ⟨r, hr, hrO⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hO'
  set Q := chartBall b E (ψ (e x₀)) r
  have hB : ∀ u ∈ Metric.closedBall (ψ (e x₀)) r, ψ.symm u ∈ E.target := fun u hu => (hrO hu).2
  -- the simplex `v` is oriented around every point of `Q`
  have hQ : ∀ z ∈ Q, ∃ hz : z ∈ E.source, IsOrientedSimplexAroundZero b fun k ↦ v k - E z := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨E.map_target (hB u hu), ?_⟩
    rw [E.right_inv (hB u hu)]
    exact (hrO hu).1
  -- the neighbourhood of `x₀`
  let N : Set S := e.source ∩ (V : Set S) ∩ (ψ ∘ e) ⁻¹' Metric.ball (ψ (e x₀)) r
  have hN : N ∈ 𝓝 x₀ := by
    refine Filter.inter_mem (Filter.inter_mem (e.open_source.mem_nhds hx₀e) (V.2.mem_nhds hx₀)) ?_
    exact (ψ.continuous.continuousAt.comp (e.continuousAt hx₀e)).preimage_mem_nhds
      (Metric.ball_mem_nhds _ hr)
  have hNQ : ∀ x ∈ N, κV V x ∈ Q := by
    rintro x ⟨⟨hxe, hxV⟩, hxr⟩
    refine ⟨ψ (e x), Metric.ball_subset_closedBall hxr, ?_⟩
    change E.symm (ψ.symm (ψ (e x))) = κV V x
    rw [ψ.symm_apply_apply, eX_symm_apply, e.left_inv hxe]
    rfl
  -- the cocycle of the simplex `v` at a point of `N`
  have hγ : ∀ x ∈ N, ∃ γ, IsCOX b V x γ ∧
      SingularCochain.eval γ (single (chartSimplexIn E v hvt) 1) = 1 := by
    intro x hx
    obtain ⟨hz, hvz⟩ := hQ _ (hNQ x hx)
    obtain ⟨γ, hγ, h1⟩ := exists_mem_relCocycles_eval_chartSimplexIn (R := ℚ) b E hz hvz hvt
    refine ⟨γ, ⟨hγ, e, he, hx.1.1, v, ?_, hvt, h1⟩, h1⟩
    rwa [eX_κV V hx.1.2] at hvz
  refine ⟨N, hN, fun x₁ hx₁ x₂ hx₂ α₁ α₂ h₁ h₂ => ?_⟩
  obtain ⟨γ₁, hγ₁, hγ₁1⟩ := hγ x₁ hx₁
  obtain ⟨γ₂, hγ₂, hγ₂1⟩ := hγ x₂ hx₂
  have k₁ := relCoboundaries_le_relCoboundaries_compl_univ ℚ _ _
    (sub_mem_relCoboundaries_of_isCOX b V hS hx₁.1.2 h₁ hγ₁)
  have k₂ := relCoboundaries_le_relCoboundaries_compl_univ ℚ _ _
    (sub_mem_relCoboundaries_of_isCOX b V hS hx₂.1.2 h₂ hγ₂)
  -- `γ₁` and `γ₂` agree on the relative cycles of `(V⁺, V⁺ - Q)`
  have hQc : ∀ {x}, x ∈ N → ({κV V x}ᶜ : Set (XV V)) ⊇ Qᶜ := fun hx z hz hzx =>
    hz (by rw [Set.mem_singleton_iff.mp hzx]; exact hNQ _ hx)
  have hd : γ₁ - γ₂ ∈ relCoboundaries ℚ (Qᶜ : Set (XV V)) 2 := by
    refine mem_relCoboundaries_of_eval_eq_zero_rat (Qᶜ : Set (XV V)) 1
      (Submodule.sub_mem _ (fun σ hσ => hγ₁.1.1 σ (hσ.trans (hQc hx₁)))
        (fun σ hσ => hγ₂.1.1 σ (hσ.trans (hQc hx₂)))) fun c hc => ?_
    obtain ⟨hz₁, hvz₁⟩ := hQ _ (hNQ x₁ hx₁)
    obtain ⟨r₁, w, hw⟩ := exists_sub_smul_chartSimplexIn_mem (R := ℚ) b E hz₁ hvz₁ hvt c
      (inside_mono 1 (hQc hx₁) hc)
    have hbd : bd ℚ 1 (c - r₁ • single (chartSimplexIn E v hvt) 1) ∈ inside ℚ 1 Qᶜ := by
      rw [map_sub, map_smul]
      exact Submodule.sub_mem _ hc (Submodule.smul_mem _ _
        (bd_single_chartSimplex_mem_inside hvt hQ))
    have hrel₁ : IsRelBoundary ℚ 2 {κV V x₁} (c - r₁ • single (chartSimplexIn E v hvt) 1) :=
      ⟨w, by simpa using hw⟩
    have hrelQ := isRelBoundary_chartBall hB (hNQ x₁ hx₁) hbd hrel₁
    have hrel₂ : IsRelBoundary ℚ 2 {κV V x₂} (c - r₁ • single (chartSimplexIn E v hvt) 1) :=
      hrelQ.mono (Set.singleton_subset_iff.mpr (hNQ x₂ hx₂))
    have e₁ := eval_eq_zero_of_sub_bd_mem_inside hγ₁.1 hrel₁.choose_spec
    have e₂ := eval_eq_zero_of_sub_bd_mem_inside hγ₂.1 hrel₂.choose_spec
    rw [map_sub, map_smul, hγ₁1, smul_eq_mul, mul_one, sub_eq_zero] at e₁
    rw [map_sub, map_smul, hγ₂1, smul_eq_mul, mul_one, sub_eq_zero] at e₂
    rw [show SingularCochain.eval (γ₁ - γ₂) c =
        SingularCochain.eval γ₁ c - SingularCochain.eval γ₂ c
      by simp [SingularCochain.eval, linearCombination_apply, Finsupp.sum_sub, mul_sub], e₁, e₂,
      sub_self]
  have k₃ := relCoboundaries_le_relCoboundaries_compl_univ ℚ _ _ hd
  have : α₁ - α₂ = (α₁ - γ₁) + (γ₁ - γ₂) - (α₂ - γ₂) := by abel
  rw [this]
  exact Submodule.sub_mem _ (Submodule.add_mem _ k₁ k₃) k₂

end Independence

/-! ### The orientation class of `V⁺` -/

section Generator

open MMP MMP.SingularChain MMP.SingularCochain
  MMP.ThomClass MMP.FundamentalClass
  MMP.PoincareDuality
  Set Finsupp Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {S : TopCat.{0}} [T2Space S] [LocallyCompactSpace S] [ChartedSpace H S]
  (b : Module.Basis (Fin 2) ℝ H)

attribute [local instance] t2Space_XV

/-- The absolute class of a local orientation class. -/
private noncomputable def absClass (V : Opens S) [Nonempty V] {x : S} {α : Simplex (XV V) 2 → ℚ}
    (h : IsCOX b V x α) : relCohomology ℚ (Set.univᶜ : Set (XV V)) 2 :=
  Submodule.Quotient.mk ⟨α, mem_relCocycles_compl_univ ℚ h.1⟩

/-- All local orientation classes of a connected `V` have the same image in `H^2(V⁺)`. -/
private lemma absClass_eq (hS : IsOrientedAtlas H S) (V : Opens S) [Nonempty V] [ConnectedSpace V]
    {x₁ x₂ : S} (hx₁ : x₁ ∈ V) (hx₂ : x₂ ∈ V) {α₁ α₂ : Simplex (XV V) 2 → ℚ}
    (h₁ : IsCOX b V x₁ α₁) (h₂ : IsCOX b V x₂ α₂) : absClass b V h₁ = absClass b V h₂ := by
  choose c hc using fun y : V => exists_isCOX b V y.2
  let cls : V → relCohomology ℚ (Set.univᶜ : Set (XV V)) 2 := fun y => absClass b V (hc y)
  have hloc : IsLocallyConstant cls := (IsLocallyConstant.iff_eventually_eq cls).2 fun y₀ => by
    obtain ⟨N, hN, hNe⟩ := exists_nhds_sub_mem_relCoboundaries b V hS y₀.2
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds hN] with y hy
    exact (Submodule.Quotient.eq ((relCoboundaries ℚ _ 2).comap (relCocycles ℚ _ 2).subtype)).2
      (hNe y hy y₀ (mem_of_mem_nhds hN) _ _ (hc y) (hc y₀))
  have e12 := hloc.apply_eq_of_preconnectedSpace ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
  have k₁ := relCoboundaries_le_relCoboundaries_compl_univ ℚ _ _
    (sub_mem_relCoboundaries_of_isCOX b V hS hx₁ h₁ (hc ⟨x₁, hx₁⟩))
  have k₂ := relCoboundaries_le_relCoboundaries_compl_univ ℚ _ _
    (sub_mem_relCoboundaries_of_isCOX b V hS hx₂ h₂ (hc ⟨x₂, hx₂⟩))
  have e₁ : absClass b V h₁ = cls ⟨x₁, hx₁⟩ :=
    (Submodule.Quotient.eq ((relCoboundaries ℚ _ 2).comap (relCocycles ℚ _ 2).subtype)).2 k₁
  have e₂ : absClass b V h₂ = cls ⟨x₂, hx₂⟩ :=
    (Submodule.Quotient.eq ((relCoboundaries ℚ _ 2).comap (relCocycles ℚ _ 2).subtype)).2 k₂
  rw [e₁, e₂, e12]

/-- The pull-back of a local orientation class along the collapse `V⁺ → V'⁺` is a local
orientation class. -/
private lemma isCOX_cochainPullback {V' V : Opens S} (h : V' ≤ V) [Nonempty V'] [Nonempty V]
    {x : S} (hx : x ∈ V') {α : Simplex (XV V') 2 → ℚ} (hα : IsCOX b V' x α) :
    ∃ hpre : ({κV V x}ᶜ : Set (XV V)) ⊆ cV h ⁻¹' ({κV V' x}ᶜ : Set (XV V')),
      IsCOX b V x (cochainPullback ℚ (cV h) 2 α) := by
  have hpre : ({κV V x}ᶜ : Set (XV V)) ⊆ cV h ⁻¹' ({κV V' x}ᶜ : Set (XV V')) := by
    intro z hz hcz
    apply hz
    induction z using OnePoint.rec with
    | infty =>
      exfalso
      rw [Set.mem_singleton_iff, cV_apply, cf_infty, κV_apply, κf_of_mem V' hx] at hcz
      exact OnePoint.coe_ne_infty _ hcz.symm
    | coe y =>
      rw [Set.mem_singleton_iff, cV_apply, cf_coe] at hcz
      have := κV_eq_iff V' hx (y : S) hcz
      rw [κV_apply, κf_of_mem V (h hx)]
      exact congrArg _ (Subtype.ext this)
  obtain ⟨hαc, e, he, hxe, v, hv, hvt, h1⟩ := hα
  have hvt' : range (affineSimplex v) ⊆ (eX V e).target := by
    refine hvt.trans ?_
    rw [eX_target, eX_target]
    exact inter_subset_inter_right _ (preimage_mono (h := h))
  refine ⟨hpre, cochainPullback_mem_relCocycles (cV h) hpre hαc, e, he, hxe, v, hv, hvt', ?_⟩
  have hcomp : (cV h).hom.comp (chartSimplexIn (eX V e) v hvt') =
      chartSimplexIn (eX V' e) v hvt := by
    ext t
    change cf h (κf V (e.symm _)) = κf V' (e.symm _)
    rw [cf_comp_κf]
  change linearCombination ℚ (cochainPullback ℚ (cV h) 2 α) (single _ 1) = 1
  rw [linearCombination_single, one_smul, cochainPullback_apply, hcomp]
  simpa [SingularCochain.eval, linearCombination_single] using h1

end Generator

/-! ### Singular cohomology of `V⁺` -/

section Cohomology

open MMP MMP.SingularChain MMP.SingularCochain
  MMP.ThomClass MMP.FundamentalClass
  MMP.PoincareDuality
  Set Finsupp Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {S : TopCat.{0}} [T2Space S] [LocallyCompactSpace S] [ChartedSpace H S]
  (b : Module.Basis (Fin 2) ℝ H)

attribute [local instance] t2Space_XV

/-- The chosen point of `V`. -/
private noncomputable def ptV (V : Opens S) [Nonempty V] : S := (Classical.arbitrary V).1

private lemma ptV_mem (V : Opens S) [Nonempty V] : ptV V ∈ V := (Classical.arbitrary V).2

/-- The orientation class of `V⁺`. -/
private noncomputable def gV (V : Opens S) [Nonempty V] :
    relCohomology ℚ (Set.univᶜ : Set (XV V)) 2 :=
  absClass b V (exists_isCOX b V (ptV_mem V)).choose_spec

variable (V : Opens S) [Nonempty V] (h : V ≃ₜ EuclideanSpace ℝ (Fin 2))

private lemma chart_ptV : κV V (ptV V) ∈ (eX V (chartAt H (ptV V))).source :=
  mem_eX_source V (mem_chart_source H _) (ptV_mem V)

include b h in
/-- `H^k(V⁺; ℚ) = 0` for `k = 1` and `k ≥ 3`. -/
private lemma mem_relCoboundaries_XV {k : ℕ} (hk : k = 1 ∨ 3 ≤ k)
    {φ : Simplex (XV V) k → ℚ} (hφ : φ ∈ relCocycles ℚ (Set.univᶜ : Set (XV V)) k) :
    φ ∈ relCoboundaries ℚ (Set.univᶜ : Set (XV V)) k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine mem_relCoboundaries_of_point (κV V (ptV V)) (cycleVanishing_compl_singleton V h _) m ?_
    hφ.2
  rcases hk with hk | hk
  · obtain rfl : m = 0 := by omega
    exact relVanishing_singleton_of_mem_source b _ (chart_ptV V) (by norm_num)
  · exact relVanishing_singleton_high b _ (chart_ptV V) (by omega)

include b h in
private lemma subsingleton_relCohomology_XV {k : ℕ} (hk : k = 1 ∨ 3 ≤ k) :
    Subsingleton (relCohomology ℚ (Set.univᶜ : Set (XV V)) k) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨⟨φ, hφ⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨⟨ψ, hψ⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine (Submodule.Quotient.eq _).2 ?_
  exact mem_relCoboundaries_XV b V h hk (Submodule.sub_mem _ hφ hψ)

include h in
/-- `H^2(V⁺; ℚ)` is free of rank one on the orientation class. -/
private lemma bijective_smul_gV : Function.Bijective fun r : ℚ => r • gV b V := by
  obtain ⟨hα, e, he, hxe, v, hv, hvt, h1⟩ := (exists_isCOX b V (ptV_mem V)).choose_spec
  set α := (exists_isCOX b V (ptV_mem V)).choose
  set y := κV V (ptV V)
  have hy : y ∈ (eX V e).source := mem_eX_source V hxe (ptV_mem V)
  have hv' : IsOrientedSimplexAroundZero b fun k ↦ v k - (eX V e) y := by
    rwa [eX_κV V (ptV_mem V)]
  have hCV := cycleVanishing_compl_singleton V h y
  have hbd : bd ℚ 1 (single (chartSimplexIn (eX V e) v hvt) 1) ∈ inside ℚ 1 ({y}ᶜ : Set (XV V)) :=
    bd_single_chartSimplex_mem_inside hvt (fun z hz => by
      rw [Set.mem_singleton_iff.mp hz]; exact ⟨hy, hv'⟩)
  have hg0 : gV b V ≠ 0 := by
    intro h0
    have hmem : α ∈ relCoboundaries ℚ (Set.univᶜ : Set (XV V)) 2 := by
      have := (Submodule.Quotient.mk_eq_zero _).1 h0
      exact this
    have hrel := mem_relCoboundaries_of_compl_univ y hCV hα hmem
    have := eval_eq_zero_of_mem_relCoboundaries hbd hrel
    rw [this] at h1
    exact zero_ne_one h1
  refine ⟨smul_left_injective ℚ hg0, fun z => ?_⟩
  obtain ⟨⟨φ, hφ⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨β, hβ⟩ := exists_sub_mem_relCocycles y hCV hφ.2
  set r := SingularCochain.eval (φ - coboundary ℚ 1 β) (single (chartSimplexIn (eX V e) v hvt) 1)
  refine ⟨r, (Submodule.Quotient.eq _).2 ?_⟩
  have hdiff : (φ - coboundary ℚ 1 β) - r • α ∈ relCoboundaries ℚ ({y}ᶜ : Set (XV V)) 2 := by
    refine mem_relCoboundaries_of_eval_chartSimplexOf b hy hv' hvt
      (Submodule.sub_mem _ hβ (Submodule.smul_mem _ _ hα)) ?_
    have e1 : α (chartSimplexIn (eX V e) v hvt) = 1 := by
      simpa [SingularCochain.eval, linearCombination_single] using h1
    have er : r = (φ - coboundary ℚ 1 β) (chartSimplexIn (eX V e) v hvt) := by
      simp [r, SingularCochain.eval, linearCombination_single]
    change linearCombination ℚ ((φ - coboundary ℚ 1 β) - r • α)
      (single (chartSimplexIn (eX V e) v hvt) 1) = 0
    rw [linearCombination_single, one_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e1, mul_one,
      er, sub_self]
  have h2 := relCoboundaries_le_relCoboundaries_compl_univ ℚ _ _ hdiff
  have h3 := mem_relCoboundaries_compl_univ (Y := XV V) β
  change r • α - φ ∈ relCoboundaries ℚ (Set.univᶜ : Set (XV V)) 2
  have : r • α - φ = -(((φ - coboundary ℚ 1 β) - r • α) + coboundary ℚ 1 β) := by abel
  rw [this]
  exact Submodule.neg_mem _ (Submodule.add_mem _ h2 h3)

omit h in
/-- The collapse `V⁺ → V'⁺` carries the orientation class to the orientation class. -/
private lemma relCohomologyMap_gV (hS : IsOrientedAtlas H S) {V' : Opens S} (hle : V' ≤ V)
    [Nonempty V'] [ConnectedSpace V] :
    relCohomologyMap ℚ (cV hle) (fun z hz => absurd (Set.mem_univ z) hz) 2 (gV b V') = gV b V := by
  obtain ⟨_, hpull⟩ := isCOX_cochainPullback b hle (ptV_mem V')
    (exists_isCOX b V' (ptV_mem V')).choose_spec
  refine Eq.trans ?_ (absClass_eq b hS V (hle (ptV_mem V')) (ptV_mem V) hpull
    (exists_isCOX b V (ptV_mem V)).choose_spec)
  rfl

end Cohomology

/-! ### The comparison maps on compactly supported sections -/

section Bridges

variable {S : TopCat.{0}} [T2Space S] [LocallyCompactSpace S]

attribute [local instance] t2Space_XV additive_pushF additive_ΦV

/-- `Γ_c(V⁺, j_! j^* κ_* G) ⟶ Γ(S, G)`. -/
private noncomputable def aκ (V : Opens S) :
    ΦV V ⋙ Γc (XV V) ⟶ ΓF S where
  app G := (aU (UV V)).app ((TopCat.Sheaf.pushforward _ (κV V)).obj G)
  naturality _ _ f := (aU (UV V)).naturality ((TopCat.Sheaf.pushforward _ (κV V)).map f)

private lemma aκ_injective (V : Opens S) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) S) :
    Function.Injective ((aκ V).app G) :=
  aU_injective (extHyp_UV V) _

private lemma range_aκ_le (V : Opens S) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) S) (s) :
    ∃ y, (aU V).app G y = (aκ V).app G s :=
  exists_aU (extHyp V) G _ ((suppIn_push_iff V G _).mp (suppIn_aU (extHyp_UV V) _ s))

private lemma range_aU_le (V : Opens S) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) S) (s) :
    ∃ y, (aκ V).app G y = (aU V).app G s :=
  exists_aU (extHyp_UV V) _ _ ((suppIn_push_iff V G _).mpr (suppIn_aU (extHyp V) G s))

/-- `Γ_c(V⁺, j_! j^* κ_* G) ≅ Γ_c(S, j_{V!} j_V^* G)`: both are the global sections of `G` with
compact support in `V`. -/
private noncomputable def bridge (V : Opens S) : ΦV V ⋙ Γc (XV V) ≅ PF V ⋙ Γc S where
  hom := liftOfRange (aκ V) (aU V) (aU_injective (extHyp V)) (range_aκ_le V)
  inv := liftOfRange (aU V) (aκ V) (aκ_injective V) (range_aU_le V)
  hom_inv_id := by
    ext G s
    apply aκ_injective V G
    simp only [NatTrans.comp_app, ModuleCat.comp_apply, NatTrans.id_app, ModuleCat.id_apply]
    rw [liftOfRange_app_apply, liftOfRange_app_apply]
  inv_hom_id := by
    ext G s
    apply aU_injective (extHyp V) G
    simp only [NatTrans.comp_app, ModuleCat.comp_apply, NatTrans.id_app, ModuleCat.id_apply]
    rw [liftOfRange_app_apply, liftOfRange_app_apply]

private lemma aU_bridge_hom (V : Opens S) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) S) (s) :
    (aU V).app G ((bridge V).hom.app G s) = (aκ V).app G s :=
  liftOfRange_app_apply (aκ V) (aU V) (aU_injective (extHyp V)) (range_aκ_le V) G s

/-- `Γ_c(V'⁺, j_! j^* c_* G) ⟶ Γ(V⁺, G)` for the collapse `c : V⁺ → V'⁺`. -/
private noncomputable def aC {V' V : Opens S} (h : V' ≤ V) :
    TopCat.Sheaf.pushforward _ (cV h) ⋙ PF (UV V') ⋙ Γc (XV V') ⟶ ΓF (XV V) where
  app G := (aU (UV V')).app ((TopCat.Sheaf.pushforward _ (cV h)).obj G)
  naturality _ _ f := (aU (UV V')).naturality ((TopCat.Sheaf.pushforward _ (cV h)).map f)

/-- Compactly supported sections in `V'⁺` are compactly supported in `V⁺`. -/
private noncomputable def incC {V' V : Opens S} (h : V' ≤ V) :
    TopCat.Sheaf.pushforward _ (cV h) ⋙ PF (UV V') ⋙ Γc (XV V') ⟶ PF (UV V) ⋙ Γc (XV V) :=
  liftOfRange (aC h) (aU (UV V)) (aU_injective (extHyp_UV V)) fun G s =>
    exists_aU (extHyp_UV V) G _ (suppIn_of_push_cV h G _ (suppIn_aU (extHyp_UV V') _ s))

private lemma aU_incC {V' V : Opens S} (h : V' ≤ V)
    (G : TopCat.Sheaf (ModuleCat.{0} ℚ) (XV V)) (s) :
    (aU (UV V)).app G ((incC h).app G s) = (aC h).app G s :=
  liftOfRange_app_apply _ _ (aU_injective (extHyp_UV V)) (fun G s =>
    exists_aU (extHyp_UV V) G _ (suppIn_of_push_cV h G _ (suppIn_aU (extHyp_UV V') _ s))) G s

end Bridges

section CSoftPF

variable {X : TopCat.{0}} [LocallyCompactSpace X] [T2Space X]

/-- `j_! j^*` carries injective sheaves to c-soft sheaves. -/
private lemma csoft_PF {U : Opens X} (h : ExtHyp U) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) X)
    (hG : Injective G) : CSoft ((PF U).obj G) := by
  haveI := h.exact.1
  haveI : Injective ((resF U).obj G) := Injective.injective_of_adjoint (adjF U) G
  haveI : LocallyCompactSpace ((Opens.toTopCat X).obj U) :=
    U.2.isOpenEmbedding_subtypeVal.locallyCompactSpace
  haveI : T2Space ((Opens.toTopCat X).obj U) := inferInstanceAs (T2Space U)
  have hc := (compactSupportCohomology_of_isCSoft ℚ ((Opens.toTopCat X).obj U)).1.2
    ((resF U).obj G) inferInstance
  have hc' := h.csoftExt ((resF U).obj G) (fun K hK W hKW s => by
    obtain ⟨t, W', hKW', hW'W, e⟩ := hc K hK W hKW s
    exact ⟨t, W', hW'W, hKW', e.symm⟩)
  intro K hK W hKW s
  obtain ⟨t, W', hW'W, hKW', e⟩ := hc' K hK W hKW s
  exact ⟨t, W', hKW', hW'W, e.symm⟩

end CSoftPF

/-! ### Resolutions on `S` and on `V⁺` -/

section Resolutions

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]

/-- The resolution `Φ(Z)[0] ⟶ Φ(J)` induced by an injective resolution `Z[0] ⟶ J`. -/
private noncomputable def augOf (Φ : C ⥤ D) [Φ.Additive] {Z : C} (J : InjectiveResolution Z) :
    (CochainComplex.single₀ D).obj (Φ.obj Z) ⟶ (Φ.mapHomologicalComplex _).obj J.cocomplex :=
  (HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℕ) 0).inv.app Z ≫
    (Φ.mapHomologicalComplex _).map J.ι

private lemma quasiIso_augOf (Φ : C ⥤ D) [Φ.Additive] [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ] {Z : C} (J : InjectiveResolution Z) : QuasiIso (augOf Φ J) := by
  haveI : Φ.PreservesHomology := ⟨fun _ _ _ => inferInstance, fun _ _ _ => inferInstance⟩
  have h2 : QuasiIso ((Φ.mapHomologicalComplex _).map J.ι) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology J.ι Φ
  exact quasiIso_comp (hφ := quasiIso_of_isIso _) (hφ' := h2) _ _

private lemma augOf_f_zero (Φ : C ⥤ D) [Φ.Additive] {Z : C} (J : InjectiveResolution Z) :
    (augOf Φ J).f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (Φ.obj Z)).hom ≫
      Φ.map (J.ι.f 0) := by
  simp [augOf]

set_option backward.isDefEq.respectTransparency false in
private lemma augOf_naturality {C' : Type*} [Category C'] [Abelian C'] {Φ : C ⥤ D} {Φ' : C' ⥤ D}
    [Φ.Additive] [Φ'.Additive] {Z : C} {Z' : C'}
    (J : InjectiveResolution Z) (J' : InjectiveResolution Z')
    (ψ : Φ.obj Z ⟶ Φ'.obj Z') (g : (Φ.mapHomologicalComplex _).obj J.cocomplex ⟶
      (Φ'.mapHomologicalComplex _).obj J'.cocomplex)
    (h : Φ.map (J.ι.f 0) ≫ g.f 0 = ψ ≫ Φ'.map (J'.ι.f 0)) :
    augOf Φ J ≫ g = (CochainComplex.single₀ D).map ψ ≫ augOf Φ' J' := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, augOf_f_zero, augOf_f_zero,
    Category.assoc, h, HomologicalComplex.single_map_f_self]
  simp

end Resolutions

/-! ### Comparison of `H^n_c(S, j_{V!} ℚ)` with `V⁺` -/

section PlaneData

variable {S : TopCat.{0}} [T2Space S] [LocallyCompactSpace S]

attribute [local instance] t2Space_XV additive_pushF additive_ΦV

/-- The constant sheaf `ℚ`. -/
private noncomputable abbrev QQ (Y : TopCat.{0}) : TopCat.Sheaf (ModuleCat.{0} ℚ) Y :=
  cSh Y (ModuleCat.of ℚ ℚ)

/-- The chosen injective resolution of `ℚ`. -/
private noncomputable abbrev JJ (Y : TopCat.{0}) : InjectiveResolution (QQ Y) :=
  injectiveResolution (QQ Y)

set_option backward.isDefEq.respectTransparency false in
private lemma exists_πV (V : Opens S) :
    ∃ π : (JJ (XV V)).cocomplex ⟶
        ((TopCat.Sheaf.pushforward _ (κV V)).mapHomologicalComplex _).obj (JJ S).cocomplex,
      (JJ (XV V)).ι.f 0 ≫ π.f 0 =
        MMP.Analytic.constUnit (κV V) ≫ (TopCat.Sheaf.pushforward _ (κV V)).map ((JJ S).ι.f 0) := by
  haveI := MMP.Analytic.pushforward_preservesInjectiveObjects (κV V)
  refine exists_hom_of_injective _ _ (fun n =>
    show Injective ((TopCat.Sheaf.pushforward _ (κV V)).obj
    ((JJ S).cocomplex.X n)) from Functor.injective_obj _ _) _ ?_
  rw [Category.assoc, Functor.mapHomologicalComplex_obj_d, ← CategoryTheory.Functor.map_comp,
    InjectiveResolution.ι_f_zero_comp_complex_d, Functor.map_zero, Limits.comp_zero]

/-- A chosen map of resolutions `ℚ_{V⁺} ⟶ κ_* ℚ_S`. -/
private noncomputable def πV (V : Opens S) := (exists_πV V).choose

private lemma πV_spec (V : Opens S) :
    (JJ (XV V)).ι.f 0 ≫ (πV V).f 0 =
      MMP.Analytic.constUnit (κV V) ≫ (TopCat.Sheaf.pushforward _ (κV V)).map ((JJ S).ι.f 0) :=
  (exists_πV V).choose_spec

/-- `j_{V!} j_V^* J` on `S`. -/
private noncomputable abbrev CC (V : Opens S) :=
  ((PF V).mapHomologicalComplex (ComplexShape.up ℕ)).obj (JJ S).cocomplex

/-- `j_! j^* J_{V⁺}` on `V⁺`. -/
private noncomputable abbrev EE (V : Opens S) :=
  ((PF (UV V)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (JJ (XV V)).cocomplex

/-- `j_! j^* κ_* J` on `V⁺`. -/
private noncomputable abbrev DD (V : Opens S) :=
  ((ΦV V).mapHomologicalComplex (ComplexShape.up ℕ)).obj (JJ S).cocomplex

private lemma quasiIso_ιC (V : Opens S) : QuasiIso (augOf (PF V) (JJ S)) := by
  haveI := (exact_PF (extHyp V)).1
  haveI := (exact_PF (extHyp V)).2
  exact quasiIso_augOf _ _

private lemma quasiIso_ιE (V : Opens S) : QuasiIso (augOf (PF (UV V)) (JJ (XV V))) := by
  haveI := (exact_PF (extHyp_UV V)).1
  haveI := (exact_PF (extHyp_UV V)).2
  exact quasiIso_augOf _ _

private lemma quasiIso_ιD (V : Opens S) : QuasiIso (augOf (ΦV V) (JJ S)) := by
  haveI := (exact_ΦV V).1
  haveI := (exact_ΦV V).2
  exact quasiIso_augOf _ _

private lemma csoft_CC (V : Opens S) (n : ℕ) : CSoft ((CC V).X n) :=
  csoft_PF (extHyp V) _ inferInstance

private lemma csoft_EE (V : Opens S) (n : ℕ) : CSoft ((EE V).X n) :=
  csoft_PF (extHyp_UV V) _ inferInstance

private lemma csoft_DD (V : Opens S) (n : ℕ) : CSoft ((DD V).X n) := by
  haveI := MMP.Analytic.pushforward_preservesInjectiveObjects (κV V)
  exact csoft_PF (extHyp_UV V) _ (show Injective ((TopCat.Sheaf.pushforward _ (κV V)).obj
    ((JJ S).cocomplex.X n)) from Functor.injective_obj _ _)

/-- `j_! j^* π : j_! j^* J_{V⁺} ⟶ j_! j^* κ_* J`. -/
private noncomputable def Pπ (V : Opens S) : EE V ⟶ DD V :=
  ((PF (UV V)).mapHomologicalComplex _).map (πV V)

private lemma augOf_Pπ (V : Opens S) :
    augOf (PF (UV V)) (JJ (XV V)) ≫ Pπ V =
      (CochainComplex.single₀ _).map ((PF (UV V)).map (MMP.Analytic.constUnit (κV V))) ≫
        augOf (ΦV V) (JJ S) := by
  refine augOf_naturality (Φ := PF (UV V)) (Φ' := ΦV V) _ _ _ _ ?_
  change (PF (UV V)).map ((JJ (XV V)).ι.f 0) ≫ (PF (UV V)).map ((πV V).f 0) = _
  rw [← CategoryTheory.Functor.map_comp, πV_spec]
  exact (PF (UV V)).map_comp _ _

private lemma isIso_homologyMap_Pπ (V : Opens S) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      ((Γc (XV V)).mapHomologicalComplex _ |>.map (Pπ V)) n) := by
  haveI := quasiIso_ιE V
  haveI := quasiIso_ιD V
  haveI := isIso_PF_constUnit V
  have h := cmpN_naturality (augOf (PF (UV V)) (JJ (XV V))) (csoft_EE V) (augOf (ΦV V) (JJ S))
    (csoft_DD V) _ (Pπ V) (augOf_Pπ V) n
  have : HomologicalComplex.homologyMap ((Γc (XV V)).mapHomologicalComplex _ |>.map (Pπ V)) n =
      inv (cmpN (augOf (PF (UV V)) (JJ (XV V))) (csoft_EE V) n).hom ≫
        (HcF (XV V) n).map ((PF (UV V)).map (MMP.Analytic.constUnit (κV V))) ≫
          (cmpN (augOf (ΦV V) (JJ S)) (csoft_DD V) n).hom := by
    rw [IsIso.eq_inv_comp, h]
  rw [this]
  infer_instance

/-- The bridge `Γ_c(V⁺, j_! j^* κ_* J) ≅ Γ_c(S, j_{V!} j_V^* J)` of complexes. -/
private noncomputable def bridgeCx (V : Opens S) :
    ((Γc (XV V)).mapHomologicalComplex _).obj (DD V) ≅
      ((Γc S).mapHomologicalComplex _).obj (CC V) :=
  (NatIso.mapHomologicalComplex (bridge V) (ComplexShape.up ℕ)).app (JJ S).cocomplex

/-- `H^n_c(S, j_{V!} ℚ) ≅ H^n(Γ_c(V⁺, j_! j^* J_{V⁺}))`. -/
private noncomputable def Θ (V : Opens S) (n : ℕ) :
    (HcF S n).obj ((PF V).obj (QQ S)) ≅
      (((Γc (XV V)).mapHomologicalComplex _).obj (EE V)).homology n :=
  haveI := quasiIso_ιC V
  haveI := isIso_homologyMap_Pπ V n
  cmpN (augOf (PF V) (JJ S)) (csoft_CC V) n ≪≫
    (HomologicalComplex.homologyMapIso (bridgeCx V) n).symm ≪≫
      (asIso (HomologicalComplex.homologyMap
        ((Γc (XV V)).mapHomologicalComplex _ |>.map (Pπ V)) n)).symm

end PlaneData

/-! ### Compactly supported sections near the point at infinity -/

section AtInfinity

variable {S : TopCat.{0}} [T2Space S] [LocallyCompactSpace S]

attribute [local instance] t2Space_XV additive_pushF additive_ΦV

/-- The germ at a point, as a natural transformation from global sections. -/
private noncomputable def germAt {Y : TopCat.{0}} (y : Y) : ΓF Y ⟶ st y where
  app G := G.presheaf.germ ⊤ y (Opens.mem_top y)
  naturality _ _ f := (TopCat.Presheaf.stalkFunctor_map_germ ⊤ y (Opens.mem_top y) f.hom).symm

private lemma aU_germAt (V : Opens S) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) (XV V)) :
    (aU (UV V)).app G ≫ (germAt (OnePoint.infty : XV V)).app G = 0 := by
  ext s
  change (germAt _).app G (((adjF (UV V)).counit.app G).hom.app (op ⊤) s.1) = 0
  refine (germ_map ((adjF (UV V)).counit.app G) _ (Opens.mem_top _) s.1).trans ?_
  have hsub := ModuleCat.isZero_iff_subsingleton.mp
    ((extHyp_UV V).zero ((resF (UV V)).obj G) _ (infty_notMem_UV V))
  exact (congrArg _ (@Subsingleton.elim _ hsub _ 0)).trans (map_zero _)

set_option backward.isDefEq.respectTransparency false in
/-- `0 ⟶ Γ_c(V, G) ⟶ Γ(V⁺, G) ⟶ G_∞ ⟶ 0` for a c-soft `G`. -/
private lemma shortExact_atInfinity (V : Opens S) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) (XV V))
    (hG : CSoft G) :
    (ShortComplex.mk _ _ (aU_germAt V G)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    intro t
    constructor
    · intro ht
      have hsupp : SuppIn (UV V) G t := by
        obtain ⟨N, hN, hNt, hres⟩ := (germ_eq_zero_iff _ _ (Opens.mem_top _) t).mp ht
        refine ⟨(N : Set (XV V))ᶜ, N.2.isClosed_compl.isCompact, fun z hz => ?_, fun z hz => ?_⟩
        · induction z using OnePoint.rec with
          | infty => exact absurd hN hz
          | coe y => exact coe_mem_UV V y
        · have hzN : z ∈ N := not_not.mp hz
          rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hNt) z hzN]
          exact (congrArg _ hres).trans (map_zero _)
      exact exists_aU (extHyp_UV V) G t hsupp
    · rintro ⟨s, rfl⟩
      exact ConcreteCategory.congr_hom (aU_germAt V G) s
  · exact (ModuleCat.mono_iff_injective _).mpr (aU_injective (extHyp_UV V) G)
  · refine (ModuleCat.epi_iff_surjective _).mpr fun c => ?_
    obtain ⟨W, hW, s, rfl⟩ := G.presheaf.exists_germ_eq c
    obtain ⟨t, W', hKW', hW'W, e⟩ := hG {OnePoint.infty} isCompact_singleton W
      (Set.singleton_subset_iff.mpr hW) s
    refine ⟨t, ?_⟩
    change G.presheaf.germ ⊤ _ (Opens.mem_top _) t = G.presheaf.germ W _ hW s
    have h1 := G.presheaf.germ_res_apply (homOfLE (le_top : W' ≤ ⊤)) _ (hKW' rfl) t
    have h2 := G.presheaf.germ_res_apply (homOfLE hW'W) _ (hKW' rfl) s
    rw [← h1, ← h2]
    exact congrArg _ e

end AtInfinity

/-! ### The long exact sequence at infinity -/

section AtInfinityHomology

/-- A map of `ℕ`-indexed cochain complexes which is a monomorphism in degree `0` is a
monomorphism on `H^0`. -/
private lemma mono_homologyMap_zero {C : Type*} [Category C] [Abelian C]
    {K L : CochainComplex C ℕ} (φ : K ⟶ L) [Mono (φ.f 0)] :
    Mono (HomologicalComplex.homologyMap φ 0) := by
  haveI : Mono (HomologicalComplex.cyclesMap φ 0) := by
    haveI : Mono (HomologicalComplex.cyclesMap φ 0 ≫ L.iCycles 0) := by
      rw [HomologicalComplex.cyclesMap_i]; infer_instance
    exact mono_of_mono _ (L.iCycles 0)
  have hπK : IsIso (K.homologyπ 0) := (CochainComplex.isoHomologyπ₀ K).isIso_hom
  have hπL : IsIso (L.homologyπ 0) := (CochainComplex.isoHomologyπ₀ L).isIso_hom
  have : HomologicalComplex.homologyMap φ 0 =
      inv (K.homologyπ 0) ≫ HomologicalComplex.cyclesMap φ 0 ≫ L.homologyπ 0 := by
    rw [← HomologicalComplex.homologyπ_naturality φ 0, IsIso.inv_hom_id_assoc]
  rw [this]
  infer_instance

private lemma additive_ΓF (Y : TopCat.{0}) : (ΓF Y).Additive := ⟨fun {_ _ _ _} => rfl⟩

private lemma preservesZeroMorphisms_ΓF (Y : TopCat.{0}) : (ΓF Y).PreservesZeroMorphisms :=
  haveI := additive_ΓF Y
  inferInstance

private lemma preservesFiniteLimits_ΓF (Y : TopCat.{0}) : PreservesFiniteLimits (ΓF Y) :=
  comp_preservesFiniteLimits (sheafToPresheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ))
    ((evaluation _ _).obj (op ⊤))

private lemma additive_st {Y : TopCat.{0}} (y : Y) : (st y).Additive :=
  inferInstanceAs (TopCat.Sheaf.forget _ Y ⋙ TopCat.Presheaf.stalkFunctor _ y).Additive

variable {S : TopCat.{0}} [T2Space S] [LocallyCompactSpace S]

attribute [local instance] t2Space_XV additive_pushF additive_ΦV additive_ΓF additive_st
  preservesZeroMorphisms_ΓF preservesFiniteLimits_ΓF

private lemma preservesZeroMorphisms_ΓF_XV (V : Opens S) : (ΓF (XV V)).PreservesZeroMorphisms :=
  preservesZeroMorphisms_ΓF _

private lemma additive_ΓF_XV (V : Opens S) : (ΓF (XV V)).Additive := additive_ΓF _

private lemma preservesFiniteLimits_ΓF_XV (V : Opens S) : PreservesFiniteLimits (ΓF (XV V)) :=
  preservesFiniteLimits_ΓF _

private lemma additive_st_XV (V : Opens S) (y : XV V) : (st y).Additive := additive_st y

attribute [local instance] preservesZeroMorphisms_ΓF_XV additive_ΓF_XV preservesFiniteLimits_ΓF_XV
  additive_st_XV

/-- Global sections of the resolution of `ℚ_{V⁺}`. -/
private noncomputable abbrev ΓX (V : Opens S) :=
  ((ΓF (XV V)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (JJ (XV V)).cocomplex

/-- Stalks at infinity of the resolution of `ℚ_{V⁺}`. -/
private noncomputable abbrev StX (V : Opens S) :=
  ((st (Y := XV V) OnePoint.infty).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (JJ (XV V)).cocomplex

/-- Compactly supported sections of `j_! j^* J_{V⁺}`. -/
private noncomputable abbrev ΓcE (V : Opens S) :=
  ((Γc (XV V)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (EE V)

private noncomputable def fInf (V : Opens S) : ΓcE V ⟶ ΓX V :=
  (NatTrans.mapHomologicalComplex (aU (UV V)) _).app (JJ (XV V)).cocomplex

private noncomputable def gInf (V : Opens S) : ΓX V ⟶ StX V :=
  (NatTrans.mapHomologicalComplex (germAt (Y := XV V) OnePoint.infty) _).app (JJ (XV V)).cocomplex

private lemma fInf_gInf (V : Opens S) : fInf V ≫ gInf V = 0 := by
  ext n : 1
  exact aU_germAt V _

private lemma csoft_JX (V : Opens S) (n : ℕ) : CSoft ((JJ (XV V)).cocomplex.X n) := by
  exact (compactSupportCohomology_of_isCSoft ℚ (XV V)).1.2 ((JJ (XV V)).cocomplex.X n)
    inferInstance

private lemma shortExact_inf (V : Opens S) :
    (ShortComplex.mk _ _ (fInf_gInf V)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    shortExact_atInfinity V _ (csoft_JX V n)

private lemma isZero_homology_StX (V : Opens S) (n : ℕ) (hn : n ≠ 0) :
    IsZero ((StX V).homology n) := by
  haveI := quasiIso_augOf (st (Y := XV V) OnePoint.infty) (JJ (XV V))
  exact (HomologicalComplex.isZero_single_obj_homology _ _ _ n hn).of_iso
    (asIso (HomologicalComplex.homologyMap (augOf _ (JJ (XV V))) n)).symm

private lemma isIso_homologyMap_fInf (V : Opens S) (n : ℕ) (hn : 2 ≤ n) :
    IsIso (HomologicalComplex.homologyMap (fInf V) n) := by
  have hS := shortExact_inf V
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  haveI : Mono (HomologicalComplex.homologyMap (fInf V) (k + 1)) :=
    (hS.homology_exact₁ k (k + 1) rfl).mono_g
      ((isZero_homology_StX V k (by omega)).eq_of_src _ _)
  haveI : Epi (HomologicalComplex.homologyMap (fInf V) (k + 1)) :=
    (hS.homology_exact₂ (k + 1)).epi_f ((isZero_homology_StX V (k + 1) (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

set_option backward.isDefEq.respectTransparency false in
private lemma bijective_homologyMap_gInf (V : Opens S) [ConnectedSpace (XV V)] :
    Function.Bijective (HomologicalComplex.homologyMap (gInf V) 0) := by
  let J := JJ (XV V)
  have hΓ := (J.exact₀.map_of_mono_of_preservesKernel (ΓF (XV V)) inferInstance inferInstance)
  have hst := (J.exact₀.map_of_mono_of_preservesKernel (st (Y := XV V) OnePoint.infty)
    inferInstance inferInstance)
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hΓ hst
  have hmono : Function.Injective ((st (Y := XV V) OnePoint.infty).map (J.ι.f 0)) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hnat : ∀ q, (germAt (Y := XV V) OnePoint.infty).app _ ((ΓF (XV V)).map (J.ι.f 0) q) =
      (st (Y := XV V) OnePoint.infty).map (J.ι.f 0) ((germAt (Y := XV V) OnePoint.infty).app _ q) :=
    fun q => ConcreteCategory.congr_hom ((germAt (Y := XV V) OnePoint.infty).naturality (J.ι.f 0)) q
  refine bijective_homologyMap_zero _ (fun x hx h0 => ?_) (fun y hy => ?_)
  · obtain ⟨q, rfl⟩ := (hΓ x).mp hx
    have hq : (QQ (XV V)).presheaf.germ ⊤ OnePoint.infty (Opens.mem_top _) q = 0 :=
      hmono ((hnat q).symm.trans (h0.trans (map_zero _).symm))
    rw [eq_zero_of_germ_eq_zero_of_connected (ModuleCat.of ℚ ℚ) q _ hq]
    exact map_zero _
  · obtain ⟨w, rfl⟩ := (hst y).mp hy
    obtain ⟨e, he⟩ := constantSheaf_exists_constSection_germ (V := XV V) (ModuleCat.of ℚ ℚ)
      OnePoint.infty w
    refine ⟨(ΓF (XV V)).map (J.ι.f 0) (constSection _ e), ?_, ?_⟩
    · change ((ΓF (XV V)).map (J.ι.f 0) ≫ (ΓF (XV V)).map (J.cocomplex.d 0 1)) _ = 0
      rw [← CategoryTheory.Functor.map_comp, J.ι_f_zero_comp_complex_d, Functor.map_zero]
      rfl
    · exact (hnat _).trans (congrArg _ he)

private lemma isZero_homology_ΓcE_zero (V : Opens S) [ConnectedSpace (XV V)] :
    IsZero ((ΓcE V).homology 0) := by
  haveI : Mono ((fInf V).f 0) :=
    (ModuleCat.mono_iff_injective _).mpr (aU_injective (extHyp_UV V) _)
  haveI := mono_homologyMap_zero (fInf V)
  haveI : Mono (HomologicalComplex.homologyMap (gInf V) 0) :=
    (ModuleCat.mono_iff_injective _).mpr (bijective_homologyMap_gInf V).1
  have h0 : HomologicalComplex.homologyMap (fInf V) 0 = 0 := by
    rw [← cancel_mono (HomologicalComplex.homologyMap (gInf V) 0), zero_comp,
      ← HomologicalComplex.homologyMap_comp, fInf_gInf, HomologicalComplex.homologyMap_zero]
  exact IsZero.of_mono_eq_zero _ h0

private lemma isZero_homology_ΓcE_one (V : Opens S) [ConnectedSpace (XV V)]
    (h1 : IsZero ((ΓX V).homology 1)) : IsZero ((ΓcE V).homology 1) := by
  have hS := shortExact_inf V
  haveI : Epi (HomologicalComplex.homologyMap (gInf V) 0) :=
    (ModuleCat.epi_iff_surjective _).mpr (bijective_homologyMap_gInf V).2
  have hδ : hS.δ 0 1 rfl = 0 := (hS.homology_exact₃ 0 1 rfl).epi_f_iff.mp inferInstance
  haveI : Mono (HomologicalComplex.homologyMap (fInf V) 1) :=
    (hS.homology_exact₁ 0 1 rfl).mono_g hδ
  exact IsZero.of_mono (HomologicalComplex.homologyMap (fInf V) 1) h1

end AtInfinityHomology

/-! ### Shrinking the plane -/

section Shrink

variable {S : TopCat.{0}} [T2Space S] [LocallyCompactSpace S]

attribute [local instance] t2Space_XV additive_pushF additive_ΦV additive_ΓF additive_st
  preservesZeroMorphisms_ΓF preservesFiniteLimits_ΓF

variable {V' V : Opens S} (hle : V' ≤ V)

private lemma eq_zero_of_stalk {Y : TopCat.{0}} {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) Y} (φ : F ⟶ G)
    (h : ∀ y, (st y).map φ = 0) : φ = 0 := by
  apply Sheaf.hom_ext
  ext W t
  refine (eq_zero_of_germ G (φ.hom.app W t) fun x hx => ?_).trans rfl
  rw [germ_map]
  exact (ConcreteCategory.congr_hom (h x) _).trans rfl

/-- The counit `j_! j^* G ⟶ G`. -/
private noncomputable def εU (U : Opens S) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) S) :
    (PF U).obj G ⟶ G :=
  (adjF U).counit.app G

private lemma mono_εU (U : Opens S) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) S) : Mono (εU U G) :=
  mono_counit (extHyp U) G

private lemma εU_naturality (U : Opens S) {G G' : TopCat.Sheaf (ModuleCat.{0} ℚ) S} (f : G ⟶ G') :
    (PF U).map f ≫ εU U G' = εU U G ≫ f :=
  (adjF U).counit.naturality f

attribute [local instance] mono_εU

include hle in
private lemma counit_comp_cokernel (G : TopCat.Sheaf (ModuleCat.{0} ℚ) S) :
    εU V' G ≫ cokernel.π (εU V G) = 0 := by
  change (adjF V').counit.app G ≫ cokernel.π ((adjF V).counit.app G) = 0
  refine eq_zero_of_stalk _ fun x => ?_
  rw [Functor.map_comp]
  by_cases hx : x ∈ V
  · haveI := isIso_stalk_counit (extHyp V) G ⟨x, hx⟩
    haveI : Epi ((st x).map ((adjF V).counit.app G)) := @IsIso.epi_of_iso _ _ _ _ _ this
    have h0 : (st x).map ((adjF V).counit.app G) ≫ (st x).map (cokernel.π ((adjF V).counit.app G))
        = 0 := by rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
    rw [(cancel_epi ((st x).map ((adjF V).counit.app G))).mp (h0.trans (comp_zero).symm),
      comp_zero]
  · exact ((extHyp V').zero _ x fun hx' => hx (hle hx')).eq_of_src _ _

include hle in
/-- `j_{V'!} j_{V'}^* ⟶ j_{V!} j_V^*` for `V' ⊆ V`. -/
private noncomputable def νPF : PF V' ⟶ PF V where
  app G := Abelian.monoLift (εU V G) (εU V' G) (counit_comp_cokernel hle G)
  naturality G G' f := by
    rw [← cancel_mono (εU V G'), Category.assoc, Category.assoc, Abelian.monoLift_comp,
      εU_naturality, εU_naturality, ← Category.assoc, Abelian.monoLift_comp]

private lemma νPF_comp_εU (G : TopCat.Sheaf (ModuleCat.{0} ℚ) S) :
    (νPF hle).app G ≫ εU V G = εU V' G :=
  Abelian.monoLift_comp _ _ _

private lemma eq_νPF (G : TopCat.Sheaf (ModuleCat.{0} ℚ) S) (m : (PF V').obj G ⟶ (PF V).obj G)
    (hm : m ≫ εU V G = εU V' G) : m = (νPF hle).app G := by
  rw [← cancel_mono (εU V G), hm, νPF_comp_εU]

private lemma aU_νPF (G : TopCat.Sheaf (ModuleCat.{0} ℚ) S) (s) :
    (aU V).app G ((Γc S).map ((νPF hle).app G) s) = (aU V').app G s := by
  change (inclΓ S).app G ((Γc S).map (εU V G) ((Γc S).map ((νPF hle).app G) s)) =
    (inclΓ S).app G ((Γc S).map (εU V' G) s)
  rw [← νPF_comp_εU hle G, Functor.map_comp, ModuleCat.comp_apply]

end Shrink

/-! ### Shrinking the plane: the comparison on `V⁺` -/

section ShrinkX

variable {S : TopCat.{0}} [T2Space S] [LocallyCompactSpace S]

attribute [local instance] t2Space_XV additive_pushF additive_ΦV additive_ΓF additive_st
  preservesZeroMorphisms_ΓF preservesFiniteLimits_ΓF preservesZeroMorphisms_ΓF_XV additive_ΓF_XV
  preservesFiniteLimits_ΓF_XV

variable {V' V : Opens S} (hle : V' ≤ V)

set_option backward.isDefEq.respectTransparency false in
private lemma exists_gC :
    ∃ g : (JJ (XV V')).cocomplex ⟶
        ((TopCat.Sheaf.pushforward _ (cV hle)).mapHomologicalComplex _).obj (JJ (XV V)).cocomplex,
      (JJ (XV V')).ι.f 0 ≫ g.f 0 = MMP.Analytic.constUnit (cV hle) ≫
        (TopCat.Sheaf.pushforward _ (cV hle)).map ((JJ (XV V)).ι.f 0) := by
  haveI := MMP.Analytic.pushforward_preservesInjectiveObjects (cV hle)
  refine exists_hom_of_injective _ _ (fun n => show Injective ((TopCat.Sheaf.pushforward _
    (cV hle)).obj ((JJ (XV V)).cocomplex.X n)) from Functor.injective_obj _ _) _ ?_
  rw [Category.assoc, Functor.mapHomologicalComplex_obj_d, ← CategoryTheory.Functor.map_comp,
    InjectiveResolution.ι_f_zero_comp_complex_d, Functor.map_zero, Limits.comp_zero]

/-- A map of resolutions `ℚ_{V'⁺} ⟶ c_* ℚ_{V⁺}` over the collapse `c : V⁺ → V'⁺`. -/
private noncomputable def gC := (exists_gC hle).choose

private lemma gC_spec : (JJ (XV V')).ι.f 0 ≫ (gC hle).f 0 = MMP.Analytic.constUnit (cV hle) ≫
    (TopCat.Sheaf.pushforward _ (cV hle)).map ((JJ (XV V)).ι.f 0) :=
  (exists_gC hle).choose_spec

/-- `g ≫ c_* π_V`, transported along `κ_V ≫ c = f₁`. -/
private noncomputable def πHat (f₁ : S ⟶ XV V') (hf : κV V ≫ cV hle = f₁) :
    (JJ (XV V')).cocomplex ⟶
      ((TopCat.Sheaf.pushforward _ f₁).mapHomologicalComplex _).obj (JJ S).cocomplex :=
  gC hle ≫ ((TopCat.Sheaf.pushforward _ (cV hle)).mapHomologicalComplex _).map (πV V) ≫
    (NatTrans.mapHomologicalComplex
      (eqToHom (congrArg (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ)) hf)) _).app (JJ S).cocomplex

set_option backward.isDefEq.respectTransparency false in
private lemma πHat_spec (f₁ : S ⟶ XV V') (hf : κV V ≫ cV hle = f₁) :
    (JJ (XV V')).ι.f 0 ≫ (πHat hle f₁ hf).f 0 =
      MMP.Analytic.constUnit f₁ ≫ (TopCat.Sheaf.pushforward _ f₁).map ((JJ S).ι.f 0) := by
  subst hf
  change (JJ (XV V')).ι.f 0 ≫ (gC hle).f 0 ≫
    (TopCat.Sheaf.pushforward _ (cV hle)).map ((πV V).f 0) ≫ 𝟙 _ = _
  rw [Category.comp_id, reassoc_of% (gC_spec hle), ← CategoryTheory.Functor.map_comp, πV_spec,
    CategoryTheory.Functor.map_comp, MMP.Analytic.constUnit_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma ΓF_πHat (f₁ : S ⟶ XV V') (hf : κV V ≫ cV hle = f₁) (n : ℕ) (x) :
    (ΓF (XV V')).map ((πHat hle f₁ hf).f n) x =
      (ΓF (XV V)).map ((πV V).f n) ((ΓF (XV V')).map ((gC hle).f n) x) := by
  subst hf
  rfl

/-- `Γ_c(V'⁺, j_! j^* J_{V'⁺}) ⟶ Γ_c(V⁺, j_! j^* J_{V⁺})`, induced by `g`. -/
private noncomputable def wC : ΓcE V' ⟶ ΓcE V :=
  ((Γc (XV V')).mapHomologicalComplex _).map (((PF (UV V')).mapHomologicalComplex _).map (gC hle)) ≫
    (NatTrans.mapHomologicalComplex (incC hle) _).app (JJ (XV V)).cocomplex

private lemma wC_fInf :
    wC hle ≫ fInf V = fInf V' ≫ ((ΓF (XV V')).mapHomologicalComplex _).map (gC hle) := by
  ext n s
  exact (aU_incC hle _ _).trans
    (ConcreteCategory.congr_hom ((aU (UV V')).naturality ((gC hle).f n)) s)

/-- The map `j_{V'!} j^* J ⟶ j_{V!} j^* J` of complexes on `S`. -/
private noncomputable def νJ : CC V' ⟶ CC V :=
  (NatTrans.mapHomologicalComplex (νPF hle) _).app (JJ S).cocomplex

set_option backward.isDefEq.respectTransparency false in
private lemma chain_compat :
    ((Γc (XV V')).mapHomologicalComplex _).map (((PF (UV V')).mapHomologicalComplex _).map
        (πHat hle (κV V') (κV_comp_cV hle))) ≫ (bridgeCx V').hom ≫
      ((Γc S).mapHomologicalComplex _).map (νJ hle) =
    wC hle ≫ ((Γc (XV V)).mapHomologicalComplex _).map (Pπ V) ≫ (bridgeCx V).hom := by
  ext n s
  apply aU_injective (extHyp V) ((JJ S).cocomplex.X n)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  refine Eq.trans (b := (ΓF (XV V)).map ((πV V).f n) ((ΓF (XV V')).map ((gC hle).f n)
    ((aU (UV V')).app ((JJ (XV V')).cocomplex.X n) s))) ?_ ?_
  · refine (aU_νPF hle _ _).trans ((aU_bridge_hom V' _ _).trans ?_)
    refine (ConcreteCategory.congr_hom ((aU (UV V')).naturality
      ((πHat hle (κV V') (κV_comp_cV hle)).f n)) s).trans ?_
    exact ΓF_πHat hle _ (κV_comp_cV hle) n _
  · refine Eq.symm ((aU_bridge_hom V _ _).trans ?_)
    refine (ConcreteCategory.congr_hom ((aU (UV V)).naturality ((πV V).f n)) _).trans ?_
    refine congrArg ((ΓF (XV V)).map ((πV V).f n)) ?_
    exact (aU_incC hle _ _).trans
      (ConcreteCategory.congr_hom ((aU (UV V')).naturality ((gC hle).f n)) s)

end ShrinkX

/-! ### The comparison in cohomology -/

section ShrinkH

open MMP MMP.SingularCochain

variable {S : TopCat.{0}} [T2Space S] [LocallyCompactSpace S]

attribute [local instance] t2Space_XV additive_pushF additive_ΦV additive_ΓF additive_st
  preservesZeroMorphisms_ΓF preservesFiniteLimits_ΓF preservesZeroMorphisms_ΓF_XV additive_ΓF_XV
  preservesFiniteLimits_ΓF_XV quasiIso_ιC

private lemma Θ_hom_comp (V : Opens S) (n : ℕ) :
    (Θ V n).hom ≫
      HomologicalComplex.homologyMap ((Γc (XV V)).mapHomologicalComplex _ |>.map (Pπ V)) n ≫
      HomologicalComplex.homologyMap (bridgeCx V).hom n =
    (cmpN (augOf (PF V) (JJ S)) (csoft_CC V) n).hom := by
  haveI := isIso_homologyMap_Pπ V n
  simp only [Θ, Iso.trans_hom, Iso.symm_hom, asIso_inv, HomologicalComplex.homologyMapIso_inv,
    Category.assoc, IsIso.inv_hom_id_assoc]
  rw [← HomologicalComplex.homologyMap_comp, Iso.inv_hom_id, HomologicalComplex.homologyMap_id,
    Category.comp_id]

variable {V' V : Opens S} (hle : V' ≤ V)

private lemma homologyMap_Pπ_eq (n : ℕ) :
    HomologicalComplex.homologyMap ((Γc (XV V')).mapHomologicalComplex _ |>.map (Pπ V')) n =
      HomologicalComplex.homologyMap ((Γc (XV V')).mapHomologicalComplex _ |>.map
        (((PF (UV V')).mapHomologicalComplex _).map (πHat hle (κV V') (κV_comp_cV hle)))) n := by
  haveI := MMP.Analytic.pushforward_preservesInjectiveObjects (κV V')
  have hK : ∀ k, Injective ((((TopCat.Sheaf.pushforward _ (κV V')).mapHomologicalComplex _).obj
      (JJ S).cocomplex).X k) := fun k =>
    show Injective ((TopCat.Sheaf.pushforward _ (κV V')).obj ((JJ S).cocomplex.X k)) from
      Functor.injective_obj _ _
  have h := homotopyOfInj (JJ (XV V')) hK (πV V') (πHat hle (κV V') (κV_comp_cV hle))
    ((πV_spec V').trans (πHat_spec hle _ _).symm)
  exact ((Γc (XV V')).mapHomotopy ((PF (UV V')).mapHomotopy h)).homologyMap_eq n

set_option backward.isDefEq.respectTransparency false in
private lemma augOf_νJ :
    augOf (PF V') (JJ S) ≫ νJ hle =
      (CochainComplex.single₀ _).map ((νPF hle).app (QQ S)) ≫ augOf (PF V) (JJ S) :=
  augOf_naturality (Φ := PF V') (Φ' := PF V) _ _ _ _ ((νPF hle).naturality ((JJ S).ι.f 0))

private lemma Θ_naturality (n : ℕ) :
    (HcF S n).map ((νPF hle).app (QQ S)) ≫ (Θ V n).hom = (Θ V' n).hom ≫
      HomologicalComplex.homologyMap (wC hle) n := by
  haveI := isIso_homologyMap_Pπ V n
  rw [← cancel_mono (HomologicalComplex.homologyMap ((Γc (XV V)).mapHomologicalComplex _ |>.map
    (Pπ V)) n ≫ HomologicalComplex.homologyMap (bridgeCx V).hom n), Category.assoc, Θ_hom_comp,
    ← cmpN_naturality _ (csoft_CC V') _ (csoft_CC V) _ (νJ hle) (augOf_νJ hle) n,
    Category.assoc, ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← chain_compat, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    ← homologyMap_Pπ_eq, ← Θ_hom_comp, Category.assoc, Category.assoc]

end ShrinkH

/-! ### Compactly supported cohomology of a plane -/

section PlaneCohomology

open MMP MMP.SingularCochain

variable {S : TopCat.{0}} [T2Space S] [LocallyCompactSpace S]

attribute [local instance] t2Space_XV additive_pushF additive_ΦV additive_ΓF additive_st
  preservesZeroMorphisms_ΓF preservesFiniteLimits_ΓF preservesZeroMorphisms_ΓF_XV additive_ΓF_XV
  preservesFiniteLimits_ΓF_XV quasiIso_ιC

/-- The chosen identification of rational sheaf cohomology with singular cohomology. -/
private noncomputable def eSing :
    ∀ (X : TopCat.{0}) [MetrizableSpace X], LocallyContractibleSpace X →
      ∀ (J : InjectiveResolution (QQ X)) (n : ℕ),
        ((((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj
          (op ⊤)).mapHomologicalComplex _).obj J.cocomplex).homology n ≅
          ModuleCat.of ℚ (relCohomology ℚ ((Set.univ : Set X)ᶜ) n) :=
  MMP.Analytic.exists_homology_globalSections_injectiveResolution_iso_relCohomology.choose

private lemma eSing_naturality (X Y : TopCat.{0}) [MetrizableSpace X] [MetrizableSpace Y]
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y) (f : Y ⟶ X)
    (J : InjectiveResolution (QQ X)) (J' : InjectiveResolution (QQ Y))
    (g : J.cocomplex ⟶ ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).mapHomologicalComplex
      _).obj J'.cocomplex)
    (hg : J.ι.f 0 ≫ g.f 0 =
      MMP.Analytic.constUnit f ≫ (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).map (J'.ι.f 0))
    (n : ℕ) :
    HomologicalComplex.homologyMap ((((sheafSections (Opens.grothendieckTopology X)
        (ModuleCat.{0} ℚ)).obj (op ⊤)).mapHomologicalComplex _).map g) n ≫
        (eSing Y hY J' n).hom =
      (eSing X hX J n).hom ≫
        ModuleCat.ofHom (relCohomologyMap ℚ f (fun z hz => absurd (Set.mem_univ z) hz) n) :=
  MMP.Analytic.exists_homology_globalSections_injectiveResolution_iso_relCohomology.choose_spec
    X Y hX hY f J J' g hg n

/-- `H^2_c(S, j_{V!} ℚ) ≅ H^2(V⁺; ℚ)`. -/
private noncomputable def Ψ2 (V : Opens S) [MetrizableSpace (XV V)]
    (hL : LocallyContractibleSpace (XV V)) :
    (HcF S 2).obj ((PF V).obj (QQ S)) ≅
      ModuleCat.of ℚ (relCohomology ℚ ((Set.univ : Set (XV V))ᶜ) 2) :=
  haveI := isIso_homologyMap_fInf V 2 le_rfl
  Θ V 2 ≪≫ asIso (HomologicalComplex.homologyMap (fInf V) 2) ≪≫ eSing (XV V) hL (JJ (XV V)) 2

private lemma Ψ2_hom (V : Opens S) [MetrizableSpace (XV V)]
    (hL : LocallyContractibleSpace (XV V)) :
    (Ψ2 V hL).hom = (Θ V 2).hom ≫ HomologicalComplex.homologyMap (fInf V) 2 ≫
      (eSing (XV V) hL (JJ (XV V)) 2).hom := rfl

set_option backward.isDefEq.respectTransparency false in
private lemma Ψ2_naturality {V' V : Opens S} (hle : V' ≤ V) [MetrizableSpace (XV V)]
    [MetrizableSpace (XV V')] (hL : LocallyContractibleSpace (XV V))
    (hL' : LocallyContractibleSpace (XV V')) :
    (HcF S 2).map ((νPF hle).app (QQ S)) ≫ (Ψ2 V hL).hom = (Ψ2 V' hL').hom ≫
      ModuleCat.ofHom (relCohomologyMap ℚ (cV hle) (fun z hz => absurd (Set.mem_univ z) hz) 2) := by
  have hE := eSing_naturality (XV V') (XV V) hL' hL (cV hle) (JJ (XV V')) (JJ (XV V)) (gC hle)
    (gC_spec hle) 2
  have hΘ : (HcF S 2).map ((νPF hle).app (QQ S)) ≫ (Θ V 2).hom =
      (Θ V' 2).hom ≫ HomologicalComplex.homologyMap (wC hle) 2 := Θ_naturality hle 2
  have hw := congrArg (fun t => HomologicalComplex.homologyMap t 2) (wC_fInf hle)
  simp only [HomologicalComplex.homologyMap_comp] at hw
  rw [Ψ2_hom, Ψ2_hom, Category.assoc]
  rw [← Category.assoc, hΘ, Category.assoc, reassoc_of% hw]
  exact congrArg (fun t => (Θ V' 2).hom ≫ HomologicalComplex.homologyMap (fInf V') 2 ≫ t) hE

end PlaneCohomology

/-! ### The case of rational coefficients -/

/-- The theorem for the constant sheaf `ℚ`: vanishing outside degree `2` and generators of
`H^2_c(S, j_{V!} ℚ)` compatible with the extension maps. -/
private theorem key_rat (H : Type u) [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] (hH : Module.finrank ℝ H = 2) (S : TopCat.{0}) [T2Space S]
    [ChartedSpace H S] (hS : MMP.IsOrientedAtlas H S) :
    let res : ∀ U : Opens S, TopCat.Sheaf (ModuleCat.{0} ℚ) S ⥤
        TopCat.Sheaf (ModuleCat.{0} ℚ) ((Opens.toTopCat S).obj U) := fun U =>
      haveI := U.isOpenEmbedding.functor_isContinuous
      U.isOpenEmbedding.functor.sheafPushforwardContinuous _ _ _
    let ext : ∀ U : Opens S, TopCat.Sheaf (ModuleCat.{0} ℚ) ((Opens.toTopCat S).obj U) ⥤
        TopCat.Sheaf (ModuleCat.{0} ℚ) S := fun U =>
      haveI := U.isOpenEmbedding.functor_isContinuous
      U.isOpenEmbedding.functor.sheafPullback _ _ _
    let adj : ∀ U : Opens S, ext U ⊣ res U := fun U =>
      haveI := U.isOpenEmbedding.functor_isContinuous
      U.isOpenEmbedding.functor.sheafAdjunctionContinuous _ _ _
    let Hc : ∀ (Y : TopCat.{0}) (_ : ℤ), TopCat.Sheaf (ModuleCat.{0} ℚ) Y ⥤ ModuleCat.{0} ℚ :=
      fun Y q => DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (compactSupportSectionsFunctor ℚ (X := Y)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ q
    let QS : TopCat.Sheaf (ModuleCat.{0} ℚ) S :=
      (constantSheaf (Opens.grothendieckTopology S) (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
    (∀ V : Opens S, Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2)) → ∀ q : ℤ, q ≠ 2 →
      IsZero ((Hc S q).obj ((ext V).obj ((res V).obj QS)))) ∧
    ∃ g : ∀ V : Opens S, Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2)) →
        (Hc S 2).obj ((ext V).obj ((res V).obj QS)),
      (∀ V hV, Function.Bijective fun r : ℚ => r • g V hV) ∧
      ∀ (V' V : Opens S) (_ : V' ≤ V) (hV' : Nonempty (V' ≃ₜ EuclideanSpace ℝ (Fin 2)))
        (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2)))
        (m : (ext V').obj ((res V').obj QS) ⟶ (ext V).obj ((res V).obj QS)),
        m ≫ (adj V).counit.app QS = (adj V').counit.app QS →
          (Hc S 2).map m (g V' hV') = g V hV := by
  intro res ext adj Hc QS
  haveI : LocallyCompactSpace S := ChartedSpace.locallyCompactSpace H S
  let b : Module.Basis (Fin 2) ℝ H := Module.finBasisOfFinrankEq ℝ H hH
  have hplane : ∀ V : Opens S, Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2)) →
      Nonempty V ∧ ConnectedSpace V ∧ ConnectedSpace (XV V) ∧ MetrizableSpace (XV V) ∧
        LocallyContractibleSpace (XV V) := by
    rintro V ⟨h⟩
    haveI : ConnectedSpace V := h.symm.surjective.connectedSpace h.symm.continuous
    haveI : NoncompactSpace V := h.symm.isClosedEmbedding.noncompactSpace
    exact ⟨⟨h.symm 0⟩, inferInstance, inferInstanceAs (ConnectedSpace (OnePoint V)),
      metrizableSpace_XV V h, locallyContractibleSpace_XV V h⟩
  have hzero : ∀ V : Opens S, ∀ (h : V ≃ₜ EuclideanSpace ℝ (Fin 2)) [Nonempty V]
      [MetrizableSpace (XV V)] (hL : LocallyContractibleSpace (XV V)) (k : ℕ), k = 1 ∨ 3 ≤ k →
      IsZero ((ΓX V).homology k) := by
    intro V h _ _ hL k hk
    haveI := subsingleton_relCohomology_XV b V h hk
    exact (ModuleCat.isZero_of_subsingleton _).of_iso (eSing (XV V) hL (JJ (XV V)) k)
  refine ⟨fun V hV q hq => ?_, ?_⟩
  · obtain ⟨hne, -, hcX, hM, hL⟩ := hplane V hV
    obtain ⟨h⟩ := hV
    change IsZero ((HcF S q).obj ((PF V).obj (QQ S)))
    rcases lt_or_ge q 0 with hq0 | hq0
    · haveI := quasiIso_ιC V
      exact isZero_HcF_neg (augOf (PF V) (JJ S)) (csoft_CC V) q hq0
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq0
    refine IsZero.of_iso ?_ (Θ V n)
    rcases n with _ | _ | n
    · exact isZero_homology_ΓcE_zero V
    · exact isZero_homology_ΓcE_one V (hzero V h hL 1 (Or.inl rfl))
    · rcases n with _ | n
      · exact absurd rfl hq
      · haveI := isIso_homologyMap_fInf V (n + 3) (by omega)
        exact (hzero V h hL (n + 3) (Or.inr (by omega))).of_iso
          (asIso (HomologicalComplex.homologyMap (fInf V) (n + 3)))
  · refine ⟨fun V hV => haveI := (hplane V hV).1; haveI := (hplane V hV).2.2.2.1
      (Ψ2 V (hplane V hV).2.2.2.2).inv (gV b V), fun V hV => ?_, ?_⟩
    · obtain ⟨hne, -, -, hM, hL⟩ := hplane V hV
      obtain ⟨h⟩ := hV
      have hfun : (fun r : ℚ => r • (Ψ2 V hL).inv (gV b V)) =
          (Ψ2 V hL).inv ∘ fun r : ℚ => r • gV b V :=
        funext fun r => ((Ψ2 V hL).inv.hom.map_smul r (gV b V)).symm
      exact hfun ▸ (ConcreteCategory.bijective_of_isIso (Ψ2 V hL).inv).comp
        (bijective_smul_gV b V h)
    · intro V' V hle hV' hV m hm
      obtain ⟨hne', -, -, hM', hL'⟩ := hplane V' hV'
      obtain ⟨hne, hcV, -, hM, hL⟩ := hplane V hV
      have hm' : m = (νPF hle).app (QQ S) := eq_νPF hle (QQ S) m hm
      subst hm'
      change (HcF S 2).map ((νPF hle).app (QQ S)) ((Ψ2 V' hL').inv (gV b V')) =
        (Ψ2 V hL).inv (gV b V)
      apply (ConcreteCategory.bijective_of_isIso (Ψ2 V hL).hom).1
      rw [Iso.inv_hom_id_apply, ← ConcreteCategory.comp_apply, Ψ2_naturality hle hL hL',
        ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
      exact relCohomologyMap_gV b V hS hle

@[expose] public section

/-- Let `S` be a Hausdorff surface with an oriented atlas modelled on a real normed plane `H`,
and for a finite-dimensional `ℚ`-vector space `E` let `E_S` be the constant sheaf on `S` and
`E_V = E_S|_V`. For every open `V ⊆ S` homeomorphic to `ℝ²`, `H^q_c(V, E_V) = 0` for `q ≠ 2`.
Moreover, for every family of natural isomorphisms `ι_U : H^2_c(U, -) ≅ H^2_c(S, j_{U!} -)`
there are isomorphisms `tr_V : H^2_c(V, E_V) ≅ E`, natural in `E`, such that for opens
`V' ≤ V` homeomorphic to `ℝ²` and the inclusion `m : j_{V'!}(E_{V'}) ⟶ j_{V!}(E_V)` over `E_S`,
the extension map `ι_{V'} ≫ H^2_c(S, m) ≫ ι_V⁻¹` followed by `tr_V` is `tr_{V'}`. Here `Hc Y q`
is the functor whose value on `F` is `MMP.Fourfold.compactSupportCohomology ℚ q F`. -/
@[mmp "lem_mmp_compact_support_oriented_plane_trace"]
public theorem compactSupportCohomology_orientedPlane_trace
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (hH : Module.finrank ℝ H = 2) (S : TopCat.{0}) [T2Space S] [ChartedSpace H S]
    (hS : MMP.IsOrientedAtlas H S) :
    let res : ∀ U : Opens S, TopCat.Sheaf (ModuleCat.{0} ℚ) S ⥤
        TopCat.Sheaf (ModuleCat.{0} ℚ) ((Opens.toTopCat S).obj U) := fun U =>
      haveI := U.isOpenEmbedding.functor_isContinuous
      U.isOpenEmbedding.functor.sheafPushforwardContinuous _ _ _
    let ext : ∀ U : Opens S, TopCat.Sheaf (ModuleCat.{0} ℚ) ((Opens.toTopCat S).obj U) ⥤
        TopCat.Sheaf (ModuleCat.{0} ℚ) S := fun U =>
      haveI := U.isOpenEmbedding.functor_isContinuous
      U.isOpenEmbedding.functor.sheafPullback _ _ _
    let adj : ∀ U : Opens S, ext U ⊣ res U := fun U =>
      haveI := U.isOpenEmbedding.functor_isContinuous
      U.isOpenEmbedding.functor.sheafAdjunctionContinuous _ _ _
    let Hc : ∀ (Y : TopCat.{0}) (_ : ℤ), TopCat.Sheaf (ModuleCat.{0} ℚ) Y ⥤ ModuleCat.{0} ℚ :=
      fun Y q => DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (compactSupportSectionsFunctor ℚ (X := Y)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ q
    let constS : FGModuleCat.{0} ℚ ⥤ TopCat.Sheaf (ModuleCat.{0} ℚ) S :=
      (ModuleCat.isFG.{0} ℚ).ι ⋙ constantSheaf (Opens.grothendieckTopology S) (ModuleCat.{0} ℚ)
    (∀ V : Opens S, Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2)) → ∀ q : ℤ, q ≠ 2 →
      ∀ E : FGModuleCat.{0} ℚ, IsZero ((Hc _ q).obj ((res V).obj (constS.obj E)))) ∧
    ∀ ι : ∀ U : Opens S, Hc ((Opens.toTopCat S).obj U) 2 ≅ ext U ⋙ Hc S 2,
      ∃ tr : ∀ V : Opens S, Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2)) →
          (constS ⋙ res V ⋙ Hc _ 2 ≅ (ModuleCat.isFG.{0} ℚ).ι),
        ∀ (V' V : Opens S) (_ : V' ≤ V) (hV' : Nonempty (V' ≃ₜ EuclideanSpace ℝ (Fin 2)))
          (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2))) (E : FGModuleCat.{0} ℚ)
          (m : (ext V').obj ((res V').obj (constS.obj E)) ⟶
            (ext V).obj ((res V).obj (constS.obj E))),
          m ≫ (adj V).counit.app (constS.obj E) = (adj V').counit.app (constS.obj E) →
            (ι V').hom.app _ ≫ (Hc S 2).map m ≫ (ι V).inv.app _ ≫ (tr V hV).hom.app E =
              (tr V' hV').hom.app E := by
  intro res ext adj Hc constS
  haveI : LocallyCompactSpace S := ChartedSpace.locallyCompactSpace H S
  obtain ⟨hvan, g, hg, hcompat⟩ := key_rat H hH S hS
  obtain ⟨-, hm, ι₀, e₀, -, -, he₀⟩ := compactSupportCohomology_extendByZero ℚ S
  have hadd : ∀ (V : Opens S) (q : ℤ), (constS ⋙ res V ⋙ Hc _ q).Additive := by
    intro V q
    haveI : (constantSheaf (Opens.grothendieckTopology S) (ModuleCat.{0} ℚ)).Additive :=
      (constantSheafAdj (Opens.grothendieckTopology S) (ModuleCat.{0} ℚ)
        isTerminalTop).left_adjoint_additive
    haveI : constS.Additive := ⟨fun {_ _ f g} => by
      change (constantSheaf (Opens.grothendieckTopology S) (ModuleCat.{0} ℚ)).map
        (f.hom + g.hom) = _
      exact Functor.map_add _⟩
    haveI : (res V).Additive := ⟨fun {_ _ _ _} => by apply Sheaf.hom_ext; rfl⟩
    haveI : (Hc ((Opens.toTopCat S).obj V) q).Additive := by dsimp only [Hc]; infer_instance
    infer_instance
  refine ⟨fun V hV q hq E => ?_, fun ι => ?_⟩
  · haveI := hadd V q
    refine isZero_obj (constS ⋙ res V ⋙ Hc _ q) ?_ E
    exact IsZero.of_iso (hvan V hV q hq) ((ι₀ V q).app _)
  · let QS := constS.obj one
    -- the generators of `F_V(ℚ) = H^2_c(V, ℚ)`
    let x₀ : ∀ V : Opens S, Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2)) →
        (constS ⋙ res V ⋙ Hc _ 2).obj one := fun V hV => (ι V).inv.app ((res V).obj QS) (g V hV)
    have hx₀ : ∀ V hV, Function.Bijective fun r : ℚ => r • x₀ V hV := by
      intro V hV
      have h1 : (fun r : ℚ => r • x₀ V hV) =
          (ι V).inv.app ((res V).obj QS) ∘ fun r : ℚ => r • g V hV := by
        funext r
        simp only [x₀, Function.comp_apply, map_smul]
      rw [h1]
      exact (ConcreteCategory.bijective_of_isIso ((ι V).inv.app ((res V).obj QS))).comp (hg V hV)
    refine ⟨fun V hV => haveI := hadd V 2; (isoOfGen (constS ⋙ res V ⋙ Hc _ 2) (x₀ V hV)
      (hx₀ V hV)).symm, fun V' V hle hV' hV E m hmE => ?_⟩
    haveI := hadd V 2
    haveI := hadd V' 2
    -- the extension maps, as a natural transformation
    let θ : res V' ⋙ Hc _ 2 ⟶ res V ⋙ Hc _ 2 :=
      Functor.whiskerLeft (res V') (ι V').hom ≫ Functor.whiskerLeft (res V') (ι₀ V' 2).inv ≫
        e₀ 2 hle ≫ Functor.whiskerLeft (res V) (ι₀ V 2).hom ≫
        Functor.whiskerLeft (res V) (ι V).inv
    let η : constS ⋙ res V' ⋙ Hc _ 2 ⟶ constS ⋙ res V ⋙ Hc _ 2 := Functor.whiskerLeft constS θ
    have hη : ∀ (F : TopCat.Sheaf (ModuleCat.{0} ℚ) S)
        (m' : (ext V').obj ((res V').obj F) ⟶ (ext V).obj ((res V).obj F)),
        m' ≫ (adj V).counit.app F = (adj V').counit.app F →
          θ.app F = (ι V').hom.app _ ≫ (Hc S 2).map m' ≫ (ι V).inv.app _ := by
      intro F m' hm'
      simp only [θ, NatTrans.comp_app, Functor.whiskerLeft_app]
      rw [he₀ 2 V' V hle F m' hm']
      simp only [Category.assoc]
      erw [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_assoc]
    obtain ⟨m₁, hm₁, -⟩ := hm QS V' V hle
    have key := isoOfGen_comp (constS ⋙ res V' ⋙ Hc _ 2) (x₀ V' hV') (x₀ V hV) (hx₀ V' hV')
      (hx₀ V hV) η ?_ E
    · beta_reduce
      rw [Iso.symm_hom, Iso.symm_hom, ← key,
        show η.app E = θ.app (constS.obj E) from rfl, hη _ m hmE]
      simp only [Category.assoc]
    · change θ.app QS (x₀ V' hV') = x₀ V hV
      rw [hη QS m₁ hm₁]
      simp only [x₀, ModuleCat.comp_apply]
      congr 1
      have h1 : (ι V').hom.app ((res V').obj QS) ((ι V').inv.app ((res V').obj QS) (g V' hV')) =
          g V' hV' := by
        rw [← ModuleCat.comp_apply, Iso.inv_hom_id_app]
        rfl
      rw [h1]
      exact hcompat V' V hle hV' hV m₁ hm₁

end

end MMP.Fourfold
