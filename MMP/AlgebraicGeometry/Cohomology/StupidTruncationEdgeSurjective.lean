module

public import MMP.AlgebraicGeometry.Cohomology.HodgeDegenerationSummand
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.StupidTruncationNaturality
public import StacksFrontier.Homology.DerivedCategory.Bridge.Basic

/-!
# The edge map of the stupid filtration is surjective under `E₁`-degeneration

Let `π : Y ⟶ T` be a morphism of schemes with `Γ(T, ⊤)` a field, and `X` a complex of sheaves of
`π⁻¹𝒪_T`-modules. The projection `σ^{≥0}X ⟶ X⁰` of the stupid truncation onto its degree-zero
term induces the edge map `ℍ^k(σ^{≥0}X) ⟶ H^k(X⁰)` of the Hodge-to-de Rham spectral sequence.
The triangle `σ^{≥1}X ⟶ σ^{≥0}X ⟶ X⁰ ⟶` gives an exact sequence
`ℍ^k(σ^{≥1}X) ⟶ ℍ^k(σ^{≥0}X) ⟶ H^k(X⁰)`, so the edge map is onto as soon as
`dim ℍ^k(σ^{≥0}X) = dim ℍ^k(σ^{≥1}X) + dim H^k(X⁰)`. Since both
`dim ℍ^k(σ^{≥1}X) ≤ ∑_{0 < p ≤ k} dim H^{k-p}(Xᵖ)` and the analogous bound hold in general,
`E₁`-degeneration `dim ℍ^k(σ^{≥0}X) = ∑_{p ≤ k} dim H^{k-p}(Xᵖ)` forces this equality.

If `φ : K' ⟶ K` is a quasi-isomorphism of complexes concentrated in degrees `≥ 0` and the
spectral sequence of `K` degenerates at `E₁`, then the edge map of `K` precomposed with the
isomorphism `ℍ^k(K') ≅ ℍ^k(K)` is the edge map of `K'` followed by `H^k(φ⁰)`, so
`H^k(φ⁰) : H^k(K'⁰) ⟶ H^k(K⁰)` is surjective.

## Main results

* `MMP.LcBpf.surjective_hypFunctor_map_truncGEπ0_of_finrank_eq_sum`: the edge map
  `ℍ^k(σ^{≥0}X) ⟶ H^k(X⁰)` is surjective under `E₁`-degeneration.
* `MMP.LcBpf.surjective_hypFunctor_map_singleFunctor_f_zero_of_quasiIso`,
  `MMP.LcBpf.surjective_rightDerived_map_f_zero_of_quasiIso`: for a quasi-isomorphism `φ : K' ⟶ K`
  of complexes indexed by `ℕ` with `K` degenerate at `E₁`, the map `H^k(φ⁰)` is surjective.
* `MMP.LcBpf.surjective_derivedGlobalSectionsOver_map_of_quasiIso`: the same statement for the
  cohomology of `𝒪_V`-modules on a scheme `V` over a field, when the degree-zero terms are
  restrictions of scalars of `𝒪_V`-modules.
* `MMP.LcBpf.surjective_map_iff_of_square`,
  `MMP.LcBpf.surjective_derivedGlobalSectionsOver_map_iff_restrictScalars`: transport of
  surjectivity of a map on cohomology along isomorphisms and changes of the sheaf of rings.

## References

* [P. Deligne, *Théorie de Hodge II*][Deligne1971]
* [O. Fujino, *Fundamental theorems for the log minimal model program*][Fujino2011], Theorem 5.1
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public section

namespace MMP.LcBpf

universe v

section ChangeOfRing

open CategoryTheory TopologicalSpace Stacks.Cohomology.ModuleComparison

/-- Surjectivity of a linear map is invariant under isomorphisms of arrows. -/
theorem surjective_iff_of_square {k : Type} [Ring k] {M₁ M₂ N₁ N₂ : ModuleCat.{0} k}
    (a : M₁ ⟶ M₂) (b : N₁ ⟶ N₂) (e₁ : M₁ ≅ N₁) (e₂ : M₂ ≅ N₂) (w : a ≫ e₂.hom = e₁.hom ≫ b) :
    Function.Surjective a.hom ↔ Function.Surjective b.hom :=
  (MorphismProperty.surjective _).arrow_mk_iso_iff (Arrow.isoMk e₁ e₂ w.symm)

/-- Surjectivity of a morphism of abelian groups is invariant under isomorphisms of arrows. -/
theorem surjective_iff_of_arrowIso_addCommGrp {A B A' B' : AddCommGrpCat.{v}}
    (a : A ⟶ B) (b : A' ⟶ B') (e₁ : A ≅ A') (e₂ : B ≅ B') (w : a ≫ e₂.hom = e₁.hom ≫ b) :
    Function.Surjective a.hom ↔ Function.Surjective b.hom :=
  (MorphismProperty.surjective _).arrow_mk_iso_iff (Arrow.isoMk e₁ e₂ w.symm)

/-- Surjectivity of the image of a morphism under a functor to modules is invariant under
isomorphisms of arrows. -/
theorem surjective_map_iff_of_square {k : Type} [Ring k] {C : Type*} [Category C]
    (G : C ⥤ ModuleCat.{0} k) {A B A' B' : C} (a : A ⟶ B) (b : A' ⟶ B') (e₁ : A ≅ A')
    (e₂ : B ≅ B') (w : a ≫ e₂.hom = e₁.hom ≫ b) :
    Function.Surjective (G.map a).hom ↔ Function.Surjective (G.map b).hom :=
  surjective_iff_of_square _ _ (G.mapIso e₁) (G.mapIso e₂) (by
    simp only [Functor.mapIso_hom, ← G.map_comp, w])

/-- **Cohomology of a map is unchanged by restricting the sheaf of rings** ([Stacks, Tag 03FD]).
For `ψ : R ⟶ R'` and a map `φ` of sheaves of `R'`-modules, `Hⁿ(U, φ)` computed in `Mod(R)` after
restricting scalars is surjective exactly when `Hⁿ(U, φ)` computed in `Mod(R')` is. -/
theorem surjective_hfunctor_map_restrictScalars_iff {X : Type v} [TopologicalSpace X]
    {R R' : Sheaf (Opens.grothendieckTopology X) RingCat.{v}} (ψ : R ⟶ R') (U : Opens X) (n : ℕ)
    {F G : SheafOfModules.{v} R'} (φ : F ⟶ G) :
    Function.Surjective ((Hfunctor R U n).map ((SheafOfModules.restrictScalars.{v} ψ).map φ)).hom ↔
      Function.Surjective ((Hfunctor R' U n).map φ).hom := by
  have n₁ := (underlyingSectionsIso R U n).hom.naturality
    ((SheafOfModules.restrictScalars.{v} ψ).map φ)
  have n₂ := (underlyingSectionsIso R' U n).hom.naturality φ
  exact (surjective_iff_of_arrowIso_addCommGrp _ _ ((underlyingSectionsIso R U n).app _)
    ((underlyingSectionsIso R U n).app _) n₁).trans
    (surjective_iff_of_arrowIso_addCommGrp _ _ ((underlyingSectionsIso R' U n).app _)
    ((underlyingSectionsIso R' U n).app _) n₂).symm

/-- **Right derived functors to modules, read in abelian groups.** For an additive
`Γ : C ⥤ Mod(k)`, the map `Rⁿ Γ(φ)` is surjective exactly when `Rⁿ(Γ ⋙ forget)(φ)` is: the
forgetful functor is exact, so it commutes with right derived functors. -/
theorem surjective_rightDerived_map_iff_forget₂ {C : Type*} [Category C] [Abelian C]
    [HasInjectiveResolutions C] {k : Type v} [Ring k] (Γ : C ⥤ ModuleCat.{v} k) [Γ.Additive]
    (n : ℕ) {F G : C} (φ : F ⟶ G) :
    Function.Surjective ((Γ.rightDerived n).map φ).hom ↔
      Function.Surjective
        (((Γ ⋙ forget₂ (ModuleCat.{v} k) AddCommGrpCat.{v}).rightDerived n).map φ).hom := by
  have e := Stacks.Cohomology.DerivedForget.rightDerivedCompIso Γ
    (forget₂ (ModuleCat.{v} k) AddCommGrpCat.{v}) n
  exact surjective_iff_of_arrowIso_addCommGrp _ _ (e.app F) (e.app G) (e.hom.naturality φ)

end ChangeOfRing

section DerivedGlobalSections

open CategoryTheory AlgebraicGeometry

/-- **A right derived functor on cohomology of a map, through a lift to resolutions.** Let `R` be
a functor on derived categories with a comparison `β : Q ∘ F ⟶ R ∘ Q` invertible at the complexes
`I` and `J`. If `fK : K ⟶ I`, `fL : L ⟶ J` are quasi-isomorphisms and `g : I ⟶ J` in the homotopy
category satisfies `fK ≫ g = c ≫ fL`, then `Hⁿ(R(c))` is surjective exactly when `Hⁿ(F(g))` is. -/
theorem surjective_homology_map_iff_of_lift {A : Type*} [Category A] [Abelian A]
    {k : Type} [Ring k] [HasDerivedCategory A] [HasDerivedCategory (ModuleCat.{0} k)]
    (F : A ⥤ ModuleCat.{0} k) [F.Additive]
    (R : DerivedCategory A ⥤ DerivedCategory (ModuleCat.{0} k))
    (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    {K L I J : CochainComplex A ℤ} (c : K ⟶ L) (fK : K ⟶ I) (fL : L ⟶ J) [QuasiIso fK]
    [QuasiIso fL] [IsIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))]
    [IsIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J))]
    (g : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I ⟶
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J)
    (hg : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map fK ≫ g =
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (c ≫ fL)) (n : ℤ) :
    Function.Surjective ((DerivedCategory.homologyFunctor (ModuleCat.{0} k) n).map
        (R.map (DerivedCategory.Q.map c))).hom ↔
      Function.Surjective ((HomotopyCategory.homologyFunctor (ModuleCat.{0} k)
        (ComplexShape.up ℤ) n).map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map g)).hom := by
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let e := DerivedCategory.quotientCompQhIso A
  -- `Q c` is `Qh g` up to the isomorphisms `Q fK`, `Q fL`
  have s1 : DerivedCategory.Q.map c ≫ (asIso (DerivedCategory.Q.map fL) ≪≫ (e.app J).symm).hom =
      (asIso (DerivedCategory.Q.map fK) ≪≫ (e.app I).symm).hom ≫ DerivedCategory.Qh.map g := by
    have nK := e.inv.naturality fK
    have nc := e.inv.naturality (c ≫ fL)
    simp only [Functor.comp_map] at nK nc
    simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, Iso.app_inv, Category.assoc]
    rw [← Functor.map_comp_assoc, nc, reassoc_of% nK, ← Functor.map_comp, hg]
  have t1 := surjective_map_iff_of_square (R ⋙ DerivedCategory.homologyFunctor _ n) _ _ _ _ s1
  -- `R (Qh g)` is `Qh (F g)` up to `β`
  have s2 : R.map (DerivedCategory.Qh.map g) ≫ (asIso (β.app (q.obj J))).inv =
      (asIso (β.app (q.obj I))).inv ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map g) := by
    have := β.naturality g
    simp only [Functor.comp_map] at this
    rw [asIso_inv, asIso_inv, IsIso.eq_inv_comp, ← Category.assoc, ← this, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  have t2 := surjective_map_iff_of_square (DerivedCategory.homologyFunctor _ n) _ _
    (asIso (β.app (q.obj I))).symm (asIso (β.app (q.obj J))).symm s2
  -- homology of `Qh` is homotopy-category homology
  have s3 := ((DerivedCategory.homologyFunctorFactorsh (ModuleCat.{0} k) n).hom.naturality
    ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map g))
  have t3 := surjective_iff_of_square _ _
    ((DerivedCategory.homologyFunctorFactorsh (ModuleCat.{0} k) n).app _)
    ((DerivedCategory.homologyFunctorFactorsh (ModuleCat.{0} k) n).app _) s3
  simp only [Functor.comp_map] at t1 t3
  exact t1.trans (t2.trans t3)

/-- **Derived global sections on a map of sheaves are classical cohomology.** For a map `φ` of
`𝒪_V`-modules, `Hⁿ(V, φ)` computed by the unbounded `derivedGlobalSectionsOver f` is surjective
exactly when `Rⁿ Γ(φ)` is, the classical right derived functor of `globalSectionsOver f`: both are
computed on the chosen injective resolutions, which are K-injective. -/
theorem surjective_derivedGlobalSectionsOver_map_iff {k : Type} [Field k] {V : Scheme.{0}}
    (f : V ⟶ Spec (.of k)) [HasDerivedCategory V.Modules] [HasDerivedCategory (ModuleCat.{0} k)]
    {F G : V.Modules} (φ : F ⟶ G) (n : ℕ) :
    Function.Surjective ((DerivedCategory.homologyFunctor (ModuleCat.{0} k) n).map
        ((derivedGlobalSectionsOver f).map
          ((DerivedCategory.singleFunctor V.Modules 0).map φ))).hom ↔
      Function.Surjective (((globalSectionsOver f).rightDerived n).map φ).hom := by
  let c := (CochainComplex.singleFunctor V.Modules 0).map φ
  have hres : ∀ K : CochainComplex V.Modules ℤ, ∃ (J : CochainComplex V.Modules ℤ) (q : K ⟶ J),
      J.IsKInjective ∧ QuasiIso q := Stacks.Perfect.CechAugmentation.exists_isKInjective_quasiIso
  have iF := Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective
    (globalSectionsOver f) (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f) hres
    (injectiveResolution F).cochainComplex inferInstance
  have iG := Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective
    (globalSectionsOver f) (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f) hres
    (injectiveResolution G).cochainComplex inferInstance
  have hg := (Stacks.DerivedIndexing.resUnit (C := V.Modules)).naturality φ
  have t1 := surjective_homology_map_iff_of_lift (globalSectionsOver f)
    (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f) c
    (injectiveResolution F).ι' (injectiveResolution G).ι'
    (Stacks.DerivedIndexing.resH.map φ) (by
      rw [Functor.map_comp]
      exact hg.symm) (n : ℤ)
  -- the single complex
  have s0 := (DerivedCategory.singleFunctorIsoCompQ V.Modules 0).hom.naturality φ
  have t0 := surjective_map_iff_of_square (derivedGlobalSectionsOver f ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{0} k) n) _ _
    ((DerivedCategory.singleFunctorIsoCompQ V.Modules 0).app F)
    ((DerivedCategory.singleFunctorIsoCompQ V.Modules 0).app G) s0
  -- classical derived functors through the chosen resolutions
  have e := Stacks.DerivedIndexing.rightDerivedIsoRes (globalSectionsOver f) n
  have t2 := surjective_iff_of_square _ _ (e.app F) (e.app G) (e.hom.naturality φ)
  simp only [Functor.comp_map] at t0 t2
  exact t0.trans (t1.trans t2.symm)

/-- **The comparison of the two cohomologies of a map.** For a map `φ` of `𝒪_V`-modules and any
`ψ : π⁻¹𝒪_{Spec k} ⟶ 𝒪_V`, `Hⁿ(V, φ)` computed by `derivedGlobalSectionsOver f` is surjective
exactly when `Hⁿ(V, φ)` computed in sheaves of `π⁻¹𝒪`-modules, after restricting scalars along `ψ`,
is ([Stacks, Tag 03FD]). -/
theorem surjective_derivedGlobalSectionsOver_map_iff_restrictScalars {k : Type} [Field k]
    {V : Scheme.{0}} (f : V ⟶ Spec (.of k)) [HasDerivedCategory V.Modules]
    [HasDerivedCategory (ModuleCat.{0} k)]
    (ψ : MMP.FourfoldProofs.FractionalLogComplexProof.invRing f ⟶ V.ringCatSheaf)
    {F G : V.Modules} (φ : F ⟶ G) (n : ℕ) :
    Function.Surjective ((DerivedCategory.homologyFunctor (ModuleCat.{0} k) n).map
        ((derivedGlobalSectionsOver f).map
          ((DerivedCategory.singleFunctor V.Modules 0).map φ))).hom ↔
      Function.Surjective
        (((MMP.FourfoldProofs.FractionalLogComplexProof.globalSections f).rightDerived n).map
          ((SheafOfModules.restrictScalars.{0} ψ).map φ)).hom :=
  (surjective_derivedGlobalSectionsOver_map_iff f φ n).trans
    ((surjective_rightDerived_map_iff_forget₂ (globalSectionsOver f) n φ).trans
      ((surjective_hfunctor_map_restrictScalars_iff ψ ⊤ n φ).symm.trans
        (surjective_rightDerived_map_iff_forget₂
          (MMP.FourfoldProofs.FractionalLogComplexProof.globalSections f) n
          ((SheafOfModules.restrictScalars.{0} ψ).map φ)).symm))

end DerivedGlobalSections

section EdgeMap

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MMP.FourfoldProofs.FractionalLogComplexProof MMP.Mori.Divisor.LogSpreadingProof
  MMP.FourfoldProofs.LogDegenerationProof StacksDraft.StupidTruncation HomologicalComplex ComplexShape

attribute [local instance] HasDerivedCategory.standard

variable {Y T : Scheme.{0}} (h : Y ⟶ T)

/-- The projection `σ^{≥0}X ⟶ X⁰` onto the degree-zero term. -/
noncomputable def truncGEπ0 (X : CochainComplex (SheafOfModules.{0} (invRing h)) ℤ) :
    truncGE h X 0 ⟶ single0 h (X.X 0) :=
  ObjectProperty.homMk (stupidTruncGEπ X 0)

/-- The inclusion `σ^{≥1}X ⟶ σ^{≥0}X`. -/
noncomputable def truncGEι01 (X : CochainComplex (SheafOfModules.{0} (invRing h)) ℤ) :
    truncGE h X (0 + 1) ⟶ truncGE h X 0 :=
  ObjectProperty.homMk (stupidTruncGEMapLE X (show (0:ℤ) ≤ 0 + 1 by omega))

/-- The triangle `σ^{≥1}X ⟶ σ^{≥0}X ⟶ X⁰ ⟶` of the bounded below derived category, with the
projection to the degree-zero term as its second morphism, is distinguished. -/
theorem distinguished_truncGE_zero (X : CochainComplex (SheafOfModules.{0} (invRing h)) ℤ) :
    ∃ (δ : DerivedCategory.Plus.Q.obj (single0 h (X.X 0)) ⟶
        (DerivedCategory.Plus.Q.obj (truncGE h X (0 + 1)))⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk (DerivedCategory.Plus.Q.map (truncGEι01 h X))
        (DerivedCategory.Plus.Q.map (truncGEπ0 h X)) δ ∈ distTriang _ := by
  obtain ⟨Z, g, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle
    (DerivedCategory.Plus.Q.map (truncGEι01 h X))
  have h₁ := DerivedCategory.Plus.ι.map_distinguished _ hT
  have h₂ := stupidTruncGESplitTriangleQ_distinguished X 0
  obtain ⟨e, he₁, he₂⟩ := Pretriangulated.exists_iso_of_arrow_iso _ _ h₁ h₂ (Iso.refl _)
  let e₃ : Z ≅ DerivedCategory.Plus.Q.obj (single0 h (X.X 0)) :=
    (ObjectProperty.fullyFaithfulι _).preimageIso (Pretriangulated.Triangle.π₃.mapIso e)
  have hg : g ≫ e₃.hom = DerivedCategory.Plus.Q.map (truncGEπ0 h X) := by
    apply (ObjectProperty.fullyFaithfulι _).map_injective
    have c : DerivedCategory.Plus.ι.map g ≫ e.hom.hom₃ =
        𝟙 _ ≫ DerivedCategory.Q.map (stupidTruncGEπ X 0) := by
      have := e.hom.comm₂
      rwa [he₂] at this
    rw [Category.id_comp] at c
    rw [Functor.map_comp]
    exact (congrArg (_ ≫ ·) ((ObjectProperty.fullyFaithfulι _).map_preimage _)).trans c
  refine ⟨e₃.inv ≫ δ, Pretriangulated.isomorphic_distinguished _ hT _ ?_⟩
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e₃.symm ?_ ?_ ?_
  · simp [truncGEι01]
  · simp [← hg]
  · simp

/-- **The equality case of the dimension bound in an exact sequence.** If `A ⟶ B ⟶ C` is exact
over a field with finite-dimensional terms and `dim B = dim A + dim C`, then `B ⟶ C` is
surjective. -/
theorem surjective_of_finrank_eq_add_of_exact {k : Type*} [Field k] {A B C : Type*}
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    (f : A →ₗ[k] B) (g : B →ₗ[k] C) (hfg : Function.Exact f g)
    (hA : Module.Finite k A) (hB : Module.Finite k B) (hC : Module.Finite k C)
    (hEq : Module.finrank k B = Module.finrank k A + Module.finrank k C) :
    Function.Surjective g := by
  have e := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.exact_iff.1 hfg] at e
  have h1 := LinearMap.finrank_range_le f
  have h2 := Submodule.finrank_le (LinearMap.range g)
  exact LinearMap.range_eq_top.1 (Submodule.eq_top_of_finrank_eq (by omega))

/-- If `dim ℍ^k(σ^{≥0}X) = dim ℍ^k(σ^{≥1}X) + dim H^k(X⁰)`, the edge map
`ℍ^k(σ^{≥0}X) ⟶ H^k(X⁰)` is surjective. -/
theorem surjective_hypFunctor_map_truncGEπ0 (hT : IsField Γ(T, ⊤))
    (X : CochainComplex (SheafOfModules.{0} (invRing h)) ℤ) (k : ℤ)
    (iA : Module.Finite Γ(T, ⊤) (hyp h (DerivedCategory.Plus.Q.obj (truncGE h X (0 + 1))) k))
    (iB : Module.Finite Γ(T, ⊤) (hyp h (DerivedCategory.Plus.Q.obj (truncGE h X 0)) k))
    (iC : Module.Finite Γ(T, ⊤) (hyp h (DerivedCategory.Plus.Q.obj (single0 h (X.X 0))) k))
    (heq : Module.finrank Γ(T, ⊤) (hyp h (DerivedCategory.Plus.Q.obj (truncGE h X 0)) k) =
      Module.finrank Γ(T, ⊤) (hyp h (DerivedCategory.Plus.Q.obj (truncGE h X (0 + 1))) k) +
        Module.finrank Γ(T, ⊤) (hyp h (DerivedCategory.Plus.Q.obj (single0 h (X.X 0))) k)) :
    Function.Surjective
      ((hypFunctor h k).map (DerivedCategory.Plus.Q.map (truncGEπ0 h X))).hom := by
  let := hT.toField
  let := Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus (globalSections h)
  have := CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus (globalSections h)
  obtain ⟨δ, hTr⟩ := distinguished_truncGE_zero h X
  let G := (globalSections h).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{0} ((invRing h).obj.obj (op ⊤))) k
  have hex := (ShortComplex.moduleCat_exact_iff _).1 (G.map_distinguished_exact _ hTr)
  have hz : G.map (Pretriangulated.Triangle.mk (DerivedCategory.Plus.Q.map (truncGEι01 h X))
      (DerivedCategory.Plus.Q.map (truncGEπ0 h X)) δ).mor₁ ≫
      G.map (Pretriangulated.Triangle.mk (DerivedCategory.Plus.Q.map (truncGEι01 h X))
        (DerivedCategory.Plus.Q.map (truncGEπ0 h X)) δ).mor₂ = 0 := by
    rw [← Functor.map_comp, Pretriangulated.comp_distTriang_mor_zero₁₂ _ hTr, Functor.map_zero]
  let f := ((ModuleCat.restrictScalars.{0} (invRingUnit h)).map
    (G.map (Pretriangulated.Triangle.mk (DerivedCategory.Plus.Q.map (truncGEι01 h X))
      (DerivedCategory.Plus.Q.map (truncGEπ0 h X)) δ).mor₁)).hom
  let g := ((ModuleCat.restrictScalars.{0} (invRingUnit h)).map
    (G.map (Pretriangulated.Triangle.mk (DerivedCategory.Plus.Q.map (truncGEι01 h X))
      (DerivedCategory.Plus.Q.map (truncGEπ0 h X)) δ).mor₂)).hom
  have hfg : Function.Exact f g := fun y => by
    refine ⟨fun hy => hex y hy, ?_⟩
    rintro ⟨x, rfl⟩
    exact congrArg (fun φ => φ.hom x) hz
  exact surjective_of_finrank_eq_add_of_exact (k := Γ(T, ⊤))
    (A := hyp h (DerivedCategory.Plus.Q.obj (truncGE h X (0 + 1))) k)
    (B := hyp h (DerivedCategory.Plus.Q.obj (truncGE h X 0)) k)
    (C := hyp h (DerivedCategory.Plus.Q.obj (single0 h (X.X 0))) k) f g hfg iA iB iC heq

/-- `Q (single0 M) ≅ (singleFunctor 0).obj M` in the bounded below derived category. -/
noncomputable def single0Iso (M : SheafOfModules.{0} (invRing h)) :
    DerivedCategory.Plus.Q.obj (single0 h M) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj M :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M).symm

/-- **Edge-map surjectivity from `E₁`-degeneration.** If
`dim ℍ^k(σ^{≥0}X) = ∑_{q ≤ k} dim H^q(X^{k-q})`, then the edge map `ℍ^k(σ^{≥0}X) ⟶ H^k(X⁰)`,
induced by the projection to the degree-zero term, is surjective. -/
theorem surjective_hypFunctor_map_truncGEπ0_of_finrank_eq_sum (hT : IsField Γ(T, ⊤))
    (X : CochainComplex (SheafOfModules.{0} (invRing h)) ℤ) (k : ℕ)
    (hfin : ∀ q : ℕ, q < k + 1 →
      Module.Finite Γ(T, ⊤)
        (hyp h ((DerivedCategory.Plus.singleFunctor _ 0).obj (X.X (k - q))) q))
    (heq : Module.finrank Γ(T, ⊤) (hyp h (DerivedCategory.Plus.Q.obj (truncGE h X 0)) k) =
      ∑ q ∈ Finset.range (k + 1), Module.finrank Γ(T, ⊤)
          (hyp h ((DerivedCategory.Plus.singleFunctor _ 0).obj (X.X (k - q))) q)) :
    Function.Surjective
      ((hypFunctor h k).map (DerivedCategory.Plus.Q.map (truncGEπ0 h X))).hom := by
  obtain ⟨f₀, r₀⟩ := finite_and_finrank_hyp_truncGE_le h hT X k (k + 1) hfin
  obtain ⟨f₁, r₁⟩ := finite_and_finrank_hyp_truncGE_le h hT X k k fun q hq => hfin q (by omega)
  have e₀ : (k : ℤ) + 1 - ((k + 1 : ℕ) : ℤ) = 0 := by push_cast; ring
  have e₁ : (k : ℤ) + 1 - (k : ℤ) = 0 + 1 := by ring
  rw [e₀] at f₀ r₀
  rw [e₁] at f₁ r₁
  have hk0 : (k : ℤ) - (k : ℕ) = 0 := by ring
  have fC' := hfin k (by omega)
  rw [hk0] at fC'
  have iC := finite_and_finrank_hyp_eq_of_iso h (single0Iso h (X.X 0)) (k : ℤ)
  have fC : Module.Finite Γ(T, ⊤) (hyp h (DerivedCategory.Plus.Q.obj (single0 h (X.X 0))) k) :=
    iC.1.2 fC'
  obtain ⟨δ, hTr⟩ := distinguished_truncGE_zero h X
  obtain ⟨-, rT⟩ := @finite_and_finrank_hyp_le_of_distinguished _ _ h hT _ hTr k f₁ fC
  refine surjective_hypFunctor_map_truncGEπ0 h hT X k f₁ f₀ fC ?_
  have hs := Finset.sum_range_succ (fun q => Module.finrank Γ(T, ⊤)
    (hyp h ((DerivedCategory.Plus.singleFunctor _ 0).obj (X.X (k - q))) q)) k
  have hb : Module.finrank Γ(T, ⊤)
      (hyp h ((DerivedCategory.Plus.singleFunctor _ 0).obj (X.X ((k : ℤ) - (k : ℕ)))) (k : ℕ)) =
      Module.finrank Γ(T, ⊤) (hyp h (DerivedCategory.Plus.Q.obj (single0 h (X.X 0))) k) := by
    rw [hk0]
    exact iC.2.symm
  have rT' : Module.finrank Γ(T, ⊤) (hyp h (DerivedCategory.Plus.Q.obj (truncGE h X 0)) k) ≤
      Module.finrank Γ(T, ⊤) (hyp h (DerivedCategory.Plus.Q.obj (truncGE h X (0 + 1))) k) +
        Module.finrank Γ(T, ⊤) (hyp h (DerivedCategory.Plus.Q.obj (single0 h (X.X 0))) k) := rT
  clear rT
  omega

/-- On a sheaf placed in degree zero, the hypercohomology `hyp` of a map is the classical right
derived functor of global sections: `ℍʲ(φ[0])` is surjective exactly when `Rʲ Γ(φ)` is. -/
theorem surjective_hypFunctor_map_singleFunctor_iff {M N : SheafOfModules.{0} (invRing h)}
    (φ : M ⟶ N) (j : ℕ) :
    Function.Surjective
        ((hypFunctor h j).map ((DerivedCategory.Plus.singleFunctor _ 0).map φ)).hom ↔
      Function.Surjective (((globalSections h).rightDerived j).map φ).hom := by
  have e := Stacks.DerivedIndexing.rightDerivedIso (globalSections h) j
  exact (Iff.rfl : Function.Surjective
      ((hypFunctor h j).map ((DerivedCategory.Plus.singleFunctor _ 0).map φ)).hom ↔
      Function.Surjective (((globalSections h).rightDerivedPlus j).map φ).hom).trans
    (surjective_iff_of_square _ _ (e.app M) (e.app N) (e.hom.naturality φ)).symm

/-- The complex `K` indexed by `ℕ`, extended by zero to `ℤ`, as a bounded below complex. -/
noncomputable abbrev extendPlus (K : CochainComplex (SheafOfModules.{0} (invRing h)) ℕ) :
    CochainComplex.Plus (SheafOfModules.{0} (invRing h)) :=
  ⟨K.extend ComplexShape.embeddingUpNat, 0,
    CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩

/-- For a complex indexed by `ℕ`, the term `H^j` of `E₁` in degree `n` of its extension to `ℤ`
is `H^j(Kⁿ)`. -/
theorem finite_and_finrank_hyp_singleFunctor_extend_X
    (K : CochainComplex (SheafOfModules.{0} (invRing h)) ℕ) (n : ℕ) (j : ℤ) :
    (Module.Finite Γ(T, ⊤) (hyp h ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((K.extend ComplexShape.embeddingUpNat).X (n : ℤ))) j) ↔
      Module.Finite Γ(T, ⊤) (Hc h (single0 h (K.X n)) j)) ∧
    Module.finrank Γ(T, ⊤) (hyp h ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((K.extend ComplexShape.embeddingUpNat).X (n : ℤ))) j) =
      Module.finrank Γ(T, ⊤) (Hc h (single0 h (K.X n)) j) :=
  finite_and_finrank_hyp_eq_of_iso h ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
    (K.extendXIso ComplexShape.embeddingUpNat rfl) ≪≫ (single0Iso h (K.X n)).symm) j

/-- **The edge map of a complex indexed by `ℕ` is surjective under `E₁`-degeneration.** If
`dim ℍ^k(K) = ∑_{p ≤ k} dim H^{k-p}(Kᵖ)` with finite-dimensional terms, then the edge map
`ℍ^k(K) ⟶ H^k(K⁰)`, read on `σ^{≥0}` of the extension of `K` to `ℤ`, is surjective. -/
theorem surjective_hypFunctor_map_truncGEπ0_extend_of_finrank_eq_sum (hT : IsField Γ(T, ⊤))
    (K : CochainComplex (SheafOfModules.{0} (invRing h)) ℕ) (k : ℕ)
    (hfin : ∀ p : ℕ, p < k + 1 →
      Module.Finite Γ(T, ⊤) (Hc h (single0 h (K.X p)) ((k - p : ℕ) : ℤ)))
    (heq : Module.finrank Γ(T, ⊤) (Hc h (extendPlus h K) k) =
      ∑ p ∈ Finset.range (k + 1),
        Module.finrank Γ(T, ⊤) (Hc h (single0 h (K.X p)) ((k - p : ℕ) : ℤ))) :
    Function.Surjective ((hypFunctor h k).map (DerivedCategory.Plus.Q.map
      (truncGEπ0 h (K.extend ComplexShape.embeddingUpNat)))).hom := by
  set X := K.extend ComplexShape.embeddingUpNat
  have hidx : ∀ q : ℕ, q < k + 1 → (k : ℤ) - q = ((k - q : ℕ) : ℤ) := fun q hq => by omega
  have hX := finite_and_finrank_hyp_singleFunctor_extend_X h K
  refine surjective_hypFunctor_map_truncGEπ0_of_finrank_eq_sum h hT X k (fun q hq => ?_) ?_
  · rw [hidx q hq]
    refine (hX (k - q) q).1.2 ?_
    have := hfin (k - q) (by omega)
    rwa [Nat.sub_sub_self (by omega)] at this
  · have hI := isIso_ιStupidTrunc X (embeddingUpIntGE 0)
    have e : DerivedCategory.Plus.Q.obj (truncGE h X 0) ≅
        DerivedCategory.Plus.Q.obj (extendPlus h K) :=
      DerivedCategory.Plus.Q.mapIso ((ObjectProperty.fullyFaithfulι _).preimageIso
        (@asIso _ _ _ _ (ιStupidTrunc X (embeddingUpIntGE 0)) hI))
    rw [(finite_and_finrank_hyp_eq_of_iso h e (k : ℤ)).2, hyp_Q_obj, heq,
      ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have hq := Finset.mem_range.1 hq
    rw [hidx q hq, (hX (k - q) q).2, show k + 1 - 1 - q = k - q by omega,
      Nat.sub_sub_self (by omega)]

/-- If `a` is an isomorphism and `a ≫ π = π' ≫ b`, then `F.map b` is surjective whenever
`F.map π` is. -/
theorem surjective_map_of_comp_eq_of_isIso {k : Type} [Ring k] {C : Type*} [Category C]
    (F : C ⥤ ModuleCat.{0} k) {W X Y Z : C} (a : W ⟶ X) (π : X ⟶ Z) (π' : W ⟶ Y) (b : Y ⟶ Z)
    [IsIso a] (sq : F.map a ≫ F.map π = F.map π' ≫ F.map b)
    (hπ : Function.Surjective (F.map π).hom) : Function.Surjective (F.map b).hom := by
  have hs : Function.Surjective (F.map a ≫ F.map π).hom := by
    rw [ModuleCat.hom_comp, LinearMap.coe_comp]
    exact hπ.comp (F.mapIso (asIso a)).toLinearEquiv.surjective
  rw [sq, ModuleCat.hom_comp, LinearMap.coe_comp] at hs
  exact hs.of_comp

/-- **The degree-zero map of a quasi-isomorphism is surjective on cohomology** when the target
degenerates at `E₁`. Let `φ : K' ⟶ K` be a quasi-isomorphism of complexes of sheaves of
`π⁻¹𝒪_T`-modules indexed by `ℕ`. If `dim ℍ^k(K) = ∑_{p ≤ k} dim H^{k-p}(Kᵖ)` with
finite-dimensional terms, then `H^k(φ⁰) : H^k(K'⁰) ⟶ H^k(K⁰)` is surjective: composed with the
isomorphism `ℍ^k(K') ≅ ℍ^k(K)` and the edge map of `K` it is the edge map of `K'`. -/
theorem surjective_hypFunctor_map_singleFunctor_f_zero_of_quasiIso (hT : IsField Γ(T, ⊤))
    {K' K : CochainComplex (SheafOfModules.{0} (invRing h)) ℕ} (φ : K' ⟶ K) [QuasiIso φ]
    (k : ℕ)
    (hfin : ∀ p : ℕ, p < k + 1 →
      Module.Finite Γ(T, ⊤) (Hc h (single0 h (K.X p)) ((k - p : ℕ) : ℤ)))
    (heq : Module.finrank Γ(T, ⊤) (Hc h (extendPlus h K) k) =
      ∑ p ∈ Finset.range (k + 1),
        Module.finrank Γ(T, ⊤) (Hc h (single0 h (K.X p)) ((k - p : ℕ) : ℤ))) :
    Function.Surjective
      ((hypFunctor h k).map ((DerivedCategory.Plus.singleFunctor _ 0).map (φ.f 0))).hom := by
  set X := K.extend ComplexShape.embeddingUpNat
  set X' := K'.extend ComplexShape.embeddingUpNat
  let ψ : X' ⟶ X := extendMap φ ComplexShape.embeddingUpNat
  have hedge := surjective_hypFunctor_map_truncGEπ0_extend_of_finrank_eq_sum h hT K k hfin heq
  have hI := isIso_ιStupidTrunc X (embeddingUpIntGE 0)
  have hq : QuasiIso (stupidTruncMap ψ (embeddingUpIntGE 0)) := by
    rw [← quasiIso_iff_comp_right _ (ιStupidTrunc X (embeddingUpIntGE 0)),
      stupidTruncMap_ιStupidTrunc]
    infer_instance
  let a : truncGE h X' 0 ⟶ truncGE h X 0 :=
    ObjectProperty.homMk (stupidTruncMap ψ (embeddingUpIntGE 0))
  let b : single0 h (X'.X 0) ⟶ single0 h (X.X 0) :=
    ObjectProperty.homMk ((single _ (up ℤ) 0).map (ψ.f 0))
  have sq : a ≫ truncGEπ0 h X = truncGEπ0 h X' ≫ b :=
    (ObjectProperty.fullyFaithfulι _).map_injective (stupidTruncMap_comp_stupidTruncGEπ ψ 0)
  have ha : IsIso (DerivedCategory.Plus.Q.map a) := by
    have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map a)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
    exact isIso_of_fully_faithful DerivedCategory.Plus.ι _
  have hb := surjective_map_of_comp_eq_of_isIso (hypFunctor h k) (DerivedCategory.Plus.Q.map a)
    _ (DerivedCategory.Plus.Q.map (truncGEπ0 h X')) (DerivedCategory.Plus.Q.map b)
    (by rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, sq])
    hedge
  have hψ : ψ.f 0 = (K'.extendXIso ComplexShape.embeddingUpNat rfl).hom ≫ φ.f 0 ≫
      (K.extendXIso ComplexShape.embeddingUpNat rfl).inv :=
    extendMap_f φ ComplexShape.embeddingUpNat rfl
  refine (surjective_map_iff_of_square (hypFunctor h k) _ _
    (single0Iso h (X'.X 0) ≪≫ (DerivedCategory.Plus.singleFunctor _ 0).mapIso
      (K'.extendXIso ComplexShape.embeddingUpNat rfl))
    (single0Iso h (X.X 0) ≪≫ (DerivedCategory.Plus.singleFunctor _ 0).mapIso
      (K.extendXIso ComplexShape.embeddingUpNat rfl)) ?_).1 hb
  apply DerivedCategory.Plus.ι.map_injective
  change DerivedCategory.Q.map ((single _ (up ℤ) 0).map (ψ.f 0)) ≫ (𝟙 _ ≫
      DerivedCategory.Q.map ((single _ (up ℤ) 0).map
        (K.extendXIso ComplexShape.embeddingUpNat rfl).hom)) =
    (𝟙 _ ≫ DerivedCategory.Q.map ((single _ (up ℤ) 0).map
        (K'.extendXIso ComplexShape.embeddingUpNat rfl).hom)) ≫
      DerivedCategory.Q.map ((single _ (up ℤ) 0).map (φ.f 0))
  rw [hψ, Category.id_comp, Category.id_comp]
  refine (DerivedCategory.Q.map_comp _ _).symm.trans
    (Eq.trans ?_ (DerivedCategory.Q.map_comp _ _))
  refine congrArg DerivedCategory.Q.map ?_
  refine ((single (SheafOfModules.{0} (invRing h)) (up ℤ) 0).map_comp _ _).symm.trans
    (Eq.trans ?_ ((single (SheafOfModules.{0} (invRing h)) (up ℤ) 0).map_comp _ _))
  refine congrArg (single (SheafOfModules.{0} (invRing h)) (up ℤ) 0).map ?_
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (φ.f 0 ≫ ·) (K.extendXIso ComplexShape.embeddingUpNat rfl).inv_hom_id).trans
      (Category.comp_id _))))

/-- **The degree-zero map of a quasi-isomorphism is surjective on cohomology**, for the classical
right derived functors of global sections: the form of
`MMP.LcBpf.surjective_hypFunctor_map_singleFunctor_f_zero_of_quasiIso` on `Rᵏ Γ(φ⁰)`. -/
theorem surjective_rightDerived_map_f_zero_of_quasiIso (hT : IsField Γ(T, ⊤))
    {K' K : CochainComplex (SheafOfModules.{0} (invRing h)) ℕ} (φ : K' ⟶ K) [QuasiIso φ]
    (k : ℕ)
    (hfin : ∀ p : ℕ, p < k + 1 →
      Module.Finite Γ(T, ⊤) (Hc h (single0 h (K.X p)) ((k - p : ℕ) : ℤ)))
    (heq : Module.finrank Γ(T, ⊤) (Hc h (extendPlus h K) k) =
      ∑ p ∈ Finset.range (k + 1),
        Module.finrank Γ(T, ⊤) (Hc h (single0 h (K.X p)) ((k - p : ℕ) : ℤ))) :
    Function.Surjective (((globalSections h).rightDerived k).map (φ.f 0)).hom :=
  (surjective_hypFunctor_map_singleFunctor_iff h (φ.f 0) k).1
    (surjective_hypFunctor_map_singleFunctor_f_zero_of_quasiIso h hT φ k hfin heq)

end EdgeMap

section ModulesOverAField

open CategoryTheory AlgebraicGeometry
open MMP.FourfoldProofs.FractionalLogComplexProof MMP.Mori.Divisor.LogSpreadingProof
  MMP.FourfoldProofs.LogDegenerationProof

/-- **The degree-zero map of a quasi-isomorphism is surjective on the cohomology of
`𝒪_V`-modules.** Let `V` be a scheme over a field `k`, `ψ : π⁻¹𝒪 ⟶ 𝒪_V`, and
`φ : K' ⟶ K` a quasi-isomorphism of complexes of sheaves of `π⁻¹𝒪`-modules indexed by `ℕ` whose
degree-zero terms are the restrictions of scalars of `𝒪_V`-modules `F'` and `F`, with `φ⁰`
induced by `g : F' ⟶ F`. If `K` degenerates at `E₁` in degree `n`, with finite-dimensional
`E₁`-terms, then `Hⁿ(V, g) : Hⁿ(V, F') ⟶ Hⁿ(V, F)` is surjective. -/
theorem surjective_derivedGlobalSectionsOver_map_of_quasiIso {k : Type} [Field k]
    {V : Scheme.{0}} (f : V ⟶ Spec (.of k)) [HasDerivedCategory V.Modules]
    [HasDerivedCategory (ModuleCat.{0} k)] (ψ : invRing f ⟶ V.ringCatSheaf)
    {K' K : CochainComplex (SheafOfModules.{0} (invRing f)) ℕ} (φ : K' ⟶ K) [QuasiIso φ]
    {F' F : V.Modules} (g : F' ⟶ F)
    (e' : K'.X 0 ≅ (SheafOfModules.restrictScalars.{0} ψ).obj F')
    (e : K.X 0 ≅ (SheafOfModules.restrictScalars.{0} ψ).obj F)
    (w : φ.f 0 ≫ e.hom = e'.hom ≫ (SheafOfModules.restrictScalars.{0} ψ).map g) (n : ℕ)
    (hfin : ∀ p : ℕ, p < n + 1 →
      Module.Finite Γ(Spec (.of k), ⊤) (Hc f (single0 f (K.X p)) ((n - p : ℕ) : ℤ)))
    (heq : Module.finrank Γ(Spec (.of k), ⊤) (Hc f (extendPlus f K) n) =
      ∑ p ∈ Finset.range (n + 1),
        Module.finrank Γ(Spec (.of k), ⊤) (Hc f (single0 f (K.X p)) ((n - p : ℕ) : ℤ))) :
    Function.Surjective ((DerivedCategory.homologyFunctor (ModuleCat.{0} k) n).map
      ((derivedGlobalSectionsOver f).map
        ((DerivedCategory.singleFunctor V.Modules 0).map g))).hom := by
  have hT : IsField Γ(Spec (.of k), ⊤) := MulEquiv.isField (Field.toIsField k)
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv
  exact (surjective_derivedGlobalSectionsOver_map_iff_restrictScalars f ψ g n).2
    ((surjective_map_iff_of_square ((globalSections f).rightDerived n) _ _ e' e w).1
      (surjective_rightDerived_map_f_zero_of_quasiIso f hT φ n hfin heq))

end ModulesOverAField

end MMP.LcBpf
