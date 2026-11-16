/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Duality.Sweep.SheafExtDerivedComparison
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKerStalk
public import MMP.AlgebraicGeometry.Cohomology.Duality.CanonicalExtSequence

/-!
# Sheaf `𝓔xt⁰`, the first-variable `𝓔xt` sequence of a sheaf of ideals, and multiplication maps

Let `Y` be a ringed space, `F` and `G` sheaves of `𝒪_Y`-modules. Since `𝓗om(F, -)` is left
exact, the zeroth sheaf Ext is the internal Hom: `𝓔xt⁰(F, G) ≅ 𝓗om(F, G)`, and through the
comparison of the right-derived and the derived-category sheaf Ext this is
`H⁰ R𝓗om(F[0], G[0]) ≅ 𝓗om(F, G)`.

For a sheaf of ideals `ℐ ⊆ 𝒪_Y` with quotient `𝒪_Y/ℐ`, applying `𝓗om(-, G)` to
`0 → ℐ → 𝒪_Y → 𝒪_Y/ℐ → 0` gives the exact sequence
`𝓗om(𝒪_Y, G) → 𝓗om(ℐ, G) → 𝓔xt¹(𝒪_Y/ℐ, G) → 0`, the last zero being
`𝓔xt¹(𝒪_Y, G) = 0`.

## Main results

* `MMP.Flips.sheafExtZeroIso`: `𝓔xt⁰(F, G) ≅ 𝓗om(F, G)`.
* `MMP.Flips.derivedSheafExtZeroIso`: `H⁰ R𝓗om(F[0], G[0]) ≅ 𝓗om(F, G)`.
* `MMP.Flips.exists_epi_exact_sheafExt_one`: the exact sequence
  `𝓗om(𝒪_Y, G) → 𝓗om(ℐ, G) → 𝓔xt¹(𝒪_Y/ℐ, G) → 0`.
* `MMP.Flips.exists_epi_exact_extStructureSheaf_one`: the same for the ideal sheaf
  `MMP.Flips.closedImmersionIdeal i` of a closed immersion, with `𝓔xt¹(i_* 𝒪_S, G)`.
* `MMP.Flips.IsDualizingSheaf.exists_epi_exact_internalHom_ideal`: for `X` Cohen–Macaulay,
  `𝓗om(𝒪_X, ω_X) → 𝓗om(𝓘_S, ω_X) → i_* ω_S → 0` is exact.
* `MMP.Flips.mulInternalHom`: for submodules `𝓕, 𝓖 ⊆ K(X)` and `φ : 𝓐 ⟶ 𝒪_X` with
  `𝓕 · φ(𝓐) ⊆ 𝓖`, the morphism `𝓕 ⟶ 𝓗om(𝓐, 𝓖)`, `x ↦ (a ↦ φ(a) x)`.
* `MMP.Flips.isIso_mulInternalHom_id`: `𝓖 ≅ 𝓗om(𝒪_X, 𝓖)`, `x ↦ (a ↦ a x)`.
* `MMP.Flips.bijective_mulInternalHom_app`: when `φ` identifies `𝓐` with `𝓗 ⊆ K(X)`,
  `mulInternalHom` is bijective on the sections over `U` as soon as `x ↦ (l ↦ x l)` is a bijection
  onto the local homomorphisms `𝓗|_U ⟶ 𝓖|_U`.

## References

* [Stacks Project, Tag 0BQW](https://stacks.math.columbia.edu/tag/0BQW)
* [Stacks Project, Tag 01DR](https://stacks.math.columbia.edu/tag/01DR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

-- The Stacks results used here are stated at the locally small models of `D(R)`, `D(𝒪_X)`
-- and `D(SheafOfModules R)`, which Stacks scopes
-- (`StacksFrontier.Homology.DerivedCategory.LocallySmall`).
open scoped Stacks.SmallDerivedModel
open Stacks.SheafOfModules.InternalHom

namespace MMP.Flips

universe u

set_option backward.isDefEq.respectTransparency false

section ExtZero

attribute [local instance 10000] HasDerivedCategory.standard

variable (Y : AlgebraicGeometry.RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))

/-- **`𝓔xt⁰(F, G) = 𝓗om(F, G)`**: the internal Hom out of `F` is left exact. -/
def sheafExtZeroIso :
    Stacks.RingedSpace.sheafExt Y F G 0 ≅
      (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
        F).obj G :=
  (Functor.rightDerivedZeroIsoSelf _).app G

/-- **`H⁰ R𝓗om(F[0], G[0]) = 𝓗om(F, G)`.** -/
def derivedSheafExtZeroIso :
    Stacks.SheafOfModules.derivedSheafExt Y.sheaf
        (DerivedCategory.Q.obj ((HomologicalComplex.single
          (Stacks.SheafOfModules.StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj F))
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))
        ((0 : ℕ) : ℤ) ≅
      (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
        F).obj G :=
  (Stacks.RingedSpace.sheafExtIsoDerivedSheafExt Y F G 0).symm ≪≫ sheafExtZeroIso Y F G

end ExtZero

section IdealSequence

variable (Y : AlgebraicGeometry.RingedSpace.{u, u})
  (I : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)).Submodule)
  (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))

/-- The internal Hom out of `F`, applied degreewise to the injective resolution of `G`. -/
abbrev internalHomInjectiveResolution
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℕ :=
  ((internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
    F).mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution G).cocomplex

/-- `𝓗om(F, G)` is the degree-zero cohomology of `𝓗om(F, J^•)`, `J^•` the injective resolution
of `G`. -/
def internalHomIsoHomologyZero
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) :
    (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
        F).obj G ≅ (internalHomInjectiveResolution Y G F).homology 0 :=
  asIso ((injectiveResolution G).toRightDerivedZero'
      (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
        F)) ≪≫ CochainComplex.isoHomologyπ₀ _

/-- The forward map of `internalHomIsoHomologyZero` is the comparison into the degree-zero
right derived functor followed by the projection onto degree-zero cohomology. -/
theorem internalHomIsoHomologyZero_hom
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) :
    (internalHomIsoHomologyZero Y G F).hom =
      (injectiveResolution G).toRightDerivedZero'
        (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
          F) ≫ HomologicalComplex.homologyπ _ 0 :=
  rfl

/-- The identification `internalHomIsoHomologyZero` is natural in the first variable. -/
theorem internalHomIsoHomologyZero_naturality
    {F F' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)} (k : F' ⟶ F) :
    (internalHomMapLeftNatTrans Y.sheaf k).app G ≫ (internalHomIsoHomologyZero Y G F').hom =
      (internalHomIsoHomologyZero Y G F).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (internalHomMapLeftNatTrans Y.sheaf k)
            (ComplexShape.up ℕ)).app (injectiveResolution G).cocomplex) 0 := by
  have key : (internalHomMapLeftNatTrans Y.sheaf k).app G ≫
      (injectiveResolution G).toRightDerivedZero'
        (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf F') =
      (injectiveResolution G).toRightDerivedZero'
        (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf F) ≫
        HomologicalComplex.cyclesMap
          ((NatTrans.mapHomologicalComplex (internalHomMapLeftNatTrans Y.sheaf k)
            (ComplexShape.up ℕ)).app (injectiveResolution G).cocomplex) 0 := by
    rw [← cancel_mono (HomologicalComplex.iCycles _ _)]
    simp only [Category.assoc, InjectiveResolution.toRightDerivedZero'_comp_iCycles,
      HomologicalComplex.cyclesMap_i, InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc]
    exact ((internalHomMapLeftNatTrans Y.sheaf k).naturality _).symm
  rw [internalHomIsoHomologyZero_hom, internalHomIsoHomologyZero_hom, ← Category.assoc, key,
    Category.assoc, Category.assoc, HomologicalComplex.homologyπ_naturality]

/-- `𝓔xt¹(𝒪_Y, G) = 0`, read on the complex `𝓗om(𝒪_Y, J^•)`. -/
theorem isZero_internalHomInjectiveResolution_unit_homology_one :
    IsZero ((internalHomInjectiveResolution Y G
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))).homology 1) :=
  (Stacks.RingedSpace.isZero_sheafExt_unit_succ Y G 0).of_iso
    ((injectiveResolution G).isoRightDerivedObj _ 1).symm

/-- **The first-variable `𝓔xt` sequence of a sheaf of ideals.** For a sheaf of ideals
`ℐ ⊆ 𝒪_Y` and a module `G` there is an epimorphism `δ : 𝓗om(ℐ, G) ⟶ 𝓔xt¹(𝒪_Y/ℐ, G)` whose
kernel is the image of the restriction `𝓗om(𝒪_Y, G) ⟶ 𝓗om(ℐ, G)`. -/
theorem exists_epi_exact_sheafExt_one :
    ∃ δ : (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
        I.toSheafOfModules).obj G ⟶
        Stacks.RingedSpace.sheafExt Y (Stacks.Duality.quotientByIdealSheaf Y I) G 1,
      ∃ hδ : (internalHomMapLeftNatTrans Y.sheaf I.ι).app G ≫ δ = 0,
        Epi δ ∧ (ShortComplex.mk _ _ hδ).Exact := by
  let K := (injectiveResolution G).cocomplex
  have hS := Stacks.Duality.sheafHomComplexSequence_shortExact Y I K
  let eO := internalHomIsoHomologyZero Y G
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
  let eI := internalHomIsoHomologyZero Y G I.toSheafOfModules
  let eE := (injectiveResolution G).isoRightDerivedObj
    (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
      (Stacks.Duality.quotientByIdealSheaf Y I)) 1
  have hcomm := internalHomIsoHomologyZero_naturality Y G I.ι
  let δ := eI.hom ≫ hS.δ 0 1 rfl ≫ eE.inv
  have hδ : (internalHomMapLeftNatTrans Y.sheaf I.ι).app G ≫ δ = 0 := by
    calc (internalHomMapLeftNatTrans Y.sheaf I.ι).app G ≫ δ
        = ((internalHomMapLeftNatTrans Y.sheaf I.ι).app G ≫ eI.hom) ≫ hS.δ 0 1 rfl ≫ eE.inv :=
          (Category.assoc _ _ _).symm
      _ = eO.hom ≫ (HomologicalComplex.homologyMap
            (Stacks.Duality.sheafHomComplexSequence Y I K).g 0 ≫ hS.δ 0 1 rfl) ≫ eE.inv := by
          rw [hcomm]
          simp only [Category.assoc]
          rfl
      _ = 0 := by rw [hS.comp_δ 0 1 rfl, zero_comp, comp_zero]
  refine ⟨δ, hδ, ?_, ?_⟩
  · have : Epi (hS.δ 0 1 rfl) := (hS.homology_exact₁ 0 1 rfl).epi_f
      ((isZero_internalHomInjectiveResolution_unit_homology_one Y G).eq_of_tgt _ _)
    exact epi_comp eI.hom (hS.δ 0 1 rfl ≫ eE.inv)
  · refine (ShortComplex.exact_iff_of_iso ?_).2 (hS.homology_exact₃ 0 1 rfl)
    exact ShortComplex.isoMk eO eI eE hcomm.symm
      (by change _ = (eI.hom ≫ hS.δ 0 1 rfl ≫ eE.inv) ≫ eE.hom
          simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

end IdealSequence

section ClosedImmersion

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (i : S ⟶ X)

/-- The ideal sheaf `𝓘_S ⊆ 𝒪_X` of a morphism `i : S ⟶ X`: the kernel of `𝒪_X ⟶ i_* 𝒪_S`. -/
def closedImmersionIdeal : (SheafOfModules.unit X.ringCatSheaf).Submodule :=
  SheafOfModules.Submodule.ker (ClosedImmersionCoherentImage.unitToPushforwardUnit i)

/-- For a closed immersion, `𝒪_X / 𝓘_S ≅ i_* 𝒪_S`. -/
def quotientClosedImmersionIdealIso [IsClosedImmersion i] :
    Stacks.Duality.quotientByIdealSheaf X.toRingedSpace (closedImmersionIdeal i) ≅
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit S.ringCatSheaf) :=
  haveI := ClosedImmersionCoherentImage.epi_unitToPushforwardUnit i
  (colimit.isColimit _).coconePointUniqueUpToIso
    (SheafOfModules.Submodule.exact_ker_shortComplex
      (ClosedImmersionCoherentImage.unitToPushforwardUnit i)).gIsCokernel

/-- `𝓔xt¹(𝒪_X / 𝓘_S, G) ≅ 𝓔xt¹(i_* 𝒪_S, G)` for a closed immersion, the right-hand side in the
derived-category spelling `MMP.Flips.extStructureSheaf`. -/
def sheafExtOneQuotientIso [IsClosedImmersion i] (G : X.Modules) :
    Stacks.RingedSpace.sheafExt X.toRingedSpace
        (Stacks.Duality.quotientByIdealSheaf X.toRingedSpace (closedImmersionIdeal i)) G 1 ≅
      extStructureSheaf i G 1 :=
  Stacks.RingedSpace.sheafExtIsoDerivedSheafExt X.toRingedSpace _ G 1 ≪≫
    Stacks.SheafOfModules.derivedSheafExtMapIso X.sheaf ((1 : ℕ) : ℤ)
      ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app _ ≪≫
        DerivedCategory.Q.mapIso ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
          (quotientClosedImmersionIdealIso i).symm))
      ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app G).symm ≪≫
    eqToIso (by simp only [extStructureSheaf, Stacks.Duality.extSheafOf, neg_neg]; rfl)

/-- **The `𝓔xt` sequence of a closed subscheme.** For a closed immersion `i : S ⟶ X` and an
`𝒪_X`-module `G` there is an epimorphism `𝓗om(𝓘_S, G) ⟶ 𝓔xt¹(i_* 𝒪_S, G)` whose kernel is the
image of the restriction `𝓗om(𝒪_X, G) ⟶ 𝓗om(𝓘_S, G)`. -/
theorem exists_epi_exact_extStructureSheaf_one [IsClosedImmersion i] (G : X.Modules) :
    ∃ δ : (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology X)
        X.sheaf (closedImmersionIdeal i).toSheafOfModules).obj G ⟶ extStructureSheaf i G 1,
      ∃ hδ : (internalHomMapLeftNatTrans X.sheaf (closedImmersionIdeal i).ι).app G ≫ δ = 0,
        Epi δ ∧ (ShortComplex.mk _ _ hδ).Exact := by
  obtain ⟨δ, hδ, hepi, hex⟩ :=
    exists_epi_exact_sheafExt_one X.toRingedSpace (closedImmersionIdeal i) G
  refine ⟨δ ≫ (sheafExtOneQuotientIso i G).hom, by rw [reassoc_of% hδ, zero_comp],
    epi_comp _ _, ?_⟩
  refine (ShortComplex.exact_iff_of_iso ?_).1 hex
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (sheafExtOneQuotientIso i G)
    (by simp) (by simp)

/-- **The adjunction sequence, sheaf-theoretic core.** Let `X` be Cohen–Macaulay of finite type
and pure dimension `d + 1` over `k` with dualizing sheaf `ω_X`, and `i : S ⟶ X` a closed
subscheme of pure dimension `d` with dualizing sheaf `ω_S`. Then there is an epimorphism
`𝓗om(𝓘_S, ω_X) ⟶ i_* ω_S` whose kernel is the image of `𝓗om(𝒪_X, ω_X) ⟶ 𝓗om(𝓘_S, ω_X)`. -/
theorem IsDualizingSheaf.exists_epi_exact_internalHom_ideal {k : Type u} [Field k]
    [IsLocallyNoetherian X] {π : X ⟶ Spec (.of k)} {d : ℕ} {ωX : X.Modules}
    (hX : IsDualizingSheaf π (d + 1) ωX)
    (hCM : ∀ x : X, IsCohenMacaulayLocalRing (X.presheaf.stalk x))
    [IsClosedImmersion i] {ωS : S.Modules} (hS : IsDualizingSheaf (i ≫ π) d ωS) :
    ∃ δ : (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology X)
        X.sheaf (closedImmersionIdeal i).toSheafOfModules).obj ωX ⟶
          (Scheme.Modules.pushforward i).obj ωS,
      ∃ hδ : (internalHomMapLeftNatTrans X.sheaf (closedImmersionIdeal i).ι).app ωX ≫ δ = 0,
        Epi δ ∧ (ShortComplex.mk _ _ hδ).Exact := by
  obtain ⟨hN, hL⟩ := isNoetherian_and_locallyOfFiniteType_of_isDualizingSheaf hX
  have : CompactSpace X := hN.toCompactSpace
  obtain ⟨e⟩ := hX.nonempty_iso_ext hCM i hS
  obtain ⟨δ, hδ, hepi, hex⟩ := exists_epi_exact_extStructureSheaf_one i ωX
  refine ⟨δ ≫ e.inv, by rw [reassoc_of% hδ, zero_comp], epi_comp _ _, ?_⟩
  refine (ShortComplex.exact_iff_of_iso ?_).1 hex
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e.symm (by simp) (by simp)

end ClosedImmersion

section MulInternalHom

open Opposite MMP.Mori RationalFunctionsSubmodule Stacks.PresheafOfModules.InternalHom

variable {X : Scheme.{u}}

/-- `x · φ(𝓐) ⊆ 𝓖` for every section `x` of `𝓕`: the condition under which `x ↦ (a ↦ φ(a) x)` is
a morphism `𝓕 ⟶ 𝓗om(𝓐, 𝓖)`. -/
def MulInternalHomCond (F G : RationalFunctionsSubmodule X) {A : X.Modules}
    (φ : A ⟶ SheafOfModules.unit X.ringCatSheaf) : Prop :=
  ∀ {U W : X.Opens} (i : W ⟶ U) {x : ToType ((rationalFunctionsPresheaf X).obj (op U))},
    x ∈ F.sections U → ∀ a : A.val.obj (op W),
      (show Γ(X, W) from φ.val.app (op W) a) • (rationalFunctionsPresheaf X).map i.op x ∈
        G.sections W

/-- For `x ∈ 𝓕(U)` with `x · φ(𝓐) ⊆ 𝓖`, the morphism `𝓐|_U ⟶ 𝓖|_U`, `a ↦ φ(a) x`. -/
def mulInternalHomSection {F G : RationalFunctionsSubmodule X} {A : X.Modules}
    {φ : A ⟶ SheafOfModules.unit X.ringCatSheaf} (h : MulInternalHomCond F G φ) (U : X.Opens)
    (x : F.sections U) :
    (restrFun X.sheaf.obj U).obj A.val ⟶ (restrFun X.sheaf.obj U).obj G.toModules.val :=
  PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom
        { toFun := fun a => ⟨(show Γ(X, W.unop.left) from φ.val.app (op W.unop.left) a) •
            (rationalFunctionsPresheaf X).map W.unop.hom.op x.1, h W.unop.hom x.2 a⟩
          map_zero' := by
            apply Subtype.ext
            change (show Γ(X, W.unop.left) from φ.val.app (op W.unop.left) 0) • _ = 0
            rw [map_zero, zero_smul]
          map_add' := fun a b => by
            apply Subtype.ext
            change (show Γ(X, W.unop.left) from φ.val.app (op W.unop.left) (a + b)) • _ =
              (show Γ(X, W.unop.left) from φ.val.app (op W.unop.left) a) • _ +
              (show Γ(X, W.unop.left) from φ.val.app (op W.unop.left) b) • _
            rw [map_add, add_smul] }
      naturality := fun W₁ W₂ g => by
        ext a
        apply Subtype.ext
        change (show Γ(X, W₂.unop.left) from φ.val.app (op W₂.unop.left)
            (A.val.map g.unop.left.op a)) • (rationalFunctionsPresheaf X).map W₂.unop.hom.op x.1 =
          (rationalFunctionsPresheaf X).map g.unop.left.op
            ((show Γ(X, W₁.unop.left) from φ.val.app (op W₁.unop.left) a) •
              (rationalFunctionsPresheaf X).map W₁.unop.hom.op x.1)
        rw [rationalFunctionsPresheaf_map_smul, PresheafOfModules.naturality_apply]
        rfl }
    (fun W r a => Subtype.ext <| by
      change (show Γ(X, W.unop.left) from φ.val.app (op W.unop.left) (r • a)) •
          (rationalFunctionsPresheaf X).map W.unop.hom.op x.1 =
        (show Γ(X, W.unop.left) from r) •
          ((show Γ(X, W.unop.left) from φ.val.app (op W.unop.left) a) •
            (rationalFunctionsPresheaf X).map W.unop.hom.op x.1)
      rw [map_smul, smul_eq_mul, mul_smul])

/-- The section `mulInternalHomSection h U x` sends `a` over `W` to `φ(a) · x|_W` in `K(X)`. -/
theorem mulInternalHomSection_app_apply {F G : RationalFunctionsSubmodule X} {A : X.Modules}
    {φ : A ⟶ SheafOfModules.unit X.ringCatSheaf} (h : MulInternalHomCond F G φ) (U : X.Opens)
    (x : F.sections U) (W : (Over U)ᵒᵖ)
    (a : A.val.obj (op W.unop.left)) :
    (show G.sections W.unop.left from (mulInternalHomSection h U x).app W a).1 =
      (show Γ(X, W.unop.left) from φ.val.app (op W.unop.left) a) •
        (rationalFunctionsPresheaf X).map W.unop.hom.op x.1 :=
  rfl

/-- Two morphisms `𝓐|_U ⟶ 𝓖|_U` into a submodule of `K(X)` agree when they agree in `K(X)`. -/
theorem restrFun_hom_ext {G : RationalFunctionsSubmodule X} {A : X.Modules} {U : X.Opens}
    {α β : (restrFun X.sheaf.obj U).obj A.val ⟶ (restrFun X.sheaf.obj U).obj G.toModules.val}
    (H : ∀ (W : (Over U)ᵒᵖ) (a : A.val.obj (op W.unop.left)),
      (show G.sections W.unop.left from α.app W a).1 =
        (show G.sections W.unop.left from β.app W a).1) : α = β :=
  PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun a => Subtype.ext (H W a))

/-- **Multiplication into an internal Hom.** If `x · φ(𝓐) ⊆ 𝓖` for the sections `x` of `𝓕`, then
`x ↦ (a ↦ φ(a) x)` is a morphism `𝓕 ⟶ 𝓗om(𝓐, 𝓖)`. -/
def mulInternalHom {F G : RationalFunctionsSubmodule X} {A : X.Modules}
    {φ : A ⟶ SheafOfModules.unit X.ringCatSheaf} (h : MulInternalHomCond F G φ) :
    F.toModules ⟶ (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology X) X.sheaf
      A).obj G.toModules :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun x => mulInternalHomSection h U.unop x
          map_zero' := restrFun_hom_ext fun W a => by
            change (show Γ(X, W.unop.left) from φ.val.app (op W.unop.left) a) •
              (rationalFunctionsPresheaf X).map W.unop.hom.op 0 = 0
            rw [map_zero, smul_zero]
          map_add' := fun x y => restrFun_hom_ext fun W a => by
            change (show Γ(X, W.unop.left) from φ.val.app (op W.unop.left) a) •
              (rationalFunctionsPresheaf X).map W.unop.hom.op (x.1 + y.1) =
              (show Γ(X, W.unop.left) from φ.val.app (op W.unop.left) a) •
                (rationalFunctionsPresheaf X).map W.unop.hom.op x.1 +
              (show Γ(X, W.unop.left) from φ.val.app (op W.unop.left) a) •
                (rationalFunctionsPresheaf X).map W.unop.hom.op y.1
            rw [map_add, smul_add] }
      naturality := fun U₁ U₂ f => by
        ext x
        exact restrFun_hom_ext fun W a => rfl }
    (fun U r x => restrFun_hom_ext fun W a => by
      change (show Γ(X, W.unop.left) from φ.val.app (op W.unop.left) a) •
          (rationalFunctionsPresheaf X).map W.unop.hom.op ((show Γ(X, U.unop) from r) • x.1) =
        (show Γ(X, W.unop.left) from X.presheaf.map W.unop.hom.op r) •
          ((show Γ(X, W.unop.left) from φ.val.app (op W.unop.left) a) •
            (rationalFunctionsPresheaf X).map W.unop.hom.op x.1)
      rw [rationalFunctionsPresheaf_map_smul, smul_comm])⟩

/-- On the sections over `U`, `mulInternalHom h` is `mulInternalHomSection h U`. -/
theorem mulInternalHom_app_apply {F G : RationalFunctionsSubmodule X} {A : X.Modules}
    {φ : A ⟶ SheafOfModules.unit X.ringCatSheaf} (h : MulInternalHomCond F G φ) (U : X.Opens)
    (x : F.sections U) :
    (mulInternalHom h).val.app (op U) x = mulInternalHomSection h U x :=
  rfl

/-- Restricting `x ↦ (a ↦ φ(a) x)` along `k : 𝓐' ⟶ 𝓐` gives `x ↦ (a' ↦ φ(k a') x)`. -/
theorem mulInternalHom_comp_internalHomMapLeft {F G : RationalFunctionsSubmodule X}
    {A A' : X.Modules} {φ : A ⟶ SheafOfModules.unit X.ringCatSheaf}
    (h : MulInternalHomCond F G φ) (k : A' ⟶ A) (h' : MulInternalHomCond F G (k ≫ φ)) :
    mulInternalHom h ≫ (internalHomMapLeftNatTrans X.sheaf k).app G.toModules =
      mulInternalHom h' :=
  SheafOfModules.hom_ext <| PresheafOfModules.hom_ext fun _ =>
    ModuleCat.hom_ext <| LinearMap.ext fun _ => restrFun_hom_ext fun _ _ => rfl

/-- A morphism of `𝒪_X`-modules bijective on the sections over every open is an isomorphism. -/
theorem isIso_of_bijective_app {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ U : X.Opens, Function.Bijective (f.val.app (op U))) : IsIso f := by
  let e : M.val ≅ N.val := PresheafOfModules.isoMk
    (fun U => (LinearEquiv.ofBijective (f.val.app U).hom (hf U.unop)).toModuleIso)
    (fun U V g => by
      ext x
      exact PresheafOfModules.naturality_apply f.val g x)
  have he : e.hom = f.val := PresheafOfModules.hom_ext fun _ => rfl
  have : IsIso ((SheafOfModules.forget X.ringCatSheaf).map f) := by
    change IsIso f.val
    rw [← he]
    infer_instance
  have := (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).reflectsIsomorphisms
  exact isIso_of_reflects_iso f (SheafOfModules.forget _)

/-- `x · 𝒪_X ⊆ 𝓖` for the sections `x` of `𝓖`. -/
theorem mulInternalHomCond_id (G : RationalFunctionsSubmodule X) :
    MulInternalHomCond G G (𝟙 (SheafOfModules.unit X.ringCatSheaf)) :=
  fun i _ hx a => G.sections _ |>.smul_mem (show Γ(X, _) from a) (G.map_mem i hx)

/-- `𝓖 ≅ 𝓗om(𝒪_X, 𝓖)`, `x ↦ (a ↦ a x)`. -/
theorem isIso_mulInternalHom_id (G : RationalFunctionsSubmodule X) :
    IsIso (mulInternalHom (mulInternalHomCond_id G)) := by
  refine isIso_of_bijective_app _ fun U => ⟨fun x y hxy => ?_, fun β => ?_⟩
  · have := congrArg (fun α : (restrFun X.sheaf.obj U).obj
        (SheafOfModules.unit X.ringCatSheaf).val ⟶ (restrFun X.sheaf.obj U).obj G.toModules.val =>
      (show G.sections U from α.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))).1) hxy
    change (1 : Γ(X, U)) • (rationalFunctionsPresheaf X).map (𝟙 U).op x.1 =
      (1 : Γ(X, U)) • (rationalFunctionsPresheaf X).map (𝟙 U).op y.1 at this
    rw [one_smul, one_smul, rationalFunctionsPresheaf_map_id_apply,
      rationalFunctionsPresheaf_map_id_apply] at this
    exact Subtype.ext this
  · refine ⟨(show G.sections U from β.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))), ?_⟩
    refine restrFun_hom_ext fun W a => ?_
    change (show Γ(X, W.unop.left) from a) • (rationalFunctionsPresheaf X).map W.unop.hom.op
      (show G.sections U from β.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))).1 = _
    let g : op (Over.mk (𝟙 U)) ⟶ W := (Over.homMk W.unop.hom : W.unop ⟶ Over.mk (𝟙 U)).op
    have h1 := PresheafOfModules.naturality_apply β g (1 : Γ(X, U))
    have h2 : ((restrFun X.sheaf.obj U).obj (SheafOfModules.unit X.ringCatSheaf).val).map g
        (1 : Γ(X, U)) = (1 : Γ(X, W.unop.left)) := map_one (X.presheaf.map W.unop.hom.op).hom
    rw [h2] at h1
    have h3 := (β.app W).hom.map_smul (show Γ(X, W.unop.left) from a) (1 : Γ(X, W.unop.left))
    rw [smul_eq_mul, mul_one] at h3
    rw [h3, h1]
    rfl

private theorem smul_eq_mul_algebraMap_app {A : X.Modules}
    {φ : A ⟶ SheafOfModules.unit X.ringCatSheaf} (W : X.Opens) (a : A.val.obj (op W))
    (z : ToType ((rationalFunctionsPresheaf X).obj (op W))) :
    (show Γ(X, W) from φ.val.app (op W) a) • z =
      z * algebraMap Γ(X, W) ((rationalFunctionsPresheaf X).obj (op W))
        (show Γ(X, W) from φ.val.app (op W) a) := by
  rw [Algebra.smul_def, mul_comm]

/-- Over an open `U`, `x ↦ (a ↦ φ(a) x)` is injective on `𝓕(U)` as soon as `φ(𝓐)` covers `𝓗`
and `x ↦ (l ↦ x l)` is injective from `𝓕(U)` to the local homomorphisms `𝓗|_U ⟶ 𝓖|_U`. -/
theorem injective_mulInternalHom_app {F G H : RationalFunctionsSubmodule X} {A : X.Modules}
    {φ : A ⟶ SheafOfModules.unit X.ringCatSheaf} (h : MulInternalHomCond F G φ) (U : X.Opens)
    (hsurj : ∀ (W : X.Opens) (l : ToType ((rationalFunctionsPresheaf X).obj (op W))),
      l ∈ H.sections W → ∃ a : A.val.obj (op W),
        algebraMap Γ(X, W) ((rationalFunctionsPresheaf X).obj (op W))
          (show Γ(X, W) from φ.val.app (op W) a) = l)
    (hmul : ∀ x ∈ F.sections U, ∀ (W : X.Opens) (i : W ⟶ U)
      (l : ToType ((rationalFunctionsPresheaf X).obj (op W))), l ∈ H.sections W →
        (rationalFunctionsPresheaf X).map i.op x * l ∈ G.sections W)
    (hinj : Function.Injective fun x : F.sections U => mulLocalHom H G U x.1 (hmul x.1 x.2)) :
    Function.Injective ((mulInternalHom h).val.app (op U)) := by
  choose pre hpre using hsurj
  intro x y hxy
  apply hinj
  simp only [mulLocalHom]
  congr 1
  funext W hW
  apply LinearMap.ext
  rintro ⟨l, hl⟩
  apply Subtype.ext
  change (rationalFunctionsPresheaf X).map (homOfLE hW).op x.1 * l =
    (rationalFunctionsPresheaf X).map (homOfLE hW).op y.1 * l
  rw [← hpre W l hl]
  have := congrArg (fun α : (restrFun X.sheaf.obj U).obj A.val ⟶
      (restrFun X.sheaf.obj U).obj G.toModules.val =>
    (show G.sections W from α.app (op (Over.mk (homOfLE hW))) (pre W l hl)).1) hxy
  change (show Γ(X, W) from φ.val.app (op W) (pre W l hl)) •
      (rationalFunctionsPresheaf X).map (homOfLE hW).op x.1 =
    (show Γ(X, W) from φ.val.app (op W) (pre W l hl)) •
      (rationalFunctionsPresheaf X).map (homOfLE hW).op y.1 at this
  rwa [smul_eq_mul_algebraMap_app, smul_eq_mul_algebraMap_app] at this

section Preimage

variable {H : RationalFunctionsSubmodule X} {A : X.Modules}
  {φ : A ⟶ SheafOfModules.unit X.ringCatSheaf}
  (hinj : ∀ W : X.Opens, Function.Injective fun a : A.val.obj (op W) =>
    algebraMap Γ(X, W) ((rationalFunctionsPresheaf X).obj (op W))
      (show Γ(X, W) from φ.val.app (op W) a))
  {pre : ∀ (W : X.Opens) (l : ToType ((rationalFunctionsPresheaf X).obj (op W))),
    l ∈ H.sections W → A.val.obj (op W)}
  (hpre : ∀ (W : X.Opens) (l : ToType ((rationalFunctionsPresheaf X).obj (op W)))
    (hl : l ∈ H.sections W), algebraMap Γ(X, W) ((rationalFunctionsPresheaf X).obj (op W))
      (show Γ(X, W) from φ.val.app (op W) (pre W l hl)) = l)

include hinj hpre

private theorem preimage_add (W : X.Opens) (l₁ l₂ : H.sections W) :
    pre W (l₁ + l₂).1 (l₁ + l₂).2 = pre W l₁.1 l₁.2 + pre W l₂.1 l₂.2 := by
  apply hinj W
  beta_reduce
  change _ = algebraMap Γ(X, W) ((rationalFunctionsPresheaf X).obj (op W))
    (show Γ(X, W) from φ.val.app (op W) (pre W l₁.1 l₁.2 + pre W l₂.1 l₂.2))
  rw [map_add, map_add, hpre, hpre, hpre]
  rfl

private theorem preimage_smul (W : X.Opens) (r : Γ(X, W)) (l : H.sections W) :
    pre W (r • l).1 (r • l).2 = (show X.ringCatSheaf.obj.obj (op W) from r) • pre W l.1 l.2 := by
  apply hinj W
  beta_reduce
  change _ = algebraMap Γ(X, W) ((rationalFunctionsPresheaf X).obj (op W))
    (show Γ(X, W) from φ.val.app (op W)
      ((show X.ringCatSheaf.obj.obj (op W) from r) • pre W l.1 l.2))
  rw [hpre, map_smul, smul_eq_mul, map_mul, hpre]
  exact Algebra.smul_def r l.1

private theorem preimage_restrict (W W' : X.Opens) (i : W' ⟶ W) (l : H.sections W) :
    pre W' (H.restrictHom i l).1 (H.restrictHom i l).2 = A.val.map i.op (pre W l.1 l.2) := by
  apply hinj W'
  beta_reduce
  change _ = algebraMap Γ(X, W') ((rationalFunctionsPresheaf X).obj (op W'))
    (show Γ(X, W') from φ.val.app (op W') (A.val.map i.op (pre W l.1 l.2)))
  rw [hpre, PresheafOfModules.naturality_apply]
  change (rationalFunctionsPresheaf X).map i.op l.1 =
    algebraMap Γ(X, W') ((rationalFunctionsPresheaf X).obj (op W'))
      (X.presheaf.map i.op (show Γ(X, W) from φ.val.app (op W) (pre W l.1 l.2)))
  rw [← rationalFunctionsPresheaf_map_algebraMap, hpre]

end Preimage

/-- Over an open `U`, `x ↦ (a ↦ φ(a) x)` is surjective from `𝓕(U)` onto `𝓗om(𝓐, 𝓖)(U)` as soon
as `φ` identifies `𝓐` with `𝓗` and `x ↦ (l ↦ x l)` is surjective from `𝓕(U)` onto the local
homomorphisms `𝓗|_U ⟶ 𝓖|_U`. -/
theorem surjective_mulInternalHom_app {F G H : RationalFunctionsSubmodule X} {A : X.Modules}
    {φ : A ⟶ SheafOfModules.unit X.ringCatSheaf} (h : MulInternalHomCond F G φ) (U : X.Opens)
    (hmem : ∀ (W : X.Opens) (a : A.val.obj (op W)),
      algebraMap Γ(X, W) ((rationalFunctionsPresheaf X).obj (op W))
        (show Γ(X, W) from φ.val.app (op W) a) ∈ H.sections W)
    (hinj : ∀ W : X.Opens, Function.Injective fun a : A.val.obj (op W) =>
      algebraMap Γ(X, W) ((rationalFunctionsPresheaf X).obj (op W))
        (show Γ(X, W) from φ.val.app (op W) a))
    (hsurj : ∀ (W : X.Opens) (l : ToType ((rationalFunctionsPresheaf X).obj (op W))),
      l ∈ H.sections W → ∃ a : A.val.obj (op W),
        algebraMap Γ(X, W) ((rationalFunctionsPresheaf X).obj (op W))
          (show Γ(X, W) from φ.val.app (op W) a) = l)
    (hmul : ∀ x ∈ F.sections U, ∀ (W : X.Opens) (i : W ⟶ U)
      (l : ToType ((rationalFunctionsPresheaf X).obj (op W))), l ∈ H.sections W →
        (rationalFunctionsPresheaf X).map i.op x * l ∈ G.sections W)
    (hsurj' : Function.Surjective fun x : F.sections U => mulLocalHom H G U x.1 (hmul x.1 x.2)) :
    Function.Surjective ((mulInternalHom h).val.app (op U)) := by
  choose pre hpre using hsurj
  intro β
  let ψ : LocalHom H G U :=
    { app := fun W hW =>
        { toFun := fun l => β.app (op (Over.mk (homOfLE hW))) (pre W l.1 l.2)
          map_add' := fun l₁ l₂ => by
            change β.app (op (Over.mk (homOfLE hW))) (pre W (l₁ + l₂).1 (l₁ + l₂).2) = _
            rw [preimage_add hinj hpre, map_add]
          map_smul' := fun r l => by
            change β.app (op (Over.mk (homOfLE hW))) (pre W (r • l).1 (r • l).2) = _
            rw [preimage_smul hinj hpre, map_smul]
            rfl }
      naturality := fun W W' hW i l => by
        change (show G.sections W' from β.app (op (Over.mk (homOfLE (i.le.trans hW))))
          (pre W' (H.restrictHom i l).1 (H.restrictHom i l).2)).1 =
          (rationalFunctionsPresheaf X).map i.op
            (show G.sections W from β.app (op (Over.mk (homOfLE hW))) (pre W l.1 l.2)).1
        rw [preimage_restrict hinj hpre]
        exact congrArg Subtype.val (PresheafOfModules.naturality_apply β
          (Over.homMk i : Over.mk (homOfLE (i.le.trans hW)) ⟶ Over.mk (homOfLE hW)).op
          (pre W l.1 l.2)) }
  obtain ⟨x, hx⟩ := hsurj' ψ
  refine ⟨x, restrFun_hom_ext fun W a => ?_⟩
  have := congrArg (fun ψ' : LocalHom H G U => (ψ'.app W.unop.left W.unop.hom.le
    ⟨_, hmem W.unop.left a⟩).1) hx
  change (rationalFunctionsPresheaf X).map (homOfLE W.unop.hom.le).op x.1 *
      algebraMap Γ(X, W.unop.left) ((rationalFunctionsPresheaf X).obj (op W.unop.left))
        (show Γ(X, W.unop.left) from φ.val.app (op W.unop.left) a) =
    (show G.sections W.unop.left from β.app (op (Over.mk (homOfLE W.unop.hom.le)))
      (pre W.unop.left _ (hmem W.unop.left a))).1 at this
  rwa [hinj W.unop.left (hpre W.unop.left _ (hmem W.unop.left a)),
    ← smul_eq_mul_algebraMap_app] at this

/-- Let `φ : 𝓐 ⟶ 𝒪_X` identify `𝓐`, through `𝒪_X ⟶ K(X)`, with a submodule `𝓗 ⊆ K(X)`. Over an
open `U`, `x ↦ (a ↦ φ(a) x)` is bijective from `𝓕(U)` onto `𝓗om(𝓐, 𝓖)(U)` as soon as
`x ↦ (l ↦ x l)` is a bijection from `𝓕(U)` onto the local homomorphisms `𝓗|_U ⟶ 𝓖|_U`. -/
theorem bijective_mulInternalHom_app {F G H : RationalFunctionsSubmodule X} {A : X.Modules}
    {φ : A ⟶ SheafOfModules.unit X.ringCatSheaf} (h : MulInternalHomCond F G φ) (U : X.Opens)
    (hmem : ∀ (W : X.Opens) (a : A.val.obj (op W)),
      algebraMap Γ(X, W) ((rationalFunctionsPresheaf X).obj (op W))
        (show Γ(X, W) from φ.val.app (op W) a) ∈ H.sections W)
    (hinj : ∀ W : X.Opens, Function.Injective fun a : A.val.obj (op W) =>
      algebraMap Γ(X, W) ((rationalFunctionsPresheaf X).obj (op W))
        (show Γ(X, W) from φ.val.app (op W) a))
    (hsurj : ∀ (W : X.Opens) (l : ToType ((rationalFunctionsPresheaf X).obj (op W))),
      l ∈ H.sections W → ∃ a : A.val.obj (op W),
        algebraMap Γ(X, W) ((rationalFunctionsPresheaf X).obj (op W))
          (show Γ(X, W) from φ.val.app (op W) a) = l)
    (hmul : ∀ x ∈ F.sections U, ∀ (W : X.Opens) (i : W ⟶ U)
      (l : ToType ((rationalFunctionsPresheaf X).obj (op W))), l ∈ H.sections W →
        (rationalFunctionsPresheaf X).map i.op x * l ∈ G.sections W)
    (hbij : Function.Bijective fun x : F.sections U => mulLocalHom H G U x.1 (hmul x.1 x.2)) :
    Function.Bijective ((mulInternalHom h).val.app (op U)) :=
  ⟨injective_mulInternalHom_app h U hsurj hmul hbij.1,
    surjective_mulInternalHom_app h U hmem hinj hsurj hmul hbij.2⟩

end MulInternalHom

end MMP.Flips
