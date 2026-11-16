module

public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.TwistGeneration
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.SerreFiniteness
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaInvertible.AmpleCriterion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPower
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.Canonical
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.SectionProduct.PullbackUnitSection
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.FreePresentation
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveAmbientSections

/-!
# Sections of high powers of a generated invertible module

Let `X` be proper over a Noetherian ring `R`, let `M` be an invertible `𝒪_X`-module and let
`σ₀, …, σ_N` be global sections of `M^{⊗ D}` generating it. Then all sufficiently high powers of
`M` are generated, over the section ring, by `N + 1` fixed sections of degree `D`: there is `N₀`
with every section of `M^{⊗ (D + n)}`, `n ≥ N₀`, of the form `∑ⱼ sⱼ · aⱼ`.

The argument is the standard one for a semiample invertible module. The `σⱼ` define a morphism
`g : X ⟶ ℙᴺ_R` with `g^* 𝒪(1) ≅ M^{⊗ D}`; `g` is proper. Write `n = r + D k` with `0 ≤ r < D`.
The direct image `g_*(M^{⊗ r})` is coherent, and Serre's theorem on `ℙᴺ_R` makes
`g_*(M^{⊗ r}) ⊗ (⨁ᵢ 𝒪 ⟶ 𝒪(1))`, twisted by `𝒪(k)`, surjective on global sections for `k ≫ 0`.
The projection formula `g_*(F) ⊗ H ≅ g_*(F ⊗ g^* H)` for invertible `H` carries this surjectivity
to `X`, and the global sections of a direct image are those of the module.

## Main results

* `MMP.SemiampleSections.exists_surjective_twistPowMap`: Serre's theorem in lifting form, for an
  epimorphism of coherent modules on a scheme proper over a Noetherian ring with an ample `O`.
* `MMP.SemiampleSections.surjective_of_surjective_pushforward`: transfer of surjectivity on
  sections along a morphism, through the projection formula.
* `MMP.SemiampleSections.exists_surjective_twistPowMap_pullback`: surjectivity of the high
  twists of `g^* Ψ ≫ θ`, for `θ : g^* O ≅ M^{⊗ D}`.
* `MMP.SemiampleSections.exists_forall_eq_sum_mul_of_generatesStalks`: the generation statement.

## Implementation notes

Two spellings of the tensor product of `𝒪_X`-modules are in play: the monoidal structure
`Stacks.SheafInternalHom.schemeMonoidalCategory`, in which the section ring and the twists
`Stacks.TwistedSections.twistPowMap` are written, and the sheafified tensor product
`Stacks.SheafOfModules.Tensor.sheafTensor`, in which the projection formula is stated. They are
compared by `MMP.SemiampleSections.tensorRightIsoSheafTensorRight` and
`MMP.SemiampleSections.tensorLeftIsoSheafTensorLeft`; every transfer of surjectivity goes through an
isomorphism of arrows (`MMP.SemiampleSections.surjective_map_of_arrowIso`) or a commutative
square with an invertible edge (`MMP.SemiampleSections.surjective_map_of_square`).

## References

* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Prod

universe u

namespace MMP.SemiampleSections

/-! ### Iterates of an endofunctor -/

section Iterate

variable {C : Type*} [Category C]

/-- The `k`-fold iterate of an endofunctor, composing on the right. -/
def iter (T : C ⥤ C) : ℕ → (C ⥤ C)
  | 0 => 𝟭 C
  | k + 1 => iter T k ⋙ T

/-- The `0`-fold iterate of `T` is the identity functor. -/
@[simp]
theorem iter_zero (T : C ⥤ C) : iter T 0 = 𝟭 C := rfl

/-- The `(k + 1)`-fold iterate of `T` is the `k`-fold iterate followed by `T`. -/
theorem iter_succ (T : C ⥤ C) (k : ℕ) : iter T (k + 1) = iter T k ⋙ T := rfl

/-- Isomorphic endofunctors have isomorphic iterates. -/
def iterIso {T T' : C ⥤ C} (ν : T ≅ T') : (k : ℕ) → (iter T k ≅ iter T' k)
  | 0 => Iso.refl _
  | k + 1 => Functor.isoWhiskerRight (iterIso ν k) T ≪≫ Functor.isoWhiskerLeft (iter T' k) ν

/-- Iterating `T` `a + b` times is iterating it `a` times and then `b` times. -/
def iterAddIso (T : C ⥤ C) (a : ℕ) : (b : ℕ) → (iter T (a + b) ≅ iter T a ⋙ iter T b)
  | 0 => (Functor.rightUnitor _).symm
  | b + 1 => Functor.isoWhiskerRight (iterAddIso T a b) T

/-- Iterating `D * k` times is iterating the `D`-fold iterate `k` times. -/
def iterMulIso (T : C ⥤ C) (D : ℕ) : (k : ℕ) → (iter T (D * k) ≅ iter (iter T D) k)
  | 0 => Iso.refl _
  | k + 1 => iterAddIso T (D * k) D ≪≫ Functor.isoWhiskerRight (iterMulIso T D k) (iter T D)

variable {D : Type*} [Category D]

/-- A transformation `F ⋙ T ⟶ T' ⋙ F` iterates to `F ⋙ T^k ⟶ T'^k ⋙ F`. -/
def iterComm (F : C ⥤ D) (T : D ⥤ D) (T' : C ⥤ C) (α : F ⋙ T ⟶ T' ⋙ F) :
    (k : ℕ) → (F ⋙ iter T k ⟶ iter T' k ⋙ F)
  | 0 => 𝟙 F
  | k + 1 => Functor.whiskerRight (iterComm F T T' α k) T ≫
      Functor.whiskerLeft (iter T' k) α

/-- The iterate of an invertible transformation `F ⋙ T ⟶ T' ⋙ F` is invertible. -/
instance isIso_iterComm (F : C ⥤ D) (T : D ⥤ D) (T' : C ⥤ C) (α : F ⋙ T ⟶ T' ⋙ F)
    [IsIso α] : ∀ k, IsIso (iterComm F T T' α k)
  | 0 => inferInstanceAs (IsIso (𝟙 F))
  | k + 1 => by
    have := isIso_iterComm F T T' α k
    exact inferInstanceAs (IsIso (Functor.whiskerRight (iterComm F T T' α k) T ≫
      Functor.whiskerLeft (iter T' k) α))

end Iterate

/-! ### Surjectivity on a functor to types, along isomorphisms of arrows -/

section Surj

variable {C : Type*} [Category C] (Φ : C ⥤ Type*)

/-- Surjectivity transfers along a commutative square whose right edge is an isomorphism. -/
theorem surjective_map_of_square {A B A' B' : C} (φ : A ⟶ B) (φ' : A' ⟶ B') (a : A ⟶ A')
    (b : B ⟶ B') [IsIso b] (w : φ ≫ b = a ≫ φ') (hφ : Function.Surjective (Φ.map φ)) :
    Function.Surjective (Φ.map φ') := by
  intro y
  obtain ⟨x, hx⟩ := hφ (Φ.map (inv b) y)
  refine ⟨Φ.map a x, ?_⟩
  rw [← types_comp_apply (Φ.map a) (Φ.map φ'), ← Φ.map_comp, ← w, Φ.map_comp,
    types_comp_apply, hx, ← types_comp_apply (Φ.map (inv b)) (Φ.map b), ← Φ.map_comp]
  simp

/-- Surjectivity of `Φ` on an arrow transfers along an isomorphism of arrows. -/
theorem surjective_map_of_arrowIso {f g : Arrow C} (e : f ≅ g)
    (hf : Function.Surjective (Φ.map f.hom)) : Function.Surjective (Φ.map g.hom) :=
  surjective_map_of_square Φ f.hom g.hom e.hom.left e.hom.right e.hom.w.symm hf

end Surj

/-! ### Iterated whiskering in a braided monoidal category -/

section Monoidal

open Stacks.TwistedSections Stacks.TensorPowers
open Stacks.AlgebraicGeometry.ProperAmpleCohomology (twistPowIsoTensor)

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- Iterating `- ⊗ L` is `Stacks.TwistedSections.twistPowMap`, as arrows. -/
theorem arrow_twistPowMap (L : C) {A B : C} (φ : A ⟶ B) :
    ∀ k : ℕ, Arrow.mk (twistPowMap L φ k) = (iter (tensorRight L) k).mapArrow.obj (Arrow.mk φ)
  | 0 => rfl
  | k + 1 => by
    change (tensorRight L).mapArrow.obj (Arrow.mk (twistPowMap L φ k)) = _
    rw [arrow_twistPowMap L φ k]
    rfl

/-- Whiskering `a` and then `b` times is whiskering `a + b` times, as arrows. -/
theorem arrow_twistPowMap_twistPowMap (L : C) {A B : C} (φ : A ⟶ B) (a : ℕ) :
    ∀ b : ℕ, Arrow.mk (twistPowMap L (twistPowMap L φ a) b) = Arrow.mk (twistPowMap L φ (a + b))
  | 0 => rfl
  | b + 1 => by
    change (tensorRight L).mapArrow.obj (Arrow.mk (twistPowMap L (twistPowMap L φ a) b)) =
      (tensorRight L).mapArrow.obj (Arrow.mk (twistPowMap L φ (a + b)))
    rw [arrow_twistPowMap_twistPowMap L φ a b]

/-- Naturality in `φ`: `twistPowMap L φ n` followed by `twistPowIsoTensor B L n` equals
`twistPowIsoTensor A L n` followed by `φ ▷ L^{⊗ n}`. -/
theorem twistPowMap_twistPowIsoTensor (L : C) {A B : C} (φ : A ⟶ B) :
    ∀ n : ℕ, twistPowMap L φ n ≫ (twistPowIsoTensor B L n).hom =
      (twistPowIsoTensor A L n).hom ≫ φ ▷ natTensorPow L n
  | 0 => by
    change φ ≫ (ρ_ B).inv = (ρ_ A).inv ≫ φ ▷ 𝟙_ C
    simp
  | n + 1 => by
    change twistPowMap L φ n ▷ L ≫
        ((twistPowIsoTensor B L n).hom ▷ L ≫
          (α_ B (natTensorPow L n) L).hom) =
      ((twistPowIsoTensor A L n).hom ▷ L ≫
          (α_ A (natTensorPow L n) L).hom) ≫ φ ▷ (natTensorPow L n ⊗ L)
    rw [← Category.assoc, ← comp_whiskerRight, twistPowMap_twistPowIsoTensor L φ n,
      comp_whiskerRight, Category.assoc, Category.assoc, associator_naturality_left]

/-- `twistPowMap L φ n` is `φ ▷ L^{⊗ n}`, up to isomorphism of arrows. -/
def twistPowMapArrowIso (L : C) {A B : C} (φ : A ⟶ B) (n : ℕ) :
    Arrow.mk (twistPowMap L φ n) ≅ Arrow.mk (φ ▷ natTensorPow L n) :=
  Arrow.isoMk (twistPowIsoTensor A L n) (twistPowIsoTensor B L n)
    (twistPowMap_twistPowIsoTensor L φ n).symm

/-- The `D`-fold iterate of `- ⊗ L` is `- ⊗ L^{⊗ D}`. -/
def iterTensorRightIso (L : C) :
    (D : ℕ) → (iter (tensorRight L) D ≅ tensorRight (natTensorPow L D))
  | 0 => NatIso.ofComponents (fun X => (ρ_ X).symm) (fun f => by
      change f ≫ (ρ_ _).inv = (ρ_ _).inv ≫ f ▷ 𝟙_ C
      simp)
  | D + 1 => Functor.isoWhiskerRight (iterTensorRightIso L D) (tensorRight L) ≪≫
      (tensorRightTensor (natTensorPow L D) L).symm

/-- Whiskering `D * k` times by `L` is whiskering `k` times by `L^{⊗ D}`, as arrows. -/
def twistPowMapMulArrowIso (L : C) {A B : C} (φ : A ⟶ B) (D k : ℕ) :
    Arrow.mk (twistPowMap L φ (D * k)) ≅ Arrow.mk (twistPowMap (natTensorPow L D) φ k) :=
  eqToIso (arrow_twistPowMap L φ (D * k)) ≪≫
    ((Functor.mapArrowFunctor C C).mapIso
      (iterMulIso (tensorRight L) D k ≪≫ iterIso (iterTensorRightIso L D) k)).app (Arrow.mk φ) ≪≫
    eqToIso (arrow_twistPowMap (natTensorPow L D) φ k).symm

variable [BraidedCategory C]

/-- Whiskering on the right and on the left agree up to the braiding, as arrows. -/
def whiskerRightArrowIso {A B : C} (φ : A ⟶ B) (Z : C) :
    Arrow.mk (φ ▷ Z) ≅ Arrow.mk (Z ◁ φ) :=
  Arrow.isoMk (β_ A Z) (β_ B Z) (BraidedCategory.braiding_naturality_left φ Z).symm

end Monoidal

/-! ### The scheme-level comparisons -/

section Scheme

open AlgebraicGeometry Stacks.TwistedSections Stacks.TensorPowers

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-- The global sections of an `𝒪_X`-module, as a functor to types. -/
abbrev gammaTop (X : Scheme.{u}) : X.Modules ⥤ Type u :=
  Scheme.Modules.toPresheaf X ⋙ (evaluation _ _).obj (op ⊤) ⋙ forget Ab.{u}

/-- Tensoring on the right by `L`, in the sheafified-tensor spelling of
`Stacks.SheafOfModules.Tensor.sheafTensor` in which the projection formula is stated. -/
abbrev sheafTensorRight {X : Scheme.{u}} (L : X.Modules) : X.Modules ⥤ X.Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).flip.obj L

/-- Tensoring on the left by `G`, in the sheafified-tensor spelling, as an endofunctor of
`X.Modules`. -/
abbrev sheafTensorLeft {X : Scheme.{u}} (G : X.Modules) : X.Modules ⥤ X.Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj G

/-- The monoidal tensor product of `X.Modules` and the sheafified tensor product agree, naturally
in the left factor. -/
def tensorRightIsoSheafTensorRight {X : Scheme.{u}} (L : X.Modules) :
    tensorRight L ≅ sheafTensorRight L :=
  (BraidedCategory.tensorLeftIsoTensorRight L).symm ≪≫
    Stacks.SheafInternalHom.tensorLeftIso X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L ≪≫
    Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L

/-- The monoidal tensor product of `X.Modules` and the sheafified tensor product agree, naturally
in the right factor. -/
def tensorLeftIsoSheafTensorLeft {X : Scheme.{u}} (G : X.Modules) :
    tensorLeft G ≅ sheafTensorLeft G :=
  Stacks.SheafInternalHom.tensorLeftIso X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) G

/-- The uncurried bifunctor applied to `f ×ₘ 𝟙 b` is `F` applied to `f` with `b` fixed. -/
theorem uncurry_map_id_right {A B E : Type*} [Category A] [Category B] [Category E]
    (F : A ⥤ B ⥤ E) {a a' : A} (f : a ⟶ a') (b : B) :
    (Functor.uncurry.obj F).map (f ×ₘ 𝟙 b) = (F.flip.obj b).map f := by simp

/-- The uncurried bifunctor applied to `𝟙 a ×ₘ f` is `F.obj a` applied to `f`. -/
theorem uncurry_map_id_left {A B E : Type*} [Category A] [Category B] [Category E]
    (F : A ⥤ B ⥤ E) (a : A) {b b' : B} (f : b ⟶ b') :
    (Functor.uncurry.obj F).map (𝟙 a ×ₘ f) = (F.obj a).map f := by simp

/-- **The projection formula morphism** `g_* G ⊗ H ⟶ g_*(G ⊗ g^* H)` of
`Stacks.ProjectionFormula.projectionFormulaMap'`, as a natural transformation in `G`. -/
def projectionFormulaNatTrans {X Y : Scheme.{u}} (g : X ⟶ Y) (H : Y.Modules) :
    Scheme.Modules.pushforward g ⋙ sheafTensorRight H ⟶
      sheafTensorRight ((Scheme.Modules.pullback g).obj H) ⋙ Scheme.Modules.pushforward g where
  app G := Stacks.ProjectionFormula.projectionFormulaMap' g.toLRSHom.toShHom G H
  naturality G G' φ := by
    have := Stacks.ProjectionFormula.projectionFormulaMap'_natural g.toLRSHom.toShHom φ (𝟙 H)
    erw [uncurry_map_id_right, CategoryTheory.Functor.map_id, uncurry_map_id_right] at this
    exact this

/-- The projection formula morphism is an isomorphism when `H` is invertible. -/
instance isIso_projectionFormulaNatTrans {X Y : Scheme.{u}} (g : X ⟶ Y) (H : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y H] : IsIso (projectionFormulaNatTrans g H) := by
  have := Stacks.ProjectionFormula.isInvertible_of_isInvertibleModule Y H
  have : ∀ G, IsIso ((projectionFormulaNatTrans g H).app G) := fun G =>
    Stacks.ProjectionFormula.isIso_projectionFormulaMap g.toLRSHom.toShHom G H
  exact NatIso.isIso_of_isIso_app _

/-- The projection formula morphism is natural in the module on the target. -/
theorem projectionFormulaNatTrans_app_naturality_right {X Y : Scheme.{u}} (g : X ⟶ Y)
    (F : X.Modules) {H₁ H₂ : Y.Modules} (e : H₁ ⟶ H₂) :
    (sheafTensorLeft ((Scheme.Modules.pushforward g).obj F)).map e ≫
        (projectionFormulaNatTrans g H₂).app F =
      (projectionFormulaNatTrans g H₁).app F ≫ (Scheme.Modules.pushforward g).map
        ((sheafTensorLeft F).map ((Scheme.Modules.pullback g).map e)) := by
  have := Stacks.ProjectionFormula.projectionFormulaMap'_natural g.toLRSHom.toShHom (𝟙 F) e
  erw [CategoryTheory.Functor.map_id, uncurry_map_id_left, uncurry_map_id_left] at this
  exact this

/-- **Transfer of surjectivity along a morphism to `P`.** If, after `k` twists by an invertible
`O` on `P`, the map `g_* F ⊗ H₁ ⟶ g_* F ⊗ H₂` induced by `e : H₁ ⟶ H₂` (with `H₂` invertible) is
surjective on global sections, then so is the map `F ⊗ g^* H₁ ⟶ F ⊗ g^* H₂` on `X` after `k`
twists by `g^* O`. -/
theorem surjective_of_surjective_pushforward {X P : Scheme.{u}} (g : X ⟶ P) (O : P.Modules)
    [Stacks.Ample.IsInvertibleModule P O] (F : X.Modules) {H₁ H₂ : P.Modules}
    [Stacks.Ample.IsInvertibleModule P H₂] (e : H₁ ⟶ H₂) (k : ℕ)
    (h : Function.Surjective ((gammaTop P).map ((iter (sheafTensorRight O) k).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor P.toRingedSpace.sheaf).obj
        ((Scheme.Modules.pushforward g).obj F)).map e)))) :
    Function.Surjective ((gammaTop X).map
      ((iter (sheafTensorRight ((Scheme.Modules.pullback g).obj O)) k).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj F).map
          ((Scheme.Modules.pullback g).map e)))) := by
  let γ := iterComm (Scheme.Modules.pushforward g) (sheafTensorRight O)
    (sheafTensorRight ((Scheme.Modules.pullback g).obj O)) (projectionFormulaNatTrans g O) k
  let b := (iter (sheafTensorRight O) k).map ((projectionFormulaNatTrans g H₂).app F) ≫
    γ.app _
  let a := (iter (sheafTensorRight O) k).map ((projectionFormulaNatTrans g H₁).app F) ≫
    γ.app _
  have : IsIso ((projectionFormulaNatTrans g H₂).app F) := inferInstance
  have : IsIso b := by dsimp only [b]; infer_instance
  have key : Function.Surjective ((gammaTop P).map ((Scheme.Modules.pushforward g).map
      ((iter (sheafTensorRight ((Scheme.Modules.pullback g).obj O)) k).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj F).map
          ((Scheme.Modules.pullback g).map e))))) := by
    refine surjective_map_of_square (gammaTop P) _ _ a b ?_ h
    have hn : (iter (sheafTensorRight O) k).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor P.toRingedSpace.sheaf).obj
          ((Scheme.Modules.pushforward g).obj F)).map e) ≫
          (iter (sheafTensorRight O) k).map ((projectionFormulaNatTrans g H₂).app F) =
        (iter (sheafTensorRight O) k).map ((projectionFormulaNatTrans g H₁).app F) ≫
          (iter (sheafTensorRight O) k).map ((Scheme.Modules.pushforward g).map
            (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj F).map
              ((Scheme.Modules.pullback g).map e))) :=
      ((iter (sheafTensorRight O) k).map_comp _ _).symm.trans
        ((congrArg (iter (sheafTensorRight O) k).map
          (projectionFormulaNatTrans_app_naturality_right g F e)).trans
          ((iter (sheafTensorRight O) k).map_comp _ _))
    have w : (iter (sheafTensorRight O) k).map ((Scheme.Modules.pushforward g).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj F).map
          ((Scheme.Modules.pullback g).map e))) ≫ γ.app _ =
        γ.app _ ≫ (Scheme.Modules.pushforward g).map
          ((iter (sheafTensorRight ((Scheme.Modules.pullback g).obj O)) k).map
            (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj F).map
              ((Scheme.Modules.pullback g).map e))) :=
      γ.naturality _
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ γ.app _) hn).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) w).trans (Category.assoc _ _ _).symm)))
  exact key

/-- **Serre's theorem, lifting form.** On a scheme proper over a Noetherian ring with an ample
invertible `O`, every epimorphism of coherent modules is surjective on global sections after
enough twists by `O`. -/
theorem exists_surjective_twistPowMap {P : Scheme.{u}} {R : Type u} [CommRing R]
    [IsNoetherianRing R] (π : P ⟶ Spec (CommRingCat.of R)) [IsProper π] (O : P.Modules)
    [Stacks.Ample.IsInvertibleModule P O] (hO : Stacks.Ample.IsAmple P O) {A B : P.Modules}
    [hA : A.IsCoherent] [hB : B.IsCoherent] (ψ : A ⟶ B) [hψ : Epi ψ] :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → Function.Surjective ((gammaTop P).map (twistPowMap O ψ k)) := by
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) :=
    isLocallyNoetherian_Spec.mpr inferInstance
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian π
  have : (kernel ψ).IsCoherent := _root_.SheafOfModules.kernel_isCoherent ψ
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist π
      (kernel ψ) O hO
  refine ⟨d₀, fun k hk => ?_⟩
  have hz := Stacks.AlgebraicGeometry.ProperAmpleCohomology.isZero_Hgroup_twistPow P (kernel ψ) O
    1 k (hd₀ k 1 hk Nat.one_pos)
  have hzero := (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    P.ringCatSheaf ⊤ 1 _).mpr hz
  exact Stacks.Cohomology.surjective_sections_of_isZero_firstCohomology P ⊤
    (Stacks.AlgebraicGeometry.ProperAmpleCohomology.shortExact_twistShortComplex O ψ k) hzero

/-- **Serre's theorem for a twisted quotient of a free module.** On `P` proper over a
Noetherian ring with an ample invertible `O`, let `Ψ : ⨁ᵢ 𝒪_P ⟶ O` be an epimorphism and `G` a
coherent module. Then `G ⊗ Ψ`, twisted `k` times by `O`, is surjective on global sections for all
large `k`. -/
theorem exists_surjective_sheafTensor_map {P : Scheme.{u}} {R : Type u} [CommRing R]
    [IsNoetherianRing R] (π : P ⟶ Spec (CommRingCat.of R)) [IsProper π] (O : P.Modules)
    [Stacks.Ample.IsInvertibleModule P O] (hO : Stacks.Ample.IsAmple P O) {r : ℕ}
    (Ψ : (⨁ fun _ : Fin r => 𝟙_ P.Modules) ⟶ O) [Epi Ψ] (G : P.Modules) [G.IsCoherent] :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → Function.Surjective ((gammaTop P).map
      ((iter (sheafTensorRight O) k).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor P.toRingedSpace.sheaf).obj G).map Ψ))) := by
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) :=
    isLocallyNoetherian_Spec.mpr inferInstance
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian π
  have hsum : (⨁ fun _ : Fin r => 𝟙_ P.Modules).IsCoherent :=
    Stacks.AlgebraicGeometry.RelativeSerreVanishing.isCoherent_bicone
      (biproduct.isBilimit (fun _ : Fin r => 𝟙_ P.Modules))
      fun _ => Stacks.AlgebraicGeometry.ProperAmpleCohomology.isCoherent_tensorUnit P
  have hA : (((Stacks.SheafOfModules.Tensor.sheafTensor P.toRingedSpace.sheaf).obj G).obj
      (⨁ fun _ : Fin r => 𝟙_ P.Modules : P.Modules) : P.Modules).IsCoherent :=
    @AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent P.toRingedSpace G _ ‹_› hsum
  have hB : (((Stacks.SheafOfModules.Tensor.sheafTensor P.toRingedSpace.sheaf).obj G).obj
      O : P.Modules).IsCoherent :=
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible P G O
  have hepi : Epi (C := P.Modules)
      (((Stacks.SheafOfModules.Tensor.sheafTensor P.toRingedSpace.sheaf).obj G).map Ψ) := by
    have hΨ : Epi (C := SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf P.toRingedSpace.sheaf)) Ψ := ‹Epi Ψ›
    exact @preserves_epi_of_preservesColimit _ _ _ _ _ _ _ Ψ
      (_root_.SheafOfModules.preservesColimitsOfSize_sheafTensor_obj P.toRingedSpace.sheaf G _) hΨ
  obtain ⟨k₀, hk₀⟩ := exists_surjective_twistPowMap π O hO (hA := hA) (hB := hB)
    (((Stacks.SheafOfModules.Tensor.sheafTensor P.toRingedSpace.sheaf).obj G).map Ψ)
    (hψ := hepi)
  refine ⟨k₀, fun k hk => ?_⟩
  let χ : (((Stacks.SheafOfModules.Tensor.sheafTensor P.toRingedSpace.sheaf).obj G).obj
      (⨁ fun _ : Fin r => 𝟙_ P.Modules : P.Modules) : P.Modules) ⟶
      (((Stacks.SheafOfModules.Tensor.sheafTensor P.toRingedSpace.sheaf).obj G).obj O :
        P.Modules) :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor P.toRingedSpace.sheaf).obj G).map Ψ
  have e : Arrow.mk (twistPowMap O χ k) ≅
      (iter (sheafTensorRight O) k).mapArrow.obj (Arrow.mk χ) :=
    eqToIso (@arrow_twistPowMap P.Modules _ (Stacks.SheafInternalHom.schemeMonoidalCategory P)
      O _ _ χ k) ≪≫
      ((Functor.mapArrowFunctor P.Modules P.Modules).mapIso
        (iterIso (tensorRightIsoSheafTensorRight O) k)).app (Arrow.mk χ)
  have h1 : Function.Surjective ((gammaTop P).map (Arrow.mk (twistPowMap O χ k)).hom) :=
    hk₀ k hk
  have h2 : Function.Surjective ((gammaTop P).map
      ((iter (sheafTensorRight O) k).mapArrow.obj (Arrow.mk χ)).hom) :=
    surjective_map_of_arrowIso (gammaTop P) e h1
  exact h2

/-- Multiplication by a section of `L^{⊗ D}` is its iterated whiskering, up to the identifications
of the twisted unit and of the twisted power with tensor powers. -/
theorem mulMap_eq_twistPowMap {X : Scheme.{u}} (M : X.Modules) {D : ℕ}
    (s : Stacks.GradedSections.powSections M D) :
    ∀ n : ℕ, Stacks.GradedSections.mulMap s n =
      eqToHom (Stacks.SectionRingProjTheta.twistPow_unit M n).symm ≫ twistPowMap M s n ≫
        eqToHom (Stacks.AlgebraicGeometry.ProperAmpleCohomology.twistPow_natTensorPow M D n)
  | 0 => by
    change s = 𝟙 _ ≫ s ≫ 𝟙 _
    simp
  | n + 1 => by
    rw [Stacks.GradedSections.mulMap_succ, mulMap_eq_twistPowMap M s n, twistPowMap_succ,
      comp_whiskerRight, comp_whiskerRight, eqToHom_whiskerRight, eqToHom_whiskerRight]
    rfl

/-- **Generation of high powers from surjectivity on sections.** Let `ψ : Q ⟶ M^{⊗ D}` be the sum
`∑ᵢ pᵢ ≫ sᵢ` of maps factoring through `𝒪_X`. If `ψ` twisted `n` times by `M` is surjective on
global sections, then every section of `M^{⊗ (D + n)}` is `∑ᵢ sᵢ · aᵢ` with `aᵢ` sections of
`M^{⊗ n}`. -/
theorem exists_eq_sum_mul_of_surjective {X : Scheme.{u}} (M : X.Modules) {D : ℕ} {ι : Type*}
    [Fintype ι] {Q : X.Modules} (ψ : Q ⟶ natTensorPow M D) (p : ι → (Q ⟶ 𝟙_ X.Modules))
    (s : ι → Stacks.GradedSections.powSections M D) (hps : ∑ i, p i ≫ s i = ψ) (n : ℕ)
    (h : Function.Surjective ((gammaTop X).map (twistPowMap M ψ n)))
    (u : Stacks.GradedSections.powSections M (D + n)) :
    ∃ a : ι → Stacks.GradedSections.powSections M n,
      u = ∑ i, Stacks.GradedSections.mul (s i) (a i) := by
  set hJ := Stacks.AlgebraicGeometry.ProperAmpleCohomology.twistPow_natTensorPow M D n
  set h1 := Stacks.SectionRingProjTheta.twistPow_unit M n
  obtain ⟨x, hx⟩ := h (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _
    (u ≫ eqToHom hJ.symm))
  set v := (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).symm x
  have hv : v ≫ twistPowMap M ψ n = u ≫ eqToHom hJ.symm := by
    apply (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).injective
    rw [Stacks.AlgebraicGeometry.ProperAmpleCohomology.schemeGlobalSectionsAddEquiv_comp]
    exact (congrArg _ (AddEquiv.apply_symm_apply
      (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (twistPow Q M n))
      (show Γ(twistPow Q M n, ⊤) from x))).trans hx
  refine ⟨fun i => v ≫ twistPowMap M (p i) n ≫ eqToHom h1, ?_⟩
  have hsum : twistPowMap M ψ n = ∑ i, twistPowMap M (p i) n ≫ twistPowMap M (s i) n := by
    rw [← hps, Stacks.AlgebraicGeometry.ProperAmpleCohomology.twistPowMap_sum]
    exact Finset.sum_congr rfl fun i _ => twistPowMap_comp _ _ _
  calc u = (v ≫ twistPowMap M ψ n) ≫ eqToHom hJ := by
        rw [hv]
        simp
    _ = ∑ i, Stacks.GradedSections.mul (s i) (v ≫ twistPowMap M (p i) n ≫ eqToHom h1) := by
      rw [hsum, Preadditive.comp_sum, Preadditive.sum_comp]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Stacks.GradedSections.mul_def, mulMap_eq_twistPowMap]
      simp

/-- The sheafified-tensor twist and the monoidal twist have the same surjectivity on sections. -/
theorem surjective_iter_tensorRight_of_sheafTensor {X : Scheme.{u}} {E F Q : X.Modules}
    (φ : Q ⟶ E) (k : ℕ)
    (h : Function.Surjective ((gammaTop X).map ((iter (sheafTensorRight E) k).map
      ((sheafTensorLeft F).map φ)))) :
    Function.Surjective ((gammaTop X).map ((iter (tensorRight E) k).map (F ◁ φ))) := by
  have e1 : (iter (sheafTensorRight E) k).mapArrow.obj
        ((sheafTensorLeft F).mapArrow.obj (Arrow.mk φ)) ≅
      (iter (tensorRight E) k).mapArrow.obj (Arrow.mk (F ◁ φ)) :=
    (iter (sheafTensorRight E) k).mapArrow.mapIso
        (((Functor.mapArrowFunctor X.Modules X.Modules).mapIso
          (tensorLeftIsoSheafTensorLeft F)).app (Arrow.mk φ)).symm ≪≫
      (((Functor.mapArrowFunctor X.Modules X.Modules).mapIso
        (iterIso (tensorRightIsoSheafTensorRight E) k)).app (Arrow.mk (F ◁ φ))).symm
  have h0 : Function.Surjective ((gammaTop X).map ((iter (sheafTensorRight E) k).mapArrow.obj
        ((sheafTensorLeft F).mapArrow.obj (Arrow.mk φ))).hom) := h
  have h1 : Function.Surjective ((gammaTop X).map
      ((iter (tensorRight E) k).mapArrow.obj (Arrow.mk (F ◁ φ))).hom) :=
    surjective_map_of_arrowIso (gammaTop X) e1 h0
  exact h1

/-- For `θ : E ≅ J`, if `F ◁ φ` twisted `k` times by `E` is surjective on global sections, then so
is `F ◁ (φ ≫ θ.hom)` twisted `k` times by `J`. -/
theorem surjective_iter_whiskerLeft_comp {X : Scheme.{u}} {E J F Q : X.Modules} (θ : E ≅ J)
    (φ : Q ⟶ E) (k : ℕ)
    (h : Function.Surjective ((gammaTop X).map ((iter (tensorRight E) k).map (F ◁ φ)))) :
    Function.Surjective ((gammaTop X).map
      ((iter (tensorRight J) k).map (F ◁ (φ ≫ θ.hom)))) := by
  have e2 : (iter (tensorRight E) k).mapArrow.obj (Arrow.mk (F ◁ φ)) ≅
      (iter (tensorRight J) k).mapArrow.obj (Arrow.mk (F ◁ φ)) :=
    ((Functor.mapArrowFunctor X.Modules X.Modules).mapIso
      (iterIso ((tensoringRight X.Modules).mapIso θ) k)).app (Arrow.mk (F ◁ φ))
  have h2 : Function.Surjective ((gammaTop X).map
      ((iter (tensorRight J) k).mapArrow.obj (Arrow.mk (F ◁ φ))).hom) :=
    surjective_map_of_arrowIso (gammaTop X) e2 h
  refine surjective_map_of_square (gammaTop X) _ _ (𝟙 _)
    ((iter (tensorRight J) k).map (F ◁ θ.hom)) ?_ h2
  change (iter (tensorRight J) k).map (F ◁ φ) ≫ (iter (tensorRight J) k).map (F ◁ θ.hom) =
    𝟙 _ ≫ (iter (tensorRight J) k).map (F ◁ (φ ≫ θ.hom))
  rw [Category.id_comp, ← Functor.map_comp, ← MonoidalCategory.whiskerLeft_comp]

/-- **From the sheafified-tensor twist by `E` to the twist by `M`.** Let `θ : E ≅ M^{⊗ D}` and
`φ : Q ⟶ E`. If `M^{⊗ r} ⊗ φ`, twisted `k` times by `E` in the sheafified-tensor spelling, is
surjective on global sections, then so is `φ ≫ θ` twisted `r + D k` times by `M`. -/
theorem surjective_twistPowMap_of_surjective_sheafTensor {X : Scheme.{u}} (M : X.Modules)
    {D : ℕ} {E : X.Modules} (θ : E ≅ natTensorPow M D) {Q : X.Modules} (φ : Q ⟶ E) (r k : ℕ)
    (h : Function.Surjective ((gammaTop X).map ((iter (sheafTensorRight E) k).map
      ((sheafTensorLeft (natTensorPow M r)).map φ)))) :
    Function.Surjective ((gammaTop X).map (twistPowMap M (φ ≫ θ.hom) (r + D * k))) := by
  have h3 := surjective_iter_whiskerLeft_comp θ φ k
    (surjective_iter_tensorRight_of_sheafTensor φ k h)
  have e4 : (iter (tensorRight (natTensorPow M D)) k).mapArrow.obj
        (Arrow.mk (natTensorPow M r ◁ (φ ≫ θ.hom))) ≅
      Arrow.mk (twistPowMap M (φ ≫ θ.hom) (r + D * k)) :=
    (iter (tensorRight (natTensorPow M D)) k).mapArrow.mapIso
      ((whiskerRightArrowIso (φ ≫ θ.hom) (natTensorPow M r)).symm ≪≫
        (twistPowMapArrowIso M (φ ≫ θ.hom) r).symm) ≪≫
    eqToIso (arrow_twistPowMap (natTensorPow M D) (twistPowMap M (φ ≫ θ.hom) r) k).symm ≪≫
      (twistPowMapMulArrowIso M (twistPowMap M (φ ≫ θ.hom) r) D k).symm ≪≫
      eqToIso (arrow_twistPowMap_twistPowMap M (φ ≫ θ.hom) r (D * k))
  have h3' : Function.Surjective ((gammaTop X).map
      ((iter (tensorRight (natTensorPow M D)) k).mapArrow.obj
        (Arrow.mk (natTensorPow M r ◁ (φ ≫ θ.hom)))).hom) := h3
  have h4 : Function.Surjective ((gammaTop X).map
      (Arrow.mk (twistPowMap M (φ ≫ θ.hom) (r + D * k))).hom) :=
    surjective_map_of_arrowIso (gammaTop X) e4 h3'
  exact h4

/-- A finite family of global sections generating an invertible module presents it as a quotient
of a finite biproduct of copies of `𝒪_X`. -/
theorem exists_epi_biproduct_of_generatesStalks {P : Scheme.{u}} {O : P.Modules}
    [Stacks.Ample.IsInvertibleModule P O] {n : ℕ} (T : Fin n → Γ(O, ⊤))
    (hT : Stacks.ProjectiveFromSections.GeneratesStalks T) :
    ∃ Ψ : (⨁ fun _ : Fin n => 𝟙_ P.Modules) ⟶ O, Epi Ψ := by
  have hT' : Stacks.ProjectiveFromSections.GeneratesStalks
      (fun i : ULift.{u} (Fin n) => T i.down) :=
    Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x =>
      let ⟨i, hi⟩ := Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks T hT x
      ⟨⟨i⟩, hi⟩
  let τ : O.GeneratingSections :=
    { I := ULift.{u} (Fin n)
      s := fun i => (Stacks.NonvanishingSpelling.sectionsEquiv P O).symm (T i.down)
      epi := Stacks.ProjectiveFromSections.epi_freeHomEquiv_symm_of_generatesStalks _ hT' }
  exact ⟨Stacks.AlgebraicGeometry.ProperAmpleCohomology.generatingSectionsBiproductHom τ
    Equiv.ulift, inferInstance⟩

/-- **Surjectivity on sections of high twists, through a morphism to a projective scheme.** Let
`g : X ⟶ P` be proper with `X` and `P` proper over a Noetherian ring, `O` ample invertible on `P`
with an epimorphism `Ψ : ⨁ᵢ 𝒪_P ⟶ O`, and `θ : g^* O ≅ M^{⊗ D}`. Then for every `r`, the
morphism `g^* Ψ ≫ θ`, twisted `r + D k` times by `M`, is surjective on global sections for all
large `k`. -/
theorem exists_surjective_twistPowMap_pullback {X P : Scheme.{u}} {R : Type u} [CommRing R]
    [IsNoetherianRing R] (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (π : P ⟶ Spec (CommRingCat.of R)) [IsProper π] (g : X ⟶ P) [IsProper g] (O : P.Modules)
    [Stacks.Ample.IsInvertibleModule P O] (hO : Stacks.Ample.IsAmple P O) {m : ℕ}
    (Ψ : (⨁ fun _ : Fin m => 𝟙_ P.Modules) ⟶ O) [Epi Ψ] (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] {D : ℕ}
    (θ : (Scheme.Modules.pullback g).obj O ≅ natTensorPow M D) (r : ℕ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → Function.Surjective ((gammaTop X).map
      (twistPowMap M ((Scheme.Modules.pullback g).map Ψ ≫ θ.hom) (r + D * k))) := by
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) :=
    isLocallyNoetherian_Spec.mpr inferInstance
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : (natTensorPow M r).IsCoherent := by
    rw [← Stacks.SectionRingProjTheta.twistPow_unit M r]
    exact Stacks.AlgebraicGeometry.ProperAmpleCohomology.isCoherent_twistPow _ _
      (Stacks.AlgebraicGeometry.ProperAmpleCohomology.isCoherent_tensorUnit _) r
  have : ((Scheme.Modules.pushforward g).obj (natTensorPow M r)).IsCoherent :=
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward g _
  obtain ⟨k₀, hk₀⟩ := exists_surjective_sheafTensor_map π O hO Ψ
    ((Scheme.Modules.pushforward g).obj (natTensorPow M r))
  refine ⟨k₀, fun k hk => ?_⟩
  have h1 := surjective_of_surjective_pushforward g O (natTensorPow M r) Ψ k (hk₀ k hk)
  exact surjective_twistPowMap_of_surjective_sheafTensor M θ _ r k h1

/-- A morphism `ψ` out of `g^* (⨁ⱼ 𝒪_P)` is `∑ⱼ (g^* πⱼ ≫ w) ≫ (w⁻¹ ≫ g^* ιⱼ ≫ ψ)`, where
`w : g^* 𝒪_P ≅ 𝒪_X` is the unit isomorphism. -/
theorem sum_pullback_biproduct_comp {X P : Scheme.{u}} (g : X ⟶ P) {m : ℕ} {Y : X.Modules}
    (ψ : (Scheme.Modules.pullback g).obj (⨁ fun _ : Fin m => 𝟙_ P.Modules) ⟶ Y) :
    ∑ j, ((Scheme.Modules.pullback g).map (biproduct.π (fun _ : Fin m => 𝟙_ P.Modules) j) ≫
        (Stacks.PullbackUnitSection.unitPullbackIso g).hom) ≫
      ((Stacks.PullbackUnitSection.unitPullbackIso g).inv ≫
        (Scheme.Modules.pullback g).map (biproduct.ι (fun _ : Fin m => 𝟙_ P.Modules) j) ≫ ψ) =
      ψ := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simp_rw [← Category.assoc, ← Functor.map_comp]
  rw [← Preadditive.sum_comp, ← Functor.map_sum, biproduct.total, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- **High powers of a generated invertible module are generated in one degree.** Let `X` be
proper over a Noetherian ring and `M` invertible on `X`, with `σ₀, …, σ_N` global sections of
`M^{⊗ D}` for some `D > 0` generating it. Then there are sections `s₀, …, s_N` of `M^{⊗ D}` and
an `N₀` such that for `n ≥ N₀` every section of `M^{⊗ (D + n)}` is `∑ⱼ sⱼ · aⱼ` with `aⱼ`
sections of `M^{⊗ n}`. -/
theorem exists_forall_eq_sum_mul_of_generatesStalks {X : Scheme.{u}} {R : Type u} [CommRing R]
    [IsNoetherianRing R] (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p] (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] {D N : ℕ} (hD : 0 < D)
    [Stacks.Ample.IsInvertibleModule X (natTensorPow M D)]
    (σ : Fin (N + 1) → Γ(natTensorPow M D, ⊤))
    (hσ : Stacks.ProjectiveFromSections.GeneratesStalks σ) :
    ∃ (s : Fin (N + 1) → Stacks.GradedSections.powSections M D) (N₀ : ℕ), ∀ n : ℕ, N₀ ≤ n →
      ∀ u : Stacks.GradedSections.powSections M (D + n),
        ∃ a : Fin (N + 1) → Stacks.GradedSections.powSections M n,
          u = ∑ j, Stacks.GradedSections.mul (s j) (a j) := by
  classical
  set g := Stacks.ProjectiveFromSections.toProjectiveSpaceOver σ hσ p
  obtain ⟨θ, -⟩ := exists_iso_projectiveSpaceTwistingSheaf_toProjectiveSpaceOver σ hσ p
  set O := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N
    (Spec (CommRingCat.of R))
  have hO : Stacks.Ample.IsAmple _ O :=
    Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf N (Spec (CommRingCat.of R))
  have : IsProper (Stacks.Tag01VT.projectiveSpaceHom N (Spec (CommRingCat.of R))) :=
    projectiveSpaceOver_isProper N (Spec (CommRingCat.of R))
  have : IsProper g := by
    have h : g ≫ Stacks.Tag01VT.projectiveSpaceHom N (Spec (CommRingCat.of R)) = p :=
      Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst σ hσ p
    have : IsProper (g ≫ Stacks.Tag01VT.projectiveSpaceHom N (Spec (CommRingCat.of R))) := by
      rw [h]; infer_instance
    exact IsProper.of_comp g (Stacks.Tag01VT.projectiveSpaceHom N (Spec (CommRingCat.of R)))
  obtain ⟨Ψ, hΨ⟩ := exists_epi_biproduct_of_generatesStalks (O := O) _
    (Stacks.ProjectiveSpaceModuli.taut_generates
      (projectiveSpaceOver.toIntegralAtUniverse N (Spec (CommRingCat.of R))))
  set ψ := (Scheme.Modules.pullback g).map Ψ ≫ θ.hom
  choose k₀ hk₀ using fun r => exists_surjective_twistPowMap_pullback p
    (Stacks.Tag01VT.projectiveSpaceHom N (Spec (CommRingCat.of R))) g O hO Ψ M θ r
  set w := Stacks.PullbackUnitSection.unitPullbackIso g
  refine ⟨fun j => w.inv ≫ (Scheme.Modules.pullback g).map
      (biproduct.ι (fun _ : Fin (N + 1) => 𝟙_ _) j) ≫ ψ,
    D * (Finset.range D).sup k₀, fun n hn u => ?_⟩
  have hn' : n % D + D * (n / D) = n := Nat.mod_add_div n D
  have hk : k₀ (n % D) ≤ n / D := by
    refine le_trans (Finset.le_sup (Finset.mem_range.mpr (Nat.mod_lt n hD))) ?_
    exact (Nat.le_div_iff_mul_le hD).mpr (by rw [Nat.mul_comm]; exact hn)
  have hsurj := hk₀ (n % D) (n / D) hk
  rw [hn'] at hsurj
  exact exists_eq_sum_mul_of_surjective M ψ
    (fun j => (Scheme.Modules.pullback g).map (biproduct.π (fun _ : Fin (N + 1) => 𝟙_ _) j) ≫
      w.hom) _ (sum_pullback_biproduct_comp g ψ) n hsurj u

end Scheme

end MMP.SemiampleSections

end
