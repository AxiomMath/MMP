module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaIntegerAssoc
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.Multiplication
public import StacksFrontier.AlgebraicGeometry.AmpleTwistAcyclicity.Basic
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.VanishingHigherDirectImagesLocallyFree
public import StacksFrontier.AlgebraicGeometry.Perfect.CohomologyAndBaseChangeAcyclic

/-!
# Multiplication by coordinate sections on the twists of a family, and its matrices

Let `π : 𝒞 ⟶ S` be a morphism of schemes, `H` and `A` invertible `𝒪_𝒞`-modules (in the
application `H` is the pull-back of `𝒪(1)` along a morphism to projective space, and `A` is
relatively ample), and `n` a natural number. For an integer `m` write
`N_m = H^{⊗ m} ⊗ A^{⊗ n}`. A global section `σ` of `H` gives the multiplication morphism
`σ : N_m ⟶ N_{m+1}` of `𝒪_𝒞`-modules, and its direct image over an open `W` of `S` is an
`Γ(S, W)`-linear map `Γ(W, π_* N_m) → Γ(W, π_* N_{m+1})`.

If the three modules `Γ(W, π_* N_m)`, `m = -2, -1, 0`, are free with chosen bases, multiplication
by a section `σ` has matrices `X₁ σ : V₂ → V₁` and `X₀ σ : V₁ → V₀` in these bases; because the
multiplication by two sections commute, `X₀ σ * X₁ τ = X₀ τ * X₁ σ`.

## Main definitions

* `MMP.Chow.coordMulHom`: multiplication `H^{⊗ m} ⟶ H^{⊗ (m+1)}` by a section of `H`.
* `MMP.Chow.coordMul`: the multiplication `N_m ⟶ N_{m+1}` of the twists.
* `MMP.Chow.directImageSectionsMap`: the `Γ(S, W)`-linear map induced by a morphism on the sections
  of the direct image over `W`.
* `MMP.Chow.KoszulSheafData`: three free direct images with bases, with the matrices
  `MMP.Chow.KoszulSheafData.matrix₀` and `MMP.Chow.KoszulSheafData.matrix₁` of the multiplications.

## Main results

* `MMP.Chow.coordMul_comm`: multiplication by two sections commutes.
* `MMP.Chow.KoszulSheafData.matrix₀_mul_matrix₁_comm`: `X₀ σ * X₁ τ = X₀ τ * X₁ σ`.

## Implementation notes

The commutation reduces, by associativity of the multiplication of the tensor powers of an
invertible module, to the commutativity of the product of the two sections in the symmetric
monoidal category of modules, where it follows from the triviality of the braiding of the unit
and from the commutativity of the multiplication of the tensor powers.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory BraidedCategory AlgebraicGeometry Stacks.Ample
  Stacks.RelativeVeryAmple

universe v u w

namespace MMP.Chow

section Abstract

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

private theorem braiding_unit_self [BraidedCategory C] : (β_ (𝟙_ C) (𝟙_ C)).hom = 𝟙 _ := by
  have h := CategoryTheory.braiding_leftUnitor (𝟙_ C)
  rw [← MonoidalCategory.unitors_equal] at h
  exact (cancel_mono (λ_ (𝟙_ C)).hom).1 (by simpa using h)

private theorem sectionProd_aux {T : C} (σ τ : 𝟙_ C ⟶ T) :
    σ ≫ (ρ_ T).inv ≫ T ◁ τ = (ρ_ (𝟙_ C)).inv ≫ (σ ⊗ₘ τ) := by
  rw [← Category.assoc, rightUnitor_inv_naturality, MonoidalCategory.tensorHom_def]
  simp

/-- The product of two sections of `T` under a commutative multiplication `T ⊗ T ⟶ T₂`
commutes. -/
private theorem sectionProd_comm [BraidedCategory C] {T T₂ : C} (B : T ⊗ T ⟶ T₂)
    (hB : (β_ T T).hom ≫ B = B) (σ τ : 𝟙_ C ⟶ T) :
    σ ≫ (ρ_ T).inv ≫ T ◁ τ ≫ B = τ ≫ (ρ_ T).inv ≫ T ◁ σ ≫ B := by
  have e : ∀ σ τ : 𝟙_ C ⟶ T, σ ≫ (ρ_ T).inv ≫ T ◁ τ ≫ B = (ρ_ (𝟙_ C)).inv ≫ (σ ⊗ₘ τ) ≫ B := by
    intro σ τ
    have := sectionProd_aux σ τ
    calc σ ≫ (ρ_ T).inv ≫ T ◁ τ ≫ B = (σ ≫ (ρ_ T).inv ≫ T ◁ τ) ≫ B := by simp
      _ = _ := by rw [this]; simp
  rw [e, e]
  conv_rhs => rw [← hB]
  rw [← Category.assoc (τ ⊗ₘ σ), BraidedCategory.braiding_naturality, braiding_unit_self]
  simp

/-- Two successive multiplications by sections, through an associative multiplication. -/
private theorem mulStep_comp {P₂ P₁ P₀ T T₂ : C} (A₁ : P₂ ⊗ T ⟶ P₁) (A₂ : P₁ ⊗ T ⟶ P₀)
    (B : T ⊗ T ⟶ T₂) (K : P₂ ⊗ T₂ ⟶ P₀)
    (h : A₁ ▷ T ≫ A₂ = (α_ P₂ T T).hom ≫ P₂ ◁ B ≫ K) (σ τ : 𝟙_ C ⟶ T) :
    (ρ_ P₂).inv ≫ P₂ ◁ σ ≫ A₁ ≫ (ρ_ P₁).inv ≫ P₁ ◁ τ ≫ A₂ =
      (ρ_ P₂).inv ≫ P₂ ◁ (σ ≫ (ρ_ T).inv ≫ T ◁ τ ≫ B) ≫ K := by
  have h1 : A₁ ≫ (ρ_ P₁).inv ≫ P₁ ◁ τ ≫ A₂ = (ρ_ (P₂ ⊗ T)).inv ≫ (P₂ ⊗ T) ◁ τ ≫
      (α_ P₂ T T).hom ≫ P₂ ◁ B ≫ K := by
    rw [← h]
    rw [← Category.assoc A₁, rightUnitor_inv_naturality]
    simp only [Category.assoc]
    rw [← whisker_exchange_assoc]
  have h2 : (ρ_ (P₂ ⊗ T)).inv ≫ (P₂ ⊗ T) ◁ τ ≫ (α_ P₂ T T).hom =
      P₂ ◁ ((ρ_ T).inv ≫ T ◁ τ) := by
    rw [MonoidalCategory.whiskerLeft_comp]
    have e1 : (P₂ ⊗ T) ◁ τ ≫ (α_ P₂ T T).hom = (α_ P₂ T (𝟙_ C)).hom ≫ P₂ ◁ T ◁ τ := by simp
    rw [e1, ← Category.assoc]
    congr 1
    simp
  rw [h1]
  rw [MonoidalCategory.whiskerLeft_comp] at h2
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% h2]

end Abstract

section TensorPowers

open AlgebraicGeometry.SheafOfModules Stacks.SheafOfModules.TensorSheafification

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

variable (L : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) [IsInvertible 𝒪 h𝒪 L]

/-- Multiplication `L^{⊗ n} ⟶ L^{⊗ (n+1)}` by a morphism `𝟙 ⟶ L^{⊗ 1}` from the tensor unit. -/
noncomputable def mulPow
    (σ : 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶ tensorPow 𝒪 h𝒪 L ((1 : ℕ) : ℤ))
    (n : ℤ) : tensorPow 𝒪 h𝒪 L n ⟶ tensorPow 𝒪 h𝒪 L (n + ((1 : ℕ) : ℤ)) :=
  (ρ_ (tensorPow 𝒪 h𝒪 L n)).inv ≫ tensorPow 𝒪 h𝒪 L n ◁ σ ≫
    (tensorPowAddIso 𝒪 h𝒪 L n ((1 : ℕ) : ℤ)).hom

/-- **Multiplications by two sections commute on the tensor powers.** -/
theorem mulPow_comm
    (σ τ : 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶
      tensorPow 𝒪 h𝒪 L ((1 : ℕ) : ℤ)) (n : ℤ) :
    mulPow 𝒪 h𝒪 L σ n ≫ mulPow 𝒪 h𝒪 L τ (n + ((1 : ℕ) : ℤ)) =
      mulPow 𝒪 h𝒪 L τ n ≫ mulPow 𝒪 h𝒪 L σ (n + ((1 : ℕ) : ℤ)) := by
  have hB : (β_ (tensorPow 𝒪 h𝒪 L ((1 : ℕ) : ℤ)) (tensorPow 𝒪 h𝒪 L ((1 : ℕ) : ℤ))).hom ≫
      (tensorPowAddIso 𝒪 h𝒪 L ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ)).hom =
        (tensorPowAddIso 𝒪 h𝒪 L ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ)).hom := by
    have h2 := congrArg Iso.hom (tensorPowAddIso_comm_natCast 𝒪 h𝒪 L 1 1)
    simp only [Iso.trans_hom] at h2
    exact h2
  have hA := tensorPowAddIso_assoc_natCast_right 𝒪 h𝒪 L n 1 1
  have key := fun σ τ => mulStep_comp (tensorPowAddIso 𝒪 h𝒪 L n ((1 : ℕ) : ℤ)).hom
    (tensorPowAddIso 𝒪 h𝒪 L (n + ((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ)).hom
    (tensorPowAddIso 𝒪 h𝒪 L ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ)).hom
    ((tensorPowAddIso 𝒪 h𝒪 L n (((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ))).hom ≫
      (eqToIso (congrArg (tensorPow 𝒪 h𝒪 L)
        (show n + (((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ)) = n + ((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) from
          by ring))).hom)
    (by rw [hA]) σ τ
  unfold mulPow
  simp only [Category.assoc]
  rw [key σ τ, key τ σ, sectionProd_comm _ hB σ τ]

end TensorPowers

section Sheaves

open Stacks.SheafOfModules.TensorSheafification

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

variable {X : Scheme.{u}} (H A : X.Modules) [IsInvertibleModule X H] [IsInvertibleModule X A]

/-- A global section of `H`, as a morphism from the monoidal unit to the first tensor power. -/
noncomputable def sectionToPow (σ : Γ(H, ⊤)) :
    𝟙_ (SheafOfModules.{u} (structureSheaf X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))) ⟶
      tensorPowModule X H ((1 : ℕ) : ℤ) :=
  (unitModuleIsoTensorUnit X).inv ≫ Stacks.EnriquesSeveriZariski.sectionHom H σ ≫
    (tensorPowModuleOneIso X H).inv

/-- **Multiplication by a global section** `σ` of `H`, as a morphism
`H^{⊗ m} ⟶ H^{⊗ (m+1)}` of `𝒪_X`-modules. -/
noncomputable def coordMulHom (σ : Γ(H, ⊤)) (m : ℤ) :
    tensorPowModule X H m ⟶ tensorPowModule X H (m + 1) :=
  mulPow X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) H
    (sectionToPow H σ) m

/-- Multiplications by two global sections of `H` commute. -/
theorem coordMulHom_comm (σ τ : Γ(H, ⊤)) (m : ℤ) :
    coordMulHom H σ m ≫ coordMulHom H τ (m + 1) = coordMulHom H τ m ≫ coordMulHom H σ (m + 1) :=
  mulPow_comm X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) H
    (sectionToPow H σ) (sectionToPow H τ) m

/-- The twist `H^{⊗ m} ⊗ A^{⊗ n}`. -/
abbrev twistMod (n : ℕ) (m : ℤ) : X.Modules :=
  tensorModules X (tensorPowModule X H m) (tensorPowModule X A n)

private theorem map_app_comp_comm {D E E' : Type*} [Category D] [Category E] [Category E']
    (F : D ⥤ E ⥤ E') {a b c b' : D} (f₁ : a ⟶ b) (f₂ : b ⟶ c) (g₁ : a ⟶ b') (g₂ : b' ⟶ c)
    (h : f₁ ≫ f₂ = g₁ ≫ g₂) (B : E) :
    (F.map f₁).app B ≫ (F.map f₂).app B = (F.map g₁).app B ≫ (F.map g₂).app B := by
  rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← F.map_comp, ← F.map_comp, h]

/-- **Multiplication by a global section** `σ` of `H` on the twists,
`H^{⊗ m} ⊗ A^{⊗ n} ⟶ H^{⊗ (m+1)} ⊗ A^{⊗ n}`. -/
noncomputable def coordMul (σ : Γ(H, ⊤)) (n : ℕ) (m : ℤ) :
    twistMod H A n m ⟶ twistMod H A n (m + 1) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
    Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
      ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))⟩).map
      (coordMulHom H σ m)).app (tensorPowModule X A n)

/-- **Multiplications by two global sections of `H` commute on the twists.** -/
theorem coordMul_comm (σ τ : Γ(H, ⊤)) (n : ℕ) (m : ℤ) :
    coordMul H A σ n m ≫ coordMul H A τ n (m + 1) =
      coordMul H A τ n m ≫ coordMul H A σ n (m + 1) := by
  unfold coordMul
  exact map_app_comp_comm _ _ _ _ _ (coordMulHom_comm H σ τ m) _

end Sheaves

section Sections

variable {𝒞 S : Scheme.{u}} (π : 𝒞 ⟶ S) (W : S.Opens)

/-- The sections over `W` of the direct image `π_* M`, a module over `Γ(S, W)`. -/
abbrev directImageSections (M : 𝒞.Modules) : Type u :=
  Γ((Scheme.Modules.pushforward π).obj M, W)

/-- A morphism of `𝒪_𝒞`-modules induces a `Γ(S, W)`-linear map on the sections of the direct
images over `W`. -/
def directImageSectionsMap {M N : 𝒞.Modules} (φ : M ⟶ N) :
    directImageSections π W M →ₗ[Γ(S, W)] directImageSections π W N where
  toFun x := (((Scheme.Modules.pushforward π).map φ).app W).hom x
  map_add' x y := map_add _ x y
  map_smul' r x := Scheme.Modules.Hom.app_smul _ r x

/-- The map induced on the sections of the direct images over `W` by a composite `φ ≫ ψ` is the
composite of the maps induced by `φ` and `ψ`. -/
theorem directImageSectionsMap_comp {M N P : 𝒞.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) :
    directImageSectionsMap π W (φ ≫ ψ) =
      directImageSectionsMap π W ψ ∘ₗ directImageSectionsMap π W φ := by
  ext x
  simp [directImageSectionsMap, Scheme.Modules.Hom.comp_app]
  rfl

end Sections

/-- **Free direct images of three consecutive twists, with bases.** Over the open `W` of the base
`S`, the direct images `Γ(W, π_* (H^{⊗ m} ⊗ A^{⊗ n}))`, `m = -2, -1, 0`, are free of ranks
`r₂, r₁, r₀` with chosen bases. -/
structure KoszulSheafData {𝒞 S : Scheme.{u}} (π : 𝒞 ⟶ S) (H A : 𝒞.Modules)
    [IsInvertibleModule 𝒞 H] [IsInvertibleModule 𝒞 A] (n : ℕ) where
  /-- the open of the base -/
  W : S.Opens
  /-- the rank of the sections for `m = 0` -/
  r₀ : ℕ
  /-- the rank of the sections for `m = -1` -/
  r₁ : ℕ
  /-- the rank of the sections for `m = -2` -/
  r₂ : ℕ
  /-- a basis for `m = 0` -/
  b₀ : Module.Basis (Fin r₀) Γ(S, W) (directImageSections π W (twistMod H A n (-2 + 1 + 1)))
  /-- a basis for `m = -1` -/
  b₁ : Module.Basis (Fin r₁) Γ(S, W) (directImageSections π W (twistMod H A n (-2 + 1)))
  /-- a basis for `m = -2` -/
  b₂ : Module.Basis (Fin r₂) Γ(S, W) (directImageSections π W (twistMod H A n (-2)))

namespace KoszulSheafData

variable {𝒞 S : Scheme.{u}} {π : 𝒞 ⟶ S} {H A : 𝒞.Modules}
  [IsInvertibleModule 𝒞 H] [IsInvertibleModule 𝒞 A] {n : ℕ} (D : KoszulSheafData π H A n)

/-- The matrix of multiplication by a global section `σ` of `H`, from the sections for `m = -1`
to those for `m = 0`, in the chosen bases. -/
noncomputable def matrix₀ (σ : Γ(H, ⊤)) : Matrix (Fin D.r₀) (Fin D.r₁) Γ(S, D.W) :=
  LinearMap.toMatrix D.b₁ D.b₀ (directImageSectionsMap π D.W (coordMul H A σ n (-2 + 1)))

/-- The matrix of multiplication by a global section `σ` of `H`, from the sections for `m = -2`
to those for `m = -1`, in the chosen bases. -/
noncomputable def matrix₁ (σ : Γ(H, ⊤)) : Matrix (Fin D.r₁) (Fin D.r₂) Γ(S, D.W) :=
  LinearMap.toMatrix D.b₂ D.b₁ (directImageSectionsMap π D.W (coordMul H A σ n (-2)))

/-- **The matrices of multiplication by two sections commute:** `X₀ σ * X₁ τ = X₀ τ * X₁ σ`. -/
theorem matrix₀_mul_matrix₁_comm (σ τ : Γ(H, ⊤)) :
    D.matrix₀ σ * D.matrix₁ τ = D.matrix₀ τ * D.matrix₁ σ := by
  unfold matrix₀ matrix₁
  rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp, ← directImageSectionsMap_comp,
    ← directImageSectionsMap_comp, coordMul_comm]

end KoszulSheafData

end MMP.Chow

end
