module

public import MMP.Attr
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Two closed embeddings of an affine scheme are stably equivalent (Kollár 3.39)

Let `R` be a ring, `X = Spec B` an affine `R`-scheme and `i₁ : X ↪ 𝔸ⁿ_R`, `i₂ : X ↪ 𝔸ᵐ_R`
closed embeddings over `R`. Let `i'₁ : X → 𝔸ⁿ⁺ᵐ_R` be `i₁` followed by `x ↦ (x, 0)` and `i'₂`
be `i₂` followed by `y ↦ (0, y)`. Then some `R`-automorphism `φ` of `𝔸ⁿ⁺ᵐ_R` has
`φ ∘ i'₁ = i'₂` (Kollár, *Lectures on resolution of singularities*, Lemma 3.39).

## Main statements

* `MMP.Resolution.Kollar.exists_iso_affineSpace_comp_eq`: Kollár's Lemma 3.39.

## Implementation notes

`𝔸ⁿ_R` is Mathlib's `𝔸(ι; Spec R)` with coordinates indexed by a type `ι` (Kollár's case is
`ι = Fin n`; the index type lives in the universe of the schemes), and `𝔸ⁿ⁺ᵐ_R` is
`𝔸(ι ⊕ κ; Spec R)`. A morphism `X → 𝔸(ι; Spec R)` over `Spec R` is given by its coordinates, global
sections of `X` (`AffineSpace.homOfVector`); so `i'₁` has coordinates `(i₁^* xᵢ, 0)` and `i'₂`
has coordinates `(0, i₂^* yⱼ)`. Composition is written in diagrammatic order: `φ ∘ i'₁` is
`i'₁ ≫ φ.hom`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Resolution.Kollar

variable {R : CommRingCat.{u}} {X : Scheme.{u}} {ι κ : Type u} (sX : X ⟶ Spec R)

/-- `i₁ : X → 𝔸(ι; Spec R)` followed by the inclusion `x ↦ (x, 0)` of `𝔸(ι; Spec R)` into
`𝔸(ι ⊕ κ; Spec R)`: the morphism over `Spec R` with coordinates `(i₁^* xᵢ, 0)`. -/
noncomputable def embedFst (i₁ : X ⟶ 𝔸(ι; Spec R)) : X ⟶ 𝔸(ι ⊕ κ; Spec R) :=
  AffineSpace.homOfVector sX (Sum.elim (fun i ↦ i₁.appTop (AffineSpace.coord (Spec R) i)) 0)

/-- `i₂ : X → 𝔸(κ; Spec R)` followed by the inclusion `y ↦ (0, y)` of `𝔸(κ; Spec R)` into
`𝔸(ι ⊕ κ; Spec R)`: the morphism over `Spec R` with coordinates `(0, i₂^* yⱼ)`. -/
noncomputable def embedSnd (i₂ : X ⟶ 𝔸(κ; Spec R)) : X ⟶ 𝔸(ι ⊕ κ; Spec R) :=
  AffineSpace.homOfVector sX (Sum.elim 0 (fun j ↦ i₂.appTop (AffineSpace.coord (Spec R) j)))

private lemma comp_appTop_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Γ(Z, ⊤)) : (f ≫ g).appTop x = f.appTop (g.appTop x) := rfl

private lemma embedFst_coord_inl (i₁ : X ⟶ 𝔸(ι; Spec R)) (i : ι) :
    (embedFst (κ := κ) sX i₁).appTop (AffineSpace.coord (Spec R) (Sum.inl i)) =
      i₁.appTop (AffineSpace.coord (Spec R) i) :=
  AffineSpace.homOfVector_appTop_coord _ _ _

private lemma embedFst_coord_inr (i₁ : X ⟶ 𝔸(ι; Spec R)) (j : κ) :
    (embedFst (κ := κ) sX i₁).appTop (AffineSpace.coord (Spec R) (Sum.inr j)) = 0 :=
  AffineSpace.homOfVector_appTop_coord _ _ _

private lemma embedSnd_coord_inl (i₂ : X ⟶ 𝔸(κ; Spec R)) (i : ι) :
    (embedSnd (ι := ι) sX i₂).appTop (AffineSpace.coord (Spec R) (Sum.inl i)) = 0 :=
  AffineSpace.homOfVector_appTop_coord _ _ _

private lemma embedSnd_coord_inr (i₂ : X ⟶ 𝔸(κ; Spec R)) (j : κ) :
    (embedSnd (ι := ι) sX i₂).appTop (AffineSpace.coord (Spec R) (Sum.inr j)) =
      i₂.appTop (AffineSpace.coord (Spec R) j) :=
  AffineSpace.homOfVector_appTop_coord _ _ _

section Shear

open AffineSpace

variable {n m : Type u} {S : Scheme.{u}}

/-- The shear of `𝔸(n; S)` over `S`: `x ↦ x + p`, for `p` a family of global sections. -/
private noncomputable def shear (p : n → Γ(𝔸(n; S), ⊤)) : 𝔸(n; S) ⟶ 𝔸(n; S) :=
  homOfVector (𝔸(n; S) ↘ S) (fun k ↦ coord S k + p k)

private lemma shear_over (p : n → Γ(𝔸(n; S), ⊤)) :
    shear p ≫ 𝔸(n; S) ↘ S = 𝔸(n; S) ↘ S :=
  homOfVector_over _ _

private lemma shear_appTop_coord (p : n → Γ(𝔸(n; S), ⊤)) (k : n) :
    (shear p).appTop (coord S k) = coord S k + p k :=
  homOfVector_appTop_coord _ _ _

private lemma shear_fix (p : n → Γ(𝔸(n; S), ⊤)) (f : m → n) (hp : ∀ a, p (f a) = 0)
    (g : Γ(𝔸(m; S), ⊤)) :
    (shear p).appTop ((reindex f S).appTop g) = (reindex f S).appTop g := by
  have : shear p ≫ reindex f S = reindex f S := by
    apply hom_ext
    · simp [shear_over]
    · intro a
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord,
        shear_appTop_coord, hp, add_zero]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, this]

private lemma shear_shear (p : n → Γ(𝔸(n; S), ⊤))
    (h : ∀ k, (shear p).appTop (p k) = p k) : shear p ≫ shear (-p) = 𝟙 _ := by
  apply hom_ext
  · simp [shear_over]
  · intro k
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, shear_appTop_coord, Pi.neg_apply,
      map_add, map_neg, shear_appTop_coord, h]
    simp

private noncomputable def shearIso (p : n → Γ(𝔸(n; S), ⊤))
    (h₁ : ∀ k, (shear p).appTop (p k) = p k) (h₂ : ∀ k, (shear (-p)).appTop (p k) = p k) :
    𝔸(n; S) ≅ 𝔸(n; S) where
  hom := shear p
  inv := shear (-p)
  hom_inv_id := shear_shear p h₁
  inv_hom_id := by
    have := shear_shear (-p) (fun k ↦ by rw [Pi.neg_apply, map_neg, h₂])
    rwa [neg_neg] at this

end Shear

/-- **Kollár, Lemma 3.39.** Let `R` be a ring, `X` an affine `R`-scheme and
`i₁ : X ↪ 𝔸ⁿ_R`, `i₂ : X ↪ 𝔸ᵐ_R` closed embeddings over `R`. Let `i'₁ : X → 𝔸ⁿ⁺ᵐ_R` be `i₁`
followed by `x ↦ (x, 0)` and `i'₂` be `i₂` followed by `y ↦ (0, y)`. Then there is an
`R`-automorphism `φ` of `𝔸ⁿ⁺ᵐ_R` with `φ ∘ i'₁ = i'₂`. -/
@[mmp "lem_kr3b_affine_embeddings_stably_equivalent"]
theorem exists_iso_affineSpace_comp_eq [IsAffine X] (i₁ : X ⟶ 𝔸(ι; Spec R))
    (i₂ : X ⟶ 𝔸(κ; Spec R)) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (h₁ : i₁ ≫ 𝔸(ι; Spec R) ↘ Spec R = sX) (h₂ : i₂ ≫ 𝔸(κ; Spec R) ↘ Spec R = sX) :
    ∃ φ : 𝔸(ι ⊕ κ; Spec R) ≅ 𝔸(ι ⊕ κ; Spec R),
      φ.hom ≫ 𝔸(ι ⊕ κ; Spec R) ↘ Spec R = 𝔸(ι ⊕ κ; Spec R) ↘ Spec R ∧
        embedFst sX i₁ ≫ φ.hom = embedSnd sX i₂ := by
  have hs₁ := (IsClosedImmersion.isAffine_surjective_of_isAffine i₁).2
  have hs₂ := (IsClosedImmersion.isAffine_surjective_of_isAffine i₂).2
  choose c hc using fun j ↦ hs₁ (i₂.appTop (AffineSpace.coord (Spec R) j))
  choose d hd using fun i ↦ hs₂ (i₁.appTop (AffineSpace.coord (Spec R) i))
  let p₁ : ι ⊕ κ → Γ(𝔸(ι ⊕ κ; Spec R), ⊤) :=
    Sum.elim 0 (fun j ↦ (AffineSpace.reindex Sum.inl (Spec R)).appTop (c j))
  let p₂ : ι ⊕ κ → Γ(𝔸(ι ⊕ κ; Spec R), ⊤) :=
    Sum.elim (fun i ↦ (AffineSpace.reindex Sum.inr (Spec R)).appTop (d i)) 0
  have e₁ : embedFst (κ := κ) sX i₁ ≫ AffineSpace.reindex Sum.inl (Spec R) = i₁ := by
    apply AffineSpace.hom_ext
    · simp [embedFst, h₁]
    · intro i
      rw [comp_appTop_apply, AffineSpace.reindex_appTop_coord, embedFst_coord_inl]
  have e₂ : embedSnd (ι := ι) sX i₂ ≫ AffineSpace.reindex Sum.inr (Spec R) = i₂ := by
    apply AffineSpace.hom_ext
    · simp [embedSnd, h₂]
    · intro i
      rw [comp_appTop_apply, AffineSpace.reindex_appTop_coord, embedSnd_coord_inr]
  have f₁ : ∀ k, (shear p₁).appTop (p₁ k) = p₁ k := by
    rintro (k | k)
    · simp [p₁]
    · exact shear_fix p₁ Sum.inl (fun a ↦ rfl) _
  have f₁' : ∀ k, (shear (-p₁)).appTop (p₁ k) = p₁ k := by
    rintro (k | k)
    · simp [p₁]
    · exact shear_fix (-p₁) Sum.inl (fun a ↦ by simp [p₁]) _
  have f₂ : ∀ k, (shear p₂).appTop (p₂ k) = p₂ k := by
    rintro (k | k)
    · exact shear_fix p₂ Sum.inr (fun a ↦ rfl) _
    · simp [p₂]
  have f₂' : ∀ k, (shear (-p₂)).appTop (p₂ k) = p₂ k := by
    rintro (k | k)
    · exact shear_fix (-p₂) Sum.inr (fun a ↦ by simp [p₂]) _
    · simp [p₂]
  let ψ₁ := shearIso p₁ f₁ f₁'
  let ψ₂ := shearIso p₂ f₂ f₂'
  have key₁ : embedFst (κ := κ) sX i₁ ≫ shear p₁ = AffineSpace.homOfVector sX (Sum.elim
      (fun i ↦ i₁.appTop (AffineSpace.coord (Spec R) i))
      (fun j ↦ i₂.appTop (AffineSpace.coord (Spec R) j))) := by
    apply AffineSpace.hom_ext
    · simp [shear_over, embedFst]
    · rintro (i | j)
      · rw [comp_appTop_apply, shear_appTop_coord, map_add, embedFst_coord_inl,
          AffineSpace.homOfVector_appTop_coord]
        simp [p₁]
      · have : p₁ (Sum.inr j) = (AffineSpace.reindex Sum.inl (Spec R)).appTop (c j) := rfl
        rw [comp_appTop_apply, shear_appTop_coord, map_add, embedFst_coord_inr, this,
          ← comp_appTop_apply, e₁, hc, zero_add, AffineSpace.homOfVector_appTop_coord]
        rfl
  have key₂ : embedSnd (ι := ι) sX i₂ ≫ shear p₂ = AffineSpace.homOfVector sX (Sum.elim
      (fun i ↦ i₁.appTop (AffineSpace.coord (Spec R) i))
      (fun j ↦ i₂.appTop (AffineSpace.coord (Spec R) j))) := by
    apply AffineSpace.hom_ext
    · simp [shear_over, embedSnd]
    · rintro (i | j)
      · have : p₂ (Sum.inl i) = (AffineSpace.reindex Sum.inr (Spec R)).appTop (d i) := rfl
        rw [comp_appTop_apply, shear_appTop_coord, map_add, embedSnd_coord_inl, this,
          ← comp_appTop_apply, e₂, hd, zero_add, AffineSpace.homOfVector_appTop_coord]
        rfl
      · rw [comp_appTop_apply, shear_appTop_coord, map_add, embedSnd_coord_inr,
          AffineSpace.homOfVector_appTop_coord]
        simp [p₂]
  have key₁' : embedFst (κ := κ) sX i₁ ≫ ψ₁.hom = AffineSpace.homOfVector sX (Sum.elim
      (fun i ↦ i₁.appTop (AffineSpace.coord (Spec R) i))
      (fun j ↦ i₂.appTop (AffineSpace.coord (Spec R) j))) := key₁
  have key₂' : embedSnd (ι := ι) sX i₂ ≫ ψ₂.hom = AffineSpace.homOfVector sX (Sum.elim
      (fun i ↦ i₁.appTop (AffineSpace.coord (Spec R) i))
      (fun j ↦ i₂.appTop (AffineSpace.coord (Spec R) j))) := key₂
  refine ⟨ψ₁ ≪≫ ψ₂.symm, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    have h₃ : ψ₂.inv ≫ 𝔸(ι ⊕ κ; Spec R) ↘ Spec R = 𝔸(ι ⊕ κ; Spec R) ↘ Spec R :=
      shear_over _
    rw [h₃]
    exact shear_over _
  · simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, key₁', ← key₂', Category.assoc]
    simp

end MMP.Resolution.Kollar
