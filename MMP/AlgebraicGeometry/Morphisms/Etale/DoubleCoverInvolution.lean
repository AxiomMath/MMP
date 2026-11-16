/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EffectiveEpi
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# The covering involution of a finite étale double cover

Let `p : X ⟶ S` be a finite étale morphism of constant degree `2`. The diagonal of `p` is an
open and closed immersion, so `X ×_S X` is the disjoint union of the diagonal and its
complement `C`. The first projection `C ⟶ X` is finite étale of degree `2 - 1 = 1`, hence an
isomorphism, and its inverse followed by the second projection is an involution `τ` of `X`
over `S` for which `(id, τ) : X ⨿ X ⟶ X ×_S X` is an isomorphism: `p` is a `ℤ/2`-torsor.

## Main results

* `MMP.Flips.finrank_eq_finrank_inl_add_finrank_inr`: the degree of a finite flat morphism out of
  a coproduct is the sum of the degrees of its restrictions to the summands.
* `MMP.Flips.exists_involution_of_finrank_eq_two`: a finite étale morphism of degree `2` has an
  involution `τ` over the base with `(id, τ) : X ⨿ X ≅ X ×_S X`.
* `MMP.Flips.exists_app_eq_of_involution`: for such a `ℤ/2`-torsor `p` (flat, surjective and
  affine), a `τ`-invariant function on `p⁻¹V`, `V` affine, is pulled back from `V`.

## Implementation notes

The descent of functions uses that a flat surjective morphism of affine schemes is a regular
epimorphism (`AlgebraicGeometry.isRegularEpi_of_flat_of_surjective_of_isAffine`), applied to the
morphism `p⁻¹V ⟶ 𝔸¹_ℤ` given by the function; the torsor isomorphism reduces the compatibility on
`p⁻¹V ×_V p⁻¹V` to the identity and to `τ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace MMP.Flips

open AlgebraicGeometry

/-! ### The degree of a morphism out of a coproduct -/

section Coprod

/-- The inclusion of the first summand into a coproduct of schemes is a closed immersion. -/
instance isClosedImmersion_coprod_inl (X₁ X₂ : Scheme.{u}) :
    IsClosedImmersion (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) := by
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rw [← (isCompl_range_inl_inr X₁ X₂).symm.compl_eq]
  exact (coprod.inr : X₂ ⟶ X₁ ⨿ X₂).isOpenEmbedding.isOpen_range.isClosed_compl

/-- The inclusion of the second summand into a coproduct of schemes is a closed immersion. -/
instance isClosedImmersion_coprod_inr (X₁ X₂ : Scheme.{u}) :
    IsClosedImmersion (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) := by
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rw [← (isCompl_range_inl_inr X₁ X₂).compl_eq]
  exact (coprod.inl : X₁ ⟶ X₁ ⨿ X₂).isOpenEmbedding.isOpen_range.isClosed_compl

/-- The rank of `R → A × B` is the sum of the ranks of `R → A` and `R → B`. -/
theorem finrank_ringHom_prod {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    (φ₁ : R →+* A) (φ₂ : R →+* B) (hf : (φ₁.prod φ₂).Finite) (hfl : (φ₁.prod φ₂).Flat) :
    (φ₁.prod φ₂).finrank = φ₁.finrank + φ₂.finrank := by
  letI := φ₁.toAlgebra
  letI := φ₂.toAlgebra
  have hφ : φ₁.prod φ₂ = algebraMap R (A × B) := rfl
  rw [hφ] at hf hfl ⊢
  have : Module.Finite R (A × B) := hf
  have : Module.Flat R (A × B) := hfl
  have : Module.Finite R A := Module.Finite.of_surjective (LinearMap.fst R A B) Prod.fst_surjective
  have : Module.Finite R B := Module.Finite.of_surjective (LinearMap.snd R A B) Prod.snd_surjective
  have : Module.Flat R A :=
    Module.Flat.of_retract (LinearMap.inl R A B) (LinearMap.fst R A B) (by ext; simp)
  have : Module.Flat R B :=
    Module.Flat.of_retract (LinearMap.inr R A B) (LinearMap.snd R A B) (by ext; simp)
  rw [RingHom.finrank_algebraMap, ← RingHom.algebraMap_toAlgebra φ₁,
    ← RingHom.algebraMap_toAlgebra φ₂, RingHom.finrank_algebraMap, RingHom.finrank_algebraMap,
    Module.rankAtStalk_prod]

/-- The degree of a finite flat morphism from a coproduct of affine schemes to an affine scheme
is the sum of the degrees of its restrictions to the summands. -/
theorem finrank_eq_finrank_inl_add_finrank_inr_of_isAffine {R : CommRingCat.{u}}
    {X₁ X₂ : Scheme.{u}} [IsAffine X₁] [IsAffine X₂] (h : X₁ ⨿ X₂ ⟶ Spec R) [IsFinite h]
    [Flat h] : h.finrank = (coprod.inl ≫ h).finrank + (coprod.inr ≫ h).finrank := by
  let e : X₁ ⨿ X₂ ≅ Spec (.of (Γ(X₁, ⊤) × Γ(X₂, ⊤))) :=
    coprod.mapIso X₁.isoSpec X₂.isoSpec ≪≫ asIso (coprodSpec Γ(X₁, ⊤) Γ(X₂, ⊤))
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (e.inv ≫ h)
  have hh : h = e.hom ≫ Spec.map φ := by rw [hφ, Iso.hom_inv_id_assoc]
  have h1 : coprod.inl ≫ h = X₁.isoSpec.hom ≫
      Spec.map (φ ≫ CommRingCat.ofHom (RingHom.fst _ _)) := by
    rw [hh, Spec.map_comp]
    simp [e, ← coprodSpec_inl]
    rfl
  have h2 : coprod.inr ≫ h = X₂.isoSpec.hom ≫
      Spec.map (φ ≫ CommRingCat.ofHom (RingHom.snd _ _)) := by
    rw [hh, Spec.map_comp]
    simp [e, ← coprodSpec_inr]
    rfl
  have : IsFinite (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have hfφ : Flat (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have e1 : Spec.map (φ ≫ CommRingCat.ofHom (RingHom.fst _ _)) =
      X₁.isoSpec.inv ≫ coprod.inl ≫ h := by rw [h1, Iso.inv_hom_id_assoc]
  have e2 : Spec.map (φ ≫ CommRingCat.ofHom (RingHom.snd _ _)) =
      X₂.isoSpec.inv ≫ coprod.inr ≫ h := by rw [h2, Iso.inv_hom_id_assoc]
  have hf1 : IsFinite (Spec.map (φ ≫ CommRingCat.ofHom (RingHom.fst _ _))) := by
    rw [e1]
    infer_instance
  have hf2 : IsFinite (Spec.map (φ ≫ CommRingCat.ofHom (RingHom.snd _ _))) := by
    rw [e2]
    infer_instance
  have hl1 : Flat (Spec.map (φ ≫ CommRingCat.ofHom (RingHom.fst _ _))) := by
    rw [e1]
    infer_instance
  have hl2 : Flat (Spec.map (φ ≫ CommRingCat.ofHom (RingHom.snd _ _))) := by
    rw [e2]
    infer_instance
  rw [h1, h2, hh, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_comp_left_of_isIso,
    Scheme.Hom.finrank_comp_left_of_isIso]
  rw [IsFinite.SpecMap_iff] at hf1 hf2
  rw [Flat.SpecMap_iff] at hl1 hl2 hfφ
  have hfin : φ.hom.Finite := by rwa [← IsFinite.SpecMap_iff]
  rw [Scheme.Hom.finrank_SpecMap_eq_finrank hf1 hl1, Scheme.Hom.finrank_SpecMap_eq_finrank hf2 hl2,
    Scheme.Hom.finrank_SpecMap_eq_finrank hfin hfφ]
  have hp : φ.hom = ((RingHom.fst _ _).comp φ.hom).prod ((RingHom.snd _ _).comp φ.hom) := by
    ext r <;> rfl
  rw [hp] at hfin hfφ ⊢
  exact finrank_ringHom_prod _ _ hfin hfφ

/-- The pull-back of `h : X₁ ⨿ X₂ ⟶ Y` along `i` is the coproduct of the pull-backs of
`coprod.inl ≫ h` and `coprod.inr ≫ h`, compatibly with the second projections. -/
theorem exists_iso_coprod_pullback {X₁ X₂ Y T : Scheme.{u}} (h : X₁ ⨿ X₂ ⟶ Y) (i : T ⟶ Y) :
    ∃ E : pullback (coprod.inl ≫ h) i ⨿ pullback (coprod.inr ≫ h) i ≅ pullback h i,
      coprod.inl ≫ E.hom ≫ pullback.snd h i = pullback.snd _ _ ∧
      coprod.inr ≫ E.hom ≫ pullback.snd h i = pullback.snd _ _ := by
  obtain ⟨a₁, ha₁f, ha₁s⟩ : ∃ a₁ : pullback (coprod.inl ≫ h) i ⟶ pullback h i,
      a₁ ≫ pullback.fst h i = pullback.fst _ _ ≫ coprod.inl ∧
      a₁ ≫ pullback.snd h i = pullback.snd _ _ :=
    ⟨pullback.lift _ _ (by simp [pullback.condition]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  obtain ⟨a₂, ha₂f, ha₂s⟩ : ∃ a₂ : pullback (coprod.inr ≫ h) i ⟶ pullback h i,
      a₂ ≫ pullback.fst h i = pullback.fst _ _ ≫ coprod.inr ∧
      a₂ ≫ pullback.snd h i = pullback.snd _ _ :=
    ⟨pullback.lift _ _ (by simp [pullback.condition]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  have hvk := FinitaryExtensive.van_kampen' _ (coprodIsCoprod X₁ X₂)
  rw [BinaryCofan.isVanKampen_iff] at hvk
  have p₁ : IsPullback a₁ (pullback.fst _ _) (pullback.fst h i) coprod.inl := by
    refine IsPullback.of_right ?_ ha₁f (IsPullback.of_hasPullback h i).flip
    rw [ha₁s]
    exact (IsPullback.of_hasPullback (coprod.inl ≫ h) i).flip
  have p₂ : IsPullback a₂ (pullback.fst _ _) (pullback.fst h i) coprod.inr := by
    refine IsPullback.of_right ?_ ha₂f (IsPullback.of_hasPullback h i).flip
    rw [ha₂s]
    exact (IsPullback.of_hasPullback (coprod.inr ≫ h) i).flip
  obtain ⟨hc⟩ := (hvk (BinaryCofan.mk a₁ a₂) (pullback.fst _ _) (pullback.fst _ _)
    (pullback.fst h i) ha₁f.symm ha₂f.symm).mpr ⟨p₁, p₂⟩
  refine ⟨(coprodIsCoprod _ _).coconePointUniqueUpToIso hc, ?_, ?_⟩
  · rw [← Category.assoc]
    erw [(coprodIsCoprod _ _).comp_coconePointUniqueUpToIso_hom hc ⟨WalkingPair.left⟩]
    exact ha₁s
  · rw [← Category.assoc]
    erw [(coprodIsCoprod _ _).comp_coconePointUniqueUpToIso_hom hc ⟨WalkingPair.right⟩]
    exact ha₂s

/-- **The degree of a morphism out of a coproduct.** The degree of a finite flat morphism
`X₁ ⨿ X₂ ⟶ Y` is the sum of the degrees of its restrictions to `X₁` and `X₂`. -/
theorem finrank_eq_finrank_inl_add_finrank_inr {X₁ X₂ Y : Scheme.{u}} (h : X₁ ⨿ X₂ ⟶ Y)
    [IsFinite h] [Flat h] : h.finrank = (coprod.inl ≫ h).finrank + (coprod.inr ≫ h).finrank := by
  ext y
  obtain ⟨R, i, _, t, rfl⟩ := Y.exists_Spec_apply_eq y
  obtain ⟨E, hE₁, hE₂⟩ := exists_iso_coprod_pullback h i
  have : IsAffine (pullback (coprod.inl ≫ h) i) := isAffine_of_isAffineHom (pullback.snd _ i)
  have : IsAffine (pullback (coprod.inr ≫ h) i) := isAffine_of_isAffineHom (pullback.snd _ i)
  have key := congrFun (finrank_eq_finrank_inl_add_finrank_inr_of_isAffine
    (E.hom ≫ pullback.snd h i)) t
  rw [hE₁, hE₂, Scheme.Hom.finrank_comp_left_of_isIso] at key
  simp only [Pi.add_apply, Scheme.Hom.finrank_pullback_snd] at key
  exact key

/-- Two open immersions with complementary images exhibit their target as a coproduct. -/
theorem isIso_coprod_desc_of_isCompl {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsOpenImmersion f] [IsOpenImmersion g] (hfg : IsCompl f.opensRange g.opensRange) :
    IsIso (coprod.desc f g) := by
  obtain ⟨hc⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl f g hfg
  let e : X ⨿ Y ≅ S := (colimit.isColimit (pair X Y)).coconePointUniqueUpToIso hc
  have h1 : coprod.inl ≫ e.hom = f :=
    (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom hc ⟨WalkingPair.left⟩
  have h2 : coprod.inr ≫ e.hom = g :=
    (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom hc ⟨WalkingPair.right⟩
  have : e.hom = coprod.desc f g :=
    coprod.hom_ext (by rw [coprod.inl_desc, h1]) (by rw [coprod.inr_desc, h2])
  rw [← this]
  infer_instance

/-- The degree of the second summand of a finite flat morphism of degree `2` out of a coproduct
is `1` when that of the first summand is. -/
theorem finrank_comp_inr_eq_one {X₁ X₂ Y : Scheme.{u}} (h : X₁ ⨿ X₂ ⟶ Y) [IsFinite h] [Flat h]
    (h₂ : h.finrank = 2) (h₁ : (coprod.inl ≫ h).finrank = 1) :
    (coprod.inr ≫ h).finrank = 1 := by
  have := finrank_eq_finrank_inl_add_finrank_inr h
  rw [h₁, h₂] at this
  ext y
  have := congrFun this y
  simp only [Pi.add_apply, Pi.one_apply, Pi.ofNat_apply] at this ⊢
  omega

end Coprod

/-! ### The covering involution -/

section Involution

/-- A morphism landing in an open `U` on which `q` restricts to an isomorphism factors through
the inverse of that restriction. -/
theorem eq_comp_inv_comp_ι_of_range_subset {X Y : Scheme.{u}} (U : Y.Opens) (q : Y ⟶ X)
    [IsIso (U.ι ≫ q)] (u : X ⟶ Y) (hu : Set.range u ⊆ Set.range U.ι) :
    u = (u ≫ q) ≫ inv (U.ι ≫ q) ≫ U.ι := by
  have hl := IsOpenImmersion.lift_fac U.ι u hu
  have : IsOpenImmersion.lift U.ι u hu = (u ≫ q) ≫ inv (U.ι ≫ q) := by
    rw [IsIso.eq_comp_inv, ← Category.assoc, hl]
  conv_lhs => rw [← hl]
  rw [this, Category.assoc]

/-- A section `σ` of the first projection `X ×_S X ⟶ X` avoiding the diagonal, through which every
map avoiding the diagonal factors, then `σ ≫ pullback.snd p p` is an involution of `X`. -/
theorem snd_comp_comp_snd_eq_id {X S : Scheme.{u}} (p : X ⟶ S) (σ : X ⟶ pullback p p)
    (hσf : σ ≫ pullback.fst p p = 𝟙 X)
    (hσC : Set.range σ ⊆ (Set.range (pullback.diagonal p))ᶜ)
    (hland : ∀ u : X ⟶ pullback p p, Set.range u ⊆ (Set.range (pullback.diagonal p))ᶜ →
      u = (u ≫ pullback.fst p p) ≫ σ) :
    (σ ≫ pullback.snd p p) ≫ σ ≫ pullback.snd p p = 𝟙 X := by
  set s := (pullbackSymmetry p p).hom
  have hss : s ≫ s = 𝟙 _ := by
    apply pullback.hom_ext <;> simp [s]
  have hΔs : pullback.diagonal p ≫ s = pullback.diagonal p := by
    apply pullback.hom_ext <;> simp [s]
  have hu : Set.range (σ ≫ s) ⊆ (Set.range (pullback.diagonal p))ᶜ := by
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    refine hσC ⟨x, rfl⟩ ⟨y, ?_⟩
    have e1 : (pullback.diagonal p ≫ s) y = ((σ ≫ s) ≫ s) x := by
      simp only [Scheme.Hom.comp_apply] at hy ⊢
      rw [hy]
    rwa [hΔs, Category.assoc, hss, Category.comp_id] at e1
  have e := hland _ hu
  have h1 : (σ ≫ s) ≫ pullback.fst p p = σ ≫ pullback.snd p p := by simp [s]
  rw [h1] at e
  have := congrArg (· ≫ pullback.snd p p) e
  simp only [Category.assoc, s, pullbackSymmetry_hom_comp_snd] at this
  rw [hσf] at this
  simpa only [Category.assoc] using this.symm

/-- **The covering involution of a finite étale double cover.** A finite étale morphism
`p : X ⟶ S` of constant degree `2` has an automorphism `τ` over `S` such that
`(id, τ) : X ⨿ X ⟶ X ×_S X` is an isomorphism. -/
theorem exists_involution_of_finrank_eq_two {X S : Scheme.{u}} (p : X ⟶ S) [IsFinite p]
    [Etale p] (h2 : p.finrank = 2) :
    ∃ τ : X ≅ X, ∃ hτ : τ.hom ≫ p = p,
      IsIso (coprod.desc (pullback.lift (𝟙 _) (𝟙 _) rfl)
        (pullback.lift (𝟙 _) τ.hom (by rw [hτ, Category.id_comp])) : X ⨿ X ⟶ pullback p p) := by
  set Δ := pullback.diagonal p
  have hΔc : IsClosed (Set.range Δ) := Δ.isClosedEmbedding.isClosed_range
  let C : (pullback p p).Opens := ⟨(Set.range Δ)ᶜ, hΔc.isOpen_compl⟩
  have hCι : Set.range C.ι = (Set.range Δ)ᶜ := Scheme.Opens.range_ι C
  have hcompl : IsCompl Δ.opensRange C.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι, isCompl_iff, disjoint_iff, codisjoint_iff]
    constructor <;> ext1 <;> simp [C, Scheme.Hom.opensRange]
  have hΨ : IsIso (coprod.desc Δ C.ι) := isIso_coprod_desc_of_isCompl Δ C.ι hcompl
  have hh : (coprod.desc Δ C.ι ≫ pullback.fst p p).finrank = 2 := by
    ext y
    rw [Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_pullback_fst, h2]
    rfl
  have hfC : coprod.inr ≫ coprod.desc Δ C.ι ≫ pullback.fst p p = C.ι ≫ pullback.fst p p := by
    rw [coprod.inr_desc_assoc]
  have hinr : (C.ι ≫ pullback.fst p p).finrank = 1 := by
    rw [← hfC]
    refine finrank_comp_inr_eq_one _ hh ?_
    rw [coprod.inl_desc_assoc, pullback.diagonal_fst, Scheme.Hom.finrank_eq_one_of_isIso (𝟙 X)]
  have : IsFinite (C.ι ≫ pullback.fst p p) := by
    rw [← hfC]
    infer_instance
  have : IsIso (C.ι ≫ pullback.fst p p) := (Scheme.Hom.isIso_iff_finrank_eq _).mpr hinr
  set g := inv (C.ι ≫ pullback.fst p p)
  set σ := g ≫ C.ι
  have hσf : σ ≫ pullback.fst p p = 𝟙 X := by
    simp only [σ, Category.assoc, g, IsIso.inv_hom_id]
  set τ' := σ ≫ pullback.snd p p
  have hτp : τ' ≫ p = p := by
    simp only [τ', Category.assoc, ← pullback.condition, reassoc_of% hσf]
  have hσ : pullback.lift (𝟙 X) τ' (by rw [hτp, Category.id_comp]) = σ :=
    pullback.hom_ext (by rw [pullback.lift_fst, hσf]) (by rw [pullback.lift_snd])
  have hσC : Set.range σ ⊆ (Set.range Δ)ᶜ := by
    rw [← hCι]
    rintro _ ⟨x, rfl⟩
    exact ⟨g x, rfl⟩
  have hττ : τ' ≫ τ' = 𝟙 X := snd_comp_comp_snd_eq_id p σ hσf hσC
    fun u hu => eq_comp_inv_comp_ι_of_range_subset C _ u (hCι ▸ hu)
  refine ⟨⟨τ', τ', hττ, hττ⟩, hτp, ?_⟩
  have : coprod.desc (pullback.lift (𝟙 _) (𝟙 _) rfl)
      (pullback.lift (𝟙 X) τ' (by rw [hτp, Category.id_comp])) =
      coprod.map (𝟙 X) g ≫ coprod.desc Δ C.ι := by
    rw [hσ]
    apply coprod.hom_ext <;> simp [σ, Δ, pullback.diagonal]
  change IsIso (coprod.desc (pullback.lift (𝟙 _) (𝟙 _) rfl)
    (pullback.lift (𝟙 X) τ' (by rw [hτp, Category.id_comp])))
  rw [this]
  infer_instance

end Involution

/-! ### Descent of functions along a double cover -/

section Descent

/-- Under the torsor isomorphism `(id, τ) : X ⨿ X ≅ X ×_S X`, two morphisms `g₁, g₂ : Z ⟶ X'`
with the same image in `S`, where `ι : X' ⟶ X` is a monomorphism along which `τ` lifts to `τ'`,
agree after composing with any `τ'`-invariant `f : X' ⟶ T`. -/
theorem eq_of_comp_eq_of_involution {X S : Scheme.{u}} (p : X ⟶ S) (τ : X ≅ X) (hτ : τ.hom ≫ p = p)
    (hΦ : IsIso (coprod.desc (pullback.lift (𝟙 _) (𝟙 _) rfl)
      (pullback.lift (𝟙 _) τ.hom (by rw [hτ, Category.id_comp])) : X ⨿ X ⟶ pullback p p))
    {X' : Scheme.{u}} (ι : X' ⟶ X) [Mono ι] (τ' : X' ⟶ X') (hτ' : τ' ≫ ι = ι ≫ τ.hom)
    {T : Scheme.{u}} (f : X' ⟶ T) (hf : τ' ≫ f = f) {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ X')
    (hg : (g₁ ≫ ι) ≫ p = (g₂ ≫ ι) ≫ p) : g₁ ≫ f = g₂ ≫ f := by
  set Φ := coprod.desc (pullback.lift (𝟙 _) (𝟙 _) rfl)
      (pullback.lift (𝟙 _) τ.hom (by rw [hτ, Category.id_comp]))
  set w := pullback.lift (g₁ ≫ ι) (g₂ ≫ ι) hg
  obtain ⟨E, hE₁, hE₂⟩ := exists_iso_coprod_pullback Φ w
  have : IsIso (pullback.snd Φ w) := inferInstance
  rw [← cancel_epi (E.hom ≫ pullback.snd Φ w)]
  have hE₁' : (coprod.inl ≫ E.hom ≫ pullback.snd Φ w) = _ := hE₁
  have hE₂' : (coprod.inr ≫ E.hom ≫ pullback.snd Φ w) = _ := hE₂
  apply coprod.hom_ext
  · have h1 := pullback.condition (f := coprod.inl ≫ Φ) (g := w)
    have e₁ := congrArg (· ≫ pullback.fst p p) h1
    have e₂ := congrArg (· ≫ pullback.snd p p) h1
    simp only [Category.assoc, Φ, coprod.inl_desc_assoc, pullback.lift_fst, pullback.lift_snd, w,
      Category.comp_id] at e₁ e₂
    have e : pullback.snd (coprod.inl ≫ Φ) w ≫ g₁ = pullback.snd (coprod.inl ≫ Φ) w ≫ g₂ := by
      rw [← cancel_mono ι, Category.assoc, Category.assoc, ← e₁, ← e₂]
    simp only [← Category.assoc] at hE₁' ⊢
    rw [hE₁', e]
  · have h1 := pullback.condition (f := coprod.inr ≫ Φ) (g := w)
    have e₁ := congrArg (· ≫ pullback.fst p p) h1
    have e₂ := congrArg (· ≫ pullback.snd p p) h1
    simp only [Category.assoc, Φ, coprod.inr_desc_assoc, pullback.lift_fst, pullback.lift_snd, w,
      Category.comp_id] at e₁ e₂
    have e : pullback.snd (coprod.inr ≫ Φ) w ≫ g₂ =
        pullback.snd (coprod.inr ≫ Φ) w ≫ g₁ ≫ τ' := by
      rw [← cancel_mono ι, Category.assoc, Category.assoc, Category.assoc, hτ', ← e₂,
        ← reassoc_of% e₁]
    simp only [← Category.assoc] at hE₂' ⊢
    rw [hE₂', e]
    simp only [Category.assoc, hf]

/-- The polynomial ring `ℤ[t]`, in universe `u`. -/
private noncomputable abbrev polyZ : CommRingCat.{u} := .of (Polynomial (ULift.{u} ℤ))

/-- The morphism to `Spec ℤ[t]` given by a global section. -/
private noncomputable def toA1 (Y : Scheme.{u}) (b : Γ(Y, ⊤)) : Y ⟶ Spec polyZ :=
  Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom
    ((Int.castRingHom _).comp ULift.ringEquiv.toRingHom) b))

private theorem toA1_appTop (Y : Scheme.{u}) (b : Γ(Y, ⊤)) :
    (toA1 Y b).appTop ((Scheme.ΓSpecIso polyZ).inv Polynomial.X) = b := by
  rw [toA1, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, ← CommRingCat.comp_apply,
    Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Iso.inv_hom_id_assoc]
  simp

private theorem comp_toA1 {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (b : Γ(Y, ⊤)) :
    g ≫ toA1 Y b = toA1 Y' (g.appTop b) := by
  rw [toA1, ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp, toA1]
  congr 2
  ext1
  exact Polynomial.ringHom_ext (fun c => by simp) (by simp)

/-- **Descent of functions along a `ℤ/2`-torsor.** Let `p : X ⟶ S` be flat, surjective and
affine, with an automorphism `τ` over `S` such that `(id, τ) : X ⨿ X ≅ X ×_S X`. Over an
affine open `V ⊆ S`, a `τ`-invariant function on `p⁻¹V` is the pull-back of a function on
`V`. -/
theorem exists_app_eq_of_involution {X S : Scheme.{u}} (p : X ⟶ S) [Flat p] [Surjective p]
    [IsAffineHom p] (τ : X ≅ X) (hτ : τ.hom ≫ p = p)
    (hΦ : IsIso (coprod.desc (pullback.lift (𝟙 _) (𝟙 _) rfl)
      (pullback.lift (𝟙 _) τ.hom (by rw [hτ, Category.id_comp])) : X ⨿ X ⟶ pullback p p))
    {V : S.Opens} (hV : IsAffineOpen V) (b : Γ(X, p ⁻¹ᵁ V))
    (hb : τ.hom.appLE (p ⁻¹ᵁ V) (p ⁻¹ᵁ V)
      (by rw [← Scheme.Hom.comp_preimage, hτ]) b = b) :
    ∃ a : Γ(S, V), p.app V a = b := by
  have hle : p ⁻¹ᵁ V ≤ τ.hom ⁻¹ᵁ (p ⁻¹ᵁ V) := by rw [← Scheme.Hom.comp_preimage, hτ]
  have : IsAffine V := hV
  have : IsAffine (p ⁻¹ᵁ V) := hV.preimage p
  have : Surjective (p ∣_ V) := by
    constructor
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := p.surjective y
    exact ⟨⟨x, hy⟩, Subtype.ext (morphismRestrict_base_coe p V ⟨x, hy⟩)⟩
  have : IsRegularEpi (p ∣_ V) := isRegularEpi_of_flat_of_surjective_of_isAffine (p ∣_ V)
  have hτ' : τ.hom.resLE (p ⁻¹ᵁ V) (p ⁻¹ᵁ V) hle ≫ (p ⁻¹ᵁ V).ι = (p ⁻¹ᵁ V).ι ≫ τ.hom :=
    Scheme.Hom.resLE_comp_ι _ _
  have hb' : (τ.hom.resLE (p ⁻¹ᵁ V) (p ⁻¹ᵁ V) hle).appTop ((p ⁻¹ᵁ V).topIso.inv b) =
      (p ⁻¹ᵁ V).topIso.inv b := by
    simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, CommRingCat.comp_apply]
    rw [← CommRingCat.comp_apply (p ⁻¹ᵁ V).topIso.inv (p ⁻¹ᵁ V).topIso.hom, Iso.inv_hom_id,
      CommRingCat.id_apply, hb]
  have hf : τ.hom.resLE (p ⁻¹ᵁ V) (p ⁻¹ᵁ V) hle ≫ toA1 _ ((p ⁻¹ᵁ V).topIso.inv b) =
      toA1 _ ((p ⁻¹ᵁ V).topIso.inv b) := by rw [comp_toA1, hb']
  have hw : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ p ⁻¹ᵁ V), g₁ ≫ p ∣_ V = g₂ ≫ p ∣_ V →
      g₁ ≫ toA1 _ ((p ⁻¹ᵁ V).topIso.inv b) = g₂ ≫ toA1 _ ((p ⁻¹ᵁ V).topIso.inv b) :=
    fun g₁ g₂ h => eq_of_comp_eq_of_involution p τ hτ hΦ (p ⁻¹ᵁ V).ι _ hτ' _ hf g₁ g₂ (by
      rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, reassoc_of% h])
  obtain ⟨v, hv⟩ : ∃ v, p ∣_ V ≫ v = toA1 _ ((p ⁻¹ᵁ V).topIso.inv b) :=
    ⟨_, EffectiveEpi.fac (p ∣_ V) _ hw⟩
  refine ⟨V.topIso.hom (v.appTop ((Scheme.ΓSpecIso polyZ).inv Polynomial.X)), ?_⟩
  have h1 := congrArg (fun g => g.appTop ((Scheme.ΓSpecIso polyZ).inv Polynomial.X)) hv
  have hp' : (p ∣_ V).appTop = V.topIso.hom ≫ p.appLE V (p ⁻¹ᵁ V) le_rfl ≫
      (p ⁻¹ᵁ V).topIso.inv := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    exact Scheme.Hom.resLE_app_top _ _
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hp'] at h1
  rw [toA1_appTop] at h1
  have h2 := congrArg (p ⁻¹ᵁ V).topIso.hom h1
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at h2
  rwa [Scheme.Hom.app_eq_appLE]

end Descent

end MMP.Flips
