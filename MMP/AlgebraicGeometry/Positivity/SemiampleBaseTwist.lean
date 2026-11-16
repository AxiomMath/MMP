module

public import MMP.AlgebraicGeometry.Divisor.LinearSeries
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubmodule.RestrictEpi
public import StacksFrontier.AlgebraicGeometry.TensorSheafSpellingIso.Strict

/-!
# Removing a base twist from a globally generated adjoint

Let `f : T ⟶ Z` be a morphism of Noetherian schemes, and let `L` and `G` be invertible sheaves
on `T` and `Z`. If some positive power of `L ⊗ f^*G` is globally generated, then `L` is
semiample over `Z`: some positive power `L^{⊗ m}` is `f`-generated, that is, the counit
`f^* f_* L^{⊗ m} ⟶ L^{⊗ m}` is an epimorphism.

## Main results

* `MMP.Fourfold.exists_epi_counit_tensorPow_of_isGloballyGenerated_tensorPow_pullback`.

## Implementation notes

The auxiliary lemmas live in the namespace `Proof_lem_fourfold_remove_generated_base_twist`,
opened only for the main result. Over an open `V ⊆ Z` on which `G^{⊗ m}` is trivial,
`(L^{⊗ m} ⊗ f^*G^{⊗ m})|_{f⁻¹V} ≅ L^{⊗ m}|_{f⁻¹V}`, so the global generators give sections of
`L^{⊗ m}` over `f⁻¹V` generating it near every point there; such sections lie in the image of
the counit over `f⁻¹V` (triangle identity of `f^* ⊣ f_*`), so the counit is locally surjective.
A rational invertible sheaf is an element of `Pic(T) ⊗ ℚ`; with a common denominator the
statement for invertible sheaves and positive powers covers the rational case.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace Proof_lem_fourfold_remove_generated_base_twist

open MMP.Intersection MMP.Intersection.Scheme.Modules

/-! ### Trivializations and tensor products -/

section Trivial

/-- If `B` becomes trivial along `j`, then `j^*(A ⊗ B) ≅ j^*A`. -/
private def pullbackTensorIsoOfIsoUnit {U X : Scheme.{u}} (j : U ⟶ X) (A B : X.Modules)
    (e : (Scheme.Modules.pullback j).obj B ≅ SheafOfModules.unit U.ringCatSheaf) :
    (Scheme.Modules.pullback j).obj (A ⊗ B) ≅ (Scheme.Modules.pullback j).obj A :=
  let c := (Scheme.Modules.pullbackPushforwardAdjunction j).leftAdjointUniq
      (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction j.toLRSHom.toShHom)
  c.app _ ≪≫ Stacks.RelativeVeryAmple.pullbackTensorModulesIso j A B ≪≫
    Stacks.RelativeVeryAmple.tensorModulesMapIso U (Iso.refl _) ((c.app B).symm ≪≫ e) ≪≫
    Stacks.TensorSheafSpellingIso.tensorModulesRightUnitor U _ ≪≫ (c.app A).symm

/-- A module trivial over `V ⊆ Z` pulls back to a module trivial over `f⁻¹V`. -/
private def pullbackPreimageIsoUnit {T Z : Scheme.{u}} (f : T ⟶ Z) (H : Z.Modules) (V : Z.Opens)
    (e : (Scheme.Modules.pullback V.ι).obj H ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) :
    (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj ((Scheme.Modules.pullback f).obj H) ≅
      SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf :=
  (Scheme.Modules.pullbackComp (f ⁻¹ᵁ V).ι f).app H ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι f V).symm).app H ≪≫
    ((Scheme.Modules.pullbackComp (f ∣_ V) V.ι).app H).symm ≪≫
    (Scheme.Modules.pullback (f ∣_ V)).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso (f ∣_ V)

/-- Every point of `X` has a neighbourhood over which a line bundle is trivial. -/
private theorem exists_pullback_iso_unit_of_isLineBundle {X : Scheme.{u}} {G : X.Modules}
    (hG : IsLineBundle G) (x : X) :
    ∃ V : X.Opens, x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj G ≅
        SheafOfModules.unit V.toScheme.ringCatSheaf) := by
  obtain ⟨V, hxV, ⟨e⟩⟩ := hG x
  exact ⟨V, hxV, ⟨((Scheme.Modules.restrictFunctorIsoPullback V.ι).app G).symm ≪≫ e ≪≫
    Limits.coproductUniqueIso _⟩⟩

/-- If `j^*G` is trivial, then so is `j^*(G^{⊗ n})` for every `n`. -/
private def pullbackTensorPowIsoUnit {U X : Scheme.{u}} (j : U ⟶ X) (G : X.Modules)
    (e : (Scheme.Modules.pullback j).obj G ≅ SheafOfModules.unit U.ringCatSheaf) :
    (n : ℕ) → ((Scheme.Modules.pullback j).obj (tensorPow G n) ≅
      SheafOfModules.unit U.ringCatSheaf)
  | 0 => Scheme.Modules.pullbackUnitIso j
  | n + 1 => pullbackTensorIsoOfIsoUnit j (tensorPow G n) G e ≪≫ pullbackTensorPowIsoUnit j G e n

end Trivial

/-! ### Local generation by sections over a fixed open -/

section Sections

variable {X : Scheme.{u}}

/-- `P` is *generated over* the open `A` if near every point of `A` every local section of `P` is
a combination of restrictions of sections of `P` over `A`. -/
private def IsGeneratedOver (P : X.Modules) (A : X.Opens) : Prop :=
  ∀ x ∈ A, ∀ (W : X.Opens) (t : Γ(P, W)), x ∈ W →
    ∃ (W' : X.Opens) (hW : W' ≤ W) (hA : W' ≤ A), x ∈ W' ∧
      ∃ (n : ℕ) (r : Fin n → Γ(X, W')) (s : Fin n → Γ(P, A)),
        P.presheaf.map (homOfLE hW).op t = ∑ i, r i • P.presheaf.map (homOfLE hA).op (s i)

/-- Composing two restriction maps of `P` is restriction to the smaller open. -/
private lemma map_map (P : X.Modules) {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (a : Γ(P, U)) :
    P.presheaf.map (homOfLE h₂).op (P.presheaf.map (homOfLE h₁).op a) =
      P.presheaf.map (homOfLE (h₂.trans h₁)).op a := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- A morphism of modules commutes with restriction. -/
private lemma app_map {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (h : V ≤ U)
    (a : Γ(M, U)) :
    φ.app V (M.presheaf.map (homOfLE h).op a) = N.presheaf.map (homOfLE h).op (φ.app U a) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) a

/-- A morphism of modules sends a combination of restrictions of sections over `A` to the same
combination of restrictions of their images. -/
private lemma app_sum_smul_map {M N : X.Modules} (φ : M ⟶ N) {A W : X.Opens} (h : W ≤ A)
    {n : ℕ} (r : Fin n → Γ(X, W)) (s : Fin n → Γ(M, A)) :
    φ.app W (∑ i, r i • M.presheaf.map (homOfLE h).op (s i)) =
      ∑ i, r i • N.presheaf.map (homOfLE h).op (φ.app A (s i)) := by
  simp only [map_sum, Scheme.Modules.Hom.app_smul, app_map]

/-- The restriction maps of `M|_U` are those of `M` on the images of the opens. -/
private lemma restrict_presheaf_map (M : X.Modules) {U : X.Opens} {O O' : U.toScheme.Opens}
    (h : O' ≤ O) (a : Γ(M.restrict U.ι, O)) :
    (M.restrict U.ι).presheaf.map (homOfLE h).op a =
      M.presheaf.map (homOfLE (U.ι.image_mono h)).op a :=
  rfl

/-- A globally generated module is generated over every open. -/
private lemma isGeneratedOver_of_isGloballyGenerated {P : X.Modules}
    (hP : IsGloballyGenerated P) (A : X.Opens) : IsGeneratedOver P A := by
  intro x hxA W t hxW
  obtain ⟨W₀, hW₀, hxW₀, n, s, r, h⟩ := hP x (Set.mem_univ x) W hxW t
  refine ⟨W₀ ⊓ A, inf_le_left.trans hW₀, inf_le_right, ⟨hxW₀, hxA⟩, n,
    fun i => X.presheaf.map (homOfLE (inf_le_left : W₀ ⊓ A ≤ W₀)).op (r i),
    fun i => P.presheaf.map (homOfLE le_top).op (s i), ?_⟩
  rw [← map_map P hW₀ inf_le_left, h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.map_smul, map_map, map_map]

end Sections

/-- Generation over an open `U` is transported along an isomorphism of the restrictions to `U`. -/
private lemma IsGeneratedOver.of_restrict_iso {X : Scheme.{u}} {P Q : X.Modules} {U : X.Opens}
    (ψ : Q.restrict U.ι ≅ P.restrict U.ι) (hQ : IsGeneratedOver Q U) : IsGeneratedOver P U := by
  intro x hxU W t hxW
  let O : U.toScheme.Opens := U.ι ⁻¹ᵁ W
  have hW₀ : U.ι ''ᵁ O ≤ W := U.ι.image_preimage_le W
  let x' : U.toScheme := ⟨x, hxU⟩
  let t₀ : Γ(P.restrict U.ι, O) := P.presheaf.map (homOfLE hW₀).op t
  let q : Γ(Q, U.ι ''ᵁ O) := ψ.inv.app O t₀
  obtain ⟨W₁, hW₁, hU₁, hxW₁, n, r, s, hs⟩ := hQ x hxU _ q ⟨x', hxW, rfl⟩
  let O₁ : U.toScheme.Opens := U.ι ⁻¹ᵁ W₁
  have hO₁ : O₁ ≤ O := U.ι.preimage_mono (hW₁.trans hW₀)
  have h₂ : U.ι ''ᵁ O₁ ≤ W₁ := U.ι.image_preimage_le W₁
  have hUtop : U ≤ U.ι ''ᵁ ⊤ := (Scheme.Opens.ι_image_top U).ge
  have hUtop' : U.ι ''ᵁ ⊤ ≤ U := (Scheme.Opens.ι_image_top U).le
  let s' : Fin n → Γ(Q.restrict U.ι, ⊤) := fun i => Q.presheaf.map (homOfLE hUtop').op (s i)
  let w : Fin n → Γ(P.restrict U.ι, ⊤) := fun i => ψ.hom.app ⊤ (s' i)
  let r' : Fin n → Γ(X, U.ι ''ᵁ O₁) := fun i => X.presheaf.map (homOfLE h₂).op (r i)
  refine ⟨U.ι ''ᵁ O₁, h₂.trans (hW₁.trans hW₀), h₂.trans hU₁, ⟨x', hxW₁, rfl⟩, n, r',
    fun i => P.presheaf.map (homOfLE hUtop).op (w i), ?_⟩
  let ρ : Fin n → Γ(U.toScheme, O₁) := fun i => (U.ι.appIso O₁).hom (r' i)
  have hρ : ∀ i, (U.ι.appIso O₁).inv (ρ i) = r' i := fun i =>
    ConcreteCategory.congr_hom (U.ι.appIso O₁).hom_inv_id (r' i)
  have hsmul : ∀ (M : X.Modules) (a : Γ(M.restrict U.ι, O₁)) (c : Γ(U.toScheme, O₁)),
      c • a = HSMul.hSMul (β := Γ(M, U.ι ''ᵁ O₁)) ((U.ι.appIso O₁).inv c) a :=
    fun _ _ _ => rfl
  have hq : (Q.restrict U.ι).presheaf.map (homOfLE hO₁).op q =
      ∑ i, ρ i • (Q.restrict U.ι).presheaf.map (homOfLE le_top).op (s' i) := by
    change Q.presheaf.map (homOfLE (h₂.trans hW₁)).op q = _
    rw [← map_map Q hW₁ h₂, hs, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsmul, hρ, Scheme.Modules.map_smul, map_map, restrict_presheaf_map]
    exact congrArg (r' i • ·) (map_map Q hUtop' _ (s i)).symm
  have ht : (P.restrict U.ι).presheaf.map (homOfLE hO₁).op t₀ =
      ∑ i, ρ i • (P.restrict U.ι).presheaf.map (homOfLE le_top).op (w i) := by
    have h1 : ψ.hom.app O q = t₀ := by
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, ψ.inv_hom_id]
      rfl
    rw [← h1, ← app_map, hq, app_sum_smul_map]
  rw [← map_map P hW₀ (h₂.trans hW₁)]
  refine ht.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [hsmul, hρ]
  exact congrArg (r' i • ·) (map_map P hUtop (h₂.trans hU₁) (w i)).symm

/-! ### The counit -/

/-- If near every point of `T` the module `M` is generated over the inverse image of an open of
`Z`, then the counit `f^* f_* M ⟶ M` is an epimorphism. -/
private lemma epi_counit_of_forall_isGeneratedOver {T Z : Scheme.{u}} (f : T ⟶ Z) (M : T.Modules)
    (h : ∀ x : T, ∃ V : Z.Opens, f x ∈ V ∧ IsGeneratedOver M (f ⁻¹ᵁ V)) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M) := by
  apply Stacks.AlgebraicGeometry.FiniteTypeSubmodule.epi_of_isLocallySurjective_mapPresheaf
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro W t x hxW
  obtain ⟨V, hxV, hV⟩ := h x
  obtain ⟨W', hW, hA, hxW', n, r, s, hs⟩ := hV x hxV W t hxW
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let F' := (Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward f).obj M)
  let e : Fin n → Γ(F', f ⁻¹ᵁ V) := fun i =>
    (adj.unit.app ((Scheme.Modules.pushforward f).obj M)).app V (s i)
  have he : ∀ i, (adj.counit.app M).app (f ⁻¹ᵁ V) (e i) = s i := fun i =>
    congrArg (fun φ : (Scheme.Modules.pushforward f).obj M ⟶
      (Scheme.Modules.pushforward f).obj M => (φ.app V).hom (s i)) (adj.right_triangle_components M)
  refine ⟨W', hW, ⟨∑ i, r i • F'.presheaf.map (homOfLE hA).op (e i), ?_⟩, hxW'⟩
  refine (app_sum_smul_map (adj.counit.app M) hA r e).trans ?_
  simp only [he]
  exact hs.symm

end Proof_lem_fourfold_remove_generated_base_twist

namespace MMP.Fourfold

open MMP.Intersection MMP.Intersection.Scheme.Modules
open Proof_lem_fourfold_remove_generated_base_twist

/-- **Removing a base twist.** Let `f : T ⟶ Z` be a morphism of Noetherian schemes and `L`, `G`
invertible sheaves on `T` and `Z`. If `L^{⊗ m} ⊗ f^*(G^{⊗ m})` is globally generated for some
`m > 0`, then `L` is `f`-semiample: for some `m > 0` the counit `f^* f_* L^{⊗ m} ⟶ L^{⊗ m}` of
`Scheme.Modules.pullbackPushforwardAdjunction f` is an epimorphism. -/
@[mmp "lem_fourfold_remove_generated_base_twist"]
public theorem exists_epi_counit_tensorPow_of_isGloballyGenerated_tensorPow_pullback
    {T Z : Scheme.{u}} [IsNoetherian T] [IsNoetherian Z] (f : T ⟶ Z)
    {L : T.Modules} {G : Z.Modules} (hL : IsLineBundle L) (hG : IsLineBundle G)
    (h : ∃ m : ℕ, 0 < m ∧
      IsGloballyGenerated (tensorPow L m ⊗ (Scheme.Modules.pullback f).obj (tensorPow G m))) :
    ∃ m : ℕ, 0 < m ∧
      Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app (tensorPow L m)) := by
  obtain ⟨m, hm, hgg⟩ := h
  refine ⟨m, hm, epi_counit_of_forall_isGeneratedOver f _ fun x => ?_⟩
  obtain ⟨V, hxV, ⟨e⟩⟩ := exists_pullback_iso_unit_of_isLineBundle hG (f x)
  refine ⟨V, hxV, ?_⟩
  let eK := pullbackPreimageIsoUnit f (tensorPow G m) V (pullbackTensorPowIsoUnit V.ι G e m)
  let ψ := (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app _ ≪≫
    pullbackTensorIsoOfIsoUnit _ (tensorPow L m) _ eK ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app (tensorPow L m)).symm
  exact IsGeneratedOver.of_restrict_iso ψ (isGeneratedOver_of_isGloballyGenerated hgg _)

end MMP.Fourfold
