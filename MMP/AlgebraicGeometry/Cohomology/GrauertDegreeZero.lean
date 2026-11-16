module
public import MMP.AlgebraicGeometry.ProjectiveBundle.VectorBundles
public import StacksFrontier.AlgebraicGeometry.Perfect.C1590Private.GlobalGenerationNearFibre
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankLocusDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.ResidueField
public import StacksFrontier.AlgebraicGeometry.Perfect.AcyclicDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineEssentialSurjectivity

/-!
# Constant zeroth fibre cohomology: locally free direct image and base change

Let `f : Z ⟶ T` be a projective morphism to a variety `T` over a field `k`, and `ℱ` a coherent
`𝒪_Z`-module flat over `T`. For a point `t : T` write `g : Spec κ(t) ⟶ T` for the canonical
morphism, `Z_t = Z ×_T Spec κ(t)` for the fibre, `p : Z_t ⟶ Z` and `q : Z_t ⟶ Spec κ(t)` for
the projections, and `ℱ_t = p^* ℱ`. Then `H⁰(Z_t, ℱ_t) = Γ(Spec κ(t), q_* ℱ_t)`, a
`κ(t)`-vector space. If `t ↦ dim_{κ(t)} H⁰(Z_t, ℱ_t)` is constant, equal to `h`, then `f_* ℱ`
is locally free of rank `h`, and for every `t` the base change morphism
`g^* f_* ℱ ⟶ q_* p^* ℱ` is an isomorphism. On global sections this is the natural map
`f_* ℱ ⊗ κ(t) ⟶ H⁰(Z_t, ℱ_t)`.

## Main results

* `MMP.isLocallyFreeOfRank_pushforward_and_isIso_baseChange_of_finrank_eq`: the theorem stated
  above (Grauert's theorem in degree zero).

## Implementation notes

The base change morphism `g^* f_* ℱ ⟶ q_* p^* ℱ` is written out explicitly. It is the morphism
corresponding under the adjunction `g^* ⊣ g_*` to the composite
`f_* ℱ ⟶ f_* p_* p^* ℱ ≅ (p ≫ f)_* p^* ℱ = (q ≫ g)_* p^* ℱ ≅ g_* q_* p^* ℱ`, where the first
arrow is `f_*` of the unit of `p^* ⊣ p_*`. The fibre `f_* ℱ ⊗ κ(t)` is the module of global
sections of `g^* f_* ℱ` (`MMP.Intersection.Scheme.Modules.fiber`). Since `Spec κ(t)` is a point,
asking for the morphism of sheaves to be an isomorphism is the same as asking for the map on
global sections to be bijective. The constancy hypothesis names its value `h`, and the local
freeness is given with that rank.

The proof is local on `T`. Near a point `t₀`, over an affine open `Spec A ⊆ T`, the global
sections of every base change of `ℱ` to an `A`-algebra in which a fixed `g ∉ 𝔭_{t₀}` is
invertible are free of rank `h` on a basis compatible with further base change
(`AlgebraicGeometry.C1590Private.exists_away_free_sections_of_finrank_le`, which uses that `A`
is reduced). Over `D(g)` this makes `f_* ℱ` free of rank `h`, and at the residue field of `t₀`
it makes the base change map on global sections carry a basis to a basis.

## References

* [R. Lazarsfeld, *Positivity in Algebraic Geometry I*][lazarsfeld2004]
* [R. Hartshorne, *Algebraic Geometry*, III.12.9][hartshorne1977]
-/

open CategoryTheory Limits AlgebraicGeometry

namespace MMP

universe u

/-! ### Points of an affine open and their residue fields -/

private theorem specMap_evaluation_fromSpec {T : Scheme} {V : T.Opens} (hV : IsAffineOpen V)
    (t : T) (ht : t ∈ V) :
    Spec.map (T.evaluation V t ht) ≫ hV.fromSpec = T.fromSpecResidueField t := by
  rw [Scheme.evaluation, Spec.map_comp, Category.assoc, ← IsAffineOpen.fromSpecStalk,
    IsAffineOpen.fromSpecStalk_eq_fromSpecStalk]
  rfl

private theorem ker_evaluation {T : Scheme} {V : T.Opens} (hV : IsAffineOpen V)
    (y : Spec Γ(T, V)) (t : T) (ht : t ∈ V) (hy : hV.fromSpec y = t) :
    RingHom.ker (T.evaluation V t ht).hom = y.asIdeal := by
  let s : Spec (T.residueField t) := IsLocalRing.closedPoint _
  have h1 : hV.fromSpec (Spec.map (T.evaluation V t ht) s) = t := by
    rw [← Scheme.Hom.comp_apply, specMap_evaluation_fromSpec, Scheme.fromSpecResidueField_apply]
  have h2 : Spec.map (T.evaluation V t ht) s = y :=
    hV.fromSpec.isOpenEmbedding.injective (h1.trans hy.symm)
  rw [← h2]
  change _ = Ideal.comap (T.evaluation V t ht).hom (IsLocalRing.maximalIdeal _)
  rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]

/-! ### Fibres over a chart -/

/-- The comparison of the base change of `f` along `k = j ≫ ι` with the base change along `ι`. -/
private noncomputable def liftFibre {Z T : Scheme} (f : Z ⟶ T) {A : CommRingCat}
    (ι : Spec A ⟶ T) {S : Scheme} (j : S ⟶ Spec A) (k : S ⟶ T) (hk : j ≫ ι = k) :
    pullback f k ⟶ pullback f ι :=
  pullback.lift (pullback.fst f k) (pullback.snd f k ≫ j)
    (by rw [Category.assoc, hk, pullback.condition])

private theorem liftFibre_fst {Z T : Scheme} (f : Z ⟶ T) {A : CommRingCat} (ι : Spec A ⟶ T)
    {S : Scheme} (j : S ⟶ Spec A) (k : S ⟶ T) (hk : j ≫ ι = k) :
    liftFibre f ι j k hk ≫ pullback.fst f ι = pullback.fst f k :=
  pullback.lift_fst _ _ _

private theorem isPullback_liftFibre {Z T : Scheme} (f : Z ⟶ T) {A : CommRingCat}
    (ι : Spec A ⟶ T) {S : Scheme} (j : S ⟶ Spec A) (k : S ⟶ T) (hk : j ≫ ι = k) :
    IsPullback (liftFibre f ι j k hk) (pullback.snd f k) (pullback.snd f ι) j := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f ι)
  rw [liftFibre_fst, hk]
  exact IsPullback.of_hasPullback f k

/-- The pullback of `ℱ` to the fibre through the chart is the pullback along the projection. -/
private noncomputable def liftFibreIso {Z T : Scheme} (f : Z ⟶ T) {A : CommRingCat}
    (ι : Spec A ⟶ T) {S : Scheme} (j : S ⟶ Spec A) (k : S ⟶ T) (hk : j ≫ ι = k)
    (F : Z.Modules) :
    (Scheme.Modules.pullback (liftFibre f ι j k hk)).obj
        ((Scheme.Modules.pullback (pullback.fst f ι)).obj F) ≅
      (Scheme.Modules.pullback (pullback.fst f k)).obj F :=
  (Scheme.Modules.pullbackComp _ _).app F ≪≫
    (Scheme.Modules.pullbackCongr (liftFibre_fst f ι j k hk)).app F

/-- Global sections of isomorphic modules are isomorphic. -/
private noncomputable def sectionsAddEquiv {P : Scheme} {N N' : P.Modules} (e : N ≅ N') :
    Γ(N, ⊤) ≃+ Γ(N', ⊤) where
  toFun x := e.hom.app ⊤ x
  invFun y := e.inv.app ⊤ y
  left_inv x := by
    change (e.hom.app ⊤ ≫ e.inv.app ⊤) x = x
    rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id]
    rfl
  right_inv y := by
    change (e.inv.app ⊤ ≫ e.hom.app ⊤) y = y
    rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl
  map_add' x y := map_add _ x y

/-- Isomorphic modules over a scheme over a field have global sections of the same dimension,
the one read through the structure morphism, the other on the direct image to the point. -/
private theorem finrank_sections_eq (K : Type*) [Field K] {P : Scheme} (q : P ⟶ Spec (.of K))
    {N N' : P.Modules} (e : N ≅ N') :
    letI := Stacks.Cech.sectionsModule q N ⊤
    letI : Module K Γ((Scheme.Modules.pushforward q).obj N', ⊤) :=
      Module.compHom _ (Scheme.ΓSpecIso (.of K)).inv.hom
    Module.finrank K Γ(N, ⊤) =
      Module.finrank K Γ((Scheme.Modules.pushforward q).obj N', ⊤) := by
  letI := Stacks.Cech.sectionsModule q N ⊤
  letI : Module K Γ((Scheme.Modules.pushforward q).obj N', ⊤) :=
    Module.compHom _ (Scheme.ΓSpecIso (.of K)).inv.hom
  have hb : ∀ c : K, (Stacks.Cech.baseRingHom q ⊤).hom c =
      q.app ⊤ ((Scheme.ΓSpecIso (.of K)).inv.hom c) := fun c => by
    simp only [Stacks.Cech.baseRingHom, Stacks.Cech.globalRingHom, homOfLE_refl, op_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  exact LinearEquiv.finrank_eq
    { sectionsAddEquiv e with
      map_smul' := fun c x => by
        change e.hom.app ⊤ ((Stacks.Cech.baseRingHom q ⊤).hom c • x) = _
        rw [Scheme.Modules.Hom.app_smul, hb]
        rfl }

/-- A linear map carrying a basis to a basis, read through a semilinear identification of the
target, is a base change. -/
private theorem isBaseChange_of_equivFun {R S M N N' : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] [Module R N]
    [IsScalarTower R S N] [AddCommGroup N'] [Module S N'] {n : ℕ}
    (bM : (Fin n → R) ≃ₗ[R] M) (bN : (Fin n → S) ≃ₗ[S] N') (c : N ≃+ N')
    (hc : ∀ (s : S) (x : N), c (s • x) = s • c x) (g : M →ₗ[R] N)
    (hg : ∀ i, c (g (bM (Pi.single i 1))) = bN (Pi.single i 1)) :
    IsBaseChange S g := by
  let c' : N ≃ₗ[S] N' := { c with map_smul' := hc }
  let b := Module.Basis.ofEquivFun bM.symm
  let b' := Module.Basis.ofEquivFun (bN.trans c'.symm).symm
  refine IsBaseChange.of_equiv ((Algebra.TensorProduct.basis S b).equiv b' (Equiv.refl _))
    fun x => ?_
  have : ((((Algebra.TensorProduct.basis S b).equiv b' (Equiv.refl _)).toLinearMap.restrictScalars
      R).comp (TensorProduct.mk R S M 1)) = g :=
    b.ext fun i => by
      simp only [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.restrictScalars_apply,
        LinearEquiv.coe_coe, ← Algebra.TensorProduct.basis_apply, Module.Basis.equiv_apply,
        Equiv.refl_apply]
      simp only [b, b', Module.Basis.coe_ofEquivFun, LinearEquiv.symm_symm,
        LinearEquiv.trans_apply]
      rw [← hg i]
      exact c'.symm_apply_apply _
  exact LinearMap.congr_fun this x

/-- A quasi-coherent module on `Spec R` which is a direct image `q_* N` whose global sections are
free of rank `n` over `R` is free of rank `n`. -/
private theorem nonempty_iso_free {R : CommRingCat.{u}} {X : Scheme.{u}} (q : X ⟶ Spec R)
    (M : (Spec R).Modules) [M.IsQuasicoherent] (N : X.Modules)
    (eM : M ≅ (Scheme.Modules.pushforward q).obj N) {n : ℕ}
    (b : letI := Stacks.Cech.sectionsModule (A := R) q N ⊤
      (Fin n → R) ≃ₗ[R] Γ(N, ⊤)) :
    Nonempty (M ≅ SheafOfModules.free (ULift.{u} (Fin n))) := by
  letI := Stacks.Cech.sectionsModule (A := R) q N ⊤
  have hb : ∀ c : R, q.app ⊤ ((Spec R).presheaf.map (⊤ : (Spec R).Opens).leTop.op
      ((Scheme.ΓSpecIso R).inv c)) = (Stacks.Cech.baseRingHom (A := R) q ⊤).hom c := fun c => by
    simp only [Stacks.Cech.baseRingHom, Stacks.Cech.globalRingHom, homOfLE_refl, op_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  let φ : Γ(M, ⊤) ≃ₗ[R] Γ(N, ⊤) :=
    { sectionsAddEquiv eM with
      map_smul' := fun c x => by
        change eM.hom.app ⊤ (c • x) = (Stacks.Cech.baseRingHom (A := R) q ⊤).hom c •
          (show Γ(N, ⊤) from eM.hom.app ⊤ x)
        rw [Scheme.Modules.smul_Spec_def, Scheme.Modules.Hom.app_smul, ← hb]
        rfl }
  let e₀ : Γ(M, ⊤) ≃ₗ[R] (Fin n → R) := φ.trans b.symm
  let e : Γ(M, ⊤) ≃ₗ[R] (ULift.{u} (Fin n) →₀ R) :=
    e₀.trans ((Finsupp.linearEquivFunOnFinite R R (ULift.{u} (Fin n))).trans
      (LinearEquiv.funCongrLeft R R Equiv.ulift.symm)).symm
  exact ⟨(asIso M.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso e.toModuleIso ≪≫
    tildeFinsupp (ULift.{u} (Fin n))⟩

/-! ### Degree-zero base change over an affine base from base change of global sections -/

section AffineBaseChange

open Stacks.Cech Stacks.AlgebraicGeometry.FlatBaseChange
  Stacks.AlgebraicGeometry.AcyclicDirectImageBaseChange
open scoped TensorProduct

/-- The structural ring maps of the identities of `Spec A` and `Spec B` on global sections form a
pushout square with `φ` and the map on global sections of `Spec.map φ`. -/
private theorem isPushout_baseRingHom_spec {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) :
    IsPushout (baseRingHom (𝟙 (Spec (.of A))) ⊤) (CommRingCat.ofHom φ)
      ((Spec.map (CommRingCat.ofHom φ)).app ⊤)
      (baseRingHom (𝟙 (Spec (.of B))) (Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ ⊤)) :=
  have := isIso_baseRingHom_id_top A
  have : IsIso (baseRingHom (𝟙 (Spec (.of B))) (Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ ⊤)) :=
    isIso_baseRingHom_id_top B
  IsPushout.of_horiz_isIso ⟨baseRingHom_comp_app _ _ _ _ IsPullback.of_id_snd ⊤⟩

/-- Over `Spec.map φ : Spec B ⟶ Spec A`, if the global sections of the pullback of `ℱ` are the
base change of the global sections of `ℱ`, through the pullback of sections, then the
degree-zero base-change morphism `g^* f_* ℱ ⟶ f'_* (g')^* ℱ` is an isomorphism. -/
private theorem isIso_pushforwardBaseChange_of_isBaseChange {A B : Type u} [CommRing A]
    [CommRing B] (φ : A →+* B) {X X' : Scheme.{u}}
    {f : X ⟶ Spec (.of A)} {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X}
    (H : IsPullback g' f' f (Spec.map (CommRingCat.ofHom φ))) [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent]
    (hbc₂ : letI : Algebra A B := φ.toAlgebra
      letI := sectionsModule f F ⊤
      letI := sectionsModule f' ((Scheme.Modules.pullback g').obj F) (g' ⁻¹ᵁ ⊤)
      letI := baseSectionsModule g' F φ f' (g' ⁻¹ᵁ ⊤)
      letI := isScalarTowerBaseSections g' F φ f' (g' ⁻¹ᵁ ⊤)
      IsBaseChange B (pullbackSectionsBaseₗ g' F φ f f'
        (fun W => baseRingHom_comp_app _ f f' g' H W) ⊤)) :
    IsIso (pushforwardBaseChange H.w F) := by
  have : ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_qcqs f F
  have := isQuasicoherent_pullback_pushforward (Spec.map (CommRingCat.ofHom φ)) f F
  have := isQuasicoherent_pushforward_pullback H F
  refine isIso_of_bijective_app_top _ ?_
  let : Algebra A B := φ.toAlgebra
  have hbc₁ := isBaseChange_pullbackSectionsBaseₗ (Spec.map (CommRingCat.ofHom φ))
    ((Scheme.Modules.pushforward f).obj F) φ (𝟙 _) (𝟙 _)
    (baseRingHom_comp_app _ _ _ _ IsPullback.of_id_snd)
    (isAffineOpen_top (Spec (.of A))) (isAffineOpen_top (Spec (.of B)))
    (isPushout_baseRingHom_spec φ)
  letI := sectionsModule (𝟙 (Spec (.of B)))
    ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).obj
      ((Scheme.Modules.pushforward f).obj F)) (Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ ⊤)
  letI := sectionsModule f' ((Scheme.Modules.pullback g').obj F) (g' ⁻¹ᵁ ⊤)
  letI := baseSectionsModule g' F φ f' (g' ⁻¹ᵁ ⊤)
  letI := isScalarTowerBaseSections g' F φ f' (g' ⁻¹ᵁ ⊤)
  letI := baseSectionsModule (Spec.map (CommRingCat.ofHom φ))
    ((Scheme.Modules.pushforward f).obj F) φ (𝟙 (Spec (.of B)))
    (Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ ⊤)
  letI := isScalarTowerBaseSections (Spec.map (CommRingCat.ofHom φ))
    ((Scheme.Modules.pushforward f).obj F) φ (𝟙 (Spec (.of B)))
    (Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ ⊤)
  letI := sectionsModule f F ⊤
  obtain ⟨e₁, h₁⟩ : ∃ e : B ⊗[A] Γ(F, (⊤ : X.Opens)) ≃ₗ[B]
        Γ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).obj
          ((Scheme.Modules.pushforward f).obj F), Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ ⊤),
      ∀ (b : B) (a : Γ(F, (⊤ : X.Opens))), e (b ⊗ₜ[A] a) =
        b • pullbackSections (Spec.map (CommRingCat.ofHom φ))
          ((Scheme.Modules.pushforward f).obj F) ⊤ a :=
    exists_linearEquiv_tmul_congr
      (iM := sectionsModule (𝟙 (Spec (.of A))) ((Scheme.Modules.pushforward f).obj F) ⊤)
      (jM := sectionsModule f F ⊤) (sectionsModule_pushforward f F) rfl _
      (by
        let := sectionsModule (𝟙 (Spec (.of A))) ((Scheme.Modules.pushforward f).obj F) ⊤
        exact ⟨hbc₁.equiv, fun b a => hbc₁.equiv_tmul b a⟩)
  let ψ : Γ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).obj
        ((Scheme.Modules.pushforward f).obj F), Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ ⊤) →ₗ[B]
      Γ((Scheme.Modules.pullback g').obj F, g' ⁻¹ᵁ ⊤) :=
    { toFun := fun y => (pushforwardBaseChange H.w F).app ⊤ y
      map_add' := fun _ _ => map_add _ _ _
      map_smul' := fun b y =>
        (Scheme.Modules.Hom.app_smul (pushforwardBaseChange H.w F)
          ((baseRingHom (𝟙 (Spec (.of B))) ⊤).hom b) y).trans <|
          congrArg (fun s : Γ(X', (⊤ : X'.Opens)) =>
          s • (show Γ((Scheme.Modules.pullback g').obj F, (⊤ : X'.Opens)) from
            (pushforwardBaseChange H.w F).app ⊤ y))
          (baseRingHom_pushforward_apply f' b) }
  exact bijective_of_tmul_normalisation e₁ h₁ hbc₂.equiv (fun b a => hbc₂.equiv_tmul b a) ψ
    (fun a => pushforwardBaseChange_app_top_unit H.w F a)

/-- Over `Spec.map ψ`, if the global sections of `p^* G` and of its pullback `(m ≫ p)^* G` are
free on bases matched by the pullback of sections, then the degree-zero base-change morphism of
`p^* G` is an isomorphism. -/
theorem isIso_baseChangeNatTrans_of_basis {B B' : Type u} [CommRing B] [CommRing B']
    (ψ : B →+* B') {X X' Y : Scheme.{u}} {s : X ⟶ Spec (.of B)} {s' : X' ⟶ Spec (.of B')}
    {m : X' ⟶ X} (sq : IsPullback m s' s (Spec.map (CommRingCat.ofHom ψ))) [QuasiCompact s]
    [QuasiSeparated s] (p : X ⟶ Y) (G : Y.Modules)
    [((Scheme.Modules.pullback p).obj G).IsQuasicoherent] {r : ℕ}
    (bM : letI := sectionsModule s ((Scheme.Modules.pullback p).obj G) ⊤
      (Fin r → B) ≃ₗ[B] Γ((Scheme.Modules.pullback p).obj G, ⊤))
    (bN : letI := sectionsModule s' ((Scheme.Modules.pullback (m ≫ p)).obj G) ⊤
      (Fin r → B') ≃ₗ[B'] Γ((Scheme.Modules.pullback (m ≫ p)).obj G, ⊤))
    (hb : ∀ i, ((Scheme.Modules.pullbackComp m p).hom.app G).app ⊤
        (pullbackSectionHom m ((Scheme.Modules.pullback p).obj G) ⊤ ⊤ (by simp)
          (bM (Pi.single i 1))) = bN (ψ ∘ Pi.single i 1)) :
    IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans sq.w).app
      ((Scheme.Modules.pullback p).obj G)) := by
  rw [baseChangeNatTrans_app_eq_pushforwardBaseChange]
  refine isIso_pushforwardBaseChange_of_isBaseChange (B := B') ψ sq _ ?_
  letI : Algebra B B' := ψ.toAlgebra
  letI := sectionsModule s ((Scheme.Modules.pullback p).obj G) ⊤
  letI : Module B' Γ((Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback p).obj G),
      m ⁻¹ᵁ ⊤) :=
    sectionsModule s' ((Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback p).obj G))
      (m ⁻¹ᵁ ⊤)
  letI : Module B Γ((Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback p).obj G),
      m ⁻¹ᵁ ⊤) :=
    baseSectionsModule m ((Scheme.Modules.pullback p).obj G) ψ s' (m ⁻¹ᵁ ⊤)
  letI : IsScalarTower B B'
      Γ((Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback p).obj G), m ⁻¹ᵁ ⊤) :=
    isScalarTowerBaseSections m ((Scheme.Modules.pullback p).obj G) ψ s' (m ⁻¹ᵁ ⊤)
  letI := sectionsModule s' ((Scheme.Modules.pullback (m ≫ p)).obj G) ⊤
  refine isBaseChange_of_equivFun bM bN
      (N := Γ((Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback p).obj G), m ⁻¹ᵁ ⊤))
      (sectionsAddEquiv ((Scheme.Modules.pullbackComp m p).app G))
      (fun c x => by
        change ((Scheme.Modules.pullbackComp m p).app G).hom.app ⊤
            ((baseRingHom s' (m ⁻¹ᵁ ⊤)).hom c • x) =
          (baseRingHom s' ⊤).hom c • ((Scheme.Modules.pullbackComp m p).app G).hom.app ⊤ x
        exact Scheme.Modules.Hom.app_smul _ _ _) _ fun i => ?_
  have hv : (ψ ∘ (Pi.single i 1 : Fin r → B)) = Pi.single i 1 := by
    funext j
    rw [Function.comp_apply, Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp
  refine Eq.trans ?_ (hv ▸ hb i)
  change ((Scheme.Modules.pullbackComp m p).app G).hom.app ⊤
      (pullbackSections m ((Scheme.Modules.pullback p).obj G) ⊤ (bM (Pi.single i 1))) = _
  congr 1
  change _ = ((Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback p).obj G)).presheaf.map
    (𝟙 _) (pullbackSections m ((Scheme.Modules.pullback p).obj G) ⊤ (bM (Pi.single i 1)))
  rw [CategoryTheory.Functor.map_id]
  rfl

end AffineBaseChange

/-- A module on `Y` whose pullback along an open immersion `j` is free is free on the image
of `j`. -/
theorem nonempty_restrict_opensRange_iso_free {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (E : Y.Modules) {I : Type u} (e : (Scheme.Modules.pullback j).obj E ≅ SheafOfModules.free I) :
    Nonempty (E.restrict j.opensRange.ι ≅ SheafOfModules.free I) :=
  let e' := j.isoOpensRange
  ⟨(Scheme.Modules.restrictFunctorIsoPullback j.opensRange.ι).app E ≪≫
    ((Scheme.Modules.pullbackId _).app _).symm ≪≫
    (Scheme.Modules.pullbackCongr e'.inv_hom_id).symm.app _ ≪≫
    ((Scheme.Modules.pullbackComp e'.inv e'.hom).app _).symm ≪≫
    (Scheme.Modules.pullback e'.inv).mapIso
      ((Scheme.Modules.pullbackComp e'.hom j.opensRange.ι).app E ≪≫
        (Scheme.Modules.pullbackCongr (Scheme.Hom.isoOpensRange_hom_ι j)).app E ≪≫ e) ≪≫
    Scheme.Modules.pullbackFreeIso e'.inv _⟩

/-- If, over a basic open `D(g)` of an open `Spec A ⊆ T`, the pulled-back module has free global
sections of rank `n`, then `f_* ℱ` is free of rank `n` near every point of `D(g)`. -/
theorem exists_mem_restrict_pushforward_iso_free_of_away {Z T : Scheme.{u}} (f : Z ⟶ T)
    [QuasiCompact f] [QuasiSeparated f] (F : Z.Modules) [F.IsFinitePresentation]
    {A : CommRingCat.{u}} (ι : Spec A ⟶ T) [IsOpenImmersion ι] (g : A) {y₀ : Spec A}
    (hg : g ∉ y₀.asIdeal) {t₀ : T} (hy₀ : ι y₀ = t₀) {n : ℕ}
    (b : letI := Stacks.Cech.sectionsModule (A := Localization.Away g)
            (pullback.snd (pullback.snd f ι)
              (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g)))))
            ((Scheme.Modules.pullback (pullback.fst (pullback.snd f ι)
              (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g)))))).obj
              ((Scheme.Modules.pullback (pullback.fst f ι)).obj F)) ⊤
      (Fin n → Localization.Away g) ≃ₗ[Localization.Away g]
        Γ((Scheme.Modules.pullback (pullback.fst (pullback.snd f ι)
          (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g)))))).obj
          ((Scheme.Modules.pullback (pullback.fst f ι)).obj F), ⊤)) :
    ∃ U : T.Opens, t₀ ∈ U ∧ Nonempty
      (((Scheme.Modules.pushforward f).obj F).restrict U.ι ≅
        SheafOfModules.free (ULift (Fin n))) := by
  have : F.IsQuasicoherent := Stacks.Modules.isQuasicoherent_of_isFinitePresentation F
  set α : A →+* Localization.Away g := algebraMap _ _
  set fA := pullback.snd f ι
  set gA := pullback.fst f ι
  set FA := (Scheme.Modules.pullback gA).obj F
  have sqA := IsPullback.of_hasPullback f ι
  have sq_g := IsPullback.of_hasPullback fA (Spec.map (CommRingCat.ofHom α))
  set sg := pullback.snd fA (Spec.map (CommRingCat.ofHom α))
  set pg := pullback.fst fA (Spec.map (CommRingCat.ofHom α))
  set Fg := (Scheme.Modules.pullback pg).obj FA
  have : FA.IsQuasicoherent := Stacks.Modules.isQuasicoherent_of_isFinitePresentation FA
  have hA : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans sqA.w).app F) :=
    Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat sqA F
  have hG : IsIso
      ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans sq_g.w).app FA) :=
    Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat sq_g FA
  set j := Spec.map (CommRingCat.ofHom α) ≫ ι
  set E := (Scheme.Modules.pushforward f).obj F
  have hga := Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_baseChangeNatTrans_vcomp
    sq_g.w sqA.w (sq_g.paste_horiz sqA).w F (Functor.map_isIso _ _) hG
  set M := (Scheme.Modules.pullback j).obj E
  have : M.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.FlatBaseChange.isQuasicoherent_pullback_pushforward j f F
  let eM : M ≅ (Scheme.Modules.pushforward sg).obj Fg :=
    asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      (sq_g.paste_horiz sqA).w).app F) ≪≫
      (Scheme.Modules.pushforward sg).mapIso ((Scheme.Modules.pullbackComp pg gA).app F).symm
  obtain ⟨iso1⟩ := nonempty_iso_free sg M Fg eM b
  refine ⟨j.opensRange, ?_, nonempty_restrict_opensRange_iso_free j E iso1⟩
  obtain ⟨y, hy⟩ : y₀ ∈ Set.range (PrimeSpectrum.comap α) := by
    rwa [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
  let y' : Spec (CommRingCat.of (Localization.Away g)) := y
  refine ⟨y', ?_⟩
  change ι (Spec.map (CommRingCat.ofHom α) y') = t₀
  rw [← hy₀]
  congr 1

/-! ### The local statement -/

/-- Near every point, `f_* ℱ` is free of rank `h` and the base change morphism at that point is
an isomorphism. -/
private theorem exists_restrict_pushforward_iso_free_and_isIso_pushforwardBaseChange
    {k : Type u} [Field k] {Z T : Scheme.{u}} (sT : T ⟶ Spec (.of k)) [IsVariety k sT]
    (f : Z ⟶ T) [IsProper f] (F : Z.Modules) [F.IsCoherent]
    (hF : IsFlatOver f.toLRSHom.toShHom F) (h : ℕ)
    (hh : ∀ t : T,
      letI : Module (T.residueField t) Γ((Scheme.Modules.pushforward
          (pullback.snd f (T.fromSpecResidueField t))).obj
          ((Scheme.Modules.pullback (pullback.fst f (T.fromSpecResidueField t))).obj F), ⊤) :=
        Module.compHom _ (Scheme.ΓSpecIso (T.residueField t)).inv.hom
      Module.finrank (T.residueField t) Γ((Scheme.Modules.pushforward
          (pullback.snd f (T.fromSpecResidueField t))).obj
          ((Scheme.Modules.pullback (pullback.fst f (T.fromSpecResidueField t))).obj F), ⊤) = h)
    (t₀ : T) :
    (∃ U : T.Opens, t₀ ∈ U ∧ Nonempty (((Scheme.Modules.pushforward f).obj F).restrict U.ι ≅
      SheafOfModules.free (ULift (Fin h)))) ∧
    IsIso (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange
      (pullback.condition (f := f) (g := T.fromSpecResidueField t₀)) F) := by
  classical
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : F.IsFinitePresentation :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_of_isCoherent' F
  have : F.IsQuasicoherent := Stacks.Modules.isQuasicoherent_of_isFinitePresentation F
  obtain ⟨V, hV, ht₀V, -⟩ := exists_isAffineOpen_mem_and_subset (x := t₀) (U := ⊤) trivial
  set ι := hV.fromSpec
  set fA := pullback.snd f ι
  set gA := pullback.fst f ι
  set FA := (Scheme.Modules.pullback gA).obj F
  have hflatA : IsFlatOver fA.toLRSHom.toShHom FA :=
    isFlatOver_of_moduleIso _ ((Stacks.ProjectiveBundleQuotients.pullbackIso gA).app F).symm
      (@modulePullback_isFlatOver _ _ _ _ _ _ _ _ (IsPullback.of_hasPullback f ι) F ‹_› hF)
  have hfib : ∀ (t : T) (ht : t ∈ V),
      letI : Module (T.residueField t)
          Γ((Scheme.Modules.pullback (liftFibre f ι (Spec.map (T.evaluation V t ht))
            (T.fromSpecResidueField t) (specMap_evaluation_fromSpec hV t ht))).obj FA, ⊤) :=
        Stacks.Cech.sectionsModule (pullback.snd f (T.fromSpecResidueField t))
          ((Scheme.Modules.pullback (liftFibre f ι (Spec.map (T.evaluation V t ht))
            (T.fromSpecResidueField t) (specMap_evaluation_fromSpec hV t ht))).obj FA) ⊤
      Module.finrank (T.residueField t)
        Γ((Scheme.Modules.pullback (liftFibre f ι (Spec.map (T.evaluation V t ht))
          (T.fromSpecResidueField t) (specMap_evaluation_fromSpec hV t ht))).obj FA, ⊤) = h :=
    fun t ht => (finrank_sections_eq (T.residueField t) _
      (liftFibreIso f ι _ _ (specMap_evaluation_fromSpec hV t ht) F)).trans (hh t)
  have hmem : ∀ y : Spec Γ(T, V), ι y ∈ V := fun y => by
    rw [← SetLike.mem_coe, ← hV.range_fromSpec]
    exact ⟨y, rfl⟩
  obtain ⟨y₀, hy₀⟩ : t₀ ∈ Set.range ι := by rwa [hV.range_fromSpec]
  obtain ⟨g, hg, r, Φ, hnat⟩ :=
    AlgebraicGeometry.C1590Private.exists_away_free_sections_of_finrank_le
    fA FA hflatA y₀.asIdeal h
    ⟨T.residueField t₀, inferInstance, (T.evaluation V t₀ ht₀V).hom,
      ker_evaluation hV y₀ t₀ ht₀V hy₀, _, _, _,
      isPullback_liftFibre f ι _ _ (specMap_evaluation_fromSpec hV t₀ ht₀V), (hfib t₀ ht₀V).le⟩
    (fun q _ => ⟨T.residueField (ι ⟨q, ‹_›⟩), inferInstance, (T.evaluation V _ (hmem _)).hom,
      ker_evaluation hV ⟨q, ‹_›⟩ _ _ rfl, _, _, _,
      isPullback_liftFibre f ι _ _ (specMap_evaluation_fromSpec hV _ (hmem _)),
      (hfib _ (hmem _)).ge⟩)
  have hu₀ : IsUnit ((T.evaluation V t₀ ht₀V).hom g) := isUnit_iff_ne_zero.2 fun h0 =>
    hg (by rwa [← ker_evaluation hV y₀ t₀ ht₀V hy₀])
  have hrh : r = h := by
    letI : Module (T.residueField t₀)
        Γ((Scheme.Modules.pullback (liftFibre f ι (Spec.map (T.evaluation V t₀ ht₀V))
          (T.fromSpecResidueField t₀) (specMap_evaluation_fromSpec hV t₀ ht₀V))).obj FA, ⊤) :=
      Stacks.Cech.sectionsModule (pullback.snd f (T.fromSpecResidueField t₀))
        ((Scheme.Modules.pullback (liftFibre f ι (Spec.map (T.evaluation V t₀ ht₀V))
          (T.fromSpecResidueField t₀) (specMap_evaluation_fromSpec hV t₀ ht₀V))).obj FA) ⊤
    exact (Module.finrank_fin_fun _).symm.trans
      ((Φ _ hu₀ (isPullback_liftFibre f ι _ _
        (specMap_evaluation_fromSpec hV t₀ ht₀V))).finrank_eq.trans (hfib t₀ ht₀V))
  set α : Γ(T, V) →+* Localization.Away g := algebraMap _ _
  have hα : IsUnit (α g) := IsLocalization.Away.algebraMap_isUnit g
  have sq_g := IsPullback.of_hasPullback fA (Spec.map (CommRingCat.ofHom α))
  set sg := pullback.snd fA (Spec.map (CommRingCat.ofHom α))
  set pg := pullback.fst fA (Spec.map (CommRingCat.ofHom α))
  set Fg := (Scheme.Modules.pullback pg).obj FA
  have : FA.IsQuasicoherent := Stacks.Modules.isQuasicoherent_of_isFinitePresentation FA
  have : Fg.IsQuasicoherent := Stacks.Modules.isQuasicoherent_of_isFinitePresentation Fg
  have sqA := IsPullback.of_hasPullback f ι
  have hA : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans sqA.w).app F) :=
    Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat sqA F
  have hG : IsIso
      ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans sq_g.w).app FA) :=
    Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat sq_g FA
  refine ⟨by
    subst hrh
    exact exists_mem_restrict_pushforward_iso_free_of_away f F ι g hg hy₀ (Φ α hα sq_g), ?_⟩
  let ψc : CommRingCat.of (Localization.Away g) ⟶ T.residueField t₀ :=
    CommRingCat.ofHom (IsLocalization.Away.lift g hu₀)
  have hspec :
      Spec.map ψc ≫ Spec.map (CommRingCat.ofHom α) = Spec.map (T.evaluation V t₀ ht₀V) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact DFunLike.congr_fun (IsLocalization.Away.lift_comp g hu₀) x
  have sq_t := isPullback_liftFibre f ι _ _ (specMap_evaluation_fromSpec hV t₀ ht₀V)
  set lt := liftFibre f ι (Spec.map (T.evaluation V t₀ ht₀V)) (T.fromSpecResidueField t₀)
    (specMap_evaluation_fromSpec hV t₀ ht₀V)
  set snd := pullback.snd f (T.fromSpecResidueField t₀)
  let m : pullback f (T.fromSpecResidueField t₀) ⟶ pullback fA (Spec.map (CommRingCat.ofHom α)) :=
    pullback.lift lt (snd ≫ Spec.map ψc)
      (by rw [Category.assoc, hspec, sq_t.w])
  have hm : m ≫ pg = lt := pullback.lift_fst _ _ _
  have sq1 : IsPullback m snd sg (Spec.map ψc) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) sq_g
    rwa [hm, hspec]
  have h1 := isIso_baseChangeNatTrans_of_basis ψc.hom sq1 pg FA (Φ α hα sq_g)
    (Φ (B := T.residueField t₀) (ψc.hom.comp α) (hα.map ψc.hom)
      (Stacks.Cech.isPullback_comp_specMap α ψc.hom fA sg snd pg m sq_g sq1))
    fun i => hnat α ψc.hom hα sq_g sq1 (Pi.single i 1)
  have h12 := Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_baseChangeNatTrans_vcomp
    sq1.w sq_g.w (sq1.paste_horiz sq_g).w FA (Functor.map_isIso _ _) h1
  have h123 := Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_baseChangeNatTrans_vcomp
    (sq1.paste_horiz sq_g).w sqA.w ((sq1.paste_horiz sq_g).paste_horiz sqA).w F
    (Functor.map_isIso _ _) h12
  rw [← Stacks.AlgebraicGeometry.FlatBaseChange.baseChangeNatTrans_app_eq_pushforwardBaseChange]
  exact Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_baseChangeNatTrans_congr
    (by rw [hm, liftFibre_fst]) (by rw [hspec, specMap_evaluation_fromSpec]) _ _ F h123

/-- **Grauert's theorem in degree zero.** Let `f : Z ⟶ T` be projective with `T` a variety over
`k`, and `ℱ` a coherent `𝒪_Z`-module flat over `T`. If for every point `t : T` the fibre
cohomology `H⁰(Z_t, ℱ_t) = Γ(Spec κ(t), q_* p^* ℱ)` (with `p, q` the projections of
`Z_t = Z ×_T Spec κ(t)`) has `κ(t)`-dimension `h`, then `f_* ℱ` is locally free of rank `h` and
for every `t` the base change morphism `g^* f_* ℱ ⟶ q_* p^* ℱ` along
`g = T.fromSpecResidueField t` is an isomorphism; on global sections it is the natural map
`f_* ℱ ⊗ κ(t) ⟶ H⁰(Z_t, ℱ_t)`. -/
@[mmp "lem_mmp_foundation_laz_constant_hzero_base_change"]
public theorem isLocallyFreeOfRank_pushforward_and_isIso_baseChange_of_finrank_eq
    {k : Type u} [Field k] {Z T : Scheme.{u}} (sT : T ⟶ Spec (.of k)) [IsVariety k sT]
    (f : Z ⟶ T) (hf : IsProjective f) (F : Z.Modules) [F.IsCoherent]
    (hF : IsFlatOver f.toLRSHom.toShHom F) (h : ℕ)
    (hh : ∀ t : T,
      letI : Module (T.residueField t) Γ((Scheme.Modules.pushforward
          (pullback.snd f (T.fromSpecResidueField t))).obj
          ((Scheme.Modules.pullback (pullback.fst f (T.fromSpecResidueField t))).obj F), ⊤) :=
        Module.compHom _ (Scheme.ΓSpecIso (T.residueField t)).inv.hom
      Module.finrank (T.residueField t) Γ((Scheme.Modules.pushforward
          (pullback.snd f (T.fromSpecResidueField t))).obj
          ((Scheme.Modules.pullback (pullback.fst f (T.fromSpecResidueField t))).obj F), ⊤) = h) :
    MMP.Intersection.Scheme.Modules.IsLocallyFreeOfRank ((Scheme.Modules.pushforward f).obj F) h ∧
      ∀ t : T, IsIso
        (((Scheme.Modules.pullbackPushforwardAdjunction (T.fromSpecResidueField t)).homEquiv
            _ _).symm
          ((Scheme.Modules.pushforward f).map
              ((Scheme.Modules.pullbackPushforwardAdjunction
                (pullback.fst f (T.fromSpecResidueField t))).unit.app F) ≫
            (Scheme.Modules.pushforwardComp (pullback.fst f (T.fromSpecResidueField t)) f).hom.app
              _ ≫
            (Scheme.Modules.pushforwardCongr pullback.condition).hom.app _ ≫
            (Scheme.Modules.pushforwardComp (pullback.snd f (T.fromSpecResidueField t))
              (T.fromSpecResidueField t)).inv.app _)) :=
  have := hf.isProper
  ⟨fun t =>
    (exists_restrict_pushforward_iso_free_and_isIso_pushforwardBaseChange sT f F hF h hh t).1,
  fun t =>
    (exists_restrict_pushforward_iso_free_and_isIso_pushforwardBaseChange sT f F hF h hh t).2⟩

end MMP
