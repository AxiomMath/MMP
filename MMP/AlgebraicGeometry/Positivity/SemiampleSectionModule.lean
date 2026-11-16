module

public import MMP.AlgebraicGeometry.Positivity.SemiampleSections
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.SerreFiniteness

/-!
# Twisted sections of a coherent module over a generated invertible module

Let `X` be proper over a Noetherian ring `R`, let `M` be an invertible `𝒪_X`-module, let
`σ₀, …, σ_N` be global sections of `M^{⊗ D}` (`D > 0`) generating it, and let `G` be a coherent
`𝒪_X`-module. Then the module of twisted sections `⨁_{n ≥ 0} Γ(X, G ⊗ M^{⊗ n})` is a finite module
over the section ring `⨁_{n ≥ 0} Γ(X, M^{⊗ n})`.

The argument is the module version of the one for the section ring itself. The `σⱼ` define a
morphism `g : X ⟶ ℙᴺ_R` with `g^* 𝒪(1) ≅ M^{⊗ D}`, and Serre's theorem for the coherent direct
image `g_*(G ⊗ M^{⊗ r})` (`0 ≤ r < D`) on `ℙᴺ_R`, carried to `X` by the projection formula, shows
that for `n ≫ 0` every section of `G ⊗ M^{⊗ (D + n)}` is `∑ⱼ sⱼ · aⱼ` with `sⱼ` fixed sections of
`M^{⊗ D}` and `aⱼ` sections of `G ⊗ M^{⊗ n}`. Each graded piece being finite over the global
functions, a strong induction on the degree finishes.

## Main results

* `MMP.SemiampleSections.moduleFinite_twistModule_of_forall_eq_sum_gsmul`: the graded module
  engine, for generation by a fixed family of sections of the section ring of positive degree.
* `MMP.SemiampleSections.exists_surjective_whiskerLeft_pullback`: Serre's theorem for
  `g_*(G ⊗ M^{⊗ r})`, carried to `X`.
* `MMP.SemiampleSections.exists_forall_eq_sum_gsmul_of_generatesStalks`: the generation statement.
* `MMP.SemiampleSections.moduleFinite_twistModule_of_generatesStalks`: the finiteness statement.

## References

* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace MMP.SemiampleSections

/-! ### Monoidal preliminaries -/

section Monoidal

open Stacks.TwistedSections Stacks.TensorPowers

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- Iterating `- ⊗ L` on an object is twisting it by `L`. -/
theorem iter_tensorRight_obj (L A : C) :
    ∀ k : ℕ, (iter (tensorRight L) k).obj A = twistPow A L k
  | 0 => rfl
  | k + 1 => congrArg (· ⊗ L) (iter_tensorRight_obj L A k)

/-- The unit twisted `D` times by `M`, compared with `M^{⊗ D}` in two ways, by the unitor. -/
theorem eqToHom_twistPow_unit_comp_twistPowIsoTensor (M : C) :
    ∀ D : ℕ, eqToHom (Stacks.SectionRingProjTheta.twistPow_unit M D).symm ≫
        (Stacks.AlgebraicGeometry.ProperAmpleCohomology.twistPowIsoTensor (𝟙_ C) M D).hom =
      (λ_ (natTensorPow M D)).inv
  | 0 => by
    change 𝟙 _ ≫ (ρ_ (𝟙_ C)).inv = (λ_ (𝟙_ C)).inv
    rw [Category.id_comp, unitors_inv_equal]
  | D + 1 => by
    rw [show eqToHom (Stacks.SectionRingProjTheta.twistPow_unit M (D + 1)).symm =
        eqToHom (Stacks.SectionRingProjTheta.twistPow_unit M D).symm ▷ M by
      rw [eqToHom_whiskerRight]; rfl]
    change _ ≫ ((Stacks.AlgebraicGeometry.ProperAmpleCohomology.twistPowIsoTensor
        (𝟙_ C) M D).hom ▷ M ≫ (α_ (𝟙_ C) (natTensorPow M D) M).hom) =
      (λ_ (natTensorPow M D ⊗ M)).inv
    rw [← Category.assoc, ← comp_whiskerRight,
      eqToHom_twistPow_unit_comp_twistPowIsoTensor M D, leftUnitor_tensor_inv]

/-- **The action of a section, through the twist.** For a section `s` of `M^{⊗ D}` and a twisted
section `a` of degree `n`, `s · a`, read in `(G ⊙ n) ⊗ M^{⊗ D}`, is `a ⊗ s`. -/
theorem gsmul_comp_hom (G M : C) {D n : ℕ} (s : Stacks.GradedSections.powSections M D)
    (a : twistSections G M n) :
    gsmul s a ≫ eqToHom ((congrArg (twistPow G M) (Nat.add_comm D n)).trans
        (Stacks.SectionRingProjTheta.twistPow_twistPow G M n D).symm) ≫
      (Stacks.AlgebraicGeometry.ProperAmpleCohomology.twistPowIsoTensor
        (twistPow G M n) M D).hom =
      a ≫ (ρ_ _).inv ≫ twistPow G M n ◁ s := by
  rw [gsmul_def, twistCongr, Stacks.AlgebraicGeometry.ProperAmpleCohomology.actMap_eq_twistPowMap]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [twistPowMap_twistPowIsoTensor, ← Category.assoc (eqToHom _),
    eqToHom_twistPow_unit_comp_twistPowIsoTensor, leftUnitor_inv_naturality_assoc,
    whisker_exchange, unitors_inv_equal, ← rightUnitor_inv_naturality_assoc]

variable [BraidedCategory C]

/-- Whiskering on the left by `T` commutes with finite sums once `- ⊗ T` is additive. -/
theorem whiskerLeft_sum_of_additive [Preadditive C] (T : C) [(tensorRight T).Additive]
    {Q R : C} {J : Type*} (t : Finset J) (g : J → (Q ⟶ R)) :
    T ◁ ∑ j ∈ t, g j = ∑ j ∈ t, T ◁ g j := by
  have h : ∀ f : Q ⟶ R, T ◁ f = (β_ T Q).hom ≫ (tensorRight T).map f ≫ (β_ T R).inv :=
    fun f => by
      change T ◁ f = (β_ T Q).hom ≫ f ▷ T ≫ (β_ T R).inv
      rw [← BraidedCategory.braiding_naturality_right_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h, Functor.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]
  exact Finset.sum_congr rfl fun j _ => (h (g j)).symm

/-- Tensoring on the left by `A` and then twisting `k` times by `E` is tensoring on the left by
`A` twisted `k` times by `E`. -/
def tensorLeftIterIso (E A : C) :
    (k : ℕ) → (tensorLeft A ⋙ iter (tensorRight E) k ≅ tensorLeft ((iter (tensorRight E) k).obj A))
  | 0 => Functor.rightUnitor _
  | k + 1 => (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (tensorLeftIterIso E A k) (tensorRight E) ≪≫
      Functor.isoWhiskerLeft _ (BraidedCategory.tensorLeftIsoTensorRight E).symm ≪≫
      (tensorLeftTensor E _).symm ≪≫ (tensoringLeft C).mapIso (β_ E _)

/-- Twisting `A ◁ ψ` `k` times by `E` is `A'` whiskered by `ψ`, for any `A'` isomorphic to `A`
twisted `k` times, as arrows. -/
def iterWhiskerLeftArrowIso (E : C) {A A' : C} (k : ℕ) (e : (iter (tensorRight E) k).obj A ≅ A')
    {Q B : C} (ψ : Q ⟶ B) :
    (iter (tensorRight E) k).mapArrow.obj (Arrow.mk (A ◁ ψ)) ≅ Arrow.mk (A' ◁ ψ) :=
  ((Functor.mapArrowFunctor C C).mapIso (tensorLeftIterIso E A k ≪≫
    (tensoringLeft C).mapIso e)).app (Arrow.mk ψ)

end Monoidal

/-! ### The graded module engine -/

section Engine

open AlgebraicGeometry Stacks.TwistedSections Stacks.TensorPowers Stacks.GradedSections

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

/-- **The graded module engine, generation by the ring.** Let `L` be invertible and `G` any
`𝒪_X`-module. If every graded piece of `Γ_*(X, G, L)` is spanned over the global functions by a
finite set, and there are `m ≥ 1` and sections `s₁, …, s_r` of `L^{⊗ m}` with every twisted
section of degree `m + n`, `n ≥ N`, of the form `∑ⱼ sⱼ · aⱼ`, then `Γ_*(X, G, L)` is a finite
module over the section ring `Γ_*(X, L)`, generated by its pieces of degree `< m + N`. -/
theorem moduleFinite_twistModule_of_forall_eq_sum_gsmul {X : Scheme.{u}} (G L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L]
    (hfin : ∀ p : ℕ, ∃ t : Finset (twistSections G L p),
      Submodule.span Γ(X, ⊤) (t : Set (twistSections G L p)) = ⊤)
    (m r N : ℕ) (hm : 1 ≤ m) (s : Fin r → powSections L m)
    (hgen : ∀ n : ℕ, N ≤ n → ∀ u : twistSections G L (m + n),
      ∃ a : Fin r → twistSections G L n, u = ∑ j, gsmul (s j) (a j)) :
    Module.Finite (sectionRing L) (twistModule G L) := by
  classical
  choose gen hgenspan using hfin
  let T : Finset (twistModule G L) :=
    (Finset.range (m + N)).biUnion fun p => (gen p).image (DirectSum.of (twistSections G L) p)
  have key : ∀ p : ℕ, ∀ u : twistSections G L p, DirectSum.of (twistSections G L) p u ∈
      Submodule.span (sectionRing L) (T : Set (twistModule G L)) := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      rcases lt_or_ge p (m + N) with hp | hp
      · intro u
        refine Submodule.span_mono ?_ (Stacks.SectionRingZero.of_mem_span L
          (gen p : Set (twistSections G L p)) (by rw [hgenspan p]; trivial))
        rintro _ ⟨y, hy, rfl⟩
        exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_range.mpr hp, Finset.mem_image_of_mem _ hy⟩
      · obtain ⟨n, rfl⟩ := Nat.le.dest (Nat.le_trans (Nat.le_add_right m N) hp)
        intro u
        obtain ⟨a, ha⟩ := hgen n (by omega) u
        rw [ha, map_sum]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [← of_smul_of]
        exact Submodule.smul_mem _ _ (ih n (by omega) (a j))
  refine Module.finite_def.mpr ⟨T, eq_top_iff.mpr fun z hz => ?_⟩
  clear hz
  induction z using DirectSum.induction_on with
  | zero => exact Submodule.zero_mem _
  | of p u => exact key p u
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end Engine

/-! ### Generation of high twists -/

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

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

/-- **Generation of high twists from surjectivity on sections.** Let `ψ : Q ⟶ M^{⊗ D}` be the sum
`∑ᵢ pᵢ ≫ sᵢ` of maps factoring through `𝒪_X`. If `(G ⊙ n) ◁ ψ` is surjective on global sections,
then every section of `G ⊗ M^{⊗ (D + n)}` is `∑ᵢ sᵢ · aᵢ` with `aᵢ` sections of `G ⊗ M^{⊗ n}`. -/
theorem exists_eq_sum_gsmul_of_surjective {X : Scheme.{u}} (G M : X.Modules) {D : ℕ} {ι : Type*}
    [Fintype ι] {Q : X.Modules} (ψ : Q ⟶ natTensorPow M D) (p : ι → (Q ⟶ 𝟙_ X.Modules))
    (s : ι → Stacks.GradedSections.powSections M D) (hps : ∑ i, p i ≫ s i = ψ) (n : ℕ)
    (h : Function.Surjective ((gammaTop X).map (twistPow G M n ◁ ψ)))
    (u : twistSections G M (D + n)) :
    ∃ a : ι → twistSections G M n, u = ∑ i, gsmul (s i) (a i) := by
  set e : twistPow G M (D + n) ≅ twistPow G M n ⊗ natTensorPow M D :=
    eqToIso ((congrArg (twistPow G M) (Nat.add_comm D n)).trans
        (Stacks.SectionRingProjTheta.twistPow_twistPow G M n D).symm) ≪≫
      Stacks.AlgebraicGeometry.ProperAmpleCohomology.twistPowIsoTensor (twistPow G M n) M D
  obtain ⟨x, hx⟩ := h (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _ (u ≫ e.hom))
  set v := (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).symm x
  have hv : v ≫ twistPow G M n ◁ ψ = u ≫ e.hom := by
    apply (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).injective
    rw [Stacks.AlgebraicGeometry.ProperAmpleCohomology.schemeGlobalSectionsAddEquiv_comp]
    exact (congrArg _ (AddEquiv.apply_symm_apply
      (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (twistPow G M n ⊗ Q))
      (show Γ(twistPow G M n ⊗ Q, ⊤) from x))).trans hx
  refine ⟨fun i => v ≫ twistPow G M n ◁ p i ≫ (ρ_ _).hom, ?_⟩
  rw [← cancel_mono e.hom, Preadditive.sum_comp, ← hv, ← hps, whiskerLeft_sum_of_additive,
    Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := gsmul_comp_hom G M (s i) (v ≫ twistPow G M n ◁ p i ≫ (ρ_ _).hom)
  simp only [e, Iso.trans_hom, eqToIso.hom] at this ⊢
  rw [this]
  simp

/-- **Surjectivity on sections of high twists of `G`, through a morphism to a projective
scheme.** In the situation of `MMP.SemiampleSections.exists_surjective_twistPowMap_pullback`, for a
coherent `G` and every `r`, the morphism `(G ⊙ (r + D k)) ◁ (g^* Ψ ≫ θ)` is surjective on global
sections for all large `k`. This is Serre's theorem for the coherent `g_*(G ⊙ r)` on `P`, carried
to `X` by the projection formula. -/
theorem exists_surjective_whiskerLeft_pullback {X P : Scheme.{u}} {R : Type u} [CommRing R]
    [IsNoetherianRing R] (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (π : P ⟶ Spec (CommRingCat.of R)) [IsProper π] (g : X ⟶ P) [IsProper g] (O : P.Modules)
    [Stacks.Ample.IsInvertibleModule P O] (hO : Stacks.Ample.IsAmple P O) {m : ℕ}
    (Ψ : (⨁ fun _ : Fin m => 𝟙_ P.Modules) ⟶ O) [Epi Ψ] (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] {D : ℕ}
    (θ : (Scheme.Modules.pullback g).obj O ≅ natTensorPow M D) (G : X.Modules) [G.IsCoherent]
    (r : ℕ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → Function.Surjective ((gammaTop X).map
      (twistPow G M (r + D * k) ◁ ((Scheme.Modules.pullback g).map Ψ ≫ θ.hom))) := by
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) :=
    isLocallyNoetherian_Spec.mpr inferInstance
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : (twistPow G M r).IsCoherent :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.isCoherent_twistPow _ _ inferInstance r
  have : ((Scheme.Modules.pushforward g).obj (twistPow G M r)).IsCoherent :=
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward g _
  obtain ⟨k₀, hk₀⟩ := exists_surjective_sheafTensor_map π O hO Ψ
    ((Scheme.Modules.pushforward g).obj (twistPow G M r))
  refine ⟨k₀, fun k hk => ?_⟩
  have h1 := surjective_of_surjective_pushforward g O (twistPow G M r) Ψ k (hk₀ k hk)
  have h3 := surjective_iter_whiskerLeft_comp θ _ k
    (surjective_iter_tensorRight_of_sheafTensor _ k h1)
  have eobj : (iter (tensorRight (natTensorPow M D)) k).obj (twistPow G M r) ≅
      twistPow G M (r + D * k) :=
    ((iterMulIso (tensorRight M) D k ≪≫ iterIso (iterTensorRightIso M D) k).app
        (twistPow G M r)).symm ≪≫
      eqToIso ((iter_tensorRight_obj M (twistPow G M r) (D * k)).trans
        (Stacks.SectionRingProjTheta.twistPow_twistPow G M r (D * k)))
  have h3' : Function.Surjective ((gammaTop X).map
      ((iter (tensorRight (natTensorPow M D)) k).mapArrow.obj
        (Arrow.mk (twistPow G M r ◁ ((Scheme.Modules.pullback g).map Ψ ≫ θ.hom)))).hom) := h3
  have h4 := surjective_map_of_arrowIso (gammaTop X)
    (iterWhiskerLeftArrowIso (natTensorPow M D) k eobj _) h3'
  exact h4

/-- **High twists of a coherent module are generated in one degree over the section ring.** Let
`X` be proper over a Noetherian ring, `M` invertible on `X` with `σ₀, …, σ_N` global sections of
`M^{⊗ D}` generating it, and `G` coherent. Then there are sections `s₀, …, s_N` of `M^{⊗ D}` and
an `N₀` such that for `n ≥ N₀` every section of `G ⊗ M^{⊗ (D + n)}` is `∑ⱼ sⱼ · aⱼ` with `aⱼ`
sections of `G ⊗ M^{⊗ n}`. -/
theorem exists_forall_eq_sum_gsmul_of_generatesStalks {X : Scheme.{u}} {R : Type u} [CommRing R]
    [IsNoetherianRing R] (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p] (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] {D N : ℕ} (hD : 0 < D)
    [Stacks.Ample.IsInvertibleModule X (natTensorPow M D)]
    (σ : Fin (N + 1) → Γ(natTensorPow M D, ⊤))
    (hσ : Stacks.ProjectiveFromSections.GeneratesStalks σ) (G : X.Modules) [G.IsCoherent] :
    ∃ (s : Fin (N + 1) → Stacks.GradedSections.powSections M D) (N₀ : ℕ), ∀ n : ℕ, N₀ ≤ n →
      ∀ u : twistSections G M (D + n),
        ∃ a : Fin (N + 1) → twistSections G M n, u = ∑ j, gsmul (s j) (a j) := by
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
    have : IsProper (g ≫ Stacks.Tag01VT.projectiveSpaceHom N (Spec (CommRingCat.of R))) := by
      rw [Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst σ hσ p]
      infer_instance
    exact IsProper.of_comp g (Stacks.Tag01VT.projectiveSpaceHom N (Spec (CommRingCat.of R)))
  obtain ⟨Ψ, hΨ⟩ := exists_epi_biproduct_of_generatesStalks (O := O) _
    (Stacks.ProjectiveSpaceModuli.taut_generates
      (projectiveSpaceOver.toIntegralAtUniverse N (Spec (CommRingCat.of R))))
  set ψ := (Scheme.Modules.pullback g).map Ψ ≫ θ.hom
  choose k₀ hk₀ using fun r => exists_surjective_whiskerLeft_pullback p
    (Stacks.Tag01VT.projectiveSpaceHom N (Spec (CommRingCat.of R))) g O hO Ψ M θ G r
  set w := Stacks.PullbackUnitSection.unitPullbackIso g
  refine ⟨fun j => w.inv ≫ (Scheme.Modules.pullback g).map
      (biproduct.ι (fun _ : Fin (N + 1) => 𝟙_ _) j) ≫ ψ,
    D * (Finset.range D).sup k₀, fun n hn u => ?_⟩
  have hk : k₀ (n % D) ≤ n / D :=
    (Finset.le_sup (Finset.mem_range.mpr (Nat.mod_lt n hD))).trans
      ((Nat.le_div_iff_mul_le hD).mpr (by rwa [Nat.mul_comm]))
  have hsurj := hk₀ (n % D) (n / D) hk
  rw [Nat.mod_add_div n D] at hsurj
  exact exists_eq_sum_gsmul_of_surjective G M ψ
    (fun j => (Scheme.Modules.pullback g).map (biproduct.π (fun _ : Fin (N + 1) => 𝟙_ _) j) ≫
      w.hom) _ (sum_pullback_biproduct_comp g ψ) n hsurj u

/-- **Finiteness of the twisted sections over a generated invertible module.** Let `X` be proper
over a Noetherian ring, `M` invertible on `X` with `σ₀, …, σ_N` global sections of `M^{⊗ D}`,
`D > 0`, generating it, and `G` coherent. Then `⨁_{n ≥ 0} Γ(X, G ⊗ M^{⊗ n})` is a finite module
over the section ring `⨁_{n ≥ 0} Γ(X, M^{⊗ n})`. -/
theorem moduleFinite_twistModule_of_generatesStalks {X : Scheme.{u}} {R : Type u} [CommRing R]
    [IsNoetherianRing R] (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p] (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] {D N : ℕ} (hD : 0 < D)
    [Stacks.Ample.IsInvertibleModule X (natTensorPow M D)]
    (σ : Fin (N + 1) → Γ(natTensorPow M D, ⊤))
    (hσ : Stacks.ProjectiveFromSections.GeneratesStalks σ) (G : X.Modules) [G.IsCoherent] :
    Module.Finite (Stacks.GradedSections.sectionRing M) (twistModule G M) := by
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) :=
    isLocallyNoetherian_Spec.mpr inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨s, N₀, hs⟩ := exists_forall_eq_sum_gsmul_of_generatesStalks p M hD σ hσ G
  refine moduleFinite_twistModule_of_forall_eq_sum_gsmul G M (fun q => ?_) D (N + 1) N₀ hD s hs
  have := Stacks.AlgebraicGeometry.ProperAmpleCohomology.isCoherent_twistPow G M inferInstance q
  exact Stacks.SectionRingZero.exists_finset_span_eq_top p (twistPow G M q)

end Scheme

end MMP.SemiampleSections

end
