module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksExists
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.ThomClassPullback
public import MMP.AlgebraicTopology.SingularCohomology.Relative.Excision

/-!
# Two orientation data related by a bundle isomorphism give the same class (Stacks bundles)

Let `D₁ = (ℰ₁, σ₁, V₁, Q₁)` and `D₂ = (ℰ₂, σ₂, V₂, Q₂)` be orientation data of a closed imbedding
`i : X → Y` of complex schemes (`MMP.Modules.RegularImbeddingOrientationDatum`). If on an open
neighbourhood `W ⊆ V₁ ∩ V₂` of `X(ℂ)` there is an isomorphism `φ : Q₁|_W ≅ Q₂|_W` of complex
topological vector bundles carrying `σ̄₁` to `σ̄₂`, then the orientation classes defined by `D₁`
and `D₂` agree: `φ` pulls the Thom class of `Q₂` back to that of `Q₁`
(`MMP.ThomClass.IsThomClassOfRank.map`), and restriction to `W` is injective on
`H^{2d}(Y, Y - X)` (excision).

## Main results

* `MMP.Modules.RegularImbeddingOrientationDatum.eq_of_continuous_equiv`: the comparison.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Bundle

namespace MMP.Modules

open UnderlyingSpace MMP.ThomClass

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]

namespace RegularImbeddingOrientationDatum

variable {i : X ⟶ Y} [i.IsOver (Spec (.of ℂ))] {d : ℕ} (R : Type) [CommRing R]

/-- `σ̄` maps `V - X` into `Q - 0_Q`, as a map of pairs. -/
lemma compl_subset_preimage_sectionBarHom (D : RegularImbeddingOrientationDatum i d) :
    (Subtype.val ⁻¹' range (UnderlyingSpace.map i) : Set D.nbhd)ᶜ ⊆
      D.sectionBarHom ⁻¹' (range (Bundle.zeroSection D.F D.Q))ᶜ :=
  fun _ hy h ↦ hy (D.sectionBar_preimage_subset h)

/-- `σ̄^* u_Q`, with `u_Q` first moved to degree `2d`. -/
lemma thomPullback_apply (D : RegularImbeddingOrientationDatum i d)
    (uQ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D.F D.Q))
      (range (Bundle.zeroSection D.F D.Q)) (2 * Module.finrank ℂ D.F : ℕ))
    (e : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D.F D.Q))
      (range (Bundle.zeroSection D.F D.Q)) (2 * Module.finrank ℂ D.F : ℕ) =
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D.F D.Q))
        (range (Bundle.zeroSection D.F D.Q)) (2 * d : ℕ)) :
    (D.thomPullback R).hom uQ = (relativeSingularCohomology.map R (ModuleCat.of R R)
      D.sectionBarHom D.compl_subset_preimage_sectionBarHom _).hom ((eqToHom e).hom uQ) := by
  have h1 : (relativeSingularCohomology.map R (ModuleCat.of R R) (𝟙 (TopCat.of D.nbhd))
      (A := (D.sectionBar ⁻¹' range (Bundle.zeroSection D.F D.Q))ᶜ)
      (A' := (Subtype.val ⁻¹' range (UnderlyingSpace.map i))ᶜ)
      (fun _ h ↦ Set.compl_subset_compl.mpr D.sectionBar_preimage_subset h)
      (2 * Module.finrank ℂ D.F : ℕ)).hom
      ((relativeSingularCohomology.map R (ModuleCat.of R R) D.sectionBarHom
        (A := (range (Bundle.zeroSection D.F D.Q))ᶜ)
        (A' := (D.sectionBar ⁻¹' range (Bundle.zeroSection D.F D.Q))ᶜ)
        (fun _ hx ↦ hx) (2 * Module.finrank ℂ D.F : ℕ)).hom uQ) =
      (relativeSingularCohomology.map R (ModuleCat.of R R) D.sectionBarHom
        D.compl_subset_preimage_sectionBarHom (2 * Module.finrank ℂ D.F : ℕ)).hom uQ :=
    (relativeSingularCohomology.map_comp_apply' R _ _ D.compl_subset_preimage_sectionBarHom _
      uQ).symm.trans (relativeSingularCohomology.map_congr_apply R (Category.id_comp _) _ _ _ _)
  exact (congrArg (eqToHom (show cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of D.nbhd)
      (Subtype.val ⁻¹' range (UnderlyingSpace.map i)) (2 * Module.finrank ℂ D.F : ℕ) =
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of D.nbhd)
      (Subtype.val ⁻¹' range (UnderlyingSpace.map i)) (2 * d : ℕ) by rw [D.finrank_F])).hom
    h1).trans (relativeSingularCohomology.map_eqToHom_apply R _ _ (by rw [D.finrank_F]) e _ uQ)

/-- Restriction to `W ⊆ V` factors through the restriction to `V`. -/
lemma excisionRestrict_eq_map_inclusion {W : Set (UnderlyingSpace ℂ Y)}
    (D : RegularImbeddingOrientationDatum i d) (hWD : W ⊆ D.nbhd) (k : ℤ)
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) i)) k) :
    (excisionRestrict R (range (UnderlyingSpace.map (K := ℂ) i)) W k).hom u =
      (relativeSingularCohomology.map R (ModuleCat.of R R)
        (TopCat.ofHom (ContinuousMap.inclusion hWD))
        (A' := (Subtype.val ⁻¹' (range (UnderlyingSpace.map (K := ℂ) i)) : Set W)ᶜ)
        (A := (Subtype.val ⁻¹' (range (UnderlyingSpace.map (K := ℂ) i)) : Set D.nbhd)ᶜ)
        (fun _ h ↦ h) k).hom
        ((excisionRestrict R (range (UnderlyingSpace.map (K := ℂ) i)) D.nbhd k).hom u) := by
  have e : (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(W, UnderlyingSpace ℂ Y)) :
      TopCat.of W ⟶ TopCat.of (UnderlyingSpace ℂ Y)) =
      TopCat.ofHom (ContinuousMap.inclusion hWD) ≫
        TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(D.nbhd, UnderlyingSpace ℂ Y)) :=
    TopCat.ext fun _ ↦ rfl
  exact (relativeSingularCohomology.map_congr_apply R e _ (fun _ h ↦ h) k u).trans
    (relativeSingularCohomology.map_comp_apply' R (fun _ h ↦ h) (fun _ h ↦ h) _ k u)

/-- If `s ≫ g` is `σ̄|_W`, then the class `u` defined by `D`, restricted to `W ⊆ V`, is
`s^* g^* u_Q`. -/
lemma excisionRestrict_eq_map_map {W : Set (UnderlyingSpace ℂ Y)}
    (D : RegularImbeddingOrientationDatum i d) (hWD : W ⊆ D.nbhd) {E : TopCat.{0}} {A : Set E}
    (s : TopCat.of W ⟶ E)
    (hs : (Subtype.val ⁻¹' range (UnderlyingSpace.map (K := ℂ) i) : Set W)ᶜ ⊆ s ⁻¹' A)
    (g : E ⟶ TopCat.of (TotalSpace D.F D.Q))
    (hg : A ⊆ g ⁻¹' (range (Bundle.zeroSection D.F D.Q))ᶜ)
    (key : s ≫ g = TopCat.ofHom (ContinuousMap.inclusion hWD) ≫ D.sectionBarHom)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map i)) (2 * d : ℕ)}
    {uQ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D.F D.Q))
      (range (Bundle.zeroSection D.F D.Q)) (2 * Module.finrank ℂ D.F : ℕ)}
    (hu : (excisionRestrict R _ D.nbhd _).hom u = (D.thomPullback R).hom uQ)
    (hd : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D.F D.Q))
      (range (Bundle.zeroSection D.F D.Q)) (2 * Module.finrank ℂ D.F : ℕ) =
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D.F D.Q))
        (range (Bundle.zeroSection D.F D.Q)) (2 * d : ℕ)) :
    (excisionRestrict R (range (UnderlyingSpace.map (K := ℂ) i)) W _).hom u =
      (relativeSingularCohomology.map R (ModuleCat.of R R) s hs ((2 * d : ℕ) : ℤ)).hom
        ((relativeSingularCohomology.map R (ModuleCat.of R R) g hg ((2 * d : ℕ) : ℤ)).hom
          ((eqToHom hd).hom uQ)) := by
  have hι : (Subtype.val ⁻¹' (range (UnderlyingSpace.map (K := ℂ) i)) : Set W)ᶜ ⊆
      (TopCat.ofHom (ContinuousMap.inclusion hWD)) ⁻¹'
        (Subtype.val ⁻¹' (range (UnderlyingSpace.map (K := ℂ) i)) : Set D.nbhd)ᶜ :=
    fun _ h ↦ h
  have he : (Subtype.val ⁻¹' (range (UnderlyingSpace.map (K := ℂ) i)) : Set W)ᶜ ⊆
      (TopCat.ofHom (ContinuousMap.inclusion hWD) ≫ D.sectionBarHom) ⁻¹'
        (range (Bundle.zeroSection D.F D.Q))ᶜ := fun y hy ↦
    D.compl_subset_preimage_sectionBarHom (show ContinuousMap.inclusion hWD y ∈ _ from hy)
  refine (excisionRestrict_eq_map_inclusion R D hWD _ u).trans ?_
  rw [hu, thomPullback_apply R D uQ hd]
  exact (relativeSingularCohomology.map_comp_apply' R hι
    D.compl_subset_preimage_sectionBarHom he _ _).symm.trans
    ((relativeSingularCohomology.map_congr_apply R key.symm he (by rwa [key]) _ _).trans
      (relativeSingularCohomology.map_comp_apply' R hs hg _ _ _))

/-- **Comparison of two orientation data.** If on an open neighbourhood `W ⊆ V₁ ∩ V₂` of `X(ℂ)`
an isomorphism `φ : Q₁|_W ≅ Q₂|_W` of complex topological vector bundles carries `σ̄₁` to `σ̄₂`,
then the classes `u₁, u₂` defined by the data `D₁, D₂` agree. -/
theorem eq_of_continuous_equiv [IsClosedImmersion i]
    (D₁ D₂ : RegularImbeddingOrientationDatum i d)
    {W : Set (UnderlyingSpace ℂ Y)} (hW : IsOpen W) (hXW : range (UnderlyingSpace.map i) ⊆ W)
    (hW₁ : W ⊆ D₁.nbhd) (hW₂ : W ⊆ D₂.nbhd)
    (φ : ∀ y : W, D₁.Q ⟨y, hW₁ y.2⟩ ≃L[ℂ] D₂.Q ⟨y, hW₂ y.2⟩)
    (hφ : Continuous fun p : TotalSpace D₁.F (⇑(ContinuousMap.inclusion hW₁) *ᵖ D₁.Q) ↦
      (⟨⟨p.proj, hW₂ p.proj.2⟩, φ p.proj p.2⟩ : TotalSpace D₂.F D₂.Q))
    (hsec : ∀ (y : W) (v : D₁.Q ⟨y, hW₁ y.2⟩), D₁.sectionBar ⟨y, hW₁ y.2⟩ = ⟨⟨y, hW₁ y.2⟩, v⟩ →
      D₂.sectionBar ⟨y, hW₂ y.2⟩ = ⟨⟨y, hW₂ y.2⟩, φ y v⟩)
    {u₁ u₂ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map i)) (2 * d : ℕ)}
    {uQ₁ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D₁.F D₁.Q))
      (range (Bundle.zeroSection D₁.F D₁.Q)) (2 * Module.finrank ℂ D₁.F : ℕ)}
    {uQ₂ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D₂.F D₂.Q))
      (range (Bundle.zeroSection D₂.F D₂.Q)) (2 * Module.finrank ℂ D₂.F : ℕ)}
    (hQ₁ : MMP.IsThomClass D₁.F D₁.Q uQ₁) (hQ₂ : MMP.IsThomClass D₂.F D₂.Q uQ₂)
    (hu₁ : (excisionRestrict R _ D₁.nbhd _).hom u₁ = (D₁.thomPullback R).hom uQ₁)
    (hu₂ : (excisionRestrict R _ D₂.nbhd _).hom u₂ = (D₂.thomPullback R).hom uQ₂) :
    u₁ = u₂ := by
  set ι₁ := ContinuousMap.inclusion hW₁
  set ι₂ := ContinuousMap.inclusion hW₂
  let σ : W → TotalSpace D₁.F (⇑ι₁ *ᵖ D₁.Q) := fun y ↦
    ⟨y, cast (congrArg D₁.Q (D₁.proj_sectionBar (ι₁ y))) (D₁.sectionBar (ι₁ y)).2⟩
  have hσ₁ : ∀ y, Pullback.lift ι₁ (σ y) = D₁.sectionBar (ι₁ y) := fun y ↦
    TotalSpace.mk_cast_snd _ (D₁.proj_sectionBar (ι₁ y))
  have hσc : Continuous σ := by
    unfold Pullback.TotalSpace.topologicalSpace
    rw [pullbackTopology_def]
    refine continuous_inf_rng.2 ⟨continuous_induced_rng.2 ?_, continuous_induced_rng.2 ?_⟩
    · exact continuous_id
    change Continuous fun y ↦ Pullback.lift ι₁ (σ y)
    simp only [hσ₁]
    exact D₁.continuous_sectionBar.comp ι₁.continuous
  let σH : TopCat.of W ⟶ TopCat.of (TotalSpace D₁.F (⇑ι₁ *ᵖ D₁.Q)) := TopCat.ofHom ⟨σ, hσc⟩
  let Φ : TopCat.of (TotalSpace D₁.F (⇑ι₁ *ᵖ D₁.Q)) ⟶ TopCat.of (TotalSpace D₂.F D₂.Q) :=
    TopCat.ofHom ⟨_, hφ⟩
  let pbm := pullbackBundleMap D₁.F D₁.Q ι₁
  have key₁ : σH ≫ pbm = TopCat.ofHom ι₁ ≫ D₁.sectionBarHom := TopCat.ext hσ₁
  have key₂ : σH ≫ Φ = TopCat.ofHom ι₂ ≫ D₂.sectionBarHom :=
    TopCat.ext fun y ↦ (hsec y (σ y).2 (hσ₁ y).symm).symm
  have hpbm : ∀ x v, pbm ⟨x, v⟩ = ⟨ι₁ x, (ContinuousLinearEquiv.refl ℂ (D₁.Q (ι₁ x))) v⟩ :=
    fun _ _ ↦ rfl
  have hΦ : ∀ x v, Φ ⟨x, v⟩ = ⟨ι₂ x, φ x v⟩ := fun _ _ ↦ rfl
  have hs₁ : ((Subtype.val : W → _) ⁻¹' (range (UnderlyingSpace.map (K := ℂ) i)))ᶜ ⊆
      σH ⁻¹' (range (Bundle.zeroSection D₁.F (⇑ι₁ *ᵖ D₁.Q)))ᶜ := by
    rintro y hy ⟨b, hb⟩
    refine hy (D₁.sectionBar_preimage_subset (show ι₁ y ∈ D₁.sectionBar ⁻¹' _ from ⟨ι₁ b, ?_⟩))
    rw [← hσ₁ y]
    change Pullback.lift ι₁ (Bundle.zeroSection D₁.F (⇑ι₁ *ᵖ D₁.Q) b) = _
    rw [hb]
    rfl
  have hd₁ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D₁.F D₁.Q))
      (range (Bundle.zeroSection D₁.F D₁.Q)) (2 * Module.finrank ℂ D₁.F : ℕ) =
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D₁.F D₁.Q))
        (range (Bundle.zeroSection D₁.F D₁.Q)) (2 * d : ℕ) := by rw [D₁.finrank_F]
  have hd₂ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D₂.F D₂.Q))
      (range (Bundle.zeroSection D₂.F D₂.Q)) (2 * Module.finrank ℂ D₂.F : ℕ) =
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D₂.F D₂.Q))
        (range (Bundle.zeroSection D₂.F D₂.Q)) (2 * d : ℕ) := by rw [D₂.finrank_F]
  have e₃ := IsThomClassOfRank.eq D₁.finrank_F
    ((hQ₁.isThomClassOfRank D₁.finrank_F hd₁).map hpbm)
    ((hQ₂.isThomClassOfRank D₂.finrank_F hd₂).map hΦ)
  refine (cohomologyWithSupports.excisionIso R (Y := TopCat.of (UnderlyingSpace ℂ Y)) hW
    isClosed_range_map hXW ((2 * d : ℕ) : ℤ)).toLinearEquiv.injective ?_
  change (excisionRestrict R _ W _).hom u₁ = (excisionRestrict R _ W _).hom u₂
  rw [excisionRestrict_eq_map_map R D₁ hW₁ σH hs₁ pbm
      (compl_zeroSection_subset_preimage hpbm) key₁ hu₁ hd₁,
    excisionRestrict_eq_map_map R D₂ hW₂ σH hs₁ Φ
      (compl_zeroSection_subset_preimage hΦ) key₂ hu₂ hd₂, e₃]

end RegularImbeddingOrientationDatum

end MMP.Modules
