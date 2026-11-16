module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksBaseChangeChart
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksLineSectionZero
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksSectionComponentGeneric

/-!
# The pull-back of a section of a Stacks vector bundle

Let `f : X' ⟶ X` be a morphism of schemes, `ℰ` a quasi-coherent `𝒪_X`-module and
`σ : X ⟶ 𝐕(ℰ)` a section of `π : 𝐕(ℰ) ⟶ X`. Since `𝐕(f^*ℰ) = X' ×_X 𝐕(ℰ)`
(`Scheme.Modules.isPullback_vectorBundleBaseChangeMap`), `σ` pulls back to the section
`f^*σ = (𝟙, σ ∘ f) : X' ⟶ 𝐕(f^*ℰ)` (`MMP.Modules.pullbackSectionMap`). The zero section of
`𝐕(f^*ℰ)` is the base change of that of `𝐕(ℰ)`
(`MMP.Modules.isPullback_zeroSection_baseChangeMap`), so the zero scheme of `f^*σ` is the
pull-back `f⁻¹ Z(σ)` of the zero scheme of `σ` (`MMP.Modules.zeroLocus_pullbackSectionMap`).

## Main results

* `MMP.Modules.zeroSection_eq_vectorBundleOverZeroSection`: the zero section of `𝐕(ℰ)` is the
  point of `𝐕(ℰ)` with module morphism `0`.
* `MMP.Modules.isPullback_zeroSection_baseChangeMap`: the zero sections form a cartesian square.
* `MMP.Modules.zeroLocus_pullbackSectionMap`: `Z(f^*σ) = f⁻¹ Z(σ)`.
* `MMP.Modules.pullbackSectionMap_ne_zeroSection`: on a reduced `X`, `f^*σ ≠ 0` for `σ ≠ 0` and `f`
  surjective.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Appendix B.3.2, §19.1 (proof of Lemma 19.1.3).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace MMP.Modules

section HomExt

variable {X : Scheme.{0}}

/-- Two morphisms of `𝒪_X`-modules that agree on the sections over every affine open agree. -/
lemma hom_ext_of_affineOpens {M N : X.Modules} (φ ψ : M ⟶ N)
    (h : ∀ V : X.affineOpens, φ.app V.1 = ψ.app V.1) : φ = ψ := by
  refine Scheme.Modules.hom_ext φ ψ fun U ↦ ?_
  ext s
  let F : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  let ι := {V : X.affineOpens // V.1 ≤ U}
  refine TopCat.Sheaf.eq_of_locally_eq' F (fun V : ι ↦ V.1.1) U (fun V ↦ homOfLE V.2) ?_ _ _
    fun V ↦ ?_
  · intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hxV⟩
  · change (N.presheaf.map (homOfLE V.2).op) ((φ.app U) s) =
      (N.presheaf.map (homOfLE V.2).op) ((ψ.app U) s)
    have e₁ := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE V.2).op) s
    have e₂ := ConcreteCategory.congr_hom (ψ.mapPresheaf.naturality (homOfLE V.2).op) s
    simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at e₁ e₂
    rw [← e₁, ← e₂, h V.1]

end HomExt

variable {X : Scheme.{0}} (E : X.Modules) [E.IsQuasicoherent]

/-- **The zero section of `𝐕(ℰ)` is the point with module morphism `0`**: Stacks' zero section
`vectorBundleZeroSection` (from the augmentation of `Sym ℰ`) is `vectorBundleOverZeroSection`
(the point of `𝐕(ℰ)` over `𝟙 X` with module morphism `0`). -/
theorem zeroSection_eq_vectorBundleOverZeroSection :
    zeroSection E = (Scheme.Modules.vectorBundleOverZeroSection E).left := by
  let u : Over.mk (𝟙 X) ⟶ Scheme.Modules.vectorBundleOver X (F := E) :=
    Over.homMk (zeroSection E) (zeroSection_proj E)
  suffices hu : u = Scheme.Modules.vectorBundleOverZeroSection E from
    congrArg (fun h ↦ h.left) hu
  apply (Scheme.Modules.vectorBundleHomEquiv E _).injective
  rw [Scheme.Modules.vectorBundleHomEquiv_vectorBundleOverZeroSection]
  refine hom_ext_of_affineOpens _ _ fun V ↦ ?_
  ext m
  have hle : (Over.mk (𝟙 X)).hom ⁻¹ᵁ V.1 ≤ u.left ⁻¹ᵁ (proj E ⁻¹ᵁ V.1) :=
    (zeroSection_preimage_proj_preimage V.1).ge
  have h := appLE_totalSections_generator E u V m hle
  change ((Scheme.Modules.vectorBundleHomEquiv E _ u).val.app (op V.1)).hom m = 0
  rw [← h]
  have h2 := ConcreteCategory.congr_hom (totalSections_appLE_zeroSection E V)
    (generator E V.2 m)
  rw [ConcreteCategory.comp_apply] at h2
  exact h2.trans (symmetricAlgebraSheafAugmentation_app_generator E V.2 m)

variable {X' : Scheme.{0}} (f : X' ⟶ X) [((Scheme.Modules.pullback f).obj E).IsQuasicoherent]

/-- **The bundle map of a base change carries the zero section to the zero section.** -/
lemma zeroSection_comp_baseChangeMap :
    zeroSection ((Scheme.Modules.pullback f).obj E) ≫ baseChangeMap f E =
      f ≫ zeroSection E := by
  rw [zeroSection_eq_vectorBundleOverZeroSection, zeroSection_eq_vectorBundleOverZeroSection]
  exact Scheme.Modules.vectorBundleOverZeroSection_comp_vectorBundleBaseChangeMap f E

/-- **The zero section of `𝐕(f^*ℰ)` is the base change of the zero section of `𝐕(ℰ)`.** -/
theorem isPullback_zeroSection_baseChangeMap :
    IsPullback (zeroSection ((Scheme.Modules.pullback f).obj E)) f (baseChangeMap f E)
      (zeroSection E) := by
  refine IsPullback.of_right (h₁₂ := proj ((Scheme.Modules.pullback f).obj E)) (v₁₃ := f)
    (h₂₂ := proj E) ?_ (zeroSection_comp_baseChangeMap E f)
    (Scheme.Modules.isPullback_vectorBundleBaseChangeMap f E).flip
  rw [zeroSection_proj, zeroSection_proj]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- The ideal of the zero section of `𝐕(f^*ℰ)` is the pull-back of that of `𝐕(ℰ)`. -/
lemma ker_zeroSection_pullback :
    (zeroSection ((Scheme.Modules.pullback f).obj E)).ker =
      (zeroSection E).ker.comap (baseChangeMap f E) := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← (isPullback_zeroSection_baseChangeMap E f).isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

variable {E} {σ : X ⟶ totalSpace E} (hσ : σ ≫ proj E = 𝟙 X)

/-- **The pull-back `f^*σ : X' ⟶ 𝐕(f^*ℰ)` of a section `σ` of `𝐕(ℰ)`**: the point `(𝟙, σ ∘ f)` of
`𝐕(f^*ℰ) = X' ×_X 𝐕(ℰ)`. -/
def pullbackSectionMap : X' ⟶ totalSpace ((Scheme.Modules.pullback f).obj E) :=
  (Scheme.Modules.isPullback_vectorBundleBaseChangeMap f E).lift (f ≫ σ) (𝟙 X')
    (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])

/-- The composite of `f^*σ` with the bundle map `𝐕(f^*ℰ) ⟶ 𝐕(ℰ)` is `σ ∘ f`. -/
@[reassoc (attr := simp)]
lemma pullbackSectionMap_baseChangeMap :
    pullbackSectionMap f hσ ≫ baseChangeMap f E = f ≫ σ :=
  IsPullback.lift_fst _ _ _ _

/-- The pull-back `f^*σ` is a section of the projection `𝐕(f^*ℰ) ⟶ X'`. -/
@[reassoc (attr := simp)]
lemma pullbackSectionMap_proj :
    pullbackSectionMap f hσ ≫ proj ((Scheme.Modules.pullback f).obj E) = 𝟙 X' :=
  IsPullback.lift_snd _ _ _ _

/-- For `X'` over `Spec ℂ`, the pull-back `f^*σ` is a morphism over `Spec ℂ`. -/
instance isOver_pullbackSectionMap [X'.Over (Spec (.of ℂ))] :
    (pullbackSectionMap f hσ).IsOver (Spec (.of ℂ)) :=
  ⟨by
    change pullbackSectionMap f hσ ≫ proj ((Scheme.Modules.pullback f).obj E) ≫
      X' ↘ Spec (.of ℂ) = X' ↘ Spec (.of ℂ)
    rw [pullbackSectionMap_proj_assoc]⟩

/-- **The zero scheme of a pulled-back section is the pull-back of the zero scheme**:
`Z(f^*σ) = f⁻¹ Z(σ)`. -/
theorem zeroLocus_pullbackSectionMap :
    zeroLocus _ (pullbackSectionMap f hσ) = (zeroLocus E σ).comap f := by
  rw [zeroLocus, zeroLocus, ker_zeroSection_pullback, ← Scheme.IdealSheafData.comap_comp,
    pullbackSectionMap_baseChangeMap, Scheme.IdealSheafData.comap_comp]

/-- **A non-zero section pulls back to a non-zero section** along a surjective morphism, on a
reduced scheme. -/
theorem pullbackSectionMap_ne_zeroSection [IsReduced X] (h0 : σ ≠ zeroSection E)
    (hf : Function.Surjective f) :
    pullbackSectionMap f hσ ≠ zeroSection ((Scheme.Modules.pullback f).obj E) := by
  intro h
  have h1 := zeroLocus_pullbackSectionMap f hσ
  rw [h, zeroLocus_zeroSection] at h1
  apply h0
  refine eq_zeroSection_of_zeroLocus_eq_bot hσ
    (Scheme.IdealSheafData.eq_bot_of_support_eq_top' _ ?_)
  refine TopologicalSpace.Closeds.ext (Set.eq_univ_of_forall fun x ↦ ?_)
  obtain ⟨y, rfl⟩ := hf x
  have : y ∈ ((zeroLocus E σ).comap f).support := by
    rw [← h1, Scheme.IdealSheafData.support_bot]
    trivial
  rw [Scheme.IdealSheafData.support_comap] at this
  exact this

end MMP.Modules
