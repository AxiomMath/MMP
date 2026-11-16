module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksSection
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyPullback
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleZeroSectionConormal
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.RingTheory.AugmentationIdealSymmetricAlgebra

/-!
# Local equations of the zero scheme of a section of a Stacks vector bundle (Fulton, B.3.2)

Let `ℰ` be a quasi-coherent `𝒪_X`-module and `c = (V, b)` a chart of `𝐕(ℰ)`: an affine open `V`
of `X` with a basis `b₁, …, b_r` of `Γ(ℰ, V)`, whose elements are the coordinate functions
`bᵢ ∈ Γ(π⁻¹V, 𝒪)` (`MMP.Modules.chartCoordSection`). The zero section is cut out on `π⁻¹V` by
`b₁, …, b_r` (`MMP.Modules.ideal_ker_zeroSection`), so the zero scheme `Z(σ) = σ⁻¹(0(X))` of a
morphism `σ : X ⟶ 𝐕(ℰ)` is cut out on an affine `W ⊆ σ⁻¹(π⁻¹V)` by `σ^♯b₁, …, σ^♯b_r`
(`MMP.Modules.ideal_zeroLocus`), the local coordinates of `σ`, whose values at a complex point
`p` are the chart coordinates of `σ(p)` (`MMP.Modules.eval_sectionCoord`).

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Appendix B.3.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Opposite

namespace MMP.Modules

variable {X : Scheme.{0}} {E : X.Modules} [E.IsQuasicoherent] {r : ℕ}

/-- The zero section `0 : X ⟶ 𝐕(ℰ)` pulls back `π⁻¹(V)` to `V`. -/
lemma zeroSection_preimage_proj_preimage (V : X.Opens) :
    zeroSection E ⁻¹ᵁ (proj E ⁻¹ᵁ V) = V :=
  Stacks.VectorBundleConormal.preimage_chartOpen E V

variable (E) in
/-- The part `π⁻¹(V)` of `𝐕(ℰ)` over an affine open `V` is affine. -/
lemma isAffineOpen_proj_preimage (V : X.affineOpens) : IsAffineOpen (proj E ⁻¹ᵁ V.1) :=
  IsAffine.of_isIso (specIso E V).hom

variable (E) in
/-- **The zero section on the sections over `π⁻¹(V)` is the augmentation of `Sym(ℰ)`.** -/
lemma totalSections_appLE_zeroSection (V : X.affineOpens) :
    totalSections E V ≫ (zeroSection E).appLE (proj E ⁻¹ᵁ V.1) V.1
        (zeroSection_preimage_proj_preimage V.1).ge =
      (Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app (op V.1) := by
  have e := (zeroSection_preimage_proj_preimage (E := E) V.1).ge
  have h1 : (zeroSection E).resLE (proj E ⁻¹ᵁ V.1) V.1 e ≫ (specIso E V).hom =
      V.1.toSpecΓ ≫
        Spec.map ((Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app (op V.1)) := by
    rw [← cancel_mono (specSectionsι E V), Category.assoc, specIso_hom_specSectionsι,
      Scheme.Hom.resLE_comp_ι, Category.assoc]
    exact Scheme.Modules.ι_vectorBundleZeroSection X E V
  have h2 := congrArg Scheme.Hom.appTop h1
  simp only [Scheme.Hom.comp_appTop] at h2
  have h3 : (zeroSection E).appLE (proj E ⁻¹ᵁ V.1) V.1 e =
      (proj E ⁻¹ᵁ V.1).topIso.inv ≫ ((zeroSection E).resLE (proj E ⁻¹ᵁ V.1) V.1 e).appTop ≫
        V.1.topIso.hom := by
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h3, totalSections]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% h2, Scheme.Opens.toSpecΓ_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp, eqToHom_trans,
    eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id, Iso.inv_hom_id]

variable (E) in
/-- **The zero section of `𝐕(ℰ)` is cut out on `π⁻¹(V)` by the degree-one sections.** -/
lemma ideal_ker_zeroSection_eq_span_generator (V : X.affineOpens) :
    (zeroSection E).ker.ideal ⟨proj E ⁻¹ᵁ V.1, isAffineOpen_proj_preimage E V⟩ =
      Ideal.span (range fun m : Γ(E, V.1) ↦ totalSections E V (generator E V.2 m)) := by
  set e := (zeroSection_preimage_proj_preimage (E := E) V.1).ge
  rw [Scheme.Hom.ker_apply]
  have hker : RingHom.ker ((zeroSection E).app (proj E ⁻¹ᵁ V.1)).hom =
      RingHom.ker ((zeroSection E).appLE (proj E ⁻¹ᵁ V.1) V.1 e).hom := by
    rw [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.ker_comp_of_injective]
    rw [Subsingleton.elim (homOfLE e)
      (eqToHom (zeroSection_preimage_proj_preimage (E := E) V.1).symm)]
    exact (ConcreteCategory.bijective_of_isIso _).1
  have : IsIso (totalSections E V) := by
    have : IsIso ((specIso E V).hom.appTop) := inferInstanceAs (IsIso ((specIso E V).hom.app ⊤))
    unfold totalSections
    infer_instance
  set eq := Stacks.SymAlgSections.symSectionsRingEquiv E V.2
  have hc : (RingHom.ker ((zeroSection E).appLE (proj E ⁻¹ᵁ V.1) V.1 e).hom).comap
      (totalSections E V).hom =
      RingHom.ker ((Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app (op V.1)).hom := by
    rw [RingHom.comap_ker, ← CommRingCat.hom_comp, totalSections_appLE_zeroSection]
  have haug : RingHom.ker
      ((Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app (op V.1)).hom =
      (SymmetricAlgebra.augmentationIdeal Γ(X, V.1) Γ(E, V.1)).map eq.toRingHom := by
    rw [← Stacks.SymAlgSections.comap_ker_symmetricAlgebraSheafAugmentation_app E V.2]
    exact (Ideal.map_comap_of_surjective eq.toRingHom eq.surjective _).symm
  calc RingHom.ker ((zeroSection E).app (proj E ⁻¹ᵁ V.1)).hom
      = ((RingHom.ker ((zeroSection E).appLE (proj E ⁻¹ᵁ V.1) V.1 e).hom).comap
          (totalSections E V).hom).map (totalSections E V).hom := by
        rw [hker, Ideal.map_comap_of_surjective _
          (ConcreteCategory.bijective_of_isIso (totalSections E V)).2]
    _ = Ideal.span (range fun m : Γ(E, V.1) ↦ totalSections E V (generator E V.2 m)) := by
        rw [hc, haug, ← SymmetricAlgebra.span_range_ι_eq_augmentationIdeal, Ideal.map_span,
          Ideal.map_span, ← range_comp, ← range_comp]
        rfl

variable (E) in
/-- **The zero section of `𝐕(ℰ)` is cut out on `π⁻¹(V)` by the coordinates `b₁, …, b_r` of a
chart `c = (V, b)`.** -/
theorem ideal_ker_zeroSection (c : Chart E r) :
    (zeroSection E).ker.ideal ⟨proj E ⁻¹ᵁ c.1.1, isAffineOpen_proj_preimage E c.1⟩ =
      Ideal.span (range (chartCoordSection c)) := by
  rw [ideal_ker_zeroSection_eq_span_generator]
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono ?_)
  · rintro _ ⟨m, rfl⟩
    dsimp only
    rw [← c.2.sum_repr m, map_sum, map_sum]
    refine Ideal.sum_mem _ fun i _ ↦ ?_
    erw [generator_smul, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    exact ⟨c.2 i, rfl⟩

/-- The `i`-th local coordinate `σ^♯bᵢ` of `σ : X ⟶ 𝐕(ℰ)` in a chart `c = (V, b)`, on an open
`W ⊆ σ⁻¹(π⁻¹V)`. -/
def sectionCoord (σ : X ⟶ totalSpace E) (c : Chart E r) {W : X.Opens}
    (hW : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)) (i : Fin r) : Γ(X, W) :=
  σ.appLE (proj E ⁻¹ᵁ c.1.1) W hW (chartCoordSection c i)

/-- **The zero scheme of `σ : X ⟶ 𝐕(ℰ)` is cut out by the local coordinates of `σ`**: on an
affine open `W ⊆ σ⁻¹(π⁻¹V)` its ideal is generated by `σ^♯b₁, …, σ^♯b_r`. -/
theorem ideal_zeroLocus (σ : X ⟶ totalSpace E) (c : Chart E r) (W : X.affineOpens)
    (hW : W.1 ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)) :
    (zeroLocus E σ).ideal W = Ideal.span (range (sectionCoord σ c hW)) := by
  rw [zeroLocus, Stacks.IdealSheaf.ideal_comap_appLE _ σ
    ⟨proj E ⁻¹ᵁ c.1.1, isAffineOpen_proj_preimage E c.1⟩ W hW, ideal_ker_zeroSection,
    Ideal.map_span, ← range_comp]
  rfl

open UnderlyingSpace in
/-- The values of the local coordinates of `σ` at a complex point `p` are the chart coordinates
of `σ(p)`. -/
lemma eval_sectionCoord [X.Over (Spec (.of ℂ))] (σ : X ⟶ totalSpace E)
    [σ.IsOver (Spec (.of ℂ))] (c : Chart E r) {W : X.Opens}
    (hW : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)) (p : UnderlyingSpace ℂ X) (hp : ⊤ ≤ p.toHom ⁻¹ᵁ W)
    (i : Fin r) :
    eval p hp (sectionCoord σ c hW i) = coord c (mapFun σ p) i := by
  rw [sectionCoord, eval_appLE, coord_apply]

end MMP.Modules
