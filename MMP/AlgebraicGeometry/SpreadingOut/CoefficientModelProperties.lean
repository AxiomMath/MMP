module

public import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
public import MMP.AlgebraicGeometry.SpreadingOut.CoefficientModelStages
public import MMP.RingTheory.Kaehler.PluriformProduct

/-!
# Properties of a coefficient model at late stages

Let `k₀ ⊆ K` be algebraically closed fields of characteristic zero and let `M` be a model of a
finite diagram `X` of integral projective `K`-schemes. This file proves that the properties of
`X` that the spreading-out theorem transfers already hold at all late stages of `M`: projectivity
and flatness, smoothness, the properties of the morphisms, relative ampleness, isomorphisms of
the specified sheaves, and isomorphisms with the sheaves of top differential forms. It then
develops the local tools for orders of vanishing on late fibres: sections that descend to a
stage, local data at a point with discrete valuation ring stalk, the orders of a section along
the prime divisors of a fibre, and nonzero rational top forms built from étale coordinates.

## Main definitions

* `MMP.Spreading.EvAbove`: a property of the stages above a given stage that holds at all
  stages from some stage on.

## Main results

* `MMP.Spreading.eventually_projective_flat`, `MMP.Spreading.eventually_smooth`,
  `MMP.Spreading.eventually_morphisms`, `MMP.Spreading.eventually_ample`,
  `MMP.Spreading.eventually_sheafIso`, `MMP.Spreading.eventually_differentials`: the properties
  of the model over `Spec R`.
* `MMP.Spreading.Model.exists_ord_section`: orders along the prime divisors of a late fibre are
  orders along prime divisors of the generic fibre.
* `MMP.Spreading.exists_etale_chart_of_smooth_on`: étale coordinates on a smooth stage.

## References

* [EGA IV, 8.10, 9.7, 12.2]
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace MMP.Spreading

noncomputable section

/-! ### The properties of the model -/

section Properties

variable {k₀ K : Type u} [Field k₀] [Field K] [IsAlgClosed k₀] [IsAlgClosed K] [CharZero k₀]
  [Algebra k₀ K] {J : Type u} [SmallCategory J] [FinCategory J] {X : J ⥤ Over (Spec (.of K))}
  (hint : ∀ j, IsIntegral (X.obj j).left)
  {ι : Type u} [Finite ι] {v : ι → J} {𝓛 : ∀ i, (X.obj (v i)).left.Modules}
  [h𝓛 : ∀ i, Stacks.Ample.IsInvertibleModule _ (𝓛 i)]

variable (M : Model k₀ X v 𝓛)

/-- **Projectivity and flatness.** -/
public lemma eventually_projective_flat : M.Eventually fun S h =>
    (∀ j, IsProjective ((M.stage h).obj j).hom ∧ Flat ((M.stage h).obj j).hom) ∧
    (∀ {j j'} (g : j ⟶ j'), IsProjective ((M.stage h).map g).left) := by
  have : Fintype J := FinCategory.fintypeObj
  have : MorphismProperty.RespectsIso @Flat :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hP : ∀ (S : CoefficientModels.FGSub k₀ K) (h : M.R ≤ S) (j : J),
      IsProjectiveMorphism ((M.stage h).obj j).hom := fun S h j =>
    IsProjectiveMorphism.baseChange (M.hproj j) _
  have hflat : M.Eventually fun S h => ∀ j, Flat ((M.stage h).obj j).hom := by
    refine Model.Eventually.forall fun j => ?_
    have hK := (M.prop_obj_iff @Flat j).mp inferInstance
    have := M.compactSpace j
    have := M.quasiSeparatedSpace j
    have := M.locallyOfFinitePresentation_toTerminal j
    have : CompactSpace (Over.mk (𝟙 (Spec (.of M.R.1)))).left :=
      inferInstanceAs (CompactSpace (Spec _))
    have : QuasiSeparatedSpace (Over.mk (𝟙 (Spec (.of M.R.1)))).left :=
      inferInstanceAs (QuasiSeparatedSpace (Spec _))
    exact (M.eventually_of_exists @Flat (toTerminal (M.Y.obj j))
      (M.exists_flat (toTerminal (M.Y.obj j)) hK)).mono fun S h hS =>
        (prop_overPullback_toTerminal_iff @Flat _ _).mp hS
  refine hflat.mono fun S h hS => ⟨fun j => ⟨?_, hS j⟩, fun {j j'} g => ?_⟩
  · exact (isProjective_iff_isProjectiveMorphism_of_isAffine _).mpr (hP S h j)
  · have := (isProper_of_isProjectiveMorphism _ (hP S h j')).toIsSeparated
    refine IsProjective.of_comp _ ((M.stage h).obj j').hom ?_
    rw [Over.w]
    exact (isProjective_iff_isProjectiveMorphism_of_isAffine _).mpr (hP S h j)

include hint in
/-- **Birationality spreads to the fibres**: a birational morphism of the diagram over `K` is
birational on every field-valued fibre of every late stage (with irreducible vertices). -/
public lemma Model.eventually_birational {j j' : J} (g : j ⟶ j')
    (hg : Mori.IsBirationalMorphism (X.map g).left) :
    M.Eventually fun S h => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      IrreducibleSpace ((M.stage h ⋙ Over.pullback t).obj j).left →
      IrreducibleSpace ((M.stage h ⋙ Over.pullback t).obj j').left →
      Mori.IsBirationalMorphism ((M.stage h ⋙ Over.pullback t).map g).left := by
  have := hint j
  obtain ⟨W, hWne, hWo⟩ := hg.exists_isOpenImmersion
  have hlft := M.locallyOfFiniteType_obj j
  have : QuasiCompact (X.obj j).hom :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (M.cart.isPullback j) (M.fp j).2.1
  have : IsLocallyNoetherian (X.obj j).left := LocallyOfFiniteType.isLocallyNoetherian (X.obj j).hom
  have : CompactSpace (X.obj j).left := QuasiCompact.compactSpace_of_compactSpace (X.obj j).hom
  have : IsNoetherian (X.obj j).left := ⟨⟩
  have hWc : IsCompact (W : Set (X.obj j).left) := TopologicalSpace.NoetherianSpace.isCompact _
  obtain ⟨S₀', h₀', HV⟩ := M.exists_open j W hWc
  obtain ⟨Sf, hf, Hf⟩ := eventually_projective_flat M
  let S₀ : CoefficientModels.FGSub k₀ K := ⟨S₀'.1 ⊔ Sf.1, S₀'.2.sup Sf.2⟩
  have hS₀' : S₀' ≤ S₀ := le_sup_left (a := S₀'.1)
  have hSf : Sf ≤ S₀ := le_sup_right (b := Sf.1)
  have h₀ : M.R ≤ S₀ := h₀'.trans hS₀'
  obtain ⟨V, hVc, hVW⟩ := HV S₀ hS₀'
  have hflat : Flat ((M.stage h₀).obj j).hom := ((Hf S₀ hSf).1 j).2
  have : LocallyOfFinitePresentation ((M.stage h₀).obj j).hom := (M.finitePresentation_stage h₀ j).1
  -- the morphism at the stage `S₀`
  let A : Over (Spec (.of S₀.1)) := Over.mk (V.ι ≫ ((M.stage h₀).obj j).hom)
  let φ : A ⟶ (M.stage h₀).obj j' := Over.homMk (V.ι ≫ ((M.stage h₀).map g).left)
    (by simp only [A, Over.mk_hom, Category.assoc, Over.w])
  have hK : IsOpenImmersion ((Over.pullback (κ S₀.1)).map φ).left := by
    have hr := (M.isCartesian_cmp h₀).isPullback_restrict g V
    have hψ : IsOpenImmersion ((M.cmp h₀ j ⁻¹ᵁ V).ι ≫ (X.map g).left) := by
      rwa [hVW]
    obtain ⟨a, ha⟩ := isPullback_of_isPullback_comp hr (overPullback_isPullback (κ S₀.1) A _ φ)
      ((M.isCartesian_cmp h₀).isPullback j').isoPullback.inv (IsPullback.isoPullback_inv_fst _)
    exact MorphismProperty.of_isPullback ha hψ
  have : CompactSpace A.left := isCompact_iff_compactSpace.mp hVc
  have := M.quasiSeparatedSpace_stage h₀ j
  have : QuasiSeparatedSpace A.left :=
    (isQuasiSeparated_iff_quasiSeparatedSpace (V : Set ((M.stage h₀).obj j).left) V.isOpen).mp
      (IsQuasiSeparated.of_quasiSeparatedSpace _)
  have := M.compactSpace_stage h₀ j'
  have := M.quasiSeparatedSpace_stage h₀ j'
  have := M.locallyOfFinitePresentation_stage_map h₀ g
  have : LocallyOfFinitePresentation φ.left :=
    show LocallyOfFinitePresentation (V.ι ≫ ((M.stage h₀).map g).left) from inferInstance
  obtain ⟨S₁, h₁, H₁⟩ := exists_stage_isOpenImmersion S₀ φ hK
  have hne : (M.cmp h₀ j ⁻¹ᵁ V : Set (X.obj j).left).Nonempty := by rwa [hVW]
  obtain ⟨S₂, h₂, H₂⟩ := M.exists_nonempty_fibre j h₀ V hne
  refine ⟨⟨S₁.1 ⊔ S₂.1, S₁.2.sup S₂.2⟩, h₀.trans (h₁.trans (le_sup_left (a := S₁.1))),
    fun S hS L _ t hi hi' => ?_⟩
  have hS₁ : S₁ ≤ S := (le_sup_left (a := S₁.1)).trans hS
  have hS₂ : S₂ ≤ S := (le_sup_right (b := S₂.1)).trans hS
  have hS₀ : S₀ ≤ S := h₁.trans hS₁
  have hst := (M.isCartesian_stageCmp h₀ hS₀).isPullback_restrict g V
  have hψS : IsOpenImmersion ((M.stageCmp h₀ hS₀ j ⁻¹ᵁ V).ι ≫
      ((M.stage (h₀.trans hS₀)).map g).left) := by
    obtain ⟨a, ha⟩ := isPullback_of_isPullback_comp
      (overPullback_isPullback (π (show S₀.1 ≤ S.1 from hS₀)) A _ φ) hst
      ((M.isCartesian_stageCmp h₀ hS₀).isPullback j').isoPullback.hom
      (IsPullback.isoPullback_hom_fst _)
    exact MorphismProperty.of_isPullback ha (H₁ S hS₁)
  have hft := (isCartesian_pullback t (M.stage (h₀.trans hS₀))).isPullback_restrict g
    (M.stageCmp h₀ hS₀ j ⁻¹ᵁ V)
  have hψt := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hft hψS
  exact isBirationalMorphism_of_isOpenImmersion_ι_comp' _ _ (H₂ S hS₂ L t)

/-- **Smoothness of the vertices.** -/
public lemma eventually_smooth : M.Eventually fun S h =>
    ∀ j, Smooth (X.obj j).hom → Smooth ((M.stage h).obj j).hom := by
  have : Fintype J := FinCategory.fintypeObj
  have : MorphismProperty.RespectsIso @Smooth :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine Model.Eventually.forall fun j => ?_
  by_cases hj : Smooth (X.obj j).hom
  · have hK := (M.prop_obj_iff @Smooth j).mp hj
    have := M.compactSpace j
    have := M.quasiSeparatedSpace j
    have := M.locallyOfFinitePresentation_toTerminal j
    have : CompactSpace (Over.mk (𝟙 (Spec (.of M.R.1)))).left :=
      inferInstanceAs (CompactSpace (Spec _))
    have : QuasiSeparatedSpace (Over.mk (𝟙 (Spec (.of M.R.1)))).left :=
      inferInstanceAs (QuasiSeparatedSpace (Spec _))
    have H := M.exists_smooth (toTerminal (M.Y.obj j)) hK
    refine (M.eventually_of_exists @Smooth (toTerminal (M.Y.obj j))
      H).mono fun S h hS _ => ?_
    exact (prop_overPullback_toTerminal_iff @Smooth _ _).mp hS
  · exact M.eventually_true.mono fun _ _ _ hj' => absurd hj' hj

/-- **Properties of the morphisms.** -/
public lemma eventually_morphisms : M.Eventually fun S h =>
    ∀ {j j'} (g : j ⟶ j'),
      (Flat (X.map g).left → Flat ((M.stage h).map g).left) ∧
      (Surjective (X.map g).left → Surjective ((M.stage h).map g).left) ∧
      (IsIso (X.map g).left → IsIso ((M.stage h).map g).left) ∧
      (IsClosedImmersion (X.map g).left → IsClosedImmersion ((M.stage h).map g).left) ∧
      (Smooth (X.map g).left → Smooth ((M.stage h).map g).left) := by
  have : Fintype J := FinCategory.fintypeObj
  have H : M.Eventually fun S h => ∀ a : Σ j j' : J, j ⟶ j',
      (Flat (X.map a.2.2).left → Flat ((M.stage h).map a.2.2).left) ∧
      (Surjective (X.map a.2.2).left → Surjective ((M.stage h).map a.2.2).left) ∧
      (IsIso (X.map a.2.2).left → IsIso ((M.stage h).map a.2.2).left) ∧
      (IsClosedImmersion (X.map a.2.2).left → IsClosedImmersion ((M.stage h).map a.2.2).left) ∧
      (Smooth (X.map a.2.2).left → Smooth ((M.stage h).map a.2.2).left) := by
    refine Model.Eventually.forall fun ⟨j, j', g⟩ => ?_
    have := M.compactSpace j
    have := M.quasiSeparatedSpace j
    have := M.compactSpace j'
    have := M.quasiSeparatedSpace j'
    have := M.locallyOfFinitePresentation_map g
    exact (((M.eventually_map @Flat g (M.exists_flat _)).and
      (M.eventually_map @Surjective g (M.exists_surjective _))).and
      ((M.eventually_map (MorphismProperty.isomorphisms _) g (M.exists_isIso _)).and
      ((M.eventually_map @IsClosedImmersion g (M.exists_isClosedImmersion _)).and
      (M.eventually_map @Smooth g (M.exists_smooth _))))).mono
      fun _ _ ⟨⟨h₁, h₂⟩, h₃, h₄, h₅⟩ => ⟨h₁, h₂, h₃, h₄, h₅⟩
  exact H.mono fun _ _ h j j' g => h ⟨j, j', g⟩

/-- **Relative ampleness.** -/
public lemma eventually_ample : M.Eventually fun S h =>
    (∀ i, Mori.IsRelativelyAmple (X.obj (v i)).hom (𝓛 i) →
      @Mori.IsRelativelyAmple _ _ ((M.stage h).obj (v i)).hom (M.stageN h i)
        (M.stageN_invertible h i)) ∧
    (∀ i {j'} (g : v i ⟶ j'), Mori.IsRelativelyAmple (X.map g).left (𝓛 i) →
      @Mori.IsRelativelyAmple _ _ ((M.stage h).map g).left (M.stageN h i)
        (M.stageN_invertible h i)) := by
  have : Fintype J := FinCategory.fintypeObj
  have := M.invertible
  have hqcX : ∀ j, QuasiCompact (X.obj j).hom := fun j =>
    MorphismProperty.of_isPullback (P := @QuasiCompact) (M.cart.isPullback j) (M.fp j).2.1
  have hqsX : ∀ j, QuasiSeparated (X.obj j).hom := fun j =>
    MorphismProperty.of_isPullback (P := @QuasiSeparated) (M.cart.isPullback j) (M.fp j).2.2
  have hA : M.Eventually fun S h => ∀ i, Mori.IsRelativelyAmple (X.obj (v i)).hom (𝓛 i) →
      @Mori.IsRelativelyAmple _ _ ((M.stage h).obj (v i)).hom (M.stageN h i)
        (M.stageN_invertible h i) := by
    refine Model.Eventually.forall fun i => ?_
    by_cases hi : Mori.IsRelativelyAmple (X.obj (v i)).hom (𝓛 i)
    · have := (M.fp (v i)).2.1
      have := hqcX (v i)
      exact (M.eventually_isRelativelyAmple (v i) (M.N i) (M.Y.obj (v i)).hom (κ M.R.1)
        (X.obj (v i)).hom (M.cart.isPullback (v i)).w (𝓛 i) (M.θ i) (fun S _ => Spec (.of S.1))
        (fun S h => π (show M.R.1 ≤ S.1 from h)) (fun _ _ => inferInstance)
        (fun S h => pullback.snd _ _) (fun S h => pullback.condition.symm) hi).mono
        fun _ _ H _ => H
    · exact M.eventually_true.mono fun _ _ _ h => absurd h hi
  have hB : M.Eventually fun S h => ∀ a : Σ i : ι, Σ j' : J, v i ⟶ j',
      Mori.IsRelativelyAmple (X.map a.2.2).left (𝓛 a.1) →
      @Mori.IsRelativelyAmple _ _ ((M.stage h).map a.2.2).left (M.stageN h a.1)
        (M.stageN_invertible h a.1) := by
    refine Model.Eventually.forall fun ⟨i, j', g⟩ => ?_
    by_cases hi : Mori.IsRelativelyAmple (X.map g).left (𝓛 i)
    · have := M.compactSpace j'
      have := (M.fp (v i)).2.1
      have := (M.fp j').2.2
      have := hqcX (v i)
      have := hqsX j'
      have : QuasiCompact ((M.Y.map g).left ≫ (M.Y.obj j').hom) := by rw [Over.w]; infer_instance
      have := QuasiCompact.of_comp (M.Y.map g).left (M.Y.obj j').hom
      have : QuasiCompact ((X.map g).left ≫ (X.obj j').hom) := by rw [Over.w]; infer_instance
      have := QuasiCompact.of_comp (X.map g).left (X.obj j').hom
      have : IsAffineHom (M.p j') :=
        MorphismProperty.of_isPullback (P := @IsAffineHom) (M.cart.isPullback j').flip
          inferInstance
      exact (M.eventually_isRelativelyAmple (v i) (M.N i) (M.Y.map g).left (M.p j')
        (X.map g).left (M.cart.w g).symm (𝓛 i) (M.θ i)
        (fun S h => ((M.stage h).obj j').left)
        (fun S h => pullback.fst (M.Y.obj j').hom (π (show M.R.1 ≤ S.1 from h)))
        (fun S h => MorphismProperty.of_isPullback (P := @IsAffineHom)
          (IsPullback.of_hasPullback _ _).flip inferInstance)
        (fun S h => ((M.stage h).map g).left) (fun S h => overPullback_map_left_fst _ _)
        hi).mono fun _ _ H _ => H
    · exact M.eventually_true.mono fun _ _ _ h => absurd h hi
  exact (hA.and hB).mono fun _ _ ⟨h₁, h₂⟩ => ⟨h₁, fun i j' g => h₂ ⟨i, j', g⟩⟩

open Stacks.AlgebraicGeometry.ModuleLimits in
/-- **Isomorphisms between the sheaves.** -/
public lemma eventually_sheafIso : M.Eventually fun S h =>
    ∀ i i' (g : v i ⟶ v i'),
      Nonempty (𝓛 i ≅ (Scheme.Modules.pullback (X.map g).left).obj (𝓛 i')) →
      Nonempty (M.stageN h i ≅
        (Scheme.Modules.pullback ((M.stage h).map g).left).obj (M.stageN h i')) := by
  have : Fintype J := FinCategory.fintypeObj
  have H : M.Eventually fun S h => ∀ a : Σ i i' : ι, v i ⟶ v i',
      Nonempty (𝓛 a.1 ≅ (Scheme.Modules.pullback (X.map a.2.2).left).obj (𝓛 a.2.1)) →
      Nonempty (M.stageN h a.1 ≅
        (Scheme.Modules.pullback ((M.stage h).map a.2.2).left).obj (M.stageN h a.2.1)) := by
    refine Model.Eventually.forall fun ⟨i, i', g⟩ => ?_
    by_cases hg : Nonempty (𝓛 i ≅ (Scheme.Modules.pullback (X.map g).left).obj (𝓛 i'))
    · obtain ⟨θ₀⟩ := hg
      have := M.isFinitePresentation_N i
      have := M.isFinitePresentation_N i'
      have := isFinitePresentation_pullback (M.Y.map g).left (M.N i')
      refine (M.eventually_iso (v i) (M.N i)
        ((Scheme.Modules.pullback (M.Y.map g).left).obj (M.N i'))
        (M.θ i ≪≫ θ₀ ≪≫ (Scheme.Modules.pullback (X.map g).left).mapIso (M.θ i').symm ≪≫
          canIso _ _ _ (M.cart.w g) _ ≪≫ (canIso _ _ _ rfl _).symm)).mono
        fun S h ⟨ψ⟩ _ => ⟨ψ ≪≫ canIso _ _ _ (overPullback_map_left_fst _ _).symm _ ≪≫
          (canIso _ _ _ rfl _).symm⟩
    · exact M.eventually_true.mono fun _ _ _ h => absurd h hg
  exact H.mono fun _ _ h i i' g => h ⟨i, i', g⟩

include hint in
/-- **Top differential forms.** -/
public lemma eventually_differentials : M.Eventually fun S h =>
    ∀ i (n : ℕ),
      Nonempty (𝓛 i ≅ Scheme.Hom.relativeDifferentialForms (X.obj (v i)).hom n) →
      Nonempty (M.stageN h i ≅
        Scheme.Hom.relativeDifferentialForms ((M.stage h).obj (v i)).hom n) := by
  have : Fintype J := FinCategory.fintypeObj
  have hlft : ∀ j, LocallyOfFiniteType (X.obj j).hom := M.locallyOfFiniteType_obj
  let B : ι → ℕ := fun i => haveI := hint (v i)
    Module.finrank ((X.obj (v i)).left.presheaf.stalk (genericPoint (X.obj (v i)).left))
      ((Scheme.Hom.relativeDifferentials (X.obj (v i)).hom).presheaf.stalk
        (genericPoint (X.obj (v i)).left))
  have H : M.Eventually fun S h => ∀ a : Σ i : ι, Fin (B i + 1),
      Nonempty (𝓛 a.1 ≅ Scheme.Hom.relativeDifferentialForms (X.obj (v a.1)).hom (a.2 : ℕ)) →
      Nonempty (M.stageN h a.1 ≅
        Scheme.Hom.relativeDifferentialForms ((M.stage h).obj (v a.1)).hom (a.2 : ℕ)) := by
    refine Model.Eventually.forall fun ⟨i, n⟩ => ?_
    by_cases hn : Nonempty (𝓛 i ≅ Scheme.Hom.relativeDifferentialForms (X.obj (v i)).hom (n : ℕ))
    · obtain ⟨e⟩ := hn
      have := M.isFinitePresentation_N i
      have := M.isLocallyNoetherian (v i)
      have := (M.fp (v i)).1
      have := CoefficientModels.isNoetherianRing_of_fg k₀ K M.R
      have : (Scheme.Hom.relativeDifferentials (M.Y.obj (v i)).hom).IsCoherent :=
        Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _
      have : (Scheme.Hom.relativeDifferentialForms (M.Y.obj (v i)).hom (n : ℕ)).IsCoherent :=
        Scheme.Modules.isCoherent_exteriorPower
          (Scheme.Hom.relativeDifferentials (M.Y.obj (v i)).hom) (n : ℕ)
      have := isFinitePresentation_of_isCoherent
        (Scheme.Hom.relativeDifferentialForms (M.Y.obj (v i)).hom (n : ℕ))
      have hK := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_isPullback (M.p (v i))
        (M.Y.obj (v i)).hom (X.obj (v i)).hom (κ M.R.1) (M.cart.isPullback (v i)) (n : ℕ)
      refine (M.eventually_iso (v i) (M.N i)
        (Scheme.Hom.relativeDifferentialForms (M.Y.obj (v i)).hom (n : ℕ))
        (M.θ i ≪≫ e ≪≫ (asIso (Scheme.Hom.relativeDifferentialFormsMap (M.p (v i))
          (M.Y.obj (v i)).hom (X.obj (v i)).hom (κ M.R.1) (M.cart.isPullback (v i)).w
          (n : ℕ))).symm)).mono fun S h ⟨ψ⟩ _ => ?_
      have hS := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_isPullback
        (pullback.fst (M.Y.obj (v i)).hom (π (show M.R.1 ≤ S.1 from h)))
        (M.Y.obj (v i)).hom (pullback.snd _ _) (π (show M.R.1 ≤ S.1 from h))
        (IsPullback.of_hasPullback _ _) (n : ℕ)
      exact ⟨ψ ≪≫ asIso (Scheme.Hom.relativeDifferentialFormsMap
        (pullback.fst (M.Y.obj (v i)).hom (π (show M.R.1 ≤ S.1 from h)))
        (M.Y.obj (v i)).hom (pullback.snd _ _) (π (show M.R.1 ≤ S.1 from h))
        (IsPullback.of_hasPullback _ _).w (n : ℕ))⟩
    · exact M.eventually_true.mono fun _ _ _ h => absurd h hn
  refine H.mono fun S h H i n hn => ?_
  have := hint (v i)
  obtain ⟨e⟩ := hn
  have hle : n ≤ B i :=
    le_finrank_of_iso_relativeDifferentialForms (X.obj (v i)).hom (𝓛 i) n e
  exact H ⟨i, ⟨n, Nat.lt_succ_of_le hle⟩⟩ ⟨e⟩

/-- The fibres of a proper model over the points outside the zero set of the element of
`exists_ne_zero_geometric` are integral of the dimension of the base change to `K`, and normal if
that is normal. -/
public lemma fibre_of_exists_ne_zero_geometric {R : Subalgebra k₀ K} {Y X' : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) (r : R)
    (H : ∀ y : Spec (.of R), r ∉ y.asIdeal →
      geometrically (fun Z : Scheme.{u} => IsIntegral Z) (f.fiberToSpecResidueField y) ∧
      geometrically (fun Z : Scheme.{u} => topologicalKrullDim Z = topologicalKrullDim X')
        (f.fiberToSpecResidueField y) ∧
      (IsNormal X' → geometrically (fun Z : Scheme.{u} => IsNormal Z)
        (f.fiberToSpecResidueField y)))
    (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of R))
    (ht : r ∉ (t.base (IsLocalRing.closedPoint L)).asIdeal) :
    IsIntegral (pullback (C := Scheme.{u}) f t) ∧
      topologicalKrullDim (pullback (C := Scheme.{u}) f t) = topologicalKrullDim X' ∧
      (IsNormal X' → IsNormal (pullback (C := Scheme.{u}) f t)) := by
  have hU : Set.range t.base ⊆ {y : Spec (.of R) | r ∉ y.asIdeal} := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim z (IsLocalRing.closedPoint L)]
  have := isClosedUnderIsomorphisms_isIntegral
  have := isClosedUnderIsomorphisms_isNormal
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (fun Z : Scheme.{u} => topologicalKrullDim Z = topologicalKrullDim X') :=
    isClosedUnderIsomorphisms_topologicalKrullDim _
  have e : pullback (C := Scheme.{u}) (pullback.snd f t) (𝟙 (Spec (.of L))) ≅
      pullback (C := Scheme.{u}) f t :=
    asIso (pullback.fst (pullback.snd f t) (𝟙 (Spec (.of L))))
  have g₁ := pullback_of_geometrically
    (geometrically_pullback_snd_of_fibers f t _ hU fun y hy => (H y hy).1) L (𝟙 _)
  have g₂ := pullback_of_geometrically
    (geometrically_pullback_snd_of_fibers f t _ hU fun y hy => (H y hy).2.1) L (𝟙 _)
  refine ⟨ObjectProperty.prop_of_iso _ e g₁, ObjectProperty.prop_of_iso
    (fun Z : Scheme.{u} => topologicalKrullDim Z = topologicalKrullDim X') e g₂, fun hn => ?_⟩
  exact ObjectProperty.prop_of_iso _ e (pullback_of_geometrically
    (geometrically_pullback_snd_of_fibers f t _ hU fun y hy => (H y hy).2.2 hn) L (𝟙 _))

include hint M in
/-- The dimension of a vertex over `K` is a natural number. -/
public lemma Model.exists_topologicalKrullDim_eq (j : J) :
    ∃ d : ℕ, topologicalKrullDim (X.obj j).left = d := by
  have := hint j
  have : IsProper (M.Y.obj j).hom := isProper_of_isProjectiveMorphism _ (M.hproj j)
  have : IsProper (X.obj j).hom :=
    MorphismProperty.of_isPullback (P := @IsProper) (M.cart.isPullback j) inferInstance
  have hne_top := topologicalKrullDim_ne_top_of_isProper K (X.obj j).hom
  have hne_bot : topologicalKrullDim (X.obj j).left ≠ ⊥ := by
    rw [Ne, topologicalKrullDim_eq_bot_iff_isEmpty]
    exact not_isEmpty_of_nonempty _
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hne_bot
  lift e to ℕ using (by rintro rfl; exact hne_top he.symm)
  exact ⟨e, he.symm⟩

include hint in
/-- **Codimension bounds of closed subschemes spread to the fibres.** -/
public lemma Model.exists_le_coheight_comap {S₀ : CoefficientModels.FGSub k₀ K}
    (h₀ : M.R ≤ S₀) (j : J) (I₀ : ((M.stage h₀).obj j).left.IdealSheafData) (r : ℕ)
    (hK : ∀ x ∈ ((I₀.comap (M.cmp h₀ j)).support : Set (X.obj j).left),
      (r : ℕ∞) ≤ Order.coheight x) :
    ∃ (S₂ : CoefficientModels.FGSub k₀ K) (h₂ : S₀ ≤ S₂), ∀ (S : CoefficientModels.FGSub k₀ K)
      (h : S₂ ≤ S) (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      IsIntegral ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).left →
      topologicalKrullDim ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).left =
        topologicalKrullDim (X.obj j).left →
      ∀ x ∈ (I₀.comap (M.fibreMap h₀ (h₂.trans h) t j)).support,
        (r : ℕ∞) ≤ Order.coheight x := by
  have := hint j
  have hlftK := M.locallyOfFiniteType_obj j
  obtain ⟨d, hd⟩ := Model.exists_topologicalKrullDim_eq hint M j
  have hsupp : ((I₀.comap (M.cmp h₀ j)).support : Set (X.obj j).left) =
      M.cmp h₀ j ⁻¹' (I₀.support : Set _) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hfib : ∀ {S : CoefficientModels.FGSub k₀ K} (h : S₀ ≤ S) {L : Type u} [Field L]
      (t : Spec (.of L) ⟶ Spec (.of S.1)),
      ((I₀.comap (M.fibreMap h₀ h t j)).support : Set _) =
        M.fibreMap h₀ h t j ⁻¹' (I₀.support : Set _) := fun h L _ t => by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hfibre : ∀ {S : CoefficientModels.FGSub k₀ K} (h : S₀ ≤ S) {L : Type u} [Field L]
      (t : Spec (.of L) ⟶ Spec (.of S.1)),
      IsIntegral ((M.stage (h₀.trans h) ⋙ Over.pullback t).obj j).left →
      LocallyOfFiniteType ((M.stage (h₀.trans h) ⋙ Over.pullback t).obj j).hom := fun h L _ t _ =>
    M.locallyOfFiniteType_fibre (h₀.trans h) t j
  rcases (forall_le_coheight_iff (X.obj j).hom hd
    (I₀.comap (M.cmp h₀ j)).support.isClosed r).mp hK with hC | ⟨hrd, hdim⟩
  · obtain ⟨S₂, h₂, H⟩ := M.exists_preimage_eq_empty h₀ j I₀.support (by rw [← hsupp, hC])
    refine ⟨S₂, h₂, fun S h L _ t _ _ x hx => ?_⟩
    rw [← SetLike.mem_coe, hfib, H S h L t] at hx
    exact absurd hx (Set.notMem_empty x)
  · obtain ⟨S₂, h₂, H⟩ := M.exists_topologicalKrullDim_preimage_le h₀ j I₀.support (d - r)
      (by rw [← hsupp]; exact hdim)
    refine ⟨S₂, h₂, fun S h L _ t hI hD => ?_⟩
    haveI := hI
    have := hfibre (h₂.trans h) t hI
    refine (forall_le_coheight_iff ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).hom
      (hD.trans hd) (I₀.comap (M.fibreMap h₀ (h₂.trans h) t j)).support.isClosed r).mpr
      (Or.inr ⟨hrd, ?_⟩)
    rw [hfib]
    exact H S h L t

/-- **Inclusions of images of arrows spread to the fibres.** -/
public lemma Model.eventually_range_subset {c c' j₀ : J} (a : c ⟶ j₀) (b : c' ⟶ j₀)
    (hab : Set.range (X.map a).left.base ⊆ Set.range (X.map b).left.base) :
    M.Eventually fun S h => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      Set.range ((M.stage h ⋙ Over.pullback t).map a).left.base ⊆
        Set.range ((M.stage h ⋙ Over.pullback t).map b).left.base := by
  obtain ⟨S₂, h₂, H⟩ := M.exists_preimage_subset le_rfl j₀ (M.rangeClosed le_rfl a)
    (M.rangeClosed le_rfl b) (by
      change M.cmp le_rfl j₀ ⁻¹' Set.range _ ⊆ M.cmp le_rfl j₀ ⁻¹' Set.range _
      rw [← range_snd_of_isPullback ((M.isCartesian_cmp le_rfl).isPullback_map a),
        ← range_snd_of_isPullback ((M.isCartesian_cmp le_rfl).isPullback_map b)]
      exact hab)
  refine ⟨S₂, h₂, fun S h L _ t => ?_⟩
  have := H S h L t
  change _ ⁻¹' Set.range _ ⊆ _ ⁻¹' Set.range _ at this
  rwa [← range_snd_of_isPullback ((M.isCartesian_fibre le_rfl (h₂.trans h) t).isPullback_map a),
    ← range_snd_of_isPullback ((M.isCartesian_fibre le_rfl (h₂.trans h) t).isPullback_map b)]
    at this

/-- **Non-inclusions of images of arrows spread to the fibres.** -/
public lemma Model.eventually_range_not_subset {c c' j₀ : J} (a : c ⟶ j₀) (b : c' ⟶ j₀)
    (hab : ¬ Set.range (X.map a).left.base ⊆ Set.range (X.map b).left.base) :
    M.Eventually fun S h => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      ¬ Set.range ((M.stage h ⋙ Over.pullback t).map a).left.base ⊆
        Set.range ((M.stage h ⋙ Over.pullback t).map b).left.base := by
  obtain ⟨S₀, h₀, Hf⟩ := eventually_projective_flat M
  have hflat : Flat ((M.stage (h₀.trans le_rfl)).obj c).hom := ((Hf S₀ le_rfl).1 c).2
  have := (M.finitePresentation_stage (h₀.trans le_rfl) c).1
  let V : ((M.stage (h₀.trans le_rfl)).obj c).left.Opens :=
    ((M.stage (h₀.trans le_rfl)).map a).left ⁻¹ᵁ (M.rangeClosed (h₀.trans le_rfl) b).compl
  obtain ⟨x, hx⟩ := Set.not_subset.mp hab
  obtain ⟨⟨y, rfl⟩, hy⟩ := hx
  have hV : (M.cmp (h₀.trans le_rfl) c ⁻¹ᵁ V : Set (X.obj c).left).Nonempty := by
    refine ⟨y, ?_⟩
    change ((M.stage (h₀.trans le_rfl)).map a).left (M.cmp (h₀.trans le_rfl) c y) ∉
      Set.range ((M.stage (h₀.trans le_rfl)).map b).left.base
    rw [← Scheme.Hom.comp_apply, ← (M.isCartesian_cmp (h₀.trans le_rfl)).w a,
      Scheme.Hom.comp_apply, ← Set.mem_preimage,
      ← range_snd_of_isPullback ((M.isCartesian_cmp (h₀.trans le_rfl)).isPullback_map b)]
    exact hy
  obtain ⟨S₂, h₂, H₂⟩ := M.exists_nonempty_fibre c (h₀.trans le_rfl) V hV
  refine ⟨S₂, h₀.trans h₂, fun S h L _ t hsub => ?_⟩
  obtain ⟨z, hz⟩ := H₂ S h L t
  have hz' : M.fibreMap (h₀.trans le_rfl) (h₂.trans h) t c z ∈ V := hz
  apply hz'
  have hmem : ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).map a).left z ∈
      Set.range ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).map b).left.base :=
    hsub ⟨z, rfl⟩
  rw [range_snd_of_isPullback ((M.isCartesian_fibre (h₀.trans le_rfl) (h₂.trans h) t).isPullback_map
    b)] at hmem
  change ((M.stage (h₀.trans le_rfl)).map a).left (M.fibreMap (h₀.trans le_rfl) (h₂.trans h) t c z)
      ∈
    Set.range ((M.stage (h₀.trans le_rfl)).map b).left.base
  rw [← Scheme.Hom.comp_apply, ← (M.isCartesian_fibre (h₀.trans le_rfl) (h₂.trans h) t).w a,
    Scheme.Hom.comp_apply]
  exact hmem

include hint in
/-- **Exceptional sets of the fibres lie over the exceptional set over `K`.** The exceptional set
of a morphism of the diagram over `K` is the preimage of a closed subset `D` of a stage, whose
preimage in every field-valued fibre of every late stage contains the exceptional set of the
fibre. -/
public lemma Model.exists_exceptionalSet_subset {j j' : J} (g : j ⟶ j') :
    ∃ (S₀ : CoefficientModels.FGSub k₀ K) (h₀ : M.R ≤ S₀)
      (D : TopologicalSpace.Closeds ((M.stage h₀).obj j).left),
      M.cmp h₀ j ⁻¹' (D : Set ((M.stage h₀).obj j).left) =
        (Mori.exceptionalSet (X.map g).left : Set (X.obj j).left) ∧
      ∃ (S₂ : CoefficientModels.FGSub k₀ K) (h₂ : S₀ ≤ S₂), ∀ (S : CoefficientModels.FGSub k₀ K)
        (h : S₂ ≤ S) (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
        (Mori.exceptionalSet ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).map g).left :
          Set _) ⊆ M.fibreMap h₀ (h₂.trans h) t j ⁻¹' D := by
  classical
  have := hint j
  -- the biregular locus over `K` descends to an open at a stage
  let B := Mori.biregularLocus (X.map g).left
  have hB : IsIso ((X.map g).left ∣_ B) := Mori.isBiregular_biregularLocus _
  have : QuasiCompact (X.obj j').hom :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (M.cart.isPullback j') (M.fp j').2.1
  have := M.locallyOfFiniteType_obj j'
  have : IsLocallyNoetherian (X.obj j').left :=
    LocallyOfFiniteType.isLocallyNoetherian (X.obj j').hom
  have : CompactSpace (X.obj j').left := QuasiCompact.compactSpace_of_compactSpace (X.obj j').hom
  have : IsNoetherian (X.obj j').left := ⟨⟩
  obtain ⟨S₀, h₀, HV⟩ := M.exists_open j' B (TopologicalSpace.NoetherianSpace.isCompact _)
  obtain ⟨V, -, hVB⟩ := HV S₀ le_rfl
  -- the restriction over `V` at the stage `S₀`
  have : Algebra.FiniteType k₀ S₀.1 := (Subalgebra.fg_iff_finiteType _).mp S₀.2
  have : IsNoetherianRing S₀.1 := Algebra.FiniteType.isNoetherianRing k₀ S₀.1
  have := (M.finitePresentation_stage h₀ j).1
  have := (M.finitePresentation_stage h₀ j').1
  have := M.compactSpace_stage h₀ j
  have := M.compactSpace_stage h₀ j'
  have := M.quasiSeparatedSpace_stage h₀ j
  have := M.quasiSeparatedSpace_stage h₀ j'
  have : IsLocallyNoetherian ((M.stage h₀).obj j).left :=
    LocallyOfFiniteType.isLocallyNoetherian ((M.stage h₀).obj j).hom
  have : IsLocallyNoetherian ((M.stage h₀).obj j').left :=
    LocallyOfFiniteType.isLocallyNoetherian ((M.stage h₀).obj j').hom
  have : IsNoetherian ((M.stage h₀).obj j).left := ⟨⟩
  have : IsNoetherian ((M.stage h₀).obj j').left := ⟨⟩
  let gS₀ := ((M.stage h₀).map g).left
  let A : Over (Spec (.of S₀.1)) := Over.mk ((gS₀ ⁻¹ᵁ V).ι ≫ ((M.stage h₀).obj j).hom)
  let Bo : Over (Spec (.of S₀.1)) := Over.mk (V.ι ≫ ((M.stage h₀).obj j').hom)
  let φ : A ⟶ Bo := Over.homMk (gS₀ ∣_ V) (by
    simp only [A, Bo, Over.mk_hom]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w])
  have hK : IsIso ((Over.pullback (κ S₀.1)).map φ).left := by
    have h₁ := (M.isCartesian_cmp h₀).isPullback_restrictTarget g V
    have h₂ := overPullback_isPullback (κ S₀.1) A Bo φ
    have hcmp := AlgebraicGeometry.isPullback_morphismRestrict (M.cmp h₀ j') V
    let e : pullback Bo.hom (κ S₀.1) ⟶ (X.obj j').left :=
      ((M.isCartesian_cmp h₀).isPullback j').lift (pullback.fst Bo.hom (κ S₀.1) ≫ V.ι)
        (pullback.snd Bo.hom (κ S₀.1)) (by rw [Category.assoc]; exact pullback.condition)
    let c : pullback Bo.hom (κ S₀.1) ⟶ (M.cmp h₀ j' ⁻¹ᵁ V).toScheme :=
      hcmp.lift (pullback.fst Bo.hom (κ S₀.1)) e (IsPullback.lift_fst _ _ _ _).symm
    obtain ⟨a, ha⟩ := isPullback_of_isPullback_comp h₁ h₂ c (hcmp.lift_fst _ _ _)
    have : IsIso ((X.map g).left ∣_ (M.cmp h₀ j' ⁻¹ᵁ V)) := by rwa [hVB]
    exact MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme.{u}) ha this
  have : CompactSpace A.left :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have : CompactSpace Bo.left :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have : QuasiSeparatedSpace A.left :=
    (isQuasiSeparated_iff_quasiSeparatedSpace ((gS₀ ⁻¹ᵁ V : _) : Set ((M.stage h₀).obj j).left)
      (gS₀ ⁻¹ᵁ V).isOpen).mp (IsQuasiSeparated.of_quasiSeparatedSpace _)
  have : QuasiSeparatedSpace Bo.left :=
    (isQuasiSeparated_iff_quasiSeparatedSpace (V : Set ((M.stage h₀).obj j').left) V.isOpen).mp
      (IsQuasiSeparated.of_quasiSeparatedSpace _)
  have := M.locallyOfFinitePresentation_stage_map h₀ g
  have : LocallyOfFinitePresentation φ.left :=
    MorphismProperty.of_isPullback (AlgebraicGeometry.isPullback_morphismRestrict gS₀ V).flip
      ‹LocallyOfFinitePresentation gS₀›
  obtain ⟨S₁, h₁, H₁⟩ := exists_stage_isIso S₀ φ hK
  -- the complement of `g⁻¹ V` at the stage `S₀`, whose preimage over `K` is `Ex(g)`
  let D := (gS₀ ⁻¹ᵁ V).compl
  have hpD : M.cmp h₀ j ⁻¹' (D : Set ((M.stage h₀).obj j).left) =
      (Mori.exceptionalSet (X.map g).left : Set (X.obj j).left) := by
    ext x
    change gS₀ (M.cmp h₀ j x) ∉ V ↔ (X.map g).left x ∉ B
    rw [← hVB, ← Scheme.Hom.comp_apply, ← (M.isCartesian_cmp h₀).w g]
    rfl
  refine ⟨S₀, h₀, D, hpD, S₁, h₁, fun S h L _ t => ?_⟩
  have hS₀ : S₀ ≤ S := h₁.trans h
  -- the restriction over the preimage of `V` is an isomorphism at the stage `S`
  let W := M.stageCmp h₀ hS₀ j' ⁻¹ᵁ V
  have hWiso : IsIso (((M.stage (h₀.trans hS₀)).map g).left ∣_ W) := by
    have hst := (M.isCartesian_stageCmp h₀ hS₀).isPullback_restrictTarget g V
    have h₂' := overPullback_isPullback (π (show S₀.1 ≤ S.1 from hS₀)) A Bo φ
    let c : W.toScheme ⟶ pullback Bo.hom (π (show S₀.1 ≤ S.1 from hS₀)) :=
      pullback.lift (M.stageCmp h₀ hS₀ j' ∣_ V) (W.ι ≫ ((M.stage (h₀.trans hS₀)).obj j').hom) (by
        simp only [Bo, Over.mk_hom]
        rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Category.assoc,
          ((M.isCartesian_stageCmp h₀ hS₀).isPullback j').w])
    obtain ⟨a, ha⟩ := isPullback_of_isPullback_comp h₂' hst c (pullback.lift_fst _ _ _)
    exact MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme.{u}) ha
      (H₁ S h)
  -- hence on the fibre
  let Z := M.stage (h₀.trans hS₀) ⋙ Over.pullback t
  have hft := (isCartesian_pullback t (M.stage (h₀.trans hS₀))).isPullback_restrictTarget g W
  have hiso := MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme.{u}) hft
    hWiso
  have hle := Mori.le_biregularLocus (f := (Z.map g).left) hiso
  intro x hx
  change gS₀ ((pullback.fst ((M.stage (h₀.trans hS₀)).obj j).hom t ≫
    M.stageCmp h₀ hS₀ j) x) ∉ V
  intro hV
  apply hx
  apply hle
  have e : (Z.map g).left ≫ pullback.fst ((M.stage (h₀.trans hS₀)).obj j').hom t ≫
      M.stageCmp h₀ hS₀ j' = (pullback.fst ((M.stage (h₀.trans hS₀)).obj j).hom t ≫
        M.stageCmp h₀ hS₀ j) ≫ gS₀ := by
    rw [← Category.assoc, (isCartesian_pullback t _).w g, Category.assoc,
      (M.isCartesian_stageCmp h₀ hS₀).w g, Category.assoc]
  change ((Z.map g).left ≫ pullback.fst ((M.stage (h₀.trans hS₀)).obj j').hom t ≫
    M.stageCmp h₀ hS₀ j') x ∈ V
  rw [e]
  exact hV

include hint in
/-- **Exceptional prime divisors stay exceptional on the fibres.** For a proper birational
morphism `μ` of the diagram over `K` onto a normal vertex, a closed subset of the exceptional set
over `K`, modelled at a stage by the support of `I₀`, has fibres contained in the exceptional sets
of
the fibres of `μ` along every prime divisor of the fibre cut out by `I₀`: its image in the target
consists of points of coheight at least two, and this persists on the fibres. -/
public lemma Model.exists_subset_exceptionalSet {j j₀ : J} (μ : j ⟶ j₀)
    [IsNormal (X.obj j₀).left] (hμ : Mori.IsBirationalMorphism (X.map μ).left)
    {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (I₀ : ((M.stage h₀).obj j).left.IdealSheafData)
    (hI : ((I₀.comap (M.cmp h₀ j)).support : Set (X.obj j).left) ⊆
      Mori.exceptionalSet (X.map μ).left) :
    ∃ (S₂ : CoefficientModels.FGSub k₀ K) (h₂ : S₀ ≤ S₂), ∀ (S : CoefficientModels.FGSub k₀ K)
      (h : S₂ ≤ S) (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      IsIntegral ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j₀).left →
      topologicalKrullDim ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j₀).left =
        topologicalKrullDim (X.obj j₀).left →
      ∀ Ps : Mori.PrimeDivisor ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).left,
        Ps.idealSheaf = I₀.comap (M.fibreMap h₀ (h₂.trans h) t j) →
        Ps.support ⊆ Mori.exceptionalSet
          ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).map μ).left := by
  classical
  have := hint j
  have := hint j₀
  have : IsLocallyNoetherian (X.obj j₀).left := by
    have := (M.fp j₀).1
    have : LocallyOfFiniteType (X.obj j₀).hom :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (M.cart.isPullback j₀)
        inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian (X.obj j₀).hom
  have : IsProper (X.map μ).left := by
    have hP : ∀ i, IsProper (X.obj i).hom := fun i =>
      MorphismProperty.of_isPullback (P := @IsProper) (M.cart.isPullback i)
        (isProper_of_isProjectiveMorphism _ (M.hproj i))
    have := hP j
    have := hP j₀
    have : IsProper ((X.map μ).left ≫ (X.obj j₀).hom) := by rw [Over.w]; infer_instance
    exact IsProper.of_comp _ (X.obj j₀).hom
  have := M.isProper_stage_map h₀ μ
  -- the image of the model in the target, a closed set of points of coheight at least two
  let C : TopologicalSpace.Closeds ((M.stage h₀).obj j₀).left :=
    ⟨((M.stage h₀).map μ).left.base '' I₀.support,
      ((M.stage h₀).map μ).left.isClosedMap _ I₀.support.isClosed⟩
  have hK : ∀ x ∈ ((Scheme.IdealSheafData.vanishingIdeal C).comap (M.cmp h₀ j₀)).support,
      ((2 : ℕ) : ℕ∞) ≤ Order.coheight x := by
    intro x hx
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.support_comap,
      TopologicalSpace.Closeds.coe_preimage, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hx
    change x ∈ M.cmp h₀ j₀ ⁻¹' (((M.stage h₀).map μ).left.base '' I₀.support) at hx
    rw [preimage_image_of_isPullback ((M.isCartesian_cmp h₀).isPullback_map μ)] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyE : y ∈ Mori.exceptionalSet (X.map μ).left := hI (by
      rwa [Scheme.IdealSheafData.support_comap])
    by_contra hlt
    exact (Mori.mem_exceptionalSet.mp hyE)
      (mem_biregularLocus_of_coheight_le_one_of_isNormal _ hμ
        (Order.le_of_lt_succ (by exact_mod_cast not_le.mp hlt)))
  obtain ⟨S₂, h₂, H⟩ := M.exists_le_coheight_comap hint h₀ j₀ _ 2 hK
  refine ⟨S₂, h₂, fun S h L _ t hI' hD' Ps hPs x hx => ?_⟩
  have hco := H S h L t hI' hD'
  -- the generic point of `Ps`
  have hη : Ps.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hx
  intro hxV
  have hηV : ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).map μ).left Ps.genericPoint ∈
      Mori.biregularLocus ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).map μ).left :=
    (hη.map (Scheme.Hom.continuous _)).mem_open (Mori.biregularLocus _).isOpen hxV
  have h1 := MMP.Positivity.coheight_map_of_mem_biregularLocus _ hηV
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h1
  have hmem : ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).map μ).left Ps.genericPoint ∈
      ((Scheme.IdealSheafData.vanishingIdeal C).comap (M.fibreMap h₀ (h₂.trans h) t j₀)).support :=
          by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.support_comap,
      TopologicalSpace.Closeds.coe_preimage, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    change ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).map μ).left Ps.genericPoint ∈
      M.fibreMap h₀ (h₂.trans h) t j₀ ⁻¹' (((M.stage h₀).map μ).left.base '' I₀.support)
    rw [preimage_image_of_isPullback ((M.isCartesian_fibre h₀ (h₂.trans h) t).isPullback_map μ)]
    refine ⟨Ps.genericPoint, ?_, rfl⟩
    have : Ps.genericPoint ∈ Ps.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    change Ps.genericPoint ∈ (Ps.idealSheaf.support : Set _) at this
    rwa [hPs, Scheme.IdealSheafData.support_comap] at this
  have := hco _ hmem
  rw [h1] at this
  exact absurd this (by norm_num)

include hint in
/-- **Smallness spreads to the fibres**: the exceptional set of the fibre of a small morphism of
the diagram over `K` has codimension at least two on every field-valued fibre of every late stage
whose source vertex is integral of the dimension of the source over `K`. -/
public lemma Model.eventually_two_le_codimension {j j' : J} (g : j ⟶ j')
    (hg : 2 ≤ Mori.closedsCodimension (Mori.exceptionalSet (X.map g).left)) :
    M.Eventually fun S h => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      IsIntegral ((M.stage h ⋙ Over.pullback t).obj j).left →
      topologicalKrullDim ((M.stage h ⋙ Over.pullback t).obj j).left =
        topologicalKrullDim (X.obj j).left →
      2 ≤ Mori.closedsCodimension (Mori.exceptionalSet ((M.stage h ⋙ Over.pullback t).map g).left)
          := by
  have := hint j
  have := M.locallyOfFiniteType_obj j
  obtain ⟨d, hd⟩ := Model.exists_topologicalKrullDim_eq hint M j
  obtain ⟨S₀, h₀, D, hD, S₁, h₁, H₁⟩ := M.exists_exceptionalSet_subset hint g
  -- over `K`, the preimage of `D` is `Ex(g)`: empty or of dimension at most `d - 2`
  have hK := (forall_le_coheight_iff (X.obj j).hom hd
    (D.isClosed.preimage (M.cmp h₀ j).continuous) 2).mp fun x hx => by
      rw [hD] at hx
      exact_mod_cast Flips.le_closedsCodimension_iff_le_coheight.mp hg x hx
  obtain ⟨S₂, h₂, H₂⟩ : ∃ (S₂ : CoefficientModels.FGSub k₀ K) (h₂ : S₀ ≤ S₂),
      ∀ (S : CoefficientModels.FGSub k₀ K) (h : S₂ ≤ S) (L : Type u) [Field L]
        (t : Spec (.of L) ⟶ Spec (.of S.1)),
        M.fibreMap h₀ (h₂.trans h) t j ⁻¹' D = ∅ ∨ (2 ≤ d ∧
          topologicalKrullDim (M.fibreMap h₀ (h₂.trans h) t j ⁻¹' D) ≤
            ((d - 2 : ℕ) : WithBot ℕ∞)) := by
    rcases hK with hE | ⟨h2, hdim⟩
    · obtain ⟨S₂, h₂, H⟩ := M.exists_preimage_eq_empty h₀ j D hE
      exact ⟨S₂, h₂, fun S h L _ t => Or.inl (H S h L t)⟩
    · obtain ⟨S₂, h₂, H⟩ := M.exists_topologicalKrullDim_preimage_le h₀ j D (d - 2) hdim
      exact ⟨S₂, h₂, fun S h L _ t => Or.inr ⟨h2, H S h L t⟩⟩
  refine ⟨⟨S₁.1 ⊔ S₂.1, S₁.2.sup S₂.2⟩, h₀.trans (h₁.trans (le_sup_left (a := S₁.1))),
    fun S hS L _ t hint' hdim' => ?_⟩
  have hS₁ : S₁ ≤ S := (le_sup_left (a := S₁.1)).trans hS
  have hS₂ : S₂ ≤ S := (le_sup_right (b := S₂.1)).trans hS
  haveI := hint'
  have := M.locallyOfFiniteType_fibre (h₀.trans (h₁.trans hS₁)) t j
  -- on the fibre, `Ex` lies in the preimage of `D`, whose points have coheight at least two
  refine Flips.le_closedsCodimension_iff_le_coheight.mpr fun x hx => ?_
  exact_mod_cast (forall_le_coheight_iff
    ((M.stage (h₀.trans (h₁.trans hS₁)) ⋙ Over.pullback t).obj j).hom (hdim'.trans hd)
    (D.isClosed.preimage (M.fibreMap h₀ (h₂.trans hS₂) t j).continuous) 2).mpr
      (H₂ S hS₂ L t) x (H₁ S hS₁ L t hx)

/-- A property of the stages above `S₀` that holds at all stages from some stage on. -/
@[expose] public def EvAbove (S₀ : CoefficientModels.FGSub k₀ K)
    (P : ∀ S : CoefficientModels.FGSub k₀ K, S₀ ≤ S → Prop) :
    Prop :=
  ∃ (S₂ : CoefficientModels.FGSub k₀ K) (h₂ : S₀ ≤ S₂), ∀ S (h : S₂ ≤ S), P S (h₂.trans h)

/-- Two properties that eventually hold above `S₀` hold together eventually. -/
public lemma EvAbove.and {S₀ : CoefficientModels.FGSub k₀ K}
    {P Q : ∀ S : CoefficientModels.FGSub k₀ K, S₀ ≤ S → Prop}
    (hP : EvAbove S₀ P) (hQ : EvAbove S₀ Q) : EvAbove S₀ fun S h => P S h ∧ Q S h := by
  obtain ⟨S₁, h₁, H₁⟩ := hP
  obtain ⟨S₂, h₂, H₂⟩ := hQ
  refine ⟨⟨S₁.1 ⊔ S₂.1, S₁.2.sup S₂.2⟩, h₁.trans (le_sup_left (a := S₁.1)), fun S h => ?_⟩
  exact ⟨H₁ S ((le_sup_left (a := S₁.1)).trans h), H₂ S ((le_sup_right (b := S₂.1)).trans h)⟩

/-- A property implied by one that eventually holds above `S₀` eventually holds. -/
public lemma EvAbove.mono {S₀ : CoefficientModels.FGSub k₀ K}
    {P Q : ∀ S : CoefficientModels.FGSub k₀ K, S₀ ≤ S → Prop}
    (hP : EvAbove S₀ P) (hPQ : ∀ S h, P S h → Q S h) : EvAbove S₀ Q := by
  obtain ⟨S₁, h₁, H₁⟩ := hP
  exact ⟨S₁, h₁, fun S h => hPQ _ _ (H₁ S h)⟩

/-- The true property eventually holds above every stage. -/
public lemma EvAbove.true (S₀ : CoefficientModels.FGSub k₀ K) : EvAbove S₀ fun _ _ => True :=
  ⟨S₀, le_rfl, fun _ _ => trivial⟩

/-- Finitely many properties that each eventually hold above `S₀` hold together eventually. -/
public lemma EvAbove.forall_finset {S₀ : CoefficientModels.FGSub k₀ K} {α : Type*} (s : Finset α)
    {P : α → ∀ S : CoefficientModels.FGSub k₀ K, S₀ ≤ S → Prop}
    (hP : ∀ a ∈ s, EvAbove S₀ (P a)) : EvAbove S₀ fun S h => ∀ a ∈ s, P a S h := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (EvAbove.true S₀).mono fun _ _ _ a ha => absurd ha (Finset.notMem_empty a)
  | insert a s ha ih =>
    refine ((hP a (Finset.mem_insert_self a s)).and
      (ih fun b hb => hP b (Finset.mem_insert_of_mem hb))).mono fun S h H b hb => ?_
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact H.1
    · exact H.2 b hb

/-- Restriction maps along equal morphisms agree. -/
private lemma appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g) (U : Y.Opens)
    (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) (x : Γ(Y, U)) :
    f.appLE U V e x = g.appLE U V e' x := by
  subst hfg
  rfl

/-- **Sections descend to a stage**, as sections of the vertex over the preimage of `V`. -/
private lemma Model.exists_section' {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀) (j : J)
    (V : ((M.stage h₀).obj j).left.Opens) (hV : IsCompact (V : Set ((M.stage h₀).obj j).left))
    (a : Γ((X.obj j).left, M.cmp h₀ j ⁻¹ᵁ V)) :
    ∃ (S₁ : CoefficientModels.FGSub k₀ K) (h₁ : S₀ ≤ S₁)
      (a₁ : Γ(((M.stage (h₀.trans h₁)).obj j).left, M.stageCmp h₀ h₁ j ⁻¹ᵁ V)),
      (M.cmp (h₀.trans h₁) j).appLE (M.stageCmp h₀ h₁ j ⁻¹ᵁ V) (M.cmp h₀ j ⁻¹ᵁ V)
        (by rw [← Scheme.Hom.comp_preimage, M.cmp_stageCmp]) a₁ = a := by
  obtain ⟨S₁, h₁, a₁, ha₁⟩ := M.exists_section h₀ j V hV ((M.cmp h₀ j ⁻¹ᵁ V).topIso.inv a)
  refine ⟨S₁, h₁, (M.stageCmp h₀ h₁ j ⁻¹ᵁ V).topIso.hom a₁, ?_⟩
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top] at ha₁
  have := congrArg (M.cmp h₀ j ⁻¹ᵁ V).topIso.hom.hom ha₁
  simp only [← CommRingCat.comp_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id] at this
  simpa only [CommRingCat.comp_apply, CommRingCat.id_apply] using this

/-- **The order along a prime divisor of a unit times a power of a local equation.** If the
stalk at the generic point of a prime divisor `Γ` of the ideal sheaf of `Γ` is generated by `π`,
then `ord_Γ(u π^c) = c` for every unit `u`. -/
private lemma ord_unit_mul_pow_of_stalk_eq_span {F : Scheme.{u}} [IsIntegral F]
    [IsLocallyNoetherian F]
    (Γ : Mori.PrimeDivisor F) {π u : F.presheaf.stalk Γ.genericPoint}
    (hπ : IdealSheafData.stalk Γ.idealSheaf Γ.genericPoint = Ideal.span {π}) (hu : IsUnit u)
    (c : ℕ) :
    F.ord (algebraMap (F.presheaf.stalk Γ.genericPoint) F.functionField (u * π ^ c))
      Γ.genericPoint = c := by
  have hz := Γ.coheight_genericPoint
  haveI := Γ.integral
  have hm : Ideal.span {π} = IsLocalRing.maximalIdeal (F.presheaf.stalk Γ.genericPoint) :=
    hπ.symm.trans (IdealSheafData.stalk_subschemeι_genericPoint_eq_maximalIdeal Γ.idealSheaf)
  have hπ1 : Ring.ord (F.presheaf.stalk Γ.genericPoint) π = 1 :=
    MMP.Intersection.ord_eq_one_of_isMaximal_span (hm ▸ IsLocalRing.maximalIdeal.isMaximal _)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    have hbot : IsLocalRing.maximalIdeal (F.presheaf.stalk Γ.genericPoint) = ⊥ := by
      rw [← hm, Ideal.span_singleton_eq_bot]
    have h1 := ringKrullDim_stalk_eq_coheight Γ.genericPoint
    rw [ringKrullDim_eq_zero_of_isField (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot), hz]
      at h1
    exact absurd h1 (by decide)
  have hπK : algebraMap (F.presheaf.stalk Γ.genericPoint) F.functionField π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hπ0
  have huK : algebraMap (F.presheaf.stalk Γ.genericPoint) F.functionField u ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hu.ne_zero
  rw [map_mul, map_pow, Scheme.ord_mul huK (pow_ne_zero _ hπK), ← zpow_natCast,
    MMP.Mori.ord_zpow _ hπK, Γ.ord_algebraMap_of_isUnit hu,
    AlgebraicGeometry.ord_algebraMap_stalk _ hz π hπ0]
  change (0 : ℤ) + c * (((Ring.ord _ π).toNat : ℕ) : ℤ) = c
  rw [hπ1]
  simp

/-- **Orders through local data on a base.** Let `f : F ⟶ Y` be a morphism from an integral
locally Noetherian scheme, `W` an affine open of `Y` on which an ideal sheaf `𝓘` is generated by
`π` and `a = u π^c` with `u` a unit. For a prime divisor `Γ` of `F` with ideal sheaf `f^*𝓘` and
generic point over `W`, the order of `f^*a` along `Γ` is `c`. -/
private lemma ord_germToFunctionField_of_ideal_eq_span {Y F : Scheme.{u}} [IsIntegral F]
    [IsLocallyNoetherian F] (f : F ⟶ Y) (𝓘 : Y.IdealSheafData) (W : Y.affineOpens)
    {π u ui a : Γ(Y, W.1)} {c : ℕ} (hI : 𝓘.ideal W = Ideal.span {π}) (hu : u * ui = 1)
    (ha : a = u * π ^ c) (Γ : Mori.PrimeDivisor F) (hΓ : Γ.idealSheaf = 𝓘.comap f)
    (hη : f Γ.genericPoint ∈ W.1) [Nonempty (f ⁻¹ᵁ W.1)] :
    F.ord (F.germToFunctionField (f ⁻¹ᵁ W.1) (f.app W.1 a)) Γ.genericPoint = c := by
  have hη' : Γ.genericPoint ∈ f ⁻¹ᵁ W.1 := hη
  have e : F.presheaf.germ (f ⁻¹ᵁ W.1) _ hη' (f.app W.1 a) =
      f.stalkMap _ (Y.presheaf.germ W.1 _ hη a) :=
    (Scheme.Hom.germ_stalkMap_apply f W.1 _ hη a).symm
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField _ hη', e, ha,
    map_mul, map_mul, map_pow, map_pow]
  refine ord_unit_mul_pow_of_stalk_eq_span Γ ?_ ?_ c
  · rw [hΓ, AlgebraicGeometry.IdealSheafData.stalk_comap,
      AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ 𝓘 _ W hη, hI, Ideal.map_span,
      Ideal.map_span, Set.image_singleton, Set.image_singleton]
  · refine IsUnit.map _ (IsUnit.map _ (IsUnit.of_mul_eq_one _ hu))

/-- In a discrete valuation ring, an ideal generating the maximal ideal along a ring map contains
an element whose image generates the maximal ideal. -/
private lemma exists_mem_span_eq_maximalIdeal_of_map_eq {A R : Type*} [CommRing A] [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] (φ : A →+* R) (I : Ideal A)
    (hI : I.map φ = IsLocalRing.maximalIdeal R) :
    ∃ g ∈ I, Ideal.span {φ g} = IsLocalRing.maximalIdeal R := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hm : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  by_contra hne
  push Not at hne
  have hle : I.map φ ≤ Ideal.span {ϖ ^ 2} := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    have hgm : φ g ∈ IsLocalRing.maximalIdeal R := hI ▸ Ideal.mem_map_of_mem φ hg
    rw [hm, Ideal.mem_span_singleton'] at hgm
    obtain ⟨r, hr⟩ := hgm
    have hr' : ¬ IsUnit r := by
      intro hu
      apply hne g hg
      rw [← hr, hm, Ideal.span_singleton_mul_left_unit hu]
    have hrm : r ∈ IsLocalRing.maximalIdeal R := hr'
    rw [hm, Ideal.mem_span_singleton'] at hrm
    obtain ⟨s, hs⟩ := hrm
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    exact ⟨s, by rw [← hr, ← hs]; ring⟩
  have hϖm : ϖ ∈ I.map φ := hI ▸ hm ▸ Ideal.mem_span_singleton_self ϖ
  have := hle hϖm
  rw [Ideal.mem_span_singleton'] at this
  obtain ⟨s, hs⟩ := this
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  apply hϖ.not_isUnit
  refine IsUnit.of_mul_eq_one s (mul_left_cancel₀ hϖ0 ?_)
  rw [mul_one]
  calc ϖ * (ϖ * s) = s * ϖ ^ 2 := by ring
    _ = ϖ := hs

private lemma mem_finset_inf_opens {X : Scheme.{u}} {ι : Type*} (U : ι → X.Opens) (s : Finset ι)
    {x : X} : x ∈ s.inf U ↔ ∀ i ∈ s, x ∈ U i := by
  rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf]
  simp

/-- Finitely many elements of a stalk are germs of sections over one open neighbourhood inside a
given one. -/
private lemma exists_open_germ_eq_family {X : Scheme.{u}} (x : X) {ι : Type*} [Fintype ι]
    (r : ι → X.presheaf.stalk x) (V : X.Opens) (hxV : x ∈ V) :
    ∃ (U : X.Opens) (_ : U ≤ V) (hx : x ∈ U) (s : ι → Γ(X, U)),
      ∀ i, X.presheaf.germ U x hx (s i) = r i := by
  choose U hUV hxU s hs using fun i => X.presheaf.exists_le_germ_eq (r i) hxV
  have hx : x ∈ Finset.univ.inf U ⊓ V :=
    ⟨(mem_finset_inf_opens U _).mpr fun i _ => hxU i, hxV⟩
  have hle : ∀ i, Finset.univ.inf U ⊓ V ≤ U i := fun i =>
    inf_le_left.trans (Finset.inf_le (Finset.mem_univ i))
  refine ⟨Finset.univ.inf U ⊓ V, inf_le_right, hx,
    fun i => X.presheaf.map (homOfLE (hle i)).op (s i), fun i => ?_⟩
  rw [TopCat.Presheaf.germ_res_apply]
  exact hs i

/-- Finitely many pairs of sections with equal germs agree on one open neighbourhood. -/
private lemma exists_open_eq_family {X : Scheme.{u}} (x : X) {ι : Type*} [Fintype ι] {U : X.Opens}
    (hx : x ∈ U) (s t : ι → Γ(X, U))
    (h : ∀ i, X.presheaf.germ U x hx (s i) = X.presheaf.germ U x hx (t i)) :
    ∃ (W : X.Opens) (hW : W ≤ U) (_ : x ∈ W),
      ∀ i, X.presheaf.map (homOfLE hW).op (s i) = X.presheaf.map (homOfLE hW).op (t i) := by
  choose W hxW iU iV hW using fun i => X.presheaf.germ_eq x hx hx (s i) (t i) (h i)
  have hx' : x ∈ Finset.univ.inf W ⊓ U :=
    ⟨(mem_finset_inf_opens W _).mpr fun i _ => hxW i, hx⟩
  have hle : ∀ i, Finset.univ.inf W ⊓ U ≤ W i := fun i =>
    inf_le_left.trans (Finset.inf_le (Finset.mem_univ i))
  refine ⟨Finset.univ.inf W ⊓ U, inf_le_right, hx', fun i => ?_⟩
  have e := congrArg (X.presheaf.map (homOfLE (hle i)).op) (hW i)
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp] at e
  exact e

-- The `overlappingInstances` linter times out synthesizing `IsDomain` on a stalk here.
set_option linter.overlappingInstances false in
open Classical in
/-- **Local data at a point with discrete valuation ring stalk.** Let `f : X ⟶ Y`, `x ∈ X` with
`𝒪_{X,x}` a discrete valuation ring whose maximal ideal is the stalk of `f^*𝓘`, `W₀` an affine
open of `Y` containing `f x` and `a` a section of `Y` over `W₀` with nonzero germ at `x`. There
are `g ∈ 𝓘(W₀)` and an open `N ∋ x` over `W₀` on which `f^*a = u f^*g^c` with `u` a unit and on
which every given element of `𝓘(W₀)` is a multiple of `f^*g`. -/
private lemma exists_localData {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [IsDomain (X.presheaf.stalk x)]
    [IsDiscreteValuationRing (X.presheaf.stalk x)] (𝓘 : Y.IdealSheafData)
    (h𝓘 : IdealSheafData.stalk (𝓘.comap f) x = IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (W₀ : Y.affineOpens) (hx : f x ∈ W₀.1) (a : Γ(Y, W₀.1))
    (ha : X.presheaf.germ (f ⁻¹ᵁ W₀.1) x hx (f.app W₀.1 a) ≠ 0) {ι : Type*} [Fintype ι]
    (gen : ι → Γ(Y, W₀.1)) :
    ∃ g ∈ 𝓘.ideal W₀, ∃ (c : ℕ) (N : X.Opens) (hN : N ≤ f ⁻¹ᵁ W₀.1) (_ : x ∈ N)
      (u ui : Γ(X, N)) (d : ι → Γ(X, N)),
      u * ui = 1 ∧ f.appLE W₀.1 N hN a = u * f.appLE W₀.1 N hN g ^ c ∧
      ∀ i, gen i ∈ 𝓘.ideal W₀ → f.appLE W₀.1 N hN (gen i) = d i * f.appLE W₀.1 N hN g := by
  set R := X.presheaf.stalk x
  let φ : Γ(Y, W₀.1) →+* R := (X.presheaf.germ (f ⁻¹ᵁ W₀.1) x hx).hom.comp (f.app W₀.1).hom
  have hφ : ∀ s, φ s = X.presheaf.germ (f ⁻¹ᵁ W₀.1) x hx (f.app W₀.1 s) := fun _ => rfl
  have hmap : (𝓘.ideal W₀).map φ = IsLocalRing.maximalIdeal R := by
    rw [← h𝓘, AlgebraicGeometry.IdealSheafData.stalk_comap,
      AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ 𝓘 _ W₀ hx, Ideal.map_map]
    congr 1
    ext s
    exact (Scheme.Hom.germ_stalkMap_apply f W₀.1 x hx s).symm
  obtain ⟨g, hg, hspan⟩ := exists_mem_span_eq_maximalIdeal_of_map_eq φ _ hmap
  have hirr : Irreducible (φ g) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hspan.symm
  obtain ⟨c, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hirr
  have hd : ∀ i, gen i ∈ 𝓘.ideal W₀ → ∃ d' : R, φ (gen i) = d' * φ g := by
    intro i hi
    have : φ (gen i) ∈ Ideal.span {φ g} := hspan ▸ hmap ▸ Ideal.mem_map_of_mem φ hi
    obtain ⟨d', hd'⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨d', hd'.symm⟩
  let d' : ι → R := fun i => if hi : gen i ∈ 𝓘.ideal W₀ then (hd i hi).choose else 0
  let r : Option (Option ι) → R := fun o => match o with
    | none => (u' : R)
    | some none => ((u'⁻¹ : Rˣ) : R)
    | some (some i) => d' i
  obtain ⟨U, hU, hxU, s, hs⟩ := exists_open_germ_eq_family x r (f ⁻¹ᵁ W₀.1) hx
  let F₁ : Option (Option ι) → Γ(X, U) := fun o => match o with
    | none => s none * s (some none)
    | some none => f.appLE W₀.1 U hU a
    | some (some i) => if gen i ∈ 𝓘.ideal W₀ then f.appLE W₀.1 U hU (gen i) else 0
  let F₂ : Option (Option ι) → Γ(X, U) := fun o => match o with
    | none => 1
    | some none => s none * f.appLE W₀.1 U hU g ^ c
    | some (some i) => if gen i ∈ 𝓘.ideal W₀ then s (some (some i)) * f.appLE W₀.1 U hU g else 0
  have hgerm : ∀ z, X.presheaf.germ (f ⁻¹ᵁ W₀.1) x hx (f.app W₀.1 z) =
      X.presheaf.germ U x hxU (f.appLE W₀.1 U hU z) := by
    intro z
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
  obtain ⟨N, hNU, hxN, hN⟩ := exists_open_eq_family x hxU F₁ F₂ (by
    rintro (_ | _ | i)
    · simp only [F₁, F₂, map_mul, map_one, hs, r, Units.mul_inv]
    · simp only [F₁, F₂, map_mul, map_pow, hs, r, ← hgerm, ← hφ]
      exact hu'
    · simp only [F₁, F₂]
      split_ifs with hi
      · simp only [map_mul, hs, r, d', dif_pos hi, ← hgerm, ← hφ]
        exact (hd i hi).choose_spec
      · rfl)
  have hres : ∀ z, X.presheaf.map (homOfLE hNU).op (f.appLE W₀.1 U hU z) =
      f.appLE W₀.1 N (hNU.trans hU) z := by
    intro z
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  refine ⟨g, hg, c, N, hNU.trans hU, hxN, X.presheaf.map (homOfLE hNU).op (s none),
    X.presheaf.map (homOfLE hNU).op (s (some none)),
    fun i => X.presheaf.map (homOfLE hNU).op (s (some (some i))), ?_, ?_, fun i hi => ?_⟩
  · simpa only [F₁, F₂, map_mul, map_one] using hN none
  · simpa only [F₁, F₂, map_mul, map_pow, hres] using hN (some none)
  · simpa only [F₁, F₂, if_pos hi, map_mul, hres] using hN (some (some i))

/-- Two sections restricting to the same section on an open equal to the preimage agree there. -/
private lemma app_eq_of_appLE_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (hV : V = f ⁻¹ᵁ U) (x y : Γ(Y, U)) (h : f.appLE U V hV.le x = f.appLE U V hV.le y) :
    f.app U x = f.app U y := by
  subst hV
  rwa [Scheme.Hom.appLE_eq_app] at h

/-- **Finitely many sections descend to one stage.** -/
public lemma Model.exists_section_family {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀) (j : J)
    (V : ((M.stage h₀).obj j).left.Opens) (hV : IsCompact (V : Set ((M.stage h₀).obj j).left))
    {ι' : Type*} [Finite ι'] (a : ι' → Γ((X.obj j).left, M.cmp h₀ j ⁻¹ᵁ V)) :
    ∃ (S₁ : CoefficientModels.FGSub k₀ K) (h₁ : S₀ ≤ S₁)
      (a₁ : ι' → Γ(((M.stage (h₀.trans h₁)).obj j).left, M.stageCmp h₀ h₁ j ⁻¹ᵁ V)),
      ∀ i, (M.cmp (h₀.trans h₁) j).appLE (M.stageCmp h₀ h₁ j ⁻¹ᵁ V) (M.cmp h₀ j ⁻¹ᵁ V)
        (by rw [← Scheme.Hom.comp_preimage, M.cmp_stageCmp]) (a₁ i) = a i := by
  classical
  have := Fintype.ofFinite ι'
  choose S h a' ha' using fun i => M.exists_section' h₀ j V hV (a i)
  obtain ⟨T, hT⟩ := Finset.exists_le (insert S₀ (Finset.univ.image S))
  have h₀T : S₀ ≤ T := hT _ (Finset.mem_insert_self _ _)
  have hST : ∀ i, S i ≤ T := fun i =>
    hT _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  refine ⟨T, h₀T, fun i => (M.stageCmp (h₀.trans (h i)) (hST i) j).appLE
    (M.stageCmp h₀ (h i) j ⁻¹ᵁ V) (M.stageCmp h₀ h₀T j ⁻¹ᵁ V)
    (by rw [← Scheme.Hom.comp_preimage, M.stageCmp_comp]) (a' i), fun i => ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, ← ha' i]
  exact appLE_eq_of_eq (M.cmp_stageCmp (h₀.trans (h i)) (hST i) j) _ _ _ _ _

/-- **Finitely many equalities of sections descend to one stage.** -/
private lemma Model.exists_section_eq_family {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (j : J) (V : ((M.stage h₀).obj j).left.Opens)
    (hV : IsCompact (V : Set ((M.stage h₀).obj j).left)) {ι' : Type*} [Finite ι']
    (x y : ι' → Γ(((M.stage h₀).obj j).left, V))
    (hxy : ∀ i, (M.cmp h₀ j).app V (x i) = (M.cmp h₀ j).app V (y i)) :
    ∃ (S₁ : CoefficientModels.FGSub k₀ K) (h₁ : S₀ ≤ S₁),
      ∀ i, (M.stageCmp h₀ h₁ j).app V (x i) = (M.stageCmp h₀ h₁ j).app V (y i) := by
  classical
  have := Fintype.ofFinite ι'
  choose S h hS using fun i => M.exists_section_eq h₀ j V hV (x i) (y i) (hxy i)
  obtain ⟨T, hT⟩ := Finset.exists_le (insert S₀ (Finset.univ.image S))
  have h₀T : S₀ ≤ T := hT _ (Finset.mem_insert_self _ _)
  have hST : ∀ i, S i ≤ T := fun i =>
    hT _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  refine ⟨T, h₀T, fun i => ?_⟩
  rw [← M.stageCmp_comp h₀ (h i) (hST i) j, Scheme.Hom.comp_app]
  exact congrArg (fun z => (Scheme.Hom.app (M.stageCmp (h₀.trans (h i)) (hST i) j) _) z) (hS i)

/-- Restrictions along two consecutive stage comparisons compose. -/
private lemma Model.stageCmp_appLE_comp {S₀ S₁ S : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (h₁ : S₀ ≤ S₁) (h₂ : S₁ ≤ S) (j : J) (U : ((M.stage h₀).obj j).left.Opens)
    (U' : ((M.stage (h₀.trans h₁)).obj j).left.Opens)
    (W : ((M.stage (h₀.trans (h₁.trans h₂))).obj j).left.Opens)
    (e₁ : U' ≤ M.stageCmp h₀ h₁ j ⁻¹ᵁ U) (e₂ : W ≤ M.stageCmp (h₀.trans h₁) h₂ j ⁻¹ᵁ U')
    (e : W ≤ M.stageCmp h₀ (h₁.trans h₂) j ⁻¹ᵁ U) (z : Γ(((M.stage h₀).obj j).left, U)) :
    (M.stageCmp (h₀.trans h₁) h₂ j).appLE U' W e₂ ((M.stageCmp h₀ h₁ j).appLE U U' e₁ z) =
      (M.stageCmp h₀ (h₁.trans h₂) j).appLE U W e z := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact appLE_eq_of_eq (M.stageCmp_comp h₀ h₁ h₂ j) _ _ _ _ _

/-- Restriction along a stage comparison followed by the comparison with `K`. -/
private lemma Model.cmp_appLE_comp {S₀ S : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (h : S₀ ≤ S) (j : J) (U : ((M.stage h₀).obj j).left.Opens)
    (U' : ((M.stage (h₀.trans h)).obj j).left.Opens) (W : (X.obj j).left.Opens)
    (e₁ : U' ≤ M.stageCmp h₀ h j ⁻¹ᵁ U) (e₂ : W ≤ M.cmp (h₀.trans h) j ⁻¹ᵁ U')
    (e : W ≤ M.cmp h₀ j ⁻¹ᵁ U) (z : Γ(((M.stage h₀).obj j).left, U)) :
    (M.cmp (h₀.trans h) j).appLE U' W e₂ ((M.stageCmp h₀ h j).appLE U U' e₁ z) =
      (M.cmp h₀ j).appLE U W e z := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact appLE_eq_of_eq (M.cmp_stageCmp h₀ h j) _ _ _ _ _

/-- The comparison morphism between two stages of the model is affine. -/
public lemma Model.isAffineHom_stageCmp {S₀ S : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (h : S₀ ≤ S) (j : J) : IsAffineHom (M.stageCmp h₀ h j) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom)
    ((M.isCartesian_stageCmp h₀ h).isPullback j).flip inferInstance

/-- Every vertex of a stage of the model is locally Noetherian. -/
public lemma Model.isLocallyNoetherian_stage {S : CoefficientModels.FGSub k₀ K} (h : M.R ≤ S)
    (j : J) :
    IsLocallyNoetherian ((M.stage h).obj j).left :=
  have : Algebra.FiniteType k₀ S.1 := (Subalgebra.fg_iff_finiteType _).mp S.2
  have : IsNoetherianRing S.1 := Algebra.FiniteType.isNoetherianRing k₀ S.1
  have := (M.finitePresentation_stage h j).1
  LocallyOfFiniteType.isLocallyNoetherian ((M.stage h).obj j).hom

open Classical in
include hint in
/-- **Local equations along a prime divisor descend to a stage.** For a prime divisor `E` of a
normal vertex with a model `𝓘` at a stage and a section `a` of the model over an open through the
generic point of `E`, nonzero over `K`, there are a later stage and an affine open `W` through the
generic point on which `𝓘` is generated by one section `π` and `a = u π^c` with `u` a unit. -/
private lemma Model.exists_stage_localData {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (j : J)
    [IsLocallyNoetherian (X.obj j).left] [IsNormal (X.obj j).left]
    (𝓘 : ((M.stage h₀).obj j).left.IdealSheafData) (E : Mori.PrimeDivisor (X.obj j).left)
    (hE : 𝓘.comap (M.cmp h₀ j) = E.idealSheaf) (V : ((M.stage h₀).obj j).left.Opens)
    (a : Γ(((M.stage h₀).obj j).left, V)) (hηV : M.cmp h₀ j E.genericPoint ∈ V)
    (ha : (X.obj j).left.presheaf.germ (M.cmp h₀ j ⁻¹ᵁ V) E.genericPoint hηV
      ((M.cmp h₀ j).app V a) ≠ 0) :
    ∃ (S₃ : CoefficientModels.FGSub k₀ K) (h₃ : S₀ ≤ S₃)
      (W : ((M.stage (h₀.trans h₃)).obj j).left.affineOpens)
      (hW : W.1 ≤ M.stageCmp h₀ h₃ j ⁻¹ᵁ V) (π u ui : Γ(((M.stage (h₀.trans h₃)).obj j).left, W.1))
      (c : ℕ), (𝓘.comap (M.stageCmp h₀ h₃ j)).ideal W = Ideal.span {π} ∧ u * ui = 1 ∧
      (M.stageCmp h₀ h₃ j).appLE V W.1 hW a = u * π ^ c ∧
      M.cmp (h₀.trans h₃) j E.genericPoint ∈ W.1 := by
  have := hint j
  have := M.isLocallyNoetherian_stage h₀ j
  haveI := E.isDiscreteValuationRing_localRing
  haveI := E.integral
  -- an affine open of the stage through the generic point, inside `V`
  obtain ⟨W₀, hW₀a, hηW₀, hW₀V⟩ := exists_isAffineOpen_mem_and_subset hηV
  let W₀' : ((M.stage h₀).obj j).left.affineOpens := ⟨W₀, hW₀a⟩
  have hW₀V' : W₀ ≤ V := hW₀V
  have : IsNoetherianRing Γ(((M.stage h₀).obj j).left, W₀) :=
    IsLocallyNoetherian.component_noetherian W₀'
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (𝓘.ideal W₀') : (𝓘.ideal W₀').FG)
  let a₀ := ((M.stage h₀).obj j).left.presheaf.map (homOfLE hW₀V').op a
  have h𝓘 : IdealSheafData.stalk (𝓘.comap (M.cmp h₀ j)) E.genericPoint =
      IsLocalRing.maximalIdeal ((X.obj j).left.presheaf.stalk E.genericPoint) := by
    rw [hE]
    exact IdealSheafData.stalk_subschemeι_genericPoint_eq_maximalIdeal E.idealSheaf
  have ha₀ : (X.obj j).left.presheaf.germ (M.cmp h₀ j ⁻¹ᵁ W₀'.1) E.genericPoint hηW₀
      ((M.cmp h₀ j).app W₀'.1 a₀) ≠ 0 := by
    have e : (M.cmp h₀ j).app W₀ a₀ = (X.obj j).left.presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono _ hW₀V')).op ((M.cmp h₀ j).app V a) := by
      simp only [a₀]
      rw [← CommRingCat.comp_apply, Scheme.Hom.naturality]
      rfl
    change (X.obj j).left.presheaf.germ (M.cmp h₀ j ⁻¹ᵁ W₀) E.genericPoint hηW₀
      ((M.cmp h₀ j).app W₀ a₀) ≠ 0
    rw [e]
    erw [TopCat.Presheaf.germ_res_apply]
    exact ha
  obtain ⟨g, hg, c, N, hN, hηN, u, ui, d, hu, hga, hgd⟩ := exists_localData (M.cmp h₀ j)
    E.genericPoint 𝓘 h𝓘 W₀' hηW₀ a₀ ha₀ (fun i : s => (i : Γ(((M.stage h₀).obj j).left, W₀)))
  -- the open `N` from a stage
  obtain ⟨N', hN'a, hηN', hN'N⟩ := exists_isAffineOpen_mem_and_subset hηN
  obtain ⟨S₁, h₁, H₁⟩ := M.exists_open j N' hN'a.isCompact
  let T₁ : CoefficientModels.FGSub k₀ K := ⟨S₀.1 ⊔ S₁.1, S₀.2.sup S₁.2⟩
  have h₀₁ : S₀ ≤ T₁ := le_sup_left (a := S₀.1)
  have h₁₁ : S₁ ≤ T₁ := le_sup_right (b := S₁.1)
  obtain ⟨V₁, -, hV₁⟩ := H₁ T₁ h₁₁
  let V₁' : ((M.stage (h₀.trans h₀₁)).obj j).left.Opens := V₁ ⊓ M.stageCmp h₀ h₀₁ j ⁻¹ᵁ W₀
  have hηV₁' : M.cmp (h₀.trans h₀₁) j E.genericPoint ∈ V₁' := by
    refine ⟨?_, ?_⟩
    · exact (show E.genericPoint ∈ M.cmp (h₁.trans h₁₁) j ⁻¹ᵁ V₁ by rwa [hV₁])
    · change (M.cmp (h₀.trans h₀₁) j ≫ M.stageCmp h₀ h₀₁ j) E.genericPoint ∈ W₀
      rw [M.cmp_stageCmp]
      exact hηW₀
  obtain ⟨W₁, hW₁a, hηW₁, hW₁V₁⟩ := exists_isAffineOpen_mem_and_subset hηV₁'
  have hN''N : M.cmp (h₀.trans h₀₁) j ⁻¹ᵁ W₁ ≤ N := fun x hx => hN'N (by
    have : x ∈ M.cmp (h₁.trans h₁₁) j ⁻¹ᵁ V₁ := (hW₁V₁ hx).1
    rwa [hV₁] at this)
  have hW₁W₀ : W₁ ≤ M.stageCmp h₀ h₀₁ j ⁻¹ᵁ W₀ := fun x hx => (hW₁V₁ hx).2
  -- descend the sections
  let res := (X.obj j).left.presheaf.map (homOfLE hN''N).op
  let fam : Option (Option s) → Γ((X.obj j).left, M.cmp (h₀.trans h₀₁) j ⁻¹ᵁ W₁) := fun o =>
    match o with
    | none => res u
    | some none => res ui
    | some (some i) => res (d i)
  obtain ⟨S₂, h₁₂, x₂, hx₂⟩ := M.exists_section_family (h₀.trans h₀₁) j W₁ hW₁a.isCompact fam
  let W₂ := M.stageCmp (h₀.trans h₀₁) h₁₂ j ⁻¹ᵁ W₁
  have hW₂₀ : W₂ ≤ M.stageCmp h₀ (h₀₁.trans h₁₂) j ⁻¹ᵁ W₀ := by
    rw [← M.stageCmp_comp h₀ h₀₁ h₁₂ j, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ hW₁W₀
  have hW₂V : W₂ ≤ M.stageCmp h₀ (h₀₁.trans h₁₂) j ⁻¹ᵁ V :=
    hW₂₀.trans (Scheme.Hom.preimage_mono _ hW₀V')
  let g₂ := (M.stageCmp h₀ (h₀₁.trans h₁₂) j).appLE W₀ W₂ hW₂₀ g
  let P₁ : Option (Option s) → Γ(((M.stage ((h₀.trans h₀₁).trans h₁₂)).obj j).left, W₂) :=
    fun o => match o with
    | none => x₂ none * x₂ (some none)
    | some none => (M.stageCmp h₀ (h₀₁.trans h₁₂) j).appLE V W₂ hW₂V a
    | some (some i) => (M.stageCmp h₀ (h₀₁.trans h₁₂) j).appLE W₀ W₂ hW₂₀ i
  let P₂ : Option (Option s) → Γ(((M.stage ((h₀.trans h₀₁).trans h₁₂)).obj j).left, W₂) :=
    fun o => match o with
    | none => 1
    | some none => x₂ none * g₂ ^ c
    | some (some i) => x₂ (some (some i)) * g₂
  have hN₂ : M.cmp (h₀.trans h₀₁) j ⁻¹ᵁ W₁ = M.cmp ((h₀.trans h₀₁).trans h₁₂) j ⁻¹ᵁ W₂ := by
    rw [← Scheme.Hom.comp_preimage, M.cmp_stageCmp]
  have hK : ∀ o, (M.cmp ((h₀.trans h₀₁).trans h₁₂) j).app W₂ (P₁ o) =
      (M.cmp ((h₀.trans h₀₁).trans h₁₂) j).app W₂ (P₂ o) := by
    have hxo : ∀ o, (M.cmp ((h₀.trans h₀₁).trans h₁₂) j).appLE W₂ _ hN₂.le (x₂ o) = fam o :=
      hx₂
    have hz : ∀ (U : ((M.stage h₀).obj j).left.Opens)
        (hU : W₂ ≤ M.stageCmp h₀ (h₀₁.trans h₁₂) j ⁻¹ᵁ U) (hU' : M.cmp (h₀.trans h₀₁) j ⁻¹ᵁ W₁ ≤
          M.cmp h₀ j ⁻¹ᵁ U) (z : Γ(((M.stage h₀).obj j).left, U)),
        (M.cmp ((h₀.trans h₀₁).trans h₁₂) j).appLE W₂ _ hN₂.le
          ((M.stageCmp h₀ (h₀₁.trans h₁₂) j).appLE U W₂ hU z) =
        (M.cmp h₀ j).appLE U _ hU' z :=
      fun U hU hU' z => M.cmp_appLE_comp h₀ (h₀₁.trans h₁₂) j U W₂ _ hU hN₂.le hU' z
    have hN''W₀ : M.cmp (h₀.trans h₀₁) j ⁻¹ᵁ W₁ ≤ M.cmp h₀ j ⁻¹ᵁ W₀ := hN''N.trans hN
    have hN''V : M.cmp (h₀.trans h₀₁) j ⁻¹ᵁ W₁ ≤ M.cmp h₀ j ⁻¹ᵁ V :=
      hN''W₀.trans (Scheme.Hom.preimage_mono _ hW₀V')
    have hresK : ∀ z, res ((M.cmp h₀ j).appLE W₀ N hN z) = (M.cmp h₀ j).appLE W₀ _ hN''W₀ z := by
      intro z
      simp only [res]
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    have ha₀K : (M.cmp h₀ j).appLE W₀ N hN a₀ = (M.cmp h₀ j).appLE V N (hN.trans
        (Scheme.Hom.preimage_mono _ hW₀V')) a := by
      simp only [a₀]
      rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    have haK : (M.cmp h₀ j).appLE V _ hN''V a =
        res ((M.cmp h₀ j).appLE V N (hN.trans (Scheme.Hom.preimage_mono _ hW₀V')) a) := by
      simp only [res]
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    intro o
    apply app_eq_of_appLE_eq _ W₂ _ hN₂
    rcases o with _ | _ | i
    · change (M.cmp ((h₀.trans h₀₁).trans h₁₂) j).appLE W₂ _ hN₂.le (x₂ none * x₂ (some none)) =
        (M.cmp ((h₀.trans h₀₁).trans h₁₂) j).appLE W₂ _ hN₂.le 1
      rw [map_mul, hxo, hxo, map_one]
      simp only [fam]
      rw [← map_mul, hu, map_one]
    · simp only [P₁, P₂, map_mul, map_pow, hxo, fam, g₂, hz _ _ hN''V, hz _ _ hN''W₀, haK,
        ← ha₀K, ← hresK]
      rw [hga, map_mul, map_pow]
    · have hi : (i : Γ(((M.stage h₀).obj j).left, W₀)) ∈ 𝓘.ideal W₀' :=
        hs ▸ Submodule.subset_span i.2
      simp only [P₁, P₂, map_mul, hxo, fam, g₂, hz _ _ hN''W₀, ← hresK]
      rw [hgd i hi, map_mul]
  -- descend the equalities
  have := M.isAffineHom_stageCmp (h₀.trans h₀₁) h₁₂ j
  have hW₂a : IsAffineOpen W₂ := hW₁a.preimage _
  obtain ⟨S₃, h₂₃, hS⟩ := M.exists_section_eq_family ((h₀.trans h₀₁).trans h₁₂) j W₂
    hW₂a.isCompact P₁ P₂ hK
  have := M.isAffineHom_stageCmp ((h₀.trans h₀₁).trans h₁₂) h₂₃ j
  let W : ((M.stage (h₀.trans (h₀₁.trans (h₁₂.trans h₂₃)))).obj j).left.affineOpens :=
    ⟨M.stageCmp ((h₀.trans h₀₁).trans h₁₂) h₂₃ j ⁻¹ᵁ W₂, hW₂a.preimage _⟩
  have hWW₀ : W.1 ≤ M.stageCmp h₀ (h₀₁.trans (h₁₂.trans h₂₃)) j ⁻¹ᵁ W₀ := by
    rw [← M.stageCmp_comp h₀ (h₀₁.trans h₁₂) h₂₃ j, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ hW₂₀
  have hWV : W.1 ≤ M.stageCmp h₀ (h₀₁.trans (h₁₂.trans h₂₃)) j ⁻¹ᵁ V :=
    hWW₀.trans (Scheme.Hom.preimage_mono _ hW₀V')
  let φ₃ := M.stageCmp ((h₀.trans h₀₁).trans h₁₂) h₂₃ j
  have hcomp : ∀ (U : ((M.stage h₀).obj j).left.Opens)
      (hU : W₂ ≤ M.stageCmp h₀ (h₀₁.trans h₁₂) j ⁻¹ᵁ U)
      (hU' : W.1 ≤ M.stageCmp h₀ (h₀₁.trans (h₁₂.trans h₂₃)) j ⁻¹ᵁ U)
      (z : Γ(((M.stage h₀).obj j).left, U)),
      (M.stageCmp ((h₀.trans h₀₁).trans h₁₂) h₂₃ j).app W₂
        ((M.stageCmp h₀ (h₀₁.trans h₁₂) j).appLE U W₂ hU z) =
        (M.stageCmp h₀ (h₀₁.trans (h₁₂.trans h₂₃)) j).appLE U W.1 hU' z := by
    intro U hU hU' z
    rw [Scheme.Hom.app_eq_appLE]
    exact M.stageCmp_appLE_comp h₀ (h₀₁.trans h₁₂) h₂₃ j U W₂ W.1 hU le_rfl hU' z
  refine ⟨S₃, h₀₁.trans (h₁₂.trans h₂₃), W, hWV,
    (M.stageCmp h₀ (h₀₁.trans (h₁₂.trans h₂₃)) j).appLE W₀ W.1 hWW₀ g,
    φ₃.app W₂ (x₂ none), φ₃.app W₂ (x₂ (some none)), c, ?_, ?_, ?_, ?_⟩
  · rw [Scheme.IdealSheafData.ideal_comap_of_isAffineOpen 𝓘 _ W₀' W hWW₀]
    change Ideal.map _ (𝓘.ideal W₀') = _
    rw [← hs]
    change Ideal.map _ (Ideal.span (s : Set Γ(((M.stage h₀).obj j).left, W₀))) = _
    rw [Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨i, hi, rfl⟩
      have := hS (some (some ⟨i, hi⟩))
      simp only [P₁, P₂, map_mul, g₂] at this
      rw [hcomp W₀ hW₂₀ hWW₀, hcomp W₀ hW₂₀ hWW₀] at this
      change _ ∈ Ideal.span _
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_singleton_le_iff_mem, ← Ideal.map_span]
      have hg' : g ∈ Ideal.span (s : Set Γ(((M.stage h₀).obj j).left, W₀)) := by
        change g ∈ Submodule.span _ _
        rw [hs]
        exact hg
      exact Ideal.mem_map_of_mem _ hg'
  · simpa only [P₁, P₂, map_mul, map_one] using hS none
  · have := hS (some none)
    simp only [P₁, P₂, map_mul, map_pow, g₂] at this
    rwa [hcomp V hW₂V hWV, hcomp W₀ hW₂₀ hWW₀] at this
  · change (M.cmp (h₀.trans (h₀₁.trans (h₁₂.trans h₂₃))) j ≫ φ₃) E.genericPoint ∈ W₂
    rw [M.cmp_stageCmp]
    change (M.cmp ((h₀.trans h₀₁).trans h₁₂) j ≫ M.stageCmp (h₀.trans h₀₁) h₁₂ j)
      E.genericPoint ∈ W₁
    rw [M.cmp_stageCmp]
    exact hηW₁

/-- The generic germ of a restriction is the generic germ of the original section. -/
public lemma germToFunctionField_app_appLE {F Y Y' : Scheme.{u}} [IsIntegral F] (g : F ⟶ Y')
    (φ : Y' ⟶ Y) (f : F ⟶ Y) (hf : g ≫ φ = f) (V : Y.Opens) (W : Y'.Opens) (e : W ≤ φ ⁻¹ᵁ V)
    (a : Γ(Y, V)) (h₁ : Nonempty (g ⁻¹ᵁ W)) (h₂ : Nonempty (f ⁻¹ᵁ V)) :
    F.germToFunctionField (g ⁻¹ᵁ W) (g.app W (φ.appLE V W e a)) =
      F.germToFunctionField (f ⁻¹ᵁ V) (f.app V a) := by
  subst hf
  have h : g.app W (φ.appLE V W e a) = (g ≫ φ).appLE V (g ⁻¹ᵁ W)
      ((Scheme.Hom.preimage_mono g e).trans (Scheme.Hom.comp_preimage g φ V).ge) a := by
    rw [Scheme.Hom.app_eq_appLE g, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  rw [h, Scheme.Hom.appLE, CommRingCat.comp_apply]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

include hint in
/-- **Orders along a prime divisor spread to the fibres.** For a section `a` of a normal vertex
at a stage, nonzero at the generic point of a prime divisor `E` with a model `𝓘`, on every fibre
over every late stage the order of `a` along a prime divisor with ideal sheaf the fibre of `𝓘`
is the order of `a` along `E`. -/
private lemma Model.exists_ord_eq {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀) (j : J)
    [IsLocallyNoetherian (X.obj j).left] [IsNormal (X.obj j).left]
    (𝓘 : ((M.stage h₀).obj j).left.IdealSheafData) (E : Mori.PrimeDivisor (X.obj j).left)
    (hE : 𝓘.comap (M.cmp h₀ j) = E.idealSheaf) (V : ((M.stage h₀).obj j).left.Opens)
    (a : Γ(((M.stage h₀).obj j).left, V)) (hηV : M.cmp h₀ j E.genericPoint ∈ V)
    (ha : (X.obj j).left.presheaf.germ (M.cmp h₀ j ⁻¹ᵁ V) E.genericPoint hηV
      ((M.cmp h₀ j).app V a) ≠ 0) :
    ∃ (S₂ : CoefficientModels.FGSub k₀ K) (h₂ : S₀ ≤ S₂), ∀ (S : CoefficientModels.FGSub k₀ K)
      (h : S₂ ≤ S) (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      ∀ [IsIntegral ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).left]
        [IsLocallyNoetherian ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).left],
      topologicalKrullDim ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).left =
        topologicalKrullDim (X.obj j).left →
      ∀ Γ : Mori.PrimeDivisor ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).left,
        Γ.idealSheaf = 𝓘.comap (M.fibreMap h₀ (h₂.trans h) t j) →
        ∃ _ : M.fibreMap h₀ (h₂.trans h) t j Γ.genericPoint ∈ V,
          ∀ [Nonempty (M.fibreMap h₀ (h₂.trans h) t j ⁻¹ᵁ V)] [Nonempty (M.cmp h₀ j ⁻¹ᵁ V)],
          Scheme.ord (((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj
              j).left.germToFunctionField
            (M.fibreMap h₀ (h₂.trans h) t j ⁻¹ᵁ V) ((M.fibreMap h₀ (h₂.trans h) t j).app V a))
            Γ.genericPoint =
          Scheme.ord ((X.obj j).left.germToFunctionField (M.cmp h₀ j ⁻¹ᵁ V) ((M.cmp h₀ j).app V a))
            E.genericPoint := by
  have := hint j
  obtain ⟨S₃, h₃, W, hW, π, u, ui, c, hI, hu, ha', hηW⟩ :=
    M.exists_stage_localData hint h₀ j 𝓘 E hE V a hηV ha
  set I₃ := 𝓘.comap (M.stageCmp h₀ h₃ j)
  -- the value over `K`
  have hEI : E.idealSheaf = I₃.comap (M.cmp (h₀.trans h₃) j) := by
    rw [← Scheme.IdealSheafData.comap_comp, M.cmp_stageCmp, hE]
  have hK : ∀ [Nonempty (M.cmp h₀ j ⁻¹ᵁ V)], Scheme.ord ((X.obj j).left.germToFunctionField
      (M.cmp h₀ j ⁻¹ᵁ V) ((M.cmp h₀ j).app V a)) E.genericPoint = c := by
    intro _
    have : Nonempty (M.cmp (h₀.trans h₃) j ⁻¹ᵁ W.1) := ⟨⟨_, hηW⟩⟩
    have := ord_germToFunctionField_of_ideal_eq_span (M.cmp (h₀.trans h₃) j) I₃ W hI hu ha' E
      hEI hηW
    rwa [germToFunctionField_app_appLE _ _ _ (M.cmp_stageCmp h₀ h₃ j) V W.1 hW a ‹_› ‹_›] at this
  -- the generic points of the fibre primes lie over `W`
  let J₃ := I₃ ⊔ Scheme.IdealSheafData.vanishingIdeal W.1.compl
  have hK2 : ∀ x ∈ ((J₃.comap (M.cmp (h₀.trans h₃) j)).support : Set (X.obj j).left),
      ((2 : ℕ) : ℕ∞) ≤ Order.coheight x := by
    intro x hx
    simp only [J₃, Scheme.IdealSheafData.comap_sup, Scheme.IdealSheafData.support_sup,
      ← hEI] at hx
    obtain ⟨hxE, hxW⟩ := hx
    rw [Scheme.IdealSheafData.support_comap] at hxW
    change M.cmp (h₀.trans h₃) j x ∈ SetLike.coe
      (Scheme.IdealSheafData.vanishingIdeal W.1.compl).support at hxW
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hxW
    have hne : x ≠ E.genericPoint := fun h => hxW (h ▸ hηW)
    have hle : x ≤ E.genericPoint := by
      rw [Scheme.le_iff_specializes, specializes_iff_mem_closure,
        ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hxE
    have hlt : x < E.genericPoint := lt_of_le_not_ge hle fun h' => hne
      ((Scheme.le_iff_specializes.mp hle).antisymm (Scheme.le_iff_specializes.mp h')).eq.symm
    have := Order.coheight_add_one_le hlt
    rw [E.coheight_genericPoint] at this
    exact_mod_cast this
  obtain ⟨S₄, h₄, H₄⟩ := M.exists_le_coheight_comap hint (h₀.trans h₃) j J₃ 2 hK2
  refine ⟨S₄, h₃.trans h₄, fun S h L _ t _ _ hdim Γ hΓ => ?_⟩
  have hfm : M.fibreMap (h₀.trans h₃) (h₄.trans h) t j ≫ M.stageCmp h₀ h₃ j =
      M.fibreMap h₀ ((h₃.trans h₄).trans h) t j := M.fibreMap_comp h₀ h₃ (h₄.trans h) t j
  have hΓ' : Γ.idealSheaf = I₃.comap (M.fibreMap (h₀.trans h₃) (h₄.trans h) t j) := by
    rw [← Scheme.IdealSheafData.comap_comp, hfm, hΓ]
  have hηW' : M.fibreMap (h₀.trans h₃) (h₄.trans h) t j Γ.genericPoint ∈ W.1 := by
    by_contra hn
    have hmem : Γ.genericPoint ∈ ((J₃.comap (M.fibreMap (h₀.trans h₃) (h₄.trans h) t j)).support :
        Set _) := by
      simp only [J₃, Scheme.IdealSheafData.comap_sup, Scheme.IdealSheafData.support_sup, ← hΓ']
      refine ⟨?_, ?_⟩
      · change Γ.genericPoint ∈ Γ.support
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
      · rw [Scheme.IdealSheafData.support_comap]
        change _ ∈ SetLike.coe (Scheme.IdealSheafData.vanishingIdeal W.1.compl).support
        rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
        exact hn
    have := H₄ S h L t inferInstance hdim _ hmem
    rw [Γ.coheight_genericPoint] at this
    exact absurd this (by decide)
  have hηV' : M.fibreMap h₀ ((h₃.trans h₄).trans h) t j Γ.genericPoint ∈ V := by
    rw [← hfm]
    exact hW hηW'
  refine ⟨hηV', fun {_ _} => ?_⟩
  have : Nonempty (M.fibreMap (h₀.trans h₃) (h₄.trans h) t j ⁻¹ᵁ W.1) := ⟨⟨_, hηW'⟩⟩
  have := ord_germToFunctionField_of_ideal_eq_span _ I₃ W hI hu ha' Γ hΓ' hηW'
  rw [germToFunctionField_app_appLE _ _ _ hfm V W.1 hW a ‹_› ⟨⟨_, hηV'⟩⟩] at this
  exact this.trans hK.symm

/-- A prime divisor whose generic point lies on another prime divisor is that prime divisor. -/
private lemma primeDivisor_eq_of_genericPoint_mem {F : Scheme.{u}} (Γ P : Mori.PrimeDivisor F)
    (h : Γ.genericPoint ∈ P.support) : Γ = P := by
  have hle : Γ.genericPoint ≤ P.genericPoint := by
    rw [Scheme.le_iff_specializes, specializes_iff_mem_closure,
      ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact h
  have heq : Γ.genericPoint = P.genericPoint := by
    by_contra hne
    have hlt : Γ.genericPoint < P.genericPoint := lt_of_le_not_ge hle fun h' => hne
      ((Scheme.le_iff_specializes.mp hle).antisymm (Scheme.le_iff_specializes.mp h')).eq.symm
    have := Order.coheight_add_one_le hlt
    rw [Γ.coheight_genericPoint, P.coheight_genericPoint] at this
    exact absurd this (by decide)
  refine AlgebraicGeometry.PrimeDivisor.eq_of_support_eq ?_
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact congrArg (fun x => closure ({x} : Set F)) heq

/-- On an integral normal locally Noetherian scheme, a section whose generic germ has order zero
along every prime divisor through a point is a unit at that point. -/
private lemma isUnit_germ_of_forall_ord_eq_zero {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X]
    [IsNormal X] {U : X.Opens} [Nonempty U] (s : Γ(X, U)) (hs : X.germToFunctionField U s ≠ 0)
    {x : X} (hx : x ∈ U)
    (h : ∀ Γ : Mori.PrimeDivisor X, x ∈ Γ.support →
      X.ord (X.germToFunctionField U s) Γ.genericPoint = 0) :
    IsUnit (X.presheaf.germ U x hx s) := by
  obtain ⟨r, hr, hrs⟩ := Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero x hs h
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField _ hx] at hrs
  rwa [← IsFractionRing.injective (X.presheaf.stalk x) X.functionField hrs]

include hint in
/-- **Units off finitely many prime divisors spread to the fibres.** A section `a` of a normal
vertex at a stage, nonzero over `K`, whose orders along the prime divisors meeting its domain
vanish off a finite set `T` with models `𝓘`, is a unit at every point of a late fibre over the
domain and off the fibres of the models. -/
private lemma Model.exists_isUnit_germ {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀) (j : J)
    [IsLocallyNoetherian (X.obj j).left] [IsNormal (X.obj j).left]
    (V : ((M.stage h₀).obj j).left.Opens) (a : Γ(((M.stage h₀).obj j).left, V))
    [Nonempty (M.cmp h₀ j ⁻¹ᵁ V)]
    (ha : (X.obj j).left.germToFunctionField (M.cmp h₀ j ⁻¹ᵁ V) ((M.cmp h₀ j).app V a) ≠ 0)
    (T : Finset (Mori.PrimeDivisor (X.obj j).left))
    (𝓘 : Mori.PrimeDivisor (X.obj j).left → ((M.stage h₀).obj j).left.IdealSheafData)
    (h𝓘 : ∀ E ∈ T, (𝓘 E).comap (M.cmp h₀ j) = E.idealSheaf)
    (hT : ∀ E : Mori.PrimeDivisor (X.obj j).left, (E.support ∩ M.cmp h₀ j ⁻¹ᵁ V).Nonempty →
      Scheme.ord ((X.obj j).left.germToFunctionField (M.cmp h₀ j ⁻¹ᵁ V) ((M.cmp h₀ j).app V a))
        E.genericPoint ≠ 0 → E ∈ T) :
    ∃ (S₂ : CoefficientModels.FGSub k₀ K) (h₂ : S₀ ≤ S₂), ∀ (S : CoefficientModels.FGSub k₀ K)
      (h : S₂ ≤ S) (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)) (x)
      (hx : x ∈ M.fibreMap h₀ (h₂.trans h) t j ⁻¹ᵁ V),
      (∀ E ∈ T, M.fibreMap h₀ (h₂.trans h) t j x ∉ ((𝓘 E).support : Set _)) →
      IsUnit ((((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).left).presheaf.germ
        _ x hx ((M.fibreMap h₀ (h₂.trans h) t j).app V a)) := by
  have := hint j
  let C₁ : TopologicalSpace.Closeds ((M.stage h₀).obj j).left :=
    (((M.stage h₀).obj j).left.basicOpen a).compl
  let C₂ : TopologicalSpace.Closeds ((M.stage h₀).obj j).left :=
    V.compl ⊔ T.sup fun E => (𝓘 E).support
  have hK : M.cmp h₀ j ⁻¹' C₁ ⊆ M.cmp h₀ j ⁻¹' C₂ := by
    intro x hx
    by_contra hx₂
    simp only [C₂, Set.mem_preimage, TopologicalSpace.Closeds.coe_sup, Set.mem_union,
      not_or, TopologicalSpace.Opens.coe_compl, Set.mem_compl_iff, not_not] at hx₂
    obtain ⟨hxV, hxT⟩ := hx₂
    apply hx
    change M.cmp h₀ j x ∈ ((M.stage h₀).obj j).left.basicOpen a
    rw [← Scheme.Hom.mem_preimage, Scheme.preimage_basicOpen]
    refine (Scheme.mem_basicOpen'' _ _ x).mpr ⟨hxV, ?_⟩
    refine isUnit_germ_of_forall_ord_eq_zero _ ha hxV fun E hxE => ?_
    by_contra hne
    have hET := hT E ⟨x, hxE, hxV⟩ hne
    apply hxT
    rw [TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion]
    refine Set.mem_iUnion₂.mpr ⟨E, hET, ?_⟩
    have hx' : x ∈ ((𝓘 E).comap (M.cmp h₀ j)).support := by
      rwa [h𝓘 E hET]
    rw [Scheme.IdealSheafData.support_comap] at hx'
    exact hx'
  obtain ⟨S₂, h₂, H⟩ := M.exists_preimage_subset h₀ j C₁ C₂ hK
  refine ⟨S₂, h₂, fun S h L _ t x hx hxT => ?_⟩
  have hxV : M.fibreMap h₀ (h₂.trans h) t j x ∈ V := hx
  have hx₁ : x ∉ M.fibreMap h₀ (h₂.trans h) t j ⁻¹' C₁ := by
    intro hx₁
    have := H S h L t hx₁
    simp only [C₂, Set.mem_preimage, TopologicalSpace.Closeds.coe_sup, Set.mem_union,
      TopologicalSpace.Opens.coe_compl, Set.mem_compl_iff] at this
    rcases this with h₁ | h₁
    · exact h₁ hxV
    · rw [TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion] at h₁
      obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp h₁
      exact hxT E hE hxE
  simp only [C₁, Set.mem_preimage, TopologicalSpace.Opens.coe_compl, Set.mem_compl_iff,
    not_not] at hx₁
  have hx₁' : x ∈ M.fibreMap h₀ (h₂.trans h) t j ⁻¹ᵁ ((M.stage h₀).obj j).left.basicOpen a := hx₁
  rw [Scheme.preimage_basicOpen] at hx₁'
  obtain ⟨_, hu⟩ := (Scheme.mem_basicOpen'' _ _ x).mp hx₁'
  exact hu

/-- A point of a prime divisor other than its generic point has coheight at least two. -/
private lemma two_le_coheight_of_mem_support {F : Scheme.{u}} (E : Mori.PrimeDivisor F) {x : F}
    (hx : x ∈ E.support) (hne : x ≠ E.genericPoint) : ((2 : ℕ) : ℕ∞) ≤ Order.coheight x := by
  have hle : x ≤ E.genericPoint := by
    rw [Scheme.le_iff_specializes, specializes_iff_mem_closure,
      ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hx
  have hlt : x < E.genericPoint := lt_of_le_not_ge hle fun h' => hne
    ((Scheme.le_iff_specializes.mp hle).antisymm (Scheme.le_iff_specializes.mp h')).eq.symm
  have := Order.coheight_add_one_le hlt
  rw [E.coheight_genericPoint] at this
  exact_mod_cast this

/-- The generic point of a prime divisor lies in its support. -/
public lemma genericPoint_mem_support {F : Scheme.{u}} (E : Mori.PrimeDivisor F) :
    E.genericPoint ∈ E.support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

include hint in
/-- **Distinct prime divisors have distinct fibres.** -/
private lemma Model.exists_comap_ne {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀) (j : J)
    {E E' : Mori.PrimeDivisor (X.obj j).left} (hEE' : E ≠ E')
    {𝓘 𝓘' : ((M.stage h₀).obj j).left.IdealSheafData}
    (h𝓘 : 𝓘.comap (M.cmp h₀ j) = E.idealSheaf) (h𝓘' : 𝓘'.comap (M.cmp h₀ j) = E'.idealSheaf) :
    ∃ (S₂ : CoefficientModels.FGSub k₀ K) (h₂ : S₀ ≤ S₂), ∀ (S : CoefficientModels.FGSub k₀ K)
      (h : S₂ ≤ S) (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      IsIntegral ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).left →
      topologicalKrullDim ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).left =
        topologicalKrullDim (X.obj j).left →
      ∀ Γ : Mori.PrimeDivisor ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).left,
        Γ.idealSheaf = 𝓘.comap (M.fibreMap h₀ (h₂.trans h) t j) →
        Γ.idealSheaf ≠ 𝓘'.comap (M.fibreMap h₀ (h₂.trans h) t j) := by
  have hK : ∀ x ∈ (((𝓘 ⊔ 𝓘').comap (M.cmp h₀ j)).support : Set (X.obj j).left),
      ((2 : ℕ) : ℕ∞) ≤ Order.coheight x := by
    intro x hx
    simp only [Scheme.IdealSheafData.comap_sup, Scheme.IdealSheafData.support_sup, h𝓘,
      h𝓘'] at hx
    obtain ⟨hxE, hxE'⟩ := hx
    refine two_le_coheight_of_mem_support E hxE fun hxη => hEE' ?_
    exact primeDivisor_eq_of_genericPoint_mem E E' (hxη ▸ hxE')
  obtain ⟨S₂, h₂, H⟩ := M.exists_le_coheight_comap hint h₀ j (𝓘 ⊔ 𝓘') 2 hK
  refine ⟨S₂, h₂, fun S h L _ t hI hd Γ hΓ hΓ' => ?_⟩
  have hmem : Γ.genericPoint ∈ (((𝓘 ⊔ 𝓘').comap (M.fibreMap h₀ (h₂.trans h) t j)).support :
      Set _) := by
    simp only [Scheme.IdealSheafData.comap_sup, Scheme.IdealSheafData.support_sup, ← hΓ, ← hΓ']
    exact ⟨genericPoint_mem_support Γ, genericPoint_mem_support Γ⟩
  have := H S h L t hI hd _ hmem
  rw [Γ.coheight_genericPoint] at this
  exact absurd this (by decide)

open Classical in
include hint in
/-- **Orders of a section spread to the fibres.** Let `a` be a section of a normal vertex at a
stage over an open `V`, nonzero over `K`, and `T` a finite set of prime divisors, with models `𝓘`,
containing every prime divisor meeting `V` along which `a` has nonzero order. On every fibre over
every late stage on which the models of `T` are prime divisors, the order of `a` along a prime
divisor meeting `V` is the order of `a` along the prime divisor of `T` it is the fibre of, and
zero if it is the fibre of none. -/
public lemma Model.exists_ord_section {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀) (j : J)
    [IsLocallyNoetherian (X.obj j).left] [IsNormal (X.obj j).left]
    (V : ((M.stage h₀).obj j).left.Opens) (a : Γ(((M.stage h₀).obj j).left, V))
    [Nonempty (M.cmp h₀ j ⁻¹ᵁ V)]
    (ha : (X.obj j).left.germToFunctionField (M.cmp h₀ j ⁻¹ᵁ V) ((M.cmp h₀ j).app V a) ≠ 0)
    (T : Finset (Mori.PrimeDivisor (X.obj j).left))
    (𝓘 : Mori.PrimeDivisor (X.obj j).left → ((M.stage h₀).obj j).left.IdealSheafData)
    (h𝓘 : ∀ E ∈ T, (𝓘 E).comap (M.cmp h₀ j) = E.idealSheaf)
    (hT : ∀ E : Mori.PrimeDivisor (X.obj j).left, (E.support ∩ M.cmp h₀ j ⁻¹ᵁ V).Nonempty →
      Scheme.ord ((X.obj j).left.germToFunctionField (M.cmp h₀ j ⁻¹ᵁ V) ((M.cmp h₀ j).app V a))
        E.genericPoint ≠ 0 → E ∈ T) :
    EvAbove S₀ fun S hS => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1))
      [IsIntegral ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left]
      [IsLocallyNoetherian ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left],
      topologicalKrullDim ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left =
        topologicalKrullDim (X.obj j).left →
      (∀ E ∈ T, ∃ Ps : Mori.PrimeDivisor ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left,
        Ps.idealSheaf = (𝓘 E).comap (M.fibreMap h₀ hS t j)) →
      ∀ [Nonempty (M.fibreMap h₀ hS t j ⁻¹ᵁ V)],
      ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left.germToFunctionField
          (M.fibreMap h₀ hS t j ⁻¹ᵁ V) ((M.fibreMap h₀ hS t j).app V a) ≠ 0 ∧
      ∀ Γ : Mori.PrimeDivisor ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left,
        (Γ.support ∩ M.fibreMap h₀ hS t j ⁻¹ᵁ V).Nonempty →
        Scheme.ord (((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left.germToFunctionField
            (M.fibreMap h₀ hS t j ⁻¹ᵁ V) ((M.fibreMap h₀ hS t j).app V a)) Γ.genericPoint =
          ∑ E ∈ T, if Γ.idealSheaf = (𝓘 E).comap (M.fibreMap h₀ hS t j) then
            Scheme.ord ((X.obj j).left.germToFunctionField (M.cmp h₀ j ⁻¹ᵁ V)
              ((M.cmp h₀ j).app V a)) E.genericPoint else 0 := by
  have := hint j
  -- units off the fibres of `T`
  have e₁ : EvAbove S₀ fun S hS => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1))
      (x) (hx : x ∈ M.fibreMap h₀ hS t j ⁻¹ᵁ V),
      (∀ E ∈ T, M.fibreMap h₀ hS t j x ∉ ((𝓘 E).support : Set _)) →
      IsUnit ((((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left).presheaf.germ
        _ x hx ((M.fibreMap h₀ hS t j).app V a)) := by
    obtain ⟨S₂, h₂, H⟩ := M.exists_isUnit_germ hint h₀ j V a ha T 𝓘 h𝓘 hT
    exact ⟨S₂, h₂, fun S h L _ t => H S h L t⟩
  -- orders along the fibres of `T`
  have e₂ : EvAbove S₀ fun S hS => ∀ E ∈ T, ∀ (L : Type u) [Field L]
      (t : Spec (.of L) ⟶ Spec (.of S.1))
      [IsIntegral ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left]
      [IsLocallyNoetherian ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left],
      topologicalKrullDim ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left =
        topologicalKrullDim (X.obj j).left →
      ∀ Γ : Mori.PrimeDivisor ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left,
        Γ.idealSheaf = (𝓘 E).comap (M.fibreMap h₀ hS t j) →
        (Γ.support ∩ M.fibreMap h₀ hS t j ⁻¹ᵁ V).Nonempty →
        ∀ [Nonempty (M.fibreMap h₀ hS t j ⁻¹ᵁ V)],
        Scheme.ord (((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left.germToFunctionField
            (M.fibreMap h₀ hS t j ⁻¹ᵁ V) ((M.fibreMap h₀ hS t j).app V a)) Γ.genericPoint =
          Scheme.ord ((X.obj j).left.germToFunctionField (M.cmp h₀ j ⁻¹ᵁ V)
            ((M.cmp h₀ j).app V a)) E.genericPoint := by
    refine EvAbove.forall_finset T fun E hE => ?_
    by_cases hEV : (E.support ∩ M.cmp h₀ j ⁻¹ᵁ V).Nonempty
    · have hηV : M.cmp h₀ j E.genericPoint ∈ V := (E.genericPoint_mem_iff _).mpr hEV
      have hgerm : (X.obj j).left.presheaf.germ (M.cmp h₀ j ⁻¹ᵁ V) E.genericPoint hηV
          ((M.cmp h₀ j).app V a) ≠ 0 := by
        intro h0
        apply ha
        rw [← Scheme.algebraMap_germ_eq_germToFunctionField _
          (show E.genericPoint ∈ M.cmp h₀ j ⁻¹ᵁ V from hηV), h0, map_zero]
      obtain ⟨S₂, h₂, H⟩ := M.exists_ord_eq hint h₀ j (𝓘 E) E (h𝓘 E hE) V a hηV hgerm
      refine ⟨S₂, h₂, fun S h L _ t _ _ hd Γ hΓ _ _ => ?_⟩
      obtain ⟨-, H'⟩ := H S h L t hd Γ hΓ
      exact H'
    · have hK : M.cmp h₀ j ⁻¹' ((𝓘 E).support : Set _) ⊆ M.cmp h₀ j ⁻¹' (V.compl : Set _) := by
        intro x hx hxV
        apply hEV
        refine ⟨x, ?_, hxV⟩
        have hx' : x ∈ ((𝓘 E).comap (M.cmp h₀ j)).support := by
          rwa [Scheme.IdealSheafData.support_comap]
        rwa [h𝓘 E hE] at hx'
      obtain ⟨S₂, h₂, H⟩ := M.exists_preimage_subset h₀ j _ _ hK
      refine ⟨S₂, h₂, fun S h L _ t _ _ hd Γ hΓ hΓV _ => ?_⟩
      exfalso
      obtain ⟨x, hxΓ, hxV⟩ := hΓV
      have hx' : x ∈ ((𝓘 E).comap (M.fibreMap h₀ (h₂.trans h) t j)).support := by
        rwa [← hΓ]
      rw [Scheme.IdealSheafData.support_comap] at hx'
      exact H S h L t hx' hxV
  -- distinct members of `T` have distinct fibres
  have e₃ : EvAbove S₀ fun S hS => ∀ E ∈ T, ∀ E' ∈ T, E ≠ E' → ∀ (L : Type u) [Field L]
      (t : Spec (.of L) ⟶ Spec (.of S.1)),
      IsIntegral ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left →
      topologicalKrullDim ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left =
        topologicalKrullDim (X.obj j).left →
      ∀ Γ : Mori.PrimeDivisor ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left,
        Γ.idealSheaf = (𝓘 E).comap (M.fibreMap h₀ hS t j) →
        Γ.idealSheaf ≠ (𝓘 E').comap (M.fibreMap h₀ hS t j) := by
    refine EvAbove.forall_finset T fun E hE => EvAbove.forall_finset T fun E' hE' => ?_
    by_cases hEE' : E = E'
    · exact (EvAbove.true S₀).mono fun _ _ _ h => absurd hEE' h
    · obtain ⟨S₂, h₂, H⟩ := M.exists_comap_ne hint h₀ j hEE' (h𝓘 E hE) (h𝓘 E' hE')
      exact ⟨S₂, h₂, fun S h _ L _ t hI hd Γ hΓ => H S h L t hI hd Γ hΓ⟩
  refine ((e₁.and e₂).and e₃).mono fun S hS H L _ t _ _ hd hsp _ => ?_
  obtain ⟨⟨H₁, H₂⟩, H₃⟩ := H
  have key : ∀ x (hx : x ∈ M.fibreMap h₀ hS t j ⁻¹ᵁ V),
      (∀ E ∈ T, x ∉ (((𝓘 E).comap (M.fibreMap h₀ hS t j)).support : Set _)) →
      IsUnit ((((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left).presheaf.germ
        _ x hx ((M.fibreMap h₀ hS t j).app V a)) := by
    intro x hx hxT
    refine H₁ L t x hx fun E hE hxE => hxT E hE ?_
    rw [Scheme.IdealSheafData.support_comap]
    exact hxE
  constructor
  · have hη : genericPoint ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left ∈
        M.fibreMap h₀ hS t j ⁻¹ᵁ V :=
      ((genericPoint_spec _).mem_open_set_iff (M.fibreMap h₀ hS t j ⁻¹ᵁ V).isOpen).mpr
        (by simpa using ‹Nonempty (M.fibreMap h₀ hS t j ⁻¹ᵁ V)›)
    have hnot : ∀ E ∈ T, genericPoint ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left ∉
        (((𝓘 E).comap (M.fibreMap h₀ hS t j)).support : Set _) := by
      intro E hE hmem
      obtain ⟨Ps, hPs⟩ := hsp E hE
      rw [← hPs] at hmem
      have h1 : genericPoint ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left ≤
          Ps.genericPoint := by
        rw [Scheme.le_iff_specializes, specializes_iff_mem_closure,
          ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact hmem
      have h2 : Ps.genericPoint ≤
          genericPoint ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left :=
        Scheme.le_iff_specializes.mpr ((genericPoint_spec _).specializes trivial)
      have heq := ((Scheme.le_iff_specializes.mp h1).antisymm
        (Scheme.le_iff_specializes.mp h2)).eq
      have hc := Ps.coheight_genericPoint
      rw [heq] at hc
      have h0 : Order.coheight
          (genericPoint ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left) = 0 :=
        Order.coheight_eq_zero.mpr fun b _ =>
          Scheme.le_iff_specializes.mpr ((genericPoint_spec _).specializes trivial)
      rw [h0] at hc
      exact absurd hc (by decide)
    exact (key _ hη hnot).ne_zero
  · intro Γ hΓV
    have hηΓ : Γ.genericPoint ∈ M.fibreMap h₀ hS t j ⁻¹ᵁ V := (Γ.genericPoint_mem_iff _).mpr hΓV
    by_cases hsome : ∃ E ∈ T, Γ.idealSheaf = (𝓘 E).comap (M.fibreMap h₀ hS t j)
    · obtain ⟨E, hE, hΓE⟩ := hsome
      rw [Finset.sum_eq_single E (fun E' hE' hne => if_neg (H₃ E hE E' hE' (Ne.symm hne) L t
        inferInstance hd Γ hΓE)) (fun h => absurd hE h), if_pos hΓE]
      exact H₂ E hE L t hd Γ hΓE hΓV
    · push Not at hsome
      rw [Finset.sum_eq_zero (fun E hE => if_neg (hsome E hE))]
      have hnot : ∀ E ∈ T, Γ.genericPoint ∉
          (((𝓘 E).comap (M.fibreMap h₀ hS t j)).support : Set _) := by
        intro E hE hmem
        obtain ⟨Ps, hPs⟩ := hsp E hE
        rw [← hPs] at hmem
        have hΓP := primeDivisor_eq_of_genericPoint_mem Γ Ps hmem
        exact hsome E hE (hΓP ▸ hPs)
      have hu := key _ hηΓ hnot
      rw [← Scheme.algebraMap_germ_eq_germToFunctionField _ hηΓ]
      exact Γ.ord_algebraMap_of_isUnit hu

/-- **Étale coordinates give a basis of the differentials**, for an étale map from a polynomial
ring over any base. -/
private lemma exists_basis_kaehler_of_etale {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {n : ℕ} (g : MvPolynomial (Fin n) R →ₐ[R] A) (hg : g.toRingHom.Etale) :
    ∃ b : Module.Basis (Fin n) A Ω[A⁄R], ∀ i,
      b i = KaehlerDifferential.D R A (g (MvPolynomial.X i)) := by
  let : Algebra (MvPolynomial (Fin n) R) A := g.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) A :=
    IsScalarTower.of_algebraMap_eq' (by ext a; exact (g.commutes a).symm)
  have : Algebra.Etale (MvPolynomial (Fin n) R) A := hg
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale R (MvPolynomial (Fin n) R) A
  refine ⟨hbc.basis (KaehlerDifferential.mvPolynomialBasis R (Fin n)), fun i => ?_⟩
  simp only [IsBaseChange.basis_apply, KaehlerDifferential.mvPolynomialBasis_apply,
    KaehlerDifferential.map_D]
  rfl

/-- A basis of differentials transfers along a pushout of rings. -/
private lemma exists_basis_kaehler_of_isPushout {R L A B : Type*} [CommRing R] [CommRing L]
    [CommRing A]
    [CommRing B] [Algebra R L] [Algebra R A] [Algebra R B] [Algebra L B] [Algebra A B]
    [IsScalarTower R L B] [IsScalarTower R A B] [Algebra.IsPushout R L A B] {ι : Type*}
    {a : ι → A} (b : Module.Basis ι A Ω[A⁄R]) (hb : ∀ i, b i = KaehlerDifferential.D R A (a i)) :
    ∃ b' : Module.Basis ι B Ω[B⁄L], ∀ i,
      b' i = KaehlerDifferential.D L B (algebraMap A B (a i)) := by
  refine ⟨(b.baseChange B).map (KaehlerDifferential.tensorKaehlerEquiv R L A B), fun i => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, hb,
    KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul]

/-- A basis of differentials transfers along a formally étale extension. -/
private lemma exists_basis_kaehler_of_formallyEtale {L B T : Type*} [CommRing L] [CommRing B]
    [CommRing T] [Algebra L B] [Algebra L T] [Algebra B T] [IsScalarTower L B T]
    [Algebra.FormallyEtale B T] {ι : Type*} {x : ι → B} (b : Module.Basis ι B Ω[B⁄L])
    (hb : ∀ i, b i = KaehlerDifferential.D L B (x i)) :
    ∃ b' : Module.Basis ι T Ω[T⁄L], ∀ i,
      b' i = KaehlerDifferential.D L T (algebraMap B T (x i)) := by
  refine ⟨(b.baseChange T).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale L B T),
    fun i => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, hb, KaehlerDifferential.map_D]

/-- `(V.ι ≫ q)` on global sections, through `Γ(V, ⊤) ≅ Γ(Y, V)`. -/
private lemma ι_comp_appTop_topIso_hom {Y Z : Scheme.{u}} (q : Y ⟶ Z) (V : Y.Opens) :
    (V.ι ≫ q).appTop ≫ V.topIso.hom = q.appLE ⊤ V le_top := by
  rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  erw [← Functor.map_comp]
  rfl

/-- `f ∣_ U` on global sections, through `Γ(U, ⊤) ≅ Γ(Y, U)`. -/
private lemma appTop_morphismRestrict_topIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (f ∣_ U).appTop ≫ (f ⁻¹ᵁ U).topIso.hom = U.topIso.hom ≫ f.app U := by
  have h : U.topIso.inv ≫ (f ∣_ U).appTop = f.app U ≫ (f ⁻¹ᵁ U).topIso.inv := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
      Iso.inv_hom_id_assoc, Scheme.Hom.appLE]
    simp
  rw [← Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The fibre of a chart is a pushout of rings**: for a pullback square `F = Y ×_{Spec R} Spec L`
and an affine open `V` of `Y`, `Γ(F, fst⁻¹ V) = L ⊗_{Γ(Spec R)} Γ(Y, V)`. -/
private lemma isPushout_sections_of_isPullback {Y F : Scheme.{u}} {R : CommRingCat.{u}} {L : Type u}
    [Field L] {q : Y ⟶ Spec R} {t : Spec (.of L) ⟶ Spec R} {fst : F ⟶ Y}
    {snd : F ⟶ Spec (.of L)} (hpb : IsPullback fst snd q t) (V : Y.Opens) (hV : IsAffineOpen V) :
    IsPushout (t.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom) (q.appLE ⊤ V le_top)
      ((Scheme.ΓSpecIso (.of L)).inv ≫ snd.appLE ⊤ (fst ⁻¹ᵁ V) le_top) (fst.app V) := by
  have sq : IsPullback (fst ∣_ V) ((fst ⁻¹ᵁ V).ι ≫ snd) (V.ι ≫ q) t :=
    (AlgebraicGeometry.isPullback_morphismRestrict fst V).paste_vert hpb
  have : IsAffine V.toScheme := hV
  have hpo := (isPushout_appTop_of_isPullback sq).flip
  refine hpo.of_iso (Iso.refl _) (Scheme.ΓSpecIso (.of L)) V.topIso (fst ⁻¹ᵁ V).topIso
    (by simp) ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.id_comp, ι_comp_appTop_topIso_hom]
  · rw [Iso.hom_inv_id_assoc, ← ι_comp_appTop_topIso_hom]
  · exact appTop_morphismRestrict_topIso_hom fst V

/-- **Étale coordinates of a chart give bases of the differentials on its fibres.** Let
`F = Y ×_{Spec R} Spec L` and `V` an affine open of `Y` with an étale map
`Γ(Spec R)[X₁, …, Xₙ] → Γ(Y, V)` over `Γ(Spec R)`. At every point `p` of `F` over `V`, the
differentials of the pulled-back coordinates form a basis of `Ω_{𝒪_{F,p}/L}`. -/
public lemma exists_basis_kaehler_stalk_of_isPullback {Y F : Scheme.{u}} {R : CommRingCat.{u}}
    {L : Type u} [Field L] {q : Y ⟶ Spec R} {t : Spec (.of L) ⟶ Spec R} {fst : F ⟶ Y}
    {snd : F ⟶ Spec (.of L)} (hpb : IsPullback fst snd q t) (V : Y.Opens) (hV : IsAffineOpen V)
    {n : ℕ} (g : MvPolynomial (Fin n) Γ(Spec R, ⊤) →+* Γ(Y, V)) (hg : g.Etale)
    (hgC : g.comp MvPolynomial.C = (q.appLE ⊤ V le_top).hom) (p : F) (hp : p ∈ fst ⁻¹ᵁ V) :
    letI := MMP.Mori.stalkAlgebra snd p
    ∃ b : Module.Basis (Fin n) (F.presheaf.stalk p) Ω[F.presheaf.stalk p⁄L], ∀ i,
      b i = KaehlerDifferential.D L _
        (F.presheaf.germ (fst ⁻¹ᵁ V) p hp (fst.app V (g (MvPolynomial.X i)))) := by
  letI : Algebra Γ(Spec R, ⊤) Γ(Y, V) := (q.appLE ⊤ V le_top).hom.toAlgebra
  letI : Algebra Γ(Spec R, ⊤) L := (t.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom).hom.toAlgebra
  letI : Algebra L Γ(F, fst ⁻¹ᵁ V) := MMP.Mori.sectionAlgebra snd (fst ⁻¹ᵁ V)
  letI : Algebra Γ(Y, V) Γ(F, fst ⁻¹ᵁ V) := (fst.app V).hom.toAlgebra
  letI : Algebra Γ(Spec R, ⊤) Γ(F, fst ⁻¹ᵁ V) :=
    (q.appLE ⊤ V le_top ≫ fst.app V).hom.toAlgebra
  have : IsScalarTower Γ(Spec R, ⊤) Γ(Y, V) Γ(F, fst ⁻¹ᵁ V) := IsScalarTower.of_algebraMap_eq' rfl
  have hpo := isPushout_sections_of_isPullback hpb V hV
  have : IsScalarTower Γ(Spec R, ⊤) L Γ(F, fst ⁻¹ᵁ V) := IsScalarTower.of_algebraMap_eq' (by
    have := congrArg CommRingCat.Hom.hom hpo.w
    simp only [CommRingCat.hom_comp] at this
    change (q.appLE ⊤ V le_top ≫ fst.app V).hom = _
    rw [CommRingCat.hom_comp, ← this]
    rfl)
  have : Algebra.IsPushout Γ(Spec R, ⊤) L Γ(Y, V) Γ(F, fst ⁻¹ᵁ V) :=
    CommRingCat.isPushout_iff_isPushout.mp hpo
  let gA : MvPolynomial (Fin n) Γ(Spec R, ⊤) →ₐ[Γ(Spec R, ⊤)] Γ(Y, V) :=
    { toRingHom := g
      commutes' := fun r => congrArg (fun φ => φ r) hgC }
  obtain ⟨bA, hbA⟩ := exists_basis_kaehler_of_etale gA hg
  obtain ⟨bB, hbB⟩ := exists_basis_kaehler_of_isPushout (L := L) (B := Γ(F, fst ⁻¹ᵁ V)) bA hbA
  have : IsAffineHom fst := MorphismProperty.of_isPullback (P := @IsAffineHom) hpb.flip
      inferInstance
  have hFa : IsAffineOpen (fst ⁻¹ᵁ V) := hV.preimage fst
  letI := MMP.Mori.stalkAlgebra snd p
  letI : Algebra Γ(F, fst ⁻¹ᵁ V) (F.presheaf.stalk p) := F.presheaf.algebra_section_stalk ⟨p, hp⟩
  have : IsScalarTower L Γ(F, fst ⁻¹ᵁ V) (F.presheaf.stalk p) :=
    MMP.Mori.isScalarTower_section_stalk snd (fst ⁻¹ᵁ V) ⟨p, hp⟩
  have : IsLocalization.AtPrime (F.presheaf.stalk p) (hFa.primeIdealOf ⟨p, hp⟩).asIdeal :=
    hFa.isLocalization_stalk ⟨p, hp⟩
  have : Algebra.FormallyEtale Γ(F, fst ⁻¹ᵁ V) (F.presheaf.stalk p) :=
    Algebra.FormallyEtale.of_isLocalization (hFa.primeIdealOf ⟨p, hp⟩).asIdeal.primeCompl
  obtain ⟨b, hb⟩ := exists_basis_kaehler_of_formallyEtale (T := F.presheaf.stalk p) bB hbB
  exact ⟨b, hb⟩

/-- **The wedge of a basis of differentials at a point generates the top forms there**, with
nonzero image in the rational top forms. -/
public lemma span_ιMulti_D_and_ne_zero {L : Type u} [Field L] {F : Scheme.{u}} [IsIntegral F]
    (sF : F ⟶ Spec (.of L)) (x : F) {n : ℕ} (y : Fin n → F.presheaf.stalk x)
    (b : letI := MMP.Mori.stalkAlgebra sF x
      Module.Basis (Fin n) (F.presheaf.stalk x) Ω[F.presheaf.stalk x⁄L])
    (hb : letI := MMP.Mori.stalkAlgebra sF x
      ∀ i, b i = KaehlerDifferential.D L (F.presheaf.stalk x) (y i)) :
    letI := MMP.Mori.stalkAlgebra sF x
    letI := MMP.Mori.functionFieldAlgebra sF
    haveI := MMP.Mori.isScalarTower_stalk_functionField sF x
    Submodule.span (F.presheaf.stalk x)
        {exteriorPower.ιMulti (F.presheaf.stalk x) n fun i =>
          KaehlerDifferential.D L (F.presheaf.stalk x) (y i)} = ⊤ ∧
      MMP.Mori.topFormsMap L (F.presheaf.stalk x) F.functionField n
        (exteriorPower.ιMulti (F.presheaf.stalk x) n fun i =>
          KaehlerDifferential.D L (F.presheaf.stalk x) (y i)) ≠ 0 := by
  letI := MMP.Mori.stalkAlgebra sF x
  letI := MMP.Mori.functionFieldAlgebra sF
  haveI := MMP.Mori.isScalarTower_stalk_functionField sF x
  have hspan : Submodule.span (F.presheaf.stalk x)
      (Set.range fun i => KaehlerDifferential.D L (F.presheaf.stalk x) (y i)) = ⊤ := by
    rw [← b.span_eq]
    congr 1
    ext w
    simp [hb]
  have hσ := ExteriorAlgebra.span_singleton_ιMulti_eq_top _ hspan
  refine ⟨hσ, ?_⟩
  have : Module.Free (F.presheaf.stalk x) Ω[F.presheaf.stalk x⁄L] := .of_basis b
  have : Module.Finite (F.presheaf.stalk x) Ω[F.presheaf.stalk x⁄L] := .of_basis b
  have hK : Module.finrank F.functionField Ω[F.functionField⁄L] = n :=
    (MMP.Mori.finrank_kaehlerDifferential_eq_of_isFractionRing (A := F.presheaf.stalk x)).trans
      (by rw [Module.finrank_eq_card_basis b, Fintype.card_fin])
  have : FiniteDimensional F.functionField Ω[F.functionField⁄L] := Module.Finite.of_basis
    (b.ofIsLocalizedModule F.functionField (nonZeroDivisors (F.presheaf.stalk x))
      (KaehlerDifferential.map L L (F.presheaf.stalk x) F.functionField))
  have := MMP.Mori.nontrivial_exteriorPower_of_finrank_eq L F.functionField hK
  exact MMP.Mori.topFormsMap_ne_zero_of_span_eq_top hσ

/-- **The order of a top form against a basis of differentials.** If the differentials of `y`
form a basis of `Ω_{𝒪_{F,Γ}/L}` at the generic point of a prime divisor `Γ`, then the order along
`Γ` of `c · dy₁ ∧ ⋯ ∧ dyₙ` is the order of `c`. -/
private lemma ordForm_toPluriForms_eq_ord {L : Type u} [Field L] {F : Scheme.{u}} [IsIntegral F]
    [IsLocallyNoetherian F] (sF : F ⟶ Spec (.of L)) (Γ : Mori.PrimeDivisor F) {n : ℕ}
    (y : Fin n → F.presheaf.stalk Γ.genericPoint)
    (b : letI := MMP.Mori.stalkAlgebra sF Γ.genericPoint
      Module.Basis (Fin n) (F.presheaf.stalk Γ.genericPoint)
        Ω[F.presheaf.stalk Γ.genericPoint⁄L])
    (hb : letI := MMP.Mori.stalkAlgebra sF Γ.genericPoint
      ∀ i, b i = KaehlerDifferential.D L (F.presheaf.stalk Γ.genericPoint) (y i))
    (c : F.functionField) (ω : Mori.RationalTopForms sF n)
    (hω : letI := MMP.Mori.functionFieldAlgebra sF
      ω = c • exteriorPower.ιMulti F.functionField n fun i =>
        KaehlerDifferential.D L F.functionField
          (algebraMap (F.presheaf.stalk Γ.genericPoint) F.functionField (y i))) :
    Γ.ordForm (ω.toPluriForms sF) = F.ord c Γ.genericPoint := by
  letI := MMP.Mori.stalkAlgebra sF Γ.genericPoint
  letI := MMP.Mori.functionFieldAlgebra sF
  haveI := MMP.Mori.isScalarTower_stalk_functionField sF Γ.genericPoint
  obtain ⟨hσ, h0⟩ := span_ιMulti_D_and_ne_zero sF Γ.genericPoint y b hb
  rw [Γ.ordForm_eq _ hσ h0]
  congr 1
  have hb1 : MMP.Mori.topFormsBasis _ hσ h0 () = exteriorPower.ιMulti F.functionField n fun i =>
      KaehlerDifferential.D L F.functionField
        (algebraMap (F.presheaf.stalk Γ.genericPoint) F.functionField (y i)) := by
    rw [MMP.Mori.topFormsBasis_apply, MMP.Mori.topFormsMap_ιMulti]
    simp only [KaehlerDifferential.map_D]
  have hpf : ω.toPluriForms sF =
      MMP.Fourfold.formPow (c • MMP.Mori.topFormsBasis _ hσ h0 ()) 1 := by
    rw [hb1, ← hω]
    rfl
  unfold MMP.Mori.formCoeff
  rw [hpf, MMP.Fourfold.formPow_smul, pow_one]
  exact MMP.Fourfold.repr_smul_formPow _ 1 c

/-- A relation between wedges of differentials pushes forward along algebra maps over a
change of base. -/
public lemma ιMulti_D_algebraMap_eq_smul {R L A K : Type*} [CommRing R] [CommRing L] [CommRing A]
    [CommRing K] [Algebra R L] [Algebra R A] [Algebra A K] [Algebra L K] [Algebra R K]
    [IsScalarTower R A K] [IsScalarTower R L K] {n : ℕ} (z w : Fin n → A) (h₀ : A)
    (hrel : exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D R A (z i)) =
      h₀ • exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D R A (w i))) :
    exteriorPower.ιMulti K n (fun i => KaehlerDifferential.D L K (algebraMap A K (z i))) =
      algebraMap A K h₀ •
        exteriorPower.ιMulti K n (fun i => KaehlerDifferential.D L K (algebraMap A K (w i))) := by
  let Ψ : Ω[A⁄R] [⋀^Fin n]→ₗ[A] ⋀[K]^n Ω[K⁄L] :=
    ({ ((exteriorPower.ιMulti K n (M := Ω[K⁄L])).toMultilinearMap.restrictScalars A) with
        map_eq_zero_of_eq' := fun v _ _ h hij =>
          (exteriorPower.ιMulti K n (M := Ω[K⁄L])).map_eq_zero_of_eq v h hij } :
        Ω[K⁄L] [⋀^Fin n]→ₗ[A] ⋀[K]^n Ω[K⁄L]).compLinearMap (KaehlerDifferential.map R L A K)
  have := congrArg (exteriorPower.alternatingMapLinearEquiv Ψ) hrel
  rw [map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti] at this
  simp only [Ψ, AlternatingMap.compLinearMap_apply, KaehlerDifferential.map_D] at this
  rwa [← algebraMap_smul K h₀] at this

/-- The two ways from the base of a pullback square to the function field of the fibre agree. -/
public lemma appLE_comp_germToFunctionField_of_isPullback {Y F : Scheme.{u}} {R : CommRingCat.{u}}
    {L : Type u} [Field L] {q : Y ⟶ Spec R} {t : Spec (.of L) ⟶ Spec R} {fst : F ⟶ Y}
    {snd : F ⟶ Spec (.of L)} (hpb : IsPullback fst snd q t) [IsIntegral F] (W : Y.Opens)
    [Nonempty (fst ⁻¹ᵁ W)] :
    q.appLE ⊤ W le_top ≫ fst.app W ≫ F.germToFunctionField (fst ⁻¹ᵁ W) =
      (t.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom) ≫ (Scheme.ΓSpecIso (.of L)).inv ≫ snd.appTop ≫
        F.presheaf.germ ⊤ (genericPoint F) (TopologicalSpace.Opens.mem_top _) := by
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  have h : q.appLE ⊤ W le_top ≫ fst.app W =
      (fst ≫ q).appTop ≫ F.presheaf.map (homOfLE (le_top : fst ⁻¹ᵁ W ≤ ⊤)).op := by
    dsimp only [Scheme.Hom.appLE]
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.Hom.naturality]
    rfl
  rw [← Category.assoc, h, hpb.w, Scheme.Hom.comp_appTop, Category.assoc, Category.assoc]
  congr 2
  exact TopCat.Presheaf.germ_res _ _ _ _

/-- **The order of a chart form along a prime divisor of a fibre.** Let `F = Y ×_{Spec R} Spec L`,
`V` an affine chart of `Y` with étale coordinates `g(Xᵢ)`, `W ⊆ V` an open, and `z` sections over
`W` with `dz₁ ∧ ⋯ ∧ dzₙ = h₀ · dg(X₁) ∧ ⋯ ∧ dg(Xₙ)` over `Γ(Spec R)`. Along a prime divisor of `F`
with generic point over `V`, the order of the rational form `dz₁ ∧ ⋯ ∧ dzₙ` of `F` is the order
of `h₀`. -/
public lemma ordForm_eq_ord_of_isPullback {Y F : Scheme.{u}} {R : CommRingCat.{u}} {L : Type u}
    [Field L] {q : Y ⟶ Spec R} {t : Spec (.of L) ⟶ Spec R} {fst : F ⟶ Y} {snd : F ⟶ Spec (.of L)}
    (hpb : IsPullback fst snd q t) [IsIntegral F] [IsLocallyNoetherian F] (V : Y.Opens)
    (hV : IsAffineOpen V) {n : ℕ} (g : MvPolynomial (Fin n) Γ(Spec R, ⊤) →+* Γ(Y, V))
    (hg : g.Etale) (hgC : g.comp MvPolynomial.C = (q.appLE ⊤ V le_top).hom) (W : Y.Opens)
    (hWV : W ≤ V) [Nonempty (fst ⁻¹ᵁ W)] (z : Fin n → Γ(Y, W)) (h₀ : Γ(Y, W))
    (hrel : letI := (q.appLE ⊤ W le_top).hom.toAlgebra
      exteriorPower.ιMulti Γ(Y, W) n (fun i => KaehlerDifferential.D Γ(Spec R, ⊤) Γ(Y, W) (z i)) =
        h₀ • exteriorPower.ιMulti Γ(Y, W) n (fun i => KaehlerDifferential.D Γ(Spec R, ⊤) Γ(Y, W)
          (Y.presheaf.map (homOfLE hWV).op (g (MvPolynomial.X i)))))
    (Γ : Mori.PrimeDivisor F) (hΓ : Γ.genericPoint ∈ fst ⁻¹ᵁ V) (ω : Mori.RationalTopForms snd n)
    (hω : letI := MMP.Mori.functionFieldAlgebra snd
      ω = exteriorPower.ιMulti F.functionField n fun i =>
        KaehlerDifferential.D L F.functionField
            (F.germToFunctionField (fst ⁻¹ᵁ W) (fst.app W (z i)))) :
    Γ.ordForm (ω.toPluriForms snd) =
      F.ord (F.germToFunctionField (fst ⁻¹ᵁ W) (fst.app W h₀)) Γ.genericPoint := by
  letI : Algebra Γ(Spec R, ⊤) Γ(Y, W) := (q.appLE ⊤ W le_top).hom.toAlgebra
  letI : Algebra Γ(Y, W) F.functionField :=
    (fst.app W ≫ F.germToFunctionField (fst ⁻¹ᵁ W)).hom.toAlgebra
  letI : Algebra Γ(Spec R, ⊤) L := (t.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom).hom.toAlgebra
  letI := MMP.Mori.functionFieldAlgebra snd
  letI : Algebra Γ(Spec R, ⊤) F.functionField :=
    (q.appLE ⊤ W le_top ≫ fst.app W ≫ F.germToFunctionField (fst ⁻¹ᵁ W)).hom.toAlgebra
  have : IsScalarTower Γ(Spec R, ⊤) Γ(Y, W) F.functionField := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Spec R, ⊤) L F.functionField := IsScalarTower.of_algebraMap_eq' (by
    change (q.appLE ⊤ W le_top ≫ fst.app W ≫ F.germToFunctionField (fst ⁻¹ᵁ W)).hom = _
    rw [appLE_comp_germToFunctionField_of_isPullback hpb W]
    rfl)
  have h1 := ιMulti_D_algebraMap_eq_smul (R := Γ(Spec R, ⊤)) (L := L) (K := F.functionField) z _
    h₀ hrel
  obtain ⟨b, hb⟩ := exists_basis_kaehler_stalk_of_isPullback hpb V hV g hg hgC Γ.genericPoint hΓ
  haveI : Nonempty (fst ⁻¹ᵁ V) := ⟨⟨_, hΓ⟩⟩
  have hy : ∀ i, algebraMap Γ(Y, W) F.functionField
      (Y.presheaf.map (homOfLE hWV).op (g (MvPolynomial.X i))) =
      algebraMap (F.presheaf.stalk Γ.genericPoint) F.functionField
        (F.presheaf.germ (fst ⁻¹ᵁ V) Γ.genericPoint hΓ (fst.app V (g (MvPolynomial.X i)))) := by
    intro i
    rw [Scheme.algebraMap_germ_eq_germToFunctionField]
    have e : fst.app W (Y.presheaf.map (homOfLE hWV).op (g (MvPolynomial.X i))) =
        F.presheaf.map (homOfLE (Scheme.Hom.preimage_mono fst hWV)).op
          (fst.app V (g (MvPolynomial.X i))) := by
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
      congr 1
      exact congrArg CommRingCat.Hom.hom (fst.naturality (homOfLE hWV).op)
    change F.germToFunctionField (fst ⁻¹ᵁ W) (fst.app W _) = _
    rw [e]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  refine ordForm_toPluriForms_eq_ord snd Γ _ b hb _ ω (hω.trans (h1.trans ?_))
  simp only [hy]
  rfl

/-- **Étale charts of a smooth scheme over an affine base.** -/
private lemma exists_etale_chart {Y : Scheme.{u}} {R : CommRingCat.{u}} (q : Y ⟶ Spec R) [Smooth q]
    (y : Y) :
    ∃ (V : Y.Opens) (_ : IsAffineOpen V) (_ : y ∈ V) (n : ℕ)
      (g : MvPolynomial (Fin n) Γ(Spec R, ⊤) →+* Γ(Y, V)),
      g.Etale ∧ g.comp MvPolynomial.C = (q.appLE ⊤ V le_top).hom := by
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hyV₀, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hsm : (q.appLE ⊤ V₀ le_top).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth q ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨V₀, hV₀⟩ _
  rw [RingHom.smooth_iff_locally_isStandardSmooth,
    RingHom.locally_iff_isLocalization RingHom.isStandardSmooth_respectsIso] at hsm
  obtain ⟨s, hs, H⟩ := hsm
  have : ∃ r ∈ s, y ∈ Y.basicOpen r := by
    by_contra hne
    push Not at hne
    have hle : Ideal.map (Y.presheaf.germ V₀ y hyV₀).hom (Ideal.span (s : Set Γ(Y, V₀))) ≤
        IsLocalRing.maximalIdeal _ := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨r, hr, rfl⟩
      have := hne r hr
      rwa [Scheme.mem_basicOpen _ _ _ hyV₀] at this
    rw [hs, Ideal.map_top] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hle)
  obtain ⟨r, hr, hyr⟩ := this
  let V := Y.basicOpen r
  have hVa : IsAffineOpen V := hV₀.basicOpen r
  letI : Algebra Γ(Y, V₀) Γ(Y, V) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom.toAlgebra
  have : IsLocalization.Away r Γ(Y, V) := hV₀.isLocalization_basicOpen r
  have hstd := H r hr Γ(Y, V)
  obtain ⟨n, g, hgC, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial hstd
  refine ⟨V, hVa, hyr, n, g, hg, ?_⟩
  rw [hgC]
  change ((q.appLE ⊤ V₀ le_top) ≫ Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom = _
  exact congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_map q _ _)

/-- **Étale charts inside an open on which a scheme is smooth over an affine base.** -/
public lemma exists_etale_chart_of_smooth_on {Y : Scheme.{u}} {R : CommRingCat.{u}} (q : Y ⟶ Spec R)
    (U : Y.Opens) [Smooth (U.ι ≫ q)] (y : Y) (hy : y ∈ U) :
    ∃ (V : Y.Opens) (_ : V ≤ U) (_ : IsAffineOpen V) (_ : y ∈ V) (n : ℕ)
      (g : MvPolynomial (Fin n) Γ(Spec R, ⊤) →+* Γ(Y, V)),
      g.Etale ∧ g.comp MvPolynomial.C = (q.appLE ⊤ V le_top).hom := by
  obtain ⟨V', hV', hyV', n, g', hg', hgC'⟩ := exists_etale_chart (U.ι ≫ q) ⟨y, hy⟩
  refine ⟨U.ι ''ᵁ V', U.ι.image_le_opensRange V' |>.trans (by simp),
    hV'.image_of_isOpenImmersion U.ι, ⟨⟨y, hy⟩, hyV', rfl⟩, n,
    (U.ι.appIso V').inv.hom.comp g', ?_, ?_⟩
  · exact RingHom.Etale.respectsIso.1 g' (U.ι.appIso V').symm.commRingCatIsoToRingEquiv hg'
  · rw [RingHom.comp_assoc, hgC', ← CommRingCat.hom_comp]
    congr 1
    rw [Iso.comp_inv_eq, Scheme.Hom.appIso_hom']
    erw [Scheme.Hom.appLE_comp_appLE]

/-- **The Jacobian of a change of chart.** On a basic open `W` of an affine chart `V` with étale
coordinates `g(Xᵢ)`, the wedge of the differentials of any `n` sections over `W` is a multiple
`h₀` of the wedge of the differentials of the coordinates. -/
public lemma exists_wedge_eq_smul {Y : Scheme.{u}} {R : CommRingCat.{u}} (q : Y ⟶ Spec R)
    (V : Y.Opens)
    (hV : IsAffineOpen V) {n : ℕ} (g : MvPolynomial (Fin n) Γ(Spec R, ⊤) →+* Γ(Y, V))
    (hg : g.Etale) (hgC : g.comp MvPolynomial.C = (q.appLE ⊤ V le_top).hom) (f : Γ(Y, V))
    (z : Fin n → Γ(Y, Y.basicOpen f)) :
    letI := (q.appLE ⊤ (Y.basicOpen f) le_top).hom.toAlgebra
    ∃ h₀ : Γ(Y, Y.basicOpen f),
      exteriorPower.ιMulti Γ(Y, Y.basicOpen f) n
          (fun i => KaehlerDifferential.D Γ(Spec R, ⊤) Γ(Y, Y.basicOpen f) (z i)) =
        h₀ • exteriorPower.ιMulti Γ(Y, Y.basicOpen f) n (fun i =>
          KaehlerDifferential.D Γ(Spec R, ⊤) Γ(Y, Y.basicOpen f)
            (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op (g (MvPolynomial.X i)))) := by
  letI : Algebra Γ(Spec R, ⊤) Γ(Y, V) := (q.appLE ⊤ V le_top).hom.toAlgebra
  letI : Algebra Γ(Spec R, ⊤) Γ(Y, Y.basicOpen f) :=
      (q.appLE ⊤ (Y.basicOpen f) le_top).hom.toAlgebra
  letI : Algebra Γ(Y, V) Γ(Y, Y.basicOpen f) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom.toAlgebra
  have : IsScalarTower Γ(Spec R, ⊤) Γ(Y, V) Γ(Y, Y.basicOpen f) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom
      (Scheme.Hom.appLE_map q _ _)).symm
  have : IsLocalization.Away f Γ(Y, Y.basicOpen f) := hV.isLocalization_basicOpen f
  have : Algebra.FormallyEtale Γ(Y, V) Γ(Y, Y.basicOpen f) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers f)
  let gA : MvPolynomial (Fin n) Γ(Spec R, ⊤) →ₐ[Γ(Spec R, ⊤)] Γ(Y, V) :=
    { toRingHom := g
      commutes' := fun r => congrArg (fun φ => φ r) hgC }
  obtain ⟨bV, hbV⟩ := exists_basis_kaehler_of_etale gA hg
  obtain ⟨bW, hbW⟩ := exists_basis_kaehler_of_formallyEtale (T := Γ(Y, Y.basicOpen f)) bV hbV
  have hspan : Submodule.span Γ(Y, Y.basicOpen f) (Set.range fun i =>
      KaehlerDifferential.D Γ(Spec R, ⊤) Γ(Y, Y.basicOpen f)
        (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op (g (MvPolynomial.X i)))) = ⊤ := by
    rw [← bW.span_eq]
    congr 1
    ext w
    simp only [Set.mem_range, hbW]
    rfl
  have hσ := ExteriorAlgebra.span_singleton_ιMulti_eq_top _ hspan
  have hmem := hσ.ge (Submodule.mem_top (x := exteriorPower.ιMulti Γ(Y, Y.basicOpen f) n
      (fun i => KaehlerDifferential.D Γ(Spec R, ⊤) Γ(Y, Y.basicOpen f) (z i))))
  obtain ⟨h₀, hh₀⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨h₀, hh₀.symm⟩

/-- A nonzero vector of a line spans it. -/
public lemma span_singleton_eq_top_of_basis_unit {K L : Type*} [Field K] [AddCommGroup L]
    [Module K L] (B : Module.Basis Unit K L) {ω : L} (hω : ω ≠ 0) : Submodule.span K {ω} = ⊤ :=
  (finrank_eq_one_iff_of_nonzero ω hω).mp ((Module.finrank_eq_card_basis B).trans Fintype.card_unit)

/-- **The order of `c ω^{⊗m}`** along a prime divisor of a normal variety of dimension `n`
over a perfect field: `ord_Γ(c ω^{⊗m}) = v_Γ(c) + m ord_Γ(ω)`. -/
public lemma ordForm_smul_formPow {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] {n : ℕ} (hn : topologicalKrullDim X = n) (Γ : Mori.PrimeDivisor X)
    (ω : Mori.RationalTopForms sX n) (hω : ω ≠ 0) {c : X.functionField} (hc : c ≠ 0) (m : ℕ) :
    letI := MMP.Mori.functionFieldAlgebra sX
    Γ.ordForm (sX := sX) (d := n) (m := m) (c • MMP.Fourfold.formPow
      (ω : ⋀[X.functionField]^n Ω[X.functionField⁄k]) m) =
      X.ord c Γ.genericPoint + m * Γ.ordForm (ω.toPluriForms sX) := by
  letI := MMP.Mori.functionFieldAlgebra sX
  obtain ⟨B⟩ := MMP.Fourfold.exists_basis_topForms (sX := sX) hn
  let b := MMP.Mori.basisOfSpanSingleton (span_singleton_eq_top_of_basis_unit B hω) hω
  have hb : b () = ω := MMP.Mori.basisOfSpanSingleton_apply _ _ _
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul
    (MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq hn) b
  have hτ : ∀ (a : ℕ) (d : X.functionField), d ≠ 0 →
      (d • MMP.Fourfold.formPow (b ()) a : Mori.PluriForms k X.functionField n a) ≠ 0 := by
    intro a d hd h0
    have := MMP.Fourfold.repr_smul_formPow b a d
    rw [h0] at this
    simp at this
    exact hd this.symm
  have hbasis : (Mori.ZTensorPower.basis b 1 () : Mori.PluriForms k X.functionField n 1) =
      ω.toPluriForms sX := by
    have := Mori.ZTensorPower.basis_ofNat b 1
    refine this.trans ?_
    rw [hb]
    rfl
  have hne1 : ω.toPluriForms sX ≠ 0 := by
    rw [← hbasis]
    exact (Mori.ZTensorPower.basis b 1).ne_zero ()
  have e2 := hN 1 _ hne1
  have hrep : (Mori.ZTensorPower.basis b 1).repr (ω.toPluriForms sX) () = 1 := by
    rw [← hbasis]
    simp
  have hord1 : X.ord (1 : X.functionField) Γ.genericPoint = 0 := by
    rw [Scheme.ord_eq_iff Γ.coheight_genericPoint one_ne_zero, map_one, ofAdd_zero,
      WithZero.coe_one]
  rw [hrep, hord1, zero_add, one_mul] at e2
  have e1 := hN m _ (hτ m c hc)
  rw [MMP.Fourfold.repr_smul_formPow] at e1
  rw [e2, ← hb]
  exact e1

/-- Every nonzero multiple of a pull-back generator is a pull-back generator. -/
public lemma isPullbackGenerator_of_ne_zero {k : Type*} [CommRing k] {K K' : Type*} [Field K]
    [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}
    {ω₀ ω : ⋀[K]^d Ω[K⁄k]} (hω₀ : MMP.Mori.IsPullbackGenerator K' ω₀) (hω : ω ≠ 0) :
    MMP.Mori.IsPullbackGenerator K' ω := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hω₀.1 ▸ Submodule.mem_top (x := ω))
  have hc : c ≠ 0 := by rintro rfl; exact hω (zero_smul _ _)
  refine ⟨?_, ?_, ?_⟩
  · rw [Submodule.span_singleton_smul_eq (Ne.isUnit hc)]
    exact hω₀.1
  · rw [map_smul, ← algebraMap_smul K',
      Submodule.span_singleton_smul_eq (Ne.isUnit ((map_ne_zero _).mpr hc))]
    exact hω₀.2.1
  · rw [map_smul, ← algebraMap_smul K']
    exact smul_ne_zero ((map_ne_zero _).mpr hc) hω₀.2.2

/-- **The order of a pulled-back `c ω^{⊗m}`** along a prime divisor of the source of a birational
morphism of normal varieties of dimension `n` over a perfect field. -/
public lemma ordForm_pullback_smul_formPow {k : Type u} [Field k] [PerfectField k]
    {Z W : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of k)) [IsIntegral Z] [LocallyOfFiniteType sZ] (μ : W ⟶ Z) [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [LocallyOfFiniteType (μ ≫ sZ)] [IsDominant μ]
    (hbij : Function.Bijective (AlgebraicGeometry.functionFieldMap μ)) {n : ℕ}
    (hn : topologicalKrullDim Z = n) (hnW : topologicalKrullDim W = n)
    (F : Mori.PrimeDivisor W) (ω : Mori.RationalTopForms sZ n) (hω : ω ≠ 0)
    {c : Z.functionField} (hc : c ≠ 0) (m : ℕ) :
    letI := MMP.Mori.functionFieldAlgebra sZ
    F.ordForm (Mori.pullbackRationalPluriForms sZ μ (d := n) (m := m)
        (c • MMP.Fourfold.formPow (ω : ⋀[Z.functionField]^n Ω[Z.functionField⁄k]) m)) =
      W.ord (AlgebraicGeometry.functionFieldMap μ c) F.genericPoint +
        m * F.ordForm (Mori.pullbackRationalPluriForms sZ μ (ω.toPluriForms sZ)) := by
  letI := MMP.Mori.functionFieldAlgebra sZ
  letI := MMP.Mori.functionFieldAlgebra (μ ≫ sZ)
  letI := MMP.Mori.functionFieldMapAlgebra μ
  haveI := MMP.Mori.isScalarTower_functionFieldMap sZ μ
  obtain ⟨ω₀, hω₀⟩ := MMP.Mori.exists_isPullbackGenerator_of_bijective sZ μ hbij
    (MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq hn)
  have hω' := isPullbackGenerator_of_ne_zero hω₀ hω
  have p1 : Mori.pullbackRationalPluriForms sZ μ (d := n) (m := m)
      (c • MMP.Fourfold.formPow (ω : ⋀[Z.functionField]^n Ω[Z.functionField⁄k]) m) =
      algebraMap Z.functionField W.functionField c •
        MMP.Fourfold.formPow (MMP.Mori.topFormsMap k Z.functionField W.functionField n ω) m :=
    MMP.Fourfold.pullbackForms_smul_formPow hω' m c
  have p2 : Mori.pullbackRationalPluriForms sZ μ (ω.toPluriForms sZ) =
      MMP.Fourfold.formPow (MMP.Mori.topFormsMap k Z.functionField W.functionField n ω) 1 := by
    have := MMP.Fourfold.pullbackForms_smul_formPow hω' 1 (1 : Z.functionField)
    rwa [one_smul, map_one, one_smul] at this
  let ω' : Mori.RationalTopForms (μ ≫ sZ) n :=
    MMP.Mori.topFormsMap k Z.functionField W.functionField n ω
  have hω'0 : ω' ≠ 0 := hω'.2.2
  have hc' : algebraMap Z.functionField W.functionField c ≠ 0 := (map_ne_zero _).mpr hc
  rw [p1, p2]
  exact ordForm_smul_formPow hnW F ω' hω'0 hc' m

end Properties

end

end MMP.Spreading
