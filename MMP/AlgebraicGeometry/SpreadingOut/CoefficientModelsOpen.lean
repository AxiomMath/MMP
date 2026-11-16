module

public import MMP.AlgebraicGeometry.SpreadingOut.CoefficientModels
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic

/-!
# Open immersions in the model of a diagram

Let `X` be a finite diagram of schemes of finite presentation over the limit of a cofiltered
diagram of quasi-compact quasi-separated schemes with affine transition morphisms, with stage
data `d`. An arrow of `X` which is an open immersion has, from some stage on, a model which is
an open immersion (Stacks 0EUU), and then at every still later stage.

## Main results

* `MMP.CoefficientModels.DiagramStageData.exists_isOpenImmersion`: from some stage on, the
  models of the arrows of `X` which are open immersions are open immersions.

## References

* [Stacks Project, Tag 0EUU](https://stacks.math.columbia.edu/tag/0EUU)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MMP.CoefficientModels

namespace DiagramStageData

variable {I : Type u} [SmallCategory I] [IsCofiltered I] [∀ i j : I, Subsingleton (i ⟶ j)]
  {D : I ⥤ Scheme.{u}} {c : Cone D}
  [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] {n : ℕ}
  {J : Type u} [SmallCategory J] {X : J ⥤ Over c.pt}
  {ι : ∀ j, (X.obj j).left ⟶ projectiveSpaceOver n c.pt} (d : DiagramStageData D c n X ι)

/-- An arrow of `X` which is an open immersion has, at some stage below `d.m₁`, a model which is
an open immersion (Stacks 0EUU). -/
theorem exists_stage_isOpenImmersion (hc : IsLimit c) {j j' : J} (φ : j ⟶ j')
    (hφ : IsOpenImmersion (X.map φ).left) :
    ∃ (ic : I) (hic : ic ⟶ d.m₁.left), IsOpenImmersion ((Over.pullback (D.map hic)).map
      (Over.homMk (stageLift (d.H φ) (d.H_w φ) (𝟙 d.m₁)) (stageLift_fst _ _ _) :
        Over.mk (pullback.fst (D.map d.m₁.hom) (d.W j).hom) ⟶
          Over.mk (pullback.fst (D.map d.m₁.hom) (d.W j').hom))).left := by
  let Z : J → Over (D.obj d.m₁.left) := fun j =>
    Over.mk (pullback.fst (D.map d.m₁.hom) (d.W j).hom)
  let fx : Z j ⟶ Z j' := Over.homMk (stageLift (d.H φ) (d.H_w φ) (𝟙 d.m₁)) (stageLift_fst _ _ _)
  have : CompactSpace (Z j).left :=
    compactSpace_stageObj D (d.W j) (d.finitePresentation j) d.m₁
  have : QuasiSeparatedSpace (Z j).left :=
    quasiSeparatedSpace_stageObj D (d.W j) (d.finitePresentation j) d.m₁
  have : CompactSpace (Z j').left :=
    compactSpace_stageObj D (d.W j') (d.finitePresentation j') d.m₁
  have : QuasiSeparatedSpace (Z j').left :=
    quasiSeparatedSpace_stageObj D (d.W j') (d.finitePresentation j') d.m₁
  have : LocallyOfFinitePresentation (d.W j).hom := (d.finitePresentation j).1
  have : LocallyOfFinitePresentation (d.W j').hom := (d.finitePresentation j').1
  have : LocallyOfFinitePresentation fx.left := by
    have : LocallyOfFinitePresentation (fx.left ≫ (Z j').hom) := by
      rw [Over.w fx]
      dsimp [Z]
      infer_instance
    have : LocallyOfFiniteType (Z j').hom := by
      dsimp [Z]
      infer_instance
    exact locallyOfFinitePresentation_of_comp fx.left (Z j').hom
  have hlim : IsOpenImmersion ((Over.pullback (c.π.app d.m₁.left)).map fx).left :=
    overPullback_map_of_isPullback (c.π.app d.m₁.left) fx @IsOpenImmersion
      (X.map φ).left (d.isPullback_proj d.m₁ j) (d.isPullback_proj d.m₁ j')
      (d.proj_stageLift d.m₁ (𝟙 d.m₁) φ).symm (Over.w (X.map φ)) hφ
  exact exists_isOpenImmersion_pullback D c hc d.m₁.left (Z j) (Z j') fx hlim

/-- **From some stage on, the models of the arrows which are open immersions are open
immersions** (Stacks 0EUU). -/
theorem exists_isOpenImmersion (hc : IsLimit c) [FinCategory J] :
    ∃ (b : Over d.i₀) (bb : b ⟶ d.m₂), ∀ {m : Over d.i₀} (bm : m ⟶ b) {j j' : J} (φ : j ⟶ j'),
      IsOpenImmersion (X.map φ).left → IsOpenImmersion ((d.diagram (bm ≫ bb)).map φ).left := by
  classical
  have key : ∀ (j j' : J) (φ : j ⟶ j'), ∃ (ic : I) (hic : ic ⟶ d.m₁.left),
      IsOpenImmersion (X.map φ).left →
        IsOpenImmersion ((Over.pullback (D.map hic)).map
          (Over.homMk (stageLift (d.H φ) (d.H_w φ) (𝟙 d.m₁)) (stageLift_fst _ _ _) :
            Over.mk (pullback.fst (D.map d.m₁.hom) (d.W j).hom) ⟶
              Over.mk (pullback.fst (D.map d.m₁.hom) (d.W j').hom))).left := by
    intro j j' φ
    by_cases hφ : IsOpenImmersion (X.map φ).left
    · obtain ⟨ic, hic, hci⟩ := d.exists_stage_isOpenImmersion hc φ hφ
      exact ⟨ic, hic, fun _ => hci⟩
    · exact ⟨d.m₁.left, 𝟙 _, (absurd · hφ)⟩
  choose ic hic hicx using key
  let mcx : (Σ (j j' : J), (j ⟶ j')) → Over d.i₀ := fun x =>
    Over.mk (hic x.1 x.2.1 x.2.2 ≫ d.m₁.hom)
  obtain ⟨b, hb⟩ := IsCofiltered.inf_objs_exists (insert d.m₂ (Finset.univ.image mcx))
  have bb : b ⟶ d.m₂ := (hb (Finset.mem_insert_self _ _)).some
  have dcx : ∀ {j j' : J} (φ : j ⟶ j'), b ⟶ mcx ⟨j, j', φ⟩ := fun {j j'} φ =>
    (hb (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (Finset.mem_univ ⟨j, j', φ⟩)))).some
  refine ⟨b, bb, fun {m} bm {j j'} φ hφ => ?_⟩
  let dd : m ⟶ mcx ⟨j, j', φ⟩ := bm ≫ dcx φ
  have hd : ((bm ≫ bb) ≫ d.b₂).left = dd.left ≫ hic j j' φ := Subsingleton.elim _ _
  have hsq := isPullback_stageLift_stageMap (d.H φ) (d.H_w φ) ((bm ≫ bb) ≫ d.b₂) (𝟙 d.m₁)
  rw [Category.comp_id] at hsq
  refine of_isPullback_overPullback (D.map (hic j j' φ)) _ @IsOpenImmersion
    (hicx j j' φ hφ) ((d.diagram (bm ≫ bb)).map φ).left
    (stageMap D (d.W j) ((bm ≫ bb) ≫ d.b₂)) (stageMap D (d.W j') ((bm ≫ bb) ≫ d.b₂))
    (pullback.fst (D.map m.hom) (d.W j').hom ≫ D.map dd.left) hsq ?_
  change stageMap D (d.W j') ((bm ≫ bb) ≫ d.b₂) ≫ pullback.fst _ _ = _
  rw [stageMap_fst, hd, D.map_comp]
  exact (Category.assoc _ _ _).symm

end DiagramStageData

end MMP.CoefficientModels

end
