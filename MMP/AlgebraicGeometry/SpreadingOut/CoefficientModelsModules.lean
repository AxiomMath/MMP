module

public import MMP.AlgebraicGeometry.SpreadingOut.CoefficientModels
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.InvertibleUnconditional
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.AmpleRestrict
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PullbackUnitModule

/-!
# Spreading out modules of finite presentation over the stages of a model

Let `S = lim S_i` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition morphisms, and let `W` over `S_{i₀}` be a stage model of finite presentation of a
scheme `X` over `S`. A module of finite presentation on `X` is the pullback of a module of finite
presentation on the base change of `W` to some later stage (Stacks 01ZR), and then on every
still later one; over a locally Noetherian stage that module is coherent.

## Main definitions

* `MMP.CoefficientModels.ModuleStageData`: models of a finite system of modules on the objects of
  a diagram with stage data, with the model `MMP.CoefficientModels.ModuleStageData.module` at
  every sufficiently late stage and its identification
  `MMP.CoefficientModels.ModuleStageData.moduleIso`.

## Main results

* `MMP.CoefficientModels.exists_stage_module`: the descent of a module of finite presentation to
  a base change of the stage model.
* `MMP.CoefficientModels.stageModuleIso`: the identification of the module with the pullback of
  its model moved to a later stage.
* `MMP.CoefficientModels.isCoherent_stage_pullback`: over a locally Noetherian stage the model,
  moved to any later stage, is coherent.
* `MMP.CoefficientModels.exists_moduleStageData`: a finite system of modules of finite
  presentation has models, trivial where the module is trivial and invertible where the module
  is invertible (Stacks 0B8W).

## References

* [EGA IV₃, §8]
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MMP.CoefficientModels

section StageModule

variable {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u}) {i₀ : I} (W : Over (D.obj i₀))
  (c : Cone D) (X : Over c.pt) (g : X.left ⟶ W.left)
  (hpb : IsPullback g X.hom W.hom (c.π.app i₀))

/-- The identification of a module on `X` with the pullback of its stage model, moved from the
stage `mₑ` to a later stage `m`. -/
def stageModuleIso {M : X.left.Modules} {mₑ : Over i₀} {N : (stageObj D W mₑ).Modules}
    (θ : M ≅ (Scheme.Modules.pullback (leg D W c X g hpb mₑ)).obj N) {m : Over i₀}
    (b : m ⟶ mₑ) :
    M ≅ (Scheme.Modules.pullback (leg D W c X g hpb m)).obj
      ((Scheme.Modules.pullback (stageMap D W b)).obj N) :=
  θ ≪≫ (Scheme.Modules.pullbackCongr (leg_stageMap D W c X g hpb b)).symm.app N ≪≫
    (Scheme.Modules.pullbackComp (leg D W c X g hpb m) (stageMap D W b)).symm.app N

/-- **The stage model of a module is coherent over a locally Noetherian stage.** -/
theorem isCoherent_stage_pullback (hW : FinitePresentation W.hom) {mₑ m : Over i₀}
    [IsLocallyNoetherian (D.obj m.left)] (b : m ⟶ mₑ) (N : (stageObj D W mₑ).Modules)
    [N.IsFinitePresentation] :
    ((Scheme.Modules.pullback (stageMap D W b)).obj N).IsCoherent := by
  have : LocallyOfFinitePresentation W.hom := hW.1
  have : IsLocallyNoetherian (stageObj D W m) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (D.map m.hom) W.hom)
  exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation _
    (Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ N)

variable [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hpb in
/-- **A module of finite presentation on `X` descends to a base change of the stage model**
(Stacks 01ZR). -/
theorem exists_stage_module (hc : IsLimit c) (hW : FinitePresentation W.hom)
    (M : X.left.Modules) [M.IsFinitePresentation] :
    ∃ (mₑ : Over i₀) (N : (stageObj D W mₑ).Modules), N.IsFinitePresentation ∧
      Nonempty (M ≅ (Scheme.Modules.pullback (leg D W c X g hpb mₑ)).obj N) := by
  have {j k : Over i₀} (e : j ⟶ k) : IsAffineHom ((stageDiagram D W).map e) :=
    isAffineHom_stageMap D W e
  have (m : Over i₀) : CompactSpace ((stageDiagram D W).obj m) := compactSpace_stageObj D W hW m
  have (m : Over i₀) : QuasiSeparatedSpace ((stageDiagram D W).obj m) :=
    quasiSeparatedSpace_stageObj D W hW m
  exact @Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs
    _ _ _ (stageDiagram D W) _ (legCone D W c X g hpb) (isLimitLegCone D W c X g hpb hc) _ _ M ‹_›

end StageModule

/-! ### Models of a system of modules on the objects of a diagram -/

section ModuleStageData

variable {I : Type u} [SmallCategory I] {D : I ⥤ Scheme.{u}} {c : Cone D} {n : ℕ}
  {J : Type u} [SmallCategory J] {X : J ⥤ Over c.pt}
  {ι : ∀ j, (X.obj j).left ⟶ projectiveSpaceOver n c.pt} (d : DiagramStageData D c n X ι)
  {E : Type*} [Category E] (π : E ⥤ J) (M : ∀ e, (X.obj (π.obj e)).left.Modules)

/-- Models of modules `M e` on the objects `X (π e)` of a diagram with stage data `d`: a module
`N₀ e` of finite presentation on the base change of the stage model of `X (π e)` to a stage
`mₑ e`, with pullback `M e`, and a stage `m₃` later than `d.m₂` and all the stages `mₑ e`. -/
structure ModuleStageData where
  /-- The stage at which `M e` is modelled. -/
  mₑ : E → Over d.i₀
  /-- The model of `M e`. -/
  N₀ (e : E) : (stageObj D (d.W (π.obj e)) (mₑ e)).Modules
  /-- The model of `M e` is of finite presentation. -/
  isFinitePresentation (e : E) : (N₀ e).IsFinitePresentation
  /-- The identification of `M e` with the pullback of its model. -/
  θ₀ (e : E) : M e ≅ (Scheme.Modules.pullback (d.proj (mₑ e) (π.obj e))).obj (N₀ e)
  /-- A stage later than `d.m₂` and all the stages `mₑ e`. -/
  m₃ : Over d.i₀
  /-- The transition from `m₃` to `d.m₂`. -/
  b₃ : m₃ ⟶ d.m₂
  /-- The transitions from `m₃` to the stages `mₑ e`. -/
  bₑ (e : E) : m₃ ⟶ mₑ e

namespace ModuleStageData

variable {d π M} (md : ModuleStageData d π M) {m : Over d.i₀} (bm : m ⟶ md.m₃)

/-- The model of `M e` at a stage `m` later than `md.m₃`. -/
def module (e : E) : (stageObj D (d.W (π.obj e)) m).Modules :=
  (Scheme.Modules.pullback (stageMap D (d.W (π.obj e)) (bm ≫ md.bₑ e))).obj (md.N₀ e)

/-- The identification of the pullback of the model of `M e` at the stage `m` with `M e`. -/
def moduleIso (e : E) :
    (Scheme.Modules.pullback (d.proj m (π.obj e))).obj (md.module bm e) ≅ M e :=
  (stageModuleIso D (d.W (π.obj e)) c (X.obj (π.obj e)) (d.g _) (d.isPullback _) (md.θ₀ e)
    (bm ≫ md.bₑ e)).symm

/-- The model of `M e` at a stage later than `md.m₃` is of finite presentation. -/
instance isFinitePresentation_module (e : E) : (md.module bm e).IsFinitePresentation :=
  have := md.isFinitePresentation e
  Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ (md.N₀ e)

/-- **Over a locally Noetherian stage the model of `M e` is coherent.** -/
theorem isCoherent_module [IsLocallyNoetherian (D.obj m.left)] (e : E) :
    (md.module bm e).IsCoherent :=
  have := md.isFinitePresentation e
  isCoherent_stage_pullback D (d.W (π.obj e)) (d.finitePresentation _) (bm ≫ md.bₑ e) (md.N₀ e)

/-- An invertible model of `M e` stays invertible at every later stage. -/
theorem isInvertibleModule_module {e : E}
    (h : Stacks.Ample.IsInvertibleModule _ (md.N₀ e)) :
    Stacks.Ample.IsInvertibleModule _ (md.module bm e) :=
  have := h
  inferInstanceAs (Stacks.Ample.IsInvertibleModule _ ((Scheme.Modules.pullback _).obj _))

/-- A trivial model of `M e` stays trivial at every later stage. -/
theorem nonempty_iso_unit_module {e : E}
    (h : Nonempty (md.N₀ e ≅ SheafOfModules.unit _)) :
    Nonempty (md.module bm e ≅ SheafOfModules.unit _) :=
  ⟨(Scheme.Modules.pullback _).mapIso h.some ≪≫ Stacks.FundamentalGroup.pullbackUnitIso _⟩

end ModuleStageData

variable [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

/-- **A finite system of modules of finite presentation on the objects of the diagram has
models** (Stacks 01ZR), chosen trivial where the module is trivial and invertible where the
module is invertible (Stacks 0B8W). -/
theorem exists_moduleStageData (hc : IsLimit c) [Finite E] (hM : ∀ e, (M e).IsFinitePresentation) :
    ∃ md : ModuleStageData d π M,
      (∀ e, Stacks.Ample.IsInvertibleModule _ (M e) →
        Stacks.Ample.IsInvertibleModule _ (md.N₀ e)) ∧
      (∀ e, Nonempty (M e ≅ SheafOfModules.unit _) →
        Nonempty (md.N₀ e ≅ SheafOfModules.unit _)) := by
  classical
  have key : ∀ e, ∃ (mₑ : Over d.i₀) (N : (stageObj D (d.W (π.obj e)) mₑ).Modules),
      N.IsFinitePresentation ∧
      Nonempty (M e ≅ (Scheme.Modules.pullback (d.proj mₑ (π.obj e))).obj N) ∧
      (Stacks.Ample.IsInvertibleModule _ (M e) → Stacks.Ample.IsInvertibleModule _ N) ∧
      (Nonempty (M e ≅ SheafOfModules.unit _) → Nonempty (N ≅ SheafOfModules.unit _)) := by
    intro e
    let j := π.obj e
    by_cases ht : Nonempty (M e ≅ SheafOfModules.unit _)
    · refine ⟨d.m₂, SheafOfModules.unit _, inferInstance,
        ⟨ht.some ≪≫ (Stacks.FundamentalGroup.pullbackUnitIso _).symm⟩, fun _ => inferInstance,
        fun _ => ⟨Iso.refl _⟩⟩
    by_cases hi : Stacks.Ample.IsInvertibleModule _ (M e)
    · have {a b : Over d.i₀} (f : a ⟶ b) : IsAffineHom ((stageDiagram D (d.W j)).map f) :=
        isAffineHom_stageMap D (d.W j) f
      have (a : Over d.i₀) : CompactSpace ((stageDiagram D (d.W j)).obj a) :=
        compactSpace_stageObj D (d.W j) (d.finitePresentation j) a
      have (a : Over d.i₀) : QuasiSeparatedSpace ((stageDiagram D (d.W j)).obj a) :=
        quasiSeparatedSpace_stageObj D (d.W j) (d.finitePresentation j) a
      obtain ⟨a, L, hL, hiso⟩ :=
        Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit
          (stageDiagram D (d.W j)) (legCone D (d.W j) c (X.obj j) (d.g j) (d.isPullback j))
          (isLimitLegCone D (d.W j) c (X.obj j) (d.g j) (d.isPullback j) hc) (M e) hi
      have : Stacks.Ample.IsInvertibleModule _ L := hL
      exact ⟨a, L, @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible _ L hL,
        hiso, fun _ => hL, fun h => absurd h ht⟩
    · have := hM e
      obtain ⟨a, N, hN, hiso⟩ := exists_stage_module D (d.W j) c (X.obj j) (d.g j)
        (d.isPullback j) hc (d.finitePresentation j) (M e)
      exact ⟨a, N, hN, hiso, fun h => absurd h hi, fun h => absurd h ht⟩
  choose mₑ N hN hθ hinv htriv using key
  have := Fintype.ofFinite E
  obtain ⟨m₃, hm₃⟩ := IsCofiltered.inf_objs_exists (insert d.m₂ (Finset.univ.image mₑ))
  exact ⟨⟨mₑ, N, hN, fun e => (hθ e).some, m₃, (hm₃ (Finset.mem_insert_self _ _)).some,
    fun e => (hm₃ (by simp)).some⟩, hinv, htriv⟩

end ModuleStageData

end MMP.CoefficientModels

end
