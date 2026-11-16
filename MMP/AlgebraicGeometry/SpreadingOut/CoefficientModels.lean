module

public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.NoetherianApproximation.ProjectiveImmersionStageModel

/-!
# Spreading out over finitely generated coefficient subalgebras

Let `k₀` be a commutative ring and `K` a commutative `k₀`-algebra. The ring `K` is the filtered
union of its finitely generated `k₀`-subalgebras `R`, so `Spec K` is the cofiltered limit of the
affine schemes `Spec R`, with affine transition morphisms. This is the limit along which data of
finite presentation over `K` are spread out to a finitely generated coefficient ring.

## Main definitions

* `MMP.CoefficientModels.FGSub`: the finitely generated `k₀`-subalgebras of `K`, ordered by
  inclusion; a directed nonempty poset.
* `MMP.CoefficientModels.ringDiagram` and `MMP.CoefficientModels.ringCocone`: the diagram of
  those subalgebras in `CommRingCat` and the cocone on it with apex `K`.
* `MMP.CoefficientModels.specDiagram` and `MMP.CoefficientModels.specCone`: the cofiltered
  diagram `R ↦ Spec R` and its cone with apex `Spec K`.
* `MMP.CoefficientModels.DiagramStageData`: stage data of a model of a finite diagram of
  projectively immersed schemes over a cofiltered limit, with the model
  `MMP.CoefficientModels.DiagramStageData.diagram` at every sufficiently late stage and the
  projections `MMP.CoefficientModels.DiagramStageData.proj` to it.

## Main results

* `MMP.CoefficientModels.isColimitRingCocone`: `K` is the filtered colimit of its finitely
  generated `k₀`-subalgebras.
* `MMP.CoefficientModels.isLimitSpecCone`: `Spec K` is the limit of the `Spec R`.
* `MMP.CoefficientModels.isNoetherianRing_of_fg` and
  `MMP.CoefficientModels.isLocallyNoetherian_specDiagram_obj`: over a Noetherian `k₀`, each stage
  is a Noetherian ring, and its spectrum a locally Noetherian scheme.
* `MMP.CoefficientModels.isLimitLegCone`: for a cofiltered limit `S = lim S_i` and a model `W` of
  `X` over the stage `S_{i₀}`, the scheme `X` is the limit of the base changes of `W` to the
  stages over `i₀`.
* `MMP.CoefficientModels.exists_stage_hom` and `MMP.CoefficientModels.exists_stage_eq`: a
  morphism out of `X` to a scheme of finite presentation over `S_{i₀}` factors through a later
  base change of `W`, and two such factorizations agree at a still later stage.
* `MMP.CoefficientModels.exists_common_projectiveStageModel`: finitely many projectively
  immersed schemes of finite presentation over `S` have models at a common stage.
* `MMP.CoefficientModels.exists_diagramStageData`: a finite diagram of projectively immersed
  schemes of finite presentation over the limit has stage data, whose models keep immersions
  into projective space and closed immersions.
* `MMP.CoefficientModels.exists_diagram_model`: a finite diagram of projectively immersed
  schemes of finite presentation over `S` has a model, with immersions into the same projective
  space and cartesian base change squares, at every sufficiently late stage; closed immersions
  into projective space and closed immersions along the arrows of the diagram stay closed
  immersions in the model (Stacks 01ZP).
* `MMP.CoefficientModels.overPullback_map_of_isPullback` and
  `MMP.CoefficientModels.of_isPullback_overPullback`: moving a property of morphisms between a
  base change given by cartesian squares and the morphism `(Over.pullback g).map f₀`.
* `MMP.CoefficientModels.exists_fgSubalgebra_diagram_model`: the case `S = Spec K` of a
  Noetherian ring, with the stages the spectra of the finitely generated `k₀`-subalgebras `R ⊆ K`.

## Implementation notes

The ring `k₀` may live in a different universe from `K`; the index poset lives in the universe of
`K`, as the subalgebras are subsets of `K`. The colimit is checked directly on elements: an
element `x` of `K` is sent through the stage `k₀[x]`, and any two stages containing `x` give the
same value since both include into their supremum.

The base changes of a stage model `W` over `S_{i₀}` are indexed by `Over i₀` and written as the
fibre products `pullback (D.map m.hom) W.hom` (`MMP.CoefficientModels.stageDiagram`), which is
`AlgebraicGeometry.Scheme.baseChangeDiagram` up to the identity natural isomorphism; stating the
stages this way keeps the fibre products syntactically visible to `rw` and `simp`. A morphism
between base changes of two stage models is recorded by its second component, a morphism into
the second stage model over `S_{i₀}` (`MMP.CoefficientModels.stageLift`), so that moving to a
later stage is precomposition. The diagram model is built over an index category in which
parallel morphisms agree, as for the opposite of the poset of finitely generated subalgebras;
this makes the finitely many stage changes in the construction compatible without bookkeeping.

## References

* [EGA IV₃, §8]
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v

namespace MMP.CoefficientModels

variable (k₀ : Type v) [CommRing k₀] (K : Type u) [CommRing K] [Algebra k₀ K]

/-- The finitely generated `k₀`-subalgebras of `K`, ordered by inclusion. -/
abbrev FGSub := {R : Subalgebra k₀ K // R.FG}

/-- The poset of finitely generated subalgebras is nonempty. -/
instance : Nonempty (FGSub k₀ K) := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

/-- Any two finitely generated subalgebras are contained in a third. -/
instance : IsDirected (FGSub k₀ K) (· ≤ ·) :=
  ⟨fun R S => ⟨⟨R.1 ⊔ S.1, R.2.sup S.2⟩, le_sup_left (a := R.1), le_sup_right (b := S.1)⟩⟩

/-- The finitely generated subalgebra `k₀[s]` generated by a finite set `s`. -/
def adjoinFinset (s : Finset K) : FGSub k₀ K :=
  ⟨Algebra.adjoin k₀ (s : Set K), Subalgebra.fg_adjoin_finset s⟩

/-- A finite set `s` is contained in the subalgebra `k₀[s]`. -/
theorem subset_adjoinFinset (s : Finset K) : (s : Set K) ⊆ (adjoinFinset k₀ K s).1 :=
  Algebra.subset_adjoin

/-- The diagram of finitely generated `k₀`-subalgebras of `K` in `CommRingCat`. -/
def ringDiagram : FGSub k₀ K ⥤ CommRingCat.{u} where
  obj R := CommRingCat.of R.1
  map f := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom f)).toRingHom

/-- The cocone on `MMP.CoefficientModels.ringDiagram` with apex `K`. -/
def ringCocone : Cocone (ringDiagram k₀ K) where
  pt := CommRingCat.of K
  ι :=
    { app R := CommRingCat.ofHom R.1.val.toRingHom
      naturality _ _ _ := rfl }

variable {k₀ K}

/-- The value at `x` of a cocone leg does not depend on the stage containing `x`. -/
theorem cocone_ι_app_eq (s : Cocone (ringDiagram k₀ K)) {R S : FGSub k₀ K} {x : K}
    (hR : x ∈ R.1) (hS : x ∈ S.1) :
    s.ι.app R ⟨x, hR⟩ = s.ι.app S ⟨x, hS⟩ := by
  let T : FGSub k₀ K := ⟨R.1 ⊔ S.1, R.2.sup S.2⟩
  exact (ConcreteCategory.congr_hom (s.w (homOfLE (le_sup_left (a := R.1)) : R ⟶ T))
    ⟨x, hR⟩).symm.trans
    (ConcreteCategory.congr_hom (s.w (homOfLE (le_sup_right (b := S.1)) : S ⟶ T)) ⟨x, hS⟩)

/-- The value of the universal map at an element, through the stage `k₀[x]`. -/
def liftFun (s : Cocone (ringDiagram k₀ K)) (x : K) : s.pt :=
  s.ι.app (adjoinFinset k₀ K {x}) ⟨x, subset_adjoinFinset k₀ K {x} (by simp)⟩

/-- `liftFun s x` is the value at `x` of the leg of `s` at any stage containing `x`. -/
theorem liftFun_eq (s : Cocone (ringDiagram k₀ K)) {R : FGSub k₀ K} {x : K} (hx : x ∈ R.1) :
    liftFun s x = s.ι.app R ⟨x, hx⟩ :=
  cocone_ι_app_eq s _ _

/-- The universal ring map out of `K`. -/
def liftHom (s : Cocone (ringDiagram k₀ K)) : K →+* s.pt where
  toFun := liftFun s
  map_one' := by
    rw [liftFun_eq s (R := ⟨⊥, Subalgebra.fg_bot⟩) (one_mem _)]
    exact (s.ι.app _).hom.map_one
  map_mul' x y := by
    classical
    let R := adjoinFinset k₀ K {x, y}
    have hx : x ∈ R.1 := subset_adjoinFinset k₀ K _ (by simp)
    have hy : y ∈ R.1 := subset_adjoinFinset k₀ K _ (by simp)
    rw [liftFun_eq s (mul_mem hx hy), liftFun_eq s hx, liftFun_eq s hy]
    exact (s.ι.app R).hom.map_mul ⟨x, hx⟩ ⟨y, hy⟩
  map_zero' := by
    rw [liftFun_eq s (R := ⟨⊥, Subalgebra.fg_bot⟩) (zero_mem _)]
    exact (s.ι.app _).hom.map_zero
  map_add' x y := by
    classical
    let R := adjoinFinset k₀ K {x, y}
    have hx : x ∈ R.1 := subset_adjoinFinset k₀ K _ (by simp)
    have hy : y ∈ R.1 := subset_adjoinFinset k₀ K _ (by simp)
    rw [liftFun_eq s (add_mem hx hy), liftFun_eq s hx, liftFun_eq s hy]
    exact (s.ι.app R).hom.map_add ⟨x, hx⟩ ⟨y, hy⟩

variable (k₀ K)

/-- **`K` is the filtered colimit of its finitely generated `k₀`-subalgebras.** -/
def isColimitRingCocone : IsColimit (ringCocone k₀ K) where
  desc s := CommRingCat.ofHom (liftHom s)
  fac s R := by
    ext x
    exact liftFun_eq s x.2
  uniq s m hm := by
    ext (x : K)
    let R := adjoinFinset k₀ K {x}
    have hx : x ∈ R.1 := subset_adjoinFinset k₀ K _ (Finset.mem_singleton_self x)
    exact (ConcreteCategory.congr_hom (hm R) ⟨x, hx⟩).trans (liftFun_eq s hx).symm

/-- The cofiltered diagram `R ↦ Spec R` of spectra of the finitely generated subalgebras. -/
def specDiagram : (FGSub k₀ K)ᵒᵖ ⥤ Scheme.{u} :=
  (ringDiagram k₀ K).op ⋙ Scheme.Spec

/-- The cone on `MMP.CoefficientModels.specDiagram` with apex `Spec K`. -/
def specCone : Cone (specDiagram k₀ K) :=
  Scheme.Spec.mapCone (ringCocone k₀ K).op

/-- The stage of `MMP.CoefficientModels.specDiagram` at `R` is `Spec R`. -/
theorem specDiagram_obj (R : (FGSub k₀ K)ᵒᵖ) :
    (specDiagram k₀ K).obj R = Spec (CommRingCat.of R.unop.1) := rfl

/-- The apex of `MMP.CoefficientModels.specCone` is `Spec K`. -/
theorem specCone_pt : (specCone k₀ K).pt = Spec (CommRingCat.of K) := rfl

/-- The leg of `MMP.CoefficientModels.specCone` at `R` is the spectrum of `R → K`. -/
theorem specCone_π_app (R : (FGSub k₀ K)ᵒᵖ) :
    (specCone k₀ K).π.app R = Spec.map (CommRingCat.ofHom (algebraMap R.unop.1 K)) := rfl

/-- **`Spec K` is the limit of the spectra of its finitely generated `k₀`-subalgebras.** -/
def isLimitSpecCone : IsLimit (specCone k₀ K) :=
  isLimitOfPreserves Scheme.Spec (isColimitRingCocone k₀ K).op

/-- Every stage `Spec R` is affine. -/
instance (R : (FGSub k₀ K)ᵒᵖ) : IsAffine ((specDiagram k₀ K).obj R) := by
  rw [specDiagram_obj]
  infer_instance

/-- The transition morphisms of `MMP.CoefficientModels.specDiagram` are affine. -/
instance {R S : (FGSub k₀ K)ᵒᵖ} (f : R ⟶ S) : IsAffineHom ((specDiagram k₀ K).map f) :=
  isAffineHom_of_isAffine _

/-- Every stage `Spec R` is quasi-compact. -/
instance (R : (FGSub k₀ K)ᵒᵖ) : CompactSpace ((specDiagram k₀ K).obj R) := by
  rw [specDiagram_obj]
  infer_instance

/-- Every stage `Spec R` is quasi-separated. -/
instance (R : (FGSub k₀ K)ᵒᵖ) : QuasiSeparatedSpace ((specDiagram k₀ K).obj R) := by
  rw [specDiagram_obj]
  infer_instance

/-- Over a Noetherian ring, every finitely generated subalgebra is a Noetherian ring. -/
theorem isNoetherianRing_of_fg [IsNoetherianRing k₀] (R : FGSub k₀ K) :
    IsNoetherianRing R.1 :=
  have : Algebra.FiniteType k₀ R.1 := R.1.fg_iff_finiteType.mp R.2
  Algebra.FiniteType.isNoetherianRing k₀ R.1

/-- Over a Noetherian ring, every stage is a locally Noetherian scheme. -/
instance isLocallyNoetherian_specDiagram_obj [IsNoetherianRing k₀] (R : (FGSub k₀ K)ᵒᵖ) :
    IsLocallyNoetherian ((specDiagram k₀ K).obj R) := by
  have := isNoetherianRing_of_fg k₀ K R.unop
  rw [specDiagram_obj]
  infer_instance

/-! ### Stages of a model of a scheme over a cofiltered limit -/

section StageCone

variable {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u}) {i₀ : I} (W : Over (D.obj i₀))

/-- The base change of a stage model `W` to the later stage `m`. -/
abbrev stageObj (m : Over i₀) : Scheme.{u} := pullback (D.map m.hom) W.hom

/-- The transition morphism between base changes of the stage model `W`. -/
def stageMap {m m' : Over i₀} (e : m ⟶ m') : stageObj D W m ⟶ stageObj D W m' :=
  pullback.lift (pullback.fst _ _ ≫ D.map e.left) (pullback.snd _ _) (by
    rw [Category.assoc, ← D.map_comp, Over.w e, pullback.condition])

/-- The first projection of `MMP.CoefficientModels.stageMap` is the transition morphism of `D`. -/
@[reassoc (attr := simp)]
theorem stageMap_fst {m m' : Over i₀} (e : m ⟶ m') :
    stageMap D W e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ D.map e.left :=
  pullback.lift_fst _ _ _

/-- `MMP.CoefficientModels.stageMap` commutes with the projections to `W`. -/
@[reassoc (attr := simp)]
theorem stageMap_snd {m m' : Over i₀} (e : m ⟶ m') :
    stageMap D W e ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The diagram of base changes of the stage model `W` to the stages over `i₀`. -/
@[simps]
def stageDiagram : Over i₀ ⥤ Scheme.{u} where
  obj m := stageObj D W m
  map e := stageMap D W e
  map_id m := pullback.hom_ext (by simp) (by simp)
  map_comp e e' := pullback.hom_ext (by simp) (by simp)

/-- `MMP.CoefficientModels.stageDiagram` is `AlgebraicGeometry.Scheme.baseChangeDiagram`. -/
def stageDiagramIso : stageDiagram D W ≅ Scheme.baseChangeDiagram D i₀ W :=
  NatIso.ofComponents (fun m => Iso.refl _) (fun {m m'} e => by
    simp only [Iso.refl_hom]
    refine pullback.hom_ext ?_ ?_
    · exact (stageMap_fst D W e).trans (Scheme.baseChangeDiagram_map_fst D i₀ W e).symm
    · exact (stageMap_snd D W e).trans (Scheme.baseChangeDiagram_map_snd D i₀ W e).symm)

/-- The stage structure morphisms down to `D.obj i₀`. -/
@[simps]
def stageStructure : stageDiagram D W ⟶ (Functor.const _).obj (D.obj i₀) where
  app m := pullback.snd _ _ ≫ W.hom
  naturality m m' e := by
    dsimp
    rw [Category.comp_id]
    exact stageMap_snd_assoc D W e _

/-- The transition morphism between base changes of `W` is a base change of `D.map e.left`. -/
theorem isPullback_stageMap {m m' : Over i₀} (e : m ⟶ m') :
    IsPullback (stageMap D W e) (pullback.fst (D.map m.hom) W.hom)
      (pullback.fst (D.map m'.hom) W.hom) (D.map e.left) := by
  refine IsPullback.of_right ?_ (stageMap_fst D W e) (IsPullback.of_hasPullback _ _).flip
  rw [stageMap_snd, ← D.map_comp, Over.w e]
  exact (IsPullback.of_hasPullback _ _).flip

/-- If the transition morphisms of `D` are affine, so are those between base changes of `W`. -/
theorem isAffineHom_stageMap [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    {m m' : Over i₀} (e : m ⟶ m') : IsAffineHom (stageMap D W e) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_stageMap D W e).flip
    inferInstance

/-- The transition morphism along an identity is the identity. -/
@[simp]
theorem stageMap_id (m : Over i₀) : stageMap D W (𝟙 m) = 𝟙 _ :=
  (stageDiagram D W).map_id m

/-- The transition morphisms between base changes of `W` compose. -/
theorem stageMap_comp {m m' m'' : Over i₀} (e : m ⟶ m') (e' : m' ⟶ m'') :
    stageMap D W (e ≫ e') = stageMap D W e ≫ stageMap D W e' :=
  (stageDiagram D W).map_comp e e'

variable {D} in
/-- A morphism from a base change of the stage model `W` into a stage model `W'` over the
stage, read at a later stage `m` as a morphism of base changes over `D.obj m`. -/
def stageLift {W W' : Over (D.obj i₀)} {m₁ : Over i₀} (H : stageObj D W m₁ ⟶ W'.left)
    (hH : H ≫ W'.hom = pullback.snd _ _ ≫ W.hom) {m : Over i₀} (b : m ⟶ m₁) :
    stageObj D W m ⟶ stageObj D W' m :=
  pullback.lift (pullback.fst _ _) (stageMap D W b ≫ H) (by
    rw [Category.assoc, hH, stageMap_snd_assoc, pullback.condition])

section StageLift

variable {D} {W W' W'' : Over (D.obj i₀)} {m₁ : Over i₀} (H : stageObj D W m₁ ⟶ W'.left)
  (hH : H ≫ W'.hom = pullback.snd _ _ ≫ W.hom)

/-- `MMP.CoefficientModels.stageLift` commutes with the projections to `D.obj m`. -/
@[reassoc (attr := simp)]
theorem stageLift_fst {m : Over i₀} (b : m ⟶ m₁) :
    stageLift H hH b ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The second component of `MMP.CoefficientModels.stageLift` is `H` after the transition
morphism. -/
@[reassoc (attr := simp)]
theorem stageLift_snd {m : Over i₀} (b : m ⟶ m₁) :
    stageLift H hH b ≫ pullback.snd _ _ = stageMap D W b ≫ H :=
  pullback.lift_snd _ _ _

/-- `MMP.CoefficientModels.stageLift` commutes with the transition morphisms. -/
theorem stageLift_stageMap {m m' : Over i₀} (e : m' ⟶ m) (b : m ⟶ m₁) (b' : m' ⟶ m₁)
    (he : e ≫ b = b') :
    stageLift H hH b' ≫ stageMap D W' e = stageMap D W e ≫ stageLift H hH b := by
  subst he
  refine pullback.hom_ext ?_ ?_
  · simp
  · simp [stageMap_comp]

/-- The square formed by `MMP.CoefficientModels.stageLift` at the stages `m'` and `m` and the
transition morphisms is cartesian. -/
theorem isPullback_stageLift_stageMap {m m' : Over i₀} (e : m' ⟶ m) (b : m ⟶ m₁) :
    IsPullback (stageMap D W e) (stageLift H hH (e ≫ b)) (stageLift H hH b)
      (stageMap D W' e) := by
  refine IsPullback.of_bot ?_ (stageLift_stageMap H hH e b _ rfl).symm
    (isPullback_stageMap D W' e)
  rw [stageLift_fst, stageLift_fst]
  exact isPullback_stageMap D W e

end StageLift

variable (c : Cone D) (X : Over c.pt) (g : X.left ⟶ W.left)
  (hpb : IsPullback g X.hom W.hom (c.π.app i₀))

include hpb in
/-- The compatibility of the two components of `MMP.CoefficientModels.leg` over `D.obj m.left`. -/
theorem leg_condition (m : Over i₀) :
    (X.hom ≫ c.π.app m.left) ≫ D.map m.hom = g ≫ W.hom := by
  rw [Category.assoc, c.w m.hom]
  exact hpb.w.symm

/-- The projection from `X` to the base change of the stage model `W` to a later stage `m`. -/
def leg (m : Over i₀) : X.left ⟶ stageObj D W m :=
  pullback.lift (X.hom ≫ c.π.app m.left) g (leg_condition D W c X g hpb m)

/-- The first component of `MMP.CoefficientModels.leg` is the limit projection. -/
@[reassoc (attr := simp)]
theorem leg_fst (m : Over i₀) :
    leg D W c X g hpb m ≫ pullback.fst _ _ = X.hom ≫ c.π.app m.left :=
  pullback.lift_fst _ _ _

/-- The second component of `MMP.CoefficientModels.leg` is `g`. -/
@[reassoc (attr := simp)]
theorem leg_snd (m : Over i₀) : leg D W c X g hpb m ≫ pullback.snd _ _ = g :=
  pullback.lift_snd _ _ _

/-- `MMP.CoefficientModels.leg` commutes with the transition morphisms. -/
@[reassoc (attr := simp)]
theorem leg_stageMap {m m' : Over i₀} (e : m ⟶ m') :
    leg D W c X g hpb m ≫ stageMap D W e = leg D W c X g hpb m' :=
  pullback.hom_ext (by simp) (by simp)

include hpb in
/-- The projection from `X` to a later base change of its stage model is a base change of the
limit projection. -/
theorem isPullback_leg (m : Over i₀) :
    IsPullback (leg D W c X g hpb m) X.hom (pullback.fst (D.map m.hom) W.hom)
      (c.π.app m.left) := by
  refine IsPullback.of_right ?_ (leg_fst D W c X g hpb m) (IsPullback.of_hasPullback _ _).flip
  rw [leg_snd, c.w m.hom]
  exact hpb

/-- `MMP.CoefficientModels.leg` intertwines a morphism `a : X ⟶ X'` with the
`MMP.CoefficientModels.stageLift` of a morphism `H` compatible with `a`. -/
theorem leg_stageLift {W' : Over (D.obj i₀)} {X' : Over c.pt} {g' : X'.left ⟶ W'.left}
    (hpb' : IsPullback g' X'.hom W'.hom (c.π.app i₀)) (a : X ⟶ X') {m₁ m : Over i₀}
    (H : stageObj D W m₁ ⟶ W'.left) (hH : H ≫ W'.hom = pullback.snd _ _ ≫ W.hom)
    (b : m ⟶ m₁) (ha : leg D W c X g hpb m₁ ≫ H = a.left ≫ g') :
    leg D W c X g hpb m ≫ stageLift H hH b = a.left ≫ leg D W' c X' g' hpb' m := by
  refine pullback.hom_ext ?_ ?_
  · simp
  · simp [ha]

/-- The cone with apex `X` over the diagram of base changes of the stage model `W`. -/
@[simps]
def legCone : Cone (stageDiagram D W) where
  pt := X.left
  π :=
    { app m := leg D W c X g hpb m
      naturality _ _ e := (Category.id_comp _).trans (leg_stageMap D W c X g hpb e).symm }

/-- `X` is the limit of the base changes of its stage model. -/
def isLimitLegCone [IsCofiltered I] (hc : IsLimit c) : IsLimit (legCone D W c X g hpb) := by
  refine (IsLimit.postcomposeHomEquiv (stageDiagramIso D W) _).symm
    (IsLimit.ofIsoLimit (Scheme.isLimitBaseChangeCone D i₀ W c hc)
      (Cone.ext (c' := (Cone.postcompose (stageDiagramIso D W).hom).obj (legCone D W c X g hpb))
        (show (Scheme.baseChangeCone D i₀ W c).pt ≅ X.left from hpb.flip.isoPullback.symm)
        (fun m => ?_)))
  refine pullback.hom_ext ?_ ?_
  · refine (Scheme.baseChangeCone_π_fst D i₀ W c m).trans ?_
    change _ = (hpb.flip.isoPullback.inv ≫ leg D W c X g hpb m ≫ 𝟙 _) ≫ pullback.fst _ _
    simp
  · refine (Scheme.baseChangeCone_π_snd D i₀ W c m).trans ?_
    change _ = (hpb.flip.isoPullback.inv ≫ leg D W c X g hpb m ≫ 𝟙 _) ≫ pullback.snd _ _
    simp

variable [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

/-- A base change of a stage model of finite presentation is quasi-compact. -/
theorem compactSpace_stageObj (hW : FinitePresentation W.hom) (m : Over i₀) :
    CompactSpace (stageObj D W m) := by
  have : QuasiCompact W.hom := hW.2.1
  have : QuasiCompact (pullback.fst (D.map m.hom) W.hom) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback _ _).flip hW.2.1
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst (D.map m.hom) W.hom)

/-- A base change of a stage model of finite presentation is quasi-separated. -/
theorem quasiSeparatedSpace_stageObj (hW : FinitePresentation W.hom) (m : Over i₀) :
    QuasiSeparatedSpace (stageObj D W m) := by
  have : QuasiSeparated W.hom := hW.2.2
  have : QuasiSeparated (pullback.fst (D.map m.hom) W.hom) :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) (IsPullback.of_hasPullback _ _).flip
      hW.2.2
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.map m.hom) W.hom)

include hpb in
/-- **A morphism out of `X` into a scheme locally of finite presentation over the stage factors
through a later base change of the stage model** (Stacks 01ZC). -/
theorem exists_stage_hom (hc : IsLimit c) (hW : FinitePresentation W.hom)
    (W' : Over (D.obj i₀)) [LocallyOfFinitePresentation W'.hom] (a : X.left ⟶ W'.left)
    (ha : a ≫ W'.hom = X.hom ≫ c.π.app i₀) :
    ∃ (m : Over i₀) (h : stageObj D W m ⟶ W'.left),
      leg D W c X g hpb m ≫ h = a ∧ h ≫ W'.hom = pullback.snd _ _ ≫ W.hom := by
  have : EssentiallySmall.{u} (Over i₀) := Scheme.essentiallySmall_over i₀
  have {j k : Over i₀} (e : j ⟶ k) : IsAffineHom ((stageDiagram D W).map e) :=
    isAffineHom_stageMap D W e
  have (m : Over i₀) : CompactSpace ((stageDiagram D W).obj m) := compactSpace_stageObj D W hW m
  have (m : Over i₀) : QuasiSeparatedSpace ((stageDiagram D W).obj m) :=
    quasiSeparatedSpace_stageObj D W hW m
  exact Scheme.exists_π_app_comp_eq_of_essentiallySmall
    (stageDiagram D W) (legCone D W c X g hpb) (isLimitLegCone D W c X g hpb hc)
    (stageStructure D W) W'.hom a (by
      ext m
      simp only [NatTrans.comp_app, Functor.const_obj_obj, legCone_π_app,
        stageStructure_app, Functor.const_map_app]
      exact (leg_snd_assoc D W c X g hpb m W.hom).trans (hpb.w.trans ha.symm))

include hpb in
/-- **Two morphisms out of a later base change of the stage model which agree on `X` agree at a
still later stage** (Stacks 01ZM part (3)). -/
theorem exists_stage_eq (hc : IsLimit c) (hW : FinitePresentation W.hom)
    (W' : Over (D.obj i₀)) [LocallyOfFiniteType W'.hom] {m : Over i₀}
    (h h' : stageObj D W m ⟶ W'.left)
    (hh : h ≫ W'.hom = pullback.snd _ _ ≫ W.hom) (hh' : h' ≫ W'.hom = pullback.snd _ _ ≫ W.hom)
    (heq : leg D W c X g hpb m ≫ h = leg D W c X g hpb m ≫ h') :
    ∃ (m' : Over i₀) (e : m' ⟶ m), stageMap D W e ≫ h = stageMap D W e ≫ h' := by
  have : EssentiallySmall.{u} (Over i₀) := Scheme.essentiallySmall_over i₀
  have {j k : Over i₀} (e : j ⟶ k) : IsAffineHom ((stageDiagram D W).map e) :=
    isAffineHom_stageMap D W e
  have (m : Over i₀) : CompactSpace ((stageDiagram D W).obj m) := compactSpace_stageObj D W hW m
  exact Scheme.exists_hom_comp_eq_comp_of_essentiallySmall
    (stageDiagram D W) (legCone D W c X g hpb) (isLimitLegCone D W c X g hpb hc)
    (stageStructure D W) W'.hom h h' hh.symm hh'.symm heq

end StageCone

/-! ### Transferring properties of morphisms along base change squares -/

section Transfer

variable {S T : Scheme.{u}} (g : T ⟶ S) {X₀ Y₀ : Over S} (f₀ : X₀ ⟶ Y₀)

/-- If `f` is a base change of `f₀` along `g`, in the sense of two cartesian squares over `g`,
then `(Over.pullback g).map f₀` has every isomorphism-invariant property `P` that `f` has. -/
theorem overPullback_map_of_isPullback (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X Y : Scheme.{u}} (f : X ⟶ Y) {pX : X ⟶ X₀.left} {xT : X ⟶ T} {pY : Y ⟶ Y₀.left}
    {yT : Y ⟶ T} (hX : IsPullback pX xT X₀.hom g) (hY : IsPullback pY yT Y₀.hom g)
    (h1 : f ≫ pY = pX ≫ f₀.left) (h2 : f ≫ yT = xT) (hf : P f) :
    P ((Over.pullback g).map f₀).left := by
  refine (MorphismProperty.arrow_mk_iso_iff P (Arrow.isoMk hX.isoPullback hY.isoPullback ?_)).mp hf
  refine pullback.hom_ext ?_ ?_
  · simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Category.assoc,
      IsPullback.isoPullback_hom_fst, overPullback_map_left_fst,
      IsPullback.isoPullback_hom_fst_assoc]
    exact h1.symm
  · simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Category.assoc,
      IsPullback.isoPullback_hom_snd, overPullback_map_left_snd, IsPullback.isoPullback_hom_snd]
    exact h2.symm

/-- A base change of `f₀` along a morphism lying over `g` has every property stable under base
change which `(Over.pullback g).map f₀` has. -/
theorem of_isPullback_overPullback (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (hF : P ((Over.pullback g).map f₀).left)
    {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') (u : X' ⟶ X₀.left) (v : Y' ⟶ Y₀.left) (y : Y' ⟶ T)
    (hsq : IsPullback u f' f₀.left v) (hy : v ≫ Y₀.hom = y ≫ g) : P f' := by
  let τ : Y' ⟶ pullback Y₀.hom g := pullback.lift v y hy
  have hx : u ≫ X₀.hom = (f' ≫ y) ≫ g := by
    rw [← Over.w f₀, ← Category.assoc, hsq.w, Category.assoc, hy, Category.assoc]
  let σ : X' ⟶ pullback X₀.hom g := pullback.lift u (f' ≫ y) hx
  have hp : σ ≫ ((Over.pullback g).map f₀).left = f' ≫ τ := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, overPullback_map_left_fst, σ, τ, pullback.lift_fst_assoc,
        pullback.lift_fst]
      exact hsq.w
    · rw [Category.assoc, overPullback_map_left_snd]
      simp only [σ, τ, pullback.lift_snd, Category.assoc]
  have H : IsPullback (σ ≫ pullback.fst X₀.hom g) f' f₀.left (τ ≫ pullback.fst Y₀.hom g) := by
    rw [show σ ≫ pullback.fst X₀.hom g = u from pullback.lift_fst _ _ _,
      show τ ≫ pullback.fst Y₀.hom g = v from pullback.lift_fst _ _ _]
    exact hsq
  exact MorphismProperty.of_isPullback
    (IsPullback.of_right H hp (overPullback_isPullback g X₀ Y₀ f₀)) hF

end Transfer

/-! ### A common stage for finitely many projectively immersed schemes -/

section CommonStage

variable {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

/-- **Finitely many projectively immersed schemes of finite presentation over the limit have
models at a common stage.** -/
theorem exists_common_projectiveStageModel (hc : IsLimit c) (n : ℕ) {ι : Type*} [Finite ι]
    (X : ι → Over c.pt) (j : ∀ a, (X a).left ⟶ projectiveSpaceOver n c.pt)
    (hj : ∀ a, j a ≫ (projectiveSpaceOver n c.pt ↘ c.pt) = (X a).hom)
    [∀ a, IsImmersion (j a)] (hfp : ∀ a, FinitePresentation (X a).hom) :
    ∃ (i₀ : I) (W : ι → Over (D.obj i₀)) (g : ∀ a, (X a).left ⟶ (W a).left)
      (jW : ∀ a, (W a).left ⟶ projectiveSpaceOver n (D.obj i₀)),
      ∀ a, FinitePresentation (W a).hom ∧ IsPullback (g a) (X a).hom (W a).hom (c.π.app i₀) ∧
        jW a ≫ (projectiveSpaceOver n (D.obj i₀) ↘ D.obj i₀) = (W a).hom ∧
        g a ≫ jW a = j a ≫ projectiveSpaceOverMap n (c.π.app i₀) ∧ IsImmersion (jW a) := by
  classical
  have : EssentiallySmall.{u} I := essentiallySmallSelf I
  have hstage : ∀ a, ∃ (k : I) (Xk : Scheme.{u}) (fk : Xk ⟶ D.obj k) (g' : (X a).left ⟶ Xk)
      (jk : Xk ⟶ projectiveSpaceOver n (D.obj k)),
      FinitePresentation fk ∧ IsPullback g' (X a).hom fk (c.π.app k) ∧
      jk ≫ (projectiveSpaceOver n (D.obj k) ↘ D.obj k) = fk ∧
      g' ≫ jk = j a ≫ projectiveSpaceOverMap n (c.π.app k) ∧ IsImmersion jk := fun a => by
    obtain ⟨i, Xi, fi, g, ji, hfi, hpb, hji, hgj⟩ :=
      exists_projectiveStageModel D c (X a).hom n (j a) (hj a) hc (hfp a)
    exact exists_projectiveStageModel_isImmersion D c (X a).hom n (j a) (hj a) hc fi g ji hfi hpb
      hji hgj
  choose k Xk fk g' jk hfk hpbk hjk hgjk himk using hstage
  have := Fintype.ofFinite ι
  obtain ⟨i₀, hi₀⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  have e : ∀ a, i₀ ⟶ k a := fun a => (hi₀ (Finset.mem_image_of_mem k (Finset.mem_univ a))).some
  have hw : ∀ a, ((X a).hom ≫ c.π.app i₀) ≫ D.map (e a) = g' a ≫ fk a := fun a => by
    rw [Category.assoc, c.w]
    exact (hpbk a).w.symm
  let gm : ∀ a, (X a).left ⟶ pullback (D.map (e a)) (fk a) :=
    fun a => pullback.lift _ _ (hw a)
  have hstep : ∀ a, ∃ jm : pullback (D.map (e a)) (fk a) ⟶ projectiveSpaceOver n (D.obj i₀),
      FinitePresentation (pullback.fst (D.map (e a)) (fk a)) ∧
      IsPullback (gm a) (X a).hom (pullback.fst (D.map (e a)) (fk a)) (c.π.app i₀) ∧
      jm ≫ (projectiveSpaceOver n (D.obj i₀) ↘ D.obj i₀) = pullback.fst (D.map (e a)) (fk a) ∧
      gm a ≫ jm = j a ≫ projectiveSpaceOverMap n (c.π.app i₀) ∧ IsImmersion jm := fun a => by
    have := himk a
    obtain ⟨jm, h1, h2, h3, h4, -, h6⟩ := exists_projectiveStageModel_baseChange D c (X a).hom n
      (j a) (hj a) (e a) (fk a) (g' a) (jk a) (hfk a) (hpbk a) (hjk a) (hgjk a) (gm a)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    exact ⟨jm, h1, h2, h3, h4, MorphismProperty.of_isPullback h6 inferInstance⟩
  choose jm hjm using hstep
  exact ⟨i₀, fun a => Over.mk (pullback.fst (D.map (e a)) (fk a)), gm, jm, hjm⟩

/-- The base change of a projective stage model `jW` to a later stage `m` is a projective stage
model, whose immersion is a base change of `jW`. -/
theorem exists_projectiveStageModel_stageObj (n : ℕ) {i₀ : I} {W : Over (D.obj i₀)}
    (hW : FinitePresentation W.hom) {X : Over c.pt} (ι : X.left ⟶ projectiveSpaceOver n c.pt)
    (hιover : ι ≫ (projectiveSpaceOver n c.pt ↘ c.pt) = X.hom) {g : X.left ⟶ W.left}
    (hpb : IsPullback g X.hom W.hom (c.π.app i₀)) (jW : W.left ⟶ projectiveSpaceOver n (D.obj i₀))
    (hjW : jW ≫ (projectiveSpaceOver n (D.obj i₀) ↘ D.obj i₀) = W.hom)
    (hgj : g ≫ jW = ι ≫ projectiveSpaceOverMap n (c.π.app i₀)) [IsImmersion jW] (m : Over i₀) :
    ∃ jm : stageObj D W m ⟶ projectiveSpaceOver n (D.obj m.left),
      FinitePresentation (pullback.fst (D.map m.hom) W.hom) ∧
      jm ≫ (projectiveSpaceOver n (D.obj m.left) ↘ D.obj m.left) =
        pullback.fst (D.map m.hom) W.hom ∧
      leg D W c X g hpb m ≫ jm = ι ≫ projectiveSpaceOverMap n (c.π.app m.left) ∧
      IsImmersion jm ∧
      IsPullback (pullback.snd (D.map m.hom) W.hom) jm jW
        (projectiveSpaceOverMap n (D.map m.hom)) := by
  obtain ⟨jm, h₁, -, h₃, h₄, -, h₆⟩ := exists_projectiveStageModel_baseChange D c X.hom n ι
    hιover m.hom W.hom g jW hW hpb hjW hgj (leg D W c X g hpb m) (leg_fst _ _ _ _ _ _ _)
    (leg_snd _ _ _ _ _ _ _)
  exact ⟨jm, h₁, h₃, h₄, MorphismProperty.of_isPullback h₆ inferInstance, h₆⟩

/-- **Closed immersions into projective space stay closed immersions at a later stage** (Stacks
01ZP): for a stage model `jW` of an immersion `ι` into projective space, there is a stage from
which on every base change of `jW` is a closed immersion if `ι` is. -/
theorem exists_stage_isClosedImmersion_projective (hc : IsLimit c) (n : ℕ) {i₀ : I}
    {W : Over (D.obj i₀)} (hW : FinitePresentation W.hom) {X : Over c.pt}
    (ι : X.left ⟶ projectiveSpaceOver n c.pt)
    (hιover : ι ≫ (projectiveSpaceOver n c.pt ↘ c.pt) = X.hom) {g : X.left ⟶ W.left}
    (hpb : IsPullback g X.hom W.hom (c.π.app i₀)) {jW : W.left ⟶ projectiveSpaceOver n (D.obj i₀)}
    (hjW : jW ≫ (projectiveSpaceOver n (D.obj i₀) ↘ D.obj i₀) = W.hom)
    (hgj : g ≫ jW = ι ≫ projectiveSpaceOverMap n (c.π.app i₀)) :
    ∃ mc : Over i₀, ∀ {m : Over i₀} (_ : m ⟶ mc)
      (jm : stageObj D W m ⟶ projectiveSpaceOver n (D.obj m.left)),
      IsPullback (pullback.snd (D.map m.hom) W.hom) jm jW
        (projectiveSpaceOverMap n (D.map m.hom)) →
      IsClosedImmersion ι → IsClosedImmersion jm := by
  by_cases hι : IsClosedImmersion ι
  swap
  · exact ⟨Over.mk (𝟙 i₀), fun _ _ _ h => absurd h hι⟩
  have : EssentiallySmall.{u} I := essentiallySmallSelf I
  have hP := ProjectiveQuot.finitePresentation_projectiveSpaceOver n (D.obj i₀)
  have : QuasiCompact (projectiveSpaceOver n (D.obj i₀) ↘ D.obj i₀) := hP.2.1
  have : QuasiSeparated (projectiveSpaceOver n (D.obj i₀) ↘ D.obj i₀) := hP.2.2
  let P : Over (D.obj i₀) := Over.mk (projectiveSpaceOver n (D.obj i₀) ↘ D.obj i₀)
  have : CompactSpace P.left :=
    QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceOver n (D.obj i₀) ↘ D.obj i₀)
  have : QuasiSeparatedSpace P.left :=
    quasiSeparatedSpace_of_quasiSeparated (projectiveSpaceOver n (D.obj i₀) ↘ D.obj i₀)
  let f : W ⟶ P := Over.homMk jW hjW
  have : QuasiCompact W.hom := hW.2.1
  have : QuasiSeparated W.hom := hW.2.2
  have : CompactSpace W.left := QuasiCompact.compactSpace_of_compactSpace W.hom
  have : QuasiSeparatedSpace W.left := quasiSeparatedSpace_of_quasiSeparated W.hom
  have : LocallyOfFinitePresentation W.hom := hW.1
  have : LocallyOfFiniteType f.left := by
    have : LocallyOfFiniteType (f.left ≫ P.hom) := by
      rw [Over.w f]
      infer_instance
    exact locallyOfFiniteType_of_comp f.left P.hom
  have : IsClosedImmersion ((Over.pullback (c.π.app i₀)).map f).left :=
    overPullback_map_of_isPullback (c.π.app i₀) f @IsClosedImmersion ι hpb
      (isPullback_projectiveSpaceOverMap n (c.π.app i₀)) hgj.symm hιover hι
  obtain ⟨i, hi, hci⟩ := exists_isClosedImmersion_baseChange_of_isLimit D c hc i₀ W P f
  refine ⟨Over.mk hi, fun {m} e jm hjm _ => ?_⟩
  refine of_isPullback_overPullback (D.map (Over.mk hi).hom) f @IsClosedImmersion hci jm
    (pullback.snd _ _) (projectiveSpaceOverMap n (D.map m.hom))
    ((projectiveSpaceOver n (D.obj m.left) ↘ D.obj m.left) ≫ D.map e.left) hjm ?_
  rw [Category.assoc, ← D.map_comp, Over.w e]
  exact projectiveSpaceOverMap_fst n (D.map m.hom)

/-- **Closed immersions along a morphism stay closed immersions at a later stage** (Stacks
01ZP): for a model `H` over the stage `m₁` of a morphism `a`, there is a stage below `m₁` from
which on the induced morphisms of base changes are closed immersions if `a` is one. -/
theorem exists_stage_isClosedImmersion_stageLift (hc : IsLimit c) {i₀ : I}
    {W W' : Over (D.obj i₀)} (hW : FinitePresentation W.hom) (hW' : FinitePresentation W'.hom)
    {X X' : Over c.pt} {g : X.left ⟶ W.left} {g' : X'.left ⟶ W'.left}
    (hpb : IsPullback g X.hom W.hom (c.π.app i₀))
    (hpb' : IsPullback g' X'.hom W'.hom (c.π.app i₀)) (a : X ⟶ X') {m₁ : Over i₀}
    (H : stageObj D W m₁ ⟶ W'.left) (hH : H ≫ W'.hom = pullback.snd _ _ ≫ W.hom)
    (ha : leg D W c X g hpb m₁ ≫ H = a.left ≫ g') :
    ∃ (ic : I) (hic : ic ⟶ m₁.left), ∀ {m : Over i₀} (b : m ⟶ m₁) (e : m.left ⟶ ic),
      b.left = e ≫ hic → IsClosedImmersion a.left → IsClosedImmersion (stageLift H hH b) := by
  by_cases hx : IsClosedImmersion a.left
  swap
  · exact ⟨m₁.left, 𝟙 _, fun _ _ _ h => absurd h hx⟩
  have : EssentiallySmall.{u} I := essentiallySmallSelf I
  let Z : Over (D.obj m₁.left) := Over.mk (pullback.fst (D.map m₁.hom) W.hom)
  let Z' : Over (D.obj m₁.left) := Over.mk (pullback.fst (D.map m₁.hom) W'.hom)
  let f : Z ⟶ Z' := Over.homMk (stageLift H hH (𝟙 m₁)) (stageLift_fst _ _ _)
  have : CompactSpace Z.left := compactSpace_stageObj D W hW m₁
  have : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_stageObj D W hW m₁
  have : CompactSpace Z'.left := compactSpace_stageObj D W' hW' m₁
  have : QuasiSeparatedSpace Z'.left := quasiSeparatedSpace_stageObj D W' hW' m₁
  have : LocallyOfFinitePresentation W'.hom := hW'.1
  have : LocallyOfFinitePresentation W.hom := hW.1
  have : LocallyOfFiniteType f.left := by
    have : LocallyOfFiniteType (f.left ≫ Z'.hom) := by
      rw [Over.w f]
      dsimp [Z]
      infer_instance
    exact locallyOfFiniteType_of_comp f.left Z'.hom
  have : IsClosedImmersion ((Over.pullback (c.π.app m₁.left)).map f).left :=
    overPullback_map_of_isPullback (c.π.app m₁.left) f @IsClosedImmersion a.left
      (isPullback_leg D W c X g hpb m₁) (isPullback_leg D W' c X' g' hpb' m₁)
      (leg_stageLift D W c X g hpb hpb' a H hH (𝟙 m₁) ha).symm (Over.w a) hx
  obtain ⟨ic, hic, hci⟩ := exists_isClosedImmersion_baseChange_of_isLimit D c hc m₁.left Z Z' f
  refine ⟨ic, hic, fun {m} b e hb _ => ?_⟩
  have hsq := isPullback_stageLift_stageMap H hH b (𝟙 m₁)
  rw [Category.comp_id] at hsq
  refine of_isPullback_overPullback (D.map hic) f @IsClosedImmersion hci (stageLift H hH b)
    (stageMap D W b) (stageMap D W' b) (pullback.fst (D.map m.hom) W'.hom ≫ D.map e) hsq ?_
  change stageMap D W' b ≫ pullback.fst _ _ = _
  rw [stageMap_fst, hb, D.map_comp]
  exact (Category.assoc _ _ _).symm

/-- **The arrows of a finite diagram over the limit have models at a common stage**: for stage
models `W j` of the objects, every arrow `φ` is modelled over a common later stage `m₁` by a
morphism `H φ` into `W j'`. -/
theorem exists_stage_arrowModels (hc : IsLimit c) {J : Type u} [SmallCategory J]
    [FinCategory J] (X : J ⥤ Over c.pt) {i₀ : I} (W : J → Over (D.obj i₀))
    (g : ∀ j, (X.obj j).left ⟶ (W j).left) (hWfp : ∀ j, FinitePresentation (W j).hom)
    (hpb : ∀ j, IsPullback (g j) (X.obj j).hom (W j).hom (c.π.app i₀)) :
    ∃ (m₁ : Over i₀) (H : ∀ {j j' : J} (_ : j ⟶ j'), stageObj D (W j) m₁ ⟶ (W j').left),
      (∀ {j j'} (φ : j ⟶ j'), H φ ≫ (W j').hom = pullback.snd _ _ ≫ (W j).hom) ∧
      ∀ {j j'} (φ : j ⟶ j'),
        leg D (W j) c (X.obj j) (g j) (hpb j) m₁ ≫ H φ = (X.map φ).left ≫ g j' := by
  classical
  let Arr := Σ (j : J) (j' : J), (j ⟶ j')
  have hfac : ∀ x : Arr, ∃ (m : Over i₀) (h : stageObj D (W x.1) m ⟶ (W x.2.1).left),
      leg D (W x.1) c (X.obj x.1) (g x.1) (hpb x.1) m ≫ h = (X.map x.2.2).left ≫ g x.2.1 ∧
      h ≫ (W x.2.1).hom = pullback.snd _ _ ≫ (W x.1).hom := fun x => by
    have : LocallyOfFinitePresentation (W x.2.1).hom := (hWfp _).1
    refine exists_stage_hom D (W x.1) c (X.obj x.1) (g x.1) (hpb x.1) hc (hWfp _) (W x.2.1) _ ?_
    rw [Category.assoc, (hpb x.2.1).w, ← Category.assoc, Over.w]
  choose mx hx hx₁ hx₂ using hfac
  obtain ⟨m₁, hm₁⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image mx)
  have b₁ : ∀ x, m₁ ⟶ mx x := fun x =>
    (hm₁ (Finset.mem_image_of_mem _ (Finset.mem_univ x))).some
  let H : ∀ x : Arr, stageObj D (W x.1) m₁ ⟶ (W x.2.1).left :=
    fun x => stageMap D _ (b₁ x) ≫ hx x
  have hHleg : ∀ x : Arr, leg D (W x.1) c (X.obj x.1) (g x.1) (hpb x.1) m₁ ≫ H x =
      (X.map x.2.2).left ≫ g x.2.1 := fun x => by
    simp only [H, leg_stageMap_assoc, hx₁]
  have hHw : ∀ x : Arr, H x ≫ (W x.2.1).hom = pullback.snd _ _ ≫ (W x.1).hom := fun x => by
    simp only [H, Category.assoc, hx₂, stageMap_snd_assoc]
  exact ⟨m₁, fun {j j'} φ => H ⟨j, j', φ⟩, fun {j j'} φ => hHw ⟨j, j', φ⟩,
    fun {j j'} φ => hHleg ⟨j, j', φ⟩⟩

/-- **The models of two composable arrows compose to the model of the composite at a later
stage**, by Stacks 01ZM part (3). -/
theorem exists_stageLift_comp_eq (hc : IsLimit c) {i₀ : I} {W W' W'' : Over (D.obj i₀)}
    (hW : FinitePresentation W.hom) (hW'' : FinitePresentation W''.hom) {X X' X'' : Over c.pt}
    {g : X.left ⟶ W.left} {g' : X'.left ⟶ W'.left} {g'' : X''.left ⟶ W''.left}
    (hpb : IsPullback g X.hom W.hom (c.π.app i₀))
    (hpb' : IsPullback g' X'.hom W'.hom (c.π.app i₀)) (a : X ⟶ X') (a' : X' ⟶ X'')
    {m₁ : Over i₀} (H₁ : stageObj D W m₁ ⟶ W'.left)
    (hH₁ : H₁ ≫ W'.hom = pullback.snd _ _ ≫ W.hom) (ha₁ : leg D W c X g hpb m₁ ≫ H₁ = a.left ≫ g')
    (H₂ : stageObj D W' m₁ ⟶ W''.left) (hH₂ : H₂ ≫ W''.hom = pullback.snd _ _ ≫ W'.hom)
    (ha₂ : leg D W' c X' g' hpb' m₁ ≫ H₂ = a'.left ≫ g'')
    (H₃ : stageObj D W m₁ ⟶ W''.left) (hH₃ : H₃ ≫ W''.hom = pullback.snd _ _ ≫ W.hom)
    (ha₃ : leg D W c X g hpb m₁ ≫ H₃ = (a ≫ a').left ≫ g'') :
    ∃ (m : Over i₀) (e : m ⟶ m₁),
      stageMap D W e ≫ stageLift H₁ hH₁ (𝟙 m₁) ≫ H₂ = stageMap D W e ≫ H₃ := by
  have : LocallyOfFinitePresentation W''.hom := hW''.1
  refine exists_stage_eq D W c X g hpb hc hW W'' _ _ ?_ hH₃ ?_
  · simp only [Category.assoc, hH₂, stageLift_snd_assoc, hH₁, stageMap_id, Category.id_comp]
  · rw [← Category.assoc, leg_stageLift D W c X g hpb hpb' a H₁ hH₁ (𝟙 m₁) ha₁, Category.assoc,
      ha₂, ha₃]
    simp

end CommonStage

section DiagramStageData

variable {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u}) (c : Cone D) (n : ℕ)
  {J : Type u} [SmallCategory J] (X : J ⥤ Over c.pt)
  (ι : ∀ j, (X.obj j).left ⟶ projectiveSpaceOver n c.pt)

/-- The stage data of a model of a diagram `X` of projectively immersed schemes over the limit
`c.pt`: models `W j` of the objects at a stage `i₀`, immersed into projective space by `jW j`,
models `H φ` of the arrows over a later stage `m₁`, and a still later stage `m₂` from which on
the models of the arrows respect identities and composition. -/
structure DiagramStageData where
  /-- The stage at which the objects are modelled. -/
  i₀ : I
  /-- The models of the objects. -/
  W : J → Over (D.obj i₀)
  /-- The projections from the objects to their models. -/
  g : ∀ j, (X.obj j).left ⟶ (W j).left
  /-- The immersions of the models into projective space. -/
  jW : ∀ j, (W j).left ⟶ projectiveSpaceOver n (D.obj i₀)
  /-- The models are of finite presentation over the stage. -/
  finitePresentation (j : J) : FinitePresentation (W j).hom
  /-- Each object is the base change of its model. -/
  isPullback (j : J) : IsPullback (g j) (X.obj j).hom (W j).hom (c.π.app i₀)
  /-- The immersions lie over the stage. -/
  jW_over (j : J) : jW j ≫ (projectiveSpaceOver n (D.obj i₀) ↘ D.obj i₀) = (W j).hom
  /-- The projections are compatible with the immersions. -/
  g_jW (j : J) : g j ≫ jW j = ι j ≫ projectiveSpaceOverMap n (c.π.app i₀)
  /-- The models of the objects are immersed into projective space. -/
  isImmersion_jW (j : J) : IsImmersion (jW j)
  /-- The stage over which the arrows are modelled. -/
  m₁ : Over i₀
  /-- The models of the arrows, recorded by their second components. -/
  H {j j' : J} (φ : j ⟶ j') : stageObj D (W j) m₁ ⟶ (W j').left
  /-- The models of the arrows lie over the stage model. -/
  H_w {j j' : J} (φ : j ⟶ j') : H φ ≫ (W j').hom = pullback.snd _ _ ≫ (W j).hom
  /-- The models of the arrows restrict to the given arrows. -/
  leg_H {j j' : J} (φ : j ⟶ j') :
    leg D (W j) c (X.obj j) (g j) (isPullback j) m₁ ≫ H φ = (X.map φ).left ≫ g j'
  /-- The stage from which on the models of the arrows form a diagram. -/
  m₂ : Over i₀
  /-- The transition from `m₂` to `m₁`. -/
  b₂ : m₂ ⟶ m₁
  /-- From `m₂` on, the model of an identity is the projection. -/
  H_id (j : J) : stageMap D (W j) b₂ ≫ H (𝟙 j) = stageMap D (W j) b₂ ≫ pullback.snd _ _
  /-- From `m₂` on, the models of the arrows compose. -/
  H_comp {j j' j'' : J} (φ : j ⟶ j') (ψ : j' ⟶ j'') :
    stageMap D (W j) b₂ ≫ stageLift (H φ) (H_w φ) (𝟙 m₁) ≫ H ψ =
      stageMap D (W j) b₂ ≫ H (φ ≫ ψ)

namespace DiagramStageData

variable {D c n X ι} (d : DiagramStageData D c n X ι)

/-- The model of the diagram at a stage `m` later than `d.m₂`. -/
def diagram {m : Over d.i₀} (bm : m ⟶ d.m₂) : J ⥤ Over (D.obj m.left) where
  obj j := Over.mk (pullback.fst (D.map m.hom) (d.W j).hom)
  map {j j'} φ := Over.homMk (stageLift (d.H φ) (d.H_w φ) (bm ≫ d.b₂)) (stageLift_fst _ _ _)
  map_id j := by
    ext1
    refine pullback.hom_ext ?_ ?_
    · simp
    · simp only [Over.homMk_left, Over.id_left, stageLift_snd, Category.id_comp, stageMap_comp,
        Category.assoc, d.H_id, stageMap_snd]
  map_comp {j j' j''} φ ψ := by
    ext1
    refine pullback.hom_ext ?_ ?_
    · simp
    · simp only [Over.homMk_left, Over.comp_left, Category.assoc, stageLift_snd]
      rw [← Category.assoc (stageLift _ _ (bm ≫ d.b₂)),
        stageLift_stageMap (d.H φ) (d.H_w φ) (bm ≫ d.b₂) (𝟙 d.m₁) (bm ≫ d.b₂)
          (Category.comp_id _)]
      simp only [stageMap_comp, Category.assoc, d.H_comp]

variable {m : Over d.i₀} (bm : m ⟶ d.m₂)

/-- The object of the model at `j` is the base change of `d.W j` to `m`. -/
@[simp]
theorem diagram_obj_left (j : J) : ((d.diagram bm).obj j).left = stageObj D (d.W j) m := rfl

/-- The structure morphism of the model at `j` is the first projection. -/
@[simp]
theorem diagram_obj_hom (j : J) :
    ((d.diagram bm).obj j).hom = pullback.fst (D.map m.hom) (d.W j).hom := rfl

/-- The model of an arrow `φ` is the `MMP.CoefficientModels.stageLift` of `d.H φ`. -/
@[simp]
theorem diagram_map_left {j j' : J} (φ : j ⟶ j') :
    ((d.diagram bm).map φ).left = stageLift (d.H φ) (d.H_w φ) (bm ≫ d.b₂) := rfl

/-- The model of the diagram does not depend on the chosen morphism to `d.m₂`. -/
theorem diagram_congr [∀ i j : I, Subsingleton (i ⟶ j)] (bm' : m ⟶ d.m₂) :
    d.diagram bm = d.diagram bm' := by
  rw [Subsingleton.elim bm bm']

variable (m) in
/-- The projection from the given diagram to its model at the stage `m`. -/
def proj (j : J) : (X.obj j).left ⟶ stageObj D (d.W j) m :=
  leg D (d.W j) c (X.obj j) (d.g j) (d.isPullback j) m

/-- The projections to the models commute with the arrows of the diagram and their models. -/
@[reassoc]
theorem proj_map {j j' : J} (φ : j ⟶ j') :
    (X.map φ).left ≫ d.proj m j' = d.proj m j ≫ ((d.diagram bm).map φ).left :=
  (leg_stageLift D (d.W j) c (X.obj j) (d.g j) (d.isPullback j) (d.isPullback j') (X.map φ)
    (d.H φ) (d.H_w φ) (bm ≫ d.b₂) (d.leg_H φ)).symm

variable (m) in
/-- The projection to the model at `j` is a base change of the limit projection. -/
theorem isPullback_proj (j : J) :
    IsPullback (d.proj m j) (X.obj j).hom (pullback.fst (D.map m.hom) (d.W j).hom)
      (c.π.app m.left) :=
  isPullback_leg D (d.W j) c (X.obj j) (d.g j) (d.isPullback j) m

variable (m) in
/-- The projections to the models commute with the transition morphisms. -/
@[reassoc]
theorem proj_stageMap {m' : Over d.i₀} (e : m ⟶ m') (j : J) :
    d.proj m j ≫ stageMap D (d.W j) e = d.proj m' j :=
  leg_stageMap D (d.W j) c (X.obj j) (d.g j) (d.isPullback j) e

variable (m) in
/-- The projections to the models commute with the models of the arrows. -/
@[reassoc]
theorem proj_stageLift (b : m ⟶ d.m₁) {j j' : J} (φ : j ⟶ j') :
    d.proj m j ≫ stageLift (d.H φ) (d.H_w φ) b = (X.map φ).left ≫ d.proj m j' :=
  leg_stageLift D (d.W j) c (X.obj j) (d.g j) (d.isPullback j) (d.isPullback j') (X.map φ)
    (d.H φ) (d.H_w φ) b (d.leg_H φ)

/-- The stage data `d` with the stage `d.m₂` moved to a later stage `m`. -/
def restrict (e : m ⟶ d.m₂) : DiagramStageData D c n X ι where
  __ := d
  m₂ := m
  b₂ := e ≫ d.b₂
  H_id j := by simp only [stageMap_comp, Category.assoc, d.H_id]
  H_comp φ ψ := by simp only [stageMap_comp, Category.assoc, d.H_comp]

end DiagramStageData

end DiagramStageData

/-! ### A model of a finite diagram of projectively immersed schemes -/

section DiagramModel

variable {I : Type u} [SmallCategory I] [IsCofiltered I] [∀ i j : I, Subsingleton (i ⟶ j)]
  (D : I ⥤ Scheme.{u}) (c : Cone D)
  [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

/-- **A finite diagram of projectively immersed schemes of finite presentation over the limit
has stage data**: models of the objects and arrows at a common stage, which respect identities
and composition at a later stage. -/
theorem nonempty_diagramStageData (hc : IsLimit c) (n : ℕ) {J : Type u} [SmallCategory J]
    [FinCategory J] (X : J ⥤ Over c.pt) (ι : ∀ j, (X.obj j).left ⟶ projectiveSpaceOver n c.pt)
    [∀ j, IsImmersion (ι j)]
    (hιover : ∀ j, ι j ≫ (projectiveSpaceOver n c.pt ↘ c.pt) = (X.obj j).hom)
    (hfp : ∀ j, FinitePresentation (X.obj j).hom) :
    Nonempty (DiagramStageData D c n X ι) := by
  classical
  obtain ⟨i₀, W, g, jW, hW⟩ := exists_common_projectiveStageModel D c hc n X.obj ι hιover hfp
  choose hWfp hpb hjW hgj himm using hW
  obtain ⟨m₁, H, hHw, hHleg⟩ := exists_stage_arrowModels D c hc X W g hWfp hpb
  have hid : ∀ j : J, ∃ (m : Over i₀) (e : m ⟶ m₁),
      stageMap D (W j) e ≫ H (𝟙 j) = stageMap D (W j) e ≫ pullback.snd _ _ := fun j => by
    have : LocallyOfFinitePresentation (W j).hom := (hWfp j).1
    exact exists_stage_eq D (W j) c (X.obj j) (g j) (hpb j) hc (hWfp j) (W j) _ _ (hHw (𝟙 j))
      rfl (by rw [hHleg (𝟙 j), leg_snd]; simp)
  have hcomp : ∀ y : Σ (j : J) (j' : J) (j'' : J), (j ⟶ j') × (j' ⟶ j''),
      ∃ (m : Over i₀) (e : m ⟶ m₁),
        stageMap D (W y.1) e ≫ stageLift (H y.2.2.2.1) (hHw _) (𝟙 m₁) ≫ H y.2.2.2.2 =
          stageMap D (W y.1) e ≫ H (y.2.2.2.1 ≫ y.2.2.2.2) := fun y => by
    obtain ⟨j, j', j'', φ, ψ⟩ := y
    exact exists_stageLift_comp_eq D c hc (hWfp j) (hWfp j'') (hpb j) (hpb j') (X.map φ)
      (X.map ψ) (H φ) (hHw φ) (hHleg φ) (H ψ) (hHw ψ) (hHleg ψ) (H (φ ≫ ψ)) (hHw _)
      (by rw [hHleg, Functor.map_comp])
  choose mj ej hej using hid
  choose my ey hey using hcomp
  obtain ⟨m₂, hm₂⟩ := IsCofiltered.inf_objs_exists
    (insert m₁ (Finset.univ.image mj ∪ Finset.univ.image my))
  have b₂ : m₂ ⟶ m₁ := (hm₂ (Finset.mem_insert_self _ _)).some
  have dj : ∀ j, m₂ ⟶ mj j := fun j => (hm₂ (by simp)).some
  have dy : ∀ y, m₂ ⟶ my y := fun y => (hm₂ (by simp)).some
  exact ⟨{
    i₀ := i₀, W := W, g := g, jW := jW, finitePresentation := hWfp, isPullback := hpb,
    jW_over := hjW, g_jW := hgj, isImmersion_jW := himm, m₁ := m₁, H := H, H_w := hHw,
    leg_H := hHleg, m₂ := m₂, b₂ := b₂,
    H_id := fun j => by
      rw [show b₂ = dj j ≫ ej j from Subsingleton.elim _ _, stageMap_comp, Category.assoc,
        Category.assoc, hej]
    H_comp := fun {j j' j''} φ ψ => by
      rw [show b₂ = dy ⟨j, j', j'', φ, ψ⟩ ≫ ey ⟨j, j', j'', φ, ψ⟩ from Subsingleton.elim _ _,
        stageMap_comp, Category.assoc, Category.assoc, hey ⟨j, j', j'', φ, ψ⟩] }⟩

/-- **Stage data of a finite diagram of projectively immersed schemes of finite presentation,
with immersions of the models at every later stage** (EGA IV₃ 8.8.2, Stacks 01ZM): there is stage
data `d` such that at every stage `m` later than `d.m₂`, the base changes of the models carry
immersions into the same projective space, compatible with the projections `d.proj` and with the
given immersions `ι`; closed immersions into projective space, and along the arrows of the
diagram, stay closed immersions (Stacks 01ZP). -/
theorem exists_diagramStageData (hc : IsLimit c) (n : ℕ) {J : Type u} [SmallCategory J]
    [FinCategory J] (X : J ⥤ Over c.pt) (ι : ∀ j, (X.obj j).left ⟶ projectiveSpaceOver n c.pt)
    [∀ j, IsImmersion (ι j)]
    (hιover : ∀ j, ι j ≫ (projectiveSpaceOver n c.pt ↘ c.pt) = (X.obj j).hom)
    (hfp : ∀ j, FinitePresentation (X.obj j).hom) :
    ∃ d : DiagramStageData D c n X ι, ∀ (m : Over d.i₀) (bm : m ⟶ d.m₂),
      ∃ ιY : ∀ j, stageObj D (d.W j) m ⟶ projectiveSpaceOver n (D.obj m.left),
      (∀ j, IsImmersion (ιY j)) ∧
      (∀ j, ιY j ≫ (projectiveSpaceOver n (D.obj m.left) ↘ D.obj m.left) =
        pullback.fst (D.map m.hom) (d.W j).hom) ∧
      (∀ j, d.proj m j ≫ ιY j = ι j ≫ projectiveSpaceOverMap n (c.π.app m.left)) ∧
      (∀ j, FinitePresentation (pullback.fst (D.map m.hom) (d.W j).hom)) ∧
      (∀ j, IsClosedImmersion (ι j) → IsClosedImmersion (ιY j)) ∧
      (∀ {j j'} (φ : j ⟶ j'), IsClosedImmersion (X.map φ).left →
        IsClosedImmersion ((d.diagram bm).map φ).left) := by
  classical
  obtain ⟨d⟩ := nonempty_diagramStageData D c hc n X ι hιover hfp
  choose mc hmc using fun j => exists_stage_isClosedImmersion_projective D c hc n
    (d.finitePresentation j) (ι j) (hιover j) (d.isPullback j) (d.jW_over j) (d.g_jW j)
  choose ic hic hicx using fun x : Σ (j : J) (j' : J), (j ⟶ j') =>
    exists_stage_isClosedImmersion_stageLift D c hc (d.finitePresentation x.1)
      (d.finitePresentation x.2.1) (d.isPullback x.1) (d.isPullback x.2.1) (X.map x.2.2)
      (d.H x.2.2) (d.H_w x.2.2) (d.leg_H x.2.2)
  let mcx : (Σ (j : J) (j' : J), (j ⟶ j')) → Over d.i₀ := fun x => Over.mk (hic x ≫ d.m₁.hom)
  obtain ⟨m₂, hm₂⟩ := IsCofiltered.inf_objs_exists
    (insert d.m₂ (Finset.univ.image mc ∪ Finset.univ.image mcx))
  have b : m₂ ⟶ d.m₂ := (hm₂ (Finset.mem_insert_self _ _)).some
  have dc : ∀ j, m₂ ⟶ mc j := fun j => (hm₂ (by simp)).some
  have dcx : ∀ x, m₂ ⟶ mcx x := fun x => (hm₂ (by simp)).some
  refine ⟨d.restrict b, fun m bm => ?_⟩
  have := d.isImmersion_jW
  choose jm hfpm hover hleg himm hpbm using fun j => exists_projectiveStageModel_stageObj D c n
    (d.finitePresentation j) (ι j) (hιover j) (d.isPullback j) (d.jW j) (d.jW_over j) (d.g_jW j) m
  exact ⟨jm, himm, hover, hleg, hfpm, fun j hj => hmc j (bm ≫ dc j) (jm j) (hpbm j) hj,
    fun {j j'} φ hφ => hicx ⟨j, j', φ⟩ (bm ≫ (d.restrict b).b₂) (bm ≫ dcx ⟨j, j', φ⟩).left
      (Subsingleton.elim _ _) hφ⟩

/-- **A finite diagram of projectively immersed schemes of finite presentation over the limit
has a model at every sufficiently late stage** (EGA IV₃ 8.8.2, Stacks 01ZM): a diagram of the
same shape over the stage, with immersions into the same projective space, whose base change is
the given diagram with its immersions. -/
theorem exists_diagram_model (hc : IsLimit c) (n : ℕ) {J : Type u} [SmallCategory J]
    [FinCategory J] (X : J ⥤ Over c.pt) (ι : ∀ j, (X.obj j).left ⟶ projectiveSpaceOver n c.pt)
    [∀ j, IsImmersion (ι j)]
    (hιover : ∀ j, ι j ≫ (projectiveSpaceOver n c.pt ↘ c.pt) = (X.obj j).hom)
    (hfp : ∀ j, FinitePresentation (X.obj j).hom) :
    ∃ i₂ : I, ∀ (i : I) (_ : i ⟶ i₂), ∃ (Y : J ⥤ Over (D.obj i))
      (ιY : ∀ j, (Y.obj j).left ⟶ projectiveSpaceOver n (D.obj i))
      (p : ∀ j, (X.obj j).left ⟶ (Y.obj j).left),
      (∀ {j j'} (φ : j ⟶ j'), (X.map φ).left ≫ p j' = p j ≫ (Y.map φ).left) ∧
      (∀ j, IsImmersion (ιY j)) ∧
      (∀ j, ιY j ≫ (projectiveSpaceOver n (D.obj i) ↘ D.obj i) = (Y.obj j).hom) ∧
      (∀ j, IsPullback (p j) (X.obj j).hom (Y.obj j).hom (c.π.app i)) ∧
      (∀ j, p j ≫ ιY j = ι j ≫ projectiveSpaceOverMap n (c.π.app i)) ∧
      (∀ j, FinitePresentation (Y.obj j).hom) ∧
      (∀ j, IsClosedImmersion (ι j) → IsClosedImmersion (ιY j)) ∧
      (∀ {j j'} (φ : j ⟶ j'), IsClosedImmersion (X.map φ).left →
        IsClosedImmersion (Y.map φ).left) := by
  obtain ⟨d, hd⟩ := exists_diagramStageData D c hc n X ι hιover hfp
  refine ⟨d.m₂.left, fun i e => ?_⟩
  let m : Over d.i₀ := Over.mk (e ≫ d.m₂.hom)
  let bm : m ⟶ d.m₂ := Over.homMk e
  obtain ⟨ιY, h1, h2, h3, h4, h5, h6⟩ := hd m bm
  exact ⟨d.diagram bm, ιY, d.proj m, d.proj_map bm, h1, h2, d.isPullback_proj m, h3, h4, h5, h6⟩

end DiagramModel

/-! ### Models over finitely generated coefficient subalgebras of a field -/

section Coefficients

/-- A scheme immersed into projective space over a Noetherian ring is of finite presentation
over it. -/
theorem finitePresentation_of_isImmersion_projectiveSpaceOver (K : Type u) [CommRing K]
    [IsNoetherianRing K] {X : Scheme.{u}} (n : ℕ) (ι : X ⟶ projectiveSpaceOver n (Spec (.of K)))
    [IsImmersion ι] :
    FinitePresentation (ι ≫ (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))) := by
  have hP := ProjectiveQuot.finitePresentation_projectiveSpaceOver n (Spec (.of K))
  have : LocallyOfFinitePresentation (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) :=
    hP.1
  have : QuasiCompact (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) := hP.2.1
  have : IsLocallyNoetherian (projectiveSpaceOver n (Spec (.of K))) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))
  have : CompactSpace (projectiveSpaceOver n (Spec (.of K))) :=
    QuasiCompact.compactSpace_of_compactSpace
      (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))
  have : IsNoetherian (projectiveSpaceOver n (Spec (.of K))) := ⟨⟩
  have : TopologicalSpace.NoetherianSpace X := ι.isEmbedding.noetherianSpace
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- **A finite diagram of schemes immersed into projective space over a Noetherian ring `K`
has a model over every sufficiently large finitely generated `k₀`-subalgebra `R ⊆ K`**
(EGA IV₃ 8.8.2): a diagram of `R`-schemes of finite presentation of the same shape, immersed
into `ℙⁿ_R`, whose base change along `Spec K ⟶ Spec R` is the given diagram with its
immersions. -/
theorem exists_fgSubalgebra_diagram_model (k₀ : Type v) [CommRing k₀] (K : Type u) [CommRing K]
    [IsNoetherianRing K] [Algebra k₀ K] {J : Type u} [SmallCategory J] [FinCategory J]
    (X : J ⥤ Over (Spec (.of K))) (n : ℕ)
    (ι : ∀ j, (X.obj j).left ⟶ projectiveSpaceOver n (Spec (.of K))) [∀ j, IsImmersion (ι j)]
    (hιover : ∀ j, ι j ≫ (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) =
      (X.obj j).hom) :
    ∃ R₂ : FGSub k₀ K, ∀ R : FGSub k₀ K, R₂ ≤ R →
      ∃ (Y : J ⥤ Over (Spec (.of R.1)))
        (ιY : ∀ j, (Y.obj j).left ⟶ projectiveSpaceOver n (Spec (.of R.1)))
        (p : ∀ j, (X.obj j).left ⟶ (Y.obj j).left),
        (∀ {j j'} (φ : j ⟶ j'), (X.map φ).left ≫ p j' = p j ≫ (Y.map φ).left) ∧
        (∀ j, IsImmersion (ιY j)) ∧
        (∀ j, ιY j ≫ (projectiveSpaceOver n (Spec (.of R.1)) ↘ Spec (.of R.1)) =
          (Y.obj j).hom) ∧
        (∀ j, IsPullback (p j) (X.obj j).hom (Y.obj j).hom
          (Spec.map (CommRingCat.ofHom (algebraMap R.1 K)))) ∧
        (∀ j, ι j ≫ projectiveSpaceOver.toIntegralAtUniverse n _ =
          p j ≫ ιY j ≫ projectiveSpaceOver.toIntegralAtUniverse n _) ∧
        (∀ j, FinitePresentation (Y.obj j).hom) ∧
        (∀ j, IsClosedImmersion (ι j) → IsClosedImmersion (ιY j)) ∧
        (∀ {j j'} (φ : j ⟶ j'), IsClosedImmersion (X.map φ).left →
          IsClosedImmersion (Y.map φ).left) := by
  have hfp : ∀ j, FinitePresentation (X.obj j).hom := fun j => by
    rw [← hιover j]
    exact finitePresentation_of_isImmersion_projectiveSpaceOver K n (ι j)
  have : ∀ j, @IsImmersion _ (projectiveSpaceOver n (specCone k₀ K).pt) (ι j) :=
    fun j => inferInstanceAs (IsImmersion (ι j))
  obtain ⟨i₂, h⟩ := exists_diagram_model (specDiagram k₀ K) (specCone k₀ K)
    (isLimitSpecCone k₀ K) n (J := J) X ι hιover hfp
  refine ⟨i₂.unop, fun R hR => ?_⟩
  obtain ⟨Y, ιY, p, hp, himm, hover, hpb, hι, hYfp, hcl, hclm⟩ := h (op R) (homOfLE hR).op
  refine ⟨Y, ιY, p, hp, himm, hover, hpb, fun j => ?_, hYfp, hcl, hclm⟩
  exact (congrArg (ι j ≫ ·)
    (projectiveSpaceOverMap_snd n ((specCone k₀ K).π.app (op R))).symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (hι j).symm).trans
        (Category.assoc _ _ _)))

end Coefficients

end MMP.CoefficientModels

end
