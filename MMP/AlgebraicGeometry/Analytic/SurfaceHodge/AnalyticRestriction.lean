module

public import MMP.AlgebraicGeometry.Analytic.GAGA.Differentials
public import MMP.AlgebraicGeometry.Analytic.JacobianLogarithm.EtaleCoordinates
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem

/-!
# Restriction of analytic functions and of `H¹(X^an, 𝒪)` along a morphism

Let `i : C ⟶ X` be a morphism of schemes over `ℂ`, smooth of some relative dimension, separated
and quasi-compact. Then `X^an` and `C^an` are complex manifolds whose sheaves of holomorphic
functions are `𝒪_{X^an}` and `𝒪_{C^an}`, and the realization `i^an : C^an → X^an` is
holomorphic, because in the algebraic charts of `X^an` its coordinates are regular functions on
`C`. Composing with `i^an` is a morphism of sheaves of rings
`𝒪_{X^an} ⟶ (i^an)_* 𝒪_{C^an}`, and with the pullback on sheaf cohomology it induces the
restriction `H¹(X^an, 𝒪) → H¹(C^an, 𝒪)`.

## Main definitions

* `MMP.Analytic.SurfaceHodge.HolomorphicModel`: a complex manifold structure on `X^an` with
  algebraic charts, together with an isomorphism of `𝒪_{X^an}` with its sheaf of holomorphic
  functions that is evaluation on regular functions.
* `MMP.Analytic.SurfaceHodge.analyticPullback`: `𝒪_{X^an} ⟶ (i^an)_* 𝒪_{C^an}`, composition with
  `i^an`.
* `MMP.Analytic.SurfaceHodge.sheafHOnePullback`: the map `H¹(T, A) → H¹(T', B)` induced by a
  morphism `A ⟶ f_* B` along a continuous map `f : T' ⟶ T`.
* `MMP.Analytic.SurfaceHodge.analyticRestrictionH1`: the restriction
  `H¹(X^an, 𝒪) → H¹(C^an, 𝒪)`.

## Main results

* `MMP.Analytic.SurfaceHodge.nonempty_holomorphicModel`: a holomorphic model exists for a
  separated quasi-compact scheme smooth of relative dimension `n` over `ℂ`.
* `MMP.Analytic.SurfaceHodge.contMDiff_realize`: `i^an` is holomorphic.
* `MMP.Analytic.SurfaceHodge.analyticPullback_apply`: the pullback of a section is its
  composition with `i^an`, read as holomorphic functions.
* `MMP.Analytic.SurfaceHodge.HolomorphicModel.theta_apply_eq`: a section of `𝒪_{X^an}` read as a
  holomorphic function does not depend on the model.
* `MMP.Analytic.SurfaceHodge.analyticRestrictionH1_eq`: the restriction on `H¹` is the one built
  from any pair of holomorphic models; `exists_analyticRestrictionH1_eq` for smooth schemes.

## Implementation notes

The restriction on `H¹` is defined for every morphism over `ℂ`; it is the map built from
holomorphic models of `X^an` and `C^an` when both exist, and `0` otherwise. It does not depend on
the models (`analyticRestrictionH1_eq`), because a section of `𝒪_{X^an}` read as a holomorphic
function in any model is the function of its values.

## References

* [J.-P. Serre, *Géométrie algébrique et géométrie analytique*]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace Topology
open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.ComplexPoints
open scoped Manifold ContDiff

namespace MMP.Analytic.SurfaceHodge

attribute [local instance] hasExt_of_enoughInjectives
attribute [local implicit_reducible] TopCat.Sheaf

/-- The additive sheaf of `𝒪_{X^an}`. -/
noncomputable abbrev analyticO {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) :
    Sheaf (Opens.grothendieckTopology (space sX)) AddCommGrpCat.{0} :=
  (sheafCompose (Opens.grothendieckTopology (space sX)) (forget₂ RingCat AddCommGrpCat)).obj
    (ringCatSheaf sX)

/-- A *holomorphic model* of `X^an`: a complex manifold structure on `X(ℂ)` whose charts are
algebraic coordinates, and an isomorphism of `𝒪_{X^an}` with the sheaf of holomorphic functions
that is evaluation on regular functions. -/
structure HolomorphicModel {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) where
  /-- the complex dimension -/
  n : ℕ
  /-- the charts -/
  cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)
  /-- the charts form a complex manifold -/
  isManifold : letI := cs; IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX)
  /-- each chart is given by regular functions minus constants -/
  atlas_coords : letI := cs; ∀ φ ∈ atlas (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX),
    ∃ (W : X.Opens) (z : Fin n → Γ(X, W)) (c : Fin n → ℂ) (hW : φ.source ⊆ chart W),
      ∀ y (hy : y ∈ φ.source) (j : Fin n), φ y j = evalHom W ⟨y, hW hy⟩ (z j) - c j
  /-- `𝒪_{X^an}` is the sheaf of holomorphic functions -/
  Θ : letI := cs; structureSheaf sX ≅ 𝒪[n, ComplexPoints sX]
  /-- `Θ` sends a regular function to the function of its values -/
  hΘ : letI := cs; ∀ (V : X.Opens) (g : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
    Θ.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) g) y =
      evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g

/-- A separated quasi-compact scheme smooth of relative dimension `n` over `ℂ` has a holomorphic
model. -/
theorem nonempty_holomorphicModel {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [SmoothOfRelativeDimension n sX] [IsSeparated sX] [QuasiCompact sX] :
    Nonempty (HolomorphicModel sX) := by
  haveI : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  obtain ⟨cs, hm, -, -, hat, Θ, hΘ, -⟩ :=
    analytification_smooth_differentials_of_smoothOfRelativeDimension (n := n) sX 0
      (Mori.DivisorWithCoeffs.isSNC_zero sX)
  exact ⟨⟨n, cs, hm, hat, Θ, hΘ⟩⟩

section Pullback

variable {X C : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sC : C ⟶ Spec (.of ℂ)}

/-- Evaluating the pullback of a regular function at a `ℂ`-point is evaluating the function at
the image point. -/
theorem evalHom_appLE_realize (i : C ⟶ X) (hi : i ≫ sX = sC) {W : X.Opens} {V : C.Opens}
    (h : V ≤ i ⁻¹ᵁ W) (y : chart (sX := sC) V) (f : Γ(X, W)) :
    evalHom V y ((i.appLE W V h).hom f) =
      evalHom W ⟨realize i hi y.1, mem_chart_iff.2 (h (mem_chart_iff.1 y.2))⟩ f := by
  simp only [evalHom, RingHom.coe_comp, Function.comp_apply]
  rw [← CommRingCat.comp_apply (i.appLE W V h), Scheme.Hom.appLE_comp_appLE]
  rfl

variable {nX nC : ℕ} [csX : ChartedSpace (EuclideanSpace ℂ (Fin nX)) (ComplexPoints sX)]
  [csC : ChartedSpace (EuclideanSpace ℂ (Fin nC)) (ComplexPoints sC)]

/-- The pullback of a regular function along `i` is holomorphic on `C^an`. -/
theorem exists_contMDiffAt_evalHom_realize (i : C ⟶ X) (hi : i ≫ sX = sC)
    (ΘC : structureSheaf sC ≅ 𝒪[nC, ComplexPoints sC])
    (hΘC : ∀ (V : C.Opens) (g : Γ(C, V)) (y : (Opens.map (toSchemeHom sC)).obj V),
      ΘC.hom.hom.app (op _) ((analytificationHom sC).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
    {W : X.Opens} (f : Γ(X, W)) (y : ComplexPoints sC) (hy : realize i hi y ∈ chart W) :
    ∃ g : ComplexPoints sC → ℂ, ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin nC)) 𝓘(ℂ) ∞ g y ∧
      ∀ y' (hy' : realize i hi y' ∈ chart W), g y' = evalHom W ⟨_, hy'⟩ f := by
  let V : C.Opens := i ⁻¹ᵁ W
  let U : Opens (space sC) := (Opens.map (toSchemeHom sC)).obj V
  have hU : ∀ y', y' ∈ U ↔ realize i hi y' ∈ chart W := fun y' => by
    rw [mem_chart_iff]
    exact Iff.rfl
  let a : Γ(C, V) := (i.appLE W V le_rfl).hom f
  let S := ΘC.hom.hom.app (op U) ((analytificationHom sC).hom.c.app (op V) a)
  have hS : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin nC)) 𝓘(ℂ) ∞ (S : U → ℂ) :=
    smoothSheaf.contMDiff_section (IM := 𝓘(ℂ, EuclideanSpace ℂ (Fin nC))) (I := 𝓘(ℂ))
      (N := ℂ) (U := op U) S
  classical
  refine ⟨fun y' => if h : y' ∈ U then S ⟨y', h⟩ else 0, ?_, fun y' hy' => ?_⟩
  · have hyU : y ∈ U := (hU y).2 hy
    refine contMDiffAt_subtype_iff (U := U) (x := ⟨y, hyU⟩) |>.1 ?_
    refine (hS ⟨y, hyU⟩).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    simp only [dif_pos x.2]
  · have hy'U : y' ∈ U := (hU y').2 hy'
    simp only [dif_pos hy'U]
    exact (hΘC V a ⟨y', hy'U⟩).trans
      (evalHom_appLE_realize i hi le_rfl ⟨y', mem_chart_iff.2 hy'U⟩ f)

/-- **The realization of a morphism is holomorphic**, for the algebraic charts. -/
theorem contMDiff_realize (i : C ⟶ X) (hi : i ≫ sX = sC)
    (hat : ∀ φ ∈ atlas (EuclideanSpace ℂ (Fin nX)) (ComplexPoints sX),
      ∃ (W : X.Opens) (z : Fin nX → Γ(X, W)) (c : Fin nX → ℂ) (hW : φ.source ⊆ chart W),
        ∀ y (hy : y ∈ φ.source) (j : Fin nX), φ y j = evalHom W ⟨y, hW hy⟩ (z j) - c j)
    (ΘC : structureSheaf sC ≅ 𝒪[nC, ComplexPoints sC])
    (hΘC : ∀ (V : C.Opens) (g : Γ(C, V)) (y : (Opens.map (toSchemeHom sC)).obj V),
      ΘC.hom.hom.app (op _) ((analytificationHom sC).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g) :
    ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin nC)) 𝓘(ℂ, EuclideanSpace ℂ (Fin nX)) ∞
      (realize i hi) := by
  intro y
  rw [contMDiffAt_iff_target]
  refine ⟨(continuous_realize i hi).continuousAt, ?_⟩
  set φ := chartAt (EuclideanSpace ℂ (Fin nX)) (realize i hi y)
  obtain ⟨W, z, c, hW, hφ⟩ := hat φ (chart_mem_atlas _ _)
  have hy : realize i hi y ∈ chart W := hW (mem_chart_source _ _)
  choose g hg hgv using fun j => exists_contMDiffAt_evalHom_realize i hi ΘC hΘC (z j) y hy
  let A : (Fin nX → ℂ) → EuclideanSpace ℂ (Fin nX) :=
    fun v => (EuclideanSpace.equiv (Fin nX) ℂ).symm (v - c)
  have hA : ContDiff ℂ ∞ A :=
    (EuclideanSpace.equiv (Fin nX) ℂ).symm.contDiff.comp (contDiff_id.sub contDiff_const)
  have hG : ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin nC)) 𝓘(ℂ, EuclideanSpace ℂ (Fin nX)) ∞
      (fun y' => A (fun j => g j y')) y :=
    hA.contMDiff.contMDiffAt.comp y
      ((contMDiffAt_pi_space (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin nC)))
        (φ := fun y' j => g j y')).2 hg)
  refine hG.congr_of_eventuallyEq ?_
  filter_upwards [(continuous_realize i hi).continuousAt.preimage_mem_nhds
    (φ.open_source.mem_nhds (mem_chart_source _ _))] with y' hy'
  rw [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_apply, Function.comp_apply, id]
  have hgy : (fun j => g j y') = fun j => evalHom W ⟨_, hW hy'⟩ (z j) :=
    funext fun j => hgv j y' (hW hy')
  ext j
  rw [hφ _ hy' j]
  simp only [A, hgy]
  rfl

/-- **Pullback of analytic functions** along `i^an`: the morphism `𝒪_{X^an} ⟶ (i^an)_* 𝒪_{C^an}`
which, read as holomorphic functions, is composition with `i^an`. -/
noncomputable def analyticPullback (i : C ⟶ X) (hi : i ≫ sX = sC)
    (hf : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin nC)) 𝓘(ℂ, EuclideanSpace ℂ (Fin nX)) ∞
      (realize i hi))
    (ΘX : structureSheaf sX ≅ 𝒪[nX, ComplexPoints sX])
    (ΘC : structureSheaf sC ≅ 𝒪[nC, ComplexPoints sC]) :
    structureSheaf sX ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{0} (analyticMap i hi)).obj (structureSheaf sC) :=
  CategoryStruct.comp ΘX.hom <| CategoryStruct.comp
    (ContMDiff.smoothSheafCommRingHom (IM := 𝓘(ℂ, EuclideanSpace ℂ (Fin nC)))
      (IP := 𝓘(ℂ, EuclideanSpace ℂ (Fin nX))) (I := 𝓘(ℂ)) (M := ComplexPoints sC)
      (P := ComplexPoints sX) (R := ℂ) (f := realize i hi) (hf := hf))
    ((TopCat.Sheaf.pushforward CommRingCat.{0} (analyticMap i hi)).map ΘC.inv)

/-- The pullback of a section, read as a holomorphic function, is its composition with `i^an`. -/
theorem analyticPullback_apply (i : C ⟶ X) (hi : i ≫ sX = sC)
    (hf : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin nC)) 𝓘(ℂ, EuclideanSpace ℂ (Fin nX)) ∞
      (realize i hi))
    (ΘX : structureSheaf sX ≅ 𝒪[nX, ComplexPoints sX])
    (ΘC : structureSheaf sC ≅ 𝒪[nC, ComplexPoints sC]) (W : Opens (space sX))
    (s : (structureSheaf sX).obj.obj (op W))
    (y : (Opens.map (analyticMap i hi)).obj W) :
    ΘC.hom.hom.app (op ((Opens.map (analyticMap i hi)).obj W))
        ((analyticPullback i hi hf ΘX ΘC).hom.app (op W) s) y =
      ΘX.hom.hom.app (op W) s ⟨realize i hi y.1, y.2⟩ := by
  have e : (analyticPullback i hi hf ΘX ΘC).hom.app (op W) s =
      ΘC.inv.hom.app (op ((Opens.map (analyticMap i hi)).obj W))
        ((ContMDiff.smoothSheafCommRingHom (IM := 𝓘(ℂ, EuclideanSpace ℂ (Fin nC)))
          (IP := 𝓘(ℂ, EuclideanSpace ℂ (Fin nX))) (I := 𝓘(ℂ)) (M := ComplexPoints sC)
          (P := ComplexPoints sX) (R := ℂ) (f := realize i hi) (hf := hf)).hom.app (op W)
          (ΘX.hom.hom.app (op W) s)) := rfl
  rw [e]
  erw [MMP.JacobianLogarithm.Fam.theta_inv_hom_apply]
  rfl

end Pullback

section SheafH

/-- The map `H¹(T, A) → H¹(T', B)` induced by a morphism `θ : A ⟶ f_* B` along a continuous map
`f : T' ⟶ T`: pullback on cohomology followed by the adjoint `f⁻¹ A ⟶ B` of `θ`. -/
noncomputable def sheafHOnePullback {T T' : TopCat.{0}} (f : T' ⟶ T)
    {A : TopCat.Sheaf AddCommGrpCat.{0} T} {B : TopCat.Sheaf AddCommGrpCat.{0} T'}
    (θ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj B) :
    Sheaf.H A 1 →+ Sheaf.H B 1 :=
  ((MMP.JacobianLogarithm.extIso T).inv.app A ≫
    sheafCohomologyPullback f A ((1 : ℕ) : ℤ) ≫
    (sheafCohomology T' ((1 : ℕ) : ℤ)).map
      (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).homEquiv A B).symm θ) ≫
    (MMP.JacobianLogarithm.extIso T').hom.app B).hom

end SheafH

section Restriction

variable {X C : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sC : C ⟶ Spec (.of ℂ)}

/-- The pullback `𝒪_{X^an} ⟶ (i^an)_* 𝒪_{C^an}` of additive sheaves built from holomorphic
models. -/
noncomputable def analyticPullbackOfModel (MX : HolomorphicModel sX) (MC : HolomorphicModel sC)
    (i : C ⟶ X) (hi : i ≫ sX = sC) :
    analyticO sX ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap i hi)).obj
      (analyticO sC) :=
  letI := MX.cs
  letI := MC.cs
  (sheafCompose _ (forget₂ RingCat AddCommGrpCat)).map
    ((sheafCompose _ (forget₂ CommRingCat RingCat)).map
      (analyticPullback i hi (contMDiff_realize i hi MX.atlas_coords MC.Θ MC.hΘ) MX.Θ MC.Θ))

/-- The restriction `H¹(X^an, 𝒪) → H¹(C^an, 𝒪)` built from holomorphic models. -/
noncomputable def analyticRestrictionH1OfModel (MX : HolomorphicModel sX)
    (MC : HolomorphicModel sC) (i : C ⟶ X) (hi : i ≫ sX = sC) :
    Sheaf.H (analyticO sX) 1 →+ Sheaf.H (analyticO sC) 1 :=
  sheafHOnePullback (analyticMap i hi) (analyticPullbackOfModel MX MC i hi)

open Classical in
/-- **Restriction of `H¹(𝒪)` of analytifications** along a morphism `i : C ⟶ X` over `ℂ`: `H¹`
of the pullback of analytic functions `𝒪_{X^an} ⟶ (i^an)_* 𝒪_{C^an}`, followed by the pullback
to `C^an`. It is defined when `X^an` and `C^an` have holomorphic models (for instance, for
separated quasi-compact schemes smooth over `ℂ`), and is `0` otherwise. -/
noncomputable def analyticRestrictionH1 (i : C ⟶ X) (hi : i ≫ sX = sC) :
    Sheaf.H (analyticO sX) 1 →+ Sheaf.H (analyticO sC) 1 :=
  if h : Nonempty (HolomorphicModel sX) ∧ Nonempty (HolomorphicModel sC) then
    analyticRestrictionH1OfModel h.1.some h.2.some i hi
  else 0

/-- A section of `𝒪_{X^an}` read as a holomorphic function does not depend on the model. -/
theorem HolomorphicModel.theta_apply_eq [LocallyOfFiniteType sX] (M M' : HolomorphicModel sX)
    {W : Opens (space sX)} (t : (structureSheaf sX).obj.obj (op W)) (y : W) :
    (letI := M.cs; M.Θ.hom.hom.app (op W) t y) = (letI := M'.cs; M'.Θ.hom.hom.app (op W) t y) := by
  obtain ⟨c, hc⟩ := exists_chart_mem (sX := sX) y.1
  letI := M.cs
  letI := M'.cs
  rw [MMP.JacobianLogarithm.Fam.theta_apply_eq_stalkEval M.Θ M.hΘ W t y c hc,
    MMP.JacobianLogarithm.Fam.theta_apply_eq_stalkEval M'.Θ M'.hΘ W t y c hc]

/-- Two sections of `𝒪_{X^an}` with the same holomorphic function in a model are equal. -/
theorem HolomorphicModel.ext (M : HolomorphicModel sX) {W : Opens (space sX)}
    {a b : (structureSheaf sX).obj.obj (op W)}
    (h : ∀ y : W, (letI := M.cs; M.Θ.hom.hom.app (op W) a y) =
      (letI := M.cs; M.Θ.hom.hom.app (op W) b y)) : a = b := by
  letI := M.cs
  rw [← MMP.JacobianLogarithm.Fam.theta_hom_inv_apply M.Θ W a,
    ← MMP.JacobianLogarithm.Fam.theta_hom_inv_apply M.Θ W b]
  congr 1
  exact Subtype.ext (funext h)

/-- The pullback of analytic functions does not depend on the holomorphic models. -/
theorem analyticPullbackOfModel_eq [LocallyOfFiniteType sX] [LocallyOfFiniteType sC]
    (MX MX' : HolomorphicModel sX) (MC MC' : HolomorphicModel sC) (i : C ⟶ X)
    (hi : i ≫ sX = sC) :
    analyticPullbackOfModel MX MC i hi = analyticPullbackOfModel MX' MC' i hi := by
  suffices h : (letI := MX.cs; letI := MC.cs;
      analyticPullback i hi (contMDiff_realize i hi MX.atlas_coords MC.Θ MC.hΘ) MX.Θ MC.Θ) =
    (letI := MX'.cs; letI := MC'.cs;
      analyticPullback i hi (contMDiff_realize i hi MX'.atlas_coords MC'.Θ MC'.hΘ) MX'.Θ MC'.Θ) by
    unfold analyticPullbackOfModel
    rw [h]
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W => ?_))
  ext s
  refine MC.ext fun y => ?_
  letI := MX.cs
  letI := MC.cs
  letI := MX'.cs
  letI := MC'.cs
  have hf := contMDiff_realize i hi MX.atlas_coords MC.Θ MC.hΘ
  have hf' := contMDiff_realize i hi MX'.atlas_coords MC'.Θ MC'.hΘ
  have h1 := analyticPullback_apply i hi hf MX.Θ MC.Θ W.unop s y
  have h2 := analyticPullback_apply i hi hf' MX'.Θ MC'.Θ W.unop s y
  have h3 := HolomorphicModel.theta_apply_eq MX MX' s ⟨realize i hi y.1, y.2⟩
  have h4 := HolomorphicModel.theta_apply_eq MC MC'
    ((analyticPullback i hi hf' MX'.Θ MC'.Θ).hom.app (op W.unop) s) y
  exact h1.trans (h3.trans (h2.symm.trans h4.symm))

/-- **The restriction on `H¹` is the one of any holomorphic models.** -/
theorem analyticRestrictionH1_eq [LocallyOfFiniteType sX] [LocallyOfFiniteType sC]
    (MX : HolomorphicModel sX) (MC : HolomorphicModel sC) (i : C ⟶ X) (hi : i ≫ sX = sC) :
    analyticRestrictionH1 i hi = analyticRestrictionH1OfModel MX MC i hi := by
  have h : Nonempty (HolomorphicModel sX) ∧ Nonempty (HolomorphicModel sC) := ⟨⟨MX⟩, ⟨MC⟩⟩
  rw [analyticRestrictionH1, dif_pos h]
  unfold analyticRestrictionH1OfModel
  rw [analyticPullbackOfModel_eq h.1.some MX h.2.some MC i hi]

/-- The restriction on `H¹` for separated quasi-compact schemes smooth over `ℂ`, as the map built
from holomorphic models. -/
theorem exists_analyticRestrictionH1_eq {nX nC : ℕ} [SmoothOfRelativeDimension nX sX]
    [IsSeparated sX] [QuasiCompact sX] [SmoothOfRelativeDimension nC sC] [IsSeparated sC]
    [QuasiCompact sC] (i : C ⟶ X) (hi : i ≫ sX = sC) :
    ∃ (MX : HolomorphicModel sX) (MC : HolomorphicModel sC),
      analyticRestrictionH1 i hi = analyticRestrictionH1OfModel MX MC i hi := by
  haveI : Smooth sX := SmoothOfRelativeDimension.smooth nX sX
  haveI : Smooth sC := SmoothOfRelativeDimension.smooth nC sC
  obtain ⟨MX⟩ := nonempty_holomorphicModel sX (n := nX)
  obtain ⟨MC⟩ := nonempty_holomorphicModel sC (n := nC)
  exact ⟨MX, MC, analyticRestrictionH1_eq MX MC i hi⟩

end Restriction

end MMP.Analytic.SurfaceHodge
