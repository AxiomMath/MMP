module

public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.ExpUniformisation
public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.AnalyticRestriction

/-!
# Naturality of the exponential map under restriction

Let `i : C ⟶ X` be a morphism of schemes over `ℂ`, and `i^an : C^an ⟶ X^an` its realization.
Restriction of analytic functions `𝒪_{X^an} ⟶ (i^an)_* 𝒪_{C^an}` induces the restriction
`res : H¹(X^an, 𝒪) → H¹(C^an, 𝒪)`, and restriction of units induces
`res^× : H¹(X^an, 𝒪^×) → H¹(C^an, 𝒪^×)`. The exponential maps `e : f ↦ exp (2πi f)` of the two
exponential sequences commute with restriction, `exp (2πi (f ∘ i^an)) = exp (2πi f) ∘ i^an`, and
hence `e_C ∘ res = res^× ∘ e_X` on `H¹`. With this, for a smooth projective surface `X` and a
smooth projective curve `C ⊂ X`, the exponential of the restriction of any `w ∈ H¹(X^an, 𝒪)` is
the class of `(i^* L_X)^an` for an invertible `L_X`, once the restriction `res^×` is known to be
the pullback of invertible modules on Picard groups.

## Main definitions

* `MMP.Analytic.SurfaceHodge.analyticUnitsPullbackOfModel`: the restriction of units
  `𝒪_{X^an}^× ⟶ (i^an)_* 𝒪_{C^an}^×`.
* `MMP.Analytic.SurfaceHodge.analyticRingedSpaceHomOfModel`: `i^an` as a morphism of ringed
  spaces `C^an ⟶ X^an`.

## Main results

* `MMP.Analytic.SurfaceHodge.sheafH_map_sheafHOnePullback`: naturality of the map on `H¹`
  induced by a morphism `A ⟶ f_* B`.
* `MMP.Analytic.SurfaceHodge.isLocalHom_stalkMap_analyticRingedSpaceHomOfModel`: `i^an` is a
  morphism of locally ringed spaces.
* `MMP.Analytic.SurfaceHodge.analyticPullbackOfModel_comp_exp`: the exponential commutes with
  restriction of functions.
* `MMP.Analytic.SurfaceHodge.sheafH_map_exp_analyticRestrictionH1OfModel`:
  `e_C (res w) = res^× (e_X w)`.
* `exists_classOf_analytify_pullback_eq_expPic_analyticRestrictionH1_of_pullback`:
  exponentials of restricted classes are restrictions of algebraic classes, given that `res^×`
  is the pullback of invertible modules.

## Implementation notes

The restriction maps are built from holomorphic models of `X^an` and `C^an`
(`MMP.Analytic.SurfaceHodge.HolomorphicModel`); `analyticRestrictionH1` does not depend on them.
The identification of `res^×` with the pullback of invertible modules is a hypothesis of the last
result.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][griffithsharris1978].
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Filter
open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.ComplexPoints

namespace MMP.Analytic.SurfaceHodge

attribute [local instance] hasExt_of_enoughInjectives
attribute [local implicit_reducible] TopCat.Sheaf

section SheafH

variable {T T' : TopCat.{0}} (f : T' ⟶ T)

/-- The pullback on Godement cohomology is natural in the sheaf. -/
private theorem sheafCohomology_map_comp_sheafCohomologyPullback
    {F G : TopCat.Sheaf AddCommGrpCat.{0} T} (φ : F ⟶ G) (n : ℤ) :
    (sheafCohomology T n).map φ ≫ sheafCohomologyPullback f G n =
      sheafCohomologyPullback f F n ≫
        (sheafCohomology T' n).map ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map φ) := by
  simp only [sheafCohomology, sheafCohomologyPullback, Functor.comp_map]
  rw [hypercohomology_map_comp_hypercohomologyPullback_assoc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  exact (HomologicalComplex.singleMapHomologicalComplex
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) (ComplexShape.up ℤ) 0).hom.naturality φ

/-- **Naturality of `sheafHOnePullback`.** For a commutative square `θ ≫ f_* b = a ≫ θ'` of
morphisms `A ⟶ f_* B`, `A' ⟶ f_* B'`, the induced maps on `H¹` commute with `a` and `b`. -/
theorem sheafH_map_sheafHOnePullback
    {A A' : TopCat.Sheaf AddCommGrpCat.{0} T} {B B' : TopCat.Sheaf AddCommGrpCat.{0} T'}
    (a : A ⟶ A') (b : B ⟶ B')
    (θ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj B)
    (θ' : A' ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj B')
    (h : θ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map b = a ≫ θ')
    (x : Sheaf.H A 1) :
    Sheaf.H.map b 1 (sheafHOnePullback f θ x) = sheafHOnePullback f θ' (Sheaf.H.map a 1 x) := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f
  have hadj : (adj.homEquiv A B).symm θ ≫ b =
      (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map a ≫ (adj.homEquiv A' B').symm θ' := by
    rw [← Adjunction.homEquiv_naturality_right_symm, h,
      Adjunction.homEquiv_naturality_left_symm]
  have e2 := ConcreteCategory.congr_hom
    (sheafCohomology_map_comp_sheafCohomologyPullback f a ((1 : ℕ) : ℤ))
    ((MMP.JacobianLogarithm.extIso T).inv.app A x)
  have e3 : ∀ u, (sheafCohomology T' ((1 : ℕ) : ℤ)).map ((adj.homEquiv A' B').symm θ')
      ((sheafCohomology T' ((1 : ℕ) : ℤ)).map ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map a)
        u) = (sheafCohomology T' ((1 : ℕ) : ℤ)).map b
      ((sheafCohomology T' ((1 : ℕ) : ℤ)).map ((adj.homEquiv A B).symm θ) u) := by
    intro u
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, hadj]
  have e4 : ∀ u, (MMP.JacobianLogarithm.extIso T').hom.app B'
      ((sheafCohomology T' ((1 : ℕ) : ℤ)).map b u) =
        Sheaf.H.map b 1 ((MMP.JacobianLogarithm.extIso T').hom.app B u) := by
    intro u
    have h1 := MMP.JacobianLogarithm.extIso_inv_naturality T' b
      ((MMP.JacobianLogarithm.extIso T').hom.app B u)
    have h2 : (MMP.JacobianLogarithm.extIso T').inv.app B
        ((MMP.JacobianLogarithm.extIso T').hom.app B u) = u :=
      Iso.hom_inv_id_app_apply _ _ _
    rw [h2] at h1
    rw [← h1]
    exact Iso.inv_hom_id_app_apply (MMP.JacobianLogarithm.extIso T') B' _
  change Sheaf.H.map b 1 ((MMP.JacobianLogarithm.extIso T').hom.app B
      ((sheafCohomology T' ((1 : ℕ) : ℤ)).map ((adj.homEquiv A B).symm θ)
        (sheafCohomologyPullback f A ((1 : ℕ) : ℤ)
          ((MMP.JacobianLogarithm.extIso T).inv.app A x)))) =
    (MMP.JacobianLogarithm.extIso T').hom.app B'
      ((sheafCohomology T' ((1 : ℕ) : ℤ)).map ((adj.homEquiv A' B').symm θ')
        (sheafCohomologyPullback f A' ((1 : ℕ) : ℤ)
          ((MMP.JacobianLogarithm.extIso T).inv.app A' (Sheaf.H.map a 1 x))))
  simp only [ConcreteCategory.comp_apply] at e2
  rw [MMP.JacobianLogarithm.extIso_inv_naturality T a x, e2, e3, e4]

end SheafH

section Units

variable {X C : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sC : C ⟶ Spec (.of ℂ)}

/-- The pullback of units of analytic functions along `i^an`, `𝒪_{X^an}^× ⟶ (i^an)_* 𝒪_{C^an}^×`,
built from holomorphic models: the units map of `analyticPullback`. -/
noncomputable def analyticUnitsPullbackOfModel (MX : HolomorphicModel sX)
    (MC : HolomorphicModel sC) (i : C ⟶ X) (hi : i ≫ sX = sC) :
    Stacks.Cohomology.Generators.unitsSheaf (analytification sX) ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap i hi)).obj
        (Stacks.Cohomology.Generators.unitsSheaf (analytification sC)) :=
  letI := MX.cs
  letI := MC.cs
  (sheafCompose _ commGroupAddCommGroupEquivalence.functor).map
    ((sheafCompose _ CommMonCat.units).map
      ((sheafCompose _ (forget₂ CommRingCat CommMonCat)).map
        (analyticPullback i hi (contMDiff_realize i hi MX.atlas_coords MC.Θ MC.hΘ) MX.Θ MC.Θ)))

/-- The realization `i^an : C^an ⟶ X^an` as a morphism of ringed spaces, with comorphism the
pullback of analytic functions, built from holomorphic models. -/
noncomputable def analyticRingedSpaceHomOfModel (MX : HolomorphicModel sX)
    (MC : HolomorphicModel sC) (i : C ⟶ X) (hi : i ≫ sX = sC) :
    analytification sC ⟶ analytification sX :=
  letI := MX.cs
  letI := MC.cs
  InducedCategory.homMk
    { base := analyticMap i hi
      c := (analyticPullback i hi (contMDiff_realize i hi MX.atlas_coords MC.Θ MC.hΘ) MX.Θ
        MC.Θ).hom }

/-- **The realization is local on stalks.** The stalk maps of `analyticRingedSpaceHomOfModel`
are local ring homomorphisms, so `i^an` is a morphism of locally ringed spaces. -/
theorem isLocalHom_stalkMap_analyticRingedSpaceHomOfModel (MX : HolomorphicModel sX)
    (MC : HolomorphicModel sC) (i : C ⟶ X) (hi : i ≫ sX = sC) (y : space sC) :
    IsLocalHom ((analyticRingedSpaceHomOfModel MX MC i hi).hom.stalkMap y).hom := by
  letI := MX.cs
  letI := MC.cs
  have hf := contMDiff_realize i hi MX.atlas_coords MC.Θ MC.hΘ
  refine ⟨fun γ hγ => ?_⟩
  obtain ⟨V, hxV, g, rfl⟩ := (analytification sX).presheaf.exists_germ_eq γ
  have e := congrArg (fun φ => φ.hom g)
    (PresheafedSpace.stalkMap_germ (analyticRingedSpaceHomOfModel MX MC i hi).hom V y hxV)
  simp only [CommRingCat.comp_apply] at e
  rw [e] at hγ
  have h1 := hγ.map ((TopCat.Presheaf.stalkFunctor CommRingCat y).map MC.Θ.hom.hom).hom
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at h1
  replace h1 := (smoothSheafCommRing.isUnit_stalk_iff _ _).1 h1
  rw [RingHom.mem_ker] at h1
  erw [smoothSheafCommRing.eval_germ] at h1
  have hp := analyticPullback_apply i hi hf MX.Θ MC.Θ V g ⟨y, hxV⟩
  have h3 : IsUnit ((TopCat.Presheaf.stalkFunctor CommRingCat (analyticMap i hi y)).map
      MX.Θ.hom.hom ((analytification sX).presheaf.germ V _ hxV g)) := by
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    refine (smoothSheafCommRing.isUnit_stalk_iff _ _).2 ?_
    rw [RingHom.mem_ker]
    erw [smoothSheafCommRing.eval_germ]
    exact fun h0 => h1 (hp.trans h0)
  have h4 := h3.map ((TopCat.Presheaf.stalkFunctor CommRingCat (analyticMap i hi y)).map
    MX.Θ.inv.hom).hom
  have hid : MX.Θ.hom.hom ≫ MX.Θ.inv.hom = 𝟙 _ := congrArg (fun φ => φ.hom) MX.Θ.hom_inv_id
  have hid' : (TopCat.Presheaf.stalkFunctor CommRingCat (analyticMap i hi y)).map MX.Θ.hom.hom ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat (analyticMap i hi y)).map MX.Θ.inv.hom = 𝟙 _ := by
    rw [← Functor.map_comp, hid, CategoryTheory.Functor.map_id]
  have h5 := ConcreteCategory.congr_hom hid' ((analytification sX).presheaf.germ V _ hxV g)
  exact (congrArg IsUnit h5).mp h4

/-- The units map of `analyticRingedSpaceHomOfModel` is `analyticUnitsPullbackOfModel`. -/
theorem analyticUnitsPullbackOfModel_app (MX : HolomorphicModel sX)
    (MC : HolomorphicModel sC) (i : C ⟶ X) (hi : i ≫ sX = sC) (W : Opens (space sX))
    (u : ((structureSheaf sX).obj.obj (op W))ˣ) :
    (analyticUnitsPullbackOfModel MX MC i hi).hom.app (op W) (Additive.ofMul u) =
      Additive.ofMul (Units.map
        ((analyticRingedSpaceHomOfModel MX MC i hi).hom.c.app (op W)).hom.toMonoidHom u) :=
  rfl

/-- **The exponential commutes with restriction.** If `e_X` and `e_C` are the exponential maps
`f ↦ exp (2πi f)` of `X^an` and `C^an`, then restricting a function and taking its exponential
is taking its exponential and restricting the unit. -/
theorem analyticPullbackOfModel_comp_exp [LocallyOfFiniteType sX] [LocallyOfFiniteType sC]
    (MX : HolomorphicModel sX) (MC : HolomorphicModel sC) (i : C ⟶ X) (hi : i ≫ sX = sC)
    (eX : analyticO sX ⟶ Stacks.Cohomology.Generators.unitsSheaf (analytification sX))
    (heX : ∀ (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W)
      (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) (g : (Fin c.1.n → ℂ) → ℂ)
      (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
      (γ : Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
      (γ' : Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
        (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
      s.1 x c = Chart.StalkRing.mk c.1 _ γ →
      ((Additive.toMul (eX.hom.app (op W) s) : ((structureSheaf sX).obj.obj (op W))ˣ) :
        (structureSheaf sX).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ γ')
    (eC : analyticO sC ⟶ Stacks.Cohomology.Generators.unitsSheaf (analytification sC))
    (heC : ∀ (W : Opens (space sC)) (s : (structureSheaf sC).obj.obj (op W)) (x : W)
      (c : {c : Chart sC // x.1 ∈ ComplexPoints.chart c.U}) (g : (Fin c.1.n → ℂ) → ℂ)
      (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
      (γ : Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
      (γ' : Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
        (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
      s.1 x c = Chart.StalkRing.mk c.1 _ γ →
      ((Additive.toMul (eC.hom.app (op W) s) : ((structureSheaf sC).obj.obj (op W))ˣ) :
        (structureSheaf sC).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ γ') :
    analyticPullbackOfModel MX MC i hi ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap i hi)).map eC =
      eX ≫ analyticUnitsPullbackOfModel MX MC i hi := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W => ?_))
  ext s
  apply Additive.toMul.injective
  apply Units.ext
  refine MC.ext fun y => ?_
  letI := MX.cs
  letI := MC.cs
  have hf := contMDiff_realize i hi MX.atlas_coords MC.Θ MC.hΘ
  have h1 := MMP.JacobianLogarithm.Fam.theta_exp MC.Θ MC.hΘ eC heC
    ((Opens.map (analyticMap i hi)).obj W.unop)
    ((analyticPullback i hi hf MX.Θ MC.Θ).hom.app W s) y
  have h3 := analyticPullback_apply i hi hf MX.Θ MC.Θ W.unop
    ((Additive.toMul (eX.hom.app W s) : ((structureSheaf sX).obj.obj W)ˣ) :
      (structureSheaf sX).obj.obj W) y
  rw [analyticPullback_apply i hi hf MX.Θ MC.Θ W.unop s y,
    ← MMP.JacobianLogarithm.Fam.theta_exp MX.Θ MX.hΘ eX heX W.unop s
      ⟨realize i hi y.1, y.2⟩] at h1
  exact h1.trans h3.symm

/-- **Naturality of the exponential map on `H¹` under restriction.** For the exponential maps
`e_X`, `e_C` of `X^an` and `C^an`, `e_C (res w) = res^× (e_X w)` in `H¹(C^an, 𝒪^×)`, where `res`
and `res^×` are the restrictions along `i^an` of `H¹(𝒪)` and of `H¹(𝒪^×)`. -/
theorem sheafH_map_exp_analyticRestrictionH1OfModel [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sC] (MX : HolomorphicModel sX) (MC : HolomorphicModel sC) (i : C ⟶ X)
    (hi : i ≫ sX = sC)
    (eX : analyticO sX ⟶ Stacks.Cohomology.Generators.unitsSheaf (analytification sX))
    (heX : ∀ (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W)
      (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) (g : (Fin c.1.n → ℂ) → ℂ)
      (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
      (γ : Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
      (γ' : Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
        (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
      s.1 x c = Chart.StalkRing.mk c.1 _ γ →
      ((Additive.toMul (eX.hom.app (op W) s) : ((structureSheaf sX).obj.obj (op W))ˣ) :
        (structureSheaf sX).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ γ')
    (eC : analyticO sC ⟶ Stacks.Cohomology.Generators.unitsSheaf (analytification sC))
    (heC : ∀ (W : Opens (space sC)) (s : (structureSheaf sC).obj.obj (op W)) (x : W)
      (c : {c : Chart sC // x.1 ∈ ComplexPoints.chart c.U}) (g : (Fin c.1.n → ℂ) → ℂ)
      (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
      (γ : Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
      (γ' : Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
        (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
      s.1 x c = Chart.StalkRing.mk c.1 _ γ →
      ((Additive.toMul (eC.hom.app (op W) s) : ((structureSheaf sC).obj.obj (op W))ˣ) :
        (structureSheaf sC).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ γ')
    (w : Sheaf.H (analyticO sX) 1) :
    Sheaf.H.map eC 1 (analyticRestrictionH1OfModel MX MC i hi w) =
      sheafHOnePullback (analyticMap i hi) (analyticUnitsPullbackOfModel MX MC i hi)
        (Sheaf.H.map eX 1 w) :=
  sheafH_map_sheafHOnePullback (analyticMap i hi) eX eC (analyticPullbackOfModel MX MC i hi)
    (analyticUnitsPullbackOfModel MX MC i hi)
    (analyticPullbackOfModel_comp_exp MX MC i hi eX heX eC heC) w

end Units

section Restriction

/-- **Exponentials of restricted classes are restrictions of algebraic classes, given the
naturality of Picard classes.** Let `X` be a smooth projective surface over `ℂ`, `ι : C ⟶ X` a
smooth projective curve in it, and `e` the exponential map of `C^an`. Suppose that the restriction
`H¹(X^an, 𝒪^×) → H¹(C^an, 𝒪^×)` along `ι^an` carries the class of `L^an` to the class of
`(ι^* L)^an`, for every invertible `𝒪_X`-module `L` (hypothesis `hpic`). Then for every
`w ∈ H¹(X^an, 𝒪)` the exponential of the restriction of `w` is the class of `(ι^* L_X)^an` for
some invertible `L_X`. -/
theorem exists_classOf_analytify_pullback_eq_expPic_analyticRestrictionH1_of_pullback
    {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))] {C : Scheme.{0}} (ι : C ⟶ X)
    [IsClosedImmersion ι] (hproj : IsProjective (ι ≫ (X ↘ Spec (.of ℂ))))
    [SmoothOfRelativeDimension 1 (ι ≫ (X ↘ Spec (.of ℂ)))]
    (e : analyticO (ι ≫ (X ↘ Spec (.of ℂ))) ⟶
      Stacks.Cohomology.Generators.unitsSheaf (analytification (ι ≫ (X ↘ Spec (.of ℂ)))))
    (he : ∀ (W : Opens (space (ι ≫ (X ↘ Spec (.of ℂ)))))
      (s : (structureSheaf (ι ≫ (X ↘ Spec (.of ℂ)))).obj.obj (op W)) (x : W)
      (c : {c : Chart (ι ≫ (X ↘ Spec (.of ℂ))) // x.1 ∈ ComplexPoints.chart c.U})
      (g : (Fin c.1.n → ℂ) → ℂ) (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
      (γ : Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
      (γ' : Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
        (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
      s.1 x c = Chart.StalkRing.mk c.1 _ γ →
      ((Additive.toMul (e.hom.app (op W) s) :
          ((structureSheaf (ι ≫ (X ↘ Spec (.of ℂ)))).obj.obj (op W))ˣ) :
        (structureSheaf (ι ≫ (X ↘ Spec (.of ℂ)))).obj.obj (op W)).1 x c =
          Chart.StalkRing.mk c.1 _ γ')
    (hpic : letI := (Stacks.Cohomology.Generators.picardGroupAddCommGroup
        (analytification (X ↘ Spec (.of ℂ))))
      letI := (Stacks.Cohomology.Generators.picardGroupAddCommGroup
        (analytification (ι ≫ (X ↘ Spec (.of ℂ)))))
      ∀ (MX : HolomorphicModel (X ↘ Spec (.of ℂ)))
      (MC : HolomorphicModel (ι ≫ (X ↘ Spec (.of ℂ)))) (L : X.Modules)
      (_ : Stacks.SheafOfModules.IsInvertible X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L)
      (hLX : Stacks.SheafOfModules.IsInvertible
        (analytification (X ↘ Spec (.of ℂ)) : RingedSpace).sheaf.obj
        (structureSheaf (analytification (X ↘ Spec (.of ℂ)) : RingedSpace).sheaf).property
        ((analytifyModule (X ↘ Spec (.of ℂ))).obj L))
      (hLC : Stacks.SheafOfModules.IsInvertible
        (analytification (ι ≫ (X ↘ Spec (.of ℂ))) : RingedSpace).sheaf.obj
        (structureSheaf (analytification (ι ≫ (X ↘ Spec (.of ℂ))) : RingedSpace).sheaf).property
        ((analytifyModule (ι ≫ (X ↘ Spec (.of ℂ)))).obj
          ((Stacks.RingedSpace.pullbackFunctor ι.toLRSHom.toShHom).obj L))),
      Stacks.SheafOfModules.Picard.classOf _ _ _ hLC =
        Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup
          (analytification (ι ≫ (X ↘ Spec (.of ℂ))))
          ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
            (space (ι ≫ (X ↘ Spec (.of ℂ))))
            (Stacks.Cohomology.Generators.unitsSheaf
              (analytification (ι ≫ (X ↘ Spec (.of ℂ))))))).symm
            (sheafHOnePullback (analyticMap ι rfl) (analyticUnitsPullbackOfModel MX MC ι rfl)
              (Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
                (space (X ↘ Spec (.of ℂ)))
                (Stacks.Cohomology.Generators.unitsSheaf
                  (analytification (X ↘ Spec (.of ℂ)))))
                ((Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup
                  (analytification (X ↘ Spec (.of ℂ)))).symm
                  (Stacks.SheafOfModules.Picard.classOf _ _ _ hLX))))))
    (w : Sheaf.H (analyticO (X ↘ Spec (.of ℂ))) 1) :
    haveI := hproj.isProper
    letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup
      (analytification (ι ≫ (X ↘ Spec (.of ℂ))))
    ∃ (LX : X.Modules) (_ : Stacks.SheafOfModules.IsInvertible X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) LX)
      (hLan : Stacks.SheafOfModules.IsInvertible
        (analytification (ι ≫ (X ↘ Spec (.of ℂ))) : RingedSpace).sheaf.obj
        (structureSheaf (analytification (ι ≫ (X ↘ Spec (.of ℂ))) : RingedSpace).sheaf).property
        ((analytifyModule (ι ≫ (X ↘ Spec (.of ℂ)))).obj
          ((Stacks.RingedSpace.pullbackFunctor ι.toLRSHom.toShHom).obj LX))),
      Stacks.SheafOfModules.Picard.classOf _ _ _ hLan =
        (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup
            (analytification (ι ≫ (X ↘ Spec (.of ℂ))))).toAddMonoidHom.comp
          ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
            (space (ι ≫ (X ↘ Spec (.of ℂ))))
            (Stacks.Cohomology.Generators.unitsSheaf
              (analytification (ι ≫ (X ↘ Spec (.of ℂ))))))).symm.toAddMonoidHom.comp
            (Sheaf.H.map e 1))
          (analyticRestrictionH1 (sX := X ↘ Spec (.of ℂ)) ι rfl w) := by
  haveI := hproj.isProper
  have hXproj : IsProjective (X ↘ Spec (.of ℂ)) :=
    IsProjectiveMorphism.isProjective
      (IsProjectiveVariety.isProjective (k := ℂ) (f := X ↘ Spec (.of ℂ)))
  haveI : IsProper (X ↘ Spec (.of ℂ)) := hXproj.isProper
  letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup
    (analytification (X ↘ Spec (.of ℂ)))
  letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup
    (analytification (ι ≫ (X ↘ Spec (.of ℂ))))
  obtain ⟨MX, MC, hres⟩ := exists_analyticRestrictionH1_eq (nX := 2) (nC := 1)
    (sX := X ↘ Spec (.of ℂ)) (sC := ι ≫ (X ↘ Spec (.of ℂ))) ι rfl
  obtain ⟨ιZ, eX, wZ, -, -, heX⟩ := exists_shortExact_exponentialSequence (X ↘ Spec (.of ℂ))
  obtain ⟨LX, hLX, hLanX, hcl⟩ := exists_classOf_analytifyModule_eq (X ↘ Spec (.of ℂ)) hXproj
    (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup (analytification (X ↘ Spec (.of ℂ)))
      ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
        (space (X ↘ Spec (.of ℂ)))
        (Stacks.Cohomology.Generators.unitsSheaf (analytification (X ↘ Spec (.of ℂ)))))).symm
        (Sheaf.H.map eX 1 w)))
  have hM : Stacks.SheafOfModules.IsInvertible C.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf C)
      ((Stacks.RingedSpace.pullbackFunctor ι.toLRSHom.toShHom).obj LX) :=
    Stacks.RingedSpace.modulePullback_isInvertible_of _ LX hLX
  have hLanC := @Stacks.RingedSpace.isInvertible_modulePullback _ _
    (analytificationHom (ι ≫ (X ↘ Spec (.of ℂ)))) _ hM
  refine ⟨LX, hLX, hLanC, ?_⟩
  rw [hpic MX MC LX hLX hLanX hLanC, hcl, AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply,
    hres]
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [sheafH_map_exp_analyticRestrictionH1OfModel MX MC ι rfl eX heX e he w]

end Restriction

end MMP.Analytic.SurfaceHodge
