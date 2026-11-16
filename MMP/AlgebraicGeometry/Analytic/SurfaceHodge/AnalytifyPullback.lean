module

public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.ExpNaturality
public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.CechPullback
public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.RestrictionTranslates
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp

/-!
# Analytification of modules commutes with pullback, and Picard classes restrict

Let `i : C ⟶ X` be a morphism of schemes over `ℂ`, and `ψ = i^an : C^an ⟶ X^an` its realization
as a morphism of ringed spaces, built from holomorphic models of `X^an` and `C^an`. The
comparison morphisms `α_X : X^an ⟶ X` and `α_C : C^an ⟶ C` form a commutative square
`α_C ≫ i = ψ ≫ α_X`: on underlying spaces both send a `ℂ`-point `y` of `C` to the closed point
`i(y)` of `X`, and on functions both send a regular function `g` on `X` to the holomorphic
function `y ↦ g(i(y))`. Since analytification of modules is pullback along `α`, pseudofunctoriality
of the pullback of modules gives `(i^* L)^an ≅ ψ^* (L^an)` for every `𝒪_X`-module `L`.

For an invertible `L`, the class of `ψ^* (L^an)` in `H¹(C^an, 𝒪^×)` is computed from local
generators of `L^an`: on a cover of `X^an` by opens carrying generators, the class of `L^an` is the
Čech class of the ratios of the generators, and the class of `ψ^* (L^an)` is the Čech class of the
pulled-back ratios on the preimage cover. The restriction `H¹(X^an, 𝒪^×) → H¹(C^an, 𝒪^×)` carries
the first Čech class to the second (`sheafHOnePullback_cechH1ToRightDerivedSections`), so the
restriction of the Picard class of `L^an` is the Picard class of `(i^* L)^an`. Combined with the
naturality of the exponential map under restriction, this is the statement that the exponential
map commutes with restriction to a curve on Picard classes of algebraic line bundles.

## Main definitions

* `MMP.Analytic.SurfaceHodge.analytifyModulePullbackIso`: `(i^* L)^an ≅ (i^an)^* (L^an)`;
  analytification of modules commutes with pullback along `i`.

## Main results

* `MMP.Analytic.SurfaceHodge.analytificationHom_comp_toShHom`: the square
  `α_C ≫ i = i^an ≫ α_X` of morphisms of ringed spaces.
* `MMP.Analytic.SurfaceHodge.classOf_analytify_pullback_eq_sheafHOnePullback`: the restriction
  `H¹(X^an, 𝒪^×) → H¹(C^an, 𝒪^×)` carries the Picard class of `L^an` to that of `(i^* L)^an`.
* `MMP.Analytic.SurfaceHodge.isExpNaturalRestriction`: for a smooth projective curve `ι : C ⟶ X`
  on a smooth projective surface, the exponential map commutes with restriction on Picard classes
  of algebraic line bundles.
* `MMP.Analytic.SurfaceHodge.exists_classOf_analytify_pullback_eq_expPic_analyticRestrictionH1`:
  the exponential of the restriction of any `w ∈ H¹(X^an, 𝒪)` is the class of `(ι^* L_X)^an` for
  an invertible `L_X`.

## Implementation notes

The class of `L^an` itself is computed through the pullback of `L^an` along the identity of
`X^an`, so that the Čech description of `MMP.JacobianLogarithm.Fam.torsorClass_pullback_eq_cech`
applies on both sides in the same form.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][griffithsharris1978], Ch. 1 §1.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.ComplexPoints

namespace MMP.Analytic.SurfaceHodge

attribute [local instance] hasExt_of_enoughInjectives
attribute [local implicit_reducible] TopCat.Sheaf

variable {X C : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sC : C ⟶ Spec (.of ℂ)}

/-- **The analytification square.** For `i : C ⟶ X` over `ℂ`, the comparison morphisms of ringed
spaces satisfy `α_C ≫ i = i^an ≫ α_X`. -/
theorem analytificationHom_comp_toShHom (MX : HolomorphicModel sX) (MC : HolomorphicModel sC)
    (i : C ⟶ X) (hi : i ≫ sX = sC) :
    analytificationHom sC ≫ i.toLRSHom.toShHom =
      analyticRingedSpaceHomOfModel MX MC i hi ≫ analytificationHom sX := by
  refine SheafedSpace.ext _ _ rfl ?_
  ext V g : 3
  letI := MX.cs
  letI := MC.cs
  refine MC.ext fun y => ?_
  simp only [eqToHom_refl, Functor.whiskerRight_id', Category.comp_id]
  change MC.Θ.hom.hom.app _ ((analytificationHom sC).hom.c.app (op (i ⁻¹ᵁ V))
      ((i.app V).hom g)) y =
    MC.Θ.hom.hom.app _ ((analyticRingedSpaceHomOfModel MX MC i hi).hom.c.app
      (op ((Opens.map (toSchemeHom sX)).obj V))
      ((analytificationHom sX).hom.c.app (op V) g)) y
  refine (MC.hΘ (i ⁻¹ᵁ V) ((i.app V).hom g) ⟨y.1, y.2⟩).trans ?_
  refine Eq.trans ?_ ((analyticPullback_apply i hi
    (contMDiff_realize i hi MX.atlas_coords MC.Θ MC.hΘ) MX.Θ MC.Θ _
    ((analytificationHom sX).hom.c.app (op V) g) ⟨y.1, y.2⟩).trans
      (MX.hΘ V g ⟨realize i hi y.1, y.2⟩)).symm
  rw [Scheme.Hom.app_eq_appLE, evalHom_appLE_realize i hi]

/-- **Analytification commutes with pullback**: `(i^* L)^an ≅ (i^an)^* (L^an)`, from the
analytification square and pseudofunctoriality of the pullback of modules. -/
noncomputable def analytifyModulePullbackIso (MX : HolomorphicModel sX)
    (MC : HolomorphicModel sC) (i : C ⟶ X) (hi : i ≫ sX = sC) (L : X.Modules) :
    (analytifyModule sC).obj
        ((Stacks.RingedSpace.pullbackFunctor i.toLRSHom.toShHom).obj L) ≅
      (Stacks.RingedSpace.pullbackFunctor (analyticRingedSpaceHomOfModel MX MC i hi)).obj
        ((analytifyModule sX).obj L) :=
  (RingedSpaceModuleAdjunction.modulePullbackComp (analytificationHom sC)
      i.toLRSHom.toShHom).symm.app L ≪≫
    (RingedSpaceModuleAdjunction.modulePullbackCongr
      (analytificationHom_comp_toShHom MX MC i hi)).app L ≪≫
    (RingedSpaceModuleAdjunction.modulePullbackComp (analyticRingedSpaceHomOfModel MX MC i hi)
      (analytificationHom sX)).app L

/-- Restricting `i^an` on `U` to `G` agrees with restricting to `V ⊆ U` first. -/
theorem analyticRingedSpaceHomOfModel_c_app_restrict (MX : HolomorphicModel sX)
    (MC : HolomorphicModel sC) (i : C ⟶ X) (hi : i ≫ sX = sC) {U V : Opens (space sX)}
    (hUV : V ≤ U) {G : Opens (space sC)} (h₁ : G ≤ (Opens.map (analyticMap i hi)).obj U)
    (h₂ : G ≤ (Opens.map (analyticMap i hi)).obj V) (a : (structureSheaf sX).obj.obj (op U)) :
    (structureSheaf sC).obj.map (homOfLE h₁).op
        ((analyticRingedSpaceHomOfModel MX MC i hi).hom.c.app (op U) a) =
      (structureSheaf sC).obj.map (homOfLE h₂).op
        ((analyticRingedSpaceHomOfModel MX MC i hi).hom.c.app (op V)
          ((structureSheaf sX).obj.map (homOfLE hUV).op a)) := by
  erw [ConcreteCategory.congr_hom
    ((analyticRingedSpaceHomOfModel MX MC i hi).hom.c.naturality (homOfLE hUV).op) a]
  change _ = (structureSheaf sC).obj.map (homOfLE h₂).op
    ((structureSheaf sC).obj.map ((Opens.map (analyticMap i hi)).map (homOfLE hUV)).op
      ((analyticRingedSpaceHomOfModel MX MC i hi).hom.c.app (op U) a))
  exact ConcreteCategory.congr_hom ((structureSheaf sC).obj.map_comp
    ((Opens.map (analyticMap i hi)).map (homOfLE hUV)).op (homOfLE h₂).op)
    ((analyticRingedSpaceHomOfModel MX MC i hi).hom.c.app (op U) a)

/-- Naturality of Picard classes under restriction, for the pullback of the invertible
`L^an` along `i^an` and along the identity of `X^an`. -/
private theorem classOf_analytify_pullback_eq_sheafHOnePullback_of_cech [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sC] (MX : HolomorphicModel sX) (MC : HolomorphicModel sC) (i : C ⟶ X)
    (hi : i ≫ sX = sC) (L : X.Modules)
    (hLX : Stacks.SheafOfModules.IsInvertible (analytification sX : RingedSpace).sheaf.obj
      (structureSheaf (analytification sX : RingedSpace).sheaf).property
      ((analytifyModule sX).obj L))
    (hinvC : Stacks.SheafOfModules.IsInvertible (analytification sC : RingedSpace).sheaf.obj
      (structureSheaf (analytification sC : RingedSpace).sheaf).property
      ((RingedSpaceModuleAdjunction.modulePullback (analyticRingedSpaceHomOfModel MX MC i hi)).obj
        ((analytifyModule sX).obj L)))
    (hinvX : Stacks.SheafOfModules.IsInvertible (analytification sX : RingedSpace).sheaf.obj
      (structureSheaf (analytification sX : RingedSpace).sheaf).property
      ((RingedSpaceModuleAdjunction.modulePullback
        (𝟙 (analytification sX : RingedSpace))).obj ((analytifyModule sX).obj L))) :
    letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification sX)
    letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification sC)
    Stacks.SheafOfModules.Picard.classOf _ _ _ hinvC =
      Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup (analytification sC)
        ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
          (space sC) (Stacks.Cohomology.Generators.unitsSheaf (analytification sC)))).symm
          (sheafHOnePullback (analyticMap i hi) (analyticUnitsPullbackOfModel MX MC i hi)
            (Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
              (space sX) (Stacks.Cohomology.Generators.unitsSheaf (analytification sX)))
              ((Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup
                (analytification sX)).symm
                (Stacks.SheafOfModules.Picard.classOf _ _ _ hinvX))))) := by
  classical
  letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification sX)
  letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification sC)
  let ψ := analyticRingedSpaceHomOfModel MX MC i hi
  let LX := (analytifyModule sX).obj L
  apply (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup
    (analytification sC)).symm.injective
  rw [AddEquiv.symm_apply_apply]
  erw [Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup_symm_classOf (analytification sC)
      ((RingedSpaceModuleAdjunction.modulePullback ψ).obj LX) hinvC,
    Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup_symm_classOf (analytification sX)
      ((RingedSpaceModuleAdjunction.modulePullback
        (𝟙 (analytification sX : RingedSpace))).obj LX) hinvX]
  choose N hmem hne using fun x : space sX =>
    @Stacks.Cohomology.Generators.exists_generator_section (analytification sX) LX
      (Stacks.Cohomology.Generators.isFiniteLocallyFreeOfRank_one_of_isInvertible
        (analytification sX) LX hLX) x
  have hN : (⊤ : Opens (space sX)) = ⨆ x, N x :=
    le_antisymm (fun x _ => Opens.mem_iSup.2 ⟨x, hmem x⟩) le_top
  let ε := fun x => (hne x).some
  let W : space sX → Opens (space sC) := fun x => (Opens.map (analyticMap i hi)).obj (N x)
  have hW : (⊤ : Opens (space sC)) = ⨆ x, W x :=
    le_antisymm (fun y _ => (Opens.mem_iSup (s := W)).2 ⟨analyticMap i hi y,
      hmem (analyticMap i hi y)⟩) le_top
  obtain ⟨zC, hzC, hcC⟩ := MMP.JacobianLogarithm.Fam.torsorClass_pullback_eq_cech ψ
    (isLocalHom_stalkMap_analyticRingedSpaceHomOfModel MX MC i hi) LX hLX
    N ε W hW id (fun _ => le_rfl) hinvC
  obtain ⟨zX, hzX, hcX⟩ := MMP.JacobianLogarithm.Fam.torsorClass_pullback_eq_cech
    (𝟙 (analytification sX : RingedSpace))
    (fun _ => inferInstance) LX hLX N ε N hN id (fun _ => le_rfl) hinvX
  rw [hcC, hcX]
  have key := sheafHOnePullback_cechH1ToRightDerivedSections (T := space sX) (T' := space sC)
    (analyticMap i hi)
    (analyticUnitsPullbackOfModel MX MC i hi) N hN W hW id (fun _ => le_rfl) zX zC
    (fun j h => ?_)
  · apply (Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
      (space sC) (Stacks.Cohomology.Generators.unitsSheaf (analytification sC)))).injective
    rw [AddEquiv.apply_symm_apply]
    convert key.symm using 2 <;> rfl
  · rw [hzC j, hzX (id ∘ j)]
    apply Additive.toMul.injective
    apply Units.ext
    simp only [toMul_ofMul]
    exact analyticRingedSpaceHomOfModel_c_app_restrict MX MC i hi
      (le_inf (iInf_le (fun k => N (j k)) 0) (iInf_le (fun k => N (j k)) 1)) _ h _

/-- **Naturality of Picard classes under restriction.** For `i : C ⟶ X` over `ℂ` and an
invertible `𝒪_X`-module `L`, the restriction `H¹(X^an, 𝒪^×) → H¹(C^an, 𝒪^×)` along `i^an`
carries the class of `L^an` to the class of `(i^* L)^an`, read in the Picard groups. -/
theorem classOf_analytify_pullback_eq_sheafHOnePullback [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sC] (MX : HolomorphicModel sX) (MC : HolomorphicModel sC) (i : C ⟶ X)
    (hi : i ≫ sX = sC) (L : X.Modules)
    (hLX : Stacks.SheafOfModules.IsInvertible (analytification sX : RingedSpace).sheaf.obj
      (structureSheaf (analytification sX : RingedSpace).sheaf).property
      ((analytifyModule sX).obj L))
    (hLC : Stacks.SheafOfModules.IsInvertible (analytification sC : RingedSpace).sheaf.obj
      (structureSheaf (analytification sC : RingedSpace).sheaf).property
      ((analytifyModule sC).obj ((Stacks.RingedSpace.pullbackFunctor i.toLRSHom.toShHom).obj L))) :
    letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification sX)
    letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification sC)
    Stacks.SheafOfModules.Picard.classOf _ _ _ hLC =
      Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup (analytification sC)
        ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
          (space sC) (Stacks.Cohomology.Generators.unitsSheaf (analytification sC)))).symm
          (sheafHOnePullback (analyticMap i hi) (analyticUnitsPullbackOfModel MX MC i hi)
            (Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
              (space sX) (Stacks.Cohomology.Generators.unitsSheaf (analytification sX)))
              ((Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup
                (analytification sX)).symm
                (Stacks.SheafOfModules.Picard.classOf _ _ _ hLX))))) := by
  letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification sX)
  letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification sC)
  let ψ := analyticRingedSpaceHomOfModel MX MC i hi
  let LX := (analytifyModule sX).obj L
  haveI := hLX
  have hinvC : Stacks.SheafOfModules.IsInvertible (analytification sC : RingedSpace).sheaf.obj
      (structureSheaf (analytification sC : RingedSpace).sheaf).property
      ((RingedSpaceModuleAdjunction.modulePullback ψ).obj LX) :=
    Stacks.RingedSpace.isInvertible_modulePullback ψ LX
  have hinvX : Stacks.SheafOfModules.IsInvertible (analytification sX : RingedSpace).sheaf.obj
      (structureSheaf (analytification sX : RingedSpace).sheaf).property
      ((RingedSpaceModuleAdjunction.modulePullback
        (𝟙 (analytification sX : RingedSpace))).obj LX) :=
    Stacks.RingedSpace.isInvertible_modulePullback (𝟙 (analytification sX : RingedSpace)) LX
  have hclC : Stacks.SheafOfModules.Picard.classOf _ _ _ hLC =
      Stacks.SheafOfModules.Picard.classOf _ _ _ hinvC :=
    (Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff _ _ _ _ hLC hinvC).2
      ⟨analytifyModulePullbackIso MX MC i hi L⟩
  have hclX : Stacks.SheafOfModules.Picard.classOf _ _ _ hLX =
      Stacks.SheafOfModules.Picard.classOf _ _ _ hinvX :=
    (Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff _ _ _ _ hLX hinvX).2
      ⟨((RingedSpaceModuleAdjunction.modulePullbackId
        (analytification sX : RingedSpace)).app LX).symm⟩
  rw [hclC, hclX]
  exact classOf_analytify_pullback_eq_sheafHOnePullback_of_cech MX MC i hi L hLX hinvC hinvX

/-- **The exponential map commutes with restriction on algebraic Picard classes.** Let `X` be a
smooth projective surface over `ℂ`, `ι : C ⟶ X` a smooth projective curve in it, and `e` the
exponential map of `C^an`. For every exponential map `e_X` of `X^an`, every `w ∈ H¹(X^an, 𝒪)` and
every invertible `L_X` with `[L_X^an] = exp_X w`, the class of `(ι^* L_X)^an` is `exp_C (res w)`.
-/
theorem isExpNaturalRestriction {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))] {C : Scheme.{0}} (ι : C ⟶ X)
    [IsClosedImmersion ι] [IsProper (ι ≫ (X ↘ Spec (.of ℂ)))]
    [SmoothOfRelativeDimension 1 (ι ≫ (X ↘ Spec (.of ℂ)))]
    (e : analyticO (ι ≫ (X ↘ Spec (.of ℂ))) ⟶
      Stacks.Cohomology.Generators.unitsSheaf (analytification (ι ≫ (X ↘ Spec (.of ℂ)))))
    (he : ∀ (W : Opens (space (ι ≫ (X ↘ Spec (.of ℂ)))))
      (s : (structureSheaf (ι ≫ (X ↘ Spec (.of ℂ)))).obj.obj (op W)) (x : W)
      (c : {c : Chart (ι ≫ (X ↘ Spec (.of ℂ))) // x.1 ∈ ComplexPoints.chart c.U})
      (g : (Fin c.1.n → ℂ) → ℂ) (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
      (γ : Filter.Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
      (γ' : Filter.Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
        (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
      s.1 x c = Chart.StalkRing.mk c.1 _ γ →
      ((Additive.toMul (e.hom.app (op W) s) :
          ((structureSheaf (ι ≫ (X ↘ Spec (.of ℂ)))).obj.obj (op W))ˣ) :
        (structureSheaf (ι ≫ (X ↘ Spec (.of ℂ)))).obj.obj (op W)).1 x c =
          Chart.StalkRing.mk c.1 _ γ') :
    haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 2 _
    haveI : Smooth (ι ≫ (X ↘ Spec (.of ℂ))) := SmoothOfRelativeDimension.smooth 1 _
    IsExpNaturalRestriction (X ↘ Spec (.of ℂ)) ι e := by
  haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 2 _
  haveI : Smooth (ι ≫ (X ↘ Spec (.of ℂ))) := SmoothOfRelativeDimension.smooth 1 _
  intro eX heX w LX _ hLXan hLan hcl
  haveI : IsProper (X ↘ Spec (.of ℂ)) := (IsProjectiveMorphism.isProjective
    (IsProjectiveVariety.isProjective (k := ℂ) (f := X ↘ Spec (.of ℂ)))).isProper
  letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup
    (analytification (X ↘ Spec (.of ℂ)))
  letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup
    (analytification (ι ≫ (X ↘ Spec (.of ℂ))))
  obtain ⟨MX, MC, hres⟩ := exists_analyticRestrictionH1_eq (nX := 2) (nC := 1)
    (sX := X ↘ Spec (.of ℂ)) (sC := ι ≫ (X ↘ Spec (.of ℂ))) ι rfl
  rw [classOf_analytify_pullback_eq_sheafHOnePullback MX MC ι rfl LX hLXan hLan, hcl,
    AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply, hres,
    sheafH_map_exp_analyticRestrictionH1OfModel MX MC ι rfl eX heX e he w]

/-- **Exponentials of restricted classes are restrictions of algebraic classes.** Let `X` be a
smooth projective surface over `ℂ`, `ι : C ⟶ X` a smooth projective curve in it, and `e` the
exponential map of `C^an`. For every `w ∈ H¹(X^an, 𝒪)` the exponential of the restriction of `w`
is the class of `(ι^* L_X)^an` for some invertible `L_X`. -/
theorem exists_classOf_analytify_pullback_eq_expPic_analyticRestrictionH1 {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))] {C : Scheme.{0}} (ι : C ⟶ X)
    [IsClosedImmersion ι] (hproj : IsProjective (ι ≫ (X ↘ Spec (.of ℂ))))
    [SmoothOfRelativeDimension 1 (ι ≫ (X ↘ Spec (.of ℂ)))]
    (e : analyticO (ι ≫ (X ↘ Spec (.of ℂ))) ⟶
      Stacks.Cohomology.Generators.unitsSheaf (analytification (ι ≫ (X ↘ Spec (.of ℂ)))))
    (he : ∀ (W : Opens (space (ι ≫ (X ↘ Spec (.of ℂ)))))
      (s : (structureSheaf (ι ≫ (X ↘ Spec (.of ℂ)))).obj.obj (op W)) (x : W)
      (c : {c : Chart (ι ≫ (X ↘ Spec (.of ℂ))) // x.1 ∈ ComplexPoints.chart c.U})
      (g : (Fin c.1.n → ℂ) → ℂ) (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
      (γ : Filter.Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
      (γ' : Filter.Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
        (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
      s.1 x c = Chart.StalkRing.mk c.1 _ γ →
      ((Additive.toMul (e.hom.app (op W) s) :
          ((structureSheaf (ι ≫ (X ↘ Spec (.of ℂ)))).obj.obj (op W))ˣ) :
        (structureSheaf (ι ≫ (X ↘ Spec (.of ℂ)))).obj.obj (op W)).1 x c =
          Chart.StalkRing.mk c.1 _ γ')
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
          (analyticRestrictionH1 (sX := X ↘ Spec (.of ℂ)) ι rfl w) :=
  haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 2 _
  haveI : Smooth (ι ≫ (X ↘ Spec (.of ℂ))) := SmoothOfRelativeDimension.smooth 1 _
  exists_classOf_analytify_pullback_eq_expPic_analyticRestrictionH1_of_pullback ι hproj e he
    (fun MX MC L _ => classOf_analytify_pullback_eq_sheafHOnePullback MX MC ι rfl L) w

end MMP.Analytic.SurfaceHodge
