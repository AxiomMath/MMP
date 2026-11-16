module

public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.ZariskiClosureDimension
public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.ExpUniformisation
public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.AnalyticRestriction
public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.IntegralCohomologyRank
public import MMP.AlgebraicGeometry.Bertini.FreeLinearSystem

/-!
# Restriction points lie in countably many translates of the exponential image

Let `X` be a smooth projective surface over `ℂ`, `ι : C ⟶ X` a smooth projective curve on it with
a point `σ`, `J` the Jacobian of `C` and `Φ : ℂⁿ → J(ℂ)` its exponential uniformisation for
coordinates `φ : ℂⁿ ≃ H¹(C^an, 𝒪)`. Let `V ⊆ ℂⁿ` be the preimage of the image of the analytic
restriction `H¹(X^an, 𝒪) → H¹(C^an, 𝒪)`. Then the restriction points of `J`, the points whose
rigidified class is the restriction of a line bundle on `X`, lie in countably many translates
`Φ(aₖ + V)`.

The argument runs through the exponential sequence of `X^an`. The first Chern class
`c₁ : Pic(X) ≅ Pic(X^an) → H²(X^an, ℤ)` has countable image, since `H²(X^an, ℤ)` is finitely
generated. Choose, for each value `β` of `c₁` taken by a line bundle restricting to a point of
`J`, one such line bundle `L_β` and a point `a_β` with `Φ a_β` the point of `L_β|_C`. If `L`
restricts to the point `x` and `c₁(L) = β`, then `L ⊗ L_β⁻¹` has analytic class `exp_X w` for
some `w ∈ H¹(X^an, 𝒪)`, by exactness of `H¹(𝒪) → Pic → H²(ℤ)`. Its restriction to `C` has
analytic class `exp_C (res w)` (naturality of the exponential map), so its rigidified class is
that of `Φ v`, `v = φ⁻¹(res w) ∈ V`, and `x = Φ(a_β + v)`.

## Main definitions

* `MMP.Analytic.SurfaceHodge.IsExpNaturalRestriction`: the exponential map commutes with
  restriction along `ι : C ⟶ X`: `[L_X^an] = exp_X w` implies `[(ι^* L_X)^an] = exp_C (res w)`.

## Main results

* `MMP.Analytic.SurfaceHodge.countable_sheafH_constantSheaf`: `H^n(X^an, ℤ)` is countable for a
  projective `X` over `ℂ`.
* `MMP.Analytic.SurfaceHodge.exists_addMonoidHom_picardGroup_analytification`: GAGA for Picard
  groups as an additive bijection `Pic(X) → Pic(X^an)`, `[L] ↦ [L^an]`, onto the model
  `Stacks.SheafOfModules.Picard.PicardGroup` of `H¹(X^an, 𝒪^×)`.
* `MMP.Analytic.SurfaceHodge.exists_sheafH_map_eq_of_picardObstruction_eq_zero`: exactness of
  `H¹(M) → Pic(A) → H²(F)` for a sequence `0 → F → M → 𝒪_A^× → 0`.
* `MMP.Analytic.SurfaceHodge.schemePullbackClass_eq_of_isExpUniformisation`: if the restriction
  of `L_X` has analytic class `exp (φ v)`, the rigidified class of `Φ v` is that restriction.
* `MMP.Analytic.SurfaceHodge.exists_translates_of_forall_eq_zero`: the abstract counting step,
  from a countable obstruction group to countably many translates.
* `MMP.Analytic.SurfaceHodge.exists_mem_schemePullbackClass_eq_of_classOf_eq`: an invertible
  module with analytic class `exp_X w` restricts to the rigidified class of some `Φ v`, `v ∈ V`.
* `MMP.Analytic.SurfaceHodge.exists_translates_of_isRestrictionPoint`: the restriction points lie
  in countably many translates `Φ(aₖ + V)`.
* `MMP.Analytic.SurfaceHodge.exists_countable_isClosed_cover_of_restriction_pinned`: `Φ(V)` is
  covered by countably many closed subsets of `J` of dimension at most `dim V`.

## Implementation notes

Naturality of the exponential map under restriction, `[(ι^* L_X)^an] = exp_C (res w)` whenever
`[L_X^an] = exp_X w` (`IsExpNaturalRestriction`), is a hypothesis of the last three results.
The first-cohomology comparison `Stacks.Thickenings.sheafCohomologyOneExtEquiv` enters the
exponential map with the space `X(ℂ)`, and the Picard obstruction with the carrier of `X^an`;
`sheafCohomologyOneExtEquiv_analytification` identifies the two by rewriting, since the
unifier does not find this identification within the default heartbeats.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][griffithsharris1978], Ch. 2 §6.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.ComplexPoints
open MMP.JacobianLogarithm

namespace MMP.Analytic.SurfaceHodge

attribute [local instance] hasExt_of_enoughInjectives
attribute [local implicit_reducible] TopCat.Sheaf

/-- **Integral cohomology of a projective scheme is countable.** For a projective scheme `X`
over `ℂ`, `H^n(X^an, ℤ)` is countable, being finitely generated. -/
theorem countable_sheafH_constantSheaf {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (hX : IsProjectiveMorphism sX) (n : ℕ) :
    Countable (Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology
      (Analytification.space sX)) AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)) n) := by
  have h := finite_range_of_sheafH_constantSheaf sX hX n (AddMonoidHom.id _)
  have : Countable (AddMonoidHom.id (Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology
      (Analytification.space sX)) AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)) n)).range :=
    Finsupp.Countable.of_moduleFinite (R := ℤ)
  exact Function.Surjective.countable (f := fun x : (AddMonoidHom.id _).range => x.1)
    fun m => ⟨⟨m, m, rfl⟩, rfl⟩

/-- **GAGA for Picard groups, additively.** For a projective scheme `X` over `ℂ`, there is an
additive bijection from the Picard group of `X` to the Picard group of `X^an` (the target of
`Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup`) sending the class of an invertible
`𝒪_X`-module `L` to the class of `L^an`. -/
theorem exists_addMonoidHom_picardGroup_analytification {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjective sX) :
    letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification sX)
    ∃ ψ : Stacks.Picard.ofScheme X →+ Stacks.SheafOfModules.Picard.PicardGroup
        (analytification sX : RingedSpace).sheaf.obj
        (structureSheaf (analytification sX : RingedSpace).sheaf).property,
      Function.Bijective ψ ∧ ∀ (L : X.Modules)
        (hL : Stacks.SheafOfModules.IsInvertible X.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L)
        (hLan : Stacks.SheafOfModules.IsInvertible (analytification sX : RingedSpace).sheaf.obj
          (structureSheaf (analytification sX : RingedSpace).sheaf).property
          ((analytifyModule sX).obj L)),
        ψ (Stacks.SheafOfModules.picardClass X.presheaf _ L hL) =
          Stacks.SheafOfModules.Picard.classOf _ _ _ hLan := by
  let := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification sX)
  obtain ⟨hinv, eG, heG, -⟩ := exists_mulEquiv_picardGroup_analytification_of_isProjective sX hX
  let G := (MulEquiv.toAdditive eG).toAddMonoidHom.comp
    (toSheafPicardHom X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))
  have hGinj : Function.Injective G :=
    (MulEquiv.toAdditive eG).injective.comp (toSheafPicardHom_injective _ _)
  have hG : ∀ (L : X.Modules)
      (hL : Stacks.SheafOfModules.IsInvertible X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L)
      (hLan : Stacks.SheafOfModules.IsInvertible (analytification sX : RingedSpace).sheaf.obj
        (structureSheaf (analytification sX : RingedSpace).sheaf).property
        ((analytifyModule sX).obj L)),
      G (Stacks.SheafOfModules.picardClass X.presheaf _ L hL) =
        ringedPicardToSheafPicardHom (analytification sX)
          (Stacks.SheafOfModules.Picard.classOf _ _ _ hLan) := by
    intro L hL hLan
    have : Stacks.Ample.IsInvertibleModule X L :=
      (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).1 hL
    change Additive.ofMul (eG (Additive.toMul (toSheafPicard X.presheaf _
      (Stacks.SheafOfModules.picardClass X.presheaf _ L hL)))) = _
    refine (congrArg (fun z => Additive.ofMul (eG (Additive.toMul z)))
      (toSheafPicard_picardClass X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L hL)).trans ?_
    exact (congrArg Additive.ofMul (heG L)).trans
      (picardToSheafPicard_classOf _ _ _ hLan).symm
  have hrep : ∀ y : Stacks.Picard.ofScheme X, ∃ p, ringedPicardToSheafPicardHom
      (analytification sX) p = G y := by
    intro y
    obtain ⟨L, hL, rfl⟩ := Stacks.SheafOfModules.exists_picardClass_eq X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) y
    exact ⟨_, (hG L hL (@Stacks.RingedSpace.isInvertible_modulePullback _ _
      (analytificationHom sX) L hL)).symm⟩
  have hj := ringedPicardToSheafPicardHom_injective (analytification sX)
    (hO := (structureSheaf (analytification sX : RingedSpace).sheaf).property)
  let ψ : Stacks.Picard.ofScheme X →+ Stacks.SheafOfModules.Picard.PicardGroup
      (analytification sX : RingedSpace).sheaf.obj
      (structureSheaf (analytification sX : RingedSpace).sheaf).property :=
    AddMonoidHom.mk' (fun y => (hrep y).choose) fun y y' => hj <|
      (hrep (y + y')).choose_spec.trans <| (map_add G y y').trans <|
        (congrArg₂ (· + ·) (hrep y).choose_spec.symm (hrep y').choose_spec.symm).trans
          (map_add _ _ _).symm
  have hψ : ∀ y, ringedPicardToSheafPicardHom (analytification sX) (ψ y) = G y :=
    fun y => (hrep y).choose_spec
  refine ⟨ψ, ⟨fun y y' h => hGinj ((hψ y).symm.trans ((congrArg _ h).trans (hψ y'))),
    fun p => ?_⟩, fun L hL hLan => hj ((hψ _).trans (hG L hL hLan))⟩
  obtain ⟨L, hL, hLan, rfl⟩ := exists_classOf_analytifyModule_eq sX hX p
  exact ⟨_, hj ((hψ _).trans (hG L hL hLan))⟩

/-- **Exactness at the Picard group.** For a ringed space `A` with local stalks and a short exact
sequence `0 ⟶ F ⟶ M ⟶ 𝒪_A^× ⟶ 0` of sheaves of abelian groups, a Picard class with vanishing
obstruction in `H²(A, F)` is the image of a class of `H¹(A, M)`. -/
theorem exists_sheafH_map_eq_of_picardObstruction_eq_zero (A : RingedSpace.{0})
    [∀ x, IsLocalRing (A.presheaf.stalk x)] {F M : TopCat.Sheaf AddCommGrpCat.{0} A}
    {i : F ⟶ M} {e : M ⟶ Stacks.Cohomology.Generators.unitsSheaf A} {w : i ≫ e = 0}
    (hS : (ShortComplex.mk i e w).ShortExact)
    (p : Stacks.SheafOfModules.Picard.PicardGroup A.sheaf.obj (structureSheaf A.sheaf).property)
    (hp : picardObstruction A hS p = 0) :
    ∃ v : Sheaf.H M 1, Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup A
      ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv A.carrier
        (Stacks.Cohomology.Generators.unitsSheaf A))).symm (Sheaf.H.map e 1 v)) = p := by
  let := Stacks.Cohomology.Generators.picardGroupAddCommGroup A
  rw [picardObstruction_apply] at hp
  obtain ⟨v, hv⟩ := (Stacks.Thickenings.cohomology_exact_quotient hS 1 _).1 hp
  refine ⟨v, ?_⟩
  rw [hv]
  exact (congrArg (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup A)
    ((Iso.addCommGroupIsoToAddEquiv _).symm_apply_apply _)).trans (AddEquiv.apply_symm_apply _ _)

section Restriction

variable {X C : Scheme.{0}} (ι : C ⟶ X) (f : C ⟶ Spec (.of ℂ)) [IsProper f]
  (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) {JX : Grp (Over (Spec (.of ℂ)))}
  (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ)
  {H : Type} [AddCommGroup H]
  (expPic : letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification f)
    H →+ Stacks.SheafOfModules.Picard.PicardGroup (analytification f : RingedSpace).sheaf.obj
      (structureSheaf (analytification f : RingedSpace).sheaf).property)
  {n : ℕ} (φ : (Fin n → ℂ) ≃+ H) (Φ : (Fin n → ℂ) → space JX.X.hom)

/-- **The rigidified class of an exponential restriction.** Let `Φ` be the exponential
uniformisation of the Jacobian of a projective curve `C`, and `ι : C ⟶ X`. If the
analytification of the restriction `ι^* L_X` of an invertible module on `X` has class
`expPic (φ v)`, then the rigidified class of `Φ v` is the restriction of the class of `L_X`. -/
theorem schemePullbackClass_eq_of_isExpUniformisation (hproj : IsProjective f)
    (hΦ : IsExpUniformisation f hdim σ hσ eJ expPic φ Φ) (v : Fin n → ℂ) (LX : X.Modules)
    (hLX : Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) LX)
    (hLan : Stacks.SheafOfModules.IsInvertible (analytification f : RingedSpace).sheaf.obj
      (structureSheaf (analytification f : RingedSpace).sheaf).property
      ((analytifyModule f).obj ((Stacks.RingedSpace.pullbackFunctor ι.toLRSHom.toShHom).obj LX)))
    (hexp : Stacks.SheafOfModules.Picard.classOf _ _ _ hLan = expPic (φ v)) :
    Stacks.Picard.schemePullbackClass (Limits.pullback.fst f (𝟙 _) ≫ ι)
        (Stacks.SheafOfModules.picardClass X.presheaf _ LX hLX) =
      Stacks.RigidifiedPicard.smallEquiv _ (Multiplicative.toAdd
        ((eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ v).1 (Φ v).2))).1.1 := by
  set x := Stacks.RigidifiedPicard.smallEquiv _ (Multiplicative.toAdd
    ((eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ v).1 (Φ v).2))).1.1
  let g : C ⟶ Limits.pullback f (𝟙 (Spec (.of ℂ))) := Limits.pullback.lift (𝟙 C) f (by simp)
  have hg : Limits.pullback.fst f (𝟙 _) ≫ g = 𝟙 _ := by
    apply Limits.pullback.hom_ext
    · simp only [g, Category.assoc, Limits.pullback.lift_fst, Category.comp_id,
        Category.id_comp]
    · simp only [g, Category.assoc, Limits.pullback.lift_snd, Category.id_comp]
      exact Limits.pullback.condition.trans (Category.comp_id _)
  obtain ⟨L, hL, hLc⟩ := Stacks.SheafOfModules.exists_picardClass_eq C.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf C)
    (Stacks.Picard.schemePullbackClass g x)
  have hfx : Stacks.Picard.schemePullbackClass (Limits.pullback.fst f (𝟙 _))
      (Stacks.SheafOfModules.picardClass C.presheaf _ L hL) = x := by
    rw [hLc, Stacks.Picard.schemePullbackClass_comp, hg, Stacks.Picard.schemePullbackClass_id]
  obtain ⟨hinvG, eG, heG, -⟩ := exists_mulEquiv_picardGroup_analytification_of_isProjective f hproj
  have hLan1 : Stacks.SheafOfModules.IsInvertible (analytification f : RingedSpace).sheaf.obj
      (structureSheaf (analytification f : RingedSpace).sheaf).property
      ((analytifyModule f).obj L) :=
    @Stacks.RingedSpace.isInvertible_modulePullback _ _ (analytificationHom f) L hL
  have h1 := (hΦ v L hL hLan1 hfx).trans hexp.symm
  have h2 := ((picardToSheafPicard_classOf (analytification f : RingedSpace).sheaf.obj
    (structureSheaf (analytification f : RingedSpace).sheaf).property _ hLan1).symm.trans
      (congrArg (picardToSheafPicard _ _) h1)).trans
    (picardToSheafPicard_classOf (analytification f : RingedSpace).sheaf.obj
      (structureSheaf (analytification f : RingedSpace).sheaf).property _ hLan)
  set M := (Stacks.RingedSpace.pullbackFunctor ι.toLRSHom.toShHom).obj LX
  have hM : Stacks.SheafOfModules.IsInvertible C.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf C) M :=
    Stacks.RingedSpace.modulePullback_isInvertible_of _ LX hLX
  have : Stacks.Ample.IsInvertibleModule C L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).1 hL
  have : Stacks.Ample.IsInvertibleModule C M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).1 hM
  have h3 : eG (Stacks.SheafPicardGroup.schemeClassOf C L) =
      eG (Stacks.SheafPicardGroup.schemeClassOf C M) :=
    (heG L).trans ((Additive.ofMul.injective h2).trans (heG M).symm)
  have h5 : Stacks.SheafOfModules.picardClass C.presheaf _ L hL =
      Stacks.SheafOfModules.picardClass C.presheaf _ M hM :=
    (Stacks.SheafOfModules.picardClass_eq_iff _ _ L M hL hM).2
      ((Stacks.SheafPicardGroup.schemeClassOf_eq_schemeClassOf_iff C L M).1 (eG.injective h3))
  rw [← Stacks.Picard.schemePullbackClass_comp]
  exact (congrArg (Stacks.Picard.schemePullbackClass (Limits.pullback.fst f (𝟙 _)))
    ((Stacks.Picard.pullbackClass_classOf ι.toLRSHom.toShHom LX hLX).trans h5.symm)).trans hfx

/-- The rigidified class of a `ℂ`-point of a Jacobian determines the point. -/
theorem eq_of_smallEquiv_eq {x x' : ComplexPoints JX.X.hom}
    (h : Stacks.RigidifiedPicard.smallEquiv _ (Multiplicative.toAdd
        ((eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x.1 x.2))).1.1 =
      Stacks.RigidifiedPicard.smallEquiv _ (Multiplicative.toAdd
        ((eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x'.1 x'.2))).1.1) : x = x' := by
  have h2 : (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x.1 x.2) =
      (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x'.1 x'.2) :=
    Multiplicative.toAdd.injective
      (Subtype.ext (Subtype.ext ((Stacks.RigidifiedPicard.smallEquiv _).injective h)))
  have h3 := ((eJ.app (op (Over.mk (𝟙 _)))).groupIsoToMulEquiv).injective h2
  exact Subtype.ext (congrArg CommaMorphism.left h3)

end Restriction

/-- The first-cohomology comparison of `Stacks.Thickenings.sheafCohomologyOneExtEquiv` for the
units of `X^an`, read on the space `X(ℂ)`. -/
theorem sheafCohomologyOneExtEquiv_analytification {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) :
    Stacks.Thickenings.sheafCohomologyOneExtEquiv (analytification sX : RingedSpace).carrier
      (Stacks.Cohomology.Generators.unitsSheaf (analytification sX)) =
    Stacks.Thickenings.sheafCohomologyOneExtEquiv (space sX)
      (Stacks.Cohomology.Generators.unitsSheaf (analytification sX)) := rfl

/-- **Translates from a countable obstruction.** Let `ρ : Y → P` and `κ : Y → H` be additive,
`H` countable, `rig : T → P` injective and `Φ : ℂⁿ → T` onto, with `rig ∘ Φ` additive. If every
`ρ y` with `κ y = 0` is `rig (Φ v)` for some `v ∈ V`, then the points `x` with `rig x` in the
range of `ρ` lie in countably many translates `Φ(aₖ + V)`. -/
theorem exists_translates_of_forall_eq_zero {Y P H T : Type*} [AddCommGroup Y] [AddCommGroup P]
    [AddCommGroup H] [Countable H] {n : ℕ} (ρ : Y →+ P) (κ : Y →+ H) (rig : T → P)
    (hrig : Function.Injective rig) (Φ : (Fin n → ℂ) → T)
    (hadd : ∀ u u', rig (Φ (u + u')) = rig (Φ u) + rig (Φ u'))
    (hsurj : Function.Surjective Φ) (V : Set (Fin n → ℂ))
    (hker : ∀ y, κ y = 0 → ∃ v ∈ V, rig (Φ v) = ρ y) :
    ∃ a : ℕ → Fin n → ℂ, ∀ x : T, (∃ y, ρ y = rig x) →
      x ∈ ⋃ k, (fun v => Φ (a k + v)) '' V := by
  classical
  let Q : H → (Fin n → ℂ) → Prop := fun β a => ∃ y, κ y = β ∧ ρ y = rig (Φ a)
  let c : H → Fin n → ℂ := fun β => if h : ∃ a, Q β a then h.choose else 0
  have hc : ∀ β, (∃ a, Q β a) → Q β (c β) := fun β h => by
    simp only [c]
    split_ifs
    exact h.choose_spec
  obtain ⟨a, ha⟩ := Set.countable_iff_exists_subset_range.1
    ((Set.to_countable (Set.range κ)).image c)
  refine ⟨a, fun x ⟨y, hy⟩ => ?_⟩
  obtain ⟨u, rfl⟩ := hsurj x
  obtain ⟨y0, hy0κ, hy0⟩ := hc (κ y) ⟨u, y, rfl, hy⟩
  obtain ⟨k, hk⟩ := ha ⟨κ y, ⟨y, rfl⟩, rfl⟩
  obtain ⟨v, hv, hvy⟩ := hker (y - y0) (by rw [map_sub, hy0κ, sub_self])
  refine Set.mem_iUnion.2 ⟨k, v, hv, hrig ?_⟩
  rw [hk, hadd, ← hy0, hvy, map_sub, hy]
  abel

/-- **Naturality of the exponential map under restriction.** For `ι : C ⟶ X` over `ℂ` and a map
`e : 𝒪_{C^an} ⟶ 𝒪_{C^an}^×` (in use, the exponential map of `C^an`): for every exponential map
`e_X` of `X^an` (the class of `exp (2πi g)` on every chart germ `g`), every
`w ∈ H¹(X^an, 𝒪)` and every invertible `𝒪_X`-module `L_X` with `[L_X^an] = exp_X w` in
`Pic(X^an)`, the class of `(ι^* L_X)^an` in `Pic(C^an)` is `exp_C (res w)`, where `res` is the
analytic restriction `MMP.Analytic.SurfaceHodge.analyticRestrictionH1`. -/
def IsExpNaturalRestriction {X C : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (ι : C ⟶ X)
    [LocallyOfFiniteType sX] [LocallyOfFiniteType (ι ≫ sX)]
    (e : analyticO (ι ≫ sX) ⟶
      Stacks.Cohomology.Generators.unitsSheaf (analytification (ι ≫ sX))) : Prop :=
  ∀ (eX : analyticO sX ⟶ Stacks.Cohomology.Generators.unitsSheaf (analytification sX)),
    (∀ (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W)
      (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U})
      (g : (Fin c.1.n → ℂ) → ℂ) (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
      (γ : Filter.Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
      (γ' : Filter.Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
        (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
      s.1 x c = Chart.StalkRing.mk c.1 _ γ →
      ((Additive.toMul (eX.hom.app (op W) s) : ((structureSheaf sX).obj.obj (op W))ˣ) :
        (structureSheaf sX).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ γ') →
    ∀ (w : Sheaf.H (analyticO sX) 1) (LX : X.Modules)
      (_ : Stacks.SheafOfModules.IsInvertible X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) LX)
      (hLXan : Stacks.SheafOfModules.IsInvertible (analytification sX : RingedSpace).sheaf.obj
        (structureSheaf (analytification sX : RingedSpace).sheaf).property
        ((analytifyModule sX).obj LX))
      (hLan : Stacks.SheafOfModules.IsInvertible
        (analytification (ι ≫ sX) : RingedSpace).sheaf.obj
        (structureSheaf (analytification (ι ≫ sX) : RingedSpace).sheaf).property
        ((analytifyModule (ι ≫ sX)).obj
          ((Stacks.RingedSpace.pullbackFunctor ι.toLRSHom.toShHom).obj LX))),
      Stacks.SheafOfModules.Picard.classOf _ _ _ hLXan =
        Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup (analytification sX)
          ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
            (space sX) (Stacks.Cohomology.Generators.unitsSheaf (analytification sX)))).symm
            (Sheaf.H.map eX 1 w)) →
      Stacks.SheafOfModules.Picard.classOf _ _ _ hLan =
        Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup (analytification (ι ≫ sX))
          ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
            (space (ι ≫ sX))
            (Stacks.Cohomology.Generators.unitsSheaf (analytification (ι ≫ sX))))).symm
            (Sheaf.H.map e 1 (analyticRestrictionH1 (sX := sX) ι rfl w)))

/-- **Exponential classes restrict to exponential points.** Let `Φ` be the exponential
uniformisation of the Jacobian of a curve `ι : C ⟶ X`, `V` the preimage under `φ` of the image of
the analytic restriction, and suppose the exponential map is natural under restriction. If an
invertible `𝒪_X`-module `L_X` has analytic class `exp_X w`, then the restriction of its class to
`C` is the rigidified class of `Φ v` for some `v ∈ V`. -/
theorem exists_mem_schemePullbackClass_eq_of_classOf_eq {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {C : Scheme.{0}}
    (ι : C ⟶ X) [LocallyOfFiniteType (ι ≫ (X ↘ Spec (.of ℂ)))]
    (hproj : IsProjective (ι ≫ (X ↘ Spec (.of ℂ))))
    (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥((ι ≫ (X ↘ Spec (.of ℂ))).fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ ι ≫ (X ↘ Spec (.of ℂ)) = 𝟙 _)
    (e : analyticO (ι ≫ (X ↘ Spec (.of ℂ))) ⟶
      Stacks.Cohomology.Generators.unitsSheaf (analytification (ι ≫ (X ↘ Spec (.of ℂ)))))
    (hnat : IsExpNaturalRestriction (X ↘ Spec (.of ℂ)) ι e)
    {JX : Grp (Over (Spec (.of ℂ)))}
    (eJ : haveI := hproj.isProper
      yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero _ hdim σ hσ)
    {n : ℕ} (φ : (Fin n → ℂ) ≃+ Sheaf.H (analyticO (ι ≫ (X ↘ Spec (.of ℂ)))) 1)
    (Φ : (Fin n → ℂ) → space JX.X.hom)
    (hΦ : haveI := hproj.isProper
      IsExpUniformisation _ hdim σ hσ eJ
      (letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup
        (analytification (ι ≫ (X ↘ Spec (.of ℂ))));
        (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup
            (analytification (ι ≫ (X ↘ Spec (.of ℂ))))).toAddMonoidHom.comp
          ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
            (space (ι ≫ (X ↘ Spec (.of ℂ))))
            (Stacks.Cohomology.Generators.unitsSheaf
              (analytification (ι ≫ (X ↘ Spec (.of ℂ))))))).symm.toAddMonoidHom.comp
            (Sheaf.H.map e 1)))
      φ Φ)
    (V : Submodule ℂ (Fin n → ℂ))
    (hV : (V : Set (Fin n → ℂ)) =
      φ ⁻¹' Set.range (analyticRestrictionH1 (sX := X ↘ Spec (.of ℂ)) ι rfl))
    (eX : analyticO (X ↘ Spec (.of ℂ)) ⟶
      Stacks.Cohomology.Generators.unitsSheaf (analytification (X ↘ Spec (.of ℂ))))
    (heX : ∀ (W : Opens (space (X ↘ Spec (.of ℂ))))
      (s : (structureSheaf (X ↘ Spec (.of ℂ))).obj.obj (op W)) (x : W)
      (c : {c : Chart (X ↘ Spec (.of ℂ)) // x.1 ∈ ComplexPoints.chart c.U})
      (g : (Fin c.1.n → ℂ) → ℂ) (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
      (γ : Filter.Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
      (γ' : Filter.Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
        (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
      s.1 x c = Chart.StalkRing.mk c.1 _ γ →
      ((Additive.toMul (eX.hom.app (op W) s) :
          ((structureSheaf (X ↘ Spec (.of ℂ))).obj.obj (op W))ˣ) :
        (structureSheaf (X ↘ Spec (.of ℂ))).obj.obj (op W)).1 x c =
          Chart.StalkRing.mk c.1 _ γ')
    (w : Sheaf.H (analyticO (X ↘ Spec (.of ℂ))) 1) (LX : X.Modules)
    (hLX : Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) LX)
    (hLXan : Stacks.SheafOfModules.IsInvertible
      (analytification (X ↘ Spec (.of ℂ)) : RingedSpace).sheaf.obj
      (structureSheaf (analytification (X ↘ Spec (.of ℂ)) : RingedSpace).sheaf).property
      ((analytifyModule (X ↘ Spec (.of ℂ))).obj LX))
    (h1 : Stacks.SheafOfModules.Picard.classOf _ _ _ hLXan =
      Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup
        (analytification (X ↘ Spec (.of ℂ)))
        ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
          (space (X ↘ Spec (.of ℂ)))
          (Stacks.Cohomology.Generators.unitsSheaf
            (analytification (X ↘ Spec (.of ℂ)))))).symm (Sheaf.H.map eX 1 w))) :
    haveI := hproj.isProper
    ∃ v ∈ V, Stacks.RigidifiedPicard.smallEquiv _ (Multiplicative.toAdd
        ((eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ v).1 (Φ v).2))).1.1 =
      Stacks.Picard.schemePullbackClass
        (Limits.pullback.fst (ι ≫ (X ↘ Spec (.of ℂ))) (𝟙 _) ≫ ι)
        (Stacks.SheafOfModules.picardClass X.presheaf _ LX hLX) := by
  have := hproj.isProper
  have hM := Stacks.RingedSpace.modulePullback_isInvertible_of ι.toLRSHom.toShHom LX hLX
  have hLan := @Stacks.RingedSpace.isInvertible_modulePullback _ _
    (analytificationHom (ι ≫ (X ↘ Spec (.of ℂ)))) _ hM
  have h2 := hnat eX heX w LX hLX hLXan hLan h1
  refine ⟨φ.symm (analyticRestrictionH1 (sX := X ↘ Spec (.of ℂ)) ι rfl w), ?_, ?_⟩
  · rw [← SetLike.mem_coe, hV]
    exact ⟨w, (φ.apply_symm_apply _).symm⟩
  · refine (schemePullbackClass_eq_of_isExpUniformisation ι _ hdim σ hσ eJ _ φ Φ hproj hΦ _ LX
      hLX hLan (h2.trans ?_)).symm
    exact congrArg _ (congrArg _ (congrArg _ (φ.apply_symm_apply _).symm))

/-- **Restriction points lie in countably many translates.** Let `X` be a smooth projective
surface over `ℂ`, `ι : C ⟶ X` a smooth projective curve with a point `σ`, `JX` the Jacobian of
`C` and `Φ : ℂⁿ → JX(ℂ)` its exponential uniformisation for coordinates
`φ : ℂⁿ ≃ H¹(C^an, 𝒪)` (`IsExpUniformisation`, with `e` the exponential map of `C^an`), additive
and onto. Let `V` be the preimage under `φ` of the image of the analytic restriction
`H¹(X^an, 𝒪) → H¹(C^an, 𝒪)`. Suppose the exponential map is natural under restriction
(`hnat`): whenever `L_X^an` has class `exp_X w`, the class of `(ι^* L_X)^an` is
`exp_C (res w)`. Then every restriction point lies in one of countably many translates
`Φ(aₖ + V)`. -/
theorem exists_translates_of_isRestrictionPoint {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))] {C : Scheme.{0}} (ι : C ⟶ X)
    [IsClosedImmersion ι] (hproj : IsProjective (ι ≫ (X ↘ Spec (.of ℂ))))
    [SmoothOfRelativeDimension 1 (ι ≫ (X ↘ Spec (.of ℂ)))]
    (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥((ι ≫ (X ↘ Spec (.of ℂ))).fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ ι ≫ (X ↘ Spec (.of ℂ)) = 𝟙 _)
    (e : analyticO (ι ≫ (X ↘ Spec (.of ℂ))) ⟶
      Stacks.Cohomology.Generators.unitsSheaf (analytification (ι ≫ (X ↘ Spec (.of ℂ)))))
    (_he : ∀ (W : Opens (space (ι ≫ (X ↘ Spec (.of ℂ)))))
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
    (hnat : IsExpNaturalRestriction (X ↘ Spec (.of ℂ)) ι e)
    {JX : Grp (Over (Spec (.of ℂ)))}
    (eJ : haveI := hproj.isProper
      yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero _ hdim σ hσ)
    {n : ℕ} (φ : (Fin n → ℂ) ≃+ Sheaf.H (analyticO (ι ≫ (X ↘ Spec (.of ℂ)))) 1)
    (Φ : (Fin n → ℂ) → space JX.X.hom)
    (hΦ : haveI := hproj.isProper
      IsExpUniformisation _ hdim σ hσ eJ
      (letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup
        (analytification (ι ≫ (X ↘ Spec (.of ℂ))));
        (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup
            (analytification (ι ≫ (X ↘ Spec (.of ℂ))))).toAddMonoidHom.comp
          ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
            (space (ι ≫ (X ↘ Spec (.of ℂ))))
            (Stacks.Cohomology.Generators.unitsSheaf
              (analytification (ι ≫ (X ↘ Spec (.of ℂ))))))).symm.toAddMonoidHom.comp
            (Sheaf.H.map e 1)))
      φ Φ)
    (hadd : ∀ v v' : Fin n → ℂ,
      (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ (v + v')).1 (Φ (v + v')).2) =
        (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ v).1 (Φ v).2) *
          (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ v').1 (Φ v').2))
    (hsurj : Function.Surjective Φ)
    (V : Submodule ℂ (Fin n → ℂ))
    (hV : (V : Set (Fin n → ℂ)) =
      φ ⁻¹' Set.range (analyticRestrictionH1 (sX := X ↘ Spec (.of ℂ)) ι rfl)) :
    haveI := hproj.isProper
    ∃ a : ℕ → Fin n → ℂ, ∀ x : ComplexPoints JX.X.hom, IsRestrictionPoint ι _ hdim σ hσ eJ x →
      x ∈ ⋃ k, (fun v => Φ (a k + v)) '' (V : Set (Fin n → ℂ)) := by
  have := hproj.isProper
  have hXpm : IsProjectiveMorphism (X ↘ Spec (.of ℂ)) := IsProjectiveVariety.isProjective (k := ℂ)
  have hXp : IsProjective (X ↘ Spec (.of ℂ)) :=
    (isProjective_iff_isProjectiveMorphism_of_isAffine _).2 hXpm
  have : IsProper (X ↘ Spec (.of ℂ)) := hXp.isProper
  obtain ⟨ιZ, eX, w0, hS, -, heX⟩ := exists_shortExact_exponentialSequence (X ↘ Spec (.of ℂ))
  let := Stacks.Cohomology.Generators.picardGroupAddCommGroup
    (analytification (X ↘ Spec (.of ℂ)))
  obtain ⟨ψ, -, hψ⟩ := exists_addMonoidHom_picardGroup_analytification _ hXp
  have := countable_sheafH_constantSheaf (X ↘ Spec (.of ℂ)) hXpm 2
  obtain ⟨a, ha⟩ := exists_translates_of_forall_eq_zero
    (Stacks.Picard.schemePullbackClassHom
      (Limits.pullback.fst (ι ≫ (X ↘ Spec (.of ℂ))) (𝟙 _) ≫ ι))
    ((picardObstruction (analytification (X ↘ Spec (.of ℂ))) hS).comp ψ)
    (fun x : ComplexPoints JX.X.hom => Stacks.RigidifiedPicard.smallEquiv _
      (Multiplicative.toAdd ((eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x.1 x.2))).1.1)
    (fun x x' h => eq_of_smallEquiv_eq _ hdim σ hσ eJ h) Φ
    (fun u u' => by
      simp only
      rw [hadd u u']
      exact map_add (Stacks.RigidifiedPicard.smallEquiv _) _ _)
    hsurj (V : Set (Fin n → ℂ)) (fun y hy => by
      obtain ⟨w, hw⟩ := exists_sheafH_map_eq_of_picardObstruction_eq_zero _ hS _ hy
      obtain ⟨LX, hLX, rfl⟩ := Stacks.SheafOfModules.exists_picardClass_eq X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) y
      have hLXan := @Stacks.RingedSpace.isInvertible_modulePullback _ _
        (analytificationHom (X ↘ Spec (.of ℂ))) LX hLX
      have h1 := (hψ LX hLX hLXan).symm.trans hw.symm
      rw [sheafCohomologyOneExtEquiv_analytification] at h1
      exact exists_mem_schemePullbackClass_eq_of_classOf_eq ι hproj hdim σ hσ e hnat eJ φ Φ hΦ V
        hV eX heX w LX hLX hLXan h1)
  exact ⟨a, ha⟩

/-- **A countable closed cover of the exponential image.** Let `Φ : ℂⁿ → J(ℂ)` be the exponential
uniformisation of the Jacobian of a curve `ι : C ⟶ X` on a smooth projective surface, additive,
onto and holomorphic in the charts of `J`, and `V` the preimage under `φ` of the image of the
analytic restriction `H¹(X^an, 𝒪) → H¹(C^an, 𝒪)`. If the exponential map is natural under
restriction and every `Φ v`, `v ∈ V`, is a restriction point, then `Φ(V)` is covered by countably
many closed subsets of `J` of dimension at most `dim V`. -/
theorem exists_countable_isClosed_cover_of_restriction_pinned {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))] {C : Scheme.{0}} (ι : C ⟶ X)
    [IsClosedImmersion ι] (hproj : IsProjective (ι ≫ (X ↘ Spec (.of ℂ))))
    [SmoothOfRelativeDimension 1 (ι ≫ (X ↘ Spec (.of ℂ)))]
    (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥((ι ≫ (X ↘ Spec (.of ℂ))).fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ ι ≫ (X ↘ Spec (.of ℂ)) = 𝟙 _)
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
    (hnat : IsExpNaturalRestriction (X ↘ Spec (.of ℂ)) ι e)
    {JX : Grp (Over (Spec (.of ℂ)))} [LocallyOfFiniteType JX.X.hom]
    (eJ : haveI := hproj.isProper
      yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero _ hdim σ hσ)
    {n : ℕ} (φ : (Fin n → ℂ) ≃+ Sheaf.H (analyticO (ι ≫ (X ↘ Spec (.of ℂ)))) 1)
    (Φ : (Fin n → ℂ) → space JX.X.hom)
    (hΦ : haveI := hproj.isProper
      IsExpUniformisation _ hdim σ hσ eJ
      (letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup
        (analytification (ι ≫ (X ↘ Spec (.of ℂ))));
        (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup
            (analytification (ι ≫ (X ↘ Spec (.of ℂ))))).toAddMonoidHom.comp
          ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
            (space (ι ≫ (X ↘ Spec (.of ℂ))))
            (Stacks.Cohomology.Generators.unitsSheaf
              (analytification (ι ≫ (X ↘ Spec (.of ℂ))))))).symm.toAddMonoidHom.comp
            (Sheaf.H.map e 1)))
      φ Φ)
    (hadd : ∀ v v' : Fin n → ℂ,
      (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ (v + v')).1 (Φ (v + v')).2) =
        (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ v).1 (Φ v).2) *
          (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ v').1 (Φ v').2))
    (hsurj : Function.Surjective Φ)
    (hhol : ∀ (v : Fin n → ℂ) (c : Chart JX.X.hom) (_ : Φ v ∈ chart c.U),
      ∃ F : (Fin n → ℂ) → (Fin c.n → ℂ), DifferentiableAt ℂ F v ∧
        ∀ᶠ v' in nhds v, ∃ h' : Φ v' ∈ chart c.U, c.coords ⟨Φ v', h'⟩ = F v')
    (V : Submodule ℂ (Fin n → ℂ))
    (hV : (V : Set (Fin n → ℂ)) =
      φ ⁻¹' Set.range (analyticRestrictionH1 (sX := X ↘ Spec (.of ℂ)) ι rfl))
    (hR : haveI := hproj.isProper
      ∀ v ∈ V, IsRestrictionPoint ι _ hdim σ hσ eJ (Φ v)) :
    haveI := hproj.isProper
    ∃ (κ' : Type) (_ : Countable κ') (T' : κ' → Set JX.X.left), (∀ k, IsClosed (T' k)) ∧
      (∀ k, topologicalKrullDim (T' k) ≤ Module.finrank ℂ V) ∧
      ∀ v ∈ V, (Φ v).toScheme ∈ ⋃ k, T' k := by
  have := hproj.isProper
  obtain ⟨a, ha⟩ := exists_translates_of_isRestrictionPoint ι hproj hdim σ hσ e he hnat eJ φ Φ
    hΦ hadd hsurj V hV
  exact exists_countable_isClosed_cover_of_subset_iUnion ι hproj hdim σ hσ JX eJ Φ hhol V a ha hR

end MMP.Analytic.SurfaceHodge
