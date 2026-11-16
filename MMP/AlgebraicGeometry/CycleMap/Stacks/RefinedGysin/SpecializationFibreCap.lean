module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationSteps
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.DivisorTransversal
public import MMP.AlgebraicGeometry.CycleMap.Stacks.FibreSpecialization
public import MMP.AlgebraicTopology.BorelMoore.FibreClassConstancy
public import MMP.AlgebraicGeometry.CycleMap.Stacks.ExteriorProduct
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleCapRuleRestriction
public import MMP.AlgebraicTopology.BorelMoore.RestrictionFunctorial
public import MMP.AlgebraicTopology.SingularCohomology.Contractible
public import MMP.AlgebraicTopology.SingularCohomology.CupProduct.Comparison
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestrictionVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.NotDominant

/-!
# The specialization formula at a fibre of a family over a curve, on Stacks cycles

Let `ρ : M ⟶ B` be a morphism from a complex scheme to a smooth complex curve, `t ∈ B` a
parameter point, and `D = Z(s) ⊆ M` the zero scheme of a global section `s` of an invertible
module `L` on `M`, with `D = ρ⁻¹(t)` scheme-theoretically and `L|_D` trivial. For every
`β ∈ A_{k+1}(M)`,

  `ρ^* u_t ∩ cl(β) = cl(i^* β)`  in `H_{2k}(ρ⁻¹(t))`,

where `i^* : A_{k+1}(M) ⟶ A_k(D)` is Stacks' Gysin map of `s` (Stacks 02TO) and `u_t` the local
orientation class of `B(ℂ)` at `t`. This is the generic step of the specialization at `0` and at
`∞` of Fulton's proof of Theorem 19.2. Both sides are additive in `β`, so it suffices to treat a
prime cycle `[V]`, `V = closure {x}`:

* if `ρ|_V` is dominant, `i^*[V] = [V ∩ D]` (Stacks 02T8) and `V ∩ D` is the fibre `V_t`, so the
  formula is Fulton's Lemma 19.1.3 for `V ⟶ B`
  (`MMP.Chow.pushforward_cycleClass_fibre_eq_capProductSupportPullback_pointCycleClass`);
* if `V ⊆ D`, `i^*[V] = 0` because `L|_D` is trivial (Stacks, Remark 0B6Z), and `ρ^* u_t ∩ cl(V)`
  vanishes because `ρ` is constant on `V(ℂ)` and `H²` of a point is zero;
* otherwise `ρ(V)` is a closed point other than `t`, `V ∩ D = ∅` and both sides vanish.

## Main results

* `MMP.borelMooreHomology.capProductSupportPullback_eq_zero_of_const`: the supported cap product
  with a class of positive degree pulled back along a constant map vanishes.
* `MMP.Chow.capProductSupportPullback_cycleClass_eq_gysin`: the specialization formula.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, Lemma 19.1.3, and §19.2, proof of
  Theorem 19.2.
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Topology Stacks.Chow
open MMP.UnderlyingSpace

namespace MMP

namespace borelMooreHomology

variable (R : Type) [CommRing R]

/-- The singular cohomology of a point vanishes in positive degrees. -/
theorem subsingleton_relativeSingularCohomology_punit (p : ℕ) (hp : 0 < p) :
    Subsingleton (relativeSingularCohomology R (ModuleCat.of R R) (TopCat.of PUnit.{1})
      (∅ : Set (TopCat.of PUnit.{1})) (p : ℤ)) := by
  let H : TopCat.Homotopy (𝟙 (TopCat.of PUnit.{1}))
      (TopCat.ofHom (ContinuousMap.const (TopCat.of PUnit.{1}) PUnit.unit)) :=
    { toFun := fun _ ↦ PUnit.unit
      continuous_toFun := continuous_const
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun _ ↦ rfl }
  refine (SingularCochain.relativeSingularCohomologyEquiv R ∅ p).toEquiv.subsingleton_congr.2
    ⟨fun a b ↦ ?_⟩
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [PoincareAlexander.mk_eq_zero_of_homotopy_const PUnit.unit H hp φ,
    PoincareAlexander.mk_eq_zero_of_homotopy_const PUnit.unit H hp ψ]

/-- **The supported cap product along a constant map.** If `f : Y' ⟶ T` is constant, then
`f^* c ∩ a = 0` for every class `c ∈ H^p(T, T - X)` of positive degree: `f^* c` is pulled back
from a point. -/
theorem capProductSupportPullback_eq_zero_of_const {Y' T : TopCat.{0}} (f : Y' ⟶ T) (t : T)
    (hf : ∀ y, f y = t) {X : Set T} (hX : IsClosed X)
    (hd : HasProperNeighbourhoodDeformations (f ⁻¹' X)) (p : ℕ) (hp : 0 < p) (k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) T X (p : ℤ))
    (a : borelMooreHomology R (ModuleCat.of R R) Y' k) :
    capProductSupportPullback R f hX hd (p : ℤ) k c a = 0 := by
  by_cases htX : t ∈ X
  · let g : Y' ⟶ TopCat.of PUnit.{1} := TopCat.ofHom (ContinuousMap.const Y' PUnit.unit)
    let h : TopCat.of PUnit.{1} ⟶ T := TopCat.ofHom (ContinuousMap.const _ t)
    have hfgh : f = g ≫ h := by
      ext y
      exact hf y
    subst hfgh
    rw [capProductSupportPullback_apply, cohomologyWithSupports.pullback_comp]
    have hS : h ⁻¹' X = univ := eq_univ_of_forall fun _ ↦ htX
    have hsub : Subsingleton (cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of PUnit.{1})
        (h ⁻¹' X) (p : ℤ)) := by
      rw [hS]
      change Subsingleton (relativeSingularCohomology R (ModuleCat.of R R) _ univᶜ (p : ℤ))
      rw [compl_univ]
      exact subsingleton_relativeSingularCohomology_punit R p hp
    rw [ModuleCat.comp_apply, Subsingleton.elim
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R) h X (p : ℤ)).hom c) 0, map_zero,
      map_zero, LinearMap.zero_apply]
  · have : IsEmpty (f ⁻¹' X) := ⟨fun y ↦ htX (hf y.1 ▸ y.2)⟩
    exact (ModuleCat.subsingleton_of_isZero (isZero_borelMooreHomology_of_isEmpty R
      (ModuleCat.of R R) (TopCat.of (f ⁻¹' X)) (k - p))).elim _ _

end borelMooreHomology

namespace Chow

open borelMooreHomology MMP.Fourfold
open scoped MMP.SubschemeOver

variable (R : Type) [CommRing R]

section Dominant

variable {B M : Scheme.{0}} [B.Over (Spec (.of ℂ))] [IsSmoothVariety ℂ (B ↘ Spec (.of ℂ))]
  [M.Over (Spec (.of ℂ))] [IsComplexScheme M] (ρ : M ⟶ B) [ρ.IsOver (Spec (.of ℂ))]

/-- **Fulton's Lemma 19.1.3 for a subvariety, read in the ambient family.** For `ρ : M ⟶ B` over
a smooth complex curve and `V = closure {x} ⊆ M` of dimension `n + 1` dominating `B`, the class
of the scheme-theoretic fibre `V_t`, pushed into `ρ⁻¹(t)`, is `ρ^* u_t ∩ cl_M(V)`. -/
theorem pushforward_fibreAmbientPointsHom_cycleClass_eq_capProductSupportPullback
    (hB : SmoothOfRelativeDimension 1 (B ↘ Spec (.of ℂ))) {n : ℕ} (x : M)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (M ↘ Spec (.of ℂ)) x =
      ((n + 1 : ℕ) : ℤ))
    [IsDominant ((integralComponentAt x).subschemeι ≫ ρ)] (t : ParameterPoint B)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ B))
      {t.complexPoint} (2 * 1 : ℕ)}
    (hu : IsLocalOrientationClass (T := TopCat.of (UnderlyingSpace ℂ B)) R
      curveOrientationBasis t.complexPoint u) :
    (pushforward R (ModuleCat.of R R)
        (fibreAmbientPointsHom (integralComponentAt x).subschemeι ρ rfl t)
        (isProperMap_fibreAmbientPointsHom (integralComponentAt x).subschemeι ρ rfl t)
        (2 * n : ℕ)).hom
        (cycleClass R n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
          (ParameterPoint.fibre ((integralComponentAt x).subschemeι ≫ ρ) t ↘ Spec (.of ℂ))
          (𝟙 _) n)) =
      BorelMooreCross.congrDegree R _ (by push_cast; ring)
        (capProductSupportPullback R (TopCat.ofHom (map (K := ℂ) ρ)) isClosed_singleton
          (hasProperNeighbourhoodDeformations_preimage_singleton ρ _) (2 * 1 : ℕ)
          (2 * (n + 1) : ℕ) u (pointCycleClass R x hx)) :=
  MMP.Chow.pushforward_cycleClass_fibre_eq_capProductSupportPullback_pointCycleClass R hB ρ
    x hx t t.complexPoint (ParameterPoint.complexPoint_toHom_closedPoint t) _ _ (fun _ ↦ rfl) _ u hu

omit [M.Over (Spec (.of ℂ))] [IsComplexScheme M] [ρ.IsOver (Spec (.of ℂ))] in
/-- For `D = ρ⁻¹(t)` and a closed subscheme `V ⊆ M`, the ideal sheaf of the fibre `V_t` in `V` is
the pullback of the ideal sheaf of `D` along `V ⟶ M`. -/
theorem ker_fibreι_comp_eq (t : ParameterPoint B) {D : M.IdealSheafData}
    (hD : D = t.ι.ker.comap ρ) (V : M.IdealSheafData) :
    (ParameterPoint.fibreι (V.subschemeι ≫ ρ) t).ker = D.comap V.subschemeι := by
  have h : (ParameterPoint.fibreι (V.subschemeι ≫ ρ) t).ker = t.ι.ker.comap (V.subschemeι ≫ ρ) := by
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      ← (ParameterPoint.isPullback_fibre (V.subschemeι ≫ ρ) t).isoPullback_hom_fst,
      Scheme.Hom.ker_comp_of_isIso]
  rw [h, hD, Scheme.IdealSheafData.comap_comp]

/-- **`V ∩ ρ⁻¹(t)` is the fibre `V_t`.** For a closed subscheme `D = ρ⁻¹(t)` of `M` (the inverse
image of the reduced point `t`) and a closed subscheme `V ⊆ M`, the closed subscheme `V ∩ D` of
`D` is the scheme-theoretic fibre of `V ⟶ M ⟶ B` at `t`. -/
def comapFibreIso (t : ParameterPoint B) {D : M.IdealSheafData} (hD : D = t.ι.ker.comap ρ)
    (V : M.IdealSheafData) :
    (V.comap D.subschemeι).subscheme ≅ ParameterPoint.fibre (V.subschemeι ≫ ρ) t :=
  V.comapIso D.subschemeι ≪≫ pullbackSymmetry _ _ ≪≫ (D.comapIso V.subschemeι).symm ≪≫
    (asIso (toSubschemeOfEqKer (ParameterPoint.fibreι (V.subschemeι ≫ ρ) t) _
      (ker_fibreι_comp_eq ρ t hD V).symm)).symm

omit [M.Over (Spec (.of ℂ))] [IsComplexScheme M] [ρ.IsOver (Spec (.of ℂ))] in
/-- The identification `V ∩ D ≅ V_t` is compatible with the maps to `M`. -/
theorem comapFibreIso_hom_fibreι (t : ParameterPoint B) {D : M.IdealSheafData}
    (hD : D = t.ι.ker.comap ρ) (V : M.IdealSheafData) :
    (comapFibreIso ρ t hD V).hom ≫ ParameterPoint.fibreι (V.subschemeι ≫ ρ) t ≫ V.subschemeι =
      (V.comap D.subschemeι).subschemeι ≫ D.subschemeι := by
  have he : inv (toSubschemeOfEqKer (ParameterPoint.fibreι (V.subschemeι ≫ ρ) t) _
      (ker_fibreι_comp_eq ρ t hD V).symm) ≫ ParameterPoint.fibreι (V.subschemeι ≫ ρ) t =
      (D.comap V.subschemeι).subschemeι := by
    rw [IsIso.inv_comp_eq, toSubschemeOfEqKer_subschemeι]
  simp only [comapFibreIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc]
  rw [reassoc_of% he, Scheme.IdealSheafData.comapIso_inv_subschemeι_assoc,
    pullbackSymmetry_hom_comp_fst_assoc, ← pullback.condition,
    Scheme.IdealSheafData.comapIso_hom_fst_assoc]

/-- On an integral scheme `B` of dimension one over `ℂ`, a point is the generic point or a
closed point. -/
theorem eq_genericPoint_or_isClosed_of_smooth (hB : SmoothOfRelativeDimension 1 (B ↘ Spec (.of ℂ)))
    (b : B) :
    haveI : IsIntegral B := (inferInstance : IsSmoothVariety ℂ (B ↘ Spec (.of ℂ))).toIsIntegral
    b = genericPoint B ∨ IsClosed ({b} : Set B) := by
  have : IsIntegral B := (inferInstance : IsSmoothVariety ℂ (B ↘ Spec (.of ℂ))).toIsIntegral
  have h1 := topologicalKrullDim_eq_of_smoothOfRelativeDimension (K := ℂ) (X := B) 1
  exact eq_genericPoint_or_isClosed (fieldChowSituation ℂ)
    (fieldChowSituation_dimensionFunction_eq_zero ℂ) (B ↘ Spec (.of ℂ))
    (schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq
      (B ↘ Spec (.of ℂ)) (n := 1) (by exact_mod_cast h1)) b

omit [B.Over (Spec (.of ℂ))] [IsSmoothVariety ℂ (B ↘ Spec (.of ℂ))] [M.Over (Spec (.of ℂ))]
    [IsComplexScheme M] [ρ.IsOver (Spec (.of ℂ))] in
/-- The support of `ρ⁻¹(t)` is the set-theoretic fibre over `t`. -/
theorem coe_support_comap_ker (t : ParameterPoint B) :
    ((t.ι.ker.comap ρ).support : Set M) = ρ.base ⁻¹' {t.point} := by
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Scheme.Hom.support_ker, ParameterPoint.range_ι, t.isClosed_point.closure_eq]

omit [B.Over (Spec (.of ℂ))] [IsSmoothVariety ℂ (B ↘ Spec (.of ℂ))] [M.Over (Spec (.of ℂ))]
    [IsComplexScheme M] [ρ.IsOver (Spec (.of ℂ))] in
/-- A point of `closure {x}` maps into `closure {ρ x}`. -/
theorem map_mem_closure_singleton {x y : M} (hy : y ∈ closure ({x} : Set M)) :
    ρ.base y ∈ closure ({ρ.base x} : Set B) := by
  have := image_closure_subset_closure_image (f := ρ.base) ρ.continuous ⟨y, hy, rfl⟩
  rwa [image_singleton] at this

omit [IsSmoothVariety ℂ (B ↘ Spec (.of ℂ))] [IsComplexScheme M] in
/-- The complex points of `closure {x}` map to points of `closure {ρ x}`. -/
theorem map_toHom_mem_closure (x : M) (v : UnderlyingSpace ℂ (integralComponentAt x).subscheme) :
    (map (K := ℂ) ((integralComponentAt x).subschemeι ≫ ρ) v).toHom
        (IsLocalRing.closedPoint ℂ) ∈ closure ({ρ.base x} : Set B) := by
  rw [toHom_map]
  refine map_mem_closure_singleton ρ ?_
  rw [← coe_support_integralComponentAt, ← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨_, rfl⟩

omit [B.Over (Spec (.of ℂ))] [IsSmoothVariety ℂ (B ↘ Spec (.of ℂ))] [M.Over (Spec (.of ℂ))]
    [IsComplexScheme M] [ρ.IsOver (Spec (.of ℂ))] in
/-- If `ρ x` is a closed point other than `t`, then `closure {x}` misses `D = ρ⁻¹(t)`. -/
theorem isEmpty_comap_integralComponentAt_of_isClosed (t : ParameterPoint B)
    {D : M.IdealSheafData} (hD : (D.support : Set M) = ρ.base ⁻¹' {t.point}) {x : M}
    (hxt : ρ.base x ≠ t.point) (hcl : IsClosed ({ρ.base x} : Set B)) :
    IsEmpty ((integralComponentAt x).comap D.subschemeι).subscheme := by
  refine ⟨fun z ↦ hxt ?_⟩
  have hzD : (((integralComponentAt x).comap D.subschemeι).subschemeι ≫ D.subschemeι).base z ∈
      (D.support : Set M) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨_, rfl⟩
  have hzV : (((integralComponentAt x).comap D.subschemeι).subschemeι ≫ D.subschemeι).base z ∈
      closure ({x} : Set M) := by
    have h1 : ((integralComponentAt x).comap D.subschemeι).subschemeι.base z ∈
        (((integralComponentAt x).comap D.subschemeι).support : Set D.subscheme) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨_, rfl⟩
    rw [Scheme.IdealSheafData.support_comap] at h1
    rwa [← coe_support_integralComponentAt x]
  rw [hD] at hzD
  have h2 := map_mem_closure_singleton ρ hzV
  rw [hcl.closure_eq, mem_singleton_iff] at h2
  exact h2.symm.trans (mem_singleton_iff.mp (mem_preimage.mp hzD))

end Dominant

/-! ### The specialization formula -/

section Gysin

variable {B M : Scheme.{0}} [B.Over (Spec (.of ℂ))] [IsSmoothVariety ℂ (B ↘ Spec (.of ℂ))]
  [M.Over (Spec (.of ℂ))] [IsComplexScheme M] (ρ : M ⟶ B) [ρ.IsOver (Spec (.of ℂ))]
  (L : M.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible M.sheaf.obj M.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- A closed subscheme of a complex scheme, over `ℂ` through its inclusion, is a complex
scheme. -/
theorem isComplexScheme_subscheme {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
    (I : Z.IdealSheafData) : IsComplexScheme I.subscheme :=
  isComplexScheme_of_isClosedImmersion I.subschemeι

attribute [local instance] isComplexScheme_subscheme

/-- The fundamental cycle of `closure {x}` is the prime cycle `[x]`. -/
theorem cycleAssociatedToClosedSubscheme_integralComponentAt_eq_pointCycle
    (C : ChowSituation.{0}) {X : Scheme.{0}} (p : X ⟶ C.S) [LocallyOfFiniteType p] {k : ℤ}
    (x : X) (hx : relativeDimension C.dimensionFunction p x = k) :
    cycleAssociatedToClosedSubscheme C p (integralComponentAt x).subschemeι k =
      pointCycle C p k x hx := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  rw [pointCycle_apply]
  split_ifs with hy
  · subst hy
    exact cycleAssociatedToClosedSubscheme_integralComponentAt_self _ p y
      (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq _ p y hx)
  · exact cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne _ p k x hy

/-- **Remark 0B6Z on a prime cycle.** If `L|_D` is trivial, the Gysin map of `s` kills the prime
cycle of a point of `D = Z(s)`. -/
theorem gysinHomomorphismOfInvertible_pointCycle_eq_zero
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme M L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme M L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme M L s).subschemeι).obj L))
    {k : ℤ} (x : M)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (M ↘ Spec (.of ℂ)) x = k + 1)
    (hxD : x ∈ ((Stacks.Divisors.zeroScheme M L s).support : Set M)) :
    gysinHomomorphismOfInvertible (fieldChowSituation ℂ) (M ↘ Spec (.of ℂ)) k L s
      (pointCycle (fieldChowSituation ℂ) (M ↘ Spec (.of ℂ)) (k + 1) x hx) = 0 := by
  rw [← Scheme.IdealSheafData.range_subschemeι] at hxD
  obtain ⟨y, rfl⟩ := hxD
  have hy : relativeDimension (fieldChowSituation ℂ).dimensionFunction
      ((Stacks.Divisors.zeroScheme M L s).subschemeι ≫ M ↘ Spec (.of ℂ)) y = k + 1 := by
    rwa [relativeDimension_comp_closedImmersion]
  rw [← properPushforward_pointCycle (fieldChowSituation ℂ) (M ↘ Spec (.of ℂ)) _
    (Stacks.Divisors.zeroScheme M L s).subschemeι rfl (k + 1) y hy hx]
  exact gysinHomomorphismOfInvertible_properPushforward_zeroSchemeι_eq_zero _ _ k L s htriv _

variable (t : ParameterPoint B)

/-- `ρ⁻¹(t)(ℂ)` has arbitrarily small proper neighbourhood deformations. -/
abbrev fibreDeformations :
    HasProperNeighbourhoodDeformations ((TopCat.ofHom (map (K := ℂ) ρ)).hom ⁻¹'
      {t.complexPoint}) :=
  hasProperNeighbourhoodDeformations_preimage_singleton ρ _

/-- **`ρ^* u_t ∩ cl(V) = 0` for `V` inside the fibre `ρ⁻¹(t)`**: `ρ` is constant on `V(ℂ)`. -/
theorem capProductSupportPullback_pointCycleClass_eq_zero_of_map_eq {k : ℕ} (x : M)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (M ↘ Spec (.of ℂ)) x =
      ((k + 1 : ℕ) : ℤ))
    (hxt : ρ.base x = t.point)
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ B))
      {t.complexPoint} (2 * 1 : ℕ)) :
    capProductSupportPullback R (TopCat.ofHom (map (K := ℂ) ρ)) isClosed_singleton
        (fibreDeformations ρ t) (2 * 1 : ℕ) (2 * (k + 1) : ℕ) u (pointCycleClass R x hx) = 0 := by
  set ι := (integralComponentAt x).subschemeι
  change capProductSupportPullback R _ _ _ _ _ u
    ((pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) ι))
      (isProperMap_map (K := ℂ) ι) _).hom _) = 0
  rw [← pushforward_preimageRestrictHom_capProductSupportPullback (isProperMap_map (K := ℂ) ι) _
    (fibreAmbientPointsHom_aux ι ρ rfl) isClosed_singleton _
    (hasProperNeighbourhoodDeformations_preimage_singleton (ι ≫ ρ) _),
    capProductSupportPullback_eq_zero_of_const R _ t.complexPoint _ _ _ 2 (by norm_num),
    map_zero]
  intro v
  rw [UnderlyingSpace.eq_iff_toHom_closedPoint_eq, ParameterPoint.complexPoint_toHom_closedPoint]
  have h := map_toHom_mem_closure ρ x v
  rwa [hxt, t.isClosed_point.closure_eq] at h

/-- **`ρ^* u_t ∩ cl(V) = 0` for `V` meeting no point over `t`.** -/
theorem capProductSupportPullback_pointCycleClass_eq_zero_of_notMem {k : ℕ} (x : M)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (M ↘ Spec (.of ℂ)) x =
      ((k + 1 : ℕ) : ℤ))
    (hxt : ρ.base x ≠ t.point) (hcl : IsClosed ({ρ.base x} : Set B))
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ B))
      {t.complexPoint} (2 * 1 : ℕ)) :
    capProductSupportPullback R (TopCat.ofHom (map (K := ℂ) ρ)) isClosed_singleton
        (fibreDeformations ρ t) (2 * 1 : ℕ) (2 * (k + 1) : ℕ) u (pointCycleClass R x hx) = 0 := by
  set ι := (integralComponentAt x).subschemeι
  change capProductSupportPullback R _ _ _ _ _ u
    ((pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) ι))
      (isProperMap_map (K := ℂ) ι) _).hom _) = 0
  rw [← pushforward_preimageRestrictHom_capProductSupportPullback (isProperMap_map (K := ℂ) ι) _
    (fibreAmbientPointsHom_aux ι ρ rfl) isClosed_singleton _
    (hasProperNeighbourhoodDeformations_preimage_singleton (ι ≫ ρ) _)]
  have : IsEmpty ((TopCat.ofHom (map (K := ℂ) (ι ≫ ρ))).hom ⁻¹' {t.complexPoint}) := by
    refine ⟨fun ⟨v, hv⟩ ↦ hxt ?_⟩
    have h := map_toHom_mem_closure ρ x v
    rw [hcl.closure_eq, mem_singleton_iff] at h
    have hv' : map (K := ℂ) (ι ≫ ρ) v = t.complexPoint := hv
    rw [hv', ParameterPoint.complexPoint_toHom_closedPoint] at h
    exact h.symm
  rw [(ModuleCat.subsingleton_of_isZero (isZero_borelMooreHomology_of_isEmpty R
    (ModuleCat.of R R) (TopCat.of ((TopCat.ofHom (map (K := ℂ) (ι ≫ ρ))).hom ⁻¹'
      {t.complexPoint})) _)).elim (capProductSupportPullback R _ _ _ _ _ u _) 0, map_zero]

omit [IsSmoothVariety ℂ (B ↘ Spec (.of ℂ))] in
/-- Transport along `i = i'` and back is the identity. -/
theorem congrDegree_congrDegree_self (X : TopCat.{0}) {i i' : ℤ} (h : i = i') (h' : i' = i)
    (a : borelMooreHomology R (ModuleCat.of R R) X i) :
    BorelMooreCross.congrDegree R X h' (BorelMooreCross.congrDegree R X h a) = a := by
  subst h
  rfl

omit [M.Over (Spec (.of ℂ))] [IsComplexScheme M] in
/-- Transport of the cycle of a closed subscheme along an equality of structure morphisms. -/
theorem cycleGroupStructureCongr_cycleAssociatedToClosedSubscheme {Z : Scheme.{0}}
    {q q' : M ⟶ (fieldChowSituation ℂ).S} [LocallyOfFiniteType q] [LocallyOfFiniteType q']
    (hq : q = q') (j : Z ⟶ M) [IsClosedImmersion j] (k : ℤ) :
    cycleGroupStructureCongr (fieldChowSituation ℂ) hq k
        (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) q j k) =
      cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) q' j k := by
  subst hq
  rfl

omit [IsComplexScheme M] [ρ.IsOver (Spec (.of ℂ))] in
/-- The identification `V ∩ D ≅ V_t` is a morphism over `ℂ`. -/
theorem isOver_comapFibreIso_hom {D : M.IdealSheafData} (hD : D = t.ι.ker.comap ρ)
    (V : M.IdealSheafData) : (comapFibreIso ρ t hD V).hom.IsOver (Spec (.of ℂ)) := ⟨by
  change (comapFibreIso ρ t hD V).hom ≫ ParameterPoint.fibreι (V.subschemeι ≫ ρ) t ≫
      V.subschemeι ≫ M ↘ Spec (.of ℂ) =
    (V.comap D.subschemeι).subschemeι ≫ D.subschemeι ≫ M ↘ Spec (.of ℂ)
  rw [reassoc_of% comapFibreIso_hom_fibreι ρ t hD V]⟩

attribute [local instance] isOver_comapFibreIso_hom

/-- The inclusion `κ : D(ℂ) ⟶ ρ⁻¹(t)` restricted to `(V ∩ D)(ℂ)` is the inclusion of `V_t(ℂ)`. -/
theorem map_subschemeι_comp_eq_fibreAmbientPointsHom {D : M.IdealSheafData}
    (hD : D = t.ι.ker.comap ρ)
    (κ : TopCat.of (UnderlyingSpace ℂ D.subscheme) ⟶
      TopCat.of ((TopCat.ofHom (map (K := ℂ) ρ)).hom ⁻¹' {t.complexPoint}))
    (hκι : κ ≫ subsetInclusion _ = TopCat.ofHom (map (K := ℂ) D.subschemeι))
    (V : M.IdealSheafData) :
    TopCat.ofHom (map (K := ℂ) (V.comap D.subschemeι).subschemeι) ≫ κ =
      TopCat.ofHom (map (K := ℂ) (comapFibreIso ρ t hD V).hom) ≫
        fibreAmbientPointsHom V.subschemeι ρ rfl t := by
  refine ConcreteCategory.hom_ext _ _ fun p ↦ Subtype.ext ?_
  have h1 := congrArg (fun f ↦ (f (map (K := ℂ) (V.comap D.subschemeι).subschemeι p) :
    UnderlyingSpace ℂ M)) hκι
  refine h1.trans (UnderlyingSpace.ext ?_)
  change (map (K := ℂ) D.subschemeι (map (K := ℂ) (V.comap D.subschemeι).subschemeι p)).toHom =
    (map (K := ℂ) V.subschemeι (map (K := ℂ) (ParameterPoint.fibreι (V.subschemeι ≫ ρ) t)
      (map (K := ℂ) (comapFibreIso ρ t hD V).hom p))).toHom
  simp only [toHom_map, Category.assoc, comapFibreIso_hom_fibreι ρ t hD V]

/-- **The specialization formula for a subvariety dominating `B`** (Fulton, Lemma 19.1.3): for
`D = ρ⁻¹(t)`, `κ : D(ℂ) ⟶ ρ⁻¹(t)` the inclusion and `V = closure {x}` dominating `B`,
`ρ^* u_t ∩ cl(V) = κ_* cl([V ∩ D])`. -/
theorem capProductSupportPullback_pointCycleClass_eq_of_isDominant
    (hB : SmoothOfRelativeDimension 1 (B ↘ Spec (.of ℂ))) {D : M.IdealSheafData}
    (hD : D = t.ι.ker.comap ρ)
    (κ : TopCat.of (UnderlyingSpace ℂ D.subscheme) ⟶
      TopCat.of ((TopCat.ofHom (map (K := ℂ) ρ)).hom ⁻¹' {t.complexPoint}))
    (hκ : IsProperMap κ)
    (hκι : κ ≫ subsetInclusion _ = TopCat.ofHom (map (K := ℂ) D.subschemeι))
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ B))
      {t.complexPoint} (2 * 1 : ℕ)}
    (hu : IsLocalOrientationClass (T := TopCat.of (UnderlyingSpace ℂ B)) R
      curveOrientationBasis t.complexPoint u)
    {k : ℕ} (x : M)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (M ↘ Spec (.of ℂ)) x =
      ((k + 1 : ℕ) : ℤ))
    [IsDominant ((integralComponentAt x).subschemeι ≫ ρ)] :
    capProductSupportPullback R (TopCat.ofHom (map (K := ℂ) ρ)) isClosed_singleton
        (fibreDeformations ρ t) (2 * 1 : ℕ) (2 * (k + 1) : ℕ) u (pointCycleClass R x hx) =
      BorelMooreCross.congrDegree R _ (by push_cast; ring)
        ((pushforward R (ModuleCat.of R R) κ hκ (2 * k : ℕ)).hom
          (cycleClass R k (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
            (D.subscheme ↘ Spec (.of ℂ))
            ((integralComponentAt x).comap D.subschemeι).subschemeι (k : ℤ)))) := by
  have : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  have hE1 : cycleClass R k (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
      (D.subscheme ↘ Spec (.of ℂ)) ((integralComponentAt x).comap D.subschemeι).subschemeι
        (k : ℤ)) =
      pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (map (K := ℂ) ((integralComponentAt x).comap D.subschemeι).subschemeι))
        (isProperMap_map (K := ℂ) _) (2 * k : ℕ)
        (cycleClass R k (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
          (((integralComponentAt x).comap D.subschemeι).subscheme ↘ Spec (.of ℂ)) (𝟙 _)
            (k : ℤ))) := by
    rw [← cycleClass_properPushforward,
      properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
    congr 1
  have hE2 : cycleClass R k (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
      (ParameterPoint.fibre ((integralComponentAt x).subschemeι ≫ ρ) t ↘ Spec (.of ℂ)) (𝟙 _)
        (k : ℤ)) =
      pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (map (K := ℂ) (comapFibreIso ρ t hD (integralComponentAt x)).hom))
        (isProperMap_map (K := ℂ) _) (2 * k : ℕ)
        (cycleClass R k (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
          (((integralComponentAt x).comap D.subschemeι).subscheme ↘ Spec (.of ℂ)) (𝟙 _)
            (k : ℤ))) := by
    rw [← cycleClass_properPushforward,
      properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
    congr 1
    exact cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _
      (comapFibreIso ρ t hD (integralComponentAt x)).symm (by simp) _
  have hdom := pushforward_fibreAmbientPointsHom_cycleClass_eq_capProductSupportPullback R ρ hB
    x hx t hu
  have e1 := pushforward_comp_apply' R
    (TopCat.ofHom (map (K := ℂ) ((integralComponentAt x).comap D.subschemeι).subschemeι)) κ
    (isProperMap_map (K := ℂ) _) hκ (2 * k : ℕ)
    (cycleClass R k (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
      (((integralComponentAt x).comap D.subschemeι).subscheme ↘ Spec (.of ℂ)) (𝟙 _) (k : ℤ)))
  have e2 := pushforward_comp_apply' R
    (TopCat.ofHom (map (K := ℂ) (comapFibreIso ρ t hD (integralComponentAt x)).hom))
    (fibreAmbientPointsHom (integralComponentAt x).subschemeι ρ rfl t)
    (isProperMap_map (K := ℂ) _)
    (isProperMap_fibreAmbientPointsHom (integralComponentAt x).subschemeι ρ rfl t) (2 * k : ℕ)
    (cycleClass R k (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
      (((integralComponentAt x).comap D.subschemeι).subscheme ↘ Spec (.of ℂ)) (𝟙 _) (k : ℤ)))
  have hmap := map_subschemeι_comp_eq_fibreAmbientPointsHom ρ t hD κ hκι (integralComponentAt x)
  have e3 := pushforward_apply_eq_of_hom_eq R (ModuleCat.of R R) hmap
    (hκ.comp (isProperMap_map (K := ℂ) _))
    ((isProperMap_fibreAmbientPointsHom (integralComponentAt x).subschemeι ρ rfl t).comp
      (isProperMap_map (K := ℂ) _)) (2 * k : ℕ)
    (cycleClass R k (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
      (((integralComponentAt x).comap D.subschemeι).subscheme ↘ Spec (.of ℂ)) (𝟙 _) (k : ℤ)))
  erw [hE1, ← e1, e3, e2, ← hE2, hdom]
  exact (congrDegree_congrDegree_self R _ _ _ _).symm

/-- **The specialization formula on a prime cycle** (Fulton, proof of Theorem 19.2, with
Lemma 19.1.3). Let `D = Z(s) = ρ⁻¹(t)` with `L|_D` trivial, `κ : D(ℂ) ⟶ ρ⁻¹(t)` the inclusion and
`u_t` the local orientation class of `B(ℂ)` at `t`. For a point `x` of delta-dimension `k + 1`,
`ρ^* u_t ∩ cl([x]) = κ_* cl(i^*[x])`. -/
theorem capProductSupportPullback_pointCycleClass_eq_gysin
    (hB : SmoothOfRelativeDimension 1 (B ↘ Spec (.of ℂ)))
    (hD : Stacks.Divisors.zeroScheme M L s = t.ι.ker.comap ρ)
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme M L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme M L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme M L s).subschemeι).obj L))
    (κ : TopCat.of (UnderlyingSpace ℂ (Stacks.Divisors.zeroScheme M L s).subscheme) ⟶
      TopCat.of ((TopCat.ofHom (map (K := ℂ) ρ)).hom ⁻¹' {t.complexPoint}))
    (hκ : IsProperMap κ)
    (hκι : κ ≫ subsetInclusion _ =
      TopCat.ofHom (map (K := ℂ) (Stacks.Divisors.zeroScheme M L s).subschemeι))
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ B))
      {t.complexPoint} (2 * 1 : ℕ)}
    (hu : IsLocalOrientationClass (T := TopCat.of (UnderlyingSpace ℂ B)) R
      curveOrientationBasis t.complexPoint u)
    {k : ℕ} (x : M)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (M ↘ Spec (.of ℂ)) x =
      ((k + 1 : ℕ) : ℤ)) :
    capProductSupportPullback R (TopCat.ofHom (map (K := ℂ) ρ)) isClosed_singleton
        (fibreDeformations ρ t) (2 * 1 : ℕ) (2 * (k + 1) : ℕ) u (pointCycleClass R x hx) =
      BorelMooreCross.congrDegree R _ (by push_cast; ring)
        ((pushforward R (ModuleCat.of R R) κ hκ (2 * k : ℕ)).hom
          (chowCycleClass R k (chowGroupCongr (fieldChowSituation ℂ)
            (q := (Stacks.Divisors.zeroScheme M L s).subschemeι ≫ M ↘ Spec (.of ℂ))
            (q' := (Stacks.Divisors.zeroScheme M L s).subscheme ↘ Spec (.of ℂ)) rfl (k : ℤ)
            (gysinHomomorphismOfInvertible (fieldChowSituation ℂ) (M ↘ Spec (.of ℂ)) (k : ℤ) L s
              (pointCycle (fieldChowSituation ℂ) (M ↘ Spec (.of ℂ)) ((k + 1 : ℕ) : ℤ) x
                hx))))) := by
  have hsupp : ((Stacks.Divisors.zeroScheme M L s).support : Set M) = ρ.base ⁻¹' {t.point} := by
    rw [hD, coe_support_comap_ker]
  by_cases hxD : x ∈ ((Stacks.Divisors.zeroScheme M L s).support : Set M)
  · have h0 : gysinHomomorphismOfInvertible (fieldChowSituation ℂ) (M ↘ Spec (.of ℂ)) (k : ℤ) L s
        (pointCycle (fieldChowSituation ℂ) (M ↘ Spec (.of ℂ)) ((k + 1 : ℕ) : ℤ) x hx) = 0 :=
      gysinHomomorphismOfInvertible_pointCycle_eq_zero L s htriv x hx hxD
    rw [h0, map_zero, map_zero, map_zero, map_zero]
    rw [hsupp] at hxD
    exact capProductSupportPullback_pointCycleClass_eq_zero_of_map_eq R ρ t x hx hxD u
  have hxt : ρ.base x ≠ t.point := fun h ↦ hxD (hsupp ▸ h)
  let D := Stacks.Divisors.zeroScheme M L s
  let V := integralComponentAt x
  have hint : IsIntegral V.subscheme := isIntegral_integralComponentAt x
  have hG : gysinHomomorphismOfInvertible (fieldChowSituation ℂ) (M ↘ Spec (.of ℂ)) (k : ℤ) L s
      (pointCycle (fieldChowSituation ℂ) (M ↘ Spec (.of ℂ)) ((k + 1 : ℕ) : ℤ) x hx) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
        (D.subschemeι ≫ M ↘ Spec (.of ℂ)) (V.comap D.subschemeι).subschemeι (k : ℤ)) := by
    rw [← cycleAssociatedToClosedSubscheme_integralComponentAt_eq_pointCycle]
    exact gysinHomomorphismOfInvertible_of_not_le _ _ _ L s V hint
      (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq _ _ x hx)
      fun h ↦ hxD ((le_integralComponentAt_iff_mem_support _ x).1 h)
  rw [hG]
  erw [chowGroupCongr_mk, cycleGroupStructureCongr_cycleAssociatedToClosedSubscheme,
    chowCycleClass_mk]
  rcases eq_genericPoint_or_isClosed_of_smooth hB (ρ.base x) with hgen | hcl
  · have : IsDominant ((integralComponentAt x).subschemeι ≫ ρ) := by
      have : IsIntegral B := (inferInstance : IsSmoothVariety ℂ (B ↘ Spec (.of ℂ))).toIsIntegral
      refine ⟨Dense.mono (singleton_subset_iff.2 ⟨genericPoint (integralComponentAt x).subscheme,
        ?_⟩) (dense_iff_closure_eq.2 (genericPoint_spec B).def)⟩
      change ρ.base ((integralComponentAt x).subschemeι.base
        (genericPoint (integralComponentAt x).subscheme)) = _
      rw [subschemeι_genericPoint, hgen]
    exact capProductSupportPullback_pointCycleClass_eq_of_isDominant R ρ t hB hD κ hκ hκι hu x hx
  · have hempty := isEmpty_comap_integralComponentAt_of_isClosed ρ t hsupp hxt hcl
    have hcyc : cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
        (D.subscheme ↘ Spec (.of ℂ)) (V.comap D.subschemeι).subschemeι (k : ℤ) = 0 :=
      Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦
        cycleAssociatedToClosedSubscheme_apply_eq_zero _ _ _ _ y fun ⟨ξ, _, _⟩ ↦ hempty.elim ξ.1)
    rw [hcyc, map_zero, map_zero, map_zero]
    exact capProductSupportPullback_pointCycleClass_eq_zero_of_notMem R ρ t x hx hxt hcl u

/-- **The specialization formula on cycles**: `ρ^* u_t ∩ cl(c) = κ_* cl(i^* c)` for every
`(k + 1)`-cycle `c` on `M`. -/
theorem capProductSupportPullback_cycleClass_eq_gysin
    (hB : SmoothOfRelativeDimension 1 (B ↘ Spec (.of ℂ)))
    (hD : Stacks.Divisors.zeroScheme M L s = t.ι.ker.comap ρ)
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme M L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme M L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme M L s).subschemeι).obj L))
    (κ : TopCat.of (UnderlyingSpace ℂ (Stacks.Divisors.zeroScheme M L s).subscheme) ⟶
      TopCat.of ((TopCat.ofHom (map (K := ℂ) ρ)).hom ⁻¹' {t.complexPoint}))
    (hκ : IsProperMap κ)
    (hκι : κ ≫ subsetInclusion _ =
      TopCat.ofHom (map (K := ℂ) (Stacks.Divisors.zeroScheme M L s).subschemeι))
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ B))
      {t.complexPoint} (2 * 1 : ℕ)}
    (hu : IsLocalOrientationClass (T := TopCat.of (UnderlyingSpace ℂ B)) R
      curveOrientationBasis t.complexPoint u)
    {k : ℕ} (c : CycleGroup (fieldChowSituation ℂ) (M ↘ Spec (.of ℂ)) ((k + 1 : ℕ) : ℤ)) :
    capProductSupportPullback R (TopCat.ofHom (map (K := ℂ) ρ)) isClosed_singleton
        (fibreDeformations ρ t) (2 * 1 : ℕ) (2 * (k + 1) : ℕ) u (cycleClass R (k + 1) c) =
      BorelMooreCross.congrDegree R _ (by push_cast; ring)
        ((pushforward R (ModuleCat.of R R) κ hκ (2 * k : ℕ)).hom
          (chowCycleClass R k (chowGroupCongr (fieldChowSituation ℂ)
            (q := (Stacks.Divisors.zeroScheme M L s).subschemeι ≫ M ↘ Spec (.of ℂ))
            (q' := (Stacks.Divisors.zeroScheme M L s).subscheme ↘ Spec (.of ℂ)) rfl (k : ℤ)
            (gysinHomomorphismOfInvertible (fieldChowSituation ℂ) (M ↘ Spec (.of ℂ)) (k : ℤ) L s
              c)))) := by
  rw [eq_sum_pointCycleOrZero c]
  simp only [map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  congr 1
  have hxm : relativeDimension (fieldChowSituation ℂ).dimensionFunction (M ↘ Spec (.of ℂ)) x =
      ((k + 1 : ℕ) : ℤ) :=
    (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation ℂ) _ _ c.1).mp c.2 x
      ((finite_support_cycle c).mem_toFinset.mp hx)
  rw [pointCycleOrZero, dite_eq_left hxm, cycleClass_pointCycle]
  exact capProductSupportPullback_pointCycleClass_eq_gysin R ρ L s t hB hD htriv κ hκ hκι hu x hxm

/-- **The specialization formula** (Fulton, proof of Theorem 19.2, with Lemma 19.1.3): for a
morphism `ρ : M ⟶ B` from a complex scheme to a smooth complex curve, a parameter point `t`, the
zero scheme `D = Z(s) = ρ⁻¹(t)` of a global section of an invertible module `L` with `L|_D`
trivial, and every `β ∈ A_{k+1}(M)`, `ρ^* u_t ∩ cl(β) = κ_* cl(i^* β)` in `H_{2k}(ρ⁻¹(t))`, where
`i^*` is Stacks' Gysin map of `s` (Stacks 02TO) and `κ : D(ℂ) ⟶ ρ⁻¹(t)` the inclusion. -/
theorem capProductSupportPullback_chowCycleClass_eq_gysin
    (hB : SmoothOfRelativeDimension 1 (B ↘ Spec (.of ℂ)))
    (hD : Stacks.Divisors.zeroScheme M L s = t.ι.ker.comap ρ)
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme M L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme M L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme M L s).subschemeι).obj L))
    (κ : TopCat.of (UnderlyingSpace ℂ (Stacks.Divisors.zeroScheme M L s).subscheme) ⟶
      TopCat.of ((TopCat.ofHom (map (K := ℂ) ρ)).hom ⁻¹' {t.complexPoint}))
    (hκ : IsProperMap κ)
    (hκι : κ ≫ subsetInclusion _ =
      TopCat.ofHom (map (K := ℂ) (Stacks.Divisors.zeroScheme M L s).subschemeι))
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ B))
      {t.complexPoint} (2 * 1 : ℕ)}
    (hu : IsLocalOrientationClass (T := TopCat.of (UnderlyingSpace ℂ B)) R
      curveOrientationBasis t.complexPoint u)
    {k : ℕ} (β : chowGroup (fieldChowSituation ℂ) (M ↘ Spec (.of ℂ)) ((k + 1 : ℕ) : ℤ)) :
    capProductSupportPullback R (TopCat.ofHom (map (K := ℂ) ρ)) isClosed_singleton
        (fibreDeformations ρ t) (2 * 1 : ℕ) (2 * (k + 1) : ℕ) u (chowCycleClass R (k + 1) β) =
      BorelMooreCross.congrDegree R _ (by push_cast; ring)
        ((pushforward R (ModuleCat.of R R) κ hκ (2 * k : ℕ)).hom
          (chowCycleClass R k (chowGroupCongr (fieldChowSituation ℂ)
            (q := (Stacks.Divisors.zeroScheme M L s).subschemeι ≫ M ↘ Spec (.of ℂ))
            (q' := (Stacks.Divisors.zeroScheme M L s).subscheme ↘ Spec (.of ℂ)) rfl (k : ℤ)
            ((gysinSystemOfInvertible (fieldChowSituation ℂ)).onChow (M ↘ Spec (.of ℂ)) L s
              (k : ℤ) β)))) := by
  induction β using QuotientAddGroup.induction_on with
  | H c =>
    rw [chowCycleClass_mk, gysinSystemOfInvertible_onChow_eq_gysinChowOfInvertible]
    erw [gysinChowOfInvertible_mk]
    exact capProductSupportPullback_cycleClass_eq_gysin R ρ L s t hB hD htriv κ hκ hκι hu c

/-- `MMP.Chow.capProductSupportPullback_chowCycleClass_eq_gysin`, at a complex point `p` given
as the complex point of the parameter point `t`. -/
theorem capProductSupportPullback_chowCycleClass_eq_gysin_of_eq
    (hB : SmoothOfRelativeDimension 1 (B ↘ Spec (.of ℂ)))
    (hD : Stacks.Divisors.zeroScheme M L s = t.ι.ker.comap ρ)
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme M L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme M L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme M L s).subschemeι).obj L))
    (p : UnderlyingSpace ℂ B) (hp : t.complexPoint = p)
    (hd : HasProperNeighbourhoodDeformations ((TopCat.ofHom (map (K := ℂ) ρ)).hom ⁻¹' {p}))
    (κ : TopCat.of (UnderlyingSpace ℂ (Stacks.Divisors.zeroScheme M L s).subscheme) ⟶
      TopCat.of ((TopCat.ofHom (map (K := ℂ) ρ)).hom ⁻¹' {p}))
    (hκ : IsProperMap κ)
    (hκι : κ ≫ subsetInclusion _ =
      TopCat.ofHom (map (K := ℂ) (Stacks.Divisors.zeroScheme M L s).subschemeι))
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ B))
      {p} (2 * 1 : ℕ)}
    (hu : IsLocalOrientationClass (T := TopCat.of (UnderlyingSpace ℂ B)) R
      curveOrientationBasis p u)
    {k : ℕ} (β : chowGroup (fieldChowSituation ℂ) (M ↘ Spec (.of ℂ)) ((k + 1 : ℕ) : ℤ)) :
    capProductSupportPullback R (TopCat.ofHom (map (K := ℂ) ρ)) isClosed_singleton
        hd (2 * 1 : ℕ) (2 * (k + 1) : ℕ) u (chowCycleClass R (k + 1) β) =
      BorelMooreCross.congrDegree R _ (by push_cast; ring)
        ((pushforward R (ModuleCat.of R R) κ hκ (2 * k : ℕ)).hom
          (chowCycleClass R k (chowGroupCongr (fieldChowSituation ℂ)
            (q := (Stacks.Divisors.zeroScheme M L s).subschemeι ≫ M ↘ Spec (.of ℂ))
            (q' := (Stacks.Divisors.zeroScheme M L s).subscheme ↘ Spec (.of ℂ)) rfl (k : ℤ)
            ((gysinSystemOfInvertible (fieldChowSituation ℂ)).onChow (M ↘ Spec (.of ℂ)) L s
              (k : ℤ) β)))) := by
  subst hp
  exact capProductSupportPullback_chowCycleClass_eq_gysin R ρ L s t hB hD htriv κ hκ hκι hu β

end Gysin

end Chow

end MMP
