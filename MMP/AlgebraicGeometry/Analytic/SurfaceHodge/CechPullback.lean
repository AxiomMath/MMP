module

public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.AnalyticRestriction
public import MMP.Topology.Sheaves.GodementFlasqueResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.DegreeOneComparison

/-!
# Pullback of first sheaf cohomology on Čech classes

Let `f : T' ⟶ T` be a continuous map, `A` an abelian sheaf on `T`, `B` one on `T'` and
`θ : A ⟶ f_* B`. The map `sheafHOnePullback f θ : H¹(T, A) → H¹(T', B)` is Godement pullback
followed by `H¹` of the adjoint `f⁻¹ A ⟶ B` of `θ`. In degree one a Čech cocycle `z` of `A` on a
cover `U` of `T` has a class in `H¹(T, A)`, computed in any injective resolution `J` of `A` by a
representative: a `0`-cochain `b` of `J⁰` with `db = z` and the global section of `J¹` glued from
`-d b`. For an injective resolution `J'` of `B`, a map of complexes `g : J ⟶ f_* J'` over `θ`
carries such a representative of `z`, restricted to a cover `U'` of `T'` refining `f⁻¹ U`, to a
representative of the restricted cocycle `θ(z)|_{U'}`; and `sheafHOnePullback f θ` is the map on
`H¹(Γ(-))` induced by `g`. Hence `sheafHOnePullback f θ` sends the class of `z` to the class of
`θ(z)|_{U'}`.

## Main definitions

* `MMP.Analytic.SurfaceHodge.pullCochain`: the Čech cochain on a refinement `U'` of `f⁻¹ U`
  restricted from a cochain of `f_* G` on `U`.
* `MMP.Analytic.SurfaceHodge.pullRepresentative`: the transport of a degree-one
  injective-resolution representative along `g : J ⟶ f_* J'`.

## Main results

* `MMP.Analytic.SurfaceHodge.sheafHOnePullback_sheafCohomologyOneExtEquiv_hom`:
  `sheafHOnePullback f θ` is the map induced by any `g : J ⟶ f_* J'` over `θ`.
* `MMP.Analytic.SurfaceHodge.exists_hom_injectiveResolution_pushforward`: such a `g` exists.
* `MMP.Analytic.SurfaceHodge.sheafHOnePullback_cechH1ToRightDerivedSections`:
  `sheafHOnePullback f θ` on the class of a Čech cocycle is the class of the restricted cocycle.

## References

* [Stacks, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [R. Godement, *Topologie algébrique et théorie des faisceaux*]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.CechOne

namespace MMP.Analytic.SurfaceHodge

attribute [local instance] hasExt_of_enoughInjectives
attribute [local implicit_reducible] TopCat.Sheaf

section ExtIso

/-- `extIso` is `sheafCohomologyIso` followed by `sheafCohomologyOneExtEquiv`. -/
theorem extIso_hom_app_eq (T : TopCat.{0}) (B : TopCat.Sheaf AddCommGrpCat.{0} T)
    (y : (MMP.Analytic.sheafCohomology T ((1 : ℕ) : ℤ)).obj B) :
    (MMP.JacobianLogarithm.extIso T).hom.app B y =
      (Stacks.Thickenings.sheafCohomologyOneExtEquiv T B).hom
        ((MMP.Analytic.sheafCohomologyIso T 1).hom.app B y) :=
  rfl

/-- The inverse of `extIso` on `sheafCohomologyOneExtEquiv` is the inverse of
`sheafCohomologyIso`. -/
theorem extIso_inv_app_sheafCohomologyOneExtEquiv_hom (T : TopCat.{0})
    (A : TopCat.Sheaf AddCommGrpCat.{0} T)
    (c : Stacks.Cohomology.SheafTorsor.sheafCohomologyOne T A) :
    (MMP.JacobianLogarithm.extIso T).inv.app A
        ((Stacks.Thickenings.sheafCohomologyOneExtEquiv T A).hom c) =
      (MMP.Analytic.sheafCohomologyIso T 1).inv.app A c := by
  have h2 : (MMP.Analytic.sheafCohomologyIso T 1).hom.app A
      ((MMP.Analytic.sheafCohomologyIso T 1).inv.app A c) = c :=
    (ConcreteCategory.comp_apply _ _ c).symm.trans
      ((ConcreteCategory.congr_hom ((MMP.Analytic.sheafCohomologyIso T 1).inv_hom_id_app A) c).trans
        (ConcreteCategory.id_apply c))
  have h3 := extIso_hom_app_eq T A ((MMP.Analytic.sheafCohomologyIso T 1).inv.app A c)
  rw [h2] at h3
  rw [← h3]
  exact (ConcreteCategory.comp_apply _ _ _).symm.trans
    ((ConcreteCategory.congr_hom ((MMP.JacobianLogarithm.extIso T).hom_inv_id_app A) _).trans
      (ConcreteCategory.id_apply _))

end ExtIso

section Resolutions

attribute [local instance] MMP.Analytic.globalSections_additive

variable {T T' : TopCat.{0}} (f : T' ⟶ T)

/-- `sheafHOnePullback` as a composite applied to an element. -/
theorem sheafHOnePullback_apply {A : TopCat.Sheaf AddCommGrpCat.{0} T}
    {B : TopCat.Sheaf AddCommGrpCat.{0} T'}
    (θ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj B) (x : Sheaf.H A 1) :
    sheafHOnePullback f θ x = (MMP.JacobianLogarithm.extIso T').hom.app B
      ((MMP.Analytic.sheafCohomology T' ((1 : ℕ) : ℤ)).map
        (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).homEquiv A B).symm θ)
        (MMP.Analytic.sheafCohomologyPullback f A ((1 : ℕ) : ℤ)
          ((MMP.JacobianLogarithm.extIso T).inv.app A x))) :=
  rfl

/-- **`sheafHOnePullback` on injective resolutions.** For injective resolutions `J` of `A` and
`J'` of `B` and a map of complexes `g : J ⟶ f_* J'` over `θ : A ⟶ f_* B`, `sheafHOnePullback f θ`
is, on first right-derived functors of global sections, the map induced by `g`. -/
theorem sheafHOnePullback_sheafCohomologyOneExtEquiv_hom {A : TopCat.Sheaf AddCommGrpCat.{0} T}
    {B : TopCat.Sheaf AddCommGrpCat.{0} T'}
    (θ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj B)
    (J : InjectiveResolution A) (J' : InjectiveResolution B)
    (g : J.cocomplex ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
      _).obj J'.cocomplex)
    (hg : J.ι.f 0 ≫ g.f 0 = θ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map (J'.ι.f 0))
    (c : Stacks.Cohomology.SheafTorsor.sheafCohomologyOne T A) :
    sheafHOnePullback f θ ((Stacks.Thickenings.sheafCohomologyOneExtEquiv T A).hom c) =
      (Stacks.Thickenings.sheafCohomologyOneExtEquiv T' B).hom
        ((J'.isoRightDerivedObj (MMP.Analytic.globalSections T') 1).inv
          (HomologicalComplex.homologyMap
            (((MMP.Analytic.globalSections T).mapHomologicalComplex _).map g) 1
            ((J.isoRightDerivedObj (MMP.Analytic.globalSections T) 1).hom c))) := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f
  have hθ : adj.unit.app A ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map
      ((adj.homEquiv A B).symm θ) = θ :=
    (adj.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have key := MMP.Analytic.sheafCohomologyIso_pullback f A B ((adj.homEquiv A B).symm θ) J J' g
    (by rwa [hθ]) 1
  rw [sheafHOnePullback_apply, extIso_inv_app_sheafCohomologyOneExtEquiv_hom, extIso_hom_app_eq]
  refine congrArg (Stacks.Thickenings.sheafCohomologyOneExtEquiv T' B).hom ?_
  have h2 : (MMP.Analytic.sheafCohomologyIso T 1).hom.app A
      ((MMP.Analytic.sheafCohomologyIso T 1).inv.app A c) = c :=
    (ConcreteCategory.comp_apply _ _ c).symm.trans
      ((ConcreteCategory.congr_hom ((MMP.Analytic.sheafCohomologyIso T 1).inv_hom_id_app A) c).trans
        (ConcreteCategory.id_apply c))
  refine (ConcreteCategory.congr_hom key ((MMP.Analytic.sheafCohomologyIso T 1).inv.app A c)).trans
    ?_
  rw [ConcreteCategory.comp_apply, h2]
  rfl

end Resolutions

section Cech

variable {T T' : TopCat.{0}} (f : T' ⟶ T)

/-- Two composites of restriction maps of a presheaf between the same opens agree. -/
private theorem presheaf_map_map_eq {X : TopCat.{0}} (P : TopCat.Presheaf AddCommGrpCat.{0} X)
    {V W W' Z : (Opens X)ᵒᵖ} (a : W ⟶ Z) (b : V ⟶ W) (c : W' ⟶ Z) (d : V ⟶ W')
    (x : ToType (P.obj V)) : P.map a (P.map b x) = P.map c (P.map d x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← P.map_comp, ← P.map_comp]
  rw [show b ≫ a = d ≫ c from Quiver.Hom.unop_inj (Subsingleton.elim _ _)]

/-- A restriction map of a presheaf is any composite of restriction maps. -/
private theorem presheaf_map_eq_map_map {X : TopCat.{0}} (P : TopCat.Presheaf AddCommGrpCat.{0} X)
    {V W Z : (Opens X)ᵒᵖ} (a : V ⟶ Z) (c : W ⟶ Z) (d : V ⟶ W)
    (x : ToType (P.obj V)) : P.map a x = P.map c (P.map d x) := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp]
  rw [show a = d ≫ c from Quiver.Hom.unop_inj (Subsingleton.elim _ _)]

/-- The intersections of a cover refining `f⁻¹ U` lie in the preimages of the corresponding
intersections of `U`. -/
theorem inter_le_map_inter {I I' : Type} (U : I → Opens T) (U' : I' → Opens T') (ρ : I' → I)
    (hρ : ∀ a, U' a ≤ (Opens.map f).obj (U (ρ a))) {p : ℕ} (i : Fin p → I') :
    CechCochains.inter U' i ≤ (Opens.map f).obj (CechCochains.inter U (ρ ∘ i)) := by
  intro x hx
  have hx' : x ∈ ((CechCochains.inter U' i : Opens T') : Set T') := hx
  rw [CechCochains.inter, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter] at hx'
  show f x ∈ ((CechCochains.inter U (ρ ∘ i) : Opens T) : Set T)
  rw [CechCochains.inter, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  exact fun k => hρ (i k) (hx' k)

/-- The Čech cochain on a refinement `U'` of `f⁻¹ U` obtained from a cochain of `f_* G` on `U` by
restriction. -/
noncomputable def pullCochain {I I' : Type} (U : I → Opens T) (U' : I' → Opens T') (ρ : I' → I)
    (hρ : ∀ a, U' a ≤ (Opens.map f).obj (U (ρ a))) (G : TopCat.Sheaf AddCommGrpCat.{0} T')
    (p : ℕ) (s : CechCochains.Cochain U ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj
      G).presheaf p) :
    CechCochains.Cochain U' G.presheaf p := fun i =>
  G.presheaf.map (homOfLE (inter_le_map_inter f U U' ρ hρ i)).op (s (ρ ∘ i))

/-- Restricting cochains along a refinement of `f⁻¹ U` commutes with the Čech differential. -/
theorem cechD_pullCochain {I I' : Type} (U : I → Opens T) (U' : I' → Opens T') (ρ : I' → I)
    (hρ : ∀ a, U' a ≤ (Opens.map f).obj (U (ρ a))) (G : TopCat.Sheaf AddCommGrpCat.{0} T')
    (p : ℕ) (s : CechCochains.Cochain U ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj
      G).presheaf p) :
    CechCochains.cechD U' G.presheaf p (pullCochain f U U' ρ hρ G p s) =
      pullCochain f U U' ρ hρ G (p + 1)
        (CechCochains.cechD U ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj
          G).presheaf p s) := by
  funext i
  rw [CechCochains.cechD_apply]
  simp only [pullCochain]
  rw [CechCochains.cechD_apply]
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) (map_sum _ _ _).symm
  refine Eq.trans ?_ (map_zsmul _ _ _).symm
  exact congrArg (((-1 : ℤ) ^ (j : ℕ)) • ·) (presheaf_map_map_eq G.presheaf _ _ _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- A map from an object into the cycles of the first differential of a complex of injectives
extends to a map of complexes out of any injective resolution of the object. -/
private lemma exists_hom_of_injective {C : Type*} [Category* C] [Abelian C] {Z : C}
    (I : InjectiveResolution Z) (K : CochainComplex C ℕ) (hK : ∀ n, Injective (K.X n))
    (φ : Z ⟶ K.X 0) (hφ : φ ≫ K.d 0 1 = 0) :
    ∃ g : I.cocomplex ⟶ K, I.ι.f 0 ≫ g.f 0 = φ := by
  have hg0 : I.ι.f 0 ≫ Injective.factorThru φ (I.ι.f 0) = φ := Injective.comp_factorThru _ _
  refine ⟨CochainComplex.mkHom _ _ (Injective.factorThru φ (I.ι.f 0))
    (I.exact₀.descToInjective (Injective.factorThru φ (I.ι.f 0) ≫ K.d 0 1)
      (by rw [reassoc_of% hg0, hφ]))
    (I.exact₀.comp_descToInjective _ _).symm fun n ⟨g, g', w⟩ =>
    ⟨(I.exact_succ n).descToInjective (g' ≫ K.d (n + 1) (n + 2))
      (by simp [reassoc_of% w.symm]), ((I.exact_succ n).comp_descToInjective _ _).symm⟩, ?_⟩
  rw [CochainComplex.mkHom_f_0]
  exact hg0

attribute [local instance] reflectsLimits_of_reflectsIsomorphisms in
/-- The inverse image of abelian sheaves is left exact. -/
private theorem pullback_preservesFiniteLimits :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) := by
  unfold TopCat.Sheaf.pullback
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

/-- The direct image of an injective abelian sheaf is injective. -/
private theorem injective_pushforward (I : TopCat.Sheaf AddCommGrpCat.{0} T') [Injective I] :
    Injective ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj I) := by
  have := pullback_preservesFiniteLimits f
  exact Injective.injective_of_adjoint
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f) I

set_option backward.isDefEq.respectTransparency false in
/-- A map `J ⟶ f_* J'` of injective resolutions over `θ : A ⟶ f_* B`. -/
theorem exists_hom_injectiveResolution_pushforward {A : TopCat.Sheaf AddCommGrpCat.{0} T}
    {B : TopCat.Sheaf AddCommGrpCat.{0} T'}
    (θ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj B)
    (J : InjectiveResolution A) (J' : InjectiveResolution B) :
    ∃ g : J.cocomplex ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
      _).obj J'.cocomplex,
      J.ι.f 0 ≫ g.f 0 = θ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map (J'.ι.f 0) := by
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f
  refine exists_hom_of_injective J ((P.mapHomologicalComplex _).obj J'.cocomplex)
    (fun n => by haveI := J'.injective n; exact injective_pushforward f _) _ ?_
  rw [Category.assoc, Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp,
    InjectiveResolution.ι_f_zero_comp_complex_d, Functor.map_zero, Limits.comp_zero]

end Cech

section Main

attribute [local instance] MMP.Analytic.globalSections_additive

variable {T T' : TopCat.{0}} (f : T' ⟶ T)

/-- The coboundary condition for the transported representative. -/
theorem cechD_pullRepresentative_b {A : TopCat.Sheaf AddCommGrpCat.{0} T}
    {B : TopCat.Sheaf AddCommGrpCat.{0} T'}
    (θ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj B)
    {I : Type} (U : I → Opens T) (hU : (⊤ : Opens T) = ⨆ i, U i)
    {I' : Type} (U' : I' → Opens T') (hU' : (⊤ : Opens T') = ⨆ a, U' a) (ρ : I' → I)
    (hρ : ∀ a, U' a ≤ (Opens.map f).obj (U (ρ a)))
    (J : InjectiveResolution A) (J' : InjectiveResolution B)
    (g : J.cocomplex ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
      _).obj J'.cocomplex)
    (hg : J.ι.f 0 ≫ g.f 0 = θ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map (J'.ι.f 0))
    {z : CechCochains.cocycles1 U A.presheaf} {z' : CechCochains.cocycles1 U' B.presheaf}
    (hz : ∀ (i : Fin 2 → I')
      (h : CechCochains.inter U' i ≤ (Opens.map f).obj (CechCochains.inter U (ρ ∘ i))),
      z'.val i = B.presheaf.map (homOfLE h).op
        (θ.hom.app (op (CechCochains.inter U (ρ ∘ i))) (z.val (ρ ∘ i))))
    (r : CechOneResolutionRepresentative T ⊤ U hU A J z) (i : Fin 2 → I') :
    CechCochains.cechD U' (J'.cocomplex.X 0).presheaf 0
        (pullCochain f U U' ρ hρ (J'.cocomplex.X 0) 0 (push U (g.f 0).hom 0 r.b)) i =
      (J'.ι.f 0).hom.app (op (CechCochains.inter U' i)) (z'.val i) := by
  have hi := inter_le_map_inter f U U' ρ hρ i
  have e1 : CechCochains.cechD U' (J'.cocomplex.X 0).presheaf 0
        (pullCochain f U U' ρ hρ (J'.cocomplex.X 0) 0 (push U (g.f 0).hom 0 r.b)) =
      pullCochain f U U' ρ hρ (J'.cocomplex.X 0) 1
        (push U (g.f 0).hom 1 (push U (J.ι.f 0).hom 1 z.val)) := by
    rw [cechD_pullCochain, ← push_cechD, coboundary_eq T U A ⊤ hU J r]
  refine (congrFun e1 i).trans ?_
  refine (congrArg ((J'.cocomplex.X 0).presheaf.map (homOfLE hi).op)
    (sheaf_comp_app_apply_congr T (J.ι.f 0) (g.f 0) θ
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map (J'.ι.f 0)) hg
      (CechCochains.inter U (ρ ∘ i)) (z.val (ρ ∘ i)))).trans ?_
  refine (restr_app (J'.ι.f 0).hom hi _).trans ?_
  exact congrArg ((J'.ι.f 0).hom.app (op (CechCochains.inter U' i))) (hz i hi).symm

/-- The restriction condition for the transported representative. -/
theorem restr_pullRepresentative_cycle {A : TopCat.Sheaf AddCommGrpCat.{0} T}
    {B : TopCat.Sheaf AddCommGrpCat.{0} T'}
    (θ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj B)
    {I : Type} (U : I → Opens T) (hU : (⊤ : Opens T) = ⨆ i, U i)
    {I' : Type} (U' : I' → Opens T') (hU' : (⊤ : Opens T') = ⨆ a, U' a) (ρ : I' → I)
    (hρ : ∀ a, U' a ≤ (Opens.map f).obj (U (ρ a)))
    (J : InjectiveResolution A) (J' : InjectiveResolution B)
    (g : J.cocomplex ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
      _).obj J'.cocomplex)
    (hg : J.ι.f 0 ≫ g.f 0 = θ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map (J'.ι.f 0))
    {z : CechCochains.cocycles1 U A.presheaf} {z' : CechCochains.cocycles1 U' B.presheaf}
    (hz : ∀ (i : Fin 2 → I')
      (h : CechCochains.inter U' i ≤ (Opens.map f).obj (CechCochains.inter U (ρ ∘ i))),
      z'.val i = B.presheaf.map (homOfLE h).op
        (θ.hom.app (op (CechCochains.inter U (ρ ∘ i))) (z.val (ρ ∘ i))))
    (r : CechOneResolutionRepresentative T ⊤ U hU A J z) (a : Fin 1 → I') :
    CechCochains.restr (J'.cocomplex.X 1).presheaf (inter_le_of_eq_iSup hU' a)
        ((((MMP.Analytic.globalSections T).mapHomologicalComplex _).obj
          (((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex _).obj
            J'.cocomplex)).iCycles 1
          (HomologicalComplex.cyclesMap
            (((MMP.Analytic.globalSections T).mapHomologicalComplex _).map g) 1 r.cycle)) =
      -((J'.cocomplex.d 0 1).hom.app (op (CechCochains.inter U' a))
        (pullCochain f U U' ρ hρ (J'.cocomplex.X 0) 0 (push U (g.f 0).hom 0 r.b) a)) := by
  let K := ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex _).obj
    J'.cocomplex
  have hi : ((((MMP.Analytic.globalSections T).mapHomologicalComplex _).obj K).iCycles 1)
      (HomologicalComplex.cyclesMap
        (((MMP.Analytic.globalSections T).mapHomologicalComplex _).map g) 1 r.cycle) =
      (g.f 1).hom.app (op ⊤) ((abelianResolutionSections T ⊤ J).iCycles 1 r.cycle) := by
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i]
    rfl
  have hV : CechCochains.inter U (ρ ∘ a) ≤ ⊤ := inter_le_of_eq_iSup hU (ρ ∘ a)
  have h := inter_le_map_inter f U U' ρ hρ a
  let V := CechCochains.inter U (ρ ∘ a)
  let y := (abelianResolutionSections T ⊤ J).iCycles 1 r.cycle
  refine (congrArg (CechCochains.restr (J'.cocomplex.X 1).presheaf (inter_le_of_eq_iSup hU' a))
    hi).trans ?_
  refine (presheaf_map_eq_map_map (J'.cocomplex.X 1).presheaf _ (homOfLE h).op
    ((Opens.map f).op.map (homOfLE hV).op) _).trans ?_
  refine (congrArg ((J'.cocomplex.X 1).presheaf.map (homOfLE h).op)
    (restr_app (P := (J.cocomplex.X 1).presheaf) (Q := (K.X 1).presheaf) (g.f 1).hom hV y)).trans
    ?_
  refine (congrArg (fun t => (J'.cocomplex.X 1).presheaf.map (homOfLE h).op
    ((g.f 1).hom.app (op V) t)) (restriction_eq T U A ⊤ hU J r (ρ ∘ a))).trans ?_
  refine (congrArg ((J'.cocomplex.X 1).presheaf.map (homOfLE h).op) (map_neg _ _)).trans ?_
  refine (map_neg _ _).trans ?_
  refine congrArg Neg.neg ?_
  refine (congrArg ((J'.cocomplex.X 1).presheaf.map (homOfLE h).op)
    (sheaf_comp_app_apply_congr T (J.cocomplex.d 0 1) (g.f 1) (g.f 0) (K.d 0 1)
      (g.comm 0 1).symm V (r.b (ρ ∘ a)))).trans ?_
  exact restr_app (J'.cocomplex.d 0 1).hom h _

/-- **Transport of a degree-one representative along `f`.** A representative of a Čech cocycle
`z` of `A` in an injective resolution `J`, pushed along a map of complexes `g : J ⟶ f_* J'` over
`θ : A ⟶ f_* B` and restricted to a refinement `U'` of `f⁻¹ U`, is a representative of the
restricted cocycle `z'` in `J'`. -/
noncomputable def pullRepresentative {A : TopCat.Sheaf AddCommGrpCat.{0} T}
    {B : TopCat.Sheaf AddCommGrpCat.{0} T'}
    (θ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj B)
    {I : Type} (U : I → Opens T) (hU : (⊤ : Opens T) = ⨆ i, U i)
    {I' : Type} (U' : I' → Opens T') (hU' : (⊤ : Opens T') = ⨆ a, U' a) (ρ : I' → I)
    (hρ : ∀ a, U' a ≤ (Opens.map f).obj (U (ρ a)))
    (J : InjectiveResolution A) (J' : InjectiveResolution B)
    (g : J.cocomplex ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
      _).obj J'.cocomplex)
    (hg : J.ι.f 0 ≫ g.f 0 = θ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map (J'.ι.f 0))
    {z : CechCochains.cocycles1 U A.presheaf} {z' : CechCochains.cocycles1 U' B.presheaf}
    (hz : ∀ (i : Fin 2 → I')
      (h : CechCochains.inter U' i ≤ (Opens.map f).obj (CechCochains.inter U (ρ ∘ i))),
      z'.val i = B.presheaf.map (homOfLE h).op
        (θ.hom.app (op (CechCochains.inter U (ρ ∘ i))) (z.val (ρ ∘ i))))
    (r : CechOneResolutionRepresentative T ⊤ U hU A J z) :
    CechOneResolutionRepresentative T' ⊤ U' hU' B J' z' where
  b := pullCochain f U U' ρ hρ (J'.cocomplex.X 0) 0 (push U (g.f 0).hom 0 r.b)
  cycle := HomologicalComplex.cyclesMap
    (((MMP.Analytic.globalSections T).mapHomologicalComplex _).map g) 1 r.cycle
  coboundary := cechD_pullRepresentative_b f θ U hU U' hU' ρ hρ J J' g hg hz r
  restriction := restr_pullRepresentative_cycle f θ U hU U' hU' ρ hρ J J' g hg hz r

/-- **`sheafHOnePullback` on Čech classes.** For a continuous map `f : T' ⟶ T`, a morphism
`θ : A ⟶ f_* B`, a cover `U` of `T`, a cover `U'` of `T'` refining `f⁻¹ U` through `ρ`, and a
Čech `1`-cocycle `z` of `A` on `U`, the map `sheafHOnePullback f θ` sends the class of `z` to the
class of the cocycle `θ (z_{ρ a ρ b})|_{U'_a ∩ U'_b}` of `B` on `U'`. -/
theorem sheafHOnePullback_cechH1ToRightDerivedSections
    {A : TopCat.Sheaf AddCommGrpCat.{0} T} {B : TopCat.Sheaf AddCommGrpCat.{0} T'}
    (θ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj B)
    {I : Type} (U : I → Opens T) (hU : (⊤ : Opens T) = ⨆ i, U i)
    {I' : Type} (U' : I' → Opens T') (hU' : (⊤ : Opens T') = ⨆ a, U' a) (ρ : I' → I)
    (hρ : ∀ a, U' a ≤ (Opens.map f).obj (U (ρ a)))
    (z : CechCochains.cocycles1 U A.presheaf) (z' : CechCochains.cocycles1 U' B.presheaf)
    (hz : ∀ (i : Fin 2 → I')
      (h : CechCochains.inter U' i ≤ (Opens.map f).obj (CechCochains.inter U (ρ ∘ i))),
      z'.val i = B.presheaf.map (homOfLE h).op
        (θ.hom.app (op (CechCochains.inter U (ρ ∘ i))) (z.val (ρ ∘ i)))) :
    sheafHOnePullback f θ ((Stacks.Thickenings.sheafCohomologyOneExtEquiv T A).hom
        (Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections T ⊤ U hU A
          (CechCochains.cls U A.presheaf z))) =
      (Stacks.Thickenings.sheafCohomologyOneExtEquiv T' B).hom
        (Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections T' ⊤ U' hU' B
          (CechCochains.cls U' B.presheaf z')) := by
  classical
  let J := InjectiveResolution.of A
  let J' := InjectiveResolution.of B
  obtain ⟨g, hg⟩ := exists_hom_injectiveResolution_pushforward f θ J J'
  obtain ⟨r⟩ := nonempty_cechOneResolutionRepresentative T U A ⊤ hU J z
  let r' := pullRepresentative f θ U hU U' hU' ρ hρ J J' g hg hz r
  refine (sheafHOnePullback_sheafCohomologyOneExtEquiv_hom f θ J J' g hg _).trans ?_
  refine congrArg (Stacks.Thickenings.sheafCohomologyOneExtEquiv T' B).hom ?_
  rw [cechH1ToRightDerivedSections_apply T' ⊤ U' hU' B J' z' r',
    cechH1ToRightDerivedSections_apply T ⊤ U hU A J z r]
  refine congrArg (J'.isoRightDerivedObj (MMP.Analytic.globalSections T') 1).inv ?_
  have h1 : (J.isoRightDerivedObj (MMP.Analytic.globalSections T) 1).hom
      ((J.isoRightDerivedObj (MMP.Analytic.globalSections T) 1).inv
        ((abelianResolutionSections T ⊤ J).homologyπ 1 r.cycle)) =
      (abelianResolutionSections T ⊤ J).homologyπ 1 r.cycle :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans
      ((ConcreteCategory.congr_hom (Iso.inv_hom_id _) _).trans (ConcreteCategory.id_apply _))
  refine (congrArg (HomologicalComplex.homologyMap
    (((MMP.Analytic.globalSections T).mapHomologicalComplex _).map g) 1) h1).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).symm.trans ?_
  rw [HomologicalComplex.homologyπ_naturality]
  rfl

end Main

end MMP.Analytic.SurfaceHodge
