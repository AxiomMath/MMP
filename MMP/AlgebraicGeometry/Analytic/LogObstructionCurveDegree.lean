module

import MMP.AlgebraicGeometry.SpecOverSpecSelf
public import MMP.AlgebraicGeometry.Analytic.LogObstructionChernClass
public import MMP.AlgebraicGeometry.Analytic.ComplexScheme.OfProjective
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.StacksLineBundleChern
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.Ample
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.AmpleRestrict
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ContractedDegree
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CocycleFormula

/-!
# A curve-degree consequence of a torsion logarithmic obstruction

Let `X` be a projective scheme over `ℂ` and `L` an invertible `𝒪_X`-module. If the
logarithmic obstruction `c_exp(L^an) ∈ H²(X^an, ℤ)` of the analytification of `L` vanishes in
`H²(X^an, ℤ) ⊗ ℚ`, then `deg_C L = 0` for every integral closed curve `C ⊆ X`.

The vanishing in `ℚ ⊗[ℤ] H²` says that every homomorphism `H²(X^an, ℤ) →+ ℤ` kills
`c_exp(L^an)`. Under the comparison of constant-sheaf and singular cohomology, `c_exp(L^an)` is
`± c₁(L)`, the first Chern class of the complex topological line bundle underlying `L`. Pulled
back to `C(ℂ)` it is `c₁(L|_C)`, and capping with the fundamental class of `C(ℂ)` and pushing
forward to a point evaluates it to `deg_C L`: for a line bundle with a nonzero section `s` this
is Fulton's computation of `s^* u ∩ [C]` as the class of the zero scheme of `s`, and every
line bundle on `C` is a quotient of two such.

## Main results

* `MMP.Analytic.degreeOn_eq_zero_of_tmul_picardObstruction_eq_zero`.

## Implementation notes

* The topological line bundle `L^top` underlies `L^an` through the sheaf of `𝒪_{X^an}`-modules
  of continuous sections of `L^top`, on which a holomorphic function acts through its values: a
  section of `L` over `U` gives, in the frame of a local generator at each point, the continuous
  section of its coefficients, an `𝒪_X`-linear map from `L` to the pushforward of that sheaf,
  and its adjoint is the map from `L^an`.
* A curve mapped to a point carries the trivial pullback; otherwise `C` has dimension one and
  the evaluation on its fundamental class is that of a complex curve. The comparison of the
  first Chern class of an invertible `N` on `C` with the Thom class of the line bundle
  `𝐕(N^∨)` is `MMP.Modules.topFirstChernClass_dual`; for a nonzero section `t` of `N`,
  `c₁ᵗᵒᵖ(N) ∩ [C]` is the cycle class of Stacks' zero scheme `Z(t)`
  (`MMP.Chow.cycleClass_zeroScheme_eq_firstChernClassTopCap`), whose push-forward to the point
  is the Stacks degree of `[Z(t)]_0`. Reduction to line bundles with a section is
  [Stacks, Tag 0AYM] on a reduced curve.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
* [W. Fulton, *Intersection Theory*][fulton1998], §19.1
-/

namespace MMP.FourfoldProofs.LogObstructionProof

section LogarithmFirstChern

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
  TopologicalSpace Filter _root_.Topology Bundle MMP.Analytic
  MMP.Analytic.ComplexPoints MMP.Analytic.Analytification

attribute [local instance] hasExt_of_enoughInjectives
  Stacks.Cohomology.Generators.picardGroupAddCommGroup
attribute [local implicit_reducible] TopCat.Sheaf

universe u

open MMP.SingularChain MMP.SingularCochain

section TopologicalComparison

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicTopology Metric

section CechConnecting

open CategoryTheory.Abelian

open Stacks.Cohomology.CechOne

variable {X : TopCat.{0}}

/-- The additivity of global sections, in the spelling the comparison lemmas use. -/
private abbrev sectionsAdditive :
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)).Additive :=
  inferInstanceAs (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op ⊤)).Additive

attribute [local instance] sectionsAdditive

/-- A `1`-cycle of the global sections of the chosen injective resolution, read as a map out of
the constant sheaf, is killed by the next differential. -/
private theorem sectionsCoyonedaIso_inv_iCycles_comp_d
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})
    (x : ToType (((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
      (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution F).cocomplex).cycles 1)) :
    (Stacks.Thickenings.sectionsCoyonedaIso X).inv.app _
        (((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
          (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution F).cocomplex).iCycles 1 x) ≫
      (injectiveResolution F).cocomplex.d 1 2 = 0 := by
  have h1 := ConcreteCategory.congr_hom ((Stacks.Thickenings.sectionsCoyonedaIso X).inv.naturality
    ((injectiveResolution F).cocomplex.d 1 2)) ((((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex)).iCycles 1 x)
  have h2 := ConcreteCategory.congr_hom ((((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex)).iCycles_d 1 2) x
  refine h1.symm.trans ?_
  change (Stacks.Thickenings.sectionsCoyonedaIso X).inv.app _ ((((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex)).d 1 2 ((((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex)).iCycles 1 x)) = 0
  have h3 : ConcreteCategory.hom ((((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex)).d 1 2) (ConcreteCategory.hom ((((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex)).iCycles 1) x) = 0 := h2
  rw [h3]
  exact map_zero _

/-- `sheafCohomologyOneExtEquiv` is the inverse of the degree-one comparison
`extFunctorObjIsoRightDerived`. -/
private theorem sheafCohomologyOneExtEquiv_hom_eq_extFunctorObjIsoRightDerived_inv
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :
    (Stacks.Thickenings.sheafCohomologyOneExtEquiv X F).hom =
      (ModuleSheafCohomology.extFunctorObjIsoRightDerived
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤))
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of (ULift.{0} ℤ))) (Stacks.Thickenings.sectionsCoyonedaIso X).symm 1).inv.app
        F := by
  unfold Stacks.Thickenings.sheafCohomologyOneExtEquiv
    ModuleSheafCohomology.extFunctorObjIsoRightDerived
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_inv, Iso.app_hom, NatTrans.comp_app]
  congr 1

/-- The comparison `H¹(X, F) ≃ Ext¹(ℤ_X, F)` sends the class of a `1`-cocycle of the global
sections of the chosen injective resolution of `F` to the `Ext` class of that cocycle. -/
private theorem sheafCohomologyOneExtEquiv_resolutionClass
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})
    (x : ToType (((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
      (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution F).cocomplex).cycles 1)) :
    (Stacks.Thickenings.sheafCohomologyOneExtEquiv X F).hom
        (((injectiveResolution F).isoRightDerivedObj ((sheafSections (Opens.grothendieckTopology X)
            AddCommGrpCat.{0}).obj (op ⊤)) 1).inv
          (((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
            (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
              (injectiveResolution F).cocomplex).homologyπ 1 x)) =
      (injectiveResolution F).extMk
        ((Stacks.Thickenings.sectionsCoyonedaIso X).inv.app _
          (((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
            (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
              (injectiveResolution F).cocomplex).iCycles 1 x)) 2 rfl
          (sectionsCoyonedaIso_inv_iCycles_comp_d F x) := by
  let α := (Stacks.Thickenings.sectionsCoyonedaIso X).symm
  have h := Stacks.Cohomology.ModuleComparison.extFunctorObjIsoRightDerived_succ_hom_app_comp
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤))
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ULift.{0} ℤ))) α F 0 (by simp) (by simp)
  let y := HomologicalComplex.cyclesMap
    ((NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app
      (injectiveResolution F).cocomplex) 1 x
  have hy : HomologicalComplex.cyclesMap ((NatTrans.mapHomologicalComplex α.inv
      (ComplexShape.up ℕ)).app (injectiveResolution F).cocomplex) 1 y = x := by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.cyclesMap_comp, ← NatTrans.comp_app,
      ← NatTrans.mapHomologicalComplex_comp, α.hom_inv_id, NatTrans.mapHomologicalComplex_id,
      NatTrans.id_app, HomologicalComplex.cyclesMap_id, ConcreteCategory.id_apply]
  have h' := ConcreteCategory.congr_hom h y
  set w := (ModuleSheafCohomology.extLeftHomologyData (injectiveResolution F)
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ULift.{0} ℤ))) 0).cyclesIso.hom
        (((((preadditiveCoyoneda.obj (op ((constantSheaf (Opens.grothendieckTopology X)
          AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} ℤ))))).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex).cyclesIsoSc' 0 1 2
              (by simp) (by simp)).hom y) with hw
  have h2 : ((injectiveResolution F).isoRightDerivedObj ((sheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)) 1).inv
        (((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
          (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution F).cocomplex).homologyπ 1 x) =
      (ModuleSheafCohomology.extFunctorObjIsoRightDerived
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤))
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of (ULift.{0} ℤ))) α 1).hom.app F
        (ModuleSheafCohomology.extCyclesMap (injectiveResolution F)
          ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
            (AddCommGrpCat.of (ULift.{0} ℤ))) 0 w) := by
    rw [← hy]
    exact h'.symm
  rw [h2]
  rw [sheafCohomologyOneExtEquiv_hom_eq_extFunctorObjIsoRightDerived_inv]
  refine (Iso.hom_inv_id_app_apply _ _ _).trans ?_
  refine (ModuleSheafCohomology.extCyclesMap_apply _ _ _ w).trans ?_
  congr 1
  have e1 := ConcreteCategory.congr_hom
    (ModuleSheafCohomology.extLeftHomologyData (injectiveResolution F) ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} ℤ))) 0).cyclesIso_hom_comp_i
    (((((preadditiveCoyoneda.obj (op ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} ℤ))))).mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex).cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom y)
  have e2 := ConcreteCategory.congr_hom
    ((((preadditiveCoyoneda.obj (op ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} ℤ))))).mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex).cyclesIsoSc'_hom_iCycles 0 1 2 (by simp) (by simp)) y
  have e3 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    ((NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app
      (injectiveResolution F).cocomplex) 1) x
  exact e1.trans (e2.trans e3)

/-- **The connecting map on Čech classes.** For a short exact sequence `0 ⟶ S₁ ⟶ S₂ ⟶ S₃ ⟶ 0`
and a global section `s` of `S₃`, lift `s` locally to a Čech `0`-cochain `e` of `S₂`; the
Čech `1`-cocycle `ω` of `S₁` with `f ω = δ e` has as `Ext¹` class the image of `s` under the
extension class of the sequence. -/
private theorem sheafCohomologyOneExtEquiv_cechClass_eq_comp_extClass {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)} (hS : S.ShortExact)
    (s : @Quiver.Hom (TopCat.Sheaf AddCommGrpCat.{0} X) _ (Stacks.SupportedVanishing.constZ X) S.X₃)
    {I : Type} (Ui : I → Opens X) (hUi : (⊤ : Opens X) = ⨆ i, Ui i)
    (e : CechCochains.Cochain Ui S.X₂.presheaf 0)
    (he : ∀ i : Fin 1 → I, S.g.hom.app (op (CechCochains.inter Ui i)) (e i) =
      S.X₃.presheaf.map (homOfLE le_top).op (Stacks.SupportedVanishing.homConstAddEquiv S.X₃ s))
    (ω : CechCochains.cocycles1 Ui S.X₁.presheaf)
    (hω : ∀ i : Fin 2 → I, S.f.hom.app (op (CechCochains.inter Ui i)) (ω.val i) =
      CechCochains.cechD Ui S.X₂.presheaf 0 e i) :
    (Stacks.Thickenings.sheafCohomologyOneExtEquiv X S.X₁).hom
        (cechH1ToRightDerivedSections X ⊤ Ui hUi S.X₁ (CechCochains.cls Ui S.X₁.presheaf ω)) =
      (Ext.mk₀ s).comp hS.extClass (zero_add 1) := by
  classical
  have := hS.mono_f
  have := hS.epi_g
  let J := injectiveResolution S.X₁
  let ι0 : S.X₁ ⟶ J.cocomplex.X 0 :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 S.X₁).inv ≫ J.ι.f 0
  have hι0d : ι0 ≫ J.cocomplex.d 0 1 = 0 := by
    simp only [ι0, Category.assoc, InjectiveResolution.ι_f_zero_comp_complex_d, comp_zero]
  let β : S.X₂ ⟶ J.cocomplex.X 0 := Injective.factorThru ι0 S.f
  have hβ : S.f ≫ β = ι0 := Injective.comp_factorThru _ _
  have w1 : S.f ≫ (β ≫ J.cocomplex.d 0 1) = 0 := by rw [← Category.assoc, hβ, hι0d]
  let γ : S.X₃ ⟶ J.cocomplex.X 1 := hS.gIsCokernel.desc (CokernelCofork.ofπ _ w1)
  have hγ : S.g ≫ γ = β ≫ J.cocomplex.d 0 1 := hS.gIsCokernel.fac _ WalkingParallelPair.one
  have hγd : γ ≫ J.cocomplex.d 1 2 = 0 := by
    rw [← cancel_epi S.g, reassoc_of% hγ, HomologicalComplex.d_comp_d, comp_zero, comp_zero]
  -- the Ext side
  have hmono : Mono ι0 := mono_comp _ _
  let T := ShortComplex.mk ι0 (cokernel.π ι0) (cokernel.condition _)
  have hT : T.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  let j : cokernel ι0 ⟶ J.cocomplex.X 1 := cokernel.desc _ _ hι0d
  have hj : cokernel.π ι0 ≫ j = J.cocomplex.d 0 1 := cokernel.π_desc _ _ _
  have hTJ := extClass_eq_extMk J (cokernel.π ι0) (cokernel.condition _) hT j hj
  have w2 : S.f ≫ (β ≫ cokernel.π ι0) = 0 := by
    rw [← Category.assoc, hβ, cokernel.condition]
  let τ₃ : S.X₃ ⟶ cokernel ι0 := hS.gIsCokernel.desc (CokernelCofork.ofπ _ w2)
  have hτ₃ : S.g ≫ τ₃ = β ≫ cokernel.π ι0 := hS.gIsCokernel.fac _ WalkingParallelPair.one
  have hτj : τ₃ ≫ j = γ := by
    rw [← cancel_epi S.g, reassoc_of% hτ₃, hj, hγ]
  let fST : S ⟶ T :=
    { τ₁ := 𝟙 _
      τ₂ := β
      τ₃ := τ₃
      comm₁₂ := by simpa [T] using hβ.symm
      comm₂₃ := hτ₃.symm }
  have hnat := hS.extClass_naturality hT fST
  rw [show fST.τ₁ = 𝟙 _ from rfl, Ext.comp_mk₀_id] at hnat
  have hR : (Ext.mk₀ s).comp hS.extClass (zero_add 1) =
      J.extMk (-(s ≫ γ)) 2 rfl (by
        rw [Preadditive.neg_comp, Category.assoc, neg_eq_zero, hγd, comp_zero]) := by
    rw [hnat, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, hTJ,
      InjectiveResolution.mk₀_comp_extMk]
    congr 1
    rw [Preadditive.comp_neg, Category.assoc, hτj]
  rw [hR]
  -- the Čech side: an injective-resolution representative of `ω`
  set t := Stacks.SupportedVanishing.homConstAddEquiv S.X₃ s with ht
  have hcyc : ConcreteCategory.hom ((abelianResolutionSections X ⊤ J).d 1 (1 + 1))
      (-(γ.hom.app (op ⊤) t)) = 0 := by
    rw [map_neg, neg_eq_zero, abelianResolutionSections_d_apply]
    exact sheaf_comp_app_apply_eq_zero X γ (J.cocomplex.d 1 2) hγd ⊤ t
  let r : CechOneResolutionRepresentative X ⊤ Ui hUi S.X₁ J ω :=
    { b := push Ui β.hom 0 e
      cycle := mkCycles (abelianResolutionSections X ⊤ J) 1 (-(γ.hom.app (op ⊤) t)) hcyc
      coboundary := fun i => by
        rw [← push_cechD, push_apply, ← hω i]
        exact (sheaf_comp_app_apply_congr X S.f β (𝟙 _) ι0 (by rw [hβ, Category.id_comp]) _ _)
      restriction := fun i => by
        rw [iCycles_mkCycles, map_neg, push_apply]
        congr 1
        refine (restr_app γ.hom _ t).trans ?_
        change γ.hom.app _ (S.X₃.presheaf.map (homOfLE le_top).op t) = _
        rw [← he i]
        exact sheaf_comp_app_apply_congr X S.g γ β (J.cocomplex.d 0 1) hγ _ _ }
  rw [cechH1ToRightDerivedSections_apply X ⊤ Ui hUi S.X₁ J ω r]
  refine (sheafCohomologyOneExtEquiv_resolutionClass S.X₁ r.cycle).trans ?_
  congr 1
  have e1 : (abelianResolutionSections X ⊤ J).iCycles 1 r.cycle = -(γ.hom.app (op ⊤) t) :=
    iCycles_mkCycles _ _ _ hcyc
  have e2 := Stacks.SupportedVanishing.homConstAddEquiv_comp (B := S.X₃) (B' := J.cocomplex.X 1)
    s γ
  change (Stacks.Thickenings.sectionsCoyonedaIso X).inv.app _
    ((abelianResolutionSections X ⊤ J).iCycles 1 r.cycle) = _
  rw [e1, map_neg, ← e2]
  congr 1
  have key := Iso.hom_inv_id_app_apply (Stacks.Thickenings.sectionsCoyonedaIso X) (J.cocomplex.X 1)
  exact key _

end CechConnecting

/-- `sheafCohomologyOneExtEquiv` is natural in the sheaf. -/
private theorem sheafCohomologyOneExtEquiv_naturality {Y : TopCat.{0}}
    {F G : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}} (f : F ⟶ G)
    (x : Stacks.Cohomology.SheafTorsor.sheafCohomologyOne Y F) :
    ((Stacks.Thickenings.sheafCohomologyOneExtEquiv Y F).hom x).comp (Ext.mk₀ f) (add_zero 1) =
      (Stacks.Thickenings.sheafCohomologyOneExtEquiv Y G).hom
        ((((sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{0}).obj
          (op ⊤)).rightDerived 1).map f x) := by
  haveI := sectionsAdditive (X := Y)
  rw [sheafCohomologyOneExtEquiv_hom_eq_extFunctorObjIsoRightDerived_inv,
    sheafCohomologyOneExtEquiv_hom_eq_extFunctorObjIsoRightDerived_inv]
  exact (ConcreteCategory.congr_hom ((ModuleSheafCohomology.extFunctorObjIsoRightDerived
    ((sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{0}).obj (op ⊤))
    ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ULift.{0} ℤ))) (Stacks.Thickenings.sectionsCoyonedaIso Y).symm
        1).inv.naturality f) x).symm

noncomputable section Kappa

open Stacks.SupportedVanishing

variable {M : TopCat.{0}}

/-- Evaluation of `0`-cochains at points, on presheaves. -/
private def evP : singCochainTerm Zc M 0 ⟶ (funSheaf M ℂ).obj where
  app V := AddCommGrpCat.ofHom
    { toFun := fun φ x =>
        ((fnEquiv Zc ((Opens.toTopCat M).obj V.unop) 0 φ (ContinuousMap.const _ x) : ℤ) : ℂ)
      map_zero' := by
        funext x
        erw [fnEquiv_zero]
        simp only [Pi.zero_apply, Int.cast_zero]
      map_add' := fun φ ψ => by
        funext x
        erw [fnEquiv_add]
        simp only [Pi.add_apply, Int.cast_add] }
  naturality V W i := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ => funext fun x => ?_)
    exact congrArg (fun n : ℤ => (n : ℂ))
      (fnEquiv_map Zc ((Opens.toTopCat M).map i.unop) 0 φ (ContinuousMap.const _ x))

private lemma evP_app (V : (Opens M)ᵒᵖ) (φ : (singCochainTerm Zc M 0).obj V) (x : V.unop) :
    (evP.app V φ : V.unop → ℂ) x =
      ((fnEquiv Zc ((Opens.toTopCat M).obj V.unop) 0 φ (ContinuousMap.const _ x) : ℤ) : ℂ) := rfl

private lemma fnEquiv_constCochain (Y : TopCat.{0}) (n : ℤ) (τ : Sx Y 0) :
    fnEquiv Zc Y 0 (constCochain Zc Y n) τ = n := by
  rw [fnEquiv_apply, cochainEval_constCochain]

private lemma evP_reprFn (V : Opens M) (g : Sx M 0 → ℤ) (x : V) :
    (evP.app (op V) (reprFn Zc M 0 V g) : V → ℂ) x = (g (ContinuousMap.const _ x.1) : ℂ) := by
  change ((fnEquiv Zc _ 0 ((fnEquiv Zc _ 0).symm _) _ : ℤ) : ℂ) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- Evaluation `𝒮⁰ ⟶ ℂ^M` of `0`-cochains at points. -/
private def ev0 : (KS M).X 0 ⟶ funSheaf M ℂ :=
  ((sheafificationAdjunction (Opens.grothendieckTopology M) AddCommGrpCat.{0}).homEquiv
    (singCochainTerm Zc M 0) (funSheaf M ℂ)).symm evP

private lemma unit_ev0 : unitNat (singCochainTerm Zc M 0) ≫ (ev0 (M := M)).hom = evP :=
  ((sheafificationAdjunction (Opens.grothendieckTopology M) AddCommGrpCat.{0}).homEquiv_unit
    _ _ ev0).symm.trans (Equiv.apply_symm_apply _ evP)

private lemma ev0_unit_reprFn (V : Opens M) (g : Sx M 0 → ℤ) (x : V) :
    (ev0.hom.app (op V) ((unitNat (singCochainTerm Zc M 0)).app (op V) (reprFn Zc M 0 V g)) :
      V → ℂ) x = (g (ContinuousMap.const _ x.1) : ℂ) := by
  rw [← evP_reprFn, ← unit_ev0]
  rfl

private lemma aug0_ev0 : aug0 M ≫ ev0 = constFun M := by
  let J := Opens.grothendieckTopology M
  let adj1 := constantPresheafAdj AddCommGrpCat.{0} (isTerminalTop : IsTerminal (⊤ : Opens M))
  let adj2 := sheafificationAdjunction J AddCommGrpCat.{0}
  let c : (Functor.const (Opens M)ᵒᵖ).obj (AddCommGrpCat.of ℤ) ⟶ (funSheaf M ℂ).obj :=
    (adj1.homEquiv (AddCommGrpCat.of ℤ) (funSheaf M ℂ).obj).symm (constGlobal M)
  have hc : constFun M = (adj2.homEquiv _ _).symm c :=
    congrArg (fun F => (F (AddCommGrpCat.of ℤ) (funSheaf M ℂ)).symm (constGlobal M))
      (Adjunction.comp_homEquiv adj1 adj2)
  have h1 : aug0 M ≫ ev0 = (adj2.homEquiv _ _).symm (constToCochain Zc M ≫ evP) :=
    (adj2.homEquiv_naturality_left_symm (Y := funSheaf M ℂ) (constToCochain Zc M) (evP (M := M))).symm
  have h2 : constToCochain Zc M ≫ evP = c := by
    refine NatTrans.ext (funext fun U => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun n =>
      funext fun x => ?_))
    have e1 : ∀ m : ℤ, (c.app U m : U.unop → ℂ) x = (m : ℂ) := fun m => rfl
    rw [NatTrans.comp_app, ConcreteCategory.comp_apply]
    erw [evP_app]
    refine Eq.trans ?_ (e1 n).symm
    exact congrArg (fun m : ℤ => (m : ℂ)) (fnEquiv_constCochain _ n _)
  rw [hc, h1, h2]

variable (hM : LocallyContractibleSpace M)

private lemma aug0_ev0_π : aug0 M ≫ ev0 ≫ cokernel.π (constFun M) = 0 := by
  rw [← Category.assoc, aug0_ev0, cokernel.condition]

/-- The map `Z¹ ⟶ ℂ^M / ℤ_M` induced by evaluation. -/
private def kappa : Z1 M ⟶ quotSheaf M :=
  (S1_shortExact hM).gIsCokernel.desc (CokernelCofork.ofπ _ (aug0_ev0_π (M := M)))

private lemma g1_kappa : g1 M ≫ kappa hM = ev0 ≫ cokernel.π (constFun M) :=
  (S1_shortExact hM).gIsCokernel.fac _ WalkingParallelPair.one

private lemma extClass_S1 : (S1_shortExact hM).extClass =
    (Ext.mk₀ (kappa hM)).comp (quotSeq_shortExact M).extClass (zero_add 1) := by
  let f : S1 M ⟶ ShortComplex.mk (constFun M) (cokernel.π (constFun M)) (cokernel.condition _) :=
    { τ₁ := 𝟙 _
      τ₂ := ev0
      τ₃ := kappa hM
      comm₁₂ := (Category.id_comp _).trans aug0_ev0.symm
      comm₂₃ := (g1_kappa hM).symm }
  have h := (S1_shortExact hM).extClass_naturality (quotSeq_shortExact M) f
  rwa [show f.τ₁ = 𝟙 _ from rfl, Ext.comp_mk₀_id] at h

private lemma Psi_eq_comp (z : Sx M 2 → ℤ) (hz : cob 2 z = 0) :
    Psi hM z hz = (((Ext.mk₀ (zhat z hz)).comp (S2_shortExact hM).extClass (zero_add 1)).comp
      (Ext.mk₀ (kappa hM)) (add_zero 1)).comp (quotSeq_shortExact M).extClass
        (show 1 + 1 = 2 from rfl) := by
  rw [Psi, extClass_S1, Ext.comp_assoc_of_second_deg_zero]

end Kappa

noncomputable section Kappa2

open Stacks.SupportedVanishing

variable {M : TopCat.{0}}

/-- The local section of `𝒮^p` over `V` of a singular cochain. -/
private abbrev locS (p : ℕ) (V : Opens M) (g : Sx M p → ℤ) : ToType (((KS M).X p).obj.obj (op V)) :=
  (unitNat (singCochainTerm Zc M p)).app (op V) (reprFn Zc M p V g)

private lemma locS_res (p : ℕ) {V W : Opens M} (h : W ≤ V) (g : Sx M p → ℤ) :
    ((KS M).X p).obj.map (homOfLE h).op (locS p V g) = locS p W g := by
  refine (ConcreteCategory.congr_hom ((unitNat (singCochainTerm Zc M p)).naturality
    (homOfLE h).op) _).symm.trans ?_
  exact congrArg _ (reprFn_res Zc M p h g)

private lemma locS_sub (p : ℕ) (V : Opens M) (g g' : Sx M p → ℤ) :
    locS p V (g - g') = locS p V g - locS p V g' := by
  simp only [locS]
  erw [reprFn_sub]
  exact map_sub _ _ _

private lemma locS_zero (p : ℕ) (V : Opens M) : locS (M := M) p V 0 = 0 := by
  simp only [locS]
  erw [reprFn_zero]
  exact map_zero _

private lemma locS_congr (p : ℕ) (V : Opens M) {g g' : Sx M p → ℤ}
    (h : ∀ t : Sx M p, Set.range t ⊆ V → g t = g' t) : locS p V g = locS p V g' := by
  simp only [locS]
  rw [(reprFn_eq Zc M p V g g').2 h]

private lemma KS_d_eq (p : ℕ) : (KS M).d p (p + 1) =
    (presheafToSheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0}).map
      (singCochainTermD Zc M p) :=
  congrArg (presheafToSheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0}).map
    (show (singCochainPresheafComplex Zc M).d p (p + 1) = singCochainTermD Zc M p from
      CochainComplex.of_d _ _ _)

private lemma KS_d_locS (p : ℕ) (V : Opens M) (g : Sx M p → ℤ) :
    ((KS M).d p (p + 1)).hom.app (op V) (locS p V g) = locS (p + 1) V (cob p g) := by
  rw [KS_d_eq]
  have h := (sheafificationAdjunction (Opens.grothendieckTopology M) AddCommGrpCat.{0}).unit.naturality
    (singCochainTermD Zc M p)
  have h2 := ConcreteCategory.congr_hom (congrArg (fun t => t.app (op V)) h) (reprFn Zc M p V g)
  refine h2.symm.trans ?_
  exact congrArg _ (reprFn_d Zc M p V g)

private lemma app_injective {F G : Sh M} (f : F ⟶ G) [Mono f] (U : Opens M) :
    Function.Injective (f.hom.app (op U)) := by
  have : Mono f.hom := (sheafToPresheaf _ _).map_mono f
  exact (AddCommGrpCat.mono_iff_injective _).1 inferInstance

private lemma comp_app_apply {F G H : Sh M} (f : F ⟶ G) (g : G ⟶ H) (U : Opens M)
    (x : ToType (F.obj.obj (op U))) :
    (f ≫ g).hom.app (op U) x = g.hom.app (op U) (f.hom.app (op U) x) := rfl

private lemma hom_app_map {F G : Sh M} (f : F ⟶ G) {V W : Opens M} (h : W ≤ V)
    (x : ToType (F.obj.obj (op V))) :
    f.hom.app (op W) (F.obj.map (homOfLE h).op x) = G.obj.map (homOfLE h).op (f.hom.app (op V) x) :=
  ConcreteCategory.congr_hom (f.hom.naturality (homOfLE h).op) x

private lemma cechD_zero_apply {F : TopCat.Presheaf AddCommGrpCat.{0} M} {I : Type}
    (Ui : I → Opens M) (e : CechCochains.Cochain Ui F 0) (i : Fin 2 → I) :
    CechCochains.cechD Ui F 0 e i =
      CechCochains.restr F (CechCochains.inter_le_omit Ui i 0) (e (i ∘ (0 : Fin 2).succAbove)) -
      CechCochains.restr F (CechCochains.inter_le_omit Ui i 1) (e (i ∘ (1 : Fin 2).succAbove)) := by
  change ∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) • CechCochains.restr _ _ (e (i ∘ j.succAbove)) = _
  rw [Fin.sum_univ_two]
  simp [sub_eq_add_neg]

variable (hM : LocallyContractibleSpace M)

/-- **The class of a singular `2`-cocycle is the Čech class of its integer primitives.** -/
private theorem Psi_eq_quotExtClass [MetrizableSpace M] (z : Sx M 2 → ℤ) (hz : cob 2 z = 0)
    {I : Type} (Ui : I → Opens M) (hUi : (⊤ : Opens M) = ⨆ i, Ui i) (w : I → Sx M 1 → ℤ)
    (hw : ∀ i (σ : Sx M 2), Set.range σ ⊆ Ui i → z σ = coboundary ℤ 1 (w i) σ)
    (c : CechCochains.cocycles1 Ui (quotSheaf M).obj) (hc : IsKappaCocycle Ui w c) :
    Psi hM z hz = quotExtClass M Ui hUi c := by
  classical
  have hwc : ∀ i (V : Opens M), V ≤ Ui i → ∀ σ : Sx M 2, Set.range σ ⊆ V → cob 1 (w i) σ = z σ :=
    fun i V hV σ hσ => by rw [cob_eq_coboundary, hw i σ (hσ.trans hV)]
  have hinter : ∀ {p : ℕ} (i : Fin p → I) (k : Fin p), CechCochains.inter Ui i ≤ Ui (i k) :=
    fun i k => iInf_le (fun k => Ui (i k)) k
  -- the local lifts of the class of `z`
  let e : CechCochains.Cochain Ui ((KS M).X 1).obj 0 := fun i =>
    locS 1 (CechCochains.inter Ui i) (w (i 0))
  have he : ∀ i : Fin 1 → I, (g2 M).hom.app (op (CechCochains.inter Ui i)) (e i) =
      (Z2 M).obj.map (homOfLE le_top).op (homConstAddEquiv (Z2 M) (zhat z hz)) := by
    intro i
    apply app_injective (kernel.ι ((KS M).d 2 3))
    have h1 : (kernel.ι ((KS M).d 2 3)).hom.app (op ⊤) (homConstAddEquiv (Z2 M) (zhat z hz)) =
        locS 2 ⊤ z := by
      rw [← homConstAddEquiv_comp, zhat_ι, homConstAddEquiv_epsH]
      rfl
    rw [← comp_app_apply, g2_ι, KS_d_locS]
    erw [hom_app_map, h1, locS_res]
    exact locS_congr 2 _ (hwc (i 0) _ (hinter i 0))
  have hx : ∀ i : Fin 2 → I, CechCochains.cechD Ui _ 0 e i =
      locS 1 (CechCochains.inter Ui i) (w (i 1) - w (i 0)) := by
    intro i
    rw [cechD_zero_apply, locS_sub]
    simp only [CechCochains.restr, e]
    erw [locS_res, locS_res]
    rfl
  have hgx : ∀ i : Fin 2 → I,
      (g2 M).hom.app (op (CechCochains.inter Ui i)) (CechCochains.cechD Ui _ 0 e i) = 0 := by
    intro i
    apply app_injective (kernel.ι ((KS M).d 2 3))
    rw [← comp_app_apply, g2_ι, hx, map_zero, KS_d_locS, ← locS_zero 2 (CechCochains.inter Ui i)]
    refine locS_congr 2 _ fun t ht => ?_
    rw [cob_sub (A := Zc), Pi.sub_apply, hwc (i 1) _ (hinter i 1) t ht, hwc (i 0) _ (hinter i 0) t ht,
      sub_self]
    rfl
  have hex : ∀ i : Fin 2 → I, ∃ t, (kernel.ι ((KS M).d 1 2)).hom.app (op (CechCochains.inter Ui i)) t =
      CechCochains.cechD Ui _ 0 e i :=
    fun i => TopCat.Sheaf.sections_exact_of_left_exact (S := S2 M) (S2_shortExact hM).exact
      (S2_shortExact hM).mono_f _ (hgx i)
  choose ω' hω' using hex
  have hωcoc : ω' ∈ CechCochains.cocycles1 Ui (Z1 M).obj := by
    refine (CechCochains.mem_cocycles1_iff _ _ _).2 ?_
    funext i
    apply app_injective (kernel.ι ((KS M).d 1 2))
    have hpush : Stacks.Cohomology.CechOne.push Ui (kernel.ι ((KS M).d 1 2)).hom 1 ω' =
        CechCochains.cechD Ui _ 0 e :=
      funext fun i => (Stacks.Cohomology.CechOne.push_apply (P := (Z1 M).obj) Ui _ 1 ω' i).trans
        (hω' i)
    have h := congrArg (fun f => f i)
      (Stacks.Cohomology.CechOne.push_cechD Ui (kernel.ι ((KS M).d 1 2)).hom 1 ω')
    simp only [Stacks.Cohomology.CechOne.push_apply] at h
    erw [h, hpush, CechCochains.cechD_cechD]
    exact (map_zero _).symm
  let ω : CechCochains.cocycles1 Ui (Z1 M).obj := ⟨ω', hωcoc⟩
  have hκω : ∀ i : Fin 2 → I,
      c.1 i = (kappa hM).hom.app (op (CechCochains.inter Ui i)) (ω.1 i) := by
    intro i
    refine TopCat.Presheaf.section_ext (quotSheaf M) _ _ _ fun y hy => ?_
    obtain ⟨V, hV, hyV, a, ha_edge, ha_c⟩ := hc i y hy
    rw [← TopCat.Presheaf.germ_res_apply (quotSheaf M).obj (homOfLE hV) y hyV,
      ← TopCat.Presheaf.germ_res_apply (quotSheaf M).obj (homOfLE hV) y hyV]
    congr 1
    let a' : Sx M 0 → ℤ := fun σ => if h : σ (stdSimplex.vertex 0) ∈ V then a ⟨_, h⟩ else 0
    have ha' : ∀ (σ : Sx M 0) (p : V), σ (stdSimplex.vertex 0) = p.1 → a' σ = a p := by
      intro σ p hp
      simp only [a']
      rw [dif_pos (by rw [hp]; exact p.2)]
      exact congrArg a (Subtype.ext hp)
    have hω_V : (Z1 M).obj.map (homOfLE hV).op (ω' i) = (g1 M).hom.app (op V) (locS 0 V a') := by
      apply app_injective (kernel.ι ((KS M).d 1 2))
      erw [hom_app_map, hω', hx, locS_res]
      rw [← comp_app_apply, g1_ι, KS_d_locS]
      refine locS_congr 1 V fun τ hτ => ?_
      rw [Pi.sub_apply, ha_edge τ hτ]
      show _ = ∑ k : Fin 2, ((-1 : ℤ) ^ (k : ℕ)) • a' (τ.comp (face 0 k))
      rw [Fin.sum_univ_two, ha' (τ.comp (face 0 0)) ⟨_, hτ ⟨stdSimplex.vertex 1, rfl⟩⟩
        (by rw [ContinuousMap.comp_apply, face00_vertex]),
        ha' (τ.comp (face 0 1)) ⟨_, hτ ⟨stdSimplex.vertex 0, rfl⟩⟩
        (by rw [ContinuousMap.comp_apply, face01_vertex])]
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
      rw [sub_eq_add_neg]
    erw [ha_c, ← hom_app_map (kappa hM)]
    erw [hω_V]
    rw [← comp_app_apply, g1_kappa, comp_app_apply]
    congr 1
    funext y
    erw [ev0_unit_reprFn]
    exact congrArg (fun m : ℤ => (m : ℂ)) (ha' _ y rfl).symm
  have hcrux : (Ext.mk₀ (zhat z hz)).comp (S2_shortExact hM).extClass (zero_add 1) =
      (Stacks.Thickenings.sheafCohomologyOneExtEquiv M (Z1 M)).hom
        (Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections M ⊤ Ui hUi (Z1 M)
          (CechCochains.cls Ui (Z1 M).obj ω)) :=
    (sheafCohomologyOneExtEquiv_cechClass_eq_comp_extClass (S2_shortExact hM) (zhat z hz) Ui hUi e he ω hω').symm
  have hn := sheafCohomologyOneExtEquiv_naturality (kappa hM)
    (Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections M ⊤ Ui hUi (Z1 M)
      (CechCochains.cls Ui (Z1 M).obj ω))
  have hc2 := Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections_naturality M ⊤ Ui hUi
    (kappa hM) ω c hκω
  rw [Psi_eq_comp, hcrux]
  erw [hn, hc2]
  rfl

end Kappa2

end TopologicalComparison

section TopologicalSide

open CategoryTheory.Abelian MMP.SingularChain MMP.SingularCochain

private theorem topological_side :
    ∃ φ : ∀ (M : TopCat.{0}), MetrizableSpace M → LocallyContractibleSpace M →
        (Sheaf.H.{0} (ZSh M) 2 ≃+ relativeSingularCohomology ℤ (.of ℤ ℤ) M ∅ 2),
      ∃ ε₀ : ℤˣ, ∀ (M : TopCat.{0}) (hM : MetrizableSpace M) (hM' : LocallyContractibleSpace M)
        (z : Simplex M 2 → ℤ) (hz : z ∈ relCocycles ℤ (∅ : Set M) 2)
        {I : Type} (Ui : I → Opens M) (hUi : (⊤ : Opens M) = ⨆ i, Ui i)
        (w : I → Simplex M 1 → ℤ)
        (_ : ∀ i (σ : Simplex M 2), Set.range σ ⊆ Ui i → z σ = coboundary ℤ 1 (w i) σ)
        (c : CechCochains.cocycles1 Ui (quotSheaf M).obj), IsKappaCocycle Ui w c →
        (φ M hM hM').symm ((relativeSingularCohomologyEquiv ℤ (∅ : Set M) 2).symm
            (Submodule.Quotient.mk ⟨z, hz⟩)) =
          (ε₀ : ℤ) • quotExtClass M Ui hUi c := by
  refine ⟨fun M hM hM' => @Phi M hM hM', 1, fun M hM hM' z hz I Ui hUi w hw c hc => ?_⟩
  rw [@Phi_symm_mk M hM hM' ⟨z, hz⟩, Units.val_one, one_smul]
  exact @Psi_eq_quotExtClass M hM' hM z _ I Ui hUi w hw c hc

end TopologicalSide

/-- The analytic space of a projective scheme over `ℂ` is metrizable and locally contractible. -/
private theorem metrizable_locallyContractible_analyticSpace {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjectiveMorphism sX) :
    MetrizableSpace (analyticSpace sX) ∧ LocallyContractibleSpace (analyticSpace sX) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : IsComplexScheme X := MMP.Analytic.isComplexScheme_of_isProjective X hX.isProjective
  obtain ⟨hb, N, F, hF⟩ := UnderlyingSpace.hasBasis_contractible_and_exists_isClosedEmbedding X
  let h : analyticSpace sX ≃ₜ UnderlyingSpace ℂ X := homeomorphUnderlyingSpace (X := X)
  have hbasis : ∀ p : analyticSpace sX, (𝓝 p).HasBasis
      (fun V : Set (analyticSpace sX) ↦ IsOpen V ∧ p ∈ V ∧ ContractibleSpace V) id := fun p ↦
    ⟨fun t ↦ ⟨fun ht ↦ by
      have : h.symm ⁻¹' t ∈ 𝓝 (h p) :=
        h.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using ht)
      obtain ⟨V, ⟨hVo, hpV, hV⟩, hVt⟩ := (hb (h p)).mem_iff.1 this
      refine ⟨h.symm '' V, ⟨h.symm.isOpenMap V hVo, ⟨h p, hpV, by simp⟩,
        (h.symm.image V).symm.contractibleSpace⟩, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact hVt hy, fun ⟨W, ⟨hWo, hpW, _⟩, hWt⟩ ↦ Filter.mem_of_superset (hWo.mem_nhds hpW) hWt⟩⟩
  refine ⟨(hF.comp h.isClosedEmbedding).isEmbedding.metrizableSpace, ?_⟩
  haveI : StronglyLocallyContractibleSpace (analyticSpace sX) :=
    ⟨fun p ↦ (hbasis p).to_hasBasis (fun V ⟨hVo, hpV, hV⟩ ↦ ⟨V, ⟨hVo.mem_nhds hpV, hV⟩, le_rfl⟩)
      (fun V ⟨hV, _⟩ ↦ (hbasis p).mem_iff.1 hV)⟩
  exact StronglyLocallyContractibleSpace.locallyContractible

private theorem analytic_geometry :
    ∀ {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjectiveMorphism sX),
        haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX
        let J := Opens.grothendieckTopology (space sX)
        let O : Sheaf J AddCommGrpCat.{0} :=
          (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX)
        let Ou : Sheaf J AddCommGrpCat.{0} :=
          Stacks.Cohomology.Generators.unitsSheaf (analytification sX)
        let ZA : Sheaf J AddCommGrpCat.{0} :=
          (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
        ∀ (ι : ZA ⟶ O) (e : O ⟶ Ou) (w : ι ≫ e = 0) (hS : (ShortComplex.mk ι e w).ShortExact),
          (∀ (W : Opens (space sX)) (n : ℤ),
            (show (structureSheaf sX).obj.obj (op W) from ι.hom.app (op W)
              ((toSheafify J ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op W) n)) = n) →
          (∀ (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W)
            (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) (f : (Fin c.1.n → ℂ) → ℂ)
            (g g' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
            (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = f →
            (g' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
              (fun z => Complex.exp (2 * Real.pi * Complex.I * f z)) →
            s.1 x c = Chart.StalkRing.mk c.1 _ g →
            ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf sX).obj.obj (op W))ˣ) :
              (structureSheaf sX).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ g') →
          ∀ (L : SheafOfModules (ringCatSheaf sX))
            (hL : Stacks.SheafOfModules.IsInvertible (analytification sX).sheaf.obj
              (ringCatSheaf sX).property L)
            (E : space sX → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
            [TopologicalSpace (TotalSpace ℂ E)] [∀ x, TopologicalSpace (E x)]
            [FiberBundle ℂ E] [VectorBundle ℂ ℂ E]
            (val : ∀ V : Opens (space sX), L.val.obj (op V) → ∀ x : V, E x),
            (∀ (V : Opens (space sX)) (t : L.val.obj (op V)), Continuous fun x : V ↦ (⟨x.1, val V t x⟩ : TotalSpace ℂ E)) →
            (∀ (V : Opens (space sX)) (t t' : L.val.obj (op V)), val V (t + t') = val V t + val V t') →
            (∀ (V W : Opens (space sX)) (h : W ≤ V) (t : L.val.obj (op V)) (x : W),
              val W (L.val.map (homOfLE h).op t) x = val V t ⟨x.1, h x.2⟩) →
            (∀ (V : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op V))
              (t : L.val.obj (op V)) (x : V)
              (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U})
              (g : holGerms (c.1.coords ⟨x.1, c.2⟩)),
              s.1 x c = Chart.StalkRing.mk c.1 _ g →
              val V ((show (ringCatSheaf sX).obj.obj (op V) from s) • t) x = Germ.value (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) • val V t x) →
            (∀ x : space sX, ∃ (V : Opens (space sX)) (t : L.val.obj (op V)) (hx : x ∈ V),
              val V t ⟨x, hx⟩ ≠ 0) →
            ∀ (lam : Ou ⟶ quotSheaf (space sX)),
              e ≫ lam = valueMap sX ≫ cokernel.π (constFun (space sX)) →
            ∃ (I : Type) (Ui : I → Opens (space sX)) (hUi : (⊤ : Opens (space sX)) = ⨆ i, Ui i)
              (sec : ∀ i, (Stacks.Cohomology.Generators.generatorTorsorOfInvertible
                (analytification sX) L hL).toTorsor.F.obj (Ui i))
              (g : CechCochains.cocycles1 Ui (Stacks.Cohomology.Generators.unitsSheaf
                (analytification sX)).obj),
              Stacks.Cohomology.SheafTorsor.IsTransitionCocycle
                (Stacks.Cohomology.Generators.generatorTorsorOfInvertible
                  (analytification sX) L hL).toTorsor Ui sec g ∧
              ∃ (h : CechCochains.Cochain Ui (quotSheaf (space sX)).obj 0)
                (c : CechCochains.cocycles1 Ui (quotSheaf (space sX)).obj),
                (∀ i, c.1 i = CechCochains.cechD Ui (quotSheaf (space sX)).obj 0 h i -
                  lam.hom.app (op (CechCochains.inter Ui i)) (g.1 i)) ∧
              ∃ wc : I → MMP.SingularChain.Simplex (space sX) 1 → ℤ,
                (∀ i (σ : MMP.SingularChain.Simplex (space sX) 2),
                  Set.range σ ⊆ Ui i →
                    ComplexLineBundle.obstructionCocycle E σ =
                      MMP.SingularCochain.coboundary ℤ 1 (wc i) σ) ∧
                IsKappaCocycle Ui wc c := by
  intro X sX hX J O Ou ZA ι e w hS hι he L hL E _ _ _ _ _ _ val h1 h2 h3 h4 h5 lam hlam
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX
  haveI : Epi e := hS.epi_g
  classical
  let T := Stacks.Cohomology.Generators.generatorTorsorOfInvertible (analytification sX) L hL
  have hgen := fun x => exists_generator_ne_zero sX L hL E val h3 h4 h5 x
  choose U0 hU0 s0 hs0 using hgen
  let f0 : ∀ x, ∀ y : U0 x, E y := fun x y => val (U0 x) (T.sectionsEquiv (U0 x) (s0 x)).val y
  have hlog := fun x => exists_frameCoord_log (trivializationAt ℂ E x) (U0 x) (f0 x) (h1 _ _)
    (hU0 x) (FiberBundle.mem_baseSet_trivializationAt ℂ E x) (hs0 x)
  choose U1 hxU1 hU10 hU1e Lg hLgc hLg using hlog
  have hUi : (⊤ : Opens (space sX)) = ⨆ x, U1 x := by
    ext y
    simp only [Opens.coe_top, Opens.coe_iSup, Set.mem_univ, Set.mem_iUnion, true_iff]
    exact ⟨y, hxU1 y⟩
  let sec : ∀ x, T.F.obj (U1 x) := fun x => T.F.res (hU10 x) (s0 x)
  let g := Stacks.Cohomology.SheafTorsor.torsorTransitionCocycle T.toTorsor U1 sec
  have hg := Stacks.Cohomology.SheafTorsor.torsorTransitionCocycle_spec T.toTorsor U1 sec
  have hw := fun x => exists_obstructionCocycle_eq_coboundary (E := E) (trivializationAt ℂ E x)
  choose wc hwc1 hwc2 using hw
  let hfun : ∀ x, space sX → ℂ := fun x z =>
    (Lg x z - Complex.log (ComplexLineBundle.vertexCoord (E := E) (trivializationAt ℂ E x) z)) /
      (2 * Real.pi * Complex.I)
  let h : CechCochains.Cochain U1 (quotSheaf (space sX)).obj 0 := fun i =>
    (cokernel.π (constFun (space sX))).hom.app (op (CechCochains.inter U1 i))
      (show CechCochains.inter U1 i → ℂ from fun z => hfun (i 0) z)
  let lamg := Stacks.Cohomology.CechOne.push U1 lam.hom 1 g.1
  have hlamg : CechCochains.cechD U1 (quotSheaf (space sX)).obj 1 lamg = 0 :=
    Stacks.Cohomology.CechOne.cechD_push U1 lam.hom 1 g.1 g.2
  let c : CechCochains.cocycles1 U1 (quotSheaf (space sX)).obj :=
    ⟨CechCochains.cechD U1 (quotSheaf (space sX)).obj 0 h - lamg, by
      rw [CechCochains.mem_cocycles1_iff, map_sub, CechCochains.cechD_cechD, hlamg, sub_zero]⟩
  refine ⟨space sX, U1, hUi, sec, g, hg, h, c, fun i => rfl, wc,
    fun x σ hσ => hwc2 x σ (hσ.trans (hU1e x)), ?_⟩
  intro i y hy
  have hi0 : CechCochains.inter U1 i ≤ U1 (i 0) := iInf_le (fun k => U1 (i k)) 0
  have hi1 : CechCochains.inter U1 i ≤ U1 (i 1) := iInf_le (fun k => U1 (i k)) 1
  obtain ⟨V, hVW, hyV, φ, hφc, hφexp, hφlam⟩ := exists_local_log_lam sX e he lam hlam (g.1 i) hy
  -- the generators on the overlap are the frames `f0`
  have hgen : ∀ (k : Fin 2) (z : CechCochains.inter U1 i), val (CechCochains.inter U1 i)
      (T.sectionsEquiv _ (T.F.res (iInf_le (fun k => U1 (i k)) k) (sec (i k)))).val z =
        f0 (i k) ⟨z.1, hU10 _ (iInf_le (fun k => U1 (i k)) k z.2)⟩ := by
    intro k z
    rw [T.sectionsEquiv_restrict, T.sectionsEquiv_restrict]
    exact (h3 _ _ _ _ z).trans (h3 _ _ _ _ _)
  have hfr : ∀ z (hz : z ∈ V), f0 (i 1) ⟨z, hU10 _ (hi1 (hVW hz))⟩ =
      Complex.exp (2 * Real.pi * Complex.I * φ z) • f0 (i 0) ⟨z, hU10 _ (hi0 (hVW hz))⟩ := by
    intro z hz
    have hact := val_act_eq sX L hL E val h4 _ _ (g.1 i) (hg i) ⟨z, hVW hz⟩
    have e1 := hgen 1 ⟨z, hVW hz⟩
    have e0 := hgen 0 ⟨z, hVW hz⟩
    refine e1.symm.trans (hact.trans ?_)
    rw [← hφexp z hz]
    exact congrArg _ e0
  have hLi : ∀ x, ∀ y ∈ U1 x, Complex.exp (Lg x y) =
      frameCoord (trivializationAt ℂ E x) (U1 x) (fun z => f0 x ⟨z.1, hU10 x z.2⟩) y := by
    intro x y hy
    rw [hLg x y hy, frameCoord_of_mem _ _ _ (hU10 x hy), frameCoord_of_mem _ _ _ hy]
  obtain ⟨a, ha_edge, ha_val⟩ := exists_int_primitive (ei := trivializationAt ℂ E (i 0))
    (ej := trivializationAt ℂ E (i 1)) (Ui := U1 (i 0)) (Uj := U1 (i 1))
    (fun z => f0 (i 0) ⟨z.1, hU10 _ z.2⟩) (fun z => f0 (i 1) ⟨z.1, hU10 _ z.2⟩)
    (hLi (i 0)) (hLi (i 1)) V (hVW.trans hi0) (hVW.trans hi1)
    (fun z hz => hU1e _ (hi0 (hVW hz))) (fun z hz => hU1e _ (hi1 (hVW hz)))
    ((hLgc _).mono fun z hz => hi0 (hVW hz)) ((hLgc _).mono fun z hz => hi1 (hVW hz)) hφc
    (fun z hz => hfr z hz) (hwc1 (i 0)) (hwc1 (i 1))
  refine ⟨V, hVW, hyV, a, fun τ hτ => ha_edge τ hτ, ?_⟩
  have hnat : ∀ {W W' : Opens (space sX)} (hW : W' ≤ W) (F : W → ℂ),
      (quotSheaf (space sX)).obj.map (homOfLE hW).op
        ((cokernel.π (constFun (space sX))).hom.app (op W) F) =
      (cokernel.π (constFun (space sX))).hom.app (op W') (show W' → ℂ from
        fun z => F ⟨z.1, hW z.2⟩) := fun hW F =>
    (ConcreteCategory.congr_hom ((cokernel.π (constFun (space sX))).hom.naturality
      (homOfLE hW).op) F).symm
  change (quotSheaf (space sX)).obj.map (homOfLE hVW).op
    (CechCochains.cechD U1 (quotSheaf (space sX)).obj 0 h i -
      lam.hom.app (op (CechCochains.inter U1 i)) (g.1 i)) = _
  rw [map_sub, hφlam, cechD_zero_apply, map_sub]
  simp only [CechCochains.restr, h]
  rw [hnat, hnat, hnat, hnat]
  have hsub : ∀ F G : (funSheaf (space sX) ℂ).obj.obj (op V),
      (cokernel.π (constFun (space sX))).hom.app (op V) F -
        (cokernel.π (constFun (space sX))).hom.app (op V) G =
      (cokernel.π (constFun (space sX))).hom.app (op V) (F - G) := fun F G => (map_sub _ F G).symm
  refine ((congrArg (· - _) (hsub _ _)).trans (hsub _ _)).trans (congrArg _ ?_)
  refine funext fun z => ?_
  change _ = ((a z : ℤ) : ℂ)
  rw [ha_val z]
  rfl

/-- A morphism of abelian groups sends `x = -y` to `f x = -f y`. -/
private lemma hom_apply_eq_neg_of_eq_neg {A B : AddCommGrpCat.{0}} (f : A ⟶ B) {x y : A}
    (h : x = -y) : f x = -f y := by
  rw [h, map_neg]

/-- The exponential obstruction of `L`, computed from a units logarithm `lam` and the Čech data
of a trivializing cover: minus the class of the cocycle `c`. -/
private theorem picardObstruction_eq_neg_quotExtClass {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [IsProper sX]
    (ι : ZSh (space sX) ⟶ (sheafCompose (Opens.grothendieckTopology (space sX))
      (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX))
    (e : (sheafCompose (Opens.grothendieckTopology (space sX))
      (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX) ⟶
        Stacks.Cohomology.Generators.unitsSheaf (analytification sX))
    (w : ι ≫ e = 0) (hS : (ShortComplex.mk ι e w).ShortExact)
    (L : SheafOfModules (ringCatSheaf sX))
    (hL : Stacks.SheafOfModules.IsInvertible (analytification sX).sheaf.obj
      (ringCatSheaf sX).property L)
    (lam : Stacks.Cohomology.Generators.unitsSheaf (analytification sX) ⟶ quotSheaf (space sX))
    (hext : hS.extClass =
      (Ext.mk₀ lam).comp (quotSeq_shortExact (space sX)).extClass (zero_add 1))
    {I : Type} (Ui : I → Opens (space sX)) (hUi : (⊤ : Opens (space sX)) = ⨆ i, Ui i)
    (sec : ∀ i, (Stacks.Cohomology.Generators.generatorTorsorOfInvertible
      (analytification sX) L hL).toTorsor.F.obj (Ui i))
    (g : CechCochains.cocycles1 Ui (Stacks.Cohomology.Generators.unitsSheaf
      (analytification sX)).obj)
    (hg : Stacks.Cohomology.SheafTorsor.IsTransitionCocycle
      (Stacks.Cohomology.Generators.generatorTorsorOfInvertible
        (analytification sX) L hL).toTorsor Ui sec g)
    (h : CechCochains.Cochain Ui (quotSheaf (space sX)).obj 0)
    (c : CechCochains.cocycles1 Ui (quotSheaf (space sX)).obj)
    (hc' : ∀ i, c.1 i = CechCochains.cechD Ui (quotSheaf (space sX)).obj 0 h i -
      lam.hom.app (op (CechCochains.inter Ui i)) (g.1 i)) :
    picardObstruction (analytification sX) hS
        (Stacks.SheafOfModules.Picard.classOf _ _ L hL) =
      ((-1 : ℤˣ) : ℤ) • quotExtClass (space sX) Ui hUi c := by
  refine (picardObstruction_classOf (analytification sX) hS L hL).trans ?_
  rw [hext]
  refine (Ext.comp_assoc_of_second_deg_zero _ _ _ _).symm.trans ?_
  refine (congrArg (fun y => Ext.comp y _ _) (sheafCohomologyOneExtEquiv_naturality lam _)).trans ?_
  rw [hom_apply_eq_neg_of_eq_neg (Stacks.Thickenings.sheafCohomologyOneExtEquiv (space sX)
      (quotSheaf (space sX))).hom (rightDerived_map_torsorClass_eq_neg _ lam Ui hUi sec g hg h c hc'),
    Ext.neg_comp, Units.val_neg, Units.val_one, neg_one_zsmul]
  rfl

private theorem analytic_side :
    ∃ ε₁ : ℤˣ, ∀ {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjectiveMorphism sX),
        haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX
        let J := Opens.grothendieckTopology (space sX)
        let O : Sheaf J AddCommGrpCat.{0} :=
          (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX)
        let Ou : Sheaf J AddCommGrpCat.{0} :=
          Stacks.Cohomology.Generators.unitsSheaf (analytification sX)
        let ZA : Sheaf J AddCommGrpCat.{0} :=
          (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
        ∀ (ι : ZA ⟶ O) (e : O ⟶ Ou) (w : ι ≫ e = 0) (hS : (ShortComplex.mk ι e w).ShortExact),
          (∀ (W : Opens (space sX)) (n : ℤ),
            (show (structureSheaf sX).obj.obj (op W) from ι.hom.app (op W)
              ((toSheafify J ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op W) n)) = n) →
          (∀ (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W)
            (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) (f : (Fin c.1.n → ℂ) → ℂ)
            (g g' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
            (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = f →
            (g' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
              (fun z => Complex.exp (2 * Real.pi * Complex.I * f z)) →
            s.1 x c = Chart.StalkRing.mk c.1 _ g →
            ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf sX).obj.obj (op W))ˣ) :
              (structureSheaf sX).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ g') →
          ∀ (L : SheafOfModules (ringCatSheaf sX))
            (hL : Stacks.SheafOfModules.IsInvertible (analytification sX).sheaf.obj
              (ringCatSheaf sX).property L)
            (E : space sX → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
            [TopologicalSpace (TotalSpace ℂ E)] [∀ x, TopologicalSpace (E x)]
            [FiberBundle ℂ E] [VectorBundle ℂ ℂ E]
            (val : ∀ V : Opens (space sX), L.val.obj (op V) → ∀ x : V, E x),
            (∀ (V : Opens (space sX)) (t : L.val.obj (op V)), Continuous fun x : V ↦ (⟨x.1, val V t x⟩ : TotalSpace ℂ E)) →
            (∀ (V : Opens (space sX)) (t t' : L.val.obj (op V)), val V (t + t') = val V t + val V t') →
            (∀ (V W : Opens (space sX)) (h : W ≤ V) (t : L.val.obj (op V)) (x : W),
              val W (L.val.map (homOfLE h).op t) x = val V t ⟨x.1, h x.2⟩) →
            (∀ (V : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op V))
              (t : L.val.obj (op V)) (x : V)
              (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U})
              (g : holGerms (c.1.coords ⟨x.1, c.2⟩)),
              s.1 x c = Chart.StalkRing.mk c.1 _ g →
              val V ((show (ringCatSheaf sX).obj.obj (op V) from s) • t) x = Germ.value (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) • val V t x) →
            (∀ x : space sX, ∃ (V : Opens (space sX)) (t : L.val.obj (op V)) (hx : x ∈ V),
              val V t ⟨x, hx⟩ ≠ 0) →
            ∃ (I : Type) (Ui : I → Opens (space sX)) (hUi : (⊤ : Opens (space sX)) = ⨆ i, Ui i)
              (wc : I → MMP.SingularChain.Simplex (space sX) 1 → ℤ),
              (∀ i (σ : MMP.SingularChain.Simplex (space sX) 2),
                Set.range σ ⊆ Ui i →
                  ComplexLineBundle.obstructionCocycle E σ =
                    MMP.SingularCochain.coboundary ℤ 1 (wc i) σ) ∧
              ∃ c : CechCochains.cocycles1 Ui (quotSheaf (space sX)).obj,
                IsKappaCocycle Ui wc c ∧
                picardObstruction (analytification sX) hS
                    (Stacks.SheafOfModules.Picard.classOf _ _ L hL) =
                  (ε₁ : ℤ) • quotExtClass (space sX) Ui hUi c := by
  refine ⟨-1, ?_⟩
  intro X sX hX J O Ou ZA ι e w hS hι he L hL E _ _ _ _ _ _ val h1 h2 h3 h4 h5
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX
  obtain ⟨lam, hlam, hext⟩ := exists_unitsLog sX ι e w hS hι
  obtain ⟨I, Ui, hUi, sec, g, hg, h, c, hc', wc, hwc, hc⟩ :=
    analytic_geometry sX hX ι e w hS hι he L hL E val h1 h2 h3 h4 h5 lam hlam
  exact ⟨I, Ui, hUi, wc, hwc, c, hc,
    picardObstruction_eq_neg_quotExtClass sX ι e w hS L hL lam hext Ui hUi sec g hg h c hc'⟩

private theorem exists_addEquiv_picardObstruction_eq_firstChernClass :
    ∃ φ : ∀ {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)), IsProjectiveMorphism sX →
        (Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology (analyticSpace sX))
            AddCommGrpCat.{0}).obj (.of ℤ)) 2 ≃+
          relativeSingularCohomology ℤ (.of ℤ ℤ) (analyticSpace sX) ∅ 2),
      ∃ ε : ℤˣ, ∀ {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjectiveMorphism sX),
        haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX
        let J := Opens.grothendieckTopology (space sX)
        let O : Sheaf J AddCommGrpCat.{0} :=
          (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX)
        let Ou : Sheaf J AddCommGrpCat.{0} :=
          Stacks.Cohomology.Generators.unitsSheaf (analytification sX)
        let ZA : Sheaf J AddCommGrpCat.{0} :=
          (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
        ∀ (ι : ZA ⟶ O) (e : O ⟶ Ou) (w : ι ≫ e = 0) (hS : (ShortComplex.mk ι e w).ShortExact),
          (∀ (W : Opens (space sX)) (n : ℤ),
            (show (structureSheaf sX).obj.obj (op W) from ι.hom.app (op W)
              ((toSheafify J ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op W) n)) = n) →
          (∀ (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W)
            (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) (f : (Fin c.1.n → ℂ) → ℂ)
            (g g' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
            (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = f →
            (g' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
              (fun z => Complex.exp (2 * Real.pi * Complex.I * f z)) →
            s.1 x c = Chart.StalkRing.mk c.1 _ g →
            ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf sX).obj.obj (op W))ˣ) :
              (structureSheaf sX).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ g') →
          ∀ (L : SheafOfModules (ringCatSheaf sX))
            (hL : Stacks.SheafOfModules.IsInvertible (analytification sX).sheaf.obj
              (ringCatSheaf sX).property L)
            (E : space sX → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
            [TopologicalSpace (TotalSpace ℂ E)] [∀ x, TopologicalSpace (E x)]
            [FiberBundle ℂ E] [VectorBundle ℂ ℂ E]
            (val : ∀ V : Opens (space sX), L.val.obj (op V) → ∀ x : V, E x),
            (∀ (V : Opens (space sX)) (t : L.val.obj (op V)), Continuous fun x : V ↦ (⟨x.1, val V t x⟩ : TotalSpace ℂ E)) →
            (∀ (V : Opens (space sX)) (t t' : L.val.obj (op V)), val V (t + t') = val V t + val V t') →
            (∀ (V W : Opens (space sX)) (h : W ≤ V) (t : L.val.obj (op V)) (x : W),
              val W (L.val.map (homOfLE h).op t) x = val V t ⟨x.1, h x.2⟩) →
            (∀ (V : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op V))
              (t : L.val.obj (op V)) (x : V)
              (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U})
              (g : holGerms (c.1.coords ⟨x.1, c.2⟩)),
              s.1 x c = Chart.StalkRing.mk c.1 _ g →
              val V ((show (ringCatSheaf sX).obj.obj (op V) from s) • t) x = Germ.value (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) • val V t x) →
            (∀ x : space sX, ∃ (V : Opens (space sX)) (t : L.val.obj (op V)) (hx : x ∈ V),
              val V t ⟨x, hx⟩ ≠ 0) →
            φ sX hX (picardObstruction (analytification sX) hS
                (Stacks.SheafOfModules.Picard.classOf _ _ L hL)) =
              ε • (relativeSingularCohomology.map ℤ (.of ℤ ℤ) (𝟙 (analyticSpace sX))
                (Set.empty_subset _) 2).hom (analyticFirstChernClass E) := by
  obtain ⟨φT, ε₀, hT⟩ := topological_side
  obtain ⟨ε₁, hA⟩ := analytic_side
  refine ⟨fun sX hX ↦ φT _ (metrizable_locallyContractible_analyticSpace sX hX).1
      (metrizable_locallyContractible_analyticSpace sX hX).2, ε₀ * ε₁, ?_⟩
  intro X sX hX J O Ou ZA ι e w hS hι he L hL E _ _ _ _ _ _ val h1 h2 h3 h4 h5
  obtain ⟨I, Ui, hUi, wc, hwc, c, hc, hpic⟩ := hA sX hX ι e w hS hι he L hL E val h1 h2 h3 h4 h5
  have hm := metrizable_locallyContractible_analyticSpace sX hX
  have hz : ComplexLineBundle.obstructionCocycle E ∈
      MMP.SingularCochain.relCocycles ℤ (∅ : Set (analyticSpace sX)) 2 :=
    ⟨fun σ hσ ↦ absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp),
      LinearMap.mem_ker.2 (ComplexLineBundle.coboundary_obstructionCocycle (E := E))⟩
  have key := hT _ hm.1 hm.2 _ hz Ui hUi wc hwc c hc
  have hQ : quotExtClass (space sX) Ui hUi c = (ε₀ : ℤ) • (φT _ hm.1 hm.2).symm
      ((MMP.SingularCochain.relativeSingularCohomologyEquiv ℤ
        (∅ : Set (analyticSpace sX)) 2).symm (Submodule.Quotient.mk ⟨_, hz⟩)) := by
    rw [key, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
  have hc1 : (relativeSingularCohomology.map ℤ (.of ℤ ℤ) (𝟙 (analyticSpace sX))
      (Set.empty_subset _) 2).hom (analyticFirstChernClass E) =
      (MMP.SingularCochain.relativeSingularCohomologyEquiv ℤ
        (∅ : Set (analyticSpace sX)) 2).symm (Submodule.Quotient.mk ⟨_, hz⟩) := by
    apply (MMP.SingularCochain.relativeSingularCohomologyEquiv ℤ
      (∅ : Set (analyticSpace sX)) 2).injective
    refine (MMP.SingularCochain.relativeSingularCohomologyEquiv_map (R := ℤ)
      (𝟙 (analyticSpace sX)) (A := (Set.univᶜ : Set (analyticSpace sX))) (Set.empty_subset _) 2
      (analyticFirstChernClass E)).trans ?_
    rw [LinearEquiv.apply_symm_apply]
    simp only [analyticFirstChernClass, firstChernClass, cohomologyWithSupports.ofCocycle,
      LinearEquiv.apply_symm_apply, MMP.SingularCochain.relCohomologyMap_mk]
    rfl
  change (φT _ hm.1 hm.2) _ = _
  rw [hpic, hQ, hc1, smul_smul, map_zsmul, AddEquiv.apply_symm_apply, Units.smul_def]
  push_cast
  ring_nf

section ValSheaf

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]

private lemma sectionValue_eq_residue {W : Opens (space (X ↘ Spec (.of ℂ)))}
    (s : (structureSheaf (X ↘ Spec (.of ℂ))).obj.obj (op W)) (x : W)
    (c : Chart (X ↘ Spec (.of ℂ))) (hc : x.1 ∈ ComplexPoints.chart c.U) :
    sectionValue _ s x = residue c ⟨x.1, hc⟩ (s.1 x ⟨c, hc⟩) :=
  residue_eq_of_isCompatible s.2.2 x _ _ _ _

/-- Evaluation of sections of `𝒪_{X^an}` at the points of `W`, as a ring homomorphism. -/
private noncomputable def valueHom (W : Opens (space (X ↘ Spec (.of ℂ)))) :
    (ringCatSheaf (X ↘ Spec (.of ℂ))).obj.obj (op W) →+* (W → ℂ) where
  toFun s := sectionValue _ (show (structureSheaf (X ↘ Spec (.of ℂ))).obj.obj (op W) from s)
  map_zero' := by funext x; simp [sectionValue]; rfl
  map_add' s t := by funext x; simp only [sectionValue]; exact map_add _ _ _
  map_one' := by funext x; simp only [sectionValue]; exact map_one _
  map_mul' s t := by funext x; simp only [sectionValue]; exact map_mul _ _ _

private lemma continuous_valueHom (W : Opens (space (X ↘ Spec (.of ℂ))))
    (s : (ringCatSheaf (X ↘ Spec (.of ℂ))).obj.obj (op W)) : Continuous (valueHom W s) :=
  continuous_sectionValue _ _

variable (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]

open InvertibleModule

/-- A function on `W` with values in the fibres of `L^top` is a *continuous section*. -/
private def IsContSec {W : Opens (space (X ↘ Spec (.of ℂ)))} (f : W → ℂ) : Prop :=
  Continuous fun x : W ↦ (⟨x.1, f x⟩ : TotalSpace ℂ (topologicalLineBundle L))

private lemma isContSec_iff {W : Opens (space (X ↘ Spec (.of ℂ)))} (f : W → ℂ) :
    IsContSec L f ↔ ∀ x : W, ContinuousAt (fun y : W ↦ (lineBundleCore L).coordChange
      ((lineBundleCore L).indexAt y.1) ((lineBundleCore L).indexAt x.1) y.1 (f y)) x := by
  rw [IsContSec, continuous_iff_continuousAt]
  refine forall_congr' fun x ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  simp only [continuous_subtype_val.continuousAt, true_and]
  rfl

private lemma coordChange_apply (s s' : Generator L) (y : ComplexPoints (X ↘ Spec (.of ℂ))) (v : ℂ) :
    (lineBundleCore L).coordChange s s' y v = evalExt _ (transitionSection s s') y * v :=
  rfl

/-- The module structure on functions `W → ℂ` over the sections of `𝒪_{X^an}`, through their
values. -/
@[instance_reducible] private noncomputable def funModule (W : Opens (space (X ↘ Spec (.of ℂ)))) :
    Module ((ringCatSheaf (X ↘ Spec (.of ℂ))).obj.obj (op W)) (W → ℂ) :=
  Module.compHom _ (valueHom W)

attribute [local instance] funModule

private lemma smul_fun_apply {W : Opens (space (X ↘ Spec (.of ℂ)))}
    (r : (ringCatSheaf (X ↘ Spec (.of ℂ))).obj.obj (op W)) (f : W → ℂ) (y : W) :
    (r • f) y = valueHom W r y * f y :=
  rfl

/-- The continuous sections of `L^top` over `W`, as a module over `𝒪_{X^an}(W)`. -/
private def contSec (W : Opens (space (X ↘ Spec (.of ℂ)))) :
    Submodule ((ringCatSheaf (X ↘ Spec (.of ℂ))).obj.obj (op W)) (W → ℂ) where
  carrier := {f | IsContSec L f}
  zero_mem' := by
    change IsContSec L 0
    rw [isContSec_iff]
    intro x
    simp only [Pi.zero_apply, map_zero]
    exact continuousAt_const
  add_mem' {f g} hf hg := by
    change IsContSec L (f + g)
    change IsContSec L f at hf
    change IsContSec L g at hg
    rw [isContSec_iff] at hf hg ⊢
    intro x
    simp only [Pi.add_apply, map_add]
    exact (hf x).add (hg x)
  smul_mem' r f hf := by
    change IsContSec L (r • f)
    change IsContSec L f at hf
    rw [isContSec_iff] at hf ⊢
    intro x
    have h : (fun y : W ↦ (lineBundleCore L).coordChange ((lineBundleCore L).indexAt y.1)
        ((lineBundleCore L).indexAt x.1) y.1 ((r • f) y)) = fun y ↦ valueHom W r y *
          (lineBundleCore L).coordChange ((lineBundleCore L).indexAt y.1)
            ((lineBundleCore L).indexAt x.1) y.1 (f y) := by
      funext y
      rw [smul_fun_apply, coordChange_apply, coordChange_apply]
      ring
    rw [h]
    exact (continuous_valueHom W r).continuousAt.mul (hf x)

/-- The presheaf of continuous sections of `L^top`. -/
private noncomputable def contPresheaf : (Opens (space (X ↘ Spec (.of ℂ))))ᵒᵖ ⥤ Ab where
  obj W := AddCommGrpCat.of (contSec L W.unop)
  map {W W'} i := AddCommGrpCat.ofHom
    { toFun := fun f ↦ ⟨fun y ↦ f.1 ⟨y.1, i.unop.le y.2⟩,
        (show IsContSec L f.1 from f.2).comp (continuous_inclusion i.unop.le)⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

@[instance_reducible] private noncomputable def contModule (W : (Opens (space (X ↘ Spec (.of ℂ))))ᵒᵖ) :
    Module ((ringCatSheaf (X ↘ Spec (.of ℂ))).obj.obj W) ((contPresheaf L).obj W) :=
  inferInstanceAs (Module _ (contSec L W.unop))

attribute [local instance] contModule

/-- The local predicate of continuous sections of `L^top`. -/
private def contLocalPredicate : TopCat.LocalPredicate (fun _ : space (X ↘ Spec (.of ℂ)) ↦ ℂ) where
  pred {W} f := IsContSec L (W := W) f
  res {W W'} i f hf := hf.comp (continuous_inclusion i.le)
  locality {W} f hf := by
    change Continuous _
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨V, hxV, i, hV⟩ := hf x
    have he : Topology.IsOpenEmbedding (Set.inclusion i.le) :=
      TopologicalSpace.Opens.isOpenEmbedding_of_le i.le
    have h1 := (hV.continuousAt (x := ⟨x.1, hxV⟩))
    exact (he.continuousAt_iff (g := fun x : W ↦ (⟨x.1, f x⟩ :
      TotalSpace ℂ (topologicalLineBundle L))) (x := ⟨x.1, hxV⟩)).1 h1

/-- Forgetting the group structure gives the sheaf of sections of the local predicate. -/
private noncomputable def contPresheafCompForget :
    contPresheaf L ⋙ forget Ab ≅
      TopCat.subpresheafToTypes (contLocalPredicate L).toPrelocalPredicate :=
  NatIso.ofComponents
    (fun W ↦ Iso.refl
      ((TopCat.subpresheafToTypes (contLocalPredicate L).toPrelocalPredicate).obj W))
    (fun _ ↦ rfl)

private lemma isSheaf_contPresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology (space (X ↘ Spec (.of ℂ)))) (contPresheaf L) := by
  rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)]
  exact TopCat.Presheaf.isSheaf_of_iso (contPresheafCompForget L).symm
    (TopCat.subpresheafToTypes.isSheaf _)

/-- The sheaf of `𝒪_{X^an}`-modules of continuous sections of `L^top`. -/
private noncomputable def contSheaf : SheafOfModules.{0} (ringCatSheaf (X ↘ Spec (.of ℂ))) where
  val := PresheafOfModules.ofPresheaf (contPresheaf L) (fun _ _ _ _ _ ↦ rfl)
  isSheaf := isSheaf_contPresheaf L

variable {L} in
/-- Changing the generator multiplies the coefficient by the transition function. -/
private lemma evalExt_coeff_frame (s s' : Generator L) {U : X.Opens} (ℓ : Γ(L, U))
    {y : ComplexPoints (X ↘ Spec (.of ℂ))} (hy : y ∈ ComplexPoints.chart (U ⊓ s.W ⊓ s'.W)) :
    evalExt _ (transitionSection s s') y *
        evalExt (U ⊓ s.W) (s.coeff inf_le_right (sectionRes L inf_le_left ℓ)) y =
      evalExt (U ⊓ s'.W) (s'.coeff inf_le_right (sectionRes L inf_le_left ℓ)) y := by
  have hT1 : U ⊓ s.W ⊓ s'.W ≤ U ⊓ s.W := inf_le_left
  have hT2 : U ⊓ s.W ⊓ s'.W ≤ s.W ⊓ s'.W := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hT3 : U ⊓ s.W ⊓ s'.W ≤ U ⊓ s'.W := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hTs' : U ⊓ s.W ⊓ s'.W ≤ s'.W := inf_le_right
  have e1 := congrArg (sectionRes L hT1)
    (s.coeff_smul (inf_le_right : U ⊓ s.W ≤ s.W) (sectionRes L inf_le_left ℓ))
  have e2 := congrArg (sectionRes L hT2) (transitionSection_smul s s')
  have e3 := congrArg (sectionRes L hT3)
    (s'.coeff_smul (inf_le_right : U ⊓ s'.W ≤ s'.W) (sectionRes L inf_le_left ℓ))
  rw [sectionRes_smul, sectionRes_sectionRes, sectionRes_sectionRes] at e1 e2 e3
  have key : (X.presheaf.map (homOfLE hT1).op (s.coeff inf_le_right (sectionRes L inf_le_left ℓ)) *
      X.presheaf.map (homOfLE hT2).op (transitionSection s s')) • sectionRes L hTs' s'.a =
        sectionRes L (hT1.trans inf_le_left) ℓ := by
    rw [mul_smul, e2, e1]
  have hc := (s'.coeff_eq hTs' e3).symm.trans (s'.coeff_eq hTs' key)
  have h := congrArg (fun t ↦ evalExt _ t y) hc
  simp only [evalExt_mul _ _ hy, evalExt_res _ _ hy] at h
  rw [mul_comm]
  exact h.symm

/-- The coefficient of a section `ℓ` of `L` over `U` at a point of `U(ℂ)`, in the frame of the
chart of `L^top` at that point. -/
private noncomputable def coeffAt {U : X.Opens} (ℓ : Γ(L, U))
    (y : (Opens.map (toSchemeHom (X ↘ Spec (.of ℂ)))).obj U) : ℂ :=
  evalExt (U ⊓ ((lineBundleCore L).indexAt y.1).W)
    (((lineBundleCore L).indexAt y.1).coeff inf_le_right (sectionRes L inf_le_left ℓ)) y.1

private lemma isContSec_coeffAt {U : X.Opens} (ℓ : Γ(L, U)) : IsContSec L (coeffAt L ℓ) := by
  rw [isContSec_iff]
  intro x
  set i := (lineBundleCore L).indexAt x.1
  have hxi : x.1 ∈ ComplexPoints.chart i.W := (lineBundleCore L).mem_baseSet_at x.1
  have hxU : x.1 ∈ ComplexPoints.chart U := ComplexPoints.mem_chart_iff.2 x.2
  have hxUi : x.1 ∈ ComplexPoints.chart (U ⊓ i.W) := by rw [chart_inf]; exact ⟨hxU, hxi⟩
  have hev : (fun y : (Opens.map (toSchemeHom (X ↘ Spec (.of ℂ)))).obj U ↦
      (lineBundleCore L).coordChange ((lineBundleCore L).indexAt y.1) i y.1 (coeffAt L ℓ y)) =ᶠ[𝓝 x]
        fun y ↦ evalExt (U ⊓ i.W) (i.coeff inf_le_right (sectionRes L inf_le_left ℓ)) y.1 := by
    have hmem : {y : (Opens.map (toSchemeHom (X ↘ Spec (.of ℂ)))).obj U |
        y.1 ∈ ComplexPoints.chart i.W} ∈ 𝓝 x :=
      ((isOpen_chart i.W).preimage continuous_subtype_val).mem_nhds hxi
    filter_upwards [hmem] with y hy
    rw [coordChange_apply]
    have hyU : y.1 ∈ ComplexPoints.chart U := ComplexPoints.mem_chart_iff.2 y.2
    refine evalExt_coeff_frame _ i ℓ ?_
    rw [chart_inf, chart_inf]
    exact ⟨⟨hyU, (lineBundleCore L).mem_baseSet_at y.1⟩, hy⟩
  refine ContinuousAt.congr ?_ hev.symm
  exact ((continuousOn_evalExt _ _).continuousAt ((isOpen_chart _).mem_nhds hxUi)).comp
    continuous_subtype_val.continuousAt

variable {L} in
private lemma Generator.coeff_add' (s : Generator L) {V : X.Opens} (h : V ≤ s.W) (t t' : Γ(L, V)) :
    s.coeff h (t + t') = s.coeff h t + s.coeff h t' :=
  s.coeff_eq h (by rw [add_smul, s.coeff_smul, s.coeff_smul])

variable {L} in
private lemma Generator.coeff_smul' (s : Generator L) {V : X.Opens} (h : V ≤ s.W) (c : Γ(X, V))
    (t : Γ(L, V)) : s.coeff h (c • t) = c * s.coeff h t :=
  s.coeff_eq h (by rw [mul_smul, s.coeff_smul])

variable {L} in
private lemma Generator.coeff_sectionRes (s : Generator L) {V V' : X.Opens} (h : V ≤ s.W) (h' : V' ≤ V)
    (t : Γ(L, V)) :
    s.coeff (h'.trans h) (sectionRes L h' t) = X.presheaf.map (homOfLE h').op (s.coeff h t) :=
  s.coeff_eq _ (by
    rw [← sectionRes_sectionRes h h' s.a, ← sectionRes_smul, s.coeff_smul])

variable {L} in
private lemma sectionRes_add {V W : X.Opens} (h : V ≤ W) (t t' : Γ(L, W)) :
    sectionRes L h (t + t') = sectionRes L h t + sectionRes L h t' :=
  map_add _ _ _

private lemma evalExt_add {U : X.Opens} (g g' : Γ(X, U)) {x : ComplexPoints (X ↘ Spec (.of ℂ))}
    (hx : x ∈ ComplexPoints.chart U) :
    evalExt U (g + g') x = evalExt U g x + evalExt U g' x := by
  simp only [evalExt_of_mem _ hx, ← evalHom_apply, map_add]

private lemma coeffAt_add {U : X.Opens} (ℓ ℓ' : Γ(L, U))
    (y : (Opens.map (toSchemeHom (X ↘ Spec (.of ℂ)))).obj U) :
    coeffAt L (ℓ + ℓ') y = coeffAt L ℓ y + coeffAt L ℓ' y := by
  have hy : y.1 ∈ ComplexPoints.chart (U ⊓ ((lineBundleCore L).indexAt y.1).W) := by
    rw [chart_inf]
    exact ⟨ComplexPoints.mem_chart_iff.2 y.2, (lineBundleCore L).mem_baseSet_at y.1⟩
  simp only [coeffAt]
  rw [sectionRes_add, Generator.coeff_add', evalExt_add _ _ hy]

private lemma coeffAt_smul {U : X.Opens} (r : Γ(X, U)) (ℓ : Γ(L, U))
    (y : (Opens.map (toSchemeHom (X ↘ Spec (.of ℂ)))).obj U) :
    coeffAt L (r • ℓ) y = evalExt U r y.1 * coeffAt L ℓ y := by
  have hy : y.1 ∈ ComplexPoints.chart (U ⊓ ((lineBundleCore L).indexAt y.1).W) := by
    rw [chart_inf]
    exact ⟨ComplexPoints.mem_chart_iff.2 y.2, (lineBundleCore L).mem_baseSet_at y.1⟩
  simp only [coeffAt]
  rw [sectionRes_smul, Generator.coeff_smul', evalExt_mul _ _ hy, evalExt_res _ _ hy]

private lemma coeffAt_sectionRes {U V : X.Opens} (h : V ≤ U) (ℓ : Γ(L, U))
    (y : (Opens.map (toSchemeHom (X ↘ Spec (.of ℂ)))).obj V) :
    coeffAt L (sectionRes L h ℓ) y = coeffAt L ℓ ⟨y.1, h y.2⟩ := by
  have hy : y.1 ∈ ComplexPoints.chart (V ⊓ ((lineBundleCore L).indexAt y.1).W) := by
    rw [chart_inf]
    exact ⟨ComplexPoints.mem_chart_iff.2 y.2, (lineBundleCore L).mem_baseSet_at y.1⟩
  simp only [coeffAt]
  have hVU : V ⊓ ((lineBundleCore L).indexAt y.1).W ≤ U ⊓ ((lineBundleCore L).indexAt y.1).W :=
    inf_le_inf_right _ h
  rw [sectionRes_sectionRes, ← evalExt_res hVU _ hy, ← Generator.coeff_sectionRes _ inf_le_right hVU,
    sectionRes_sectionRes]

/-- Every `ℂ`-point of an open `V` lies in a chart contained in `V`. -/
private lemma exists_chart_le {V : X.Opens} {x : space (X ↘ Spec (.of ℂ))}
    (hx : x.toScheme ∈ V) :
    ∃ c : Chart (X ↘ Spec (.of ℂ)), c.U ≤ V ∧ x ∈ ComplexPoints.chart c.U := by
  obtain ⟨U, hU, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  obtain ⟨n, gen, h⟩ := exists_gens (sX := X ↘ Spec (.of ℂ)) hU
  exact ⟨⟨U, hU, n, gen, h⟩, hUV, ComplexPoints.mem_chart_iff.2 hxU⟩

/-- The value of the image of a section `g` of `𝒪_X` in `𝒪_{X^an}` is the value of `g`. -/
private lemma sectionValue_sharpHom (V : X.Opens) (g : Γ(X, V))
    (y : (Opens.map (toSchemeHom (X ↘ Spec (.of ℂ)))).obj V) :
    sectionValue _ (show (structureSheaf (X ↘ Spec (.of ℂ))).obj.obj
      (op ((Opens.map (toSchemeHom (X ↘ Spec (.of ℂ)))).obj V)) from sharpHom V g) y =
      evalExt V g y.1 := by
  obtain ⟨c, hcV, hyc⟩ := exists_chart_le (V := V) (x := y.1) y.2
  refine (sectionValue_eq_residue _ y c hyc).trans ?_
  rw [sharpHom_apply]
  have hg : X.presheaf.germ V y.1.toScheme y.2 g = X.presheaf.germ c.U y.1.toScheme
      (ComplexPoints.mem_chart_iff.1 hyc) (X.presheaf.map (homOfLE hcV).op g) :=
    (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hcV) _ _ g).symm
  rw [hg, Chart.stalkHom_germ]
  obtain ⟨q, hq⟩ := c.surjective (X.presheaf.map (homOfLE hcV).op g)
  change c.pres q = _ at hq
  rw [← hq, Chart.toStalkRing_pres, residue_mk, coe_polyGermHom, Germ.value_ofFun,
    evalExt_of_mem _ (ComplexPoints.mem_chart_iff.2 y.2), ← evalHom_apply,
    evalHom_res hcV ⟨y.1, hyc⟩, ← hq, Chart.evalHom_pres]

/-- The coefficient map `L ⟶ α_* 𝓔`. -/
private noncomputable def coeffMap : L ⟶
    (SheafOfModules.pushforward.{0} (ringCatSheafHom (X ↘ Spec (.of ℂ)))).obj (contSheaf L) where
  val := PresheafOfModules.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun ℓ ↦ (⟨coeffAt L ℓ, isContSec_coeffAt L ℓ⟩ : contSec L _)
          map_zero' := Subtype.ext (funext fun y ↦
            (show coeffAt L (0 : Γ(L, U.unop)) y = 0 by
              simpa using coeffAt_add L (0 : Γ(L, U.unop)) 0 y))
          map_add' := fun ℓ ℓ' ↦ Subtype.ext (funext (coeffAt_add L ℓ ℓ')) }
      naturality := fun U V i ↦ by
        ext ℓ
        exact Subtype.ext (funext (coeffAt_sectionRes L (leOfHom i.unop) ℓ)) }
    (fun U r ℓ ↦ Subtype.ext (funext fun y ↦ by
      refine (coeffAt_smul L r ℓ y).trans ?_
      exact congrArg (· * coeffAt L ℓ y) (sectionValue_sharpHom U.unop r y).symm))

private theorem exists_val :
    ∃ val : ∀ V : Opens (space (X ↘ Spec (.of ℂ))),
        ((analytifyModule (X ↘ Spec (.of ℂ))).obj L).val.obj (op V) →
        ∀ x : V, InvertibleModule.topologicalLineBundle L x.1,
      (∀ (V : Opens (space (X ↘ Spec (.of ℂ))))
        (t : ((analytifyModule (X ↘ Spec (.of ℂ))).obj L).val.obj (op V)),
        Continuous fun x : V ↦ (⟨x.1, val V t x⟩ :
          TotalSpace ℂ (InvertibleModule.topologicalLineBundle L))) ∧
      (∀ (V : Opens (space (X ↘ Spec (.of ℂ))))
        (t t' : ((analytifyModule (X ↘ Spec (.of ℂ))).obj L).val.obj (op V)),
        val V (t + t') = val V t + val V t') ∧
      (∀ (V W : Opens (space (X ↘ Spec (.of ℂ)))) (h : W ≤ V)
        (t : ((analytifyModule (X ↘ Spec (.of ℂ))).obj L).val.obj (op V)) (x : W),
        val W (((analytifyModule (X ↘ Spec (.of ℂ))).obj L).val.map (homOfLE h).op t) x =
          val V t ⟨x.1, h x.2⟩) ∧
      (∀ (V : Opens (space (X ↘ Spec (.of ℂ)))) (s : (structureSheaf (X ↘ Spec (.of ℂ))).obj.obj (op V))
        (t : ((analytifyModule (X ↘ Spec (.of ℂ))).obj L).val.obj (op V)) (x : V)
        (c : {c : Chart (X ↘ Spec (.of ℂ)) // x.1 ∈ ComplexPoints.chart c.U})
        (g : holGerms (c.1.coords ⟨x.1, c.2⟩)),
        s.1 x c = Chart.StalkRing.mk c.1 _ g →
        val V ((show (ringCatSheaf (X ↘ Spec (.of ℂ))).obj.obj (op V) from s) • t) x =
          Germ.value (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) • val V t x) ∧
      (∀ x : space (X ↘ Spec (.of ℂ)), ∃ (V : Opens (space (X ↘ Spec (.of ℂ))))
        (t : ((analytifyModule (X ↘ Spec (.of ℂ))).obj L).val.obj (op V)) (hx : x ∈ V),
          val V t ⟨x, hx⟩ ≠ 0) := by
  let adj := SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom (X ↘ Spec (.of ℂ)))
  let ψ : (analytifyModule (X ↘ Spec (.of ℂ))).obj L ⟶ contSheaf L :=
    (adj.homEquiv _ _).symm (coeffMap L)
  refine ⟨fun V t x ↦ (ψ.val.app (op V) t).1 x, fun V t ↦ (ψ.val.app (op V) t).2,
    fun V t t' ↦ ?_, fun V W h t x ↦ ?_, fun V s t x c g hs ↦ ?_, fun x ↦ ?_⟩
  · funext x
    exact congrArg (fun m : (contSheaf L).val.obj (op V) ↦ (show contSec L V from m).1 x)
      (map_add (ψ.val.app (op V)).hom t t')
  · exact congrArg (fun m : (contSheaf L).val.obj (op W) ↦ (show contSec L W from m).1 x)
      (PresheafOfModules.naturality_apply ψ.val (homOfLE h).op t)
  · refine (congrArg (fun m : (contSheaf L).val.obj (op V) ↦ (show contSec L V from m).1 x)
      ((ψ.val.app (op V)).hom.map_smul s t)).trans ?_
    refine Eq.trans (b := valueHom V s x * (show contSec L V from ψ.val.app (op V) t).1 x) rfl ?_
    refine Eq.trans ?_ (smul_eq_mul (Germ.value (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ)) _).symm
    refine congrArg (· * _) ?_
    have hs' : s.1 x ⟨c.1, c.2⟩ = Chart.StalkRing.mk c.1 _ g := hs
    exact (sectionValue_eq_residue s x c.1 c.2).trans (by rw [hs', residue_mk])
  · set i := (lineBundleCore L).indexAt x
    have hxi : x ∈ ComplexPoints.chart i.W := (lineBundleCore L).mem_baseSet_at x
    refine ⟨(Opens.map (toSchemeHom (X ↘ Spec (.of ℂ)))).obj i.W,
      (adj.unit.app L).val.app (op i.W) i.a, ComplexPoints.mem_chart_iff.1 hxi, ?_⟩
    have hu : adj.unit.app L ≫
        (SheafOfModules.pushforward.{0} (ringCatSheafHom (X ↘ Spec (.of ℂ)))).map ψ =
          coeffMap L :=
      (Adjunction.homEquiv_unit adj L (contSheaf L) ψ).symm.trans (Equiv.apply_symm_apply _ _)
    have hval := congrArg (fun F : L ⟶ (SheafOfModules.pushforward.{0}
      (ringCatSheafHom (X ↘ Spec (.of ℂ)))).obj (contSheaf L) ↦
        (show contSec L ((Opens.map (toSchemeHom (X ↘ Spec (.of ℂ)))).obj i.W) from
          F.val.app (op i.W) i.a).1 ⟨x, ComplexPoints.mem_chart_iff.1 hxi⟩) hu
    have hc : i.coeff (inf_le_right : i.W ⊓ i.W ≤ i.W) (sectionRes L inf_le_left i.a) = 1 :=
      i.coeff_eq _ (one_smul _ _)
    have h1 : coeffAt L i.a ⟨x, ComplexPoints.mem_chart_iff.1 hxi⟩ = 1 := by
      rw [coeffAt, hc, evalExt_one (by rw [chart_inf]; exact ⟨hxi, hxi⟩)]
    intro h0
    exact (one_ne_zero : (1 : ℂ) ≠ 0) (h1.symm.trans (hval.symm.trans h0))

end ValSheaf

end LogarithmFirstChern

section CurvePart

open CategoryTheory AlgebraicGeometry MMP Bundle
open MMP.Intersection.Scheme (dimension)
open scoped MMP.SubschemeOver

section

variable {C : Scheme.{0}} [C.Over (Spec (.of ℂ))] [IsComplexScheme C]
  [IsIntegral C]

/-- The fundamental class of a complex curve. -/
private noncomputable def fundCls (hC1 : ((1 : ℕ) : WithBot ℕ∞) = dimension C) :
    borelMooreHomology ℤ (ModuleCat.of ℤ ℤ) (TopCat.of (UnderlyingSpace ℂ C)) ((2 * 1 : ℕ) : ℤ) :=
  (existsUnique_isVarietyFundamentalClass ℤ hC1).choose

private lemma isVarietyFundamentalClass_fundCls (hC1 : ((1 : ℕ) : WithBot ℕ∞) = dimension C) :
    IsVarietyFundamentalClass ℤ hC1 (fundCls hC1) :=
  (existsUnique_isVarietyFundamentalClass ℤ hC1).choose_spec.1

/-- The point `Spec ℂ` is a complex scheme. -/
private theorem isComplexScheme_spec : IsComplexScheme (Spec (.of ℂ)) :=
  haveI : IsSmoothVariety ℂ (Spec (.of ℂ) ↘ Spec (.of ℂ)) :=
    MMP.isSmoothVariety_of_eq_id (MMP.specOverSpec_over_self ℂ)
  IsComplexScheme.of_isSmoothVariety _

attribute [local instance] isComplexScheme_spec

private lemma dimension_spec : ((0 : ℕ) : WithBot ℕ∞) = dimension (Spec (.of ℂ)) := by
  change _ = topologicalKrullDim (PrimeSpectrum ℂ)
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]; rfl

/-- The fundamental class of the point. -/
private noncomputable def pointCls :
    borelMooreHomology ℤ (ModuleCat.of ℤ ℤ) (TopCat.of (UnderlyingSpace ℂ (Spec (.of ℂ))))
      ((2 * 0 : ℕ) : ℤ) :=
  (existsUnique_isVarietyFundamentalClass ℤ dimension_spec).choose

private lemma bijective_smul_pointCls :
    Function.Bijective (LinearMap.toSpanSingleton ℤ _ pointCls) := by
  convert (existsUnique_isVarietyFundamentalClass ℤ dimension_spec).choose_spec.2.2 using 1
  funext r
  rfl

/-- The degree `H_0(pt) ≅ ℤ`. -/
private noncomputable def pointDeg :
    borelMooreHomology ℤ (ModuleCat.of ℤ ℤ) (TopCat.of (UnderlyingSpace ℂ (Spec (.of ℂ))))
      ((2 * 0 : ℕ) : ℤ) →+ ℤ :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ _ pointCls)
    bijective_smul_pointCls).symm.toLinearMap.toAddMonoidHom

private lemma pointDeg_toSpanSingleton (r : ℤ) :
    pointDeg (LinearMap.toSpanSingleton ℤ _ pointCls r) = r :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ _ pointCls)
    bijective_smul_pointCls).symm_apply_apply r

/-- The cycle class of the point of `Spec ℂ` has degree one. -/
private lemma pointDeg_pointCycleClass (x : Spec (.of ℂ))
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Spec (.of ℂ) ↘ Spec (.of ℂ)) x = ((0 : ℕ) : ℤ)) :
    pointDeg (MMP.Chow.pointCycleClass ℤ x hx) = 1 := by
  have hμ := (existsUnique_isVarietyFundamentalClass ℤ
    (MMP.Chow.natCast_eq_dimension_integralComponentAt x hx)).choose_spec.1
  have hcW := (existsUnique_isVarietyFundamentalClass ℤ dimension_spec).choose_spec.1
  haveI := Stacks.Chow.isIntegral_integralComponentAt x
  have hsurj : Function.Surjective (Stacks.Chow.integralComponentAt x).subschemeι.base :=
    fun _ ↦ ⟨Classical.choice inferInstance, Subsingleton.elim _ _⟩
  rw [MMP.Chow.pointCycleClass, IsVarietyFundamentalClass.pushforward_eq_residueDegree_smul _
    hsurj dimension_spec hμ hcW, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion,
    Nat.cast_one]
  exact pointDeg_toSpanSingleton 1

/-- The degree of the cycle class of a zero-cycle on `Spec ℂ` is its coefficient. -/
private lemma pointDeg_cycleClass (s : Spec (.of ℂ))
    (β : Stacks.Chow.CycleGroup (Stacks.Chow.fieldChowSituation ℂ) (Spec (.of ℂ) ↘ Spec (.of ℂ))
      ((0 : ℕ) : ℤ)) :
    pointDeg (MMP.Chow.cycleClass ℤ 0 β) = β.1 s := by
  classical
  have hpt : ∀ x : Spec (.of ℂ), x = s := fun _ ↦ Subsingleton.elim _ _
  rw [MMP.Chow.cycleClass_eq_sum, map_sum]
  by_cases h : β.1 s = 0
  · rw [h]
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    rw [hpt x, h, zero_smul, map_zero]
  · have hmem : s ∈ (MMP.Chow.finite_support_cycle β).toFinset :=
      (Set.Finite.mem_toFinset _).2 h
    rw [Finset.sum_eq_single_of_mem _ hmem (fun b _ hb ↦ absurd (hpt b) hb)]
    have hd := (Stacks.Chow.mem_cyclesOfDimension_iff_forall_point
      (Stacks.Chow.fieldChowSituation ℂ) _ _ β.1).mp β.2 s h
    rw [map_zsmul, MMP.Chow.pointCycleClassOrZero, dif_pos hd, pointDeg_pointCycleClass,
      smul_eq_mul, mul_one]

end

private lemma compl_univ_subset {α : Type*} (S : Set α) : (Set.univ : Set α)ᶜ ⊆ S :=
  fun y hy ↦ (hy (Set.mem_univ y)).elim

section DegreeTransport

variable {R : Type} [CommRing R]

private lemma congrDegree_pushforward {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : IsProperMap f) {i i' : ℤ}
    (h : i = i') (x : borelMooreHomology R (ModuleCat.of R R) X i) :
    BorelMooreCross.congrDegree R Y h
        ((borelMooreHomology.pushforward R (ModuleCat.of R R) f hf i).hom x) =
      (borelMooreHomology.pushforward R (ModuleCat.of R R) f hf i').hom
        (BorelMooreCross.congrDegree R X h x) := by
  subst h
  rfl

end DegreeTransport

section Eval

open UnderlyingSpace

variable {C : Scheme.{0}} [C.Over (Spec (.of ℂ))] [IsComplexScheme C]
  [IsIntegral C] [IsProper (C ↘ Spec (.of ℂ))]

omit [IsComplexScheme C] [IsIntegral C] [IsProper (C ↘ Spec (.of ℂ))] in
/-- The structure morphism of `C` lies over `Spec ℂ`. -/
private theorem isOver_structureMorphism : (C ↘ Spec (.of ℂ)).IsOver (Spec (.of ℂ)) :=
  ⟨by rw [MMP.specOverSpec_over_self, Category.comp_id]⟩

attribute [local instance] isOver_structureMorphism isComplexScheme_spec

private lemma isProperMap_toPoint :
    IsProperMap (UnderlyingSpace.map (K := ℂ) (C ↘ Spec (.of ℂ))) :=
  IsComplexScheme.isProperMap_map _

variable (hC1 : ((1 : ℕ) : WithBot ℕ∞) = dimension C)

/-- Evaluation of `H²(C(ℂ))` on the fundamental class: cap with `[C]`, push forward to a point,
and read off the degree. -/
private noncomputable def ev :
    cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ) (TopCat.of (UnderlyingSpace ℂ C)) Set.univ
      ((2 * 1 : ℕ) : ℤ) →+ ℤ where
  toFun c := pointDeg (BorelMooreCross.congrDegree ℤ _
    (i := ((2 * 1 : ℕ) : ℤ) - ((2 * 1 : ℕ) : ℤ)) (i' := ((2 * 0 : ℕ) : ℤ)) (by norm_num)
    ((borelMooreHomology.pushforward ℤ (ModuleCat.of ℤ ℤ)
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (C ↘ Spec (.of ℂ)))) isProperMap_toPoint
        _).hom (borelMooreHomology.capProduct ℤ _ Set.univ ((2 * 1 : ℕ) : ℤ)
          ((2 * 1 : ℕ) : ℤ) c (fundCls hC1))))
  map_zero' := by
    simp only [LinearMap.map_zero, LinearMap.zero_apply, LinearEquiv.map_zero, map_zero]
  map_add' a b := by
    simp only [LinearMap.map_add, LinearMap.add_apply, LinearEquiv.map_add, map_add]

/-- The evaluation of `c₁ᵗᵒᵖ(N)` is the degree of the push-forward to the point of
`c₁ᵗᵒᵖ(N) ∩ [C]`. -/
private theorem ev_firstChernClassTop (N : C.Modules) [Stacks.Ample.IsInvertibleModule C N] :
    ev hC1 (MMP.Chow.firstChernClassTop ℤ N) =
      pointDeg ((borelMooreHomology.pushforward ℤ (ModuleCat.of ℤ ℤ)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (C ↘ Spec (.of ℂ))))
        (isProperMap_map (K := ℂ) _) (2 * 0 : ℕ)).hom
          (MMP.Chow.firstChernClassTopCap ℤ N 0 (fundCls hC1))) := by
  simp only [MMP.Chow.firstChernClassTopCap, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe]
  rw [← congrDegree_pushforward]
  rfl

end Eval

section CohomologyTransport

/-- Changing integral coefficients along the identity of `ℤ` is the identity. -/
private lemma mapCoeff_intCastRingHom {Y : TopCat.{0}} (n : ℕ)
    (x : MMP.Analytic.singularCohomology ℤ Y n) :
    MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℤ) n x = x := by
  simp only [MMP.Analytic.singularCohomology.mapCoeff, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  rw [LinearEquiv.symm_apply_eq]
  generalize MMP.SingularCochain.relativeSingularCohomologyEquiv ℤ _ n x = y
  induction y using Submodule.Quotient.induction_on with
  | H φ =>
    first
    | rfl
    | exact congrArg (Submodule.Quotient.mk (p := _)) (Subtype.ext (funext fun _ ↦ Int.cast_id))

end CohomologyTransport

section ChernEuler

open MMP.Analytic MMP.Analytic.InvertibleModule

variable {C : Scheme.{0}} [C.Over (Spec (.of ℂ))]

/-- The first Chern class of an invertible module `N`, read on `C(ℂ)`, is the topological first
Chern class `0^* u` of the line bundle `𝐕(N^∨)`. -/
private theorem map_algebraicFirstChernClass_eq (N : C.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 N] :
    (relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
      (TopCat.ofHom ((ComplexPoints.homeomorphUnderlyingSpace (X := C)).symm : C(_, _)))
      (A' := Set.univᶜ) (A := Set.univᶜ) (compl_univ_subset _)
      ((2 * 1 : ℕ) : ℤ)).hom (algebraicFirstChernClass N) =
    MMP.Modules.topFirstChernClass ℤ (Scheme.Modules.dual N) := by
  rw [MMP.Modules.topFirstChernClass_dual, mapCoeff_intCastRingHom]
  rfl

end ChernEuler

end CurvePart

open CategoryTheory AlgebraicGeometry in
/-- The coefficient of a proper push-forward depends on the structure morphism of the target
only through its value. -/
private lemma properPushforward_apply_congr {S : Stacks.Chow.ChowSituation.{0}} {X Y : Scheme.{0}}
    (sX : X ⟶ S.S) [LocallyOfFiniteType sX] {sY tY : Y ⟶ S.S} [LocallyOfFiniteType sY]
    [LocallyOfFiniteType tY] (e : sY = tY) (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX)
    (hf₂ : f ≫ tY = sX) (k : ℤ) (c : Stacks.Chow.CycleGroup S sX k) (y : Y) :
    (Stacks.Chow.properPushforward S sX sY f hf k c).1 y =
      (Stacks.Chow.properPushforward S sX tY f hf₂ k c).1 y := by
  subst e
  rfl

section CurveEvalPart

open CategoryTheory AlgebraicGeometry MMP Opposite MMP.Analytic
open MMP.Intersection.Scheme (dimension)
open scoped MMP.SubschemeOver

variable {C : Scheme.{0}} [C.Over (Spec (.of ℂ))] [IsComplexScheme C]
  [IsIntegral C] [IsProper (C ↘ Spec (.of ℂ))]
  (hC1 : ((1 : ℕ) : WithBot ℕ∞) = dimension C)

/-- Evaluation of `H²(C^an)` on the fundamental class of the curve `C`. -/
private noncomputable def curveEval :
    relativeSingularCohomology ℤ (ModuleCat.of ℤ ℤ)
      (ComplexPoints.analyticSpace (C ↘ Spec (.of ℂ))) ∅ 2 →+ ℤ :=
  (ev hC1).comp (relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
    (TopCat.ofHom ((ComplexPoints.homeomorphUnderlyingSpace (X := C)).symm : C(_, _)))
    (A' := Set.univᶜ) (A := ∅) (compl_univ_subset _) ((2 * 1 : ℕ) : ℤ)).hom.toAddMonoidHom

private theorem curveEval_map (N : C.Modules) [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 N] :
    curveEval hC1 ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
        (𝟙 (ComplexPoints.analyticSpace (C ↘ Spec (.of ℂ)))) (Set.empty_subset _) 2).hom
          (algebraicFirstChernClass N)) =
      ev hC1 ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
        (TopCat.ofHom ((ComplexPoints.homeomorphUnderlyingSpace (X := C)).symm : C(_, _)))
        (A' := Set.univᶜ) (A := Set.univᶜ) (compl_univ_subset _)
        ((2 * 1 : ℕ) : ℤ)).hom (algebraicFirstChernClass N)) := by
  change ev hC1 ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) _ _ _).hom
    ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) _ _ _).hom _)) = _
  rw [← relativeSingularCohomology.map_comp_apply' ℤ _ _ (compl_univ_subset _)]
  exact congrArg (ev hC1)
    (relativeSingularCohomology.map_congr_apply ℤ (Category.comp_id _) _ _ _ _)

variable [LocallyOfFiniteType (C ↘ Spec (.of ℂ))] [QuasiCompact (C ↘ Spec (.of ℂ))]

attribute [local instance] isOver_structureMorphism isComplexScheme_spec

/-- **The evaluation of `c₁(N)` on `[C]` is the degree of `N`**, for an invertible module `N`
with a non-zero global section `σ`: `c₁(N)` is the topological first Chern class of `𝐕(N^∨)`,
`c₁ᵗᵒᵖ(N) ∩ [C]` is the cycle class of the zero scheme `Z(σ)` (Fulton, Lemma 19.1.3), whose
push-forward to the point is the degree of `[Z(σ)]_0`, and that degree is `deg N`. -/
private theorem curveEval_eq_of_section (hdim : topologicalKrullDim C ≤ 1) (N : C.Modules)
    [hN : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 N]
    (σ : N.sections) (hσ : σ.eval (op ⊤) ≠ 0) :
    curveEval hC1 ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
        (𝟙 (ComplexPoints.analyticSpace (C ↘ Spec (.of ℂ)))) (Set.empty_subset _) 2).hom
          (algebraicFirstChernClass N)) = invertibleCurveDegree ℂ (C ↘ Spec (.of ℂ)) hdim N := by
  haveI hN' : SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property N := hN
  -- the degree of the push-forward to the point of the cycle class of `[Z(σ)]_0` is `deg N`
  have hdeg : pointDeg ((borelMooreHomology.pushforward ℤ (ModuleCat.of ℤ ℤ)
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (C ↘ Spec (.of ℂ))))
      (UnderlyingSpace.isProperMap_map (K := ℂ) _) (2 * 0 : ℕ)).hom
        (MMP.Chow.cycleClass ℤ 0 (Stacks.Chow.cycleAssociatedToClosedSubscheme
          (Stacks.Chow.fieldChowSituation ℂ) (C ↘ Spec (.of ℂ))
          (Stacks.Divisors.zeroScheme C N (σ.eval (op ⊤))).subschemeι ((0 : ℕ) : ℤ)))) =
      invertibleCurveDegree ℂ (C ↘ Spec (.of ℂ)) hdim N := by
    rw [← MMP.Chow.cycleClass_properPushforward, pointDeg_cycleClass (IsLocalRing.closedPoint ℂ)]
    refine (properPushforward_apply_congr (S := Stacks.Chow.fieldChowSituation ℂ) _
      (MMP.specOverSpec_over_self ℂ) _ _ (Category.comp_id _) _ _ _).trans ?_
    exact (Stacks.Chow.cycleDegree_apply _ _ _ _).symm.trans
      ((degree_zeroCycle_zeroScheme_eq_finrank_cohomologyOverField ℂ (C ↘ Spec (.of ℂ)) hdim N σ
        hσ).trans (invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_zeroScheme ℂ
          (C ↘ Spec (.of ℂ)) hdim N σ hσ
          (forall_finiteDimensional_cohomologyOverField_unit ℂ (C ↘ Spec (.of ℂ)))).symm)
  -- `c₁(N) ∩ [C]` is the cycle class of `[Z(σ)]_0`
  haveI : Stacks.Ample.IsInvertibleModule C N := hN
  have hZ := MMP.Chow.cycleClass_zeroScheme_eq_firstChernClassTopCap ℤ N hC1 _ hσ
    (isVarietyFundamentalClass_fundCls hC1)
  simp only at hZ
  rw [curveEval_map, map_algebraicFirstChernClass_eq]
  change ev hC1 (MMP.Chow.firstChernClassTop ℤ N) = _
  rw [ev_firstChernClassTop, ← hZ]
  exact hdeg

end CurveEvalPart

section Twist

open CategoryTheory AlgebraicGeometry Opposite MMP.Analytic MMP

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj

private theorem eq_invertibleCurveDegree_of_sections {C : Scheme.{0}} [C.Over (Spec (.of ℂ))]
    [IsIntegral C] [IsProper (C ↘ Spec (.of ℂ))] (hdim : topologicalKrullDim C ≤ 1)
    (ψ : relativeSingularCohomology ℤ (ModuleCat.of ℤ ℤ)
      (ComplexPoints.analyticSpace (C ↘ Spec (.of ℂ))) ∅ 2 →+ ℤ)
    (hsec : ∀ (N : C.Modules) [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 N]
      (σ : N.sections), σ.eval (op ⊤) ≠ 0 →
      ψ ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
        (𝟙 (ComplexPoints.analyticSpace (C ↘ Spec (.of ℂ)))) (Set.empty_subset _) 2).hom
          (algebraicFirstChernClass N)) = invertibleCurveDegree ℂ (C ↘ Spec (.of ℂ)) hdim N)
    (M : C.Modules) [hM : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 M] :
    ψ ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
        (𝟙 (ComplexPoints.analyticSpace (C ↘ Spec (.of ℂ)))) (Set.empty_subset _) 2).hom
          (algebraicFirstChernClass M)) = invertibleCurveDegree ℂ (C ↘ Spec (.of ℂ)) hdim M := by
  haveI : IsNoetherian C :=
    Stacks.HQuasiProjectiveDimensionOne.isNoetherian_of_finiteType_over_field (C ↘ Spec (.of ℂ))
  haveI : C.IsSeparated :=
    Stacks.HQuasiProjectiveDimensionOne.isSeparated_of_isSeparated_over_field (C ↘ Spec (.of ℂ))
  haveI hLm : Stacks.Ample.IsInvertibleModule C M := hM
  haveI hM' : SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property M := hM
  obtain ⟨L, _, hL⟩ :=
    Stacks.FormalCurve.exists_isAmple_of_isProper_of_topologicalKrullDim_le_one
      (C ↘ Spec (.of ℂ)) hdim
  obtain ⟨D, D', hD, hD', -, -, ⟨e⟩⟩ :=
    InvertibleSheafGeneral.exists_effectiveCartierDivisors_tensor_invertibleSheaf L hL M
      (E := (∅ : Set C)) Set.finite_empty
  haveI := hD
  haveI := hD'
  haveI hA : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
    (Stacks.Divisors.invertibleSheaf' D) := Stacks.Divisors.invertibleSheaf_isInvertible D
  haveI hB : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
    (Stacks.Divisors.invertibleSheaf' D') := Stacks.Divisors.invertibleSheaf_isInvertible D'
  haveI hT : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      (Scheme.Modules.tensorObj M (Stacks.Divisors.invertibleSheaf' D')) :=
    Stacks.Chow.isInvertible_tensorObj _ _
  haveI hT2 : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨C.toRingedSpace.presheaf,
        C.toRingedSpace.IsSheaf⟩).obj M).obj (Stacks.Divisors.invertibleSheaf' D')) := hT
  haveI hT3 : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨C.presheaf,
        C.IsSheaf⟩).obj M).obj (Stacks.Divisors.invertibleSheaf' D')) := hT
  have e' : Scheme.Modules.tensorObj M (Stacks.Divisors.invertibleSheaf' D') ≅
      Stacks.Divisors.invertibleSheaf' D :=
    (Stacks.SheafOfModules.tensorObjIso C.sheaf.obj C.ringCatSheaf.property M
      (Stacks.Divisors.invertibleSheaf' D')).symm ≪≫ e
  have hAeq := hsec (Stacks.Divisors.invertibleSheaf' D) (Stacks.Divisors.canonicalSections D)
    (canonicalSections_eval_top_ne_zero D ‹_›)
  have hBeq := hsec (Stacks.Divisors.invertibleSheaf' D') (Stacks.Divisors.canonicalSections D')
    (canonicalSections_eval_top_ne_zero D' ‹_›)
  have hdeg := invertibleCurveDegree_tensorSheaf_eq_add ℂ (C ↘ Spec (.of ℂ)) hdim M
    (Stacks.Divisors.invertibleSheaf' D')
  have hdegiso := invertibleCurveDegree_eq_of_iso ℂ (C ↘ Spec (.of ℂ)) hdim e'
  have hch := algebraicFirstChernClass_sheafTensor M (Stacks.Divisors.invertibleSheaf' D')
  have hchiso := algebraicFirstChernClass_eq_of_iso e'
  have key : ψ ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
        (𝟙 (ComplexPoints.analyticSpace (C ↘ Spec (.of ℂ)))) (Set.empty_subset _) 2).hom
          (algebraicFirstChernClass (Scheme.Modules.tensorObj M
            (Stacks.Divisors.invertibleSheaf' D')))) =
      ψ ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
        (𝟙 (ComplexPoints.analyticSpace (C ↘ Spec (.of ℂ)))) (Set.empty_subset _) 2).hom
          (algebraicFirstChernClass M)) +
      ψ ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
        (𝟙 (ComplexPoints.analyticSpace (C ↘ Spec (.of ℂ)))) (Set.empty_subset _) 2).hom
          (algebraicFirstChernClass (Stacks.Divisors.invertibleSheaf' D'))) := by
    rw [← map_add, ← map_add]
    congr 2
  rw [hchiso, hAeq] at key
  have hdeg' : invertibleCurveDegree ℂ (C ↘ Spec (.of ℂ)) hdim
      (Scheme.Modules.tensorObj M (Stacks.Divisors.invertibleSheaf' D')) =
      invertibleCurveDegree ℂ (C ↘ Spec (.of ℂ)) hdim M +
        invertibleCurveDegree ℂ (C ↘ Spec (.of ℂ)) hdim (Stacks.Divisors.invertibleSheaf' D') :=
    hdeg
  omega

end Twist

private theorem topologicalKrullDim_eq_one {X : Type*} [TopologicalSpace X] [IrreducibleSpace X]
    [T0Space X] (h : topologicalKrullDim X ≤ 1) {a b : X} (hab : a ≠ b) :
    ((1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim X := by
  have hz : ∃ z : X, closure {z} ≠ Set.univ := by
    by_contra! H
    apply hab
    have h1 : a ⤳ b := specializes_iff_closure_subset.2 (by rw [H a, H b])
    have h2 : b ⤳ a := specializes_iff_closure_subset.2 (by rw [H a, H b])
    exact (h1.antisymm h2).eq
  obtain ⟨z, hz⟩ := hz
  have hlt : (⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ :
      TopologicalSpace.IrreducibleCloseds X) <
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ :=
    lt_of_le_of_ne (fun _ _ ↦ Set.mem_univ _) (fun he ↦ hz (congrArg (·.carrier) he))
  have hpos : 0 < topologicalKrullDim X := Order.krullDim_pos_iff.2 ⟨_, _, hlt⟩
  have h1 : (1 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
    obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.1 hpos.ne_bot
    rw [← hn] at hpos ⊢
    exact_mod_cast Order.one_le_iff_pos.2 (by exact_mod_cast hpos : (0 : ℕ∞) < n)
  exact le_antisymm (by exact_mod_cast h1) (by exact_mod_cast h)

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite Filter _root_.Topology TensorProduct
  Bundle
open MMP.Analytic MMP.Analytic.Analytification
open MMP.Intersection.Scheme (dimension)

/-- A class whose image in `ℚ ⊗[ℤ] M` vanishes is killed by every homomorphism `M →+ ℤ`. -/
private theorem apply_eq_zero_of_one_tmul_eq_zero {M : Type*} [AddCommGroup M] (φ : M →+ ℤ)
    {c : M} (h : (1 : ℚ) ⊗ₜ[ℤ] c = 0) : φ c = 0 := by
  simpa using congrArg (fun t => TensorProduct.rid ℤ ℚ (LinearMap.lTensor ℚ φ.toIntLinearMap t)) h

/-! ### Evaluation on the fundamental class of a curve -/

/-- On a proper integral complex curve `C` there is a homomorphism `H²(C(ℂ), ∅; ℤ) →+ ℤ`,
evaluation on the fundamental class, sending the first Chern class of every invertible
`𝒪_C`-module to its degree. -/
private theorem exists_curveEvaluation {C : Scheme.{0}} [C.Over (Spec (.of ℂ))] [IsComplexScheme C]
    [IsProper (C ↘ Spec (.of ℂ))] [IsIntegral C] (hC : topologicalKrullDim C ≤ 1)
    (hC1 : ((1 : ℕ) : WithBot ℕ∞) = dimension C) :
    ∃ ψ : relativeSingularCohomology ℤ (ModuleCat.of ℤ ℤ)
        (ComplexPoints.analyticSpace (C ↘ Spec (.of ℂ))) ∅ 2 →+ ℤ,
      ∀ (M : C.Modules) [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 M],
        ψ ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
            (𝟙 (ComplexPoints.analyticSpace (C ↘ Spec (.of ℂ)))) (Set.empty_subset _) 2).hom
          (algebraicFirstChernClass M)) = invertibleCurveDegree ℂ (C ↘ Spec (.of ℂ)) hC M :=
  ⟨curveEval hC1, fun M _ ↦ eq_invertibleCurveDegree_of_sections hC (curveEval hC1)
    (fun N _ σ hσ ↦ curveEval_eq_of_section hC1 hC N σ hσ) M⟩

public theorem solution {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjective sX) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    haveI := hX.isProper
    let J := Opens.grothendieckTopology (space sX)
    let O : Sheaf J AddCommGrpCat.{0} :=
      (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX)
    let Ou : Sheaf J AddCommGrpCat.{0} :=
      Stacks.Cohomology.Generators.unitsSheaf (analytification sX)
    let ZA : Sheaf J AddCommGrpCat.{0} :=
      (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
    ∀ (ι : ZA ⟶ O) (e : O ⟶ Ou) (w : ι ≫ e = 0) (hS : (ShortComplex.mk ι e w).ShortExact),
      (∀ (W : Opens (space sX)) (n : ℤ),
        (show (structureSheaf sX).obj.obj (op W) from ι.hom.app (op W)
          ((toSheafify J ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op W) n)) = n) →
      (∀ (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W)
        (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) (f : (Fin c.1.n → ℂ) → ℂ)
        (g g' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
        (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = f →
        (g' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
          (fun z => Complex.exp (2 * Real.pi * Complex.I * f z)) →
        s.1 x c = Chart.StalkRing.mk c.1 _ g →
        ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf sX).obj.obj (op W))ˣ) :
          (structureSheaf sX).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ g') →
      (∀ hLan : Stacks.SheafOfModules.IsInvertible _ _ ((analytifyModule sX).obj L),
        (1 : ℚ) ⊗ₜ[ℤ] picardObstruction (analytification sX) hS
          (Stacks.SheafOfModules.Picard.classOf _ _ ((analytifyModule sX).obj L) hLan) = 0) →
      ∀ (C : Scheme.{0}) (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C]
        [IsProper (i ≫ sX)] (hC : topologicalKrullDim C ≤ 1),
        MMP.Mori.degreeOn ℂ sX i hC L = 0 := by
  haveI := hX.isProper
  intro J O Ou ZA ι e w hS hι he hvan C i _ _ _ hC
  -- A curve mapped to a point has degree zero.
  by_cases hpt : ∃ y : X, ∀ z : C, i.base z = y
  · obtain ⟨y, hy⟩ := hpt
    exact invertibleCurveDegree_pullback_eq_zero_of_forall_eq ℂ (i ≫ sX) hC i L y hy
  -- Otherwise `C` has two distinct points, so it is a curve.
  have hC1 : ((1 : ℕ) : WithBot ℕ∞) = dimension C := by
    obtain ⟨z₀⟩ : Nonempty C := inferInstance
    push Not at hpt
    obtain ⟨z₁, hz₁⟩ := hpt (i.base z₀)
    exact topologicalKrullDim_eq_one hC (a := z₁) (b := z₀) (fun h ↦ hz₁ (h ▸ rfl))
  -- `L^an` is invertible: the analytification of an invertible module.
  have hLan : Stacks.SheafOfModules.IsInvertible _ _ ((analytifyModule sX).obj L) :=
    @Stacks.InvertiblePullback.isInvertible_pullback _ _ (analytificationHom sX) L ‹_›
  -- `c_exp(L^an)` is `ε c₁(L)` under the comparison `Φ`.
  obtain ⟨Φ, ε, hΦ⟩ := exists_addEquiv_picardObstruction_eq_firstChernClass
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := (inferInstance : LocallyOfFiniteType sX)
  obtain ⟨val, h1, h2, h3, h4, h5⟩ := exists_val (X := X) L
  have hXp : IsProjectiveMorphism (X ↘ Spec (.of ℂ)) :=
    isProjectiveMorphism_of_isProjective_of_isAffine sX hX
  have key := hΦ (X ↘ Spec (.of ℂ)) hXp ι e w hS hι he _ hLan _ val h1 h2 h3 h4 h5
  -- `X` and `C` are complex schemes.
  haveI : IsComplexScheme X := MMP.Analytic.isComplexScheme_of_isProjective X hX
  letI : C.Over (Spec (.of ℂ)) := ⟨i ≫ sX⟩
  haveI : i.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : IsComplexScheme C := IsComplexScheme.of_isClosedImmersion i
  haveI : IsProper (C ↘ Spec (.of ℂ)) := ‹IsProper (i ≫ sX)›
  -- Evaluation on the fundamental class of `C`.
  obtain ⟨ψ, hψ⟩ := exists_curveEvaluation (C := C) hC hC1
  let g := MMP.Analytic.ComplexPoints.analyticMap i (sX := C ↘ Spec (.of ℂ))
    (sY := X ↘ Spec (.of ℂ)) rfl
  let φ : _ →+ ℤ := (ψ.comp (relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) g
    (A' := ∅) (A := ∅) (Set.empty_subset _) 2).hom.toAddMonoidHom).comp
      (Φ (X ↘ Spec (.of ℂ)) hXp).toAddMonoidHom
  have h0 := apply_eq_zero_of_one_tmul_eq_zero φ (hvan hLan)
  have hpull := algebraicFirstChernClass_pullback i g (fun _ ↦ rfl) L
  have hφ : φ (picardObstruction (analytification sX) hS
      (Stacks.SheafOfModules.Picard.classOf _ _ ((analytifyModule sX).obj L) hLan)) =
        (ε : ℤ) * MMP.Mori.degreeOn ℂ sX i hC L := by
    have hc : ∀ x, (relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) g (A' := ∅) (A := ∅)
        (Set.empty_subset _) 2).hom
        ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
          (𝟙 (MMP.Analytic.ComplexPoints.analyticSpace (X ↘ Spec (.of ℂ))))
          (A' := ∅) (A := Set.univᶜ) (Set.empty_subset _) 2).hom x) =
        (relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
          (𝟙 (MMP.Analytic.ComplexPoints.analyticSpace (C ↘ Spec (.of ℂ))))
          (A' := ∅) (A := Set.univᶜ) (Set.empty_subset _) 2).hom
        ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) g (A' := Set.univᶜ)
          (A := Set.univᶜ) (fun _ hx ↦ (hx (Set.mem_univ _)).elim) 2).hom x) := by
      intro x
      rw [← relativeSingularCohomology.map_comp_apply' ℤ _ _ (Set.empty_subset _)]
      exact (relativeSingularCohomology.map_congr_apply ℤ (by simp) _ _ _ x).trans
        (relativeSingularCohomology.map_comp_apply' ℤ _ _ (Set.empty_subset _) _ x)
    change ψ ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) g (A' := ∅) (A := ∅)
      (Set.empty_subset _) 2).hom ((Φ (X ↘ Spec (.of ℂ)) hXp) _)) = _
    erw [key]
    rw [Units.smul_def, map_zsmul, map_zsmul, hc]
    erw [← hpull]
    erw [hψ ((Scheme.Modules.pullback i).obj L)]
    rfl
  rw [hφ] at h0
  exact (mul_eq_zero.mp h0).resolve_left ε.ne_zero

end MMP.FourfoldProofs.LogObstructionProof

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite Filter Topology TensorProduct
open MMP.Analytic.Analytification

namespace MMP.Analytic

/-- **A rationally zero logarithmic obstruction has zero curve degrees.** Let `X` be projective
over `ℂ` (structure morphism `sX`) and `L` an invertible `𝒪_X`-module. Let
`0 ⟶ ℤ_A ⟶ 𝒪_A ⟶ 𝒪_A^× ⟶ 0` be the exponential sequence on `A = X^an`, and suppose the
obstruction `MMP.Analytic.picardObstruction` of the class of `L^an` is zero in
`ℚ ⊗[ℤ] H²(A, ℤ_A)`. Then `MMP.Mori.degreeOn ℂ sX i hC L = 0` for every closed immersion
`i : C ⟶ X` of an integral scheme `C` of dimension at most one. -/
@[mmp "lem_mmp_log_obstruction_zero_curve_degrees"]
public theorem degreeOn_eq_zero_of_tmul_picardObstruction_eq_zero {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjective sX) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    haveI := hX.isProper
    let E := exists_shortExact_exponentialSequence sX
    (∀ hLan : Stacks.SheafOfModules.IsInvertible _ _ ((analytifyModule sX).obj L),
      (1 : ℚ) ⊗ₜ[ℤ] picardObstruction (analytification sX) E.choose_spec.choose_spec.choose_spec.1
        (Stacks.SheafOfModules.Picard.classOf _ _ ((analytifyModule sX).obj L) hLan) = 0) →
      ∀ (C : Scheme.{0}) (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C]
        [IsProper (i ≫ sX)] (hC : topologicalKrullDim C ≤ 1),
        MMP.Mori.degreeOn ℂ sX i hC L = 0 := by
  haveI := hX.isProper
  intro E hobs
  obtain ⟨hS, hι, he⟩ := E.choose_spec.choose_spec.choose_spec
  exact MMP.FourfoldProofs.LogObstructionProof.solution sX hX L _ _ _ hS hι he hobs

end MMP.Analytic
