module

import MMP.AlgebraicGeometry.SpecOverSpecSelf
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import MMP.AlgebraicTopology.ConstantSheafSingularCohomology
import MMP.Topology.Sheaves.GodementFlasqueResolution
public import MMP.AlgebraicGeometry.Analytic.ComplexScheme.OfProjective
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CocycleFormula

/-!
# Singular and constant-sheaf cohomology of projective complex schemes

For a projective scheme `X` over `ℂ` with complex realization `X^an` and an abelian group `A`,
the cohomology `H^n(X^an, A_{X^an})` of the constant sheaf agrees with the singular cohomology
`H^n_sing(X^an; A)`, and the isomorphisms can be chosen compatibly with pullback along every
morphism of projective schemes over `ℂ`.

## Main definitions

* `MMP.Analytic.constPullbackComparison`: the canonical map `M_Z ⟶ f⁻¹ M_W` of constant sheaves
  along a continuous map `f : Z ⟶ W`.
* `MMP.Analytic.pullbackConstComparison`: the canonical map `f⁻¹ M_W ⟶ M_Z`, inverse to
  `MMP.Analytic.constPullbackComparison` (`MMP.Analytic.isIso_constPullbackComparison`).

## Main results

* `MMP.Analytic.exists_addEquiv_sheafH_constantSheaf_singularCohomology`: a family of
  isomorphisms `H^n(X^an, A) ≃+ H^n_sing(X^an; A)`, natural for pullback along morphisms of
  projective complex schemes.
* `MMP.Analytic.exists_addEquiv_sheafH_constantSheaf_singularCohomology_ring`: for a commutative
  ring `R`, isomorphisms `H^n(X^an, R) ≃+ H^n_sing(X^an; R)` onto the `R`-module of singular
  cohomology with coefficients in `R`, which are `R`-linear and natural for pullback.

## Implementation notes

Sheaf cohomology is `CategoryTheory.Sheaf.H`, i.e. `Ext^n(ℤ_{X^an}, A_{X^an})` in abelian
sheaves on `X^an`, and singular cohomology is
`MMP.relativeSingularCohomology ℤ A (X^an) ∅ n`. The pullback of a class
`e ∈ Ext^n(ℤ_Y, A_Y)` along a continuous `f : Z → W` is its image under the exact functor
`f⁻¹`, which lands in `Ext^n(f⁻¹ ℤ_W, f⁻¹ A_W)`. It is compared with `Ext^n(ℤ_Z, A_Z)`
through the canonical maps `α_M : M_Z ⟶ f⁻¹ M_W`, adjoint to the composite of
`M → Γ(W, M_W)` and the unit `M_W ⟶ f_* f⁻¹ M_W` on global sections. Compatibility with
pullback is therefore stated as an identity in `Ext^n(ℤ_Z, f⁻¹ A_W)`, which does not need
inverses of the `α_M`.

Singular cochains with coefficients in an `R`-module `A`, whether `R`-linear on `C_•(M; R)` or
additive on `C_•(M; ℤ)`, are the same as functions from singular simplices to `A`; this
identifies the two cochain complexes, compatibly with the action of `R` on `A`.

## References

* [Bredon, *Sheaf theory*], III.1.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace Abelian Topology
open MMP.Analytic.ComplexPoints MMP MMP.Mori AlgebraicTopology Simplicial

namespace MMP.Analytic

attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax
attribute [local instance] MMP.Analytic.globalSections_additive

/-- A topological space is *metrizable and locally contractible* when it is metrizable and every
point has a basis of contractible open neighbourhoods. -/
private def IsMetrizableLocallyContractible (M : TopCat.{0}) : Prop :=
  MetrizableSpace M ∧
    ∀ p : M, (𝓝 p).HasBasis (fun V : Set M ↦ IsOpen V ∧ p ∈ V ∧ ContractibleSpace V) id

private theorem IsMetrizableLocallyContractible.locallyContractibleSpace {M : TopCat.{0}}
    (hM : IsMetrizableLocallyContractible M) : LocallyContractibleSpace M := by
  haveI : StronglyLocallyContractibleSpace M :=
    ⟨fun p ↦ (hM.2 p).to_hasBasis (fun V ⟨hVo, hpV, hV⟩ ↦ ⟨V, ⟨hVo.mem_nhds hpV, hV⟩, le_rfl⟩)
      (fun V ⟨hV, _⟩ ↦ by
        obtain ⟨W, ⟨hWo, hpW, hW⟩, hWV⟩ := (hM.2 p).mem_iff.1 hV
        exact ⟨W, ⟨hWo, hpW, hW⟩, hWV⟩)⟩
  exact StronglyLocallyContractibleSpace.locallyContractible

/-- The canonical comparison `M_Z ⟶ f⁻¹ M_W` of constant sheaves along a continuous map `f`:
the adjoint of the composite of `M → Γ(W, M_W)` and the unit `M_W ⟶ f_* f⁻¹ M_W` on global
sections. -/
@[expose] public noncomputable def constPullbackComparison {Z W : TopCat.{0}} (f : Z ⟶ W)
    (M : AddCommGrpCat.{0}) :
    (constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{0}).obj M ⟶
      (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj
        ((constantSheaf (Opens.grothendieckTopology W) AddCommGrpCat.{0}).obj M) :=
  ((constantSheafAdj _ _ isTerminalTop).homEquiv _ _).symm
    ((constantSheafAdj _ _ isTerminalTop).unit.app M ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app
        ((constantSheaf _ _).obj M)).hom.app (op ⊤))

/-- The defining property of `constPullbackComparison`: its adjoint under `constantSheafAdj`. -/
public theorem homEquiv_constPullbackComparison {Z W : TopCat.{0}} (f : Z ⟶ W)
    (M : AddCommGrpCat.{0}) :
    (constantSheafAdj _ _ isTerminalTop).homEquiv _ _ (constPullbackComparison f M) =
      (constantSheafAdj _ _ isTerminalTop).unit.app M ≫
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app
          ((constantSheaf _ _).obj M)).hom.app (op ⊤) :=
  Equiv.apply_symm_apply _ _

/-- The canonical comparison `f⁻¹ M_W ⟶ M_Z`, as in
`MMP.Analytic.exists_sheafCohomology_constantSheaf_iso_singularCohomology`. -/
public noncomputable def pullbackConstComparison {Z W : TopCat.{0}} (f : Z ⟶ W)
    (M : AddCommGrpCat.{0}) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj
        ((constantSheaf (Opens.grothendieckTopology W) AddCommGrpCat.{0}).obj M) ⟶
      (constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{0}).obj M :=
  (((constantSheafAdj (Opens.grothendieckTopology W) AddCommGrpCat.{0}
      Limits.isTerminalTop).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f)).homEquiv
      M ((constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{0}).obj M)).symm
    ((constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{0}
        Limits.isTerminalTop).unit.app M ≫
      ((constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{0}).obj M).obj.map
        (homOfLE le_top).op)

/-- The two comparisons of constant sheaves along `f` compose to the identity of `f⁻¹ M_W`. -/
public theorem pullbackConstComparison_comp_constPullbackComparison {Z W : TopCat.{0}}
    (f : Z ⟶ W) (M : AddCommGrpCat.{0}) :
    pullbackConstComparison f M ≫ constPullbackComparison f M = 𝟙 _ := by
  apply (((constantSheafAdj (Opens.grothendieckTopology W) AddCommGrpCat.{0} isTerminalTop).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f)).homEquiv M _).injective
  erw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_id]
  erw [Equiv.apply_symm_apply]
  erw [Adjunction.comp_unit_app]
  have h1 : (homOfLE (le_top : (Opens.map f).obj (⊤ : Opens W) ≤ ⊤)).op =
      𝟙 (op (⊤ : Opens Z)) := rfl
  erw [h1, CategoryTheory.Functor.map_id, Category.comp_id]
  change (constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{0}
      isTerminalTop).unit.app M ≫
    ((sheafSections (Opens.grothendieckTopology Z) AddCommGrpCat.{0}).obj (op ⊤)).map
      (constPullbackComparison f M) = _
  refine ((constantSheafAdj _ _ isTerminalTop).homEquiv_unit M _
    (constPullbackComparison f M)).symm.trans ?_
  rw [homEquiv_constPullbackComparison]
  exact (Adjunction.comp_unit_app _ _ _).symm

/-- The two comparisons of constant sheaves along `f` compose to the identity of `M_Z`. -/
public theorem constPullbackComparison_comp_pullbackConstComparison {Z W : TopCat.{0}}
    (f : Z ⟶ W) (M : AddCommGrpCat.{0}) :
    constPullbackComparison f M ≫ pullbackConstComparison f M = 𝟙 _ := by
  apply ((constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{0}
    isTerminalTop).homEquiv M _).injective
  erw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_id]
  have hβ := ((constantSheafAdj (Opens.grothendieckTopology W) AddCommGrpCat.{0}
    isTerminalTop).comp (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0}
      f)).homEquiv_unit (f := pullbackConstComparison f M)
  have hβ' : ((constantSheafAdj (Opens.grothendieckTopology W) AddCommGrpCat.{0}
      isTerminalTop).comp (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0}
        f)).homEquiv M _ (pullbackConstComparison f M) =
      (constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{0}
        isTerminalTop).unit.app M ≫
      ((constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{0}).obj M).obj.map
        (homOfLE le_top).op :=
    Equiv.apply_symm_apply _ _
  have h1 : (homOfLE (le_top : (Opens.map f).obj (⊤ : Opens W) ≤ ⊤)).op =
      𝟙 (op (⊤ : Opens Z)) := rfl
  erw [hβ', h1, CategoryTheory.Functor.map_id, Category.comp_id, Adjunction.comp_unit_app] at hβ
  erw [homEquiv_constPullbackComparison]
  exact hβ.symm

/-- The comparison `M_Z ⟶ f⁻¹ M_W` is an isomorphism, with inverse `pullbackConstComparison`. -/
public instance isIso_constPullbackComparison {Z W : TopCat.{0}} (f : Z ⟶ W)
    (M : AddCommGrpCat.{0}) : IsIso (constPullbackComparison f M) :=
  ⟨⟨pullbackConstComparison f M, constPullbackComparison_comp_pullbackConstComparison f M,
    pullbackConstComparison_comp_constPullbackComparison f M⟩⟩

/-- Composition with the comparison `M_Z ⟶ f⁻¹ M_W` is injective on `Ext` classes. -/
private theorem comp_mk₀_constPullbackComparison_injective {Z W : TopCat.{0}} (f : Z ⟶ W)
    (M : AddCommGrpCat.{0}) {F : TopCat.Sheaf AddCommGrpCat.{0} Z} {n : ℕ} :
    Function.Injective fun y : Ext F ((constantSheaf (Opens.grothendieckTopology Z)
        AddCommGrpCat.{0}).obj M) n ↦
      y.comp (Ext.mk₀ (constPullbackComparison f M)) (add_zero n) := by
  have e (z : Ext F ((constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{0}).obj M) n) :
      (z.comp (Ext.mk₀ (constPullbackComparison f M)) (add_zero n)).comp
        (Ext.mk₀ (pullbackConstComparison f M)) (add_zero n) = z := by
    erw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      constPullbackComparison_comp_pullbackConstComparison, Ext.comp_mk₀_id]
  intro y y' h
  exact (e y).symm.trans ((congrArg (fun z ↦ z.comp (Ext.mk₀ (pullbackConstComparison f M))
    (add_zero n)) h).trans (e y'))

noncomputable section ExtGodement

private instance instPFLGlobalSections (S : TopCat.{0}) :
    PreservesFiniteLimits (MMP.Analytic.globalSections S) :=
  inferInstanceAs (PreservesFiniteLimits
    ((sheafSections (Opens.grothendieckTopology S) AddCommGrpCat.{0}).obj (op ⊤)))

/-- The constant sheaf `ℤ_S`. -/
private def zS (S : TopCat.{0}) : TopCat.Sheaf AddCommGrpCat.{0} S :=
  (constantSheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0}).obj (.of (ULift ℤ))

/-- The unit section `1 ∈ Γ(S, ℤ_S)`. -/
private def oneSec (S : TopCat.{0}) : (MMP.Analytic.globalSections S).obj (zS S) :=
  (constantSheafAdj (Opens.grothendieckTopology S) AddCommGrpCat.{0} isTerminalTop).unit.app
    (AddCommGrpCat.of (ULift ℤ)) (ULift.up 1)

/-- Evaluation at the unit section: `Hom(ℤ_S, G) ≃+ Γ(S, G)`. -/
private def evalOne (S : TopCat.{0}) (G : TopCat.Sheaf AddCommGrpCat.{0} S) :
    (zS S ⟶ G) ≃+ (MMP.Analytic.globalSections S).obj G where
  toFun t := (MMP.Analytic.globalSections S).map t (oneSec S)
  invFun s := ((constantSheafAdj (Opens.grothendieckTopology S) AddCommGrpCat.{0}
    isTerminalTop).homEquiv _ G).symm ((AddCommGrpCat.uliftZMultiplesAddEquiv _).symm s)
  left_inv t := by
    apply ((constantSheafAdj (Opens.grothendieckTopology S) AddCommGrpCat.{0}
      isTerminalTop).homEquiv _ G).injective
    rw [Equiv.apply_symm_apply]
    apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
    rw [AddEquiv.apply_symm_apply]
    exact (ConcreteCategory.congr_hom (Adjunction.homEquiv_unit _ _ _ t) (ULift.up (1 : ℤ))).symm
  right_inv s := by
    change (MMP.Analytic.globalSections S).map _ (oneSec S) = s
    have h := Adjunction.homEquiv_unit (constantSheafAdj (Opens.grothendieckTopology S)
      AddCommGrpCat.{0} isTerminalTop) (X := AddCommGrpCat.of (ULift ℤ)) (Y := G)
      (((constantSheafAdj (Opens.grothendieckTopology S) AddCommGrpCat.{0}
        isTerminalTop).homEquiv _ G).symm ((AddCommGrpCat.uliftZMultiplesAddEquiv _).symm s))
    rw [Equiv.apply_symm_apply] at h
    have h2 := congrArg (fun φ => (ConcreteCategory.hom φ) (ULift.up (1 : ℤ))) h
    exact h2.symm.trans ((AddCommGrpCat.uliftZMultiplesAddEquiv _).apply_symm_apply s)
  map_add' t t' := by
    change (MMP.Analytic.globalSections S).map (t + t') (oneSec S) = _
    rw [Functor.map_add]
    rfl

/-- `Γ(S, -)` is corepresented by `ℤ_S`. -/
private def corep (S : TopCat.{0}) :
    MMP.Analytic.globalSections S ≅ preadditiveCoyoneda.obj (op (zS S)) :=
  (NatIso.ofComponents (fun G => (evalOne S G).toAddCommGrpIso) (by
    intro G G' a
    ext t
    change (MMP.Analytic.globalSections S).map (t ≫ a) (oneSec S) =
      (MMP.Analytic.globalSections S).map a ((MMP.Analytic.globalSections S).map t (oneSec S))
    exact ConcreteCategory.congr_hom
      ((MMP.Analytic.globalSections S).map_comp (t : zS S ⟶ G) a) (oneSec S))).symm

private lemma corep_inv_app_apply (S : TopCat.{0}) (G : TopCat.Sheaf AddCommGrpCat.{0} S)
    (t : zS S ⟶ G) :
    (corep S).inv.app G t = (MMP.Analytic.globalSections S).map t (oneSec S) := rfl

private abbrev psi (S : TopCat.{0}) (n : ℕ) :=
  ModuleSheafCohomology.extFunctorObjIsoRightDerived (MMP.Analytic.globalSections S) (zS S)
    (corep S) n

/-- `constPullbackComparison` at `ℤ`, typed with `zS`. -/
private def alphaZ {Z W : TopCat.{0}} (f : Z ⟶ W) :
    zS Z ⟶ (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj (zS W) :=
  constPullbackComparison f (AddCommGrpCat.of (ULift ℤ))

private lemma globalSections_map_constPullbackComparison_oneSec {Z W : TopCat.{0}} (f : Z ⟶ W) :
    (MMP.Analytic.globalSections Z).map (alphaZ f) (oneSec Z) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app
        (zS W)).hom.app (op ⊤) (oneSec W) := by
  have h := (constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{0}
    isTerminalTop).homEquiv_unit (f := alphaZ f)
  have h' : (constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{0}
      isTerminalTop).homEquiv _ _ (alphaZ f) =
      (constantSheafAdj _ _ isTerminalTop).unit.app (AddCommGrpCat.of (ULift ℤ)) ≫
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app
          (zS W)).hom.app (op ⊤) :=
    homEquiv_constPullbackComparison f _
  exact (ConcreteCategory.congr_hom (h.symm.trans h') (ULift.up (1 : ℤ)))

/-- The adjunction identity `Γ(α ≫ f⁻¹ t ≫ ψ)(1) = Γ(η ≫ f_* ψ)(Γ(t)(1))` on unit sections. -/
private lemma key_section {Z W : TopCat.{0}} (f : Z ⟶ W) {I : TopCat.Sheaf AddCommGrpCat.{0} W}
    {I' : TopCat.Sheaf AddCommGrpCat.{0} Z} (t : zS W ⟶ I)
    (ψ : (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj I ⟶ I') :
    (MMP.Analytic.globalSections Z).map
        (alphaZ f ≫
          (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map t ≫ ψ) (oneSec Z) =
      (MMP.Analytic.globalSections W).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app I ≫
          (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map ψ)
        ((MMP.Analytic.globalSections W).map t (oneSec W)) := by
  have hn := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.naturality t
  have hD : (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app (zS W) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map t ≫ ψ) =
      t ≫ (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app I ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map ψ := by
    rw [Functor.map_comp, ← Category.assoc]
    exact congrArg (· ≫ _) hn.symm
  have e1 := ConcreteCategory.congr_hom ((MMP.Analytic.globalSections W).map_comp t
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app I ≫
          (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map ψ)) (oneSec W)
  have eA := ConcreteCategory.congr_hom ((MMP.Analytic.globalSections Z).map_comp
    (alphaZ f)
    ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map t ≫ ψ)) (oneSec Z)
  have eC := ConcreteCategory.congr_hom ((MMP.Analytic.globalSections W).map_comp
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app (zS W))
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map t ≫ ψ))) (oneSec W)
  rw [ConcreteCategory.comp_apply] at eA eC e1
  refine eA.trans ?_
  rw [globalSections_map_constPullbackComparison_oneSec]
  refine eC.symm.trans ?_
  rw [hD]
  exact e1

private def tau (S : TopCat.{0}) (F : TopCat.Sheaf AddCommGrpCat.{0} S) (n : ℕ) :
    (Abelian.extFunctorObj (zS S) n).obj F ≃+ (MMP.Analytic.sheafCohomology S n).obj F :=
  ((psi S n).app F ≪≫ (MMP.Analytic.sheafCohomologyIso S n).symm.app F).addCommGroupIsoToAddEquiv

private lemma tau_naturality (S : TopCat.{0}) {F G : TopCat.Sheaf AddCommGrpCat.{0} S} (a : F ⟶ G)
    (n : ℕ) (x : (Abelian.extFunctorObj (zS S) n).obj F) :
    tau S G n ((Abelian.extFunctorObj (zS S) n).map a x) =
      (MMP.Analytic.sheafCohomology S n).map a (tau S F n x) := by
  have h : (Abelian.extFunctorObj (zS S) n).map a ≫ ((psi S n).app G ≪≫
      (MMP.Analytic.sheafCohomologyIso S n).symm.app G).hom =
      ((psi S n).app F ≪≫ (MMP.Analytic.sheafCohomologyIso S n).symm.app F).hom ≫
        (MMP.Analytic.sheafCohomology S n).map a := by
    simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom]
    rw [← Category.assoc, (psi S n).hom.naturality a, Category.assoc,
      (MMP.Analytic.sheafCohomologyIso S n).inv.naturality a, Category.assoc]
  exact ConcreteCategory.congr_hom h x

section Generic

variable {C : Type*} [Category C]

private lemma reassemble {K K' B1 B2 Cy' H' R' A1 A2 Cy H R : C} (o : K ⟶ K') (y1 : K' ⟶ B1)
    (y2 : B1 ⟶ B2) (y3 : B2 ⟶ Cy') (pZ : Cy' ⟶ H') (iZ : H' ⟶ R')
    (x1 : K ⟶ A1) (x2 : A1 ⟶ A2) (x3 : A2 ⟶ Cy) (cg : Cy ⟶ Cy') (pW : Cy ⟶ H) (e : R ≅ H)
    (hm : H ⟶ H')
    (h4 : o ≫ y1 ≫ y2 ≫ y3 = x1 ≫ x2 ≫ x3 ≫ cg) (hnat : pW ≫ hm = cg ≫ pZ) :
    o ≫ y1 ≫ y2 ≫ y3 ≫ pZ ≫ iZ = (x1 ≫ x2 ≫ x3 ≫ pW ≫ e.inv) ≫ e.hom ≫ hm ≫ iZ := by
  have h4' := h4 =≫ (pZ ≫ iZ)
  simp only [Category.assoc] at h4'
  rw [h4']
  simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hnat]

end Generic

section Pull

variable {Z W : TopCat.{0}} (f : Z ⟶ W) (F : TopCat.Sheaf AddCommGrpCat.{0} W)

private abbrev PB := TopCat.Sheaf.pullback AddCommGrpCat.{0} f
private abbrev PF := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f
private abbrev adjPP := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f

private lemma exists_phi : ∃ φ : ((PB f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution F).cocomplex ⟶ (injectiveResolution ((PB f).obj F)).cocomplex,
      (PB f).map ((injectiveResolution F).ι.f 0) ≫ φ.f 0 =
        (injectiveResolution ((PB f).obj F)).ι.f 0 :=
  Stacks.Cohomology.ModuleComparison.exists_mapResolutionComparison (PB f) _ _

private def phi := (exists_phi f F).choose
private lemma phi_spec : (PB f).map ((injectiveResolution F).ι.f 0) ≫ (phi f F).f 0 =
    (injectiveResolution ((PB f).obj F)).ι.f 0 := (exists_phi f F).choose_spec

/-- The adjunct of `phi`, a map of complexes `J ⟶ f_* J'`. -/
private def gmap : (injectiveResolution F).cocomplex ⟶ ((PF f).mapHomologicalComplex _).obj
    (injectiveResolution ((PB f).obj F)).cocomplex where
  f k := (adjPP f).unit.app _ ≫ (PF f).map ((phi f F).f k)
  comm' i j _ := by
    dsimp only [Functor.mapHomologicalComplex_obj_d]
    rw [Category.assoc, ← (PF f).map_comp, (phi f F).comm]
    simp only [Functor.mapHomologicalComplex_obj_d, Functor.map_comp]
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    exact ((adjPP f).unit.naturality _).symm

private lemma gmap_f (k : ℕ) :
    (gmap f F).f k = (adjPP f).unit.app _ ≫ (PF f).map ((phi f F).f k) := rfl

/-- `Γ(W, gmap)`, read as a map `Γ(W, J) ⟶ Γ(Z, J')`. -/
private def gZ : ((MMP.Analytic.globalSections W).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution F).cocomplex ⟶
    ((MMP.Analytic.globalSections Z).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution ((PB f).obj F)).cocomplex :=
  ((MMP.Analytic.globalSections W).mapHomologicalComplex (ComplexShape.up ℕ)).map (gmap f F)

private lemma i_level (k : ℕ) :
    AddCommGrpCat.ofHom (Stacks.Cohomology.ModuleComparison.extCocycleComp (PB f)
        (injectiveResolution F) (injectiveResolution ((PB f).obj F)) (phi f F)
        (alphaZ f) k) ≫
      (ModuleSheafCohomology.extLeftHomologyData (injectiveResolution ((PB f).obj F)) (zS Z) k).i ≫
        (corep Z).inv.app ((injectiveResolution ((PB f).obj F)).cocomplex.X (k + 1)) =
    (ModuleSheafCohomology.extLeftHomologyData (injectiveResolution F) (zS W) k).i ≫
      (corep W).inv.app ((injectiveResolution F).cocomplex.X (k + 1)) ≫
        (MMP.Analytic.globalSections W).map ((gmap f F).f (k + 1)) := by
  ext t
  exact key_section f t.val ((phi f F).f (k + 1))

open ModuleSheafCohomology Stacks.Cohomology.ModuleComparison in
private lemma cycles_level (k : ℕ) (hi : (ComplexShape.up ℕ).prev (k + 1) = k)
    (hk : (ComplexShape.up ℕ).next (k + 1) = k + 2) :
    AddCommGrpCat.ofHom (extCocycleComp (PB f)
        (injectiveResolution F) (injectiveResolution ((PB f).obj F)) (phi f F)
        (alphaZ f) k) ≫
      ((extLeftHomologyData (injectiveResolution ((PB f).obj F)) (zS Z) k).cyclesIso.inv ≫
        ((((preadditiveCoyoneda.obj (op (zS Z))).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution ((PB f).obj F)).cocomplex).cyclesIsoSc' k (k + 1) (k + 2)
            hi hk).inv ≫
        HomologicalComplex.cyclesMap
          ((NatTrans.mapHomologicalComplex (corep Z).inv (ComplexShape.up ℕ)).app
            (injectiveResolution ((PB f).obj F)).cocomplex) (k + 1)) =
    (extLeftHomologyData (injectiveResolution F) (zS W) k).cyclesIso.inv ≫
      ((((preadditiveCoyoneda.obj (op (zS W))).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution F).cocomplex).cyclesIsoSc' k (k + 1) (k + 2) hi hk).inv ≫
      HomologicalComplex.cyclesMap
          ((NatTrans.mapHomologicalComplex (corep W).inv (ComplexShape.up ℕ)).app
            (injectiveResolution F).cocomplex) (k + 1) ≫
      HomologicalComplex.cyclesMap (gZ f F) (k + 1) :=
  extReadingMono _ _ _ ((((MMP.Analytic.globalSections Z).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (injectiveResolution ((PB f).obj F)).cocomplex).iCycles (k + 1)) _ _
    (extReadingCollapse3 _ _ _ _ _ _ _ _
      (HomologicalComplex.cyclesMap_i
        ((NatTrans.mapHomologicalComplex (corep Z).inv (ComplexShape.up ℕ)).app
          (injectiveResolution ((PB f).obj F)).cocomplex) (k + 1))
      (HomologicalComplex.cyclesIsoSc'_inv_iCycles _ k (k + 1) (k + 2) hi hk)
      (ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles
        (extLeftHomologyData (injectiveResolution ((PB f).obj F)) (zS Z) k)))
    (extReadingCollapse4 _ _ _ _ _ _ _ _ _ _ _
      (HomologicalComplex.cyclesMap_i (gZ f F) (k + 1))
      (HomologicalComplex.cyclesMap_i
        ((NatTrans.mapHomologicalComplex (corep W).inv (ComplexShape.up ℕ)).app
          (injectiveResolution F).cocomplex) (k + 1))
      (HomologicalComplex.cyclesIsoSc'_inv_iCycles _ k (k + 1) (k + 2) hi hk)
      (ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles
        (extLeftHomologyData (injectiveResolution F) (zS W) k)))
    (i_level f F k)

open ModuleSheafCohomology Stacks.Cohomology.ModuleComparison in
private lemma star_succ_π (k : ℕ) :
    ((extLeftHomologyData (injectiveResolution F) (zS W) k).π ≫
        (extMapComp (PB f) (alphaZ f) (k + 1)).app F) ≫
        (psi Z (k + 1)).hom.app ((PB f).obj F) =
      ((extLeftHomologyData (injectiveResolution F) (zS W) k).π ≫
        (extFunctorObjIsoRightDerived (MMP.Analytic.globalSections W) (zS W) (corep W)
          (k + 1)).hom.app F) ≫
        ((injectiveResolution F).isoRightDerivedObj (MMP.Analytic.globalSections W) (k + 1)).hom ≫
        HomologicalComplex.homologyMap (gZ f F) (k + 1) ≫
        ((injectiveResolution ((PB f).obj F)).isoRightDerivedObj
          (MMP.Analytic.globalSections Z) (k + 1)).inv := by
  have hi : (ComplexShape.up ℕ).prev (k + 1) = k := by simp
  have hk : (ComplexShape.up ℕ).next (k + 1) = k + 2 := by simp
  have h1 := extMapComp_π (PB f) (injectiveResolution F)
    (injectiveResolution ((PB f).obj F)) (phi f F) (phi_spec f F) (alphaZ f) k
  have h2 := extFunctorObjIsoRightDerived_succ_π_comp (MMP.Analytic.globalSections Z) (zS Z)
    (corep Z) ((PB f).obj F) k hi hk
  have h3 := extFunctorObjIsoRightDerived_succ_π_comp (MMP.Analytic.globalSections W) (zS W)
    (corep W) F k hi hk
  have h4 := cycles_level f F k hi hk
  have key := reassemble _ _ _ _ _
    ((injectiveResolution ((PB f).obj F)).isoRightDerivedObj
      (MMP.Analytic.globalSections Z) (k + 1)).inv _ _ _ _ _
    ((injectiveResolution F).isoRightDerivedObj (MMP.Analytic.globalSections W) (k + 1))
    (HomologicalComplex.homologyMap (gZ f F) (k + 1)) h4
    (HomologicalComplex.homologyπ_naturality (gZ f F) (k + 1))
  have step1 := congrArg (· ≫ (psi Z (k + 1)).hom.app ((PB f).obj F)) h1
  have step2 := (Category.assoc (AddCommGrpCat.ofHom (extCocycleComp (PB f)
    (injectiveResolution F) (injectiveResolution ((PB f).obj F)) (phi f F) (alphaZ f) k))
    (extLeftHomologyData (injectiveResolution ((PB f).obj F)) (zS Z) k).π
    ((psi Z (k + 1)).hom.app ((PB f).obj F))).trans
    (congrArg (AddCommGrpCat.ofHom (extCocycleComp (PB f)
    (injectiveResolution F) (injectiveResolution ((PB f).obj F)) (phi f F) (alphaZ f) k) ≫ ·) h2)
  have step3 := congrArg (· ≫ ((injectiveResolution F).isoRightDerivedObj
      (MMP.Analytic.globalSections W) (k + 1)).hom ≫
        HomologicalComplex.homologyMap (gZ f F) (k + 1) ≫
        ((injectiveResolution ((PB f).obj F)).isoRightDerivedObj
          (MMP.Analytic.globalSections Z) (k + 1)).inv) h3
  exact (step1.trans step2).trans (key.trans step3.symm)

open ModuleSheafCohomology Stacks.Cohomology.ModuleComparison in
private lemma star_succ (k : ℕ)
    (t : (AddCommGrpCat.Hom.hom (homShortComplex (injectiveResolution F) (zS W) k).g).ker) :
    (psi Z (k + 1)).hom.app ((PB f).obj F) ((extMapComp (PB f) (alphaZ f) (k + 1)).app F
        ((extLeftHomologyData (injectiveResolution F) (zS W) k).π t)) =
      (HomologicalComplex.homologyMap (gZ f F) (k + 1) ≫
        ((injectiveResolution ((PB f).obj F)).isoRightDerivedObj
          (MMP.Analytic.globalSections Z) (k + 1)).inv)
        (((injectiveResolution F).isoRightDerivedObj (MMP.Analytic.globalSections W) (k + 1)).hom
          ((extFunctorObjIsoRightDerived (MMP.Analytic.globalSections W) (zS W) (corep W)
            (k + 1)).hom.app F ((extLeftHomologyData (injectiveResolution F) (zS W) k).π t))) := by
  have h := ConcreteCategory.congr_hom (star_succ_π f F k) t
  have e1 := ConcreteCategory.comp_apply
    ((extLeftHomologyData (injectiveResolution F) (zS W) k).π ≫
        (extMapComp (PB f) (alphaZ f) (k + 1)).app F)
    ((psi Z (k + 1)).hom.app ((PB f).obj F)) t
  have e2 := ConcreteCategory.comp_apply
    (extLeftHomologyData (injectiveResolution F) (zS W) k).π
    ((extMapComp (PB f) (alphaZ f) (k + 1)).app F) t
  have e3 := ConcreteCategory.comp_apply
    ((extLeftHomologyData (injectiveResolution F) (zS W) k).π ≫
        (extFunctorObjIsoRightDerived (MMP.Analytic.globalSections W) (zS W) (corep W)
          (k + 1)).hom.app F)
    (((injectiveResolution F).isoRightDerivedObj (MMP.Analytic.globalSections W) (k + 1)).hom ≫
        HomologicalComplex.homologyMap (gZ f F) (k + 1) ≫
        ((injectiveResolution ((PB f).obj F)).isoRightDerivedObj
          (MMP.Analytic.globalSections Z) (k + 1)).inv) t
  have e4 := ConcreteCategory.comp_apply
    (extLeftHomologyData (injectiveResolution F) (zS W) k).π
    ((extFunctorObjIsoRightDerived (MMP.Analytic.globalSections W) (zS W) (corep W)
          (k + 1)).hom.app F) t
  rw [e1, e2, e3, e4, ConcreteCategory.comp_apply] at h
  exact h

private lemma cycles0 (h : zS W ⟶ F) :
    (injectiveResolution ((PB f).obj F)).toRightDerivedZero' (MMP.Analytic.globalSections Z)
        ((corep Z).inv.app ((PB f).obj F) (alphaZ f ≫ (PB f).map h)) =
      HomologicalComplex.cyclesMap (gZ f F) 0
        ((injectiveResolution F).toRightDerivedZero' (MMP.Analytic.globalSections W)
          ((corep W).inv.app F h)) := by
  apply (AddCommGrpCat.mono_iff_injective (HomologicalComplex.iCycles _ 0)).1 inferInstance
  have l1 := ConcreteCategory.congr_hom
    ((injectiveResolution ((PB f).obj F)).toRightDerivedZero'_comp_iCycles
    (MMP.Analytic.globalSections Z)) ((corep Z).inv.app ((PB f).obj F) (alphaZ f ≫ (PB f).map h))
  have l2 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (gZ f F) 0)
    ((injectiveResolution F).toRightDerivedZero' (MMP.Analytic.globalSections W)
          ((corep W).inv.app F h))
  have l3 := ConcreteCategory.congr_hom ((injectiveResolution F).toRightDerivedZero'_comp_iCycles
    (MMP.Analytic.globalSections W)) ((corep W).inv.app F h)
  rw [ConcreteCategory.comp_apply] at l1 l3
  have l2a := ConcreteCategory.comp_apply (HomologicalComplex.cyclesMap (gZ f F) 0)
    ((((MMP.Analytic.globalSections Z).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution ((PB f).obj F)).cocomplex).iCycles 0)
    ((injectiveResolution F).toRightDerivedZero' (MMP.Analytic.globalSections W)
          ((corep W).inv.app F h))
  have l2b := ConcreteCategory.comp_apply
    ((((MMP.Analytic.globalSections W).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution F).cocomplex).iCycles 0) ((gZ f F).f 0)
    ((injectiveResolution F).toRightDerivedZero' (MMP.Analytic.globalSections W)
          ((corep W).inv.app F h))
  rw [l2a, l2b] at l2
  rw [l1, l2, l3]
  have hk := key_section f (h ≫ (injectiveResolution F).ι.f 0) ((phi f F).f 0)
  have hm1 : alphaZ f ≫ (PB f).map (h ≫ (injectiveResolution F).ι.f 0) ≫ (phi f F).f 0 =
      (alphaZ f ≫ (PB f).map h) ≫ (injectiveResolution ((PB f).obj F)).ι.f 0 := by
    refine (congrArg (fun m => alphaZ f ≫ m ≫ (phi f F).f 0)
      ((PB f).map_comp h ((injectiveResolution F).ι.f 0))).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun m => alphaZ f ≫ (PB f).map h ≫ m) (phi_spec f F)).trans ?_
    exact (Category.assoc _ _ _).symm
  rw [hm1] at hk
  have a1 := ConcreteCategory.congr_hom ((MMP.Analytic.globalSections Z).map_comp
    (alphaZ f ≫ (PB f).map h) ((injectiveResolution ((PB f).obj F)).ι.f 0)) (oneSec Z)
  have a2 := ConcreteCategory.congr_hom ((MMP.Analytic.globalSections W).map_comp
    h ((injectiveResolution F).ι.f 0)) (oneSec W)
  rw [ConcreteCategory.comp_apply] at a1 a2
  rw [corep_inv_app_apply, corep_inv_app_apply]
  exact a1.symm.trans (hk.trans (congrArg (fun x => (gZ f F).f 0 x) a2))

private lemma psi_zero_mk₀ (S : TopCat.{0}) (G : TopCat.Sheaf AddCommGrpCat.{0} S) (c : zS S ⟶ G)
    (J : InjectiveResolution G) :
    (psi S 0).hom.app G (Ext.mk₀ c) =
      (J.isoRightDerivedObj (MMP.Analytic.globalSections S) 0).inv
        ((((MMP.Analytic.globalSections S).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          J.cocomplex).homologyπ 0
          (J.toRightDerivedZero' (MMP.Analytic.globalSections S) ((corep S).inv.app G c))) := by
  have e1 : (psi S 0).hom.app G (Ext.mk₀ c) =
      (MMP.Analytic.globalSections S).toRightDerivedZero.app G
        ((corep S).inv.app G (Ext.addEquiv₀ (Ext.mk₀ c))) := rfl
  rw [e1, show Ext.addEquiv₀ (Ext.mk₀ c) = c from Ext.addEquiv₀.right_inv c,
    J.toRightDerivedZero_eq (MMP.Analytic.globalSections S)]
  rfl

open Stacks.Cohomology.ModuleComparison in
private lemma star_zero (h : zS W ⟶ F) :
    (psi Z 0).hom.app ((PB f).obj F) ((extMapComp (PB f) (alphaZ f) 0).app F (Ext.mk₀ h)) =
      ((injectiveResolution ((PB f).obj F)).isoRightDerivedObj
          (MMP.Analytic.globalSections Z) 0).inv
        (HomologicalComplex.homologyMap (gZ f F) 0
        (((injectiveResolution F).isoRightDerivedObj (MMP.Analytic.globalSections W) 0).hom
          ((psi W 0).hom.app F (Ext.mk₀ h)))) := by
  have L1 : (extMapComp (PB f) (alphaZ f) 0).app F (Ext.mk₀ h) =
      Ext.mk₀ (alphaZ f ≫ (PB f).map h) := by
    change (Ext.mk₀ (alphaZ f)).comp ((Ext.mk₀ h).mapExactFunctor (PB f)) (zero_add 0) = _
    rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  rw [L1, psi_zero_mk₀ Z _ _ (injectiveResolution ((PB f).obj F)),
    psi_zero_mk₀ W _ _ (injectiveResolution F)]
  have ei := Iso.inv_hom_id_apply
    ((injectiveResolution F).isoRightDerivedObj (MMP.Analytic.globalSections W) 0)
    ((((MMP.Analytic.globalSections W).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution F).cocomplex).homologyπ 0
          ((injectiveResolution F).toRightDerivedZero' (MMP.Analytic.globalSections W)
            ((corep W).inv.app F h)))
  rw [ei, cycles0]
  have hn := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality (gZ f F) 0)
    ((injectiveResolution F).toRightDerivedZero' (MMP.Analytic.globalSections W)
          ((corep W).inv.app F h))
  have e6 := ConcreteCategory.comp_apply
    ((((MMP.Analytic.globalSections W).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution F).cocomplex).homologyπ 0)
    (HomologicalComplex.homologyMap (gZ f F) 0)
    ((injectiveResolution F).toRightDerivedZero' (MMP.Analytic.globalSections W)
          ((corep W).inv.app F h))
  have e7 := ConcreteCategory.comp_apply (HomologicalComplex.cyclesMap (gZ f F) 0)
    ((((MMP.Analytic.globalSections Z).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution ((PB f).obj F)).cocomplex).homologyπ 0)
    ((injectiveResolution F).toRightDerivedZero' (MMP.Analytic.globalSections W)
          ((corep W).inv.app F h))
  rw [e6, e7] at hn
  rw [hn]

private lemma gmap_hg : (injectiveResolution F).ι.f 0 ≫ (gmap f F).f 0 =
    (adjPP f).unit.app F ≫ (PF f).map ((injectiveResolution ((PB f).obj F)).ι.f 0) := by
  rw [gmap_f, ← Category.assoc]
  have hn := (adjPP f).unit.naturality ((injectiveResolution F).ι.f 0)
  refine (congrArg (· ≫ (PF f).map ((phi f F).f 0)) hn).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg ((adjPP f).unit.app F ≫ ·) ?_
  refine ((PF f).map_comp _ _).symm.trans ?_
  exact congrArg (PF f).map (phi_spec f F)

/-- The comparison of the two derived readings of the pullback. -/
private lemma psi_pullback (n : ℕ) (e : Abelian.Ext (zS W) F n) :
    (psi Z n).hom.app ((PB f).obj F)
        ((Stacks.Cohomology.ModuleComparison.extMapComp (PB f) (alphaZ f) n).app F e) =
      ((injectiveResolution ((PB f).obj F)).isoRightDerivedObj
          (MMP.Analytic.globalSections Z) n).inv
        (HomologicalComplex.homologyMap (gZ f F) n
        (((injectiveResolution F).isoRightDerivedObj (MMP.Analytic.globalSections W) n).hom
          ((psi W n).hom.app F e))) := by
  cases n with
  | zero =>
    obtain ⟨h, rfl⟩ := (Ext.mk₀_bijective (zS W) F).2 e
    exact star_zero f F h
  | succ k =>
    obtain ⟨t, rfl⟩ :=
      ModuleSheafCohomology.extCyclesMap_surjective (injectiveResolution F) (zS W) k e
    exact (star_succ f F k t).trans (ConcreteCategory.comp_apply _ _ _)

private lemma tau_pullback (n : ℕ) (e : Abelian.Ext (zS W) F n) :
    tau Z ((PB f).obj F) n
        ((Stacks.Cohomology.ModuleComparison.extMapComp (PB f) (alphaZ f) n).app F e) =
      MMP.Analytic.sheafCohomologyPullback f F n (tau W F n e) := by
  have hg : (injectiveResolution F).ι.f 0 ≫ (gmap f F).f 0 =
      ((adjPP f).unit.app F ≫ (PF f).map (𝟙 ((PB f).obj F))) ≫
        (PF f).map ((injectiveResolution ((PB f).obj F)).ι.f 0) :=
    (gmap_hg f F).trans (congrArg
      (· ≫ (PF f).map ((injectiveResolution ((PB f).obj F)).ι.f 0))
      ((congrArg ((adjPP f).unit.app F ≫ ·) ((PF f).map_id _)).trans (Category.comp_id _))).symm
  have hc := sheafCohomologyIso_pullback f F ((PB f).obj F) (𝟙 _) (injectiveResolution F)
    (injectiveResolution ((PB f).obj F)) (gmap f F) hg n
  have hc' := ConcreteCategory.congr_hom hc
    ((MMP.Analytic.sheafCohomologyIso W n).inv.app F ((psi W n).hom.app F e))
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_app_apply] at hc'
  have i1 := ConcreteCategory.congr_hom
    ((MMP.Analytic.sheafCohomology Z n).map_id ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj F))
    (MMP.Analytic.sheafCohomologyPullback f F n
      ((MMP.Analytic.sheafCohomologyIso W n).inv.app F ((psi W n).hom.app F e)))
  have h5 := (congrArg (fun x => (MMP.Analytic.sheafCohomologyIso Z n).hom.app ((PB f).obj F) x)
    i1).symm.trans hc'
  have h6 := congrArg (fun x => (MMP.Analytic.sheafCohomologyIso Z n).inv.app ((PB f).obj F) x) h5
  simp only [Iso.hom_inv_id_app_apply] at h6
  change (MMP.Analytic.sheafCohomologyIso Z n).inv.app ((PB f).obj F)
      ((psi Z n).hom.app ((PB f).obj F)
        ((Stacks.Cohomology.ModuleComparison.extMapComp (PB f) (alphaZ f) n).app F e)) = _
  rw [psi_pullback]
  exact h6.symm

end Pull

end ExtGodement

/-- `Sheaf.H` agrees with Godement sheaf cohomology, naturally in the sheaf and compatibly with
pullback along continuous maps. -/
private theorem exists_addEquiv_sheafH_sheafCohomology :
    ∃ τ : ∀ (M : TopCat.{0}) (F : Sheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0}) (n : ℕ),
        Sheaf.H.{0} F n ≃+ (MMP.Analytic.sheafCohomology M n).obj F,
      (∀ (M : TopCat.{0}) {F G : Sheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0}}
          (a : F ⟶ G) (n : ℕ)
          (x : Sheaf.H.{0} F n),
          τ M G n (x.comp (Ext.mk₀ a) (add_zero n)) =
            (MMP.Analytic.sheafCohomology M n).map a (τ M F n x)) ∧
      ∀ {Z W : TopCat.{0}} (f : Z ⟶ W) (F : Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{0})
        (n : ℕ)
        (e : Sheaf.H.{0} F n),
        τ Z _ n ((Ext.mk₀ (constPullbackComparison f (.of (ULift ℤ)))).comp
            ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapExtAddHom _ _ n e) (zero_add n)) =
          MMP.Analytic.sheafCohomologyPullback f F n (τ W F n e) :=
  ⟨fun M F n ↦ tau M F n, fun M _ _ a n x ↦ tau_naturality M a n x,
    fun f F n e ↦ tau_pullback f F n e⟩

noncomputable section SingularBridge

variable (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A]

private abbrev forgetAb : ModuleCat.{0} R ⥤ AddCommGrpCat.{0} :=
  forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}
private abbrev chAb : TopCat.{0} ⥤ ChainComplex AddCommGrpCat.{0} ℕ :=
  (singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift ℤ))
private abbrev singAb : TopCat.{0}ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{0} ℕ :=
  chAb.op ⋙ HomologicalComplex.opFunctor _ _ ⋙
    (preadditiveYoneda.obj (AddCommGrpCat.of A)).mapHomologicalComplex _
/-- Singular cohomology `H^n(Hom(C_•(-; ℤ), A))` in abelian groups. -/
private abbrev singH (n : ℕ) : TopCat.{0}ᵒᵖ ⥤ AddCommGrpCat.{0} :=
  chAb.op ⋙ HomologicalComplex.opFunctor _ _ ⋙
    (preadditiveYoneda.obj (AddCommGrpCat.of A)).mapHomologicalComplex _ ⋙
      HomologicalComplex.homologyFunctor _ _ n
private abbrev cochMod (M : TopCat.{0}) : CochainComplex (ModuleCat.{0} R) ℕ :=
  (singularCochainComplex R (ModuleCat.of R A)).obj (op M)

/-- The singular `k`-chains of `M` with coefficients in `R`. -/
private abbrev chainsR (M : TopCat.{0}) (k : ℕ) : ModuleCat.{0} R :=
  ((TopCat.toSSet.obj M).chainComplex (ModuleCat.of R R)).X k
/-- The singular `k`-chains of `M` with coefficients in `ℤ`. -/
private abbrev chainsZ (M : TopCat.{0}) (k : ℕ) : AddCommGrpCat.{0} :=
  ((TopCat.toSSet.obj M).chainComplex (AddCommGrpCat.of (ULift.{0} ℤ))).X k

variable {R A}

/-- The value of an `R`-linear singular cochain on a singular simplex. -/
private def valR {M : TopCat.{0}} {k : ℕ} (x : chainsR R M k ⟶ ModuleCat.of R A)
    (s : (TopCat.toSSet.obj M) _⦋k⦌) : A :=
  ((TopCat.toSSet.obj M).ιChainComplex s ≫ x) (1 : R)

/-- The value of an additive singular cochain on a singular simplex. -/
private def valAb {M : TopCat.{0}} {k : ℕ} (y : chainsZ M k ⟶ AddCommGrpCat.of A)
    (s : (TopCat.toSSet.obj M) _⦋k⦌) : A :=
  ((TopCat.toSSet.obj M).ιChainComplex s ≫ y) (ULift.up 1)

private lemma valR_injective {M : TopCat.{0}} {k : ℕ}
    {x x' : chainsR R M k ⟶ ModuleCat.of R A} (h : ∀ s, valR x s = valR x' s) :
    x = x' := by
  refine SSet.chainComplex_hom_ext fun s ↦ ?_
  ext
  exact h s

private lemma valAb_injective {M : TopCat.{0}} {k : ℕ}
    {y y' : chainsZ M k ⟶ AddCommGrpCat.of A} (h : ∀ s, valAb y s = valAb y' s) :
    y = y' :=
  SSet.chainComplex_hom_ext fun s ↦ (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective (h s)

/-- The additive cochain with the same values as an `R`-linear one. -/
private def toAb {M : TopCat.{0}} {k : ℕ} (x : chainsR R M k ⟶ ModuleCat.of R A) :
    chainsZ M k ⟶ AddCommGrpCat.of A :=
  Cofan.IsColimit.desc ((TopCat.toSSet.obj M).isColimitChainComplexXCofan _ k)
    fun s ↦ (AddCommGrpCat.uliftZMultiplesAddEquiv (.of A)).symm (valR x s)

/-- The `R`-linear cochain with the same values as an additive one. -/
private def toMod {M : TopCat.{0}} {k : ℕ} (y : chainsZ M k ⟶ AddCommGrpCat.of A) :
    chainsR R M k ⟶ ModuleCat.of R A :=
  Cofan.IsColimit.desc ((TopCat.toSSet.obj M).isColimitChainComplexXCofan _ k)
    fun s ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton R A (valAb y s))

@[simp] private lemma valAb_toAb {M : TopCat.{0}} {k : ℕ}
    (x : chainsR R M k ⟶ ModuleCat.of R A) (s) : valAb (toAb x) s = valR x s := by
  unfold valAb toAb
  erw [Cofan.IsColimit.fac]
  exact (AddCommGrpCat.uliftZMultiplesAddEquiv _).apply_symm_apply _

@[simp] private lemma valR_toMod {M : TopCat.{0}} {k : ℕ}
    (y : chainsZ M k ⟶ AddCommGrpCat.of A) (s) : valR (toMod (R := R) y) s = valAb y s := by
  unfold valR toMod
  erw [Cofan.IsColimit.fac]
  exact one_smul R _

@[simp] private lemma valR_add {M : TopCat.{0}} {k : ℕ}
    (x x' : chainsR R M k ⟶ ModuleCat.of R A) (s) :
    valR (x + x') s = valR x s + valR x' s := by
  unfold valR
  rw [Preadditive.comp_add]
  rfl

@[simp] private lemma valR_smul {M : TopCat.{0}} {k : ℕ}
    (r : R) (x : chainsR R M k ⟶ ModuleCat.of R A) (s) :
    valR (r • x) s = r • valR x s := by
  unfold valR
  rw [Linear.comp_smul]
  rfl

@[simp] private lemma valAb_add {M : TopCat.{0}} {k : ℕ}
    (y y' : chainsZ M k ⟶ AddCommGrpCat.of A) (s) :
    valAb (y + y') s = valAb y s + valAb y' s := by
  unfold valAb
  rw [Preadditive.comp_add]
  rfl

private lemma valR_d {M : TopCat.{0}} {k : ℕ}
    (x : chainsR R M k ⟶ ModuleCat.of R A) (s) :
    valR ((((TopCat.toSSet.obj M).chainComplex (ModuleCat.of R R)).d (k + 1) k) ≫ x) s =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • valR x ((TopCat.toSSet.obj M).δ i s) := by
  unfold valR
  rw [← Category.assoc, SSet.ιChainComplex_d]
  simp [Preadditive.sum_comp]

private lemma valAb_d {M : TopCat.{0}} {k : ℕ}
    (y : chainsZ M k ⟶ AddCommGrpCat.of A) (s) :
    valAb ((((TopCat.toSSet.obj M).chainComplex (AddCommGrpCat.of (ULift.{0} ℤ))).d (k + 1) k) ≫ y)
        s =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • valAb y ((TopCat.toSSet.obj M).δ i s) := by
  change AddCommGrpCat.uliftZMultiplesAddEquiv _ (_ ≫ _ ≫ y) =
    ∑ i : Fin (k + 2), _ • AddCommGrpCat.uliftZMultiplesAddEquiv _ (_ ≫ y)
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp, map_sum]
  simp only [Preadditive.zsmul_comp, map_zsmul]

private lemma valR_map {Z W : TopCat.{0}} (f : Z ⟶ W) {k : ℕ}
    (x : chainsR R W k ⟶ ModuleCat.of R A) (s) :
    valR ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)).f k ≫ x) s =
      valR x ((TopCat.toSSet.map f).app _ s) := by
  unfold valR
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]

private lemma valAb_map {Z W : TopCat.{0}} (f : Z ⟶ W) {k : ℕ}
    (y : chainsZ W k ⟶ AddCommGrpCat.of A) (s) :
    valAb ((SSet.chainComplexMap (TopCat.toSSet.map f) (AddCommGrpCat.of (ULift.{0} ℤ))).f k ≫ y) s =
      valAb y ((TopCat.toSSet.map f).app _ s) := by
  unfold valAb
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]

variable (R A) in
/-- `R`-linear and additive singular cochains with coefficients in `A` agree: both are the
functions on singular simplices. -/
private def cochainEquiv (M : TopCat.{0}) (k : ℕ) :
    (cochMod R A M).X k ≃+ ((singAb A).obj (op M)).X k where
  toFun x := toAb (show chainsR R M k ⟶
    ModuleCat.of R A from x)
  invFun y := toMod (R := R) (show ((TopCat.toSSet.obj M).chainComplex
    (AddCommGrpCat.of (ULift.{0} ℤ))).X k ⟶ AddCommGrpCat.of A from y)
  left_inv x := valR_injective fun s ↦ by rw [valR_toMod, valAb_toAb]
  right_inv y := valAb_injective fun s ↦ by rw [valAb_toAb, valR_toMod]
  map_add' x y := valAb_injective fun s ↦ by
    erw [valAb_add, valAb_toAb, valAb_toAb, valAb_toAb, valR_add]

private lemma cochainEquiv_d (M : TopCat.{0}) (k : ℕ) (x : (cochMod R A M).X k) :
    cochainEquiv R A M (k + 1) ((cochMod R A M).d k (k + 1) x) =
      ((singAb A).obj (op M)).d k (k + 1) (cochainEquiv R A M k x) :=
  valAb_injective fun s ↦ by
    change valAb (toAb (((TopCat.toSSet.obj M).chainComplex (ModuleCat.of R R)).d (k + 1) k ≫
      (show chainsR R M k ⟶ ModuleCat.of R A
        from x))) s = valAb (((TopCat.toSSet.obj M).chainComplex
          (AddCommGrpCat.of (ULift.{0} ℤ))).d (k + 1) k ≫ toAb x) s
    rw [valAb_toAb, valAb_d]
    simp only [valAb_toAb (M := M) (k := k) x]
    exact valR_d (M := M) x s

private lemma cochainEquiv_map {Z W : TopCat.{0}} (f : Z ⟶ W) (k : ℕ) (x : (cochMod R A W).X k) :
    cochainEquiv R A Z k (((singularCochainComplex R (ModuleCat.of R A)).map f.op).f k x) =
      ((singAb A).map f.op).f k (cochainEquiv R A W k x) :=
  valAb_injective fun s ↦ by
    change valAb (toAb ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)).f k ≫
      (show chainsR R W k ⟶ ModuleCat.of R A
        from x))) s = valAb ((SSet.chainComplexMap (TopCat.toSSet.map f)
          (AddCommGrpCat.of (ULift.{0} ℤ))).f k ≫ toAb x) s
    rw [valAb_toAb, valAb_map, valAb_toAb (M := W) (k := k) x]
    exact valR_map f x s

variable (A) in
/-- Post-composition of additive singular cochains with multiplication by `r : R`. -/
private abbrev smulCochains (r : R) : singAb A ⟶ singAb A :=
  Functor.whiskerLeft (chAb.op ⋙ HomologicalComplex.opFunctor _ _)
    (NatTrans.mapHomologicalComplex
      (preadditiveYoneda.map (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom A r))) _)

private lemma cochainEquiv_smul (M : TopCat.{0}) (k : ℕ) (r : R) (x : (cochMod R A M).X k) :
    cochainEquiv R A M k (r • x) = ((smulCochains A r).app (op M)).f k (cochainEquiv R A M k x) :=
  valAb_injective fun s ↦ by
    change valAb (toAb (r • (show chainsR R M k ⟶
      ModuleCat.of R A from x))) s = r • valAb (toAb x) s
    rw [valAb_toAb, valAb_toAb (M := M) (k := k) x]
    exact valR_smul r x s

variable (R A) in
private def cochIso (M : TopCat.{0}) :
    ((forgetAb R).mapHomologicalComplex _).obj (cochMod R A M) ≅ (singAb A).obj (op M) :=
  HomologicalComplex.Hom.isoOfComponents (fun k ↦ (cochainEquiv R A M k).toAddCommGrpIso) (by
    rintro i j (rfl : i + 1 = j)
    ext x
    exact (cochainEquiv_d M i x).symm)

private lemma cochIso_naturality {Z W : TopCat.{0}} (f : Z ⟶ W) :
    ((forgetAb R).mapHomologicalComplex _).map
        ((singularCochainComplex R (ModuleCat.of R A)).map f.op) ≫
      (cochIso R A Z).hom = (cochIso R A W).hom ≫ (singAb A).map f.op := by
  ext k x
  exact cochainEquiv_map f k x

private lemma cochIso_smul (M : TopCat.{0}) (r : R) :
    ((forgetAb R).mapHomologicalComplex _).map (r • 𝟙 (cochMod R A M)) ≫ (cochIso R A M).hom =
      (cochIso R A M).hom ≫ (smulCochains A r).app (op M) := by
  ext k x
  exact cochainEquiv_smul M k r x

private lemma emptyHom_ext (M : TopCat.{0}) (B : ModuleCat.{0} R) (k : ℕ)
    (x y : (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj
      (TopCat.of (∅ : Set M))).X k ⟶ B) : x = y := by
  refine Sigma.hom_ext _ _ (fun σ => ?_)
  exfalso
  obtain ⟨p⟩ : Nonempty (SimplexCategory.toTop.obj ⦋k⦌) := inferInstance
  exact (show (∅ : Set M) from
    (σ.down : SimplexCategory.toTop.obj ⦋k⦌ ⟶ TopCat.of (∅ : Set M)).hom p).2

variable (R A) in
private lemma restriction_empty_eq_zero (M : TopCat.{0}) :
    singularCochainRestriction R (ModuleCat.of R A) M ∅ = 0 := by
  ext k x
  exact emptyHom_ext M _ k _ _

variable (R A) in
private def relIso (M : TopCat.{0}) (n : ℕ) :
    relativeSingularCohomology R (ModuleCat.of R A) M ∅ n ≅ (cochMod R A M).homology n :=
  haveI := kernel.ι_of_zero (restriction_empty_eq_zero R A M)
  (relativeSingularCochainComplex R (ModuleCat.of R A) M ∅).extendHomologyIso
      ComplexShape.embeddingUpNat (j := n) rfl ≪≫
    HomologicalComplex.homologyMapIso (asIso (kernel.ι _)) n

private lemma relIso_naturality {Z W : TopCat.{0}} (f : Z ⟶ W) (n : ℕ) :
    relativeSingularCohomology.map R (ModuleCat.of R A) f (Set.empty_subset _) n ≫
      (relIso R A Z n).hom =
    (relIso R A W n).hom ≫ HomologicalComplex.homologyMap
      ((singularCochainComplex R (ModuleCat.of R A)).map f.op) n := by
  change relativeSingularCohomology.map R (ModuleCat.of R A) f (Set.empty_subset _) n ≫
      ((relativeSingularCochainComplex R (ModuleCat.of R A) Z ∅).extendHomologyIso
        ComplexShape.embeddingUpNat (j := n) rfl).hom ≫
      HomologicalComplex.homologyMap (kernel.ι _) n =
    (((relativeSingularCochainComplex R (ModuleCat.of R A) W ∅).extendHomologyIso
        ComplexShape.embeddingUpNat (j := n) rfl).hom ≫
      HomologicalComplex.homologyMap (kernel.ι _) n) ≫ _
  rw [relativeSingularCohomology.map]
  erw [HomologicalComplex.extendHomologyIso_hom_naturality_assoc]
  rw [Category.assoc, ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    relativeSingularCochainComplex.map_ι]
  rfl

variable (R A) in
/-- The cohomology of `R`-linear singular cochains, as an abelian group, is that of additive
singular cochains. -/
private def homIso (M : TopCat.{0}) (n : ℕ) :
    (forgetAb R).obj ((cochMod R A M).homology n) ≅ ((singAb A).obj (op M)).homology n :=
  (((cochMod R A M).sc n).mapHomologyIso (forgetAb R)).symm ≪≫
    HomologicalComplex.homologyMapIso (cochIso R A M) n

private lemma homIso_naturality {Z Z' : TopCat.{0}} (φ : cochMod R A Z' ⟶ cochMod R A Z)
    (ψ : (singAb A).obj (op Z') ⟶ (singAb A).obj (op Z))
    (h : ((forgetAb R).mapHomologicalComplex _).map φ ≫ (cochIso R A Z).hom =
      (cochIso R A Z').hom ≫ ψ)
    (n : ℕ) :
    (forgetAb R).map (HomologicalComplex.homologyMap φ n) ≫ (homIso R A Z n).hom =
      (homIso R A Z' n).hom ≫ HomologicalComplex.homologyMap ψ n := by
  simp only [homIso, Iso.trans_hom, Iso.symm_hom, HomologicalComplex.homologyMapIso_hom]
  change (forgetAb R).map (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor _ _ n).map φ)) ≫
      (((cochMod R A Z).sc n).mapHomologyIso (forgetAb R)).inv ≫
        HomologicalComplex.homologyMap (cochIso R A Z).hom n =
    ((((cochMod R A Z').sc n).mapHomologyIso (forgetAb R)).inv ≫
        HomologicalComplex.homologyMap (cochIso R A Z').hom n) ≫ _
  have key := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map φ) (forgetAb R)
  have key3 := congrArg (fun φ => HomologicalComplex.homologyMap φ n) h
  simp only [HomologicalComplex.homologyMap_comp] at key3
  refine ((Category.assoc _ _ _).symm.trans ?_).trans (Category.assoc _ _ _).symm
  refine (congrArg (· ≫ HomologicalComplex.homologyMap (cochIso R A Z).hom n) key).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg ((((cochMod R A Z').sc n).mapHomologyIso (forgetAb R)).inv ≫ ·) key3

variable (R A) in
private def totalIso (M : TopCat.{0}) (n : ℕ) :
    (forgetAb R).obj (relativeSingularCohomology R (ModuleCat.of R A) M ∅ n) ≅
      ((singAb A).obj (op M)).homology n :=
  (forgetAb R).mapIso (relIso R A M n) ≪≫ homIso R A M n

private lemma totalIso_naturality {Z W : TopCat.{0}} (f : Z ⟶ W) (n : ℕ) :
    (forgetAb R).map
        (relativeSingularCohomology.map R (ModuleCat.of R A) f (Set.empty_subset _) n) ≫
      (totalIso R A Z n).hom =
    (totalIso R A W n).hom ≫ HomologicalComplex.homologyMap ((singAb A).map f.op) n := by
  simp only [totalIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← (forgetAb R).map_comp_assoc, relIso_naturality, (forgetAb R).map_comp_assoc,
    homIso_naturality _ _ (cochIso_naturality f), Category.assoc]

private lemma homologyMap_smul_id (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) (r : R) :
    HomologicalComplex.homologyMap (r • 𝟙 K) n = r • 𝟙 _ := by
  change ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor _ _ n).map (r • 𝟙 K)) = _
  have : (HomologicalComplex.shortComplexFunctor _ _ n).map (r • 𝟙 K) = r • 𝟙 _ := by
    ext <;> rfl
  rw [this, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

private lemma totalIso_smul (M : TopCat.{0}) (n : ℕ) (r : R)
    (x : relativeSingularCohomology R (ModuleCat.of R A) M ∅ n) :
    (totalIso R A M n).hom (r • x) =
      HomologicalComplex.homologyMap ((smulCochains A r).app (op M)) n
        ((totalIso R A M n).hom x) := by
  have h₁ : (relIso R A M n).hom (r • x) =
      HomologicalComplex.homologyMap (r • 𝟙 (cochMod R A M)) n ((relIso R A M n).hom x) := by
    rw [homologyMap_smul_id, map_smul]
    rfl
  have h₂ := ConcreteCategory.congr_hom (homIso_naturality _ _ (cochIso_smul M r) n)
    ((relIso R A M n).hom x)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h₂
  exact (congrArg (homIso R A M n).hom h₁).trans h₂

end SingularBridge

/-- **Constant-sheaf and singular cohomology on metrizable locally contractible spaces.** For a
module `A` over a commutative ring `R`, `H^n(M, A_M) ≃+ H^n_sing(M; A)`; the action of `r : R`
corresponds on the sheaf side to the constant-sheaf map of multiplication by `r`, and the
isomorphisms are natural for every continuous map between such spaces. -/
private theorem exists_addEquiv_sheafH_constantSheaf_singularCohomology_of_locallyContractible
    (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A] (n : ℕ) :
    ∃ φ : ∀ (M : TopCat.{0}), IsMetrizableLocallyContractible M →
        (Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology M)
            AddCommGrpCat.{0}).obj (.of A)) n ≃+
          relativeSingularCohomology R (.of R A) M ∅ n),
      (∀ (M : TopCat.{0}) (hM : IsMetrizableLocallyContractible M) (r : R)
          (e : Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology M)
            AddCommGrpCat.{0}).obj (.of A)) n),
        φ M hM (e.comp (Ext.mk₀ ((constantSheaf _ AddCommGrpCat.{0}).map
          (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom A r)))) (add_zero n)) =
          r • φ M hM e) ∧
      ∀ {Z W : TopCat.{0}} (hZ : IsMetrizableLocallyContractible Z)
        (hW : IsMetrizableLocallyContractible W) (f : Z ⟶ W)
        (e : Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology W)
            AddCommGrpCat.{0}).obj (.of A)) n),
        (Ext.mk₀ (constPullbackComparison f (.of (ULift ℤ)))).comp
            ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapExtAddHom _ _ n e)
            (zero_add n) =
          ((φ Z hZ).symm ((relativeSingularCohomology.map R (.of R A) f
              (Set.empty_subset _) n).hom (φ W hW e))).comp
            (Ext.mk₀ (constPullbackComparison f (.of A))) (add_zero n) := by
  obtain ⟨τ, hτnat, hτpull⟩ := exists_addEquiv_sheafH_sheafCohomology
  obtain ⟨E, hE, hEc⟩ := exists_sheafCohomology_constantSheaf_iso_singularCohomology_natural
  obtain ⟨σ, hσ, hσs⟩ : ∃ σ : ∀ M : TopCat.{0},
      relativeSingularCohomology R (.of R A) M ∅ n ≃+ (singH A n).obj (op M),
      (∀ {Z W : TopCat.{0}} (f : Z ⟶ W) (y : relativeSingularCohomology R (.of R A) W ∅ n),
        σ Z ((relativeSingularCohomology.map R (.of R A) f (Set.empty_subset _) n).hom y) =
          (singH A n).map f.op (σ W y)) ∧
      ∀ (M : TopCat.{0}) (r : R) (y : relativeSingularCohomology R (.of R A) M ∅ n),
        σ M (r • y) = HomologicalComplex.homologyMap ((smulCochains A r).app (op M)) n (σ M y) :=
    ⟨fun M ↦ (totalIso R A M n).addCommGroupIsoToAddEquiv, fun f y ↦ by
      have h := ConcreteCategory.congr_hom (totalIso_naturality (R := R) (A := A) f n) y
      rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h,
      fun M r y ↦ totalIso_smul M n r y⟩
  refine ⟨fun M hM ↦ haveI := hM.1;
    (τ M _ n).trans ((E (.of A) M hM.locallyContractibleSpace n).addCommGroupIsoToAddEquiv.trans
      (σ M).symm), ?_, ?_⟩
  · intro M hM r e
    haveI := hM.1
    have h := ConcreteCategory.congr_hom (hEc (.of A) (.of A)
      (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom A r)) M hM.locallyContractibleSpace n)
        (τ M _ n e)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    apply (σ M).injective
    simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
    rw [hσs, AddEquiv.apply_symm_apply, hτnat]
    exact h
  intro Z W hZ hW f x
  haveI := hZ.1
  haveI := hW.1
  set t := τ W _ n x
  have key := congrArg (E (.of A) Z hZ.locallyContractibleSpace n).inv (ConcreteCategory.congr_hom
    (hE (.of A) W Z hW.locallyContractibleSpace hZ.locallyContractibleSpace f n) t)
  simp only [ConcreteCategory.comp_apply, Iso.hom_inv_id_apply] at key
  have hc := pullbackConstComparison_comp_constPullbackComparison f (AddCommGrpCat.of A)
  apply (τ Z _ n).injective
  beta_reduce
  rw [hτpull]
  erw [hτnat Z (constPullbackComparison f (AddCommGrpCat.of A))]
  simp only [AddEquiv.symm_trans_apply, AddEquiv.trans_apply, AddEquiv.apply_symm_apply,
    AddEquiv.symm_symm]
  erw [hσ, AddEquiv.apply_symm_apply]
  erw [key]
  rw [← ConcreteCategory.comp_apply]
  have hc' : (MMP.Analytic.sheafCohomology Z n).map (pullbackConstComparison f (.of A)) ≫
      (MMP.Analytic.sheafCohomology Z n).map (constPullbackComparison f (.of A)) = 𝟙 _ :=
    (Functor.map_comp _ _ _).symm.trans
      ((congrArg (fun g ↦ (MMP.Analytic.sheafCohomology Z n).map g) hc).trans
        ((MMP.Analytic.sheafCohomology Z n).map_id _))
  erw [hc']
  rfl

/-- The analytic space of a projective scheme over `ℂ` is metrizable and locally contractible. -/
private theorem isMetrizableLocallyContractible_analyticSpace {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjectiveMorphism sX) :
    IsMetrizableLocallyContractible (analyticSpace sX) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : IsComplexScheme X := MMP.Analytic.isComplexScheme_of_isProjective X hX.isProjective
  obtain ⟨hb, N, F, hF⟩ := UnderlyingSpace.hasBasis_contractible_and_exists_isClosedEmbedding X
  let h : analyticSpace sX ≃ₜ UnderlyingSpace ℂ X := homeomorphUnderlyingSpace (X := X)
  refine ⟨(hF.comp h.isClosedEmbedding).isEmbedding.metrizableSpace, fun p ↦ ⟨fun t ↦
    ⟨fun ht ↦ ?_, fun ⟨W, ⟨hWo, hpW, _⟩, hWt⟩ ↦ Filter.mem_of_superset (hWo.mem_nhds hpW) hWt⟩⟩⟩
  have : h.symm ⁻¹' t ∈ 𝓝 (h p) :=
    h.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using ht)
  obtain ⟨V, ⟨hVo, hpV, hV⟩, hVt⟩ := (hb (h p)).mem_iff.1 this
  refine ⟨h.symm '' V, ⟨h.symm.isOpenMap V hVo, ⟨h p, hpV, by simp⟩,
    (h.symm.image V).symm.contractibleSpace⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hVt hy

/-- **Constant-sheaf and singular cohomology of projective complex schemes.** For an abelian
group `A` and `n : ℕ` there are isomorphisms
`φ_X : H^n(X^an, A_{X^an}) ≃+ H^n_sing(X^an; A)` for every projective scheme `X` over `ℂ`,
compatible with pullback: for a morphism `g : X ⟶ Y` over `ℂ` of projective complex schemes,
with realized map `f = g^an`, and `e ∈ H^n(Y^an, A)`, the pullbacks `f⁻¹ e` and
`φ_X⁻¹ (f^* φ_Y e)` agree after comparison through the canonical maps
`α_M : M_{X^an} ⟶ f⁻¹ M_{Y^an}` of constant sheaves. -/
@[mmp "lem_mmp_projective_singular_sheaf_comparison"]
public theorem exists_addEquiv_sheafH_constantSheaf_singularCohomology
    (A : Type) [AddCommGroup A] (n : ℕ) :
    let α : ∀ {Z W : TopCat.{0}} (f : Z ⟶ W) (M : AddCommGrpCat.{0}),
        (constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{0}).obj M ⟶
          (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj
            ((constantSheaf (Opens.grothendieckTopology W) AddCommGrpCat.{0}).obj M) :=
      fun f M ↦ ((constantSheafAdj _ _ isTerminalTop).homEquiv _ _).symm
        ((constantSheafAdj _ _ isTerminalTop).unit.app M ≫
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app
            ((constantSheaf _ _).obj M)).hom.app (op ⊤))
    ∃ φ : ∀ {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)), IsProjectiveMorphism sX →
        (Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology (analyticSpace sX))
            AddCommGrpCat.{0}).obj (.of A)) n ≃+
          relativeSingularCohomology ℤ (.of ℤ A) (analyticSpace sX) ∅ n),
      ∀ {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
        (hX : IsProjectiveMorphism sX) (hY : IsProjectiveMorphism sY) (g : X ⟶ Y)
        (hg : g ≫ sY = sX)
        (e : Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology (analyticSpace sY))
            AddCommGrpCat.{0}).obj (.of A)) n),
        (Ext.mk₀ (α (analyticMap g hg) (.of (ULift ℤ)))).comp
            ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg)).mapExtAddHom _ _ n e)
            (zero_add n) =
          ((φ sX hX).symm ((relativeSingularCohomology.map ℤ (.of ℤ A) (analyticMap g hg)
              (Set.empty_subset _) n).hom (φ sY hY e))).comp
            (Ext.mk₀ (α (analyticMap g hg) (.of A))) (add_zero n) := by
  obtain ⟨φ, -, hφ⟩ :=
    exists_addEquiv_sheafH_constantSheaf_singularCohomology_of_locallyContractible ℤ A n
  exact ⟨fun sX hX ↦ φ _ (isMetrizableLocallyContractible_analyticSpace sX hX),
    fun sX sY hX hY g hg e ↦ hφ _ _ (analyticMap g hg) e⟩

/-- **Constant-sheaf and singular cohomology of projective complex schemes, with coefficients in
a ring.** For a commutative ring `R` and `n : ℕ` there are isomorphisms
`ψ_X : H^n(X^an, R_{X^an}) ≃+ H^n_sing(X^an; R)` for every projective scheme `X` over `ℂ`. They
are `R`-linear: composing with the constant-sheaf map of multiplication by `r : R` corresponds
to `r •`. They are compatible with pullback: for a morphism `g : X ⟶ Y` over `ℂ` of projective
complex schemes, with realized map `f = g^an`, if `e' ∈ H^n(X^an, R)` and `e ∈ H^n(Y^an, R)`
have the same image in `Ext^n(ℤ_{X^an}, f⁻¹ R_{Y^an})` through the comparisons
`constPullbackComparison`, then `ψ_X e' = f^* (ψ_Y e)`. -/
public theorem exists_addEquiv_sheafH_constantSheaf_singularCohomology_ring
    (R : Type) [CommRing R] (n : ℕ) :
    ∃ ψ : ∀ {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)), IsProjectiveMorphism sX →
        (Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology (analyticSpace sX))
            AddCommGrpCat.{0}).obj (.of R)) n ≃+
          relativeSingularCohomology R (.of R R) (analyticSpace sX) ∅ n),
      (∀ {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjectiveMorphism sX) (r : R)
          (e : Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology (analyticSpace sX))
            AddCommGrpCat.{0}).obj (.of R)) n),
        ψ sX hX (e.comp (Ext.mk₀ ((constantSheaf _ AddCommGrpCat.{0}).map
          (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom R r)))) (add_zero n)) =
          r • ψ sX hX e) ∧
      ∀ {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
        (hX : IsProjectiveMorphism sX) (hY : IsProjectiveMorphism sY) (g : X ⟶ Y)
        (hg : g ≫ sY = sX)
        (e : Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology (analyticSpace sY))
            AddCommGrpCat.{0}).obj (.of R)) n)
        (e' : Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology (analyticSpace sX))
            AddCommGrpCat.{0}).obj (.of R)) n),
        (Ext.mk₀ (constPullbackComparison (analyticMap g hg) (.of (ULift ℤ)))).comp
            ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg)).mapExtAddHom _ _ n e)
            (zero_add n) =
          e'.comp (Ext.mk₀ (constPullbackComparison (analyticMap g hg) (.of R))) (add_zero n) →
        ψ sX hX e' = (relativeSingularCohomology.map R (.of R R) (analyticMap g hg)
          (Set.empty_subset _) n).hom (ψ sY hY e) := by
  obtain ⟨φ, hφs, hφ⟩ :=
    exists_addEquiv_sheafH_constantSheaf_singularCohomology_of_locallyContractible R R n
  refine ⟨fun sX hX ↦ φ _ (isMetrizableLocallyContractible_analyticSpace sX hX),
    fun sX hX r e ↦ hφs _ _ r e, fun sX sY hX hY g hg e e' h ↦ ?_⟩
  have h' := comp_mk₀_constPullbackComparison_injective _ _
    ((hφ (isMetrizableLocallyContractible_analyticSpace sX hX)
      (isMetrizableLocallyContractible_analyticSpace sY hY) (analyticMap g hg) e).symm.trans h)
  rw [← h', AddEquiv.apply_symm_apply]

end MMP.Analytic
