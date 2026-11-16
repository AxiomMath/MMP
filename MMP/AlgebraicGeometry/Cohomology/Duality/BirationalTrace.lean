module
public import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeBiduality
import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedApplicationRightUnitLawOnASite
import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Uniqueness
import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactPushforwardSingleUnit
public import StacksFrontier.AlgebraicGeometry.Duality.ModelComparisonRightAdjoint
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceDevissage
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.UpperShriekStructureSheafTrivial
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective

/-!
# Proper duality for a smooth projective birational source

This file concerns a projective birational morphism `f : Y ⟶ X` of normal
projective varieties of dimension `n` over an algebraically closed field `k` of characteristic
zero, with `Y` smooth. With `D_X = r_X^× 𝒪_{Spec k}` for a right adjoint `r_X^×` of the derived
direct image along the structure morphism, `D_X` is a dualizing complex, biduality holds on
objects with coherent cohomology, and the dual of the structural unit `𝒪_X ⟶ Rf_* 𝒪_Y` is,
under the comparison `R𝓗om(Rf_* 𝒪_Y, D_X) ≅ Rf_*(ω_Y[n])` given by the sheafy trace, the proper
trace `Rf_*(ω_Y[n]) ⟶ D_X`. By naturality of `R𝓗om(u, -)` and of `R𝓗om(𝒪_X, -) ≅ id`, this
reduces to the compatibility of `Rf_* R𝓗om(𝒪_Y, M) ⟶ R𝓗om(Rf_* 𝒪_Y, Rf_* M)` with
restriction along the unit `u`.

## Main results

* `MMP.Duality.dual_unit_eq_trace_of_isBirationalMorphism`

## Implementation notes

Everything is read at the standard model `CategoryTheory.HasDerivedCategory.standard` of the
derived categories, the model at which the sheafy trace `Stacks.Duality.sheafyTrace` and the
biduality theorem `Stacks.Duality.isIso_derivedBiduality_of_isDualizingComplex` are stated.

The right adjoints `r_X^×` and `f^×` are not chosen: the statement holds for every right adjoint
of `Rr_{X*}` and of `Rf_*` on `D_QCoh`, together with its adjunction. Right adjoints being unique
up to unique isomorphism compatible with the counits, this is the statement for any particular
construction of them ([Stacks, Tag 0A9E]). `Rf_*` is `Stacks.Duality.derivedPushforward f`,
`R𝓗om` is `Stacks.SheafOfModules.derivedSheafHom`, `𝒪` is the unit module in degree zero as an
object of `D_QCoh` (`Stacks.Duality.DerivedPushforward.derivedCategoryB_singleFunctor_obj`), and
`R𝓗om(𝒪, -) ≅ id` is `AlgebraicGeometry.RingedSite.derivedStructureSheafHomNatIso`.

The sheafy trace is built from tensor–internal-Hom adjunction data on `X` and on `Y`. These are
taken to be any such data whose underlying bijection is the bijection of [Stacks, Tag 08J8],
`Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomBijection`; the
remaining fields being propositions, this determines the data.

The structural unit `u` is the structure map `𝒪_X ⟶ f_* 𝒪_Y`
(`SheafOfModules.unitToPushforwardObjUnit`) in degree zero, followed by the comparison of the
direct image with its total right derived functor. `ω_Y[n]` is `ω_Y` placed in degree `-n`.

Biduality is stated for every object with coherent cohomology sheaves; bounded coherent complexes
are a special case.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.61, 3.5

* [Stacks Project, Tag 0FVV](https://stacks.math.columbia.edu/tag/0FVV)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0GEW](https://stacks.math.columbia.edu/tag/0GEW)
* [Stacks Project, Tag 0BRT](https://stacks.math.columbia.edu/tag/0BRT)
-/

universe u

section

open CategoryTheory AlgebraicGeometry Opposite Stacks.Duality

namespace MMP.Duality

-- The Stacks results used here are stated at the locally small models of `D(R)`, `D(𝒪_X)` and
-- `D(SheafOfModules R)`, which Stacks scopes
-- (`StacksFrontier.Homology.DerivedCategory.LocallySmall`).
open scoped Stacks.SmallDerivedModel

/-- The composition formula `Rf_* ⋙ Rr_* ≅ R(f ≫ r)_*` on `D_QCoh` at the locally small model. -/
private noncomputable def quasiCoherentDerivedPushforwardCompIsoOfQcqs {X Y S : Scheme.{u}}
    (f : Y ⟶ X) (rX : X ⟶ S)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace S] [QuasiSeparatedSpace S] [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact rX] [QuasiSeparated rX] :
    quasiCoherentDerivedPushforward f (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ⋙
      quasiCoherentDerivedPushforward rX (isQuasicoherent_homology_derivedPushforward_of_qcqs rX) ≅
      quasiCoherentDerivedPushforward (f ≫ rX)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ rX)) :=
  quasiCoherentDerivedPushforwardCompIso f rX _ _ _

end MMP.Duality

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

namespace MMP.Duality

open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi in
/-- Tensor–internal-Hom adjunction data are determined by their bijection: the remaining fields
are propositions. -/
private theorem tensorHomAdjunction_ext {C : Type*} [Category C] {T : C ⥤ C ⥤ C}
    {H : Cᵒᵖ ⥤ C ⥤ C} {D D' : TensorHomAdjunction T H}
    (h : D.toTensorHomBijection = D'.toTensorHomBijection) : D = D' := by
  obtain ⟨b, _, _, _⟩ := D
  obtain ⟨b', _, _, _⟩ := D'
  cases h
  rfl

open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi in
/-- The sheafy trace of a proper morphism of Noetherian schemes, built from tensor–internal-Hom
data whose bijections are the canonical ones, is an isomorphism at every `L` and every bounded
below `K`. -/
private theorem isIso_sheafyTrace_of_toTensorHomBijection {X Y : Scheme.{u}} (f : Y ⟶ X)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [IsProper f] [IsNoetherian X] [IsNoetherian Y]
    (DX : TensorHomAdjunction (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)
      (Stacks.SheafOfModules.derivedSheafHom X.sheaf))
    (DY : TensorHomAdjunction (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)
      (Stacks.SheafOfModules.derivedSheafHom Y.sheaf))
    (hDX : DX.toTensorHomBijection =
      derivedTensorHomBijection (Stacks.SheafOfModules.ringedSite X.sheaf))
    (hDY : DY.toTensorHomBijection =
      derivedTensorHomBijection (Stacks.SheafOfModules.ringedSite Y.sheaf))
    (hpush : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    {a : quasiCoherentDerivedCategory X ⥤ quasiCoherentDerivedCategory Y}
    (adj : quasiCoherentDerivedPushforward f hpush ⊣ a)
    (L : quasiCoherentDerivedCategory Y) (K : quasiCoherentDerivedCategory X)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    IsIso (sheafyTrace f DY DX hpush adj L K) := by
  obtain rfl : DY = derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf) :=
    tensorHomAdjunction_ext hDY
  obtain rfl : DX = derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf) :=
    tensorHomAdjunction_ext hDX
  exact isIso_sheafyTrace_of_isProper_of_isBoundedBelow f adj L K hK

/-- The composition formula `Rf_* ⋙ Rr_* ≅ R(f ≫ r)_*` on `D_QCoh` at the standard model,
transported from the locally small model along the comparison equivalences of the two models. -/
private noncomputable def quasiCoherentDerivedPushforwardCompIsoStandard {X Y S : Scheme.{u}}
    (f : Y ⟶ X) (rX : X ⟶ S)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace S] [QuasiSeparatedSpace S] [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact rX] [QuasiSeparated rX]
    (hpushX : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor S.Modules i).obj
        ((derivedPushforward rX).obj K.obj)).IsQuasicoherent)
    (hpushf : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent) :
    quasiCoherentDerivedPushforward f hpushf ⋙ quasiCoherentDerivedPushforward rX hpushX ≅
      quasiCoherentDerivedPushforward (f ≫ rX)
        (StandardModel.isQuasicoherent_homology_derivedPushforward (f ≫ rX)) :=
  ((StandardModel.quasiCoherentModelEquiv S).fullyFaithfulFunctor.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (StandardModel.quasiCoherentDerivedPushforwardModelIso rX) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (StandardModel.quasiCoherentDerivedPushforwardModelIso f) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (quasiCoherentDerivedPushforwardCompIsoOfQcqs f rX) ≪≫
      (StandardModel.quasiCoherentDerivedPushforwardModelIso (f ≫ rX)).symm)

/-- For `rY = f ≫ rX`, the composite `f^× ∘ r_X^×` of right adjoints of `Rf_*` and `Rr_{X*}`
agrees with the right adjoint of `Rr_{Y*}` on every object. -/
private theorem nonempty_iso_twistedInverseImage_comp {X Y S : Scheme.{u}} (f : Y ⟶ X)
    (rX : X ⟶ S) (rY : Y ⟶ S) (hfr : f ≫ rX = rY)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace S] [QuasiSeparatedSpace S] [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact rX] [QuasiSeparated rX]
    (hpushX : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor S.Modules i).obj
        ((derivedPushforward rX).obj K.obj)).IsQuasicoherent)
    (hpushf : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    {aX : quasiCoherentDerivedCategory S ⥤ quasiCoherentDerivedCategory X}
    (adjX : quasiCoherentDerivedPushforward rX hpushX ⊣ aX)
    {af : quasiCoherentDerivedCategory X ⥤ quasiCoherentDerivedCategory Y}
    (adjf : quasiCoherentDerivedPushforward f hpushf ⊣ af) (K : quasiCoherentDerivedCategory S) :
    Nonempty (af.obj (aX.obj K) ≅
      (twistedInverseImage rY (StandardModel.isQuasicoherent_homology_derivedPushforward rY)).obj
        K) := by
  subst hfr
  exact ⟨(Adjunction.rightAdjointUniq ((adjf.comp adjX).ofNatIsoLeft
    (quasiCoherentDerivedPushforwardCompIsoStandard f rX hpushX hpushf))
    (twistedInverseImageAdjunction _ _)).app K⟩

/-- **[Stacks, Tag 0BRT] at the standard model**: for `rY : Y ⟶ Spec k` proper and smooth of
relative dimension `n`, `∧^n Ω_{Y/k}[n] ≅ a(𝒪_{Spec k})`. -/
private theorem nonempty_singleFunctor_exteriorPower_iso_twistedInverseImage {k : Type u}
    [Field k] {Y : Scheme.{u}} (rY : Y ⟶ Spec (.of k)) (n : ℕ) [IsProper rY]
    [SmoothOfRelativeDimension n rY] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    Nonempty ((DerivedCategory.singleFunctor Y.Modules (-n)).obj
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials rY) n) ≅
      ((twistedInverseImage rY (StandardModel.isQuasicoherent_homology_derivedPushforward rY)).obj
        ⟨(DerivedCategory.singleFunctor _ 0).obj
            (SheafOfModules.unit (Spec (.of k)).ringCatSheaf),
          DerivedPushforward.derivedCategoryB_singleFunctor_obj _ inferInstance⟩).obj) := by
  let E := StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard Y.Modules)
    (Scheme.Modules.hasDerivedCategory Y)
  let e₀ := singleFunctorExteriorPowerIsoRelativeDualizingComplex rY n
  let e₁ := (ObjectProperty.ι _).mapIso (StandardModel.relativeDualizingComplexModelIso rY)
  let eₛ := (StacksDraft.DerivedModel.modelSingleFunctorIso
    (HasDerivedCategory.standard Y.Modules) (Scheme.Modules.hasDerivedCategory Y) (-n)).app
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials rY) n)
  exact ⟨E.fullyFaithfulFunctor.preimageIso (eₛ ≪≫ e₀ ≪≫ e₁.symm)⟩

/-! ### The right unit law of evaluation at the structure sheaf -/

private theorem rightUnitor_eq_of_kFlat (X : Scheme.{u})
    (A : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat (Stacks.SheafOfModules.ringedSite X.sheaf).O A) :
    (RingedSite.derivedTensorObjIso.{u, u+1} (Stacks.SheafOfModules.ringedSite X.sheaf)
      (DerivedCategory.Q.obj A) (RingedSite.derivedStructureSheaf _)).inv ≫
      RingedSite.derivedRightUnitorHom (Stacks.SheafOfModules.ringedSite X.sheaf)
        (DerivedCategory.Q.obj A) =
    (Stacks.RingedSpace.derivedTensorRightUnitorNatIso X.toRingedSpace).hom.app
      (DerivedCategory.Q.obj A) := by
  have hO := Stacks.SheafOfModules.isKFlat_single_unit
    (Stacks.SheafOfModules.ringedSite X.sheaf).O
  have h1 := RingedSite.derivedRightUnitorHom_eq_comparison
    (Stacks.SheafOfModules.ringedSite X.sheaf) A hA hO
  have h2 := RingedSite.derivedTensorObjIso_hom_comp_comparisonRight.{u, u+1}
    (Stacks.SheafOfModules.ringedSite X.sheaf) A _ hO
  have h3 := Stacks.Cohomology.DerivedProjectionFormula.derivedTensorRightUnitorNatIso_hom_app_q
    X.toRingedSpace A
  rw [h1, h3, Iso.inv_comp_eq, RingedSite.unitComparisonRightHom, ← h2, Category.assoc]
  rfl

private theorem eq_of_natural_of_iso {C : Type*} [Category C] (F : C ⥤ C)
    (α β : ∀ N, F.obj N ⟶ N)
    (hα : ∀ {N N' : C} (g : N ⟶ N'), F.map g ≫ α N' = α N ≫ g)
    (hβ : ∀ {N N' : C} (g : N ⟶ N'), F.map g ≫ β N' = β N ≫ g)
    {N N' : C} (e : N ≅ N') (h : α N = β N) : α N' = β N' :=
  (cancel_mono e.inv).1 (by rw [← hα, ← hβ, h])

private theorem derivedRightUnitorHom_natural (X : Scheme.{u})
    {N N' : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O))}
    (g : N ⟶ N') :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (SheafedSpace.sheaf X.toRingedSpace)).flip.obj
        ((DerivedCategory.singleFunctor (SheafOfModules (structureSheafRing X.toRingedSpace)) 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (SheafedSpace.sheaf X.toRingedSpace))))).map g ≫
      (RingedSite.derivedTensorObjIso.{u, u+1} (Stacks.SheafOfModules.ringedSite X.sheaf)
        N' (RingedSite.derivedStructureSheaf _)).inv ≫
      RingedSite.derivedRightUnitorHom (Stacks.SheafOfModules.ringedSite X.sheaf) N' =
    ((RingedSite.derivedTensorObjIso.{u, u+1} (Stacks.SheafOfModules.ringedSite X.sheaf)
        N (RingedSite.derivedStructureSheaf _)).inv ≫
      RingedSite.derivedRightUnitorHom (Stacks.SheafOfModules.ringedSite X.sheaf) N) ≫ g := by
  have h1 := NatTrans.congr_app ((RingedSite.derivedTensorFunctorIso.{u, u+1}
      (Stacks.SheafOfModules.ringedSite X.sheaf)).inv.naturality g)
    (RingedSite.derivedStructureSheaf.{u, u, u, u+1} (Stacks.SheafOfModules.ringedSite X.sheaf))
  letI := RingedSite.derivedTensorMonoidal (Stacks.SheafOfModules.ringedSite X.sheaf)
  have h2 := MonoidalCategory.rightUnitor_naturality g
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))

private theorem derivedTensorObjIso_inv_comp_derivedRightUnitorHom (X : Scheme.{u})
    (N : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O))) :
    (RingedSite.derivedTensorObjIso.{u, u+1} (Stacks.SheafOfModules.ringedSite X.sheaf) N
      (RingedSite.derivedStructureSheaf _)).inv ≫
      RingedSite.derivedRightUnitorHom (Stacks.SheafOfModules.ringedSite X.sheaf) N =
    (Stacks.RingedSpace.derivedTensorRightUnitorNatIso X.toRingedSpace).hom.app N := by
  obtain ⟨P, s, hP, hs⟩ := Stacks.SheafOfModules.exists_isKFlat_quasiIso
    (Stacks.SheafOfModules.ringedSite X.sheaf) (DerivedCategory.Q.objPreimage N)
  have hiso : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O)) s).2 hs
  exact eq_of_natural_of_iso _ (fun N => (RingedSite.derivedTensorObjIso.{u, u+1}
      (Stacks.SheafOfModules.ringedSite X.sheaf) N (RingedSite.derivedStructureSheaf _)).inv ≫
      RingedSite.derivedRightUnitorHom (Stacks.SheafOfModules.ringedSite X.sheaf) N)
    (fun N => (Stacks.RingedSpace.derivedTensorRightUnitorNatIso X.toRingedSpace).hom.app N)
    (fun g => derivedRightUnitorHom_natural X g)
    (fun g => (Stacks.RingedSpace.derivedTensorRightUnitorNatIso X.toRingedSpace).hom.naturality g)
    (asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso N)
    (rightUnitor_eq_of_kFlat X P hP)

open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi in
private theorem map_inv_comp_evaluation (X : Scheme.{u})
    (DX : TensorHomAdjunction (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)
      (Stacks.SheafOfModules.derivedSheafHom X.sheaf))
    (hDX : DX.toTensorHomBijection =
      derivedTensorHomBijection (Stacks.SheafOfModules.ringedSite X.sheaf))
    (N : DerivedCategory X.Modules) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
        ((RingedSite.derivedStructureSheafHomNatIso
          (Stacks.SheafOfModules.ringedSite X.sheaf)).app N).inv).app
        (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite X.sheaf)) ≫
      DX.evaluation
        (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite X.sheaf)) N =
    (Stacks.RingedSpace.derivedTensorRightUnitorNatIso X.toRingedSpace).hom.app N := by
  have hev : DX.evaluation
      (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite X.sheaf)) N =
      (derivedTensorHomBijection (Stacks.SheafOfModules.ringedSite X.sheaf)).evaluation
        (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite X.sheaf)) N := by
    rw [hDX]
  rw [hev]
  refine (congrArg (_ ≫ ·)
    (derivedTensorHomBijection_evaluation (Stacks.SheafOfModules.ringedSite X.sheaf)
    (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite X.sheaf)) N)).trans ?_
  have hnat := NatTrans.congr_app ((RingedSite.derivedTensorFunctorIso.{u, u+1}
      (Stacks.SheafOfModules.ringedSite X.sheaf)).inv.naturality
        ((RingedSite.derivedStructureSheafHomNatIso
          (Stacks.SheafOfModules.ringedSite X.sheaf)).app N).inv)
    (RingedSite.derivedStructureSheaf.{u, u, u, u+1} (Stacks.SheafOfModules.ringedSite X.sheaf))
  have hUR := RingedSite.derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit
    (Stacks.SheafOfModules.ringedSite X.sheaf) N
  rw [← derivedTensorObjIso_inv_comp_derivedRightUnitorHom X N, ← hUR]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hnat).trans (Category.assoc _ _ _))

/-! ### The structural unit is the transpose of the unit comparison -/

section RingedSpaceUnit

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open Stacks.Cohomology.DerivedPullbackTensor in
attribute [local instance] monoidalModules symmetricModules monoidalPreadditiveModules
  monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts abelianModulesSheafTensor liftMonoidal

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  StacksDraft.KFlat.modulePullback CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces RingedSpaceModuleAdjunction in
private theorem inv_epsilon_eq :
    inv (ε (Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex f)) =
      (HomologicalComplex.singleMapHomologicalComplex (StacksDraft.KFlat.modulePullback f)
          (ComplexShape.up ℤ) 0).hom.app (SheafOfModules.unit _) ≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          (modulePullbackObjUnitIso f).hom := by
  rw [IsIso.inv_eq_of_hom_inv_id]
  apply HomologicalComplex.to_single_hom_ext
  have hε := Stacks.Cohomology.DerivedPullbackTensor.epsilon_pullbackComplex_f_zero f
    (Stacks.Cohomology.DerivedPullbackTensor.isComparisonUnit_sheafTensor f)
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self, Category.assoc]
  simp only [Iso.inv_hom_id_assoc]
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hε).trans ?_)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact Iso.hom_inv_id _

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces RingedSpaceModuleAdjunction in
private theorem derivedPullbackSingleComparison_comp_unitIso :
    derivedPullbackSingleComparison f (SheafOfModules.unit (structureSheafRing Y)) ≫
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).map
        (modulePullbackObjUnitIso f).hom =
    (Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso f).hom := by
  have h := congrArg DerivedCategory.Q.map (inv_epsilon_eq f)
  rw [Functor.map_comp] at h
  unfold Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso
    derivedPullbackSingleComparison
  simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, Functor.mapIso_inv, asIso_inv,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]
  erw [h]
  rfl

private theorem natural_chase {AY AX HY HX DY DX : Type*} [Category* AY] [Category* AX]
    [Category* HY]
    [Category* HX] [Category* DY] [Category* DX]
    {Pst : AX ⥤ AY} {HsY : AY ⥤ HY} {HsX : AX ⥤ HX} {QhY : HY ⥤ DY} {QhX : HX ⥤ DX}
    {SY : AY ⥤ DY} {SX : AX ⥤ DX} {MPst : HX ⥤ HY} {Rf : DX ⥤ DY}
    (u : MPst ⋙ QhY ⟶ QhX ⋙ Rf) (σY : SY ≅ HsY ⋙ QhY) (σX : SX ≅ HsX ⋙ QhX)
    (hsPst : HsX ⋙ MPst ≅ Pst ⋙ HsY) {A B : AX} (φ : A ⟶ B) :
    σY.hom.app (Pst.obj A) ≫ QhY.map (hsPst.inv.app A) ≫ u.app (HsX.obj A) ≫
        Rf.map (σX.inv.app A) ≫ Rf.map (SX.map φ) =
      SY.map (Pst.map φ) ≫ σY.hom.app (Pst.obj B) ≫ QhY.map (hsPst.inv.app B) ≫
        u.app (HsX.obj B) ≫ Rf.map (σX.inv.app B) := by
  have n1 := σY.hom.naturality (Pst.map φ)
  have n2 := hsPst.inv.naturality φ
  have n3 := u.naturality (HsX.map φ)
  have n4 := σX.inv.naturality φ
  simp only [Functor.comp_map, Functor.comp_obj] at n1 n2 n3 n4
  rw [← Rf.map_comp, ← n4, Rf.map_comp, ← reassoc_of% n3, ← QhY.map_comp_assoc, ← n2,
    QhY.map_comp_assoc, reassoc_of% n1]

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces RingedSpaceModuleAdjunction in
private theorem homEquiv_derivedPullbackUnitIso :
    (derivedAdjunction f).homEquiv _ _
        (Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso f).hom =
      (DerivedCategory.singleFunctorIsoCompQh _ 0).hom.app
          (SheafOfModules.unit (structureSheafRing Y)) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.singleFunctor _ 0).map
          ((modulePullbackPushforwardAdjunction f).homEquiv _ _ (modulePullbackObjUnitIso f).hom)) ≫
        DerivedCategory.Qh.map
          (((modulePushforward f).mapHomotopyCategorySingleFunctorIso 0).inv.app
          (SheafOfModules.unit (structureSheafRing X))) ≫
        (derivedPushforwardUnit f).app ((HomotopyCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (structureSheafRing X))) ≫
        (derivedPushforward f).map ((DerivedCategory.singleFunctorIsoCompQh _ 0).inv.app
          (SheafOfModules.unit (structureSheafRing X))) := by
  rw [Adjunction.homEquiv_unit, ← derivedPullbackSingleComparison_comp_unitIso, Functor.map_comp,
    derivedPullbackSingleComparison_eq]
  have hA := unit_comp_singleComparison_of_fac (derivedAdjunction f)
    (modulePullbackPushforwardAdjunction f) (homotopyPullbackPushforwardAdjunction f)
    (derivedPullbackComparison f) (derivedPushforwardUnit f)
    (DerivedCategory.singleFunctorIsoCompQh _ 0) (DerivedCategory.singleFunctorIsoCompQh _ 0)
    ((modulePullback f).mapHomotopyCategorySingleFunctorIso 0)
    ((modulePushforward f).mapHomotopyCategorySingleFunctorIso 0) (SheafOfModules.unit _)
    (derivedAdjunction_unit_fac f _)
    (Adjunction.singleFunctor_map_unit_comp_mapHomotopyCategorySingleFunctorIso_inv
      (modulePullbackPushforwardAdjunction f) _)
  have hC := natural_chase (derivedPushforwardUnit f) (DerivedCategory.singleFunctorIsoCompQh _ 0)
    (DerivedCategory.singleFunctorIsoCompQh _ 0)
    ((modulePushforward f).mapHomotopyCategorySingleFunctorIso 0) (modulePullbackObjUnitIso f).hom
  have hN :=
    (DerivedCategory.singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y))
      0).hom.naturality
    ((modulePullbackPushforwardAdjunction f).homEquiv _ _ (modulePullbackObjUnitIso f).hom)
  rw [Adjunction.homEquiv_unit] at hN ⊢
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at hA hN hC ⊢
  erw [reassoc_of% hA, hC, reassoc_of% hN]

private theorem cup_generic {C D : Type*} [Category C] [Category D] (Rf : D ⥤ C) (TK : D ⥤ D)
    (Tm : C ⥤ C) {O : C} {LO OX LRL W : D} (η : O ⟶ Rf.obj LO) (ν : LO ⟶ OX) (Lη : LO ⟶ LRL)
    (ε : LRL ⟶ LO) (pfm : Tm.obj O ⟶ Rf.obj (TK.obj LO))
    (pfm' : Tm.obj (Rf.obj LO) ⟶ Rf.obj (TK.obj LRL))
    (c' : Tm.obj (Rf.obj LO) ⟶ Rf.obj (TK.obj LO)) (c : Tm.obj (Rf.obj OX) ⟶ Rf.obj (TK.obj OX))
    (ρX : TK.obj OX ⟶ W) (ρY : Tm.obj O ⟶ Rf.obj W)
    (hR : Tm.map (Rf.map ν) ≫ c = c' ≫ Rf.map (TK.map ν))
    (hC : c' = pfm' ≫ Rf.map (TK.map ε))
    (hN : Tm.map η ≫ pfm' = pfm ≫ Rf.map (TK.map Lη))
    (hT : Lη ≫ ε = 𝟙 _)
    (hU : pfm ≫ Rf.map (TK.map ν ≫ ρX) = ρY) :
    Tm.map (η ≫ Rf.map ν) ≫ c ≫ Rf.map ρX = ρY := by
  rw [Tm.map_comp, Category.assoc, reassoc_of% hR, hC, Category.assoc, reassoc_of% hN,
    ← Rf.map_comp, ← Rf.map_comp, ← Rf.map_comp, ← TK.map_comp_assoc, hT, TK.map_id,
    Category.id_comp, ← hU, Rf.map_comp]

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedProjectionFormula
  Stacks.DerivedTensor.RingedSite in
private theorem cup_homEquiv_unit_rightUnitor
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    ((derivedTensorProductFunctor Y.sheaf).obj ((derivedPushforward f).obj K)).map
        ((derivedAdjunction f).homEquiv _ _ (derivedPullbackUnitIso f).hom) ≫
      Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct f K (singleUnit X) ≫
        (derivedPushforward f).map
          ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app K).hom =
      ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).app
        ((derivedPushforward f).obj K)).hom := by
  have hU := Stacks.AlgebraicGeometry.ProjectionFormula.adjunctionTensorMap_unitObj_comp
    (derivedAdjunction f) _ _ (pullbackTensorComparison f)
    (fun Z => (Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).app Z)
    (fun W => (Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app W)
    (derivedPullbackUnitIso f)
    (fun u => Stacks.RingedSpace.derivedTensorRightUnitor_naturality X u)
    (rightUnitorCoherence_unitObject f) K
  rw [← projectionFormulaMap_eq, uncurry_map_id_left] at hU
  rw [Adjunction.homEquiv_unit]
  exact cup_generic (derivedPushforward f) ((derivedTensorProductFunctor X.sheaf).obj K)
    ((derivedTensorProductFunctor Y.sheaf).obj ((derivedPushforward f).obj K))
    ((derivedAdjunction f).unit.app (singleUnit Y)) (derivedPullbackUnitIso f).hom
    ((derivedPullback f).map ((derivedAdjunction f).unit.app (singleUnit Y)))
    ((derivedAdjunction f).counit.app ((derivedPullback f).obj (singleUnit Y)))
    _ _ _ _ _ _
    (Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_natural_right f K
      (derivedPullbackUnitIso f).hom)
    (Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_eq_projectionFormulaMap f K _)
    (projectionFormulaMap_natural_right f K ((derivedAdjunction f).unit.app (singleUnit Y)))
    ((derivedAdjunction f).left_triangle_components (singleUnit Y)) hU

end RingedSpaceUnit

open RingedSpaceModuleAdjunction in
private theorem homEquiv_modulePullbackObjUnitIso {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _
      (modulePullbackObjUnitIso f.toLRSHom.toShHom).hom =
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  unfold modulePullbackObjUnitIso modulePullbackPushforwardAdjunction
  simp only [asIso_hom]
  unfold SheafOfModules.pullbackObjUnitToUnit
  exact Equiv.apply_symm_apply _ _

private theorem unit_eq_homEquiv {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (DerivedCategory.singleFunctorIsoCompQh X.Modules 0).hom.app _ ≫
      DerivedCategory.Qh.map ((HomotopyCategory.singleFunctor X.Modules 0).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (HomotopyCategory.quotient _ _).map
          ((HomologicalComplex.singleMapHomologicalComplex
            (Scheme.Modules.pushforward f) _ 0).inv.app _)) ≫
      ((homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))).app
          ((HomotopyCategory.singleFunctor Y.Modules 0).obj
            (SheafOfModules.unit Y.ringCatSheaf)) ≫
      (derivedPushforward f).map
        ((DerivedCategory.singleFunctorIsoCompQh Y.Modules 0).inv.app _) =
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
        f.toLRSHom.toShHom).homEquiv _ _
      (Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso
        f.toLRSHom.toShHom).hom := by
  rw [homEquiv_derivedPullbackUnitIso, homEquiv_modulePullbackObjUnitIso,
    Functor.mapHomotopyCategorySingleFunctorIso_inv_app]
  exact congrArg (_ ≫ ·) ((congrArg (· ≫ _) (DerivedCategory.Qh.map_comp _ _)).trans
    (Category.assoc _ _ _))

private theorem hs_generic {C D : Type*} [Category C] [Category D] (T : C ⥤ C ⥤ C)
    (Rf : D ⥤ C) {O B A : C} {M Pd Ev : D} (u : O ⟶ B) (e : A ⟶ Rf.obj M)
    (c1 : (T.obj A).obj B ⟶ Rf.obj Pd) (ev0 : Pd ⟶ M) (a : Pd ⟶ Ev)
    (c2 : (T.obj (Rf.obj M)).obj B ⟶ Rf.obj Ev)
    (r2 : Ev ⟶ M) (ρ : ∀ Z, (T.obj Z).obj O ⟶ Z)
    (hev0 : ev0 = a ≫ r2)
    (hnat : c1 ≫ Rf.map a = (T.map e).app B ≫ c2)
    (hunit : (T.obj (Rf.obj M)).map u ≫ c2 ≫ Rf.map r2 = ρ (Rf.obj M))
    (hρ : (T.map e).app O ≫ ρ (Rf.obj M) = ρ A ≫ e) :
    (T.obj A).map u ≫ c1 ≫ Rf.map ev0 = ρ A ≫ e := by
  rw [hev0, Rf.map_comp, reassoc_of% hnat, reassoc_of% ((T.map e).naturality u), hunit, hρ]

open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi in
/-- From the adjunct of `s` restricted along `u`, the restriction of `s` along `u` read through
`R𝓗om(𝒪_X, -) ≅ id`. -/
private theorem key_core {X : Scheme.{u}}
    (DX : TensorHomAdjunction (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)
      (Stacks.SheafOfModules.derivedSheafHom X.sheaf))
    {OX A B N : DerivedCategory X.Modules}
    (ρ : ∀ Z : DerivedCategory X.Modules,
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj Z).obj OX ⟶ Z)
    (hρ : ∀ {Z Z' : DerivedCategory X.Modules} (g : Z ⟶ Z'),
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map g).app OX ≫
        ρ Z' = ρ Z ≫ g)
    (hρA : IsIso (ρ A))
    (εX : ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op OX)).obj N ≅ N)
    (hEX : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
        εX.inv).app OX ≫ DX.toTensorHomBijection.evaluation OX N = ρ N)
    (s : A ⟶ ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op B)).obj N)
    (u : OX ⟶ B) (g' : A ⟶ N)
    (hs : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj A).map u ≫
      DX.homEquiv A B N s = ρ A ≫ g') :
    s ≫ ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map u.op).app N ≫ εX.hom = g' := by
  let T := Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf
  let k := s ≫ ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map u.op).app N
  haveI : Epi (ρ A) := @IsIso.epi_of_iso _ _ _ _ _ hρA
  have h1 : DX.homEquiv A OX N k = (T.map k).app OX ≫ DX.toTensorHomBijection.evaluation OX N := by
    have h := DX.homEquiv_naturality_source k (𝟙 _)
    erw [Category.comp_id] at h
    exact h
  have h2 : DX.homEquiv A OX N k = (T.obj A).map u ≫ DX.homEquiv A B N s :=
    DX.homEquiv_naturality_middle u s
  have h3 : (T.map εX.hom).app OX ≫ ρ N = DX.toTensorHomBijection.evaluation OX N := by
    rw [← hEX]
    erw [← NatTrans.comp_app_assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  have h4 : ρ A ≫ (k ≫ εX.hom) = (T.map k).app OX ≫ DX.toTensorHomBijection.evaluation OX N := by
    erw [← hρ, Functor.map_comp, NatTrans.comp_app, Category.assoc, h3]
  have h5 : ρ A ≫ (k ≫ εX.hom) = ρ A ≫ g' := by
    rw [h4, ← h1, h2, hs]
  exact (Category.assoc _ _ _).symm.trans ((cancel_epi (ρ A)).1 h5)

open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi in
/-- The canonical map `Rf_* R𝓗om(𝒪_Y, M) ⟶ R𝓗om(Rf_*𝒪_Y, Rf_*M)`, restricted along the
structural unit `u : 𝒪_X ⟶ Rf_*𝒪_Y` and read through `R𝓗om(𝒪_X, -) ≅ id`, is `Rf_*` of
`R𝓗om(𝒪_Y, M) ≅ M`. -/
private theorem derivedSheafHomPushforward_comp_unit {X Y : Scheme.{u}} (f : Y ⟶ X)
    (DX : TensorHomAdjunction (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)
      (Stacks.SheafOfModules.derivedSheafHom X.sheaf))
    (DY : TensorHomAdjunction (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)
      (Stacks.SheafOfModules.derivedSheafHom Y.sheaf))
    (hDX : DX.toTensorHomBijection =
      derivedTensorHomBijection (Stacks.SheafOfModules.ringedSite X.sheaf))
    (hDY : DY.toTensorHomBijection =
      derivedTensorHomBijection (Stacks.SheafOfModules.ringedSite Y.sheaf))
    (M : DerivedCategory Y.Modules) :
    derivedSheafHomPushforward f DY DX
        ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit Y.ringCatSheaf)) M ≫
      ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map
          ((DerivedCategory.singleFunctorIsoCompQh X.Modules 0).hom.app _ ≫
            DerivedCategory.Qh.map ((HomotopyCategory.singleFunctor X.Modules 0).map
              (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
              (HomotopyCategory.quotient _ _).map
                ((HomologicalComplex.singleMapHomologicalComplex
                  (Scheme.Modules.pushforward f) _ 0).inv.app _)) ≫
            ((homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
              (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))).app
                ((HomotopyCategory.singleFunctor Y.Modules 0).obj
                  (SheafOfModules.unit Y.ringCatSheaf)) ≫
            (derivedPushforward f).map
              ((DerivedCategory.singleFunctorIsoCompQh Y.Modules 0).inv.app _)).op).app
        ((derivedPushforward f).obj M) ≫
      ((RingedSite.derivedStructureSheafHomNatIso
          (Stacks.SheafOfModules.ringedSite X.sheaf)).app ((derivedPushforward f).obj M)).hom =
    (derivedPushforward f).map ((RingedSite.derivedStructureSheafHomNatIso
        (Stacks.SheafOfModules.ringedSite Y.sheaf)).app M).hom := by
  let OX := (DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)
  let O' := (DerivedCategory.singleFunctor Y.Modules 0).obj (SheafOfModules.unit Y.ringCatSheaf)
  let u : OX ⟶ (derivedPushforward f).obj O' :=
    ((DerivedCategory.singleFunctorIsoCompQh X.Modules 0).hom.app _ ≫
      DerivedCategory.Qh.map ((HomotopyCategory.singleFunctor X.Modules 0).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (HomotopyCategory.quotient _ _).map
          ((HomologicalComplex.singleMapHomologicalComplex
            (Scheme.Modules.pushforward f) _ 0).inv.app _)) ≫
      ((homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))).app
          ((HomotopyCategory.singleFunctor Y.Modules 0).obj
            (SheafOfModules.unit Y.ringCatSheaf)) ≫
      (derivedPushforward f).map
        ((DerivedCategory.singleFunctorIsoCompQh Y.Modules 0).inv.app _))
  let T := Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf
  let ρ : ∀ Z : DerivedCategory X.Modules, (T.obj Z).obj OX ⟶ Z := fun Z =>
    (Stacks.RingedSpace.derivedTensorRightUnitorNatIso X.toRingedSpace).hom.app Z
  have hρ : ∀ {Z Z' : DerivedCategory X.Modules} (g : Z ⟶ Z'),
      (T.map g).app OX ≫ ρ Z' = ρ Z ≫ g := fun g =>
    (Stacks.RingedSpace.derivedTensorRightUnitorNatIso X.toRingedSpace).hom.naturality g
  have hρA : ∀ Z, IsIso (ρ Z) := fun Z =>
    Iso.isIso_hom ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X.toRingedSpace).app Z)
  let εX : ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op OX)).obj
      ((derivedPushforward f).obj M) ≅ (derivedPushforward f).obj M :=
    (RingedSite.derivedStructureSheafHomNatIso
      (Stacks.SheafOfModules.ringedSite X.sheaf)).app ((derivedPushforward f).obj M)
  have hEX : (T.map εX.inv).app OX ≫ DX.toTensorHomBijection.evaluation OX
      ((derivedPushforward f).obj M) = ρ ((derivedPushforward f).obj M) :=
    map_inv_comp_evaluation X DX hDX _
  let H := ((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op O')).obj M
  let εY : H ≅ M := (RingedSite.derivedStructureSheafHomNatIso
      (Stacks.SheafOfModules.ringedSite Y.sheaf)).app M
  have hEY := map_inv_comp_evaluation Y DY hDY M
  have hev' : DY.toTensorHomBijection.evaluation O' M =
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).map εY.hom).app O' ≫
        (Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y.toRingedSpace).hom.app M := by
    rw [← hEY]
    erw [← NatTrans.comp_app_assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
    rfl
  have hnatL :
      Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct f.toLRSHom.toShHom H O' ≫
      (derivedPushforward f).map
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).map
          εY.hom).app O') =
      (T.map ((derivedPushforward f).map εY.hom)).app ((derivedPushforward f).obj O') ≫
        Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct f.toLRSHom.toShHom M O' :=
    (Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_natural_left
      f.toLRSHom.toShHom εY.hom O').symm
  have hunit : (T.obj ((derivedPushforward f).obj M)).map u ≫
      Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct f.toLRSHom.toShHom M O' ≫
        (derivedPushforward f).map
          ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y.toRingedSpace).hom.app M) =
      ρ ((derivedPushforward f).obj M) := by
    have h := unit_eq_homEquiv f
    have h2 := cup_homEquiv_unit_rightUnitor f.toLRSHom.toShHom M
    simp only [u]
    rw [h]
    exact h2
  have hs : (T.obj ((derivedPushforward f).obj H)).map u ≫
      DX.homEquiv ((derivedPushforward f).obj H) ((derivedPushforward f).obj O')
        ((derivedPushforward f).obj M) (derivedSheafHomPushforward f DY DX O' M) =
      ρ ((derivedPushforward f).obj H) ≫ (derivedPushforward f).map εY.hom := by
    refine (congrArg (_ ≫ ·) (derivedSheafHomPushforward_homEquiv f DY DX O' M)).trans ?_
    exact hs_generic T (derivedPushforward f) u ((derivedPushforward f).map εY.hom)
      (Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct f.toLRSHom.toShHom H O')
      (DY.toTensorHomBijection.evaluation O' M)
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).map εY.hom).app O')
      (Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct f.toLRSHom.toShHom M O')
      ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y.toRingedSpace).hom.app M)
      ρ hev' hnatL hunit (hρ _)
  exact key_core DX ρ hρ (hρA _) εX hEX (derivedSheafHomPushforward f DY DX O' M) u
    ((derivedPushforward f).map εY.hom) hs

private theorem tail_generic {C : Type*} [Category C] {P Q R S T' V W : C} (d : P ⟶ Q)
    (hc : Q ⟶ R) (hu : R ⟶ S) (eD : S ⟶ W) (hu' : Q ⟶ T') (hc' : T' ⟶ S) (eM : T' ⟶ V)
    (c : V ⟶ W) (g : P ⟶ V) (n1 : hc ≫ hu = hu' ≫ hc') (n2 : hc' ≫ eD = eM ≫ c)
    (hk : d ≫ hu' ≫ eM = g) : g ≫ c = (d ≫ hc) ≫ hu ≫ eD := by
  rw [← hk]
  simp only [Category.assoc]
  rw [reassoc_of% n1, n2]

open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi in
/-- The dual of the structural unit, after the sheafy trace, is `Rf_*` of `R𝓗om(𝒪_Y, -) ≅ id`
followed by the given map `c`. -/
private theorem trace_comp_dual_unit {X Y : Scheme.{u}} (f : Y ⟶ X)
    (DX : TensorHomAdjunction (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)
      (Stacks.SheafOfModules.derivedSheafHom X.sheaf))
    (DY : TensorHomAdjunction (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)
      (Stacks.SheafOfModules.derivedSheafHom Y.sheaf))
    (hDX : DX.toTensorHomBijection =
      derivedTensorHomBijection (Stacks.SheafOfModules.ringedSite X.sheaf))
    (hDY : DY.toTensorHomBijection =
      derivedTensorHomBijection (Stacks.SheafOfModules.ringedSite Y.sheaf))
    (Mo : DerivedCategory Y.Modules) (D : DerivedCategory X.Modules)
    (c : (derivedPushforward f).obj Mo ⟶ D) :
    (derivedPushforward f).map ((RingedSite.derivedStructureSheafHomNatIso
        (Stacks.SheafOfModules.ringedSite Y.sheaf)).app Mo).hom ≫ c =
      (derivedSheafHomPushforward f DY DX
          ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit Y.ringCatSheaf)) Mo ≫
        ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op ((derivedPushforward f).obj
          ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit Y.ringCatSheaf))))).map c) ≫
      ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map
          ((DerivedCategory.singleFunctorIsoCompQh X.Modules 0).hom.app _ ≫
            DerivedCategory.Qh.map ((HomotopyCategory.singleFunctor X.Modules 0).map
              (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
              (HomotopyCategory.quotient _ _).map
                ((HomologicalComplex.singleMapHomologicalComplex
                  (Scheme.Modules.pushforward f) _ 0).inv.app _)) ≫
            ((homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
              (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))).app
                ((HomotopyCategory.singleFunctor Y.Modules 0).obj
                  (SheafOfModules.unit Y.ringCatSheaf)) ≫
            (derivedPushforward f).map
              ((DerivedCategory.singleFunctorIsoCompQh Y.Modules 0).inv.app _)).op).app D ≫
      ((RingedSite.derivedStructureSheafHomNatIso
          (Stacks.SheafOfModules.ringedSite X.sheaf)).app D).hom := by
  have hk := derivedSheafHomPushforward_comp_unit f DX DY hDX hDY Mo
  have n1 := ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map
          ((DerivedCategory.singleFunctorIsoCompQh X.Modules 0).hom.app _ ≫
            DerivedCategory.Qh.map ((HomotopyCategory.singleFunctor X.Modules 0).map
              (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
              (HomotopyCategory.quotient _ _).map
                ((HomologicalComplex.singleMapHomologicalComplex
                  (Scheme.Modules.pushforward f) _ 0).inv.app _)) ≫
            ((homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
              (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))).app
                ((HomotopyCategory.singleFunctor Y.Modules 0).obj
                  (SheafOfModules.unit Y.ringCatSheaf)) ≫
            (derivedPushforward f).map
              ((DerivedCategory.singleFunctorIsoCompQh Y.Modules 0).inv.app _)).op).naturality c
  have n2 := (RingedSite.derivedStructureSheafHomNatIso
    (Stacks.SheafOfModules.ringedSite X.sheaf)).hom.naturality c
  exact tail_generic _ _ _ _ _ _ _ _ _ n1 n2 hk

/-- **Proper duality for a smooth projective birational source.** Let `f : Y ⟶ X` be a projective
birational morphism of normal projective varieties of dimension `n` over an algebraically closed
field `k` of characteristic zero, with structure morphisms `r_X` and `r_Y = f ≫ r_X`, `Y` smooth.
Let `r_X^×` and `f^×` be right adjoints of `Rr_{X*}` and `Rf_*` on complexes with quasi-coherent
cohomology. Put `D_X = r_X^× 𝒪_{Spec k}` and `ω_Y = ∧^n Ω_{Y/k}`. Then `D_X` is a dualizing
complex, biduality with respect to `D_X` holds on objects with coherent cohomology, and there are
an isomorphism `ψ : ω_Y[n] ≅ f^× D_X` and an isomorphism `φ : R𝓗om(Rf_* 𝒪_Y, D_X) ≅ Rf_*(ω_Y[n])`,
the sheafy trace composed with `R𝓗om(𝒪_Y, -) ≅ id` and `ψ⁻¹`, under which the dual of the
structural unit `𝒪_X ⟶ Rf_* 𝒪_Y`, followed by `R𝓗om(𝒪_X, D_X) ≅ D_X`, is the proper trace
`Rf_* ψ` followed by the counit `Rf_* f^× D_X ⟶ D_X`. -/
@[mmp "lem_mmp_projective_birational_duality_interface"]
public theorem dual_unit_eq_trace_of_isBirationalMorphism {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{u}}
    (rX : X ⟶ Spec (.of k)) (rY : Y ⟶ Spec (.of k)) (f : Y ⟶ X) (n : ℕ)
    [IsProjectiveVariety k rX] [IsProjectiveVariety k rY] [IsNormal X] [IsNormal Y]
    [SmoothOfRelativeDimension n rY] (hX : topologicalKrullDim X = n)
    (hfr : f ≫ rX = rY) (hf : IsProjectiveMorphism f) (hbir : MMP.Mori.IsBirationalMorphism f) :
    haveI : IsProper f := isProper_of_isProjectiveMorphism f hf
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace rX
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated rX
    haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace rY
    haveI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated rY
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian rX
    let hpushX : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
        ((DerivedCategory.homologyFunctor (Spec (.of k)).Modules i).obj
          ((derivedPushforward rX).obj K.obj)).IsQuasicoherent := fun K i ↦
      AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs
        rX K.obj K.2 i
    let hpushf : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
        ((DerivedCategory.homologyFunctor X.Modules i).obj
          ((derivedPushforward f).obj K.obj)).IsQuasicoherent := fun K i ↦
      AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs
        f K.obj K.2 i
    let 𝒪k : quasiCoherentDerivedCategory (Spec (.of k)) :=
      ⟨(DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit (Spec (.of k)).ringCatSheaf),
        DerivedPushforward.derivedCategoryB_singleFunctor_obj _ inferInstance⟩
    let 𝒪Y : quasiCoherentDerivedCategory Y :=
      ⟨(DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit Y.ringCatSheaf),
        DerivedPushforward.derivedCategoryB_singleFunctor_obj _ inferInstance⟩
    ∀ (DX : Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)
        (Stacks.SheafOfModules.derivedSheafHom X.sheaf))
      (DY : Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)
        (Stacks.SheafOfModules.derivedSheafHom Y.sheaf)),
      DX.toTensorHomBijection =
        Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomBijection
          (Stacks.SheafOfModules.ringedSite X.sheaf) →
      DY.toTensorHomBijection =
        Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomBijection
          (Stacks.SheafOfModules.ringedSite Y.sheaf) →
    ∀ {aX : quasiCoherentDerivedCategory (Spec (.of k)) ⥤ quasiCoherentDerivedCategory X}
      (adjX : quasiCoherentDerivedPushforward rX
        hpushX ⊣ aX)
      {af : quasiCoherentDerivedCategory X ⥤ quasiCoherentDerivedCategory Y}
      (adjf : quasiCoherentDerivedPushforward f
        hpushf ⊣ af),
    IsDualizingComplex (aX.obj 𝒪k).obj ∧
    (∀ L : DerivedCategory X.Modules,
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent) →
      IsIso (RingedSite.derivedBiduality (Stacks.SheafOfModules.ringedSite X.sheaf)
        (aX.obj 𝒪k).obj L)) ∧
    ∃ (ψ : (DerivedCategory.singleFunctor Y.Modules (-n)).obj
          (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials rY) n) ≅
        (af.obj (aX.obj 𝒪k)).obj)
      (φ : ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
          (op ((derivedPushforward f).obj 𝒪Y.obj))).obj
            (aX.obj 𝒪k).obj ≅
        (derivedPushforward f).obj ((DerivedCategory.singleFunctor Y.Modules (-n)).obj
          (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials rY) n))),
      sheafyTrace f
          DY DX
          hpushf adjf
          𝒪Y
          (aX.obj 𝒪k) ≫
          φ.hom =
        (derivedPushforward f).map
          (((RingedSite.derivedStructureSheafHomNatIso
              (Stacks.SheafOfModules.ringedSite Y.sheaf)).app
            (af.obj (aX.obj 𝒪k)).obj).hom ≫
            ψ.inv) ∧
      φ.hom ≫ (derivedPushforward f).map ψ.hom ≫
          (ObjectProperty.ι _).map (adjf.counit.app
            (aX.obj 𝒪k)) =
        ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map
          ((DerivedCategory.singleFunctorIsoCompQh X.Modules 0).hom.app _ ≫
            DerivedCategory.Qh.map ((HomotopyCategory.singleFunctor X.Modules 0).map
              (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
              (HomotopyCategory.quotient _ _).map
                ((HomologicalComplex.singleMapHomologicalComplex
                  (Scheme.Modules.pushforward f) _ 0).inv.app _)) ≫
            ((homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
              (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))).app
                ((HomotopyCategory.singleFunctor Y.Modules 0).obj
                  (SheafOfModules.unit Y.ringCatSheaf)) ≫
            (derivedPushforward f).map
              ((DerivedCategory.singleFunctorIsoCompQh Y.Modules 0).inv.app _)).op).app
          (aX.obj 𝒪k).obj ≫
        ((RingedSite.derivedStructureSheafHomNatIso
          (Stacks.SheafOfModules.ringedSite X.sheaf)).app
            (aX.obj 𝒪k).obj).hom := by
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace rX
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated rX
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace rY
  haveI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated rY
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian rX
  intro hpushX hpushf 𝒪k 𝒪Y DX DY hDX hDY aX adjX af adjf
  haveI : IsNoetherian X := isNoetherian_of_isProper rX
  haveI : IsNoetherian Y := isNoetherian_of_isProper rY
  have hO : IsDualizingComplex 𝒪k.obj :=
    (isDualizingComplex_singleFunctor_model_iff (Scheme.Modules.hasDerivedCategory _) _ 0 _).2
      (Stacks.PurityRamification.isDualizingComplex_derivedStructureSheaf_spec k)
  have hDXd : Stacks.Duality.IsDualizingComplex (aX.obj 𝒪k).obj :=
    Stacks.Duality.isDualizingComplex_of_iso ((ObjectProperty.ι _).mapIso
      ((adjX.rightAdjointUniq (twistedInverseImageAdjunction rX hpushX)).symm.app 𝒪k))
      (isDualizingComplex_properRightAdjoint_obj rX 𝒪k hO)
  refine ⟨hDXd, fun L hL ↦ isIso_derivedBiduality_of_isDualizingComplex _ L hDXd hL, ?_⟩
  set ω := (DerivedCategory.singleFunctor Y.Modules (-n)).obj
    (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials rY) n)
  set DXo := aX.obj 𝒪k
  have hψ : Nonempty (ω ≅ (af.obj DXo).obj) := by
    obtain ⟨e₁⟩ := nonempty_singleFunctor_exteriorPower_iso_twistedInverseImage rY n
    obtain ⟨e₂⟩ := nonempty_iso_twistedInverseImage_comp f rX rY hfr hpushX hpushf adjX adjf 𝒪k
    exact ⟨e₁ ≪≫ (ObjectProperty.ι _).mapIso e₂.symm⟩
  have hst : IsIso (sheafyTrace f DY DX hpushf adjf 𝒪Y DXo) :=
    isIso_sheafyTrace_of_toTensorHomBijection f DX DY hDX hDY hpushf adjf 𝒪Y DXo
      (Stacks.Duality.isBoundedBelow_of_isDualizingComplex _ hDXd)
  obtain ⟨ψ⟩ := hψ
  set ε := (RingedSite.derivedStructureSheafHomNatIso
    (Stacks.SheafOfModules.ringedSite Y.sheaf)).app (af.obj DXo).obj
  set st := sheafyTrace f DY DX hpushf adjf 𝒪Y DXo
  let σ : _ ≅ _ := @asIso _ _ _ _ st hst
  have hcomp : (derivedPushforward f).map (ε.hom ≫ ψ.inv) ≫ (derivedPushforward f).map ψ.hom =
      (derivedPushforward f).map ε.hom :=
    ((derivedPushforward f).map_comp _ _).symm.trans (congrArg (derivedPushforward f).map
      ((Category.assoc _ _ _).trans ((congrArg (ε.hom ≫ ·) ψ.inv_hom_id).trans
        (Category.comp_id _))))
  refine ⟨ψ, σ.symm ≪≫ (derivedPushforward f).mapIso (ε ≪≫ ψ.symm),
    σ.hom_inv_id_assoc _, (Category.assoc _ _ _).trans ((Iso.inv_comp_eq σ).2 ?_)⟩
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hcomp).trans
    (trace_comp_dual_unit f DX DY hDX hDY (af.obj DXo).obj DXo.obj
      ((ObjectProperty.ι _).map (adjf.counit.app DXo))))

end MMP.Duality

end
