module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.BranchCounts
public import MMP.AlgebraicGeometry.MMP.Fourfold.EtaleDatum
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicTopology.ComplexVectorBundle.FirstChernClass
public import MMP.AlgebraicGeometry.Modules.SquareZeroInvertibleLift
public import MMP.RingTheory.Henselian.ArtinApproximation
import MMP.AlgebraicGeometry.MMP.Fourfold.AffineBaseRegularGeneration
import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import MMP.AlgebraicGeometry.Curves.Maps.TwoStageObstruction
import MMP.AlgebraicGeometry.Intersection.InvertibleSheafCurveDegree
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Cohomology.Duality.SmoothSerreDuality
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.AlgebraicGeometry.Morphisms.Etale.HenselizationColimit
import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Preimage
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.EtaleNeighbourhoodTerminal
import MMP.AlgebraicGeometry.Divisor.ProductLineQFactorial
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.FibreChernClassSpan
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleEmbedding
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.FibreH2Vanishing
import MMP.AlgebraicGeometry.Resolution.EtaleBaseChange
import MMP.AlgebraicGeometry.Morphisms.ProductWithLine
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.AlgebraicGeometry.Dimension.ResidueTrdeg

/-!
# Line bundles near the closed fibre of a threefold point setting

Let `(Y, π, y)` be a threefold point setting (`MMP.Fourfold.IsThreefoldPointSetting`): `Y` a
normal projective `ℚ`-factorial complex threefold with `(Y, 0)` terminal, `π : Ỹ ⟶ Y` a
projective resolution which is an isomorphism over the smooth locus, and `y` a closed singular
point. Write `A = 𝒪_{Y,y}` with maximal ideal `𝔪`, completion `Â` and henselization `Aʰ`,
`Z = Ỹ ×_Y Spec A`, `F_n = Z ×_A A/𝔪^{n+1}` (`MMP.Fourfold.pointSettingThickening`) and
`F_y = Ỹ ×_Y Spec κ(y)` (`MMP.Fourfold.pointSettingFibre`), so that `F_y ≅ F_0`.

The scheme fibre `F_y` has `H²(F_y, 𝒪) = 0`, and its rational second cohomology is spanned by
first Chern classes of line bundles. The vanishing of `H²(𝒪)` lets every line bundle on `F_0`
lift step by step along the square-zero thickenings `F_n ⊆ F_{n+1}`; Grothendieck existence
algebraizes the compatible system to `Z ×_A Â`; Artin approximation moves it to `Z ×_A Aʰ`; and
`Spec Aʰ` being the limit of the affine elementary étale neighbourhoods of `(Y, y)`, the bundles
descend to one such neighbourhood `(U, u)`. Finally, for an open `A ⊆ ℙ¹`, the product `U × A`
with the pulled-back bundles is a local étale datum for the product setting `Y × ℙ¹` along the
curve `{y} × ℙ¹`, and a small `ℚ`-factorial modification of `U` induces one of `U × A`.

## Main results

All in the namespace `MMP.Fourfold`.

* `IsThreefoldPointSetting.subsingleton_cohomologyOverField_two_and_span_firstChernClass`:
  `H²(F_y, 𝒪_{F_y}) = 0`, and `H²(F_y; ℚ)` is spanned by the classes `c₁(M)` of invertible
  modules `M` on `F_y`.
* `IsThreefoldPointSetting.exists_isInvertibleModule_pullback_iso`: every
  invertible sheaf on `F_0` extends to a compatible system on the `F_n`.
* `IsThreefoldPointSetting.exists_isInvertibleModule_pullback_adicCompletion_iso`:
  every invertible sheaf on `F_0` extends to `Z ×_A Â`.
* `IsThreefoldPointSetting.exists_isInvertibleModule_pullback_henselization_iso`:
  every family of invertible sheaves on `F_0` extends to `Z ×_A Aʰ`.
* `IsThreefoldPointSetting.exists_elementaryEtaleNeighborhood_isInvertible`: line
  bundles on `F_y` extend to `Ỹ ×_Y U` for an elementary étale neighbourhood `(U, u)` of
  `(Y, y)`, `U` a normal integral quasi-projective threefold.
* `IsThreefoldPointSetting.exists_localEtaleDatum_prod`: the product local étale
  datum and the product small model.

## Implementation notes

* The fibre `F_y` is a complex scheme through `F_y ⟶ Ỹ ⟶ Y ⟶ Spec ℂ`. Its coherent cohomology
  is `AlgebraicGeometry.cohomologyOverField` of the structure sheaf; vanishing is stated as
  `Subsingleton`, which does not depend on the scalars. Rational cohomology is the singular
  cohomology of the complex points (`MMP.Analytic.analyticSingularCohomology`), and the rational
  first Chern class of `M` is `MMP.Analytic.algebraicFirstChernClass M` carried to `ℚ` by
  `MMP.Analytic.singularCohomology.mapCoeff`.
* Restrictions are module pullbacks (`AlgebraicGeometry.Scheme.Modules.pullback`) along the
  canonical morphisms of fibre products: induced by `Ideal.Quotient.factor` along the tower, by
  `AdicCompletion.evalₐ 𝔪 1` to the completion, by an `A`-algebra map `Aʰ →ₐ[A] A/𝔪` (which
  exists and is unique) to the henselization, and by `MMP.Fourfold.localEtaleFibreMap` to an
  étale neighbourhood. The henselization is any `Aʰ` with
  `IsLocalRing.IsHenselization A (IsLocalRing.ResidueField A) Aʰ`.
* Families of line bundles are indexed by arbitrary types (finite where descent to one étale
  neighbourhood needs it).
* The affine chart `𝔸¹ ⊆ ℙ¹` of the source is generalised to any open immersion `j : A ⟶ ℙ¹`.
  A local étale datum is data; the conclusion of `exists_localEtaleDatum_prod` asserts the
  elementary étale neighbourhood structure on `(U × A, η', q)` and then the remaining fields of
  `MMP.Fourfold.LocalEtaleDatum`.

## References

* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 07QZ](https://stacks.math.columbia.edu/tag/07QZ)
* [Stacks Project, Tag 04HY](https://stacks.math.columbia.edu/tag/04HY)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 0C6R](https://stacks.math.columbia.edu/tag/0C6R)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

/-! ### Cohomology of the closed fibre -/

section ClosedFibre

open MMP.Analytic

open MMP MMP.SingularCochain in
/-- Change of coefficients `ℤ → ℚ` commutes with pullback of singular cohomology classes. -/
private theorem mapCoeff_map {X' X : TopCat.{0}} (g : X' ⟶ X)
    (c : singularCohomology ℤ X 2) :
    singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
        ((MMP.relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) g (A' := Set.univᶜ)
          (A := Set.univᶜ) (fun _ hx ↦ (hx (Set.mem_univ _)).elim) ((2 : ℕ) : ℤ)).hom c) =
      (rationalCohomologyMap g 2).hom (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 c) := by
  have e : ∀ {Z : TopCat.{0}} (x : singularCohomology ℤ Z 2),
      relativeSingularCohomologyEquiv ℚ (Set.univᶜ : Set Z) 2
          (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 x) =
        singularCohomology.relCohomologyMap (Int.castRingHom ℚ) _ 2
          (relativeSingularCohomologyEquiv ℤ _ 2 x) := fun x ↦ by
    simp only [singularCohomology.mapCoeff, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.apply_symm_apply]
  have h1 := relativeSingularCohomologyEquiv_map (R := ℚ) g (A' := (Set.univᶜ : Set X'))
    (A := (Set.univᶜ : Set X)) (fun _ hx ↦ (hx (Set.mem_univ _)).elim) 2
    (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 c)
  have h2 := relativeSingularCohomologyEquiv_map (R := ℤ) g (A' := (Set.univᶜ : Set X'))
    (A := (Set.univᶜ : Set X)) (fun _ hx ↦ (hx (Set.mem_univ _)).elim) 2 c
  apply (relativeSingularCohomologyEquiv ℚ (Set.univᶜ : Set X') 2).injective
  refine (e _).trans (Eq.trans ?_ h1.symm)
  rw [h2, e]
  generalize relativeSingularCohomologyEquiv ℤ _ 2 c = z
  induction z using Submodule.Quotient.induction_on
  rfl

/-- `H²(𝒪) = 0` passes along an isomorphism of schemes. -/
private theorem subsingleton_H_two_of_iso {X X' : Scheme.{0}} (e : X ≅ X')
    (h : Subsingleton (Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (SheafOfModules.unit X.ringCatSheaf)) 2)) :
    Subsingleton (((SheafOfModules.evaluation X'.ringCatSheaf (Opposite.op ⊤)).rightDerived 2).obj
      (SheafOfModules.unit X'.ringCatSheaf)) := by
  have h0 := (Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH
    X 2 (SheafOfModules.unit X.ringCatSheaf)).2 h
  have hc : IsIso e.inv.c := PresheafedSpace.c_isIso_of_iso e.inv.toPshHom
  have hiso := isIso_unitToPushforwardObjUnit_of_isIso_c e.inv hc
  have h1 : IsZero (Hgroup X.ringCatSheaf ⊤ 2
      ((Scheme.Modules.pushforward e.inv).obj (SheafOfModules.unit X'.ringCatSheaf))) :=
    ((Hfunctor X.ringCatSheaf ⊤ 2).mapIso
      (@asIso _ _ _ _ (SheafOfModules.unitToPushforwardObjUnit e.inv.toRingCatSheafHom)
        hiso)).isZero_iff.1 h0
  have h2 := (isZero_Hgroup_pushforward_iff e.inv (SheafOfModules.unit X'.ringCatSheaf)
    inferInstance 2).1 h1
  exact ModuleCat.subsingleton_of_isZero <|
    (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    X'.ringCatSheaf ⊤ 2 _).2 h2

/-- The rational first Chern classes of invertible modules span `H²(X^an; ℚ)` as soon as they do
on an isomorphic scheme over `ℂ`. -/
private theorem span_firstChernClass_eq_top_of_iso {X X' : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [X'.Over (Spec (.of ℂ))] (e : X ≅ X')
    (he : e.hom ≫ (X' ↘ Spec (.of ℂ)) = X ↘ Spec (.of ℂ))
    (h : Submodule.span ℚ
      {c : analyticSingularCohomology ℚ (X ↘ Spec (.of ℂ)) 2 |
        ∃ (M : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M),
          singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass M) = c} =
      ⊤) :
    Submodule.span ℚ
      {c : analyticSingularCohomology ℚ (X' ↘ Spec (.of ℂ)) 2 |
        ∃ (M : X'.Modules) (_ : SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 M),
          c = singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass M)} =
      ⊤ := by
  have he' : e.inv ≫ (X ↘ Spec (.of ℂ)) = X' ↘ Spec (.of ℂ) := by
    rw [← he, Iso.inv_hom_id_assoc]
  let g := ComplexPoints.analyticMap e.inv he'
  let g' := ComplexPoints.analyticMap e.hom he
  have hgg : g ≫ g' = 𝟙 _ := by
    rw [ComplexPoints.analyticMap_comp]
    ext x
    change x.hom ≫ e.inv ≫ e.hom = x.hom
    rw [Iso.inv_hom_id, Category.comp_id]
  rw [eq_top_iff]
  intro z _
  have hz : z = (rationalCohomologyMap g 2).hom ((rationalCohomologyMap g' 2).hom z) := by
    rw [← ModuleCat.comp_apply, ← rationalCohomologyMap_comp, hgg, rationalCohomologyMap_id]
    rfl
  have hmap := Submodule.mem_map_of_mem (f := (rationalCohomologyMap g 2).hom)
    (h ▸ Submodule.mem_top : (rationalCohomologyMap g' 2).hom z ∈ _)
  rw [Submodule.map_span, ← hz] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨c, ⟨M, hM, rfl⟩, rfl⟩
  refine ⟨(Scheme.Modules.pullback e.inv).obj M, inferInstance, ?_⟩
  rw [algebraicFirstChernClass_pullback e.inv g (fun _ ↦ rfl) M]
  exact (mapCoeff_map g _).symm

/-- For a threefold point setting `(Y, π, y)`, the scheme fibre `F_y = Ỹ ×_Y Spec κ(y)`, a complex
scheme through `F_y ⟶ Ỹ ⟶ Y ⟶ Spec ℂ`, has `H²(F_y, 𝒪_{F_y}) = 0`, and the rational first Chern
classes `c₁(M)` of invertible modules `M` on `F_y` span `H²(F_y^an; ℚ)`. -/
@[mmp "lem_mmp_indexb_closed_fibre_cohomology"]
public theorem IsThreefoldPointSetting.subsingleton_cohomologyOverField_two_and_span_firstChernClass
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {y : Y} (h : IsThreefoldPointSetting sY π y) :
    letI : (pointSettingFibre π y).Over (Spec (.of ℂ)) :=
      ⟨pullback.fst π (Y.fromSpecResidueField y) ≫ π ≫ sY⟩
    Subsingleton (cohomologyOverField ℂ (pointSettingFibre π y ↘ Spec (.of ℂ))
        (SheafOfModules.unit (pointSettingFibre π y).ringCatSheaf) 2) ∧
      Submodule.span ℚ
        {c : analyticSingularCohomology ℚ (pointSettingFibre π y ↘ Spec (.of ℂ)) 2 |
          ∃ (M : (pointSettingFibre π y).Modules)
            (_ : SheafOfModules.IsInvertible (pointSettingFibre π y).presheaf
              (pointSettingFibre π y).ringCatSheaf.2 M),
            c = singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass M)} =
        ⊤ := by
  obtain ⟨⟨_, _, _, T, hT, hLS⟩, -, -, -, -⟩ := h.isLocalSetting_pullback_projectiveLine
  have hdim := h.topologicalKrullDim_pointSettingFibre_le_two
  -- a closed point `t` of `T_y`
  obtain ⟨t, htT, ht⟩ : ∃ t ∈ pointSettingCurve sY y, IsClosed ({t} : Set _) := by
    haveI : LocallyOfFiniteType sY := h.isQFactorial.1.1.toLocallyOfFiniteType
    haveI := LocallyOfFiniteType.jacobsonSpace
      (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY)
    rw [← hT]
    exact nonempty_inter_closedPoints T.isIrreducible.nonempty T.isClosed.isLocallyClosed
  have he := productPointSettingClosedFibreIso_hom_fst h t htT ht
  set e := productPointSettingClosedFibreIso h t htT ht
  have hdimt : topologicalKrullDim (pointSettingFibre (pullback.map (π ≫ sY)
      (projectiveLine ℂ ↘ Spec (.of ℂ)) sY (projectiveLine ℂ ↘ Spec (.of ℂ)) π (𝟙 _) (𝟙 _)
      (by simp) (by simp)) t) ≤ 2 := by
    rw [(Scheme.homeoOfIso e).isHomeomorph.topologicalKrullDim_eq]
    exact hdim
  letI : (pointSettingFibre π y).Over (Spec (.of ℂ)) :=
    ⟨pullback.fst π (Y.fromSpecResidueField y) ≫ π ≫ sY⟩
  refine ⟨?_, ?_⟩
  · exact subsingleton_H_two_of_iso e (hLS.subsingleton_H_two_pointSettingFibre hdimt)
  · have hb := hLS.span_firstChernClass_pointSettingFibre_eq_top ht hdimt
    letI : (pointSettingFibre (pullback.map (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) sY
        (projectiveLine ℂ ↘ Spec (.of ℂ)) π (𝟙 _) (𝟙 _) (by simp) (by simp)) t).Over
        (Spec (.of ℂ)) :=
      ⟨pullback.fst _ _ ≫ pullback.map (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) sY
        (projectiveLine ℂ ↘ Spec (.of ℂ)) π (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
          pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY⟩
    refine span_firstChernClass_eq_top_of_iso e ?_ hb
    change e.hom ≫ pullback.fst π (Y.fromSpecResidueField y) ≫ π ≫ sY =
      pullback.fst _ _ ≫ _ ≫ pullback.fst sY _ ≫ sY
    rw [reassoc_of% he]
    simp

end ClosedFibre

/-! ### Formal lifting along the thickenings -/

section FormalLifting

open Opposite RingedSpaceModuleAdjunction TopologicalSpace

attribute [local implicit_reducible] TopCat.Sheaf
attribute [local instance] Stacks.Thickenings.hasExtAbelianSheaf
attribute [local instance] HasDerivedCategory.standard

/-- Two morphisms of sheaves of modules on a scheme agreeing on sections over every affine open
are equal. -/
private lemma hom_ext_affine {X : Scheme.{u}} {M N : X.Modules} {f g : M ⟶ N}
    (h : ∀ (U : X.affineOpens) (x : M.val.obj (op U.1)),
      (f.val.app (op U.1)).hom x = (g.val.app (op U.1)).hom x) : f = g :=
  SheafOfModules.hom_ext (Stacks.Divisors.presheafToSheaf_hom_ext_affine M.val N f.val g.val
    (fun U => by ext x; exact h U x))

/-- Vanishing of abelian sheaf cohomology gives vanishing of the derived global sections of a
sheaf of modules. -/
private lemma isZero_rightDerived_of_subsingleton {X : Scheme.{u}} (F : X.Modules) (n : ℕ)
    (h : Subsingleton (Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n)) :
    IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived n).obj F) :=
  (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup _ _ n F).2
    ((Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH X n F).2 h)

/-- Vanishing of the derived global sections of a sheaf of modules gives vanishing of the
abelian sheaf cohomology of its underlying sheaf. -/
private lemma subsingleton_of_isZero_rightDerived {X : Scheme.{u}} (F : X.Modules) (n : ℕ)
    (h : IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived n).obj F)) :
    Subsingleton (Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n) :=
  (Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH X n F).1
   ((Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
      _ _ n F).1 h)

/-- A section of the ideal sheaf of `j : W ⟶ X` restricts to zero on `W`. -/
private lemma app_kernel_ι_eq_zero {X W : Scheme.{u}} (j : W ⟶ X) (U : X.Opens)
    (t : (kernel (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom j.toLRSHom.toShHom))).val.obj (op U)) :
    j.app U ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom j.toLRSHom.toShHom))).val.app (op U) t) = 0 :=
  congrArg (fun f => (f.val.app (op U)).hom t)
    (kernel.condition (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom j.toLRSHom.toShHom)))

/-- **The ideal of `i` is a quotient of copies of `j_* 𝒪_W`.** Let `i : X' ⟶ X` and
`j : W ⟶ X` be closed immersions and `ψ : A →+* Γ(X, ⊤)`. Suppose that on every affine open the
ideal of `i` is generated by `ψ(𝔞)` for a finitely generated ideal `𝔞`, the ideal of `j` is
contained in the ideal generated by `ψ(𝔫)`, and `ψ` kills `𝔞𝔫`. Then the ideal sheaf of `i` is a
quotient of a finite direct sum of copies of `j_* 𝒪_W`: multiplication by a generator `g` of `𝔞`
kills the ideal of `j`, so factors through `𝒪_X ⟶ j_* 𝒪_W`, and lands in the ideal of `i`. -/
private theorem exists_epi_biproduct_pushforward_unit {X X' W : Scheme.{u}}
    (i : X' ⟶ X) [IsClosedImmersion i] (j : W ⟶ X) [IsClosedImmersion j]
    {A : Type u} [CommRing A] (ψ : A →+* Γ(X, ⊤)) (𝔞 𝔫 : Ideal A) (h𝔞 : 𝔞.FG)
    (h𝔞𝔫 : 𝔞 * 𝔫 ≤ RingHom.ker ψ)
    (hi : ∀ U : X.affineOpens, i.ker.ideal U =
      𝔞.map ((X.presheaf.map (homOfLE le_top).op).hom.comp ψ))
    (hj : ∀ U : X.affineOpens, j.ker.ideal U ≤
      𝔫.map ((X.presheaf.map (homOfLE le_top).op).hom.comp ψ)) :
    ∃ (r : ℕ) (Λ : (⨁ fun _ : Fin r => ((SheafOfModules.pushforward.{u}
        (structureSheafHom j.toLRSHom.toShHom)).obj (SheafOfModules.unit W.ringCatSheaf) :
          SheafOfModules.{u} X.ringCatSheaf)) ⟶
        kernel (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i.toLRSHom.toShHom) :
          SheafOfModules.unit X.ringCatSheaf ⟶ ((SheafOfModules.pushforward.{u}
            (structureSheafHom i.toLRSHom.toShHom)).obj (SheafOfModules.unit X'.ringCatSheaf) :
              SheafOfModules.{u} X.ringCatSheaf))),
      Epi Λ := by
  letI : Linear A (SheafOfModules.{u} X.ringCatSheaf) := Scheme.linearOfRingHom.{u, u} X A ψ
  set O := SheafOfModules.unit X.ringCatSheaf
  let Pj : SheafOfModules.{u} X.ringCatSheaf := (SheafOfModules.pushforward.{u}
    (structureSheafHom j.toLRSHom.toShHom)).obj (SheafOfModules.unit W.ringCatSheaf)
  let Pi : SheafOfModules.{u} X.ringCatSheaf := (SheafOfModules.pushforward.{u}
    (structureSheafHom i.toLRSHom.toShHom)).obj (SheafOfModules.unit X'.ringCatSheaf)
  let qj : O ⟶ Pj :=
    SheafOfModules.unitToPushforwardObjUnit (structureSheafHom j.toLRSHom.toShHom)
  let qi : O ⟶ Pi :=
    SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i.toLRSHom.toShHom)
  haveI : Epi qj := Stacks.ClosedImmersion.epi_unitToPushforwardObjUnit_structureSheafHom j
  let φ : ∀ U : X.affineOpens, A →+* Γ(X, (U : X.Opens)) := fun U =>
    (X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op).hom.comp ψ
  have hμ : ∀ (U : X.affineOpens) (a : A) (x : Γ(X, U)),
      (((a • 𝟙 O).val.app (op U.1)).hom x) = φ U a * x := fun U a x =>
    Stacks.SheafOfModules.smul_val_app X.ringCatSheaf A ⊤ isTerminalTop ψ a (𝟙 O) (op U.1) x
  -- multiplication by an element of `𝔞` kills the ideal of `W`
  have h1 : ∀ a ∈ 𝔞, kernel.ι qj ≫ (a • 𝟙 O) = 0 := by
    intro a ha
    apply hom_ext_affine
    intro U t
    change ((a • 𝟙 O).val.app (op U.1)).hom ((kernel.ι qj).val.app (op U.1) t) = 0
    let t' : Γ(X, U.1) := (kernel.ι qj).val.app (op U.1) t
    refine (hμ U a t').trans ?_
    have ht : t' ∈ j.ker.ideal U := by
      rw [Scheme.Hom.ker_apply]
      exact app_kernel_ι_eq_zero j U.1 t
    have hmem : φ U a * t' ∈ Ideal.map (φ U) (RingHom.ker ψ) :=
      Ideal.map_mono h𝔞𝔫 (by
        rw [Ideal.map_mul]
        exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ ha) (hj U ht))
    rwa [(Ideal.map_eq_bot_iff_le_ker _).2 fun b hb => by simp [φ, RingHom.mem_ker.1 hb]] at hmem
  let ν : ∀ a : 𝔞, Pj ⟶ O := fun a => Abelian.epiDesc qj (a.1 • 𝟙 O) (h1 a.1 a.2)
  have hν : ∀ a : 𝔞, qj ≫ ν a = a.1 • 𝟙 O := fun a => Abelian.comp_epiDesc _ _ _
  -- and lands in the ideal of `X'`
  have h2 : ∀ a : 𝔞, ν a ≫ qi = 0 := by
    intro a
    refine (cancel_epi qj).1 ?_
    rw [← Category.assoc, hν, comp_zero]
    apply hom_ext_affine
    intro U x
    change i.app U.1 (((a.1 • 𝟙 O).val.app (op U.1)).hom x) = 0
    have : φ U a.1 ∈ i.ker.ideal U := (hi U).symm ▸ Ideal.mem_map_of_mem _ a.2
    rw [Scheme.Hom.ker_apply] at this
    let x' : Γ(X, U.1) := x
    rw [hμ U a.1 x', map_mul, this, zero_mul]
  obtain ⟨r, g, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 h𝔞
  let gen : Fin r → 𝔞 := fun k => ⟨g k, hs ▸ Ideal.subset_span (Set.mem_range_self k)⟩
  let Λ : (⨁ fun _ : Fin r => Pj) ⟶ kernel qi :=
    biproduct.desc fun k => kernel.lift qi (ν (gen k)) (h2 (gen k))
  have hk : ∀ k : Fin r, qj ≫ biproduct.ι (fun _ : Fin r => Pj) k ≫ Λ ≫ kernel.ι qi =
      (gen k).1 • 𝟙 O := by
    intro k
    simp only [Λ, biproduct.ι_desc_assoc, kernel.lift_ι]
    exact hν (gen k)
  have hΛ : Epi Λ := by
    apply Stacks.Divisors.epi_of_surjective_affine
    intro U y
    let y' : Γ(X, U.1) := (kernel.ι qi).val.app (op U.1) y
    have hy : y' ∈ Ideal.span (Set.range fun k : Fin r => φ U (gen k).1) := by
      have : y' ∈ i.ker.ideal U := by
        rw [Scheme.Hom.ker_apply]
        exact app_kernel_ι_eq_zero i U.1 y
      rwa [hi U, ← hs, Ideal.map_span, ← Set.range_comp] at this
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hy
    refine ⟨∑ k, ((biproduct.ι (fun _ : Fin r => Pj) k).val.app (op U.1)).hom
      ((qj.val.app (op U.1)).hom (c k)), ?_⟩
    apply Stacks.SheafOfModules.injective_app_of_mono (kernel.ι qi) (op U.1)
    have hterm : ∀ k : Fin r, ((kernel.ι qi).val.app (op U.1)).hom ((Λ.val.app (op U.1)).hom
        (((biproduct.ι (fun _ : Fin r => Pj) k).val.app (op U.1)).hom
          ((qj.val.app (op U.1)).hom (c k)))) = φ U (gen k).1 * c k := fun k =>
      (congrArg (fun f => (f.val.app (op U.1)).hom (c k)) (hk k)).trans (hμ U _ _)
    rw [map_sum, map_sum]
    exact (Finset.sum_congr rfl fun k _ =>
      (hterm k).trans (mul_comm (φ U (gen k).1) (c k))).trans hc
  exact ⟨r, Λ, hΛ⟩

/-- **`H²` is right exact in dimension two.** On a Noetherian space of dimension at most two, an
epimorphism `P ⟶ J` of sheaves of modules with `H²(P) = 0` gives `H²(J) = 0`, since `H³` of its
kernel vanishes. -/
private lemma isZero_rightDerived_two_of_epi {X : Scheme.{u}} [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ ((2 : ℕ) : WithBot ℕ∞))
    {P J : SheafOfModules.{u} X.ringCatSheaf} (Λ : P ⟶ J) [hΛ : Epi Λ]
    (hP : IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived 2).obj P)) :
    IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived 2).obj J) := by
  let F := SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))
  have hS : (ShortComplex.mk (kernel.ι Λ) Λ (kernel.condition Λ)).ShortExact :=
    { exact := ShortComplex.exact_kernel Λ }
  have h3 : IsZero ((F.rightDerivedPlus ((2 : ℕ) + 1 : ℤ)).obj (kernel Λ)) :=
    (isZero_rightDerived_of_subsingleton (kernel Λ) 3
      (Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le
        hdim (by norm_num : 2 < 3) _)).of_iso
      ((Stacks.DerivedIndexing.rightDerivedIso F 3).app _).symm
  have := (Stacks.AlgebraicGeometry.TopDegreeBaseChange.exact_and_epi_map_rightDerived_of_isZero
    F hS 2 h3).2
  exact IsZero.of_epi ((F.rightDerived 2).map Λ) hP

/-- **`H²` of an ideal sheaf generated by global functions.** Let `X` be a Noetherian space of
dimension at most two, `i : X' ⟶ X` and `j : W ⟶ X` closed immersions and `ψ : A →+* Γ(X, ⊤)`.
If on every affine open the ideal of `i` is generated by `ψ(𝔞)` for a finitely generated ideal
`𝔞`, the ideal of `j` is contained in the ideal generated by `ψ(𝔫)`, `ψ` kills `𝔞𝔫`, and
`H²(W, 𝒪_W) = 0`, then `H²(X, J) = 0` for the ideal sheaf `J` of `i`. -/
private theorem H_two_idealAddSheaf_eq_zero {X X' W : Scheme.{u}} [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ ((2 : ℕ) : WithBot ℕ∞))
    (i : X' ⟶ X) [IsClosedImmersion i] (j : W ⟶ X) [IsClosedImmersion j]
    {A : Type u} [CommRing A] (ψ : A →+* Γ(X, ⊤)) (𝔞 𝔫 : Ideal A) (h𝔞 : 𝔞.FG)
    (h𝔞𝔫 : 𝔞 * 𝔫 ≤ RingHom.ker ψ)
    (hi : ∀ U : X.affineOpens, i.ker.ideal U =
      𝔞.map ((X.presheaf.map (homOfLE le_top).op).hom.comp ψ))
    (hj : ∀ U : X.affineOpens, j.ker.ideal U ≤
      𝔫.map ((X.presheaf.map (homOfLE le_top).op).hom.comp ψ))
    (hW : Subsingleton (Sheaf.H ((SheafOfModules.toSheaf W.ringCatSheaf).obj
      (SheafOfModules.unit W.ringCatSheaf)) 2)) :
    ∀ x : Sheaf.H (Stacks.Thickenings.idealAddSheaf i) 2, x = 0 := by
  obtain ⟨r, Λ, hΛ⟩ := exists_epi_biproduct_pushforward_unit i j ψ 𝔞 𝔫 h𝔞 h𝔞𝔫 hi hj
  let Pj : SheafOfModules.{u} X.ringCatSheaf := (SheafOfModules.pushforward.{u}
    (structureSheafHom j.toLRSHom.toShHom)).obj (SheafOfModules.unit W.ringCatSheaf)
  let F := SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))
  have hP : IsZero ((F.rightDerived 2).obj Pj) := isZero_rightDerived_of_subsingleton Pj 2
    (Stacks.Thickenings.closedImmersionCohomologyEquiv j inferInstance
      ((SheafOfModules.toSheaf W.ringCatSheaf).obj (SheafOfModules.unit W.ringCatSheaf))
      2).toEquiv.symm.subsingleton
  have hsum : IsZero ((F.rightDerived 2).obj (⨁ fun _ : Fin r => Pj)) := by
    refine IsZero.of_iso ?_ ((F.rightDerived 2).mapBiproduct _)
    rw [IsZero.iff_id_eq_zero]
    exact biproduct.hom_ext _ _ fun k => hP.eq_of_tgt _ _
  intro x
  have := subsingleton_of_isZero_rightDerived _ 2
    (isZero_rightDerived_two_of_epi hdim Λ (hΛ := hΛ) hsum)
  exact @Subsingleton.elim _ this x 0

section BaseChange

variable {R : CommRingCat.{u}} {Z : Scheme.{u}} (p : Z ⟶ Spec R)

/-- The base change `Z ×_R R/𝔞`. -/
private abbrev quotientFibre (𝔞 : Ideal R) : Scheme.{u} :=
  pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞)))

/-- `Spec R/𝔞 ⟶ Spec R/𝔟 ⟶ Spec R` is `Spec R/𝔞 ⟶ Spec R`. -/
private lemma specMap_factor_comp {𝔞 𝔟 : Ideal R} (h : 𝔟 ≤ 𝔞) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔟)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞)) :=
  ((Spec.map_comp _ _).symm).trans
    (congrArg Spec.map (CommRingCat.hom_ext (Ideal.Quotient.factor_comp_mk h)))

/-- `Spec R/𝔞 ⟶ Spec R/𝔟` is a closed immersion. -/
private instance isClosedImmersion_specMap_factor {𝔞 𝔟 : Ideal R} (h : 𝔟 ≤ 𝔞) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) :=
  IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective h)

/-- The closed immersion `Z ×_R R/𝔞 ⟶ Z ×_R R/𝔟` for `𝔟 ≤ 𝔞`. -/
private abbrev quotientFibreMap {𝔞 𝔟 : Ideal R} (h : 𝔟 ≤ 𝔞) :
    quotientFibre p 𝔞 ⟶ quotientFibre p 𝔟 :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) (𝟙 _)
    (by simp) (by simp [specMap_factor_comp])

/-- `Z ×_R R/𝔞 ⟶ Z ×_R R/𝔟` is the base change of `Spec R/𝔞 ⟶ Spec R/𝔟`. -/
private lemma isPullback_quotientFibreMap {𝔞 𝔟 : Ideal R} (h : 𝔟 ≤ 𝔞) :
    IsPullback (quotientFibreMap p h) (pullback.snd _ _) (pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) := by
  have e1 : quotientFibreMap p h ≫ pullback.fst _ _ = pullback.fst _ _ := by
    simp [quotientFibreMap]
  refine IsPullback.of_right ?_ (by simp [quotientFibreMap]) (IsPullback.of_hasPullback _ _)
  rw [e1, specMap_factor_comp h]
  exact IsPullback.of_hasPullback _ _

/-- `Z ×_R R/𝔞 ⟶ Z ×_R R/𝔟` is a closed immersion. -/
private theorem isClosedImmersion_quotientFibreMap {𝔞 𝔟 : Ideal R} (h : 𝔟 ≤ 𝔞) :
    IsClosedImmersion (quotientFibreMap p h) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_quotientFibreMap p h).flip inferInstance

/-- The ideal sheaf of `Z ×_R R/𝔞 ⟶ Z ×_R R/𝔟` is the inverse image of that of
`Spec R/𝔞 ⟶ Spec R/𝔟`. -/
private lemma ker_quotientFibreMap {𝔞 𝔟 : Ideal R} (h : 𝔟 ≤ 𝔞) :
    (quotientFibreMap p h).ker =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))).ker.comap (pullback.snd _ _) := by
  rw [← (isPullback_quotientFibreMap p h).isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- The functions on `Z ×_R R/𝔟` pulled back from `R`. -/
private def quotientFibreFunctions (𝔟 : Ideal R) :
    R →+* Γ(quotientFibre p 𝔟, ⊤) :=
  (pullback.snd p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔟)))).appTop.hom.comp
    ((Scheme.ΓSpecIso (.of (R ⧸ 𝔟))).inv.hom.comp (Ideal.Quotient.mk 𝔟))

/-- The kernel of `Γ(Spec φ)` is the kernel of `φ`, read through `Γ(Spec R) ≅ R`. -/
private lemma ker_appTop_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    RingHom.ker (Spec.map φ).appTop.hom = (RingHom.ker φ.hom).map (Scheme.ΓSpecIso R).inv.hom := by
  have e : (Spec.map φ).appTop = (Scheme.ΓSpecIso R).hom ≫ φ ≫ (Scheme.ΓSpecIso S).inv := by
    rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp, ← RingHom.comap_ker,
    RingHom.ker_comp_of_injective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).inv).1]
  exact (Ideal.map_comap_of_equiv (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv).symm

/-- On an affine open `U`, the ideal of `Z ×_R R/𝔞 ⟶ Z ×_R R/𝔟` is generated by the image of
`𝔞`. -/
private lemma ideal_ker_quotientFibreMap {𝔞 𝔟 : Ideal R} (h : 𝔟 ≤ 𝔞)
    (U : (quotientFibre p 𝔟).affineOpens) :
    (quotientFibreMap p h).ker.ideal U = 𝔞.map
      (((quotientFibre p 𝔟).presheaf.map
        (homOfLE (le_top : (U : (quotientFibre p 𝔟).Opens) ≤ ⊤)).op).hom.comp
        (quotientFibreFunctions p 𝔟)) := by
  rw [ker_quotientFibreMap, Stacks.IdealSheaf.ideal_comap_appLE _ _
    ⟨⊤, isAffineOpen_top _⟩ U (by simp), Scheme.Hom.ker_apply]
  change Ideal.map _ (RingHom.ker (Spec.map _).appTop.hom) = _
  rw [ker_appTop_specMap, CommRingCat.hom_ofHom, Ideal.Quotient.factor_ker, Ideal.map_map,
    Ideal.map_map]
  rfl

/-- The elements of `𝔟` vanish on `Z ×_R R/𝔟`. -/
private lemma quotientFibreFunctions_eq_zero {𝔟 : Ideal R} {b : R} (hb : b ∈ 𝔟) :
    quotientFibreFunctions p 𝔟 b = 0 := by
  simp [quotientFibreFunctions, Ideal.Quotient.eq_zero_iff_mem.2 hb]

/-- If `𝔞² ≤ 𝔟`, the ideal of `Z ×_R R/𝔞 ⟶ Z ×_R R/𝔟` has square zero. -/
private lemma ker_quotientFibreMap_sq {𝔞 𝔟 : Ideal R} (h : 𝔟 ≤ 𝔞) (h2 : 𝔞 ^ 2 ≤ 𝔟) :
    (quotientFibreMap p h).ker ^ 2 = ⊥ := by
  ext U : 2
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, ideal_ker_quotientFibreMap, ← Ideal.map_pow]
  simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  refine le_bot_iff.1 ((Ideal.map_mono h2).trans ?_)
  rw [Ideal.map_le_iff_le_comap]
  intro b hb
  rw [Ideal.mem_comap, Ideal.mem_bot, RingHom.comp_apply, quotientFibreFunctions_eq_zero p hb,
    map_zero]

/-- If `𝔞` lies in the radical of `𝔟`, then `Z ×_R R/𝔞 ⟶ Z ×_R R/𝔟` is surjective. -/
private lemma surjective_quotientFibreMap {𝔞 𝔟 : Ideal R} (h : 𝔟 ≤ 𝔞) (h2 : 𝔞 ≤ 𝔟.radical) :
    Surjective (quotientFibreMap p h) := by
  have : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) := by
    constructor
    change Function.Surjective (PrimeSpectrum.comap (Ideal.Quotient.factor h))
    rw [← Set.range_eq_univ, range_comap_of_surjective _ (Ideal.Quotient.factor h)
      (Ideal.Quotient.factor_surjective h), PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro x hx
    rw [SetLike.mem_coe, Ideal.Quotient.factor_ker,
      Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨k, hk⟩ := h2 ha
    rw [SetLike.mem_coe, mem_nilradical]
    exact ⟨k, by rwa [← map_pow, Ideal.Quotient.eq_zero_iff_mem]⟩
  exact MorphismProperty.of_isPullback (P := @Surjective)
    (isPullback_quotientFibreMap p h).flip this

end BaseChange

/-- One step of the tower `Z ×_R R/𝔪^{n+1}`, for a Noetherian local ring `R`: an invertible
sheaf on `F_n` lifts to `F_{n+1}`, provided `F_0` is Noetherian of dimension at most two with
`H²(F_0, 𝒪) = 0`. -/
private theorem exists_lift_quotientFibreMap {R : CommRingCat.{u}} [IsNoetherianRing R]
    [IsLocalRing R] {Z : Scheme.{u}} (p : Z ⟶ Spec R) {W : Scheme.{u}} [NoetherianSpace W]
    (e : W ≅ quotientFibre p (IsLocalRing.maximalIdeal R ^ (0 + 1)))
    (hdimW : topologicalKrullDim W ≤ 2)
    (hW : Subsingleton (Sheaf.H ((SheafOfModules.toSheaf W.ringCatSheaf).obj
      (SheafOfModules.unit W.ringCatSheaf)) 2))
    (n : ℕ) (L : (quotientFibre p (IsLocalRing.maximalIdeal R ^ (n + 1))).Modules)
    [hL : Stacks.Ample.IsInvertibleModule _ L] :
    ∃ (M : (quotientFibre p (IsLocalRing.maximalIdeal R ^ (n + 1 + 1))).Modules)
      (_ : Stacks.Ample.IsInvertibleModule _ M),
      Nonempty ((Scheme.Modules.pullback (quotientFibreMap p
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
          IsLocalRing.maximalIdeal R ^ (n + 1 + 1) ≤ IsLocalRing.maximalIdeal R ^ (n + 1)))).obj M ≅
        L) := by
  have h𝔟𝔞 : IsLocalRing.maximalIdeal R ^ (n + 1 + 1) ≤ IsLocalRing.maximalIdeal R ^ (n + 1) :=
    Ideal.pow_le_pow_right (Nat.le_succ (n + 1))
  have h𝔟𝔫 : IsLocalRing.maximalIdeal R ^ (n + 1 + 1) ≤ IsLocalRing.maximalIdeal R ^ (0 + 1) :=
    Ideal.pow_le_pow_right (by omega)
  haveI := isClosedImmersion_quotientFibreMap p h𝔟𝔞
  haveI := isClosedImmersion_quotientFibreMap p h𝔟𝔫
  haveI : IsClosedImmersion (e.hom ≫ quotientFibreMap p h𝔟𝔫) := inferInstance
  -- `F_0 ⟶ F_{n+1}` is a homeomorphism
  have hsurj : Function.Surjective (e.hom ≫ quotientFibreMap p h𝔟𝔫).base :=
    (surjective_quotientFibreMap p h𝔟𝔫 fun a ha => by
      have ha' : a ∈ IsLocalRing.maximalIdeal R := by rwa [zero_add, pow_one] at ha
      exact ⟨n + 1 + 1, Ideal.pow_mem_pow ha' (n + 1 + 1)⟩).surj.comp e.hom.homeomorph.surjective
  haveI : NoetherianSpace (quotientFibre p (IsLocalRing.maximalIdeal R ^ (n + 1 + 1))) :=
    noetherianSpace_of_surjective _ (e.hom ≫ quotientFibreMap p h𝔟𝔫).continuous hsurj
  have hdim : topologicalKrullDim (quotientFibre p (IsLocalRing.maximalIdeal R ^ (n + 1 + 1))) ≤
      ((2 : ℕ) : WithBot ℕ∞) := by
    have hemb := (e.hom ≫ quotientFibreMap p h𝔟𝔫).isClosedEmbedding
    rw [← IsHomeomorph.topologicalKrullDim_eq _
      (isHomeomorph_iff_continuous_isClosedMap_bijective.2 ⟨hemb.continuous,
        hemb.isClosedMap, hemb.injective, hsurj⟩)]
    exact_mod_cast hdimW
  have hH2 := H_two_idealAddSheaf_eq_zero hdim (quotientFibreMap p h𝔟𝔞)
    (e.hom ≫ quotientFibreMap p h𝔟𝔫)
    (quotientFibreFunctions p (IsLocalRing.maximalIdeal R ^ (n + 1 + 1)))
    (IsLocalRing.maximalIdeal R ^ (n + 1)) (IsLocalRing.maximalIdeal R ^ (0 + 1))
    (IsNoetherian.noetherian _)
    (by
      rw [← pow_add]
      intro b hb
      exact RingHom.mem_ker.2 (quotientFibreFunctions_eq_zero p hb))
    (ideal_ker_quotientFibreMap p h𝔟𝔞)
    (fun U => by
      rw [Scheme.Hom.ker_comp_of_isIso]
      exact (ideal_ker_quotientFibreMap p h𝔟𝔫 U).le) hW
  exact MMP.Resolution.Bridges.exists_isInvertibleModule_pullback_iso_of_ker_sq_eq_bot _
    (ker_quotientFibreMap_sq p h𝔟𝔞 (by
      rw [← pow_mul]
      exact Ideal.pow_le_pow_right (by omega))) hH2 L

/-- One step of the tower of a threefold point setting: an invertible sheaf on `F_n` lifts to
`F_{n+1}`. -/
private theorem exists_lift_step {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {y : Y}
    (h : IsThreefoldPointSetting sY π y) (n : ℕ)
    (L : (pointSettingThickening π y n).Modules)
    [hL : Stacks.Ample.IsInvertibleModule (pointSettingThickening π y n) L] :
    ∃ (M : (pointSettingThickening π y (n + 1)).Modules)
      (_ : Stacks.Ample.IsInvertibleModule (pointSettingThickening π y (n + 1)) M),
      Nonempty ((Scheme.Modules.pullback (quotientFibreMap (pullback.snd π (Y.fromSpecStalk y))
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
          IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (n + 1 + 1) ≤
            IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)))).obj M ≅ L) := by
  -- the scheme fibre is Noetherian of dimension at most two, with `H²(F_y, 𝒪) = 0`
  haveI := isProper_pointSettingFibre π h.isResolution.2.2.2.1 y
  haveI : LocallyOfFiniteType (pullback.snd π (Y.fromSpecResidueField y)) :=
    IsProper.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (pointSettingFibre π y) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd π (Y.fromSpecResidueField y))
  haveI : CompactSpace (pointSettingFibre π y) :=
    MMP.Fourfold.compactSpace_of_isProper (pullback.snd π (Y.fromSpecResidueField y))
  haveI : IsNoetherian (pointSettingFibre π y) := {}
  have hdimW : topologicalKrullDim (pointSettingFibre π y) ≤ 2 :=
    h.topologicalKrullDim_pointSettingFibre_le_two
  have hW : Subsingleton (Sheaf.H ((SheafOfModules.toSheaf (pointSettingFibre π y).ringCatSheaf).obj
      (SheafOfModules.unit (pointSettingFibre π y).ringCatSheaf)) 2) := by
    have hsub := (h.subsingleton_cohomologyOverField_two_and_span_firstChernClass).1
    apply subsingleton_of_isZero_rightDerived
    haveI : Subsingleton (((SheafOfModules.evaluation (pointSettingFibre π y).ringCatSheaf
        (op ⊤)).rightDerived 2).obj (SheafOfModules.unit (pointSettingFibre π y).ringCatSheaf)) :=
      hsub
    exact ModuleCat.isZero_of_subsingleton _
  exact exists_lift_quotientFibreMap (pullback.snd π (Y.fromSpecStalk y))
    (pointSettingFibreIsoThickeningZero π y) hdimW hW n L (hL := hL)

/-- **Formal lifting of line bundles.** For a threefold point setting `(Y, π, y)` with
`A = 𝒪_{Y,y}`, maximal ideal `𝔪`, and thickenings `F_n = Z ×_A A/𝔪^{n+1}`
(`MMP.Fourfold.pointSettingThickening`), every invertible sheaf `M` on `F_0` admits invertible
sheaves `M⁽ⁿ⁾` on `F_n` with `M⁽⁰⁾ = M` and `M⁽ⁿ⁺¹⁾|_{F_n} ≅ M⁽ⁿ⁾`, the restriction being the
pullback along the closed immersion `F_n ⟶ F_{n+1}` induced by `A/𝔪^{n+2} → A/𝔪^{n+1}`. -/
@[mmp "lem_mmp_indexb_formal_lifting"]
public theorem IsThreefoldPointSetting.exists_isInvertibleModule_pullback_iso
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {y : Y} (h : IsThreefoldPointSetting sY π y)
    (M : (pointSettingThickening π y 0).Modules)
    [Stacks.Ample.IsInvertibleModule (pointSettingThickening π y 0) M] :
    ∃ (L : ∀ n : ℕ, (pointSettingThickening π y n).Modules)
      (_ : ∀ n, Stacks.Ample.IsInvertibleModule (pointSettingThickening π y n) (L n)),
      L 0 = M ∧ ∀ n : ℕ, Nonempty ((Scheme.Modules.pullback
        (pullback.map _ _ _ _ (𝟙 _)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
            (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
              IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (n + 1 + 1) ≤
                IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)))))
          (𝟙 _) (by simp)
          (by
            simp only [Category.comp_id]
            exact (congrArg Spec.map (CommRingCat.hom_ext (Ideal.Quotient.factor_comp_mk
              (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))).symm).trans
              (Spec.map_comp _ _)) :
          pointSettingThickening π y n ⟶ pointSettingThickening π y (n + 1))).obj (L (n + 1)) ≅
        L n) := by
  have hstep : ∀ (n : ℕ) (S : InvertibleTowerStage (pointSettingThickening π y) n),
      ∃ S' : InvertibleTowerStage (pointSettingThickening π y) (n + 1),
        Nonempty ((Scheme.Modules.pullback (quotientFibreMap (pullback.snd π (Y.fromSpecStalk y))
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
            IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (n + 1 + 1) ≤
              IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)))).obj S'.obj ≅ S.obj) := by
    intro n S
    haveI := S.isInvertible
    obtain ⟨M', hM', e⟩ := exists_lift_step h n S.obj
    exact ⟨⟨M', hM'⟩, e⟩
  choose f hf using hstep
  let T : ∀ n, InvertibleTowerStage (pointSettingThickening π y) n := fun n =>
    Nat.rec ⟨M, inferInstance⟩ (fun n S => f n S) n
  exact ⟨fun n => (T n).obj, fun n => (T n).isInvertible, rfl, fun n => hf n (T n)⟩

end FormalLifting

/-! ### Formal algebraization -/

section FormalAlgebraization

open TopologicalSpace MMP.Mori

section Completion

variable (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The isomorphism `Â/𝔪̂^n ≅ R/𝔪^n` induced by `AdicCompletion.evalₐ`. -/
private def quotientPowEquiv (n : ℕ) :
    AdicCompletion (IsLocalRing.maximalIdeal R) R ⧸
        IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) ^ n ≃+*
      R ⧸ IsLocalRing.maximalIdeal R ^ n :=
  (Ideal.quotEquivOfEq (by
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
    exact (MMP.Fourfold.ker_evalₐ_eq_map (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
      n).symm)).trans
    (RingHom.quotientKerEquivOfSurjective (AdicCompletion.surjective_evalₐ _ n))

end Completion

/-- The evaluations `Â ⟶ R/I^{n+1}` are compatible with the projections
`R/I^{n+2} ⟶ R/I^{n+1}`. -/
private theorem factor_evalₐ_succ {R : Type} [CommRing R] (I : Ideal R) (n : ℕ)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
        I ^ (n + 1 + 1) ≤ I ^ (n + 1)) (AdicCompletion.evalₐ I (n + 1 + 1) x) =
      AdicCompletion.evalₐ I (n + 1) x := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ (h := by simp),
    ← AdicCompletion.factor_eval_eq_evalₐ (h := by simp), AdicCompletion.eval_apply,
    AdicCompletion.eval_apply, ← x.prop (Nat.le_succ (n + 1))]
  generalize x.val (n + 1 + 1) = z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [AdicCompletion.transitionMap_ideal_mk]
  exact (congrArg _ (Submodule.factor_mk _ y)).trans
    ((Ideal.Quotient.factor_mk _ y).trans (Submodule.factor_mk _ y).symm)

section Tower

variable {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {X : Scheme.{0}}
  (g : X ⟶ Spec (.of R))

local notation "𝔪" => IsLocalRing.maximalIdeal R
local notation "R̂" => AdicCompletion (IsLocalRing.maximalIdeal R) R

/-- The thickening `X ×_R R/𝔪^{n+1}` of the closed fibre of `g`. -/
private abbrev thickening (n : ℕ) : Scheme.{0} :=
  pullback g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 1)))))

/-- The base change `X ×_R R̂` of `g` to the completion. -/
private abbrev completion : Scheme.{0} :=
  pullback g (Spec.map (CommRingCat.ofHom (algebraMap R R̂)))

/-- The map `X ×_R R/𝔪^{n+1} ⟶ X ×_R R̂` induced by `R̂ ⟶ R/𝔪^{n+1}`. -/
private def thickeningToCompletion (n : ℕ) : thickening g n ⟶ completion g :=
  pullback.map _ _ _ _ (𝟙 _)
    (Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ 𝔪 (n + 1)).toRingHom)) (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm) (by
      rw [Category.comp_id]
      exact (congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x ↦
        ((AdicCompletion.evalₐ 𝔪 (n + 1)).commutes x).symm))).trans (Spec.map_comp _ _))

/-- The map `X ×_R R/𝔪^{n+1} ⟶ Spec (R̂/𝔪̂^{n+1})` through `quotientPowEquiv`. -/
private def thickeningToAdic (n : ℕ) :
    thickening g n ⟶ adicThickening R̂ (IsLocalRing.maximalIdeal R̂) n :=
  pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (quotientPowEquiv R (n + 1)).toRingHom)

/-- The closed immersion `X ×_R R/𝔪^{n+1} ⟶ X ×_R R/𝔪^{n+2}`. -/
private def thickeningSucc (n : ℕ) : thickening g n ⟶ thickening g (n + 1) :=
  pullback.map _ _ _ _ (𝟙 _)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : 𝔪 ^ (n + 1 + 1) ≤ 𝔪 ^ (n + 1)))))
    (𝟙 _) ((Category.comp_id _).trans (Category.id_comp _).symm) (by
      rw [Category.comp_id, ← Spec.map_comp]
      rfl)

private theorem thickeningSucc_comp (n : ℕ) :
    thickeningSucc g n ≫ thickeningToCompletion g (n + 1) = thickeningToCompletion g n := by
  apply pullback.hom_ext
  · simp [thickeningSucc, thickeningToCompletion]
  · simp only [thickeningSucc, thickeningToCompletion, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.assoc, ← Spec.map_comp]
    congr 2
    ext x
    exact factor_evalₐ_succ 𝔪 n x

/-- The thickening `X ×_R R/𝔪^{n+1}` is the adic thickening `X_R̂ ×_R̂ R̂/𝔪̂^{n+1}`. -/
private theorem isPullback_thickeningToCompletion (n : ℕ) :
    IsPullback (thickeningToCompletion g n) (thickeningToAdic g n) (pullback.snd _ _)
      (adicThickeningι R̂ (IsLocalRing.maximalIdeal R̂) n) := by
  let e := quotientPowEquiv R (n + 1)
  haveI : IsIso (CommRingCat.ofHom e.toRingHom) := e.toCommRingCatIso.isIso_hom
  have hbot : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 1)))))
      (Spec.map (CommRingCat.ofHom e.toRingHom)) (𝟙 _)
      (adicThickeningι R̂ (IsLocalRing.maximalIdeal R̂) n ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R̂))) :=
    IsPullback.of_vert_isIso ⟨by
      rw [Category.comp_id, adicThickeningι, ← Spec.map_comp, ← Spec.map_comp]
      rfl⟩
  refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback _ _)
  · rw [thickeningToCompletion, pullback.lift_fst, Category.comp_id]
    simpa [thickeningToAdic] using (IsPullback.of_hasPullback g _).paste_vert hbot
  · rw [thickeningToCompletion, pullback.lift_snd, thickeningToAdic, Category.assoc,
      adicThickeningι, ← Spec.map_comp]
    rfl

/-- The thickenings `X ×_R R/𝔪^{n+1}` form a cartesian tower over the adic thickenings of `R̂`. -/
private theorem isPullback_thickeningSucc (n : ℕ) :
    IsPullback (thickeningSucc g n) (thickeningToAdic g n) (thickeningToAdic g (n + 1))
      (adicThickeningSucc R̂ (IsLocalRing.maximalIdeal R̂) n) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_thickeningToCompletion g (n + 1))
  · rw [thickeningSucc_comp, adicThickeningSucc_ι]
    exact isPullback_thickeningToCompletion g n
  · simp only [thickeningSucc, thickeningToAdic, pullback.lift_snd_assoc, Category.assoc,
      adicThickeningSucc, ← Spec.map_comp]
    congr 2
    ext z
    exact factor_evalₐ_succ 𝔪 n z

end Tower

/-- **Algebraization of a compatible system of line bundles.** Over a projective
`fX : X ⟶ Spec A` with `A` an `I`-adically complete noetherian ring, a compatible system of
invertible modules on a cartesian tower of thickenings `X_n = X ×_A A/I^{n+1}` is the system of
restrictions of one invertible module on `X`. -/
private theorem exists_isInvertibleModule_of_compatible_tower (A : Type) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{0}}
    {fX : X ⟶ Spec (.of A)} (hfX : IsProjectiveMorphism fX) {Xn : ℕ → Scheme.{0}}
    (q : ∀ n, Xn n ⟶ adicThickening A I n) (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hcart : ∀ n, IsPullback (i n) (q n) (q (n + 1)) (adicThickeningSucc A I n))
    (k : ∀ n, Xn n ⟶ X) (hk : ∀ n, i n ≫ k (n + 1) = k n)
    (hkcart : ∀ n, IsPullback (k n) (q n) fX (adicThickeningι A I n))
    (Ls : ∀ n, (Xn n).Modules) (hLs : ∀ n, Stacks.Ample.IsInvertibleModule (Xn n) (Ls n))
    (φ : ∀ n, (Scheme.Modules.pullback (i n)).obj (Ls (n + 1)) ≅ Ls n) :
    ∃ (M : X.Modules) (_ : Stacks.Ample.IsInvertibleModule X M),
      Nonempty ((Scheme.Modules.pullback (k 0)).obj M ≅ Ls 0) := by
  haveI := isProper_of_isProjectiveMorphism fX hfX
  obtain ⟨M, hcoh, e, -⟩ :=
    Stacks.AmpleFormalSystemLineBundle.exists_coherent_of_restriction_isEquivalence A I fX
      q i k hk hkcart Ls hLs φ
      (Stacks.AmpleFormalSystemTheorem.adicTowerModuleAlgebraization_of_canonicalTower A I q i
        hcart (Stacks.AdicTowerRestriction.adicCanonicalTowerModuleAlgebraization A I)
        fX hfX k hk hkcart)
  exact ⟨M, Stacks.AdicTowerInvert.adicTowerInvertibility A I q fX hfX k hkcart M hcoh
    (fun n ↦ Stacks.AmpleFormalSystemLineBundle.isInvertibleModule_of_iso (e n) (hLs n)),
    ⟨(e 0).symm⟩⟩

/-- **Formal algebraization of line bundles.** For a threefold point setting `(Y, π, y)` with
`A = 𝒪_{Y,y}`, maximal ideal `𝔪`, `Z = Ỹ ×_Y Spec A` and closed fibre `F_0 = Z ×_A A/𝔪`
(`MMP.Fourfold.pointSettingThickening π y 0`), every invertible sheaf `M` on `F_0` is the
restriction of an invertible sheaf `M̂` on `Z_Â = Z ×_A Â`, `Â = AdicCompletion 𝔪 A`, along the
closed immersion `F_0 ⟶ Z_Â` induced by `AdicCompletion.evalₐ 𝔪 1 : Â → A/𝔪`. -/
@[mmp "lem_mmp_indexb_formal_algebraization"]
public theorem IsThreefoldPointSetting.exists_isInvertibleModule_pullback_adicCompletion_iso
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {y : Y} (h : IsThreefoldPointSetting sY π y)
    (M : (pointSettingThickening π y 0).Modules)
    [Stacks.Ample.IsInvertibleModule (pointSettingThickening π y 0) M] :
    ∃ (L : (pullback (pullback.snd π (Y.fromSpecStalk y))
        (Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y)
          (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
            (Y.presheaf.stalk y)))))).Modules)
      (_ : Stacks.Ample.IsInvertibleModule _ L),
      Nonempty ((Scheme.Modules.pullback
        (pullback.map _ _ _ _ (𝟙 _)
          (Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ
            (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (0 + 1)).toRingHom))
          (𝟙 _) (by simp)
          (by
            simp only [Category.comp_id]
            exact (congrArg Spec.map (CommRingCat.hom_ext
              (AlgHom.comp_algebraMap (AdicCompletion.evalₐ
                (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (0 + 1))).symm)).trans
              (Spec.map_comp _ _)) :
          pointSettingThickening π y 0 ⟶ _)).obj L ≅ M) := by
  let g : _ ⟶ Spec (.of (Y.presheaf.stalk y)) := pullback.snd π (Y.fromSpecStalk y)
  obtain ⟨Ls, hLs, rfl, hφ⟩ :=
    MMP.Fourfold.IsThreefoldPointSetting.exists_isInvertibleModule_pullback_iso h M
  exact exists_isInvertibleModule_of_compatible_tower
    (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)) _
    ((h.isResolution.2.2.2.1.baseChange _).baseChange _) (thickeningToAdic g) (thickeningSucc g)
    (isPullback_thickeningSucc g) (thickeningToCompletion g) (thickeningSucc_comp g)
    (isPullback_thickeningToCompletion g) Ls hLs (fun n ↦ (hφ n).some)

end FormalAlgebraization

/-! ### Descent to the henselization -/

section HenselianDescent

open IsLocalRing

/-- An `A`-algebra map out of a henselization of `A` (with residue field that of `A`) into an
`A`-algebra in which `𝔪` vanishes is unique. -/
private theorem algHom_ext_of_isHenselization {A : Type*} [CommRing A] [IsLocalRing A]
    {Ah : Type*} [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsHenselization A (ResidueField A) Ah] {S : Type*} [CommRing S] [Algebra A S]
    (hS : ∀ a ∈ maximalIdeal A, algebraMap A S a = 0) (g₁ g₂ : Ah →ₐ[A] S) : g₁ = g₂ := by
  have hker (g : Ah →ₐ[A] S) : ∀ x ∈ maximalIdeal Ah, g x = 0 := by
    rw [← IsHenselization.map_maximalIdeal (R := A) (L := ResidueField A)]
    refine fun x hx => (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_ :
      _ ≤ RingHom.ker (g : Ah →+* S)) hx
    simp [RingHom.mem_ker, hS a ha]
  obtain ⟨e, he⟩ := IsHenselization.exists_residueFieldEquiv (R := A) (L := ResidueField A)
    (Rh := Ah)
  ext x
  obtain ⟨a, ha⟩ := residue_surjective (e.symm (residue Ah x))
  have hx : x - algebraMap A Ah a ∈ maximalIdeal Ah := by
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero, ← he a, Algebra.algebraMap_self,
      RingHom.id_apply, ha, e.apply_symm_apply]
  have e₁ := hker g₁ _ hx
  have e₂ := hker g₂ _ hx
  rw [map_sub, sub_eq_zero, AlgHom.commutes] at e₁ e₂
  rw [e₁, e₂]

/-- **The residue of an Artin approximation.** If `ψ : B → Aʰ` approximates `φ : B → Â` modulo
`𝔪 Â`, then `φ` and `ψ` induce the same map `B → A/𝔪`: reduction `Â → A/𝔪` composed with `φ`
agrees with any `A`-algebra map `Aʰ → A/𝔪` composed with `ψ`. -/
private theorem evalₐ_comp_eq_comp_of_sub_mem {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {Ah : Type*} [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsHenselization A (ResidueField A) Ah] {B : Type*} [CommRing B] [Algebra A B]
    (φ : B →ₐ[A] AdicCompletion (maximalIdeal A) A) (ψ : B →ₐ[A] Ah)
    (hψ : ∀ x, φ x - henselizationToAdicCompletion A Ah (ψ x) ∈
      (maximalIdeal A ^ 1).map (algebraMap A (AdicCompletion (maximalIdeal A) A)))
    (r : Ah →ₐ[A] A ⧸ maximalIdeal A ^ 1) :
    (AdicCompletion.evalₐ (maximalIdeal A) 1).comp φ = r.comp ψ := by
  have hr : r = (AdicCompletion.evalₐ (maximalIdeal A) 1).comp
      (henselizationToAdicCompletion A Ah) :=
    algHom_ext_of_isHenselization (fun a ha => by
      rwa [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, pow_one]) _ _
  have hle : (maximalIdeal A ^ 1).map (algebraMap A (AdicCompletion (maximalIdeal A) A)) ≤
      RingHom.ker (AdicCompletion.evalₐ (maximalIdeal A) 1).toRingHom := by
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    rwa [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  ext x
  have hx := hle (hψ x)
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hx
  rw [hr]
  exact hx

/-- **Descent of one invertible sheaf to the henselization.** An invertible sheaf on the closed
fibre `F_0` is the restriction of an invertible sheaf on `Z ×_A Aʰ`. -/
private theorem exists_isInvertibleModule_restrict_iso {Y Yt : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {y : Y}
    (h : MMP.Fourfold.IsThreefoldPointSetting sY π y)
    (Ah : Type) [CommRing Ah] [IsLocalRing Ah] [Algebra (Y.presheaf.stalk y) Ah]
    [IsLocalRing.IsHenselization (Y.presheaf.stalk y)
      (IsLocalRing.ResidueField (Y.presheaf.stalk y)) Ah]
    (r : Ah →ₐ[Y.presheaf.stalk y]
      Y.presheaf.stalk y ⧸ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1))
    (M : (MMP.Fourfold.pointSettingThickening π y 0).Modules)
    [Stacks.Ample.IsInvertibleModule (MMP.Fourfold.pointSettingThickening π y 0) M] :
    ∃ (Mh : (pullback (pullback.snd π (Y.fromSpecStalk y))
        (Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) Ah)))).Modules)
      (_ : Stacks.Ample.IsInvertibleModule _ Mh),
      Nonempty ((Scheme.Modules.pullback
        (pullback.map _ _ _ _ (𝟙 _)
          (Spec.map (CommRingCat.ofHom r.toRingHom))
          (𝟙 _) (by simp)
          (by
            simp only [Category.comp_id]
            exact (congrArg Spec.map (CommRingCat.hom_ext
              (r.comp_algebraMap).symm)).trans (Spec.map_comp _ _)) :
          MMP.Fourfold.pointSettingThickening π y 0 ⟶ _)).obj Mh ≅ M) := by
  classical
  -- the local ring `A`, essentially of finite type over `ℂ`
  have hvar : AlgebraicGeometry.IsVariety ℂ sY := h.isResolution.1
  letI : Algebra ℂ (Y.presheaf.stalk y) := (((sY.stalkMap y).hom.comp
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫
      (Spec (.of ℂ)).presheaf.germ ⊤ (sY.base y) (by simp)).hom)).toAlgebra
  haveI : Algebra.EssFiniteType ℂ (Y.presheaf.stalk y) := essFiniteType_stalkStructureMap sY y
  haveI : IsNoetherianRing (Y.presheaf.stalk y) :=
    Algebra.EssFiniteType.isNoetherianRing ℂ (Y.presheaf.stalk y)
  -- `Z ⟶ Spec A` is proper
  haveI : IsProper π := isProper_of_isProjectiveMorphism _ h.isResolution.2.2.2.1
  let f := pullback.snd π (Y.fromSpecStalk y)
  let 𝔪 := maximalIdeal (Y.presheaf.stalk y)
  -- the completion as the filtered colimit of its finitely generated subalgebras
  let Â := AdicCompletion 𝔪 (Y.presheaf.stalk y)
  let Rd : Finset Â ⥤ Under (Y.presheaf.stalk y) :=
    { obj s := Under.mk (CommRingCat.ofHom
        (algebraMap (Y.presheaf.stalk y) (Algebra.adjoin (Y.presheaf.stalk y) (s : Set Â))))
      map {s t} g := Under.homMk ((Algebra.adjoinFinsetDiagram (Y.presheaf.stalk y) Â).map g)
        (by ext; rfl)
      map_id s := by ext; rfl
      map_comp _ _ := by ext; rfl }
  let c : Cocone Rd :=
    { pt := Under.mk (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) Â))
      ι :=
      { app s := Under.homMk ((Algebra.adjoinFinsetCocone (Y.presheaf.stalk y) Â).ι.app s)
          (by ext; rfl)
        naturality _ _ _ := by ext; rfl } }
  -- formal algebraization, then descent to a finitely generated subalgebra `B` of `Â`
  obtain ⟨L, hL, ⟨eL⟩⟩ := h.exists_isInvertibleModule_pullback_adicCompletion_iso M
  obtain ⟨j, Lj, hLj, ⟨eLj⟩⟩ :=
    (MMP.exists_isInvertible_pullback_iso_of_isColimit_under f Rd c
      (isColimitOfReflects (Under.forget _)
        (Algebra.isColimitAdjoinFinsetCocone (Y.presheaf.stalk y) Â))).1 L hL
  let B := Algebra.adjoin (Y.presheaf.stalk y) (j : Set Â)
  haveI : Algebra.FinitePresentation (Y.presheaf.stalk y) B :=
    Algebra.FinitePresentation.of_finiteType.mp
      ((Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset _))
  -- Artin approximation
  obtain ⟨ψ, hψ⟩ :=
    MMP.Resolution.Bridges.exists_algHom_henselization_approx (k := ℂ) Ah B.val 1
  let q : pullback f (Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) Ah))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) B))) :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (𝟙 _) (by simp)
      (by
        rw [Category.comp_id]
        exact (congrArg Spec.map (CommRingCat.hom_ext (ψ.comp_algebraMap).symm)).trans
          (Spec.map_comp _ _))
  refine ⟨(Scheme.Modules.pullback q).obj Lj,
    MMP.Fourfold.isInvertibleModule_pullback q Lj (hM := hLj), ⟨?_⟩⟩
  let ιh : MMP.Fourfold.pointSettingThickening π y 0 ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) Ah))) :=
    pullback.map _ _ _ _ (𝟙 _)
        (Spec.map (CommRingCat.ofHom r.toRingHom))
        (𝟙 _) (by simp [f])
        (by
          simp only [Category.comp_id]
          exact (congrArg Spec.map (CommRingCat.hom_ext
            (r.comp_algebraMap).symm)).trans (Spec.map_comp _ _))
  let ιA : MMP.Fourfold.pointSettingThickening π y 0 ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) Â))) :=
    pullback.map _ _ _ _ (𝟙 _)
        (Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ 𝔪 (0 + 1)).toRingHom))
        (𝟙 _) (by simp [f])
        (by
          simp only [Category.comp_id]
          exact (congrArg Spec.map (CommRingCat.hom_ext
            (AlgHom.comp_algebraMap (AdicCompletion.evalₐ 𝔪 (0 + 1))).symm)).trans
            (Spec.map_comp _ _))
  let pj : pullback f (Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) Â))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) B))) :=
    pullback.map f (Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) Â))) f
      (Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) B))) (𝟙 _)
      (Spec.map (CommRingCat.ofHom B.val.toRingHom)) (𝟙 _)
      ((Category.comp_id f).trans (Category.id_comp f).symm)
      ((Category.comp_id _).trans
        ((congrArg Spec.map (Under.w (c.ι.app j))).symm.trans (Spec.map_comp _ _)))
  have hcomp : ιh ≫ q = ιA ≫ pj := by
    apply pullback.hom_ext
    · simp [ιh, ιA, pj, q, f]
    · simp only [ιh, ιA, pj, q, f, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 2
      ext x
      exact (AlgHom.congr_fun (evalₐ_comp_eq_comp_of_sub_mem B.val ψ hψ r) x).symm
  exact MMP.Fourfold.pullbackCompIso hcomp Lj ≪≫
    (MMP.Fourfold.pullbackCompIso (a := ιA) (b := pj) rfl Lj).symm ≪≫
    (Scheme.Modules.pullback ιA).mapIso eLj.symm ≪≫ eL

/-- **Descent of line bundles to the henselization.** For a threefold point setting `(Y, π, y)`
with `A = 𝒪_{Y,y}`, maximal ideal `𝔪`, `Z = Ỹ ×_Y Spec A` and closed fibre `F_0 = Z ×_A A/𝔪`
(`MMP.Fourfold.pointSettingThickening π y 0`), and a henselization `Aʰ` of `A`, every family of
invertible sheaves `M i` on `F_0` is the restriction of a family of invertible sheaves `Mʰ i` on
`Z_{Aʰ} = Z ×_A Aʰ`, along the closed immersion `F_0 ⟶ Z_{Aʰ}` induced by an `A`-algebra map
`r : Aʰ →ₐ[A] A/𝔪`. -/
@[mmp "lem_mmp_indexb_henselian_descent"]
public theorem IsThreefoldPointSetting.exists_isInvertibleModule_pullback_henselization_iso
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {y : Y} (h : IsThreefoldPointSetting sY π y)
    {Ah : Type} [CommRing Ah] [IsLocalRing Ah] [Algebra (Y.presheaf.stalk y) Ah]
    [IsLocalRing.IsHenselization (Y.presheaf.stalk y)
      (IsLocalRing.ResidueField (Y.presheaf.stalk y)) Ah]
    (r : Ah →ₐ[Y.presheaf.stalk y]
      Y.presheaf.stalk y ⧸ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1))
    {ι : Type*} (M : ι → (pointSettingThickening π y 0).Modules)
    (hM : ∀ i, Stacks.Ample.IsInvertibleModule (pointSettingThickening π y 0) (M i)) :
    ∃ (Mh : ι → (pullback (pullback.snd π (Y.fromSpecStalk y))
        (Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) Ah)))).Modules)
      (_ : ∀ i, Stacks.Ample.IsInvertibleModule _ (Mh i)),
      ∀ i, Nonempty ((Scheme.Modules.pullback
        (pullback.map _ _ _ _ (𝟙 _)
          (Spec.map (CommRingCat.ofHom r.toRingHom))
          (𝟙 _) (by simp)
          (by
            simp only [Category.comp_id]
            exact (congrArg Spec.map (CommRingCat.hom_ext
              (r.comp_algebraMap).symm)).trans (Spec.map_comp _ _)) :
          pointSettingThickening π y 0 ⟶ _)).obj (Mh i) ≅ M i) := by
  choose Mh hMh e using fun i => have := hM i; exists_isInvertibleModule_restrict_iso h Ah r (M i)
  exact ⟨Mh, hMh, e⟩

end HenselianDescent

/-! ### Étale extension of line bundles -/

section EtaleLines

open TopologicalSpace MMP.Mori MMP.Resolution.Bridges Opposite

section Section

variable {S : Scheme.{0}} {s : S}

private lemma fromSpecResidueField_toBase (U : ElementaryEtaleNeighborhood S s) :
    U.obj.scheme.fromSpecResidueField U.obj.point ≫ U.obj.toBase =
      Spec.map U.obj.residueFieldMap ≫ S.fromSpecResidueField s := by
  rw [EtaleNeighborhood.residueFieldMap_def, Spec.map_comp, Category.assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  congr 1
  rw [← Scheme.residueFieldCongr_fromSpecResidueField U.obj.map_point.symm]
  rfl

/-- A morphism `Spec κ(s) ⟶ U` through the residue field of the distinguished point of an
elementary étale neighbourhood `(U, u)` of `(S, s)`, lying over `Spec κ(s) ⟶ S`, is the section
through `u`. -/
private lemma eq_elementaryNeighborhoodSection (U : ElementaryEtaleNeighborhood S s)
    (h : U.obj.scheme.residueField U.obj.point ⟶ S.residueField s)
    (hh : (Spec.map h ≫ U.obj.scheme.fromSpecResidueField U.obj.point) ≫ U.obj.toBase =
      S.fromSpecResidueField s) :
    Spec.map h ≫ U.obj.scheme.fromSpecResidueField U.obj.point =
      elementaryNeighborhoodSection U := by
  have : IsIso U.obj.residueFieldMap := U.property
  have key : U.obj.residueFieldMap ≫ h = 𝟙 _ := by
    apply Spec.map_injective
    rw [← cancel_mono (S.fromSpecResidueField s), Spec.map_comp, Spec.map_id, Category.id_comp,
      Category.assoc, ← fromSpecResidueField_toBase, ← Category.assoc, hh]
  have : h = inv U.obj.residueFieldMap := IsIso.eq_inv_of_hom_inv_id key
  subst this
  rfl

end Section

/-! ### The limit `Ỹ ×_S Spec Rh` of the `Ỹ ×_S U` -/

section Limit

variable {S : Scheme.{0}} {s : S} {Rh : Type} [CommRing Rh] [IsLocalRing Rh]
  [Algebra (S.presheaf.stalk s) Rh]

private instance (U : AffineElementaryEtaleNeighborhood S s) : IsAffine U.obj.obj.scheme :=
  U.property

variable (s Rh) in
/-- The morphism `Spec Rh ⟶ Spec 𝒪_{S,s}` of the structure map. -/
private def specAlg : Spec (CommRingCat.of Rh) ⟶ Spec (S.presheaf.stalk s) :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) Rh))

private def specLeg (U : AffineElementaryEtaleNeighborhood S s)
    (f : Γ(U.obj.obj.scheme, ⊤) ⟶ CommRingCat.of Rh) :
    Spec (CommRingCat.of Rh) ⟶ U.obj.obj.scheme :=
  Spec.map f ≫ U.obj.obj.scheme.isoSpec.inv

private lemma specLeg_eq (U : AffineElementaryEtaleNeighborhood S s)
    (f : Γ(U.obj.obj.scheme, ⊤) ⟶ CommRingCat.of Rh)
    (hf : IsOverStalk S s Rh U.obj f.hom) :
    ∃ g : U.obj.obj.scheme.presheaf.stalk U.obj.obj.point →+* Rh, IsLocalHom g ∧
      g.comp (stalkMap S s U.obj) = algebraMap (S.presheaf.stalk s) Rh ∧
      specLeg U f = Spec.map (CommRingCat.ofHom g) ≫
        U.obj.obj.scheme.fromSpecStalk U.obj.obj.point := by
  obtain ⟨g, hg, hg', hfg⟩ := hf
  refine ⟨g, hg, hg', ?_⟩
  have hf' : Spec.map f = Spec.map (CommRingCat.ofHom g) ≫
      Spec.map (U.obj.obj.scheme.presheaf.germ ⊤ U.obj.obj.point (Set.mem_univ _)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x; exact congrArg (fun φ => φ x) hfg
  rw [specLeg, hf', Category.assoc, ← IsAffineOpen.fromSpec_top,
    ← IsAffineOpen.fromSpecStalk_eq_fromSpecStalk (isAffineOpen_top _) (Set.mem_univ _)]
  rfl

private lemma specLeg_comp' {U V : AffineElementaryEtaleNeighborhood S s} (a : U ⟶ V)
    (f : Γ(U.obj.obj.scheme, ⊤) ⟶ CommRingCat.of Rh)
    (f' : Γ(V.obj.obj.scheme, ⊤) ⟶ CommRingCat.of Rh)
    (h : a.hom.hom.hom.appTop ≫ f = f') :
    specLeg U f ≫ a.hom.hom.hom = specLeg V f' := by
  rw [specLeg, specLeg, Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc,
    ← Spec.map_comp, h]

private lemma specLeg_toBase (U : AffineElementaryEtaleNeighborhood S s)
    (f : Γ(U.obj.obj.scheme, ⊤) ⟶ CommRingCat.of Rh)
    (hf : IsOverStalk S s Rh U.obj f.hom) :
    specLeg U f ≫ U.obj.obj.toBase = specAlg s Rh ≫ S.fromSpecStalk s := by
  unfold specAlg
  obtain ⟨g, -, hg', he⟩ := specLeg_eq U f hf
  rw [he, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← hg',
    ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk
      (Inseparable.of_eq U.obj.obj.map_point.symm).ge]
  simp only [stalkMap, ← Spec.map_comp, ← Category.assoc]
  congr 2

private lemma specLeg_comp {U V : AffineElementaryEtaleNeighborhood S s} (a : U ⟶ V)
    (ι : affineGlobalSections S s ⟶ (Functor.const _).obj (CommRingCat.of Rh)) :
    specLeg U (ι.app (op U)) ≫ a.hom.hom.hom = specLeg V (ι.app (op V)) := by
  have hn := ι.naturality a.op
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at hn
  exact specLeg_comp' a _ _ hn

variable {Yt : Scheme.{0}} (π : Yt ⟶ S)

private abbrev Idx (S : Scheme.{0}) (s : S) := (AffineElementaryEtaleNeighborhood S s)ᵒᵖᵒᵖ

private abbrev stage : Idx S s ⥤ Scheme.{0} where
  obj j := pullback π j.unop.unop.obj.obj.toBase
  map g := pullback.map π _ π _ (𝟙 _) g.unop.unop.hom.hom.hom (𝟙 _) (by simp)
    (by simp [g.unop.unop.hom.hom.over])
  map_id j := by apply pullback.hom_ext <;> simp
  map_comp g h := by apply pullback.hom_ext <;> simp

private def stageFst (j : Idx S s) : (stage π).obj j ⟶ Yt := pullback.fst _ _
private def stageSnd (j : Idx S s) : (stage π).obj j ⟶ j.unop.unop.obj.obj.scheme :=
  pullback.snd _ _

private lemma stage_condition (j : Idx S s) :
    stageFst π j ≫ π = stageSnd π j ≫ j.unop.unop.obj.obj.toBase := pullback.condition

private lemma stage_hom_ext {j : Idx S s} {T : Scheme.{0}} {a b : T ⟶ (stage π).obj j}
    (h₁ : a ≫ stageFst π j = b ≫ stageFst π j) (h₂ : a ≫ stageSnd π j = b ≫ stageSnd π j) :
    a = b := pullback.hom_ext h₁ h₂

@[reassoc]
private lemma stage_map_fst {j k : Idx S s} (g : j ⟶ k) :
    (stage π).map g ≫ stageFst π k = stageFst π j :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
private lemma stage_map_snd {j k : Idx S s} (g : j ⟶ k) :
    (stage π).map g ≫ stageSnd π k = stageSnd π j ≫ g.unop.unop.hom.hom.hom :=
  pullback.lift_snd _ _ _

variable (s Rh) in
private abbrev limitPt : Scheme.{0} :=
  pullback (pullback.snd π (S.fromSpecStalk s))
    (specAlg s Rh)

variable (ι : affineGlobalSections S s ⟶ (Functor.const _).obj (CommRingCat.of Rh))
  (hι : ∀ U : (AffineElementaryEtaleNeighborhood S s)ᵒᵖ,
    IsOverStalk S s Rh U.unop.obj (ι.app U).hom)

variable (s) in
private def isoSpecHom (j : Idx S s) :
    j.unop.unop.obj.obj.scheme ⟶ ((affineGlobalSections S s).op ⋙ Scheme.Spec).obj j :=
  j.unop.unop.obj.obj.scheme.isoSpec.hom

private instance (j : Idx S s) : IsIso (isoSpecHom s j) :=
  (inferInstance : IsIso j.unop.unop.obj.obj.scheme.isoSpec.hom)

private def leg (j : Idx S s) :
    Spec (CommRingCat.of Rh) ⟶ j.unop.unop.obj.obj.scheme :=
  specLeg j.unop.unop (ι.app j.unop)

private lemma leg_comp {j k : Idx S s} (g : j ⟶ k) : leg ι j ≫ g.unop.unop.hom.hom.hom = leg ι k :=
  specLeg_comp g.unop.unop ι

include hι in
private lemma leg_toBase (j : Idx S s) :
    leg ι j ≫ j.unop.unop.obj.obj.toBase = specAlg s Rh ≫ S.fromSpecStalk s :=
  specLeg_toBase _ _ (hι j.unop)

private lemma leg_isoSpec (j : Idx S s) :
    leg ι j ≫ isoSpecHom s j =
      (Scheme.Spec.mapCone (Cocone.mk _ ι).op).π.app j :=
  (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (Iso.inv_hom_id _)).trans (Category.comp_id _))

private lemma leg_spec (j : Idx S s) {T : Scheme.{0}} (b : T ⟶ Spec (CommRingCat.of Rh))
    (t : T ⟶ j.unop.unop.obj.obj.scheme)
    (h : b ≫ (Scheme.Spec.mapCone (Cocone.mk _ ι).op).π.app j =
      t ≫ isoSpecHom s j) : b ≫ leg ι j = t := by
  rw [← cancel_mono (isoSpecHom s j), Category.assoc, leg_isoSpec, h]

private def stageConeπ (j : Idx S s) : limitPt s Rh π ⟶ (stage π).obj j :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ leg ι j) (by
      rw [Category.assoc, Category.assoc, leg_toBase ι hι, pullback.condition,
        ← Category.assoc, pullback.condition, Category.assoc])

@[reassoc]
private lemma stageConeπ_fst (j : Idx S s) : stageConeπ π ι hι j ≫ stageFst π j =
    pullback.fst _ _ ≫ pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc]
private lemma stageConeπ_snd (j : Idx S s) : stageConeπ π ι hι j ≫ stageSnd π j =
    pullback.snd _ _ ≫ leg ι j := pullback.lift_snd _ _ _

private lemma stageConeπ_comp {j k : Idx S s} (g : j ⟶ k) :
    stageConeπ π ι hι j ≫ (stage π).map g = stageConeπ π ι hι k := by
  apply stage_hom_ext
  · rw [Category.assoc, stage_map_fst, stageConeπ_fst, stageConeπ_fst]
  · rw [Category.assoc, stage_map_snd, stageConeπ_snd_assoc, stageConeπ_snd,
      leg_comp ι g]

private abbrev stageCone : Cone (stage (s := s) π) where
  pt := limitPt s Rh π
  π :=
  { app j := stageConeπ π ι hι j
    naturality j k g := by
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
      exact (stageConeπ_comp π ι hι g).symm }

private lemma cone_π_fst_eq [IsFiltered (AffineElementaryEtaleNeighborhood S s)ᵒᵖ]
    (c : Cone (stage (s := s) π)) (j k : Idx S s) :
    c.π.app j ≫ stageFst π j = c.π.app k ≫ stageFst π k := by
  obtain ⟨m, a, b, -⟩ := IsFilteredOrEmpty.cocone_objs j.unop k.unop
  rw [← c.w a.op, ← c.w b.op, Category.assoc, Category.assoc, stage_map_fst, stage_map_fst]

private lemma stage_map_snd_isoSpec {j k : Idx S s} (g : j ⟶ k) :
    (stage π).map g ≫ stageSnd π k ≫ isoSpecHom s k =
      stageSnd π j ≫ isoSpecHom s j ≫ ((affineGlobalSections S s).op ⋙ Scheme.Spec).map g := by
  rw [stage_map_snd_assoc]
  exact congrArg (stageSnd π j ≫ ·)
    (Scheme.isoSpec_hom_naturality g.unop.unop.hom.hom.hom).symm

private def specCone (c : Cone (stage (s := s) π)) :
    Cone ((affineGlobalSections S s).op ⋙ Scheme.Spec) where
  pt := c.pt
  π :=
  { app j := c.π.app j ≫ stageSnd π j ≫ isoSpecHom s j
    naturality j k g := by
      refine (Category.id_comp _).trans ?_
      rw [← c.w g, Category.assoc, stage_map_snd_isoSpec, Category.assoc, Category.assoc] }

private def isLimitStageCone [IsFiltered (AffineElementaryEtaleNeighborhood S s)ᵒᵖ]
    (hc : IsColimit (Cocone.mk _ ι)) : IsLimit (stageCone π ι hι) := by
  have hS : IsLimit (Scheme.Spec.mapCone (Cocone.mk _ ι).op) :=
    isLimitOfPreserves _ hc.op
  let j₀ : Idx S s :=
    op (IsFiltered.nonempty (C := (AffineElementaryEtaleNeighborhood S s)ᵒᵖ)).some
  let ℓ : ∀ c : Cone (stage (s := s) π), c.pt ⟶ Spec (CommRingCat.of Rh) :=
    fun c => hS.lift (specCone π c)
  have hℓ : ∀ (c : Cone (stage (s := s) π)) (j : Idx S s),
      ℓ c ≫ leg ι j = c.π.app j ≫ stageSnd π j :=
    fun c j => leg_spec ι j _ _ (hS.fac (specCone π c) j)
  have hlift : ∀ c : Cone (stage (s := s) π),
      (c.π.app j₀ ≫ stageFst π j₀) ≫ π =
        (ℓ c ≫ specAlg s Rh) ≫
          S.fromSpecStalk s := fun c => by
    rw [Category.assoc, Category.assoc, ← leg_toBase ι hι j₀, ← Category.assoc (ℓ c),
      hℓ, stage_condition, Category.assoc]
  let lift : ∀ c : Cone (stage (s := s) π), c.pt ⟶ limitPt s Rh π := fun c =>
    pullback.lift (pullback.lift (c.π.app j₀ ≫ stageFst π j₀)
      (ℓ c ≫ specAlg s Rh) (hlift c))
      (ℓ c) (pullback.lift_snd _ _ _)
  have hlift_fst : ∀ c, lift c ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      c.π.app j₀ ≫ stageFst π j₀ := fun c => by
    simp only [lift, pullback.lift_fst_assoc, pullback.lift_fst]
  have hlift_snd : ∀ c, lift c ≫ pullback.snd _ _ = ℓ c := fun c => pullback.lift_snd _ _ _
  refine
  { lift := lift
    fac c j := ?_
    uniq c m hm := ?_ }
  · apply stage_hom_ext
    · change lift c ≫ stageConeπ π ι hι j ≫ _ = _
      rw [stageConeπ_fst, hlift_fst]
      exact cone_π_fst_eq π c j₀ j
    · change lift c ≫ stageConeπ π ι hι j ≫ _ = _
      rw [stageConeπ_snd, ← Category.assoc, hlift_snd]
      exact hℓ c j
  · have hm' : ∀ j, m ≫ stageConeπ π ι hι j = c.π.app j := hm
    have hsnd : m ≫ pullback.snd _ _ = ℓ c := by
      refine hS.uniq (specCone π c) _ (fun j => ?_)
      change (m ≫ pullback.snd _ _) ≫ (Scheme.Spec.mapCone (Cocone.mk _ ι).op).π.app j =
        c.π.app j ≫ stageSnd π j ≫ isoSpecHom s j
      rw [← hm' j, Category.assoc, Category.assoc, stageConeπ_snd_assoc, leg_isoSpec]
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [Category.assoc, ← stageConeπ_fst π ι hι j₀, ← Category.assoc, hm', Category.assoc,
          hlift_fst]
      · rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd, Category.assoc,
          pullback.condition, ← Category.assoc, hlift_snd]
    · rw [hsnd, hlift_snd]

private lemma isPullback_stage_map {j k : Idx S s} (g : j ⟶ k) :
    IsPullback (stageSnd π j) ((stage π).map g) g.unop.unop.hom.hom.hom (stageSnd π k) := by
  refine IsPullback.flip (IsPullback.of_right (h₁₂ := stageFst π k) (v₁₃ := π)
    (h₂₂ := k.unop.unop.obj.obj.toBase) ?_ (stage_map_snd π g)
    (IsPullback.of_hasPullback π _))
  rw [stage_map_fst, g.unop.unop.hom.hom.over]
  exact IsPullback.of_hasPullback π _

private instance isAffineHom_stage_map {j k : Idx S s} (g : j ⟶ k) :
    IsAffineHom ((stage π).map g) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_stage_map π g) inferInstance

private instance compactSpace_stage_obj [QuasiCompact π] (j : Idx S s) :
    CompactSpace ((stage π).obj j) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.snd π j.unop.unop.obj.obj.toBase)

private instance quasiSeparatedSpace_stage_obj [QuasiSeparated π] (j : Idx S s) :
    QuasiSeparatedSpace ((stage π).obj j) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.snd π j.unop.unop.obj.obj.toBase)

include hι in
/-- The composite `Spec κ(s) ⟶ Spec Rh ⟶ U` of a local map `σ : Rh ⟶ κ(s)` over `𝒪_{S,s}` and a
leg is the section of `U` through its distinguished point. -/
private lemma specMap_comp_leg (j : Idx S s) (σ : CommRingCat.of Rh ⟶ S.residueField s)
    [IsLocalHom σ.hom] (hσ : σ.hom.comp (algebraMap _ Rh) = (S.residue s).hom) :
    Spec.map σ ≫ leg ι j = elementaryNeighborhoodSection j.unop.unop.obj := by
  obtain ⟨g, hg, -, he⟩ := specLeg_eq j.unop.unop (ι.app j.unop) (hι j.unop)
  have hc : IsLocalHom (σ.hom.comp g) := RingHom.isLocalHom_comp _ _
  let h : j.unop.unop.obj.obj.scheme.residueField j.unop.unop.obj.obj.point ⟶ S.residueField s :=
    CommRingCat.ofHom (@IsLocalRing.ResidueField.lift _ _ _ _ _ (σ.hom.comp g) hc)
  have key : Spec.map σ ≫ leg ι j =
      Spec.map h ≫ j.unop.unop.obj.obj.scheme.fromSpecResidueField j.unop.unop.obj.obj.point := by
    rw [leg, he, ← Category.assoc, ← Spec.map_comp, Scheme.fromSpecResidueField, ← Category.assoc,
      ← Spec.map_comp]
    congr 2
  have hb : Spec.map σ ≫ specAlg s Rh ≫ S.fromSpecStalk s = S.fromSpecResidueField s := by
    have h₁ : CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) Rh) ≫ σ = S.residue s := by
      ext x
      exact congrArg (fun φ => φ x) hσ
    have e₁ : Spec.map σ ≫ specAlg s Rh = Spec.map (S.residue s) :=
      (Spec.map_comp _ _).symm.trans (congrArg Spec.map h₁)
    rw [← Category.assoc, e₁]
    rfl
  rw [key]
  apply eq_elementaryNeighborhoodSection
  rw [← key, Category.assoc, leg_toBase ι hι, hb]

end Limit

/-! ### Integral neighbourhoods -/

section Integral

variable {S : Scheme.{0}} {s : S}

/-- In a Noetherian scheme, a point whose local ring is a domain has an irreducible open
neighbourhood. -/
private lemma exists_isOpen_isIrreducible (X : Scheme.{0}) [NoetherianSpace X] (x : X)
    [IsDomain (X.presheaf.stalk x)] : ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ IsIrreducible V := by
  have hG : IsIrreducible (Set.range (X.fromSpecStalk x)) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (X.fromSpecStalk x).continuous.continuousOn
  obtain ⟨C, hC, hGC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hG
  let s : Set (Set X) := {C' | C' ∈ irreducibleComponents X ∧ x ∉ C'}
  have hF : IsClosed (⋃ C' ∈ s, C') :=
    (NoetherianSpace.finite_irreducibleComponents.subset fun _ h => h.1).isClosed_biUnion
      fun C' h => isClosed_of_mem_irreducibleComponents _ h.1
  refine ⟨(⋃ C' ∈ s, C')ᶜ, hF.isOpen_compl, ?_, ?_⟩
  · simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    exact fun C' h => h.2
  have hVC : (⋃ C' ∈ s, C')ᶜ ⊆ C := by
    intro y hy
    obtain ⟨C'', hC'', hyC''⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible {y} isIrreducible_singleton
    have hxC'' : x ∈ C'' := by
      by_contra hx
      simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hy
      exact hy C'' ⟨hC'', hx⟩ (hyC'' rfl)
    have hcl := isClosed_of_mem_irreducibleComponents _ hC''
    have hgen := hC''.1.isGenericPoint_genericPoint_closure
    rw [hcl.closure_eq] at hgen
    have hgx : hC''.1.genericPoint ⤳ x := by
      rw [specializes_iff_mem_closure, hgen.def]
      exact hxC''
    have hgC : hC''.1.genericPoint ∈ C := hGC (by rw [Scheme.range_fromSpecStalk]; exact hgx)
    have : C'' ⊆ C := by
      rw [← hgen.def]
      exact (isClosed_of_mem_irreducibleComponents _ hC).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hgC)
    exact this (hyC'' rfl)
  exact ⟨⟨x, by simpa using fun C' h => h.2⟩, hC.1.2.open_subset hF.isOpen_compl hVC⟩

private lemma exists_isIntegral_hom [IsLocallyNoetherian S] [IsNormal S]
    (U : AffineElementaryEtaleNeighborhood S s) :
    ∃ V : AffineElementaryEtaleNeighborhood S s, IsIntegral V.obj.obj.scheme ∧
      Nonempty (V ⟶ U) := by
  have : IsAffine U.obj.obj.scheme := U.property
  have : IsNormal U.obj.obj.scheme := isNormal_of_etale U.obj.obj.toBase
  have : IsLocallyNoetherian U.obj.obj.scheme :=
    LocallyOfFiniteType.isLocallyNoetherian U.obj.obj.toBase
  have : IsNoetherian U.obj.obj.scheme := {}
  have : IsDomain (U.obj.obj.scheme.presheaf.stalk U.obj.obj.point) :=
    IsNormal.stalk_isDomain _
  obtain ⟨V₀, hV₀, hu, hirr⟩ := exists_isOpen_isIrreducible U.obj.obj.scheme U.obj.obj.point
  obtain ⟨O, hO, huO, hOV⟩ := exists_isAffineOpen_mem_and_subset (X := U.obj.obj.scheme)
    (x := U.obj.obj.point) (U := ⟨V₀, hV₀⟩) hu
  let W : EtaleNeighborhood S s :=
    { scheme := O
      point := ⟨U.obj.obj.point, huO⟩
      toBase := O.ι ≫ U.obj.obj.toBase
      map_point := U.obj.obj.map_point }
  have hW : W.IsElementary := by
    change IsIso ((S.residueFieldCongr W.map_point).inv ≫
      W.toBase.residueFieldMap W.point)
    rw [Scheme.residueFieldMap_comp]
    change IsIso (((S.residueFieldCongr U.obj.obj.map_point).inv ≫
      U.obj.obj.toBase.residueFieldMap U.obj.obj.point) ≫ O.ι.residueFieldMap W.point)
    exact IsIso.comp_isIso' U.obj.property (inferInstance : IsIso (O.ι.residueFieldMap W.point))
  have hOirr : IsIrreducible (O : Set U.obj.obj.scheme) :=
    ⟨⟨_, huO⟩, hirr.2.open_subset O.isOpen hOV⟩
  have : IrreducibleSpace O := Subtype.irreducibleSpace hOirr
  have : IsIntegral O.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  exact ⟨⟨⟨W, hW⟩, hO⟩, this, ⟨⟨⟨⟨O.ι, rfl, rfl⟩⟩⟩⟩⟩

end Integral

/-! ### The fibre `F_y` as the thickening `F_0` -/

section Fibre

variable {Y Yt : Scheme.{0}} (π : Yt ⟶ Y) (y : Y)

private def residueQuotEquiv :
    (Y.presheaf.stalk y ⧸ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1)) ≃+*
      IsLocalRing.ResidueField (Y.presheaf.stalk y) :=
  Ideal.quotEquivOfEq (by rw [zero_add, pow_one])

private def residueQuotHom : CommRingCat.of (Y.presheaf.stalk y ⧸
    IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1)) ⟶ Y.residueField y :=
  CommRingCat.ofHom (residueQuotEquiv y).toRingHom

private def residueQuotInvHom : Y.residueField y ⟶ CommRingCat.of (Y.presheaf.stalk y ⧸
    IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1)) :=
  CommRingCat.ofHom (residueQuotEquiv y).symm.toRingHom

/-- `Spec κ(y) ⟶ Spec A/𝔪`. -/
private def specResidueQuot :
    Spec (Y.residueField y) ⟶ Spec (CommRingCat.of (Y.presheaf.stalk y ⧸
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1))) :=
  Spec.map (residueQuotHom y)

private def specResidueQuotInv :
    Spec (CommRingCat.of (Y.presheaf.stalk y ⧸
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1))) ⟶ Spec (Y.residueField y) :=
  Spec.map (residueQuotInvHom y)

private lemma specResidueQuotInv_comp : specResidueQuotInv y ≫ specResidueQuot y = 𝟙 _ := by
  rw [specResidueQuotInv, specResidueQuot, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  exact (residueQuotEquiv y).symm_apply_apply x

private lemma specResidueQuot_comp : specResidueQuot y ≫ specResidueQuotInv y = 𝟙 _ := by
  rw [specResidueQuotInv, specResidueQuot, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  exact (residueQuotEquiv y).apply_symm_apply x

private lemma specResidueQuot_fromSpecStalk :
    specResidueQuot y ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1)))) ≫ Y.fromSpecStalk y =
      Y.fromSpecResidueField y := by
  rw [specResidueQuot, ← Category.assoc, ← Spec.map_comp, Scheme.fromSpecResidueField]
  congr 2

/-- `F_y ⟶ F_0`. -/
private def fibreToThickening : pointSettingFibre π y ⟶ pointSettingThickening π y 0 :=
  pullback.lift (pullback.lift (pullback.fst _ _)
      (pullback.snd _ _ ≫ specResidueQuot y ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1)))))
      (by
        calc pullback.fst _ _ ≫ π = pullback.snd _ _ ≫ Y.fromSpecResidueField y :=
              pullback.condition
          _ = pullback.snd _ _ ≫ specResidueQuot y ≫ Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1)))) ≫
                Y.fromSpecStalk y := by rw [specResidueQuot_fromSpecStalk]
          _ = _ := by simp only [Category.assoc]; rfl))
    (pullback.snd _ _ ≫ specResidueQuot y) (by rw [pullback.lift_snd, Category.assoc]; rfl)

private def thickeningToFibre : pointSettingThickening π y 0 ⟶ pointSettingFibre π y :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ specResidueQuotInv y)
    (by
      have h₁ := pullback.condition (f := pullback.snd π (Y.fromSpecStalk y))
        (g := Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1)))))
      have h₂ := specResidueQuot_fromSpecStalk y
      rw [← h₂]
      simp only [Category.assoc]
      rw [← Category.assoc (specResidueQuotInv y), specResidueQuotInv_comp, Category.id_comp,
        pullback.condition, ← Category.assoc, h₁, Category.assoc]
      rfl)

private lemma fibreToThickening_fst_fst :
    fibreToThickening π y ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  unfold fibreToThickening
  rw [pullback.lift_fst_assoc, pullback.lift_fst]

private lemma fibreToThickening_snd :
    fibreToThickening π y ≫ pullback.snd _ _ = pullback.snd _ _ ≫ specResidueQuot y :=
  pullback.lift_snd _ _ _

private lemma fibreToThickening_thickeningToFibre :
    fibreToThickening π y ≫ thickeningToFibre π y = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, thickeningToFibre, pullback.lift_fst, fibreToThickening_fst_fst,
      Category.id_comp]
  · rw [Category.assoc, thickeningToFibre, pullback.lift_snd, ← Category.assoc,
      fibreToThickening_snd, Category.assoc, specResidueQuot_comp, Category.comp_id,
      Category.id_comp]

end Fibre

/-! ### A small cofinal family of neighbourhoods -/

section Small

variable {S : Scheme.{0}} {s : S}

/-- An elementary étale neighbourhood whose scheme is `Spec ℂ[x₁, …, xₙ]/I`. -/
private structure SmallNbhd (S : Scheme.{0}) (s : S) where
  n : ℕ
  I : Ideal (MvPolynomial (Fin n) ℂ)
  toBase : Spec (CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ I)) ⟶ S
  point : Spec (CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ I))
  etale : Etale toBase
  map_point : toBase point = s
  isElementary : IsIso (toBase.residueFieldMap point)

/-- The small neighbourhood as an object of the index category. -/
private def SmallNbhd.toIdx (t : SmallNbhd S s) : Idx S s :=
  op (op ⟨⟨@EtaleNeighborhood.mk S s _ t.point t.toBase t.etale t.map_point,
    (EtaleNeighborhood.isElementary_iff _).mpr t.isElementary⟩,
    inferInstanceAs (IsAffine (Spec _))⟩)

/-- Every affine elementary étale neighbourhood of a point of a scheme of finite type over `ℂ`
receives a map from a small one. -/
private lemma exists_smallNbhd_hom (sS : S ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sS] (X : Idx S s) :
    ∃ t : SmallNbhd S s, Nonempty (t.toIdx ⟶ X) := by
  let U := X.unop.unop
  have : IsAffine U.obj.obj.scheme := U.property
  let Xs := U.obj.obj.scheme
  let φ : CommRingCat.of ℂ ⟶ Γ(Xs, ⊤) :=
    (Scheme.ΓSpecIso (.of ℂ)).inv ≫ (U.obj.obj.toBase ≫ sS).appTop
  have h₁ : (U.obj.obj.toBase ≫ sS).appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  have hft : φ.hom.FiniteType :=
    h₁.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective)
  letI := φ.hom.toAlgebra
  have : Algebra.FiniteType ℂ Γ(Xs, ⊤) := hft
  obtain ⟨n, ψ, hψ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp this
  let e : CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ RingHom.ker ψ.toRingHom) ≅ Γ(Xs, ⊤) :=
    (RingHom.quotientKerEquivOfSurjective (f := ψ.toRingHom) hψ).toCommRingCatIso
  let ψS : Spec (CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ RingHom.ker ψ.toRingHom)) ≅ Xs :=
    (Scheme.Spec.mapIso e.op).symm ≪≫ Xs.isoSpec.symm
  have hu : ψS.hom (ψS.inv U.obj.obj.point) = U.obj.obj.point := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  have hel : IsIso (U.obj.obj.toBase.residueFieldMap U.obj.obj.point) :=
    (EtaleNeighborhood.isElementary_iff _).mp U.obj.property
  let t : SmallNbhd S s :=
    { n := n
      I := RingHom.ker ψ.toRingHom
      toBase := ψS.hom ≫ U.obj.obj.toBase
      point := ψS.inv U.obj.obj.point
      etale := inferInstance
      map_point := by rw [Scheme.Hom.comp_apply, hu, U.obj.obj.map_point]
      isElementary := by
        rw [Scheme.residueFieldMap_comp]
        have h₂ : IsIso (U.obj.obj.toBase.residueFieldMap (ψS.hom (ψS.inv U.obj.obj.point))) := by
          rwa [hu]
        have : IsOpenImmersion ψS.hom := inferInstance
        exact IsIso.comp_isIso' h₂ (inferInstance : IsIso (ψS.hom.residueFieldMap _)) }
  let f : t.toIdx.unop.unop ⟶ U := ⟨⟨⟨ψS.hom, rfl, hu⟩⟩⟩
  exact ⟨t, ⟨f.op.op⟩⟩

end Small

/-! ### The comparison of the fibre maps -/

section FibreMap

variable {Y Yt : Scheme.{0}} (π : Yt ⟶ Y) (y : Y) {Rh : Type} [CommRing Rh] [IsLocalRing Rh]
  [Algebra (Y.presheaf.stalk y) Rh]

/-- The closed immersion `F_0 ⟶ Ỹ ×_Y Spec Rh` induced by an `𝒪_{Y,y}`-algebra map
`ρ : Rh ⟶ 𝒪_{Y,y}/𝔪`. -/
private def thickeningToLimit
    (ρ : Rh →ₐ[Y.presheaf.stalk y] Y.presheaf.stalk y ⧸
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1)) :
    pointSettingThickening π y 0 ⟶ limitPt y Rh π :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom ρ.toRingHom)) (𝟙 _)
    (by simp) (by
      rw [Category.comp_id]
      exact (congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x ↦
        (ρ.commutes x).symm))).trans (Spec.map_comp _ _))

variable (ι : affineGlobalSections Y y ⟶ (Functor.const _).obj (CommRingCat.of Rh))
  (hι : ∀ U : (AffineElementaryEtaleNeighborhood Y y)ᵒᵖ,
    IsOverStalk Y y Rh U.unop.obj (ι.app U).hom)

include hι in
/-- The identification of `F_y` with the scheme fibre of `Ỹ ×_Y U ⟶ U` over the distinguished
point factors through `F_y = F_0 ⟶ Ỹ ×_Y Spec Rh ⟶ Ỹ ×_Y U`. -/
private lemma localEtaleFibreMap_eq (j : Idx Y y) (σ : CommRingCat.of Rh ⟶ Y.residueField y)
    [IsLocalHom σ.hom] (hσ : σ.hom.comp (algebraMap _ Rh) = (Y.residue y).hom)
    (ρ : Rh →ₐ[Y.presheaf.stalk y] Y.presheaf.stalk y ⧸
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1))
    (hρ : CommRingCat.ofHom ρ.toRingHom ≫ residueQuotHom y = σ) :
    localEtaleFibreMap π j.unop.unop.obj =
      fibreToThickening π y ≫ thickeningToLimit π y ρ ≫ stageConeπ π ι hι j := by
  apply stage_hom_ext π
  · have h₁ : thickeningToLimit π y ρ ≫ pullback.fst _ _ = pullback.fst _ _ :=
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    rw [Category.assoc, Category.assoc, stageConeπ_fst, reassoc_of% h₁,
      fibreToThickening_fst_fst]
    exact localEtaleFibreMap_fst π _
  · have h₁ : thickeningToLimit π y ρ ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ρ.toRingHom) :=
      pullback.lift_snd _ _ _
    have h₂ : specResidueQuot y ≫ Spec.map (CommRingCat.ofHom ρ.toRingHom) = Spec.map σ := by
      rw [specResidueQuot, ← Spec.map_comp, hρ]
    rw [Category.assoc, Category.assoc, stageConeπ_snd, reassoc_of% h₁,
      reassoc_of% (fibreToThickening_snd π y), reassoc_of% h₂, specMap_comp_leg ι hι j σ hσ]
    exact localEtaleFibreMap_snd π _

end FibreMap

/-! ### Henselization data -/

/-- A henselization `Rh` of `𝒪_{S,s}` with the induced maps `σ : Rh ⟶ κ(s)` and
`ρ : Rh ⟶ 𝒪_{S,s}/𝔪`. -/
private lemma exists_henselization_data (S : Scheme.{0}) (s : S) :
    ∃ (Rh : Type) (_ : CommRing Rh) (_ : IsLocalRing Rh) (_ : Algebra (S.presheaf.stalk s) Rh)
      (_ : IsLocalRing.IsHenselization (S.presheaf.stalk s)
        (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh)
      (σ : CommRingCat.of Rh ⟶ S.residueField s) (_ : IsLocalHom σ.hom)
      (_ : σ.hom.comp (algebraMap _ Rh) = (S.residue s).hom)
      (ρ : Rh →ₐ[S.presheaf.stalk s] S.presheaf.stalk s ⧸
        IsLocalRing.maximalIdeal (S.presheaf.stalk s) ^ (0 + 1)),
      CommRingCat.ofHom ρ.toRingHom ≫ residueQuotHom s = σ := by
  obtain ⟨Rh, hCR, hAlg, hLR, hLH, hhens, hind, -, hres⟩ :=
    IsLocalRing.exists_henselization (S.presheaf.stalk s)
  let e : IsLocalRing.ResidueField (S.presheaf.stalk s) ≃+* IsLocalRing.ResidueField Rh :=
    RingEquiv.ofBijective (IsLocalRing.ResidueField.map (algebraMap (S.presheaf.stalk s) Rh)) hres
  have hH : IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh :=
    { henselian := hhens
      ind_etale := (CommAlgCat.etale _).ind.prop_of_iso
        (CommAlgCat.isoMk (ULift.algEquiv : ULift.{0} _ ≃ₐ[_] _).symm) hind
      exists_residueFieldEquiv := ⟨e, fun x => by simp [e, IsLocalRing.ResidueField.map_residue]⟩ }
  let σ₀ : Rh →+* IsLocalRing.ResidueField (S.presheaf.stalk s) :=
    e.symm.toRingHom.comp (IsLocalRing.residue Rh)
  have hσ₀ : σ₀.comp (algebraMap _ Rh) = IsLocalRing.residue _ := by
    ext x
    change e.symm (IsLocalRing.residue Rh (algebraMap _ Rh x)) = _
    rw [← IsLocalRing.ResidueField.map_residue, RingEquiv.symm_apply_eq]
    rfl
  have : IsLocalHom σ₀ := RingHom.isLocalHom_comp _ _
  let ρ : Rh →ₐ[S.presheaf.stalk s] S.presheaf.stalk s ⧸
      IsLocalRing.maximalIdeal (S.presheaf.stalk s) ^ (0 + 1) :=
    { toRingHom := (residueQuotEquiv s).symm.toRingHom.comp σ₀
      commutes' := fun x => by
        change (residueQuotEquiv s).symm (σ₀ (algebraMap _ Rh x)) = Ideal.Quotient.mk _ x
        rw [show σ₀ (algebraMap _ Rh x) = IsLocalRing.residue _ x from
          congrArg (fun φ => φ x) hσ₀, RingEquiv.symm_apply_eq]
        rfl }
  refine ⟨Rh, hCR, hLR, hAlg, hH, CommRingCat.ofHom σ₀, ‹_›, hσ₀, ρ, ?_⟩
  ext x
  exact (residueQuotEquiv s).apply_symm_apply (σ₀ x)

/-! ### Affine varieties are quasi-projective -/

/-- An affine morphism locally of finite type is quasi-projective: the structure sheaf is
relatively ample. -/
private lemma isQuasiProjective_of_isAffineHom {X S : Scheme.{0}} (f : X ⟶ S) [IsAffineHom f]
    [LocallyOfFiniteType f] : IsQuasiProjective f := by
  refine ⟨⟨inferInstance, inferInstance⟩, Stacks.Ample.unitModule X,
    Stacks.Ample.isInvertibleModule_unit X, ?_⟩
  refine (Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple f
    (Stacks.Ample.unitModule X)).mp ?_
  refine (Stacks.RelativeAmple.isRelativelyAmple_unitModule_iff f).mpr ?_
  intro V hV
  have : IsAffine (f ⁻¹ᵁ V).toScheme := hV.preimage f
  infer_instance

/-! ### Descent of the line bundles to an integral neighbourhood -/

/-- **Descent of the line bundles.** In a threefold point setting, line bundles `M_i` on the
scheme fibre `F_y` extend to `Ỹ ×_Y U` for some affine elementary étale neighbourhood `(U, u)`
of `(Y, y)` with `U` integral: they extend to `Ỹ ×_Y Spec Aʰ` over a henselization `Aʰ` of
`𝒪_{Y,y}`, this is the limit of the `Ỹ ×_Y U`, and invertible modules descend to a stage of the
limit. -/
private lemma exists_isIntegral_bundles
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {y : Y} (h : IsThreefoldPointSetting sY π y)
    {ι : Type*} [Finite ι] (M : ι → (pointSettingFibre π y).Modules)
    (hM : ∀ i, SheafOfModules.IsInvertible (pointSettingFibre π y).presheaf
      (pointSettingFibre π y).ringCatSheaf.2 (M i)) :
    ∃ (V : AffineElementaryEtaleNeighborhood Y y)
      (N : ι → (pullback π V.obj.obj.toBase).Modules),
      IsIntegral V.obj.obj.scheme ∧
      (∀ i, SheafOfModules.IsInvertible (pullback π V.obj.obj.toBase).presheaf
          (pullback π V.obj.obj.toBase).ringCatSheaf.2 (N i)) ∧
      ∀ i, Nonempty ((Scheme.Modules.pullback (localEtaleFibreMap π V.obj)).obj (N i) ≅ M i) := by
  obtain ⟨hvarY, -, -, hprojπ, -⟩ := h.isResolution
  have : IsProper π := isProper_of_isProjectiveMorphism _ hprojπ
  -- a henselization `Aʰ` of `A = 𝒪_{Y,y}`
  obtain ⟨Ah, _, _, _, _, σ, _, hσ, ρ, hρ⟩ := exists_henselization_data Y y
  -- the line bundles on `F_0`, and their extensions to `Z_{Aʰ}`
  let L₀ : ι → (pointSettingThickening π y 0).Modules :=
    fun i => (Scheme.Modules.pullback (thickeningToFibre π y)).obj (M i)
  have hL₀ : ∀ i, Stacks.Ample.IsInvertibleModule _ (L₀ i) := fun i =>
    haveI := hM i
    SheafOfModules.isInvertible_pullback _ _
  obtain ⟨Lh, hLh, eLh⟩ := h.exists_isInvertibleModule_pullback_henselization_iso ρ L₀ hL₀
  -- `Z_{Aʰ}` is the limit of the `Ỹ ×_Y U`, and the extensions descend to a stage
  obtain ⟨hF, ιc, hover, ⟨hc⟩⟩ :=
    isFiltered_affineElementaryEtaleNeighborhood_and_isColimit Y y Ah
  -- restrict to the small neighbourhoods, which form an initial subcategory
  let G := inducedFunctor (fun t : SmallNbhd Y y => t.toIdx)
  have hcof : ∀ X : Idx Y y, ∃ t, Nonempty (G.obj t ⟶ X) :=
    fun X => exists_smallNbhd_hom sY X
  have : IsCofiltered (InducedCategory (Idx Y y) (fun t : SmallNbhd Y y => t.toIdx)) :=
    IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful G hcof
  have : G.Initial := Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful G hcof
  have hlimG := (Functor.Initial.isLimitWhiskerEquiv G (stageCone π ιc hover)).symm
    (isLimitStageCone π ιc hover hc)
  have : ∀ {i j} (f : i ⟶ j), IsAffineHom ((G ⋙ stage π).map f) :=
    fun f => isAffineHom_stage_map π (G.map f)
  have : ∀ i, CompactSpace ((G ⋙ stage π).obj i) := fun i => compactSpace_stage_obj π (G.obj i)
  have : ∀ i, QuasiSeparatedSpace ((G ⋙ stage π).obj i) :=
    fun i => quasiSeparatedSpace_stage_obj π (G.obj i)
  choose jj N₀ hN₀ eN₀ using fun i =>
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit
      (D := G ⋙ stage π) (c := (stageCone π ιc hover).whisker G) hlimG (Lh i) (hLh i)
  -- a common stage, which may be taken integral
  classical
  haveI := Fintype.ofFinite ι
  obtain ⟨j₁, hj₁⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image jj)
  obtain ⟨V, hVint, ⟨a⟩⟩ := exists_isIntegral_hom (G.obj j₁).unop.unop
  let j : Idx Y y := op (op V)
  let g : ∀ i, j ⟶ G.obj (jj i) := fun i =>
    a.op.op ≫ G.map (hj₁ (Finset.mem_image_of_mem _ (Finset.mem_univ i))).some
  let N : ι → ((stage π).obj j).Modules := fun i =>
    (Scheme.Modules.pullback ((stage π).map (g i))).obj (N₀ i)
  have eN : ∀ i, Lh i ≅ (Scheme.Modules.pullback (stageConeπ π ιc hover j)).obj (N i) := fun i =>
    (eN₀ i).some ≪≫
      (Scheme.Modules.pullbackCongr ((stageCone π ιc hover).w (g i)).symm).app (N₀ i) ≪≫
      ((Scheme.Modules.pullbackComp _ _).app (N₀ i)).symm
  have hfib := localEtaleFibreMap_eq π y ιc hover j σ hσ ρ hρ
  refine ⟨V, N, hVint, fun i => @SheafOfModules.isInvertible_pullback _ _ _ _ (hN₀ i),
    fun i => ?_⟩
  exact ⟨(Scheme.Modules.pullbackCongr (hfib.trans (Category.assoc _ _ _).symm)).app (N i) ≪≫
      ((Scheme.Modules.pullbackComp _ _).app (N i)).symm ≪≫
      (Scheme.Modules.pullback _).mapIso (eN i).symm ≪≫
      ((Scheme.Modules.pullbackComp _ _).app (Lh i)).symm ≪≫
      (Scheme.Modules.pullback _).mapIso (eLh i).some ≪≫
      (Scheme.Modules.pullbackComp _ _).app (M i) ≪≫
      (Scheme.Modules.pullbackCongr (fibreToThickening_thickeningToFibre π y)).app (M i) ≪≫
      (Scheme.Modules.pullbackId _).app (M i)⟩

/-! ### Dimension and closed points of étale neighbourhoods -/

/-- An étale morphism is étale at every point. -/
private lemma etaleAt_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (x : X) :
    EtaleAt f x := by
  obtain ⟨V, hV, hxV, -⟩ := (Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens Y))
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUV⟩ := (Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens X))
    (show x ∈ f ⁻¹ᵁ V from hxV)
  exact ⟨U, hU, hxU, V, hV, hUV, HasRingHomProperty.appLE @Etale f ‹_› ⟨V, hV⟩ ⟨U, hU⟩ hUV⟩

/-- An irreducible scheme étale over an irreducible scheme `X` locally of finite type over a
field has the dimension of `X`: its generic point maps to the generic point of `X`, and the
residue field extension there is finite. -/
private lemma topologicalKrullDim_eq_of_etale {k : Type} [Field k] {X U : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [IrreducibleSpace X] [IrreducibleSpace U]
    (ψ : U ⟶ X) [Etale ψ] : topologicalKrullDim U = topologicalKrullDim X := by
  have hX := (genericPoint_spec X)
  have hU := (genericPoint_spec U)
  obtain ⟨η', hη', hψη'⟩ :=
    Flat.generalizingMap ψ (hX.specializes (Set.mem_univ (ψ (genericPoint U))))
  have hψ : ψ (genericPoint U) = genericPoint X := by
    have h1 : genericPoint U ⤳ η' := hU.specializes (Set.mem_univ _)
    have h2 := h1.map ψ.continuous
    rw [hψη'] at h2
    exact (h2.antisymm (hX.specializes (Set.mem_univ _))).eq
  have e : ∀ (T : Scheme.{0}) [IrreducibleSpace T],
      topologicalKrullDim (closure ({genericPoint T} : Set T)) = topologicalKrullDim T := by
    intro T _
    rw [(genericPoint_spec T).def]
    exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ T).isHomeomorph
  rw [← e U, ← e X, ← hψ,
    MMP.topologicalKrullDim_closure_singleton_eq_toENat_residueTrdeg (ψ ≫ sX),
    MMP.topologicalKrullDim_closure_singleton_eq_toENat_residueTrdeg sX,
    Stacks.Chow.residueTrdeg_comp,
    Stacks.PurityRamification.residueTrdeg_eq_zero_of_etaleAt ψ (etaleAt_of_etale ψ _),
    add_zero]

/-- The distinguished point of an elementary étale neighbourhood `(U, u)` of a closed point `s`
of a scheme locally of finite type over a field is closed. -/
private lemma isClosed_singleton_point {k : Type} [Field k] {S : Scheme.{0}} {s : S}
    (sS : S ⟶ Spec (.of k)) [LocallyOfFiniteType sS] (U : ElementaryEtaleNeighborhood S s)
    (hs : IsClosed ({s} : Set S)) : IsClosed ({U.obj.point} : Set U.obj.scheme) := by
  have : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace sS
  have : JacobsonSpace U.obj.scheme := LocallyOfFiniteType.jacobsonSpace U.obj.toBase
  have : IsIso U.obj.residueFieldMap := U.property
  rw [isClosed_singleton_iff_locallyOfFiniteType] at hs ⊢
  have : LocallyOfFiniteType
      (U.obj.scheme.fromSpecResidueField U.obj.point ≫ U.obj.toBase) := by
    rw [fromSpecResidueField_toBase]
    infer_instance
  exact LocallyOfFiniteType.of_comp (f := U.obj.scheme.fromSpecResidueField U.obj.point)
    (g := U.obj.toBase) this

/-! ### Étale base change of the resolution -/

/-- In a threefold point setting, the base change `π_U` of `π` along an étale morphism
`q : U ⟶ Y` from a variety has integral source, smooth over `ℂ`, and is projective, birational
and an isomorphism over `q⁻¹(Y_reg)`. -/
private lemma pullback_snd_properties
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {y : Y} (h : IsThreefoldPointSetting sY π y)
    {U : Scheme.{0}} (q : U ⟶ Y) [Etale q] [AlgebraicGeometry.IsVariety ℂ (q ≫ sY)] :
    IsIntegral (pullback π q) ∧ Smooth (pullback.snd π q ≫ q ≫ sY) ∧
      IsProjectiveMorphism (pullback.snd π q) ∧ IsBirationalMorphism (pullback.snd π q) ∧
      IsBiregular (pullback.snd π q) (q ⁻¹ᵁ smoothLocus sY) := by
  obtain ⟨hvarY, hvarYt, hsmYt, hprojπ, -⟩ := h.isResolution
  have : IsNormal U := isNormal_of_etale q
  have hdense : Dense (smoothLocus sY : Set Y) :=
    (smoothLocus sY).isOpen.dense
      ⟨_, MMP.Threefold.Mori.OpenRestriction.genericPoint_mem_smoothLocus' (k := ℂ) (f := sY)⟩
  have : Smooth (π ≫ sY) := (MMP.Mori.isSmoothScheme_iff (π ≫ sY)).mp hsmYt
  obtain ⟨hv, hsm, hproj, hiso, hbir, -⟩ := MMP.Fourfold.isVariety_pullback_snd_of_etale
    (k := ℂ) (s₀ := sY) (sₑ := q ≫ sY) (sW := π ≫ sY) q rfl π rfl
    hprojπ (smoothLocus sY) hdense h.isBiregular
  exact ⟨hv.toIsIntegral, hsm, hproj, hbir, hiso⟩

/-- **Étale extension of line bundles from the closed fibre.** For a threefold point setting
`(Y, π, y)` and a finite family of line bundles `M i` on the scheme fibre `F_y`, there are an
elementary étale neighbourhood `(U, u)` of `(Y, y)` with `U` a normal integral quasi-projective
complex threefold and `u` closed, and line bundles `Mt i` on `Ũ = Ỹ ×_Y U` restricting to `M i`
along `MMP.Fourfold.localEtaleFibreMap π U : F_y ⟶ Ũ`, such that `Ũ` is integral and smooth
over `ℂ` and `π_U : Ũ ⟶ U` is projective, birational and an isomorphism over `q_U⁻¹(Y_reg)`. -/
@[mmp "lem_mmp_indexb_etale_lines"]
public theorem IsThreefoldPointSetting.exists_elementaryEtaleNeighborhood_isInvertible
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {y : Y} (h : IsThreefoldPointSetting sY π y)
    {ι : Type*} [Finite ι] (M : ι → (pointSettingFibre π y).Modules)
    (hM : ∀ i, SheafOfModules.IsInvertible (pointSettingFibre π y).presheaf
      (pointSettingFibre π y).ringCatSheaf.2 (M i)) :
    ∃ U : ElementaryEtaleNeighborhood Y y,
      IsIntegral U.obj.scheme ∧ IsLocallyNoetherian U.obj.scheme ∧ IsNormal U.obj.scheme ∧
      IsQuasiProjectiveVariety ℂ (U.obj.toBase ≫ sY) ∧
      IsNormalVariety ℂ (U.obj.toBase ≫ sY) ∧
      topologicalKrullDim U.obj.scheme = 3 ∧
      IsClosed ({U.obj.point} : Set U.obj.scheme) ∧
      (∃ Mt : ι → (pullback π U.obj.toBase).Modules,
        (∀ i, SheafOfModules.IsInvertible (pullback π U.obj.toBase).presheaf
          (pullback π U.obj.toBase).ringCatSheaf.2 (Mt i)) ∧
        ∀ i, Nonempty ((Scheme.Modules.pullback (localEtaleFibreMap π U)).obj (Mt i) ≅ M i)) ∧
      IsIntegral (pullback π U.obj.toBase) ∧
      Smooth (pullback.snd π U.obj.toBase ≫ U.obj.toBase ≫ sY) ∧
      IsProjectiveMorphism (pullback.snd π U.obj.toBase) ∧
      IsBirationalMorphism (pullback.snd π U.obj.toBase) ∧
      IsBiregular (pullback.snd π U.obj.toBase) (U.obj.toBase ⁻¹ᵁ smoothLocus sY) := by
  obtain ⟨V, N, hVint, hN, eR⟩ := exists_isIntegral_bundles h M hM
  haveI := h.isResolution.1
  have : IsAffine V.obj.obj.scheme := V.property
  have : IsAffineHom (V.obj.obj.toBase ≫ sY) := isAffineHom_of_isAffine _
  have : AlgebraicGeometry.IsVariety ℂ (V.obj.obj.toBase ≫ sY) := { }
  have hnorm : IsNormal V.obj.obj.scheme := isNormal_of_etale V.obj.obj.toBase
  obtain ⟨hint, hsm, hproj, hbir, hbireg⟩ := pullback_snd_properties h V.obj.obj.toBase
  refine ⟨V.obj, hVint, LocallyOfFiniteType.isLocallyNoetherian V.obj.obj.toBase, hnorm,
    ⟨isQuasiProjective_of_isAffineHom _⟩, ⟨inferInstance, hnorm⟩, ?_,
    isClosed_singleton_point sY V.obj h.isClosed_singleton, ⟨N, hN, eR⟩,
    hint, hsm, hproj, hbir, hbireg⟩
  rw [topologicalKrullDim_eq_of_etale sY V.obj.obj.toBase, h.topologicalKrullDim_eq]

end EtaleLines

/-! ### The product local étale datum -/

section ProductLocalDatum

open TopologicalSpace MMP.Mori

/-! ### Residue fields -/

/-- A morphism surjective on stalks induces isomorphisms of residue fields. -/
private theorem isIso_residueFieldMap_of_surjectiveOnStalks {X Y : Scheme.{u}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : IsIso (f.residueFieldMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(f.residueFieldMap x).hom.injective, fun a => ?_⟩
  obtain ⟨s, rfl⟩ := X.residue_surjective x a
  obtain ⟨t, rfl⟩ := f.stalkMap_surjective x s
  exact ⟨Y.residue (f x) t, by
    rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩

/-- Two morphisms `Spec K ⟶ X` through a point `x` agree once they agree after a morphism
`t : X ⟶ S` inducing an isomorphism `κ(t x) ≅ κ(x)`. -/
private theorem SpecMap_comp_fromSpecResidueField_eq_of_comp {X S : Scheme.{u}}
    {K : CommRingCat.{u}}
    (t : X ⟶ S) (x : X) [IsIso (t.residueFieldMap x)] (α β : X.residueField x ⟶ K)
    (h : Spec.map α ≫ X.fromSpecResidueField x ≫ t = Spec.map β ≫ X.fromSpecResidueField x ≫ t) :
    Spec.map α ≫ X.fromSpecResidueField x = Spec.map β ≫ X.fromSpecResidueField x := by
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc, cancel_mono, Spec.map_inj, cancel_epi] at h
  rw [h]

/-! ### Open subschemes of varieties -/

section OpenImmersion

variable {k : Type u} [Field k] {V X : Scheme.{u}} (f : V ⟶ X) [IsOpenImmersion f] [Nonempty V]

/-- A nonempty open subscheme of a variety is a variety. -/
private theorem isVariety_comp_of_isOpenImmersion {sX : X ⟶ Spec (.of k)}
    (h : AlgebraicGeometry.IsVariety k sX) :
    AlgebraicGeometry.IsVariety k (f ≫ sX) := by
  have := h
  have : IsIntegral X := h.toIsIntegral
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  have : IsIntegral V := isIntegral_of_isOpenImmersion f
  exact { }

/-- A nonempty open subscheme of a quasi-projective variety is a quasi-projective variety. -/
private theorem isQuasiProjectiveVariety_comp_of_isOpenImmersion {sX : X ⟶ Spec (.of k)}
    (h : IsQuasiProjectiveVariety k sX) : IsQuasiProjectiveVariety k (f ≫ sX) := by
  obtain ⟨hv, n, i, hi, hiq, hio⟩ := (isQuasiProjectiveVariety_iff_isHQuasiProjective k sX).1 h
  have hv' := isVariety_comp_of_isOpenImmersion f hv
  have : IsLocallyNoetherian X := @LocallyOfFiniteType.isLocallyNoetherian _ _ sX
    hv.toLocallyOfFiniteType _
  have : CompactSpace X := @QuasiCompact.compactSpace_of_compactSpace _ _ sX hv.toQuasiCompact _
  have : IsNoetherian X := ⟨⟩
  refine (isQuasiProjectiveVariety_iff_isHQuasiProjective k _).2
    ⟨hv', n, f ≫ i, @IsImmersion.comp _ _ _ _ _ inferInstance hi,
      @quasiCompact_comp _ _ _ _ _ inferInstance hiq, by rw [Category.assoc, hio]⟩

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_comp_of_isOpenImmersion {sX : X ⟶ Spec (.of k)}
    (h : IsNormalVariety k sX) : IsNormalVariety k (f ≫ sX) := by
  have := h.2
  exact ⟨isVariety_comp_of_isOpenImmersion f h.1, isNormal_of_etale f⟩

end OpenImmersion

/-! ### `ℚ`-factoriality of open subschemes -/

section QFactorial

variable {V X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] (f : V ⟶ X) [IsOpenImmersion f]

/-- The restriction of a Cartier divisor along a dominant open immersion is Cartier: a local
equation restricts to a local equation, orders along prime divisors being computed in the
local rings, which the open immersion identifies. -/
private theorem isCartier_comapDomain [IsDominant f] {D : Divisor X} (h : D.IsCartier) :
    Divisor.IsCartier (Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap f) D
      (OpenWeilRestriction.primeDivisorMap_injective f).injOn) := by
  intro x
  obtain ⟨W, hxW, φ, hφ⟩ := h (f x)
  obtain ⟨g, hg, hφg⟩ := MMP.Positivity.exists_ord_eq_of_units φ
  obtain ⟨φ', hφ'⟩ := MMP.Positivity.exists_units_of_ne_zero
    ((map_ne_zero (functionFieldMap f)).2 hg)
  refine ⟨f ⁻¹ᵁ W, hxW, φ', fun E hE => ?_⟩
  have hP : ((OpenWeilRestriction.primeDivisorMap f E).support ∩ W).Nonempty := by
    rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff]
    exact (congrArg (· ∈ W) (OpenWeilRestriction.genericPoint_primeDivisorMap f E)).mpr
      ((E.genericPoint_mem_iff _).2 hE)
  change D (OpenWeilRestriction.primeDivisorMap f E) = _
  rw [show D (OpenWeilRestriction.primeDivisorMap f E) = D.coeff _ from rfl, hφ _ hP, hφg, hφ',
    MMP.Positivity.ord_functionFieldMap_of_isIso f E _
      (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm]

/-- **`ℚ`-factoriality passes to nonempty open subschemes.** A divisor `D` on `V` is the
restriction of its extension by closure to `X`, a multiple of which is Cartier. -/
private theorem isQFactorial_comp_of_isOpenImmersion [Nonempty V] {sX : X ⟶ Spec (.of ℂ)}
    (h : IsQFactorial sX) : IsQFactorial (f ≫ sX) := by
  haveI : IsDominant f := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion f
  refine ⟨isNormalVariety_comp_of_isOpenImmersion f h.1, fun D => ?_⟩
  obtain ⟨m, hm, hmD⟩ := h.2 (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap f) D)
  refine ⟨m, hm, ?_⟩
  have := isCartier_comapDomain f hmD
  rwa [Finsupp.comapDomain_smul _ _ (OpenWeilRestriction.primeDivisorMap_injective f).injOn,
    Finsupp.comapDomain_mapDomain _ (OpenWeilRestriction.primeDivisorMap_injective f)] at this

end QFactorial

/-! ### The curve `{x} × A` -/

/-- Let `q = q_X × j : X ×_S A ⟶ Y ×_S P` with `j` an open immersion, and let `x ∈ X` with
`κ(q_X x) ≅ κ(x)`. The curve `{x} × A = Spec κ(x) ×_S A` maps by an open immersion into
`{q_X x} × P = Spec κ(q_X x) ×_S P`, compatibly with the inclusions, which are preimmersions.
Hence the generic point of `{x} × A` maps to the generic point of `{q_X x} × P`, with an
isomorphism of residue fields. -/
private theorem map_genericPoint_and_isIso_residueFieldMap {S Y P X A : Scheme.{u}}
    (sY : Y ⟶ S) (sP : P ⟶ S) (qX : X ⟶ Y) (j : A ⟶ P) [IsOpenImmersion j] (x : X)
    [IsIso (qX.residueFieldMap x)] {η : ↥(pullback (qX ≫ sY) (j ≫ sP))}
    (hη : IsGenericPoint η ((pullback.fst (qX ≫ sY) (j ≫ sP)).base ⁻¹' {x}))
    {ξ : ↥(pullback sY sP)} (hξ : IsGenericPoint ξ ((pullback.fst sY sP).base ⁻¹' {qX x})) :
    (pullback.map (qX ≫ sY) (j ≫ sP) sY sP qX j (𝟙 S) (by simp) (by simp)).base η = ξ ∧
      IsIso ((pullback.map (qX ≫ sY) (j ≫ sP) sY sP qX j (𝟙 S) (by simp)
        (by simp)).residueFieldMap η) := by
  set q := pullback.map (qX ≫ sY) (j ≫ sP) sY sP qX j (𝟙 S) (by simp) (by simp)
  haveI : MorphismProperty.IsStableUnderComposition @IsPreimmersion :=
    ⟨fun _ _ _ _ => inferInstance⟩
  let iu := pullback.map (X.fromSpecResidueField x ≫ qX ≫ sY) (j ≫ sP) (qX ≫ sY) (j ≫ sP)
    (X.fromSpecResidueField x) (𝟙 A) (𝟙 S) (by simp) (by simp)
  let iy := pullback.map (Y.fromSpecResidueField (qX x) ≫ sY) sP sY sP
    (Y.fromSpecResidueField (qX x)) (𝟙 P) (𝟙 S) (by simp) (by simp)
  let o := pullback.map (X.fromSpecResidueField x ≫ qX ≫ sY) (j ≫ sP)
    (Y.fromSpecResidueField (qX x) ≫ sY) sP (Spec.map (qX.residueFieldMap x)) j (𝟙 S)
    (by simp) (by simp)
  have hiu : IsPreimmersion iu :=
    MorphismProperty.pullbackMap (P := @IsPreimmersion) (inferInstance : IsPreimmersion
      (X.fromSpecResidueField x)) (inferInstance : IsPreimmersion (𝟙 A)) rfl (by simp)
  have hiy : IsPreimmersion iy :=
    MorphismProperty.pullbackMap (P := @IsPreimmersion) (inferInstance : IsPreimmersion
      (Y.fromSpecResidueField (qX x))) (inferInstance : IsPreimmersion (𝟙 P)) rfl (by simp)
  have ho : IsOpenImmersion o :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (inferInstance : IsOpenImmersion
      (Spec.map (qX.residueFieldMap x))) ‹IsOpenImmersion j› (by simp) rfl
  have hsq : iu ≫ q = o ≫ iy := by
    simp only [iu, iy, o, q]
    rw [pullback.map_comp, pullback.map_comp]
    congr 1 <;> simp
  have hru : Set.range iu.base = (pullback.fst (qX ≫ sY) (j ≫ sP)).base ⁻¹' {x} := by
    simp [iu, Scheme.Pullback.range_map, Scheme.range_fromSpecResidueField]
  have hry : Set.range iy.base = (pullback.fst sY sP).base ⁻¹' {qX x} := by
    simp [iy, Scheme.Pullback.range_map, Scheme.range_fromSpecResidueField]
  obtain ⟨c, rfl⟩ : η ∈ Set.range iu.base := hru ▸ hη.mem
  obtain ⟨z, rfl⟩ : ξ ∈ Set.range iy.base := hry ▸ hξ.mem
  have hgen : ∀ c', c ⤳ c' := fun c' => by
    rw [← (IsPreimmersion.isEmbedding iu).isInducing.specializes_iff, specializes_iff_mem_closure,
      hη.def, ← hru]
    exact ⟨c', rfl⟩
  obtain ⟨O, hO, hOo⟩ := (IsPreimmersion.isEmbedding iy).isInducing.isOpen_iff.mp
    o.isOpenEmbedding.isOpen_range
  have hzO : iy.base z ∈ O := by
    rw [hξ.mem_open_set_iff hO]
    refine ⟨iy.base (o.base c), ?_, ?_⟩
    · rw [← hry]; exact ⟨_, rfl⟩
    · change o.base c ∈ iy.base ⁻¹' O
      rw [hOo]; exact ⟨c, rfl⟩
  obtain ⟨c', hc'⟩ : z ∈ Set.range o.base := hOo ▸ hzO
  have hqc : q.base (iu.base c) = iy.base (o.base c) := by
    rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]
  refine ⟨?_, ?_⟩
  · rw [hqc]
    refine (Specializes.antisymm ?_ ?_).eq
    · rw [← hc']
      exact ((hgen c').map o.base.hom.continuous).map iy.base.hom.continuous
    · rw [specializes_iff_mem_closure, hξ.def, ← hry]
      exact ⟨_, rfl⟩
  · have h1 := isIso_residueFieldMap_of_surjectiveOnStalks iy (o.base c)
    have h2 : IsIso (o.residueFieldMap c) := inferInstance
    have h3 := isIso_residueFieldMap_of_surjectiveOnStalks iu c
    have key : ∀ f : _ ⟶ pullback sY sP, f = o ≫ iy → IsIso (f.residueFieldMap c) := by
      rintro f rfl
      rw [Scheme.residueFieldMap_comp]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
    have h4 := key _ hsq
    rw [Scheme.residueFieldMap_comp] at h4
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h3 h4

/-! ### Products with an open subscheme of the second factor -/

section Products

variable {S X X' A B : Scheme.{u}} (sX : X ⟶ S) (sB : B ⟶ S) (j : A ⟶ B)

/-- `X ×_S A` is the base change of `X ×_S B` along `j : A ⟶ B`. -/
private theorem isPullback_map_id_snd :
    IsPullback (pullback.snd sX (j ≫ sB))
      (pullback.map sX (j ≫ sB) sX sB (𝟙 X) j (𝟙 S) (by simp) (by simp)) j
      (pullback.snd sX sB) := by
  refine IsPullback.of_bot ?_ (by simp [pullback.lift_snd]) (IsPullback.of_hasPullback sX sB).flip
  convert (IsPullback.of_hasPullback sX (j ≫ sB)).flip using 1
  simp [pullback.lift_fst]

/-- `g × id_L : X' ×_S L ⟶ X ×_S L` is the base change of `g` along the first projection. -/
private theorem isPullback_map_fst (g : X' ⟶ X) (sL : A ⟶ S) :
    IsPullback (pullback.map (g ≫ sX) sL sX sL g (𝟙 A) (𝟙 S) (by simp) (by simp))
      (pullback.fst (g ≫ sX) sL) (pullback.fst sX sL) g :=
  IsPullback.of_right (by simpa [pullback.lift_snd] using
    (IsPullback.of_hasPullback (g ≫ sX) sL).flip) (by simp [pullback.lift_fst])
    (IsPullback.of_hasPullback sX sL).flip

/-- `g × id_A` is the base change of `g × id_B` along `id_X × j`. -/
private theorem isPullback_map_map (g : X' ⟶ X) :
    IsPullback (pullback.map (g ≫ sX) (j ≫ sB) sX (j ≫ sB) g (𝟙 A) (𝟙 S) (by simp) (by simp))
      (pullback.map (g ≫ sX) (j ≫ sB) (g ≫ sX) sB (𝟙 X') j (𝟙 S) (by simp) (by simp))
      (pullback.map sX (j ≫ sB) sX sB (𝟙 X) j (𝟙 S) (by simp) (by simp))
      (pullback.map (g ≫ sX) sB sX sB g (𝟙 B) (𝟙 S) (by simp) (by simp)) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_map_id_snd sX sB j)
  · convert isPullback_map_id_snd (g ≫ sX) sB j using 1 <;> simp [pullback.lift_snd]
  · rw [pullback.map_comp, pullback.map_comp]; congr 1 <;> simp

end Products

/-- **Fibres of a base change.** Let `g : W ⟶ V` be the base change of `g₃ : U' ⟶ U` along
`p : V ⟶ U`, and `x : X ⟶ V` a morphism whose composite with `p` factors as `c ≫ ι` through
`ι : K ⟶ U`. Then `W ×_V X = (U' ×_U K) ×_K X`, and this is also the fibre product over any `Z`
receiving a monomorphism `m : K ⟶ Z`. -/
private theorem isIso_lift_map_of_isPullback {C : Type*} [Category C] [HasPullbacks C]
    {W V U' U K X Z : C} {p' : W ⟶ U'} {g : W ⟶ V} {g₃ : U' ⟶ U} {p : V ⟶ U}
    (hsq : IsPullback p' g g₃ p) (ι : K ⟶ U) (x : X ⟶ V) (c : X ⟶ K) (hc : x ≫ p = c ≫ ι)
    (m : K ⟶ Z) [Mono m] (sV : V ⟶ Z) (hs : x ≫ sV = c ≫ m) :
    IsIso (pullback.lift (pullback.map g x g₃ ι p' c p hsq.w.symm hc)
      (pullback.snd g x) (by simp [pullback.lift_snd_assoc, hs]) :
        pullback g x ⟶ pullback (pullback.snd g₃ ι ≫ m) (x ≫ sV)) := by
  have L1 := (IsPullback.of_hasPullback g x).paste_horiz hsq
  have L2 : IsPullback (pullback.map g x g₃ ι p' c p hsq.w.symm hc) (pullback.snd g x)
      (pullback.snd g₃ ι) c := by
    refine IsPullback.of_right ?_ (by simp [pullback.lift_snd]) (IsPullback.of_hasPullback g₃ ι)
    rw [pullback.lift_fst, ← hc]
    exact L1
  have L3 : IsPullback (pullback.map g x g₃ ι p' c p hsq.w.symm hc) (pullback.snd g x)
      (pullback.snd g₃ ι ≫ m) (x ≫ sV) := by
    rw [hs]
    exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ m L2.cone L2.isLimit)
  have : pullback.lift (pullback.map g x g₃ ι p' c p hsq.w.symm hc) (pullback.snd g x)
      (by simp [pullback.lift_snd_assoc, hs]) = L3.isoPullback.hom := by
    apply pullback.hom_ext <;> simp [pullback.lift_fst, pullback.lift_snd]
  rw [this]
  infer_instance

/-! ### Base change of birational morphisms -/

/-- H-projectivity is invariant under precomposition with an isomorphism. -/
private theorem isProjectiveMorphism_iso_comp {X X' S : Scheme.{u}} (e : X' ≅ X) {f : X ⟶ S}
    (hf : IsProjectiveMorphism f) : IsProjectiveMorphism (e.hom ≫ f) := by
  obtain ⟨n, i, hi, rfl⟩ := hf
  exact ⟨n, e.hom ≫ i, inferInstance, by simp⟩

/-- Biregularity is stable under base change. -/
private theorem isBiregular_preimage_of_isPullback {P' P Y₁ Y : Scheme.{u}} {m : P' ⟶ P}
    {p' : P' ⟶ Y₁} {p : P ⟶ Y} {g : Y₁ ⟶ Y} (H : IsPullback m p' p g) {V : Y.Opens}
    (hV : IsBiregular g V) : IsBiregular m (p ⁻¹ᵁ V) := by
  have hUY : m ⁻¹ᵁ (p ⁻¹ᵁ V) = m ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (g ⁻¹ᵁ V) := by
    refine (inf_eq_left.2 ?_).symm
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, H.w]
  have H' := Scheme.Hom.isPullback_resLE H (US := V) (UT := g ⁻¹ᵁ V) (UX := p ⁻¹ᵁ V)
    le_rfl le_rfl hUY
  have hg : IsIso (g.resLE V (g ⁻¹ᵁ V) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; exact hV
  have := MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme) H'.flip hg
  unfold IsBiregular
  rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  exact this

/-- The exceptional set of a base change lies over the exceptional set. -/
private theorem exceptionalSet_subset_preimage_of_isPullback {P' P Y₁ Y : Scheme.{u}}
    {m : P' ⟶ P} {p' : P' ⟶ Y₁} {p : P ⟶ Y} {g : Y₁ ⟶ Y} (H : IsPullback m p' p g) :
    (exceptionalSet m : Set P') ⊆ p' ⁻¹' (exceptionalSet g : Set Y₁) := by
  intro x hx hgx
  apply hx
  apply le_biregularLocus (isBiregular_preimage_of_isPullback H (isBiregular_biregularLocus g))
  have : p (m x) = g (p' x) := by
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
  change p (m x) ∈ biregularLocus g
  rw [this]
  exact hgx

/-- An open immersion `W ⟶ Y` through `g` base changes to an open immersion. -/
private theorem isOpenImmersion_ι_comp_of_isPullback {P' P Y₁ Y : Scheme.{u}}
    {m : P' ⟶ P} {p' : P' ⟶ Y₁} {p : P ⟶ Y} {g : Y₁ ⟶ Y} (H : IsPullback m p' p g)
    (W : Y₁.Opens) [IsOpenImmersion (W.ι ≫ g)] : IsOpenImmersion ((p' ⁻¹ᵁ W).ι ≫ m) := by
  have hUY : p' ⁻¹ᵁ W = m ⁻¹ᵁ ⊤ ⊓ p' ⁻¹ᵁ W := by rw [Scheme.Hom.preimage_top, top_inf_eq]
  have H' := Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W) (UX := ⊤) le_top le_top hUY
  have hg : IsOpenImmersion (g.resLE ⊤ W le_top) := by
    have e := Scheme.Hom.resLE_comp_ι g (U := ⊤) (V := W) le_top
    have : IsOpenImmersion (g.resLE ⊤ W le_top ≫ (⊤ : Y.Opens).ι) := by
      rw [e]; infer_instance
    exact IsOpenImmersion.of_comp _ (⊤ : Y.Opens).ι
  have := MorphismProperty.of_isPullback (P := @IsOpenImmersion) H'.flip hg
  rw [← Scheme.Hom.resLE_comp_ι m (U := ⊤) (V := p' ⁻¹ᵁ W) le_top]
  infer_instance

/-! ### Sections of elementary étale neighbourhoods -/

/-- The structure morphism of an elementary étale neighbourhood induces an isomorphism of
residue fields at its distinguished point. -/
private theorem isIso_toBase_residueFieldMap {S : Scheme.{0}} {s : S}
    (U : ElementaryEtaleNeighborhood S s) :
    IsIso (U.obj.toBase.residueFieldMap U.obj.point) := by
  have h0 : IsIso U.obj.residueFieldMap := U.property
  rw [EtaleNeighborhood.residueFieldMap_def] at h0
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance h0

/-- For elementary étale neighbourhoods `N` of `(Z, ξ)` and `U` of `(S, s)` and a morphism
`p : N ⟶ U` over `f : Z ⟶ S` with `p(n) = u` and `s = f ξ`, the section of `N` followed by `p`
is the section of `U` precomposed with `Spec κ(ξ) ⟶ Spec κ(s)`. -/
private theorem elementaryNeighborhoodSection_comp_eq {Z S : Scheme.{0}} {ξ : Z} {s : S}
    (N : ElementaryEtaleNeighborhood Z ξ) (U : ElementaryEtaleNeighborhood S s) (f : Z ⟶ S)
    (p : N.obj.scheme ⟶ U.obj.scheme) (hp : p ≫ U.obj.toBase = N.obj.toBase ≫ f)
    (hpn : p N.obj.point = U.obj.point) (hs : s = f ξ) :
    elementaryNeighborhoodSection N ≫ p = Spec.map (f.residueFieldMap ξ) ≫
      Spec.map (S.residueFieldCongr hs).hom ≫ elementaryNeighborhoodSection U := by
  have : IsIso N.obj.residueFieldMap := N.property
  have : IsIso U.obj.residueFieldMap := U.property
  have := isIso_toBase_residueFieldMap U
  have eL : elementaryNeighborhoodSection N ≫ p = Spec.map
      ((U.obj.scheme.residueFieldCongr hpn.symm).hom ≫ p.residueFieldMap N.obj.point ≫
        inv N.obj.residueFieldMap) ≫ U.obj.scheme.fromSpecResidueField U.obj.point := by
    simp only [elementaryNeighborhoodSection, Spec.map_comp, Category.assoc,
      Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have eR : Spec.map (f.residueFieldMap ξ) ≫ Spec.map (S.residueFieldCongr hs).hom ≫
      elementaryNeighborhoodSection U = Spec.map (inv U.obj.residueFieldMap ≫
        (S.residueFieldCongr hs).hom ≫ f.residueFieldMap ξ) ≫
        U.obj.scheme.fromSpecResidueField U.obj.point := by
    simp only [elementaryNeighborhoodSection, Spec.map_comp, Category.assoc]
  rw [eL, eR]
  apply SpecMap_comp_fromSpecResidueField_eq_of_comp U.obj.toBase
  rw [← Category.assoc, ← eL, ← Category.assoc, ← eR]
  simp only [Category.assoc, hp, elementaryNeighborhoodSection_comp_toBase_assoc,
    elementaryNeighborhoodSection_comp_toBase, Scheme.residueFieldCongr_fromSpecResidueField_assoc,
    Scheme.residueFieldCongr_fromSpecResidueField,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]

/-- **The product local étale datum and the product small model.** Let `(Y, π, y)` be a
threefold point setting, `T_y = {y} × ℙ¹`, `M_i` line bundles on `F_y` with pullbacks `L_i` to
`F_{η_{T_y}}`, and `(U, u)` an elementary étale neighbourhood of `(Y, y)` with `U` a normal
integral quasi-projective complex threefold, `u` closed, and line bundles `M̃_i` on
`Ũ = Ỹ ×_Y U` restricting to `M_i` along `MMP.Fourfold.localEtaleFibreMap`, where `Ũ` is smooth
and integral and `π_U` is projective, birational and an isomorphism over `q_U⁻¹(Y_reg)`. Let
`j : A ⟶ ℙ¹` be an open subscheme, `Y_e = U × A`, `q = q_U × j`, `η'` the generic point
of `{u} × A` and `L̃_i` the pullback of `M̃_i` to `Ỹ_e = Ũ × A`. Then `q` is étale,
`q(η') = η_{T_y}` with `κ(η_{T_y}) ≅ κ(η')`, `Y_e` is a normal quasi-projective variety, and
the `L̃_i` are line bundles restricting to the `L_i`: `(Y_e, q, η', L̃_i)` is a local étale datum
for the `L_i`.
Moreover, for every projective small birational `g₃ : U' ⟶ U` with `U'` `ℚ`-factorial,
`g = g₃ × id : U' × A ⟶ Y_e` is projective and small, `U' × A` is `ℚ`-factorial, and the scheme
fibre `g⁻¹(η')` maps isomorphically onto `g₃⁻¹(u) ×_ℂ Spec κ(η')`. -/
@[mmp "lem_mmp_indexb_product_local_datum"]
public theorem IsThreefoldPointSetting.exists_localEtaleDatum_prod
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {y : Y} (h : IsThreefoldPointSetting sY π y)
    (T : IrreducibleCloseds ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))))
    (hT : (T : Set ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)))) = pointSettingCurve sY y)
    {b : ℕ} (M : Fin b → (pointSettingFibre π y).Modules)
    (hMinv : ∀ i, SheafOfModules.IsInvertible (pointSettingFibre π y).presheaf
      (pointSettingFibre π y).ringCatSheaf.2 (M i))
    (U : ElementaryEtaleNeighborhood Y y)
    [IsIntegral U.obj.scheme] [IsLocallyNoetherian U.obj.scheme] [IsNormal U.obj.scheme]
    (hU : IsQuasiProjectiveVariety ℂ (U.obj.toBase ≫ sY))
    (hUn : IsNormalVariety ℂ (U.obj.toBase ≫ sY))
    (hUdim : topologicalKrullDim U.obj.scheme = 3)
    (hu : IsClosed ({U.obj.point} : Set U.obj.scheme))
    (Mt : Fin b → (pullback π U.obj.toBase).Modules)
    (hMt : ∀ i, SheafOfModules.IsInvertible (pullback π U.obj.toBase).presheaf
      (pullback π U.obj.toBase).ringCatSheaf.2 (Mt i))
    (hMtr : ∀ i, Nonempty
      ((Scheme.Modules.pullback (localEtaleFibreMap π U)).obj (Mt i) ≅ M i))
    (hUt : IsIntegral (pullback π U.obj.toBase))
    (hUts : Smooth (pullback.snd π U.obj.toBase ≫ U.obj.toBase ≫ sY))
    (hπUp : IsProjectiveMorphism (pullback.snd π U.obj.toBase))
    (hπUb : IsBirationalMorphism (pullback.snd π U.obj.toBase))
    (hπUi : IsBiregular (pullback.snd π U.obj.toBase) (U.obj.toBase ⁻¹ᵁ smoothLocus sY))
    {A : Scheme.{0}} (j : A ⟶ projectiveLine ℂ) [IsOpenImmersion j]
    (η' : ↥(pullback (U.obj.toBase ≫ sY) (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ))))
    (hη' : IsGenericPoint η'
      ((pullback.fst (U.obj.toBase ≫ sY) (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ))).base ⁻¹'
        {U.obj.point})) :
    ∃ (hq : Etale (pullback.map (U.obj.toBase ≫ sY) (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ)) sY
        (projectiveLine ℂ ↘ Spec (.of ℂ)) U.obj.toBase j (𝟙 _) (by simp) (by simp)))
      (hmap : (pullback.map (U.obj.toBase ≫ sY) (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ)) sY
        (projectiveLine ℂ ↘ Spec (.of ℂ)) U.obj.toBase j (𝟙 _) (by simp) (by simp)).base η' =
          localSettingGenericPoint T),
      let N₀ : EtaleNeighborhood _ (localSettingGenericPoint T) :=
        { scheme := pullback (U.obj.toBase ≫ sY) (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ))
          point := η'
          toBase := pullback.map (U.obj.toBase ≫ sY) (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ)) sY
            (projectiveLine ℂ ↘ Spec (.of ℂ)) U.obj.toBase j (𝟙 _) (by simp) (by simp)
          etale_toBase := hq
          map_point := hmap }
      ∃ hel : N₀.IsElementary,
        let N : ElementaryEtaleNeighborhood _ (localSettingGenericPoint T) := ⟨N₀, hel⟩
        let π' := pullback.map (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) sY
          (projectiveLine ℂ ↘ Spec (.of ℂ)) π (𝟙 _) (𝟙 _) (by simp) (by simp)
        let Lt : Fin b → (pullback π' N.obj.toBase).Modules := fun i ↦
          (Scheme.Modules.pullback (pullback.map π' N.obj.toBase π U.obj.toBase
            (pullback.fst (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)))
            (pullback.fst (U.obj.toBase ≫ sY) (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ)))
            (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))) (by simp [π'])
            (by simp [N, N₀]))).obj (Mt i)
        IsQuasiProjectiveVariety ℂ
            (N.obj.toBase ≫ pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) ∧
          IsNormal N.obj.scheme ∧
          (∀ i, Stacks.Ample.IsInvertibleModule _ (Lt i)) ∧
          (∀ i, Nonempty ((Scheme.Modules.pullback (localEtaleFibreMap π' N)).obj (Lt i) ≅
            (Scheme.Modules.pullback
              (pullback.map _ _ π (Y.fromSpecResidueField y)
                (pullback.fst (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)))
                (Spec.map ((pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))).residueFieldMap
                    (localSettingGenericPoint T)) ≫
                  Spec.map (Y.residueFieldCongr (show y =
                    (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))).base
                      (localSettingGenericPoint T) from
                    ((Set.ext_iff.1 hT _).1
                      (isGenericPoint_localSettingGenericPoint T).mem).symm)).hom)
                (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))) (by simp [π'])
                (by
                  rw [Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
                    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]) :
                pointSettingFibre π' (localSettingGenericPoint T) ⟶
                  pointSettingFibre π y)).obj (M i))) ∧
          ∀ {U' : Scheme.{0}} [IsIntegral U'] [IsLocallyNoetherian U'] [IsNormal U']
            (g₃ : U' ⟶ U.obj.scheme), IsProjectiveMorphism g₃ →
            IsSmallMorphism (g₃ ≫ U.obj.toBase ≫ sY) (U.obj.toBase ≫ sY) g₃ →
            IsQFactorial (g₃ ≫ U.obj.toBase ≫ sY) →
            let g := pullback.map (g₃ ≫ U.obj.toBase ≫ sY)
              (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ)) (U.obj.toBase ≫ sY)
              (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ)) g₃ (𝟙 _) (𝟙 _) (by simp) (by simp)
            let sYe := N.obj.toBase ≫ pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY
            IsProjectiveMorphism g ∧
              IsSmallMorphism (g ≫ sYe) sYe g ∧
              (∃ (_ : IsLocallyNoetherian (pullback (g₃ ≫ U.obj.toBase ≫ sY)
                  (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ))))
                (_ : IsNormal (pullback (g₃ ≫ U.obj.toBase ≫ sY)
                  (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ)))),
                IsQFactorial (g ≫ sYe)) ∧
              IsIso (pullback.lift
                (pullback.map g (N.obj.scheme.fromSpecResidueField η') g₃
                  (U.obj.scheme.fromSpecResidueField U.obj.point)
                  (pullback.fst _ _)
                  (Spec.map ((pullback.fst (U.obj.toBase ≫ sY)
                      (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ))).residueFieldMap η') ≫
                    Spec.map (U.obj.scheme.residueFieldCongr (show U.obj.point =
                      (pullback.fst (U.obj.toBase ≫ sY)
                        (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ))).base η' from
                      hη'.mem.symm)).hom)
                  (pullback.fst _ _) (by simp [g])
                  (by
                    rw [Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
                      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]))
                (pullback.snd g (N.obj.scheme.fromSpecResidueField η'))
                (by
                  simp only [sYe, N, N₀, pullback.lift_snd_assoc, pullback.lift_fst_assoc,
                    Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField_assoc,
                    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]) :
                pullback g (N.obj.scheme.fromSpecResidueField η') ⟶
                  pullback (pullback.snd g₃ (U.obj.scheme.fromSpecResidueField U.obj.point) ≫
                      U.obj.scheme.fromSpecResidueField U.obj.point ≫ U.obj.toBase ≫ sY)
                    (N.obj.scheme.fromSpecResidueField η' ≫ sYe)) := by
  haveI : MorphismProperty.IsStableUnderComposition @Etale := ⟨fun _ _ _ _ => inferInstance⟩
  have hUv : AlgebraicGeometry.IsVariety ℂ (U.obj.toBase ≫ sY) := hU.toIsVariety
  have := isIso_toBase_residueFieldMap U
  have hξ : IsGenericPoint (localSettingGenericPoint T)
      ((pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))).base ⁻¹'
        {U.obj.toBase U.obj.point}) := by
    have h0 := isGenericPoint_localSettingGenericPoint T
    rw [hT] at h0
    rw [U.obj.map_point]
    exact h0
  obtain ⟨hmap, hiso⟩ := map_genericPoint_and_isIso_residueFieldMap sY
    (projectiveLine ℂ ↘ Spec (.of ℂ)) U.obj.toBase j U.obj.point hη' hξ
  have hq : Etale (pullback.map (U.obj.toBase ≫ sY) (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ)) sY
      (projectiveLine ℂ ↘ Spec (.of ℂ)) U.obj.toBase j (𝟙 _) (by simp) (by simp)) :=
    MorphismProperty.pullbackMap (P := @Etale) (inferInstance : Etale U.obj.toBase)
      (inferInstance : Etale j) rfl rfl
  refine ⟨hq, hmap, ?_⟩
  intro N₀
  have hel : N₀.IsElementary := by
    change IsIso N₀.residueFieldMap
    rw [EtaleNeighborhood.residueFieldMap_def]
    infer_instance
  refine ⟨hel, ?_⟩
  intro N π' Lt
  -- the products with `ℙ¹`
  have hLP : (∃ e : projectiveLine ℂ ≅ projectiveLine ℂ,
      e.hom ≫ (projectiveLine ℂ ↘ Spec (.of ℂ)) = projectiveLine ℂ ↘ Spec (.of ℂ)) ∨
      ∃ e : projectiveLine ℂ ≅ 𝔸(PUnit.{1}; Spec (.of ℂ)),
        e.hom ≫ (𝔸(PUnit.{1}; Spec (.of ℂ)) ↘ Spec (.of ℂ)) =
          projectiveLine ℂ ↘ Spec (.of ℂ) :=
    Or.inl ⟨Iso.refl _, by simp⟩
  obtain ⟨⟨-, -, hUPn, -, -, hUPq⟩, -, -, hG⟩ :=
    product_line_basic (U.obj.toBase ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) hUn hLP
  let ι := pullback.map (U.obj.toBase ≫ sY) (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ))
    (U.obj.toBase ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) (𝟙 _) j (𝟙 _) (by simp) (by simp)
  have hι : IsOpenImmersion ι := MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstance : IsOpenImmersion (𝟙 U.obj.scheme)) ‹_› (by simp) rfl
  haveI hYe : Nonempty ↥(pullback (U.obj.toBase ≫ sY) (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ))) :=
    ⟨η'⟩
  have hsYe : N.obj.toBase ≫ pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY =
      ι ≫ pullback.fst (U.obj.toBase ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫
        U.obj.toBase ≫ sY := by
    simp [N, N₀, ι, pullback.lift_fst_assoc]
  have hYeq : IsQuasiProjectiveVariety ℂ
      (N.obj.toBase ≫ pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) := by
    rw [hsYe]; exact isQuasiProjectiveVariety_comp_of_isOpenImmersion ι (hUPq hU)
  have hYen : IsNormalVariety ℂ
      (N.obj.toBase ≫ pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) := by
    rw [hsYe]; exact isNormalVariety_comp_of_isOpenImmersion ι hUPn
  refine ⟨hYeq, hYen.2, fun i => ?_, fun i => ?_, ?_⟩
  · haveI := (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ (Mt i)).mpr (hMt i)
    exact MMP.Fourfold.isInvertibleModule_pullback _ _
  · obtain ⟨e⟩ := hMtr i
    have hyξ : y = (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))).base
        (localSettingGenericPoint T) :=
      ((Set.ext_iff.1 hT _).1 (isGenericPoint_localSettingGenericPoint T).mem).symm
    have key := elementaryNeighborhoodSection_comp_eq N U
      (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)))
      (pullback.fst (U.obj.toBase ≫ sY) (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ)))
      (by simp [N, N₀, pullback.lift_fst]) hη'.mem hyξ
    refine ⟨(Scheme.Modules.pullbackComp _ _).app (Mt i) ≪≫
      (Scheme.Modules.pullbackCongr ?_).app (Mt i) ≪≫
      ((Scheme.Modules.pullbackComp _ (localEtaleFibreMap π U)).app (Mt i)).symm ≪≫
      (Scheme.Modules.pullback _).mapIso e⟩
    apply pullback.hom_ext
    · simp [localEtaleFibreMap, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [Category.assoc, localEtaleFibreMap_snd, localEtaleFibreMap_snd_assoc,
        pullback.lift_snd, pullback.lift_snd_assoc]
      rw [key]
  · intro U' _ _ _ g₃ hg3p hg3s hg3q g sYe
    obtain ⟨hGp, hGb, -, hGsm⟩ :=
      hG g₃ hg3s.isNormalVariety_source hg3p hg3s.isBirationalMorphism
    have hGs := hGsm hg3s
    let ι' := pullback.map (g₃ ≫ U.obj.toBase ≫ sY) (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ))
      (g₃ ≫ U.obj.toBase ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) (𝟙 _) j (𝟙 _)
      (by simp) (by simp)
    have hι' : IsOpenImmersion ι' := MorphismProperty.pullbackMap (P := @IsOpenImmersion)
      (inferInstance : IsOpenImmersion (𝟙 U')) ‹_› (by simp) rfl
    have Sq := isPullback_map_map (U.obj.toBase ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) j g₃
    haveI : Nonempty A :=
      ⟨(pullback.snd (U.obj.toBase ≫ sY) (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ))).base η'⟩
    haveI : Nonempty ↥(pullback (g₃ ≫ U.obj.toBase ≫ sY)
        (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ))) := by
      obtain ⟨x⟩ := (inferInstance : Nonempty U')
      obtain ⟨a⟩ := (inferInstance : Nonempty A)
      obtain ⟨t, -, -⟩ := Scheme.Pullback.Triplet.exists_preimage
        (⟨x, a, _, rfl, Subsingleton.elim _ _⟩ : Scheme.Pullback.Triplet
          (g₃ ≫ U.obj.toBase ≫ sY) (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ)))
      exact ⟨t⟩
    have hs' : g ≫ sYe = ι' ≫ pullback.fst (g₃ ≫ U.obj.toBase ≫ sY)
        (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ g₃ ≫ U.obj.toBase ≫ sY := by
      simp [g, sYe, N, N₀, ι', pullback.lift_fst_assoc]
    have hsrc : IsNormalVariety ℂ (g ≫ sYe) := by
      rw [hs']; exact isNormalVariety_comp_of_isOpenImmersion ι' hGs.isNormalVariety_source
    have hproj : IsProjectiveMorphism g := by
      have h0 := isProjectiveMorphism_iso_comp Sq.flip.isoPullback (hGp.baseChange _)
      rwa [Sq.flip.isoPullback_hom_snd] at h0
    haveI : IsIntegral (pullback (g₃ ≫ U.obj.toBase ≫ sY)
        (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ))) := hsrc.1.toIsIntegral
    haveI : IsIntegral (pullback (g₃ ≫ U.obj.toBase ≫ sY)
        (projectiveLine ℂ ↘ Spec (.of ℂ))) := hGs.isNormalVariety_source.1.toIsIntegral
    haveI : IsIntegral (pullback (U.obj.toBase ≫ sY)
        (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ))) := hYen.1.toIsIntegral
    haveI : IsIntegral (pullback (U.obj.toBase ≫ sY)
        (projectiveLine ℂ ↘ Spec (.of ℂ))) := hUPn.1.toIsIntegral
    have hbir : IsBirationalMorphism g := by
      obtain ⟨W₀, hW₀, hW₀o⟩ := hGb.exists_isOpenImmersion
      have := isOpenImmersion_ι_comp_of_isPullback Sq W₀
      refine MMP.Spreading.isBirationalMorphism_of_isOpenImmersion_ι_comp' g (ι' ⁻¹ᵁ W₀) ?_
      obtain ⟨w, hw1, v, rfl⟩ := nonempty_preirreducible_inter W₀.isOpen
        ι'.isOpenEmbedding.isOpen_range hW₀ (Set.range_nonempty _)
      exact ⟨v, hw1⟩
    have hcodim : 2 ≤ closedsCodimension (exceptionalSet g) := by
      rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
      intro x hx
      have h1 := exceptionalSet_subset_preimage_of_isPullback Sq hx
      have h2 := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hGs.two_le_codimension h1
      rwa [coheight_eq_of_isOpenImmersion] at h2
    refine ⟨hproj, ⟨hsrc, hYen, rfl, isProper_of_isProjectiveMorphism _ hproj, hbir, hcodim⟩,
      ?_, ?_⟩
    · have hqP := (isQFactorial_pullback_line (g₃ ≫ U.obj.toBase ≫ sY)
        (projectiveLine ℂ ↘ Spec (.of ℂ)) hg3s.isNormalVariety_source hLP).2 hg3q
      haveI : IsLocallyNoetherian (pullback (g₃ ≫ U.obj.toBase ≫ sY)
          (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ))) :=
        @LocallyOfFiniteType.isLocallyNoetherian _ _ (g ≫ sYe) hsrc.1.toLocallyOfFiniteType _
      haveI : IsNormal (pullback (g₃ ≫ U.obj.toBase ≫ sY)
          (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ))) := hsrc.2
      haveI : IsLocallyNoetherian (pullback (g₃ ≫ U.obj.toBase ≫ sY)
          (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
        @LocallyOfFiniteType.isLocallyNoetherian _ _ _
          hGs.isNormalVariety_source.1.toLocallyOfFiniteType _
      haveI : IsNormal (pullback (g₃ ≫ U.obj.toBase ≫ sY)
          (projectiveLine ℂ ↘ Spec (.of ℂ))) := hGs.isNormalVariety_source.2
      refine ⟨inferInstance, inferInstance, ?_⟩
      rw [hs']
      exact isQFactorial_comp_of_isOpenImmersion ι' hqP
    · have hfst := (isPullback_map_fst (U.obj.toBase ≫ sY) g₃
        (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ))).flip
      haveI : LocallyOfFiniteType (U.obj.toBase ≫ sY) := hUv.toLocallyOfFiniteType
      haveI : IsIso (U.obj.scheme.fromSpecResidueField U.obj.point ≫ U.obj.toBase ≫ sY) := by
        rw [← SpecMap_residueFieldIsoBase_inv (U.obj.toBase ≫ sY) U.obj.point hu]
        infer_instance
      have hc : (pullback (U.obj.toBase ≫ sY)
          (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ))).fromSpecResidueField η' ≫
          pullback.fst (U.obj.toBase ≫ sY) (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ)) =
          (Spec.map ((pullback.fst (U.obj.toBase ≫ sY)
            (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ))).residueFieldMap η') ≫
            Spec.map (U.obj.scheme.residueFieldCongr (show U.obj.point =
              (pullback.fst (U.obj.toBase ≫ sY)
                (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ))).base η' from hη'.mem.symm)).hom) ≫
          U.obj.scheme.fromSpecResidueField U.obj.point := by
        rw [Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
          Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
      have e : (pullback.map (U.obj.toBase ≫ sY) (j ≫ projectiveLine ℂ ↘ Spec (.of ℂ)) sY
          (projectiveLine ℂ ↘ Spec (.of ℂ)) U.obj.toBase j (𝟙 _) (by simp) (by simp)) ≫
          pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) =
          pullback.fst _ _ ≫ U.obj.toBase := pullback.lift_fst _ _ _
      exact isIso_lift_map_of_isPullback hfst _ _ _ hc _ sYe (by
        simp only [sYe, N, N₀]
        rw [reassoc_of% e, reassoc_of% hc]
        simp only [Category.assoc])

end ProductLocalDatum

end MMP.Fourfold

end
