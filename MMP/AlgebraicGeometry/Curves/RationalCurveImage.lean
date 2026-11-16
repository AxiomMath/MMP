module
public import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineDegree
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowFourierMukai
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IrreducibleCriterion
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechDerivedSupportImmersion
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ProjectiveLineNormal
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineProjModel
public import MMP.AlgebraicGeometry.StalkValuationRing
public import MMP.AlgebraicGeometry.Curves.NormalCurveExtension

/-!
# Images of rational curves

Let `k` be an algebraically closed field, `X` a `k`-scheme and `Y` a proper variety over `k`.
If `C ⊆ X` is a rational curve and `f : X ⟶ Y` is a `k`-morphism which does not contract `C`
to a point, then the image `f(C)`, i.e. the scheme-theoretic image of `C ⟶ X ⟶ Y`, is a
rational curve on `Y`.

The proof goes through Lüroth's theorem. The image `D` is proper over `k`, being closed in `Y`,
and is an integral curve, being the scheme-theoretic image of the integral curve `C` and not a
point. Its function field `k(D)` embeds in `k(ℙ¹) = k(t)` through `ℙ¹_k ⟶ C ⟶ D` and is not
algebraic over `k`, so Lüroth's theorem gives `k(D) ≅ k(t)` over `k`. The resulting
`k`-morphism `Spec k(ℙ¹) ⟶ D` extends over `ℙ¹_k` by the valuative criterion of properness, the
local rings of the normal curve `ℙ¹_k` being valuation rings; the extension is proper and maps
the generic point to the generic point, hence is finite, surjective and birational.

## Main results

* `MMP.Mori.IsRationalCurve.ker_subschemeι_comp`: the nonconstant image of a rational curve
  is a rational curve.

## Implementation notes

The image of `C` is the closed subscheme `(C.subschemeι ≫ f).ker` of `Y`, the scheme-theoretic
image of the composite `C ⟶ X ⟶ Y`; since `C` is reduced, it is the reduced induced structure on
the closed set `f(C)`. Nonconstancy is the statement that `f(C)` is not a subsingleton.

The source identifies the normalization of `f(C)` with `ℙ¹_k`; here the finite birational
morphism `ℙ¹_k ⟶ f(C)` (that identification composed with the normalization map) is built
directly from the function field, by extending `Spec k(ℙ¹) ⟶ f(C)` over `ℙ¹_k`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

/-- The scheme-theoretic image of a closed subscheme of `X` in a proper `k`-scheme `Y` is
proper over `k`. -/
private theorem isProper_ker {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [AlgebraicGeometry.IsProperVariety k sY] {f : X ⟶ Y}
    (C : X.IdealSheafData) :
    IsProper ((C.subschemeι ≫ f).ker.subschemeι ≫ sY) := by
  haveI : IsProper sY := IsProperVariety.toIsProper
  infer_instance

/-- The scheme-theoretic image of a curve `C` under a morphism that does not contract it is a
curve. -/
private theorem isCurveIn_ker {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsProperVariety k sY] {f : X ⟶ Y} (hf : f ≫ sY = sX)
    {C : X.IdealSheafData} (hC : IsRationalCurve sX C)
    (hnc : ¬ (f.base '' (C.support : Set X)).Subsingleton) :
    IsCurveIn (C.subschemeι ≫ f).ker := by
  obtain ⟨⟨hCi, hCd⟩, hCp, -⟩ := hC
  haveI : IsProper sY := IsProperVariety.toIsProper
  have hrange : f.base '' (C.support : Set X) = Set.range (C.subschemeι ≫ f) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.IdealSheafData.range_subschemeι]
  have hcomp : (C.subschemeι ≫ f) ≫ sY = C.subschemeι ≫ sX := by
    rw [Category.assoc, hf]
  rw [hrange] at hnc
  haveI : IsIntegral C.subscheme := hCi
  generalize C.subschemeι ≫ f = g at hcomp hnc ⊢
  generalize C.subschemeι ≫ sX = s at hcomp hCp
  subst hcomp
  haveI hφ : IsProper g := IsProper.of_comp _ sY
  haveI : AlgebraicGeometry.IsVariety k (g ≫ sY) := IsVariety.mk
  haveI : AlgebraicGeometry.IsCurve k (g ≫ sY) := ⟨hCd⟩
  have hnc' : ¬ ∃ y : Y, Set.range g = {y} := by
    rintro ⟨y, hy⟩
    exact hnc (hy ▸ Set.subsingleton_singleton)
  exact ⟨isIntegral_image g, (isCurve_imageι_comp sY g hnc').topologicalKrullDim_eq_one⟩

/-! ### The projective line -/

/-- The projective line over a field is normal: it is isomorphic to `Proj k[T₀, T₁]`. -/
private theorem isNormal_projectiveLine (k : Type u) [Field k] : IsNormal (projectiveLine k) := by
  haveI := Stacks.ResolutionOfSurfaces.isNormal_projectiveLineProj k
  exact isNormal_of_isOpenImmersion (projectiveLineIsoProj k).hom

/-- The projective line over a field has Krull dimension at most one. -/
private theorem krullDim_projectiveLine_le (k : Type u) [Field k] :
    Order.krullDim (projectiveLine k) ≤ 1 := by
  rw [Stacks.AlgebraicGeometry.AmpleDimensionOne.krullDim_eq_topologicalKrullDim,
    (projectiveLine_isCurve k).topologicalKrullDim_eq_one]

/-- Over a field `k`, the point `Spec k(T) ⟶ T ⟶ Spec k` is `Spec` of the `k`-algebra structure
of the function field. -/
private theorem spec_algebraMap_functionField {k : Type u} [Field k] {T : Scheme.{u}}
    [IsIntegral T] (sT : T ⟶ Spec (.of k)) :
    letI := functionFieldAlgebra sT
    Spec.map (CommRingCat.ofHom (algebraMap k T.functionField)) =
      T.fromSpecStalk (genericPoint T) ≫ sT := by
  rw [MMP.fromSpecStalk_comp_eq]
  rfl

/-- A dominant `k`-morphism of integral `k`-schemes induces a `k`-algebra map of function
fields. -/
private theorem functionFieldMap_algebraMap {k : Type u} [Field k] {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] (sX : X ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    (ψ : X ⟶ T) [IsDominant ψ] (hψ : ψ ≫ sT = sX) (c : k) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra sT
    functionFieldMap ψ (algebraMap k T.functionField c) = algebraMap k X.functionField c := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra sT
  have hspec : Spec.map (CommRingCat.ofHom ((functionFieldMap ψ).comp
      (algebraMap k T.functionField))) =
      Spec.map (CommRingCat.ofHom (algebraMap k X.functionField)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, spec_algebraMap_functionField sT,
      spec_algebraMap_functionField sX, ← Category.assoc, functionFieldMap_fromSpecStalk,
      Category.assoc, hψ]
  exact congrArg (fun φ : k →+* _ => φ c)
    (congrArg CommRingCat.Hom.hom (Spec.map_injective hspec))

set_option backward.isDefEq.respectTransparency false in
/-- The identification of the function field of `ℙ¹_k` with `k(t)` is `k`-linear. -/
private theorem projectiveLineFunctionFieldEquiv_algebraMap (k : Type u) [Field k] (c : k) :
    letI := functionFieldAlgebra (projectiveLine k ↘ Spec (.of k))
    projectiveLineFunctionFieldEquiv k (algebraMap k _ c) = algebraMap k (RatFunc k) c := by
  letI := functionFieldAlgebra (projectiveLine k ↘ Spec (.of k))
  have he1 : ∀ x, Stacks.Chow.functionFieldEquiv_openImmersion (projectiveLineXChart k) x =
      functionFieldMap (projectiveLineXChart k) x := by
    intro x
    rw [Stacks.Chow.functionFieldEquiv_openImmersion_eq_dominantFunctionFieldMap]
    change ((_ : (projectiveLineXChart k) (genericPoint (Spec (.of (Polynomial k)))) =
      genericPoint (projectiveLine k)) ▸
        (projectiveLineXChart k).stalkMap (genericPoint (Spec (.of (Polynomial k))))).hom x = _
    rw [stalkMap_cast_target]
    rfl
  have hspec : Spec.map (CommRingCat.ofHom ((functionFieldMap (projectiveLineXChart k)).comp
      (algebraMap k (projectiveLine k).functionField))) =
      Spec.map (CommRingCat.ofHom ((algebraMap (Polynomial k)
        (Spec (.of (Polynomial k))).functionField).comp Polynomial.C)) := by
    rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp]
    have h2 : Spec.map (CommRingCat.ofHom
        (algebraMap (Polynomial k) (Spec (.of (Polynomial k))).functionField)) =
        (Spec (.of (Polynomial k))).fromSpecStalk (genericPoint _) := by
      rw [Spec.fromSpecStalk_eq']
      rfl
    rw [spec_algebraMap_functionField, h2, ← Category.assoc, functionFieldMap_fromSpecStalk,
      Category.assoc, projectiveLineXChart_comp_structureMorphism]
  have hc := congrArg (fun φ : k →+* _ => φ c)
    (congrArg CommRingCat.Hom.hom (Spec.map_injective hspec))
  simp only [CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at hc
  change affineLineFunctionFieldEquiv k
    (Stacks.Chow.functionFieldEquiv_openImmersion (projectiveLineXChart k) _) = _
  rw [he1, hc, AlgEquiv.commutes, RatFunc.algebraMap_C]
  rfl

/-- A surjective morphism, locally of finite type, of integral schemes inducing an isomorphism of
function fields is a birational morphism. -/
private theorem isBirationalMorphism_of_bijective_functionFieldMap {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] (μ : X ⟶ T) [Surjective μ] [LocallyOfFiniteType μ]
    (hbij : Function.Bijective (functionFieldMap μ)) : IsBirationalMorphism μ := by
  let e := T.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant μ).symm)
  haveI : IsIso (e.hom ≫ μ.stalkMap (genericPoint X)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  haveI : IsIso (μ.stalkMap (genericPoint X)) := IsIso.of_isIso_comp_left e.hom _
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents T) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational μ
      (isBirational_of_isIso_stalkMap_genericPoint μ) (Or.inl ⟨inferInstance, inferInstance⟩)
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE μ U V hU.nonempty hV.nonempty hUV hiso

/-- A `k`-algebra map out of the function field of an integral curve over `k` has nontrivial
range: the function field is not algebraic over `k`. -/
private theorem fieldRange_ne_bot_of_topologicalKrullDim_eq_one {k : Type u} [Field k]
    {T : Scheme.{u}} [IsIntegral T] (sT : T ⟶ Spec (.of k)) [LocallyOfFiniteType sT]
    (hT : topologicalKrullDim T = 1) {K : Type*} [Field K] [Algebra k K]
    (β : letI := functionFieldAlgebra sT; T.functionField →ₐ[k] K) :
    letI := functionFieldAlgebra sT; β.fieldRange ≠ ⊥ := by
  letI := functionFieldAlgebra sT
  intro hE
  have halg : Algebra.IsAlgebraic k T.functionField := by
    refine ⟨fun x => ?_⟩
    have hx : β x ∈ (⊥ : IntermediateField k K) := hE ▸ ⟨x, rfl⟩
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hx
    rw [← β.commutes c] at hc
    rw [← β.toRingHom.injective hc]
    exact isAlgebraic_algebraMap c
  have htr := toENat_trdeg_functionField (sX := sT)
  rw [trdeg_eq_zero_iff.mpr halg, hT] at htr
  simp at htr

/-- Every point of `Spec` of the stalk at the generic point of an integral scheme maps to the
generic point. -/
private theorem fromSpecStalk_genericPoint_apply {T : Scheme.{u}} [IsIntegral T]
    (p : Spec (T.presheaf.stalk (genericPoint T))) :
    T.fromSpecStalk (genericPoint T) p = genericPoint T := by
  rw [show p = IsLocalRing.closedPoint _ from
    Subsingleton.elim (α := PrimeSpectrum T.functionField) _ _]
  exact Scheme.fromSpecStalk_closedPoint

/-- An integral scheme of topological Krull dimension one is nontrivial. -/
private theorem nontrivial_of_topologicalKrullDim_eq_one {T : Scheme.{u}} [IsIntegral T]
    (hT : topologicalKrullDim T = 1) : Nontrivial T := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  have h1 := Order.krullDim_nonpos_of_subsingleton (α := T)
  rw [Stacks.AlgebraicGeometry.AmpleDimensionOne.krullDim_eq_topologicalKrullDim, hT] at h1
  exact absurd h1 (by decide)

set_option backward.isDefEq.respectTransparency false in
/-- Let `T` be an integral proper curve over `k`. A `k`-isomorphism of function fields
`k(T) ≅ k(ℙ¹)` is induced by a finite birational `k`-morphism `ℙ¹_k ⟶ T`: the `k`-morphism
`Spec k(ℙ¹) ⟶ T` it defines extends over the normal curve `ℙ¹_k`. -/
private theorem exists_finite_birational_of_ringEquiv {k : Type u} [Field k] {T : Scheme.{u}}
    (sT : T ⟶ Spec (.of k)) [IsIntegral T] [IsProper sT] (hT : topologicalKrullDim T = 1)
    (α : T.functionField ≃+* (projectiveLine k).functionField)
    (hα : letI := functionFieldAlgebra sT
      letI := functionFieldAlgebra (projectiveLine k ↘ Spec (.of k))
      ∀ c : k, α (algebraMap k T.functionField c) =
        algebraMap k (projectiveLine k).functionField c) :
    ∃ μ : projectiveLine k ⟶ T, μ ≫ sT = projectiveLine k ↘ Spec (.of k) ∧
      IsFinite μ ∧ IsBirationalMorphism μ := by
  letI := functionFieldAlgebra sT
  letI : T.Over (Spec (.of k)) := ⟨sT⟩
  haveI : T.IsSeparated := ⟨by
    rw [Limits.terminal.hom_ext (Limits.terminal.from T) (sT ≫ Limits.terminal.from _)]
    infer_instance⟩
  haveI := isNormal_projectiveLine k
  set ψ₀ : Spec (projectiveLine k).functionField ⟶ T :=
    Spec.map (CommRingCat.ofHom (α : T.functionField →+* (projectiveLine k).functionField)) ≫
      T.fromSpecStalk (genericPoint T) with hψ₀
  have hψ₀S : ψ₀ ≫ sT =
      (projectiveLine k).fromSpecStalk (genericPoint _) ≫ (projectiveLine k ↘ Spec (.of k)) := by
    rw [hψ₀, Category.assoc, ← spec_algebraMap_functionField sT,
      ← spec_algebraMap_functionField (projectiveLine k ↘ Spec (.of k)), ← Spec.map_comp]
    congr 1
    ext c
    exact hα c
  haveI : ψ₀.IsOver (Spec (.of k)) := ⟨hψ₀S⟩
  haveI : IsProper (T ↘ Spec (.of k)) := ‹IsProper sT›
  obtain ⟨μ, hμover, hμ⟩ := MMP.NormalCompleteCurve.exists_hom_of_fromFunctionField
    (S := Spec (.of k)) (fun x => MMP.valuationRing_stalk
      (MMP.coheight_le_one (krullDim_projectiveLine_le k) x)) ψ₀
  have hμS : μ ≫ sT = projectiveLine k ↘ Spec (.of k) := hμover.comp_over
  have hgen : μ (genericPoint (projectiveLine k)) = genericPoint T := by
    have h := congrArg (fun φ : Spec _ ⟶ T => φ (IsLocalRing.closedPoint _)) hμ
    simp only at h
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint, hψ₀, Scheme.Hom.comp_apply] at h
    exact h.trans (fromSpecStalk_genericPoint_apply _)
  haveI : IsDominant μ := ((tfae_isDominant_of_isIntegral μ).out 1 2).mpr hgen
  have hffm : functionFieldMap μ = (α : T.functionField →+* _) := by
    have h := functionFieldMap_fromSpecStalk μ
    rw [hμ, hψ₀] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp h))
  haveI : IsProper (μ ≫ sT) := by
    rw [hμS]
    infer_instance
  haveI : IsProper μ := IsProper.of_comp μ sT
  haveI := nontrivial_of_topologicalKrullDim_eq_one hT
  haveI : IsNoetherian (projectiveLine k) := {}
  obtain ⟨hfin, hsurj⟩ := MMP.NormalCompleteCurve.isFinite_and_surjective
    (krullDim_projectiveLine_le k) μ hgen
  haveI : Surjective μ := ⟨hsurj⟩
  exact ⟨μ, hμS, hfin, isBirationalMorphism_of_bijective_functionFieldMap μ (hffm ▸ α.bijective)⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Lüroth and the projective line.** Let `T` be an integral proper curve over `k` dominated by
`ℙ¹_k` over `k`. Then `ℙ¹_k` maps onto `T` by a finite birational morphism over `k`: the function
field of `T` is a nonconstant subfield of `k(t)`, hence `k(s)` by Lüroth's theorem, and the
resulting `k`-morphism `Spec k(ℙ¹) ⟶ T` extends over the normal curve `ℙ¹_k`. -/
private theorem exists_finite_birational_of_isDominant {k : Type u} [Field k] {T : Scheme.{u}}
    (sT : T ⟶ Spec (.of k)) [IsIntegral T] [IsProper sT] (hT : topologicalKrullDim T = 1)
    (ψ : projectiveLine k ⟶ T) [IsDominant ψ] (hψ : ψ ≫ sT = projectiveLine k ↘ Spec (.of k)) :
    ∃ μ : projectiveLine k ⟶ T, μ ≫ sT = projectiveLine k ↘ Spec (.of k) ∧
      IsFinite μ ∧ IsBirationalMorphism μ := by
  letI := functionFieldAlgebra sT
  set eP := projectiveLineFunctionFieldEquiv k
  let β : T.functionField →ₐ[k] RatFunc k :=
    { (eP : (projectiveLine k).functionField →+* RatFunc k).comp (functionFieldMap ψ) with
      commutes' := fun c => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom]
        letI := functionFieldAlgebra (projectiveLine k ↘ Spec (.of k))
        rw [functionFieldMap_algebraMap _ sT ψ hψ]
        exact projectiveLineFunctionFieldEquiv_algebraMap k c }
  have hE : β.fieldRange ≠ ⊥ := fieldRange_ne_bot_of_topologicalKrullDim_eq_one sT hT β
  set g := RatFunc.Luroth.generator β.fieldRange
  have hg : Transcendental k g := RatFunc.Luroth.transcendental_generator hE
  have hrange : β.range = (IntermediateField.adjoin k {g}).toSubalgebra := by
    rw [← AlgHom.fieldRange_toSubalgebra, ← RatFunc.Luroth.eq_adjoin_generator]
  let γ : T.functionField ≃ₐ[k] RatFunc k :=
    ((AlgEquiv.ofInjectiveField β).trans (Subalgebra.equivOfEq _ _ hrange)).trans
      (RatFunc.algEquivOfTranscendental g hg).symm
  let α : T.functionField ≃+* (projectiveLine k).functionField :=
    γ.toRingEquiv.trans eP.symm
  have hα : letI := functionFieldAlgebra (projectiveLine k ↘ Spec (.of k))
      ∀ c : k, α (algebraMap k T.functionField c) =
      algebraMap k (projectiveLine k).functionField c := by
    letI := functionFieldAlgebra (projectiveLine k ↘ Spec (.of k))
    intro c
    change eP.symm (γ (algebraMap k _ c)) = _
    rw [γ.commutes, RingEquiv.symm_apply_eq, projectiveLineFunctionFieldEquiv_algebraMap]
  exact exists_finite_birational_of_ringEquiv sT hT α hα

/-- The image of a rational curve is dominated by `ℙ¹_k` through a finite birational
morphism over `k` (Lüroth's theorem and normalization). -/
private theorem exists_finite_birational {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsProperVariety k sY] {f : X ⟶ Y} (hf : f ≫ sY = sX)
    {C : X.IdealSheafData} (hC : IsRationalCurve sX C)
    (hnc : ¬ (f.base '' (C.support : Set X)).Subsingleton) :
    ∃ ν : projectiveLine k ⟶ (C.subschemeι ≫ f).ker.subscheme,
      ν ≫ (C.subschemeι ≫ f).ker.subschemeι ≫ sY = projectiveLine k ↘ Spec (.of k) ∧
        IsFinite ν ∧ IsBirationalMorphism ν := by
  obtain ⟨hDi, hDd⟩ := isCurveIn_ker hf hC hnc
  obtain ⟨-, hCp, ν, hν, -, hνb⟩ := hC
  haveI : IsProper sY := IsProperVariety.toIsProper
  have hTp := isProper_ker (sY := sY) (f := f) C
  have hφs : (C.subschemeι ≫ f) ≫ sY = C.subschemeι ≫ sX := by rw [Category.assoc, hf]
  haveI : IsDominant ν := hνb.isDominant
  generalize C.subschemeι ≫ f = φ at hDi hDd hTp hφs ⊢
  rw [← hφs] at hν hCp
  haveI := hDi
  haveI hφ : IsProper φ := IsProper.of_comp _ sY
  refine exists_finite_birational_of_isDominant _ hDd (ν ≫ φ.toImage) ?_
  change ν ≫ φ.toImage ≫ φ.imageι ≫ sY = _
  rw [Scheme.Hom.toImage_imageι_assoc, hν]

/-- The nonconstant image of a rational curve in a proper variety over an algebraically closed
field is a rational curve: if `C ⊆ X` is a rational curve and the `k`-morphism `f : X ⟶ Y` into a
proper variety `Y` does not map `C` to a point, then the scheme-theoretic image of `C` in `Y` is a
rational curve on `Y`. -/
@[mmp "lem_mmp_projective_rational_curve_image"]
public theorem IsRationalCurve.ker_subschemeι_comp {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsProperVariety k sY] {f : X ⟶ Y} (hf : f ≫ sY = sX)
    {C : X.IdealSheafData} (hC : IsRationalCurve sX C)
    (hnc : ¬ (f.base '' (C.support : Set X)).Subsingleton) :
    IsRationalCurve sY (C.subschemeι ≫ f).ker :=
  ⟨isCurveIn_ker hf hC hnc, isProper_ker C, exists_finite_birational hf hC hnc⟩

end MMP.Mori

end
