module

import MMP.AlgebraicGeometry.SpecOverSpecSelf
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.VerticalKernelBlowup
public import MMP.AlgebraicGeometry.Analytic.FiniteCochainsBetti
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.CurveRankShrinking
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.GenericDefect.DefectMapInjective
public import MMP.AlgebraicGeometry.MMP.Fourfold.AlgebraicKernelRestriction
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ContractedEdgeInjectivity
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.GenericDefect.FibreCycle
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.GenericDefect.FibreHomologyDetection
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.Topology.Sheaves.LocalSystem.ParallelTransport
import MMP.AlgebraicGeometry.Analytic.SchemeManifold
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LocallyContractible
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartConnected
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartDense
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPointsUnderlyingSpace
import MMP.AlgebraicGeometry.Analytic.ComplexScheme.OfProjective
import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceZero
import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Projective
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
import MMP.AlgebraicGeometry.Resolution.SNCWithDivisorSmooth
import MMP.AlgebraicGeometry.Analytic.CartierDivisorDictionary
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.PrimeDivisorCurveFamily
import MMP.AlgebraicGeometry.Morphisms.GenericSmoothness
import MMP.AlgebraicTopology.BorelMoore.FiniteChains
import MMP.AlgebraicTopology.PoincareDuality.PuncturedLow
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicTopology.PoincareDuality.AlexanderSquare
import MMP.AlgebraicTopology.CapProduct.Restriction
import MMP.AlgebraicTopology.PoincareDuality.DualClassSupport
import MMP.AlgebraicTopology.SingularCohomology.PairSequence.Supports
import MMP.AlgebraicTopology.BorelMoore.RestrictionPushforward
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ExceptionalFibreGeneric
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.VeryGeneralFibreLineBundles
public import MMP.AlgebraicGeometry.Morphisms.HProjective
public import MMP.Topology.KrullDimensionProperClosed
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import MMP.AlgebraicGeometry.IdealSheafSubscheme
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# Finite-dimensionality of the vertical defect spaces

Let `r : Z ⟶ Y` be a projective birational morphism from a smooth projective complex fourfold `Z`
to a normal projective `ℚ`-factorial variety `Y`, whose full exceptional locus is a reduced snc
divisor `F = ∑ Fᵢ`. The vertical kernel `K_v(r)` (`MMP.Fourfold.verticalKernel`), the vertical
boundary space `B_v(r)` (`MMP.Fourfold.verticalSurfaceClasses`), the vertical defect
`D_v(r) = K_v(r)/B_v(r)` (`MMP.Fourfold.VerticalDefect`) and its subspaces `D_{v,Q}(r)`
(`MMP.Fourfold.verticalDefectOver`) all live in `⨁ᵢ H_4(Fᵢ, ℚ)` or its quotients, which is
finite-dimensional since the `Fᵢ` are projective; moreover `B_v(r) ⊆ K_v(r)`.

When `r` is a curve-and-point exceptional model (`MMP.Fourfold.IsCurvePointExceptionalModel`),
every rational surface cycle on a component `Fᵢ` is killed by `r`, and every double surface
maps into dimension at most one, so `K_v(r) = K(r)` and `B_v(r) = B(r)`: the vertical defect is
the algebraic defect `K(r)/B(r)`. The injectivity of the generic defect map then bounds the
dimension of `D_{v,Q}(r)`, for a closed `Q ⊆ Y`, by `∑ b_T` over the curves `T ⊆ Sing Y ∩ Q`.

## Main results

* `MMP.Fourfold.finiteDimensional_componentHomology_and_verticalDefect`.

## Implementation notes

* Finite-dimensionality is stated for `⨁ᵢ H_4(Fᵢ, ℚ)` (`MMP.Fourfold.ComponentHomology`); the
  finite-dimensionality of `Cᵢ^v`, `K_v(r)`, `B_v(r)`, `D_v(r)` and `D_{v,Q}(r)`, subspaces and
  quotients of it, follows by the instances `FiniteDimensional.finiteDimensional_submodule` and
  `FiniteDimensional.finiteDimensional_quotient`.
* The identification `D_v(r) = K(r)/B(r)` is the equality of the subspaces `K_v(r) = K(r)` and
  `B_v(r) = B(r)` of `⨁ᵢ H_4(Fᵢ, ℚ)`, which makes `MMP.Fourfold.VerticalDefect` and
  `MMP.Fourfold.AlgebraicDefect` the same quotient.
* The curves `T ⊆ Sing Y` are the irreducible closed subsets of dimension one, and
  `b_T = dim_ℚ H²_c(T°, 𝒱_T)` (`MMP.Fourfold.curveLocalSystemRank`) is computed on a
  local-system open `T° ⊆ T` (`MMP.Fourfold.IsLocalSystemOpen`); the bound is asserted for every
  choice of these opens, `b_T` being independent of it.

## References

* [Kollár–Mori, *Birational geometry of algebraic varieties*]
-/

@[expose] public section

section

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP
open MMP.Mori MMP.Fourfold
open scoped MMP.SubschemeOver TensorProduct

namespace Proof_lem_mmp_conductor_vertical_defect_spaces

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
  [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- The Krull dimension of a subspace is monotone in the subset. -/
private theorem topologicalKrullDim_le_of_subset {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : A ⊆ B) : topologicalKrullDim A ≤ topologicalKrullDim B :=
  (Topology.IsInducing.of_comp (continuous_inclusion h) continuous_subtype_val
    Topology.IsInducing.subtypeVal).topologicalKrullDim_le

section BorelMoore

open CategoryTheory.Limits AlgebraicTopology MMP.LocallyFiniteChain

variable (W : TopCat.{0})

/-- A finitely supported family of simplices is locally finite. -/
private lemma isLocallyFiniteSet_of_finite {S : Type*} {car : S → Set W} {s : Set S}
    (hs : s.Finite) : IsLocallyFiniteSet car s :=
  fun _ ↦ ⟨Set.univ, Filter.univ_mem, hs.subset fun _ hτ ↦ hτ.1⟩

/-- Finite singular chains, as locally finite singular chains. -/
private noncomputable def finsuppToLF (n : SimplexCategoryᵒᵖ) :
    ((TopCat.toSSet.obj W).obj n →₀ ℚ) →ₗ[ℚ]
      lfChains ℚ (ModuleCat.of ℚ ℚ) (singularSimplexImage W (n := n)) :=
  (Finsupp.lcoeFun).codRestrict _ fun f ↦
    isLocallyFiniteSet_of_finite W f.hasFiniteSupport

/-- On a compact space every locally finite chain is finite. -/
private lemma bijective_finsuppToLF [CompactSpace W] (n : SimplexCategoryᵒᵖ) :
    Function.Bijective (finsuppToLF W n) := by
  refine ⟨fun f g h ↦ Finsupp.ext fun σ ↦ congr_fun (congrArg Subtype.val h) σ, fun c ↦ ?_⟩
  have hfin : (Function.support c.1).Finite := by
    refine (c.2.finite_inter_compact isCompact_univ).subset fun σ hσ ↦ ⟨hσ, ?_⟩
    obtain ⟨y, hy⟩ := nonempty_singularSimplexImage σ
    exact ⟨y, hy, trivial⟩
  exact ⟨Finsupp.ofSupportFinite c.1 hfin, Subtype.ext rfl⟩

/-- The coproduct of copies of `ℚ` indexed by `S` is `S →₀ ℚ`. -/
private noncomputable def sigmaIsoFinsupp (S : Type) :
    (∐ fun _ : S ↦ ModuleCat.of ℚ ℚ) ≅ ModuleCat.of ℚ (S →₀ ℚ) :=
  (Limits.coproductIsCoproduct _).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit ℚ ℚ S)

@[reassoc]
private lemma ι_sigmaIsoFinsupp_hom {S : Type} (σ : S) :
    Limits.Sigma.ι _ σ ≫ (sigmaIsoFinsupp S).hom = ModuleCat.ofHom (Finsupp.lsingle σ) :=
  Limits.IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk σ)

private lemma sigmaIsoFinsupp_hom_ι_apply {S : Type} (σ : S) (q : ℚ) :
    (sigmaIsoFinsupp S).hom.hom ((Limits.Sigma.ι (fun _ : S ↦ ModuleCat.of ℚ ℚ) σ).hom q) =
      Finsupp.single σ q := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ι_sigmaIsoFinsupp_hom]
  rfl

/-- The comparison from singular chains (as a coproduct) to locally finite chains. -/
private noncomputable def toLF :
    ((SimplicialObject.whiskering _ _).obj (sigmaConst.obj (ModuleCat.of ℚ ℚ))).obj
      (TopCat.toSSet.obj W) ⟶ locallyFiniteSingularChains ℚ (ModuleCat.of ℚ ℚ) W where
  app n := (sigmaIsoFinsupp _).hom ≫ ModuleCat.ofHom (finsuppToLF W n)
  naturality n m θ := by
    dsimp [sigmaConst]
    refine Limits.Sigma.hom_ext _ _ fun σ ↦ ?_
    simp only [Limits.Sigma.ι_comp_map'_assoc, Category.id_comp]
    refine ModuleCat.hom_ext (LinearMap.ext_ring (Subtype.ext (funext fun τ ↦ ?_)))
    change ((sigmaIsoFinsupp _).hom.hom ((Limits.Sigma.ι (fun _ ↦ ModuleCat.of ℚ ℚ)
        ((TopCat.toSSet.obj W).map θ σ)).hom 1) : (TopCat.toSSet.obj W).obj m →₀ ℚ) τ =
      pushforwardFun ((TopCat.toSSet.obj W).map θ)
        ⇑((sigmaIsoFinsupp _).hom.hom ((Limits.Sigma.ι (fun _ ↦ ModuleCat.of ℚ ℚ) σ).hom 1)) τ
    rw [sigmaIsoFinsupp_hom_ι_apply, sigmaIsoFinsupp_hom_ι_apply]
    classical
    rw [pushforwardFun_apply_eq_sum _ _ τ {σ} fun σ' h _ ↦ by
      by_contra h'
      exact h (Finsupp.single_eq_of_ne (by simpa using h'))]
    simp [Finsupp.single_apply]

private lemma isIso_toLF_app [CompactSpace W] (n : SimplexCategoryᵒᵖ) :
    IsIso ((toLF W).app n) := by
  change IsIso ((sigmaIsoFinsupp _ ≪≫
    (LinearEquiv.ofBijective _ (bijective_finsuppToLF W n)).toModuleIso).hom)
  infer_instance

/-- On a compact space, Borel–Moore homology is singular homology. -/
private noncomputable def borelMooreHomologyIso [CompactSpace W] (k : ℕ) :
    borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) W k ≅
      (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).obj W).homology k :=
  have : IsIso (toLF W) := by
    have := isIso_toLF_app W
    exact NatIso.isIso_of_isIso_app _
  borelMooreHomologyIsoOfNat ℚ _ W k ≪≫ (HomologicalComplex.homologyFunctor _ _ k).mapIso
    ((AlgebraicTopology.alternatingFaceMapComplex _).mapIso (asIso (toLF W))).symm

end BorelMoore

/-- The rational homology of a projective complex scheme is finite-dimensional. -/
private theorem finiteDimensional_rationalHomology {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] (hX : IsProjective (X ↘ Spec (.of ℂ))) (k : ℕ) :
    FiniteDimensional ℚ (RationalHomology X k) := by
  have hP := isProjectiveMorphism_of_isProjective_of_isAffine _ hX
  have : IsProper (X ↘ Spec (.of ℂ)) := isProper_of_isProjectiveMorphism _ hP
  -- `X(ℂ)` is compact
  letI : (Spec (.of ℂ)).Over (Spec (.of ℂ)) := ⟨𝟙 _⟩
  have : (X ↘ Spec (.of ℂ)).IsOver (Spec (.of ℂ)) := ⟨Category.comp_id _⟩
  have : LocallyOfFiniteType (Spec (.of ℂ) ↘ Spec (.of ℂ)) :=
    show LocallyOfFiniteType (𝟙 _) from inferInstance
  have hp := UnderlyingSpace.isProperMap_map (K := ℂ) (X ↘ Spec (.of ℂ))
  have : Subsingleton (UnderlyingSpace ℂ (Spec (.of ℂ))) :=
    ⟨fun p q ↦ UnderlyingSpace.ext
      (((Category.comp_id _).symm.trans p.toHom_comp_over).trans
        ((Category.comp_id _).symm.trans q.toHom_comp_over).symm)⟩
  have : CompactSpace (UnderlyingSpace ℂ X) :=
    ⟨by simpa using hp.isCompact_preimage Set.subsingleton_univ.isCompact⟩
  have hfin := (MMP.Analytic.finiteDimensional_singularHomology_of_isProjective X hX).1 k
  let e : TopCat.of (MMP.Analytic.ComplexPoints (X ↘ Spec (.of ℂ))) ≅
      TopCat.of (UnderlyingSpace ℂ X) :=
    TopCat.isoOfHomeo MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace
  let e' := ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) k).mapIso
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).mapIso e))
  have : FiniteDimensional ℚ ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ)
      (ComplexShape.down ℕ) k).obj
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
        (ModuleCat.of ℚ ℚ)).obj (TopCat.of (MMP.Analytic.ComplexPoints (X ↘ Spec (.of ℂ)))))) :=
    hfin
  exact .equiv
    ((borelMooreHomologyIso (TopCat.of (UnderlyingSpace ℂ X)) k).symm.toLinearEquiv.symm.trans
      e'.symm.toLinearEquiv).symm

/-- `⨁ᵢ H_4(Fᵢ, ℚ)` is finite-dimensional when the `Fᵢ` are projective. -/
private theorem finiteDimensional_componentHomology
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F : Divisor Z}
    (hcomp : r ≫ sY = Z ↘ Spec (.of ℂ))
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hres : MMP.Intersection.IsResolution sY r) :
    FiniteDimensional ℚ (ComponentHomology F) := by
  have hZ : IsProjectiveMorphism (Z ↘ Spec (.of ℂ)) := by
    rw [← hcomp]
    exact hres.2.2.2.1.comp hY.isProjective
  have hE : ∀ E : F.support, FiniteDimensional ℚ (RationalHomology E.1.idealSheaf.subscheme 4) :=
    fun E => finiteDimensional_rationalHomology (by
      change IsProjective (E.1.idealSheaf.subschemeι ≫ (Z ↘ Spec (.of ℂ)))
      exact ((MMP.isProjectiveMorphism_of_isClosedImmersion _).comp hZ).isProjective) 4
  infer_instance

/-- The vertical boundary classes are vertical kernel classes: each `Zᵢ(a)` of a vertical system
pushes forward to zero in `Y`, and the ambient classes of an oriented system cancel. -/
private theorem verticalSurfaceClasses_le_verticalKernel [Y.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y}
    [r.IsOver (Spec (.of ℂ))] [IsProper r] {F : Divisor Z}
    (hres : MMP.Intersection.IsResolution sY r)
    (hdim : topologicalKrullDim Z = 4) :
    verticalSurfaceClasses r F ≤ verticalKernel r F := by
  have : IsIntegral Z :=
    (hres.2.1 : AlgebraicGeometry.IsVariety ℂ (r ≫ sY)).toIsIntegral
  rintro x hx
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hx
  refine (mem_exceptionalKernel F).2
    ⟨fun E => ⟨Chow.divisorCycle _ (surfaceCoefficientDivisor a E.1),
      ConductorBlowup.rationalProperPushforward_divisorCycle_eq_zero_of_mem_vertical r F ha E.1,
      rfl⟩, ?_⟩
  exact ConductorBlowup.sum_componentHomologyMap_divisorClass_eq_zero_of_topologicalKrullDim_eq_four
    hdim F a ha.1

/-- On a component `E` of `F` mapping to a curve or a point, every surface cycle pushes forward
to zero in `Y`: the image of a surface has dimension at most one. -/
private theorem componentPushforward_eq_zero [Y.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y}
    [r.IsOver (Spec (.of ℂ))] [IsProper r] {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D) (E : F.support)
    (L : ComponentCycles Z E.1 2) :
    componentPushforward r E.1 2 L = 0 := by
  classical
  obtain ⟨s, -, hs⟩ := ConductorBlowup.exists_eq_sum_rationalCoeff_smul L
  rw [hs, map_sum]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [map_smul]
  refine smul_eq_zero_of_right _ ?_
  unfold Chow.pointCycleOrZero
  split_ifs with hx
  · change Chow.rationalProperPushforward _ _ _ _ (E.1.idealSheaf.subschemeι ≫ r) (comp_over _ _)
      (Chow.rationalPointCycle _ _ _ x hx) = 0
    refine ConductorBlowup.rationalProperPushforward_rationalPointCycle_eq_zero _ x hx fun hy => ?_
    have hy2 := (ConductorBlowup.relativeDimension_eq_iff_topologicalKrullDim_closure _ _ 2).1 hy
    have hsub : closure ({(E.1.idealSheaf.subschemeι ≫ r).base x} : Set Y) ⊆
        r.base '' E.1.support := by
      refine closure_minimal ?_ (r.isClosedMap _ E.1.idealSheaf.support.isClosed)
      rintro _ rfl
      exact ⟨E.1.idealSheaf.subschemeι x,
        (Scheme.IdealSheafData.range_subschemeι _).subset ⟨x, rfl⟩, rfl⟩
    have hle := (topologicalKrullDim_le_of_subset hsub).trans
      (hM.topologicalKrullDim_image_le E.1 E.2)
    rw [hy2] at hle
    exact absurd hle (by decide)
  · rw [TensorProduct.tmul_zero, map_zero]

/-- The surfaces of a prime divisor `E` of a fourfold are its prime divisors, so every surface
cycle on `E` is the cycle of a `ℚ`-divisor, whose components are surfaces of the cycle. -/
private theorem exists_divisorCycle_eq [IsIntegral Z] (hdim : topologicalKrullDim Z = 4)
    (E : MMP.Mori.PrimeDivisor Z) (c : ComponentCycles Z E 2) :
    ∃ L : QDivisor E.idealSheaf.subscheme, Chow.divisorCycle _ L = c ∧
      ∀ P ∈ L.support, Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) _ 2
        P.genericPoint c ≠ 0 := by
  classical
  obtain ⟨s, hs, -⟩ := ConductorBlowup.exists_eq_sum_rationalCoeff_smul c
  let L : QDivisor E.idealSheaf.subscheme :=
    Finsupp.onFinset (s.preimage (fun P : MMP.Mori.PrimeDivisor E.idealSheaf.subscheme =>
        P.genericPoint) AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn)
      (fun P => Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) _ 2 P.genericPoint c)
      fun P hP => Finset.mem_preimage.2 (by_contra fun h => hP (hs _ h))
  refine ⟨L, ConductorBlowup.rationalCycleGroup_ext fun y => ?_, fun P hP => ?_⟩
  · by_cases hP : ∃ P : MMP.Mori.PrimeDivisor E.idealSheaf.subscheme, P.genericPoint = y
    · obtain ⟨P, rfl⟩ := hP
      by_cases h2 : Stacks.Chow.relativeDimension
          (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
          (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) P.genericPoint = (2 : ℕ)
      · rw [ConductorBlowup.rationalCoeff_divisorCycle _ _ h2]
        rfl
      · rw [ConductorBlowup.rationalCoeff_eq_zero_of_relativeDimension_ne _ h2,
          ConductorBlowup.rationalCoeff_eq_zero_of_relativeDimension_ne _ h2]
    · push Not at hP
      rw [ConductorBlowup.rationalCoeff_divisorCycle_eq_zero _ hP]
      by_cases h2 : Stacks.Chow.relativeDimension
          (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
          (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) y = (2 : ℕ)
      · have hcoh := ConductorBlowup.coheight_eq_one_of_topologicalKrullDim_eq_four hdim E y
          ((ConductorBlowup.relativeDimension_eq_iff_topologicalKrullDim_closure _ y 2).1 h2)
        exact absurd (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh)
          (hP _)
      · rw [ConductorBlowup.rationalCoeff_eq_zero_of_relativeDimension_ne _ h2]
  · exact Finsupp.mem_support_iff.1 hP

/-- On a component `E` of `F` mapping to a curve or a point, every surface is a prime divisor of
the threefold `E`, and every surface cycle pushes forward to zero: so `Cᵢ^v = Cᵢ`. -/
private theorem verticalDivisorClasses_eq_divisorClasses [Y.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y}
    [r.IsOver (Spec (.of ℂ))] [IsProper r] {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D) (hdim : topologicalKrullDim Z = 4)
    (E : F.support) :
    verticalDivisorClasses r E.1 = divisorClasses E.1.idealSheaf.subscheme := by
  have : IsIntegral Z :=
    (hM.isResolution.2.1 : AlgebraicGeometry.IsVariety ℂ (r ≫ sY)).toIsIntegral
  refine le_antisymm ?_ ?_
  · rintro _ ⟨L, -, rfl⟩
    obtain ⟨Dv, hDv, -⟩ := exists_divisorCycle_eq hdim E.1 L
    exact ⟨Dv, by rw [← hDv]; rfl⟩
  · rintro _ ⟨Dv, rfl⟩
    exact ⟨Chow.divisorCycle _ Dv, componentPushforward_eq_zero hM E _, rfl⟩

private theorem verticalKernel_eq_algebraicKernel [Y.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y}
    [r.IsOver (Spec (.of ℂ))] [IsProper r] {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D) (hdim : topologicalKrullDim Z = 4) :
    verticalKernel r F = algebraicKernel F := by
  rw [verticalKernel, algebraicKernel]
  congr 1
  exact funext (verticalDivisorClasses_eq_divisorClasses hM hdim)

private theorem verticalSurfaceClasses_eq_orientedSurfaceClasses [Y.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y}
    [r.IsOver (Spec (.of ℂ))] [IsProper r] {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D) :
    verticalSurfaceClasses r F = orientedSurfaceClasses F := by
  have h : verticalSurfaceCoefficients r F = orientedSurfaceCoefficients F := by
    refine le_antisymm inf_le_left fun a ha => ⟨ha, fun σ _ => ?_⟩
    exact (topologicalKrullDim_le_of_subset
      (Set.image_mono (σ.carrier_subset.trans Set.inter_subset_left))).trans
      (hM.topologicalKrullDim_image_le σ.fst σ.fst_mem)
  rw [verticalSurfaceClasses, h, orientedSurfaceClasses]

/-- The dimension of a subspace `O` of a subquotient `K/B` only depends on `K`, `B` and `O`. -/
private theorem finrank_map_mkQ_congr {V : Type*} [AddCommGroup V] [Module ℚ V]
    {K K' B B' O O' : Submodule ℚ V} (hK : K = K') (hB : B = B') (hO : O = O') :
    Module.finrank ℚ ((O.comap K.subtype).map (B.comap K.subtype).mkQ) =
      Module.finrank ℚ ((O'.comap K'.subtype).map (B'.comap K'.subtype).mkQ) := by
  subst hK hB hO
  rfl

/-- On a curve-and-point model, the vertical classes over `Q` are the classes of surface cycles
all of whose surfaces map into `Q`: the vertical condition is automatic. -/
private theorem verticalKernelOver_eq [Y.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y}
    [r.IsOver (Spec (.of ℂ))] [IsProper r] {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D) (Q : Set Y) :
    verticalKernelOver r F Q = exceptionalKernel F fun E =>
      (cyclesMappingInto (E.1.idealSheaf.subschemeι ≫ r) 2 Q).map
        (Chow.rationalCycleClass _ 2) := by
  rw [verticalKernelOver]
  congr 1
  funext E
  rw [verticalDivisorClassesOver,
    LinearMap.ker_eq_top.2 (LinearMap.ext (componentPushforward_eq_zero hM E)), top_inf_eq]

section LocalSystems

open Opposite MMP MMP.Analytic MMP.Analytic.ComplexPoints

/-! ### Flat families of forms -/

section Flat

variable {X : TopCat.{0}} (𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) X)

/-- The flat families of linear forms on the stalks of a sheaf `𝓛`: families `(w_t)_t` with
`t ↦ w_t (s_t)` constant on every preconnected open `O` and every section `s` over `O`. -/
private noncomputable def flatForms :
    Submodule ℚ (∀ t : X, Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk t)) :=
  ⨅ (O : Opens X) (_ : IsPreconnected (O : Set X))
    (s : ((TopCat.Sheaf.forget _ _).obj 𝓛).obj (op O))
    (t) (ht : t ∈ O) (t') (ht' : t' ∈ O),
    LinearMap.ker
      (LinearMap.applyₗ (R := ℚ)
          (((TopCat.Sheaf.forget _ _).obj 𝓛).germ O t ht s) ∘ₗ
          LinearMap.proj (R := ℚ)
            (φ := fun t ↦ Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk t)) t -
        LinearMap.applyₗ (R := ℚ)
          (((TopCat.Sheaf.forget _ _).obj 𝓛).germ O t' ht' s) ∘ₗ
          LinearMap.proj (R := ℚ)
            (φ := fun t ↦ Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk t)) t')

variable {𝓛} in
private theorem mem_flatForms
    {w : ∀ t : X, Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk t)} :
    w ∈ flatForms 𝓛 ↔ ∀ (O : Opens X), IsPreconnected (O : Set X) →
      ∀ (s : ((TopCat.Sheaf.forget _ _).obj 𝓛).obj (op O)) (t) (ht : t ∈ O) (t') (ht' : t' ∈ O),
        w t (((TopCat.Sheaf.forget _ _).obj 𝓛).germ O t ht s) =
          w t' (((TopCat.Sheaf.forget _ _).obj 𝓛).germ O t' ht' s) := by
  simp only [flatForms, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.applyₗ_apply_apply, sub_eq_zero]

end Flat

/-! ### Stalks of inverse images and of sheafifications -/

section Stalks

variable {A B : TopCat.{0}}

private lemma stalkPushforward_naturality' (f : A ⟶ B)
    {F G : TopCat.Presheaf (ModuleCat.{0} ℚ) A} (g : F ⟶ G) (x : A) :
    TopCat.Presheaf.stalkPushforward _ f F x ≫ (TopCat.Presheaf.stalkFunctor _ x).map g =
      (TopCat.Presheaf.stalkFunctor _ (f x)).map ((TopCat.Presheaf.pushforward _ f).map g) ≫
        TopCat.Presheaf.stalkPushforward _ f G x := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦ ?_
  erw [TopCat.Presheaf.stalkPushforward_germ_assoc, TopCat.Presheaf.stalkFunctor_map_germ,
    TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ]
  rfl

private lemma stalkPushforward_comp_naturality' (f : A ⟶ B)
    {F' : TopCat.Presheaf (ModuleCat.{0} ℚ) B} {G G' : TopCat.Presheaf (ModuleCat.{0} ℚ) A}
    (u : F' ⟶ (TopCat.Presheaf.pushforward _ f).obj G) (v : G ⟶ G') (x : A) :
    ((TopCat.Presheaf.stalkFunctor _ (f x)).map u ≫ TopCat.Presheaf.stalkPushforward _ f G x) ≫
        (TopCat.Presheaf.stalkFunctor _ x).map v =
      (TopCat.Presheaf.stalkFunctor _ (f x)).map (u ≫ (TopCat.Presheaf.pushforward _ f).map v) ≫
        TopCat.Presheaf.stalkPushforward _ f G' x := by
  refine (Category.assoc _ _ _).trans ?_
  erw [stalkPushforward_naturality' f v x, Functor.map_comp, Category.assoc]
  rfl

/-- The canonical map `F_{f(x)} ⟶ (f⁻¹F)_x` is an isomorphism. -/
private lemma isIso_stalkToPullbackStalk (f : A ⟶ B) (F : TopCat.Sheaf (ModuleCat.{0} ℚ) B)
    (x : A) : IsIso (stalkToPullbackStalk f F x) := by
  let ι := (TopCat.Sheaf.pullbackIso (ModuleCat.{0} ℚ) f).app F
  have hunit : (TopCat.Sheaf.forget _ B).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F ≫
      (TopCat.Sheaf.pushforward _ f).map ι.hom) =
      (TopCat.Presheaf.pullbackPushforwardAdjunction _ f).unit.app
          ((TopCat.Sheaf.forget _ B).obj F) ≫
        (TopCat.Presheaf.pushforward _ f).map (toSheafify _ _) := by
    have := Adjunction.unit_leftAdjointUniq_hom_app
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) (ModuleCat.{0} ℚ)
        _ _) F
    have h2 := (sheafToPresheaf _ _).congr_map this
    erw [h2]
    unfold Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    erw [Adjunction.map_restrictFullyFaithful_unit_app]
    simp only [Adjunction.comp_unit_app, Iso.refl_hom, NatTrans.id_app, Functor.map_id,
      Category.comp_id]
    rfl
  have hst : stalkToPullbackStalk f F x ≫
      (TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ A).map ι.hom) =
      TopCat.Presheaf.stalkPullbackHom _ f ((TopCat.Sheaf.forget _ B).obj F) x ≫
        (TopCat.Presheaf.stalkFunctor _ x).map (toSheafify _ _) := by
    have hunit' : (TopCat.Sheaf.forget _ B).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F) ≫
        (TopCat.Presheaf.pushforward _ f).map ((TopCat.Sheaf.forget _ A).map ι.hom) =
        (TopCat.Presheaf.pullbackPushforwardAdjunction _ f).unit.app
          ((TopCat.Sheaf.forget _ B).obj F) ≫
        (TopCat.Presheaf.pushforward _ f).map (toSheafify _ _) := by
      rw [← hunit, Functor.map_comp]
      rfl
    unfold stalkToPullbackStalk TopCat.Presheaf.stalkPullbackHom
    refine (stalkPushforward_comp_naturality' _ _ _ x).trans
      (Eq.trans ?_ (stalkPushforward_comp_naturality' _ _ _ x).symm)
    exact congrArg (fun g ↦ (TopCat.Presheaf.stalkFunctor _ (f x)).map g ≫
      TopCat.Presheaf.stalkPushforward _ f _ x) hunit'
  have h1 : IsIso (TopCat.Presheaf.stalkPullbackHom _ f ((TopCat.Sheaf.forget _ B).obj F) x) :=
    (TopCat.Presheaf.stalkPullbackIso _ f ((TopCat.Sheaf.forget _ B).obj F) x).isIso_hom
  have h2 := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{0} ℚ)
    ((TopCat.Presheaf.pullback _ f).obj ((TopCat.Sheaf.forget _ B).obj F))
  have h3 : IsIso ((TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ A).map ι.hom)) :=
    ((TopCat.Presheaf.stalkFunctor _ x).mapIso ((TopCat.Sheaf.forget _ A).mapIso ι)).isIso_hom
  have : IsIso (stalkToPullbackStalk f F x ≫
      (TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ A).map ι.hom)) := by
    rw [hst]; exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h3 this

private theorem bijective_stalkToPullbackStalk (f : A ⟶ B)
    (F : TopCat.Sheaf (ModuleCat.{0} ℚ) B) (x : A) :
    Function.Bijective (stalkToPullbackStalk f F x).hom :=
  have := isIso_stalkToPullbackStalk f F x
  ConcreteCategory.bijective_of_isIso (stalkToPullbackStalk f F x)

end Stalks

/-! ### Parallel transport in a local system -/

section Transport

variable {X : TopCat.{0}} {𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) X}

/-- The identification of stalks at equal points is a cast. -/
private lemma stalkCongr_of_eq_apply (F : TopCat.Presheaf (ModuleCat.{0} ℚ) X)
    {x y : X} (h : x = y) (e : (ToType (F.stalk x)) = ToType (F.stalk y)) (w : F.stalk x) :
    (F.stalkCongr (.of_eq h)).hom.hom w = cast e w := by
  subst h
  change (F.stalkSpecializes (specializes_refl x)).hom w = w
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

private lemma stalkCongr_germ (F : TopCat.Presheaf (ModuleCat.{0} ℚ) X) {x y : X} (h : x = y)
    {U : Opens X} (hx : x ∈ U) (s : ToType (F.obj (op U))) :
    (F.stalkCongr (.of_eq h)).hom.hom (F.germ U x hx s) = F.germ U y (h ▸ hx) s := by
  subst h
  rw [stalkCongr_of_eq_apply F rfl rfl]
  rfl

/-- The germ of the image of a global section under a sheaf morphism is the image of its germ. -/
private lemma germ_map_hom {P Q : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (Ψ : P ⟶ Q)
    (x : X) (s : ToType (P.obj.obj (op ⊤))) :
    (((TopCat.Sheaf.forget _ X).obj Q).germ ⊤ x trivial).hom
        ((((TopCat.Sheaf.forget _ X).map Ψ).app (op ⊤)).hom s) =
      (TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map Ψ)
        ((((TopCat.Sheaf.forget _ X).obj P).germ ⊤ x trivial).hom s) :=
  (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial _ s).symm

/-- On stalks, the inverse of a sheaf isomorphism undoes the isomorphism. -/
private lemma stalk_inv_hom_apply {P Q : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    (Ψ : P ≅ Q) (x : X) (a : ((TopCat.Sheaf.forget _ X).obj P).stalk x) :
    (TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map Ψ.inv)
      ((TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map Ψ.hom) a) = a :=
  ((TopCat.Presheaf.stalkFunctor _ x).mapIso
    ((TopCat.Sheaf.forget _ X).mapIso Ψ)).hom_inv_id_apply a

/-- The global section of the constant sheaf with value `e`. -/
private noncomputable def constSection {W : TopCat.{0}} (E : ModuleCat.{0} ℚ) (e : E) :
    ToType (((TopCat.Sheaf.forget _ W).obj
      ((constantSheaf (Opens.grothendieckTopology W) (ModuleCat.{0} ℚ)).obj E)).obj (op ⊤)) :=
  ((CategoryTheory.toSheafify (Opens.grothendieckTopology W)
    ((Functor.const (Opens W)ᵒᵖ).obj E)).app (op ⊤)).hom e

/-- Every germ of a constant sheaf is the germ of a constant section. -/
private theorem constantSheaf_exists_constSection_germ {W : TopCat.{0}} (E : ModuleCat.{0} ℚ)
    (p : W) (c : ToType (((TopCat.Sheaf.forget _ W).obj
      ((constantSheaf (Opens.grothendieckTopology W) (ModuleCat.{0} ℚ)).obj E)).stalk p)) :
    ∃ e : E, ((TopCat.Sheaf.forget _ W).obj
      ((constantSheaf (Opens.grothendieckTopology W) (ModuleCat.{0} ℚ)).obj E)).germ
          ⊤ p (Opens.mem_top p) (constSection E e) = c := by
  let K : TopCat.Presheaf (ModuleCat.{0} ℚ) W := (Functor.const (Opens W)ᵒᵖ).obj E
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso p (ModuleCat.{0} ℚ) K
  obtain ⟨c', hc'⟩ := (ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) p).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology W) K))).2 c
  obtain ⟨U, hU, e, rfl⟩ := K.exists_germ_eq c'
  refine ⟨e, ?_⟩
  have this : K.germ U p hU e = K.germ ⊤ p (Opens.mem_top p) e :=
    TopCat.Presheaf.germ_res_apply K (homOfLE (le_top : U ≤ ⊤)) p hU e
  rw [← hc', this]
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply (F := K) ⊤ p (Opens.mem_top p)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology W) K) e).symm

/-- A sheaf isomorphic to a constant sheaf has a global section with any prescribed germ. -/
private lemma exists_global_germ_eq {W : TopCat.{0}} {P : TopCat.Sheaf (ModuleCat.{0} ℚ) W}
    {E : ModuleCat.{0} ℚ}
    (φ : P ≅ (constantSheaf (Opens.grothendieckTopology W) (ModuleCat.{0} ℚ)).obj E) (x : W)
    (c : ((TopCat.Sheaf.forget _ W).obj P).stalk x) :
    ∃ s : ToType (P.obj.obj (op ⊤)),
      c = (((TopCat.Sheaf.forget _ W).obj P).germ ⊤ x trivial).hom s := by
  obtain ⟨e, he⟩ := constantSheaf_exists_constSection_germ E x
    ((TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ W).map φ.hom) c)
  refine ⟨(((TopCat.Sheaf.forget _ _).map φ.inv).app (op ⊤)).hom (constSection E e), ?_⟩
  refine Eq.trans ?_ (germ_map_hom φ.inv x _).symm
  exact (stalk_inv_hom_apply φ x c).symm.trans (congrArg _ he.symm)

/-- The stalks of a local system are finite-dimensional. -/
private theorem finiteDimensional_stalk (h𝓛 : IsLocalSystem 𝓛) (x : X) :
    FiniteDimensional ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk x) := by
  obtain ⟨V, hx, E, hE, ⟨φ⟩⟩ := h𝓛 x
  let p : (Opens.toTopCat X).obj V := ⟨x, hx⟩
  let C := (TopCat.Sheaf.forget _ _).obj
    ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj V))
      (ModuleCat.{0} ℚ)).obj E)
  let g : E →ₗ[ℚ] C.stalk p :=
    (C.germ ⊤ p (Opens.mem_top p)).hom ∘ₗ ((CategoryTheory.toSheafify
      (Opens.grothendieckTopology _) ((Functor.const (Opens _)ᵒᵖ).obj E)).app (op ⊤)).hom
  have hg : Function.Surjective g := fun c ↦ constantSheaf_exists_constSection_germ E p c
  haveI := hE
  haveI : FiniteDimensional ℚ (C.stalk p) := Module.Finite.of_surjective g hg
  let e₁ : ((TopCat.Sheaf.forget _ X).obj 𝓛).stalk x ≃ₗ[ℚ]
      ((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        V.inclusion').obj 𝓛)).stalk p :=
    LinearEquiv.ofBijective (stalkToPullbackStalk V.inclusion' 𝓛 p).hom
      (bijective_stalkToPullbackStalk V.inclusion' 𝓛 p)
  let e₂ : _ ≃ₗ[ℚ] C.stalk p := ((TopCat.Presheaf.stalkFunctor _ p).mapIso
    ((TopCat.Sheaf.forget _ _).mapIso φ)).toLinearEquiv
  exact Module.Finite.equiv (e₁.trans e₂).symm

/-- `u` and `v` are the end germs of a global section of the inverse image of `𝓛` along the
path `γ`. -/
private def PathRel (𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) X) {x y : X} (γ : Path x y)
    (u : ((TopCat.Sheaf.forget _ _).obj 𝓛).stalk x)
    (v : ((TopCat.Sheaf.forget _ _).obj 𝓛).stalk y) : Prop :=
  ∃ s : ToType (((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
      (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj 𝓛).obj.obj (op ⊤)),
    (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
        𝓛 0).hom
      ((((TopCat.Sheaf.forget _ _).obj 𝓛).stalkCongr (.of_eq γ.source.symm)).hom.hom u) =
      (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj 𝓛)).germ
          ⊤ 0 trivial).hom s ∧
    (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
        𝓛 1).hom
      ((((TopCat.Sheaf.forget _ _).obj 𝓛).stalkCongr (.of_eq γ.target.symm)).hom.hom v) =
      (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj 𝓛)).germ
          ⊤ 1 trivial).hom s

/-- **Parallel transport.** The transport relation along a path is the graph of a linear
isomorphism, compatible with concatenation and reversal. -/
private lemma exists_transport [LocallyPathConnectedSpace X] (h𝓛 : IsLocalSystem 𝓛) :
    ∃ tr : ∀ {x y : X}, Path x y → (((TopCat.Sheaf.forget _ _).obj 𝓛).stalk x ≃ₗ[ℚ]
        ((TopCat.Sheaf.forget _ _).obj 𝓛).stalk y),
      (∀ {x y : X} (γ : Path x y) u v, PathRel 𝓛 γ u v ↔ tr γ u = v) ∧
      (∀ {x y z : X} (γ : Path x y) (δ : Path y z) u, tr (γ.trans δ) u = tr δ (tr γ u)) ∧
      (∀ {x y : X} (γ : Path x y) u, tr γ.symm (tr γ u) = u) := by
  have hinj : ∀ {a b : X} (h : a = b), Function.Injective
      (((TopCat.Sheaf.forget _ X).obj 𝓛).stalkCongr (.of_eq h)).hom.hom := fun h =>
    (ConcreteCategory.bijective_of_isIso (C := ModuleCat.{0} ℚ) _).1
  let tr : ∀ {x y : X}, Path x y → (((TopCat.Sheaf.forget _ _).obj 𝓛).stalk x ≃ₗ[ℚ]
      ((TopCat.Sheaf.forget _ _).obj 𝓛).stalk y) :=
    fun γ ↦ (h𝓛.parallelTransport (Path.Homotopic.Quotient.mk γ)).toLinearEquiv
  have htrans : ∀ {x y z : X} (γ : Path x y) (δ : Path y z) u,
      tr (γ.trans δ) u = tr δ (tr γ u) := by
    intro x y z γ δ u
    change (h𝓛.parallelTransport (Path.Homotopic.Quotient.mk (γ.trans δ))).hom u = _
    rw [Path.Homotopic.Quotient.mk_trans, h𝓛.parallelTransport_trans]
    rfl
  have hrefl : ∀ (x : X) u, tr (Path.refl x) u = u := by
    intro x u
    have h1 : Path.Homotopic.Quotient.mk ((Path.refl x).trans (Path.refl x)) =
        Path.Homotopic.Quotient.mk (Path.refl x) :=
      Quotient.sound ⟨Path.Homotopy.transRefl (Path.refl x)⟩
    have h2 : ∀ v, tr (Path.refl x) (tr (Path.refl x) v) = tr (Path.refl x) v := by
      intro v
      rw [← htrans]
      change (h𝓛.parallelTransport (Path.Homotopic.Quotient.mk _)).hom v =
          (h𝓛.parallelTransport (Path.Homotopic.Quotient.mk _)).hom v
      rw [h1]
    have := h2 ((tr (Path.refl x)).symm u)
    rwa [LinearEquiv.apply_symm_apply] at this
  refine ⟨tr, ?_, htrans, ?_⟩
  · intro x y γ u v
    constructor
    · rintro ⟨s, h0, h1⟩
      have key := h𝓛.parallelTransport_germ γ s u
        (by rw [← stalkCongr_of_eq_apply _ γ.source.symm]; exact h0)
      rw [← stalkCongr_of_eq_apply _ γ.target.symm] at key
      exact hinj γ.target.symm ((bijective_stalkToPullbackStalk _ _ 1).1 (key.trans h1.symm))
    · rintro rfl
      obtain ⟨φ⟩ := h𝓛.nonempty_pullback_path_iso_constantSheaf γ
      obtain ⟨s, h0⟩ := exists_global_germ_eq φ 0
        ((stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
          𝓛 0).hom ((((TopCat.Sheaf.forget _ X).obj 𝓛).stalkCongr
            (.of_eq γ.source.symm)).hom.hom u))
      have h1 := h𝓛.parallelTransport_germ γ s u
        (by rw [← stalkCongr_of_eq_apply _ γ.source.symm]; exact h0)
      rw [← stalkCongr_of_eq_apply _ γ.target.symm] at h1
      exact ⟨s, h0, h1⟩
  · intro x y γ u
    rw [← htrans]
    have h1 : Path.Homotopic.Quotient.mk (γ.trans γ.symm) =
        Path.Homotopic.Quotient.mk (Path.refl x) :=
      Quotient.sound ⟨(Path.Homotopy.reflTransSymm γ).symm⟩
    change (h𝓛.parallelTransport (Path.Homotopic.Quotient.mk _)).hom u = u
    rw [h1]
    exact hrefl x u

/-- The section of `f^* 𝓛` over `f⁻¹(W)` attached to a section of `𝓛` over `W`. -/
private noncomputable def unitSec {A : TopCat.{0}} (f : A ⟶ X) {W : Opens X}
    (r : ToType (((TopCat.Sheaf.forget _ X).obj 𝓛).obj (op W))) :
    ToType (((TopCat.Sheaf.forget _ A).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj
      𝓛)).obj (op ((Opens.map f).obj W))) :=
  (((TopCat.Sheaf.forget _ X).map
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app 𝓛)).app
      (op W)).hom r

private theorem stalkToPullbackStalk_germ {A : TopCat.{0}} (f : A ⟶ X) {W : Opens X}
    (r : ToType (((TopCat.Sheaf.forget _ X).obj 𝓛).obj (op W))) (x : A) (hx : f x ∈ W) :
    (stalkToPullbackStalk f 𝓛 x).hom (((TopCat.Sheaf.forget _ X).obj 𝓛).germ W (f x) hx r) =
      ((TopCat.Sheaf.forget _ A).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj 𝓛)).germ
        ((Opens.map f).obj W) x hx (unitSec f r) := by
  have h : ((TopCat.Sheaf.forget _ X).obj 𝓛).germ W (f x) hx ≫ stalkToPullbackStalk f 𝓛 x =
      ((TopCat.Sheaf.forget _ X).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app 𝓛)).app
          (op W) ≫ ((TopCat.Sheaf.forget _ A).obj
            ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj 𝓛)).germ ((Opens.map f).obj W) x
              hx := by
    unfold stalkToPullbackStalk
    erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ]
    rfl
  exact congrArg (fun φ => φ.hom r) h

/-- Every section of `f^* 𝓛` is, near each point, the image of a section of `𝓛`. -/
private theorem exists_local_germ {A : TopCat.{0}} (f : A ⟶ X) {U : Opens A}
    (s : ToType (((TopCat.Sheaf.forget _ A).obj
      ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj 𝓛)).obj (op U))) (x₀ : A) (hx₀ : x₀ ∈ U) :
    ∃ (W : Opens X) (r : ToType (((TopCat.Sheaf.forget _ X).obj 𝓛).obj (op W))) (N : Opens A)
      (_ : x₀ ∈ N) (hNU : N ≤ U) (hNW : N ≤ (Opens.map f).obj W),
      ∀ x (hx : x ∈ N), ((TopCat.Sheaf.forget _ A).obj
        ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj 𝓛)).germ U x (hNU hx) s =
        (stalkToPullbackStalk f 𝓛 x).hom
          (((TopCat.Sheaf.forget _ X).obj 𝓛).germ W (f x) (hNW hx) r) := by
  obtain ⟨y, hy⟩ := (bijective_stalkToPullbackStalk f 𝓛 x₀).2
    (((TopCat.Sheaf.forget _ A).obj
      ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj 𝓛)).germ U x₀ hx₀ s)
  obtain ⟨W, hW, r, rfl⟩ := ((TopCat.Sheaf.forget _ X).obj 𝓛).exists_germ_eq y
  rw [stalkToPullbackStalk_germ] at hy
  obtain ⟨N, hN, iW, iU, e⟩ := ((TopCat.Sheaf.forget _ A).obj
    ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj 𝓛)).germ_eq x₀ _ _ _ _ hy
  refine ⟨W, r, N, hN, iU.le, iW.le, fun x hx => ?_⟩
  rw [← TopCat.Presheaf.germ_res_apply _ iU x hx, ← e, TopCat.Presheaf.germ_res_apply]
  exact (stalkToPullbackStalk_germ f r x _).symm

/-- A form of a flat family is unchanged along the identification of stalks at equal points. -/
private lemma apply_stalkCongr
    (w : ∀ t : X, Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk t)) {a b : X}
    (h : a = b) (u : ((TopCat.Sheaf.forget _ X).obj 𝓛).stalk a) :
    w b ((((TopCat.Sheaf.forget _ X).obj 𝓛).stalkCongr (.of_eq h)).hom.hom u) = w a u := by
  subst h
  rw [stalkCongr_of_eq_apply _ rfl rfl]
  rfl

/-- **Flat forms are invariant under transport.** -/
private theorem apply_eq_of_pathRel [LocallyPathConnectedSpace X]
    {w : ∀ t : X, Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk t)}
    (hw : w ∈ flatForms 𝓛) {x y : X} (γ : Path x y) {u v} (h : PathRel 𝓛 γ u v) :
    w x u = w y v := by
  obtain ⟨σ, h0, h1⟩ := h
  let f := TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap
  let e := fun a ↦ Equiv.ofBijective _ (bijective_stalkToPullbackStalk f 𝓛 a)
  let P := (TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj 𝓛)
  let g : unitInterval → ℚ := fun a ↦ w (f a) ((e a).symm ((P.germ ⊤ a trivial).hom σ))
  have hg : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro a₀
    obtain ⟨W, r, N, ha₀N, hNU, hNW, hloc⟩ := exists_local_germ f σ a₀ trivial
    have hfa₀W : f a₀ ∈ W := hNW ha₀N
    let O : Opens X := ⟨pathComponentIn (W : Set X) (f a₀), W.isOpen.pathComponentIn _⟩
    have hOW : O ≤ W := pathComponentIn_subset
    have hfa₀ : f a₀ ∈ O := mem_pathComponentIn_self hfa₀W
    have hOpre : IsPreconnected (O : Set X) :=
      (isPathConnected_pathComponentIn hfa₀W).isConnected.isPreconnected
    have key : ∀ c (hcN : c ∈ N) (hcO : f c ∈ O), g c =
        w (f c) (((TopCat.Sheaf.forget _ X).obj 𝓛).germ O (f c) hcO
          ((((TopCat.Sheaf.forget _ X).obj 𝓛).map (homOfLE hOW).op).hom r)) := by
      intro c hcN hcO
      have hc := hloc c hcN
      change w (f c) ((e c).symm ((P.germ ⊤ c trivial).hom σ)) = _
      rw [show (P.germ ⊤ c trivial).hom σ = (P.germ ⊤ c (hNU hcN)).hom σ from rfl, hc]
      rw [show (e c).symm ((stalkToPullbackStalk f 𝓛 c).hom _) = _ from
        (e c).symm_apply_apply _, TopCat.Presheaf.germ_res_apply]
    filter_upwards [N.isOpen.mem_nhds ha₀N,
      (O.isOpen.preimage f.hom.continuous).mem_nhds hfa₀] with b hbN hbO
    rw [key b hbN hbO, key a₀ ha₀N hfa₀]
    exact (mem_flatForms.1 hw) O hOpre _ _ hbO _ hfa₀
  have hc := hg.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ 0)
    (Set.mem_univ 1)
  have hg0 : g 0 = w x u := by
    have h0' : (P.germ ⊤ 0 trivial).hom σ = (stalkToPullbackStalk f 𝓛 0).hom
        ((((TopCat.Sheaf.forget _ _).obj 𝓛).stalkCongr (.of_eq γ.source.symm)).hom.hom u) :=
      h0.symm
    change w (f 0) ((e 0).symm ((P.germ ⊤ 0 trivial).hom σ)) = w x u
    rw [h0', show (e 0).symm ((stalkToPullbackStalk f 𝓛 0).hom _) = _ from
      (e 0).symm_apply_apply _]
    exact apply_stalkCongr w γ.source.symm u
  have hg1 : g 1 = w y v := by
    have h1' : (P.germ ⊤ 1 trivial).hom σ = (stalkToPullbackStalk f 𝓛 1).hom
        ((((TopCat.Sheaf.forget _ _).obj 𝓛).stalkCongr (.of_eq γ.target.symm)).hom.hom v) :=
      h1.symm
    change w (f 1) ((e 1).symm ((P.germ ⊤ 1 trivial).hom σ)) = w y v
    rw [h1', show (e 1).symm ((stalkToPullbackStalk f 𝓛 1).hom _) = _ from
      (e 1).symm_apply_apply _]
    exact apply_stalkCongr w γ.target.symm v
  rw [← hg0, ← hg1, hc]

/-- **A section transports to itself** along a path in its domain. -/
private theorem pathRel_germ {O : Opens X}
    (s : ToType (((TopCat.Sheaf.forget _ X).obj 𝓛).obj (op O))) {x y : X} (γ : Path x y)
    (hγ : ∀ a, γ a ∈ O) (hx : x ∈ O) (hy : y ∈ O) :
    PathRel 𝓛 γ (((TopCat.Sheaf.forget _ X).obj 𝓛).germ O x hx s)
      (((TopCat.Sheaf.forget _ X).obj 𝓛).germ O y hy s) := by
  let f := TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap
  let P := (TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj 𝓛)
  have htop : (⊤ : Opens (TopCat.of unitInterval)) ≤ (Opens.map f).obj O := fun a _ ↦ hγ a
  have key : ∀ a : unitInterval, (stalkToPullbackStalk f 𝓛 a).hom
      (((TopCat.Sheaf.forget _ X).obj 𝓛).germ O (f a) (hγ a) s) =
      (P.germ ⊤ a trivial).hom ((P.map (homOfLE htop).op).hom (unitSec f s)) := fun a ↦
    (stalkToPullbackStalk_germ f s a (hγ a)).trans
      (TopCat.Presheaf.germ_res_apply P (homOfLE htop) a trivial (unitSec f s)).symm
  refine ⟨(P.map (homOfLE htop).op).hom (unitSec f s), ?_, ?_⟩
  · rw [stalkCongr_germ _ γ.source.symm]
    exact key 0
  · rw [stalkCongr_germ _ γ.target.symm]
    exact key 1

end Transport

/-! ### Flat forms are the invariant forms -/

section FlatInvariant

variable {X : TopCat.{0}} {𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) X}

/-- The differences `w - v` of the end germs of global sections of `γ^* 𝓛` along loops `γ` at
`t`: they span the relations of the monodromy coinvariants of `𝓛_t`. -/
private def loopSet (𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) X) (t : X) :
    Set (((TopCat.Sheaf.forget _ _).obj 𝓛).stalk t) :=
  {u | ∃ (γ : Path t t)
      (s : ToType (((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
          𝓛).obj.obj (op ⊤)))
      (w v : ((TopCat.Sheaf.forget _ _).obj 𝓛).stalk t),
      (stalkToPullbackStalk
          (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
          𝓛 0).hom
        ((((TopCat.Sheaf.forget _ _).obj 𝓛).stalkCongr
          (.of_eq γ.source.symm)).hom.hom w) =
        (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
          (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
            𝓛)).germ ⊤ 0 trivial).hom s ∧
      (stalkToPullbackStalk
          (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
          𝓛 1).hom
        ((((TopCat.Sheaf.forget _ _).obj 𝓛).stalkCongr
          (.of_eq γ.target.symm)).hom.hom v) =
        (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
          (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
            𝓛)).germ ⊤ 1 trivial).hom s ∧
      u = w - v}

private theorem sub_mem_loopSet {t : X} {γ : Path t t} {w v} (h : PathRel 𝓛 γ w v) :
    w - v ∈ loopSet 𝓛 t := by
  obtain ⟨s, h0, h1⟩ := h
  exact ⟨γ, s, w, v, h0, h1, rfl⟩

private theorem pathRel_of_mem_loopSet {t : X} {u} (h : u ∈ loopSet 𝓛 t) :
    ∃ (γ : Path t t) (w v : ((TopCat.Sheaf.forget _ _).obj 𝓛).stalk t),
      PathRel 𝓛 γ w v ∧ u = w - v := by
  obtain ⟨γ, s, w, v, h0, h1, rfl⟩ := h
  exact ⟨γ, w, v, ⟨s, h0, h1⟩, rfl⟩

variable [LocallyPathConnectedSpace X] [PathConnectedSpace X]

/-- **A flat family of forms vanishing at one point vanishes.** -/
private theorem eq_zero_of_mem_flatForms_of_isLocalSystem (h𝓛 : IsLocalSystem 𝓛)
    {w : ∀ t : X, Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk t)}
    (hw : w ∈ flatForms 𝓛) (t₀ : X) (h0 : w t₀ = 0) : w = 0 := by
  obtain ⟨tr, htr, -, -⟩ := exists_transport h𝓛
  funext t
  refine LinearMap.ext fun v ↦ ?_
  rw [apply_eq_of_pathRel hw (PathConnectedSpace.somePath t t₀) ((htr _ v _).2 rfl), h0]
  rfl

/-- **Evaluation at a point identifies the flat forms with the invariant forms**, the forms
vanishing on the relations of the monodromy coinvariants. -/
private theorem finite_and_finrank_flatForms (h𝓛 : IsLocalSystem 𝓛) (t₀ : X) :
    Module.Finite ℚ (flatForms 𝓛) ∧ Module.finrank ℚ (flatForms 𝓛) =
      Module.finrank ℚ (((TopCat.Sheaf.forget _ _).obj 𝓛).stalk t₀ ⧸
        Submodule.span ℚ (loopSet 𝓛 t₀)) := by
  obtain ⟨tr, htr, htrans, hsymm⟩ := exists_transport h𝓛
  haveI := finiteDimensional_stalk h𝓛 t₀
  let V := ((TopCat.Sheaf.forget _ _).obj 𝓛).stalk t₀
  let S := Submodule.span ℚ (loopSet 𝓛 t₀)
  let ev : flatForms 𝓛 →ₗ[ℚ] Module.Dual ℚ V :=
    (LinearMap.proj (R := ℚ)
      (φ := fun t ↦ Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk t)) t₀).comp
      (flatForms 𝓛).subtype
  have hinj : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (eq_zero_of_mem_flatForms_of_isLocalSystem h𝓛 w.2 t₀ hw)
  -- the inverse transport is the transport along the reversed path
  have hinv : ∀ {x y : X} (γ : Path x y) v, (tr γ).symm v = tr γ.symm v := by
    intro x y γ v
    obtain ⟨u, rfl⟩ := (tr γ).surjective v
    rw [LinearEquiv.symm_apply_apply, hsymm]
  have hrange : LinearMap.range ev = S.dualAnnihilator := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      rw [Submodule.mem_dualAnnihilator]
      intro u hu
      refine (Submodule.span_le (p := LinearMap.ker (ev w))).2 ?_ hu
      intro u hu
      obtain ⟨γ, a, b, hab, rfl⟩ := pathRel_of_mem_loopSet hu
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact apply_eq_of_pathRel w.2 γ hab
    · intro φ hφ
      rw [Submodule.mem_dualAnnihilator] at hφ
      -- `φ` is invariant under the transport along loops
      have hinv' : ∀ (ℓ : Path t₀ t₀) z, φ (tr ℓ z) = φ z := by
        intro ℓ z
        have := hφ _ (Submodule.subset_span (sub_mem_loopSet ((htr ℓ z _).2 rfl)))
        rw [map_sub, sub_eq_zero] at this
        exact this.symm
      let γ : ∀ t : X, Path t₀ t := fun t ↦ PathConnectedSpace.somePath t₀ t
      let w : ∀ t : X, Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk t) :=
        fun t ↦ φ ∘ₗ (tr (γ t)).symm.toLinearMap
      have hw : w ∈ flatForms 𝓛 := by
        rw [mem_flatForms]
        intro O hO s t ht t' ht'
        have hpc : IsPathConnected (O : Set X) :=
          (O.isOpen.isConnected_iff_isPathConnected).1 ⟨⟨t, ht⟩, hO⟩
        have J := hpc.joinedIn t ht t' ht'
        have hδ := (htr _ _ _).1 (pathRel_germ s J.somePath J.somePath_mem ht ht')
        change φ ((tr (γ t)).symm _) = φ ((tr (γ t')).symm _)
        rw [← hδ]
        set z := (tr (γ t)).symm (((TopCat.Sheaf.forget _ X).obj 𝓛).germ O t ht s) with hz
        have hs : ((TopCat.Sheaf.forget _ X).obj 𝓛).germ O t ht s = tr (γ t) z := by
          rw [hz, LinearEquiv.apply_symm_apply]
        rw [hs, hinv, ← htrans, ← htrans, hinv']
      refine ⟨⟨w, hw⟩, ?_⟩
      refine LinearMap.ext fun z ↦ ?_
      change φ ((tr (γ t₀)).symm z) = φ z
      rw [← hinv' (γ t₀) ((tr (γ t₀)).symm z), LinearEquiv.apply_symm_apply]
  refine ⟨Module.Finite.of_injective ev hinj, ?_⟩
  rw [(LinearEquiv.ofInjective ev hinj).finrank_eq, (LinearEquiv.ofEq _ _ hrange).finrank_eq,
    ← (Submodule.dualQuotEquivDualAnnihilator S).finrank_eq, Subspace.dual_finrank_eq]

end FlatInvariant

/-! ### The complex points of a local-system open -/

section CurveTopology

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y}

/-- The curve `T` is the image of its closed immersion into `Y`. -/
private lemma range_curveι : Set.range (curveι T) = (T : Set Y) := by
  simp [Scheme.IdealSheafData.range_subschemeι]

/-- The curve `T` with its reduced structure is irreducible, Noetherian and of dimension one. -/
private lemma curveScheme_facts (hY : MMP.Mori.IsVariety ℂ sY)
    (hT : topologicalKrullDim (T : Set Y) = 1) :
    IrreducibleSpace (curveScheme T) ∧ topologicalKrullDim (curveScheme T) = 1 ∧
      IsNoetherian (curveScheme T) := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hY
  let e : curveScheme T ≃ₜ (T : Set Y) :=
    (curveι T).isClosedEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr range_curveι)
  haveI : IrreducibleSpace (T : Set Y) := Subtype.irreducibleSpace T.isIrreducible
  haveI : IsLocallyNoetherian (curveScheme T) :=
    LocallyOfFiniteType.isLocallyNoetherian (curveι T ≫ sY)
  haveI : CompactSpace (curveScheme T) :=
    QuasiCompact.compactSpace_of_compactSpace (curveι T ≫ sY)
  refine ⟨e.symm.surjective.irreducibleSpace e.symm.continuous, ?_, ⟨⟩⟩
  exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).trans hT

/-- A local-system open is a smooth curve over `ℂ` with connected, locally path connected
complex realization. -/
private lemma isLocalSystemOpen_facts (hY : MMP.Mori.IsVariety ℂ sY)
    (hT : topologicalKrullDim (T : Set Y) = 1) {W : (curveScheme T).Opens}
    (hW : IsLocalSystemOpen sY W) :
    AlgebraicGeometry.IsVariety ℂ (W.ι ≫ curveι T ≫ sY) ∧
      SmoothOfRelativeDimension 1 (W.ι ≫ curveι T ≫ sY) ∧
      ConnectedSpace (analyticSpace (W.ι ≫ curveι T ≫ sY)) ∧
      LocallyPathConnectedSpace (analyticSpace (W.ι ≫ curveι T ≫ sY)) := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hY
  obtain ⟨hirr, hdim, hnoeth⟩ := curveScheme_facts hY hT
  haveI := hnoeth
  haveI : Smooth (W.ι ≫ curveι T ≫ sY) := hW.smooth
  haveI : ConnectedSpace W := hW.connectedSpace
  haveI : IsIntegral W :=
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (W.ι ≫ curveι T ≫ sY)
  haveI hV : AlgebraicGeometry.IsVariety ℂ (W.ι ≫ curveι T ≫ sY) :=
    { toIsIntegral := inferInstance, toIsSeparated := inferInstance,
      toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
  haveI : Nonempty W := hW.connectedSpace.toNonempty
  obtain ⟨w⟩ := ‹Nonempty W›
  have hdimW : topologicalKrullDim W = 1 :=
    ((AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ (curveScheme T) (curveι T ≫ sY)
      (W : Set (curveScheme T)) W.isOpen ⟨w.1, w.2⟩).symm.trans hdim)
  exact ⟨hV, MMP.Intersection.smoothOfRelativeDimension_of_isVariety _ 1 hdimW,
    MMP.Fourfold.connectedSpace_analyticSpace _,
    MMP.Fourfold.locallyPathConnectedSpace_analyticSpace _⟩

end CurveTopology

section CurveRank

variable {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}

/-- The resolution `r` is surjective: it is proper and dominant. -/
private theorem surjective_base (hM : IsCurvePointExceptionalModel sY r F D) :
    Function.Surjective r.base := by
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
  haveI : IsDominant r := MMP.Mori.IsBirationalMorphism.isDominant hM.isResolution.2.2.2.2
  have h := r.denseRange.closure_range
  rw [r.isClosedMap.isClosed_range.closure_eq] at h
  exact Set.range_eq_univ.1 h

/-- The curves `T ⊆ Sing Y` are finitely many: each is the image of a component of `F`. -/
private theorem finite_curves (hM : IsCurvePointExceptionalModel sY r F D) :
    Finite {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
      topologicalKrullDim (T : Set Y) = 1} := by
  classical
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
  let K : Mori.PrimeDivisor Z → Set Y := fun E ↦ r.base '' (E.support : Set Z)
  have hKcl : ∀ E : Mori.PrimeDivisor Z, IsClosed (K E) := fun E ↦ r.isClosedMap _ (by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure)
  have hKirr : ∀ E : Mori.PrimeDivisor Z, IsIrreducible (K E) := fun E ↦ by
    refine IsIrreducible.image ?_ _ r.continuous.continuousOn
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  -- every singular curve is the image of a component of `F`
  have hmem : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
      topologicalKrullDim (T : Set Y) = 1}, ∃ E ∈ F.support, K E = T.1 := by
    intro T
    have hsub : (T.1 : Set Y) ⊆ ⋃₀ ((F.support.image K : Finset (Set Y)) : Set (Set Y)) := by
      intro y hy
      obtain ⟨z, rfl⟩ := surjective_base hM y
      have hz : z ∈ (F.supp : Set Z) := by
        rw [hM.supp_eq_preimage_singularLocus]; exact T.2.1 hy
      rw [DivisorWithCoeffs.coe_supp] at hz
      obtain ⟨E, hE, hzE⟩ := Set.mem_iUnion₂.1 hz
      exact Set.mem_sUnion.2 ⟨K E, Finset.mem_coe.2 (Finset.mem_image_of_mem K hE), z, hzE, rfl⟩
    obtain ⟨S, hS, hTS⟩ := (isIrreducible_iff_sUnion_isClosed.1 T.1.isIrreducible)
      (F.support.image K) (fun S hS ↦ by
        obtain ⟨E, -, rfl⟩ := Finset.mem_image.1 hS
        exact hKcl E) hsub
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.1 hS
    refine ⟨E, hE, ?_⟩
    by_contra hne
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne (hKirr E) T.1.isClosed
      hTS (Ne.symm hne) (ne_top_of_le_ne_top (by decide) (hM.topologicalKrullDim_image_le E hE))
    rw [T.2.2] at hlt
    exact absurd (hlt.trans_le (hM.topologicalKrullDim_image_le E hE)) (lt_irrefl _)
  choose e he he' using hmem
  refine Finite.of_injective (fun T ↦ (⟨e T, he T⟩ : F.support)) fun T T' h ↦ ?_
  have h' : e T = e T' := congrArg Subtype.val h
  exact Subtype.ext (SetLike.coe_injective ((he' T).symm.trans (h' ▸ he' T')))

/-- The flat families of forms on `𝒱_T` form a finite-dimensional space. -/
private theorem finite_flatForms (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (hdim : topologicalKrullDim (T : Set Y) = 1)
    {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY r To) :
    Module.Finite ℚ (flatForms (curveLocalSystem sY To)) := by
  obtain ⟨-, -, hconn, hlpc⟩ := isLocalSystemOpen_facts hM.isResolution.1 hdim
    hTo.toIsLocalSystemOpen
  haveI := hlpc
  haveI : PathConnectedSpace (analyticSpace (To.ι ≫ curveι T ≫ sY)) :=
    pathConnectedSpace_iff_connectedSpace.2 hconn
  obtain ⟨t₀⟩ := hconn.toNonempty
  exact (finite_and_finrank_flatForms hTo.isLocalSystem t₀).1

/-- **The dimension of the monodromy-invariant forms** is the rank `b_T`. -/
private theorem finrank_flatForms (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hdim : topologicalKrullDim (T : Set Y) = 1)
    {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY r To) :
    Module.finrank ℚ (flatForms (curveLocalSystem sY To)) = curveLocalSystemRank sY To := by
  obtain ⟨-, -, hconn, hlpc⟩ := isLocalSystemOpen_facts hM.isResolution.1 hdim
    hTo.toIsLocalSystemOpen
  haveI := hlpc
  haveI : PathConnectedSpace (analyticSpace (To.ι ≫ curveι T ≫ sY)) :=
    pathConnectedSpace_iff_connectedSpace.2 hconn
  obtain ⟨t₀⟩ := hconn.toNonempty
  exact (finite_and_finrank_flatForms hTo.isLocalSystem t₀).2.trans
    ((IsLocalSystemOpen.curveLocalSystemRank_eq hM.isResolution.1 hM.topologicalKrullDim_eq
      hdim hT hTo.toIsLocalSystemOpen hTo.toIsLocalSystemOpen).2 t₀).symm

end CurveRank

end LocalSystems

section Injectivity

open MMP.Analytic MMP.Analytic.ComplexPoints Opposite CategoryTheory.Limits

/-- The restriction of a family in a product of submodules to the indices satisfying `p`. -/
private noncomputable def projSubtype {ι : Type*} {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℚ (V i)] (N : ∀ i, Submodule ℚ (V i)) (p : ι → Prop) :
    Submodule.pi Set.univ N →ₗ[ℚ] ∀ i : {i // p i}, N i.1 :=
  LinearMap.pi fun i => LinearMap.codRestrict (N i.1)
    ((LinearMap.proj i.1) ∘ₗ (Submodule.pi Set.univ N).subtype) fun m => m.2 i.1 trivial

/-- A subspace on which a linear map to a finite-dimensional space has no kernel has dimension at
most that of the target. -/
private theorem finrank_le_of_forall_mem {V V' : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup V'] [Module ℚ V'] [FiniteDimensional ℚ V'] (W : Submodule ℚ V)
    (ψ : V →ₗ[ℚ] V') (h : ∀ x ∈ W, ψ x = 0 → x = 0) :
    Module.finrank ℚ W ≤ Module.finrank ℚ V' := by
  refine LinearMap.finrank_le_finrank_of_injective (f := ψ ∘ₗ W.subtype) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  exact fun x hx => Subtype.ext (h x.1 x.2 hx)

variable {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}

/-- The cycle associated to a closed subscheme with no points is zero. -/
private theorem cycleAssociatedToClosedSubscheme_eq_zero_of_isEmpty {X W : Scheme.{0}}
    {f : X ⟶ Spec (.of ℂ)} {hf : LocallyOfFiniteType f} {i : W ⟶ X} {hi : IsClosedImmersion i}
    (hW : IsEmpty W) {k : ℤ} :
    @Stacks.Chow.cycleAssociatedToClosedSubscheme (Stacks.Chow.fieldChowSituation ℂ) X W f hf i
      hi k = 0 :=
  Subtype.ext (Function.locallyFinsuppWithin.ext fun x =>
    Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero (Stacks.Chow.fieldChowSituation ℂ)
      f i k x fun h => isEmptyElim h.choose.1)

/-- The fibre of a morphism over a point outside its image is empty. -/
private theorem isEmpty_pullback_of_forall_ne {X : Scheme.{0}} (f₀ : X ⟶ Y)
    (g : Spec (.of ℂ) ⟶ Y) (h : ∀ x, f₀.base x ≠ g.base (IsLocalRing.closedPoint ℂ)) :
    IsEmpty (pullback f₀ g : Scheme.{0}) := ⟨fun z => by
  have hz := congrArg (fun k => k.base z) (pullback.condition (f := f₀) (g := g))
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hz
  exact h _ (hz.trans (congrArg _ (Subsingleton.elim _ _)))⟩

/-- The cycle cut on the fibre `F_t` by a tuple `L` of `ℚ`-divisors on the components of `F`:
the sum of the curve cycles `[P ×_Y t]_1` of the closed subschemes `P ×_Y t ⊆ F_t`. -/
private noncomputable def fibreCurveCycle (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (F : Divisor Z)
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme) {T : IrreducibleCloseds Y}
    (U : (curveScheme T).Opens) (t : ComplexPoints (U.ι ≫ curveι T ≫ sY))
    [IsComplexScheme (pointFibre sY r U t)] :
    Chow.RationalCycleGroup (Stacks.Chow.fieldChowSituation ℂ)
      (pointFibre sY r U t ↘ Spec (.of ℂ)) (1 : ℕ) :=
  ∑ E : F.support, ∑ P ∈ (L E).support, (L E) P •
    (1 : ℚ) ⊗ₜ[ℤ] @Stacks.Chow.cycleAssociatedToClosedSubscheme
      (Stacks.Chow.fieldChowSituation ℂ) _ _ (pointFibre sY r U t ↘ Spec (.of ℂ)) _
      (pullback.map (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι ≫ r)
        (t.hom ≫ U.ι ≫ curveι T) r (t.hom ≫ U.ι ≫ curveι T)
        (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) (𝟙 _) (𝟙 _)
        ((Category.comp_id _).trans (Category.assoc _ _ _).symm)
        ((Category.comp_id _).trans (Category.id_comp _).symm))
      (isClosedImmersion_pullback_map_of_comp_eq
        (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) r (Category.assoc _ _ _)
        (t.hom ≫ U.ι ≫ curveι T)) ((1 : ℕ) : ℤ)

/-- A tuple of `ℚ`-divisors whose prime divisors all map into `Q` cuts the zero cycle on the
fibres over the points of a curve `T ⊄ Q` outside `Q`. -/
private theorem exists_dense_fibreCurveCycle_eq_zero_of_not_subset
    (hM : IsCurvePointExceptionalModel sY r F D)
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme) (Q : Set Y) (hQ : IsClosed Q)
    (hLQ : ∀ E : F.support, ∀ P ∈ (L E).support,
      r.base '' (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)) ⊆ Q)
    (T : IrreducibleCloseds Y) (hT1 : topologicalKrullDim (T : Set Y) = 1)
    (hTQ : ¬ (T : Set Y) ⊆ Q) :
    ∃ U : (curveScheme T).Opens, Dense (U : Set (curveScheme T)) ∧
      ∀ (t : ComplexPoints (U.ι ≫ curveι T ≫ sY)) [IsComplexScheme (pointFibre sY r U t)],
        fibreCurveCycle sY r F L U t = 0 := by
  classical
  have hY : MMP.Mori.IsVariety ℂ sY := hM.isProjectiveVariety.toIsVariety
  obtain ⟨hirr, -, -⟩ := curveScheme_facts hY hT1
  let U : (curveScheme T).Opens :=
    ⟨(curveι T).base ⁻¹' Qᶜ, hQ.isOpen_compl.preimage (curveι T).continuous⟩
  refine ⟨U, ?_, fun t _ => ?_⟩
  · obtain ⟨y, hyT, hyQ⟩ := Set.not_subset.1 hTQ
    have hy : y ∈ Set.range (curveι T).base := by rw [range_curveι]; exact hyT
    obtain ⟨x, rfl⟩ := hy
    exact U.isOpen.dense ⟨x, hyQ⟩
  rw [fibreCurveCycle]
  refine Finset.sum_eq_zero fun E _ => Finset.sum_eq_zero fun P hP => ?_
  have hW := isEmpty_pullback_of_forall_ne
    (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι ≫ r) (t.hom ≫ U.ι ≫ curveι T)
    fun x hx => by
      have h1 : r.base (E.1.idealSheaf.subschemeι.base (P.idealSheaf.subschemeι.base x)) ∈ Q :=
        hLQ E P hP ⟨_, ⟨_, (Scheme.IdealSheafData.range_subschemeι _).subset ⟨_, rfl⟩, rfl⟩, rfl⟩
      have h2 : U.ι.base (t.hom.base (IsLocalRing.closedPoint ℂ)) ∈ (U : Set _) := by
        rw [← Scheme.Opens.range_ι]; exact ⟨_, rfl⟩
      have hx' : r.base (E.1.idealSheaf.subschemeι.base (P.idealSheaf.subschemeι.base x)) =
          (curveι T).base (U.ι.base (t.hom.base (IsLocalRing.closedPoint ℂ))) := hx
      exact h2 (hx' ▸ h1)
  refine Eq.trans (congrArg (fun c => (L E) P • ((1 : ℚ) ⊗ₜ[ℤ] c))
    (cycleAssociatedToClosedSubscheme_eq_zero_of_isEmpty hW)) ?_
  simp only [TensorProduct.tmul_zero, smul_zero]

/-- The transport of classes from `X(ℂ)` to the complex realization is injective. -/
private theorem pushforward_homeomorphUnderlyingSpace_injective {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] (n : ℕ) :
    Function.Injective (MMP.borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace (X := X).symm.continuous⟩)
      ComplexPoints.homeomorphUnderlyingSpace.symm.isProperMap n).hom := by
  intro a b hab
  let e := ComplexPoints.homeomorphUnderlyingSpace (X := X)
  let g : TopCat.of (ComplexPoints (X ↘ Spec (.of ℂ))) ⟶ TopCat.of (UnderlyingSpace ℂ X) :=
    TopCat.ofHom ⟨e, e.continuous⟩
  have hab' := congrArg (MMP.borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
    g e.isProperMap n).hom hab
  have hid : (TopCat.ofHom ⟨_, e.symm.continuous⟩ ≫ g) = 𝟙 _ :=
    TopCat.ext e.apply_symm_apply
  rw [MMP.borelMooreHomology.pushforward_comp_apply ℚ _ g _ _
      (hid ▸ isProperMap_id),
    MMP.borelMooreHomology.pushforward_comp_apply ℚ _ g _ _
      (hid ▸ isProperMap_id),
    MMP.borelMooreHomology.pushforward_id_apply' ℚ _ _ hid,
    MMP.borelMooreHomology.pushforward_id_apply' ℚ _ _ hid] at hab'
  exact hab'

/-- An injective additive map commutes with `finsum`, whether or not the support is finite. -/
private theorem map_finsum_of_injective {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℚ M] [Module ℚ N] (f : M →ₗ[ℚ] N) (hf : Function.Injective f) (g : ι → M) :
    f (∑ᶠ i, g i) = ∑ᶠ i, f (g i) :=
  f.toAddMonoidHom.map_finsum_of_injective hf g

/-- A tuple of `ℚ`-divisors whose curve classes on the fibres over `T°` pair to zero with every
class near the fibre, for all but finitely many `t`, cuts a fibre cycle with zero class over a
dense open of `T`. -/
private theorem exists_dense_rationalCycleClass_eq_zero_of_capProduct
    (hM : IsCurvePointExceptionalModel sY r F D)
    (T₀ : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
        topologicalKrullDim (T : Set Y) = 1}, (curveScheme T.1).Opens)
    (hT₀ : ∀ T, IsAdaptedOpen sY r (T₀ T))
    (T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
        topologicalKrullDim (T : Set Y) = 1})
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    (hL : ∀ᶠ t : analyticSpace ((T₀ T).ι ≫ curveι T.1 ≫ sY) in Filter.cofinite,
      ∃ _ : IsComplexScheme (pointFibre sY r (T₀ T) t),
      ∀ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY (T₀ T) t ∈ V)
        (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
        (p : pointFibre sY r (T₀ T) t)
        (_ : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
          (pointFibre sY r (T₀ T) t ↘ Spec (.of ℂ)) p = (0 : ℕ)),
        borelMooreHomology.capProduct ℚ
            (analyticSpace (pointFibre sY r (T₀ T) t ↘ Spec (.of ℂ))) Set.univ 2 2
            ((rationalCohomologyMap (pointFibreInclusion sY r (T₀ T) t hV) 2).hom α)
            (∑ E : F.support, (L E).sum fun P c ↦ c •
              ∑ᶠ (C : {x : pointFibre sY r (T₀ T) t // Stacks.Chow.relativeDimension
                  (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                  (pointFibre sY r (T₀ T) t ↘ Spec (.of ℂ)) x = (1 : ℕ)})
                (_ : Maximal (fun A : Set (pointFibre sY r (T₀ T) t) ↦ IsIrreducible A ∧
                  A ⊆ (pointFibreFst sY r (T₀ T) t).base ⁻¹'
                    (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
                  (closure {C.1})),
                fundamentalClass C.1 C.2) = 0) :
    ∃ U : (curveScheme T.1).Opens, Dense (U : Set (curveScheme T.1)) ∧
      ∀ (t : ComplexPoints (U.ι ≫ curveι T.1 ≫ sY)) [IsComplexScheme (pointFibre sY r U t)],
        Chow.rationalCycleClass (pointFibre sY r U t) 1 (fibreCurveCycle sY r F L U t) = 0 := by
  classical
  refine hM.exists_dense_rationalCycleClass_fibreCycle_eq_zero T₀ hT₀ T L ?_
  filter_upwards [hL] with t ht
  obtain ⟨inst, ht⟩ := ht
  refine ⟨inst, ?_⟩
  have hw := hM.eq_zero_of_capProduct_restrict_eq_zero T₀ T t _ ht
  refine pushforward_homeomorphUnderlyingSpace_injective (2 * 1) ?_
  rw [map_zero]
  refine Eq.trans ?_ hw
  rw [map_sum]
  refine Finset.sum_congr rfl fun E _ => ?_
  simp only [Finsupp.sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [map_smul]
  congr 1
  refine (map_finsum_of_injective _
    (pushforward_homeomorphUnderlyingSpace_injective (X := pointFibre sY r (T₀ T) t) (2 * 1))
    _).trans (finsum_congr fun C => ?_)
  rw [finsum_eq_if, finsum_eq_if]
  split_ifs
  · rfl
  · exact map_zero _

/-- A class of `K(r)` with a representative over `Q` has a tuple of `ℚ`-divisor representatives
all of whose prime divisors map into `Q`. -/
private theorem exists_divisor_rep_of_mem
    (hM : IsCurvePointExceptionalModel sY r F D) (hdim : topologicalKrullDim Z = 4) (Q : Set Y)
    {x : ComponentHomology F}
    (hx : x ∈ exceptionalKernel F fun E =>
      (cyclesMappingInto (E.1.idealSheaf.subschemeι ≫ r) 2 Q).map (Chow.rationalCycleClass _ 2)) :
    ∃ L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme,
      (∀ E, Chow.divisorClass E.1.idealSheaf.subscheme (L E) = x E) ∧
      ∀ E : F.support, ∀ P ∈ (L E).support,
        r.base '' (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)) ⊆ Q := by
  have : IsIntegral Z :=
    (hM.isResolution.2.1 : AlgebraicGeometry.IsVariety ℂ (r ≫ sY)).toIsIntegral
  obtain ⟨hx1, -⟩ := (mem_exceptionalKernel F).1 hx
  choose c hc hcx using fun E => Submodule.mem_map.1 (hx1 E)
  choose L hL hLs using fun E : F.support => exists_divisorCycle_eq hdim E.1 (c E)
  refine ⟨L, fun E => ?_, fun E P hP => ?_⟩
  · rw [← hcx E, ← hL E]
    rfl
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← Set.image_comp]
    exact hc E _ (hLs E P hP)

end Injectivity

/-- The bound `dim ≤ ∑_{T ⊆ Q} b_T` for the subspace of `K(r)/B(r)` of the classes with
representatives all of whose surfaces map into `Q`: the injective generic defect map has zero
coordinates at the curves `T ⊄ Q`. -/
private theorem finrank_algebraicDefectOver_le
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D) (hdim : topologicalKrullDim Z = 4) (Q : Set Y)
    (hQ : IsClosed Q)
    (To : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
        topologicalKrullDim (T : Set Y) = 1}, (curveScheme T.1).Opens)
    (hTo : ∀ T, IsLocalSystemOpen sY (To T)) :
    Module.finrank ℚ ((((exceptionalKernel F fun E =>
        (cyclesMappingInto (E.1.idealSheaf.subschemeι ≫ r) 2 Q).map
          (Chow.rationalCycleClass _ 2)).comap (algebraicKernel F).subtype).map
        (Submodule.mkQ _)) : Submodule ℚ (AlgebraicDefect F)) ≤
      ∑ᶠ (T) (_ : (T.1 : Set Y) ⊆ Q), curveLocalSystemRank sY (To T) := by
  have : FiniteDimensional ℚ (ComponentHomology F) :=
    finiteDimensional_componentHomology hM.comp_eq hM.isProjectiveVariety hM.isResolution
  obtain ⟨T₀, hT₀, hΦ⟩ := hM.exists_linearMap_curveLocalSystemDual
  have hrank : ∀ T, curveLocalSystemRank sY (T₀ T) = curveLocalSystemRank sY (To T) := fun T =>
    (IsLocalSystemOpen.curveLocalSystemRank_eq hM.isProjectiveVariety.toIsVariety
      hM.topologicalKrullDim_eq T.2.2 T.2.1 (hT₀ T).toIsLocalSystemOpen (hTo T)).1
  by_cases hall : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
      topologicalKrullDim (T : Set Y) = 1}, (T.1 : Set Y) ⊆ Q
  · -- every singular curve lies in `Q`: the total bound of the generic defect map
    have hsum : ∑ᶠ (T) (_ : (T.1 : Set Y) ⊆ Q), curveLocalSystemRank sY (To T) =
        ∑ᶠ T, curveLocalSystemRank sY (T₀ T) :=
      finsum_congr fun T => by classical rw [finsum_eq_if, if_pos (hall T), hrank]
    rw [hsum]
    exact (Submodule.finrank_le _).trans
      ((hM.mem_orientedSurfaceClasses_and_finrank_le).2 T₀ hT₀)
  · -- the generic defect map, restricted to the curves in `Q`, is injective on the classes
    -- represented over `Q`
    classical
    haveI := finite_curves hM
    letI := Fintype.ofFinite {T : IrreducibleCloseds Y //
      (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧ topologicalKrullDim (T : Set Y) = 1}
    obtain ⟨Φ, hpin, -⟩ := hΦ T₀ fun T => ⟨le_rfl, hT₀ T⟩
    let S := {T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
        topologicalKrullDim (T : Set Y) = 1} // (T.1 : Set Y) ⊆ Q}
    haveI : ∀ T : S, Module.Finite ℚ (flatForms (curveLocalSystem sY (T₀ T.1))) :=
      fun T => finite_flatForms hM T.1.2.2 (hT₀ T.1)
    let ψ : AlgebraicDefect F →ₗ[ℚ] ∀ T : S, flatForms (curveLocalSystem sY (T₀ T.1)) :=
      projSubtype (fun T => flatForms (curveLocalSystem sY (T₀ T)))
        (fun T => (T.1 : Set Y) ⊆ Q) ∘ₗ Φ
    refine (finrank_le_of_forall_mem _ ψ ?_).trans_eq ?_
    · intro x hx hψ0
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      obtain ⟨L, hL, hLQ⟩ := exists_divisor_rep_of_mem hM hdim Q hy
      have hsum : ∑ E : F.support, componentHomologyMap E.1 4
          (Chow.divisorClass E.1.idealSheaf.subscheme (L E)) = 0 := by
        simp_rw [hL]
        exact ((mem_exceptionalKernel F).1 y.2).2
      have hB := (hM.mem_orientedSurfaceClasses_and_finrank_le).1 L hsum fun T hT hT1 => by
        by_cases hTQ : (T : Set Y) ⊆ Q
        · have h0 : (Φ (Submodule.Quotient.mk y)).1 ⟨T, hT, hT1⟩ = 0 :=
            congrArg (fun f => (f ⟨⟨T, hT, hT1⟩, hTQ⟩).1) hψ0
          obtain ⟨U, hU, hU'⟩ := exists_dense_rationalCycleClass_eq_zero_of_capProduct hM T₀ hT₀
            ⟨T, hT, hT1⟩ L (by
              filter_upwards [hpin ⟨T, hT, hT1⟩ y L hL] with t ht
              obtain ⟨inst, ht⟩ := ht
              exact ⟨inst, fun V hV α p hp => by rw [ht V hV α p hp, h0]; exact zero_smul ℚ _⟩)
          exact ⟨U, hU, fun t _ => hU' t⟩
        · obtain ⟨U, hU, hU'⟩ :=
            exists_dense_fibreCurveCycle_eq_zero_of_not_subset hM L Q hQ hLQ T hT1 hTQ
          refine ⟨U, hU, fun t _ => ?_⟩
          change Chow.rationalCycleClass _ 1 (fibreCurveCycle sY r F L U t) = 0
          rw [hU' t, map_zero]
      rw [Submodule.mem_comap, Submodule.coe_subtype]
      convert hB using 1
      exact funext fun E => (hL E).symm
    · rw [Module.finrank_pi_fintype, ← finsum_eq_sum_of_fintype]
      refine (finsum_congr fun T : S =>
        (finrank_flatForms hM T.1.2.1 T.1.2.2 (hT₀ T.1)).trans (hrank T.1)).trans ?_
      exact finsum_subtype_eq_finsum_cond (M := ℕ)
        (f := fun T => curveLocalSystemRank sY (To T)) (fun T => (T.1 : Set Y) ⊆ Q)

/-- The dimension bound `dim D_{v,Q}(r) ≤ ∑_{T ⊆ Sing Y ∩ Q} b_T`. -/
private theorem finrank_verticalDefectOver_le [Y.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y}
    [r.IsOver (Spec (.of ℂ))] [IsProper r] {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D) (hdim : topologicalKrullDim Z = 4)
    (Q : Set Y) (hQ : IsClosed Q)
    (To : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
        topologicalKrullDim (T : Set Y) = 1}, (curveScheme T.1).Opens)
    (hTo : ∀ T, IsLocalSystemOpen sY (To T)) :
    Module.finrank ℚ (verticalDefectOver r F Q) ≤
      ∑ᶠ (T) (_ : (T.1 : Set Y) ⊆ Q), curveLocalSystemRank sY (To T) := by
  rw [verticalDefectOver, finrank_map_mkQ_congr (verticalKernel_eq_algebraicKernel hM hdim)
    (verticalSurfaceClasses_eq_orientedSurfaceClasses hM) (verticalKernelOver_eq hM Q)]
  exact finrank_algebraicDefectOver_le hM hdim Q hQ To hTo

end Proof_lem_mmp_conductor_vertical_defect_spaces

end

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP
open MMP.Mori

namespace MMP.Fourfold

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
  [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **Finite-dimensionality and the curve-model specialization.** Let `r : Z ⟶ Y` be a projective
resolution of a normal projective `ℚ`-factorial complex fourfold `Y` whose exceptional locus is
the support of a reduced snc divisor `F`. Then `⨁ᵢ H_4(Fᵢ, ℚ)` is finite-dimensional over `ℚ`
(hence so are `K_v(r)`, `B_v(r)`, `D_v(r)` and `D_{v,Q}(r)`), and
`B_v(r) ⊆ K_v(r)` (`MMP.Fourfold.verticalSurfaceClasses`, `MMP.Fourfold.verticalKernel`). If
moreover `r` is a curve-and-point exceptional model, then `K_v(r) = K(r)` and `B_v(r) = B(r)`
(`MMP.Fourfold.algebraicKernel`, `MMP.Fourfold.orientedSurfaceClasses`), and for every closed
`Q ⊆ Y` and every choice of local-system opens `T°` of the curves `T ⊆ Sing Y`,
`dim D_{v,Q}(r) ≤ ∑_{T ⊆ Sing Y ∩ Q} b_T` (`MMP.Fourfold.verticalDefectOver`,
`MMP.Fourfold.curveLocalSystemRank`). -/
@[mmp "lem_mmp_conductor_vertical_defect_spaces"]
public theorem finiteDimensional_componentHomology_and_verticalDefect
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F : Divisor Z}
    (hcomp : r ≫ sY = Z ↘ Spec (.of ℂ))
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hQ : IsQFactorial sY)
    (hres : MMP.Intersection.IsResolution sY r)
    (hdim : topologicalKrullDim Z = 4)
    (hred : MMP.Intersection.IsReducedEffective F)
    (hsnc : DivisorWithCoeffs.IsSNC (r ≫ sY) F)
    (hex : (F.supp : Set Z) = exceptionalSet r) :
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := hY.toIsVariety.toLocallyOfFiniteType
    haveI : r.IsOver (Spec (.of ℂ)) := ⟨hcomp⟩
    haveI : IsProper r := isProper_of_isProjectiveMorphism r hres.2.2.2.1
    FiniteDimensional ℚ (ComponentHomology F) ∧
      verticalSurfaceClasses r F ≤ verticalKernel r F ∧
      ∀ D : Divisor Z, IsCurvePointExceptionalModel sY r F D →
        verticalKernel r F = algebraicKernel F ∧
        verticalSurfaceClasses r F = orientedSurfaceClasses F ∧
        ∀ Q : Set Y, IsClosed Q →
        ∀ To : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
            topologicalKrullDim (T : Set Y) = 1}, (curveScheme T.1).Opens,
          (∀ T, IsLocalSystemOpen sY (To T)) →
          Module.finrank ℚ (verticalDefectOver r F Q) ≤
            ∑ᶠ (T) (_ : (T.1 : Set Y) ⊆ Q), curveLocalSystemRank sY (To T) := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := hY.toIsVariety.toLocallyOfFiniteType
  haveI : r.IsOver (Spec (.of ℂ)) := ⟨hcomp⟩
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hres.2.2.2.1
  open Proof_lem_mmp_conductor_vertical_defect_spaces in
  exact ⟨finiteDimensional_componentHomology hcomp hY hres,
    verticalSurfaceClasses_le_verticalKernel hres hdim,
    fun D hM => ⟨verticalKernel_eq_algebraicKernel hM hdim,
      verticalSurfaceClasses_eq_orientedSurfaceClasses hM,
      fun Q hQc To hTo => finrank_verticalDefectOver_le hM hdim Q hQc To hTo⟩⟩

end MMP.Fourfold
