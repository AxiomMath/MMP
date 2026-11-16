module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
public import MMP.AlgebraicGeometry.MMP.Surface.FloorSectionExtension
public import MMP.AlgebraicGeometry.MMP.Surface.SemiampleFloorLowering
public import MMP.AlgebraicGeometry.MMP.Surface.TrivialAdjointFloorExtension
public import MMP.RingTheory.Kaehler.PluriformProduct
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
public import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStratum
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.RingTheory.RegularLocalRing.FiniteFreeResolution
public import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
public import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
public import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
public import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
public import MMP.AlgebraicGeometry.Resolution.StratumBlowupRelativelyAmple
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.MMP.Abundance.Curve.AdmissibleSectionsGenerate
public import MMP.AlgebraicGeometry.Singularities.CyclicQuotientDifferent
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Valuation
public import MMP.AlgebraicGeometry.Resolution.Surface.CastelnuovoContraction
public import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.Positivity.RelativeBigDecomposition
public import MMP.AlgebraicGeometry.Morphisms.GenericallyFinite
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Singularities.Semismooth.Basic
public import MMP.AlgebraicGeometry.MMP.Surface.AdjointAmpleModel
public import MMP.AlgebraicGeometry.Singularities.DltFloor.SteinImage
public import MMP.AlgebraicGeometry.MMP.Fourfold.Preadmissible.SteinFloorLifting
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceZero
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Projective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
public import MMP.AlgebraicGeometry.MMP.Contraction.SemiampleSupportingDivisor
public import MMP.AlgebraicGeometry.Resolution.CommonLogResolution
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.MMP.Surface.MoriFibreSpaceOverCurve
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferentEffective
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
public import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization
public import MMP.AlgebraicGeometry.MMP.Contraction.KltRayContraction
public import MMP.AlgebraicGeometry.Morphisms.HProjective
public import MMP.AlgebraicGeometry.StalkValuationRing
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import MMP.AlgebraicGeometry.Modules.FiniteLocallyFreeRankOne
import MMP.AlgebraicGeometry.Normalization.IntegralScheme
public import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField

/-!
# Preadmissible generation for semiample dlt surfaces

Let `(S_i, B_i)`, `i ∈ I`, be a finite collection of `ℚ`-factorial projective dlt pairs on
complex surfaces whose adjoints `K_{S_i} + B_i` are semiample. Then there is `m₀ > 0` such that
in every positive even degree `m` divisible by `m₀` the preadmissible section systems
`(s_i) ∈ ⊕ᵢ H⁰(S_i, m(K_{S_i} + B_i))` — those whose residue restrictions to the proper strata
(the components of the floors `⌊B_i⌋` and their points of intersection with the other floor
components) correspond under every crepant birational map between their adjunction pairs —
generate every `𝒪_{S_i}(m(K_{S_i} + B_i))`: at every point `x` of every `S_i` some
preadmissible system has its `i`-th section nonvanishing at `x`. No compatibility of the
whole surfaces with one another is required.

## Main results

* `MMP.Fourfold.exists_generatesOn_of_mem_preadmissibleSections`: preadmissible generation in
  all sufficiently divisible even degrees.

## Implementation notes

"Rational pair" is `MMP.Fourfold.IsPair`, "dlt" is `MMP.Intersection.IsDltPair`,
"rational-factorial" is `MMP.Fourfold.IsQFactorial`, and semiampleness of the adjoint is
`MMP.Fourfold.QDivisor.IsRelativelySemiample` over `Spec ℂ` for `K_{S_i} + B_i`, `K_{S_i}` a
canonical divisor. The residue restriction maps of the source are canonical; here they are a
structure `MMP.Fourfold.ResidueRestriction` on the collection in degree `m`, and the theorem
asserts that one exists in every degree it speaks of, and that the preadmissible systems
`MMP.Fourfold.preadmissibleSections` of every such structure generate. A section `s_i` generates
`𝒪_{S_i}(m(K_{S_i} + B_i))` near `x` when it is a local generator on an open neighbourhood of `x`
(`MMP.Mori.GeneratesOn`).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP MMP.Fourfold
open MMP.Mori hiding IsPair

namespace Proof_thm_mmp_surface_semiample_dlt_preadmissible_generation

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

open scoped WithZero

/-! ### Crepant identifications of floor models -/

open MMP.Threefold.Mori.Helpers MMP.Threefold.Mori.ModelIndependence in
/-- **Orders of pulled-back forms along a valuation.** Let `σ : k(X') ≅ k(X)`, `Γ` a prime
divisor of `X` and `(Y, f, E)` a divisor over `X'` whose valuation is `v_Γ ∘ σ`. Then
`ord_Γ(σ^* τ) = ord_E(f^* τ)`: the isomorphism `φ = σ ∘ (f^*)⁻¹ : k(Y) → k(X)` carries `v_E` to
`v_Γ`, hence `𝒪_{Y,E}` onto `𝒪_{X,Γ}`, and `σ^* = φ^* ∘ f^*`. -/
private theorem ordForm_pluriformPullback_eq_ordPullback {k : Type u} [Field k] [CharZero k]
    {X X' : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (hX' : IsNormalVariety k sX') {n : ℕ} (hn : topologicalKrullDim X = n)
    (hn' : topologicalKrullDim X' = n)
    (σ : FunctionFieldEquiv sX sX') (Γ : MMP.Mori.PrimeDivisor X) (D : DivisorOver k sX')
    (hv : ∀ g : X'.functionField, D.valuation g = Γ.divisorialValuation ((σ.toHom) g))
    {m : ℤ} (τ : RationalPluriForms sX' n m) :
    Γ.ordForm (pluriformPullback sX sX' σ.toHom n m τ) = D.ordPullback τ := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (D.f ≫ sX') := D.isNormalVariety.1.toLocallyOfFiniteType
  let A := functionFieldAlgebra sX
  let A' := functionFieldAlgebra sX'
  let AY := functionFieldAlgebra (D.f ≫ sX')
  let Af := functionFieldMapAlgebra D.f
  have hT1 := isScalarTower_functionFieldMap sX' D.f
  have hb := D.isBirationalMorphism.functionFieldMap_bijective
  let F := RingEquiv.ofBijective _ hb
  let φ : D.Y.functionField →+* X.functionField := (σ.toHom).toRingHom.comp F.symm.toRingHom
  have hφ : ∀ g, φ (functionFieldMap D.f g) = (σ.toHom) g := fun g => by
    change (σ.toHom) (F.symm (F g)) = _
    rw [F.symm_apply_apply]
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨g, rfl⟩ := σ.surjective z
    exact ⟨functionFieldMap D.f g, hφ g⟩
  have hval : ∀ y : D.Y.functionField,
      Γ.divisorialValuation (φ y) = D.E.divisorialValuation y := by
    intro y
    obtain ⟨g, rfl⟩ := hb.2 y
    rw [hφ g, ← hv g]
    rfl
  have hord : ∀ y : D.Y.functionField,
      X.ord (φ y) Γ.genericPoint = D.Y.ord y D.E.genericPoint := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp [Scheme.ord_zero]
    · have hey : φ y ≠ 0 := (map_ne_zero φ).mpr hy
      have h1 := hval y
      rw [Γ.divisorialValuation_eq_exp_neg_ord hey, D.E.divisorialValuation_eq_exp_neg_ord hy,
        WithZero.exp_inj] at h1
      omega
  have h12 : ∀ a1 : D.E.localRing, ∃ a2 : Γ.localRing,
      algebraMap Γ.localRing X.functionField a2 =
        φ (algebraMap D.E.localRing D.Y.functionField a1) := by
    intro a1
    have : D.E.divisorialValuation (algebraMap D.E.localRing D.Y.functionField a1) ≤ 1 :=
      (D.E.divisorialValuation_le_one_iff _).mpr ⟨a1, rfl⟩
    rw [← hval] at this
    obtain ⟨a2, ha2⟩ := (Γ.divisorialValuation_le_one_iff _).mp this
    exact ⟨a2, ha2⟩
  have h21 : ∀ a2 : Γ.localRing, ∃ a1 : D.E.localRing,
      φ (algebraMap D.E.localRing D.Y.functionField a1) =
        algebraMap Γ.localRing X.functionField a2 := by
    intro a2
    obtain ⟨y, hy⟩ := hφs (algebraMap Γ.localRing X.functionField a2)
    have : D.E.divisorialValuation y ≤ 1 := by
      rw [← hval, hy]
      exact (Γ.divisorialValuation_le_one_iff _).mpr ⟨a2, rfl⟩
    obtain ⟨a1, ha1⟩ := (D.E.divisorialValuation_le_one_iff _).mp this
    exact ⟨a1, by rw [ha1]; exact hy⟩
  obtain ⟨ψ, hψb, hψ⟩ := exists_ringHom_bijective_of_range φ h12 h21
  have hd' : (Algebra.trdeg k X'.functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX') hn'
  have htr : Algebra.trdeg k X'.functionField = Algebra.trdeg k D.Y.functionField :=
    trdeg_functionField_eq_of_bijective sX' D.f hb
  have htrX : Algebra.trdeg k X.functionField = Algebra.trdeg k X'.functionField :=
    trdeg_functionField_eq (sX := sX) (sX' := sX') hn hn'
  have hd1 : (Algebra.trdeg k D.Y.functionField).toNat = n := by rw [← htr]; exact hd'
  letI := stalkAlgebra (D.f ≫ sX') D.E.genericPoint
  letI := stalkAlgebra sX Γ.genericPoint
  haveI := isScalarTower_stalk_functionField (D.f ≫ sX') D.E.genericPoint
  haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
  letI Aφ : Algebra D.Y.functionField X.functionField := φ.toAlgebra
  have hTφ : IsScalarTower k D.Y.functionField X.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change algebraMap k X.functionField c = φ (algebraMap k D.Y.functionField c)
    rw [IsScalarTower.algebraMap_apply k X'.functionField D.Y.functionField c]
    change _ = φ (functionFieldMap D.f (algebraMap k X'.functionField c))
    rw [hφ]
    exact ((σ.toHom).commutes c).symm
  letI : Algebra D.E.localRing Γ.localRing := ψ.toAlgebra
  letI : Algebra D.E.localRing X.functionField :=
    ((algebraMap Γ.localRing X.functionField).comp ψ).toAlgebra
  have hS1 : IsScalarTower k D.E.localRing Γ.localRing := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    apply IsFractionRing.injective Γ.localRing X.functionField
    change _ = algebraMap Γ.localRing X.functionField (ψ (algebraMap k D.E.localRing c))
    rw [hψ, ← IsScalarTower.algebraMap_apply k D.E.localRing D.Y.functionField c,
      ← IsScalarTower.algebraMap_apply k Γ.localRing X.functionField c]
    exact IsScalarTower.algebraMap_apply k D.Y.functionField X.functionField c
  have hS2 : IsScalarTower D.E.localRing Γ.localRing X.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hS3 : IsScalarTower D.E.localRing D.Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => hψ a
  have hS4 : IsScalarTower k D.E.localRing X.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = algebraMap Γ.localRing X.functionField (ψ (algebraMap k D.E.localRing c))
    rw [IsScalarTower.algebraMap_apply k Γ.localRing X.functionField c,
      IsScalarTower.algebraMap_apply k D.E.localRing Γ.localRing c]
    rfl
  have : Algebra.EssFiniteType k D.Y.functionField :=
    essFiniteType_functionField (sX := D.f ≫ sX')
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_bijective sX' D.f hb hd'
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator (k := k) (K := D.Y.functionField)
    (K' := X.functionField) (htr.symm.trans htrX.symm) hd1
  have hω0φ : IsPullbackGenerator X.functionField
      (topFormsMap k X'.functionField D.Y.functionField n ω0) :=
    IsPullbackGenerator.of_span hω1 hω0.2.1 hω0.2.2
  obtain ⟨σE, hσE, h0σE⟩ := D.E.exists_topForms_generator (sX := D.f ≫ sX') hd1
  have hωT : IsPullbackGenerator X.functionField
      (topFormsMap k D.E.localRing D.Y.functionField n σE) :=
    IsPullbackGenerator.of_span hω1 (span_singleton_topFormsMap (nonZeroDivisors _) hσE) h0σE
  have key := ordAt_pullbackForms_eq (k := k) (K := D.Y.functionField) (K' := X.functionField)
    (A := D.E.localRing) (A' := Γ.localRing) (d := n) (m := m) hψb
    (v := fun y => D.Y.ord y D.E.genericPoint) (v' := fun y => X.ord y Γ.genericPoint)
    (fun x y hx hy => D.E.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => D.E.ord_algebraMap_of_isUnit ha)
    (fun x y hx hy => Γ.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => Γ.ord_algebraMap_of_isUnit ha)
    (fun x => hord x) hσE hωT (pullbackForms (K' := D.Y.functionField) m τ)
  let Aσ : Algebra X'.functionField X.functionField := (σ.toHom).toRingHom.toAlgebra
  have tσ : @IsScalarTower k X'.functionField X.functionField _ Aσ.toSMul _ := by
    letI := Aσ; exact IsScalarTower.of_algebraMap_eq fun c => ((σ.toHom).commutes c).symm
  have t3 : @IsScalarTower X'.functionField D.Y.functionField X.functionField Af.toSMul
      Aφ.toSMul Aσ.toSMul :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ Af Aφ Aσ fun g => (hφ g).symm
  have hcomp := @pullbackForms_comp k _ n m X'.functionField D.Y.functionField
    X.functionField _ _ _ A' AY A Af Aφ Aσ hT1 hTφ tσ t3 ω0 hω0 hω0φ τ
  calc Γ.ordForm (pluriformPullback sX sX' σ.toHom n m τ)
      = ordAt Γ.localRing (fun y => X.ord y Γ.genericPoint)
          (@pullbackForms k _ X'.functionField X.functionField _ _ A' A Aσ tσ n m τ) := rfl
    _ = ordAt Γ.localRing (fun y => X.ord y Γ.genericPoint)
          (pullbackForms (K' := X.functionField) m
            (pullbackForms (K' := D.Y.functionField) m τ)) := by rw [hcomp]
    _ = D.ordPullback τ := key

section ResidueFunctoriality

variable {k : Type u} [Field k] {X X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X']

/-- `φ^*(c w^{⊗a}) = φ(c) (φ^*w)^{⊗a}` for every `d`-form `w`, on varieties of dimension `d`. -/
private theorem pluriformPullback_smul_formPow' [CharZero k] [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sX'] {d : ℕ} (hX : topologicalKrullDim X = d)
    (hX' : topologicalKrullDim X' = d) (φ : FunctionFieldHom sX sX')
    (w : letI := functionFieldAlgebra sX'; ⋀[X'.functionField]^d Ω[X'.functionField⁄k])
    (a : ℕ) (c : X'.functionField) :
    letI := functionFieldAlgebra sX'; letI := functionFieldAlgebra sX
    letI : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
    haveI : IsScalarTower k X'.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    pluriformPullback sX sX' φ d a (c • formPow w a) =
      φ c • formPow (topFormsMap k X'.functionField X.functionField d w) a := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  have : IsScalarTower k X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_functionFieldHom hX hX' φ
    have e1 : (formPow w 0 : PluriForms k X'.functionField d (0 : ℕ)) = formPow ω 0 := by
      unfold formPow; congr 1; funext i; exact i.elim0
    have e2 : (formPow (topFormsMap k X'.functionField X.functionField d w) 0 :
        PluriForms k X.functionField d (0 : ℕ)) =
        formPow (topFormsMap k X'.functionField X.functionField d ω) 0 := by
      unfold formPow; congr 1; funext i; exact i.elim0
    rw [e1, e2]
    exact pluriformPullback_smul_formPow φ hω 0 c
  by_cases hw : w = 0
  · have h0 : ∀ {K : Type u} [Field K] [Algebra k K],
        (formPow (0 : ⋀[K]^d Ω[K⁄k]) a : PluriForms k K d a) = 0 := by
      intro K _ _
      unfold formPow
      exact (PiTensorProduct.tprod K).map_coord_zero ⟨0, ha⟩ rfl
    subst hw
    rw [map_zero (topFormsMap k X'.functionField X.functionField d), h0, h0, smul_zero, smul_zero]
    exact map_zero (pluriformPullback sX sX' φ d a)
  · obtain ⟨b⟩ := exists_basis_topForms (sX := sX') hX'
    have hspan : Submodule.span X'.functionField {w} = ⊤ := by
      have hc : b.repr w () ≠ 0 := by
        intro h
        apply hw
        rw [← b.sum_repr w]
        simp [h]
      obtain ⟨r, hr⟩ : ∃ r, r = b.repr w () := ⟨_, rfl⟩
      rw [← hr] at hc
      refine Submodule.eq_top_iff'.mpr fun x => Submodule.mem_span_singleton.mpr
        ⟨b.repr x () / r, ?_⟩
      have hx : x = b.repr x () • b () := by
        conv_lhs => rw [← b.sum_repr x]
        simp
      have hw' : w = r • b () := by
        conv_lhs => rw [← b.sum_repr w]
        simp [hr]
      rw [hw', smul_smul, div_mul_cancel₀ _ hc, ← hx]
    exact pluriformPullback_smul_formPow φ
      (isPullbackGenerator_functionFieldHom hX hX' φ hspan hw) a c

/-- The image of `c • ιMulti (D ∘ v)` under `φ^*`. -/
private theorem topFormsMap_smul_ιMulti_D (φ : FunctionFieldHom sX sX') {d : ℕ}
    (c : X'.functionField) (v : Fin d → X'.functionField) :
    letI := functionFieldAlgebra sX'; letI := functionFieldAlgebra sX
    letI : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
    haveI : IsScalarTower k X'.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    topFormsMap k X'.functionField X.functionField d
        (c • exteriorPower.ιMulti X'.functionField d
          fun i => KaehlerDifferential.D k X'.functionField (v i)) =
      φ c • exteriorPower.ιMulti X.functionField d
          fun i => KaehlerDifferential.D k X.functionField (φ (v i)) := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  have : IsScalarTower k X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  rw [LinearMap.map_smul, topFormsMap_ιMulti, algebra_compatible_smul X.functionField c]
  simp only [KaehlerDifferential.map_D]
  rfl

/-- **Poincaré residues are functorial under isomorphisms of the local rings.** Let
`σ : k(Y') → k(Y)` and `σ_T : k(T') → k(T)` be `k`-homomorphisms of function fields, and
`ψ : 𝒪_{Y',T'} → 𝒪_{Y,T}` a ring homomorphism of the local rings along the divisors, compatible
with `σ` and `σ_T` and preserving orders. Then `Res_T(σ^*τ) = σ_T^* Res_{T'}(τ)`. -/
private theorem isPoincareResidue_pluriformPullback [CharZero k] {T T' : Scheme.{u}} [IsIntegral T]
    [IsIntegral T'] [IsLocallyNoetherian X] [IsLocallyNoetherian X'] (j : T ⟶ X) (j' : T' ⟶ X')
    [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sX'] [LocallyOfFiniteType (j ≫ sX)] [LocallyOfFiniteType (j' ≫ sX')]
    {n : ℕ} (hX : topologicalKrullDim X = (n + 1 : ℕ))
    (hX' : topologicalKrullDim X' = (n + 1 : ℕ)) (hT : topologicalKrullDim T = n)
    (hT' : topologicalKrullDim T' = n) (σ : FunctionFieldHom sX sX')
    (σT : FunctionFieldHom (j ≫ sX) (j' ≫ sX'))
    (ψ : X'.presheaf.stalk (j' (genericPoint T')) →+* X.presheaf.stalk (j (genericPoint T)))
    (hψ : ∀ a, algebraMap _ X.functionField (ψ a) = σ (algebraMap _ X'.functionField a))
    (hψT : ∀ a, (j.stalkMap (genericPoint T)).hom (ψ a) =
      σT ((j'.stalkMap (genericPoint T')).hom a))
    (hord : ∀ a, X.ord (algebraMap _ X.functionField (ψ a)) (j (genericPoint T)) =
      X'.ord (algebraMap _ X'.functionField a) (j' (genericPoint T')))
    {m : ℕ} {τ : RationalPluriForms sX' (n + 1) m} {ρ : RationalPluriForms (j' ≫ sX') n m}
    (h : IsPoincareResidue sX' j' n m τ ρ) :
    IsPoincareResidue sX j n m (pluriformPullback sX sX' σ (n + 1) m τ)
      (pluriformPullback (j ≫ sX) (j' ≫ sX') σT n m ρ) := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (j' ≫ sX')
  let := functionFieldAlgebra (j ≫ sX)
  obtain ⟨t, g, x, ht, rfl, rfl⟩ := h
  refine ⟨ψ t, ψ g, fun i => ψ (x i), by rw [hord]; exact ht, ?_, ?_⟩
  · have e := pluriformPullback_smul_formPow' hX hX' σ
      ((algebraMap _ X'.functionField t)⁻¹ • exteriorPower.ιMulti X'.functionField (n + 1)
        (Fin.cons (KaehlerDifferential.D k X'.functionField (algebraMap _ _ t))
          fun i => KaehlerDifferential.D k X'.functionField (algebraMap _ _ (x i)))) m
      (algebraMap _ X'.functionField g)
    have e2 := topFormsMap_smul_ιMulti_D σ (algebraMap _ X'.functionField t)⁻¹
      (Fin.cons (algebraMap _ X'.functionField t) fun i => algebraMap _ X'.functionField (x i) :
        Fin (n + 1) → X'.functionField)
    have hc : ∀ {K : Type u} [Field K] [Algebra k K] (a : K) (b : Fin n → K),
        (Fin.cons (KaehlerDifferential.D k K a) (fun i => KaehlerDifferential.D k K (b i)) :
          Fin (n + 1) → Ω[K⁄k]) = fun i => KaehlerDifferential.D k K ((Fin.cons a b : Fin (n + 1) → K) i) := by
      intro K _ _ a b
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp
    refine e.trans ?_
    rw [hc, e2, hc]
    simp only [hψ, map_inv₀, formPow]
    congr 4
    funext _
    congr 2
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  · have e := pluriformPullback_smul_formPow' hT hT' σT
      (exteriorPower.ιMulti T'.functionField n
        fun i => KaehlerDifferential.D k T'.functionField ((j'.stalkMap (genericPoint T')).hom (x i)))
      m ((j'.stalkMap (genericPoint T')).hom g)
    refine e.trans ?_
    have e2 := topFormsMap_smul_ιMulti_D σT 1
      (fun i => (j'.stalkMap (genericPoint T')).hom (x i))
    rw [one_smul, map_one, one_smul] at e2
    rw [e2]
    simp only [hψT, formPow]
    rfl

end ResidueFunctoriality

/-- A closed subscheme whose underlying set is a prime divisor of a variety of dimension `e + 1`
has dimension `e`. -/
private theorem topologicalKrullDim_eq_of_range_eq_support {k : Type u} [Field k] {Y T : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y] [LocallyOfFiniteType sY]
    (j : T ⟶ Y) [IsClosedImmersion j]
    (P : MMP.Mori.PrimeDivisor Y) (h : Set.range j.base = (P.support : Set Y)) {e : ℕ}
    (hY : topologicalKrullDim Y = (e + 1 : ℕ)) : topologicalKrullDim T = e := by
  have hemb := j.isClosedEmbedding.isEmbedding
  let φ := hemb.toHomeomorph
  have h1 : topologicalKrullDim T = topologicalKrullDim (Set.range j.base) :=
    le_antisymm φ.isInducing.topologicalKrullDim_le φ.symm.isInducing.topologicalKrullDim_le
  rw [h1, h, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  have h2 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY P.genericPoint
  rw [P.coheight_genericPoint, hY] at h2
  generalize topologicalKrullDim (closure {P.genericPoint} : Set Y) = a at h2 ⊢
  rcases a with _ | _ | a
  · exfalso
    change (⊥ : WithBot ℕ∞) + 1 = _ at h2
    rw [WithBot.bot_add] at h2
    exact WithBot.bot_ne_coe (h2.trans (by push_cast; rfl))
  · exfalso
    change ((⊤ : ℕ∞) : WithBot ℕ∞) + ((1 : ℕ∞) : WithBot ℕ∞) = (((e + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) at h2
    rw [← WithBot.coe_add, WithBot.coe_inj, top_add] at h2
    exact ENat.top_ne_coe _ h2
  · have : ((a + 1 : ℕ) : WithBot ℕ∞) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
      rw [← h2]; push_cast; rfl
    have : a + 1 = e + 1 := by exact_mod_cast this
    have : a = e := by omega
    subst this; rfl

/-- The generic point of a closed subscheme with underlying set a prime divisor `P` is the generic
point of `P`. -/
private theorem map_genericPoint_eq_of_range_eq {Y T : Scheme.{u}} [IrreducibleSpace T]
    (j : T ⟶ Y) (P : MMP.Mori.PrimeDivisor Y) (hrange : Set.range j.base = (P.support : Set Y)) :
    j (genericPoint T) = P.genericPoint := by
  have h1 : closure ({j (genericPoint T)} : Set Y) = Set.range j.base := by
    apply le_antisymm
    · rw [hrange]
      exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure P ▸
        isClosed_closure).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr (hrange ▸ Set.mem_range_self _))
    · rintro _ ⟨z, rfl⟩
      have hz : genericPoint T ⤳ z := (genericPoint_spec T).specializes trivial
      exact specializes_iff_mem_closure.mp (hz.map j.continuous)
  have h2 : closure ({j (genericPoint T)} : Set Y) = closure {P.genericPoint} := by
    rw [h1, hrange, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact (inseparable_iff_closure_eq.mpr h2).eq

section CrepantModel

variable {k : Type} [Field k]

/-- Pull-back of rational forms along a composite of birational morphisms. -/
private theorem pullbackRationalPluriForms_comp' [PerfectField k] {X Y Z : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z] {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX]
    (f : Y ⟶ X) (g : Z ⟶ Y) [IsDominant f] [IsDominant g] [LocallyOfFiniteType (f ≫ sX)]
    (hf : Function.Bijective (functionFieldMap f)) (hg : Function.Bijective (functionFieldMap g))
    {d : ℕ} (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    {m : ℤ} (τ : RationalPluriForms sX d m) :
    pullbackRationalPluriForms (f ≫ sX) g (pullbackRationalPluriForms sX f τ) =
      (pullbackRationalPluriForms sX (g ≫ f) τ : RationalPluriForms (g ≫ f ≫ sX) d m) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldAlgebra (g ≫ f ≫ sX)
  let := functionFieldMapAlgebra f
  let := functionFieldMapAlgebra g
  let := functionFieldMapAlgebra (g ≫ f)
  have := isScalarTower_functionFieldMap sX f
  have := isScalarTower_functionFieldMap (f ≫ sX) g
  have : IsScalarTower k X.functionField Z.functionField :=
    isScalarTower_functionFieldMap sX (g ≫ f)
  have : IsScalarTower X.functionField Y.functionField Z.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g f a).symm
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  have hd' : (Algebra.trdeg k Y.functionField).toNat = d := by
    rw [← trdeg_functionField_eq_of_bijective sX f hf]
    exact hd
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator_of_bijective (f ≫ sX) g hg hd'
  have hω' : IsPullbackGenerator Z.functionField
      (topFormsMap k X.functionField Y.functionField d ω0) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω1 hω0.2.1 hω0.2.2
  exact MMP.Threefold.Mori.Helpers.pullbackForms_comp hω0 hω' τ

/-- **Log discrepancies along a crepant model.** Let `g : V ⟶ T` be a proper birational
morphism of normal varieties, `ρ ≠ 0` a rational top form on `T` with `div ρ` canonical, and
`C` the crepant boundary on `V`: `g^*(div ρ + B_T) = div(g^*ρ) + C`. Then every divisor `E`
proper over `V` has the same log discrepancy over `(V, C)` as over `(T, B_T)`. -/
private theorem exists_isLogDiscrepancy_compDivisorOver [PerfectField k] {T V : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [LocallyOfFiniteType sT] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (hT : IsNormalVariety k sT) (g : V ⟶ T) [IsProper g] (hg : IsBirationalMorphism g)
    (hV : IsNormalVariety k (g ≫ sT)) [IsDominant g] [LocallyOfFiniteType (g ≫ sT)] {d : ℕ}
    {ρ : RationalPluriForms sT d 1} (hρ : ρ ≠ 0) (hK : (divisorOfForm ρ).IsCanonicalDivisor sT d)
    (hρV : pullbackRationalPluriForms sT g ρ ≠ 0)
    (hKV : (divisorOfForm (pullbackRationalPluriForms sT g ρ)).IsCanonicalDivisor (g ≫ sT) d)
    {BT : QDivisor T} {C : QDivisor V} (hq : (Divisor.toQDivisor (divisorOfForm ρ) + BT).IsQCartier)
    {hgen : ∀ Z : irreducibleComponents V,
      g (componentGenericPoint V Z) ∉ (Divisor.toQDivisor (divisorOfForm ρ) + BT).supp}
    (hpb : (Divisor.toQDivisor (divisorOfForm ρ) + BT).IsPullback g hgen
      (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sT g ρ)) + C))
    (E : DivisorOver k (g ≫ sT)) (hE : IsProper E.f) :
    ∃ a : ℝ, MMP.Intersection.IsLogDiscrepancy (g ≫ sT) d (QDivisor.toRDivisor C) E a ∧
      MMP.Intersection.IsLogDiscrepancy sT d (QDivisor.toRDivisor BT)
        (compDivisorOver g hV hg E) a := by
  set m := (Divisor.toQDivisor (divisorOfForm ρ) + BT).cartierIndex hq
  have hm : 0 < m := QDivisor.cartierIndex_pos hq
  obtain ⟨D0, hD0, hD0c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hq
  obtain ⟨D0V, hD0V, hpbV⟩ := hpb m hm D0 hD0 hD0c
  have hD0Vc : D0V.IsCartier := hpbV.isCartier hD0c
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  have : LocallyOfFiniteType (E.f ≫ g ≫ sT) := E.isNormalVariety.1.toLocallyOfFiniteType
  have : CompactSpace E.Y := by
    have := E.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (E.f ≫ g ≫ sT)
  have hgenY := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant E.f D0V
  set D0Y := D0V.pullback hD0Vc hgenY
  have hY : D0V.IsPullback E.f hgenY D0Y := Divisor.isPullback_pullback hD0Vc hgenY
  have hcomp : D0.IsPullback (E.f ≫ g)
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (E.f ≫ g) D0) D0Y :=
    MMP.ProgramBaseChange.divisor_isPullback_comp rfl hpbV hY _
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨1 + (E.ordPullback (pullbackRationalPluriForms sT g ρ) : ℝ) -
    ∑ _i : Fin 1, (1 / (m : ℝ)) * (D0Y.coeff E.E : ℝ), ⟨hV, hE, _, hρV,
      ⟨_, hKV, fun Γ => coeff_divisorOfForm _ Γ⟩, 1, fun _ => 1 / (m : ℝ), fun _ => D0V,
      fun _ => D0Y, fun _ => hD0Vc, fun Γ => ?_, fun _ => ⟨hgenY, hY⟩, rfl⟩,
    ⟨hT, ?_, ρ, hρ, ⟨_, hK, fun Γ => coeff_divisorOfForm _ Γ⟩, 1, fun _ => 1 / (m : ℝ),
      fun _ => D0, fun _ => D0Y, fun _ => hD0c, fun Γ => ?_, fun _ => ⟨_, hcomp⟩, ?_⟩⟩
  · have h := congrArg (fun D : QDivisor V => D.coeff Γ) hD0V
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      coeff_divisorOfForm] at h
    have h' : ((D0V.coeff Γ : ℚ) : ℝ) = (m : ℝ) * (((Γ.ordForm (pullbackRationalPluriForms sT g ρ) :
        ℚ) : ℝ) + ((C.coeff Γ : ℚ) : ℝ)) := by
      rw [h, zsmul_eq_mul]; push_cast; ring
    rw [Fin.sum_univ_one, QDivisor.coeff_toRDivisor]
    push_cast at h' ⊢
    rw [h']
    field_simp
  · haveI := hE
    exact (inferInstance : IsProper (E.f ≫ g))
  · have h := congrArg (fun D : QDivisor T => D.coeff Γ) hD0
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      coeff_divisorOfForm] at h
    have h' : ((D0.coeff Γ : ℚ) : ℝ) = (m : ℝ) * (((Γ.ordForm ρ : ℚ) : ℝ) +
        ((BT.coeff Γ : ℚ) : ℝ)) := by
      rw [h, zsmul_eq_mul]; push_cast; ring
    rw [Fin.sum_univ_one, QDivisor.coeff_toRDivisor]
    push_cast at h' ⊢
    rw [h']
    field_simp
  · have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sT)
      hK.topologicalKrullDim_eq
    have hc := pullbackRationalPluriForms_comp' g E.f hg.functionFieldMap_bijective
      E.isBirationalMorphism.functionFieldMap_bijective hd ρ
    have : (compDivisorOver g hV hg E).ordPullback ρ =
        E.ordPullback (pullbackRationalPluriForms sT g ρ) := by
      change E.E.ordForm (pullbackRationalPluriForms sT (E.f ≫ g) ρ) =
        E.E.ordForm (pullbackRationalPluriForms (g ≫ sT) E.f (pullbackRationalPluriForms sT g ρ))
      rw [hc]
      rfl
    rw [this]
    rfl

/-- **A crepant proper birational morphism is a crepant birational map.** If `g : V ⟶ T` is a
proper birational morphism of normal varieties and `g^*(div ρ + B_T) = div(g^*ρ) + C`, then
`g^* : k(T) ≅ k(V)` identifies the divisorial log discrepancies of `(V, C)` and `(T, B_T)`. -/
private theorem isCrepantBirationalMap_of_isPullback [PerfectField k] {T V : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [LocallyOfFiniteType sT] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (hT : IsNormalVariety k sT) (g : V ⟶ T) [IsProper g] (hg : IsBirationalMorphism g)
    (hV : IsNormalVariety k (g ≫ sT)) [IsDominant g] [LocallyOfFiniteType (g ≫ sT)] {d : ℕ}
    {ρ : RationalPluriForms sT d 1} (hρ : ρ ≠ 0) (hK : (divisorOfForm ρ).IsCanonicalDivisor sT d)
    (hρV : pullbackRationalPluriForms sT g ρ ≠ 0)
    (hKV : (divisorOfForm (pullbackRationalPluriForms sT g ρ)).IsCanonicalDivisor (g ≫ sT) d)
    {BT : QDivisor T} {C : QDivisor V} (hq : (Divisor.toQDivisor (divisorOfForm ρ) + BT).IsQCartier)
    {hgen : ∀ Z : irreducibleComponents V,
      g (componentGenericPoint V Z) ∉ (Divisor.toQDivisor (divisorOfForm ρ) + BT).supp}
    (hpb : (Divisor.toQDivisor (divisorOfForm ρ) + BT).IsPullback g hgen
      (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sT g ρ)) + C)) :
    IsCrepantBirationalMap (g ≫ sT) sT C BT
      (functionFieldAlgEquiv sT g hg.functionFieldMap_bijective) := by
  have hdT : topologicalKrullDim T = d := hK.topologicalKrullDim_eq
  have hdV : topologicalKrullDim V = d := hKV.topologicalKrullDim_eq
  intro v a
  constructor
  · rintro ⟨n', E, hEv, hEa⟩
    obtain rfl : n' = d := by
      have := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hEa).symm.trans hdV
      exact_mod_cast this
    obtain ⟨a0, h1, h2⟩ := exists_isLogDiscrepancy_compDivisorOver hT g hg hV hρ hK hρV hKV hq hpb
      E hEa.2.1
    obtain rfl := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hEa h1 rfl
    refine ⟨n', compDivisorOver g hV hg E, ?_, h2⟩
    rw [valuation_compDivisorOver, hEv]
    rfl
  · rintro ⟨n', D, hDv, hDa⟩
    obtain rfl : n' = d := by
      have := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hDa).symm.trans hdT
      exact_mod_cast this
    obtain ⟨E, hE⟩ := exists_divisorOver_comap_eq hV hg D
    obtain ⟨E', hE'⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hV E
    obtain ⟨a0, h1, h2⟩ := exists_isLogDiscrepancy_compDivisorOver hT g hg hV hρ hK hρV hKV hq hpb
      E'.toDivisorOver E'.isProper
    have hval : (compDivisorOver g hV hg E'.toDivisorOver).valuation = D.valuation := by
      rw [valuation_compDivisorOver, hE]
      change (E'.valuation).comap _ = _
      rw [hE']
    obtain rfl := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hDa h2 hval.symm
    refine ⟨n', E'.toDivisorOver, ?_, h1⟩
    change E'.valuation = v
    rw [hE']
    ext x
    obtain ⟨y, rfl⟩ := hg.functionFieldMap_bijective.2 x
    have h3 := congrArg (fun w : Valuation T.functionField ℤᵐ⁰ => w y) (hE.symm.trans hDv)
    exact h3

/-- Two ring homomorphisms out of the function field of an integral scheme agree once the
induced morphisms of spectra agree after `Spec 𝒪_{X,η} ⟶ X`. -/
private theorem ringHom_ext_of_specMap_fromSpecStalk {X : Scheme.{0}} [IsIntegral X]
    {R : CommRingCat.{0}} {α β : X.functionField ⟶ R}
    (h : Spec.map α ≫ X.fromSpecStalk (genericPoint X) =
      Spec.map β ≫ X.fromSpecStalk (genericPoint X)) : α = β :=
  Spec.map_injective ((cancel_mono _).mp h)

/-- **The normalized graph of a birational map.** For a `k`-isomorphism `σ : k(X') ≅ k(X)` of
function fields of integral schemes proper over `k`, the normalization `W` of `X' ×_k X` in the
graph point `Spec k(X) ⟶ X' ×_k X` of `σ` is a normal integral scheme with proper birational
projections `p : W ⟶ X`, `q : W ⟶ X'` over `k` such that `q^* = p^* ∘ σ`. -/
private theorem exists_model_of_functionFieldEquiv {X X' : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X']
    [IsProper sX] [IsProper sX'] (σ : FunctionFieldEquiv sX sX') :
    ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsNormal W) (p : W ⟶ X) (q : W ⟶ X')
      (_ : IsDominant p) (_ : IsDominant q),
      IsProper p ∧ IsProper q ∧ IsBirational p ∧ IsBirational q ∧ p ≫ sX = q ≫ sX' ∧
      letI := functionFieldAlgebra sX
      letI := functionFieldAlgebra sX'
      functionFieldMap q = (functionFieldMap p).comp σ.toRingEquiv.toRingHom := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra sX'
  set θ : X'.functionField →+* X.functionField := σ.toRingEquiv.toRingHom with hθ
  set F := X.fromSpecStalk (genericPoint X) with hF
  set F' := X'.fromSpecStalk (genericPoint X') with hF'
  have hα : (Spec.map (CommRingCat.ofHom θ) ≫ F') ≫ sX' = F ≫ sX := by
    rw [Category.assoc, hF', hF, MMP.fromSpecStalk_comp_eq,
      MMP.fromSpecStalk_comp_eq, ← Spec.map_comp]
    congr 1
    ext c
    exact σ.commutes c
  set γ : Spec X.functionField ⟶ Limits.pullback sX' sX :=
    Limits.pullback.lift (Spec.map (CommRingCat.ofHom θ) ≫ F') F hα with hγ
  haveI : QuasiCompact γ := quasiCompact_of_isField (by exact Field.toIsField _) _
  haveI : QuasiSeparated γ := QuasiSeparated.of_quasiSeparatedSpace _
  have hγs : γ ≫ Limits.pullback.snd sX' sX = F := Limits.pullback.lift_snd _ _ _
  have hγf : γ ≫ Limits.pullback.fst sX' sX = Spec.map (CommRingCat.ofHom θ) ≫ F' :=
    Limits.pullback.lift_fst _ _ _
  -- finiteness of the normalization
  haveI : LocallyOfFiniteType (Limits.pullback.snd sX' sX ≫ sX) := inferInstance
  have hP : IsNagataScheme (Limits.pullback sX' sX) :=
    isNagataScheme_of_locallyOfFiniteType (Limits.pullback.snd sX' sX ≫ sX)
      (isNagataScheme_spec_of_isNagataRing _ IsNagataRing.of_field)
  have : Finite (Spec X.functionField) :=
    inferInstanceAs (Finite (PrimeSpectrum X.functionField))
  haveI hfin : IsFinite γ.fromNormalization := by
    refine isFinite_fromNormalization γ hP
      (fun U _ => have : Finite U := Subtype.finite
        TopologicalSpace.NoetherianSpace.finite_irreducibleComponents) fun x => ?_
    let := (γ.residueFieldMap x.1).hom.toAlgebra
    have hsurj : Function.Surjective (γ.residueFieldMap x.1).hom := by
      have h := surjective_residueFieldMap_of_surjectiveOnStalks F x.1
      rw [Scheme.Hom.residueFieldMap_congr hγs.symm, Scheme.residueFieldMap_comp] at h
      exact fun z => ⟨_, (h z).choose_spec⟩
    have : Algebra.EssFiniteType (Limits.pullback sX' sX |>.residueField (γ x.1))
        ((Spec X.functionField).residueField x.1) := by
      rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
      exact (RingHom.FiniteType.of_surjective _ hsurj).essFiniteType
    exact IntermediateField.fg_top _ _
  haveI : IsNormal γ.normalization := isNormal_normalization_of_isField (by exact Field.toIsField _) _
  haveI : IsIntegral γ.normalization := inferInstance
  set u := γ.fromNormalization ≫ Limits.pullback.snd sX' sX with hu
  set v := γ.fromNormalization ≫ Limits.pullback.fst sX' sX with hv
  set j := γ.toNormalization with hj
  have hjγ : j ≫ γ.fromNormalization = γ := Scheme.Hom.toNormalization_fromNormalization γ
  have hju : j ≫ u = F := by rw [hu, ← Category.assoc, hjγ, hγs]
  have hjv : j ≫ v = Spec.map (CommRingCat.ofHom θ) ≫ F' := by
    rw [hv, ← Category.assoc, hjγ, hγf]
  letI := isDominant_fromSpecStalk_genericPoint X
  letI := isDominant_fromSpecStalk_genericPoint X'
  have : IsDominant (j ≫ u) := by rw [hju]; infer_instance
  haveI hud : IsDominant u := IsDominant.of_comp j _
  have : IsDominant (j ≫ v) := by
    rw [hjv]
    haveI : Surjective (Spec.map (CommRingCat.ofHom θ)) := surjective_specMap_of_field θ
    infer_instance
  haveI hvd : IsDominant v := IsDominant.of_comp j _
  haveI hjd : IsDominant j := inferInstance
  set E := (Spec X.functionField).fromSpecStalk (genericPoint (Spec X.functionField)) with hE
  have hFE : Spec.map (CommRingCat.ofHom (functionFieldMap F)) = E :=
    (cancel_mono F).mp (functionFieldMap_fromSpecStalk F)
  have h2 : (functionFieldMap j).comp (functionFieldMap u) = functionFieldMap F := by
    have : CommRingCat.ofHom ((functionFieldMap j).comp (functionFieldMap u)) =
        CommRingCat.ofHom (functionFieldMap F) := by
      refine ringHom_ext_of_specMap_fromSpecStalk ?_
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, functionFieldMap_fromSpecStalk u,
        ← Category.assoc, functionFieldMap_fromSpecStalk j, Category.assoc, hju, hFE]
    exact congrArg CommRingCat.Hom.hom this
  have h1 : (functionFieldMap j).comp (functionFieldMap v) = (functionFieldMap F).comp θ := by
    have : CommRingCat.ofHom ((functionFieldMap j).comp (functionFieldMap v)) =
        CommRingCat.ofHom ((functionFieldMap F).comp θ) := by
      refine ringHom_ext_of_specMap_fromSpecStalk ?_
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, functionFieldMap_fromSpecStalk v,
        ← Category.assoc, functionFieldMap_fromSpecStalk j, Category.assoc, hjv,
        CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hFE]
    exact congrArg CommRingCat.Hom.hom this
  have hFb := bijective_functionFieldMap_fromSpecStalk_genericPoint X
  have hcompat : functionFieldMap v = (functionFieldMap u).comp θ := by
    ext a
    apply (functionFieldMap j).injective
    have e1 := congrArg (fun φ => φ a) h1
    have e2 := congrArg (fun φ => φ (θ a)) h2
    simp only [RingHom.comp_apply] at e1 e2
    rw [e1, ← e2]
    rfl
  refine ⟨γ.normalization, inferInstance, inferInstance, u, v, hud, hvd, inferInstance,
    inferInstance, ?_, ?_, ?_, hcompat⟩
  · refine isBirational_of_surjective_functionFieldMap u fun w => ?_
    obtain ⟨a, ha⟩ := hFb.2 (functionFieldMap j w)
    refine ⟨a, (functionFieldMap j).injective ?_⟩
    have e2 := congrArg (fun φ => φ a) h2
    simp only [RingHom.comp_apply] at e2
    rw [e2, ha]
  · refine isBirational_of_surjective_functionFieldMap v fun w => ?_
    obtain ⟨a, ha⟩ := hFb.2 (functionFieldMap j w)
    obtain ⟨b, rfl⟩ := σ.surjective a
    refine ⟨b, (functionFieldMap j).injective ?_⟩
    have e1 := congrArg (fun φ => φ b) h1
    simp only [RingHom.comp_apply] at e1
    rw [e1, ← ha]
    rfl
  · rw [hu, hv, Category.assoc, Category.assoc, Limits.pullback.condition]

/-- **Log discrepancies of the prime divisors of a model.** If `p : W ⟶ X` is a proper birational
morphism of normal varieties and `G = p^*(div τ + B)`, the prime divisor `F` of `W` has log
discrepancy `1 + ord_F(p^*τ) - coeff_F G` over `(X, B)`. -/
private theorem isLogDiscrepancy_of_isPullback {X W : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (hX : IsNormalVariety k sX) (p : W ⟶ X) [IsProper p] (hp : IsBirationalMorphism p)
    (hW : IsNormalVariety k (p ≫ sX)) [IsDominant p] [LocallyOfFiniteType (p ≫ sX)] {n : ℕ}
    {τ : RationalPluriForms sX n 1} (hτ : τ ≠ 0) (hK : (divisorOfForm τ).IsCanonicalDivisor sX n)
    {B : QDivisor X} {G : QDivisor W} (hq : (Divisor.toQDivisor (divisorOfForm τ) + B).IsQCartier)
    {hgen : ∀ Z : irreducibleComponents W,
      p (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (divisorOfForm τ) + B).supp}
    (hpb : (Divisor.toQDivisor (divisorOfForm τ) + B).IsPullback p hgen G) (F : Mori.PrimeDivisor W) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) ⟨W, p, hW, hp, F⟩
      (1 + ((F.ordForm (pullbackRationalPluriForms sX p τ) : ℤ) : ℝ) - ((G.coeff F : ℚ) : ℝ)) := by
  set m := (Divisor.toQDivisor (divisorOfForm τ) + B).cartierIndex hq
  have hm : 0 < m := QDivisor.cartierIndex_pos hq
  obtain ⟨D0, hD0, hD0c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hq
  obtain ⟨D0W, hD0W, hpbW⟩ := hpb m hm D0 hD0 hD0c
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨hX, inferInstance, τ, hτ, ⟨_, hK, fun Γ => coeff_divisorOfForm _ Γ⟩, 1,
    fun _ => 1 / (m : ℝ), fun _ => D0, fun _ => D0W, fun _ => hD0c, fun Γ => ?_,
    fun _ => ⟨_, hpbW⟩, ?_⟩
  · have h := congrArg (fun D : QDivisor X => D.coeff Γ) hD0
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      coeff_divisorOfForm] at h
    have h' : ((D0.coeff Γ : ℚ) : ℝ) = (m : ℝ) * (((Γ.ordForm τ : ℚ) : ℝ) +
        ((B.coeff Γ : ℚ) : ℝ)) := by
      rw [h, zsmul_eq_mul]; push_cast; ring
    rw [Fin.sum_univ_one, QDivisor.coeff_toRDivisor]
    push_cast at h' ⊢
    rw [h']
    field_simp
  · have h := congrArg (fun D : QDivisor W => D.coeff F) hD0W
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul] at h
    have h' : ((D0W.coeff F : ℚ) : ℝ) = (m : ℝ) * ((G.coeff F : ℚ) : ℝ) := by
      rw [h, zsmul_eq_mul]; push_cast; ring
    rw [Fin.sum_univ_one]
    push_cast at h' ⊢
    rw [h']
    field_simp
    rfl

/-- **Pull-back of a transported form to a common model.** If `p : W ⟶ X` and `q : W ⟶ X'` are
birational with `q^* = p^* ∘ σ`, then along every prime divisor `F` of `W` the forms `p^*(σ^*τ)`
and `q^*τ` have the same order. -/
private theorem ordForm_pullback_pluriformPullback_eq [CharZero k] {X X' W : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X']
    [IsLocallyNoetherian X'] [IsNormal X'] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') {n : ℕ}
    (hn : topologicalKrullDim X = n) (hn' : topologicalKrullDim X' = n)
    (σ : FunctionFieldEquiv sX sX') (p : W ⟶ X) (q : W ⟶ X') (hp : IsBirationalMorphism p)
    (hq : IsBirationalMorphism q) (hWp : IsNormalVariety k (p ≫ sX))
    (hWq : IsNormalVariety k (q ≫ sX')) [IsDominant p] [IsDominant q]
    (hcompat : ∀ a, functionFieldMap q a = functionFieldMap p ((σ.toHom) a))
    (F : Mori.PrimeDivisor W) {m : ℤ} (τ : RationalPluriForms sX' n m) :
    F.ordForm (pullbackRationalPluriForms sX p (pluriformPullback sX sX' σ.toHom n m τ)) =
      F.ordForm (pullbackRationalPluriForms sX' q τ) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (p ≫ sX) := hWp.1.toLocallyOfFiniteType
  haveI := hX.1
  haveI := hWp.1
  have hnW : topologicalKrullDim W = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hp).symm.trans hn
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra sX'
  letI := functionFieldAlgebra (p ≫ sX)
  let ep : FunctionFieldEquiv (p ≫ sX) sX := functionFieldAlgEquiv sX p hp.functionFieldMap_bijective
  let σ' : FunctionFieldEquiv (p ≫ sX) sX' := σ.trans ep
  have h1 : pullbackRationalPluriForms sX p (pluriformPullback sX sX' σ.toHom n m τ) =
      pluriformPullback (p ≫ sX) sX' σ'.toHom n m τ := by
    have := pluriformPullback_comp (sX := p ≫ sX) (sX' := sX) (sX'' := sX') hnW hn hn' m
      ep.toHom σ.toHom τ
    exact this
  rw [h1]
  let D : DivisorOver k sX' := ⟨W, q, hWq, hq, F⟩
  have hv : ∀ g, D.valuation g = F.divisorialValuation ((σ'.toHom) g) := by
    intro g
    change F.divisorialValuation (functionFieldMap q g) = _
    rw [hcompat]
    rfl
  exact ordForm_pluriformPullback_eq_ordPullback hWp hX' hnW hn' σ' F D hv τ

/-- **Crepant birational maps have equal pull-backs on a common model.** If
`σ : (X, B) ⇢ (X', B')` is crepant, `p : W ⟶ X`, `q : W ⟶ X'` proper birational with
`q^* = p^* ∘ σ`, and `τ = σ^*τ'`, then `p^*(div τ + B) = q^*(div τ' + B')`. -/
private theorem pullback_eq_pullback_of_isCrepantBirationalMap [CharZero k] {X X' W : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral X']
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X'] [LocallyOfFiniteType sX']
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') {B : QDivisor X} {B' : QDivisor X'}
    (σ : FunctionFieldEquiv sX sX') (hσ : IsCrepantBirationalMap sX sX' B B' σ)
    (p : W ⟶ X) (q : W ⟶ X') [IsProper p] [IsProper q] (hp : IsBirationalMorphism p)
    (hq : IsBirationalMorphism q) (hWp : IsNormalVariety k (p ≫ sX))
    (hWq : IsNormalVariety k (q ≫ sX')) [IsDominant p] [IsDominant q]
    [LocallyOfFiniteType (p ≫ sX)] [LocallyOfFiniteType (q ≫ sX')]
    (hcompat : ∀ a, functionFieldMap q a = functionFieldMap p ((σ.toHom) a)) {n : ℕ}
    {τ' : RationalPluriForms sX' n 1} (hτ' : τ' ≠ 0)
    (hK' : (divisorOfForm τ').IsCanonicalDivisor sX' n)
    (hτ : pluriformPullback sX sX' σ.toHom n 1 τ' ≠ 0)
    (hK : (divisorOfForm (pluriformPullback sX sX' σ.toHom n 1 τ')).IsCanonicalDivisor sX n)
    (hQ : (Divisor.toQDivisor (divisorOfForm (pluriformPullback sX sX' σ.toHom n 1 τ')) +
      B).IsQCartier) (hQ' : (Divisor.toQDivisor (divisorOfForm τ') + B').IsQCartier)
    {G G' : QDivisor W}
    {hgen : ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉
      (Divisor.toQDivisor (divisorOfForm (pluriformPullback sX sX' σ.toHom n 1 τ')) + B).supp}
    {hgen' : ∀ Z : irreducibleComponents W, q (componentGenericPoint W Z) ∉
      (Divisor.toQDivisor (divisorOfForm τ') + B').supp}
    (hG : (Divisor.toQDivisor (divisorOfForm (pluriformPullback sX sX' σ.toHom n 1 τ')) +
      B).IsPullback p hgen G)
    (hG' : (Divisor.toQDivisor (divisorOfForm τ') + B').IsPullback q hgen' G') : G = G' := by
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  have hn' : topologicalKrullDim X' = n := hK'.topologicalKrullDim_eq
  refine Finsupp.ext fun F => ?_
  have h1 := isLogDiscrepancy_of_isPullback hX p hp hWp hτ hK hQ hG F
  have h2 := isLogDiscrepancy_of_isPullback hX' q hq hWq hτ' hK' hQ' hG' F
  obtain ⟨n'', D'', hD''v, hD''⟩ := (hσ _ _).mp ⟨n, _, rfl, h1⟩
  have hv : D''.valuation = (⟨W, q, hWq, hq, F⟩ : DivisorOver k sX').valuation := by
    rw [hD''v]
    ext g
    change F.divisorialValuation (functionFieldMap p ((σ.toHom) g)) =
      F.divisorialValuation (functionFieldMap q g)
    rw [hcompat]
  have he := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hD'' h2 hv
  have hord := ordForm_pullback_pluriformPullback_eq hX hX' hn hn' σ p q hp hq hWp hWq hcompat F τ'
  rw [hord] at he
  have : ((G.coeff F : ℚ) : ℝ) = ((G'.coeff F : ℚ) : ℝ) := by linarith
  exact_mod_cast this

/-- **The divisor of a nonzero rational top form on a normal variety is canonical.** -/
private theorem isCanonicalDivisor_divisorOfForm [PerfectField k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    {τ : RationalPluriForms sX n 1} (hτ : τ ≠ 0) : (divisorOfForm τ).IsCanonicalDivisor sX n := by
  letI := functionFieldAlgebra sX
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hn
  have hb : (b () : RationalTopForms sX n) ≠ 0 := b.ne_zero ()
  have hK := MMP.Spreading.CanonExist.isCanonicalDivisor_topFormDivisor hX hn hb
  exact hK.of_linearlyEquivalent (by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK hτ)

/-- A separated birational morphism of finite type onto a Noetherian integral scheme is a
birational morphism in the sense of rational maps. -/
private theorem isBirationalMorphism_of_isBirational' {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsNoetherian X] (f : Y ⟶ X) [IsSeparated f] [LocallyOfFiniteType f]
    (hf : IsBirational f) : IsBirationalMorphism f := by
  haveI := hf.isDominant
  obtain ⟨V, hV, hiso⟩ := exists_isIso_restrict_of_mem_genericPoints f hf (genericPoint X)
    (Stacks.Chow.genericPoint_mem_genericPoints X)
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE f (f ⁻¹ᵁ V) V
    ⟨genericPoint Y, show f (genericPoint Y) ∈ V by
      rwa [MMP.Positivity.map_genericPoint_eq_of_isDominant]⟩ ⟨_, hV⟩ le_rfl ?_
  simpa [Scheme.Hom.resLE] using hiso

/-- **The strict transform of a prime divisor.** If `p : W ⟶ X` is a proper birational morphism
onto a normal Noetherian integral scheme, every prime divisor `P` of `X` is the image of a prime
divisor `Q` of `W` over which `p` is an isomorphism near `η_P`; its valuation is that of `P`. -/
private theorem exists_primeDivisor_map_genericPoint_eq {X W : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsNoetherian X] [IsNormal X] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (hX : IsNormalVariety k sX) (p : W ⟶ X) [IsProper p]
    (hp : IsBirational p)
    (hW : IsNormalVariety k (p ≫ sX)) (P : Mori.PrimeDivisor X) :
    ∃ (Q : Mori.PrimeDivisor W) (U : X.Opens), p Q.genericPoint = P.genericPoint ∧
      P.genericPoint ∈ U ∧ IsIso (p ∣_ U) ∧
      haveI := hp.isDominant
      ∀ g, Q.divisorialValuation (functionFieldMap p g) = P.divisorialValuation g := by
  haveI := hp.isDominant
  haveI := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk
    P.coheight_genericPoint
  obtain ⟨U, hPU, hUiso⟩ := exists_isIso_restrict_of_isDiscreteValuationRing p hp P.genericPoint
  obtain ⟨x, hx⟩ : P.genericPoint ∈ Set.range p := by
    rw [← p.isClosedMap.isClosed_range.closure_eq, p.denseRange.closure_range]; trivial
  have hxb : p x ∈ biregularLocus p := le_biregularLocus (f := p) (V := U) hUiso (hx ▸ hPU)
  have hx1 : Order.coheight x = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus p hxb, hx]
    exact P.coheight_genericPoint
  set Q : Mori.PrimeDivisor W := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx1
  have hQ : MMP.Mori.PrimeDivisor.genericPoint Q = x :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hx1
  haveI : LocallyOfFiniteType p := by
    have := hW.1.toLocallyOfFiniteType
    exact locallyOfFiniteType_of_comp p sX
  let D : DivisorOver k sX := ⟨W, p, hW, isBirationalMorphism_of_isBirational' p hp, Q⟩
  have hD := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hX D P
    (by change p _ = _; rw [hQ, hx])
  refine ⟨Q, U, by rw [hQ, hx], hPU, hUiso, fun g => ?_⟩
  have h := congrArg (fun w => w g) hD
  change MMP.Mori.PrimeDivisor.divisorialValuation Q (functionFieldMap p g) =
    P.divisorialValuation (functionFieldMap (𝟙 X) g) at h
  rw [h, MMP.Mori.functionFieldMap_id_apply]

/-- **The normalization of a prime divisor.** A prime divisor `Q` of a normal variety `W` has a
normalization: a normal variety `N` with a proper morphism `ν : N ⟶ W` sending the generic point
of `N` to that of `Q`, whose stalk map there is surjective. -/
private theorem exists_normalization_primeDivisor' {W : Scheme.{0}} {sW : W ⟶ Spec (.of k)}
    [IsIntegral W] (hW : IsNormalVariety k sW) (Q : Mori.PrimeDivisor W) :
    ∃ (N : Scheme.{0}) (_ : IsIntegral N) (ν : N ⟶ W), IsNormalVariety k (ν ≫ sW) ∧ IsProper ν ∧
      ν (genericPoint N) = Q.genericPoint ∧ Function.Surjective (ν.stalkMap (genericPoint N)).hom := by
  have := Q.integral
  have := hW.1
  have : AlgebraicGeometry.IsVariety k (Q.idealSheaf.subschemeι ≫ sW) :=
    (MMP.Mori.isVariety_iff k _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨⟨hvar, hnorm, hfin, -, -⟩, -, -, -, -⟩ :=
    MMP.Threefold.normalization_spec (Q.idealSheaf.subschemeι ≫ sW)
  set Z := Q.idealSheaf.subscheme
  set hZ := MMP.finite_irreducibleComponents_of_isIntegral Z
  set ν₀ := Z.normalization hZ
  have hbir : IsBirational ν₀ := Scheme.isBirational_normalization _ _
  haveI : IsIntegral (Z.normalizationScheme hZ) := hvar.toIsIntegral
  haveI := hbir.isDominant
  have hgen : ν₀ (genericPoint _) = genericPoint Z := map_genericPoint_of_isDominant ν₀
  refine ⟨_, inferInstance, ν₀ ≫ Q.idealSheaf.subschemeι, ⟨by rw [Category.assoc]; exact hvar,
    hnorm⟩, inferInstance, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply, hgen]
    rfl
  · rw [Scheme.Hom.stalkMap_comp]
    have h1 : IsIso (ν₀.stalkMap (genericPoint _)) :=
      hbir.2 _ (by rw [genericPoints_eq_singleton]; rfl)
    have hA := Q.idealSheaf.subschemeι.stalkMap_surjective (ν₀ (genericPoint _))
    have hB := (ConcreteCategory.bijective_of_isIso (ν₀.stalkMap (genericPoint _))).2
    intro z
    obtain ⟨y, rfl⟩ := hB z
    obtain ⟨w, rfl⟩ := hA y
    exact ⟨w, rfl⟩

/-- A quasi-compact morphism from a reduced scheme whose image lies in the image of a closed
immersion `ι` factors through `ι`. -/
private theorem exists_comp_eq_of_range_subset {N Y Z : Scheme.{0}} [IsReduced N] (ι : Y ⟶ Z)
    [IsClosedImmersion ι] (g : N ⟶ Z) [QuasiCompact g] (h : Set.range g ⊆ Set.range ι) :
    ∃ α : N ⟶ Y, α ≫ ι = g := by
  have H : ι.ker ≤ g.ker := Stacks.Chow.ker_le_of_support_subset_range ι g.ker (by
    rw [Scheme.Hom.support_ker]
    exact closure_minimal h ι.isClosedEmbedding.isClosed_range)
  exact ⟨IsClosedImmersion.lift ι g H, IsClosedImmersion.lift_fac _ _ _⟩

/-- **Stalk maps and function field maps.** For a dominant morphism `f : W ⟶ X` of integral
schemes, a point `y` of `W` and a specialization `z` of `f y`, restricting from `z` to `f y`,
pulling back to `y` and passing to `k(W)` is `𝒪_{X,z} → k(X) → k(W)`. -/
private theorem stalkSpecializes_stalkMap_algebraMap {W X : Scheme.{0}} [IsIntegral W]
    [IsIntegral X] (f : W ⟶ X) [IsDominant f] (y : W) (z : X) (h : f y ⤳ z) :
    X.presheaf.stalkSpecializes h ≫ f.stalkMap y ≫
        CommRingCat.ofHom (algebraMap (W.presheaf.stalk y) W.functionField) =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk z) X.functionField) ≫
        CommRingCat.ofHom (functionFieldMap f) := by
  have h0 : genericPoint W ⤳ y := (genericPoint_spec W).specializes trivial
  have h1 : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
  change X.presheaf.stalkSpecializes h ≫ f.stalkMap y ≫ W.presheaf.stalkSpecializes h0 =
    X.presheaf.stalkSpecializes h1 ≫ ((X.presheaf.stalkCongr (Inseparable.of_eq
      (map_genericPoint_of_isDominant f).symm)).hom ≫ f.stalkMap (genericPoint W))
  rw [← Scheme.Hom.stalkSpecializes_stalkMap, TopCat.Presheaf.stalkCongr_hom, ← Category.assoc,
    ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  congr 1
  exact (TopCat.Presheaf.stalkSpecializes_comp _ _ _).symm

/-- **Stalk maps along a lift through a closed immersion.** If `α : N ⟶ T` lifts `ν ≫ p` through
`ι : T ⟶ X`, then for a germ `a` at the generic point of `T`, pulling back along `p` and `ν` gives
`α^*(a|_T)`. -/
private theorem stalkMap_apply_eq_functionFieldMap_apply {X T W N : Scheme.{0}} [IsIntegral T]
    [IsIntegral N] (p : W ⟶ X) (ι : T ⟶ X) (ν : N ⟶ W) (α : N ⟶ T) [IsDominant α]
    (hα : α ≫ ι = ν ≫ p) (hp : p (ν (genericPoint N)) ⤳ ι (genericPoint T))
    (a : X.presheaf.stalk (ι (genericPoint T))) :
    (ν.stalkMap (genericPoint N)).hom ((p.stalkMap _).hom ((X.presheaf.stalkSpecializes hp).hom a)) =
      functionFieldMap α ((ι.stalkMap (genericPoint T)).hom a) := by
  have hα0 : α (genericPoint N) ⤳ genericPoint T := by rw [map_genericPoint_of_isDominant α]
  have hαf : functionFieldMap α = (T.presheaf.stalkSpecializes hα0 ≫ α.stalkMap _).hom := by
    unfold functionFieldMap
    rw [TopCat.Presheaf.stalkCongr_hom]
  have key : X.presheaf.stalkSpecializes hp ≫ p.stalkMap _ ≫ ν.stalkMap (genericPoint N) =
      ι.stalkMap (genericPoint T) ≫ T.presheaf.stalkSpecializes hα0 ≫
        α.stalkMap (genericPoint N) := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk (ι (genericPoint T)))).1
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, Category.assoc, ← hα,
      Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
    simp only [Category.assoc]
    rw [← Category.assoc (Spec.map (T.presheaf.stalkSpecializes hα0)),
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    simp only [Category.assoc]
    rw [← Category.assoc (Spec.map (α.stalkMap (genericPoint N))),
      Scheme.SpecMap_stalkMap_fromSpecStalk, Category.assoc]
  rw [hαf]
  exact congrArg (fun φ => φ.hom a) key

/-- **Function field maps through a common model.** Let `p : W ⟶ X`, `q : W ⟶ X'` be dominant with
`q^* = p^* ∘ σ`, let `ι : T ⟶ X`, `ι' : T' ⟶ X'` be integral closed subschemes, and `ψ` a map of
local rings at their generic points compatible with `σ`, inducing `σ_T : k(T') → k(T)`. If
`ν : N ⟶ W` sends the generic point of `N` to a point over `T` and `T'`, and `α : N ⟶ T`,
`β : N ⟶ T'` lift `ν ≫ p` and `ν ≫ q`, then `β^* = α^* ∘ σ_T`. -/
private theorem functionFieldMap_eq_comp_of_stalkMap {X X' T T' W N : Scheme.{0}} [IsIntegral X]
    [IsIntegral X'] [IsIntegral T] [IsIntegral T'] [IsIntegral W] [IsIntegral N]
    (σ : X'.functionField →+* X.functionField) (p : W ⟶ X) (q : W ⟶ X') [IsDominant p]
    [IsDominant q] (hcompat : functionFieldMap q = (functionFieldMap p).comp σ)
    (ι : T ⟶ X) (ι' : T' ⟶ X') [IsClosedImmersion ι']
    (ψ : X'.presheaf.stalk (ι' (genericPoint T')) →+* X.presheaf.stalk (ι (genericPoint T)))
    (hψ : ∀ a, algebraMap _ X.functionField (ψ a) = σ (algebraMap _ X'.functionField a))
    (σT : T'.functionField →+* T.functionField)
    (hσT : ∀ a, σT ((ι'.stalkMap (genericPoint T')).hom a) =
      (ι.stalkMap (genericPoint T)).hom (ψ a))
    (ν : N ⟶ W) (α : N ⟶ T) (β : N ⟶ T') [IsDominant α] [IsDominant β]
    (hα : α ≫ ι = ν ≫ p) (hβ : β ≫ ι' = ν ≫ q)
    (hp : p (ν (genericPoint N)) ⤳ ι (genericPoint T))
    (hq : q (ν (genericPoint N)) ⤳ ι' (genericPoint T')) :
    functionFieldMap β = (functionFieldMap α).comp σT := by
  set y := ν (genericPoint N)
  have key3 : ∀ a, (X'.presheaf.stalkSpecializes hq ≫ q.stalkMap y).hom a =
      (X.presheaf.stalkSpecializes hp ≫ p.stalkMap y).hom (ψ a) := by
    intro a
    apply IsFractionRing.injective (W.presheaf.stalk y) W.functionField
    have e1 := congrArg (fun φ => φ.hom a) (stalkSpecializes_stalkMap_algebraMap q y _ hq)
    have e2 := congrArg (fun φ => φ.hom (ψ a)) (stalkSpecializes_stalkMap_algebraMap p y _ hp)
    refine e1.trans (Eq.trans ?_ e2.symm)
    change functionFieldMap q (algebraMap _ _ a) = functionFieldMap p (algebraMap _ _ (ψ a))
    rw [hcompat, RingHom.comp_apply, hψ]
  ext b
  obtain ⟨a, rfl⟩ := ι'.stalkMap_surjective (genericPoint T') b
  rw [RingHom.comp_apply, hσT, ← stalkMap_apply_eq_functionFieldMap_apply q ι' ν β hβ hq,
    ← stalkMap_apply_eq_functionFieldMap_apply p ι ν α hα hp]
  exact congrArg (ν.stalkMap (genericPoint N)).hom (key3 a)

/-- **Birationality of a lift.** If `α : N ⟶ T` lifts `ν ≫ p` through `ι : T ⟶ X`, `p` is an
isomorphism of stalks at `ν(η_N)`, `ν(η_N)` lies over `ι(η_T)` and the stalk map of `ν` at the
generic point is surjective, then `α^* : k(T) → k(N)` is surjective. -/
private theorem surjective_functionFieldMap_of_lift {X T W N : Scheme.{0}} [IsIntegral T]
    [IsIntegral N] (p : W ⟶ X) (ι : T ⟶ X) (ν : N ⟶ W) (α : N ⟶ T) [IsDominant α]
    (hα : α ≫ ι = ν ≫ p) (hpν : p (ν (genericPoint N)) = ι (genericPoint T))
    (hiso : IsIso (p.stalkMap (ν (genericPoint N))))
    (hν : Function.Surjective (ν.stalkMap (genericPoint N)).hom) :
    Function.Surjective (functionFieldMap α) := by
  have hp : p (ν (genericPoint N)) ⤳ ι (genericPoint T) := by rw [hpν]
  have hsp : IsIso (X.presheaf.stalkSpecializes hp) := by
    have := (X.presheaf.stalkCongr (Inseparable.of_eq hpν.symm)).isIso_hom
    rw [TopCat.Presheaf.stalkCongr_hom] at this
    exact this
  intro z
  obtain ⟨w, rfl⟩ := hν z
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso (p.stalkMap _)).2 w
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (X.presheaf.stalkSpecializes hp)).2 b
  exact ⟨_, (stalkMap_apply_eq_functionFieldMap_apply p ι ν α hα hp a).symm⟩

/-- `MMP.Fourfold.IsCrepantBirationalMap` for a crepant proper birational morphism
`g : V ⟶ T`, for any structure morphism `s_V = g ≫ s_T` of `V` and any `k`-isomorphism
`e : k(T) ≅ k(V)` acting as `g^*`. -/
private theorem isCrepantBirationalMap_of_isPullback' [PerfectField k] {T V : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [LocallyOfFiniteType sT] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (hT : IsNormalVariety k sT) (g : V ⟶ T) [IsProper g] (hg : IsBirationalMorphism g)
    (hV : IsNormalVariety k (g ≫ sT)) [IsDominant g] [LocallyOfFiniteType (g ≫ sT)] {d : ℕ}
    {ρ : RationalPluriForms sT d 1} (hρ : ρ ≠ 0) (hK : (divisorOfForm ρ).IsCanonicalDivisor sT d)
    (hρV : pullbackRationalPluriForms sT g ρ ≠ 0)
    (hKV : (divisorOfForm (pullbackRationalPluriForms sT g ρ)).IsCanonicalDivisor (g ≫ sT) d)
    {BT : QDivisor T} {C : QDivisor V} (hq : (Divisor.toQDivisor (divisorOfForm ρ) + BT).IsQCartier)
    {hgen : ∀ Z : irreducibleComponents V,
      g (componentGenericPoint V Z) ∉ (Divisor.toQDivisor (divisorOfForm ρ) + BT).supp}
    (hpb : (Divisor.toQDivisor (divisorOfForm ρ) + BT).IsPullback g hgen
      (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sT g ρ)) + C))
    {sV : V ⟶ Spec (.of k)} (hsV : g ≫ sT = sV) (e : FunctionFieldEquiv sV sT)
    (he : ∀ a, e a = functionFieldMap g a) :
    IsCrepantBirationalMap sV sT C BT e := by
  subst hsV
  have : e = functionFieldAlgEquiv sT g hg.functionFieldMap_bijective := by
    letI := functionFieldAlgebra sT
    letI := functionFieldAlgebra (g ≫ sT)
    exact AlgEquiv.ext he
  subst this
  exact isCrepantBirationalMap_of_isPullback hT g hg hV hρ hK hρV hKV hq hpb

/-- A normal integral scheme proper over a normal variety is a normal variety. -/
private theorem isNormalVariety_comp_of_isProper {X Y : Scheme.{0}} [IsIntegral Y] [IsNormal Y]
    {s : X ⟶ Spec (.of k)} (hs : IsNormalVariety k s) (f : Y ⟶ X) [IsProper f] :
    IsNormalVariety k (f ≫ s) := by
  obtain ⟨-, h1, h2, h3⟩ := (MMP.Mori.isVariety_iff k s).mp hs.1
  exact ⟨(MMP.Mori.isVariety_iff k (f ≫ s)).mpr
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩

/-- **Crepancy between points.** A normal variety of dimension zero carries no divisors over it,
so every isomorphism of function fields of two such varieties is crepant. -/
private theorem isCrepantBirationalMap_of_topologicalKrullDim_eq_zero {T T' : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)} {sT' : T' ⟶ Spec (.of k)} [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] [IsIntegral T'] [IsLocallyNoetherian T'] [IsNormal T']
    (hT : topologicalKrullDim T = 0) (hT' : topologicalKrullDim T' = 0) (B : QDivisor T)
    (B' : QDivisor T') (σ : FunctionFieldEquiv sT sT') :
    IsCrepantBirationalMap sT sT' B B' σ := by
  have key : ∀ {S : Scheme.{0}} {s : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S]
      [IsNormal S], topologicalKrullDim S = 0 → ∀ (C : QDivisor S) v a,
      ¬ HasLogDiscrepancy s C v a := by
    intro S s _ _ _ hS C v a h
    obtain ⟨n, D, -, hD⟩ := h
    obtain ⟨hSv, -⟩ := hD
    have := D.isIntegral
    haveI := hSv.1
    haveI := D.isNormalVariety.1
    have hY : topologicalKrullDim D.Y = 0 :=
      (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism s (D.f ≫ s)
        D.isBirationalMorphism).symm.trans hS
    have h1 := AlgebraicGeometry.coheight_le_topologicalKrullDim D.E.genericPoint
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, hY] at h1
    exact absurd h1 (by decide)
  intro v a
  exact ⟨fun h => absurd h (key hT B v a), fun h => absurd h (key hT' B' _ a)⟩

/-- A birational morphism `g : V ⟶ T` gives a `k`-isomorphism `k(T) ≅ k(V)` acting as `g^*` for
every structure morphism `s_V = g ≫ s_T` of `V`. -/
private theorem exists_functionFieldEquiv_of_comp_eq {V T : Scheme.{0}} [IsIntegral V]
    [IsIntegral T] {sT : T ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} (g : V ⟶ T) [IsDominant g]
    (hg : Function.Bijective (functionFieldMap g)) (h : g ≫ sT = sV) :
    ∃ e : FunctionFieldEquiv sV sT, ∀ a, e a = functionFieldMap g a := by
  subst h
  exact ⟨functionFieldAlgEquiv sT g hg, fun _ => rfl⟩

/-- The generic point of a prime divisor along which a `ℚ`-divisor has coefficient zero is not in
its support. -/
private theorem genericPoint_notMem_supp_of_coeff_eq_zero {Y : Scheme.{0}} {D : QDivisor Y}
    {P : Mori.PrimeDivisor Y} (h : D.coeff P = 0) : P.genericPoint ∉ D.supp := by
  intro hm
  obtain ⟨E, hE, hPE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hm
  obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hPE
  exact hE h

/-- The pull-back predicate only depends on the morphism, not on how it is written. -/
private theorem isPullback_of_hom_eq {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f g : X ⟶ Y} (h : f = g) {D : QDivisor Y}
    {hf : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp}
    {hg : ∀ Z : irreducibleComponents X, g (componentGenericPoint X Z) ∉ D.supp} {D' : QDivisor X}
    (H : D.IsPullback f hf D') : D.IsPullback g hg D' := by
  subst h
  exact H

/-- The pull-back predicate only depends on the divisor pulled back. -/
private theorem isPullback_of_eq_source {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {D₁ D₂ : QDivisor Y} (h : D₁ = D₂)
    {h₁ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D₁.supp}
    {h₂ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D₂.supp} {D' : QDivisor X}
    (H : D₁.IsPullback f h₁ D') : D₂.IsPullback f h₂ D' := by
  subst h
  exact H

/-- The pull-back of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_of_isPullback {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {D : QDivisor Y} (hD : D.IsQCartier)
    {hf : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp} {D' : QDivisor X}
    (H : D.IsPullback f hf D') : D'.IsQCartier := by
  obtain ⟨C, hC, hCc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hD
  obtain ⟨C', hC', hpb⟩ := H _ (QDivisor.cartierIndex_pos hD) C hC hCc
  exact ⟨_, by exact_mod_cast (QDivisor.cartierIndex_pos hD).ne', C', hC', hpb.isCartier hCc⟩

/-- Pull-backs of `ℚ`-divisors compose. -/
private theorem qDivisor_isPullback_comp' {X Y Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian Z] [IsNormal Z] (p : Y ⟶ X) (q : Z ⟶ Y) {M : QDivisor X}
    {MY : QDivisor Y} {MZ : QDivisor Z}
    {hM : ∀ C : irreducibleComponents Y, p (componentGenericPoint Y C) ∉ M.supp}
    {hMY : ∀ C : irreducibleComponents Z, q (componentGenericPoint Z C) ∉ MY.supp}
    (h₁ : M.IsPullback p hM MY) (h₂ : MY.IsPullback q hMY MZ)
    (hM' : ∀ C : irreducibleComponents Z, (q ≫ p) (componentGenericPoint Z C) ∉ M.supp) :
    M.IsPullback (q ≫ p) hM' MZ := fun m hm D hD hDc => by
  obtain ⟨D', hD', hpb⟩ := h₁ m hm D hD hDc
  obtain ⟨D'', hD'', hpb'⟩ := h₂ m hm D' hD' (hpb.isCartier hDc)
  exact ⟨D'', hD'', MMP.ProgramBaseChange.divisor_isPullback_comp rfl hpb hpb' _⟩

/-- A morphism out of an irreducible scheme whose generic point maps to the generic point of a
prime divisor `P_f` lands in the image of any closed immersion onto `P_f`. -/
private theorem range_comp_subset_of_map_genericPoint {N W Y Z : Scheme.{0}} [IrreducibleSpace N]
    (ν : N ⟶ W) (f : W ⟶ Y) (ιf : Z ⟶ Y) (Pf : Mori.PrimeDivisor Y)
    (hr : Set.range ιf.base = (Pf.support : Set Y))
    (h : f (ν (genericPoint N)) = Pf.genericPoint) :
    Set.range (ν ≫ f).base ⊆ Set.range ιf.base := by
  rintro _ ⟨z, rfl⟩
  rw [hr, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  have hz : genericPoint N ⤳ z := (genericPoint_spec N).specializes trivial
  have h2 := hz.map (ν ≫ f).base.hom.continuous
  change (ν ≫ f) (genericPoint N) ⤳ (ν ≫ f) z at h2
  rw [Scheme.Hom.comp_apply, h] at h2
  exact specializes_iff_mem_closure.mp h2

/-- **Crepant maps induce crepant maps on floor divisors.** Let `σ : (X, B) ⇢ (X', B')` be a
crepant birational map of normal varieties proper over `k`, and `T ⊂ X`, `T' ⊂ X'` normal floor
divisors with their differents `B_T`, `B_{T'}`, such that `σ` identifies the local rings
`𝒪_{X',T'} ≅ 𝒪_{X,T}` and so induces `σ_T : k(T') ≅ k(T)`. Then `σ_T` is a crepant birational map
`(T, B_T) ⇢ (T', B_{T'})`: on the normalization `N` of the strict transform of `T` on a common
model `W`, both adjunction pairs pull back to the restriction of the common pull-back
`p^*(K_X + B) = q^*(K_{X'} + B')`. -/
private theorem isCrepantBirationalMap_of_isAdjunctionStep [IsAlgClosed k] [CharZero k]
    {X X' T T' : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsProper sX] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    [LocallyOfFiniteType sX'] [IsProper sX']
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') {n : ℕ}
    (hn : topologicalKrullDim X = (n + 1 : ℕ)) (hn' : topologicalKrullDim X' = (n + 1 : ℕ))
    {B : QDivisor X} {B' : QDivisor X'} {K : Divisor X} {K' : Divisor X'}
    (hK : K.IsCanonicalDivisor sX (n + 1)) (hK' : K'.IsCanonicalDivisor sX' (n + 1))
    (hKB : (Divisor.toQDivisor K + B).IsQCartier) (hKB' : (Divisor.toQDivisor K' + B').IsQCartier)
    (σ : FunctionFieldEquiv sX sX') (hσ : IsCrepantBirationalMap sX sX' B B' σ)
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [IsIntegral T'] [IsLocallyNoetherian T'] [IsNormal T'] [CompactSpace T']
    {ι : T ⟶ X} {ι' : T' ⟶ X'} [IsClosedImmersion ι] [IsClosedImmersion ι']
    {BT : QDivisor T} {BT' : QDivisor T'}
    (hι : IsAdjunctionStep sX B ι BT) (hι' : IsAdjunctionStep sX' B' ι' BT')
    (P : Mori.PrimeDivisor X) (P' : Mori.PrimeDivisor X')
    (hrP : Set.range ι.base = (P.support : Set X)) (hrP' : Set.range ι'.base = (P'.support : Set X'))
    (hP' : ∀ g, P'.divisorialValuation g = P.divisorialValuation ((σ.toHom) g))
    (ψ : X'.presheaf.stalk (ι' (genericPoint T')) →+* X.presheaf.stalk (ι (genericPoint T)))
    (hψ : ∀ a, algebraMap _ X.functionField (ψ a) = (σ.toHom) (algebraMap _ X'.functionField a))
    (hord : ∀ a, X.ord (algebraMap _ X.functionField (ψ a)) (ι (genericPoint T)) =
      X'.ord (algebraMap _ X'.functionField a) (ι' (genericPoint T')))
    (σT : FunctionFieldEquiv (ι ≫ sX) (ι' ≫ sX'))
    (hσT : ∀ a, (σT.toHom) ((ι'.stalkMap (genericPoint T')).hom a) =
      (ι.stalkMap (genericPoint T)).hom (ψ a)) :
    IsCrepantBirationalMap (ι ≫ sX) (ι' ≫ sX') BT BT' σT := by
  have hT := hι.1
  have hT' := hι'.1
  haveI : LocallyOfFiniteType (ι ≫ sX) := hT.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (ι' ≫ sX') := hT'.1.toLocallyOfFiniteType
  have hdT : topologicalKrullDim T = n := topologicalKrullDim_eq_of_range_eq_support sX ι P hrP hn
  have hdT' : topologicalKrullDim T' = n :=
    topologicalKrullDim_eq_of_range_eq_support sX' ι' P' hrP' hn'
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · exact isCrepantBirationalMap_of_topologicalKrullDim_eq_zero (by exact_mod_cast hdT)
      (by exact_mod_cast hdT') BT BT' σT
  obtain ⟨Q'⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdT' hnpos.ne'
  -- a form `τ'` with a simple pole along `T'` and its residue `ρ'`
  obtain ⟨τ', hτ'0, hτ'P, -, ρ', hρ', hρ'0, -⟩ :=
    MMP.Fourfold.exists_form_of_residue_order sX' hX' (by exact_mod_cast hn') ι' hT'
      P' hrP' Q'
  -- its transport `τ = σ^*τ'`, with residue `ρ = σ_T^*ρ'`
  set τ := pluriformPullback sX sX' σ.toHom (n + 1) 1 τ' with hτdef
  set ρ := pluriformPullback (ι ≫ sX) (ι' ≫ sX') σT.toHom n 1 ρ' with hρdef
  have hρres : IsPoincareResidue sX ι n 1 τ ρ :=
    isPoincareResidue_pluriformPullback ι ι' hn hn' hdT hdT' σ.toHom σT.toHom ψ hψ
      (fun a => (hσT a).symm) hord hρ'
  have hτP : P.ordForm τ = -1 := by
    have hv : ∀ g, (DivisorOver.ofPrimeDivisor k hX' P').valuation g =
        P.divisorialValuation ((σ.toHom) g) := by
      intro g
      change P'.divisorialValuation (functionFieldMap (𝟙 X') g) = _
      rw [MMP.Mori.functionFieldMap_id_apply, hP']
    rw [hτdef, ordForm_pluriformPullback_eq_ordPullback hX hX' hn hn' σ P _ hv τ',
      DivisorOver.ordPullback_ofPrimeDivisor hX' hn' P' τ', hτ'P]
  have hτ0 : τ ≠ 0 := by
    intro h
    rw [h, Mori.PrimeDivisor.ordForm_zero] at hτP
    exact absurd hτP (by decide)
  have hD : (Divisor.toQDivisor (divisorOfForm τ) + B).IsQCartier :=
    hKB.add_of_linearlyEquivalent (by
      simpa using (MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK hτ0).symm)
  have hD' : (Divisor.toQDivisor (divisorOfForm τ') + B').IsQCartier :=
    hKB'.add_of_linearlyEquivalent (by
      simpa using (MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX' hK' hτ'0).symm)
  -- adjunction on both sides
  obtain ⟨hgenT, hpbT⟩ := hι.isPullback_divisorOfForm_add_of_isPoincareResidue
    (by exact_mod_cast hn) P hrP τ hτ0 hτP ρ hρres hD
  obtain ⟨hgenT', hpbT'⟩ := hι'.isPullback_divisorOfForm_add_of_isPoincareResidue
    (by exact_mod_cast hn') P' hrP' τ' hτ'0 hτ'P ρ' hρ' hD'
  -- a common model `W` and the common pull-back `G = G'`
  obtain ⟨W, _, _, p, q, _, _, hpP, hqP, hpb, hqb, hpq, hcompat⟩ :=
    exists_model_of_functionFieldEquiv σ
  have hWp : IsNormalVariety k (p ≫ sX) := isNormalVariety_comp_of_isProper hX p
  have hWq : IsNormalVariety k (q ≫ sX') := isNormalVariety_comp_of_isProper hX' q
  haveI : LocallyOfFiniteType (p ≫ sX) := hWp.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (q ≫ sX') := hWq.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  haveI : CompactSpace W := by
    have := hWp.1
    exact QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  haveI : IsNoetherian X := {}
  haveI : IsNoetherian X' := {}
  have hpB : IsBirationalMorphism p := isBirationalMorphism_of_isBirational' p hpb
  have hqB : IsBirationalMorphism q := isBirationalMorphism_of_isBirational' q hqb
  have hcompat' : ∀ a, functionFieldMap q a = functionFieldMap p ((σ.toHom) a) := fun a => by
    rw [hcompat]
    rfl
  have hgenG := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' p
    (Divisor.toQDivisor (divisorOfForm τ) + B)
  have hgenG' := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' q
    (Divisor.toQDivisor (divisorOfForm τ') + B')
  set G := QDivisor.pullback _ hD hgenG
  have hG := QDivisor.isPullback_pullback hD hgenG
  have hG' := QDivisor.isPullback_pullback hD' hgenG'
  have hGG' := pullback_eq_pullback_of_isCrepantBirationalMap hX hX' σ hσ p q hpB hqB hWp hWq
    hcompat' hτ'0 (isCanonicalDivisor_divisorOfForm hX' hn' hτ'0) hτ0
    (isCanonicalDivisor_divisorOfForm hX hn hτ0) hD hD' hG hG'
  -- the strict transform `Q` of `T` on `W`, over both `T` and `T'`
  obtain ⟨Q, U, hQP, hPU, hUiso, hQv⟩ := exists_primeDivisor_map_genericPoint_eq hX p hpb hWp P
  have hqQ : q Q.genericPoint = P'.genericPoint := by
    let D1 : DivisorOver k sX' := ⟨W, q, hWq, hqB, Q⟩
    have hv : D1.valuation = (DivisorOver.ofPrimeDivisor k hX' P').valuation := by
      ext g
      change Q.divisorialValuation (functionFieldMap q g) =
        P'.divisorialValuation (functionFieldMap (𝟙 X') g)
      rw [MMP.Mori.functionFieldMap_id_apply, hcompat', hQv, hP']
    exact MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX'.1 hv
  -- the normalization `ν : N ⟶ W` of `Q` and the lifts `α : N ⟶ T`, `β : N ⟶ T'`
  obtain ⟨N, _, ν, hNv, hνP, hνη, hνsurj⟩ := exists_normalization_primeDivisor' hWp Q
  haveI := hνP
  haveI : IsNormal N := hNv.2
  have hιη := map_genericPoint_eq_of_range_eq ι P hrP
  have hι'η := map_genericPoint_eq_of_range_eq ι' P' hrP'
  have hpν : p (ν (genericPoint N)) = ι (genericPoint T) := by rw [hνη, hQP, hιη]
  have hqν : q (ν (genericPoint N)) = ι' (genericPoint T') := by rw [hνη, hqQ, hι'η]
  obtain ⟨α, hα⟩ := exists_comp_eq_of_range_subset ι (ν ≫ p)
    (range_comp_subset_of_map_genericPoint ν p ι P hrP (by rw [hpν, hιη]))
  obtain ⟨β, hβ⟩ := exists_comp_eq_of_range_subset ι' (ν ≫ q)
    (range_comp_subset_of_map_genericPoint ν q ι' P' hrP' (by rw [hqν, hι'η]))
  have hαη : α (genericPoint N) = genericPoint T := ι.isClosedEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hα, Scheme.Hom.comp_apply, hpν])
  have hβη : β (genericPoint N) = genericPoint T' := ι'.isClosedEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hβ, Scheme.Hom.comp_apply, hqν])
  haveI : IsDominant α := ⟨Dense.mono (s₁ := {genericPoint T})
    (Set.singleton_subset_iff.mpr ⟨_, hαη⟩) (dense_iff_closure_eq.mpr (genericPoint_spec T))⟩
  haveI : IsDominant β := ⟨Dense.mono (s₁ := {genericPoint T'})
    (Set.singleton_subset_iff.mpr ⟨_, hβη⟩) (dense_iff_closure_eq.mpr (genericPoint_spec T'))⟩
  -- `β^* = α^* ∘ σ_T`, and `α`, `β` are birational
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra sX'
  letI := functionFieldAlgebra (ι ≫ sX)
  letI := functionFieldAlgebra (ι' ≫ sX')
  have hαβ : functionFieldMap β = (functionFieldMap α).comp (σT.toHom).toRingHom :=
    functionFieldMap_eq_comp_of_stalkMap (σ.toHom).toRingHom p q hcompat ι ι' ψ hψ
      (σT.toHom).toRingHom hσT ν α β hα hβ (by rw [hpν]) (by rw [hqν])
  haveI : IsNoetherian T := {}
  haveI : IsNoetherian T' := {}
  have hpiso : IsIso (p.stalkMap (ν (genericPoint N))) :=
    MMP.isIso_stalkMap_of_mem_biregularLocus p
      (le_biregularLocus (f := p) (V := U) hUiso (by rw [hpν, hιη]; exact hPU))
  have hαs := surjective_functionFieldMap_of_lift p ι ν α hα hpν hpiso hνsurj
  have hαbij : Function.Bijective (functionFieldMap α) := ⟨(functionFieldMap α).injective, hαs⟩
  have hβbij : Function.Bijective (functionFieldMap β) := by
    rw [hαβ]
    exact hαbij.comp σT.bijective
  haveI : IsProper α := by
    have : IsProper (α ≫ ι) := by rw [hα]; infer_instance
    exact IsProper.of_comp α ι
  haveI : IsProper β := by
    have : IsProper (β ≫ ι') := by rw [hβ]; infer_instance
    exact IsProper.of_comp β ι'
  have hαB : IsBirationalMorphism α :=
    isBirationalMorphism_of_isBirational' α (isBirational_of_surjective_functionFieldMap α hαs)
  have hβB : IsBirationalMorphism β :=
    isBirationalMorphism_of_isBirational' β (isBirational_of_surjective_functionFieldMap β hβbij.2)
  -- `N` as a normal variety over `k`
  have hsN : α ≫ ι ≫ sX = ν ≫ p ≫ sX := by rw [← Category.assoc, hα, Category.assoc]
  have hsβ : β ≫ ι' ≫ sX' = α ≫ ι ≫ sX := by
    rw [← Category.assoc, hβ, Category.assoc, ← hpq, hsN]
  have hNα : IsNormalVariety k (α ≫ ι ≫ sX) := hsN ▸ hNv
  have hNβ : IsNormalVariety k (β ≫ ι' ≫ sX') := hsβ ▸ hNα
  haveI : LocallyOfFiniteType (α ≫ ι ≫ sX) := hNα.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (β ≫ ι' ≫ sX') := hNβ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian (α ≫ ι ≫ sX)
  haveI : CompactSpace N := by
    have := hNα.1
    exact QuasiCompact.compactSpace_of_compactSpace (α ≫ ι ≫ sX)
  -- the common pull-back `G` vanishes along `Q`
  have hBP := hι.coeff_eq_one hrP
  have hDP : (Divisor.toQDivisor (divisorOfForm τ) + B).coeff P = 0 := by
    rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hτP, hBP]
    norm_num
  have hGQ : G.coeff Q = 0 := by
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy
      (⟨hX, n + 1, K, hK, hKB⟩ : Mori.IsPair sX B) (isCanonicalDivisor_divisorOfForm hX hn hτ0)
      (DivisorOver.ofPrimeDivisor k hX P)
    have hc' : c = -B.coeff P := hc.eq_neg_coeff_of_ofPrimeDivisor hX
    have hlogP := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
      (show IsProper (𝟙 X) by infer_instance)
    have hlogQ := isLogDiscrepancy_of_isPullback hX p hpB hWp hτ0
      (isCanonicalDivisor_divisorOfForm hX hn hτ0) hD hG Q
    have hval : (⟨W, p, hWp, hpB, Q⟩ : DivisorOver k sX).valuation =
        (DivisorOver.ofPrimeDivisor k hX P).valuation := by
      ext g
      change Q.divisorialValuation (functionFieldMap p g) =
        P.divisorialValuation (functionFieldMap (𝟙 X) g)
      rw [MMP.Mori.functionFieldMap_id_apply, hQv]
    have he := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlogQ hlogP hval
    haveI : IsIso (p.stalkMap Q.genericPoint) := by rw [← hνη]; exact hpiso
    have hordQ : Q.ordForm (pullbackRationalPluriForms sX p τ) = P.ordForm τ :=
      MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p hpB.functionFieldMap_bijective
        (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn) Q P hQP τ
    rw [hordQ, hτP, hc', hBP] at he
    have : ((G.coeff Q : ℚ) : ℝ) = 0 := by push_cast at he ⊢; linarith
    exact_mod_cast this
  -- `H = (ν ≫ p)^*(div τ + B)`, computed through `T` and through `W`
  have hgenH : ∀ Z : irreducibleComponents N,
      (ν ≫ p) (componentGenericPoint N Z) ∉ (Divisor.toQDivisor (divisorOfForm τ) + B).supp := by
    intro Z
    rw [componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply, hpν, hιη]
    exact genericPoint_notMem_supp_of_coeff_eq_zero hDP
  have hH := QDivisor.isPullback_pullback hD hgenH
  set H := QDivisor.pullback _ hD hgenH
  have hqT := isQCartier_of_isPullback hD hpbT
  have hqT' := isQCartier_of_isPullback hD' hpbT'
  have hgenα := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' α
    (Divisor.toQDivisor (divisorOfForm ρ) + BT)
  have hgenβ := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' β
    (Divisor.toQDivisor (divisorOfForm ρ') + BT')
  have hEα := QDivisor.isPullback_pullback hqT hgenα
  have hEβ := QDivisor.isPullback_pullback hqT' hgenβ
  have hHα : H = QDivisor.pullback _ hqT hgenα :=
    (QDivisor.IsQCartier.existsUnique_isPullback hD hgenH).unique hH
      (isPullback_of_hom_eq hα (qDivisor_isPullback_comp' ι α hpbT hEα (by rw [hα]; exact hgenH)))
  have hgenν : ∀ Z : irreducibleComponents N, ν (componentGenericPoint N Z) ∉ G.supp := by
    intro Z
    rw [componentGenericPoint_eq_genericPoint, hνη]
    exact genericPoint_notMem_supp_of_coeff_eq_zero hGQ
  have hqG := isQCartier_of_isPullback hD hG
  have hHν := QDivisor.isPullback_pullback hqG hgenν
  have hHHν : H = QDivisor.pullback _ hqG hgenν :=
    (QDivisor.IsQCartier.existsUnique_isPullback hD hgenH).unique hH
      (qDivisor_isPullback_comp' p ν hG hHν hgenH)
  have hgenν' : ∀ Z : irreducibleComponents N,
      ν (componentGenericPoint N Z) ∉ (QDivisor.pullback _ hD' hgenG').supp := by
    rw [← hGG']; exact hgenν
  have hgenH' : ∀ Z : irreducibleComponents N,
      (ν ≫ q) (componentGenericPoint N Z) ∉ (Divisor.toQDivisor (divisorOfForm τ') + B').supp := by
    intro Z
    rw [componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply, hqν, hι'η]
    have hBP' := hι'.coeff_eq_one hrP'
    refine genericPoint_notMem_supp_of_coeff_eq_zero ?_
    rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hτ'P, hBP']
    norm_num
  have hH' : (Divisor.toQDivisor (divisorOfForm τ') + B').IsPullback (ν ≫ q) hgenH' H := by
    rw [hHHν]
    exact qDivisor_isPullback_comp' q ν hG' (isPullback_of_eq_source (h₂ := hgenν') hGG' hHν)
      hgenH'
  have hHβ : H = QDivisor.pullback _ hqT' hgenβ :=
    (QDivisor.IsQCartier.existsUnique_isPullback hD' hgenH').unique hH'
      (isPullback_of_hom_eq hβ (qDivisor_isPullback_comp' ι' β hpbT' hEβ
        (by rw [hβ]; exact hgenH')))
  -- the forms `α^*ρ` and `β^*ρ'` on `N` have the same divisor
  have hcompatN : ∀ a, functionFieldMap β a = functionFieldMap α ((σT.toHom) a) := fun a => by
    rw [hαβ]
    rfl
  have hρ0 : ρ ≠ 0 := by
    intro h0
    apply hρ'0
    have e := pluriformPullback_comp (sX := ι' ≫ sX') (sX' := ι ≫ sX) (sX'' := ι' ≫ sX') hdT' hdT
      hdT' 1 (FunctionFieldEquiv.toHom (ι' ≫ sX') (ι ≫ sX) σT.symm) σT.toHom ρ'
    have h1 : (FunctionFieldEquiv.toHom (ι' ≫ sX') (ι ≫ sX) σT.symm).comp σT.toHom =
        FunctionFieldEquiv.toHom (ι' ≫ sX') (ι' ≫ sX') 1 := by
      ext a
      exact σT.symm_apply_apply a
    rw [← hρdef, h0, map_zero, h1, pluriformPullback_one hdT'] at e
    exact e.symm
  haveI := hT.1
  haveI := hT'.1
  haveI := hNα.1
  haveI := hNβ.1
  have hdN : topologicalKrullDim N = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (ι ≫ sX) (α ≫ ι ≫ sX)
      hαB).symm.trans hdT
  have hdNβ : topologicalKrullDim N = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (ι' ≫ sX') (β ≫ ι' ≫ sX')
      hβB).symm.trans hdT'
  have hρα0 : pullbackRationalPluriForms (ι ≫ sX) α ρ ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' α hαbij
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := ι ≫ sX) hdT) hρ0
  have hρβ0 : pullbackRationalPluriForms (ι' ≫ sX') β ρ' ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' β hβbij
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := ι' ≫ sX') hdT') hρ'0
  have hdivαβ : divisorOfForm (pullbackRationalPluriForms (ι ≫ sX) α ρ) =
      divisorOfForm (pullbackRationalPluriForms (ι' ≫ sX') β ρ') := by
    refine Finsupp.ext fun F => ?_
    change (divisorOfForm _).coeff F = (divisorOfForm _).coeff F
    rw [coeff_divisorOfForm, coeff_divisorOfForm, hρdef]
    exact ordForm_pullback_pluriformPullback_eq hT hT' hdT hdT' σT α β hαB hβB hNα hNβ hcompatN F ρ'
  -- the crepant boundary `C` on `N`, and crepancy of `N ⟶ T` and of `N ⟶ T'`
  set C : QDivisor N := H - Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms (ι ≫ sX) α ρ))
  have hCα : Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms (ι ≫ sX) α ρ)) + C = H :=
    add_sub_cancel _ _
  have hCβ : Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms (ι' ≫ sX') β ρ')) + C =
      H := by
    rw [← hdivαβ]
    exact hCα
  obtain ⟨eα, heα⟩ := exists_functionFieldEquiv_of_comp_eq (sT := ι ≫ sX) α hαbij rfl
  obtain ⟨eβ, heβ⟩ := exists_functionFieldEquiv_of_comp_eq (sT := ι' ≫ sX') β hβbij hsβ
  have crepA : IsCrepantBirationalMap (α ≫ ι ≫ sX) (ι ≫ sX) C BT eα :=
    isCrepantBirationalMap_of_isPullback' hT α hαB hNα hρ0 (isCanonicalDivisor_divisorOfForm hT hdT hρ0)
      hρα0 (isCanonicalDivisor_divisorOfForm hNα hdN hρα0) hqT (by rw [hCα, hHα]; exact hEα) rfl eα
      heα
  have crepB : IsCrepantBirationalMap (α ≫ ι ≫ sX) (ι' ≫ sX') C BT' eβ :=
    isCrepantBirationalMap_of_isPullback' hT' β hβB hNβ hρ'0
      (isCanonicalDivisor_divisorOfForm hT' hdT' hρ'0) hρβ0
      (isCanonicalDivisor_divisorOfForm hNβ hdNβ hρβ0) hqT' (by rw [hCβ, hHβ]; exact hEβ) hsβ eβ heβ
  letI := functionFieldAlgebra (α ≫ ι ≫ sX)
  have hσT' : eβ.trans eα.symm = σT := by
    ext a
    change eα.symm (eβ a) = σT a
    rw [AlgEquiv.symm_apply_eq, heα, heβ, hcompatN]
    rfl
  rw [← hσT']
  exact crepA.symm.trans crepB

end CrepantModel

/-! ### Floor models and single adjunction steps -/

/-- Two reduced closed subschemes with the same underlying set are isomorphic over the ambient
scheme. -/
private theorem exists_iso_comp_eq_of_range_eq {T₁ T₂ Z : Scheme.{0}} [IsReduced T₁]
    [IsReduced T₂] (i₁ : T₁ ⟶ Z) (i₂ : T₂ ⟶ Z) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (h : Set.range i₁.base = Set.range i₂.base) : ∃ ψ : T₁ ≅ T₂, ψ.hom ≫ i₂ = i₁ := by
  obtain ⟨α, hα⟩ := exists_comp_eq_of_range_subset i₂ i₁ h.le
  obtain ⟨β, hβ⟩ := exists_comp_eq_of_range_subset i₁ i₂ h.ge
  refine ⟨⟨α, β, ?_, ?_⟩, hα⟩
  · rw [← cancel_mono i₁, Category.assoc, hβ, hα, Category.id_comp]
  · rw [← cancel_mono i₂, Category.assoc, hα, hβ, Category.id_comp]

/-- **An adjunction step onto a floor component.** On a dlt pair `(Y, B_Y)` of dimension `d + 1`
over `ℂ`, every prime divisor `Q` with `coeff_Q B_Y ≥ 1` is the image of an adjunction step
`T ⟶ Y` with its different `B_T`, and `(T, B_T)` is dlt. -/
private theorem exists_isAdjunctionStep_of_one_le_coeff {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY]
    {BY : QDivisor Y} (hdlt : MMP.Intersection.IsDltPair sY BY) {d : ℕ}
    (hd : topologicalKrullDim Y = (d + 1 : ℕ)) (Q : Mori.PrimeDivisor Y)
    (hQ : 1 ≤ BY.coeff Q) :
    ∃ (T : Scheme.{0}) (jT : T ⟶ Y) (BT : QDivisor T) (hj : IsAdjunctionStep sY BY jT BT),
      Set.range jT.base = (Q.support : Set Y) ∧
        haveI : IsIntegral T := hj.1.1.toIsIntegral
        haveI : IsNormal T := hj.1.2
        haveI : IsLocallyNoetherian T := by
          have := hj.1.1
          exact LocallyOfFiniteType.isLocallyNoetherian (jT ≫ sY)
        MMP.Intersection.IsDltPair (jT ≫ sY) BT := by
  have hinter : (⋂ P ∈ ({Q} : Finset (Mori.PrimeDivisor Y)), (P.support : Set Y)) =
      Q.support := by simp
  have hS : IsDltStratum sY BY (Q.support : Set Y) := by
    refine ⟨hdlt, {Q}, Finset.singleton_nonempty _, by simpa using hQ, ?_, ?_⟩
    · rw [hinter]
      exact ⟨Q.genericPoint, by
        rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩
    · rw [hinter]
      refine ⟨⟨?_, le_rfl⟩, fun T hT _ => hT.2⟩
      rw [PrimeDivisor.support_eq_closure]
      exact isIrreducible_singleton.closure
  obtain ⟨⟨⟨T, ι, BT, hrange, ⟨F⟩⟩, hdltF⟩, -⟩ := hS.exists_isStratumAdjunctionPair_and_isDltPair
  have hdltT := hdltF F hrange
  cases F with
  | refl h =>
    exfalso
    have h1 : genericPoint Y ∈ Set.range (𝟙 Y : Y ⟶ Y).base := ⟨_, rfl⟩
    rw [hrange] at h1
    exact MMP.Threefold.Mori.OpenRestriction.genericPoint_notMem_support Q h1
  | @step S T ι₀ BS F₀ jT BT hj =>
    cases F₀ with
    | refl h =>
      have hj' : IsAdjunctionStep sY BY jT BT := by
        simpa only [Category.id_comp] using hj
      refine ⟨T, jT, BT, hj', by simpa using hrange, ?_⟩
      simpa only [Category.comp_id] using hdltT
    | step F₁ j₁ BT₁ hj₁ =>
      exfalso
      haveI : IsIntegral T := hj.1.1.toIsIntegral
      haveI := (StratumAdjunctionData.step (.step F₁ j₁ BS hj₁) jT BT hj).isClosedImmersion
      have hdT : topologicalKrullDim T = d :=
        topologicalKrullDim_eq_of_range_eq_support sY _ Q hrange hd
      have hlen := StratumAdjunctionData.dim_add_length (sX := sY) hd
        (StratumAdjunctionData.step (.step F₁ j₁ BS hj₁) jT BT hj) hdT
      simp only [StratumAdjunctionData.length] at hlen
      omega

/-- An isomorphism of integral schemes induces a bijection of function fields. -/
private theorem functionFieldMap_bijective_of_isIso {A A' : Scheme.{0}} [IsIntegral A]
    [IsIntegral A'] (e : A ≅ A') : Function.Bijective (functionFieldMap e.hom) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨functionFieldMap e.inv, fun t => ?_, fun t => ?_⟩
  · rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr (Iso.inv_hom_id e), functionFieldMap_id_apply]
  · rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr (Iso.hom_inv_id e), functionFieldMap_id_apply]

/-- **A crepant birational map matching two prime divisors matches their coefficients.** -/
private theorem coeff_eq_of_isCrepantBirationalMap {Y Y' : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    {sY : Y ⟶ Spec (.of ℂ)} {sY' : Y' ⟶ Spec (.of ℂ)} {BY : QDivisor Y} {BY' : QDivisor Y'}
    (hP : MMP.Mori.IsPair sY BY) (hP' : MMP.Mori.IsPair sY' BY') {d d' : ℕ} {K : Divisor Y}
    {K' : Divisor Y'} (hK : K.IsCanonicalDivisor sY d) (hK' : K'.IsCanonicalDivisor sY' d')
    (σ : FunctionFieldEquiv sY sY') (hσ : IsCrepantBirationalMap sY sY' BY BY' σ)
    (P : Mori.PrimeDivisor Y) (P' : Mori.PrimeDivisor Y')
    (hPP : ∀ g, P'.divisorialValuation g = P.divisorialValuation ((σ.toHom) g)) :
    BY'.coeff P' = BY.coeff P := by
  have hX := hP.isNormalVariety
  have hXj := hP'.isNormalVariety
  set DΓ := DivisorOver.ofPrimeDivisor ℂ hX P
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK DΓ
  have hc' : c = -BY.coeff P := hc.eq_neg_coeff_of_ofPrimeDivisor hX
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
    (show IsProper (𝟙 Y) by infer_instance)
  obtain ⟨n', D, hDv, hDlog⟩ := (hσ DΓ.valuation (1 + c)).mp ⟨d, DΓ, rfl, hlog⟩
  set DΓ' := DivisorOver.ofPrimeDivisor ℂ hXj P'
  obtain ⟨c₂, hc₂⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP' hK' DΓ'
  have hc₂' : c₂ = -BY'.coeff P' := hc₂.eq_neg_coeff_of_ofPrimeDivisor hXj
  have hlog' := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc₂
    (show IsProper (𝟙 Y') by infer_instance)
  have hv : D.valuation = DΓ'.valuation := by
    ext g
    rw [hDv]
    change P.divisorialValuation (functionFieldMap (𝟙 Y) _) =
      P'.divisorialValuation (functionFieldMap (𝟙 Y') g)
    rw [functionFieldMap_id_apply, functionFieldMap_id_apply, hPP]
    rfl
  have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hDlog hlog' hv
  have h2 : ((c : ℚ) : ℝ) = ((c₂ : ℚ) : ℝ) := by linarith
  have h3 : c = c₂ := by exact_mod_cast h2
  rw [hc', hc₂'] at h3
  linarith

/-- The divisorial valuation of a prime divisor depends only on its generic point. -/
private theorem divisorialValuation_eq_of_genericPoint_eq {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {E E' : Mori.PrimeDivisor Y}
    (h : E.genericPoint = E'.genericPoint) (g : Y.functionField) :
    E.divisorialValuation g = E'.divisorialValuation g := by
  by_cases hg : g = 0
  · rw [hg, map_zero, map_zero]
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg, h]

/-- **Divisorial valuations under an isomorphism.** If `ψ : Y ≅ Z` carries the generic point of
`Q` to that of `Q'`, then `v_{Q'} = v_Q ∘ ψ^*`. -/
private theorem divisorialValuation_eq_of_iso {Y Z : Scheme.{0}} [IsIntegral Y] [IsNoetherian Y]
    [IsNormal Y] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] {sY : Y ⟶ Spec (.of ℂ)}
    (hYn : IsNormalVariety ℂ sY) (ψ : Y ≅ Z) (hZn : IsNormalVariety ℂ (ψ.inv ≫ sY))
    (Q : Mori.PrimeDivisor Y) (Q' : Mori.PrimeDivisor Z) (h : ψ.hom Q.genericPoint = Q'.genericPoint)
    (g : Z.functionField) :
    Q'.divisorialValuation g = Q.divisorialValuation (functionFieldMap ψ.hom g) := by
  have hbir : IsBirational ψ.inv := by
    have : IsIso (ψ.inv.stalkMap (genericPoint Z)) :=
      ((isIso_iff_isIso_stalkMap ψ.inv).mp inferInstance).2 _
    exact isBirational_of_isIso_stalkMap_genericPoint ψ.inv
  obtain ⟨Q'', -, hQ''g, -, -, hQ''v⟩ :=
    exists_primeDivisor_map_genericPoint_eq (k := ℂ) hYn ψ.inv hbir hZn Q
  have hgen : Q''.genericPoint = Q'.genericPoint := by
    rw [← h, ← hQ''g, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  have h1 := hQ''v (functionFieldMap ψ.hom g)
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_congr (Iso.inv_hom_id ψ),
    functionFieldMap_id_apply, divisorialValuation_eq_of_genericPoint_eq hgen] at h1
  exact h1

/-- **The local ring of an adjunction step under an isomorphism.** If `ψ_T : T ≅ T'` lies over
`ψ : Y ≅ Z`, with `T ⟶ Y`, `T' ⟶ Z` closed immersions onto prime divisors `Q`, `Q'`, then `ψ`
induces a map `𝒪_{Z,Q'} → 𝒪_{Y,Q}` compatible with `ψ^*` on function fields, with `ψ_T^*` on the
residue fields `k(T') → k(T)`, and with orders; and `v_{Q'} = v_Q ∘ ψ^*`. -/
private theorem exists_stalkHom_of_iso
    {Y Z T T' : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hYn : IsNormalVariety ℂ sY) (hZn : IsNormalVariety ℂ sZ)
    (ψ : Y ≅ Z) (hψs : ψ.hom ≫ sZ = sY)
    (σ : FunctionFieldEquiv sY sZ) (hσ : ∀ a, σ a = functionFieldMap ψ.hom a)
    [IsIntegral T] [IsIntegral T'] {jT : T ⟶ Y} {jT' : T' ⟶ Z} [IsClosedImmersion jT]
    [IsClosedImmersion jT'] (Q : Mori.PrimeDivisor Y) (Q' : Mori.PrimeDivisor Z)
    (hQr : Set.range jT.base = (Q.support : Set Y)) (hQ'r : Set.range jT'.base = (Q'.support : Set Z))
    (ψT : T ≅ T') (hψT : ψT.hom ≫ jT' = jT ≫ ψ.hom)
    (σT : FunctionFieldEquiv (jT ≫ sY) (jT' ≫ sZ)) (hσT : ∀ a, σT a = functionFieldMap ψT.hom a) :
    ∃ ψs : Z.presheaf.stalk (jT' (genericPoint T')) →+* Y.presheaf.stalk (jT (genericPoint T)),
      (∀ a, algebraMap _ Y.functionField (ψs a) = (σ.toHom) (algebraMap _ Z.functionField a)) ∧
      (∀ a, (σT.toHom) ((jT'.stalkMap (genericPoint T')).hom a) =
        (jT.stalkMap (genericPoint T)).hom (ψs a)) ∧
      (∀ a, Y.ord (algebraMap _ Y.functionField (ψs a)) (jT (genericPoint T)) =
        Z.ord (algebraMap _ Z.functionField a) (jT' (genericPoint T'))) ∧
      ∀ g, Q'.divisorialValuation g = Q.divisorialValuation ((σ.toHom) g) := by
  haveI : IsNoetherian Y := {}
  have hsZ : ψ.inv ≫ sY = sZ := by rw [← hψs, Iso.inv_hom_id_assoc]
  have hr : Set.range (jT ≫ ψ.hom).base = (Q'.support : Set Z) := by
    rw [← hψT, ← hQ'r, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      (ConcreteCategory.bijective_of_isIso ψT.hom.base).2.range_eq, Set.image_univ]
  have e1 : jT (genericPoint T) = Q.genericPoint := map_genericPoint_eq_of_range_eq jT Q hQr
  have e2 : jT' (genericPoint T') = Q'.genericPoint := map_genericPoint_eq_of_range_eq jT' Q' hQ'r
  have hgen : ψ.hom Q.genericPoint = Q'.genericPoint := by
    rw [← e1]
    exact map_genericPoint_eq_of_range_eq (jT ≫ ψ.hom) Q' hr
  have hvQ : ∀ g, Q'.divisorialValuation g = Q.divisorialValuation ((σ.toHom) g) := by
    intro g
    rw [divisorialValuation_eq_of_iso hYn ψ (by rw [hsZ]; exact hZn) Q Q' hgen g]
    exact congrArg _ (hσ g).symm
  have hsp : ψ.hom (jT (genericPoint T)) ⤳ jT' (genericPoint T') := by
    rw [e1, e2, hgen]
  have hψs' : ∀ a, algebraMap _ Y.functionField
      ((Z.presheaf.stalkSpecializes hsp ≫ ψ.hom.stalkMap (jT (genericPoint T))).hom a) =
      (σ.toHom) (algebraMap _ Z.functionField a) := by
    intro a
    have h := congrArg (fun φ => φ.hom a)
      (stalkSpecializes_stalkMap_algebraMap ψ.hom (jT (genericPoint T)) _ hsp)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    change _ = σ _
    rw [hσ]
    exact h
  refine ⟨_, hψs', fun a => ?_, fun a => ?_, hvQ⟩
  · change σT _ = _
    rw [hσT]
    exact (stalkMap_apply_eq_functionFieldMap_apply ψ.hom jT' jT ψT.hom hψT hsp a).symm
  · rw [hψs']
    generalize algebraMap _ Z.functionField a = x
    rw [e1, e2]
    by_cases hx : x = 0
    · rw [hx, map_zero, Scheme.ord_zero, Scheme.ord_zero]
      rfl
    have hσx : (σ.toHom) x ≠ 0 := (map_ne_zero _).mpr hx
    have h1 := hvQ x
    rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hx,
      MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hσx] at h1
    have h2 := WithZero.exp_injective h1
    omega

/-- **An isomorphism of adjunction steps over a crepant isomorphism is crepant.** Let
`ψ : Y ≅ Z` be an isomorphism of normal projective varieties over `ℂ` identifying `(Y, B_Y)`
and `(Z, B_Z)` crepantly, and `T ⟶ Y`, `T' ⟶ Z` adjunction steps identified by an isomorphism
`ψ_T : T ≅ T'` over `ψ`. Then `ψ_T` identifies the adjunction pairs `(T, B_T)` and `(T', B_T')`
crepantly. -/
private theorem isCrepantBirationalMap_of_isAdjunctionStep_of_iso
    {Y Z T T' : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY] [IsProper sY]
    [LocallyOfFiniteType sZ] [IsProper sZ]
    (hYn : IsNormalVariety ℂ sY) (hZn : IsNormalVariety ℂ sZ) {d : ℕ}
    (hd : topologicalKrullDim Y = (d + 1 : ℕ)) (hdZ : topologicalKrullDim Z = (d + 1 : ℕ))
    {BY : QDivisor Y} {BZ : QDivisor Z} {K : Divisor Y} {KZ : Divisor Z}
    (hK : K.IsCanonicalDivisor sY (d + 1)) (hKZ : KZ.IsCanonicalDivisor sZ (d + 1))
    (hKB : (Divisor.toQDivisor K + BY).IsQCartier)
    (hKBZ : (Divisor.toQDivisor KZ + BZ).IsQCartier)
    (ψ : Y ≅ Z) (hψs : ψ.hom ≫ sZ = sY)
    (σ : FunctionFieldEquiv sY sZ) (hσ : ∀ a, σ a = functionFieldMap ψ.hom a)
    (hσc : IsCrepantBirationalMap sY sZ BY BZ σ)
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [IsIntegral T'] [IsLocallyNoetherian T']
    [IsNormal T'] {jT : T ⟶ Y} {jT' : T' ⟶ Z} {BT : QDivisor T} {BT' : QDivisor T'}
    (hj : IsAdjunctionStep sY BY jT BT) (hjT' : IsAdjunctionStep sZ BZ jT' BT')
    (ψT : T ≅ T') (hψT : ψT.hom ≫ jT' = jT ≫ ψ.hom)
    (σT : FunctionFieldEquiv (jT ≫ sY) (jT' ≫ sZ)) (hσT : ∀ a, σT a = functionFieldMap ψT.hom a) :
    IsCrepantBirationalMap (jT ≫ sY) (jT' ≫ sZ) BT BT' σT := by
  obtain ⟨-, Q, -, hQr, hci, -⟩ := id hj
  obtain ⟨-, Q', -, hQ'r, hci', -⟩ := id hjT'
  haveI := hci
  haveI := hci'
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace jT
  haveI : CompactSpace T' := QuasiCompact.compactSpace_of_compactSpace jT'
  obtain ⟨ψs, hψs', hψT', hord, hvQ⟩ :=
    exists_stalkHom_of_iso hYn hZn ψ hψs σ hσ Q Q' hQr hQ'r ψT hψT σT hσT
  exact isCrepantBirationalMap_of_isAdjunctionStep (k := ℂ) hYn hZn hd hdZ hK hKZ hKB hKBZ σ hσc
    hj hjT' Q Q' hQr hQ'r hvQ ψs hψs' hord σT hψT'

/-- **Poincaré residues under an isomorphism of adjunction steps.** If `ψ_T : T ≅ T'` lies over
`ψ : Y ≅ Z` and `T ⟶ Y`, `T' ⟶ Z` are closed immersions onto prime divisors, then
`Res_T(ψ^*τ) = ψ_T^* Res_{T'}(τ)`. -/
private theorem isPoincareResidue_pluriformPullback_of_iso
    {Y Z T T' : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY]
    [LocallyOfFiniteType sZ] (hYn : IsNormalVariety ℂ sY) (hZn' : IsNormalVariety ℂ sZ) {d : ℕ}
    (hd : topologicalKrullDim Y = (d + 1 : ℕ)) (hdZ : topologicalKrullDim Z = (d + 1 : ℕ))
    (ψ : Y ≅ Z) (hψs : ψ.hom ≫ sZ = sY)
    (σ : FunctionFieldEquiv sY sZ) (hσ : ∀ a, σ a = functionFieldMap ψ.hom a)
    [IsIntegral T] [IsIntegral T'] {jT : T ⟶ Y} {jT' : T' ⟶ Z} [IsClosedImmersion jT]
    [IsClosedImmersion jT'] [LocallyOfFiniteType (jT ≫ sY)] [LocallyOfFiniteType (jT' ≫ sZ)]
    (Q : Mori.PrimeDivisor Y) (Q' : Mori.PrimeDivisor Z)
    (hQr : Set.range jT.base = (Q.support : Set Y)) (hQ'r : Set.range jT'.base = (Q'.support : Set Z))
    (ψT : T ≅ T') (hψT : ψT.hom ≫ jT' = jT ≫ ψ.hom)
    (σT : FunctionFieldEquiv (jT ≫ sY) (jT' ≫ sZ)) (hσT : ∀ a, σT a = functionFieldMap ψT.hom a)
    {N : ℕ} {τ : RationalPluriForms sZ (d + 1) N} {ρ : RationalPluriForms (jT' ≫ sZ) d N}
    (h : IsPoincareResidue sZ jT' d N τ ρ) :
    IsPoincareResidue sY jT d N (pluriformPullback sY sZ σ.toHom (d + 1) N τ)
      (pluriformPullback (jT ≫ sY) (jT' ≫ sZ) σT.toHom d N ρ) := by
  obtain ⟨ψs, hψs', hψT', hord, -⟩ :=
    exists_stalkHom_of_iso hYn hZn' ψ hψs σ hσ Q Q' hQr hQ'r ψT hψT σT hσT
  exact isPoincareResidue_pluriformPullback jT jT' hd hdZ
    (topologicalKrullDim_eq_of_range_eq_support sY jT Q hQr hd)
    (topologicalKrullDim_eq_of_range_eq_support sZ jT' Q' hQ'r hdZ) σ.toHom σT.toHom ψs hψs'
    (fun a => (hψT' a).symm) hord h

/-- **One adjunction step, carried across a crepant isomorphism.** Let `ψ : Y ≅ Z` be an
isomorphism of normal projective varieties over `ℂ` identifying the pairs `(Y, B_Y)` and
`(Z, B_Z)` crepantly, with `(Z, B_Z)` dlt. For an adjunction step `T ⟶ Y` onto `Q` there is an
adjunction step `T' ⟶ Z` onto `ψ(Q)` with `(T', B_T')` dlt, and an isomorphism `T ≅ T'` over `ψ`
identifying `(T, B_T)` and `(T', B_T')` crepantly. -/
private theorem exists_isAdjunctionStep_iso_of_isAdjunctionStep
    {Y Z T : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY] [IsProper sY]
    [LocallyOfFiniteType sZ] [IsProper sZ]
    (hYn : IsNormalVariety ℂ sY) (hZn : IsNormalVariety ℂ sZ) {d : ℕ}
    (hd : topologicalKrullDim Y = (d + 1 : ℕ)) (hdZ : topologicalKrullDim Z = (d + 1 : ℕ))
    {BY : QDivisor Y} {BZ : QDivisor Z} {K : Divisor Y} {KZ : Divisor Z}
    (hK : K.IsCanonicalDivisor sY (d + 1)) (hKZ : KZ.IsCanonicalDivisor sZ (d + 1))
    (hKB : (Divisor.toQDivisor K + BY).IsQCartier)
    (hKBZ : (Divisor.toQDivisor KZ + BZ).IsQCartier)
    (hPY : MMP.Mori.IsPair sY BY) (hPZ : MMP.Mori.IsPair sZ BZ)
    (hdltZ : MMP.Intersection.IsDltPair sZ BZ)
    (ψ : Y ≅ Z) (hψs : ψ.hom ≫ sZ = sY)
    (σ : FunctionFieldEquiv sY sZ) (hσ : ∀ a, σ a = functionFieldMap ψ.hom a)
    (hσc : IsCrepantBirationalMap sY sZ BY BZ σ)
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] {jT : T ⟶ Y} {BT : QDivisor T}
    (hj : IsAdjunctionStep sY BY jT BT) :
    ∃ (T' : Scheme.{0}) (jT' : T' ⟶ Z) (BT' : QDivisor T') (hjT' : IsAdjunctionStep sZ BZ jT' BT')
      (ψT : T ≅ T'), ψT.hom ≫ jT' = jT ≫ ψ.hom ∧
      haveI : IsIntegral T' := hjT'.1.1.toIsIntegral
      haveI : IsNormal T' := hjT'.1.2
      haveI : IsLocallyNoetherian T' := by
        have := hjT'.1.1
        exact LocallyOfFiniteType.isLocallyNoetherian (jT' ≫ sZ)
      MMP.Intersection.IsDltPair (jT' ≫ sZ) BT' ∧
      ∃ σT : FunctionFieldEquiv (jT ≫ sY) (jT' ≫ sZ),
        (∀ a, σT a = functionFieldMap ψT.hom a) ∧
        IsCrepantBirationalMap (jT ≫ sY) (jT' ≫ sZ) BT BT' σT := by
  classical
  obtain ⟨-, Q, hQ1, hQr, hci, -⟩ := id hj
  haveI := hci
  haveI : IsNoetherian Y := {}
  have hsZ : ψ.inv ≫ sY = sZ := by rw [← hψs, Iso.inv_hom_id_assoc]
  have hbir : IsBirational ψ.inv := by
    have : IsIso (ψ.inv.stalkMap (genericPoint Z)) :=
      ((isIso_iff_isIso_stalkMap ψ.inv).mp inferInstance).2 _
    exact isBirational_of_isIso_stalkMap_genericPoint ψ.inv
  obtain ⟨Q', -, hQ'g, -, -, -⟩ := exists_primeDivisor_map_genericPoint_eq (k := ℂ) hYn ψ.inv
    hbir (by rw [hsZ]; exact hZn) Q
  have hgen : ψ.hom Q.genericPoint = Q'.genericPoint := by
    rw [← hQ'g, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  have hvQ : ∀ g, Q'.divisorialValuation g = Q.divisorialValuation ((σ.toHom) g) := by
    intro g
    rw [divisorialValuation_eq_of_iso hYn ψ (by rw [hsZ]; exact hZn) Q Q' hgen g]
    exact congrArg _ (hσ g).symm
  have hcoef : BZ.coeff Q' = BY.coeff Q :=
    coeff_eq_of_isCrepantBirationalMap hPY hPZ hK hKZ σ hσc Q Q' hvQ
  obtain ⟨T', jT', BT', hjT', hrT', hdltT'⟩ :=
    exists_isAdjunctionStep_of_one_le_coeff hdltZ hdZ Q' (hcoef ▸ hQ1)
  haveI : IsIntegral T' := hjT'.1.1.toIsIntegral
  haveI : IsNormal T' := hjT'.1.2
  haveI : IsLocallyNoetherian T' := by
    have := hjT'.1.1
    exact LocallyOfFiniteType.isLocallyNoetherian (jT' ≫ sZ)
  obtain ⟨-, -, -, -, hci', -⟩ := id hjT'
  haveI := hci'
  have hrange : Set.range (jT ≫ ψ.hom).base = Set.range jT'.base := by
    rw [hrT', Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hQr,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have h := (Scheme.homeoOfIso ψ).image_closure {Q.genericPoint}
    rw [Set.image_singleton] at h
    change ψ.hom.base '' _ = _
    erw [h]
    change closure {ψ.hom Q.genericPoint} = _
    rw [hgen]
  obtain ⟨ψT, hψT⟩ := exists_iso_comp_eq_of_range_eq (jT ≫ ψ.hom) jT' hrange
  have hsT : ψT.hom ≫ jT' ≫ sZ = jT ≫ sY := by
    rw [← Category.assoc, hψT, Category.assoc, hψs]
  obtain ⟨σT, hσT⟩ := exists_functionFieldEquiv_of_comp_eq (k := ℂ) ψT.hom
    (functionFieldMap_bijective_of_isIso ψT) hsT
  exact ⟨T', jT', BT', hjT', ψT, hψT, hdltT', σT, hσT,
    isCrepantBirationalMap_of_isAdjunctionStep_of_iso hYn hZn hd hdZ hK hKZ hKB hKBZ ψ hψs σ hσ
      hσc hj hjT' ψT hψT σT hσT⟩

/-! ### Changing the structure morphism by an equality -/

/-- A crepant birational map along equal structure morphisms. -/
private theorem exists_isCrepantBirationalMap_congr {S S' : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] [IsIntegral S'] [IsLocallyNoetherian S'] [IsNormal S']
    {s₁ s₁' : S ⟶ Spec (.of ℂ)} {s₂ s₂' : S' ⟶ Spec (.of ℂ)} (h₁ : s₁ = s₁') (h₂ : s₂ = s₂')
    {B : QDivisor S} {B' : QDivisor S'} (σ : FunctionFieldEquiv s₁ s₂)
    (hσ : IsCrepantBirationalMap s₁ s₂ B B' σ) :
    ∃ σ' : FunctionFieldEquiv s₁' s₂', (∀ a, (σ'.toHom) a = (σ.toHom) a) ∧
      IsCrepantBirationalMap s₁' s₂' B B' σ' := by
  subst h₁ h₂
  exact ⟨σ, fun _ => rfl, hσ⟩

/-- Pull-backs of forms along equal structure morphisms agree. -/
private theorem pluriformPullback_heq {S S' : Scheme.{0}} [IsIntegral S] [IsIntegral S']
    {s₁ s₁' : S ⟶ Spec (.of ℂ)} {s₂ s₂' : S' ⟶ Spec (.of ℂ)} (h₁ : s₁ = s₁') (h₂ : s₂ = s₂')
    (σ : FunctionFieldEquiv s₁ s₂) (σ' : FunctionFieldEquiv s₁' s₂')
    (hσ : ∀ a, (σ'.toHom) a = (σ.toHom) a)
    {e : ℕ} {N : ℤ} {ρ : RationalPluriForms s₂ e N} {ρ' : RationalPluriForms s₂' e N}
    (hρ : HEq ρ ρ') :
    HEq (pluriformPullback s₁ s₂ σ.toHom e N ρ) (pluriformPullback s₁' s₂' σ'.toHom e N ρ') := by
  subst h₁ h₂
  letI := functionFieldAlgebra s₁
  letI := functionFieldAlgebra s₂
  have : σ' = σ := AlgEquiv.ext fun a => hσ a
  subst this
  rw [eq_of_heq hρ]

/-- Poincaré residues along equal structure morphisms. -/
private theorem isPoincareResidue_congr {Y T : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsIntegral T] (jT : T ⟶ Y) {s s' : Y ⟶ Spec (.of ℂ)} (h : s = s') {e N : ℕ}
    {τ : RationalPluriForms s (e + 1) N} {τ' : RationalPluriForms s' (e + 1) N}
    {ρ : RationalPluriForms (jT ≫ s) e N} {ρ' : RationalPluriForms (jT ≫ s') e N}
    (hτ : HEq τ τ') (hρ : HEq ρ ρ') (hr : IsPoincareResidue s jT e N τ ρ) :
    IsPoincareResidue s' jT e N τ' ρ' := by
  subst h
  rw [← eq_of_heq hτ, ← eq_of_heq hρ]
  exact hr

/-- Dlt pairs along equal structure morphisms. -/
private theorem isDltPair_congr {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    {s s' : S ⟶ Spec (.of ℂ)} (h : s = s') {B : QDivisor S} (hB : MMP.Intersection.IsDltPair s B) :
    MMP.Intersection.IsDltPair s' B := h ▸ hB

/-! ### Powers of forms on a line -/

/-- **Equal forms have equal powers.** On a line `Ω^d_{K/ℂ}`, if `c ω^{⊗m} = c' ω'^{⊗m}` with
`m > 0`, then `c^a ω^{⊗am} = c'^a ω'^{⊗am}`. -/
private theorem smul_formPow_pow_eq {K : Type*} [Field K] [Algebra ℂ K] {d : ℕ}
    (b : Module.Basis Unit K (⋀[K]^d Ω[K⁄ℂ])) {m : ℕ} {w w' : ⋀[K]^d Ω[K⁄ℂ]} {c c' : K}
    (h : (c • formPow w m : PluriForms ℂ K d m) = c' • formPow w' m) (a : ℕ) :
    (c ^ a • formPow w (a * m) : PluriForms ℂ K d ((a * m : ℕ) : ℤ)) =
      c' ^ a • formPow w' (a * m) := by
  rw [← basis_unit_repr_smul b w, ← basis_unit_repr_smul b w'] at h ⊢
  simp only [formPow_smul, smul_smul] at h ⊢
  have h1 := congrArg (fun τ => (ZTensorPower.basis b m).repr τ ()) h
  simp only [repr_smul_formPow] at h1
  have key : ∀ x y : K, x ^ a * y ^ (a * m) = (x * y ^ m) ^ a := fun x y => by ring
  rw [key, key, h1]

/-- **Powers of iterated residues.** Along a flag ending at a stratum of dimension `e`, if
`c ω^{⊗m}` has iterated residue `c₁ ω₁^{⊗m}`, then `c^a ω^{⊗am}` has iterated residue
`c₁^a ω₁^{⊗am}` for every `a > 0`. -/
private theorem isIteratedResidueRec_pow {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {BY : QDivisor Y} {n m : ℕ}
    (ω : letI := functionFieldAlgebra sY; ⋀[Y.functionField]^n Ω[Y.functionField⁄ℂ])
    (c : Y.functionField) {S : Scheme.{0}} [IsIntegral S] {ι : S ⟶ Y} {BS : QDivisor S}
    (G : StratumAdjunctionData sY BY ι BS) {e : ℕ} (he : topologicalKrullDim S = e)
    (ω₁ : letI := functionFieldAlgebra (ι ≫ sY); ⋀[S.functionField]^e Ω[S.functionField⁄ℂ])
    (c₁ : S.functionField)
    (h : letI := functionFieldAlgebra sY; letI := functionFieldAlgebra (ι ≫ sY)
      IsIteratedResidueRec (c • (formPow ω m : RationalPluriForms sY n m)) G e
      (c₁ • (formPow ω₁ m : RationalPluriForms (ι ≫ sY) e m))) :
    letI := functionFieldAlgebra sY; letI := functionFieldAlgebra (ι ≫ sY)
    ∀ a, 0 < a → IsIteratedResidueRec
      (c ^ a • (formPow ω (a * m) : RationalPluriForms sY n ((a * m : ℕ) : ℤ))) G e
      (c₁ ^ a • (formPow ω₁ (a * m) : RationalPluriForms (ι ≫ sY) e ((a * m : ℕ) : ℤ))) := by
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (ι ≫ sY)
  intro a ha
  suffices H : ∀ N : ℕ, N = a * m → IsIteratedResidueRec
      (c ^ a • (formPow ω N : RationalPluriForms sY n N)) G e
      (c₁ ^ a • (formPow ω₁ N : RationalPluriForms (ι ≫ sY) e N)) from H _ rfl
  induction a, ha using Nat.le_induction with
  | base =>
    intro N hN
    rw [Nat.succ_eq_add_one, zero_add, one_mul] at hN
    subst hN
    simpa only [pow_one] using h
  | succ a ha ih =>
    intro N hN
    have hmul := IsIteratedResidueRec.mul G he (ih _ rfl) h
    rw [RationalPluriForms.mul_smul_formPow, RationalPluriForms.mul_smul_formPow, ← pow_succ,
      ← pow_succ] at hmul
    rw [Nat.succ_mul] at hN
    subst hN
    exact hmul

/-! ### Matching flags of `(X, B)` with flags of the floor components -/

/-- **Every flag of positive length of `(X, B)` is a flag of a floor component.** A flag
`X ⊃ T₁ ⊃ ⋯ ⊃ S` of iterated adjunction of `(X, B)` starts at a model `T₁` of a floor component
`P`; it is matched by a flag `C_P ⊃ ⋯ ⊃ S'` of `(C_P, B_{C_P})`, one step shorter, with an
isomorphism `S ≅ S'` over `X` which identifies the adjunction pairs crepantly and carries the
iterated residues of a form `τ` along `X ⊃ ⋯ ⊃ S` to those of its residue along `C_P`. -/
private theorem exists_flagMatch
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : Mori.IsProjectiveVariety ℂ sX) {n : ℕ}
    (hdim : topologicalKrullDim X = (n + 1 : ℕ)) {B : QDivisor X}
    {C : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} → Scheme.{0}}
    [∀ P, IsIntegral (C P)] [∀ P, IsLocallyNoetherian (C P)] [∀ P, IsNormal (C P)]
    {j : ∀ P, C P ⟶ X} {BC : ∀ P, QDivisor (C P)} {m : ℕ}
    (hC : ∀ P, IsAdjunctionStep sX B (j P) (BC P) ∧
      Set.range (j P).base = (P.1.support : Set X))
    (hset : IsStratifiedSectionSetting (fun P => j P ≫ sX) BC n m)
    (hcanX : ∀ {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S}
      (F : StratumAdjunctionData sX B ι BS),
      haveI := F.isIntegral_stratum
      haveI := F.isNormal_stratum
      haveI := F.isLocallyNoetherian_stratum
      ∃ (d : ℕ) (K : Divisor S), K.IsCanonicalDivisor (ι ≫ sX) d ∧
        (Divisor.toQDivisor K + BS).IsQCartier) :
    ∀ {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS),
      1 ≤ F.length →
      ∃ (P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0}) (S' : Scheme.{0}) (ι' : S' ⟶ C P)
        (BS' : QDivisor S') (F' : StratumAdjunctionData (j P ≫ sX) (BC P) ι' BS') (ψ : S ≅ S'),
        F'.length + 1 = F.length ∧ ψ.hom ≫ ι' ≫ j P = ι ∧
        (haveI := F'.isIntegral_stratum
         haveI := F'.isNormal_stratum
         haveI := F'.isLocallyNoetherian_stratum
         MMP.Intersection.IsDltPair (ι' ≫ j P ≫ sX) BS') ∧
        haveI := F.isIntegral_stratum
        haveI := F.isNormal_stratum
        haveI := F.isLocallyNoetherian_stratum
        haveI := F'.isIntegral_stratum
        haveI := F'.isNormal_stratum
        haveI := F'.isLocallyNoetherian_stratum
        ∃ σ : FunctionFieldEquiv (ι ≫ sX) (ι' ≫ j P ≫ sX),
          (∀ a, (σ.toHom) a = functionFieldMap ψ.hom a) ∧
          IsCrepantBirationalMap (ι ≫ sX) (ι' ≫ j P ≫ sX) BS BS' σ ∧
          ∀ (N : ℕ) (τ : RationalPluriForms sX (n + 1) N)
            (ρP : RationalPluriForms (j P ≫ sX) n N), IsPoincareResidue sX (j P) n N τ ρP →
            ∀ (e : ℕ), topologicalKrullDim S = e →
            ∀ ρ' : RationalPluriForms (ι' ≫ j P ≫ sX) e N, IsIteratedResidueRec ρP F' e ρ' →
              IsIteratedResidueRec τ F e
                (pluriformPullback (ι ≫ sX) (ι' ≫ j P ≫ sX) σ.toHom e N ρ') := by
  classical
  haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
  have hXn : IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
  have hCproper : ∀ P, IsProper (j P ≫ sX) := fun P =>
    isProper_of_isProjectiveMorphism _ (hset.isProjectiveVariety P).isProjective
  intro S ι BS F
  induction F with
  | refl h => intro hF; simp [StratumAdjunctionData.length] at hF
  | @step S₀ T ι₀ BS₀ F₀ jT BT hj ih =>
    intro _
    haveI := F₀.isIntegral_stratum
    haveI := F₀.isNormal_stratum
    haveI := F₀.isLocallyNoetherian_stratum
    haveI := F₀.isClosedImmersion
    haveI : IsIntegral T := hj.1.1.toIsIntegral
    haveI : IsNormal T := hj.1.2
    haveI : IsLocallyNoetherian T := by
      have := hj.1.1
      exact LocallyOfFiniteType.isLocallyNoetherian (jT ≫ ι₀ ≫ sX)
    by_cases h0 : F₀.length = 0
    · -- the first step `X ⊃ T`, matched with `C_P` itself
      cases F₀ with
      | step F₁ j₁ BT₁ hj₁ => simp [StratumAdjunctionData.length] at h0
      | refl hp =>
        have hj' : IsAdjunctionStep sX B jT BT := by simpa only [Category.id_comp] using hj
        obtain ⟨-, Q, hQ1, hQr, hci, -⟩ := id hj'
        haveI := hci
        have hfl : ⌊B.coeff Q⌋ ≠ 0 := by
          have : (1 : ℤ) ≤ ⌊B.coeff Q⌋ := Int.le_floor.mpr (by exact_mod_cast hQ1)
          omega
        let P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} := ⟨Q, hfl⟩
        have hPr : Set.range (j P).base = (Q.support : Set X) := (hC P).2
        obtain ⟨-, -, -, -, hciP, -⟩ := id (hC P).1
        haveI := hciP
        obtain ⟨ψ, hψ⟩ := exists_iso_comp_eq_of_range_eq jT (j P) (hQr.trans hPr.symm)
        obtain ⟨-, d, K, hK, hKB⟩ := hp
        have hd : d = n + 1 := by
          have := hK.topologicalKrullDim_eq
          rw [hdim] at this
          exact_mod_cast this.symm
        subst hd
        have hσ0 : ∀ a, (1 : FunctionFieldEquiv sX sX) a = functionFieldMap (Iso.refl X).hom a :=
          fun a => (functionFieldMap_id_apply a).symm
        have hσc0 : IsCrepantBirationalMap sX sX B B 1 := (crepantBirationalAutomorphisms sX B).one_mem
        have hψX : ψ.hom ≫ j P = jT ≫ (Iso.refl X).hom := by rw [hψ]; rfl
        have hsT : ψ.hom ≫ j P ≫ sX = jT ≫ sX := by rw [← Category.assoc, hψ]
        obtain ⟨σT, hσT⟩ := exists_functionFieldEquiv_of_comp_eq (k := ℂ) ψ.hom
          (functionFieldMap_bijective_of_isIso ψ) hsT
        have hcrep := isCrepantBirationalMap_of_isAdjunctionStep_of_iso hXn hXn hdim hdim hK hK hKB
          hKB (Iso.refl X) (Category.id_comp sX) 1 hσ0 hσc0 hj' (hC P).1 ψ hψX σT hσT
        obtain ⟨σ, hσσ, hσcrep⟩ := exists_isCrepantBirationalMap_congr
          (show jT ≫ sX = (jT ≫ 𝟙 X) ≫ sX by simp)
          (show j P ≫ sX = 𝟙 (C P) ≫ j P ≫ sX by simp) σT hcrep
        refine ⟨P, C P, 𝟙 _, BC P, .refl (hset.isPair P).isPair, ψ,
          by simp [StratumAdjunctionData.length], by simp [hψ],
          isDltPair_congr (Category.id_comp _).symm (hset.isDltPair P),
          σ, fun a => (hσσ a).trans (hσT a), hσcrep, ?_⟩
        intro N τ ρP hres e he ρ' hiter
        obtain ⟨rfl, hρ⟩ := hiter
        have hclean := isPoincareResidue_pluriformPullback_of_iso hXn hXn hdim hdim (Iso.refl X)
          (Category.id_comp sX) 1 hσ0 Q Q hQr hPr ψ hψX σT hσT hres
        rw [pluriformPullback_one (by exact_mod_cast hdim)] at hclean
        have h₁ : (jT ≫ 𝟙 X) ≫ sX = jT ≫ sX := by rw [Category.comp_id]
        have h₂ : 𝟙 (C P) ≫ j P ≫ sX = j P ≫ sX := Category.id_comp _
        have hpb := pluriformPullback_heq h₁ h₂ σ σT (fun a => (hσσ a).symm) hρ
        refine ⟨cast (by rw [Category.id_comp]) τ, ⟨rfl, cast_heq _ _⟩,
          cast (by rw [Category.id_comp])
            (pluriformPullback (jT ≫ sX) (j P ≫ sX) σT.toHom n N ρP), ?_, ?_⟩
        · exact isPoincareResidue_congr jT (Category.id_comp sX).symm (cast_heq _ _).symm
            (cast_heq _ _).symm hclean
        · exact hpb.trans (cast_heq _ _).symm
    · obtain ⟨P, S', ι', BS', F', ψ, hlen, hcomp, hdlt', hrest⟩ := ih (by omega)
      haveI := F'.isIntegral_stratum
      haveI := F'.isNormal_stratum
      haveI := F'.isLocallyNoetherian_stratum
      haveI := F'.isClosedImmersion
      obtain ⟨σ, hσ, hσc, hres⟩ := hrest
      haveI := hCproper P
      haveI : CompactSpace (C P) := QuasiCompact.compactSpace_of_compactSpace (j P ≫ sX)
      haveI : CompactSpace S₀ := QuasiCompact.compactSpace_of_compactSpace ι₀
      haveI : CompactSpace S' := QuasiCompact.compactSpace_of_compactSpace ι'
      have hS₀n : IsNormalVariety ℂ (ι₀ ≫ sX) := F₀.isNormalVariety
      have hS'n : IsNormalVariety ℂ (ι' ≫ j P ≫ sX) := F'.isNormalVariety
      haveI : LocallyOfFiniteType (ι₀ ≫ sX) := hS₀n.1.toLocallyOfFiniteType
      haveI : LocallyOfFiniteType (ι' ≫ j P ≫ sX) := hS'n.1.toLocallyOfFiniteType
      haveI : LocallyOfFiniteType (jT ≫ ι₀ ≫ sX) := hj.1.1.toLocallyOfFiniteType
      obtain ⟨-, Q, hQ1, hQr, hci, -⟩ := id hj
      haveI := hci
      -- dimensions: `T` has dimension `d`, the ambient strata `S₀ ≅ S'` dimension `d + 1`
      set d := (letI := functionFieldAlgebra (jT ≫ ι₀ ≫ sX)
        (Algebra.trdeg ℂ T.functionField).toNat) with hd
      have hdT : topologicalKrullDim T = d := topologicalKrullDim_eq_toNat_trdeg (jT ≫ ι₀ ≫ sX)
      have hdS₀ : topologicalKrullDim S₀ = (d + 1 : ℕ) := by
        rw [topologicalKrullDim_eq_toNat_trdeg (ι₀ ≫ sX), ← hj.trdeg_add_one]
      have hdS' : topologicalKrullDim S' = (d + 1 : ℕ) := by
        have h1 := StratumAdjunctionData.dim_add_length (sX := sX) hdim F₀ hdS₀
        have h2 := StratumAdjunctionData.dim_add_length (sX := j P ≫ sX)
          (hset.topologicalKrullDim_eq P) F'
          (topologicalKrullDim_eq_toNat_trdeg (ι' ≫ j P ≫ sX))
        rw [topologicalKrullDim_eq_toNat_trdeg (ι' ≫ j P ≫ sX)]
        congr 1
        norm_cast
        omega
      -- canonical divisors and `ℚ`-Cartier adjoints on both sides
      obtain ⟨d₁, K, hK, hKB⟩ := hcanX F₀
      obtain ⟨d₂, K', hK', hK'C⟩ := hset.isCartierDivisor P F'
      have hd₁ : d₁ = d + 1 := by
        have := hK.topologicalKrullDim_eq
        rw [hdS₀] at this
        exact_mod_cast this.symm
      have hd₂ : d₂ = d + 1 := by
        have := hK'.topologicalKrullDim_eq
        rw [hdS'] at this
        exact_mod_cast this.symm
      subst hd₁ hd₂
      have hKB' : (Divisor.toQDivisor K' + BS').IsQCartier :=
        ⟨m, by exact_mod_cast hset.pos.ne', hK'C⟩
      have hψs : ψ.hom ≫ ι' ≫ j P ≫ sX = ι₀ ≫ sX := by
        rw [← hcomp]
        simp only [Category.assoc]
      have hσ' : ∀ a, σ a = functionFieldMap ψ.hom a := hσ
      obtain ⟨T', jT', BT', hjT', ψT, hψT, hdltT', σT, hσT, hσTc⟩ :=
        exists_isAdjunctionStep_iso_of_isAdjunctionStep hS₀n hS'n hdS₀ hdS' hK hK' hKB hKB'
          ⟨hS₀n, _, K, hK, hKB⟩ ⟨hS'n, _, K', hK', hKB'⟩ hdlt' ψ hψs σ hσ' hσc hj
      haveI : IsIntegral T' := hjT'.1.1.toIsIntegral
      haveI : IsNormal T' := hjT'.1.2
      haveI : IsLocallyNoetherian T' := by
        have := hjT'.1.1
        exact LocallyOfFiniteType.isLocallyNoetherian (jT' ≫ ι' ≫ j P ≫ sX)
      haveI : LocallyOfFiniteType (jT' ≫ ι' ≫ j P ≫ sX) := hjT'.1.1.toLocallyOfFiniteType
      obtain ⟨-, Q', -, hQ'r, hci', -⟩ := id hjT'
      haveI := hci'
      obtain ⟨σn, hσn, hσnc⟩ := exists_isCrepantBirationalMap_congr
        (show jT ≫ ι₀ ≫ sX = (jT ≫ ι₀) ≫ sX by rw [Category.assoc])
        (show jT' ≫ ι' ≫ j P ≫ sX = (jT' ≫ ι') ≫ j P ≫ sX by rw [Category.assoc]) σT hσTc
      refine ⟨P, T', jT' ≫ ι', BT', F'.step jT' BT' hjT', ψT,
        by simp only [StratumAdjunctionData.length]; omega, ?_,
        isDltPair_congr (by rw [Category.assoc]) hdltT', σn, fun a => (hσn a).trans (hσT a),
        hσnc, ?_⟩
      · rw [Category.assoc, ← Category.assoc ψT.hom, hψT, Category.assoc, hcomp]
      intro N τ ρP hresP e he ρ' hiter
      obtain ⟨ρ₀', hρ₀', ρ'', hr'', hρ''⟩ := hiter
      have he' : e = d := by
        rw [hdT] at he
        exact_mod_cast he.symm
      subst he'
      have IH := hres N τ ρP hresP (d + 1) hdS₀ ρ₀' hρ₀'
      have hfun := isPoincareResidue_pluriformPullback_of_iso hS₀n hS'n hdS₀ hdS' ψ hψs σ hσ' Q Q'
        hQr hQ'r ψT hψT σT hσT hr''
      refine ⟨_, IH, _, hfun, ?_⟩
      exact pluriformPullback_heq (by rw [Category.assoc]) (by rw [Category.assoc]) σn σT
        (fun a => (hσn a).symm) hρ''

/-- **No full pole, no residue.** Let `j : T ⟶ Y` be the inclusion of a normal prime divisor `P`
of a normal complex variety `Y` of dimension `n + 1`. If a rational `N`-canonical form `τ`,
`N > 0`, has order `> -N` along `P`, its Poincaré residue along `T` is zero: `τ = f σ^{⊗N}` for a
form `σ` with a simple pole along `P`, and `f` vanishes along `P`. -/
private theorem isPoincareResidue_eq_zero_of_neg_lt_ordForm {Y T : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y] [CompactSpace Y]
    [LocallyOfFiniteType sY] (hY : IsNormalVariety ℂ sY) {n : ℕ}
    (hdim : topologicalKrullDim Y = n + 1) (j : T ⟶ Y) [IsClosedImmersion j] [IsIntegral T]
    [IsNormal T] [IsLocallyNoetherian T] [CompactSpace T] (hT : IsNormalVariety ℂ (j ≫ sY))
    (P : Mori.PrimeDivisor Y) (hP : Set.range j.base = (P.support : Set Y))
    (Q : Mori.PrimeDivisor T) {N : ℕ} (hN : 0 < N) {τ : RationalPluriForms sY (n + 1) N}
    (hτ : τ ≠ 0 → -(N : ℤ) < P.ordForm τ) {ρ : RationalPluriForms (j ≫ sY) n N}
    (hρ : IsPoincareResidue sY j n N τ ρ) : ρ = 0 := by
  classical
  haveI : LocallyOfFiniteType (j ≫ sY) := hT.1.toLocallyOfFiniteType
  have hjT := MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hP
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (j ≫ sY)
  by_cases hτ0 : τ = 0
  · subst hτ0
    obtain ⟨t, g, x, ht, -, -⟩ := id hρ
    have h0 : IsPoincareResidue sY j n N (0 : RationalPluriForms sY (n + 1) N) 0 := by
      refine ⟨t, 0, x, ht, ?_, ?_⟩ <;> simp <;> rfl
    exact IsPoincareResidue.unique_of_isClosedImmersion P hjT hρ h0
  have hd : (Algebra.trdeg ℂ Y.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) (by rw [hdim]; norm_cast)
  obtain ⟨σ, hσ0, hσP, -, ρσ, hσres, -, -⟩ :=
    exists_form_of_residue_order sY hY hdim j hT P hP Q
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hσM0 := MMP.CyclicChartDifferent.Aux.pluriPow_ne_zero (sX := sY)
    (by rw [hdim]; norm_cast) hσ0 M
  obtain ⟨b₀⟩ := exists_basis_topForms (sX := sY) (d := n + 1) (by rw [hdim]; norm_cast)
  have hrank : Module.finrank Y.functionField
      (RationalPluriForms sY (n + 1) ((M + 1 : ℕ) : ℤ)) = 1 := by
    let bb : Module.Basis Unit Y.functionField
        (RationalPluriForms sY (n + 1) ((M + 1 : ℕ) : ℤ)) :=
      ZTensorPower.basis b₀ ((M + 1 : ℕ) : ℤ)
    rw [Module.finrank_eq_card_basis bb, Fintype.card_unit]
  obtain ⟨f, hf⟩ := (finrank_eq_one_iff_of_nonzero' _ hσM0).mp hrank τ
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hτ0 (by rw [← hf, zero_smul])
  have hordf : 0 < Y.ord f P.genericPoint := by
    have h1 := P.ordForm_smul (sX := sY) hd hf0 hσM0
    rw [hf, MMP.CyclicChartDifferent.Aux.ordForm_pluriPow (by rw [hdim]; norm_cast) hσ0 P M,
      hσP] at h1
    have := hτ hτ0
    omega
  -- a uniformizing function `ϖ` and the quotient `f / ϖ`, both regular along `P`
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := MMP.CyclicChartDifferent.Aux.exists_ord_eq_one P
  have hf'0 : f * ϖ⁻¹ ≠ 0 := mul_ne_zero hf0 (inv_ne_zero hϖ0)
  have hordf' : 0 ≤ Y.ord (f * ϖ⁻¹) P.genericPoint := by
    have h1 := Scheme.ord_mul (x := P.genericPoint) hϖ0 (inv_ne_zero hϖ0)
    rw [mul_inv_cancel₀ hϖ0, AlgebraicGeometry.ord_one', hϖ1] at h1
    rw [Scheme.ord_mul hf0 (inv_ne_zero hϖ0)]
    omega
  obtain ⟨a', ha'⟩ := MMP.CyclicChartDifferent.Aux.exists_algebraMap_eq_of_ord_nonneg P hf'0 hordf'
  obtain ⟨c', hc'⟩ := MMP.CyclicChartDifferent.Aux.exists_algebraMap_eq_of_ord_nonneg P hϖ0
    (by omega)
  have hsp : j (genericPoint T) ⤳ P.genericPoint := specializes_of_eq hjT
  set c := Y.presheaf.stalkSpecializes hsp c' with hc
  set b' := Y.presheaf.stalkSpecializes hsp a' with hb'
  have hcK : algebraMap _ Y.functionField c = ϖ := by
    rw [hc, MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes', hc']
  have hb'K : algebraMap _ Y.functionField b' = f * ϖ⁻¹ := by
    rw [hb', MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes', ha']
  obtain ⟨π, -, hπ, -, -, -, hunif⟩ := exists_uniformizer_of_eq_genericPoint (sY := sY) P hjT
  have hc0 : (j.stalkMap (genericPoint T)).hom c = 0 := by
    obtain ⟨u, -, hu⟩ := hunif c (by rw [hcK, hjT]; exact hϖ1)
    rw [hu, map_mul]
    exact mul_eq_zero_of_right _ hπ
  have hres := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul
    (MMP.CyclicChartDifferent.Aux.isPoincareResidue_pluriPow P hjT hdim hσres M) (c * b')
  rw [map_mul, hcK, hb'K, mul_comm, mul_assoc, inv_mul_cancel₀ hϖ0, mul_one, hf, map_mul, hc0,
    zero_mul, zero_smul] at hres
  exact IsPoincareResidue.unique_of_isClosedImmersion P hjT hρ hres

/-- An integral scheme of finite type over `ℂ` of dimension `d ≥ 1` has a prime divisor: the
next-to-last point of a maximal chain of specializations ending at a closed point. -/
private theorem nonempty_primeDivisor_of_one_le {T : Scheme.{0}} (sT : T ⟶ Spec (.of ℂ))
    [IsIntegral T] [LocallyOfFiniteType sT] [CompactSpace T] {d : ℕ}
    (h : topologicalKrullDim T = d) (hd : 1 ≤ d) : Nonempty (Mori.PrimeDivisor T) := by
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton (X := T) isClosed_univ Set.univ_nonempty
  have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sT x
  rw [hx.closure_eq, h] at h1
  have h0 : topologicalKrullDim ({x} : Set T) = 0 := by
    haveI : Subsingleton ({x} : Set T) := Set.subsingleton_singleton.coe_sort
    haveI : Nonempty ({x} : Set T) := ⟨⟨x, rfl⟩⟩
    haveI : DiscreteTopology ({x} : Set T) := inferInstance
    haveI : Nonempty (TopologicalSpace.IrreducibleCloseds ({x} : Set T)) :=
      ⟨⟨closure {(⟨x, rfl⟩ : ({x} : Set T))}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology _) Order.krullDim_nonneg
  rw [h0, zero_add] at h1
  have hc : Order.coheight x = d := by exact_mod_cast h1
  obtain ⟨p, hp, hlen⟩ := Order.exists_series_of_le_coheight x (n := d) hc.ge
  subst hlen
  have hc' := Order.coheight_eq_index_of_length_eq_head_coheight (p := p) (by rw [hp, hc])
    (Fin.rev ⟨1, by omega⟩)
  rw [Fin.rev_rev] at hc'
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc'⟩

/-- The Poincaré residue of the zero form along an adjunction step is zero. -/
private theorem eq_zero_of_isPoincareResidue_zero {Y T : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [LocallyOfFiniteType sY] [IsIntegral T]
    {j : T ⟶ Y} {BY : QDivisor Y} {BT : QDivisor T} (hj : IsAdjunctionStep sY BY j BT)
    {n m : ℕ} {ρ : RationalPluriForms (j ≫ sY) n m}
    (h : IsPoincareResidue sY j n m 0 ρ) : ρ = 0 := by
  obtain ⟨t, g, x, ht, -, -⟩ := id h
  have h0 : IsPoincareResidue sY j n m (0 : RationalPluriForms sY (n + 1) m) 0 := by
    refine ⟨t, 0, x, ht, ?_, ?_⟩ <;> simp <;> rfl
  exact IsPoincareResidue.unique hj h h0

/-- Transport of the zero form and of orders along an equality of structure morphisms. -/
private theorem ordForm_eq_of_heq {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {s s' : Y ⟶ Spec (.of ℂ)} (h : s = s') {d : ℕ} {m : ℤ} {x : RationalPluriForms s d m}
    {y : RationalPluriForms s' d m} (hxy : HEq x y) (P : Mori.PrimeDivisor Y) :
    P.ordForm x = P.ordForm y ∧ (x ≠ 0 → y ≠ 0) ∧ (y = 0 → x = 0) := by
  subst h
  obtain rfl := eq_of_heq hxy
  exact ⟨rfl, id, id⟩

private theorem eq_zero_of_heq_zero {Y : Scheme.{0}} [IsIntegral Y] {s s' : Y ⟶ Spec (.of ℂ)}
    (h : s = s') {d : ℕ} {m : ℤ} {x : RationalPluriForms s d m}
    (hx : HEq x (0 : RationalPluriForms s' d m)) : x = 0 := by
  subst h
  exact eq_of_heq hx

/-- **Iterated residues of a form without full poles along the floor vanish.** If a rational
`N`-canonical form `τ` on a normal projective complex variety `X` of dimension `n ≥ 2` has order
`> -N` along every prime divisor `P` with `coeff_P B ≥ 1`, then its iterated residue along every
flag of strata of positive length is zero. -/
private theorem eq_zero_of_isIteratedResidueRec {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (hX : Mori.IsProjectiveVariety ℂ sX)
    (hXn : IsNormalVariety ℂ sX) {B : QDivisor X} {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N)
    (hdim : topologicalKrullDim X = n) {τ : RationalPluriForms sX n N}
    (hτ : ∀ P : Mori.PrimeDivisor X, 1 ≤ B.coeff P → τ ≠ 0 → -(N : ℤ) < P.ordForm τ) :
    ∀ {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS)
      {e : ℕ} {ρ : @RationalPluriForms ℂ _ S (ι ≫ sX) F.isIntegral_stratum e N},
      1 ≤ F.length → topologicalKrullDim S = e → IsIteratedResidueRec τ F e ρ → ρ = 0 := by
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : CompactSpace X := by
    haveI := hX.toIsVariety
    exact QuasiCompact.compactSpace_of_compactSpace sX
  intro S ι BS F
  induction F with
  | refl h =>
    intro e ρ hl
    simp [StratumAdjunctionData.length] at hl
  | @step S₀ T ι₀ BS₀ F₀ j BT hj ih =>
    intro e ρ _ hT ⟨ρ₀, h₀, ρ', hr, hρ⟩
    haveI := F₀.isIntegral_stratum
    haveI := F₀.isNormal_stratum
    haveI := F₀.isLocallyNoetherian_stratum
    haveI : IsIntegral T := hj.1.1.toIsIntegral
    haveI : LocallyOfFiniteType (ι₀ ≫ sX) := F₀.isNormalVariety.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (j ≫ ι₀ ≫ sX) := hj.1.1.toLocallyOfFiniteType
    have hS₀ : topologicalKrullDim S₀ = (e + 1 : ℕ) := by
      have h1 := hj.trdeg_add_one
      have h2 := topologicalKrullDim_eq_toNat_trdeg (j ≫ ι₀ ≫ sX)
      have h3 := topologicalKrullDim_eq_toNat_trdeg (ι₀ ≫ sX)
      rw [hT] at h2
      have : e = (letI := functionFieldAlgebra (j ≫ ι₀ ≫ sX)
          (Algebra.trdeg ℂ T.functionField).toNat) := by exact_mod_cast h2
      rw [h3, ← h1, ← this]
    have hρ'0 : ρ' = 0 := by
      cases F₀ with
      | refl hp =>
        obtain ⟨rfl, hρ₀⟩ := h₀
        obtain ⟨-, P, hP1, hPr, hci, -⟩ := id hj
        haveI := hci
        have hT' : IsNormalVariety ℂ (j ≫ 𝟙 X ≫ sX) := hj.1
        haveI : IsNormal T := hT'.2
        haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (j ≫ 𝟙 X ≫ sX)
        haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace j
        have hXn' : IsNormalVariety ℂ (𝟙 X ≫ sX) := (Category.id_comp sX).symm ▸ hXn
        obtain ⟨Q⟩ := nonempty_primeDivisor_of_one_le (j ≫ 𝟙 X ≫ sX) hT (by omega)
        have ho := ordForm_eq_of_heq (Category.id_comp sX) hρ₀ P
        exact isPoincareResidue_eq_zero_of_neg_lt_ordForm (𝟙 X ≫ sX) hXn'
          (by rw [hdim]; norm_cast) j hT' P hPr Q hN
          (fun h0 => ho.1 ▸ hτ P hP1 (ho.2.1 h0)) hr
      | step F₁ j₁ B₁ hj₁ =>
        have := ih (by simp [StratumAdjunctionData.length]) hS₀ h₀
        subst this
        exact eq_zero_of_isPoincareResidue_zero hj hr
    subst hρ'0
    exact eq_zero_of_heq_zero (Category.assoc j ι₀ sX) hρ

/-! ### The floor curves -/

section Floor

variable {I : Type u} {X : I → Scheme.{0}} [∀ i, IsIntegral (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    {sX : ∀ i, X i ⟶ Spec (.of ℂ)} {B : ∀ i, QDivisor (X i)}

/-- A floor component of a dlt pair has coefficient one. -/
private theorem one_le_coeff_of_floor_ne_zero {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {BY : QDivisor Y}
    (hdlt : MMP.Intersection.IsDltPair sY BY) (P : Mori.PrimeDivisor Y)
    (hP : ⌊BY.coeff P⌋ ≠ 0) : 1 ≤ BY.coeff P := by
  have h0 : 0 ≤ BY.coeff P := hdlt.1.2.1 P
  have h1 : BY.coeff P ≤ 1 := hdlt.2.1 P
  by_contra h
  push Not at h
  exact hP (Int.floor_eq_zero_iff.2 ⟨h0, h⟩)

/-- The floor of a `ℚ`-divisor has finitely many components. -/
private theorem finite_floor {Y : Scheme.{0}} (BY : QDivisor Y) :
    Finite {P : Mori.PrimeDivisor Y // ⌊BY.coeff P⌋ ≠ 0} := by
  refine Finite.Set.subset (BY.support : Set (Mori.PrimeDivisor Y)) fun P hP => ?_
  simp only [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h0
  exact hP (by rw [DivisorWithCoeffs.coeff] at *; simp [h0])

end Floor

/-! ### Residue restrictions -/

section ResidueAdd

open exteriorPower

variable {k : Type*} [Field k] {O : Type*} [CommRing O] [IsDomain O] [Algebra k O]
  {K : Type*} [Field K] [Algebra k K] [Algebra O K] [IsScalarTower k O K] [IsFractionRing O K]
  {L : Type*} [Field L] [Algebra k L] [Algebra O L] [IsScalarTower k O L]

/-- **Sums of logarithmic pluriforms and of their residues.** On a line `Ω^{e+1}_{K/k}`, the sum
of two logarithmic pluriforms is a logarithmic pluriform along one of the two frames, and its
residue is the sum of the residues. -/
private theorem exists_logPluriForm_add [Module.Free O Ω[O⁄k]] [ValuationRing O] {e : ℕ}
    (hline : Module.finrank K (⋀[K]^(e + 1) Ω[K⁄k]) = 1)
    (hπ : Function.Surjective (algebraMap O L)) {t₀ : O} (ht₀ : algebraMap O L t₀ = 0)
    {r : Ω[O⁄k] →ₗ[O] O} (hr : r (KaehlerDifferential.D k O t₀) = 1) (m : ℕ) (g₁ g₂ : O)
    {u₁ u₂ : O} (hu₁ : IsUnit u₁) (hu₂ : IsUnit u₂) (x₁ x₂ : Fin e → O) :
    ∃ (g u : O) (x : Fin e → O), (u = u₁ ∨ u = u₂) ∧
      logPluriForm (O := O) k K m e g₁ (u₁ * t₀) x₁ +
          logPluriForm (O := O) k K m e g₂ (u₂ * t₀) x₂ =
        logPluriForm (O := O) k K m e g (u * t₀) x ∧
      logPluriResidue (O := O) k L m e g₁ x₁ + logPluriResidue (O := O) k L m e g₂ x₂ =
        logPluriResidue (O := O) k L m e g x := by
  have hω : ∀ (g t : O) (x : Fin e → O), logPluriForm (O := O) k K m e g t x =
      algebraMap O K g • formPow ((algebraMap O K t)⁻¹ • ιMulti K (e + 1)
        (Fin.cons (KaehlerDifferential.D k K (algebraMap O K t))
          fun i => KaehlerDifferential.D k K (algebraMap O K (x i)))) m := fun _ _ _ => rfl
  have hv : ∀ (g : O) (x : Fin e → O), logPluriResidue (O := O) k L m e g x =
      algebraMap O L g • formPow (ιMulti L e
        fun i => KaehlerDifferential.D k L (algebraMap O L (x i))) m := fun _ _ => rfl
  rcases exists_frame_comparison (L := L) hline hπ ht₀ hr hu₁ hu₂ x₁ x₂ with
    ⟨c, hcK, hcL⟩ | ⟨c, hcK, hcL⟩
  · beta_reduce at hcK hcL
    refine ⟨g₁ + g₂ * c ^ m, u₁, x₁, Or.inl rfl, ?_, ?_⟩
    · rw [hω, hω, hω, hcK, formPow_smul (algebraMap O K c)]
      simp only [map_add, map_mul, map_pow, add_smul, mul_smul]
      try rfl
    · rw [hv, hv, hv, hcL, formPow_smul (algebraMap O L c)]
      simp only [map_add, map_mul, map_pow, add_smul, mul_smul]
      try rfl
  · beta_reduce at hcK hcL
    refine ⟨g₁ * c ^ m + g₂, u₂, x₂, Or.inr rfl, ?_, ?_⟩
    · rw [hω, hω, hω, hcK, formPow_smul (algebraMap O K c)]
      simp only [map_add, map_mul, map_pow, add_smul, mul_smul]
      try rfl
    · rw [hv, hv, hv, hcL, formPow_smul (algebraMap O L c)]
      simp only [map_add, map_mul, map_pow, add_smul, mul_smul]
      try rfl

end ResidueAdd

section PoincareAdd

variable {Y T : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] [IsIntegral T] {j : T ⟶ Y}

/-- **Additivity of the Poincaré residue** along an adjunction step of a variety of dimension
`n + 1`: `Res(τ₁ + τ₂) = Res(τ₁) + Res(τ₂)`. -/
private theorem IsPoincareResidue.add [LocallyOfFiniteType sY] {BY : QDivisor Y}
    {BT : QDivisor T} (hj : IsAdjunctionStep sY BY j BT) {n m : ℕ}
    (hY : topologicalKrullDim Y = n + 1)
    {τ₁ τ₂ : RationalPluriForms sY (n + 1) m} {ρ₁ ρ₂ : RationalPluriForms (j ≫ sY) n m}
    (h₁ : IsPoincareResidue sY j n m τ₁ ρ₁) (h₂ : IsPoincareResidue sY j n m τ₂ ρ₂) :
    IsPoincareResidue sY j n m (τ₁ + τ₂) (ρ₁ + ρ₂) := by
  obtain ⟨P, hP, hci⟩ := hj.exists_primeDivisor
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (j ≫ sY)
  let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  have := isScalarTower_stalk_functionField sY (j (genericPoint T))
  obtain ⟨hdvr, hfree, -, -, -, -⟩ := stalk_facts_of_eq_genericPoint (sY := sY) P hP
  obtain ⟨htow, hsurj⟩ := stalkMap_facts_of_isClosedImmersion (sY := sY) (j := j)
  obtain ⟨ϖ, r, hϖ0, hr, -, -, hunif⟩ := exists_uniformizer_of_eq_genericPoint (sY := sY) P hP
  obtain ⟨b₀⟩ := MMP.Fourfold.exists_basis_topForms (sX := sY) (by exact_mod_cast hY)
  have hline : Module.finrank Y.functionField (⋀[Y.functionField]^(n + 1) Ω[Y.functionField⁄ℂ]) =
      1 := by rw [Module.finrank_eq_card_basis b₀, Fintype.card_unit]
  obtain ⟨t₁, g₁, x₁, ht₁, hτ₁, rfl⟩ := h₁
  obtain ⟨t₂, g₂, x₂, ht₂, hτ₂, rfl⟩ := h₂
  obtain ⟨u₁, hu₁, rfl⟩ := hunif t₁ ht₁
  obtain ⟨u₂, hu₂, rfl⟩ := hunif t₂ ht₂
  obtain ⟨g, u, x, hu, hK, hL⟩ := exists_logPluriForm_add (L := T.functionField) hline hsurj hϖ0
    hr m g₁ g₂ hu₁ hu₂ x₁ x₂
  refine ⟨u * ϖ, g, x, ?_, hτ₁ ▸ hτ₂ ▸ hK, hL.symm ▸ rfl⟩
  rcases hu with rfl | rfl
  · exact ht₁
  · exact ht₂

/-- **`ℂ`-linearity of the Poincaré residue**: `Res(c τ) = c Res(τ)`. -/
private theorem IsPoincareResidue.smul {BY : QDivisor Y} {BT : QDivisor T}
    (hj : IsAdjunctionStep sY BY j BT) {n m : ℕ} {τ : RationalPluriForms sY (n + 1) m}
    {ρ : RationalPluriForms (j ≫ sY) n m} (h : IsPoincareResidue sY j n m τ ρ) (c : ℂ) :
    IsPoincareResidue sY j n m (c • τ) (c • ρ) := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (j ≫ sY)
  let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  have := isScalarTower_stalk_functionField sY (j (genericPoint T))
  obtain ⟨htow, -⟩ := hj.stalkMap_facts
  obtain ⟨t, g, x, ht, hτ, hρ⟩ := h
  refine ⟨t, algebraMap ℂ _ c * g, x, ht, ?_, ?_⟩
  · rw [hτ, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul]
    rfl
  · rw [hρ, map_mul]
    have e : (j.stalkMap (genericPoint T)).hom (algebraMap ℂ _ c) =
        algebraMap ℂ T.functionField c :=
      (IsScalarTower.algebraMap_apply ℂ (Y.presheaf.stalk (j (genericPoint T)))
        T.functionField c).symm
    rw [e, mul_smul]
    rfl

end PoincareAdd

/-- Sums of rational pluriforms do not depend on the structure morphism beyond equality. -/
private theorem add_heq {X : Scheme.{0}} [IsIntegral X] {s s' : X ⟶ Spec (.of ℂ)} (h : s = s')
    {d : ℕ} {m : ℤ} {x₁ x₂ : RationalPluriForms s d m} {y₁ y₂ : RationalPluriForms s' d m}
    (h₁ : HEq x₁ y₁) (h₂ : HEq x₂ y₂) : HEq (x₁ + x₂) (y₁ + y₂) := by
  subst h
  rw [eq_of_heq h₁, eq_of_heq h₂]

/-- Scalar multiples of rational pluriforms do not depend on the structure morphism beyond
equality. -/
private theorem smul_heq {X : Scheme.{0}} [IsIntegral X] {s s' : X ⟶ Spec (.of ℂ)} (h : s = s')
    {d : ℕ} {m : ℤ} (c : ℂ) {x : RationalPluriForms s d m} {y : RationalPluriForms s' d m}
    (h₁ : HEq x y) : HEq (c • x) (c • y) := by
  subst h
  rw [eq_of_heq h₁]

/-- Iterated residues, in the unfolded form, are additive and `ℂ`-linear along a flag whose final
stratum has dimension `e`. -/
private theorem isIteratedResidueRec_add_smul {S : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)} {B : QDivisor S} {n m : ℕ}
    {T : Scheme.{0}} {ι : T ⟶ S} {BT : QDivisor T} (F : StratumAdjunctionData sS B ι BT) :
    ∀ {e : ℕ}, topologicalKrullDim T = e →
      (∀ (τ₁ τ₂ : RationalPluriForms sS n m)
        (ρ₁ ρ₂ : @RationalPluriForms ℂ _ T (ι ≫ sS) F.isIntegral_stratum e m),
        IsIteratedResidueRec τ₁ F e ρ₁ → IsIteratedResidueRec τ₂ F e ρ₂ →
          IsIteratedResidueRec (τ₁ + τ₂) F e (ρ₁ + ρ₂)) ∧
      ∀ (c : ℂ) (τ : RationalPluriForms sS n m)
        (ρ : @RationalPluriForms ℂ _ T (ι ≫ sS) F.isIntegral_stratum e m),
        IsIteratedResidueRec τ F e ρ → IsIteratedResidueRec (c • τ) F e (c • ρ) := by
  induction F with
  | refl h =>
    intro e _
    refine ⟨?_, ?_⟩
    · rintro τ₁ τ₂ ρ₁ ρ₂ ⟨rfl, h₁⟩ ⟨-, h₂⟩
      exact ⟨rfl, add_heq (Category.id_comp sS) h₁ h₂⟩
    · rintro c τ ρ ⟨rfl, h₁⟩
      exact ⟨rfl, smul_heq (Category.id_comp sS) c h₁⟩
  | @step S' T ι BS F j BT hj ih =>
    intro e he
    haveI := F.isIntegral_stratum
    haveI := F.isNormal_stratum
    haveI := F.isLocallyNoetherian_stratum
    haveI : IsIntegral T := hj.1.1.toIsIntegral
    haveI : LocallyOfFiniteType (ι ≫ sS) := F.isNormalVariety.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (j ≫ ι ≫ sS) := hj.1.1.toLocallyOfFiniteType
    have hS' : topologicalKrullDim S' = (e + 1 : ℕ) := by
      have h1 := hj.trdeg_add_one
      have h2 := topologicalKrullDim_eq_toNat_trdeg (j ≫ ι ≫ sS)
      have h3 := topologicalKrullDim_eq_toNat_trdeg (ι ≫ sS)
      rw [he] at h2
      rw [h3]
      have : e = (letI := functionFieldAlgebra (j ≫ ι ≫ sS)
          (Algebra.trdeg ℂ T.functionField).toNat) := by exact_mod_cast h2
      congr 1
      omega
    obtain ⟨ihadd, ihsmul⟩ := ih hS'
    refine ⟨?_, ?_⟩
    · rintro τ₁ τ₂ ρ₁ ρ₂ ⟨ρ₀₁, h₀₁, ρ'₁, hr₁, hh₁⟩ ⟨ρ₀₂, h₀₂, ρ'₂, hr₂, hh₂⟩
      exact ⟨ρ₀₁ + ρ₀₂, ihadd _ _ _ _ h₀₁ h₀₂, ρ'₁ + ρ'₂,
        IsPoincareResidue.add hj (by exact_mod_cast hS') hr₁ hr₂,
        add_heq (Category.assoc j ι sS) hh₁ hh₂⟩
    · rintro c τ ρ ⟨ρ₀, h₀, ρ', hr, hh⟩
      exact ⟨c • ρ₀, ihsmul c _ _ h₀, c • ρ', IsPoincareResidue.smul hj hr c,
        smul_heq (Category.assoc j ι sS) c hh⟩

/-- **Iterated residues are additive and `ℂ`-linear** along every flag of strata whose final
stratum has dimension `e`. -/
private theorem isIteratedResidue_add_smul {S : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)} {B : QDivisor S} {n m : ℕ}
    {T : Scheme.{0}} {ι : T ⟶ S} {BT : QDivisor T} (F : StratumAdjunctionData sS B ι BT) (e : ℕ)
    (he : topologicalKrullDim T = e) :
    haveI := F.isIntegral_stratum
    (∀ (τ₁ τ₂ : RationalPluriForms sS n m) (ρ₁ ρ₂ : RationalPluriForms (ι ≫ sS) e m),
      IsIteratedResidue sS B τ₁ F e ρ₁ → IsIteratedResidue sS B τ₂ F e ρ₂ →
        IsIteratedResidue sS B (τ₁ + τ₂) F e (ρ₁ + ρ₂)) ∧
    ∀ (c : ℂ) (τ : RationalPluriForms sS n m) (ρ : RationalPluriForms (ι ≫ sS) e m),
      IsIteratedResidue sS B τ F e ρ → IsIteratedResidue sS B (c • τ) F e (c • ρ) := by
  haveI := F.isIntegral_stratum
  obtain ⟨hadd, hsmul⟩ := isIteratedResidueRec_add_smul (n := n) (m := m) F he
  exact ⟨fun τ₁ τ₂ ρ₁ ρ₂ h₁ h₂ => IsIteratedResidue.of_rec F (hadd _ _ _ _ h₁.rec' h₂.rec'),
    fun c τ ρ h => IsIteratedResidue.of_rec F (hsmul c _ _ h.rec')⟩

/-- The order of a form does not see a rewriting of the structure morphism. -/
private theorem ordForm_cast {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {s s' : X ⟶ Spec (.of ℂ)} (h : s = s') {d : ℕ} {m : ℤ} (τ : RationalPluriForms s d m)
    (P : Mori.PrimeDivisor X)
    (e : RationalPluriForms s d m = RationalPluriForms s' d m) :
    P.ordForm (cast e τ) = P.ordForm τ := by
  subst h
  rfl

/-- **Residues at a point of a normal curve exist.** Along an adjunction step `j : Q ⟶ C` onto a
point of a normal curve, every rational `m`-canonical form with a pole of order at most `m`
there has a Poincaré residue. -/
private theorem exists_isPoincareResidue_of_curve {C Q : Scheme.{0}} [IsIntegral C]
    [IsLocallyNoetherian C] [IsNormal C] {s : C ⟶ Spec (.of ℂ)}
    (hC : IsNormalVariety ℂ s) (hdim : topologicalKrullDim C = 1) {BC : QDivisor C}
    {j : Q ⟶ C} {BQ : QDivisor Q} (hj : IsAdjunctionStep s BC j BQ) [IsIntegral Q] {m : ℕ}
    (ρ : RationalPluriForms s 1 m)
    (hρ : ∀ P : Mori.PrimeDivisor C, j (genericPoint Q) = P.genericPoint → ρ ≠ 0 →
      -(m : ℤ) ≤ P.ordForm ρ) :
    ∃ ρ' : RationalPluriForms (j ≫ s) 0 m, IsPoincareResidue s j 0 m ρ ρ' := by
  classical
  haveI : LocallyOfFiniteType s := hC.1.toLocallyOfFiniteType
  obtain ⟨P, hP, hci⟩ := hj.exists_primeDivisor
  let O := C.presheaf.stalk (j (genericPoint Q))
  let := stalkAlgebra s (j (genericPoint Q))
  let := functionFieldAlgebra s
  let := functionFieldAlgebra (j ≫ s)
  let : Algebra O Q.functionField := (j.stalkMap (genericPoint Q)).hom.toAlgebra
  have := isScalarTower_stalk_functionField s (j (genericPoint Q))
  obtain ⟨hdvr, hfree, hfin, -, hcoh, hrank⟩ := hj.stalk_facts
  obtain ⟨-, hsurj⟩ := hj.stalkMap_facts
  obtain ⟨ϖ, r, -, hr, hker, -, -⟩ := hj.exists_uniformizer
  have htr : (Algebra.trdeg ℂ C.functionField).toNat = 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (by exact_mod_cast hdim)
  -- `ϖ` is a uniformizer
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)).symm.trans hker
  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hmax
  have hϖ0 : algebraMap O C.functionField ϖ ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hϖirr.ne_zero
  have hord : C.ord (algebraMap O C.functionField ϖ) (j (genericPoint Q)) = 1 :=
    (Scheme.ord_eq_iff hcoh hϖ0).mpr (Ring.ordFrac_irreducible hϖirr)
  -- `dϖ` generates `Ω_{𝒪/ℂ}`
  have hspan : Submodule.span O (Set.range ![KaehlerDifferential.D ℂ O ϖ]) = ⊤ := by
    haveI := hfree
    haveI := hfin
    have hrk : Module.finrank O Ω[O⁄ℂ] = 1 := hrank.trans htr
    let b₀ := Module.finBasisOfFinrankEq O Ω[O⁄ℂ] hrk
    set c := b₀.repr (KaehlerDifferential.D ℂ O ϖ) 0 with hc_def
    have hD : KaehlerDifferential.D ℂ O ϖ = c • b₀ 0 := by
      conv_lhs => rw [← b₀.sum_repr (KaehlerDifferential.D ℂ O ϖ)]
      simp [Fin.sum_univ_one, hc_def]
    have hc : IsUnit c := IsUnit.of_mul_eq_one (r (b₀ 0)) (by
      rw [← smul_eq_mul, ← map_smul, ← hD, hr])
    refine eq_top_iff.mpr ?_
    rw [← b₀.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have : b₀ 0 = ((hc.unit⁻¹ : Oˣ) : O) • KaehlerDifferential.D ℂ O ϖ := by
      conv_rhs => rw [hD]
      rw [smul_smul, hc.val_inv_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  -- the frame `dϖ` of `Ω_{k(C)/ℂ}`
  have := essFiniteType_functionField (sX := s)
  have hK1 : Module.finrank C.functionField Ω[C.functionField⁄ℂ] = 1 :=
    (finrank_kaehlerDifferential_eq_trdeg ℂ C.functionField).trans htr
  have : FiniteDimensional C.functionField Ω[C.functionField⁄ℂ] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent ℂ C.functionField).1
  haveI := nontrivial_exteriorPower_of_finrank_eq ℂ C.functionField hK1
  have hσ := MMP.Fourfold.span_singleton_ιMulti_eq_top _ hspan
  have h0 := topFormsMap_ne_zero_of_span_eq_top (k := ℂ) (K := C.functionField) hσ
  set F0 := topFormsMap ℂ O C.functionField 1 (exteriorPower.ιMulti O 1
    ![KaehlerDifferential.D ℂ O ϖ]) with hF0_def
  have hfr1 : Module.finrank C.functionField (⋀[C.functionField]^1 Ω[C.functionField⁄ℂ]) = 1 := by
    rw [exteriorPower.finrank_eq, hK1, Nat.choose_self]
  have hspanK : Submodule.span C.functionField {F0} = ⊤ :=
    (finrank_eq_one_iff_of_nonzero F0 h0).mp hfr1
  let bK := basisOfSpanSingleton hspanK h0
  set c := (ZTensorPower.basis bK (m : ℤ)).repr ρ () with hc_def
  have hρeq : ρ = c • (PiTensorProduct.tprod C.functionField (fun _ : Fin m => F0) :
      TensorPower C.functionField m (⋀[C.functionField]^1 Ω[C.functionField⁄ℂ])) := by
    have h1 := basis_unit_repr_smul (ZTensorPower.basis bK (m : ℤ)) ρ
    have h2 := ZTensorPower.basis_ofNat bK m
    rw [basisOfSpanSingleton_apply] at h2
    rw [← hc_def] at h1
    rw [← h2]
    exact h1.symm
  by_cases hρ0 : ρ = 0
  · refine ⟨0, ϖ, 0, Fin.elim0, hord, ?_, ?_⟩
    · rw [hρ0, map_zero]
      exact (zero_smul _ _).symm
    · rw [map_zero]
      exact (zero_smul _ _).symm
  have hc0 : c ≠ 0 := fun h => hρ0 (by rw [hρeq, h]; exact zero_smul _ _)
  have hordc : C.ord c P.genericPoint ≥ -(m : ℤ) := by
    have := MMP.CyclicChartDifferent.ordForm_eq_of_frame (sX := s) P hP ![KaehlerDifferential.D ℂ O ϖ]
      hspan h0 c ρ hρeq
    rw [← this]
    exact hρ P hP hρ0
  -- the coefficient along the frame `(dϖ/ϖ)^m` is regular
  have hgK : c * algebraMap O C.functionField ϖ ^ m ≠ 0 := mul_ne_zero hc0 (pow_ne_zero _ hϖ0)
  obtain ⟨g, hg⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
    (j (genericPoint Q)) hgK fun Γ hΓ => by
      have hΓP : Γ.genericPoint = P.genericPoint := by
        have hsp : Γ.genericPoint ⤳ j (genericPoint Q) := by
          rw [specializes_iff_mem_closure, ← PrimeDivisor.support_eq_closure]; exact hΓ
        rw [hP] at hsp
        exact MMP.ProgramBaseChange.eq_of_specializes_of_coheight_eq_one hsp
          Γ.coheight_genericPoint P.coheight_genericPoint
      rw [hΓP, Scheme.ord_mul hc0 (pow_ne_zero _ hϖ0), Scheme.ord_pow hϖ0, ← hP, hord]
      rw [hP]
      omega
  refine ⟨_, ϖ, g, Fin.elim0, hord, ?_, rfl⟩
  have hF0' : exteriorPower.ιMulti C.functionField (0 + 1)
      (Fin.cons (KaehlerDifferential.D ℂ C.functionField (algebraMap O C.functionField ϖ))
        fun i : Fin 0 => KaehlerDifferential.D ℂ C.functionField
          (algebraMap O C.functionField (Fin.elim0 i))) = F0 := by
    rw [hF0_def, topFormsMap_ιMulti]
    congr 1
    funext i
    fin_cases i
    simp [KaehlerDifferential.map_D]
  rw [hρeq, hg, hF0', tprod_const_smul, smul_smul]
  congr 1
  have h1 : algebraMap O C.functionField ϖ * (algebraMap O C.functionField ϖ)⁻¹ = 1 :=
    mul_inv_cancel₀ hϖ0
  rw [mul_assoc, ← mul_pow]
  erw [h1]
  rw [one_pow, mul_one]

/-- **The pole bound of a log pluricanonical section.** If every coefficient of `B` is at most
one, a nonzero section of `m(K + B)` has a pole of order at most `m` along every prime divisor. -/
private theorem neg_le_ordForm_of_mem_logPluricanonicalSections {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {B : QDivisor Y}
    (hB1 : ∀ P, B.coeff P ≤ 1) {n m : ℕ} {τ : RationalPluriForms sY n m}
    (hτ : τ ∈ logPluricanonicalSections sY n m B) (P : Mori.PrimeDivisor Y) (hτ0 : τ ≠ 0) :
    -(m : ℤ) ≤ P.ordForm τ := by
  have h1 := hτ.2 P ⟨P.genericPoint, by
    rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl, trivial⟩ hτ0
  rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul] at h1
  have h2 : ⌊((m : ℤ) • B.coeff P)⌋ ≤ (m : ℤ) := by
    have hx : (m : ℤ) • B.coeff P ≤ (((m : ℤ) : ℚ)) := by
      rw [zsmul_eq_mul]
      have := hB1 P
      push_cast
      nlinarith [(Nat.cast_nonneg m : (0 : ℚ) ≤ m)]
    exact (Int.floor_mono hx).trans_eq (Int.floor_intCast _)
  omega

/-- **Iterated residues on a dlt curve exist.** Along every flag of strata of a dlt pair
`(C, B_C)` on a normal curve, every section of `m(K_C + B_C)` has an iterated residue: a flag
has length at most one, and along a point of coefficient one the pole order is at most `m`. -/
private theorem exists_isIteratedResidue_curve {C : Scheme.{0}} [IsIntegral C]
    [IsLocallyNoetherian C] [IsNormal C] {sC : C ⟶ Spec (.of ℂ)}
    (hC : IsNormalVariety ℂ sC) (hdim : topologicalKrullDim C = 1) {BC : QDivisor C}
    (hdlt : MMP.Intersection.IsDltPair sC BC) {m : ℕ}
    {T : Scheme.{0}} {ι : T ⟶ C} {BT : QDivisor T} (F : StratumAdjunctionData sC BC ι BT) (e : ℕ)
    (he : topologicalKrullDim T = e) (τ : RationalPluriForms sC 1 m)
    (hτ : τ ∈ logPluricanonicalSections sC 1 m BC) :
    haveI := F.isIntegral_stratum
    ∃ ρ : RationalPluriForms (ι ≫ sC) e m, IsIteratedResidue sC BC τ F e ρ := by
  haveI : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  have hC' : IsNormalVariety ℂ (𝟙 C ≫ sC) := by rw [Category.id_comp]; exact hC
  have hlen := F.dim_add_length (n := 1) (by exact_mod_cast hdim) he
  have e0 : RationalPluriForms sC 1 m = RationalPluriForms (𝟙 C ≫ sC) 1 m := by
    rw [Category.id_comp]
  cases F with
  | refl h =>
    simp only [StratumAdjunctionData.length, add_zero] at hlen
    subst hlen
    exact ⟨_, IsIteratedResidue.refl h⟩
  | step F₁ j BT hj =>
    cases F₁ with
    | refl h =>
      simp only [StratumAdjunctionData.length] at hlen
      obtain rfl : e = 0 := by omega
      haveI : IsIntegral T := hj.1.1.toIsIntegral
      obtain ⟨ρ', hρ'⟩ := exists_isPoincareResidue_of_curve hC' (by exact_mod_cast hdim) hj
        (cast e0 τ) fun P _ h0 => by
          rw [ordForm_cast (Category.id_comp sC).symm]
          exact neg_le_ordForm_of_mem_logPluricanonicalSections hdlt.2.1 hτ P
            fun h => h0 (by subst h; rfl)
      exact ⟨_, IsIteratedResidue.step (IsIteratedResidue.refl h) hρ'⟩
    | step F₂ _ _ _ =>
      simp only [StratumAdjunctionData.length] at hlen
      omega

/-- **Residue restriction maps on a collection of dlt curves exist**, in every degree of the
stratified setting: the iterated residue along a flag exists, is unique and is linear. -/
private theorem nonempty_residueRestriction_curve {J : Type u} {C : J → Scheme.{0}}
    [∀ j, IsIntegral (C j)] [∀ j, IsLocallyNoetherian (C j)] [∀ j, IsNormal (C j)]
    {sC : ∀ j, C j ⟶ Spec (.of ℂ)} {BC : ∀ j, QDivisor (C j)} {m : ℕ}
    (hset : IsStratifiedSectionSetting sC BC 1 m) :
    Nonempty (ResidueRestriction sC BC 1 m) := by
  classical
  have hex : ∀ (j : J) {T : Scheme.{0}} {ι : T ⟶ C j} {BT : QDivisor T}
      (F : StratumAdjunctionData (sC j) (BC j) ι BT) (e : ℕ), topologicalKrullDim T = e →
      ∀ τ ∈ logPluricanonicalSections (sC j) 1 m (BC j),
        haveI := F.isIntegral_stratum
        ∃ ρ : RationalPluriForms (ι ≫ sC j) e m, IsIteratedResidue (sC j) (BC j) τ F e ρ :=
    fun j _ _ _ F e he τ hτ => exists_isIteratedResidue_curve (hset.isPair j).isPair.1
      (by exact_mod_cast hset.topologicalKrullDim_eq j) (hset.isDltPair j) F e he τ hτ
  exact ⟨{ setting := hset,
            toFun := fun j T ι BT F e =>
              haveI := F.isIntegral_stratum
              if he : topologicalKrullDim T = e then
                { toFun := fun τ => (hex j F e he τ τ.2).choose
                  map_add' := fun τ₁ τ₂ => IsIteratedResidue.unique
                    (hex j F e he (τ₁ + τ₂) (τ₁ + τ₂).2).choose_spec
                    ((isIteratedResidue_add_smul F e he).1 _ _ _ _
                      (hex j F e he τ₁ τ₁.2).choose_spec
                      (hex j F e he τ₂ τ₂.2).choose_spec)
                  map_smul' := fun c τ => IsIteratedResidue.unique
                    (hex j F e he (c • τ) (c • τ).2).choose_spec
                    ((isIteratedResidue_add_smul F e he).2 c _ _
                      (hex j F e he τ τ.2).choose_spec) }
              else 0,
            isIteratedResidue := fun j T ι BT F e τ he => by
              haveI := F.isIntegral_stratum
              simp only [dif_pos he]
              exact (hex j F e he τ τ.2).choose_spec }⟩

/-- **A normal curve over `ℂ` is smooth**: its local rings are fields or discrete valuation
rings, hence regular. -/
private theorem isSmoothScheme_of_topologicalKrullDim_eq_one {C : Scheme.{0}} [IsIntegral C]
    [IsLocallyNoetherian C] [IsNormal C] {sC : C ⟶ Spec (.of ℂ)} (hC : IsNormalVariety ℂ sC)
    (hdim : topologicalKrullDim C = 1) : IsSmoothScheme sC := by
  haveI : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  refine eq_top_iff.mpr fun y _ => ?_
  rw [MMP.Mori.mem_smoothLocus_iff, ← InfinitesimalLifting.smoothAt_iff_exists_open_smooth_comp]
  refine (Set.ext_iff.mp (AlgebraicGeometry.smoothAt_locus_eq_regular_locus ℂ sC) y).mpr ?_
  show IsRegularLocalRing (C.presheaf.stalk y)
  have h2 : ringKrullDim (C.presheaf.stalk y) ≤ 1 := by
    rw [← hdim, topologicalKrullDim_eq_iSup_krullDimOfRing_stalk C]
    exact le_iSup (fun y : C => ringKrullDim (C.presheaf.stalk y)) y
  haveI : Ring.KrullDimLE 1 (C.presheaf.stalk y) := by
    rw [Ring.krullDimLE_iff]; exact_mod_cast h2
  haveI : Ring.DimensionLEOne (C.presheaf.stalk y) := ⟨fun {p} hp0 hp => by
    rcases Ring.krullDimLE_one_iff.1 inferInstance p hp with h | h
    · exact absurd (le_bot_iff.1 (h.2 ⟨Ideal.isPrime_bot, le_rfl⟩ bot_le)) hp0
    · exact h⟩
  haveI := IsNormal.stalk_normal (X := C) y
  haveI : IsDedekindDomain (C.presheaf.stalk y) :=
    (isDedekindDomain_iff _ (FractionRing (C.presheaf.stalk y))).2 ⟨inferInstance, inferInstance,
      inferInstance, fun {_} => (isIntegrallyClosed_iff _).mp inferInstance⟩
  haveI : IsPrincipalIdealRing (C.presheaf.stalk y) :=
    IsPrincipalIdealRing.of_isNoetherianRing_of_isBezout
  infer_instance

/-- An epimorphic counit of `f^* ⊣ f_*` stays epimorphic along an isomorphism of modules. -/
private theorem epi_counit_of_iso {X Z : Scheme.{0}} (f : X ⟶ Z) {M N : X.Modules} (e : N ≅ M)
    (h : Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M)) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app N) := by
  set adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have hnat := adj.counit.naturality e.hom
  have heq : adj.counit.app N =
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).map e.hom ≫
        adj.counit.app M ≫ e.inv := by
    rw [← Category.assoc, hnat, Functor.id_map, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [heq]
  infer_instance

section Conversion

open MMP.Intersection

/-- The order of `v⁻¹` is minus the order of `v`. -/
private theorem scheme_ord_inv {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {v : X.functionField} (hv : v ≠ 0) {z : X} : X.ord v⁻¹ z = -X.ord v z := by
  have := Scheme.ord_mul (x := z) hv (inv_ne_zero hv)
  rw [mul_inv_cancel₀ hv, Scheme.ord_one] at this
  omega

/-- The order of a regular function at a point of coheight one is the length of its quotient. -/
private theorem scheme_ord_algebraMap {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {z : X} (hz : Order.coheight z = 1) {a : X.presheaf.stalk z} (ha : a ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk z) X.functionField a) z = (Ring.ord _ a).toNat := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have hne : algebraMap (X.presheaf.stalk z) X.functionField a ≠ 0 := by
    rwa [Ne, IsFractionRing.to_map_eq_zero_iff]
  rw [Scheme.ord_eq_iff hz hne]
  unfold Scheme.ordHom
  rw [Ring.ordFrac_eq_ord _ ha]
  have hnzd : a ∈ nonZeroDivisors _ := mem_nonZeroDivisors_of_ne_zero ha
  exact Ring.ordMonoidWithZeroHom_eq_coe (R := X.presheaf.stalk z) hnzd
    (ENat.natCast_toNat (Ring.ord_ne_top hnzd)).symm

open MMP.Intersection in
/-- On an integral locally Noetherian scheme, a point of coheight zero lies in the support of no
Cartier divisor. -/
private theorem notMem_cartierSupport_of_coheight_eq_zero {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] (A : X.CartierDivisor) {x : X} (hx : Order.coheight x = 0) :
    x ∉ cartierSupport A := by
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le (by simp [hx])
  have : IsArtinianRing (X.presheaf.stalk x) := isArtinianRing_iff_krullDimLE_zero.mpr this
  exact notMem_cartierSupport_of_isArtinianRing A x

/-- Every Cartier divisor on a Noetherian integral scheme has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [TopologicalSpace.NoetherianSpace X] (A : X.CartierDivisor) :
    ∃ w : Divisor X, IsWeilDivisorOfCartier A w := by
  have hfin := MMP.Mori.finite_setOf_genericPoint_mem (isClosed_cartierSupport A)
    (fun s hs h0 => notMem_cartierSupport_of_coheight_eq_zero A h0 hs)
  refine ⟨Finsupp.ofSupportFinite (fun P => primeDivisorOrder P A) (hfin.subset fun P hP => ?_),
    fun P => ?_⟩
  · by_contra h
    have hg : (primeDivisorSubvariety P).genericPoint = P.genericPoint := rfl
    refine hP ((isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset fun h' => h ?_)
    show P.genericPoint ∈ cartierSupport A
    rw [← hg]
    exact genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact isOrderAlong_primeDivisorOrder A P

/-- The Weil divisor of the realization of `q • C`, for a `ℚ`-Cartier divisor `C` with Weil
`ℚ`-divisor `D`, is `q • D`. -/
private theorem coeff_eq_mul_of_isWeilDivisorOfCartier_realization {X : Scheme.{0}}
    [IsLocallyNoetherian X] {D : QDivisor X} {C : KCartierDivisor ℚ X}
    (hC : ∀ P : MMP.Mori.PrimeDivisor X,
      D.coeff P = C.sum fun E c => c * (primeDivisorOrder P E : ℚ)) {q : ℕ}
    (h : ∀ E, ∃ n : ℤ, ((q : ℚ) • C) E = n) {B : Divisor X}
    (hB : IsWeilDivisorOfCartier (KCartierDivisor.realization ((q : ℚ) • C) h) B)
    (P : MMP.Mori.PrimeDivisor X) : (B.coeff P : ℚ) = q * D.coeff P := by
  classical
  have hc : ∀ E, ((Classical.choose (h E) : ℤ) : ℚ) = ((q : ℚ) • C) E := fun E =>
    (Classical.choose_spec (h E)).symm
  rw [← (hB P).primeDivisorOrder_eq, KCartierDivisor.realization, Finsupp.sum, map_sum,
    Int.cast_sum, hC P, Finsupp.sum, Finset.mul_sum]
  have hz : ∀ E ∈ C.support, E ∉ ((q : ℚ) • C).support →
      (q : ℚ) * (C E * (primeDivisorOrder P E : ℚ)) = 0 := fun E _ hE => by
    rw [Finsupp.notMem_support_iff, Finsupp.smul_apply, smul_eq_mul] at hE
    rw [← mul_assoc, hE, zero_mul]
  rw [← Finset.sum_subset (Finsupp.support_smul (b := (q : ℚ)) (g := C)) hz]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [map_zsmul, smul_eq_mul, Int.cast_mul, hc, Finsupp.smul_apply, smul_eq_mul, mul_assoc]

/-- An integral scheme is its own unique irreducible component. -/
private theorem univ_mem_irreducibleComponents (X : Scheme.{0}) [IsIntegral X] :
    (Set.univ : Set X) ∈ irreducibleComponents X := by
  rw [irreducibleComponents_eq_singleton]; rfl

private theorem specializes_genericPoint {Y : Scheme.{0}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z)).specializes

private theorem genericPoint_specializes {Y : Scheme.{0}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

/-- A rational function `φ ∈ K(Y)`, read in every factor of `K(Y) = ∏_Z 𝒪_{Y,η_Z}`. -/
private noncomputable def toRationalFunctions {Y : Scheme.{0}} [IsIntegral Y] :
    Y.functionField →+* RationalFunctions Y :=
  Pi.ringHom fun Z => (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom

private theorem stalkSpecializes_toRationalFunctions {Y : Scheme.{0}} [IsIntegral Y]
    (Z : irreducibleComponents Y) (φ : Y.functionField) :
    (Y.presheaf.stalkSpecializes (genericPoint_specializes Z)).hom
      (toRationalFunctions φ Z) = φ := by
  change (Y.presheaf.stalkSpecializes _).hom ((Y.presheaf.stalkSpecializes _).hom φ) = φ
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- `v_P` on the factor `𝒪_{Y,η}` of `K(Y)` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (P : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y P.component)) :
    P.valuation s = (P.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes P.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

/-- The order along `P` of the unit of `K(Y)` defined by `φ ≠ 0` is `ord_{η_P}(φ)`. -/
private theorem ord_toRationalFunctions {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (P : MMP.Mori.PrimeDivisor Y) {φ : Y.functionField}
    (hφ : φ ≠ 0) (ψ : (RationalFunctions Y)ˣ) (hψ : (ψ : RationalFunctions Y) =
      toRationalFunctions φ) : P.ord ψ = Scheme.ord φ P.genericPoint := by
  have h2 := valuation_eq_inv_divisorialValuation P ((ψ : RationalFunctions Y) P.component)
  rw [hψ, stalkSpecializes_toRationalFunctions, ← hψ, P.valuation_component,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hφ, ← WithZero.exp_neg,
    neg_neg] at h2
  exact WithZero.exp_injective h2

/-- A Cartier Weil divisor on a normal integral Noetherian scheme is the Weil divisor of a
Cartier divisor. -/
private theorem exists_isWeilDivisorOfCartier_of_isCartier {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {L : Divisor X} (hL : L.IsCartier) :
    ∃ E : X.CartierDivisor, IsWeilDivisorOfCartier E L := by
  classical
  haveI : IsNoetherian X := ⟨⟩
  haveI := hL.isInvertibleModule_divisorialSheaf
  obtain ⟨E₀, ⟨e₀⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L.divisorialSheaf
  obtain ⟨w, hw⟩ := exists_isWeilDivisorOfCartier E₀
  obtain ⟨e₁⟩ := hw.nonempty_sheaf_iso_divisorialSheaf
  obtain ⟨φ, hφ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso (e₀ ≪≫ e₁)
  -- `φ` as a rational function `r₀` on the integral scheme `X`
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨Set.univ, univ_mem_irreducibleComponents X⟩⟩
  set r₀ : X.functionField := (X.presheaf.stalkSpecializes (genericPoint_specializes Z₀)).hom
    ((φ : RationalFunctions X) Z₀) with hr₀
  have hr : toRationalFunctions r₀ = (φ : RationalFunctions X) := by
    funext Z
    have hmem : ∀ W : irreducibleComponents X, (W : Set X) = Set.univ := fun W => by
      have h1 : (W : Set X) ∈ ({Set.univ} : Set (Set X)) := by
        rw [← irreducibleComponents_eq_singleton]; exact W.2
      exact h1
    have hZ : Z₀ = Z := Subtype.ext ((hmem Z₀).trans (hmem Z).symm)
    subst hZ
    change (X.presheaf.stalkSpecializes _).hom ((X.presheaf.stalkSpecializes _).hom _) = _
    rw [TopCat.Presheaf.stalkSpecializes_comp_apply, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  have hr0 : r₀ ≠ 0 := by
    intro h0
    haveI : Nontrivial (RationalFunctions X) := Pi.nontrivial_at Z₀
    rw [h0, map_zero] at hr
    exact φ.ne_zero hr.symm
  have hordφ : ∀ Q : MMP.Mori.PrimeDivisor X, Q.ord φ = Scheme.ord r₀ Q.genericPoint :=
    fun Q => ord_toRationalFunctions Q hr0 φ hr.symm
  -- the principal Cartier divisor of `r₀`
  set c : (X.totalQuotientSheaf.obj.obj (Opposite.op ⊤))ˣ :=
    Units.map (MMP.CartierDivisorSheaf.ofFunctionField (X := X) ⊤).toMonoidHom
      (Units.mk0 r₀ hr0) with hc
  set Pc := MMP.Intersection.principalDivisor c with hPc
  have hPord : ∀ Q : MMP.Mori.PrimeDivisor X,
      primeDivisorOrder Q Pc = Scheme.ord r₀ Q.genericPoint := by
    intro Q
    obtain ⟨⟨a, b⟩, hab⟩ :=
      IsLocalization.surj (nonZeroDivisors (X.presheaf.stalk Q.genericPoint)) r₀
    have hbK : algebraMap _ X.functionField (b : X.presheaf.stalk Q.genericPoint) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
    have hb0 : (b : X.presheaf.stalk Q.genericPoint) ≠ 0 := nonZeroDivisors.ne_zero b.2
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at hab
      exact mul_ne_zero hr0 hbK hab
    have hloc : IsLocalEquationAt Pc Q.genericPoint
        (X.totalQuotientSheaf.presheaf.germ ⊤ Q.genericPoint trivial (c : _)) :=
      ⟨⊤, trivial, c, isLocalEquationOn_principalDivisor c, rfl⟩
    have hfrac : IsFraction (X.totalQuotientSheaf.presheaf.germ ⊤ Q.genericPoint trivial (c : _))
        a b := by
      refine ⟨isUnit_stalkToTotalQuotient_of_mem_nonZeroDivisors b.2, ?_⟩
      apply (totalQuotientStalkToFunctionField_bijective Q.genericPoint).1
      rw [map_mul, totalQuotientStalkToFunctionField_stalkToTotalQuotient,
        totalQuotientStalkToFunctionField_stalkToTotalQuotient]
      erw [MMP.CartierDivisorSheaf.totalQuotientStalkToFunctionField_germ_top_ofFunctionField]
      rw [mul_comm]
      exact hab
    have : Ring.KrullDimLE 1 (X.presheaf.stalk (primeDivisorSubvariety Q).genericPoint) :=
      krullDimLE_of_coheight_le Q.coheight_genericPoint.le
    have hO := isOrderAlong_of_isFraction (V := primeDivisorSubvariety Q) hloc
      (mem_nonZeroDivisors_of_ne_zero ha0) b.2 hfrac
    rw [hO.primeDivisorOrder_eq]
    have h1 := Scheme.ord_mul (x := Q.genericPoint) hr0 hbK
    rw [hab, scheme_ord_algebraMap Q.coheight_genericPoint ha0,
      scheme_ord_algebraMap Q.coheight_genericPoint hb0] at h1
    change ((Ring.ord _ a).toNat : ℤ) -
      ((Ring.ord _ (b : X.presheaf.stalk Q.genericPoint)).toNat : ℤ) = _
    linarith
  refine ⟨E₀ + Pc, fun Q => ?_⟩
  have h := isOrderAlong_primeDivisorOrder (E₀ + Pc) Q
  have e : primeDivisorOrder Q (E₀ + Pc) = L.coeff Q := by
    have hLQ := congrArg (fun D : Divisor X => D.coeff Q) hφ
    simp only [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor] at hLQ
    rw [map_add, (hw Q).primeDivisorOrder_eq, hPord, ← hordφ]
    omega
  rwa [e] at h

/-- A relatively semiample `ℚ`-divisor has a relatively free Cartier multiple. -/
private theorem exists_isRelativelyFreeDivisor_of_isRelativelySemiample {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (f : X ⟶ Z)
    (D : QDivisor X) (h : QDivisor.IsRelativelySemiample f D) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • D ∧ L.IsCartier ∧
      IsRelativelyFreeDivisor f L := by
  classical
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨C, hC, q, hq, hint, hfree⟩ := h
  obtain ⟨w, hw⟩ := exists_isWeilDivisorOfCartier
    (KCartierDivisor.realization ((q : ℚ) • C) hint)
  refine ⟨q, hq, w, ?_, hw.isCartier, ?_⟩
  · ext P
    rw [Divisor.coeff_toQDivisor, coeff_eq_mul_of_isWeilDivisorOfCartier_realization hC hint hw P]
    simp [DivisorWithCoeffs.coeff_apply, zsmul_eq_mul]
  · obtain ⟨e⟩ := hw.nonempty_sheaf_iso_divisorialSheaf
    exact epi_counit_of_iso f e.symm hfree

/-! ### The normalization components -/

/-- A unit of `K(X)` which is regular at a point `x` of the prime divisor `E` has nonnegative
order along `E`, and order zero if it is a unit at `x`. -/
private theorem zero_le_ordUnit_of_eq_stalkToRationalFunctions {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] (E : Mori.PrimeDivisor X) {x : X}
    (hxE : x ∈ E.support) (t : X.presheaf.stalk x)
    (u : (X.presheaf.stalk (componentGenericPoint X E.component))ˣ)
    (hu : (stalkToRationalFunctions X (E.support_subset_component hxE)).hom t = u) :
    0 ≤ E.ordUnit u ∧ (IsUnit t → E.ordUnit u = 0) := by
  have hspec : E.genericPoint ⤳ x := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxE
    exact specializes_iff_mem_closure.mpr hxE
  set b : E.localRing := (X.presheaf.stalkSpecializes hspec).hom t with hb
  have hbu : E.toComponent.hom b = u := by
    rw [hb, E.toComponent_stalkSpecializes hspec (E.support_subset_component hxE), hu]
  refine ⟨?_, fun ht => E.ordUnit_eq_zero_of_isUnit (ht.map _) hbu⟩
  have := E.isDiscreteValuationRing_localRing
  have hb0 : b ≠ 0 := fun h0 => u.ne_zero (by rw [← hbu, h0, map_zero])
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have h := E.valuation_eq_exp_ordUnit u
  rw [← hbu, hv, map_mul, map_pow, map_mul, map_pow, E.valuation_toComponent_of_isUnit v.isUnit,
    E.valuation_toComponent_of_irreducible hϖ, one_mul, ← WithZero.exp_nsmul] at h
  have := WithZero.exp_injective h
  simp only [nsmul_eq_mul, mul_one] at this
  omega

/-- **Pull-backs of effective divisors.** If `G` is a Cartier divisor on `Y`, `G'` its pull-back
along `j : X ⟶ Y` and `G` is effective, resp. zero, along the prime divisors through `j(x)`, then
`G'` is effective, resp. zero, along the prime divisors through `x`. -/
private theorem coeff_isPullback_of_forall {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (j : X ⟶ Y) {G : Divisor Y} (hGc : G.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, j (componentGenericPoint X Z) ∉ G.supp}
    {G' : Divisor X} (h : G.IsPullback j hB G') (x : X) :
    ((∀ Γ : Mori.PrimeDivisor Y, j x ∈ Γ.support → 0 ≤ G.coeff Γ) →
      ∀ E : Mori.PrimeDivisor X, x ∈ E.support → 0 ≤ G'.coeff E) ∧
    ((∀ Γ : Mori.PrimeDivisor Y, j x ∈ Γ.support → G.coeff Γ = 0) →
      ∀ E : Mori.PrimeDivisor X, x ∈ E.support → G'.coeff E = 0) := by
  obtain ⟨U, hU, φ, hφ⟩ := hGc (j x)
  set W := pointComponent (j x)
  have key : ∀ (r : Y.presheaf.stalk (j x)),
      (stalkToRationalFunctions Y (mem_pointComponent (j x))).hom r = (φ : RationalFunctions Y) W →
      ∀ E : Mori.PrimeDivisor X, x ∈ E.support →
        0 ≤ G'.coeff E ∧ (IsUnit r → G'.coeff E = 0) := by
    intro r hr E hxE
    have hE : (E.support ∩ j ⁻¹ᵁ U).Nonempty := ⟨x, hxE, hU⟩
    rw [h U φ hφ E hE]
    set Z := E.component
    have hxZ : x ∈ Z.1 := E.support_subset_component hxE
    have hsZ : componentGenericPoint X Z ⤳ x :=
      (isGenericPoint_componentGenericPoint X Z).specializes hxZ
    have hsY : j (componentGenericPoint X Z) ⤳ j x := hsZ.map j.continuous
    have hW : j (componentGenericPoint X Z) ∈ W.1 := by
      have : (W.1 : Set Y) = Set.univ := by
        have h1 : (W.1 : Set Y) ∈ ({Set.univ} : Set (Set Y)) := by
          rw [← irreducibleComponents_eq_singleton]; exact W.2
        exact h1
      rw [this]; trivial
    obtain ⟨a, ha⟩ := hφ.exists_unit_stalk (E.map_componentGenericPoint_mem j hE) (hB Z) hW
    have har : (a : Y.presheaf.stalk _) = (Y.presheaf.stalkSpecializes hsY).hom r := by
      apply stalkToRationalFunctions_injective hW
      rw [ha]
      change _ = (Y.presheaf.stalkSpecializes hsY ≫ Y.presheaf.stalkSpecializes _).hom r
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      exact hr.symm
    rw [pullbackComponent_eq hB hφ (E.map_componentGenericPoint_mem j hE) hW a ha]
    have hval : (Units.map (j.stalkMap (componentGenericPoint X Z)).hom.toMonoidHom a :
        X.presheaf.stalk _) = (stalkToRationalFunctions X hxZ).hom ((j.stalkMap x).hom r) := by
      change (j.stalkMap (componentGenericPoint X Z)).hom
        (a : Y.presheaf.stalk (j (componentGenericPoint X Z))) = _
      rw [har]
      exact Scheme.Hom.stalkSpecializes_stalkMap_apply j _ x hsZ r
    obtain ⟨h1, h2⟩ := zero_le_ordUnit_of_eq_stalkToRationalFunctions E hxE
      ((j.stalkMap x).hom r) _ hval.symm
    exact ⟨h1, fun hru => h2 (hru.map _)⟩
  constructor
  · intro hG E hxE
    obtain ⟨r, hr⟩ := exists_stalk_eq_of_forall_zero_le_ord (mem_pointComponent (j x)) φ
      fun Γ hΓ => by rw [← hφ Γ ⟨j x, hΓ, hU⟩]; exact hG Γ hΓ
    exact (key r hr E hxE).1
  · intro hG E hxE
    obtain ⟨a, ha⟩ := exists_unit_stalk_of_forall_ord_eq_zero (mem_pointComponent (j x)) φ
      fun Γ hΓ => by rw [← hφ Γ ⟨j x, hΓ, hU⟩]; exact hG Γ hΓ
    exact (key a ha E hxE).2 a.isUnit

/-- The unit of `K(Y)` defined by a nonzero rational function. -/
private noncomputable def unitOfFunction {Y : Scheme.{0}} [IsIntegral Y] {g : Y.functionField}
    (hg : g ≠ 0) : (RationalFunctions Y)ˣ :=
  Units.map toRationalFunctions.toMonoidHom (Units.mk0 g hg)

end Conversion

/-- The generic point of a prime divisor lies on it. -/
private theorem genericPoint_mem_support {X : Scheme.{0}} (D : Mori.PrimeDivisor X) :
    D.genericPoint ∈ D.support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- The generic point of a prime divisor `P` lies in the support of a divisor only if `P` is a
component of it. -/
private theorem genericPoint_notMem_supp {Y : Scheme.{0}} {D : Divisor Y}
    (P : Mori.PrimeDivisor Y) (hP : D.coeff P = 0) : P.genericPoint ∉ D.supp := by
  rw [DivisorWithCoeffs.mem_supp_iff]
  rintro ⟨E, hE, hPE⟩
  obtain rfl := MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hPE
  exact hE hP

/-- The degree of a divisor does not change when it is regarded as a `ℚ`-divisor. -/
private theorem sum_toQDivisor {X : Scheme.{0}} (D : Divisor X) :
    (Divisor.toQDivisor D).sum (fun _ a => a) = ((D.sum fun _ a => a : ℤ) : ℚ) := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), hf, hg]; push_cast; ring
  | single P a =>
    have : Divisor.toQDivisor (Finsupp.single P a) = Finsupp.single P (a : ℚ) := by
      ext E
      change ((Finsupp.single P a E : ℤ) : ℚ) = Finsupp.single P (a : ℚ) E
      rw [Finsupp.single_apply, Finsupp.single_apply]; split_ifs <;> simp
    rw [this, Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]

/-- **Floor curves of a semiample dlt surface have nonnegative adjoint degree.** If `(S, B)` is
a projective `ℚ`-factorial dlt surface pair with `K_S + B` semiample and `(C, B_C)` is obtained
by an adjunction step onto a floor component `P`, then `deg(K_C + B_C) ≥ 0`. Take a top form `σ`
with a simple pole along `P` and residue `ρ`; then `(div σ + B)|_C = div ρ + B_C`. A free multiple
`L ∼ m(div σ + B)` has a member `G = L + div ψ ≥ 0` not containing `P`, whose restriction
`m(div ρ + B_C) + div ψ|_C` is effective; principal divisors have degree zero on `C`. -/
private theorem zero_le_degree_of_isAdjunctionStep {S : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)}
    (hS : Mori.IsProjectiveVariety ℂ sS) (hdim : topologicalKrullDim S = 2)
    (hQ : IsQFactorial sS) {B : QDivisor S} (hB : IsPair sS B)
    (hdlt : MMP.Intersection.IsDltPair sS B) {K : Divisor S} (hK : K.IsCanonicalDivisor sS 2)
    (hsemi : QDivisor.IsRelativelySemiample sS (Divisor.toQDivisor K + B))
    {C : Scheme.{0}} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] {j : C ⟶ S}
    {BC : QDivisor C} (hj : IsAdjunctionStep sS B j BC)
    (hdltC : MMP.Intersection.IsDltPair (j ≫ sS) BC)
    (KC : Divisor C) (hKC : KC.IsCanonicalDivisor (j ≫ sS) 1) :
    0 ≤ (KC.sum fun _ a => (a : ℚ)) + BC.sum fun _ a => a := by
  classical
  haveI : LocallyOfFiniteType sS := hS.toLocallyOfFiniteType
  haveI : QuasiCompact sS := hS.toQuasiCompact
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have hYv : IsNormalVariety ℂ sS := ⟨hS.toIsVariety, inferInstance⟩
  obtain ⟨hSv, P, hP1, hrange, hci, -⟩ := id hj
  haveI := hci
  haveI : LocallyOfFiniteType (j ≫ sS) := hSv.1.toLocallyOfFiniteType
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace j
  have hCP : B.coeff P = 1 := le_antisymm (hdlt.2.1 P) hP1
  have hdimC : topologicalKrullDim C = 1 := hKC.topologicalKrullDim_eq
  obtain ⟨Q⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdimC (by norm_num)
  obtain ⟨σ, hσ0, hσP, -, ρ, hρ, hρ0, -⟩ :=
    exists_form_of_residue_order sS hYv (n := 1) hdim j hSv P hrange Q
  have hD : (Divisor.toQDivisor (divisorOfForm σ) + B).IsQCartier :=
    isQCartier_of_isQFactorial sS hQ _
  obtain ⟨hgen, hpb⟩ := hj.isPullback_divisorOfForm_add_of_isPoincareResidue (n := 1) hdim P
    hrange σ hσ0 hσP ρ hρ hD
  obtain ⟨m, hm, L, hL, hLc, hfree⟩ :=
    exists_isRelativelyFreeDivisor_of_isRelativelySemiample sS _ hsemi
  obtain ⟨φ, hφ⟩ : (divisorOfForm σ).LinearlyEquivalent K := by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hYv hK (m := 1) hσ0
  set L' : Divisor S := L + principalDivisor (φ ^ m) with hL'_def
  have hL'coeff : ∀ Γ, (L'.coeff Γ : ℚ) = m * ((divisorOfForm σ).coeff Γ + B.coeff Γ) := by
    intro Γ
    have h1 := congrArg (fun D : QDivisor S => D.coeff Γ) hL
    have h2 := congrArg (fun D : Divisor S => D.coeff Γ) hφ
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      zsmul_eq_mul] at h1
    simp only [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor] at h2
    simp only [hL'_def, DivisorWithCoeffs.coeff_add, coeff_principalDivisor, PrimeDivisor.ord_pow]
    push_cast
    rw [h1, nsmul_eq_mul]
    have h2' : ((divisorOfForm σ).coeff Γ : ℚ) - K.coeff Γ = Γ.ord φ := by exact_mod_cast h2
    push_cast
    linear_combination (-(m : ℚ)) * h2'
  have hL' : Divisor.toQDivisor L' = (m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + B) := by
    ext Γ
    rw [Divisor.coeff_toQDivisor, hL'coeff Γ]
    simp [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul]
    ring
  have hL'c : L'.IsCartier := hLc.add (Divisor.isCartier_principalDivisor _)
  have hL'P : L'.coeff P = 0 := by
    have := hL'coeff P
    rw [coeff_divisorOfForm, hσP, hCP] at this
    exact_mod_cast (by simpa using this : (L'.coeff P : ℚ) = 0)
  obtain ⟨D', hD', hpbD⟩ := hpb m hm L' hL' hL'c
  have hjη : ∀ Z : irreducibleComponents C, j (componentGenericPoint C Z) = P.genericPoint :=
    fun Z => by rw [componentGenericPoint_eq_genericPoint Z]; exact map_genericPoint_eq_of_range_eq j P hrange
  obtain ⟨s⟩ : Nonempty C := ⟨genericPoint C⟩
  obtain ⟨U₀, hU₀, ψ, hψ1, hψ2⟩ :=
    exists_coeff_add_ord_eq_zero_of_isRelativelyFree sS hLc hfree (j s)
  set ψ' := ψ * (φ ^ m)⁻¹ with hψ'_def
  set G : Divisor S := L' + principalDivisor ψ' with hG_def
  have hGcoeff : ∀ Γ, G.coeff Γ = L.coeff Γ + Γ.ord ψ := fun Γ => by
    simp only [hG_def, hL'_def, hψ'_def, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
      PrimeDivisor.ord_mul, PrimeDivisor.ord_inv]
    ring
  have hψ'P : (principalDivisor ψ').coeff P = 0 := by
    have h1 := hψ2 P (by rw [← hrange]; exact ⟨s, rfl⟩)
    have h2 := hGcoeff P
    rw [hG_def, DivisorWithCoeffs.coeff_add, hL'P, zero_add] at h2
    rw [h2, h1]
  have hGP : G.coeff P = 0 := by rw [hG_def, DivisorWithCoeffs.coeff_add, hL'P, hψ'P, add_zero]
  have hB₁ : ∀ Z : irreducibleComponents C, j (componentGenericPoint C Z) ∉ L'.supp :=
    fun Z => by rw [hjη]; exact genericPoint_notMem_supp P hL'P
  have hB₂ : ∀ Z : irreducibleComponents C,
      j (componentGenericPoint C Z) ∉ (principalDivisor ψ').supp :=
    fun Z => by rw [hjη]; exact genericPoint_notMem_supp P hψ'P
  have hB' : ∀ Z : irreducibleComponents C, j (componentGenericPoint C Z) ∉ G.supp :=
    fun Z => by rw [hjη]; exact genericPoint_notMem_supp P hGP
  have hpbG := (hpbD.of_eq rfl (hB₂ := hB₁)).add hL'c (Divisor.isCartier_principalDivisor ψ') hB'
    (Divisor.isPullback_principalDivisor ψ' hB₂)
  have hGc : G.IsCartier := hL'c.add (Divisor.isCartier_principalDivisor _)
  have hU₀top : ∀ Γ : Mori.PrimeDivisor S, (Γ.support ∩ sS ⁻¹ᵁ U₀).Nonempty := by
    intro Γ
    obtain ⟨y⟩ : Nonempty Γ.support := ⟨⟨Γ.genericPoint, genericPoint_mem_support Γ⟩⟩
    refine ⟨y, y.2, ?_⟩
    have : sS.base y = sS.base (j s) := Subsingleton.elim _ _
    show sS.base y ∈ U₀
    rw [this]; exact hU₀
  set ψC := pullbackRationalFunction j ψ' hB₂ with hψC
  have hnn : ∀ E : Mori.PrimeDivisor C, 0 ≤ (D' + principalDivisor ψC).coeff E := by
    intro E
    exact (coeff_isPullback_of_forall j hGc hpbG E.genericPoint).1 (fun Γ _ => by
      rw [hGcoeff]; exact hψ1 Γ (hU₀top Γ)) E (genericPoint_mem_support E)
  -- degrees
  have hsm := isSmoothScheme_of_topologicalKrullDim_eq_one hSv hdimC
  have hprop : IsProper (j ≫ sS) := by
    haveI : IsProper sS := (instIsProperVarietyOfIsProjectiveVariety ℂ sS).toIsProper
    infer_instance
  have hdeg0 := MMP.Flips.sum_principalDivisor_eq_zero hSv hsm hprop hdimC ψC
  obtain ⟨χ, hχ⟩ : (divisorOfForm ρ).LinearlyEquivalent KC := by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hSv hKC (m := 1) hρ0
  have hdegχ := MMP.Flips.sum_principalDivisor_eq_zero hSv hsm hprop hdimC χ
  have h1 : 0 ≤ (D' + principalDivisor ψC).sum (fun _ a => a) :=
    Finsupp.sum_nonneg fun E _ => hnn E
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), hdeg0, add_zero] at h1
  have h2 : (divisorOfForm ρ).sum (fun _ a => a) = KC.sum (fun _ a => a) := by
    have := congrArg (fun D : Divisor C => D.sum fun _ a => a) hχ
    beta_reduce at this
    rw [Finsupp.sum_sub_index (fun _ _ _ => rfl), hdegχ] at this
    omega
  set deg : QDivisor C →+ ℚ := Finsupp.liftAddHom fun _ => AddMonoidHom.id ℚ with hdeg_def
  have hdeg : ∀ D : QDivisor C, D.sum (fun _ a => a) = deg D := fun D => by
    rw [hdeg_def, Finsupp.liftAddHom_apply]
    rfl
  have h3 := congrArg deg hD'
  rw [map_zsmul, map_add, ← hdeg, ← hdeg, ← hdeg, sum_toQDivisor, sum_toQDivisor, h2] at h3
  have hm0 : (0 : ℚ) < m := by exact_mod_cast hm
  have h1' : (0 : ℚ) ≤ ((D'.sum fun _ a => a : ℤ) : ℚ) := by exact_mod_cast h1
  have h4 : ((m : ℤ) : ℚ) * (((KC.sum fun _ a => a : ℤ) : ℚ) + BC.sum fun _ a => a) ≥ 0 := by
    rw [h3, zsmul_eq_mul] at h1'
    exact h1'
  push_cast at h4
  exact (mul_nonneg_iff_of_pos_left hm0).1 h4

/-- **Admissible generation on a collection of dlt curves**, in the form used here: for proper
normal curves with dlt boundaries whose adjoints have nonnegative degree, admissible systems
generate in every sufficiently divisible even degree, which carries the stratified setting. -/
private theorem exists_admissibleSections_generatesOn_of_dlt_curve {J : Type u} [Finite J]
    {C : J → Scheme.{0}} [∀ j, IsIntegral (C j)] [∀ j, IsLocallyNoetherian (C j)]
    [∀ j, IsNormal (C j)] {sC : ∀ j, C j ⟶ Spec (.of ℂ)} (hvar : ∀ j, IsNormalVariety ℂ (sC j))
    (hprop : ∀ j, IsProper (sC j)) (hdim : ∀ j, topologicalKrullDim (C j) = 1)
    {BC : ∀ j, QDivisor (C j)} (hdlt : ∀ j, MMP.Intersection.IsDltPair (sC j) (BC j))
    (hdeg : ∀ j (K : Divisor (C j)), K.IsCanonicalDivisor (sC j) 1 →
      0 ≤ (K.sum fun _ a => (a : ℚ)) + (BC j).sum fun _ a => a) :
    ∃ m₁ : ℕ, 0 < m₁ ∧ ∀ m : ℕ, 0 < m → m₁ ∣ m → Even m →
      IsStratifiedSectionSetting sC BC 1 m ∧
      ∀ (Rf : ResidueRestriction sC BC 1 m) j (y : C j),
        ∃ t ∈ admissibleSections Rf, ∃ U : (C j).Opens, y ∈ U ∧
          Mori.GeneratesOn (BC j) m U (t j).1 := by
  have hsm : ∀ j, IsSmoothScheme (sC j) := fun j =>
    isSmoothScheme_of_topologicalKrullDim_eq_one (hvar j) (hdim j)
  have hK : ∀ j, ∃ K : Divisor (C j), K.IsCanonicalDivisor (sC j) 1 := fun j => by
    haveI := (hvar j).1
    haveI := hprop j
    haveI : CompactSpace (C j) := QuasiCompact.compactSpace_of_compactSpace (sC j)
    exact exists_isCanonicalDivisor_of_isSmoothScheme (sC j) (hsm j) (n := 1)
      (by exact_mod_cast hdim j)
  choose K hK using hK
  exact exists_admissibleSections_generatesOn_of_curve hvar hsm hprop hdim
    (fun j P => ⟨(hdlt j).1.2.1 P, (hdlt j).2.1 P⟩) hK fun j => hdeg j (K j) (hK j)

/-- **Regular functions on a proper normal variety are constant.** A rational function on a
normal integral scheme, proper over an algebraically closed field `k`, with nonnegative order
along every prime divisor is a constant of `k`. -/
private theorem exists_eq_algebraMap_of_forall_ord_nonneg {k : Type} [Field k] [IsAlgClosed k]
    {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) [IsProper sX]
    (g : X.functionField) (hg : ∀ Γ : MMP.Mori.PrimeDivisor X, 0 ≤ X.ord g Γ.genericPoint) :
    ∃ c : k, g = (letI := MMP.Mori.functionFieldAlgebra sX; algebraMap k X.functionField c) := by
  classical
  by_cases hg0 : g = 0
  · exact ⟨0, by rw [hg0, map_zero]⟩
  have ha : ∀ x : X, ∃ b : X.presheaf.stalk x,
      algebraMap (X.presheaf.stalk x) X.functionField b = g := fun x =>
    MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg x hg0
      (fun Γ _ => hg Γ)
  -- glue
  have hlocal (y : X) : ∃ (U : X.Opens) (hy : y ∈ U) (b : Γ(X, U)),
      ∃ hU : Nonempty U, @Scheme.germToFunctionField X _ U hU b = g := by
    obtain ⟨b, hb⟩ := ha y
    obtain ⟨U, hy, c, hc⟩ := X.presheaf.exists_germ_eq b
    let : Nonempty U := ⟨⟨y, hy⟩⟩
    exact ⟨U, hy, c, inferInstance, by
      rw [← X.algebraMap_germ_eq_germToFunctionField hy c, hc, hb]⟩
  choose U hy b hU hb using hlocal
  let (y : X) : Nonempty (U y) := hU y
  have hgen (y : X) : genericPoint X ∈ U y :=
    ((genericPoint_spec X).mem_open_set_iff (U y).isOpen).mpr ⟨y, trivial, hy y⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf U b := by
    intro i j
    have hmem : genericPoint X ∈ U i ⊓ U j := ⟨hgen i, hgen j⟩
    apply germ_injective_of_isIntegral X (U := U i ⊓ U j) (genericPoint X) hmem
    rw [X.presheaf.germ_res_apply, X.presheaf.germ_res_apply]
    exact (hb i).trans (hb j).symm
  obtain ⟨c, hc, -⟩ := X.sheaf.existsUnique_gluing' U ⊤
    (fun i ↦ homOfLE le_top) (by
      intro y _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hy y⟩) b hcompat
  have hcg : X.presheaf.germ ⊤ (genericPoint X) trivial c = g := by
    rw [← hb (genericPoint X), ← hc (genericPoint X)]
    exact (X.presheaf.germ_res_apply (homOfLE le_top) (genericPoint X)
      (hgen (genericPoint X)) c).symm
  -- constants
  let φ : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop).hom
  letI := φ.toAlgebra
  have hfin : φ.Finite := by
    have h1 := finite_appTop_of_universallyClosed k sX
    exact RingHom.Finite.comp h1 (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  have : Module.Finite k Γ(X, ⊤) := hfin
  have : Algebra.IsIntegral k Γ(X, ⊤) := inferInstance
  obtain ⟨c', hc'⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤))).2 c
  refine ⟨c', ?_⟩
  rw [← hcg, ← hc']
  rfl

/-- **Sections of a numerically trivial adjoint are multiples of one form.** On a normal
variety `T`, proper over `ℂ`, let `ρ` be a nonzero rational `m`-canonical form with
`div ρ = -m B_T`. Then every section of `H⁰(T, m(K_T + B_T))` is a constant multiple of `ρ`. -/
private theorem exists_eq_smul_of_mem_logPluricanonicalSections {T : Scheme.{0}} [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T]
    {sT : T ⟶ Spec (.of ℂ)} [IsProper sT] {d : ℕ} (hd : topologicalKrullDim T = d) {m : ℕ}
    {BT : QDivisor T} {ρ : RationalPluriForms sT d m} (hρ0 : ρ ≠ 0)
    (hρ : ∀ Q : MMP.Mori.PrimeDivisor T, (Q.ordForm ρ : ℚ) = -(m * BT.coeff Q))
    {u : RationalPluriForms sT d m} (hu : u ∈ logPluricanonicalSections sT d m BT) :
    ∃ c : ℂ, u = c • ρ := by
  classical
  by_cases hu0 : u = 0
  · exact ⟨0, by rw [hu0, zero_smul]⟩
  letI := MMP.Mori.functionFieldAlgebra sT
  obtain ⟨b⟩ := exists_basis_topForms (sX := sT) hd
  let e : Module.Basis Unit T.functionField (RationalPluriForms sT d m) :=
    MMP.Mori.ZTensorPower.basis b (m : ℤ)
  have hρr : e.repr ρ () ≠ 0 := by
    intro h
    apply hρ0
    rw [← MMP.Mori.basis_unit_repr_smul e ρ, h, zero_smul]
  set ψ : T.functionField := e.repr u () / e.repr ρ () with hψdef
  have hψ : u = ψ • ρ := by
    conv_lhs => rw [← MMP.Mori.basis_unit_repr_smul e u]
    conv_rhs => rw [← MMP.Mori.basis_unit_repr_smul e ρ]
    rw [smul_smul, hψdef, div_mul_cancel₀ _ hρr]
  have hψ0 : ψ ≠ 0 := by
    intro h; apply hu0; rw [hψ, h, zero_smul]
  have hord : ∀ Γ : MMP.Mori.PrimeDivisor T, 0 ≤ T.ord ψ Γ.genericPoint := by
    intro Γ
    have h1 := (MMP.Mori.mem_pluricanonicalSections.mp hu).2 Γ
      ⟨Γ.genericPoint, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
        trivial⟩ hu0
    rw [MMP.Mori.DivisorWithCoeffs.coeff_roundDown, hψ,
      Γ.ordForm_smul_of_topologicalKrullDim_eq hd hψ0 hρ0] at h1
    have h2 := hρ Γ
    have h3 : ((m : ℤ) • BT).coeff Γ = (m : ℚ) * BT.coeff Γ := by
      change ((m : ℤ) • BT) Γ = _
      rw [Finsupp.smul_apply, zsmul_eq_mul]; push_cast; rfl
    rw [h3] at h1
    have h4 := Int.floor_le ((m : ℚ) * BT.coeff Γ)
    have h5 : ((T.ord ψ Γ.genericPoint + Γ.ordForm ρ + ⌊(m : ℚ) * BT.coeff Γ⌋ : ℤ) : ℚ) ≥ 0 := by
      exact_mod_cast h1
    push_cast at h5
    have h6 : ((T.ord ψ Γ.genericPoint : ℤ) : ℚ) > -1 := by linarith
    exact_mod_cast (show (-1 : ℤ) < T.ord ψ Γ.genericPoint by exact_mod_cast h6)
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_forall_ord_nonneg sT ψ hord
  refine ⟨c, ?_⟩
  rw [hψ, hc]
  rfl

/-- **A form with divisor `-mB`.** If `K + B ∼_ℚ 0` on a normal surface, there is `N > 0` such
that in every positive degree `m` divisible by `N` some nonzero rational `m`-canonical form `ω`
has `div ω = -mB`. -/
private theorem exists_pluriform_ordForm_eq_neg_smul {S : Scheme.{0}} [IsIntegral S]
    [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} (hX : Mori.IsNormalVariety ℂ sS) (hdim : topologicalKrullDim S = 2)
    {B : QDivisor S} {K : Divisor S} (hK : K.IsCanonicalDivisor sS 2)
    (hK0 : (Divisor.toQDivisor K + B).QLinearlyEquivalent 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : ℕ, N ∣ m → 0 < m → ∃ ω : RationalPluriForms sS 2 m, ω ≠ 0 ∧
      ∀ Γ : Mori.PrimeDivisor S, (Γ.ordForm ω : ℚ) = -(m * B.coeff Γ) := by
  classical
  have : LocallyOfFiniteType sS := hX.1.toLocallyOfFiniteType
  have hdim2 : topologicalKrullDim S = ((2 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  obtain ⟨ω₀, hω₀0, hω₀K⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨N, hN, φ, hφ⟩ := hK0
  let Z₀ := MMP.Mori.pointComponent (genericPoint S)
  set f : S.functionField := (MMP.Positivity.componentToFunctionField Z₀).hom (φ.val Z₀) with hfdef
  have hf0 : f ≠ 0 := ((φ.isUnit.map (Pi.evalRingHom _ Z₀)).map _).ne_zero
  have hordf : ∀ Γ : Mori.PrimeDivisor S,
      (S.ord f Γ.genericPoint : ℚ) = N * (K.coeff Γ + B.coeff Γ) := by
    intro Γ
    have h1 := MMP.Positivity.ord_eq_ord_componentToFunctionField Γ φ
    have hZ : Γ.component = Z₀ := Subsingleton.elim
      (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := S)) _ _
    rw [hZ, ← hfdef] at h1
    have h2 := congrArg (fun G : QDivisor S => G.coeff Γ) hφ
    simp only [sub_zero, MMP.Mori.DivisorWithCoeffs.coeff_smul,
      MMP.Mori.DivisorWithCoeffs.coeff_add,
      Divisor.coeff_toQDivisor, MMP.Mori.coeff_principalDivisor, zsmul_eq_mul] at h2
    rw [← h1, ← h2]
    push_cast; ring
  refine ⟨N, hN, fun m hNm hm => ?_⟩
  obtain ⟨r, hr⟩ := hNm
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
  letI := MMP.Mori.functionFieldAlgebra sS
  set τ := MMP.CyclicChartDifferent.Aux.pluriPow ω₀ M with hτdef
  have hτ0 : τ ≠ 0 := MMP.CyclicChartDifferent.Aux.pluriPow_ne_zero hdim2 hω₀0 M
  have hfr0 : (f ^ (-(r : ℤ))) ≠ 0 := zpow_ne_zero _ hf0
  refine ⟨(f ^ (-(r : ℤ))) • τ, smul_ne_zero hfr0 hτ0, fun Γ => ?_⟩
  rw [Γ.ordForm_smul_of_topologicalKrullDim_eq hdim2 hfr0 hτ0, hτdef,
    MMP.CyclicChartDifferent.Aux.ordForm_pluriPow hdim2 hω₀0 Γ M, MMP.Mori.ord_zpow _ hf0, hω₀K Γ]
  have h1 := hordf Γ
  have hr' : ((M + 1 : ℕ) : ℚ) = N * r := by exact_mod_cast hr
  push_cast at h1 hr' ⊢
  rw [h1]
  linear_combination ((K.coeff Γ : ℚ) + B.coeff Γ) * hr'

/-- **Local generators of a semiample adjoint.** If `K + B` is semiample on a projective normal
surface, there is `N > 0` such that every point has a section of `N(K + B)` generating it on a
neighbourhood: for a free multiple `L` of `K + B`, a member `L + div ψ` avoiding the point gives
the section `ψ · ω^{⊗N}`, `div ω = K`. -/
private theorem exists_generatesOn_of_isRelativelySemiample {S : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)}
    (hS : Mori.IsProjectiveVariety ℂ sS) (hdim : topologicalKrullDim S = 2) {B : QDivisor S}
    {K : Divisor S} (hK : K.IsCanonicalDivisor sS 2)
    (hsemi : QDivisor.IsRelativelySemiample sS (Divisor.toQDivisor K + B)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : S, ∃ σ ∈ logPluricanonicalSections sS 2 N B,
      ∃ V : S.Opens, x ∈ V ∧ GeneratesOn B N V σ := by
  classical
  haveI : LocallyOfFiniteType sS := hS.toLocallyOfFiniteType
  haveI : QuasiCompact sS := hS.toQuasiCompact
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have hX : IsNormalVariety ℂ sS := ⟨hS.toIsVariety, inferInstance⟩
  have hdim2 : topologicalKrullDim S = ((2 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  obtain ⟨N, hN, L, hL, hLc, hfree⟩ :=
    exists_isRelativelyFreeDivisor_of_isRelativelySemiample sS _ hsemi
  obtain ⟨ω₀, hω₀0, hω₀K⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  set τ := MMP.CyclicChartDifferent.Aux.pluriPow ω₀ M with hτdef
  have hτ0 : τ ≠ 0 := MMP.CyclicChartDifferent.Aux.pluriPow_ne_zero hdim2 hω₀0 M
  have hLcoeff : ∀ Γ, (L.coeff Γ : ℚ) = ((M + 1 : ℕ) : ℚ) * (K.coeff Γ + B.coeff Γ) := by
    intro Γ
    have h1 := congrArg (fun D : QDivisor S => D.coeff Γ) hL
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      nsmul_eq_mul] at h1
    exact h1
  refine ⟨M + 1, by omega, fun x => ?_⟩
  obtain ⟨U₀, hU₀, ψ, hψ1, hψ2⟩ := exists_coeff_add_ord_eq_zero_of_isRelativelyFree sS hLc hfree x
  have hU₀top : ∀ Γ : Mori.PrimeDivisor S, (Γ.support ∩ sS ⁻¹ᵁ U₀).Nonempty := by
    intro Γ
    obtain ⟨y⟩ : Nonempty Γ.support := ⟨⟨Γ.genericPoint, genericPoint_mem_support Γ⟩⟩
    refine ⟨y, y.2, ?_⟩
    have : sS.base y = sS.base x := Subsingleton.elim _ _
    show sS.base y ∈ U₀
    rw [this]; exact hU₀
  set Z₀ := MMP.Mori.pointComponent (genericPoint S)
  set g : S.functionField := (MMP.Positivity.componentToFunctionField Z₀).hom (ψ.val Z₀) with hgdef
  have hg0 : g ≠ 0 := ((ψ.isUnit.map (Pi.evalRingHom _ Z₀)).map _).ne_zero
  have hordg : ∀ Γ : Mori.PrimeDivisor S, S.ord g Γ.genericPoint = Γ.ord ψ := by
    intro Γ
    have h1 := MMP.Positivity.ord_eq_ord_componentToFunctionField Γ ψ
    have hZ : Γ.component = Z₀ := Subsingleton.elim
      (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := S)) _ _
    rw [hZ, ← hgdef] at h1
    exact h1.symm
  have hσ0 : g • τ ≠ 0 := smul_ne_zero hg0 hτ0
  -- `ord_Γ σ + N b_Γ = (L + div ψ)_Γ`
  have hkey : ∀ Γ : Mori.PrimeDivisor S,
      ((Γ.ordForm (g • τ) : ℤ) : ℚ) + ((M + 1 : ℕ) : ℚ) * B.coeff Γ =
        ((L.coeff Γ + Γ.ord ψ : ℤ) : ℚ) := by
    intro Γ
    rw [Γ.ordForm_smul_of_topologicalKrullDim_eq hdim2 hg0 hτ0, hτdef,
      MMP.CyclicChartDifferent.Aux.ordForm_pluriPow hdim2 hω₀0 Γ M, hω₀K Γ, hordg Γ]
    push_cast
    rw [hLcoeff Γ]
    push_cast
    ring
  -- `N B` is integral
  have hint : ∀ Γ : Mori.PrimeDivisor S, ⌊((M + 1 : ℕ) : ℤ) • B.coeff Γ⌋ =
      L.coeff Γ - ((M + 1 : ℕ) : ℤ) * K.coeff Γ := by
    intro Γ
    rw [Int.floor_eq_iff]
    have := hLcoeff Γ
    rw [zsmul_eq_mul]
    push_cast at this ⊢
    constructor <;> nlinarith
  have hmem : g • τ ∈ logPluricanonicalSections sS 2 (M + 1) B := by
    refine (mem_pluricanonicalSections_of_ne_bot (by simp)).2 fun Γ _ _ => ?_
    rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, hint Γ]
    have h1 := hkey Γ
    have h2 : (0 : ℚ) ≤ ((L.coeff Γ + Γ.ord ψ : ℤ) : ℚ) := by exact_mod_cast hψ1 Γ (hU₀top Γ)
    have h3 := hLcoeff Γ
    have h4 : ((Γ.ordForm (g • τ) : ℤ) : ℚ) + ((L.coeff Γ - ((M + 1 : ℕ) : ℤ) * K.coeff Γ : ℤ) : ℚ)
        ≥ 0 := by
      push_cast at h1 h2 h3 ⊢
      linarith
    exact_mod_cast h4
  set E : Divisor S := L + principalDivisor ψ with hEdef
  have hEcoeff : ∀ Γ, E.coeff Γ = L.coeff Γ + Γ.ord ψ := fun Γ => by
    simp [hEdef, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  have hzero : ∀ Γ : Mori.PrimeDivisor S, (Γ.support ∩ (E.supp.compl : Set S)).Nonempty →
      E.coeff Γ = 0 := by
    rintro Γ ⟨y, hyΓ, hyV⟩
    by_contra hne
    exact hyV (DivisorWithCoeffs.mem_supp_iff.2 ⟨Γ, hne, hyΓ⟩)
  refine ⟨g • τ, hmem, E.supp.compl, ?_, hσ0, fun Γ hΓ => ?_⟩
  · intro hx
    obtain ⟨Γ, hΓ, hxΓ⟩ := DivisorWithCoeffs.mem_supp_iff.1 hx
    exact hΓ (by rw [hEcoeff]; exact hψ2 Γ hxΓ)
  · have h1 := hkey Γ
    rw [← hEcoeff, hzero Γ hΓ] at h1
    push_cast at h1 ⊢
    exact h1

section ResidueRestrictionExists

open MMP.Flips

/-- A scheme projective over a field is quasi-compact. -/
private theorem compactSpace_of_isProjectiveMorphism {X : Scheme.{0}}
    {s : X ⟶ Spec (.of ℂ)} (hs : IsProjectiveMorphism s) : CompactSpace X :=
  haveI : IsProper s := isProper_of_isProjectiveMorphism s hs
  (quasiCompact_iff_compactSpace s).mp inferInstance

private theorem topologicalKrullDim_eq_add_one_of_isAdjunctionStep {Y T : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sY] {BY : QDivisor Y} {j : T ⟶ Y} {BT : QDivisor T}
    (hj : IsAdjunctionStep sY BY j BT) {e : ℕ} (he : topologicalKrullDim T = e) :
    topologicalKrullDim Y = (e + 1 : ℕ) := by
  haveI : IsIntegral T := hj.1.1.toIsIntegral
  haveI : LocallyOfFiniteType (j ≫ sY) := hj.1.1.toLocallyOfFiniteType
  have h1 := hj.trdeg_add_one
  have h2 := topologicalKrullDim_eq_toNat_trdeg (j ≫ sY)
  have h3 := topologicalKrullDim_eq_toNat_trdeg sY
  rw [he] at h2
  rw [h3]
  have : e = (letI := functionFieldAlgebra (j ≫ sY)
      (Algebra.trdeg ℂ T.functionField).toNat) := by exact_mod_cast h2
  congr 1
  omega

/-- An adjunction stratum of a surface is a curve. -/
private theorem topologicalKrullDim_eq_one_of_isAdjunctionStep {S C : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] [IsIntegral C] {sS : S ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sS] (hdim : topologicalKrullDim S = 2) {B : QDivisor S} {j : C ⟶ S}
    {BC : QDivisor C} (hj : IsAdjunctionStep sS B j BC) :
    topologicalKrullDim C = (1 : ℕ) := by
  have : LocallyOfFiniteType (j ≫ sS) := hj.1.1.toLocallyOfFiniteType
  have h1 := hj.trdeg_add_one
  have h2 := topologicalKrullDim_eq_toNat_trdeg sS
  rw [hdim] at h2
  have h2' : (letI := functionFieldAlgebra sS;
      (Algebra.trdeg ℂ S.functionField).toNat) = 2 := by
    have : ((2 : ℕ) : WithBot ℕ∞) = ((letI := functionFieldAlgebra sS;
        (Algebra.trdeg ℂ S.functionField).toNat : ℕ) : WithBot ℕ∞) := h2
    exact_mod_cast this.symm
  rw [topologicalKrullDim_eq_toNat_trdeg (j ≫ sS)]
  congr 1
  omega

/-- **Completing a frame.** In a free module of rank two over a local ring, a vector `v` with
`r v = 1` for a linear form `r` is completed to a spanning pair `(v, w)` by an element `w` of any
spanning set. -/
private theorem exists_mem_span_pair_eq_top {O M : Type*} [CommRing O] [IsLocalRing O]
    [AddCommGroup M] [Module O M] (b₀ : Module.Basis (Fin 2) O M) (r : M →ₗ[O] O) {v : M}
    (hr : r v = 1) {S : Set M} (hS : Submodule.span O S = ⊤) :
    ∃ w ∈ S, Submodule.span O (Set.range ![v, w]) = ⊤ := by
  classical
  set c₁ := b₀.coord 0
  set c₂ := b₀.coord 1
  let φ : M →ₗ[O] O := c₁ v • c₂ - c₂ v • c₁
  have hφ : ∀ w, φ w = c₁ v * c₂ w - c₂ v * c₁ w := fun w => by
    simp [φ, smul_eq_mul]
  have hv : v = c₁ v • b₀ 0 + c₂ v • b₀ 1 := by
    have := b₀.sum_repr v
    rw [Fin.sum_univ_two] at this
    exact this.symm
  have key : ∀ w, IsUnit (φ w) → Submodule.span O (Set.range ![v, w]) = ⊤ := by
    intro w hw
    have hvS : v ∈ Submodule.span O (Set.range ![v, w]) := Submodule.subset_span ⟨0, rfl⟩
    have hwS : w ∈ Submodule.span O (Set.range ![v, w]) := Submodule.subset_span ⟨1, rfl⟩
    have e0 : φ w • b₀ 0 = c₂ w • v - c₂ v • w := by
      refine b₀.ext_elem fun i => ?_
      obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      · simp [hφ, c₁, c₂]; ring
      · simp [hφ, c₁, c₂]; ring
    have e1 : φ w • b₀ 1 = c₁ v • w - c₁ w • v := by
      refine b₀.ext_elem fun i => ?_
      obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      · simp [hφ, c₁, c₂]; ring
      · simp [hφ, c₁, c₂]; ring
    refine eq_top_iff.mpr ?_
    rw [← b₀.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hb : ∀ x : M, φ w • x ∈ Submodule.span O (Set.range ![v, w]) →
        x ∈ Submodule.span O (Set.range ![v, w]) := fun x hx => by
      have := Submodule.smul_mem _ ((hw.unit⁻¹ : Oˣ) : O) hx
      rwa [smul_smul, hw.val_inv_mul, one_smul] at this
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · have h := Submodule.sub_mem _ (Submodule.smul_mem _ (c₂ w) hvS)
        (Submodule.smul_mem _ (c₂ v) hwS)
      rw [← e0] at h
      exact hb _ h
    · have h := Submodule.sub_mem _ (Submodule.smul_mem _ (c₁ v) hwS)
        (Submodule.smul_mem _ (c₁ w) hvS)
      rw [← e1] at h
      exact hb _ h
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hmem : ∀ w ∈ S, φ w ∈ IsLocalRing.maximalIdeal O := fun w hw =>
    (IsLocalRing.mem_maximalIdeal _).mpr fun hu => hne w hw (key w hu)
  have hall : ∀ x : M, φ x ∈ IsLocalRing.maximalIdeal O := by
    have : Submodule.span O S ≤ Submodule.comap φ (IsLocalRing.maximalIdeal O) :=
      Submodule.span_le.mpr fun w hw => hmem w hw
    rw [hS] at this
    exact fun x => this trivial
  have h0 := hall (b₀ 0)
  have h1 := hall (b₀ 1)
  rw [hφ] at h0 h1
  simp only [c₁, c₂, Module.Basis.coord_apply, Module.Basis.repr_self] at h0 h1
  simp at h0 h1
  have hr' : r v = c₁ v * r (b₀ 0) + c₂ v * r (b₀ 1) := by
    conv_lhs => rw [hv]
    simp [smul_eq_mul]
  have : r v ∈ IsLocalRing.maximalIdeal O := by
    rw [hr']
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_right _ _ h0)
  rw [hr] at this
  exact (IsLocalRing.mem_maximalIdeal _).mp this isUnit_one

/-- **Residues along a floor curve exist.** Along an adjunction step `j : T ⟶ S` onto a prime
divisor `P` of a normal surface, every rational `m`-canonical form with a pole of order at most
`m` along `P` has a Poincaré residue. -/
private theorem exists_isPoincareResidue_of_surface {S T : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S] {s : S ⟶ Spec (.of ℂ)}
    (hS : IsNormalVariety ℂ s) (hdim : topologicalKrullDim S = 2) {B : QDivisor S} {j : T ⟶ S}
    {BT : QDivisor T} (hj : IsAdjunctionStep s B j BT) [IsIntegral T] {m : ℕ}
    (τ : RationalPluriForms s 2 m)
    (hτ : ∀ P : Mori.PrimeDivisor S, j (genericPoint T) = P.genericPoint → τ ≠ 0 →
      -(m : ℤ) ≤ P.ordForm τ) :
    ∃ ρ : RationalPluriForms (j ≫ s) 1 m, IsPoincareResidue s j 1 m τ ρ := by
  classical
  haveI : LocallyOfFiniteType s := hS.1.toLocallyOfFiniteType
  obtain ⟨P, hP, hci⟩ := hj.exists_primeDivisor
  let O := S.presheaf.stalk (j (genericPoint T))
  let := stalkAlgebra s (j (genericPoint T))
  let := functionFieldAlgebra s
  let := functionFieldAlgebra (j ≫ s)
  let : Algebra O T.functionField := (j.stalkMap (genericPoint T)).hom.toAlgebra
  have := isScalarTower_stalk_functionField s (j (genericPoint T))
  obtain ⟨hdvr, hfree, hfin, -, hcoh, hrank⟩ := hj.stalk_facts
  obtain ⟨-, hsurj⟩ := hj.stalkMap_facts
  obtain ⟨ϖ, r, -, hr, hker, -, -⟩ := hj.exists_uniformizer
  have htr : (Algebra.trdeg ℂ S.functionField).toNat = 2 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (by exact_mod_cast hdim)
  -- `ϖ` is a uniformizer
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)).symm.trans hker
  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hmax
  have hϖ0 : algebraMap O S.functionField ϖ ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hϖirr.ne_zero
  have hord : S.ord (algebraMap O S.functionField ϖ) (j (genericPoint T)) = 1 :=
    (Scheme.ord_eq_iff hcoh hϖ0).mpr (Ring.ordFrac_irreducible hϖirr)
  -- `dϖ` generates `Ω_{𝒪/ℂ}`
  haveI := hfree
  haveI := hfin
  have hrk : Module.finrank O Ω[O⁄ℂ] = 2 := hrank.trans htr
  obtain ⟨_, ⟨a, rfl⟩, hspan⟩ := exists_mem_span_pair_eq_top
    (Module.finBasisOfFinrankEq O Ω[O⁄ℂ] hrk) r hr (KaehlerDifferential.span_range_derivation ℂ O)
  -- the frame `dϖ` of `Ω_{k(C)/ℂ}`
  have := essFiniteType_functionField (sX := s)
  have hK1 : Module.finrank S.functionField Ω[S.functionField⁄ℂ] = 2 :=
    (finrank_kaehlerDifferential_eq_trdeg ℂ S.functionField).trans htr
  have : FiniteDimensional S.functionField Ω[S.functionField⁄ℂ] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent ℂ S.functionField).1
  haveI := nontrivial_exteriorPower_of_finrank_eq ℂ S.functionField hK1
  have hσ := MMP.Fourfold.span_singleton_ιMulti_eq_top _ hspan
  have h0 := topFormsMap_ne_zero_of_span_eq_top (k := ℂ) (K := S.functionField) hσ
  set F0 := topFormsMap ℂ O S.functionField 2 (exteriorPower.ιMulti O 2
    ![KaehlerDifferential.D ℂ O ϖ, KaehlerDifferential.D ℂ O a]) with hF0_def
  have hfr1 : Module.finrank S.functionField (⋀[S.functionField]^2 Ω[S.functionField⁄ℂ]) = 1 := by
    rw [exteriorPower.finrank_eq, hK1, Nat.choose_self]
  have hspanK : Submodule.span S.functionField {F0} = ⊤ :=
    (finrank_eq_one_iff_of_nonzero F0 h0).mp hfr1
  let bK := basisOfSpanSingleton hspanK h0
  set c := (ZTensorPower.basis bK (m : ℤ)).repr τ () with hc_def
  have hτeq : τ = c • (PiTensorProduct.tprod S.functionField (fun _ : Fin m => F0) :
      TensorPower S.functionField m (⋀[S.functionField]^2 Ω[S.functionField⁄ℂ])) := by
    have h1 := basis_unit_repr_smul (ZTensorPower.basis bK (m : ℤ)) τ
    have h2 := ZTensorPower.basis_ofNat bK m
    rw [basisOfSpanSingleton_apply] at h2
    rw [← hc_def] at h1
    rw [← h2]
    exact h1.symm
  by_cases hτ0 : τ = 0
  · refine ⟨0, ϖ, 0, ![a], hord, ?_, ?_⟩
    · rw [hτ0, map_zero]
      exact (zero_smul _ _).symm
    · rw [map_zero]
      exact (zero_smul _ _).symm
  have hc0 : c ≠ 0 := fun h => hτ0 (by rw [hτeq, h]; exact zero_smul _ _)
  have hordc : S.ord c P.genericPoint ≥ -(m : ℤ) := by
    have := MMP.CyclicChartDifferent.ordForm_eq_of_frame (sX := s) P hP ![KaehlerDifferential.D ℂ O ϖ, KaehlerDifferential.D ℂ O a]
      hspan h0 c τ hτeq
    rw [← this]
    exact hτ P hP hτ0
  -- the coefficient along the frame `(dϖ/ϖ)^m` is regular
  have hgK : c * algebraMap O S.functionField ϖ ^ m ≠ 0 := mul_ne_zero hc0 (pow_ne_zero _ hϖ0)
  obtain ⟨g, hg⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
    (j (genericPoint T)) hgK fun Γ hΓ => by
      have hΓP : Γ.genericPoint = P.genericPoint := by
        have hsp : Γ.genericPoint ⤳ j (genericPoint T) := by
          rw [specializes_iff_mem_closure, ← PrimeDivisor.support_eq_closure]; exact hΓ
        rw [hP] at hsp
        exact MMP.ProgramBaseChange.eq_of_specializes_of_coheight_eq_one hsp
          Γ.coheight_genericPoint P.coheight_genericPoint
      rw [hΓP, Scheme.ord_mul hc0 (pow_ne_zero _ hϖ0), Scheme.ord_pow hϖ0, ← hP, hord]
      rw [hP]
      omega
  refine ⟨_, ϖ, g, ![a], hord, ?_, rfl⟩
  have hF0' : exteriorPower.ιMulti S.functionField (1 + 1)
      (Fin.cons (KaehlerDifferential.D ℂ S.functionField (algebraMap O S.functionField ϖ))
        fun i : Fin 1 => KaehlerDifferential.D ℂ S.functionField
          (algebraMap O S.functionField (![a] i))) = F0 := by
    rw [hF0_def, topFormsMap_ιMulti]
    congr 1
    funext i
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · simp [KaehlerDifferential.map_D]
    · exact (KaehlerDifferential.map_D ℂ ℂ O S.functionField a).symm
  rw [hτeq, hg, hF0', tprod_const_smul, smul_smul]
  congr 1
  have h1 : algebraMap O S.functionField ϖ * (algebraMap O S.functionField ϖ)⁻¹ = 1 :=
    mul_inv_cancel₀ hϖ0
  rw [mul_assoc, ← mul_pow]
  erw [h1]
  rw [one_pow, mul_one]

/-- Multiplying a form by (the image of) a regular function along `T` multiplies its residue by
the restriction of the function. -/
private theorem IsPoincareResidue.algebraMap_smul {Y T : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsIntegral T] {j : T ⟶ Y} {n m : ℕ}
    {τ : RationalPluriForms sY (n + 1) m} {ρ : RationalPluriForms (j ≫ sY) n m}
    (h : IsPoincareResidue sY j n m τ ρ) (g : Y.presheaf.stalk (j (genericPoint T))) :
    IsPoincareResidue sY j n m (algebraMap _ Y.functionField g • τ)
      ((j.stalkMap (genericPoint T)).hom g • ρ) := by
  obtain ⟨t, g₀, x, ht, hτ, hρ⟩ := h
  refine ⟨t, g * g₀, x, ht, ?_, ?_⟩
  · rw [hτ, map_mul]
    exact (mul_smul _ _ _).symm
  · rw [hρ, map_mul]
    exact (mul_smul _ _ _).symm

/-- **Local generators along a floor curve.** For a projective surface pair `(S, B)` and every
sufficiently divisible `m`, near every point of a floor curve `(T, B_T)` there is a local generator
of `𝒪_S(m(K_S + B))` whose residue is a local generator of `𝒪_T(m(K_T + B_T))`. -/
private theorem exists_generatesOn_isPoincareResidue_floor {S : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)}
    (hS : Mori.IsProjectiveVariety ℂ sS) (hdim : topologicalKrullDim S = 2)
    {B : QDivisor S} (hB : Fourfold.IsPair sS B) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ M : ℕ, m₀ ∣ M + 1 →
      ∀ {T : Scheme.{0}} {j : T ⟶ S} {BT : QDivisor T} (_ : IsAdjunctionStep sS B j BT)
        [IsIntegral T] [IsLocallyNoetherian T] (_ : Mori.PrimeDivisor T) (x : T),
        ∃ U : S.Opens, j x ∈ U ∧ ∃ τ'' : RationalPluriForms sS (1 + 1) ((M + 1 : ℕ) : ℤ),
          GeneratesOn B (M + 1) U τ'' ∧ ∃ ρ'' : RationalPluriForms (j ≫ sS) 1 ((M + 1 : ℕ) : ℤ),
            IsPoincareResidue sS j 1 (M + 1) τ'' ρ'' ∧ GeneratesOn BT (M + 1) (j ⁻¹ᵁ U) ρ'' := by
  classical
  obtain ⟨hX, n₀, K, hK, N, hN0, hNC⟩ := hB.isPair
  refine ⟨N.natAbs, Int.natAbs_pos.mpr hN0, fun M hmd T j BT hj _ _ P x => ?_⟩
  haveI : CompactSpace S := compactSpace_of_isProjectiveMorphism hS.isProjective
  haveI : LocallyOfFiniteType sS := hX.1.toLocallyOfFiniteType
  have hdim' : topologicalKrullDim S = (1 + 1 : ℕ) := by rw [hdim]; rfl
  have hjstep := hj
  obtain ⟨hT, P₁, hP₁1, hrange, hci, -⟩ := hjstep
  haveI : IsClosedImmersion j := hci
  haveI : IsNormal T := hT.2
  haveI : LocallyOfFiniteType (j ≫ sS) := hT.1.toLocallyOfFiniteType
  haveI : QuasiCompact (j ≫ sS) := hT.1.toQuasiCompact
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (j ≫ sS)
  have hdimT : topologicalKrullDim T = 1 := by
    exact_mod_cast topologicalKrullDim_eq_one_of_isAdjunctionStep hdim hj
  -- a rational top form with a simple pole along `P₁` and its residue
  obtain ⟨σ, hσ0, hσP, -, ρσ, hρσ, hρσ0, -⟩ :=
    exists_form_of_residue_order sS hX hdim' j hT P₁ hrange P
  -- `div σ` is a canonical divisor up to a principal one
  obtain rfl : n₀ = 2 := by
    have := hK.1.symm.trans hdim
    exact_mod_cast this
  let := functionFieldAlgebra sS
  have htr := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sS) hdim'
  obtain ⟨bS⟩ := MMP.Fourfold.exists_basis_topForms (sX := sS) hdim'
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX (n := 1 + 1) hK
  set c := (ZTensorPower.basis bS 1).repr σ () / (ZTensorPower.basis bS 1).repr ω () with hc_def
  have hrσ : (ZTensorPower.basis bS 1).repr σ () ≠ 0 := repr_ne_zero_of_ne_zero bS hσ0
  have hrω : (ZTensorPower.basis bS 1).repr ω () ≠ 0 := repr_ne_zero_of_ne_zero bS hω0
  have hc0 : c ≠ 0 := div_ne_zero hrσ hrω
  obtain ⟨φc, hφc⟩ := MMP.Positivity.exists_units_of_ne_zero hc0
  have hdivσ : divisorOfForm σ = K + principalDivisor φc := by
    ext Γ
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul htr bS
    have e1 := hNΓ 1 σ hσ0
    have e2 := hNΓ 1 ω hω0
    rw [hω] at e2
    have hm1 := Scheme.ord_mul (x := Γ.genericPoint) hrσ (inv_ne_zero hrω)
    have hm2 := scheme_ord_inv (z := Γ.genericPoint) hrω
    have hcord : S.ord c Γ.genericPoint = S.ord ((ZTensorPower.basis bS 1).repr σ ())
        Γ.genericPoint - S.ord ((ZTensorPower.basis bS 1).repr ω ()) Γ.genericPoint := by
      rw [hc_def, div_eq_mul_inv]
      erw [hm1, hm2]
      ring
    rw [coeff_divisorOfForm, DivisorWithCoeffs.coeff_add, coeff_principalDivisor, hφc, e1, hcord]
    omega
  -- a Cartier divisor `DM = m (div σ + B)`
  obtain ⟨D₀, hD₀, hD₀c⟩ := hNC
  obtain ⟨z, hz⟩ : N ∣ ((M + 1 : ℕ) : ℤ) := Int.natAbs_dvd.mp (by exact_mod_cast hmd)
  set DM : Divisor S := z • D₀ + ((M + 1 : ℕ) : ℤ) • principalDivisor φc with hDM_def
  have hDMc : DM.IsCartier :=
    (hD₀c.zsmul z).add ((Divisor.isCartier_principalDivisor φc).zsmul _)
  have hDMq : Divisor.toQDivisor DM =
      ((M + 1 : ℕ) : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + B) := by
    rw [hDM_def, map_add, map_zsmul, map_zsmul, hD₀, hdivσ, map_add, smul_smul, mul_comm, ← hz]
    simp only [smul_add]
    abel
  have hD : (Divisor.toQDivisor (divisorOfForm σ) + B).IsQCartier :=
    ⟨((M + 1 : ℕ) : ℤ), by positivity, DM, hDMq, hDMc⟩
  obtain ⟨hgen, hpb⟩ := hj.isPullback_divisorOfForm_add_of_isPoincareResidue hdim' P₁ hrange σ
    hσ0 hσP ρσ hρσ hD
  have hB' : Divisor.toQDivisor (divisorOfForm σ) + Finsupp.single P₁ 1 +
      (B - Finsupp.single P₁ 1) = Divisor.toQDivisor (divisorOfForm σ) + B := by abel
  obtain ⟨hgen', hpb'⟩ : ∃ hg, (Divisor.toQDivisor (divisorOfForm σ) + Finsupp.single P₁ 1 +
      (B - Finsupp.single P₁ 1)).IsPullback j hg (Divisor.toQDivisor (divisorOfForm ρσ) + BT) := by
    rw [hB']; exact ⟨hgen, hpb⟩
  obtain ⟨U, hxU, τ'', hτ'', ρ'', hρ'', hρ''gen⟩ :=
    MMP.CyclicChartDifferent.Aux.exists_generatesOn_isPoincareResidue sS hdim' j hT
      (by rw [hdimT]; rfl) P₁ hrange (B - Finsupp.single P₁ 1) σ hσ0 ρσ hρσ hρσ0 BT hgen' hpb'
      M DM (by rw [hB']; exact hDMq) hDMc x
  have hBB : Finsupp.single P₁ 1 + (B - Finsupp.single P₁ 1) = B := by abel
  rw [hBB] at hτ''
  exact ⟨U, hxU, τ'', hτ'', ρ'', hρ'', hρ''gen⟩

/-- **The adjunction bound at the points of a floor curve.** For a projective `ℚ`-factorial dlt
surface pair `(S, B)` and every sufficiently divisible `m`, the residue along a floor curve
`(T, B_T)` of a section of `𝒪_S(m(K_S + B))` has a pole of order at most `m` at every point of
the floor of `B_T`. -/
private theorem exists_le_ordForm_of_isPoincareResidue {S : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)}
    (hS : Mori.IsProjectiveVariety ℂ sS) (hdim : topologicalKrullDim S = 2)
    (hQ : IsQFactorial sS) {B : QDivisor S} (hB : Fourfold.IsPair sS B)
    (hdlt : MMP.Intersection.IsDltPair sS B) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, 0 < m → m₀ ∣ m → ∀ τ ∈ logPluricanonicalSections sS 2 m B,
      ∀ (s : S ⟶ Spec (.of ℂ)), s = sS →
      ∀ {T : Scheme.{0}} {j : T ⟶ S} {BT : QDivisor T} (_ : IsAdjunctionStep s B j BT)
        [IsIntegral T] [IsLocallyNoetherian T] (ρ : RationalPluriForms (j ≫ s) 1 m)
        (e : RationalPluriForms sS 2 m = RationalPluriForms s 2 m),
        IsPoincareResidue s j 1 m (cast e τ) ρ →
        ∀ {Q : Scheme.{0}} [IsIntegral Q] {j' : Q ⟶ T} {BQ : QDivisor Q},
          IsAdjunctionStep (j ≫ s) BT j' BQ →
          ∀ P : Mori.PrimeDivisor T, j' (genericPoint Q) = P.genericPoint → ρ ≠ 0 →
            -(m : ℤ) ≤ P.ordForm ρ := by
  classical
  have hX : IsNormalVariety ℂ sS := hB.isPair.1
  obtain ⟨m₀, hm₀, hgen⟩ := exists_generatesOn_isPoincareResidue_floor hS hdim hB
  refine ⟨m₀, hm₀, fun m hm0 hmd τ hτ s hs T j BT hj _ _ ρ e hρ
    Q _ j' BQ hj' P hP hρ0 => ?_⟩
  subst s
  rw [cast_eq] at hρ
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
  haveI : CompactSpace S := compactSpace_of_isProjectiveMorphism hS.isProjective
  haveI : LocallyOfFiniteType sS := hX.1.toLocallyOfFiniteType
  have hdim' : topologicalKrullDim S = (1 + 1 : ℕ) := by rw [hdim]; rfl
  obtain ⟨U, hxU, τ'', hτ'', ρ'', hρ'', hρ''gen⟩ := hgen M hmd hj P P.genericPoint
  have hjstep := hj
  obtain ⟨hT, P₁, hP₁1, hrange, hci, -⟩ := hjstep
  haveI : IsClosedImmersion j := hci
  haveI : IsNormal T := hT.2
  haveI : LocallyOfFiniteType (j ≫ sS) := hT.1.toLocallyOfFiniteType
  have hdimT : topologicalKrullDim T = 1 := by
    exact_mod_cast topologicalKrullDim_eq_one_of_isAdjunctionStep hdim hj
  let := functionFieldAlgebra sS
  obtain ⟨bS⟩ := MMP.Fourfold.exists_basis_topForms (sX := sS) hdim'
  -- `τ ≠ 0`
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    have h0 := IsPoincareResidue.smul hj hρ 0
    rw [zero_smul, zero_smul] at h0
    exact hρ0 (IsPoincareResidue.unique hj hρ h0)
  -- `τ = h τ''` with `h` regular at `j(η_P)`
  have hτ''0 := hτ''.1
  set bm := ZTensorPower.basis bS ((M + 1 : ℕ) : ℤ)
  have hr1 : bm.repr τ () ≠ 0 := repr_ne_zero_of_ne_zero bS hτ0
  have hr2 : bm.repr τ'' () ≠ 0 := repr_ne_zero_of_ne_zero bS hτ''0
  set h := bm.repr τ () / bm.repr τ'' () with hh_def
  have hh0 : h ≠ 0 := div_ne_zero hr1 hr2
  have hτeq : τ = h • τ'' := by
    refine bm.ext_elem fun i => ?_
    obtain rfl : i = () := rfl
    have e := congrArg (fun f => f ()) (bm.repr.map_smul h τ'')
    simp only [Finsupp.smul_apply, smul_eq_mul] at e
    have e' : bm.repr τ () = h * bm.repr τ'' () := by rw [hh_def, div_mul_cancel₀ _ hr2]
    exact e'.trans ((congrArg (fun f => f ()) (congrArg bm.repr rfl)).trans e).symm
  obtain ⟨u, hu⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
    (j P.genericPoint) hh0 fun Γ hΓ => by
      have e1 := Γ.ordForm_smul_of_topologicalKrullDim_eq hdim' hh0 hτ''0
      rw [← hτeq] at e1
      have e2 := hτ''.2 Γ ⟨_, hΓ, hxU⟩
      have e3 := hτ.2 Γ ⟨Γ.genericPoint, by
        rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl, trivial⟩ hτ0
      rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at e3
      have e4 := Int.floor_le ((((M + 1 : ℕ) : ℤ) : ℚ) * B.coeff Γ)
      have : (0 : ℚ) ≤ S.ord h Γ.genericPoint := by
        have e3' : (0 : ℚ) ≤ (Γ.ordForm τ : ℚ) + ⌊((((M + 1 : ℕ) : ℤ) : ℚ) * B.coeff Γ)⌋ := by
          exact_mod_cast e3
        rw [e1] at e3'
        push_cast at e2 e3' e4 ⊢
        linarith
      exact_mod_cast this
  have hsp : genericPoint T ⤳ P.genericPoint := (genericPoint_spec T).specializes trivial
  set u' := (S.presheaf.stalkSpecializes (hsp.map j.continuous)).hom u with hu'_def
  have hu' : algebraMap _ S.functionField u' = h := by
    rw [hu'_def, MMP.Mori.algebraMap_stalkSpecializes, hu]
  have hres := IsPoincareResidue.algebraMap_smul hρ'' u'
  rw [hu', ← hτeq] at hres
  have hρeq := IsPoincareResidue.unique hj hρ hres
  -- the restriction of `h` to `T` is regular at `η_P`
  set w := (j.stalkMap P.genericPoint).hom u with hw_def
  have hc' : (j.stalkMap (genericPoint T)).hom u' =
      (T.presheaf.stalkSpecializes hsp).hom w := by
    rw [hu'_def, hw_def, Scheme.Hom.stalkSpecializes_stalkMap_apply]
  have hcne : (j.stalkMap (genericPoint T)).hom u' ≠ 0 := fun h0 =>
    hρ0 (by rw [hρeq, h0]; exact zero_smul _ _)
  have hw0 : w ≠ 0 := fun h0 => hcne (by rw [hc', h0, map_zero])
  have hcord : 0 ≤ T.ord ((j.stalkMap (genericPoint T)).hom u') P.genericPoint := by
    rw [hc']
    change 0 ≤ T.ord (algebraMap _ T.functionField w) P.genericPoint
    rw [scheme_ord_algebraMap P.coheight_genericPoint hw0]
    positivity
  -- the coefficient of `B_T` along `P` is at most one
  have hstr : IsDltStratum sS B (P₁.support : Set S) := by
    refine ⟨hdlt, {P₁}, Finset.singleton_nonempty _, by simpa using hP₁1,
      ⟨P₁.genericPoint, by
        simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left]
        rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩, ?_⟩
    refine ⟨⟨?_, by simp⟩, fun T' hT' _ => by simpa using hT'.2⟩
    rw [PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  have hj0 : IsAdjunctionStep (𝟙 S ≫ sS) B j BT := by rw [Category.id_comp]; exact hj
  have hdltT := (IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair hstr).1.2
    (StratumAdjunctionData.step (.refl hB.isPair) j BT hj0)
    (by rw [Category.comp_id]; exact hrange)
  have hBT1 : BT.coeff P ≤ 1 := hdltT.2.1 P
  -- conclusion
  have e1 := P.ordForm_smul_of_topologicalKrullDim_eq (by rw [hdimT]; rfl) hcne hρ''gen.1
  rw [← hρeq] at e1
  have e2 := hρ''gen.2 P ⟨P.genericPoint, by
    rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl, hxU⟩
  have : (-(((M + 1 : ℕ) : ℤ)) : ℚ) ≤ (P.ordForm ρ : ℚ) := by
    rw [e1]
    push_cast at e2 hcord ⊢
    have hcord' : (0 : ℚ) ≤ (T.ord ((j.stalkMap (genericPoint T)).hom u') P.genericPoint : ℚ) := by
      exact_mod_cast hcord
    nlinarith [(Nat.cast_nonneg M : (0 : ℚ) ≤ M)]
  exact_mod_cast this

/-- **Iterated residues of log pluricanonical sections exist** along every flag of strata of a
projective `ℚ`-factorial dlt surface pair, in every sufficiently divisible degree. -/
private theorem exists_isIteratedResidue {S : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)}
    (hS : Mori.IsProjectiveVariety ℂ sS) (hdim : topologicalKrullDim S = 2)
    (hQ : IsQFactorial sS) {B : QDivisor S} (hB : Fourfold.IsPair sS B)
    (hdlt : MMP.Intersection.IsDltPair sS B) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, 0 < m → m₀ ∣ m → ∀ {T : Scheme.{0}} {ι : T ⟶ S}
      {BT : QDivisor T} (F : StratumAdjunctionData sS B ι BT) (e : ℕ),
      topologicalKrullDim T = e → ∀ τ ∈ logPluricanonicalSections sS 2 m B,
        haveI := F.isIntegral_stratum
        ∃ ρ : RationalPluriForms (ι ≫ sS) e m, IsIteratedResidue sS B τ F e ρ := by
  obtain ⟨m₀, hm₀, hbound⟩ := exists_le_ordForm_of_isPoincareResidue hS hdim hQ hB hdlt
  haveI : CompactSpace S := compactSpace_of_isProjectiveMorphism hS.isProjective
  have hX : IsNormalVariety ℂ sS := hB.isPair.1
  have hX' : IsNormalVariety ℂ (𝟙 S ≫ sS) := by rw [Category.id_comp]; exact hX
  refine ⟨m₀, hm₀, fun m hm0 hmd T ι BT F e he τ hτ => ?_⟩
  have hlen := F.dim_add_length (n := 2) (by exact_mod_cast hdim) he
  have e0 : RationalPluriForms sS 2 m = RationalPluriForms (𝟙 S ≫ sS) 2 m := by
    rw [Category.id_comp]
  cases F with
  | refl h =>
    simp only [StratumAdjunctionData.length, add_zero] at hlen
    subst hlen
    exact ⟨_, IsIteratedResidue.refl h⟩
  | step F₁ j BT hj =>
    cases F₁ with
    | refl h =>
      simp only [StratumAdjunctionData.length] at hlen
      obtain rfl : e = 1 := by omega
      haveI : IsIntegral T := hj.1.1.toIsIntegral
      obtain ⟨ρ', hρ'⟩ := exists_isPoincareResidue_of_surface hX' (by exact_mod_cast hdim) hj
        (cast e0 τ) fun P _ h0 => by
          rw [ordForm_cast (Category.id_comp sS).symm]
          exact neg_le_ordForm_of_mem_logPluricanonicalSections hdlt.2.1 hτ P
              fun h => h0 (by subst h; rfl)
      exact ⟨_, IsIteratedResidue.step (IsIteratedResidue.refl h) hρ'⟩
    | step F₂ j₁ BT₁ hj₁ =>
      cases F₂ with
      | refl h =>
        simp only [StratumAdjunctionData.length] at hlen
        obtain rfl : e = 0 := by omega
        haveI : IsIntegral T := hj.1.1.toIsIntegral
        have hj₁' := hj₁
        haveI : IsIntegral _ := hj₁.1.1.toIsIntegral
        haveI := hj₁.1.1.toLocallyOfFiniteType
        haveI := LocallyOfFiniteType.isLocallyNoetherian (j₁ ≫ 𝟙 S ≫ sS)
        haveI := hj₁.1.2
        obtain ⟨ρ₁, hρ₁⟩ := exists_isPoincareResidue_of_surface hX' (by exact_mod_cast hdim) hj₁
          (cast e0 τ) fun P _ h0 => by
            rw [ordForm_cast (Category.id_comp sS).symm]
            exact neg_le_ordForm_of_mem_logPluricanonicalSections hdlt.2.1 hτ P
              fun h => h0 (by subst h; rfl)
        have hF₁ := IsIteratedResidue.step (hj := hj₁) (IsIteratedResidue.refl h) hρ₁
        have hC : IsNormalVariety ℂ ((j₁ ≫ 𝟙 S) ≫ sS) := by
          rw [Category.assoc]; exact hj₁.1
        haveI : LocallyOfFiniteType ((j₁ ≫ 𝟙 S) ≫ sS) := hC.1.toLocallyOfFiniteType
        have hdimC := topologicalKrullDim_eq_add_one_of_isAdjunctionStep hj he
        have hj' := (Category.assoc j₁ (𝟙 S) sS) ▸ hj
        obtain ⟨ρ₂, hρ₂⟩ := exists_isPoincareResidue_of_curve hC (by exact_mod_cast hdimC) hj
          (cast (by rw [Category.assoc]) ρ₁) fun P hP h0 => by
            rw [ordForm_cast (Category.assoc j₁ (𝟙 S) sS).symm]
            exact hbound m hm0 hmd τ hτ (𝟙 S ≫ sS) (Category.id_comp sS) hj₁ ρ₁ e0 hρ₁ hj' P hP
              fun h => h0 (by subst h; rfl)
        exact ⟨_, IsIteratedResidue.step hF₁ hρ₂⟩
      | step F₃ _ _ _ =>
        simp only [StratumAdjunctionData.length] at hlen
        omega

/-- **Stratum adjoints are Cartier** in every sufficiently divisible degree, for a projective
`ℚ`-factorial dlt surface pair. -/
private theorem exists_isCartierDivisor_stratum {S : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)}
    (hS : Mori.IsProjectiveVariety ℂ sS) (hdim : topologicalKrullDim S = 2)
    (hQ : IsQFactorial sS) {B : QDivisor S} (hB : Fourfold.IsPair sS B)
    (hdlt : MMP.Intersection.IsDltPair sS B) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, 0 < m → m₀ ∣ m → ∀ {T : Scheme.{0}} {ι : T ⟶ S}
      {BT : QDivisor T} (F : StratumAdjunctionData sS B ι BT),
      haveI := F.isIntegral_stratum
      haveI := F.isNormal_stratum
      haveI := F.isLocallyNoetherian_stratum
      ∃ (d : ℕ) (K : Divisor T), K.IsCanonicalDivisor (ι ≫ sS) d ∧
        ((m : ℤ) • (Divisor.toQDivisor K + BT)).IsCartierDivisor := by
  classical
  obtain ⟨hX, n₀, K, hK, N, hN0, hNC⟩ := hB.isPair
  obtain ⟨m₁, hm₁, hgen⟩ := exists_generatesOn_isPoincareResidue_floor hS hdim hB
  haveI : CompactSpace S := compactSpace_of_isProjectiveMorphism hS.isProjective
  haveI : LocallyOfFiniteType sS := hX.1.toLocallyOfFiniteType
  obtain rfl : n₀ = 2 := by
    have := hK.1.symm.trans hdim
    exact_mod_cast this
  obtain ⟨D₀, hD₀, hD₀c⟩ := hNC
  refine ⟨N.natAbs * m₁, Nat.mul_pos (Int.natAbs_pos.mpr hN0) hm₁, fun m hm0 hmd T ι BT F => ?_⟩
  obtain ⟨z, hz⟩ : N ∣ (m : ℤ) :=
    Int.natAbs_dvd.mp (by exact_mod_cast (dvd_mul_right _ _).trans hmd)
  have hm₁d : m₁ ∣ m := (dvd_mul_left _ _).trans hmd
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
  cases F with
  | refl h =>
    refine ⟨2, K, by rw [Category.id_comp]; exact hK, z • D₀, ?_, hD₀c.zsmul z⟩
    rw [map_zsmul, hD₀, smul_smul, mul_comm, ← hz]
  | step F₁ j BT hj =>
    cases F₁ with
    | refl h =>
      haveI : IsIntegral T := hj.1.1.toIsIntegral
      have hj' : IsAdjunctionStep sS B j BT := by rw [Category.id_comp] at hj; exact hj
      have hT' : IsNormalVariety ℂ (j ≫ sS) := hj'.1
      haveI : IsNormal T := hT'.2
      haveI : LocallyOfFiniteType (j ≫ sS) := hT'.1.toLocallyOfFiniteType
      haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (j ≫ sS)
      haveI : QuasiCompact (j ≫ sS) := hT'.1.toQuasiCompact
      haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (j ≫ sS)
      have hdimT : topologicalKrullDim T = (1 : ℕ) :=
        topologicalKrullDim_eq_one_of_isAdjunctionStep hdim hj'
      -- a prime divisor of `T`
      obtain ⟨x₀, -, hx₀⟩ := (isClosed_univ (X := T)).exists_closed_singleton Set.univ_nonempty
      have hco : Order.coheight x₀ = 1 := by
        have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (j ≫ sS) x₀
        rw [hx₀.closure_eq, hdimT] at h1
        have hd0 : topologicalKrullDim ({x₀} : Set T) ≤ 0 :=
          topologicalKrullDim_zero_of_discreteTopology _
        generalize topologicalKrullDim ({x₀} : Set T) = d at h1 hd0
        generalize Order.coheight x₀ = c at h1 ⊢
        induction d using WithBot.recBotCoe with
        | bot => simp at h1
        | coe d =>
          have : d = 0 := le_antisymm (by exact_mod_cast hd0) (by simp)
          subst this
          rw [WithBot.coe_zero, zero_add] at h1
          exact_mod_cast h1
      let Q₀ := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x₀ hco
      -- a canonical divisor of `T` and the divisor of a form
      obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor (j ≫ sS) hT' hdimT
      let := functionFieldAlgebra (j ≫ sS)
      have htrT := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := j ≫ sS) hdimT
      obtain ⟨bT⟩ := MMP.Fourfold.exists_basis_topForms (sX := j ≫ sS) hdimT
      obtain ⟨ωT, hωT0, hωT⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hT' hKT
      have hd₀ : (ZTensorPower.basis bT 1).repr ωT () ≠ 0 := repr_ne_zero_of_ne_zero bT hωT0
      set d₀ := (ZTensorPower.basis bT 1).repr ωT () with hd₀_def
      -- local equations of `m(K_T + B_T)`
      have hloc : ∀ x : T, ∃ U : T.Opens, x ∈ U ∧ ∃ c : T.functionField, c ≠ 0 ∧
          ∀ P : Mori.PrimeDivisor T, (P.support ∩ U).Nonempty →
            ((M + 1 : ℕ) : ℚ) * (KT.coeff P + BT.coeff P) = T.ord c P.genericPoint := by
        intro x
        obtain ⟨U, hxU, -, -, ρ'', -, hρ''⟩ := hgen M hm₁d hj' Q₀ x
        have hr0 : (ZTensorPower.basis bT ((M + 1 : ℕ) : ℤ)).repr ρ'' () ≠ 0 :=
          repr_ne_zero_of_ne_zero bT hρ''.1
        refine ⟨j ⁻¹ᵁ U, hxU, d₀ ^ (M + 1) *
          ((ZTensorPower.basis bT ((M + 1 : ℕ) : ℤ)).repr ρ'' ())⁻¹,
          mul_ne_zero (pow_ne_zero _ hd₀) (inv_ne_zero hr0), fun P hP => ?_⟩
        obtain ⟨NP, hNP⟩ := P.exists_ordForm_eq_ord_add_mul htrT bT
        have e1 := hNP _ ρ'' hρ''.1
        have e2 := hNP 1 ωT hωT0
        rw [hωT, ← hd₀_def] at e2
        have e3 := hρ''.2 P hP
        have hm1 := Scheme.ord_mul (x := P.genericPoint) (pow_ne_zero (M + 1) hd₀)
          (inv_ne_zero hr0)
        have hm2 := scheme_ord_inv (z := P.genericPoint) hr0
        have hm3 := Scheme.ord_pow (x := P.genericPoint) hd₀ (M + 1)
        rw [hm1, hm2, hm3]
        rw [e1] at e3
        have e2' : (KT.coeff P : ℚ) = (T.ord d₀ P.genericPoint : ℚ) + NP := by
          exact_mod_cast (by rw [e2]; ring : (KT.coeff P : ℤ) = T.ord d₀ P.genericPoint + NP)
        push_cast at e3 ⊢
        rw [e2']
        linear_combination e3
      choose U hxU c hc0 hc using hloc
      -- integrality of `m B_T`
      have hBTint : ∀ P : Mori.PrimeDivisor T, ∃ w : ℤ, (w : ℚ) = ((M + 1 : ℕ) : ℚ) * BT.coeff P :=
        fun P => ⟨T.ord (c P.genericPoint) P.genericPoint - ((M + 1 : ℕ) : ℤ) * KT.coeff P, by
          have := hc P.genericPoint P ⟨P.genericPoint, by
            rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl, hxU _⟩
          push_cast at this ⊢
          linarith⟩
      set BTm : Divisor T := DivisorWithCoeffs.roundDown (((M + 1 : ℕ) : ℤ) • BT) with hBTm_def
      have hBTm : ∀ P, (BTm.coeff P : ℚ) = ((M + 1 : ℕ) : ℚ) * BT.coeff P := fun P => by
        obtain ⟨w, hw⟩ := hBTint P
        rw [hBTm_def, DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul,
          zsmul_eq_mul]
        push_cast
        push_cast at hw
        rw [← hw, Int.floor_intCast]
      set D : Divisor T := ((M + 1 : ℕ) : ℤ) • KT + BTm with hD_def
      have hDco : ∀ P, (D.coeff P : ℚ) = ((M + 1 : ℕ) : ℚ) * (KT.coeff P + BT.coeff P) :=
        fun P => by
          rw [hD_def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
          push_cast
          rw [hBTm]
          push_cast
          ring
      have hDc : D.IsCartier := by
        intro x
        obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (hc0 x)
        refine ⟨U x, hxU x, φ, fun P hP => ?_⟩
        rw [hφ]
        have := hc x P hP
        rw [← hDco] at this
        exact_mod_cast this
      refine ⟨1, KT, by simpa only [Category.comp_id] using hKT, D, ?_, hDc⟩
      ext P
      rw [Divisor.coeff_toQDivisor, hDco]
      simp [zsmul_eq_mul]
      ring
    | step F₂ j₁ BT₁ hj₁ =>
      cases F₂ with
      | refl h =>
        haveI : IsIntegral T := hj.1.1.toIsIntegral
        have ht : (j ≫ j₁ ≫ 𝟙 S) ≫ sS = j ≫ (j₁ ≫ 𝟙 S) ≫ sS := by simp only [Category.assoc]
        have hT : IsNormalVariety ℂ ((j ≫ j₁ ≫ 𝟙 S) ≫ sS) := ht ▸ hj.1
        haveI : IsNormal T := hT.2
        haveI : LocallyOfFiniteType ((j ≫ j₁ ≫ 𝟙 S) ≫ sS) := hT.1.toLocallyOfFiniteType
        haveI : IsLocallyNoetherian T :=
          LocallyOfFiniteType.isLocallyNoetherian ((j ≫ j₁ ≫ 𝟙 S) ≫ sS)
        haveI : QuasiCompact ((j ≫ j₁ ≫ 𝟙 S) ≫ sS) := hT.1.toQuasiCompact
        haveI : CompactSpace T :=
          QuasiCompact.compactSpace_of_compactSpace ((j ≫ j₁ ≫ 𝟙 S) ≫ sS)
        have hlen := (StratumAdjunctionData.step (.step (.refl h) j₁ _ hj₁) j _ hj).dim_add_length
          (n := 2) (by exact_mod_cast hdim)
          (topologicalKrullDim_eq_toNat_trdeg ((j ≫ j₁ ≫ 𝟙 S) ≫ sS))
        simp only [StratumAdjunctionData.length] at hlen
        have hdimT : topologicalKrullDim T = (0 : ℕ) := by
          rw [topologicalKrullDim_eq_toNat_trdeg ((j ≫ j₁ ≫ 𝟙 S) ≫ sS)]
          congr 1
          omega
        have hno : ∀ Γ : Mori.PrimeDivisor T, False := fun Γ => by
          have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight
            ((j ≫ j₁ ≫ 𝟙 S) ≫ sS) Γ.genericPoint
          rw [Γ.coheight_genericPoint, hdimT] at h1
          generalize topologicalKrullDim (closure {Γ.genericPoint} : Set T) = d at h1
          induction d using WithBot.recBotCoe with
          | bot => simp at h1
          | coe d =>
            have : (d + 1 : ℕ∞) = 0 := by exact_mod_cast h1
            simp at this
        obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor ((j ≫ j₁ ≫ 𝟙 S) ≫ sS) hT hdimT
        have h0 : ((M + 1 : ℕ) : ℤ) • (Divisor.toQDivisor KT + BT) = 0 := by
          ext Γ
          exact (hno Γ).elim
        refine ⟨0, KT, hKT, 0, by rw [h0, map_zero], fun x => ⟨⊤, trivial, 1, fun E _ =>
          (hno E).elim⟩⟩
      | step F₃ j₂ BT₂ hj₂ =>
        have hv := (StratumAdjunctionData.step (.step (.step F₃ j₂ _ hj₂) j₁ _ hj₁) j _
          hj).isNormalVariety
        haveI : IsIntegral T := hv.1.toIsIntegral
        have hlen := (StratumAdjunctionData.step (.step (.step F₃ j₂ _ hj₂) j₁ _ hj₁) j _
          hj).dim_add_length (n := 2) (by exact_mod_cast hdim)
          (@topologicalKrullDim_eq_toNat_trdeg ℂ _ T _ _ hv.1.toLocallyOfFiniteType)
        simp only [StratumAdjunctionData.length] at hlen
        omega

/-- **Residue restriction maps exist** in every sufficiently divisible even degree, for a finite
collection of projective `ℚ`-factorial dlt surface pairs: the iterated residue along a flag
exists, is unique and is linear. -/
private theorem exists_residueRestriction {I : Type*} [Finite I] {S : I → Scheme.{0}}
    [∀ i, IsIntegral (S i)] [∀ i, IsLocallyNoetherian (S i)] [∀ i, IsNormal (S i)]
    {sS : ∀ i, S i ⟶ Spec (.of ℂ)} (hS : ∀ i, Mori.IsProjectiveVariety ℂ (sS i))
    (hdim : ∀ i, topologicalKrullDim (S i) = 2) (hQ : ∀ i, IsQFactorial (sS i))
    {B : ∀ i, QDivisor (S i)} (hB : ∀ i, Fourfold.IsPair (sS i) (B i))
    (hdlt : ∀ i, MMP.Intersection.IsDltPair (sS i) (B i)) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, 0 < m → m₀ ∣ m → Even m →
      Nonempty (ResidueRestriction sS B 2 m) := by
  classical
  haveI := Fintype.ofFinite I
  choose m₁ hm₁ hcart using fun i => exists_isCartierDivisor_stratum (hS i) (hdim i) (hQ i) (hB i)
    (hdlt i)
  choose m₂ hm₂ hex using fun i => exists_isIteratedResidue (hS i) (hdim i) (hQ i) (hB i)
    (hdlt i)
  refine ⟨∏ i, m₁ i * m₂ i, Finset.prod_pos fun i _ => Nat.mul_pos (hm₁ i) (hm₂ i),
    fun m hmpos hm hev => ?_⟩
  have hdvd₁ : ∀ i, m₁ i ∣ m := fun i =>
    (dvd_mul_right _ _).trans ((Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans hm)
  have hdvd₂ : ∀ i, m₂ i ∣ m := fun i =>
    (dvd_mul_left _ _).trans ((Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans hm)
  refine ⟨{ setting := ⟨inferInstance, hS, hB, hdlt, hdim, hev, hmpos,
      fun i _ _ _ F => hcart i m hmpos (hdvd₁ i) F⟩
            toFun := fun i T ι BT F e =>
              haveI := F.isIntegral_stratum
              if he : topologicalKrullDim T = e then
                { toFun := fun τ => (hex i m hmpos (hdvd₂ i) F e he τ τ.2).choose
                  map_add' := fun τ₁ τ₂ => IsIteratedResidue.unique
                    (hex i m hmpos (hdvd₂ i) F e he (τ₁ + τ₂) (τ₁ + τ₂).2).choose_spec
                    ((isIteratedResidue_add_smul F e he).1 _ _ _ _
                      (hex i m hmpos (hdvd₂ i) F e he τ₁ τ₁.2).choose_spec
                      (hex i m hmpos (hdvd₂ i) F e he τ₂ τ₂.2).choose_spec)
                  map_smul' := fun c τ => IsIteratedResidue.unique
                    (hex i m hmpos (hdvd₂ i) F e he (c • τ) (c • τ).2).choose_spec
                    ((isIteratedResidue_add_smul F e he).2 c _ _
                      (hex i m hmpos (hdvd₂ i) F e he τ τ.2).choose_spec) }
              else 0
            isIteratedResidue := fun i T ι BT F e τ he => by
              haveI := F.isIntegral_stratum
              simp only [dif_pos he]
              exact (hex i m hmpos (hdvd₂ i) F e he τ τ.2).choose_spec }⟩

end ResidueRestrictionExists

/-! ### Big adjoints -/

/-- `Spec ℂ` is a projective variety over itself. -/
private theorem isProjectiveVariety_id_spec :
    Mori.IsProjectiveVariety ℂ (𝟙 (Spec (.of ℂ))) := by
  haveI : IsIntegral (Spec (.of ℂ)) := inferInstance
  refine (Mori.isProjectiveVariety_iff ℂ _).2 ⟨(Mori.isVariety_iff ℂ _).2
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    MMP.isProjectiveMorphism_of_isClosedImmersion _⟩

/-- A dlt surface pair is lc in the sense of Kollár–Mori. -/
private theorem isLcPair_of_isDltPair {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    (hdlt : MMP.Intersection.IsDltPair sX B) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2) :
    Mori.IsLcPair sX 2 K B :=
  ((MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hK B).mp hdlt).isLcPair

/-- **Semiample divisors are nef.** A `ℚ`-divisor `D` on a normal variety `X` over `ℂ` with a
relatively free Cartier multiple `L = qD` has non-negative degree on every proper curve `C`:
some member `L + div ψ ≥ 0` of `|L|` misses a point of `C`. -/
private theorem isRelativelyNef_of_isRelativelyFreeDivisor {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [QuasiCompact sX] {D : QDivisor X} {q : ℕ} (hq : 0 < q) {L : Divisor X}
    (hLq : Divisor.toQDivisor L = (q : ℤ) • D) (hLc : L.IsCartier)
    (hfree : IsRelativelyFreeDivisor sX L) : D.IsRelativelyNef sX sX := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hDq : D.IsQCartier := ⟨q, by exact_mod_cast hq.ne', L, hLq, hLc⟩
  refine ⟨hDq, fun Cv _ => ?_⟩
  obtain ⟨U', hxU', ψ, h1, h2⟩ :=
    exists_coeff_add_ord_eq_zero_of_isRelativelyFree sX hLc hfree Cv.point
  haveI : Subsingleton (Spec (.of ℂ)) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  have hall : ∀ y : X, sX y ∈ U' := fun y => by
    rw [Subsingleton.elim (sX y) (sX Cv.point)]; exact hxU'
  set B' := L + Mori.principalDivisor ψ with hB'
  have hB'c : B'.IsCartier := hLc.add (Mori.Divisor.isCartier_principalDivisor ψ)
  have hB'0 : 0 ≤ B' := by
    intro P
    have hη : P.genericPoint ∈ P.support := by
      rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    have := h1 P ⟨P.genericPoint, hη, hall _⟩
    show (0 : ℤ) ≤ B'.coeff P
    rw [hB', DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
    exact this
  have hnot : Cv.point ∉ B'.supp := fun hm => by
    obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hm
    exact hP (by rw [hB', DivisorWithCoeffs.coeff_add, coeff_principalDivisor]; exact h2 P hxP)
  obtain ⟨c₀, hc₀⟩ := MMP.Threefold.Mori.exists_ι_eq_point Cv.point
  have hnn := (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sX Cv.ι Cv.dim_le B' hB'c hB'0
    ⟨c₀, hc₀ ▸ hnot⟩).1
  have hlin : B'.LinearlyEquivalent L := ⟨ψ, by rw [hB', add_sub_cancel_left]⟩
  have hdeg : B'.degreeOn ℂ sX Cv.ι Cv.dim_le hB'c = L.degreeOn ℂ sX Cv.ι Cv.dim_le hLc := by
    have := hB'c.isInvertibleModule_divisorialSheaf
    have := hLc.isInvertibleModule_divisorialSheaf
    exact degreeOn_eq_of_iso ℂ sX Cv.ι Cv.dim_le hlin.divisorialSheafIso
  have hI := QDivisor.intersectionNumber_eq_of_smul ℂ sX Cv.ι Cv.dim_le D hDq hq L hLc hLq
  have h0 : 0 ≤ D.intersectionNumber ℂ sX Cv.ι Cv.dim_le hDq := by
    rw [hI]
    exact div_nonneg (by rw [← hdeg]; exact_mod_cast hnn) (by positivity)
  rw [QDivisor.intersectionNumber] at h0
  have hm : (0 : ℚ) < D.cartierIndex hDq := by exact_mod_cast QDivisor.cartierIndex_pos hDq
  have hd := mul_nonneg h0 hm.le
  rw [div_mul_cancel₀ _ hm.ne'] at hd
  rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single]
  simp only [Finsupp.sum_single_index, Rat.cast_zero, zero_mul, smul_eq_mul, mul_one,
    Rat.cast_div, Rat.cast_one, Rat.cast_natCast, one_div]
  exact mul_nonneg (by positivity) (by exact_mod_cast hd)

/-- The reduced floor `⌊B⌋`, as the closed subscheme `B.roundDown.suppScheme`, has underlying set
the union of the floor components. -/
private theorem range_suppIdeal_subschemeι {X : Scheme.{0}} (D : Divisor X) :
    Set.range D.suppIdeal.subschemeι.base = ⋃ E ∈ D.support, (E.support : Set X) := by
  rw [Scheme.IdealSheafData.range_subschemeι, DivisorWithCoeffs.coe_support_suppIdeal,
    DivisorWithCoeffs.coe_supp]

/-- `A / q` is `ℚ`-Cartier for a Cartier divisor `A` and `q > 0`. -/
private theorem isQCartier_inv_smul {R : Scheme.{0}} [IsLocallyNoetherian R] [IsNormal R]
    {A : Divisor R} (hAc : A.IsCartier) {q : ℕ} (hq : 0 < q) :
    ((q : ℚ)⁻¹ • Divisor.toQDivisor A).IsQCartier := by
  have hkq : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  exact ⟨q, by exact_mod_cast hq.ne', A, by
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]; simp [hkq], hAc⟩

/-- **Pull-back of `A / q`.** If the Cartier divisor `A` pulls back to `W` along a dominant `h`,
then `A / q` pulls back to `W / q`. -/
private theorem isPullback_inv_smul {X R : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral R] [CompactSpace R] [IsLocallyNoetherian R]
    [IsNormal R] (h : X ⟶ R) [IsDominant h] {A : Divisor R} (hAc : A.IsCartier)
    {hA : ∀ Z : irreducibleComponents X, h (componentGenericPoint X Z) ∉ A.supp} {W : Divisor X}
    (hW : A.IsPullback h hA W) {q : ℕ} (hq : 0 < q)
    (hgen : ∀ Z : irreducibleComponents X,
      h (componentGenericPoint X Z) ∉ ((q : ℚ)⁻¹ • Divisor.toQDivisor A).supp) :
    ((q : ℚ)⁻¹ • Divisor.toQDivisor A).IsPullback h hgen ((q : ℚ)⁻¹ • Divisor.toQDivisor W) := by
  intro m hm D hD hDc
  have hkD : (q : ℤ) • D = (m : ℤ) • A := Divisor.toQDivisor_injective (by
    rw [map_zsmul, map_zsmul, hD, smul_smul, ← Int.cast_smul_eq_zsmul ℚ,
      ← Int.cast_smul_eq_zsmul ℚ (m : ℤ), smul_smul]
    congr 1
    push_cast
    field_simp)
  have hgD := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' h D
  have hpD := Divisor.isPullback_pullback hDc hgD
  have h1 := hpD.zsmul hDc (q : ℤ)
    (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' h _)
  have h2 := (hW.zsmul hAc (m : ℤ)
    (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' h _)).of_eq
      hkD.symm (hB₂ := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' h _)
  have h3 : (q : ℤ) • D.pullback hDc hgD = (m : ℤ) • W :=
    Divisor.IsPullback.eq (hDc.zsmul _) h1 h2
  refine ⟨D.pullback hDc hgD, ?_, hpD⟩
  have h4 := congrArg Divisor.toQDivisor h3
  rw [map_zsmul, map_zsmul] at h4
  have hk0 : ((q : ℤ)) ≠ 0 := by exact_mod_cast hq.ne'
  apply smul_right_injective (QDivisor X) hk0
  change (q : ℤ) • _ = (q : ℤ) • _
  rw [h4]
  simp only [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
  congr 1
  push_cast
  field_simp

/-- If `M = q(K + B)` is linearly equivalent to `W`, then `K + B ∼_ℚ W / q`. -/
private theorem qLinearlyEquivalent_inv_smul {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {K M W : Divisor X} {B : QDivisor X} {q : ℕ} (hq : 0 < q)
    (hMq : Divisor.toQDivisor M = (q : ℤ) • (Divisor.toQDivisor K + B))
    (hMW : M.LinearlyEquivalent W) :
    (Divisor.toQDivisor K + B).QLinearlyEquivalent ((q : ℚ)⁻¹ • Divisor.toQDivisor W) := by
  obtain ⟨φ, hφ⟩ := hMW
  have hkq : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hMq' : Divisor.toQDivisor M = (q : ℚ) • (Divisor.toQDivisor K + B) := by
    rw [hMq, ← Int.cast_smul_eq_zsmul ℚ]; rfl
  exact ⟨q, hq, φ, by
    rw [← hφ, map_sub, hMq']
    simp only [← Int.cast_smul_eq_zsmul ℚ]
    rw [smul_sub, smul_smul]
    simp [hkq]⟩

/-- **Preadmissible lifting for a big semiample adjoint.** For a `ℚ`-factorial projective dlt
surface `(X, B)` with nonempty floor and `K + B` nef and big, the conclusion of
`MMP.Fourfold.exists_isPoincareResidue_pow_of_mem_admissibleSections` holds in every even degree
divisible by the index `k` of the adjoint ample model `h : X ⟶ X'`: the floor image `h(⌊B⌋)` is a
proper closed subset of the surface `X'`, so it has the structure-sheaf property. -/
private theorem exists_isPoincareResidue_pow_of_isRelativelyBig {X : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hX : Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 2)
    (hQ : IsQFactorial sX) {B : QDivisor X} (hB : IsPair sX B)
    (hdlt : MMP.Intersection.IsDltPair sX B) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2)
    (hsemi : QDivisor.IsRelativelySemiample sX (Divisor.toQDivisor K + B))
    (hnef : QDivisor.IsRelativelyNef sX sX (Divisor.toQDivisor K + B))
    (hbig : QDivisor.IsRelativelyBig sX (Divisor.toQDivisor K + B)) (hS0 : B.roundDown ≠ 0) :
    ∃ k : ℕ, 0 < k ∧
      ∀ (C : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} → Scheme.{0})
        [∀ P, IsIntegral (C P)] [∀ P, IsLocallyNoetherian (C P)] [∀ P, IsNormal (C P)]
        (j : ∀ P, C P ⟶ X) (BC : ∀ P, QDivisor (C P))
        (_ : ∀ P, IsAdjunctionStep sX B (j P) (BC P) ∧
          Set.range (j P).base = (P.1.support : Set X))
        {m : ℕ} (_ : Even m) (_ : k ∣ m) (RS : ResidueRestriction (fun P => j P ≫ sX) BC 1 m)
        {A : Type} [Finite A] (t : A → ∀ P, logPluricanonicalSections (j P ≫ sX) 1 m (BC P))
        (_ : ∀ α, t α ∈ admissibleSections RS),
      ∃ a : ℕ, 0 < a ∧
        (∀ RX : ResidueRestriction (fun _ : Unit => sX) (fun _ => B) (1 + 1) (a * m),
          ∀ α, ∃ s ∈ preadmissibleSections RX, ∀ P,
            letI := functionFieldAlgebra (j P ≫ sX)
            ∀ (ω : ⋀[(C P).functionField]^1 Ω[(C P).functionField⁄ℂ]) (c : (C P).functionField),
              (t α P : RationalPluriForms (j P ≫ sX) 1 m) =
                  c • (formPow ω m : RationalPluriForms (j P ≫ sX) 1 m) →
                IsPoincareResidue sX (j P) 1 (a * m)
                  (s () : RationalPluriForms sX (1 + 1) ((a * m : ℕ) : ℤ))
                  (c ^ a • (formPow ω (a * m) :
                    RationalPluriForms (j P ≫ sX) 1 ((a * m : ℕ) : ℤ)))) ∧
        ((∀ P (y : C P), ∃ α, ∃ W : (C P).Opens, y ∈ W ∧
            GeneratesOn (BC P) m W (t α P : RationalPluriForms (j P ≫ sX) 1 m)) →
          ∀ x : X, ∃ σ ∈ logPluricanonicalSections sX (1 + 1) (a * m) B, ∃ U : X.Opens, x ∈ U ∧
            GeneratesOn B (a * m) U (σ : RationalPluriForms sX (1 + 1) ((a * m : ℕ) : ℤ)) ∧
            ((∀ P, IsPoincareResidue sX (j P) 1 (a * m)
                (σ : RationalPluriForms sX (1 + 1) ((a * m : ℕ) : ℤ)) 0) ∨
              ∃ α, ∀ P,
                letI := functionFieldAlgebra (j P ≫ sX)
                ∀ (ω : ⋀[(C P).functionField]^1 Ω[(C P).functionField⁄ℂ])
                  (c : (C P).functionField),
                  (t α P : RationalPluriForms (j P ≫ sX) 1 m) =
                      c • (formPow ω m : RationalPluriForms (j P ≫ sX) 1 m) →
                    IsPoincareResidue sX (j P) 1 (a * m)
                      (σ : RationalPluriForms sX (1 + 1) ((a * m : ℕ) : ℤ))
                      (c ^ a • (formPow ω (a * m) :
                        RationalPluriForms (j P ≫ sX) 1 ((a * m : ℕ) : ℤ))))) := by
  classical
  have hB0 : 0 ≤ B := fun P => hdlt.1.2.1 P
  obtain ⟨V', _, _, _, _, sV', h, f', hhf, hf', hV'n, hV'p, hhp, hhb, hhO, -, k, hk, L, hL,
    -, hLamp, M, hMeq, ⟨hM, hpb⟩, -⟩ :=
    Mori.IsLcPair.exists_isRelativelyAmple_of_isRelativelyNef_of_isRelativelyBig hB0
      (isLcPair_of_isDltPair hdlt hK) hX isProjectiveVariety_id_spec sX (Category.comp_id _)
      hnef hbig
  obtain rfl : sV' = f' := by rw [← hf', Category.comp_id]
  refine ⟨k, hk, fun C _ _ _ j BC hC m hm hkm RS A _ t ht => ?_⟩
  haveI := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal B.roundDown.supp
  set ιS := B.roundDown.suppIdeal.subschemeι with hιS
  have hrS : Set.range ιS.base = ⋃ E ∈ B.roundDown.support, (E.support : Set X) :=
    range_suppIdeal_subschemeι _
  haveI : IsReduced B.roundDown.suppIdeal.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hrV : Set.range (ιS ≫ h).imageι.base = h.base '' Set.range ιS.base := by
    haveI : IsProper h := isProper_of_isProjectiveMorphism h hhp
    change Set.range (ιS ≫ h).ker.subschemeι.base = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker,
      (ιS ≫ h).isClosedMap.isClosed_range.closure_eq, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp]
  have hO : ∀ U : (ιS ≫ h).image.Opens, IsIso ((ιS ≫ h).toImage.app U) := by
    haveI : Mori.IsProjectiveVariety ℂ sX := hX
    haveI : Mori.IsProjectiveVariety ℂ sV' := hV'p
    have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
    have hHq := isQCartier_inv_smul hL hk
    haveI := hhb.isDominant
    have hgen : ∀ Z : irreducibleComponents X,
        h (componentGenericPoint X Z) ∉ ((k : ℚ)⁻¹ • Divisor.toQDivisor L).supp :=
      MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' h _
    have hKBM : Divisor.toQDivisor K + B = (k : ℚ)⁻¹ • Divisor.toQDivisor M := by
      rw [hMeq, smul_smul, inv_mul_cancel₀ hkq, one_smul]
    have hpbQ : ((k : ℚ)⁻¹ • Divisor.toQDivisor L).IsPullback h hgen
        (Divisor.toQDivisor K + B) := hKBM ▸ isPullback_inv_smul h hL hpb hk hgen
    have hne : Set.range (B.roundDown.suppIdeal.subschemeι ≫ h).base ≠ Set.univ := by
      intro huniv
      haveI : IsNoetherian V' := {}
      haveI : IsProper h := isProper_of_isProjectiveMorphism h hhp
      have hb := hhb.functionFieldMap_bijective
      have hbir : IsBirational h := isBirational_of_surjective_functionFieldMap h hb.2
      obtain ⟨W, hW, hiso⟩ := exists_isIso_restrict_of_mem_genericPoints h hbir
        (genericPoint V') (Stacks.Chow.genericPoint_mem_genericPoints V')
      obtain ⟨y, hy⟩ : genericPoint V' ∈ Set.range (B.roundDown.suppIdeal.subschemeι ≫ h).base :=
        huniv ▸ trivial
      have hxW : ιS y ∈ h ⁻¹ᵁ W := by
        show h (ιS y) ∈ W
        rw [Scheme.Hom.comp_apply] at hy; rw [hy]; exact hW
      have hηW : genericPoint X ∈ h ⁻¹ᵁ W := by
        show h (genericPoint X) ∈ W
        rw [map_genericPoint_of_isDominant]; exact hW
      have hxη : ιS y = genericPoint X := by
        have hinj := (ConcreteCategory.bijective_of_isIso (h ∣_ W).base).1
        have e : (h ∣_ W) ⟨ιS y, hxW⟩ = (h ∣_ W) ⟨genericPoint X, hηW⟩ := by
          apply Subtype.ext
          refine (morphismRestrict_base_coe h W ⟨ιS y, hxW⟩).trans
            (Eq.trans ?_ (morphismRestrict_base_coe h W ⟨genericPoint X, hηW⟩).symm)
          rw [Scheme.Hom.comp_apply] at hy
          change h (ιS y) = h (genericPoint X)
          rw [hy, map_genericPoint_of_isDominant]
        exact congrArg Subtype.val (hinj e)
      have hmem : genericPoint X ∈ Set.range ιS.base := hxη ▸ ⟨y, rfl⟩
      rw [hrS] at hmem
      obtain ⟨E, -, hE⟩ := Set.mem_iUnion₂.mp hmem
      exact MMP.Threefold.Mori.OpenRestriction.genericPoint_notMem_support E hE
    exact isIso_app_toImage_suppScheme_of_isDltPair_of_qLinearlyEquivalent sX sV' h hhf hhp hhO
      K B ((MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hK B).mp hdlt) hQ _ hHq _
      ⟨hgen, hpbQ⟩ (by rfl) hne
  exact exists_isPoincareResidue_pow_of_mem_admissibleSections hX (n := 1) hdim hQ hB hdlt hK
    hsemi hV'n hV'p h hhf hhp hhO hk hL hLamp ⟨hM, hpb⟩ (by rw [hMeq]) hS0 ιS hrS
    (ιS ≫ h).imageι hrV (ιS ≫ h).toImage (Scheme.Hom.toImage_imageι _) hO C j BC hC hm hkm RS t ht

/-- **A pole of full order has a nonzero residue.** Let `j : T ⟶ Y` be the inclusion of a normal
prime divisor `P` of a normal complex variety `Y` of dimension `n + 1`. If a rational
`N`-canonical form `τ ≠ 0`, `N > 0`, with `ord_P τ ≥ -N` has Poincaré residue zero along `T`,
then `ord_P τ > -N`: writing `τ = f σ^{⊗N}` for a form `σ` with a simple pole along `P`, an order
`ord_P τ = -N` makes `f` a unit along `P`, and the residue `f|_T (Res σ)^{⊗N}` is nonzero. -/
private theorem neg_lt_ordForm_of_isPoincareResidue_zero {Y T : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y] [CompactSpace Y]
    [LocallyOfFiniteType sY] (hY : IsNormalVariety ℂ sY) {n : ℕ}
    (hdim : topologicalKrullDim Y = n + 1) (j : T ⟶ Y) [IsClosedImmersion j] [IsIntegral T]
    [IsNormal T] [IsLocallyNoetherian T] [CompactSpace T] (hT : IsNormalVariety ℂ (j ≫ sY))
    (hdT : topologicalKrullDim T = n)
    (P : Mori.PrimeDivisor Y) (hP : Set.range j.base = (P.support : Set Y))
    (Q : Mori.PrimeDivisor T) {N : ℕ} (hN : 0 < N) {τ : RationalPluriForms sY (n + 1) N}
    (hτ0 : τ ≠ 0) (hle : -(N : ℤ) ≤ P.ordForm τ)
    (hρ : IsPoincareResidue sY j n N τ 0) : -(N : ℤ) < P.ordForm τ := by
  classical
  haveI : LocallyOfFiniteType (j ≫ sY) := hT.1.toLocallyOfFiniteType
  have hjT := MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hP
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (j ≫ sY)
  have hd : (Algebra.trdeg ℂ Y.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) (by rw [hdim]; norm_cast)
  obtain ⟨σ, hσ0, hσP, -, ρσ, hσres, hρσ0, -⟩ :=
    exists_form_of_residue_order sY hY hdim j hT P hP Q
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hσM0 := MMP.CyclicChartDifferent.Aux.pluriPow_ne_zero (sX := sY)
    (by rw [hdim]; norm_cast) hσ0 M
  obtain ⟨b₀⟩ := exists_basis_topForms (sX := sY) (d := n + 1) (by rw [hdim]; norm_cast)
  have hrank : Module.finrank Y.functionField
      (RationalPluriForms sY (n + 1) ((M + 1 : ℕ) : ℤ)) = 1 := by
    let bb : Module.Basis Unit Y.functionField
        (RationalPluriForms sY (n + 1) ((M + 1 : ℕ) : ℤ)) :=
      ZTensorPower.basis b₀ ((M + 1 : ℕ) : ℤ)
    rw [Module.finrank_eq_card_basis bb, Fintype.card_unit]
  obtain ⟨f, hf⟩ := (finrank_eq_one_iff_of_nonzero' _ hσM0).mp hrank τ
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hτ0 (by rw [← hf, zero_smul])
  have hordf : Y.ord f P.genericPoint = P.ordForm τ + (M + 1 : ℕ) := by
    have h1 := P.ordForm_smul (sX := sY) hd hf0 hσM0
    rw [hf, MMP.CyclicChartDifferent.Aux.ordForm_pluriPow (by rw [hdim]; norm_cast) hσ0 P M,
      hσP] at h1
    push_cast at h1 ⊢
    omega
  by_contra hlt
  have heq : P.ordForm τ = -((M + 1 : ℕ) : ℤ) := le_antisymm (not_lt.mp hlt) hle
  have hf00 : Y.ord f P.genericPoint = 0 := by rw [hordf, heq]; ring
  obtain ⟨v, hv, hvf⟩ := MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero
    (j (genericPoint T)) hf0 fun Γ hΓ => by
      rw [hjT] at hΓ
      obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hΓ
      exact hf00
  have hres := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul
    (MMP.CyclicChartDifferent.Aux.isPoincareResidue_pluriPow P hjT hdim hσres M) v
  rw [hvf, hf] at hres
  have h0 := IsPoincareResidue.unique_of_isClosedImmersion P hjT hρ hres
  have hρM0 := MMP.CyclicChartDifferent.Aux.pluriPow_ne_zero (sX := j ≫ sY)
    (by rw [hdT]) hρσ0 M
  have hvu : (j.stalkMap (genericPoint T)).hom v ≠ 0 := (hv.map _).ne_zero
  exact smul_ne_zero hvu hρM0 h0.symm

/-! ### The semiample contraction -/

/-- The projection of `ℙ(G) = Proj_Z(Sym G)` is proper when `G` is quasi-coherent of finite
type. -/
private theorem isProper_relativeProj_toBase {Z : Scheme.{0}} (G : Z.Modules) [G.IsQuasicoherent]
    [G.IsFiniteType] :
    IsProper (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
      (Stacks.SymGraded.schemeSheafGradedAlgebra G
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent G))).toBase := by
  have h := Stacks.RelativeProj.isProper_projectiveBundleToBase_of_isFiniteType Z G
  rw [← Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase G] at h
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mp h

/-- An `f`-ample Cartier divisor is ample over an affine neighbourhood of every point. -/
private theorem isRelativelyAmple_of_isRelativelyAmpleCartier {X Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} {W : Divisor Y}
    (hW : MMP.Flips.IsRelativelyAmpleCartier f W) : W.IsRelativelyAmple f hW.1 := by
  obtain ⟨hWc, hamp⟩ := hW
  have := hWc.isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  exact ⟨V, hV, hyV, hamp V hV⟩

/-- A projective morphism in the sense of EGA onto a scheme H-projective over a field is
H-projective, the target carrying an ample invertible sheaf. -/
private theorem isProjectiveMorphism_of_isProjective_of_isProjectiveMorphism {k : Type}
    [Field k] {Y Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of k)) (hsZ : IsProjectiveMorphism sZ)
    (f : Y ⟶ Z) (hf : IsProjective f) : IsProjectiveMorphism f := by
  haveI := Stacks.Ample.isInvertibleModule_unit (Spec (.of k))
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective sZ _
    (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    (isQuasiProjective_of_isHQuasiProjective _
      (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.1 hsZ).1)
  haveI := hL
  exact isProjectiveMorphism_of_isProjective f L hLa hf

/-- The Stein factor `V ⟶ V' ⟶ Z` of the morphism defined by a relatively free Cartier divisor
`R` with `𝒪(R) ≅ 𝒪_V(M)`, with `𝒪_V(M) ≅ h^* 𝒪_{V'}(A)` for an `f'`-ample Cartier divisor `A`. -/
private theorem exists_steinFactor
    {V Z : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    (hVn : IsNormalVariety ℂ sV)
    (hV : MMP.Mori.IsProjectiveVariety ℂ sV) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (f : V ⟶ Z) (hf : f ≫ sZ = sV) {M : Divisor V} (R : V.CartierDivisor)
    (hfree : IsRelativelyFreeCartier f R)
    (eR : MMP.CartierDivisor.sheaf R ≅ M.divisorialSheaf) :
    ∃ (V' : Scheme.{0}) (_ : IsIntegral V') (_ : IsLocallyNoetherian V') (_ : IsNormal V')
      (_ : CompactSpace V') (h : V ⟶ V') (f' : V' ⟶ Z),
      h ≫ f' = f ∧ IsNormalVariety ℂ (f' ≫ sZ) ∧ MMP.Mori.IsProjectiveVariety ℂ (f' ≫ sZ) ∧
        IsProjectiveMorphism h ∧ (∀ U : V'.Opens, IsIso (h.app U)) ∧
        ∃ (A : Divisor V') (hA : A.IsCartier), A.IsRelativelyAmple f' hA ∧
          Nonempty (M.divisorialSheaf ≅ (Scheme.Modules.pullback h).obj A.divisorialSheaf) := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sV := hV
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZ
  haveI : AlgebraicGeometry.IsVariety ℂ sV := hV.toIsVariety
  haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZ.toIsVariety
  haveI : IsProper sV := isProper_of_isProjectiveMorphism _ hV.isProjective
  haveI : IsProper sZ := isProper_of_isProjectiveMorphism _ hZ.isProjective
  haveI : IsProper f := by
    haveI : IsProper (f ≫ sZ) := hf ▸ inferInstance
    exact IsProper.of_comp f sZ
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have key := IsRelativelyFreeCartier.steinFactor_isRelativelyAmpleCartier sV sZ hVn
    (inferInstance : AlgebraicGeometry.IsVariety ℂ sZ) f hf R hfree
  dsimp only at key
  obtain ⟨⟨Φ, hΦ, e, hdef⟩, hall⟩ := key
  obtain ⟨hΦp, hall⟩ := hall Φ hΦ e hdef
  haveI : ((Scheme.Modules.pushforward f).obj
      (MMP.CartierDivisor.sheaf R)).IsQuasicoherent :=
    ProperCoherentFiniteType.isQuasicoherent_pushforward f _ inferInstance
  haveI : ((Scheme.Modules.pushforward f).obj
      (MMP.CartierDivisor.sheaf R)).IsFiniteType :=
    (AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f
      (MMP.CartierDivisor.sheaf R)).isFiniteType
  set π := (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
      (Stacks.SymGraded.schemeSheafGradedAlgebra ((Scheme.Modules.pushforward f).obj
        (MMP.CartierDivisor.sheaf R))
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _))).toBase with hπ
  haveI : IsProper π := isProper_relativeProj_toBase _
  obtain ⟨V', h, τ, ⟨hSt⟩, hhp, -, hO, -, hτ, -, hproj, -, -, -⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isVariety sV (π ≫ sZ) Φ
      (by rw [← Category.assoc, hΦ, hf])
  obtain ⟨hV'n, -, -, i1, i2, i3, A, hA, -, ⟨eA⟩⟩ := hall V' h τ hSt
  haveI := i1
  haveI := hτ
  have hhf : h ≫ τ ≫ π = f := by rw [← Category.assoc, hSt.comp, hΦ]
  haveI : AlgebraicGeometry.IsVariety ℂ ((τ ≫ π) ≫ sZ) := by
    rw [Category.assoc]; exact hV'n.1
  have hA' := isRelativelyAmple_of_isRelativelyAmpleCartier hA
  have hf'p : IsProjectiveMorphism (τ ≫ π) := by
    haveI := hA.1.isInvertibleModule_divisorialSheaf
    haveI : CompactSpace Z := (quasiCompact_iff_compactSpace sZ).mp inferInstance
    haveI : IsNoetherian Z := ⟨⟩
    exact isProjectiveMorphism_of_isProjective_of_isProjectiveMorphism sZ hZ.isProjective _
      (MMP.isProjective_of_isProper_of_isRelativelyAmple (τ ≫ π) A.divisorialSheaf hA')
  have hV'p : MMP.Mori.IsProjectiveVariety ℂ ((τ ≫ π) ≫ sZ) :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr ⟨inferInstance, hf'p.comp hZ.isProjective⟩
  haveI : IsQuasiProjectiveVariety ℂ sV := IsProjectiveVariety.isQuasiProjectiveVariety ℂ sV
  have hhproj : IsProjectiveMorphism h :=
    MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety sV ((τ ≫ π) ≫ sZ) h
      (by rw [← Category.assoc, hhf, hf])
  refine ⟨V', hV'n.1.toIsIntegral, i1, i2, i3, h, τ ≫ π, hhf, by rwa [Category.assoc], hV'p, hhproj,
    hO, A, hA.1, hA', ⟨eR.symm ≪≫ eA⟩⟩

/-- A morphism inducing isomorphisms on all rings of sections is dominant: an open set missing
the image would have no sections upstairs. -/
private theorem isDominant_of_forall_isIso_app {X Y : Scheme.{0}} (f : X ⟶ Y)
    (hf : ∀ U : Y.Opens, IsIso (f.app U)) : IsDominant f := by
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq]
  by_contra hne
  set U : Y.Opens := ⟨(closure (Set.range f.base))ᶜ, isClosed_closure.isOpen_compl⟩
  have hU : (U : Set Y).Nonempty := Set.nonempty_compl.mpr hne
  haveI : Nonempty U := hU.to_subtype
  have hpre : f ⁻¹ᵁ U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact hx (subset_closure (Set.mem_range_self x))
  haveI : Subsingleton Γ(X, f ⁻¹ᵁ U) :=
    CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hpre)
  haveI : Subsingleton Γ(Y, U) :=
    (asIso (f.app U)).commRingCatIsoToRingEquiv.injective.subsingleton
  exact not_subsingleton Γ(Y, U) inferInstance

/-- `HasPowLifting sX B k`: in every even degree `m` divisible by `k`, for every finite family of
admissible systems `t_α` on the floor curves of `(X, B)`, there is `a > 0` such that equal powers
`t_α^a` lift to preadmissible sections of `am(K + B)`, and, if the `t_α` generate the floor curves,
every point of `X` has a generator of `am(K + B)` with zero floor residues or lifting some
`t_α^a`. This is the conclusion of
`MMP.Fourfold.exists_isPoincareResidue_pow_of_mem_admissibleSections` for surfaces. -/
private def HasPowLifting {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (B : QDivisor X) (k : ℕ) : Prop :=
  ∀ (C : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} → Scheme.{0})
    [∀ P, IsIntegral (C P)] [∀ P, IsLocallyNoetherian (C P)] [∀ P, IsNormal (C P)]
    (j : ∀ P, C P ⟶ X) (BC : ∀ P, QDivisor (C P))
    (_ : ∀ P, IsAdjunctionStep sX B (j P) (BC P) ∧
      Set.range (j P).base = (P.1.support : Set X))
    {m : ℕ} (_ : Even m) (_ : k ∣ m) (RS : ResidueRestriction (fun P => j P ≫ sX) BC 1 m)
    {A : Type} [Finite A] (t : A → ∀ P, logPluricanonicalSections (j P ≫ sX) 1 m (BC P))
    (_ : ∀ α, t α ∈ admissibleSections RS),
  ∃ a : ℕ, 0 < a ∧
    (∀ RX : ResidueRestriction (fun _ : Unit => sX) (fun _ => B) (1 + 1) (a * m),
      ∀ α, ∃ s ∈ preadmissibleSections RX, ∀ P,
        letI := functionFieldAlgebra (j P ≫ sX)
        ∀ (ω : ⋀[(C P).functionField]^1 Ω[(C P).functionField⁄ℂ]) (c : (C P).functionField),
          (t α P : RationalPluriForms (j P ≫ sX) 1 m) =
              c • (formPow ω m : RationalPluriForms (j P ≫ sX) 1 m) →
            IsPoincareResidue sX (j P) 1 (a * m)
              (s () : RationalPluriForms sX (1 + 1) ((a * m : ℕ) : ℤ))
              (c ^ a • (formPow ω (a * m) :
                RationalPluriForms (j P ≫ sX) 1 ((a * m : ℕ) : ℤ)))) ∧
    ((∀ P (y : C P), ∃ α, ∃ W : (C P).Opens, y ∈ W ∧
        GeneratesOn (BC P) m W (t α P : RationalPluriForms (j P ≫ sX) 1 m)) →
      ∀ x : X, ∃ σ ∈ logPluricanonicalSections sX (1 + 1) (a * m) B, ∃ U : X.Opens, x ∈ U ∧
        GeneratesOn B (a * m) U (σ : RationalPluriForms sX (1 + 1) ((a * m : ℕ) : ℤ)) ∧
        ((∀ P, IsPoincareResidue sX (j P) 1 (a * m)
            (σ : RationalPluriForms sX (1 + 1) ((a * m : ℕ) : ℤ)) 0) ∨
          ∃ α, ∀ P,
            letI := functionFieldAlgebra (j P ≫ sX)
            ∀ (ω : ⋀[(C P).functionField]^1 Ω[(C P).functionField⁄ℂ])
              (c : (C P).functionField),
              (t α P : RationalPluriForms (j P ≫ sX) 1 m) =
                  c • (formPow ω m : RationalPluriForms (j P ≫ sX) 1 m) →
                IsPoincareResidue sX (j P) 1 (a * m)
                  (σ : RationalPluriForms sX (1 + 1) ((a * m : ℕ) : ℤ))
                  (c ^ a • (formPow ω (a * m) :
                    RationalPluriForms (j P ≫ sX) 1 ((a * m : ℕ) : ℤ)))))

/-- The dimension formula for a dominant morphism onto the closure of its image: `X` has the
dimension of `closure f(X)` plus that of the generic fibre. -/
private theorem topologicalKrullDim_eq_add_fiber {k : Type} [Field k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sY] (f : X ⟶ Y) (hf : f ≫ sY = sX) [QuasiCompact f] :
    topologicalKrullDim X = topologicalKrullDim (closure (Set.range f.base)) +
      topologicalKrullDim (f.fiber (f (genericPoint X))) := by
  have hLY : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hLX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hfact : f.toImage ≫ f.imageι = f := Scheme.Hom.toImage_imageι f
  have hLS : LocallyOfFiniteType (f.imageι ≫ sY) := by infer_instance
  haveI : LocallyOfFiniteType (f.toImage ≫ f.imageι ≫ sY) := by
    rw [← Category.assoc, hfact, hf]; infer_instance
  haveI : LocallyOfFiniteType f.toImage := LocallyOfFiniteType.of_comp (g := f.imageι ≫ sY)
      inferInstance
  haveI : IsLocallyNoetherian f.image := LocallyOfFiniteType.isLocallyNoetherian (f.imageι ≫ sY)
  haveI : IrreducibleSpace f.image := (irreducibleSpace_def _).2 (by
      have h := ((IrreducibleSpace.isIrreducible_univ X).image _
          f.toImage.continuous.continuousOn).closure
      rwa [Set.image_univ, (IsDominant.denseRange (f := f.toImage)).closure_eq] at h)
  obtain ⟨O, hO, hne, hform⟩ :=
      exists_isOpen_nonempty_topologicalKrullDimAt_eq_add_fiber_of_irreducibleSpace f.toImage
  have hξ : genericPoint X ∈ O := by
    obtain ⟨w, hw⟩ := hne
    exact ((genericPoint_spec X).mem_open_set_iff hO).2 ⟨w, ⟨trivial, hw⟩⟩
  have h1 := hform _ hξ
  have e1 : topologicalKrullDim X = topologicalKrullDimAt X (genericPoint X) :=
    topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X sX _
  have e2 : topologicalKrullDim f.image =
      topologicalKrullDimAt f.image (f.toImage (genericPoint X)) :=
    topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k f.image (f.imageι ≫ sY) _
  have e3 : topologicalKrullDim f.image = topologicalKrullDim (closure (Set.range f.base)) := by
    let e := f.imageι.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (Scheme.Hom.range_imageι f))
    exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph
  have hset : (f.toImage ⁻¹' {f.toImage (genericPoint X)} : Set X) = f ⁻¹' {f (genericPoint X)} :=
      by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; rw [← hfact]; simp only [Scheme.Hom.comp_apply]; rw [h]
    · intro h
      rw [← hfact] at h
      simp only [Scheme.Hom.comp_apply] at h
      exact f.imageι.injective h
  have hirr : IsIrreducible (f.toImage ⁻¹' {f.toImage (genericPoint X)} : Set X) := by
    rw [← isIrreducible_iff_closure]
    have : closure (f.toImage ⁻¹' {f.toImage (genericPoint X)} : Set X) = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← (genericPoint_spec X).def]
      exact closure_mono (by simp)
    rw [this]; exact IrreducibleSpace.isIrreducible_univ X
  haveI : IrreducibleSpace (f.toImage.fiber (f.toImage (genericPoint X))) := by
    refine (irreducibleSpace_def _).2 ?_
    haveI : IrreducibleSpace ↥(f.toImage ⁻¹' {f.toImage (genericPoint X)} : Set X) :=
      Subtype.irreducibleSpace hirr
    let φ := f.toImage.fiberHomeo (f.toImage (genericPoint X))
    have h := (IrreducibleSpace.isIrreducible_univ
      ↥(f.toImage ⁻¹' {f.toImage (genericPoint X)} : Set X)).image φ.symm
      φ.symm.continuous.continuousOn
    rwa [Set.image_univ, φ.symm.surjective.range_eq] at h
  have e4 : topologicalKrullDim (f.toImage.fiber (f.toImage (genericPoint X))) =
      topologicalKrullDimAt (f.toImage.fiber (f.toImage (genericPoint X)))
        (f.toImage.asFiber (genericPoint X)) :=
    have := Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField f.toImage
      (f.toImage (genericPoint X))
    topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible
      (f.image.residueField (f.toImage (genericPoint X)))
      (f.toImage.fiber (f.toImage (genericPoint X)))
      (f.toImage.fiberToSpecResidueField _) _
  have e5 : topologicalKrullDim (f.toImage.fiber (f.toImage (genericPoint X))) =
      topologicalKrullDim (f.fiber (f (genericPoint X))) := by
    let e := (f.toImage.fiberHomeo (f.toImage (genericPoint X))).trans
      ((Homeomorph.setCongr hset).trans (f.fiberHomeo (f (genericPoint X))).symm)
    exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph
  rw [e1, h1, ← e4, ← e2, e3, e5]

/-- The dimension formula in natural numbers: with `a = dim X` and `b = dim closure f(X)`, we have
`b ≤ a` and the generic fibre has dimension `a - b`. -/
private theorem exists_dim_generic_fibre {k : Type} [Field k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sY] (f : X ⟶ Y) (hf : f ≫ sY = sX) [QuasiCompact f] [CompactSpace X] :
    ∃ a b : ℕ, topologicalKrullDim X = a ∧ topologicalKrullDim (closure (Set.range f.base)) = b ∧
      b ≤ a ∧ topologicalKrullDim (f.fiber (f (genericPoint X))) = ((a - b : ℕ) : ℕ∞) := by
  have h := topologicalKrullDim_eq_add_fiber sX sY f hf
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  have hbot : topologicalKrullDim X ≠ ⊥ := fun hb =>
    ((Order.krullDim_eq_bot_iff.mp hb).false (TopologicalSpace.IrreducibleCloseds.closureSingleton
        (genericPoint X))).elim
  induction hX : topologicalKrullDim X using WithBot.recBotCoe with
  | bot => exact absurd hX hbot
  | coe a' =>
    induction hB : topologicalKrullDim (closure (Set.range f.base)) using WithBot.recBotCoe with
    | bot => rw [hX, hB] at h; simp at h
    | coe B =>
      induction hD : topologicalKrullDim (f.fiber (f (genericPoint X))) using WithBot.recBotCoe with
      | bot => rw [hX, hB, hD] at h; simp at h
      | coe D =>
        rw [hX, hB, hD, ← WithBot.coe_add, WithBot.coe_inj] at h
        have ha : a' ≠ ⊤ := by rintro rfl; exact h1 hX
        have hB' : B ≠ ⊤ := by rintro rfl; rw [top_add] at h; exact ha h
        have hD' : D ≠ ⊤ := by rintro rfl; rw [add_top] at h; exact ha h
        lift a' to ℕ using ha
        lift B to ℕ using hB'
        lift D to ℕ using hD'
        have h' : a' = B + D := by exact_mod_cast h
        refine ⟨a', B, rfl, rfl, by omega, ?_⟩
        have : D = a' - B := by omega
        rw [this]

/-- **A floor which maps onto the base of a contraction from a surface forces a curve base.** If
`h : X ⟶ R` is a dominant morphism from a dlt surface `(X, B)` to a positive-dimensional variety
and `h` maps the floor `⌊B⌋` onto `R`, then `R` is a curve: some floor curve maps onto `R`. -/
private theorem topologicalKrullDim_eq_one_of_range_eq_univ {X R : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hX : Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 2) {B : QDivisor X}
    (hdlt : MMP.Intersection.IsDltPair sX B) [IsIntegral R] {sR : R ⟶ Spec (.of ℂ)}
    (hRp : Mori.IsProjectiveVariety ℂ sR) (h : X ⟶ R) (hhf : h ≫ sR = sX)
    (hhp : IsProjectiveMorphism h) [IsDominant h]
    (huniv : Set.range (B.roundDown.suppIdeal.subschemeι ≫ h).base = Set.univ)
    (hR0 : topologicalKrullDim R ≠ 0) : topologicalKrullDim R = 1 := by
  classical
  haveI : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sR := hRp.toLocallyOfFiniteType
  haveI : IsProper h := isProper_of_isProjectiveMorphism h hhp
  have hclR : closure (Set.range h.base) = Set.univ := h.denseRange.closure_range
  have hdR : ∀ {T : Scheme.{0}} [IsIntegral T] [CompactSpace T] (j : T ⟶ X)
      [LocallyOfFiniteType (j ≫ sX)] [QuasiCompact (j ≫ h)],
      closure (Set.range (j ≫ h).base) = Set.univ →
      ∃ a b : ℕ, topologicalKrullDim T = a ∧ topologicalKrullDim R = b ∧ b ≤ a := by
    intro T _ _ j _ _ hcl
    obtain ⟨a, b, ha, hb, hba, -⟩ := exists_dim_generic_fibre (j ≫ sX) sR (j ≫ h)
      (by rw [Category.assoc, hhf])
    refine ⟨a, b, ha, ?_, hba⟩
    rw [hcl] at hb
    rw [← hb]
    exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ R)
      (Homeomorph.Set.univ R).isHomeomorph).symm
  -- the floor component mapping onto `R`
  have hrS := range_suppIdeal_subschemeι B.roundDown
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrS, Set.image_iUnion₂] at huniv
  have hirr : IsIrreducible (Set.univ : Set R) := IrreducibleSpace.isIrreducible_univ R
  obtain ⟨s', hs', hsub⟩ := (isIrreducible_iff_sUnion_isClosed.mp hirr)
    ((B.roundDown.support).image fun E => h.base '' (E.support : Set X))
    (by
      simp only [Finset.mem_image]
      rintro _ ⟨E, -, rfl⟩
      exact h.isClosedMap _ (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure))
    (by
      intro y _
      have : y ∈ ⋃ i ∈ B.roundDown.support, h.base '' (i.support : Set X) := huniv ▸ trivial
      obtain ⟨E, hE, hy⟩ := Set.mem_iUnion₂.mp this
      have hmem : (Set.image h.base (E.support : Set X)) ∈
          ((B.roundDown.support.image fun E => Set.image h.base (E.support : Set X) :
            Finset (Set R)) : Set (Set R)) :=
        Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hE)
      exact Set.mem_sUnion.mpr ⟨_, hmem, hy⟩)
  obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hs'
  have hfl : ⌊B.coeff E⌋ ≠ 0 := by
    have h1 : (B.roundDown).coeff E ≠ 0 := Finsupp.mem_support_iff.mp hE
    rwa [DivisorWithCoeffs.coeff_roundDown] at h1
  obtain ⟨T, jT, BT, hj, hrange, -⟩ := exists_isAdjunctionStep_of_one_le_coeff hdlt (d := 1)
    (by rw [hdim]; rfl) E (one_le_coeff_of_floor_ne_zero hdlt E hfl)
  haveI : IsIntegral T := hj.1.1.toIsIntegral
  obtain ⟨-, -, -, -, hci, -⟩ := id hj
  haveI := hci
  haveI : LocallyOfFiniteType (jT ≫ sX) := hj.1.1.toLocallyOfFiniteType
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace jT
  have hdT : topologicalKrullDim T = 1 :=
    topologicalKrullDim_eq_of_range_eq_support sX jT E hrange (by rw [hdim]; rfl)
  have hcl : closure (Set.range (jT ≫ h).base) = Set.univ := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]
    exact Set.eq_univ_of_univ_subset (hsub.trans subset_closure)
  obtain ⟨a, b, ha, hb, hba⟩ := hdR jT hcl
  rw [hdT] at ha
  have ha1 : a = 1 := by exact_mod_cast ha.symm
  subst ha1
  rw [hb] at hR0 ⊢
  have hb0 : b ≠ 0 := fun h0 => hR0 (by rw [h0]; rfl)
  have : b = 1 := by omega
  rw [this]; rfl

section LiftsPowSection

variable {I : Type u} {X : I → Scheme.{0}} [∀ i, IsIntegral (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    {sX : ∀ i, X i ⟶ Spec (.of ℂ)} {B : ∀ i, QDivisor (X i)}
    {Sf : (Σ i, {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0}) → Scheme.{0}}
    [∀ j, IsIntegral (Sf j)] [∀ j, IsLocallyNoetherian (Sf j)] [∀ j, IsNormal (Sf j)]
    {jf : ∀ j, Sf j ⟶ X j.1} {BSf : ∀ j, QDivisor (Sf j)}

variable (sX B jf BSf) in
/-- `σ`, a section of `N(K_{X_i} + B_i)`, lifts the `c`-th power of the floor system `u`
(in degree `m`): along every floor `j_{i,P}`, if `u_{i,P} = f · ω^{⊗m}` then the Poincaré
residue of `σ` is `f^c · ω^{⊗N}`; this is meant for `N = cm`. -/
private def LiftsPow (i : I) (m c N : ℕ) (σ : RationalPluriForms (sX i) 2 (N : ℤ))
    (u : ∀ j, logPluricanonicalSections (jf j ≫ sX j.1) 1 m (BSf j)) : Prop :=
  ∀ P : {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0},
    letI := functionFieldAlgebra (jf ⟨i, P⟩ ≫ sX i)
    ∀ (ω : ⋀[(Sf ⟨i, P⟩).functionField]^1 Ω[(Sf ⟨i, P⟩).functionField⁄ℂ])
      (f : (Sf ⟨i, P⟩).functionField),
      ((u ⟨i, P⟩ : logPluricanonicalSections (jf ⟨i, P⟩ ≫ sX i) 1 m (BSf ⟨i, P⟩)) :
          RationalPluriForms (jf ⟨i, P⟩ ≫ sX i) 1 m) =
          f • (formPow ω m : RationalPluriForms (jf ⟨i, P⟩ ≫ sX i) 1 m) →
        IsPoincareResidue (sX i) (jf ⟨i, P⟩) 1 N σ
          (f ^ c • (formPow ω N : RationalPluriForms (jf ⟨i, P⟩ ≫ sX i) 1 (N : ℤ)))

variable [Finite I] [∀ i, CompactSpace (X i)]
    (hdim : ∀ i, topologicalKrullDim (X i) = 2)
    (hSf : ∀ j, IsAdjunctionStep (sX j.1) (B j.1) (jf j) (BSf j) ∧
      Set.range (jf j).base = (j.2.1.support : Set (X j.1)))

/-- The floors of one component `X i` form a stratified section setting. -/
private theorem isStratifiedSectionSetting_floors_of_liftsPow {m : ℕ}
    (Rf : ResidueRestriction (fun j => jf j ≫ sX j.1) BSf 1 m) (i : I) :
    IsStratifiedSectionSetting
      (fun P : {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0} => jf ⟨i, P⟩ ≫ sX i)
      (fun P => BSf ⟨i, P⟩) 1 m where
  finite := by
    haveI := Rf.setting.finite
    exact Finite.of_injective
      (fun P : {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0} =>
        (⟨i, P⟩ : Σ i, {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0}))
      fun _ _ h => eq_of_heq (Sigma.mk.inj h).2
  isProjectiveVariety := fun P => Rf.setting.isProjectiveVariety ⟨i, P⟩
  isPair := fun P => Rf.setting.isPair ⟨i, P⟩
  isDltPair := fun P => Rf.setting.isDltPair ⟨i, P⟩
  topologicalKrullDim_eq := fun P => Rf.setting.topologicalKrullDim_eq ⟨i, P⟩
  even := Rf.setting.even
  pos := Rf.setting.pos
  isCartierDivisor := fun P => Rf.setting.isCartierDivisor ⟨i, P⟩

/-- Along every flag of `(X i, B i)`, the stratum's log canonical divisor is `ℚ`-Cartier. -/
private theorem exists_isCanonicalDivisor_isQCartier_of_liftsPow {N : ℕ}
    (R : ResidueRestriction sX B 2 N) (i : I) {S : Scheme.{0}} {ι : S ⟶ X i}
    {BS : QDivisor S} (F : StratumAdjunctionData (sX i) (B i) ι BS) :
    haveI := F.isIntegral_stratum
    haveI := F.isNormal_stratum
    haveI := F.isLocallyNoetherian_stratum
    ∃ (d : ℕ) (K : Divisor S), K.IsCanonicalDivisor (ι ≫ sX i) d ∧
      (Divisor.toQDivisor K + BS).IsQCartier := by
  obtain ⟨d, K, hK, hKC⟩ := R.setting.isCartierDivisor i F
  exact ⟨d, K, hK, ⟨((N : ℕ) : ℤ), by exact_mod_cast R.setting.pos.ne', hKC⟩⟩

/-- The residue of `s i` along a flag `G₀` of `X i` is read off the residue of `u` along a
matched flag `G` of a floor of `X i`. -/
private theorem toFun_eq_of_liftsPow {m c : ℕ} (hc0 : 0 < c)
    (Rf : ResidueRestriction (fun j => jf j ≫ sX j.1) BSf 1 m)
    (u : ∀ j, logPluricanonicalSections (jf j ≫ sX j.1) 1 m (BSf j))
    (R : ResidueRestriction sX B 2 (c * m))
    (s : ∀ i, logPluricanonicalSections (sX i) 2 (c * m) (B i))
    (hs : ∀ i, LiftsPow sX B jf BSf i m c (c * m)
      (s i : RationalPluriForms (sX i) 2 ((c * m : ℕ) : ℤ)) u)
    (i : I) (Q : {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0})
    {T : Scheme.{0}} {ιT : T ⟶ Sf ⟨i, Q⟩} {BT : QDivisor T}
    (G : StratumAdjunctionData (jf ⟨i, Q⟩ ≫ sX i) (BSf ⟨i, Q⟩) ιT BT)
    {T₀ : Scheme.{0}} {ι₀ : T₀ ⟶ X i} {B₀ : QDivisor T₀}
    (G₀ : StratumAdjunctionData (sX i) (B i) ι₀ B₀) (e : ℕ) :
    haveI := G.isIntegral_stratum
    haveI := G₀.isIntegral_stratum
    topologicalKrullDim T = e → topologicalKrullDim T₀ = e →
    ∀ (τ : FunctionFieldEquiv (ι₀ ≫ sX i) (ιT ≫ jf ⟨i, Q⟩ ≫ sX i)),
    (∀ (N : ℕ) (ζ : RationalPluriForms (sX i) (1 + 1) N)
      (ρQ : RationalPluriForms (jf ⟨i, Q⟩ ≫ sX i) 1 N),
      IsPoincareResidue (sX i) (jf ⟨i, Q⟩) 1 N ζ ρQ → ∀ (e' : ℕ),
      topologicalKrullDim T₀ = e' →
      ∀ ρ' : RationalPluriForms (ιT ≫ jf ⟨i, Q⟩ ≫ sX i) e' N,
        IsIteratedResidueRec ρQ G e' ρ' →
        IsIteratedResidueRec ζ G₀ e'
          (pluriformPullback (ι₀ ≫ sX i) (ιT ≫ jf ⟨i, Q⟩ ≫ sX i) τ.toHom e' N ρ')) →
    letI := functionFieldAlgebra (ιT ≫ jf ⟨i, Q⟩ ≫ sX i)
    ∀ (b : Module.Basis Unit T.functionField (⋀[T.functionField]^e Ω[T.functionField⁄ℂ]))
      (c₁ : T.functionField),
      Rf.toFun ⟨i, Q⟩ G e (u ⟨i, Q⟩) =
          c₁ • (formPow (b ()) m : RationalPluriForms (ιT ≫ jf ⟨i, Q⟩ ≫ sX i) e m) →
      R.toFun i G₀ e (s i) = pluriformPullback (ι₀ ≫ sX i) (ιT ≫ jf ⟨i, Q⟩ ≫ sX i) τ.toHom e
        ((c * m : ℕ) : ℤ) (c₁ ^ c • (formPow (b ()) (c * m) :
          RationalPluriForms (ιT ≫ jf ⟨i, Q⟩ ≫ sX i) e ((c * m : ℕ) : ℤ))) := by
  intro hT hT₀ τ hresG b c₁ hc₁
  haveI := G.isIntegral_stratum
  haveI := G₀.isIntegral_stratum
  letI := functionFieldAlgebra (jf ⟨i, Q⟩ ≫ sX i)
  letI := functionFieldAlgebra (ιT ≫ jf ⟨i, Q⟩ ≫ sX i)
  haveI : LocallyOfFiniteType (jf ⟨i, Q⟩ ≫ sX i) :=
    (Rf.setting.isPair ⟨i, Q⟩).isPair.isNormalVariety.1.toLocallyOfFiniteType
  obtain ⟨b₀⟩ := exists_basis_topForms (sX := jf ⟨i, Q⟩ ≫ sX i)
    (Rf.setting.topologicalKrullDim_eq ⟨i, Q⟩)
  obtain ⟨c₀, huQ⟩ : ∃ c₀ : (Sf ⟨i, Q⟩).functionField,
      (u ⟨i, Q⟩ : RationalPluriForms (jf ⟨i, Q⟩ ≫ sX i) 1 m) =
      c₀ • formPow (b₀ ()) m := ⟨_, eq_repr_smul_formPow b₀ _⟩
  have hIt := (Rf.isIteratedResidue ⟨i, Q⟩ G e (u ⟨i, Q⟩) hT).rec'
  rw [hc₁, huQ] at hIt
  have hpow := isIteratedResidueRec_pow (b₀ ()) c₀ G hT (b ()) c₁ hIt c hc0
  have hsQ := hs i Q (b₀ ()) c₀ huQ
  have h1 := hresG (c * m) (s i) _ hsQ e hT₀ _ hpow
  exact IsIteratedResidueRec.unique G₀ (R.isIteratedResidue i G₀ e (s i) hT₀).rec' h1

/-- A matched stratum of a floor has the dimension of the stratum of `X i` it matches. -/
private theorem topologicalKrullDim_eq_of_liftsPow {m : ℕ}
    (hd : ∀ i, topologicalKrullDim (X i) = ((1 + 1 : ℕ) : WithBot ℕ∞))
    (Rf : ResidueRestriction (fun j => jf j ≫ sX j.1) BSf 1 m) (e : ℕ)
    (i : I) (Q : {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0})
    {T : Scheme.{0}} {ιT : T ⟶ Sf ⟨i, Q⟩} {BT : QDivisor T}
    (G : StratumAdjunctionData (jf ⟨i, Q⟩ ≫ sX i) (BSf ⟨i, Q⟩) ιT BT)
    {T₀ : Scheme.{0}} {ι₀ : T₀ ⟶ X i} {B₀ : QDivisor T₀}
    (G₀ : StratumAdjunctionData (sX i) (B i) ι₀ B₀) :
    G.length + 1 = G₀.length → topologicalKrullDim T₀ = e →
    haveI := G.isIntegral_stratum
    topologicalKrullDim T = e := by
  intro hl hT₀
  haveI := G.isIntegral_stratum
  haveI : LocallyOfFiniteType (ιT ≫ jf ⟨i, Q⟩ ≫ sX i) :=
    G.isNormalVariety.1.toLocallyOfFiniteType
  have e1 := StratumAdjunctionData.dim_add_length (sX := sX i) (hd i) G₀ hT₀
  have e2 := StratumAdjunctionData.dim_add_length (sX := jf ⟨i, Q⟩ ≫ sX i)
    (Rf.setting.topologicalKrullDim_eq ⟨i, Q⟩) G
    (topologicalKrullDim_eq_toNat_trdeg (ιT ≫ jf ⟨i, Q⟩ ≫ sX i))
  rw [topologicalKrullDim_eq_toNat_trdeg (ιT ≫ jf ⟨i, Q⟩ ≫ sX i)]
  congr 1
  norm_cast
  omega

/-- Pulling back along `σ ∘ σ₂` is pulling back along `σ₁ ∘ (σ₁⁻¹ ∘ σ ∘ σ₂)`. -/
private theorem pluriformPullback_pullback_eq_trans_of_liftsPow
    {A A' A₁ A₂ : Scheme.{0}} [IsIntegral A] [IsIntegral A'] [IsIntegral A₁] [IsIntegral A₂]
    {sA : A ⟶ Spec (.of ℂ)} {sA' : A' ⟶ Spec (.of ℂ)} {sA₁ : A₁ ⟶ Spec (.of ℂ)}
    {sA₂ : A₂ ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA']
    [LocallyOfFiniteType sA₁] [LocallyOfFiniteType sA₂] {e : ℕ}
    (hA : topologicalKrullDim A = e) (hA' : topologicalKrullDim A' = e)
    (hA₁ : topologicalKrullDim A₁ = e) (hA₂ : topologicalKrullDim A₂ = e) (N : ℤ)
    (σ : FunctionFieldEquiv sA sA') (σ₂ : FunctionFieldEquiv sA' sA₂)
    (σ₁ : FunctionFieldEquiv sA sA₁) (y : RationalPluriForms sA₂ e N) :
    letI := functionFieldAlgebra sA
    letI := functionFieldAlgebra sA'
    letI := functionFieldAlgebra sA₁
    letI := functionFieldAlgebra sA₂
    pluriformPullback sA sA' σ.toHom e N (pluriformPullback sA' sA₂ σ₂.toHom e N y) =
      pluriformPullback sA sA₁ σ₁.toHom e N
        (pluriformPullback sA₁ sA₂
          (FunctionFieldEquiv.toHom sA₁ sA₂ (σ₂.trans (σ.trans σ₁.symm))) e N y) := by
  letI := functionFieldAlgebra sA
  letI := functionFieldAlgebra sA'
  letI := functionFieldAlgebra sA₁
  letI := functionFieldAlgebra sA₂
  have hh : (σ.toHom).comp (σ₂.toHom) =
      (σ₁.toHom).comp (FunctionFieldEquiv.toHom sA₁ sA₂ (σ₂.trans (σ.trans σ₁.symm))) := by
    ext x
    change σ (σ₂ x) = σ₁ (σ₁.symm (σ (σ₂ x)))
    rw [AlgEquiv.apply_symm_apply]
  rw [pluriformPullback_comp hA hA' hA₂, pluriformPullback_comp hA hA₁ hA₂, hh]

/-- `φ^*(c₂ w₂^{⊗m}) = c₁ b₁^{⊗m}` gives `c₁^c b₁^{⊗cm} = φ^*(c₂^c w₂^{⊗cm})`. -/
private theorem smul_formPow_pow_eq_pluriformPullback_of_liftsPow
    {A₁ A₂ : Scheme.{0}} [IsIntegral A₁] [IsIntegral A₂]
    {sA₁ : A₁ ⟶ Spec (.of ℂ)} {sA₂ : A₂ ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sA₁] [LocallyOfFiniteType sA₂] {e : ℕ}
    (hA₁ : topologicalKrullDim A₁ = e) (hA₂ : topologicalKrullDim A₂ = e) (m c : ℕ)
    (φ : FunctionFieldHom sA₁ sA₂)
    (b₁ : letI := functionFieldAlgebra sA₁
      Module.Basis Unit A₁.functionField (⋀[A₁.functionField]^e Ω[A₁.functionField⁄ℂ]))
    (w₂ : letI := functionFieldAlgebra sA₂; ⋀[A₂.functionField]^e Ω[A₂.functionField⁄ℂ])
    (c₁ : A₁.functionField) (c₂ : A₂.functionField) :
    letI := functionFieldAlgebra sA₁
    letI := functionFieldAlgebra sA₂
    pluriformPullback sA₁ sA₂ φ e m (c₂ • (formPow w₂ m : RationalPluriForms sA₂ e m)) =
      c₁ • (formPow (b₁ ()) m : RationalPluriForms sA₁ e m) →
    (c₁ ^ c • (formPow (b₁ ()) (c * m) : RationalPluriForms sA₁ e ((c * m : ℕ) : ℤ))) =
      pluriformPullback sA₁ sA₂ φ e ((c * m : ℕ) : ℤ)
        (c₂ ^ c • (formPow w₂ (c * m) : RationalPluriForms sA₂ e ((c * m : ℕ) : ℤ))) := by
  letI := functionFieldAlgebra sA₁
  letI := functionFieldAlgebra sA₂
  intro hadm
  rw [pluriformPullback_smul_formPow' hA₁ hA₂ φ w₂ m c₂] at hadm
  rw [pluriformPullback_smul_formPow' hA₁ hA₂ φ w₂ (c * m) (c₂ ^ c), map_pow φ c₂ c]
  exact (smul_formPow_pow_eq b₁ hadm c).symm

/-- From the admissible relation `σ̃^*(c₂ w₂^{⊗m}) = c₁ b₁^{⊗m}` along
`σ̃ = σ₁⁻¹ ∘ σ ∘ σ₂`, the `c`-th powers correspond along `σ ∘ σ₂` and `σ₁`. -/
private theorem pluriformPullback_pow_eq_of_liftsPow
    {A A' A₁ A₂ : Scheme.{0}} [IsIntegral A] [IsIntegral A'] [IsIntegral A₁] [IsIntegral A₂]
    {sA : A ⟶ Spec (.of ℂ)} {sA' : A' ⟶ Spec (.of ℂ)} {sA₁ : A₁ ⟶ Spec (.of ℂ)}
    {sA₂ : A₂ ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA']
    [LocallyOfFiniteType sA₁] [LocallyOfFiniteType sA₂] {e : ℕ}
    (hA : topologicalKrullDim A = e) (hA' : topologicalKrullDim A' = e)
    (hA₁ : topologicalKrullDim A₁ = e) (hA₂ : topologicalKrullDim A₂ = e) (m c : ℕ)
    (σ : FunctionFieldEquiv sA sA') (σ₂ : FunctionFieldEquiv sA' sA₂)
    (σ₁ : FunctionFieldEquiv sA sA₁)
    (b₁ : letI := functionFieldAlgebra sA₁
      Module.Basis Unit A₁.functionField (⋀[A₁.functionField]^e Ω[A₁.functionField⁄ℂ]))
    (w₂ : letI := functionFieldAlgebra sA₂; ⋀[A₂.functionField]^e Ω[A₂.functionField⁄ℂ])
    (c₁ : A₁.functionField) (c₂ : A₂.functionField) :
    letI := functionFieldAlgebra sA
    letI := functionFieldAlgebra sA'
    letI := functionFieldAlgebra sA₁
    letI := functionFieldAlgebra sA₂
    pluriformPullback sA₁ sA₂ (FunctionFieldEquiv.toHom sA₁ sA₂ (σ₂.trans (σ.trans σ₁.symm)))
        e m (c₂ • (formPow w₂ m : RationalPluriForms sA₂ e m)) =
      c₁ • (formPow (b₁ ()) m : RationalPluriForms sA₁ e m) →
    pluriformPullback sA sA' σ.toHom e ((c * m : ℕ) : ℤ)
        (pluriformPullback sA' sA₂ σ₂.toHom e ((c * m : ℕ) : ℤ)
          (c₂ ^ c • (formPow w₂ (c * m) : RationalPluriForms sA₂ e ((c * m : ℕ) : ℤ)))) =
      pluriformPullback sA sA₁ σ₁.toHom e ((c * m : ℕ) : ℤ)
        (c₁ ^ c • (formPow (b₁ ()) (c * m) : RationalPluriForms sA₁ e ((c * m : ℕ) : ℤ))) := by
  letI := functionFieldAlgebra sA
  letI := functionFieldAlgebra sA'
  letI := functionFieldAlgebra sA₁
  letI := functionFieldAlgebra sA₂
  intro hadm
  rw [smul_formPow_pow_eq_pluriformPullback_of_liftsPow hA₁ hA₂ m c _ b₁ w₂ c₁ c₂ hadm]
  exact pluriformPullback_pullback_eq_trans_of_liftsPow hA hA' hA₁ hA₂ _ σ σ₂ σ₁ _

include hdim hSf in
/-- **Lifts of an admissible floor system are preadmissible.** A system whose every component
lifts the `c`-th power of one admissible floor system is preadmissible. -/
private theorem mem_preadmissibleSections_of_liftsPow {m c : ℕ}
    (Rf : ResidueRestriction (fun j => jf j ≫ sX j.1) BSf 1 m)
    {u : ∀ j, logPluricanonicalSections (jf j ≫ sX j.1) 1 m (BSf j)}
    (hu : u ∈ admissibleSections Rf) (R : ResidueRestriction sX B 2 (c * m))
    (s : ∀ i, logPluricanonicalSections (sX i) 2 (c * m) (B i))
    (hs : ∀ i, LiftsPow sX B jf BSf i m c (c * m) (s i : RationalPluriForms (sX i) 2 ((c * m : ℕ) : ℤ)) u) :
    s ∈ preadmissibleSections R := by
  classical
  have hXi : ∀ i, Mori.IsProjectiveVariety ℂ (sX i) := R.setting.isProjectiveVariety
  haveI : ∀ i, LocallyOfFiniteType (sX i) := fun i =>
    (hXi i).toIsVariety.toLocallyOfFiniteType
  haveI : ∀ i, CompactSpace (X i) := fun i => by
    haveI := (hXi i).toIsVariety
    exact QuasiCompact.compactSpace_of_compactSpace (sX i)
  have hc0 : 0 < c := Nat.pos_of_mul_pos_right R.setting.pos
  have hd : ∀ i, topologicalKrullDim (X i) = ((1 + 1 : ℕ) : WithBot ℕ∞) := fun i => by
    rw [hdim i]; rfl
  have hread := toFun_eq_of_liftsPow hc0 Rf u R s hs
  intro i i' S S' ι ι' BS BS' F F' e h₁ h₂ hdS hdS' σ hσ
  haveI := F.isIntegral_stratum
  haveI := F.isNormal_stratum
  haveI := F.isLocallyNoetherian_stratum
  haveI := F'.isIntegral_stratum
  haveI := F'.isNormal_stratum
  haveI := F'.isLocallyNoetherian_stratum
  haveI : LocallyOfFiniteType (ι ≫ sX i) := F.isNormalVariety.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (ι' ≫ sX i') := F'.isNormalVariety.1.toLocallyOfFiniteType
  obtain ⟨P, S₁, ι₁, BS₁, F₁, ψ, hl₁, -, -, hrest₁⟩ :=
    exists_flagMatch (C := fun P => Sf ⟨i, P⟩) (j := fun P => jf ⟨i, P⟩)
      (BC := fun P => BSf ⟨i, P⟩) (hXi i) (hd i) (fun P => hSf ⟨i, P⟩)
      (isStratifiedSectionSetting_floors_of_liftsPow Rf i)
      (exists_isCanonicalDivisor_isQCartier_of_liftsPow R i) F h₁
  obtain ⟨P', S₂, ι₂, BS₂, F₂, ψ', hl₂, -, -, hrest₂⟩ :=
    exists_flagMatch (C := fun P => Sf ⟨i', P⟩) (j := fun P => jf ⟨i', P⟩)
      (BC := fun P => BSf ⟨i', P⟩) (hXi i') (hd i') (fun P => hSf ⟨i', P⟩)
      (isStratifiedSectionSetting_floors_of_liftsPow Rf i')
      (exists_isCanonicalDivisor_isQCartier_of_liftsPow R i') F' h₂
  haveI := F₁.isIntegral_stratum
  haveI := F₁.isNormal_stratum
  haveI := F₁.isLocallyNoetherian_stratum
  haveI := F₂.isIntegral_stratum
  haveI := F₂.isNormal_stratum
  haveI := F₂.isLocallyNoetherian_stratum
  haveI : LocallyOfFiniteType (ι₁ ≫ jf ⟨i, P⟩ ≫ sX i) :=
    F₁.isNormalVariety.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (ι₂ ≫ jf ⟨i', P'⟩ ≫ sX i') :=
    F₂.isNormalVariety.1.toLocallyOfFiniteType
  obtain ⟨σψ, -, hσψc, hres⟩ := hrest₁
  obtain ⟨σψ', -, hσψc', hres'⟩ := hrest₂
  -- the matched strata have dimension `e`
  have hdS₁ : topologicalKrullDim S₁ = e :=
    topologicalKrullDim_eq_of_liftsPow hd Rf e i P F₁ F hl₁ hdS
  have hdS₂ : topologicalKrullDim S₂ = e :=
    topologicalKrullDim_eq_of_liftsPow hd Rf e i' P' F₂ F' hl₂ hdS'
  letI := functionFieldAlgebra (ι₁ ≫ jf ⟨i, P⟩ ≫ sX i)
  letI := functionFieldAlgebra (ι₂ ≫ jf ⟨i', P'⟩ ≫ sX i')
  obtain ⟨b₁⟩ := exists_basis_topForms (sX := ι₁ ≫ jf ⟨i, P⟩ ≫ sX i) hdS₁
  obtain ⟨b₂⟩ := exists_basis_topForms (sX := ι₂ ≫ jf ⟨i', P'⟩ ≫ sX i') hdS₂
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : S₁.functionField, Rf.toFun ⟨i, P⟩ F₁ e (u ⟨i, P⟩) =
      c₁ • (formPow (b₁ ()) m : RationalPluriForms (ι₁ ≫ jf ⟨i, P⟩ ≫ sX i) e m) :=
    ⟨_, eq_repr_smul_formPow b₁ _⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : S₂.functionField, Rf.toFun ⟨i', P'⟩ F₂ e (u ⟨i', P'⟩) =
      c₂ • (formPow (b₂ ()) m : RationalPluriForms (ι₂ ≫ jf ⟨i', P'⟩ ≫ sX i') e m) :=
    ⟨_, eq_repr_smul_formPow b₂ _⟩
  beta_reduce
  rw [hread i P F₁ F e hdS₁ hdS σψ hres b₁ c₁ hc₁,
    hread i' P' F₂ F' e hdS₂ hdS' σψ' hres' b₂ c₂ hc₂]
  -- the crepant map `σ̃ = σψ⁻¹ ∘ σ ∘ σψ'` between the matched strata
  letI := functionFieldAlgebra (ι ≫ sX i)
  letI := functionFieldAlgebra (ι' ≫ sX i')
  have hσt : IsCrepantBirationalMap (ι₁ ≫ jf ⟨i, P⟩ ≫ sX i) (ι₂ ≫ jf ⟨i', P'⟩ ≫ sX i')
      BS₁ BS₂ (σψ'.trans (σ.trans σψ.symm)) :=
    (hσψc.symm.trans hσ).trans hσψc'
  have hadm := hu ⟨i, P⟩ ⟨i', P'⟩ F₁ F₂ e (Nat.zero_le _) (Nat.zero_le _) hdS₁ hdS₂ _ hσt
  beta_reduce at hadm
  rw [hc₁, hc₂] at hadm
  exact pluriformPullback_pow_eq_of_liftsPow hdS hdS' hdS₁ hdS₂ m c σ σψ' σψ b₁ (b₂ ()) c₁ c₂ hadm

end LiftsPowSection

/-! ### Floor curves, residues and the endpoint of the floor-lowering program -/

namespace FloorAdjunction

section EndpointPrelims

open TopologicalSpace

/-- The coheight of a point of a scheme is at most its dimension. -/
private theorem coheight_le_topologicalKrullDim {X : Scheme.{0}} (x : X) :
    (Order.coheight x : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  rw [topologicalKrullDim,
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := (X : Type)))]
  exact Order.coheight_le_krullDim _

section RayCopy

open MMP.Fourfold MMP.Mori MMP.Flips

/-- A morphism of projective complex varieties is projective. -/
private theorem isProjectiveMorphism_of_isProjectiveVariety {W V : Scheme.{0}}
    {sW : W ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hV : MMP.Mori.IsProjectiveVariety ℂ sV) (q : W ⟶ V) (hq : q ≫ sV = sW) :
    IsProjectiveMorphism q :=
  haveI : IsSeparated sV := hV.toIsSeparated
  IsProjectiveMorphism.of_comp q sV (hq ▸ hW.isProjective)

/-- Numerical classes of curves are separated by the degrees of invertible sheaves. -/
private theorem numericalCurveClasses_ext {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) {z z' : NumericalCurveClasses sX}
    (h : ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      NumericalCurveClasses.degree sX L z = NumericalCurveClasses.degree sX L z') : z = z' := by
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
  obtain ⟨Z', rfl⟩ := OneCycle.numericalClass_surjective sX z'
  rw [← sub_eq_zero, ← map_sub]
  refine (Submodule.Quotient.mk_eq_zero _).mpr (OneCycle.mem_numericallyTrivial.mpr fun L _ => ?_)
  have := h L
  simp only [NumericalCurveClasses.degree_numericalClass] at this
  rw [map_sub, this, sub_self]

/-- A relatively ample Cartier divisor has a relatively ample divisorial sheaf. -/
private theorem isRelativelyAmple_divisorialSheaf {X W : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ W} {L : Divisor X}
    (hL : MMP.Flips.IsRelativelyAmpleCartier f L) :
    haveI := hL.1.isInvertibleModule_divisorialSheaf
    MMP.Mori.IsRelativelyAmple f L.divisorialSheaf := fun y => by
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  exact ⟨V, hV, hyV, hL.2 V hV⟩

/-- **The curves contracted by a negative extremal contraction span one ray.** If `f : X ⟶ W` is
an `E`-negative extremal contraction (`ρ(X/W) = 1`, `-E` `f`-ample), then some curve `C₀`
contracted by `f` has nonzero class, and the class of every curve contracted by `f` is a positive
multiple of `[C₀]`. -/
private theorem exists_ray_of_isNegativeExtremalContraction {X W : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} {E : RDivisor X} {f : X ⟶ W}
    (hneg : IsNegativeExtremalContraction ℂ sX sW E f) :
    ∃ C₀ : ProperCurve sX, C₀.IsContractedBy f ∧
      OneCycle.numericalClass sX (C₀.cycle ℝ) ≠ 0 ∧
      ∀ C : ProperCurve sX, C.IsContractedBy f →
        ∃ c : ℝ, 0 < c ∧ c • OneCycle.numericalClass sX (C₀.cycle ℝ) =
          OneCycle.numericalClass sX (C.cycle ℝ) := by
  classical
  obtain ⟨m, r, L, hm1, -, hL, -⟩ := hneg.isRelativelyAntiAmple
  haveI := (hL ⟨0, hm1⟩).1.isInvertibleModule_divisorialSheaf
  obtain ⟨A', ⟨eA⟩⟩ :=
    MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf (L ⟨0, hm1⟩).divisorialSheaf
  have hrel := isRelativelyAmple_divisorialSheaf (hL ⟨0, hm1⟩)
  -- `A'` has positive degree on every contracted curve
  have hpos : ∀ C : ProperCurve sX, C.IsContractedBy f →
      0 < C.degree ℂ (MMP.CartierDivisor.sheaf A') := by
    intro C hC
    have := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _
      hrel C hC
    rwa [degreeOn_eq_of_iso ℂ sX C.ι C.dim_le eA] at this
  -- `(Z · 1 · E) = deg_Z 𝒪_X(E)` on the cycle of a curve
  have hdeg : ∀ (C : ProperCurve sX) (D : X.CartierDivisor),
      (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ D) =
        (C.degree ℂ (MMP.CartierDivisor.sheaf D) : ℝ) := by
    intro C D
    rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]
  -- the relative Néron–Severi space `N¹(X/W)` is a line
  set V := MMP.Flips.RelativeNumericalDivisorClasses sX f
  have hrank : Module.rank ℝ V = 1 := by
    have h := hneg.relativePicardNumber_eq_one
    rw [MMP.Flips.relativePicardNumber] at h
    exact Cardinal.toENat_eq_one.mp h
  have hfin : Module.finrank ℝ V = 1 := Module.finrank_eq_of_rank_eq (by rw [hrank]; rfl)
  haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hfin
  -- a contracted curve on which some Cartier divisor is nonzero
  obtain ⟨b, hb⟩ := exists_ne (0 : V)
  obtain ⟨D, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  have hD : D ∉ MMP.Flips.relativeNumericallyTrivialDivisors sX f := fun h =>
    hb ((Submodule.Quotient.mk_eq_zero _).mpr h)
  rw [MMP.Flips.mem_relativeNumericallyTrivialDivisors] at hD
  push Not at hD
  obtain ⟨C₀, hC₀, -⟩ := hD
  -- the class of `A'` spans `N¹(X/W)`
  set a : V := Submodule.Quotient.mk (KCartierDivisor.ofCartier ℝ A')
  have ha : a ≠ 0 := by
    intro h
    have h' := (MMP.Flips.mem_relativeNumericallyTrivialDivisors sX f).mp
      ((Submodule.Quotient.mk_eq_zero _).mp h) C₀ hC₀
    rw [hdeg] at h'
    exact (hpos C₀ hC₀).ne' (by exact_mod_cast h')
  have hspan := (finrank_eq_one_iff_of_nonzero' a ha).mp hfin
  -- every Cartier divisor is numerically a multiple of `A'` over `W`
  have hmul : ∀ D : X.CartierDivisor, ∃ μ : ℝ, ∀ C : ProperCurve sX, C.IsContractedBy f →
      (C.degree ℂ (MMP.CartierDivisor.sheaf D) : ℝ) =
        μ * C.degree ℂ (MMP.CartierDivisor.sheaf A') := by
    intro D
    obtain ⟨μ, hμ⟩ := hspan (Submodule.Quotient.mk (KCartierDivisor.ofCartier ℝ D))
    refine ⟨μ, fun C hC => ?_⟩
    have hmem : KCartierDivisor.ofCartier ℝ D - μ • KCartierDivisor.ofCartier ℝ A' ∈
        MMP.Flips.relativeNumericallyTrivialDivisors sX f := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub,
        Submodule.Quotient.mk_smul, ← hμ, sub_self]
    have h := (MMP.Flips.mem_relativeNumericallyTrivialDivisors sX f).mp hmem C hC
    rw [OneCycle.intersectionNumber, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, ← OneCycle.intersectionNumber, ← OneCycle.intersectionNumber,
      hdeg, hdeg, smul_eq_mul, sub_eq_zero] at h
    exact h
  have hC₀pos := hpos C₀ hC₀
  refine ⟨C₀, hC₀, fun h0 => ?_, fun C hC => ?_⟩
  · have := congrArg (NumericalCurveClasses.degree sX (MMP.CartierDivisor.sheaf A'))
      h0
    rw [map_zero, NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle] at this
    exact hC₀pos.ne' (by exact_mod_cast this)
  · have hCpos := hpos C hC
    refine ⟨(C.degree ℂ (MMP.CartierDivisor.sheaf A') : ℝ) /
      C₀.degree ℂ (MMP.CartierDivisor.sheaf A'), by positivity, ?_⟩
    refine numericalCurveClasses_ext sX fun M _ => ?_
    obtain ⟨D, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf M
    obtain ⟨μ, hμ⟩ := hmul D
    rw [map_smul, NumericalCurveClasses.degree_numericalClass,
      NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle,
      OneCycle.degree_cycle, smul_eq_mul]
    have e₀ : C₀.degree ℂ M = C₀.degree ℂ (MMP.CartierDivisor.sheaf D) :=
      degreeOn_eq_of_iso ℂ sX C₀.ι C₀.dim_le e
    have e₁ : C.degree ℂ M = C.degree ℂ (MMP.CartierDivisor.sheaf D) :=
      degreeOn_eq_of_iso ℂ sX C.ι C.dim_le e
    rw [e₀, e₁, hμ C₀ hC₀, hμ C hC]
    have : (C₀.degree ℂ (MMP.CartierDivisor.sheaf A') : ℝ) ≠ 0 := by
      exact_mod_cast hC₀pos.ne'
    field_simp

/-! ### Relative and absolute classes -/

section Natural

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {f : X ⟶ Y}

private theorem degree_relativeToAbsolute (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (z : RelativeNumericalCurveClasses sX f) :
    NumericalCurveClasses.degree sX L (relativeToAbsolute sX f z) =
      RelativeNumericalCurveClasses.degree sX f L z := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  rfl

private theorem continuous_relativeToAbsolute : Continuous (relativeToAbsolute sX f) :=
  continuous_iInf_rng.2 fun L => continuous_iInf_rng.2 fun h => continuous_induced_rng.2 <| by
    have := h
    have he : ⇑(NumericalCurveClasses.degree sX L) ∘ ⇑(relativeToAbsolute sX f) =
        RelativeNumericalCurveClasses.degree sX f L :=
      funext (degree_relativeToAbsolute L)
    rw [he]
    exact RelativeNumericalCurveClasses.continuous_degree sX f L

private theorem relativeToAbsolute_mem_coneOfCurves {z : RelativeNumericalCurveClasses sX f}
    (hz : z ∈ relativeConeOfCurves sX f) : relativeToAbsolute sX f z ∈ coneOfCurves sX := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨C, hC⟩, rfl⟩ := hx
    exact numericalClass_cycle_mem_coneOfCurves sX C
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [show a • x = (a : ℝ) • x from rfl, map_smul]
    exact (coneOfCurves sX).smul_mem a.2 hx

private theorem relativeToAbsolute_mem_closedConeOfCurves {z : RelativeNumericalCurveClasses sX f}
    (hz : z ∈ relativeClosedConeOfCurves sX f) :
    relativeToAbsolute sX f z ∈ closedConeOfCurves sX :=
  closure_mono (Set.image_subset_iff.2 fun _ hw => relativeToAbsolute_mem_coneOfCurves hw)
    (image_closure_subset_closure_image continuous_relativeToAbsolute ⟨z, hz, rfl⟩)

/-- The natural map `N₁(X/Y) → N₁(X)` is injective. -/
private theorem relativeToAbsolute_injective : Function.Injective (relativeToAbsolute sX f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (mem_relativeNumericallyTrivial.mpr ((Submodule.Quotient.mk_eq_zero _).mp hz))

end Natural

variable {k : Type} [Field k] {X : Scheme.{0}} in
/-- A ray `ℝ_{≥0} · v`, `v ≠ 0`, is closed in `N₁(X)` for the numerical topology. -/
private theorem isClosed_ray (sX : X ⟶ Spec (.of k)) {v : NumericalCurveClasses sX}
    (hv : v ≠ 0) : IsClosed {w : NumericalCurveClasses sX | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} := by
  obtain ⟨L₀, hL₀, hv₀⟩ : ∃ (L₀ : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf
      X.ringCatSheaf.2 L₀), NumericalCurveClasses.degree sX L₀ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (numericalCurveClasses_ext sX fun L _ => by rw [hcon L, map_zero])
  set a := NumericalCurveClasses.degree sX L₀ v
  have hS : {w : NumericalCurveClasses sX | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} =
      {w | 0 ≤ NumericalCurveClasses.degree sX L₀ w / a} ∩
        ⋂ (L : X.Modules) (h : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
          {w | NumericalCurveClasses.degree sX L w =
            NumericalCurveClasses.degree sX L₀ w / a * NumericalCurveClasses.degree sX L v} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hca : NumericalCurveClasses.degree sX L₀ (c • v) / a = c := by
        rw [map_smul, smul_eq_mul, mul_div_assoc, div_self hv₀, mul_one]
      refine ⟨by rw [hca]; exact hc, fun L _ => ?_⟩
      rw [hca, map_smul, smul_eq_mul]
    · rintro ⟨hc, hL⟩
      refine ⟨_, hc, numericalCurveClasses_ext sX fun L _ => ?_⟩
      rw [map_smul, smul_eq_mul, hL L]
  rw [hS]
  have hc₀ := NumericalCurveClasses.continuous_degree sX L₀
  refine (isClosed_le continuous_const (hc₀.div_const a)).inter
    (isClosed_iInter fun L => isClosed_iInter fun h => ?_)
  have hc := NumericalCurveClasses.continuous_degree sX L
  exact isClosed_eq hc ((hc₀.div_const a).mul continuous_const)

variable {k : Type} [Field k] {X Y : Scheme.{0}} in
/-- If every curve contracted by `f` has its class on the ray `ℝ≥0 · v`, then so does the image
in `N₁(X)` of every class of the closed relative cone `NE̅(X/Y)`. -/
private theorem relativeToAbsolute_mem_ray (sX : X ⟶ Spec (.of k)) (f : X ⟶ Y)
    {v : NumericalCurveClasses sX} (hv : v ≠ 0)
    (hcontr : ∀ C : ProperCurve sX, C.IsContractedBy f →
      ∃ c : ℝ, 0 ≤ c ∧ c • v = OneCycle.numericalClass sX (C.cycle ℝ))
    {z : RelativeNumericalCurveClasses sX f} (hz : z ∈ relativeClosedConeOfCurves sX f) :
    ∃ c : ℝ, 0 ≤ c ∧ c • v = relativeToAbsolute sX f z := by
  set ι := relativeToAbsolute sX f
  have hsub : (relativeConeOfCurves sX f : Set _) ⊆ ι ⁻¹' {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨C, hC⟩, rfl⟩ := hx
      exact hcontr C hC
    | zero => exact ⟨0, le_rfl, by rw [zero_smul, map_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hcx⟩ := hx
      obtain ⟨c', hc', hcy⟩ := hy
      exact ⟨c + c', add_nonneg hc hc', by rw [add_smul, hcx, hcy, map_add]⟩
    | smul a x _ hx =>
      obtain ⟨c, hc, hcx⟩ := hx
      exact ⟨a * c, mul_nonneg a.2 hc, by rw [mul_smul, hcx]; exact (map_smul ι (a : ℝ) x).symm⟩
  exact closure_minimal hsub
    ((isClosed_ray sX hv).preimage continuous_relativeToAbsolute) hz

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} in
/-- Every proper curve has a normalization, a curve of dimension at most one. -/
private theorem exists_curveNormalization (C : ProperCurve sX) :
    ∃ (N : Scheme.{0}) (ν : N ⟶ C.scheme) (_ : IsCurveNormalization ν),
      topologicalKrullDim N ≤ 1 := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  exact ⟨_, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le⟩

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X] in
/-- `L · C` is the degree of `𝒪_X(L)` along `C`. -/
private theorem isCartierIntersectionNumber_degreeOn (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    MMP.Flips.IsCartierIntersectionNumber k sX C L hL (L.degreeOn k sX C.ι C.dim_le hL) := by
  obtain ⟨N, ν, hν, hdim⟩ := exists_curveNormalization C
  refine ⟨N, ν, hν, hdim, ?_⟩
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (MMP.Fourfold.Oai4C1.Negativity.degreeOn_normalization C hν hdim _).symm

section RIntersection

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A presentation `D = ∑ rⱼ Lⱼ` computes `D · C = ∑ rⱼ deg_C 𝒪_X(Lⱼ)`. -/
private theorem isRIntersectionNumber_sum (C : ProperCurve sX) {D : RDivisor X} {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    MMP.Flips.IsRIntersectionNumber k sX D r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) :=
  ⟨hL, _, hD, fun j => isCartierIntersectionNumber_degreeOn C (L j) (hL j), rfl⟩

/-- **Real intersection numbers of `ℚ`-Cartier divisors.** For a `ℚ`-Cartier `D`, every value of
the real intersection number of `D` with a proper curve `C` (from any presentation of `D` by
Cartier divisors) is the intersection number `D · C`. -/
private theorem intersectionNumber_eq_of_isRIntersectionNumber {D : QDivisor X}
    (hD : D.IsQCartier) (C : ProperCurve sX) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    {x : ℝ} (hx : MMP.Flips.IsRIntersectionNumber k sX (QDivisor.toRDivisor D) r L C x) :
    ((D.intersectionNumber k sX C.ι C.dim_le hD : ℚ) : ℝ) = x := by
  set c := D.cartierIndex hD
  have hc : (0 : ℚ) < c := by exact_mod_cast QDivisor.cartierIndex_pos hD
  set M : Divisor X := (D.cartierIndexSMul hD : Divisor X)
  have hM : M.IsCartier := (D.cartierIndexSMul hD).2
  have hMD := QDivisor.toQDivisor_cartierIndexSMul D hD
  have hDR : QDivisor.toRDivisor D =
      ∑ _j : Fin 1, ((1 : ℝ) / c) • Divisor.toRDivisor M := by
    ext P
    have hP := congrArg (fun E => DivisorWithCoeffs.coeff E P) hMD
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at hP
    simp only [QDivisor.coeff_toRDivisor, Finset.univ_unique, Finset.sum_singleton,
      DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
    have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    have : ((M.coeff P : ℚ) : ℝ) = (c : ℝ) * (D.coeff P : ℝ) := by
      rw [hP]; push_cast; ring
    rw [show ((M.coeff P : ℤ) : ℝ) = ((M.coeff P : ℚ) : ℝ) by push_cast; rfl, this]
    field_simp
  have hy := isRIntersectionNumber_sum C (fun _ : Fin 1 => (1 : ℝ) / c) (fun _ => M)
    (fun _ => hM) hDR
  have heq := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ r L _ _ _ _ hx hy
  rw [heq, QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX C.ι C.dim_le D hD M hM hMD]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  push_cast
  ring

/-- **A `ℚ`-Cartier divisor whose negative is `f`-ample is negative on `f`-contracted curves.** -/
private theorem intersectionNumber_neg_of_isRelativelyAntiAmple [CompactSpace X] {V : Scheme.{0}}
    (f : X ⟶ V) {D : QDivisor X} (hD : D.IsQCartier)
    (hA : MMP.Flips.IsRelativelyAntiAmple f (QDivisor.toRDivisor D)) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) : D.intersectionNumber k sX C.ι C.dim_le hD < 0 := by
  obtain ⟨m, r, A, hm, hr, hAa, hLeq⟩ := hA
  have hAc : ∀ j, (A j).IsCartier := fun j => (hAa j).1
  have hLeq' : QDivisor.toRDivisor D = ∑ j, (-r j) • Divisor.toRDivisor (A j) := by
    have hL' : QDivisor.toRDivisor D = -(-QDivisor.toRDivisor D) := (neg_neg _).symm
    rw [hL', hLeq]
    simp [neg_smul, Finset.sum_neg_distrib]
  have hx := isRIntersectionNumber_sum C (fun j => -r j) A hAc hLeq'
  have hpos : ∀ j, (0 : ℝ) < (A j).degreeOn k sX C.ι C.dim_le (hAc j) := fun j => by
    haveI := (hAc j).isInvertibleModule_divisorialSheaf
    exact_mod_cast MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy
      f _ (isRelativelyAmple_divisorialSheaf (hAa j)) C hC
  have hsum : 0 < ∑ j, r j * ((A j).degreeOn k sX C.ι C.dim_le (hAc j) : ℝ) :=
    Finset.sum_pos (fun j _ => mul_pos (hr j) (hpos j)) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have heq := intersectionNumber_eq_of_isRIntersectionNumber hD C hx
  have : ((D.intersectionNumber k sX C.ι C.dim_le hD : ℚ) : ℝ) < 0 := by
    rw [heq]
    simp only [neg_mul, Finset.sum_neg_distrib]
    linarith
  exact_mod_cast this

end RIntersection

variable {X : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} in
/-- On `N₁(X/S)` the curve form is the absolute one composed with the natural map
`N₁(X/S) → N₁(X)`. -/
private theorem relativeCurveForm_eq_comp {S : Scheme.{0}} (f : X ⟶ S) (D : QDivisor X)
    (h : D.IsQCartier) :
    QDivisor.relativeCurveForm sX f D h =
      QDivisor.curveForm sX D h ∘ₗ relativeToAbsolute sX f := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun Z => ?_)
  simp only [QDivisor.relativeCurveForm, QDivisor.curveForm, Finsupp.sum, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun _ _ => rfl

/-- **The contraction of a negative extremal contraction over `Z` is the contraction of a
negative extremal ray of `NE̅(X/Z)`.** Let `f : X ⟶ W` be a `D`-negative extremal contraction of
projective varieties, with `W ⟶ Z` and `X` `ℚ`-factorial. Then the classes of the curves
contracted by `f` span an extremal ray `R` of `NE̅(X/Z)` which is `D`-negative, `f` is its
contraction over `Z`, and the image of `R` in `N₁(X)` is an extremal ray of `NE̅(X)` whose
contraction is `f`. -/
private theorem exists_isNegativeRelativeRayContraction {X W Z : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hW : MMP.Mori.IsProjectiveVariety ℂ sW) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hQ : IsQFactorial sX) {f : X ⟶ W} {gW : W ⟶ Z} {π : X ⟶ Z} (hfg : f ≫ gW = π)
    (hgW : gW ≫ sZ = sW) {D : QDivisor X}
    (hneg : IsNegativeExtremalContraction ℂ sX sW (QDivisor.toRDivisor D) f) :
    ∃ R : Set (RelativeNumericalCurveClasses sX π),
      IsNegativeRelativeRayContraction sX π sW D R f gW ∧
      IsContractionOfFace ℂ sX sW (relativeToAbsolute sX π '' R) f ∧
      IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
        (relativeToAbsolute sX π '' R) ∧
      ∃ C₀ : ProperCurve sX, C₀.IsContractedBy f ∧ relativeToAbsolute sX π '' R =
        {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C₀.cycle ℝ) = w} := by
  classical
  have hfW : f ≫ sW = sX := hneg.isContraction.comp_eq
  obtain ⟨C₀, hC₀, hne, hray⟩ := exists_ray_of_isNegativeExtremalContraction hneg
  set v₀ := OneCycle.numericalClass sX (C₀.cycle ℝ) with hv₀
  have hC₀π : C₀.IsContractedBy π := fun x hx => by
    rw [← hfg, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC₀ x hx]
  -- an ample invertible sheaf on `W`, whose pull-back detects the curves contracted by `f`
  obtain ⟨H, _, hH⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hW
  haveI : IsSeparated sW := hW.toIsSeparated
  haveI : LocallyOfFiniteType sW := hW.toIsVariety.toLocallyOfFiniteType
  have hkey : ∀ C : ProperCurve sX, C.IsContractedBy f ↔
      ∃ c : ℝ, 0 ≤ c ∧ c • v₀ = OneCycle.numericalClass sX (C.cycle ℝ) := by
    intro C
    refine ⟨fun hC => (hray C hC).imp fun c hc => ⟨hc.1.le, hc.2⟩, fun ⟨c, _, hc⟩ => ?_⟩
    refine MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero f hfW H hH C ?_
    have h0 := MMP.Mori.ProperCurve.degree_pullback_eq_zero_of_isContractedBy f hfW C₀ hC₀ H
    have := congrArg (NumericalCurveClasses.degree sX ((Scheme.Modules.pullback f).obj H)) hc
    rw [map_smul, NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle,
      NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle, h0] at this
    simp only [Int.cast_zero, smul_zero] at this
    exact_mod_cast this.symm
  -- the closed relative cone of `f` is the ray of `[C₀]`
  set vW := C₀.relativeClass f hC₀
  have hvW : relativeToAbsolute sX f vW = v₀ := rfl
  set RW := {w : RelativeNumericalCurveClasses sX f | ∃ c : ℝ, 0 ≤ c ∧ c • vW = w}
  have hNEW : (relativeClosedConeOfCurves sX f : Set _) = RW := by
    ext z
    refine ⟨fun hz => ?_, ?_⟩
    · obtain ⟨c, hc, hcz⟩ := relativeToAbsolute_mem_ray sX f hne (fun C hC => (hkey C).mp hC) hz
      exact ⟨c, hc, relativeToAbsolute_injective (by rw [map_smul, hvW, hcz])⟩
    · rintro ⟨c, hc, rfl⟩
      exact (relativeClosedConeOfCurves sX f).smul_mem hc
        (subset_closure (relativeClass_mem_relativeConeOfCurves hC₀))
  have hvW0 : vW ≠ 0 := fun h => hne (by rw [← hvW, h, map_zero])
  have hrayW : IsExtremalRay ℝ (relativeClosedConeOfCurves sX f : Set _) RW := by
    rw [hNEW]
    refine ⟨⟨subset_rfl, ⟨⟨0, le_rfl, zero_smul _ _⟩, ?_⟩, ?_, fun u hu w hw _ => ⟨hu, hw⟩⟩,
      vW, hvW0, rfl⟩
    · rintro _ ⟨c, hc, rfl⟩ a ha
      exact ⟨a * c, mul_nonneg ha.le hc, mul_smul _ _ _⟩
    · rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
      exact ⟨c + c', add_nonneg hc hc', add_smul _ _ _⟩
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sW := hW
  have hrayX := isExtremalRay_image_relativeToAbsolute sX sW f hfW hrayW
  set ray := {w : NumericalCurveClasses sX | ∃ c : ℝ, 0 ≤ c ∧ c • v₀ = w}
  have himW : relativeToAbsolute sX f '' RW = ray := by
    ext w
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, by rw [map_smul, hvW]⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c • vW, ⟨c, hc, rfl⟩, by rw [map_smul, hvW]⟩
  rw [himW] at hrayX
  -- the ray over `Z`
  set v := C₀.relativeClass π hC₀π
  have hv : relativeToAbsolute sX π v = v₀ := rfl
  set R := {w : RelativeNumericalCurveClasses sX π | ∃ c : ℝ, 0 ≤ c ∧ c • v = w}
  have hmemR : ∀ w, w ∈ R ↔ relativeToAbsolute sX π w ∈ ray := by
    intro w
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, by rw [map_smul, hv]⟩
    · rintro ⟨c, hc, hcw⟩
      exact ⟨c, hc, relativeToAbsolute_injective (by rw [map_smul, hv, hcw])⟩
  have himR : relativeToAbsolute sX π '' R = ray := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hmemR u).mp hu
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c • v, ⟨c, hc, rfl⟩, by rw [map_smul, hv]⟩
  have hv0 : v ≠ 0 := fun h => hne (by rw [← hv, h, map_zero])
  have hRray : IsExtremalRay ℝ (relativeClosedConeOfCurves sX π : Set _) R := by
    refine ⟨⟨?_, ⟨⟨0, le_rfl, zero_smul _ _⟩, ?_⟩, ?_, ?_⟩, v, hv0, rfl⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact (relativeClosedConeOfCurves sX π).smul_mem hc
        (subset_closure (relativeClass_mem_relativeConeOfCurves hC₀π))
    · rintro _ ⟨c, hc, rfl⟩ a ha
      exact ⟨a * c, mul_nonneg ha.le hc, mul_smul _ _ _⟩
    · rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
      exact ⟨c + c', add_nonneg hc hc', add_smul _ _ _⟩
    · intro u hu w hw huw
      rw [hmemR, map_add] at huw
      obtain ⟨h1, h2⟩ := hrayX.1.2.2.2 _ (relativeToAbsolute_mem_closedConeOfCurves hu) _
        (relativeToAbsolute_mem_closedConeOfCurves hw) huw
      exact ⟨(hmemR u).mpr h1, (hmemR w).mpr h2⟩
  refine ⟨R, ⟨⟨isQCartier_of_isQFactorial sX hQ D, hRray, fun u hu hu0 => ?_⟩,
    ⟨hRray.1, isProjectiveMorphism_of_isProjectiveVariety hW hZ gW hgW, hfg,
      hneg.isContraction.isIso_app, fun C hC => ?_⟩, hneg⟩,
    ⟨hX, hW, hfW, ?_, fun C => ?_, hneg.isContraction.isIso_app⟩, himR ▸ hrayX, C₀, hC₀, himR⟩
  · obtain ⟨c, hc, rfl⟩ := hu
    have hc0 : 0 < c := lt_of_le_of_ne hc (fun h => hu0 (by rw [← h, zero_smul]))
    rw [map_smul, smul_eq_mul, relativeCurveForm_eq_comp, LinearMap.comp_apply, hv,
      MMP.ProgramBaseChange.curveForm_numericalClass_cycle]
    have := intersectionNumber_neg_of_isRelativelyAntiAmple f (isQCartier_of_isQFactorial sX hQ D)
      hneg.isRelativelyAntiAmple C₀ hC₀
    exact mul_neg_of_pos_of_neg hc0 (by exact_mod_cast this)
  · rw [hmemR]
    exact hkey C
  · rw [himR]
    exact hrayX.1
  · rw [himR]
    exact hkey C

/-- Two morphisms to an affine scheme agreeing after a morphism `f` with `Γ(f)` bijective
agree. -/
private theorem eq_of_comp_eq_of_isIso_app_top {X W Y : Scheme.{0}} [IsAffine Y] (f : X ⟶ W)
    (hf : IsIso (f.app ⊤)) {a b : W ⟶ Y} (h : f ≫ a = f ≫ b) : a = b := by
  apply ext_of_isAffine
  have := congrArg Scheme.Hom.appTop h
  simp only [Scheme.Hom.comp_appTop] at this
  exact (cancel_mono (f.app ⊤)).mp this

/-- Pull-backs along `f' ≫ g` of invertible sheaves are pull-backs along `f'`, so
`f^* N¹(Z)_ℝ ⊆ f'^* N¹(Z')_ℝ` when `f = f' ≫ g`. -/
private theorem pullbackNumericalClasses_le_of_comp_eq {X Z Z' : Scheme.{0}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ))
    {f : X ⟶ Z} {f' : X ⟶ Z'} {g : Z' ⟶ Z} (h : f' ≫ g = f) :
    pullbackNumericalClasses sX f ≤ pullbackNumericalClasses sX f' := by
  refine Submodule.span_mono ?_
  rintro d ⟨E, M, hM, ⟨i⟩, rfl⟩
  exact ⟨E, (Scheme.Modules.pullback g).obj M,
    Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback g M,
    ⟨i ≪≫ (Scheme.Modules.pullbackCongr h.symm).app M ≪≫
      ((Scheme.Modules.pullbackComp f' g).app M).symm⟩, rfl⟩

/-- Relative ampleness over `Z'` along `f ≫ e`, for an isomorphism `e : Z ⟶ Z'`, is relative
ampleness over `Z` along `f`. -/
private theorem isRelativelyAmple_of_comp_isIso {X Z Z' : Scheme.{0}} (f : X ⟶ Z) (e : Z ⟶ Z')
    [IsIso e] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (h : MMP.Mori.IsRelativelyAmple (f ≫ e) L) : MMP.Mori.IsRelativelyAmple f L := by
  intro y
  obtain ⟨V, hV, hyV, hA⟩ := h (e y)
  exact ⟨e ⁻¹ᵁ V, hV.preimage_of_isIso e, hyV, hA⟩

/-- **Comparison with the contraction of the ray.** Two contractions `f : X ⟶ Z`,
`f' : X ⟶ Z'` of the same extremal ray `R` of a projective variety differ by an isomorphism of
targets over `ℂ`, so the projectivity of `Z'`, `ρ(X/Z') = 1` and the `f'`-ampleness of a divisor
pass to `f`. -/
private theorem contraction_data_of_isContractionOfRay {X Z Z' : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sZ' : Z' ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f) {f' : X ⟶ Z'}
    (hf' : IsContractionOfRay sX sZ' R f') (hZ' : MMP.Mori.IsProjectiveVariety ℂ sZ')
    (hρ : relativePicardNumberN1 sX f' = 1) {D : QDivisor X}
    (hamp : D.HasRelativelyAmpleMultiple f') :
    MMP.Mori.IsProjectiveVariety ℂ sZ ∧ relativePicardNumberN1 sX f = 1 ∧
      D.HasRelativelyAmpleMultiple f := by
  have hc : ∀ {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} {g : X ⟶ W},
      IsContractionOfRay sX sW R g → ∀ C : ProperCurve sX,
        OneCycle.numericalClass sX (C.cycle ℝ) ∈ R → C.IsContractedBy g :=
    fun hg C hC => (hg.isContractedBy_iff C).mpr hC
  obtain ⟨a, ha, -⟩ := existsUnique_comp_eq_of_isContractionOfRay hX hf'.isProjectiveMorphism
    hf'.comp_eq hR (hc hf') hf
  obtain ⟨b, hb, -⟩ := existsUnique_comp_eq_of_isContractionOfRay hX hf.isProjectiveMorphism
    hf.comp_eq hR (hc hf) hf'
  obtain ⟨c, -, hu⟩ := existsUnique_comp_eq_of_isContractionOfRay hX hf.isProjectiveMorphism
    hf.comp_eq hR (hc hf) hf
  obtain ⟨c', -, hu'⟩ := existsUnique_comp_eq_of_isContractionOfRay hX hf'.isProjectiveMorphism
    hf'.comp_eq hR (hc hf') hf'
  have hab : a ≫ b = 𝟙 Z :=
    (hu _ (show f ≫ a ≫ b = f by rw [← Category.assoc, ha, hb])).trans (hu _ (Category.comp_id f)).symm
  have hba : b ≫ a = 𝟙 Z' :=
    (hu' _ (show f' ≫ b ≫ a = f' by rw [← Category.assoc, hb, ha])).trans (hu' _ (Category.comp_id f')).symm
  have : IsIso a := ⟨⟨b, hab, hba⟩⟩
  have hsZ : sZ = a ≫ sZ' := by
    have : IsProper f := isProper_of_isProjectiveMorphism _ hf.isProjectiveMorphism
    have : IsIso f.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ f.c fun U => hf.isIso_app U.unop
    obtain ⟨t, -, hs⟩ := MMP.existsUnique_comp_eq_of_isIso_c f sX
      fun _ _ _ => Subsingleton.elim _ _
    exact (hs _ hf.comp_eq).trans (hs _ (show f ≫ a ≫ sZ' = sX by rw [← Category.assoc, ha, hf'.comp_eq])).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [MMP.Mori.isProjectiveVariety_iff]
    refine ⟨hf.isNormalVariety_target.1, ?_⟩
    obtain ⟨n, i, hi, hif⟩ := ((MMP.Mori.isProjectiveVariety_iff ℂ sZ').mp hZ').2
    exact ⟨n, a ≫ i, inferInstance, by rw [hsZ, Category.assoc, hif]⟩
  · rw [← hρ, relativePicardNumberN1, relativePicardNumberN1,
      le_antisymm (pullbackNumericalClasses_le_of_comp_eq sX ha)
        (pullbackNumericalClasses_le_of_comp_eq sX
          (show f' ≫ inv a = f by rw [← ha, Category.assoc, IsIso.hom_inv_id, Category.comp_id]))]
  · obtain ⟨m, hm, L, hL, hLD, hLa⟩ := hamp
    refine ⟨m, hm, L, hL, hLD, ?_⟩
    have := hL.isInvertibleModule_divisorialSheaf
    exact isRelativelyAmple_of_comp_isIso f a _ (ha ▸ hLa)

end RayCopy

section Composite

open MMP.Fourfold MMP.Mori MMP.Flips

/-- **Preimages along maps with connected fibres.** Let `q` be a closed map sending a closed set
`F` onto `G`, all of whose fibres in `F` are preconnected. The part of `F` over a preconnected
subset of `G` is preconnected. -/
private theorem isPreconnected_preimage_inter {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y]
    {q : X → Y} (hq : IsClosedMap q) {F : Set X} (hF : IsClosed F) {G : Set Y}
    (hFG : q '' F = G) (hfib : ∀ y ∈ G, _root_.IsPreconnected (q ⁻¹' {y} ∩ F)) {W : Set Y}
    (hWG : W ⊆ G) (hW : _root_.IsPreconnected W) : _root_.IsPreconnected (q ⁻¹' W ∩ F) := by
  rw [isPreconnected_closed_iff]
  intro t t' ht ht' hcov ⟨a, ha, hat⟩ ⟨b, hb, hbt'⟩
  set W₁ := q '' (q ⁻¹' W ∩ F ∩ t)
  set W₂ := q '' (q ⁻¹' W ∩ F ∩ t')
  -- `W₁ ∩ W` and `W₂ ∩ W` are relatively closed and cover `W`
  have hW₁ : IsClosed (q '' (F ∩ t)) := hq _ (hF.inter ht)
  have hW₂ : IsClosed (q '' (F ∩ t')) := hq _ (hF.inter ht')
  have hcovW : W ⊆ q '' (F ∩ t) ∪ q '' (F ∩ t') := by
    intro y hy
    obtain ⟨x, hxF, rfl⟩ := hFG.symm ▸ hWG hy
    rcases hcov ⟨hy, hxF⟩ with h | h
    · exact Or.inl ⟨x, ⟨hxF, h⟩, rfl⟩
    · exact Or.inr ⟨x, ⟨hxF, h⟩, rfl⟩
  obtain ⟨y, hyW, ⟨x₁, ⟨hx₁F, hx₁t⟩, hx₁⟩, ⟨x₂, ⟨hx₂F, hx₂t⟩, hx₂⟩⟩ :=
    (isPreconnected_closed_iff.mp hW) _ _ hW₁ hW₂ hcovW ⟨q a, ha.1, a, ⟨ha.2, hat⟩, rfl⟩
      ⟨q b, hb.1, b, ⟨hb.2, hbt'⟩, rfl⟩
  have hfy := hfib y (hWG hyW)
  have hsub : q ⁻¹' {y} ∩ F ⊆ q ⁻¹' W ∩ F := fun z hz => ⟨by
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz ⊢; rw [hz.1]; exact hyW, hz.2⟩
  obtain ⟨z, hz, hzt, hzt'⟩ := (isPreconnected_closed_iff.mp hfy) t t' ht ht'
    (hsub.trans hcov) ⟨x₁, ⟨hx₁, hx₁F⟩, hx₁t⟩ ⟨x₂, ⟨hx₂, hx₂F⟩, hx₂t⟩
  exact ⟨z, hsub hz, hzt, hzt'⟩

/-- The reduced floor `⌊D⌋` as a union of supports, indexed by the prime divisors with nonzero
round-down coefficient. -/
private abbrev floorUnion {X : Scheme.{0}} (D : QDivisor X) : Set X :=
  ⋃ E : {E : MMP.Mori.PrimeDivisor X // ⌊D.coeff E⌋ ≠ 0}, (E.1.support : Set X)

private theorem floorUnion_eq {X : Scheme.{0}} (D : QDivisor X) :
    floorUnion D = ⋃ E ∈ D.roundDown.support, (E.support : Set X) := by
  ext x
  simp only [floorUnion, Set.mem_iUnion, Finsupp.mem_support_iff, exists_prop, Subtype.exists]
  constructor
  · rintro ⟨E, hE, hx⟩
    exact ⟨E, by rwa [← DivisorWithCoeffs.coeff_roundDown] at hE, hx⟩
  · rintro ⟨E, hE, hx⟩
    exact ⟨E, by rwa [← DivisorWithCoeffs.coeff_roundDown], hx⟩

private theorem isClosed_floorUnion {X : Scheme.{0}} (D : QDivisor X) :
    IsClosed (floorUnion D) := by
  rw [floorUnion_eq]
  exact (D.roundDown.support.finite_toSet).isClosed_biUnion fun E _ => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure

/-- **A floor map with connected fibres.** If every pair of reduced closed subschemes on closed
sets `F ⊆ X`, `F' ⊆ X'` receives a morphism over `q` with connected fibres, then `q` maps `F` onto
`F'` and the part of `F` over each point of `F'` is connected. -/
private theorem image_eq_and_isPreconnected_of_floorMap {X X' : Scheme.{0}} (q : X ⟶ X')
    {F : Set X} {F' : Set X'} (hF : IsClosed F) (hF' : IsClosed F')
    (H : ∀ (T T' : Scheme.{0}) (ι : T ⟶ X) (ι' : T' ⟶ X') [IsClosedImmersion ι] [IsReduced T]
      [IsClosedImmersion ι'] [IsReduced T'], Set.range ι.base = F → Set.range ι'.base = F' →
      (∃ h : T ⟶ T', h ≫ ι' = ι ≫ q) ∧ ∀ h : T ⟶ T', h ≫ ι' = ι ≫ q →
        (∀ U : T'.Opens, IsIso (h.app U)) ∧ ∀ t : T', _root_.IsConnected (h.base ⁻¹' {t})) :
    q.base '' F = F' ∧ ∀ y ∈ F', _root_.IsPreconnected (q.base ⁻¹' {y} ∩ F) := by
  let Z : TopologicalSpace.Closeds X := ⟨F, hF⟩
  let Z' : TopologicalSpace.Closeds X' := ⟨F', hF'⟩
  let ι := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  let ι' := (Scheme.IdealSheafData.vanishingIdeal Z').subschemeι
  have hι : Set.range ι.base = F := Scheme.IdealSheafData.range_subschemeι_vanishingIdeal Z
  have hι' : Set.range ι'.base = F' := Scheme.IdealSheafData.range_subschemeι_vanishingIdeal Z'
  obtain ⟨⟨h, hh⟩, hall⟩ := H _ _ ι ι' hι hι'
  obtain ⟨-, hconn⟩ := hall h hh
  have hpt : ∀ a, ι'.base (h.base a) = q.base (ι.base a) := fun a => by
    have := congrArg (fun φ => φ.base a) hh
    simpa using this
  refine ⟨?_, fun y hy => ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hι] at hx
      obtain ⟨a, rfl⟩ := hx
      rw [← hpt, ← hι']
      exact ⟨_, rfl⟩
    · intro hy
      rw [← hι'] at hy
      obtain ⟨t, rfl⟩ := hy
      obtain ⟨a, ha⟩ := (hconn t).nonempty
      refine ⟨ι.base a, hι ▸ ⟨a, rfl⟩, ?_⟩
      rw [← hpt]
      exact congrArg ι'.base ha
  · rw [← hι'] at hy
    obtain ⟨t, rfl⟩ := hy
    have : q.base ⁻¹' {ι'.base t} ∩ F = ι.base '' (h.base ⁻¹' {t}) := by
      ext x
      constructor
      · rintro ⟨hx, hxF⟩
        rw [← hι] at hxF
        obtain ⟨a, rfl⟩ := hxF
        refine ⟨a, ?_, rfl⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
        rw [← hpt] at hx
        exact ι'.isClosedEmbedding.injective hx
      · rintro ⟨a, ha, rfl⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha ⊢
        exact ⟨show q.base (ι.base a) = ι'.base t by rw [← hpt, ha], hι ▸ ⟨a, rfl⟩⟩
    rw [this]
    exact (hconn t).isPreconnected.image _ ι.continuous.continuousOn

private theorem compHom_compHom {X Y Z W : Scheme.{0}} (f : X.RationalMap Y) (g : Y ⟶ Z)
    (h : Z ⟶ W) : (f.compHom g).compHom h = f.compHom (g ≫ h) := by
  induction f using Quotient.inductionOn
  rfl

private theorem compHom_id {X Y : Scheme.{0}} (f : X.RationalMap Y) : f.compHom (𝟙 Y) = f := by
  induction f using Quotient.inductionOn with
  | h f =>
    change (f.compHom (𝟙 Y)).toRationalMap = f.toRationalMap
    congr 1

private theorem toRationalMap_compHom {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f.toRationalMap.compHom g = (f ≫ g).toRationalMap := by
  rfl

/-- A rational map `φ` over `Z` into the isomorphic `fp : X' ⟶ Z` is the morphism `f ≫ fp⁻¹`. -/
private theorem eq_toRationalMap_of_isOver {X X' Z : Scheme.{0}} (φ : X.RationalMap X')
    (f : X ⟶ Z) (fp : X' ⟶ Z) [IsIso fp] (h : φ.compHom fp = f.toRationalMap) :
    φ = (f ≫ inv fp).toRationalMap := by
  rw [← toRationalMap_compHom, ← h, compHom_compHom, IsIso.hom_inv_id, compHom_id]

end Composite

namespace FL

section FLInter

open MMP.Fourfold MMP.Mori MMP.Flips

private theorem principalDivisor_zpow {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (φ : (RationalFunctions X)ˣ) (n : ℤ) :
    MMP.Mori.principalDivisor (φ ^ n) = n • MMP.Mori.principalDivisor φ := by
  ext D
  simp [PrimeDivisor.ord_zpow]

/-- Intersection numbers with a proper curve depend only on the `ℚ`-linear equivalence class. -/
private theorem intersectionNumber_eq_of_qLinearlyEquivalent {X C : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] (i : C ⟶ X) [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)
    {D₁ D₂ : QDivisor X} (hD₁ : D₁.IsQCartier) (hD₂ : D₂.IsQCartier)
    (h : D₁.QLinearlyEquivalent D₂) :
    D₁.intersectionNumber ℂ sX i hdim hD₁ = D₂.intersectionNumber ℂ sX i hdim hD₂ := by
  obtain ⟨m, hm, φ, hφ⟩ := h
  have ha := QDivisor.cartierIndex_pos hD₂
  obtain ⟨Da, hDa, hDac⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hD₂
  set a := D₂.cartierIndex hD₂
  have hN : 0 < m * a := Nat.mul_pos hm ha
  set ψ := φ ^ (a : ℤ)
  have hE2 : Divisor.toQDivisor ((m : ℤ) • Da) = (((m * a : ℕ)) : ℤ) • D₂ := by
    rw [map_zsmul, hDa, smul_smul]
    push_cast
    ring_nf
  have hE1 : Divisor.toQDivisor ((m : ℤ) • Da + MMP.Mori.principalDivisor ψ) =
      (((m * a : ℕ)) : ℤ) • D₁ := by
    rw [map_add, hE2, principalDivisor_zpow, map_zsmul, ← hφ, smul_smul]
    have : (((m * a : ℕ)) : ℤ) = (a : ℤ) * (m : ℤ) := by push_cast; ring
    rw [this, smul_sub]
    abel
  have hc1 := (hDac.zsmul (m : ℤ)).add (Divisor.isCartier_principalDivisor ψ)
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sX i hdim D₁ hD₁ hN _ hc1 hE1,
    QDivisor.intersectionNumber_eq_of_smul ℂ sX i hdim D₂ hD₂ hN _ (hDac.zsmul _) hE2,
    Divisor.degreeOn_add ℂ sX i hdim _ _ (hDac.zsmul _) (Divisor.isCartier_principalDivisor ψ),
    MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX i hdim
      (Divisor.isCartier_principalDivisor ψ) ⟨ψ, by rw [sub_zero]⟩]
  simp

end FLInter

end FL

section NumTrivial

open MMP.Fourfold MMP.Mori MMP.Flips

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier: each prime divisor `P` has a
Cartier multiple `m_P P`, and `D = ∑ (D_P / m_P) (m_P P)`. -/
private theorem isCartierCombination_of_isQFactorial {Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    (hY : IsQFactorial sY) (D : RDivisor Y) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor Y), (∀ j, (L j).IsCartier) ∧
      D = ∑ j, r j • Divisor.toRDivisor (L j) := by
  classical
  choose m hm hc using fun P : MMP.Mori.PrimeDivisor Y => hY.2 (Finsupp.single P 1)
  let e := D.support.equivFin
  refine ⟨_, fun j => D (e.symm j) / m (e.symm j),
    fun j => ((m (e.symm j) : ℕ) : ℤ) • Finsupp.single (e.symm j : MMP.Mori.PrimeDivisor Y) 1,
    fun j => hc _, ?_⟩
  have hterm : ∀ P : MMP.Mori.PrimeDivisor Y, (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor Y)) =
        Finsupp.single P (D P) := by
    intro P
    ext Q
    have hm0 : (m P : ℝ) ≠ 0 := by exact_mod_cast (hm P).ne'
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
    by_cases hQ : P = Q
    · subst hQ
      simp [DivisorWithCoeffs.coeff_apply, div_mul_cancel₀ _ hm0]
    · simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, hQ]
  rw [Equiv.sum_comp e.symm (fun P : D.support => (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single (P : MMP.Mori.PrimeDivisor Y) 1 :
        Divisor Y)))]
  rw [Finset.sum_coe_sort D.support (fun P => (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor Y)))]
  simp_rw [hterm]
  exact (Finsupp.sum_single D).symm

end NumTrivial

section Generators

open MMP.Mori MMP.Fourfold

/-- Rational pluriforms of a fixed degree on a variety form a line over the function field:
every form is a multiple of a given nonzero one. -/
private theorem exists_eq_smul_of_ne_zero {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [LocallyOfFiniteType sX] {d : ℕ} (hdim : topologicalKrullDim X = d) {m : ℤ}
    {u : RationalPluriForms sX d m} (hu : u ≠ 0) (w : RationalPluriForms sX d m) :
    ∃ h : X.functionField, w = h • u := by
  let := functionFieldAlgebra sX
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hdim
  let B := ZTensorPower.basis b m
  have hu' := basis_unit_repr_smul B u
  have hw' := basis_unit_repr_smul B w
  have hru : B.repr u () ≠ 0 := by
    intro h; rw [h, zero_smul] at hu'; exact hu hu'.symm
  refine ⟨B.repr w () / B.repr u (), ?_⟩
  have key : (B.repr w () / B.repr u ()) • (B.repr u () • B ()) = B.repr w () • B () := by
    rw [smul_smul, div_mul_cancel₀ _ hru]
  rw [hu'] at key
  exact hw'.symm.trans key.symm

/-- The pull-back of rational forms is semilinear along `q^* : k(V) → k(S)`. -/
private theorem pullbackRationalPluriForms_smul' {S V : Scheme.{0}} [IsIntegral S] [IsIntegral V]
    {sV : V ⟶ Spec (.of ℂ)} (q : S ⟶ V) [IsDominant q] {d : ℕ} {m : ℤ}
    (a : V.functionField) (τ : RationalPluriForms sV d m) :
    pullbackRationalPluriForms sV q (a • τ) =
      functionFieldMap q a • pullbackRationalPluriForms sV q τ := by
  let := functionFieldAlgebra sV
  let := functionFieldAlgebra (q ≫ sV)
  let := functionFieldMapAlgebra q
  have := isScalarTower_functionFieldMap sV q
  exact pullbackForms_smul (K := V.functionField) (K' := S.functionField) (m := m) a τ

/-- The pull-back of rational forms is multiplicative. -/
private theorem pullbackRationalPluriForms_mul {S V : Scheme.{0}} [IsIntegral S] [IsIntegral V]
    {sV : V ⟶ Spec (.of ℂ)} (q : S ⟶ V) [IsDominant q] {d a b : ℕ}
    (τ : RationalPluriForms sV d a) (τ' : RationalPluriForms sV d b) :
    pullbackRationalPluriForms sV q (RationalPluriForms.mul sV d a b τ τ') =
      RationalPluriForms.mul (q ≫ sV) d a b (pullbackRationalPluriForms sV q τ)
        (pullbackRationalPluriForms sV q τ') := by
  let := functionFieldAlgebra sV
  let := functionFieldAlgebra (q ≫ sV)
  let := functionFieldMapAlgebra q
  have := isScalarTower_functionFieldMap sV q
  exact pullbackForms_pluriFormsMul (K := V.functionField) (K' := S.functionField) τ τ'

end Generators

end EndpointPrelims

open MMP MMP.Fourfold
open MMP.Mori (Divisor QDivisor RationalPluriForms)

/-- A coefficient in `[0, 1]` with nonzero round-down is one. -/
private theorem eq_one_of_floor_ne_zero {x : ℚ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (h : ⌊x⌋ ≠ 0) :
    x = 1 :=
  h1.eq_or_lt.resolve_right fun h1 => h (Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩)

/-- A scheme of dimension zero has no prime divisors. -/
private theorem isEmpty_primeDivisor_of_topologicalKrullDim_eq_zero {T : Scheme.{0}}
    (h : topologicalKrullDim T = 0) :
    IsEmpty (Mori.PrimeDivisor T) := ⟨fun P => by
  have h1 : (Order.coheight P.genericPoint : WithBot ℕ∞) ≤ topologicalKrullDim T :=
    coheight_le_topologicalKrullDim _
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, h] at h1
  exact absurd h1 (by decide)⟩

/-- On a normal variety of dimension zero no valuation has a log discrepancy: a variety
birational to it has dimension zero, hence no prime divisors. -/
private theorem not_hasLogDiscrepancy_of_topologicalKrullDim_eq_zero {T : Scheme.{0}}
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    {sT : T ⟶ Spec (.of ℂ)} (hT : Mori.IsNormalVariety ℂ sT) (h0 : topologicalKrullDim T = 0)
    (BT : QDivisor T) (v : Valuation T.functionField ℤᵐ⁰) (a : ℝ) :
    ¬ HasLogDiscrepancy sT BT v a := by
  rintro ⟨n, D, -, -⟩
  haveI : MMP.Mori.IsVariety ℂ sT := hT.1
  haveI : MMP.Mori.IsVariety ℂ (D.f ≫ sT) := D.isNormalVariety.1
  have hd := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sT (D.f ≫ sT)
    D.isBirationalMorphism
  exact (isEmpty_primeDivisor_of_topologicalKrullDim_eq_zero (hd ▸ h0)).elim D.E

/-- The function field of a variety of dimension zero over `ℂ` is `ℂ`. -/
private theorem bijective_algebraMap_of_topologicalKrullDim_eq_zero {T : Scheme.{0}}
    [IsIntegral T] {sT : T ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sT] (h0 : topologicalKrullDim T = 0) :
    Function.Bijective (letI := MMP.Mori.functionFieldAlgebra sT;
      algebraMap ℂ T.functionField) := by
  letI := MMP.Mori.functionFieldAlgebra sT
  have h := topologicalKrullDim_eq_toNat_trdeg sT
  rw [h0] at h
  have h' : (Algebra.trdeg ℂ T.functionField).toNat = 0 := by exact_mod_cast h.symm
  have := MMP.Mori.essFiniteType_functionField (sX := sT)
  have h3 : Algebra.trdeg ℂ T.functionField = 0 := by
    rw [← Cardinal.cast_toNat_of_lt_aleph0 (trdeg_lt_aleph0 (K := ℂ) (L := T.functionField)), h']
    rfl
  have : Algebra.IsAlgebraic ℂ T.functionField := trdeg_eq_zero_iff.mp h3
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- **Points are crepant.** Any two normal varieties of dimension zero over `ℂ`, with any
boundaries, are related by a crepant birational map. -/
private theorem exists_isCrepantBirationalMap_of_topologicalKrullDim_eq_zero {T T' : Scheme.{0}}
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsIntegral T'] [IsLocallyNoetherian T'] [IsNormal T']
    {sT : T ⟶ Spec (.of ℂ)} {sT' : T' ⟶ Spec (.of ℂ)} (hT : Mori.IsNormalVariety ℂ sT)
    (hT' : Mori.IsNormalVariety ℂ sT') (h0 : topologicalKrullDim T = 0)
    (h0' : topologicalKrullDim T' = 0) (BT : QDivisor T) (BT' : QDivisor T') :
    ∃ σ : FunctionFieldEquiv sT sT', IsCrepantBirationalMap sT sT' BT BT' σ := by
  letI := MMP.Mori.functionFieldAlgebra sT
  letI := MMP.Mori.functionFieldAlgebra sT'
  haveI : LocallyOfFiniteType sT := hT.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sT' := hT'.1.toLocallyOfFiniteType
  let e := AlgEquiv.ofBijective (Algebra.ofId ℂ T.functionField)
    (bijective_algebraMap_of_topologicalKrullDim_eq_zero h0)
  let e' := AlgEquiv.ofBijective (Algebra.ofId ℂ T'.functionField)
    (bijective_algebraMap_of_topologicalKrullDim_eq_zero h0')
  refine ⟨e'.symm.trans e, fun v a => ?_⟩
  exact iff_of_false (not_hasLogDiscrepancy_of_topologicalKrullDim_eq_zero hT h0 BT v a)
    (not_hasLogDiscrepancy_of_topologicalKrullDim_eq_zero hT' h0' BT' _ a)
/-- `⋀⁰ M` is spanned by the empty product. -/
private theorem span_ιMulti_zero (K M : Type) [Field K] [AddCommGroup M] [Module K M] :
    Submodule.span K {exteriorPower.ιMulti K 0 (Fin.elim0 : Fin 0 → M)} = ⊤ := by
  rw [← exteriorPower.ιMulti_span (R := K) (M := M) (n := 0)]
  congr 1
  ext x
  simp only [Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro rfl; exact ⟨_, rfl⟩
  · rintro ⟨f, rfl⟩; congr 1; funext i; exact i.elim0

/-- The empty product in `⋀⁰ M` is nonzero. -/
private theorem ιMulti_zero_ne_zero (K M : Type) [Field K] [AddCommGroup M] [Module K M] :
    exteriorPower.ιMulti K 0 (Fin.elim0 : Fin 0 → M) ≠ 0 := by
  intro h
  have h1 := span_ιMulti_zero K M
  rw [h, Submodule.span_singleton_eq_bot.mpr rfl] at h1
  have : Nontrivial (⋀[K]^0 M) := (exteriorPower.zeroEquiv K M).nontrivial
  exact bot_ne_top h1

/-- **Pull-back of constant degree-zero forms.** Pluriform pull-back along a `ℂ`-isomorphism of
function fields fixes the constant forms `c · 1^{⊗m}` of degree zero. -/
private theorem pluriformPullback_smul_formPow_ιMulti_zero {T T' : Scheme.{0}} [IsIntegral T]
    [IsIntegral T']
    {sT : T ⟶ Spec (.of ℂ)} {sT' : T' ⟶ Spec (.of ℂ)} (σ : FunctionFieldEquiv sT sT') (m : ℕ)
    (c : ℂ) :
    letI := MMP.Mori.functionFieldAlgebra sT
    letI := MMP.Mori.functionFieldAlgebra sT'
    pluriformPullback sT sT' σ.toHom 0 m (algebraMap ℂ T'.functionField c •
      (formPow (k := ℂ) (exteriorPower.ιMulti T'.functionField 0 Fin.elim0) m :
        RationalPluriForms sT' 0 m)) =
    algebraMap ℂ T.functionField c •
      (formPow (k := ℂ) (exteriorPower.ιMulti T.functionField 0 Fin.elim0) m :
        RationalPluriForms sT 0 m) := by
  letI := MMP.Mori.functionFieldAlgebra sT
  letI := MMP.Mori.functionFieldAlgebra sT'
  letI : Algebra T'.functionField T.functionField := σ.toHom.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ T'.functionField T.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (σ.toHom.commutes c).symm
  have htop : MMP.Mori.topFormsMap ℂ T'.functionField T.functionField 0
      (exteriorPower.ιMulti T'.functionField 0 Fin.elim0) =
      exteriorPower.ιMulti T.functionField 0 Fin.elim0 := by
    rw [MMP.Mori.topFormsMap_ιMulti]
    congr 1
    funext i; exact i.elim0
  have hgen : MMP.Mori.IsPullbackGenerator T.functionField
      (exteriorPower.ιMulti T'.functionField 0 (Fin.elim0 : Fin 0 → Ω[T'.functionField⁄ℂ])) := by
    refine ⟨span_ιMulti_zero _ _, ?_, ?_⟩
    · rw [htop]; exact span_ιMulti_zero _ _
    · rw [htop]; exact ιMulti_zero_ne_zero _ _
  have := pluriformPullback_smul_formPow (sX := sT) (sX' := sT') σ.toHom hgen m
    (algebraMap ℂ T'.functionField c)
  rw [this, htop]
  congr 1
  exact σ.toHom.commutes c
/-- The constant degree-zero form `1^{⊗m}` is nonzero. -/
private theorem formPow_ιMulti_zero_ne_zero (K : Type) [Field K] [Algebra ℂ K] (m : ℕ) :
    (formPow (k := ℂ) (exteriorPower.ιMulti K 0 (Fin.elim0 : Fin 0 → Ω[K⁄ℂ])) m :
      MMP.Mori.PluriForms ℂ K 0 m) ≠ 0 := by
  have h := Module.Basis.ne_zero (MMP.Mori.ZTensorPower.basis
    (MMP.Mori.basisOfSpanSingleton (span_ιMulti_zero K Ω[K⁄ℂ]) (ιMulti_zero_ne_zero K Ω[K⁄ℂ]))
    (m : ℤ)) ()
  rwa [MMP.Fourfold.ZTensorPower.basis_natCast (k := ℂ), MMP.Mori.basisOfSpanSingleton_apply] at h

section KM550

open MMP.Mori MMP.Flips

section Step

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {Y : Scheme.{0}}
  {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {BY : QDivisor Y}

/-! ### A rational top form with a simple pole along a normal prime divisor -/

/-- The top exterior power of a linearly independent family is nonzero. -/
private theorem ιMulti_ne_zero_of_linearIndependent {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] {n : ℕ} {v : Fin n → W} (hv : LinearIndependent K v) :
    exteriorPower.ιMulti K n v ≠ 0 := by
  classical
  let b := Module.Basis.span hv
  have hb : (fun i => ((b i : Submodule.span K (Set.range v)) : W)) = v := by
    funext i; simp [b, Module.Basis.span_apply]
  have hmap : exteriorPower.map n (Submodule.span K (Set.range v)).subtype
      (exteriorPower.ιMulti K n b) = exteriorPower.ιMulti K n v := by
    rw [exteriorPower.map_apply_ιMulti]
    exact congrArg _ hb
  intro h0
  have h1 : exteriorPower.ιMulti K n b = 0 := by
    apply exteriorPower.map_injective_field (n := n) (Submodule.injective_subtype _)
    rw [hmap, h0, map_zero]
  have h2 := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) h1
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_zero, b.det_self] at h2
  exact one_ne_zero h2

/-- A nonzero element of the maximal ideal of the local ring at the generic point of a prime
divisor. -/
private theorem exists_mem_maximalIdeal_ne_zero {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (P : MMP.Mori.PrimeDivisor X) (y : X)
    (hy : y = P.genericPoint) :
    ∃ t : X.presheaf.stalk y, t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) ∧
      algebraMap (X.presheaf.stalk y) X.functionField t ≠ 0 := by
  subst hy
  have := P.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
  exact ⟨ϖ, hϖ.not_isUnit, (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero⟩

/-- A normal prime divisor `S` of a normal complex variety `M` carries a rational top form `τ`
with a simple pole along `S` and a nonzero Poincaré residue. -/
private theorem exists_isPoincareResidue_ne_zero {k : Type} [Field k] [CharZero k]
    {M S : Scheme.{0}} (sM : M ⟶ Spec (.of k))
    [IsIntegral M] [IsNormal M] [IsLocallyNoetherian M] [CompactSpace M]
    [LocallyOfFiniteType sM] (hX : IsNormalVariety k sM) {n : ℕ}
    (hdim : topologicalKrullDim M = n + 1) (j : S ⟶ M) [IsClosedImmersion j] [IsIntegral S]
    [IsNormal S] [IsLocallyNoetherian S] [CompactSpace S] (hT : IsNormalVariety k (j ≫ sM))
    (P : MMP.Mori.PrimeDivisor M) (hP : Set.range j.base = (P.support : Set M)) :
    ∃ τ : RationalPluriForms sM (n + 1) 1, τ ≠ 0 ∧ P.ordForm τ = -1 ∧
      ∃ ρ : RationalPluriForms (j ≫ sM) n 1, IsPoincareResidue sM j n 1 τ ρ ∧ ρ ≠ 0 := by
  classical
  haveI : LocallyOfFiniteType (j ≫ sM) := hT.1.toLocallyOfFiniteType
  have hjT := MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hP
  letI := functionFieldAlgebra sM
  letI := functionFieldAlgebra (j ≫ sM)
  have hd : (Algebra.trdeg k M.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sM) (by rw [hdim]; norm_cast)
  have hdimT := MMP.Fourfold.topologicalKrullDim_eq_of_range_eq_support sM hdim j P hP
  -- coordinates on `S` with independent differentials
  have := essFiniteType_functionField (sX := j ≫ sM)
  have hfin : Module.finrank S.functionField Ω[S.functionField⁄k] = n :=
    (finrank_kaehlerDifferential_eq_trdeg k S.functionField).trans
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq hdimT)
  have : FiniteDimensional S.functionField Ω[S.functionField⁄k] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k S.functionField).1
  obtain ⟨b, hbsub, hbspan, hbli⟩ :=
    exists_linearIndependent S.functionField (Set.range (KaehlerDifferential.D k S.functionField))
  have hbtop : Submodule.span S.functionField (Set.range ((↑) : b → Ω[S.functionField⁄k])) = ⊤ := by
    rw [Subtype.range_coe, hbspan, KaehlerDifferential.span_range_derivation]
  let bb := Module.Basis.mk hbli hbtop.ge
  have : Finite b := Module.Finite.finite_basis bb
  letI : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = n := by rw [← Module.finrank_eq_card_basis bb, hfin]
  let e : Fin n ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  choose xb hxb using fun i : Fin n => hbsub (e i).2
  obtain ⟨x, hx⟩ : ∃ x : Fin n → M.presheaf.stalk (j (genericPoint S)),
      ∀ i, (j.stalkMap (genericPoint S)).hom (x i) = xb i :=
    ⟨fun i => (SurjectiveOnStalks.stalkMap_surjective j (genericPoint S) (xb i)).choose,
      fun i => (SurjectiveOnStalks.stalkMap_surjective j (genericPoint S) (xb i)).choose_spec⟩
  have hli : LinearIndependent S.functionField
      (fun i => KaehlerDifferential.D k S.functionField ((j.stalkMap (genericPoint S)).hom (x i))) := by
    have h := hbli.comp e e.injective
    convert h using 1
    funext i
    simp only [Function.comp_apply, hx, hxb]
  -- a uniformizing element along `S`
  obtain ⟨t, htm, ht0⟩ := exists_mem_maximalIdeal_ne_zero P (j (genericPoint S)) hjT
  letI := stalkAlgebra sM (j (genericPoint S))
  let ν : MvPolynomial (Fin (n + 1)) k →ₐ[k] M.presheaf.stalk (j (genericPoint S)) :=
    MvPolynomial.aeval (Fin.cons t x)
  have hν0 : ν (MvPolynomial.X 0) = t := by simp [ν]
  have hνs : ∀ i : Fin n, ν (MvPolynomial.X i.succ) = x i := fun i => by simp [ν]
  have hF : (algebraMap _ M.functionField t)⁻¹ *
      algebraMap _ M.functionField (ν (MvPolynomial.X 0)) =
      algebraMap _ M.functionField (1 : M.presheaf.stalk (j (genericPoint S))) := by
    rw [hν0, inv_mul_cancel₀ ht0, map_one]
  obtain ⟨c, hc, hres, hord⟩ := exists_isPoincareResidue_smul_tprod_ιMulti sM hd j P hjT ν
    (by rw [hν0]; exact htm) (fun h => ht0 (by rw [← hν0, h, map_zero]))
    (by simpa only [hνs] using hli) hF
  refine ⟨_, fun h0 => ?_, hord isUnit_one, _, hres, ?_⟩
  · have := hord isUnit_one
    rw [h0, PrimeDivisor.ordForm_zero] at this
    exact absurd this (by norm_num)
  · rw [map_one, mul_one]
    haveI : CharZero S.functionField :=
      charZero_of_injective_algebraMap (algebraMap k S.functionField).injective
    refine smul_ne_zero (Nat.cast_ne_zero.mpr hc.ne') ?_
    intro h0
    have h1 := congrArg (PiTensorProduct.subsingletonEquiv (R := S.functionField)
      (s := fun _ : Fin 1 => ⋀[S.functionField]^n Ω[S.functionField⁄k]) 0) h0
    rw [PiTensorProduct.subsingletonEquiv_apply_tprod] at h1
    exact ιMulti_ne_zero_of_linearIndependent (by simpa only [hνs] using hli)
      (h1.trans (LinearEquiv.map_zero _))

/-! ### Log canonicity by forward adjunction -/

/-- The pull-back predicate depends only on the divisors, not on the proof of `(∗)`. -/
private theorem isPullback_congr {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {D D' : QDivisor Y}
    {hD : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ D.supp} {R R' : QDivisor X}
    (h : D.IsPullback f hD R) (e : D = D') (e' : R = R') : D'.IsPullback f (e ▸ hD) R' := by
  subst e e'
  exact h

/-- **Forward adjunction for one adjunction step.** For one adjunction step `(Y, B_Y) ⇝ (T, B_T)`
from a pair with `0 ≤ B_Y ≤ 1` onto a prime divisor `P`, `(T, B_T)` is a pair, and every divisor
`F` over `T` has an exceptional divisor `E` over `Y` with the same centre and the same
discrepancy: `a(F, T, B_T) = a(E, Y, B_Y)`. -/
private theorem isPair_and_forall_exists_isExceptional {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {BY : QDivisor Y} (hY : MMP.Mori.IsPair sY BY) (hB0 : 0 ≤ BY)
    (hB1 : ∀ P, BY.coeff P ≤ 1) {T : Scheme.{0}} {j : T ⟶ Y} {BT : QDivisor T}
    (h : IsAdjunctionStep sY BY j BT) [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] :
    MMP.Mori.IsPair (j ≫ sY) BT ∧ (∀ Q, 0 ≤ BT.coeff Q) ∧
      ∃ (n : ℕ) (K : Divisor Y) (KT : Divisor T), K.IsCanonicalDivisor sY (n + 1) ∧
        KT.IsCanonicalDivisor (j ≫ sY) n ∧ (Divisor.toQDivisor K + BY).IsQCartier ∧
        (Divisor.toQDivisor KT + BT).IsQCartier ∧
        ∀ F : DivisorOver k (j ≫ sY), ∃ E : DivisorOver k sY, E.IsExceptional ∧
          j.base (F.f.base F.E.genericPoint) = E.f.base E.E.genericPoint ∧
          ∀ a : ℚ, IsDiscrepancy (j ≫ sY) n KT BT F a ↔ IsDiscrepancy sY (n + 1) K BY E a := by
  classical
  obtain ⟨hTv, P, hP1, hP, hci, -⟩ := id h
  have hXv : IsNormalVariety k sY := hY.1
  haveI : LocallyOfFiniteType sY := hXv.1.toLocallyOfFiniteType
  haveI : CompactSpace Y := haveI := hXv.1; QuasiCompact.compactSpace_of_compactSpace sY
  haveI : LocallyOfFiniteType (j ≫ sY) := hTv.1.toLocallyOfFiniteType
  haveI : CompactSpace T := haveI := hTv.1; QuasiCompact.compactSpace_of_compactSpace (j ≫ sY)
  obtain ⟨N, K, hK, hQ⟩ := hY.2
  -- the dimension of `Y` is `n + 1`
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := by
    have hPP := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY P.genericPoint
    rw [P.coheight_genericPoint, hK.topologicalKrullDim_eq] at hPP
    rcases N with _ | n
    · exfalso
      revert hPP
      generalize topologicalKrullDim (closure {P.genericPoint} : Set Y) = e
      induction e using WithBot.recBotCoe with
      | bot => simp
      | coe m =>
        induction m using ENat.recTopCoe with
        | top => norm_cast
        | coe m => norm_cast
    · exact ⟨n, rfl⟩
  have hdim : topologicalKrullDim Y = n + 1 := by rw [hK.topologicalKrullDim_eq]; push_cast; rfl
  have hdimT := MMP.Fourfold.topologicalKrullDim_eq_of_range_eq_support sY hdim j P hP
  have hBP : BY.coeff P = 1 := le_antisymm (hB1 P) hP1
  -- `B_Y = P + B` with `B ≥ 0` not containing `P`
  set B : QDivisor Y := BY - Finsupp.single P 1 with hBdef
  have hBY : BY = Finsupp.single P 1 + B := by rw [hBdef]; abel
  have hBP0 : B.coeff P = 0 := by
    rw [hBdef, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_self, hBP, sub_self]
  have hB : 0 ≤ B := fun Q => by
    rcases eq_or_ne P Q with rfl | hQP
    · exact hBP0.ge
    · have := hB0 Q
      simpa [hBdef, Finsupp.single_apply, hQP] using this
  -- a form with a simple pole along `P` and its residue
  obtain ⟨τ, hτ0, hτP, ρ, hρ, hρ0⟩ := exists_isPoincareResidue_ne_zero sY hXv hdim j hTv P hP
  have hlin := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXv hK hτ0
  rw [one_smul] at hlin
  have hDq : (Divisor.toQDivisor (divisorOfForm τ) + BY).IsQCartier :=
    hQ.add_of_linearlyEquivalent hlin.symm
  obtain ⟨hgen₁, hpb₁⟩ :=
    h.isPullback_divisorOfForm_add_of_isPoincareResidue hdim P hP τ hτ0 hτP ρ hρ hDq
  have hDq' : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsQCartier := by
    rwa [add_assoc, ← hBY]
  have hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
      (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).supp := by
    rw [add_assoc, ← hBY]; exact hgen₁
  have hpb : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsPullback j hgen
      (Divisor.toQDivisor (divisorOfForm ρ) + BT) :=
    isPullback_congr hpb₁ (by rw [add_assoc, ← hBY]) rfl
  -- local generators of a Cartier multiple and their residues
  obtain ⟨M₀, hM₀, DM, hDM, hDMc⟩ := hDq'.exists_pos
  obtain ⟨M', rfl⟩ : ∃ M', M₀ = M' + 1 := ⟨M₀ - 1, by omega⟩
  have hgens := MMP.CyclicChartDifferent.Aux.exists_generatesOn_isPoincareResidue sY hdim j hTv
    hdimT P hP B τ hτ0 ρ hρ hρ0 BT hgen hpb M' DM hDM hDMc
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor (j ≫ sY) hTv hdimT
  have hCart : (((M' + 1 : ℕ) : ℤ) • (Divisor.toQDivisor KT + BT)).IsCartierDivisor :=
    isCartierDivisor_of_forall_generatesOn hTv hKT fun w => by
      obtain ⟨U, hU, -, -, ρ', -, hρ'⟩ := hgens w
      exact ⟨j ⁻¹ᵁ U, hU, ρ', hρ'⟩
  have hBT0 : ∀ Q, 0 ≤ BT.coeff Q := fun Q =>
    coeff_nonneg_of_isPullback_divisorOfForm_isPoincareResidue_of_charZero sY hXv hdim j hTv P hP
      B (DivisorWithCoeffs.isEffective_iff_nonneg.mpr hB) hBP0 τ hτ0 hτP ρ hρ hDq' BT hgen hpb Q
  refine ⟨⟨hTv, n, KT, hKT, ⟨((M' + 1 : ℕ) : ℤ), by positivity, hCart⟩⟩, hBT0, n, K, KT, hK,
    hKT, hQ, ⟨((M' + 1 : ℕ) : ℤ), by positivity, hCart⟩, fun F => ?_⟩
  have hDK : ∃ m : ℕ, 0 < m ∧
      ((m : ℤ) • (Divisor.toQDivisor K + (Finsupp.single P 1 + B))).IsCartierDivisor := by
    rw [← hBY]; exact hQ.exists_pos
  obtain ⟨E, hE, hc, hiff⟩ := exists_isExceptional_isDiscrepancy_iff_of_isPoincareResidue sY hXv n
    K hK P j hTv hP KT hKT B hB hBP0 hDK BT ⟨M' + 1, by omega, hgens⟩ F
  exact ⟨E, hE, hc, fun a => by rw [hiff a, ← hBY]⟩

/-- On a log canonical pair every discrepancy, of a divisor over `X` on any model, is `≥ -1`:
a proper model with the same valuation has log discrepancy `1 + a ≥ 0`. -/
private theorem neg_one_le_of_isLogCanonicalPair {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {Δ : QDivisor X} (hlc : MMP.Intersection.IsLogCanonicalPair sX Δ) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {D : DivisorOver k sX} {a : ℚ}
    (ha : IsDiscrepancy sX n K Δ D a) : -1 ≤ a := by
  have hX := hlc.1.1
  haveI : CompactSpace X := haveI := hX.1; QuasiCompact.compactSpace_of_compactSpace sX
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  obtain ⟨E, hE⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hX D
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hlc.1 hK E.toDivisorOver
  have hc := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX hE
  have h1 := hlc.2.2 _ _ _
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha' E.isProper)
  rw [MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hE.symm hc.symm ha ha']
  exact_mod_cast (by linarith : (-1 : ℝ) ≤ a')

/-- A prime divisor `P` of a pair `(X, B)`, regarded as a divisor over `X`, has discrepancy
`-coeff_P B`. -/
private theorem isDiscrepancy_ofPrimeDivisor {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {B : QDivisor X} (hQ : (Divisor.toQDivisor K + B).IsQCartier)
    (P : MMP.Mori.PrimeDivisor X) :
    IsDiscrepancy sX n K B (DivisorOver.ofPrimeDivisor k hX P) (-B.coeff P) := by
  obtain ⟨m, hm, hmC⟩ := hQ.exists_pos
  obtain ⟨-, V, hV, τ, hτ⟩ :=
    MMP.Positivity.IsPair.exists_generatesOn ⟨hX, n, K, hK, hQ⟩ hK hmC P.genericPoint
  refine ⟨hX, hK, m, hm, hmC, V, hV, τ, hτ, ?_⟩
  rw [DivisorOver.ordPullback_ofPrimeDivisor hX hK.topologicalKrullDim_eq P τ]
  have hPV : (P.support ∩ (V : Set X)).Nonempty := by
    refine ⟨P.genericPoint, ?_, hV⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  linear_combination -hτ.2 P hPV

/-- On a dlt pair with bad set `Z`, every discrepancy of a divisor over `X` whose centre lies in
`Z` is `> -1`: a proper model with the same valuation has the same centre and log discrepancy
`1 + a > 0`. -/
private theorem neg_one_lt_of_isDltPair {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {Δ : QDivisor X} (hP : MMP.Mori.IsPair sX Δ) {Z : TopologicalSpace.Closeds X}
    (hpos : ∀ (n : ℕ) (D : DivisorOver k sX), (D.center : Set X) ⊆ Z →
      ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n (MMP.Mori.QDivisor.toRDivisor Δ) D a →
        0 < a)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {D : DivisorOver k sX} {a : ℚ}
    (hDZ : D.f D.E.genericPoint ∈ (Z : Set X)) (ha : IsDiscrepancy sX n K Δ D a) : -1 < a := by
  have hX := hP.1
  haveI : CompactSpace X := haveI := hX.1; QuasiCompact.compactSpace_of_compactSpace sX
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  obtain ⟨E, hE⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hX D
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK E.toDivisorOver
  have hc := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX hE
  have hEZ : (E.toDivisorOver.center : Set X) ⊆ Z := by
    rw [DivisorOver.center_eq_closure_genericPoint]
    refine (Z.isClosed.closure_subset_iff).mpr ?_
    rw [Set.singleton_subset_iff]
    exact hc ▸ hDZ
  have h1 := hpos n _ hEZ _
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha' E.isProper)
  rw [MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hE.symm hc.symm ha ha']
  exact_mod_cast (by linarith : (-1 : ℝ) < a')

end Step

section Transport

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
  {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X}

/-- The discrepancy does not depend on the chosen canonical divisor. -/
private theorem isDiscrepancy_of_isCanonicalDivisor {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {n n' : ℕ} {K K' : Divisor Y}
    {Δ : QDivisor Y} {D : DivisorOver k sY} {a : ℚ} (hK' : K'.IsCanonicalDivisor sY n')
    (h : IsDiscrepancy sY n K Δ D a) : IsDiscrepancy sY n' K' Δ D a := by
  have hX := h.1
  haveI : CompactSpace Y := haveI := hX.1; QuasiCompact.compactSpace_of_compactSpace sY
  obtain rfl : n' = n := by
    have := hK'.topologicalKrullDim_eq.symm.trans h.2.1.topologicalKrullDim_eq
    exact_mod_cast this
  exact MMP.Spreading.isDiscrepancy_of_linearlyEquivalent h
    (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sY hX hK' h.2.1)

/-- **Forward adjunction along a flag.** Along a flag of iterated adjunction from a log canonical
pair `(X, B)` with `0 ≤ B ≤ 1`, the final pair `(S, B_S)` is a pair with `B_S ≥ 0`, and every
discrepancy of a divisor over `S` is the discrepancy of a divisor over `X` whose centre is the
image of its centre. -/
private theorem forall_exists_isDiscrepancy_of_stratumAdjunctionData
    (hlc : MMP.Intersection.IsLogCanonicalPair sX B) (hB1 : ∀ P, B.coeff P ≤ 1)
    {T : Scheme.{0}} {ι : T ⟶ X} {BT : QDivisor T} (F : StratumAdjunctionData sX B ι BT) :
    haveI : IsIntegral T := F.isNormalVariety.1.toIsIntegral
    haveI : IsNormal T := F.isNormalVariety.2
    haveI : IsLocallyNoetherian T := by
      have := F.isNormalVariety.1
      exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sX)
    MMP.Mori.IsPair (ι ≫ sX) BT ∧ (∀ Q, 0 ≤ BT.coeff Q) ∧
      ∀ (D : DivisorOver k (ι ≫ sX)) (n' : ℕ) (K' : Divisor T) (a : ℚ),
        IsDiscrepancy (ι ≫ sX) n' K' BT D a →
        ∃ (E : DivisorOver k sX) (n : ℕ) (K : Divisor X),
          E.f.base E.E.genericPoint = ι.base (D.f.base D.E.genericPoint) ∧
          IsDiscrepancy sX n K B E a := by
  induction F with
  | refl h =>
    have key : ∀ (g : X ⟶ Spec (.of k)), g = sX →
        MMP.Mori.IsPair g B ∧ (∀ Q, 0 ≤ B.coeff Q) ∧
        ∀ (D : DivisorOver k g) (n' : ℕ) (K' : Divisor X) (a : ℚ),
          IsDiscrepancy g n' K' B D a →
          ∃ (E : DivisorOver k sX) (n : ℕ) (K : Divisor X),
            E.f.base E.E.genericPoint = (𝟙 X : X ⟶ X).base (D.f.base D.E.genericPoint) ∧
            IsDiscrepancy sX n K B E a := by
      rintro g rfl
      exact ⟨h, hlc.2.1, fun D n' K' a hD => ⟨D, n', K', rfl, hD⟩⟩
    exact key _ (Category.id_comp sX)
  | step F j BT h ih =>
    rename_i S T ι BS
    haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    haveI : IsNormal S := F.isNormalVariety.2
    haveI : IsLocallyNoetherian S := by
      have := F.isNormalVariety.1
      exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sX)
    haveI : IsIntegral T := (F.step j BT h).isNormalVariety.1.toIsIntegral
    haveI : IsNormal T := (F.step j BT h).isNormalVariety.2
    haveI : IsLocallyNoetherian T := by
      have := (F.step j BT h).isNormalVariety.1
      exact LocallyOfFiniteType.isLocallyNoetherian ((j ≫ ι) ≫ sX)
    obtain ⟨hPS, hS0, htr⟩ := ih
    -- the coefficients of `B_S` are at most one
    have hS1 : ∀ Q, BS.coeff Q ≤ 1 := by
      intro Q
      obtain ⟨hXS, nS, KS, hKS, hQS⟩ := hPS
      obtain ⟨E, nE, KE, -, hE⟩ := htr _ _ _ _ (isDiscrepancy_ofPrimeDivisor hXS hKS hQS Q)
      have := neg_one_le_of_isLogCanonicalPair hlc hE.2.1 hE
      linarith
    obtain ⟨hPT, hT0, n, K, KT, hK, hKT, -, -, hF⟩ :=
      isPair_and_forall_exists_isExceptional hPS (fun Q => hS0 Q) hS1 h
    simp only [Category.assoc]
    refine ⟨hPT, hT0, fun D n' K' a hD => ?_⟩
    obtain ⟨E, -, hc, hiff⟩ := hF D
    obtain ⟨E', nE, KE, hc', hE'⟩ :=
      htr E _ _ _ ((hiff a).mp (isDiscrepancy_of_isCanonicalDivisor hKT hD))
    refine ⟨E', nE, KE, ?_, hE'⟩
    rw [hc', ← hc]
    rfl

/-- **Strata of a dlt pair are generically snc** (KM 5.50). A boundary stratum `S ≠ X` of a dlt
pair `(X, B)` is not contained in the bad set `Z` of the dlt condition: the last step of a flag
ending at `S` cuts `S` out as a coefficient-one prime divisor of the previous stratum, whose
discrepancy `≤ -1` forward adjunction carries to a divisor over `X` with centre `S`. -/
private theorem not_subset_of_isDltStratum (hB : MMP.Fourfold.IsPair sX B)
    (hdlt : MMP.Intersection.IsDltPair sX B) {Z : TopologicalSpace.Closeds X}
    (hpos : ∀ (n : ℕ) (D : DivisorOver k sX), (D.center : Set X) ⊆ Z →
      ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n (MMP.Mori.QDivisor.toRDivisor B) D a →
        0 < a)
    {S : Set X} (hS : IsDltStratum sX B S) (hSX : S ≠ Set.univ) : ¬ S ⊆ Z := by
  intro hSZ
  obtain ⟨T, ι, BT, hrange, ⟨F⟩⟩ :=
    (IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair hS).1.1
  cases F with
  | refl h => exact hSX (by rw [← hrange]; exact Set.range_id)
  | @step S₀ T₀ ι₀ BS₀ F₀ j BT₀ h =>
    haveI : IsIntegral S₀ := F₀.isNormalVariety.1.toIsIntegral
    haveI : IsNormal S₀ := F₀.isNormalVariety.2
    haveI : IsLocallyNoetherian S₀ := by
      have := F₀.isNormalVariety.1
      exact LocallyOfFiniteType.isLocallyNoetherian (ι₀ ≫ sX)
    obtain ⟨hPS, -, htr⟩ :=
      forall_exists_isDiscrepancy_of_stratumAdjunctionData hdlt.1 hdlt.2.1 F₀
    obtain ⟨hXS, nS, KS, hKS, hQS⟩ := hPS
    obtain ⟨-, P', hP'1, hP', -⟩ := h
    obtain ⟨E, nE, KE, hc, hE⟩ := htr _ _ _ _ (isDiscrepancy_ofPrimeDivisor hXS hKS hQS P')
    have hη : P'.genericPoint ∈ Set.range j.base := by
      rw [hP', AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    obtain ⟨y, hy⟩ := hη
    have hEZ : E.f.base E.E.genericPoint ∈ (Z : Set X) := by
      rw [hc]
      apply hSZ
      rw [← hrange]
      exact ⟨y, by rw [Scheme.Hom.comp_base, TopCat.comp_app, hy]; rfl⟩
    have := neg_one_lt_of_isDltPair hB.isPair hpos hE.2.1 hEZ hE
    linarith

/-- **KM 5.50 for two floor components.** For a dlt pair `(X, B)` with bad set `Z` and prime
divisors `P ≠ Q` of coefficient at least one, every irreducible subset `W ⊆ P ∩ Q` lies in an
irreducible closed subset of `P ∩ Q` whose generic point is outside `Z`: an irreducible
component of `P ∩ Q` containing `W` is a boundary stratum. -/
private theorem exists_notMem_of_isDltPair' (hdlt : MMP.Intersection.IsDltPair sX B)
    {Z : TopologicalSpace.Closeds X}
    (hpos : ∀ (n : ℕ) (D : DivisorOver k sX), (D.center : Set X) ⊆ Z →
      ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n (MMP.Mori.QDivisor.toRDivisor B) D a →
        0 < a)
    {P Q : MMP.Mori.PrimeDivisor X} (hPQ : P ≠ Q) (hP : 1 ≤ B.coeff P) (hQ : 1 ≤ B.coeff Q)
    {W : Set X} (hW : IsIrreducible W) (hWPQ : W ⊆ (P.support : Set X) ∩ Q.support) :
    ∃ c : X, c ∉ (Z : Set X) ∧ W ⊆ closure {c} ∧
      closure {c} ⊆ (P.support : Set X) ∩ Q.support := by
  classical
  set C : Set X := (P.support : Set X) ∩ Q.support with hCdef
  have hC : IsClosed C := P.idealSheaf.support.isClosed.inter Q.idealSheaf.support.isClosed
  -- a maximal irreducible subset of `C` containing `W`
  obtain ⟨m, hWm, hm⟩ :=
    zorn_subset_nonempty { t : Set X | IsPreirreducible t ∧ t ⊆ C }
      (fun c hc hcc _ =>
        ⟨⋃₀ c, ⟨fun u v hu hv ⟨y, hy, hyu⟩ ⟨x, hx, hxv⟩ =>
          let ⟨p, hpc, hyp⟩ := Set.mem_sUnion.1 hy
          let ⟨q, hqc, hxq⟩ := Set.mem_sUnion.1 hx
          Or.casesOn (hcc.total hpc hqc)
            (fun hpq : p ⊆ q =>
              let ⟨x, hxp, hxuv⟩ := (hc hqc).1 u v hu hv ⟨y, hpq hyp, hyu⟩ ⟨x, hxq, hxv⟩
              ⟨x, Set.mem_sUnion_of_mem hxp hqc, hxuv⟩)
            fun hqp : q ⊆ p =>
            let ⟨x, hxp, hxuv⟩ := (hc hpc).1 u v hu hv ⟨y, hyp, hyu⟩ ⟨x, hqp hxq, hxv⟩
            ⟨x, Set.mem_sUnion_of_mem hxp hpc, hxuv⟩,
          Set.sUnion_subset fun t ht => (hc ht).2⟩,
          fun _ hxc => Set.subset_sUnion_of_mem hxc⟩)
      W ⟨hW.2, hWPQ⟩
  have hmirr : IsIrreducible m := ⟨hW.1.mono hWm, hm.prop.1⟩
  have hmax : Maximal (fun T : Set X => IsIrreducible T ∧
      T ⊆ ⋂ R ∈ ({P, Q} : Finset (MMP.Mori.PrimeDivisor X)), (R.support : Set X)) m := by
    have hJ : (⋂ R ∈ ({P, Q} : Finset (MMP.Mori.PrimeDivisor X)), (R.support : Set X)) = C := by
      simp [hCdef]
    rw [hJ]
    exact ⟨⟨hmirr, hm.prop.2⟩, fun T hT hmT => hm.le_of_ge ⟨hT.1.2, hT.2⟩ hmT⟩
  have hstr : IsDltStratum sX B m := by
    refine ⟨hdlt, {P, Q}, Finset.insert_nonempty _ _, ?_, ?_, hmax⟩
    · intro R hR
      rcases Finset.mem_insert.mp hR with rfl | hR
      · exact hP
      · rw [Finset.mem_singleton.mp hR]; exact hQ
    · obtain ⟨w, hw⟩ := hW.1
      exact ⟨w, by simpa [hCdef] using hWPQ hw⟩
  have hB : MMP.Fourfold.IsPair sX B := ⟨inferInstance, inferInstance, hdlt.1.1, hdlt.1.2.1⟩
  have hmC : closure m = m := by
    refine (hm.le_of_ge ⟨hm.prop.1.closure, hC.closure_subset_iff.mpr hm.prop.2⟩
      subset_closure).antisymm subset_closure
  have hmX : m ≠ Set.univ := by
    intro h
    apply MMP.Threefold.Mori.CanonUniq.genericPoint_notMem_support P
    exact (hm.prop.2 (h ▸ Set.mem_univ (genericPoint X))).1
  have hnot := not_subset_of_isDltStratum hB hdlt hpos hstr hmX
  set c := hmirr.genericPoint with hc
  have hcl : closure {c} = m := by
    rw [hmirr.isGenericPoint_genericPoint_closure.def, hmC]
  refine ⟨c, fun hcZ => hnot ?_, hcl ▸ hWm, hcl ▸ hm.prop.2⟩
  rw [← hcl]
  exact Z.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hcZ)

end Transport

end KM550

section Node

/-- **Differentials along a map onto fractions.** If every element of `B` is a fraction of
images of elements of `A` with unit denominator, the differentials of the images of a family
spanning `Ω_{A/k}` span `Ω_{B/k}`. -/
private theorem span_range_D_algebraMap_eq_top {k A B : Type*} [CommRing k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (hfrac : ∀ b : B, ∃ a s : A, IsUnit (algebraMap A B s) ∧
      b * algebraMap A B s = algebraMap A B a)
    {ι : Type*} (w : ι → A)
    (hw : Submodule.span A (Set.range fun i => KaehlerDifferential.D k A (w i)) = ⊤) :
    Submodule.span B (Set.range fun i => KaehlerDifferential.D k B (algebraMap A B (w i))) =
      ⊤ := by
  set N := Submodule.span B (Set.range fun i => KaehlerDifferential.D k B (algebraMap A B (w i)))
  have h1 : ∀ a : A, KaehlerDifferential.D k B (algebraMap A B a) ∈ N := by
    intro a
    have ha : KaehlerDifferential.D k A a ∈
        Submodule.span A (Set.range fun i => KaehlerDifferential.D k A (w i)) :=
      hw ▸ Submodule.mem_top
    have h2 := Submodule.mem_map_of_mem (f := KaehlerDifferential.map k k A B) ha
    rw [Submodule.map_span, KaehlerDifferential.map_D, ← Set.range_comp] at h2
    have h3 : (⇑(KaehlerDifferential.map k k A B) ∘ fun i => KaehlerDifferential.D k A (w i)) =
        fun i => KaehlerDifferential.D k B (algebraMap A B (w i)) := by
      funext i; exact KaehlerDifferential.map_D k k A B (w i)
    rw [h3] at h2
    exact Submodule.span_le_restrictScalars A B _ h2
  have h2 : ∀ b : B, KaehlerDifferential.D k B b ∈ N := by
    intro b
    obtain ⟨a, s, hs, hb⟩ := hfrac b
    have h4 : algebraMap A B s • KaehlerDifferential.D k B b =
        KaehlerDifferential.D k B (algebraMap A B a) -
          b • KaehlerDifferential.D k B (algebraMap A B s) := by
      rw [← hb, Derivation.leibniz]; abel
    have h5 : algebraMap A B s • KaehlerDifferential.D k B b ∈ N := by
      rw [h4]; exact N.sub_mem (h1 a) (N.smul_mem b (h1 s))
    have h6 := N.smul_mem (↑hs.unit⁻¹ : B) h5
    rwa [smul_smul, IsUnit.val_inv_mul, one_smul] at h6
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  exact h2 b

open IsLocalRing in
/-- **Generators of the maximal ideal give generators of `Ω`.** Over a local ring `R` with
`Ω_{R/k}` finite and `Ω_{κ/k} = 0` for its residue field `κ`, the differentials of a family
generating the maximal ideal generate `Ω_{R/k}`. -/
private theorem span_range_D_eq_top_of_span_eq_maximalIdeal {k R : Type*} [Field k] [CommRing R]
    [IsLocalRing R] [Algebra k R] [Module.Finite R Ω[R⁄k]]
    [Subsingleton Ω[ResidueField R⁄k]] {n : ℕ} (t : Fin n → R)
    (ht : Ideal.span (Set.range t) = maximalIdeal R) :
    Submodule.span R (Set.range fun i => KaehlerDifferential.D k R (t i)) = ⊤ := by
  rw [← IsLocalRing.map_tensorProduct_mk_eq_top, Submodule.map_span,
    ← Set.range_comp]
  have h := MMP.Flips.ResolutionInputs.span_tmul_D k t ht
  rw [top_le_iff] at h
  have h2 := congrArg (Submodule.restrictScalars R) h
  rw [Submodule.restrictScalars_span R (ResidueField R) residue_surjective,
    Submodule.restrictScalars_top] at h2
  exact h2

/-- The stalk of a scheme locally of finite type over `k` is essentially of finite type. -/
private theorem essFiniteType_stalk {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (x : X) :
    letI := MMP.Mori.stalkAlgebra sX x
    Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  obtain ⟨W, hW, hpW, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.stalkAlgebra sX x
  let : Algebra Γ(X, W) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hpW⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hW.primeIdealOf ⟨x, hpW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨x, hpW⟩
  have : IsScalarTower k Γ(X, W) (X.presheaf.stalk x) :=
    MMP.Mori.isScalarTower_section_stalk sX W ⟨x, hpW⟩
  have : Algebra.FiniteType k Γ(X, W) :=
    MMP.Mori.finiteType_sectionAlgebra sX hW
  have : Algebra.EssFiniteType Γ(X, W) (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.of_isLocalization _ (hW.primeIdealOf ⟨x, hpW⟩).asIdeal.primeCompl
  exact Algebra.EssFiniteType.comp k Γ(X, W) _

/-- **Generators of the maximal ideal at a closed point give generators of `Ω`.** At a closed
point `x` of a scheme locally of finite type over a field of characteristic zero, the
differentials of a family generating the maximal ideal of `𝒪_{X,x}` generate `Ω_{𝒪_{X,x}/k}`. -/
private theorem span_range_D_stalk_eq_top {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (x : X) (hx : IsClosed ({x} : Set X))
    {n : ℕ} (t : Fin n → X.presheaf.stalk x)
    (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    letI := MMP.Mori.stalkAlgebra sX x
    Submodule.span (X.presheaf.stalk x)
      (Set.range fun i => KaehlerDifferential.D k (X.presheaf.stalk x) (t i)) = ⊤ := by
  letI := MMP.Mori.stalkAlgebra sX x
  have := essFiniteType_stalk sX x
  have : Module.Finite k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sX x hx
  have : Algebra.FormallyUnramified k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    Algebra.FormallyUnramified.of_isSeparable _ _
  exact span_range_D_eq_top_of_span_eq_maximalIdeal t ht

/-- A stalk at a generization `y ⤳ x` consists of fractions of elements of `𝒪_{X,x}`. -/
private theorem exists_mul_stalkSpecializes_eq {X : Scheme.{0}} {x y : X} (h : y ⤳ x)
    (b : X.presheaf.stalk y) : ∃ a s : X.presheaf.stalk x,
      IsUnit ((X.presheaf.stalkSpecializes h).hom s) ∧
      b * (X.presheaf.stalkSpecializes h).hom s = (X.presheaf.stalkSpecializes h).hom a := by
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  have hyW : y ∈ W := h.mem_open W.isOpen hxW
  let : Algebra Γ(X, W) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hyW⟩
  have := hW.isLocalization_stalk ⟨y, hyW⟩
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (hW.primeIdealOf ⟨y, hyW⟩).asIdeal.primeCompl b
  have hg : ∀ c : Γ(X, W), algebraMap Γ(X, W) (X.presheaf.stalk y) c =
      (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ W x hxW).hom c) := by
    intro c
    change (X.presheaf.germ W y hyW).hom c = _
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  refine ⟨(X.presheaf.germ W x hxW).hom r, (X.presheaf.germ W x hxW).hom s, ?_, ?_⟩
  · rw [← hg]
    exact IsLocalization.map_units _ s
  · rw [← hg, ← hg]
    exact hrs

/-- The function field consists of fractions of elements of any stalk. -/
private theorem exists_mul_algebraMap_eq {X : Scheme.{0}} [IsIntegral X] (y : X)
    (b : X.functionField) : ∃ a s : X.presheaf.stalk y,
      IsUnit (algebraMap (X.presheaf.stalk y) X.functionField s) ∧
      b * algebraMap _ X.functionField s = algebraMap _ X.functionField a := by
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors (X.presheaf.stalk y)) b
  refine ⟨r, s, ?_, hrs⟩
  exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2).isUnit

/-- The specialization map of stalks is a map of `k`-algebras. -/
private theorem stalkSpecializes_algebraMap {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) {x y : X} (h : y ⤳ x) (c : k) :
    (X.presheaf.stalkSpecializes h).hom (letI := MMP.Mori.stalkAlgebra sX x; algebraMap k _ c) =
      (letI := MMP.Mori.stalkAlgebra sX y; algebraMap k _ c) := by
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
    X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top _) ≫
    X.presheaf.stalkSpecializes h).hom c = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  rfl

/-- **The order of a coordinate form.** Let `X` be a variety of dimension `d` over a perfect
field, `x ∈ X`, and `t₁, …, t_d ∈ 𝒪_{X,x}` with `dt₁, …, dt_d` generating `Ω_{𝒪_{X,x}/k}`.
Along every prime divisor `Γ` through `x`, `ord_Γ (a · (dt₁ ∧ ⋯ ∧ dt_d)^{⊗m}) = ord_Γ a`. -/
private theorem ordForm_smul_tprod_ιMulti_D {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [LocallyOfFiniteType sX] {d : ℕ} (hd : topologicalKrullDim X = d) (x : X)
    (t : Fin d → X.presheaf.stalk x)
    (ht : letI := MMP.Mori.stalkAlgebra sX x
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun i => KaehlerDifferential.D k (X.presheaf.stalk x) (t i)) = ⊤)
    (Γ : MMP.Mori.PrimeDivisor X) (hΓ : x ∈ Γ.support) {m : ℕ} (a : X.functionField)
    (τ : RationalPluriForms sX d m)
    (hτ : letI := MMP.Mori.functionFieldAlgebra sX
      τ = (a • PiTensorProduct.tprod X.functionField (fun _ : Fin m =>
        exteriorPower.ιMulti X.functionField d (fun i => KaehlerDifferential.D k X.functionField
          (algebraMap _ X.functionField (t i)))) :
          TensorPower X.functionField m (⋀[X.functionField]^d Ω[X.functionField⁄k]))) :
    Γ.ordForm τ = X.ord a Γ.genericPoint := by
  letI := MMP.Mori.functionFieldAlgebra sX
  letI := MMP.Mori.stalkAlgebra sX x
  letI := MMP.Mori.stalkAlgebra sX Γ.genericPoint
  have hsp : Γ.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hΓ
  letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk Γ.genericPoint) :=
    (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
  haveI : IsScalarTower k (X.presheaf.stalk x) (X.presheaf.stalk Γ.genericPoint) :=
    IsScalarTower.of_algebraMap_eq fun c => (stalkSpecializes_algebraMap sX hsp c).symm
  haveI := MMP.Mori.isScalarTower_stalk_functionField sX x
  haveI := MMP.Mori.isScalarTower_stalk_functionField sX Γ.genericPoint
  set w : Fin d → Ω[(X.presheaf.stalk Γ.genericPoint)⁄k] := fun i =>
    KaehlerDifferential.D k _ (algebraMap (X.presheaf.stalk x) _ (t i)) with hw
  have hspan : Submodule.span (X.presheaf.stalk Γ.genericPoint) (Set.range w) = ⊤ :=
    span_range_D_algebraMap_eq_top (exists_mul_stalkSpecializes_eq hsp) t ht
  have hK : Submodule.span X.functionField (Set.range fun i =>
      KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField (t i))) = ⊤ :=
    span_range_D_algebraMap_eq_top (exists_mul_algebraMap_eq x) t ht
  have hmap : (fun i => KaehlerDifferential.map k k (X.presheaf.stalk Γ.genericPoint)
      X.functionField (w i)) =
      fun i => KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField (t i)) := by
    funext i
    rw [hw, KaehlerDifferential.map_D]
    congr 1
    exact MMP.Mori.algebraMap_stalkSpecializes hsp (t i)
  have htop : MMP.Mori.topFormsMap k (X.presheaf.stalk Γ.genericPoint) X.functionField d
      (exteriorPower.ιMulti _ d w) = exteriorPower.ιMulti X.functionField d
        (fun i => KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField (t i))) := by
    rw [MMP.Mori.topFormsMap_ιMulti, hmap]
  have := MMP.Mori.essFiniteType_functionField (sX := sX)
  have hfin : Module.finrank X.functionField Ω[X.functionField⁄k] = d :=
    (MMP.Mori.finrank_kaehlerDifferential_eq_trdeg k X.functionField).trans
      (MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq hd)
  have : FiniteDimensional X.functionField Ω[X.functionField⁄k] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k X.functionField).1
  have hli := linearIndependent_of_top_le_span_of_card_eq_finrank hK.ge
    (by rw [Fintype.card_fin, hfin])
  have h0 : MMP.Mori.topFormsMap k (X.presheaf.stalk Γ.genericPoint) X.functionField d
      (exteriorPower.ιMulti _ d w) ≠ 0 := by
    rw [htop]; exact ιMulti_ne_zero_of_linearIndependent hli
  exact MMP.CyclicChartDifferent.ordForm_eq_of_frame Γ rfl w hspan h0 a τ (by rw [htop]; exact hτ)

/-- An open immersion `U ⟶ X` restricted to its image is an isomorphism. -/
private theorem isIso_ι_restrict_self' {X : Scheme.{0}} (U : X.Opens) : IsIso (U.ι ∣_ U) := by
  have : Surjective (U.ι ∣_ U) := by
    constructor
    intro y
    let x : (U.ι ⁻¹ᵁ U).toScheme := ⟨y, by simp⟩
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    have := Scheme.Hom.comp_apply (U.ι ∣_ U) U.ι x
    rw [morphismRestrict_ι] at this
    exact this.symm
  exact isIso_of_mono_of_strongEpi (U.ι ∣_ U)

/-- The inverse transform of a divisor along the inclusion of an open subscheme is its
restriction. -/
private theorem inverseTransformDivisor_ι_eq_restrictOpen' {X : Scheme.{0}} {R : Type*}
    [AddCommMonoid R] (U : X.Opens) (B : MMP.Mori.DivisorWithCoeffs R X) :
    MMP.Mori.inverseTransformDivisor U.ι B = B.restrictOpen U := by
  have hbir : ∀ x : U.toScheme, U.ι x ∈ MMP.Mori.biregularLocus U.ι := fun x =>
    MMP.Mori.le_biregularLocus (isIso_ι_restrict_self' U)
      (by rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩)
  refine Finsupp.ext fun W => ?_
  refine (MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (E := AlgebraicGeometry.OpenWeilRestriction.primeDivisorMap U.ι W)
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      (AlgebraicGeometry.OpenWeilRestriction.genericPoint_primeDivisorMap U.ι W).symm (hbir _))
    (fun E' hE' => ?_) B).trans rfl
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  rw [AlgebraicGeometry.OpenWeilRestriction.genericPoint_primeDivisorMap,
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hE').1]

open IsLocalRing in
/-- **Coordinates at a point where two floor components meet.** Let `(S, B)` be a dlt surface and
`P ≠ Q` prime divisors of coefficient one meeting at a point `x` outside the bad set of the dlt
condition. Then `𝒪_{S,x}` has a regular system of parameters `(u, v)` with `P = (u)` and
`Q = (v)` at `x`, and `P`, `Q` are the only components of `B` through `x`. -/
private theorem exists_coordinates_of_mem_inter {S : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)}
    (hdim : topologicalKrullDim S = 2) {B : QDivisor S} {Z : TopologicalSpace.Closeds S}
    (hsnc : MMP.Mori.DivisorWithCoeffs.IsSNC (Scheme.Opens.ι (Z.compl : S.Opens) ≫ sS)
      (MMP.Mori.inverseTransformDivisor (Scheme.Opens.ι (Z.compl : S.Opens)) B))
    {P Q : MMP.Mori.PrimeDivisor S} (hPQ : P ≠ Q) (hP : B.coeff P ≠ 0) (hQ : B.coeff Q ≠ 0)
    {x : S} (hx : x ∈ (P.support : Set S) ∩ Q.support) (hxZ : x ∉ (Z : Set S)) :
    ∃ u v : S.presheaf.stalk x,
      Ideal.span {u, v} = maximalIdeal (S.presheaf.stalk x) ∧
      MMP.Mori.IsRegularSystemOfParameters ![u, v] ∧
      IdealSheafData.stalk P.idealSheaf x = Ideal.span {u} ∧
      IdealSheafData.stalk Q.idealSheaf x = Ideal.span {v} ∧
      ∀ Γ : MMP.Mori.PrimeDivisor S, x ∈ Γ.support → B.coeff Γ ≠ 0 → Γ = P ∨ Γ = Q := by
  classical
  set U : S.Opens := Z.compl
  have hxU : x ∈ U := hxZ
  rw [inverseTransformDivisor_ι_eq_restrictOpen'] at hsnc
  obtain ⟨n, z, jj, hz, hjj, hI⟩ : ∃ (n : ℕ) (z : Fin n → S.presheaf.stalk x)
      (jj : {E : MMP.Mori.PrimeDivisor S // E ∈ B.support ∧ x ∈ E.support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧ Function.Injective jj ∧
        ∀ E, IdealSheafData.stalk E.1.idealSheaf x = Ideal.span {z (jj E)} :=
    (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff U.ι B ⟨x, hxU⟩).mp
      (hsnc.2 ⟨x, hxU⟩)
  have hPs : P ∈ B.support := Finsupp.mem_support_iff.mpr hP
  have hQs : Q ∈ B.support := Finsupp.mem_support_iff.mpr hQ
  set EP : {E : MMP.Mori.PrimeDivisor S // E ∈ B.support ∧ x ∈ E.support} := ⟨P, hPs, hx.1⟩
  set EQ : {E : MMP.Mori.PrimeDivisor S // E ∈ B.support ∧ x ∈ E.support} := ⟨Q, hQs, hx.2⟩
  have hne : jj EP ≠ jj EQ := fun h => hPQ (congrArg Subtype.val (hjj h))
  -- `n = 2`
  have hn2 : n ≤ 2 := by
    have h1 := hz.2
    have h2 : ringKrullDim (S.presheaf.stalk x) ≤ 2 := by
      rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, ← hdim, topologicalKrullDim,
        Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := (S : Type)))]
      exact Order.coheight_le_krullDim _
    rw [h1] at h2
    exact_mod_cast h2
  have hn2' : 2 ≤ n := by
    by_contra h
    have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr (by omega)
    exact hne (Subsingleton.elim _ _)
  obtain rfl : n = 2 := le_antisymm hn2 hn2'
  have hall : ∀ i : Fin 2, i = jj EP ∨ i = jj EQ := by
    intro i
    have : ∀ a b : Fin 2, a ≠ b → ∀ c : Fin 2, c = a ∨ c = b := by decide
    exact this _ _ hne i
  refine ⟨z (jj EP), z (jj EQ), ?_, ?_, hI EP, hI EQ, fun Γ hΓ hΓB => ?_⟩
  · rw [← hz.1]
    congr 1
    ext a
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl) <;> exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩
      rcases hall i with rfl | rfl <;> simp
  · refine ⟨?_, hz.2⟩
    rw [← hz.1]
    congr 1
    ext a
    simp only [Set.mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩
      rcases hall i with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  · set EΓ : {E : MMP.Mori.PrimeDivisor S // E ∈ B.support ∧ x ∈ E.support} :=
      ⟨Γ, Finsupp.mem_support_iff.mpr hΓB, hΓ⟩
    rcases hall (jj EΓ) with h | h
    · exact Or.inl (congrArg Subtype.val (hjj h))
    · exact Or.inr (congrArg Subtype.val (hjj h))

/-- A unit of the local ring at a prime divisor has order zero. -/
private theorem ord_algebraMap_eq_zero_of_isUnit' {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y]
    (P : MMP.Mori.PrimeDivisor Y) {x : Y} (hx : x = P.genericPoint) {b : Y.presheaf.stalk x}
    (hb : IsUnit b) : Y.ord (algebraMap _ Y.functionField b) P.genericPoint = 0 := by
  subst hx
  exact P.ord_algebraMap_of_isUnit hb

/-- In a domain, a nonzero prime contained in a prime of height one is equal to it. -/
private lemma eq_of_le_of_height_eq_one' {A : Type*} [CommRing A] [IsDomain A] {I q : Ideal A}
    [I.IsPrime] [q.IsPrime] (hI : I ≠ ⊥) (hle : I ≤ q) (hq : q.height = 1) : I = q := by
  by_contra hne
  have : q.FiniteHeight := Ideal.finiteHeight_iff_lt.mpr (Or.inr (by rw [hq]; simp))
  have h1 := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hle hne)
  rw [hq, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1
  exact hI h1

open Classical in
/-- **The orders of a local equation of a prime divisor.** If `Γ ∋ y` is cut out at `y` by a
member `t` of a regular system of parameters of `𝒪_{Y,y}`, then `t` has order one along `Γ` and
order zero along every other prime divisor through `y`. -/
private theorem ord_algebraMap_eq_ite_of_stalk_eq_span' {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {y : Y} {n : ℕ} {z : Fin n → Y.presheaf.stalk y}
    (hz : MMP.Mori.IsRegularSystemOfParameters z) (i : Fin n) (Γ : MMP.Mori.PrimeDivisor Y)
    (hΓy : y ∈ Γ.support) (hΓ : IdealSheafData.stalk Γ.idealSheaf y = Ideal.span {z i})
    (E : MMP.Mori.PrimeDivisor Y) (hE : y ∈ E.support) :
    Y.ord (algebraMap _ Y.functionField (z i)) E.genericPoint = if E = Γ then 1 else 0 := by
  classical
  have hsp : E.genericPoint ⤳ y := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hE
  set tE := Y.presheaf.stalkSpecializes hsp (z i) with htE
  have halg : algebraMap _ Y.functionField tE = algebraMap _ Y.functionField (z i) :=
    MMP.Fourfold.algebraMap_stalkSpecializes' Y hsp _
  have hmax : IsLocalRing.maximalIdeal (Y.presheaf.stalk E.genericPoint) =
      Ideal.map (Y.presheaf.stalkSpecializes hsp).hom (IdealSheafData.stalk E.idealSheaf y) := by
    rw [← MMP.Resolution.Aux.stalk_eq_map_stalkSpecializes,
      MMP.Resolution.Aux.stalk_idealSheaf_genericPoint]
  haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  have hz0 : z i ≠ 0 := MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz i
  split_ifs with hEΓ
  · subst hEΓ
    rw [hΓ, Ideal.map_span, Set.image_singleton] at hmax
    haveI : IsDiscreteValuationRing (Y.presheaf.stalk E.genericPoint) :=
      E.isDiscreteValuationRing_localRing
    have htE0 : tE ≠ 0 := by
      intro h0
      have : algebraMap _ Y.functionField (z i) = 0 := by rw [← halg, h0, map_zero]
      exact hz0 (IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
        (this.trans (map_zero _).symm))
    rw [← halg]
    exact MMP.Fourfold.ord_algebraMap_eq_one_of_irreducible E.coheight_genericPoint
      (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal tE htE0 hmax)
  · have hnot : z i ∉ MMP.Intersection.primeOfSpecializes hsp := by
      intro hmem
      obtain ⟨q, hqE, hq, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support E hE
      obtain ⟨qΓ, -, hqΓ, hqΓh⟩ :=
        MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support Γ hΓy
      have hpq : MMP.Intersection.primeOfSpecializes hsp = q.asIdeal := by
        have hsp' : Y.fromSpecStalk y q ⤳ y := hqE ▸ hsp
        rw [MMP.Resolution.primeOfSpecializes_congr hqE.symm hsp hsp']
        exact MMP.Resolution.primeOfSpecializes_fromSpecStalk y q hsp'
      have hle : IdealSheafData.stalk Γ.idealSheaf y ≤ q.asIdeal := by
        rw [hΓ, Ideal.span_le, Set.singleton_subset_iff, ← hpq]; exact hmem
      haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk y)
      haveI : (IdealSheafData.stalk Γ.idealSheaf y).IsPrime := by rw [hqΓ]; exact qΓ.2
      have heq : IdealSheafData.stalk Γ.idealSheaf y = q.asIdeal := by
        refine eq_of_le_of_height_eq_one' ?_ hle hqh
        rw [hΓ, Ne, Ideal.span_singleton_eq_bot]; exact hz0
      exact hEΓ (MMP.Intersection.eq_of_stalk_idealSheaf_eq hE hΓy (hq.trans heq.symm))
    have hu : IsUnit tE := by
      by_contra hnu
      exact hnot ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
    rw [← halg]
    exact ord_algebraMap_eq_zero_of_isUnit' E rfl hu

/-- A local equation `t` of a prime divisor `Γ` at `y` that is a member of a regular system of
parameters becomes a unit at the generic point of every other prime divisor `E` through `y`. -/
private theorem isUnit_stalkSpecializes_of_stalk_eq_span {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {y : Y} {n : ℕ} {z : Fin n → Y.presheaf.stalk y}
    (hz : MMP.Mori.IsRegularSystemOfParameters z) (i : Fin n) (Γ : MMP.Mori.PrimeDivisor Y)
    (hΓy : y ∈ Γ.support) (hΓ : IdealSheafData.stalk Γ.idealSheaf y = Ideal.span {z i})
    (E : MMP.Mori.PrimeDivisor Y) (hE : y ∈ E.support) (hEΓ : E ≠ Γ) {e : Y}
    (he : e = E.genericPoint) (hsp : e ⤳ y) :
    IsUnit ((Y.presheaf.stalkSpecializes hsp).hom (z i)) := by
  subst he
  haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  have hz0 : z i ≠ 0 := MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz i
  have hnot : z i ∉ MMP.Intersection.primeOfSpecializes hsp := by
    intro hmem
    obtain ⟨q, hqE, hq, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support E hE
    obtain ⟨qΓ, -, hqΓ, hqΓh⟩ :=
      MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support Γ hΓy
    have hpq : MMP.Intersection.primeOfSpecializes hsp = q.asIdeal := by
      have hsp' : Y.fromSpecStalk y q ⤳ y := hqE ▸ hsp
      rw [MMP.Resolution.primeOfSpecializes_congr hqE.symm hsp hsp']
      exact MMP.Resolution.primeOfSpecializes_fromSpecStalk y q hsp'
    have hle : IdealSheafData.stalk Γ.idealSheaf y ≤ q.asIdeal := by
      rw [hΓ, Ideal.span_le, Set.singleton_subset_iff, ← hpq]; exact hmem
    haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk y)
    haveI : (IdealSheafData.stalk Γ.idealSheaf y).IsPrime := by rw [hqΓ]; exact qΓ.2
    have heq : IdealSheafData.stalk Γ.idealSheaf y = q.asIdeal := by
      refine eq_of_le_of_height_eq_one' ?_ hle hqh
      rw [hΓ, Ne, Ideal.span_singleton_eq_bot]; exact hz0
    exact hEΓ (MMP.Intersection.eq_of_stalk_idealSheaf_eq hE hΓy (hq.trans heq.symm))
  by_contra hnu
  exact hnot ((IsLocalRing.mem_maximalIdeal _).mpr hnu)

/-- `tprod` of a constant scalar multiple. -/
private theorem tprod_const_smul {K W : Type*} [Field K] [AddCommGroup W] [Module K W] (m : ℕ)
    (c : K) (w : W) :
    PiTensorProduct.tprod K (fun _ : Fin m => c • w) =
      c ^ m • PiTensorProduct.tprod K (fun _ : Fin m => w) := by
  have := (PiTensorProduct.tprod K : MultilinearMap K (fun _ : Fin m => W) _).map_smul_univ
    (fun _ => c) (fun _ => w)
  rw [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The algebra map from the stalk at the generic point to the function field is the identity. -/
private theorem algebraMap_stalk_genericPoint' (T : Scheme.{0}) [IsIntegral T]
    (z : T.presheaf.stalk (genericPoint T)) :
    @algebraMap (T.presheaf.stalk (genericPoint T)) T.functionField _ _
      (stalkFunctionFieldAlgebra T (genericPoint T)) z = z := by
  change (T.presheaf.stalkSpecializes _).hom z = z
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- Restricting to the generic point of a closed subscheme commutes with specialization: for
`j : C ⟶ S` and `x' ∈ C`, the germ at `j(η_C)` of `b ∈ 𝒪_{S,j(x')}`, restricted to `C`, is the
restriction of `b` to `𝒪_{C,x'}` regarded in `k(C)`. -/
private theorem stalkMap_genericPoint_stalkSpecializes {S C : Scheme.{0}} [IsIntegral C]
    (j : C ⟶ S) (x' : C) (hsp : j (genericPoint C) ⤳ j x')
    (b : S.presheaf.stalk (j x')) :
    (j.stalkMap (genericPoint C)).hom ((S.presheaf.stalkSpecializes hsp).hom b) =
      algebraMap _ C.functionField ((j.stalkMap x').hom b) := by
  have hsp0 : genericPoint C ⤳ x' := (genericPoint_spec C).specializes trivial
  have h := Scheme.Hom.stalkSpecializes_stalkMap j (genericPoint C) x' hsp0
  have h2 := congrArg (fun f => f.hom b) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [h2, ← MMP.Mori.algebraMap_stalkSpecializes hsp0, algebraMap_stalk_genericPoint']

/-- **The residue of a node form along one branch.** Let `j : C ⟶ S` be a closed immersion
onto a prime divisor `P`, `x' ∈ C`, and `(u, v)` a regular system of parameters of `𝒪_{S,j(x')}`
with `P = (u)` and `v` cutting out a second prime divisor `Q ≠ P`. For a unit `a`, the residue
along `C` of `a · (du/u ∧ dv/v)^{⊗m}` is `ā · (dv̄/v̄)^{⊗m}`, with `ā`, `v̄` the restrictions
to `𝒪_{C,x'}`. -/
private theorem isPoincareResidue_smul_tprod_dlog {S C : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)} [IsIntegral C]
    (j : C ⟶ S) [IsClosedImmersion j] {P Q : MMP.Mori.PrimeDivisor S} (hPQ : P ≠ Q)
    (hP : Set.range j.base = (P.support : Set S)) (x' : C) (hxQ : j x' ∈ Q.support)
    {u v a : S.presheaf.stalk (j x')} (hreg : MMP.Mori.IsRegularSystemOfParameters ![u, v])
    (hu : IdealSheafData.stalk P.idealSheaf (j x') = Ideal.span {u})
    (hv : IdealSheafData.stalk Q.idealSheaf (j x') = Ideal.span {v}) (ha : IsUnit a)
    {m : ℕ} {ω : RationalPluriForms sS 2 m}
    (hω : letI := MMP.Mori.functionFieldAlgebra sS
      ω = ((algebraMap _ S.functionField a *
          (algebraMap _ S.functionField u * algebraMap _ S.functionField v)⁻¹ ^ m) •
        PiTensorProduct.tprod S.functionField (fun _ : Fin m =>
          exteriorPower.ιMulti S.functionField 2 (fun i => KaehlerDifferential.D ℂ S.functionField
            (algebraMap _ S.functionField (![u, v] i)))) :
        TensorPower S.functionField m (⋀[S.functionField]^2 Ω[S.functionField⁄ℂ]))) :
    letI := MMP.Mori.functionFieldAlgebra (j ≫ sS)
    IsPoincareResidue sS j 1 m ω
      ((algebraMap _ C.functionField ((j.stalkMap x').hom a) *
          (algebraMap _ C.functionField ((j.stalkMap x').hom v))⁻¹ ^ m) •
        PiTensorProduct.tprod C.functionField (fun _ : Fin m =>
          exteriorPower.ιMulti C.functionField 1 (fun _ => KaehlerDifferential.D ℂ C.functionField
            (algebraMap _ C.functionField ((j.stalkMap x').hom v)))) :
        TensorPower C.functionField m (⋀[C.functionField]^1 Ω[C.functionField⁄ℂ])) := by
  classical
  letI := MMP.Mori.functionFieldAlgebra sS
  letI := MMP.Mori.functionFieldAlgebra (j ≫ sS)
  have hy : j (genericPoint C) = P.genericPoint := MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hP
  have hxP : j x' ∈ P.support := by rw [← hP]; exact ⟨x', rfl⟩
  have hsp0 : genericPoint C ⤳ x' := (genericPoint_spec C).specializes trivial
  have hsp : j (genericPoint C) ⤳ j x' := hsp0.map j.base.hom.continuous
  set sp := (S.presheaf.stalkSpecializes hsp).hom
  have hvu : IsUnit (sp v) :=
    isUnit_stalkSpecializes_of_stalk_eq_span hreg 1 Q hxQ hv P hxP hPQ hy hsp
  have halg : ∀ b, algebraMap _ S.functionField (sp b) = algebraMap _ S.functionField b :=
    fun b => MMP.Mori.algebraMap_stalkSpecializes hsp b
  have hu0 : algebraMap _ S.functionField u ≠ 0 := by
    haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hreg
    intro h
    exact MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hreg 0
      (IsFractionRing.injective (S.presheaf.stalk (j x')) S.functionField
        (h.trans (map_zero _).symm))
  set vinv : S.presheaf.stalk (j (genericPoint C)) := ↑hvu.unit⁻¹ with hvinvdef
  have hvv : vinv * sp v = 1 := hvu.val_inv_mul
  have hvinv : algebraMap _ S.functionField vinv = (algebraMap _ S.functionField v)⁻¹ := by
    rw [← halg v]
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, hvv, map_one])
  have hψinv : (j.stalkMap (genericPoint C)).hom vinv =
      ((j.stalkMap (genericPoint C)).hom (sp v))⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, hvv, map_one])
  refine ⟨sp u, sp a * vinv ^ m, fun _ => sp v, ?_, ?_, ?_⟩
  · rw [halg, hy]
    have := ord_algebraMap_eq_ite_of_stalk_eq_span' hreg 0 P hxP hu P hxP
    rw [if_pos rfl] at this
    exact this
  · rw [hω, tprod_const_smul, smul_smul]
    have hcons : (Fin.cons (KaehlerDifferential.D ℂ S.functionField
          (algebraMap _ S.functionField (sp u)))
        fun _ : Fin 1 => KaehlerDifferential.D ℂ S.functionField
          (algebraMap _ S.functionField (sp v)) : Fin 2 → Ω[S.functionField⁄ℂ]) =
        fun i => KaehlerDifferential.D ℂ S.functionField (algebraMap _ S.functionField
          (![u, v] i)) := by
      funext i
      fin_cases i
      · simp [halg]
      · simp [halg]
    rw [hcons]
    congr 1
    rw [map_mul, map_pow, hvinv, halg, halg]
    rw [mul_inv, mul_pow]
    ring
  · rw [map_mul, map_pow, hψinv]
    simp only [sp, stalkMap_genericPoint_stalkSpecializes j x' hsp]
    rfl

/-- The kernel of a morphism from a reduced scheme is the vanishing ideal of the closure of its
image. -/
private theorem ker_eq_vanishingIdeal' {A B : Scheme.{0}} (g : A ⟶ B) [IsReduced A] :
    g.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range g.base)) := by
  rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
    ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
  simp only [TopologicalSpace.Closeds.coe_top, Set.image_univ]

/-- A closed immersion from a reduced scheme onto a prime divisor `P` has kernel the ideal
of `P`. -/
private theorem ker_eq_idealSheaf' {T Y : Scheme.{0}} [IsLocallyNoetherian Y] (j : T ⟶ Y)
    [IsClosedImmersion j] [IsReduced T] (P : MMP.Mori.PrimeDivisor Y)
    (hP : Set.range j.base = (P.support : Set Y)) : j.ker = P.idealSheaf := by
  rw [ker_eq_vanishingIdeal', ← MMP.Intersection.vanishingIdeal_support_idealSheaf P]
  congr 1
  apply TopologicalSpace.Closeds.ext
  rw [TopologicalSpace.Closeds.coe_closure, hP]
  exact P.idealSheaf.support.isClosed.closure_eq

/-- The kernel of the stalk map of a closed immersion at `y` is the stalk at `ι y` of its
kernel. -/
private theorem ker_stalkMap_eq_stalk_ker' {S W : Scheme.{0}} (ι : S ⟶ W) [IsClosedImmersion ι]
    (y : S) : RingHom.ker (ι.stalkMap y).hom = IdealSheafData.stalk ι.ker (ι y) := by
  have key : ∀ (K : W.IdealSheafData) (t : S ⟶ K.subscheme) [IsIso t],
      RingHom.ker ((t ≫ K.subschemeι).stalkMap y).hom =
        IdealSheafData.stalk K ((t ≫ K.subschemeι) y) := by
    intro K t _
    have : IsIso (t.stalkMap y) :=
      (IsOpenImmersion.iff_isIso_stalkMap.1 (IsOpenImmersion.of_isIso t)).2 y
    rw [Scheme.Hom.stalkMap_comp]
    change RingHom.ker ((t.stalkMap y).hom.comp (K.subschemeι.stalkMap (t y)).hom) =
      IdealSheafData.stalk K (K.subschemeι (t y))
    rw [RingHom.ker_comp_of_injective _ (ConcreteCategory.bijective_of_isIso (t.stalkMap y)).1]
    exact Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk K (t y)
  have e : ι.toImage ≫ ι.ker.subschemeι = ι := ι.toImage_imageι
  have := key ι.ker ι.toImage
  rwa [e] at this

open IsLocalRing in
/-- **A branch through a node is a smooth point of its floor curve.** Let `j : C ⟶ S` be a closed
immersion of an integral normal curve onto a prime divisor `P`, `x' ∈ C`, and `(u, v)` generators
of the maximal ideal of `𝒪_{S,j(x')}` with `P = (u)` there, `j(x')` lying on a second prime
divisor `Q ≠ P`. Then `ū = 0`, `v̄` generates the maximal ideal of `𝒪_{C,x'}`, `x'` has coheight
one, and `v̄` has order one at `x'`. -/
private theorem stalkMap_facts_of_mem_inter {S C : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (j : C ⟶ S) [IsClosedImmersion j] {P Q : MMP.Mori.PrimeDivisor S} (hPQ : P ≠ Q)
    (hP : Set.range j.base = (P.support : Set S)) (hdimC : topologicalKrullDim C = 1) (x' : C)
    (hxQ : j x' ∈ Q.support) {u v : S.presheaf.stalk (j x')}
    (hspan : Ideal.span {u, v} = maximalIdeal (S.presheaf.stalk (j x')))
    (hu : IdealSheafData.stalk P.idealSheaf (j x') = Ideal.span {u}) :
    (j.stalkMap x').hom u = 0 ∧
      Ideal.span {(j.stalkMap x').hom v} = maximalIdeal (C.presheaf.stalk x') ∧
      ∃ hx : Order.coheight x' = 1,
        C.ord (algebraMap _ C.functionField ((j.stalkMap x').hom v)) x' = 1 := by
  classical
  set ψ := (j.stalkMap x').hom
  have hker : RingHom.ker ψ = Ideal.span {u} := by
    rw [ker_stalkMap_eq_stalk_ker', ker_eq_idealSheaf' j P hP, hu]
  have hu0 : ψ u = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self u
  have hmax : Ideal.span {ψ v} = maximalIdeal (C.presheaf.stalk x') := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective ψ (j.stalkMap_surjective x'), ← hspan,
      Ideal.map_span, Set.image_pair, hu0, Ideal.span_insert_zero]
  refine ⟨hu0, hmax, ?_⟩
  -- the coheight of `x'`
  have hgen : genericPoint C ⤳ x' := (genericPoint_spec C).specializes trivial
  have hne : x' ≠ genericPoint C := by
    intro h
    have hy := MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hP
    rw [← h] at hy
    rw [hy] at hxQ
    exact hPQ (MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hxQ)
  have hlt : x' < genericPoint C := lt_of_le_not_ge hgen fun h' => hne (hgen.antisymm h').eq.symm
  have h1 := Order.coheight_add_one_le hlt
  have h2 : (Order.coheight x' : WithBot ℕ∞) ≤ topologicalKrullDim C :=
    coheight_le_topologicalKrullDim _
  rw [hdimC] at h2
  have h3 : Order.coheight x' ≤ 1 := (WithBot.coe_le_coe (a := Order.coheight x') (b := 1)).mp h2
  have hcoh : Order.coheight x' = 1 := by
    refine le_antisymm h3 ?_
    have : (0 : ℕ∞) + 1 ≤ Order.coheight (genericPoint C) + 1 := by gcongr; exact bot_le
    exact (this.trans h1).trans_eq' (by simp)
  refine ⟨hcoh, ?_⟩
  have hdvr : IsDiscreteValuationRing (C.presheaf.stalk x') := by
    let E : MMP.Mori.PrimeDivisor C := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x' hcoh
    have hE : E.genericPoint = x' :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x' hcoh
    have h := E.isDiscreteValuationRing_localRing
    simp only [MMP.Mori.PrimeDivisor.localRing] at h
    rwa [hE] at h
  have hv0 : ψ v ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at hmax
    exact IsDiscreteValuationRing.not_a_field _ hmax.symm
  exact MMP.Fourfold.ord_algebraMap_eq_one_of_irreducible hcoh
    (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hv0 hmax.symm)

/-- The restriction maps of stalks along a morphism over `k` are `k`-algebra maps. -/
private theorem stalkMap_algebraMap' {k : Type} [Field k] {X T : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (j : T ⟶ X) (t : T) (c : k) :
    (j.stalkMap t).hom (letI := MMP.Mori.stalkAlgebra sX (j t); algebraMap k _ c) =
      (letI := MMP.Mori.stalkAlgebra (j ≫ sX) t; algebraMap k _ c) := by
  have h : (Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ sX).appTop ≫
        T.presheaf.germ ⊤ t (TopologicalSpace.Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ (j t) (TopologicalSpace.Opens.mem_top _)) ≫ j.stalkMap t := by
    simp only [Category.assoc, Scheme.Hom.germ_stalkMap, Scheme.Hom.comp_appTop]
    rfl
  exact (congrArg (fun f => f.hom c) h).symm

open IsLocalRing in
/-- **The value of a function at a closed point.** At a closed point `x` of a scheme locally of
finite type over an algebraically closed field `k`, every `a ∈ 𝒪_{X,x}` is congruent to a
constant `c ∈ k` modulo the maximal ideal. -/
private theorem exists_sub_algebraMap_mem_maximalIdeal {k : Type} [Field k] [IsAlgClosed k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (x : X)
    (hx : IsClosed ({x} : Set X)) (a : X.presheaf.stalk x) :
    ∃ c : k, a - (letI := MMP.Mori.stalkAlgebra sX x; algebraMap k _ c) ∈
      maximalIdeal (X.presheaf.stalk x) := by
  letI := MMP.Mori.stalkAlgebra sX x
  have : Module.Finite k (ResidueField (X.presheaf.stalk x)) :=
    MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sX x hx
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
    (K := ResidueField (X.presheaf.stalk x))).2 (residue (X.presheaf.stalk x) a)
  refine ⟨c, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, ← hc, IsScalarTower.algebraMap_apply k
    (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x))]
  exact sub_self _

/-- A local homomorphism into a field kills the maximal ideal. -/
private theorem map_eq_zero_of_mem_maximalIdeal {A K : Type*} [CommRing A] [IsLocalRing A]
    [Field K] (φ : A →+* K) [IsLocalHom φ] {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A) :
    φ a = 0 := by
  by_contra h
  exact ((IsLocalRing.mem_maximalIdeal _).mp ha) (isUnit_of_map_unit φ a (Ne.isUnit h))

/-- **Dimension along a flag.** On a flag of iterated adjunction of length `ℓ` from a variety
of dimension `n`, `ℓ ≤ n` and the final stratum has dimension `n - ℓ`. -/
private theorem length_le_and_topologicalKrullDim_eq {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X} {n : ℕ}
    (hX : topologicalKrullDim X = n) {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S}
    (F : StratumAdjunctionData sX B ι BS) :
    F.length ≤ n ∧ topologicalKrullDim S = ((n - F.length : ℕ) : WithBot ℕ∞) := by
  induction F with
  | refl h => exact ⟨Nat.zero_le _, by rw [hX]; rfl⟩
  | step F j BT h ih =>
    rename_i S₀ T ι₀ BS₀
    obtain ⟨hlen, hdS⟩ := ih
    haveI := F.isIntegral_stratum
    haveI : LocallyOfFiniteType (ι₀ ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
    obtain ⟨-, P, -, hP, hci, -⟩ := h
    have h1 : (Order.coheight P.genericPoint : WithBot ℕ∞) ≤ topologicalKrullDim S₀ :=
      coheight_le_topologicalKrullDim _
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, hdS] at h1
    have h2 : 1 ≤ n - F.length := by
      by_contra hc
      have h0 : n - F.length = 0 := by omega
      rw [h0] at h1
      exact absurd h1 (by decide)
    obtain ⟨d, hd⟩ : ∃ d, n - F.length = d + 1 := ⟨n - F.length - 1, by omega⟩
    have h3 := MMP.Fourfold.topologicalKrullDim_eq_of_range_eq_support (ι₀ ≫ sX) (n := d)
      (by rw [hdS, hd]; push_cast; rfl) j P hP
    refine ⟨by change F.length + 1 ≤ n; omega, ?_⟩
    rw [h3]
    change ((d : ℕ) : WithBot ℕ∞) = ((n - (F.length + 1) : ℕ) : WithBot ℕ∞)
    congr 1
    omega

/-- **The residue at a point of a curve.** Along a closed immersion `j' : T ⟶ C` with
`t ∈ 𝒪_{C,j'(η_T)}` of order one, the residue of `b · (dt/t)^{⊗m}` is `b̄ · 1^{⊗m}`. -/
private theorem isPoincareResidue_smul_tprod_dlog_point {k : Type} [Field k] {C T : Scheme.{0}}
    [IsIntegral C] [IsLocallyNoetherian C] {sC : C ⟶ Spec (.of k)} [IsIntegral T] (j' : T ⟶ C)
    {b t : C.presheaf.stalk (j' (genericPoint T))}
    (ht : C.ord (algebraMap _ C.functionField t) (j' (genericPoint T)) = 1) (m : ℕ) :
    letI := MMP.Mori.functionFieldAlgebra sC
    letI := MMP.Mori.functionFieldAlgebra (j' ≫ sC)
    IsPoincareResidue sC j' 0 m
      ((algebraMap _ C.functionField b * (algebraMap _ C.functionField t)⁻¹ ^ m) •
        PiTensorProduct.tprod C.functionField (fun _ : Fin m =>
          exteriorPower.ιMulti C.functionField 1 (fun _ => KaehlerDifferential.D k C.functionField
            (algebraMap _ C.functionField t))) :
        TensorPower C.functionField m (⋀[C.functionField]^1 Ω[C.functionField⁄k]))
      ((j'.stalkMap (genericPoint T)).hom b •
        (MMP.Fourfold.formPow (k := k) (exteriorPower.ιMulti T.functionField 0 Fin.elim0) m :
          RationalPluriForms (j' ≫ sC) 0 m)) := by
  letI := MMP.Mori.functionFieldAlgebra sC
  letI := MMP.Mori.functionFieldAlgebra (j' ≫ sC)
  refine ⟨t, b, Fin.elim0, ht, ?_, ?_⟩
  · rw [tprod_const_smul, smul_smul, mul_comm (algebraMap _ C.functionField b)]
    congr 2
  · congr 2

/-- **One-step flags from a curve.** For the flag `C ⊃ T` of one adjunction step from `(C, B_C)`,
a Poincaré residue `ρ_T` of `ρ` along `T` is its iterated residue along the flag. -/
private theorem isIteratedResidue_step_refl {k : Type} [Field k] {C : Scheme.{0}}
    {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    {BC : QDivisor C} (h0 : MMP.Mori.IsPair sC BC) {T : Scheme.{0}} {j' : T ⟶ C}
    {BT : QDivisor T} (h' : IsAdjunctionStep (𝟙 C ≫ sC) BC j' BT) {m : ℕ}
    {ρ : RationalPluriForms sC 1 m}
    (σ : @RationalPluriForms k _ T ((j' ≫ 𝟙 C) ≫ sC) h'.1.1.toIsIntegral 0 m)
    (hρT : ∃ ρT : @RationalPluriForms k _ T (j' ≫ sC) h'.1.1.toIsIntegral 0 m,
      @IsPoincareResidue k _ C T sC _ _ h'.1.1.toIsIntegral j' 0 m ρ ρT ∧ HEq σ ρT) :
    @IsIteratedResidue k _ C sC _ _ _ BC 1 m ρ T (j' ≫ 𝟙 C) BT h'.1.1.toIsIntegral
      (.step (.refl h0) j' BT h') 0 σ := by
  haveI : IsIntegral T := h'.1.1.toIsIntegral
  obtain ⟨ρT, hr, hσ⟩ := hρT
  apply IsIteratedResidue.of_rec
  have key : ∀ (s : C ⟶ Spec (.of k)) (hs : s = sC),
      ∃ ρ₀ : RationalPluriForms s 1 m, HEq ρ₀ ρ ∧
        ∃ ρ' : RationalPluriForms (j' ≫ s) 0 m, IsPoincareResidue s j' 0 m ρ₀ ρ' ∧
          HEq ρT ρ' := by
    rintro s rfl
    exact ⟨ρ, HEq.rfl, ρT, hr, HEq.rfl⟩
  obtain ⟨ρ₀, h1, ρ', h2, h3⟩ := key (𝟙 C ≫ sC) (Category.id_comp _)
  exact ⟨ρ₀, ⟨rfl, h1⟩, ρ', h2, hσ.trans h3⟩

/-- Constant degree-zero forms agree along equal structure morphisms. -/
private theorem heq_algebraMap_smul_formPow {k : Type} [Field k] {T : Scheme.{0}} [IsIntegral T]
    {s₁ s₂ : T ⟶ Spec (.of k)} (h : s₁ = s₂) (c : k) (m : ℕ) :
    HEq (letI := MMP.Mori.functionFieldAlgebra s₁
      (algebraMap k T.functionField c •
        MMP.Fourfold.formPow (k := k) (exteriorPower.ιMulti T.functionField 0 Fin.elim0) m :
          RationalPluriForms s₁ 0 m))
      (letI := MMP.Mori.functionFieldAlgebra s₂
      (algebraMap k T.functionField c •
        MMP.Fourfold.formPow (k := k) (exteriorPower.ιMulti T.functionField 0 Fin.elim0) m :
          RationalPluriForms s₂ 0 m)) := by
  subst h
  rfl

end Node

/-- **Floor components of a dlt surface meet in the snc locus** (Kollár–Mori 5.50). If
`(S, B)` is dlt with bad set `Z` (`S ∖ Z` smooth, `B` snc there, and positive log discrepancy
over `Z`), then no point lying on two distinct components of `⌊B⌋` lies in `Z`. -/
private theorem notMem_of_mem_inter_of_isDltPair
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} (hdim : topologicalKrullDim S = 2) {B : QDivisor S}
    (hdlt : MMP.Intersection.IsDltPair sS B) {Z : TopologicalSpace.Closeds S}
    (hpos : ∀ (n : ℕ) (D : Mori.DivisorOver ℂ sS), (D.center : Set S) ⊆ Z →
      ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sS n (Mori.QDivisor.toRDivisor B) D a → 0 < a)
    {P Q : Mori.PrimeDivisor S} (hPQ : P ≠ Q) (hP : 1 ≤ B.coeff P) (hQ : 1 ≤ B.coeff Q)
    {x : S} (hx : x ∈ (P.support : Set S) ∩ Q.support) : x ∉ (Z : Set S) := by
  classical
  obtain ⟨c, hcZ, hxc, hcPQ⟩ := exists_notMem_of_isDltPair' hdlt hpos hPQ hP hQ
    isIrreducible_singleton (Set.singleton_subset_iff.mpr hx)
  have hcmem := hcPQ (subset_closure rfl)
  have hcP : P.genericPoint ⤳ c := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hcmem.1
  have hcne : c ≠ P.genericPoint := by
    rintro rfl
    exact hPQ (MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hcmem.2)
  have hxc' : c ⤳ x := specializes_iff_mem_closure.mpr (hxc rfl)
  by_cases hxe : x = c
  · subst hxe; exact hcZ
  exfalso
  have h1 : c < P.genericPoint :=
    lt_of_le_not_ge hcP fun h' => hcne (Specializes.antisymm hcP h').eq.symm
  have h2 : x < c := lt_of_le_not_ge hxc' fun h' => hxe (Specializes.antisymm hxc' h').eq.symm
  have h4 := Order.coheight_add_one_le h1
  have h5 := Order.coheight_add_one_le h2
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h4
  have h6 : (Order.coheight x : WithBot ℕ∞) ≤ topologicalKrullDim S :=
    coheight_le_topologicalKrullDim _
  rw [hdim] at h6
  have h7 : Order.coheight x ≤ 2 := (WithBot.coe_le_coe (a := Order.coheight x) (b := 2)).mp h6
  have h9 : (1 : ℕ∞) + 1 + 1 ≤ Order.coheight c + 1 := by gcongr
  have h8 : (1 : ℕ∞) + 1 + 1 ≤ 2 := h9.trans (h5.trans h7)
  exact absurd h8 (by decide)

/-- **Floor curves of a dlt pair are dlt.** One adjunction step from a dlt pair onto a prime
divisor gives a dlt pair (`IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair` for the
stratum `P`). -/
private theorem isDltPair_of_isAdjunctionStep {S C : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)} {B : QDivisor S}
    (hdlt : MMP.Intersection.IsDltPair sS B) {j : C ⟶ S} {BC : QDivisor C} [IsIntegral C]
    [IsLocallyNoetherian C] [IsNormal C] (hj : IsAdjunctionStep sS B j BC)
    (P : Mori.PrimeDivisor S) (hP : Set.range j.base = (P.support : Set S)) :
    MMP.Intersection.IsDltPair (j ≫ sS) BC := by
  classical
  obtain ⟨-, P', hP'1, hP', -⟩ := id hj
  have hPP : P' = P := by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    have h1 : P'.genericPoint ∈ (P.support : Set S) := by
      rw [← hP, hP', AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    have h2 : P.genericPoint ∈ (P'.support : Set S) := by
      rw [← hP', hP, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at h1 h2
    exact (h2.antisymm h1).eq
  subst hPP
  have hirr : IsIrreducible (P'.support : Set S) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  have hI : (⋂ R ∈ ({P'} : Finset (Mori.PrimeDivisor S)), (R.support : Set S)) = P'.support := by
    simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left]
  have hS : IsDltStratum sS B (P'.support : Set S) := by
    refine ⟨hdlt, {P'}, Finset.singleton_nonempty _, fun R hR => ?_, ?_, ?_⟩
    · rw [Finset.mem_singleton.mp hR]; exact hP'1
    · rw [hI]; exact hirr.nonempty
    · rw [hI]
      exact ⟨⟨hirr, le_rfl⟩, fun T hT _ => hT.2⟩
  have hj' : IsAdjunctionStep (𝟙 S ≫ sS) B j BC := by rw [Category.id_comp]; exact hj
  have h := (IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair hS).1.2
    (.step (.refl hdlt.1.1) j BC hj') (by simp [hP'])
  have key : ∀ s : C ⟶ Spec (.of ℂ), s = j ≫ sS → MMP.Intersection.IsDltPair s BC →
      MMP.Intersection.IsDltPair (j ≫ sS) BC := by
    rintro s rfl h; exact h
  exact key _ (by simp) h

/-- In even degree, reordering the two factors of a top form leaves its tensor powers
unchanged. -/
private theorem tprod_ιMulti_comp_swap {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    {m : ℕ} (hm : Even m) (w : Fin 2 → W) :
    PiTensorProduct.tprod K (fun _ : Fin m => exteriorPower.ιMulti K 2 (w ∘ Equiv.swap 0 1)) =
      PiTensorProduct.tprod K (fun _ : Fin m => exteriorPower.ιMulti K 2 w) := by
  have h : exteriorPower.ιMulti K 2 (w ∘ Equiv.swap 0 1) = (-1 : K) • exteriorPower.ιMulti K 2 w := by
    rw [AlternatingMap.map_swap (exteriorPower.ιMulti K 2) w (by decide : (0 : Fin 2) ≠ 1),
      neg_one_smul]
  rw [h, tprod_const_smul, hm.neg_one_pow, one_smul]

/-- Transport of a crepant birational map along equalities of structure morphisms. -/
private theorem exists_heq_isCrepantBirationalMap {k : Type} [Field k] {X X' : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X']
    [IsNormal X'] {s₁ s : X ⟶ Spec (.of k)} {s₂ s' : X' ⟶ Spec (.of k)} (e₁ : s₁ = s)
    (e₂ : s₂ = s') {B : QDivisor X} {B' : QDivisor X'} (σ : FunctionFieldEquiv s s')
    (hσ : IsCrepantBirationalMap s s' B B' σ) :
    ∃ σ₁ : FunctionFieldEquiv s₁ s₂, HEq σ₁ σ ∧ IsCrepantBirationalMap s₁ s₂ B B' σ₁ := by
  subst e₁ e₂
  exact ⟨σ, HEq.rfl, hσ⟩

/-- Transport of a pluriform pull-back along equalities of structure morphisms. -/
private theorem pluriformPullback_eq_of_heq {k : Type} [Field k] {X X' : Scheme.{0}}
    [IsIntegral X] [IsIntegral X'] {s₁ s : X ⟶ Spec (.of k)} {s₂ s' : X' ⟶ Spec (.of k)}
    (e₁ : s₁ = s) (e₂ : s₂ = s') {σ₁ : FunctionFieldEquiv s₁ s₂} {σ : FunctionFieldEquiv s s'}
    (hσ : HEq σ₁ σ) {n m : ℕ} {x₁ : RationalPluriForms s₂ n m} {x : RationalPluriForms s' n m}
    (hx : HEq x₁ x) {y₁ : RationalPluriForms s₁ n m} {y : RationalPluriForms s n m}
    (hy : HEq y₁ y) (h : pluriformPullback s₁ s₂ σ₁.toHom n m x₁ = y₁) :
    pluriformPullback s s' σ.toHom n m x = y := by
  subst e₁ e₂
  cases eq_of_heq hσ
  cases eq_of_heq hx
  cases eq_of_heq hy
  exact h

/-- **Admissibility on whole components.** For an admissible system `(t_i)` and a crepant
birational map `σ : (X_i, B_i) ⇢ (X_{i'}, B_{i'})` between two of the pairs, `σ^* t_{i'} = t_i`. -/
private theorem pluriformPullback_eq_of_mem_admissibleSections {k : Type} [Field k] [CharZero k]
    {I : Type} {X : I → Scheme.{0}} {sX : ∀ i, X i ⟶ Spec (.of k)} [∀ i, IsIntegral (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)] {B : ∀ i, QDivisor (X i)} {n m : ℕ}
    (R : ResidueRestriction sX B n m) {t : ∀ i, logPluricanonicalSections (sX i) n m (B i)}
    (ht : t ∈ admissibleSections R) (i i' : I) (σ : FunctionFieldEquiv (sX i) (sX i'))
    (hσ : IsCrepantBirationalMap (sX i) (sX i') (B i) (B i') σ) :
    pluriformPullback (sX i) (sX i') σ.toHom n m (t i' : RationalPluriForms (sX i') n m) =
      (t i : RationalPluriForms (sX i) n m) := by
  have hpi := (R.setting.isPair i).isPair
  have hpi' := (R.setting.isPair i').isPair
  let F : StratumAdjunctionData (sX i) (B i) (𝟙 (X i)) (B i) := .refl hpi
  let F' : StratumAdjunctionData (sX i') (B i') (𝟙 (X i')) (B i') := .refl hpi'
  obtain ⟨σ₁, hσ₁, hcrep⟩ := exists_heq_isCrepantBirationalMap (Category.id_comp (sX i))
    (Category.id_comp (sX i')) σ hσ
  have key := ht i i' F F' n (Nat.zero_le _) (Nat.zero_le _) (R.setting.topologicalKrullDim_eq i)
    (R.setting.topologicalKrullDim_eq i') σ₁ hcrep
  have h1 := IsIteratedResidue.unique (R.isIteratedResidue i F n (t i)
    (R.setting.topologicalKrullDim_eq i)) (IsIteratedResidue.refl hpi)
  have h2 := IsIteratedResidue.unique (R.isIteratedResidue i' F' n (t i')
    (R.setting.topologicalKrullDim_eq i')) (IsIteratedResidue.refl hpi')
  exact pluriformPullback_eq_of_heq (Category.id_comp (sX i)) (Category.id_comp (sX i')) hσ₁
    (by rw [h2]; exact cast_heq _ _) (by rw [h1]; exact cast_heq _ _) key

/-- **Connected unions of closed sets are chained.** If `⋃_{i ∈ J} A_i` is preconnected, for
finitely many nonempty closed sets `A_i`, any two members of `J` are joined by a chain of
meeting sets. -/
private theorem reflTransGen_of_isPreconnected_biUnion {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Finite ι] (A : ι → Set X) (hA : ∀ i, IsClosed (A i)) (hne : ∀ i, (A i).Nonempty)
    {J : Set ι} (hW : _root_.IsPreconnected (⋃ i ∈ J, A i)) {i i' : ι} (hi : i ∈ J) (hi' : i' ∈ J) :
    Relation.ReflTransGen (fun a b => (A a ∩ A b).Nonempty) i i' := by
  classical
  set J₀ := {j | j ∈ J ∧ Relation.ReflTransGen (fun a b => (A a ∩ A b).Nonempty) i j}
  set U₁ := ⋃ j ∈ J₀, A j
  set U₂ := ⋃ j ∈ J \ J₀, A j
  have hU₁ : IsClosed U₁ := (Set.toFinite J₀).isClosed_biUnion fun j _ => hA j
  have hU₂ : IsClosed U₂ := (Set.toFinite (J \ J₀)).isClosed_biUnion fun j _ => hA j
  by_contra hcon
  have hi'0 : i' ∈ J \ J₀ := ⟨hi', fun h => hcon h.2⟩
  have hcov : (⋃ j ∈ J, A j) ⊆ U₁ ∪ U₂ := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, hj, hxj⟩ := hx
    by_cases hj0 : j ∈ J₀
    · exact Or.inl (Set.mem_biUnion hj0 hxj)
    · exact Or.inr (Set.mem_biUnion ⟨hj, hj0⟩ hxj)
  obtain ⟨x, hx⟩ := hne i
  obtain ⟨x', hx'⟩ := hne i'
  have h1 : ((⋃ j ∈ J, A j) ∩ U₁).Nonempty :=
    ⟨x, Set.mem_biUnion hi hx, Set.mem_biUnion (show i ∈ J₀ from ⟨hi, Relation.ReflTransGen.refl⟩) hx⟩
  have h2 : ((⋃ j ∈ J, A j) ∩ U₂).Nonempty :=
    ⟨x', Set.mem_biUnion hi' hx', Set.mem_biUnion hi'0 hx'⟩
  obtain ⟨y, -, hy1, hy2⟩ := (isPreconnected_closed_iff.mp hW) U₁ U₂ hU₁ hU₂ hcov h1 h2
  simp only [U₁, U₂, Set.mem_iUnion] at hy1 hy2
  obtain ⟨j, hj, hyj⟩ := hy1
  obtain ⟨k, hk, hyk⟩ := hy2
  exact hk.2 ⟨hk.1, hj.2.tail ⟨y, hyj, hyk⟩⟩

/-- **Rational pluriforms descend along a birational morphism.** If `f : X ⟶ Z` induces an
isomorphism of function fields, every rational `m`-canonical form on `X` is the pull-back
`f^* τ` of a rational `m`-canonical form `τ` on `Z`. -/
private theorem exists_pullbackRationalPluriForms_eq {X Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Z] {sZ : Z ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sZ] (f : X ⟶ Z) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {n : ℕ}
    (hd : letI := Mori.functionFieldAlgebra sZ; (Algebra.trdeg ℂ Z.functionField).toNat = n)
    {m : ℤ} (ω : RationalPluriForms (f ≫ sZ) n m) :
    ∃ τ : RationalPluriForms sZ n m, Mori.pullbackRationalPluriForms sZ f τ = ω := by
  let := Mori.functionFieldAlgebra sZ
  let := Mori.functionFieldAlgebra (f ≫ sZ)
  let := Mori.functionFieldMapAlgebra f
  have := Mori.isScalarTower_functionFieldMap sZ f
  obtain ⟨ω₀, hω₀⟩ := Mori.exists_isPullbackGenerator_of_bijective sZ f hbij hd
  obtain ⟨g, hg⟩ := hbij.2
    ((Mori.ZTensorPower.basis (Mori.basisOfSpanSingleton hω₀.2.1 hω₀.2.2) m).repr ω ())
  refine ⟨g • Mori.ZTensorPower.basis (Mori.basisOfSpanSingleton hω₀.1 hω₀.ne_zero) m (), ?_⟩
  change Mori.pullbackForms (K := Z.functionField) (K' := X.functionField) m _ = ω
  rw [Mori.pullbackForms_eq hω₀, Mori.pullbackFormsAlong]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_eq_same, smul_eq_mul, mul_one]
  change functionFieldMap f g • _ = ω
  rw [hg]
  exact Mori.basis_unit_repr_smul _ ω

/-- Pull-back along a birational morphism is injective on rational pluriforms. -/
private theorem pullbackRationalPluriForms_injective {S V : Scheme.{0}} [IsIntegral S]
    [IsIntegral V] {sV : V ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sV] (q : S ⟶ V) [IsDominant q]
    (hbij : Function.Bijective (functionFieldMap q)) {n : ℕ}
    (hd : letI := Mori.functionFieldAlgebra sV; (Algebra.trdeg ℂ V.functionField).toNat = n)
    {m : ℤ} : Function.Injective (Mori.pullbackRationalPluriForms (d := n) (m := m) sV q) := by
  letI := Mori.functionFieldAlgebra sV
  letI := Mori.functionFieldAlgebra (q ≫ sV)
  letI := Mori.functionFieldMapAlgebra q
  haveI := Mori.isScalarTower_functionFieldMap sV q
  obtain ⟨ω₀, hω₀⟩ := Mori.exists_isPullbackGenerator_of_bijective sV q hbij hd
  have hform : ∀ τ : RationalPluriForms sV n m, Mori.pullbackRationalPluriForms sV q τ =
      (algebraMap V.functionField S.functionField
        ((Mori.ZTensorPower.basis (Mori.basisOfSpanSingleton hω₀.1 hω₀.ne_zero) m).repr τ ()) •
        Mori.ZTensorPower.basis (Mori.basisOfSpanSingleton hω₀.2.1 hω₀.2.2) m () :
        RationalPluriForms (q ≫ sV) n m) := fun τ =>
    (Mori.pullbackForms_eq hω₀ m τ).trans rfl
  intro a b hab
  rw [hform, hform] at hab
  have hb0 := (Mori.ZTensorPower.basis (Mori.basisOfSpanSingleton hω₀.2.1 hω₀.2.2) m).ne_zero ()
  have h1 := smul_left_injective S.functionField hb0 hab
  have h2 := (algebraMap V.functionField S.functionField).injective h1
  rw [← Mori.basis_unit_repr_smul (Mori.ZTensorPower.basis
      (Mori.basisOfSpanSingleton hω₀.1 hω₀.ne_zero) m) a,
    ← Mori.basis_unit_repr_smul (Mori.ZTensorPower.basis
      (Mori.basisOfSpanSingleton hω₀.1 hω₀.ne_zero) m) b, h2]

/-- A surjective homomorphism of local rings induces a surjection of residue fields. -/
private theorem residueFieldMap_surjective {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X)
    (h : Function.Surjective (f.stalkMap x).hom) : Function.Surjective (f.residueFieldMap x).hom := by
  intro a
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
  obtain ⟨c, rfl⟩ := h b
  refine ⟨Y.residue (f x) c, ?_⟩
  exact congrArg (fun φ => φ.hom c) (Scheme.residue_residueFieldMap f x)

/-- On an integral scheme of dimension one, every point other than the generic point is closed. -/
private theorem isClosed_singleton_of_ne_genericPoint {C : Scheme.{0}} [IsIntegral C]
    (hdim : topologicalKrullDim C = 1) {x : C} (hne : x ≠ genericPoint C) :
    IsClosed ({x} : Set C) := by
  rw [← closure_subset_iff_isClosed]
  intro z hz
  by_contra hzx
  have hsp : x ⤳ z := specializes_iff_mem_closure.mpr hz
  have h1 : z < x := lt_of_le_not_ge hsp fun h => hzx (by
    have := (Specializes.antisymm h hsp).eq
    simp only [Set.mem_singleton_iff]; first | exact this | exact this.symm)
  have h2 : x < genericPoint C := lt_of_le_not_ge
    ((genericPoint_spec C).specializes trivial) fun h => hne
      ((((genericPoint_spec C).specializes trivial).antisymm h).eq.symm)
  have h3 := Order.coheight_add_one_le h1
  have h4 := Order.coheight_add_one_le h2
  have h5 : (Order.coheight z : WithBot ℕ∞) ≤ topologicalKrullDim C :=
    coheight_le_topologicalKrullDim _
  rw [hdim] at h5
  have h6 : Order.coheight z ≤ 1 := (WithBot.coe_le_coe (a := Order.coheight z) (b := 1)).mp h5
  have h7 : Order.coheight (genericPoint C) + 1 + 1 ≤ Order.coheight x + 1 := by gcongr
  have : (0 : ℕ∞) + 1 + 1 ≤ 1 :=
    ((by gcongr; exact bot_le : (0 : ℕ∞) + 1 + 1 ≤ Order.coheight (genericPoint C) + 1 + 1).trans
      (h7.trans h3)).trans h6
  exact absurd this (by decide)

/-- **Proper closed subsets of a curve are finite.** -/
private theorem finite_of_isClosed_of_genericPoint_notMem {C : Scheme.{0}} [IsIntegral C]
    [IsLocallyNoetherian C] [CompactSpace C] (hdim : topologicalKrullDim C = 1) {Z : Set C}
    (hZ : IsClosed Z) (hη : genericPoint C ∉ Z) : Z.Finite := by
  haveI : IsNoetherian C := ⟨⟩
  obtain ⟨S, hSfin, hScl, hSirr, hSZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [hSZ]
  refine hSfin.sUnion fun T hT => ?_
  have hTcl := hScl T hT
  have hTirr := hSirr T hT
  have hTZ : T ⊆ Z := by rw [hSZ]; exact Set.subset_sUnion_of_mem hT
  set ξ := hTirr.genericPoint
  have hξ : IsGenericPoint ξ T := by
    have := hTirr.isGenericPoint_genericPoint_closure
    rwa [hTcl.closure_eq] at this
  have hξZ : ξ ∈ Z := hTZ hξ.mem
  have hξne : ξ ≠ genericPoint C := fun h => hη (h ▸ hξZ)
  rw [← hξ.def, (isClosed_singleton_of_ne_genericPoint hdim hξne).closure_eq]
  exact Set.finite_singleton ξ

/-- **Finite fibres of a map from a curve.** A closed morphism from an integral scheme of
dimension one which does not send the generic point to a closed point has finite fibres. -/
private theorem finite_preimage_singleton_of_curve {C V : Scheme.{0}} [IsIntegral C]
    [IsLocallyNoetherian C] [CompactSpace C] (hdim : topologicalKrullDim C = 1) (ν : C ⟶ V)
    (hν : IsClosedMap ν.base) (hgen : ¬ IsClosed ({ν.base (genericPoint C)} : Set V)) (y : V) :
    (ν.base ⁻¹' {y}).Finite := by
  by_cases hη : ν.base (genericPoint C) = y
  · refine (Set.finite_singleton (genericPoint C)).subset fun x hx => ?_
    by_contra hne
    apply hgen
    rw [hη, ← (show ν.base x = y from hx), ← Set.image_singleton]
    exact hν _ (isClosed_singleton_of_ne_genericPoint hdim hne)
  · rcases (ν.base ⁻¹' {y}).eq_empty_or_nonempty with he | ⟨x, hx⟩
    · rw [he]; exact Set.finite_empty
    refine (finite_of_isClosed_of_genericPoint_notMem hdim
      (isClosed_closure.preimage ν.base.hom.continuous) fun h => ?_).subset
      (Set.preimage_mono subset_closure)
    have h1 : y ⤳ ν.base (genericPoint C) := specializes_iff_mem_closure.mpr h
    have h2 : ν.base (genericPoint C) ⤳ y := by
      rw [← (show ν.base x = y from hx)]
      exact ((genericPoint_spec C).specializes trivial).map ν.base.hom.continuous
    exact hη (h2.antisymm h1).eq

/-- **Normalizations of image curves.** Let `q : S ⟶ V` be a proper birational morphism of
integral schemes onto a normal surface over `ℂ`, and `j : C ⟶ S` a closed immersion of an
integral curve onto a prime divisor `P'` whose image is a prime divisor `P` of `V`. Then
`j ≫ q : C ⟶ P` is finite, has image `P`, and is an isomorphism of residue fields at the generic
point of `C`. -/
private theorem isFinite_and_range_and_isIso_residueFieldMap {S V C : Scheme.{0}} [IsIntegral S]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [IsIntegral C] [IsLocallyNoetherian C]
    [CompactSpace C] {sV : V ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sV]
    (hVdim : topologicalKrullDim V = 2) (q : S ⟶ V) [IsProper q] [IsDominant q]
    [LocallyOfFiniteType q] (hbij : Function.Bijective (functionFieldMap q))
    (j : C ⟶ S) [IsClosedImmersion j] (P' : Mori.PrimeDivisor S)
    (hP' : Set.range j.base = (P'.support : Set S)) (hCdim : topologicalKrullDim C = 1)
    (Pk : Mori.PrimeDivisor V) (hη : q P'.genericPoint = Pk.genericPoint) :
    IsFinite (j ≫ q) ∧ Set.range (j ≫ q).base = (Pk.support : Set V) ∧
      ∃ _ : IsIntegral C, IsIso ((j ≫ q).residueFieldMap (genericPoint C)) := by
  have hjη : j (genericPoint C) = P'.genericPoint :=
    MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P' hP'
  have hνη : (j ≫ q).base (genericPoint C) = Pk.genericPoint := by
    rw [Scheme.Hom.comp_base, TopCat.comp_app, hjη, hη]
  -- the range
  have hrange : Set.range (j ≫ q).base = (Pk.support : Set V) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hP',
      AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← q.isClosedMap.closure_image_eq_of_continuous q.base.hom.continuous, Set.image_singleton,
      hη]
  -- the generic point of `Pk` is not closed
  have hgen : ¬ IsClosed ({(j ≫ q).base (genericPoint C)} : Set V) := by
    intro hc
    rw [hνη] at hc
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sV Pk.genericPoint
    rw [hc.closure_eq, Pk.coheight_genericPoint, hVdim] at h
    have h0 : topologicalKrullDim ({Pk.genericPoint} : Set V) ≤ 0 := by
      haveI : Subsingleton ({Pk.genericPoint} : Set V) := Set.subsingleton_singleton.coe_sort
      haveI : Subsingleton (TopologicalSpace.IrreducibleCloseds ({Pk.genericPoint} : Set V)) :=
        ⟨fun A A' => by
          ext x
          obtain ⟨a, ha⟩ := A.isIrreducible.nonempty
          obtain ⟨a', ha'⟩ := A'.isIrreducible.nonempty
          constructor
          · intro _; rw [Subsingleton.elim x a']; exact ha'
          · intro _; rw [Subsingleton.elim x a]; exact ha⟩
      exact Order.krullDim_nonpos_of_subsingleton
    have h1 : topologicalKrullDim ({Pk.genericPoint} : Set V) + ((1 : ℕ∞) : WithBot ℕ∞) ≤
        0 + ((1 : ℕ∞) : WithBot ℕ∞) := by gcongr
    rw [h] at h1
    exact absurd h1 (by decide)
  haveI : IsProper (j ≫ q) := inferInstance
  haveI : LocallyOfFiniteType (j ≫ q) := inferInstance
  haveI : LocallyQuasiFinite (j ≫ q) := (locallyQuasiFinite_iff_finite_preimage_singleton).mpr
    (finite_preimage_singleton_of_curve hCdim (j ≫ q) (j ≫ q).isClosedMap hgen)
  refine ⟨IsFinite.of_isProper_of_locallyQuasiFinite (j ≫ q), hrange, inferInstance, ?_⟩
  -- the residue field map at the generic point
  have hv : ValuationRing (V.presheaf.stalk (q (j (genericPoint C)))) := by
    rw [hjη, hη]
    have := Pk.isDiscreteValuationRing_localRing
    exact inferInstanceAs (ValuationRing Pk.localRing)
  have hiso : IsIso (q.stalkMap (j (genericPoint C))) :=
    MMP.Positivity.isIso_stalkMap_of_valuationRing q hbij _
  have hsurj : Function.Surjective ((j ≫ q).residueFieldMap (genericPoint C)).hom := by
    intro a
    obtain ⟨b, rfl⟩ := residueFieldMap_surjective j _ (j.stalkMap_surjective _) a
    obtain ⟨c, rfl⟩ := residueFieldMap_surjective q _ (ConcreteCategory.bijective_of_isIso _).2 b
    exact ⟨c, by rw [Scheme.residueFieldMap_comp]; rfl⟩
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨RingHom.injective _, hsurj⟩

/-- **Degree-one horizontal curves are birational to the base.** Let `ν : N ⟶ V` be an
isomorphism of residue fields at the generic point of `N` onto a point `P` with
`[κ(P) : κ(g P)] = 1`, where `g P` is the generic point of `T`. Then `ν ≫ g` induces an
isomorphism of function fields `k(T) ≅ k(N)`. -/
private theorem bijective_functionFieldMap_of_finrank_eq_one {N V T : Scheme.{0}}
    [IsIntegral N] [IsIntegral T] (ν : N ⟶ V) (g : V ⟶ T) [IsDominant (ν ≫ g)]
    (hν : IsIso (ν.residueFieldMap (genericPoint N)))
    (hdeg : (letI := (g.residueFieldMap (ν.base (genericPoint N))).hom.toAlgebra
      Module.finrank (T.residueField (g.base (ν.base (genericPoint N))))
        (V.residueField (ν.base (genericPoint N)))) = 1) :
    Function.Bijective (functionFieldMap (ν ≫ g)) := by
  -- the residue field extension at the generic point of `N` is bijective
  have hg : Function.Bijective (g.residueFieldMap (ν.base (genericPoint N))).hom := by
    letI := (g.residueFieldMap (ν.base (genericPoint N))).hom.toAlgebra
    refine ⟨RingHom.injective _, fun a => ?_⟩
    have htop : (⊤ : Subalgebra (T.residueField (g.base (ν.base (genericPoint N))))
        (V.residueField (ν.base (genericPoint N)))) = ⊥ :=
      (Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr hdeg).symm
    have ha : a ∈ (⊥ : Subalgebra (T.residueField (g.base (ν.base (genericPoint N))))
        (V.residueField (ν.base (genericPoint N)))) := htop ▸ Algebra.mem_top
    obtain ⟨b, hb⟩ := Algebra.mem_bot.mp ha
    exact ⟨b, hb⟩
  have hres : Function.Bijective ((ν ≫ g).residueFieldMap (genericPoint N)).hom := by
    rw [Scheme.residueFieldMap_comp]
    exact (ConcreteCategory.bijective_of_isIso (ν.residueFieldMap (genericPoint N))).comp hg
  have h := residueFieldMap_comp_genericResidueEquivOfDominant (ν ≫ g)
  have h' : (functionFieldMap (ν ≫ g) : T.functionField → N.functionField) =
      (genericResidueEquiv N).symm ∘ ((ν ≫ g).residueFieldMap (genericPoint N)).hom ∘
        (genericResidueEquivOfDominant (ν ≫ g)) := by
    funext a
    have := congrArg (fun φ : T.functionField →+* N.residueField (genericPoint N) => φ a) h
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom] at this
    simp only [Function.comp_apply, this, RingEquiv.symm_apply_apply]
  rw [h']
  exact (genericResidueEquiv N).symm.bijective.comp
    (hres.comp (genericResidueEquivOfDominant (ν ≫ g)).bijective)

/-- **Identifying two curves over a base.** Two dominant morphisms `f₁ : N₁ ⟶ T`, `f₂ : N₂ ⟶ T`
over `k` inducing isomorphisms of function fields give a `k`-isomorphism `k(N₂) ≅ k(N₁)` over
`k(T)`. -/
private theorem exists_functionFieldEquiv_over {k : Type} [Field k] {N₁ N₂ T : Scheme.{0}}
    [IsIntegral N₁] [IsIntegral N₂] [IsIntegral T] (sT : T ⟶ Spec (.of k)) (f₁ : N₁ ⟶ T)
    (f₂ : N₂ ⟶ T) [IsDominant f₁] [IsDominant f₂] (h₁ : Function.Bijective (functionFieldMap f₁))
    (h₂ : Function.Bijective (functionFieldMap f₂)) {s₁ : N₁ ⟶ Spec (.of k)}
    {s₂ : N₂ ⟶ Spec (.of k)} (e₁ : f₁ ≫ sT = s₁) (e₂ : f₂ ≫ sT = s₂) :
    ∃ σ : FunctionFieldEquiv s₁ s₂, ∀ a, σ (functionFieldMap f₂ a) = functionFieldMap f₁ a := by
  subst e₁ e₂
  letI := Mori.functionFieldAlgebra sT
  letI := Mori.functionFieldAlgebra (f₁ ≫ sT)
  letI := Mori.functionFieldAlgebra (f₂ ≫ sT)
  have ht₁ := Mori.isScalarTower_functionFieldMap sT f₁
  have ht₂ := Mori.isScalarTower_functionFieldMap sT f₂
  let e₁ := RingEquiv.ofBijective (functionFieldMap f₁) h₁
  let e₂ := RingEquiv.ofBijective (functionFieldMap f₂) h₂
  have hc₁ : ∀ c : k, functionFieldMap f₁ (algebraMap k T.functionField c) =
      algebraMap k N₁.functionField c := fun c => by
    letI := Mori.functionFieldMapAlgebra f₁
    exact (IsScalarTower.algebraMap_apply k T.functionField N₁.functionField c).symm
  have hc₂ : ∀ c : k, functionFieldMap f₂ (algebraMap k T.functionField c) =
      algebraMap k N₂.functionField c := fun c => by
    letI := Mori.functionFieldMapAlgebra f₂
    exact (IsScalarTower.algebraMap_apply k T.functionField N₂.functionField c).symm
  refine ⟨AlgEquiv.ofRingEquiv (f := e₂.symm.trans e₁) fun c => ?_, fun a => ?_⟩
  · change e₁ (e₂.symm (algebraMap k N₂.functionField c)) = _
    rw [← hc₂, show functionFieldMap f₂ (algebraMap k T.functionField c) =
      e₂ (algebraMap k T.functionField c) from rfl, RingEquiv.symm_apply_apply]
    exact hc₁ c
  · change e₁ (e₂.symm (functionFieldMap f₂ a)) = _
    rw [show functionFieldMap f₂ a = e₂ a from rfl, RingEquiv.symm_apply_apply]
    rfl

/-- **Pull-back of a log coordinate form.** Along a birational morphism `q : S ⟶ V` of integral
schemes over `ℂ` of dimension `n + 1`, the pull-back of `g · (dt/t ∧ dx₁ ∧ ⋯ ∧ dxₙ)^{⊗m}`, with
`t, g, xᵢ ∈ 𝒪_{V,q(s)}` and `dt ∧ dx ≠ 0`, is the same expression in their images in `𝒪_{S,s}`. -/
private theorem pullbackRationalPluriForms_smul_tprod_dlog {S V : Scheme.{0}} [IsIntegral S]
    [IsIntegral V] {sV : V ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sV] (q : S ⟶ V) [IsDominant q]
    (hbij : Function.Bijective (functionFieldMap q)) {n : ℕ}
    (hd : letI := Mori.functionFieldAlgebra sV; (Algebra.trdeg ℂ V.functionField).toNat = n + 1)
    (m : ℕ) (s : S) (t g : V.presheaf.stalk (q s)) (x : Fin n → V.presheaf.stalk (q s))
    (hw0 : letI := Mori.functionFieldAlgebra sV
      exteriorPower.ιMulti V.functionField (n + 1)
        (Fin.cons (KaehlerDifferential.D ℂ V.functionField (algebraMap _ V.functionField t))
          fun i => KaehlerDifferential.D ℂ V.functionField (algebraMap _ V.functionField (x i))) ≠
        0) :
    letI := Mori.functionFieldAlgebra sV
    letI := Mori.functionFieldAlgebra (q ≫ sV)
    Mori.pullbackRationalPluriForms (d := n + 1) (m := m) sV q
      ((algebraMap _ V.functionField g • PiTensorProduct.tprod V.functionField
        (fun _ : Fin m => (algebraMap _ V.functionField t)⁻¹ •
          exteriorPower.ιMulti V.functionField (n + 1)
            (Fin.cons (KaehlerDifferential.D ℂ V.functionField (algebraMap _ _ t))
              fun i => KaehlerDifferential.D ℂ V.functionField (algebraMap _ _ (x i)))) :
          TensorPower V.functionField m (⋀[V.functionField]^(n + 1) Ω[V.functionField⁄ℂ])) :
        RationalPluriForms sV (n + 1) m) =
      ((algebraMap _ S.functionField ((q.stalkMap s).hom g) •
        PiTensorProduct.tprod S.functionField
        (fun _ : Fin m => (algebraMap _ S.functionField ((q.stalkMap s).hom t))⁻¹ •
          exteriorPower.ιMulti S.functionField (n + 1)
            (Fin.cons (KaehlerDifferential.D ℂ S.functionField
                (algebraMap _ _ ((q.stalkMap s).hom t)))
              fun i => KaehlerDifferential.D ℂ S.functionField
                (algebraMap _ _ ((q.stalkMap s).hom (x i))))) :
          TensorPower S.functionField m (⋀[S.functionField]^(n + 1) Ω[S.functionField⁄ℂ])) :
        RationalPluriForms (q ≫ sV) (n + 1) m) := by
  letI := Mori.functionFieldAlgebra sV
  letI := Mori.functionFieldAlgebra (q ≫ sV)
  letI := Mori.functionFieldMapAlgebra q
  haveI := Mori.isScalarTower_functionFieldMap sV q
  set ψ := (q.stalkMap s).hom
  have halg : ∀ a, algebraMap V.functionField S.functionField (algebraMap _ V.functionField a) =
      algebraMap _ S.functionField (ψ a) := fun a =>
    Mori.functionFieldMap_algebraMap_stalk q s a
  set w : ⋀[V.functionField]^(n + 1) Ω[V.functionField⁄ℂ] :=
    exteriorPower.ιMulti V.functionField (n + 1)
      (Fin.cons (KaehlerDifferential.D ℂ V.functionField (algebraMap _ V.functionField t))
        fun i => KaehlerDifferential.D ℂ V.functionField (algebraMap _ V.functionField (x i)))
    with hwdef
  obtain ⟨ω₀, hω₀⟩ := Mori.exists_isPullbackGenerator_of_bijective sV q hbij hd
  have hfin1 : Module.finrank V.functionField
      (⋀[V.functionField]^(n + 1) Ω[V.functionField⁄ℂ]) = 1 := by
    have := Mori.essFiniteType_functionField (sX := sV)
    rw [exteriorPower.finrank_eq, Mori.finrank_kaehlerDifferential_eq_trdeg ℂ V.functionField,
      hd, Nat.choose_self]
  have hgen : Mori.IsPullbackGenerator S.functionField w :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω₀
      ((finrank_eq_one_iff_of_nonzero w hw0).mp hfin1) hw0
  have hpb := MMP.Fourfold.pullbackForms_smul_formPow (K := V.functionField)
    (K' := S.functionField) hgen m
    (algebraMap _ V.functionField g * (algebraMap _ V.functionField t)⁻¹ ^ m)
  change Mori.pullbackForms (K := V.functionField) (K' := S.functionField) m _ = _
  rw [tprod_const_smul, smul_smul]
  change Mori.pullbackForms (K := V.functionField) (K' := S.functionField) m
    ((algebraMap _ V.functionField g * (algebraMap _ V.functionField t)⁻¹ ^ m) •
      MMP.Fourfold.formPow (k := ℂ) w m) = _
  rw [hpb, tprod_const_smul, smul_smul, map_mul, map_pow, map_inv₀, halg, halg]
  congr 1
  rw [hwdef, Mori.topFormsMap_ιMulti]
  congr 2
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.cons_zero, KaehlerDifferential.map_D]; exact congrArg _ (halg t)
  · simp only [Fin.cons_succ, KaehlerDifferential.map_D]; exact congrArg _ (halg (x i))

/-- Coordinate forms agree along equal structure morphisms. -/
private theorem heq_smul_tprod_ιMulti {C : Scheme.{0}} [IsIntegral C]
    {s₁ s₂ : C ⟶ Spec (.of ℂ)} (h : s₁ = s₂) {n m : ℕ} (a : C.functionField)
    (b : Fin n → C.functionField) :
    HEq (letI := Mori.functionFieldAlgebra s₁
      ((a • PiTensorProduct.tprod C.functionField (fun _ : Fin m =>
        exteriorPower.ιMulti C.functionField n (fun i => KaehlerDifferential.D ℂ C.functionField
          (b i))) : TensorPower C.functionField m (⋀[C.functionField]^n Ω[C.functionField⁄ℂ])) :
        RationalPluriForms s₁ n m))
      (letI := Mori.functionFieldAlgebra s₂
      ((a • PiTensorProduct.tprod C.functionField (fun _ : Fin m =>
        exteriorPower.ιMulti C.functionField n (fun i => KaehlerDifferential.D ℂ C.functionField
          (b i))) : TensorPower C.functionField m (⋀[C.functionField]^n Ω[C.functionField⁄ℂ])) :
        RationalPluriForms s₂ n m)) := by
  subst h
  rfl

/-- **Residues pull back to the strict transform.** Let `q : S ⟶ V` be a birational morphism of
normal integral schemes over `ℂ`, an isomorphism of local rings at the generic point of a prime
divisor `P'` of `S` with image the prime divisor `P` of `V`, and `j : C ⟶ S` onto `P'`. If
`ρ = Res_{j ≫ q} τ`, then `ρ = Res_j (q^* τ)`. -/
private theorem isPoincareResidue_pullbackRationalPluriForms {S V C : Scheme.{0}} [IsIntegral S]
    [IsIntegral V] [IsLocallyNoetherian S] [IsLocallyNoetherian V] [IsNormal S] [IsNormal V]
    [IsIntegral C] {sV : V ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sV] (q : S ⟶ V) [IsDominant q]
    (hbij : Function.Bijective (functionFieldMap q)) (j : C ⟶ S)
    (P' : Mori.PrimeDivisor S) (hjη : j (genericPoint C) = P'.genericPoint)
    (Pk : Mori.PrimeDivisor V) (hη : q P'.genericPoint = Pk.genericPoint)
    [IsIso (q.stalkMap P'.genericPoint)] {n : ℕ}
    (hd : letI := Mori.functionFieldAlgebra sV; (Algebra.trdeg ℂ V.functionField).toNat = n + 1)
    {m : ℕ} (hm : 0 < m) {τ : RationalPluriForms sV (n + 1) m} (hτ0 : τ ≠ 0)
    {ρ : RationalPluriForms ((j ≫ q) ≫ sV) n m} (hρ : IsPoincareResidue sV (j ≫ q) n m τ ρ) :
    ∃ ρ' : RationalPluriForms (j ≫ q ≫ sV) n m,
      IsPoincareResidue (q ≫ sV) j n m (Mori.pullbackRationalPluriForms sV q τ) ρ' ∧
        HEq ρ' ρ := by
  classical
  letI := Mori.functionFieldAlgebra sV
  letI := Mori.functionFieldAlgebra (q ≫ sV)
  letI := Mori.functionFieldMapAlgebra q
  haveI := Mori.isScalarTower_functionFieldMap sV q
  letI := Mori.functionFieldAlgebra ((j ≫ q) ≫ sV)
  have hjqη : q.base (j.base (genericPoint C)) = Pk.genericPoint := by rw [hjη, hη]
  have key : ∀ (t g : V.presheaf.stalk (q (j (genericPoint C))))
      (x : Fin n → V.presheaf.stalk (q (j (genericPoint C)))),
      V.ord (algebraMap _ V.functionField t) (q (j (genericPoint C))) = 1 →
      τ = (algebraMap _ V.functionField g • PiTensorProduct.tprod V.functionField
        (fun _ : Fin m => (algebraMap _ V.functionField t)⁻¹ •
          exteriorPower.ιMulti V.functionField (n + 1)
            (Fin.cons (KaehlerDifferential.D ℂ V.functionField (algebraMap _ _ t))
              fun i => KaehlerDifferential.D ℂ V.functionField (algebraMap _ _ (x i)))) :
          TensorPower V.functionField m (⋀[V.functionField]^(n + 1) Ω[V.functionField⁄ℂ])) →
      ρ = (((j ≫ q).stalkMap (genericPoint C)).hom g • PiTensorProduct.tprod C.functionField
        (fun _ : Fin m => exteriorPower.ιMulti C.functionField n
          fun i => KaehlerDifferential.D ℂ C.functionField
            (((j ≫ q).stalkMap (genericPoint C)).hom (x i))) :
          TensorPower C.functionField m (⋀[C.functionField]^n Ω[C.functionField⁄ℂ])) →
      ∃ ρ' : RationalPluriForms (j ≫ q ≫ sV) n m,
        IsPoincareResidue (q ≫ sV) j n m (Mori.pullbackRationalPluriForms sV q τ) ρ' ∧
          HEq ρ' ρ := by
    intro t g x ht hτ hρ
    set ψ := (q.stalkMap (j (genericPoint C))).hom with hψdef
    have hψ : ∀ a, algebraMap _ S.functionField (ψ a) =
        functionFieldMap q (algebraMap _ V.functionField a) := fun a =>
      (Mori.functionFieldMap_algebraMap_stalk q _ a).symm
    set w : ⋀[V.functionField]^(n + 1) Ω[V.functionField⁄ℂ] :=
      exteriorPower.ιMulti V.functionField (n + 1)
        (Fin.cons (KaehlerDifferential.D ℂ V.functionField (algebraMap _ V.functionField t))
          fun i => KaehlerDifferential.D ℂ V.functionField (algebraMap _ V.functionField (x i)))
      with hwdef
    have hτw : τ = (algebraMap _ V.functionField g * (algebraMap _ V.functionField t)⁻¹ ^ m) •
        (MMP.Fourfold.formPow (k := ℂ) w m : RationalPluriForms sV (n + 1) m) := by
      rw [hτ, tprod_const_smul, smul_smul]; rfl
    have hw0 : w ≠ 0 := by
      intro h0
      apply hτ0
      have h1 : PiTensorProduct.tprod V.functionField (fun _ : Fin m =>
          (algebraMap _ V.functionField t)⁻¹ • w) = 0 := by
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        exact MultilinearMap.map_coord_zero _ (0 : Fin (m' + 1)) (by rw [h0, smul_zero])
      rw [hτ, h1]
      exact smul_zero (algebraMap _ V.functionField g)
    -- `w` is a pull-back generator
    obtain ⟨ω₀, hω₀⟩ := Mori.exists_isPullbackGenerator_of_bijective sV q hbij hd
    have hfin1 : Module.finrank V.functionField
        (⋀[V.functionField]^(n + 1) Ω[V.functionField⁄ℂ]) = 1 := by
      have := Mori.essFiniteType_functionField (sX := sV)
      rw [exteriorPower.finrank_eq, Mori.finrank_kaehlerDifferential_eq_trdeg ℂ V.functionField,
        hd, Nat.choose_self]
    have hgen : Mori.IsPullbackGenerator S.functionField w :=
      MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω₀
        ((finrank_eq_one_iff_of_nonzero w hw0).mp hfin1) hw0
    have hpb := MMP.Fourfold.pullbackForms_smul_formPow (K := V.functionField)
      (K' := S.functionField) hgen m
      (algebraMap _ V.functionField g * (algebraMap _ V.functionField t)⁻¹ ^ m)
    have halg : ∀ a, algebraMap V.functionField S.functionField (algebraMap _ V.functionField a) =
        algebraMap _ S.functionField (ψ a) := fun a => (hψ a).symm
    refine ⟨_, ⟨ψ t, ψ g, fun i => ψ (x i), ?_, ?_, rfl⟩, ?_⟩
    · calc S.ord (algebraMap _ S.functionField (ψ t)) (j (genericPoint C))
          = S.ord (functionFieldMap q (algebraMap _ V.functionField t)) (j (genericPoint C)) := by
            rw [hψ]
        _ = S.ord (functionFieldMap q (algebraMap _ V.functionField t)) P'.genericPoint :=
            congrArg _ hjη
        _ = V.ord (algebraMap _ V.functionField t) Pk.genericPoint :=
            MMP.Positivity.ord_functionFieldMap_of_isIso q P' Pk hη _
        _ = 1 := by rw [← hjqη]; exact ht
    · change Mori.pullbackForms (K := V.functionField) (K' := S.functionField) m τ = _
      rw [hτw]
      change Mori.pullbackForms (K := V.functionField) (K' := S.functionField) m
        ((algebraMap _ V.functionField g * (algebraMap _ V.functionField t)⁻¹ ^ m) •
          MMP.Fourfold.formPow (k := ℂ) w m) = _
      rw [hpb, tprod_const_smul, smul_smul, map_mul, map_pow, map_inv₀, halg, halg]
      congr 1
      rw [hwdef, Mori.topFormsMap_ιMulti]
      congr 2
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero, KaehlerDifferential.map_D]; exact congrArg _ (halg t)
      · simp only [Fin.cons_succ, KaehlerDifferential.map_D]; exact congrArg _ (halg (x i))
    · have hcomp : ∀ a : V.presheaf.stalk (q (j (genericPoint C))),
          (j.stalkMap (genericPoint C)).hom (ψ a) = ((j ≫ q).stalkMap (genericPoint C)).hom a :=
        fun a => by rw [Scheme.Hom.stalkMap_comp]; rfl
      rw [hρ]
      simp only [hcomp]
      exact (heq_smul_tprod_ιMulti (Category.assoc j q sV).symm _ _)
  obtain ⟨t, g, x, ht, hτ, hρ⟩ := hρ
  exact key t g x ht hτ hρ

/-- **Residues descend from the strict transform.** In the setting of
`isPoincareResidue_pullbackRationalPluriForms`, if `q^* Ω = ω` and `ρ = Res_j ω`, then `ρ` is
also the residue of `Ω` along `j ≫ q`. -/
private theorem exists_isPoincareResidue_of_pullback_eq {S V C : Scheme.{0}} [IsIntegral S]
    [IsIntegral V] [IsLocallyNoetherian S] [IsLocallyNoetherian V] [IsNormal S] [IsNormal V]
    [IsIntegral C] {sV : V ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sV] (q : S ⟶ V) [IsDominant q]
    (hbij : Function.Bijective (functionFieldMap q)) (j : C ⟶ S)
    (P' : Mori.PrimeDivisor S) (hjη : j (genericPoint C) = P'.genericPoint)
    (Pk : Mori.PrimeDivisor V) (hη : q P'.genericPoint = Pk.genericPoint)
    [IsIso (q.stalkMap P'.genericPoint)] {n : ℕ}
    (hd : letI := Mori.functionFieldAlgebra sV; (Algebra.trdeg ℂ V.functionField).toNat = n + 1)
    {m : ℕ} (hm : 0 < m) {Ω : RationalPluriForms sV (n + 1) m}
    {ω : RationalPluriForms (q ≫ sV) (n + 1) m}
    (hpull : Mori.pullbackRationalPluriForms sV q Ω = ω) (hω0 : ω ≠ 0)
    {ρ : RationalPluriForms (j ≫ q ≫ sV) n m} (hρ : IsPoincareResidue (q ≫ sV) j n m ω ρ) :
    ∃ ρ' : RationalPluriForms ((j ≫ q) ≫ sV) n m,
      IsPoincareResidue sV (j ≫ q) n m Ω ρ' ∧ HEq ρ' ρ := by
  classical
  letI := Mori.functionFieldAlgebra sV
  letI := Mori.functionFieldAlgebra (q ≫ sV)
  letI := Mori.functionFieldAlgebra (j ≫ q ≫ sV)
  letI := Mori.functionFieldAlgebra ((j ≫ q) ≫ sV)
  letI := Mori.functionFieldMapAlgebra q
  haveI := Mori.isScalarTower_functionFieldMap sV q
  haveI : IsIso (q.stalkMap (j (genericPoint C))) := by rw [hjη]; infer_instance
  obtain ⟨tS, gS, xS, ht, hω, hρ⟩ := hρ
  have hsurj : Function.Surjective (q.stalkMap (j (genericPoint C))).hom :=
    (ConcreteCategory.bijective_of_isIso (q.stalkMap (j (genericPoint C)))).2
  obtain ⟨t, rfl⟩ := hsurj tS
  obtain ⟨g, rfl⟩ := hsurj gS
  choose x hx using fun i => hsurj (xS i)
  obtain rfl : xS = fun i => (q.stalkMap (j (genericPoint C))).hom (x i) := funext fun i => (hx i).symm
  have hψ : ∀ a, algebraMap _ S.functionField ((q.stalkMap (j (genericPoint C))).hom a) =
      functionFieldMap q (algebraMap _ V.functionField a) := fun a =>
    (Mori.functionFieldMap_algebraMap_stalk q _ a).symm
  have hwS0 : exteriorPower.ιMulti S.functionField (n + 1)
      (Fin.cons (KaehlerDifferential.D ℂ S.functionField
          (algebraMap _ S.functionField ((q.stalkMap (j (genericPoint C))).hom t)))
        fun i => KaehlerDifferential.D ℂ S.functionField
          (algebraMap _ S.functionField ((q.stalkMap (j (genericPoint C))).hom (x i)))) ≠ 0 := by
    intro h0
    apply hω0
    have h1 : PiTensorProduct.tprod S.functionField (fun _ : Fin m =>
        (algebraMap _ S.functionField ((q.stalkMap (j (genericPoint C))).hom t))⁻¹ •
          exteriorPower.ιMulti S.functionField (n + 1)
            (Fin.cons (KaehlerDifferential.D ℂ S.functionField
                (algebraMap _ S.functionField ((q.stalkMap (j (genericPoint C))).hom t)))
              fun i => KaehlerDifferential.D ℂ S.functionField
                (algebraMap _ S.functionField ((q.stalkMap (j (genericPoint C))).hom (x i))))) =
        0 := by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact MultilinearMap.map_coord_zero _ (0 : Fin (m' + 1)) (by rw [h0, smul_zero])
    rw [hω, h1]
    exact smul_zero (algebraMap _ S.functionField ((q.stalkMap (j (genericPoint C))).hom g))
  have hwV0 : exteriorPower.ιMulti V.functionField (n + 1)
      (Fin.cons (KaehlerDifferential.D ℂ V.functionField (algebraMap _ V.functionField t))
        fun i => KaehlerDifferential.D ℂ V.functionField (algebraMap _ V.functionField (x i))) ≠
      0 := by
    intro h0
    apply hwS0
    have h1 := congrArg (Mori.topFormsMap ℂ V.functionField S.functionField (n + 1)) h0
    rw [Mori.topFormsMap_ιMulti, map_zero] at h1
    rw [← h1]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero, KaehlerDifferential.map_D]
      exact congrArg _ (hψ t)
    · simp only [Fin.cons_succ, KaehlerDifferential.map_D]
      exact congrArg _ (hψ (x i))
  have hform := pullbackRationalPluriForms_smul_tprod_dlog q hbij hd m (j (genericPoint C)) t g x
    hwV0
  -- `Ω` is the coordinate form
  have hΩ : Ω = ((algebraMap _ V.functionField g • PiTensorProduct.tprod V.functionField
      (fun _ : Fin m => (algebraMap _ V.functionField t)⁻¹ •
        exteriorPower.ιMulti V.functionField (n + 1)
          (Fin.cons (KaehlerDifferential.D ℂ V.functionField (algebraMap _ _ t))
            fun i => KaehlerDifferential.D ℂ V.functionField (algebraMap _ _ (x i)))) :
        TensorPower V.functionField m (⋀[V.functionField]^(n + 1) Ω[V.functionField⁄ℂ])) :
      RationalPluriForms sV (n + 1) m) := by
    apply pullbackRationalPluriForms_injective q hbij hd
    rw [hpull, hform, hω]
  have hjqη : (j ≫ q).base (genericPoint C) = Pk.genericPoint := by
    rw [Scheme.Hom.comp_base, TopCat.comp_app, hjη, hη]
  refine ⟨_, ⟨t, g, x, ?_, hΩ, rfl⟩, ?_⟩
  · calc V.ord (algebraMap _ V.functionField t) ((j ≫ q).base (genericPoint C))
        = V.ord (algebraMap _ V.functionField t) Pk.genericPoint := congrArg _ hjqη
      _ = S.ord (functionFieldMap q (algebraMap _ V.functionField t)) P'.genericPoint :=
          (MMP.Positivity.ord_functionFieldMap_of_isIso q P' Pk hη _).symm
      _ = S.ord (algebraMap _ S.functionField ((q.stalkMap (j (genericPoint C))).hom t))
          (j (genericPoint C)) := by
          rw [hψ]; exact congrArg _ hjη.symm
      _ = 1 := ht
  · have hcomp : ∀ a : V.presheaf.stalk (q (j (genericPoint C))),
        ((j ≫ q).stalkMap (genericPoint C)).hom a =
          (j.stalkMap (genericPoint C)).hom ((q.stalkMap (j (genericPoint C))).hom a) :=
      fun a => by rw [Scheme.Hom.stalkMap_comp]; rfl
    rw [hρ]
    simp only [hcomp]
    exact (heq_smul_tprod_ιMulti (Category.assoc j q sV) _ _)

/-- **Powers of a local generator and of its residue.** If `τ` generates `𝒪(a(K + B))` on `U`
and `ρ = Res_T τ` along an adjunction step, then for every `k` the power `τ^{k+1}` generates
`𝒪(a(k+1)(K + B))` on `U`, its residue is `ρ^{k+1}`, and `ord_Q ρ^{k+1} = (k + 1) ord_Q ρ`. -/
private theorem exists_pow_generatesOn_isPoincareResidue {Y T : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    {sY : Y ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY] {BY : QDivisor Y} {j : T ⟶ Y}
    {BT : QDivisor T} (hj : IsAdjunctionStep sY BY j BT) {n : ℕ}
    (hY : topologicalKrullDim Y = n + 1) (hT : topologicalKrullDim T = n) {B : QDivisor Y}
    {U : Y.Opens} {a : ℕ} {τ : RationalPluriForms sY (n + 1) a}
    {ρ : RationalPluriForms (j ≫ sY) n a} (hτ : Mori.GeneratesOn B a U τ) (hρ0 : ρ ≠ 0)
    (hρ : IsPoincareResidue sY j n a τ ρ) (Q : Mori.PrimeDivisor T) :
    ∀ k : ℕ, ∃ (τk : RationalPluriForms sY (n + 1) ((a * (k + 1) : ℕ) : ℤ))
      (ρk : RationalPluriForms (j ≫ sY) n ((a * (k + 1) : ℕ) : ℤ)),
      Mori.GeneratesOn B (a * (k + 1)) U τk ∧ IsPoincareResidue sY j n (a * (k + 1)) τk ρk ∧
        ρk ≠ 0 ∧ Q.ordForm ρk = ((k + 1 : ℕ) : ℤ) * Q.ordForm ρ := by
  haveI : LocallyOfFiniteType (j ≫ sY) := hj.1.1.toLocallyOfFiniteType
  have hY' : topologicalKrullDim Y = ((n + 1 : ℕ) : WithBot ℕ∞) := by rw [hY]; rfl
  have hT' : topologicalKrullDim T = ((n : ℕ) : WithBot ℕ∞) := hT
  intro k
  induction k with
  | zero =>
    have key : ∀ D : ℕ, D = a → ∃ (τk : RationalPluriForms sY (n + 1) (D : ℤ))
        (ρk : RationalPluriForms (j ≫ sY) n (D : ℤ)), Mori.GeneratesOn B D U τk ∧
          IsPoincareResidue sY j n D τk ρk ∧ ρk ≠ 0 ∧
          Q.ordForm ρk = ((0 + 1 : ℕ) : ℤ) * Q.ordForm ρ := by
      rintro D rfl
      exact ⟨τ, ρ, hτ, hρ, hρ0, by simp⟩
    exact key _ (by simp)
  | succ k ih =>
    obtain ⟨τk, ρk, hτk, hρk, hρk0, hordk⟩ := ih
    refine ⟨RationalPluriForms.mul sY (n + 1) (a * (k + 1)) a τk τ,
      RationalPluriForms.mul (j ≫ sY) n (a * (k + 1)) a ρk ρ,
      MMP.Fourfold.GeneratesOn.mul hY' hτk hτ,
      hρk.mul hj hY hρ, RationalPluriForms.mul_ne_zero hT' hρk0 hρ0, ?_⟩
    rw [ordForm_mul Q hρk0 hρ0, hordk]
    push_cast
    ring

/-- **Vertical prime divisors of a Mori fibre space over a curve are fibres.** If every closed
fibre of `g : V ⟶ T` over a curve is irreducible, a prime divisor `E` not dominating `T` is a
whole fibre, so it meets every prime divisor `P` dominating `T`. -/
private theorem inter_nonempty_of_not_horizontal {V T : Scheme.{0}} [IsIntegral V]
    [IsIntegral T] (hVdim : topologicalKrullDim V = 2) (hT1 : topologicalKrullDim T = 1)
    {g : V ⟶ T} (hgc : IsClosedMap g.base) (hgdom : g.base (genericPoint V) = genericPoint T)
    (hirr : ∀ t : T, IsClosed ({t} : Set T) → IsIrreducible (g.base ⁻¹' {t}))
    (E : Mori.PrimeDivisor V) (hE : g.base E.genericPoint ≠ genericPoint T)
    (P : Mori.PrimeDivisor V) (hP : g.base P.genericPoint = genericPoint T) :
    ((E.support : Set V) ∩ P.support).Nonempty := by
  set t := g.base E.genericPoint with ht
  have hcohle : ∀ {X : Scheme.{0}} {n : ℕ}, topologicalKrullDim X = n → ∀ y : X,
      Order.coheight y ≤ n := by
    intro X n hX y
    have h : (Order.coheight y : WithBot ℕ∞) ≤ topologicalKrullDim X :=
      coheight_le_topologicalKrullDim _
    rw [hX] at h
    exact_mod_cast h
  -- `t` is a closed point of the curve `T`
  have htη : t < genericPoint T := lt_of_le_not_ge ((genericPoint_spec T).specializes trivial)
    fun h => hE (((genericPoint_spec T).specializes trivial).antisymm h).eq.symm
  have htc : IsClosed ({t} : Set T) := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    by_contra hne
    have hyt : y < t := lt_of_le_not_ge (specializes_iff_mem_closure.mpr hy) fun h => hne (by
      have := (Specializes.antisymm h (specializes_iff_mem_closure.mpr hy)).eq
      simp only [Set.mem_singleton_iff]
      first | exact this | exact this.symm)
    have h1 := Order.coheight_add_one_le htη
    have h2 := Order.coheight_add_one_le hyt
    have h3 := hcohle (n := 1) (by rw [hT1]; rfl) y
    have h4 : Order.coheight (genericPoint T) + 1 + 1 ≤ Order.coheight t + 1 := by gcongr
    have : (0 : ℕ∞) + 1 + 1 ≤ 1 :=
      ((by gcongr; exact bot_le : (0 : ℕ∞) + 1 + 1 ≤ Order.coheight (genericPoint T) + 1 + 1).trans
        (h4.trans h2)).trans h3
    exact absurd this (by decide)
  -- the fibre over `t` is the support of `E`
  have hcl : IsClosed (g.base ⁻¹' {t}) := htc.preimage g.base.hom.continuous
  have hirrt := hirr t htc
  have hEsub : (E.support : Set V) ⊆ g.base ⁻¹' {t} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr rfl)
  set ξ := hirrt.genericPoint with hξ
  have hξspec : IsGenericPoint ξ (g.base ⁻¹' {t}) := by
    have := hirrt.isGenericPoint_genericPoint_closure
    rwa [hcl.closure_eq] at this
  have hξE : ξ ⤳ E.genericPoint := hξspec.specializes (hEsub (MMP.Flips.primeDivisor_genericPoint_mem_support _))
  have hξt : g.base ξ = t := hξspec.mem
  have hξV : ξ < genericPoint V := lt_of_le_not_ge ((genericPoint_spec V).specializes trivial)
    fun h => hE (by
      rw [← hξt, (((genericPoint_spec V).specializes trivial).antisymm h).eq.symm, hgdom] at ht
      exact ht.symm)
  have hEξ : E.genericPoint = ξ := by
    by_contra hne
    have hlt : E.genericPoint < ξ := lt_of_le_not_ge hξE fun h => hne (hξE.antisymm h).eq.symm
    have h1 := Order.coheight_add_one_le hlt
    have h2 := Order.coheight_add_one_le hξV
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h1
    have h4 : Order.coheight (genericPoint V) + 1 + 1 ≤ Order.coheight ξ + 1 := by gcongr
    have : (0 : ℕ∞) + 1 + 1 ≤ 1 :=
      ((by gcongr; exact bot_le : (0 : ℕ∞) + 1 + 1 ≤ Order.coheight (genericPoint V) + 1 + 1).trans
        h4).trans h1
    exact absurd this (by decide)
  have hfib : g.base ⁻¹' {t} = E.support := by
    rw [← hξspec.def, ← hEξ, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  -- `P` dominates `T`, so it meets the fibre over `t`
  have himg : g.base '' (P.support : Set V) = Set.univ := by
    have hc : IsClosed (g.base '' (P.support : Set V)) := hgc _ P.idealSheaf.support.isClosed
    refine Set.eq_univ_of_forall fun y => ?_
    have hmem : genericPoint T ∈ g.base '' (P.support : Set V) := ⟨P.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support _, hP⟩
    exact ((genericPoint_spec T).specializes trivial).mem_closed hc hmem
  obtain ⟨y, hyP, hyt⟩ := (Set.eq_univ_iff_forall.mp himg) t
  exact ⟨y, hfib ▸ hyt, hyP⟩

/-- **Floor curves of `V` come from floor curves of `S`.** If a closed map `q` sends the floor
of `S` onto the floor of `V`, every floor curve of `V` is the image of a floor curve of `S`. -/
private theorem exists_image_eq_of_image_floor {S V : Scheme.{0}} {B : QDivisor S}
    {BV : QDivisor V} (q : S ⟶ V) (hqc : IsClosedMap q.base)
    (hFimg : q.base '' (⋃ P : {P : Mori.PrimeDivisor S // ⌊B.coeff P⌋ ≠ 0}, (P.1.support : Set S)) = (⋃ E : {E : Mori.PrimeDivisor V // ⌊BV.coeff E⌋ ≠ 0}, (E.1.support : Set V)))
    (E : Mori.PrimeDivisor V) (hE : ⌊BV.coeff E⌋ ≠ 0) :
    ∃ P : {P : Mori.PrimeDivisor S // ⌊B.coeff P⌋ ≠ 0},
      q.base '' (P.1.support : Set S) = E.support := by
  have hηE : E.genericPoint ∈ (E.support : Set V) := MMP.Flips.primeDivisor_genericPoint_mem_support _
  have hEF : E.genericPoint ∈ ⋃ E : {E : Mori.PrimeDivisor V // ⌊BV.coeff E⌋ ≠ 0},
      (E.1.support : Set V) := Set.mem_iUnion.mpr ⟨⟨E, hE⟩, hηE⟩
  rw [← hFimg] at hEF
  obtain ⟨x, hx, hxE⟩ := hEF
  obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
  refine ⟨P, ?_⟩
  have hPη : P.1.genericPoint ∈ (P.1.support : Set S) := MMP.Flips.primeDivisor_genericPoint_mem_support _
  have hsp : q.base P.1.genericPoint ⤳ E.genericPoint := by
    rw [← hxE]
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxP
    exact (specializes_iff_mem_closure.mpr hxP).map q.base.hom.continuous
  -- `q(η_P)` lies on a floor curve of `V`, so it is not the generic point of `V`
  have hqF : q.base P.1.genericPoint ∈ ⋃ E : {E : Mori.PrimeDivisor V // ⌊BV.coeff E⌋ ≠ 0},
      (E.1.support : Set V) := hFimg ▸ ⟨_, Set.mem_iUnion.mpr ⟨P, hPη⟩, rfl⟩
  obtain ⟨E', hE'⟩ := Set.mem_iUnion.mp hqF
  have hEq : q.base P.1.genericPoint = E.genericPoint := by
    by_contra hne
    have hlt : E.genericPoint < q.base P.1.genericPoint :=
      lt_of_le_not_ge hsp fun h => hne (hsp.antisymm h).eq
    have h1 := Order.coheight_add_one_le hlt
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h1
    have h0 : Order.coheight (q.base P.1.genericPoint) = 0 := by
      by_contra h0
      have h2 : 1 ≤ Order.coheight (q.base P.1.genericPoint) := ENat.one_le_iff_ne_zero.mpr h0
      have h3 : (1 : ℕ∞) + 1 ≤ Order.coheight (q.base P.1.genericPoint) + 1 := by gcongr
      exact absurd (h3.trans h1) (by decide)
    have hmax := Order.coheight_eq_zero.mp h0
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hE'
    have hsp' : E'.1.genericPoint ⤳ q.base P.1.genericPoint := specializes_iff_mem_closure.mpr hE'
    have heq : q.base P.1.genericPoint = E'.1.genericPoint := (hsp'.antisymm (hmax hsp')).eq.symm
    have := E'.1.coheight_genericPoint
    rw [← heq, h0] at this
    exact absurd this (by decide)
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    ← hqc.closure_image_eq_of_continuous q.base.hom.continuous, Set.image_singleton, hEq]

end FloorAdjunction

/-! ### The horizontal case over a curve -/

section HorizA

open MMP MMP.Fourfold MMP.Flips
open MMP.Mori hiding IsPair
open FloorAdjunction

/-- **One divisorial step of the program.** The step `q_i : X_i ⟶ X_{i+1}` (`q_i ≫ f_i⁺ = f_i`) is
a proper birational morphism over the base of the program, it maps the floor of `B_i` onto that of
`B_{i+1}` with connected fibres, and every prime divisor of `X_{i+1}` is the image of a prime
divisor of `X_i`, with an isomorphism of local rings and the same coefficient. -/
private theorem exists_step {S Y : Scheme.{0}} [IsIntegral S] [CompactSpace S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    {p : S ⟶ Y} {K : Divisor S} {L B : QDivisor S}
    (P : RelativeDltProgram sS sY p K L) (BU : ∀ i, QDivisor (P.Y i)) (i : ℕ)
    (hi : (i : ℕ∞) < P.n)
    (hBU : BU i = MMP.Mori.RationalMap.transformDivisor (P.φ i) (divisorSeq B BU i))
    (hstep : IsBirationalMorphism (P.f i) ∧
          (∃ E : MMP.Mori.PrimeDivisor (modelSeq S P.Y i),
            (MMP.Mori.exceptionalSet (P.f i) : Set (modelSeq S P.Y i)) = E.support) ∧
          IsIso (P.fp i) ∧
          ∃ q : modelSeq S P.Y i ⟶ P.Y i, q ≫ P.fp i = P.f i ∧
            (∃ (hqY : IsNormalVariety ℂ (q ≫ P.sY i)) (hq : IsBirationalMorphism q),
              MMP.Mori.IsCrepantBoundary (P.sY i) 2 (P.KY i) (BU i) q hqY hq
                (divisorSeq B BU i)) ∧
            ∀ (T T' : Scheme.{0}) (ι : T ⟶ modelSeq S P.Y i) (ι' : T' ⟶ P.Y i)
              [IsClosedImmersion ι] [IsReduced T] [IsClosedImmersion ι'] [IsReduced T'],
              Set.range ι.base =
                  ⋃ E ∈ (divisorSeq B BU i).roundDown.support, (E.support : Set _) →
              Set.range ι'.base = ⋃ E ∈ (BU i).roundDown.support, (E.support : Set _) →
              (∃ h : T ⟶ T', h ≫ ι' = ι ≫ q) ∧
              ∀ h : T ⟶ T', h ≫ ι' = ι ≫ q →
                (∀ U : T'.Opens, IsIso (h.app U)) ∧
                  ∀ t : T', _root_.IsConnected (h.base ⁻¹' {t})) :
    ∃ q : modelSeq S P.Y i ⟶ P.Y i, q ≫ P.sY i = modelStr sS P.sY i ∧ IsProper q ∧
      IsBirationalMorphism q ∧ q ≫ P.πY i = modelMap p P.πY i ∧
      q.base '' floorUnion (divisorSeq B BU i) = floorUnion (BU i) ∧
      (∀ y ∈ floorUnion (BU i),
        _root_.IsPreconnected (q.base ⁻¹' {y} ∩ floorUnion (divisorSeq B BU i))) ∧
      ∀ Γ : MMP.Mori.PrimeDivisor (P.Y i), ∃ Γ' : MMP.Mori.PrimeDivisor (modelSeq S P.Y i),
        q Γ'.genericPoint = Γ.genericPoint ∧ IsIso (q.stalkMap Γ'.genericPoint) ∧
          (BU i).coeff Γ = (divisorSeq B BU i).coeff Γ' := by
  classical
  obtain ⟨hfb, -, hiso, q', hq', -, hfloor⟩ := hstep
  haveI := hiso
  have hst := P.isElementaryDltStep i hi
  have hmi := P.isRelativeDltModel i hi.le
  have hi1 : ((i + 1 : ℕ) : ℕ∞) ≤ P.n := by
    have := Order.add_one_le_of_lt hi
    exact_mod_cast this
  have hmi1 := P.isRelativeDltModel (i + 1) hi1
  have hctr := hst.isNegativeRelativeRayContraction.isNegativeExtremalContraction
  have hmod : IsModificationOf (P.f i) (P.fp i) (P.φ i) := by
    rcases hst.divisorial_or_flip with h' | hflip
    · exact h'.2.2.2
    · exact hflip.isModificationOf
  have hqq : q' = P.f i ≫ inv (P.fp i) := by rw [← hq']; simp
  subst hqq
  set q := P.f i ≫ inv (P.fp i) with hqdef
  have hφ : P.φ i = q.toRationalMap := eq_toRationalMap_of_isOver _ _ _ hmod.2
  have hfg := hst.isNegativeRelativeRayContraction.isRelativeContractionOfFace.comp_eq
  have hZ : IsNormalVariety ℂ (P.sZ i) := hctr.isNormalVariety_target
  haveI : IsIntegral (P.Z i) := hZ.1.toIsIntegral
  haveI : LocallyOfFiniteType (P.sZ i) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (P.Z i) := LocallyOfFiniteType.isLocallyNoetherian (P.sZ i)
  haveI : IsNormal (P.Z i) := hZ.2
  have hqπ : q ≫ P.πY i = modelMap p P.πY i := by
    rw [← hst.comp_eq, ← Category.assoc, hq', hfg]
  have hqs : q ≫ P.sY i = modelStr sS P.sY i := by
    have h1 := hmi1.comp_eq
    have h0 := hmi.comp_eq
    change P.πY i ≫ sY = P.sY i at h1
    rw [← h1, ← Category.assoc, hqπ, h0]
  haveI : IsProper (P.f i) := hctr.isContraction.isProper
  haveI : IsProper q := by rw [hqdef]; infer_instance
  have hqb : IsBirationalMorphism q :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational (inv (P.fp i)) (P.f i)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
        (isBirationalMorphism_of_isIso _))
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb)
  obtain ⟨himg, hfib⟩ := image_eq_and_isPreconnected_of_floorMap q
    (isClosed_floorUnion _) (isClosed_floorUnion _) fun T T' ι ι' _ _ _ _ hι hι' =>
      hfloor T T' ι ι' (by rw [hι, floorUnion_eq]) (by rw [hι', floorUnion_eq])
  have hY : IsNormalVariety ℂ (P.sY i) := hmi1.isQFactorial.1
  have hX : IsNormalVariety ℂ (q ≫ P.sY i) := by rw [hqs]; exact hmi.isQFactorial.1
  refine ⟨q, hqs, inferInstance, hqb, hqπ, himg, hfib, fun Γ => ?_⟩
  obtain ⟨E, hE, hEiso, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hX hqb Γ
  refine ⟨E, hE, hEiso, ?_⟩
  rw [hBU, hφ]
  exact htr _

/-- **The composite of the steps.** Along a program whose steps have the data of `exists_step`,
the composite `S ⟶ X_i` of the first `i` steps is a proper birational morphism over the base,
mapping the floor of `B` onto that of `B_i` with connected fibres, and every prime divisor of
`X_i` is the image of a prime divisor of `S` with an isomorphism of local rings and the same
coefficient. -/
private theorem exists_composite {S Y : Scheme.{0}} [IsIntegral S] [CompactSpace S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    {p : S ⟶ Y} {K : Divisor S} {L B : QDivisor S}
    (P : RelativeDltProgram sS sY p K L) (BU : ∀ i, QDivisor (P.Y i))
    (hBU : ∀ i : ℕ, (i : ℕ∞) < P.n →
      BU i = MMP.Mori.RationalMap.transformDivisor (P.φ i) (divisorSeq B BU i))
    (hstep : ∀ i : ℕ, (i : ℕ∞) < P.n →
        IsBirationalMorphism (P.f i) ∧
          (∃ E : MMP.Mori.PrimeDivisor (modelSeq S P.Y i),
            (MMP.Mori.exceptionalSet (P.f i) : Set (modelSeq S P.Y i)) = E.support) ∧
          IsIso (P.fp i) ∧
          ∃ q : modelSeq S P.Y i ⟶ P.Y i, q ≫ P.fp i = P.f i ∧
            (∃ (hqY : IsNormalVariety ℂ (q ≫ P.sY i)) (hq : IsBirationalMorphism q),
              MMP.Mori.IsCrepantBoundary (P.sY i) 2 (P.KY i) (BU i) q hqY hq
                (divisorSeq B BU i)) ∧
            ∀ (T T' : Scheme.{0}) (ι : T ⟶ modelSeq S P.Y i) (ι' : T' ⟶ P.Y i)
              [IsClosedImmersion ι] [IsReduced T] [IsClosedImmersion ι'] [IsReduced T'],
              Set.range ι.base =
                  ⋃ E ∈ (divisorSeq B BU i).roundDown.support, (E.support : Set _) →
              Set.range ι'.base = ⋃ E ∈ (BU i).roundDown.support, (E.support : Set _) →
              (∃ h : T ⟶ T', h ≫ ι' = ι ≫ q) ∧
              ∀ h : T ⟶ T', h ≫ ι' = ι ≫ q →
                (∀ U : T'.Opens, IsIso (h.app U)) ∧
                  ∀ t : T', _root_.IsConnected (h.base ⁻¹' {t})) :
    ∀ i : ℕ, (i : ℕ∞) ≤ P.n → ∃ q : S ⟶ modelSeq S P.Y i, q ≫ modelStr sS P.sY i = sS ∧
      IsProper q ∧ IsBirationalMorphism q ∧ q ≫ modelMap p P.πY i = p ∧
      q.base '' floorUnion B = floorUnion (divisorSeq B BU i) ∧
      (∀ y ∈ floorUnion (divisorSeq B BU i),
        _root_.IsPreconnected (q.base ⁻¹' {y} ∩ floorUnion B)) ∧
      ∀ Γ : MMP.Mori.PrimeDivisor (modelSeq S P.Y i), ∃ Γ' : MMP.Mori.PrimeDivisor S,
        q Γ'.genericPoint = Γ.genericPoint ∧ IsIso (q.stalkMap Γ'.genericPoint) ∧
          (divisorSeq B BU i).coeff Γ = B.coeff Γ'
  | 0, _ => by
    show ∃ q : S ⟶ S, q ≫ sS = sS ∧ IsProper q ∧ IsBirationalMorphism q ∧ q ≫ p = p ∧
      q.base '' floorUnion B = floorUnion B ∧
      (∀ y ∈ floorUnion B, _root_.IsPreconnected (q.base ⁻¹' {y} ∩ floorUnion B)) ∧
      ∀ Γ : MMP.Mori.PrimeDivisor S, ∃ Γ' : MMP.Mori.PrimeDivisor S,
        q Γ'.genericPoint = Γ.genericPoint ∧ IsIso (q.stalkMap Γ'.genericPoint) ∧
          B.coeff Γ = B.coeff Γ'
    refine ⟨𝟙 S, Category.id_comp _, inferInstance, isBirationalMorphism_of_isIso _,
      Category.id_comp _, ?_, ?_, ?_⟩
    · simp
    · intro y hy
      have : (𝟙 S : S ⟶ S).base ⁻¹' {y} ∩ floorUnion B = {y} := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
          Scheme.Hom.id_base, TopCat.hom_id, ContinuousMap.id_apply]
        constructor
        · exact fun h => h.1
        · rintro rfl; exact ⟨rfl, hy⟩
      rw [this]
      exact isPreconnected_singleton
    · intro Γ
      exact ⟨Γ, rfl, inferInstance, rfl⟩
  | i + 1, hi => by
    have hi' : (i : ℕ∞) < P.n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self i) hi
    obtain ⟨q₀, hs0, hp0, hb0, hπ0, himg0, hfib0, hco0⟩ :=
      exists_composite P BU hBU hstep i hi'.le
    obtain ⟨q₁, hs1, hp1, hb1, hπ1, himg1, hfib1, hco1⟩ :=
      exists_step P BU i hi' (hBU i hi') (hstep i hi')
    haveI := hp0
    haveI := hp1
    have hcomp : ∀ x, (q₀ ≫ q₁).base x = q₁.base (q₀.base x) := fun x => rfl
    show ∃ q : S ⟶ P.Y i, q ≫ P.sY i = sS ∧ IsProper q ∧ IsBirationalMorphism q ∧
      q ≫ P.πY i = p ∧
      q.base '' floorUnion B = floorUnion (BU i) ∧
      (∀ y ∈ floorUnion (BU i), _root_.IsPreconnected (q.base ⁻¹' {y} ∩ floorUnion B)) ∧
      ∀ Γ : MMP.Mori.PrimeDivisor (P.Y i), ∃ Γ' : MMP.Mori.PrimeDivisor S,
        q Γ'.genericPoint = Γ.genericPoint ∧ IsIso (q.stalkMap Γ'.genericPoint) ∧
          (BU i).coeff Γ = B.coeff Γ'
    refine ⟨q₀ ≫ q₁, ?_, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Category.assoc, hs1, hs0]
    · exact MMP.Mori.isBirationalMorphism_comp_of_isBirational q₁ q₀
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb1)
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb0)
    · rw [Category.assoc, hπ1, hπ0]
    · rw [← himg1, ← himg0, Set.image_image]
      rfl
    · intro y hy
      have hsub : q₁.base ⁻¹' {y} ∩ floorUnion (divisorSeq B BU i) ⊆
          floorUnion (divisorSeq B BU i) := Set.inter_subset_right
      have h := isPreconnected_preimage_inter q₀.isClosedMap (isClosed_floorUnion B) himg0
        hfib0 hsub (hfib1 y hy)
      have heq : (q₀ ≫ q₁).base ⁻¹' {y} ∩ floorUnion B =
          q₀.base ⁻¹' (q₁.base ⁻¹' {y} ∩ floorUnion (divisorSeq B BU i)) ∩ floorUnion B := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, hcomp]
        constructor
        · rintro ⟨hx, hxF⟩
          exact ⟨⟨hx, himg0 ▸ ⟨x, hxF, rfl⟩⟩, hxF⟩
        · rintro ⟨⟨hx, -⟩, hxF⟩
          exact ⟨hx, hxF⟩
      rw [heq]
      exact h
    · intro Γ
      obtain ⟨Γ', h1, hiso1, hc1⟩ := hco1 Γ
      obtain ⟨Γ'', h0, hiso0, hc0⟩ := hco0 Γ'
      refine ⟨Γ'', by rw [hcomp, h0, h1], ?_, hc1.trans hc0⟩
      rw [Scheme.Hom.stalkMap_comp]
      have h1' : IsIso (q₁.stalkMap (q₀.base Γ''.genericPoint)) := by rw [h0]; exact hiso1
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1' hiso0

/-- **The final contraction of a program over a projective base is a Mori fibre space.** -/
private theorem isMoriFibreSpace_of_isNegativeRelativeRayContraction' {V T R : Scheme.{0}}
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    {sV : V ⟶ Spec (.of ℂ)} (hV : MMP.Mori.IsProjectiveVariety ℂ sV) (hQ : IsQFactorial sV)
    {n : ℕ} {K : Divisor V} (hK : K.IsCanonicalDivisor sV n) {Δ : QDivisor V}
    (hklt : IsKltPair sV Δ) {sR : R ⟶ Spec (.of ℂ)} (hRp : MMP.Mori.IsProjectiveVariety ℂ sR)
    {π : V ⟶ R} (hπ : π ≫ sR = sV) {sT : T ⟶ Spec (.of ℂ)} {gT : T ⟶ R}
    {g : V ⟶ T} {Rr : Set (RelativeNumericalCurveClasses sV π)}
    (hR : IsNegativeRelativeRayContraction sV π sT (Divisor.toQDivisor K + Δ) Rr g gT)
    (hdim : topologicalKrullDim T < topologicalKrullDim V) :
    IsMoriFibreSpace sV sT K Δ g := by
  have hneg := hR.isNegativeExtremalContraction
  have hface := hR.isRelativeContractionOfFace
  have hgT : g ≫ sT = sV := hneg.isContraction.comp_eq
  have hiso : ∀ U, IsIso (g.app U) := hneg.isContraction.isIso_app
  have hsT : gT ≫ sR = sT := eq_of_comp_eq_of_isIso_app_top g (hiso ⊤)
    (by rw [← Category.assoc, hface.comp_eq, hπ, hgT])
  have hT : MMP.Mori.IsProjectiveVariety ℂ sT :=
    (MMP.Mori.isProjectiveVariety_iff ℂ sT).mpr
      ⟨hneg.isNormalVariety_target.1, hsT ▸ hface.isProjectiveMorphism.comp hRp.isProjective⟩
  have hpt : MMP.Mori.IsProjectiveVariety ℂ (𝟙 (Spec (.of ℂ))) :=
    (MMP.Mori.isProjectiveVariety_iff ℂ _).mpr
      ⟨(MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance,
        inferInstance⟩, MMP.isProjectiveMorphism_of_isClosedImmersion _⟩
  obtain ⟨R', hR', hface', hext', -⟩ := exists_isNegativeRelativeRayContraction hV hT hpt hQ hgT
    (Category.comp_id sT) hneg
  obtain ⟨⟨hDq, -, hRneg⟩, -, -⟩ := hR'
  have hRabs : IsNegativeExtremalRayOf sV (Divisor.toQDivisor K + Δ)
      (relativeToAbsolute sV sV '' R') := by
    refine ⟨hDq, hext', ?_⟩
    rintro _ ⟨u, hu, rfl⟩ hw
    have hu0 : u ≠ 0 := fun h => hw (by rw [h, map_zero])
    have := hRneg u hu hu0
    rwa [relativeCurveForm_eq_comp, LinearMap.comp_apply] at this
  obtain ⟨-, Z', sZ', f', hf', hZ', hρ, hamp⟩ :=
    exists_isContractionOfRay_of_isKltPair sV hV hklt hK hRabs
  haveI : IsProper g :=
    isProper_of_isProjectiveMorphism _ (isProjectiveMorphism_of_isProjectiveVariety hV hT g hgT)
  have hgray : IsContractionOfRay sV sT (relativeToAbsolute sV sV '' R') g :=
    { isNormalVariety_source := hneg.isNormalVariety_source
      isNormalVariety_target := hneg.isNormalVariety_target
      comp_eq := hgT
      isProjectiveMorphism := isProjectiveMorphism_of_isProjectiveVariety hV hT g hgT
      surjective := fun t => (g.isConnected_preimage_singleton_of_isIso_app hiso t).nonempty
      isIso_app := hiso
      isContractedBy_iff := hface'.isContractedBy_iff }
  obtain ⟨-, hρg, hampg⟩ :=
    contraction_data_of_isContractionOfRay hV hext' hgray hf' hZ' hρ hamp
  exact
    { isProjectiveVariety := hV
      isLogCanonicalPair := ⟨hklt.1.isPair, hklt.1.nonneg, fun m D a ha => (hklt.2 m D a ha).le⟩
      isCanonicalDivisor := ⟨n, hK⟩
      isContraction := hgray.toIsContraction
      isProjectiveVariety_target := hT
      relativePicardNumber_eq_one := hρg
      dim_lt := hdim
      hasRelativelyAmpleMultiple := hampg }

/-- A projective morphism with `h_* 𝒪 = 𝒪` between normal varieties is a contraction. -/
private theorem isContraction_of_isIso_app {X R : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sR : R ⟶ Spec (.of ℂ)}
    (hXn : IsNormalVariety ℂ sX) (hRn : IsNormalVariety ℂ sR) (h : X ⟶ R) (hhf : h ≫ sR = sX)
    (hhp : IsProjectiveMorphism h) (hhO : ∀ U : R.Opens, IsIso (h.app U)) :
    IsContraction sX sR h := by
  haveI : IsProper h := isProper_of_isProjectiveMorphism h hhp
  exact { isNormalVariety_source := hXn
          isNormalVariety_target := hRn
          comp_eq := hhf
          isProjectiveMorphism := hhp
          surjective := fun t => (h.isConnected_preimage_singleton_of_isIso_app hhO t).nonempty
          isIso_app := hhO }

/-- Over the spectrum of a field, relative ampleness is ampleness. -/
private theorem isAmple_of_isRelativelyAmple' {k : Type} [Field k] {X : Scheme.{0}}
    (s : X ⟶ Spec (.of k)) (N : X.Modules) [Stacks.Ample.IsInvertibleModule X N]
    (h : MMP.Mori.IsRelativelyAmple s N) : Stacks.Ample.IsAmple X N := by
  obtain ⟨V, -, hyV, hA⟩ := h (IsLocalRing.closedPoint _)
  have hV : V = ⊤ := TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun z => by
    rw [Subsingleton.elim z (IsLocalRing.closedPoint _)]; exact hyV)
  subst hV
  have : IsIso (s ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens)).ι := inferInstanceAs (IsIso X.topIso.hom)
  exact Stacks.RelativeAmpleAffineBase.isAmple_of_isAmple_modulePullback _ N hA

/-- `A / q` is ample for a relatively ample Cartier divisor `A` over `Spec ℂ`. -/
private theorem isAmple_inv_smul {R : Scheme.{0}} [IsLocallyNoetherian R] [CompactSpace R] [IsNormal R]
    {sR : R ⟶ Spec (.of ℂ)} {A : Divisor R} (hAc : A.IsCartier)
    (hAamp : A.IsRelativelyAmple sR hAc) {q : ℕ} (hq : 0 < q) :
    ((q : ℚ)⁻¹ • Divisor.toQDivisor A).IsAmple := by
  have hkq : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  refine ⟨q, hq, A, ?_, hAc, ?_⟩
  · rw [smul_smul, mul_inv_cancel₀ hkq, one_smul]
  · haveI := hAc.isInvertibleModule_divisorialSheaf
    exact isAmple_of_isRelativelyAmple' sR _ hAamp

/-- **The pull-back of `A / q`.** If `W = h^*A` and `M ∼ W` with `M = q(K + B)`, then
`K + B ∼_ℚ h^*(A / q)`. -/
private theorem exists_qLinearlyEquivalent_pullback {X R : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral R] [CompactSpace R] [IsLocallyNoetherian R]
    [IsNormal R] (h : X ⟶ R) [IsDominant h] {A : Divisor R} (hAc : A.IsCartier) {W : Divisor X}
    (hW : ∃ hA, A.IsPullback h hA W) {K : Divisor X} {B : QDivisor X} {q : ℕ} (hq : 0 < q)
    {M : Divisor X} (hMq : Divisor.toQDivisor M = (q : ℤ) • (Divisor.toQDivisor K + B))
    (hMW : M.LinearlyEquivalent W) :
    ∃ (hAq : ((q : ℚ)⁻¹ • Divisor.toQDivisor A).IsQCartier)
      (hη : ∀ Z : irreducibleComponents X,
        h (componentGenericPoint X Z) ∉ ((q : ℚ)⁻¹ • Divisor.toQDivisor A).supp),
      (Divisor.toQDivisor K + B).QLinearlyEquivalent
        (((q : ℚ)⁻¹ • Divisor.toQDivisor A).pullback hAq hη) := by
  obtain ⟨hA0, hW⟩ := hW
  have hHq := isQCartier_inv_smul hAc hq
  have hgen := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' h
    ((q : ℚ)⁻¹ • Divisor.toQDivisor A)
  refine ⟨hHq, hgen, ?_⟩
  rw [(QDivisor.IsQCartier.existsUnique_isPullback hHq hgen).unique
    (QDivisor.isPullback_pullback hHq hgen) (isPullback_inv_smul h hAc hW hq hgen)]
  exact qLinearlyEquivalent_inv_smul hq hMq hMW

/-- **A floor mapping onto a curve is not vertical.** -/
private theorem not_isVertical_of_range_eq_univ {X R : Scheme.{0}} [CompactSpace X] [IsIntegral R]
    (h : X ⟶ R) [IsProper h] {B : QDivisor X}
    (huniv : Set.range (B.roundDown.suppIdeal.subschemeι ≫ h).base = Set.univ)
    (hR1 : topologicalKrullDim R = 1) :
    ¬ QDivisor.IsVertical h (Divisor.toQDivisor B.roundDown) := by
  classical
  intro hv
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    range_suppIdeal_subschemeι] at huniv
  have hη : genericPoint R ∈ h.base '' ⋃ E ∈ B.roundDown.support, (E.support : Set X) := by
    rw [huniv]; trivial
  obtain ⟨x, hx, hxη⟩ := hη
  obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp hx
  have hE0 : (Divisor.toQDivisor B.roundDown) E ≠ 0 := by
    rw [Finsupp.mem_support_iff] at hE
    change ((B.roundDown E : ℤ) : ℚ) ≠ 0
    exact_mod_cast hE
  have hEcl : IsClosed (E.support : Set X) := E.idealSheaf.support.isClosed
  obtain ⟨y, hyE, hyc⟩ := hEcl.exists_closed_singleton ⟨x, hxE⟩
  have hyη : h y = genericPoint R := by
    rw [hv E hE0 y hyE, ← hv E hE0 x hxE]; exact hxη
  have hcl : IsClosed ({genericPoint R} : Set R) := by
    rw [← hyη, ← Set.image_singleton]; exact h.isClosedMap _ hyc
  have huniv' : ({genericPoint R} : Set R) = Set.univ := by
    have := (genericPoint_spec R).def
    rwa [hcl.closure_eq] at this
  haveI : Subsingleton R := ⟨fun a b => by
    have ha : a ∈ ({genericPoint R} : Set R) := by rw [huniv']; trivial
    have hb : b ∈ ({genericPoint R} : Set R) := by rw [huniv']; trivial
    rw [Set.mem_singleton_iff] at ha hb
    rw [ha, hb]⟩
  haveI : DiscreteTopology R := ⟨Subsingleton.elim _ _⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology R
  rw [hR1] at h0
  exact absurd h0 (by decide)

/-- **The endpoint of the floor-lowering program over a curve.** For a `ℚ`-factorial projective
dlt surface `(S, B)` with `K + B ∼_ℚ h^*A` for an ample `A` on a normal projective curve `R`
and a horizontal floor, the floor-lowering program over `R` ends with a Mori fibre space
`g : V ⟶ T` over `R`, reached by a proper birational morphism `q : S ⟶ V` over `R` which maps
the floor onto the floor with connected fibres and under which every prime divisor of `V` is a
strict transform with the same coefficient. -/
private theorem exists_endpoint
    {S R : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} (hS : Mori.IsProjectiveVariety ℂ sS)
    (hdim : topologicalKrullDim S = 2)
    (hQ : IsQFactorial sS) {B : QDivisor S}
    (hdlt : MMP.Intersection.IsDltPair sS B) {K : Divisor S} (hK : K.IsCanonicalDivisor sS 2)
    [CompactSpace R] [IsLocallyNoetherian R] [IsNormal R] {sR : R ⟶ Spec (.of ℂ)}
    (hRp : Mori.IsProjectiveVariety ℂ sR) {h : S ⟶ R} (hp : IsContraction sS sR h)
    (hR1 : topologicalKrullDim R ≤ 1) {A : QDivisor R} (hA : A.IsAmple)
    (hDA : ∃ (hAq : A.IsQCartier)
      (hη : ∀ Z : irreducibleComponents S, h (componentGenericPoint S Z) ∉ A.supp),
      (Divisor.toQDivisor K + B).QLinearlyEquivalent (A.pullback hAq hη))
    (hhor : ¬ QDivisor.IsVertical h (Divisor.toQDivisor B.roundDown)) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : CompactSpace V) (_ : IsLocallyNoetherian V)
      (_ : IsNormal V) (sV : V ⟶ Spec (.of ℂ)) (q : S ⟶ V) (πV : V ⟶ R) (KV : Divisor V)
      (BV : QDivisor V) (ε : ℚ) (T : Scheme.{0}) (_ : IsIntegral T) (sT : T ⟶ Spec (.of ℂ))
      (g : V ⟶ T) (gT : T ⟶ R),
      q ≫ sV = sS ∧ IsProper q ∧ IsBirationalMorphism q ∧ q ≫ πV = h ∧ g ≫ gT = πV ∧
      Mori.IsProjectiveVariety ℂ sV ∧ topologicalKrullDim V = 2 ∧ IsQFactorial sV ∧
      KV.IsCanonicalDivisor sV 2 ∧ MMP.Intersection.IsLogCanonicalPair sV BV ∧
      (0 < ε ∧ ε < 1) ∧ IsKltPair sV (BV - ε • Divisor.toQDivisor BV.roundDown) ∧
      IsDominant g ∧ IsMoriFibreSpace sV sT KV (BV - ε • Divisor.toQDivisor BV.roundDown) g ∧
      q.base '' floorUnion B = floorUnion BV ∧
      (∀ y ∈ floorUnion BV, _root_.IsPreconnected (q.base ⁻¹' {y} ∩ floorUnion B)) ∧
      (∀ Γ : Mori.PrimeDivisor V, ∃ Γ' : Mori.PrimeDivisor S,
        q Γ'.genericPoint = Γ.genericPoint ∧ IsIso (q.stalkMap Γ'.genericPoint) ∧
          BV.coeff Γ = B.coeff Γ') := by
  classical
  have hSv : Mori.IsVariety ℂ sS := ((Mori.isProjectiveVariety_iff ℂ sS).mp hS).1
  haveI := hSv
  haveI : LocallyOfFiniteType sS := hSv.toLocallyOfFiniteType
  obtain ⟨P, BU, hn, hproj, -, hBU, hmod, hstep, hfin, -⟩ :=
    IsContraction.exists_relativeDltProgram_sub_smul_roundDown hS hdim hQ hK hdlt hp
      hRp hR1 hA hDA (1 / 2) ⟨by norm_num, by norm_num⟩
  have hfinal : P.hasFinal := hfin (Or.inl hhor)
  obtain ⟨-, hR, hdimT⟩ := P.final_spec hfinal
  have hnn : ((P.n.toNat : ℕ) : ℕ∞) ≤ P.n := by rw [ENat.coe_toNat hn]
  obtain ⟨q, hqs, hqp, hqb, hqπ, himg, hfib, hco⟩ := exists_composite P BU hBU hstep _ hnn
  have hm := P.isRelativeDltModel _ hnn
  obtain ⟨hlow, hklt, hlc⟩ := hmod _ hnn
  have hVv : Mori.IsVariety ℂ (modelStr sS P.sY P.n.toNat) := hm.isQFactorial.1.1
  haveI := hVv
  haveI : LocallyOfFiniteType (modelStr sS P.sY P.n.toNat) := hVv.toLocallyOfFiniteType
  have hVdim : topologicalKrullDim (modelSeq S P.Y P.n.toNat) = 2 := by
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism
      (modelStr sS P.sY P.n.toNat) sS hqb, hdim]
  obtain ⟨mK, hmK⟩ := hm.isCanonicalDivisor
  have hmK2 : mK = 2 := by
    have h := hmK.topologicalKrullDim_eq
    rw [hVdim] at h
    exact_mod_cast h.symm
  subst hmK2
  rw [hlow] at hklt hR
  have hMFS := isMoriFibreSpace_of_isNegativeRelativeRayContraction' (hproj.2 _ hnn)
    hm.isQFactorial hmK hklt hRp hm.comp_eq hR hdimT
  haveI : IsIntegral P.T := hMFS.isProjectiveVariety_target.toIsVariety.toIsIntegral
  exact ⟨modelSeq S P.Y P.n.toNat, inferInstance, inferInstance, inferInstance, inferInstance,
    modelStr sS P.sY P.n.toNat, q, modelMap h P.πY P.n.toNat, divisorSeq K P.KY P.n.toNat,
    divisorSeq B BU P.n.toNat, 1 / 2, P.T, inferInstance, P.sT, P.g, P.gT, hqs, hqp, hqb, hqπ,
    hR.isRelativeContractionOfFace.comp_eq, hproj.2 _ hnn, hVdim, hm.isQFactorial,
    hmK, hlc, ⟨by norm_num, by norm_num⟩, hklt,
    ⟨hMFS.isContraction.surjective.denseRange⟩, hMFS, himg, hfib, hco⟩

/-- **A local frame of the adjoint pulled back from the base.** Let `M = q(K + B)` be linearly
equivalent to `W = h^*A` for a Cartier divisor `A` on `R`, and let `h` factor as `h' ≫ gT`.
There is a nonzero rational `q`-canonical form `Ω` with `div Ω + qB = W`; near every point of
`T` some `e ∈ k(T)` makes `h'^* e · Ω` a generator of `𝒪(q(K + B))` over the preimage. -/
private theorem exists_frame {X T R : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hXn : IsNormalVariety ℂ sX)
    (hdim : topologicalKrullDim X = 2) [IsIntegral T] [IsIntegral R] [IsLocallyNoetherian R]
    [IsNormal R] (h : X ⟶ R) [IsDominant h] (h' : X ⟶ T) [IsDominant h'] (gT : T ⟶ R)
    [IsDominant gT] (hh : h' ≫ gT = h) {A : Divisor R} (hAc : A.IsCartier) {W : Divisor X}
    (hW : ∃ hA, A.IsPullback h hA W) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2)
    {B : QDivisor X} {q : ℕ} (hq : 0 < q) {M : Divisor X}
    (hMq : Divisor.toQDivisor M = (q : ℤ) • (Divisor.toQDivisor K + B))
    (hMW : M.LinearlyEquivalent W) :
    ∃ Ω : RationalPluriForms sX 2 q, Ω ≠ 0 ∧ ∀ t : T, ∃ U : T.Opens, t ∈ U ∧
      ∃ e : T.functionField, e ≠ 0 ∧ GeneratesOn B q (h' ⁻¹ᵁ U) (functionFieldMap h' e • Ω) := by
  classical
  haveI : LocallyOfFiniteType sX := hXn.1.toLocallyOfFiniteType
  have hdim2 : topologicalKrullDim X = ((2 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  obtain ⟨hA0, hW⟩ := hW
  obtain ⟨ω₀, hω₀0, hω₀K⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXn hK
  obtain ⟨φ, hφ⟩ := hMW
  let Z₀ := MMP.Mori.pointComponent (genericPoint X)
  set f : X.functionField := (MMP.Positivity.componentToFunctionField Z₀).hom (φ.val Z₀)
    with hfdef
  have hf0 : f ≠ 0 := ((φ.isUnit.map (Pi.evalRingHom _ Z₀)).map _).ne_zero
  have hordf : ∀ Γ : Mori.PrimeDivisor X, X.ord f Γ.genericPoint = M.coeff Γ - W.coeff Γ := by
    intro Γ
    have h1 := MMP.Positivity.ord_eq_ord_componentToFunctionField Γ φ
    have hZ : Γ.component = Z₀ := Subsingleton.elim
      (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
    rw [hZ, ← hfdef] at h1
    have h2 := congrArg (fun G : Divisor X => G.coeff Γ) hφ
    simp only [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor] at h2
    rw [← h1, h2]
  obtain ⟨Q, rfl⟩ : ∃ Q, q = Q + 1 := ⟨q - 1, by omega⟩
  letI := MMP.Mori.functionFieldAlgebra sX
  set τ := MMP.CyclicChartDifferent.Aux.pluriPow ω₀ Q with hτdef
  have hτ0 : τ ≠ 0 := MMP.CyclicChartDifferent.Aux.pluriPow_ne_zero hdim2 hω₀0 Q
  have hfi0 : f⁻¹ ≠ 0 := inv_ne_zero hf0
  refine ⟨f⁻¹ • τ, smul_ne_zero hfi0 hτ0, fun t => ?_⟩
  obtain ⟨U, hU, φA, hφA⟩ := hAc (gT t)
  have Z₁ : irreducibleComponents R := MMP.Mori.pointComponent (genericPoint R)
  set a := MMP.Threefold.Mori.Helpers.evalFF Z₁ (φA : MMP.Mori.RationalFunctions R) with hadef
  have ha0 : a ≠ 0 := (φA.isUnit.map (MMP.Threefold.Mori.Helpers.evalFF Z₁)).ne_zero
  refine ⟨gT ⁻¹ᵁ U, hU, (functionFieldMap gT a)⁻¹, inv_ne_zero ((map_ne_zero _).mpr ha0), ?_⟩
  have hga : functionFieldMap h' (functionFieldMap gT a)⁻¹ = (functionFieldMap h a)⁻¹ := by
    rw [map_inv₀, MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hh]
  rw [hga]
  have hha0 : (functionFieldMap h a)⁻¹ ≠ 0 := inv_ne_zero ((map_ne_zero _).mpr ha0)
  refine ⟨smul_ne_zero hha0 (smul_ne_zero hfi0 hτ0), fun Γ hΓ => ?_⟩
  have hηΓ : Γ.genericPoint ∈ h' ⁻¹ᵁ (gT ⁻¹ᵁ U) := (Γ.genericPoint_mem_iff _).mpr hΓ
  have hηU : h Γ.genericPoint ∈ U := by
    rw [← hh]; exact hηΓ
  have hWΓ := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hW hφA Γ hηU Z₁
  rw [← hadef] at hWΓ
  rw [Γ.ordForm_smul_of_topologicalKrullDim_eq hdim2 hha0 (smul_ne_zero hfi0 hτ0),
    Γ.ordForm_smul_of_topologicalKrullDim_eq hdim2 hfi0 hτ0, hτdef,
    MMP.CyclicChartDifferent.Aux.ordForm_pluriPow hdim2 hω₀0 Γ Q, hω₀K Γ,
    scheme_ord_inv ((map_ne_zero _).mpr ha0), scheme_ord_inv hf0, hordf Γ, ← hWΓ]
  have h1 := congrArg (fun G : QDivisor X => G.coeff Γ) hMq
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
    zsmul_eq_mul] at h1
  push_cast at h1 ⊢
  rw [h1]
  ring

/-- The order along `E` of a unit of the stalk at a point `x ∈ E` is zero. -/
private theorem ord_algebraMap_eq_zero_of_isUnit_of_mem {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (E : Mori.PrimeDivisor X) {x : X}
    (hx : x ∈ E.support) {a : X.presheaf.stalk x} (ha : IsUnit a) :
    X.ord (algebraMap _ X.functionField a) E.genericPoint = 0 := by
  have hsp : E.genericPoint ⤳ x := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
    exact specializes_iff_mem_closure.mpr hx
  rw [← MMP.Mori.algebraMap_stalkSpecializes hsp a]
  exact E.ord_algebraMap_of_isUnit (ha.map _)

/-- **The frame on the endpoint.** A frame `h'^*e · Ω` of the adjoint on `X` descends to a frame
`g^*e · Ω_V` on `V`, for `q : X ⟶ V` a birational morphism over `T` under which every prime
divisor of `V` is a strict transform with the same coefficient, and `q^*Ω_V = Ω`. -/
private theorem exists_frame_endpoint {X V T : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [IsIntegral T]
    {sV : V ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sV] (hVdim : topologicalKrullDim V = 2)
    (q : X ⟶ V) [IsDominant q] (hqb : IsBirationalMorphism q) (g : V ⟶ T) [IsDominant g]
    [IsDominant (q ≫ g)] {B : QDivisor X} {BV : QDivisor V}
    (hcoef : ∀ Γ : Mori.PrimeDivisor V, ∃ Γ' : Mori.PrimeDivisor X,
      q Γ'.genericPoint = Γ.genericPoint ∧ IsIso (q.stalkMap Γ'.genericPoint) ∧
        BV.coeff Γ = B.coeff Γ')
    {m : ℕ} {Ω : RationalPluriForms (q ≫ sV) 2 m} (hΩ0 : Ω ≠ 0)
    (hfr : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ e : T.functionField, e ≠ 0 ∧
      GeneratesOn (sX := q ≫ sV) B m ((q ≫ g) ⁻¹ᵁ U) (functionFieldMap (q ≫ g) e • Ω)) :
    ∃ ΩV : RationalPluriForms sV 2 m, pullbackRationalPluriForms sV q ΩV = Ω ∧ ΩV ≠ 0 ∧
      ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ e : T.functionField, e ≠ 0 ∧
        GeneratesOn BV m (g ⁻¹ᵁ U) (functionFieldMap g e • ΩV) ∧
        GeneratesOn (sX := q ≫ sV) B m ((q ≫ g) ⁻¹ᵁ U) (functionFieldMap (q ≫ g) e • Ω) := by
  classical
  have hbij := hqb.functionFieldMap_bijective
  have hd : (letI := Mori.functionFieldAlgebra sV
      (Algebra.trdeg ℂ V.functionField).toNat) = 2 :=
    Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (by rw [hVdim]; rfl)
  obtain ⟨ΩV, hΩV⟩ := exists_pullbackRationalPluriForms_eq q hbij hd Ω
  have hΩV0 : ΩV ≠ 0 := by
    rintro rfl
    apply hΩ0
    rw [← hΩV]
    have h := pullbackRationalPluriForms_smul' q (0 : V.functionField)
      (0 : RationalPluriForms sV 2 m)
    rw [zero_smul, map_zero, zero_smul] at h
    exact h
  refine ⟨ΩV, hΩV, hΩV0, fun t => ?_⟩
  obtain ⟨U, hU, e, he, hgen⟩ := hfr t
  refine ⟨U, hU, e, he, ⟨smul_ne_zero ((map_ne_zero _).mpr he) hΩV0, fun Γ hΓ => ?_⟩, hgen⟩
  obtain ⟨Γ', h1, hiso, hc⟩ := hcoef Γ
  haveI := hiso
  have hpb := MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso q hbij hd Γ' Γ h1
    (functionFieldMap g e • ΩV)
  rw [pullbackRationalPluriForms_smul', hΩV,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply] at hpb
  have hηΓ : Γ.genericPoint ∈ g ⁻¹ᵁ U := (Γ.genericPoint_mem_iff _).mpr hΓ
  have hΓ' : (Γ'.support ∩ ((q ≫ g) ⁻¹ᵁ U : Set X)).Nonempty :=
    ⟨Γ'.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support Γ', show g (q Γ'.genericPoint) ∈ U by
      rw [h1]; exact hηΓ⟩
  have := hgen.2 Γ' hΓ'
  rw [← hpb, hc]
  exact this

/-- **A Cartier divisor missing a curve has degree zero on it.** On a `ℚ`-factorial variety,
write `D = P - N` with `P, N ≥ 0` missing the curve; a common multiple makes both Cartier, and
effective Cartier divisors missing the curve have degree zero. -/
private theorem degreeOn_eq_zero_of_forall_notMem_supp {X C : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] (hQ : IsQFactorial sX)
    (i : C ⟶ X) [IsProper (i ≫ sX)] [IsIntegral C] (hdim : topologicalKrullDim C ≤ 1)
    {D : Divisor X} (hD : D.IsCartier) (hdis : ∀ c : C, i c ∉ D.supp) :
    D.degreeOn ℂ sX i hdim hD = 0 := by
  classical
  obtain ⟨c₀⟩ : Nonempty C := ⟨genericPoint C⟩
  let P : Divisor X := Finsupp.mapRange (fun a : ℤ => max a 0) (by simp) D
  let N : Divisor X := Finsupp.mapRange (fun a : ℤ => max (-a) 0) (by simp) D
  have hPc : ∀ Γ, P.coeff Γ = max (D.coeff Γ) 0 := fun Γ => Finsupp.mapRange_apply ..
  have hNc : ∀ Γ, N.coeff Γ = max (-D.coeff Γ) 0 := fun Γ => Finsupp.mapRange_apply ..
  obtain ⟨a, ha, haP⟩ := hQ.2 P
  obtain ⟨b, hb, hbN⟩ := hQ.2 N
  have hP' : (((b : ℕ) : ℤ) • ((a : ℤ) • P)).IsCartier := haP.zsmul _
  have hN' : (((a : ℕ) : ℤ) • ((b : ℤ) • N)).IsCartier := hbN.zsmul _
  have hnD : ((a * b : ℕ) • D).IsCartier := hD.nsmul _
  have hsum : (a * b : ℕ) • D + ((a : ℤ) • ((b : ℤ) • N)) = ((b : ℤ) • ((a : ℤ) • P)) := by
    ext Γ
    change ((a * b : ℕ) • D + ((a : ℤ) • ((b : ℤ) • N))).coeff Γ =
      ((((b : ℕ) : ℤ) • ((a : ℤ) • P))).coeff Γ
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, hPc, hNc, smul_eq_mul,
      nsmul_eq_mul]
    push_cast
    rcases le_total 0 (D.coeff Γ) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hsupp : ∀ (E : Divisor X) (hE : ∀ Γ, E.coeff Γ ≠ 0 → D.coeff Γ ≠ 0) (c : C),
      i c ∉ E.supp := by
    intro E hE c hc
    obtain ⟨Γ, hΓ, hcΓ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hc
    exact hdis c (DivisorWithCoeffs.mem_supp_iff.mpr ⟨Γ, hE Γ hΓ, hcΓ⟩)
  have hdeg0 : ∀ (E : Divisor X) (hEc : E.IsCartier), 0 ≤ E →
      (∀ Γ, E.coeff Γ ≠ 0 → D.coeff Γ ≠ 0) → E.degreeOn ℂ sX i hdim hEc = 0 := by
    intro E hEc hE0 hE
    exact (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sX i hdim E hEc hE0
      ⟨c₀, hsupp E hE c₀⟩).2.mpr (hsupp E hE)
  have h1 := hdeg0 _ hP' (fun Γ => by
      change (0 : ℤ) ≤ ((((b : ℕ) : ℤ) • ((a : ℤ) • P))).coeff Γ
      simp only [DivisorWithCoeffs.coeff_smul, hPc, smul_eq_mul]
      positivity)
    (fun Γ hΓ => by
      simp only [DivisorWithCoeffs.coeff_smul, hPc, smul_eq_mul] at hΓ
      intro h0; rw [h0] at hΓ; simp at hΓ)
  have h2 := hdeg0 _ hN' (fun Γ => by
      change (0 : ℤ) ≤ ((((a : ℕ) : ℤ) • ((b : ℤ) • N))).coeff Γ
      simp only [DivisorWithCoeffs.coeff_smul, hNc, smul_eq_mul]
      positivity)
    (fun Γ hΓ => by
      simp only [DivisorWithCoeffs.coeff_smul, hNc, smul_eq_mul] at hΓ
      intro h0; rw [h0] at hΓ; simp at hΓ)
  have h3 := Divisor.degreeOn_add ℂ sX i hdim _ _ hnD hN'
  rw [Divisor.degreeOn_congr hsum (hnD.add hN') hP', h1, h2, add_zero,
    Divisor.degreeOn_nsmul' ℂ sX i hdim D hD] at h3
  have hab : ((a * b : ℕ) : ℤ) ≠ 0 := by positivity
  exact (mul_eq_zero.mp h3.symm).resolve_left hab

/-- **The adjoint is numerically trivial over the Mori fibre space.** If locally over `T` some
`g^*e · Ω_V` generates `𝒪_V(m(K_V + B_V))`, then `K_V + B_V` is numerically trivial over `g`:
on a contracted curve `C` over `t`, `m(K_V + B_V) ∼_ℚ div(g^*e · Ω_V) + mB_V`, whose support
misses `g⁻¹(U) ⊇ C`. -/
private theorem isNumericallyTrivialOver_of_frame {V T : Scheme.{0}} [IsIntegral V] [CompactSpace V]
    [IsLocallyNoetherian V] [IsNormal V] {sV : V ⟶ Spec (.of ℂ)} [QuasiCompact sV]
    (hQ : IsQFactorial sV) {KV : Divisor V} (hKV : KV.IsCanonicalDivisor sV 2) {BV : QDivisor V}
    [IsIntegral T] (g : V ⟶ T) [IsDominant g] {m : ℕ} (hm : 0 < m)
    {ΩV : RationalPluriForms sV 2 m}
    (hfr : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ e : T.functionField, e ≠ 0 ∧
      GeneratesOn BV m (g ⁻¹ᵁ U) (functionFieldMap g e • ΩV)) :
    MMP.Flips.IsNumericallyTrivialOver ℂ sV g
      (Mori.QDivisor.toRDivisor (Divisor.toQDivisor KV + BV)) := by
  classical
  have hVn : IsNormalVariety ℂ sV := hQ.1
  haveI : LocallyOfFiniteType sV := hVn.1.toLocallyOfFiniteType
  set D := Divisor.toQDivisor KV + BV with hDdef
  have hDq := isQCartier_of_isQFactorial sV hQ D
  refine ⟨isCartierCombination_of_isQFactorial hQ _, isCartierCombination_of_isQFactorial hQ _,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  have e1 := intersectionNumber_eq_of_isRIntersectionNumber hDq C h₁
  have h₂' : MMP.Flips.IsRIntersectionNumber ℂ sV (QDivisor.toRDivisor (0 : QDivisor V)) r₂ L₂ C
      x₂ := by
    rwa [map_zero]
  have e2 := intersectionNumber_eq_of_isRIntersectionNumber QDivisor.isQCartier_zero C h₂'
  rw [← e1, ← e2]
  have hz : (0 : QDivisor V).intersectionNumber ℂ sV C.ι C.dim_le QDivisor.isQCartier_zero = 0 := by
    rw [QDivisor.intersectionNumber_eq_of_smul ℂ sV C.ι C.dim_le 0 _ one_pos 0
      Divisor.isCartier_zero (by simp), Divisor.degreeOn_zero']
    simp
  rw [hz]
  -- the frame over `g(C)`
  obtain ⟨U, hU, e, he, hgen⟩ := hfr (g C.point)
  set τ := functionFieldMap g e • ΩV with hτdef
  have hτ0 : τ ≠ 0 := hgen.1
  obtain ⟨ψ, hψ⟩ := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hVn hKV hτ0
  set G : QDivisor V := Divisor.toQDivisor (divisorOfForm τ) + (m : ℤ) • BV with hGdef
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hlin : D.QLinearlyEquivalent ((m : ℚ)⁻¹ • G) := by
    refine ⟨m, hm, ψ⁻¹, ?_⟩
    ext Γ
    have h1 := congrArg (fun F : Divisor V => F.coeff Γ) hψ
    simp only [DivisorWithCoeffs.coeff_sub, coeff_divisorOfForm, DivisorWithCoeffs.coeff_smul,
      coeff_principalDivisor, smul_eq_mul] at h1
    simp only [hDdef, hGdef, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm,
      coeff_principalDivisor, PrimeDivisor.ord_inv, zsmul_eq_mul, smul_eq_mul]
    have h1' : ((Γ.ordForm τ : ℤ) : ℚ) - (m : ℚ) * (KV.coeff Γ : ℚ) = (Γ.ord ψ : ℚ) := by
      exact_mod_cast h1
    have hmi : (m : ℚ) * (m : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hm'
    push_cast
    linear_combination (-1 : ℚ) * h1' - (((Γ.ordForm τ : ℤ) : ℚ) + (m : ℚ) * BV.coeff Γ) * hmi
  have hGq : ((m : ℚ)⁻¹ • G).IsQCartier := isQCartier_of_isQFactorial sV hQ _
  rw [FL.intersectionNumber_eq_of_qLinearlyEquivalent C.ι C.dim_le hDq hGq hlin]
  obtain ⟨D0, hD0, hD0c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hGq
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sV C.ι C.dim_le _ hGq
    (QDivisor.cartierIndex_pos hGq) D0 hD0c hD0]
  suffices h : D0.degreeOn ℂ sV C.ι C.dim_le hD0c = 0 by rw [h]; simp
  refine degreeOn_eq_zero_of_forall_notMem_supp hQ C.ι C.dim_le hD0c fun c hc => ?_
  obtain ⟨Γ, hΓ, hcΓ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hc
  apply hΓ
  have hcU : C.ι c ∈ (g ⁻¹ᵁ U : Set V) := by
    have hmem : C.ι c ∈ closure ({C.point} : Set V) := by
      rw [← C.range_ι]; exact ⟨c, rfl⟩
    show g (C.ι c) ∈ U
    rw [hC _ hmem]; exact hU
  have h0 := hgen.2 Γ ⟨C.ι c, hcΓ, hcU⟩
  have h1 := congrArg (fun F : QDivisor V => F.coeff Γ) hD0
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, hGdef,
    DivisorWithCoeffs.coeff_add, coeff_divisorOfForm, zsmul_eq_mul, smul_eq_mul] at h1
  have : ((D0.coeff Γ : ℤ) : ℚ) = 0 := by
    rw [h1]
    push_cast at h0 ⊢
    rw [h0]; ring
  exact_mod_cast this

/-- **The residue of a local generator along a floor curve.** Let `j : C ⟶ X` be an adjunction
step of a projective dlt surface pair `(X, B)` onto `P`, with different `B_C`, and `τ` a generator
of `𝒪_X(m(K + B))` on `U`. Its Poincaré residue `ρ` is nonzero, and has order `-m · coeff_Q B_C`
at every prime divisor `Q` of `C` with `j(Q) ∈ U`: it agrees up to a unit with the residue of the
local generator of `exists_generatesOn_isPoincareResidue_floor`. -/
private theorem ordForm_isPoincareResidue_of_generatesOn {X C : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hX : Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 2) {B : QDivisor X}
    (hB : Fourfold.IsPair sX B) (hdlt : MMP.Intersection.IsDltPair sX B)
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] {j : C ⟶ X} {BC : QDivisor C}
    (hj : IsAdjunctionStep sX B j BC) {m : ℕ} (hm : 0 < m) {U : X.Opens}
    {τ : RationalPluriForms sX 2 m} (hτ : GeneratesOn B m U τ)
    {ρ : RationalPluriForms (j ≫ sX) 1 m} (hρ : IsPoincareResidue sX j 1 m τ ρ)
    (hU : (Set.range j.base ∩ U).Nonempty) :
    ρ ≠ 0 ∧ ∀ Q : Mori.PrimeDivisor C, j Q.genericPoint ∈ U →
      (Q.ordForm ρ : ℚ) = -(m * BC.coeff Q) := by
  classical
  have hXn : IsNormalVariety ℂ sX := hB.isPair.1
  haveI : LocallyOfFiniteType sX := hXn.1.toLocallyOfFiniteType
  obtain ⟨hT, P, hP1, hrange, hci, -⟩ := id hj
  haveI := hci
  haveI : IsNormal C := hT.2
  haveI : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace j
  have hBP : B.coeff P = 1 := le_antisymm (hdlt.2.1 P) hP1
  have hdimC : topologicalKrullDim C = (1 : ℕ) :=
    topologicalKrullDim_eq_one_of_isAdjunctionStep hdim hj
  have hdimC1 : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞) := hdimC
  have hdim2 : topologicalKrullDim X = ((2 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  obtain ⟨Q₀⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdimC one_ne_zero
  -- the residue is nonzero: the pole along `P` has full order
  have hPU : (P.support ∩ (U : Set X)).Nonempty := by
    obtain ⟨y, ⟨c, rfl⟩, hy⟩ := hU
    exact ⟨j c, hrange ▸ ⟨c, rfl⟩, hy⟩
  have hordP : P.ordForm τ = -(m : ℤ) := by
    have h := hτ.2 P hPU
    rw [hBP] at h
    have : ((P.ordForm τ : ℤ) : ℚ) = -(m : ℚ) := by linarith
    exact_mod_cast this
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    have := neg_lt_ordForm_of_isPoincareResidue_zero sX hXn (n := 1)
      (by rw [hdim]; rfl) j hT (by rw [hdimC]) P hrange Q₀ hm hτ.1 hordP.ge hρ
    omega
  refine ⟨hρ0, fun Q hQ => ?_⟩
  obtain ⟨m₀, hm₀, hgen⟩ := exists_generatesOn_isPoincareResidue_floor hX hdim hB
  have hdimS : topologicalKrullDim X = (1 : ℕ) + 1 := by rw [hdim]; rfl
  obtain ⟨τN, ρN, hτN, hρN, hρN0, hordN⟩ := exists_pow_generatesOn_isPoincareResidue hj hdimS
    hdimC hτ hρ0 hρ Q (m₀ - 1)
  have hMdiv : m₀ ∣ (m * (m₀ - 1 + 1) - 1) + 1 := by
    rw [Nat.sub_add_cancel (Nat.mul_pos hm (Nat.succ_pos _))]
    simp only [Nat.succ_eq_add_one, Nat.sub_add_cancel hm₀]
    exact Dvd.intro_left _ rfl
  obtain ⟨U'', hxU'', τ'', hτ''gen, ρ'', hρ'', hρ''gen⟩ := hgen _ hMdiv hj Q₀ Q.genericPoint
  have hMeq : (m * (m₀ - 1 + 1) - 1) + 1 = m * (m₀ - 1 + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos hm (Nat.succ_pos _))
  revert τ'' ρ''
  rw [hMeq]
  intro τ'' hτ''gen ρ'' hρ'' hρ''gen
  -- `τN = f τ''` with `f` a unit at `y = j(η_Q)`
  set y := j Q.genericPoint with hydef
  letI := Mori.functionFieldAlgebra sX
  obtain ⟨bas⟩ := exists_basis_topForms (sX := sX) hdim2
  let e : Module.Basis Unit X.functionField
      (RationalPluriForms sX 2 ((m * (m₀ - 1 + 1) : ℕ) : ℤ)) :=
    MMP.Mori.ZTensorPower.basis bas ((m * (m₀ - 1 + 1) : ℕ) : ℤ)
  have hτ''0 : τ'' ≠ 0 := hτ''gen.1
  have hr : e.repr τ'' () ≠ 0 := by
    intro h; apply hτ''0; rw [← MMP.Mori.basis_unit_repr_smul e τ'', h, zero_smul]
  set f : X.functionField := e.repr τN () / e.repr τ'' () with hfdef
  have hf : τN = f • τ'' := by
    conv_lhs => rw [← MMP.Mori.basis_unit_repr_smul e τN]
    conv_rhs => rw [← MMP.Mori.basis_unit_repr_smul e τ'']
    rw [smul_smul, hfdef, div_mul_cancel₀ _ hr]
  have hf0 : f ≠ 0 := by intro h; apply hτN.1; rw [hf, h, zero_smul]
  have hordf : ∀ Γ : Mori.PrimeDivisor X, y ∈ Γ.support → X.ord f Γ.genericPoint = 0 := by
    intro Γ hΓ
    have h1 := Γ.ordForm_smul_of_topologicalKrullDim_eq hdim2 hf0 hτ''0
    rw [← hf] at h1
    have h2 := hτN.2 Γ ⟨y, hΓ, hQ⟩
    have h3 := hτ''gen.2 Γ ⟨y, hΓ, hxU''⟩
    rw [h1] at h2
    push_cast at h2 h3
    have : ((X.ord f Γ.genericPoint : ℤ) : ℚ) = 0 := by linarith
    exact_mod_cast this
  obtain ⟨a, ha, haf⟩ := MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero y hf0
    hordf
  have hsp0 : genericPoint C ⤳ Q.genericPoint := (genericPoint_spec C).specializes trivial
  have hsp : j (genericPoint C) ⤳ y := hsp0.map j.base.hom.continuous
  set b := (X.presheaf.stalkSpecializes hsp).hom a with hbdef
  have hbf : algebraMap _ X.functionField b = f := by
    rw [hbdef, MMP.Mori.algebraMap_stalkSpecializes hsp a, haf]
  have hres := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hρ'' b
  rw [hbf, ← hf] at hres
  have huniq := IsPoincareResidue.unique hj hρN hres
  have hbbar : (j.stalkMap (genericPoint C)).hom b =
      algebraMap _ C.functionField ((j.stalkMap Q.genericPoint).hom a) :=
    stalkMap_genericPoint_stalkSpecializes j Q.genericPoint hsp a
  have hbbaru : IsUnit ((j.stalkMap Q.genericPoint).hom a) := ha.map _
  have hbbar0 : (j.stalkMap (genericPoint C)).hom b ≠ 0 := by
    rw [hbbar]; exact (hbbaru.map (algebraMap _ C.functionField)).ne_zero
  have h4 := Q.ordForm_smul_of_topologicalKrullDim_eq hdimC1 hbbar0 hρ''gen.1
  rw [← huniq, hordN, hbbar, ord_algebraMap_eq_zero_of_isUnit' Q rfl hbbaru, zero_add] at h4
  have h5 := hρ''gen.2 Q ⟨Q.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support _, hxU''⟩
  rw [← h4] at h5
  push_cast at h5
  have hN0 : ((m₀ - 1 : ℕ) : ℚ) + 1 ≠ 0 := by positivity
  have : (((m₀ - 1 : ℕ) : ℚ) + 1) * ((Q.ordForm ρ : ℚ) + m * BC.coeff Q) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hN0
  · linarith

/-- **Powers of a form and of its pull-back.** For a nonzero form `τ` of degree `a` on `V` and a
dominant `q : X ⟶ V` of surfaces, every degree `D = a(k + 1)` carries a form `τ_k` (the power
`τ^{k+1}`) with `ord τ_k = (k + 1) ord τ` on `V` and `ord q^*τ_k = (k + 1) ord q^*τ` on `X`. -/
private theorem exists_pow_pullback {X V : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral V] [IsLocallyNoetherian V] {sV : V ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sV]
    (q : X ⟶ V) [IsDominant q] [LocallyOfFiniteType (q ≫ sV)]
    (hVd : topologicalKrullDim V = 2) (hXd : topologicalKrullDim X = 2) {a : ℕ}
    {τ : RationalPluriForms sV 2 a} (hτ : τ ≠ 0) (hqτ : pullbackRationalPluriForms sV q τ ≠ 0) :
    ∀ k D : ℕ, D = a * (k + 1) → ∃ τk : RationalPluriForms sV 2 D, τk ≠ 0 ∧
      pullbackRationalPluriForms sV q τk ≠ 0 ∧
      (∀ Γ : Mori.PrimeDivisor V, Γ.ordForm τk = ((k + 1 : ℕ) : ℤ) * Γ.ordForm τ) ∧
      ∀ E : Mori.PrimeDivisor X, E.ordForm (pullbackRationalPluriForms sV q τk) =
        ((k + 1 : ℕ) : ℤ) * E.ordForm (pullbackRationalPluriForms sV q τ) := by
  have hVd2 : topologicalKrullDim V = ((2 : ℕ) : WithBot ℕ∞) := by rw [hVd]; rfl
  have hXd2 : topologicalKrullDim X = ((2 : ℕ) : WithBot ℕ∞) := by rw [hXd]; rfl
  intro k
  induction k with
  | zero =>
    rintro D rfl
    have key : ∀ D' : ℕ, D' = a → ∃ τk : RationalPluriForms sV 2 D', τk ≠ 0 ∧
        pullbackRationalPluriForms sV q τk ≠ 0 ∧
        (∀ Γ : Mori.PrimeDivisor V, Γ.ordForm τk = ((0 + 1 : ℕ) : ℤ) * Γ.ordForm τ) ∧
        ∀ E : Mori.PrimeDivisor X, E.ordForm (pullbackRationalPluriForms sV q τk) =
          ((0 + 1 : ℕ) : ℤ) * E.ordForm (pullbackRationalPluriForms sV q τ) := by
      rintro D' rfl
      exact ⟨τ, hτ, hqτ, fun Γ => by simp, fun E => by simp⟩
    exact key _ (by simp)
  | succ k ih =>
    rintro D rfl
    obtain ⟨τk, hτk, hqτk, hΓk, hEk⟩ := ih _ rfl
    refine ⟨RationalPluriForms.mul sV 2 (a * (k + 1)) a τk τ,
      RationalPluriForms.mul_ne_zero hVd2 hτk hτ, ?_, fun Γ => ?_, fun E => ?_⟩
    · rw [pullbackRationalPluriForms_mul]
      exact RationalPluriForms.mul_ne_zero hXd2 hqτk hqτ
    · rw [ordForm_mul Γ hτk hτ, hΓk]
      push_cast; ring
    · rw [pullbackRationalPluriForms_mul, ordForm_mul E hqτk hqτ, hEk]
      push_cast; ring

/-- **Generators pull back to generators.** If `ω` generates `𝒪_V(m(K_V + B_V))` on `W_V` and
`q^*ω` generates `𝒪_X(m(K + B))` on `W_X`, then for every generator `τ` on `U` the pull-back
`q^*τ` generates on `q⁻¹(U ∩ W_V) ∩ W_X`: `τ = f ω` with `f` a unit along `U ∩ W_V`. -/
private theorem generatesOn_pullback {X V : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {sV : V ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sV] (hVdim : topologicalKrullDim V = 2)
    (hXdim : topologicalKrullDim X = 2) (q : X ⟶ V) [IsDominant q]
    [LocallyOfFiniteType (q ≫ sV)] {B : QDivisor X} {BV : QDivisor V} {m : ℕ}
    {ω : RationalPluriForms sV 2 m} {WV : V.Opens} {WX : X.Opens}
    (hV : GeneratesOn BV m WV ω)
    (hX : GeneratesOn (sX := q ≫ sV) B m WX (pullbackRationalPluriForms sV q ω))
    {U : V.Opens} {τ : RationalPluriForms sV 2 m} (hτ : GeneratesOn BV m U τ) :
    GeneratesOn (sX := q ≫ sV) B m (q ⁻¹ᵁ (U ⊓ WV) ⊓ WX) (pullbackRationalPluriForms sV q τ) := by
  classical
  have hdV2 : topologicalKrullDim V = ((2 : ℕ) : WithBot ℕ∞) := by rw [hVdim]; rfl
  have hdX2 : topologicalKrullDim X = ((2 : ℕ) : WithBot ℕ∞) := by rw [hXdim]; rfl
  letI := Mori.functionFieldAlgebra sV
  have hω0 : ω ≠ 0 := hV.1
  obtain ⟨b⟩ := exists_basis_topForms (sX := sV) hdV2
  let bm : Module.Basis Unit V.functionField (RationalPluriForms sV 2 (m : ℤ)) :=
    MMP.Mori.ZTensorPower.basis b (m : ℤ)
  have hr : bm.repr ω () ≠ 0 := by
    intro h0; apply hω0; rw [← MMP.Mori.basis_unit_repr_smul bm ω, h0, zero_smul]
  set f := bm.repr τ () / bm.repr ω () with hfdef
  have hτf : τ = f • ω := by
    conv_lhs => rw [← MMP.Mori.basis_unit_repr_smul bm τ]
    conv_rhs => rw [← MMP.Mori.basis_unit_repr_smul bm ω]
    rw [smul_smul, hfdef, div_mul_cancel₀ _ hr]
  have hf0 : f ≠ 0 := by intro h0; apply hτ.1; rw [hτf, h0, zero_smul]
  have hpbτ : pullbackRationalPluriForms sV q τ =
      functionFieldMap q f • pullbackRationalPluriForms sV q ω := by
    rw [hτf, pullbackRationalPluriForms_smul']
  have hqf0 : functionFieldMap q f ≠ 0 := (map_ne_zero _).mpr hf0
  refine ⟨?_, fun E hE => ?_⟩
  · rw [hpbτ]
    exact smul_ne_zero hqf0 hX.1
  obtain ⟨x, hxE, hxU, hxW⟩ := hE
  have hxU1 : q x ∈ U := hxU.1
  have hxU2 : q x ∈ WV := hxU.2
  have hordf : ∀ Γ : Mori.PrimeDivisor V, q x ∈ Γ.support → V.ord f Γ.genericPoint = 0 := by
    intro Γ hΓ
    have h1 := hτ.2 Γ ⟨q x, hΓ, hxU1⟩
    have h2 := hV.2 Γ ⟨q x, hΓ, hxU2⟩
    rw [hτf, Γ.ordForm_smul_of_topologicalKrullDim_eq hdV2 hf0 hω0] at h1
    push_cast at h1 h2
    have : ((V.ord f Γ.genericPoint : ℤ) : ℚ) = 0 := by linarith
    exact_mod_cast this
  obtain ⟨a, ha, haf⟩ := MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero (q x)
    hf0 hordf
  have hqa : functionFieldMap q f = algebraMap _ X.functionField ((q.stalkMap x).hom a) := by
    have h := congrArg (fun φ => φ.hom a)
      (stalkSpecializes_stalkMap_algebraMap q x (q x) (specializes_refl _))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      TopCat.Presheaf.stalkSpecializes_refl, CommRingCat.hom_id, RingHom.id_apply] at h
    rw [← haf]
    exact h.symm
  have hordqf : X.ord (functionFieldMap q f) E.genericPoint = 0 := by
    rw [hqa]
    exact ord_algebraMap_eq_zero_of_isUnit_of_mem E hxE (ha.map _)
  have h3 := hX.2 E ⟨x, hxE, hxW⟩
  rw [hpbτ, E.ordForm_smul_of_topologicalKrullDim_eq hdX2 hqf0 hX.1, hordqf, zero_add]
  exact h3

/-- **The adjunction boundary of a strict transform is the different.** Let `q : X ⟶ V` be a
birational morphism over `T` carrying local frames of the adjoints (`g^*e · Ω_V` on `V`, its
pull-back on `X`), and `j : C ⟶ X` an adjunction step onto a floor curve whose image is a prime
divisor of `V`, with different `B_C`. If `Θ` on `C` is such that near every point the residue
along `j ≫ q` of a local generator of `m(K_V + B_V)` generates `m(K_C + Θ)`, then `Θ = B_C`. -/
private theorem eq_of_isAdjunctionBoundary {X V T C : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [IsIntegral T] {sV : V ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sV]
    (q : X ⟶ V) [IsDominant q] (hqb : IsBirationalMorphism q)
    (hX : Mori.IsProjectiveVariety ℂ (q ≫ sV)) (hdim : topologicalKrullDim X = 2)
    (hVdim : topologicalKrullDim V = 2) {B : QDivisor X} (hB : Fourfold.IsPair (q ≫ sV) B)
    (hdlt : MMP.Intersection.IsDltPair (q ≫ sV) B) {BV : QDivisor V} (g : V ⟶ T)
    [IsDominant g] [IsDominant (q ≫ g)] {d : ℕ} (hd : 0 < d) {ΩV : RationalPluriForms sV 2 d}
    (hfr : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ e : T.functionField, e ≠ 0 ∧
      GeneratesOn BV d (g ⁻¹ᵁ U) (functionFieldMap g e • ΩV) ∧
      GeneratesOn (sX := q ≫ sV) B d ((q ≫ g) ⁻¹ᵁ U)
        (functionFieldMap (q ≫ g) e • pullbackRationalPluriForms sV q ΩV))
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] {j : C ⟶ X} {BC : QDivisor C}
    (hj : IsAdjunctionStep (q ≫ sV) B j BC) (P' : Mori.PrimeDivisor X)
    (hP' : Set.range j.base = (P'.support : Set X)) (Pk : Mori.PrimeDivisor V)
    (hη : q P'.genericPoint = Pk.genericPoint) [IsIso (q.stalkMap P'.genericPoint)]
    {Θ : QDivisor C}
    (hΘ : ∃ m : ℕ, 0 < m ∧ ∀ x : C, ∃ U : V.Opens, (j ≫ q).base x ∈ U ∧
      ∃ τ : RationalPluriForms sV 2 m, GeneratesOn BV m U τ ∧
        ∃ ρ : RationalPluriForms ((j ≫ q) ≫ sV) 1 m, IsPoincareResidue sV (j ≫ q) 1 m τ ρ ∧
          GeneratesOn Θ m ((j ≫ q) ⁻¹ᵁ U) ρ) :
    Θ = BC := by
  classical
  have hXn : IsNormalVariety ℂ (q ≫ sV) := hB.isPair.1
  haveI : LocallyOfFiniteType (q ≫ sV) := hXn.1.toLocallyOfFiniteType
  have hbij := hqb.functionFieldMap_bijective
  have hd2 : (letI := Mori.functionFieldAlgebra sV
      (Algebra.trdeg ℂ V.functionField).toNat) = 1 + 1 :=
    Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (by rw [hVdim]; rfl)
  obtain ⟨-, -, -, -, hci, -⟩ := id hj
  haveI := hci
  have hjη : j (genericPoint C) = P'.genericPoint :=
    MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P' hP'
  obtain ⟨m', hm', hloc⟩ := hΘ
  ext Q
  change Θ.coeff Q = BC.coeff Q
  obtain ⟨U, hxU, τ, hτgen, ρ, hρres, hρgen⟩ := hloc Q.genericPoint
  have hΘQ := hρgen.2 Q ⟨Q.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support _, hxU⟩
  set y := (j ≫ q) Q.genericPoint with hydef
  obtain ⟨U', hU', e, he, hfV, hfX⟩ := hfr (g y)
  set ω := functionFieldMap g e • ΩV with hωdef
  have hqω : pullbackRationalPluriForms sV q ω =
      functionFieldMap (q ≫ g) e • pullbackRationalPluriForms sV q ΩV := by
    rw [hωdef, pullbackRationalPluriForms_smul',
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  rw [← hqω] at hfX
  -- powers of `τ` and `ω` in the common degree `m' d`
  have hqτ0 : pullbackRationalPluriForms sV q τ ≠ 0 := by
    intro h0
    apply hτgen.1
    apply pullbackRationalPluriForms_injective q hbij hd2
    rw [h0]
    have h := pullbackRationalPluriForms_smul' q (0 : V.functionField)
      (0 : RationalPluriForms sV 2 m')
    rw [zero_smul, map_zero, zero_smul] at h
    exact h.symm
  obtain ⟨τd, hτd0, hqτd0, hτdV, hτdX⟩ := exists_pow_pullback q hVdim hdim hτgen.1 hqτ0
    (d - 1) (m' * d) (by rw [Nat.sub_add_cancel hd])
  obtain ⟨ωm, hωm0, hqωm0, hωmV, hωmX⟩ := exists_pow_pullback q hVdim hdim hfV.1 hfX.1
    (m' - 1) (m' * d) (by rw [Nat.sub_add_cancel hm', mul_comm])
  have hgenpow : ∀ {Wt : V.Opens} {a k D : ℕ} (_ : D = a * (k + 1))
      {σ : RationalPluriForms sV 2 a} {σk : RationalPluriForms sV 2 D},
      GeneratesOn BV a Wt σ → σk ≠ 0 →
      (∀ Γ : Mori.PrimeDivisor V, Γ.ordForm σk = ((k + 1 : ℕ) : ℤ) * Γ.ordForm σ) →
      GeneratesOn BV D Wt σk := by
    intro Wt a k D hD σ σk hσ hσk hord
    refine ⟨hσk, fun Γ hΓ => ?_⟩
    have h := hσ.2 Γ hΓ
    rw [hord, hD]
    push_cast at h ⊢
    linear_combination ((k : ℚ) + 1) * h
  have hgenpowX : ∀ {Wt : X.Opens} {a k D : ℕ} (_ : D = a * (k + 1))
      {σ : RationalPluriForms (q ≫ sV) 2 a} {σk : RationalPluriForms (q ≫ sV) 2 D},
      GeneratesOn (sX := q ≫ sV) B a Wt σ → σk ≠ 0 →
      (∀ Γ : Mori.PrimeDivisor X, Γ.ordForm σk = ((k + 1 : ℕ) : ℤ) * Γ.ordForm σ) →
      GeneratesOn (sX := q ≫ sV) B D Wt σk := by
    intro Wt a k D hD σ σk hσ hσk hord
    refine ⟨hσk, fun Γ hΓ => ?_⟩
    have h := hσ.2 Γ hΓ
    rw [hord, hD]
    push_cast at h ⊢
    linear_combination ((k : ℚ) + 1) * h
  have hτdg : GeneratesOn BV (m' * d) U τd :=
    hgenpow (k := d - 1) (by rw [Nat.sub_add_cancel hd]) hτgen hτd0 hτdV
  have hωmg : GeneratesOn BV (m' * d) (g ⁻¹ᵁ U') ωm :=
    hgenpow (k := m' - 1) (by rw [Nat.sub_add_cancel hm', mul_comm]) hfV hωm0 hωmV
  have hqωmg : GeneratesOn (sX := q ≫ sV) B (m' * d) ((q ≫ g) ⁻¹ᵁ U')
      (pullbackRationalPluriForms sV q ωm) :=
    hgenpowX (k := m' - 1) (by rw [Nat.sub_add_cancel hm', mul_comm]) hfX hqωm0 hωmX
  have hqτd := generatesOn_pullback hVdim hdim q hωmg hqωmg hτdg
  -- the pull-back `q^*τ` generates near `j(η_Q)`
  set W := q ⁻¹ᵁ (U ⊓ g ⁻¹ᵁ U') ⊓ (q ≫ g) ⁻¹ᵁ U' with hWdef
  have hdX2 : topologicalKrullDim X = ((2 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  have hqτ : GeneratesOn (sX := q ≫ sV) B m' W (pullbackRationalPluriForms sV q τ) := by
    refine ⟨hqτ0, fun E hE => ?_⟩
    have h := hqτd.2 E hE
    rw [hτdX] at h
    have hd' : ((d - 1 + 1 : ℕ) : ℚ) = d := by rw [Nat.sub_add_cancel hd]
    push_cast at h hd' ⊢
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have : (d : ℚ) * (((E.ordForm (pullbackRationalPluriForms sV q τ) : ℤ) : ℚ) +
      m' * B.coeff E) = 0 := by
      linear_combination h - ((E.ordForm (pullbackRationalPluriForms sV q τ) : ℤ) : ℚ) * hd'
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hd0
    · exact h'
  have hjW : j Q.genericPoint ∈ W := by
    refine ⟨⟨hxU, ?_⟩, ?_⟩
    · show g y ∈ U'; exact hU'
    · show g y ∈ U'; exact hU'
  obtain ⟨ρ', hρ', hρ'ρ⟩ := isPoincareResidue_pullbackRationalPluriForms q hbij j P' hjη Pk hη hd2
    hm' hτgen.1 hρres
  have hC1 := (ordForm_isPoincareResidue_of_generatesOn hX hdim hB hdlt hj hm' hqτ hρ'
    ⟨j Q.genericPoint, ⟨_, rfl⟩, hjW⟩).2 Q hjW
  have hord := (ordForm_eq_of_heq (Category.assoc j q sV).symm hρ'ρ Q).1
  rw [hord] at hC1
  have hm'0 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  have : (m' : ℚ) * (Θ.coeff Q - BC.coeff Q) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hm'0
  · linarith

end HorizA

section HorizB

open MMP MMP.Fourfold MMP.Flips
open MMP.Mori hiding IsPair
open FloorAdjunction

/-- **Horizontal floor curves are strict transforms of horizontal floor curves.** If
`q : X ⟶ V` maps the floor of `B` onto that of `B_V` and `P` is a floor curve of `X` dominating
the curve `T` through `q ≫ g`, then `q(η_P)` is the generic point of a horizontal floor curve `E`
of `V`: it lies on a floor curve `E`, which then dominates `T`, and a closed point of `E` would
map to a closed point of `T`. -/
private theorem exists_horizontal_floor {X V T : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V]
    [IsIntegral T] {sV : V ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sV]
    (hVdim : topologicalKrullDim V = 2) (hT1 : topologicalKrullDim T = 1) (q : X ⟶ V)
    (g : V ⟶ T) (hgc : IsClosedMap g.base) {B : QDivisor X} {BV : QDivisor V}
    (himg : q.base '' floorUnion B = floorUnion BV) (P : Mori.PrimeDivisor X)
    (hP : ⌊B.coeff P⌋ ≠ 0) (hPh : (q ≫ g) P.genericPoint = genericPoint T) :
    ∃ E : Mori.PrimeDivisor V, ⌊BV.coeff E⌋ ≠ 0 ∧ g E.genericPoint = genericPoint T ∧
      q P.genericPoint = E.genericPoint := by
  classical
  have hyF : q P.genericPoint ∈ floorUnion BV := by
    rw [← himg]
    exact ⟨P.genericPoint, Set.mem_iUnion.mpr ⟨⟨P, hP⟩,
      MMP.Flips.primeDivisor_genericPoint_mem_support _⟩, rfl⟩
  obtain ⟨⟨E, hE⟩, hyE⟩ := Set.mem_iUnion.mp hyF
  have hsp : E.genericPoint ⤳ q P.genericPoint := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyE
    exact specializes_iff_mem_closure.mpr hyE
  have hgy : g (q P.genericPoint) = genericPoint T := hPh
  have hgE : g E.genericPoint = genericPoint T := by
    have h1 : g E.genericPoint ⤳ genericPoint T := by
      rw [← hgy]; exact hsp.map g.base.hom.continuous
    have h2 : IsGenericPoint (g E.genericPoint) (⊤ : Set T) := by
      refine le_antisymm le_top ?_
      calc (⊤ : Set T) = closure {genericPoint T} := (genericPoint_spec T).def.symm
        _ ≤ closure {g E.genericPoint} := closure_minimal (Set.singleton_subset_iff.mpr
          (specializes_iff_mem_closure.mp h1)) isClosed_closure
    exact (h2.eq (genericPoint_spec T))
  refine ⟨E, hE, hgE, ?_⟩
  by_contra hne
  haveI := E.integral
  set ι := E.idealSheaf.subschemeι with hιdef
  have hrange : Set.range ι.base = (E.support : Set V) := by
    rw [hιdef, Scheme.IdealSheafData.range_subschemeι]
  have hdimE : topologicalKrullDim E.idealSheaf.subscheme = (1 : ℕ) :=
    topologicalKrullDim_eq_of_range_eq_support sV ι E hrange
      (by rw [hVdim]; norm_num)
  obtain ⟨y', hy'⟩ : q P.genericPoint ∈ Set.range ι.base := hrange ▸ hyE
  have hy'η : y' ≠ genericPoint E.idealSheaf.subscheme := by
    rintro rfl
    exact hne (hy'.symm.trans (map_genericPoint_eq_of_range_eq ι E hrange))
  have hcl : IsClosed ({y'} : Set E.idealSheaf.subscheme) :=
    isClosed_singleton_of_ne_genericPoint hdimE hy'η
  have hcl2 : IsClosed ({q P.genericPoint} : Set V) := by
    rw [← hy', ← Set.image_singleton]
    exact ι.isClosedEmbedding.isClosedMap _ hcl
  have hcl3 : IsClosed ({genericPoint T} : Set T) := by
    rw [← hgy, ← Set.image_singleton]
    exact hgc _ hcl2
  exact MMP.Fourfold.not_isClosed_genericPoint hT1 hcl3

/-- The stalk map of a birational morphism at the generic point of a prime divisor lying over the
generic point of a prime divisor is an isomorphism (both are discrete valuation rings of the same
function field). -/
private theorem isIso_stalkMap_of_map_eq_genericPoint {X V : Scheme.{0}} [IsIntegral X] [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] (q : X ⟶ V) [IsDominant q]
    (hbij : Function.Bijective (functionFieldMap q)) (P : Mori.PrimeDivisor X)
    (E : Mori.PrimeDivisor V) (h : q P.genericPoint = E.genericPoint) :
    IsIso (q.stalkMap P.genericPoint) := by
  have : ValuationRing (V.presheaf.stalk (q P.genericPoint)) := by
    rw [h]
    have := E.isDiscreteValuationRing_localRing
    exact inferInstanceAs (ValuationRing E.localRing)
  exact MMP.Positivity.isIso_stalkMap_of_valuationRing q hbij _

/-- **Uniqueness of strict transforms.** Two prime divisors of `X` over the generic point of the
same prime divisor of `V`, for a birational `q : X ⟶ V`, coincide: they have the same valuation
on `k(X) = k(V)`. -/
private theorem eq_of_map_genericPoint_eq {X V : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] {sX : X ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) (q : X ⟶ V) [IsDominant q]
    (hbij : Function.Bijective (functionFieldMap q)) {P P' : Mori.PrimeDivisor X}
    (E : Mori.PrimeDivisor V) (h : q P.genericPoint = E.genericPoint)
    (h' : q P'.genericPoint = E.genericPoint) : P = P' := by
  haveI := isIso_stalkMap_of_map_eq_genericPoint q hbij P E h
  haveI := isIso_stalkMap_of_map_eq_genericPoint q hbij P' E h'
  have hord : ∀ f : X.functionField, X.ord f P.genericPoint = X.ord f P'.genericPoint := by
    intro f
    obtain ⟨f₀, rfl⟩ := hbij.2 f
    rw [MMP.Positivity.ord_functionFieldMap_of_isIso q P E h f₀,
      MMP.Positivity.ord_functionFieldMap_of_isIso q P' E h' f₀]
  have hv : (DivisorOver.ofPrimeDivisor ℂ hX P).valuation =
      (DivisorOver.ofPrimeDivisor ℂ hX P').valuation := by
    ext f
    change P.divisorialValuation (functionFieldMap (𝟙 X) f) =
      P'.divisorialValuation (functionFieldMap (𝟙 X) f)
    rw [MMP.Mori.functionFieldMap_id_apply]
    by_cases hf : f = 0
    · rw [hf, map_zero, map_zero]
    rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hf,
      MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hf, hord]
  have hη := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
  have hη' : P.genericPoint = P'.genericPoint := hη
  exact (MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support
    (hη' ▸ MMP.Flips.primeDivisor_genericPoint_mem_support P)).symm

/-- **Residues of a function pulled back from the base.** Along a curve `j : C ⟶ X` dominating
`T` through `h'`, multiplying a form by `h'^*ψ` multiplies its residue by `(j ≫ h')^*ψ`. -/
private theorem isPoincareResidue_functionFieldMap_smul {X T C : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsIntegral T] [IsIntegral C] {sX : X ⟶ Spec (.of ℂ)}
    (h' : X ⟶ T) [IsDominant h'] {j : C ⟶ X} [IsDominant (j ≫ h')] {n M : ℕ}
    {Ω : RationalPluriForms sX (n + 1) M} {ρ : RationalPluriForms (j ≫ sX) n M}
    (hρ : IsPoincareResidue sX j n M Ω ρ) (ψ : T.functionField) :
    IsPoincareResidue sX j n M (functionFieldMap h' ψ • Ω) (functionFieldMap (j ≫ h') ψ • ρ) := by
  have hη : h' (j (genericPoint C)) = genericPoint T := by
    have := map_genericPoint_of_isDominant (j ≫ h')
    simpa using this
  have hp : h' (j (genericPoint C)) ⤳ (𝟙 T) (genericPoint T) := by
    rw [hη]; rfl
  set germ := (h'.stalkMap (j (genericPoint C))).hom
    ((T.presheaf.stalkSpecializes hp).hom ψ) with hgerm
  have h1 : algebraMap _ X.functionField germ = functionFieldMap h' ψ := by
    have h := congrArg (fun φ => φ.hom ψ)
      (stalkSpecializes_stalkMap_algebraMap h' (j (genericPoint C))
        (genericPoint T) hp)
    rw [hgerm]
    refine h.trans ?_
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    congr 1
    exact algebraMap_stalk_genericPoint' T ψ
  have h2 : (j.stalkMap (genericPoint C)).hom germ = functionFieldMap (j ≫ h') ψ := by
    have h := stalkMap_apply_eq_functionFieldMap_apply h' (𝟙 T) j (j ≫ h')
      (Category.comp_id _) hp ψ
    rw [hgerm, h]
    congr 1
    rw [Scheme.Hom.stalkMap_id]
    rfl
  have := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hρ germ
  rwa [h1, h2] at this

/-- **Functions on a double cover fixed by the deck group come from the base.** Let `ν : N ⟶ V`
induce an isomorphism of residue fields at the generic point of `N` onto a point of `V` of degree
two over its image in `T`. A function on `N` fixed by every `k(T)`-automorphism of `k(N)` (as a
`ℂ`-isomorphism of function fields over `T`) is pulled back from `T`: the quadratic extension
`k(N)/k(T)` is Galois in characteristic zero. -/
private theorem exists_functionFieldMap_eq_of_forall_fixed {N V T : Scheme.{0}} [IsIntegral N]
    [IsIntegral T] (ν : N ⟶ V) (g : V ⟶ T) [IsDominant (ν ≫ g)]
    (hν : IsIso (ν.residueFieldMap (genericPoint N)))
    (hdeg : (letI := (g.residueFieldMap (ν.base (genericPoint N))).hom.toAlgebra
      Module.finrank (T.residueField (g.base (ν.base (genericPoint N))))
        (V.residueField (ν.base (genericPoint N)))) = 2)
    {sT : T ⟶ Spec (.of ℂ)} {sN : N ⟶ Spec (.of ℂ)} (e : (ν ≫ g) ≫ sT = sN)
    (u : N.functionField)
    (hu : ∀ σ : FunctionFieldEquiv sN sN,
      (∀ a, σ (functionFieldMap (ν ≫ g) a) = functionFieldMap (ν ≫ g) a) → σ u = u) :
    ∃ ψ : T.functionField, functionFieldMap (ν ≫ g) ψ = u := by
  classical
  subst e
  letI := Mori.functionFieldAlgebra sT
  letI := Mori.functionFieldAlgebra ((ν ≫ g) ≫ sT)
  letI A := Mori.functionFieldMapAlgebra (ν ≫ g)
  haveI hT := Mori.isScalarTower_functionFieldMap sT (ν ≫ g)
  -- the degree of `k(N)/k(T)` is two
  have h := residueFieldMap_comp_genericResidueEquivOfDominant (ν ≫ g)
  have hfin1 : Module.finrank T.functionField N.functionField =
      (letI := ((ν ≫ g).residueFieldMap (genericPoint N)).hom.toAlgebra;
        Module.finrank (T.residueField ((ν ≫ g).base (genericPoint N)))
          (N.residueField (genericPoint N))) := by
    letI := ((ν ≫ g).residueFieldMap (genericPoint N)).hom.toAlgebra
    refine Algebra.finrank_eq_of_equiv_equiv (genericResidueEquivOfDominant (ν ≫ g))
      (genericResidueEquiv N) ?_
    ext a
    have := congrArg (fun φ : T.functionField →+* N.residueField (genericPoint N) => φ a) h
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom] at this ⊢
    exact this
  have hfin2 : (letI := ((ν ≫ g).residueFieldMap (genericPoint N)).hom.toAlgebra;
        Module.finrank (T.residueField ((ν ≫ g).base (genericPoint N)))
          (N.residueField (genericPoint N))) =
      (letI := (g.residueFieldMap (ν.base (genericPoint N))).hom.toAlgebra;
        Module.finrank (T.residueField (g.base (ν.base (genericPoint N))))
          (V.residueField (ν.base (genericPoint N)))) := by
    letI := ((ν ≫ g).residueFieldMap (genericPoint N)).hom.toAlgebra
    letI := (g.residueFieldMap (ν.base (genericPoint N))).hom.toAlgebra
    refine (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _)
      ((asIso (ν.residueFieldMap (genericPoint N))).commRingCatIsoToRingEquiv.symm) ?_)
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.refl_apply]
    change (g.residueFieldMap (ν.base (genericPoint N))).hom a =
      (asIso (ν.residueFieldMap (genericPoint N))).commRingCatIsoToRingEquiv.symm
        (((ν ≫ g).residueFieldMap (genericPoint N)).hom a)
    rw [RingEquiv.eq_symm_apply, Scheme.residueFieldMap_comp]
    rfl
  have hfin : Module.finrank T.functionField N.functionField = 2 := by
    rw [hfin1, hfin2, hdeg]
  haveI : Algebra.IsQuadraticExtension T.functionField N.functionField := ⟨hfin⟩
  haveI : FiniteDimensional T.functionField N.functionField :=
    Module.finite_of_finrank_eq_succ hfin
  haveI : CharZero T.functionField :=
    charZero_of_injective_algebraMap (algebraMap ℂ T.functionField).injective
  have hmem : u ∈ Set.range (algebraMap T.functionField N.functionField) := by
    refine (IsGalois.mem_range_algebraMap_iff_fixed u).mpr fun f => ?_
    exact hu (f.restrictScalars ℂ) fun a => f.commutes a
  obtain ⟨ψ, hψ⟩ := hmem
  exact ⟨ψ, hψ⟩

/-- Pluriform pull-back is semilinear along the homomorphism of function fields. -/
private theorem pluriformPullback_smul_left {X X' : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sX' : X' ⟶ Spec (.of ℂ)} [IsIntegral X] [IsIntegral X'] (φ : FunctionFieldHom sX sX')
    {d : ℕ} {m : ℤ} (c : X'.functionField) (τ : RationalPluriForms sX' d m) :
    pluriformPullback sX sX' φ d m (c • τ) = φ c • pluriformPullback sX sX' φ d m τ := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  have : IsScalarTower ℂ X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  exact pullbackForms_smul (K := X'.functionField) (K' := X.functionField) c τ

/-- The pull-back of a nonzero function from the base has order zero along a prime divisor
dominating the base. -/
private theorem ord_functionFieldMap_eq_zero_of_map_genericPoint {X T : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsIntegral T] (h' : X ⟶ T) [IsDominant h']
    (P : Mori.PrimeDivisor X) (hP : h' P.genericPoint = genericPoint T) {e : T.functionField}
    (he : e ≠ 0) : X.ord (functionFieldMap h' e) P.genericPoint = 0 := by
  have hp : h' P.genericPoint ⤳ genericPoint T := by rw [hP]
  set germ := (h'.stalkMap P.genericPoint).hom ((T.presheaf.stalkSpecializes hp).hom e)
    with hgerm
  have h1 : algebraMap _ X.functionField germ = functionFieldMap h' e := by
    have h := congrArg (fun φ => φ.hom e)
      (stalkSpecializes_stalkMap_algebraMap h' P.genericPoint (genericPoint T) hp)
    rw [hgerm]
    refine h.trans ?_
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    congr 1
    exact algebraMap_stalk_genericPoint' T e
  have hu : IsUnit germ := by
    have hue : IsUnit ((T.presheaf.stalkSpecializes hp).hom e) :=
      (IsUnit.mk0 e he).map (T.presheaf.stalkSpecializes hp).hom
    exact hue.map _
  rw [← h1]
  exact P.ord_algebraMap_of_isUnit hu

/-- **The residue of a frame along a horizontal floor curve.** If locally over `T` the form
`h'^*e · Ω` generates `𝒪(M(K + B))`, its residue along a floor curve dominating `T` exists and is
nonzero. -/
private theorem exists_isPoincareResidue_of_frame {X T C : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hX : Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 2) {B : QDivisor X}
    (hB : Fourfold.IsPair sX B) (hdlt : MMP.Intersection.IsDltPair sX B) [IsIntegral T]
    (h' : X ⟶ T) [IsDominant h'] {M : ℕ} (hM : 0 < M) {Ω : RationalPluriForms sX 2 M}
    (hfr : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ e : T.functionField, e ≠ 0 ∧
      GeneratesOn B M (h' ⁻¹ᵁ U) (functionFieldMap h' e • Ω))
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] {j : C ⟶ X} {BC : QDivisor C}
    (hj : IsAdjunctionStep sX B j BC) [IsDominant (j ≫ h')] :
    ∃ ρ : RationalPluriForms (j ≫ sX) 1 M, ρ ≠ 0 ∧ IsPoincareResidue sX j 1 M Ω ρ := by
  classical
  have hXn : IsNormalVariety ℂ sX := hB.isPair.1
  haveI : LocallyOfFiniteType sX := hXn.1.toLocallyOfFiniteType
  obtain ⟨hT, P, hP1, hrange, hci, -⟩ := id hj
  haveI := hci
  have hdim2 : topologicalKrullDim X = ((2 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  have hBP : B.coeff P = 1 := le_antisymm (hdlt.2.1 P) hP1
  have hjη : j (genericPoint C) = P.genericPoint :=
    MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hrange
  have hPη : h' P.genericPoint = genericPoint T := by
    rw [← hjη]
    have := map_genericPoint_of_isDominant (j ≫ h')
    simpa using this
  obtain ⟨U, hU, e, he, hgen⟩ := hfr (genericPoint T)
  have hPU : (P.support ∩ (h' ⁻¹ᵁ U : Set X)).Nonempty :=
    ⟨P.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support _,
      show h' P.genericPoint ∈ U by rw [hPη]; exact hU⟩
  have he' : functionFieldMap h' e ≠ 0 := (map_ne_zero _).mpr he
  have hΩ0 : Ω ≠ 0 := fun h0 => hgen.1 (by rw [h0, smul_zero])
  have hord : P.ordForm Ω = -(M : ℤ) := by
    have h := hgen.2 P hPU
    rw [P.ordForm_smul_of_topologicalKrullDim_eq hdim2 he' hΩ0,
      ord_functionFieldMap_eq_zero_of_map_genericPoint h' P hPη he, zero_add, hBP] at h
    have : ((P.ordForm Ω : ℤ) : ℚ) = -(M : ℚ) := by linarith
    exact_mod_cast this
  obtain ⟨ρ, hρ⟩ := exists_isPoincareResidue_of_surface hXn hdim hj Ω
    fun P' hP' _ => by
      have : P' = P := MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support
        (hP' ▸ hjη ▸ MMP.Flips.primeDivisor_genericPoint_mem_support P)
      rw [this, hord]
  refine ⟨ρ, fun h0 => ?_, hρ⟩
  have hres := isPoincareResidue_functionFieldMap_smul h' hρ e
  rw [h0, smul_zero] at hres
  have := (ordForm_isPoincareResidue_of_generatesOn hX hdim hB hdlt hj hM hgen hres
    ⟨j (genericPoint C), ⟨_, rfl⟩, show h' (j (genericPoint C)) ∈ U by rw [hjη, hPη]; exact hU⟩).1
  exact this rfl

end HorizB

section HorizC

open MMP MMP.Fourfold MMP.Flips
open MMP.Mori hiding IsPair
open FloorAdjunction

/-- A morphism of integral schemes sending the generic point to the generic point is dominant. -/
private theorem isDominant_of_map_genericPoint {C T : Scheme.{0}} [IsIntegral C] [IsIntegral T]
    (f : C ⟶ T) (hf : f (genericPoint C) = genericPoint T) : IsDominant f := by
  rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
  refine Set.eq_univ_of_forall fun y => ?_
  exact closure_mono (Set.singleton_subset_iff.mpr
    (show genericPoint T ∈ Set.range f.base from ⟨_, hf⟩))
    (specializes_iff_mem_closure.mp ((genericPoint_spec T).specializes trivial))

/-- **Descent of horizontal residues.** At the endpoint `g : V ⟶ T` of the floor-lowering
program, the horizontal floor of `V` is a section, a bisection or two sections
(`IsMoriFibreSpace.isIrreducible_fibre_and_horizontalFloor_residue`), and every horizontal floor
curve of `X` is the strict transform of one of them. In every sufficiently divisible even degree
`M`, a system `t'` of `M`-canonical forms on the floor curves invariant under all crepant
birational maps between them is, along the horizontal floor curves, the system of residues of
`h'^*ψ · q^*Ω_M` for one `ψ ∈ k(T)`: in degree one the curve is birational to `T`; for two
sections the crepant identification over `T` matches the residues; for a bisection the residue
quotients are invariant under the deck group, hence pulled back from `T`. -/
private theorem exists_descent
    {X V T : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [IsIntegral T]
    {sV : V ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)}
    (q : X ⟶ V) [IsProper q] [IsDominant q] (hqb : IsBirationalMorphism q)
    (hX : Mori.IsProjectiveVariety ℂ (q ≫ sV)) (hdim : topologicalKrullDim X = 2)
    {B : QDivisor X} (hB : Fourfold.IsPair (q ≫ sV) B)
    (hdlt : MMP.Intersection.IsDltPair (q ≫ sV) B)
    (hVdim : topologicalKrullDim V = 2)
    (hVQ : IsQFactorial sV) {KV : Divisor V} (hKV : KV.IsCanonicalDivisor sV 2) {BV : QDivisor V}
    (hVlc : MMP.Intersection.IsLogCanonicalPair sV BV) {ε : ℚ} (hε : 0 < ε ∧ ε < 1)
    (hVklt : IsKltPair sV (BV - ε • Divisor.toQDivisor BV.roundDown))
    (g : V ⟶ T) [IsDominant g] [IsDominant (q ≫ g)]
    (hMFS : IsMoriFibreSpace sV sT KV (BV - ε • Divisor.toQDivisor BV.roundDown) g)
    (hT1 : topologicalKrullDim T = 1)
    (himg : q.base '' floorUnion B = floorUnion BV)
    (hcoef : ∀ Γ : Mori.PrimeDivisor V, ∃ Γ' : Mori.PrimeDivisor X,
      q Γ'.genericPoint = Γ.genericPoint ∧ IsIso (q.stalkMap Γ'.genericPoint) ∧
        BV.coeff Γ = B.coeff Γ')
    {d : ℕ} (hd : 0 < d) {ΩV : RationalPluriForms sV 2 d}
    (hfr : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ e : T.functionField, e ≠ 0 ∧
      GeneratesOn BV d (g ⁻¹ᵁ U) (functionFieldMap g e • ΩV) ∧
      GeneratesOn (sX := q ≫ sV) B d ((q ≫ g) ⁻¹ᵁ U)
        (functionFieldMap (q ≫ g) e • pullbackRationalPluriForms sV q ΩV))
    (C : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} → Scheme.{0})
    [∀ P, IsIntegral (C P)] [∀ P, IsLocallyNoetherian (C P)] [∀ P, IsNormal (C P)]
    (j : ∀ P, C P ⟶ X) (BC : ∀ P, QDivisor (C P))
    (hC : ∀ P, IsAdjunctionStep (q ≫ sV) B (j P) (BC P) ∧
      Set.range (j P).base = (P.1.support : Set X)) :
    ∃ m₁ : ℕ, 0 < m₁ ∧ ∀ M : ℕ, m₁ ∣ M → Even M → 0 < M →
      ∀ ΩM : RationalPluriForms sV 2 M,
      (∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ e : T.functionField, e ≠ 0 ∧
        GeneratesOn BV M (g ⁻¹ᵁ U) (functionFieldMap g e • ΩM) ∧
        GeneratesOn (sX := q ≫ sV) B M ((q ≫ g) ⁻¹ᵁ U)
          (functionFieldMap (q ≫ g) e • pullbackRationalPluriForms sV q ΩM)) →
      ∀ t' : ∀ P, RationalPluriForms (j P ≫ q ≫ sV) 1 M,
      (∀ P P' (σ : FunctionFieldEquiv (j P ≫ q ≫ sV) (j P' ≫ q ≫ sV)),
        IsCrepantBirationalMap (j P ≫ q ≫ sV) (j P' ≫ q ≫ sV) (BC P) (BC P') σ →
        pluriformPullback (j P ≫ q ≫ sV) (j P' ≫ q ≫ sV) σ.toHom 1 M (t' P') = t' P) →
      ∃ ψ : T.functionField, ∀ P, (q ≫ g) P.1.genericPoint = genericPoint T →
        IsPoincareResidue (q ≫ sV) (j P) 1 M
          (functionFieldMap (q ≫ g) ψ • pullbackRationalPluriForms sV q ΩM) (t' P) := by
  classical
  haveI : LocallyOfFiniteType sV := hVQ.1.1.toLocallyOfFiniteType
  haveI : QuasiCompact sV := (quasiCompact_iff_compactSpace sV).mpr inferInstance
  have hXn : IsNormalVariety ℂ (q ≫ sV) := hB.isPair.1
  haveI : LocallyOfFiniteType (q ≫ sV) := hXn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType q := LocallyOfFiniteType.of_comp (f := q) (g := sV) inferInstance
  have hbij := hqb.functionFieldMap_bijective
  haveI : IsProper g := isProper_of_isProjectiveMorphism g hMFS.isContraction.isProjectiveMorphism
  have hgc : IsClosedMap g.base := g.isClosedMap
  have hgT : g ≫ sT = sV := hMFS.isContraction.comp_eq
  have hd2 : (letI := Mori.functionFieldAlgebra sV
      (Algebra.trdeg ℂ V.functionField).toNat) = 1 + 1 :=
    Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (by rw [hVdim]; rfl)
  have hnum := isNumericallyTrivialOver_of_frame hVQ hKV g hd
    (fun t => by obtain ⟨U, hU, e, he, h1, -⟩ := hfr t; exact ⟨U, hU, e, he, h1⟩)
  obtain ⟨-, hH⟩ := IsMoriFibreSpace.isIrreducible_fibre_and_horizontalFloor_residue sV sT
    hVdim hVQ KV hKV BV hVlc ε hε hVklt g hMFS hT1 hnum
  -- the floor curves
  haveI hci : ∀ P, IsClosedImmersion (j P) := fun P => (hC P).1.2.choose_spec.2.2.1
  have hCdim : ∀ P, topologicalKrullDim (C P) = 1 := fun P => by
    have := topologicalKrullDim_eq_one_of_isAdjunctionStep hdim (hC P).1
    exact_mod_cast this
  have hCdim1 : ∀ P, topologicalKrullDim (C P) = ((1 : ℕ) : WithBot ℕ∞) := fun P => by
    rw [hCdim P]; rfl
  have hjη : ∀ P, j P (genericPoint (C P)) = P.1.genericPoint := fun P =>
    MMP.CyclicChartDifferent.Aux.map_genericPoint_eq (j P) P.1 (hC P).2
  haveI : ∀ P, CompactSpace (C P) := fun P => (j P).isClosedEmbedding.compactSpace
  haveI : ∀ P, LocallyOfFiniteType (j P ≫ q ≫ sV) := fun P => (hC P).1.1.1.toLocallyOfFiniteType
  have hdom : ∀ (P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0}),
      (q ≫ g) P.1.genericPoint = genericPoint T →
      IsDominant ((j P ≫ q) ≫ g) ∧ IsDominant (j P ≫ (q ≫ g)) := fun P hP =>
    ⟨isDominant_of_map_genericPoint _ (by
      change (q ≫ g) (j P (genericPoint (C P))) = _; rw [hjη]; exact hP),
     isDominant_of_map_genericPoint _ (by
      change (q ≫ g) (j P (genericPoint (C P))) = _; rw [hjη]; exact hP)⟩
  have hnormal : ∀ (P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0}) (E : Mori.PrimeDivisor V),
      q P.1.genericPoint = E.genericPoint →
      IsFinite (j P ≫ q) ∧ Set.range (j P ≫ q).base = (E.support : Set V) ∧
        ∃ _ : IsIntegral (C P), IsIso ((j P ≫ q).residueFieldMap (genericPoint (C P))) :=
    fun P E hη => isFinite_and_range_and_isIso_residueFieldMap (sV := sV) hVdim q hbij (j P)
      P.1 (hC P).2 (hCdim P) E hη
  have hfloorE : ∀ E : Mori.PrimeDivisor V, ⌊BV.coeff E⌋ ≠ 0 →
      ∃ P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0}, q P.1.genericPoint = E.genericPoint := by
    intro E hE
    obtain ⟨P', h1, -, hc⟩ := hcoef E
    exact ⟨⟨P', by rwa [← hc]⟩, h1⟩
  have hhor : ∀ P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0},
      (q ≫ g) P.1.genericPoint = genericPoint T → ∃ E : Mori.PrimeDivisor V,
        ⌊BV.coeff E⌋ ≠ 0 ∧ g E.genericPoint = genericPoint T ∧
          q P.1.genericPoint = E.genericPoint :=
    fun P hP => exists_horizontal_floor (sV := sV) hVdim hT1 q g hgc himg P.1 P.2 hP
  have huniq : ∀ (P P' : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0}) (E : Mori.PrimeDivisor V),
      q P.1.genericPoint = E.genericPoint → q P'.1.genericPoint = E.genericPoint → P = P' :=
    fun P P' E h h' => Subtype.ext (eq_of_map_genericPoint_eq hXn q hbij E h h')
  have hres : ∀ {M : ℕ}, 0 < M → ∀ ΩM : RationalPluriForms sV 2 M,
      (∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ e : T.functionField, e ≠ 0 ∧
        GeneratesOn BV M (g ⁻¹ᵁ U) (functionFieldMap g e • ΩM) ∧
        GeneratesOn (sX := q ≫ sV) B M ((q ≫ g) ⁻¹ᵁ U)
          (functionFieldMap (q ≫ g) e • pullbackRationalPluriForms sV q ΩM)) →
      ∀ P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0},
        (q ≫ g) P.1.genericPoint = genericPoint T →
        ∃ ρ : RationalPluriForms (j P ≫ q ≫ sV) 1 M, ρ ≠ 0 ∧
          IsPoincareResidue (q ≫ sV) (j P) 1 M (pullbackRationalPluriForms sV q ΩM) ρ := by
    intro M hM ΩM hfrM P hP
    haveI := (hdom P hP).2
    exact exists_isPoincareResidue_of_frame hX hdim hB hdlt (q ≫ g) hM
      (fun t => by obtain ⟨U, hU, e, he, -, h2⟩ := hfrM t; exact ⟨U, hU, e, he, h2⟩) (hC P).1
  rcases hH with ⟨E, hHE, hdegE, hisoE⟩ | ⟨E, hHE, hdegE, hallE⟩ |
    ⟨E₁, E₂, hne, hH12, hdeg₁, hdeg₂, hlink⟩
  · -- a single section
    have hEmem : E ∈ {P | ⌊BV.coeff P⌋ ≠ 0 ∧ g.base P.genericPoint = genericPoint T} := by
      rw [hHE]; rfl
    obtain ⟨P₁, hη₁⟩ := hfloorE E hEmem.1
    obtain ⟨hdomA, hdomB⟩ := hdom P₁ (by
      change g (q P₁.1.genericPoint) = _; rw [hη₁]; exact hEmem.2)
    haveI := hdomA
    haveI := hdomB
    have hiso := hisoE (C P₁) (j P₁ ≫ q) (hnormal P₁ E hη₁)
    have hb : Function.Bijective (functionFieldMap (j P₁ ≫ (q ≫ g))) := by
      have h1 := functionFieldMap_bijective_of_isIso (asIso ((j P₁ ≫ q) ≫ g))
      have h2 : functionFieldMap (j P₁ ≫ (q ≫ g)) = functionFieldMap ((j P₁ ≫ q) ≫ g) :=
        MMP.Positivity.DivisorOver.functionFieldMap_congr (Category.assoc _ _ _).symm
      rw [h2]
      exact h1
    refine ⟨1, one_pos, fun M _ _ hM0 ΩM hfrM t' _ => ?_⟩
    obtain ⟨ρ₁, hρ₁0, hρ₁⟩ := hres hM0 ΩM hfrM P₁ (by
      change g (q P₁.1.genericPoint) = _; rw [hη₁]; exact hEmem.2)
    obtain ⟨u, hu⟩ := exists_eq_smul_of_ne_zero (hCdim1 P₁) hρ₁0 (t' P₁)
    obtain ⟨ψ, hψ⟩ := hb.2 u
    refine ⟨ψ, fun P hP => ?_⟩
    obtain ⟨E', hE'1, hE'2, hηE'⟩ := hhor P hP
    have hE'E : E' = E := by
      have : E' ∈ {P | ⌊BV.coeff P⌋ ≠ 0 ∧ g.base P.genericPoint = genericPoint T} :=
        ⟨hE'1, hE'2⟩
      rw [hHE] at this
      exact this
    subst hE'E
    obtain rfl := huniq P P₁ E' hηE' hη₁
    rw [hu, ← hψ]
    exact isPoincareResidue_functionFieldMap_smul (q ≫ g) hρ₁ ψ
  · -- a bisection
    have hEmem : E ∈ {P | ⌊BV.coeff P⌋ ≠ 0 ∧ g.base P.genericPoint = genericPoint T} := by
      rw [hHE]; rfl
    obtain ⟨P₁, hη₁⟩ := hfloorE E hEmem.1
    have hP₁h : (q ≫ g) P₁.1.genericPoint = genericPoint T := by
      change g (q P₁.1.genericPoint) = _; rw [hη₁]; exact hEmem.2
    obtain ⟨hdomA, hdomB⟩ := hdom P₁ hP₁h
    haveI := hdomA
    haveI := hdomB
    haveI := isIso_stalkMap_of_map_eq_genericPoint q hbij P₁.1 E hη₁
    obtain ⟨Θ, hΘ, m₀, hm₀, hσall⟩ := hallE (C P₁) (j P₁ ≫ q) (hnormal P₁ E hη₁)
    obtain rfl : Θ = BC P₁ := eq_of_isAdjunctionBoundary q hqb hX hdim hVdim hB hdlt g hd hfr
      (hC P₁).1 P₁.1 (hC P₁).2 E hη₁ hΘ
    refine ⟨m₀, hm₀, fun M hdvd hev hM0 ΩM hfrM t' ht' => ?_⟩
    obtain ⟨ρ₁, hρ₁0, hρ₁⟩ := hres hM0 ΩM hfrM P₁ hP₁h
    obtain ⟨u, hu⟩ := exists_eq_smul_of_ne_zero (hCdim1 P₁) hρ₁0 (t' P₁)
    have hqΩ0 : pullbackRationalPluriForms sV q ΩM ≠ 0 := by
      obtain ⟨U, hU, e, he, -, h2⟩ := hfrM (genericPoint T)
      intro h0; apply h2.1; rw [h0, smul_zero]
    obtain ⟨ρV, hρV, hρVρ⟩ := exists_isPoincareResidue_of_pullback_eq q hbij (j P₁) P₁.1 (hjη P₁)
      E hη₁ hd2 hM0 rfl hqΩ0 hρ₁
    have hvert : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ φ : T.functionField,
        GeneratesOn BV M (g ⁻¹ᵁ U) (functionFieldMap g φ • ΩM) := fun t => by
      obtain ⟨U, hU, e, -, h1, -⟩ := hfrM t; exact ⟨U, hU, e, h1⟩
    have hfix : ∀ σ : FunctionFieldEquiv ((j P₁ ≫ q) ≫ sV) ((j P₁ ≫ q) ≫ sV),
        (∀ a, σ (functionFieldMap ((j P₁ ≫ q) ≫ g) a) = functionFieldMap ((j P₁ ≫ q) ≫ g) a) →
        σ u = u := by
      intro σ hσ
      obtain ⟨hcrep, hρinv⟩ := hσall σ hσ
      have hρinv' := hρinv M hdvd hev ΩM hvert ρV hρV
      obtain ⟨σ', hσσ', hcrep'⟩ := exists_isCrepantBirationalMap_congr
        (Category.assoc (j P₁) q sV) (Category.assoc (j P₁) q sV) σ hcrep
      have h1 := ht' P₁ P₁ σ' hcrep'
      have h2 := pluriformPullback_heq (Category.assoc (j P₁) q sV)
        (Category.assoc (j P₁) q sV) σ σ' hσσ' hρVρ
      rw [hρinv'] at h2
      have h3 : pluriformPullback _ _ σ'.toHom 1 M ρ₁ = ρ₁ := (eq_of_heq (hρVρ.symm.trans h2)).symm
      rw [hu, pluriformPullback_smul_left, h3] at h1
      have h4 : (σ'.toHom) u = u := smul_left_injective _ hρ₁0 h1
      exact ((hσσ' u).symm.trans h4 : _)
    have hνη : (j P₁ ≫ q).base (genericPoint (C P₁)) = E.genericPoint := by
      change q (j P₁ (genericPoint (C P₁))) = _; rw [hjη, hη₁]
    obtain ⟨ψ, hψ⟩ := exists_functionFieldMap_eq_of_forall_fixed (j P₁ ≫ q) g
      (hnormal P₁ E hη₁).2.2.choose_spec (by rw [hνη]; exact hdegE)
      (show ((j P₁ ≫ q) ≫ g) ≫ sT = (j P₁ ≫ q) ≫ sV by rw [Category.assoc, hgT]) u hfix
    refine ⟨ψ, fun P hP => ?_⟩
    obtain ⟨E', hE'1, hE'2, hηE'⟩ := hhor P hP
    have hE'E : E' = E := by
      have : E' ∈ {P | ⌊BV.coeff P⌋ ≠ 0 ∧ g.base P.genericPoint = genericPoint T} :=
        ⟨hE'1, hE'2⟩
      rw [hHE] at this
      exact this
    subst hE'E
    obtain rfl := huniq P P₁ E' hηE' hη₁
    have hψ' : functionFieldMap (j P ≫ (q ≫ g)) ψ = u := by
      rw [MMP.Positivity.DivisorOver.functionFieldMap_congr (Category.assoc _ _ _).symm]
      exact hψ
    rw [hu, ← hψ']
    exact isPoincareResidue_functionFieldMap_smul (q ≫ g) hρ₁ ψ
  · -- two sections
    have hE₁mem : E₁ ∈ {P | ⌊BV.coeff P⌋ ≠ 0 ∧ g.base P.genericPoint = genericPoint T} := by
      rw [hH12]; exact Or.inl rfl
    have hE₂mem : E₂ ∈ {P | ⌊BV.coeff P⌋ ≠ 0 ∧ g.base P.genericPoint = genericPoint T} := by
      rw [hH12]; exact Or.inr rfl
    obtain ⟨P₁, hη₁⟩ := hfloorE E₁ hE₁mem.1
    obtain ⟨P₂, hη₂⟩ := hfloorE E₂ hE₂mem.1
    have hP₁h : (q ≫ g) P₁.1.genericPoint = genericPoint T := by
      change g (q P₁.1.genericPoint) = _; rw [hη₁]; exact hE₁mem.2
    have hP₂h : (q ≫ g) P₂.1.genericPoint = genericPoint T := by
      change g (q P₂.1.genericPoint) = _; rw [hη₂]; exact hE₂mem.2
    obtain ⟨hdom₁A, hdom₁B⟩ := hdom P₁ hP₁h
    obtain ⟨hdom₂A, hdom₂B⟩ := hdom P₂ hP₂h
    haveI := hdom₁A
    haveI := hdom₁B
    haveI := hdom₂A
    haveI := hdom₂B
    haveI := isIso_stalkMap_of_map_eq_genericPoint q hbij P₁.1 E₁ hη₁
    haveI := isIso_stalkMap_of_map_eq_genericPoint q hbij P₂.1 E₂ hη₂
    obtain ⟨Θ₁, hΘ₁, Θ₂, hΘ₂, m₀, hm₀, hσall⟩ := hlink (C P₁) (j P₁ ≫ q) (C P₂) (j P₂ ≫ q)
      (hnormal P₁ E₁ hη₁) (hnormal P₂ E₂ hη₂)
    obtain rfl : Θ₁ = BC P₁ := eq_of_isAdjunctionBoundary q hqb hX hdim hVdim hB hdlt g hd hfr
      (hC P₁).1 P₁.1 (hC P₁).2 E₁ hη₁ hΘ₁
    obtain rfl : Θ₂ = BC P₂ := eq_of_isAdjunctionBoundary q hqb hX hdim hVdim hB hdlt g hd hfr
      (hC P₂).1 P₂.1 (hC P₂).2 E₂ hη₂ hΘ₂
    have hνη₁ : (j P₁ ≫ q).base (genericPoint (C P₁)) = E₁.genericPoint := by
      change q (j P₁ (genericPoint (C P₁))) = _; rw [hjη, hη₁]
    have hνη₂ : (j P₂ ≫ q).base (genericPoint (C P₂)) = E₂.genericPoint := by
      change q (j P₂ (genericPoint (C P₂))) = _; rw [hjη, hη₂]
    have hb₁ := bijective_functionFieldMap_of_finrank_eq_one (j P₁ ≫ q) g
      (hnormal P₁ E₁ hη₁).2.2.choose_spec (by rw [hνη₁]; exact hdeg₁)
    have hb₂ := bijective_functionFieldMap_of_finrank_eq_one (j P₂ ≫ q) g
      (hnormal P₂ E₂ hη₂).2.2.choose_spec (by rw [hνη₂]; exact hdeg₂)
    obtain ⟨σ₀, hσ₀⟩ := exists_functionFieldEquiv_over sT ((j P₁ ≫ q) ≫ g) ((j P₂ ≫ q) ≫ g)
      hb₁ hb₂ (s₁ := (j P₁ ≫ q) ≫ sV) (s₂ := (j P₂ ≫ q) ≫ sV) (by rw [Category.assoc, hgT])
      (by rw [Category.assoc, hgT])
    obtain ⟨hcrep, hlinkρ⟩ := hσall σ₀ hσ₀
    obtain ⟨σ', hσσ', hcrep'⟩ := exists_isCrepantBirationalMap_congr
      (Category.assoc (j P₁) q sV) (Category.assoc (j P₂) q sV) σ₀ hcrep
    refine ⟨m₀, hm₀, fun M hdvd hev hM0 ΩM hfrM t' ht' => ?_⟩
    obtain ⟨ρ₁, hρ₁0, hρ₁⟩ := hres hM0 ΩM hfrM P₁ hP₁h
    obtain ⟨ρ₂, hρ₂0, hρ₂⟩ := hres hM0 ΩM hfrM P₂ hP₂h
    obtain ⟨u₁, hu₁⟩ := exists_eq_smul_of_ne_zero (hCdim1 P₁) hρ₁0 (t' P₁)
    obtain ⟨u₂, hu₂⟩ := exists_eq_smul_of_ne_zero (hCdim1 P₂) hρ₂0 (t' P₂)
    have hqΩ0 : pullbackRationalPluriForms sV q ΩM ≠ 0 := by
      obtain ⟨U, hU, e, he, -, h2⟩ := hfrM (genericPoint T)
      intro h0; apply h2.1; rw [h0, smul_zero]
    obtain ⟨ρV₁, hρV₁, hρV₁ρ⟩ := exists_isPoincareResidue_of_pullback_eq q hbij (j P₁) P₁.1
      (hjη P₁) E₁ hη₁ hd2 hM0 rfl hqΩ0 hρ₁
    obtain ⟨ρV₂, hρV₂, hρV₂ρ⟩ := exists_isPoincareResidue_of_pullback_eq q hbij (j P₂) P₂.1
      (hjη P₂) E₂ hη₂ hd2 hM0 rfl hqΩ0 hρ₂
    have hvert : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ φ : T.functionField,
        GeneratesOn BV M (g ⁻¹ᵁ U) (functionFieldMap g φ • ΩM) := fun t => by
      obtain ⟨U, hU, e, -, h1, -⟩ := hfrM t; exact ⟨U, hU, e, h1⟩
    have hl := hlinkρ M hdvd hev ΩM hvert ρV₁ ρV₂ hρV₁ hρV₂
    have h2 := pluriformPullback_heq (Category.assoc (j P₁) q sV)
      (Category.assoc (j P₂) q sV) σ₀ σ' hσσ' hρV₂ρ
    rw [hl] at h2
    have h3 : pluriformPullback _ _ σ'.toHom 1 M ρ₂ = ρ₁ := eq_of_heq (h2.symm.trans hρV₁ρ)
    have h1 := ht' P₁ P₂ σ' hcrep'
    rw [hu₂, hu₁, pluriformPullback_smul_left, h3] at h1
    have h4 : (σ'.toHom) u₂ = u₁ := smul_left_injective _ hρ₁0 h1
    obtain ⟨ψ₁, hψ₁⟩ := hb₁.2 u₁
    obtain ⟨ψ₂, hψ₂⟩ := hb₂.2 u₂
    have h5 : functionFieldMap ((j P₁ ≫ q) ≫ g) ψ₂ = functionFieldMap ((j P₁ ≫ q) ≫ g) ψ₁ := by
      rw [← hσ₀ ψ₂, hψ₂, hψ₁, ← h4, hσσ' u₂]
      rfl
    have hψ : ψ₂ = ψ₁ := (functionFieldMap _).injective h5
    refine ⟨ψ₁, fun P hP => ?_⟩
    obtain ⟨E', hE'1, hE'2, hηE'⟩ := hhor P hP
    have hE' : E' ∈ ({E₁, E₂} : Set (Mori.PrimeDivisor V)) := hH12 ▸ ⟨hE'1, hE'2⟩
    rcases hE' with rfl | rfl
    · obtain rfl := huniq P P₁ _ hηE' hη₁
      have hψ' : functionFieldMap (j P ≫ (q ≫ g)) ψ₁ = u₁ := by
        rw [MMP.Positivity.DivisorOver.functionFieldMap_congr (Category.assoc _ _ _).symm]
        exact hψ₁
      rw [hu₁, ← hψ']
      exact isPoincareResidue_functionFieldMap_smul (q ≫ g) hρ₁ ψ₁
    · obtain rfl := huniq P P₂ _ hηE' hη₂
      have hψ' : functionFieldMap (j P ≫ (q ≫ g)) ψ₁ = u₂ := by
        rw [MMP.Positivity.DivisorOver.functionFieldMap_congr (Category.assoc _ _ _).symm, ← hψ]
        exact hψ₂
      rw [hu₂, ← hψ']
      exact isPoincareResidue_functionFieldMap_smul (q ≫ g) hρ₂ ψ₁

end HorizC

section HorizD

open MMP MMP.Fourfold MMP.Flips
open MMP.Mori hiding IsPair
open FloorAdjunction

section NodeLoc

open MMP.Mori MMP.Fourfold Scheme IsLocalRing

private theorem exists_isUnit_eq_smul_tprod_ιMulti_loc {S : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sS]
    (hdim : topologicalKrullDim S = 2) {B : QDivisor S}
    {P Q : MMP.Mori.PrimeDivisor S} (hPQ : P ≠ Q) (hP : B.coeff P = 1) (hQ : B.coeff Q = 1)
    {x : S} (hxc : IsClosed ({x} : Set S)) (hx : x ∈ (P.support : Set S) ∩ Q.support)
    {u v : S.presheaf.stalk x} (hspan : Ideal.span {u, v} = maximalIdeal (S.presheaf.stalk x))
    (hreg : MMP.Mori.IsRegularSystemOfParameters ![u, v])
    (hu : IdealSheafData.stalk P.idealSheaf x = Ideal.span {u})
    (hv : IdealSheafData.stalk Q.idealSheaf x = Ideal.span {v})
    (hB : ∀ Γ : MMP.Mori.PrimeDivisor S, x ∈ Γ.support → B.coeff Γ ≠ 0 → Γ = P ∨ Γ = Q)
    {m : ℕ} {ω : RationalPluriForms sS 2 m} (hω0 : ω ≠ 0)
    (hω : ∀ Γ : MMP.Mori.PrimeDivisor S, x ∈ Γ.support → (Γ.ordForm ω : ℚ) = -(m * B.coeff Γ)) :
    ∃ a : S.presheaf.stalk x, IsUnit a ∧
      letI := MMP.Mori.functionFieldAlgebra sS
      ω = ((algebraMap _ S.functionField a *
          (algebraMap _ S.functionField u * algebraMap _ S.functionField v)⁻¹ ^ m) •
        PiTensorProduct.tprod S.functionField (fun _ : Fin m =>
          exteriorPower.ιMulti S.functionField 2 (fun i => KaehlerDifferential.D ℂ S.functionField
            (algebraMap _ S.functionField (![u, v] i)))) :
        TensorPower S.functionField m (⋀[S.functionField]^2 Ω[S.functionField⁄ℂ])) := by
  classical
  letI := MMP.Mori.functionFieldAlgebra sS
  letI := MMP.Mori.stalkAlgebra sS x
  haveI := MMP.Mori.isScalarTower_stalk_functionField sS x
  have hdim2 : topologicalKrullDim S = ((2 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  have hrange : Ideal.span (Set.range ![u, v]) = maximalIdeal (S.presheaf.stalk x) := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
    exact hspan
  have ht := span_range_D_stalk_eq_top sS x hxc ![u, v] hrange
  set w : ⋀[S.functionField]^2 Ω[S.functionField⁄ℂ] := exteriorPower.ιMulti S.functionField 2
    (fun i => KaehlerDifferential.D ℂ S.functionField (algebraMap _ S.functionField (![u, v] i)))
    with hwdef
  -- `w` spans the line of top forms
  have := MMP.Mori.essFiniteType_functionField (sX := sS)
  have hfin : Module.finrank S.functionField Ω[S.functionField⁄ℂ] = 2 :=
    (MMP.Mori.finrank_kaehlerDifferential_eq_trdeg ℂ S.functionField).trans
      (MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq hdim2)
  have : FiniteDimensional S.functionField Ω[S.functionField⁄ℂ] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent ℂ S.functionField).1
  have hK : Submodule.span S.functionField (Set.range fun i =>
      KaehlerDifferential.D ℂ S.functionField (algebraMap _ S.functionField (![u, v] i))) = ⊤ :=
    span_range_D_algebraMap_eq_top (exists_mul_algebraMap_eq x) ![u, v] ht
  have hli := linearIndependent_of_top_le_span_of_card_eq_finrank hK.ge
    (by rw [Fintype.card_fin, hfin])
  have hw0 : w ≠ 0 := ιMulti_ne_zero_of_linearIndependent hli
  have h1 : Module.finrank S.functionField (⋀[S.functionField]^2 Ω[S.functionField⁄ℂ]) = 1 := by
    rw [exteriorPower.finrank_eq, hfin, Nat.choose_self]
  have hwspan := (finrank_eq_one_iff_of_nonzero w hw0).mp h1
  let b := MMP.Mori.basisOfSpanSingleton hwspan hw0
  let e : Module.Basis Unit S.functionField (RationalPluriForms sS 2 m) :=
    MMP.Mori.ZTensorPower.basis b (m : ℤ)
  have he : (e () : TensorPower S.functionField m (⋀[S.functionField]^2 Ω[S.functionField⁄ℂ])) =
      PiTensorProduct.tprod S.functionField (fun _ : Fin m => w) := by
    have := MMP.Mori.ZTensorPower.basis_ofNat b m
    rw [MMP.Mori.basisOfSpanSingleton_apply] at this
    exact this
  set g := e.repr ω () with hgdef
  have hg : ω = (g • PiTensorProduct.tprod S.functionField (fun _ : Fin m => w) :
      TensorPower S.functionField m (⋀[S.functionField]^2 Ω[S.functionField⁄ℂ])) := by
    rw [← he]
    exact (MMP.Mori.basis_unit_repr_smul e ω).symm
  have hg0 : g ≠ 0 := by
    intro h; apply hω0; rw [hg, h, zero_smul]; rfl
  have hordg : ∀ Γ : MMP.Mori.PrimeDivisor S, x ∈ Γ.support →
      S.ord g Γ.genericPoint = Γ.ordForm ω := fun Γ hΓ =>
    (ordForm_smul_tprod_ιMulti_D hdim2 x ![u, v] ht Γ hΓ g ω hg).symm
  haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hreg
  have hu0 : algebraMap _ S.functionField u ≠ 0 := fun h =>
    MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hreg 0
      (IsFractionRing.injective (S.presheaf.stalk x) S.functionField (h.trans (map_zero _).symm))
  have hv0 : algebraMap _ S.functionField v ≠ 0 := fun h =>
    MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hreg 1
      (IsFractionRing.injective (S.presheaf.stalk x) S.functionField (h.trans (map_zero _).symm))
  set h := g * (algebraMap _ S.functionField u * algebraMap _ S.functionField v) ^ m with hhdef
  have huv0 : algebraMap _ S.functionField u * algebraMap _ S.functionField v ≠ 0 :=
    mul_ne_zero hu0 hv0
  have hh0 : h ≠ 0 := mul_ne_zero hg0 (pow_ne_zero _ huv0)
  have hordh : ∀ Γ : MMP.Mori.PrimeDivisor S, x ∈ Γ.support → S.ord h Γ.genericPoint = 0 := by
    intro Γ hΓ
    have hou := ord_algebraMap_eq_ite_of_stalk_eq_span' hreg 0 P hx.1 hu Γ hΓ
    have hov := ord_algebraMap_eq_ite_of_stalk_eq_span' hreg 1 Q hx.2 hv Γ hΓ
    have hpow := MMP.Mori.ord_zpow Γ.genericPoint huv0 (m : ℤ)
    rw [zpow_natCast] at hpow
    rw [hhdef, Scheme.ord_mul hg0 (pow_ne_zero _ huv0), hpow, Scheme.ord_mul hu0 hv0, hordg Γ hΓ]
    have hcoef := hω Γ hΓ
    change S.ord (algebraMap _ S.functionField (![u, v] 0)) Γ.genericPoint = _ at hou
    change S.ord (algebraMap _ S.functionField (![u, v] 1)) Γ.genericPoint = _ at hov
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hou hov
    rw [hou, hov]
    by_cases hΓP : Γ = P
    · subst hΓP
      rw [if_pos rfl, if_neg hPQ]
      rw [hP] at hcoef
      have : (Γ.ordForm ω : ℚ) = -m := by rw [hcoef]; ring
      have : Γ.ordForm ω = -(m : ℤ) := by exact_mod_cast this
      rw [this]; ring
    · by_cases hΓQ : Γ = Q
      · subst hΓQ
        rw [if_neg hΓP, if_pos rfl]
        rw [hQ] at hcoef
        have : (Γ.ordForm ω : ℚ) = -m := by rw [hcoef]; ring
        have : Γ.ordForm ω = -(m : ℤ) := by exact_mod_cast this
        rw [this]; ring
      · rw [if_neg hΓP, if_neg hΓQ]
        have hB0 : B.coeff Γ = 0 := by
          by_contra hne
          rcases hB Γ hΓ hne with h | h
          · exact hΓP h
          · exact hΓQ h
        rw [hB0, mul_zero, neg_zero] at hcoef
        have : Γ.ordForm ω = 0 := by exact_mod_cast hcoef
        rw [this]; ring
  obtain ⟨a, ha, hah⟩ := MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero x hh0 hordh
  refine ⟨a, ha, ?_⟩
  rw [hg, hah, hhdef, mul_assoc, ← mul_pow, mul_inv_cancel₀ huv0, one_pow, mul_one]

open IsLocalRing in
/-- **The point stratum of a node on one branch.** Let `j : C ⟶ S` be an adjunction step onto
a floor curve `P` of a dlt surface, meeting a second floor curve `Q` at a closed point `x`, with
coordinates `P = (u)`, `Q = (v)` at `x`, and let `ω = a · (du/u ∧ dv/v)^{⊗m}` with `a` a unit,
`a ≡ λ` modulo `𝔪_x`. If `ρ = Res_C ω` has `div ρ = -m B_C`, the point of `C` over `x` is a
stratum of `(C, B_C)` reached by a flag along which the iterated residue of `ρ` is `λ · 1^{⊗m}`. -/
private theorem exists_pointStratum_of_branch_loc {S : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sS]
    (hdim : topologicalKrullDim S = 2) {B : QDivisor S}
    {C : Scheme.{0}} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    {j : C ⟶ S} {BC : QDivisor C} (hj : IsAdjunctionStep sS B j BC)
    (hdltC : MMP.Intersection.IsDltPair (j ≫ sS) BC)
    {P Q : MMP.Mori.PrimeDivisor S} (hPQ : P ≠ Q) (hP : Set.range j.base = (P.support : Set S))
    {x : S} (hxc : IsClosed ({x} : Set S)) (hxP : x ∈ P.support) (hxQ : x ∈ Q.support)
    {x' : C} (hx' : j x' = x)
    {u v a : S.presheaf.stalk x} (hspan : Ideal.span {u, v} = maximalIdeal (S.presheaf.stalk x))
    (hreg : MMP.Mori.IsRegularSystemOfParameters ![u, v])
    (hu : IdealSheafData.stalk P.idealSheaf x = Ideal.span {u})
    (hv : IdealSheafData.stalk Q.idealSheaf x = Ideal.span {v}) (ha : IsUnit a) {lam : ℂ}
    (hlam : a - (letI := MMP.Mori.stalkAlgebra sS x; algebraMap ℂ _ lam) ∈
      maximalIdeal (S.presheaf.stalk x))
    {m : ℕ} (hm : 0 < m) {ω : RationalPluriForms sS 2 m}
    (hω : letI := MMP.Mori.functionFieldAlgebra sS
      ω = ((algebraMap _ S.functionField a *
          (algebraMap _ S.functionField u * algebraMap _ S.functionField v)⁻¹ ^ m) •
        PiTensorProduct.tprod S.functionField (fun _ : Fin m =>
          exteriorPower.ιMulti S.functionField 2 (fun i => KaehlerDifferential.D ℂ S.functionField
            (algebraMap _ S.functionField (![u, v] i)))) :
        TensorPower S.functionField m (⋀[S.functionField]^2 Ω[S.functionField⁄ℂ])))
    {ρ : RationalPluriForms (j ≫ sS) 1 m} (hρ : IsPoincareResidue sS j 1 m ω ρ)
    (hρord : ∀ Q' : MMP.Mori.PrimeDivisor C, Q'.genericPoint = x' →
      (Q'.ordForm ρ : ℚ) = -(m * BC.coeff Q'))
    {b : C.presheaf.stalk x'} {β : ℂ}
    (hb : b - (letI := MMP.Mori.stalkAlgebra (j ≫ sS) x'; algebraMap ℂ _ β) ∈
      maximalIdeal (C.presheaf.stalk x')) :
    ∃ (T : Scheme.{0}) (ιT : T ⟶ C) (BT : QDivisor T)
      (F : StratumAdjunctionData (j ≫ sS) BC ιT BT),
      topologicalKrullDim T = 0 ∧
      (haveI := F.isIntegral_stratum
       letI := MMP.Mori.functionFieldAlgebra (ιT ≫ j ≫ sS)
       IsIteratedResidue (j ≫ sS) BC (algebraMap _ C.functionField b • ρ) F 0
        (algebraMap ℂ T.functionField (β * lam) •
          (MMP.Fourfold.formPow (k := ℂ) (exteriorPower.ιMulti T.functionField 0 Fin.elim0) m :
            RationalPluriForms (ιT ≫ j ≫ sS) 0 m))) := by
  classical
  subst hx'
  haveI : LocallyOfFiniteType (j ≫ sS) := hj.1.1.toLocallyOfFiniteType
  haveI : IsClosedImmersion j := hj.2.choose_spec.2.2.1
  have hdimC : topologicalKrullDim C = 1 :=
    MMP.Fourfold.topologicalKrullDim_eq_of_range_eq_support sS (n := 1)
      (by rw [hdim]; rfl) j P hP
  -- the residue along `C`
  have hρ' := isPoincareResidue_smul_tprod_dlog j hPQ hP x' hxQ hreg hu hv ha hω
  have hρeq := IsPoincareResidue.unique hj hρ hρ'
  set ψ := (j.stalkMap x').hom with hψ
  obtain ⟨hu0, hmax, hcoh, hord⟩ := stalkMap_facts_of_mem_inter j hPQ hP hdimC x' hxQ hspan hu
  -- the point `x'` is closed in `C`
  have hx'c : IsClosed ({x'} : Set C) := by
    have : ({x'} : Set C) = j.base ⁻¹' {j x'} := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ rfl, fun h => j.isClosedEmbedding.injective h⟩
    rw [this]
    exact hxc.preimage j.base.hom.continuous
  -- the prime divisor `x'` of `C` has coefficient one in `B_C`
  let E : MMP.Mori.PrimeDivisor C := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x' hcoh
  have hE : E.genericPoint = x' :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x' hcoh
  have hE' : AlgebraicGeometry.PrimeDivisor.genericPoint E = x' :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x' hcoh
  have hEx : x' ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hE']; exact subset_closure rfl
  have hEsupp : (E.support : Set C) = {x'} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hE', hx'c.closure_eq]
  letI := MMP.Mori.functionFieldAlgebra (j ≫ sS)
  have hdimC1 : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞) := by rw [hdimC]; rfl
  have htC : Submodule.span (C.presheaf.stalk x') (Set.range fun _ : Fin 1 =>
      (letI := MMP.Mori.stalkAlgebra (j ≫ sS) x';
        KaehlerDifferential.D ℂ (C.presheaf.stalk x') (ψ v))) = ⊤ :=
    span_range_D_stalk_eq_top (j ≫ sS) x' hx'c (fun _ => ψ v) (by rw [Set.range_const]; exact hmax)
  have hψa : IsUnit (ψ a) := ha.map ψ
  have hψa0 : algebraMap _ C.functionField (ψ a) ≠ 0 :=
    (hψa.map (algebraMap _ C.functionField)).ne_zero
  have hψv0 : algebraMap _ C.functionField (ψ v) ≠ 0 := by
    intro h0; rw [h0] at hord; simp at hord
  have hordE := ordForm_smul_tprod_ιMulti_D hdimC1 x' (fun _ => ψ v) htC E hEx
    (algebraMap _ C.functionField (ψ a) * (algebraMap _ C.functionField (ψ v))⁻¹ ^ m) _ hρeq
  have hcoef : BC.coeff E = 1 := by
    have h1 := hρord E hE
    have hord' : C.ord (algebraMap _ C.functionField (ψ v)) E.genericPoint = 1 := by
      rw [hE]; exact hord
    rw [hordE, Scheme.ord_mul hψa0 (pow_ne_zero _ (inv_ne_zero hψv0)),
      ord_algebraMap_eq_zero_of_isUnit' E hE.symm hψa, ← zpow_natCast,
      MMP.Mori.ord_zpow _ (inv_ne_zero hψv0), ← zpow_neg_one,
      MMP.Mori.ord_zpow _ hψv0, hord'] at h1
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast at h1
    have : (m : ℚ) * (BC.coeff E - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hm'
    · linarith
  -- the point is a dlt stratum, reached by a flag
  have hstr : IsDltStratum (j ≫ sS) BC {x'} := by
    refine ⟨hdltC, {E}, Finset.singleton_nonempty _, fun R hR => ?_, ?_, ?_⟩
    · rw [Finset.mem_singleton.mp hR, hcoef]
    · refine ⟨x', ?_⟩
      simp only [Finset.mem_singleton, Set.mem_iInter]
      rintro R rfl; exact hEx
    · have hI : (⋂ R ∈ ({E} : Finset (MMP.Mori.PrimeDivisor C)), (R.support : Set C)) = {x'} := by
        simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left, hEsupp]
      rw [hI]
      exact ⟨⟨isIrreducible_singleton, le_rfl⟩, fun T hT _ => hT.2⟩
  obtain ⟨⟨⟨T, ι, BT, hrange, ⟨F⟩⟩, -⟩, -⟩ :=
    IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair hstr
  have hlen := length_le_and_topologicalKrullDim_eq hdimC1 F
  cases F with
  | refl h0 =>
    exfalso
    have hη : genericPoint C ∈ Set.range (𝟙 C : C ⟶ C).base := ⟨genericPoint C, rfl⟩
    rw [hrange, Set.mem_singleton_iff] at hη
    have hmax' : IsMax (genericPoint C) := fun b _ => (genericPoint_spec C).specializes trivial
    rw [← hη, Order.coheight_eq_zero.mpr hmax'] at hcoh
    exact absurd hcoh (by decide)
  | step F₀ j' BT' h' =>
    cases F₀ with
    | step F₁ j₁ BT₁ h₁ =>
      exfalso
      have := hlen.1
      change F₁.length + 1 + 1 ≤ 1 at this
      omega
    | refl h0 =>
      haveI : IsIntegral T := h'.1.1.toIsIntegral
      refine ⟨T, j' ≫ 𝟙 C, BT, .step (.refl h0) j' BT h', ?_, ?_⟩
      · rw [hlen.2]; rfl
      · have hjT : j' (genericPoint T) = x' := by
          have : (j' ≫ 𝟙 C).base (genericPoint T) ∈ Set.range (j' ≫ 𝟙 C).base := ⟨_, rfl⟩
          rw [hrange, Set.mem_singleton_iff] at this
          simpa using this
        subst hjT
        have hres0 := isPoincareResidue_smul_tprod_dlog_point (b := ψ a) (sC := j ≫ sS) j' hord m
        have hres1 := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hres0 b
        refine isIteratedResidue_step_refl h0 h' _ ⟨_, by rw [hρeq]; exact hres1, ?_⟩
        -- the value of `ā` at the point
        have hval : (j'.stalkMap (genericPoint T)).hom (ψ a) =
            (letI := MMP.Mori.functionFieldAlgebra (j' ≫ j ≫ sS);
              algebraMap ℂ T.functionField lam) := by
          set φ := (j'.stalkMap (genericPoint T)).hom.comp ψ
          have h0' := map_eq_zero_of_mem_maximalIdeal φ hlam
          rw [map_sub, sub_eq_zero] at h0'
          change (j'.stalkMap (genericPoint T)).hom (ψ a) = _ at h0'
          rw [h0']
          change (j'.stalkMap (genericPoint T)).hom ((j.stalkMap (j' (genericPoint T))).hom
            (letI := MMP.Mori.stalkAlgebra sS (j (j' (genericPoint T))); algebraMap ℂ _ lam)) = _
          rw [stalkMap_algebraMap' sS j, stalkMap_algebraMap' (j ≫ sS) j']
        have hvalb : (j'.stalkMap (genericPoint T)).hom b =
            (letI := MMP.Mori.functionFieldAlgebra (j' ≫ j ≫ sS);
              algebraMap ℂ T.functionField β) := by
          have h0' := map_eq_zero_of_mem_maximalIdeal (j'.stalkMap (genericPoint T)).hom hb
          rw [map_sub, sub_eq_zero] at h0'
          rw [h0', stalkMap_algebraMap' (j ≫ sS) j']
        refine HEq.trans (heq_algebraMap_smul_formPow (by simp) (β * lam) m) (heq_of_eq ?_)
        rw [hvalb, hval, map_mul]
        exact mul_smul _ _ _

open IsLocalRing in
/-- **Node matching.** Let two floor curves `C_P`, `C_Q` of a projective dlt surface meet at a
closed point `x`, `ω` a generator of `𝒪(m(K + B))` near `x`, and `t` an admissible system with
`t_P = b_P · Res_P ω`, `t_Q = b_Q · Res_Q ω`, where `b_P`, `b_Q` are regular at the points over
`x` with values `β_P`, `β_Q`. Then `β_P = β_Q`: the point strata of `x` on the two curves are
crepant, and the even iterated residues of `ω` along the two branches agree. -/
private theorem value_eq_of_mem_inter
    {S : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} (hS : Mori.IsProjectiveVariety ℂ sS)
    (hdim : topologicalKrullDim S = 2) {B : QDivisor S} (hB : Fourfold.IsPair sS B)
    (hdlt : MMP.Intersection.IsDltPair sS B)
    (C : {P : Mori.PrimeDivisor S // ⌊B.coeff P⌋ ≠ 0} → Scheme.{0})
    [∀ P, IsIntegral (C P)] [∀ P, IsLocallyNoetherian (C P)] [∀ P, IsNormal (C P)]
    (j : ∀ P, C P ⟶ S) (BC : ∀ P, QDivisor (C P))
    (hC : ∀ P, IsAdjunctionStep sS B (j P) (BC P) ∧
      Set.range (j P).base = (P.1.support : Set S))
    {m : ℕ} (hm0 : 0 < m)
    (R : ResidueRestriction (fun P => j P ≫ sS) BC 1 m) {t : ∀ P, _}
    (ht : t ∈ admissibleSections R) {P Q : {P : Mori.PrimeDivisor S // ⌊B.coeff P⌋ ≠ 0}}
    (hne : P ≠ Q) {x : S} (hxc : IsClosed ({x} : Set S)) (hxP : x ∈ P.1.support)
    (hxQ : x ∈ Q.1.support) {U : S.Opens} (hxU : x ∈ U) {ω : RationalPluriForms sS 2 m}
    (hω : GeneratesOn B m U ω) {ρP : RationalPluriForms (j P ≫ sS) 1 m}
    (hρP : IsPoincareResidue sS (j P) 1 m ω ρP) {ρQ : RationalPluriForms (j Q ≫ sS) 1 m}
    (hρQ : IsPoincareResidue sS (j Q) 1 m ω ρQ) {xP : C P} (hxP' : j P xP = x) {xQ : C Q}
    (hxQ' : j Q xQ = x) {bP : (C P).presheaf.stalk xP} {βP : ℂ}
    (hbP : bP - (letI := MMP.Mori.stalkAlgebra (j P ≫ sS) xP; algebraMap ℂ _ βP) ∈
      maximalIdeal ((C P).presheaf.stalk xP))
    {bQ : (C Q).presheaf.stalk xQ} {βQ : ℂ}
    (hbQ : bQ - (letI := MMP.Mori.stalkAlgebra (j Q ≫ sS) xQ; algebraMap ℂ _ βQ) ∈
      maximalIdeal ((C Q).presheaf.stalk xQ))
    (htP : (t P : RationalPluriForms (j P ≫ sS) 1 m) =
      algebraMap _ (C P).functionField bP • ρP)
    (htQ : (t Q : RationalPluriForms (j Q ≫ sS) 1 m) =
      algebraMap _ (C Q).functionField bQ • ρQ) : βP = βQ := by
  classical
  have hX : Mori.IsNormalVariety ℂ sS := hB.isPair.1
  haveI : LocallyOfFiniteType sS := hX.1.toLocallyOfFiniteType
  have hPQ' : P.1 ≠ Q.1 := fun h => hne (Subtype.ext h)
  have hBP : ∀ P : {P : Mori.PrimeDivisor S // ⌊B.coeff P⌋ ≠ 0}, B.coeff P.1 = 1 := fun P =>
    eq_one_of_floor_ne_zero (hB.nonneg P.1) (hdlt.2.1 P.1) P.2
  have hx : x ∈ (P.1.support : Set S) ∩ Q.1.support := ⟨hxP, hxQ⟩
  obtain ⟨Z, -, hsnc, hpos⟩ := hdlt.2.2
  have hxZ := notMem_of_mem_inter_of_isDltPair hdim hdlt hpos hPQ' (hBP P).ge (hBP Q).ge hx
  obtain ⟨u, v, hspan, hreg, hu, hv, hBx⟩ := exists_coordinates_of_mem_inter hdim hsnc hPQ'
    (by rw [hBP P]; exact one_ne_zero) (by rw [hBP Q]; exact one_ne_zero) hx hxZ
  obtain ⟨a, ha, hωa⟩ := exists_isUnit_eq_smul_tprod_ιMulti_loc hdim hPQ' (hBP P) (hBP Q) hxc hx
    hspan hreg hu hv hBx hω.1 fun Γ hΓ => by
      have := hω.2 Γ ⟨x, hΓ, hxU⟩; linarith
  obtain ⟨lam, hlam⟩ := exists_sub_algebraMap_mem_maximalIdeal sS x hxc a
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [map_zero, sub_zero] at hlam
    exact (IsLocalRing.mem_maximalIdeal _).mp hlam ha
  have hordP : ∀ Q' : MMP.Mori.PrimeDivisor (C P), Q'.genericPoint = xP →
      (Q'.ordForm ρP : ℚ) = -(m * (BC P).coeff Q') := fun Q' hQ' =>
    (ordForm_isPoincareResidue_of_generatesOn hS hdim hB hdlt (hC P).1 hm0 hω hρP
      ⟨x, ⟨xP, hxP'⟩, hxU⟩).2 Q' (by rw [hQ', hxP']; exact hxU)
  have hordQ : ∀ Q' : MMP.Mori.PrimeDivisor (C Q), Q'.genericPoint = xQ →
      (Q'.ordForm ρQ : ℚ) = -(m * (BC Q).coeff Q') := fun Q' hQ' =>
    (ordForm_isPoincareResidue_of_generatesOn hS hdim hB hdlt (hC Q).1 hm0 hω hρQ
      ⟨x, ⟨xQ, hxQ'⟩, hxU⟩).2 Q' (by rw [hQ', hxQ']; exact hxU)
  obtain ⟨T, ιT, BT, F, hT, hres⟩ := exists_pointStratum_of_branch_loc hdim (hC P).1
    (isDltPair_of_isAdjunctionStep hdlt (hC P).1 P.1 (hC P).2) hPQ' (hC P).2 hxc hx.1 hx.2
    hxP' hspan hreg hu hv ha hlam hm0 hωa hρP hordP hbP
  letI := MMP.Mori.functionFieldAlgebra sS
  have hspan' : Ideal.span {v, u} = IsLocalRing.maximalIdeal (S.presheaf.stalk x) := by
    rw [Set.pair_comm]; exact hspan
  have hrange : Set.range ![v, u] = Set.range ![u, v] := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_cons,
      Matrix.range_empty, Set.union_empty, Set.union_empty, Set.singleton_union,
      Set.singleton_union, Set.pair_comm]
  have hreg' : MMP.Mori.IsRegularSystemOfParameters ![v, u] := by
    refine ⟨?_, hreg.2⟩
    rw [hrange]; exact hreg.1
  have hm : Even m := R.setting.even
  have hω' : ω = ((algebraMap _ S.functionField a *
        (algebraMap _ S.functionField v * algebraMap _ S.functionField u)⁻¹ ^ m) •
      PiTensorProduct.tprod S.functionField (fun _ : Fin m =>
        exteriorPower.ιMulti S.functionField 2 (fun i => KaehlerDifferential.D ℂ S.functionField
          (algebraMap _ S.functionField (![v, u] i)))) :
      TensorPower S.functionField m (⋀[S.functionField]^2 Ω[S.functionField⁄ℂ])) := by
    have hcomp : (fun i => KaehlerDifferential.D ℂ S.functionField
        (algebraMap _ S.functionField (![v, u] i))) =
        (fun i => KaehlerDifferential.D ℂ S.functionField
          (algebraMap _ S.functionField (![u, v] i))) ∘ Equiv.swap 0 1 := by
      funext i; fin_cases i <;> rfl
    rw [hcomp, tprod_ιMulti_comp_swap hm, mul_comm (algebraMap _ S.functionField v)]
    exact hωa
  obtain ⟨T', ιT', BT', F', hT', hres'⟩ := exists_pointStratum_of_branch_loc hdim (hC Q).1
    (isDltPair_of_isAdjunctionStep hdlt (hC Q).1 Q.1 (hC Q).2) (Ne.symm hPQ') (hC Q).2 hxc hx.2
    hx.1 hxQ' hspan' hreg' hv hu ha hlam hm0 hω' hρQ hordQ hbQ
  haveI := F.isIntegral_stratum
  haveI := F.isNormal_stratum
  haveI := F.isLocallyNoetherian_stratum
  haveI := F'.isIntegral_stratum
  haveI := F'.isNormal_stratum
  haveI := F'.isLocallyNoetherian_stratum
  letI := MMP.Mori.functionFieldAlgebra (ιT ≫ j P ≫ sS)
  letI := MMP.Mori.functionFieldAlgebra (ιT' ≫ j Q ≫ sS)
  obtain ⟨σ, hσ⟩ := exists_isCrepantBirationalMap_of_topologicalKrullDim_eq_zero
    F.isNormalVariety F'.isNormalVariety hT hT' BT BT'
  have hadm := ht P Q F F' 0 (Nat.zero_le _) (Nat.zero_le _) hT hT' σ hσ
  set e : RationalPluriForms (ιT ≫ j P ≫ sS) 0 m :=
    formPow (k := ℂ) (exteriorPower.ιMulti T.functionField 0 Fin.elim0) m with he
  set e' : RationalPluriForms (ιT' ≫ j Q ≫ sS) 0 m :=
    formPow (k := ℂ) (exteriorPower.ιMulti T'.functionField 0 Fin.elim0) m with he'
  have h1 : R.toFun P F 0 (t P) = algebraMap ℂ T.functionField (βP * lam) • e := by
    refine IsIteratedResidue.unique (R.isIteratedResidue P F 0 (t P) hT) ?_
    rw [htP]
    exact hres
  have h2 : R.toFun Q F' 0 (t Q) = algebraMap ℂ T'.functionField (βQ * lam) • e' := by
    refine IsIteratedResidue.unique (R.isIteratedResidue Q F' 0 (t Q) hT') ?_
    rw [htQ]
    exact hres'
  rw [h1, h2] at hadm
  have h5 := pluriformPullback_smul_formPow_ιMulti_zero (sT := ιT ≫ j P ≫ sS)
    (sT' := ιT' ≫ j Q ≫ sS) σ m (βQ * lam)
  have hadm' : algebraMap ℂ T.functionField (βQ * lam) • e =
      algebraMap ℂ T.functionField (βP * lam) • e := h5.symm.trans hadm
  have he0 : e ≠ 0 := formPow_ιMulti_zero_ne_zero _ m
  have h3 := smul_left_injective T.functionField he0 hadm'
  haveI : LocallyOfFiniteType (ιT ≫ j P ≫ sS) := F.isNormalVariety.1.toLocallyOfFiniteType
  have h4 := (bijective_algebraMap_of_topologicalKrullDim_eq_zero
    (sT := ιT ≫ j P ≫ sS) hT).1 h3
  exact (mul_right_cancel₀ hlam0 h4).symm

end NodeLoc

/-- **Every floor curve is chained to a horizontal one.** Let `q : X ⟶ V` map the floor of `B`
onto that of `B_V` with connected fibres, `g : V ⟶ T` a fibration over a curve with irreducible
closed fibres, and `E₀` a horizontal floor curve of `V`. Every floor curve of `X` is joined by a
chain of meeting floor curves to a floor curve of `X` dominating `T`: on `V` every floor curve is
horizontal or meets `E₀`, and preconnected parts of the floor of `V` pull back to chained families
of floor curves of `X`. -/
private theorem exists_reflTransGen_horizontal {X V T : Scheme.{0}} [IsIntegral V] [IsIntegral T]
    (q : X ⟶ V) (hqc : IsClosedMap q.base) {B : QDivisor X} {BV : QDivisor V}
    (hFimg : q.base '' floorUnion B = floorUnion BV)
    (hFfib : ∀ y ∈ floorUnion BV, _root_.IsPreconnected (q.base ⁻¹' {y} ∩ floorUnion B))
    (hfin : Finite {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0})
    (g : V ⟶ T) (hVdim : topologicalKrullDim V = 2) (hT1 : topologicalKrullDim T = 1)
    (hgc : IsClosedMap g.base) (hggen : g.base (genericPoint V) = genericPoint T)
    (hirr : ∀ t : T, IsClosed ({t} : Set T) → IsIrreducible (g.base ⁻¹' {t}))
    (E₀ : Mori.PrimeDivisor V) (hE₀ : ⌊BV.coeff E₀⌋ ≠ 0)
    (hE₀h : g.base E₀.genericPoint = genericPoint T)
    (P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0}) :
    ∃ P' : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0},
      (q ≫ g) P'.1.genericPoint = genericPoint T ∧
      Relation.ReflTransGen (fun P Q : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} =>
        ((P.1.support : Set X) ∩ Q.1.support).Nonempty) P P' := by
  classical
  have hvert := inter_nonempty_of_not_horizontal hVdim hT1 hgc hggen hirr
  have hAcl : ∀ P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0},
      IsClosed (P.1.support : Set X) := fun P => P.1.idealSheaf.support.isClosed
  have hAne : ∀ P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0},
      (P.1.support : Set X).Nonempty := fun P =>
    ⟨P.1.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support _⟩
  have hFS : IsClosed (floorUnion B) := isClosed_iUnion_of_finite hAcl
  have hsubF : floorUnion B ⊆ q.base ⁻¹' floorUnion BV :=
    fun x hx => hFimg ▸ Set.mem_image_of_mem _ hx
  have himgE : ∀ P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0},
      ∃ E : {E : Mori.PrimeDivisor V // ⌊BV.coeff E⌋ ≠ 0},
        (P.1.support : Set X) ⊆ q.base ⁻¹' (E.1.support : Set V) := by
    intro P
    have hη : q.base P.1.genericPoint ∈ floorUnion BV :=
      hsubF (Set.mem_iUnion.mpr ⟨P, MMP.Flips.primeDivisor_genericPoint_mem_support _⟩)
    obtain ⟨E, hE⟩ := Set.mem_iUnion.mp hη
    refine ⟨E, fun x hx => ?_⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
    have hsp : P.1.genericPoint ⤳ x := specializes_iff_mem_closure.mpr hx
    exact (hsp.map q.base.hom.continuous).mem_closed E.1.idealSheaf.support.isClosed hE
  have hchainS : ∀ (W : Set V), W ⊆ floorUnion BV → _root_.IsPreconnected W →
      (∀ (x : X) (P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0}), x ∈ P.1.support →
        q.base x ∈ W → (P.1.support : Set X) ⊆ q.base ⁻¹' W) →
      ∀ P P' : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0},
        (P.1.support : Set X) ⊆ q.base ⁻¹' W → (P'.1.support : Set X) ⊆ q.base ⁻¹' W →
        Relation.ReflTransGen (fun P Q : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} =>
          ((P.1.support : Set X) ∩ Q.1.support).Nonempty) P P' := by
    intro W hWF hW hsat P P' hP hP'
    have h1 := isPreconnected_preimage_inter hqc hFS hFimg hFfib hWF hW
    have h2 : q.base ⁻¹' W ∩ floorUnion B =
        ⋃ R ∈ {R : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} |
          (R.1.support : Set X) ⊆ q.base ⁻¹' W}, (R.1.support : Set X) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, floorUnion]
      constructor
      · rintro ⟨hxW, R, hxR⟩
        exact ⟨R, hsat x R hxR hxW, hxR⟩
      · rintro ⟨R, hR, hxR⟩
        exact ⟨hR hxR, R, hxR⟩
    rw [h2] at h1
    exact reflTransGen_of_isPreconnected_biUnion _ hAcl hAne h1 hP hP'
  have hsuppre : ∀ E : {E : Mori.PrimeDivisor V // ⌊BV.coeff E⌋ ≠ 0},
      _root_.IsPreconnected (E.1.support : Set V) := fun E => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isPreconnected_singleton.closure
  set rV := fun E E' : {E : Mori.PrimeDivisor V // ⌊BV.coeff E⌋ ≠ 0} =>
    ((E.1.support : Set V) ∩ E'.1.support).Nonempty
  have hrVsymm : ∀ {E E'}, rV E E' → rV E' E := fun ⟨x, h1, h2⟩ => ⟨x, h2, h1⟩
  -- the chain class of a floor curve `Q` of `V`
  let Wk : {E : Mori.PrimeDivisor V // ⌊BV.coeff E⌋ ≠ 0} → Set V := fun Q =>
    ⋃ E ∈ {E | Relation.ReflTransGen rV E Q}, (E.1.support : Set V)
  have hWkF : ∀ Q, Wk Q ⊆ floorUnion BV := fun Q x hx => by
    simp only [Wk, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx
    obtain ⟨E, -, hxE⟩ := hx
    exact Set.mem_iUnion.mpr ⟨E, hxE⟩
  have hsubWk : ∀ {E Q}, Relation.ReflTransGen rV E Q → (E.1.support : Set V) ⊆ Wk Q :=
    fun {E Q} h x hx => Set.mem_biUnion (show E ∈ {E | Relation.ReflTransGen rV E Q} from h) hx
  have hWkpre : ∀ Q, _root_.IsPreconnected (Wk Q) := fun Q => by
    refine _root_.IsPreconnected.biUnion_of_reflTransGen (fun E _ => hsuppre E) ?_
    have hto : ∀ {E}, Relation.ReflTransGen rV E Q → Relation.ReflTransGen
        (fun i j => (((i.1.support : Set V) ∩ j.1.support).Nonempty ∧
          i ∈ {E | Relation.ReflTransGen rV E Q})) E Q := by
      intro E h
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => exact Relation.ReflTransGen.refl
      | head hab hbc ih => exact Relation.ReflTransGen.head ⟨hab, hbc.head hab⟩ ih
    have hfrom : ∀ {E}, Relation.ReflTransGen rV E Q → Relation.ReflTransGen
        (fun i j => (((i.1.support : Set V) ∩ j.1.support).Nonempty ∧
          i ∈ {E | Relation.ReflTransGen rV E Q})) Q E := by
      intro E h
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => exact Relation.ReflTransGen.refl
      | @head a b hab hbc ih =>
        exact ih.tail ⟨hrVsymm hab, hbc⟩
    intro E hE E' hE'
    exact (hto hE).trans (hfrom hE')
  have hsat' : ∀ Q (P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0})
      (E : {E : Mori.PrimeDivisor V // ⌊BV.coeff E⌋ ≠ 0}), Relation.ReflTransGen rV E Q →
      (P.1.support : Set X) ⊆ q.base ⁻¹' (E.1.support : Set V) →
      (P.1.support : Set X) ⊆ q.base ⁻¹' Wk Q := fun Q P E hE hPE x hx =>
    hsubWk hE (hPE hx)
  have hWksat : ∀ Q (x : X) (P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0}),
      x ∈ P.1.support → q.base x ∈ Wk Q → (P.1.support : Set X) ⊆ q.base ⁻¹' Wk Q := by
    intro Q x P hx hxW
    obtain ⟨E', hE'⟩ := himgE P
    simp only [Wk, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hxW
    obtain ⟨E, hEQ, hxE⟩ := hxW
    exact hsat' Q P E' (Relation.ReflTransGen.head ⟨_, hE' hx, hxE⟩ hEQ) hE'
  -- the floor curve of `V` under `P`, and a horizontal one chained to it
  obtain ⟨E', hE'⟩ := himgE P
  obtain ⟨Q, hQh, hEQ⟩ : ∃ Q : {E : Mori.PrimeDivisor V // ⌊BV.coeff E⌋ ≠ 0},
      g.base Q.1.genericPoint = genericPoint T ∧ Relation.ReflTransGen rV E' Q := by
    by_cases hh : g.base E'.1.genericPoint = genericPoint T
    · exact ⟨E', hh, Relation.ReflTransGen.refl⟩
    · exact ⟨⟨E₀, hE₀⟩, hE₀h, Relation.ReflTransGen.single (hvert E'.1 hh E₀ hE₀h)⟩
  obtain ⟨PQ, hPQ⟩ := exists_image_eq_of_image_floor q hqc hFimg Q.1 Q.2
  have hηQ : q PQ.1.genericPoint = Q.1.genericPoint := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← hqc.closure_image_eq_of_continuous q.base.hom.continuous,
      Set.image_singleton] at hPQ
    exact (specializes_iff_closure_subset.mpr hPQ.ge).antisymm
      (specializes_iff_closure_subset.mpr hPQ.le) |>.eq
  refine ⟨PQ, ?_, hchainS _ (hWkF Q) (hWkpre Q) (hWksat Q) P PQ (hsat' Q P E' hEQ hE')
    fun x hx => hsubWk Relation.ReflTransGen.refl (hPQ ▸ Set.mem_image_of_mem _ hx)⟩
  change g (q PQ.1.genericPoint) = _
  rw [hηQ]; exact hQh

end HorizD

section HorizE

open MMP MMP.Fourfold MMP.Flips
open MMP.Mori hiding IsPair
open FloorAdjunction

/-- **Regularity descends along a dominant map of curves.** If `f : C ⟶ T` is dominant, `T`
normal, `f(y)` a point of codimension one and `f^*ψ` is regular at `y`, then `ψ` is regular at
`f(y)`, and its germ maps to that of `f^*ψ`: in the valuation ring `𝒪_{T,f(y)}`, otherwise
`ψ⁻¹` would be a non-unit whose image `(f^*ψ)⁻¹` is a unit. -/
private theorem exists_stalk_eq_of_functionFieldMap_eq {C T : Scheme.{0}} [IsIntegral C] [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] (f : C ⟶ T) [IsDominant f] (y : C)
    (hy1 : Order.coheight (f y) = 1) {ψ : T.functionField} {b : C.presheaf.stalk y}
    (hb : functionFieldMap f ψ = algebraMap _ C.functionField b) :
    ∃ φ : T.presheaf.stalk (f y), algebraMap _ T.functionField φ = ψ ∧
      (f.stalkMap y).hom φ = b := by
  classical
  have hcompat : ∀ φ : T.presheaf.stalk (f y), functionFieldMap f (algebraMap _ _ φ) =
      algebraMap _ C.functionField ((f.stalkMap y).hom φ) :=
    fun φ => MMP.Mori.functionFieldMap_algebraMap_stalk f y φ
  have hinj : Function.Injective (algebraMap (C.presheaf.stalk y) C.functionField) :=
    IsFractionRing.injective _ _
  let P : Mori.PrimeDivisor T := AlgebraicGeometry.PrimeDivisor.ofCoheightOne (f y) hy1
  have hP : P.genericPoint = f y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hy1
  have hV : ValuationRing (T.presheaf.stalk (f y)) := by
    rw [← hP]
    have := P.isDiscreteValuationRing_localRing
    exact inferInstanceAs (ValuationRing P.localRing)
  have key : ∀ φ : T.presheaf.stalk (f y), algebraMap _ T.functionField φ = ψ →
      ∃ φ : T.presheaf.stalk (f y), algebraMap _ T.functionField φ = ψ ∧
        (f.stalkMap y).hom φ = b := fun φ hφ =>
    ⟨φ, hφ, hinj (by rw [← hcompat, hφ, hb])⟩
  by_cases hψ : ψ = 0
  · exact key 0 (by rw [map_zero, hψ])
  rcases ValuationRing.isInteger_or_isInteger (T.presheaf.stalk (f y)) ψ with ⟨φ, hφ⟩ | ⟨φ', hφ'⟩
  · exact key φ hφ
  · by_cases hu : IsUnit φ'
    · refine key (hu.unit⁻¹ : (T.presheaf.stalk (f y))ˣ) ?_
      have : algebraMap _ T.functionField φ' * algebraMap _ T.functionField
          ((hu.unit⁻¹ : (T.presheaf.stalk (f y))ˣ) : T.presheaf.stalk (f y)) = 1 := by
        rw [← map_mul]; simp
      rw [hφ'] at this
      exact (eq_inv_of_mul_eq_one_right this).trans (inv_inv ψ)
    · exfalso
      have h1 : functionFieldMap f ψ⁻¹ * functionFieldMap f ψ = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hψ, map_one]
      rw [← hφ', hcompat, hb, ← map_mul] at h1
      have h2 : (f.stalkMap y).hom φ' * b = 1 := hinj (by rw [h1, map_one])
      exact hu (isUnit_of_map_unit (f.stalkMap y).hom φ' (IsUnit.of_mul_eq_one _ h2))

/-- **Residues of a pulled-back regular function along a vertical curve.** If `j : C ⟶ X` maps
the generic point of `C` to a point over `t`, and `φ ∈ 𝒪_{T,t}` has value `β` at `t`, then
multiplying a form by `h'^*φ` multiplies its residue along `C` by the constant `β`. -/
private theorem isPoincareResidue_functionFieldMap_smul_of_vertical {X T C : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsIntegral T] [IsIntegral C] {sX : X ⟶ Spec (.of ℂ)}
    {sT : T ⟶ Spec (.of ℂ)} (h' : X ⟶ T) [IsDominant h'] (hsT : h' ≫ sT = sX) {j : C ⟶ X}
    {n M : ℕ} {Ω : RationalPluriForms sX (n + 1) M} {ρ : RationalPluriForms (j ≫ sX) n M}
    (hρ : IsPoincareResidue sX j n M Ω ρ) {t : T} (ht : h' (j (genericPoint C)) = t)
    (φ : T.presheaf.stalk t) {β : ℂ}
    (hφ : φ - (letI := MMP.Mori.stalkAlgebra sT t; algebraMap ℂ _ β) ∈
      IsLocalRing.maximalIdeal (T.presheaf.stalk t)) :
    IsPoincareResidue sX j n M (functionFieldMap h' (algebraMap _ T.functionField φ) • Ω)
      (letI := MMP.Mori.functionFieldAlgebra (j ≫ sX); algebraMap ℂ C.functionField β • ρ) := by
  subst ht hsT
  set germ := (h'.stalkMap (j (genericPoint C))).hom φ with hgerm
  have h1 : algebraMap _ X.functionField germ =
      functionFieldMap h' (algebraMap _ T.functionField φ) :=
    (MMP.Mori.functionFieldMap_algebraMap_stalk h' (j (genericPoint C)) φ).symm
  have h2 : (j.stalkMap (genericPoint C)).hom germ =
      (letI := MMP.Mori.functionFieldAlgebra (j ≫ h' ≫ sT); algebraMap ℂ C.functionField β) := by
    set L := (j.stalkMap (genericPoint C)).hom.comp (h'.stalkMap (j (genericPoint C))).hom
    have hL := map_eq_zero_of_mem_maximalIdeal L hφ
    rw [map_sub, sub_eq_zero] at hL
    change L φ = _
    rw [hL]
    change (j.stalkMap (genericPoint C)).hom ((h'.stalkMap (j (genericPoint C))).hom
      (letI := MMP.Mori.stalkAlgebra sT (h' (j (genericPoint C))); algebraMap ℂ _ β)) = _
    rw [stalkMap_algebraMap' sT h', stalkMap_algebraMap' (h' ≫ sT) j]
  have := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hρ germ
  rw [h1, h2] at this
  exact this

/-- **Residues of a local generator exist.** A generator `τ` of `𝒪(M(K + B))` on `W` has a
nonzero Poincaré residue along every floor curve meeting `W`, of order `-M · coeff B_C` at the
points over `W`. -/
private theorem exists_residue_of_generatesOn {X C : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hX : Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 2) {B : QDivisor X}
    (hB : Fourfold.IsPair sX B) (hdlt : MMP.Intersection.IsDltPair sX B)
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] {j : C ⟶ X} {BC : QDivisor C}
    (hj : IsAdjunctionStep sX B j BC) {M : ℕ} (hM : 0 < M) {W : X.Opens}
    {τ : RationalPluriForms sX 2 M} (hτ : GeneratesOn B M W τ)
    (hW : (Set.range j.base ∩ W).Nonempty) :
    ∃ ρ : RationalPluriForms (j ≫ sX) 1 M, IsPoincareResidue sX j 1 M τ ρ ∧ ρ ≠ 0 ∧
      ∀ Q : Mori.PrimeDivisor C, j Q.genericPoint ∈ W →
        (Q.ordForm ρ : ℚ) = -(M * BC.coeff Q) := by
  classical
  have hXn : IsNormalVariety ℂ sX := hB.isPair.1
  obtain ⟨hT, P, hP1, hrange, hci, -⟩ := id hj
  have hBP : B.coeff P = 1 := le_antisymm (hdlt.2.1 P) hP1
  have hjη : j (genericPoint C) = P.genericPoint :=
    MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hrange
  have hPW : (P.support ∩ (W : Set X)).Nonempty := by
    obtain ⟨y, ⟨c, rfl⟩, hy⟩ := hW
    exact ⟨j c, hrange ▸ ⟨c, rfl⟩, hy⟩
  have hord : P.ordForm τ = -(M : ℤ) := by
    have h := hτ.2 P hPW
    rw [hBP] at h
    have : ((P.ordForm τ : ℤ) : ℚ) = -(M : ℚ) := by linarith
    exact_mod_cast this
  obtain ⟨ρ, hρ⟩ := exists_isPoincareResidue_of_surface hXn hdim hj τ
    fun P' hP' _ => by
      have : P' = P := MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support
        (hP' ▸ hjη ▸ MMP.Flips.primeDivisor_genericPoint_mem_support P)
      rw [this, hord]
  obtain ⟨hρ0, hρord⟩ := ordForm_isPoincareResidue_of_generatesOn hX hdim hB hdlt hj hM hτ hρ hW
  exact ⟨ρ, hρ, hρ0, hρord⟩

open IsLocalRing in
/-- **Residues along the vertical floor curves.** Let `h' : X ⟶ T` be a fibration over a normal
curve with local frames `h'^*e · Ω` of `𝒪(M(K + B))`, `t'` an admissible system on the floor
curves, and `ψ ∈ k(T)` such that `h'^*ψ · Ω` has residue `t'_P` along every horizontal floor
curve. If every floor curve is chained to a horizontal one, `h'^*ψ · Ω` has residue `t'_P` along
every floor curve. Along a vertical curve over `t` the residue of the frame generates everywhere,
so `t'_P` is a constant multiple of it; node matching along the chain identifies the constant
with the value at `t` of `ψ/e`, which is regular at `t` because `t'` is regular on the horizontal
curve the chain reaches. -/
private theorem isPoincareResidue_of_reflTransGen
    {X T : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sT : T ⟶ Spec (.of ℂ)} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [LocallyOfFiniteType sT] (h' : X ⟶ T) [IsDominant h']
    (hX : Mori.IsProjectiveVariety ℂ (h' ≫ sT)) (hdim : topologicalKrullDim X = 2)
    {B : QDivisor X} (hB : Fourfold.IsPair (h' ≫ sT) B)
    (hdlt : MMP.Intersection.IsDltPair (h' ≫ sT) B)
    (C : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} → Scheme.{0})
    [∀ P, IsIntegral (C P)] [∀ P, IsLocallyNoetherian (C P)] [∀ P, IsNormal (C P)]
    (j : ∀ P, C P ⟶ X) (BC : ∀ P, QDivisor (C P))
    (hC : ∀ P, IsAdjunctionStep (h' ≫ sT) B (j P) (BC P) ∧
      Set.range (j P).base = (P.1.support : Set X))
    (hT1 : topologicalKrullDim T = 1) (hh'c : IsClosedMap h'.base) {M : ℕ} (hM0 : 0 < M)
    (RM : ResidueRestriction (fun P => j P ≫ h' ≫ sT) BC 1 M) {t' : ∀ P, _}
    (ht' : t' ∈ admissibleSections RM) {Ω : RationalPluriForms (h' ≫ sT) 2 M}
    (hfr : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ e : T.functionField, e ≠ 0 ∧
      GeneratesOn B M (h' ⁻¹ᵁ U) (functionFieldMap h' e • Ω))
    (ψ : T.functionField)
    (hhor : ∀ P, h' P.1.genericPoint = genericPoint T →
      IsPoincareResidue (h' ≫ sT) (j P) 1 M (functionFieldMap h' ψ • Ω)
        (t' P : RationalPluriForms (j P ≫ h' ≫ sT) 1 M))
    (hchain : ∀ P, ∃ P', h' P'.1.genericPoint = genericPoint T ∧
      Relation.ReflTransGen (fun P Q : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} =>
        ((P.1.support : Set X) ∩ Q.1.support).Nonempty) P P') (P) :
    IsPoincareResidue (h' ≫ sT) (j P) 1 M (functionFieldMap h' ψ • Ω)
      (t' P : RationalPluriForms (j P ≫ h' ≫ sT) 1 M) := by
  classical
  have hXn : IsNormalVariety ℂ (h' ≫ sT) := hB.isPair.1
  haveI : LocallyOfFiniteType (h' ≫ sT) := hXn.1.toLocallyOfFiniteType
  haveI hci : ∀ P, IsClosedImmersion (j P) := fun P => (hC P).1.2.choose_spec.2.2.1
  have hjη : ∀ P, j P (genericPoint (C P)) = P.1.genericPoint := fun P =>
    MMP.CyclicChartDifferent.Aux.map_genericPoint_eq (j P) P.1 (hC P).2
  haveI : ∀ P, CompactSpace (C P) := fun P => (j P).isClosedEmbedding.compactSpace
  haveI : ∀ P, LocallyOfFiniteType (j P ≫ h' ≫ sT) := fun P =>
    (hC P).1.1.1.toLocallyOfFiniteType
  haveI : IsProper (h' ≫ sT) := isProper_of_isProjectiveMorphism _ hX.isProjective
  haveI hprop : ∀ P, IsProper (j P ≫ h' ≫ sT) := fun P => inferInstance
  have hCdim : ∀ P, topologicalKrullDim (C P) = 1 := fun P => by
    have := topologicalKrullDim_eq_one_of_isAdjunctionStep hdim (hC P).1
    exact_mod_cast this
  have hCdim1 : ∀ P, topologicalKrullDim (C P) = ((1 : ℕ) : WithBot ℕ∞) := fun P => by
    rw [hCdim P]; rfl
  by_cases hPh : h' P.1.genericPoint = genericPoint T
  · exact hhor P hPh
  -- vertical floor curves lie over closed points
  have hvert : ∀ R : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0},
      h' R.1.genericPoint ≠ genericPoint T → ∀ x ∈ R.1.support, h' x = h' R.1.genericPoint := by
    intro R hR x hx
    have hcl := isClosed_singleton_of_ne_genericPoint hT1 hR
    have hsp : R.1.genericPoint ⤳ x := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
      exact specializes_iff_mem_closure.mpr hx
    have h2 := hsp.map h'.base.hom.continuous
    exact (Set.mem_singleton_iff.mp
      (h2.mem_closed hcl (Set.mem_singleton _)))
  set t := h' P.1.genericPoint with htdef
  have htc : IsClosed ({t} : Set T) := isClosed_singleton_of_ne_genericPoint hT1 hPh
  have ht1 : Order.coheight t = 1 := MMP.Fourfold.coheight_eq_one_of_ne_genericPoint hT1 hPh
  obtain ⟨U, hU, e, he, hτ⟩ := hfr t
  set τ := functionFieldMap h' e • Ω with hτdef
  set ψe := ψ * e⁻¹ with hψedef
  have hψΩ : functionFieldMap h' ψ • Ω = functionFieldMap h' ψe • τ := by
    rw [hτdef, smul_smul, ← map_mul, hψedef, mul_assoc, inv_mul_cancel₀ he, mul_one]
  -- residues of the frame
  have hres : ∀ R : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0}, (∃ x ∈ R.1.support, h' x ∈ U) →
      ∃ ρ : RationalPluriForms (j R ≫ h' ≫ sT) 1 M, IsPoincareResidue (h' ≫ sT) (j R) 1 M τ ρ ∧
        ρ ≠ 0 ∧ ∀ Q : Mori.PrimeDivisor (C R), j R Q.genericPoint ∈ h' ⁻¹ᵁ U →
          (Q.ordForm ρ : ℚ) = -(M * (BC R).coeff Q) := by
    rintro R ⟨x, hx, hxU⟩
    exact exists_residue_of_generatesOn hX hdim hB hdlt (hC R).1 hM0 hτ
      ⟨x, (hC R).2 ▸ hx, hxU⟩
  -- the coefficient along a horizontal curve
  have hhcoef : ∀ R : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0},
      h' R.1.genericPoint = genericPoint T → ∀ ρ, IsPoincareResidue (h' ≫ sT) (j R) 1 M τ ρ →
      ∃ _ : IsDominant (j R ≫ h'),
        (t' R : RationalPluriForms (j R ≫ h' ≫ sT) 1 M) = functionFieldMap (j R ≫ h') ψe • ρ := by
    intro R hR ρ hρ
    haveI : IsDominant (j R ≫ h') := isDominant_of_map_genericPoint _ (by
      change h' (j R (genericPoint (C R))) = _; rw [hjη, hR])
    refine ⟨inferInstance, ?_⟩
    have h1 := isPoincareResidue_functionFieldMap_smul h' hρ ψe
    rw [← hψΩ] at h1
    exact IsPoincareResidue.unique (hC R).1 (hhor R hR) h1
  -- a closed point in the intersection of two meeting floor curves
  have hinter : ∀ R R' : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0},
      ((R.1.support : Set X) ∩ R'.1.support).Nonempty →
      ∃ x, IsClosed ({x} : Set X) ∧ x ∈ R.1.support ∧ x ∈ R'.1.support := by
    intro R R' h
    obtain ⟨x, hx, hxc⟩ := (R.1.idealSheaf.support.isClosed.inter
      R'.1.idealSheaf.support.isClosed).exists_closed_singleton h
    exact ⟨x, hxc, hx.1, hx.2⟩
  -- Stage 1: a vertical curve over `t` meets a horizontal one
  have hstage1 : ∀ R R' : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0},
      Relation.ReflTransGen (fun P Q : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} =>
        ((P.1.support : Set X) ∩ Q.1.support).Nonempty) R R' →
      h' R'.1.genericPoint = genericPoint T → h' R.1.genericPoint = t →
      ∃ (Rh : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0}) (x : X), IsClosed ({x} : Set X) ∧
        x ∈ Rh.1.support ∧ h' x = t ∧ h' Rh.1.genericPoint = genericPoint T := by
    intro R R' hRR' hR' hRt
    induction hRR' using Relation.ReflTransGen.head_induction_on with
    | refl => exact absurd (hRt.symm.trans hR') hPh
    | @head R R₂ hRR₂ _ ih =>
      obtain ⟨x, hxc, hxR, hxR₂⟩ := hinter R R₂ hRR₂
      have hxt : h' x = t := by
        rw [hvert R (by rw [hRt]; exact hPh) x hxR, hRt]
      by_cases hR₂h : h' R₂.1.genericPoint = genericPoint T
      · exact ⟨R₂, x, hxc, hxR₂, hxt, hR₂h⟩
      · exact ih (by rw [← hvert R₂ hR₂h x hxR₂, hxt])
  obtain ⟨P', hP'h, hPP'⟩ := hchain P
  obtain ⟨Rh, x, hxc, hxRh, hxt, hRhh⟩ := hstage1 P P' hPP' hP'h rfl
  -- `ψ / e` is regular at `t`
  obtain ⟨φt, hφt⟩ : ∃ φ : T.presheaf.stalk t, algebraMap _ T.functionField φ = ψe := by
    by_cases hψe : ψe = 0
    · exact ⟨0, by rw [map_zero, hψe]⟩
    obtain ⟨ρh, hρh, hρh0, hρhord⟩ := hres Rh ⟨x, hxRh, by rw [hxt]; exact hU⟩
    obtain ⟨hdomh, hth⟩ := hhcoef Rh hRhh ρh hρh
    obtain ⟨xh, hxh⟩ : x ∈ Set.range (j Rh).base := (hC Rh).2 ▸ hxRh
    have hxhη : xh ≠ genericPoint (C Rh) := by
      rintro rfl
      have h1 : h' x = genericPoint T := by rw [← hxh, hjη]; exact hRhh
      exact hPh (hxt.symm.trans h1)
    have hxh1 : Order.coheight xh = 1 := MMP.Fourfold.coheight_eq_one_of_ne_genericPoint
      (hCdim1 Rh) hxhη
    let Qx : Mori.PrimeDivisor (C Rh) := AlgebraicGeometry.PrimeDivisor.ofCoheightOne xh hxh1
    have hQx : Qx.genericPoint = xh := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hxh1
    have hf0 : functionFieldMap (j Rh ≫ h') ψe ≠ 0 := (map_ne_zero _).mpr hψe
    obtain ⟨b, hb⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg xh
      hf0 fun Γ hΓ => by
        have hΓx : Γ.genericPoint = xh := by
          have hsp : Γ.genericPoint ⤳ xh := by
            rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
            exact hΓ
          exact MMP.ProgramBaseChange.eq_of_specializes_of_coheight_eq_one hsp
            Γ.coheight_genericPoint hxh1
        have hmem := (t' Rh).2
        have ht'0 : (t' Rh : RationalPluriForms (j Rh ≫ h' ≫ sT) 1 M) ≠ 0 := by
          rw [hth]; exact smul_ne_zero hf0 hρh0
        have h1 := (MMP.Mori.mem_pluricanonicalSections.mp hmem).2 Γ
          ⟨Γ.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support _, trivial⟩ ht'0
        rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, hth,
          Γ.ordForm_smul_of_topologicalKrullDim_eq (hCdim1 Rh) hf0 hρh0] at h1
        have h2 := hρhord Γ (by
          change h' (j Rh Γ.genericPoint) ∈ U
          rw [hΓx, hxh, hxt]; exact hU)
        have h3 := Int.floor_le (((M : ℕ) : ℤ) • (BC Rh).coeff Γ)
        rw [zsmul_eq_mul] at h3
        have : (0 : ℚ) ≤ ((C Rh).ord (functionFieldMap (j Rh ≫ h') ψe) Γ.genericPoint : ℚ) := by
          have h1' : (0 : ℚ) ≤ (((C Rh).ord (functionFieldMap (j Rh ≫ h') ψe) Γ.genericPoint +
              Γ.ordForm ρh + ⌊((M : ℕ) : ℤ) • (BC Rh).coeff Γ⌋ : ℤ) : ℚ) := by exact_mod_cast h1
          rw [zsmul_eq_mul] at h1'
          push_cast at h1' h2 h3 ⊢
          linarith
        exact_mod_cast this
    have hy1 : Order.coheight ((j Rh ≫ h') xh) = 1 := by
      change Order.coheight (h' (j Rh xh)) = 1
      rw [hxh, hxt]; exact ht1
    obtain ⟨φ, hφ, -⟩ := exists_stalk_eq_of_functionFieldMap_eq (j Rh ≫ h') xh hy1 hb.symm
    have hφt : (j Rh ≫ h') xh = t := by change h' (j Rh xh) = t; rw [hxh, hxt]
    have key : ∀ {y : T} (_ : y = t) (φ : T.presheaf.stalk y),
        algebraMap _ T.functionField φ = ψe →
        ∃ φ' : T.presheaf.stalk t, algebraMap _ T.functionField φ' = ψe := by
      intro y hy φ h
      subst hy
      exact ⟨φ, h⟩
    exact key hφt φ hφ
  -- the value of `ψ / e` at `t`
  obtain ⟨β, hβ⟩ := exists_sub_algebraMap_mem_maximalIdeal sT t htc φt
  have hφy : ∀ {y : T} (_ : y = t), ∃ φ' : T.presheaf.stalk y,
      algebraMap _ T.functionField φ' = ψe ∧
      φ' - (letI := MMP.Mori.stalkAlgebra sT y; algebraMap ℂ _ β) ∈ maximalIdeal _ := by
    intro y hy
    subst hy
    exact ⟨φt, hφt, hβ⟩
  -- the coefficient of a horizontal curve at a point over `t`
  have hbhor : ∀ (R : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0}) [IsDominant (j R ≫ h')]
      (xR : C R), h' (j R xR) = t → ∃ b : (C R).presheaf.stalk xR,
        algebraMap _ (C R).functionField b = functionFieldMap (j R ≫ h') ψe ∧
        b - (letI := MMP.Mori.stalkAlgebra (j R ≫ h' ≫ sT) xR; algebraMap ℂ _ β) ∈
          maximalIdeal _ := by
    intro R _ xR hxR
    obtain ⟨φ', hφ', hφ'β⟩ := hφy hxR
    refine ⟨(j R).stalkMap xR |>.hom ((h'.stalkMap (j R xR)).hom φ'), ?_, ?_⟩
    · have h1 : functionFieldMap (j R ≫ h')
          (algebraMap (T.presheaf.stalk (h' (j R xR))) T.functionField φ') =
          algebraMap _ (C R).functionField (((j R ≫ h').stalkMap xR).hom φ') :=
        MMP.Mori.functionFieldMap_algebraMap_stalk (j R ≫ h') xR φ'
      rw [hφ'] at h1
      rw [h1, Scheme.Hom.stalkMap_comp]
      rfl
    · have h1 : ((j R).stalkMap xR).hom ((h'.stalkMap (j R xR)).hom
          (φ' - (letI := MMP.Mori.stalkAlgebra sT (h' (j R xR)); algebraMap ℂ _ β))) ∈
          maximalIdeal _ := by
        set L := ((j R).stalkMap xR).hom.comp (h'.stalkMap (j R xR)).hom
        change L _ ∈ _
        by_contra hc
        exact ((IsLocalRing.mem_maximalIdeal _).mp hφ'β)
          (isUnit_of_map_unit L _ ((IsLocalRing.notMem_maximalIdeal).mp hc))
      rwa [map_sub, map_sub, stalkMap_algebraMap' sT h', stalkMap_algebraMap' (h' ≫ sT) (j R)]
        at h1
  -- the coefficient of a vertical curve
  have hbconst : ∀ (R : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0}) (xR : C R) (c : ℂ)
      (ρ : RationalPluriForms (j R ≫ h' ≫ sT) 1 M),
      (letI := MMP.Mori.stalkAlgebra (j R ≫ h' ≫ sT) xR;
        algebraMap ℂ ((C R).presheaf.stalk xR) c) -
          (letI := MMP.Mori.stalkAlgebra (j R ≫ h' ≫ sT) xR; algebraMap ℂ _ c) ∈
        maximalIdeal ((C R).presheaf.stalk xR) ∧
      (c • ρ = algebraMap _ (C R).functionField
        (letI := MMP.Mori.stalkAlgebra (j R ≫ h' ≫ sT) xR;
          algebraMap ℂ ((C R).presheaf.stalk xR) c) • ρ) := by
    intro R xR c ρ
    letI := MMP.Mori.stalkAlgebra (j R ≫ h' ≫ sT) xR
    letI := MMP.Mori.functionFieldAlgebra (j R ≫ h' ≫ sT)
    haveI := MMP.Mori.isScalarTower_stalk_functionField (j R ≫ h' ≫ sT) xR
    refine ⟨by rw [sub_self]; exact zero_mem _, ?_⟩
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  -- Stage 3: along the vertical curves over `t`, `t'` is `β` times the residue of the frame
  have hstage3 : ∀ R R' : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0},
      Relation.ReflTransGen (fun P Q : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} =>
        ((P.1.support : Set X) ∩ Q.1.support).Nonempty) R R' →
      h' R'.1.genericPoint = genericPoint T → h' R.1.genericPoint = t →
      ∀ ρ, IsPoincareResidue (h' ≫ sT) (j R) 1 M τ ρ →
        (t' R : RationalPluriForms (j R ≫ h' ≫ sT) 1 M) = β • ρ := by
    intro R R' hRR' hR' hRt
    induction hRR' using Relation.ReflTransGen.head_induction_on with
    | refl => exact absurd (hRt.symm.trans hR') hPh
    | @head R R₂ hRR₂ hR₂R' ih =>
      intro ρ hρ
      by_cases hRR : R = R₂
      · subst hRR
        exact ih hRt ρ hρ
      have hRv : h' R.1.genericPoint ≠ genericPoint T := by rw [hRt]; exact hPh
      have hRU : ∀ x ∈ R.1.support, h' x ∈ U := fun x hx => by
        rw [hvert R hRv x hx, hRt]; exact hU
      obtain ⟨ρ₀, hρ₀, hρ₀0, hρ₀ord⟩ := hres R ⟨R.1.genericPoint,
        MMP.Flips.primeDivisor_genericPoint_mem_support _,
        hRU _ (MMP.Flips.primeDivisor_genericPoint_mem_support _)⟩
      obtain rfl := IsPoincareResidue.unique (hC R).1 hρ hρ₀
      obtain ⟨c, hc⟩ := exists_eq_smul_of_mem_logPluricanonicalSections
        (hCdim1 R) hρ₀0 (fun Q => hρ₀ord Q (hRU _ ((hC R).2 ▸ ⟨Q.genericPoint, rfl⟩))) (t' R).2
      obtain ⟨x, hxc, hxR, hxR₂⟩ := hinter R R₂ hRR₂
      have hxt : h' x = t := by rw [hvert R hRv x hxR, hRt]
      have hxU : x ∈ h' ⁻¹ᵁ U := show h' x ∈ U by rw [hxt]; exact hU
      obtain ⟨xR, hxR'⟩ : x ∈ Set.range (j R).base := (hC R).2 ▸ hxR
      obtain ⟨xR₂, hxR₂'⟩ : x ∈ Set.range (j R₂).base := (hC R₂).2 ▸ hxR₂
      obtain ⟨ρ₂, hρ₂, -, -⟩ := hres R₂ ⟨x, hxR₂, hxU⟩
      obtain ⟨hbR, htR⟩ := hbconst R xR c ρ
      have hcalg := hc.trans htR
      have hcβ : c = β := by
        by_cases hR₂h : h' R₂.1.genericPoint = genericPoint T
        · obtain ⟨hdom₂, ht₂⟩ := hhcoef R₂ hR₂h ρ₂ hρ₂
          obtain ⟨b₂, hb₂, hb₂β⟩ := hbhor R₂ xR₂ (by rw [hxR₂', hxt])
          rw [← hb₂] at ht₂
          exact value_eq_of_mem_inter hX hdim hB hdlt C j BC hC hM0 RM ht' hRR hxc hxR hxR₂ hxU
            hτ hρ hρ₂ hxR' hxR₂' hbR hb₂β hcalg ht₂
        · have hR₂t : h' R₂.1.genericPoint = t := by
            rw [← hvert R₂ hR₂h x hxR₂, hxt]
          have ht₂ := ih hR₂t ρ₂ hρ₂
          obtain ⟨hb₂, ht₂'⟩ := hbconst R₂ xR₂ β ρ₂
          rw [ht₂'] at ht₂
          exact value_eq_of_mem_inter hX hdim hB hdlt C j BC hC hM0 RM ht' hRR hxc hxR hxR₂ hxU
            hτ hρ hρ₂ hxR' hxR₂' hbR hb₂ hcalg ht₂
      rw [hc, hcβ]
  -- Stage 4: the residue along `P`
  have hPU : ∀ x ∈ P.1.support, h' x ∈ U := fun x hx => by
    rw [hvert P hPh x hx]; exact hU
  obtain ⟨ρP, hρP, -, -⟩ := hres P ⟨P.1.genericPoint,
    MMP.Flips.primeDivisor_genericPoint_mem_support _,
    hPU _ (MMP.Flips.primeDivisor_genericPoint_mem_support _)⟩
  have h1 := hstage3 P P' hPP' hP'h rfl ρP hρP
  have h2 := isPoincareResidue_functionFieldMap_smul_of_vertical h' rfl hρP
    (t := t) (by rw [hjη]) φt hβ
  rw [hφt, ← hψΩ] at h2
  rw [h1]
  letI := MMP.Mori.functionFieldAlgebra (j P ≫ h' ≫ sT)
  have h3 : (β • ρP : RationalPluriForms (j P ≫ h' ≫ sT) 1 M) =
      algebraMap ℂ (C P).functionField β • ρP := rfl
  rw [h3]
  exact h2

end HorizE

section Horiz

open MMP MMP.Fourfold MMP.Flips
open MMP.Mori hiding IsPair
open FloorAdjunction

/-- Powers of log pluricanonical sections: if `c ω^{⊗m} ∈ H⁰(m(K + B))` then
`c^a ω^{⊗am} ∈ H⁰(am(K + B))` for `a > 0`. -/
private theorem pow_mem_logPluricanonicalSections {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {BY : QDivisor Y} {n m : ℕ}
    (ω : letI := functionFieldAlgebra sY; ⋀[Y.functionField]^n Ω[Y.functionField⁄ℂ])
    (c : Y.functionField)
    (h : letI := functionFieldAlgebra sY
      (c • (formPow ω m : RationalPluriForms sY n m)) ∈ logPluricanonicalSections sY n m BY) :
    letI := functionFieldAlgebra sY
    ∀ a, 0 < a → (c ^ a • (formPow ω (a * m) : RationalPluriForms sY n ((a * m : ℕ) : ℤ))) ∈
      logPluricanonicalSections sY n (a * m) BY := by
  letI := functionFieldAlgebra sY
  intro a ha
  suffices H : ∀ N : ℕ, N = a * m → (c ^ a • (formPow ω N : RationalPluriForms sY n N)) ∈
      logPluricanonicalSections sY n N BY from H _ rfl
  induction a, ha using Nat.le_induction with
  | base =>
    intro N hN
    rw [Nat.succ_eq_add_one, zero_add, one_mul] at hN
    subst hN
    simpa only [pow_one] using h
  | succ a ha ih =>
    intro N hN
    have hmul := mul_mem_logPluricanonicalSections (ih _ rfl) h
    rw [RationalPluriForms.mul_smul_formPow, ← pow_succ] at hmul
    rw [Nat.succ_mul] at hN
    subst hN
    exact hmul

/-- **Powers of an admissible system.** For an admissible system `t` of degree `m` on a
collection of dlt curves and `a > 0`, the system `t^a` of degree `am` is admissible for a residue
restriction structure in degree `am`: iterated residues of powers are powers of iterated
residues, and pluriform pull-back commutes with powers. -/
private theorem exists_pow_admissibleSections {J : Type u} {C : J → Scheme.{0}}
    [∀ j, IsIntegral (C j)] [∀ j, IsLocallyNoetherian (C j)] [∀ j, IsNormal (C j)]
    {sC : ∀ j, C j ⟶ Spec (.of ℂ)} {BC : ∀ j, QDivisor (C j)} {m : ℕ}
    (RS : ResidueRestriction sC BC 1 m) {t : ∀ j, logPluricanonicalSections (sC j) 1 m (BC j)}
    (ht : t ∈ admissibleSections RS) {a : ℕ} (ha : 0 < a) :
    ∃ (RM : ResidueRestriction sC BC 1 (a * m))
      (t' : ∀ j, logPluricanonicalSections (sC j) 1 (a * m) (BC j)),
      t' ∈ admissibleSections RM ∧ ∀ j,
        letI := functionFieldAlgebra (sC j)
        ∀ (ω : ⋀[(C j).functionField]^1 Ω[(C j).functionField⁄ℂ]) (c : (C j).functionField),
          (t j : RationalPluriForms (sC j) 1 m) = c • (formPow ω m : RationalPluriForms (sC j) 1 m) →
          (t' j : RationalPluriForms (sC j) 1 ((a * m : ℕ) : ℤ)) =
            c ^ a • (formPow ω (a * m) : RationalPluriForms (sC j) 1 ((a * m : ℕ) : ℤ)) := by
  classical
  have hset := RS.setting
  have hset' : IsStratifiedSectionSetting sC BC 1 (a * m) :=
    { finite := hset.finite
      isProjectiveVariety := hset.isProjectiveVariety
      isPair := hset.isPair
      isDltPair := hset.isDltPair
      topologicalKrullDim_eq := hset.topologicalKrullDim_eq
      even := hset.even.mul_left a
      pos := Nat.mul_pos ha hset.pos
      isCartierDivisor := fun j S ι BS F => by
        haveI := F.isIntegral_stratum
        haveI := F.isNormal_stratum
        haveI := F.isLocallyNoetherian_stratum
        obtain ⟨d, K, hK, D₀, hD₀, hD₀c⟩ := hset.isCartierDivisor j F
        refine ⟨d, K, hK, (a : ℤ) • D₀, ?_, hD₀c.zsmul _⟩
        rw [map_zsmul, hD₀, smul_smul]
        push_cast
        rfl }
  obtain ⟨RM⟩ := nonempty_residueRestriction_curve hset'
  have hb : ∀ j, letI := functionFieldAlgebra (sC j)
      Nonempty (Module.Basis Unit (C j).functionField
        (⋀[(C j).functionField]^1 Ω[(C j).functionField⁄ℂ])) := fun j => by
    haveI := (hset.isProjectiveVariety j).toLocallyOfFiniteType
    exact exists_basis_topForms (sX := sC j) (hset.topologicalKrullDim_eq j)
  let b := fun j => (hb j).some
  let c : ∀ j, (C j).functionField := fun j =>
    letI := functionFieldAlgebra (sC j)
    (ZTensorPower.basis (b j) m).repr (t j : RationalPluriForms (sC j) 1 m) ()
  have hc : ∀ j, letI := functionFieldAlgebra (sC j)
      (t j : RationalPluriForms (sC j) 1 m) = c j • (formPow (b j ()) m : RationalPluriForms (sC j) 1 m) :=
    fun j => by
      letI := functionFieldAlgebra (sC j)
      exact eq_repr_smul_formPow (b j) _
  let t' : ∀ j, logPluricanonicalSections (sC j) 1 (a * m) (BC j) := fun j =>
    letI := functionFieldAlgebra (sC j)
    ⟨c j ^ a • (formPow (b j ()) (a * m) : RationalPluriForms (sC j) 1 ((a * m : ℕ) : ℤ)),
      pow_mem_logPluricanonicalSections (b j ()) (c j) (hc j ▸ (t j).2) a ha⟩
  have ht'c : ∀ j, letI := functionFieldAlgebra (sC j)
      ∀ (ω : ⋀[(C j).functionField]^1 Ω[(C j).functionField⁄ℂ]) (c' : (C j).functionField),
        (t j : RationalPluriForms (sC j) 1 m) = c' • (formPow ω m : RationalPluriForms (sC j) 1 m) →
        (t' j : RationalPluriForms (sC j) 1 ((a * m : ℕ) : ℤ)) =
          c' ^ a • (formPow ω (a * m) : RationalPluriForms (sC j) 1 ((a * m : ℕ) : ℤ)) := by
    intro j ω c' h
    letI := functionFieldAlgebra (sC j)
    exact smul_formPow_pow_eq (b j) ((hc j).symm.trans h) a
  refine ⟨RM, t', ?_, ht'c⟩
  -- the residue restrictions of `t'`
  have hread : ∀ j {S : Scheme.{0}} {ι : S ⟶ C j} {BS : QDivisor S}
      (F : StratumAdjunctionData (sC j) (BC j) ι BS) (e : ℕ),
      haveI := F.isIntegral_stratum
      topologicalKrullDim S = e →
      letI := functionFieldAlgebra (ι ≫ sC j)
      ∀ (bS : Module.Basis Unit S.functionField (⋀[S.functionField]^e Ω[S.functionField⁄ℂ]))
        (c₁ : S.functionField),
        RS.toFun j F e (t j) = c₁ • (formPow (bS ()) m : RationalPluriForms (ι ≫ sC j) e m) →
        RM.toFun j F e (t' j) =
          c₁ ^ a • (formPow (bS ()) (a * m) : RationalPluriForms (ι ≫ sC j) e ((a * m : ℕ) : ℤ)) := by
    intro j S ι BS F e hS bS c₁ hc₁
    haveI := F.isIntegral_stratum
    letI := functionFieldAlgebra (sC j)
    letI := functionFieldAlgebra (ι ≫ sC j)
    have hIt := (RS.isIteratedResidue j F e (t j) hS).rec'
    rw [hc₁, hc j] at hIt
    have hpow := isIteratedResidueRec_pow (b j ()) (c j) F hS (bS ()) c₁ hIt a ha
    exact IsIteratedResidueRec.unique F (RM.isIteratedResidue j F e (t' j) hS).rec' hpow
  intro j j' S S' ι ι' BS BS' F F' e h₁ h₂ hdS hdS' σ hσ
  haveI := F.isIntegral_stratum
  haveI := F.isNormal_stratum
  haveI := F.isLocallyNoetherian_stratum
  haveI := F'.isIntegral_stratum
  haveI := F'.isNormal_stratum
  haveI := F'.isLocallyNoetherian_stratum
  haveI : LocallyOfFiniteType (ι ≫ sC j) := F.isNormalVariety.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (ι' ≫ sC j') := F'.isNormalVariety.1.toLocallyOfFiniteType
  letI := functionFieldAlgebra (ι ≫ sC j)
  letI := functionFieldAlgebra (ι' ≫ sC j')
  obtain ⟨b₁⟩ := exists_basis_topForms (sX := ι ≫ sC j) hdS
  obtain ⟨b₂⟩ := exists_basis_topForms (sX := ι' ≫ sC j') hdS'
  set c₁ := (ZTensorPower.basis b₁ m).repr (RS.toFun j F e (t j)) ()
  set c₂ := (ZTensorPower.basis b₂ m).repr (RS.toFun j' F' e (t j')) ()
  have hc₁ : RS.toFun j F e (t j) =
      c₁ • (formPow (b₁ ()) m : RationalPluriForms (ι ≫ sC j) e m) := eq_repr_smul_formPow b₁ _
  have hc₂ : RS.toFun j' F' e (t j') =
      c₂ • (formPow (b₂ ()) m : RationalPluriForms (ι' ≫ sC j') e m) := eq_repr_smul_formPow b₂ _
  rw [hread j F e hdS b₁ c₁ hc₁, hread j' F' e hdS' b₂ c₂ hc₂]
  have hadm := ht j j' F F' e h₁ h₂ hdS hdS' σ hσ
  rw [hc₁, hc₂, pluriformPullback_smul_formPow' hdS hdS' σ.toHom (b₂ ()) m c₂]
    at hadm
  rw [pluriformPullback_smul_formPow' hdS hdS' σ.toHom (b₂ ()) (a * m) (c₂ ^ a),
    map_pow (σ.toHom) c₂ a]
  exact smul_formPow_pow_eq b₁ hadm a

/-- **Frames in multiple degrees.** Local frames `g^*e · Ω_V` (and their pull-backs to `X`) in
degree `d` give local frames `g^*e^c · Ω_V^c` in degree `dc`. -/
private theorem exists_frame_pow {X V T : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [IsIntegral T]
    {sV : V ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sV] (q : X ⟶ V) [IsDominant q]
    [LocallyOfFiniteType (q ≫ sV)] (hVd : topologicalKrullDim V = 2)
    (hXd : topologicalKrullDim X = 2) (g : V ⟶ T) [IsDominant g] [IsDominant (q ≫ g)]
    {B : QDivisor X} {BV : QDivisor V} {d : ℕ} {ΩV : RationalPluriForms sV 2 d}
    (hfr : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ e : T.functionField, e ≠ 0 ∧
      GeneratesOn BV d (g ⁻¹ᵁ U) (functionFieldMap g e • ΩV) ∧
      GeneratesOn (sX := q ≫ sV) B d ((q ≫ g) ⁻¹ᵁ U)
        (functionFieldMap (q ≫ g) e • pullbackRationalPluriForms sV q ΩV))
    (c : ℕ) (hc : 0 < c) (D : ℕ) (hD : D = d * c) :
    ∃ ΩVc : RationalPluriForms sV 2 D, ∀ t : T, ∃ U : T.Opens, t ∈ U ∧
      ∃ e : T.functionField, e ≠ 0 ∧
      GeneratesOn BV D (g ⁻¹ᵁ U) (functionFieldMap g e • ΩVc) ∧
      GeneratesOn (sX := q ≫ sV) B D ((q ≫ g) ⁻¹ᵁ U)
        (functionFieldMap (q ≫ g) e • pullbackRationalPluriForms sV q ΩVc) := by
  subst hD
  have hVd2 : topologicalKrullDim V = ((2 : ℕ) : WithBot ℕ∞) := by rw [hVd]; rfl
  have hXd2 : topologicalKrullDim X = ((2 : ℕ) : WithBot ℕ∞) := by rw [hXd]; rfl
  obtain ⟨U₀, -, e₀, he₀, h₀V, h₀X⟩ := hfr (genericPoint T)
  have hΩ0 : ΩV ≠ 0 := fun h => h₀V.1 (by rw [h, smul_zero])
  have hqΩ0 : pullbackRationalPluriForms sV q ΩV ≠ 0 := fun h => h₀X.1 (by rw [h, smul_zero])
  obtain ⟨ΩVc, hΩc0, hqΩc0, hordV, hordX⟩ := exists_pow_pullback q hVd hXd hΩ0 hqΩ0 (c - 1)
    (d * c) (by rw [Nat.sub_add_cancel hc])
  refine ⟨ΩVc, fun t => ?_⟩
  obtain ⟨U, hU, e, he, hV, hX⟩ := hfr t
  have hec : e ^ c ≠ 0 := pow_ne_zero c he
  have hgec : functionFieldMap g (e ^ c) ≠ 0 := (map_ne_zero _).mpr hec
  have hqgec : functionFieldMap (q ≫ g) (e ^ c) ≠ 0 := (map_ne_zero _).mpr hec
  have hge : functionFieldMap g e ≠ 0 := (map_ne_zero _).mpr he
  have hqge : functionFieldMap (q ≫ g) e ≠ 0 := (map_ne_zero _).mpr he
  have hc' : ((c - 1 + 1 : ℕ) : ℤ) = c := by rw [Nat.sub_add_cancel hc]
  refine ⟨U, hU, e ^ c, hec, ⟨smul_ne_zero hgec hΩc0, fun Γ hΓ => ?_⟩,
    ⟨smul_ne_zero hqgec hqΩc0, fun Γ hΓ => ?_⟩⟩
  · have h := hV.2 Γ hΓ
    rw [Γ.ordForm_smul_of_topologicalKrullDim_eq hVd2 hge hΩ0] at h
    rw [Γ.ordForm_smul_of_topologicalKrullDim_eq hVd2 hgec hΩc0, hordV, hc', map_pow,
      Scheme.ord_pow hge]
    push_cast at h ⊢
    linear_combination (c : ℚ) * h
  · have h := hX.2 Γ hΓ
    rw [Γ.ordForm_smul_of_topologicalKrullDim_eq hXd2 hqge hqΩ0] at h
    rw [Γ.ordForm_smul_of_topologicalKrullDim_eq hXd2 hqgec hqΩc0, hordX, hc', map_pow,
      Scheme.ord_pow hqge]
    push_cast at h ⊢
    linear_combination (c : ℚ) * h

/-- The order along a prime divisor `E` of a regular function at a point of `E` is nonnegative. -/
private theorem ord_algebraMap_nonneg_of_mem {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (E : Mori.PrimeDivisor X) {x : X} (hx : x ∈ E.support)
    (a : X.presheaf.stalk x) : 0 ≤ X.ord (algebraMap _ X.functionField a) E.genericPoint := by
  have hsp : E.genericPoint ⤳ x := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
    exact specializes_iff_mem_closure.mpr hx
  rw [← MMP.Mori.algebraMap_stalkSpecializes hsp a]
  set b := (X.presheaf.stalkSpecializes hsp).hom a
  by_cases hb : b = 0
  · rw [hb, map_zero, Scheme.ord_zero]
    exact le_rfl
  rw [scheme_ord_algebraMap E.coheight_genericPoint hb]
  positivity

open IsLocalRing in
/-- **Regularity of the descended function along a horizontal floor curve.** If `h'^*ψ · Ω` has
residue `t'` along a horizontal floor curve `C` and `t'` is a section of `M(K_C + B_C)`, then
`ψ/e` is regular at every closed point `t` under `C`, for a frame `h'^*e · Ω` near `t`; it is a
unit at `t` if `t'` generates near a point of `C` over `t`. -/
private theorem exists_regular_of_horizontal
    {X T : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    (h' : X ⟶ T) [IsDominant h'] (hX : Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 2) {B : QDivisor X} (hB : Fourfold.IsPair sX B)
    (hdlt : MMP.Intersection.IsDltPair sX B) (hT1 : topologicalKrullDim T = 1)
    {C : Scheme.{0}} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] {j : C ⟶ X}
    {BC : QDivisor C} (hj : IsAdjunctionStep sX B j BC) [IsDominant (j ≫ h')]
    {M : ℕ} (hM0 : 0 < M) {Ω : RationalPluriForms sX 2 M} {ψ : T.functionField}
    {t' : RationalPluriForms (j ≫ sX) 1 M}
    (ht'mem : t' ∈ logPluricanonicalSections (j ≫ sX) 1 M BC)
    (hhor : IsPoincareResidue sX j 1 M (functionFieldMap h' ψ • Ω) t')
    {y : C} {t : T} (hyt : h' (j y) = t) (htη : t ≠ genericPoint T)
    {U : T.Opens} (hU : t ∈ U) {e : T.functionField} (he : e ≠ 0)
    (hτ : GeneratesOn B M (h' ⁻¹ᵁ U) (functionFieldMap h' e • Ω)) :
    ∃ φ : T.presheaf.stalk t, algebraMap _ T.functionField φ = ψ * e⁻¹ ∧
      ((∃ W : C.Opens, y ∈ W ∧ GeneratesOn BC M W t') → IsUnit φ) := by
  classical
  subst hyt
  have hXn : IsNormalVariety ℂ sX := hB.isPair.1
  haveI : LocallyOfFiniteType sX := hXn.1.toLocallyOfFiniteType
  obtain ⟨hT, P, -, hrange, hci, -⟩ := id hj
  haveI := hci
  have hCdim1 : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞) := by
    have := topologicalKrullDim_eq_one_of_isAdjunctionStep hdim hj
    rw [this]
  have ht1 : Order.coheight (h' (j y)) = 1 :=
    MMP.Fourfold.coheight_eq_one_of_ne_genericPoint hT1 htη
  set τ := functionFieldMap h' e • Ω with hτdef
  set ψe := ψ * e⁻¹ with hψedef
  have hψΩ : functionFieldMap h' ψ • Ω = functionFieldMap h' ψe • τ := by
    rw [hτdef, smul_smul, ← map_mul, hψedef, mul_assoc, inv_mul_cancel₀ he, mul_one]
  obtain ⟨ρ, hρ, hρ0, hρord⟩ := exists_residue_of_generatesOn hX hdim hB hdlt hj hM0 hτ
    ⟨j y, ⟨y, rfl⟩, show h' (j y) ∈ U from hU⟩
  have ht' : t' = functionFieldMap (j ≫ h') ψe • ρ := by
    have h1 := isPoincareResidue_functionFieldMap_smul h' hρ ψe
    rw [← hψΩ] at h1
    exact IsPoincareResidue.unique hj hhor h1
  have hyη : y ≠ genericPoint C := by
    rintro rfl
    apply htη
    have := map_genericPoint_of_isDominant (j ≫ h')
    simpa using this
  have hy1 : Order.coheight y = 1 := MMP.Fourfold.coheight_eq_one_of_ne_genericPoint hCdim1 hyη
  let Qy : Mori.PrimeDivisor C := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hy1
  have hQy : Qy.genericPoint = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hy1
  have hΓy : ∀ Γ : Mori.PrimeDivisor C, y ∈ Γ.support → Γ.genericPoint = y := by
    intro Γ hΓ
    have hsp : Γ.genericPoint ⤳ y := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hΓ
    exact MMP.ProgramBaseChange.eq_of_specializes_of_coheight_eq_one hsp
      Γ.coheight_genericPoint hy1
  have hρy : ∀ Γ : Mori.PrimeDivisor C, y ∈ Γ.support →
      (Γ.ordForm ρ : ℚ) = -(M * BC.coeff Γ) := fun Γ hΓ =>
    hρord Γ (by change h' (j Γ.genericPoint) ∈ U; rw [hΓy Γ hΓ]; exact hU)
  by_cases hψe : ψe = 0
  · refine ⟨0, by rw [map_zero, hψe], fun ⟨W, hyW, hW⟩ => ?_⟩
    exfalso
    apply hW.1
    rw [ht', hψe, map_zero, zero_smul]
  have hf0 : functionFieldMap (j ≫ h') ψe ≠ 0 := (map_ne_zero _).mpr hψe
  have ht'0 : t' ≠ 0 := by rw [ht']; exact smul_ne_zero hf0 hρ0
  obtain ⟨b, hb⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg y
    hf0 fun Γ hΓ => by
      have h1 := (MMP.Mori.mem_pluricanonicalSections.mp ht'mem).2 Γ
        ⟨Γ.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support _, trivial⟩ ht'0
      rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, ht',
        Γ.ordForm_smul_of_topologicalKrullDim_eq hCdim1 hf0 hρ0] at h1
      have h2 := hρy Γ hΓ
      have h3 := Int.floor_le (((M : ℕ) : ℤ) • BC.coeff Γ)
      rw [zsmul_eq_mul] at h3
      have : (0 : ℚ) ≤ (C.ord (functionFieldMap (j ≫ h') ψe) Γ.genericPoint : ℚ) := by
        have h1' : (0 : ℚ) ≤ ((C.ord (functionFieldMap (j ≫ h') ψe) Γ.genericPoint +
            Γ.ordForm ρ + ⌊((M : ℕ) : ℤ) • BC.coeff Γ⌋ : ℤ) : ℚ) := by exact_mod_cast h1
        rw [zsmul_eq_mul] at h1'
        push_cast at h1' h2 h3 ⊢
        linarith
      exact_mod_cast this
  obtain ⟨φ, hφ, hφb⟩ := exists_stalk_eq_of_functionFieldMap_eq (j ≫ h') y ht1 hb.symm
  refine ⟨φ, hφ, fun ⟨W, hyW, hW⟩ => ?_⟩
  have hordf : ∀ Γ : Mori.PrimeDivisor C, y ∈ Γ.support →
      C.ord (functionFieldMap (j ≫ h') ψe) Γ.genericPoint = 0 := by
    intro Γ hΓ
    have h1 := hW.2 Γ ⟨y, hΓ, hyW⟩
    rw [ht', Γ.ordForm_smul_of_topologicalKrullDim_eq hCdim1 hf0 hρ0] at h1
    have h2 := hρy Γ hΓ
    push_cast at h1 h2
    have : ((C.ord (functionFieldMap (j ≫ h') ψe) Γ.genericPoint : ℤ) : ℚ) = 0 := by linarith
    exact_mod_cast this
  obtain ⟨a, ha, haf⟩ := MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero y hf0
    hordf
  have hab : a = b := IsFractionRing.injective (C.presheaf.stalk y) C.functionField
    (by rw [haf, hb])
  rw [← hab] at hφb
  exact isUnit_of_map_unit ((j ≫ h').stalkMap y).hom φ (hφb ▸ ha)

/-- **The lift is a section.** If `ψ/e` is regular at every closed point `t` of `T`, for local
frames `h'^*e · Ω` near `t`, then `h'^*ψ · Ω ∈ H⁰(X, M(K + B))`. -/
private theorem mem_logPluricanonicalSections_of_regular
    {X T : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] (hdim : topologicalKrullDim X = 2)
    [IsIntegral T] (h' : X ⟶ T) [IsDominant h'] (hh'c : IsClosedMap h'.base) {B : QDivisor X} {M : ℕ}
    {Ω : RationalPluriForms sX 2 M} (ψ : T.functionField)
    (hreg : ∀ t : T, IsClosed ({t} : Set T) → ∃ U : T.Opens, t ∈ U ∧ ∃ e : T.functionField,
      e ≠ 0 ∧ GeneratesOn B M (h' ⁻¹ᵁ U) (functionFieldMap h' e • Ω) ∧
      ∃ φ : T.presheaf.stalk t, algebraMap _ T.functionField φ = ψ * e⁻¹) :
    functionFieldMap h' ψ • Ω ∈ logPluricanonicalSections sX 2 M B := by
  classical
  have hdim2 : topologicalKrullDim X = ((2 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  refine (mem_pluricanonicalSections_of_ne_bot (by simp)).2 fun Γ _ hs0 => ?_
  obtain ⟨x, hxΓ, hxc⟩ := Γ.idealSheaf.support.isClosed.exists_closed_singleton
    ⟨Γ.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support _⟩
  have htc : IsClosed ({h' x} : Set T) := by
    rw [← Set.image_singleton]; exact hh'c _ hxc
  obtain ⟨U, hU, e, he, hτ, φ, hφ⟩ := hreg (h' x) htc
  have hψ0 : ψ ≠ 0 := by
    rintro rfl; apply hs0; rw [map_zero, zero_smul]
  have hψe0 : ψ * e⁻¹ ≠ 0 := mul_ne_zero hψ0 (inv_ne_zero he)
  have hψΩ : functionFieldMap h' ψ • Ω =
      functionFieldMap h' (ψ * e⁻¹) • (functionFieldMap h' e • Ω) := by
    rw [smul_smul, ← map_mul, mul_assoc, inv_mul_cancel₀ he, mul_one]
  have hτ0 := hτ.1
  have hord := hτ.2 Γ ⟨x, hxΓ, hU⟩
  rw [hψΩ, Γ.ordForm_smul_of_topologicalKrullDim_eq hdim2 ((map_ne_zero _).mpr hψe0) hτ0,
    DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul]
  have hint : ((((M : ℕ) : ℤ) • B.coeff Γ : ℚ)) =
      ((-(Γ.ordForm (functionFieldMap h' e • Ω)) : ℤ) : ℚ) := by
    rw [zsmul_eq_mul]; push_cast; linarith
  rw [hint, Int.floor_intCast]
  have hfx : functionFieldMap h' (ψ * e⁻¹) =
      algebraMap _ X.functionField ((h'.stalkMap x).hom φ) := by
    rw [← hφ]; exact MMP.Mori.functionFieldMap_algebraMap_stalk h' x φ
  have := ord_algebraMap_nonneg_of_mem Γ hxΓ ((h'.stalkMap x).hom φ)
  rw [← hfx] at this
  omega

/-- Powers of local generators: if `c ω^{⊗m}` generates `𝒪(m(K + B))` on `W` then
`c^a ω^{⊗am}` generates `𝒪(am(K + B))` on `W` for `a > 0`. -/
private theorem generatesOn_pow {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [LocallyOfFiniteType sY] {n : ℕ}
    (hY : topologicalKrullDim Y = n) {BY : QDivisor Y} {m : ℕ} {W : Y.Opens}
    (ω : letI := functionFieldAlgebra sY; ⋀[Y.functionField]^n Ω[Y.functionField⁄ℂ])
    (c : Y.functionField)
    (h : letI := functionFieldAlgebra sY
      GeneratesOn BY m W (c • (formPow ω m : RationalPluriForms sY n m))) :
    letI := functionFieldAlgebra sY
    ∀ a, 0 < a → GeneratesOn BY (a * m) W
      (c ^ a • (formPow ω (a * m) : RationalPluriForms sY n ((a * m : ℕ) : ℤ))) := by
  letI := functionFieldAlgebra sY
  intro a ha
  suffices H : ∀ N : ℕ, N = a * m → GeneratesOn BY N W
      (c ^ a • (formPow ω N : RationalPluriForms sY n N)) from H _ rfl
  induction a, ha using Nat.le_induction with
  | base =>
    intro N hN
    rw [Nat.succ_eq_add_one, zero_add, one_mul] at hN
    subst hN
    simpa only [pow_one] using h
  | succ a ha ih =>
    intro N hN
    have h1 := ih _ rfl
    have hmul0 := RationalPluriForms.mul_ne_zero hY h1.1 h.1
    rw [RationalPluriForms.mul_smul_formPow, ← pow_succ] at hmul0
    rw [Nat.succ_mul] at hN
    subst hN
    refine ⟨hmul0, fun Γ hΓ => ?_⟩
    have hord := ordForm_mul Γ h1.1 h.1
    rw [RationalPluriForms.mul_smul_formPow, ← pow_succ] at hord
    rw [hord]
    have e1 := h1.2 Γ hΓ
    have e2 := h.2 Γ hΓ
    push_cast at e1 e2 ⊢
    linear_combination e1 + e2

/-- **Generators times local units.** If `τ` generates `𝒪(M(K + B))` over `h'⁻¹U` and `f ∈ k(T)`
is a unit at `t = h'(x₀) ∈ U`, then `h'^*f · τ` generates on a neighbourhood of every
generization `x` of `x₀`: off the support of `div(h'^*f)`, which avoids `x`. -/
private theorem exists_generatesOn_smul_of_isUnit {X T : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (hdim : topologicalKrullDim X = 2) [IsIntegral T] (h' : X ⟶ T) [IsDominant h']
    {B : QDivisor X} {M : ℕ} {U : T.Opens} {τ : RationalPluriForms sX 2 M}
    (hτ : GeneratesOn B M (h' ⁻¹ᵁ U) τ) {x x₀ : X} (hxx₀ : x ⤳ x₀) (hU : h' x₀ ∈ U)
    {φ : T.presheaf.stalk (h' x₀)} (hφu : IsUnit φ) :
    ∃ W : X.Opens, x ∈ W ∧
      GeneratesOn B M W (functionFieldMap h' (algebraMap _ T.functionField φ) • τ) := by
  classical
  have hdim2 : topologicalKrullDim X = ((2 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  set f := functionFieldMap h' (algebraMap _ T.functionField φ) with hfdef
  have hfst : f = algebraMap _ X.functionField ((h'.stalkMap x₀).hom φ) :=
    MMP.Mori.functionFieldMap_algebraMap_stalk h' x₀ φ
  have hu : IsUnit ((h'.stalkMap x₀).hom φ) := hφu.map _
  have hf0 : f ≠ 0 := by
    rw [hfst]; exact (hu.map (algebraMap _ X.functionField)).ne_zero
  set D := Mori.principalDivisor (unitOfFunction hf0) with hD
  have hDc : ∀ Γ : Mori.PrimeDivisor X, D.coeff Γ = X.ord f Γ.genericPoint := fun Γ => by
    rw [hD, Mori.coeff_principalDivisor]
    exact ord_toRationalFunctions Γ hf0 _ rfl
  have hzero : ∀ Γ : Mori.PrimeDivisor X, (Γ.support ∩ (D.supp.compl : Set X)).Nonempty →
      D.coeff Γ = 0 := by
    rintro Γ ⟨y, hyΓ, hyV⟩
    by_contra hne
    exact hyV (DivisorWithCoeffs.mem_supp_iff.2 ⟨Γ, hne, hyΓ⟩)
  refine ⟨h' ⁻¹ᵁ U ⊓ D.supp.compl, ⟨hxx₀.mem_open (h' ⁻¹ᵁ U).isOpen hU, fun hx => ?_⟩,
    smul_ne_zero hf0 hτ.1, fun Γ hΓ => ?_⟩
  · obtain ⟨Γ, hΓ, hxΓ⟩ := DivisorWithCoeffs.mem_supp_iff.1 hx
    apply hΓ
    rw [hDc, hfst]
    exact ord_algebraMap_eq_zero_of_isUnit_of_mem Γ
      (hxx₀.mem_closed Γ.idealSheaf.support.isClosed hxΓ) hu
  · obtain ⟨y, hyΓ, hyU, hyD⟩ := hΓ
    have h1 := hτ.2 Γ ⟨y, hyΓ, hyU⟩
    have h2 := hzero Γ ⟨y, hyΓ, hyD⟩
    rw [hDc] at h2
    rw [Γ.ordForm_smul_of_topologicalKrullDim_eq hdim2 hf0 hτ.1, h2, zero_add]
    exact h1

end Horiz

section HorizF

open MMP MMP.Fourfold MMP.Flips
open MMP.Mori hiding IsPair
open FloorAdjunction

/-- `isPoincareResidue_of_reflTransGen` for a structure morphism `sX` equal to `h' ≫ sT`. -/
private theorem isPoincareResidue_of_reflTransGen_of_comp_eq
    {X T : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] [LocallyOfFiniteType sT] (h' : X ⟶ T) [IsDominant h'] (hs : h' ≫ sT = sX)
    (hX : Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 2)
    {B : QDivisor X} (hB : Fourfold.IsPair sX B)
    (hdlt : MMP.Intersection.IsDltPair sX B)
    (C : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} → Scheme.{0})
    [∀ P, IsIntegral (C P)] [∀ P, IsLocallyNoetherian (C P)] [∀ P, IsNormal (C P)]
    (j : ∀ P, C P ⟶ X) (BC : ∀ P, QDivisor (C P))
    (hC : ∀ P, IsAdjunctionStep sX B (j P) (BC P) ∧
      Set.range (j P).base = (P.1.support : Set X))
    (hT1 : topologicalKrullDim T = 1) (hh'c : IsClosedMap h'.base) {M : ℕ} (hM0 : 0 < M)
    (RM : ResidueRestriction (fun P => j P ≫ sX) BC 1 M) {t' : ∀ P, _}
    (ht' : t' ∈ admissibleSections RM) {Ω : RationalPluriForms sX 2 M}
    (hfr : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ e : T.functionField, e ≠ 0 ∧
      GeneratesOn B M (h' ⁻¹ᵁ U) (functionFieldMap h' e • Ω))
    (ψ : T.functionField)
    (hhor : ∀ P, h' P.1.genericPoint = genericPoint T →
      IsPoincareResidue sX (j P) 1 M (functionFieldMap h' ψ • Ω)
        (t' P : RationalPluriForms (j P ≫ sX) 1 M))
    (hchain : ∀ P, ∃ P', h' P'.1.genericPoint = genericPoint T ∧
      Relation.ReflTransGen (fun P Q : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} =>
        ((P.1.support : Set X) ∩ Q.1.support).Nonempty) P P') (P) :
    IsPoincareResidue sX (j P) 1 M (functionFieldMap h' ψ • Ω)
      (t' P : RationalPluriForms (j P ≫ sX) 1 M) := by
  subst hs
  exact isPoincareResidue_of_reflTransGen h' hX hdim hB hdlt C j BC hC hT1 hh'c hM0 RM ht' hfr ψ
    hhor hchain P

/-- An integral scheme of dimension `< 2` with a point other than its generic point is a curve. -/
private theorem topologicalKrullDim_eq_one_of_lt_two {T : Scheme.{0}} [IsIntegral T]
    (h2 : topologicalKrullDim T < 2) {x : T} (hx : x ≠ genericPoint T) :
    topologicalKrullDim T = 1 := by
  have hlt : x < genericPoint T := lt_of_le_not_ge
    ((genericPoint_spec T).specializes trivial) fun h => hx
      ((((genericPoint_spec T).specializes trivial).antisymm h).eq.symm)
  have hc : (1 : ℕ∞) ≤ Order.coheight x := by
    have := Order.coheight_add_one_le hlt
    exact le_trans (by simp) this
  have h1 : ((1 : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim T :=
    le_trans (WithBot.coe_le_coe.mpr hc) (AlgebraicGeometry.coheight_le_topologicalKrullDim x)
  induction hd : topologicalKrullDim T using WithBot.recBotCoe with
  | bot => rw [hd] at h1; exact absurd h1 (by simp)
  | coe n =>
    rw [hd] at h1 h2
    have hn2 : n < 2 := WithBot.coe_lt_coe.mp (by simpa using h2)
    have hn1 : 1 ≤ n := WithBot.coe_le_coe.mp h1
    have hnt : n ≠ ⊤ := ne_top_of_lt hn2
    lift n to ℕ using hnt
    have : n = 1 := by norm_cast at hn2 hn1; omega
    subst this
    rfl

/-- **The base is a curve and a floor curve dominates it.** If `h = h' ≫ g_T` with the floor not
vertical over `R` and `dim T < 2`, then `T` is a curve and some floor curve dominates `T`. -/
private theorem exists_horizontal_of_not_isVertical {X T R : Scheme.{0}} [IsIntegral X] [IsIntegral T]
    {B : QDivisor X} (h : X ⟶ R) (h' : X ⟶ T) (gT : T ⟶ R) (hh : h' ≫ gT = h)
    (hhor : ¬ QDivisor.IsVertical h (Divisor.toQDivisor B.roundDown))
    (h2 : topologicalKrullDim T < 2) :
    topologicalKrullDim T = 1 ∧
      ∃ P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0}, h' P.1.genericPoint = genericPoint T := by
  classical
  simp only [QDivisor.IsVertical, not_forall] at hhor
  obtain ⟨E, hE, x, hxE, hne⟩ := hhor
  have hfl : ⌊B.coeff E⌋ ≠ 0 := by
    intro h0; apply hE
    change ((B.roundDown.coeff E : ℤ) : ℚ) = 0
    rw [DivisorWithCoeffs.coeff_roundDown, h0, Int.cast_zero]
  have hne' : h' x ≠ h' E.genericPoint := fun e => hne (by
    rw [← hh, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, e])
  have hT1 : topologicalKrullDim T = 1 := by
    by_cases e : h' E.genericPoint = genericPoint T
    · exact topologicalKrullDim_eq_one_of_lt_two h2 (x := h' x) (by rwa [e] at hne')
    · exact topologicalKrullDim_eq_one_of_lt_two h2 e
  refine ⟨hT1, ⟨E, hfl⟩, ?_⟩
  by_contra e
  have hcl := isClosed_singleton_of_ne_genericPoint hT1 e
  have hsp : E.genericPoint ⤳ x := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxE
    exact specializes_iff_mem_closure.mpr hxE
  exact hne' (Set.mem_singleton_iff.mp
    ((hsp.map h'.base.hom.continuous).mem_closed hcl (Set.mem_singleton _)))

/-- **Preadmissibility of a lift.** A section of `am(K + B)` whose residues along the floor curves
are the `a`-th powers of an admissible floor system is preadmissible. -/
private theorem mem_preadmissibleSections_of_forall_isPoincareResidue {X : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hdim : topologicalKrullDim X = 2) {B : QDivisor X}
    (C : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} → Scheme.{0})
    [∀ P, IsIntegral (C P)] [∀ P, IsLocallyNoetherian (C P)] [∀ P, IsNormal (C P)]
    (j : ∀ P, C P ⟶ X) (BC : ∀ P, QDivisor (C P))
    (hC : ∀ P, IsAdjunctionStep sX B (j P) (BC P) ∧
      Set.range (j P).base = (P.1.support : Set X))
    {m : ℕ} (RS : ResidueRestriction (fun P => j P ≫ sX) BC 1 m)
    {u : ∀ P, logPluricanonicalSections (j P ≫ sX) 1 m (BC P)} (hu : u ∈ admissibleSections RS)
    {a : ℕ} (RX : ResidueRestriction (fun _ : Unit => sX) (fun _ => B) (1 + 1) (a * m))
    (σ : logPluricanonicalSections sX (1 + 1) (a * m) B)
    (hσ : ∀ P,
      letI := functionFieldAlgebra (j P ≫ sX)
      ∀ (ω : ⋀[(C P).functionField]^1 Ω[(C P).functionField⁄ℂ]) (c : (C P).functionField),
        (u P : RationalPluriForms (j P ≫ sX) 1 m) =
            c • (formPow ω m : RationalPluriForms (j P ≫ sX) 1 m) →
          IsPoincareResidue sX (j P) 1 (a * m)
            (σ : RationalPluriForms sX (1 + 1) ((a * m : ℕ) : ℤ))
            (c ^ a • (formPow ω (a * m) :
              RationalPluriForms (j P ≫ sX) 1 ((a * m : ℕ) : ℤ)))) :
    (fun _ => σ) ∈ preadmissibleSections RX := by
  classical
  let Rf : ResidueRestriction
      (fun jj : (Σ _ : Unit, {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0}) => j jj.2 ≫ sX)
      (fun jj => BC jj.2) 1 m :=
    { setting :=
        { finite := by haveI := RS.setting.finite; infer_instance
          isProjectiveVariety := fun jj => RS.setting.isProjectiveVariety jj.2
          isPair := fun jj => RS.setting.isPair jj.2
          isDltPair := fun jj => RS.setting.isDltPair jj.2
          topologicalKrullDim_eq := fun jj => RS.setting.topologicalKrullDim_eq jj.2
          even := RS.setting.even
          pos := RS.setting.pos
          isCartierDivisor := fun jj _ _ _ F => RS.setting.isCartierDivisor jj.2 F }
      toFun := fun jj _ _ _ F e => RS.toFun jj.2 F e
      isIteratedResidue := fun jj _ _ _ F e τ h => RS.isIteratedResidue jj.2 F e τ h }
  exact mem_preadmissibleSections_of_liftsPow (X := fun _ : Unit => X)
    (sX := fun _ => sX) (B := fun _ => B) (Sf := fun jj => C jj.2) (jf := fun jj => j jj.2)
    (BSf := fun jj => BC jj.2) (fun _ => hdim) (fun jj => hC jj.2) Rf
    (u := fun jj => u jj.2)
    (fun i i' _ _ _ _ _ _ F F' e h1 h2 h3 h4 σ' hσ' => hu i.2 i'.2 F F' e h1 h2 h3 h4 σ' hσ')
    RX (fun _ => σ) (fun _ P => hσ P)

/-- A dominant closed map from a nonempty space is surjective. -/
private theorem surjective_of_isDominant_of_isClosedMap {Y Z : Scheme.{0}} (f : Y ⟶ Z) [IsDominant f]
    (hf : IsClosedMap f.base) : Function.Surjective f.base := by
  have h := hf.isClosed_range.closure_eq
  rw [f.denseRange.closure_eq] at h
  exact fun z => (h.symm ▸ Set.mem_univ z : z ∈ Set.range f.base)

/-- **The horizontal case over a curve.** If the reduced floor of `(X, B)` maps onto the base of
the semiample contraction `h : X ⟶ R` of a non-trivial adjoint, powers of admissible floor systems
lift. -/
private theorem exists_hasPowLifting_of_range_eq_univ_of_curve {X : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hX : Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 2)
    (hQ : IsQFactorial sX) {B : QDivisor X} (hB : IsPair sX B)
    (hdlt : MMP.Intersection.IsDltPair sX B) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2)
    (hsemi : QDivisor.IsRelativelySemiample sX (Divisor.toQDivisor K + B))
    (hD : ¬ (Divisor.toQDivisor K + B).QLinearlyEquivalent 0)
    {R : Scheme.{0}} [IsIntegral R] [CompactSpace R] [IsLocallyNoetherian R] [IsNormal R]
    {sR : R ⟶ Spec (.of ℂ)} (hRn : IsNormalVariety ℂ sR) (hRp : Mori.IsProjectiveVariety ℂ sR)
    (h : X ⟶ R) (hhf : h ≫ sR = sX) (hhp : IsProjectiveMorphism h)
    (hhO : ∀ U : R.Opens, IsIso (h.app U)) {q : ℕ} (hq : 0 < q) {A : Divisor R}
    (hAc : A.IsCartier) (hAamp : A.IsRelativelyAmple sR hAc) {W : Divisor X}
    (hW : ∃ hA, A.IsPullback h hA W)
    (hWq : (Divisor.toQDivisor W).QLinearlyEquivalent ((q : ℚ) • (Divisor.toQDivisor K + B)))
    (huniv : Set.range (B.roundDown.suppIdeal.subschemeι ≫ h).base = Set.univ)
    (hR1 : topologicalKrullDim R = 1) :
    ∃ k : ℕ, 0 < k ∧ HasPowLifting sX B k := by
  classical
  haveI : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have hXn : IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
  haveI := isDominant_of_forall_isIso_app h hhO
  haveI : IsProper h := isProper_of_isProjectiveMorphism h hhp
  have hp := isContraction_of_isIso_app hXn hRn h hhf hhp hhO
  have hAQ := isAmple_inv_smul hAc hAamp hq
  obtain ⟨n, hn, φ, hφ⟩ := hWq
  set M₀ : Divisor X := (n : ℤ) • W - Mori.principalDivisor φ with hM₀
  have hM₀q : Divisor.toQDivisor M₀ = ((n * q : ℕ) : ℤ) • (Divisor.toQDivisor K + B) := by
    rw [hM₀, map_sub, map_zsmul]
    ext E
    have h1 := congrArg (fun D : QDivisor X => D.coeff E) hφ
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, zsmul_eq_mul, smul_eq_mul] at h1 ⊢
    push_cast at h1 ⊢
    linear_combination h1
  have hM₀W : M₀.LinearlyEquivalent ((n : ℤ) • W) :=
    ⟨φ⁻¹, by rw [hM₀, sub_sub_cancel_left, Mori.principalDivisor_inv]⟩
  obtain ⟨hA0, hpbW⟩ := hW
  have hW' : ∃ hA, ((n : ℤ) • A).IsPullback h hA ((n : ℤ) • W) :=
    ⟨_, hpbW.zsmul hAc (n : ℤ)
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' h _)⟩
  have hAc' : ((n : ℤ) • A).IsCartier := hAc.zsmul _
  have hnq : 0 < n * q := Nat.mul_pos hn hq
  have hDA := exists_qLinearlyEquivalent_pullback h hAc' hW' hnq hM₀q hM₀W
  have hAeq : (((n * q : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor ((n : ℤ) • A)) =
      (q : ℚ)⁻¹ • Divisor.toQDivisor A := by
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    ext E
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, zsmul_eq_mul,
      smul_eq_mul]
    push_cast
    field_simp
  rw [hAeq] at hDA
  have hhor := not_isVertical_of_range_eq_univ h huniv hR1
  obtain ⟨V, _, _, _, _, sV, p, πV, KV, BV, ε, T, _, sT, g, gT, hps, hpp, hpb, hpπ, hgπ, hVp,
    hVdim, hVQ, hKV, hVlc, hε, hVklt, hgdom, hMFS, himg, hfib, hcoef⟩ :=
    exists_endpoint hX hdim hQ hdlt hK hRp hp hR1.le hAQ hDA hhor
  subst hps
  haveI := hgdom
  haveI : IsDominant p := hpb.isDominant
  haveI := hpp
  haveI : LocallyOfFiniteType sV := hVp.toLocallyOfFiniteType
  haveI : QuasiCompact sV := (quasiCompact_iff_compactSpace sV).mpr inferInstance
  have hgT : g ≫ sT = sV := hMFS.isContraction.comp_eq
  haveI : IsProper g := isProper_of_isProjectiveMorphism g hMFS.isContraction.isProjectiveMorphism
  have hTn : IsNormalVariety ℂ sT := hMFS.isContraction.isNormalVariety_target
  haveI : LocallyOfFiniteType sT := hTn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  haveI : IsNormal T := hTn.2
  have hh : (p ≫ g) ≫ gT = h := by rw [Category.assoc, hgπ, hpπ]
  haveI : IsDominant gT := by
    haveI : IsDominant ((p ≫ g) ≫ gT) := by rw [hh]; infer_instance
    exact IsDominant.of_comp (p ≫ g) gT
  have h2 : topologicalKrullDim T < 2 := hVdim ▸ hMFS.dim_lt
  obtain ⟨hT1, Ph, hPh⟩ := exists_horizontal_of_not_isVertical h (p ≫ g) gT hh hhor h2
  have hh'c : IsClosedMap (p ≫ g).base := (p ≫ g).isClosedMap
  -- the base frame
  obtain ⟨Ω, hΩ0, hfrX⟩ := exists_frame hXn hdim h (p ≫ g) gT hh hAc' hW' hK hnq hM₀q hM₀W
  obtain ⟨ΩV, hΩV, hΩV0, hfr⟩ := exists_frame_endpoint hVdim p hpb g hcoef hΩ0 hfrX
  rw [← hΩV] at hfr
  -- irreducible fibres and a horizontal floor curve of `V`
  have hnum := isNumericallyTrivialOver_of_frame hVQ hKV g hnq
    (fun t => by obtain ⟨U, hU, e, he, h1, -⟩ := hfr t; exact ⟨U, hU, e, he, h1⟩)
  have hirr := (IsMoriFibreSpace.isIrreducible_fibre_and_horizontalFloor_residue sV sT
    hVdim hVQ KV hKV BV hVlc ε hε hVklt g hMFS hT1 hnum).1
  obtain ⟨E₀, hE₀, hE₀h, -⟩ := exists_horizontal_floor (sV := sV) hVdim hT1 p g g.isClosedMap
    himg Ph.1 Ph.2 hPh
  have hggen : g.base (genericPoint V) = genericPoint T := map_genericPoint_of_isDominant g
  refine ⟨n * q, hnq, fun C _ _ _ j BC hC m hm hkm RS A _ t ht => ?_⟩
  haveI hci : ∀ P, IsClosedImmersion (j P) := fun P => (hC P).1.2.choose_spec.2.2.1
  have hjη : ∀ P, j P (genericPoint (C P)) = P.1.genericPoint := fun P =>
    MMP.CyclicChartDifferent.Aux.map_genericPoint_eq (j P) P.1 (hC P).2
  haveI : ∀ P, CompactSpace (C P) := fun P => (j P).isClosedEmbedding.compactSpace
  haveI : ∀ P, LocallyOfFiniteType (j P ≫ p ≫ sV) := fun P =>
    (hC P).1.1.1.toLocallyOfFiniteType
  have hCdim1 : ∀ P, topologicalKrullDim (C P) = ((1 : ℕ) : WithBot ℕ∞) := fun P => by
    have := topologicalKrullDim_eq_one_of_isAdjunctionStep hdim (hC P).1
    rw [this]
  haveI : IsDominant (j Ph ≫ (p ≫ g)) := isDominant_of_map_genericPoint _ (by
    change (p ≫ g) (j Ph (genericPoint (C Ph))) = _
    rw [hjη]; exact hPh)
  have hfin : Finite {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} := RS.setting.finite
  have hchain := fun P => exists_reflTransGen_horizontal p p.isClosedMap himg hfib hfin g hVdim
    hT1 g.isClosedMap hggen hirr E₀ hE₀ hE₀h P
  obtain ⟨m₁, hm₁, hdesc⟩ := exists_descent p hpb hX hdim hB hdlt hVdim hVQ hKV hVlc hε hVklt g
    hMFS hT1 himg hcoef hnq hfr C j BC hC
  obtain ⟨c, rfl⟩ := hkm
  have hm0 : 0 < n * q * c := RS.setting.pos
  have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hm0)
  have hM0 : 0 < (m₁ * (n * q * c)) := Nat.mul_pos hm₁ hm0
  obtain ⟨ΩM, hfrM⟩ := exists_frame_pow p hVdim hdim g hfr (c * m₁) (Nat.mul_pos hc0 hm₁) (m₁ * (n * q * c))
    (by ring)
  have hfrMX : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ e : T.functionField, e ≠ 0 ∧
      GeneratesOn B (m₁ * (n * q * c)) ((p ≫ g) ⁻¹ᵁ U)
        (functionFieldMap (p ≫ g) e • pullbackRationalPluriForms sV p ΩM) := fun t => by
    obtain ⟨U, hU, e, he, -, h1⟩ := hfrM t
    exact ⟨U, hU, e, he, h1⟩
  have hα : ∀ α, ∃ (RM : ResidueRestriction (fun P => j P ≫ p ≫ sV) BC 1 (m₁ * (n * q * c)))
      (t' : ∀ P, logPluricanonicalSections (j P ≫ p ≫ sV) 1 (m₁ * (n * q * c)) (BC P)),
      t' ∈ admissibleSections RM ∧ (∀ P,
        letI := functionFieldAlgebra (j P ≫ p ≫ sV)
        ∀ (ω : ⋀[(C P).functionField]^1 Ω[(C P).functionField⁄ℂ]) (f : (C P).functionField),
          (t α P : RationalPluriForms (j P ≫ p ≫ sV) 1 ((n * q * c : ℕ) : ℤ)) =
              f • (formPow ω (n * q * c) : RationalPluriForms (j P ≫ p ≫ sV) 1 ((n * q * c : ℕ) : ℤ)) →
          (t' P : RationalPluriForms (j P ≫ p ≫ sV) 1 ((m₁ * (n * q * c) : ℕ) : ℤ)) =
            f ^ m₁ • (formPow ω (m₁ * (n * q * c)) : RationalPluriForms (j P ≫ p ≫ sV) 1 ((m₁ * (n * q * c) : ℕ) : ℤ))) ∧
      ∃ ψ : T.functionField, ∀ P, IsPoincareResidue (p ≫ sV) (j P) 1 (m₁ * (n * q * c))
        (functionFieldMap (p ≫ g) ψ • pullbackRationalPluriForms sV p ΩM)
        (t' P : RationalPluriForms (j P ≫ p ≫ sV) 1 ((m₁ * (n * q * c) : ℕ) : ℤ)) := by
    intro α
    obtain ⟨RM, t', ht', hpow⟩ := exists_pow_admissibleSections RS (ht α) hm₁
    have hcrep : ∀ (P P' : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0})
        (σ : FunctionFieldEquiv (j P ≫ p ≫ sV) (j P' ≫ p ≫ sV)),
        IsCrepantBirationalMap (j P ≫ p ≫ sV) (j P' ≫ p ≫ sV) (BC P) (BC P') σ →
        pluriformPullback (j P ≫ p ≫ sV) (j P' ≫ p ≫ sV) σ.toHom 1 ((m₁ * (n * q * c) : ℕ) : ℤ)
          (t' P' : RationalPluriForms (j P' ≫ p ≫ sV) 1 ((m₁ * (n * q * c) : ℕ) : ℤ)) =
          (t' P : RationalPluriForms (j P ≫ p ≫ sV) 1 ((m₁ * (n * q * c) : ℕ) : ℤ)) :=
      fun P P' σ hσ => pluriformPullback_eq_of_mem_admissibleSections (k := ℂ) RM ht' P P' σ hσ
    have hd2 := hdesc (m₁ * (n * q * c)) (dvd_mul_right _ _) (hm.mul_left _) hM0 ΩM hfrM
      (fun P => (t' P : RationalPluriForms (j P ≫ p ≫ sV) 1 ((m₁ * (n * q * c) : ℕ) : ℤ)))
    obtain ⟨ψ, hψ⟩ := hd2 (fun P P' σ hσ => by
      have := hcrep P P' σ hσ
      exact this)
    exact ⟨RM, t', ht', hpow, ψ, isPoincareResidue_of_reflTransGen_of_comp_eq (p ≫ g) (sT := sT)
      (by rw [Category.assoc, hgT]) hX hdim hB hdlt C j BC hC hT1 hh'c hM0 RM ht' hfrMX ψ hψ
      hchain⟩
  choose RM t' ht' hpow ψ hres using hα
  obtain ⟨s, hs⟩ : ∃ s : A → RationalPluriForms (p ≫ sV) 2 ((m₁ * (n * q * c) : ℕ) : ℤ),
      ∀ α, s α = functionFieldMap (p ≫ g) (ψ α) • pullbackRationalPluriForms sV p ΩM :=
    ⟨fun α => functionFieldMap (p ≫ g) (ψ α) • pullbackRationalPluriForms sV p ΩM, fun _ => rfl⟩
  have hsurj := surjective_of_isDominant_of_isClosedMap (j Ph ≫ (p ≫ g))
    (j Ph ≫ (p ≫ g)).isClosedMap
  have hreg : ∀ α (y : C Ph) (t : T), (p ≫ g) (j Ph y) = t → t ≠ genericPoint T →
      ∀ (U : T.Opens), t ∈ U → ∀ e : T.functionField, e ≠ 0 →
      GeneratesOn B (m₁ * (n * q * c)) ((p ≫ g) ⁻¹ᵁ U)
        (functionFieldMap (p ≫ g) e • pullbackRationalPluriForms sV p ΩM) →
      ∃ φ : T.presheaf.stalk t, algebraMap _ T.functionField φ = ψ α * e⁻¹ ∧
        ((∃ W : (C Ph).Opens, y ∈ W ∧
          GeneratesOn (BC Ph) (m₁ * (n * q * c)) W (t' α Ph : RationalPluriForms (j Ph ≫ p ≫ sV) 1 ((m₁ * (n * q * c) : ℕ) : ℤ))) →
          IsUnit φ) :=
    fun α y t hyt htη U hU e he hτ => exists_regular_of_horizontal (p ≫ g) hX hdim hB hdlt hT1
      (hC Ph).1 hM0 (t' α Ph).2 (hres α Ph) hyt htη hU he hτ
  have hmem : ∀ α, s α ∈ logPluricanonicalSections (p ≫ sV) 2 (m₁ * (n * q * c)) B := fun α => by
    rw [hs]
    exact mem_logPluricanonicalSections_of_regular hdim (p ≫ g) hh'c (ψ α) fun t htc => by
      obtain ⟨U, hU, e, he, hτ⟩ := hfrMX t
      obtain ⟨y, hy⟩ := hsurj t
      obtain ⟨φ, hφ, -⟩ := hreg α y t (by rw [← hy]; rfl)
        (fun e' => MMP.Fourfold.not_isClosed_genericPoint hT1 (e' ▸ htc)) U hU e he hτ
      exact ⟨U, hU, e, he, hτ, φ, hφ⟩
  have hlift : ∀ α P,
      letI := functionFieldAlgebra (j P ≫ p ≫ sV)
      ∀ (ω : ⋀[(C P).functionField]^1 Ω[(C P).functionField⁄ℂ]) (f : (C P).functionField),
        (t α P : RationalPluriForms (j P ≫ p ≫ sV) 1 ((n * q * c : ℕ) : ℤ)) =
            f • (formPow ω (n * q * c) : RationalPluriForms (j P ≫ p ≫ sV) 1 ((n * q * c : ℕ) : ℤ)) →
          IsPoincareResidue (p ≫ sV) (j P) 1 (m₁ * (n * q * c)) (s α)
            (f ^ m₁ • (formPow ω (m₁ * (n * q * c)) : RationalPluriForms (j P ≫ p ≫ sV) 1 ((m₁ * (n * q * c) : ℕ) : ℤ))) := by
    intro α P ω f hf
    rw [← hpow α P ω f hf, hs]
    exact hres α P
  refine ⟨m₁, hm₁, fun RX α => ⟨fun _ => ⟨s α, hmem α⟩,
    mem_preadmissibleSections_of_forall_isPoincareResidue hdim C j BC hC RS (ht α) RX
      ⟨s α, hmem α⟩ (hlift α), fun P ω f hf => hlift α P ω f hf⟩, ?_⟩
  intro hgen x
  obtain ⟨x₀, hx₀, hx₀c⟩ := (isClosed_closure (s := ({x} : Set X))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  have hxx₀ : x ⤳ x₀ := specializes_iff_mem_closure.mpr hx₀
  have htc : IsClosed ({(p ≫ g) x₀} : Set T) := by
    rw [← Set.image_singleton]; exact hh'c _ hx₀c
  have htη : (p ≫ g) x₀ ≠ genericPoint T := fun e' =>
    MMP.Fourfold.not_isClosed_genericPoint hT1 (e' ▸ htc)
  obtain ⟨y, hy⟩ := hsurj ((p ≫ g) x₀)
  have hyt : (p ≫ g) (j Ph y) = (p ≫ g) x₀ := by rw [← hy]; rfl
  obtain ⟨α, Wy, hyW, hgW⟩ := hgen Ph y
  obtain ⟨U, hU, e, he, hτ⟩ := hfrMX ((p ≫ g) x₀)
  letI := functionFieldAlgebra (j Ph ≫ p ≫ sV)
  obtain ⟨b⟩ := exists_basis_topForms (sX := j Ph ≫ p ≫ sV) (hCdim1 Ph)
  have hb := eq_repr_smul_formPow b
    (t α Ph : RationalPluriForms (j Ph ≫ p ≫ sV) 1 ((n * q * c : ℕ) : ℤ))
  have hgW' := hgW
  rw [hb] at hgW'
  have hgM := generatesOn_pow (hCdim1 Ph) (b ()) _ hgW' m₁ hm₁
  rw [← hpow α Ph (b ()) _ hb] at hgM
  obtain ⟨φ, hφ, hunit⟩ := hreg α y _ hyt htη U hU e he hτ
  obtain ⟨W', hxW', hgen'⟩ := exists_generatesOn_smul_of_isUnit hdim (p ≫ g) hτ hxx₀ hU
    (hunit ⟨Wy, hyW, hgM⟩)
  rw [hφ, smul_smul, ← map_mul, mul_assoc (ψ α) e⁻¹ e, inv_mul_cancel₀ he, mul_one] at hgen'
  exact ⟨s α, hmem α, W', hxW', by rw [hs]; exact hgen', Or.inr ⟨α, hlift α⟩⟩

end HorizF

/-- **The horizontal case.** If the reduced floor of `(X, B)` maps onto the base of the
semiample contraction `h : X ⟶ R` of a non-trivial adjoint, powers of admissible floor systems
lift. -/
private theorem exists_hasPowLifting_of_range_eq_univ {X : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hX : Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 2)
    (hQ : IsQFactorial sX) {B : QDivisor X} (hB : IsPair sX B)
    (hdlt : MMP.Intersection.IsDltPair sX B) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2)
    (hsemi : QDivisor.IsRelativelySemiample sX (Divisor.toQDivisor K + B))
    (hD : ¬ (Divisor.toQDivisor K + B).QLinearlyEquivalent 0)
    {R : Scheme.{0}} [IsIntegral R] [CompactSpace R] [IsLocallyNoetherian R] [IsNormal R]
    {sR : R ⟶ Spec (.of ℂ)} (hRn : IsNormalVariety ℂ sR) (hRp : Mori.IsProjectiveVariety ℂ sR)
    (h : X ⟶ R) (hhf : h ≫ sR = sX) (hhp : IsProjectiveMorphism h)
    (hhO : ∀ U : R.Opens, IsIso (h.app U)) {q : ℕ} (hq : 0 < q) {A : Divisor R}
    (hAc : A.IsCartier) (hAamp : A.IsRelativelyAmple sR hAc) {W : Divisor X}
    (hW : ∃ hA, A.IsPullback h hA W)
    (hWq : (Divisor.toQDivisor W).QLinearlyEquivalent ((q : ℚ) • (Divisor.toQDivisor K + B)))
    (huniv : Set.range (B.roundDown.suppIdeal.subschemeι ≫ h).base = Set.univ) :
    ∃ k : ℕ, 0 < k ∧ HasPowLifting sX B k := by
  by_cases hR0 : topologicalKrullDim R = 0
  · exfalso
    apply hD
    have hempty : IsEmpty (Mori.PrimeDivisor R) := ⟨fun P => by
      have h1 := AlgebraicGeometry.coheight_le_topologicalKrullDim P.genericPoint
      rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, hR0] at h1
      exact absurd h1 (by decide)⟩
    have hA0 : A = 0 := Finsupp.ext fun P => (hempty.false P).elim
    subst hA0
    obtain ⟨hA, hpb⟩ := hW
    have hW0 : W = 0 := Divisor.IsPullback.eq hAc hpb (Divisor.isPullback_zero _)
    subst hW0
    obtain ⟨n, hn, φ, hφ⟩ := hWq
    refine ⟨n * q, Nat.mul_pos hn hq, φ⁻¹, ?_⟩
    ext E
    have h1 := congrArg (fun D : QDivisor X => D.coeff E) hφ
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_principalDivisor,
      DivisorWithCoeffs.coeff_zero, zsmul_eq_mul, map_zero] at h1 ⊢
    rw [PrimeDivisor.ord_inv]
    push_cast at h1 ⊢
    linear_combination (-1 : ℚ) * h1
  · haveI := isDominant_of_forall_isIso_app h hhO
    exact exists_hasPowLifting_of_range_eq_univ_of_curve hX hdim hQ hB hdlt hK hsemi hD hRn hRp
      h hhf hhp hhO hq hAc hAamp hW hWq huniv
      (topologicalKrullDim_eq_one_of_range_eq_univ hX hdim hdlt hRp h hhf hhp huniv hR0)

/-- **Preadmissible lifting through the semiample contraction.** For a `ℚ`-factorial projective
dlt surface `(X, B)` with nonempty floor and semiample adjoint `K + B` which is not `ℚ`-trivial,
powers of admissible floor systems lift: if the floor image is a proper closed subset of the base
`R` of the semiample contraction `h : X ⟶ R`, it has the structure-sheaf property. -/
private theorem exists_hasPowLifting_of_not_qLinearlyEquivalent {X : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 2) (hQ : IsQFactorial sX) {B : QDivisor X} (hB : IsPair sX B)
    (hdlt : MMP.Intersection.IsDltPair sX B) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2)
    (hsemi : QDivisor.IsRelativelySemiample sX (Divisor.toQDivisor K + B))
    (hD : ¬ (Divisor.toQDivisor K + B).QLinearlyEquivalent 0) (hS0 : B.roundDown ≠ 0)
    {q : ℕ} (hq : 0 < q) {M : Divisor X}
    (hMq : Divisor.toQDivisor M = (q : ℤ) • (Divisor.toQDivisor K + B))
    (E : X.CartierDivisor) (hfree : IsRelativelyFreeCartier sX E)
    (eE : MMP.CartierDivisor.sheaf E ≅ M.divisorialSheaf) :
    ∃ k : ℕ, 0 < k ∧ HasPowLifting sX B k := by
  classical
  haveI : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have hXn : IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
  obtain ⟨V', _, _, _, _, h, f', hhf, hV'n, hV'p, hhp, hhO, A, hAc, hAamp, ⟨eA⟩⟩ :=
    exists_steinFactor hXn hX isProjectiveVariety_id_spec sX (Category.comp_id _) E hfree eE
  rw [Category.comp_id] at hV'n hV'p
  haveI := isDominant_of_forall_isIso_app h hhO
  have hBA := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant h A
  obtain ⟨W, hW⟩ := hAc.exists_isPullback (f := h) hBA
  have eW := hW.divisorialSheafIso (hBc := hAc)
  obtain ⟨φ, hφ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso (eA ≪≫ eW.symm)
  have hMq' : Divisor.toQDivisor M = (q : ℚ) • (Divisor.toQDivisor K + B) := by
    rw [hMq, ← Int.cast_smul_eq_zsmul ℚ]; rfl
  have hWq : (Divisor.toQDivisor W).QLinearlyEquivalent ((q : ℚ) • (Divisor.toQDivisor K + B)) :=
    hMq' ▸ (Divisor.LinearlyEquivalent.qLinearlyEquivalent ⟨φ, hφ⟩).symm
  by_cases huniv : Set.range (B.roundDown.suppIdeal.subschemeι ≫ h).base = Set.univ
  · exact exists_hasPowLifting_of_range_eq_univ hX hdim hQ hB hdlt hK hsemi hD hV'n hV'p h hhf
      hhp hhO hq hAc hAamp ⟨hBA, hW⟩ hWq huniv
  refine ⟨q, hq, fun C _ _ _ j BC hC m hm hkm RS A' _ t ht => ?_⟩
  haveI := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal B.roundDown.supp
  set ιS := B.roundDown.suppIdeal.subschemeι with hιS
  have hrS : Set.range ιS.base = ⋃ E ∈ B.roundDown.support, (E.support : Set X) :=
    range_suppIdeal_subschemeι _
  haveI : IsReduced B.roundDown.suppIdeal.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hrV : Set.range (ιS ≫ h).imageι.base = h.base '' Set.range ιS.base := by
    haveI : IsProper h := isProper_of_isProjectiveMorphism h hhp
    change Set.range (ιS ≫ h).ker.subschemeι.base = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker,
      (ιS ≫ h).isClosedMap.isClosed_range.closure_eq, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp]
  have hO : ∀ U : (ιS ≫ h).image.Opens, IsIso ((ιS ≫ h).toImage.app U) := by
    haveI : Mori.IsProjectiveVariety ℂ sX := hX
    haveI : Mori.IsProjectiveVariety ℂ f' := hV'p
    have hgen := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' h
      ((q : ℚ)⁻¹ • Divisor.toQDivisor A)
    exact isIso_app_toImage_suppScheme_of_isDltPair_of_qLinearlyEquivalent sX f' h hhf hhp hhO
      K B ((MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hK B).mp hdlt) hQ _
      (isQCartier_inv_smul hAc hq) _ ⟨hgen, isPullback_inv_smul h hAc hW hq hgen⟩
      (qLinearlyEquivalent_inv_smul hq hMq ⟨φ, hφ⟩) huniv
  exact exists_isPoincareResidue_pow_of_mem_admissibleSections hX (n := 1) hdim hQ hB hdlt hK
    hsemi hV'n hV'p h hhf hhp hhO hq hAc hAamp ⟨hBA, hW⟩ hWq hS0 ιS hrS
    (ιS ≫ h).imageι hrV (ιS ≫ h).toImage (Scheme.Hom.toImage_imageι _) hO C j BC hC hm hkm RS t ht

section Steps

variable {I : Type u} {X : I → Scheme.{0}} [∀ i, IsIntegral (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    {sX : ∀ i, X i ⟶ Spec (.of ℂ)} {B : ∀ i, QDivisor (X i)}
    {Sf : (Σ i, {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0}) → Scheme.{0}}
    [∀ j, IsIntegral (Sf j)] [∀ j, IsLocallyNoetherian (Sf j)] [∀ j, IsNormal (Sf j)]
    {jf : ∀ j, Sf j ⟶ X j.1} {BSf : ∀ j, QDivisor (Sf j)}

variable (sX B) in
/-- `σ`, a section of `N(K_{X_i} + B_i)`, has no pole of full order `N` along any floor of `X_i`;
its Poincaré residues along the floors then vanish
(`isPoincareResidue_eq_zero_of_neg_lt_ordForm`). -/
private def ResiduesVanish (i : I) (N : ℕ) (σ : RationalPluriForms (sX i) 2 (N : ℤ)) : Prop :=
  ∀ P : {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0}, σ ≠ 0 → -(N : ℤ) < P.1.ordForm σ

variable [Finite I] [∀ i, CompactSpace (X i)]
    (hX : ∀ i, Mori.IsProjectiveVariety ℂ (sX i))
    (hdim : ∀ i, topologicalKrullDim (X i) = 2) (hQ : ∀ i, IsQFactorial (sX i))
    (hB : ∀ i, IsPair (sX i) (B i))
    (hdlt : ∀ i, MMP.Intersection.IsDltPair (sX i) (B i)) {K : ∀ i, Divisor (X i)}
    (hK : ∀ i, (K i).IsCanonicalDivisor (sX i) 2)
    (hsemi : ∀ i, QDivisor.IsRelativelySemiample (sX i) (Divisor.toQDivisor (K i) + B i))
    (hSf : ∀ j, IsAdjunctionStep (sX j.1) (B j.1) (jf j) (BSf j) ∧
      Set.range (jf j).base = (j.2.1.support : Set (X j.1)))

/-- **A finite generating family.** If admissible floor systems generate every floor at every
point, finitely many of them do. -/
private theorem exists_finite_generating_family {m : ℕ}
    (Rf : ResidueRestriction (fun j => jf j ≫ sX j.1) BSf 1 m)
    (hgen : ∀ j (y : Sf j), ∃ t ∈ admissibleSections Rf, ∃ V : (Sf j).Opens, y ∈ V ∧
      GeneratesOn (BSf j) m V
        ((t j : logPluricanonicalSections (jf j ≫ sX j.1) 1 m (BSf j)) :
          RationalPluriForms (jf j ≫ sX j.1) 1 m)) :
    ∃ (A : Type u) (_ : Finite A)
      (t : A → ∀ j, logPluricanonicalSections (jf j ≫ sX j.1) 1 m (BSf j)),
      (∀ α, t α ∈ admissibleSections Rf) ∧
      ∀ j (y : Sf j), ∃ α, ∃ V : (Sf j).Opens, y ∈ V ∧
        GeneratesOn (BSf j) m V
          ((t α j : logPluricanonicalSections (jf j ≫ sX j.1) 1 m (BSf j)) :
            RationalPluriForms (jf j ≫ sX j.1) 1 m) := by
  classical
  haveI := Rf.setting.finite
  have hcpt : ∀ j, CompactSpace (Sf j) := fun j => by
    haveI := (Rf.setting.isProjectiveVariety j).toIsVariety
    exact QuasiCompact.compactSpace_of_compactSpace (jf j ≫ sX j.1)
  choose t ht V hyV hV using hgen
  have hfin : ∀ j, ∃ F : Finset (Sf j),
      ⋃ y ∈ F, ((V j y : (Sf j).Opens) : Set (Sf j)) = Set.univ := fun j =>
    CompactSpace.elim_nhds_subcover _ fun y => (V j y).isOpen.mem_nhds (hyV j y)
  choose F hF using hfin
  refine ⟨Σ j, F j, inferInstance, fun α => t α.1 α.2, fun α => ht _ _, fun j y => ?_⟩
  have hy : y ∈ ⋃ y ∈ F j, ((V j y : (Sf j).Opens) : Set (Sf j)) := (hF j).symm ▸ Set.mem_univ y
  obtain ⟨y₀, hy₀, hy⟩ := Set.mem_iUnion₂.1 hy
  exact ⟨⟨j, ⟨y₀, hy₀⟩⟩, V j y₀, hy, hV j y₀⟩

include hX hdim hSf in
/-- **Powers of lifts.** For `σ ∈ H⁰(N(K_{X_i} + B_i))` and `b > 0`, the power
`σ^b ∈ H⁰(bN(K_{X_i} + B_i))` lifts `u^{bc}` whenever `σ` lifts `u^c`, generates wherever `σ`
does, and has zero floor residues if `σ` does. -/
private theorem exists_pow (i : I) {N : ℕ} {σ : RationalPluriForms (sX i) 2 (N : ℤ)}
    (hσ : σ ∈ logPluricanonicalSections (sX i) 2 N (B i)) {b : ℕ} (hb : 0 < b) :
    ∃ σ' ∈ logPluricanonicalSections (sX i) 2 (b * N) (B i),
      (∀ m c u, LiftsPow sX B jf BSf i m c N σ u → LiftsPow sX B jf BSf i m (b * c) (b * N) σ' u) ∧
      (∀ V : (X i).Opens, GeneratesOn (B i) N V σ → GeneratesOn (B i) (b * N) V σ') ∧
      (ResiduesVanish sX B i N σ → ResiduesVanish sX B i (b * N) σ') := by
  haveI : LocallyOfFiniteType (sX i) := (hX i).1.toLocallyOfFiniteType
  have hY : topologicalKrullDim (X i) = ((1 + 1 : ℕ) : WithBot ℕ∞) := by rw [hdim i]; rfl
  induction b, hb using Nat.le_induction with
  | base =>
    rw [show Nat.succ 0 * N = N by simp]
    exact ⟨σ, hσ, fun _ _ _ h => by simpa using h, fun _ h => h, id⟩
  | succ b hb ih =>
    obtain ⟨σ', hσ', h1, h2, h3⟩ := ih
    rw [Nat.succ_mul]
    refine ⟨RationalPluriForms.mul (sX i) 2 (b * N) N σ' σ,
      mul_mem_logPluricanonicalSections hσ' hσ, ?_, fun V hV => GeneratesOn.mul (hdim i) (h2 V hV) hV,
      fun hv P => ?_⟩
    · intro m c u hu P ω f hf
      rw [Nat.succ_mul]
      have := IsPoincareResidue.mul (hSf ⟨i, P⟩).1 hY (h1 m c u hu P ω f hf) (hu P ω f hf)
      rwa [RationalPluriForms.mul_smul_formPow, ← pow_add] at this
    · intro h0
      have h1 : σ' ≠ 0 := fun h => h0 (by rw [h, map_zero, LinearMap.zero_apply])
      have h2 : σ ≠ 0 := fun h => h0 (by rw [h, map_zero])
      rw [ordForm_mul P.1 h1 h2]
      have := h3 hv P h1
      have := hv P h2
      push_cast
      omega

include hX hdim hSf in
/-- **Powers of lifts, in degree `cm`.** If `σ ∈ H⁰(am(K_{X_i} + B_i))` and `a ∣ c`, some
`σ' ∈ H⁰(cm(K_{X_i} + B_i))` lifts `u^c` whenever `σ` lifts `u^a`, generates wherever `σ` does,
and has zero residues if `σ` does. -/
private theorem exists_pow_of_dvd (i : I) {m a c : ℕ} (ha : 0 < a) (hac : a ∣ c)
    (hc : 0 < c) {σ : RationalPluriForms (sX i) 2 ((a * m : ℕ) : ℤ)}
    (hσ : σ ∈ logPluricanonicalSections (sX i) 2 (a * m) (B i)) :
    ∃ σ' ∈ logPluricanonicalSections (sX i) 2 (c * m) (B i),
      (∀ u, LiftsPow sX B jf BSf i m a (a * m) σ u → LiftsPow sX B jf BSf i m c (c * m) σ' u) ∧
      (∀ V : (X i).Opens, GeneratesOn (B i) (a * m) V σ → GeneratesOn (B i) (c * m) V σ') ∧
      (ResiduesVanish sX B i (a * m) σ → ResiduesVanish sX B i (c * m) σ') := by
  obtain ⟨b, rfl⟩ := hac
  have hb : 0 < b := Nat.pos_of_mul_pos_left hc
  obtain ⟨σ', hσ', h1, h2, h3⟩ := exists_pow hX hdim hSf i hσ hb
  have e : b * (a * m) = a * b * m := by ring
  revert σ'
  rw [e]
  intro σ' hσ' h1 h2 h3
  exact ⟨σ', hσ', fun u hu => by simpa only [mul_comm b a] using h1 m a u hu, h2, h3⟩

include hX hdim hQ hB hdlt hK hsemi hSf in
/-- **The lifting on one component, from a lifting on its floor.** If powers of admissible systems
on the floor curves of `X_i` lift in the sense of `HasPowLifting`, the conclusion of
`exists_liftsPow_of_component` holds for `X_i`: restrict the floor systems to `X_i`, and note that
a generator with zero residues along the floors has no pole of full order there. -/
private theorem exists_liftsPow_of_component_of_hasPowLifting (i : I)
    (hfl : Nonempty {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0})
    (hst : ∃ k₁ : ℕ, 0 < k₁ ∧ HasPowLifting (sX i) (B i) k₁) :
    ∃ k : ℕ, 0 < k ∧ ∀ m : ℕ, k ∣ m → Even m →
      ∀ Rf : ResidueRestriction (fun j => jf j ≫ sX j.1) BSf 1 m,
      ∀ {A : Type*} [Finite A]
        (t : A → ∀ j, logPluricanonicalSections (jf j ≫ sX j.1) 1 m (BSf j)),
        (∀ α, t α ∈ admissibleSections Rf) →
        (∀ P (y : Sf ⟨i, P⟩), ∃ α, ∃ V : (Sf ⟨i, P⟩).Opens, y ∈ V ∧
          GeneratesOn (BSf ⟨i, P⟩) m V
            ((t α ⟨i, P⟩ : logPluricanonicalSections (jf ⟨i, P⟩ ≫ sX i) 1 m (BSf ⟨i, P⟩)) :
              RationalPluriForms (jf ⟨i, P⟩ ≫ sX i) 1 m)) →
        ∃ a : ℕ, 0 < a ∧
          (∀ α, ∃ σ ∈ logPluricanonicalSections (sX i) 2 (a * m) (B i),
            LiftsPow sX B jf BSf i m a (a * m) σ (t α)) ∧
          ∀ x : X i, ∃ σ ∈ logPluricanonicalSections (sX i) 2 (a * m) (B i),
            ∃ V : (X i).Opens, x ∈ V ∧ GeneratesOn (B i) (a * m) V σ ∧
              (ResiduesVanish sX B i (a * m) σ ∨ ∃ α, LiftsPow sX B jf BSf i m a (a * m) σ (t α)) := by
  classical
  haveI : LocallyOfFiniteType (sX i) := (hX i).toLocallyOfFiniteType
  haveI : QuasiCompact (sX i) := (hX i).toQuasiCompact
  obtain ⟨k₁, hk₁, hst⟩ := hst
  obtain ⟨m₀, hm₀, hRX⟩ := exists_residueRestriction (I := Unit) (S := fun _ => X i)
    (sS := fun _ => sX i) (B := fun _ => B i) (fun _ => hX i) (fun _ => hdim i) (fun _ => hQ i)
    (fun _ => hB i) (fun _ => hdlt i)
  refine ⟨k₁ * m₀, Nat.mul_pos hk₁ hm₀, fun m hm hev Rf A _ t ht hgen => ?_⟩
  have hm0 : 0 < m := Rf.setting.pos
  let R' : ResidueRestriction
      (fun P : {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0} => jf ⟨i, P⟩ ≫ sX i)
      (fun P => BSf ⟨i, P⟩) 1 m :=
    { setting :=
        { finite := by
            haveI := Rf.setting.finite
            exact Finite.of_injective
              (fun P : {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0} =>
                (⟨i, P⟩ : Σ i, {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0}))
              fun _ _ h => eq_of_heq (Sigma.mk.inj h).2
          isProjectiveVariety := fun P => Rf.setting.isProjectiveVariety ⟨i, P⟩
          isPair := fun P => Rf.setting.isPair ⟨i, P⟩
          isDltPair := fun P => Rf.setting.isDltPair ⟨i, P⟩
          topologicalKrullDim_eq := fun P => Rf.setting.topologicalKrullDim_eq ⟨i, P⟩
          even := Rf.setting.even
          pos := Rf.setting.pos
          isCartierDivisor := fun P => Rf.setting.isCartierDivisor ⟨i, P⟩ },
      toFun := fun P => Rf.toFun ⟨i, P⟩,
      isIteratedResidue := fun P => Rf.isIteratedResidue ⟨i, P⟩ }
  haveI := Fintype.ofFinite A
  let e := Fintype.equivFin A
  let t' : Fin (Fintype.card A) → ∀ P : {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0},
      logPluricanonicalSections (jf ⟨i, P⟩ ≫ sX i) 1 m (BSf ⟨i, P⟩) :=
    fun α P => t (e.symm α) ⟨i, P⟩
  have hadm : ∀ α, t' α ∈ admissibleSections R' :=
    fun α P P' _ _ _ _ _ _ F F' e' h₁ h₂ h₃ h₄ σ hσ =>
      ht (e.symm α) ⟨i, P⟩ ⟨i, P'⟩ F F' e' h₁ h₂ h₃ h₄ σ hσ
  obtain ⟨a, ha, hlifts, hgens⟩ := hst (fun P => Sf ⟨i, P⟩) (fun P => jf ⟨i, P⟩)
    (fun P => BSf ⟨i, P⟩) (fun P => hSf ⟨i, P⟩) hev (dvd_trans (dvd_mul_right _ _) hm) R' t' hadm
  obtain ⟨RX⟩ := hRX (a * m) (Nat.mul_pos ha hm0)
    (dvd_trans (dvd_trans (dvd_mul_left _ _) hm) (dvd_mul_left _ _)) (hev.mul_left a)
  refine ⟨a, ha, fun α => ?_, fun x => ?_⟩
  · obtain ⟨s, -, hs⟩ := hlifts RX (e α)
    refine ⟨(s () : RationalPluriForms (sX i) 2 ((a * m : ℕ) : ℤ)), (s ()).2,
      fun P ω f hf => hs P ω f ?_⟩
    simpa [t'] using hf
  · obtain ⟨σ, hσ, U, hxU, hgU, hcase⟩ := hgens (fun P y => by
      obtain ⟨α, V, hy, hV⟩ := hgen P y
      exact ⟨e α, V, hy, by simpa [t'] using hV⟩) x
    refine ⟨σ, hσ, U, hxU, hgU, ?_⟩
    rcases hcase with hz | ⟨α, hα⟩
    · left
      intro P hσ0
      have hle : -((a * m : ℕ) : ℤ) ≤ P.1.ordForm σ :=
        neg_le_ordForm_of_mem_logPluricanonicalSections (hdlt i).2.1 hσ P.1 hσ0
      obtain ⟨hstep, hrange⟩ := hSf ⟨i, P⟩
      obtain ⟨hT, -, -, -, hci, -⟩ := id hstep
      haveI := hci
      haveI : CompactSpace (Sf ⟨i, P⟩) := QuasiCompact.compactSpace_of_compactSpace (jf ⟨i, P⟩)
      haveI : LocallyOfFiniteType (jf ⟨i, P⟩ ≫ sX i) := hT.1.toLocallyOfFiniteType
      have hdT : topologicalKrullDim (Sf ⟨i, P⟩) = 1 :=
        topologicalKrullDim_eq_of_range_eq_support (sX i) (jf ⟨i, P⟩) P.1 hrange
          (by rw [hdim i]; rfl)
      obtain ⟨Q⟩ := nonempty_primeDivisor_of_one_le (jf ⟨i, P⟩ ≫ sX i) hdT le_rfl
      exact neg_lt_ordForm_of_isPoincareResidue_zero (sX i) ⟨(hX i).toIsVariety, inferInstance⟩
        (n := 1) (by rw [hdim i]; rfl) (jf ⟨i, P⟩) hT (by rw [hdT]; rfl) P.1 hrange Q
        (Nat.mul_pos ha hm0) hσ0 hle (hz P)
    · exact Or.inr ⟨e.symm α, fun P ω f hf => hα P ω f (by simpa [t'] using hf)⟩

include hX hdim hQ hB hdlt hK hsemi hSf in
/-- **The lifting on one component, nonzero adjoint, nonempty floor.** Through the semiample
contraction of `K_{X_i} + B_i`. -/
private theorem exists_liftsPow_of_component_of_steinFactor (i : I)
    (hfl : Nonempty {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0})
    (hD : ¬ (Divisor.toQDivisor (K i) + B i).QLinearlyEquivalent 0) :
    ∃ k : ℕ, 0 < k ∧ ∀ m : ℕ, k ∣ m → Even m →
      ∀ Rf : ResidueRestriction (fun j => jf j ≫ sX j.1) BSf 1 m,
      ∀ {A : Type*} [Finite A]
        (t : A → ∀ j, logPluricanonicalSections (jf j ≫ sX j.1) 1 m (BSf j)),
        (∀ α, t α ∈ admissibleSections Rf) →
        (∀ P (y : Sf ⟨i, P⟩), ∃ α, ∃ V : (Sf ⟨i, P⟩).Opens, y ∈ V ∧
          GeneratesOn (BSf ⟨i, P⟩) m V
            ((t α ⟨i, P⟩ : logPluricanonicalSections (jf ⟨i, P⟩ ≫ sX i) 1 m (BSf ⟨i, P⟩)) :
              RationalPluriForms (jf ⟨i, P⟩ ≫ sX i) 1 m)) →
        ∃ a : ℕ, 0 < a ∧
          (∀ α, ∃ σ ∈ logPluricanonicalSections (sX i) 2 (a * m) (B i),
            LiftsPow sX B jf BSf i m a (a * m) σ (t α)) ∧
          ∀ x : X i, ∃ σ ∈ logPluricanonicalSections (sX i) 2 (a * m) (B i),
            ∃ V : (X i).Opens, x ∈ V ∧ GeneratesOn (B i) (a * m) V σ ∧
              (ResiduesVanish sX B i (a * m) σ ∨ ∃ α, LiftsPow sX B jf BSf i m a (a * m) σ (t α)) := by
  classical
  haveI : LocallyOfFiniteType (sX i) := (hX i).toLocallyOfFiniteType
  obtain ⟨P₀⟩ := hfl
  have hS0 : (B i).roundDown ≠ 0 := by
    intro h0
    apply P₀.2
    have := congrArg (fun D : Divisor (X i) => D.coeff P₀.1) h0
    simpa [DivisorWithCoeffs.coeff_roundDown] using this
  obtain ⟨q, hq, L, hL, hLc, hfree⟩ :=
    exists_isRelativelyFreeDivisor_of_isRelativelySemiample (sX i) _ (hsemi i)
  obtain ⟨E, hE⟩ := exists_isWeilDivisorOfCartier_of_isCartier hLc
  obtain ⟨e⟩ := hE.nonempty_sheaf_iso_divisorialSheaf
  exact exists_liftsPow_of_component_of_hasPowLifting hX hdim hQ hB hdlt hK hsemi hSf i ⟨P₀⟩
    (exists_hasPowLifting_of_not_qLinearlyEquivalent (hX i) (hdim i) (hQ i) (hB i) (hdlt i)
      (hK i) (hsemi i) hD hS0 hq hL E (epi_counit_of_iso (sX i) e hfree) e)

include hX hdim hQ hB hdlt hK hsemi hSf in
/-- **The lifting on one component, big adjoint.** Through the adjoint ample model. -/
private theorem exists_liftsPow_of_component_of_isRelativelyBig (i : I)
    (hfl : Nonempty {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0})
    (hbig : QDivisor.IsRelativelyBig (sX i) (Divisor.toQDivisor (K i) + B i)) :
    ∃ k : ℕ, 0 < k ∧ ∀ m : ℕ, k ∣ m → Even m →
      ∀ Rf : ResidueRestriction (fun j => jf j ≫ sX j.1) BSf 1 m,
      ∀ {A : Type*} [Finite A]
        (t : A → ∀ j, logPluricanonicalSections (jf j ≫ sX j.1) 1 m (BSf j)),
        (∀ α, t α ∈ admissibleSections Rf) →
        (∀ P (y : Sf ⟨i, P⟩), ∃ α, ∃ V : (Sf ⟨i, P⟩).Opens, y ∈ V ∧
          GeneratesOn (BSf ⟨i, P⟩) m V
            ((t α ⟨i, P⟩ : logPluricanonicalSections (jf ⟨i, P⟩ ≫ sX i) 1 m (BSf ⟨i, P⟩)) :
              RationalPluriForms (jf ⟨i, P⟩ ≫ sX i) 1 m)) →
        ∃ a : ℕ, 0 < a ∧
          (∀ α, ∃ σ ∈ logPluricanonicalSections (sX i) 2 (a * m) (B i),
            LiftsPow sX B jf BSf i m a (a * m) σ (t α)) ∧
          ∀ x : X i, ∃ σ ∈ logPluricanonicalSections (sX i) 2 (a * m) (B i),
            ∃ V : (X i).Opens, x ∈ V ∧ GeneratesOn (B i) (a * m) V σ ∧
              (ResiduesVanish sX B i (a * m) σ ∨ ∃ α, LiftsPow sX B jf BSf i m a (a * m) σ (t α))  := by
  classical
  haveI : LocallyOfFiniteType (sX i) := (hX i).toLocallyOfFiniteType
  haveI : QuasiCompact (sX i) := (hX i).toQuasiCompact
  obtain ⟨P₀⟩ := hfl
  have hS0 : (B i).roundDown ≠ 0 := by
    intro h0
    apply P₀.2
    have := congrArg (fun D : Divisor (X i) => D.coeff P₀.1) h0
    simpa [DivisorWithCoeffs.coeff_roundDown] using this
  obtain ⟨q, hq, L, hL, hLc, hfree⟩ :=
    exists_isRelativelyFreeDivisor_of_isRelativelySemiample (sX i) _ (hsemi i)
  have hnef := isRelativelyNef_of_isRelativelyFreeDivisor hq hL hLc hfree
  exact exists_liftsPow_of_component_of_hasPowLifting hX hdim hQ hB hdlt hK hsemi hSf i ⟨P₀⟩
    (exists_isPoincareResidue_pow_of_isRelativelyBig (hX i) (hdim i) (hQ i) (hB i) (hdlt i)
      (hK i) (hsemi i) hnef hbig hS0)

include hX hdim hQ hB hdlt hK hsemi hSf in
/-- **The lifting on one component, nonzero adjoint and nonempty floor.** -/
private theorem exists_liftsPow_of_component_of_not_qLinearlyEquivalent (i : I)
    (hfl : Nonempty {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0})
    (hD : ¬ (Divisor.toQDivisor (K i) + B i).QLinearlyEquivalent 0) :
    ∃ k : ℕ, 0 < k ∧ ∀ m : ℕ, k ∣ m → Even m →
      ∀ Rf : ResidueRestriction (fun j => jf j ≫ sX j.1) BSf 1 m,
      ∀ {A : Type*} [Finite A]
        (t : A → ∀ j, logPluricanonicalSections (jf j ≫ sX j.1) 1 m (BSf j)),
        (∀ α, t α ∈ admissibleSections Rf) →
        (∀ P (y : Sf ⟨i, P⟩), ∃ α, ∃ V : (Sf ⟨i, P⟩).Opens, y ∈ V ∧
          GeneratesOn (BSf ⟨i, P⟩) m V
            ((t α ⟨i, P⟩ : logPluricanonicalSections (jf ⟨i, P⟩ ≫ sX i) 1 m (BSf ⟨i, P⟩)) :
              RationalPluriForms (jf ⟨i, P⟩ ≫ sX i) 1 m)) →
        ∃ a : ℕ, 0 < a ∧
          (∀ α, ∃ σ ∈ logPluricanonicalSections (sX i) 2 (a * m) (B i),
            LiftsPow sX B jf BSf i m a (a * m) σ (t α)) ∧
          ∀ x : X i, ∃ σ ∈ logPluricanonicalSections (sX i) 2 (a * m) (B i),
            ∃ V : (X i).Opens, x ∈ V ∧ GeneratesOn (B i) (a * m) V σ ∧
              (ResiduesVanish sX B i (a * m) σ ∨ ∃ α, LiftsPow sX B jf BSf i m a (a * m) σ (t α)) := by
  by_cases hbig : QDivisor.IsRelativelyBig (sX i) (Divisor.toQDivisor (K i) + B i)
  · exact exists_liftsPow_of_component_of_isRelativelyBig hX hdim hQ hB hdlt hK hsemi hSf i hfl
      hbig
  · exact exists_liftsPow_of_component_of_steinFactor hX hdim hQ hB hdlt hK hsemi hSf i hfl hD

include hX hdim hQ hB hdlt hK hsemi hSf in
/-- **The lifting on one component.** For a single component `X_i` there is `k > 0` such that
in every degree `m` divisible by `k`, every finite family of admissible floor systems which
generates the floors of `X_i` has a common power `a` such that: the `a`-th power of every member
lifts to a section of `am(K_{X_i} + B_i)`, and every point of `X_i` has a generating section of
`am(K_{X_i} + B_i)` which either has zero residues along the floors or lifts the `a`-th power of
a member of the family. -/
private theorem exists_liftsPow_of_component (i : I) :
    ∃ k : ℕ, 0 < k ∧ ∀ m : ℕ, k ∣ m → Even m →
      ∀ Rf : ResidueRestriction (fun j => jf j ≫ sX j.1) BSf 1 m,
      ∀ {A : Type*} [Finite A]
        (t : A → ∀ j, logPluricanonicalSections (jf j ≫ sX j.1) 1 m (BSf j)),
        (∀ α, t α ∈ admissibleSections Rf) →
        (∀ P (y : Sf ⟨i, P⟩), ∃ α, ∃ V : (Sf ⟨i, P⟩).Opens, y ∈ V ∧
          GeneratesOn (BSf ⟨i, P⟩) m V
            ((t α ⟨i, P⟩ : logPluricanonicalSections (jf ⟨i, P⟩ ≫ sX i) 1 m (BSf ⟨i, P⟩)) :
              RationalPluriForms (jf ⟨i, P⟩ ≫ sX i) 1 m)) →
        ∃ a : ℕ, 0 < a ∧
          (∀ α, ∃ σ ∈ logPluricanonicalSections (sX i) 2 (a * m) (B i),
            LiftsPow sX B jf BSf i m a (a * m) σ (t α)) ∧
          ∀ x : X i, ∃ σ ∈ logPluricanonicalSections (sX i) 2 (a * m) (B i),
            ∃ V : (X i).Opens, x ∈ V ∧ GeneratesOn (B i) (a * m) V σ ∧
              (ResiduesVanish sX B i (a * m) σ ∨ ∃ α, LiftsPow sX B jf BSf i m a (a * m) σ (t α)) := by
  by_cases hfl : IsEmpty {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0}
  · -- no floor: generators of a free multiple, and no residue condition
    obtain ⟨N, hN, hgen⟩ :=
      exists_generatesOn_of_isRelativelySemiample (hX i) (hdim i) (hK i) (hsemi i)
    refine ⟨N, hN, fun m hm _ Rf A _ t _ _ => ?_⟩
    obtain ⟨c, rfl⟩ := hm
    have hc : 0 < c := Nat.pos_of_mul_pos_left Rf.setting.pos
    refine ⟨1, one_pos, fun α => ⟨0, zero_mem _, fun P => (hfl.false P).elim⟩, fun x => ?_⟩
    obtain ⟨σ, hσ, V, hxV, hV⟩ := hgen x
    obtain ⟨σ', hσ', -, h2, -⟩ := exists_pow hX hdim hSf i hσ hc
    have e : c * N = 1 * (N * c) := by ring
    revert σ'
    rw [e]
    intro σ' hσ' h2
    exact ⟨σ', hσ', V, hxV, h2 V hV, Or.inl fun P => (hfl.false P).elim⟩
  by_cases hD : (Divisor.toQDivisor (K i) + B i).QLinearlyEquivalent 0
  · -- trivial adjoint: admissible floor systems extend, and nonzero sections generate everywhere
    haveI : LocallyOfFiniteType (sX i) := (hX i).toLocallyOfFiniteType
    haveI : IsProper (sX i) := (instIsProperVarietyOfIsProjectiveVariety ℂ (sX i)).toIsProper
    have hXn : IsNormalVariety ℂ (sX i) := ⟨(hX i).toIsVariety, inferInstance⟩
    obtain ⟨m₀, hm₀, hext⟩ := exists_isPoincareResidue_of_mem_admissibleSections (hX i) (hdim i)
      (hQ i) (hB i) (hdlt i) (hK i) hD (fun P => Sf ⟨i, P⟩) (fun P => jf ⟨i, P⟩)
      (fun P => BSf ⟨i, P⟩) (fun P => hSf ⟨i, P⟩)
    obtain ⟨N, hN, hω⟩ := exists_pluriform_ordForm_eq_neg_smul hXn (hdim i) (hK i) hD
    refine ⟨m₀ * N, Nat.mul_pos hm₀ hN, fun m hm hev Rf A _ t ht hgen => ?_⟩
    have hm0 : 0 < m := Rf.setting.pos
    let R' : ResidueRestriction
        (fun P : {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0} => jf ⟨i, P⟩ ≫ sX i)
        (fun P => BSf ⟨i, P⟩) 1 m :=
      { setting :=
          { finite := by
              haveI := Rf.setting.finite
              exact Finite.of_injective
                (fun P : {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0} =>
                  (⟨i, P⟩ : Σ i, {P : Mori.PrimeDivisor (X i) // ⌊(B i).coeff P⌋ ≠ 0}))
                fun _ _ h => eq_of_heq (Sigma.mk.inj h).2
            isProjectiveVariety := fun P => Rf.setting.isProjectiveVariety ⟨i, P⟩
            isPair := fun P => Rf.setting.isPair ⟨i, P⟩
            isDltPair := fun P => Rf.setting.isDltPair ⟨i, P⟩
            topologicalKrullDim_eq := fun P => Rf.setting.topologicalKrullDim_eq ⟨i, P⟩
            even := Rf.setting.even
            pos := Rf.setting.pos
            isCartierDivisor := fun P => Rf.setting.isCartierDivisor ⟨i, P⟩ },
        toFun := fun P => Rf.toFun ⟨i, P⟩,
        isIteratedResidue := fun P => Rf.isIteratedResidue ⟨i, P⟩ }
    have hadm : ∀ α, (fun P => t α ⟨i, P⟩) ∈ admissibleSections R' :=
      fun α P P' _ _ _ _ _ _ F F' e h₁ h₂ h₃ h₄ σ hσ =>
        ht α ⟨i, P⟩ ⟨i, P'⟩ F F' e h₁ h₂ h₃ h₄ σ hσ
    choose s hs hres using fun α =>
      hext m (dvd_trans (dvd_mul_right _ _) hm) hev R' _ (hadm α)
    obtain ⟨ω, hω0, hωord⟩ := hω m (dvd_trans (dvd_mul_left _ _) hm) hm0
    have hlift : ∀ α, LiftsPow sX B jf BSf i m 1 m (s α) (t α) := by
      intro α P ω' f hf
      rw [pow_one, ← hf]
      exact hres α P
    refine ⟨1, one_pos, ?_⟩
    rw [one_mul]
    refine ⟨fun α => ⟨s α, hs α, hlift α⟩, fun x => ?_⟩
    obtain ⟨P₀⟩ := not_isEmpty_iff.1 hfl
    obtain ⟨α₀, V₀, -, hV₀⟩ := hgen P₀ (genericPoint _)
    have hs0 : s α₀ ≠ 0 := by
      intro h0
      have h1 := hres α₀ P₀
      rw [h0] at h1
      have h2 := IsPoincareResidue.smul (hSf ⟨i, P₀⟩).1 h1 0
      rw [zero_smul, zero_smul] at h2
      exact hV₀.1 (IsPoincareResidue.unique (hSf ⟨i, P₀⟩).1 h1 h2)
    obtain ⟨c, hc⟩ := exists_eq_smul_of_mem_logPluricanonicalSections (hdim i) hω0 hωord (hs α₀)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hs0 (by rw [hc, zero_smul])
    refine ⟨s α₀, hs α₀, ⊤, trivial, ⟨hs0, fun Γ _ => ?_⟩, Or.inr ⟨α₀, hlift α₀⟩⟩
    rw [hc, ordForm_const_smul Γ hc0, hωord Γ]
    ring
  · exact exists_liftsPow_of_component_of_not_qLinearlyEquivalent hX hdim hQ hB hdlt hK hsemi hSf i
      (not_isEmpty_iff.1 hfl) hD

/-- **Sections with zero floor residues are preadmissible**, with zero in the other
components. -/
private theorem single_mem_preadmissibleSections [DecidableEq I] {N : ℕ}
    (R : ResidueRestriction sX B 2 N) (i : I) (σ : logPluricanonicalSections (sX i) 2 N (B i))
    (hσ : ResiduesVanish sX B i N (σ : RationalPluriForms (sX i) 2 (N : ℤ))) :
    Pi.single i σ ∈ preadmissibleSections R := by
  classical
  have key : ∀ (i' : I) {S : Scheme.{0}} {ι : S ⟶ X i'} {BS : QDivisor S}
      (F : StratumAdjunctionData (sX i') (B i') ι BS) (e : ℕ), 1 ≤ F.length →
      topologicalKrullDim S = e →
      (haveI := F.isIntegral_stratum
       R.toFun i' F e
        ((Pi.single i σ : ∀ i, logPluricanonicalSections (sX i) 2 N (B i)) i') = 0) := by
    intro i' S ι BS F e hF hS
    haveI := F.isIntegral_stratum
    by_cases hi : i' = i
    · subst hi
      rw [Pi.single_eq_same]
      have hR := R.isIteratedResidue i' F e σ hS
      refine eq_zero_of_isIteratedResidueRec (R.setting.isProjectiveVariety i')
        (R.setting.isPair i').isPair.1 (by norm_num) R.setting.pos
        (R.setting.topologicalKrullDim_eq i') (fun P hP h0 => ?_) F hF hS hR.rec'
      have hfl : ⌊(B i').coeff P⌋ ≠ 0 := by
        have := Int.floor_mono hP
        rw [Int.floor_one] at this
        omega
      exact hσ ⟨P, hfl⟩ h0
    · rw [Pi.single_eq_of_ne hi, map_zero]
  intro i₁ i₂ S S' ι ι' BS BS' F F' e h₁ h₂ hS hS' σc hσc
  haveI := F.isIntegral_stratum
  haveI := F'.isIntegral_stratum
  rw [key i₂ F' e h₂ hS', key i₁ F e h₁ hS, map_zero]

end Steps

private theorem solution
    {I : Type*} [Finite I] {S : I → Scheme.{0}} [∀ i, IsIntegral (S i)]
    [∀ i, CompactSpace (S i)] [∀ i, IsLocallyNoetherian (S i)] [∀ i, IsNormal (S i)]
    {sS : ∀ i, S i ⟶ Spec (.of ℂ)} (hS : ∀ i, Mori.IsProjectiveVariety ℂ (sS i))
    (hdim : ∀ i, topologicalKrullDim (S i) = 2) (hQ : ∀ i, IsQFactorial (sS i))
    {B : ∀ i, QDivisor (S i)} (hB : ∀ i, IsPair (sS i) (B i))
    (hdlt : ∀ i, MMP.Intersection.IsDltPair (sS i) (B i)) {K : ∀ i, Divisor (S i)}
    (hK : ∀ i, (K i).IsCanonicalDivisor (sS i) 2)
    (hsemi : ∀ i, QDivisor.IsRelativelySemiample (sS i) (Divisor.toQDivisor (K i) + B i)) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, 0 < m → m₀ ∣ m → Even m →
      Nonempty (ResidueRestriction sS B 2 m) ∧
      ∀ (R : ResidueRestriction sS B 2 m) (i : I) (x : S i),
        ∃ s ∈ preadmissibleSections R, ∃ V : (S i).Opens, x ∈ V ∧
          GeneratesOn (B i) m V
            ((s i : logPluricanonicalSections (sS i) 2 m (B i)) :
              RationalPluriForms (sS i) 2 m) := by
  classical
  haveI := Fintype.ofFinite I
  haveI : ∀ i, LocallyOfFiniteType (sS i) := fun i => (hS i).1.toLocallyOfFiniteType
  -- the floor curves `C_{i,P}` with their differents
  have hfl : ∀ j : (Σ i, {P : Mori.PrimeDivisor (S i) // ⌊(B i).coeff P⌋ ≠ 0}),
      ∃ (T : Scheme.{0}) (jT : T ⟶ S j.1) (BT : QDivisor T)
        (hj : IsAdjunctionStep (sS j.1) (B j.1) jT BT),
          Set.range jT.base = (j.2.1.support : Set (S j.1)) ∧
          haveI : IsIntegral T := hj.1.1.toIsIntegral
          haveI : IsNormal T := hj.1.2
          haveI : IsLocallyNoetherian T := by
            have := hj.1.1
            exact LocallyOfFiniteType.isLocallyNoetherian (jT ≫ sS j.1)
          MMP.Intersection.IsDltPair (jT ≫ sS j.1) BT := fun j =>
    exists_isAdjunctionStep_of_one_le_coeff (hdlt j.1)
      (d := 1) (by rw [hdim j.1]; rfl) j.2.1
      (one_le_coeff_of_floor_ne_zero (hdlt j.1) j.2.1 j.2.2)
  choose Sf jf BSf hjf hrf hdltf using hfl
  have hSf : ∀ j, IsAdjunctionStep (sS j.1) (B j.1) (jf j) (BSf j) ∧
      Set.range (jf j).base = (j.2.1.support : Set (S j.1)) := fun j => ⟨hjf j, hrf j⟩
  haveI : ∀ j, IsIntegral (Sf j) := fun j => (hSf j).1.1.1.toIsIntegral
  haveI : ∀ j, IsNormal (Sf j) := fun j => (hSf j).1.1.2
  haveI : ∀ j, IsLocallyNoetherian (Sf j) := fun j => by
    have := (hSf j).1.1.1.toLocallyOfFiniteType
    exact LocallyOfFiniteType.isLocallyNoetherian (jf j ≫ sS j.1)
  haveI : Finite (Σ i, {P : Mori.PrimeDivisor (S i) // ⌊(B i).coeff P⌋ ≠ 0}) := by
    haveI := fun i => finite_floor (B i)
    infer_instance
  -- admissible generation on the floor curves
  obtain ⟨m₁, hm₁, hcurve⟩ : ∃ m₁ : ℕ, 0 < m₁ ∧ ∀ m : ℕ, 0 < m → m₁ ∣ m → Even m →
      IsStratifiedSectionSetting (fun j => jf j ≫ sS j.1) BSf 1 m ∧
      ∀ (Rf : ResidueRestriction (fun j => jf j ≫ sS j.1) BSf 1 m) j (y : Sf j),
        ∃ t ∈ admissibleSections Rf, ∃ U : (Sf j).Opens, y ∈ U ∧
          Mori.GeneratesOn (BSf j) m U (t j).1 := by
    have hci : ∀ j, IsClosedImmersion (jf j) := fun j => by
      obtain ⟨-, -, -, -, hci, -⟩ := (hSf j).1
      exact hci
    refine exists_admissibleSections_generatesOn_of_dlt_curve (fun j => (hSf j).1.1)
      (fun j => ?_) (fun j => topologicalKrullDim_eq_of_range_eq_support (sS j.1) (jf j) j.2.1
        (hSf j).2 (by rw [hdim j.1]; rfl)) hdltf (fun j KC hKC => ?_)
    · obtain ⟨-, -, -, -, hci, -⟩ := (hSf j).1
      haveI := hci
      haveI : IsProper (sS j.1) := (instIsProperVarietyOfIsProjectiveVariety ℂ (sS j.1)).toIsProper
      infer_instance
    · exact zero_le_degree_of_isAdjunctionStep (hS j.1) (hdim j.1) (hQ j.1) (hB j.1) (hdlt j.1)
        (hK j.1) (hsemi j.1) (hSf j).1 (hdltf j) KC hKC
  -- the lifting on each component
  choose k hk0 hk using fun i => exists_liftsPow_of_component hS hdim hQ hB hdlt hK hsemi hSf i
  -- the base floor degree `m'`
  set m' : ℕ := 2 * m₁ * ∏ i, k i with hm'
  have hm'0 : 0 < m' :=
    Nat.mul_pos (Nat.mul_pos two_pos hm₁) (Finset.prod_pos fun i _ => hk0 i)
  have hkm : ∀ i, k i ∣ m' := fun i =>
    (Finset.dvd_prod_of_mem k (Finset.mem_univ i)).trans (Dvd.intro_left _ rfl)
  have hev' : Even m' := by rw [hm', mul_assoc]; exact even_two_mul _
  obtain ⟨hset, hgen⟩ := hcurve m' hm'0 ⟨2 * ∏ i, k i, by rw [hm']; ring⟩ hev'
  obtain ⟨Rf⟩ := nonempty_residueRestriction_curve hset
  obtain ⟨G, hGfin, tG, htGadm, htGgen⟩ := exists_finite_generating_family Rf fun j y => by
    obtain ⟨t, ht, U, hyU, hU⟩ := hgen Rf j y
    exact ⟨t, ht, U, hyU, hU⟩
  have hcomp := fun i => hk i m' (hkm i) hev' Rf tG htGadm fun P y => htGgen ⟨i, P⟩ y
  choose a ha0 hlift hgenx using hcomp
  set q : ℕ := ∏ i, a i with hq
  have hq0 : 0 < q := Finset.prod_pos fun i _ => ha0 i
  obtain ⟨mR, hmR0, hR⟩ := exists_residueRestriction hS hdim hQ hB hdlt
  refine ⟨q * m' * mR, Nat.mul_pos (Nat.mul_pos hq0 hm'0) hmR0, ?_⟩
  intro m hmpos hdvd hev
  refine ⟨hR m hmpos ((Dvd.intro_left _ rfl).trans hdvd) hev, ?_⟩
  obtain ⟨c, rfl⟩ := (Dvd.intro _ rfl : q * m' ∣ q * m' * mR).trans hdvd
  have e : q * m' * c = (c * q) * m' := by ring
  rw [e]
  intro R
  have hc0 : 0 < c * q := by
    have := R.setting.pos
    rcases Nat.eq_zero_or_pos (c * q) with h | h
    · rw [h, zero_mul] at this; omega
    · exact h
  have haq : ∀ i, a i ∣ c * q := fun i =>
    (Finset.dvd_prod_of_mem a (Finset.mem_univ i)).trans (Dvd.intro_left _ rfl)
  have hL : ∀ α i, ∃ σ ∈ logPluricanonicalSections (sS i) 2 ((c * q) * m') (B i),
      LiftsPow sS B jf BSf i m' (c * q) ((c * q) * m') σ (tG α) := by
    intro α i
    obtain ⟨σ, hσ, hσl⟩ := hlift i α
    obtain ⟨σ', hσ', h1, -, -⟩ := exists_pow_of_dvd hS hdim hSf i (ha0 i) (haq i) hc0 hσ
    exact ⟨σ', hσ', h1 _ hσl⟩
  choose σL hσLmem hσL using hL
  intro i x
  obtain ⟨σ, hσ, V, hxV, hgV, hcase⟩ := hgenx i x
  obtain ⟨σ', hσ', h1, h2, h3⟩ := exists_pow_of_dvd hS hdim hSf i (ha0 i) (haq i) hc0 hσ
  rcases hcase with hz | ⟨α, hα⟩
  · refine ⟨Pi.single i ⟨σ', hσ'⟩,
      single_mem_preadmissibleSections R i ⟨σ', hσ'⟩ (h3 hz), V, hxV, ?_⟩
    simpa using h2 V hgV
  · refine ⟨Function.update (fun i' => ⟨σL α i', hσLmem α i'⟩) i ⟨σ', hσ'⟩,
      mem_preadmissibleSections_of_liftsPow hdim (fun j => (hSf j)) Rf (htGadm α) R _
        fun i' => ?_, V, hxV, ?_⟩
    · by_cases h : i' = i
      · subst h
        simpa using h1 _ hα
      · simpa [h] using hσL α i'
    · simpa using h2 V hgV

end Proof_thm_mmp_surface_semiample_dlt_preadmissible_generation

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Preadmissible generation for semiample dlt surfaces.** Let `(S_i, B_i)`, `i ∈ I` finite, be
`ℚ`-factorial projective dlt pairs (`MMP.Fourfold.IsPair`, `MMP.Intersection.IsDltPair`) on complex
surfaces, with canonical divisors `K_i` such that `K_i + B_i` is semiample. Then there is `m₀ > 0`
such that for every positive even `m` divisible by `m₀` a residue restriction structure on the
collection in degree `m` exists, and for every such structure `R`, every `i` and every point
`x ∈ S_i`, there is a preadmissible section system `s ∈ preadmissibleSections R` whose `i`-th
section generates `𝒪_{S_i}(m(K_{S_i} + B_i))` on an open neighbourhood of `x`. -/
@[mmp "thm_mmp_surface_semiample_dlt_preadmissible_generation"]
public theorem exists_generatesOn_of_mem_preadmissibleSections
    {I : Type*} [Finite I] {S : I → Scheme.{0}} [∀ i, IsIntegral (S i)]
    [∀ i, CompactSpace (S i)] [∀ i, IsLocallyNoetherian (S i)] [∀ i, IsNormal (S i)]
    {sS : ∀ i, S i ⟶ Spec (.of ℂ)} (hS : ∀ i, Mori.IsProjectiveVariety ℂ (sS i))
    (hdim : ∀ i, topologicalKrullDim (S i) = 2) (hQ : ∀ i, IsQFactorial (sS i))
    {B : ∀ i, QDivisor (S i)} (hB : ∀ i, IsPair (sS i) (B i))
    (hdlt : ∀ i, MMP.Intersection.IsDltPair (sS i) (B i)) {K : ∀ i, Divisor (S i)}
    (hK : ∀ i, (K i).IsCanonicalDivisor (sS i) 2)
    (hsemi : ∀ i, QDivisor.IsRelativelySemiample (sS i) (Divisor.toQDivisor (K i) + B i)) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, 0 < m → m₀ ∣ m → Even m →
      Nonempty (ResidueRestriction sS B 2 m) ∧
      ∀ (R : ResidueRestriction sS B 2 m) (i : I) (x : S i),
        ∃ s ∈ preadmissibleSections R, ∃ V : (S i).Opens, x ∈ V ∧
          GeneratesOn (B i) m V
            ((s i : logPluricanonicalSections (sS i) 2 m (B i)) :
              RationalPluriForms (sS i) 2 m) :=
                by revert I S sS hS hdim hQ B hB hdlt K hK hsemi; first | exact Proof_thm_mmp_surface_semiample_dlt_preadmissible_generation.solution | exact Proof_thm_mmp_surface_semiample_dlt_preadmissible_generation.solution _ | exact Proof_thm_mmp_surface_semiample_dlt_preadmissible_generation.solution _ _ | exact Proof_thm_mmp_surface_semiample_dlt_preadmissible_generation.solution _ _ _ | exact Proof_thm_mmp_surface_semiample_dlt_preadmissible_generation.solution _ _ _ _

end MMP.Fourfold

