module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
import MMP.AlgebraicGeometry.MMP.BasepointFree.UniformRelativeFreeness
public import MMP.AlgebraicGeometry.MMP.Threefold.MinimalModel.RealKltLogTerminalModel
public import MMP.AlgebraicGeometry.MMP.Threefold.BigBoundaryModelFixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.Divisor.OrderPullback
import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
import MMP.AlgebraicGeometry.Divisor.PullbackExistence
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.MMP.MinimalModel.RealKltCompactification
import MMP.AlgebraicGeometry.Singularities.RealKltPolytope
import MMP.AlgebraicGeometry.Positivity.RelativeKodairaDecomposition
import MMP.AlgebraicGeometry.Positivity.RelativeEffectiveAdjoint
public import MMP.AlgebraicGeometry.MMP.Fourfold.StableBase
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.MMP.Threefold.LogMMP
import MMP.AlgebraicGeometry.MMP.Fourfold.RationalProgram
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.GenericFibreDegree
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefModelEquivalence
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationFiniteFibres
import StacksFrontier.AlgebraicGeometry.Curves.InseparableFactorizationChain
import MMP.AlgebraicGeometry.MMP.Fourfold.ExceptionalSupport
import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryAlgebra
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoMonomialValuation
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.GenericSurfacePlaces
import MMP.AlgebraicGeometry.Positivity.BigBirationalTransform
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.SpreadingOut.LocalEquations
public import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField

/-!
# Threefold log terminal models and fixed parts over an affine birational base

Let `f : S ⟶ T` be a projective birational morphism of normal complex varieties, with `T` affine
and `S` a `ℚ`-factorial threefold, and let `Θ` be an effective real klt boundary on `S`, with
canonical divisor `K` of `S`. Then:

* `(S, Θ)` has a `ℚ`-factorial klt log terminal model `φ : S ⤏ Y` over `T`: `Y` is projective
  over `T`, `φ` is a birational contraction over `T`, `(Y, φ_* Θ)` is real klt, `K_Y + φ_* Θ`
  is nef over `T`, and on a common resolution `p : W ⟶ S`, `q : W ⟶ Y` the comparison
  `p^*(K + Θ) - q^*(K_Y + φ_* Θ)` is effective, `q`-exceptional, and positive along the strict
  transform of every prime divisor of `S` contracted by `φ`;
* the divisorial stable base primes of `K + Θ` over `T` persist for all effective klt boundaries
  with the same support whose coefficients are close to those of `Θ`;
* there are a neighbourhood of `Θ` in its smallest rational affine hull and an integer `r > 0`
  such that for every effective klt `Φ` there and every `k > 0` with `k(K + Φ)/r` integral
  Cartier, `|k(K + Φ)|` is nonempty and every prime divisor in its fixed part over `T` is a
  divisorial stable base prime of `K + Θ` over `T`;
* if `Θ` is rational, the algebra `⊕_{m ≥ 0} H⁰(S, ⌊m(K + Θ)⌋)` is a finitely generated
  `Γ(T, 𝒪_T)`-algebra.

## Main results

* `MMP.Fourfold.IsRealKltPair.exists_logTerminalModel_of_isBirationalMorphism_of_isAffine`.

## Implementation notes

The last three assertions are spelled exactly as the clauses of
`MMP.Fourfold.BirationalFiniteGenerationProperty` for `d = 3`. Since `T` is affine, the relative
floor-section algebra `⊕_m f_* 𝒪_S(⌊m(K + Θ)⌋)` is a quasi-coherent `𝒪_T`-algebra which is
locally of finite type over `T` if and only if its algebra of global sections, the canonical ring
`MMP.Mori.Divisor.canonicalRing`, is finitely generated over `Γ(T, 𝒪_T)`; the latter is stated.
The common resolution of the log terminal model is a `MMP.Fourfold.IsLogComparisonResolution`,
so that the canonical divisor `K_Y` of `Y` is cut out by the same rational top form as `K`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Opposite MMP.Fourfold MMP.Mori

namespace Proof_thm_fourfold_birational_affine_threefold_f3

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The image of an effective divisor under a map of prime divisors is effective. -/
private theorem mapDomain_nonneg {α β M : Type*} [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] (v : α → β) {Θ : α →₀ M} (h : ∀ a, 0 ≤ Θ a) :
    0 ≤ Finsupp.mapDomain v Θ :=
  Finsupp.sum_nonneg' fun a => Finsupp.single_nonneg.mpr (h a)

/-! ### Birationality of a compactification -/

/-- If `i ≫ f̄ = f ≫ j` with `i`, `j` open immersions and `f` birational, then `f̄` is birational:
on a nonempty open `W` of the source where `f` is an open immersion, `f̄` restricted to the image
of `W` is the open immersion `W ⟶ T ⟶ T̄`. -/
private theorem isBirationalMorphism_of_comp_eq {S T Sb Tb : Scheme.{0}} [IrreducibleSpace Sb]
    [IrreducibleSpace Tb] [Nonempty S] {f : S ⟶ T} {fb : Sb ⟶ Tb} {i : S ⟶ Sb} {j : T ⟶ Tb}
    [IsOpenImmersion i] [IsOpenImmersion j] (h : i ≫ fb = f ≫ j)
    (hf : IsBirationalMorphism f) : IsBirationalMorphism fb := by
  obtain ⟨W, hW, hWo⟩ := hf.exists_isOpenImmersion
  have hc : (i.isoImage W).hom ≫ (i ''ᵁ W).ι = W.ι ≫ i := Scheme.Hom.isoImage_hom_ι _ _
  have e : (i ''ᵁ W).ι ≫ fb = (i.isoImage W).inv ≫ (W.ι ≫ f) ≫ j := by
    rw [← cancel_epi (i.isoImage W).hom, reassoc_of% hc, Iso.hom_inv_id_assoc]
    simp only [Category.assoc]
    rw [h]
  have : IsOpenImmersion ((i ''ᵁ W).ι ≫ fb) := by rw [e]; infer_instance
  obtain ⟨w, hw⟩ := hW
  exact MMP.Spreading.isBirationalMorphism_of_isOpenImmersion_ι_comp' fb (i ''ᵁ W)
    ⟨i w, w, hw, rfl⟩

/-- A dense open subvariety has the dimension of the ambient variety. -/
private theorem topologicalKrullDim_eq_of_isOpenImmersion {S Sb : Scheme.{0}}
    (sS : S ⟶ Spec (.of ℂ)) (sSb : Sb ⟶ Spec (.of ℂ)) [MMP.Mori.IsVariety ℂ sS]
    [MMP.Mori.IsVariety ℂ sSb] [Nonempty S] (i : S ⟶ Sb) [IsOpenImmersion i] :
    topologicalKrullDim Sb = topologicalKrullDim S := by
  have : IsIntegral S := AlgebraicGeometry.IsVariety.toIsIntegral (f := sS)
  have : IsIntegral Sb := AlgebraicGeometry.IsVariety.toIsIntegral (f := sSb)
  have : IsOpenImmersion ((⊤ : S.Opens).ι ≫ i) := inferInstance
  obtain ⟨x⟩ := ‹Nonempty S›
  exact MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sSb sS
    (MMP.Spreading.isBirationalMorphism_of_isOpenImmersion_ι_comp' i ⊤ ⟨x, trivial⟩)

open MMP.Positivity in
/-- A canonical divisor `K` of a dense open subvariety `i : S ⟶ S̄` of a normal variety extends to
a canonical divisor `K̄` of `S̄` with the same coefficient along the closure of every prime divisor
of `S`: write `K = div(ω)` for a rational top form `ω` on `S` and take `K̄ = div(ω̄)` for the form
`ω̄` on `S̄` with `i^* ω̄ = ω`, which exists since `i` induces an isomorphism of function fields.
-/
private theorem exists_isCanonicalDivisor_coeff_primeDivisorMap {S Sb : Scheme.{0}}
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S] [IsIntegral Sb]
    [IsLocallyNoetherian Sb] [IsNormal Sb] [CompactSpace Sb] {sSb : Sb ⟶ Spec (.of ℂ)}
    (hSb : IsNormalVariety ℂ sSb) (i : S ⟶ Sb) [IsOpenImmersion i] [Nonempty S] {n : ℕ}
    {K : Divisor S} (hK : K.IsCanonicalDivisor (i ≫ sSb) n) :
    ∃ Kb : Divisor Sb, Kb.IsCanonicalDivisor sSb n ∧
      ∀ P, Kb.coeff (OpenWeilRestriction.primeDivisorMap i P) = K.coeff P := by
  have : LocallyOfFiniteType sSb := hSb.1.toLocallyOfFiniteType
  have : MMP.Mori.IsVariety ℂ sSb := hSb.1
  have : QuasiCompact (i ≫ sSb) := inferInstance
  have hS : IsNormalVariety ℂ (i ≫ sSb) := ⟨(MMP.Mori.isVariety_iff ℂ _).mpr
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩
  have : MMP.Mori.IsVariety ℂ (i ≫ sSb) := hS.1
  have : LocallyOfFiniteType (i ≫ sSb) := inferInstance
  obtain ⟨x⟩ := ‹Nonempty S›
  have hib : IsBirationalMorphism i := by
    have : IsOpenImmersion ((⊤ : S.Opens).ι ≫ i) := inferInstance
    exact MMP.Spreading.isBirationalMorphism_of_isOpenImmersion_ι_comp' i ⊤ ⟨x, trivial⟩
  have := hib.isDominant
  have hbij := hib.functionFieldMap_bijective
  have hn : topologicalKrullDim Sb = n := by
    rw [topologicalKrullDim_eq_of_isOpenImmersion (i ≫ sSb) sSb i, hK.topologicalKrullDim_eq]
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sSb) hn
  obtain ⟨ω₁, hω₁0, hω₁⟩ := IsCanonicalDivisor.exists_ordForm_eq hS hK
  let := functionFieldAlgebra sSb
  let := functionFieldAlgebra (i ≫ sSb)
  let := functionFieldMapAlgebra i
  have := isScalarTower_functionFieldMap sSb i
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sSb i hbij hd
  obtain ⟨g, hg⟩ := hbij.2
    ((ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) 1).repr ω₁ ())
  let τ : RationalPluriForms sSb n 1 :=
    g • ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) 1 ()
  have hpull : pullbackRationalPluriForms sSb i τ = ω₁ := by
    change pullbackForms (K := Sb.functionField) (K' := S.functionField) 1 τ = ω₁
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    simp only [τ, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
    change functionFieldMap i g • _ = ω₁
    rw [hg]
    exact basis_unit_repr_smul _ ω₁
  have hτ0 : τ ≠ 0 := by
    intro h0
    apply hω₁0
    rw [← hpull, h0]
    change pullbackForms (K := Sb.functionField) (K' := S.functionField) 1 0 = 0
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    simp
  obtain ⟨Kb₀, hKb₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sSb hSb hn
  have hlin := linearlyEquivalent_divisorOfForm_zsmul hSb hKb₀ hτ0
  rw [one_zsmul] at hlin
  refine ⟨divisorOfForm τ, hKb₀.of_linearlyEquivalent hlin, fun P => ?_⟩
  rw [coeff_divisorOfForm, ← hω₁ P, ← hpull]
  exact (ordForm_pullbackRationalPluriForms_of_isIso i hbij hd P _
    (OpenWeilRestriction.genericPoint_primeDivisorMap i P).symm τ).symm

/-- The generic point of the closure of a prime divisor of an open subscheme, read through the
abbreviation `MMP.Mori.PrimeDivisor.genericPoint`. -/
private theorem genericPoint_primeDivisorMap' {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j]
    (W : MMP.Mori.PrimeDivisor X) :
    MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap j W) =
      j W.genericPoint :=
  OpenWeilRestriction.genericPoint_primeDivisorMap j W

/-! ### Global sections over an affine birational base -/

section Sections

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

/-- A separated birational morphism of integral schemes does not map the generic point of a prime
divisor to the generic point of the target. -/
private theorem apply_genericPoint_ne_genericPoint {f : X ⟶ Y} [IsSeparated f]
    (hf : IsBirationalMorphism f) (P : MMP.Mori.PrimeDivisor X) :
    f P.genericPoint ≠ genericPoint Y := by
  intro h
  have := hf.isDominant
  have h₂ : f (genericPoint X) = genericPoint Y :=
    MMP.Positivity.map_genericPoint_eq_of_isDominant f
  have : ValuationRing (Y.presheaf.stalk (genericPoint Y)) :=
    inferInstanceAs (ValuationRing Y.functionField)
  have hP : P.genericPoint = genericPoint X :=
    MMP.Fourfold.eq_of_map_eq_of_valuationRing hf.functionFieldMap_bijective h h₂
  have h1 := P.coheight_genericPoint
  rw [hP] at h1
  have : IsMax (genericPoint X) := fun y _ => genericPoint_specializes y
  rw [Order.coheight_eq_zero.mpr this] at h1
  simp at h1

/-- On an integral affine scheme, finitely many points other than the generic point lie outside
a basic open containing the generic point. -/
private theorem exists_basicOpen_genericPoint_mem [IsAffine Y] (s : Finset Y)
    (hs : ∀ y ∈ s, y ≠ genericPoint Y) :
    ∃ a : Γ(Y, ⊤), genericPoint Y ∈ Y.basicOpen a ∧ ∀ y ∈ s, y ∉ Y.basicOpen a := by
  let Z : Set Y := ⋃ y ∈ s, closure {y}
  have hZ : IsClosed Z := isClosed_biUnion_finset fun y _ => isClosed_closure
  have hηZ : genericPoint Y ∉ Z := by
    simp only [Z, Set.mem_iUnion, not_exists]
    intro y hy hη
    exact hs y hy ((specializes_iff_mem_closure.mpr hη).antisymm
      (genericPoint_specializes y)).eq
  let V : Y.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  obtain ⟨a, haV, ha⟩ := (isAffineOpen_top Y).exists_basicOpen_le
    (V := V) ⟨genericPoint Y, hηZ⟩ trivial
  refine ⟨a, ha, fun y hy hya => haV hya ?_⟩
  exact Set.mem_biUnion hy (subset_closure rfl)

variable [IsLocallyNoetherian X] [IsNormal X]

/-- A nonzero, non-unit element of the local ring along a prime divisor has order at least one
there. -/
private theorem ordGE_one_toComponent (E : MMP.Mori.PrimeDivisor X) {a : E.localRing}
    (ha : a ∈ IsLocalRing.maximalIdeal E.localRing) :
    E.OrdGE 1 (E.toComponent.hom a) := by
  have := E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at ha
  obtain ⟨c, rfl⟩ := ha
  have h1 : E.OrdGE 1 (E.toComponent.hom ϖ) :=
    Or.inr (E.valuation_toComponent_of_irreducible hϖ).ge
  have h0 : E.OrdGE 0 (E.toComponent.hom c) := by
    by_cases hc : c = 0
    · rw [hc, map_zero]; exact MMP.Mori.PrimeDivisor.OrdGE.zero 0
    · exact Or.inr (by rw [WithZero.exp_zero]; exact E.one_le_valuation_toComponent hc)
  have := h0.mul h1
  rwa [zero_add, ← map_mul] at this

/-- Over an integral affine base, every Weil divisor on the source of a separated birational
morphism has a nonzero global section: a high power of the pull-back of a regular function
vanishing at the images of the generic points of its support. -/
private theorem exists_ne_zero_mem_divisorialSubmodule_top [IsAffine Y] {f : X ⟶ Y}
    [IsSeparated f] (hf : IsBirationalMorphism f) (D : Divisor X) :
    ∃ φ ∈ D.divisorialSubmodule ⊤, φ ≠ 0 := by
  classical
  obtain ⟨a, haη, has⟩ := exists_basicOpen_genericPoint_mem (D.support.image fun P =>
    f P.genericPoint) (by
      simp only [Finset.mem_image]
      rintro _ ⟨P, -, rfl⟩
      exact apply_genericPoint_ne_genericPoint hf P)
  have := hf.isDominant
  let b : Γ(X, ⊤) := f.appTop a
  have hb : ∀ x : X, x ∈ X.basicOpen b ↔ f x ∈ Y.basicOpen a := fun x => by
    rw [← Scheme.preimage_basicOpen_top]; rfl
  let N : ℕ := ∑ P ∈ D.support, (D.coeff P).natAbs
  refine ⟨algebraMap Γ(X, ⊤) _ (b ^ N), fun E hE => ?_, fun h0 => ?_⟩
  · by_cases hED : E ∈ D.support
    · have hgerm : (algebraMap Γ(X, ⊤) ((rationalFunctionsPresheaf X).obj (op ⊤)) (b ^ N))
          ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩ =
          E.toComponent.hom (X.presheaf.germ ⊤ E.genericPoint trivial (b ^ N)) :=
        (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf
          (show E.genericPoint ∈ (⊤ : X.Opens) from trivial) E.specializes_genericPoint
          (b ^ N)).symm
      rw [hgerm]
      have hmem : X.presheaf.germ ⊤ E.genericPoint trivial b ∈
          IsLocalRing.maximalIdeal E.localRing := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact has _ (Finset.mem_image_of_mem _ hED)
          ((hb _).mp ((X.mem_basicOpen b _ trivial).mpr hu))
      have h1 := (ordGE_one_toComponent E hmem).pow N
      rw [← map_pow, ← map_pow] at h1
      refine h1.mono ?_
      have h2 : -D.coeff E ≤ ((D.coeff E).natAbs : ℤ) := by
        rw [Int.natCast_natAbs]; exact neg_le_abs _
      have h3 : (D.coeff E).natAbs ≤ N :=
        Finset.single_le_sum (f := fun P => (D.coeff P).natAbs) (fun _ _ => Nat.zero_le _) hED
      have h4 : ((D.coeff E).natAbs : ℤ) ≤ N := by exact_mod_cast h3
      linarith
    · have h := MMP.Mori.Divisor.isDivisorialSection_algebraMap (D := (0 : Divisor X)) le_rfl
        (U := ⊤) (b ^ N) E hE
      have hDE : D.coeff E = 0 := Finsupp.notMem_support_iff.mp hED
      have h0 : (0 : Divisor X).coeff E = 0 := rfl
      rw [hDE]
      rw [h0] at h
      exact h
  · obtain ⟨Z, -⟩ := MMP.Mori.exists_mem_irreducibleComponents (genericPoint X)
    have hZU : componentGenericPoint X Z ∈ (⊤ : X.Opens) := trivial
    have h := congrFun h0 ⟨Z, hZU⟩
    change X.presheaf.germ ⊤ _ hZU (b ^ N) = 0 at h
    have hZ1 : Z.1 = Set.univ := by
      have h' : Z.1 ∈ ({Set.univ} : Set (Set X)) :=
        (irreducibleComponents_eq_singleton (X := X)) ▸ Z.2
      exact h'
    have hgp := isGenericPoint_componentGenericPoint X Z
    rw [hZ1] at hgp
    have hZη : componentGenericPoint X Z = genericPoint X := hgp.eq (genericPoint_spec X)
    have hmem : componentGenericPoint X Z ∈ X.basicOpen b := by
      rw [hb, hZη, MMP.Positivity.map_genericPoint_eq_of_isDominant f]
      exact haη
    have hu := ((X.mem_basicOpen b _ hZU).mp hmem).pow N
    rw [← map_pow, h] at hu
    exact not_isUnit_zero hu

end Sections

/-! ### Rational functions of an integral scheme -/

section FunctionField

variable {X : Scheme.{0}} [IsIntegral X]

/-- An integral scheme has exactly one irreducible component. -/
private theorem irreducibleComponents_eq (Z Z' : irreducibleComponents X) : Z = Z' := by
  have h : ∀ Z : irreducibleComponents X, (Z : Set X) = Set.univ := fun Z => by
    have h1 : (Z : Set X) ∈ ({Set.univ} : Set (Set X)) := by
      rw [← irreducibleComponents_eq_singleton]; exact Z.2
    exact h1
  exact Subtype.ext ((h Z).trans (h Z').symm)

/-- Generization from the generic point of a component to the function field. -/
private noncomputable abbrev toFF (Z : irreducibleComponents X) :
    X.presheaf.stalk (componentGenericPoint X Z) →+* X.functionField :=
  (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial :
    genericPoint X ⤳ componentGenericPoint X Z)).hom

private theorem stalkSpecializes_bijective_of_eq {x y : X} (h : x ⤳ y) (e : x = y) :
    Function.Bijective (X.presheaf.stalkSpecializes h).hom := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact ⟨fun _ _ h => h, fun a => ⟨a, rfl⟩⟩

private theorem toFF_bijective (Z : irreducibleComponents X) : Function.Bijective (toFF Z) :=
  stalkSpecializes_bijective_of_eq _ (MMP.Fourfold.componentGenericPoint_eq_genericPoint Z).symm

/-- The value in the function field of a section of `𝒦_X` over a nonempty open. -/
private noncomputable def sectionValue {W : X.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ W}) :
    (rationalFunctionsPresheaf X).obj (op W) →+* X.functionField :=
  (toFF Z.1).comp (Pi.evalRingHom _ Z)

private theorem sectionValue_eq {W : X.Opens}
    (Z Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ W}) :
    sectionValue Z = sectionValue Z' := by
  obtain rfl : Z = Z' := Subtype.ext (irreducibleComponents_eq _ _)
  rfl

private theorem sectionValue_bijective {W : X.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ W}) :
    Function.Bijective (sectionValue Z) := by
  refine ⟨fun φ ψ h => ?_, fun t => ?_⟩
  · have h' : φ Z = ψ Z := (toFF_bijective Z.1).1 h
    funext Z'
    obtain rfl : Z' = Z := Subtype.ext (irreducibleComponents_eq _ _)
    exact h'
  · obtain ⟨s, hs⟩ := (toFF_bijective Z.1).2 t
    refine ⟨fun Z' => ?_, ?_⟩
    · obtain ⟨Z', hZ'⟩ := Z'
      obtain rfl : Z' = Z.1 := irreducibleComponents_eq _ _
      exact s
    · exact hs

variable [IsLocallyNoetherian X] [IsNormal X]

/-- `v_E(s) ≥ n` read in the function field. -/
private theorem ordGE_iff (E : MMP.Mori.PrimeDivisor X) (n : ℤ)
    (s : X.presheaf.stalk (componentGenericPoint X E.component)) :
    E.OrdGE n s ↔ s = 0 ∨ n ≤ X.ord (toFF E.component s) E.genericPoint := by
  classical
  by_cases hs : s = 0
  · exact ⟨fun _ => Or.inl hs, fun _ => Or.inl hs⟩
  have hfield := MMP.Mori.RationalFunctions.isField_stalk (X := X) E.component
  obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hs
  let u : (X.presheaf.stalk (componentGenericPoint X E.component))ˣ := ⟨s, b, hb, by
    rw [mul_comm]; exact hb⟩
  let φ : (MMP.Mori.RationalFunctions X)ˣ :=
    (MMP.Mori.RationalFunctions.unitsEquiv (X := X)).symm (Function.update 1 E.component u)
  have hφ : (φ : MMP.Mori.RationalFunctions X) E.component = s := by
    simp [φ, u, MMP.Mori.RationalFunctions.unitsEquiv]
  have h1 := E.valuation_component φ
  have h2 := MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord E φ
  have h3 : MMP.Threefold.Mori.Helpers.evalFF E.component (φ : MMP.Mori.RationalFunctions X) =
      toFF E.component s := by
    rw [← hφ]; rfl
  rw [hφ] at h1
  rw [h3] at h2
  rw [MMP.Mori.PrimeDivisor.OrdGE, h1, ← h2, WithZero.exp_le_exp]

/-- Sections of `𝒪_X(D)` over `W`, read in the function field. -/
private theorem isDivisorialSection_iff {D : MMP.Mori.Divisor X} {W : X.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ W})
    (φ : (rationalFunctionsPresheaf X).obj (op W)) :
    D.IsDivisorialSection W φ ↔ ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ W).Nonempty →
      sectionValue Z φ = 0 ∨ -D.coeff E ≤ X.ord (sectionValue Z φ) E.genericPoint := by
  refine forall_congr' fun E => ?_
  refine ⟨fun h hE => ?_, fun h hE => ?_⟩
  · rw [sectionValue_eq Z ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩]
    rcases (ordGE_iff E _ _).mp (h hE) with h0 | h0
    · left
      exact (congrArg (toFF E.component) h0).trans (map_zero _)
    · exact Or.inr h0
  · rw [sectionValue_eq Z ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩] at h
    refine (ordGE_iff E _ _).mpr ?_
    rcases h hE with h0 | h0
    · left
      exact (toFF_bijective E.component).1 (h0.trans (map_zero _).symm)
    · exact Or.inr h0

end FunctionField

/-! ### Transfer along an open immersion -/

section OpenImmersion

variable {X : Scheme.{0}} [IsIntegral X]

/-- An index of the unique irreducible component, as a component meeting a nonempty open. -/
private noncomputable def componentIndex (W : X.Opens) [Nonempty W] :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ W} :=
  ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩, by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]
    obtain ⟨⟨x, hx⟩⟩ := ‹Nonempty W›
    exact ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr ⟨x, trivial, hx⟩⟩

/-- The value in the function field of a rational function of an integral scheme. -/
private theorem evalFF_bijective (Z : irreducibleComponents X) :
    Function.Bijective (MMP.Threefold.Mori.Helpers.evalFF Z :
      MMP.Mori.RationalFunctions X →+* X.functionField) := by
  refine ⟨fun φ ψ h => ?_, fun t => ?_⟩
  · have h' : φ Z = ψ Z := (toFF_bijective Z).1 h
    funext Z'
    obtain rfl : Z' = Z := irreducibleComponents_eq _ _
    exact h'
  · obtain ⟨s, hs⟩ := (toFF_bijective Z).2 t
    refine ⟨fun Z' => ?_, ?_⟩
    · obtain rfl : Z' = Z := irreducibleComponents_eq _ _
      exact s
    · exact hs

variable {S Sb : Scheme.{0}} [IsIntegral S] [IsIntegral Sb] [IsLocallyNoetherian S]
  [IsLocallyNoetherian Sb] [IsNormal S] [IsNormal Sb] (i : S ⟶ Sb) [IsOpenImmersion i]
  [IsDominant i]

private theorem functionFieldMap_bijective_of_isOpenImmersion' :
    Function.Bijective (functionFieldMap i) :=
  MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion i ⊤ ⟨genericPoint S, trivial⟩

private theorem ord_functionFieldMap_primeDivisorMap (P : MMP.Mori.PrimeDivisor S)
    (g : Sb.functionField) :
    S.ord (functionFieldMap i g) P.genericPoint =
      Sb.ord g (OpenWeilRestriction.primeDivisorMap i P).genericPoint :=
  MMP.Positivity.ord_functionFieldMap_of_isIso i P _
    (OpenWeilRestriction.genericPoint_primeDivisorMap i P).symm g

private theorem exists_primeDivisorMap_eq_of_nonempty (W : S.Opens)
    (E : MMP.Mori.PrimeDivisor Sb) (hE : (E.support ∩ (i ''ᵁ W : Set Sb)).Nonempty) :
    ∃ P : MMP.Mori.PrimeDivisor S, OpenWeilRestriction.primeDivisorMap i P = E ∧
      (P.support ∩ (W : Set S)).Nonempty := by
  have hgp : E.genericPoint ∈ i ''ᵁ W := (MMP.Mori.PrimeDivisor.genericPoint_mem_iff E _).mpr hE
  obtain ⟨x, hxW, hx⟩ := hgp
  obtain ⟨P, hP⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff i E).mpr ⟨x, hx⟩
  refine ⟨P, hP, (MMP.Mori.PrimeDivisor.genericPoint_mem_iff P W).mp ?_⟩
  have h1 : i P.genericPoint = i x := by
    rw [← OpenWeilRestriction.genericPoint_primeDivisorMap, hP]
    exact hx.symm
  have h2 : P.genericPoint = x := i.isOpenEmbedding.injective h1
  show P.genericPoint ∈ W
  rw [h2]
  exact hxW

private theorem primeDivisorMap_support_inter_nonempty (W : S.Opens)
    (P : MMP.Mori.PrimeDivisor S) (hP : (P.support ∩ (W : Set S)).Nonempty) :
    ((OpenWeilRestriction.primeDivisorMap i P).support ∩ (i ''ᵁ W : Set Sb)).Nonempty := by
  refine (MMP.Mori.PrimeDivisor.genericPoint_mem_iff (OpenWeilRestriction.primeDivisorMap i P) _).mp ?_
  rw [genericPoint_primeDivisorMap']
  exact ⟨_, (P.genericPoint_mem_iff W).mpr hP, rfl⟩

/-- Sections of `𝒪(D)` correspond along an open immersion, when the coefficients of the divisors
agree along the prime divisors meeting the open set. -/
private theorem mem_divisorialSubmodule_iff_of_isOpenImmersion (W : S.Opens) (Wb : Sb.Opens)
    (hW : Wb = i ''ᵁ W)
    (Zb : {Z : irreducibleComponents Sb // componentGenericPoint Sb Z ∈ Wb})
    (Z : {Z : irreducibleComponents S // componentGenericPoint S Z ∈ W})
    {Db : MMP.Mori.Divisor Sb} {D : MMP.Mori.Divisor S}
    (hD : ∀ P : MMP.Mori.PrimeDivisor S, (P.support ∩ (W : Set S)).Nonempty →
      Db.coeff (OpenWeilRestriction.primeDivisorMap i P) = D.coeff P)
    (φb : (rationalFunctionsPresheaf Sb).obj (op Wb))
    (φ : (rationalFunctionsPresheaf S).obj (op W))
    (hφ : sectionValue Z φ = functionFieldMap i (sectionValue Zb φb)) :
    φb ∈ Db.divisorialSubmodule Wb ↔ φ ∈ D.divisorialSubmodule W := by
  subst hW
  change Db.IsDivisorialSection _ φb ↔ D.IsDivisorialSection _ φ
  rw [isDivisorialSection_iff Zb, isDivisorialSection_iff Z, hφ]
  have hinj := (functionFieldMap_bijective_of_isOpenImmersion' i).1
  refine ⟨fun h P hP => ?_, fun h E hE => ?_⟩
  · rcases h _ (primeDivisorMap_support_inter_nonempty i W P hP) with h0 | h0
    · left; rw [h0, map_zero]
    · right; rwa [ord_functionFieldMap_primeDivisorMap, ← hD P hP]
  · obtain ⟨P, rfl, hP⟩ := exists_primeDivisorMap_eq_of_nonempty i W E hE
    rcases h P hP with h0 | h0
    · left; exact hinj (h0.trans (map_zero _).symm)
    · right; rwa [ord_functionFieldMap_primeDivisorMap, ← hD P hP] at h0

/-- The ring isomorphism `K(S̄) ≅ K(S)` of rational functions along an open immersion. -/
private noncomputable def rationalFunctionsEquiv :
    MMP.Mori.RationalFunctions Sb ≃+* MMP.Mori.RationalFunctions S :=
  (RingEquiv.ofBijective _ (evalFF_bijective (componentIndex (⊤ : Sb.Opens)).1)).trans
    ((RingEquiv.ofBijective _ (functionFieldMap_bijective_of_isOpenImmersion' i)).trans
      (RingEquiv.ofBijective _ (evalFF_bijective (componentIndex (⊤ : S.Opens)).1)).symm)

private theorem evalFF_rationalFunctionsEquiv (Z : irreducibleComponents S)
    (Zb : irreducibleComponents Sb) (g : MMP.Mori.RationalFunctions Sb) :
    MMP.Threefold.Mori.Helpers.evalFF Z (rationalFunctionsEquiv i g) =
      functionFieldMap i (MMP.Threefold.Mori.Helpers.evalFF Zb g) := by
  rw [irreducibleComponents_eq Z (componentIndex (⊤ : S.Opens)).1,
    irreducibleComponents_eq Zb (componentIndex (⊤ : Sb.Opens)).1]
  exact (RingEquiv.ofBijective _ (evalFF_bijective (componentIndex (⊤ : S.Opens)).1)).apply_symm_apply _

private theorem ord_rationalFunctionsEquiv (P : MMP.Mori.PrimeDivisor S)
    (g : (MMP.Mori.RationalFunctions Sb)ˣ) :
    P.ord (Units.map (rationalFunctionsEquiv i).toMonoidHom g) =
      MMP.Mori.PrimeDivisor.ord (OpenWeilRestriction.primeDivisorMap i P) g := by
  rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
  change S.ord (MMP.Threefold.Mori.Helpers.evalFF _ (rationalFunctionsEquiv i g)) _ = _
  rw [evalFF_rationalFunctionsEquiv i _
      (MMP.Mori.PrimeDivisor.component (OpenWeilRestriction.primeDivisorMap i P)),
    ord_functionFieldMap_primeDivisorMap]

end OpenImmersion

/-! ### Cartier divisors with a prescribed Weil divisor -/

section WeilToCartier

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

open MMP.Intersection in
/-- On an integral locally Noetherian scheme, a point of coheight zero lies in the support of no
Cartier divisor. -/
private theorem notMem_cartierSupport_of_coheight_eq_zero (A : X.CartierDivisor) {x : X}
    (hx : Order.coheight x = 0) : x ∉ cartierSupport A := by
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le (by simp [hx])
  have : IsArtinianRing (X.presheaf.stalk x) := isArtinianRing_iff_krullDimLE_zero.mpr this
  exact notMem_cartierSupport_of_isArtinianRing A x

open MMP.Intersection in
/-- Every Cartier divisor on a Noetherian integral scheme has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier (A : X.CartierDivisor) :
    ∃ w : MMP.Mori.Divisor X, IsWeilDivisorOfCartier A w := by
  haveI : IsNoetherian X := {}
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

/-- The order at a point of coheight one of an element of the local ring is its order. -/
private theorem ord_algebraMap_stalk {η : X} (hη : Order.coheight η = 1)
    {r : X.presheaf.stalk η} (hr : r ≠ 0) :
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk η) := krullDimLE_of_coheight_le hη.le
    X.ord (algebraMap (X.presheaf.stalk η) X.functionField r) η = (Ring.ord _ r).toNat := by
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk η) := krullDimLE_of_coheight_le hη.le
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hη]
  simp only [Scheme.ordHom]
  rw [Ring.ordFrac_eq_ord _ hr]
  have hnz : r ∈ nonZeroDivisors (X.presheaf.stalk η) := mem_nonZeroDivisors_of_ne_zero hr
  simp only [Ring.ordMonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_pos hnz]
  rw [← ENat.coe_toNat (Ring.ord_ne_top hnz)]
  simp

open MMP.Intersection MMP.CartierDivisorSheaf in
/-- The principal Cartier divisor of a rational function has the principal Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier_principalDivisor (φ : (RationalFunctions X)ˣ) :
    ∃ A : X.CartierDivisor, IsWeilDivisorOfCartier A (MMP.Mori.principalDivisor φ) := by
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
  have hsub : ∀ W : irreducibleComponents X, W = Z₀ := fun W => by
    have hmem : ∀ W : irreducibleComponents X, (W : Set X) = Set.univ := fun W => by
      have h1 : (W : Set X) ∈ ({Set.univ} : Set (Set X)) := by
        rw [← irreducibleComponents_eq_singleton]; exact W.2
      exact h1
    exact Subtype.ext ((hmem W).trans (hmem Z₀).symm)
  set r₀ := MMP.Threefold.Mori.Helpers.evalFF Z₀ (φ : RationalFunctions X)
  have hr0 : r₀ ≠ 0 := (φ.isUnit.map _).ne_zero
  have hordφ : ∀ Q : MMP.Mori.PrimeDivisor X, Q.ord φ = Scheme.ord r₀ Q.genericPoint := by
    intro Q
    rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hsub Q.component]
  set c : (X.totalQuotientSheaf.obj.obj (Opposite.op ⊤))ˣ :=
    Units.map (ofFunctionField (X := X) ⊤).toMonoidHom (Units.mk0 r₀ hr0)
  refine ⟨principalDivisor c, fun Q => ?_⟩
  rw [MMP.Mori.coeff_principalDivisor, hordφ]
  obtain ⟨⟨a, b⟩, hab⟩ :=
    IsLocalization.surj (nonZeroDivisors (X.presheaf.stalk Q.genericPoint)) r₀
  have hbK : algebraMap _ X.functionField (b : X.presheaf.stalk Q.genericPoint) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hb0 : (b : X.presheaf.stalk Q.genericPoint) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    exact mul_ne_zero hr0 hbK hab
  have hloc : IsLocalEquationAt (principalDivisor c) Q.genericPoint
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
  convert hO using 1
  have h1 := Scheme.ord_mul (x := Q.genericPoint) hr0 hbK
  rw [hab, ord_algebraMap_stalk Q.coheight_genericPoint ha0,
    ord_algebraMap_stalk Q.coheight_genericPoint hb0] at h1
  change _ = ((Ring.ord _ a).toNat : ℤ) -
    ((Ring.ord _ (b : X.presheaf.stalk Q.genericPoint)).toNat : ℤ)
  linarith

/-- **A Cartier Weil divisor is the Weil divisor of a Cartier divisor.** The divisorial sheaf of
`D` is `𝒪_X(C)` for a Cartier divisor `C`, whose Weil divisor is linearly equivalent to `D`; a
principal correction gives Weil divisor exactly `D`. -/
private theorem exists_isWeilDivisorOfCartier_of_isCartier {D : Divisor X} (hD : D.IsCartier) :
    ∃ A : X.CartierDivisor, MMP.Intersection.IsWeilDivisorOfCartier A D := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  obtain ⟨C, ⟨eC⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  obtain ⟨w, hw⟩ := exists_isWeilDivisorOfCartier C
  obtain ⟨ew⟩ := hw.nonempty_sheaf_iso_divisorialSheaf
  obtain ⟨ψ, hψ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso (eC ≪≫ ew)
  obtain ⟨P, hP⟩ := exists_isWeilDivisorOfCartier_principalDivisor ψ
  refine ⟨C + P, fun Q => ?_⟩
  have hDw : D = w + MMP.Mori.principalDivisor ψ := by rw [← hψ]; abel
  rw [hDw, DivisorWithCoeffs.coeff_add]
  exact (hw Q).add (hP Q)

end WeilToCartier

/-! ### Stable base loci along an open immersion over an open immersion of bases -/

section StableBase

private theorem coeff_add_sum_smul_principalDivisor {X : Scheme.{0}} [IsLocallyNoetherian X]
    [CompactSpace X] [IsNormal X] (D : MMP.Mori.RDivisor X)
    {s : ℕ} (a : Fin s → ℝ) (g : Fin s → (MMP.Mori.RationalFunctions X)ˣ)
    (P : MMP.Mori.PrimeDivisor X) :
    (D + ∑ k, a k • Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero
      (MMP.Mori.principalDivisor (g k))).coeff P = D.coeff P + ∑ k, a k * (P.ord (g k) : ℝ) := by
  have h : ∀ k, (MMP.Mori.principalDivisor (g k)) P = P.ord (g k) := fun k =>
    MMP.Mori.coeff_principalDivisor (g k) P
  simp only [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, h]

variable {S Sb T Tb : Scheme.{0}} [IsIntegral S] [IsIntegral Sb] [IsLocallyNoetherian S]
  [IsLocallyNoetherian Sb] [IsNormal S] [IsNormal Sb] [CompactSpace S] [CompactSpace Sb]
  {i : S ⟶ Sb} [IsOpenImmersion i] [IsDominant i] {f : S ⟶ T} {fb : Sb ⟶ Tb} {j : T ⟶ Tb}
  [IsOpenImmersion j]

/-- Divisorial stable base primes correspond along a pull-back square of open immersions, when the
divisors have the same coefficients along the primes of the open part. -/
private theorem isInRelativeDivisorialStableBase_primeDivisorMap_iff
    (H : IsPullback i f fb j) {D : MMP.Mori.RDivisor S} {Db : MMP.Mori.RDivisor Sb}
    (hD : ∀ P, Db.coeff (OpenWeilRestriction.primeDivisorMap i P) = D.coeff P)
    (G : MMP.Mori.PrimeDivisor S) :
    MMP.Fourfold.IsInRelativeDivisorialStableBase f D G ↔
      MMP.Fourfold.IsInRelativeDivisorialStableBase fb Db
        (OpenWeilRestriction.primeDivisorMap i G) := by
  let ρ := rationalFunctionsEquiv i
  have hpt : ∀ x : S, fb (i x) = j (f x) := fun x => by
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
  have hcoeff : ∀ {s : ℕ} (a : Fin s → ℝ) (g : Fin s → (MMP.Mori.RationalFunctions Sb)ˣ)
      (P : MMP.Mori.PrimeDivisor S),
      (Db + ∑ k, a k • Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero
        (MMP.Mori.principalDivisor (g k))).coeff (OpenWeilRestriction.primeDivisorMap i P) =
      (D + ∑ k, a k • Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero
        (MMP.Mori.principalDivisor (Units.map ρ.toMonoidHom (g k)))).coeff P := by
    intro s a g P
    rw [coeff_add_sum_smul_principalDivisor, coeff_add_sum_smul_principalDivisor, hD]
    simp only [ρ, ord_rationalFunctionsEquiv]
  have hρ : ∀ g : (MMP.Mori.RationalFunctions S)ˣ,
      Units.map ρ.toMonoidHom (Units.map ρ.symm.toMonoidHom g) = g := fun g => by
    ext; simp
  constructor
  · intro h U hU s a g hL
    have hU' : f G.genericPoint ∈ j ⁻¹ᵁ U := by
      show j (f G.genericPoint) ∈ U
      rw [← hpt, ← OpenWeilRestriction.genericPoint_primeDivisorMap]
      exact hU
    rw [hcoeff]
    refine h (j ⁻¹ᵁ U) hU' s a (fun k => Units.map ρ.toMonoidHom (g k)) fun P hP => ?_
    rw [← hcoeff]
    refine hL _ ((MMP.Mori.PrimeDivisor.genericPoint_mem_iff
      (OpenWeilRestriction.primeDivisorMap i P) _).mp ?_)
    rw [genericPoint_primeDivisorMap']
    show fb (i P.genericPoint) ∈ U
    rw [hpt]
    exact (P.genericPoint_mem_iff (f ⁻¹ᵁ (j ⁻¹ᵁ U))).mpr hP
  · intro h U hU s a g hL
    have hU' : fb (OpenWeilRestriction.primeDivisorMap i G).genericPoint ∈ j ''ᵁ U := by
      rw [OpenWeilRestriction.genericPoint_primeDivisorMap, hpt]
      exact ⟨_, hU, rfl⟩
    have himg : fb ⁻¹ᵁ j ''ᵁ U = i ''ᵁ f ⁻¹ᵁ U :=
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H.flip U).symm
    have := h (j ''ᵁ U) hU' s a (fun k => Units.map ρ.symm.toMonoidHom (g k)) fun E hE => by
      rw [himg] at hE
      obtain ⟨P, rfl, hP⟩ := exists_primeDivisorMap_eq_of_nonempty i _ E hE
      rw [hcoeff]
      simp only [hρ]
      exact hL P hP
    rw [hcoeff] at this
    simpa only [hρ] using this

end StableBase

/-! ### Germs in the function field -/

section Germs

private theorem sectionValue_toRationalFunctionsPresheaf {X : Scheme.{0}} [IsIntegral X]
    {W : X.Opens} [Nonempty W]
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ W}) (s : Γ(X, W)) :
    sectionValue Z (((toRationalFunctionsPresheaf X).app (op W)).hom s) =
      X.germToFunctionField W s := by
  change (X.presheaf.stalkSpecializes _).hom (X.presheaf.germ W _ Z.2 s) = _
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply]

private theorem functionFieldMap_germToFunctionField {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (g : Y ⟶ X) [IsDominant g] (U : X.Opens) [Nonempty U] [Nonempty (g ⁻¹ᵁ U)]
    (a : Γ(X, U)) :
    functionFieldMap g (X.germToFunctionField U a) =
      Y.germToFunctionField (g ⁻¹ᵁ U) ((g.app U).hom a) := by
  have hY : genericPoint Y ∈ g ⁻¹ᵁ U := by
    obtain ⟨⟨y, hy⟩⟩ := ‹Nonempty (g ⁻¹ᵁ U)›
    exact ((genericPoint_spec Y).mem_open_set_iff (g ⁻¹ᵁ U).isOpen).mpr ⟨y, trivial, hy⟩
  have hx : g (genericPoint Y) ∈ U := hY
  have h1 := MMP.Mori.functionFieldMap_algebraMap_stalk g (genericPoint Y)
    (X.presheaf.germ U (g (genericPoint Y)) hx a)
  rw [Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := U) hx a] at h1
  erw [Scheme.Hom.germ_stalkMap_apply g U (genericPoint Y) hx a] at h1
  rw [Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) (U := g ⁻¹ᵁ U) hY _] at h1
  exact h1

private theorem germToFunctionField_app_congr {X Y : Scheme.{0}} [IsIntegral X] {g₁ g₂ : X ⟶ Y}
    (h : g₁ = g₂) (U : Y.Opens) [Nonempty (g₁ ⁻¹ᵁ U)] [Nonempty (g₂ ⁻¹ᵁ U)] (a : Γ(Y, U)) :
    X.germToFunctionField (g₁ ⁻¹ᵁ U) ((g₁.app U).hom a) =
      X.germToFunctionField (g₂ ⁻¹ᵁ U) ((g₂.app U).hom a) := by
  subst h
  rfl

private theorem exists_germToFunctionField_app_top_eq {X Y : Scheme.{0}} [IsIntegral X]
    (g : X ⟶ Y) {V : Y.Opens} (hV : V = ⊤) [Nonempty (g ⁻¹ᵁ V)] [Nonempty (g ⁻¹ᵁ (⊤ : Y.Opens))]
    (c : Γ(Y, V)) : ∃ b : Γ(Y, ⊤),
      X.germToFunctionField (g ⁻¹ᵁ V) ((g.app V).hom c) =
        X.germToFunctionField (g ⁻¹ᵁ ⊤) ((g.app ⊤).hom b) := by
  subst hV
  exact ⟨c, rfl⟩

private theorem exists_germToFunctionField_app_eq_top {X Y : Scheme.{0}} [IsIntegral X]
    (g : X ⟶ Y) {V : Y.Opens} (hV : V = ⊤) [Nonempty (g ⁻¹ᵁ V)] [Nonempty (g ⁻¹ᵁ (⊤ : Y.Opens))]
    (b : Γ(Y, ⊤)) : ∃ c : Γ(Y, V),
      X.germToFunctionField (g ⁻¹ᵁ V) ((g.app V).hom c) =
        X.germToFunctionField (g ⁻¹ᵁ ⊤) ((g.app ⊤).hom b) := by
  subst hV
  exact ⟨b, rfl⟩

end Germs

/-! ### Open squares -/

section OpenSquares

/-- H-projectivity along a pull-back square. -/
private theorem isProjectiveMorphism_of_isPullback {P X Y Z : Scheme.{0}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (H : IsPullback fst snd f g)
    (hf : IsProjectiveMorphism f) : IsProjectiveMorphism snd := by
  obtain ⟨n, e, he, hef⟩ := hf.baseChange g
  refine ⟨n, H.isoPullback.hom ≫ e, inferInstance, ?_⟩
  rw [Category.assoc, hef, H.isoPullback_hom_snd]

/-- Birationality along a pull-back square of open immersions. -/
private theorem isBirationalMorphism_of_isPullback {U V X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral U] [IsIntegral V] {g : U ⟶ V} {iU : U ⟶ X} {iV : V ⟶ Y} {f : X ⟶ Y}
    [IsOpenImmersion iU] [IsOpenImmersion iV] (H : IsPullback g iU iV f)
    (hf : IsBirationalMorphism f) : IsBirationalMorphism g := by
  obtain ⟨O, hOd, hO⟩ := MMP.Fourfold.Crepant.exists_isOpenImmersion_of_isBirationalMorphism hf
  let O' : U.Opens := iU ⁻¹ᵁ O
  have hne : (O' : Set U).Nonempty := by
    obtain ⟨u⟩ : Nonempty U := inferInstance
    obtain ⟨x, hxU, hxO⟩ := hOd.inter_open_nonempty (Set.range iU) iU.isOpenEmbedding.isOpen_range
      ⟨iU u, u, rfl⟩
    obtain ⟨y, rfl⟩ := hxU
    exact ⟨y, hxO⟩
  have hc : O'.ι ≫ g ≫ iV = (iU ∣_ O) ≫ O.ι ≫ f := by
    rw [H.w, morphismRestrict_ι_assoc]
  have h1 : IsOpenImmersion ((O'.ι ≫ g) ≫ iV) := by
    rw [Category.assoc, hc]; infer_instance
  have : IsOpenImmersion (O'.ι ≫ g) := IsOpenImmersion.of_comp _ iV
  exact MMP.Spreading.isBirationalMorphism_of_isOpenImmersion_ι_comp' g O' hne

/-- The image of the source of an open square is the preimage of the image of its base. -/
private theorem preimage_opensRange_of_isPullback {U V X Y : Scheme.{0}} {g : U ⟶ V}
    {iU : U ⟶ X} {iV : V ⟶ Y} {f : X ⟶ Y} [IsOpenImmersion iU] [IsOpenImmersion iV]
    (H : IsPullback g iU iV f) : f ⁻¹ᵁ iV.opensRange = iU.opensRange := by
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H ⊤
  rw [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange,
    Scheme.Hom.image_top_eq_opensRange] at h
  exact h.symm

/-- The extension of function fields only depends on the morphism. -/
private theorem functionFieldMap_congr {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    {f g : X ⟶ Y} [IsDominant f] [IsDominant g] (h : f = g) :
    functionFieldMap f = functionFieldMap g := by
  subst h; rfl

end OpenSquares

/-! ### Transforms of prime divisors along open squares -/

section Transforms

open AlgebraicGeometry.OpenWeilRestriction

/-- The push-forward of divisors along partial maps of prime divisors, compared along injective
maps of prime divisors which intertwine them. -/
private theorem mapPrimeDivisors_apply_of_comap {X X' Y Y' : Scheme.{0}} {R : Type*}
    [AddCommGroup R] {α : MMP.Mori.PrimeDivisor X → MMP.Mori.PrimeDivisor X'}
    {β : MMP.Mori.PrimeDivisor Y → MMP.Mori.PrimeDivisor Y'}
    (hα : Function.Injective α) (hβ : Function.Injective β)
    {τ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)}
    {τ' : MMP.Mori.PrimeDivisor X' → Option (MMP.Mori.PrimeDivisor Y')}
    (h₁ : ∀ P, τ' (α P) = (τ P).map β) (h₂ : ∀ Q F, τ' Q = some (β F) → Q ∈ Set.range α)
    {D : DivisorWithCoeffs R X} {D' : DivisorWithCoeffs R X'} (hD : ∀ P, D' (α P) = D P)
    (F : MMP.Mori.PrimeDivisor Y) :
    DivisorWithCoeffs.mapPrimeDivisors τ' D' (β F) =
      DivisorWithCoeffs.mapPrimeDivisors τ D F := by
  classical
  have hsplit : D' = Finsupp.mapDomain α D + (D' - Finsupp.mapDomain α D) := by abel
  have hN : ∀ Q ∈ (D' - Finsupp.mapDomain α D).support, Q ∉ Set.range α := by
    rintro Q hQ ⟨P, rfl⟩
    rw [Finsupp.mem_support_iff, Finsupp.sub_apply, Finsupp.mapDomain_apply_of_injective hα, hD,
      sub_self] at hQ
    exact hQ rfl
  have h1 : ∀ E : DivisorWithCoeffs R X,
      DivisorWithCoeffs.mapPrimeDivisors τ' (Finsupp.mapDomain α E) =
        Finsupp.mapDomain β (DivisorWithCoeffs.mapPrimeDivisors τ E) := by
    intro E
    induction E using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [Finsupp.mapDomain_add, map_add, map_add, ha, hb, Finsupp.mapDomain_add]
    | single P r =>
      rw [Finsupp.mapDomain_single, DivisorWithCoeffs.mapPrimeDivisors_single,
        DivisorWithCoeffs.mapPrimeDivisors_single, h₁]
      rcases τ P with _ | G
      · simp
      · simp [Finsupp.mapDomain_single]
  have h2 : DivisorWithCoeffs.mapPrimeDivisors τ' (D' - Finsupp.mapDomain α D) (β F) = 0 := by
    set N := D' - Finsupp.mapDomain α D with hNdef
    have hNs : N = ∑ Q ∈ N.support, Finsupp.single Q (N Q) := (Finsupp.sum_single N).symm
    rw [hNs, map_sum, Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun Q hQ => ?_
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases hτ : τ' Q with _ | G
    · rfl
    · change Finsupp.single G (N Q) (β F) = 0
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact hN Q hQ (h₂ Q F hτ)
  rw [hsplit, map_add, Finsupp.add_apply, h2, add_zero, h1, Finsupp.mapDomain_apply_of_injective hβ]

/-- Prime divisors of the source of an open square and their transforms. -/
private theorem transformPrimeDivisor_primeDivisorMap_of_isPullback {U V X Y : Scheme.{0}}
    [IsReduced U] [IsReduced X] [IsSeparated (V ↘ Limits.terminal Scheme)]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] {g : U ⟶ V} {iU : U ⟶ X} {iV : V ⟶ Y}
    {f : X ⟶ Y} [IsOpenImmersion iU] [IsOpenImmersion iV] (H : IsPullback g iU iV f) :
    (∀ E, RationalMap.transformPrimeDivisor f.toRationalMap (primeDivisorMap iU E) =
      (RationalMap.transformPrimeDivisor g.toRationalMap E).map (primeDivisorMap iV)) ∧
    (∀ Q F, RationalMap.transformPrimeDivisor f.toRationalMap Q = some (primeDivisorMap iV F) →
      Q ∈ Set.range (primeDivisorMap iU)) := by
  have hw : ∀ x, f (iU x) = iV (g x) := fun x => by
    rw [← Scheme.Hom.comp_apply, ← H.w, Scheme.Hom.comp_apply]
  refine ⟨fun E => ?_, fun Q F hQ => ?_⟩
  · rcases hE : RationalMap.transformPrimeDivisor g.toRationalMap E with _ | F
    · rw [Option.map_none, Option.eq_none_iff_forall_ne_some]
      intro G hG
      rw [MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff,
        genericPoint_primeDivisorMap', hw] at hG
      obtain ⟨F, rfl⟩ := (mem_range_primeDivisorMap_iff iV G).mpr ⟨_, hG⟩
      rw [genericPoint_primeDivisorMap'] at hG
      have := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff g E F).mpr
        (iV.isOpenEmbedding.injective hG)
      rw [hE] at this
      simp at this
    · rw [Option.map_some, MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff,
        genericPoint_primeDivisorMap', genericPoint_primeDivisorMap', hw,
        (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff g E F).mp hE]
  · rw [MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff,
      genericPoint_primeDivisorMap'] at hQ
    have hmem : Q.genericPoint ∈ f ⁻¹ᵁ iV.opensRange := by
      show f Q.genericPoint ∈ iV.opensRange
      rw [hQ]; exact ⟨_, rfl⟩
    rw [preimage_opensRange_of_isPullback H] at hmem
    exact (mem_range_primeDivisorMap_iff iU Q).mpr hmem

/-- The push-forward of a divisor along a morphism, compared with the push-forward of its
restriction along the restricted morphism of an open square. -/
private theorem transformDivisor_primeDivisorMap_of_isPullback {U V X Y : Scheme.{0}}
    [IsReduced U] [IsReduced X] [IsSeparated (V ↘ Limits.terminal Scheme)]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] {g : U ⟶ V} {iU : U ⟶ X} {iV : V ⟶ Y}
    {f : X ⟶ Y} [IsOpenImmersion iU] [IsOpenImmersion iV] (H : IsPullback g iU iV f)
    {R : Type*} [AddCommGroup R] {D : DivisorWithCoeffs R U} {D' : DivisorWithCoeffs R X}
    (hD : ∀ P, D' (primeDivisorMap iU P) = D P) (F : MMP.Mori.PrimeDivisor V) :
    RationalMap.transformDivisor f.toRationalMap D' (primeDivisorMap iV F) =
      RationalMap.transformDivisor g.toRationalMap D F :=
  mapPrimeDivisors_apply_of_comap (primeDivisorMap_injective iU) (primeDivisorMap_injective iV)
    (transformPrimeDivisor_primeDivisorMap_of_isPullback H).1
    (transformPrimeDivisor_primeDivisorMap_of_isPullback H).2 hD F

/-- Transforms of prime divisors along `q ∘ p⁻¹`, for a common model `p`, `q`, compared with
those of its restriction over open subschemes. -/
private theorem transformPrimeDivisor_compHom_primeDivisorMap {k : Type} [Field k]
    {S Sb W Wb V Yb : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [IsIntegral Sb] [IsLocallyNoetherian Sb] [IsNormal Sb] [IsIntegral W] [IsIntegral Wb]
    [IsLocallyNoetherian Wb] [IsNormal Wb]
    [IsSeparated (S ↘ Limits.terminal Scheme)] [IsSeparated (Sb ↘ Limits.terminal Scheme)]
    [IsSeparated (V ↘ Limits.terminal Scheme)] [IsSeparated (Yb ↘ Limits.terminal Scheme)]
    {sSb : Sb ⟶ Spec (.of k)} {i : S ⟶ Sb} {ιW : W ⟶ Wb} {ιV : V ⟶ Yb} [IsOpenImmersion i]
    [IsOpenImmersion ιW] [IsOpenImmersion ιV] {p : W ⟶ S} {pb : Wb ⟶ Sb} {q : W ⟶ V}
    {qb : Wb ⟶ Yb} (hSb : IsNormalVariety k sSb) (hWb : IsNormalVariety k (pb ≫ sSb))
    (Hp : IsPullback p ιW i pb) (Hq : IsPullback q ιW ιV qb) [IsProper p] [IsProper pb]
    [IsSeparated p] [IsSeparated pb] (hpB : IsBirationalMorphism p)
    (hpbB : IsBirationalMorphism pb) {h : S.RationalMap W}
    (hh : RationalMap.IsInverse p.toRationalMap h) {hb : Sb.RationalMap Wb}
    (hhb : RationalMap.IsInverse pb.toRationalMap hb) :
    (∀ P, RationalMap.transformPrimeDivisor (hb.compHom qb) (primeDivisorMap i P) =
      (RationalMap.transformPrimeDivisor (h.compHom q) P).map (primeDivisorMap ιV)) ∧
    (∀ Q F, RationalMap.transformPrimeDivisor (hb.compHom qb) Q = some (primeDivisorMap ιV F) →
      Q ∈ Set.range (primeDivisorMap i)) := by
  classical
  have hwp : ∀ x, pb (ιW x) = i (p x) := fun x => by
    rw [← Scheme.Hom.comp_apply, ← Hp.w, Scheme.Hom.comp_apply]
  have hwq : ∀ x, qb (ιW x) = ιV (q x) := fun x => by
    rw [← Scheme.Hom.comp_apply, ← Hq.w, Scheme.Hom.comp_apply]
  have hrp := preimage_opensRange_of_isPullback Hp
  have hrq := preimage_opensRange_of_isPullback Hq
  have hst : ∀ Q : MMP.Mori.PrimeDivisor Sb, ∃ QW : MMP.Mori.PrimeDivisor Wb,
      pb QW.genericPoint = Q.genericPoint := fun Q => by
    obtain ⟨E, hE, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hSb hWb hpbB Q
    exact ⟨E, hE⟩
  have hstS : ∀ P : MMP.Mori.PrimeDivisor S, ∃ PW : MMP.Mori.PrimeDivisor W,
      p PW.genericPoint = P.genericPoint := by
    intro P
    obtain ⟨QW, hQW⟩ := hst (primeDivisorMap i P)
    have hmem : QW.genericPoint ∈ pb ⁻¹ᵁ i.opensRange := by
      show pb QW.genericPoint ∈ i.opensRange
      rw [hQW, genericPoint_primeDivisorMap']; exact ⟨_, rfl⟩
    rw [hrp] at hmem
    obtain ⟨PW, rfl⟩ := (mem_range_primeDivisorMap_iff ιW QW).mpr hmem
    refine ⟨PW, i.isOpenEmbedding.injective ?_⟩
    have h1 := hQW
    rw [genericPoint_primeDivisorMap', genericPoint_primeDivisorMap', hwp] at h1
    exact h1
  refine ⟨fun P => ?_, fun Q F hQ => ?_⟩
  · obtain ⟨PW, hPW⟩ := hstS P
    have hPbW : pb (MMP.Mori.PrimeDivisor.genericPoint (primeDivisorMap ιW PW)) =
        MMP.Mori.PrimeDivisor.genericPoint (primeDivisorMap i P) := by
      rw [genericPoint_primeDivisorMap', genericPoint_primeDivisorMap', hwp, hPW]
    have e1 := fun F => transformPrimeDivisor_eq_some_iff_of_isInverse p hpB hh q rfl P PW hPW F
    have e2 := fun G => transformPrimeDivisor_eq_some_iff_of_isInverse pb hpbB hhb qb rfl
      (primeDivisorMap i P) (primeDivisorMap ιW PW) hPbW G
    rcases hP : RationalMap.transformPrimeDivisor (h.compHom q) P with _ | F
    · rw [Option.map_none, Option.eq_none_iff_forall_ne_some]
      intro G hG
      rw [e2, genericPoint_primeDivisorMap', hwq] at hG
      obtain ⟨F, rfl⟩ := (mem_range_primeDivisorMap_iff ιV G).mpr ⟨_, hG⟩
      rw [genericPoint_primeDivisorMap'] at hG
      have := (e1 F).mpr (ιV.isOpenEmbedding.injective hG)
      rw [hP] at this
      simp at this
    · rw [Option.map_some, e2, genericPoint_primeDivisorMap', genericPoint_primeDivisorMap', hwq,
        (e1 F).mp hP]
  · obtain ⟨QW, hQW⟩ := hst Q
    have e2 := (transformPrimeDivisor_eq_some_iff_of_isInverse pb hpbB hhb qb rfl Q QW hQW _).mp hQ
    rw [genericPoint_primeDivisorMap'] at e2
    have hmem : QW.genericPoint ∈ qb ⁻¹ᵁ ιV.opensRange := by
      show qb QW.genericPoint ∈ ιV.opensRange
      rw [e2]; exact ⟨_, rfl⟩
    rw [hrq] at hmem
    obtain ⟨w, hw⟩ := hmem
    refine (mem_range_primeDivisorMap_iff i Q).mpr ⟨p w, ?_⟩
    rw [← hwp, hw, hQW]

end Transforms

/-! ### Restriction of divisors along open immersions -/

section Comap

open AlgebraicGeometry.OpenWeilRestriction

/-- The restriction of a divisor along an open immersion `i : S ⟶ S̄`: the coefficient along a
prime divisor of `S` is the coefficient along its closure. -/
private noncomputable abbrev comapDivisor {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i]
    {R : Type*} [Zero R] (D : DivisorWithCoeffs R Y) : DivisorWithCoeffs R X :=
  Finsupp.comapDomain (primeDivisorMap i) D (primeDivisorMap_injective i).injOn

private theorem coeff_comapDivisor {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i]
    {R : Type*} [Zero R] (D : DivisorWithCoeffs R Y) (P : MMP.Mori.PrimeDivisor X) :
    (comapDivisor i D).coeff P = D.coeff (primeDivisorMap i P) := rfl

private theorem comapDivisor_sum_smul_toRDivisor {X Y : Scheme.{0}} (i : X ⟶ Y)
    [IsOpenImmersion i] {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y) :
    comapDivisor i (∑ j, r j • Divisor.toRDivisor (L j)) =
      ∑ j, r j • Divisor.toRDivisor (comapDivisor i (L j)) := by
  refine Finsupp.ext fun P => ?_
  change (comapDivisor i _).coeff P = (∑ j, r j • Divisor.toRDivisor (comapDivisor i (L j))).coeff P
  rw [coeff_comapDivisor, MMP.Fourfold.coeff_sum_smul_toRDivisor,
    MMP.Fourfold.coeff_sum_smul_toRDivisor]
  rfl

variable {S Sb : Scheme.{0}} [IsIntegral S] [IsIntegral Sb] [IsLocallyNoetherian S]
  [IsLocallyNoetherian Sb] [IsNormal S] [IsNormal Sb]

/-- A local equation of `D` on `U` restricts to a local equation of the restriction of `D` on the
preimage of `U`. -/
private theorem isLocalEquation_comapDivisor (i : S ⟶ Sb) [IsOpenImmersion i] [IsDominant i]
    {B : Divisor Sb} {U : Sb.Opens} {φ : (RationalFunctions Sb)ˣ} (hφ : B.IsLocalEquation U φ) :
    Divisor.IsLocalEquation (comapDivisor i B) (i ⁻¹ᵁ U)
      (Units.map (rationalFunctionsEquiv i).toMonoidHom φ) := by
  intro P hP
  have hP' : ((primeDivisorMap i P).support ∩ U).Nonempty := by
    refine (MMP.Mori.PrimeDivisor.genericPoint_mem_iff (primeDivisorMap i P) U).mp ?_
    rw [genericPoint_primeDivisorMap']
    exact (P.genericPoint_mem_iff (i ⁻¹ᵁ U)).mpr hP
  rw [coeff_comapDivisor, ord_rationalFunctionsEquiv]
  exact hφ _ hP'

/-- The restriction of a Cartier divisor along an open immersion is Cartier. -/
private theorem isCartier_comapDivisor (i : S ⟶ Sb) [IsOpenImmersion i] [IsDominant i]
    {B : Divisor Sb} (hB : B.IsCartier) : Divisor.IsCartier (comapDivisor i B) := by
  intro x
  obtain ⟨U, hxU, φ, hφ⟩ := hB (i x)
  exact ⟨i ⁻¹ᵁ U, hxU, _, isLocalEquation_comapDivisor i hφ⟩

variable {W Wb : Scheme.{0}} [IsIntegral W] [IsIntegral Wb] [IsLocallyNoetherian W]
  [IsLocallyNoetherian Wb] [IsNormal W] [IsNormal Wb]

/-- Pull-backs of Cartier divisors commute with restriction along an open square. -/
private theorem isPullback_comapDivisor [CompactSpace W] {i : S ⟶ Sb} [IsOpenImmersion i]
    [IsDominant i] {ιW : W ⟶ Wb} [IsOpenImmersion ιW] [IsDominant ιW] {p : W ⟶ S}
    {pb : Wb ⟶ Sb} [IsDominant p] [IsDominant pb] (Hp : IsPullback p ιW i pb) {B : Divisor Sb}
    (hBc : B.IsCartier) {hB : ∀ Z : irreducibleComponents Wb, pb (componentGenericPoint Wb Z) ∉ B.supp}
    {B' : Divisor Wb} (h : B.IsPullback pb hB B') :
    Divisor.IsPullback p (comapDivisor i B)
      (map_componentGenericPoint_notMem_supp_of_isDominant p _) (comapDivisor ιW B') := by
  obtain ⟨B'', hB''⟩ := (isCartier_comapDivisor i hBc).exists_isPullback (f := p)
    (map_componentGenericPoint_notMem_supp_of_isDominant p _)
  suffices e : comapDivisor ιW B' = B'' by rw [e]; exact hB''
  refine Finsupp.ext fun E => ?_
  obtain ⟨U, hU, φ, hφ⟩ := hBc (i (p E.genericPoint))
  have hpbE : pb (MMP.Mori.PrimeDivisor.genericPoint (primeDivisorMap ιW E)) ∈ U := by
    rw [genericPoint_primeDivisorMap', ← Scheme.Hom.comp_apply, ← Hp.w, Scheme.Hom.comp_apply]
    exact hU
  let Z₀ : irreducibleComponents Sb := ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩
  let Z₁ : irreducibleComponents S := ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩
  have h1 := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h hφ _ hpbE Z₀
  have h2 := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hB''
    (isLocalEquation_comapDivisor i hφ) E hU Z₁
  change B'.coeff (primeDivisorMap ιW E) = B''.coeff E
  have hcoe : ((Units.map (rationalFunctionsEquiv i).toMonoidHom φ : (RationalFunctions S)ˣ) :
      RationalFunctions S) = rationalFunctionsEquiv i (φ : RationalFunctions Sb) := rfl
  have key : ∀ g : Sb.functionField,
      functionFieldMap p (functionFieldMap i g) = functionFieldMap ιW (functionFieldMap pb g) := by
    intro g
    rw [← RingHom.comp_apply, ← functionFieldMap_comp, functionFieldMap_congr Hp.w,
      functionFieldMap_comp, RingHom.comp_apply]
  rw [h1, h2, hcoe, evalFF_rationalFunctionsEquiv i Z₁ Z₀, key]
  exact (ord_functionFieldMap_primeDivisorMap ιW E _).symm

/-- `ℝ`-Cartier pull-backs commute with restriction along an open square. -/
private theorem isRCartierPullback_comapDivisor [CompactSpace W] {i : S ⟶ Sb}
    [IsOpenImmersion i] [IsDominant i] {ιW : W ⟶ Wb} [IsOpenImmersion ιW] [IsDominant ιW]
    {p : W ⟶ S} {pb : Wb ⟶ Sb} [IsDominant p] [IsDominant pb] (Hp : IsPullback p ιW i pb)
    {D : RDivisor Sb} {G : RDivisor Wb} (h : MMP.Flips.IsRCartierPullback pb D G) :
    MMP.Flips.IsRCartierPullback p (comapDivisor i D) (comapDivisor ιW G) := by
  obtain ⟨m, r, L, L', hL, hD, hpbL, hG⟩ := h
  refine ⟨m, r, fun j => comapDivisor i (L j), fun j => comapDivisor ιW (L' j),
    fun j => isCartier_comapDivisor i (hL j), ?_, fun j => ?_, ?_⟩
  · rw [hD, comapDivisor_sum_smul_toRDivisor]
  · obtain ⟨hB, hj⟩ := hpbL j
    exact ⟨_, isPullback_comapDivisor Hp (hL j) hj⟩
  · rw [hG, comapDivisor_sum_smul_toRDivisor]

end Comap

/-! ### Exceptional prime divisors and coheight -/

section Exceptional

open AlgebraicGeometry.OpenWeilRestriction

private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add] at h
    have h := WithBot.coe_injective h
    obtain ⟨hd, hc⟩ : d ≠ ⊤ ∧ c ≠ ⊤ := by
      rw [← not_or, ← ENat.add_eq_top, h]; exact ENat.natCast_ne_top n
    lift d to ℕ using hd
    lift c to ℕ using hc
    rw [show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_ofNat,
      ← WithBot.coe_add, WithBot.coe_le_coe]
    norm_cast at h ⊢
    omega

/-- A variety over a field has finite dimension. -/
private theorem exists_topologicalKrullDim_eq_natCast {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX] [CompactSpace X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  induction hd : topologicalKrullDim X using WithBot.recBotCoe with
  | bot =>
    exact ((Order.krullDim_eq_bot_iff.mp hd).false
      (⟨closure {genericPoint X}, isIrreducible_singleton.closure, isClosed_closure⟩ :
        TopologicalSpace.IrreducibleCloseds X)).elim
  | coe d =>
    lift d to ℕ using fun h => h1 (by rw [hd, h]; rfl)
    exact ⟨d, rfl⟩

/-- A prime divisor is exceptional for a proper birational morphism of normal varieties exactly
when its generic point maps to a point of coheight at least two. -/
private theorem isExceptionalPrimeDivisor_iff {k : Type} [Field k] {W Y : Scheme.{0}}
    [IsLocallyNoetherian W] [IsNormal W] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) {q : W ⟶ Y}
    (hW : IsNormalVariety k (q ≫ sY)) [IsProper q] (hq : IsBirationalMorphism q)
    (E : MMP.Mori.PrimeDivisor W) :
    MMP.Flips.IsExceptionalPrimeDivisor sY q E ↔ 2 ≤ Order.coheight (q E.genericPoint) := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : QuasiCompact sY := hY.1.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast sY
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY (q E.genericPoint)
  rw [hn] at hd
  constructor
  · rintro ⟨hY', hq', hp', hE⟩
    unfold MMP.Flips.ProperDivisorOver.IsExceptional at hE
    rw [MMP.Flips.ProperDivisorOver.center_eq_toDivisorOver_center,
      MMP.Mori.DivisorOver.center_eq_closure_genericPoint, hn] at hE
    exact (withBot_add_two_le_iff hd).mp hE
  · intro h2
    refine ⟨hW, hq, inferInstance, ?_⟩
    unfold MMP.Flips.ProperDivisorOver.IsExceptional
    rw [MMP.Flips.ProperDivisorOver.center_eq_toDivisorOver_center,
      MMP.Mori.DivisorOver.center_eq_closure_genericPoint, hn]
    exact (withBot_add_two_le_iff hd).mpr h2

/-- If the generic point of a prime divisor `P` maps, through a representative `g` of `φ`, to a
point of coheight at most one, then `P` is not `φ`-exceptional. -/
private theorem not_isExceptional_of_coheight_le_one {X Y : Scheme.{0}} [IsReduced X]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] {φ : X.RationalMap Y}
    (g : X.PartialMap Y) (hg : g.toRationalMap = φ) (P : MMP.Mori.PrimeDivisor X)
    (hP : P.genericPoint ∈ g.domain) (h : Order.coheight (g.hom ⟨P.genericPoint, hP⟩) ≤ 1) :
    ¬ RationalMap.IsExceptional φ P := by
  intro hex
  have hdef : RationalMap.DefinedAt φ P.genericPoint :=
    RationalMap.definedAt_iff.mpr ⟨g, hP, hg⟩
  have h2 := RationalMap.isExceptional_iff.mp hex hdef
  have htr := MMP.Flips.coe_transform_eq_closure_singleton g hg P hP
  have h3 := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h2 (g.hom ⟨P.genericPoint, hP⟩)
    (by rw [htr]; exact subset_closure rfl)
  exact absurd (h3.trans h) (by norm_num)

end Exceptional

/-! ### Canonical divisors on a common model -/

section Canonical

open MMP.Positivity

/-- Rational top forms pull back surjectively along a dominant morphism inducing an isomorphism
of function fields. -/
private theorem exists_pullbackRationalPluriForms_eq {A B : Scheme.{0}} [IsIntegral A]
    [IsIntegral B] {sB : B ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sB] (g : A ⟶ B) [IsDominant g]
    (hbij : Function.Bijective (functionFieldMap g)) {n : ℕ}
    (hd : letI := functionFieldAlgebra sB; (Algebra.trdeg ℂ B.functionField).toNat = n)
    (ω₁ : RationalPluriForms (g ≫ sB) n 1) :
    ∃ τ : RationalPluriForms sB n 1, pullbackRationalPluriForms sB g τ = ω₁ := by
  let := functionFieldAlgebra sB
  let := functionFieldAlgebra (g ≫ sB)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sB g
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sB g hbij hd
  obtain ⟨c, hc⟩ := hbij.2
    ((ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) 1).repr ω₁ ())
  refine ⟨c • ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) 1 (), ?_⟩
  change pullbackForms (K := B.functionField) (K' := A.functionField) 1 _ = ω₁
  rw [pullbackForms_eq hω, pullbackFormsAlong]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_eq_same, smul_eq_mul, mul_one]
  change functionFieldMap g c • _ = ω₁
  rw [hc]
  exact basis_unit_repr_smul _ ω₁

/-- The pull-back of a nonzero form along a dominant morphism inducing an isomorphism of function
fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {A B : Scheme.{0}} [IsIntegral A]
    [IsIntegral B] {sB : B ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sB] (g : A ⟶ B) [IsDominant g]
    (hbij : Function.Bijective (functionFieldMap g)) {n : ℕ}
    (hd : letI := functionFieldAlgebra sB; (Algebra.trdeg ℂ B.functionField).toNat = n)
    {τ : RationalPluriForms sB n 1} (hτ : τ ≠ 0) : pullbackRationalPluriForms sB g τ ≠ 0 := by
  let := functionFieldAlgebra sB
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sB g hbij hd
  let := functionFieldAlgebra (g ≫ sB)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sB g
  have hpull : pullbackRationalPluriForms sB g τ = pullbackFormsAlong hω 1 τ :=
    pullbackForms_eq hω 1 τ
  have hrepr := repr_pullbackFormsAlong hω 1 τ
  intro h0
  have h0' : pullbackFormsAlong hω 1 τ = 0 := hpull ▸ h0
  have h1 : algebraMap B.functionField A.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) 1).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ
    ((map_eq_zero_iff _ (RingHom.injective (algebraMap B.functionField A.functionField))).mp h1)

/-- The pull-back of the zero form is zero. -/
private theorem pullbackRationalPluriForms_zero {A B : Scheme.{0}} [IsIntegral A]
    [IsIntegral B] {sB : B ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sB] (g : A ⟶ B) [IsDominant g]
    (hbij : Function.Bijective (functionFieldMap g)) {n : ℕ}
    (hd : letI := functionFieldAlgebra sB; (Algebra.trdeg ℂ B.functionField).toNat = n) :
    pullbackRationalPluriForms sB g (0 : RationalPluriForms sB n 1) = 0 := by
  let := functionFieldAlgebra sB
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sB g hbij hd
  let := functionFieldAlgebra (g ≫ sB)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sB g
  change pullbackForms (K := B.functionField) (K' := A.functionField) 1 0 = 0
  rw [pullbackForms_eq hω, pullbackFormsAlong]
  simp

private theorem divisorOfForm_cast {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {s s' : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType s]
    [LocallyOfFiniteType s'] (h : s = s') {n : ℕ} (τ : RationalPluriForms s n 1) :
    divisorOfForm (h ▸ τ) = divisorOfForm τ := by
  subst h; rfl

private theorem eq_zero_of_cast_eq_zero {X : Scheme.{0}} [IsIntegral X] {s s' : X ⟶ Spec (.of ℂ)}
    (h : s = s') {n : ℕ} {τ : RationalPluriForms s n 1} (h0 : h ▸ τ = 0) : τ = 0 := by
  subst h; exact h0

/-- **Canonical divisors on a common model.** For a common model `p : W ⟶ S`, `q : W ⟶ Y` of a
birational map `φ = q ∘ p⁻¹` of normal varieties extracting no divisor, and a canonical divisor
`K` of `S`, there is a canonical divisor `K_W` of `W` with `p_* K_W = K` and `q_* K_W = φ_* K`,
and `φ_* K` is a canonical divisor of `Y`. -/
private theorem exists_isCanonicalDivisor_common_model {Sb Wb Yb : Scheme.{0}} [IsIntegral Sb]
    [IsLocallyNoetherian Sb] [IsNormal Sb] [CompactSpace Sb] [IsIntegral Wb]
    [IsLocallyNoetherian Wb] [IsNormal Wb] [CompactSpace Wb] [IsIntegral Yb]
    [IsLocallyNoetherian Yb] [IsNormal Yb] [CompactSpace Yb]
    {sSb : Sb ⟶ Spec (.of ℂ)} {sWb : Wb ⟶ Spec (.of ℂ)} {sYb : Yb ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sSb] [LocallyOfFiniteType sWb] [LocallyOfFiniteType sYb]
    (hSn : IsNormalVariety ℂ sSb) (hWn : IsNormalVariety ℂ sWb) (hYn : IsNormalVariety ℂ sYb)
    [IsSeparated (Sb ↘ Limits.terminal Scheme)] [IsSeparated (Yb ↘ Limits.terminal Scheme)]
    {pb : Wb ⟶ Sb} {qb : Wb ⟶ Yb} (hpbs : pb ≫ sSb = sWb) (hqbs : qb ≫ sYb = sWb)
    [IsProper pb] [IsProper qb] [IsSeparated pb] [IsSeparated qb]
    (hpbB : IsBirationalMorphism pb) (hqbB : IsBirationalMorphism qb) {hb : Sb.RationalMap Wb}
    (hinv : RationalMap.IsInverse pb.toRationalMap hb)
    (hnoex : ∀ F : MMP.Mori.PrimeDivisor Yb,
      ¬ MMP.Flips.RationalMap.IsInverseExceptional (hb.compHom qb) F)
    {Kb : Divisor Sb} (hKb : Kb.IsCanonicalDivisor sSb 3) :
    ∃ KWb : Divisor Wb, KWb.IsCanonicalDivisor sWb 3 ∧
      RationalMap.transformDivisor pb.toRationalMap KWb = Kb ∧
      RationalMap.transformDivisor qb.toRationalMap KWb =
        RationalMap.transformDivisor (hb.compHom qb) Kb ∧
      Divisor.IsCanonicalDivisor sYb 3 (RationalMap.transformDivisor (hb.compHom qb) Kb) := by
  classical
  subst hpbs
  haveI : MMP.Mori.IsVariety ℂ sSb := hSn.1
  haveI : MMP.Mori.IsVariety ℂ sYb := hYn.1
  haveI : MMP.Mori.IsVariety ℂ (pb ≫ sSb) := hWn.1
  haveI : IsDominant pb := hpbB.isDominant
  haveI : IsDominant qb := hqbB.isDominant
  have hWq : IsNormalVariety ℂ (qb ≫ sYb) := hqbs ▸ hWn
  haveI : LocallyOfFiniteType (qb ≫ sYb) := hWq.1.toLocallyOfFiniteType
  haveI : MMP.Mori.IsVariety ℂ (qb ≫ sYb) := hWq.1
  have hdimS : topologicalKrullDim Sb = 3 := hKb.topologicalKrullDim_eq
  have hdimW : topologicalKrullDim Wb = 3 :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sSb (pb ≫ sSb) hpbB).symm.trans
      hdimS
  have hdimY : topologicalKrullDim Yb = 3 :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sYb (qb ≫ sYb) hqbB).trans
      hdimW
  have hbijp := hpbB.functionFieldMap_bijective
  have hbijq := hqbB.functionFieldMap_bijective
  have hdS := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sSb) hdimS
  have hdY := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sYb) hdimY
  obtain ⟨ω₁, hω₁0, hω₁⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hSn hKb
  set ωW := pullbackRationalPluriForms sSb pb ω₁ with hωW
  have hωW0 : ωW ≠ 0 := pullbackRationalPluriForms_ne_zero pb hbijp hdS hω₁0
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (pb ≫ sSb) hWn hdimW
  have hKW : (divisorOfForm ωW).IsCanonicalDivisor (pb ≫ sSb) 3 := by
    have hl := linearlyEquivalent_divisorOfForm_zsmul hWn hK₀ hωW0
    rw [one_zsmul] at hl
    exact hK₀.of_linearlyEquivalent hl
  -- `p_* div(p^* ω) = div ω`
  have hpush : RationalMap.transformDivisor pb.toRationalMap (divisorOfForm ωW) = Kb := by
    refine Finsupp.ext fun P => ?_
    obtain ⟨E, hE, hEiso, hEtr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hSn hWn hpbB P
    rw [hEtr]
    change (divisorOfForm ωW).coeff E = Kb.coeff P
    rw [coeff_divisorOfForm, hωW,
      ordForm_pullbackRationalPluriForms_of_isIso pb hbijp hdS E P hE ω₁, hω₁]
  -- a form `σ` on `Y` with `q^* σ = p^* ω`
  obtain ⟨σ, hσ⟩ := exists_pullbackRationalPluriForms_eq qb hbijq hdY (hqbs.symm ▸ ωW)
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    apply hωW0
    apply eq_zero_of_cast_eq_zero hqbs.symm
    rw [← hσ]
    exact pullbackRationalPluriForms_zero qb hbijq hdY
  have hdivσ : divisorOfForm (pullbackRationalPluriForms sYb qb σ) = divisorOfForm ωW := by
    rw [hσ]; exact divisorOfForm_cast hqbs.symm ωW
  have hFW : ∀ F : MMP.Mori.PrimeDivisor Yb, ∃ FW : MMP.Mori.PrimeDivisor Wb,
      qb FW.genericPoint = F.genericPoint ∧ IsIso (qb.stalkMap FW.genericPoint) ∧
        ∀ D : Divisor Wb, RationalMap.transformDivisor qb.toRationalMap D F = D FW := fun F => by
    obtain ⟨E, hE, hEiso, hEtr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hYn hWq hqbB F
    exact ⟨E, hE, hEiso, fun D => hEtr D⟩
  have hpushq : RationalMap.transformDivisor qb.toRationalMap (divisorOfForm ωW) =
      divisorOfForm σ := by
    refine Finsupp.ext fun F => ?_
    obtain ⟨E, hE, hEiso, hEtr⟩ := hFW F
    haveI := hEiso
    rw [hEtr, ← hdivσ]
    change (divisorOfForm (pullbackRationalPluriForms sYb qb σ)).coeff E =
      (divisorOfForm σ).coeff F
    rw [coeff_divisorOfForm, coeff_divisorOfForm,
      ordForm_pullbackRationalPluriForms_of_isIso qb hbijq hdY E F hE σ]
  have hphi : RationalMap.transformDivisor (hb.compHom qb) Kb = divisorOfForm σ := by
    refine Finsupp.ext fun F => ?_
    obtain ⟨FW, hFWe, hFWiso, -⟩ := hFW F
    obtain ⟨P, hP⟩ : ∃ P, RationalMap.transformPrimeDivisor (hb.compHom qb) P = some F := by
      by_contra hc
      exact hnoex F fun P hP => hc ⟨P, hP⟩
    have hst : ∀ P' : MMP.Mori.PrimeDivisor Sb,
        RationalMap.transformPrimeDivisor (hb.compHom qb) P' = some F →
        ∃ PW : MMP.Mori.PrimeDivisor Wb, pb PW.genericPoint = P'.genericPoint ∧
          IsIso (pb.stalkMap PW.genericPoint) ∧ PW = FW := by
      intro P' hP'
      obtain ⟨E, hE, hEiso, -⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hSn hWn hpbB P'
      have hq := (transformPrimeDivisor_eq_some_iff_of_isInverse pb hpbB hinv qb rfl P' E hE
        F).mp hP'
      refine ⟨E, hE, hEiso, AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_⟩
      exact (Crepant.eq_of_apply_eq_of_coheight_le_one qb hbijq (hq.trans hFWe.symm)
        (by rw [hFWe, F.coheight_genericPoint])).symm
    have huniq : ∀ P', RationalMap.transformPrimeDivisor (hb.compHom qb) P' = some F → P' = P := by
      intro P' hP'
      obtain ⟨E, hE, -, hEF⟩ := hst P' hP'
      obtain ⟨E', hE', -, hE'F⟩ := hst P hP
      rw [hEF, ← hE'F] at hE
      exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hE.symm.trans hE')
    obtain ⟨PW, hPW, hPWiso, hPWF⟩ := hst P hP
    haveI := hPWiso
    haveI : IsIso (qb.stalkMap PW.genericPoint) := hPWF ▸ hFWiso
    have hqPW : qb PW.genericPoint = F.genericPoint := hPWF ▸ hFWe
    change DivisorWithCoeffs.mapPrimeDivisors (RationalMap.transformPrimeDivisor (hb.compHom qb))
      Kb F = (divisorOfForm σ).coeff F
    rw [MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hP huniq Kb]
    have e1 : Kb.coeff P = PW.ordForm ωW := by
      rw [hωW, ordForm_pullbackRationalPluriForms_of_isIso pb hbijp hdS PW P hPW ω₁, hω₁]
    have e2 : PW.ordForm ωW = PW.ordForm (pullbackRationalPluriForms sYb qb σ) := by
      have := congrArg (fun D : Divisor Wb => D.coeff PW) hdivσ
      simp only [coeff_divisorOfForm] at this
      exact this.symm
    change Kb.coeff P = _
    rw [e1, e2, coeff_divisorOfForm,
      ordForm_pullbackRationalPluriForms_of_isIso qb hbijq hdY PW F hqPW σ]
  obtain ⟨KY₀, hKY₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sYb hYn hdimY
  have hcanσ : (divisorOfForm σ).IsCanonicalDivisor sYb 3 := by
    have hl := linearlyEquivalent_divisorOfForm_zsmul hYn hKY₀ hσ0
    rw [one_zsmul] at hl
    exact hKY₀.of_linearlyEquivalent hl
  exact ⟨divisorOfForm ωW, hKW, hpush, hpushq.trans hphi.symm, hphi ▸ hcanσ⟩

end Canonical

/-! ### `ℚ`-factoriality and kltness on open subschemes -/

section OpenKlt

open AlgebraicGeometry.OpenWeilRestriction

/-- `ℚ`-factoriality restricts to a nonempty open subscheme: a divisor on the open subscheme is
the restriction of its closure. -/
private theorem isQFactorial_restrictOpen {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (h : IsQFactorial sX)
    (U : X.Opens) [Nonempty U] : IsQFactorial (U.ι ≫ sX) := by
  classical
  haveI : IsDominant U.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion U.ι
  refine ⟨h.1.restrictOpen U, fun D => ?_⟩
  obtain ⟨m, hm, hmc⟩ := h.2 (Finsupp.mapDomain (primeDivisorMap U.ι) D)
  refine ⟨m, hm, ?_⟩
  have he : ((m : ℤ) • D) =
      comapDivisor U.ι ((m : ℤ) • Finsupp.mapDomain (primeDivisorMap U.ι) D) := by
    refine Finsupp.ext fun W => ?_
    change ((m : ℤ) • D) W = ((m : ℤ) • Finsupp.mapDomain (primeDivisorMap U.ι) D)
      (primeDivisorMap U.ι W)
    rw [Finsupp.smul_apply, Finsupp.smul_apply,
      Finsupp.mapDomain_apply_of_injective (primeDivisorMap_injective _)]
  rw [he]
  exact isCartier_comapDivisor U.ι hmc

/-- **Kltness restricts to open subschemes.** An effective real klt boundary on a projective
`ℚ`-factorial complex variety restricts to a klt boundary on every nonempty open subscheme: it lies
below a klt `ℚ`-boundary, kltness of `ℚ`-pairs restricts to opens, and lowering a boundary on a
`ℚ`-factorial variety keeps log discrepancies positive. -/
private theorem isRealKltPair_restrictOpen {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hXp : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX) {Δ : RDivisor X}
    (hΔ0 : ∀ P, 0 ≤ Δ.coeff P) (hΔ : IsRealKltPair sX Δ) (U : X.Opens) [Nonempty U] :
    IsRealKltPair (U.ι ≫ sX) (Δ.restrictOpen U) := by
  classical
  haveI := hXp
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsNoetherian X := {}
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have hXn : IsNormalVariety ℂ sX := hQ.1
  have hQU := isQFactorial_restrictOpen hQ U
  obtain ⟨C, hC, hle⟩ := IsRealKltPair.exists_isKltPair_ge sX
    (AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ _) hQ hΔ0 hΔ
  obtain ⟨n, K, hK, -⟩ := hΔ.2.2.1
  have hKU : Divisor.IsCanonicalDivisor (U.ι ≫ sX) n (K.restrictOpen U) := hK.restrictOpen hXn U
  have hCm := (isKltPair_iff_mori_isKltPair sX hK hC.1).mp hC
  have hCmU := MMP.Mori.IsKltPair.restrictOpen U hCm
  have hCU : IsKltPair (U.ι ≫ sX) (C.restrictOpen U) :=
    (isKltPair_iff_mori_isKltPair (U.ι ≫ sX) hKU
      ⟨inferInstance, inferInstance, hCmU.1.isPair, fun W => hC.1.nonneg _⟩).mpr hCmU
  refine ⟨hXn.restrictOpen U, fun P => hΔ.2.1 _, ⟨n, K.restrictOpen U, hKU, hQU.isRCartier _⟩,
    pos_of_isLogDiscrepancy_of_le hQU (fun P => ?_) hCU.2⟩
  change Δ.coeff (primeDivisorMap U.ι P) ≤ ((C.coeff (primeDivisorMap U.ι P) : ℚ) : ℝ)
  exact hle _

end OpenKlt

/-! ### Relative nefness on open subschemes -/

section OpenNef

/-- The degree of a Cartier divisor along a curve only depends on the morphism. -/
private theorem degreeOn_congr_hom {X C : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {L : Divisor X} (hL : L.IsCartier)
    {i i' : C ⟶ X} (h : i = i') [IsProper (i ≫ sX)] [IsProper (i' ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) :
    L.degreeOn ℂ sX i hdim hL = L.degreeOn ℂ sX i' hdim hL := by
  subst h; rfl

/-- The degree of the restriction of a Cartier divisor to an open subscheme along a curve in it is
its degree along the curve in the ambient scheme. -/
private theorem degreeOn_restrictOpen {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] (U : X.Opens) [Nonempty U]
    [QuasiCompact (U.ι ≫ sX)] {L : Divisor X} (hL : L.IsCartier)
    (hLU : Divisor.IsCartier (L.restrictOpen U)) {C : Scheme.{0}} (i : C ⟶ U.toScheme)
    [IsProper (i ≫ U.ι ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) :
    haveI : IsProper ((i ≫ U.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
    Divisor.degreeOn (D := L.restrictOpen U) ℂ (U.ι ≫ sX) i hdim hLU =
      L.degreeOn ℂ sX (i ≫ U.ι) hdim hL := by
  haveI : IsProper ((i ≫ U.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ sX)
  haveI : IsDominant U.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion U.ι
  have hp := MMP.Flips.isPullback_restrictOpen U hL
  have := hL.isInvertibleModule_divisorialSheaf
  have := hLU.isInvertibleModule_divisorialSheaf
  change MMP.Mori.degreeOn ℂ (U.ι ≫ sX) i hdim (Divisor.divisorialSheaf (L.restrictOpen U)) =
    MMP.Mori.degreeOn ℂ sX (i ≫ U.ι) hdim L.divisorialSheaf
  rw [degreeOn_eq_of_iso ℂ (U.ι ≫ sX) i hdim
      (Divisor.IsPullback.divisorialSheafIso (hBc := hL) hp),
    degreeOn_pullback_eq_degreeOn_comp (U.ι ≫ sX) sX U.ι i rfl]

/-- **Relative nefness restricts to open subschemes over open subschemes of the base.** -/
private theorem isRelativelyNef_restrictOpen {X B T : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [IsSeparated sX]
    [QuasiCompact sX] {π : X ⟶ B} {j : T ⟶ B} (U : X.Opens) [Nonempty U]
    [QuasiCompact (U.ι ≫ sX)] {πU : U.toScheme ⟶ T} (hπU : πU ≫ j = U.ι ≫ π) {D : RDivisor X}
    (hD : MMP.Flips.IsRelativelyNef ℂ sX π D) :
    MMP.Flips.IsRelativelyNef ℂ (U.ι ≫ sX) πU (D.restrictOpen U) := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ sX)
  haveI : IsDominant U.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion U.ι
  obtain ⟨m, r, L, hL, hDL, hnef⟩ := hD
  have hLU : ∀ j, Divisor.IsCartier ((L j).restrictOpen U) := fun j =>
    isCartier_comapDivisor U.ι (hL j)
  refine ⟨m, r, fun j => (L j).restrictOpen U, hLU, ?_, fun C hC x hx => ?_⟩
  · rw [hDL]; exact comapDivisor_sum_smul_toRDivisor U.ι r L
  obtain ⟨Γ, e, hΓpt, he⟩ := MMP.Flips.exists_properCurve_of_opens sX U C
  obtain ⟨hL', d, hDeq, hd, hxd⟩ := hx
  refine hnef Γ ?_ x ⟨hL, d, hDL, fun j => ?_, hxd⟩
  · intro y hy
    rw [← MMP.Mori.ProperCurve.range_ι] at hy
    obtain ⟨z, rfl⟩ := hy
    have h1 : e.inv ≫ e.hom ≫ Γ.ι = e.inv ≫ C.ι ≫ U.ι := by rw [he]
    rw [Iso.inv_hom_id_assoc] at h1
    have hz := congrArg (fun g : Γ.scheme ⟶ X => g z) h1
    simp only [Scheme.Hom.comp_apply] at hz
    have hc : C.ι (e.inv z) ∈ closure {C.point} := by
      rw [← MMP.Mori.ProperCurve.range_ι]; exact ⟨_, rfl⟩
    have hπ : ∀ c, π (U.ι c) = j (πU c) := fun c => by
      rw [← Scheme.Hom.comp_apply, ← hπU, Scheme.Hom.comp_apply]
    rw [hz, hΓpt, hπ, hπ, hC _ hc]
  · obtain ⟨C', ν, hν, hdim, hdj⟩ := hd j
    haveI := hν.isFinite
    haveI := hν.isIntegral
    refine ⟨C', ν ≫ e.hom, ⟨hν.isIntegral, hν.isNormal, inferInstance, ?_⟩, hdim, ?_⟩
    · exact MMP.Fourfold.Crepant.isBirationalMorphism_comp hν.isBirationalMorphism
        (isBirationalMorphism_of_isIso e.hom)
    · haveI : IsProper ((ν ≫ C.ι) ≫ U.ι ≫ sX) := by
        rw [Category.assoc]; infer_instance
      haveI : IsProper (((ν ≫ C.ι) ≫ U.ι) ≫ sX) := by
        rw [Category.assoc, Category.assoc]; infer_instance
      haveI : IsProper (((ν ≫ e.hom) ≫ Γ.ι) ≫ sX) := by
        rw [Category.assoc]; infer_instance
      rw [hdj, degreeOn_restrictOpen U (hL j) (hLU j) (ν ≫ C.ι) hdim]
      exact degreeOn_congr_hom (hL j) (by rw [Category.assoc, Category.assoc, he]) hdim

end OpenNef

/-! ### Rational affine families of divisors and fixed parts on a common model -/

namespace OneModel

open MMP Filter Topology

section Families

variable {s : ℕ}

private theorem ratAffineForm_zero (t : Fin s → ℝ) : ratAffineForm (0 : (Fin s → ℚ) × ℚ) t = 0 := by
  simp [ratAffineForm]

private theorem ratAffineForm_add (f g : (Fin s → ℚ) × ℚ) (t : Fin s → ℝ) :
    ratAffineForm (f + g) t = ratAffineForm f t + ratAffineForm g t := by
  simp only [ratAffineForm, Prod.fst_add, Prod.snd_add, Pi.add_apply, Rat.cast_add, add_mul,
    Finset.sum_add_distrib]
  ring

private theorem ratAffineForm_smul (c : ℚ) (f : (Fin s → ℚ) × ℚ) (t : Fin s → ℝ) :
    ratAffineForm (c • f) t = c * ratAffineForm f t := by
  simp only [ratAffineForm, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
    Rat.cast_mul, mul_add, Finset.mul_sum, mul_assoc]

private theorem ratAffineForm_sub (f g : (Fin s → ℚ) × ℚ) (t : Fin s → ℝ) :
    ratAffineForm (f - g) t = ratAffineForm f t - ratAffineForm g t := by
  simp only [ratAffineForm, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, Rat.cast_sub, sub_mul,
    Finset.sum_sub_distrib]
  ring

private theorem ratAffineForm_const (q : ℚ) (t : Fin s → ℝ) :
    ratAffineForm ((0, q) : (Fin s → ℚ) × ℚ) t = q := by
  simp [ratAffineForm]

private theorem coeff_finset_sum {X : Scheme.{0}} {ι : Type*} (I : Finset ι)
    (f : ι → RDivisor X) (E : Mori.PrimeDivisor X) :
    (∑ i ∈ I, f i).coeff E = ∑ i ∈ I, (f i).coeff E :=
  map_sum (DivisorWithCoeffs.coeffAddMonoidHom E) f I

private theorem ratAffineForm_sum {ι : Type*} (I : Finset ι) (f : ι → (Fin s → ℚ) × ℚ)
    (t : Fin s → ℝ) : ratAffineForm (∑ i ∈ I, f i) t = ∑ i ∈ I, ratAffineForm (f i) t := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [ratAffineForm_zero]
  | insert i I hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ratAffineForm_add, ih]

/-- A family of real divisors whose coefficients are rational affine functions of the
parameter, all supported in one finite set of primes. -/
private def IsRatAffineFamily {X : Scheme.{0}} (F : (Fin s → ℝ) → RDivisor X) : Prop :=
  ∃ (S : Finset (Mori.PrimeDivisor X)) (β : Mori.PrimeDivisor X → (Fin s → ℚ) × ℚ),
    (∀ P ∉ S, β P = 0) ∧ ∀ t P, (F t).coeff P = ratAffineForm (β P) t

variable {X : Scheme.{0}}

private theorem isRatAffineFamily_of_coeff (F : (Fin s → ℝ) → RDivisor X) {n : ℕ}
    (PX : Fin n → Mori.PrimeDivisor X) (a : Fin n → (Fin s → ℚ) × ℚ)
    (hcoeff : ∀ t i, (F t).coeff (PX i) = ratAffineForm (a i) t)
    (hsupp : ∀ t, ↑(F t).support ⊆ Set.range PX) : IsRatAffineFamily F := by
  classical
  refine ⟨Finset.univ.image PX, fun P => if h : P ∈ Set.range PX then a h.choose else 0, ?_, ?_⟩
  · intro P hP
    have : P ∉ Set.range PX := fun ⟨i, hi⟩ => hP (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)
    simp [this]
  · intro t P
    by_cases h : P ∈ Set.range PX
    · dsimp only
      rw [dif_pos h, ← hcoeff t h.choose, h.choose_spec]
    · dsimp only
      rw [dif_neg h, ratAffineForm_zero]
      by_contra h0
      exact h (hsupp t (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 h0)))

private theorem IsRatAffineFamily.const_add {F : (Fin s → ℝ) → RDivisor X}
    (hF : IsRatAffineFamily F) (K : Divisor X) :
    IsRatAffineFamily (fun t => Divisor.toRDivisor K + F t) := by
  classical
  obtain ⟨S, β, hS, hβ⟩ := hF
  refine ⟨S ∪ K.support, fun P => β P + (0, (K.coeff P : ℚ)), fun P hP => ?_, fun t P => ?_⟩
  · rw [Finset.mem_union, not_or] at hP
    have hK : K.coeff P = 0 := Finsupp.notMem_support_iff.1 hP.2
    dsimp only
    rw [hS P hP.1, hK]
    simp
  · rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, hβ, ratAffineForm_add,
      ratAffineForm_const]
    push_cast
    ring

private theorem IsRatAffineFamily.sub {F G : (Fin s → ℝ) → RDivisor X}
    (hF : IsRatAffineFamily F) (hG : IsRatAffineFamily G) :
    IsRatAffineFamily (fun t => F t - G t) := by
  classical
  obtain ⟨S, β, hS, hβ⟩ := hF
  obtain ⟨S', γ, hS', hγ⟩ := hG
  refine ⟨S ∪ S', fun P => β P - γ P, fun P hP => ?_, fun t P => ?_⟩
  · rw [Finset.mem_union, not_or] at hP
    dsimp only
    rw [hS P hP.1, hS' P hP.2, sub_zero]
  · rw [DivisorWithCoeffs.coeff_sub, hβ, hγ, ratAffineForm_sub]

private theorem IsRatAffineFamily.exists_finset {F : (Fin s → ℝ) → RDivisor X}
    (hF : IsRatAffineFamily F) : ∃ S : Finset (Mori.PrimeDivisor X), ∀ t, (F t).support ⊆ S := by
  obtain ⟨S, β, hS, hβ⟩ := hF
  refine ⟨S, fun t P hP => ?_⟩
  by_contra h
  apply Finsupp.mem_support_iff.1 hP
  have := hβ t P
  rw [hS P h, ratAffineForm_zero] at this
  exact this

private theorem IsRatAffineFamily.exists_affineMap {F : (Fin s → ℝ) → RDivisor X}
    (hF : IsRatAffineFamily F) : ∃ L : (Fin s → ℝ) →ᵃ[ℝ] RDivisor X, ∀ t, L t = F t := by
  classical
  obtain ⟨S, β, hS, hβ⟩ := hF
  let ℓ : Mori.PrimeDivisor X → (Fin s → ℝ) →ₗ[ℝ] ℝ := fun P =>
    ∑ j, ((β P).1 j : ℝ) • LinearMap.proj j
  have hℓ : ∀ P v, ℓ P v = ∑ j, ((β P).1 j : ℝ) * v j := fun P v => by simp [ℓ]
  let lin : (Fin s → ℝ) →ₗ[ℝ] RDivisor X :=
    ∑ P ∈ S, LinearMap.smulRight (ℓ P) (Finsupp.single P (1 : ℝ))
  have hlin : ∀ v P, (lin v).coeff P = ℓ P v := fun v P => by
    simp only [lin, LinearMap.sum_apply, LinearMap.smulRight_apply, coeff_finset_sum,
      DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_apply, Finsupp.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']
    rw [Finsupp.finset_sum_apply]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq']
    split_ifs with hP
    · rfl
    · rw [hℓ, hS P hP]; simp
  refine ⟨⟨F, lin, fun t v => ?_⟩, fun t => rfl⟩
  ext P
  change (F (v + t)).coeff P = (lin v + F t).coeff P
  rw [DivisorWithCoeffs.coeff_add, hlin, hℓ, hβ, hβ]
  simp only [ratAffineForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

/-- A rational affine relation among the coefficients of `F δ` holds for `F t` along the
smallest rational affine hull of `δ`. -/
private theorem IsRatAffineFamily.relation {F : (Fin s → ℝ) → RDivisor X}
    (hF : IsRatAffineFamily F) {δ t : Fin s → ℝ} (ht : t ∈ rationalAffineHull δ)
    (c : Mori.PrimeDivisor X →₀ ℚ) (q : ℚ)
    (hc : (c.sum fun P cP => (cP : ℝ) * (F δ).coeff P) = q) :
    (c.sum fun P cP => (cP : ℝ) * (F t).coeff P) = q := by
  obtain ⟨S, β, hS, hβ⟩ := hF
  have key : ∀ u, (c.sum fun P cP => (cP : ℝ) * (F u).coeff P) =
      ratAffineForm (∑ P ∈ c.support, c P • β P) u := fun u => by
    rw [Finsupp.sum, ratAffineForm_sum]
    exact Finset.sum_congr rfl fun P _ => by rw [ratAffineForm_smul, hβ]
  rw [key] at hc ⊢
  have := mem_rationalAffineHull.1 ht (∑ P ∈ c.support, c P • β P - (0, q))
    (by rw [ratAffineForm_sub, hc, ratAffineForm_const, sub_self])
  rw [ratAffineForm_sub, ratAffineForm_const] at this
  linarith

private theorem IsRatAffineFamily.eventually_nonneg {F : (Fin s → ℝ) → RDivisor X}
    (hF : IsRatAffineFamily F) {V : Set (Fin s → ℝ)} (hV : IsRationalAffineSubspace V)
    {δ : Fin s → ℝ} (hδV : δ ∈ V) (hδ : 0 ≤ F δ) :
    (rationalAffineHull δ : Set (Fin s → ℝ)) ⊆ V ∧
      ∀ᶠ t in 𝓝[(rationalAffineHull δ : Set (Fin s → ℝ))] δ,
        0 ≤ F t ∧ (F t).support = (F δ).support := by
  obtain ⟨S, β, hS, hβ⟩ := hF
  refine exceptional_support_rational_hull (fun i => (S.equivFin.symm i : Mori.PrimeDivisor X))
    (fun i => β (S.equivFin.symm i)) F (fun t i => hβ t _) (fun t P hP => ?_) hV hδV hδ
  have hPS : P ∈ S := by
    by_contra h
    apply Finsupp.mem_support_iff.1 (Finset.mem_coe.1 hP)
    have := hβ t P
    rw [hS P h, ratAffineForm_zero] at this
    exact this
  exact ⟨S.equivFin ⟨P, hPS⟩, by simp⟩

/-- On a scheme on which every Weil divisor has a Cartier multiple, the pull-back of a rational
affine family along a dominant morphism is again a rational affine family. -/
private theorem IsRatAffineFamily.exists_isRCartierPullback [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X] {T : Scheme.{0}} [IsLocallyNoetherian T] [IsNormal T] [IsIntegral T]
    [CompactSpace T] {F : (Fin s → ℝ) → RDivisor X} (hF : IsRatAffineFamily F)
    (hQ : ∀ D : Divisor X, ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartier) (f : T ⟶ X)
    [IsDominant f] :
    ∃ G : (Fin s → ℝ) → RDivisor T, IsRatAffineFamily G ∧
      ∀ t, MMP.Flips.IsRCartierPullback f (F t) (G t) := by
  classical
  obtain ⟨S, β, hS, hβ⟩ := hF
  choose m hm hmC using fun P : Mori.PrimeDivisor X => hQ (Finsupp.single P 1)
  set L : Mori.PrimeDivisor X → Divisor X := fun P => (m P : ℤ) • Finsupp.single P 1 with hLdef
  set L' : Mori.PrimeDivisor X → Divisor T := fun P => (L P).pullback (hmC P)
    (map_componentGenericPoint_notMem_supp_of_isDominant f (L P)) with hL'def
  refine ⟨fun t => ∑ P ∈ S, (ratAffineForm (β P) t / m P) • Divisor.toRDivisor (L' P),
    ⟨S.biUnion fun P => (L' P).support,
      fun E => ∑ P ∈ S, (((L' P).coeff E : ℚ) / m P) • β P, fun E hE => ?_, fun t E => ?_⟩,
    fun t => ?_⟩
  · refine Finset.sum_eq_zero fun P hP => ?_
    have : (L' P).coeff E = 0 := by
      by_contra h
      exact hE (Finset.mem_biUnion.2 ⟨P, hP, Finsupp.mem_support_iff.2 h⟩)
    rw [this]
    simp
  · rw [ratAffineForm_sum, coeff_finset_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [ratAffineForm_smul, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
    push_cast
    ring
  · have hFt : F t = ∑ P ∈ S, (ratAffineForm (β P) t / m P) • Divisor.toRDivisor (L P) := by
      ext E
      change (F t).coeff E = (∑ P ∈ S, (ratAffineForm (β P) t / m P) •
        Divisor.toRDivisor (L P)).coeff E
      rw [coeff_finset_sum, hβ]
      have hterm : ∀ P ∈ S, ((ratAffineForm (β P) t / m P) • Divisor.toRDivisor (L P)).coeff E =
          if P = E then ratAffineForm (β P) t else 0 := fun P _ => by
        rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, hLdef]
        dsimp only
        rw [DivisorWithCoeffs.coeff_smul]
        by_cases hPE : P = E
        · subst hPE
          have : (m P : ℝ) ≠ 0 := by exact_mod_cast (hm P).ne'
          rw [if_pos rfl, DivisorWithCoeffs.coeff_single_self, smul_eq_mul, smul_eq_mul, mul_one,
            Int.cast_natCast]
          field_simp
        · rw [if_neg hPE, DivisorWithCoeffs.coeff_single_of_ne hPE]
          simp
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
      split_ifs with hE
      · rfl
      · rw [hS E hE, ratAffineForm_zero]
    rw [hFt]
    exact isRCartierPullback_sum S _ _ fun P _ => isRCartierPullback_smul _
      (isRCartierPullback_toRDivisor (hmC P) _ (Divisor.isPullback_pullback (hmC P) _))

end Families

/-! ### Convex geometry -/

section Convex

/-- If `Δ` lies in the algebraic relative interior of a convex set `C`, then from `Δ` one can
move a little towards every point of the affine span of `C` without leaving `C`. -/
private theorem exists_lineMap_mem_of_mem_affineSpan {M : Type*} [AddCommGroup M] [Module ℝ M]
    {C : Set M} (hC : Convex ℝ C) {Δ : M} (hΔ : Δ ∈ C)
    (hrel : ∀ x ∈ C, ∃ ε : ℝ, 0 < ε ∧ Δ + ε • (Δ - x) ∈ C) {y : M}
    (hy : y ∈ affineSpan ℝ C) : ∃ ε : ℝ, 0 < ε ∧ AffineMap.lineMap Δ y ε ∈ C := by
  -- the directions along which one can leave `Δ` inside `C`
  let K : Set M := {u | ∃ ε : ℝ, 0 < ε ∧ Δ + ε • u ∈ C}
  have shrink : ∀ {u : M} {ε : ℝ}, 0 < ε → Δ + ε • u ∈ C → ∀ ε', 0 ≤ ε' → ε' ≤ ε →
      Δ + ε' • u ∈ C := fun {u ε} hε hu ε' h0 h1 => by
    have := hC.add_smul_sub_mem hΔ hu ⟨div_nonneg h0 hε.le, (div_le_one hε).2 h1⟩
    rwa [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hε.ne'] at this
  have hadd : ∀ u v, u ∈ K → v ∈ K → u + v ∈ K := by
    rintro u v ⟨ε₁, hε₁, hu⟩ ⟨ε₂, hε₂, hv⟩
    set ε := min ε₁ ε₂
    have hε : 0 < ε := lt_min hε₁ hε₂
    have hu' := shrink hε₁ hu ε hε.le (min_le_left _ _)
    have hv' := shrink hε₂ hv ε hε.le (min_le_right _ _)
    refine ⟨ε / 2, half_pos hε, ?_⟩
    have := hC hu' hv' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    convert this using 1
    module
  have hsmul : ∀ (c : ℝ) u, 0 < c → u ∈ K → c • u ∈ K := by
    rintro c u hc ⟨ε, hε, hu⟩
    exact ⟨ε / c, div_pos hε hc, by rwa [smul_smul, div_mul_cancel₀ _ hc.ne']⟩
  have hzero : (0 : M) ∈ K := ⟨1, one_pos, by simpa using hΔ⟩
  -- every vector of the span, and its negative, is such a direction
  have hdir : y -ᵥ Δ ∈ vectorSpan ℝ C := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction hy (subset_affineSpan ℝ C hΔ)
  rw [vectorSpan_eq_span_vsub_set_right ℝ hΔ] at hdir
  have key : ∀ u ∈ Submodule.span ℝ ((· -ᵥ Δ) '' C), u ∈ K ∧ -u ∈ K := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      refine ⟨⟨1, one_pos, by simpa using hx⟩, ?_⟩
      obtain ⟨ε, hε, h⟩ := hrel x hx
      exact ⟨ε, hε, by simpa [vsub_eq_sub, neg_sub] using h⟩
    | zero => exact ⟨hzero, by simpa using hzero⟩
    | add u v _ _ hu hv => exact ⟨hadd u v hu.1 hv.1, by rw [neg_add]; exact hadd _ _ hu.2 hv.2⟩
    | smul c u _ hu =>
      rcases lt_trichotomy c 0 with hc | rfl | hc
      · refine ⟨?_, ?_⟩
        · rw [show c • u = (-c) • -u by simp]; exact hsmul _ _ (neg_pos.2 hc) hu.2
        · rw [show -(c • u) = (-c) • u by simp]; exact hsmul _ _ (neg_pos.2 hc) hu.1
      · rw [zero_smul, neg_zero]; exact ⟨hzero, hzero⟩
      · exact ⟨hsmul c u hc hu.1, by rw [← smul_neg]; exact hsmul c _ hc hu.2⟩
  obtain ⟨ε, hε, h⟩ := (key _ hdir).1
  refine ⟨ε, hε, ?_⟩
  rw [AffineMap.lineMap_apply_module', add_comm]
  simpa [vsub_eq_sub] using h

/-- A convex set containing `δ` which absorbs every direction of the smallest rational affine
hull `W` of `δ` is a neighbourhood of `δ` in `W`. -/
private theorem mem_nhdsWithin_rationalAffineHull_of_convex {s : ℕ} {U : Set (Fin s → ℝ)}
    (hU : Convex ℝ U) {δ : Fin s → ℝ} (hδ : δ ∈ U)
    (habs : ∀ t ∈ rationalAffineHull δ, ∃ ε : ℝ, 0 < ε ∧ AffineMap.lineMap δ t ε ∈ U) :
    U ∈ 𝓝[(rationalAffineHull δ : Set (Fin s → ℝ))] δ := by
  classical
  obtain ⟨m, p, e, hind, -, hchar⟩ := exists_rational_frame δ
  let pR : Fin s → ℝ := fun j => (p j : ℝ)
  have hindR : LinearIndependent ℝ (fun i => fun j => (e i j : ℝ)) :=
    linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℝ) (v := e) |>.2 hind
  let Φlin : (Fin m → ℝ) →ₗ[ℝ] (Fin s → ℝ) :=
    Fintype.linearCombination ℝ (fun i j => (e i j : ℝ))
  have hΦinj : Function.Injective Φlin := hindR.fintypeLinearCombination_injective
  obtain ⟨Ψ, hΨ⟩ := Φlin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hΦinj)
  have hΨc : Continuous Ψ := LinearMap.continuous_of_finiteDimensional Ψ
  let φA : (Fin m → ℝ) →ᵃ[ℝ] (Fin s → ℝ) := Φlin.toAffineMap + AffineMap.const ℝ _ pR
  have hφA : ∀ σ, φA σ = Φlin σ + pR := fun σ => rfl
  have hchar' : ∀ x, x ∈ rationalAffineHull δ ↔ ∃ σ, x = φA σ := fun x => by
    rw [hchar]
    refine exists_congr fun σ => ?_
    rw [hφA]
    constructor <;> intro h <;> rw [h] <;> ext j <;>
      simp [Φlin, pR, Fintype.linearCombination_apply, add_comm]
  have hΨφ : ∀ σ, Ψ (φA σ - pR) = σ := fun σ => by
    rw [hφA, add_sub_cancel_right]; exact LinearMap.congr_fun hΨ σ
  obtain ⟨σ₀, hσ₀⟩ := (hchar' δ).1 (self_mem_rationalAffineHull δ)
  -- the problem in the parameter space `ℝ^m`
  set U' : Set (Fin m → ℝ) := φA ⁻¹' U with hU'def
  have hU' : Convex ℝ U' := hU.affine_preimage φA
  have habs' : ∀ σ, ∃ ε : ℝ, 0 < ε ∧ AffineMap.lineMap σ₀ σ ε ∈ U' := fun σ => by
    obtain ⟨ε, hε, h⟩ := habs (φA σ) ((hchar' _).2 ⟨σ, rfl⟩)
    exact ⟨ε, hε, by rw [hU'def, Set.mem_preimage, AffineMap.apply_lineMap, ← hσ₀]; exact h⟩
  have hσ₀U : σ₀ ∈ U' := by rw [hU'def, Set.mem_preimage, ← hσ₀]; exact hδ
  have hspan : affineSpan ℝ U' = ⊤ := by
    refine eq_top_iff.2 fun σ _ => ?_
    obtain ⟨ε, hε, h⟩ := habs' σ
    have := AffineMap.lineMap_mem (1 / ε) (subset_affineSpan ℝ U' hσ₀U) (subset_affineSpan ℝ U' h)
    convert this using 1
    rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module', add_sub_cancel_right,
      smul_smul, one_div, inv_mul_cancel₀ hε.ne', one_smul, sub_add_cancel]
  obtain ⟨y, hy⟩ := (hU'.interior_nonempty_iff_affineSpan_eq_top).2 hspan
  have hint : σ₀ ∈ interior U' := by
    obtain ⟨ε, hε, hz⟩ := habs' (σ₀ + (σ₀ - y))
    have hcomb := hU'.combo_interior_self_mem_interior hy hz (a := ε / (1 + ε)) (b := 1 / (1 + ε))
      (by positivity) (by positivity) (by field_simp; ring)
    convert hcomb using 1
    rw [AffineMap.lineMap_apply_module']
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  -- back to `W`
  have hO : {x | Ψ (x - pR) ∈ interior U'} ∈ 𝓝 δ := by
    refine (isOpen_interior.preimage (hΨc.comp (continuous_id.sub continuous_const))).mem_nhds ?_
    show Ψ (δ - pR) ∈ interior U'
    rw [hσ₀, hΨφ]; exact hint
  refine mem_of_superset (inter_mem (nhdsWithin_le_nhds hO) self_mem_nhdsWithin) ?_
  rintro x ⟨hx, hxW⟩
  obtain ⟨σ, rfl⟩ := (hchar' x).1 hxW
  have : σ ∈ U' := interior_subset (by simpa only [Set.mem_setOf_eq, hΨφ] using hx)
  exact this

/-- The real affine span of finitely many rational divisors is cut out by rational affine
relations: a real divisor satisfying every rational relation of a point of the span lies in it. -/
private theorem mem_affineSpan_of_forall_relation {Y : Scheme.{0}} (VQ : Finset (QDivisor Y))
    {Δ Φ : RDivisor Y} (hΔ : Δ ∈ affineSpan ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))))
    (hΦ : ∀ (c : Mori.PrimeDivisor Y →₀ ℚ) (q : ℚ),
      (c.sum fun P cP => (cP : ℝ) * Δ.coeff P) = q → (c.sum fun P cP => (cP : ℝ) * Φ.coeff P) = q) :
    Φ ∈ affineSpan ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))) := by
  classical
  set R := QDivisor.toRDivisor (X := Y) with hRdef
  obtain ⟨v₀, hv₀⟩ : VQ.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    simp only [Finset.coe_empty, Set.image_empty, AffineSubspace.span_empty] at hΔ
    exact AffineSubspace.notMem_bot ℝ _ Δ hΔ
  have hRv₀ : R v₀ ∈ R '' (VQ : Set (QDivisor Y)) := Set.mem_image_of_mem R hv₀
  set Ssupp : Finset (Mori.PrimeDivisor Y) := Δ.support ∪ VQ.biUnion fun v => v.support
  have hRsupp : ∀ v ∈ VQ, (R v).support ⊆ Ssupp := fun v hv P hP => by
    have : v.coeff P ≠ 0 := fun h0 => Finsupp.mem_support_iff.1 hP (by
      change (R v).coeff P = 0
      rw [hRdef, QDivisor.coeff_toRDivisor, h0, Rat.cast_zero])
    exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨v, hv, Finsupp.mem_support_iff.2 this⟩)
  -- the support of `Φ` lies in that of `Δ`
  have hΦsupp : Φ.support ⊆ Δ.support := fun P hP => by
    by_contra h
    have h0 : Δ.coeff P = 0 := Finsupp.notMem_support_iff.1 h
    have := hΦ (Finsupp.single P 1) 0 (by rw [Finsupp.sum_single_index (by simp)]; simp [h0])
    rw [Finsupp.sum_single_index (by simp)] at this
    have h2 : Φ.coeff P = 0 := by simpa using this
    exact Finsupp.mem_support_iff.1 hP h2
  let ι := {P // P ∈ Ssupp}
  have hrel : ∀ (c : ι → ℚ) (D : RDivisor Y),
      ((∑ i : ι, Finsupp.single (i : Mori.PrimeDivisor Y) (c i)).sum fun P cP =>
        (cP : ℝ) * D.coeff P) = ∑ i : ι, (c i : ℝ) * D.coeff i := fun c D => by
    rw [← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
    exact Finset.sum_congr rfl fun i _ => Finsupp.sum_single_index (by simp)
  let lam : (ι → ℚ) → RDivisor Y →ₗ[ℝ] ℝ := fun c =>
    ∑ i : ι, (c i : ℝ) • Finsupp.lapply (i : Mori.PrimeDivisor Y)
  have hlam : ∀ c D, lam c D = ∑ i : ι, (c i : ℝ) * D.coeff i := fun c D => by
    simp [lam, DivisorWithCoeffs.coeff_apply]
  -- the rational system of the direction of the span
  let w : VQ → ι → ℚ := fun v i => v.1.coeff i - v₀.coeff i
  let Φsys : Set (ι → ℚ) := {c | ∀ v : VQ, ∑ i, c i * w v i = 0}
  let x : ι → ℝ := fun i => (Φ - R v₀).coeff i
  have hx : ∀ c ∈ Φsys, ∑ i, (c i : ℝ) * x i = 0 := by
    intro c hc
    have hker : vectorSpan ℝ (R '' (VQ : Set (QDivisor Y))) ≤ LinearMap.ker (lam c) := by
      rw [vectorSpan_eq_span_vsub_set_right ℝ hRv₀, Submodule.span_le]
      rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub, hlam, hRdef,
        DivisorWithCoeffs.coeff_sub, QDivisor.coeff_toRDivisor]
      have h' : ((∑ i, c i * w ⟨v, hv⟩ i : ℚ) : ℝ) = 0 := by rw [hc ⟨v, hv⟩]; simp
      push_cast [w] at h'
      rw [← h']
    have hΔdir : Δ -ᵥ R v₀ ∈ vectorSpan ℝ (R '' (VQ : Set (QDivisor Y))) := by
      rw [← direction_affineSpan]
      exact AffineSubspace.vsub_mem_direction hΔ (subset_affineSpan ℝ _ hRv₀)
    have h1 : lam c Δ = lam c (R v₀) := by
      have := hker hΔdir
      rwa [LinearMap.mem_ker, vsub_eq_sub, map_sub, sub_eq_zero] at this
    set q : ℚ := ∑ i : ι, c i * v₀.coeff i with hqdef
    have hq : lam c (R v₀) = q := by
      rw [hlam, hqdef]; push_cast; simp [hRdef, QDivisor.coeff_toRDivisor]
    have h2 := hΦ (∑ i : ι, Finsupp.single (i : Mori.PrimeDivisor Y) (c i)) q
      (by rw [hrel, ← hlam, h1, hq])
    rw [hrel, ← hlam, ← hq] at h2
    have : ∑ i, (c i : ℝ) * x i = lam c Φ - lam c (R v₀) := by
      rw [hlam, hlam, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [x, DivisorWithCoeffs.coeff_sub]; ring
    rw [this, h2, sub_self]
  have hxspan := mem_span_rational_solutions Φsys x hx
  -- the rational solutions lie in the span of the `w v`
  have hsol : ∀ y : ι → ℚ, (∀ c ∈ Φsys, ∑ i, c i * y i = 0) →
      y ∈ Submodule.span ℚ (Set.range w) := by
    intro y hy
    have hdot : ∀ (φ : Module.Dual ℚ (ι → ℚ)) (z : ι → ℚ),
        φ z = ∑ i, φ (Pi.single i 1) * z i := fun φ z => by
      rw [LinearMap.pi_apply_eq_sum_univ φ z]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul, mul_comm]
      congr 2
      ext j
      simp [Pi.single_apply, eq_comm]
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := Submodule.span ℚ (Set.range w)),
      Submodule.mem_dualCoannihilator]
    intro φ hφ
    have hc : (fun i => φ (Pi.single i 1)) ∈ Φsys := fun v => by
      rw [← hdot]
      exact (Submodule.mem_dualAnnihilator _).1 hφ _ (Submodule.subset_span ⟨v, rfl⟩)
    rw [hdot]
    exact hy _ hc
  have hcast : ∀ y ∈ Submodule.span ℚ (Set.range w),
      (fun i => (y i : ℝ)) ∈ Submodule.span ℝ (Set.range fun v i => (w v i : ℝ)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, rfl⟩ := hz
      exact Submodule.subset_span ⟨v, rfl⟩
    | zero =>
      convert Submodule.zero_mem _ using 1
      ext; simp
    | add a b _ _ ha hb =>
      convert Submodule.add_mem _ ha hb using 1
      ext; simp
    | smul q a _ ha =>
      convert Submodule.smul_mem _ (q : ℝ) ha using 1
      ext; simp [Rat.smul_def]
  have hxW : x ∈ Submodule.span ℝ (Set.range fun v i => (w v i : ℝ)) := by
    refine Submodule.span_le.2 ?_ hxspan
    rintro _ ⟨y, hy, rfl⟩
    exact hcast y (hsol y hy)
  -- back to divisors
  let ℓ : (ι → ℝ) →ₗ[ℝ] RDivisor Y :=
    ∑ i : ι, LinearMap.smulRight (LinearMap.proj i) (Finsupp.single (i : Mori.PrimeDivisor Y) 1)
  have hℓ : ∀ D : RDivisor Y, D.support ⊆ Ssupp → ℓ (fun i => D.coeff i) = D := fun D hD => by
    simp only [ℓ, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
    rw [Finset.sum_coe_sort Ssupp (fun P => D.coeff P • Finsupp.single P (1 : ℝ))]
    conv_rhs => rw [← Finsupp.sum_single D]
    rw [Finsupp.sum_of_support_subset D hD _ (fun _ _ => Finsupp.single_zero _)]
    exact Finset.sum_congr rfl fun P _ => Finsupp.smul_single_one _ _
  have hℓw : ∀ v : VQ, ℓ (fun i => (w v i : ℝ)) = R v - R v₀ := fun v => by
    rw [← hℓ (R v - R v₀) (Finsupp.support_sub.trans
      (Finset.union_subset (hRsupp v v.2) (hRsupp v₀ hv₀)))]
    congr 1
    ext i
    simp [w, hRdef, DivisorWithCoeffs.coeff_sub, QDivisor.coeff_toRDivisor]
  have hℓx : ℓ x = Φ - R v₀ := hℓ _ (Finsupp.support_sub.trans
    (Finset.union_subset (hΦsupp.trans Finset.subset_union_left) (hRsupp v₀ hv₀)))
  have hdir : Φ - R v₀ ∈ vectorSpan ℝ (R '' (VQ : Set (QDivisor Y))) := by
    rw [← hℓx]
    have : Submodule.map ℓ (Submodule.span ℝ (Set.range fun v i => (w v i : ℝ))) ≤
        vectorSpan ℝ (R '' (VQ : Set (QDivisor Y))) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨v, rfl⟩
      rw [hℓw]
      exact vsub_mem_vectorSpan ℝ (Set.mem_image_of_mem R v.2) hRv₀
    exact this (Submodule.mem_map_of_mem hxW)
  have := AffineSubspace.vadd_mem_of_mem_direction (by rwa [direction_affineSpan])
    (subset_affineSpan ℝ _ hRv₀)
  simpa [vadd_eq_add] using this

end Convex

/-! ### Divisor bookkeeping -/

section Bookkeeping

variable {X Y : Scheme.{0}}

private theorem toRDivisor_injective : Function.Injective (Divisor.toRDivisor (X := X)) :=
  fun D D' h => Finsupp.ext fun E => by
    have := congrArg (fun D : RDivisor X => D.coeff E) h
    simp only [Divisor.coeff_toRDivisor] at this
    exact_mod_cast this

private theorem toRDivisor_single (P : Mori.PrimeDivisor X) (r : ℤ) :
    Divisor.toRDivisor (Finsupp.single P r) = Finsupp.single P (r : ℝ) := by
  classical
  ext E
  rw [Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
    Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp

/-- The birational transform commutes with regarding an integral divisor as a real one. -/
private theorem toRDivisor_transformDivisor (φ : X.RationalMap Y) (D : Divisor X) :
    Divisor.toRDivisor (RationalMap.transformDivisor φ D) =
      RationalMap.transformDivisor φ (Divisor.toRDivisor D) := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add D D' h h' => simp only [map_add, h, h']
  | single P r =>
    rw [toRDivisor_single, RationalMap.transformDivisor_single,
      RationalMap.transformDivisor_single]
    cases RationalMap.transformPrimeDivisor φ P with
    | none => exact map_zero _
    | some E => exact toRDivisor_single E r

private theorem transformDivisor_smul (φ : X.RationalMap Y) (c : ℝ) (D : RDivisor X) :
    RationalMap.transformDivisor φ (c • D) = c • RationalMap.transformDivisor φ D :=
  (RationalMap.transformDivisorₗ ℝ φ).map_smul c D

private theorem isRCartier_of_isRCartierPullback [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {D : RDivisor X} {G : RDivisor Y}
    (h : MMP.Flips.IsRCartierPullback f D G) : RDivisor.IsRCartier D := by
  obtain ⟨m, r, L, L', hL, rfl, -, -⟩ := h
  exact ⟨m, r, L, hL, fun P => coeff_sum_smul_toRDivisor r L P⟩

/-- On a scheme on which every Weil divisor has a Cartier multiple, one positive integer makes
every divisor supported in a fixed finite set Cartier. -/
private theorem exists_zsmul_isCartier [IsLocallyNoetherian X] [IsNormal X]
    (hQ : ∀ D : Divisor X, ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartier)
    (S : Finset (Mori.PrimeDivisor X)) :
    ∃ e : ℕ, 0 < e ∧ ∀ C : Divisor X, C.support ⊆ S → ((e : ℤ) • C).IsCartier := by
  classical
  choose m hm hmC using fun P : Mori.PrimeDivisor X => hQ (Finsupp.single P 1)
  refine ⟨∏ P ∈ S, m P, Finset.prod_pos fun P _ => hm P, fun C hC => ?_⟩
  have hCsum : C = ∑ P ∈ S, C P • Finsupp.single P 1 := by
    conv_lhs => rw [← Finsupp.sum_single C]
    rw [Finsupp.sum_of_support_subset C hC _ (fun _ _ => Finsupp.single_zero _)]
    exact Finset.sum_congr rfl fun P _ => (Finsupp.smul_single_one _ _).symm
  have hterm : ∀ P ∈ S, ((∏ Q ∈ S, m Q : ℕ) : ℤ) • (C P • Finsupp.single P (1 : ℤ)) =
      (C P * ∏ Q ∈ S.erase P, (m Q : ℤ)) • ((m P : ℤ) • Finsupp.single P 1) := fun P hP => by
    rw [smul_smul, smul_smul, ← Finset.mul_prod_erase S m hP]
    congr 1
    push_cast
    ring
  have hsum : ∀ (I : Finset (Mori.PrimeDivisor X)) (g : Mori.PrimeDivisor X → ℤ),
      Divisor.IsCartier (∑ P ∈ I, g P • ((m P : ℤ) • (Finsupp.single P 1 : Divisor X))) := by
    intro I g
    induction I using Finset.induction_on with
    | empty => simpa using Divisor.isCartier_zero
    | insert P I hP ih =>
      rw [Finset.sum_insert hP]
      exact ((hmC P).zsmul _).add ih
  rw [hCsum, Finset.smul_sum, Finset.sum_congr rfl hterm]
  exact hsum S _

end Bookkeeping

/-! ### Uniform freeness on `Y` -/

section Freeness

variable {Y Z : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- On a klt pair every boundary coefficient is `< 1`: the log discrepancy `1 - b_P` of a prime
divisor `P` of `Y` is positive. -/
private theorem coeff_lt_one_of_isKltPair {Θ : QDivisor Y} (hΘ : IsKltPair sY Θ)
    (P : MMP.Mori.PrimeDivisor Y) : Θ.coeff P < 1 := by
  obtain ⟨hvar, n, K, hK, -⟩ := id hΘ.1.isPair
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hΘ.1.isPair hK
    (DivisorOver.ofPrimeDivisor ℂ hvar P)
  have hp : IsProper (DivisorOver.ofPrimeDivisor ℂ hvar P).f := by
    change IsProper (𝟙 Y); infer_instance
  have h := hΘ.2 n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha hp)
  rw [IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hvar ha] at h
  push_cast at h
  exact_mod_cast (by linarith : ((Θ.coeff P : ℚ) : ℝ) < 1)

/-- The coefficients of `∑ᵢ xᵢ Pᵢ` for distinct primes `Pᵢ`. -/
private theorem coeff_sum_single {R : Type*} [AddCommMonoid R] {r : ℕ}
    {pr : Fin r → MMP.Mori.PrimeDivisor Y} (hpr : Function.Injective pr) (x : Fin r → R) :
    (∀ j, DivisorWithCoeffs.coeff (∑ i, Finsupp.single (pr i) (x i)) (pr j) = x j) ∧
      ∀ P, P ∉ Set.range pr → DivisorWithCoeffs.coeff (∑ i, Finsupp.single (pr i) (x i)) P = 0 := by
  classical
  refine ⟨fun j => ?_, fun P hP => ?_⟩
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply,
      Finset.sum_eq_single j (fun i _ hij => Finsupp.single_eq_of_ne' (hpr.ne hij))
        (fun h => absurd (Finset.mem_univ j) h), Finsupp.single_eq_same]
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
    exact Finset.sum_eq_zero fun i _ => Finsupp.single_eq_of_ne' fun h => hP ⟨i, h⟩

/-- The uniform freeness theorem, applied to a rational klt polytope around a real klt
boundary `Δ` containing a relatively big `G`. -/
private theorem exists_uniform_freeness (hYQ : IsQFactorial sY)
    (hYp : Mori.IsProjectiveVariety ℂ sY) (hZp : Mori.IsProjectiveVariety ℂ sZ)
    (fY : Y ⟶ Z) (hfY : fY ≫ sZ = sY) {KY : Divisor Y}
    (hKY : ∃ m : ℕ, KY.IsCanonicalDivisor sY m) {Δ : RDivisor Y} (hΔ0 : 0 ≤ Δ)
    (hΔklt : IsRealKltPair sY Δ) {G : QDivisor Y} (hG0 : 0 ≤ G) (hGbig : G.IsRelativelyBig fY)
    (hGΔ : QDivisor.toRDivisor G ≤ Δ)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sY fY (Divisor.toRDivisor KY + Δ)) :
    ∃ VQ : Finset (QDivisor Y),
      Δ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))) ∧
      (∀ Γ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))), ∃ ε : ℝ, 0 < ε ∧
          Δ + ε • (Δ - Γ) ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y)))) ∧
      (∃ b : ℕ, 0 < b ∧
        ∀ Γ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))), ∀ c : ℝ, 0 < c →
          ∀ D : Divisor Y, D.IsCartier → c • (Divisor.toRDivisor KY + Γ) = Divisor.toRDivisor D →
            IsRelativelyFreeDivisor fY ((b : ℤ) • D)) ∧
      ∃ H : Finset (Divisor Y),
        (∀ h ∈ H, h.IsCartier ∧ ∃ p : ℕ, 0 < p ∧ IsRelativelyFreeDivisor fY ((p : ℤ) • h)) ∧
        ∀ Γ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))),
          ∃ t : Divisor Y → ℝ, (∀ h, 0 ≤ t h) ∧
            Divisor.toRDivisor KY + Γ = ∑ h ∈ H, t h • Divisor.toRDivisor h := by
  classical
  have : AlgebraicGeometry.IsProjectiveVariety ℂ sY := hYp
  have : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZp
  -- coordinates on the primes of the supports of `Δ` and `G`
  set S : Finset (Mori.PrimeDivisor Y) := Δ.support ∪ G.support with hSdef
  let pr : Fin S.card → Mori.PrimeDivisor Y := fun i => (S.equivFin.symm i : Mori.PrimeDivisor Y)
  have hpr : Function.Injective pr := Subtype.val_injective.comp S.equivFin.symm.injective
  have hprS : ∀ P ∈ S, P ∈ Set.range pr := fun P hP => ⟨S.equivFin ⟨P, hP⟩, by simp [pr]⟩
  have hGS : ∀ P, P ∉ Set.range pr → G.coeff P = 0 := fun P hP => by
    by_contra h
    exact hP (hprS P (Finset.mem_union_right _ (Finsupp.mem_support_iff.2 h)))
  have hΔS : ∀ P, P ∉ Set.range pr → Δ.coeff P = 0 := fun P hP => by
    by_contra h
    exact hP (hprS P (Finset.mem_union_left _ (Finsupp.mem_support_iff.2 h)))
  obtain ⟨V, -, hint, hVG, hVklt⟩ := exists_rationalPolytope_isKltPair_of_isRealKltPair sY hYp
    hYQ Δ hΔ0 hΔklt G hG0 hGΔ pr hpr
    (fun P hP => by_contra fun h => hP (hΔS P h)) (fun P hP => by_contra fun h => hP (hGS P h))
  -- the vertices as `ℚ`-divisors
  let toQ : (Fin S.card → ℚ) → QDivisor Y := fun v => ∑ i, Finsupp.single (pr i) (v i)
  have hGv : ∀ v ∈ V, ∀ i, G.coeff (pr i) ≤ v i := fun v hv i => by
    have := hVG _ (subset_convexHull ℝ _ ⟨v, hv, rfl⟩) i
    simp only at this
    exact_mod_cast this
  let V0 := V.image toQ
  have hV0 : ∀ Γ ∈ V0, ∃ v ∈ V, Γ = toQ v := fun Γ hΓ => by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hΓ
    exact ⟨v, hv, rfl⟩
  have hV0G : ∀ Γ ∈ V0, G ≤ Γ := fun Γ hΓ P => by
    obtain ⟨v, hv, rfl⟩ := hV0 Γ hΓ
    by_cases hP : P ∈ Set.range pr
    · obtain ⟨i, rfl⟩ := hP
      have := (coeff_sum_single hpr v).1 i
      change G.coeff (pr i) ≤ (toQ v).coeff (pr i)
      rw [this]; exact hGv v hv i
    · change G.coeff P ≤ (toQ v).coeff P
      rw [hGS P hP, (coeff_sum_single hpr v).2 P hP]
  have hV0klt : ∀ Γ ∈ V0, IsKltPair sY Γ := fun Γ hΓ => by
    obtain ⟨v, hv, rfl⟩ := hV0 Γ hΓ
    exact hVklt v hv
  have hV0eff : ∀ Γ ∈ V0, Γ.IsEffective := fun Γ hΓ E => (hG0 E).trans (hV0G Γ hΓ E)
  have hV0le : ∀ Γ ∈ V0, ∀ E, Γ.coeff E ≤ 1 := fun Γ hΓ E =>
    (coeff_lt_one_of_isKltPair (hV0klt Γ hΓ) E).le
  -- `Δ` lies in the convex hull of the vertices
  let Lm : (Fin S.card → ℝ) →ₗ[ℝ] RDivisor Y :=
    ∑ i, LinearMap.smulRight (LinearMap.proj i) (Finsupp.single (pr i) (1 : ℝ))
  have hLm : ∀ x, Lm x = ∑ i, Finsupp.single (pr i) (x i) := fun x => by
    simp only [Lm, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
    exact Finset.sum_congr rfl fun i _ => Finsupp.smul_single_one _ _
  have hLmv : ∀ v, Lm (fun i => (v i : ℝ)) = QDivisor.toRDivisor (toQ v) := fun v => by
    rw [hLm]
    ext P
    change DivisorWithCoeffs.coeff (∑ i, Finsupp.single (pr i) (v i : ℝ)) P =
      (QDivisor.toRDivisor (toQ v)).coeff P
    rw [QDivisor.coeff_toRDivisor]
    by_cases hP : P ∈ Set.range pr
    · obtain ⟨j, rfl⟩ := hP
      rw [(coeff_sum_single hpr _).1 j, (coeff_sum_single hpr v).1 j]
    · rw [(coeff_sum_single hpr _).2 P hP, (coeff_sum_single hpr v).2 P hP, Rat.cast_zero]
  have hLmΔ : Lm (fun i => Δ.coeff (pr i)) = Δ := by
    rw [hLm]
    ext P
    change DivisorWithCoeffs.coeff (∑ i, Finsupp.single (pr i) (Δ.coeff (pr i))) P = Δ.coeff P
    by_cases hP : P ∈ Set.range pr
    · obtain ⟨j, rfl⟩ := hP
      rw [(coeff_sum_single hpr _).1 j]
    · rw [(coeff_sum_single hpr _).2 P hP, hΔS P hP]
  have hΔconv : Δ ∈ convexHull ℝ (QDivisor.toRDivisor '' (V0 : Set (QDivisor Y))) := by
    have : Δ ∈ Lm '' convexHull ℝ ((fun v i => (v i : ℝ)) '' (V : Set (Fin S.card → ℚ))) :=
      ⟨_, intrinsicInterior_subset hint, hLmΔ⟩
    rw [LinearMap.image_convexHull, Set.image_image] at this
    convert this using 2
    ext D
    simp only [V0, Finset.coe_image, Set.mem_image, exists_exists_and_eq_and, hLmv]
  obtain ⟨VQ, -, -, hΔVQ, hrel, hb, H, hH, hcone⟩ :=
    QDivisor.IsRelativelyBig.exists_isRelativelyFreeDivisor_nsmul_of_isRelativelyNef sY sZ hYQ
      fY hfY hKY hGbig (fun E => hG0 E) V0 hV0eff hV0le hV0G hV0klt hΔconv hnef
  exact ⟨VQ, hΔVQ, hrel, hb, H, hH, hcone⟩

end Freeness

/-! ### Fixed parts on the common model -/

section CommonModel

variable {k : Type} [Field k] {X Y T Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
  [IsIntegral X] [IsIntegral Y] [IsIntegral T]
  [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
  [IsLocallyNoetherian T] [IsNormal T] [CompactSpace X] [CompactSpace Y] [CompactSpace T]

/-- Let `p : T ⟶ X`, `q : T ⟶ Y` be a common model over `Z`, and let `E = p^*D - q^*D'` be
effective with `q_*E = 0`. If `C` is an integral Cartier divisor with `C = c • D` whose
counterpart `C' = c • D'` on `Y` is Cartier and relatively free, then every fixed component of
`C` over `Z` is a component of `p_*E`. -/
private theorem pos_transformDivisor_of_pos_relativeFixedMultiplicity
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) (hT : IsNormalVariety k sT)
    (hZ : Mori.IsVariety k sZ) (p : T ⟶ X) (q : T ⟶ Y) (fX : X ⟶ Z) (fY : Y ⟶ Z)
    [IsProper p] [IsProper q] (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q)
    (hpX : p ≫ sX = sT) (hqY : q ≫ sY = sT) (hfX : fX ≫ sZ = sX) (hfY : fY ≫ sZ = sY)
    (hZc : p ≫ fX = q ≫ fY) {D : RDivisor X} {D' : RDivisor Y} {PD QD : RDivisor T}
    (hPD : MMP.Flips.IsRCartierPullback p D PD) (hQD : MMP.Flips.IsRCartierPullback q D' QD)
    (hE0 : 0 ≤ PD - QD)
    (hqE : RationalMap.transformDivisor (X := T) q.toRationalMap (PD - QD) = 0)
    {c : ℝ} (hc : 0 < c) {C : Divisor X} (hC : C.IsCartier)
    (hCD : Divisor.toRDivisor C = c • D) {C' : Divisor Y} (hC' : C'.IsCartier)
    (hC'D : Divisor.toRDivisor C' = c • D') (hfree : IsRelativelyFreeDivisor fY C')
    {F : Mori.PrimeDivisor X} (hF : 0 < relativeFixedMultiplicity fX C F) :
    0 < (RationalMap.transformDivisor (X := T) p.toRationalMap (PD - QD)).coeff F := by
  have := hp.isDominant
  have := hq.isDominant
  have hB := map_componentGenericPoint_notMem_supp_of_isDominant p C
  have hB' := map_componentGenericPoint_notMem_supp_of_isDominant q C'
  set E : Divisor T := C.pullback hC hB - C'.pullback hC' hB' with hEdef
  have hEk : Divisor.toRDivisor E = c • (PD - QD) := by
    rw [hEdef, map_sub, smul_sub,
      MMP.Flips.IsRCartierPullback.eq p
        (isRCartierPullback_toRDivisor hC hB (Divisor.isPullback_pullback hC hB))
        (hCD ▸ isRCartierPullback_smul c hPD),
      MMP.Flips.IsRCartierPullback.eq q
        (isRCartierPullback_toRDivisor hC' hB' (Divisor.isPullback_pullback hC' hB'))
        (hC'D ▸ isRCartierPullback_smul c hQD)]
  have hE0' : 0 ≤ E := fun G => by
    have h := congrArg (fun D : RDivisor T => D.coeff G) hEk
    simp only [Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at h
    have : (0 : ℝ) ≤ E.coeff G := h ▸ mul_nonneg hc.le (hE0 G)
    exact_mod_cast this
  have hqE' : RationalMap.transformDivisor (X := T) q.toRationalMap E = 0 := by
    apply toRDivisor_injective
    rw [map_zero, toRDivisor_transformDivisor, hEk, transformDivisor_smul, hqE, smul_zero]
  obtain ⟨m, hm1, hm2⟩ := (sections_and_fixed_part_of_pullback_eq_add hX hY hT hZ p q fX fY hp
    hq hpX hqY hfX hfY hZc hC hC' hE0' hqE' ⟨hB, hB', by rw [hEdef]; abel⟩).2 hfree F
  have h := congrArg (fun D : RDivisor X => D.coeff F)
    (toRDivisor_transformDivisor p.toRationalMap E)
  simp only [Divisor.coeff_toRDivisor, hm1, hEk, transformDivisor_smul,
    DivisorWithCoeffs.coeff_smul, smul_eq_mul] at h
  rw [hm2] at hF
  have hm : (0 : ℝ) < m := by exact_mod_cast hF
  exact pos_of_mul_pos_right (by rwa [← Int.cast_natCast, h] at hm) hc.le

end CommonModel

/-! ### Fixed parts from a cone of relatively semiample divisors -/

section ConeFixedParts

/-- **Fixed parts on a common model from a semiample cone.** Let `p : T ⟶ X`, `q : T ⟶ Y` be a
common model over a variety `Z` of a birational contraction `φ = q ∘ p⁻¹` of `ℚ`-factorial
varieties, `D_t` a rational affine family of divisors on `X` with `φ_* D_t = K_Y + Γ_t` and
comparison `E_t = p^* D_t - q^* φ_* D_t` exceptional over `Y` and effective at `δ`. Suppose that
`Γ_δ` lies in the algebraic relative interior of the convex hull of finitely many `ℚ`-divisors,
and that `K_Y + Γ` lies, for every `Γ` of this hull, in the cone spanned by finitely many Cartier
divisors with relatively free multiples over `Z`. Then for some `r > 0` and all `t` near `δ` in
the smallest rational affine hull of `δ`, every fixed prime over `Z` of an integral multiple
`r C = k D_t` is a stable base prime of `D_δ`. -/
private theorem exists_fixedParts_of_cone
    {X Y T Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    {sT : T ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsIntegral Y] [IsIntegral T]
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian T] [IsNormal T] [CompactSpace X] [CompactSpace Y] [CompactSpace T]
    (hXQ : IsQFactorial sX) (hYQ : IsQFactorial sY) (hT : IsNormalVariety ℂ sT)
    (hZ : Mori.IsVariety ℂ sZ) (fX : X ⟶ Z) (fY : Y ⟶ Z) (hfX : fX ≫ sZ = sX)
    (hfY : fY ≫ sZ = sY) (φ : X.RationalMap Y) (p : T ⟶ X) (q : T ⟶ Y) [IsProper p]
    [IsProper q] (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q)
    (hpX : p ≫ sX = sT) (hqY : q ≫ sY = sT) (hZc : p ≫ fX = q ≫ fY)
    {s : ℕ} (D : (Fin s → ℝ) → RDivisor X) {n : ℕ} (PX : Fin n → Mori.PrimeDivisor X)
    (a : Fin n → (Fin s → ℚ) × ℚ) (hDcoeff : ∀ t i, (D t).coeff (PX i) = ratAffineForm (a i) t)
    (hDsupp : ∀ t, ↑(D t).support ⊆ Set.range PX)
    (KY : Divisor Y)
    (Γ : (Fin s → ℝ) → RDivisor Y) {n' : ℕ} (PY : Fin n' → Mori.PrimeDivisor Y)
    (b : Fin n' → (Fin s → ℚ) × ℚ) (hΓcoeff : ∀ t i, (Γ t).coeff (PY i) = ratAffineForm (b i) t)
    (hΓsupp : ∀ t, ↑(Γ t).support ⊆ Set.range PY)
    (hD' : ∀ t, RationalMap.transformDivisor φ (D t) = Divisor.toRDivisor KY + Γ t)
    (P Q : (Fin s → ℝ) → RDivisor T)
    (hP : ∀ t, MMP.Flips.IsRCartierPullback p (D t) (P t))
    (hQ : ∀ t, MMP.Flips.IsRCartierPullback q (Divisor.toRDivisor KY + Γ t) (Q t))
    (hqE : ∀ t, RationalMap.transformDivisor (X := T) q.toRationalMap (P t - Q t) = 0)
    {δ : Fin s → ℝ} (hEδ : 0 ≤ P δ - Q δ)
    (VQ : Finset (QDivisor Y))
    (hΔVQ : Γ δ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))))
    (hVQrel : ∀ Γ' ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))),
      ∃ ε : ℝ, 0 < ε ∧
        Γ δ + ε • (Γ δ - Γ') ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))))
    {ι : Type} [Fintype ι] (H : ι → Divisor Y) (hHc : ∀ i, (H i).IsCartier)
    (hHfree : ∀ i, ∃ m : ℕ, 0 < m ∧ IsRelativelyFreeDivisor fY ((m : ℤ) • H i))
    (hcone : ∀ Γ' ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))),
      ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧
        Divisor.toRDivisor KY + Γ' = ∑ i, c i • Divisor.toRDivisor (H i)) :
    ∃ r : ℕ, 0 < r ∧ ∀ᶠ t in 𝓝[(rationalAffineHull δ : Set (Fin s → ℝ))] δ,
      ∀ k : ℕ, 0 < k → ∀ C : Divisor X, C.IsCartier →
        Divisor.toRDivisor ((r : ℤ) • C) = (k : ℝ) • D t →
          ∀ F : Mori.PrimeDivisor X, 0 < relativeFixedMultiplicity fX ((r : ℤ) • C) F →
            IsInRelativeDivisorialStableBase fX (D δ) F := by
  classical
  have hX : IsNormalVariety ℂ sX := hXQ.1
  have hY : IsNormalVariety ℂ sY := hYQ.1
  have := hp.isDominant
  have := hq.isDominant
  have hTX : IsNormalVariety ℂ (p ≫ sX) := hpX ▸ hT
  have hDfam : IsRatAffineFamily D := isRatAffineFamily_of_coeff D PX a hDcoeff hDsupp
  have hΓfam : IsRatAffineFamily Γ := isRatAffineFamily_of_coeff Γ PY b hΓcoeff hΓsupp
  have hD'fam : IsRatAffineFamily (fun t => Divisor.toRDivisor KY + Γ t) := hΓfam.const_add KY
  obtain ⟨GP, hGPfam, hGP⟩ := hDfam.exists_isRCartierPullback hXQ.2 p
  obtain ⟨GQ, hGQfam, hGQ⟩ := hD'fam.exists_isRCartierPullback hYQ.2 q
  have hPV : ∀ t, P t = GP t := fun t => MMP.Flips.IsRCartierPullback.eq p (hP t) (hGP t)
  have hQV : ∀ t, Q t = GQ t := fun t => MMP.Flips.IsRCartierPullback.eq q (hQ t) (hGQ t)
  have hEδ' : 0 ≤ GP δ - GQ δ := by simpa only [← hPV δ, ← hQV δ] using hEδ
  obtain ⟨-, hEev⟩ := (hGPfam.sub hGQfam).eventually_nonneg (V := Set.univ) ⟨∅, by simp⟩
    (Set.mem_univ δ) hEδ'
  -- `Γ t` stays in the polytope near `δ` in the smallest rational affine hull
  have hΓev : ∀ᶠ t in 𝓝[(rationalAffineHull δ : Set (Fin s → ℝ))] δ,
      Γ t ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))) := by
    obtain ⟨LΓ, hLΓ⟩ := hΓfam.exists_affineMap
    have hconv := convex_convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y)))
    have hU := mem_nhdsWithin_rationalAffineHull_of_convex
      (U := LΓ ⁻¹' convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))))
      (hconv.affine_preimage LΓ) (by simpa [hLΓ] using hΔVQ) fun t ht => by
        have hspan : Γ t ∈ affineSpan ℝ
            (convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y)))) := by
          rw [affineSpan_convexHull]
          exact mem_affineSpan_of_forall_relation VQ (convexHull_subset_affineSpan _ hΔVQ)
            fun c q hc => hΓfam.relation ht c q hc
        obtain ⟨ε, hε, hmem⟩ := exists_lineMap_mem_of_mem_affineSpan hconv hΔVQ hVQrel hspan
        exact ⟨ε, hε, by rw [Set.mem_preimage, AffineMap.apply_lineMap, hLΓ, hLΓ]; exact hmem⟩
    filter_upwards [hU] with t ht
    simpa [hLΓ] using ht
  -- the uniform freeness index of the cone and a uniform Cartier index on `Y`
  obtain ⟨SY, hSY⟩ := hD'fam.exists_finset
  let PH : Finset (Mori.PrimeDivisor Y) := SY ∪ Finset.univ.biUnion fun i => (H i).support
  obtain ⟨bb, hbb, hfreecone⟩ := exists_pos_isRelativelyFreeDivisor_nsmul_of_mem_cone hY hZ fY
    hfY H hHc hHfree PH fun i => (Finset.subset_biUnion_of_mem (fun i => (H i).support)
      (Finset.mem_univ i)).trans Finset.subset_union_right
  obtain ⟨e, he, hecart⟩ := exists_zsmul_isCartier hYQ.2 PH
  refine ⟨e * bb, Nat.mul_pos he hbb, ?_⟩
  filter_upwards [hEev, hΓev] with t ⟨hEt0, hEtsupp⟩ hΓt k hk C hC hCk F hF
  -- the push-forward `C'` of `C`, with `r C' = k (K_Y + Γ_t)`
  set C' : Divisor Y := RationalMap.transformDivisor φ C with hC'def
  have hC'k : Divisor.toRDivisor (((e * bb : ℕ) : ℤ) • C') =
      (k : ℝ) • (Divisor.toRDivisor KY + Γ t) := by
    rw [map_zsmul, hC'def, toRDivisor_transformDivisor, ← map_zsmul, ← map_zsmul, hCk,
      transformDivisor_smul, hD' t]
  have hC'supp : C'.support ⊆ SY := by
    intro P hP
    by_contra hPS
    have h1 := congrArg (fun D : RDivisor Y => D.coeff P) hC'k
    have h2 : (Divisor.toRDivisor KY + Γ t).coeff P = 0 := by
      by_contra h0
      exact hPS (hSY t (Finsupp.mem_support_iff.2 h0))
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, h2, smul_zero] at h1
    have h3 : C'.coeff P ≠ 0 := Finsupp.mem_support_iff.1 hP
    simp only [smul_eq_mul, Int.cast_mul, Int.cast_natCast, mul_eq_zero, Nat.cast_eq_zero,
      Int.cast_eq_zero] at h1
    rcases h1 with (h1 | h1) | h1
    · exact he.ne' h1
    · exact hbb.ne' h1
    · exact h3 h1
  have hC'PH : C'.support ⊆ PH := hC'supp.trans Finset.subset_union_left
  have hCe : ((e : ℤ) • C').IsCartier := hecart C' hC'PH
  have hfreeY : IsRelativelyFreeDivisor fY (((e * bb : ℕ) : ℤ) • C') := by
    have hbb' : (bb : ℝ) ≠ 0 := by exact_mod_cast hbb.ne'
    obtain ⟨c, hc0, hcsum⟩ := hcone (Γ t) hΓt
    have hsub : ((e : ℤ) • C').support ⊆ C'.support := fun x hx => by
      rw [Finsupp.mem_support_iff] at hx ⊢
      intro h0
      apply hx
      rw [Finsupp.smul_apply, h0, smul_zero]
    have hsupp : ((e : ℤ) • C').support ⊆ PH := hsub.trans hC'PH
    have hcomb : Divisor.toRDivisor ((e : ℤ) • C') =
        ∑ i, ((k : ℝ) / bb * c i) • Divisor.toRDivisor (H i) := by
      have hz : ∀ n : ℤ, Divisor.toRDivisor (n • C') = (n : ℝ) • Divisor.toRDivisor C' :=
        fun n => by rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ]
      have h1 : Divisor.toRDivisor ((e : ℤ) • C') =
          ((k : ℝ) / bb) • (Divisor.toRDivisor KY + Γ t) := by
        have h3 := hC'k
        rw [hz] at h3
        have h4 : ((k : ℝ) / bb) • (Divisor.toRDivisor KY + Γ t) =
            (1 / (bb : ℝ)) • ((k : ℝ) • (Divisor.toRDivisor KY + Γ t)) := by
          rw [smul_smul]; congr 1; ring
        rw [hz, h4, ← h3, smul_smul]
        congr 1
        push_cast
        field_simp
      rw [h1, hcsum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]
    have := hfreecone ((e : ℤ) • C') hCe hsupp
      ⟨fun i => (k : ℝ) / bb * c i, fun i => mul_nonneg (by positivity) (hc0 i), hcomb⟩
    rwa [smul_smul, show ((bb : ℤ) * e) = ((e * bb : ℕ) : ℤ) by push_cast; ring] at this
  have hDY : (((e * bb : ℕ) : ℤ) • C').IsCartier := by
    rw [show (((e * bb : ℕ) : ℤ) • C') = (bb : ℤ) • ((e : ℤ) • C') by
      rw [smul_smul]; push_cast; ring_nf]
    exact hCe.zsmul _
  have hpos := pos_transformDivisor_of_pos_relativeFixedMultiplicity hX hY hT hZ p q fX fY hp
    hq hpX hqY hfX hfY hZc (hP t) (hQ t) (by rw [hPV t, hQV t]; exact hEt0)
    (hqE t) (by exact_mod_cast hk) (hC.zsmul _) hCk hDY hC'k hfreeY hF
  obtain ⟨G', -, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX hTX hp F
  refine isInRelativeDivisorialStableBase_of_pos_transformDivisor hX hY hT p q fX fY hp hq hpX
    hqY hZc (hP δ) (hQ δ) (add_sub_cancel _ _).symm (hqE δ) F ?_
  rw [DivisorWithCoeffs.coeff, htr, hPV δ, hQV δ]
  rw [DivisorWithCoeffs.coeff, htr, hPV t, hQV t] at hpos
  have hmem : G' ∈ (GP δ - GQ δ).support := hEtsupp ▸ Finsupp.mem_support_iff.2 hpos.ne'
  exact (hEδ' G').lt_of_ne (Finsupp.mem_support_iff.1 hmem).symm

end ConeFixedParts

end OneModel

namespace F3Help

open Filter Topology

section Arithmetic

variable {X Y : Scheme.{0}}

/-- The birational transform commutes with a change of coefficients along an additive map. -/
private theorem transformDivisor_mapCoeffsAddMonoidHom {R S : Type*} [AddCommGroup R]
    [AddCommGroup S] (f : R →+ S) (φ : X.RationalMap Y) (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor φ (DivisorWithCoeffs.mapCoeffsAddMonoidHom f D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom f (MMP.Mori.RationalMap.transformDivisor φ D) := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add D D' h h' => simp only [map_add, h, h']
  | single P r =>
    have h1 : ∀ (Z : Scheme.{0}) (Q : MMP.Mori.PrimeDivisor Z),
        DivisorWithCoeffs.mapCoeffsAddMonoidHom f (Finsupp.single Q r) =
          Finsupp.single Q (f r) := fun Z Q => by
      rw [DivisorWithCoeffs.mapCoeffsAddMonoidHom_apply]
      exact Finsupp.mapRange_single
    rw [h1, MMP.Mori.RationalMap.transformDivisor_single,
      MMP.Mori.RationalMap.transformDivisor_single]
    rcases MMP.Mori.RationalMap.transformPrimeDivisor φ P with _ | Q
    · exact (map_zero (DivisorWithCoeffs.mapCoeffsAddMonoidHom f)).symm
    · exact (h1 Y Q).symm

private theorem transformDivisor_toRDivisor (φ : X.RationalMap Y) (D : Divisor X) :
    MMP.Mori.RationalMap.transformDivisor φ (Divisor.toRDivisor D) =
      Divisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor φ D) :=
  transformDivisor_mapCoeffsAddMonoidHom _ φ D

private theorem transformDivisor_qToRDivisor (φ : X.RationalMap Y) (D : QDivisor X) :
    MMP.Mori.RationalMap.transformDivisor φ (QDivisor.toRDivisor D) =
      QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor φ D) :=
  transformDivisor_mapCoeffsAddMonoidHom _ φ D

/-- The birational transform of an effective divisor is effective. -/
private theorem transformDivisor_nonneg {R : Type*} [AddCommMonoid R] [PartialOrder R]
    [IsOrderedAddMonoid R] (φ : X.RationalMap Y) {D : DivisorWithCoeffs R X} (hD : 0 ≤ D) :
    0 ≤ MMP.Mori.RationalMap.transformDivisor φ D := by
  classical
  rw [MMP.Mori.RationalMap.transformDivisor, DivisorWithCoeffs.mapPrimeDivisors,
    Finsupp.liftAddHom_apply]
  refine Finset.sum_nonneg fun P _ => ?_
  dsimp only
  rcases MMP.Mori.RationalMap.transformPrimeDivisor φ P with _ | Q
  · simp
  · exact Finsupp.single_nonneg.mpr (hD P)

private theorem transformDivisor_mono {R : Type*} [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] (φ : X.RationalMap Y) {D D' : DivisorWithCoeffs R X} (hD : D ≤ D') :
    MMP.Mori.RationalMap.transformDivisor φ D ≤ MMP.Mori.RationalMap.transformDivisor φ D' := by
  have := transformDivisor_nonneg φ (sub_nonneg.mpr hD)
  rwa [map_sub, sub_nonneg] at this

private theorem qToRDivisor_nonneg {D : QDivisor X} (hD : 0 ≤ D) : 0 ≤ QDivisor.toRDivisor D :=
  fun P => by
    change (0 : ℝ) ≤ ((D P : ℚ) : ℝ)
    exact_mod_cast hD P

private theorem nonneg_of_qToRDivisor_nonneg {D : QDivisor X} (hD : 0 ≤ QDivisor.toRDivisor D) :
    0 ≤ D := fun P => by
  have : (0 : ℝ) ≤ ((D P : ℚ) : ℝ) := hD P
  exact_mod_cast this

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier: each prime divisor has a Cartier
multiple, and `D = ∑_P (D_P / m_P) · (m_P P)`. -/
private theorem isRCartier_of_isQFactorial [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : IsQFactorial sX) (D : RDivisor X) : RDivisor.IsRCartier D := by
  classical
  choose m hm hmC using fun P : MMP.Mori.PrimeDivisor X => hX.2 (Finsupp.single P 1)
  let e := D.support.equivFin
  refine ⟨D.support.card, fun i => D (e.symm i) / m (e.symm i),
    fun i => ((m (e.symm i) : ℕ) : ℤ) • Finsupp.single (e.symm i : MMP.Mori.PrimeDivisor X) 1,
    fun i => hmC _, fun Γ => ?_⟩
  let G : MMP.Mori.PrimeDivisor X → ℝ := fun x => if x = Γ then D x else 0
  have key : ∀ i, D (e.symm i) / m (e.symm i) *
      ((DivisorWithCoeffs.coeff (((m (e.symm i) : ℕ) : ℤ) •
        Finsupp.single (e.symm i : MMP.Mori.PrimeDivisor X) (1 : ℤ)) Γ : ℤ) : ℝ) =
        (fun x : D.support => G x.1) (e.symm i) := by
    intro i
    have hmx : ((m (e.symm i) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (hm _).ne'
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    simp only [G]
    by_cases h1 : (e.symm i : MMP.Mori.PrimeDivisor X) = Γ
    · rw [ite_eq_left h1, ite_eq_left h1]
      push_cast
      field_simp
    · rw [ite_eq_right h1, ite_eq_right h1]
      simp
  rw [Fintype.sum_equiv e.symm _ (fun x : D.support => G x.1) key,
    Finset.sum_coe_sort D.support G]
  simp only [G, Finset.sum_ite_eq', DivisorWithCoeffs.coeff_apply]
  split_ifs with h
  · rfl
  · exact Finsupp.notMem_support_iff.mp h

open Classical in
/-- The coefficients of a finite real combination of prime divisors. -/
private theorem coeff_sum_smul_single {n : ℕ} (PX : Fin n → MMP.Mori.PrimeDivisor X)
    (t : Fin n → ℝ) (P : MMP.Mori.PrimeDivisor X) :
    (∑ i, t i • Finsupp.single (PX i) (1 : ℝ) : RDivisor X).coeff P =
      ∑ i, if PX i = P then t i else 0 := by
  classical
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> simp

private theorem coeff_sum_smul_single_self {n : ℕ} {PX : Fin n → MMP.Mori.PrimeDivisor X}
    (hPX : Function.Injective PX) (t : Fin n → ℝ) (j : Fin n) :
    (∑ i, t i • Finsupp.single (PX i) (1 : ℝ) : RDivisor X).coeff (PX j) = t j := by
  classical
  rw [coeff_sum_smul_single, Finset.sum_eq_single j (fun i _ hij => ite_eq_right (hPX.ne hij))
    (by simp), ite_eq_left rfl]

/-- A real divisor supported on the image of an enumeration `PX` of a finite set of primes is the
combination of the `PX i` with its own coefficients. -/
private theorem eq_sum_smul_single {n : ℕ} {PX : Fin n → MMP.Mori.PrimeDivisor X}
    (hPX : Function.Injective PX) (Ξ : RDivisor X) (hΞ : ∀ P, Ξ P ≠ 0 → ∃ i, PX i = P) :
    Ξ = ∑ i, Ξ (PX i) • Finsupp.single (PX i) (1 : ℝ) := by
  classical
  ext P
  change Ξ.coeff P = (∑ i, Ξ (PX i) • Finsupp.single (PX i) (1 : ℝ) : RDivisor X).coeff P
  by_cases h : ∃ i, PX i = P
  · obtain ⟨j, rfl⟩ := h
    rw [coeff_sum_smul_single_self hPX]
    rfl
  · have h0 : Ξ P = 0 := by
      by_contra h'
      exact h (hΞ P h')
    rw [coeff_sum_smul_single, DivisorWithCoeffs.coeff_apply, h0]
    exact (Finset.sum_eq_zero fun i _ => ite_eq_right fun e => h ⟨i, e⟩).symm

/-- An `ℝ`-Cartier divisor in the sense of `MMP.Fourfold.RDivisor.IsRCartier` is a real
combination of Cartier divisors in the sense of `MMP.Flips.IsCartierCombination`. -/
private theorem isCartierCombination_of_isRCartier [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X] {D : RDivisor X} (h : RDivisor.IsRCartier D) :
    MMP.Flips.IsCartierCombination D := by
  obtain ⟨m, r, C, hC, hD⟩ := h
  refine ⟨m, r, C, hC, ?_⟩
  ext P
  rw [hD P, DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul]
  rfl

end Arithmetic

/-! ### Coefficients along a common resolution of a contraction -/

section Transfer

/-- For an inverse `h` of `p`, the composite `p ∘ h` is the identity. -/
private theorem compHom_eq_id_of_isInverse {X W : Scheme.{0}} [IsReduced X] [IsReduced W]
    [IsSeparated (X ↘ ⊤_ Scheme)] {p : W ⟶ X} {h : X.RationalMap W}
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) :
    h.compHom p = Scheme.Hom.toRationalMap (𝟙 X) := by
  obtain ⟨e, he1, he2⟩ := id hinv
  have hs : e.source.ι ≫ p = e.iso.hom ≫ e.target.ι :=
    ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp he1)).symm
  rw [← he2, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff,
    Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
  change e.iso.inv ≫ e.source.ι ≫ p = e.target.ι ≫ 𝟙 X
  rw [hs, Iso.inv_hom_id_assoc, Category.comp_id]

/-- **The point over a source prime.** Let `p : W ⟶ X` be proper with inverse `h` and
`q : W ⟶ Y` with `q ∘ h = φ`. If `φ_* Q = F`, a point of `W` lies over `η_Q` and over `η_F`: the
image of `η_Q` under a representative of `h` defined there. -/
private theorem exists_apply_eq_genericPoint_of_isInverse {X Y W : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsReduced W] [IsSeparated (X ↘ ⊤_ Scheme)]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {p : W ⟶ X} [IsProper p] {q : W ⟶ Y} {h : X.RationalMap W}
    {φ : X.RationalMap Y} (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h)
    (hq : h.compHom q = φ) {Q : MMP.Mori.PrimeDivisor X} {F : MMP.Mori.PrimeDivisor Y}
    (hQ : MMP.Mori.RationalMap.transformPrimeDivisor φ Q = some F) :
    ∃ w : W, q w = F.genericPoint ∧ p w = Q.genericPoint := by
  have hhp := compHom_eq_id_of_isInverse hinv
  have hdom : Q.genericPoint ∈ h.domain :=
    MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 X) p h hhp
      Q.coheight_genericPoint.le
  obtain ⟨g', hg'Q, hg'⟩ := Scheme.RationalMap.mem_domain.mp hdom
  refine ⟨g'.hom ⟨Q.genericPoint, hg'Q⟩,
    (MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hQ (g'.compHom q)
      (by rw [Scheme.RationalMap.compHom_toRationalMap, hg', hq]) hg'Q).symm, ?_⟩
  have h1 : (g'.compHom p).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', hhp]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom p) (g' := Scheme.PartialMap.id X) h1 hg'Q trivial
  change (g'.hom ≫ p) ⟨_, hg'Q⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨_, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- Two points of `W` over the generic point of a prime divisor of `Y`, along a birational
morphism `q : W ⟶ Y` of normal integral schemes, coincide. -/
private theorem eq_of_apply_eq_genericPoint {W Y : Scheme.{0}} [IsIntegral W] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {q : W ⟶ Y} [IsSeparated q]
    (hqb : IsBirationalMorphism q) {F : MMP.Mori.PrimeDivisor Y} {w₁ w₂ : W}
    (h₁ : q w₁ = F.genericPoint) (h₂ : q w₂ = F.genericPoint) : w₁ = w₂ := by
  have := hqb.isDominant
  have := F.isDiscreteValuationRing_localRing
  have : ValuationRing (Y.presheaf.stalk (q w₁)) := by rw [h₁]; infer_instance
  have := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hqb h₁
  have := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hqb h₂
  exact MMP.Positivity.eq_of_isIso_stalkMap q hqb.functionFieldMap_bijective (h₂.trans h₁.symm)

/-- **The source prime of a target prime.** For a birational contraction `φ = q ∘ p⁻¹`, every
prime divisor `E` of `W` over a prime divisor `F` of `Y` lies over a prime divisor `Q` of `X`
with `φ_* Q = F`, the only such prime, so that `(φ_* D)(F) = D(Q)` for every divisor `D`. -/
private theorem exists_primeDivisor_of_apply_eq_genericPoint {X Y W : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral W] [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)]
    {p : W ⟶ X} [IsProper p] {q : W ⟶ Y} [IsSeparated q] (hqb : IsBirationalMorphism q)
    {h : X.RationalMap W} {φ : X.RationalMap Y}
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (hq : h.compHom q = φ)
    (hcontr : ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    {E : MMP.Mori.PrimeDivisor W} {F : MMP.Mori.PrimeDivisor Y}
    (hE : q E.genericPoint = F.genericPoint) :
    ∃ Q : MMP.Mori.PrimeDivisor X, p E.genericPoint = Q.genericPoint ∧
      ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
        MMP.Mori.RationalMap.transformDivisor φ D F = D Q := by
  obtain ⟨Q, hQ⟩ : ∃ Q, MMP.Mori.RationalMap.transformPrimeDivisor φ Q = some F := by
    have := hcontr F
    simpa [MMP.Flips.RationalMap.IsInverseExceptional] using this
  obtain ⟨w, hwq, hwp⟩ := exists_apply_eq_genericPoint_of_isInverse hinv hq hQ
  have hw : E.genericPoint = w := eq_of_apply_eq_genericPoint hqb hE hwq
  refine ⟨Q, hw ▸ hwp, fun D => ?_⟩
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hQ (fun Q' hQ' => ?_) D
  obtain ⟨w', hwq', hwp'⟩ := exists_apply_eq_genericPoint_of_isInverse hinv hq hQ'
  have hww : w = w' := eq_of_apply_eq_genericPoint hqb hwq hwq'
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hwp'.symm.trans (hww ▸ hwp))

/-- **The comparison of a contraction is exceptional.** Let `φ = q ∘ p⁻¹ : X ⤏ Y` be a
birational contraction with a common resolution `p : W ⟶ X`, `q : W ⟶ Y`. For an `ℝ`-Cartier
`D` on `X` and `D' = φ_* D`, the push-forward along `q` of `p^*D - q^*D'` vanishes: at a prime
divisor `E` of `W` over a prime `F` of `Y`, both pull-backs have the coefficient of the source
prime of `F` in `D`. -/
private theorem transformDivisor_sub_eq_zero_of_isInverse {X Y W : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)]
    {p : W ⟶ X} [IsProper p] {q : W ⟶ Y} [IsSeparated q] (hpb : IsBirationalMorphism p)
    (hqb : IsBirationalMorphism q) {h : X.RationalMap W} {φ : X.RationalMap Y}
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (hq : h.compHom q = φ)
    (hcontr : ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    {D : RDivisor X} {D' : RDivisor Y} (hD' : MMP.Mori.RationalMap.transformDivisor φ D = D')
    {P Q : RDivisor W} (hP : MMP.Flips.IsRCartierPullback p D P)
    (hQ : MMP.Flips.IsRCartierPullback q D' Q) :
    MMP.Mori.RationalMap.transformDivisor (X := W) q.toRationalMap (P - Q) = 0 := by
  rw [MMP.Mori.RationalMap.transformDivisor]
  refine MMP.Fourfold.mapPrimeDivisors_eq_zero_of_forall _ fun E F hEF => ?_
  have hE := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff q E F).mp hEF
  obtain ⟨Q₀, hpE, hφ⟩ :=
    exists_primeDivisor_of_apply_eq_genericPoint hqb hinv hq hcontr hE
  have := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hpb hpE
  have := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hqb hE
  have h1 := MMP.Fourfold.coeff_eq_of_isRCartierPullback E Q₀ hpE hP
  have h2 := MMP.Fourfold.coeff_eq_of_isRCartierPullback E F hE hQ
  have h3 : D'.coeff F = D.coeff Q₀ := by rw [← hD']; exact hφ D
  change P.coeff E - Q.coeff E = 0
  rw [h1, h2, h3, sub_self]

end Transfer

/-- Membership in the smallest rational affine hull, in the coordinates of an enumeration `PX` of
a set of primes containing the support of `Δ`. -/
private theorem mem_rationalAffineHull_of_isInSmallestRationalAffineHull {X : Scheme.{0}}
    {n : ℕ} (PX : Fin n → MMP.Mori.PrimeDivisor X)
    {Δ Ξ : RDivisor X} (h : IsInSmallestRationalAffineHull Δ Ξ) :
    (fun i => Ξ (PX i)) ∈ rationalAffineHull (fun i => Δ (PX i)) := by
  classical
  intro f hf
  let c : MMP.Mori.PrimeDivisor X →₀ ℚ := ∑ j, Finsupp.single (PX j) (f.1 j)
  have hsum : ∀ Θ : RDivisor X, (c.sum fun P cP => (cP : ℝ) * Θ.coeff P) =
      ∑ j, (f.1 j : ℝ) * Θ (PX j) := by
    intro Θ
    change (∑ j, Finsupp.single (PX j) (f.1 j)).sum _ = _
    rw [← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.sum_single_index (by simp)]
    rfl
  have h1 := h.2 c (-f.2) (by
    rw [hsum]
    have : ratAffineForm f (fun i => Δ (PX i)) = 0 := hf
    simp only [ratAffineForm] at this
    push_cast
    linarith)
  rw [hsum] at h1
  simp only [ratAffineForm]
  push_cast at h1
  linarith

end F3Help

/-! ### Relative freeness on open subschemes -/

section OpenFree

open AlgebraicGeometry.OpenWeilRestriction

/-- **Relative freeness restricts to open subschemes over open subschemes of the base.** A
section of `𝒪(D)` near the fibre through `U ⟶ X` not vanishing at a point restricts to such a
section of `𝒪(D|_U)`. -/
private theorem isRelativelyFreeDivisor_restrictOpen {X B T : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {π : X ⟶ B} {j : T ⟶ B}
    (U : X.Opens) [Nonempty U] [CompactSpace U] {πU : U.toScheme ⟶ T}
    (hπU : πU ≫ j = U.ι ≫ π) {D : Divisor X} (hD : D.IsCartier)
    (hfree : IsRelativelyFreeDivisor π D) :
    IsRelativelyFreeDivisor πU (D.restrictOpen U) := by
  haveI : IsDominant U.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion U.ι
  have hπ : ∀ y, π (U.ι y) = j (πU y) := fun y => by
    rw [← Scheme.Hom.comp_apply, ← hπU, Scheme.Hom.comp_apply]
  refine isRelativelyFreeDivisor_of_forall_exists πU fun x => ?_
  obtain ⟨W, hW, ψ, hψ, hψx⟩ := exists_coeff_add_ord_eq_zero_of_isRelativelyFree π hD hfree (U.ι x)
  refine ⟨j ⁻¹ᵁ W, by show j (πU x) ∈ W; rw [← hπ]; exact hW,
    Units.map (rationalFunctionsEquiv U.ι).toMonoidHom ψ, fun P hP => ?_, fun P hxP => ?_⟩
  · have hP' : ((primeDivisorMap U.ι P).support ∩ π ⁻¹ᵁ W).Nonempty := by
      refine (MMP.Mori.PrimeDivisor.genericPoint_mem_iff _ _).mp ?_
      rw [genericPoint_primeDivisorMap']
      show π (U.ι P.genericPoint) ∈ W
      rw [hπ]
      exact (P.genericPoint_mem_iff (πU ⁻¹ᵁ (j ⁻¹ᵁ W))).mpr hP
    rw [ord_rationalFunctionsEquiv]
    exact hψ _ hP'
  · rw [ord_rationalFunctionsEquiv]
    refine hψx _ ?_
    have hx : x ∈ closure ({AlgebraicGeometry.PrimeDivisor.genericPoint P} : Set U.toScheme) := by
      rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact hxP
    show U.ι x ∈ AlgebraicGeometry.PrimeDivisor.support (primeDivisorMap U.ι P)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, genericPoint_primeDivisorMap,
      ← Set.image_singleton]
    exact image_closure_subset_closure_image U.ι.continuous ⟨x, hx, rfl⟩

end OpenFree

/-! ### Restricting a log terminal model over a compactified base -/

section RestrictModel

open AlgebraicGeometry.OpenWeilRestriction

/-- Composition of a rational map with two morphisms. -/
private theorem compHom_compHom {X Y Z T : Scheme.{0}} (φ : X.RationalMap Y) (f : Y ⟶ Z)
    (g : Z ⟶ T) : (φ.compHom f).compHom g = φ.compHom (f ≫ g) := by
  obtain ⟨φ, rfl⟩ := Scheme.RationalMap.exists_rep φ
  rw [← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap]
  congr 1

open MMP.Flips in
/-- **Restricting a log terminal model over a compactified base.** Let `S ⊆ S̄ ⟶ T̄ ⊇ T` be a
pull-back square of open immersions, and let `φ̄ : S̄ ⤏ Ȳ` over `T̄` be a `ℚ`-factorial klt nef
weak model of `(S̄, Θ̄)`, with a common resolution `p̄`, `q̄` carrying the effective exceptional
comparison. Then its restriction over `T` is a `ℚ`-factorial klt nef log terminal model of
`(S, Θ)` over `T`, with the restricted comparison. -/
private theorem logTerminalModel_of_compactification
    {S T Sb Tb : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sS] {sT : T ⟶ Spec (.of ℂ)} {f : S ⟶ T}
    [IsIntegral Sb] [IsLocallyNoetherian Sb] [IsNormal Sb] [CompactSpace Sb]
    {sTb : Tb ⟶ Spec (.of ℂ)} {j : T ⟶ Tb} [IsOpenImmersion j] {fb : Sb ⟶ Tb} {i : S ⟶ Sb}
    [IsOpenImmersion i] [IsDominant i]
    (hSQ : IsQFactorial sS) (hf : f ≫ sT = sS)
    (hTb : IsNormalVariety ℂ sTb) (hjs : j ≫ sTb = sT) (hpb : IsPullback i f fb j)
    (hiS : i ≫ fb ≫ sTb = sS) (hTn : IsNormalVariety ℂ sT)
    (hTp : MMP.Mori.IsProjectiveVariety ℂ sTb) (hSp : MMP.Mori.IsProjectiveVariety ℂ (fb ≫ sTb))
    (hSQb : IsQFactorial (fb ≫ sTb)) (hbig : (0 : QDivisor Sb).IsRelativelyBig fb)
    {Θ : RDivisor S} (hΘ : ∀ P, 0 ≤ Θ.coeff P) {K : Divisor S} {Kb : Divisor Sb}
    (hKb : Kb.IsCanonicalDivisor (fb ≫ sTb) 3)
    (hKbc : ∀ P, Kb.coeff (OpenWeilRestriction.primeDivisorMap i P) = K.coeff P)
    {Yb : Scheme.{0}} [IsIntegral Yb] [IsLocallyNoetherian Yb] [IsNormal Yb]
    {sYb : Yb ⟶ Spec (.of ℂ)} [QuasiCompact sYb] {πYb : Yb ⟶ Tb} {φb : Sb.RationalMap Yb}
    (hNW : IsNefWeakModel (fb ≫ sTb) sYb sTb fb πYb Kb
      (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Θ) φb)
    (hYQ : IsQFactorial sYb)
    (hYk : IsRealKltPair sYb (RationalMap.transformDivisor φb
      (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Θ)))
    {Wb : Scheme.{0}} [IsIntegral Wb] [IsLocallyNoetherian Wb] [IsNormal Wb]
    {sWb : Wb ⟶ Spec (.of ℂ)} {pb : Wb ⟶ Sb} {qb : Wb ⟶ Yb} {hb : Sb.RationalMap Wb}
    (hWv : MMP.Mori.IsVariety ℂ sWb) (hWsm : MMP.Mori.IsSmoothScheme sWb)
    (hpbs : pb ≫ fb ≫ sTb = sWb) (hqbs : qb ≫ sYb = sWb)
    (hpbp : IsProjectiveMorphism pb) (hqbp : IsProjectiveMorphism qb)
    (hpbb : IsBirationalMorphism pb) (hqbb : IsBirationalMorphism qb)
    (hinv : RationalMap.IsInverse pb.toRationalMap hb) (hcomp : hb.compHom qb = φb)
    {GX GY : RDivisor Wb}
    (hGX : IsRCartierPullback pb
      (logCanonicalDivisor Kb (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Θ)) GX)
    (hGY : IsRCartierPullback qb
      (logCanonicalDivisor (RationalMap.transformDivisor φb Kb) (RationalMap.transformDivisor φb
        (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Θ))) GY)
    (heff : ∀ P, 0 ≤ (GX - GY).coeff P)
    (hexc : ∀ P, (GX - GY).coeff P ≠ 0 → IsExceptionalPrimeDivisor sYb qb P)
    (hpos : ∀ P : MMP.Mori.PrimeDivisor Sb, RationalMap.IsExceptional φb P →
      ∀ P' : MMP.Mori.PrimeDivisor Wb,
        RationalMap.transformPrimeDivisor pb.toRationalMap P' = some P → 0 < (GX - GY).coeff P') :
    (∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
        (sY : Y ⟶ Spec (.of ℂ)) (_ : QuasiCompact sY) (πY : Y ⟶ T) (KY : Divisor Y)
        (φ : S.RationalMap Y),
      πY ≫ sT = sY ∧ IsProjectiveMorphism πY ∧ IsQFactorial sY ∧
        KY.IsCanonicalDivisor sY 3 ∧
        IsRealKltPair sY (RationalMap.transformDivisor φ Θ) ∧
        RationalMap.IsBirational φ ∧ MMP.Flips.RationalMap.IsOver f πY φ ∧
        (∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F) ∧
        MMP.Flips.IsRelativelyNef ℂ sY πY
          (MMP.Flips.logCanonicalDivisor KY (RationalMap.transformDivisor φ Θ)) ∧
        ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
          (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ S) (q : W ⟶ Y) (h : S.RationalMap W)
          (GS GY : RDivisor W),
          IsLogComparisonResolution sS sY sW φ K Θ KY (RationalMap.transformDivisor φ Θ)
            p q h GS GY ∧
          ∀ P : MMP.Mori.PrimeDivisor S, RationalMap.IsExceptional φ P →
            ∀ P' : MMP.Mori.PrimeDivisor W, RationalMap.transformPrimeDivisor h P = some P' →
              0 < (GS - GY).coeff P') ∧
    (∃ ε : ℝ, 0 < ε ∧ ∃ r : ℕ, 0 < r ∧ ∀ Φ : RDivisor S, IsInSmallestRationalAffineHull Θ Φ →
      (∀ P, 0 ≤ Φ.coeff P) → IsRealKltPair sS Φ →
      (∀ P, |Φ.coeff P - Θ.coeff P| < ε) →
      ∀ k : ℕ, 0 < k → ∀ D : Divisor S, D.IsCartier →
        (∀ P, (k : ℝ) / r *
        (MMP.Mori.DivisorWithCoeffs.coeff (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K) P +
            Φ.coeff P) = D.coeff P) →
          ∀ G : MMP.Mori.PrimeDivisor S, 0 < relativeFixedMultiplicity f ((r : ℤ) • D) G →
            IsInRelativeDivisorialStableBase f
              ((Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K) + Θ) G) := by
  classical
  subst hcomp
  set Θb := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Θ with hΘbdef
  have hinj := primeDivisorMap_injective i
  -- normality, separatedness and compactness
  have hSn : IsNormalVariety ℂ sS := hSQ.1
  have hYn : IsNormalVariety ℂ sYb := hNW.isNormalVariety_target
  have hSbn : IsNormalVariety ℂ (fb ≫ sTb) := hNW.isNormalVariety_source
  have hWbn : IsNormalVariety ℂ sWb := ⟨hWv, inferInstance⟩
  have hWbp : IsNormalVariety ℂ (pb ≫ fb ≫ sTb) := hpbs ▸ hWbn
  have hWbq : IsNormalVariety ℂ (qb ≫ sYb) := hqbs ▸ hWbn
  haveI : IsIntegral Tb := hTb.1.toIsIntegral
  haveI : IsSeparated sTb := hTb.1.toIsSeparated
  haveI : IsSeparated sYb := hYn.1.toIsSeparated
  haveI : IsSeparated sS := hSn.1.toIsSeparated
  haveI : IsSeparated sWb := hWv.toIsSeparated
  haveI : LocallyOfFiniteType sYb := hYn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sWb := hWv.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fb ≫ sTb) := hSbn.1.toLocallyOfFiniteType
  haveI : QuasiCompact sWb := hWv.toQuasiCompact
  haveI : CompactSpace Yb := QuasiCompact.compactSpace_of_compactSpace sYb
  haveI : CompactSpace Wb := QuasiCompact.compactSpace_of_compactSpace sWb
  haveI : IsSeparated (Tb ↘ Limits.terminal Scheme) := isSeparated_terminal sTb
  haveI : IsSeparated (Yb ↘ Limits.terminal Scheme) := isSeparated_terminal sYb
  haveI : IsSeparated (S ↘ Limits.terminal Scheme) := isSeparated_terminal sS
  haveI : IsSeparated (fb ≫ sTb) := hSbn.1.toIsSeparated
  haveI : IsSeparated (Sb ↘ Limits.terminal Scheme) := isSeparated_terminal (fb ≫ sTb)
  haveI : IsDominant pb := hpbb.isDominant
  haveI : IsDominant qb := hqbb.isDominant
  haveI : IsProper pb := isProper_of_isProjectiveMorphism pb hpbp
  haveI : IsProper qb := isProper_of_isProjectiveMorphism qb hqbp
  haveI : Nonempty S := ⟨genericPoint S⟩
  -- the two composites `W̄ ⟶ T̄` agree
  have hpq : pb ≫ fb = qb ≫ πYb :=
    comp_eq_comp_of_isOver fb πYb hNW.isOver pb qb hb hinv rfl
  -- the open parts over `T`
  set V : Yb.Opens := πYb ⁻¹ᵁ j.opensRange with hV
  set Wo : Wb.Opens := pb ⁻¹ᵁ i.opensRange with hWo
  have hUi : fb ⁻¹ᵁ j.opensRange = i.opensRange := preimage_opensRange_of_isPullback hpb.flip
  have hWV : qb ⁻¹ᵁ V = Wo := by
    rw [hV, hWo, ← hUi, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hpq]
  -- the restricted morphisms
  let p : Wo.toScheme ⟶ S := IsOpenImmersion.lift i (Wo.ι ≫ pb) (by
    rintro _ ⟨x, rfl⟩; exact x.2)
  have hp : p ≫ i = Wo.ι ≫ pb := IsOpenImmersion.lift_fac _ _ _
  let πY : V.toScheme ⟶ T := IsOpenImmersion.lift j (V.ι ≫ πYb) (by
    rintro _ ⟨x, rfl⟩; exact x.2)
  have hπY : πY ≫ j = V.ι ≫ πYb := IsOpenImmersion.lift_fac _ _ _
  let q : Wo.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι (Wo.ι ≫ qb) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hx : x.1 ∈ qb ⁻¹ᵁ V := by rw [hWV]; exact x.2
    exact hx)
  have hq : q ≫ V.ι = Wo.ι ≫ qb := IsOpenImmersion.lift_fac _ _ _
  have Hp : IsPullback p Wo.ι i pb :=
    IsOpenImmersion.isPullback _ _ _ _ hp.symm (Scheme.Opens.opensRange_ι _).symm
  have Hπ : IsPullback πY V.ι j πYb :=
    IsOpenImmersion.isPullback _ _ _ _ hπY.symm (Scheme.Opens.opensRange_ι _).symm
  have Hq : IsPullback q Wo.ι V.ι qb :=
    IsOpenImmersion.isPullback _ _ _ _ hq.symm (by
      rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, hWV])
  -- nonemptiness and instances on the open parts
  have hηW : genericPoint Wb ∈ Wo := by
    show pb (genericPoint Wb) ∈ i.opensRange
    rw [MMP.Positivity.map_genericPoint_eq_of_isDominant pb]
    exact ((genericPoint_spec Sb).mem_open_set_iff i.opensRange.isOpen).mpr
      ⟨i (genericPoint S), trivial, genericPoint S, rfl⟩
  haveI : Nonempty Wo := ⟨⟨genericPoint Wb, hηW⟩⟩
  haveI : Nonempty V := ⟨q ⟨genericPoint Wb, hηW⟩⟩
  haveI : IsNoetherian Wb := {}
  haveI : IsNoetherian Yb := {}
  haveI : CompactSpace Wo := isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  haveI : CompactSpace V := isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  haveI : IsDominant Wo.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion Wo.ι
  haveI : IsDominant V.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion V.ι
  have hpB : IsBirationalMorphism p := isBirationalMorphism_of_isPullback Hp hpbb
  have hqB : IsBirationalMorphism q := isBirationalMorphism_of_isPullback Hq hqbb
  haveI : IsDominant p := hpB.isDominant
  haveI : IsDominant q := hqB.isDominant
  have hpP : IsProjectiveMorphism p := isProjectiveMorphism_of_isPullback Hp.flip hpbp
  have hqP : IsProjectiveMorphism q := isProjectiveMorphism_of_isPullback Hq.flip hqbp
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpP
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqP
  have hπYb : IsProjectiveMorphism πYb := by
    refine IsProjectiveMorphism.of_comp πYb sTb ?_
    rw [hNW.comp_eq_target]
    exact hNW.isProjectiveVariety_target.isProjective
  have hπP : IsProjectiveMorphism πY := isProjectiveMorphism_of_isPullback Hπ.flip hπYb
  have hVn : IsNormalVariety ℂ (V.ι ≫ sYb) := hYn.restrictOpen V
  have hWon : IsNormalVariety ℂ (Wo.ι ≫ sWb) := hWbn.restrictOpen Wo
  have hqs : q ≫ V.ι ≫ sYb = Wo.ι ≫ sWb := by
    rw [← Category.assoc, hq, Category.assoc, hqbs]
  have hps : p ≫ sS = Wo.ι ≫ sWb := by
    rw [← hiS, ← Category.assoc, hp, Category.assoc, hpbs]
  have hWoq : IsNormalVariety ℂ (q ≫ V.ι ≫ sYb) := hqs ▸ hWon
  have hWop : IsNormalVariety ℂ (p ≫ sS) := hps ▸ hWon
  haveI : IsSeparated (V.toScheme ↘ Limits.terminal Scheme) := isSeparated_terminal (V.ι ≫ sYb)
  haveI : IsSeparated (Wo.toScheme ↘ Limits.terminal Scheme) := isSeparated_terminal (Wo.ι ≫ sWb)
  -- the restricted map `φ = q ∘ p⁻¹`
  let h : S.RationalMap Wo.toScheme := hpB.inverse
  have hh : RationalMap.IsInverse p.toRationalMap h := hpB.isInverse_inverse
  let φ : S.RationalMap V.toScheme := h.compHom q
  have hTr := transformPrimeDivisor_compHom_primeDivisorMap hSbn hWbp Hp Hq hpB hpbb hh hinv
  -- push-forwards along `φ` are restrictions of push-forwards along `φ̄`
  have hφD : ∀ (D : RDivisor S) (D' : RDivisor Sb), (∀ P, D' (primeDivisorMap i P) = D P) →
      RationalMap.transformDivisor φ D =
        (RationalMap.transformDivisor (hb.compHom qb) D').restrictOpen V := fun D D' hD =>
    Finsupp.ext fun F =>
      (mapPrimeDivisors_apply_of_comap hinj (primeDivisorMap_injective V.ι) hTr.1 hTr.2 hD F).symm
  have hφΘ : RationalMap.transformDivisor φ Θ =
      (RationalMap.transformDivisor (hb.compHom qb) Θb).restrictOpen V :=
    hφD Θ Θb fun P => Finsupp.mapDomain_apply_of_injective hinj Θ P
  -- canonical divisors
  obtain ⟨KWb, hKWb, hpKWb, hqKWb, hKYb⟩ := exists_isCanonicalDivisor_common_model hSbn hWbn hYn
    hpbs hqbs hpbb hqbb hinv hNW.not_isInverseExceptional hKb
  set KY : Divisor V.toScheme := (RationalMap.transformDivisor (hb.compHom qb) Kb).restrictOpen V
  set KW : Divisor Wo.toScheme := KWb.restrictOpen Wo
  have hpKW : RationalMap.transformDivisor p.toRationalMap KW = K := by
    refine Finsupp.ext fun P => ?_
    rw [← transformDivisor_primeDivisorMap_of_isPullback Hp (D := KW) (D' := KWb) (fun E => rfl) P,
      hpKWb]
    exact hKbc P
  have hqKW : RationalMap.transformDivisor q.toRationalMap KW = KY := by
    refine Finsupp.ext fun F => ?_
    rw [← transformDivisor_primeDivisorMap_of_isPullback Hq (D := KW) (D' := KWb) (fun E => rfl) F,
      hqKWb]
    rfl
  -- the comparison on the restricted resolution
  set GS : RDivisor Wo.toScheme := GX.restrictOpen Wo
  set GYW : RDivisor Wo.toScheme := GY.restrictOpen Wo
  have hlogS : comapDivisor i (logCanonicalDivisor Kb Θb) = logCanonicalDivisor K Θ := by
    refine Finsupp.ext fun P => ?_
    change (logCanonicalDivisor Kb Θb).coeff (primeDivisorMap i P) = (logCanonicalDivisor K Θ).coeff P
    rw [MMP.Flips.logCanonicalDivisor, MMP.Flips.logCanonicalDivisor, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, Divisor.coeff_toRDivisor, hKbc]
    congr 1
    exact Finsupp.mapDomain_apply_of_injective hinj Θ P
  have hlogY : comapDivisor V.ι (logCanonicalDivisor (RationalMap.transformDivisor (hb.compHom qb) Kb)
      (RationalMap.transformDivisor (hb.compHom qb) Θb)) =
      logCanonicalDivisor KY (RationalMap.transformDivisor φ Θ) := by
    rw [hφΘ]
    refine Finsupp.ext fun F => ?_
    change (logCanonicalDivisor _ _).coeff (primeDivisorMap V.ι F) =
      (logCanonicalDivisor KY _).coeff F
    rw [MMP.Flips.logCanonicalDivisor, MMP.Flips.logCanonicalDivisor, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, Divisor.coeff_toRDivisor]
    rfl
  have hGS : IsRCartierPullback p (logCanonicalDivisor K Θ) GS := by
    rw [← hlogS]; exact isRCartierPullback_comapDivisor Hp hGX
  have hGYW : IsRCartierPullback q (logCanonicalDivisor KY (RationalMap.transformDivisor φ Θ)) GYW := by
    rw [← hlogY]; exact isRCartierPullback_comapDivisor Hq hGY
  have hdiff : ∀ E : MMP.Mori.PrimeDivisor Wo.toScheme,
      (GS - GYW).coeff E = (GX - GY).coeff (primeDivisorMap Wo.ι E) := fun E => rfl
  -- exceptional primes
  have hcohq : ∀ E : MMP.Mori.PrimeDivisor Wo.toScheme,
      Order.coheight (qb (MMP.Mori.PrimeDivisor.genericPoint (primeDivisorMap Wo.ι E))) =
        Order.coheight (q E.genericPoint) := fun E => by
    rw [genericPoint_primeDivisorMap', ← Scheme.Hom.comp_apply, ← hq, Scheme.Hom.comp_apply,
      coheight_eq_of_isOpenImmersion]
  have hπYs : πY ≫ sT = V.ι ≫ sYb := by
    rw [← hjs, ← Category.assoc, hπY, Category.assoc, hNW.comp_eq_target]
  have hqπ : q ≫ πY = p ≫ f := by
    rw [← cancel_mono j]
    calc (q ≫ πY) ≫ j = q ≫ V.ι ≫ πYb := by rw [Category.assoc, hπY]
      _ = Wo.ι ≫ qb ≫ πYb := by rw [← Category.assoc, hq, Category.assoc]
      _ = Wo.ι ≫ pb ≫ fb := by rw [hpq]
      _ = p ≫ i ≫ fb := by rw [← Category.assoc, ← hp, Category.assoc]
      _ = (p ≫ f) ≫ j := by rw [hpb.w, Category.assoc]
  -- `φ` lies over `T`
  have hover : MMP.Flips.RationalMap.IsOver f πY φ := by
    show (h.compHom q).compHom πY = f.toRationalMap
    rw [compHom_compHom, hqπ, ← compHom_compHom, Crepant.compHom_eq_of_isInverse hh,
      show Scheme.Hom.toRationalMap (𝟙 S) = Scheme.RationalMap.id S from rfl,
      Scheme.RationalMap.id_compHom]
  -- `φ` extracts no divisor
  have hcontr : ∀ F : MMP.Mori.PrimeDivisor V.toScheme,
      ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F := by
    intro F hF
    refine hNW.not_isInverseExceptional (primeDivisorMap V.ι F) fun Q hQ => ?_
    obtain ⟨P, rfl⟩ := hTr.2 Q F hQ
    have h1 := hTr.1 P
    rw [hQ] at h1
    rcases hP : RationalMap.transformPrimeDivisor φ P with _ | F'
    · rw [hP] at h1; simp at h1
    · rw [hP, Option.map_some, Option.some_inj] at h1
      have hFF := primeDivisorMap_injective V.ι h1
      rw [← hFF] at hP
      exact hF P hP
  refine ⟨⟨V.toScheme, inferInstance, inferInstance, inferInstance, V.ι ≫ sYb, inferInstance, πY,
    KY, φ, hπYs, hπP, isQFactorial_restrictOpen hYQ V, hKYb.restrictOpen hYn V, ?_,
    hh.isBirational_compHom hqB, hover, hcontr, ?_, Wo.toScheme, inferInstance, inferInstance,
    inferInstance, Wo.ι ≫ sWb, p, q, h, GS, GYW, ?_, ?_⟩, ?_⟩
  · -- klt
    rw [hφΘ]
    exact isRealKltPair_restrictOpen hNW.isProjectiveVariety_target hYQ
      (fun P => DivisorWithCoeffs.mapPrimeDivisors_nonneg _ (mapDomain_nonneg _ hΘ) P) hYk V
  · -- nefness over `T`
    rw [← hlogY]
    exact isRelativelyNef_restrictOpen V hπY hNW.isRelativelyNef
  · -- the comparison resolution
    refine ⟨?_, MMP.Threefold.Resolution.isSmoothScheme_ι ℂ hWsm Wo, hps, hqs, hpP, hqP, hpB, hqB,
      hh, rfl, ⟨3, KW, hKWb.restrictOpen hWbn Wo, hpKW, hqKW⟩, hGS, hGYW, fun E => ?_,
      fun E hE => ?_⟩
    · exact (MMP.Mori.isVariety_iff ℂ _).mpr
        ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
    · rw [hdiff]; exact heff _
    · rw [hdiff] at hE
      have h1 := hexc _ hE
      rw [isExceptionalPrimeDivisor_iff hYn hWbq hqbb, hcohq] at h1
      exact (isExceptionalPrimeDivisor_iff hVn hWoq hqB E).mpr h1
  · -- positivity along the strict transforms of the `φ`-exceptional primes
    intro P hPex P' hP'
    rw [hdiff]
    -- the strict transform `P_W` of `P`
    obtain ⟨E₀, hE₀, -⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0}
      hSbn hWbp hpbb (primeDivisorMap i P)
    have hmem : E₀.genericPoint ∈ Wo := by
      show pb E₀.genericPoint ∈ i.opensRange
      rw [hE₀, genericPoint_primeDivisorMap']; exact ⟨_, rfl⟩
    obtain ⟨PW, rfl⟩ := (mem_range_primeDivisorMap_iff Wo.ι E₀).mpr ⟨⟨_, hmem⟩, rfl⟩
    have hPW : p PW.genericPoint = P.genericPoint := by
      refine i.isOpenEmbedding.injective ?_
      have h1 := hE₀
      rw [genericPoint_primeDivisorMap', genericPoint_primeDivisorMap', ← Scheme.Hom.comp_apply,
        ← hp, Scheme.Hom.comp_apply] at h1
      exact h1
    obtain ⟨g₀, hg₀, hR, hval⟩ := exists_rep_apply_eq_of_isInverse p hpB hh P PW hPW
    -- `P'` is `P_W`
    have hP'PW : P' = PW := by
      refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
      have := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hP' g₀ hg₀ hR
      rw [hval] at this
      exact this
    subst hP'PW
    have hPbW : pb (MMP.Mori.PrimeDivisor.genericPoint (primeDivisorMap Wo.ι P')) =
        MMP.Mori.PrimeDivisor.genericPoint (primeDivisorMap i P) := by
      rw [genericPoint_primeDivisorMap', genericPoint_primeDivisorMap', ← Scheme.Hom.comp_apply,
        ← hp, Scheme.Hom.comp_apply, hPW]
    refine hpos (primeDivisorMap i P) ?_ (primeDivisorMap Wo.ι P')
      ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff _ _ _).mpr hPbW)
    -- `P̄` is `φ̄`-exceptional
    by_contra hne
    obtain ⟨g₁, hg₁, hR₁, hval₁⟩ := exists_rep_apply_eq_of_isInverse pb hpbb hinv _ _ hPbW
    have hc := SamePrimes.coheight_apply_le_one_of_not_isExceptional qb g₁
      (by rw [Scheme.RationalMap.compHom_toRationalMap, hg₁]) hR₁ hne
    rw [hval₁, hcohq] at hc
    refine not_isExceptional_of_coheight_le_one (g₀.compHom q)
      (by rw [Scheme.RationalMap.compHom_toRationalMap, hg₀]) P hR ?_ hPex
    change Order.coheight (q (g₀.hom ⟨P.genericPoint, hR⟩)) ≤ 1
    rw [hval]
    exact hc
  · -- the fixed parts along the smallest rational affine hull
    -- the push-forward of `K`
    have hφK : RationalMap.transformDivisor φ K = KY :=
      Finsupp.ext fun F => (mapPrimeDivisors_apply_of_comap hinj (primeDivisorMap_injective V.ι)
        hTr.1 hTr.2 (D := K) (D' := Kb) (fun P => hKbc P) F).symm
    -- the coordinates: the primes of `K` and of `Θ`
    let Sset : Finset (MMP.Mori.PrimeDivisor S) := K.support ∪ Θ.support
    let e := Sset.equivFin
    let PX : Fin Sset.card → MMP.Mori.PrimeDivisor S := fun i => (e.symm i).1
    have hPX : Function.Injective PX := fun i j hij => e.symm.injective (Subtype.ext hij)
    have hPXmem : ∀ P ∈ Sset, ∃ i, PX i = P := fun P hP => ⟨e ⟨P, hP⟩, by simp [PX]⟩
    let D : (Fin Sset.card → ℝ) → RDivisor S := fun t =>
      Divisor.toRDivisor K + ∑ i, t i • Finsupp.single (PX i) (1 : ℝ)
    let δ : Fin Sset.card → ℝ := fun i => Θ (PX i)
    have hΘsum : Θ = ∑ i, δ i • Finsupp.single (PX i) (1 : ℝ) :=
      F3Help.eq_sum_smul_single hPX Θ fun P hP => hPXmem P
        (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hP))
    have hDδ : D δ = MMP.Flips.logCanonicalDivisor K Θ := by
      change Divisor.toRDivisor K + ∑ i, δ i • Finsupp.single (PX i) (1 : ℝ) =
        Divisor.toRDivisor K + Θ
      rw [← hΘsum]
    -- the family on `S`
    let a : Fin Sset.card → (Fin Sset.card → ℚ) × ℚ := fun i => (Pi.single i 1, (K (PX i) : ℚ))
    have hDcoeff : ∀ t i, (D t).coeff (PX i) = ratAffineForm (a i) t := by
      intro t i
      simp only [D, a, ratAffineForm, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor,
        F3Help.coeff_sum_smul_single_self hPX]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
      simp only [Pi.single_eq_same, Rat.cast_one, one_mul, Rat.cast_intCast,
        DivisorWithCoeffs.coeff_apply]
      ring
    have hDsupp : ∀ t, ↑(D t).support ⊆ Set.range PX := by
      intro t P hP
      by_contra hPr
      have hK0 : K P = 0 := by
        by_contra hK
        exact hPr (hPXmem P (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hK)))
      apply Finsupp.mem_support_iff.mp hP
      have hK0' : (K.coeff P : ℝ) = 0 := by rw [DivisorWithCoeffs.coeff_apply, hK0, Int.cast_zero]
      change (Divisor.toRDivisor K + ∑ i, t i • Finsupp.single (PX i) (1 : ℝ)).coeff P = 0
      rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, hK0', zero_add,
        F3Help.coeff_sum_smul_single]
      exact Finset.sum_eq_zero fun i _ => ite_eq_right fun e => hPr ⟨i, e⟩
    have hDc : ∀ t, RDivisor.IsRCartier (D t) := fun t => hSQ.isRCartier (D t)
    -- the family on `V`
    have hQV := isQFactorial_restrictOpen hYQ V
    let Γ : (Fin Sset.card → ℝ) → RDivisor V.toScheme := fun t =>
      MMP.Mori.RationalMap.transformDivisor φ (∑ i, t i • Finsupp.single (PX i) (1 : ℝ))
    let SY : Finset (MMP.Mori.PrimeDivisor V.toScheme) :=
      Finset.univ.biUnion fun i => (MMP.Mori.RationalMap.transformPrimeDivisor φ (PX i)).toFinset
    let eY := SY.equivFin
    let PY : Fin SY.card → MMP.Mori.PrimeDivisor V.toScheme := fun j => (eY.symm j).1
    let b : Fin SY.card → (Fin Sset.card → ℚ) × ℚ := fun j =>
      (fun i => if MMP.Mori.RationalMap.transformPrimeDivisor φ (PX i) = some (PY j) then 1 else 0,
        0)
    have hΓcoeffP : ∀ t (F : MMP.Mori.PrimeDivisor V.toScheme), (Γ t).coeff F =
        ∑ i, if MMP.Mori.RationalMap.transformPrimeDivisor φ (PX i) = some F then t i else 0 := by
      intro t F
      simp only [Γ, map_sum, DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← MMP.Mori.RationalMap.transformDivisorₗ_apply ℝ, map_smul,
        MMP.Mori.RationalMap.transformDivisorₗ_apply, MMP.Mori.RationalMap.transformDivisor_single]
      rcases hi : MMP.Mori.RationalMap.transformPrimeDivisor φ (PX i) with _ | Q
      · simp
      · by_cases hQ : Q = F
        · subst hQ; simp
        · simp [hQ]
    have hΓcoeff : ∀ t j, (Γ t).coeff (PY j) = ratAffineForm (b j) t := by
      intro t j
      rw [hΓcoeffP]
      simp only [b, ratAffineForm, Rat.cast_zero, add_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    have hΓsupp : ∀ t, ↑(Γ t).support ⊆ Set.range PY := by
      intro t F hF
      have hF' : (Γ t).coeff F ≠ 0 := Finsupp.mem_support_iff.mp hF
      rw [hΓcoeffP] at hF'
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hF'
      have hiF : MMP.Mori.RationalMap.transformPrimeDivisor φ (PX i) = some F := by
        by_contra hne; exact hi (ite_eq_right hne)
      have hFS : F ∈ SY := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [hiF]⟩
      exact ⟨eY ⟨F, hFS⟩, by simp [PY]⟩
    have hD' : ∀ t, MMP.Mori.RationalMap.transformDivisor φ (D t) =
        Divisor.toRDivisor KY + Γ t :=
      fun t => by simp only [D, Γ, map_add, F3Help.transformDivisor_toRDivisor, hφK]
    have hYc : ∀ t, RDivisor.IsRCartier (Divisor.toRDivisor KY + Γ t) := fun t =>
      hQV.isRCartier _
    -- the pull-backs
    have hPex : ∀ t, ∃ G, MMP.Flips.IsRCartierPullback p (D t) G := fun t =>
      (MMP.Flips.existsUnique_isRCartierPullback p
        (F3Help.isCartierCombination_of_isRCartier (hDc t))).exists
    choose P hP using hPex
    have hQex : ∀ t, ∃ G, MMP.Flips.IsRCartierPullback q (Divisor.toRDivisor KY + Γ t) G :=
      fun t => (MMP.Flips.existsUnique_isRCartierPullback q
        (F3Help.isCartierCombination_of_isRCartier (hYc t))).exists
    choose Q hQ using hQex
    have hqE : ∀ t,
        MMP.Mori.RationalMap.transformDivisor (X := Wo.toScheme) q.toRationalMap (P t - Q t) = 0 :=
      fun t => F3Help.transformDivisor_sub_eq_zero_of_isInverse hpB hqB hh rfl hcontr (hD' t)
        (hP t) (hQ t)
    -- the data at `δ`
    have hΓδ : Γ δ = MMP.Mori.RationalMap.transformDivisor φ Θ := by
      change MMP.Mori.RationalMap.transformDivisor φ (∑ i, δ i • Finsupp.single (PX i) (1 : ℝ)) = _
      rw [← hΘsum]
    have hPδ : P δ = GS := MMP.Flips.IsRCartierPullback.eq p (hP δ) (by rw [hDδ]; exact hGS)
    have hQδ : Q δ = GYW := MMP.Flips.IsRCartierPullback.eq q (hQ δ) (by rw [hΓδ]; exact hGYW)
    have hEδ : 0 ≤ P δ - Q δ := by
      rw [hPδ, hQδ]
      intro E
      have h0 := heff (primeDivisorMap Wo.ι E)
      rw [← hdiff E] at h0
      exact h0
    -- the semiample cone on `Ȳ`, from the uniform freeness theorem
    set KYb := RationalMap.transformDivisor (hb.compHom qb) Kb with hKYbdef
    set ΘY := RationalMap.transformDivisor (hb.compHom qb) Θb with hΘYdef
    have hΘY0 : 0 ≤ ΘY := DivisorWithCoeffs.mapPrimeDivisors_nonneg _ (mapDomain_nonneg _ hΘ)
    obtain ⟨-, -, hGbig⟩ := isRelativelyBig_transformDivisor_of_isBirationalContraction
      (fb ≫ sTb) sYb sTb hSbn hSp hYQ hNW.isProjectiveVariety_target hTp fb πYb rfl
      hNW.comp_eq_target (hb.compHom qb) hNW.isBirational hNW.isOver hNW.not_isInverseExceptional
      0 le_rfl (MMP.Fourfold.isQCartier_of_isQFactorial _ hSQb 0) hbig
    rw [map_zero] at hGbig
    obtain ⟨VQ, hΔVQ, hrel, -, H, hH, hcone⟩ := OneModel.exists_uniform_freeness hYQ
      hNW.isProjectiveVariety_target hTp πYb hNW.comp_eq_target ⟨3, hKYb⟩ hΘY0 hYk
      (G := 0) le_rfl hGbig (by rw [map_zero]; exact hΘY0) hNW.isRelativelyNef
    -- its restriction to `V`
    let ρ : RDivisor Yb →ₗ[ℝ] RDivisor V.toScheme :=
      Finsupp.lcomapDomain (primeDivisorMap V.ι) (primeDivisorMap_injective V.ι)
    have hρ : ∀ D : RDivisor Yb, ρ D = D.restrictOpen V := fun D => rfl
    have hρQ : ∀ Γ : QDivisor Yb,
        ρ (QDivisor.toRDivisor Γ) = QDivisor.toRDivisor (Γ.restrictOpen V) :=
      fun Γ => Finsupp.ext fun F => rfl
    have hρZ : ∀ D : Divisor Yb,
        ρ (Divisor.toRDivisor D) = Divisor.toRDivisor (DivisorWithCoeffs.restrictOpen V D) :=
      fun D => Finsupp.ext fun F => rfl
    let VQV : Finset (QDivisor V.toScheme) := VQ.image fun Γ => Γ.restrictOpen V
    have himV : QDivisor.toRDivisor '' (VQV : Set (QDivisor V.toScheme)) =
        ρ '' (QDivisor.toRDivisor '' (VQ : Set (QDivisor Yb))) := by
      rw [Finset.coe_image, Set.image_image, Set.image_image]
      exact Set.image_congr fun Γ _ => (hρQ Γ).symm
    have hconvV : convexHull ℝ (QDivisor.toRDivisor '' (VQV : Set (QDivisor V.toScheme))) =
        ρ '' convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Yb))) := by
      rw [himV, LinearMap.image_convexHull]
    have hΓδρ : Γ δ = ρ ΘY := by rw [hΓδ, hφΘ, hρ]
    have hΔVQV : Γ δ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQV : Set (QDivisor V.toScheme))) := by
      rw [hconvV, hΓδρ]; exact ⟨_, hΔVQ, rfl⟩
    have hrelV : ∀ Γ' ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQV : Set (QDivisor V.toScheme))),
        ∃ ε : ℝ, 0 < ε ∧ Γ δ + ε • (Γ δ - Γ') ∈
          convexHull ℝ (QDivisor.toRDivisor '' (VQV : Set (QDivisor V.toScheme))) := by
      intro Γ' hΓ'
      rw [hconvV] at hΓ' ⊢
      obtain ⟨Γ'', hΓ'', rfl⟩ := hΓ'
      obtain ⟨ε, hε, hmem⟩ := hrel Γ'' hΓ''
      refine ⟨ε, hε, ⟨_, hmem, ?_⟩⟩
      rw [hΓδρ, map_add, map_smul, map_sub]
    let HV : H → Divisor V.toScheme := fun h => DivisorWithCoeffs.restrictOpen V h.1
    have hHcV : ∀ h, (HV h).IsCartier := fun h => isCartier_comapDivisor V.ι (hH h.1 h.2).1
    have hHfreeV : ∀ h, ∃ m : ℕ, 0 < m ∧ IsRelativelyFreeDivisor πY ((m : ℤ) • HV h) := by
      intro h
      obtain ⟨m, hm, hmfree⟩ := (hH h.1 h.2).2
      refine ⟨m, hm, ?_⟩
      have := isRelativelyFreeDivisor_restrictOpen V hπY (((hH h.1 h.2).1).zsmul _) hmfree
      rwa [show DivisorWithCoeffs.restrictOpen V ((m : ℤ) • h.1) = (m : ℤ) • HV h from
        Finsupp.ext fun F => rfl] at this
    have hconeV : ∀ Γ' ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQV : Set (QDivisor V.toScheme))),
        ∃ c : H → ℝ, (∀ h, 0 ≤ c h) ∧
          Divisor.toRDivisor KY + Γ' = ∑ h, c h • Divisor.toRDivisor (HV h) := by
      intro Γ' hΓ'
      rw [hconvV] at hΓ'
      obtain ⟨Γ'', hΓ'', rfl⟩ := hΓ'
      obtain ⟨t, ht, htsum⟩ := hcone Γ'' hΓ''
      refine ⟨fun h => t h.1, fun h => ht _, ?_⟩
      have h1 := congrArg ρ htsum
      rw [map_add, map_sum] at h1
      rw [show Divisor.toRDivisor KY = ρ (Divisor.toRDivisor KYb) from Finsupp.ext fun F => rfl,
        h1, ← Finset.sum_coe_sort H]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [map_smul, hρZ]
    -- the fixed parts on the common model `p`, `q`
    obtain ⟨r, hr, h2⟩ := OneModel.exists_fixedParts_of_cone hSQ hQV hWon hTn.1 f πY hf hπYs φ
      p q hpB hqB hps hqs hqπ.symm D PX a hDcoeff hDsupp KY Γ PY b hΓcoeff hΓsupp hD' P Q hP hQ
      hqE hEδ VQV hΔVQV hrelV HV hHcV hHfreeV hconeV
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h2
    obtain ⟨ε₂, hε₂, h2⟩ := h2
    have hcoord : ∀ Ξ : RDivisor S, Ξ.support ⊆ Θ.support →
        D (fun i => Ξ (PX i)) = MMP.Flips.logCanonicalDivisor K Ξ := by
      intro Ξ hΞ
      change Divisor.toRDivisor K + ∑ i, Ξ (PX i) • Finsupp.single (PX i) (1 : ℝ) =
        Divisor.toRDivisor K + Ξ
      rw [← F3Help.eq_sum_smul_single hPX Ξ fun P hP => hPXmem P
        (Finset.mem_union_right _ (hΞ (Finsupp.mem_support_iff.mpr hP)))]
    refine ⟨ε₂, hε₂, r, hr, fun Ξ hΞ _ _ hclose k hk Dc hDc' hDk G hG => ?_⟩
    have hdist : dist (fun i => Ξ (PX i)) δ < ε₂ :=
      (dist_pi_lt_iff hε₂).mpr fun i => by rw [Real.dist_eq]; exact hclose (PX i)
    have hmem := F3Help.mem_rationalAffineHull_of_isInSmallestRationalAffineHull PX hΞ
    have hrk : Divisor.toRDivisor ((r : ℤ) • Dc) = (k : ℝ) • D (fun i => Ξ (PX i)) := by
      rw [hcoord Ξ hΞ.1]
      ext P
      have hkP := hDk P
      simp only [DivisorWithCoeffs.coeff_apply] at hkP
      have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
      change ((((r : ℤ) • Dc) P : ℤ) : ℝ) = (k : ℝ) * (MMP.Flips.logCanonicalDivisor K Ξ) P
      rw [Finsupp.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, ← hkP]
      change (r : ℝ) * ((k : ℝ) / r * (((K P : ℤ) : ℝ) + Ξ P)) = (k : ℝ) * (((K P : ℤ) : ℝ) + Ξ P)
      field_simp
    have := h2 hdist hmem k hk Dc hDc' hrk G hG
    rw [hDδ] at this
    exact this

end RestrictModel

/-! ### The rational birational program in dimension three -/

universe u

namespace RationalProgramThree

open TopologicalSpace MMP.Mori MMP.Fourfold

open MMP MMP.Flips in
/-- If `g'` represents `φ` at `η_P` and `g'(η_P) = η_E`, then the strict transform of `P` under
`φ` is `E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- `X ⟶ ⊤_ Scheme` is separated for a variety `X`. -/
private theorem isSeparated_terminal_of_isVariety {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX) : IsSeparated (X ↘ ⊤_ Scheme) := by
  have : IsSeparated sX := hX.toIsSeparated
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- A proper birational morphism `μ : Y ⟶ X` of varieties onto a normal variety is an isomorphism
over a neighbourhood of every point `x` of `X` whose local ring is a valuation ring (the generic
point, and the generic points of the prime divisors): the fibre over `x` is a single point, so
`x` lies in the finite-fibre locus, over which `μ` is an isomorphism. -/
private theorem mem_biregularLocus_of_valuationRing {Y X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) {μ : Y ⟶ X}
    [IsProper μ] (hY : MMP.Mori.IsVariety ℂ (μ ≫ sX)) (hμ : IsBirationalMorphism μ) (x : X)
    [ValuationRing (X.presheaf.stalk x)] : x ∈ biregularLocus μ := by
  have : IsIntegral Y := hY.toIsIntegral
  have : IsNormal X := hX.2
  have : IsDominant μ := hμ.isDominant
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (μ ≫ sX) := hY.toIsSeparated
  have : IsSeparated μ := IsSeparated.of_comp μ sX
  have hbij := hμ.functionFieldMap_bijective
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso μ
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hμ)).1 inferInstance
  let V : X.Opens := ⟨_, hU⟩
  have hxV : x ∈ V := by
    change (μ ⁻¹' {x}).Finite
    refine Set.Subsingleton.finite fun a ha b hb => ?_
    have ha' : μ a = x := ha
    have hb' : μ b = x := hb
    have : ValuationRing (X.presheaf.stalk (μ a)) := by rw [ha']; infer_instance
    have : ValuationRing (X.presheaf.stalk (μ b)) := by rw [hb']; infer_instance
    have := MMP.Positivity.isIso_stalkMap_of_valuationRing μ hbij a
    have := MMP.Positivity.isIso_stalkMap_of_valuationRing μ hbij b
    exact MMP.Positivity.eq_of_isIso_stalkMap μ hbij (hb'.trans ha'.symm)
  exact le_biregularLocus (f := μ) (V := V) hiso hxV

/-! ### Birationality at the generic point -/

/-- For integral schemes, a morphism is birational at the generic point when it maps the generic
point to the generic point and is an isomorphism on the stalks there. -/
private theorem isBirational_iff_of_isIntegral {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) : IsBirational f ↔
      f (genericPoint X) = genericPoint Y ∧ IsIso (f.stalkMap (genericPoint X)) := by
  unfold IsBirational
  rw [genericPoints_eq_singleton, genericPoints_eq_singleton, Set.bijOn_singleton]
  simp

/-- If `f` and `f ≫ g` are birational at the generic point, so is `g`. -/
private theorem isBirational_of_comp {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsBirational f) (hfg : IsBirational (f ≫ g)) :
    IsBirational g := by
  rw [isBirational_iff_of_isIntegral] at *
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hfg1, hfg2⟩ := hfg
  refine ⟨by rw [← hf1, ← Scheme.Hom.comp_apply, hfg1], ?_⟩
  rw [Scheme.Hom.stalkMap_comp] at hfg2
  have : IsIso (g.stalkMap (f (genericPoint X))) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hf2 hfg2
  exact hf1 ▸ this

/-! ### Crepant dlt lifts -/

open MMP.Threefold.Mori.OpenRestriction in
/-- The restriction of an snc divisor to an open subscheme is snc. -/
private theorem isSNC_restrictOpen {R : Type*} [Zero R] {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ E : MMP.Mori.PrimeDivisor X, LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ g)]
    {D : DivisorWithCoeffs R X} (hD : D.IsSNC g) (U : X.Opens) :
    (D.restrictOpen U).IsSNC (U.ι ≫ g) := by
  refine ⟨fun E₀ hE₀ => ?_, fun x => (sncStalk_restrict_iff U.ι D x).mpr (hD.2 (U.ι x))⟩
  have hsm := hD.1 (OpenWeilRestriction.primeDivisorMap U.ι E₀)
    (Finsupp.mem_support_iff.2 (Finsupp.mem_support_iff.1 hE₀ : D.restrictOpen U E₀ ≠ 0))
  rw [IsSmoothScheme, smoothLocus_eq_smoothLocus] at hsm
  exact (isSmoothScheme_comap_iff U.ι g (OpenWeilRestriction.primeDivisorMap U.ι E₀).idealSheaf
    E₀.idealSheaf (idealSheaf_comap_primeDivisorMap U.ι E₀)).mpr fun z _ => hsm ▸ trivial

section RIntersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A proper curve over `k` is a curve over `k`. -/
private theorem isCurve_properCurve (C : ProperCurve sX) :
    AlgebraicGeometry.IsCurve k (C.ι ≫ sX) where
  toIsIntegral := inferInstance
  toIsSeparated := inferInstance
  toLocallyOfFiniteType := (inferInstance : IsProper (C.ι ≫ sX)).toLocallyOfFiniteType
  toQuasiCompact := inferInstance
  topologicalKrullDim_eq_one := C.dim_eq

/-- A proper curve has more than one point. -/
private theorem not_subsingleton (C : ProperCurve sX) : ¬ Subsingleton C.scheme := fun _ => by
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : MMP.Flips.IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  refine not_subsingleton C ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := ν.surjective a
  obtain ⟨x', rfl⟩ := ν.surjective b
  exact (hy x).trans (hy x').symm

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{u}} {ν : C' ⟶ C.scheme}
    (hν : MMP.Flips.IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have hp : IsProper (ν ≫ C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z) (hf : IsBirationalMorphism f) [IsDominant f]
    [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : MMP.Flips.IsCurveNormalization ν)
    (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    degreeOn k sX (ν ≫ C.ι) hdim M = degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 := isCurve_properCurve C
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one_of_isBirationalMorphism ν hν.isBirationalMorphism, Nat.cast_one,
    one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [degreeOn, degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`, whichever normalization computes it. -/
private theorem eq_degreeOn {C : ProperCurve sX} {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : MMP.Flips.IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact degreeOn_normalization C hν hdim _

/-- Every Cartier divisor has an intersection number with a proper curve: the normalization
of the curve is a normal proper curve birational to it. -/
private theorem exists_isCartierIntersectionNumber (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) : ∃ d, MMP.Flips.IsCartierIntersectionNumber k sX C L hL d := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve k p := isCurve_properCurve C
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : MMP.Flips.IsCurveNormalization (normalizationOverField k p) :=
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
        exact MMP.Flips.isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV
          hiso }
  exact ⟨_, _, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le,
    rfl⟩

/-- A presentation `D = ∑ rⱼ Lⱼ` computes `D · C = ∑ rⱼ deg_C 𝒪_X(Lⱼ)`. -/
private theorem isRIntersectionNumber_sum (C : ProperCurve sX) {D : RDivisor X} {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    MMP.Flips.IsRIntersectionNumber k sX D r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) := by
  choose d hd using fun j => exists_isCartierIntersectionNumber C (L j) (hL j)
  refine ⟨hL, d, hD, hd, Finset.sum_congr rfl fun j _ => ?_⟩
  rw [eq_degreeOn (hd j)]

/-- **The two notions of relative nefness agree.** A `ℚ`-Cartier `ℚ`-divisor `D` whose real
divisor is `f`-nef, with intersection numbers computed from a presentation by Cartier divisors, is
`f`-nef in the `ℚ`-Cartier sense: both compute `D · C` as the degree of `D` along `C`. -/
private theorem isRelativelyNef_of_isRelativelyNef_toRDivisor [IsIntegral X] {Y : Scheme.{u}}
    {f : X ⟶ Y} {D : QDivisor X} (hD : D.IsQCartier)
    (h : MMP.Flips.IsRelativelyNef k sX f (QDivisor.toRDivisor D)) :
    QDivisor.IsRelativelyNef sX f D := by
  obtain ⟨m, r, L, hL, hDeq, hnn⟩ := h
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hD fun C hC => ?_
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
  have hx := isRIntersectionNumber_sum C r L hL hDeq
  have hy := isRIntersectionNumber_sum C (fun _ : Fin 1 => (1 : ℝ) / c) (fun _ => M)
    (fun _ => hM) hDR
  have heq := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ r L _ _ _ _ hx hy
  have h0 := hnn C hC _ hx
  rw [heq] at h0
  rw [QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX C.ι C.dim_le D hD M hM hMD]
  simp only [Finset.univ_unique, Finset.sum_singleton] at h0
  have : (0 : ℝ) ≤ ((M.degreeOn k sX C.ι C.dim_le hM : ℚ) / c : ℚ) := by
    push_cast
    rw [div_eq_mul_one_div, mul_comm]
    exact h0
  exact_mod_cast this

end RIntersection

/-! ### Prime divisors along a step of the program -/

/-- A map `φ : X ⤏ X'` over `Z` (for `f : X ⟶ Z`, `f⁺ : X' ⟶ Z`) satisfies `f⁺ ∘ φ = f` at every
point of its domain of definition, `Z` being separated. -/
private theorem apply_toPartialMap_hom {X X' Z : Scheme.{u}} [IsIntegral X] [X'.IsSeparated]
    [Z.IsSeparated] (f : X ⟶ Z) (fp : X' ⟶ Z) (φ : X.RationalMap X')
    (hφ : φ.compHom fp = f.toRationalMap) (x : X) (hx : x ∈ φ.domain) :
    fp (φ.toPartialMap.hom ⟨x, hx⟩) = f x := by
  have he : (φ.toPartialMap.compHom fp).toRationalMap = f.toPartialMap.toRationalMap := by
    change _ = f.toRationalMap
    rw [← hφ]
    conv_rhs => rw [← φ.toRationalMap_toPartialMap]
    rfl
  obtain ⟨W, hW, hWl, hWr, hEq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp he
  have hWl' : W ≤ φ.toPartialMap.domain := hWl
  have : IsDominant (X.homOfLE hWl') := AlgebraicGeometry.Opens.isDominant_homOfLE hW _
  have hEq' : X.homOfLE hWl' ≫ φ.toPartialMap.hom ≫ fp = X.homOfLE hWr ≫ X.topIso.hom ≫ f := by
    simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.compHom_hom,
      Scheme.Hom.toPartialMap_hom] at hEq
    exact hEq
  have key : φ.toPartialMap.hom ≫ fp = φ.toPartialMap.domain.ι ≫ f := by
    refine ext_of_isDominant (X.homOfLE hWl') ?_
    refine hEq'.trans ?_
    rw [Scheme.topIso_hom, Scheme.homOfLE_ι_assoc]
    exact Scheme.homOfLE_ι_assoc X hWr f
  exact congrArg (fun g : φ.toPartialMap.domain.toScheme ⟶ Z => g ⟨x, hx⟩) key

/-- A morphism restricting to an isomorphism over `V` is injective on the preimage of `V`. -/
private theorem eq_of_isIso_morphismRestrict {X Y : Scheme.{u}} (g : X ⟶ Y) (V : Y.Opens)
    [IsIso (g ∣_ V)] {a b : X} (ha : g a ∈ V) (h : g a = g b) : a = b := by
  have hb : g b ∈ V := h ▸ ha
  have hopen : IsOpenImmersion ((g ⁻¹ᵁ V).ι ≫ g) := by
    rw [← morphismRestrict_ι]; infer_instance
  have := ((g ⁻¹ᵁ V).ι ≫ g).isOpenEmbedding.injective
    (a₁ := (⟨a, ha⟩ : g ⁻¹ᵁ V)) (a₂ := ⟨b, hb⟩) h
  exact congrArg Subtype.val this

/-- **Prime divisors along a step.** Let `f : X ⟶ Z` and `f⁺ : X' ⟶ Z` be proper birational
morphisms of varieties onto a normal variety and `φ : X ⤏ X'` a map over `Z`. If a prime divisor
`F'` of `X'` lies over a prime divisor `Q` of `Z`, then `f` and `f⁺` are isomorphisms over a
neighbourhood `V₀` of `η_Q`, there is a prime divisor `F` of `X` over `Q`, and every divisor `D`
on `X` has `coeff_{F'} φ_* D = coeff_F D`. -/
private theorem exists_primeDivisor_of_isOver {X X' Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsIntegral Z] [IsLocallyNoetherian Z]
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ) (f : X ⟶ Z) (fp : X' ⟶ Z)
    [IsProper f] [IsProper fp] (hXv : MMP.Mori.IsVariety ℂ (f ≫ sZ))
    (hX'v : MMP.Mori.IsVariety ℂ (fp ≫ sZ)) (hf : IsBirationalMorphism f)
    (hfp : IsBirationalMorphism fp) (φ : X.RationalMap X') (hφ : φ.compHom fp = f.toRationalMap)
    (F' : MMP.Mori.PrimeDivisor X') (Q : MMP.Mori.PrimeDivisor Z)
    (hQ : fp F'.genericPoint = Q.genericPoint) :
    ∃ (F : MMP.Mori.PrimeDivisor X) (V₀ : Z.Opens) (hV : Q.genericPoint ∈ V₀),
      IsIso (f ∣_ V₀) ∧ IsIso (fp ∣_ V₀) ∧ f F.genericPoint = Q.genericPoint ∧
      ∀ D : QDivisor X, (MMP.Mori.RationalMap.transformDivisor φ D).coeff F' = D.coeff F := by
  classical
  have : IsNormal Z := hZ.2
  have : IsSeparated sZ := hZ.1.toIsSeparated
  have : Z.IsSeparated := ⟨by rw [← Limits.terminal.comp_from sZ]; infer_instance⟩
  have : IsSeparated (fp ≫ sZ) := hX'v.toIsSeparated
  have : X'.IsSeparated := ⟨by rw [← Limits.terminal.comp_from (fp ≫ sZ)]; infer_instance⟩
  have hsep := isSeparated_terminal_of_isVariety hX'v
  have := Q.isDiscreteValuationRing_localRing
  set V₀ : Z.Opens := biregularLocus f ⊓ biregularLocus fp
  have hQV : Q.genericPoint ∈ V₀ :=
    ⟨mem_biregularLocus_of_valuationRing hZ hXv hf _,
      mem_biregularLocus_of_valuationRing hZ hX'v hfp _⟩
  have hfV : IsIso (f ∣_ V₀) := isBiregular_iff_le_biregularLocus.mpr inf_le_left
  have hfpV : IsIso (fp ∣_ V₀) := isBiregular_iff_le_biregularLocus.mpr inf_le_right
  -- the point of `X` over `η_Q`
  set U : X.Opens := f ⁻¹ᵁ V₀
  have hUopen : IsOpenImmersion (U.ι ≫ f) := by rw [← morphismRestrict_ι]; infer_instance
  set y : U := (inv (f ∣_ V₀)) ⟨Q.genericPoint, hQV⟩
  have hfy : f (U.ι y) = Q.genericPoint := by
    have h1 : (f ∣_ V₀) y = ⟨Q.genericPoint, hQV⟩ := by
      change ((inv (f ∣_ V₀)) ≫ (f ∣_ V₀)) _ = _
      rw [IsIso.inv_hom_id]; rfl
    have h2 := congrArg (fun g : U.toScheme ⟶ Z => g y) (morphismRestrict_ι f V₀)
    change V₀.ι ((f ∣_ V₀) y) = f (U.ι y) at h2
    rw [← h2, h1]; rfl
  have hcoh : Order.coheight (U.ι y) = 1 := by
    rw [coheight_eq_of_isOpenImmersion U.ι, ← coheight_eq_of_isOpenImmersion (U.ι ≫ f)]
    change Order.coheight (f (U.ι y)) = 1
    rw [hfy, Q.coheight_genericPoint]
  set F : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
  have hFη : F.genericPoint = U.ι y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hfF : f F.genericPoint = Q.genericPoint := by rw [hFη, hfy]
  refine ⟨F, V₀, hQV, hfV, hfpV, hfF, fun D => ?_⟩
  -- the strict transform of `F` is `F'`, and only `F` maps to `F'`
  have hdom : ∀ P : MMP.Mori.PrimeDivisor X, P.genericPoint ∈ φ.domain := fun P =>
    MMP.Flips.RationalMap.mem_domain_of_coheight_le_one f fp φ hφ (by rw [P.coheight_genericPoint])
  have hg' : φ.toPartialMap.toRationalMap = φ := φ.toRationalMap_toPartialMap
  have hF' : F'.genericPoint = φ.toPartialMap.hom ⟨F.genericPoint, hdom F⟩ := by
    refine eq_of_isIso_morphismRestrict fp V₀ (hQ ▸ hQV) ?_
    rw [hQ, apply_toPartialMap_hom f fp φ hφ _ (hdom F), hfF]
  have hE := transformPrimeDivisor_eq_some_of_genericPoint_eq φ.toPartialMap hg' (hdom F) hF'
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hE (fun P hP => ?_) D
  have h1 :=
    MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hP φ.toPartialMap hg' (hdom P)
  have h2 : f P.genericPoint = f F.genericPoint := by
    rw [← apply_toPartialMap_hom f fp φ hφ _ (hdom P), ← h1, hQ, hfF]
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_isIso_morphismRestrict f V₀ (h2 ▸ hfF ▸ hQV) h2)

/-- **Valuations along a step.** With `f : X ⟶ Z`, `f⁺ : X' ⟶ Z` isomorphisms over `V₀ ∋ η_Q` and
prime divisors `F ⊆ X`, `F' ⊆ X'` over `Q`, the divisors `F` and `F'` over `S` (via
`π = g ∘ f` and `π' = g ∘ f⁺`) define the same valuation of `k(S)`. -/
private theorem valuation_eq_of_isIso_morphismRestrict {X X' Z S : Scheme.{0}} [IsIntegral S]
    {sS : S ⟶ Spec (.of ℂ)} (f : X ⟶ Z) (fp : X' ⟶ Z) (g : Z ⟶ S) {π : X ⟶ S} {π' : X' ⟶ S}
    (hπ : f ≫ g = π) (hπ' : fp ≫ g = π') (hX : IsNormalVariety ℂ (π ≫ sS))
    (hX' : IsNormalVariety ℂ (π' ≫ sS)) (hb : IsBirationalMorphism π)
    (hb' : IsBirationalMorphism π') (V₀ : Z.Opens) [IsIso (f ∣_ V₀)] [IsIso (fp ∣_ V₀)]
    (F : MMP.Mori.PrimeDivisor X) (F' : MMP.Mori.PrimeDivisor X') (hV : f F.genericPoint ∈ V₀)
    (h : fp F'.genericPoint = f F.genericPoint) :
    (⟨X', π', hX', hb', F'⟩ : DivisorOver ℂ sS).valuation =
      (⟨X, π, hX, hb, F⟩ : DivisorOver ℂ sS).valuation := by
  have hV' : fp F'.genericPoint ∈ V₀ := h ▸ hV
  let e : (fp ⁻¹ᵁ V₀).toScheme ≅ (f ⁻¹ᵁ V₀).toScheme := asIso (fp ∣_ V₀) ≪≫ (asIso (f ∣_ V₀)).symm
  refine MMP.Positivity.DivisorOver.valuation_eq_of_iso _ _ (fp ⁻¹ᵁ V₀) (f ⁻¹ᵁ V₀) hV' hV e ?_ ?_
  · change ((fp ∣_ V₀) ≫ inv (f ∣_ V₀)) ≫ (f ⁻¹ᵁ V₀).ι ≫ π = (fp ⁻¹ᵁ V₀).ι ≫ π'
    rw [← hπ, ← hπ', ← Category.assoc (f ⁻¹ᵁ V₀).ι, ← morphismRestrict_ι, ← Category.assoc,
      Category.assoc _ (inv _), IsIso.inv_hom_id_assoc, ← Category.assoc, morphismRestrict_ι,
      Category.assoc]
  · have hinj : Function.Injective (f ∣_ V₀) := (f ∣_ V₀).isOpenEmbedding.injective
    apply hinj
    change ((fp ∣_ V₀) ≫ inv (f ∣_ V₀) ≫ (f ∣_ V₀)) _ = _
    rw [IsIso.inv_hom_id, Category.comp_id]
    apply Subtype.ext
    have h1 := congrArg (fun k : (fp ⁻¹ᵁ V₀).toScheme ⟶ Z => k ⟨F'.genericPoint, hV'⟩)
      (morphismRestrict_ι fp V₀)
    have h2 := congrArg (fun k : (f ⁻¹ᵁ V₀).toScheme ⟶ Z => k ⟨F.genericPoint, hV⟩)
      (morphismRestrict_ι f V₀)
    change V₀.ι _ = fp F'.genericPoint at h1
    change V₀.ι _ = f F.genericPoint at h2
    exact h1.trans (h.trans h2.symm)

/-- A small contraction `f : X ⟶ Z` of integral schemes is birational, and maps the generic point
of every prime divisor of `X` to the generic point of a prime divisor of `Z`: it is an
isomorphism off closed subsets of codimension `≥ 2`. -/
private theorem isBirationalMorphism_and_exists_of_isSmall {k : Type u} [Field k]
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z] {sZ : Z ⟶ Spec (.of k)}
    {sX : X ⟶ Spec (.of k)} {f : X ⟶ Z} (h : MMP.Flips.IsSmall k sZ sX f) :
    IsBirationalMorphism f ∧ ∀ F : MMP.Mori.PrimeDivisor X,
      ∃ Q : MMP.Mori.PrimeDivisor Z, f F.genericPoint = Q.genericPoint := by
  obtain ⟨-, V, W, hV, hW, hle, hiso⟩ := h
  refine ⟨MMP.Flips.isBirationalMorphism_of_isIso_resLE f V.compl W.compl
    (MMP.Flips.nonempty_compl_of_two_le_closedsCodimension V hV)
    (MMP.Flips.nonempty_compl_of_two_le_closedsCodimension W hW) hle hiso, fun F => ?_⟩
  have hFV : F.genericPoint ∈ (V.compl : X.Opens) := by
    intro hmem
    have := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV) _ hmem
    rw [F.coheight_genericPoint] at this
    exact absurd this (by decide)
  have hopen : IsOpenImmersion (Scheme.Opens.ι (X := X) V.compl ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f hle]; infer_instance
  have hcoh : Order.coheight (f F.genericPoint) = 1 := by
    have h1 := coheight_eq_of_isOpenImmersion (Scheme.Opens.ι (X := X) V.compl ≫ f)
      (x := (⟨F.genericPoint, hFV⟩ : Scheme.Opens.toScheme (X := X) V.compl))
    have h2 := coheight_eq_of_isOpenImmersion (Scheme.Opens.ι (X := X) V.compl)
      (x := (⟨F.genericPoint, hFV⟩ : Scheme.Opens.toScheme (X := X) V.compl))
    change Order.coheight (f F.genericPoint) = _ at h1
    change Order.coheight F.genericPoint = _ at h2
    rw [h1, ← h2, F.coheight_genericPoint]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm⟩

/-- **The data of a step of a program.** The `i`-th step `X_i → Z_i ← X_{i+1}` of a relative
elementary dlt program consists of proper birational morphisms onto a normal variety `Z_i` over
`S`, with `φ_i : X_i ⤏ X_{i+1}` a map over `Z_i`, and every prime divisor of `X_{i+1}` lies over a
prime divisor of `Z_i` (for a divisorial step `X_{i+1} ≅ Z_i`; for a flip, `f⁺` is small). -/
private theorem exists_step {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    {π : X ⟶ S} {K : Divisor X} {B : QDivisor X} (P : RelativeDltProgram sX sS π K B) (i : ℕ)
    (hi : (i : ℕ∞) < P.n) :
    ∃ (_ : IsIntegral (P.Z i)) (_ : IsLocallyNoetherian (P.Z i)),
      IsNormalVariety ℂ (P.sZ i) ∧ IsProper (P.f i) ∧ IsProper (P.fp i) ∧
      MMP.Mori.IsVariety ℂ (P.f i ≫ P.sZ i) ∧ MMP.Mori.IsVariety ℂ (P.fp i ≫ P.sZ i) ∧
      IsBirationalMorphism (P.f i) ∧ IsBirationalMorphism (P.fp i) ∧
      P.f i ≫ P.gZ i = modelMap π P.πY i ∧ P.fp i ≫ P.gZ i = P.πY i ∧
      (P.φ i).compHom (P.fp i) = (P.f i).toRationalMap ∧
      ∀ F' : MMP.Mori.PrimeDivisor (P.Y i), ∃ Q : MMP.Mori.PrimeDivisor (P.Z i),
        P.fp i F'.genericPoint = Q.genericPoint := by
  have hstep := P.isElementaryDltStep i hi
  have hctr := hstep.isNegativeRelativeRayContraction.isNegativeExtremalContraction
  have hZ : IsNormalVariety ℂ (P.sZ i) := hctr.isNormalVariety_target
  have hcon := hctr.isContraction
  haveI : IsIntegral (P.Z i) := hZ.1.toIsIntegral
  haveI : LocallyOfFiniteType (P.sZ i) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (P.Z i) := LocallyOfFiniteType.isLocallyNoetherian (P.sZ i)
  haveI : IsSeparated (P.sZ i) := hZ.1.toIsSeparated
  haveI : QuasiCompact (P.sZ i) := hZ.1.toQuasiCompact
  have hf : IsProper (P.f i) := hcon.isProper
  have hfv : MMP.Mori.IsVariety ℂ (P.f i ≫ P.sZ i) := hcon.comp_eq ▸ hcon.isVariety_source
  have hfg := hstep.isNegativeRelativeRayContraction.isRelativeContractionOfFace.comp_eq
  rcases hstep.divisorial_or_flip with ⟨hfb, -, hiso, hmod⟩ | hflip
  · have hfpv : MMP.Mori.IsVariety ℂ (P.fp i ≫ P.sZ i) :=
      { toIsIntegral := inferInstance, toIsSeparated := inferInstance,
        toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
    refine ⟨inferInstance, inferInstance, hZ, hf, inferInstance, hfv, hfpv, hfb,
      isBirationalMorphism_of_isIso _, hfg, hstep.comp_eq, hmod.2, fun F' => ?_⟩
    have hcoh : Order.coheight (P.fp i F'.genericPoint) = 1 := by
      rw [coheight_eq_of_isOpenImmersion (P.fp i), F'.coheight_genericPoint]
    exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh,
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm⟩
  · obtain ⟨hfb, -⟩ := isBirationalMorphism_and_exists_of_isSmall hflip.isSmall_source
    obtain ⟨hfpb, hQ⟩ := isBirationalMorphism_and_exists_of_isSmall hflip.isSmall
    have hfpv : MMP.Mori.IsVariety ℂ (P.fp i ≫ P.sZ i) :=
      hflip.isSmall.comp_eq ▸ hflip.isSmall.isVariety_source
    exact ⟨inferInstance, inferInstance, hZ, hf, hflip.isProper, hfv, hfpv, hfb, hfpb, hfg,
      hstep.comp_eq, hflip.isModificationOf.2, hQ⟩

/-- **The models of a program over `S`.** Let `P` be a relative elementary dlt program over `S`
starting from a birational morphism `p : Y ⟶ S`. Every model `π_i : X_i ⟶ S`, `i ≤ n`, is
birational, and every prime divisor `F'` of `X_i` is the transform of a prime divisor `F` of `Y`:
they define the same valuation of `k(S)`, and `coeff_{F'} B_i = coeff_F B_0`. -/
private theorem isBirationalMorphism_and_exists_primeDivisor {S Y : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)} [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (p : Y ⟶ S) {KY : Divisor Y} {Γ : QDivisor Y}
    (hbir : IsBirationalMorphism p) (hYn : IsNormalVariety ℂ (p ≫ sS))
    (P : RelativeDltProgram (p ≫ sS) sS p KY Γ) :
    ∀ i : ℕ, (i : ℕ∞) ≤ P.n → ∃ hbi : IsBirationalMorphism (modelMap p P.πY i),
      ∀ (hni : IsNormalVariety ℂ (modelMap p P.πY i ≫ sS))
        (F' : MMP.Mori.PrimeDivisor (modelSeq Y P.Y i)), ∃ F : MMP.Mori.PrimeDivisor Y,
        (⟨_, modelMap p P.πY i, hni, hbi, F'⟩ : DivisorOver ℂ sS).valuation =
          (⟨Y, p, hYn, hbir, F⟩ : DivisorOver ℂ sS).valuation ∧
        (divisorSeq Γ P.BY i).coeff F' = Γ.coeff F := by
  intro i
  induction i with
  | zero => exact fun _ => ⟨hbir, fun hni F' => ⟨F', rfl, rfl⟩⟩
  | succ i ih =>
    intro hi
    have hi' : (i : ℕ∞) < P.n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self i) hi
    obtain ⟨hbi, hti⟩ := ih hi'.le
    obtain ⟨_, _, hZ, hf, hfp, hfv, hfpv, hfb, hfpb, hfg, hfpg, hφ, hQ⟩ := exists_step P i hi'
    have hmi := P.isRelativeDltModel i hi'.le
    have hmi1 := P.isRelativeDltModel (i + 1) hi
    have : IsProper (P.πY i) := isProper_of_isProjectiveMorphism _ hmi1.isProjectiveMorphism
    -- the next model is birational over `S`
    have hBi := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbi
    have hBf := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb
    have hBfp := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfpb
    have hBg : IsBirational (P.gZ i) := isBirational_of_comp hBf (hfg ▸ hBi)
    have hB' : IsBirational (P.πY i) := hfpg ▸ hBfp.comp hBg
    have hbi' : IsBirationalMorphism (P.πY i) := by
      have := isBirationalMorphism_comp_of_isBirational (P.πY i) (𝟙 _) hB'
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
          (isBirationalMorphism_of_isIso _))
      simpa using this
    refine ⟨hbi', fun hni F' => ?_⟩
    obtain ⟨Q, hQF⟩ := hQ F'
    obtain ⟨F, V₀, hV, hfV, hfpV, hfF, hcoeff⟩ := exists_primeDivisor_of_isOver hZ (P.f i)
      (P.fp i) hfv hfpv hfb hfpb (P.φ i) hφ F' Q hQF
    have hni_i : IsNormalVariety ℂ (modelMap p P.πY i ≫ sS) :=
      hmi.comp_eq ▸ hmi.isQFactorial.1
    obtain ⟨F₀, hv0, hc0⟩ := hti hni_i F
    refine ⟨F₀, ?_, ?_⟩
    · exact (valuation_eq_of_isIso_morphismRestrict (P.f i) (P.fp i) (P.gZ i) hfg hfpg hni_i hni
        hbi hbi' V₀ F F' (hfF ▸ hV) (hQF.trans hfF.symm)).trans hv0
    · change (P.BY i).coeff F' = _
      rw [P.BY_eq i hi', hcoeff, hc0]

/-- A birational proper morphism `π : U ⟶ S` onto a normal variety does not factor through a
scheme `T` of smaller dimension: over the open subset of `S` where `π` is an isomorphism,
`U ⟶ T` is a topological embedding, so `dim U ≤ dim T`. -/
private theorem topologicalKrullDim_le_of_comp_eq {U T S : Scheme.{0}} [IsIntegral U]
    [IsIntegral S] [IsLocallyNoetherian S] {sS : S ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sS)
    {πU : U ⟶ S} [IsProper πU] (hUv : MMP.Mori.IsVariety ℂ (πU ≫ sS))
    (hb : IsBirationalMorphism πU) (g : U ⟶ T) (gT : T ⟶ S) (h : g ≫ gT = πU) :
    topologicalKrullDim U ≤ topologicalKrullDim T := by
  haveI : ValuationRing (S.presheaf.stalk (genericPoint S)) :=
    inferInstanceAs (ValuationRing S.functionField)
  have hA := mem_biregularLocus_of_valuationRing hX hUv hb (genericPoint S)
  have hiso : IsIso (πU ∣_ biregularLocus πU) := isBiregular_biregularLocus πU
  haveI : IsDominant πU := hb.isDominant
  set W : U.Opens := πU ⁻¹ᵁ biregularLocus πU
  have hWne : (W : Set U).Nonempty := ⟨genericPoint U, by
    change πU (genericPoint U) ∈ biregularLocus πU
    rw [map_genericPoint_of_isDominant]; exact hA⟩
  have hopen : IsOpenImmersion (W.ι ≫ πU) := by rw [← morphismRestrict_ι]; infer_instance
  have hind : Topology.IsInducing (W.ι ≫ g).base := by
    refine Topology.IsInducing.of_comp (W.ι ≫ g).base.hom.continuous gT.base.hom.continuous ?_
    have : (W.ι ≫ πU).base = (W.ι ≫ g).base ≫ gT.base := by
      rw [← h, ← Category.assoc, Scheme.Hom.comp_base]
    have h2 := (W.ι ≫ πU).isOpenEmbedding.isInducing
    rw [this] at h2
    exact h2
  haveI : AlgebraicGeometry.IsVariety ℂ (πU ≫ sS) := hUv
  rw [AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ U (πU ≫ sS) _ W.isOpen hWne]
  exact hind.topologicalKrullDim_le

/-! ### The birational map to the last model -/

section BirationalMap

/-- Two morphisms `h₁ h₂ : T ⟶ Y` from a reduced irreducible scheme with `h₁ ≫ q = h₂ ≫ q` are
equal, if `q : Y ⟶ Z` is separated and an isomorphism over an open `V ⊆ Z` met by `h₁ ≫ q`. -/
private theorem eq_of_comp_eq_of_isIso_morphismRestrict {T Y Z : Scheme.{u}} [IsReduced T]
    [IrreducibleSpace T] (q : Y ⟶ Z) [IsSeparated q] (V : Z.Opens) [IsIso (q ∣_ V)]
    {h₁ h₂ : T ⟶ Y} (h : h₁ ≫ q = h₂ ≫ q) {t : T} (ht : (h₁ ≫ q) t ∈ V) : h₁ = h₂ := by
  set O : T.Opens := (h₁ ≫ q) ⁻¹ᵁ V
  haveI : IsDominant O.ι := Opens.isDominant_ι (O.2.dense ⟨t, ht⟩)
  refine ext_of_isDominant_of_isSeparated q h O.ι ?_
  have hr : ∀ g : T ⟶ Y, g ≫ q = h₁ ≫ q →
      Set.range (O.ι ≫ g) ⊆ Set.range (q ⁻¹ᵁ V).ι := by
    rintro g hg _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : ((O.ι ≫ g) ≫ q) x ∈ V := by
      rw [Category.assoc, hg, Scheme.Hom.comp_apply]
      exact x.2
    rwa [Scheme.Hom.comp_apply] at this
  have hmono : Mono ((q ⁻¹ᵁ V).ι ≫ q) := by
    rw [← morphismRestrict_ι]; infer_instance
  have e₁ := IsOpenImmersion.lift_fac _ _ (hr h₁ rfl)
  have e₂ := IsOpenImmersion.lift_fac _ _ (hr h₂ h.symm)
  rw [← e₁, ← e₂]
  congr 1
  refine (cancel_mono ((q ⁻¹ᵁ V).ι ≫ q)).mp ?_
  rw [← Category.assoc, e₁, ← Category.assoc, e₂, Category.assoc, Category.assoc, h]

/-- A partial map representing a rational map `φ : X ⤏ X'` over `Z` lies over `Z`. -/
private theorem hom_comp_eq_of_compHom_eq {X X' Z : Scheme.{u}} [IsReduced X]
    [IsSeparated (Z ↘ ⊤_ Scheme)] (f : X ⟶ Z) (fp : X' ⟶ Z) (g : X.PartialMap X')
    (h : g.toRationalMap.compHom fp = f.toRationalMap) : g.hom ≫ fp = g.domain.ι ≫ f :=
  (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp (by
      rw [Scheme.RationalMap.compHom_toRationalMap]; exact h))

/-- The generic point of an irreducible scheme lies in every nonempty open subset. -/
private theorem genericPoint_mem {X : Scheme.{u}} [IrreducibleSpace X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.2).mpr (by simpa using hU)

/-- **The birational map between two models over `Z`.** Let `p : W ⟶ Z` and `q : Y ⟶ Z` be
proper birational morphisms from normal varieties onto a normal variety. There is a birational
map `φ : W ⤏ Y` over `Z`; for prime divisors `D ⊆ W`, `Q ⊆ Y` defining the same valuation of
`k(Z)`, the transform of `D` is `Q`, and `D` is the only prime divisor whose transform is `Q`. -/
private theorem exists_isBirational_isOver_of_valuation_eq {W Y Z : Scheme.{0}}
    [IsIntegral W] [IsIntegral Y] [IsIntegral Z] [IsLocallyNoetherian Z]
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ) (p : W ⟶ Z) (q : Y ⟶ Z)
    [IsProper p] [IsProper q] (hW : IsNormalVariety ℂ (p ≫ sZ))
    (hY : IsNormalVariety ℂ (q ≫ sZ)) (hp : IsBirationalMorphism p)
    (hq : IsBirationalMorphism q) :
    ∃ φ : W.RationalMap Y, MMP.Mori.RationalMap.IsBirational φ ∧
      MMP.Flips.RationalMap.IsOver p q φ ∧
      ∀ (D : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor Y),
        (⟨W, p, hW, hp, D⟩ : DivisorOver ℂ sZ).valuation =
            (⟨Y, q, hY, hq, Q⟩ : DivisorOver ℂ sZ).valuation →
          MMP.Mori.RationalMap.transformPrimeDivisor φ D = some Q ∧
            ∀ D', MMP.Mori.RationalMap.transformPrimeDivisor φ D' = some Q → D' = D := by
  classical
  haveI : IsNormal Z := hZ.2
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  have hsepZ : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_terminal_of_isVariety hZ.1
  have hsepY : IsSeparated (Y ↘ ⊤_ Scheme) := isSeparated_terminal_of_isVariety hY.1
  haveI : ValuationRing (Z.presheaf.stalk (genericPoint Z)) :=
    inferInstanceAs (ValuationRing Z.functionField)
  haveI : IsDominant p := hp.isDominant
  haveI : IsDominant q := hq.isDominant
  set V : Z.Opens := biregularLocus p ⊓ biregularLocus q
  have hηV : genericPoint Z ∈ V :=
    ⟨mem_biregularLocus_of_valuationRing hZ hW.1 hp _,
      mem_biregularLocus_of_valuationRing hZ hY.1 hq _⟩
  haveI hpV : IsIso (p ∣_ V) := isBiregular_iff_le_biregularLocus.mpr inf_le_left
  haveI hqV : IsIso (q ∣_ V) := isBiregular_iff_le_biregularLocus.mpr inf_le_right
  have hpη : p (genericPoint W) ∈ V := by rw [map_genericPoint_of_isDominant]; exact hηV
  have hqη : q (genericPoint Y) ∈ V := by rw [map_genericPoint_of_isDominant]; exact hηV
  let e₀ : W.PartialIso Y :=
    { source := p ⁻¹ᵁ V
      dense_source := (p ⁻¹ᵁ V).2.dense ⟨_, hpη⟩
      target := q ⁻¹ᵁ V
      dense_target := (q ⁻¹ᵁ V).2.dense ⟨_, hqη⟩
      iso := asIso (p ∣_ V) ≪≫ (asIso (q ∣_ V)).symm }
  have he₀ : e₀.iso.hom ≫ e₀.target.ι ≫ q = e₀.source.ι ≫ p := by
    change (p ∣_ V) ≫ inv (q ∣_ V) ≫ (q ⁻¹ᵁ V).ι ≫ q = (p ⁻¹ᵁ V).ι ≫ p
    rw [← morphismRestrict_ι, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  -- every partial map over `Z` represents `e₀`
  have hrep : ∀ g : W.PartialMap Y, g.hom ≫ q = g.domain.ι ≫ p →
      g.toRationalMap = e₀.toRationalMap := by
    intro g hg
    set O : W.Opens := g.domain ⊓ e₀.source
    have hO : Dense (O : Set W) := g.dense_domain.inter_of_isOpen_left e₀.dense_source g.domain.2
    have hηO : genericPoint W ∈ O := genericPoint_mem O hO.nonempty
    haveI : Nonempty O := ⟨⟨_, hηO⟩⟩
    refine Scheme.PartialMap.toRationalMap_eq_iff.mpr ⟨O, hO, inf_le_left, inf_le_right, ?_⟩
    change W.homOfLE inf_le_left ≫ g.hom = W.homOfLE inf_le_right ≫ e₀.iso.hom ≫ e₀.target.ι
    have hc : (W.homOfLE inf_le_left ≫ g.hom) ≫ q =
        (W.homOfLE inf_le_right ≫ e₀.iso.hom ≫ e₀.target.ι) ≫ q := by
      simp only [Category.assoc, hg, he₀, Scheme.homOfLE_ι_assoc]
    refine eq_of_comp_eq_of_isIso_morphismRestrict q V hc (t := ⟨_, hηO⟩) ?_
    rw [Category.assoc, hg, Scheme.homOfLE_ι_assoc]
    exact hpη
  have hover : MMP.Flips.RationalMap.IsOver p q e₀.toRationalMap := by
    change e₀.toRationalMap.compHom q = p.toPartialMap.toRationalMap
    rw [Scheme.PartialIso.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap]
    refine Scheme.PartialMap.toRationalMap_eq_iff.mpr
      ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mpr ?_)
    change (e₀.iso.hom ≫ e₀.target.ι) ≫ q = e₀.source.ι ≫ p
    rw [Category.assoc, he₀]
  refine ⟨e₀.toRationalMap, ⟨e₀, rfl⟩, hover, fun D Q hv => ?_⟩
  obtain ⟨U, V', hU, hV', e, h1, h2⟩ :=
    MMP.Positivity.DivisorOver.exists_iso_of_valuation_eq hZ.1 _ _ hv
  change D.genericPoint ∈ U at hU
  change Q.genericPoint ∈ V' at hV'
  change e.hom ≫ V'.ι ≫ q = U.ι ≫ p at h1
  change e.hom ⟨D.genericPoint, hU⟩ = ⟨Q.genericPoint, hV'⟩ at h2
  let g' : W.PartialMap Y := ⟨U, U.2.dense ⟨_, hU⟩, e.hom ≫ V'.ι⟩
  have hg' : g'.toRationalMap = e₀.toRationalMap :=
    hrep g' (by change (e.hom ≫ V'.ι) ≫ q = U.ι ≫ p; rw [Category.assoc, h1])
  have hDQ : MMP.Mori.RationalMap.transformPrimeDivisor e₀.toRationalMap D = some Q := by
    refine transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hU ?_
    change Q.genericPoint = V'.ι (e.hom ⟨D.genericPoint, hU⟩)
    rw [h2]; rfl
  refine ⟨hDQ, fun D' hD'Q => ?_⟩
  obtain ⟨g, hD', hg⟩ := MMP.Mori.RationalMap.definedAt_iff.mp
    (MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hD'Q).1
  have hgQ : Q.genericPoint = g.hom ⟨D'.genericPoint, hD'⟩ :=
    MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hD'Q g hg hD'
  have hgover : g.hom ≫ q = g.domain.ι ≫ p := hom_comp_eq_of_compHom_eq p q g (by rw [hg]; exact hover)
  set O : g.domain.toScheme.Opens := g.hom ⁻¹ᵁ V'
  have hoO : (⟨D'.genericPoint, hD'⟩ : g.domain.toScheme) ∈ O := by
    change g.hom _ ∈ V'
    rw [← hgQ]; exact hV'
  let o : O.toScheme := ⟨_, hoO⟩
  haveI : Nonempty g.domain.toScheme := ⟨⟨_, hD'⟩⟩
  haveI : Nonempty O.toScheme := ⟨o⟩
  haveI : IsDominant (O.ι ≫ g.domain.ι) := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  have hcomp : ((g.hom ∣_ V') ≫ e.inv ≫ U.ι) ≫ p = (O.ι ≫ g.domain.ι) ≫ p := by
    have h1' : e.inv ≫ U.ι ≫ p = V'.ι ≫ q := by
      rw [← h1, Iso.inv_hom_id_assoc]
    rw [Category.assoc, Category.assoc, h1', ← Category.assoc, morphismRestrict_ι,
      Category.assoc, hgover, Category.assoc]
  have heq := eq_of_comp_eq_of_isIso_morphismRestrict p V hcomp (t := genericPoint O.toScheme)
    (by
      rw [hcomp, Scheme.Hom.comp_apply, map_genericPoint_of_isDominant]
      exact hpη)
  have hval := congrArg (fun k : O.toScheme ⟶ W => k o) heq
  have hrest : (g.hom ∣_ V') o = ⟨Q.genericPoint, hV'⟩ := by
    apply Subtype.ext
    have := congrArg (fun k : O.toScheme ⟶ Y => k o) (morphismRestrict_ι g.hom V')
    change V'.ι ((g.hom ∣_ V') o) = g.hom (O.ι o) at this
    exact this.trans hgQ.symm
  have hinv : e.inv ⟨Q.genericPoint, hV'⟩ = ⟨D.genericPoint, hU⟩ := by
    rw [← h2]
    change (e.hom ≫ e.inv) _ = _
    rw [Iso.hom_inv_id]; rfl
  change U.ι (e.inv ((g.hom ∣_ V') o)) = g.domain.ι (O.ι o) at hval
  rw [hrest, hinv] at hval
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective hval.symm

end BirationalMap

section Main

attribute [local instance] AlgebraicGeometry.IsVariety.toIsIntegral
attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **The rational birational program property `Q(3)`.** -/
private theorem rationalBirationalProgramProperty_three :
    MMP.Fourfold.RationalBirationalProgramProperty 3 := by
  classical
  refine ⟨by norm_num, ?_⟩
  intro W _ _ _ _ sW Z sZ p hWp hWn hWsm hWd hZp hZn hZd hpZ hpproj hpbir K hK C hC hsnc
  subst hpZ
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsNormal Z := hZn.2
  haveI : QuasiCompact sZ := hZn.1.toQuasiCompact
  haveI : QuasiCompact (p ≫ sZ) := hWn.1.toQuasiCompact
  haveI : LocallyOfFiniteType (p ≫ sZ) := hWn.1.toLocallyOfFiniteType
  have : IsProper p := isProper_of_isProjectiveMorphism p hpproj
  -- the smooth snc pair `(W, C)` is `ℚ`-factorial and dlt
  have hQW : IsQFactorial (p ≫ sZ) := ⟨hWn, fun D => ⟨1, one_pos, by
    simpa using MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hWsm D⟩⟩
  have hdltM : MMP.Mori.IsDltPair (p ≫ sZ) 3 K C := by
    refine ⟨⟨hWn, hK, MMP.Fourfold.isQCartier_of_isQFactorial _ hQW _⟩,
      fun P => ⟨(hC P).1, (hC P).2.le⟩, ⊤, hWsm.ge, isSNC_restrictOpen (p ≫ sZ) hsnc ⊤, ?_⟩
    intro D a hD _
    exfalso
    obtain ⟨x, hx⟩ := D.center.isIrreducible.nonempty
    exact hD hx (by simp)
  have hdlt : MMP.Intersection.IsDltPair (p ≫ sZ) C :=
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair (p ≫ sZ) hK C).mpr hdltM
  -- the threefold log minimal model program over `Z`
  obtain ⟨-, -, P, hPproj, hPn, hPend⟩ := MMP.Fourfold.projectiveLowerLogMMP_three.2 W Z
    (p ≫ sZ) sZ p K C hWp hZp rfl hWd.le hQW ⟨3, hK⟩ hdlt
  set m := P.n.toNat with hmdef
  have hm : (m : ℕ∞) ≤ P.n := ENat.coe_toNat_le_self _
  have hmod := P.isRelativeDltModel m hm
  set U := modelSeq W P.Y m
  set πU : U ⟶ Z := modelMap p P.πY m with hπUdef
  have hcomp : πU ≫ sZ = modelStr (p ≫ sZ) P.sY m := hmod.comp_eq
  have hQU : IsQFactorial (πU ≫ sZ) := hcomp ▸ hmod.isQFactorial
  have hUnv : IsNormalVariety ℂ (πU ≫ sZ) := hQU.1
  have hprojU : IsProjectiveMorphism πU := hmod.isProjectiveMorphism
  have : IsProper πU := isProper_of_isProjectiveMorphism πU hprojU
  haveI : QuasiCompact (modelStr (p ≫ sZ) P.sY m) := hmod.isQFactorial.1.1.toQuasiCompact
  -- every model is birational over `Z`, and its prime divisors come from `W`
  obtain ⟨hbirU, htrack0⟩ := isBirationalMorphism_and_exists_primeDivisor p hpbir hWn P m hm
  have htrack := htrack0 hUnv
  -- no fibre-type contraction over the base `Z`
  have hnotFinal : ¬ P.hasFinal := by
    intro hfin
    obtain ⟨-, hctr, hlt⟩ := P.final_spec hfin
    have hle := topologicalKrullDim_le_of_comp_eq hZn hUnv.1 hbirU P.g P.gT
      hctr.isRelativeContractionOfFace.comp_eq
    exact absurd hlt (not_lt.mpr hle)
  obtain ⟨φ, hφb, hφo, hφ⟩ :=
    exists_isBirational_isOver_of_valuation_eq hZn p πU hWn hUnv hpbir hbirU
  refine ⟨P, hPn, hPproj, hnotFinal, hmod.isQFactorial, hPproj.2 m hm, hprojU, ?_, ?_, φ, hφb,
    hφo, ?_, ?_⟩
  · -- the boundary coefficients stay below one, so the dlt pair is klt
    refine MMP.Intersection.IsDltPair.isKltPair_of_forall_coeff_lt_one hmod.isDltPair fun F' => ?_
    obtain ⟨F, -, hc⟩ := htrack F'
    rw [hc]; exact (hC F).2
  · exact isRelativelyNef_of_isRelativelyNef_toRDivisor
      (MMP.Fourfold.isQCartier_of_isQFactorial _ hmod.isQFactorial _)
      (hPend.resolve_right hnotFinal)
  · refine DivisorWithCoeffs.ext' fun Q => ?_
    obtain ⟨F, hv, hc⟩ := htrack Q
    obtain ⟨hFQ, huniq⟩ := hφ F Q hv.symm
    rw [hc]
    exact (MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hFQ huniq C).symm
  · intro Q
    obtain ⟨F, hv, -⟩ := htrack Q
    exact ⟨F, (hφ F Q hv.symm).1⟩

end Main

end RationalProgramThree

section Clauses

variable {S T : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sS] {sT : T ⟶ Spec (.of ℂ)} {f : S ⟶ T}
    (hSQ : IsQFactorial sS) (hdim : topologicalKrullDim S = 3)
    (hT : IsNormalVariety ℂ sT) (hTa : IsAffine T) (hf : f ≫ sT = sS)
    (hfp : IsProjectiveMorphism f) (hfb : IsBirationalMorphism f)
    {Θ : RDivisor S} (hΘ : ∀ P, 0 ≤ Θ.coeff P) (hklt : IsRealKltPair sS Θ)
    {K : Divisor S} (hK : K.IsCanonicalDivisor sS 3)

include hSQ hdim hT hTa hf hfp hfb hΘ hklt hK

/-- A compactification `S ⊆ S̄ ⟶ T̄ ⊇ T` of `f`, with the extended klt boundary, the extended
canonical divisor, `ℝ`-Cartier presentations of all real divisors with pseudo-effective classes
over `T̄`, the relative bigness of `0` over `T̄` and the description of the smallest rational
affine hull. -/
private theorem exists_compactificationData :
    ∃ (Tb : Scheme.{0}) (sTb : Tb ⟶ Spec (.of ℂ)) (j : T ⟶ Tb) (_ : IsOpenImmersion j)
      (Sb : Scheme.{0}) (_ : IsIntegral Sb) (_ : IsLocallyNoetherian Sb) (_ : IsNormal Sb)
      (_ : CompactSpace Sb) (fb : Sb ⟶ Tb) (i : S ⟶ Sb) (_ : IsOpenImmersion i)
      (_ : IsDominant i) (Kb : Divisor Sb),
      IsNormalVariety ℂ sTb ∧ MMP.Mori.IsProjectiveVariety ℂ sTb ∧ j ≫ sTb = sT ∧
      IsProjectiveMorphism fb ∧ IsPullback i f fb j ∧
      MMP.Mori.IsProjectiveVariety ℂ (fb ≫ sTb) ∧ IsQFactorial (fb ≫ sTb) ∧
      IsRealKltPair (fb ≫ sTb) (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Θ) ∧
      IsBirationalMorphism fb ∧ topologicalKrullDim Sb = 3 ∧
      Kb.IsCanonicalDivisor (fb ≫ sTb) 3 ∧
      (∀ P, Kb.coeff (OpenWeilRestriction.primeDivisorMap i P) = K.coeff P) ∧
      (∀ B : RDivisor Sb, ∃ (m : ℕ) (r : Fin m → ℝ) (E : Fin m → Sb.CartierDivisor)
          (w : Fin m → Divisor Sb),
        (∀ k, MMP.Intersection.IsWeilDivisorOfCartier (E k) (w k)) ∧
        B = ∑ k, r k • Divisor.toRDivisor (w k) ∧
        KCartierDivisor.IsRelativelyPseudoEffective (fb ≫ sTb) fb
          (∑ k, Finsupp.single (E k) (r k))) ∧
      (0 : QDivisor Sb).IsRelativelyBig fb ∧
      (∀ Ψ : RDivisor Sb, IsInSmallestRationalAffineHull
          (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Θ) Ψ ↔
        ∃ Φ : RDivisor S, IsInSmallestRationalAffineHull Θ Φ ∧
          Ψ = Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Φ) := by
  haveI := hTa
  have hTi : IsIntegral T := hT.1.toIsIntegral
  obtain ⟨Tb, sTb, j, hTp, hTn, hj, hjs, Sb, h1, h2, h3, sSb, fb, i, hi, hSp, hSQb, hfbp, hfbs,
    hpb, hΘk, hhull⟩ :=
    exists_realKltCompactification_of_rationalBirationalProgramProperty (d := 3) (by norm_num)
      RationalProgramThree.rationalBirationalProgramProperty_three sT hT sS hSQ
      (by exact_mod_cast hdim) f hf hfp Θ hΘ
      hklt
  subst hfbs
  haveI := hSp
  haveI : IsIntegral Tb := hTn.1.toIsIntegral
  haveI : CompactSpace Sb := QuasiCompact.compactSpace_of_compactSpace (fb ≫ sTb)
  haveI : Nonempty S := ⟨genericPoint S⟩
  haveI : IsDominant i := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion i
  have hiS : i ≫ fb ≫ sTb = sS := by rw [← Category.assoc, hpb.w, Category.assoc, hjs, hf]
  have hfbb : IsBirationalMorphism fb := isBirationalMorphism_of_comp_eq hpb.w hfb
  haveI : MMP.Mori.IsVariety ℂ sS := hklt.1.1
  haveI : MMP.Mori.IsVariety ℂ (fb ≫ sTb) := hSQb.1.1
  have hdimb : topologicalKrullDim Sb = 3 :=
    (topologicalKrullDim_eq_of_isOpenImmersion sS (fb ≫ sTb) i).trans hdim
  have hK' : K.IsCanonicalDivisor (i ≫ fb ≫ sTb) 3 := by rw [hiS]; exact hK
  obtain ⟨Kb, hKb, hKbc⟩ := exists_isCanonicalDivisor_coeff_primeDivisorMap hSQb.1 i hK'
  haveI : IsProper fb := isProper_of_isProjectiveMorphism fb hfbp
  have hbir : IsBirationalMorphism fb.toImage := MMP.Fourfold.isBirationalMorphism_toImage fb hfbb
  have hpe := isRelativelyPseudoEffective_and_isRelativelyBig_zero_of_isBirationalMorphism_toImage
    (fb ≫ sTb) sTb fb hSp hSQb hTp hTn rfl hbir
  refine ⟨Tb, sTb, j, hj, Sb, h1, h2, h3, inferInstance, fb, i, hi, inferInstance, Kb, hTn, hTp,
    hjs, hfbp, hpb, hSp, hSQb, hΘk, hfbb, hdimb, hKb, hKbc, fun B => ?_, hpe.2, hhull⟩
  obtain ⟨m, r, L, hL, hcoeff⟩ := hSQb.isRCartier B
  choose A hA using fun k => exists_isWeilDivisorOfCartier_of_isCartier (hL k)
  refine ⟨m, r, A, L, hA, ?_, hpe.1 _⟩
  refine Finsupp.ext fun P => ?_
  have := hcoeff P
  rw [DivisorWithCoeffs.coeff_apply] at this
  rw [this, Finsupp.finset_sum_apply]
  rfl

/-- The log terminal model of `(S, Θ)` over `T` and the fixed parts along the smallest rational
affine hull, restricted from the compactification. -/
private theorem logTerminalModel_and_fixedParts :
    (∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
        (sY : Y ⟶ Spec (.of ℂ)) (_ : QuasiCompact sY) (πY : Y ⟶ T) (KY : Divisor Y)
        (φ : S.RationalMap Y),
      πY ≫ sT = sY ∧ IsProjectiveMorphism πY ∧ IsQFactorial sY ∧
        KY.IsCanonicalDivisor sY 3 ∧
        IsRealKltPair sY (RationalMap.transformDivisor φ Θ) ∧
        RationalMap.IsBirational φ ∧ MMP.Flips.RationalMap.IsOver f πY φ ∧
        (∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F) ∧
        MMP.Flips.IsRelativelyNef ℂ sY πY
          (MMP.Flips.logCanonicalDivisor KY (RationalMap.transformDivisor φ Θ)) ∧
        ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
          (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ S) (q : W ⟶ Y) (h : S.RationalMap W)
          (GS GY : RDivisor W),
          IsLogComparisonResolution sS sY sW φ K Θ KY (RationalMap.transformDivisor φ Θ)
            p q h GS GY ∧
          ∀ P : MMP.Mori.PrimeDivisor S, RationalMap.IsExceptional φ P →
            ∀ P' : MMP.Mori.PrimeDivisor W, RationalMap.transformPrimeDivisor h P = some P' →
              0 < (GS - GY).coeff P') ∧
    (∃ ε : ℝ, 0 < ε ∧ ∃ r : ℕ, 0 < r ∧ ∀ Φ : RDivisor S, IsInSmallestRationalAffineHull Θ Φ →
      (∀ P, 0 ≤ Φ.coeff P) → IsRealKltPair sS Φ →
      (∀ P, |Φ.coeff P - Θ.coeff P| < ε) →
      ∀ k : ℕ, 0 < k → ∀ D : Divisor S, D.IsCartier →
        (∀ P, (k : ℝ) / r *
        (MMP.Mori.DivisorWithCoeffs.coeff (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K) P +
            Φ.coeff P) = D.coeff P) →
          ∀ G : MMP.Mori.PrimeDivisor S, 0 < relativeFixedMultiplicity f ((r : ℤ) • D) G →
            IsInRelativeDivisorialStableBase f
              ((Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K) + Θ) G) := by
  classical
  obtain ⟨Tb, sTb, j, hj, Sb, h1, h2, h3, h4, fb, i, hi, hid, Kb, hTn, hTp, hjs, hfbp, hpb, hSp,
    hSQb, hΘk, hfbb, hdimb, hKb, hKbc, hpsef, hbig, -⟩ :=
    exists_compactificationData hSQ hdim hT hTa hf hfp hfb hΘ hklt hK
  obtain ⟨Yb, _, _, _, sYb, _, πYb, φb, hNW, hYQ, hYk, Wb, _, _, _, sWb, pb, qb, hb, hWv, hWsm,
    hpbs, hqbs, hpbp, hqbp, hpbb, hqbb, hinv, hcomp, GX, GY, hGX, hGY, heff, hexc, hpos⟩ :=
    IsRealKltPair.exists_isNefWeakModel_of_isRelativelyPseudoEffective hSp hTp rfl hSQb hdimb
      ⟨3, hKb⟩ (mapDomain_nonneg _ hΘ) hΘk (hpsef _)
  have hiS : i ≫ fb ≫ sTb = sS := by rw [← Category.assoc, hpb.w, Category.assoc, hjs, hf]
  exact (logTerminalModel_of_compactification hSQ hf hTn hjs hpb hiS hT hTp hSp hSQb hbig hΘ hKb
    hKbc hNW hYQ hYk hWv hWsm hpbs hqbs hpbp hqbp hpbb hqbb hinv hcomp hGX hGY heff hexc hpos)

/-- The `ℚ`-factorial klt nef log terminal model of `(S, Θ)` over `T`. -/
private theorem exists_logTerminalModel :
    (∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
        (sY : Y ⟶ Spec (.of ℂ)) (_ : QuasiCompact sY) (πY : Y ⟶ T) (KY : Divisor Y)
        (φ : S.RationalMap Y),
      πY ≫ sT = sY ∧ IsProjectiveMorphism πY ∧ IsQFactorial sY ∧
        KY.IsCanonicalDivisor sY 3 ∧
        IsRealKltPair sY (RationalMap.transformDivisor φ Θ) ∧
        RationalMap.IsBirational φ ∧ MMP.Flips.RationalMap.IsOver f πY φ ∧
        (∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F) ∧
        MMP.Flips.IsRelativelyNef ℂ sY πY
          (MMP.Flips.logCanonicalDivisor KY (RationalMap.transformDivisor φ Θ)) ∧
        ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
          (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ S) (q : W ⟶ Y) (h : S.RationalMap W)
          (GS GY : RDivisor W),
          IsLogComparisonResolution sS sY sW φ K Θ KY (RationalMap.transformDivisor φ Θ)
            p q h GS GY ∧
          ∀ P : MMP.Mori.PrimeDivisor S, RationalMap.IsExceptional φ P →
            ∀ P' : MMP.Mori.PrimeDivisor W, RationalMap.transformPrimeDivisor h P = some P' →
              0 < (GS - GY).coeff P') :=
  (logTerminalModel_and_fixedParts hSQ hdim hT hTa hf hfp hfb hΘ hklt hK).1

/-- Persistence of the divisorial stable base primes of `K + Θ` over `T` near `Θ`. -/
private theorem exists_persistence :
    (∃ ε : ℝ, 0 < ε ∧ ∀ Θ' : RDivisor S, Θ'.support ⊆ Θ.support →
      (∀ P, 0 ≤ Θ'.coeff P) → IsRealKltPair sS Θ' →
      (∀ P, |Θ'.coeff P - Θ.coeff P| < ε) →
      ∀ G : MMP.Mori.PrimeDivisor S, IsInRelativeDivisorialStableBase f
        ((Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K) + Θ) G →
        IsInRelativeDivisorialStableBase f
          ((Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K) + Θ') G) := by
  classical
  obtain ⟨Tb, sTb, j, hj, Sb, h1, h2, h3, h4, fb, i, hi, hid, Kb, hTn, hTp, hjs, hfbp, hpb, hSp,
    hSQb, hΘk, hfbb, hdimb, hKb, hKbc, hpsef, hbig, -⟩ :=
    exists_compactificationData hSQ hdim hT hTa hf hfp hfb hΘ hklt hK
  have hinj := OpenWeilRestriction.primeDivisorMap_injective i
  have hmap : ∀ (Ξ : RDivisor S) (P : MMP.Mori.PrimeDivisor S),
      Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Ξ
        (OpenWeilRestriction.primeDivisorMap i P) = Ξ P := fun Ξ P =>
    Finsupp.mapDomain_apply_of_injective hinj Ξ P
  have hmap0 : ∀ (Ξ : RDivisor S) (Q : MMP.Mori.PrimeDivisor Sb),
      Q ∉ Set.range (OpenWeilRestriction.primeDivisorMap i) →
      Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Ξ Q = 0 := fun Ξ Q hQ =>
    Finsupp.mapDomain_notin_range Ξ Q hQ
  have hKΘ : ∀ (Ξ : RDivisor S) (P : MMP.Mori.PrimeDivisor S),
      (MMP.Flips.logCanonicalDivisor Kb
        (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Ξ)).coeff
          (OpenWeilRestriction.primeDivisorMap i P) =
        DivisorWithCoeffs.coeff ((Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K) + Ξ) P := by
    intro Ξ P
    rw [MMP.Flips.logCanonicalDivisor, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add,
      Divisor.coeff_toRDivisor, hKbc]
    rw [show DivisorWithCoeffs.coeff (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Ξ)
      (OpenWeilRestriction.primeDivisorMap i P) = Ξ P from hmap Ξ P]
    rfl
  have hΔ : IsRealKltPair (fb ≫ sTb)
      (QDivisor.toRDivisor 0 + Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Θ) := by
    rw [map_zero, zero_add]; exact hΘk
  obtain ⟨-, ⟨ε₁, hε₁, hpers⟩, -, -⟩ :=
    IsRealKltPair.exists_isNefWeakModel_and_fixedParts_of_isRelativelyBig hSp hTp rfl hSQb hdimb
      ⟨3, hKb⟩ le_rfl hbig (mapDomain_nonneg _ hΘ) hΔ (hpsef _)
  simp only [map_zero, zero_add] at hpers
  -- openness of the klt condition on the support of `Θ̄`
  let p : Θ.support → MMP.Mori.PrimeDivisor Sb := fun P => OpenWeilRestriction.primeDivisorMap i P
  let x : Θ.support → ℝ := fun P => Θ P
  have hsum : ∀ Ξ : RDivisor S, Ξ.support ⊆ Θ.support →
      Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Ξ =
        ∑ P, Finsupp.single (p P) (Ξ P) := by
    intro Ξ hs
    rw [Finsupp.mapDomain, Finsupp.sum_of_support_subset Ξ hs _
      (fun _ _ => Finsupp.single_zero _)]
    exact (Finset.sum_coe_sort Θ.support
      (fun P => Finsupp.single (OpenWeilRestriction.primeDivisorMap i P) (Ξ P))).symm
  haveI := hSp
  haveI : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ (fb ≫ sTb) :=
    AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ _
  have hev := (eventually_isRealKltPair_and_isRealTerminalPair (fb ≫ sTb) inferInstance hSQb p
    x).1 (by rw [← hsum Θ subset_rfl]; exact hΘk)
  obtain ⟨U, hUo, hxU, hU⟩ := mem_nhdsWithin.mp hev
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hUo x hxU
  refine ⟨min ε₁ δ, lt_min hε₁ hδ, fun Θ' hs h0 hk hclose G hG => ?_⟩
  have hΘ'k : IsRealKltPair (fb ≫ sTb)
      (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Θ') := by
    rw [hsum Θ' hs]
    refine hU ⟨hball ((dist_pi_lt_iff hδ).mpr fun P => ?_), fun P => h0 P⟩
    rw [Real.dist_eq]
    exact (hclose P).trans_le (min_le_right _ _)
  have hsupp : (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Θ').support ⊆
      (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Θ).support := by
    rw [Finsupp.mapDomain_support_of_injective hinj, Finsupp.mapDomain_support_of_injective hinj]
    exact Finset.image_subset_image hs
  have hcl : ∀ Q, |DivisorWithCoeffs.coeff
      (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Θ') Q -
      DivisorWithCoeffs.coeff (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Θ) Q| <
        ε₁ := fun Q => by
    rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply]
    by_cases hQ : Q ∈ Set.range (OpenWeilRestriction.primeDivisorMap i)
    · obtain ⟨P, rfl⟩ := hQ
      rw [hmap, hmap]
      exact (hclose P).trans_le (min_le_left _ _)
    · rw [hmap0 Θ' Q hQ, hmap0 Θ Q hQ, sub_zero, abs_zero]
      exact hε₁
  have hG₁ := (isInRelativeDivisorialStableBase_primeDivisorMap_iff hpb (hKΘ Θ) G).mp hG
  have hG₂ := hpers _ hsupp (mapDomain_nonneg _ h0) hΘ'k hcl _ hG₁
  exact (isInRelativeDivisorialStableBase_primeDivisorMap_iff hpb (hKΘ Θ') G).mpr hG₂

/-- Nonemptiness and fixed parts of `|k(K + Φ)|` along the smallest rational affine hull. -/
private theorem exists_fixedParts :
    (∃ ε : ℝ, 0 < ε ∧ ∃ r : ℕ, 0 < r ∧ ∀ Φ : RDivisor S, IsInSmallestRationalAffineHull Θ Φ →
      (∀ P, 0 ≤ Φ.coeff P) → IsRealKltPair sS Φ →
      (∀ P, |Φ.coeff P - Θ.coeff P| < ε) →
      ∀ k : ℕ, 0 < k → ∀ D : Divisor S, D.IsCartier →
        (∀ P, (k : ℝ) / r *
        (MMP.Mori.DivisorWithCoeffs.coeff (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K) P +
            Φ.coeff P) = D.coeff P) →
        (∃ φ ∈ ((r : ℤ) • D).divisorialSubmodule ⊤, φ ≠ 0) ∧
          ∀ G : MMP.Mori.PrimeDivisor S, 0 < relativeFixedMultiplicity f ((r : ℤ) • D) G →
            IsInRelativeDivisorialStableBase f
              ((Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K) + Θ) G) := by
  have : IsIntegral T := hT.1.toIsIntegral
  have : IsProper f := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hfp).2
  obtain ⟨ε, hε, r, hr, hfix⟩ : ∃ ε : ℝ, 0 < ε ∧ ∃ r : ℕ, 0 < r ∧ ∀ Φ : RDivisor S,
      IsInSmallestRationalAffineHull Θ Φ → (∀ P, 0 ≤ Φ.coeff P) → IsRealKltPair sS Φ →
      (∀ P, |Φ.coeff P - Θ.coeff P| < ε) →
      ∀ k : ℕ, 0 < k → ∀ D : Divisor S, D.IsCartier →
        (∀ P, (k : ℝ) / r *
        (MMP.Mori.DivisorWithCoeffs.coeff (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K) P +
            Φ.coeff P) = D.coeff P) →
          ∀ G : MMP.Mori.PrimeDivisor S, 0 < relativeFixedMultiplicity f ((r : ℤ) • D) G →
            IsInRelativeDivisorialStableBase f
              ((Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K) + Θ) G :=
    (logTerminalModel_and_fixedParts hSQ hdim hT hTa hf hfp hfb hΘ hklt hK).2
  exact ⟨ε, hε, r, hr, fun Φ h₁ h₂ h₃ h₄ k hk D hD hDk =>
    ⟨exists_ne_zero_mem_divisorialSubmodule_top hfb _, hfix Φ h₁ h₂ h₃ h₄ k hk D hD hDk⟩⟩

/-- Finite generation of the canonical ring of `(S, Θ)` over `Γ(T, 𝒪_T)` for rational `Θ`. -/
private theorem finiteGeneration :
    (∀ Θq : QDivisor S, QDivisor.toRDivisor Θq = Θ →
      ∃ G : Finset (Polynomial ((rationalFunctionsPresheaf S).obj (op ⊤))),
        (K.canonicalRing sS hK Θq : Set (Polynomial ((rationalFunctionsPresheaf S).obj (op ⊤)))) =
          Subring.closure (Set.range (relativeConstantsMap f) ∪ ↑G)) := by
  classical
  intro Θq hΘq
  obtain ⟨Tb, sTb, j, hj, Sb, h1, h2, h3, h4, fb, i, hi, hid, Kb, hTn, hTp, hjs, hfbp, hpb, hSp,
    hSQb, hΘk, hfbb, hdimb, hKb, hKbc, hpsef, hbig, -⟩ :=
    exists_compactificationData hSQ hdim hT hTa hf hfp hfb hΘ hklt hK
  haveI := hTa
  have hinj := OpenWeilRestriction.primeDivisorMap_injective i
  set Θb := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Θ with hΘb
  set Θbq : QDivisor Sb := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Θq
    with hΘbq_def
  have hΘbq : QDivisor.toRDivisor Θbq = QDivisor.toRDivisor 0 + Θb := by
    rw [map_zero, zero_add]
    refine Finsupp.ext fun Q => ?_
    change ((Θbq Q : ℚ) : ℝ) = Θb Q
    by_cases hQ : Q ∈ Set.range (OpenWeilRestriction.primeDivisorMap i)
    · obtain ⟨P, rfl⟩ := hQ
      rw [hΘbq_def, hΘb, Finsupp.mapDomain_apply_of_injective hinj, Finsupp.mapDomain_apply_of_injective hinj, ← hΘq]
      rfl
    · rw [hΘbq_def, hΘb, Finsupp.mapDomain_notin_range _ _ hQ,
        Finsupp.mapDomain_notin_range _ _ hQ, Rat.cast_zero]
  have hΔ : IsRealKltPair (fb ≫ sTb) (QDivisor.toRDivisor 0 + Θb) := by
    rw [map_zero, zero_add]; exact hΘk
  obtain ⟨-, -, -, hfg⟩ :=
    IsRealKltPair.exists_isNefWeakModel_and_fixedParts_of_isRelativelyBig hSp hTp rfl hSQb hdimb
      ⟨3, hKb⟩ le_rfl hbig (mapDomain_nonneg _ hΘ) hΔ (hpsef _)
  have hUa : IsAffineOpen (j ''ᵁ ⊤) := (isAffineOpen_top T).image_of_isOpenImmersion j
  obtain ⟨Gen, hGen⟩ := hfg Θbq hΘbq (j ''ᵁ ⊤) hUa
  have himg : fb ⁻¹ᵁ j ''ᵁ ⊤ = i ''ᵁ ⊤ :=
    (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback hpb.flip ⊤).symm
  haveI : Nonempty S := ⟨genericPoint S⟩
  haveI : Nonempty (fb ⁻¹ᵁ j ''ᵁ ⊤) :=
    ⟨⟨i (genericPoint S), by rw [himg]; exact ⟨_, trivial, rfl⟩⟩⟩
  haveI : Nonempty (⊤ : S.Opens) := ⟨⟨genericPoint S, trivial⟩⟩
  let Zb := componentIndex (fb ⁻¹ᵁ j ''ᵁ ⊤)
  let Z := componentIndex (⊤ : S.Opens)
  let e := (RingEquiv.ofBijective _ (sectionValue_bijective Zb)).trans
    ((RingEquiv.ofBijective _ (functionFieldMap_bijective_of_isOpenImmersion' i)).trans
      (RingEquiv.ofBijective _ (sectionValue_bijective Z)).symm)
  have he : ∀ x, sectionValue Z (e x) = functionFieldMap i (sectionValue Zb x) := fun x =>
    (RingEquiv.ofBijective _ (sectionValue_bijective Z)).apply_symm_apply _
  let E := Polynomial.mapEquiv e
  have hE : ∀ q m, (E q).coeff m = e (q.coeff m) := fun q m => Polynomial.coeff_map _ _
  have hDcoeff : ∀ (m : ℕ) (P : MMP.Mori.PrimeDivisor S),
      (m • Kb + DivisorWithCoeffs.roundDown ((m : ℚ) • Θbq)).coeff
          (OpenWeilRestriction.primeDivisorMap i P) =
        (m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Θq)).coeff P := by
    intro m P
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_roundDown,
      DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_smul, hKbc, DivisorWithCoeffs.coeff_apply,
      DivisorWithCoeffs.coeff_apply, hΘbq_def, Finsupp.mapDomain_apply_of_injective hinj]
    rfl
  have hmem : ∀ q : Polynomial ((rationalFunctionsPresheaf Sb).obj (op (fb ⁻¹ᵁ j ''ᵁ ⊤))),
      (∀ m : ℕ, q.coeff m ∈ (m • Kb + DivisorWithCoeffs.roundDown ((m : ℚ) • Θbq)).divisorialSubmodule
        (fb ⁻¹ᵁ j ''ᵁ ⊤)) ↔ E q ∈ K.canonicalRing sS hK Θq := by
    intro q
    show _ ↔ ∀ m : ℕ, (E q).coeff m ∈ K.canonicalRingPiece sS hK Θq m
    refine forall_congr' fun m => ?_
    rw [hE]
    exact mem_divisorialSubmodule_iff_of_isOpenImmersion i ⊤ _ himg Zb Z
      (fun P _ => hDcoeff m P) _ _ (he _)
  -- the constants
  have hU1 : j ⁻¹ᵁ j ''ᵁ ⊤ = ⊤ := Scheme.Hom.preimage_image_eq j ⊤
  have hmemU : ∀ x : S, i x ∈ fb ⁻¹ᵁ j ''ᵁ ⊤ := fun x => by rw [himg]; exact ⟨x, trivial, rfl⟩
  haveI : Nonempty (i ⁻¹ᵁ fb ⁻¹ᵁ j ''ᵁ ⊤) := ⟨⟨genericPoint S, hmemU _⟩⟩
  haveI : Nonempty ((i ≫ fb) ⁻¹ᵁ j ''ᵁ ⊤) := ⟨⟨genericPoint S, hmemU _⟩⟩
  haveI : Nonempty ((f ≫ j) ⁻¹ᵁ j ''ᵁ ⊤) := ⟨⟨genericPoint S, ⟨f (genericPoint S), trivial, rfl⟩⟩⟩
  haveI : Nonempty (f ⁻¹ᵁ j ⁻¹ᵁ j ''ᵁ ⊤) := ⟨⟨genericPoint S, ⟨f (genericPoint S), trivial, rfl⟩⟩⟩
  haveI : Nonempty (f ⁻¹ᵁ (⊤ : T.Opens)) := ⟨⟨genericPoint S, trivial⟩⟩
  have hval : ∀ a : Γ(Tb, j ''ᵁ ⊤), sectionValue Z
      (e (((toRationalFunctionsPresheaf Sb).app (op (fb ⁻¹ᵁ j ''ᵁ ⊤))).hom
        ((fb.app (j ''ᵁ ⊤)).hom a))) =
      S.germToFunctionField (f ⁻¹ᵁ j ⁻¹ᵁ j ''ᵁ ⊤)
        ((f.app (j ⁻¹ᵁ j ''ᵁ ⊤)).hom ((j.app (j ''ᵁ ⊤)).hom a)) := by
    intro a
    rw [he, sectionValue_toRationalFunctionsPresheaf, functionFieldMap_germToFunctionField]
    exact germToFunctionField_app_congr (g₁ := i ≫ fb) (g₂ := f ≫ j) hpb.w (j ''ᵁ ⊤) a
  have hpt : ∀ (a : Γ(Tb, j ''ᵁ ⊤)), ∃ b : Γ(T, ⊤),
      e (((toRationalFunctionsPresheaf Sb).app (op (fb ⁻¹ᵁ j ''ᵁ ⊤))).hom
        ((fb.app (j ''ᵁ ⊤)).hom a)) =
        ((toRationalFunctionsPresheaf S).app (op ⊤)).hom (f.appTop.hom b) := by
    intro a
    obtain ⟨b, hb⟩ := exists_germToFunctionField_app_top_eq f hU1 ((j.app (j ''ᵁ ⊤)).hom a)
    refine ⟨b, (sectionValue_bijective Z).1 ?_⟩
    rw [hval, hb, sectionValue_toRationalFunctionsPresheaf]
    rfl
  have hsurj : Function.Surjective (j.app (j ''ᵁ ⊤)).hom :=
    (ConcreteCategory.bijective_of_isIso (j.app (j ''ᵁ ⊤))).2
  have hpt' : ∀ b : Γ(T, ⊤), ∃ (a : Γ(Tb, j ''ᵁ ⊤)),
      e (((toRationalFunctionsPresheaf Sb).app (op (fb ⁻¹ᵁ j ''ᵁ ⊤))).hom
        ((fb.app (j ''ᵁ ⊤)).hom a)) =
        ((toRationalFunctionsPresheaf S).app (op ⊤)).hom (f.appTop.hom b) := by
    intro b
    obtain ⟨c, hc⟩ := exists_germToFunctionField_app_eq_top f hU1 b
    obtain ⟨a, rfl⟩ := hsurj c
    refine ⟨a, (sectionValue_bijective Z).1 ?_⟩
    rw [hval, hc, sectionValue_toRationalFunctionsPresheaf]
    rfl
  have hEC : ∀ x, E (Polynomial.C x) = Polynomial.C (e x) := fun x => Polynomial.map_C _
  have hrange : E.toRingHom '' Set.range (Polynomial.C.comp
      (((toRationalFunctionsPresheaf Sb).app (op (fb ⁻¹ᵁ j ''ᵁ ⊤))).hom.comp
        (fb.app (j ''ᵁ ⊤)).hom)) = Set.range (relativeConstantsMap f) := by
    rw [← Set.range_comp]
    ext p
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := hpt a
      refine ⟨b, ?_⟩
      change Polynomial.C (((toRationalFunctionsPresheaf S).app (op ⊤)).hom (f.appTop.hom b)) =
        E (Polynomial.C (((toRationalFunctionsPresheaf Sb).app (op (fb ⁻¹ᵁ j ''ᵁ ⊤))).hom
          ((fb.app (j ''ᵁ ⊤)).hom a)))
      rw [hEC]
      exact congrArg Polynomial.C hb.symm
    · rintro ⟨b, rfl⟩
      obtain ⟨a, ha⟩ := hpt' b
      refine ⟨a, ?_⟩
      change E (Polynomial.C (((toRationalFunctionsPresheaf Sb).app (op (fb ⁻¹ᵁ j ''ᵁ ⊤))).hom
          ((fb.app (j ''ᵁ ⊤)).hom a))) =
        Polynomial.C (((toRationalFunctionsPresheaf S).app (op ⊤)).hom (f.appTop.hom b))
      rw [hEC]
      exact congrArg Polynomial.C ha
  refine ⟨Gen.image E.toRingHom, ?_⟩
  have hL : (K.canonicalRing sS hK Θq : Set _) = E '' {p | ∀ m : ℕ, p.coeff m ∈
      (m • Kb + DivisorWithCoeffs.roundDown ((m : ℚ) • Θbq)).divisorialSubmodule
        (fb ⁻¹ᵁ j ''ᵁ ⊤)} := by
    ext p
    constructor
    · intro hp
      refine ⟨E.symm p, (hmem _).mpr ?_, E.apply_symm_apply p⟩
      rw [RingEquiv.apply_symm_apply]
      exact hp
    · rintro ⟨q, hq, rfl⟩
      exact (hmem q).mp hq
  rw [hL, hGen]
  have hmap := RingHom.map_closure E.toRingHom (Set.range (Polynomial.C.comp
      (((toRationalFunctionsPresheaf Sb).app (op (fb ⁻¹ᵁ j ''ᵁ ⊤))).hom.comp
        (fb.app (j ''ᵁ ⊤)).hom)) ∪ ↑Gen)
  rw [Set.image_union, hrange] at hmap
  rw [Finset.coe_image, ← hmap, Subring.coe_map]
  rfl

end Clauses

private theorem solution
    {S T : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sS] {sT : T ⟶ Spec (.of ℂ)} {f : S ⟶ T}
    (hSQ : IsQFactorial sS) (hdim : topologicalKrullDim S = 3)
    (hT : IsNormalVariety ℂ sT) (hTa : IsAffine T) (hf : f ≫ sT = sS)
    (hfp : IsProjectiveMorphism f) (hfb : IsBirationalMorphism f)
    {Θ : RDivisor S} (hΘ : ∀ P, 0 ≤ Θ.coeff P) (hklt : IsRealKltPair sS Θ)
    {K : Divisor S} (hK : K.IsCanonicalDivisor sS 3) :
    let KR : RDivisor S := Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K
    -- a `ℚ`-factorial klt nef log terminal model over `T`
    (∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
        (sY : Y ⟶ Spec (.of ℂ)) (_ : QuasiCompact sY) (πY : Y ⟶ T) (KY : Divisor Y)
        (φ : S.RationalMap Y),
      πY ≫ sT = sY ∧ IsProjectiveMorphism πY ∧ IsQFactorial sY ∧
        KY.IsCanonicalDivisor sY 3 ∧
        IsRealKltPair sY (RationalMap.transformDivisor φ Θ) ∧
        RationalMap.IsBirational φ ∧ MMP.Flips.RationalMap.IsOver f πY φ ∧
        (∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F) ∧
        MMP.Flips.IsRelativelyNef ℂ sY πY
          (MMP.Flips.logCanonicalDivisor KY (RationalMap.transformDivisor φ Θ)) ∧
        ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
          (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ S) (q : W ⟶ Y) (h : S.RationalMap W)
          (GS GY : RDivisor W),
          IsLogComparisonResolution sS sY sW φ K Θ KY (RationalMap.transformDivisor φ Θ)
            p q h GS GY ∧
          ∀ P : MMP.Mori.PrimeDivisor S, RationalMap.IsExceptional φ P →
            ∀ P' : MMP.Mori.PrimeDivisor W, RationalMap.transformPrimeDivisor h P = some P' →
              0 < (GS - GY).coeff P') ∧
    -- persistence of the divisorial stable base primes near `Θ`
    (∃ ε : ℝ, 0 < ε ∧ ∀ Θ' : RDivisor S, Θ'.support ⊆ Θ.support →
      (∀ P, 0 ≤ Θ'.coeff P) → IsRealKltPair sS Θ' →
      (∀ P, |Θ'.coeff P - Θ.coeff P| < ε) →
      ∀ G : MMP.Mori.PrimeDivisor S, IsInRelativeDivisorialStableBase f (KR + Θ) G →
        IsInRelativeDivisorialStableBase f (KR + Θ') G) ∧
    -- the fixed parts along the smallest rational affine hull
    (∃ ε : ℝ, 0 < ε ∧ ∃ r : ℕ, 0 < r ∧ ∀ Φ : RDivisor S, IsInSmallestRationalAffineHull Θ Φ →
      (∀ P, 0 ≤ Φ.coeff P) → IsRealKltPair sS Φ →
      (∀ P, |Φ.coeff P - Θ.coeff P| < ε) →
      ∀ k : ℕ, 0 < k → ∀ D : Divisor S, D.IsCartier →
        (∀ P, (k : ℝ) / r * (KR.coeff P + Φ.coeff P) = D.coeff P) →
        (∃ φ ∈ ((r : ℤ) • D).divisorialSubmodule ⊤, φ ≠ 0) ∧
          ∀ G : MMP.Mori.PrimeDivisor S, 0 < relativeFixedMultiplicity f ((r : ℤ) • D) G →
            IsInRelativeDivisorialStableBase f (KR + Θ) G) ∧
    -- finite generation of the floor-section algebra for rational `Θ`
    (∀ Θq : QDivisor S, QDivisor.toRDivisor Θq = Θ →
      ∃ G : Finset (Polynomial ((rationalFunctionsPresheaf S).obj (op ⊤))),
        (K.canonicalRing sS hK Θq : Set (Polynomial ((rationalFunctionsPresheaf S).obj (op ⊤)))) =
          Subring.closure (Set.range (relativeConstantsMap f) ∪ ↑G)) := by
  intro KR
  exact ⟨exists_logTerminalModel hSQ hdim hT hTa hf hfp hfb hΘ hklt hK,
    exists_persistence hSQ hdim hT hTa hf hfp hfb hΘ hklt hK,
    exists_fixedParts hSQ hdim hT hTa hf hfp hfb hΘ hklt hK,
    finiteGeneration hSQ hdim hT hTa hf hfp hfb hΘ hklt hK⟩

end Proof_thm_fourfold_birational_affine_threefold_f3

end

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.Fourfold

open MMP.Mori

/-- **Threefold log terminal models and fixed parts over an affine birational base.** Let
`f : S ⟶ T` be a projective birational morphism of normal complex varieties, `T` affine, `S` a
`ℚ`-factorial threefold with canonical divisor `K`, and `Θ` an effective real klt boundary on
`S`. Then `(S, Θ)` has a `ℚ`-factorial klt log terminal model `φ : S ⤏ Y` projective over `T`,
with effective exceptional comparison on a common resolution, positive along the primes
contracted by `φ`; the divisorial stable base primes of `K + Θ` over `T` persist near `Θ`; along
the smallest rational affine hull of `Θ` there are `ε > 0` and `r > 0` such that `|k(K + Φ)|` is
nonempty with fixed part made of stable base primes of `K + Θ` whenever `Φ` is effective klt and
`ε`-close to `Θ` and `k(K + Φ)/r` is integral Cartier; and if `Θ` is rational, its canonical
ring is a finitely generated `Γ(T, 𝒪_T)`-algebra. -/
@[mmp "thm_fourfold_birational_affine_threefold_f3"]
public theorem IsRealKltPair.exists_logTerminalModel_of_isBirationalMorphism_of_isAffine
    {S T : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sS] {sT : T ⟶ Spec (.of ℂ)} {f : S ⟶ T}
    (hSQ : IsQFactorial sS) (hdim : topologicalKrullDim S = 3)
    (hT : IsNormalVariety ℂ sT) (hTa : IsAffine T) (hf : f ≫ sT = sS)
    (hfp : IsProjectiveMorphism f) (hfb : IsBirationalMorphism f)
    {Θ : RDivisor S} (hΘ : ∀ P, 0 ≤ Θ.coeff P) (hklt : IsRealKltPair sS Θ)
    {K : Divisor S} (hK : K.IsCanonicalDivisor sS 3) :
    let KR : RDivisor S := Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K
    -- a `ℚ`-factorial klt nef log terminal model over `T`
    (∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
        (sY : Y ⟶ Spec (.of ℂ)) (_ : QuasiCompact sY) (πY : Y ⟶ T) (KY : Divisor Y)
        (φ : S.RationalMap Y),
      πY ≫ sT = sY ∧ IsProjectiveMorphism πY ∧ IsQFactorial sY ∧
        KY.IsCanonicalDivisor sY 3 ∧
        IsRealKltPair sY (RationalMap.transformDivisor φ Θ) ∧
        RationalMap.IsBirational φ ∧ MMP.Flips.RationalMap.IsOver f πY φ ∧
        (∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F) ∧
        MMP.Flips.IsRelativelyNef ℂ sY πY
          (MMP.Flips.logCanonicalDivisor KY (RationalMap.transformDivisor φ Θ)) ∧
        ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
          (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ S) (q : W ⟶ Y) (h : S.RationalMap W)
          (GS GY : RDivisor W),
          IsLogComparisonResolution sS sY sW φ K Θ KY (RationalMap.transformDivisor φ Θ)
            p q h GS GY ∧
          ∀ P : MMP.Mori.PrimeDivisor S, RationalMap.IsExceptional φ P →
            ∀ P' : MMP.Mori.PrimeDivisor W, RationalMap.transformPrimeDivisor h P = some P' →
              0 < (GS - GY).coeff P') ∧
    -- persistence of the divisorial stable base primes near `Θ`
    (∃ ε : ℝ, 0 < ε ∧ ∀ Θ' : RDivisor S, Θ'.support ⊆ Θ.support →
      (∀ P, 0 ≤ Θ'.coeff P) → IsRealKltPair sS Θ' →
      (∀ P, |Θ'.coeff P - Θ.coeff P| < ε) →
      ∀ G : MMP.Mori.PrimeDivisor S, IsInRelativeDivisorialStableBase f (KR + Θ) G →
        IsInRelativeDivisorialStableBase f (KR + Θ') G) ∧
    -- the fixed parts along the smallest rational affine hull
    (∃ ε : ℝ, 0 < ε ∧ ∃ r : ℕ, 0 < r ∧ ∀ Φ : RDivisor S, IsInSmallestRationalAffineHull Θ Φ →
      (∀ P, 0 ≤ Φ.coeff P) → IsRealKltPair sS Φ →
      (∀ P, |Φ.coeff P - Θ.coeff P| < ε) →
      ∀ k : ℕ, 0 < k → ∀ D : Divisor S, D.IsCartier →
        (∀ P, (k : ℝ) / r * (KR.coeff P + Φ.coeff P) = D.coeff P) →
        (∃ φ ∈ ((r : ℤ) • D).divisorialSubmodule ⊤, φ ≠ 0) ∧
          ∀ G : MMP.Mori.PrimeDivisor S, 0 < relativeFixedMultiplicity f ((r : ℤ) • D) G →
            IsInRelativeDivisorialStableBase f (KR + Θ) G) ∧
    -- finite generation of the floor-section algebra for rational `Θ`
    (∀ Θq : QDivisor S, QDivisor.toRDivisor Θq = Θ →
      ∃ G : Finset (Polynomial ((rationalFunctionsPresheaf S).obj (op ⊤))),
        (K.canonicalRing sS hK Θq : Set (Polynomial ((rationalFunctionsPresheaf S).obj (op ⊤)))) =
          Subring.closure (Set.range (relativeConstantsMap f) ∪ ↑G)) :=
            by revert S T sS sT f hSQ hdim hT hTa hf hfp hfb Θ hΘ hklt K hK; first | exact Proof_thm_fourfold_birational_affine_threefold_f3.solution | exact Proof_thm_fourfold_birational_affine_threefold_f3.solution _ | exact Proof_thm_fourfold_birational_affine_threefold_f3.solution _ _ | exact Proof_thm_fourfold_birational_affine_threefold_f3.solution _ _ _ | exact Proof_thm_fourfold_birational_affine_threefold_f3.solution _ _ _ _

end MMP.Fourfold
