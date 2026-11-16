module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.MMP.Fourfold.AffineBaseRegularGeneration
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent
import MMP.AlgebraicGeometry.Vanishing.SncDirectImageCohomology
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Resolution.StrongResolution.QuasiProjective
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Principalization.ResolutionPrincipalization
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Curves.NormalizationLiftInvertible
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafCoherent
import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics

/-!
# Vanishing and extension for a union of lc centres

Let `(X, B)` be an lc pair with effective `ℚ`-boundary on a normal projective variety over `ℂ`, put
`D = K_X + B`, and let `W ⊆ X` be a union of lc centres of `(X, B)`, with its reduced subscheme
structure `ι : W ⟶ X` and ideal sheaf `ℐ_W`. If `M` is a Cartier divisor with `M - D` ample, then
for every `i > 0` `H^i(X, ℐ_W(M)) = 0` and `H^i(W, 𝒪_W(M)) = 0`, and the restriction
`H^0(X, 𝒪_X(M)) → H^0(W, 𝒪_W(M))` is surjective. `W` may be a single (for instance minimal) lc
centre: the statement is not only about the whole non-klt locus.

## Main results

* `MMP.Mori.isZero_Hgroup_kernel_unit_and_surjective_of_isAmple_sub`: the statement.

## Implementation notes

An lc centre of `(X, B)` is the centre `center_X E` of a divisor `E` over `X` (exceptional, or a
prime divisor of `X`) with discrepancy `a(E, X, B) = -1`. The reduced structure on `W` is the
closed subscheme cut out by `Scheme.IdealSheafData.vanishingIdeal W`. Writing `L = 𝒪_X(M)` and
`η : L ⟶ ι_* ι^* L` for the unit of the adjunction `ι^* ⊣ ι_*`, the sheaf `𝒪_W(M)` is `ι^* L`,
the twisted ideal sheaf `ℐ_W(M) = ℐ_W ⊗ L` is the kernel of `η` (as `L` is invertible), and the
restriction map on global sections is `η` on the open `⊤`. Cohomology is sheaf cohomology of
`𝒪`-modules, `Hgroup _ ⊤ i`.

## References

* [O. Fujino, *Fundamental theorems for the log minimal model program*][Fujino11]
-/

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite MMP.Mori

namespace MMP.Mori.LcCentreUnionExtension

attribute [local instance] HasDerivedCategory.standard

/-- A regular function on an affine open `U` lies in the ideal of the reduced closed subscheme
`W` exactly when it vanishes at every point of `W ∩ U`. -/
private theorem mem_vanishingIdeal_ideal_iff {X : Scheme.{0}} (W : Closeds X) (U : X.affineOpens)
    (a : Γ(X, U)) :
    a ∈ (Scheme.IdealSheafData.vanishingIdeal W).ideal U ↔
      ∀ x ∈ (W : Set X), x ∈ (U : X.Opens) → x ∉ X.basicOpen a := by
  have hmem : ∀ p, U.2.fromSpec p ∈ X.basicOpen a ↔ a ∉ p.asIdeal := fun p => by
    change p ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen a ↔ _
    rw [U.2.fromSpec_preimage_basicOpen]
    rfl
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  refine ⟨fun h x hxW hxU hxa => ?_, fun h p hp => ?_⟩
  · obtain ⟨p, rfl⟩ : x ∈ Set.range U.2.fromSpec := by rwa [U.2.range_fromSpec]
    exact (hmem p).1 hxa (h p hxW)
  · by_contra hpa
    have hU : U.2.fromSpec p ∈ (U : X.Opens) := by
      have := Set.mem_range_self (f := U.2.fromSpec) p
      rwa [U.2.range_fromSpec] at this
    exact h _ hp hU ((hmem p).2 hpa)

/-- An element of the maximal ideal of the discrete valuation ring `𝒪_{X,E}` vanishes to order at
least one along `E`. -/
private theorem ordGE_one_toComponent_of_mem_maximalIdeal {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] (E : MMP.Mori.PrimeDivisor X) {a : E.localRing}
    (ha : a ∈ IsLocalRing.maximalIdeal E.localRing) : E.OrdGE 1 (E.toComponent.hom a) := by
  by_cases h0 : a = 0
  · left; rw [h0, map_zero]
  right
  let := E.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions E.genericPoint_mem_component
  have : Ring.KrullDimLE 1 E.localRing := krullDimLE_of_coheight_le E.coheight_genericPoint.le
  have := E.isDiscreteValuationRing_localRing
  change WithZero.exp 1 ≤ Ring.ordFrac E.localRing (IsLocalization.algEquiv
    (nonZeroDivisors E.localRing) _ (FractionRing E.localRing) (algebraMap E.localRing _ a))
  rw [AlgEquiv.commutes]
  set v := Ring.ordFrac E.localRing (algebraMap E.localRing (FractionRing E.localRing) a)
  have h1 : 1 ≤ v := Ring.ordFrac_ge_one_of_ne_zero h0
  have h2 : v ≠ 1 := fun h =>
    (IsLocalRing.mem_maximalIdeal _).mp ha
      (Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing.2 h)
  have hv0 : v ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one h1)
  rw [← WithZero.exp_log hv0] at h1 h2 ⊢
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  rw [← WithZero.exp_zero, Ne, WithZero.exp_inj] at h2
  rw [WithZero.exp_le_exp]
  omega

/-- The germ of a regular function along a prime divisor, read in the function field of its
component, is the image of its germ in the local ring of the divisor. -/
private theorem germ_component_eq_toComponent {V : Scheme.{0}} [IsLocallyNoetherian V] [IsNormal V]
    (P : MMP.Mori.PrimeDivisor V) {U' : V.Opens} (b : Γ(V, U')) (hP : P.genericPoint ∈ U')
    (hc : componentGenericPoint V P.component ∈ U') :
    V.presheaf.germ U' _ hc b = P.toComponent.hom (V.presheaf.germ U' _ hP b) :=
  (TopCat.Presheaf.germ_stalkSpecializes_apply V.presheaf hP _ b).symm

/-- A regular function vanishing at the generic point of a prime divisor `P` vanishes to order at
least one along `P`. -/
private theorem ordGE_one_germ_of_notMem_basicOpen {V : Scheme.{0}} [IsLocallyNoetherian V]
    [IsNormal V] (P : MMP.Mori.PrimeDivisor V) {U' : V.Opens} (b : Γ(V, U'))
    (hP : P.genericPoint ∈ U') (hb : P.genericPoint ∉ V.basicOpen b)
    (hc : componentGenericPoint V P.component ∈ U') :
    P.OrdGE 1 (V.presheaf.germ U' _ hc b) := by
  rw [germ_component_eq_toComponent P b hP hc]
  refine ordGE_one_toComponent_of_mem_maximalIdeal P ?_
  rw [IsLocalRing.mem_maximalIdeal]
  exact fun hu => hb ((Scheme.mem_basicOpen V b _ hP).2 hu)

/-- A regular function has nonnegative order along every prime divisor. -/
private theorem ordGE_zero_germ {V : Scheme.{0}} [IsLocallyNoetherian V] [IsNormal V]
    (P : MMP.Mori.PrimeDivisor V) {U' : V.Opens} (b : Γ(V, U')) (hP : P.genericPoint ∈ U')
    (hc : componentGenericPoint V P.component ∈ U') :
    P.OrdGE 0 (V.presheaf.germ U' _ hc b) := by
  rw [germ_component_eq_toComponent P b hP hc]
  by_cases h0 : V.presheaf.germ U' _ hP b = 0
  · left; rw [h0, map_zero]
  · right; rw [WithZero.exp_zero]; exact P.one_le_valuation_toComponent h0

/-- A regular function invertible at the generic point of a prime divisor has order zero along
it. -/
private theorem valuation_germ_eq_one_of_mem_basicOpen {V : Scheme.{0}} [IsLocallyNoetherian V]
    [IsNormal V] (P : MMP.Mori.PrimeDivisor V) {U' : V.Opens} (b : Γ(V, U'))
    (hP : P.genericPoint ∈ U') (hb : P.genericPoint ∈ V.basicOpen b)
    (hc : componentGenericPoint V P.component ∈ U') :
    P.valuation (V.presheaf.germ U' _ hc b) = 1 := by
  rw [germ_component_eq_toComponent P b hP hc]
  exact P.valuation_toComponent_of_isUnit ((Scheme.mem_basicOpen V b _ hP).1 hb)

/-- An identity in the function field of `V` between a component value and the pull-back of a
component value on `X` is the corresponding identity for the extension `fieldMap` of the local
rings at the generic points. -/
private theorem fieldMap_eq_of_stalkSpecializes {X V : Scheme.{0}} [IsIntegral X] [IsIntegral V]
    (g : V ⟶ X) [IsDominant g] (ZX : irreducibleComponents X) (ZY : irreducibleComponents V)
    (x : X.presheaf.stalk (componentGenericPoint X ZX))
    (y : V.presheaf.stalk (componentGenericPoint V ZY))
    (h : (V.presheaf.stalkSpecializes (genericPoint_specializes _)).hom y =
      functionFieldMap g ((X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom x)) :
    MMP.Fourfold.fieldMap g ZX ZY x = y := by
  rw [MMP.Fourfold.fieldMap_eq, RingHom.comp_apply, RingHom.comp_apply]
  change (V.presheaf.stalkSpecializes
      (specializes_of_eq (MMP.Fourfold.componentGenericPoint_eq_genericPoint ZY))).hom
    (functionFieldMap g ((X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom x)) = y
  rw [← h, ← ConcreteCategory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp,
    TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- A closed subset of a Noetherian space which is a union of irreducible closed subsets from a
family `S` is already the union of finitely many members of `S`: each of its finitely many
irreducible pieces has its generic point in some member of `S`. -/
private theorem exists_finset_subset_eq_biUnion {X : Scheme.{0}} [IsLocallyNoetherian X]
    [CompactSpace X] (W : Closeds X) (S : Set (IrreducibleCloseds X))
    (hW : (W : Set X) = ⋃ Z ∈ S, (Z : Set X)) :
    ∃ S' : Finset (IrreducibleCloseds X), (S' : Set (IrreducibleCloseds X)) ⊆ S ∧
      (W : Set X) = ⋃ Z ∈ S', (Z : Set X) := by
  classical
  haveI : IsNoetherian X := {}
  obtain ⟨T, hT, hTW⟩ := TopologicalSpace.NoetherianSpace.exists_finset_irreducible W
  have key : ∀ C ∈ T, ∃ Z ∈ S, (C : Set X) ⊆ Z := by
    intro C hC
    have hirr : IsIrreducible (C : Set X) := hT ⟨C, hC⟩
    have hCW : (C : Set X) ⊆ W := by
      rw [hTW]
      exact (Finset.le_sup (f := id) hC : C ≤ T.sup id)
    have hgen := hirr.isGenericPoint_genericPoint_closure
    rw [C.isClosed.closure_eq] at hgen
    have hξ : hirr.genericPoint ∈ (W : Set X) := hCW hgen.mem
    rw [hW] at hξ
    simp only [Set.mem_iUnion] at hξ
    obtain ⟨Z, hZS, hξZ⟩ := hξ
    refine ⟨Z, hZS, ?_⟩
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hξZ) Z.isClosed
  choose f hfS hfC using key
  refine ⟨T.attach.image fun C => f C.1 C.2, ?_, ?_⟩
  · intro Z hZ
    obtain ⟨C, -, rfl⟩ := Finset.mem_image.mp hZ
    exact hfS C.1 C.2
  · apply le_antisymm
    · intro x hx
      have hx' : x ∈ ((T.sup id : Closeds X) : Set X) := by rw [← hTW]; exact hx
      rw [Closeds.coe_finset_sup, Finset.sup_eq_iSup] at hx'
      simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Function.comp_apply, id] at hx'
      obtain ⟨C, hC, hxC⟩ := hx'
      simp only [Set.mem_iUnion, Finset.mem_image]
      exact ⟨f C hC, ⟨⟨C, hC⟩, Finset.mem_attach _ _, rfl⟩, hfC C hC hxC⟩
    · intro x hx
      simp only [Set.mem_iUnion, Finset.mem_image] at hx
      obtain ⟨Z, ⟨C, -, rfl⟩, hxZ⟩ := hx
      rw [hW]
      simp only [Set.mem_iUnion]
      exact ⟨f C.1 C.2, hfS C.1 C.2, hxZ⟩

/-- On a variety, the valuation of every divisor over `X` has a nonempty centre: it is realized
by a divisor on a projective birational model of `X`, which dominates the local ring at the
centre `f(η_E)`. -/
private theorem hasNonemptyCenter_valuation {X : Scheme.{0}} [IsIntegral X]
    (sX : X ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsVariety ℂ sX] (E : DivisorOver ℂ sX) :
    MMP.Flips.HasNonemptyCenter ℂ sX E.valuation := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  have hdiv : MMP.Flips.IsDivisorOfFunctionField ℂ sX E.valuation :=
    MMP.Fourfold.SNCWeight.Restriction.isDivisorOfFunctionField_comap_primeDivisor sX E.f
      E.isNormalVariety E.isBirationalMorphism.functionFieldMap_bijective E.E
  obtain ⟨D, -, hD, -⟩ := MMP.Flips.exists_properDivisorOver_isProjective_of_dominates sX hdiv
    (E.f E.E.genericPoint)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one E _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one E _ rfl)
  exact ⟨hdiv, D, hD⟩

/-- **A crepant log resolution adapted to `W`.** There is a projective birational morphism
`g : V ⟶ X` from a smooth projective variety with a canonical divisor `K_V` and a `ℚ`-divisor
`B_V` with snc support, coefficients `≤ 1` and negative coefficients only along `g`-exceptional
divisors, such that `K_V + B_V = g^*(K + B)` through every Cartier multiple of `K + B`; and a
finite set `T` of prime divisors of `V` of coefficient one in `B_V`, mapping into `W`, whose images
cover `W`. -/
private theorem exists_crepantModel
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of ℂ)) (hproj : IsProjectiveMorphism sX)
    {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hB : IsLcPair sX n K B) (hBeff : B.IsEffective) (hB1 : ∀ P, B.coeff P ≤ 1)
    (W : Closeds X) (S : Set (IrreducibleCloseds X))
    (hS : ∀ Z ∈ S, ∃ E : DivisorOver ℂ sX, E.center = Z ∧ IsDiscrepancy sX n K B E (-1))
    (hW : (W : Set X) = ⋃ Z ∈ S, (Z : Set X)) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (sV : V ⟶ Spec (.of ℂ)) (_ : MMP.Mori.IsProjectiveVariety ℂ sV) (g : V ⟶ X) (_ : IsDominant g)
      (nV : ℕ) (KV : Divisor V) (BV : QDivisor V) (T : Finset (MMP.Mori.PrimeDivisor V)),
      MMP.Mori.IsSmoothScheme sV ∧ g ≫ sX = sV ∧ IsProjective g ∧ IsProper g ∧
      IsBirationalMorphism g ∧ KV.IsCanonicalDivisor sV nV ∧ BV.IsSNC sV ∧ (∀ P, BV P ≤ 1) ∧
      (∀ P, BV P < 0 → RationalMap.IsExceptional g.toRationalMap P) ∧
      (∀ (m : ℕ), 0 < m → ∀ D : Divisor X,
        Divisor.toQDivisor D = (m : ℤ) • (Divisor.toQDivisor K + B) → D.IsCartier →
          ∃ DV : Divisor V, Divisor.toQDivisor DV = (m : ℤ) • (Divisor.toQDivisor KV + BV) ∧
            ∃ hD, D.IsPullback g hD DV) ∧
      (∀ P ∈ T, BV P = 1 ∧ g.base '' P.support ⊆ W) ∧
      (W : Set X) ⊆ ⋃ P ∈ T, g.base '' P.support := by
  classical
  have hX : IsNormalVariety ℂ sX := hB.1.1
  have hPw : IsPairWith sX n K B := hB.1
  have hP : IsPair sX B := hB.isPair
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hX.1
  haveI : MMP.Mori.IsProjectiveVariety ℂ sX :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ sX).2 ⟨hX.1, hproj⟩
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  -- finitely many centres, each with a divisor of discrepancy `-1`
  obtain ⟨S', hS'S, hWS'⟩ := exists_finset_subset_eq_biUnion W S hW
  choose E hEc hEd using fun Z : S' => hS Z.1 (hS'S Z.2)
  -- a smooth projective model `W₀` on which every `E Z` is a prime divisor
  obtain ⟨W₀, w, hW₀, hwb, -, hsm₀, hwp, -, hE', hpv⟩ :=
    MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq sX
      (ι := PUnit.{1}) (fun _ => 𝟙 X) (fun _ => isBirationalMorphism_of_isIso _)
      (fun _ => by simpa using hX)
      (κ := S') (fun Z => (E Z).valuation) (fun Z => hasNonemptyCenter_valuation sX (E Z))
  choose E' hE'v using hE'
  haveI : IsIntegral W₀ := hW₀.1.toIsIntegral
  haveI : LocallyOfFiniteType (w ≫ sX) := hW₀.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W₀ := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sX)
  haveI : IsNormal W₀ := hW₀.2
  haveI := hwb.isDominant
  -- the crepant boundary of `(X, B)` on `W₀`
  obtain ⟨⟨B₀, hB₀, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary hP hB.1.2.1 w hW₀ hwb
  -- a log resolution of `W₀` along `Supp B₀` and the divisors `E' Z`
  obtain ⟨Y, h, hres, -, hSY, -⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset (w ≫ sX) hW₀
      (B₀.support ∪ Finset.univ.image E')
  haveI : IsProper h := hres.isProjective.isProper
  haveI : IsProper w := hwp.isProjective.isProper
  haveI : IsIntegral Y := hres.isVariety_source.toIsIntegral
  set g : Y ⟶ X := h ≫ w with hg
  have hgb : IsBirationalMorphism g :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational w h
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hwb)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hres.isBirationalMorphism)
  haveI : IsProper g := inferInstance
  have hgres : IsSmoothResolution sX g := ⟨inferInstance, hgb, by
    have := hres.isSmoothScheme; rwa [hg, Category.assoc]⟩
  obtain ⟨hY, hdimY, -⟩ := hgres.isNormalVariety hX
  haveI : LocallyOfFiniteType (g ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  haveI : IsNormal Y := hY.2
  haveI : CompactSpace Y := (hY.1.toQuasiCompact).compactSpace_of_compactSpace
  haveI := hgb.isDominant
  have hgproj : IsProjective g := hres.isProjective.comp hwp.isProjective
  have hprojY : MMP.Mori.IsProjectiveVariety ℂ (g ≫ sX) :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ (g ≫ sX)).2 ⟨hY.1,
      isProjectiveMorphism_of_isProjective_of_isAffine (g ≫ sX)
        (hgproj.comp hproj.isProjective)⟩
  haveI : AlgebraicGeometry.IsVariety ℂ (g ≫ sX) := hY.1
  -- a canonical divisor `K_V` with `g_* K_V = K`, and the crepant boundary `B_V`
  have hn : topologicalKrullDim Y = n := hdimY.trans hB.1.2.1.topologicalKrullDim_eq
  obtain ⟨K₀, hK₀⟩ :=
    MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (g ≫ sX) hgres.isSmoothScheme hn
  obtain ⟨KV, hKV, hKVt⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hX hY hgb hB.1.2.1 hK₀
  obtain ⟨⟨BV, hBV, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary hP hB.1.2.1 g hY hgb
  have hpull := IsPair.isPullback_of_isCrepantBoundary hP g hY hgb hB.1.2.1 hKV
    (Or.inr ⟨inferInstance, hKVt⟩) hBV
  -- the strict transforms on `V` of the divisors `E' Z`
  have hT : ∀ j : S', ∃ T : MMP.Mori.PrimeDivisor Y,
      (⟨Y, g, hY, hgb, T⟩ : DivisorOver ℂ sX).valuation = (E j).valuation := fun j => by
    obtain ⟨T, hT⟩ := MMP.Fourfold.Oai4C1.CommonModel.exists_primeDivisor_valuation_eq
      (⟨W₀, w, hW₀, hwb, E' j⟩ : DivisorOver ℂ sX) g hY hgb h hres.isBirationalMorphism rfl
    exact ⟨T, hT.trans (hE'v j)⟩
  choose Tj hTj using hT
  -- the coefficients of `B_V`: at most one, and negative only along `g`-exceptional divisors
  have hcoef : ∀ P : MMP.Mori.PrimeDivisor Y, BV P ≤ 1 ∧
      (¬ (⟨Y, g, hY, hgb, P⟩ : DivisorOver ℂ sX).IsExceptional → 0 ≤ BV P) := by
    intro P
    by_cases hPe : (⟨Y, g, hY, hgb, P⟩ : DivisorOver ℂ sX).IsExceptional
    · refine ⟨?_, fun h => absurd hPe h⟩
      have h1 : (((BV.coeff P : ℚ) : ℝ) : EReal) ≤ ((1 : ℝ) : EReal) := by
        simpa using (discrep_le hPe (hBV P)).trans' hB.2
      rw [← DivisorWithCoeffs.coeff_apply]
      exact_mod_cast EReal.coe_le_coe_iff.mp h1
    · obtain ⟨Γ, -, hΓ⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hPw _ hPe
      have hco : BV.coeff P = B.coeff Γ := neg_injective ((hBV P).eq hΓ)
      rw [← DivisorWithCoeffs.coeff_apply, hco]
      exact ⟨hB1 Γ, fun _ => hBeff Γ⟩
  -- the strict transforms `T_j` lie over the centres `Z_j`
  have hTη : ∀ j : S', g (Tj j).genericPoint = (E j).f (E j).E.genericPoint := fun j =>
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 (hTj j)
  have hZ : ∀ j : S', ((j : IrreducibleCloseds X) : Set X) = closure {g (Tj j).genericPoint} :=
    fun j => by
      rw [hTη j, ← hEc j]
      exact DivisorOver.center_eq_closure_genericPoint (E j)
  refine ⟨Y, inferInstance, inferInstance, inferInstance, g ≫ sX, hprojY, g, inferInstance, n, KV,
    BV, Finset.univ.image Tj, hgres.isSmoothScheme, rfl, hgproj, inferInstance, hgb, hKV, ?_, ?_,
    ?_, fun m hm D hD hDC => (hpull.1 m hm D hD hDC).imp fun DY h => ⟨h.1, h.2.2⟩, ?_, ?_⟩
  · -- `Supp B_V` lies in the snc divisor `Ex(h) ∪ h⁻¹(Supp B₀ ∪ ⋃ E')`
    have hgs : g ≫ sX = h ≫ w ≫ sX := by rw [hg, Category.assoc]
    have hYW : IsNormalVariety ℂ (h ≫ w ≫ sX) := hgs ▸ hY
    haveI := hres.isBirationalMorphism.isDominant
    have hval : ∀ P : MMP.Mori.PrimeDivisor Y, (⟨Y, g, hY, hgb, P⟩ : DivisorOver ℂ sX).valuation =
        (⟨Y, h, hYW, hres.isBirationalMorphism, P⟩ : DivisorOver ℂ (w ≫ sX)).valuation.comap
          (functionFieldMap w) := by
      intro P; ext x
      change P.divisorialValuation (functionFieldMap g x) =
        P.divisorialValuation (functionFieldMap h (functionFieldMap w x))
      rw [MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply h w hg.symm]
    have hval₀ : ∀ P₀ : MMP.Mori.PrimeDivisor W₀,
        (⟨W₀, w, hW₀, hwb, P₀⟩ : DivisorOver ℂ sX).valuation =
          (DivisorOver.ofPrimeDivisor ℂ hW₀ P₀).valuation.comap (functionFieldMap w) := by
      intro P₀; ext x
      change P₀.divisorialValuation (functionFieldMap w x) =
        P₀.divisorialValuation (functionFieldMap (𝟙 W₀) (functionFieldMap w x))
      rw [MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply (𝟙 W₀) w (Category.id_comp w)]
    have hsupp : ∀ P ∈ BV.support, P.genericPoint ∈ ((exceptionalSet h : Set Y) ∪
        h ⁻¹' ((B₀.support ∪ Finset.univ.image E').sup
          fun E => (E.idealSheaf.support : Set W₀))) := by
      intro P hP
      by_cases hPe :
          (⟨Y, h, hYW, hres.isBirationalMorphism, P⟩ : DivisorOver ℂ (w ≫ sX)).IsExceptional
      · exact Or.inl (MMP.Positivity.support_subset_exceptionalSet P hPe
          (MMP.Flips.primeDivisor_genericPoint_mem_support P))
      · right
        obtain ⟨P₀, hP₀⟩ :=
          MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hW₀ _ hPe
        have hη : h P.genericPoint = P₀.genericPoint :=
          MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hW₀.1 hP₀
        have hco : BV.coeff P = B₀.coeff P₀ := neg_injective
          (MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPw
            (by rw [hval, hval₀, hP₀]) (hBV P) (hB₀ P₀))
        show h P.genericPoint ∈
          ((B₀.support ∪ Finset.univ.image E').sup fun E => (E.idealSheaf.support : Set W₀))
        rw [hη, Finset.sup_set_eq_biUnion]
        refine Set.mem_iUnion₂.2 ⟨P₀, Finset.mem_union_left _ ?_,
          MMP.Flips.primeDivisor_genericPoint_mem_support P₀⟩
        rw [Finsupp.mem_support_iff] at hP ⊢
        rwa [← DivisorWithCoeffs.coeff_apply, ← hco, DivisorWithCoeffs.coeff_apply]
    haveI : AlgebraicGeometry.IsNoetherian Y := {}
    rw [hgs]
    rcases MMP.Resolution.isSNCSubset_of_isSNCClosedSubset (h ≫ w ≫ sX)
      (S := ⟨_, hSY.1⟩) hSY with h0 | ⟨s, hs, hsnc⟩
    · have hsm : IsSmoothScheme (h ≫ w ≫ sX) := hgs ▸ hgres.isSmoothScheme
      haveI : LocallyOfFinitePresentation (h ≫ w ≫ sX) :=
        (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := h ≫ w ≫ sX)).mpr
          (hgs ▸ inferInstance)
      refine (MMP.Mori.DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℤ) _
        hsm).of_support_subset fun P hP => ?_
      have hP' := hsupp P hP
      have h0' := congrArg (fun C : Closeds Y => (C : Set Y)) h0
      simp only [Closeds.coe_bot] at h0'
      have hP'' : P.genericPoint ∈ ((⟨_, hSY.1⟩ : Closeds Y) : Set Y) := hP'
      rw [h0'] at hP''
      exact absurd hP'' (Set.notMem_empty _)
    · refine hsnc.of_support_subset fun P hP => ?_
      have hmem : P.genericPoint ∈ ⋃ E ∈ s, (E.support : Set Y) := by
        rw [hs]; exact hsupp P hP
      obtain ⟨E₁, hE₁, hηE⟩ := Set.mem_iUnion₂.1 hmem
      rw [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hηE] at hE₁
      rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply]
      simp [Finsupp.single_apply, hE₁]
  · exact fun P => (hcoef P).1
  · intro P hP
    by_contra hPe
    exact absurd hP (not_lt.mpr ((hcoef P).2 hPe))
  · intro P hP
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hP
    refine ⟨?_, ?_⟩
    · have := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPw (hTj j) (hBV (Tj j)) (hEd j)
      rw [← DivisorWithCoeffs.coeff_apply]
      linarith
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine (image_closure_subset_closure_image g.continuous).trans ?_
      rw [Set.image_singleton, ← hZ j, hWS']
      exact Set.subset_biUnion_of_mem (u := fun Z : IrreducibleCloseds X => (Z : Set X)) j.2
  · intro x hx
    rw [hWS'] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨Z, hZS', hxZ⟩ := hx
    have hxZ' : x ∈ closure {g (Tj ⟨Z, hZS'⟩).genericPoint} := by
      rw [← hZ ⟨Z, hZS'⟩]; exact hxZ
    have hcl : IsClosed (g.base '' (Tj ⟨Z, hZS'⟩).support) :=
      g.isClosedMap _ (by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure)
    have hmem : g (Tj ⟨Z, hZS'⟩).genericPoint ∈ g.base '' (Tj ⟨Z, hZS'⟩).support := by
      refine ⟨_, ?_, rfl⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have := closure_minimal (Set.singleton_subset_iff.mpr hmem) hcl hxZ'
    simp only [Set.mem_iUnion]
    exact ⟨Tj ⟨Z, hZS'⟩, Finset.mem_image.mpr ⟨⟨Z, hZS'⟩, Finset.mem_univ _, rfl⟩, this⟩

/-- The coefficients of the reduced divisor `∑_{P ∈ T} P`. -/
private theorem sum_single_one_apply {V : Scheme.{0}} [DecidableEq (MMP.Mori.PrimeDivisor V)]
    (T : Finset (MMP.Mori.PrimeDivisor V))
    (P : MMP.Mori.PrimeDivisor V) :
    (∑ Q ∈ T, Finsupp.single Q (1 : ℤ)) P = if P ∈ T then 1 else 0 := by
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

/-- **The adjoint sheaf computes `ℐ_W(M)`.** Let `g : V ⟶ X` be a projective birational morphism
of normal varieties, `A` an effective divisor on `V` all of whose components are `g`-exceptional,
`T` a finite set of prime divisors of `V` off the support of `A` mapping into `W` whose images
cover `W`, and `M_V = g^*M`. Then `g_* 𝒪_V(M_V + A - T) ≅ ℐ_W(M)`, the kernel of
`𝒪_X(M) ⟶ ι_* ι^* 𝒪_X(M)`. -/
private theorem nonempty_pushforward_iso_kernel
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsVariety ℂ sX) (W : Closeds X)
    {M : Divisor X} (hM : M.IsCartier)
    {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] (g : V ⟶ X)
    [IsDominant g] (hV : MMP.Mori.IsVariety ℂ (g ≫ sX)) [IsProper g]
    (hg : IsBirationalMorphism g) (MV : Divisor V)
    (hMV : M.IsPullback g (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant g M)
      MV)
    (A : Divisor V) (hAc : A.IsCartier) (hA : 0 ≤ A)
    (hAexc : ∀ P, A P ≠ 0 → RationalMap.IsExceptional g.toRationalMap P)
    (T : Finset (MMP.Mori.PrimeDivisor V)) (hAT : ∀ P ∈ T, A P = 0)
    (hTW : ∀ P ∈ T, g.base '' P.support ⊆ W)
    (hWT : (W : Set X) ⊆ ⋃ P ∈ T, g.base '' P.support) :
    Nonempty ((Scheme.Modules.pushforward g).obj
        (MV + A - ∑ P ∈ T, Finsupp.single P 1).divisorialSheaf ≅
      kernel ((Scheme.Modules.pullbackPushforwardAdjunction
        (Scheme.IdealSheafData.vanishingIdeal W).subschemeι).unit.app M.divisorialSheaf)) := by
  classical
  set η := (Scheme.Modules.pullbackPushforwardAdjunction
    (Scheme.IdealSheafData.vanishingIdeal W).subschemeι).unit.app M.divisorialSheaf with hη
  obtain ⟨e, he⟩ := Divisor.exists_iso_pushforward_divisorialSheaf_add_of_isExceptional sX g hX hV
    hg M hM _ MV hMV A hAc hA (fun P hP => hAexc P hP)
  set TD : Divisor V := ∑ P ∈ T, Finsupp.single P 1 with hTD
  have hTD0 : 0 ≤ TD := Finset.sum_nonneg fun _ _ => Finsupp.single_nonneg.2 zero_le_one
  have hFle : MV + A - TD ≤ MV + A := sub_le_self _ hTD0
  set φ := (Scheme.Modules.pushforward g).map (Divisor.divisorialSheafInclusion hFle) ≫ e.inv
    with hφ
  haveI : Mono φ := by
    haveI : Mono ((Scheme.Modules.pushforward g).map (Divisor.divisorialSheafInclusion hFle)) :=
      inferInstance
    exact mono_comp _ _
  have hTco : ∀ P, TD P = if P ∈ T then 1 else 0 := sum_single_one_apply T
  haveI : M.divisorialSheaf.IsQuasicoherent := Divisor.isQuasicoherent_divisorialSheaf M
  have hKη : Stacks.Algebraization.kernelSubmodule η =
      Stacks.Algebraization.idealPowerMultiple (Scheme.IdealSheafData.vanishingIdeal W) 1
        M.divisorialSheaf := by
    rw [hη, Stacks.Algebraization.kernelSubmodule_unit_app_eq_idealMultiple,
      Scheme.IdealSheafData.ker_subschemeι]
  have hKaff := (Stacks.Algebraization.idealPowerMultiple_le_iff
    (Scheme.IdealSheafData.vanishingIdeal W) 1 M.divisorialSheaf _).1 le_rfl
  -- the sections of `g_* 𝒪_V(M_V + A - T)` land in `ℐ_W · 𝒪_X(M)` over small affine opens
  have key : ∀ (V' : X.affineOpens) (V₀ : X.Opens) (_ : (V'.1 : X.Opens) ≤ V₀)
      (ψ : (RationalFunctions X)ˣ) (_ : M.IsLocalEquation V₀ ψ)
      (t : Γ((Scheme.Modules.pushforward g).obj (MV + A - TD).divisorialSheaf, V'.1)),
      (φ.app V'.1).hom t ∈ (Stacks.Algebraization.kernelSubmodule η).obj (op V'.1) := by
    intro V' V₀ hV'₀ ψ hψ t
    rw [hKη]
    refine hKaff V' ?_
    rw [pow_one]
    set σ := (φ.app V'.1).hom t with hσdef
    have hσt : (Scheme.Modules.Hom.app e.hom V'.1).hom σ =
        Submodule.inclusion (Divisor.divisorialSubmodule_mono hFle _) t := by
      rw [hσdef, hφ, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
        ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
      rfl
    have := MMP.Fourfold.subsingleton_irreducibleComponents (X := X)
    let ZX : irreducibleComponents X := pointComponent (genericPoint X)
    by_cases hU : componentGenericPoint X ZX ∈ (V'.1 : X.Opens)
    swap
    · have hσ0 : σ = 0 := by
        refine Subtype.ext (funext fun Z => absurd ?_ hU)
        rw [← Subsingleton.elim Z.1 ZX]
        exact Z.2
      rw [hσ0]
      exact Submodule.zero_mem _
    -- the local generator `ψ⁻¹` of `𝒪_X(M)` on `V'`
    have hψinv : M.IsDivisorialSection V'.1
        (fun Z => ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1) := by
      intro P hP
      right
      rw [P.valuation_component, P.ord_inv,
        ← hψ P (hP.mono (Set.inter_subset_inter_right _ hV'₀))]
    let e' : Γ(M.divisorialSheaf, V'.1) :=
      (⟨_, Divisor.mem_divisorialSubmodule.2 hψinv⟩ : M.divisorialSubmodule V'.1)
    -- `ψ σ` is a regular function `a` on `V'`
    have hsec : (0 : Divisor X).IsDivisorialSection V'.1
        (fun Z => (ψ : RationalFunctions X) Z.1 * σ.1 Z) := by
      intro P hP
      have hPV₀ : (P.support ∩ V₀).Nonempty := hP.mono (Set.inter_subset_inter_right _ hV'₀)
      have h1 : P.OrdGE (M.coeff P) ((ψ : RationalFunctions X) P.component) :=
        Or.inr (le_of_eq (by rw [P.valuation_component, hψ P hPV₀]))
      have h2 := h1.mul (σ.2 P hP)
      rw [add_neg_cancel] at h2
      rw [DivisorWithCoeffs.coeff_zero, neg_zero]
      exact h2
    obtain ⟨a, ha⟩ := hsec.exists_eq
    have hσ : σ = a • e' := by
      refine Subtype.ext (funext fun Z => ?_)
      change σ.1 Z = X.presheaf.germ _ _ Z.2 a *
        ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1
      have hZ : X.presheaf.germ _ _ Z.2 a = (ψ : RationalFunctions X) Z.1 * σ.1 Z := congrFun ha Z
      rw [hZ, mul_comm ((ψ : RationalFunctions X) Z.1), mul_assoc, ← Pi.mul_apply, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Pi.one_apply, mul_one]
    rw [hσ]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    -- `a` vanishes along `W`, since `g^*a` vanishes along every component of `T`
    rw [mem_vanishingIdeal_ideal_iff]
    intro w hwW hwV' hwa
    obtain ⟨P, hPT, y, hyP, rfl⟩ : ∃ P ∈ T, ∃ y ∈ P.support, g y = w := by simpa using hWT hwW
    have hy : y ∈ V.basicOpen (g.app V'.1 a) := by rw [← Scheme.preimage_basicOpen]; exact hwa
    have hηP : P.genericPoint ∈ V.basicOpen (g.app V'.1 a) := by
      have hsp : P.genericPoint ⤳ y := by
        rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact hyP
      exact hsp.mem_open (V.basicOpen _).isOpen hy
    have hPV' : (P.support ∩ (g ⁻¹ᵁ V'.1 : V.Opens)).Nonempty := ⟨y, hyP, V.basicOpen_le _ hy⟩
    have hc := P.componentGenericPoint_mem_of_nonempty hPV'
    have hgP := P.genericPoint_mem_of_nonempty hPV'
    have hv1 := valuation_germ_eq_one_of_mem_basicOpen P (g.app V'.1 a) hgP hηP hc
    rw [← MMP.Fourfold.fieldMap_germ g ZX P.component hU a] at hv1
    have hga : X.presheaf.germ _ _ hU a = (ψ : RationalFunctions X) ZX * σ.1 ⟨ZX, hU⟩ :=
      congrFun ha ⟨ZX, hU⟩
    rw [hga, map_mul, map_mul] at hv1
    have hPV₀ : (P.support ∩ (g ⁻¹ᵁ V₀ : V.Opens)).Nonempty :=
      hPV'.mono (Set.inter_subset_inter_right _ fun x hx => hV'₀ hx)
    rw [MMP.Fourfold.valuation_fieldMap_of_isPullback g hMV hψ P hPV₀ ZX] at hv1
    have hft : MMP.Fourfold.fieldMap g ZX P.component (σ.1 ⟨ZX, hU⟩) = t.1 ⟨P.component, hc⟩ := by
      apply fieldMap_eq_of_stalkSpecializes
      have h := (he V'.1 σ ZX hU P.component hc).1
      rw [hσt] at h
      exact h
    rw [hft] at hv1
    have ht := t.2 P hPV'
    have hFP : -(MV + A - TD).coeff P = 1 - MV.coeff P := by
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_sub, Finsupp.coe_add, Pi.sub_apply,
        Pi.add_apply, hAT P hPT, hTco, if_pos hPT]
      ring
    rw [hFP] at ht
    rcases ht with h0 | hge
    · rw [h0, map_zero, mul_zero] at hv1
      exact zero_ne_one hv1
    · have h3 : WithZero.exp (MV.coeff P) * WithZero.exp (1 - MV.coeff P) ≤
          WithZero.exp (MV.coeff P) * P.valuation (t.1 ⟨P.component, hc⟩) := by gcongr
      rw [← WithZero.exp_add, add_sub_cancel, hv1, ← WithZero.exp_zero, WithZero.exp_le_exp] at h3
      omega
  have hφη : φ ≫ η = 0 := by
    have hK : ∀ (U : X.Opens)
        (t : Γ((Scheme.Modules.pushforward g).obj (MV + A - TD).divisorialSheaf, U)),
        (φ.app U).hom t ∈ (Stacks.Algebraization.kernelSubmodule η).obj (op U) := by
      intro U t
      apply (Stacks.Algebraization.kernelSubmodule η).isSheaf
      rw [Opens.mem_grothendieckTopology]
      intro x hx
      obtain ⟨V₀, hxV₀, ψ, hψ⟩ := hM x
      obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hV'U⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (⟨hx, hxV₀⟩ : x ∈ U ⊓ V₀) (U ⊓ V₀).2
      refine ⟨V', homOfLE (hV'U.trans inf_le_left), ?_, hxV'⟩
      have h1 := key ⟨V', hV'⟩ V₀ (hV'U.trans inf_le_right) ψ hψ
        ((((Scheme.Modules.pushforward g).obj (MV + A - TD).divisorialSheaf).presheaf.map
          (homOfLE (hV'U.trans inf_le_left)).op).hom t)
      have h2 := (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality
        (homOfLE (hV'U.trans inf_le_left)).op) t).symm
      have h3 : (M.divisorialSheaf.presheaf.map (homOfLE (hV'U.trans inf_le_left)).op).hom
          ((φ.app U).hom t) = (φ.app V').hom
            ((((Scheme.Modules.pushforward g).obj (MV + A - TD).divisorialSheaf).presheaf.map
              (homOfLE (hV'U.trans inf_le_left)).op).hom t) := h2
      change (M.divisorialSheaf.presheaf.map (homOfLE (hV'U.trans inf_le_left)).op).hom
        ((φ.app U).hom t) ∈ (Stacks.Algebraization.kernelSubmodule η).obj (op V')
      rw [h3]
      exact h1
    ext U t
    have := hK U t
    rw [Stacks.Algebraization.kernelSubmodule_toSubmodule_obj] at this
    exact this
  have hle : Stacks.Algebraization.kernelSubmodule η ≤ imageSubmodule φ := by
    haveI : M.divisorialSheaf.IsQuasicoherent := Divisor.isQuasicoherent_divisorialSheaf M
    rw [hη, Stacks.Algebraization.kernelSubmodule_unit_app_eq_idealMultiple,
      Scheme.IdealSheafData.ker_subschemeι, Stacks.Algebraization.idealPowerMultiple_le_iff]
    intro U
    rw [pow_one]
    change _ ≤ (imageSubmodule φ).toSubmodule.obj _
    rw [imageSubmodule_obj φ inferInstance]
    refine Submodule.smul_le.2 fun a ha s _ => ?_
    have := MMP.Fourfold.subsingleton_irreducibleComponents (X := X)
    let ZX : irreducibleComponents X := pointComponent (genericPoint X)
    let ZY : irreducibleComponents V := pointComponent (genericPoint V)
    by_cases hU : componentGenericPoint X ZX ∈ (U : X.Opens)
    swap
    · refine ⟨0, ?_⟩
      rw [map_zero]
      refine Subtype.ext (funext fun Z => absurd ?_ hU)
      rw [← Subsingleton.elim Z.1 ZX]
      exact Z.2
    have hZY : componentGenericPoint V ZY ∈ g ⁻¹ᵁ (U : X.Opens) := by
      change g _ ∈ (U : X.Opens)
      rw [MMP.Fourfold.map_componentGenericPoint g ZY ZX]; exact hU
    obtain ⟨-, τs, -, hτs⟩ := he U s ZX hU ZY hZY
    set τ := (Scheme.Modules.Hom.app e.hom U).hom (a • s) with hτdef
    have hτ : τ = a • (Scheme.Modules.Hom.app e.hom U).hom s := Scheme.Modules.Hom.app_smul _ a s
    have hmem : (MV + A - TD).IsDivisorialSection (g ⁻¹ᵁ U) τ.1 := by
      intro P hP
      have hc := P.componentGenericPoint_mem_of_nonempty hP
      have hgP : P.genericPoint ∈ g ⁻¹ᵁ (U : X.Opens) := P.genericPoint_mem_of_nonempty hP
      have hval : τ.1 ⟨P.component, hc⟩ =
          V.presheaf.germ _ _ hc (g.app U a) * τs.1 ⟨P.component, hc⟩ := by
        rw [hτ, hτs]; rfl
      rw [hval]
      have hs := τs.2 P hP
      have ha' : P.OrdGE (TD P) (V.presheaf.germ _ _ hc (g.app U a)) := by
        rw [hTco]; split_ifs with hPT
        · refine ordGE_one_germ_of_notMem_basicOpen P _ hgP ?_ hc
          rw [← Scheme.preimage_basicOpen]
          intro h
          refine (mem_vanishingIdeal_ideal_iff W U a).1 ha _ (hTW P hPT ⟨P.genericPoint, ?_, rfl⟩)
            hgP h
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact subset_closure rfl
        · exact ordGE_zero_germ P _ hgP hc
      refine (ha'.mul hs).mono ?_
      have hA' : 0 ≤ A P := hA P
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_sub, Finsupp.coe_add, Pi.sub_apply,
        Pi.add_apply]
      omega
    refine ⟨⟨τ.1, hmem⟩, ?_⟩
    have hinv : (Scheme.Modules.Hom.app e.inv U).hom τ = a • s := by
      rw [hτdef, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id]
      rfl
    rw [← hinv]
    rfl
  have heq : imageSubmodule φ = Stacks.Algebraization.kernelSubmodule η :=
    le_antisymm (imageSubmodule_le_kernelSubmodule φ η hφη) hle
  exact ⟨imageSubmoduleIso φ inferInstance ≪≫ eqToIso (by rw [heq]) ≪≫
    Stacks.Algebraization.kernelSubmoduleIso η⟩

/-- **An adjoint model of `ℐ_W(M)`.** There are a smooth projective variety `V`, a projective
morphism `g : V ⟶ X` over `ℂ`, a canonical divisor `K_V`, an snc boundary `C` with coefficients
in `[0, 1]` and a Cartier divisor `F` on `V` such that `F - (K_V + C) ∼_ℚ g^*(M - (K + B))`
(through every Cartier multiple of `M - (K + B)`) and `g_* 𝒪_V(F) ≅ ℐ_W(M)`. With `B_V`, `T`
from `exists_crepantModel` and `A = ⌈-(B_V^{<1})⌉`, these are `F = g^*M + A - T` and
`C = A - T + B_V`. -/
private theorem exists_adjointModel
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of ℂ)) (hproj : IsProjectiveMorphism sX)
    {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hB : IsLcPair sX n K B) (hBeff : B.IsEffective) (hB1 : ∀ P, B.coeff P ≤ 1)
    (W : Closeds X) (S : Set (IrreducibleCloseds X))
    (hS : ∀ Z ∈ S, ∃ E : DivisorOver ℂ sX, E.center = Z ∧ IsDiscrepancy sX n K B E (-1))
    (hW : (W : Set X) = ⋃ Z ∈ S, (Z : Set X))
    {M : Divisor X} (hM : M.IsCartier) :
    ∃ (V : Scheme.{0}) (sV : V ⟶ Spec (.of ℂ)) (_ : MMP.Mori.IsProjectiveVariety ℂ sV)
      (_ : IsLocallyNoetherian V) (_ : IsNormal V) (g : V ⟶ X) (nV : ℕ) (KV : Divisor V)
      (C : QDivisor V) (F : Divisor V),
      MMP.Mori.IsSmoothScheme sV ∧ g ≫ sX = sV ∧ IsProjective g ∧
      KV.IsCanonicalDivisor sV nV ∧ C.IsSNC sV ∧ (∀ E, 0 ≤ C E) ∧ (∀ E, C E ≤ 1) ∧
      F.IsCartier ∧
      (∀ (m : ℕ) (D : Divisor X), D.IsCartier →
        Divisor.toQDivisor D = (m : ℚ) • (Divisor.toQDivisor M - (Divisor.toQDivisor K + B)) →
        ∃ DV : Divisor V,
          Divisor.toQDivisor DV = (m : ℚ) • (Divisor.toQDivisor F - (Divisor.toQDivisor KV + C)) ∧
          Nonempty (DV.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj D.divisorialSheaf)) ∧
      Nonempty ((Scheme.Modules.pushforward g).obj F.divisorialSheaf ≅
        kernel ((Scheme.Modules.pullbackPushforwardAdjunction
          (Scheme.IdealSheafData.vanishingIdeal W).subschemeι).unit.app M.divisorialSheaf)) := by
  classical
  obtain ⟨V, _, _, _, sV, _, g, _, nV, KV, BV, T, hsm, hgs, hgp, hgpr, hgb, hKV, hBVs, hBV1, hBVexc,
    hcrep, hT, hWT⟩ := exists_crepantModel sX hproj hB hBeff hB1 W S hS hW
  have hVar : MMP.Mori.IsVariety ℂ (g ≫ sX) := hgs ▸ ‹MMP.Mori.IsProjectiveVariety ℂ sV›.toIsVariety
  have hXvar : MMP.Mori.IsVariety ℂ sX := hB.1.1.1
  haveI : CompactSpace V :=
    haveI := hVar.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  -- `A = ⌈-(B_V^{<1})⌉` and the reduced divisor `T`
  let A : Divisor V := Finsupp.ofSupportFinite (fun P => if BV P < 1 then -⌊BV P⌋ else 0)
    (BV.support.finite_toSet.subset fun P hP => by
      by_contra h
      simp only [Finset.mem_coe, Finsupp.mem_support_iff, not_not] at h
      simp [h] at hP)
  have hAco : ∀ P, A P = if BV P < 1 then -⌊BV P⌋ else 0 := fun P => rfl
  let TD : Divisor V := ∑ P ∈ T, Finsupp.single P 1
  have hTco : ∀ P, TD P = if P ∈ T then 1 else 0 := sum_single_one_apply T
  have hA0 : 0 ≤ A := by
    rw [Finsupp.le_def]
    intro P
    rw [hAco]; split_ifs with h
    · have : ⌊BV P⌋ ≤ 0 := Int.floor_le_iff.mpr (by simpa using h)
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    · exact le_rfl
  have hAexc : ∀ P, A P ≠ 0 → RationalMap.IsExceptional g.toRationalMap P := by
    intro P hP
    rw [hAco] at hP
    split_ifs at hP with h
    · apply hBVexc
      have : ⌊BV P⌋ ≤ 0 := Int.floor_le_iff.mpr (by simpa using h)
      have h2 : ⌊BV P⌋ < 0 := by omega
      exact Int.floor_lt.mp h2 |>.trans_eq (by simp)
    · exact absurd rfl hP
  have hAT : ∀ P ∈ T, A P = 0 := by
    intro P hP
    rw [hAco, if_neg (by rw [(hT P hP).1]; exact lt_irrefl 1)]
  have hBV1T : ∀ P, BV P < 1 → P ∉ T := fun P h hP => by rw [(hT P hP).1] at h; exact lt_irrefl _ h
  obtain ⟨MV, hMV⟩ := hM.exists_isPullback
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant g M)
  let C : QDivisor V := Divisor.toQDivisor (A - TD) + BV
  have hCco : ∀ P, C P = ((A P - TD P : ℤ) : ℚ) + BV P := fun P => by
    simp [C, ← DivisorWithCoeffs.coeff_apply]
  have hCval : ∀ P, (BV P < 1 → C P = Int.fract (BV P)) ∧ (¬ BV P < 1 → BV P = 1 ∧
      C P = if P ∈ T then 0 else 1) := by
    intro P
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hCco, hAco, if_pos h, hTco, if_neg (hBV1T P h), Int.fract]
      push_cast; ring
    · have h1 : BV P = 1 := le_antisymm (hBV1 P) (not_lt.mp h)
      refine ⟨h1, ?_⟩
      rw [hCco, hAco, if_neg h, hTco, h1]
      split_ifs <;> norm_num
  refine ⟨V, sV, inferInstance, inferInstance, inferInstance, g, nV, KV, C, MV + A - TD, hsm, hgs,
    hgp, hKV, ?_, ?_, ?_, MMP.Fourfold.isCartier_of_isSmoothScheme hsm _, ?_, ?_⟩
  · refine hBVs.of_support_subset fun P hP => ?_
    rw [Finsupp.mem_support_iff] at hP ⊢
    intro h0
    apply hP
    rw [(hCval P).1 (by rw [h0]; exact zero_lt_one), h0, Int.fract_zero]
  · intro P
    by_cases h : BV P < 1
    · rw [(hCval P).1 h]; exact Int.fract_nonneg _
    · rw [((hCval P).2 h).2]; split_ifs <;> norm_num
  · intro P
    by_cases h : BV P < 1
    · rw [(hCval P).1 h]; exact (Int.fract_lt_one _).le
    · rw [((hCval P).2 h).2]; split_ifs <;> norm_num
  · intro m D hD hDq
    have hcoV : ∀ (E : Divisor V) P, Divisor.toQDivisor E P = (E P : ℚ) := fun _ _ => rfl
    have hcoX : ∀ (E : Divisor X) P, Divisor.toQDivisor E P = (E P : ℚ) := fun _ _ => rfl
    have hDq' : ∀ P, (D P : ℚ) = m * (M P - (K P + B P)) := fun P => by
      have := congrArg (· P) hDq
      simpa [hcoX] using this
    set G : Divisor X := (m : ℤ) • M - D with hG
    have hGC : G.IsCartier := (hM.zsmul _).sub hD
    have hGq : Divisor.toQDivisor G = (m : ℤ) • (Divisor.toQDivisor K + B) := by
      refine Finsupp.ext fun P => ?_
      rw [hcoX]
      simp only [G, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul,
        Int.cast_sub, Int.cast_mul, Int.cast_natCast, hcoX]
      rw [hDq' P, zsmul_eq_mul]; push_cast; ring
    have hGs := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant g G
    obtain ⟨DY, hDYq, hDYpb⟩ : ∃ DY : Divisor V,
        Divisor.toQDivisor DY = (m : ℤ) • (Divisor.toQDivisor KV + BV) ∧ G.IsPullback g hGs DY := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · have hG0 : G = 0 := by
          refine Finsupp.ext fun P => ?_
          have h1 := hDq' P
          simp only [Nat.cast_zero, zero_mul, Int.cast_eq_zero] at h1
          rw [hG]
          simp [h1]
        refine ⟨0, by simp, ?_⟩
        revert hGs
        rw [hG0]
        intro hGs
        exact Divisor.isPullback_zero hGs
      · obtain ⟨DY, h1, _, h2⟩ := hcrep m hm G hGq hGC
        exact ⟨DY, h1, h2⟩
    have hDs := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant g D
    have hDpb : D.IsPullback g hDs ((m : ℤ) • MV + (-1 : ℤ) • DY) := by
      have h1 := hMV.zsmul hM (m : ℤ)
        (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant g _)
      have h2 := hDYpb.zsmul hGC (-1 : ℤ)
        (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant g _)
      have h3 := h1.add (hM.zsmul _) (hGC.zsmul _)
        (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant g _) h2
      refine Divisor.IsPullback.of_eq ?_ h3
      simp [G]
    refine ⟨(m : ℤ) • MV + (-1 : ℤ) • DY, ?_, ?_⟩
    · refine Finsupp.ext fun P => ?_
      have h1 := congrArg (· P) hDYq
      simp only [hcoV, Finsupp.coe_smul, Pi.smul_apply, Finsupp.coe_add, Pi.add_apply,
        zsmul_eq_mul] at h1
      simp only [hcoV, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_neg, Int.cast_one,
        Finsupp.coe_sub, Pi.sub_apply, Int.cast_sub, hCco]
      rw [h1]; push_cast; ring
    · have := Divisor.nonempty_divisorialSheaf_pullback_iso hD g hDs
      rwa [hDpb.pullback_eq hD] at this
  · haveI := hgpr
    exact nonempty_pushforward_iso_kernel sX hXvar W hM g hVar hgb MV hMV A
      (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _) hA0 hAexc T hAT
      (fun P hP => (hT P hP).2) hWT

/-- **Vanishing for the twisted ideal of a union of lc centres, boundary coefficients `≤ 1`**:
`H^i(X, ℐ_W(M)) = 0` for
`i > 0`, where `ℐ_W(M)` is the kernel of the unit `𝒪_X(M) ⟶ ι_* ι^* 𝒪_X(M)`. It is the
vanishing of `H^i(X, g_* 𝒪_V(F))` for the adjoint model `exists_adjointModel`. -/
private theorem isZero_Hgroup_kernel_unit_of_coeff_le_one
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of ℂ)) (hproj : IsProjectiveMorphism sX)
    {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hB : IsLcPair sX n K B) (hBeff : B.IsEffective) (hB1 : ∀ P, B.coeff P ≤ 1)
    (W : Closeds X) (S : Set (IrreducibleCloseds X))
    (hS : ∀ Z ∈ S, ∃ E : DivisorOver ℂ sX, E.center = Z ∧ IsDiscrepancy sX n K B E (-1))
    (hW : (W : Set X) = ⋃ Z ∈ S, (Z : Set X))
    {M : Divisor X} (hM : M.IsCartier)
    (hamp : (Divisor.toQDivisor M - (Divisor.toQDivisor K + B)).IsAmple) (i : ℕ) (hi : 0 < i) :
    IsZero (Hgroup X.ringCatSheaf ⊤ i (kernel
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (Scheme.IdealSheafData.vanishingIdeal W).subschemeι).unit.app M.divisorialSheaf))) := by
  obtain ⟨V, sV, _, _, _, g, nV, KV, C, F, hsm, hgs, hgp, hKV, hC, hC0, hC1, hF, hlin, ⟨e⟩⟩ :=
    exists_adjointModel sX hproj hB hBeff hB1 W S hS hW hM
  haveI : MMP.Mori.IsProjectiveVariety ℂ sX :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ sX).2 ⟨hB.1.1.1, hproj⟩
  obtain ⟨m, hm, D, hD, hDC, hDA⟩ := hamp
  haveI := hDC.isInvertibleModule_divisorialSheaf
  have hv := MMP.Mori.subsingleton_cohomologyOverField_rightDerived_pushforward_divisorialSheaf
    sX sV hsm g hgs hgp KV hKV C hC hC0 hC1 F hF D.divisorialSheaf hDA
    ⟨m, hm, hlin m D hDC hD⟩ i 0 hi
  have hz : IsZero (Hgroup X.ringCatSheaf ⊤ i
      (((Scheme.Modules.pushforward g).rightDerived 0).obj F.divisorialSheaf)) := by
    refine (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      X.ringCatSheaf ⊤ i _).1 ?_
    rw [ModuleCat.isZero_iff_subsingleton]
    exact hv
  exact hz.of_iso ((Hfunctor X.ringCatSheaf ⊤ i).mapIso
    (e.symm ≪≫ ((Scheme.Modules.pushforward g).rightDerivedZeroIsoSelf.app _).symm))

/-- On a scheme of dimension at most one every point has coheight at most one. -/
private theorem coheight_le_one_of_topologicalKrullDim_le_one {X : Scheme.{0}}
    (hd : topologicalKrullDim X ≤ 1) (x : X) : Order.coheight x ≤ 1 := by
  have h : (Order.coheight x : WithBot ℕ∞) ≤ 1 := by
    refine le_trans ?_ hd
    rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact Order.coheight_le_krullDim _
  exact_mod_cast h

/-- On a normal variety of dimension at most one no divisor over `X` is exceptional: its centre
has codimension at most one. -/
private theorem not_isExceptional_of_topologicalKrullDim_le_one {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    (hd : topologicalKrullDim X ≤ 1) (D : DivisorOver ℂ sX) : ¬ D.IsExceptional := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI : IsSeparated sX := hX.1.toIsSeparated
  haveI : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of ℂ) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  intro hD
  unfold DivisorOver.IsExceptional at hD
  rw [MMP.Positivity.isExceptional_toRationalMap_iff] at hD
  have hcl : TopologicalSpace.Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := TopologicalSpace.Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center] at hD
  exact absurd (hD.trans (coheight_le_one_of_topologicalKrullDim_le_one hd _)) (by decide)

/-- On a normal integral scheme of dimension at most one every local ring is a field or a discrete
valuation ring, hence factorial, so every divisor is Cartier. -/
private theorem isCartier_of_topologicalKrullDim_le_one {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (hd : topologicalKrullDim X ≤ 1) (D : Divisor X) :
    D.IsCartier := by
  have hUFD : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) := by
    intro x
    have hco' := coheight_le_one_of_topologicalKrullDim_le_one hd x
    rcases (show Order.coheight x = 0 ∨ Order.coheight x = 1 by
      rcases eq_or_ne (Order.coheight x) 0 with h | h
      · exact Or.inl h
      · exact Or.inr (le_antisymm hco' (ENat.one_le_iff_ne_zero.mpr h))) with h0 | h1
    · -- the generic point: the stalk is the function field
      have hmax : IsMax x := Order.coheight_eq_zero.mp h0
      have hx : x = genericPoint X := by
        have hle : x ≤ genericPoint X :=
          Scheme.le_iff_specializes.mpr ((genericPoint_spec X).specializes (Set.mem_univ x))
        exact ((Scheme.le_iff_specializes.mp (hmax hle)).antisymm
          (Scheme.le_iff_specializes.mp hle)).eq
      subst hx
      change UniqueFactorizationMonoid X.functionField
      infer_instance
    · let P : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h1
      have hP : P.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x h1
      have := P.isDiscreteValuationRing_localRing
      rw [← hP]
      change UniqueFactorizationMonoid P.localRing
      infer_instance
  induction D using Finsupp.induction_linear with
  | zero => exact Divisor.isCartier_zero
  | add D₁ D₂ h₁ h₂ => exact h₁.add h₂
  | single P c =>
    rw [← Finsupp.smul_single_one]
    exact (MMP.Threefold.Mori.isCartier_single_of_forall_uniqueFactorizationMonoid hUFD P).zsmul c

/-- On a scheme of dimension at most one the generic point of a prime divisor is a closed point:
a proper specialization would have coheight at least two. -/
private theorem isClosed_singleton_genericPoint_of_topologicalKrullDim_le_one {X : Scheme.{0}}
    (hd : topologicalKrullDim X ≤ 1) (P : MMP.Mori.PrimeDivisor X) :
    IsClosed ({P.genericPoint} : Set X) := by
  refine isClosed_iff_clusterPt.mpr fun y hy => ?_
  have hsp : P.genericPoint ⤳ y :=
    specializes_iff_mem_closure.mpr (mem_closure_iff_clusterPt.mpr hy)
  by_contra hne
  have hlt : y < P.genericPoint := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp)
    fun hle => hne (hsp.antisymm (Scheme.le_iff_specializes.mp hle)).eq.symm
  have h1 := Order.coheight_strictAnti hlt
  rw [P.coheight_genericPoint] at h1
  exact absurd (lt_of_lt_of_le (h1 (by simp))
    (coheight_le_one_of_topologicalKrullDim_le_one hd y)) (lt_irrefl _)

/-- **Adding an effective divisor on a curve preserves `H¹`-vanishing.** On a proper normal curve
`X` over `ℂ`, if `H¹(X, 𝒪_X(N)) = 0` and `R ≥ 0`, then `Hⁱ(X, 𝒪_X(N + R)) = 0` for `i > 0`: the
cokernel of `𝒪_X(N) ⟶ 𝒪_X(N + R)` is coherent with finite support, so its `H¹` vanishes, and
`H²` vanishes on a curve. -/
private theorem isZero_Hgroup_divisorialSheaf_add_of_nonneg {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (sX : X ⟶ Spec (.of ℂ)) [IsProper sX]
    (hXv : MMP.Mori.IsVariety ℂ sX) (hd : topologicalKrullDim X ≤ 1) (N R : Divisor X)
    (hR : 0 ≤ R) (h1 : IsZero (Hgroup X.ringCatSheaf ⊤ 1 N.divisorialSheaf)) (i : ℕ)
    (hi : 0 < i) : IsZero (Hgroup X.ringCatSheaf ⊤ i (N + R).divisorialSheaf) := by
  classical
  haveI : IsNoetherian X := {}
  rcases Nat.lt_or_ge 1 i with h2 | h2
  · exact MMP.Fourfold.isZero_Hgroup_of_topologicalKrullDim_le _ (d := 1) (by exact_mod_cast hd) h2
  obtain rfl : i = 1 := by omega
  set j := Divisor.divisorialSheafInclusion (le_add_of_nonneg_right hR : N ≤ N + R) with hj
  have hS : (ShortComplex.mk j (cokernel.π j) (cokernel.condition j)).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel j) }
  -- the cokernel is coherent and supported on the finitely many points of `Supp R`
  haveI := (MMP.Threefold.isCoherent_divisorialSheaf_and_isIso_divisorialSheafTensorMul sX hXv N
    0).1
  haveI := (MMP.Threefold.isCoherent_divisorialSheaf_and_isIso_divisorialSheafTensorMul sX hXv
    (N + R) 0).1
  haveI hcoh : (cokernel j).IsCoherent := SheafOfModules.cokernel_isCoherent j
  set Z : Set X := ⋃ P ∈ R.support, ({P.genericPoint} : Set X) with hZ
  have hZc : IsClosed Z := isClosed_biUnion_finset fun P _ =>
    isClosed_singleton_genericPoint_of_topologicalKrullDim_le_one hd P
  have hsupp : SheafOfModules.supp (cokernel j) ⊆ Z := by
    have h := Stacks.Coherent.supp_cokernel_subset_support_of_isIso_restrict
      (Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZc⟩) j ?_
    · intro x hx
      have := h hx
      rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
    · refine Divisor.isIso_restrict_divisorialSheafInclusion _ fun E hE => ?_
      rw [DivisorWithCoeffs.coeff_add, left_eq_add]
      by_contra hER
      obtain ⟨x, hxE, hxU⟩ := hE
      apply hxU
      change x ∈ ((Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZc⟩).support : Set X)
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      have hEs : E ∈ R.support := Finsupp.mem_support_iff.mpr hER
      have hxη : x = E.genericPoint := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
          (isClosed_singleton_genericPoint_of_topologicalKrullDim_le_one hd E).closure_eq] at hxE
        exact hxE
      exact Set.mem_biUnion hEs (hxη ▸ rfl)
  have hfin : (SheafOfModules.supp (cokernel j)).Finite :=
    ((R.support.finite_toSet.biUnion fun P _ => Set.finite_singleton _).subset hsupp)
  have hdimQ : topologicalKrullDim (SheafOfModules.supp (cokernel j)) ≤ 0 := by
    haveI : Finite (SheafOfModules.supp (cokernel j)) := hfin.to_subtype
    haveI : T1Space (SheafOfModules.supp (cokernel j)) := by
      refine ⟨fun x => ?_⟩
      obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.mp (hsupp x.2)
      have hx : (x : X) = P.genericPoint := hxP
      have hcl := isClosed_singleton_genericPoint_of_topologicalKrullDim_le_one hd P
      rw [← hx] at hcl
      have h' : (Subtype.val ⁻¹' ({(x : X)} : Set X) :
          Set (SheafOfModules.supp (cokernel j))) = {x} := by
        ext y; simp [Subtype.ext_iff]
      rw [← h']
      exact hcl.preimage continuous_subtype_val
    exact topologicalKrullDim_zero_of_discreteTopology _
  have hQ := isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero ℂ sX (cokernel j)
    hdimQ 1 one_pos
  have hQ' : IsZero (Hgroup X.ringCatSheaf ⊤ 1 (cokernel j)) := by
    refine (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      X.ringCatSheaf ⊤ 1 _).1 ?_
    rw [ModuleCat.isZero_iff_subsingleton]
    rw [ModuleCat.isZero_iff_subsingleton] at hQ
    exact hQ
  let D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (secF X.ringCatSheaf ⊤)
  exact (D.exact_map hS 1).isZero_of_both_isZero h1 hQ'

/-- The pull-back of a Cartier divisor along the identity is the divisor itself. -/
private theorem isPullback_id {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (M : Divisor X) :
    M.IsPullback (𝟙 X) (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (𝟙 X) M)
      M := by
  intro U φ hφ E hE
  have hffm : ∀ t : X.functionField, functionFieldMap (𝟙 X) t = t := fun t =>
    (functionFieldMap (𝟙 X)).injective
      (MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply (𝟙 X) (𝟙 X) (Category.id_comp _) t)
  have hfm : ∀ x, MMP.Fourfold.fieldMap (𝟙 X) E.component E.component x = x := by
    intro x
    rw [MMP.Fourfold.fieldMap_eq, RingHom.comp_apply, RingHom.comp_apply, hffm,
      ← ConcreteCategory.comp_apply, Iso.hom_inv_id]
    rfl
  have hu : MMP.Mori.pullbackComponent (𝟙 X)
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (𝟙 X) M) hφ E.component
        (E.map_componentGenericPoint_mem (𝟙 X) hE) =
      Units.map (RationalFunctions.component X E.component).toMonoidHom φ := by
    ext
    rw [MMP.Fourfold.pullbackComponent_eq_fieldMap (𝟙 X) _ hφ E.component _ E.component, hfm]
    rfl
  rw [hu, ← PrimeDivisor.ord_eq_ordUnit]
  exact hφ E hE

/-- In dimension at least two the boundary of an lc pair has coefficients at most one: a
coefficient above one makes the total discrepancy `< -1`, hence `discrep = -∞` (Kollár–Mori
2.31(1)). -/
private theorem coeff_le_one_of_isLcPair {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {d : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (h : IsLcPair sX d K Δ) (hd : 2 ≤ d) (E : MMP.Mori.PrimeDivisor X) :
    Δ.coeff E ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hX := h.1.1
  have htot := totalDiscrep_le_neg_coeff hX (MMP.Positivity.IsPair.exists_isDiscrepancy
    h.1.isPair h.1.2.1 (DivisorOver.ofPrimeDivisor ℂ hX E))
  have hc : (((-Δ.coeff E : ℚ) : ℝ) : EReal) < ((-1 : ℝ) : EReal) :=
    EReal.coe_lt_coe_iff.mpr (by push_cast; exact_mod_cast (by linarith : -Δ.coeff E < -1))
  have h2 := h.2
  rw [discrep_eq_bot_of_totalDiscrep_lt_neg_one h.1 hd
    (htot.trans_lt (hc.trans_eq (by norm_num)))] at h2
  exact ((EReal.bot_lt_coe (-1)).trans_eq (by simp)).not_ge h2

/-- `H^i(X, ℐ_W(M)) = 0` for `i > 0` when some boundary coefficient of `B` exceeds one. -/
private theorem isZero_Hgroup_kernel_unit_of_not_forall_coeff_le_one
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of ℂ)) (hproj : IsProjectiveMorphism sX)
    {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hB : IsLcPair sX n K B) (hBeff : B.IsEffective) (hB1 : ¬ ∀ P, B.coeff P ≤ 1)
    (W : Closeds X) (S : Set (IrreducibleCloseds X))
    (hS : ∀ Z ∈ S, ∃ E : DivisorOver ℂ sX, E.center = Z ∧ IsDiscrepancy sX n K B E (-1))
    (hW : (W : Set X) = ⋃ Z ∈ S, (Z : Set X))
    {M : Divisor X} (hM : M.IsCartier)
    (hamp : (Divisor.toQDivisor M - (Divisor.toQDivisor K + B)).IsAmple) (i : ℕ) (hi : 0 < i) :
    IsZero (Hgroup X.ringCatSheaf ⊤ i (kernel
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (Scheme.IdealSheafData.vanishingIdeal W).subschemeι).unit.app M.divisorialSheaf))) := by
  classical
  have hX : IsNormalVariety ℂ sX := hB.1.1
  have hPw : IsPairWith sX n K B := hB.1
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hproj
  -- an lc pair has a coefficient above one only in dimension at most one
  have hn1 : n ≤ 1 := by
    by_contra h
    exact hB1 fun P => coeff_le_one_of_isLcPair hB (by omega) P
  have hd : topologicalKrullDim X ≤ 1 := by
    rw [hB.1.2.1.topologicalKrullDim_eq]; exact_mod_cast hn1
  have hnoexc := not_isExceptional_of_topologicalKrullDim_le_one hX hd
  have hcart := isCartier_of_topologicalKrullDim_le_one hd
  -- lower the coefficients above one: `R = ∑ (⌈b⌉ - 1) P` over the points with `b > 1`
  let R : Divisor X := Finsupp.ofSupportFinite (fun P => if 1 < B P then ⌈B P⌉ - 1 else 0)
    (B.support.finite_toSet.subset fun P hP => by
      by_contra h
      simp only [Finset.mem_coe, Finsupp.mem_support_iff, not_not] at h
      simp [h] at hP)
  have hRco : ∀ P, R P = if 1 < B P then ⌈B P⌉ - 1 else 0 := fun P => rfl
  have hR0 : 0 ≤ R := by
    rw [Finsupp.le_def]
    intro P
    rw [hRco]; split_ifs with h
    · have : (1 : ℤ) < ⌈B P⌉ := Int.lt_ceil.mpr (by exact_mod_cast h)
      simp only [Finsupp.coe_zero, Pi.zero_apply]; omega
    · exact le_rfl
  set B'' : QDivisor X := B - Divisor.toQDivisor R with hB''
  have hB''co : ∀ P, B'' P = B P - R P := fun P => by simp [B'', ← DivisorWithCoeffs.coeff_apply]
  have hB''le : ∀ P, B''.coeff P ≤ 1 := by
    intro P
    rw [DivisorWithCoeffs.coeff_apply, hB''co, hRco]
    split_ifs with h
    · push_cast
      linarith [Int.le_ceil (B P)]
    · simp only [Int.cast_zero, sub_zero]; exact not_lt.mp h
  have hB''eff : B''.IsEffective := by
    intro P
    rw [DivisorWithCoeffs.coeff_apply, hB''co, hRco]
    split_ifs with h
    · push_cast
      linarith [Int.ceil_lt_add_one (B P)]
    · simp only [Int.cast_zero, sub_zero]; exact hBeff P
  -- `(X, B'')` is an lc pair with the same lc centres in `S`
  have hB'' : IsLcPair sX n K B'' := by
    refine ⟨⟨hX, hB.1.2.1, ?_⟩, ?_⟩
    · have := hB.1.2.2.add (QDivisor.isQCartier_toQDivisor (hcart (-R)))
      convert this using 1
      simp [B'', sub_eq_add_neg, add_assoc]
    · rw [discrep_eq_top fun D a hD _ => hnoexc D hD]
      exact le_top
  have hcentre : ∀ E : DivisorOver ℂ sX, IsDiscrepancy sX n K B E (-1) →
      ∃ Γ : MMP.Mori.PrimeDivisor X, (E.center : Set X) = Γ.support ∧ B.coeff Γ = 1 ∧
        IsDiscrepancy sX n K B'' E (-1) := by
    intro E hE
    obtain ⟨Γ, hΓc, hΓd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hPw E (hnoexc E)
    have hBΓ : B.coeff Γ = 1 := neg_injective (hΓd.eq hE)
    obtain ⟨Γ', hΓ'c, hΓ'd⟩ :=
      DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hB''.1 E (hnoexc E)
    have hΓΓ' : Γ' = Γ := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support (by
      rw [← hΓ'c, hΓc]; exact MMP.Flips.primeDivisor_genericPoint_mem_support Γ)
    rw [hΓΓ'] at hΓ'd
    have hB''Γ : B''.coeff Γ = 1 := by
      rw [DivisorWithCoeffs.coeff_apply, hB''co, hRco, ← DivisorWithCoeffs.coeff_apply, hBΓ,
        if_neg (lt_irrefl 1)]
      simp
    rw [hB''Γ] at hΓ'd
    exact ⟨Γ, hΓc, hBΓ, hΓ'd⟩
  have hS'' : ∀ Z ∈ S, ∃ E : DivisorOver ℂ sX, E.center = Z ∧ IsDiscrepancy sX n K B'' E (-1) :=
    fun Z hZ => by
      obtain ⟨E, hEc, hEd⟩ := hS Z hZ
      obtain ⟨-, -, -, h⟩ := hcentre E hEd
      exact ⟨E, hEc, h⟩
  have hamp'' : (Divisor.toQDivisor (M - R) - (Divisor.toQDivisor K + B'')).IsAmple := by
    convert hamp using 1
    simp only [B'', map_sub]
    abel
  -- the vanishing for `M - R`
  have hvan := isZero_Hgroup_kernel_unit_of_coeff_le_one sX hproj hB'' hB''eff hB''le W S hS'' hW
    (hcart _) hamp''
  -- the centres are finitely many points `Γ` of `X`
  obtain ⟨S', hS'S, hWS'⟩ := exists_finset_subset_eq_biUnion W S hW
  have hΓ : ∀ Z : S', ∃ Γ : MMP.Mori.PrimeDivisor X,
      ((Z : IrreducibleCloseds X) : Set X) = Γ.support := fun Z => by
    obtain ⟨E, hEc, hEd⟩ := hS Z.1 (hS'S Z.2)
    obtain ⟨Γ, hΓc, -, -⟩ := hcentre E hEd
    exact ⟨Γ, by rw [← hEc]; exact hΓc⟩
  choose Γ hΓ using hΓ
  set T : Finset (MMP.Mori.PrimeDivisor X) := Finset.univ.image Γ with hT
  have hid : ∀ s : Set X, (𝟙 X : X ⟶ X).base '' s = s := fun s => by simp
  have hTW : ∀ P ∈ T, (𝟙 X : X ⟶ X).base '' P.support ⊆ W := by
    intro P hP
    obtain ⟨Z, -, rfl⟩ := Finset.mem_image.mp hP
    rw [hid, ← hΓ Z, hWS']
    exact Set.subset_biUnion_of_mem (u := fun Z : IrreducibleCloseds X => (Z : Set X)) Z.2
  have hWT : (W : Set X) ⊆ ⋃ P ∈ T, (𝟙 X : X ⟶ X).base '' P.support := by
    intro x hx
    rw [hWS'] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨Z, hZ, hxZ⟩ := hx
    simp only [Set.mem_iUnion, hid]
    exact ⟨Γ ⟨Z, hZ⟩, Finset.mem_image.mpr ⟨⟨Z, hZ⟩, Finset.mem_univ _, rfl⟩,
      (hΓ ⟨Z, hZ⟩) ▸ hxZ⟩
  -- both kernels are divisorial sheaves on `X` itself
  have hV : MMP.Mori.IsVariety ℂ (𝟙 X ≫ sX) := by rw [Category.id_comp]; exact hX.1
  obtain ⟨e₁⟩ := nonempty_pushforward_iso_kernel sX hX.1 W hM (𝟙 X) hV
    (isBirationalMorphism_of_isIso _) M (isPullback_id M) 0 Divisor.isCartier_zero le_rfl
    (fun P h => absurd rfl h) T (fun _ _ => rfl) hTW hWT
  obtain ⟨e₂⟩ := nonempty_pushforward_iso_kernel sX hX.1 W (hcart (M - R)) (𝟙 X) hV
    (isBirationalMorphism_of_isIso _) (M - R) (isPullback_id (M - R)) 0 Divisor.isCartier_zero
    le_rfl (fun P h => absurd rfl h) T (fun _ _ => rfl) hTW hWT
  have h1 : IsZero (Hgroup X.ringCatSheaf ⊤ 1
      (M - R + 0 - ∑ P ∈ T, Finsupp.single P 1).divisorialSheaf) :=
    (hvan 1 one_pos).of_iso ((Hfunctor X.ringCatSheaf ⊤ 1).mapIso
      (((Scheme.Modules.pushforwardId X).app _).symm ≪≫ e₂))
  have h2 := isZero_Hgroup_divisorialSheaf_add_of_nonneg sX hX.1 hd
    (M - R + 0 - ∑ P ∈ T, Finsupp.single P 1) R hR0 h1 i hi
  rw [show M - R + 0 - ∑ P ∈ T, Finsupp.single P 1 + R = M + 0 - ∑ P ∈ T, Finsupp.single P 1 by
    abel] at h2
  exact h2.of_iso ((Hfunctor X.ringCatSheaf ⊤ i).mapIso
    (e₁.symm ≪≫ (Scheme.Modules.pushforwardId X).app _))

/-- **Vanishing for the twisted ideal of a union of lc centres**: `H^i(X, ℐ_W(M)) = 0` for
`i > 0`, where `ℐ_W(M)` is the kernel of the unit `𝒪_X(M) ⟶ ι_* ι^* 𝒪_X(M)`. -/
private theorem isZero_Hgroup_kernel_unit
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of ℂ)) (hproj : IsProjectiveMorphism sX)
    {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hB : IsLcPair sX n K B) (hBeff : B.IsEffective)
    (W : Closeds X) (S : Set (IrreducibleCloseds X))
    (hS : ∀ Z ∈ S, ∃ E : DivisorOver ℂ sX, E.center = Z ∧ IsDiscrepancy sX n K B E (-1))
    (hW : (W : Set X) = ⋃ Z ∈ S, (Z : Set X))
    {M : Divisor X} (hM : M.IsCartier)
    (hamp : (Divisor.toQDivisor M - (Divisor.toQDivisor K + B)).IsAmple) (i : ℕ) (hi : 0 < i) :
    IsZero (Hgroup X.ringCatSheaf ⊤ i (kernel
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (Scheme.IdealSheafData.vanishingIdeal W).subschemeι).unit.app M.divisorialSheaf))) := by
  by_cases hB1 : ∀ P, B.coeff P ≤ 1
  · exact isZero_Hgroup_kernel_unit_of_coeff_le_one sX hproj hB hBeff hB1 W S hS hW hM hamp i hi
  · exact isZero_Hgroup_kernel_unit_of_not_forall_coeff_le_one sX hproj hB hBeff hB1 W S hS hW hM
      hamp i hi

/-- For the empty closed subset the subscheme is empty, so the unit `𝓕 ⟶ ι_* ι^* 𝓕` is zero and
its kernel is all of `𝓕`. -/
private theorem isIso_kernel_ι_unit_vanishingIdeal_bot {X : Scheme.{0}} (F : X.Modules) :
    IsIso (kernel.ι ((Scheme.Modules.pullbackPushforwardAdjunction
      (Scheme.IdealSheafData.vanishingIdeal (⊥ : Closeds X)).subschemeι).unit.app F)) := by
  haveI : IsEmpty (Scheme.IdealSheafData.vanishingIdeal (⊥ : Closeds X)).subscheme := by
    rw [Scheme.IdealSheafData.vanishingIdeal_bot]; infer_instance
  have hZ : IsZero ((Scheme.Modules.pullback
      (Scheme.IdealSheafData.vanishingIdeal (⊥ : Closeds X)).subschemeι).obj F) := by
    rw [IsZero.iff_id_eq_zero]
    ext U x
    rw [← one_smul Γ((Scheme.IdealSheafData.vanishingIdeal (⊥ : Closeds X)).subscheme, U) x,
      Subsingleton.elim (1 : Γ((Scheme.IdealSheafData.vanishingIdeal (⊥ : Closeds X)).subscheme,
        U)) 0, zero_smul, map_zero, map_zero]
  rw [(Functor.map_isZero (Scheme.Modules.pushforward
    (Scheme.IdealSheafData.vanishingIdeal (⊥ : Closeds X)).subschemeι) hZ).eq_of_tgt
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (Scheme.IdealSheafData.vanishingIdeal (⊥ : Closeds X)).subschemeι).unit.app F) 0]
  infer_instance

end MMP.Mori.LcCentreUnionExtension

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.Mori

attribute [local instance] HasDerivedCategory.standard in
/-- **Vanishing and extension for a union of lc centres.** Let `(X, B)` be an lc pair (with
canonical divisor `K` and effective `ℚ`-boundary `B`) on a normal projective variety of
dimension `n` over `ℂ`, and let `W ⊆ X` be a union of lc centres of `(X, B)` (centres of
divisors `E` over `X` with `a(E, X, B) = -1`), with its
reduced subscheme structure `ι : W ⟶ X`. If `M` is a Cartier divisor with `M - (K + B)` ample,
then, writing `η : 𝒪_X(M) ⟶ ι_* ι^* 𝒪_X(M)` for the adjunction unit, for every `i > 0`
`H^i(X, ker η) = H^i(X, ℐ_W(M)) = 0` and `H^i(W, ι^* 𝒪_X(M)) = H^i(W, 𝒪_W(M)) = 0`, and the
restriction `H^0(X, 𝒪_X(M)) → H^0(W, 𝒪_W(M))` (the map `η` on global sections) is surjective. -/
@[mmp "thm_mmp_lc_bpf_lc_centre_ideal_vanishing"]
public theorem isZero_Hgroup_kernel_unit_and_surjective_of_isAmple_sub
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of ℂ)) (hproj : IsProjectiveMorphism sX)
    {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hB : IsLcPair sX n K B) (hBeff : B.IsEffective)
    (W : Closeds X) (S : Set (IrreducibleCloseds X))
    (hS : ∀ Z ∈ S, ∃ E : DivisorOver ℂ sX, E.center = Z ∧ IsDiscrepancy sX n K B E (-1))
    (hW : (W : Set X) = ⋃ Z ∈ S, (Z : Set X))
    {M : Divisor X} (hM : M.IsCartier)
    (hamp : (Divisor.toQDivisor M - (Divisor.toQDivisor K + B)).IsAmple) :
    let ι := (Scheme.IdealSheafData.vanishingIdeal W).subschemeι
    let η := (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app M.divisorialSheaf
    (∀ i : ℕ, 0 < i → IsZero (Hgroup X.ringCatSheaf ⊤ i (kernel η))) ∧
      (∀ i : ℕ, 0 < i →
        IsZero (Hgroup (Scheme.IdealSheafData.vanishingIdeal W).subscheme.ringCatSheaf ⊤ i
          ((Scheme.Modules.pullback ι).obj M.divisorialSheaf))) ∧
      Function.Surjective (η.val.app (op ⊤)) := by
  intro ι η
  have hker := LcCentreUnionExtension.isZero_Hgroup_kernel_unit sX hproj hB hBeff W S hS hW hM hamp
  have hL : ∀ i : ℕ, 0 < i → IsZero (Hgroup X.ringCatSheaf ⊤ i M.divisorialSheaf) := fun i hi =>
    (LcCentreUnionExtension.isZero_Hgroup_kernel_unit sX hproj hB hBeff ⊥ ∅ (by simp) (by simp)
      hM hamp i hi).of_iso ((Hfunctor X.ringCatSheaf ⊤ i).mapIso (@asIso _ _ _ _ _
        (LcCentreUnionExtension.isIso_kernel_ι_unit_vanishingIdeal_bot M.divisorialSheaf))).symm
  have hSE : (ShortComplex.mk (kernel.ι η) η (kernel.condition η)).ShortExact := by
    haveI := Stacks.ClosedImmersion.epi_unit_app ι M.divisorialSheaf
    exact { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel η) }
  refine ⟨hker, fun i hi => ?_, ?_⟩
  · have hqc : ((Scheme.Modules.pullback ι).obj M.divisorialSheaf).IsQuasicoherent :=
      @SheafOfModules.modulePullback_isQuasicoherent _ _ ι.toLRSHom.toShHom _
        (Divisor.isQuasicoherent_divisorialSheaf M)
    refine (MMP.Fourfold.isZero_Hgroup_pushforward_iff ι _ hqc i).1 ?_
    exact ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
      (secF X.ringCatSheaf ⊤)).scδ₁_exact hSE i).isZero_of_both_isZero (hL i hi)
        (hker (i + 1) (by omega))
  · exact MMP.Fourfold.surjective_secF_map_of_shortExact _ hSE (hker 1 one_pos)

end MMP.Mori
