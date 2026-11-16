module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.MMP.Fourfold.Preadmissible.SncStratumSectionReduction
import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStratum
import MMP.AlgebraicGeometry.MMP.Abundance.PreadmissibleCrepantBoundaryFixed
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Divisor.AlgebraicHartogsUnits
import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParametersCharZero
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.Resolution.SNCRestriction
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.RingTheory.RegularLocalRing.FiniteFreeResolution
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.MMP.Fourfold.PairSingularities
import MMP.AlgebraicGeometry.Singularities.Surface.ReducedBoundaryLc
import MMP.AlgebraicGeometry.Resolution.StratumBlowupRelativelyAmple
import MMP.AlgebraicGeometry.Singularities.CyclicQuotientDifferent
public import MMP.AlgebraicGeometry.StalkValuationRing
import MMP.AlgebraicGeometry.Normalization.IntegralScheme

/-!
# Crepant birational maps fix preadmissible restrictions on proper strata

Let `(X_i, B_i)`, `i ∈ I`, be a finite collection of normal projective rational dlt pairs of the
same dimension `n ≤ 3`. Let `m` be a sufficiently divisible even degree, and let
`W ⊆ ⊕ᵢ H⁰(X_i, m(K_{X_i} + B_i))` be the space of preadmissible section systems. Let
`σ : (X_i, B_i) ⇢ (X_j, B_j)` be a crepant birational map and `s ∈ W`. Replace the `i`-th entry
of `s` by the pull-back `σ^* s_j`. The result is again preadmissible. Moreover, any preadmissible
system with `i`-th entry `σ^* s_j` has the same residue restrictions as `s_i` on every proper
stratum of `X_i`. These are the stability and fixed-boundary hypotheses of
`MMP.Fourfold.exists_admissibleSections_generatesOn_of_finite`.

The proof resolves each component by a log resolution preserving the generic points of the lc
strata. It takes a common resolution of `X_i` and `X_j` and reduces each floor divisor
alternately along the two maps, until it reaches a stratum mapping birationally onto strata of
both. Preadmissibility identifies the two restrictions there.

## Main results

* `MMP.Fourfold.exists_preadmissibleSections_update_pluriformPullback_of_isCrepantBirationalMap`:
  stability of the preadmissible space under crepant birational identifications, and
  invariance of its proper-stratum residue restrictions.

## References

* [Kollár et al., *Flips and abundance for algebraic threefolds*][kollar1992flips]
-/

universe u

open CategoryTheory AlgebraicGeometry MMP MMP.Mori MMP.Fourfold
open scoped WithZero

namespace Proof_lem_fourfold_preadmissible_stratum_restrictions_fixed

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

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

open MMP.Threefold.Mori.Helpers in
/-- **Hartogs bound for log pluricanonical forms.** Let `(X, B)` be a pair with canonical divisor
`K`, `m > 0` with `m(K + B)` Cartier, and `τ ≠ 0` in `H⁰(X, m(K + B))`. For every divisor `D` over
`X` there is a local generator `τ₀` of `𝒪_X(m(K + B))` at the centre of `D` computing the
discrepancy `a(D, X, B) = ord_D(τ₀) / m`, and `ord_D(τ₀) ≤ ord_D(τ)`. -/
private theorem exists_isDiscrepancy_ordPullback_le {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {n : ℕ} {B : QDivisor X}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {m : ℕ} (hm : 0 < m)
    (hmD : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) (D : DivisorOver k sX)
    {τ : RationalPluriForms sX n m} (hτ : τ ∈ logPluricanonicalSections sX n m B)
    (hτne : τ ≠ 0) :
    ∃ τ0 : RationalPluriForms sX n m, IsDiscrepancy sX n K B D ((D.ordPullback τ0 : ℚ) / m) ∧
      D.ordPullback τ0 ≤ D.ordPullback τ := by
  classical
  have hn := hK.topologicalKrullDim_eq
  have hP : MMP.Mori.IsPair sX B := ⟨hX, n, K, hK, ⟨m, by exact_mod_cast hm.ne', hmD⟩⟩
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  set x := D.f D.E.genericPoint
  obtain ⟨⟨D₀, hD₀⟩, U, hxU, τ0, hτ0⟩ := MMP.Positivity.IsPair.exists_generatesOn hP hK hmD x
  have hdisc : IsDiscrepancy sX n K B D ((D.ordPullback τ0 : ℚ) / m) :=
    ⟨hX, hK, m, hm, hmD, U, hxU, τ0, hτ0, by field_simp⟩
  refine ⟨τ0, hdisc, ?_⟩
  let A := functionFieldAlgebra sX
  obtain ⟨bas, N, hN⟩ := D.exists_ordPullback_eq hX hn
  set cτ := (ZTensorPower.basis bas m).repr τ () with hcτ
  set c0 := (ZTensorPower.basis bas m).repr τ0 () with hc0
  have hcτ0 : cτ ≠ 0 := repr_ne_zero_of_ne_zero bas hτne
  have hc00 : c0 ≠ 0 := repr_ne_zero_of_ne_zero bas hτ0.1
  set g := cτ / c0 with hg
  have hg0 : g ≠ 0 := div_ne_zero hcτ0 hc00
  have hcτg : cτ = g * c0 := by rw [hg, div_mul_cancel₀ _ hc00]
  have hY : D.ordPullback τ =
      D.Y.ord (functionFieldMap D.f g) D.E.genericPoint + D.ordPullback τ0 := by
    rw [hN m τ hτne, hN m τ0 hτ0.1, ← hcτ, ← hc0, hcτg, map_mul,
      Scheme.ord_mul ((map_ne_zero _).mpr hg0) ((map_ne_zero _).mpr hc00)]
    ring
  have hXg : ∀ Γ' : MMP.Mori.PrimeDivisor X,
      Γ'.ordForm τ = X.ord g Γ'.genericPoint + Γ'.ordForm τ0 := by
    intro Γ'
    obtain ⟨N', hN'⟩ := Γ'.exists_ordForm_eq_ord_add_mul hd bas
    rw [hN' m τ hτne, hN' m τ0 hτ0.1, ← hcτ, ← hc0, hcτg, Scheme.ord_mul hg0 hc00]
    ring
  rw [mem_logPluricanonicalSections, mem_pluricanonicalSections_of_ne_bot top_ne_bot] at hτ
  have hgx : ∀ Γ' : MMP.Mori.PrimeDivisor X, x ∈ Γ'.support → 0 ≤ X.ord g Γ'.genericPoint := by
    intro Γ' hxΓ'
    have h1 := hτ Γ' ⟨x, hxΓ', trivial⟩ hτne
    have h2 := hτ0.2 Γ' ⟨x, hxΓ', hxU⟩
    have hD₀c : ((D₀.coeff Γ' : ℤ) : ℚ) = m * B.coeff Γ' := by
      have := congrArg (fun D : QDivisor X => D.coeff Γ') hD₀
      simpa using this
    have e1 : DivisorWithCoeffs.coeff (DivisorWithCoeffs.roundDown ((m : ℤ) • B)) Γ' =
        D₀.coeff Γ' := by
      rw [DivisorWithCoeffs.coeff_roundDown]
      have e : DivisorWithCoeffs.coeff ((m : ℤ) • B) Γ' = ((D₀.coeff Γ' : ℤ) : ℚ) := by
        rw [← hD₀]; simp
      rw [e, Int.floor_intCast]
    rw [e1] at h1
    rw [← hD₀c] at h2
    have h3 : Γ'.ordForm τ0 = -D₀.coeff Γ' :=
      by exact_mod_cast (by push_cast; linarith : (Γ'.ordForm τ0 : ℚ) = ((-D₀.coeff Γ' : ℤ) : ℚ))
    rw [hXg Γ', h3] at h1
    linarith
  obtain ⟨r, hr⟩ := exists_algebraMap_stalk_eq_of_forall_ord_nonneg _ hg0 hgx
  have hG := ord_functionFieldMap_nonneg D hg0 r hr
  linarith

/-- **Sections against a divisor of known discrepancy.** If `D` is a divisor over `X` with
discrepancy `a(D, X, B) = -c` and `m(K + B)` is Cartier, then every `τ ≠ 0` in
`H⁰(X, m(K + B))` has `ord_D(τ) + ⌊mc⌋ ≥ 0`. -/
private theorem ordPullback_add_floor_nonneg {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {n : ℕ} {B : QDivisor X}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {m : ℕ} (hm : 0 < m)
    (hmD : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) (D : DivisorOver k sX)
    {τ : RationalPluriForms sX n m} (hτ : τ ∈ logPluricanonicalSections sX n m B)
    (hτne : τ ≠ 0) {c : ℚ} (hc : IsDiscrepancy sX n K B D (-c)) :
    0 ≤ D.ordPullback τ + ⌊((m : ℤ) • c : ℚ)⌋ := by
  obtain ⟨τ0, hdisc, hle⟩ := exists_isDiscrepancy_ordPullback_le hX hK hm hmD D hτ hτne
  have he := hc.eq hdisc
  rw [eq_div_iff (by positivity)] at he
  have h5 : -(D.ordPullback τ : ℤ) ≤ ⌊((m : ℤ) • c : ℚ)⌋ := by
    rw [Int.le_floor, zsmul_eq_mul]
    push_cast
    have : (D.ordPullback τ0 : ℚ) ≤ D.ordPullback τ := by exact_mod_cast hle
    linarith
  linarith

/-- **Crepant birational maps carry log pluricanonical sections to log pluricanonical
sections.** Let `σ : (X, B) ⇢ (X', B')` be a crepant birational map of pairs, with canonical
divisors `K`, `K'` of the same dimension `n`, and `m > 0` with `m(K + B)` and `m(K' + B')`
Cartier. Then `σ^*` carries `H⁰(X', m(K' + B'))` into `H⁰(X, m(K + B))`. -/
private theorem pluriformPullback_mem_logPluricanonicalSections_of_isCrepantBirationalMap
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X X' : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (hX' : IsNormalVariety k sX') {n : ℕ} {B : QDivisor X} {B' : QDivisor X'}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {K' : Divisor X'}
    (hK' : K'.IsCanonicalDivisor sX' n) {m : ℕ} (hm : 0 < m)
    (hmD : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor)
    (hmD' : ((m : ℤ) • (Divisor.toQDivisor K' + B')).IsCartierDivisor)
    {σ : FunctionFieldEquiv sX sX'} (hσ : IsCrepantBirationalMap sX sX' B B' σ)
    {τ : RationalPluriForms sX' n m} (hτ : τ ∈ logPluricanonicalSections sX' n m B') :
    pluriformPullback sX sX' σ.toHom n m τ ∈ logPluricanonicalSections sX n m B := by
  classical
  have hn := hK.topologicalKrullDim_eq
  have hn' := hK'.topologicalKrullDim_eq
  have hP : MMP.Mori.IsPair sX B := ⟨hX, n, K, hK, ⟨m, by exact_mod_cast hm.ne', hmD⟩⟩
  have hP' : MMP.Mori.IsPair sX' B' := ⟨hX', n, K', hK', ⟨m, by exact_mod_cast hm.ne', hmD'⟩⟩
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  by_cases hτne : τ = 0
  · rw [hτne, map_zero]; exact zero_mem _
  rw [mem_logPluricanonicalSections, mem_pluricanonicalSections_of_ne_bot top_ne_bot]
  intro Γ _ _
  set DΓ := DivisorOver.ofPrimeDivisor k hX Γ
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK DΓ
  have hc' : c = -B.coeff Γ := hc.eq_neg_coeff_of_ofPrimeDivisor hX
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
    (show IsProper (𝟙 X) by infer_instance)
  obtain ⟨n', D, hDv, hDlog⟩ := (hσ DΓ.valuation (1 + c)).mp ⟨n, DΓ, rfl, hlog⟩
  have hnn : n' = n := by
    have := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hDlog).symm.trans hn'
    exact_mod_cast this
  rw [hnn] at hDlog
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have hv : ∀ g : X'.functionField, D.valuation g = Γ.divisorialValuation ((σ.toHom) g) := by
    intro g
    rw [hDv]
    change Γ.divisorialValuation (functionFieldMap (𝟙 X) _) = _
    rw [functionFieldMap_id_apply]
    rfl
  rw [ordForm_pluriformPullback_eq_ordPullback hX hX' hn hn' σ Γ D hv τ,
    DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul]
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP' hK' D
  have h1 := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha hDlog
  have hac : a = -B.coeff Γ := by rw [← hc']; exact_mod_cast (by linarith : (a : ℝ) = c)
  exact ordPullback_add_floor_nonneg hX' hK' hm hmD' D hτ hτne (hac ▸ ha)

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

/-- A `k`-isomorphism `σ : k(X') ≅ k(X)` carrying the valuation of a prime divisor `P` of `X` to
that of a prime divisor `P'` of `X'` restricts to an isomorphism `𝒪_{X',P'} ≅ 𝒪_{X,P}` which
preserves orders. -/
private theorem exists_stalk_ringEquiv_of_divisorialValuation_eq {k : Type u} [Field k]
    {X X' : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} (σ : FunctionFieldEquiv sX sX')
    (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor X')
    (hP' : ∀ g, P'.divisorialValuation g = P.divisorialValuation ((σ.toHom) g)) {x : X} {x' : X'}
    (hx : x = P.genericPoint) (hx' : x' = P'.genericPoint) :
    ∃ ψ : X'.presheaf.stalk x' ≃+* X.presheaf.stalk x,
      (∀ a, algebraMap _ X.functionField (ψ a) = (σ.toHom) (algebraMap _ X'.functionField a)) ∧
      ∀ a, X.ord (algebraMap _ X.functionField (ψ a)) x =
        X'.ord (algebraMap _ X'.functionField a) x' := by
  subst hx hx'
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let φ : X'.functionField →+* X.functionField := (σ.toHom).toRingHom
  have h12 : ∀ a1 : P'.localRing, ∃ a2 : P.localRing,
      algebraMap P.localRing X.functionField a2 = φ (algebraMap P'.localRing X'.functionField a1) := by
    intro a1
    have : P'.divisorialValuation (algebraMap P'.localRing X'.functionField a1) ≤ 1 :=
      (P'.divisorialValuation_le_one_iff _).mpr ⟨a1, rfl⟩
    rw [hP'] at this
    obtain ⟨a2, ha2⟩ := (P.divisorialValuation_le_one_iff _).mp this
    exact ⟨a2, by rw [ha2]; rfl⟩
  have h21 : ∀ a2 : P.localRing, ∃ a1 : P'.localRing,
      φ (algebraMap P'.localRing X'.functionField a1) = algebraMap P.localRing X.functionField a2 := by
    intro a2
    obtain ⟨y, hy⟩ := σ.surjective (algebraMap P.localRing X.functionField a2)
    have : P'.divisorialValuation y ≤ 1 := by
      rw [hP']
      change P.divisorialValuation (σ y) ≤ 1
      rw [hy]
      exact (P.divisorialValuation_le_one_iff _).mpr ⟨a2, rfl⟩
    obtain ⟨a1, ha1⟩ := (P'.divisorialValuation_le_one_iff _).mp this
    exact ⟨a1, by change σ _ = _; rw [ha1]; exact hy⟩
  obtain ⟨ψ, hψb, hψ⟩ :=
    MMP.Threefold.Mori.ModelIndependence.exists_ringHom_bijective_of_range φ h12 h21
  refine ⟨RingEquiv.ofBijective ψ hψb, fun a => hψ a, fun a => ?_⟩
  change X.ord (algebraMap _ X.functionField (ψ a)) _ = _
  rw [hψ]
  set y := algebraMap P'.localRing X'.functionField a
  by_cases hy : y = 0
  · rw [hy, map_zero]; simp [Scheme.ord_zero]
  · have hey : φ y ≠ 0 := (map_ne_zero φ).mpr hy
    have h1 : P'.divisorialValuation y = P.divisorialValuation (φ y) := hP' y
    rw [P.divisorialValuation_eq_exp_neg_ord hey, P'.divisorialValuation_eq_exp_neg_ord hy,
      WithZero.exp_inj] at h1
    change X.ord (φ y) _ = _
    omega

/-- An isomorphism `ψ : 𝒪_{X',T'} ≅ 𝒪_{X,T}` of the local rings along two adjunction strata,
compatible with a `k`-isomorphism `σ : k(X') ≅ k(X)`, induces a `k`-isomorphism of residue fields
`σ_T : k(T') ≅ k(T)` with `σ_T(a|_{T'}) = ψ(a)|_T`. -/
private theorem exists_functionFieldEquiv_of_stalk_ringEquiv {k : Type u} [Field k]
    {X X' T T' : Scheme.{u}} [IsIntegral X] [IsIntegral X'] [IsIntegral T] [IsIntegral T']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} (σ : FunctionFieldEquiv sX sX')
    {j : T ⟶ X} {j' : T' ⟶ X'} {BX : QDivisor X} {BX' : QDivisor X'} {BT : QDivisor T}
    {BT' : QDivisor T'} [IsLocallyNoetherian X] [IsLocallyNoetherian X'] [IsNormal X] [IsNormal X']
    (hj : IsAdjunctionStep sX BX j BT) (hj' : IsAdjunctionStep sX' BX' j' BT')
    (ψ : X'.presheaf.stalk (j' (genericPoint T')) ≃+* X.presheaf.stalk (j (genericPoint T)))
    (hψ : ∀ a, algebraMap _ X.functionField (ψ a) = (σ.toHom) (algebraMap _ X'.functionField a)) :
    ∃ σT : FunctionFieldEquiv (j ≫ sX) (j' ≫ sX'), ∀ a,
      (σT.toHom) ((j'.stalkMap (genericPoint T')).hom a) =
        (j.stalkMap (genericPoint T)).hom (ψ a) := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (j' ≫ sX')
  let := functionFieldAlgebra (j ≫ sX)
  let := stalkAlgebra sX (j (genericPoint T))
  let := stalkAlgebra sX' (j' (genericPoint T'))
  have := isScalarTower_stalk_functionField sX (j (genericPoint T))
  have := isScalarTower_stalk_functionField sX' (j' (genericPoint T'))
  obtain ⟨htow, hsurj⟩ := hj.stalkMap_facts
  obtain ⟨htow', hsurj'⟩ := hj'.stalkMap_facts
  set f' := (j'.stalkMap (genericPoint T')).hom
  set g := (j.stalkMap (genericPoint T)).hom
  have hgψ : Function.Surjective (g.comp ψ.toRingHom) := hsurj.comp ψ.surjective
  have hker : RingHom.ker f' = RingHom.ker (g.comp ψ.toRingHom) := by
    have h1 := IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj')
    have h2 := IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hgψ)
    exact h1.trans h2.symm
  have hIJ : RingHom.ker g = (RingHom.ker f').map ψ := by
    rw [hker, ← RingHom.comap_ker]
    exact (Ideal.map_comap_of_surjective ψ ψ.surjective _).symm
  let e : T'.functionField ≃+* T.functionField :=
    ((RingHom.quotientKerEquivOfSurjective hsurj').symm.trans
      (Ideal.quotientEquiv _ _ ψ hIJ)).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have he : ∀ a, e (f' a) = g (ψ a) := by
    intro a
    have : (RingHom.quotientKerEquivOfSurjective hsurj').symm (f' a) = Ideal.Quotient.mk _ a := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [e, RingEquiv.trans_apply, this]
    rfl
  have hψk : ∀ c : k, ψ (algebraMap k _ c) = algebraMap k _ c := by
    intro c
    apply IsFractionRing.injective (X.presheaf.stalk (j (genericPoint T))) X.functionField
    rw [hψ, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact (σ.toHom).commutes c
  refine ⟨AlgEquiv.ofRingEquiv (f := e) fun c => ?_, fun a => he a⟩
  letI : Algebra (X'.presheaf.stalk (j' (genericPoint T'))) T'.functionField := f'.toAlgebra
  letI : Algebra (X.presheaf.stalk (j (genericPoint T))) T.functionField := g.toAlgebra
  have h1 : algebraMap k T'.functionField c = f' (algebraMap k _ c) :=
    IsScalarTower.algebraMap_apply k (X'.presheaf.stalk (j' (genericPoint T'))) T'.functionField c
  have h2 : algebraMap k T.functionField c = g (algebraMap k _ c) :=
    IsScalarTower.algebraMap_apply k (X.presheaf.stalk (j (genericPoint T))) T.functionField c
  rw [h1, he, hψk, h2]

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

section ToricUniformizer

open Polynomial IsLocalRing

/-- In a local ring, a unit plus an element of the maximal ideal is a unit. -/
private theorem isUnit_add_of_mem_maximalIdeal {O : Type*} [CommRing O] [IsLocalRing O] {a b : O}
    (ha : IsUnit a) (hb : b ∈ maximalIdeal O) : IsUnit (a + b) := by
  by_contra h
  have h1 : a + b ∈ maximalIdeal O := (mem_maximalIdeal _).2 h
  have : a ∈ maximalIdeal O := by simpa using (maximalIdeal O).sub_mem h1 hb
  exact (mem_maximalIdeal _).1 this ha

/-- Let `u` lie in the maximal ideal of a local ring `𝒪` and `φ : S → 𝒪` send nonzero elements to
units. A nonzero polynomial `P` over `S` has `P(u) = u^a e` with `e ≡ φ(c)` modulo `𝔪` for some
`c ≠ 0`; in particular `e` is a unit. -/
private theorem eval₂_eq_pow_mul_isUnit {S O : Type*} [CommRing S] [CommRing O] [IsLocalRing O]
    (φ : S →+* O) (hφ : ∀ c, c ≠ 0 → IsUnit (φ c)) (u : O) (hu : u ∈ maximalIdeal O)
    (P : S[X]) (hP : P ≠ 0) : ∃ (a : ℕ) (e : O) (c : S), c ≠ 0 ∧ IsUnit e ∧
      e - φ c ∈ maximalIdeal O ∧ P.eval₂ φ u = u ^ a * e := by
  obtain ⟨P', hP', hdvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP 0
  rw [map_zero, sub_zero, Polynomial.X_dvd_iff] at hdvd
  have hdec : P'.eval₂ φ u = φ (P'.coeff 0) + u * (P'.divX).eval₂ φ u := by
    conv_lhs => rw [← Polynomial.divX_mul_X_add P']
    rw [eval₂_add, eval₂_C, eval₂_mul, eval₂_X, add_comm, mul_comm u]
  refine ⟨P.rootMultiplicity 0, P'.eval₂ φ u, P'.coeff 0, hdvd, ?_, ?_, ?_⟩
  · rw [hdec]
    exact isUnit_add_of_mem_maximalIdeal (hφ _ hdvd) (Ideal.mul_mem_right _ _ hu)
  · rw [hdec, add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ hu
  · conv_lhs => rw [hP']
    rw [eval₂_mul, map_zero, sub_zero, eval₂_X_pow]

/-- **A generator in the maximal ideal is a uniformizer.** Let `𝒪` be a discrete valuation ring
and `u ∈ 𝔪` nonzero, and let `φ : S → 𝒪` send nonzero elements to units. If every element of `𝒪`
times some nonzero `Q(u)` is some `P(u)`, for polynomials `P, Q` over `S`, then `u` is a
uniformizer. -/
private theorem irreducible_of_forall_mul_eval₂_eq {S O : Type*} [CommRing S] [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (φ : S →+* O) (hφ : ∀ c, c ≠ 0 → IsUnit (φ c))
    (u : O) (hu : u ∈ maximalIdeal O) (hu0 : u ≠ 0)
    (hgen : ∀ x : O, ∃ P Q : S[X], Q.eval₂ φ u ≠ 0 ∧ x * Q.eval₂ φ u = P.eval₂ φ u) :
    Irreducible u := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨d, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hu0 hϖ
  obtain ⟨P, Q, hQ0, hPQ⟩ := hgen ϖ
  have hP0 : P ≠ 0 := by
    rintro rfl
    rw [eval₂_zero] at hPQ
    exact hQ0 ((mul_eq_zero.1 hPQ).resolve_left hϖ.ne_zero)
  have hQ0' : Q ≠ 0 := by rintro rfl; exact hQ0 (eval₂_zero _ _)
  obtain ⟨a, e, -, -, he, -, hPe⟩ := eval₂_eq_pow_mul_isUnit φ hφ u hu P hP0
  obtain ⟨b, e', -, -, he', -, hQe⟩ := eval₂_eq_pow_mul_isUnit φ hφ u hu Q hQ0'
  rw [hPe, hQe, hv] at hPQ
  have key : (↑(v ^ b * he'.unit) : O) * ϖ ^ (1 + d * b) = ↑(v ^ a * he.unit) * ϖ ^ (d * a) := by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    calc _ = ϖ * ((v * ϖ ^ d) ^ b * e') := by ring
      _ = (v * ϖ ^ d) ^ a * e := hPQ
      _ = _ := by ring
  have h1 := IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ _ _ _ _ key
  have hd : d = 1 := by
    have : d ∣ 1 := ⟨a - b, by
      rcases Nat.lt_or_ge a b with h | h
      · nlinarith [Nat.mul_le_mul_left d h.le]
      · rw [Nat.mul_sub, ← h1]; omega⟩
    exact Nat.dvd_one.1 this
  rw [hv, hd, pow_one]
  exact (irreducible_isUnit_mul v.isUnit).2 hϖ

/-- **Residues of units are ratios of coefficient images.** In the setting of
`irreducible_of_forall_mul_eval₂_eq`, every unit `x` of `𝒪` is congruent modulo `𝔪` to
`φ(c₁) φ(c₂)⁻¹` for some `c₁, c₂ ∈ S` with `c₂ ≠ 0`. -/
private theorem exists_mul_sub_mem_maximalIdeal_of_isUnit {S O : Type*} [CommRing S] [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (φ : S →+* O) (hφ : ∀ c, c ≠ 0 → IsUnit (φ c))
    (u : O) (hu : u ∈ maximalIdeal O) (hu0 : u ≠ 0)
    (hgen : ∀ x : O, ∃ P Q : S[X], Q.eval₂ φ u ≠ 0 ∧ x * Q.eval₂ φ u = P.eval₂ φ u)
    (x : O) (hx : IsUnit x) :
    ∃ c₁ c₂ : S, c₂ ≠ 0 ∧ x * φ c₂ - φ c₁ ∈ maximalIdeal O := by
  have hirr := irreducible_of_forall_mul_eval₂_eq φ hφ u hu hu0 hgen
  obtain ⟨P, Q, hQ0, hPQ⟩ := hgen x
  have hP0 : P ≠ 0 := by
    rintro rfl
    rw [eval₂_zero] at hPQ
    exact hQ0 ((mul_eq_zero.1 hPQ).resolve_left hx.ne_zero)
  have hQ0' : Q ≠ 0 := by rintro rfl; exact hQ0 (eval₂_zero _ _)
  obtain ⟨a, e, c₁, -, he, hc₁, hPe⟩ := eval₂_eq_pow_mul_isUnit φ hφ u hu P hP0
  obtain ⟨b, e', c₂, hc₂0, he', hc₂, hQe⟩ := eval₂_eq_pow_mul_isUnit φ hφ u hu Q hQ0'
  rw [hPe, hQe] at hPQ
  have key : (↑(hx.unit * he'.unit) : O) * u ^ b = ↑he.unit * u ^ a := by
    simp only [Units.val_mul, IsUnit.unit_spec]
    calc x * e' * u ^ b = x * (u ^ b * e') := by ring
      _ = u ^ a * e := hPQ
      _ = e * u ^ a := by ring
  have hab := IsDiscreteValuationRing.unit_mul_pow_congr_pow hirr hirr _ _ _ _ key
  subst hab
  have hxe : x * e' = e := by
    have := hPQ
    rw [show x * (u ^ b * e') = u ^ b * (x * e') by ring] at this
    exact mul_left_cancel₀ (pow_ne_zero _ hu0) this
  refine ⟨c₁, c₂, hc₂0, ?_⟩
  have : x * φ c₂ - φ c₁ = (e - φ c₁) - x * (e' - φ c₂) := by rw [← hxe]; ring
  rw [this]
  exact (maximalIdeal O).sub_mem hc₁ (Ideal.mul_mem_left _ _ hc₂)

/-- Let `φ : S → 𝒪` be a ring homomorphism whose image contains `k` and `w`. Every element of the
`k`-subalgebra generated by `u, w` is `P(u)` for a polynomial `P` over `S`. -/
private theorem exists_eval₂_eq_of_mem_adjoin_pair {k S O : Type*} [Field k] [CommRing S]
    [CommRing O] [Algebra k O] (φ : S →+* O) (hk : ∀ c : k, ∃ s, φ s = algebraMap k O c)
    (u w : O) (hw : ∃ s, φ s = w) {x : O} (hx : x ∈ Algebra.adjoin k ({u, w} : Set O)) :
    ∃ P : S[X], P.eval₂ φ u = x := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact ⟨X, by simp⟩
    · obtain ⟨s, hs⟩ := hw; exact ⟨C s, by simp [hs]⟩
  | algebraMap c => obtain ⟨s, hs⟩ := hk c; exact ⟨C s, by simp [hs]⟩
  | add a b _ _ ha hb =>
    obtain ⟨P, rfl⟩ := ha; obtain ⟨Q, rfl⟩ := hb; exact ⟨P + Q, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨P, rfl⟩ := ha; obtain ⟨Q, rfl⟩ := hb; exact ⟨P * Q, by simp⟩

/-- If the fraction field of a domain `𝒪` is generated over `k` by `u, w ∈ 𝒪`, and `φ : S → 𝒪`
has `k` and `w` in its image, then every `x ∈ 𝒪` satisfies `x Q(u) = P(u)` for polynomials
`P, Q` over `S` with `Q(u) ≠ 0`. -/
private theorem forall_exists_mul_eval₂_eq_of_adjoin_pair_eq_top {k S O K : Type*} [Field k]
    [CommRing S] [CommRing O] [IsDomain O] [Algebra k O] [Field K] [Algebra O K]
    [IsFractionRing O K] [Algebra k K] [IsScalarTower k O K] (φ : S →+* O)
    (hk : ∀ c : k, ∃ s, φ s = algebraMap k O c) (u w : O) (hw : ∃ s, φ s = w)
    (htop : IntermediateField.adjoin k ({algebraMap O K u, algebraMap O K w} : Set K) = ⊤)
    (x : O) : ∃ P Q : S[X], Q.eval₂ φ u ≠ 0 ∧ x * Q.eval₂ φ u = P.eval₂ φ u := by
  have hx : algebraMap O K x ∈
      IntermediateField.adjoin k ({algebraMap O K u, algebraMap O K w} : Set K) :=
    htop ▸ IntermediateField.mem_top
  obtain ⟨r, hr, s, hs, hrs⟩ := IntermediateField.mem_adjoin_iff_div.1 hx
  have himg : ({algebraMap O K u, algebraMap O K w} : Set K) =
      (IsScalarTower.toAlgHom k O K) '' ({u, w} : Set O) := by
    simp [Set.image_insert_eq, Set.image_singleton]
  rw [himg, ← AlgHom.map_adjoin] at hr hs
  obtain ⟨r0, hr0, rfl⟩ := hr
  obtain ⟨s0, hs0, rfl⟩ := hs
  obtain ⟨P, hP⟩ := exists_eval₂_eq_of_mem_adjoin_pair φ hk u w hw hr0
  obtain ⟨Q, hQ⟩ := exists_eval₂_eq_of_mem_adjoin_pair φ hk u w hw hs0
  have hinj := IsFractionRing.injective O K
  replace hrs : algebraMap O K x = algebraMap O K r0 / algebraMap O K s0 := hrs
  by_cases hs00 : s0 = 0
  · subst hs00
    have hx0 : x = 0 := hinj (by simpa using hrs)
    exact ⟨0, 1, by simp, by simp [hx0]⟩
  refine ⟨P, Q, hQ ▸ hs00, ?_⟩
  rw [hP, hQ]
  apply hinj
  have hs' : algebraMap O K s0 ≠ 0 := (map_ne_zero_iff _ hinj).2 hs00
  rw [map_mul, hrs, div_mul_cancel₀ _ hs']

/-- **Unimodular reduction in rank two.** Every `(x, y) ∈ ℤ²` is carried to `(gcd(x, y), 0)` by
an integer matrix of determinant one. -/
private theorem exists_det_eq_one_mulVec_eq (x y : ℤ) :
    ∃ M : Matrix (Fin 2) (Fin 2) ℤ, M.det = 1 ∧
      M.mulVec ![x, y] = ![(Int.gcd x y : ℤ), 0] := by
  by_cases h0 : Int.gcd x y = 0
  · have h1 : x = 0 := Int.gcd_eq_zero_iff.1 h0 |>.1
    have h2 : y = 0 := Int.gcd_eq_zero_iff.1 h0 |>.2
    refine ⟨1, by simp, ?_⟩
    rw [Matrix.one_mulVec, h0, h1, h2]
    ext i; fin_cases i <;> simp
  have hd : ((Int.gcd x y : ℕ) : ℤ) ≠ 0 := by exact_mod_cast h0
  obtain ⟨p, hp⟩ : ((Int.gcd x y : ℕ) : ℤ) ∣ x := Int.gcd_dvd_left ..
  obtain ⟨q, hq⟩ : ((Int.gcd x y : ℕ) : ℤ) ∣ y := Int.gcd_dvd_right ..
  have hb := Int.gcd_eq_gcd_ab x y
  generalize ((Int.gcd x y : ℕ) : ℤ) = g at hd hp hq hb ⊢
  generalize Int.gcdA x y = a at hb ⊢
  generalize Int.gcdB x y = b at hb ⊢
  subst hp hq
  refine ⟨!![a, b; -q, p], ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    apply mul_left_cancel₀ hd
    linear_combination -hb
  · ext i; fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; linear_combination -hb
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring

/-- **Unimodular completion in rank three.** A primitive vector `(a, b, c) ∈ ℤ³` is carried to
`(1, 0, 0)` by an integer matrix of determinant one. -/
private theorem exists_det_eq_one_mulVec_eq_three (a b c : ℤ)
    (h : Int.gcd a (Int.gcd b c : ℤ) = 1) :
    ∃ M : Matrix (Fin 3) (Fin 3) ℤ, M.det = 1 ∧ M.mulVec ![a, b, c] = ![1, 0, 0] := by
  obtain ⟨N, hN, hNv⟩ := exists_det_eq_one_mulVec_eq b c
  obtain ⟨N', hN', hN'v⟩ := exists_det_eq_one_mulVec_eq a (Int.gcd b c)
  rw [h] at hN'v
  have e1 : N 0 0 * b + N 0 1 * c = Int.gcd b c := by
    have := congrFun hNv 0; simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e2 : N 1 0 * b + N 1 1 * c = 0 := by
    have := congrFun hNv 1; simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e3 : N' 0 0 * a + N' 0 1 * (Int.gcd b c : ℤ) = 1 := by
    have := congrFun hN'v 0; simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e4 : N' 1 0 * a + N' 1 1 * (Int.gcd b c : ℤ) = 0 := by
    have := congrFun hN'v 1; simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  rw [Matrix.det_fin_two] at hN hN'
  let A : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, N 0 0, N 0 1; 0, N 1 0, N 1 1]
  let B : Matrix (Fin 3) (Fin 3) ℤ := !![N' 0 0, N' 0 1, 0; N' 1 0, N' 1 1, 0; 0, 0, 1]
  refine ⟨B * A, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_fin_three, Matrix.det_fin_three]
    simp [A, B]
    linear_combination (N 0 0 * N 1 1 - N 0 1 * N 1 0) * hN' + hN
  · rw [← Matrix.mulVec_mulVec]
    ext i; fin_cases i
    · simp [A, B, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      linear_combination N' 0 1 * e1 + e3
    · simp [A, B, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      linear_combination N' 1 1 * e1 + e4
    · simp [A, B, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      linear_combination e2

/-- `∏ gᶠ⁽ⁱ⁾ = g^{∑ f(i)}` in a commutative group. -/
private theorem prod_zpow_eq_zpow_sum' {G : Type*} [CommGroup G] {ι : Type*} (s : Finset ι)
    (g : G) (f : ι → ℤ) : ∏ i ∈ s, g ^ f i = g ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

/-- **Monomial change of coordinates.** If `M` is an invertible integer matrix and
`s_a = ∏_b z_b^{M_{ab}}`, every Laurent monomial `z^u` is the monomial `s^{u M⁻¹}`. -/
private theorem prod_zpow_eq_prod_monomial_zpow {G : Type*} [CommGroup G] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (z : ι → G) (M : Matrix ι ι ℤ) (hM : IsUnit M.det)
    (u : ι → ℤ) :
    ∏ b, z b ^ u b = ∏ a, (∏ b, z b ^ M a b) ^ (Matrix.vecMul u M⁻¹) a := by
  have hc : Matrix.vecMul (Matrix.vecMul u M⁻¹) M = u := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hM, Matrix.vecMul_one]
  conv_lhs => rw [← hc]
  simp only [← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [prod_zpow_eq_zpow_sum']
  congr 1
  simp only [Matrix.vecMul, dotProduct]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- **Discrete valuations of a rational function field in two generators.** Let `𝒪` be a
discrete valuation ring over `k` whose fraction field is generated over `k` by `u, w ∈ 𝒪`, with
`u ∈ 𝔪` nonzero and `w` such that `p(w)` is a unit for every nonzero `p ∈ k[X]` (the residue
of `w` is transcendental over `k`). Then `u` is a uniformizer, and every unit of `𝒪` is congruent
modulo `𝔪` to `p(w) q(w)⁻¹` with `p, q ∈ k[w]`, `q ≠ 0`. -/
private theorem irreducible_and_residue_of_adjoin_pair_eq_top {k O K : Type*} [Field k]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra k O] [Field K] [Algebra O K]
    [IsFractionRing O K] [Algebra k K] [IsScalarTower k O K] (u w : O)
    (hu : u ∈ maximalIdeal O) (hu0 : u ≠ 0)
    (hw : ∀ p : k[X], p ≠ 0 → IsUnit ((aeval w).toRingHom p))
    (htop : IntermediateField.adjoin k ({algebraMap O K u, algebraMap O K w} : Set K) = ⊤) :
    Irreducible u ∧ ∀ x : O, IsUnit x →
      ∃ p q : k[X], q ≠ 0 ∧ x * (aeval w).toRingHom q - (aeval w).toRingHom p ∈ maximalIdeal O := by
  have hk : ∀ c : k, ∃ s : k[X], (aeval w).toRingHom s = algebraMap k O c :=
    fun c => ⟨C c, by simp⟩
  have hw' : ∃ s : k[X], (aeval w).toRingHom s = w := ⟨X, by simp⟩
  have hgen := forall_exists_mul_eval₂_eq_of_adjoin_pair_eq_top (K := K) (S := k[X])
    (aeval w).toRingHom hk u w hw' htop
  exact ⟨irreducible_of_forall_mul_eval₂_eq (S := k[X]) _ hw u hu hu0 hgen,
    exists_mul_sub_mem_maximalIdeal_of_isUnit (S := k[X]) _ hw u hu hu0 hgen⟩

/-- Over an algebraically closed field, a unit `w` of a local `k`-algebra either has
transcendental residue (`p(w)` is a unit for every nonzero `p ∈ k[X]`) or is congruent to a
constant modulo the maximal ideal. -/
private theorem forall_isUnit_aeval_or_exists_sub_mem {k O : Type*} [Field k] [IsAlgClosed k]
    [CommRing O] [IsLocalRing O] [Algebra k O] (w : O) :
    (∀ p : k[X], p ≠ 0 → IsUnit (aeval w p)) ∨ ∃ r : k, w - algebraMap k O r ∈ maximalIdeal O := by
  by_contra h
  push Not at h
  obtain ⟨⟨p, hp0, hpu⟩, hno⟩ := h
  have hmem : aeval w p ∈ maximalIdeal O := (mem_maximalIdeal _).2 hpu
  rw [(IsAlgClosed.splits p).eq_prod_roots] at hmem
  rw [map_mul, aeval_C, map_multiset_prod, Multiset.map_map] at hmem
  have hc : IsUnit (algebraMap k O p.leadingCoeff) :=
    (isUnit_iff_ne_zero.2 (leadingCoeff_ne_zero.2 hp0)).map _
  have hP : (maximalIdeal O).IsPrime := Ideal.IsMaximal.isPrime inferInstance
  rcases hP.mem_or_mem hmem with h1 | h1
  · exact (mem_maximalIdeal _).1 h1 hc
  · obtain ⟨y, hy, hmy⟩ := (hP.multiset_prod_mem_iff_exists_mem _).1 h1
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.1 hy
    simp only [Function.comp_apply, map_sub, aeval_X, aeval_C] at hmy
    exact hno r hmy

end ToricUniformizer

section DlogResidues

/-- An alternating map applied to the rows of a matrix times a family is the determinant times
its value on the family. -/
private theorem map_sum_smul_eq_det_smul {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : M [⋀^ι]→ₗ[R] N) (A : Matrix ι ι R) (v : ι → M) :
    g (fun i => ∑ j, A i j • v j) = A.det • g v := by
  have h1 : g (fun i => ∑ j, A i j • v j) =
      ∑ r : ι → ι, (∏ i, A i (r i)) • g (fun i => v (r i)) := by
    have := g.toMultilinearMap.map_sum (fun i j => A i j • v j)
    simp only [AlternatingMap.coe_multilinearMap] at this
    rw [this]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact g.toMultilinearMap.map_smul_univ _ _
  rw [h1]
  have h2 : ∀ r : ι → ι, ¬ Function.Injective r →
      (∏ i, A i (r i)) • g (fun i => v (r i)) = 0 := by
    intro r hr
    obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.1 hr
    rw [g.map_eq_zero_of_eq (fun i => v (r i)) (i := a) (j := b) (by simp [hab]) hne, smul_zero]
  have hinj : Set.InjOn (fun σ : Equiv.Perm ι => (σ : ι → ι))
      ((Finset.univ : Finset (Equiv.Perm ι)) : Set _) :=
    fun a _ b _ h => Equiv.ext (congrFun h)
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image fun σ : Equiv.Perm ι => (σ : ι → ι)))
    (fun r _ hr => h2 r fun hi => hr (Finset.mem_image.2
      ⟨Equiv.ofBijective r hi.bijective_of_finite, Finset.mem_univ _, rfl⟩)),
    Finset.sum_image hinj, ← Matrix.det_transpose, Matrix.det_apply', Finset.sum_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [show (fun i => v (σ i)) = v ∘ σ from rfl, g.map_perm]
  simp only [Matrix.transpose_apply]
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul R, smul_smul, mul_comm]

/-- The logarithmic differential `u ↦ u⁻¹ du` of the units of a field, as a homomorphism. -/
private noncomputable def dlogHom (k K : Type*) [Field k] [Field K] [Algebra k K] :
    Kˣ →* Multiplicative (Ω[K⁄k]) where
  toFun u := Multiplicative.ofAdd (((u : K))⁻¹ • KaehlerDifferential.D k K (u : K))
  map_one' := by simp
  map_mul' u v := by
    rw [← ofAdd_add]
    congr 1
    simp only [Units.val_mul, Derivation.leibniz, mul_inv_rev, smul_add, smul_smul]
    rw [add_comm]
    have hu := u.ne_zero
    have hv := v.ne_zero
    congr 2 <;> field_simp

/-- **Logarithmic forms under a monomial change of coordinates.** For units `s₁, …, s_r` of a
field and an integer matrix `M`, the wedge of the `dlog` of the monomials `∏_b s_b^{M_{ab}}` is
`det M` times the wedge of the `dlog s_b`. -/
private theorem ιMulti_dlogHom_monomial (k K : Type*) [Field k] [Field K] [Algebra k K] {r : ℕ}
    (s : Fin r → Kˣ) (M : Matrix (Fin r) (Fin r) ℤ) :
    exteriorPower.ιMulti K r (fun a => Multiplicative.toAdd (dlogHom k K (∏ b, s b ^ M a b))) =
      ((M.det : ℤ) : K) •
        exteriorPower.ιMulti K r (fun b => Multiplicative.toAdd (dlogHom k K (s b))) := by
  have h : ∀ a, Multiplicative.toAdd (dlogHom k K (∏ b, s b ^ M a b)) =
      ∑ b, (M.map (Int.cast : ℤ → K)) a b • Multiplicative.toAdd (dlogHom k K (s b)) := by
    intro a
    rw [map_prod, toAdd_prod]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_zpow, toAdd_zpow, Matrix.map_apply, Int.cast_smul_eq_zsmul]
  simp_rw [h]
  rw [map_sum_smul_eq_det_smul]
  congr 1
  exact (RingHom.map_det (Int.castRingHom K) M).symm

/-- `(a w)^{⊗m} = a^m w^{⊗m}`. -/
private theorem formPow_smul' {k K : Type*} [Field k] [Field K] [Algebra k K] {d : ℕ}
    (a : K) (w : ⋀[K]^d Ω[K⁄k]) (m : ℕ) : formPow (a • w) m = a ^ m • formPow w m := by
  unfold formPow
  rw [show (fun _ : Fin m => a • w) = fun i => (fun _ : Fin m => a) i • (fun _ : Fin m => w) i from rfl,
    MultilinearMap.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

/-- A ring homomorphism to a field sends `(u⁻¹)^m` to `φ(u)⁻¹^m`. -/
private theorem ringHom_units_inv_pow {O K : Type*} [CommRing O] [Field K] (φ : O →+* K) (u : Oˣ)
    (m : ℕ) : φ ((u⁻¹ ^ m : Oˣ) : O) = (φ (u : O))⁻¹ ^ m := by
  rw [Units.val_pow_eq_pow_val, map_pow]
  congr 1
  exact eq_inv_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])

/-- **The residue of a logarithmic form along a divisor.** If `t` is a uniformizer of `𝒪_{Y,T}`
and `e₁, …, e_n` are units there, the `m`-th power of `dlog t ∧ dlog e₁ ∧ ⋯ ∧ dlog e_n` has
Poincaré residue the `m`-th power of `dlog ē₁ ∧ ⋯ ∧ dlog ē_n` along `T`. -/
private theorem isPoincareResidue_formPow_dlog {k : Type} [Field k] {Y T : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsIntegral T] (j : T ⟶ Y)
    {n : ℕ} (m : ℕ) (t : Y.presheaf.stalk (j (genericPoint T)))
    (e : Fin n → Y.presheaf.stalk (j (genericPoint T))) (he : ∀ i, IsUnit (e i))
    (ht : (letI := functionFieldAlgebra sY; Y.ord (algebraMap _ Y.functionField t) (j (genericPoint T))) = 1) :
    letI := functionFieldAlgebra sY
    letI := functionFieldAlgebra (j ≫ sY)
    IsPoincareResidue sY j n m
      (formPow (exteriorPower.ιMulti Y.functionField (n + 1)
        (Fin.cons ((algebraMap _ Y.functionField t)⁻¹ •
            KaehlerDifferential.D k Y.functionField (algebraMap _ _ t))
          fun i => (algebraMap _ Y.functionField (e i))⁻¹ •
            KaehlerDifferential.D k Y.functionField (algebraMap _ _ (e i)))) m)
      (formPow (exteriorPower.ιMulti T.functionField n
          fun i => ((j.stalkMap (genericPoint T)).hom (e i))⁻¹ •
            KaehlerDifferential.D k T.functionField ((j.stalkMap (genericPoint T)).hom (e i))) m) := by
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (j ≫ sY)
  set u : (Y.presheaf.stalk (j (genericPoint T)))ˣ := ∏ i, (he i).unit
  refine ⟨t, ((u⁻¹ ^ m : (Y.presheaf.stalk (j (genericPoint T)))ˣ) : _), e, ht, ?_, ?_⟩
  · have hc : (Fin.cons ((algebraMap _ Y.functionField t)⁻¹ •
            KaehlerDifferential.D k Y.functionField (algebraMap _ _ t))
          fun i => (algebraMap _ Y.functionField (e i))⁻¹ •
            KaehlerDifferential.D k Y.functionField (algebraMap _ _ (e i)) : Fin (n+1) → _) =
        fun l => (Fin.cons (algebraMap _ Y.functionField t)⁻¹
            (fun i => (algebraMap _ Y.functionField (e i))⁻¹) : Fin (n+1) → Y.functionField) l •
          (Fin.cons (KaehlerDifferential.D k Y.functionField (algebraMap _ _ t))
            fun i => KaehlerDifferential.D k Y.functionField (algebraMap _ _ (e i)) : Fin (n+1) → _) l := by
      funext l; refine Fin.cases ?_ (fun i => ?_) l <;> simp
    have hu : (algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField (u : Y.presheaf.stalk (j (genericPoint T)))) = ∏ i, algebraMap _ Y.functionField (e i) := by
      simp [u, map_prod]
    rw [hc, AlternatingMap.map_smul_univ, Fin.prod_cons, formPow_smul',
      ringHom_units_inv_pow (algebraMap _ Y.functionField), hu]
    have e1 : ∀ (a : Y.functionField) (W : ⋀[Y.functionField]^(n + 1) Ω[Y.functionField⁄k]),
        (PiTensorProduct.tprod Y.functionField fun _ : Fin m => a • W) =
          a ^ m • PiTensorProduct.tprod Y.functionField (fun _ : Fin m => W) :=
      fun a W => formPow_smul' a W m
    simp only [e1, smul_smul]
    unfold formPow
    congr 1
    rw [mul_pow, mul_comm, Finset.prod_inv_distrib]
  · have hc : (fun i => ((j.stalkMap (genericPoint T)).hom (e i))⁻¹ •
            KaehlerDifferential.D k T.functionField ((j.stalkMap (genericPoint T)).hom (e i))) =
        fun i => (fun i => ((j.stalkMap (genericPoint T)).hom (e i))⁻¹) i •
          (fun i => KaehlerDifferential.D k T.functionField ((j.stalkMap (genericPoint T)).hom (e i))) i :=
      rfl
    have hu : (j.stalkMap (genericPoint T)).hom (u : Y.presheaf.stalk (j (genericPoint T))) = ∏ i, (j.stalkMap (genericPoint T)).hom (e i) := by
      simp [u, map_prod]
    rw [hc, AlternatingMap.map_smul_univ, formPow_smul',
      ringHom_units_inv_pow (j.stalkMap (genericPoint T)).hom, hu]
    simp only [formPow, ← Finset.prod_inv_distrib]
    rfl

end DlogResidues

section DlogWedge

open IsLocalRing

private theorem alternating_fin_two_add_smul {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (g : M [⋀^Fin 2]→ₗ[R] N) (x y : M) (a b : R) :
    g ![x, a • y + b • x] = a • g ![x, y] := by
  have h1 : (![x, a • y + b • x] : Fin 2 → M) =
      Function.update ![x, y] 1 (a • y + b • x) := by
    ext i; fin_cases i <;> rfl
  have h2 : ∀ z : M, (Function.update ![x, y] 1 z : Fin 2 → M) = ![x, z] := by
    intro z; ext i; fin_cases i <;> rfl
  rw [h1, g.map_update_add, g.map_update_smul, g.map_update_smul, h2, h2,
    g.map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) rfl (by decide), smul_zero, add_zero]

variable {k A K : Type*} [Field k] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Algebra k A] [Field K] [Algebra A K] [IsFractionRing A K] [Algebra k K] [IsScalarTower k A K]

/-- The form `dlog x ∧ dlog w` in `Ω²_{K/k}`. -/
private noncomputable def dlogWedge (w : A) (x : K) : ⋀[K]^2 Ω[K⁄k] :=
  exteriorPower.ιMulti K 2 ![x⁻¹ • KaehlerDifferential.D k K x,
    (algebraMap A K w)⁻¹ • KaehlerDifferential.D k K (algebraMap A K w)]

private theorem dlogWedge_mul (w : A) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    dlogWedge (k := k) w (x * y) = dlogWedge w x + dlogWedge w y := by
  unfold dlogWedge
  rw [← AlternatingMap.map_vecCons_add]
  congr 2
  rw [Derivation.leibniz, mul_inv, smul_add, smul_smul, smul_smul]
  rw [add_comm]
  congr 1 <;> field_simp

private theorem ιMulti_D_mem_range (a b : A) :
    exteriorPower.ιMulti K 2 ![KaehlerDifferential.D k K (algebraMap A K a),
      KaehlerDifferential.D k K (algebraMap A K b)] ∈
      LinearMap.range (topFormsMap k A K 2) := by
  refine ⟨exteriorPower.ιMulti A 2 ![KaehlerDifferential.D k A a, KaehlerDifferential.D k A b], ?_⟩
  rw [topFormsMap_ιMulti]
  congr 1
  ext i; fin_cases i <;> simp [KaehlerDifferential.map_D]

private theorem algebraMap_smul_mem_range {z : ⋀[K]^2 Ω[K⁄k]}
    (hz : z ∈ LinearMap.range (topFormsMap k A K 2)) (a : A) :
    algebraMap A K a • z ∈ LinearMap.range (topFormsMap k A K 2) := by
  rw [← algebra_compatible_smul]
  exact Submodule.smul_mem _ a hz

private theorem dlogWedge_algebraMap_unit_mem (w : A) (hw : IsUnit w) (e : A) (he : IsUnit e) :
    dlogWedge (k := k) w (algebraMap A K e) ∈ LinearMap.range (topFormsMap k A K 2) := by
  unfold dlogWedge
  obtain ⟨e', he'⟩ := he.exists_left_inv
  obtain ⟨w', hw'⟩ := hw.exists_left_inv
  have h1 : (algebraMap A K e)⁻¹ = algebraMap A K e' :=
    (eq_inv_of_mul_eq_one_left (by rw [← map_mul, he', map_one])).symm
  have h2 : (algebraMap A K w)⁻¹ = algebraMap A K w' :=
    (eq_inv_of_mul_eq_one_left (by rw [← map_mul, hw', map_one])).symm
  rw [h1, h2, AlternatingMap.map_vecCons_smul]
  refine algebraMap_smul_mem_range ?_ e'
  have : (![KaehlerDifferential.D k K (algebraMap A K e),
      algebraMap A K w' • KaehlerDifferential.D k K (algebraMap A K w)] : Fin 2 → Ω[K⁄k]) =
      Function.update ![KaehlerDifferential.D k K (algebraMap A K e),
        KaehlerDifferential.D k K (algebraMap A K w)] 1
        (algebraMap A K w' • KaehlerDifferential.D k K (algebraMap A K w)) := by
    ext i; fin_cases i <;> rfl
  rw [this, AlternatingMap.map_update_smul]
  refine algebraMap_smul_mem_range ?_ w'
  have h3 : Function.update ![KaehlerDifferential.D k K (algebraMap A K e),
      KaehlerDifferential.D k K (algebraMap A K w)] 1 (KaehlerDifferential.D k K (algebraMap A K w)) =
      ![KaehlerDifferential.D k K (algebraMap A K e), KaehlerDifferential.D k K (algebraMap A K w)] := by
    ext i; fin_cases i <;> rfl
  rw [h3]
  exact ιMulti_D_mem_range e w

private theorem dlogWedge_pow (w : A) {x : K} (hx : x ≠ 0) (n : ℕ) :
    dlogWedge (k := k) w (x ^ n) = n • dlogWedge w x := by
  induction n with
  | zero =>
    unfold dlogWedge
    simp only [pow_zero, map_one, Derivation.map_one_eq_zero, smul_zero, zero_smul]
    exact (exteriorPower.ιMulti K 2).map_coord_zero (0 : Fin 2) rfl
  | succ n ih =>
    rw [pow_succ, dlogWedge_mul w (pow_ne_zero _ hx) hx, ih, succ_nsmul]

private theorem dlogWedge_uniformizer_mem (w : A) (hw : IsUnit w) (r : k)
    (hr : w - algebraMap k A r ∈ maximalIdeal A) {π : A} (hπ : Irreducible π) :
    dlogWedge (k := k) w (algebraMap A K π) ∈ LinearMap.range (topFormsMap k A K 2) := by
  set t := w - algebraMap k A r with ht
  have hDw : KaehlerDifferential.D k K (algebraMap A K w) =
      KaehlerDifferential.D k K (algebraMap A K t) := by
    rw [ht, map_sub, map_sub, ← IsScalarTower.algebraMap_apply, Derivation.map_algebraMap,
      sub_zero]
  obtain ⟨w', hw'⟩ := hw.exists_left_inv
  have h2 : (algebraMap A K w)⁻¹ = algebraMap A K w' :=
    (eq_inv_of_mul_eq_one_left (by rw [← map_mul, hw', map_one])).symm
  have hπ0 : algebraMap A K π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hπ.ne_zero
  unfold dlogWedge
  rw [hDw, h2]
  by_cases ht0 : t = 0
  · rw [ht0, map_zero, Derivation.map_zero, smul_zero,
      (exteriorPower.ιMulti K 2).map_coord_zero (1 : Fin 2) rfl]
    exact Submodule.zero_mem _
  obtain ⟨b, e', he'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht0 hπ
  have hb : b ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at he'
    exact (mem_maximalIdeal _).1 hr (he' ▸ e'.isUnit)
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
  set p := algebraMap A K π
  set E := algebraMap A K (e' : A)
  have hDt : KaehlerDifferential.D k K (algebraMap A K t) =
      p ^ (c + 1) • KaehlerDifferential.D k K E +
        (E * ((c + 1 : ℕ) : K) * p ^ c) • KaehlerDifferential.D k K p := by
    rw [he', map_mul, map_pow, Derivation.leibniz, Derivation.leibniz_pow]
    simp only [E, p, Nat.succ_sub_one, Nat.succ_eq_add_one]
    module
  rw [hDt, AlternatingMap.map_vecCons_smul, smul_add, smul_smul, smul_smul,
    alternating_fin_two_add_smul, smul_smul]
  have hcoef : p⁻¹ * (algebraMap A K w' * p ^ (c + 1)) = algebraMap A K (w' * π ^ c) := by
    rw [map_mul, map_pow, pow_succ]; field_simp; rfl
  rw [hcoef]
  exact algebraMap_smul_mem_range (ιMulti_D_mem_range π e') _

/-- **`dlog x ∧ dlog w` is regular when `w̄` is constant.** Let `𝒪` be a discrete valuation ring
over `k` with fraction field `K`, and `w ∈ 𝒪` a unit congruent to a constant `r ∈ k` modulo `𝔪`.
For every `x ∈ K^×` the form `dlog x ∧ dlog w` comes from `Ω²_{𝒪/k}`. -/
private theorem dlogWedge_mem_range (w : A) (hw : IsUnit w) (r : k)
    (hr : w - algebraMap k A r ∈ maximalIdeal A) {x : K} (hx : x ≠ 0) :
    dlogWedge (k := k) w x ∈ LinearMap.range (topFormsMap k A K 2) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hinj := IsFractionRing.injective A K
  have hA : ∀ a : A, a ≠ 0 → dlogWedge (k := k) w (algebraMap A K a) ∈
      LinearMap.range (topFormsMap k A K 2) := by
    intro a ha
    obtain ⟨n, e, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    have hπ0 : algebraMap A K π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ.ne_zero
    have he0 : algebraMap A K (e : A) ≠ 0 := (map_ne_zero_iff _ hinj).2 e.ne_zero
    rw [map_mul, map_pow, dlogWedge_mul w he0 (pow_ne_zero _ hπ0), dlogWedge_pow w hπ0]
    exact Submodule.add_mem _ (dlogWedge_algebraMap_unit_mem w hw e e.isUnit)
      (Submodule.smul_of_tower_mem _ n (dlogWedge_uniformizer_mem w hw r hr hπ))
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap A K b ≠ 0 := (map_ne_zero_iff _ hinj).2 hb0
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have hdiv : algebraMap A K a / algebraMap A K b * algebraMap A K b = algebraMap A K a :=
    div_mul_cancel₀ _ hbK
  have e := dlogWedge_mul (k := k) w hx hbK
  rw [hdiv] at e
  have : dlogWedge (k := k) w (algebraMap A K a / algebraMap A K b) =
      dlogWedge w (algebraMap A K a) - dlogWedge w (algebraMap A K b) := by
    rw [e]; abel
  rw [this]
  exact Submodule.sub_mem _ (hA a ha0) (hA b hb0)

end DlogWedge

section ClosedImmersionStalks

/-- The kernel of the stalk map of `g ≫ I.subschemeι`, `g` an isomorphism, is the stalk of `I`. -/
private theorem ker_stalkMap_eq_of_eq_comp_subschemeι {T X : Scheme} (I : X.IdealSheafData)
    (g : T ⟶ I.subscheme) [IsIso g] (j : T ⟶ X) (h : j = g ≫ I.subschemeι) (p : T) :
    RingHom.ker (j.stalkMap p).hom = IdealSheafData.stalk I (j p) := by
  subst h
  rw [Scheme.Hom.stalkMap_comp]
  change RingHom.ker ((g.stalkMap p).hom.comp (I.subschemeι.stalkMap (g p)).hom) =
    IdealSheafData.stalk I (I.subschemeι (g p))
  rw [RingHom.ker_comp_of_injective]
  · exact MMP.Resolution.Aux.ker_stalkMap_eq_stalk_of_eq I I.subschemeι rfl (g p)
  · exact (ConcreteCategory.bijective_of_isIso (g.stalkMap p)).1

/-- The kernel of the stalk map of a closed immersion is the stalk of its kernel ideal sheaf. -/
private theorem ker_stalkMap_eq_stalk_ker {T X : Scheme} (j : T ⟶ X) [IsClosedImmersion j] (p : T) :
    RingHom.ker (j.stalkMap p).hom = IdealSheafData.stalk j.ker (j p) :=
  ker_stalkMap_eq_of_eq_comp_subschemeι j.ker j.toImage j j.toImage_imageι.symm p

/-- The kernel of a closed immersion from a reduced scheme is the vanishing ideal of its range. -/
private theorem ker_eq_vanishingIdeal_of_isReduced' {Y W : Scheme.{0}} (ι : Y ⟶ W)
    [IsClosedImmersion ι] [IsReduced Y] (T : TopologicalSpace.Closeds W)
    (hT : (T : Set W) = Set.range ι) :
    ι.ker = Scheme.IdealSheafData.vanishingIdeal T := by
  have hrad : ι.ker.radical = ι.ker := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
    apply le_antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := hx
      rw [RingHom.mem_ker, map_pow] at hn
      rw [RingHom.mem_ker]
      exact IsReduced.eq_zero _ ⟨n, hn⟩
    · exact Ideal.le_radical
  have hs : (ι.ker.support : Set W) = Set.range ι := by
    rw [Scheme.Hom.support_ker, (ι.isClosedEmbedding).isClosed_range.closure_eq]
  have : ι.ker.support = T := by
    apply TopologicalSpace.Closeds.ext
    rw [hs, hT]
  rw [← this, Scheme.IdealSheafData.vanishingIdeal_support, hrad]

/-- The ideal sheaf of a prime divisor is the vanishing ideal of its support. -/
private theorem idealSheaf_eq_vanishingIdeal {X : Scheme.{0}} (E : Mori.PrimeDivisor X) :
    E.idealSheaf = Scheme.IdealSheafData.vanishingIdeal E.idealSheaf.support := by
  haveI := E.integral
  have h := ker_eq_vanishingIdeal_of_isReduced' E.idealSheaf.subschemeι E.idealSheaf.support
    (Scheme.IdealSheafData.range_subschemeι _).symm
  rwa [Scheme.IdealSheafData.ker_subschemeι] at h

/-- **Stalks of a reduced closed subscheme onto a prime divisor.** If `j : T ⟶ X` is a closed
immersion from a reduced scheme with image the support of a prime divisor `E`, the kernel of the
stalk map of `j` at `p` is the stalk of the ideal sheaf of `E` at `j p`. -/
private theorem ker_stalkMap_eq_stalk_idealSheaf {T X : Scheme.{0}} (j : T ⟶ X)
    [IsClosedImmersion j] [IsReduced T] (E : Mori.PrimeDivisor X)
    (hE : Set.range j = (E.support : Set X)) (p : T) :
    RingHom.ker (j.stalkMap p).hom = IdealSheafData.stalk E.idealSheaf (j p) := by
  rw [ker_stalkMap_eq_stalk_ker, ker_eq_vanishingIdeal_of_isReduced' j E.idealSheaf.support
    hE.symm, ← idealSheaf_eq_vanishingIdeal]

/-- **Local equations at the generic point of a component.** Let `E` be a prime divisor through
`x` whose ideal at `x` is generated by `y`. At the generic point of `E` the image of `y` generates
the maximal ideal, and the image of a local equation of any other prime divisor through `x` is a
unit. -/
private theorem maximalIdeal_eq_span_and_isUnit_at_genericPoint {X : Scheme.{0}}
    (E : Mori.PrimeDivisor X) {x : X} (hx : x ∈ E.support) {y : X.presheaf.stalk x}
    (hy : IdealSheafData.stalk E.idealSheaf x = Ideal.span {y}) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint) =
        Ideal.span {(X.presheaf.stalkSpecializes
          (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hx)).hom y} ∧
      ∀ (E' : Mori.PrimeDivisor X), E' ≠ E → ∀ y' : X.presheaf.stalk x,
        IdealSheafData.stalk E'.idealSheaf x = Ideal.span {y'} →
        IsUnit ((X.presheaf.stalkSpecializes
          (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hx)).hom y') := by
  set h := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hx
  refine ⟨?_, fun E' hE' y' hy' => ?_⟩
  · rw [← MMP.Resolution.Aux.stalk_idealSheaf_genericPoint,
      MMP.Resolution.Aux.stalk_eq_map_stalkSpecializes E.idealSheaf h, hy, Ideal.map_span,
      Set.image_singleton]
  · by_contra hnu
    have hmem : (X.presheaf.stalkSpecializes h).hom y' ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint) :=
      (IsLocalRing.mem_maximalIdeal _).2 hnu
    have hle : IdealSheafData.stalk E'.idealSheaf x ≤ MMP.Intersection.primeOfSpecializes h := by
      rw [hy', Ideal.span_le, Set.singleton_subset_iff]
      exact hmem
    have hgen := (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes E'.idealSheaf h).2 hle
    exact hE' (MMP.Positivity.PrimeDivisor.eq_of_genericPoint_specializes
      (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E' hgen))

/-- **The local ring of a component of an snc divisor.** Let `z₁, …, z_n` be a regular system of
parameters of `𝒪_{X,x}` and `j : T ⟶ X` a closed immersion from a reduced scheme onto a prime
divisor `E` whose ideal at `x = j(p)` is `(z_a)`. Then `𝒪_{T,p}` is a regular local ring and the
restrictions of the `z_b`, `b ≠ a`, form a regular system of parameters. -/
private theorem isRegularSystemOfParameters_stalkMap_of_isClosedImmersion {T X : Scheme.{0}}
    [IsLocallyNoetherian X] (j : T ⟶ X) [IsClosedImmersion j] [IsReduced T] (E : Mori.PrimeDivisor X)
    (hE : Set.range j = (E.support : Set X)) (p : T) {n : ℕ}
    {z : Fin n → X.presheaf.stalk (j p)} (hz : IsRegularSystemOfParameters z) (a : Fin n)
    (ha : IdealSheafData.stalk E.idealSheaf (j p) = Ideal.span {z a}) :
    ∃ _ : IsRegularLocalRing (T.presheaf.stalk p),
      IsRegularSystemOfParameters (fun i : Fin ({a}ᶜ : Finset (Fin n)).card =>
        (j.stalkMap p).hom (z (({a}ᶜ : Finset (Fin n)).orderEmbOfFin rfl i))) := by
  haveI : IsRegularLocalRing (X.presheaf.stalk (j p)) :=
    MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  obtain ⟨hreg, -, hsys⟩ :=
    MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz {a}
  have hspan : Ideal.span (z '' ({a} : Finset (Fin n))) = RingHom.ker (j.stalkMap p).hom := by
    rw [ker_stalkMap_eq_stalk_idealSheaf j E hE p, ha, Finset.coe_singleton, Set.image_singleton]
  have hsurj : Function.Surjective (j.stalkMap p).hom := j.stalkMap_surjective p
  let e : (X.presheaf.stalk (j p) ⧸ Ideal.span (z '' ({a} : Finset (Fin n)))) ≃+*
      T.presheaf.stalk p :=
    (Ideal.quotEquivOfEq hspan).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  haveI := hreg
  haveI hTreg : IsRegularLocalRing (T.presheaf.stalk p) := IsRegularLocalRing.of_ringEquiv e
  refine ⟨hTreg, ?_⟩
  have hsys' := MMP.Mori.IsRegularSystemOfParameters.map_ringEquiv e hsys
  have hpt : ∀ x : X.presheaf.stalk (j p),
      e (Ideal.Quotient.mk (Ideal.span (z '' ({a} : Finset (Fin n)))) x) =
        (j.stalkMap p).hom x := fun x => rfl
  simp only [hpt] at hsys'
  exact hsys'

end ClosedImmersionStalks

section SNCRestriction

/-- **Log canonical places of a dlt pair lie over its snc locus.** Let `(X, B)` be a dlt pair
and `D` a proper divisor over `X` with log discrepancy `0`. Then the generic point of the centre
of `D` lies in an open `U` on which `X` is smooth and `B|_U` is snc. -/
private theorem exists_snc_open_of_isDltPair {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X}
    (hdlt : MMP.Intersection.IsDltPair sX B) {n : ℕ} (D : DivisorOver k sX)
    (hD : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D 0) :
    ∃ U : X.Opens, D.f D.E.genericPoint ∈ U ∧ MMP.Mori.IsSmoothScheme (U.ι ≫ sX) ∧
      DivisorWithCoeffs.IsSNC (U.ι ≫ sX) (B.restrictOpen U) := by
  obtain ⟨-, -, Z, hsm, hsnc, hpos⟩ := hdlt
  refine ⟨Z.compl, ?_, hsm, ?_⟩
  · by_contra hη
    have hsub : (D.center : Set X) ⊆ Z := by
      rw [D.center_eq_closure_genericPoint]
      refine closure_minimal (Set.singleton_subset_iff.2 ?_) Z.isClosed
      by_contra h
      exact hη h
    exact lt_irrefl _ (hpos n D hsub 0 hD)
  · rwa [← MMP.Mori.inverseTransformDivisor_ι_eq_restrictOpen]

/-- **Log canonical places over the reduced snc boundary.** Let `(X, B)` be a pair with
`0 ≤ B ≤ 1`, `D` a proper divisor over `X` with discrepancy `-1`, and `U ⊆ X` an open containing
the generic point of the centre of `D`, smooth and with `B|_U` snc. Then the restriction of `D` to
`U` has discrepancy `-1` over the reduced divisor `T` with the support of `B|_U`. -/
private theorem exists_isDiscrepancy_reducedDivisorOf {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : ∀ P, 0 ≤ B.coeff P ∧ B.coeff P ≤ 1) {n : ℕ} {K : Divisor X}
    (hP : MMP.Mori.IsPairWith sX n K B) (D : DivisorOver k sX) (hDp : IsProper D.f)
    (hD : MMP.Mori.IsDiscrepancy sX n K B D (-1)) (U : X.Opens)
    (hηU : D.f D.E.genericPoint ∈ U) (hsm : MMP.Mori.IsSmoothScheme (U.ι ≫ sX))
    (hsnc : DivisorWithCoeffs.IsSNC (U.ι ≫ sX) (B.restrictOpen U)) :
    haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
    haveI : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨_, hηU⟩)
    ∃ D' : DivisorOver k (U.ι ≫ sX), IsProper D'.f ∧
      D.valuation = D'.valuation.comap (functionFieldMap U.ι) ∧
      MMP.Mori.IsDiscrepancy (U.ι ≫ sX) n (K.restrictOpen U)
        (Divisor.toQDivisor (MMP.Intersection.reducedDivisorOf (B.restrictOpen U).support)) D'
        (-1) := by
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  haveI : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨_, hηU⟩)
  have hU : ((D.center : Set X) ∩ U).Nonempty := ⟨_, by
    rw [D.center_eq_closure_genericPoint]; exact subset_closure rfl, hηU⟩
  obtain ⟨hY, hf, E', -, hval, hiff⟩ := MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff hP D U hU
  set T := MMP.Intersection.reducedDivisorOf (B.restrictOpen U).support with hT
  refine ⟨⟨_, D.f ∣_ U, hY, hf, E'⟩, ?_, hval, ?_⟩
  · haveI := hDp
    change IsProper (D.f ∣_ U)
    infer_instance
  have hD' := (hiff (-1)).1 hD
  have hΔe : (Divisor.toQDivisor T - B.restrictOpen U).IsEffective := by
    intro P
    classical
    obtain ⟨h0, h1⟩ := hB (OpenWeilRestriction.primeDivisorMap U.ι P)
    rw [DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor, hT,
      MMP.Intersection.coeff_reducedDivisorOf, DivisorWithCoeffs.coeff_restrictOpen]
    split_ifs with hmem
    · push_cast; linarith
    · have : (B.restrictOpen U).coeff P = 0 := by
        by_contra hne
        exact hmem (Finsupp.mem_support_iff.2 hne)
      rw [DivisorWithCoeffs.coeff_restrictOpen] at this
      rw [this]; simp
  have hΔq := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm (Divisor.toQDivisor T - B.restrictOpen U)
  obtain ⟨a', hle, ha'⟩ := MMP.Threefold.Mori.Helpers.exists_isDiscrepancy_add_le hΔe hΔq hD'
  rw [add_sub_cancel] at ha'
  have hpU : IsProper (D.f ∣_ U) := by haveI := hDp; infer_instance
  have hla := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha' hpU
  rw [QDivisor.toRDivisor_toQDivisor] at hla
  obtain ⟨N, hN⟩ := MMP.Intersection.IsLogDiscrepancy.exists_nat_eq_of_isSNC _
    (hP.1.restrictOpen U).1 hsm (MMP.Intersection.isReducedEffective_reducedDivisorOf _)
    (hsnc.of_support_subset (by rw [MMP.Intersection.support_reducedDivisorOf])) hla
  have h1 : (-1 : ℚ) ≤ a' := by
    have : (0 : ℝ) ≤ 1 + (a' : ℝ) := hN ▸ Nat.cast_nonneg N
    exact_mod_cast (by linarith : (-1 : ℝ) ≤ a')
  rwa [show a' = -1 from le_antisymm hle h1] at ha'

end SNCRestriction

section MonomialResidues

/-- `∏ exp(fᵢ) = exp(∑ fᵢ)` in `ℤᵐ⁰`. -/
private theorem prod_exp {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, WithZero.exp (f i) = WithZero.exp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, WithZero.exp_add]

/-- The value of a monomial `z^β` under a valuation with `v(zᵢ) = exp(-αᵢ)`. -/
private theorem valuation_prod_pow_eq {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    {ι : Type*} [Fintype ι] (z : ι → R) (α : ι → ℕ) (v : Valuation K ℤᵐ⁰)
    (hz : ∀ i, v (algebraMap R K (z i)) = WithZero.exp (-(α i : ℤ))) (β : ι → ℕ) :
    v (algebraMap R K (∏ i, z i ^ β i)) = WithZero.exp (-((∑ i, α i * β i : ℕ) : ℤ)) := by
  rw [map_prod, map_prod]
  simp only [map_pow, hz, ← WithZero.exp_nsmul, prod_exp]
  congr 1
  push_cast
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [nsmul_eq_mul]; ring

/-- **Leading forms in a monomial ideal.** Let `v` be a valuation of `K`, nonnegative on `R`, with
`v(zᵢ) = exp(-αᵢ)`, and `T ∈ K` of value `exp(-1)`. Every `f ∈ 𝔞_{α,M}` satisfies
`v(f/T^M - ∑_β c_β z^β/T^M) < 1` for finitely many `β` of weight exactly `M` and `c_β ∈ R`. -/
private theorem exists_sub_lt_one_of_mem_weightedMonomialIdeal {R K : Type*} [CommRing R]
    [Field K] [Algebra R K] {ι : Type*} [Fintype ι] (z : ι → R) (α : ι → ℕ)
    (v : Valuation K ℤᵐ⁰) (hv : ∀ r : R, v (algebraMap R K r) ≤ 1)
    (hz : ∀ i, v (algebraMap R K (z i)) = WithZero.exp (-(α i : ℤ)))
    (T : K) (hT : v T = WithZero.exp (-1)) (M : ℕ) {f : R}
    (hf : f ∈ weightedMonomialIdeal z α M) :
    ∃ (s : Finset (ι → ℕ)) (c : (ι → ℕ) → R), (∀ β ∈ s, ∑ i, α i * β i = M) ∧
      v (algebraMap R K f / T ^ M -
        ∑ β ∈ s, algebraMap R K (c β) * (algebraMap R K (∏ i, z i ^ β i) / T ^ M)) < 1 := by
  classical
  have hTM : v (T ^ M) = WithZero.exp (-(M : ℤ)) := by
    rw [map_pow, hT, ← WithZero.exp_nsmul]; congr 1; simp
  unfold weightedMonomialIdeal at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    rcases hβ.eq_or_lt with h | h
    · refine ⟨{β}, fun _ => 1, by simpa using h.symm, ?_⟩
      simp
    · refine ⟨∅, fun _ => 0, by simp, ?_⟩
      simp only [Finset.sum_empty, sub_zero, map_div₀, valuation_prod_pow_eq z α v hz, hTM]
      rw [← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
  | zero => exact ⟨∅, fun _ => 0, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, c, hs, hc⟩ := hx
    obtain ⟨s', c', hs', hc'⟩ := hy
    refine ⟨s ∪ s', fun β => (if β ∈ s then c β else 0) + (if β ∈ s' then c' β else 0), ?_, ?_⟩
    · intro β hβ
      rcases Finset.mem_union.1 hβ with h | h
      exacts [hs β h, hs' β h]
    · have e : ∀ (t u : Finset (ι → ℕ)) (d : (ι → ℕ) → R), t ⊆ u →
          ∑ β ∈ u, algebraMap R K (if β ∈ t then d β else 0) *
            (algebraMap R K (∏ i, z i ^ β i) / T ^ M) =
          ∑ β ∈ t, algebraMap R K (d β) * (algebraMap R K (∏ i, z i ^ β i) / T ^ M) := by
        intro t u d htu
        rw [← Finset.sum_subset htu]
        · exact Finset.sum_congr rfl fun β hβ => by rw [if_pos hβ]
        · intro β _ hβ; rw [if_neg hβ, map_zero, zero_mul]
      simp only [map_add, add_mul, Finset.sum_add_distrib]
      rw [e s _ c Finset.subset_union_left, e s' _ c' Finset.subset_union_right, add_div]
      have : ∀ a b A B : K, a + b - (A + B) = (a - A) + (b - B) := fun _ _ _ _ => by ring
      rw [this]
      exact v.map_add_lt hc hc'
  | smul a x _ hx =>
    obtain ⟨s, c, hs, hc⟩ := hx
    refine ⟨s, fun β => a * c β, hs, ?_⟩
    have : algebraMap R K (a • x) / T ^ M -
        ∑ β ∈ s, algebraMap R K (a * c β) * (algebraMap R K (∏ i, z i ^ β i) / T ^ M) =
        algebraMap R K a * (algebraMap R K x / T ^ M -
          ∑ β ∈ s, algebraMap R K (c β) * (algebraMap R K (∏ i, z i ^ β i) / T ^ M)) := by
      rw [smul_eq_mul, mul_sub, Finset.mul_sum]
      simp only [map_mul]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun β _ => by ring
    rw [this, map_mul]
    calc v (algebraMap R K a) * _ ≤ 1 * v (algebraMap R K x / T ^ M -
          ∑ β ∈ s, algebraMap R K (c β) * (algebraMap R K (∏ i, z i ^ β i) / T ^ M)) :=
          mul_le_mul_left (hv a) _
      _ < 1 := by rwa [one_mul]

/-- **Residues of a monomial valuation are ratios of leading forms.** Let `v` be a valuation of
the fraction field `K` of `R`, nonnegative on `R`, with `v(zᵢ) = exp(-αᵢ)`, such that every
nonzero `f ∈ R` of value `exp(-M)` lies in `𝔞_{α,M}`, and let `T ∈ K` have value `exp(-1)`. Then
for every `h ∈ K` with `v(h) ≤ 1` there are `a, b ∈ K`, each a sum `∑ c_β z^β/T^M` over monomials
of one weight `M`, with `v(b) = 1` and `v(h b - a) < 1`; so the residue of `h` is the quotient of
the residues of `a` and `b`. -/
private theorem exists_leadingForms_of_valuation_le_one {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] {ι : Type*} [Fintype ι] (z : ι → R)
    (α : ι → ℕ) (v : Valuation K ℤᵐ⁰) (hv : ∀ r : R, v (algebraMap R K r) ≤ 1)
    (hz : ∀ i, v (algebraMap R K (z i)) = WithZero.exp (-(α i : ℤ)))
    (hmono : ∀ f : R, f ≠ 0 → ∃ M : ℕ, f ∈ weightedMonomialIdeal z α M ∧
      v (algebraMap R K f) = WithZero.exp (-(M : ℤ)))
    (T : K) (hT : v T = WithZero.exp (-1)) {h : K} (hh : v h ≤ 1) :
    ∃ (M : ℕ) (s s' : Finset (ι → ℕ)) (c c' : (ι → ℕ) → R),
      (∀ β ∈ s, ∑ i, α i * β i = M) ∧ (∀ β ∈ s', ∑ i, α i * β i = M) ∧
      v (∑ β ∈ s', algebraMap R K (c' β) * (algebraMap R K (∏ i, z i ^ β i) / T ^ M)) = 1 ∧
      v (h * (∑ β ∈ s', algebraMap R K (c' β) * (algebraMap R K (∏ i, z i ^ β i) / T ^ M)) -
        ∑ β ∈ s, algebraMap R K (c β) * (algebraMap R K (∏ i, z i ^ β i) / T ^ M)) < 1 := by
  classical
  have hT0 : T ≠ 0 := by
    intro h0; rw [h0, map_zero] at hT; exact WithZero.zero_ne_coe hT
  obtain ⟨f₁, f₂, hf₂, rfl⟩ := IsFractionRing.div_surjective (A := R) h
  have hf₂0 : f₂ ≠ 0 := nonZeroDivisors.ne_zero hf₂
  have hinj := IsFractionRing.injective R K
  have h2 : algebraMap R K f₂ ≠ 0 := (map_ne_zero_iff _ hinj).2 hf₂0
  obtain ⟨M₂, hM₂, hv₂⟩ := hmono f₂ hf₂0
  have hTM : v (T ^ M₂) = WithZero.exp (-(M₂ : ℤ)) := by
    rw [map_pow, hT, ← WithZero.exp_nsmul]; congr 1; simp
  have hf₁M : f₁ ∈ weightedMonomialIdeal z α M₂ := by
    by_cases hf₁0 : f₁ = 0
    · rw [hf₁0]; exact Ideal.zero_mem _
    obtain ⟨M₁, hM₁, hv₁⟩ := hmono f₁ hf₁0
    have hle : M₂ ≤ M₁ := by
      rw [map_div₀, hv₁, hv₂, ← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_le_exp] at hh
      omega
    exact weightedMonomialIdeal_antitone z α hle hM₁
  obtain ⟨s, c, hs, hc⟩ := exists_sub_lt_one_of_mem_weightedMonomialIdeal z α v hv hz T hT M₂ hf₁M
  obtain ⟨s', c', hs', hc'⟩ := exists_sub_lt_one_of_mem_weightedMonomialIdeal z α v hv hz T hT M₂ hM₂
  set A := ∑ β ∈ s, algebraMap R K (c β) * (algebraMap R K (∏ i, z i ^ β i) / T ^ M₂)
  set A' := ∑ β ∈ s', algebraMap R K (c' β) * (algebraMap R K (∏ i, z i ^ β i) / T ^ M₂)
  have hq : v (algebraMap R K f₂ / T ^ M₂) = 1 := by
    rw [map_div₀, hv₂, hTM, div_self (by simp)]
  refine ⟨M₂, s, s', c, c', hs, hs', ?_, ?_⟩
  · change v A' = 1
    have : A' = algebraMap R K f₂ / T ^ M₂ - (algebraMap R K f₂ / T ^ M₂ - A') := by ring
    rw [this, Valuation.map_sub_eq_of_lt_left _ (by rwa [hq])]
    exact hq
  · change v (algebraMap R K f₁ / algebraMap R K f₂ * A' - A) < 1
    have : algebraMap R K f₁ / algebraMap R K f₂ * A' - A =
        algebraMap R K f₁ / algebraMap R K f₂ * (A' - algebraMap R K f₂ / T ^ M₂) +
          (algebraMap R K f₁ / T ^ M₂ - A) := by
      field_simp
      ring
    rw [this]
    refine v.map_add_lt ?_ hc
    rw [map_mul]
    calc _ ≤ 1 * v (A' - algebraMap R K f₂ / T ^ M₂) := mul_le_mul_left hh _
      _ < 1 := by rw [one_mul, Valuation.map_sub_swap]; exact hc'

end MonomialResidues

section ResidueOrder

/-- A rational function without pole along a prime divisor `P` lies in the local ring `𝒪_{Y,P}`. -/
private theorem exists_algebraMap_eq_of_zero_le_ord {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (P : Mori.PrimeDivisor Y) {x : Y}
    (hx : x = P.genericPoint) {f : Y.functionField} (hf : f ≠ 0) (h : 0 ≤ Y.ord f x) :
    ∃ c : Y.presheaf.stalk x, algebraMap _ Y.functionField c = f := by
  subst hx
  have : P.divisorialValuation f ≤ 1 := by
    rw [P.divisorialValuation_eq_exp_neg_ord hf, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  obtain ⟨c, hc⟩ := (P.divisorialValuation_le_one_iff f).mp this
  exact ⟨c, hc⟩

/-- A nonzero element of `𝒪_{Y,P}` vanishes along `P` exactly when it lies in the maximal ideal. -/
private theorem one_le_ord_iff_mem_maximalIdeal {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (P : Mori.PrimeDivisor Y) {x : Y}
    (hx : x = P.genericPoint) {c : Y.presheaf.stalk x} (hc : c ≠ 0) :
    1 ≤ Y.ord (algebraMap _ Y.functionField c) x ↔
      c ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x) := by
  subst hx
  have h0 : algebraMap _ Y.functionField c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hc
  rw [← P.divisorialValuation_algebraMap_lt_one_iff, P.divisorialValuation_eq_exp_neg_ord h0,
    ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

/-- Restriction `𝒪_{Y,T} → k(T)` along a closed immersion kills exactly the maximal ideal. -/
private theorem stalkMap_eq_zero_iff {Y T : Scheme.{0}} [IsIntegral T] (j : T ⟶ Y)
    [IsClosedImmersion j] (c : Y.presheaf.stalk (j (genericPoint T))) :
    (j.stalkMap (genericPoint T)).hom c = 0 ↔ c ∈ IsLocalRing.maximalIdeal _ := by
  have hsurj : Function.Surjective (j.stalkMap (genericPoint T)).hom :=
    SurjectiveOnStalks.stalkMap_surjective j _
  have := IsLocalRing.eq_maximalIdeal
    (RingHom.ker_isMaximal_of_surjective (K := T.functionField) _ hsurj)
  rw [← this]
  rfl

/-- An element of `𝒪_{Y,P}` lies in the maximal ideal exactly when its valuation along `P` is
`< 1`. -/
private theorem mem_maximalIdeal_iff_divisorialValuation_lt_one {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (P : Mori.PrimeDivisor Y) {x : Y}
    (hx : x = P.genericPoint) (c : Y.presheaf.stalk x) :
    c ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x) ↔
      P.divisorialValuation (algebraMap _ Y.functionField c) < 1 := by
  subst hx
  exact (P.divisorialValuation_algebraMap_lt_one_iff c).symm

/-- A rational function of valuation `≤ 1` along a prime divisor `P` lies in `𝒪_{Y,P}`. -/
private theorem exists_algebraMap_eq_of_divisorialValuation_le_one {Y : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (P : Mori.PrimeDivisor Y) {x : Y}
    (hx : x = P.genericPoint) {f : Y.functionField} (hf : P.divisorialValuation f ≤ 1) :
    ∃ c : Y.presheaf.stalk x, algebraMap _ Y.functionField c = f := by
  subst hx
  obtain ⟨c, hc⟩ := (P.divisorialValuation_le_one_iff f).mp hf
  exact ⟨c, hc⟩

open Classical in
/-- The residue along a closed immersion `j : T ⟶ Y` onto a prime divisor `P` of a rational
function `f` of valuation `≤ 1`: the restriction to `T` of its lift to `𝒪_{Y,P}` (and `0` if `f`
has a pole). -/
private noncomputable def residueAlong {Y T : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral T] (j : T ⟶ Y) (P : Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint) (f : Y.functionField) : T.functionField :=
  if hf : P.divisorialValuation f ≤ 1 then
    (j.stalkMap (genericPoint T)).hom
      (exists_algebraMap_eq_of_divisorialValuation_le_one P hP hf).choose
  else 0

/-- The residue of the image of `c ∈ 𝒪_{Y,P}` is its restriction to `T`. -/
private theorem residueAlong_algebraMap {Y T : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral T] (j : T ⟶ Y) (P : Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint) (c : Y.presheaf.stalk (j (genericPoint T))) :
    residueAlong j P hP (algebraMap _ Y.functionField c) = (j.stalkMap (genericPoint T)).hom c := by
  have hle : P.divisorialValuation (algebraMap _ Y.functionField c) ≤ 1 := by
    obtain ⟨c', hc'⟩ : ∃ c' : P.localRing, algebraMap P.localRing Y.functionField c' =
        algebraMap _ Y.functionField c := by
      revert c; rw [hP]; intro c; exact ⟨c, rfl⟩
    rw [← hc']
    exact (P.divisorialValuation_le_one_iff _).2 ⟨c', rfl⟩
  rw [residueAlong, dif_pos hle]
  congr 1
  exact IsFractionRing.injective _ Y.functionField
    (exists_algebraMap_eq_of_divisorialValuation_le_one P hP hle).choose_spec

/-- Residues along `P` are additive on rational functions without pole along `P`. -/
private theorem residueAlong_add {Y T : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral T] (j : T ⟶ Y) (P : Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint) {f g : Y.functionField}
    (hf : P.divisorialValuation f ≤ 1) (hg : P.divisorialValuation g ≤ 1) :
    residueAlong j P hP (f + g) = residueAlong j P hP f + residueAlong j P hP g := by
  obtain ⟨c, rfl⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one P hP hf
  obtain ⟨d, rfl⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one P hP hg
  rw [← map_add, residueAlong_algebraMap, residueAlong_algebraMap, residueAlong_algebraMap,
    map_add]

/-- Residues along `P` are multiplicative on rational functions without pole along `P`. -/
private theorem residueAlong_mul {Y T : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral T] (j : T ⟶ Y) (P : Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint) {f g : Y.functionField}
    (hf : P.divisorialValuation f ≤ 1) (hg : P.divisorialValuation g ≤ 1) :
    residueAlong j P hP (f * g) = residueAlong j P hP f * residueAlong j P hP g := by
  obtain ⟨c, rfl⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one P hP hf
  obtain ⟨d, rfl⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one P hP hg
  rw [← map_mul, residueAlong_algebraMap, residueAlong_algebraMap, residueAlong_algebraMap,
    map_mul]

/-- A rational function of valuation `< 1` along `P` has residue zero. -/
private theorem residueAlong_eq_zero_of_lt_one {Y T : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] (j : T ⟶ Y) [IsClosedImmersion j]
    (P : Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint) {f : Y.functionField}
    (hf : P.divisorialValuation f < 1) : residueAlong j P hP f = 0 := by
  obtain ⟨c, rfl⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one P hP hf.le
  rw [residueAlong_algebraMap, stalkMap_eq_zero_iff j]
  exact (mem_maximalIdeal_iff_divisorialValuation_lt_one P hP c).2 hf

/-- A rational function of valuation `1` along `P` has nonzero residue. -/
private theorem residueAlong_ne_zero {Y T : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] (j : T ⟶ Y) [IsClosedImmersion j]
    (P : Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint) {f : Y.functionField}
    (hf : P.divisorialValuation f = 1) : residueAlong j P hP f ≠ 0 := by
  obtain ⟨c, rfl⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one P hP hf.le
  rw [residueAlong_algebraMap, Ne, stalkMap_eq_zero_iff j,
    mem_maximalIdeal_iff_divisorialValuation_lt_one P hP c, hf]
  exact lt_irrefl 1

/-- Residues along `P` of finite sums of rational functions without pole along `P`. -/
private theorem residueAlong_sum {Y T : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral T] (j : T ⟶ Y) (P : Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint) {ι : Type*} (s : Finset ι)
    (f : ι → Y.functionField) (hf : ∀ i ∈ s, P.divisorialValuation (f i) ≤ 1) :
    residueAlong j P hP (∑ i ∈ s, f i) = ∑ i ∈ s, residueAlong j P hP (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [← map_zero (algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField),
      residueAlong_algebraMap, map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      residueAlong_add j P hP (hf a (Finset.mem_insert_self _ _))
        ((P.divisorialValuation).map_sum_le fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- Every element of `k(T)` is the residue of a rational function without pole along `P`. -/
private theorem exists_residueAlong_eq {Y T : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral T] (j : T ⟶ Y) [IsClosedImmersion j] (P : Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint) (g : T.functionField) :
    ∃ f : Y.functionField, P.divisorialValuation f ≤ 1 ∧ residueAlong j P hP f = g := by
  obtain ⟨c, rfl⟩ := SurjectiveOnStalks.stalkMap_surjective j (genericPoint T) g
  refine ⟨algebraMap _ Y.functionField c, ?_, residueAlong_algebraMap j P hP c⟩
  obtain ⟨c', hc'⟩ : ∃ c' : P.localRing, algebraMap P.localRing Y.functionField c' =
      algebraMap _ Y.functionField c := by
    revert c; rw [hP]; intro c; exact ⟨c, rfl⟩
  rw [← hc']
  exact (P.divisorialValuation_le_one_iff _).2 ⟨c', rfl⟩

/-- If `v_P(h b - a) < 1` with `v_P(b) = 1`, the residue of `h` is the residue of `a` divided by
that of `b`. -/
private theorem residueAlong_eq_div_of_sub_lt_one {Y T : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] (j : T ⟶ Y) [IsClosedImmersion j]
    (P : Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint)
    {h a b : Y.functionField} (hh : P.divisorialValuation h ≤ 1)
    (ha : P.divisorialValuation a ≤ 1) (hb : P.divisorialValuation b = 1)
    (hlt : P.divisorialValuation (h * b - a) < 1) :
    residueAlong j P hP h = residueAlong j P hP a / residueAlong j P hP b := by
  have hb0 := residueAlong_ne_zero j P hP hb
  rw [eq_div_iff hb0, ← residueAlong_mul j P hP hh hb.le]
  have h1 : P.divisorialValuation (h * b) ≤ 1 := by
    rw [map_mul]; calc _ ≤ 1 * 1 := mul_le_mul' hh hb.le
      _ = 1 := one_mul 1
  have := residueAlong_add j P hP (f := h * b - a) (g := a) hlt.le ha
  rw [sub_add_cancel, residueAlong_eq_zero_of_lt_one j P hP hlt, zero_add] at this
  exact this

/-- Residues along `P` of finite products of rational functions without pole along `P`. -/
private theorem residueAlong_prod {Y T : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral T] (j : T ⟶ Y) (P : Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint) {ι : Type*} (s : Finset ι)
    (f : ι → Y.functionField) (hf : ∀ i ∈ s, P.divisorialValuation (f i) ≤ 1) :
    residueAlong j P hP (∏ i ∈ s, f i) = ∏ i ∈ s, residueAlong j P hP (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [← map_one (algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField),
      residueAlong_algebraMap, map_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      residueAlong_mul j P hP (hf a (Finset.mem_insert_self _ _))
        (by rw [map_prod]; exact Finset.prod_le_one' fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- Residues along `P` commute with integer powers of rational functions of valuation `1`. -/
private theorem residueAlong_zpow {Y T : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral T] (j : T ⟶ Y) [IsClosedImmersion j] (P : Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint) {x : Y.functionField}
    (hx : P.divisorialValuation x = 1) (n : ℤ) :
    residueAlong j P hP (x ^ n) = residueAlong j P hP x ^ n := by
  have hpow : ∀ m : ℕ, residueAlong j P hP (x ^ m) = residueAlong j P hP x ^ m := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero, pow_zero, ← map_one (algebraMap (Y.presheaf.stalk (j (genericPoint T)))
        Y.functionField), residueAlong_algebraMap, map_one]
    | succ m ih =>
      rw [pow_succ, residueAlong_mul j P hP (by rw [map_pow, hx, one_pow]) hx.le, ih, pow_succ]
  have hinv : ∀ y : Y.functionField, P.divisorialValuation y = 1 →
      residueAlong j P hP y⁻¹ = (residueAlong j P hP y)⁻¹ := by
    intro y hy
    have hy0 : y ≠ 0 := by intro h; rw [h, map_zero] at hy; exact zero_ne_one hy
    have h1 : residueAlong j P hP y * residueAlong j P hP y⁻¹ = 1 := by
      rw [← residueAlong_mul j P hP hy.le (by rw [map_inv₀, hy, inv_one]), mul_inv_cancel₀ hy0]
      simpa using hpow 0
    exact eq_inv_of_mul_eq_one_right h1
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · exact_mod_cast hpow m
  · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast,
      hinv _ (by rw [map_pow, hx, one_pow]), hpow]

/-- **Residues of degree-zero monomials.** Let `z_i` be units of `k(Y)`, `M` an invertible integer
matrix with rows `s_a = ∏_b z_b^{M_{ab}}`, and `i₀` an index such that `s_{i₀}` has weight one and
the `i₀`-th coordinate of `u M⁻¹` is the weight `⟨α, u⟩` of `u`. If the `s_a`, `a ≠ i₀`, have
valuation `1` along `P`, then the residue of every `z^β / s_{i₀}^{⟨α,β⟩}` lies in the field
generated over `k` by the residues of the `s_a`, `a ≠ i₀`. -/
private theorem residueAlong_monomial_mem_adjoin {k : Type} [Field k] {Y T : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] (j : T ⟶ Y)
    [IsClosedImmersion j] (P : Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint)
    [Algebra k T.functionField] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (zU : ι → (Y.functionField)ˣ) (α : ι → ℕ) (M : Matrix ι ι ℤ) (hM : IsUnit M.det) (i₀ : ι)
    (hcol : ∀ u : ι → ℤ, Matrix.vecMul u M⁻¹ i₀ = ∑ i, (α i : ℤ) * u i)
    (hrow : ∑ i, (α i : ℤ) * M i₀ i = 1)
    (hs : ∀ a, a ≠ i₀ →
      P.divisorialValuation ((∏ b, zU b ^ M a b : (Y.functionField)ˣ) : Y.functionField) = 1)
    (β : ι → ℕ) :
    residueAlong j P hP ((∏ i, (zU i : Y.functionField) ^ β i) /
        ((∏ b, zU b ^ M i₀ b : (Y.functionField)ˣ) : Y.functionField) ^ (∑ i, α i * β i)) ∈
      IntermediateField.adjoin k (Set.range fun a : {a // a ≠ i₀} =>
        residueAlong j P hP ((∏ b, zU b ^ M a.1 b : (Y.functionField)ˣ) : Y.functionField)) := by
  set w : ℕ := ∑ i, α i * β i
  set u : ι → ℤ := fun i => (β i : ℤ) - (w : ℤ) * M i₀ i
  set sU : ι → (Y.functionField)ˣ := fun a => ∏ b, zU b ^ M a b
  have hc0 : Matrix.vecMul u M⁻¹ i₀ = 0 := by
    rw [hcol]
    simp only [u, mul_sub, Finset.sum_sub_distrib]
    have : ∑ i, (α i : ℤ) * ((w : ℤ) * M i₀ i) = (w : ℤ) * ∑ i, (α i : ℤ) * M i₀ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hrow, mul_one]
    simp [w]
  have hU : (∏ i, zU i ^ β i) / sU i₀ ^ w = ∏ i, zU i ^ u i := by
    simp only [u, sU, zpow_sub, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
      zpow_natCast, ← Finset.prod_pow]
    congr 2
    exact Finset.prod_congr rfl fun i _ => by rw [← zpow_natCast, ← zpow_mul, mul_comm]
  have heq : (∏ i, (zU i : Y.functionField) ^ β i) /
      ((sU i₀ : (Y.functionField)ˣ) : Y.functionField) ^ w =
      ((∏ a, sU a ^ Matrix.vecMul u M⁻¹ a : (Y.functionField)ˣ) : Y.functionField) := by
    rw [← prod_zpow_eq_prod_monomial_zpow zU M hM u, ← hU]
    simp [Units.val_div_eq_div_val, Units.coe_prod]
  change residueAlong j P hP (_ / ((sU i₀ : (Y.functionField)ˣ) : Y.functionField) ^ w) ∈ _
  rw [heq, Units.coe_prod]
  have hv1 : ∀ a, P.divisorialValuation
      (((sU a ^ Matrix.vecMul u M⁻¹ a : (Y.functionField)ˣ)) : Y.functionField) = 1 := by
    intro a
    by_cases ha : a = i₀
    · subst ha; rw [hc0, zpow_zero, Units.val_one, map_one]
    · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hs a ha, one_zpow]
  rw [residueAlong_prod j P hP _ _ fun a _ => (hv1 a).le]
  refine IntermediateField.prod_mem _ fun a _ => ?_
  by_cases ha : a = i₀
  · subst ha
    rw [hc0, zpow_zero, Units.val_one,
      ← map_one (algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField),
      residueAlong_algebraMap, map_one]
    exact IntermediateField.one_mem _
  · rw [Units.val_zpow_eq_zpow_val, residueAlong_zpow j P hP (hs a ha)]
    have hmem : residueAlong j P hP ((sU a : (Y.functionField)ˣ) : Y.functionField) ∈
        IntermediateField.adjoin k (Set.range fun a : {a // a ≠ i₀} =>
          residueAlong j P hP ((∏ b, zU b ^ M a.1 b : (Y.functionField)ˣ) : Y.functionField)) :=
      IntermediateField.subset_adjoin _ _ (Set.mem_range.2 ⟨⟨a, ha⟩, rfl⟩)
    exact zpow_mem hmem _

/-- **Generation of the residue field of a monomial valuation along a prime divisor.** Let `P` be
a prime divisor of `Y` with closed immersion `j : T ⟶ Y`, and suppose `v_P` is monomial with
respect to `z : ι → R` (`R ⊆ k(Y)` with fraction field `k(Y)`), `T₀` a rational function with
`v_P(T₀) = exp(-1)`. If every element of `R` is congruent to a constant of `k` modulo `v_P < 1`,
then an intermediate field `L` of `k(T)` containing the residues of all `z^β / T₀^{⟨α,β⟩}` is all
of `k(T)`. -/
private theorem eq_top_of_residueAlong_monomial_mem {k : Type} [Field k] {Y T : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] (j : T ⟶ Y)
    [IsClosedImmersion j] (P : Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint)
    [Algebra k Y.functionField] [Algebra k T.functionField]
    (hk : ∀ c : k, residueAlong j P hP (algebraMap k Y.functionField c) =
      algebraMap k T.functionField c)
    (hkv : ∀ c : k, P.divisorialValuation (algebraMap k Y.functionField c) ≤ 1)
    {R : Type*} [CommRing R] [IsDomain R] [Algebra R Y.functionField]
    [IsFractionRing R Y.functionField] {ι : Type*} [Fintype ι] (z : ι → R) (α : ι → ℕ)
    (hv : ∀ r : R, P.divisorialValuation (algebraMap R Y.functionField r) ≤ 1)
    (hz : ∀ i, P.divisorialValuation (algebraMap R Y.functionField (z i)) =
      WithZero.exp (-(α i : ℤ)))
    (hmono : ∀ f : R, f ≠ 0 → ∃ M : ℕ, f ∈ weightedMonomialIdeal z α M ∧
      P.divisorialValuation (algebraMap R Y.functionField f) = WithZero.exp (-(M : ℤ)))
    (T₀ : Y.functionField) (hT : P.divisorialValuation T₀ = WithZero.exp (-1))
    (hconst : ∀ r : R, ∃ c : k, P.divisorialValuation
      (algebraMap R Y.functionField r - algebraMap k Y.functionField c) < 1)
    (L : IntermediateField k T.functionField)
    (hL : ∀ β : ι → ℕ, residueAlong j P hP
      (algebraMap R Y.functionField (∏ i, z i ^ β i) / T₀ ^ (∑ i, α i * β i)) ∈ L) :
    L = ⊤ := by
  classical
  set v := P.divisorialValuation
  have hTM : ∀ M : ℕ, v (T₀ ^ M) = WithZero.exp (-(M : ℤ)) := fun M => by
    rw [map_pow, hT, ← WithZero.exp_nsmul]; congr 1; simp
  -- monomials of weight `M` divided by `T₀^M` have valuation `1`
  have hmon1 : ∀ (M : ℕ) (β : ι → ℕ), ∑ i, α i * β i = M →
      v (algebraMap R Y.functionField (∏ i, z i ^ β i) / T₀ ^ M) = 1 := by
    intro M β hβ
    rw [map_div₀, valuation_prod_pow_eq z α v hz, hβ, hTM, div_self (by simp)]
  -- residues of elements of `R` are constants
  have hres_const : ∀ r : R, residueAlong j P hP (algebraMap R Y.functionField r) ∈ L := by
    intro r
    obtain ⟨c, hc⟩ := hconst r
    have e : algebraMap R Y.functionField r =
        (algebraMap R Y.functionField r - algebraMap k Y.functionField c) +
          algebraMap k Y.functionField c := by ring
    rw [e, residueAlong_add j P hP hc.le (hkv c), residueAlong_eq_zero_of_lt_one j P hP hc,
      zero_add, hk]
    exact L.algebraMap_mem c
  -- the residues of the leading forms lie in `L`
  have hform : ∀ (M : ℕ) (s : Finset (ι → ℕ)) (c : (ι → ℕ) → R),
      (∀ β ∈ s, ∑ i, α i * β i = M) →
      residueAlong j P hP (∑ β ∈ s, algebraMap R Y.functionField (c β) *
        (algebraMap R Y.functionField (∏ i, z i ^ β i) / T₀ ^ M)) ∈ L := by
    intro M s c hs
    have hle : ∀ β ∈ s, v (algebraMap R Y.functionField (c β) *
        (algebraMap R Y.functionField (∏ i, z i ^ β i) / T₀ ^ M)) ≤ 1 := by
      intro β hβ
      rw [map_mul, hmon1 M β (hs β hβ), mul_one]; exact hv _
    rw [residueAlong_sum j P hP _ _ hle]
    refine L.sum_mem fun β hβ => ?_
    rw [residueAlong_mul j P hP (hv _) (hmon1 M β (hs β hβ)).le]
    refine L.mul_mem (hres_const _) ?_
    have := hL β
    rwa [hs β hβ] at this
  rw [eq_top_iff]
  intro g _
  obtain ⟨f, hf, rfl⟩ := exists_residueAlong_eq j P hP g
  obtain ⟨M, s, s', c, c', hs, hs', hb, hab⟩ :=
    exists_leadingForms_of_valuation_le_one z α v hv hz hmono T₀ hT hf
  have hale : v (∑ β ∈ s, algebraMap R Y.functionField (c β) *
      (algebraMap R Y.functionField (∏ i, z i ^ β i) / T₀ ^ M)) ≤ 1 :=
    v.map_sum_le fun β hβ => by rw [map_mul, hmon1 M β (hs β hβ), mul_one]; exact hv _
  rw [residueAlong_eq_div_of_sub_lt_one j P hP hf hale hb hab]
  exact L.div_mem (hform M s c hs) (hform M s' c' hs')

/-- **A frame of differentials at a smooth point.** At a point `y` of the smooth locus of a scheme
over `k`, the module `Ω_{𝒪_{X,y}/k}` is free of finite rank. -/
private theorem exists_basis_kaehler_stalk_of_mem_smoothLocus {k : Type} [Field k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) {y : X} (hy : y ∈ Mori.smoothLocus sX) :
    letI := stalkAlgebra sX y
    ∃ n : ℕ, Nonempty (Module.Basis (Fin n) (X.presheaf.stalk y) Ω[X.presheaf.stalk y⁄k]) := by
  obtain ⟨U, hU, hyU⟩ : ∃ U : X.Opens, Smooth (U.ι ≫ sX) ∧ y ∈ U := by
    obtain ⟨U, hU, hyU⟩ := TopologicalSpace.Opens.mem_sSup.1 hy
    exact ⟨U, hU, hyU⟩
  obtain ⟨n, ⟨b⟩, -⟩ := MMP.Threefold.Resolution.exists_basis_kaehler_stalk (sX := U.ι ≫ sX)
    (⟨y, hyU⟩ : U.toScheme)
  letI : Algebra k ((U : Scheme).presheaf.stalk ⟨y, hyU⟩) := stalkAlgebra (U.ι ≫ sX) ⟨y, hyU⟩
  letI : Algebra ((U : Scheme).presheaf.stalk ⟨y, hyU⟩) (X.presheaf.stalk y) :=
    MMP.Positivity.opensStalkIsoAlgebra U ⟨y, hyU⟩
  letI := stalkAlgebra sX y
  haveI : IsScalarTower k ((U : Scheme).presheaf.stalk ⟨y, hyU⟩) (X.presheaf.stalk y) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have h : (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
          X.presheaf.germ ⊤ y (TopologicalSpace.Opens.mem_top _) =
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ sX).appTop ≫
          (U : Scheme).presheaf.germ ⊤ ⟨y, hyU⟩ (TopologicalSpace.Opens.mem_top _)) ≫
          (U.stalkIso ⟨y, hyU⟩).hom := by
      simp only [Category.assoc, Scheme.Opens.germ_stalkIso_hom, Scheme.Hom.comp_appTop]
      congr 2
      exact (X.presheaf.germ_res (homOfLE le_top) _ _).symm
    exact congrArg CommRingCat.Hom.hom h
  have hbij : Function.Bijective (algebraMap ((U : Scheme).presheaf.stalk ⟨y, hyU⟩)
      (X.presheaf.stalk y)) :=
    ConcreteCategory.bijective_of_isIso (U.stalkIso ⟨y, hyU⟩).hom
  haveI : Algebra.FormallyEtale ((U : Scheme).presheaf.stalk ⟨y, hyU⟩) (X.presheaf.stalk y) :=
    Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId _ _) hbij)
  exact ⟨n, ⟨(b.baseChange (X.presheaf.stalk y)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k _ (X.presheaf.stalk y))⟩⟩

/-- **Forms coming from the local ring are regular in codimension one.** On a normal variety of
dimension `d` over a perfect field, the `m`-th power of the image in `Ω^d_{k(X)/k}` of any
`η ∈ Ω^d_{𝒪_{X,Γ}/k}` has nonnegative order along the prime divisor `Γ`. -/
private theorem zero_le_ordForm_formPow_topFormsMap {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] (Γ : Mori.PrimeDivisor X) {d : ℕ} (hd : topologicalKrullDim X = d)
    (m : ℕ) :
    letI := stalkAlgebra sX Γ.genericPoint
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
    ∀ η : ⋀[Γ.localRing]^d Ω[Γ.localRing⁄k],
      0 ≤ Γ.ordForm (show RationalPluriForms sX d m from
        formPow (topFormsMap k Γ.localRing X.functionField d η) m) := by
  letI := stalkAlgebra sX Γ.genericPoint
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
  intro η
  obtain ⟨σ, hσ, h0⟩ := Γ.exists_topForms_generator_of_topologicalKrullDim_eq (sX := sX) hd
  obtain ⟨c, hc⟩ : ∃ c : Γ.localRing, c • σ = η :=
    Submodule.mem_span_singleton.1 (hσ ▸ Submodule.mem_top)
  rw [← hc, LinearMap.map_smul, algebra_compatible_smul X.functionField c, formPow_smul]
  unfold Mori.PrimeDivisor.ordForm
  dsimp only
  rw [ordAt_eq Γ.ord_mul_of_ne_zero
    (fun a ha => Γ.ord_algebraMap_of_isUnit ha) hσ h0]
  unfold formCoeff
  rw [show topFormsMap k Γ.localRing X.functionField d σ = topFormsBasis Γ.localRing hσ h0 () from
    (topFormsBasis_apply hσ h0 ()).symm, repr_smul_formPow]
  by_cases hc0 : algebraMap Γ.localRing X.functionField c ^ m = 0
  · rw [hc0]; simp [Scheme.ord_zero]
  · have hle : Γ.divisorialValuation (algebraMap Γ.localRing X.functionField c ^ m) ≤ 1 := by
      rw [map_pow]
      exact pow_le_one' ((Γ.divisorialValuation_le_one_iff _).2 ⟨c, rfl⟩) m
    rw [Γ.divisorialValuation_eq_exp_neg_ord hc0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle
    omega

/-- **Forms built from regular functions are regular in codimension one.** On a normal variety of
dimension `d` over a perfect field, the `m`-th power of `dv₁ ∧ ⋯ ∧ dv_d`, for `vᵢ ∈ 𝒪_{X,Γ}`, has
nonnegative order along the prime divisor `Γ`. -/
private theorem zero_le_ordForm_formPow_ιMulti_D {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] (Γ : Mori.PrimeDivisor X) {d : ℕ} (hd : topologicalKrullDim X = d)
    (m : ℕ) (v : Fin d → Γ.localRing) :
    letI := stalkAlgebra sX Γ.genericPoint
    letI := functionFieldAlgebra sX
    0 ≤ Γ.ordForm (show RationalPluriForms sX d m from formPow (exteriorPower.ιMulti
      X.functionField d fun i =>
        KaehlerDifferential.D k X.functionField (algebraMap Γ.localRing X.functionField (v i))) m) := by
  letI := stalkAlgebra sX Γ.genericPoint
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
  have himg : topFormsMap k Γ.localRing X.functionField d
      (exteriorPower.ιMulti Γ.localRing d fun i => KaehlerDifferential.D k Γ.localRing (v i)) =
      exteriorPower.ιMulti X.functionField d fun i =>
        KaehlerDifferential.D k X.functionField (algebraMap Γ.localRing X.functionField (v i)) := by
    simp only [topFormsMap_ιMulti, KaehlerDifferential.map_D]
  have h := zero_le_ordForm_formPow_topFormsMap Γ hd m
    (exteriorPower.ιMulti Γ.localRing d fun i => KaehlerDifferential.D k Γ.localRing (v i))
  rwa [himg] at h

/-- **No pole when the residue is constant.** On a normal surface over a perfect field, let `Γ` be
a prime divisor, `w ∈ 𝒪_{X,Γ}` a unit congruent to a constant modulo `𝔪_Γ`, and `x ∈ k(X)^×`.
Then `(dlog x ∧ dlog w)^{⊗m}` has nonnegative order along `Γ`. -/
private theorem zero_le_ordForm_formPow_dlogWedge {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] (Γ : Mori.PrimeDivisor X) (hd : topologicalKrullDim X = (2 : ℕ))
    (m : ℕ) :
    letI := stalkAlgebra sX Γ.genericPoint
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
    ∀ (w : Γ.localRing), IsUnit w → ∀ r : k,
      w - algebraMap k Γ.localRing r ∈ IsLocalRing.maximalIdeal Γ.localRing →
      ∀ x : X.functionField, x ≠ 0 →
        0 ≤ Γ.ordForm (show RationalPluriForms sX 2 m from
          formPow (dlogWedge (k := k) (K := X.functionField) w x) m) := by
  letI := stalkAlgebra sX Γ.genericPoint
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
  haveI := Γ.isDiscreteValuationRing_localRing
  intro w hw r hr x hx
  obtain ⟨η, hη⟩ := dlogWedge_mem_range (k := k) (K := X.functionField) w hw r hr hx
  rw [← hη]
  exact zero_le_ordForm_formPow_topFormsMap Γ hd m η

open Polynomial in
/-- **The toric step along a curve of a surface.** On a normal surface over an algebraically
closed field of characteristic zero, let `Γ` be a prime divisor and `u, w ∈ 𝒪_{X,Γ}` generate
`k(X)`, with `u ∈ 𝔪_Γ` nonzero and `w` a unit. If `(dlog u ∧ dlog w)^{⊗m}` has a pole along `Γ`,
then `u` is a uniformizer of `𝒪_{X,Γ}` and the residue field `k(Γ)` is generated by `w̄`. -/
private theorem irreducible_and_residue_of_ordForm_dlogWedge_neg {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX] (Γ : Mori.PrimeDivisor X)
    (hd : topologicalKrullDim X = (2 : ℕ)) (m : ℕ) :
    letI := stalkAlgebra sX Γ.genericPoint
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
    ∀ (u w : Γ.localRing), u ∈ IsLocalRing.maximalIdeal Γ.localRing → u ≠ 0 → IsUnit w →
      IntermediateField.adjoin k ({algebraMap Γ.localRing X.functionField u,
        algebraMap Γ.localRing X.functionField w} : Set X.functionField) = ⊤ →
      Γ.ordForm (show RationalPluriForms sX 2 m from formPow (dlogWedge (k := k)
        (K := X.functionField) w (algebraMap Γ.localRing X.functionField u)) m) < 0 →
      Irreducible u ∧ ∀ x : Γ.localRing, IsUnit x →
        ∃ p q : k[X], q ≠ 0 ∧ x * (aeval w).toRingHom q - (aeval w).toRingHom p ∈
          IsLocalRing.maximalIdeal Γ.localRing := by
  letI := stalkAlgebra sX Γ.genericPoint
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
  haveI := Γ.isDiscreteValuationRing_localRing
  intro u w hu hu0 hw htop hneg
  rcases forall_isUnit_aeval_or_exists_sub_mem (k := k) w with h | ⟨r, hr⟩
  · exact irreducible_and_residue_of_adjoin_pair_eq_top (K := X.functionField) u w hu hu0 h htop
  · exfalso
    have hu0' : algebraMap Γ.localRing X.functionField u ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hu0
    exact absurd hneg (not_lt.2 (zero_le_ordForm_formPow_dlogWedge Γ hd m w hw r hr _ hu0'))

/-- **Residues and orders along a normal prime divisor.** Let `j : T ⟶ X` be the inclusion of a
normal prime divisor `P` of a normal variety `X` of dimension `e + 1 ≥ 2`, and `w ≠ 0` a rational
`(M + 1)`-canonical form with at most a pole of order `M + 1` along `P`. Then the Poincaré residue
of `w` along `T` vanishes exactly when the pole of `w` along `P` has order at most `M`. -/
private theorem isPoincareResidue_eq_zero_iff {k : Type} [Field k] [CharZero k] {X T : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X]
    [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {e : ℕ}
    (hdim : topologicalKrullDim X = (e + 1 : ℕ)) (he : 0 < e)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X)) {M : ℕ}
    {w : RationalPluriForms sX (e + 1) ((M + 1 : ℕ) : ℤ)} (hw0 : w ≠ 0)
    (hw : -((M + 1 : ℕ) : ℤ) ≤ P.ordForm w) {ρ : RationalPluriForms (j ≫ sX) e ((M + 1 : ℕ) : ℤ)}
    (hρ : IsPoincareResidue sX j e (M + 1) w ρ) :
    ρ = 0 ↔ -(M : ℤ) ≤ P.ordForm w := by
  classical
  haveI : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
  letI := functionFieldAlgebra sX
  have hjT := map_genericPoint_eq_of_range_eq j P hP
  have hdT : topologicalKrullDim T = e := topologicalKrullDim_eq_of_range_eq_support sX j P hP hdim
  obtain ⟨Q⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdT he.ne'
  obtain ⟨σ₁, hσ0, hσP, -, ρσ, hρσ, hρσ0, -⟩ :=
    MMP.Fourfold.exists_form_of_residue_order sX hX (by exact_mod_cast hdim) j hT
      P hP Q
  have hdim' : topologicalKrullDim X = e + 1 := by exact_mod_cast hdim
  set w₀ := MMP.CyclicChartDifferent.Aux.pluriPow σ₁ M
  have hw₀ := MMP.CyclicChartDifferent.Aux.isPoincareResidue_pluriPow P hjT hdim' hρσ M
  have hw₀0 : w₀ ≠ 0 := MMP.CyclicChartDifferent.Aux.pluriPow_ne_zero hdim hσ0 M
  have hw₀T0 : MMP.CyclicChartDifferent.Aux.pluriPow ρσ M ≠ 0 :=
    MMP.CyclicChartDifferent.Aux.pluriPow_ne_zero hdT hρσ0 M
  have hw₀P : P.ordForm w₀ = -((M + 1 : ℕ) : ℤ) := by
    rw [MMP.CyclicChartDifferent.Aux.ordForm_pluriPow hdim hσ0 P M, hσP]; ring
  obtain ⟨b₀⟩ := exists_basis_topForms (sX := sX) (d := e + 1) hdim
  have hrank : Module.finrank X.functionField
      (RationalPluriForms sX (e + 1) ((M + 1 : ℕ) : ℤ)) = 1 := by
    let bb : Module.Basis Unit X.functionField
        (RationalPluriForms sX (e + 1) ((M + 1 : ℕ) : ℤ)) := by exact ZTensorPower.basis b₀ ((M + 1 : ℕ) : ℤ)
    rw [Module.finrank_eq_card_basis bb, Fintype.card_unit]
  obtain ⟨f, hf⟩ := (finrank_eq_one_iff_of_nonzero' w₀ hw₀0).mp hrank w
  have hf0 : f ≠ 0 := by rintro rfl; rw [zero_smul] at hf; exact hw0 hf.symm
  have hord : P.ordForm w = X.ord f P.genericPoint + P.ordForm w₀ := by
    rw [← hf]; exact P.ordForm_smul_of_topologicalKrullDim_eq hdim hf0 hw₀0
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_zero_le_ord P hjT hf0 (by rw [hjT]; omega)
  have hc0 : c ≠ 0 := by rintro rfl; rw [map_zero] at hc; exact hf0 hc.symm
  have hres := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hw₀ c
  rw [hc, hf] at hres
  have huniq := IsPoincareResidue.unique_of_isClosedImmersion P hjT hρ hres
  rw [huniq, smul_eq_zero, or_iff_left hw₀T0, stalkMap_eq_zero_iff,
    ← one_le_ord_iff_mem_maximalIdeal P hjT hc0, hc, hjT]
  omega

end ResidueOrder

section CentreTransport

variable {k : Type} [Field k]

private theorem coeff_eq_zero_of_isPullback_of_forall {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {B : QDivisor Y}
    (hBq : B.IsQCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : QDivisor X} (h : B.IsPullback f hB B') (U : Y.Opens)
    (hU : ∀ E : Mori.PrimeDivisor Y, (E.support ∩ (U : Set Y)).Nonempty → B.coeff E = 0)
    (E : Mori.PrimeDivisor X) (hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty) : B'.coeff E = 0 := by
  set m := B.cartierIndex hBq
  have hm : 0 < m := QDivisor.cartierIndex_pos hBq
  obtain ⟨D0, hD0, hD0c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hBq
  obtain ⟨D0', hD0', hpb⟩ := h m hm D0 hD0 hD0c
  have hφ : D0.IsLocalEquation U 1 := fun E' hE' => by
    have := congrArg (fun G : QDivisor Y => G.coeff E') hD0
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, hU E' hE',
      smul_zero] at this
    rw [Mori.PrimeDivisor.ord_one]; exact_mod_cast this
  have h0 := hpb U 1 hφ E hE
  rw [pullbackComponent_eq _ hφ (E.map_componentGenericPoint_mem f hE)
    (mem_pointComponent _) 1 (by simp), map_one, Mori.PrimeDivisor.ordUnit_one] at h0
  have := congrArg (fun G : QDivisor X => G.coeff E) hD0'
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, h0, Int.cast_zero] at this
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  exact (smul_eq_zero.mp this.symm).resolve_left hm'

private theorem qDivisor_isPullback_zero_of_forall {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {B : QDivisor Y}
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    (U : Y.Opens)
    (hU : ∀ E : Mori.PrimeDivisor Y, (E.support ∩ (U : Set Y)).Nonempty → B.coeff E = 0)
    (hf : Set.range f.base ⊆ U) :
    B.IsPullback f hB 0 := by
  intro m hm D hD _
  refine ⟨0, by simp, Divisor.IsPullback.of_forall_exists fun E => ?_⟩
  have hφ : D.IsLocalEquation U 1 := fun E' hE' => by
    have := congrArg (fun G : QDivisor Y => G.coeff E') hD
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, hU E' hE',
      smul_zero] at this
    rw [Mori.PrimeDivisor.ord_one]; exact_mod_cast this
  have hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty :=
    ⟨E.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
      hf ⟨_, rfl⟩⟩
  refine ⟨U, 1, hφ, hE, ?_⟩
  rw [pullbackComponent_eq _ hφ (E.map_componentGenericPoint_mem f hE)
    (mem_pointComponent _) 1 (by simp), map_one, Mori.PrimeDivisor.ordUnit_one,
    DivisorWithCoeffs.coeff_zero]

/-- **A prime divisor pulled back to zero along a birational morphism is zero.** Let
`α : N ⟶ T` be a proper birational morphism of normal varieties, `ρ` a nonzero rational top form
on `T` with `div ρ + B_T` `ℚ`-Cartier, and suppose `α^*(div ρ + B_T) = 0`. Then `div ρ + B_T = 0`:
along each prime `C` of `T` the strict transform `C_N` has the log discrepancy
`1 - coeff_C B_T = 1 + ord_C ρ`. -/
private theorem eq_zero_of_isPullback_eq_zero [PerfectField k] {T N : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)} [IsIntegral T] [IsNoetherian T] [IsNormal T] [CompactSpace T]
    [LocallyOfFiniteType sT] [IsIntegral N] [IsLocallyNoetherian N] [IsNormal N] [CompactSpace N]
    (hT : IsNormalVariety k sT) (α : N ⟶ T) [IsProper α] (hαb : IsBirational α)
    (hN : IsNormalVariety k (α ≫ sT)) [LocallyOfFiniteType (α ≫ sT)] {d : ℕ}
    (hd : topologicalKrullDim T = d)
    {ρ : RationalPluriForms sT d 1} (hρ : ρ ≠ 0) {BT : QDivisor T}
    (hq : (Divisor.toQDivisor (divisorOfForm ρ) + BT).IsQCartier)
    {hgen : ∀ Z : irreducibleComponents N,
      α (componentGenericPoint N Z) ∉ (Divisor.toQDivisor (divisorOfForm ρ) + BT).supp}
    (hpb : (Divisor.toQDivisor (divisorOfForm ρ) + BT).IsPullback α hgen 0) :
    Divisor.toQDivisor (divisorOfForm ρ) + BT = 0 := by
  haveI := hαb.isDominant
  have hαB : IsBirationalMorphism α := isBirationalMorphism_of_isBirational' α hαb
  have hK := isCanonicalDivisor_divisorOfForm hT hd hρ
  ext C
  obtain ⟨CN, V, hCN, hCV, hViso, hCv⟩ := exists_primeDivisor_map_genericPoint_eq hT α hαb hN C
  have hlogN := isLogDiscrepancy_of_isPullback hT α hαB hN hρ hK hq hpb CN
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy
    (⟨hT, d, divisorOfForm ρ, hK, hq⟩ : Mori.IsPair sT BT) hK (DivisorOver.ofPrimeDivisor k hT C)
  have hc' : c = -BT.coeff C := hc.eq_neg_coeff_of_ofPrimeDivisor hT
  have hlogC := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
    (show IsProper (𝟙 T) by infer_instance)
  have hval : (⟨N, α, hN, hαB, CN⟩ : DivisorOver k sT).valuation =
      (DivisorOver.ofPrimeDivisor k hT C).valuation := by
    ext g
    change CN.divisorialValuation (functionFieldMap α g) =
      C.divisorialValuation (functionFieldMap (𝟙 T) g)
    rw [MMP.Mori.functionFieldMap_id_apply, hCv]
  have he := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlogN hlogC hval
  haveI : IsIso (α.stalkMap CN.genericPoint) :=
    MMP.isIso_stalkMap_of_mem_biregularLocus α
      (le_biregularLocus (f := α) (V := V) hViso (by rw [hCN]; exact hCV))
  have hordC : CN.ordForm (pullbackRationalPluriForms sT α ρ) = C.ordForm ρ :=
    MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso α hαB.functionFieldMap_bijective
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sT) hd) CN C hCN ρ
  rw [hordC, hc', DivisorWithCoeffs.coeff_zero] at he
  rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm,
    DivisorWithCoeffs.coeff_zero]
  have : ((C.ordForm ρ : ℚ) : ℝ) + ((BT.coeff C : ℚ) : ℝ) = 0 := by push_cast at he ⊢; linarith
  exact_mod_cast this

/-- **Crepant transport kills the adjoint divisor along a divisor contracted into a log
generator's domain.** Let `σ : (X, B) ⇢ (X', B')` be a crepant birational map of normal varieties
proper over `k`, `T ⊂ X` a floor divisor `P` with its different `B_T`, and `D` the divisor over
`X'` with the valuation of `P`. Let `τ'` be a rational top form on `X'` with
`div τ' + B' = 0` on an open `U` containing the centre of `D`. Then `τ = σ^*τ'` has a simple pole
along `P`, and its residue `ρ` along `T` satisfies `div ρ + B_T = 0`: on the normalization `N` of
the strict transform of `P` on a common model `W`, the pull-back of `div τ + B` is that of
`div τ' + B'`, which vanishes because `N` maps into `U`. -/
private theorem divisorOfForm_add_eq_zero_of_center_subset [IsAlgClosed k] [CharZero k]
    {X X' T : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsProper sX] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    [LocallyOfFiniteType sX'] [IsProper sX']
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') {n : ℕ}
    (hn : topologicalKrullDim X = (n + 1 : ℕ)) (hn' : topologicalKrullDim X' = (n + 1 : ℕ))
    (hn0 : 0 < n)
    {B : QDivisor X} {B' : QDivisor X'} {K : Divisor X} {K' : Divisor X'}
    (hK : K.IsCanonicalDivisor sX (n + 1)) (hK' : K'.IsCanonicalDivisor sX' (n + 1))
    (hKB : (Divisor.toQDivisor K + B).IsQCartier) (hKB' : (Divisor.toQDivisor K' + B').IsQCartier)
    (σ : FunctionFieldEquiv sX sX') (hσ : IsCrepantBirationalMap sX sX' B B' σ)
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    {ι : T ⟶ X} [IsClosedImmersion ι] {BT : QDivisor T} (hι : IsAdjunctionStep sX B ι BT)
    (P : Mori.PrimeDivisor X) (hrP : Set.range ι.base = (P.support : Set X))
    (hP1 : B.coeff P = 1) (D : DivisorOver k sX') (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g))
    {τ' : RationalPluriForms sX' (n + 1) 1} (hτ'0 : τ' ≠ 0) (U : X'.Opens)
    (hDU : (D.center : Set X') ⊆ U)
    (hU : ∀ E : Mori.PrimeDivisor X', (E.support ∩ (U : Set X')).Nonempty →
      (Divisor.toQDivisor (divisorOfForm τ') + B').coeff E = 0) :
    P.ordForm (pluriformPullback sX sX' σ.toHom (n + 1) 1 τ') = -1 ∧
      ∀ ρ, IsPoincareResidue sX ι n 1 (pluriformPullback sX sX' σ.toHom (n + 1) 1 τ') ρ →
        Divisor.toQDivisor (divisorOfForm ρ) + BT = 0 := by
  have hT := hι.1
  haveI : LocallyOfFiniteType (ι ≫ sX) := hT.1.toLocallyOfFiniteType
  have hdT : topologicalKrullDim T = n := topologicalKrullDim_eq_of_range_eq_support sX ι P hrP hn
  set τ := pluriformPullback sX sX' σ.toHom (n + 1) 1 τ' with hτdef
  have hτ0 : τ ≠ 0 := by
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra sX'
    intro h0
    apply hτ'0
    have e := pluriformPullback_comp (sX := sX') (sX' := sX) (sX'' := sX') hn' hn hn' 1
      (FunctionFieldEquiv.toHom sX' sX σ.symm) σ.toHom τ'
    have h1 : (FunctionFieldEquiv.toHom sX' sX σ.symm).comp σ.toHom =
        FunctionFieldEquiv.toHom sX' sX' 1 := by
      ext a
      exact σ.symm_apply_apply a
    rw [← hτdef, h0, map_zero, h1, pluriformPullback_one hn'] at e
    exact e.symm
  have hD : (Divisor.toQDivisor (divisorOfForm τ) + B).IsQCartier :=
    hKB.add_of_linearlyEquivalent (by
      simpa using (MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK hτ0).symm)
  have hD' : (Divisor.toQDivisor (divisorOfForm τ') + B').IsQCartier :=
    hKB'.add_of_linearlyEquivalent (by
      simpa using (MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX' hK' hτ'0).symm)
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
  -- the strict transform `Q` of `P` on `W` lies over the centre of `D`
  obtain ⟨Q, V, hQP, hPV, hViso, hQv⟩ := exists_primeDivisor_map_genericPoint_eq hX p hpb hWp P
  have hqQ : q Q.genericPoint = D.f D.E.genericPoint := by
    let D1 : DivisorOver k sX' := ⟨W, q, hWq, hqB, Q⟩
    have hv : D1.valuation = D.valuation := by
      ext g
      change Q.divisorialValuation (functionFieldMap q g) = _
      rw [hcompat', hQv, hDv]
    exact MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX'.1 hv
  have hcU : D.f D.E.genericPoint ∈ U := hDU (by
    rw [D.center_eq_closure_genericPoint]; exact subset_closure rfl)
  -- `G` vanishes along `Q`, so `τ` has a simple pole along `P`
  have hGQ : G.coeff Q = 0 := by
    rw [show G = QDivisor.pullback _ hD' hgenG' from hGG']
    exact coeff_eq_zero_of_isPullback_of_forall hD' hG' U hU Q
      ⟨Q.genericPoint, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
        show q Q.genericPoint ∈ U by rw [hqQ]; exact hcU⟩
  have hpiso : IsIso (p.stalkMap Q.genericPoint) :=
    MMP.isIso_stalkMap_of_mem_biregularLocus p
      (le_biregularLocus (f := p) (V := V) hViso (by rw [hQP]; exact hPV))
  have hτP : P.ordForm τ = -1 := by
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
    have hordQ : Q.ordForm (pullbackRationalPluriForms sX p τ) = P.ordForm τ :=
      MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p hpB.functionFieldMap_bijective
        (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn) Q P hQP τ
    rw [hordQ, hc', hGQ, hP1] at he
    have : ((P.ordForm τ : ℤ) : ℝ) = -1 := by push_cast at he ⊢; linarith
    exact_mod_cast this
  refine ⟨hτP, fun ρ hρres => ?_⟩
  obtain ⟨hgenT, hpbT⟩ := hι.isPullback_divisorOfForm_add_of_isPoincareResidue
    (by exact_mod_cast hn) P hrP τ hτ0 hτP ρ hρres hD
  have hρ0 : ρ ≠ 0 := by
    intro h0
    have key := isPoincareResidue_eq_zero_iff (M := 0) sX hX hn hn0 ι hT P hrP hτ0
      (by rw [hτP]; norm_num) hρres
    have := key.mp h0
    rw [hτP] at this
    norm_num at this
  -- the normalization `ν : N ⟶ W` of `Q` and the lift `α : N ⟶ T`
  obtain ⟨N, _, ν, hNv, hνP, hνη, hνsurj⟩ := exists_normalization_primeDivisor' hWp Q
  haveI := hνP
  haveI : IsNormal N := hNv.2
  have hιη := map_genericPoint_eq_of_range_eq ι P hrP
  have hpν : p (ν (genericPoint N)) = ι (genericPoint T) := by rw [hνη, hQP, hιη]
  obtain ⟨α, hα⟩ := exists_comp_eq_of_range_subset ι (ν ≫ p)
    (range_comp_subset_of_map_genericPoint ν p ι P hrP (by rw [hpν, hιη]))
  have hαη : α (genericPoint N) = genericPoint T := ι.isClosedEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hα, Scheme.Hom.comp_apply, hpν])
  haveI : IsDominant α := ⟨Dense.mono (s₁ := {genericPoint T})
    (Set.singleton_subset_iff.mpr ⟨_, hαη⟩) (dense_iff_closure_eq.mpr (genericPoint_spec T))⟩
  haveI : IsNoetherian T := {}
  have hpiso' : IsIso (p.stalkMap (ν (genericPoint N))) := by rw [hνη]; exact hpiso
  have hαs := surjective_functionFieldMap_of_lift p ι ν α hα hpν hpiso' hνsurj
  haveI : IsProper α := by
    have : IsProper (α ≫ ι) := by rw [hα]; infer_instance
    exact IsProper.of_comp α ι
  have hαb : IsBirational α := isBirational_of_surjective_functionFieldMap α hαs
  have hsN : α ≫ ι ≫ sX = ν ≫ p ≫ sX := by rw [← Category.assoc, hα, Category.assoc]
  have hNα : IsNormalVariety k (α ≫ ι ≫ sX) := hsN ▸ hNv
  haveI : LocallyOfFiniteType (α ≫ ι ≫ sX) := hNα.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian (α ≫ ι ≫ sX)
  haveI : CompactSpace N := by
    have := hNα.1
    exact QuasiCompact.compactSpace_of_compactSpace (α ≫ ι ≫ sX)
  -- `H = (ν ≫ p)^*(div τ + B)`, computed through `T` and through `W`
  have hDP : (Divisor.toQDivisor (divisorOfForm τ) + B).coeff P = 0 := by
    rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hτP, hP1]
    norm_num
  have hgenH : ∀ Z : irreducibleComponents N,
      (ν ≫ p) (componentGenericPoint N Z) ∉ (Divisor.toQDivisor (divisorOfForm τ) + B).supp := by
    intro Z
    rw [componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply, hpν, hιη]
    exact genericPoint_notMem_supp_of_coeff_eq_zero hDP
  have hH := QDivisor.isPullback_pullback hD hgenH
  set H := QDivisor.pullback _ hD hgenH
  have hqT := isQCartier_of_isPullback hD hpbT
  have hgenα := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' α
    (Divisor.toQDivisor (divisorOfForm ρ) + BT)
  have hEα := QDivisor.isPullback_pullback hqT hgenα
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
  have hcU' : ∀ z : N, (ν ≫ q) z ∈ U := by
    intro z
    apply hDU
    rw [D.center_eq_closure_genericPoint, ← hqQ, ← hνη]
    have hz : genericPoint N ⤳ z := (genericPoint_spec N).specializes trivial
    exact specializes_iff_mem_closure.mp (hz.map (ν ≫ q).base.hom.continuous)
  have hgenH' : ∀ Z : irreducibleComponents N,
      (ν ≫ q) (componentGenericPoint N Z) ∉ (Divisor.toQDivisor (divisorOfForm τ') + B').supp := by
    intro Z hZ
    obtain ⟨E, hE, hzE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
    exact hE (hU E ⟨_, hzE, hcU' _⟩)
  have hH' : (Divisor.toQDivisor (divisorOfForm τ') + B').IsPullback (ν ≫ q) hgenH' H := by
    rw [hHHν]
    exact qDivisor_isPullback_comp' q ν hG' (isPullback_of_eq_source (h₂ := hgenν') hGG' hHν)
      hgenH'
  have hH0 : H = 0 :=
    (QDivisor.IsQCartier.existsUnique_isPullback hD' hgenH').unique hH'
      (qDivisor_isPullback_zero_of_forall U hU (by rintro _ ⟨z, rfl⟩; exact hcU' z))
  have hpb0 : (Divisor.toQDivisor (divisorOfForm ρ) + BT).IsPullback α hgenα 0 := by
    rw [← hH0, hHα]; exact hEα
  exact eq_zero_of_isPullback_eq_zero hT α hαb hNα hdT hρ0 hqT hpb0

end CentreTransport

section SNCLogGenerator

open KaehlerDifferential in
private theorem span_D_algebraMap_eq_top_of_isLocalization {k A B : Type*} [CommRing k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (S : Submonoid A) [IsLocalization S B] {ι : Type*} (w : ι → A)
    (hw : Submodule.span A (Set.range fun i => KaehlerDifferential.D k A (w i)) = ⊤) :
    Submodule.span B (Set.range fun i => KaehlerDifferential.D k B (algebraMap A B (w i))) = ⊤ := by
  set N := Submodule.span B (Set.range fun i => KaehlerDifferential.D k B (algebraMap A B (w i)))
  have hA : ∀ a : A, KaehlerDifferential.D k B (algebraMap A B a) ∈ N := by
    intro a
    have ha : KaehlerDifferential.D k A a ∈ Submodule.span A (Set.range fun i => KaehlerDifferential.D k A (w i)) := hw ▸ Submodule.mem_top
    have hmap : ∀ y ∈ Submodule.span A (Set.range fun i => KaehlerDifferential.D k A (w i)),
        KaehlerDifferential.map k k A B y ∈ N := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        rw [KaehlerDifferential.map_D]
        exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add y y' _ _ h h' => rw [map_add]; exact N.add_mem h h'
      | smul r y _ h =>
        rw [LinearMap.map_smul_of_tower, ← algebraMap_smul B r]
        exact N.smul_mem _ h
    have := hmap _ ha
    rwa [KaehlerDifferential.map_D] at this
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  obtain ⟨⟨r, s⟩, hb⟩ := IsLocalization.mk'_surjective S b
  dsimp only at hb
  subst hb
  have hs : IsUnit (algebraMap A B s) := IsLocalization.map_units B s
  have e : algebraMap A B s * IsLocalization.mk' B r s = algebraMap A B r :=
    IsLocalization.mul_mk'_eq_mk'_of_mul _ _ _ |>.trans (by simp)
  have h1 := congrArg (KaehlerDifferential.D k B) e
  rw [Derivation.leibniz] at h1
  have h2 : algebraMap A B s • KaehlerDifferential.D k B (IsLocalization.mk' B r s) =
      KaehlerDifferential.D k B (algebraMap A B r) - IsLocalization.mk' B r s • KaehlerDifferential.D k B (algebraMap A B s) := by
    rw [← h1]; abel
  have h3 : KaehlerDifferential.D k B (IsLocalization.mk' B r s) =
      (hs.unit⁻¹ : Bˣ).val • (KaehlerDifferential.D k B (algebraMap A B r) -
        IsLocalization.mk' B r s • KaehlerDifferential.D k B (algebraMap A B s)) := by
    rw [← h2, smul_smul, IsUnit.val_inv_mul, one_smul]
  change KaehlerDifferential.D k B (IsLocalization.mk' B r s) ∈ N
  rw [h3]
  exact N.smul_mem _ (N.sub_mem (hA r) (N.smul_mem _ (hA s)))

open KaehlerDifferential in
private theorem span_D_eq_top_of_span_eq_maximalIdeal {k O : Type*} [Field k] [CommRing O]
    [IsLocalRing O] [Algebra k O] [Module.Finite O Ω[O⁄k]]
    (hres : Function.Surjective (algebraMap k (IsLocalRing.ResidueField O)))
    {ι : Type*} (z : ι → O) (hz : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal O) :
    Submodule.span O (Set.range fun i => KaehlerDifferential.D k O (z i)) = ⊤ := by
  rw [← IsLocalRing.map_tensorProduct_mk_eq_top]
  set L := IsLocalRing.ResidueField O
  have hπ : Function.Surjective (algebraMap O L) := IsLocalRing.residue_surjective
  have hexact := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k O L hπ
  haveI : Subsingleton Ω[L⁄k] := subsingleton_of_surjective k L hres
  have hker : RingHom.ker (algebraMap O L) = IsLocalRing.maximalIdeal O := by
    ext a; simp [L, IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
  rw [Submodule.map_span, eq_top_iff]
  rintro y -
  obtain ⟨c, rfl⟩ := (hexact y).mp (Subsingleton.elim _ _)
  obtain ⟨⟨a, ha⟩, rfl⟩ := Ideal.toCotangent_surjective _ c
  rw [KaehlerDifferential.kerCotangentToTensor_toCotangent]
  change (1 : L) ⊗ₜ[O] KaehlerDifferential.D k O a ∈ _
  have ha' : a ∈ Ideal.span (Set.range z) := by rw [hz, ← hker]; exact ha
  clear ha
  induction ha' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Submodule.subset_span ⟨D k O (z i), ⟨i, rfl⟩, by simp⟩
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [map_add, TensorProduct.tmul_add]
    exact Submodule.add_mem _ ihx ihy
  | smul r x hx ih =>
    rw [smul_eq_mul, Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul,
      TensorProduct.tmul_smul]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ih) ?_
    have : algebraMap O L x = 0 := by
      rw [← RingHom.mem_ker, hker, ← hz]; exact hx
    rw [← algebraMap_smul L x, this, zero_smul]
    exact Submodule.zero_mem _

/-- The stalk algebras are compatible with generization. -/
private theorem isScalarTower_stalkSpecializes {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) {y x : X} (h : y ⤳ x) :
    letI := stalkAlgebra sX x
    letI := stalkAlgebra sX y
    letI := (X.presheaf.stalkSpecializes h).hom.toAlgebra
    IsScalarTower k (X.presheaf.stalk x) (X.presheaf.stalk y) := by
  letI := stalkAlgebra sX x
  letI := stalkAlgebra sX y
  letI := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  have e : (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ y (TopologicalSpace.Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top _)) ≫
        X.presheaf.stalkSpecializes h := by
    simp
  exact congrArg CommRingCat.Hom.hom e

/-- **Orders of forms built on a frame at a point.** Let `w₁, …, w_d ∈ 𝒪_{X,x}` have
differentials spanning `Ω_{𝒪_{X,x}/k}`, `d = dim X`. Along every prime divisor `Γ` through `x`,
the order of `a • (dw₁ ∧ ⋯ ∧ dw_d)^{⊗m}` is `ord_Γ(a)`. -/
private theorem ordForm_smul_formPow_ιMulti_D_eq {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] {d : ℕ} (hd : topologicalKrullDim X = d) (m : ℕ) {x : X}
    (Γ : Mori.PrimeDivisor X) (hΓ : x ∈ Γ.support) (w : Fin d → X.presheaf.stalk x)
    (hw : letI := stalkAlgebra sX x
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun i => KaehlerDifferential.D k (X.presheaf.stalk x) (w i)) = ⊤)
    (a : X.functionField) :
    letI := functionFieldAlgebra sX
    Γ.ordForm (show RationalPluriForms sX d m from a • formPow (exteriorPower.ιMulti
      X.functionField d fun i => KaehlerDifferential.D k X.functionField
        (algebraMap (X.presheaf.stalk x) X.functionField (w i))) m) =
      X.ord a Γ.genericPoint := by
  set h := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support Γ hΓ
  letI := stalkAlgebra sX x
  letI := stalkAlgebra sX Γ.genericPoint
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
  letI := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  haveI := isScalarTower_stalkSpecializes sX h
  haveI := MMP.Intersection.isLocalization_stalkSpecializes h
  set w' : Fin d → Ω[(X.presheaf.stalk Γ.genericPoint)⁄k] := fun i =>
    KaehlerDifferential.D k _ ((X.presheaf.stalkSpecializes h).hom (w i))
  have hw' : Submodule.span (X.presheaf.stalk Γ.genericPoint) (Set.range w') = ⊤ :=
    span_D_algebraMap_eq_top_of_isLocalization
      (Ideal.comap (X.presheaf.stalkSpecializes h).hom
        (IsLocalRing.maximalIdeal (X.presheaf.stalk Γ.genericPoint))).primeCompl w hw
  have himg : topFormsMap k (X.presheaf.stalk Γ.genericPoint) X.functionField d
      (exteriorPower.ιMulti _ d w') = exteriorPower.ιMulti X.functionField d fun i =>
        KaehlerDifferential.D k X.functionField
          (algebraMap (X.presheaf.stalk x) X.functionField (w i)) := by
    simp only [w', topFormsMap_ιMulti, KaehlerDifferential.map_D, Mori.algebraMap_stalkSpecializes]
  have h0 : topFormsMap k (X.presheaf.stalk Γ.genericPoint) X.functionField d
      (exteriorPower.ιMulti _ d w') ≠ 0 := by
    obtain ⟨σ, -, hσ0⟩ := Γ.exists_topForms_generator_of_topologicalKrullDim_eq (sX := sX) hd
    obtain ⟨c, hc⟩ : ∃ c : X.presheaf.stalk Γ.genericPoint, c • exteriorPower.ιMulti _ d w' = σ :=
      Submodule.mem_span_singleton.1 (MMP.Fourfold.span_singleton_ιMulti_eq_top w' hw' ▸
        Submodule.mem_top)
    intro h0
    apply hσ0
    rw [← hc, LinearMap.map_smul_of_tower, h0, smul_zero]
  refine MMP.CyclicChartDifferent.ordForm_eq_of_frame Γ rfl w' hw' h0 a _ ?_
  rw [himg]
  rfl

open Classical in
/-- **Orders of local equations along prime divisors through a point.** Let `E` be a prime
divisor through `x` with ideal `(y)` at `x`. Along a prime divisor `Γ` through `x`, `y` has order
one if `Γ = E` and is a unit otherwise. -/
private theorem ord_algebraMap_eq_ite_of_stalk_eq_span {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {x : X} (Γ : Mori.PrimeDivisor X) (hΓ : x ∈ Γ.support)
    (E : Mori.PrimeDivisor X) (hE : x ∈ E.support) {y : X.presheaf.stalk x}
    (hy : IdealSheafData.stalk E.idealSheaf x = Ideal.span {y}) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField y) Γ.genericPoint =
      if Γ = E then 1 else 0 := by
  set h := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support Γ hΓ
  rw [← Mori.algebraMap_stalkSpecializes h]
  haveI := Γ.isDiscreteValuationRing_localRing
  split_ifs with hΓE
  · subst hΓE
    obtain ⟨hm, -⟩ := maximalIdeal_eq_span_and_isUnit_at_genericPoint Γ hΓ hy
    have hirr : Irreducible ((X.presheaf.stalkSpecializes h).hom y) :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hm
    have h0 : algebraMap (X.presheaf.stalk Γ.genericPoint) X.functionField
        ((X.presheaf.stalkSpecializes h).hom y) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hirr.ne_zero
    exact (Scheme.ord_eq_iff Γ.coheight_genericPoint h0).mpr (Ring.ordFrac_irreducible hirr)
  · have hu : IsUnit ((X.presheaf.stalkSpecializes h).hom y) := by
      by_contra hnu
      have hmem : (X.presheaf.stalkSpecializes h).hom y ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk Γ.genericPoint) :=
        (IsLocalRing.mem_maximalIdeal _).2 hnu
      have hle : IdealSheafData.stalk E.idealSheaf x ≤ MMP.Intersection.primeOfSpecializes h := by
        rw [hy, Ideal.span_le, Set.singleton_subset_iff]
        exact hmem
      have hgen := (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes E.idealSheaf h).2 hle
      exact hΓE (MMP.Positivity.PrimeDivisor.eq_of_genericPoint_specializes
        (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hgen)).symm
    exact Γ.ord_algebraMap_of_isUnit hu

private theorem ord_prod_inv_pow {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {ι : Type*} (s : Finset ι) {f : ι → X.functionField} (hf : ∀ a, f a ≠ 0) (y : X) (m : ℕ) :
    X.ord ((∏ a ∈ s, (f a)⁻¹) ^ m) y = -((m : ℤ) * ∑ a ∈ s, X.ord (f a) y) := by
  have h0 : X.ord (1 : X.functionField) y = 0 := by
    have := Scheme.ord_of_isUnit (U := ⊤) (f := (1 : Γ(X, ⊤))) isUnit_one (x := y) trivial
    simpa using this
  have hinv : ∀ a, X.ord (f a)⁻¹ y = -X.ord (f a) y := fun a => by
    have := Scheme.ord_mul (x := y) (hf a) (inv_ne_zero (hf a))
    rw [mul_inv_cancel₀ (hf a), h0] at this
    omega
  have hprod : ∀ t : Finset ι, X.ord (∏ a ∈ t, (f a)⁻¹) y = -∑ a ∈ t, X.ord (f a) y := by
    classical
    intro t
    induction t using Finset.induction_on with
    | empty => simp [h0]
    | insert b t hb ih =>
      rw [Finset.prod_insert hb, Scheme.ord_mul (inv_ne_zero (hf b))
        (Finset.prod_ne_zero_iff.2 fun a _ => inv_ne_zero (hf a)), ih, hinv,
        Finset.sum_insert hb]
      ring
  have hne : (∏ a ∈ s, (f a)⁻¹) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => inv_ne_zero (hf a)
  induction m with
  | zero => simp [h0]
  | succ n ih =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero _ hne) hne, ih, hprod]
    push_cast
    ring

open Classical in
/-- **The snc log generator.** Let `z₁, …, z_d ∈ 𝒪_{X,x}` (`d = dim X`) be nonzero with
differentials spanning `Ω_{𝒪_{X,x}/k}`, and `L₁, …, L_d` distinct prime divisors through `x` with
ideals `(z_a)` at `x`. Along a prime divisor `Γ` through `x`, the form
`(dlog z₁ ∧ ⋯ ∧ dlog z_d)^{⊗m}` has order `-m` if `Γ` is one of the `L_a` and `0` otherwise. -/
private theorem ordForm_formPow_dlog_eq {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] {d : ℕ} (hd : topologicalKrullDim X = d) (m : ℕ) {x : X}
    (z : Fin d → X.presheaf.stalk x) (hz0 : ∀ a, z a ≠ 0)
    (hw : letI := stalkAlgebra sX x
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun i => KaehlerDifferential.D k (X.presheaf.stalk x) (z i)) = ⊤)
    (L : Fin d → Mori.PrimeDivisor X) (hL : Function.Injective L) (hLx : ∀ a, x ∈ (L a).support)
    (hLz : ∀ a, IdealSheafData.stalk (L a).idealSheaf x = Ideal.span {z a})
    (Γ : Mori.PrimeDivisor X) (hΓ : x ∈ Γ.support) :
    letI := functionFieldAlgebra sX
    Γ.ordForm (show RationalPluriForms sX d m from formPow (exteriorPower.ιMulti
      X.functionField d fun a =>
        (algebraMap (X.presheaf.stalk x) X.functionField (z a))⁻¹ • KaehlerDifferential.D k
          X.functionField (algebraMap (X.presheaf.stalk x) X.functionField (z a))) m) =
      if Γ ∈ Set.range L then -(m : ℤ) else 0 := by
  letI := functionFieldAlgebra sX
  set f : Fin d → X.functionField := fun a => algebraMap (X.presheaf.stalk x) X.functionField (z a)
  have hf : ∀ a, f a ≠ 0 := fun a =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hz0 a)
  have hsplit : (exteriorPower.ιMulti X.functionField d fun a =>
      (f a)⁻¹ • KaehlerDifferential.D k X.functionField (f a)) =
      (∏ a, (f a)⁻¹) • exteriorPower.ιMulti X.functionField d fun a =>
        KaehlerDifferential.D k X.functionField (f a) := by
    rw [← AlternatingMap.map_smul_univ]
  change Γ.ordForm (show RationalPluriForms sX d m from formPow (exteriorPower.ιMulti
      X.functionField d fun a => (f a)⁻¹ • KaehlerDifferential.D k X.functionField (f a)) m) = _
  rw [hsplit, formPow_smul', ordForm_smul_formPow_ιMulti_D_eq hd m Γ hΓ z hw,
    ord_prod_inv_pow Finset.univ hf]
  simp only [f]
  rw [Finset.sum_congr rfl fun a _ => ord_algebraMap_eq_ite_of_stalk_eq_span Γ hΓ (L a) (hLx a)
    (hLz a)]
  split_ifs with hmem
  · obtain ⟨a₀, rfl⟩ := hmem
    rw [Finset.sum_eq_single a₀ (fun b _ hb => if_neg fun h => hb (hL h).symm)
      (fun h => absurd (Finset.mem_univ a₀) h), if_pos rfl]
    ring
  · rw [Finset.sum_eq_zero fun a _ => if_neg fun h => hmem ⟨a, h.symm⟩]
    ring

end SNCLogGenerator

section SNCCentre

open MMP.Threefold.Mori.Helpers in
/-- **Raising the boundary through the centre strictly lowers the discrepancy.** If `Δ'` is
effective with positive coefficient along a prime divisor through the centre of `D`, then
`a(D, X, Δ + Δ') < a(D, X, Δ)`. -/
private theorem isDiscrepancy_lt_of_effective {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ Δ' : QDivisor X}
    (hΔ'e : Δ'.IsEffective) {D : DivisorOver k sX} {a a' : ℚ}
    (ha : IsDiscrepancy sX n K Δ D a) (ha' : IsDiscrepancy sX n K (Δ + Δ') D a')
    {Γ₀ : Mori.PrimeDivisor X} (hΓ₀ : D.f D.E.genericPoint ∈ Γ₀.support)
    (hpos : 0 < Δ'.coeff Γ₀) : a' < a := by
  obtain ⟨hX, hK, m, hm, -, U, hU, τ, hτ, hτa⟩ := ha
  obtain ⟨-, -, m', hm', -, U', hU', τ', hτ', hτa'⟩ := ha'
  let := functionFieldAlgebra sX
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hn := hK.topologicalKrullDim_eq
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b, N, hN⟩ := D.exists_ordPullback_eq hX hn
  set c := (ZTensorPower.basis b m).repr τ () with hc_def
  set c' := (ZTensorPower.basis b m').repr τ' () with hc'_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hτ.1
  have hc' : c' ≠ 0 := repr_ne_zero_of_ne_zero b hτ'.1
  set g : X.functionField := c ^ (m' : ℤ) * c' ^ (-(m : ℤ)) with hg_def
  have hg : g ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (zpow_ne_zero _ hc')
  have hordeq : ∀ Γ : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ Γ.support →
      (X.ord g Γ.genericPoint : ℚ) = (m : ℚ) * m' * Δ'.coeff Γ := by
    intro Γ hΓ
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    have e1 := hτ.2 Γ ⟨_, hΓ, hU⟩
    have e2 := hτ'.2 Γ ⟨_, hΓ, hU'⟩
    have f1 : (Γ.ordForm τ : ℚ) = (X.ord c Γ.genericPoint : ℚ) + m * NΓ := by
      exact_mod_cast hNΓ m τ hτ.1
    have f2 : (Γ.ordForm τ' : ℚ) = (X.ord c' Γ.genericPoint : ℚ) + m' * NΓ := by
      exact_mod_cast hNΓ m' τ' hτ'.1
    rw [hg_def, Scheme.ord_mul (zpow_ne_zero _ hc) (zpow_ne_zero _ hc'), ord_zpow _ hc,
      ord_zpow _ hc']
    rw [DivisorWithCoeffs.coeff_add] at e2
    push_cast
    linear_combination (m' : ℚ) * e1 - (m : ℚ) * e2 - (m' : ℚ) * f1 + (m : ℚ) * f2
  have hord : ∀ Γ : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ Γ.support →
      0 ≤ X.ord g Γ.genericPoint := by
    intro Γ hΓ
    have h1 := hordeq Γ hΓ
    have h2 : (0 : ℚ) ≤ (m : ℚ) * m' * Δ'.coeff Γ := by
      have := hΔ'e Γ
      positivity
    exact_mod_cast h1 ▸ h2
  obtain ⟨r, hr⟩ := exists_algebraMap_stalk_eq_of_forall_ord_nonneg _ hg hord
  have hr0 : r ≠ 0 := by rintro rfl; rw [map_zero] at hr; exact hg hr.symm
  have hrm : r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (D.f D.E.genericPoint)) := by
    by_contra hnu
    have hu : IsUnit r := by simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hnu
    have hsp : Γ₀.genericPoint ⤳ D.f D.E.genericPoint := specializes_iff_mem_closure.mpr (by
      rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact hΓ₀)
    have h0 := Γ₀.ord_algebraMap_of_isUnit (hu.map (X.presheaf.stalkSpecializes hsp).hom)
    rw [Mori.algebraMap_stalkSpecializes, hr] at h0
    have h1 := hordeq Γ₀ hΓ₀
    rw [h0] at h1
    have : (0 : ℚ) < (m : ℚ) * m' * Δ'.coeff Γ₀ := by positivity
    push_cast at h1
    linarith
  set r' := (D.f.stalkMap D.E.genericPoint).hom r
  have hr' : algebraMap _ D.Y.functionField r' = functionFieldMap D.f g := by
    rw [← hr, functionFieldMap_algebraMap_stalk]
  have hr'0 : r' ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at hr'
    exact (map_ne_zero _).mpr hg hr'.symm
  have hr'm : r' ∈ IsLocalRing.maximalIdeal (D.Y.presheaf.stalk D.E.genericPoint) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).mp hrm (isUnit_of_map_unit _ _ hu)
  have hE := (one_le_ord_iff_mem_maximalIdeal D.E rfl hr'0).mpr hr'm
  rw [hr'] at hE
  have hfc : functionFieldMap D.f c ≠ 0 := (map_ne_zero _).mpr hc
  have hfc' : functionFieldMap D.f c' ≠ 0 := (map_ne_zero _).mpr hc'
  rw [hg_def, map_mul, map_zpow₀, map_zpow₀,
    Scheme.ord_mul (zpow_ne_zero _ hfc) (zpow_ne_zero _ hfc'), ord_zpow _ hfc, ord_zpow _ hfc']
    at hE
  have hY1 : (1 : ℚ) ≤ ((m' : ℚ) * D.Y.ord (functionFieldMap D.f c) D.E.genericPoint +
      -(m : ℚ) * D.Y.ord (functionFieldMap D.f c') D.E.genericPoint) := by
    exact_mod_cast hE
  have h1 : (D.ordPullback τ : ℚ) =
      (D.Y.ord (functionFieldMap D.f c) D.E.genericPoint : ℚ) + m * N := by
    exact_mod_cast hN m τ hτ.1
  have h2 : (D.ordPullback τ' : ℚ) =
      (D.Y.ord (functionFieldMap D.f c') D.E.genericPoint : ℚ) + m' * N := by
    exact_mod_cast hN m' τ' hτ'.1
  have key : (m : ℚ) * m' * (a - a') =
      ((m' : ℚ) * D.Y.ord (functionFieldMap D.f c) D.E.genericPoint +
      -(m : ℚ) * D.Y.ord (functionFieldMap D.f c') D.E.genericPoint) := by
    linear_combination (m' : ℚ) * hτa - (m : ℚ) * hτa' + (m' : ℚ) * h1 - (m : ℚ) * h2
  have hm0 : (0 : ℚ) < (m : ℚ) * m' := by positivity
  nlinarith

/-- **Boundary components through a log canonical place of a dlt pair have coefficient one.**
Let `(X, B)` be a dlt pair and `D` a proper divisor over `X` with discrepancy `-1`. Every prime
divisor of `Supp B` through the centre of `D` has coefficient one: on the snc open around the
centre, raising such a coefficient to one would strictly lower the discrepancy below `-1`. -/
private theorem coeff_eq_one_of_isDiscrepancy_neg_one {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {B : QDivisor X} (hdlt : MMP.Intersection.IsDltPair sX B) {n : ℕ}
    {K : Divisor X} (hP : MMP.Mori.IsPairWith sX n K B) (D : DivisorOver k sX)
    (hDp : IsProper D.f) (hD : MMP.Mori.IsDiscrepancy sX n K B D (-1))
    (G : Mori.PrimeDivisor X) (hG : D.f D.E.genericPoint ∈ G.support) (hG0 : B.coeff G ≠ 0) :
    B.coeff G = 1 := by
  classical
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hD hDp
  norm_num at hlog
  obtain ⟨U, hηU, hsm, hsnc⟩ := exists_snc_open_of_isDltPair hdlt D hlog
  have hB : ∀ P, 0 ≤ B.coeff P ∧ B.coeff P ≤ 1 := fun P => ⟨hdlt.1.2.1 P, hdlt.2.1 P⟩
  have hU : ((D.center : Set X) ∩ U).Nonempty := ⟨_, by
    rw [D.center_eq_closure_genericPoint]; exact subset_closure rfl, hηU⟩
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  haveI : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨_, hηU⟩)
  obtain ⟨hY, hf, E', hE', -, hiff⟩ := MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff hP D U hU
  set T := MMP.Intersection.reducedDivisorOf (B.restrictOpen U).support with hT
  have hD' := (hiff (-1)).1 hD
  have hΔe : (Divisor.toQDivisor T - B.restrictOpen U).IsEffective := by
    intro P
    obtain ⟨h0, h1⟩ := hB (OpenWeilRestriction.primeDivisorMap U.ι P)
    rw [DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor, hT,
      MMP.Intersection.coeff_reducedDivisorOf, DivisorWithCoeffs.coeff_restrictOpen]
    split_ifs with hmem
    · push_cast; linarith
    · have : (B.restrictOpen U).coeff P = 0 := by
        by_contra hne
        exact hmem (Finsupp.mem_support_iff.2 hne)
      rw [DivisorWithCoeffs.coeff_restrictOpen] at this
      rw [this]; simp
  have hΔq := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
    (Divisor.toQDivisor T - B.restrictOpen U)
  obtain ⟨a', hle, ha'⟩ := MMP.Threefold.Mori.Helpers.exists_isDiscrepancy_add_le hΔe hΔq hD'
  have hpU : IsProper (D.f ∣_ U) := by haveI := hDp; infer_instance
  have hla := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha' hpU
  rw [add_sub_cancel, QDivisor.toRDivisor_toQDivisor] at hla
  obtain ⟨N, hN⟩ := MMP.Intersection.IsLogDiscrepancy.exists_nat_eq_of_isSNC _
    (hP.1.restrictOpen U).1 hsm (MMP.Intersection.isReducedEffective_reducedDivisorOf _)
    (hsnc.of_support_subset (by rw [MMP.Intersection.support_reducedDivisorOf])) hla
  have h1 : (-1 : ℚ) ≤ a' := by
    have : (0 : ℝ) ≤ 1 + (a' : ℝ) := hN ▸ Nat.cast_nonneg N
    exact_mod_cast (by linarith : (-1 : ℝ) ≤ a')
  -- the restriction of `G` to `U`
  obtain ⟨GU, hGU⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    U.ι G ⟨_, hηU⟩ hG
  have hcen : (D.f ∣_ U) E'.genericPoint ∈ GU.support := by
    rw [← MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι, hGU]
    have hιE : (D.f ⁻¹ᵁ U).ι E'.genericPoint = D.E.genericPoint := by
      rw [← hE']
      exact (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hιE]
    exact hG
  by_contra hne
  have hlt1 : B.coeff G < 1 := lt_of_le_of_ne (hB G).2 hne
  have hmemU : GU ∈ (B.restrictOpen U).support := by
    refine Finsupp.mem_support_iff.2 ?_
    change B.coeff (OpenWeilRestriction.primeDivisorMap U.ι GU) ≠ 0
    rw [hGU]
    exact hG0
  have hpos : 0 < (Divisor.toQDivisor T - B.restrictOpen U).coeff GU := by
    rw [DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor, hT,
      MMP.Intersection.coeff_reducedDivisorOf, DivisorWithCoeffs.coeff_restrictOpen, hGU,
      if_pos hmemU]
    push_cast; linarith
  have := isDiscrepancy_lt_of_effective hΔe hD' ha' hcen hpos
  linarith

/-- **Centres are compatible with restriction to an open subset.** -/
private theorem map_genericPoint_eq_of_valuation_eq_comap {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (hX : MMP.Mori.IsVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] (D : DivisorOver k sX) (D'' : DivisorOver k (U.ι ≫ sX))
    (hv : D.valuation = D''.valuation.comap (functionFieldMap U.ι)) :
    U.ι (D''.f D''.E.genericPoint) = D.f D.E.genericPoint := by
  haveI := hX.toIsSeparated
  set y := D''.f D''.E.genericPoint
  have hval : ∀ a : X.presheaf.stalk (U.ι y), D.valuation (algebraMap _ X.functionField a) =
      D''.valuation (algebraMap _ (U : Scheme).functionField ((U.ι.stalkMap y).hom a)) := by
    intro a
    rw [hv, Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
  refine MMP.Positivity.DivisorOver.eq_of_dominates sX D.valuation (x := U.ι y) ?_ ?_
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D _ rfl)
  · intro a
    rw [hval]
    exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D'' _ rfl _
  · intro a ha
    rw [hval]
    refine MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D'' _ rfl _ ?_
    exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)

/-- Ring maps carry weighted monomial ideals to weighted monomial ideals. -/
private theorem map_weightedMonomialIdeal {R S : Type*} [CommRing R] [CommRing S] {ι : Type*}
    [Fintype ι] (φ : R →+* S) (z : ι → R) (α : ι → ℕ) (m : ℕ) :
    Ideal.map φ (weightedMonomialIdeal z α m) = weightedMonomialIdeal (fun i => φ (z i)) α m := by
  rw [weightedMonomialIdeal, Ideal.map_span, weightedMonomialIdeal]
  congr 1
  ext r
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨β, hβ, rfl⟩, rfl⟩
    exact ⟨β, hβ, by simp [map_prod, map_pow]⟩
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨_, ⟨β, hβ, rfl⟩, by simp [map_prod, map_pow]⟩

/-- Weighted monomial ideals do not depend on the indexing. -/
private theorem weightedMonomialIdeal_comp_equiv {R : Type*} [CommRing R] {ι κ : Type*}
    [Fintype ι] [Fintype κ] (e : κ ≃ ι) (z : ι → R) (α : ι → ℕ) (m : ℕ) :
    weightedMonomialIdeal (fun j => z (e j)) (fun j => α (e j)) m = weightedMonomialIdeal z α m := by
  rw [weightedMonomialIdeal, weightedMonomialIdeal]
  congr 1
  ext r
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨fun i => β (e.symm i), ?_, ?_⟩
    · rw [← Equiv.sum_comp e]; simpa using hβ
    · rw [← Equiv.prod_comp e]; simp
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨fun j => β (e j), ?_, ?_⟩
    · rw [Equiv.sum_comp e (fun i => α i * β i)]; exact hβ
    · exact (Equiv.prod_comp e (fun i => z i ^ β i)).symm

/-- A monomial of positive weight lies in the ideal generated by the variables. -/
private theorem weightedMonomialIdeal_le_span {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (z : ι → R) (α : ι → ℕ) {m : ℕ} (hm : 1 ≤ m) :
    weightedMonomialIdeal z α m ≤ Ideal.span (Set.range z) := by
  classical
  refine Ideal.span_le.mpr ?_
  rintro r ⟨β, hβ, rfl⟩
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, 0 < α i * β i := by
    by_contra h
    push Not at h
    have : ∑ i, α i * β i = 0 := Finset.sum_eq_zero fun i hi => by have := h i hi; omega
    omega
  have hβi : 0 < β i := by
    rcases Nat.eq_zero_or_pos (β i) with h | h
    · rw [h, mul_zero] at hi; omega
    · exact h
  rw [SetLike.mem_coe, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  refine Ideal.mul_mem_right _ _ ?_
  rw [← Nat.succ_pred_eq_of_pos hβi, pow_succ]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- A member of a regular system of parameters is not in the ideal of the others. -/
private theorem notMem_span_image_compl_of_isRegularSystemOfParameters {A : Type*} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {n : ℕ} {z : Fin n → A}
    (hz : IsRegularSystemOfParameters z) (b : Fin n) :
    z b ∉ Ideal.span (z '' ({b}ᶜ : Finset (Fin n))) := by
  intro hmem
  haveI : IsRegularLocalRing A := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  obtain ⟨hreg, hdim, -⟩ :=
    MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz ({b}ᶜ : Finset (Fin n))
  set I := Ideal.span (z '' ({b}ᶜ : Finset (Fin n)))
  have hzero : ∀ i, Ideal.Quotient.mk I (z i) = 0 := by
    intro i
    rw [Ideal.Quotient.eq_zero_iff_mem]
    by_cases hi : i = b
    · subst hi; exact hmem
    · exact Ideal.subset_span ⟨i, by simp [hi], rfl⟩
  have hmax : IsLocalRing.maximalIdeal (A ⧸ I) = ⊥ := by
    have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) hsurj, ← hz.1,
      Ideal.map_span, eq_bot_iff, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp [hzero i]
  have hcard : (({b}ᶜ : Finset (Fin n)).card) = n - 1 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 fun h => (h ▸ b).elim0
  have hfield : IsField (A ⧸ I) := (IsLocalRing.isField_iff_maximalIdeal_eq).2 hmax
  have h0 : ringKrullDim (A ⧸ I) = 0 := ringKrullDim_eq_zero_of_isField hfield
  rw [h0, hcard] at hdim
  have : n - (n - 1) = 1 := by omega
  rw [this] at hdim
  exact absurd hdim (by norm_num)

/-- A valuation bounded by one on the image of a ring is one on the images of its units. -/
private theorem valuation_eq_one_of_forall_le_one {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) (v : Valuation K ℤᵐ⁰) (h : ∀ a, v (φ a) ≤ 1) (u : Rˣ) : v (φ u) = 1 := by
  refine le_antisymm (h u) ?_
  have hm : v (φ u) * v (φ ((u⁻¹ : Rˣ) : R)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  calc (1 : ℤᵐ⁰) = v (φ u) * v (φ ((u⁻¹ : Rˣ) : R)) := hm.symm
    _ ≤ v (φ u) * 1 := by gcongr; exact h _
    _ = v (φ u) := mul_one _

/-- **Snc coordinates and the monomial structure at the centre of a log canonical place.** Let
`(X, B)` be a dlt pair over an algebraically closed field of characteristic zero and `D` a proper
divisor over `X` with discrepancy `-1`, with centre of generic point `x`. Then `X` is smooth at
`x`, and there are a regular system of parameters `z₁, …, z_c` of `𝒪_{X,x}` and distinct prime
divisors `L₁, …, L_c` through `x` with ideals `(z_a)` at `x`, which are the components of
`Supp B` through `x`, all of coefficient one; and `D` is monomial in the `z_a` with positive
weights `α_a`. -/
private theorem exists_sncCoordinates_of_isDiscrepancy_neg_one {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X} (hdlt : MMP.Intersection.IsDltPair sX B)
    {n : ℕ} {K : Divisor X} (hP : MMP.Mori.IsPairWith sX n K B) (D : DivisorOver k sX)
    (hDp : IsProper D.f) (hD : MMP.Mori.IsDiscrepancy sX n K B D (-1)) :
    ∃ (c : ℕ) (z : Fin c → X.presheaf.stalk (D.f D.E.genericPoint))
      (L : Fin c → Mori.PrimeDivisor X) (α : Fin c → ℕ),
      IsRegularSystemOfParameters z ∧ Function.Injective L ∧
      (∀ a, D.f D.E.genericPoint ∈ (L a).support) ∧
      (∀ a, IdealSheafData.stalk (L a).idealSheaf (D.f D.E.genericPoint) = Ideal.span {z a}) ∧
      (∀ E : Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ E.support → B.coeff E ≠ 0 →
        E ∈ Set.range L) ∧
      (∀ a, B.coeff (L a) = 1) ∧
      D.f D.E.genericPoint ∈ Mori.smoothLocus sX ∧
      (∀ a, 0 < α a) ∧
      (∀ a, D.valuation (algebraMap _ X.functionField (z a)) = WithZero.exp (-(α a : ℤ))) ∧
      ∀ f : X.presheaf.stalk (D.f D.E.genericPoint), f ≠ 0 → ∃ M : ℕ,
        f ∈ weightedMonomialIdeal z α M ∧
        D.valuation (algebraMap _ X.functionField f) = WithZero.exp (-(M : ℤ)) := by
  classical
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hD hDp
  norm_num at hlog
  obtain ⟨U, hxU, hsm, hsnc⟩ := exists_snc_open_of_isDltPair hdlt D hlog
  have hB : ∀ P, 0 ≤ B.coeff P ∧ B.coeff P ≤ 1 := fun P => ⟨hdlt.1.2.1 P, hdlt.2.1 P⟩
  obtain ⟨D', hD'p, hval, hD'T⟩ :=
    exists_isDiscrepancy_reducedDivisorOf hB hP D hDp hD U hxU hsm hsnc
  have hcoeff1 := coeff_eq_one_of_isDiscrepancy_neg_one hdlt hP D hDp hD
  have hvle := MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl
  have hvlt := MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D _ rfl
  generalize hxdef : D.f D.E.genericPoint = x at hxU hcoeff1 hvle hvlt ⊢
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  haveI : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨_, hxU⟩)
  have hXv : MMP.Mori.IsVariety k sX := hP.1.1
  haveI : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  -- smoothness at `x`
  have hxsm : x ∈ Mori.smoothLocus sX := by
    haveI : LocallyOfFiniteType (U.ι ≫ sX) := inferInstance
    haveI : LocallyOfFinitePresentation (U.ι ≫ sX) := inferInstance
    exact Mori.le_smoothLocus sX ((Mori.isSmoothScheme_iff (U.ι ≫ sX)).1 hsm) hxU
  -- the snc data at `x` on `X`
  -- the monomial structure on `U`
  set T := MMP.Intersection.reducedDivisorOf (B.restrictOpen U).support with hT
  have hTsnc : T.IsSNC (U.ι ≫ sX) :=
    hsnc.of_support_subset (by rw [MMP.Intersection.support_reducedDivisorOf])
  have hred := MMP.Fourfold.isReducedSNCDiscrepancy_zero_of_isDiscrepancy (hP.1.restrictOpen U)
    hsm (MMP.Intersection.isReducedEffective_reducedDivisorOf _) hTsnc hD'T.2.1 D' hD'p hD'T
  obtain ⟨Z, hZc, -, α0, ⟨z0, hz0⟩, hall⟩ := hred.isMonomialValuationOfWeight_of_eq_zero
  obtain ⟨hzv, hmonW⟩ := hall z0 hz0
  obtain ⟨-, -, -, -, -, -, -, -, hαpos, -, hmono⟩ := hmonW
  have hyx : U.ι Z.isIrreducible.genericPoint = x := by
    obtain ⟨D'', -, hξ, hZ⟩ := hZc
    have hη : Z.isIrreducible.genericPoint = D''.f D''.E.genericPoint := by
      have h1 : IsGenericPoint Z.isIrreducible.genericPoint (Z : Set U) := by
        have := Z.isIrreducible.isGenericPoint_genericPoint_closure
        rwa [Z.isClosed.closure_eq] at this
      have h2 : IsGenericPoint (D''.f D''.E.genericPoint) (Z : Set U) := by
        rw [hZ, D''.center_eq_closure_genericPoint]
        exact isGenericPoint_closure
      exact h1.eq h2
    rw [hη]
    rw [← hxdef]
    exact map_genericPoint_eq_of_valuation_eq_comap hXv U D D'' (by rw [hval, hξ])
  subst hyx
  obtain ⟨N, z', jj, hz', hjj, hI⟩ :=
    (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff U.ι B Z.isIrreducible.genericPoint).1
      (hsnc.2 Z.isIrreducible.genericPoint)
  set e := MMP.Threefold.Mori.OpenRestriction.stalkEquivOfOpenImmersion U.ι Z.isIrreducible.genericPoint with he
  -- valuations along `D` are read on `U`
  have hvalU : ∀ f : X.presheaf.stalk (U.ι Z.isIrreducible.genericPoint),
      D.valuation (algebraMap _ X.functionField f) =
        D'.valuation (algebraMap _ (U : Scheme).functionField (e f)) := by
    intro f
    rw [hval, Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    rfl
  -- ideals of the components
  have hIdeal : ∀ j : sncIndexSet T (Z : Set U), IdealSheafData.stalk (OpenWeilRestriction.primeDivisorMap U.ι j.1).idealSheaf (U.ι Z.isIrreducible.genericPoint) =
      Ideal.span {e.symm (z0 j)} := by
    intro j
    have h1 := MMP.Threefold.Mori.OpenRestriction.stalk_comap_eq_map U.ι (OpenWeilRestriction.primeDivisorMap U.ι j.1).idealSheaf Z.isIrreducible.genericPoint
    rw [MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap, hz0 j,
      ← MMP.Threefold.Mori.OpenRestriction.stalkEquivOfOpenImmersion_coe] at h1
    rw [← MMP.Threefold.Mori.OpenRestriction.map_symm_map e
      (IdealSheafData.stalk (OpenWeilRestriction.primeDivisorMap U.ι j.1).idealSheaf (U.ι Z.isIrreducible.genericPoint)), ← h1, Ideal.map_span,
      Set.image_singleton]
  have hTsupp : ∀ E : Mori.PrimeDivisor U, E ∈ T.support → E ∈ (B.restrictOpen U).support :=
    fun E h => by rwa [hT, MMP.Intersection.support_reducedDivisorOf] at h
  have hJmem : ∀ j : sncIndexSet T (Z : Set U), OpenWeilRestriction.primeDivisorMap U.ι j.1 ∈ B.support ∧ U.ι Z.isIrreducible.genericPoint ∈ (OpenWeilRestriction.primeDivisorMap U.ι j.1).support := by
    intro j
    have hj := Finset.mem_filter.1 j.2
    have hj1 : j.1 ∈ (B.restrictOpen U).support := hTsupp _ hj.1
    refine ⟨?_, (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι j.1 Z.isIrreducible.genericPoint).2
      (hj.2 (by
        have := Z.isIrreducible.isGenericPoint_genericPoint_closure
        rw [Z.isClosed.closure_eq] at this
        exact this.mem))⟩
    have := Finsupp.mem_support_iff.1 hj1
    exact Finsupp.mem_support_iff.2 this
  set φ : sncIndexSet T (Z : Set U) → {E : Mori.PrimeDivisor X // E ∈ B.support ∧ U.ι Z.isIrreducible.genericPoint ∈ E.support} :=
    fun j => ⟨OpenWeilRestriction.primeDivisorMap U.ι j.1, hJmem j⟩ with hφ
  have hφbij : Function.Bijective φ := by
    refine ⟨fun a b h => Subtype.ext (OpenWeilRestriction.primeDivisorMap_injective U.ι
      (congrArg Subtype.val h)), ?_⟩
    rintro ⟨E, hE1, hE2⟩
    obtain ⟨EU, hEU⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
      U.ι E Z.isIrreducible.genericPoint hE2
    refine ⟨⟨EU, Finset.mem_filter.2 ⟨?_, ?_⟩⟩, Subtype.ext hEU⟩
    · rw [hT, MMP.Intersection.support_reducedDivisorOf]
      refine Finsupp.mem_support_iff.2 ?_
      change B.coeff (OpenWeilRestriction.primeDivisorMap U.ι EU) ≠ 0
      rw [hEU]
      exact Finsupp.mem_support_iff.1 hE1
    · have hyE : Z.isIrreducible.genericPoint ∈ EU.support :=
        (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι EU Z.isIrreducible.genericPoint).1
          (by rw [hEU]; exact hE2)
      have hZcl : (Z : Set U) = closure {Z.isIrreducible.genericPoint} := by
        have := Z.isIrreducible.isGenericPoint_genericPoint_closure
        rw [Z.isClosed.closure_eq] at this
        exact this.symm
      rw [hZcl]
      refine closure_minimal (Set.singleton_subset_iff.2 hyE) ?_
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isClosed_closure
  -- the components of `B` through `x` are the regular parameters
  have hgen : ∀ j : sncIndexSet T (Z : Set U),
      e.symm (z0 j) ∈ Ideal.span {z' (jj (φ j))} := by
    intro j
    rw [← hI (φ j)]
    change e.symm (z0 j) ∈ IdealSheafData.stalk
      (OpenWeilRestriction.primeDivisorMap U.ι j.1).idealSheaf (U.ι Z.isIrreducible.genericPoint)
    rw [hIdeal j]
    exact Ideal.mem_span_singleton_self _
  have hsurj : Function.Surjective jj := by
    by_contra hns
    simp only [Function.Surjective, not_forall, not_exists] at hns
    obtain ⟨b, hb⟩ := hns
    have hb0 : z' b ≠ 0 := by
      haveI : IsRegularLocalRing (X.presheaf.stalk (U.ι Z.isIrreducible.genericPoint)) :=
        MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz'
      exact MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz' b
    have hbm : z' b ∈ IsLocalRing.maximalIdeal _ := by
      rw [← hz'.1]; exact Ideal.subset_span ⟨b, rfl⟩
    have he0 : e (z' b) ≠ 0 := (map_ne_zero_iff _ e.injective).2 hb0
    obtain ⟨M, hM, hξM⟩ := hmono (e (z' b)) he0
    have hlt := hvlt (z' b) hbm
    rw [hvalU, hξM] at hlt
    have hM1 : 1 ≤ M := by
      by_contra h0
      have : M = 0 := by omega
      rw [this] at hlt
      simp at hlt
    have hmem := weightedMonomialIdeal_le_span z0 α0 hM1 hM.1
    have hmem' : z' b ∈ Ideal.map e.symm.toRingHom (Ideal.span (Set.range z0)) := by
      have := Ideal.mem_map_of_mem e.symm.toRingHom hmem
      simpa using this
    rw [Ideal.map_span] at hmem'
    refine notMem_span_image_compl_of_isRegularSystemOfParameters hz' b ?_
    refine (Ideal.span_le.2 ?_) hmem'
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    refine Ideal.span_mono ?_ (hgen j)
    rw [Set.singleton_subset_iff]
    refine ⟨jj (φ j), ?_, rfl⟩
    simp only [Finset.coe_compl, Finset.coe_singleton, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact hb _
  -- the coordinates indexed by `Fin N`
  have hbij : Function.Bijective jj := ⟨hjj, hsurj⟩
  set eS := (Equiv.ofBijective jj hbij).symm with heS
  set eJ := eS.trans (Equiv.ofBijective φ hφbij).symm with heJ
  have hφeJ : ∀ a, φ (eJ a) = eS a := fun a =>
    Equiv.ofBijective_apply_symm_apply φ hφbij (eS a)
  have hjjeS : ∀ a, jj (eS a) = a := fun a => Equiv.ofBijective_apply_symm_apply jj hbij a
  have hspan : ∀ a, Ideal.span {z' a} = Ideal.span {e.symm (z0 (eJ a))} := by
    intro a
    rw [← hIdeal (eJ a)]
    have h1 := hI (eS a)
    rw [hjjeS] at h1
    rw [← h1, ← hφeJ a]
  refine ⟨N, z', fun a => (eS a).1, fun a => α0 (eJ a), hz', ?_, fun a => (eS a).2.2, ?_, ?_, ?_,
    hxsm, fun a => hαpos _, ?_, ?_⟩
  · intro a b h
    exact eS.injective (Subtype.ext h)
  · intro a
    rw [hI (eS a), hjjeS]
  · intro E hE hE0
    exact ⟨jj ⟨E, Finsupp.mem_support_iff.2 hE0, hE⟩,
      congrArg Subtype.val (Equiv.ofBijective_symm_apply_apply jj hbij _)⟩
  · intro a
    exact hcoeff1 _ (eS a).2.2 (Finsupp.mem_support_iff.1 (eS a).2.1)
  · intro a
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp (hspan a)
    have hu1 := valuation_eq_one_of_forall_le_one (algebraMap _ X.functionField) D.valuation hvle u
    have hv : D.valuation (algebraMap _ X.functionField (e.symm (z0 (eJ a)))) =
        WithZero.exp (-(α0 (eJ a) : ℤ)) := by
      rw [hvalU, RingEquiv.apply_symm_apply, hzv]
    rw [← hu, map_mul, map_mul, hu1, mul_one] at hv
    exact hv
  · intro f hf
    obtain ⟨M, hM, hξM⟩ := hmono (e f) ((map_ne_zero_iff _ e.injective).2 hf)
    refine ⟨M, ?_, by rw [hvalU, hξM]⟩
    rw [weightedMonomialIdeal_eq_of_span_eq hspan,
      weightedMonomialIdeal_comp_equiv eJ (fun j => e.symm (z0 j)) α0 M]
    rw [show (fun j => e.symm (z0 j)) = fun j => e.symm.toRingHom (z0 j) from rfl,
      ← map_weightedMonomialIdeal]
    have := Ideal.mem_map_of_mem e.symm.toRingHom
      (show e f ∈ weightedMonomialIdeal z0 α0 M from hM.1)
    simpa using this

end SNCCentre

section AffinePlaneModel

private theorem isScalarTower_functionField_Spec {k : Type} [Field k] {A : CommRingCat.{0}}
    [IsDomain A] [Algebra k A] :
    letI := functionFieldAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    IsScalarTower k A (Spec A).functionField := by
  letI := functionFieldAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  refine IsScalarTower.of_algebraMap_eq' ?_
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap k A))).appTop ≫
    (Spec A).presheaf.germ ⊤ _ (TopologicalSpace.Opens.mem_top _)).hom =
    (StructureSheaf.toStalk A _).hom.comp (algebraMap k A)
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Scheme.ΓSpecIso_inv]
  rfl

private theorem exists_aeval_div_of_adjoin_eq_top {k K : Type} [Field k] [Field K] [Algebra k K]
    (u w : K) (hgen : IntermediateField.adjoin k ({u, w} : Set K) = ⊤) (x : K) :
    ∃ r s : MvPolynomial (Fin 2) k, MvPolynomial.aeval ![u, w] s ≠ 0 ∧
      x * MvPolynomial.aeval ![u, w] s = MvPolynomial.aeval ![u, w] r := by
  have hrange : Set.range ![u, w] = ({u, w} : Set K) := by
    ext y; simp [Fin.exists_fin_two, eq_comm, or_comm]
  have hx : x ∈ IntermediateField.adjoin k (Set.range ![u, w]) := by
    rw [hrange, hgen]; trivial
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_range_iff k ![u, w] x).1 hx
  by_cases hs : MvPolynomial.aeval ![u, w] s = 0
  · refine ⟨0, 1, by simp, ?_⟩
    rw [hrs, hs, div_zero, zero_mul, map_zero]
  · exact ⟨r, s, hs, by rw [hrs, div_mul_cancel₀ _ hs]⟩

private theorem algebraicIndependent_of_adjoin_eq_top {k K : Type} [Field k] [Field K] [Algebra k K]
    (htr : Algebra.trdeg k K = 2) (u w : K)
    (hgen : IntermediateField.adjoin k ({u, w} : Set K) = ⊤) :
    AlgebraicIndependent k ![u, w] := by
  haveI : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range ![u, w])) K := by
    refine ⟨fun x => ?_⟩
    obtain ⟨r, s, hs, hrs⟩ := exists_aeval_div_of_adjoin_eq_top u w hgen x
    have hr : MvPolynomial.aeval ![u, w] r ∈ Algebra.adjoin k (Set.range ![u, w]) := by
      rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨r, rfl⟩
    have hs' : MvPolynomial.aeval ![u, w] s ∈ Algebra.adjoin k (Set.range ![u, w]) := by
      rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨s, rfl⟩
    refine ⟨Polynomial.C ⟨_, hs'⟩ * Polynomial.X - Polynomial.C ⟨_, hr⟩, ?_, ?_⟩
    · intro h0
      have := congrArg (Polynomial.coeff · 1) h0
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
        if_neg one_ne_zero, sub_zero, Polynomial.coeff_zero, if_pos] at this
      exact hs (congrArg Subtype.val this)
    · rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_C]
      change MvPolynomial.aeval ![u, w] s * x - MvPolynomial.aeval ![u, w] r = 0
      rw [mul_comm, hrs, sub_self]
  have h1 : Algebra.trdeg k K < Cardinal.aleph0 := by rw [htr]; exact Cardinal.natCast_lt_aleph0
  have h2 : Cardinal.mk (Fin 2) ≤ Algebra.trdeg k K := by rw [htr]; simp
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg k ![u, w] h1 h2).1

private theorem isFractionRing_aeval_of_adjoin_eq_top {k K : Type} [Field k] [Field K] [Algebra k K]
    (htr : Algebra.trdeg k K = 2) (u w : K)
    (hgen : IntermediateField.adjoin k ({u, w} : Set K) = ⊤) :
    letI := (MvPolynomial.aeval (R := k) ![u, w] : MvPolynomial (Fin 2) k →ₐ[k] K).toRingHom.toAlgebra
    IsFractionRing (MvPolynomial (Fin 2) k) K := by
  letI := (MvPolynomial.aeval (R := k) ![u, w] : MvPolynomial (Fin 2) k →ₐ[k] K).toRingHom.toAlgebra
  have hinj : Function.Injective (MvPolynomial.aeval (R := k) ![u, w] : MvPolynomial (Fin 2) k →ₐ[k] K) :=
    algebraicIndependent_of_adjoin_eq_top htr u w hgen
  refine ⟨fun r => ?_, fun x => ?_, fun {a b} h => ⟨1, ?_⟩⟩
  · refine IsUnit.mk0 _ ?_
    change MvPolynomial.aeval (R := k) ![u, w] (r : MvPolynomial (Fin 2) k) ≠ 0
    rw [Ne, ← map_zero (MvPolynomial.aeval (R := k) ![u, w]), hinj.eq_iff]
    exact nonZeroDivisors.coe_ne_zero r
  · obtain ⟨r, s, hs, hrs⟩ := exists_aeval_div_of_adjoin_eq_top u w hgen x
    have hs0 : s ∈ nonZeroDivisors (MvPolynomial (Fin 2) k) :=
      mem_nonZeroDivisors_of_ne_zero fun h => hs (by rw [h, map_zero])
    exact ⟨⟨r, ⟨s, hs0⟩⟩, hrs⟩
  · rw [OneMemClass.coe_one, one_mul, one_mul]
    exact hinj h

/-- `X.fromSpecStalk x ≫ s_X` is `Spec` of the structure map of the stalk. -/
private theorem fromSpecStalk_comp_eq_specMap' {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (x : X) :
    X.fromSpecStalk x ≫ sX =
      Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.presheaf.germ ⊤ x trivial) := by
  have key : (Scheme.ΓSpecIso (.of k)).inv ≫ (X.fromSpecStalk x ≫ sX).appTop ≫
      (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom =
      (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.presheaf.germ ⊤ x trivial := by
    simp only [Scheme.Hom.comp_appTop, Category.assoc, Scheme.fromSpecStalk_appTop]
    have : (homOfLE le_top : (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ ⊤) = 𝟙 _ := rfl
    rw [this, op_id, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id,
      Category.comp_id]
  have hpre : Spec.preimage (X.fromSpecStalk x ≫ sX) =
      (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.presheaf.germ ⊤ x trivial := by
    rw [← key]
    have := Scheme.ΓSpecIso_naturality (Spec.preimage (X.fromSpecStalk x ≫ sX))
    rw [Spec.map_preimage] at this
    rw [this, Iso.inv_hom_id_assoc]
  rw [← hpre, Spec.map_preimage]

/-- **Centres on proper varieties** (valuative criterion). A valuation of the function field of
an integral scheme proper over `k`, trivial on `k`, dominates the local ring of some point. -/
private theorem exists_dominates_of_isProper_of_trivial {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (hprop : IsProper sX)
    (w : Valuation X.functionField ℤᵐ⁰)
    (hk : ∀ c : k, c ≠ 0 → w ((((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial).hom) c) = 1) :
    ∃ x : X, (∀ a : X.presheaf.stalk x, w (algebraMap _ X.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
        w (algebraMap _ X.functionField a) < 1 := by
  set ψ := (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial
  let R := w.valuationSubring
  let ιk : k →+* R := ψ.hom.codRestrict R fun c => by
    by_cases hc : c = 0
    · rw [hc, map_zero]; exact R.zero_mem
    · exact (w.mem_valuationSubring_iff _).2 (hk c hc).le
  have hsq : X.fromSpecStalk (genericPoint X) ≫ sX =
      Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫
        Spec.map (CommRingCat.ofHom ιk) := by
    rw [fromSpecStalk_comp_eq_specMap', ← Spec.map_comp]
    congr 1
  let S : ValuativeCommSq sX :=
    { R := R
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := Spec.map (CommRingCat.ofHom ιk)
      commSq := ⟨hsq⟩ }
  have hex : ValuativeCriterion.Existence sX := by
    have h : @IsProper _ _ sX := hprop
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  change Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫ l =
    X.fromSpecStalk (genericPoint X) at hl₁
  set x := l (IsLocalRing.closedPoint R)
  set φ := Scheme.stalkClosedPointTo l
  have hgen : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hext : φ ≫ CommRingCat.ofHom (algebraMap R X.functionField) =
      X.presheaf.stalkSpecializes hgen := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk x), Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Spec.map_comp, Category.assoc]
    change _ ≫ Spec.map (Scheme.stalkClosedPointTo l) ≫ X.fromSpecStalk _ = _
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
    exact hl₁
  have hcompat : ∀ a : X.presheaf.stalk x,
      algebraMap R X.functionField (φ.hom a) = algebraMap (X.presheaf.stalk x) X.functionField a :=
    fun a => congrArg (fun f => f.hom a) hext
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [← hcompat]; exact (w.mem_valuationSubring_iff _).1 (φ.hom a).2
  · rw [← hcompat]
    have hnu : ¬ IsUnit (φ.hom a) := fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit φ.hom a hu)
    set r := φ.hom a
    have hr1 : w (r : X.functionField) ≤ 1 := (w.mem_valuationSubring_iff _).1 r.2
    refine lt_of_le_of_ne hr1 fun heq => hnu ?_
    change w (r : X.functionField) = 1 at heq
    have hr0 : (r : X.functionField) ≠ 0 := fun h0 => by
      rw [h0, map_zero] at heq; exact zero_ne_one heq
    have hinv : (r : X.functionField)⁻¹ ∈ R := (w.mem_valuationSubring_iff _).2 (by
      rw [map_inv₀, heq, inv_one])
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext
      (show (r : X.functionField) * (r : X.functionField)⁻¹ = 1 from mul_inv_cancel₀ hr0)⟩

/-- **The affine plane realises the `u`-adic valuation.** Let `T` be a normal variety of dimension
two, proper over `k`, whose function field is generated by `u` and `w`. Then there is a proper
divisor over `T` along which `dlog u ∧ dlog w` has a simple pole: the `u`-adic valuation of
`k(T) = k(u, w)`, realised by the axis `u = 0` of the affine plane `Spec k[u, w]`. -/
private theorem exists_properDivisorOver_ordPullback_dlog_eq_neg_one {k : Type} [Field k]
    [CharZero k] {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)} [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] (hT : IsNormalVariety k sT) [IsProper sT] (hd : topologicalKrullDim T = (2 : ℕ))
    (u w : T.functionField) (hu : u ≠ 0) (hw : w ≠ 0)
    (hgen : letI := functionFieldAlgebra sT
      IntermediateField.adjoin k ({u, w} : Set T.functionField) = ⊤) :
    letI := functionFieldAlgebra sT
    ∃ E : DivisorOver k sT, IsProper E.f ∧
      E.ordPullback (show RationalPluriForms sT 2 ((1 : ℕ) : ℤ) from formPow (exteriorPower.ιMulti
        T.functionField 2 ![u⁻¹ • KaehlerDifferential.D k _ u,
          w⁻¹ • KaehlerDifferential.D k _ w]) 1) = -1 := by
  letI := functionFieldAlgebra sT
  set sY := Spec.map (CommRingCat.ofHom (algebraMap k (CommRingCat.of (MvPolynomial (Fin 2) k)))) with hsY
  haveI : IsNormal (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))) := isNormal_spec_of_isIntegrallyClosed _
  have hY : Mori.IsNormalVariety k sY := ⟨⟨⟩, inferInstance⟩
  letI := functionFieldAlgebra sY
  haveI := isScalarTower_functionField_Spec (k := k) (A := CommRingCat.of (MvPolynomial (Fin 2) k))
  haveI hdom : IsDomain (CommRingCat.of (MvPolynomial (Fin 2) k)) :=
    (inferInstance : IsDomain (MvPolynomial (Fin 2) k))
  letI algY : Algebra (CommRingCat.of (MvPolynomial (Fin 2) k))
    (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec _
  haveI : IsFractionRing (CommRingCat.of (MvPolynomial (Fin 2) k))
      (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_affine _
  haveI : LocallyOfFiniteType sT := hT.1.toLocallyOfFiniteType
  have htr : Algebra.trdeg k T.functionField = 2 := by
    have h := (toENat_trdeg_functionField (sX := sT)).trans hd
    have h' : Cardinal.toENat (Algebra.trdeg k T.functionField) = (2 : ℕ) := by
      have h2 : ((Cardinal.toENat (Algebra.trdeg k T.functionField) : ℕ∞) : WithBot ℕ∞) =
          (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) := h
      exact WithBot.coe_injective h2
    exact Cardinal.toENat_eq_natCast.1 h'
  letI : Algebra (CommRingCat.of (MvPolynomial (Fin 2) k)) T.functionField :=
    (MvPolynomial.aeval (R := k) ![u, w] : MvPolynomial (Fin 2) k →ₐ[k] T.functionField).toRingHom.toAlgebra
  haveI : IsFractionRing (CommRingCat.of (MvPolynomial (Fin 2) k)) T.functionField := isFractionRing_aeval_of_adjoin_eq_top htr u w hgen
  haveI : IsScalarTower k (CommRingCat.of (MvPolynomial (Fin 2) k)) T.functionField := IsScalarTower.of_algebraMap_eq fun c =>
    ((MvPolynomial.aeval (R := k) ![u, w]).commutes c).symm
  set e0 : T.functionField ≃ₐ[(CommRingCat.of (MvPolynomial (Fin 2) k))] (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).functionField :=
    IsLocalization.algEquiv (nonZeroDivisors (CommRingCat.of (MvPolynomial (Fin 2) k)))
      T.functionField (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).functionField with he0
  set e : T.functionField ≃ₐ[k] (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).functionField := e0.restrictScalars k with he
  have heX : ∀ i : Fin 2, e (![u, w] i) =
      algebraMap (CommRingCat.of (MvPolynomial (Fin 2) k)) (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).functionField (MvPolynomial.X i) := by
    intro i
    have h1 : ![u, w] i = algebraMap (CommRingCat.of (MvPolynomial (Fin 2) k)) T.functionField (MvPolynomial.X i) := by
      change _ = MvPolynomial.aeval ![u, w] (MvPolynomial.X i)
      rw [MvPolynomial.aeval_X]
    rw [h1]
    change e0 (algebraMap (CommRingCat.of (MvPolynomial (Fin 2) k)) T.functionField (MvPolynomial.X i)) = _
    exact e0.commutes _
  -- the plane: dimension two, and the prime divisor `u = 0`
  have hdimY : topologicalKrullDim (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))) = (2 : ℕ) := by
    change topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin 2) k)) = _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
    norm_num
  have hX0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ≠ 0 := MvPolynomial.X_ne_zero 0
  have hprime : (Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) k)}).IsPrime :=
    (Ideal.span_singleton_prime hX0).2 MvPolynomial.X_prime
  let p : Spec (CommRingCat.of (MvPolynomial (Fin 2) k)) := ⟨_, hprime⟩
  letI algp : Algebra (MvPolynomial (Fin 2) k)
      ((Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).presheaf.stalk p) :=
    (StructureSheaf.toStalk (MvPolynomial (Fin 2) k) p).hom.toAlgebra
  haveI hloc : IsLocalization.AtPrime
      ((Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).presheaf.stalk p)
      (Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) k)}) :=
    StructureSheaf.IsLocalization.to_stalk (MvPolynomial (Fin 2) k) p
  have hp1 : Order.coheight p = 1 := by
    have h := ringKrullDim_stalk_eq_coheight p
    have h2 := IsLocalization.AtPrime.ringKrullDim_eq_height
      (Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) k)})
      ((Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).presheaf.stalk p)
    rw [Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hX0) MvPolynomial.X_prime.not_unit] at h2
    rw [h2] at h
    exact_mod_cast h.symm
  set E : Mori.PrimeDivisor (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))) :=
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne p hp1 with hEdef
  have hEη : E.genericPoint = p := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne p hp1
  have hEideal : E.genericPoint.asIdeal = Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) k)} := by
    rw [hEη]
  clear_value p
  letI algE : Algebra (MvPolynomial (Fin 2) k)
      ((Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).presheaf.stalk E.genericPoint) :=
    (StructureSheaf.toStalk (MvPolynomial (Fin 2) k) E.genericPoint).hom.toAlgebra
  haveI : E.genericPoint.asIdeal.IsPrime := E.genericPoint.isPrime
  haveI hlocE : IsLocalization.AtPrime
      ((Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).presheaf.stalk E.genericPoint)
      E.genericPoint.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (MvPolynomial (Fin 2) k) E.genericPoint
  haveI := E.isDiscreteValuationRing_localRing
  -- compatibility of the algebra maps to the function field
  have hcomp : ∀ f : MvPolynomial (Fin 2) k,
      algebraMap ((Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).presheaf.stalk E.genericPoint)
        (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).functionField
        (algebraMap (MvPolynomial (Fin 2) k) _ f) =
        algebraMap (CommRingCat.of (MvPolynomial (Fin 2) k))
          (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).functionField f := by
    intro f
    have h := StructureSheaf.toStalk_stalkSpecializes (R := MvPolynomial (Fin 2) k)
      ((genericPoint_spec (Spec (CommRingCat.of (MvPolynomial (Fin 2) k)))).specializes
        (show E.genericPoint ∈ (Set.univ : Set _) from trivial))
    exact congrArg (fun φ => φ.hom f) h
  -- orders of the coordinates along `E`
  have hmax : IsLocalRing.maximalIdeal
      ((Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).presheaf.stalk E.genericPoint) =
      Ideal.span {algebraMap (MvPolynomial (Fin 2) k) _ (MvPolynomial.X 0)} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal E.genericPoint.asIdeal, hEideal,
      Ideal.map_span, Set.image_singleton]
  have hirr : Irreducible (algebraMap (MvPolynomial (Fin 2) k)
      ((Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).presheaf.stalk E.genericPoint)
      (MvPolynomial.X 0)) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  have hord0 : (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).ord
      (algebraMap (CommRingCat.of (MvPolynomial (Fin 2) k)) _ (MvPolynomial.X 0)) E.genericPoint
      = 1 := by
    rw [← hcomp]
    have h0 : algebraMap ((Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).presheaf.stalk
        E.genericPoint) (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).functionField
        (algebraMap (MvPolynomial (Fin 2) k) _ (MvPolynomial.X 0)) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hirr.ne_zero
    exact (Scheme.ord_eq_iff E.coheight_genericPoint h0).mpr (Ring.ordFrac_irreducible hirr)
  have hX1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ∉ E.genericPoint.asIdeal := by
    rw [hEideal, Ideal.mem_span_singleton]
    intro h
    have := (MvPolynomial.X_dvd_X (R := k)).1 h
    exact absurd this (by decide)
  have hord1 : (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).ord
      (algebraMap (CommRingCat.of (MvPolynomial (Fin 2) k)) _ (MvPolynomial.X 1)) E.genericPoint
      = 0 := by
    rw [← hcomp]
    exact E.ord_algebraMap_of_isUnit (IsLocalization.map_units _
      (⟨MvPolynomial.X 1, hX1⟩ : E.genericPoint.asIdeal.primeCompl))
  -- the frame `dX₀, dX₁` along `E`
  letI := stalkAlgebra sY E.genericPoint
  haveI hstk : IsScalarTower k (MvPolynomial (Fin 2) k)
      ((Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).presheaf.stalk E.genericPoint) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫
      (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).presheaf.germ ⊤ _
        (TopologicalSpace.Opens.mem_top _)).hom =
      (StructureSheaf.toStalk (MvPolynomial (Fin 2) k) _).hom.comp
        (algebraMap k (MvPolynomial (Fin 2) k))
    rw [hsY, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Scheme.ΓSpecIso_inv]
    rfl
  have hA : Submodule.span (MvPolynomial (Fin 2) k) (Set.range fun i : Fin 2 =>
      KaehlerDifferential.D k (MvPolynomial (Fin 2) k) (MvPolynomial.X i)) = ⊤ := by
    have h := (KaehlerDifferential.mvPolynomialBasis k (Fin 2)).span_eq
    have hfun : (⇑(KaehlerDifferential.mvPolynomialBasis k (Fin 2))) =
        fun i : Fin 2 => KaehlerDifferential.D k (MvPolynomial (Fin 2) k) (MvPolynomial.X i) :=
      funext fun i => KaehlerDifferential.mvPolynomialBasis_apply k (Fin 2) i
    rw [hfun] at h
    exact h
  have hw := span_D_algebraMap_eq_top_of_isLocalization (k := k)
    (B := (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).presheaf.stalk E.genericPoint)
    E.genericPoint.asIdeal.primeCompl (fun i : Fin 2 => MvPolynomial.X i) hA
  have hEmem : E.genericPoint ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  set f : Fin 2 → (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).functionField := fun i =>
    algebraMap (CommRingCat.of (MvPolynomial (Fin 2) k)) _ (MvPolynomial.X i) with hfdef
  have hf0 : ∀ i, f i ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (MvPolynomial.X_ne_zero i)
  -- the order of `dlog X₀ ∧ dlog X₁` along `E`
  have hordY : E.ordForm (show RationalPluriForms sY 2 ((1 : ℕ) : ℤ) from formPow (exteriorPower.ιMulti
      (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).functionField 2
        fun i => (f i)⁻¹ • KaehlerDifferential.D k _ (f i)) 1) = -1 := by
    have hsplit : (exteriorPower.ιMulti (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).functionField 2
        fun i => (f i)⁻¹ • KaehlerDifferential.D k _ (f i)) =
        (∏ i, (f i)⁻¹) • exteriorPower.ιMulti _ 2 fun i => KaehlerDifferential.D k _ (f i) := by
      rw [← AlternatingMap.map_smul_univ]
    have hfw : (fun i : Fin 2 => KaehlerDifferential.D k
        (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).functionField (f i)) =
        fun i => KaehlerDifferential.D k _ (algebraMap
          ((Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).presheaf.stalk E.genericPoint) _
          (algebraMap (MvPolynomial (Fin 2) k) _ (MvPolynomial.X i))) := by
      funext i; rw [hcomp]
    change E.ordForm (show RationalPluriForms sY 2 ((1 : ℕ) : ℤ) from formPow (exteriorPower.ιMulti _ 2
      fun i => (f i)⁻¹ • KaehlerDifferential.D k _ (f i)) 1) = -1
    rw [hsplit, formPow_smul', hfw, ordForm_smul_formPow_ιMulti_D_eq hdimY 1 E hEmem _ hw,
      ord_prod_inv_pow Finset.univ hf0, Fin.sum_univ_two]
    simp only [hfdef, hord0, hord1]
    norm_num
  -- the pull-back of `dlog u ∧ dlog w` to the plane is `dlog X₀ ∧ dlog X₁`
  have hpull : pluriformPullback sY sT (FunctionFieldEquiv.toHom sY sT e) 2 ((1 : ℕ) : ℤ)
      (show RationalPluriForms sT 2 ((1 : ℕ) : ℤ) from formPow (exteriorPower.ιMulti T.functionField 2
        ![u⁻¹ • KaehlerDifferential.D k _ u, w⁻¹ • KaehlerDifferential.D k _ w]) 1) =
      (show RationalPluriForms sY 2 ((1 : ℕ) : ℤ) from formPow (exteriorPower.ιMulti
        (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).functionField 2
          fun i => (f i)⁻¹ • KaehlerDifferential.D k _ (f i)) 1) := by
    have hvT : (![u⁻¹ • KaehlerDifferential.D k T.functionField u,
        w⁻¹ • KaehlerDifferential.D k _ w] : Fin 2 → Ω[T.functionField⁄k]) =
        fun i => (![u, w] i)⁻¹ • KaehlerDifferential.D k _ (![u, w] i) := by
      funext i; fin_cases i <;> rfl
    have hsplit : (exteriorPower.ιMulti T.functionField 2
        fun i => (![u, w] i)⁻¹ • KaehlerDifferential.D k _ (![u, w] i)) =
        (∏ i, (![u, w] i)⁻¹) • (1 : T.functionField) • exteriorPower.ιMulti _ 2
          fun i => KaehlerDifferential.D k _ (![u, w] i) := by
      rw [one_smul, ← AlternatingMap.map_smul_univ]
    have hsplitY : (exteriorPower.ιMulti (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).functionField 2
        fun i => (f i)⁻¹ • KaehlerDifferential.D k _ (f i)) =
        (∏ i, (f i)⁻¹) • exteriorPower.ιMulti _ 2 fun i => KaehlerDifferential.D k _ (f i) := by
      rw [← AlternatingMap.map_smul_univ]
    rw [hvT, hsplit, formPow_smul', pluriformPullback_smul_formPow' hdimY hd (FunctionFieldEquiv.toHom sY sT e) _ 1,
      topFormsMap_smul_ιMulti_D]
    have hef : ∀ i, (FunctionFieldEquiv.toHom sY sT e) (![u, w] i) = f i := fun i => heX i
    simp only [map_one, one_smul, map_pow, map_prod, map_inv₀, hef, one_pow]
    change _ = formPow (exteriorPower.ιMulti _ 2 fun i => (f i)⁻¹ • KaehlerDifferential.D k _ (f i)) 1
    rw [hsplitY, formPow_smul']
  -- the valuation `ord_E ∘ e` of `k(T)`, and a divisor over `T` realising it
  set v : Valuation T.functionField ℤᵐ⁰ := E.divisorialValuation.comap
    (e : T.functionField →+* (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).functionField)
    with hvdef
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k sT v := ⟨_, sY, hY, E, e, rfl⟩
  have hk : ∀ c : k, c ≠ 0 → v ((((Scheme.ΓSpecIso (.of k)).inv ≫ sT.appTop ≫
      T.presheaf.germ ⊤ (genericPoint T) trivial).hom) c) = 1 := by
    intro c hc
    change E.divisorialValuation (e (algebraMap k T.functionField c)) = 1
    rw [e.commutes, IsScalarTower.algebraMap_apply k (CommRingCat.of (MvPolynomial (Fin 2) k)),
      ← hcomp]
    have hu : IsUnit (algebraMap (MvPolynomial (Fin 2) k)
        ((Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).presheaf.stalk E.genericPoint)
        (algebraMap k (MvPolynomial (Fin 2) k) c)) :=
      ((isUnit_iff_ne_zero.2 hc).map (algebraMap k (MvPolynomial (Fin 2) k))).map _
    rw [E.divisorialValuation_eq_exp_neg_ord ((hu.map _).ne_zero),
      E.ord_algebraMap_of_isUnit hu, neg_zero, WithZero.exp_zero]
  haveI : AlgebraicGeometry.IsVariety k sT := hT.1
  obtain ⟨x, hle, hlt⟩ := exists_dominates_of_isProper_of_trivial (sX := sT) inferInstance v hk
  obtain ⟨E', -, hval, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates sT hdiv x hle hlt
  refine ⟨E'.toDivisorOver, E'.isProper, ?_⟩
  have hv' : ∀ g, E'.toDivisorOver.valuation g =
      E.divisorialValuation ((FunctionFieldEquiv.toHom sY sT e) g) := by
    intro g
    exact congrArg (fun v => v g) hval
  rw [← ordForm_pluriformPullback_eq_ordPullback hY hT hdimY hd e E E'.toDivisorOver hv', hpull]
  exact hordY

/-- The centre of a divisor over an integral scheme has codimension at least one. -/
private theorem one_le_coheight_map_genericPoint' {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (D : DivisorOver k sX) :
    1 ≤ Order.coheight (D.f D.E.genericPoint) := by
  by_contra hlt
  have h0 : Order.coheight (D.f D.E.genericPoint) = 0 := ENat.lt_one_iff_eq_zero.1 (not_le.1 hlt)
  have hsp : genericPoint X ⤳ D.f D.E.genericPoint := (genericPoint_spec X).specializes trivial
  have hx : D.f D.E.genericPoint = genericPoint X :=
    ((show D.f D.E.genericPoint ⤳ genericPoint X from (Order.coheight_eq_zero.1 h0) hsp).antisymm
      hsp).eq
  obtain ⟨g, hg⟩ := MMP.Positivity.DivisorOver.exists_valuation_eq_exp_neg_one D
  obtain ⟨a, ha⟩ :=
    MMP.Positivity.DivisorOver.algebraMap_stalk_surjective_of_eq_genericPoint _ hx g⁻¹
  have hle := MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl a
  rw [ha, map_inv₀, hg, ← WithZero.exp_neg, neg_neg] at hle
  exact absurd hle (by decide)

/-- **A toric log generator on a dlt surface has a pole.** Let `(T, B_T)` be a projective dlt
surface whose function field is generated by `u` and `w`, and suppose `θ = dlog u ∧ dlog w`
satisfies `div θ + B_T = 0`. Then some component `C` of `⌊B_T⌋` is a pole of `θ`: the `u`-adic
valuation is a divisor of discrepancy `-1`, whose centre lies on `⌊B_T⌋` because `(T, B_T)` is
dlt. -/
private theorem exists_primeDivisor_ordForm_dlog_eq_neg_one {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)} [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] (hT : IsNormalVariety k sT) [IsProper sT] (hd : topologicalKrullDim T = (2 : ℕ))
    {BT : QDivisor T} (hdlt : MMP.Intersection.IsDltPair sT BT)
    (u w : T.functionField) (hu : u ≠ 0) (hw : w ≠ 0)
    (hgen : letI := functionFieldAlgebra sT
      IntermediateField.adjoin k ({u, w} : Set T.functionField) = ⊤)
    (hθ : letI := functionFieldAlgebra sT
      ∀ Γ : Mori.PrimeDivisor T, (Γ.ordForm (show RationalPluriForms sT 2 ((1 : ℕ) : ℤ) from
        formPow (exteriorPower.ιMulti T.functionField 2 ![u⁻¹ • KaehlerDifferential.D k _ u,
          w⁻¹ • KaehlerDifferential.D k _ w]) 1) : ℚ) + BT.coeff Γ = 0) :
    letI := functionFieldAlgebra sT
    ∃ C : Mori.PrimeDivisor T, C.ordForm (show RationalPluriForms sT 2 ((1 : ℕ) : ℤ) from
        formPow (exteriorPower.ιMulti T.functionField 2 ![u⁻¹ • KaehlerDifferential.D k _ u,
          w⁻¹ • KaehlerDifferential.D k _ w]) 1) = -1 ∧ BT.coeff C = 1 := by
  letI := functionFieldAlgebra sT
  set θ : RationalPluriForms sT 2 ((1 : ℕ) : ℤ) := formPow (exteriorPower.ιMulti T.functionField 2
    ![u⁻¹ • KaehlerDifferential.D k _ u, w⁻¹ • KaehlerDifferential.D k _ w]) 1 with hθdef
  obtain ⟨E', hE'p, hE'⟩ := exists_properDivisorOver_ordPullback_dlog_eq_neg_one hT hd u w hu hw hgen
  haveI : LocallyOfFiniteType sT := hT.1.toLocallyOfFiniteType
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have hθ0 : θ ≠ 0 := by
    intro h0
    rw [← hθdef, h0] at hE'
    have := E'.isIntegral
    have := E'.isLocallyNoetherian
    have := E'.isDominant
    have h1 : pullbackRationalPluriForms sT E'.f (0 : RationalPluriForms sT 2 ((1 : ℕ) : ℤ)) = 0 := by
      let := functionFieldAlgebra (E'.f ≫ sT)
      let := functionFieldMapAlgebra E'.f
      have := isScalarTower_functionFieldMap sT E'.f
      have h := pullbackForms_smul (K' := E'.Y.functionField) (k := k) (d := 2) (m := ((1 : ℕ) : ℤ))
        (0 : T.functionField) (0 : RationalPluriForms sT 2 ((1 : ℕ) : ℤ))
      simp only [zero_smul, map_zero] at h
      exact h
    have h2 : E'.ordPullback (0 : RationalPluriForms sT 2 ((1 : ℕ) : ℤ)) = 0 := by
      unfold MMP.Mori.DivisorOver.ordPullback
      rw [h1, Mori.PrimeDivisor.ordForm_zero]
    rw [h2] at hE'
    exact absurd hE' (by decide)
  have hK := isCanonicalDivisor_divisorOfForm hT hd hθ0
  have hKB : Divisor.toQDivisor (divisorOfForm θ) + BT = 0 := by
    ext Γ
    rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm,
      DivisorWithCoeffs.coeff_zero]
    exact hθ Γ
  have hcart : ((1 : ℕ) : ℤ) • (Divisor.toQDivisor (divisorOfForm θ) + BT) |>.IsCartierDivisor := by
    rw [hKB, smul_zero]
    exact ⟨0, by simp, Divisor.isCartier_zero⟩
  have hP : MMP.Mori.IsPairWith sT 2 (divisorOfForm θ) BT :=
    ⟨hT, hK, ⟨1, one_ne_zero, by simpa using hcart⟩⟩
  have hdisc : MMP.Mori.IsDiscrepancy sT 2 (divisorOfForm θ) BT E' (-1) := by
    refine ⟨hT, hK, 1, one_pos, hcart, ⊤, TopologicalSpace.Opens.mem_top _, θ, ⟨hθ0, fun Γ _ => ?_⟩, ?_⟩
    · have := hθ Γ
      push_cast
      linarith
    · rw [← hθdef] at hE'
      rw [hE']
      norm_num
  obtain ⟨c, z, L, α, hz, -, hLx, -, -, hL1, -⟩ :=
    exists_sncCoordinates_of_isDiscrepancy_neg_one hdlt hP E' hE'p hdisc
  have hc : 0 < c := by
    by_contra h0
    have hc0 : c = 0 := by omega
    have h1 := one_le_coheight_map_genericPoint' E'
    have h2 := hz.2
    rw [ringKrullDim_stalk_eq_coheight, hc0] at h2
    have : Order.coheight (E'.f E'.E.genericPoint) = 0 := by exact_mod_cast h2
    rw [this] at h1
    exact absurd h1 (by decide)
  refine ⟨L ⟨0, hc⟩, ?_, hL1 _⟩
  have := hθ (L ⟨0, hc⟩)
  rw [hL1] at this
  have h2 : ((L ⟨0, hc⟩).ordForm θ : ℚ) = -1 := by linarith
  exact_mod_cast h2

end AffinePlaneModel

section MonomialFrame

/-- Elements of a weighted monomial ideal of level `m` have valuation at most `exp (-m)`. -/
private theorem valuation_le_of_mem_weightedMonomialIdeal {R K : Type*} [CommRing R] [Field K]
    [Algebra R K] {ι : Type*} [Fintype ι] (z : ι → R) (α : ι → ℕ) (v : Valuation K ℤᵐ⁰)
    (hle : ∀ r : R, v (algebraMap R K r) ≤ 1)
    (hz : ∀ i, v (algebraMap R K (z i)) = WithZero.exp (-(α i : ℤ))) {m : ℕ} {f : R}
    (hf : f ∈ weightedMonomialIdeal z α m) :
    v (algebraMap R K f) ≤ WithZero.exp (-(m : ℤ)) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    rw [valuation_prod_pow_eq z α v hz β, WithZero.exp_le_exp]
    have : (m : ℤ) ≤ ((∑ i, α i * β i : ℕ) : ℤ) := by exact_mod_cast hβ
    omega
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (v.map_add _ _).trans (max_le hx hy)
  | smul r x _ hx =>
    rw [smul_eq_mul, map_mul, map_mul]
    calc v (algebraMap R K r) * v (algebraMap R K x) ≤ 1 * WithZero.exp (-(m : ℤ)) := by
          gcongr
          exact hle r
      _ = _ := one_mul _

/-- If all weights are divisible by `d`, so is every level at which a monomial valuation is
attained. -/
private theorem dvd_of_mem_weightedMonomialIdeal {R K : Type*} [CommRing R] [Field K]
    [Algebra R K] {ι : Type*} [Fintype ι] (z : ι → R) (α : ι → ℕ) (v : Valuation K ℤᵐ⁰)
    (hle : ∀ r : R, v (algebraMap R K r) ≤ 1)
    (hz : ∀ i, v (algebraMap R K (z i)) = WithZero.exp (-(α i : ℤ))) {d : ℕ} (hd : 0 < d)
    (hdα : ∀ i, d ∣ α i) {M : ℕ} {f : R} (hf : f ∈ weightedMonomialIdeal z α M)
    (hv : v (algebraMap R K f) = WithZero.exp (-(M : ℤ))) : d ∣ M := by
  set M' := d * ((M + d - 1) / d) with hM'
  have hle' : M ≤ M' := by
    rw [hM']
    have := Nat.lt_div_mul_add (a := M + d - 1) hd
    have h2 : (M + d - 1) / d * d = d * ((M + d - 1) / d) := mul_comm _ _
    omega
  have hmem : f ∈ weightedMonomialIdeal z α M' := by
    refine (Ideal.span_mono ?_) hf
    rintro r ⟨β, hβ, rfl⟩
    refine ⟨β, ?_, rfl⟩
    have hdvd : d ∣ ∑ i, α i * β i := Finset.dvd_sum fun i _ => (hdα i).mul_right _
    obtain ⟨q, hq⟩ := hdvd
    rw [hM', hq]
    refine Nat.mul_le_mul_left d ?_
    rw [hq] at hβ
    calc (M + d - 1) / d = (M + (d - 1)) / d := by rw [Nat.add_sub_assoc hd]
      _ ≤ (d * q + (d - 1)) / d := Nat.div_le_div_right (Nat.add_le_add_right hβ _)
      _ = q := by rw [Nat.mul_add_div hd, Nat.div_eq_of_lt (by omega), add_zero]
  have h1 := valuation_le_of_mem_weightedMonomialIdeal z α v hle hz hmem
  rw [hv, WithZero.exp_le_exp] at h1
  have hMM : M' ≤ M := by omega
  have : M = M' := le_antisymm hle' hMM
  rw [this, hM']
  exact Dvd.intro _ rfl

/-- **Normalised monomial valuations have primitive weights.** If `v` is monomial in `z` with
weights `α` on a domain `R` and takes the value `exp (-1)` on its fraction field, then the only
common divisor of the weights is `1`: writing an element of value `exp (-1)` as `a / b`, the
levels of `a` and `b` are consecutive multiples of every common divisor. -/
private theorem eq_one_of_forall_dvd_of_monomial {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] {ι : Type*} [Fintype ι] (z : ι → R)
    (α : ι → ℕ) (v : Valuation K ℤᵐ⁰)
    (hle : ∀ r : R, v (algebraMap R K r) ≤ 1)
    (hz : ∀ i, v (algebraMap R K (z i)) = WithZero.exp (-(α i : ℤ)))
    (hmono : ∀ f : R, f ≠ 0 → ∃ M : ℕ, f ∈ weightedMonomialIdeal z α M ∧
      v (algebraMap R K f) = WithZero.exp (-(M : ℤ)))
    (hT : ∃ g : K, v g = WithZero.exp (-1)) {d : ℕ}
    (hdα : ∀ i, d ∣ α i) : d = 1 := by
  obtain ⟨g, hg⟩ := hT
  have hg0 : g ≠ 0 := fun h => by rw [h, map_zero] at hg; exact WithZero.exp_ne_zero hg.symm
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) g
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := fun h => hg0 (by rw [h, map_zero, zero_div])
  obtain ⟨Ma, hMa, hva⟩ := hmono a ha0
  obtain ⟨Mb, hMb, hvb⟩ := hmono b hb0
  rw [map_div₀, hva, hvb, ← WithZero.exp_sub, WithZero.exp_inj] at hg
  have hMab : Ma = Mb + 1 := by omega
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · exfalso
    have hα0 : ∀ i, α i = 0 := fun i => Nat.eq_zero_of_zero_dvd (h0 ▸ hdα i)
    have hbot : weightedMonomialIdeal z α Ma = ⊥ := by
      rw [weightedMonomialIdeal, Ideal.span_eq_bot]
      rintro r ⟨β, hβ, rfl⟩
      simp [hα0] at hβ
      omega
    rw [hbot] at hMa
    exact ha0 hMa
  · have h1 := dvd_of_mem_weightedMonomialIdeal z α v hle hz hpos hdα hMa hva
    have h2 := dvd_of_mem_weightedMonomialIdeal z α v hle hz hpos hdα hMb hvb
    rw [hMab] at h1
    exact Nat.eq_one_of_dvd_one ((Nat.dvd_add_right h2).1 h1)

/-- `eq_one_of_forall_dvd_of_monomial` in three variables, as a `gcd`. -/
private theorem gcd_eq_one_of_monomial {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (z : Fin 3 → R) (α : Fin 3 → ℕ) (v : Valuation K ℤᵐ⁰)
    (hle : ∀ r : R, v (algebraMap R K r) ≤ 1)
    (hz : ∀ i, v (algebraMap R K (z i)) = WithZero.exp (-(α i : ℤ)))
    (hmono : ∀ f : R, f ≠ 0 → ∃ M : ℕ, f ∈ weightedMonomialIdeal z α M ∧
      v (algebraMap R K f) = WithZero.exp (-(M : ℤ)))
    (hT : ∃ g : K, v g = WithZero.exp (-1)) :
    Int.gcd (α 0 : ℤ) (Int.gcd (α 1 : ℤ) (α 2 : ℤ) : ℤ) = 1 := by
  rw [Int.gcd_natCast_natCast, Int.gcd_natCast_natCast]
  refine eq_one_of_forall_dvd_of_monomial z α v hle hz hmono hT fun i => ?_
  fin_cases i
  · exact Nat.gcd_dvd_left _ _
  · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)

/-- Valuations of integer monomials in units. -/
private theorem valuation_prod_zpow_eq {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    (v : Valuation K ℤᵐ⁰) (zU : ι → Kˣ) (α : ι → ℤ)
    (hz : ∀ i, v (zU i : K) = WithZero.exp (-α i)) (u : ι → ℤ) :
    v ((∏ i, zU i ^ u i : Kˣ) : K) = WithZero.exp (-∑ i, u i * α i) := by
  rw [Units.coe_prod, map_prod]
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀, hz, ← WithZero.exp_zsmul, prod_exp]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]; ring

/-- **The monomial frame along a log canonical place.** Let `σ : k(X') ≅ k(X)`, `P` a prime
divisor of `X` with closed immersion `ι : T ⟶ X`, and suppose `v_P ∘ σ` is monomial at a point
`x` of `X'` in a regular system of parameters `z₁, z₂, z₃` with weights `α`, the residue field of
`x` being `k`. Then there are a uniformizer `t` of `𝒪_{X,P}` and units `e₁, e₂` with
`dlog σz₁ ∧ dlog σz₂ ∧ dlog σz₃ = dlog t ∧ dlog e₁ ∧ dlog e₂`, and the residues `ē₁, ē₂`
generate `k(T)`. -/
private theorem exists_monomialFrame {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X X' T : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsIntegral T] (ι : T ⟶ X)
    [IsClosedImmersion ι] (P : Mori.PrimeDivisor X) (hP : ι (genericPoint T) = P.genericPoint)
    (σ : FunctionFieldEquiv sX sX') {x : X'} (z : Fin 3 → X'.presheaf.stalk x)
    (α : Fin 3 → ℕ) (hz0 : ∀ a, z a ≠ 0)
    (hle : ∀ r : X'.presheaf.stalk x,
      P.divisorialValuation ((σ.toHom) (algebraMap _ X'.functionField r)) ≤ 1)
    (hlt : ∀ r ∈ IsLocalRing.maximalIdeal (X'.presheaf.stalk x),
      P.divisorialValuation ((σ.toHom) (algebraMap _ X'.functionField r)) < 1)
    (hzv : ∀ a, P.divisorialValuation ((σ.toHom) (algebraMap _ X'.functionField (z a))) =
      WithZero.exp (-(α a : ℤ)))
    (hmono : ∀ f : X'.presheaf.stalk x, f ≠ 0 → ∃ M : ℕ, f ∈ weightedMonomialIdeal z α M ∧
      P.divisorialValuation ((σ.toHom) (algebraMap _ X'.functionField f)) =
        WithZero.exp (-(M : ℤ)))
    (hres : letI := stalkAlgebra sX' x
      ∀ r : X'.presheaf.stalk x, ∃ c : k, r - algebraMap k _ c ∈ IsLocalRing.maximalIdeal _) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (ι ≫ sX)
    ∃ (t : X.presheaf.stalk (ι (genericPoint T))) (e : Fin 2 → X.presheaf.stalk (ι (genericPoint T))),
      (∀ i, IsUnit (e i)) ∧
      X.ord (algebraMap _ X.functionField t) (ι (genericPoint T)) = 1 ∧
      exteriorPower.ιMulti X.functionField 3 (fun a =>
          ((σ.toHom) (algebraMap _ X'.functionField (z a)))⁻¹ •
            KaehlerDifferential.D k X.functionField ((σ.toHom) (algebraMap _ X'.functionField (z a)))) =
        exteriorPower.ιMulti X.functionField 3 (Fin.cons
          ((algebraMap _ X.functionField t)⁻¹ • KaehlerDifferential.D k _ (algebraMap _ _ t))
          fun i => (algebraMap _ X.functionField (e i))⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ _ (e i))) ∧
      IntermediateField.adjoin k (Set.range fun i => (ι.stalkMap (genericPoint T)).hom (e i)) = ⊤ := by
  classical
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (ι ≫ sX)
  letI := functionFieldAlgebra sX'
  set v := P.divisorialValuation with hvdef
  letI algR : Algebra (X'.presheaf.stalk x) X.functionField :=
    ((σ.toHom : X'.functionField →ₐ[k] X.functionField).toRingHom.comp
      (algebraMap (X'.presheaf.stalk x) X'.functionField)).toAlgebra
  have halgR : ∀ r : (X'.presheaf.stalk x), algebraMap (X'.presheaf.stalk x) X.functionField r =
      (σ.toHom) (algebraMap (X'.presheaf.stalk x) X'.functionField r) := fun _ => rfl
  haveI : IsFractionRing (X'.presheaf.stalk x) X.functionField := by
    let e : X'.functionField ≃ₐ[(X'.presheaf.stalk x)] X.functionField :=
      { σ.toRingEquiv with commutes' := fun _ => rfl }
    exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors (X'.presheaf.stalk x)) e
  -- primitive weights and a unimodular change of monomials
  have hT1 : ∃ g : X.functionField, v g = WithZero.exp (-1) := by
    haveI := P.isDiscreteValuationRing_localRing
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
    have h0 : algebraMap P.localRing X.functionField ϖ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
    refine ⟨algebraMap P.localRing X.functionField ϖ, ?_⟩
    rw [hvdef, P.divisorialValuation_eq_exp_neg_ord h0,
      (Scheme.ord_eq_iff P.coheight_genericPoint h0).mpr (Ring.ordFrac_irreducible hϖ)]
  have hgcd := gcd_eq_one_of_monomial (R := X'.presheaf.stalk x) (K := X.functionField) z α v
    (fun r => by rw [halgR]; exact hle r) (fun a => by rw [halgR]; exact hzv a)
    (fun f hf => by
      obtain ⟨M, hM, hMv⟩ := hmono f hf
      exact ⟨M, hM, by rw [halgR]; exact hMv⟩) hT1
  obtain ⟨M, hMdet, hMα⟩ := exists_det_eq_one_mulVec_eq_three (α 0) (α 1) (α 2) hgcd
  have hz0' : ∀ a, (σ.toHom) (algebraMap (X'.presheaf.stalk x) X'.functionField (z a)) ≠ 0 := fun a =>
    (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hz0 a))
  set zU : Fin 3 → (X.functionField)ˣ := fun a => Units.mk0 _ (hz0' a) with hzU
  set sU : Fin 3 → (X.functionField)ˣ := fun a => ∏ b, zU b ^ M a b with hsU
  have hαvec : (![(α 0 : ℤ), α 1, α 2] : Fin 3 → ℤ) = fun i => (α i : ℤ) := by
    funext i; fin_cases i <;> rfl
  have hsv : ∀ a, v (sU a : X.functionField) =
      WithZero.exp (-((![(1 : ℤ), 0, 0] : Fin 3 → ℤ) a)) := by
    intro a
    rw [hsU, valuation_prod_zpow_eq v zU (fun i => (α i : ℤ)) (fun i => hzv i), ← hMα, hαvec]
    rfl
  have hs0 : v (sU 0 : X.functionField) = WithZero.exp (-1) := by rw [hsv]; rfl
  have hs1 : ∀ a, a ≠ 0 → v (sU a : X.functionField) = 1 := by
    intro a ha
    rw [hsv]
    fin_cases a
    · exact absurd rfl ha
    · rfl
    · rfl
  -- the uniformizer `t = s₀` and the units `e = (s₁, s₂)` in `𝒪_{X,P}`
  obtain ⟨t, ht⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one P hP (hs0.le.trans
    (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega))
  have he : ∀ i : Fin 2, ∃ c : X.presheaf.stalk (ι (genericPoint T)),
      algebraMap _ X.functionField c = (sU i.succ : X.functionField) := fun i =>
    exists_algebraMap_eq_of_divisorialValuation_le_one P hP (hs1 _ (Fin.succ_ne_zero i)).le
  choose e he using he
  have heu : ∀ i, IsUnit (e i) := by
    intro i
    by_contra hnu
    have hm := (mem_maximalIdeal_iff_divisorialValuation_lt_one P hP (e i)).1
      ((IsLocalRing.mem_maximalIdeal _).2 hnu)
    rw [he, hs1 _ (Fin.succ_ne_zero i)] at hm
    exact lt_irrefl _ hm
  have ht1 : X.ord (algebraMap _ X.functionField t) (ι (genericPoint T)) = 1 := by
    have h0 : algebraMap _ X.functionField t ≠ 0 := by rw [ht]; exact (sU 0).ne_zero
    have h := P.divisorialValuation_eq_exp_neg_ord h0
    rw [← hvdef, ht, hs0, WithZero.exp_inj, neg_inj] at h
    rw [ht, hP]
    exact h.symm
  refine ⟨t, e, heu, ht1, ?_, ?_⟩
  · -- the `dlog`-forms agree, `det M = 1`
    have h1 := ιMulti_dlogHom_monomial k X.functionField zU M
    rw [hMdet, Int.cast_one, one_smul] at h1
    have hL : (fun a => ((σ.toHom) (algebraMap _ X'.functionField (z a)))⁻¹ •
        KaehlerDifferential.D k X.functionField ((σ.toHom) (algebraMap _ X'.functionField (z a)))) =
        fun b => Multiplicative.toAdd (dlogHom k X.functionField (zU b)) := rfl
    have hR : (Fin.cons ((algebraMap _ X.functionField t)⁻¹ •
          KaehlerDifferential.D k _ (algebraMap _ _ t))
          fun i => (algebraMap _ X.functionField (e i))⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ _ (e i)) : Fin 3 → Ω[X.functionField⁄k]) =
        fun a => Multiplicative.toAdd (dlogHom k X.functionField (∏ b, zU b ^ M a b)) := by
      funext a
      refine Fin.cases ?_ (fun i => ?_) a
      · simp only [Fin.cons_zero, ht]; rfl
      · simp only [Fin.cons_succ, he]; rfl
    rw [hL, hR, h1]
  · -- the residues `ē₁, ē₂` generate `k(T)`
    have hvst : ∀ a : X.presheaf.stalk (ι (genericPoint T)),
        v (algebraMap _ X.functionField a) ≤ 1 := by
      intro a
      have : ∃ c' : P.localRing, algebraMap P.localRing X.functionField c' =
          algebraMap _ X.functionField a := by
        revert a; rw [hP]; intro a; exact ⟨a, rfl⟩
      obtain ⟨c', hc'⟩ := this
      rw [← hc']
      exact (P.divisorialValuation_le_one_iff _).2 ⟨c', rfl⟩
    have hk : ∀ c : k, residueAlong ι P hP (algebraMap k X.functionField c) =
        algebraMap k T.functionField c := by
      intro c
      letI := stalkAlgebra sX (ι (genericPoint T))
      haveI := isScalarTower_stalk_functionField sX (ι (genericPoint T))
      rw [IsScalarTower.algebraMap_apply k (X.presheaf.stalk (ι (genericPoint T))) X.functionField c,
        residueAlong_algebraMap]
      change ((ι.stalkMap (genericPoint T)).hom ((((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ _ (TopologicalSpace.Opens.mem_top _)).hom) c)) =
        (((Scheme.ΓSpecIso (.of k)).inv ≫ (ι ≫ sX).appTop ≫
          T.presheaf.germ ⊤ _ (TopologicalSpace.Opens.mem_top _)).hom c)
      rw [← CommRingCat.comp_apply, Category.assoc, Category.assoc, Scheme.Hom.germ_stalkMap,
        Scheme.Hom.comp_appTop, Category.assoc]
      rfl
    have hkv : ∀ c : k, v (algebraMap k X.functionField c) ≤ 1 := by
      intro c
      letI := stalkAlgebra sX (ι (genericPoint T))
      haveI := isScalarTower_stalk_functionField sX (ι (genericPoint T))
      rw [IsScalarTower.algebraMap_apply k (X.presheaf.stalk (ι (genericPoint T))) X.functionField c]
      exact hvst _
    have hconst : ∀ r : X'.presheaf.stalk x, ∃ c : k, v (algebraMap (X'.presheaf.stalk x)
        X.functionField r - algebraMap k X.functionField c) < 1 := by
      intro r
      letI := stalkAlgebra sX' x
      haveI := isScalarTower_stalk_functionField sX' x
      obtain ⟨c, hc⟩ := hres r
      refine ⟨c, ?_⟩
      have h := hlt _ hc
      rwa [map_sub, map_sub, ← IsScalarTower.algebraMap_apply, AlgHom.commutes, ← halgR] at h
    have hinv : M⁻¹.mulVec ![1, 0, 0] = ![(α 0 : ℤ), α 1, α 2] := by
      rw [← hMα, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (by rw [hMdet]; exact isUnit_one),
        Matrix.one_mulVec]
    have hcolM : ∀ b, M⁻¹ b 0 = (α b : ℤ) := by
      intro b
      have := congrFun hinv b
      rw [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
      simp at this
      rw [this, hαvec]
    have hcol : ∀ u : Fin 3 → ℤ, Matrix.vecMul u M⁻¹ 0 = ∑ i, (α i : ℤ) * u i := by
      intro u
      rw [Matrix.vecMul, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcolM, mul_comm]
    have hrow : ∑ i, (α i : ℤ) * M 0 i = 1 := by
      have := congrFun hMα 0
      rw [Matrix.mulVec, dotProduct, hαvec] at this
      exact (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans this
    refine eq_top_of_residueAlong_monomial_mem ι P hP hk hkv (R := X'.presheaf.stalk x) z α
      (fun r => by rw [halgR]; exact hle r) (fun a => by rw [halgR]; exact hzv a)
      (fun f hf => by
        obtain ⟨M', hM', hMv⟩ := hmono f hf
        exact ⟨M', hM', by rw [halgR]; exact hMv⟩)
      (sU 0 : X.functionField) hs0 hconst _ fun β => ?_
    have h := residueAlong_monomial_mem_adjoin (k := k) ι P hP zU α M
      (by rw [hMdet]; exact isUnit_one) 0 hcol hrow (fun a ha => hs1 a ha) β
    have heq : algebraMap (X'.presheaf.stalk x) X.functionField (∏ i, z i ^ β i) =
        ∏ i, ((zU i : X.functionField)) ^ β i := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_pow, halgR]
      rfl
    rw [heq]
    refine (IntermediateField.adjoin_le_iff.2 ?_) h
    rintro _ ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 ha
    change residueAlong ι P hP (sU i.succ : X.functionField) ∈ _
    rw [← he i, residueAlong_algebraMap]
    exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩

/-- `eq_one_of_forall_dvd_of_monomial` in two variables, as a `gcd`. -/
private theorem gcd_eq_one_of_monomial_two {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (z : Fin 2 → R) (α : Fin 2 → ℕ) (v : Valuation K ℤᵐ⁰)
    (hle : ∀ r : R, v (algebraMap R K r) ≤ 1)
    (hz : ∀ i, v (algebraMap R K (z i)) = WithZero.exp (-(α i : ℤ)))
    (hmono : ∀ f : R, f ≠ 0 → ∃ M : ℕ, f ∈ weightedMonomialIdeal z α M ∧
      v (algebraMap R K f) = WithZero.exp (-(M : ℤ)))
    (hT : ∃ g : K, v g = WithZero.exp (-1)) :
    Int.gcd (α 0 : ℤ) (α 1 : ℤ) = 1 := by
  rw [Int.gcd_natCast_natCast]
  refine eq_one_of_forall_dvd_of_monomial z α v hle hz hmono hT fun i => ?_
  fin_cases i
  · exact Nat.gcd_dvd_left _ _
  · exact Nat.gcd_dvd_right _ _

/-- **The monomial frame along a log canonical place, in two variables.** Let `σ : k(X') ≅ k(X)`,
`P` a prime divisor of `X` with closed immersion `ι : T ⟶ X`, and suppose `v_P ∘ σ` is monomial at
a point `x` of `X'` in a regular system of parameters `z₁, z₂` with weights `α`, the residue field
of `x` being `k`. Then there are a uniformizer `t` of `𝒪_{X,P}` and a unit `e₁` with
`dlog σz₁ ∧ dlog σz₂ = dlog t ∧ dlog e₁`, and the residue `ē₁` generates `k(T)`. -/
private theorem exists_monomialFrame_two {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X X' T : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsIntegral T] (ι : T ⟶ X)
    [IsClosedImmersion ι] (P : Mori.PrimeDivisor X) (hP : ι (genericPoint T) = P.genericPoint)
    (σ : FunctionFieldEquiv sX sX') {x : X'} (z : Fin 2 → X'.presheaf.stalk x)
    (α : Fin 2 → ℕ) (hz0 : ∀ a, z a ≠ 0)
    (hle : ∀ r : X'.presheaf.stalk x,
      P.divisorialValuation ((σ.toHom) (algebraMap _ X'.functionField r)) ≤ 1)
    (hlt : ∀ r ∈ IsLocalRing.maximalIdeal (X'.presheaf.stalk x),
      P.divisorialValuation ((σ.toHom) (algebraMap _ X'.functionField r)) < 1)
    (hzv : ∀ a, P.divisorialValuation ((σ.toHom) (algebraMap _ X'.functionField (z a))) =
      WithZero.exp (-(α a : ℤ)))
    (hmono : ∀ f : X'.presheaf.stalk x, f ≠ 0 → ∃ M : ℕ, f ∈ weightedMonomialIdeal z α M ∧
      P.divisorialValuation ((σ.toHom) (algebraMap _ X'.functionField f)) =
        WithZero.exp (-(M : ℤ)))
    (hres : letI := stalkAlgebra sX' x
      ∀ r : X'.presheaf.stalk x, ∃ c : k, r - algebraMap k _ c ∈ IsLocalRing.maximalIdeal _) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (ι ≫ sX)
    ∃ (t : X.presheaf.stalk (ι (genericPoint T))) (e : Fin 1 → X.presheaf.stalk (ι (genericPoint T))),
      (∀ i, IsUnit (e i)) ∧
      X.ord (algebraMap _ X.functionField t) (ι (genericPoint T)) = 1 ∧
      exteriorPower.ιMulti X.functionField 2 (fun a =>
          ((σ.toHom) (algebraMap _ X'.functionField (z a)))⁻¹ •
            KaehlerDifferential.D k X.functionField ((σ.toHom) (algebraMap _ X'.functionField (z a)))) =
        exteriorPower.ιMulti X.functionField 2 (Fin.cons
          ((algebraMap _ X.functionField t)⁻¹ • KaehlerDifferential.D k _ (algebraMap _ _ t))
          fun i => (algebraMap _ X.functionField (e i))⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ _ (e i))) ∧
      IntermediateField.adjoin k (Set.range fun i => (ι.stalkMap (genericPoint T)).hom (e i)) = ⊤ := by
  classical
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (ι ≫ sX)
  letI := functionFieldAlgebra sX'
  set v := P.divisorialValuation with hvdef
  letI algR : Algebra (X'.presheaf.stalk x) X.functionField :=
    ((σ.toHom : X'.functionField →ₐ[k] X.functionField).toRingHom.comp
      (algebraMap (X'.presheaf.stalk x) X'.functionField)).toAlgebra
  have halgR : ∀ r : (X'.presheaf.stalk x), algebraMap (X'.presheaf.stalk x) X.functionField r =
      (σ.toHom) (algebraMap (X'.presheaf.stalk x) X'.functionField r) := fun _ => rfl
  haveI : IsFractionRing (X'.presheaf.stalk x) X.functionField := by
    let e : X'.functionField ≃ₐ[(X'.presheaf.stalk x)] X.functionField :=
      { σ.toRingEquiv with commutes' := fun _ => rfl }
    exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors (X'.presheaf.stalk x)) e
  -- primitive weights and a unimodular change of monomials
  have hT1 : ∃ g : X.functionField, v g = WithZero.exp (-1) := by
    haveI := P.isDiscreteValuationRing_localRing
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
    have h0 : algebraMap P.localRing X.functionField ϖ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
    refine ⟨algebraMap P.localRing X.functionField ϖ, ?_⟩
    rw [hvdef, P.divisorialValuation_eq_exp_neg_ord h0,
      (Scheme.ord_eq_iff P.coheight_genericPoint h0).mpr (Ring.ordFrac_irreducible hϖ)]
  have hgcd := gcd_eq_one_of_monomial_two (R := X'.presheaf.stalk x) (K := X.functionField) z α v
    (fun r => by rw [halgR]; exact hle r) (fun a => by rw [halgR]; exact hzv a)
    (fun f hf => by
      obtain ⟨M, hM, hMv⟩ := hmono f hf
      exact ⟨M, hM, by rw [halgR]; exact hMv⟩) hT1
  obtain ⟨M, hMdet, hMα⟩ := exists_det_eq_one_mulVec_eq (α 0) (α 1)
  rw [hgcd] at hMα
  have hz0' : ∀ a, (σ.toHom) (algebraMap (X'.presheaf.stalk x) X'.functionField (z a)) ≠ 0 := fun a =>
    (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hz0 a))
  set zU : Fin 2 → (X.functionField)ˣ := fun a => Units.mk0 _ (hz0' a) with hzU
  set sU : Fin 2 → (X.functionField)ˣ := fun a => ∏ b, zU b ^ M a b with hsU
  have hαvec : (![(α 0 : ℤ), α 1] : Fin 2 → ℤ) = fun i => (α i : ℤ) := by
    funext i; fin_cases i <;> rfl
  have hsv : ∀ a, v (sU a : X.functionField) =
      WithZero.exp (-((![((1 : ℕ) : ℤ), 0] : Fin 2 → ℤ) a)) := by
    intro a
    rw [hsU, valuation_prod_zpow_eq v zU (fun i => (α i : ℤ)) (fun i => hzv i), ← hMα, hαvec]
    rfl
  have hs0 : v (sU 0 : X.functionField) = WithZero.exp (-1) := by rw [hsv]; rfl
  have hs1 : ∀ a, a ≠ 0 → v (sU a : X.functionField) = 1 := by
    intro a ha
    rw [hsv]
    fin_cases a
    · exact absurd rfl ha
    · rfl
  -- the uniformizer `t = s₀` and the units `e = (s₁, s₂)` in `𝒪_{X,P}`
  obtain ⟨t, ht⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one P hP (hs0.le.trans
    (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega))
  have he : ∀ i : Fin 1, ∃ c : X.presheaf.stalk (ι (genericPoint T)),
      algebraMap _ X.functionField c = (sU i.succ : X.functionField) := fun i =>
    exists_algebraMap_eq_of_divisorialValuation_le_one P hP (hs1 _ (Fin.succ_ne_zero i)).le
  choose e he using he
  have heu : ∀ i, IsUnit (e i) := by
    intro i
    by_contra hnu
    have hm := (mem_maximalIdeal_iff_divisorialValuation_lt_one P hP (e i)).1
      ((IsLocalRing.mem_maximalIdeal _).2 hnu)
    rw [he, hs1 _ (Fin.succ_ne_zero i)] at hm
    exact lt_irrefl _ hm
  have ht1 : X.ord (algebraMap _ X.functionField t) (ι (genericPoint T)) = 1 := by
    have h0 : algebraMap _ X.functionField t ≠ 0 := by rw [ht]; exact (sU 0).ne_zero
    have h := P.divisorialValuation_eq_exp_neg_ord h0
    rw [← hvdef, ht, hs0, WithZero.exp_inj, neg_inj] at h
    rw [ht, hP]
    exact h.symm
  refine ⟨t, e, heu, ht1, ?_, ?_⟩
  · -- the `dlog`-forms agree, `det M = 1`
    have h1 := ιMulti_dlogHom_monomial k X.functionField zU M
    rw [hMdet, Int.cast_one, one_smul] at h1
    have hL : (fun a => ((σ.toHom) (algebraMap _ X'.functionField (z a)))⁻¹ •
        KaehlerDifferential.D k X.functionField ((σ.toHom) (algebraMap _ X'.functionField (z a)))) =
        fun b => Multiplicative.toAdd (dlogHom k X.functionField (zU b)) := rfl
    have hR : (Fin.cons ((algebraMap _ X.functionField t)⁻¹ •
          KaehlerDifferential.D k _ (algebraMap _ _ t))
          fun i => (algebraMap _ X.functionField (e i))⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ _ (e i)) : Fin 2 → Ω[X.functionField⁄k]) =
        fun a => Multiplicative.toAdd (dlogHom k X.functionField (∏ b, zU b ^ M a b)) := by
      funext a
      refine Fin.cases ?_ (fun i => ?_) a
      · simp only [Fin.cons_zero, ht]; rfl
      · simp only [Fin.cons_succ, he]; rfl
    rw [hL, hR, h1]
  · -- the residues `ē₁, ē₂` generate `k(T)`
    have hvst : ∀ a : X.presheaf.stalk (ι (genericPoint T)),
        v (algebraMap _ X.functionField a) ≤ 1 := by
      intro a
      have : ∃ c' : P.localRing, algebraMap P.localRing X.functionField c' =
          algebraMap _ X.functionField a := by
        revert a; rw [hP]; intro a; exact ⟨a, rfl⟩
      obtain ⟨c', hc'⟩ := this
      rw [← hc']
      exact (P.divisorialValuation_le_one_iff _).2 ⟨c', rfl⟩
    have hk : ∀ c : k, residueAlong ι P hP (algebraMap k X.functionField c) =
        algebraMap k T.functionField c := by
      intro c
      letI := stalkAlgebra sX (ι (genericPoint T))
      haveI := isScalarTower_stalk_functionField sX (ι (genericPoint T))
      rw [IsScalarTower.algebraMap_apply k (X.presheaf.stalk (ι (genericPoint T))) X.functionField c,
        residueAlong_algebraMap]
      change ((ι.stalkMap (genericPoint T)).hom ((((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ _ (TopologicalSpace.Opens.mem_top _)).hom) c)) =
        (((Scheme.ΓSpecIso (.of k)).inv ≫ (ι ≫ sX).appTop ≫
          T.presheaf.germ ⊤ _ (TopologicalSpace.Opens.mem_top _)).hom c)
      rw [← CommRingCat.comp_apply, Category.assoc, Category.assoc, Scheme.Hom.germ_stalkMap,
        Scheme.Hom.comp_appTop, Category.assoc]
      rfl
    have hkv : ∀ c : k, v (algebraMap k X.functionField c) ≤ 1 := by
      intro c
      letI := stalkAlgebra sX (ι (genericPoint T))
      haveI := isScalarTower_stalk_functionField sX (ι (genericPoint T))
      rw [IsScalarTower.algebraMap_apply k (X.presheaf.stalk (ι (genericPoint T))) X.functionField c]
      exact hvst _
    have hconst : ∀ r : X'.presheaf.stalk x, ∃ c : k, v (algebraMap (X'.presheaf.stalk x)
        X.functionField r - algebraMap k X.functionField c) < 1 := by
      intro r
      letI := stalkAlgebra sX' x
      haveI := isScalarTower_stalk_functionField sX' x
      obtain ⟨c, hc⟩ := hres r
      refine ⟨c, ?_⟩
      have h := hlt _ hc
      rwa [map_sub, map_sub, ← IsScalarTower.algebraMap_apply, AlgHom.commutes, ← halgR] at h
    have hinv : M⁻¹.mulVec ![((1 : ℕ) : ℤ), 0] = ![(α 0 : ℤ), α 1] := by
      rw [← hMα, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (by rw [hMdet]; exact isUnit_one),
        Matrix.one_mulVec]
    have hcolM : ∀ b, M⁻¹ b 0 = (α b : ℤ) := by
      intro b
      have := congrFun hinv b
      rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      simp at this
      rw [this, hαvec]
    have hcol : ∀ u : Fin 2 → ℤ, Matrix.vecMul u M⁻¹ 0 = ∑ i, (α i : ℤ) * u i := by
      intro u
      rw [Matrix.vecMul, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcolM, mul_comm]
    have hrow : ∑ i, (α i : ℤ) * M 0 i = 1 := by
      have := congrFun hMα 0
      rw [Matrix.mulVec, dotProduct, hαvec] at this
      exact (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans this
    refine eq_top_of_residueAlong_monomial_mem ι P hP hk hkv (R := X'.presheaf.stalk x) z α
      (fun r => by rw [halgR]; exact hle r) (fun a => by rw [halgR]; exact hzv a)
      (fun f hf => by
        obtain ⟨M', hM', hMv⟩ := hmono f hf
        exact ⟨M', hM', by rw [halgR]; exact hMv⟩)
      (sU 0 : X.functionField) hs0 hconst _ fun β => ?_
    have h := residueAlong_monomial_mem_adjoin (k := k) ι P hP zU α M
      (by rw [hMdet]; exact isUnit_one) 0 hcol hrow (fun a ha => hs1 a ha) β
    have heq : algebraMap (X'.presheaf.stalk x) X.functionField (∏ i, z i ^ β i) =
        ∏ i, ((zU i : X.functionField)) ^ β i := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_pow, halgR]
      rfl
    rw [heq]
    refine (IntermediateField.adjoin_le_iff.2 ?_) h
    rintro _ ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 ha
    change residueAlong ι P hP (sU i.succ : X.functionField) ∈ _
    rw [← he i, residueAlong_algebraMap]
    exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩

end MonomialFrame

section FloorFlags

/-- In a quasi-compact scheme of dimension at most `d`, a point of coheight at least `d` is
closed. -/
private theorem isClosed_singleton_of_le_coheight {X : Scheme.{0}} [CompactSpace X] {d : ℕ}
    (hdim : topologicalKrullDim X ≤ d) {x : X} (hx : (d : ℕ∞) ≤ Order.coheight x) :
    IsClosed ({x} : Set X) := by
  by_contra hcl
  obtain ⟨c, -, hxc, hne⟩ := exists_isClosed_singleton_specializes hcl
  have hlt : c < x := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hxc)
    fun h => hne (hxc.antisymm (Scheme.le_iff_specializes.mp h)).eq
  have h3 : ∀ y : X, Order.coheight y ≤ (d : ℕ∞) := fun y => by
    have := (AlgebraicGeometry.coheight_le_topologicalKrullDim y).trans hdim
    exact_mod_cast this
  have h1 : Order.coheight x < Order.coheight c :=
    Order.coheight_strictAnti hlt ((h3 x).trans_lt (WithTop.coe_lt_top d))
  replace h3 := h3 c
  exact absurd (hx.trans_lt (h1.trans_le h3)) (lt_irrefl _)

/-- At a closed point of a scheme locally of finite type over an algebraically closed field `k`,
every element of the local ring is congruent to a constant modulo the maximal ideal. -/
private theorem exists_sub_mem_maximalIdeal_of_isClosed {k : Type} [Field k] [IsAlgClosed k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (x : X)
    (hx : IsClosed ({x} : Set X)) :
    letI := stalkAlgebra sX x
    ∀ r : X.presheaf.stalk x, ∃ c : k, r - algebraMap k _ c ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  letI := stalkAlgebra sX x
  have hfin := MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sX x hx
  intro r
  have hint : Algebra.IsIntegral k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    Algebra.IsIntegral.of_finite k _
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
    (K := IsLocalRing.ResidueField (X.presheaf.stalk x))).2 (IsLocalRing.residue _ r)
  refine ⟨c, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc, IsScalarTower.algebraMap_apply k
    (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x))]
  exact sub_self _

/-- **A coefficient-one prime divisor of a dlt pair is a dlt stratum**: it is the intersection
of the single floor divisor `L`. -/
private theorem isDltStratum_support_of_one_le_coeff {k : Type} [Field k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {BY : QDivisor Y} (hdlt : MMP.Intersection.IsDltPair sY BY) (L : MMP.Mori.PrimeDivisor Y)
    (hL : 1 ≤ BY.coeff L) : IsDltStratum sY BY (L.support : Set Y) := by
  refine ⟨hdlt, {L}, Finset.singleton_nonempty _, by simpa using hL, ?_, ?_⟩
  · simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left]
    exact ⟨L.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support L⟩
  · simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left]
    refine ⟨⟨?_, le_rfl⟩, fun T hT _ => hT.2⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure

/-- **Adjunction to a coefficient-one prime divisor of a dlt pair.** Every prime divisor `L` of a
dlt pair `(Y, B_Y)` of dimension `e + 1` with `coeff_L B_Y ≥ 1` is the image of an adjunction step
`T ⟶ Y` with `dim T = e`. -/
private theorem exists_isAdjunctionStep_of_isDltPair {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : IsNormalVariety k sY) {BY : QDivisor Y}
    (hdlt : MMP.Intersection.IsDltPair sY BY) {e : ℕ}
    (hdim : topologicalKrullDim Y = (e + 1 : ℕ)) (L : MMP.Mori.PrimeDivisor Y)
    (hL : 1 ≤ BY.coeff L) :
    ∃ (T : Scheme.{0}) (ι : T ⟶ Y) (BT : QDivisor T) (_ : MMP.Mori.IsPair sY BY)
      (_ : IsAdjunctionStep (𝟙 Y ≫ sY) BY ι BT) (_ : IsIntegral T),
      Set.range ι.base = (L.support : Set Y) ∧ topologicalKrullDim T = e := by
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have hstr := isDltStratum_support_of_one_le_coeff hdlt L hL
  obtain ⟨⟨⟨T', ι', BT', hr', ⟨F'⟩⟩, -⟩, -⟩ := hstr.exists_isStratumAdjunctionPair_and_isDltPair
  haveI := F'.isIntegral_stratum
  haveI := F'.isClosedImmersion
  have hdimT' : topologicalKrullDim T' = e :=
    topologicalKrullDim_eq_of_range_eq_support sY ι' L hr' hdim
  have hlen := F'.dim_add_length hdim hdimT'
  cases F' with
  | refl h' => simp [StratumAdjunctionData.length] at hlen
  | step F'' j'' BT'' hj'' =>
    cases F'' with
    | step F3 _ _ _ => simp [StratumAdjunctionData.length] at hlen <;> omega
    | refl h' => exact ⟨T', j'', BT', h', hj'', inferInstance, hr', hdimT'⟩

/-- The adjunction pair of a step out of a dlt pair is dlt. -/
private theorem isDltPair_of_isAdjunctionStep {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {BY : QDivisor Y} (hdlt : MMP.Intersection.IsDltPair sY BY) (h : MMP.Mori.IsPair sY BY)
    {T : Scheme.{0}} {ι : T ⟶ Y} {BT : QDivisor T} (hι : IsAdjunctionStep (𝟙 Y ≫ sY) BY ι BT)
    (L : MMP.Mori.PrimeDivisor Y) (hL : 1 ≤ BY.coeff L)
    (hr : Set.range ι.base = (L.support : Set Y)) [IsIntegral T] [IsNormal T]
    [IsLocallyNoetherian T] : MMP.Intersection.IsDltPair (ι ≫ sY) BT := by
  have hstr := isDltStratum_support_of_one_le_coeff hdlt L hL
  obtain ⟨⟨-, hdl⟩, -⟩ := hstr.exists_isStratumAdjunctionPair_and_isDltPair
  have h2 := hdl (StratumAdjunctionData.step (.refl h) ι BT hι) (by simpa using hr)
  simpa using h2

/-- Poincaré residues do not depend on the structure morphism beyond equality. -/
private theorem IsPoincareResidue.congr_structure {k : Type} [Field k] {Y T : Scheme.{0}}
    {s s' : Y ⟶ Spec (.of k)} (hs : s = s') [IsIntegral Y] [IsLocallyNoetherian Y] [IsIntegral T]
    {j : T ⟶ Y} {n m : ℕ} {τ : RationalPluriForms s (n + 1) m} {ρ : RationalPluriForms (j ≫ s) n m}
    {τ' : RationalPluriForms s' (n + 1) m} {ρ' : RationalPluriForms (j ≫ s') n m}
    (h : IsPoincareResidue s j n m τ ρ) (h1 : HEq τ τ') (h2 : HEq ρ ρ') :
    IsPoincareResidue s' j n m τ' ρ' := by
  subst hs
  cases h1
  cases h2
  exact h

/-- Multiplying a form by an element `c` of the local ring along `T` multiplies its Poincaré
residue by the restriction `c̄`. -/
private theorem IsPoincareResidue.smul_stalk {k : Type} [Field k] {Y T : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsIntegral T] {j : T ⟶ Y}
    {n m : ℕ} {τ : RationalPluriForms sY (n + 1) m} {ρ : RationalPluriForms (j ≫ sY) n m}
    (h : IsPoincareResidue sY j n m τ ρ) (c : Y.presheaf.stalk (j (genericPoint T))) :
    letI := functionFieldAlgebra sY
    IsPoincareResidue sY j n m (algebraMap _ Y.functionField c • τ)
      ((j.stalkMap (genericPoint T)).hom c • ρ) := by
  letI := functionFieldAlgebra sY
  obtain ⟨t, g, x, ht, hτ, hρ⟩ := h
  exact ⟨t, c * g, x, ht, by rw [hτ, map_mul, mul_smul]; rfl, by rw [hρ, map_mul, mul_smul]; rfl⟩

/-- **The snc log generator is a log generator near its point.** Let `z₁, …, z_d` be a regular
system of parameters at a smooth point `x` of a variety `X` of dimension `d` with residue field
`k`, cutting out distinct prime divisors `L_a` which are exactly the components of `Supp B` through
`x`, all of coefficient one. Then `div(dlog z₁ ∧ ⋯ ∧ dlog z_d) + B` vanishes on an open
neighbourhood of `x`. -/
private theorem exists_open_coeff_divisorOfForm_add_eq_zero {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {d : ℕ} (hd : topologicalKrullDim X = d) {x : X}
    (z : Fin d → X.presheaf.stalk x) (hz : IsRegularSystemOfParameters z)
    (hsm : x ∈ Mori.smoothLocus sX)
    (hres : letI := stalkAlgebra sX x
      Function.Surjective (algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x))))
    (L : Fin d → Mori.PrimeDivisor X) (hL : Function.Injective L) (hLx : ∀ a, x ∈ (L a).support)
    (hLz : ∀ a, IdealSheafData.stalk (L a).idealSheaf x = Ideal.span {z a}) {B : QDivisor X}
    (hBL : ∀ E : Mori.PrimeDivisor X, x ∈ E.support → B.coeff E ≠ 0 → E ∈ Set.range L)
    (hL1 : ∀ a, B.coeff (L a) = 1) :
    letI := functionFieldAlgebra sX
    ∃ U : X.Opens, x ∈ U ∧ ∀ E : Mori.PrimeDivisor X, (E.support ∩ (U : Set X)).Nonempty →
      (Divisor.toQDivisor (divisorOfForm (show RationalPluriForms sX d ((1 : ℕ) : ℤ) from
        formPow (exteriorPower.ιMulti X.functionField d fun a =>
          (algebraMap (X.presheaf.stalk x) X.functionField (z a))⁻¹ • KaehlerDifferential.D k
            X.functionField (algebraMap (X.presheaf.stalk x) X.functionField (z a))) 1)) +
        B).coeff E = 0 := by
  classical
  letI := functionFieldAlgebra sX
  letI := stalkAlgebra sX x
  set τ : RationalPluriForms sX d ((1 : ℕ) : ℤ) := formPow (exteriorPower.ιMulti X.functionField d
    fun a => (algebraMap (X.presheaf.stalk x) X.functionField (z a))⁻¹ • KaehlerDifferential.D k
      X.functionField (algebraMap (X.presheaf.stalk x) X.functionField (z a))) 1 with hτ
  haveI : IsRegularLocalRing (X.presheaf.stalk x) :=
    MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  have hz0 : ∀ a, z a ≠ 0 := fun a => MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz a
  obtain ⟨r, ⟨b⟩⟩ := exists_basis_kaehler_stalk_of_mem_smoothLocus sX hsm
  haveI : Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] := Module.Finite.of_basis b
  have hw := span_D_eq_top_of_span_eq_maximalIdeal hres z hz.1
  have hx0 : ∀ E : Mori.PrimeDivisor X, x ∈ E.support →
      (Divisor.toQDivisor (divisorOfForm τ) + B).coeff E = 0 := by
    intro E hE
    have h1 := ordForm_formPow_dlog_eq hd 1 z hz0 hw L hL hLx hLz E hE
    rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm]
    change ((E.ordForm τ : ℤ) : ℚ) + B.coeff E = 0
    rw [hτ, h1]
    split_ifs with hEL
    · obtain ⟨a, rfl⟩ := hEL
      rw [hL1]; push_cast; ring
    · by_cases hB : B.coeff E = 0
      · rw [hB]; simp
      · exact absurd (hBL E hE hB) hEL
  set N := Divisor.toQDivisor (divisorOfForm τ) + B with hN
  set S : Finset (Mori.PrimeDivisor X) := N.support.filter fun E => x ∉ E.support with hS
  have hSc : IsClosed (⋃ E ∈ S, (E.support : Set X)) :=
    isClosed_biUnion_finset fun E _ => by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  refine ⟨⟨(⋃ E ∈ S, (E.support : Set X))ᶜ, hSc.isOpen_compl⟩, ?_, ?_⟩
  · change x ∉ ⋃ E ∈ S, (E.support : Set X)
    simp only [Set.mem_iUnion, not_exists]
    intro E hE hxE
    exact (Finset.mem_filter.1 hE).2 hxE
  · intro E ⟨y, hyE, hyU⟩
    by_contra hne
    by_cases hxE : x ∈ E.support
    · exact hne (hx0 E hxE)
    · apply hyU
      refine Set.mem_biUnion (x := E) ?_ hyE
      exact Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 hne, hxE⟩

/-- On a proper integral scheme over an algebraically closed field `k`, a rational function without
poles is a constant. -/
private theorem exists_eq_algebraMap_of_forall_zero_le_ord {k : Type} [Field k] [IsAlgClosed k]
    {C : Scheme.{0}} (sC : C ⟶ Spec (.of k)) [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    [IsProper sC] (f : C.functionField)
    (h : ∀ Γ : Mori.PrimeDivisor C, 0 ≤ C.ord f Γ.genericPoint) :
    letI := functionFieldAlgebra sC
    ∃ c : k, f = algebraMap k C.functionField c := by
  letI := functionFieldAlgebra sC
  haveI : Nonempty (⊤ : C.Opens) := ⟨⟨genericPoint C, trivial⟩⟩
  obtain ⟨s, hs⟩ := MMP.Threefold.Bridges.exists_germToFunctionField_eq_of_forall_zero_le_ord
    (X := C) ⊤ f fun Γ _ => h Γ
  letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appTop).hom.toAlgebra
  haveI : LocallyOfFiniteType sC := inferInstance
  have hfin : Module.Finite k Γ(C, ⊤) := by
    have := AlgebraicGeometry.finite_appTop_of_universallyClosed (f := sC)
    have h2 : ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appTop).hom.Finite :=
      RingHom.Finite.comp this (RingHom.Finite.of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
    exact h2
  haveI : Algebra.IsIntegral k Γ(C, ⊤) := Algebra.IsIntegral.of_finite k _
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
    (K := Γ(C, ⊤))).2 s
  refine ⟨c, ?_⟩
  rw [← hs, ← hc]
  rfl

/-- A uniformizer: every prime divisor carries a rational function of order one. -/
private theorem exists_ord_eq_one {C : Scheme.{0}} [IsIntegral C] [IsLocallyNoetherian C]
    [IsNormal C] (q : Mori.PrimeDivisor C) :
    ∃ π : C.functionField, π ≠ 0 ∧ C.ord π q.genericPoint = 1 := by
  haveI := q.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible q.localRing
  have h0 : algebraMap (C.presheaf.stalk q.genericPoint) C.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  exact ⟨_, h0, (Scheme.ord_eq_iff q.coheight_genericPoint h0).mpr (Ring.ordFrac_irreducible hϖ)⟩

/-- **A generator of a rational function field is a uniformizer at its zeros.** If `k(C)` is
generated by `w` over `k`, then `w` vanishes to order exactly one at each of its zeros. -/
private theorem ord_eq_one_of_adjoin_simple_eq_top {k : Type} [Field k] {C : Scheme.{0}}
    (sC : C ⟶ Spec (.of k)) [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (q : Mori.PrimeDivisor C) {w : C.functionField} (hw : w ≠ 0)
    (hgen : letI := functionFieldAlgebra sC
      IntermediateField.adjoin k ({w} : Set C.functionField) = ⊤)
    (hq : 0 < C.ord w q.genericPoint) : C.ord w q.genericPoint = 1 := by
  classical
  letI := functionFieldAlgebra sC
  letI := stalkAlgebra sC q.genericPoint
  haveI := isScalarTower_stalk_functionField sC q.genericPoint
  set v := q.divisorialValuation with hv
  set d := C.ord w q.genericPoint with hd
  have hvw : v w = WithZero.exp (-d) := q.divisorialValuation_eq_exp_neg_ord hw
  obtain ⟨w', hw'⟩ := exists_algebraMap_eq_of_zero_le_ord q rfl hw hq.le
  have hle : ∀ a : C.presheaf.stalk q.genericPoint, v (algebraMap _ C.functionField a) ≤ 1 :=
    fun a => (q.divisorialValuation_le_one_iff _).2 ⟨a, rfl⟩
  have hc1 : ∀ c : k, c ≠ 0 → v (algebraMap k C.functionField c) = 1 := by
    intro c hc
    have h1 : v (algebraMap k C.functionField c) ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply k (C.presheaf.stalk q.genericPoint)]; exact hle _
    have h2 : v (algebraMap k C.functionField c⁻¹) ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply k (C.presheaf.stalk q.genericPoint)]; exact hle _
    have h3 : v (algebraMap k C.functionField c) * v (algebraMap k C.functionField c⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
    refine le_antisymm h1 ?_
    by_contra hlt
    push Not at hlt
    have h4 : v (algebraMap k C.functionField c) * v (algebraMap k C.functionField c⁻¹) ≤
        v (algebraMap k C.functionField c) * 1 := mul_le_mul' le_rfl h2
    rw [h3, mul_one] at h4
    exact absurd (h4.trans_lt hlt) (lt_irrefl _)
  -- polynomials in `w`
  have hpoly : ∀ r : Polynomial k, v (Polynomial.aeval w r) ≤ 1 := by
    intro r
    rw [← hw', Polynomial.aeval_algebraMap_apply]
    exact hle _
  have hpoly0 : ∀ r : Polynomial k, r.coeff 0 ≠ 0 → v (Polynomial.aeval w r) = 1 := by
    intro r hr
    have hsplit : Polynomial.aeval w r =
        Polynomial.aeval w (Polynomial.C (r.coeff 0)) + w * Polynomial.aeval w r.divX := by
      conv_lhs => rw [← Polynomial.X_mul_divX_add r]
      rw [map_add, map_mul, Polynomial.aeval_X]; ring
    have hlt : v (w * Polynomial.aeval w r.divX) < v (Polynomial.aeval w (Polynomial.C (r.coeff 0))) := by
      rw [Polynomial.aeval_C, hc1 _ hr, map_mul, hvw]
      calc WithZero.exp (-d) * v (Polynomial.aeval w r.divX) ≤ WithZero.exp (-d) * 1 := by
            gcongr; exact hpoly _
        _ < 1 := by rw [mul_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    rw [hsplit, Valuation.map_add_eq_of_lt_left _ hlt, Polynomial.aeval_C, hc1 _ hr]
  have hpolyv : ∀ r : Polynomial k, r ≠ 0 → ∃ n : ℕ,
      v (Polynomial.aeval w r) = WithZero.exp (-(d * n)) := by
    intro r hr
    obtain ⟨r1, hr1, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hr 0
    set n := Polynomial.rootMultiplicity 0 r with hn
    refine ⟨n, ?_⟩
    have hc : r1.coeff 0 ≠ 0 := by
      intro h0
      apply hndvd
      rw [map_zero, sub_zero]
      exact Polynomial.X_dvd_iff.2 h0
    have e1 : Polynomial.aeval w r = w ^ n * Polynomial.aeval w r1 := by
      conv_lhs => rw [hr1]
      rw [map_mul, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_zero, sub_zero]
    rw [e1, map_mul, map_pow, hvw, hpoly0 r1 hc, mul_one, ← WithZero.exp_nsmul]
    congr 1
    rw [nsmul_eq_mul]
    ring
  -- every order is a multiple of `d`
  obtain ⟨π, hπ0, hπ1⟩ := exists_ord_eq_one q
  have hmem : π ∈ IntermediateField.adjoin k ({w} : Set C.functionField) := by
    rw [hgen]; trivial
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff k π).1 hmem
  have hs0 : Polynomial.aeval w s ≠ 0 := by
    intro h0; rw [h0, div_zero] at hrs; exact hπ0 hrs
  have hr0 : Polynomial.aeval w r ≠ 0 := by
    intro h0; rw [h0, zero_div] at hrs; exact hπ0 hrs
  obtain ⟨nr, hnr⟩ := hpolyv r (fun h => hr0 (by rw [h, map_zero]))
  obtain ⟨ns, hns⟩ := hpolyv s (fun h => hs0 (by rw [h, map_zero]))
  have hvπ : v π = WithZero.exp (-1) := by
    rw [q.divisorialValuation_eq_exp_neg_ord hπ0, hπ1]
  rw [hrs, map_div₀, hnr, hns, ← WithZero.exp_sub, WithZero.exp_inj] at hvπ
  have : d * ((nr : ℤ) - ns) = 1 := by linarith
  have hd1 := Int.eq_one_or_neg_one_of_mul_eq_one this
  omega

/-- An element of order one along a prime divisor generates the maximal ideal of its local ring. -/
private theorem maximalIdeal_eq_span_of_ord_eq_one {C : Scheme.{0}} [IsIntegral C]
    [IsLocallyNoetherian C] [IsNormal C] (q : Mori.PrimeDivisor C)
    {w' : C.presheaf.stalk q.genericPoint} (hw0 : w' ≠ 0)
    (hw' : C.ord (algebraMap _ C.functionField w') q.genericPoint = 1) :
    IsLocalRing.maximalIdeal (C.presheaf.stalk q.genericPoint) = Ideal.span {w'} := by
  have hwa : algebraMap _ C.functionField w' ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hw0
  apply le_antisymm
  · intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact zero_mem _
    have h1 := (one_le_ord_iff_mem_maximalIdeal q rfl hx0).2 hx
    have hxa : algebraMap _ C.functionField x ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hx0
    have hv : q.divisorialValuation (algebraMap _ C.functionField x /
        algebraMap _ C.functionField w') ≤ 1 := by
      rw [map_div₀, q.divisorialValuation_eq_exp_neg_ord hxa,
        q.divisorialValuation_eq_exp_neg_ord hwa, hw', ← WithZero.exp_sub, ← WithZero.exp_zero,
        WithZero.exp_le_exp]
      omega
    obtain ⟨y, hy⟩ := (q.divisorialValuation_le_one_iff _).1 hv
    rw [Ideal.mem_span_singleton']
    refine ⟨y, IsFractionRing.injective _ C.functionField ?_⟩
    rw [map_mul]
    change algebraMap q.localRing C.functionField y * _ = _
    rw [hy, div_mul_cancel₀ _ hwa]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (one_le_ord_iff_mem_maximalIdeal q rfl hw0).1 (by rw [hw'])

/-- **The point step along a rational floor curve.** Let `(C, B_C)` be a projective dlt curve whose
function field is generated by `w`, with `div(dlog w) + B_C = 0`. Then there is an adjunction step
`T_q ⟶ C` onto a point `q`, at which the residue of `(dlog w)^{⊗m}` is `1`. -/
private theorem exists_isAdjunctionStep_residue_dlog_of_curve {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {C : Scheme.{0}} {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C]
    [IsNormal C] (hC : IsNormalVariety k sC) [IsProper sC] (hd : topologicalKrullDim C = (1 : ℕ))
    {BC : QDivisor C} (hdlt : MMP.Intersection.IsDltPair sC BC) (w : C.functionField)
    (hw : w ≠ 0)
    (hgen : letI := functionFieldAlgebra sC
      IntermediateField.adjoin k ({w} : Set C.functionField) = ⊤)
    (hψ : letI := functionFieldAlgebra sC
      ∀ Γ : Mori.PrimeDivisor C, (Γ.ordForm (show RationalPluriForms sC 1 ((1 : ℕ) : ℤ) from
        formPow (exteriorPower.ιMulti C.functionField 1 ![w⁻¹ • KaehlerDifferential.D k _ w]) 1) : ℚ)
        + BC.coeff Γ = 0) :
    letI := functionFieldAlgebra sC
    ∃ (Tq : Scheme.{0}) (ιq : Tq ⟶ C) (Bq : QDivisor Tq) (_ : IsAdjunctionStep sC BC ιq Bq)
      (_ : IsIntegral Tq), topologicalKrullDim Tq = (0 : ℕ) ∧
      ∀ m : ℕ, letI := functionFieldAlgebra (ιq ≫ sC)
        IsPoincareResidue sC ιq 0 m
          (formPow (exteriorPower.ιMulti C.functionField 1 ![w⁻¹ • KaehlerDifferential.D k _ w]) m)
          (formPow (exteriorPower.ιMulti Tq.functionField 0 ![]) m) := by
  classical
  letI := functionFieldAlgebra sC
  haveI : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  have htr := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sC) hd
  -- `w` is not a constant
  have hnc : ∀ c : k, w ≠ algebraMap k C.functionField c := by
    intro c hc
    have hbot : IntermediateField.adjoin k ({w} : Set C.functionField) = ⊥ :=
      IntermediateField.adjoin_simple_eq_bot_iff.2 (by rw [hc]; exact IntermediateField.algebraMap_mem _ c)
    rw [hgen] at hbot
    haveI : Algebra.IsAlgebraic k C.functionField := by
      refine ⟨fun x => ?_⟩
      have hx : x ∈ (⊥ : IntermediateField k C.functionField) := by rw [← hbot]; trivial
      obtain ⟨c', rfl⟩ := IntermediateField.mem_bot.1 hx
      exact isAlgebraic_algebraMap c'
    rw [trdeg_eq_zero (R := k) (A := C.functionField)] at htr
    simp at htr
  -- a zero `q` of `w`
  obtain ⟨q, hq⟩ : ∃ q : Mori.PrimeDivisor C, 0 < C.ord w q.genericPoint := by
    by_contra hcon
    push Not at hcon
    have hinv : ∀ Γ : Mori.PrimeDivisor C, 0 ≤ C.ord w⁻¹ Γ.genericPoint := by
      intro Γ
      have e1 := Γ.divisorialValuation_eq_exp_neg_ord (inv_ne_zero hw)
      have e2 := Γ.divisorialValuation_eq_exp_neg_ord hw
      rw [map_inv₀, e2, ← WithZero.exp_neg, WithZero.exp_inj] at e1
      linarith [hcon Γ]
    obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_forall_zero_le_ord sC w⁻¹ hinv
    exact hnc c⁻¹ (by rw [map_inv₀, ← hc, inv_inv])
  have hq1 := ord_eq_one_of_adjoin_simple_eq_top sC q hw hgen hq
  -- `q` has coefficient one
  have hqc : BC.coeff q = 1 := by
    have hcl : IsClosed ({q.genericPoint} : Set C) := by
      haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
      exact isClosed_singleton_of_le_coheight (d := 1) hd.le (by rw [q.coheight_genericPoint]; rfl)
    obtain ⟨w', hw'⟩ := exists_algebraMap_eq_of_zero_le_ord q rfl hw hq.le
    have hw'0 : w' ≠ 0 := by rintro rfl; rw [map_zero] at hw'; exact hw hw'.symm
    have hm := maximalIdeal_eq_span_of_ord_eq_one q hw'0 (by rw [hw']; exact hq1)
    have hspan : Ideal.span (Set.range ![w']) =
        IsLocalRing.maximalIdeal (C.presheaf.stalk q.genericPoint) := by
      rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty, hm]
    letI := stalkAlgebra sC q.genericPoint
    have hres : Function.Surjective (algebraMap k
        (IsLocalRing.ResidueField (C.presheaf.stalk q.genericPoint))) := by
      intro y
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨c, hc⟩ := exists_sub_mem_maximalIdeal_of_isClosed sC q.genericPoint hcl r
      refine ⟨c, ?_⟩
      have h0 := (IsLocalRing.residue_eq_zero_iff _).2 hc
      rw [map_sub, sub_eq_zero] at h0
      rw [IsScalarTower.algebraMap_apply k (C.presheaf.stalk q.genericPoint)
        (IsLocalRing.ResidueField (C.presheaf.stalk q.genericPoint)),
        IsLocalRing.ResidueField.algebraMap_eq, ← h0]
    obtain ⟨r, ⟨b⟩⟩ := exists_basis_kaehler_stalk_of_mem_smoothLocus sC
      (MMP.Threefold.Mori.CanonUniq.genericPoint_mem_smoothLocus hC.1 q)
    haveI : Module.Finite (C.presheaf.stalk q.genericPoint) Ω[C.presheaf.stalk q.genericPoint⁄k] :=
      Module.Finite.of_basis b
    have hspD := span_D_eq_top_of_span_eq_maximalIdeal hres ![w'] hspan
    have hLz : IdealSheafData.stalk q.idealSheaf q.genericPoint = Ideal.span {(![w'] : Fin 1 → _) 0} := by
      rw [MMP.Resolution.Aux.stalk_idealSheaf_genericPoint]
      exact hm
    have hmem : q.genericPoint ∈ q.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    have h1 := ordForm_formPow_dlog_eq (sX := sC) hd 1 ![w'] (fun a => by fin_cases a; exact hw'0)
      hspD ![q] (fun a b _ => Subsingleton.elim a b) (fun a => by fin_cases a; exact hmem)
      (fun a => by fin_cases a; exact hLz) q hmem
    have h2 := hψ q
    have e : (fun a : Fin 1 => (algebraMap (C.presheaf.stalk q.genericPoint) C.functionField
        ((![w'] : Fin 1 → _) a))⁻¹ • KaehlerDifferential.D k C.functionField
          (algebraMap (C.presheaf.stalk q.genericPoint) C.functionField ((![w'] : Fin 1 → _) a))) =
        ![w⁻¹ • KaehlerDifferential.D k _ w] := by
      funext a; fin_cases a; simp [hw']
    rw [e] at h1
    rw [h1, if_pos ⟨0, rfl⟩] at h2
    push_cast at h2
    linarith
  -- the adjunction step onto `q`
  obtain ⟨Tq, ιq, Bq, -, hιq, hTq, hrq, hdq⟩ :=
    exists_isAdjunctionStep_of_isDltPair hC hdlt (e := 0) (by simpa using hd) q (by rw [hqc])
  rw [Category.id_comp] at hιq
  refine ⟨Tq, ιq, Bq, hιq, hTq, by exact_mod_cast hdq, fun m => ?_⟩
  have hP := map_genericPoint_eq_of_range_eq ιq q hrq
  obtain ⟨t, ht⟩ := exists_algebraMap_eq_of_zero_le_ord q hP hw (by rw [hP]; exact hq.le)
  letI := functionFieldAlgebra (ιq ≫ sC)
  set f0 : Fin 0 → C.presheaf.stalk (ιq (genericPoint Tq)) := Fin.elim0 with hf0
  have hres := isPoincareResidue_formPow_dlog sC ιq m t (n := 0) f0 (fun i => i.elim0)
    (by rw [ht, hP]; exact hq1)
  have e1 : (formPow (exteriorPower.ιMulti C.functionField 1 ![w⁻¹ • KaehlerDifferential.D k _ w]) m :
      RationalPluriForms sC (0 + 1) m) = formPow (exteriorPower.ιMulti C.functionField (0 + 1)
        (Fin.cons ((algebraMap _ C.functionField t)⁻¹ •
            KaehlerDifferential.D k C.functionField (algebraMap _ _ t))
          fun i => (algebraMap _ C.functionField (f0 i))⁻¹ •
            KaehlerDifferential.D k C.functionField (algebraMap _ C.functionField (f0 i)))) m := by
    congr 2
    funext a; fin_cases a; simp [ht]
  have e2 : (formPow (exteriorPower.ιMulti Tq.functionField 0 ![]) m :
      RationalPluriForms (ιq ≫ sC) 0 m) = formPow (exteriorPower.ιMulti Tq.functionField 0
        fun i => ((ιq.stalkMap (genericPoint Tq)).hom (f0 i))⁻¹ •
          KaehlerDifferential.D k Tq.functionField ((ιq.stalkMap (genericPoint Tq)).hom
            (f0 i))) m := by
    congr 2
    funext a; exact a.elim0
  rw [e1, e2]
  exact hres

/-- The stalk maps of a morphism of `k`-schemes are compatible with the constants. -/
private theorem stalkMap_algebraMap_const {k : Type} [Field k] {X Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (f : X ⟶ Y) (x : X) (c : k) :
    letI := stalkAlgebra sY (f x)
    letI := stalkAlgebra (f ≫ sY) x
    (f.stalkMap x).hom (algebraMap k _ c) = algebraMap k _ c := by
  change (f.stalkMap x).hom ((((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫
    Y.presheaf.germ ⊤ (f x) (TopologicalSpace.Opens.mem_top _)).hom) c) =
    (((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ sY).appTop ≫
      X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top _)).hom c)
  rw [← CommRingCat.comp_apply, Category.assoc, Category.assoc, Scheme.Hom.germ_stalkMap,
    Scheme.Hom.comp_appTop, Category.assoc]
  rfl

/-- `(dlog x₁ ∧ ⋯ ∧ dlog x_d)^{⊗m} = (x₁⋯x_d)^{-m} (dx₁ ∧ ⋯ ∧ dx_d)^{⊗m}`. -/
private theorem formPow_ιMulti_dlog_eq_smul {k K : Type*} [Field k] [Field K] [Algebra k K]
    {d : ℕ} (x : Fin d → K) (m : ℕ) :
    formPow (exteriorPower.ιMulti K d fun i => (x i)⁻¹ • KaehlerDifferential.D k K (x i)) m =
      ((∏ i, x i)⁻¹) ^ m • formPow (exteriorPower.ιMulti K d fun i =>
        KaehlerDifferential.D k K (x i)) m := by
  rw [show (fun i => (x i)⁻¹ • KaehlerDifferential.D k K (x i)) =
      fun i => (fun i => (x i)⁻¹) i • (fun i => KaehlerDifferential.D k K (x i)) i from rfl,
    AlternatingMap.map_smul_univ, formPow_smul', Finset.prod_inv_distrib]

/-- **The toric step along a floor curve of a surface.** Let `(T, B_T)` be a projective dlt
surface whose function field is generated by `u, w`, with `θ = dlog u ∧ dlog w` satisfying
`div θ + B_T = 0`. Then there are an adjunction step `T_C ⟶ T` onto a component of `⌊B_T⌋` and
`w̄ ∈ k(T_C)` generating `k(T_C)`, with `Res θ^{⊗m} = (dlog w̄)^{⊗m}` for every `m` and
`div(dlog w̄) + B_C = 0`. -/
private theorem exists_isAdjunctionStep_residue_dlog_of_surface {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)} [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] (hT : IsNormalVariety k sT) [IsProper sT]
    (hd : topologicalKrullDim T = (2 : ℕ)) {BT : QDivisor T}
    (hdlt : MMP.Intersection.IsDltPair sT BT) (u w : T.functionField) (hu : u ≠ 0) (hw : w ≠ 0)
    (hgen : letI := functionFieldAlgebra sT
      IntermediateField.adjoin k ({u, w} : Set T.functionField) = ⊤)
    (hθ : letI := functionFieldAlgebra sT
      ∀ Γ : Mori.PrimeDivisor T, (Γ.ordForm (show RationalPluriForms sT 2 ((1 : ℕ) : ℤ) from
        formPow (exteriorPower.ιMulti T.functionField 2 ![u⁻¹ • KaehlerDifferential.D k _ u,
          w⁻¹ • KaehlerDifferential.D k _ w]) 1) : ℚ) + BT.coeff Γ = 0) :
    letI := functionFieldAlgebra sT
    ∃ (TC : Scheme.{0}) (ιC : TC ⟶ T) (BC : QDivisor TC) (_ : IsAdjunctionStep sT BT ιC BC)
      (_ : IsIntegral TC) (_ : IsLocallyNoetherian TC) (_ : IsNormal TC),
      MMP.Intersection.IsDltPair (ιC ≫ sT) BC ∧ topologicalKrullDim TC = (1 : ℕ) ∧
      ∃ wC : TC.functionField, wC ≠ 0 ∧
        (letI := functionFieldAlgebra (ιC ≫ sT);
          IntermediateField.adjoin k ({wC} : Set TC.functionField) = ⊤) ∧
        (∀ m : ℕ, letI := functionFieldAlgebra (ιC ≫ sT);
          IsPoincareResidue sT ιC 1 m
            (formPow (exteriorPower.ιMulti T.functionField 2 ![u⁻¹ • KaehlerDifferential.D k _ u,
              w⁻¹ • KaehlerDifferential.D k _ w]) m)
            (formPow (exteriorPower.ιMulti TC.functionField 1
              ![wC⁻¹ • KaehlerDifferential.D k _ wC]) m)) ∧
        (letI := functionFieldAlgebra (ιC ≫ sT);
          ∀ Γ : Mori.PrimeDivisor TC, (Γ.ordForm (show RationalPluriForms (ιC ≫ sT) 1
            ((1 : ℕ) : ℤ) from formPow (exteriorPower.ιMulti TC.functionField 1
              ![wC⁻¹ • KaehlerDifferential.D k _ wC]) 1) : ℚ) + BC.coeff Γ = 0) := by
  classical
  letI := functionFieldAlgebra sT
  haveI : LocallyOfFiniteType sT := hT.1.toLocallyOfFiniteType
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  obtain ⟨C, hCθ, hC1⟩ := exists_primeDivisor_ordForm_dlog_eq_neg_one hT hd hdlt u w hu hw hgen hθ
  set θ1 : RationalPluriForms sT 2 ((1 : ℕ) : ℤ) := formPow (exteriorPower.ιMulti T.functionField 2
    ![u⁻¹ • KaehlerDifferential.D k _ u, w⁻¹ • KaehlerDifferential.D k _ w]) 1 with hθ1
  have hθ0 : θ1 ≠ 0 := by
    intro h0
    rw [h0, Mori.PrimeDivisor.ordForm_zero] at hCθ
    exact absurd hCθ (by decide)
  -- the unimodular change of coordinates at `C`
  set v := C.divisorialValuation with hv
  set a1 := T.ord u C.genericPoint with ha1
  set a2 := T.ord w C.genericPoint with ha2
  obtain ⟨M, hMdet, hMv⟩ := exists_det_eq_one_mulVec_eq a1 a2
  set zU : Fin 2 → (T.functionField)ˣ := ![Units.mk0 u hu, Units.mk0 w hw] with hzU
  set sU : Fin 2 → (T.functionField)ˣ := fun a => ∏ b, zU b ^ M a b with hsU
  have hzv : ∀ i, v (zU i : T.functionField) = WithZero.exp (-(![a1, a2] i)) := by
    intro i; fin_cases i
    · exact C.divisorialValuation_eq_exp_neg_ord hu
    · exact C.divisorialValuation_eq_exp_neg_ord hw
  have hsv : ∀ a, v (sU a : T.functionField) =
      WithZero.exp (-((![(Int.gcd a1 a2 : ℤ), 0] : Fin 2 → ℤ) a)) := by
    intro a
    rw [hsU, valuation_prod_zpow_eq v zU _ hzv, ← hMv]
    rfl
  have hdl : exteriorPower.ιMulti T.functionField 2
      ![u⁻¹ • KaehlerDifferential.D k _ u, w⁻¹ • KaehlerDifferential.D k _ w] =
      exteriorPower.ιMulti T.functionField 2
        ![(sU 0 : T.functionField)⁻¹ • KaehlerDifferential.D k _ (sU 0 : T.functionField),
          (sU 1 : T.functionField)⁻¹ • KaehlerDifferential.D k _ (sU 1 : T.functionField)] := by
    have h1 := ιMulti_dlogHom_monomial k T.functionField zU M
    rw [hMdet, Int.cast_one, one_smul] at h1
    have e1 : (![u⁻¹ • KaehlerDifferential.D k _ u, w⁻¹ • KaehlerDifferential.D k _ w] :
        Fin 2 → Ω[T.functionField⁄k]) =
        fun b => Multiplicative.toAdd (dlogHom k T.functionField (zU b)) := by
      funext b; fin_cases b <;> rfl
    have e2 : (![(sU 0 : T.functionField)⁻¹ • KaehlerDifferential.D k _ (sU 0 : T.functionField),
          (sU 1 : T.functionField)⁻¹ • KaehlerDifferential.D k _ (sU 1 : T.functionField)] :
        Fin 2 → Ω[T.functionField⁄k]) =
        fun a => Multiplicative.toAdd (dlogHom k T.functionField (∏ b, zU b ^ M a b)) := by
      funext a; fin_cases a <;> rfl
    rw [e1, e2, h1]
  -- `gcd(a₁, a₂) > 0`: otherwise `θ` would be regular along `C`
  have hg : 0 < Int.gcd a1 a2 := by
    by_contra h0
    have h00 : Int.gcd a1 a2 = 0 := by omega
    obtain ⟨h1, h2⟩ := Int.gcd_eq_zero_iff.1 h00
    obtain ⟨u', hu'⟩ := exists_algebraMap_eq_of_zero_le_ord C rfl hu (by rw [← ha1, h1])
    obtain ⟨w', hw'⟩ := exists_algebraMap_eq_of_zero_le_ord C rfl hw (by rw [← ha2, h2])
    set τ0 : RationalPluriForms sT 2 ((1 : ℕ) : ℤ) := formPow (exteriorPower.ιMulti
      T.functionField 2 ![KaehlerDifferential.D k T.functionField u,
        KaehlerDifferential.D k T.functionField w]) 1 with hτ0def
    have hsm : θ1 = (u * w)⁻¹ • τ0 := by
      have h := formPow_ιMulti_dlog_eq_smul (k := k) (d := 2) ![u, w] 1
      have e3 : (fun i => (![u, w] i)⁻¹ • KaehlerDifferential.D k T.functionField (![u, w] i)) =
          ![u⁻¹ • KaehlerDifferential.D k _ u, w⁻¹ • KaehlerDifferential.D k _ w] := by
        funext i; fin_cases i <;> rfl
      have e4 : (fun i => KaehlerDifferential.D k T.functionField (![u, w] i)) =
          ![KaehlerDifferential.D k T.functionField u, KaehlerDifferential.D k T.functionField w] := by
        funext i; fin_cases i <;> rfl
      rw [e3, e4, Fin.prod_univ_two, pow_one] at h
      exact h
    have hτ0 : τ0 ≠ 0 := by
      intro h0; apply hθ0; rw [hsm, h0, smul_zero]
    have hc0 : (u * w)⁻¹ ≠ 0 := by simp [hu, hw]
    have hreg := zero_le_ordForm_formPow_ιMulti_D (sX := sT) C hd 1 ![u', w']
    have e5 : (fun i => KaehlerDifferential.D k T.functionField (algebraMap C.localRing
        T.functionField ((![u', w'] : Fin 2 → C.localRing) i))) =
        ![KaehlerDifferential.D k T.functionField u, KaehlerDifferential.D k T.functionField w] := by
      funext i; fin_cases i
      · simp [hu']
      · simp [hw']
    have hreg' : 0 ≤ C.ordForm τ0 := by
      rw [hτ0def, ← e5]; exact hreg
    have hvc : T.ord (u * w)⁻¹ C.genericPoint = 0 := by
      have e6 := C.divisorialValuation_eq_exp_neg_ord hc0
      rw [map_inv₀, map_mul, C.divisorialValuation_eq_exp_neg_ord hu,
        C.divisorialValuation_eq_exp_neg_ord hw, ← ha1, ← ha2, h1, h2] at e6
      simp only [neg_zero, WithZero.exp_zero, mul_one, inv_one] at e6
      rw [← WithZero.exp_zero, WithZero.exp_inj] at e6
      omega
    have hord := Mori.PrimeDivisor.ordForm_smul_of_topologicalKrullDim_eq C hd hc0 hτ0
    have : 0 ≤ C.ordForm θ1 := by
      rw [hsm, hord, hvc, zero_add]; exact hreg'
    rw [hCθ] at this
    exact absurd this (by decide)
  -- the new coordinates in `𝒪_{T,C}`
  have hu0 : (sU 0 : T.functionField) ≠ 0 := (sU 0).ne_zero
  have hw0 : (sU 1 : T.functionField) ≠ 0 := (sU 1).ne_zero
  have hou0 : T.ord (sU 0 : T.functionField) C.genericPoint = Int.gcd a1 a2 := by
    have e := C.divisorialValuation_eq_exp_neg_ord hu0
    rw [hsv, WithZero.exp_inj] at e
    simpa using e.symm
  have how0 : T.ord (sU 1 : T.functionField) C.genericPoint = 0 := by
    have e := C.divisorialValuation_eq_exp_neg_ord hw0
    rw [hsv, WithZero.exp_inj] at e
    simpa using e.symm
  obtain ⟨u0, hu0'⟩ := exists_algebraMap_eq_of_zero_le_ord C rfl hu0 (by rw [hou0]; positivity)
  obtain ⟨w0, hw0'⟩ := exists_algebraMap_eq_of_zero_le_ord C rfl hw0 (by rw [how0])
  have hu0ne : u0 ≠ 0 := by rintro rfl; rw [map_zero] at hu0'; exact hu0 hu0'.symm
  have hw0ne : w0 ≠ 0 := by rintro rfl; rw [map_zero] at hw0'; exact hw0 hw0'.symm
  have hu0m : u0 ∈ IsLocalRing.maximalIdeal C.localRing :=
    (one_le_ord_iff_mem_maximalIdeal C rfl hu0ne).1 (by rw [hu0', hou0]; exact_mod_cast hg)
  have hw0u : IsUnit w0 := by
    by_contra hn
    have := (one_le_ord_iff_mem_maximalIdeal C rfl hw0ne).2 ((IsLocalRing.mem_maximalIdeal _).2 hn)
    rw [hw0', how0] at this
    omega
  have hgen0 : IntermediateField.adjoin k ({algebraMap C.localRing T.functionField u0,
      algebraMap C.localRing T.functionField w0} : Set T.functionField) = ⊤ := by
    rw [hu0', hw0', eq_top_iff, ← hgen, IntermediateField.adjoin_le_iff]
    have hdet : IsUnit M.det := by rw [hMdet]; exact isUnit_one
    set L := IntermediateField.adjoin k
      ({(sU 0 : T.functionField), (sU 1 : T.functionField)} : Set T.functionField) with hL
    have hsL : ∀ a, (sU a : T.functionField) ∈ L := by
      intro a
      fin_cases a
      · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
      · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)
    have hmem : ∀ b, (zU b : T.functionField) ∈ L := by
      intro b
      have h := prod_zpow_eq_prod_monomial_zpow zU M hdet (Pi.single b (1 : ℤ))
      have h1 : (∏ c, zU c ^ (Pi.single b (1 : ℤ) : Fin 2 → ℤ) c) = zU b := by
        rw [Fintype.prod_eq_single b (fun c hc => by rw [Pi.single_eq_of_ne hc, zpow_zero]),
          Pi.single_eq_same, zpow_one]
      rw [h1] at h
      rw [h, Units.coe_prod]
      apply IntermediateField.prod_mem
      intro a _
      rw [Units.val_zpow_eq_zpow_val]
      exact Subfield.zpow_mem (s := L.toSubfield) (hsL a) _
    rintro x (rfl | rfl)
    · exact hmem 0
    · exact hmem 1
  letI := stalkAlgebra sT C.genericPoint
  haveI := isScalarTower_stalk_functionField sT C.genericPoint
  have hdw : (formPow (dlogWedge (k := k) (K := T.functionField) w0
      (algebraMap C.localRing T.functionField u0)) 1 : RationalPluriForms sT 2 ((1 : ℕ) : ℤ)) =
      θ1 := by
    unfold dlogWedge
    rw [hu0', hw0', hθ1, hdl]
  have hnc : ∀ c : k, w0 - algebraMap k C.localRing c ∉ IsLocalRing.maximalIdeal C.localRing := by
    intro c hc
    have h := zero_le_ordForm_formPow_dlogWedge (sX := sT) C hd 1 w0 hw0u c hc
      (algebraMap _ _ u0) (by rw [hu0']; exact hu0)
    have h' : 0 ≤ C.ordForm θ1 := by rw [← hdw]; exact h
    rw [hCθ] at h'
    exact absurd h' (by decide)
  obtain ⟨hirr, hpoly⟩ := irreducible_and_residue_of_ordForm_dlogWedge_neg (sX := sT) C hd 1 u0 w0
    hu0m hu0ne hw0u hgen0 (by
      have h3 : C.ordForm θ1 < 0 := by rw [hCθ]; decide
      rw [← hdw] at h3
      exact h3)
  have hu0a : algebraMap C.localRing T.functionField u0 ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hu0ne
  haveI := C.isDiscreteValuationRing_localRing
  have hord1 : T.ord (algebraMap C.localRing T.functionField u0) C.genericPoint = 1 :=
    (Scheme.ord_eq_iff C.coheight_genericPoint hu0a).mpr (Ring.ordFrac_irreducible hirr)
  -- the adjunction step onto `C`
  obtain ⟨TC, ιC, BC, hpairT, hιC, hTC, hrC, hdC⟩ :=
    exists_isAdjunctionStep_of_isDltPair hT hdlt (e := 1) (by simpa using hd) C (by rw [hC1])
  have hιC0 := hιC
  rw [Category.id_comp] at hιC
  have hPC := map_genericPoint_eq_of_range_eq ιC C hrC
  haveI : LocallyOfFiniteType (ιC ≫ sT) := hιC.1.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian TC := LocallyOfFiniteType.isLocallyNoetherian (ιC ≫ sT)
  haveI : IsNormal TC := hιC.1.2
  have hdltC := isDltPair_of_isAdjunctionStep hdlt hpairT hιC0 C (by rw [hC1]) hrC
  obtain ⟨-, -, -, -, hci, -⟩ := id hιC
  haveI := hci
  haveI : CompactSpace TC := QuasiCompact.compactSpace_of_compactSpace ιC
  -- transport to the stalk at the image of the generic point of `T_C`
  have key : ∀ (y : T) (hy : y = C.genericPoint), ∃ (t e : T.presheaf.stalk y),
      algebraMap _ T.functionField t = (sU 0 : T.functionField) ∧
      algebraMap _ T.functionField e = (sU 1 : T.functionField) ∧ IsUnit e ∧
      T.ord (algebraMap _ T.functionField t) y = 1 ∧
      IdealSheafData.stalk C.idealSheaf y = IsLocalRing.maximalIdeal (T.presheaf.stalk y) ∧
      (letI := stalkAlgebra sT y;
        (∀ c : k, e - algebraMap k _ c ∉ IsLocalRing.maximalIdeal (T.presheaf.stalk y)) ∧
        ∀ x : T.presheaf.stalk y, IsUnit x → ∃ p q : Polynomial k, q ≠ 0 ∧
          x * Polynomial.aeval e q - Polynomial.aeval e p ∈
            IsLocalRing.maximalIdeal (T.presheaf.stalk y)) := by
    rintro y rfl
    exact ⟨u0, w0, hu0', hw0', hw0u, hord1, MMP.Resolution.Aux.stalk_idealSheaf_genericPoint C,
      hnc, hpoly⟩
  obtain ⟨t, e, ht, he, heu, ht1, hstk, hnc', hpoly'⟩ := key _ hPC
  letI := functionFieldAlgebra (ιC ≫ sT)
  set wC := (ιC.stalkMap (genericPoint TC)).hom e with hwC
  have hres : ∀ m : ℕ, IsPoincareResidue sT ιC 1 m
      (formPow (exteriorPower.ιMulti T.functionField 2 ![u⁻¹ • KaehlerDifferential.D k _ u,
        w⁻¹ • KaehlerDifferential.D k _ w]) m)
      (formPow (exteriorPower.ιMulti TC.functionField 1
        ![wC⁻¹ • KaehlerDifferential.D k _ wC]) m) := by
    intro m
    have h := isPoincareResidue_formPow_dlog sT ιC m t ![e] (fun i => by fin_cases i; exact heu) ht1
    have e1 : (formPow (exteriorPower.ιMulti T.functionField 2
        ![u⁻¹ • KaehlerDifferential.D k _ u, w⁻¹ • KaehlerDifferential.D k _ w]) m :
        RationalPluriForms sT (1 + 1) m) = formPow (exteriorPower.ιMulti T.functionField (1 + 1)
          (Fin.cons ((algebraMap _ T.functionField t)⁻¹ •
              KaehlerDifferential.D k T.functionField (algebraMap _ _ t))
            fun i => (algebraMap _ T.functionField ((![e] : Fin 1 → _) i))⁻¹ •
              KaehlerDifferential.D k T.functionField
                (algebraMap _ T.functionField ((![e] : Fin 1 → _) i)))) m := by
      rw [hdl]
      congr 2
      funext i; fin_cases i
      · simp [ht]
      · simp [he]
    have e2 : (formPow (exteriorPower.ιMulti TC.functionField 1
        ![wC⁻¹ • KaehlerDifferential.D k _ wC]) m : RationalPluriForms (ιC ≫ sT) 1 m) =
        formPow (exteriorPower.ιMulti TC.functionField 1 fun i =>
          ((ιC.stalkMap (genericPoint TC)).hom ((![e] : Fin 1 → _) i))⁻¹ •
            KaehlerDifferential.D k TC.functionField ((ιC.stalkMap (genericPoint TC)).hom
              ((![e] : Fin 1 → _) i))) m := by
      congr 2
      funext i; fin_cases i; rfl
    rw [e1, e2]
    exact h
  -- the kernel of the restriction to `k(T_C)` is the maximal ideal
  have hker : RingHom.ker (ιC.stalkMap (genericPoint TC)).hom =
      IsLocalRing.maximalIdeal (T.presheaf.stalk (ιC (genericPoint TC))) := by
    rw [ker_stalkMap_eq_stalk_idealSheaf ιC C hrC (genericPoint TC), hstk]
  have hwC0 : wC ≠ 0 := (heu.map (ιC.stalkMap (genericPoint TC)).hom).ne_zero
  -- the restriction is a `k`-algebra map
  letI := stalkAlgebra sT (ιC (genericPoint TC))
  let φ : T.presheaf.stalk (ιC (genericPoint TC)) →ₐ[k] TC.functionField :=
    { (ιC.stalkMap (genericPoint TC)).hom with
      commutes' := fun c => stalkMap_algebraMap_const sT ιC (genericPoint TC) c }
  have hφ : ∀ a, φ a = (ιC.stalkMap (genericPoint TC)).hom a := fun _ => rfl
  -- `w̄` is transcendental
  have htr : ∀ q : Polynomial k, q ≠ 0 → Polynomial.aeval wC q ≠ 0 := by
    intro q hq hq0
    have halg : IsAlgebraic k wC := ⟨q, hq, hq0⟩
    haveI : FiniteDimensional k (IntermediateField.adjoin k ({wC} : Set TC.functionField)) :=
      IntermediateField.adjoin.finiteDimensional halg.isIntegral
    haveI : Algebra.IsAlgebraic k (IntermediateField.adjoin k ({wC} : Set TC.functionField)) :=
      Algebra.IsAlgebraic.of_finite k _
    have hbot := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic
      (IntermediateField.adjoin k ({wC} : Set TC.functionField))
    have hmem : wC ∈ (⊥ : IntermediateField k TC.functionField) := by
      rw [← hbot]; exact IntermediateField.mem_adjoin_simple_self k wC
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hmem
    apply hnc' c
    rw [← hker, RingHom.mem_ker, map_sub, ← hφ (algebraMap k _ c), AlgHom.commutes, hc]
    exact sub_self _
  have hadj : IntermediateField.adjoin k ({wC} : Set TC.functionField) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    by_cases hy0 : y = 0
    · rw [hy0]; exact zero_mem _
    obtain ⟨x, rfl⟩ := ιC.stalkMap_surjective (genericPoint TC) y
    have hxu : IsUnit x := by
      by_contra hxn
      apply hy0
      have : x ∈ RingHom.ker (ιC.stalkMap (genericPoint TC)).hom := by
        rw [hker]; exact (IsLocalRing.mem_maximalIdeal _).2 hxn
      exact this
    obtain ⟨p, q, hq, hpq⟩ := hpoly' x hxu
    have h0 : φ (x * Polynomial.aeval e q - Polynomial.aeval e p) = 0 := by
      rw [hφ, ← RingHom.mem_ker, hker]; exact hpq
    rw [map_sub, map_mul, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply,
      sub_eq_zero, hφ, hφ] at h0
    rw [IntermediateField.mem_adjoin_simple_iff]
    refine ⟨p, q, ?_⟩
    rw [eq_div_iff (htr q hq)]
    exact h0
  -- `div(dlog w̄) + B_C = 0` by the residue different
  have hz : Divisor.toQDivisor (divisorOfForm θ1) + BT = 0 := by
    ext Γ
    rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm,
      DivisorWithCoeffs.coeff_zero]
    exact hθ Γ
  have hθC : C.ordForm θ1 = -1 := hCθ
  obtain ⟨hgenC, hpb⟩ := hιC.isPullback_divisorOfForm_add_of_isPoincareResidue (n := 1)
    (by rw [hd]; norm_cast) C hrC θ1 hθ0 hθC _ (hres 1) (by rw [hz]; exact QDivisor.isQCartier_zero)
  refine ⟨TC, ιC, BC, hιC, hTC, inferInstance, inferInstance, hdltC, by exact_mod_cast hdC, wC,
    hwC0, hadj, hres, fun Γ => ?_⟩
  have h1 := coeff_eq_zero_of_isPullback_of_forall (by rw [hz]; exact QDivisor.isQCartier_zero)
    hpb ⊤ (fun E _ => by rw [hz, DivisorWithCoeffs.coeff_zero]) Γ
    ⟨Γ.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl, trivial⟩
  rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor] at h1
  exact h1

/-- Multiplying a form by a constant multiplies its Poincaré residue by the constant. -/
private theorem IsPoincareResidue.smul_const {k : Type} [Field k] {Y T : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsIntegral T] {j : T ⟶ Y}
    {n m : ℕ} {τ : RationalPluriForms sY (n + 1) m} {ρ : RationalPluriForms (j ≫ sY) n m}
    (h : IsPoincareResidue sY j n m τ ρ) (c : k) :
    IsPoincareResidue sY j n m (c • τ) (c • ρ) := by
  letI := functionFieldAlgebra sY
  letI := stalkAlgebra sY (j (genericPoint T))
  haveI := isScalarTower_stalk_functionField sY (j (genericPoint T))
  have h1 := IsPoincareResidue.smul_stalk h (algebraMap k (Y.presheaf.stalk (j (genericPoint T))) c)
  rw [← IsScalarTower.algebraMap_apply, stalkMap_algebraMap_const sY j (genericPoint T) c] at h1
  exact h1

/-- Rational pluriforms transported along an equality of structure morphisms. -/
private theorem exists_heq_rationalPluriForms {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {s s' : X ⟶ Spec (.of k)} (hs : s = s') {d : ℕ} {m : ℤ} (x : RationalPluriForms s d m) :
    ∃ y : RationalPluriForms s' d m, HEq x y :=
  ⟨cast (by rw [hs]) x, (cast_heq _ _).symm⟩

/-- The constant pluriforms of degree zero do not depend on the structure morphism beyond
equality. -/
private theorem heq_smul_formPow_ιMulti_zero {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {s s' : X ⟶ Spec (.of k)} (hs : s = s') (c : k) (m : ℕ) :
    HEq (letI := functionFieldAlgebra s;
      (c • (show RationalPluriForms s 0 m from
        formPow (exteriorPower.ιMulti X.functionField 0 ![]) m)))
      (letI := functionFieldAlgebra s';
        (c • (show RationalPluriForms s' 0 m from
          formPow (exteriorPower.ιMulti X.functionField 0 ![]) m))) := by
  subst hs; rfl

/-- **A point stratum reached through a floor divisor carrying a monomial frame.** Let `P` be a
floor divisor of a projective dlt threefold `(X, B)`, with adjunction step `T ⟶ X`, and let
`t, e₁, e₂ ∈ 𝒪_{X,P}` be a uniformizer and two units whose residues generate `k(T)`, such that
`θ = dlog ē₁ ∧ dlog ē₂` satisfies `div θ + B_T = 0`. Then there is a flag of length three from `X`
through `T` to a point `S`, along which the iterated residue of `g (dlog t ∧ dlog e₁ ∧ dlog e₂)^m`
is the constant residue `ḡ ∈ k` of `g`. -/
private theorem exists_flag_isIteratedResidueRec_of_frame {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsProper sX] {B : QDivisor X} (hdlt : MMP.Intersection.IsDltPair sX B)
    (h : MMP.Mori.IsPair sX B) (P : Mori.PrimeDivisor X) (hP1 : 1 ≤ B.coeff P)
    {T : Scheme.{0}} {ι : T ⟶ X} {BT : QDivisor T} (hι : IsAdjunctionStep (𝟙 X ≫ sX) B ι BT)
    [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    (hrange : Set.range ι.base = (P.support : Set X))
    (hdT : topologicalKrullDim T = (2 : ℕ))
    (t : X.presheaf.stalk (ι (genericPoint T))) (e : Fin 2 → X.presheaf.stalk (ι (genericPoint T)))
    (he : ∀ i, IsUnit (e i))
    (ht : (letI := functionFieldAlgebra sX;
      X.ord (algebraMap _ X.functionField t) (ι (genericPoint T))) = 1)
    (hgen : letI := functionFieldAlgebra (ι ≫ sX);
      IntermediateField.adjoin k (Set.range fun i => (ι.stalkMap (genericPoint T)).hom (e i)) = ⊤)
    (hθ : letI := functionFieldAlgebra (ι ≫ sX);
      ∀ Γ : Mori.PrimeDivisor T, (Γ.ordForm (show RationalPluriForms (ι ≫ sX) 2 ((1 : ℕ) : ℤ) from
        formPow (exteriorPower.ιMulti T.functionField 2 fun i =>
          ((ι.stalkMap (genericPoint T)).hom (e i))⁻¹ • KaehlerDifferential.D k _
            ((ι.stalkMap (genericPoint T)).hom (e i))) 1) : ℚ) + BT.coeff Γ = 0) (m : ℕ) :
    ∃ (S : Scheme.{0}) (ιS : S ⟶ X) (BS : QDivisor S) (F : StratumAdjunctionData sX B ιS BS),
      F.length = 3 ∧ topologicalKrullDim S = (0 : ℕ) ∧
      ∀ (g : X.presheaf.stalk (ι (genericPoint T))) (c : k),
        (letI := functionFieldAlgebra (ι ≫ sX);
          (ι.stalkMap (genericPoint T)).hom g = algebraMap k T.functionField c) →
        (letI := functionFieldAlgebra sX; haveI := F.isIntegral_stratum;
          letI := functionFieldAlgebra (ιS ≫ sX);
          IsIteratedResidueRec ((algebraMap _ X.functionField g •
            (show RationalPluriForms sX (2 + 1) m from formPow (exteriorPower.ιMulti X.functionField
              (2 + 1) (Fin.cons ((algebraMap _ X.functionField t)⁻¹ •
                KaehlerDifferential.D k _ (algebraMap _ X.functionField t))
                fun i => (algebraMap _ X.functionField (e i))⁻¹ •
                  KaehlerDifferential.D k _ (algebraMap _ X.functionField (e i)))) m)))
            F 0 (c • (show RationalPluriForms (ιS ≫ sX) 0 m from
              formPow (exteriorPower.ιMulti S.functionField 0 ![]) m))) := by
  classical
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (ι ≫ sX)
  have hX := h.1
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hTnv : IsNormalVariety k (ι ≫ sX) := by
    have := hι.1; rwa [Category.id_comp] at this
  haveI : LocallyOfFiniteType (ι ≫ sX) := hTnv.1.toLocallyOfFiniteType
  obtain ⟨-, -, -, -, hci, -⟩ := id hι
  haveI := hci
  have hdltT := isDltPair_of_isAdjunctionStep hdlt h hι P hP1 hrange
  set ē : Fin 2 → T.functionField := fun i => (ι.stalkMap (genericPoint T)).hom (e i) with hē
  have hē0 : ∀ i, ē i ≠ 0 := fun i => ((he i).map (ι.stalkMap (genericPoint T)).hom).ne_zero
  have hgen2 : IntermediateField.adjoin k ({ē 0, ē 1} : Set T.functionField) = ⊤ := by
    rw [← hgen]
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_two, hē]
    tauto
  have hvec : (fun i => (ē i)⁻¹ • KaehlerDifferential.D k T.functionField (ē i)) =
      ![(ē 0)⁻¹ • KaehlerDifferential.D k _ (ē 0), (ē 1)⁻¹ • KaehlerDifferential.D k _ (ē 1)] := by
    funext i; fin_cases i <;> rfl
  have hθ2 : ∀ Γ : Mori.PrimeDivisor T, (Γ.ordForm (show RationalPluriForms (ι ≫ sX) 2
      ((1 : ℕ) : ℤ) from formPow (exteriorPower.ιMulti T.functionField 2
        ![(ē 0)⁻¹ • KaehlerDifferential.D k _ (ē 0), (ē 1)⁻¹ • KaehlerDifferential.D k _ (ē 1)])
        1) : ℚ) + BT.coeff Γ = 0 := by
    intro Γ
    rw [← hvec]
    exact hθ Γ
  obtain ⟨TC, ιC, BC, hιC, hTC, hTCln, hTCn, hdltC, hdC, wC, hwC0, hadj, hresC, hψ⟩ :=
    exists_isAdjunctionStep_residue_dlog_of_surface (sT := ι ≫ sX) hTnv hdT hdltT (ē 0) (ē 1)
      (hē0 0) (hē0 1) hgen2 hθ2
  obtain ⟨-, -, -, -, hciC, -⟩ := id hιC
  haveI := hciC
  obtain ⟨Tq, ιq, Bq, hιq, hTq, hdq, hresq⟩ :=
    exists_isAdjunctionStep_residue_dlog_of_curve (sC := ιC ≫ ι ≫ sX) hιC.1 hdC hdltC wC hwC0
      hadj hψ
  have hιC' : IsAdjunctionStep ((ι ≫ 𝟙 X) ≫ sX) BT ιC BC := by simpa using hιC
  have hιq' : IsAdjunctionStep ((ιC ≫ ι ≫ 𝟙 X) ≫ sX) BC ιq Bq := by simpa using hιq
  refine ⟨Tq, ιq ≫ ιC ≫ ι ≫ 𝟙 X, Bq,
    .step (.step (.step (.refl h) ι BT hι) ιC BC hιC') ιq Bq hιq', rfl, hdq, fun g c hg => ?_⟩
  set Ω3 : RationalPluriForms sX (2 + 1) m := formPow (exteriorPower.ιMulti X.functionField (2 + 1)
    (Fin.cons ((algebraMap _ X.functionField t)⁻¹ •
      KaehlerDifferential.D k _ (algebraMap _ X.functionField t))
      fun i => (algebraMap _ X.functionField (e i))⁻¹ •
        KaehlerDifferential.D k _ (algebraMap _ X.functionField (e i)))) m with hΩ3
  set τg : RationalPluriForms sX (2 + 1) m := algebraMap _ X.functionField g • Ω3 with hτg
  set θm : RationalPluriForms (ι ≫ sX) 2 m := formPow (exteriorPower.ιMulti T.functionField 2
    ![(ē 0)⁻¹ • KaehlerDifferential.D k _ (ē 0), (ē 1)⁻¹ • KaehlerDifferential.D k _ (ē 1)]) m
    with hθm
  letI := functionFieldAlgebra (ιC ≫ ι ≫ sX)
  set ψm : RationalPluriForms (ιC ≫ ι ≫ sX) 1 m := formPow (exteriorPower.ιMulti TC.functionField 1
    ![wC⁻¹ • KaehlerDifferential.D k _ wC]) m with hψm
  letI := functionFieldAlgebra (ιq ≫ ιC ≫ ι ≫ sX)
  set εm : RationalPluriForms (ιq ≫ ιC ≫ ι ≫ sX) 0 m :=
    formPow (exteriorPower.ιMulti Tq.functionField 0 ![]) m with hεm
  have r1 : IsPoincareResidue sX ι 2 m τg (c • θm) := by
    have h1 := isPoincareResidue_formPow_dlog sX ι m t e he ht
    have h2 := IsPoincareResidue.smul_stalk h1 g
    rw [hg] at h2
    have e1 : (formPow (exteriorPower.ιMulti T.functionField 2 fun i =>
        ((ι.stalkMap (genericPoint T)).hom (e i))⁻¹ • KaehlerDifferential.D k T.functionField
          ((ι.stalkMap (genericPoint T)).hom (e i))) m : RationalPluriForms (ι ≫ sX) 2 m) = θm := by
      rw [hθm, ← hvec]
    rw [← e1]
    exact h2
  have r2 : IsPoincareResidue (ι ≫ sX) ιC 1 m (c • θm) (c • ψm) :=
    IsPoincareResidue.smul_const (hresC m) c
  have r3 : IsPoincareResidue (ιC ≫ ι ≫ sX) ιq 0 m (c • ψm) (c • εm) :=
    IsPoincareResidue.smul_const (hresq m) c
  have hs1 : sX = 𝟙 X ≫ sX := (Category.id_comp _).symm
  obtain ⟨ρ0, hρ0⟩ := exists_heq_rationalPluriForms hs1 τg
  have hs1' : ι ≫ sX = ι ≫ 𝟙 X ≫ sX := by rw [Category.id_comp]
  obtain ⟨ρ1, hρ1⟩ := exists_heq_rationalPluriForms hs1' (c • θm)
  have r1' : IsPoincareResidue (𝟙 X ≫ sX) ι 2 m ρ0 ρ1 :=
    IsPoincareResidue.congr_structure hs1 r1 hρ0 hρ1
  have hs2 : ι ≫ sX = (ι ≫ 𝟙 X) ≫ sX := by simp
  obtain ⟨ρ1', hρ1'⟩ := exists_heq_rationalPluriForms hs2 (c • θm)
  obtain ⟨ρ2, hρ2⟩ := exists_heq_rationalPluriForms (congrArg (ιC ≫ ·) hs2) (c • ψm)
  have r2' : IsPoincareResidue ((ι ≫ 𝟙 X) ≫ sX) ιC 1 m ρ1' ρ2 :=
    IsPoincareResidue.congr_structure hs2 r2 hρ1' hρ2
  have hs3 : ιC ≫ ι ≫ sX = (ιC ≫ ι ≫ 𝟙 X) ≫ sX := by simp
  obtain ⟨ρ2', hρ2'⟩ := exists_heq_rationalPluriForms hs3 (c • ψm)
  obtain ⟨ρ3, hρ3⟩ := exists_heq_rationalPluriForms (congrArg (ιq ≫ ·) hs3) (c • εm)
  have r3' : IsPoincareResidue ((ιC ≫ ι ≫ 𝟙 X) ≫ sX) ιq 0 m ρ2' ρ3 :=
    IsPoincareResidue.congr_structure hs3 r3 hρ2' hρ3
  have hs4 : ιq ≫ ιC ≫ ι ≫ sX = (ιq ≫ ιC ≫ ι ≫ 𝟙 X) ≫ sX := by simp
  have hfin := (heq_smul_formPow_ιMulti_zero hs4 c m).symm.trans hρ3
  exact ⟨ρ2', ⟨ρ1', ⟨ρ0, ⟨rfl, hρ0.symm⟩, ρ1, r1', hρ1'.symm.trans hρ1⟩, ρ2, r2',
    hρ2'.symm.trans hρ2⟩, ρ3, r3', hfin⟩

end FloorFlags

section SNCPointFlags

/-- The stalk at `x` of the ideal sheaf of a prime divisor through `x` is the prime of its generic
point in `𝒪_{X,x}`. -/
private theorem stalk_idealSheaf_eq_primeOfSpecializes {X : Scheme.{0}} (E : Mori.PrimeDivisor X)
    {x : X} (hx : x ∈ E.support) :
    IdealSheafData.stalk E.idealSheaf x = MMP.Intersection.primeOfSpecializes
      (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hx) := by
  set h := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hx
  rw [idealSheaf_eq_vanishingIdeal E, MMP.Resolution.stalk_vanishingIdeal_eq]
  have hset : X.fromSpecStalk x ⁻¹' (E.idealSheaf.support : Set X) =
      PrimeSpectrum.zeroLocus (MMP.Intersection.primeOfSpecializes h : Set _) := by
    ext p
    simp only [Set.mem_preimage, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    have hsp : X.fromSpecStalk x p ⤳ x := Stacks.Chow.specializes_fromSpecStalk x p
    have hp := MMP.Resolution.primeOfSpecializes_fromSpecStalk x p hsp
    constructor
    · intro hmem
      have hg : E.genericPoint ⤳ X.fromSpecStalk x p :=
        MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hmem
      have := MMP.Resolution.primeOfSpecializes_trans_le hg hsp
      rw [hp] at this
      exact this
    · intro hle
      have hle' : MMP.Intersection.primeOfSpecializes h ≤
          MMP.Intersection.primeOfSpecializes hsp := by rw [hp]; exact hle
      have hg := MMP.Intersection.specializes_of_primeOfSpecializes_le h hsp hle'
      have : X.fromSpecStalk x p ∈ (E.support : Set X) := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact specializes_iff_mem_closure.mp hg
      exact this
  erw [hset]
  rw [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
  exact (inferInstance : (MMP.Intersection.primeOfSpecializes h).IsPrime).radical

/-- **Coordinate divisors.** At a point `y` of an integral locally noetherian scheme whose local
ring has a regular system of parameters `w`, each `w_b` cuts out a prime divisor through `y`. -/
private theorem exists_primeDivisor_stalk_eq_span {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {y : X} {n : ℕ} {w : Fin n → X.presheaf.stalk y}
    (hw : IsRegularSystemOfParameters w) (b : Fin n) :
    ∃ E : Mori.PrimeDivisor X, y ∈ E.support ∧
      IdealSheafData.stalk E.idealSheaf y = Ideal.span {w b} := by
  haveI : IsRegularLocalRing (X.presheaf.stalk y) :=
    MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hw
  haveI := IsRegularLocalRing.isDomain (X.presheaf.stalk y)
  obtain ⟨hreg, -, -⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hw {b}
  have him : w '' ((({b} : Finset (Fin n)) : Set (Fin n))) = {w b} := by
    rw [Finset.coe_singleton, Set.image_singleton]
  rw [him] at hreg
  haveI := hreg
  haveI := IsRegularLocalRing.isDomain (X.presheaf.stalk y ⧸ Ideal.span {w b})
  have hprime : (Ideal.span {w b}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).1 inferInstance
  have hw0 : w b ≠ 0 := MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hw b
  have hwm : w b ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
    rw [← hw.1]; exact Ideal.subset_span ⟨b, rfl⟩
  have hh : (Ideal.span {w b}).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hw0)
      ((IsLocalRing.mem_maximalIdeal _).1 hwm)
  let q : (Spec (X.presheaf.stalk y) : Type) :=
    (⟨Ideal.span {w b}, hprime⟩ : PrimeSpectrum (X.presheaf.stalk y))
  have hc : Order.coheight (X.fromSpecStalk y q) = 1 :=
    (Stacks.Chow.coheight_fromSpecStalk_eq_height y q).trans hh
  set E : Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc
  have hEη : E.genericPoint = X.fromSpecStalk y q :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc
  have hsp : X.fromSpecStalk y q ⤳ y := Stacks.Chow.specializes_fromSpecStalk y q
  have hyE : y ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have e : AlgebraicGeometry.PrimeDivisor.genericPoint E = X.fromSpecStalk y q := hEη
    rw [e]
    exact specializes_iff_mem_closure.mp hsp
  refine ⟨E, hyE, ?_⟩
  rw [stalk_idealSheaf_eq_primeOfSpecializes E hyE,
    MMP.Resolution.primeOfSpecializes_congr hEη _ hsp,
    MMP.Resolution.primeOfSpecializes_fromSpecStalk y q hsp]

/-- **Coordinates on a component.** If `j : T ⟶ X` is a closed immersion from a reduced scheme
onto a prime divisor `E` whose ideal at `j p` is generated by the first member `z₀` of a regular
system of parameters `z`, the restrictions of the remaining `z_{i+1}` are a regular system of
parameters of `𝒪_{T,p}`. -/
private theorem isRegularSystemOfParameters_stalkMap_succ {T X : Scheme.{0}}
    [IsLocallyNoetherian X] (j : T ⟶ X) [IsClosedImmersion j] [IsReduced T]
    (E : Mori.PrimeDivisor X) (hE : Set.range j = (E.support : Set X)) (p : T) {d : ℕ}
    {z : Fin (d + 1) → X.presheaf.stalk (j p)} (hz : IsRegularSystemOfParameters z)
    (ha : IdealSheafData.stalk E.idealSheaf (j p) = Ideal.span {z 0}) :
    IsRegularSystemOfParameters (fun i : Fin d => (j.stalkMap p).hom (z i.succ)) := by
  obtain ⟨-, hsys⟩ := isRegularSystemOfParameters_stalkMap_of_isClosedImmersion j E hE p hz 0 ha
  have hcard : ({0}ᶜ : Finset (Fin (d + 1))).card = d := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]; omega
  refine ⟨?_, ?_⟩
  · rw [← hsys.1]
    congr 1
    ext x
    simp only [Set.mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      have hmem : i.succ ∈ Set.range (({0}ᶜ : Finset (Fin (d + 1))).orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        simp [Fin.succ_ne_zero]
      obtain ⟨i', hi'⟩ := hmem
      exact ⟨i', by rw [hi']⟩
    · rintro ⟨i, rfl⟩
      have h0 : (({0}ᶜ : Finset (Fin (d + 1))).orderEmbOfFin rfl) i ≠ 0 := by
        have := Finset.orderEmbOfFin_mem ({0}ᶜ : Finset (Fin (d + 1))) rfl i
        rwa [Finset.mem_compl, Finset.mem_singleton] at this
      obtain ⟨i', hi'⟩ := Fin.exists_succ_eq.2 h0
      exact ⟨i', by rw [hi']⟩
  · rw [hsys.2, hcard]

/-- **The residue of an snc log form along a coordinate divisor.** Let `z₀, …, z_d` be local
equations at `j(y)` of distinct prime divisors `L₀, …, L_d`, and `j : T ⟶ S` a closed immersion
onto `L₀`. The residue of `g (dlog z₀ ∧ ⋯ ∧ dlog z_d)^{⊗m}` along `T` is
`ḡ (dlog z̄₁ ∧ ⋯ ∧ dlog z̄_d)^{⊗m}`, the bars denoting restriction to `𝒪_{T,y}`. -/
private theorem isPoincareResidue_formPow_dlog_coordinate {k : Type} [Field k] {S T : Scheme.{0}}
    (sS : S ⟶ Spec (.of k)) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [IsIntegral T]
    (j : T ⟶ S) (L0 : Mori.PrimeDivisor S) (hr : Set.range j.base = (L0.support : Set S))
    (y' : T) {d : ℕ} (z : Fin (d + 1) → S.presheaf.stalk (j y'))
    (L : Fin (d + 1) → Mori.PrimeDivisor S) (hL : Function.Injective L)
    (hLy : ∀ a, j y' ∈ (L a).support)
    (hLz : ∀ a, IdealSheafData.stalk (L a).idealSheaf (j y') = Ideal.span {z a})
    (hL0 : L 0 = L0) (g : S.presheaf.stalk (j y')) (m : ℕ) :
    letI := functionFieldAlgebra sS
    letI := functionFieldAlgebra (j ≫ sS)
    IsPoincareResidue sS j d m
      (algebraMap _ S.functionField g •
        formPow (exteriorPower.ιMulti S.functionField (d + 1) fun a =>
          (algebraMap _ S.functionField (z a))⁻¹ •
            KaehlerDifferential.D k S.functionField (algebraMap _ S.functionField (z a))) m)
      (algebraMap (T.presheaf.stalk y') T.functionField ((j.stalkMap y').hom g) •
        formPow (exteriorPower.ιMulti T.functionField d fun i =>
          (algebraMap (T.presheaf.stalk y') T.functionField ((j.stalkMap y').hom (z i.succ)))⁻¹ •
            KaehlerDifferential.D k T.functionField (algebraMap (T.presheaf.stalk y')
              T.functionField ((j.stalkMap y').hom (z i.succ)))) m) := by
  letI := functionFieldAlgebra sS
  letI := functionFieldAlgebra (j ≫ sS)
  have h0 : genericPoint T ⤳ y' := (genericPoint_spec T).specializes trivial
  set h' := j.base.hom.map_specializes h0 with hh'
  have hP : j (genericPoint T) = L0.genericPoint := map_genericPoint_eq_of_range_eq j L0 hr
  have key : ∀ (p : S) (hp : p = (L 0).genericPoint) (h'' : p ⤳ j y'),
      S.ord (algebraMap (S.presheaf.stalk p) S.functionField
        ((S.presheaf.stalkSpecializes h'').hom (z 0))) p = 1 ∧
      ∀ i : Fin d, IsUnit ((S.presheaf.stalkSpecializes h'').hom (z i.succ)) := by
    rintro p rfl h''
    obtain ⟨hm, hu⟩ := maximalIdeal_eq_span_and_isUnit_at_genericPoint (L 0) (hLy 0) (hLz 0)
    haveI := (L 0).isDiscreteValuationRing_localRing
    have hirr : Irreducible ((S.presheaf.stalkSpecializes h'').hom (z 0)) :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hm
    have hne : algebraMap (S.presheaf.stalk (L 0).genericPoint) S.functionField
        ((S.presheaf.stalkSpecializes h'').hom (z 0)) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hirr.ne_zero
    exact ⟨(Scheme.ord_eq_iff (L 0).coheight_genericPoint hne).mpr (Ring.ordFrac_irreducible hirr),
      fun i => hu (L i.succ) (fun h => Fin.succ_ne_zero i (hL h)) (z i.succ) (hLz i.succ)⟩
  obtain ⟨hord, hunit⟩ := key (j (genericPoint T)) (by rw [hP, hL0]) h'
  have h1 := isPoincareResidue_formPow_dlog sS j m ((S.presheaf.stalkSpecializes h').hom (z 0))
    (fun i => (S.presheaf.stalkSpecializes h').hom (z i.succ)) hunit hord
  have h2 := IsPoincareResidue.smul_stalk h1 ((S.presheaf.stalkSpecializes h').hom g)
  have hsp : ∀ a, (j.stalkMap (genericPoint T)).hom ((S.presheaf.stalkSpecializes h').hom a) =
      algebraMap (T.presheaf.stalk y') T.functionField ((j.stalkMap y').hom a) :=
    fun a => Scheme.Hom.stalkSpecializes_stalkMap_apply j (genericPoint T) y' h0 a
  have hal : ∀ a, algebraMap (S.presheaf.stalk (j (genericPoint T))) S.functionField
      ((S.presheaf.stalkSpecializes h').hom a) = algebraMap _ S.functionField a :=
    fun a => Mori.algebraMap_stalkSpecializes h' a
  simp only [hsp, hal] at h2
  have e : (fun a => (algebraMap _ S.functionField (z a))⁻¹ •
      KaehlerDifferential.D k S.functionField (algebraMap _ S.functionField (z a))) =
      Fin.cons ((algebraMap _ S.functionField (z 0))⁻¹ •
        KaehlerDifferential.D k S.functionField (algebraMap _ S.functionField (z 0)))
        fun i => (algebraMap _ S.functionField (z i.succ))⁻¹ •
          KaehlerDifferential.D k S.functionField (algebraMap _ S.functionField (z i.succ)) := by
    funext a
    refine Fin.cases ?_ (fun i => ?_) a <;> rfl
  rw [e]
  exact h2

/-- Over a perfect field, a point with regular local ring is a smooth point. -/
private theorem mem_smoothLocus_of_isRegularLocalRing {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (x : X)
    [IsRegularLocalRing (X.presheaf.stalk x)] : x ∈ Mori.smoothLocus sX := by
  have h := congrArg (x ∈ ·) (AlgebraicGeometry.smoothAt_locus_eq_regular_locus k sX)
  have hs : x ∈ {x : X | InfinitesimalLifting.SmoothAt sX x} := h.mpr ‹_›
  rw [smoothLocus_eq_smoothLocus]
  exact Scheme.Hom.mem_smoothLocus.mpr (InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap sX _ hs)

/-- At a closed point of a scheme locally of finite type over an algebraically closed field the
residue field is `k`. -/
private theorem surjective_algebraMap_residueField_of_isClosed {k : Type} [Field k]
    [IsAlgClosed k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (x : X)
    (hx : IsClosed ({x} : Set X)) :
    letI := stalkAlgebra sX x
    Function.Surjective (algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x))) := by
  letI := stalkAlgebra sX x
  intro y
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨c, hc⟩ := exists_sub_mem_maximalIdeal_of_isClosed sX x hx r
  refine ⟨c, ?_⟩
  have h0 := (IsLocalRing.residue_eq_zero_iff _).2 hc
  rw [map_sub, sub_eq_zero] at h0
  rw [IsScalarTower.algebraMap_apply k (X.presheaf.stalk x)
    (IsLocalRing.ResidueField (X.presheaf.stalk x)), IsLocalRing.ResidueField.algebraMap_eq, ← h0]

/-- **Residues of an snc log form at a point stratum.** Let `(S, B_S)` be the final pair of a flag
of a pair `(X, B)`, dlt of dimension `d`, `y` a closed smooth point with regular system of
parameters `z₁, …, z_d` cutting out distinct prime divisors `L_a`, which are the components of
`Supp B_S` through `y`, all of coefficient one, with `div(dlog z₁ ∧ ⋯ ∧ dlog z_d) + B_S`
`ℚ`-Cartier. If the iterated residue of `τ` along the flag is `g (dlog z₁ ∧ ⋯ ∧ dlog z_d)^{⊗m}`
with `g ≡ c` modulo `𝔪_y`, `c ∈ k`, then the flag extends by `d` adjunction steps to a point
along which the iterated residue of `τ` is `c`. -/
private theorem exists_flag_isIteratedResidueRec_of_sncPoint {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {B : QDivisor X} {n m : ℕ} (τ : RationalPluriForms sX n m) (d : ℕ) :
    ∀ {S : Scheme.{0}} {ιS : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ιS BS)
      [IsIntegral S] [IsNormal S] [IsLocallyNoetherian S] [CompactSpace S]
      (sS : S ⟶ Spec (.of k)) (_ : ιS ≫ sX = sS) [LocallyOfFiniteType sS], IsNormalVariety k sS →
      MMP.Intersection.IsDltPair sS BS → topologicalKrullDim S = d →
      ∀ (y : S), IsClosed ({y} : Set S) → ∀ (z : Fin d → S.presheaf.stalk y),
      IsRegularSystemOfParameters z → y ∈ Mori.smoothLocus sS →
      ∀ (L : Fin d → Mori.PrimeDivisor S), Function.Injective L → (∀ a, y ∈ (L a).support) →
      (∀ a, IdealSheafData.stalk (L a).idealSheaf y = Ideal.span {z a}) →
      (∀ E : Mori.PrimeDivisor S, y ∈ E.support → BS.coeff E ≠ 0 → E ∈ Set.range L) →
      (∀ a, BS.coeff (L a) = 1) →
      (letI := functionFieldAlgebra sS;
        (Divisor.toQDivisor (divisorOfForm (show RationalPluriForms sS d ((1 : ℕ) : ℤ) from
          formPow (exteriorPower.ιMulti S.functionField d fun a =>
            (algebraMap (S.presheaf.stalk y) S.functionField (z a))⁻¹ • KaehlerDifferential.D k
              S.functionField (algebraMap (S.presheaf.stalk y) S.functionField (z a))) 1)) +
          BS).IsQCartier) →
      ∀ (g : S.presheaf.stalk y) (c : k),
      (letI := stalkAlgebra sS y; g - algebraMap k _ c ∈ IsLocalRing.maximalIdeal _) →
      (∃ ρ : @RationalPluriForms k _ S (ιS ≫ sX) F.isIntegral_stratum d m,
        IsIteratedResidueRec τ F d ρ ∧ HEq ρ (letI := functionFieldAlgebra sS;
          (show RationalPluriForms sS d m from algebraMap _ S.functionField g •
            formPow (exteriorPower.ιMulti S.functionField d fun a =>
            (algebraMap (S.presheaf.stalk y) S.functionField (z a))⁻¹ • KaehlerDifferential.D k
              S.functionField (algebraMap (S.presheaf.stalk y) S.functionField (z a))) m))) →
      ∃ (S' : Scheme.{0}) (ιS' : S' ⟶ X) (BS' : QDivisor S')
        (F' : StratumAdjunctionData sX B ιS' BS'),
        F'.length = F.length + d ∧ topologicalKrullDim S' = (0 : ℕ) ∧
        (haveI := F'.isIntegral_stratum; letI := functionFieldAlgebra (ιS' ≫ sX);
          IsIteratedResidueRec τ F' 0 (c • (show RationalPluriForms (ιS' ≫ sX) 0 m from
            formPow (exteriorPower.ιMulti S'.functionField 0 ![]) m))) := by
  induction d with
  | zero =>
    intro S ιS BS F _ _ _ _ sS hsS _ hS hdlt hdim y hy z hz hsm L hL hLy hLz hBL hL1 hQ g c hgc hρ
    subst hsS
    letI := functionFieldAlgebra (ιS ≫ sX)
    letI := stalkAlgebra (ιS ≫ sX) y
    haveI := isScalarTower_stalk_functionField (ιS ≫ sX) y
    obtain ⟨ρ, hρ1, hρ2⟩ := hρ
    have hm : IsLocalRing.maximalIdeal (S.presheaf.stalk y) = ⊥ := by
      rw [← hz.1]; simp
    have hgc' : g = algebraMap k _ c := by
      rw [hm, Submodule.mem_bot, sub_eq_zero] at hgc; exact hgc
    refine ⟨S, ιS, BS, F, by simp, hdim, ?_⟩
    have e2 : (fun a : Fin 0 => (algebraMap (S.presheaf.stalk y) S.functionField (z a))⁻¹ •
        KaehlerDifferential.D k S.functionField
          (algebraMap (S.presheaf.stalk y) S.functionField (z a))) = ![] :=
      funext fun a => a.elim0
    have e : ρ = c • (show RationalPluriForms (ιS ≫ sX) 0 m from
        formPow (exteriorPower.ιMulti S.functionField 0 ![]) m) := by
      rw [eq_of_heq hρ2]
      simp only [e2, hgc']
      rw [← IsScalarTower.algebraMap_apply]
      rfl
    rw [← e]; exact hρ1
  | succ d ih =>
    intro S ιS BS F _ _ _ _ sS hsS _ hS hdlt hdim y hy z hz hsm L hL hLy hLz hBL hL1 hQ g c hgc hρ
    subst hsS
    classical
    letI := functionFieldAlgebra (ιS ≫ sX)
    obtain ⟨T, j, BT, hpairS, hj0, hTi, hrT, hdT⟩ :=
      exists_isAdjunctionStep_of_isDltPair hS hdlt (e := d) hdim (L 0) (by rw [hL1 0])
    have hj : IsAdjunctionStep (ιS ≫ sX) BS j BT := by
      have := hj0; rwa [Category.id_comp] at this
    have hTnv : IsNormalVariety k (j ≫ ιS ≫ sX) := hj.1
    letI := functionFieldAlgebra (j ≫ ιS ≫ sX)
    haveI : IsNormal T := hTnv.2
    haveI : LocallyOfFiniteType (j ≫ ιS ≫ sX) := hTnv.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (j ≫ ιS ≫ sX)
    obtain ⟨-, -, -, -, hci, -⟩ := id hj
    haveI := hci
    haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace j
    have hdltT := isDltPair_of_isAdjunctionStep hdlt hpairS hj0 (L 0) (by rw [hL1 0]) hrT
    obtain ⟨y', rfl⟩ : ∃ y', j y' = y := by
      have : y ∈ Set.range j.base := by rw [hrT]; exact hLy 0
      exact this
    -- facts at `y = j y'`
    letI := stalkAlgebra (ιS ≫ sX) (j y')
    have hres := surjective_algebraMap_residueField_of_isClosed (ιS ≫ sX) (j y') hy
    obtain ⟨r, ⟨b⟩⟩ := exists_basis_kaehler_stalk_of_mem_smoothLocus (ιS ≫ sX) hsm
    haveI : Module.Finite (S.presheaf.stalk (j y')) Ω[S.presheaf.stalk (j y')⁄k] :=
      Module.Finite.of_basis b
    have hw := span_D_eq_top_of_span_eq_maximalIdeal hres z hz.1
    haveI : IsRegularLocalRing (S.presheaf.stalk (j y')) :=
      MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
    have hz0 : ∀ a, z a ≠ 0 := fun a => MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz a
    -- the snc log generator and its residue
    set τ1 : RationalPluriForms (ιS ≫ sX) (d + 1) ((1 : ℕ) : ℤ) := formPow (exteriorPower.ιMulti
      S.functionField (d + 1) fun a => (algebraMap (S.presheaf.stalk (j y')) S.functionField (z a))⁻¹ •
        KaehlerDifferential.D k S.functionField
          (algebraMap (S.presheaf.stalk (j y')) S.functionField (z a))) 1 with hτ1
    have hτ1L : (L 0).ordForm τ1 = -1 := by
      have := ordForm_formPow_dlog_eq hdim 1 z hz0 hw L hL hLy hLz (L 0) (hLy 0)
      rw [if_pos ⟨0, rfl⟩] at this
      exact this
    have hτ10 : τ1 ≠ 0 := by
      intro h0; rw [h0, Mori.PrimeDivisor.ordForm_zero] at hτ1L; exact absurd hτ1L (by decide)
    have hres1 := isPoincareResidue_formPow_dlog_coordinate (ιS ≫ sX) j (L 0) hrT y' z L hL hLy
      hLz rfl 1 1
    simp only [map_one, one_smul] at hres1
    obtain ⟨hgenT, hpbT⟩ := hj.isPullback_divisorOfForm_add_of_isPoincareResidue (n := d)
      (by rw [hdim]; norm_cast) (L 0) hrT τ1 hτ10 hτ1L _ hres1 hQ
    obtain ⟨U, hyU, hU⟩ := exists_open_coeff_divisorOfForm_add_eq_zero hdim z hz hsm hres L hL
      hLy hLz hBL hL1
    -- coordinates and coordinate divisors on `T`
    have hz' := isRegularSystemOfParameters_stalkMap_succ j (L 0) hrT y' hz (hLz 0)
    set z' : Fin d → T.presheaf.stalk y' := fun i => (j.stalkMap y').hom (z i.succ) with hz'def
    haveI : IsRegularLocalRing (T.presheaf.stalk y') :=
      MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz'
    have hz'0 : ∀ a, z' a ≠ 0 := fun a => MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz' a
    have hsm' : y' ∈ Mori.smoothLocus (j ≫ ιS ≫ sX) :=
      mem_smoothLocus_of_isRegularLocalRing (j ≫ ιS ≫ sX) y'
    have hy' : IsClosed ({y'} : Set T) := by
      have e : ({y'} : Set T) = j.base ⁻¹' {j y'} := by
        ext p
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        exact ⟨fun h => by rw [h], fun h => j.isClosedEmbedding.injective h⟩
      rw [e]
      exact hy.preimage j.isClosedEmbedding.continuous
    choose L' hL'y hL'z using fun b => exists_primeDivisor_stalk_eq_span hz' b
    have hL'inj : Function.Injective L' := by
      intro a a' haa
      by_contra hne
      have hsp : Ideal.span {z' a} = Ideal.span {z' a'} := by rw [← hL'z a, ← hL'z a', haa]
      obtain ⟨hreg, -, hsys⟩ :=
        MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz' {a}
      have hb : a' ∈ Set.range (({a}ᶜ : Finset (Fin d)).orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        simp [Ne.symm hne]
      obtain ⟨i, hi⟩ := hb
      haveI := hreg
      have h0 := MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hsys i
      apply h0
      rw [hi, Ideal.Quotient.eq_zero_iff_mem, Finset.coe_singleton, Set.image_singleton, hsp]
      exact Ideal.mem_span_singleton_self _
    letI := stalkAlgebra (j ≫ ιS ≫ sX) y'
    have hres' := surjective_algebraMap_residueField_of_isClosed (j ≫ ιS ≫ sX) y' hy'
    obtain ⟨r', ⟨b'⟩⟩ := exists_basis_kaehler_stalk_of_mem_smoothLocus (j ≫ ιS ≫ sX) hsm'
    haveI : Module.Finite (T.presheaf.stalk y') Ω[T.presheaf.stalk y'⁄k] :=
      Module.Finite.of_basis b'
    have hw' := span_D_eq_top_of_span_eq_maximalIdeal hres' z' hz'.1
    have hcoef : ∀ E : Mori.PrimeDivisor T, y' ∈ E.support →
        BT.coeff E = if E ∈ Set.range L' then 1 else 0 := by
      intro E hE
      have h1 := coeff_eq_zero_of_isPullback_of_forall hQ hpbT U hU E ⟨y', hE, hyU⟩
      rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor] at h1
      have h2 := ordForm_formPow_dlog_eq (sX := j ≫ ιS ≫ sX) hdT 1 z' hz'0 hw' L' hL'inj hL'y
        hL'z E hE
      have h3 : ((divisorOfForm (show RationalPluriForms (j ≫ ιS ≫ sX) d ((1 : ℕ) : ℤ) from
          formPow (exteriorPower.ιMulti T.functionField d fun a =>
            (algebraMap (T.presheaf.stalk y') T.functionField (z' a))⁻¹ • KaehlerDifferential.D k
              T.functionField (algebraMap (T.presheaf.stalk y') T.functionField (z' a))) 1)).coeff E :
          ℚ) = if E ∈ Set.range L' then -1 else 0 := by
        rw [coeff_divisorOfForm, h2]; split_ifs <;> simp
      rw [h3] at h1
      split_ifs at h1 ⊢ <;> linarith
    have hBL' : ∀ E : Mori.PrimeDivisor T, y' ∈ E.support → BT.coeff E ≠ 0 → E ∈ Set.range L' := by
      intro E hE h0
      rw [hcoef E hE] at h0
      by_contra hn
      rw [if_neg hn] at h0
      exact h0 rfl
    have hL1' : ∀ a, BT.coeff (L' a) = 1 := fun a => by rw [hcoef _ (hL'y a), if_pos ⟨a, rfl⟩]
    have hQ' := isQCartier_of_isPullback hQ hpbT
    -- the residue of the given form
    obtain ⟨ρ, hρ1, hρ2⟩ := hρ
    have hres2 := isPoincareResidue_formPow_dlog_coordinate (ιS ≫ sX) j (L 0) hrT y' z L hL hLy
      hLz rfl g m
    have hgc' : (j.stalkMap y').hom g - algebraMap k _ c ∈
        IsLocalRing.maximalIdeal (T.presheaf.stalk y') := by
      have := map_nonunit (j.stalkMap y').hom _ hgc
      rwa [map_sub, stalkMap_algebraMap_const (ιS ≫ sX) j y' c] at this
    obtain ⟨ρ', hρ'⟩ := exists_heq_rationalPluriForms (s := j ≫ ιS ≫ sX) (s' := (j ≫ ιS) ≫ sX)
      (Category.assoc _ _ _).symm (show RationalPluriForms (j ≫ ιS ≫ sX) d m from
      (algebraMap (T.presheaf.stalk y') T.functionField ((j.stalkMap y').hom g) •
        formPow (exteriorPower.ιMulti T.functionField d fun i =>
          (algebraMap (T.presheaf.stalk y') T.functionField ((j.stalkMap y').hom (z i.succ)))⁻¹ •
            KaehlerDifferential.D k T.functionField (algebraMap (T.presheaf.stalk y')
              T.functionField ((j.stalkMap y').hom (z i.succ)))) m))
    have hrec : IsIteratedResidueRec τ (F.step j BT hj) d ρ' :=
      ⟨ρ, hρ1, _, by rw [eq_of_heq hρ2]; exact hres2, hρ'.symm⟩
    obtain ⟨S', ιS', BS', F', hlen, hdim', hfin⟩ := ih (F.step j BT hj) (j ≫ ιS ≫ sX)
      (Category.assoc _ _ _) hTnv hdltT hdT y' hy' z' hz' hsm' L' hL'inj hL'y hL'z hBL' hL1' hQ'
      ((j.stalkMap y').hom g) c hgc' ⟨ρ', hrec, hρ'.symm⟩
    refine ⟨S', ιS', BS', F', ?_, hdim', hfin⟩
    rw [hlen]
    simp only [StratumAdjunctionData.length]
    omega

end SNCPointFlags

section PointHelpers

/-- The `m`-th power of the unit form of degree zero is nonzero. -/
private theorem formPow_ιMulti_zero_ne_zero {k K : Type*} [Field k] [Field K] [Algebra k K]
    (m : ℕ) : (formPow (exteriorPower.ιMulti K 0 ![]) m : PluriForms k K 0 m) ≠ 0 := by
  intro h0
  let Φ : MultilinearMap K (fun _ : Fin m => ⋀[K]^0 Ω[K⁄k]) K :=
    (MultilinearMap.mkPiAlgebra K (Fin m) K).compLinearMap
      fun _ => (exteriorPower.zeroEquiv K Ω[K⁄k]).toLinearMap
  have h1 := congrArg (PiTensorProduct.lift Φ) h0
  unfold formPow at h1
  rw [PiTensorProduct.lift.tprod] at h1
  erw [map_zero] at h1
  simp [Φ] at h1

/-- The members of a regular system of parameters lie in the weighted monomial ideal of level one
for positive weights. -/
private theorem span_range_le_weightedMonomialIdeal_one {R : Type*} [CommRing R] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (z : ι → R) (α : ι → ℕ) (hα : ∀ i, 0 < α i) :
    Ideal.span (Set.range z) ≤ weightedMonomialIdeal z α 1 := by
  rw [Ideal.span_le]
  rintro _ ⟨a, rfl⟩
  refine Ideal.subset_span ⟨Pi.single a 1, ?_, ?_⟩
  · rw [Finset.sum_eq_single a (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])
      (fun h => absurd (Finset.mem_univ a) h), Pi.single_eq_same, mul_one]
    exact hα a
  · rw [Fintype.prod_eq_single a (fun b hb => by rw [Pi.single_eq_of_ne hb, pow_zero]),
      Pi.single_eq_same, pow_one]

/-- `φ^*(c (dlog x₁ ∧ ⋯ ∧ dlog x_d)^{⊗a}) = φ(c) (dlog φx₁ ∧ ⋯ ∧ dlog φx_d)^{⊗a}`. -/
private theorem pluriformPullback_smul_formPow_dlog {k : Type} [Field k] [CharZero k]
    {X X' : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X]
    [IsIntegral X'] [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] {d : ℕ}
    (hX : topologicalKrullDim X = d) (hX' : topologicalKrullDim X' = d)
    (φ : FunctionFieldHom sX sX') (x : Fin d → X'.functionField) (a : ℕ)
    (c : X'.functionField) :
    letI := functionFieldAlgebra sX'; letI := functionFieldAlgebra sX
    pluriformPullback sX sX' φ d a (c • formPow (exteriorPower.ιMulti X'.functionField d
      fun i => (x i)⁻¹ • KaehlerDifferential.D k X'.functionField (x i)) a) =
      φ c • formPow (exteriorPower.ιMulti X.functionField d
        fun i => (φ (x i))⁻¹ • KaehlerDifferential.D k X.functionField (φ (x i))) a := by
  letI := functionFieldAlgebra sX'
  letI := functionFieldAlgebra sX
  rw [pluriformPullback_smul_formPow' hX hX' φ]
  congr 2
  have e1 : (exteriorPower.ιMulti X'.functionField d
      fun i => (x i)⁻¹ • KaehlerDifferential.D k X'.functionField (x i)) =
      (∏ i, (x i)⁻¹) • exteriorPower.ιMulti X'.functionField d
        fun i => KaehlerDifferential.D k X'.functionField (x i) := by
    rw [show (fun i => (x i)⁻¹ • KaehlerDifferential.D k X'.functionField (x i)) =
      fun i => (fun i => (x i)⁻¹) i • (fun i => KaehlerDifferential.D k X'.functionField (x i)) i
        from rfl, AlternatingMap.map_smul_univ]
  have e2 : (exteriorPower.ιMulti X.functionField d
      fun i => (φ (x i))⁻¹ • KaehlerDifferential.D k X.functionField (φ (x i))) =
      (∏ i, (φ (x i))⁻¹) • exteriorPower.ιMulti X.functionField d
        fun i => KaehlerDifferential.D k X.functionField (φ (x i)) := by
    rw [show (fun i => (φ (x i))⁻¹ • KaehlerDifferential.D k X.functionField (φ (x i))) =
      fun i => (fun i => (φ (x i))⁻¹) i • (fun i => KaehlerDifferential.D k X.functionField
        (φ (x i))) i from rfl, AlternatingMap.map_smul_univ]
  rw [e1, e2, topFormsMap_smul_ιMulti_D φ, map_prod]
  simp only [map_inv₀]

/-- **Local coefficients of log pluricanonical sections.** At a point `x` with snc coordinates
`z₁, …, z_d`, the components of `Supp B` through `x` being the divisors `L_a = (z_a)`, all of
coefficient one, every section `ω` of `m(K_X + B)` is `g (dlog z₁ ∧ ⋯ ∧ dlog z_d)^{⊗m}` with
`g ∈ 𝒪_{X,x}`. -/
private theorem exists_algebraMap_smul_of_mem_logPluricanonicalSections {k : Type} [Field k]
    [PerfectField k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX] {d : ℕ}
    (hd : topologicalKrullDim X = d) (hd0 : 0 < d) {x : X} (z : Fin d → X.presheaf.stalk x)
    (hz0 : ∀ a, z a ≠ 0)
    (hw : letI := stalkAlgebra sX x
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun i => KaehlerDifferential.D k (X.presheaf.stalk x) (z i)) = ⊤)
    (L : Fin d → Mori.PrimeDivisor X) (hL : Function.Injective L) (hLx : ∀ a, x ∈ (L a).support)
    (hLz : ∀ a, IdealSheafData.stalk (L a).idealSheaf x = Ideal.span {z a}) {B : QDivisor X}
    (hBL : ∀ E : Mori.PrimeDivisor X, x ∈ E.support → B.coeff E ≠ 0 → E ∈ Set.range L)
    (hL1 : ∀ a, B.coeff (L a) = 1) {m : ℕ} (hm : 0 < m) (ω : RationalPluriForms sX d m)
    (hω : ω ∈ logPluricanonicalSections sX d m B) :
    letI := functionFieldAlgebra sX
    ∃ g : X.presheaf.stalk x, ω = algebraMap _ X.functionField g •
      (show RationalPluriForms sX d m from formPow (exteriorPower.ιMulti X.functionField d
        fun a => (algebraMap (X.presheaf.stalk x) X.functionField (z a))⁻¹ •
          KaehlerDifferential.D k X.functionField
            (algebraMap (X.presheaf.stalk x) X.functionField (z a))) m) := by
  classical
  letI := functionFieldAlgebra sX
  set τ0 : RationalPluriForms sX d m := formPow (exteriorPower.ιMulti X.functionField d
    fun a => (algebraMap (X.presheaf.stalk x) X.functionField (z a))⁻¹ •
      KaehlerDifferential.D k X.functionField
        (algebraMap (X.presheaf.stalk x) X.functionField (z a))) m with hτ0
  have hord := fun E hE => ordForm_formPow_dlog_eq hd m z hz0 hw L hL hLx hLz E hE
  have hτ00 : τ0 ≠ 0 := by
    intro h0
    have := hord (L ⟨0, hd0⟩) (hLx _)
    rw [if_pos ⟨_, rfl⟩] at this
    change (L ⟨0, hd0⟩).ordForm τ0 = _ at this
    rw [h0, Mori.PrimeDivisor.ordForm_zero] at this
    omega
  by_cases hω0 : ω = 0
  · exact ⟨0, by rw [hω0, map_zero, zero_smul]⟩
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hd
  set Bm := Mori.ZTensorPower.basis b (m : ℤ)
  have hrep : ∀ y : RationalPluriForms sX d m, Bm.repr y () • Bm () = y :=
    fun y => MMP.Mori.basis_unit_repr_smul Bm y
  have hτr : Bm.repr τ0 () ≠ 0 := by
    intro h; apply hτ00
    have := hrep τ0
    rw [h, zero_smul] at this
    exact this.symm
  set f := Bm.repr ω () / Bm.repr τ0 () with hf
  have hωf : ω = f • τ0 := by
    have h3 : (Bm.repr ω () • Bm () : ZTensorPower X.functionField
        (⋀[X.functionField]^d Ω[X.functionField⁄k]) (m : ℤ)) =
        f • (Bm.repr τ0 () • Bm () : ZTensorPower X.functionField
          (⋀[X.functionField]^d Ω[X.functionField⁄k]) (m : ℤ)) := by
      rw [smul_smul, hf, div_mul_cancel₀ _ hτr]
    rw [hrep ω, hrep τ0] at h3
    exact h3
  have hf0 : f ≠ 0 := by
    intro h; apply hω0; rw [hωf, h, zero_smul]
  have hpos : ∀ E : Mori.PrimeDivisor X, x ∈ E.support → 0 ≤ X.ord f E.genericPoint := by
    intro E hE
    have h1 := (mem_pluricanonicalSections_of_ne_bot top_ne_bot).1
      ((mem_logPluricanonicalSections sX).1 hω) E ⟨E.genericPoint, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
        trivial⟩ hω0
    rw [hωf, Mori.PrimeDivisor.ordForm_smul_of_topologicalKrullDim_eq E hd hf0 hτ00] at h1
    have h2 := hord E hE
    change E.ordForm τ0 = _ at h2
    rw [h2, DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul] at h1
    split_ifs at h1 with hE'
    · obtain ⟨a, rfl⟩ := hE'
      rw [hL1, zsmul_eq_mul, mul_one, Int.floor_intCast] at h1
      omega
    · have hB0 : B.coeff E = 0 := by
        by_contra h; exact hE' (hBL E hE h)
      rw [hB0, smul_zero, Int.floor_zero] at h1
      omega
  obtain ⟨g, hg⟩ := MMP.Threefold.Bridges.exists_algebraMap_stalk_eq_of_forall_zero_le_ord x hf0 hpos
  exact ⟨g, by rw [hωf, ← hg]⟩

/-- The function field of an integral `k`-scheme of dimension zero locally of finite type over an
algebraically closed field `k` is `k`. -/
private theorem bijective_algebraMap_functionField_of_topologicalKrullDim_eq_zero {k : Type}
    [Field k] [IsAlgClosed k] {S : Scheme.{0}} (sS : S ⟶ Spec (.of k)) [IsIntegral S]
    [LocallyOfFiniteType sS] [CompactSpace S] (hS : topologicalKrullDim S = (0 : ℕ)) :
    letI := functionFieldAlgebra sS
    Function.Bijective (algebraMap k S.functionField) := by
  letI := functionFieldAlgebra sS
  refine ⟨(algebraMap k S.functionField).injective, fun r => ?_⟩
  have hcl : IsClosed ({genericPoint S} : Set S) :=
    isClosed_singleton_of_le_coheight (d := 0) hS.le (by simp)
  obtain ⟨c, hc⟩ := exists_sub_mem_maximalIdeal_of_isClosed sS (genericPoint S) hcl r
  refine ⟨c, ?_⟩
  have h0 : IsLocalRing.maximalIdeal S.functionField = ⊥ := IsLocalRing.maximalIdeal_eq_bot
  rw [h0, Submodule.mem_bot, sub_eq_zero] at hc
  exact hc.symm

/-- A `k`-isomorphism between the function fields of two point strata. -/
private theorem nonempty_functionFieldEquiv_of_topologicalKrullDim_eq_zero {k : Type} [Field k]
    [IsAlgClosed k] {S S' : Scheme.{0}} (sS : S ⟶ Spec (.of k)) (sS' : S' ⟶ Spec (.of k))
    [IsIntegral S] [IsIntegral S'] [LocallyOfFiniteType sS] [LocallyOfFiniteType sS']
    [CompactSpace S] [CompactSpace S'] (hS : topologicalKrullDim S = (0 : ℕ))
    (hS' : topologicalKrullDim S' = (0 : ℕ)) : Nonempty (FunctionFieldEquiv sS sS') := by
  letI := functionFieldAlgebra sS
  letI := functionFieldAlgebra sS'
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId k S'.functionField)
    (bijective_algebraMap_functionField_of_topologicalKrullDim_eq_zero sS' hS')).symm.trans
      (AlgEquiv.ofBijective (Algebra.ofId k S.functionField)
        (bijective_algebraMap_functionField_of_topologicalKrullDim_eq_zero sS hS))⟩

/-- The pull-back of a constant form of degree zero is the same constant. -/
private theorem pluriformPullback_smul_formPow_ιMulti_zero {k : Type} [Field k] [CharZero k]
    {X X' : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X]
    [IsIntegral X'] [LocallyOfFiniteType sX] [LocallyOfFiniteType sX']
    (hX : topologicalKrullDim X = (0 : ℕ)) (hX' : topologicalKrullDim X' = (0 : ℕ))
    (φ : FunctionFieldHom sX sX') (c : k) (m : ℕ) :
    letI := functionFieldAlgebra sX'; letI := functionFieldAlgebra sX
    pluriformPullback sX sX' φ 0 m (c • (show RationalPluriForms sX' 0 m from
      formPow (exteriorPower.ιMulti X'.functionField 0 ![]) m)) =
      c • (show RationalPluriForms sX 0 m from
        formPow (exteriorPower.ιMulti X.functionField 0 ![]) m) := by
  letI := functionFieldAlgebra sX'
  letI := functionFieldAlgebra sX
  have h := pluriformPullback_smul_formPow_dlog hX hX' φ ![] m (algebraMap k X'.functionField c)
  have e1 : (fun i : Fin 0 => ((![] : Fin 0 → X'.functionField) i)⁻¹ •
      KaehlerDifferential.D k X'.functionField ((![] : Fin 0 → X'.functionField) i)) = ![] :=
    funext fun i => i.elim0
  have e2 : (fun i : Fin 0 => (φ ((![] : Fin 0 → X'.functionField) i))⁻¹ •
      KaehlerDifferential.D k X.functionField (φ ((![] : Fin 0 → X'.functionField) i))) = ![] :=
    funext fun i => i.elim0
  rw [e1, e2, AlgHom.commutes] at h
  exact h

end PointHelpers

section CurveHelpers

open KaehlerDifferential in
private theorem span_D_sum_eq_top_of_span_eq_maximalIdeal {k O : Type*} [Field k] [CommRing O]
    [IsLocalRing O] [Algebra k O] [Module.Finite O Ω[O⁄k]]
    {ι ι' : Type*} (z : ι → O) (hz : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal O)
    (v : ι' → O)
    (hv : Submodule.span (IsLocalRing.ResidueField O) (Set.range fun i =>
      KaehlerDifferential.D k (IsLocalRing.ResidueField O)
        (algebraMap O (IsLocalRing.ResidueField O) (v i))) = ⊤) :
    Submodule.span O (Set.range (Sum.elim (fun i => KaehlerDifferential.D k O (z i))
      (fun i => KaehlerDifferential.D k O (v i)))) = ⊤ := by
  rw [← IsLocalRing.map_tensorProduct_mk_eq_top]
  set L := IsLocalRing.ResidueField O
  have hπ : Function.Surjective (algebraMap O L) := IsLocalRing.residue_surjective
  have hexact := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k O L hπ
  have hker : RingHom.ker (algebraMap O L) = IsLocalRing.maximalIdeal O := by
    ext a; simp [L, IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
  rw [Submodule.map_span, eq_top_iff]
  rintro y -
  obtain ⟨S, hS⟩ : ∃ S : Submodule O (TensorProduct O L Ω[O⁄k]), S = Submodule.span O
      ((TensorProduct.mk O L Ω[O⁄k] 1) '' Set.range (Sum.elim
        (fun i => KaehlerDifferential.D k O (z i)) (fun i => KaehlerDifferential.D k O (v i)))) :=
    ⟨_, rfl⟩
  suffices h : y ∈ S by rw [hS] at h; exact h
  -- the image of `y` in `Ω_L` is a combination of the `d v̄_i`
  have hy : KaehlerDifferential.mapBaseChange k O L y ∈
      Submodule.map ((KaehlerDifferential.mapBaseChange k O L).restrictScalars O) S := by
    have h1 : KaehlerDifferential.mapBaseChange k O L y ∈ Submodule.span L (Set.range fun i =>
        KaehlerDifferential.D k L (algebraMap O L (v i))) := hv ▸ Submodule.mem_top
    generalize KaehlerDifferential.mapBaseChange k O L y = w0 at h1
    induction h1 using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      refine ⟨(1 : L) ⊗ₜ[O] KaehlerDifferential.D k O (v i),
        hS ▸ Submodule.subset_span ⟨_, ⟨Sum.inr i, rfl⟩, rfl⟩, ?_⟩
      simp [KaehlerDifferential.mapBaseChange_tmul]
    | zero => exact Submodule.zero_mem _
    | add w w' _ _ hw hw' => exact Submodule.add_mem _ hw hw'
    | smul c w _ hw =>
      obtain ⟨a, rfl⟩ := hπ c
      rw [algebraMap_smul]
      exact Submodule.smul_mem _ a hw
  obtain ⟨y', hy'S, hyy'⟩ := hy
  have hdiff : y - y' ∈ S := by
    obtain ⟨c, hc⟩ := (hexact (y - y')).mp (by
      rw [map_sub, show KaehlerDifferential.mapBaseChange k O L y' =
        KaehlerDifferential.mapBaseChange k O L y from hyy', sub_self])
    obtain ⟨⟨a, ha⟩, rfl⟩ := Ideal.toCotangent_surjective _ c
    rw [← hc, KaehlerDifferential.kerCotangentToTensor_toCotangent]
    change (1 : L) ⊗ₜ[O] KaehlerDifferential.D k O a ∈ _
    have ha' : a ∈ Ideal.span (Set.range z) := by rw [hz, ← hker]; exact ha
    clear ha hc
    subst hS
    induction ha' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨KaehlerDifferential.D k O (z i), ⟨Sum.inl i, rfl⟩, rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
      rw [map_add, TensorProduct.tmul_add]
      exact Submodule.add_mem _ ihx ihy
    | smul r x hx ih =>
      rw [smul_eq_mul, Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul,
        TensorProduct.tmul_smul]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ ih) ?_
      have : algebraMap O L x = 0 := by
        rw [← RingHom.mem_ker, hker, ← hz]; exact hx
      rw [← algebraMap_smul L x, this, zero_smul]
      exact Submodule.zero_mem _
  have := S.add_mem hdiff hy'S
  rwa [sub_add_cancel] at this

open Classical in
/-- **The snc log generator with unit coordinates.** Let `z₁, …, z_d ∈ 𝒪_{X,x}` (`d = dim X`) be
nonzero with differentials spanning `Ω_{𝒪_{X,x}/k}`. Suppose that for `a` in a set `S` the
element `z_a` generates the ideal of a prime divisor `L_a` through `x` (the `L_a` distinct), and
that `z_a` is a unit for `a ∉ S`. Along a prime divisor `Γ` through `x`, the form
`(dlog z₁ ∧ ⋯ ∧ dlog z_d)^{⊗m}` has order `-m` if `Γ` is one of the `L_a`, `a ∈ S`, and `0`
otherwise. -/
private theorem ordForm_formPow_dlog_eq_of_isUnit {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] {d : ℕ} (hd : topologicalKrullDim X = d) (m : ℕ) {x : X}
    (z : Fin d → X.presheaf.stalk x) (hz0 : ∀ a, z a ≠ 0)
    (hw : letI := stalkAlgebra sX x
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun i => KaehlerDifferential.D k (X.presheaf.stalk x) (z i)) = ⊤)
    (S : Set (Fin d)) (L : Fin d → Mori.PrimeDivisor X) (hL : Set.InjOn L S)
    (hLx : ∀ a ∈ S, x ∈ (L a).support)
    (hLz : ∀ a ∈ S, IdealSheafData.stalk (L a).idealSheaf x = Ideal.span {z a})
    (hu : ∀ a ∉ S, IsUnit (z a))
    (Γ : Mori.PrimeDivisor X) (hΓ : x ∈ Γ.support) :
    letI := functionFieldAlgebra sX
    Γ.ordForm (show RationalPluriForms sX d m from formPow (exteriorPower.ιMulti
      X.functionField d fun a =>
        (algebraMap (X.presheaf.stalk x) X.functionField (z a))⁻¹ • KaehlerDifferential.D k
          X.functionField (algebraMap (X.presheaf.stalk x) X.functionField (z a))) m) =
      if Γ ∈ L '' S then -(m : ℤ) else 0 := by
  letI := functionFieldAlgebra sX
  set f : Fin d → X.functionField := fun a => algebraMap (X.presheaf.stalk x) X.functionField (z a)
  have hf : ∀ a, f a ≠ 0 := fun a =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hz0 a)
  have hsplit : (exteriorPower.ιMulti X.functionField d fun a =>
      (f a)⁻¹ • KaehlerDifferential.D k X.functionField (f a)) =
      (∏ a, (f a)⁻¹) • exteriorPower.ιMulti X.functionField d fun a =>
        KaehlerDifferential.D k X.functionField (f a) := by
    rw [← AlternatingMap.map_smul_univ]
  change Γ.ordForm (show RationalPluriForms sX d m from formPow (exteriorPower.ιMulti
      X.functionField d fun a => (f a)⁻¹ • KaehlerDifferential.D k X.functionField (f a)) m) = _
  rw [hsplit, formPow_smul', ordForm_smul_formPow_ιMulti_D_eq hd m Γ hΓ z hw,
    ord_prod_inv_pow Finset.univ hf]
  have hord : ∀ a, X.ord (f a) Γ.genericPoint = if a ∈ S ∧ Γ = L a then 1 else 0 := by
    intro a
    by_cases ha : a ∈ S
    · simp only [f]
      rw [ord_algebraMap_eq_ite_of_stalk_eq_span Γ hΓ (L a) (hLx a ha) (hLz a ha)]
      simp [ha]
    · rw [if_neg (fun h => ha h.1)]
      set h := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support Γ hΓ
      simp only [f]
      rw [← Mori.algebraMap_stalkSpecializes h]
      exact Γ.ord_algebraMap_of_isUnit ((hu a ha).map _)
  rw [Finset.sum_congr rfl fun a _ => hord a]
  split_ifs with hmem
  · obtain ⟨a₀, ha₀, rfl⟩ := hmem
    rw [Finset.sum_eq_single a₀ (fun b _ hb => if_neg fun h => hb (hL h.1 ha₀ h.2.symm))
      (fun h => absurd (Finset.mem_univ a₀) h), if_pos ⟨ha₀, rfl⟩]
    ring
  · rw [Finset.sum_eq_zero fun a _ => if_neg fun h => hmem ⟨a, h.1, h.2.symm⟩]
    ring

/-- **The snc log generator with unit coordinates is a log generator near its point.** As
`ordForm_formPow_dlog_eq_of_isUnit`, when moreover the `L_a`, `a ∈ S`, are exactly the components
of `Supp B` through `x`, all of coefficient one: `div(dlog z₁ ∧ ⋯ ∧ dlog z_d) + B` vanishes on an
open neighbourhood of `x`. -/
private theorem exists_open_coeff_divisorOfForm_add_eq_zero_of_isUnit {k : Type} [Field k]
    [PerfectField k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] {d : ℕ}
    (hd : topologicalKrullDim X = d) {x : X}
    (z : Fin d → X.presheaf.stalk x) (hz0 : ∀ a, z a ≠ 0)
    (hw : letI := stalkAlgebra sX x
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun i => KaehlerDifferential.D k (X.presheaf.stalk x) (z i)) = ⊤)
    (S : Set (Fin d)) (L : Fin d → Mori.PrimeDivisor X) (hL : Set.InjOn L S)
    (hLx : ∀ a ∈ S, x ∈ (L a).support)
    (hLz : ∀ a ∈ S, IdealSheafData.stalk (L a).idealSheaf x = Ideal.span {z a})
    (hu : ∀ a ∉ S, IsUnit (z a)) {B : QDivisor X}
    (hBL : ∀ E : Mori.PrimeDivisor X, x ∈ E.support → B.coeff E ≠ 0 → E ∈ L '' S)
    (hL1 : ∀ a ∈ S, B.coeff (L a) = 1) :
    letI := functionFieldAlgebra sX
    ∃ U : X.Opens, x ∈ U ∧ ∀ E : Mori.PrimeDivisor X, (E.support ∩ (U : Set X)).Nonempty →
      (Divisor.toQDivisor (divisorOfForm (show RationalPluriForms sX d ((1 : ℕ) : ℤ) from
        formPow (exteriorPower.ιMulti X.functionField d fun a =>
          (algebraMap (X.presheaf.stalk x) X.functionField (z a))⁻¹ • KaehlerDifferential.D k
            X.functionField (algebraMap (X.presheaf.stalk x) X.functionField (z a))) 1)) +
        B).coeff E = 0 := by
  classical
  letI := functionFieldAlgebra sX
  set τ : RationalPluriForms sX d ((1 : ℕ) : ℤ) := formPow (exteriorPower.ιMulti X.functionField d
    fun a => (algebraMap (X.presheaf.stalk x) X.functionField (z a))⁻¹ • KaehlerDifferential.D k
      X.functionField (algebraMap (X.presheaf.stalk x) X.functionField (z a))) 1 with hτ
  have hx0 : ∀ E : Mori.PrimeDivisor X, x ∈ E.support →
      (Divisor.toQDivisor (divisorOfForm τ) + B).coeff E = 0 := by
    intro E hE
    have h1 := ordForm_formPow_dlog_eq_of_isUnit hd 1 z hz0 hw S L hL hLx hLz hu E hE
    rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm]
    change ((E.ordForm τ : ℤ) : ℚ) + B.coeff E = 0
    rw [hτ, h1]
    split_ifs with hEL
    · obtain ⟨a, ha, rfl⟩ := hEL
      rw [hL1 a ha]; push_cast; ring
    · by_cases hB : B.coeff E = 0
      · rw [hB]; simp
      · exact absurd (hBL E hE hB) hEL
  set N := Divisor.toQDivisor (divisorOfForm τ) + B with hN
  set S' : Finset (Mori.PrimeDivisor X) := N.support.filter fun E => x ∉ E.support with hS'
  have hSc : IsClosed (⋃ E ∈ S', (E.support : Set X)) :=
    isClosed_biUnion_finset fun E _ => by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  refine ⟨⟨(⋃ E ∈ S', (E.support : Set X))ᶜ, hSc.isOpen_compl⟩, ?_, ?_⟩
  · change x ∉ ⋃ E ∈ S', (E.support : Set X)
    simp only [Set.mem_iUnion, not_exists]
    intro E hE hxE
    exact (Finset.mem_filter.1 hE).2 hxE
  · intro E ⟨y, hyE, hyU⟩
    by_contra hne
    by_cases hxE : x ∈ E.support
    · exact hne (hx0 E hxE)
    · apply hyU
      refine Set.mem_biUnion (x := E) ?_ hyE
      exact Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 hne, hxE⟩

/-- **Coefficients of log sections along an snc log generator with unit coordinates.** In the
situation of `exists_open_coeff_divisorOfForm_add_eq_zero_of_isUnit`, every log `m`-canonical
section is `g · (dlog z₁ ∧ ⋯ ∧ dlog z_d)^{⊗m}` with `g ∈ 𝒪_{X,x}`. -/
private theorem exists_algebraMap_smul_of_mem_logPluricanonicalSections_of_isUnit {k : Type}
    [Field k] [PerfectField k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX] {d : ℕ}
    (hd : topologicalKrullDim X = d) {x : X} (z : Fin d → X.presheaf.stalk x)
    (hz0 : ∀ a, z a ≠ 0)
    (hw : letI := stalkAlgebra sX x
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun i => KaehlerDifferential.D k (X.presheaf.stalk x) (z i)) = ⊤)
    (S : Set (Fin d)) (L : Fin d → Mori.PrimeDivisor X) (hL : Set.InjOn L S)
    (hLx : ∀ a ∈ S, x ∈ (L a).support)
    (hLz : ∀ a ∈ S, IdealSheafData.stalk (L a).idealSheaf x = Ideal.span {z a})
    (hu : ∀ a ∉ S, IsUnit (z a)) (hS : S.Nonempty) {B : QDivisor X}
    (hBL : ∀ E : Mori.PrimeDivisor X, x ∈ E.support → B.coeff E ≠ 0 → E ∈ L '' S)
    (hL1 : ∀ a ∈ S, B.coeff (L a) = 1) {m : ℕ} (hm : 0 < m) (ω : RationalPluriForms sX d m)
    (hω : ω ∈ logPluricanonicalSections sX d m B) :
    letI := functionFieldAlgebra sX
    ∃ g : X.presheaf.stalk x, ω = algebraMap _ X.functionField g •
      (show RationalPluriForms sX d m from formPow (exteriorPower.ιMulti X.functionField d
        fun a => (algebraMap (X.presheaf.stalk x) X.functionField (z a))⁻¹ •
          KaehlerDifferential.D k X.functionField
            (algebraMap (X.presheaf.stalk x) X.functionField (z a))) m) := by
  classical
  letI := functionFieldAlgebra sX
  set τ0 : RationalPluriForms sX d m := formPow (exteriorPower.ιMulti X.functionField d
    fun a => (algebraMap (X.presheaf.stalk x) X.functionField (z a))⁻¹ •
      KaehlerDifferential.D k X.functionField
        (algebraMap (X.presheaf.stalk x) X.functionField (z a))) m with hτ0
  have hord := fun E hE => ordForm_formPow_dlog_eq_of_isUnit hd m z hz0 hw S L hL hLx hLz hu E hE
  obtain ⟨a₀, ha₀⟩ := hS
  have hτ00 : τ0 ≠ 0 := by
    intro h0
    have := hord (L a₀) (hLx a₀ ha₀)
    rw [if_pos ⟨a₀, ha₀, rfl⟩] at this
    change (L a₀).ordForm τ0 = _ at this
    rw [h0, Mori.PrimeDivisor.ordForm_zero] at this
    omega
  by_cases hω0 : ω = 0
  · exact ⟨0, by rw [hω0, map_zero, zero_smul]⟩
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hd
  set Bm := Mori.ZTensorPower.basis b (m : ℤ)
  have hrep : ∀ y : RationalPluriForms sX d m, Bm.repr y () • Bm () = y :=
    fun y => MMP.Mori.basis_unit_repr_smul Bm y
  have hτr : Bm.repr τ0 () ≠ 0 := by
    intro h; apply hτ00
    have := hrep τ0
    rw [h, zero_smul] at this
    exact this.symm
  set f := Bm.repr ω () / Bm.repr τ0 () with hf
  have hωf : ω = f • τ0 := by
    have h3 : (Bm.repr ω () • Bm () : ZTensorPower X.functionField
        (⋀[X.functionField]^d Ω[X.functionField⁄k]) (m : ℤ)) =
        f • (Bm.repr τ0 () • Bm () : ZTensorPower X.functionField
          (⋀[X.functionField]^d Ω[X.functionField⁄k]) (m : ℤ)) := by
      rw [smul_smul, hf, div_mul_cancel₀ _ hτr]
    rw [hrep ω, hrep τ0] at h3
    exact h3
  have hf0 : f ≠ 0 := by
    intro h; apply hω0; rw [hωf, h, zero_smul]
  have hpos : ∀ E : Mori.PrimeDivisor X, x ∈ E.support → 0 ≤ X.ord f E.genericPoint := by
    intro E hE
    have h1 := (mem_pluricanonicalSections_of_ne_bot top_ne_bot).1
      ((mem_logPluricanonicalSections sX).1 hω) E ⟨E.genericPoint, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
        trivial⟩ hω0
    rw [hωf, Mori.PrimeDivisor.ordForm_smul_of_topologicalKrullDim_eq E hd hf0 hτ00] at h1
    have h2 := hord E hE
    change E.ordForm τ0 = _ at h2
    rw [h2, DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul] at h1
    split_ifs at h1 with hE'
    · obtain ⟨a, ha, rfl⟩ := hE'
      rw [hL1 a ha, zsmul_eq_mul, mul_one, Int.floor_intCast] at h1
      omega
    · have hB0 : B.coeff E = 0 := by
        by_contra h; exact hE' (hBL E hE h)
      rw [hB0, smul_zero, Int.floor_zero] at h1
      omega
  obtain ⟨g, hg⟩ := MMP.Threefold.Bridges.exists_algebraMap_stalk_eq_of_forall_zero_le_ord x hf0 hpos
  exact ⟨g, by rw [hωf, ← hg]⟩

/-- **The residue of a log form along a coordinate divisor, with unit coordinates.** Let `z₀` be a
local equation at `j(y)` of a prime divisor `L₀` and `j : T ⟶ S` a closed immersion onto `L₀`, and
let `z₁, …, z_d` lie outside the ideal of `L₀` at `j(y)`. The residue of
`g (dlog z₀ ∧ ⋯ ∧ dlog z_d)^{⊗m}` along `T` is `ḡ (dlog z̄₁ ∧ ⋯ ∧ dlog z̄_d)^{⊗m}`, the bars
denoting restriction to `𝒪_{T,y}`. -/
private theorem isPoincareResidue_formPow_dlog_coordinate_of_notMem {k : Type} [Field k]
    {S T : Scheme.{0}} (sS : S ⟶ Spec (.of k)) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [IsIntegral T] (j : T ⟶ S) (L0 : Mori.PrimeDivisor S)
    (hr : Set.range j.base = (L0.support : Set S)) (y' : T) {d : ℕ}
    (z : Fin (d + 1) → S.presheaf.stalk (j y')) (hLy : j y' ∈ L0.support)
    (hz0 : IdealSheafData.stalk L0.idealSheaf (j y') = Ideal.span {z 0})
    (hzu : ∀ i : Fin d, z i.succ ∉ IdealSheafData.stalk L0.idealSheaf (j y'))
    (g : S.presheaf.stalk (j y')) (m : ℕ) :
    letI := functionFieldAlgebra sS
    letI := functionFieldAlgebra (j ≫ sS)
    IsPoincareResidue sS j d m
      (algebraMap _ S.functionField g •
        formPow (exteriorPower.ιMulti S.functionField (d + 1) fun a =>
          (algebraMap _ S.functionField (z a))⁻¹ •
            KaehlerDifferential.D k S.functionField (algebraMap _ S.functionField (z a))) m)
      (algebraMap (T.presheaf.stalk y') T.functionField ((j.stalkMap y').hom g) •
        formPow (exteriorPower.ιMulti T.functionField d fun i =>
          (algebraMap (T.presheaf.stalk y') T.functionField ((j.stalkMap y').hom (z i.succ)))⁻¹ •
            KaehlerDifferential.D k T.functionField (algebraMap (T.presheaf.stalk y')
              T.functionField ((j.stalkMap y').hom (z i.succ)))) m) := by
  letI := functionFieldAlgebra sS
  letI := functionFieldAlgebra (j ≫ sS)
  have h0 : genericPoint T ⤳ y' := (genericPoint_spec T).specializes trivial
  set h' := j.base.hom.map_specializes h0 with hh'
  have hP : j (genericPoint T) = L0.genericPoint := map_genericPoint_eq_of_range_eq j L0 hr
  have key : ∀ (p : S) (hp : p = L0.genericPoint) (h'' : p ⤳ j y'),
      S.ord (algebraMap (S.presheaf.stalk p) S.functionField
        ((S.presheaf.stalkSpecializes h'').hom (z 0))) p = 1 ∧
      ∀ i : Fin d, IsUnit ((S.presheaf.stalkSpecializes h'').hom (z i.succ)) := by
    rintro p rfl h''
    obtain ⟨hm, -⟩ := maximalIdeal_eq_span_and_isUnit_at_genericPoint L0 hLy hz0
    haveI := L0.isDiscreteValuationRing_localRing
    have hirr : Irreducible ((S.presheaf.stalkSpecializes h'').hom (z 0)) :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hm
    have hne : algebraMap (S.presheaf.stalk L0.genericPoint) S.functionField
        ((S.presheaf.stalkSpecializes h'').hom (z 0)) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hirr.ne_zero
    refine ⟨(Scheme.ord_eq_iff L0.coheight_genericPoint hne).mpr (Ring.ordFrac_irreducible hirr),
      fun i => ?_⟩
    by_contra hnu
    apply hzu i
    rw [stalk_idealSheaf_eq_primeOfSpecializes L0 hLy]
    exact (IsLocalRing.mem_maximalIdeal _).2 hnu
  obtain ⟨hord, hunit⟩ := key (j (genericPoint T)) hP h'
  have h1 := isPoincareResidue_formPow_dlog sS j m ((S.presheaf.stalkSpecializes h').hom (z 0))
    (fun i => (S.presheaf.stalkSpecializes h').hom (z i.succ)) hunit hord
  have h2 := IsPoincareResidue.smul_stalk h1 ((S.presheaf.stalkSpecializes h').hom g)
  have hsp : ∀ a, (j.stalkMap (genericPoint T)).hom ((S.presheaf.stalkSpecializes h').hom a) =
      algebraMap (T.presheaf.stalk y') T.functionField ((j.stalkMap y').hom a) :=
    fun a => Scheme.Hom.stalkSpecializes_stalkMap_apply j (genericPoint T) y' h0 a
  have hal : ∀ a, algebraMap (S.presheaf.stalk (j (genericPoint T))) S.functionField
      ((S.presheaf.stalkSpecializes h').hom a) = algebraMap _ S.functionField a :=
    fun a => Mori.algebraMap_stalkSpecializes h' a
  simp only [hsp, hal] at h2
  have e : (fun a => (algebraMap _ S.functionField (z a))⁻¹ •
      KaehlerDifferential.D k S.functionField (algebraMap _ S.functionField (z a))) =
      Fin.cons ((algebraMap _ S.functionField (z 0))⁻¹ •
        KaehlerDifferential.D k S.functionField (algebraMap _ S.functionField (z 0)))
        fun i => (algebraMap _ S.functionField (z i.succ))⁻¹ •
          KaehlerDifferential.D k S.functionField (algebraMap _ S.functionField (z i.succ)) := by
    funext a
    refine Fin.cases ?_ (fun i => ?_) a <;> rfl
  rw [e]
  exact h2

/-- **Generation of the residue field of a monomial valuation over the residues of `R`.** As
`eq_top_of_residueAlong_monomial_mem`, without assuming that the residues of elements of `R` are
constants: an intermediate field of `k(T)` containing the residues of `R` and of all
`z^β / T₀^{⟨α,β⟩}` is all of `k(T)`. -/
private theorem eq_top_of_residueAlong_monomial_mem_of_le {k : Type} [Field k] {Y T : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] (j : T ⟶ Y)
    [IsClosedImmersion j] (P : Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint)
    [Algebra k T.functionField]
    {R : Type*} [CommRing R] [IsDomain R] [Algebra R Y.functionField]
    [IsFractionRing R Y.functionField] {ι : Type*} [Fintype ι] (z : ι → R) (α : ι → ℕ)
    (hv : ∀ r : R, P.divisorialValuation (algebraMap R Y.functionField r) ≤ 1)
    (hz : ∀ i, P.divisorialValuation (algebraMap R Y.functionField (z i)) =
      WithZero.exp (-(α i : ℤ)))
    (hmono : ∀ f : R, f ≠ 0 → ∃ M : ℕ, f ∈ weightedMonomialIdeal z α M ∧
      P.divisorialValuation (algebraMap R Y.functionField f) = WithZero.exp (-(M : ℤ)))
    (T₀ : Y.functionField) (hT : P.divisorialValuation T₀ = WithZero.exp (-1))
    (L : IntermediateField k T.functionField)
    (hres_const : ∀ r : R, residueAlong j P hP (algebraMap R Y.functionField r) ∈ L)
    (hL : ∀ β : ι → ℕ, residueAlong j P hP
      (algebraMap R Y.functionField (∏ i, z i ^ β i) / T₀ ^ (∑ i, α i * β i)) ∈ L) :
    L = ⊤ := by
  classical
  set v := P.divisorialValuation
  have hTM : ∀ M : ℕ, v (T₀ ^ M) = WithZero.exp (-(M : ℤ)) := fun M => by
    rw [map_pow, hT, ← WithZero.exp_nsmul]; congr 1; simp
  -- monomials of weight `M` divided by `T₀^M` have valuation `1`
  have hmon1 : ∀ (M : ℕ) (β : ι → ℕ), ∑ i, α i * β i = M →
      v (algebraMap R Y.functionField (∏ i, z i ^ β i) / T₀ ^ M) = 1 := by
    intro M β hβ
    rw [map_div₀, valuation_prod_pow_eq z α v hz, hβ, hTM, div_self (by simp)]
  -- the residues of the leading forms lie in `L`
  have hform : ∀ (M : ℕ) (s : Finset (ι → ℕ)) (c : (ι → ℕ) → R),
      (∀ β ∈ s, ∑ i, α i * β i = M) →
      residueAlong j P hP (∑ β ∈ s, algebraMap R Y.functionField (c β) *
        (algebraMap R Y.functionField (∏ i, z i ^ β i) / T₀ ^ M)) ∈ L := by
    intro M s c hs
    have hle : ∀ β ∈ s, v (algebraMap R Y.functionField (c β) *
        (algebraMap R Y.functionField (∏ i, z i ^ β i) / T₀ ^ M)) ≤ 1 := by
      intro β hβ
      rw [map_mul, hmon1 M β (hs β hβ), mul_one]; exact hv _
    rw [residueAlong_sum j P hP _ _ hle]
    refine L.sum_mem fun β hβ => ?_
    rw [residueAlong_mul j P hP (hv _) (hmon1 M β (hs β hβ)).le]
    refine L.mul_mem (hres_const _) ?_
    have := hL β
    rwa [hs β hβ] at this
  rw [eq_top_iff]
  intro g _
  obtain ⟨f, hf, rfl⟩ := exists_residueAlong_eq j P hP g
  obtain ⟨M, s, s', c, c', hs, hs', hb, hab⟩ :=
    exists_leadingForms_of_valuation_le_one z α v hv hz hmono T₀ hT hf
  have hale : v (∑ β ∈ s, algebraMap R Y.functionField (c β) *
      (algebraMap R Y.functionField (∏ i, z i ^ β i) / T₀ ^ M)) ≤ 1 :=
    v.map_sum_le fun β hβ => by rw [map_mul, hmon1 M β (hs β hβ), mul_one]; exact hv _
  rw [residueAlong_eq_div_of_sub_lt_one j P hP hf hale hb hab]
  exact L.div_mem (hform M s c hs) (hform M s' c' hs')

/-- **The monomial frame along a log canonical place, with a unit coordinate.** As
`exists_monomialFrame`, for coordinates `z₁, z₂, z₃` at a point `x` of `X'` of which `z₃` is a unit
of weight zero, and without assuming that the residue field of `x` is `k`: there are a uniformizer
`t` of `𝒪_{X,P}` and units `e₁, e₂` with `e₂ = σz₃` and
`dlog σz₁ ∧ dlog σz₂ ∧ dlog σz₃ = dlog t ∧ dlog e₁ ∧ dlog e₂`, and `k(T)` is generated by `ē₁`
over the residues of `𝒪_{X',x}`. -/
private theorem exists_monomialFrame_of_unit {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X X' T : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsIntegral T] (ι : T ⟶ X)
    [IsClosedImmersion ι] (P : Mori.PrimeDivisor X) (hP : ι (genericPoint T) = P.genericPoint)
    (σ : FunctionFieldEquiv sX sX') {x : X'} (z : Fin 3 → X'.presheaf.stalk x)
    (α : Fin 3 → ℕ) (hα2 : α 2 = 0) (hz0 : ∀ a, z a ≠ 0)
    (hle : ∀ r : X'.presheaf.stalk x,
      P.divisorialValuation ((σ.toHom) (algebraMap _ X'.functionField r)) ≤ 1)
    (hlt : ∀ r ∈ IsLocalRing.maximalIdeal (X'.presheaf.stalk x),
      P.divisorialValuation ((σ.toHom) (algebraMap _ X'.functionField r)) < 1)
    (hzv : ∀ a, P.divisorialValuation ((σ.toHom) (algebraMap _ X'.functionField (z a))) =
      WithZero.exp (-(α a : ℤ)))
    (hmono : ∀ f : X'.presheaf.stalk x, f ≠ 0 → ∃ M : ℕ, f ∈ weightedMonomialIdeal z α M ∧
      P.divisorialValuation ((σ.toHom) (algebraMap _ X'.functionField f)) =
        WithZero.exp (-(M : ℤ))) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (ι ≫ sX)
    ∃ (t : X.presheaf.stalk (ι (genericPoint T))) (e : Fin 2 → X.presheaf.stalk (ι (genericPoint T))),
      (∀ i, IsUnit (e i)) ∧
      X.ord (algebraMap _ X.functionField t) (ι (genericPoint T)) = 1 ∧
      exteriorPower.ιMulti X.functionField 3 (fun a =>
          ((σ.toHom) (algebraMap _ X'.functionField (z a)))⁻¹ •
            KaehlerDifferential.D k X.functionField ((σ.toHom) (algebraMap _ X'.functionField (z a)))) =
        exteriorPower.ιMulti X.functionField 3 (Fin.cons
          ((algebraMap _ X.functionField t)⁻¹ • KaehlerDifferential.D k _ (algebraMap _ _ t))
          fun i => (algebraMap _ X.functionField (e i))⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ _ (e i))) ∧
      algebraMap _ X.functionField (e 1) = (σ.toHom) (algebraMap _ X'.functionField (z 2)) ∧
      IntermediateField.adjoin k (Set.range (fun r : X'.presheaf.stalk x =>
        residueAlong ι P hP ((σ.toHom) (algebraMap _ X'.functionField r))) ∪
          {(ι.stalkMap (genericPoint T)).hom (e 0)}) = ⊤ := by
  classical
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (ι ≫ sX)
  letI := functionFieldAlgebra sX'
  set v := P.divisorialValuation with hvdef
  letI algR : Algebra (X'.presheaf.stalk x) X.functionField :=
    ((σ.toHom : X'.functionField →ₐ[k] X.functionField).toRingHom.comp
      (algebraMap (X'.presheaf.stalk x) X'.functionField)).toAlgebra
  have halgR : ∀ r : (X'.presheaf.stalk x), algebraMap (X'.presheaf.stalk x) X.functionField r =
      (σ.toHom) (algebraMap (X'.presheaf.stalk x) X'.functionField r) := fun _ => rfl
  haveI : IsFractionRing (X'.presheaf.stalk x) X.functionField := by
    let e : X'.functionField ≃ₐ[(X'.presheaf.stalk x)] X.functionField :=
      { σ.toRingEquiv with commutes' := fun _ => rfl }
    exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors (X'.presheaf.stalk x)) e
  -- primitive weights and a unimodular change of monomials
  have hT1 : ∃ g : X.functionField, v g = WithZero.exp (-1) := by
    haveI := P.isDiscreteValuationRing_localRing
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
    have h0 : algebraMap P.localRing X.functionField ϖ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
    refine ⟨algebraMap P.localRing X.functionField ϖ, ?_⟩
    rw [hvdef, P.divisorialValuation_eq_exp_neg_ord h0,
      (Scheme.ord_eq_iff P.coheight_genericPoint h0).mpr (Ring.ordFrac_irreducible hϖ)]
  have hgcd := gcd_eq_one_of_monomial (R := X'.presheaf.stalk x) (K := X.functionField) z α v
    (fun r => by rw [halgR]; exact hle r) (fun a => by rw [halgR]; exact hzv a)
    (fun f hf => by
      obtain ⟨M, hM, hMv⟩ := hmono f hf
      exact ⟨M, hM, by rw [halgR]; exact hMv⟩) hT1
  have hgcd2 : Int.gcd (α 0 : ℤ) (α 1 : ℤ) = 1 := by
    rw [hα2] at hgcd; simpa using hgcd
  obtain ⟨M2, hM2det, hM2α⟩ := exists_det_eq_one_mulVec_eq (α 0) (α 1)
  rw [hgcd2] at hM2α
  have f1 : M2 0 0 * α 0 + M2 0 1 * α 1 = 1 := by
    have := congrFun hM2α 0; simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have f2 : M2 1 0 * α 0 + M2 1 1 * α 1 = 0 := by
    have := congrFun hM2α 1; simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  set M : Matrix (Fin 3) (Fin 3) ℤ := !![M2 0 0, M2 0 1, 0; M2 1 0, M2 1 1, 0; 0, 0, 1] with hMdef
  have hMdet : M.det = 1 := by
    rw [Matrix.det_fin_three]
    rw [Matrix.det_fin_two] at hM2det
    simp [M]
    linear_combination hM2det
  have hMα : M.mulVec ![(α 0 : ℤ), α 1, α 2] = ![1, 0, 0] := by
    rw [hα2]
    ext i; fin_cases i
    · simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; linear_combination f1
    · simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; linear_combination f2
    · simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hz0' : ∀ a, (σ.toHom) (algebraMap (X'.presheaf.stalk x) X'.functionField (z a)) ≠ 0 := fun a =>
    (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hz0 a))
  set zU : Fin 3 → (X.functionField)ˣ := fun a => Units.mk0 _ (hz0' a) with hzU
  set sU : Fin 3 → (X.functionField)ˣ := fun a => ∏ b, zU b ^ M a b with hsU
  have hαvec : (![(α 0 : ℤ), α 1, α 2] : Fin 3 → ℤ) = fun i => (α i : ℤ) := by
    funext i; fin_cases i <;> rfl
  have hsv : ∀ a, v (sU a : X.functionField) =
      WithZero.exp (-((![(1 : ℤ), 0, 0] : Fin 3 → ℤ) a)) := by
    intro a
    rw [hsU, valuation_prod_zpow_eq v zU (fun i => (α i : ℤ)) (fun i => hzv i), ← hMα, hαvec]
    rfl
  have hs0 : v (sU 0 : X.functionField) = WithZero.exp (-1) := by rw [hsv]; rfl
  have hs1 : ∀ a, a ≠ 0 → v (sU a : X.functionField) = 1 := by
    intro a ha
    rw [hsv]
    fin_cases a
    · exact absurd rfl ha
    · rfl
    · rfl
  -- the uniformizer `t = s₀` and the units `e = (s₁, s₂)` in `𝒪_{X,P}`
  obtain ⟨t, ht⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one P hP (hs0.le.trans
    (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega))
  have he : ∀ i : Fin 2, ∃ c : X.presheaf.stalk (ι (genericPoint T)),
      algebraMap _ X.functionField c = (sU i.succ : X.functionField) := fun i =>
    exists_algebraMap_eq_of_divisorialValuation_le_one P hP (hs1 _ (Fin.succ_ne_zero i)).le
  choose e he using he
  have heu : ∀ i, IsUnit (e i) := by
    intro i
    by_contra hnu
    have hm := (mem_maximalIdeal_iff_divisorialValuation_lt_one P hP (e i)).1
      ((IsLocalRing.mem_maximalIdeal _).2 hnu)
    rw [he, hs1 _ (Fin.succ_ne_zero i)] at hm
    exact lt_irrefl _ hm
  have ht1 : X.ord (algebraMap _ X.functionField t) (ι (genericPoint T)) = 1 := by
    have h0 : algebraMap _ X.functionField t ≠ 0 := by rw [ht]; exact (sU 0).ne_zero
    have h := P.divisorialValuation_eq_exp_neg_ord h0
    rw [← hvdef, ht, hs0, WithZero.exp_inj, neg_inj] at h
    rw [ht, hP]
    exact h.symm
  have hsU2 : sU 2 = zU 2 := by
    rw [hsU]
    simp [Fin.prod_univ_three, M]
  refine ⟨t, e, heu, ht1, ?_, ?_, ?_⟩
  · -- the `dlog`-forms agree, `det M = 1`
    have h1 := ιMulti_dlogHom_monomial k X.functionField zU M
    rw [hMdet, Int.cast_one, one_smul] at h1
    have hL : (fun a => ((σ.toHom) (algebraMap _ X'.functionField (z a)))⁻¹ •
        KaehlerDifferential.D k X.functionField ((σ.toHom) (algebraMap _ X'.functionField (z a)))) =
        fun b => Multiplicative.toAdd (dlogHom k X.functionField (zU b)) := rfl
    have hR : (Fin.cons ((algebraMap _ X.functionField t)⁻¹ •
          KaehlerDifferential.D k _ (algebraMap _ _ t))
          fun i => (algebraMap _ X.functionField (e i))⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ _ (e i)) : Fin 3 → Ω[X.functionField⁄k]) =
        fun a => Multiplicative.toAdd (dlogHom k X.functionField (∏ b, zU b ^ M a b)) := by
      funext a
      refine Fin.cases ?_ (fun i => ?_) a
      · simp only [Fin.cons_zero, ht]; rfl
      · simp only [Fin.cons_succ, he]; rfl
    rw [hL, hR, h1]
  · rw [he 1]
    change (sU (1 : Fin 2).succ : X.functionField) = _
    rw [show (1 : Fin 2).succ = 2 from rfl, hsU2]
    rfl
  · -- the residues `ē₁, ē₂` generate `k(T)`
    have hvst : ∀ a : X.presheaf.stalk (ι (genericPoint T)),
        v (algebraMap _ X.functionField a) ≤ 1 := by
      intro a
      have : ∃ c' : P.localRing, algebraMap P.localRing X.functionField c' =
          algebraMap _ X.functionField a := by
        revert a; rw [hP]; intro a; exact ⟨a, rfl⟩
      obtain ⟨c', hc'⟩ := this
      rw [← hc']
      exact (P.divisorialValuation_le_one_iff _).2 ⟨c', rfl⟩
    have hinv : M⁻¹.mulVec ![1, 0, 0] = ![(α 0 : ℤ), α 1, α 2] := by
      rw [← hMα, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (by rw [hMdet]; exact isUnit_one),
        Matrix.one_mulVec]
    have hcolM : ∀ b, M⁻¹ b 0 = (α b : ℤ) := by
      intro b
      have := congrFun hinv b
      rw [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
      simp at this
      rw [this, hαvec]
    have hcol : ∀ u : Fin 3 → ℤ, Matrix.vecMul u M⁻¹ 0 = ∑ i, (α i : ℤ) * u i := by
      intro u
      rw [Matrix.vecMul, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcolM, mul_comm]
    have hrow : ∑ i, (α i : ℤ) * M 0 i = 1 := by
      have := congrFun hMα 0
      rw [Matrix.mulVec, dotProduct, hαvec] at this
      exact (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans this
    refine eq_top_of_residueAlong_monomial_mem_of_le ι P hP (R := X'.presheaf.stalk x) z α
      (fun r => by rw [halgR]; exact hle r) (fun a => by rw [halgR]; exact hzv a)
      (fun f hf => by
        obtain ⟨M', hM', hMv⟩ := hmono f hf
        exact ⟨M', hM', by rw [halgR]; exact hMv⟩)
      (sU 0 : X.functionField) hs0 _
      (fun r => IntermediateField.subset_adjoin _ _ (Or.inl ⟨r, by rw [halgR]⟩)) fun β => ?_
    have h := residueAlong_monomial_mem_adjoin (k := k) ι P hP zU α M
      (by rw [hMdet]; exact isUnit_one) 0 hcol hrow (fun a ha => hs1 a ha) β
    have heq : algebraMap (X'.presheaf.stalk x) X.functionField (∏ i, z i ^ β i) =
        ∏ i, ((zU i : X.functionField)) ^ β i := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_pow, halgR]
      rfl
    rw [heq]
    refine (IntermediateField.adjoin_le_iff.2 ?_) h
    rintro _ ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 ha
    change residueAlong ι P hP (sU i.succ : X.functionField) ∈ _
    fin_cases i
    · change residueAlong ι P hP (sU (0 : Fin 2).succ : X.functionField) ∈ _
      rw [← he 0, residueAlong_algebraMap]
      exact IntermediateField.subset_adjoin _ _ (Or.inr rfl)
    · change residueAlong ι P hP (sU 2 : X.functionField) ∈ _
      rw [hsU2]
      exact IntermediateField.subset_adjoin _ _ (Or.inl ⟨z 2, rfl⟩)

open KaehlerDifferential in
/-- **Completing a regular system of parameters to a frame of differentials.** Let `O` be a
noetherian local `k`-algebra, formally smooth and essentially of finite type over a perfect field
`k`, and `t₁, …, t_d` a regular system of parameters. There are `r₁, …, r_e ∈ O` such that
`dt₁, …, dt_d, dr₁, …, dr_e` is a basis of `Ω_{O/k}`. -/
private theorem exists_bijective_linearCombination_D_sumElim {k O : Type*} [Field k]
    [PerfectField k] [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [Algebra k O]
    [Algebra.FormallySmooth k O] [Algebra.EssFiniteType k O] {d : ℕ} (t : Fin d → O)
    (hspan : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal O)
    (hdim : ringKrullDim O = d) :
    ∃ (e : ℕ) (r : Fin e → O), Function.Bijective (Finsupp.linearCombination O
      (fun i => KaehlerDifferential.D k O (Sum.elim t r i))) := by
  classical
  have : Algebra.EssFiniteType k (IsLocalRing.ResidueField O) :=
    Algebra.EssFiniteType.of_surjective
      (IsScalarTower.toAlgHom k O (IsLocalRing.ResidueField O)) IsLocalRing.residue_surjective
  have : Algebra.FormallySmooth k (IsLocalRing.ResidueField O) :=
    Algebra.FormallySmooth.of_perfectField
  obtain ⟨ht0, hli, -⟩ := MMP.Flips.ResolutionInputs.cotangent_basis_of_regular t hspan hdim
  have hli' := MMP.Flips.ResolutionInputs.linearIndependent_tmul_D k t ht0 hli
  have : Module.Projective O Ω[O⁄k] := ((Algebra.formallySmooth_iff _ _).mp ‹_›).1
  obtain ⟨e, v, hvS, hvli, hvsp⟩ := MMP.Flips.ResolutionInputs.exists_sumElim_basis _ hli' _
    (MMP.Flips.ResolutionInputs.span_tmul_range_D k)
  choose r hr using hvS
  have hu : (TensorProduct.mk O (IsLocalRing.ResidueField O) Ω[O⁄k] 1 ∘ fun i =>
      KaehlerDifferential.D k O (Sum.elim t r i)) = Sum.elim (fun i =>
        (1 : IsLocalRing.ResidueField O) ⊗ₜ KaehlerDifferential.D k O (t i)) v := by
    funext i
    cases i with
    | inl i => rfl
    | inr j => exact hr j
  refine ⟨e, r, ?_⟩
  apply Module.IsLocalRing.linearCombination_bijective_of_flat
  rw [hu]
  refine ⟨hvli, ?_⟩
  rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
  exact top_le_iff.mp hvsp

/-- **A unit completing two snc coordinates to a frame.** Let `x` be a point of the smooth locus
of an integral `k`-scheme of dimension three, over a perfect field, whose local ring has a regular
system of parameters `z₁, z₂`. There is a unit `v` of `𝒪_{X,x}` such that `dz₁, dz₂, dv` span
`Ω_{𝒪_{X,x}/k}`. -/
private theorem exists_isUnit_span_D_eq_top_of_mem_smoothLocus {k : Type} [Field k]
    [PerfectField k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [LocallyOfFiniteType sX] (hd : topologicalKrullDim X = (3 : ℕ))
    {x : X} (hsm : x ∈ Mori.smoothLocus sX) (z : Fin 2 → X.presheaf.stalk x)
    (hz : IsRegularSystemOfParameters z) :
    letI := stalkAlgebra sX x
    ∃ v : X.presheaf.stalk x, IsUnit v ∧ Submodule.span (X.presheaf.stalk x)
      (Set.range fun a : Fin 3 => KaehlerDifferential.D k (X.presheaf.stalk x)
        (![z 0, z 1, v] a)) = ⊤ := by
  classical
  obtain ⟨U, hU, hyU⟩ : ∃ U : X.Opens, Smooth (U.ι ≫ sX) ∧ x ∈ U := by
    obtain ⟨U, hU, hyU⟩ := TopologicalSpace.Opens.mem_sSup.1 hsm
    exact ⟨U, hU, hyU⟩
  letI : Algebra k ((U : Scheme).presheaf.stalk ⟨x, hyU⟩) := stalkAlgebra (U.ι ≫ sX) ⟨x, hyU⟩
  letI : Algebra ((U : Scheme).presheaf.stalk ⟨x, hyU⟩) (X.presheaf.stalk x) :=
    MMP.Positivity.opensStalkIsoAlgebra U ⟨x, hyU⟩
  letI := stalkAlgebra sX x
  haveI : IsScalarTower k ((U : Scheme).presheaf.stalk ⟨x, hyU⟩) (X.presheaf.stalk x) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have h : (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
          X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top _) =
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ sX).appTop ≫
          (U : Scheme).presheaf.germ ⊤ ⟨x, hyU⟩ (TopologicalSpace.Opens.mem_top _)) ≫
          (U.stalkIso ⟨x, hyU⟩).hom := by
      simp only [Category.assoc, Scheme.Opens.germ_stalkIso_hom, Scheme.Hom.comp_appTop]
      congr 2
      exact (X.presheaf.germ_res (homOfLE le_top) _ _).symm
    exact congrArg CommRingCat.Hom.hom h
  have hbij : Function.Bijective (algebraMap ((U : Scheme).presheaf.stalk ⟨x, hyU⟩)
      (X.presheaf.stalk x)) :=
    ConcreteCategory.bijective_of_isIso (U.stalkIso ⟨x, hyU⟩).hom
  set eU := AlgEquiv.ofBijective (Algebra.ofId ((U : Scheme).presheaf.stalk ⟨x, hyU⟩)
    (X.presheaf.stalk x)) hbij
  obtain ⟨h1, -, h3⟩ := MMP.Flips.ResolutionInputs.stalk_facts (U.ι ≫ sX) ⟨x, hyU⟩
  haveI := h1
  haveI := h3
  haveI : Algebra.FormallyEtale ((U : Scheme).presheaf.stalk ⟨x, hyU⟩) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_equiv eU
  haveI : Algebra.FormallySmooth k (X.presheaf.stalk x) :=
    Algebra.FormallySmooth.comp k ((U : Scheme).presheaf.stalk ⟨x, hyU⟩) _
  haveI : Algebra.EssFiniteType ((U : Scheme).presheaf.stalk ⟨x, hyU⟩) (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.of_surjective (Algebra.ofId _ _) hbij.2
  haveI : Algebra.EssFiniteType k (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.comp k ((U : Scheme).presheaf.stalk ⟨x, hyU⟩) _
  have hdim : ringKrullDim (X.presheaf.stalk x) = (2 : ℕ) := hz.2
  obtain ⟨e, r, hr⟩ := exists_bijective_linearCombination_D_sumElim (k := k) z hz.1 hdim
  -- the rank count `2 + e = 3`, through the function field
  set b := Module.Basis.ofRepr (LinearEquiv.ofBijective _ hr).symm with hb
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_stalk_functionField sX x
  haveI : Algebra.FormallyEtale (X.presheaf.stalk x) X.functionField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (X.presheaf.stalk x))
  have he : e = 1 := by
    have hK := (b.baseChange X.functionField).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (X.presheaf.stalk x)
        X.functionField)
    have hf1 := Module.finrank_eq_card_basis hK
    have := essFiniteType_functionField (sX := sX)
    have hf2 : Module.finrank X.functionField Ω[X.functionField⁄k] = 3 :=
      (finrank_kaehlerDifferential_eq_trdeg k X.functionField).trans
        (toNat_trdeg_functionField_of_topologicalKrullDim_eq hd)
    rw [hf2, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hf1
    omega
  subst he
  have hspan : Submodule.span (X.presheaf.stalk x)
      (Set.range fun i => KaehlerDifferential.D k (X.presheaf.stalk x) (Sum.elim z r i)) = ⊤ := by
    rw [← Finsupp.range_linearCombination, LinearMap.range_eq_top]
    exact hr.2
  have hrange : ∀ v : X.presheaf.stalk x, KaehlerDifferential.D k (X.presheaf.stalk x) v =
      KaehlerDifferential.D k (X.presheaf.stalk x) (r 0) →
      Set.range (fun a : Fin 3 => KaehlerDifferential.D k (X.presheaf.stalk x)
        (![z 0, z 1, v] a)) =
      Set.range fun i => KaehlerDifferential.D k (X.presheaf.stalk x) (Sum.elim z r i) := by
    intro v hv
    ext ω
    simp only [Set.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      fin_cases a
      · exact ⟨Sum.inl 0, rfl⟩
      · exact ⟨Sum.inl 1, rfl⟩
      · exact ⟨Sum.inr 0, by simp [hv]⟩
    · rintro ⟨i, rfl⟩
      rcases i with i | i
      · fin_cases i
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
      · fin_cases i
        exact ⟨2, by simp [hv]⟩
  by_cases hu : IsUnit (r 0)
  · exact ⟨r 0, hu, by rw [hrange (r 0) rfl]; exact hspan⟩
  · refine ⟨r 0 + 1, ?_, by rw [hrange (r 0 + 1) (by simp)]; exact hspan⟩
    have hm : r 0 ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
      (IsLocalRing.mem_maximalIdeal _).2 hu
    by_contra h
    have h2 : r 0 + 1 ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
      (IsLocalRing.mem_maximalIdeal _).2 h
    have : (1 : X.presheaf.stalk x) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
      have := Ideal.sub_mem _ h2 hm
      rwa [add_sub_cancel_left] at this
    exact (IsLocalRing.mem_maximalIdeal _).1 this isUnit_one

open KaehlerDifferential in
/-- **Spanning differentials pass to quotients.** If `φ : A → B` is a surjective `k`-algebra map
and the `da_i` span `Ω_{A/k}`, then the `dφ(a_i)` span `Ω_{B/k}`. -/
private theorem span_D_eq_top_of_surjective {k A B : Type*} [CommRing k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] (φ : A →ₐ[k] B) (hφ : Function.Surjective φ)
    {ι : Type*} (a : ι → A)
    (h : Submodule.span A (Set.range fun i => KaehlerDifferential.D k A (a i)) = ⊤) :
    Submodule.span B (Set.range fun i => KaehlerDifferential.D k B (φ (a i))) = ⊤ := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  set N := Submodule.span B (Set.range fun i => KaehlerDifferential.D k B (φ (a i)))
  have hmap : ∀ ω ∈ Submodule.span A (Set.range fun i => KaehlerDifferential.D k A (a i)),
      KaehlerDifferential.map k k A B ω ∈ N := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rw [KaehlerDifferential.map_D]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add y y' _ _ h h' => rw [map_add]; exact N.add_mem h h'
    | smul r y _ h =>
      rw [LinearMap.map_smul_of_tower, ← algebraMap_smul B r]
      exact N.smul_mem _ h
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  obtain ⟨c, rfl⟩ := hφ b
  have := hmap _ (h ▸ Submodule.mem_top (x := KaehlerDifferential.D k A c))
  rwa [KaehlerDifferential.map_D] at this

/-- Forms built from `dlog`s do not depend on the structure morphism beyond equality, nor on the
presentation of the family of functions. -/
private theorem heq_smul_formPow_ιMulti_dlog_of_eq {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] {s s' : X ⟶ Spec (.of k)} (hs : s = s') {d : ℕ} (c : X.functionField)
    (f g : Fin d → X.functionField) (hfg : ∀ i, f i = g i) (m : ℕ) :
    HEq (letI := functionFieldAlgebra s;
      (c • (show RationalPluriForms s d m from formPow (exteriorPower.ιMulti X.functionField d
        fun i => (f i)⁻¹ • KaehlerDifferential.D k X.functionField (f i)) m)))
      (letI := functionFieldAlgebra s';
        (c • (show RationalPluriForms s' d m from formPow (exteriorPower.ιMulti X.functionField d
          fun i => (g i)⁻¹ • KaehlerDifferential.D k X.functionField (g i)) m))) := by
  subst hs
  obtain rfl : f = g := funext hfg
  rfl

/-- **Iterated residues along a flag of length two.** If `ρ₁` is the residue of `τ` along the
first step and `ρ₂` that of `ρ₁` along the second, then `ρ₂` is the iterated residue of `τ` along
the flag. -/
private theorem isIteratedResidueRec_step_step {k : Type} [Field k] {X T₁ T₂ : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral T₁] [IsLocallyNoetherian T₁] [IsIntegral T₂]
    {B : QDivisor X} (hpair : Mori.IsPair sX B) {ι₁ : T₁ ⟶ X} {B₁ : QDivisor T₁}
    (h₁ : IsAdjunctionStep (𝟙 X ≫ sX) B ι₁ B₁) {ι₂ : T₂ ⟶ T₁} {B₂ : QDivisor T₂}
    (h₂ : IsAdjunctionStep ((ι₁ ≫ 𝟙 X) ≫ sX) B₁ ι₂ B₂) {e m : ℕ}
    {τ : RationalPluriForms sX (e + 2) m} {ρ₁ : RationalPluriForms (ι₁ ≫ sX) (e + 1) m}
    {ρ₂ : RationalPluriForms (ι₂ ≫ ι₁ ≫ sX) e m}
    (r1 : IsPoincareResidue sX ι₁ (e + 1) m τ ρ₁) (r2 : IsPoincareResidue (ι₁ ≫ sX) ι₂ e m ρ₁ ρ₂)
    (ρ : @RationalPluriForms k _ T₂ ((ι₂ ≫ ι₁ ≫ 𝟙 X) ≫ sX)
      (StratumAdjunctionData.step (.step (.refl hpair) ι₁ B₁ h₁) ι₂ B₂ h₂).isIntegral_stratum e m)
    (hρ : HEq ρ ρ₂) :
    IsIteratedResidueRec τ (.step (.step (.refl hpair) ι₁ B₁ h₁) ι₂ B₂ h₂) e ρ := by
  obtain ⟨ρ₀₀, hρ₀₀⟩ := exists_heq_rationalPluriForms (Category.id_comp sX).symm τ
  obtain ⟨ρ₀', hρ₀'⟩ := exists_heq_rationalPluriForms (s := ι₁ ≫ sX) (s' := ι₁ ≫ 𝟙 X ≫ sX)
    (by rw [Category.id_comp]) ρ₁
  obtain ⟨ρ₀, hρ₀⟩ := exists_heq_rationalPluriForms (s := ι₁ ≫ sX) (s' := (ι₁ ≫ 𝟙 X) ≫ sX)
    (by rw [Category.comp_id]) ρ₁
  obtain ⟨ρ', hρ'⟩ := exists_heq_rationalPluriForms (s := ι₂ ≫ ι₁ ≫ sX)
    (s' := ι₂ ≫ (ι₁ ≫ 𝟙 X) ≫ sX) (by rw [Category.comp_id]) ρ₂
  exact ⟨ρ₀, ⟨ρ₀₀, ⟨rfl, hρ₀₀.symm⟩, ρ₀',
    IsPoincareResidue.congr_structure (Category.id_comp sX).symm r1 hρ₀₀ hρ₀',
    hρ₀.symm.trans hρ₀'⟩, ρ',
    IsPoincareResidue.congr_structure (by rw [Category.comp_id]) r2 hρ₀ hρ', hρ.trans hρ'⟩

open Polynomial IsDedekindDomain.HeightOneSpectrum in
/-- **Residues of the `X`-adic valuation are constants.** A rational function over `K` without
pole at `X = 0` is congruent to a constant modulo the maximal ideal of the `X`-adic valuation. -/
private theorem exists_valuation_sub_algebraMap_lt_one {K : Type*} [Field K] (F : RatFunc K)
    (hF : (idealX K).valuation (RatFunc K) F ≤ 1) :
    ∃ c : K, (idealX K).valuation (RatFunc K) (F - algebraMap K (RatFunc K) c) < 1 := by
  set v := (idealX K).valuation (RatFunc K) with hv
  have hq0 : F.denom ≠ 0 := F.denom_ne_zero
  have hF' : F = algebraMap K[X] (RatFunc K) F.num / algebraMap K[X] (RatFunc K) F.denom :=
    (RatFunc.num_div_denom F).symm
  have hX : ¬ Polynomial.X ∣ F.denom := by
    intro hd
    have hcop := RatFunc.isCoprime_num_denom F
    have hnX : ¬ Polynomial.X ∣ F.num := fun hn => Polynomial.not_isUnit_X (hcop.isUnit_of_dvd' hn hd)
    have h1 : v (algebraMap _ _ F.num) = 1 := by
      rw [hv, valuation_of_algebraMap, intValuation_eq_one_iff_mem_primeCompl]
      simpa [Ideal.primeCompl, Ideal.mem_span_singleton] using hnX
    have h2 : v (algebraMap _ _ F.denom) < 1 := by
      rw [hv, valuation_of_algebraMap, intValuation_lt_one_iff_mem, idealX_span,
        Ideal.mem_span_singleton]
      exact hd
    have h20 : v (algebraMap _ _ F.denom) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hq0)
    rw [hF', map_div₀, h1] at hF
    have h3 : (1 : ℤᵐ⁰) ≤ v (algebraMap _ _ F.denom) := by
      have h4 := mul_le_mul' hF (le_refl (v (algebraMap _ _ F.denom)))
      rwa [div_mul_cancel₀ _ h20, one_mul] at h4
    exact absurd h2 (not_lt.2 h3)
  have hden1 : v (algebraMap _ _ F.denom) = 1 := by
    rw [hv, valuation_of_algebraMap, intValuation_eq_one_iff_mem_primeCompl]
    simpa [Ideal.primeCompl, Ideal.mem_span_singleton] using hX
  have hd0 : F.denom.coeff 0 ≠ 0 := fun h => hX (X_dvd_iff.2 h)
  refine ⟨F.num.coeff 0 / F.denom.coeff 0, ?_⟩
  have hden0 : algebraMap K[X] (RatFunc K) F.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hq0
  have e : F - algebraMap K (RatFunc K) (F.num.coeff 0 / F.denom.coeff 0) =
      algebraMap K[X] (RatFunc K) (F.num - C (F.num.coeff 0 / F.denom.coeff 0) * F.denom) /
        algebraMap K[X] (RatFunc K) F.denom := by
    have hFd : F * algebraMap K[X] (RatFunc K) F.denom = algebraMap K[X] (RatFunc K) F.num := by
      nth_rewrite 1 [hF']
      rw [div_mul_cancel₀ _ hden0]
    rw [eq_div_iff hden0, sub_mul, hFd, map_sub, map_mul, ← Polynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K)]
  rw [e, map_div₀, hden1, div_one, hv, valuation_of_algebraMap, intValuation_lt_one_iff_mem,
    idealX_span, Ideal.mem_span_singleton, X_dvd_iff, coeff_sub, coeff_C_mul,
    div_mul_cancel₀ _ hd0, sub_self]

open Polynomial IsDedekindDomain.HeightOneSpectrum in
/-- The valuation ring of the `X`-adic valuation of `K(X)` is the localization `K[X]_{(X)}`. -/
private theorem exists_algHom_range_eq_valuation_le_one (K : Type) [Field K] :
    ∃ φ : Localization.AtPrime (Polynomial.idealX K).asIdeal →ₐ[K] RatFunc K,
      ∀ F : RatFunc K, (Polynomial.idealX K).valuation (RatFunc K) F ≤ 1 ↔ F ∈ φ.range := by
  set p := (Polynomial.idealX K).asIdeal with hp
  set v := (Polynomial.idealX K).valuation (RatFunc K) with hv
  have hunit : ∀ y : p.primeCompl, IsUnit (algebraMap K[X] (RatFunc K) y) := fun y =>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (fun h => y.2 (by
      rw [h]; exact p.zero_mem)))
  let φ0 : Localization.AtPrime p →+* RatFunc K := IsLocalization.lift hunit
  have hφ0 : ∀ a : K[X], φ0 (algebraMap K[X] _ a) = algebraMap K[X] (RatFunc K) a :=
    fun a => IsLocalization.lift_eq hunit a
  let φ : Localization.AtPrime p →ₐ[K] RatFunc K :=
    { φ0 with
      commutes' := fun c => by
        change φ0 (algebraMap K (Localization.AtPrime p) c) = _
        rw [IsScalarTower.algebraMap_apply K K[X] (Localization.AtPrime p), hφ0,
          ← IsScalarTower.algebraMap_apply] }
  refine ⟨φ, fun F => ⟨fun hF => ?_, ?_⟩⟩
  · have hq0 : F.denom ≠ 0 := F.denom_ne_zero
    have hq0' : algebraMap K[X] (RatFunc K) F.denom ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hq0
    have hF' : F = algebraMap K[X] (RatFunc K) F.num / algebraMap K[X] (RatFunc K) F.denom :=
      (RatFunc.num_div_denom F).symm
    have hX : ¬ Polynomial.X ∣ F.denom := by
      intro hd
      have hcop := RatFunc.isCoprime_num_denom F
      have hnX : ¬ Polynomial.X ∣ F.num := fun hn =>
        Polynomial.not_isUnit_X (hcop.isUnit_of_dvd' hn hd)
      have h1 : v (algebraMap _ _ F.num) = 1 := by
        rw [hv, valuation_of_algebraMap, intValuation_eq_one_iff_mem_primeCompl]
        simpa [Ideal.primeCompl, Ideal.mem_span_singleton] using hnX
      have h2 : v (algebraMap _ _ F.denom) < 1 := by
        rw [hv, valuation_of_algebraMap, intValuation_lt_one_iff_mem, idealX_span,
          Ideal.mem_span_singleton]
        exact hd
      have h20 : v (algebraMap _ _ F.denom) ≠ 0 := (Valuation.ne_zero_iff _).2 hq0'
      rw [hF', map_div₀, h1] at hF
      have h3 : (1 : ℤᵐ⁰) ≤ v (algebraMap _ _ F.denom) := by
        have h4 := mul_le_mul' hF (le_refl (v (algebraMap _ _ F.denom)))
        rwa [div_mul_cancel₀ _ h20, one_mul] at h4
      exact absurd h2 (not_lt.2 h3)
    have hmem : F.denom ∈ p.primeCompl := by
      simpa [p, Ideal.primeCompl, idealX_span, Ideal.mem_span_singleton] using hX
    refine ⟨IsLocalization.mk' (Localization.AtPrime p) F.num ⟨F.denom, hmem⟩, ?_⟩
    change φ0 _ = F
    rw [IsLocalization.lift_mk'_spec]
    change _ = algebraMap K[X] (RatFunc K) F.denom * F
    rw [mul_comm]
    exact (div_eq_iff hq0').1 hF'.symm
  · rintro ⟨s, rfl⟩
    obtain ⟨⟨a, b⟩, hs⟩ := IsLocalization.mk'_surjective p.primeCompl s
    subst hs
    change v (φ0 _) ≤ 1
    have hy : algebraMap K[X] (RatFunc K) a =
        algebraMap K[X] (RatFunc K) b * φ0 (IsLocalization.mk' (Localization.AtPrime p) a b) :=
      (IsLocalization.lift_mk'_spec _ _ _ _).1 rfl
    have hb : v (algebraMap K[X] (RatFunc K) (b : K[X])) = 1 := by
      rw [hv, valuation_of_algebraMap]
      exact (intValuation_eq_one_iff_mem_primeCompl _ _).2 b.2
    have h1 := congrArg v hy
    rw [map_mul, hb, one_mul] at h1
    rw [← h1, hv, valuation_of_algebraMap]
    exact intValuation_le_one _ _

/-- **The `e`-adic valuation of a simple transcendental extension.** Let `L = K(e)` with `e`
transcendental over `K`, `K` essentially of finite type over `k`. The `e`-adic valuation `ν` of
`L` is trivial on `K`, takes the value `exp (-1)` at `e`, every element of its valuation ring is
congruent to an element of `K` modulo its maximal ideal, and its valuation ring
`K[e]_{(e)}` is the image of a `k`-algebra essentially of finite type. -/
private theorem exists_valuation_of_transcendental {k K L : Type} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra.EssFiniteType k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    {e : L} (he : Transcendental K e) (hgen : IntermediateField.adjoin K {e} = ⊤) :
    ∃ ν : Valuation L ℤᵐ⁰, (∀ c : K, c ≠ 0 → ν (algebraMap K L c) = 1) ∧
      ν e = WithZero.exp (-1) ∧ (∀ f : L, ν f ≤ 1 → ∃ c : K, ν (f - algebraMap K L c) < 1) ∧
      ∃ (S : Type) (_ : CommRing S) (_ : Algebra k S) (_ : Algebra.EssFiniteType k S)
        (ψ : S →ₐ[k] L), ∀ g, ν g ≤ 1 ↔ g ∈ ψ.range := by
  let φ : RatFunc K ≃ₐ[K] L := (RatFunc.algEquivOfTranscendental e he).trans
    ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv)
  have hφX : φ RatFunc.X = e := by simp [φ]
  obtain ⟨φS, hφS⟩ := exists_algHom_range_eq_valuation_le_one K
  haveI : Algebra.EssFiniteType K (Localization.AtPrime (Polynomial.idealX K).asIdeal) :=
    Algebra.EssFiniteType.comp K (Polynomial K) _
  haveI : Algebra.EssFiniteType k (Localization.AtPrime (Polynomial.idealX K).asIdeal) :=
    Algebra.EssFiniteType.comp k K _
  refine ⟨((Polynomial.idealX K).valuation (RatFunc K)).comap φ.symm.toRingEquiv.toRingHom,
    ?_, ?_, ?_, _, inferInstance, inferInstance, inferInstance,
    ((φ.toAlgHom.comp φS).restrictScalars k), fun g => ?_⟩
  · intro c hc
    simp only [Valuation.comap_apply]
    rw [show φ.symm.toRingEquiv.toRingHom (algebraMap K L c) = algebraMap K (RatFunc K) c from
      φ.symm.commutes c, IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K),
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
    simp [Ideal.primeCompl, Ideal.mem_span_singleton, Polynomial.X_dvd_iff, hc]
  · change (Polynomial.idealX K).valuation _ (φ.symm e) = _
    rw [← hφX, AlgEquiv.symm_apply_apply, Polynomial.valuation_X_eq_neg_one]
  · intro f hf
    obtain ⟨c, hc⟩ := exists_valuation_sub_algebraMap_lt_one (φ.symm f) hf
    refine ⟨c, ?_⟩
    change (Polynomial.idealX K).valuation _ (φ.symm (f - algebraMap K L c)) < 1
    rwa [map_sub, φ.symm.commutes]
  · simp only [Valuation.comap_apply]
    change _ ≤ 1 ↔ _
    rw [show φ.symm.toRingEquiv.toRingHom g = φ.symm g from rfl, hφS]
    constructor
    · rintro ⟨s, hs⟩
      refine ⟨s, ?_⟩
      change φ (φS s) = g
      have hs' : φS s = φ.symm g := hs
      rw [hs', AlgEquiv.apply_symm_apply]
    · rintro ⟨s, rfl⟩
      refine ⟨s, ?_⟩
      change φS s = φ.symm (φ (φS s))
      rw [AlgEquiv.symm_apply_apply]

/-- An integral scheme is its own unique irreducible component. -/
private theorem univ_mem_irreducibleComponents (X : Scheme.{0}) [IsIntegral X] :
    (Set.univ : Set X) ∈ irreducibleComponents X := by
  rw [irreducibleComponents_eq_singleton]; rfl

/-- The logarithmic frame `dt/t ∧ dx₁ ∧ ⋯ ∧ dx_e` of top forms along a prime divisor. -/
private noncomputable def logFrame {k : Type} [Field k] [CharZero k] {Y T : Scheme.{0}} [IsIntegral Y] [IsIntegral T] (sY : Y ⟶ Spec (.of k))
    (j : T ⟶ Y) {e : ℕ} (t : Y.presheaf.stalk (j (genericPoint T)))
    (x : Fin e → Y.presheaf.stalk (j (genericPoint T))) :
    letI := functionFieldAlgebra sY
    ⋀[Y.functionField]^(e + 1) Ω[Y.functionField⁄k] :=
  letI := functionFieldAlgebra sY
  (algebraMap _ Y.functionField t)⁻¹ • exteriorPower.ιMulti Y.functionField (e + 1)
    (Fin.cons (KaehlerDifferential.D k Y.functionField (algebraMap _ _ t))
      fun i => KaehlerDifferential.D k Y.functionField (algebraMap _ _ (x i)))

/-- The restricted frame `dx̄₁ ∧ ⋯ ∧ dx̄_e` of top forms on the divisor. -/
private noncomputable def resFrame {k : Type} [Field k] [CharZero k] {Y T : Scheme.{0}} [IsIntegral T] (sY : Y ⟶ Spec (.of k))
    (j : T ⟶ Y) {e : ℕ} (x : Fin e → Y.presheaf.stalk (j (genericPoint T))) :
    letI := functionFieldAlgebra (j ≫ sY)
    ⋀[T.functionField]^e Ω[T.functionField⁄k] :=
  letI := functionFieldAlgebra (j ≫ sY)
  exteriorPower.ιMulti T.functionField e fun i =>
    KaehlerDifferential.D k T.functionField ((j.stalkMap (genericPoint T)).hom (x i))

/-- The residue of a form written in the logarithmic frame. -/
private theorem isPoincareResidue_smul_formPow_logFrame {k : Type} [Field k] [CharZero k] {Y T : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsIntegral T] (sY : Y ⟶ Spec (.of k)) (j : T ⟶ Y) {e m : ℕ}
    {t : Y.presheaf.stalk (j (genericPoint T))} (ht : Y.ord (algebraMap _ Y.functionField t)
      (j (genericPoint T)) = 1) (x : Fin e → Y.presheaf.stalk (j (genericPoint T)))
    (h : Y.presheaf.stalk (j (genericPoint T))) :
    letI := functionFieldAlgebra sY
    letI := functionFieldAlgebra (j ≫ sY)
    IsPoincareResidue sY j e m
      (algebraMap _ Y.functionField h • formPow (logFrame sY j t x) m)
      ((j.stalkMap (genericPoint T)).hom h • formPow (resFrame sY j x) m) :=
  ⟨t, h, x, ht, rfl, rfl⟩

/-- A unit of the local ring at the generic point of a prime divisor has order zero along it,
for any spelling `x = η_P` of that point. -/
private theorem ord_algebraMap_stalk_eq_zero_of_isUnit {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (P : Mori.PrimeDivisor Y) {x : Y}
    (hx : x = P.genericPoint) {u : Y.presheaf.stalk x} (hu : IsUnit u) :
    Y.ord (algebraMap _ Y.functionField u) P.genericPoint = 0 := by
  subst hx
  exact P.ord_algebraMap_of_isUnit hu

/-- A germ at the image of the generic point of an integral closed subscheme `j : T ⟶ Y` whose
restriction to `T` is nonzero is a unit: the stalk of `T` at its generic point is a field. -/
private theorem isUnit_of_stalkMap_genericPoint_ne_zero {Y T : Scheme.{0}} [IsIntegral T]
    (j : T ⟶ Y) {g : Y.presheaf.stalk (j (genericPoint T))}
    (hg : (j.stalkMap (genericPoint T)).hom g ≠ 0) : IsUnit g := by
  have hfield : IsField (T.presheaf.stalk (genericPoint T)) := by
    have := RationalFunctions.isField_stalk T ⟨Set.univ, univ_mem_irreducibleComponents T⟩
    rwa [componentGenericPoint_eq_genericPoint] at this
  letI := hfield.toField
  exact isUnit_of_map_unit (j.stalkMap (genericPoint T)).hom g (isUnit_iff_ne_zero.mpr hg)

/-- **The logarithmic frame of a residue.** Let `σ` be a rational top form on `Y` with a simple
pole along the prime divisor `P = j(T)` and a nonzero Poincaré residue `ρσ`. Then `σ = g₀ ω₀` and
`ρσ = ḡ₀ ω̄₀` for a logarithmic frame `ω₀ = dt/t ∧ dx` and a unit `g₀`, and every rational
`m`-canonical form with `ord_P τ ≥ -m` is `h ω₀^{⊗m}` with `h` regular along `P`. -/
private theorem exists_logFrame {k : Type} [Field k] [CharZero k] {Y T : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY]
    {e : ℕ} (hd : topologicalKrullDim Y = (e + 1 : ℕ)) [IsIntegral T] {j : T ⟶ Y}
    (P : Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint)
    {σ : RationalPluriForms sY (e + 1) 1} (hσ0 : σ ≠ 0) (hσP : P.ordForm σ = -1)
    {ρσ : RationalPluriForms (j ≫ sY) e 1} (hρσ : IsPoincareResidue sY j e 1 σ ρσ)
    (hρσ0 : ρσ ≠ 0) :
    letI := functionFieldAlgebra sY
    letI := functionFieldAlgebra (j ≫ sY)
    ∃ (t g₀ : Y.presheaf.stalk (j (genericPoint T)))
      (x : Fin e → Y.presheaf.stalk (j (genericPoint T))),
      Y.ord (algebraMap _ Y.functionField t) (j (genericPoint T)) = 1 ∧ IsUnit g₀ ∧
      σ = algebraMap _ Y.functionField g₀ • formPow (logFrame sY j t x) 1 ∧
      ρσ = (j.stalkMap (genericPoint T)).hom g₀ • formPow (resFrame sY j x) 1 ∧
      ∀ (m : ℕ) (τ : RationalPluriForms sY (e + 1) m), (τ ≠ 0 → -(m : ℤ) ≤ P.ordForm τ) →
        ∃ h : Y.presheaf.stalk (j (genericPoint T)),
          τ = algebraMap _ Y.functionField h • formPow (logFrame sY j t x) m := by
  classical
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (j ≫ sY)
  obtain ⟨t, g₀, x, ht, hσ, hρσ'⟩ := hρσ
  set ω₀ := logFrame sY j t x with hω₀
  have hg₀ : (j.stalkMap (genericPoint T)).hom g₀ ≠ 0 := by
    intro h0
    apply hρσ0
    rw [hρσ', h0, zero_smul]
    rfl
  have hd' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) hd
  obtain ⟨b⟩ := exists_basis_topForms (sX := sY) hd
  obtain ⟨N, hN⟩ := P.exists_ordForm_eq_ord_add_mul hd' b
  set c := b.repr ω₀ () with hc
  have hω₀b : ω₀ = c • b () := (basis_unit_repr_smul b ω₀).symm
  have hpow : ∀ a : ℕ, (formPow ω₀ a : RationalPluriForms sY (e + 1) a) = c ^ a • formPow (b ()) a :=
    fun a => by rw [hω₀b, formPow_smul]
  have hσω : σ = algebraMap _ Y.functionField g₀ • formPow ω₀ 1 := hσ
  have hσ' : σ = (algebraMap _ Y.functionField g₀ * c) • formPow (b ()) 1 := by
    rw [hσω, mul_smul, ← pow_one c, ← hpow]
  have hc0 : c ≠ 0 := by
    intro h0; apply hσ0
    rw [hσ', h0, mul_zero, zero_smul]
    rfl
  have hcoh : Order.coheight (j (genericPoint T)) = 1 := by
    rw [hP]; exact P.coheight_genericPoint
  have hg₀u : IsUnit g₀ := isUnit_of_stalkMap_genericPoint_ne_zero j hg₀
  have hg₀ord := ord_algebraMap_stalk_eq_zero_of_isUnit P hP hg₀u
  have hσN := hN 1 σ hσ0
  have hr1 : (ZTensorPower.basis b 1).repr
      ((algebraMap _ Y.functionField g₀ * c) • formPow (b ()) 1 : RationalPluriForms sY (e + 1) 1)
      () = algebraMap _ Y.functionField g₀ * c := repr_smul_formPow b 1 _
  rw [hσ', hr1, ← hσ', hσP, Scheme.ord_mul ((hg₀u.map _).ne_zero) hc0, hg₀ord] at hσN
  refine ⟨t, g₀, x, ht, hg₀u, hσω, hρσ', fun m τ hτ => ?_⟩
  by_cases hτ0 : τ = 0
  · exact ⟨0, by rw [hτ0, map_zero, zero_smul]; rfl⟩
  set fτ := (ZTensorPower.basis b m).repr τ () / c ^ m with hfτ
  have hτf : τ = fτ • formPow ω₀ m := by
    rw [hpow, smul_smul, hfτ, div_mul_cancel₀ _ (pow_ne_zero _ hc0)]
    exact eq_repr_smul_formPow b τ
  have hrepr0 : (ZTensorPower.basis b m).repr τ () ≠ 0 := repr_ne_zero_of_ne_zero b hτ0
  have hf0 : fτ ≠ 0 := div_ne_zero hrepr0 (pow_ne_zero _ hc0)
  have hford : 0 ≤ Y.ord fτ (j (genericPoint T)) := by
    have h1 := hτ hτ0
    rw [hN m τ hτ0] at h1
    rw [hP, hfτ, div_eq_mul_inv, Scheme.ord_mul hrepr0 (inv_ne_zero (pow_ne_zero _ hc0)),
      ← zpow_natCast, ← zpow_neg, ord_zpow _ hc0]
    push_cast
    nlinarith
  obtain ⟨h, hh⟩ := (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hcoh hf0).mpr hford
  exact ⟨h, by rw [hτf, ← hh]⟩

/-- A nonzero multiple of a power of a nonzero top form is nonzero. -/
private theorem smul_formPow_ne_zero {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] {d : ℕ}
    (hd : topologicalKrullDim X = d)
    {ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^d Ω[X.functionField⁄k]}
    (hω : ω ≠ 0) {f : X.functionField} (hf : f ≠ 0) (a : ℕ) :
    letI := functionFieldAlgebra sX
    (show RationalPluriForms sX d a from f • formPow ω a) ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hd
  set c := b.repr ω () with hc
  have hωb : ω = c • b () := (basis_unit_repr_smul b ω).symm
  have hc0 : c ≠ 0 := fun h0 => hω (by rw [hωb, h0, zero_smul])
  have e1 : (f • formPow ω a : RationalPluriForms sX d a) = (f * c ^ a) • formPow (b ()) a := by
    rw [hωb, formPow_smul, smul_smul]
  change (f • formPow ω a : RationalPluriForms sX d a) ≠ 0
  rw [e1, ← ZTensorPower.basis_natCast]
  exact smul_ne_zero (mul_ne_zero hf (pow_ne_zero _ hc0)) ((ZTensorPower.basis b _).ne_zero ())

/-- The order of `f ω^{⊗a}` along a prime divisor is `ord f + a ord ω`. -/
private theorem ordForm_smul_formPow {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] {d : ℕ}
    (hd : topologicalKrullDim X = d) (Γ : Mori.PrimeDivisor X)
    {ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^d Ω[X.functionField⁄k]}
    (hω : ω ≠ 0) {f : X.functionField} (hf : f ≠ 0) (a : ℕ) :
    letI := functionFieldAlgebra sX
    Γ.ordForm (show RationalPluriForms sX d a from f • formPow ω a) =
      X.ord f Γ.genericPoint + a * Γ.ordForm (show RationalPluriForms sX d 1 from formPow ω 1) := by
  let := functionFieldAlgebra sX
  have hd' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hd
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hd
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd' b
  set c := b.repr ω () with hc
  have hωb : ω = c • b () := (basis_unit_repr_smul b ω).symm
  have hc0 : c ≠ 0 := fun h0 => hω (by rw [hωb, h0, zero_smul])
  have hpow : ∀ k : ℕ, (formPow ω k : RationalPluriForms sX d k) = c ^ k • formPow (b ()) k :=
    fun k => by rw [hωb, formPow_smul]
  have e1 : (f • formPow ω a : RationalPluriForms sX d a) = (f * c ^ a) • formPow (b ()) a := by
    rw [hpow, smul_smul]
  have e2 : (formPow ω 1 : RationalPluriForms sX d 1) = c • formPow (b ()) 1 := by
    rw [hpow, pow_one]
  have h1 : (f * c ^ a) • formPow (b ()) a ≠ (0 : RationalPluriForms sX d a) := by
    rw [← ZTensorPower.basis_natCast]
    exact smul_ne_zero (mul_ne_zero hf (pow_ne_zero _ hc0)) ((ZTensorPower.basis b _).ne_zero ())
  have h2 : c • formPow (b ()) 1 ≠ (0 : RationalPluriForms sX d 1) := by
    rw [← ZTensorPower.basis_natCast]
    exact smul_ne_zero hc0 ((ZTensorPower.basis b _).ne_zero ())
  have r1 : (ZTensorPower.basis b a).repr ((f * c ^ a) • formPow (b ()) a :
      RationalPluriForms sX d a) () = f * c ^ a := repr_smul_formPow b a _
  have r2 : (ZTensorPower.basis b 1).repr (c • formPow (b ()) 1 :
      RationalPluriForms sX d 1) () = c := repr_smul_formPow b 1 _
  rw [e1, e2, hN _ _ h1, hN _ _ h2, r1, r2, Scheme.ord_mul hf (pow_ne_zero _ hc0),
    ← zpow_natCast, ord_zpow _ hc0]
  push_cast
  ring

/-- **A top form with a simple pole along a prime divisor and nonzero residue**, on a normal
variety of dimension `n + 1 ≥ 2`. -/
private theorem exists_simplePole_isPoincareResidue_ne_zero {k : Type} [Field k] [CharZero k] {X T : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X]
    [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ} (hn : 0 < n)
    (hdim : topologicalKrullDim X = n + 1) (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T]
    [IsNormal T] [IsLocallyNoetherian T] [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX))
    (hdimT : topologicalKrullDim T = n) (P : Mori.PrimeDivisor X)
    (hP : Set.range j.base = (P.support : Set X)) :
    ∃ σ : RationalPluriForms sX (n + 1) 1, σ ≠ 0 ∧ P.ordForm σ = -1 ∧
      ∃ ρσ : RationalPluriForms (j ≫ sX) n 1, IsPoincareResidue sX j n 1 σ ρσ ∧ ρσ ≠ 0 := by
  obtain ⟨Q⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdimT hn.ne'
  obtain ⟨σ, hσ0, hσP, -, ρσ, hρσ, hρσ0, -⟩ :=
    MMP.Fourfold.exists_form_of_residue_order sX hX hdim j hT P hP Q
  exact ⟨σ, hσ0, hσP, ρσ, hρσ, hρσ0⟩

/-- **The pull-back of an effective `ℚ`-Cartier `ℚ`-divisor is effective.** With `m` the Cartier
index of `A`, `m f^*A` is the pull-back of the effective Cartier divisor `mA`, whose local
equations are regular (algebraic Hartogs), so their pull-backs have nonnegative order. -/
private theorem nonneg_of_isPullback {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {A : QDivisor X} (hA : 0 ≤ A)
    (hAq : A.IsQCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ A.supp}
    {B : QDivisor Y} (h : A.IsPullback f hB B) : 0 ≤ B := by
  have hm := QDivisor.cartierIndex_pos hAq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hAq
  obtain ⟨D', hD', hp⟩ := h _ hm D₀ hD₀ hD₀c
  have hmq : (0 : ℚ) < (A.cartierIndex hAq : ℚ) := by exact_mod_cast hm
  have hD₀n : ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ (⊤ : X.Opens)).Nonempty →
      0 ≤ D₀.coeff P := by
    intro P _
    have h2 : (D₀ P : ℚ) = A.cartierIndex hAq * A P :=
      (by simpa using congrArg (· P) hD₀ :
        Divisor.toQDivisor D₀ P = A.cartierIndex hAq * A P)
    exact_mod_cast h2 ▸ mul_nonneg hmq.le (hA P)
  intro E
  have hE : (E.support ∩ f ⁻¹ᵁ (⊤ : X.Opens)).Nonempty :=
    ⟨E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support E, trivial⟩
  have h0 := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hD₀c hD₀n hp E hE
  have h1 : (D' E : ℚ) = A.cartierIndex hAq * B E :=
    (by simpa using congrArg (· E) hD' :
      Divisor.toQDivisor D' E = A.cartierIndex hAq * B E)
  have h0' : (0 : ℚ) ≤ (D' E : ℚ) := by exact_mod_cast h0
  exact nonneg_of_mul_nonneg_right (h1 ▸ h0') hmq

/-- Pull-back of `ℚ`-Cartier `ℚ`-divisors is additive. -/
private theorem qDivisor_isPullback_add {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {G₁ G₂ : QDivisor Y}
    (hG₁ : G₁.IsQCartier) (hG₂ : G₂.IsQCartier)
    {h₁ : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G₁.supp}
    {h₂ : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G₂.supp}
    {R₁ R₂ : QDivisor X} (p₁ : G₁.IsPullback f h₁ R₁) (p₂ : G₂.IsPullback f h₂ R₂)
    (h : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ (G₁ + G₂).supp) :
    (G₁ + G₂).IsPullback f h (R₁ + R₂) := by
  intro m hm D hD hDc
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  obtain ⟨m₁, hm₁, A₁, hA₁, hA₁c⟩ := hG₁.exists_pos
  obtain ⟨m₂, hm₂, A₂, hA₂, hA₂c⟩ := hG₂.exists_pos
  have hm₁' : (m₁ : ℤ) ≠ 0 := by exact_mod_cast hm₁.ne'
  have hm₂' : (m₂ : ℤ) ≠ 0 := by exact_mod_cast hm₂.ne'
  obtain ⟨A₁', hA₁', p₁'⟩ := p₁ m₁ hm₁ A₁ hA₁ hA₁c
  obtain ⟨A₂', hA₂', p₂'⟩ := p₂ m₂ hm₂ A₂ hA₂ hA₂c
  have hsuppD : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ D.supp :=
    fun W hW => h W (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hm' hD] at hW)
  -- the supports of the auxiliary divisors
  have hsupp : ∀ {G : QDivisor Y} (A : Divisor Y) (c : ℤ), c ≠ 0 →
      Divisor.toQDivisor A = c • G →
      (∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G.supp) →
      ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ A.supp :=
    fun A c hc hA hG W hW => hG W (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hc hA] at hW)
  set N : ℤ := (m₁ : ℤ) * m₂
  have hN : N ≠ 0 := mul_ne_zero hm₁' hm₂'
  set A : Divisor Y := (m : ℤ) • ((m₂ : ℤ) • A₁ + (m₁ : ℤ) • A₂)
  have hAD : A = N • D := by
    apply Divisor.toQDivisor_injective
    simp only [A, N, map_zsmul, map_add, hA₁, hA₂, hD, smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring
  have hAc : A.IsCartier := ((hA₁c.zsmul _).add (hA₂c.zsmul _)).zsmul _
  have hA₁N : Divisor.toQDivisor ((m₂ : ℤ) • A₁) = N • G₁ := by
    simp only [map_zsmul, hA₁, smul_smul, N]; congr 1; ring
  have hA₂N : Divisor.toQDivisor ((m₁ : ℤ) • A₂) = N • G₂ := by
    simp only [map_zsmul, hA₂, smul_smul, N]
  have hsum : Divisor.toQDivisor ((m₂ : ℤ) • A₁ + (m₁ : ℤ) • A₂) = N • (G₁ + G₂) := by
    rw [map_add, hA₁N, hA₂N, smul_add]
  have hAq : Divisor.toQDivisor A = ((m : ℤ) * N) • (G₁ + G₂) := by
    simp only [A, map_zsmul, hsum, smul_smul]
  have pA := ((p₁'.zsmul hA₁c (m₂ : ℤ) (hsupp _ _ hN hA₁N h₁)).add (hA₁c.zsmul _)
    (hA₂c.zsmul _) (hsupp _ _ hN hsum h) (p₂'.zsmul hA₂c (m₁ : ℤ) (hsupp _ _ hN hA₂N h₂))).zsmul
    ((hA₁c.zsmul _).add (hA₂c.zsmul _)) (m : ℤ)
    (hsupp _ _ (mul_ne_zero hm' hN) hAq h)
  obtain ⟨D', hD'⟩ := hDc.exists_isPullback hsuppD
  refine ⟨D', ?_, hD'⟩
  have pND := hD'.zsmul hDc N (hsupp _ _ (mul_ne_zero hN hm') (by
    rw [map_zsmul, hD, smul_smul]) h)
  have heq := pA.eq hAc (pND.of_eq hAD.symm)
  have heqQ := congrArg Divisor.toQDivisor heq
  simp only [map_zsmul, map_add, hA₁', hA₂', smul_smul] at heqQ
  ext E
  have := congrArg (fun G : QDivisor X => G.coeff E) heqQ
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, zsmul_eq_mul,
    Divisor.coeff_toQDivisor, N] at this ⊢
  have hNq : ((m₁ : ℚ) * m₂) ≠ 0 := by positivity
  apply mul_left_cancel₀ hNq
  push_cast at this ⊢
  linear_combination -this

/-- Integral multiples of `ℚ`-Cartier `ℚ`-divisors are `ℚ`-Cartier. -/
private theorem isQCartier_zsmul {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {G : QDivisor X} (hG : G.IsQCartier) (c : ℤ) : (c • G).IsQCartier := by
  obtain ⟨m, hm, D, hD, hDc⟩ := hG
  refine ⟨m, hm, c • D, ?_, hDc.zsmul c⟩
  rw [map_zsmul, hD, smul_smul, smul_smul, mul_comm]

/-- A `ℚ`-divisor with coefficient zero along a prime divisor `P` is pulled back along a morphism
from an irreducible scheme whose generic point maps to the generic point of `P`. -/
private theorem forall_notMem_supp_of_coeff_eq_zero {T Y : Scheme.{0}} [IsIntegral T]
    (j : T ⟶ Y) {P : Mori.PrimeDivisor Y} (hP : j (genericPoint T) = P.genericPoint)
    {G : QDivisor Y} (hG : G.coeff P = 0) :
    ∀ W : irreducibleComponents T, j (componentGenericPoint T W) ∉ G.supp := by
  intro W
  rw [componentGenericPoint_eq_genericPoint, hP]
  exact genericPoint_notMem_supp_of_coeff_eq_zero hG

/-- The pull-back of `G' + cG` is `R' + cR`. -/
private theorem qDivisor_isPullback_add_zsmul {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [IsIntegral X] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : X ⟶ Y} {P : Mori.PrimeDivisor Y} (hfP : f (genericPoint X) = P.genericPoint)
    {G G' : QDivisor Y} (hG : G.IsQCartier) (hG' : G'.IsQCartier) (hGP : G.coeff P = 0)
    (hG'P : G'.coeff P = 0) {R R' : QDivisor X}
    (p : G.IsPullback f (forall_notMem_supp_of_coeff_eq_zero f hfP hGP) R)
    (p' : G'.IsPullback f (forall_notMem_supp_of_coeff_eq_zero f hfP hG'P) R') (c : ℕ)
    (hc : (G' + (c : ℤ) • G).coeff P = 0) :
    (G' + (c : ℤ) • G).IsPullback f (forall_notMem_supp_of_coeff_eq_zero f hfP hc)
      (R' + (c : ℤ) • R) := by
  induction c with
  | zero =>
    have e1 : G' = G' + ((0 : ℕ) : ℤ) • G := by simp
    have e2 : R' = R' + ((0 : ℕ) : ℤ) • R := by simp
    rw [← e2]
    exact isPullback_of_eq_source e1 p'
  | succ c ih =>
    have hcP : (G' + (c : ℤ) • G).coeff P = 0 := by
      simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, hGP, hG'P,
        smul_zero, add_zero]
    have hq : (G' + (c : ℤ) • G).IsQCartier := hG'.add (isQCartier_zsmul hG _)
    have e1 : G' + (c : ℤ) • G + G = G' + ((c + 1 : ℕ) : ℤ) • G := by
      rw [add_assoc]; congr 1; push_cast; rw [add_smul, one_smul]
    have e2 : R' + (c : ℤ) • R + R = R' + ((c + 1 : ℕ) : ℤ) • R := by
      rw [add_assoc]; congr 1; push_cast; rw [add_smul, one_smul]
    rw [← e2]
    refine isPullback_of_eq_source e1 (qDivisor_isPullback_add hq hG (ih hcP) p ?_)
    exact forall_notMem_supp_of_coeff_eq_zero f hfP (by
      rw [e1]; exact hc)

/-- `formPow 0 N = 0` for `N > 0`. -/
private theorem formPow_zero_of_pos {k : Type} [Field k] [CharZero k] {K : Type} [Field K] [Algebra k K] {d N : ℕ} (hN : 0 < N) :
    (formPow (0 : ⋀[K]^d Ω[K⁄k]) N : PluriForms k K d N) = 0 := by
  unfold formPow
  exact (PiTensorProduct.tprod K).map_coord_zero ⟨0, hN⟩ rfl

/-- **Residues of log pluricanonical sections are log pluricanonical sections.** Let `(Y, B_Y)` be
a pair on a normal variety of dimension `d + 1` with `B_Y ≤ 1` and `K_Y + B_Y` `ℚ`-Cartier, and
`j : T ⟶ Y` an adjunction step with different `B_T`. Every section `τ` of `N(K_Y + B_Y)` has a
Poincaré residue along `T`, and it is a section of `N(K_T + B_T)`: writing `τ = h ω^{⊗N}` in a
logarithmic frame `ω` along `T`, the divisor
`div τ + N B_Y = (div(hω) + B_Y) + (N - 1)(div ω + B_Y)` is effective and `ℚ`-Cartier, and by
adjunction for the forms `hω` and `ω` its restriction to `T` is `div(Res τ) + N B_T`. -/
private theorem exists_isPoincareResidue_mem_logPluricanonicalSections {k : Type} [Field k]
    [CharZero k]
    {Y T : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] (hYn : IsNormalVariety k sY) {d : ℕ}
    (hd : topologicalKrullDim Y = (d + 1 : ℕ)) {BY : QDivisor Y} (hle : ∀ P, BY.coeff P ≤ 1)
    {K : Divisor Y} (hK : K.IsCanonicalDivisor sY (d + 1))
    (hKB : (Divisor.toQDivisor K + BY).IsQCartier)
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] {j : T ⟶ Y} {BT : QDivisor T}
    (hj : IsAdjunctionStep sY BY j BT) (hdpos : 0 < d) {N : ℕ} (hN : 0 < N)
    {τ : RationalPluriForms sY (d + 1) N}
    (hτ : τ ∈ logPluricanonicalSections sY (d + 1) N BY) :
    ∃ ρ : RationalPluriForms (j ≫ sY) d N, IsPoincareResidue sY j d N τ ρ ∧
      ρ ∈ logPluricanonicalSections (j ≫ sY) d N BT := by
  classical
  obtain ⟨hTn, P, hP1, hPr, hci, -⟩ := id hj
  haveI := hci
  haveI : LocallyOfFiniteType (j ≫ sY) := hTn.1.toLocallyOfFiniteType
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace j
  have hBP : BY.coeff P = 1 := le_antisymm (hle P) hP1
  have hjgen : j (genericPoint T) = P.genericPoint :=
    MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hPr
  have hdT : topologicalKrullDim T = d := topologicalKrullDim_eq_of_range_eq_support sY j P hPr hd
  have hPmem : (P.support ∩ ((⊤ : Y.Opens) : Set Y)).Nonempty :=
    ⟨P.genericPoint, by rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl, trivial⟩
  have hpole : τ ≠ 0 → -(N : ℤ) ≤ P.ordForm τ := by
    intro hτ0
    have h1 := hτ.2 P hPmem hτ0
    rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, hBP, zsmul_eq_mul,
      mul_one, Int.floor_intCast] at h1
    omega
  have htop : (⊤ : T.Opens) ≠ ⊥ := fun h =>
    (show genericPoint T ∈ (⊥ : T.Opens) from h ▸ trivial).elim
  obtain ⟨σ, hσ0, hσP, ρσ, hρσ, hρσ0⟩ := exists_simplePole_isPoincareResidue_ne_zero sY hYn
    hdpos (by rw [hd]; norm_cast) j hTn hdT P hPr
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (j ≫ sY)
  obtain ⟨t, g₀, x, ht, hg₀u, hσeq, -, hall⟩ := exists_logFrame hd P hjgen hσ0 hσP hρσ hρσ0
  obtain ⟨h, hh⟩ := hall N τ hpole
  set ω₀ := logFrame sY j t x with hω₀def
  set ω₁ := resFrame sY j x with hω₁def
  set ρN : RationalPluriForms (j ≫ sY) d N := (j.stalkMap (genericPoint T)).hom h • formPow ω₁ N
    with hρN
  set r₁ : RationalPluriForms (j ≫ sY) d 1 := (j.stalkMap (genericPoint T)).hom h • formPow ω₁ 1
    with hr₁
  set r₀ : RationalPluriForms (j ≫ sY) d 1 := (1 : T.functionField) • formPow ω₁ 1 with hr₀
  set w₁ : RationalPluriForms (j ≫ sY) d 1 := formPow ω₁ 1 with hw₁
  refine ⟨ρN, hh ▸ isPoincareResidue_smul_formPow_logFrame sY j ht x h, ?_⟩
  by_cases hρ0 : ρN = 0
  · rw [hρ0]; exact zero_mem _
  refine ⟨fun h' => absurd h' htop, fun Γ _ hne => ?_⟩
  have hhb : (j.stalkMap (genericPoint T)).hom h ≠ 0 := fun h0 => hρ0 (by rw [hρN, h0, zero_smul]; rfl)
  have hω₁ : ω₁ ≠ 0 := fun h0 => hρ0 (by rw [hρN, h0, formPow_zero_of_pos hN, smul_zero]; rfl)
  have hω₀ : ω₀ ≠ 0 := fun h0 => hσ0 (by rw [hσeq, h0, formPow_zero_of_pos one_pos, smul_zero]; rfl)
  have hunit_ord : ∀ u : Y.presheaf.stalk (j (genericPoint T)), IsUnit u →
      Y.ord (algebraMap _ Y.functionField u) P.genericPoint = 0 :=
    fun _ hu => ord_algebraMap_stalk_eq_zero_of_isUnit P hjgen hu
  have hhu : IsUnit h := isUnit_of_stalkMap_genericPoint_ne_zero j hhb
  have hhK : algebraMap _ Y.functionField h ≠ 0 := (hhu.map _).ne_zero
  have hg₀K : algebraMap _ Y.functionField g₀ ≠ 0 := (hg₀u.map _).ne_zero
  have hdY : topologicalKrullDim Y = (d + 1 : ℕ) := hd
  -- orders along `P`
  have hω₀P : P.ordForm (show RationalPluriForms sY (d + 1) 1 from formPow ω₀ 1) = -1 := by
    have h1 := ordForm_smul_formPow hdY P hω₀ hg₀K 1
    rw [← hσeq, hσP, hunit_ord g₀ hg₀u] at h1
    simp only [Nat.cast_one, one_mul, zero_add] at h1
    exact h1.symm
  -- the two top forms `ω₀` and `h ω₀`, their residues and their divisors
  set α : RationalPluriForms sY (d + 1) 1 := (1 : Y.functionField) • formPow ω₀ 1 with hαdef
  set α' : RationalPluriForms sY (d + 1) 1 := algebraMap _ Y.functionField h • formPow ω₀ 1
    with hα'def
  have hα0 : α ≠ 0 := smul_formPow_ne_zero hdY hω₀ one_ne_zero 1
  have hα'0 : α' ≠ 0 := smul_formPow_ne_zero hdY hω₀ hhK 1
  have hordα : ∀ Γ : Mori.PrimeDivisor Y, Γ.ordForm α =
      Γ.ordForm (show RationalPluriForms sY (d + 1) 1 from formPow ω₀ 1) := fun Γ => by
    rw [hαdef, ordForm_smul_formPow hdY Γ hω₀ one_ne_zero 1, Scheme.ord_one]; push_cast; ring
  have hordα' : ∀ Γ : Mori.PrimeDivisor Y, Γ.ordForm α' = Y.ord (algebraMap _ Y.functionField h)
      Γ.genericPoint + Γ.ordForm (show RationalPluriForms sY (d + 1) 1 from formPow ω₀ 1) :=
    fun Γ => by rw [hα'def, ordForm_smul_formPow hdY Γ hω₀ hhK 1]; push_cast; ring
  have hordτ : ∀ Γ : Mori.PrimeDivisor Y, Γ.ordForm τ = Y.ord (algebraMap _ Y.functionField h)
      Γ.genericPoint + N * Γ.ordForm (show RationalPluriForms sY (d + 1) 1 from formPow ω₀ 1) :=
    fun Γ => by rw [hh, ordForm_smul_formPow hdY Γ hω₀ hhK N]
  have hresα : IsPoincareResidue sY j d 1 α r₀ := by
    have := isPoincareResidue_smul_formPow_logFrame (m := 1) sY j ht x 1
    rwa [map_one, map_one] at this
  have hresα' : IsPoincareResidue sY j d 1 α' r₁ :=
    isPoincareResidue_smul_formPow_logFrame (m := 1) sY j ht x h
  have hαP : P.ordForm α = -1 := by rw [hordα, hω₀P]
  have hα'P : P.ordForm α' = -1 := by rw [hordα', hω₀P, hunit_ord h hhu, zero_add]
  have hQC : ∀ β : RationalPluriForms sY (d + 1) 1, β ≠ 0 →
      (Divisor.toQDivisor (divisorOfForm β) + BY).IsQCartier := fun β hβ =>
    hKB.add_of_linearlyEquivalent (by
      simpa using (MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hYn hK hβ).symm)
  set A := Divisor.toQDivisor (divisorOfForm α) + BY with hAdef
  set A' := Divisor.toQDivisor (divisorOfForm α') + BY with hA'def
  have hAP : A.coeff P = 0 := by
    rw [hAdef, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hαP,
      hBP]; norm_num
  have hA'P : A'.coeff P = 0 := by
    rw [hA'def, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hα'P,
      hBP]; norm_num
  obtain ⟨hgA, hpA⟩ := hj.isPullback_divisorOfForm_add_of_isPoincareResidue (by rw [hd]; norm_cast)
    P hPr α hα0 hαP _ hresα (hQC α hα0)
  obtain ⟨hgA', hpA'⟩ := hj.isPullback_divisorOfForm_add_of_isPoincareResidue (by rw [hd]; norm_cast)
    P hPr α' hα'0 hα'P _ hresα' (hQC α' hα'0)
  have hEP : (A' + ((N - 1 : ℕ) : ℤ) • A).coeff P = 0 := by
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, hAP, hA'P, smul_zero,
      add_zero]
  have hpE := qDivisor_isPullback_add_zsmul (f := j) hjgen (hQC α hα0) (hQC α' hα'0) hAP hA'P hpA hpA'
    (N - 1) hEP
  -- the coefficients of `E = div τ + N B_Y`
  have hEcoeff : ∀ Γ : Mori.PrimeDivisor Y, (A' + ((N - 1 : ℕ) : ℤ) • A).coeff Γ =
      (Γ.ordForm τ : ℚ) + N * BY.coeff Γ := by
    intro Γ
    simp only [hAdef, hA'def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toQDivisor, coeff_divisorOfForm, zsmul_eq_mul, hordα, hordα', hordτ]
    have : ((N - 1 : ℕ) : ℚ) = (N : ℚ) - 1 := by
      rw [Nat.cast_sub hN]; push_cast; ring
    push_cast [this]
    ring
  have hE0 : 0 ≤ A' + ((N - 1 : ℕ) : ℤ) • A := by
    intro Γ
    change 0 ≤ (A' + ((N - 1 : ℕ) : ℤ) • A).coeff Γ
    rw [hEcoeff]
    by_cases hτ0 : τ = 0
    · exfalso
      apply hρ0
      have : (algebraMap _ Y.functionField h • formPow ω₀ N : RationalPluriForms sY (d + 1) N) ≠ 0 :=
        smul_formPow_ne_zero hdY hω₀ hhK N
      exact absurd (hh.symm.trans hτ0) this
    have h1 := hτ.2 Γ ⟨Γ.genericPoint, by
      rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl, trivial⟩ hτ0
    rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h1
    have h2 := Int.floor_le (((N : ℤ) : ℚ) * BY.coeff Γ)
    have h1' : (0 : ℚ) ≤ (Γ.ordForm τ : ℚ) + ⌊((N : ℤ) : ℚ) * BY.coeff Γ⌋ := by exact_mod_cast h1
    push_cast at h2 h1' ⊢
    linarith
  have hEq : (A' + ((N - 1 : ℕ) : ℤ) • A).IsQCartier :=
    (hQC α' hα'0).add (isQCartier_zsmul (hQC α hα0) _)
  have hE'0 := nonneg_of_isPullback hE0 hEq hpE Γ
  -- the coefficient of the restriction along `Γ`
  have hρord : Γ.ordForm ρN = T.ord ((j.stalkMap (genericPoint T)).hom h) Γ.genericPoint +
      N * Γ.ordForm w₁ := ordForm_smul_formPow hdT Γ hω₁ hhb N
  have e1 : (divisorOfForm r₁).coeff Γ = T.ord ((j.stalkMap (genericPoint T)).hom h)
      Γ.genericPoint + Γ.ordForm w₁ := by
    rw [coeff_divisorOfForm]
    have := ordForm_smul_formPow hdT Γ hω₁ hhb 1
    simp only [Nat.cast_one, one_mul] at this
    exact this
  have e2 : (divisorOfForm r₀).coeff Γ = Γ.ordForm w₁ := by
    rw [coeff_divisorOfForm]
    have := ordForm_smul_formPow hdT Γ hω₁ one_ne_zero 1
    simp only [Nat.cast_one, one_mul, Scheme.ord_one, zero_add] at this
    exact this
  have hcast : ((N - 1 : ℕ) : ℚ) = (N : ℚ) - 1 := by
    rw [Nat.cast_sub hN]; push_cast; ring
  have key : (0 : ℚ) ≤ (T.ord ((j.stalkMap (genericPoint T)).hom h) Γ.genericPoint : ℚ) +
      N * (Γ.ordForm w₁ : ℚ) + N * BT.coeff Γ := by
    have h0 : (0 : ℚ) ≤ (Divisor.toQDivisor (divisorOfForm r₁) + BT + ((N - 1 : ℕ) : ℤ) •
        (Divisor.toQDivisor (divisorOfForm r₀) + BT)).coeff Γ := hE'0
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toQDivisor, zsmul_eq_mul, e1, e2] at h0
    push_cast [hcast] at h0
    linarith
  rw [hρord, DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul]
  have hfl : -((T.ord ((j.stalkMap (genericPoint T)).hom h) Γ.genericPoint : ℤ) +
      N * Γ.ordForm w₁) ≤ ⌊((N : ℤ) : ℚ) * BT.coeff Γ⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith
  omega

/-- Two equivalent `ℤᵐ⁰`-valued valuations of a field which both take the value `exp (-1)` are
equal. -/
private theorem eq_of_isEquiv_of_exp_neg_one' {K : Type*} [Field K] {w₁ w₂ : Valuation K ℤᵐ⁰}
    (h : w₁.IsEquiv w₂) (h₁ : ∃ a, w₁ a = WithZero.exp (-1))
    (h₂ : ∃ a, w₂ a = WithZero.exp (-1)) : w₁ = w₂ := by
  obtain ⟨ϖ, hϖ⟩ := h₁
  obtain ⟨ϖ', hϖ'⟩ := h₂
  have hpow : ∀ (w : Valuation K ℤᵐ⁰) (c : ℤ), w ϖ = WithZero.exp c → ∀ n : ℤ,
      w (ϖ ^ n) = WithZero.exp (c * n) := by
    intro w c hc n
    rw [map_zpow₀, hc, ← WithZero.exp_zsmul, smul_eq_mul, mul_comm]
  have hw₂ϖ : w₂ ϖ ≠ 0 := by
    rw [ne_eq, ← h.eq_zero, hϖ]; exact WithZero.exp_ne_zero
  set a := WithZero.log (w₂ ϖ)
  have ha : w₂ ϖ = WithZero.exp a := (WithZero.exp_log hw₂ϖ).symm
  have hw₁ϖ' : w₁ ϖ' ≠ 0 := by
    rw [ne_eq, h.eq_zero, hϖ']; exact WithZero.exp_ne_zero
  set b := WithZero.log (w₁ ϖ')
  have hb : w₁ ϖ' = WithZero.exp b := (WithZero.exp_log hw₁ϖ').symm
  have hab : w₂ ϖ' = WithZero.exp (a * -b) := by
    rw [← hpow w₂ a ha]
    exact (Valuation.IsEquiv.eq_iff h).mp (by rw [hb, hpow w₁ (-1) hϖ]; congr 1; ring)
  rw [hϖ', WithZero.exp_inj] at hab
  have ha0 : a < 0 := by
    have : w₂ ϖ < 1 := (Valuation.isEquiv_iff_val_lt_one.mp h).mp
      (by rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    rwa [ha, ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
  have ha1 : a = -1 := by
    have : a * b = 1 := by linarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' this with h | h <;> omega
  ext g
  by_cases hg : g = 0
  · simp [hg]
  have hg1 : w₁ g ≠ 0 := by simp [hg]
  set m := WithZero.log (w₁ g)
  have hm : w₁ g = WithZero.exp m := (WithZero.exp_log hg1).symm
  have : w₂ g = w₂ (ϖ ^ (-m)) :=
    (Valuation.IsEquiv.eq_iff h).mp (by rw [hm, hpow w₁ (-1) hϖ]; congr 1; ring)
  rw [this, hpow w₂ a ha, hm, ha1]; congr 1; ring

/-- If `dw` spans the nonzero `K`-vector space `Ω_{K/k}`, then `dlog w ≠ 0` in `⋀¹ Ω_{K/k}`. -/
private theorem ιMulti_one_dlog_ne_zero {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Nontrivial Ω[K⁄k]] {w : K}
    (hw : Submodule.span K {KaehlerDifferential.D k K w} = ⊤) :
    exteriorPower.ιMulti K 1 (fun _ => w⁻¹ • KaehlerDifferential.D k K w) ≠ 0 := by
  intro h0
  have h1 := congrArg (exteriorPower.oneEquiv K Ω[K⁄k]) h0
  rw [exteriorPower.oneEquiv_ιMulti, map_zero] at h1
  have hD : KaehlerDifferential.D k K w = 0 := by
    rcases smul_eq_zero.1 h1 with h | h
    · rw [inv_eq_zero.1 h, map_zero]
    · exact h
  rw [hD, Submodule.span_singleton_eq_bot.2 rfl] at hw
  exact bot_ne_top hw

/-- Pulling a germ back along `ι₁` and then `ι₂` is pulling it back along `ι₂ ≫ ι₁ ≫ 𝟙`. -/
private theorem stalkMap_stalkMap_stalkSpecializes {X T₁ T₂ : Scheme.{0}} (ι₂ : T₂ ⟶ T₁)
    (ι₁ : T₁ ⟶ X) (y : T₂) (h : ι₁ (ι₂ y) ⤳ (ι₂ ≫ ι₁ ≫ 𝟙 X) y)
    (a : X.presheaf.stalk ((ι₂ ≫ ι₁ ≫ 𝟙 X) y)) :
    (ι₂.stalkMap y).hom ((ι₁.stalkMap (ι₂ y)).hom ((X.presheaf.stalkSpecializes h).hom a)) =
      ((ι₂ ≫ ι₁ ≫ 𝟙 X).stalkMap y).hom a := by
  have e : X.presheaf.stalkSpecializes h = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
  rw [e, Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_id]
  rfl

/-- At the generic point the canonical map from the stalk to the function field is the
identity. -/
private theorem algebraMap_stalk_genericPoint_apply (Y : Scheme.{0}) [IsIntegral Y]
    (a : Y.presheaf.stalk (genericPoint Y)) :
    @algebraMap _ _ _ _ (AlgebraicGeometry.stalkFunctionFieldAlgebra Y (genericPoint Y)) a = a := by
  change (Y.presheaf.stalkSpecializes _).hom a = a
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- Forms built from `dlog`s do not depend on the structure morphism beyond equality. -/
private theorem heq_formPow_ιMulti_dlog_of_eq {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] {s s' : X ⟶ Spec (.of k)} (hs : s = s') {d : ℕ}
    (f g : Fin d → X.functionField) (hfg : ∀ i, f i = g i) (m : ℕ) :
    HEq (letI := functionFieldAlgebra s;
      (show RationalPluriForms s d m from formPow (exteriorPower.ιMulti X.functionField d
        fun i => (f i)⁻¹ • KaehlerDifferential.D k X.functionField (f i)) m))
      (letI := functionFieldAlgebra s';
        (show RationalPluriForms s' d m from formPow (exteriorPower.ιMulti X.functionField d
          fun i => (g i)⁻¹ • KaehlerDifferential.D k X.functionField (g i)) m)) := by
  subst hs
  obtain rfl : f = g := funext hfg
  rfl

/-- Membership in the log pluricanonical sections does not depend on the structure morphism
beyond equality. -/
private theorem mem_logPluricanonicalSections_of_heq {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {s s' : X ⟶ Spec (.of k)} (hs : s = s')
    {d m : ℕ} {B : QDivisor X} {ω : RationalPluriForms s d m} {ω' : RationalPluriForms s' d m}
    (h : HEq ω ω') (hω : ω ∈ logPluricanonicalSections s d m B) :
    ω' ∈ logPluricanonicalSections s' d m B := by
  subst hs
  cases h
  exact hω

/-- The divisor of a rational pluriform does not depend on the structure morphism beyond
equality. -/
private theorem divisorOfForm_heq {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X] {s s' : X ⟶ Spec (.of k)} [LocallyOfFiniteType s]
    [LocallyOfFiniteType s'] (hs : s = s') {d : ℕ} {m : ℤ} {θ : RationalPluriForms s d m}
    {θ' : RationalPluriForms s' d m} (h : HEq θ θ') : divisorOfForm θ = divisorOfForm θ' := by
  subst hs
  cases h
  rfl

/-- **Residues of log sections along two adjunction steps.** Let `(X, B)` be a normal threefold
with `coeff B ≤ 1` and `ℚ`-Cartier `K_X + B`, `T₁ ⊂ X` an adjunction step `(T₁, B₁)` with
`ℚ`-Cartier `K_{T₁} + B₁` and `coeff B₁ ≤ 1`, and `T₂ ⊂ T₁` an adjunction step `(T₂, B₂)`. If
`ω` is a log `N`-canonical section of `(X, B)`, `ρ_a = Res_{T₁} ω` and `ρ_b = Res_{T₂} ρ_a`, then
`ρ_b` is a log `N`-canonical section of `(T₂, B₂)`. -/
private theorem mem_logPluricanonicalSections_of_isPoincareResidue_two {k : Type} [Field k]
    [CharZero k] {X T₁ T₂ : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX)
    (hd : topologicalKrullDim X = (3 : ℕ)) {B : QDivisor X} (hle : ∀ P, B.coeff P ≤ 1)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 3) (hKB : (Divisor.toQDivisor K + B).IsQCartier)
    [IsIntegral T₁] [IsLocallyNoetherian T₁] [IsNormal T₁] [CompactSpace T₁] {ι₁ : T₁ ⟶ X}
    [LocallyOfFiniteType (ι₁ ≫ sX)] {B₁ : QDivisor T₁} (h₁ : IsAdjunctionStep sX B ι₁ B₁)
    (hT₁ : IsNormalVariety k (ι₁ ≫ sX)) (hd₁ : topologicalKrullDim T₁ = (2 : ℕ))
    (hle₁ : ∀ P, B₁.coeff P ≤ 1) {K₁ : Divisor T₁} (hK₁ : K₁.IsCanonicalDivisor (ι₁ ≫ sX) 2)
    (hKB₁ : (Divisor.toQDivisor K₁ + B₁).IsQCartier)
    [IsIntegral T₂] [IsLocallyNoetherian T₂] [IsNormal T₂] {ι₂ : T₂ ⟶ T₁} {B₂ : QDivisor T₂}
    (h₂ : IsAdjunctionStep (ι₁ ≫ sX) B₁ ι₂ B₂) {N : ℕ} (hN : 0 < N)
    {ω : RationalPluriForms sX 3 N} (hω : ω ∈ logPluricanonicalSections sX 3 N B)
    {ρa : RationalPluriForms (ι₁ ≫ sX) 2 N} (ha : IsPoincareResidue sX ι₁ 2 N ω ρa)
    {ρb : RationalPluriForms (ι₂ ≫ ι₁ ≫ sX) 1 N} (hb : IsPoincareResidue (ι₁ ≫ sX) ι₂ 1 N ρa ρb) :
    ρb ∈ logPluricanonicalSections (ι₂ ≫ ι₁ ≫ sX) 1 N B₂ := by
  obtain ⟨ρa', ha', hma⟩ := exists_isPoincareResidue_mem_logPluricanonicalSections hX
    (d := 2) (by rw [hd]) hle hK hKB h₁ (by norm_num) hN hω
  rw [IsPoincareResidue.unique h₁ ha' ha] at hma
  obtain ⟨ρb', hb', hmb⟩ := exists_isPoincareResidue_mem_logPluricanonicalSections hT₁
    (d := 1) (by rw [hd₁]) hle₁ hK₁ hKB₁ h₂ (by norm_num) hN hma
  rwa [IsPoincareResidue.unique h₂ hb' hb] at hmb

/-- **The flag to a curve stratum.** Let `(X, B)` be a dlt threefold and `x` a point with snc
coordinates `z₁, z₂` (local equations of the coefficient-one divisors `L₁, L₂` through `x`, the
only components of `Supp B` through `x`), completed by a unit `v` to a frame of `Ω_{𝒪_{X,x}}`.
There is a flag `X ⊃ L₁ ⊃ Z` of length two ending at the closure `Z` of `x`, along which the
iterated residue of `g (dlog z₁ ∧ dlog z₂ ∧ dlog v)^m` is `ḡ (dlog v̄)^m`, the bars denoting
restriction to `k(Z)`; moreover `div(dlog v̄) + B_Z` is the pull-back of
`div(dlog z₁ ∧ dlog z₂ ∧ dlog v) + B`. -/
private theorem exists_flag_isIteratedResidueRec_of_curve {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (hX : IsNormalVariety k sX) [LocallyOfFiniteType sX]
    {B : QDivisor X} (hpair : Mori.IsPair sX B) (hdlt : MMP.Intersection.IsDltPair sX B)
    (hd : topologicalKrullDim X = (3 : ℕ)) {x : X}
    (z : Fin 2 → X.presheaf.stalk x) (hz : IsRegularSystemOfParameters z)
    (v : X.presheaf.stalk x) (hvu : IsUnit v)
    (hw : letI := stalkAlgebra sX x
      Submodule.span (X.presheaf.stalk x) (Set.range fun a : Fin 3 =>
        KaehlerDifferential.D k (X.presheaf.stalk x) (![z 0, z 1, v] a)) = ⊤)
    (L : Fin 2 → Mori.PrimeDivisor X) (hL : Function.Injective L) (hLx : ∀ a, x ∈ (L a).support)
    (hLz : ∀ a, IdealSheafData.stalk (L a).idealSheaf x = Ideal.span {z a})
    (hBL : ∀ E : Mori.PrimeDivisor X, x ∈ E.support → B.coeff E ≠ 0 → E ∈ Set.range L)
    (hL1 : ∀ a, B.coeff (L a) = 1)
    (hQ : letI := functionFieldAlgebra sX
      (Divisor.toQDivisor (divisorOfForm (show RationalPluriForms sX 3 ((1 : ℕ) : ℤ) from
        formPow (exteriorPower.ιMulti X.functionField 3 fun a =>
          (algebraMap (X.presheaf.stalk x) X.functionField (![z 0, z 1, v] a))⁻¹ •
            KaehlerDifferential.D k X.functionField
              (algebraMap (X.presheaf.stalk x) X.functionField (![z 0, z 1, v] a))) 1)) +
        B).IsQCartier) :
    ∃ (T₂ : Scheme.{0}) (ιT : T₂ ⟶ X) (B₂ : QDivisor T₂) (F : StratumAdjunctionData sX B ιT B₂),
      F.length = 2 ∧ topologicalKrullDim T₂ = (1 : ℕ) ∧
      haveI := F.isIntegral_stratum
      ιT (genericPoint T₂) = x ∧ ∃ resZ : X.presheaf.stalk x →+* T₂.functionField,
        Function.Surjective resZ ∧
        (∀ r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x), resZ r = 0) ∧
        (letI := stalkAlgebra sX x; letI := functionFieldAlgebra (ιT ≫ sX)
          ∀ c : k, resZ (algebraMap k _ c) = algebraMap k _ c) ∧
        (letI := functionFieldAlgebra sX; letI := functionFieldAlgebra (ιT ≫ sX)
          ∀ (g : X.presheaf.stalk x) (m : ℕ), IsIteratedResidueRec
            (show RationalPluriForms sX 3 m from algebraMap _ X.functionField g •
              formPow (exteriorPower.ιMulti X.functionField 3 fun a =>
                (algebraMap (X.presheaf.stalk x) X.functionField (![z 0, z 1, v] a))⁻¹ •
                  KaehlerDifferential.D k X.functionField
                    (algebraMap (X.presheaf.stalk x) X.functionField (![z 0, z 1, v] a))) m)
            F 1 (resZ g • (show RationalPluriForms (ιT ≫ sX) 1 m from
              formPow (exteriorPower.ιMulti T₂.functionField 1
                fun _ => (resZ v)⁻¹ • KaehlerDifferential.D k T₂.functionField (resZ v)) m))) ∧
        (∀ (h : x ⤳ ιT (genericPoint T₂)) (a : X.presheaf.stalk (ιT (genericPoint T₂))),
          resZ ((X.presheaf.stalkSpecializes h).hom a) = (ιT.stalkMap (genericPoint T₂)).hom a) ∧
        (letI := functionFieldAlgebra sX; letI := functionFieldAlgebra (ιT ≫ sX)
          haveI := F.isLocallyNoetherian_stratum; haveI := F.isNormal_stratum
          haveI : LocallyOfFiniteType (ιT ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
          haveI := F.isClosedImmersion
          haveI : CompactSpace T₂ := QuasiCompact.compactSpace_of_compactSpace ιT
          ∃ hgen, (Divisor.toQDivisor (divisorOfForm
            (show RationalPluriForms sX 3 ((1 : ℕ) : ℤ) from
              formPow (exteriorPower.ιMulti X.functionField 3 fun a =>
                (algebraMap (X.presheaf.stalk x) X.functionField (![z 0, z 1, v] a))⁻¹ •
                  KaehlerDifferential.D k X.functionField
                    (algebraMap (X.presheaf.stalk x) X.functionField (![z 0, z 1, v] a))) 1)) +
            B).IsPullback ιT hgen (Divisor.toQDivisor (divisorOfForm
              (show RationalPluriForms (ιT ≫ sX) 1 ((1 : ℕ) : ℤ) from
                formPow (exteriorPower.ιMulti T₂.functionField 1
                  fun _ => (resZ v)⁻¹ • KaehlerDifferential.D k T₂.functionField (resZ v)) 1)) +
              B₂)) ∧
        (haveI := F.isLocallyNoetherian_stratum; haveI := F.isNormal_stratum
          MMP.Intersection.IsDltPair (ιT ≫ sX) B₂) ∧
        (∀ m : ℕ, 0 < m → ∀ K : Divisor X, K.IsCanonicalDivisor sX 3 →
          ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor →
          (∀ {S : Scheme.{0}} {ιS : S ⟶ X} {BS : QDivisor S}
            (F' : StratumAdjunctionData sX B ιS BS),
            haveI := F'.isIntegral_stratum
            haveI := F'.isNormal_stratum
            haveI := F'.isLocallyNoetherian_stratum
            ∃ (d : ℕ) (KS : Divisor S), KS.IsCanonicalDivisor (ιS ≫ sX) d ∧
              ((m : ℤ) • (Divisor.toQDivisor KS + BS)).IsCartierDivisor) →
          letI := functionFieldAlgebra sX; letI := functionFieldAlgebra (ιT ≫ sX)
          haveI := F.isLocallyNoetherian_stratum; haveI := F.isNormal_stratum
          ∀ ω : RationalPluriForms sX 3 m, ω ∈ logPluricanonicalSections sX 3 m B →
          ∀ g : X.presheaf.stalk x, ω = algebraMap _ X.functionField g •
            (show RationalPluriForms sX 3 m from formPow (exteriorPower.ιMulti X.functionField 3
              fun a => (algebraMap (X.presheaf.stalk x) X.functionField (![z 0, z 1, v] a))⁻¹ •
                KaehlerDifferential.D k X.functionField
                  (algebraMap (X.presheaf.stalk x) X.functionField (![z 0, z 1, v] a))) m) →
          (show RationalPluriForms (ιT ≫ sX) 1 m from resZ g •
            formPow (exteriorPower.ιMulti T₂.functionField 1
              fun _ => (resZ v)⁻¹ • KaehlerDifferential.D k T₂.functionField (resZ v)) m) ∈
            logPluricanonicalSections (ιT ≫ sX) 1 m B₂) := by
  classical
  letI := functionFieldAlgebra sX
  obtain ⟨T₁, ι₁, B₁, hpair1, h₁, hT₁i, hr₁, hd₁⟩ :=
    exists_isAdjunctionStep_of_isDltPair hX hdlt (e := 2) hd (L 0) (by rw [hL1 0])
  have h₁' : IsAdjunctionStep sX B ι₁ B₁ := by have := h₁; rwa [Category.id_comp] at this
  have hT₁nv : IsNormalVariety k (ι₁ ≫ sX) := h₁'.1
  haveI : IsNormal T₁ := hT₁nv.2
  haveI : LocallyOfFiniteType (ι₁ ≫ sX) := hT₁nv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian T₁ := LocallyOfFiniteType.isLocallyNoetherian (ι₁ ≫ sX)
  obtain ⟨-, -, -, -, hci₁, -⟩ := id h₁'
  haveI := hci₁
  haveI : CompactSpace T₁ := QuasiCompact.compactSpace_of_compactSpace ι₁
  have hdlt₁ := isDltPair_of_isAdjunctionStep hdlt hpair1 h₁ (L 0) (by rw [hL1 0]) hr₁
  obtain ⟨y₁, rfl⟩ : ∃ y, ι₁ y = x := by
    have : x ∈ Set.range ι₁.base := by rw [hr₁]; exact hLx 0
    exact this
  have hz0 : ∀ a, z a ≠ 0 := by
    haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
    exact fun a => MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz a
  let z3 : Fin 3 → X.presheaf.stalk (ι₁ y₁) := ![z 0, z 1, v]
  have hz30 : ∀ a, z3 a ≠ 0 := by
    intro a; fin_cases a
    · exact hz0 0
    · exact hz0 1
    · exact hvu.ne_zero
  let S3 : Set (Fin 3) := {0, 1}
  let L3 : Fin 3 → Mori.PrimeDivisor X := ![L 0, L 1, L 0]
  have hS3a : ∀ a ∈ S3, ∃ b : Fin 2, L3 a = L b ∧ z3 a = z b := by
    intro a ha
    rcases ha with rfl | rfl
    · exact ⟨0, rfl, rfl⟩
    · exact ⟨1, rfl, rfl⟩
  have hL3 : Set.InjOn L3 S3 := by
    intro a ha a' ha' haa
    rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl
    · rfl
    · exact absurd (hL haa) (by decide)
    · exact absurd (hL haa) (by decide)
    · rfl
  have hL3x : ∀ a ∈ S3, ι₁ y₁ ∈ (L3 a).support := fun a ha => by
    obtain ⟨b, hb, -⟩ := hS3a a ha; rw [hb]; exact hLx b
  have hL3z : ∀ a ∈ S3, IdealSheafData.stalk (L3 a).idealSheaf (ι₁ y₁) = Ideal.span {z3 a} :=
    fun a ha => by obtain ⟨b, hb, hb'⟩ := hS3a a ha; rw [hb, hb']; exact hLz b
  have hu3 : ∀ a ∉ S3, IsUnit (z3 a) := by
    intro a ha
    fin_cases a
    · exact absurd (Or.inl rfl) ha
    · exact absurd (Or.inr rfl) ha
    · exact hvu
  have hBL3 : ∀ E : Mori.PrimeDivisor X, ι₁ y₁ ∈ E.support → B.coeff E ≠ 0 → E ∈ L3 '' S3 := by
    intro E hE h0
    obtain ⟨b, rfl⟩ := hBL E hE h0
    fin_cases b
    · exact ⟨0, Or.inl rfl, rfl⟩
    · exact ⟨1, Or.inr rfl, rfl⟩
  have hL13 : ∀ a ∈ S3, B.coeff (L3 a) = 1 := fun a ha => by
    obtain ⟨b, hb, -⟩ := hS3a a ha; rw [hb]; exact hL1 b
  obtain ⟨U, hxU, hU⟩ := exists_open_coeff_divisorOfForm_add_eq_zero_of_isUnit hd z3 hz30 hw S3 L3
    hL3 hL3x hL3z hu3 hBL3 hL13
  -- `z₂` and `v` are not multiples of `z₁`
  haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  have hz1 : z 1 ∉ Ideal.span {z 0} := by
    obtain ⟨hreg, -, hsys⟩ :=
      MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz {0}
    have hb : (1 : Fin 2) ∈ Set.range (({0}ᶜ : Finset (Fin 2)).orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; simp
    obtain ⟨i, hi⟩ := hb
    haveI := hreg
    have h0 := MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hsys i
    intro hmem
    apply h0
    rw [hi, Ideal.Quotient.eq_zero_iff_mem, Finset.coe_singleton, Set.image_singleton]
    exact hmem
  have hzu : ∀ i : Fin 2, z3 i.succ ∉ IdealSheafData.stalk (L 0).idealSheaf (ι₁ y₁) := by
    rw [hLz 0]
    intro i; fin_cases i
    · exact hz1
    · intro hmem
      have : v ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (ι₁ y₁)) := by
        rw [← hz.1]
        exact Ideal.span_mono (s := {z 0}) (t := Set.range z)
          (Set.singleton_subset_iff.2 (Set.mem_range_self 0)) hmem
      exact (IsLocalRing.mem_maximalIdeal _).1 this hvu
  -- the residue along `L₁`
  have hres1 := fun (g : X.presheaf.stalk (ι₁ y₁)) (m : ℕ) =>
    isPoincareResidue_formPow_dlog_coordinate_of_notMem sX ι₁ (L 0) hr₁ y₁ z3 (hLx 0) (hLz 0) hzu
      g m
  -- the local ring of `L₁` at `y₁` and the curve `Z₁ ⊂ L₁` through it
  have hzT := isRegularSystemOfParameters_stalkMap_succ ι₁ (L 0) hr₁ y₁ (d := 1) hz (hLz 0)
  have hcoh : Order.coheight y₁ = 1 := by
    have h1 := hzT.2
    rw [ringKrullDim_stalk_eq_coheight] at h1
    have h2 : ((Order.coheight y₁ : ℕ∞) : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) := h1
    exact WithBot.coe_injective h2
  obtain ⟨Z₁, hZη⟩ : ∃ Z : Mori.PrimeDivisor T₁, Z.genericPoint = y₁ :=
    ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh⟩
  have hy₁Z : y₁ ∈ Z₁.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← hZη]; exact subset_closure rfl
  have hkerZ : ∀ (y : T₁) (hy : y = Z₁.genericPoint), IdealSheafData.stalk Z₁.idealSheaf y =
      IsLocalRing.maximalIdeal (T₁.presheaf.stalk y) := by
    rintro y rfl; exact MMP.Resolution.Aux.stalk_idealSheaf_genericPoint Z₁
  have hZz : IdealSheafData.stalk Z₁.idealSheaf y₁ =
      Ideal.span {(ι₁.stalkMap y₁).hom (z 1)} := by
    rw [hkerZ y₁ hZη.symm, ← hzT.1]
    congr 1
    ext w; simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩; fin_cases i; rfl
    · rintro rfl; exact ⟨0, rfl⟩
  have hv1u : IsUnit ((ι₁.stalkMap y₁).hom v) := hvu.map _
  -- the frame `dz̄₂, dv̄` at `y₁`
  letI := stalkAlgebra sX (ι₁ y₁)
  letI := stalkAlgebra (ι₁ ≫ sX) y₁
  let φ : X.presheaf.stalk (ι₁ y₁) →ₐ[k] T₁.presheaf.stalk y₁ :=
    { (ι₁.stalkMap y₁).hom with commutes' := stalkMap_algebraMap_const sX ι₁ y₁ }
  have hφs : Function.Surjective φ := ι₁.stalkMap_surjective y₁
  have hw₁' := span_D_eq_top_of_surjective φ hφs z3 hw
  have hz0T : (ι₁.stalkMap y₁).hom (z 0) = 0 := by
    rw [← RingHom.mem_ker, ker_stalkMap_eq_stalk_idealSheaf ι₁ (L 0) hr₁ y₁, hLz 0]
    exact Ideal.mem_span_singleton_self _
  have hw₁ : Submodule.span (T₁.presheaf.stalk y₁) (Set.range fun a : Fin 2 =>
      KaehlerDifferential.D k (T₁.presheaf.stalk y₁)
        (![(ι₁.stalkMap y₁).hom (z 1), (ι₁.stalkMap y₁).hom v] a)) = ⊤ := by
    rw [eq_top_iff, ← hw₁', Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    fin_cases a
    · change KaehlerDifferential.D k _ ((ι₁.stalkMap y₁).hom (z 0)) ∈ _
      rw [hz0T, map_zero]; exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨0, rfl⟩
    · exact Submodule.subset_span ⟨1, rfl⟩
  -- the residue of the log generator along `L₁`, and its order along `Z₁`
  have hzb0 : ∀ a, (![(ι₁.stalkMap y₁).hom (z 1), (ι₁.stalkMap y₁).hom v] a) ≠ 0 := by
    intro a; fin_cases a
    · haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hzT
      exact MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hzT 0
    · exact hv1u.ne_zero
  letI := functionFieldAlgebra (ι₁ ≫ sX)
  have hord1 := ordForm_formPow_dlog_eq_of_isUnit (sX := ι₁ ≫ sX) hd₁ 1
    (![(ι₁.stalkMap y₁).hom (z 1), (ι₁.stalkMap y₁).hom v]) hzb0 hw₁ {0} (fun _ => Z₁)
    (Set.injOn_singleton _ _) (fun _ _ => hy₁Z)
    (fun a ha => by rw [ha]; exact hZz)
    (fun a ha => by
      fin_cases a
      · exact absurd rfl ha
      · exact hv1u) Z₁ hy₁Z
  rw [if_pos ⟨0, rfl, rfl⟩] at hord1
  have hfun : ∀ (f : T₁.presheaf.stalk y₁ → T₁.functionField),
      (fun i : Fin 2 => (f ((ι₁.stalkMap y₁).hom (z3 i.succ)))⁻¹ •
        KaehlerDifferential.D k T₁.functionField (f ((ι₁.stalkMap y₁).hom (z3 i.succ)))) =
      fun a => (f (![(ι₁.stalkMap y₁).hom (z 1), (ι₁.stalkMap y₁).hom v] a))⁻¹ •
        KaehlerDifferential.D k T₁.functionField
          (f (![(ι₁.stalkMap y₁).hom (z 1), (ι₁.stalkMap y₁).hom v] a)) := by
    intro f; funext i; fin_cases i <;> rfl
  let τ1 : RationalPluriForms sX 3 ((1 : ℕ) : ℤ) := formPow (exteriorPower.ιMulti X.functionField 3
    fun a => (algebraMap (X.presheaf.stalk (ι₁ y₁)) X.functionField (z3 a))⁻¹ •
      KaehlerDifferential.D k X.functionField
        (algebraMap (X.presheaf.stalk (ι₁ y₁)) X.functionField (z3 a))) 1
  let ρ1 : RationalPluriForms (ι₁ ≫ sX) 2 ((1 : ℕ) : ℤ) := formPow (exteriorPower.ιMulti
    T₁.functionField 2 fun a =>
      (algebraMap (T₁.presheaf.stalk y₁) T₁.functionField
        (![(ι₁.stalkMap y₁).hom (z 1), (ι₁.stalkMap y₁).hom v] a))⁻¹ •
        KaehlerDifferential.D k T₁.functionField (algebraMap (T₁.presheaf.stalk y₁)
          T₁.functionField (![(ι₁.stalkMap y₁).hom (z 1), (ι₁.stalkMap y₁).hom v] a))) 1
  replace hord1 : Z₁.ordForm ρ1 = -1 := hord1
  have hres1' : IsPoincareResidue sX ι₁ 2 1 τ1 ρ1 := by
    have h1 := hres1 1 1
    simp only [map_one, one_smul] at h1
    rw [hfun] at h1
    exact h1
  have hτ1L : (L 0).ordForm τ1 = -1 := by
    have := ordForm_formPow_dlog_eq_of_isUnit hd 1 z3 hz30 hw S3 L3 hL3 hL3x hL3z hu3 (L 0)
      (hLx 0)
    rw [if_pos ⟨0, Or.inl rfl, rfl⟩] at this
    exact this
  have hτ10 : τ1 ≠ 0 := by
    intro h0; rw [h0, Mori.PrimeDivisor.ordForm_zero] at hτ1L; exact absurd hτ1L (by decide)
  obtain ⟨hgenT, hpbT⟩ := h₁'.isPullback_divisorOfForm_add_of_isPoincareResidue (n := 2)
    (by rw [hd]; norm_cast) (L 0) hr₁ τ1 hτ10 hτ1L ρ1 hres1' hQ
  have hc0 := coeff_eq_zero_of_isPullback_of_forall hQ hpbT U hU Z₁ ⟨y₁, hy₁Z, hxU⟩
  have hB1Z : B₁.coeff Z₁ = 1 := by
    rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm] at hc0
    change ((Z₁.ordForm ρ1 : ℤ) : ℚ) + B₁.coeff Z₁ = 0 at hc0
    rw [hord1] at hc0
    push_cast at hc0
    linarith
  -- the second step, onto the curve `Z₁`
  obtain ⟨T₂, ι₂, B₂, hpair2, h₂, hT₂i, hr₂, hd₂⟩ :=
    exists_isAdjunctionStep_of_isDltPair hT₁nv hdlt₁ (e := 1) hd₁ Z₁ (by rw [hB1Z])
  have h₂' : IsAdjunctionStep (ι₁ ≫ sX) B₁ ι₂ B₂ := by have := h₂; rwa [Category.id_comp] at this
  have h₂'' : IsAdjunctionStep ((ι₁ ≫ 𝟙 X) ≫ sX) B₁ ι₂ B₂ := by
    rw [Category.comp_id]; exact h₂'
  have hT₂nv : IsNormalVariety k (ι₂ ≫ ι₁ ≫ sX) := h₂'.1
  haveI : IsNormal T₂ := hT₂nv.2
  haveI : LocallyOfFiniteType (ι₂ ≫ ι₁ ≫ sX) := hT₂nv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian T₂ := LocallyOfFiniteType.isLocallyNoetherian (ι₂ ≫ ι₁ ≫ sX)
  obtain ⟨-, -, -, -, hci₂, -⟩ := id h₂'
  haveI := hci₂
  have hy₂ : ι₂ (genericPoint T₂) = y₁ := by
    rw [map_genericPoint_eq_of_range_eq ι₂ Z₁ hr₂, hZη]
  subst hy₂
  -- the residue along `Z₁`
  have hzu₂ : ∀ i : Fin 1, (![(ι₁.stalkMap (ι₂ (genericPoint T₂))).hom (z 1),
      (ι₁.stalkMap (ι₂ (genericPoint T₂))).hom v] i.succ) ∉
      IdealSheafData.stalk Z₁.idealSheaf (ι₂ (genericPoint T₂)) := by
    intro i; fin_cases i
    rw [hkerZ _ hZη.symm]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h hv1u
  have hres2 := fun (g : T₁.presheaf.stalk (ι₂ (genericPoint T₂))) (m : ℕ) =>
    isPoincareResidue_formPow_dlog_coordinate_of_notMem (ι₁ ≫ sX) ι₂ Z₁ hr₂ (genericPoint T₂)
      (d := 1) ![(ι₁.stalkMap (ι₂ (genericPoint T₂))).hom (z 1),
        (ι₁.stalkMap (ι₂ (genericPoint T₂))).hom v] hy₁Z hZz hzu₂ g m
  letI : Algebra (T₂.presheaf.stalk (genericPoint T₂)) T₂.functionField :=
    AlgebraicGeometry.stalkFunctionFieldAlgebra T₂ (genericPoint T₂)
  let resZ : X.presheaf.stalk (ι₁ (ι₂ (genericPoint T₂))) →+* T₂.functionField :=
    (algebraMap (T₂.presheaf.stalk (genericPoint T₂)) T₂.functionField).comp
      ((ι₂.stalkMap (genericPoint T₂)).hom.comp (ι₁.stalkMap (ι₂ (genericPoint T₂))).hom)
  have hresZ : resZ = (algebraMap (T₂.presheaf.stalk (genericPoint T₂)) T₂.functionField).comp
      ((ι₂.stalkMap (genericPoint T₂)).hom.comp (ι₁.stalkMap (ι₂ (genericPoint T₂))).hom) := rfl
  have hfield : IsField (T₂.presheaf.stalk (genericPoint T₂)) := Field.toIsField T₂.functionField
  have hsT : (ι₂ ≫ ι₁ ≫ 𝟙 X) ≫ sX = ι₂ ≫ ι₁ ≫ sX := by simp
  -- the pull-back of `div τ + B` to the curve
  have hρ10 : ρ1 ≠ 0 := by
    intro h0; rw [h0, Mori.PrimeDivisor.ordForm_zero] at hord1; exact absurd hord1 (by decide)
  have hqT₁ := isQCartier_of_isPullback hQ hpbT
  have hres2' := hres2 1 1
  simp only [map_one, one_smul] at hres2'
  haveI : CompactSpace T₂ := QuasiCompact.compactSpace_of_compactSpace ι₂
  obtain ⟨hgen2, hpb2⟩ := h₂'.isPullback_divisorOfForm_add_of_isPoincareResidue (n := 1)
    (by rw [hd₁]; norm_cast) Z₁ hr₂ ρ1 hρ10 hord1 _ hres2' hqT₁
  have hgen12 : ∀ C : irreducibleComponents T₂, (ι₂ ≫ ι₁) (componentGenericPoint T₂ C) ∉
      (Divisor.toQDivisor (divisorOfForm τ1) + B).supp := by
    intro C hC
    obtain ⟨E, hE, hzE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hC
    rw [componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply] at hzE
    exact hE (hU E ⟨_, hzE, hxU⟩)
  have hpb12 := qDivisor_isPullback_comp' ι₁ ι₂ hpbT hpb2 hgen12
  refine ⟨T₂, ι₂ ≫ ι₁ ≫ 𝟙 X, B₂, .step (.step (.refl hpair) ι₁ B₁ h₁) ι₂ B₂ h₂'', rfl, hd₂,
    by simp, resZ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((IsFractionRing.surjective_iff_isField).2 hfield).comp
      ((ι₂.stalkMap_surjective _).comp (ι₁.stalkMap_surjective _))
  · intro r hr
    have h1 : ¬ IsUnit r := (IsLocalRing.mem_maximalIdeal _).1 hr
    have h2 : ¬ IsUnit ((ι₂.stalkMap (genericPoint T₂)).hom
        ((ι₁.stalkMap (ι₂ (genericPoint T₂))).hom r)) := fun hu =>
      h1 (isUnit_of_map_unit (ι₁.stalkMap (ι₂ (genericPoint T₂))).hom r
        (isUnit_of_map_unit (ι₂.stalkMap (genericPoint T₂)).hom _ hu))
    have h3 : (ι₂.stalkMap (genericPoint T₂)).hom
        ((ι₁.stalkMap (ι₂ (genericPoint T₂))).hom r) = 0 := by
      by_contra h0
      exact h2 (IsUnit.mk0 (show T₂.functionField from _) h0)
    simp only [resZ, RingHom.comp_apply, h3, map_zero]
  · intro c
    simp only [resZ, RingHom.comp_apply]
    rw [stalkMap_algebraMap_const sX ι₁ _ c, stalkMap_algebraMap_const (ι₁ ≫ sX) ι₂ _ c]
    letI := functionFieldAlgebra (ι₂ ≫ ι₁ ≫ sX)
    haveI := isScalarTower_stalk_functionField (ι₂ ≫ ι₁ ≫ sX) (genericPoint T₂)
    rw [← IsScalarTower.algebraMap_apply]
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ (ι₂ ≫ ι₁ ≫ sX).appTop ≫
      T₂.presheaf.germ ⊤ _ (TopologicalSpace.Opens.mem_top _)).hom c) =
      (((Scheme.ΓSpecIso (.of k)).inv ≫ ((ι₂ ≫ ι₁ ≫ 𝟙 X) ≫ sX).appTop ≫
        T₂.presheaf.germ ⊤ _ (TopologicalSpace.Opens.mem_top _)).hom c)
    rw [hsT]
  · intro g m
    letI := functionFieldAlgebra (ι₂ ≫ ι₁ ≫ sX)
    have r1 := hres1 g m
    rw [hfun] at r1
    have r2 := hres2 ((ι₁.stalkMap (ι₂ (genericPoint T₂))).hom g) m
    refine isIteratedResidueRec_step_step hpair h₁ h₂'' r1 r2 _ ?_
    simp only [hresZ, RingHom.comp_apply]
    exact heq_smul_formPow_ιMulti_dlog_of_eq hsT
      (@algebraMap _ _ _ _ (AlgebraicGeometry.stalkFunctionFieldAlgebra T₂ (genericPoint T₂))
        ((ι₂.stalkMap (genericPoint T₂)).hom ((ι₁.stalkMap (ι₂ (genericPoint T₂))).hom g)))
      (fun _ => @algebraMap _ _ _ _
        (AlgebraicGeometry.stalkFunctionFieldAlgebra T₂ (genericPoint T₂))
        ((ι₂.stalkMap (genericPoint T₂)).hom ((ι₁.stalkMap (ι₂ (genericPoint T₂))).hom v)))
      (fun i : Fin 1 =>
      @algebraMap _ _ _ _ (AlgebraicGeometry.stalkFunctionFieldAlgebra T₂ (genericPoint T₂))
        ((ι₂.stalkMap (genericPoint T₂)).hom
          (![(ι₁.stalkMap (ι₂ (genericPoint T₂))).hom (z 1),
            (ι₁.stalkMap (ι₂ (genericPoint T₂))).hom v] i.succ)))
      (fun i => by fin_cases i; rfl) m
  · intro h a
    simp only [hresZ, RingHom.comp_apply]
    rw [stalkMap_stalkMap_stalkSpecializes ι₂ ι₁ _ h a]
    exact algebraMap_stalk_genericPoint_apply T₂ _
  · refine ⟨fun C => by simpa using hgen12 C, ?_⟩
    rw [divisorOfForm_heq hsT (heq_formPow_ιMulti_dlog_of_eq hsT (fun _ => resZ v)
      (fun i : Fin 1 => @algebraMap _ _ _ _
        (AlgebraicGeometry.stalkFunctionFieldAlgebra T₂ (genericPoint T₂))
        ((ι₂.stalkMap (genericPoint T₂)).hom
          (![(ι₁.stalkMap (ι₂ (genericPoint T₂))).hom (z 1),
            (ι₁.stalkMap (ι₂ (genericPoint T₂))).hom v] i.succ)))
      (fun i => by fin_cases i; rfl) 1)]
    exact isPullback_of_hom_eq (by simp) hpb12
  · have hdlt₂ := isDltPair_of_isAdjunctionStep hdlt₁ hpair2 h₂ Z₁ (by rw [hB1Z]) hr₂
    rw [hsT]; exact hdlt₂
  · intro m hm K hK hKc hcart ω hω g hωg
    letI := functionFieldAlgebra (ι₂ ≫ ι₁ ≫ sX)
    have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    have hra := hres1 g m
    rw [hfun] at hra
    rw [hωg] at hω
    obtain ⟨d₁, K₁, hK₁, hK₁c⟩ := hcart (.step (.refl hpair) ι₁ B₁ h₁)
    have hK₁' : K₁.IsCanonicalDivisor (ι₁ ≫ sX) d₁ := by simpa using hK₁
    have hd₁' : d₁ = 2 := by
      have := hK₁'.topologicalKrullDim_eq
      rw [hd₁] at this
      exact_mod_cast this.symm
    subst hd₁'
    have hρbmem := mem_logPluricanonicalSections_of_isPoincareResidue_two hX hd
      (fun P => hdlt.2.1 P) hK ⟨_, hm0, hKc⟩ h₁' hT₁nv hd₁ (fun P => hdlt₁.2.1 P) hK₁'
      ⟨_, hm0, hK₁c⟩ h₂' hm hω hra (hres2 ((ι₁.stalkMap (ι₂ (genericPoint T₂))).hom g) m)
    refine mem_logPluricanonicalSections_of_heq hsT.symm ?_ hρbmem
    simp only [hresZ, RingHom.comp_apply]
    exact (heq_smul_formPow_ιMulti_dlog_of_eq hsT
      (@algebraMap _ _ _ _ (AlgebraicGeometry.stalkFunctionFieldAlgebra T₂ (genericPoint T₂))
        ((ι₂.stalkMap (genericPoint T₂)).hom ((ι₁.stalkMap (ι₂ (genericPoint T₂))).hom g)))
      (fun _ => @algebraMap _ _ _ _
        (AlgebraicGeometry.stalkFunctionFieldAlgebra T₂ (genericPoint T₂))
        ((ι₂.stalkMap (genericPoint T₂)).hom ((ι₁.stalkMap (ι₂ (genericPoint T₂))).hom v)))
      (fun i : Fin 1 =>
      @algebraMap _ _ _ _ (AlgebraicGeometry.stalkFunctionFieldAlgebra T₂ (genericPoint T₂))
        ((ι₂.stalkMap (genericPoint T₂)).hom
          (![(ι₁.stalkMap (ι₂ (genericPoint T₂))).hom (z 1),
            (ι₁.stalkMap (ι₂ (genericPoint T₂))).hom v] i.succ)))
      (fun i => by fin_cases i; rfl) m).symm

/-- A point of an integral scheme whose stalk is a field is the generic point. -/
private theorem eq_genericPoint_of_isField_stalk {Y : Scheme.{0}} [IsIntegral Y] {y : Y}
    (h : IsField (Y.presheaf.stalk y)) : y = genericPoint Y := by
  letI := h.toField
  have h0 : ringKrullDim (Y.presheaf.stalk y) = 0 := ringKrullDim_eq_zero_of_field _
  rw [ringKrullDim_stalk_eq_coheight] at h0
  have h1 : Order.coheight y = 0 := by exact_mod_cast h0
  rw [Order.coheight_eq_zero] at h1
  have h2 : y ≤ genericPoint Y :=
    (Scheme.le_iff_specializes).2 ((genericPoint_spec Y).specializes trivial)
  exact ((Scheme.le_iff_specializes).1 (h1 h2)).antisymm
    ((Scheme.le_iff_specializes).1 h2) |>.eq

/-- **Crepancy of the identification of a curve stratum with the centre of an lc place.** Let
`σ : (X, B) ⇢ (X', B')` be a crepant birational map of normal threefolds proper over `k`, `T ⊂ X`
a floor divisor `P` whose valuation is that of a divisor `D` over `X'` with centre the generic
point `x` of a curve, and `τ'` a rational top form on `X'` with `div τ' + B' = 0` near `x`. Let
`ρ` be the residue of `σ^*τ'` along `T`, `T_C ⊂ T` a floor curve `C` along which `ρ` has a simple
pole with residue `θ_C`, and `T_Z ⟶ X'` a closed stratum through `x` on which `div τ' + B'`
restricts to `div θ_Z + B_Z`. If `λ : k(T_Z) → k(T)` is induced by `σ`, lands in `𝒪_{T,C}^×`, and
`φ : k(T_Z) ≅ k(T_C)` is `λ` followed by restriction to `C`, with `φ^*θ_Z = θ_C`, then `φ` is a
crepant birational map `(T_C, B_C) ⇢ (T_Z, B_Z)`: on the normalization `N` of the strict
transform of `C` on the normalization of the strict transform of `T` on a common model `W`, both
adjoint divisors pull back to the restriction of `p^*(K_X + B) = q^*(K_{X'} + B')`. -/
private theorem isCrepantBirationalMap_of_residue_curve {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k]
    {X X' T TC TZ : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsProper sX] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    [LocallyOfFiniteType sX'] [IsProper sX']
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX')
    (hn : topologicalKrullDim X = (3 : ℕ)) (hn' : topologicalKrullDim X' = (3 : ℕ))
    {B : QDivisor X} {B' : QDivisor X'} {K : Divisor X} {K' : Divisor X'}
    (hK : K.IsCanonicalDivisor sX 3) (hK' : K'.IsCanonicalDivisor sX' 3)
    (hKB : (Divisor.toQDivisor K + B).IsQCartier) (hKB' : (Divisor.toQDivisor K' + B').IsQCartier)
    (σ : FunctionFieldEquiv sX sX') (hσ : IsCrepantBirationalMap sX sX' B B' σ)
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    {ι : T ⟶ X} [IsClosedImmersion ι] {BT : QDivisor T} (hι : IsAdjunctionStep sX B ι BT)
    (P : Mori.PrimeDivisor X) (hrP : Set.range ι.base = (P.support : Set X))
    (hP1 : B.coeff P = 1) (D : DivisorOver k sX')
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g))
    {τ' : RationalPluriForms sX' 3 1} (hτ'0 : τ' ≠ 0) (U : X'.Opens)
    (hxU : D.f D.E.genericPoint ∈ U)
    (hU : ∀ E : Mori.PrimeDivisor X', (E.support ∩ (U : Set X')).Nonempty →
      (Divisor.toQDivisor (divisorOfForm τ') + B').coeff E = 0)
    {ρ : RationalPluriForms (ι ≫ sX) 2 1}
    (hρres : IsPoincareResidue sX ι 2 1 (pluriformPullback sX sX' σ.toHom 3 1 τ') ρ)
    [IsIntegral TC] [IsLocallyNoetherian TC] [IsNormal TC] [CompactSpace TC]
    {jC : TC ⟶ T} [IsClosedImmersion jC] {BC : QDivisor TC}
    (hjC : IsAdjunctionStep (ι ≫ sX) BT jC BC) (C : Mori.PrimeDivisor T)
    (hrC : Set.range jC.base = (C.support : Set T)) (hρC : C.ordForm ρ = -1)
    {θC : RationalPluriForms (jC ≫ ι ≫ sX) 1 1} (hθC : IsPoincareResidue (ι ≫ sX) jC 1 1 ρ θC)
    [IsIntegral TZ] [IsLocallyNoetherian TZ] [IsNormal TZ] [CompactSpace TZ]
    {ιZ : TZ ⟶ X'} [IsClosedImmersion ιZ] {BZ : QDivisor TZ}
    (hZ : IsNormalVariety k (ιZ ≫ sX')) (hdZ : topologicalKrullDim TZ = (1 : ℕ))
    (hZη : ιZ (genericPoint TZ) = D.f D.E.genericPoint)
    {θZ : RationalPluriForms (ιZ ≫ sX') 1 1} (hθZ0 : θZ ≠ 0)
    (hpbZ : ∃ hgen, (Divisor.toQDivisor (divisorOfForm τ') + B').IsPullback ιZ hgen
      (Divisor.toQDivisor (divisorOfForm θZ) + BZ))
    (lam : TZ.functionField →+* T.functionField)
    (ψ : X'.presheaf.stalk (ιZ (genericPoint TZ)) →+* X.presheaf.stalk (ι (genericPoint T)))
    (hψ : ∀ a, algebraMap _ X.functionField (ψ a) = (σ.toHom) (algebraMap _ X'.functionField a))
    (hlam : ∀ a, lam ((ιZ.stalkMap (genericPoint TZ)).hom a) =
      (ι.stalkMap (genericPoint T)).hom (ψ a))
    (hlamC : ∀ c, c ≠ 0 → C.divisorialValuation (lam c) = 1)
    (μ3 : TZ.functionField →+* T.presheaf.stalk (jC (genericPoint TC)))
    (hμ3 : ∀ c, algebraMap _ T.functionField (μ3 c) = lam c)
    {sC : TC ⟶ Spec (.of k)} (hsC : jC ≫ ι ≫ sX = sC)
    (φ : FunctionFieldEquiv sC (ιZ ≫ sX'))
    (hφ : ∀ c, φ c = (jC.stalkMap (genericPoint TC)).hom (μ3 c))
    (hθ : HEq θC (pluriformPullback sC (ιZ ≫ sX') φ.toHom 1 1 θZ)) :
    IsCrepantBirationalMap sC (ιZ ≫ sX') BC BZ φ := by
  classical
  subst hsC
  have hθ' := eq_of_heq hθ
  have hT := hι.1
  haveI : LocallyOfFiniteType (ι ≫ sX) := hT.1.toLocallyOfFiniteType
  have hdT : topologicalKrullDim T = (2 : ℕ) :=
    topologicalKrullDim_eq_of_range_eq_support sX ι P hrP hn
  have hTC := hjC.1
  haveI : LocallyOfFiniteType (jC ≫ ι ≫ sX) := hTC.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (ιZ ≫ sX') := hZ.1.toLocallyOfFiniteType
  have hdC : topologicalKrullDim TC = (1 : ℕ) :=
    topologicalKrullDim_eq_of_range_eq_support (ι ≫ sX) jC C hrC hdT
  set τ := pluriformPullback sX sX' σ.toHom 3 1 τ' with hτdef
  have hτ0 : τ ≠ 0 := by
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra sX'
    intro h0
    apply hτ'0
    have e := pluriformPullback_comp (sX := sX') (sX' := sX) (sX'' := sX') hn' hn hn' 1
      (FunctionFieldEquiv.toHom sX' sX σ.symm) σ.toHom τ'
    have h1 : (FunctionFieldEquiv.toHom sX' sX σ.symm).comp σ.toHom =
        FunctionFieldEquiv.toHom sX' sX' 1 := by
      ext a
      exact σ.symm_apply_apply a
    rw [← hτdef, h0, map_zero, h1, pluriformPullback_one hn'] at e
    exact e.symm
  have hD : (Divisor.toQDivisor (divisorOfForm τ) + B).IsQCartier :=
    hKB.add_of_linearlyEquivalent (by
      simpa using (MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK hτ0).symm)
  have hD' : (Divisor.toQDivisor (divisorOfForm τ') + B').IsQCartier :=
    hKB'.add_of_linearlyEquivalent (by
      simpa using (MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX' hK' hτ'0).symm)
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
  -- `G` vanishes near every point of `W` over `U`
  have hGU : ∀ E : Mori.PrimeDivisor W, (E.support ∩ q ⁻¹ᵁ U).Nonempty → G.coeff E = 0 := by
    intro E hE
    rw [show G = QDivisor.pullback _ hD' hgenG' from hGG']
    exact coeff_eq_zero_of_isPullback_of_forall hD' hG' U hU E hE
  -- the strict transform `Q` of `P` on `W` lies over `x`
  obtain ⟨Q, V, hQP, hPV, hViso, hQv⟩ := exists_primeDivisor_map_genericPoint_eq hX p hpb hWp P
  have hqQ : q Q.genericPoint = D.f D.E.genericPoint := by
    let D1 : DivisorOver k sX' := ⟨W, q, hWq, hqB, Q⟩
    have hv : D1.valuation = D.valuation := by
      ext g
      change Q.divisorialValuation (functionFieldMap q g) = _
      rw [hcompat', hQv, hDv]
    exact MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX'.1 hv
  have hGQ : G.coeff Q = 0 := hGU Q ⟨Q.genericPoint, by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
    show q Q.genericPoint ∈ U by rw [hqQ]; exact hxU⟩
  have hpiso : IsIso (p.stalkMap Q.genericPoint) :=
    MMP.isIso_stalkMap_of_mem_biregularLocus p
      (le_biregularLocus (f := p) (V := V) hViso (by rw [hQP]; exact hPV))
  have hτP : P.ordForm τ = -1 := by
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy
      (⟨hX, 3, K, hK, hKB⟩ : Mori.IsPair sX B) (isCanonicalDivisor_divisorOfForm hX hn hτ0)
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
    have hordQ : Q.ordForm (pullbackRationalPluriForms sX p τ) = P.ordForm τ :=
      MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p hpB.functionFieldMap_bijective
        (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn) Q P hQP τ
    rw [hordQ, hc', hGQ, hP1] at he
    have : ((P.ordForm τ : ℤ) : ℝ) = -1 := by push_cast at he ⊢; linarith
    exact_mod_cast this
  obtain ⟨hgenT, hpbT⟩ := hι.isPullback_divisorOfForm_add_of_isPoincareResidue (n := 2)
    (by rw [hn]; norm_cast) P hrP τ hτ0 hτP ρ hρres hD
  -- the normalization `νQ : NQ ⟶ W` of `Q`, and the lifts `αQ : NQ ⟶ T`, `βQ : NQ ⟶ T_Z`
  obtain ⟨NQ, _, νQ, hNv, hνP, hνη, hνsurj⟩ := exists_normalization_primeDivisor' hWp Q
  haveI := hνP
  haveI : IsNormal NQ := hNv.2
  have hιη := map_genericPoint_eq_of_range_eq ι P hrP
  have hpν : p (νQ (genericPoint NQ)) = ι (genericPoint T) := by rw [hνη, hQP, hιη]
  have hqν : q (νQ (genericPoint NQ)) = ιZ (genericPoint TZ) := by rw [hνη, hqQ, hZη]
  obtain ⟨αQ, hαQ⟩ := exists_comp_eq_of_range_subset ι (νQ ≫ p)
    (range_comp_subset_of_map_genericPoint νQ p ι P hrP (by rw [hpν, hιη]))
  have hrangeβ : Set.range (νQ ≫ q).base ⊆ Set.range ιZ.base := by
    rintro _ ⟨z, rfl⟩
    have hz : genericPoint NQ ⤳ z := (genericPoint_spec NQ).specializes trivial
    have h2 := hz.map (νQ ≫ q).base.hom.continuous
    change (νQ ≫ q) (genericPoint NQ) ⤳ (νQ ≫ q) z at h2
    rw [Scheme.Hom.comp_apply, hqν] at h2
    exact h2.mem_closed ιZ.isClosedEmbedding.isClosed_range ⟨_, rfl⟩
  obtain ⟨βQ, hβQ⟩ := exists_comp_eq_of_range_subset ιZ (νQ ≫ q) hrangeβ
  have hαQη : αQ (genericPoint NQ) = genericPoint T := ι.isClosedEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hαQ, Scheme.Hom.comp_apply, hpν])
  have hβQη : βQ (genericPoint NQ) = genericPoint TZ := ιZ.isClosedEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hβQ, Scheme.Hom.comp_apply, hqν])
  haveI : IsDominant αQ := ⟨Dense.mono (s₁ := {genericPoint T})
    (Set.singleton_subset_iff.mpr ⟨_, hαQη⟩) (dense_iff_closure_eq.mpr (genericPoint_spec T))⟩
  haveI : IsDominant βQ := ⟨Dense.mono (s₁ := {genericPoint TZ})
    (Set.singleton_subset_iff.mpr ⟨_, hβQη⟩) (dense_iff_closure_eq.mpr (genericPoint_spec TZ))⟩
  haveI : IsNoetherian T := {}
  have hpiso' : IsIso (p.stalkMap (νQ (genericPoint NQ))) := by rw [hνη]; exact hpiso
  have hαQs := surjective_functionFieldMap_of_lift p ι νQ αQ hαQ hpν hpiso' hνsurj
  haveI : IsProper αQ := by
    have : IsProper (αQ ≫ ι) := by rw [hαQ]; infer_instance
    exact IsProper.of_comp αQ ι
  haveI : IsProper βQ := by
    have : IsProper (βQ ≫ ιZ) := by rw [hβQ]; infer_instance
    exact IsProper.of_comp βQ ιZ
  have hαQb : IsBirational αQ := isBirational_of_surjective_functionFieldMap αQ hαQs
  have hsN : αQ ≫ ι ≫ sX = νQ ≫ p ≫ sX := by rw [← Category.assoc, hαQ, Category.assoc]
  have hNα : IsNormalVariety k (αQ ≫ ι ≫ sX) := hsN ▸ hNv
  haveI : LocallyOfFiniteType (αQ ≫ ι ≫ sX) := hNα.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian NQ := LocallyOfFiniteType.isLocallyNoetherian (αQ ≫ ι ≫ sX)
  haveI : CompactSpace NQ := by
    have := hNα.1
    exact QuasiCompact.compactSpace_of_compactSpace (αQ ≫ ι ≫ sX)
  -- `βQ^* = αQ^* ∘ λ`
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra sX'
  have hαβQ : functionFieldMap βQ = (functionFieldMap αQ).comp lam :=
    functionFieldMap_eq_comp_of_stalkMap (σ.toHom).toRingHom p q hcompat ι ιZ ψ hψ lam hlam
      νQ αQ βQ hαQ hβQ (by rw [hpν]) (by rw [hqν])
  -- `HQ = (νQ ≫ p)^*(div τ + B)`, computed through `T` and through `W`
  have hDP : (Divisor.toQDivisor (divisorOfForm τ) + B).coeff P = 0 := by
    rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hτP, hP1]
    norm_num
  have hgenH : ∀ Z : irreducibleComponents NQ,
      (νQ ≫ p) (componentGenericPoint NQ Z) ∉ (Divisor.toQDivisor (divisorOfForm τ) + B).supp := by
    intro Z
    rw [componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply, hpν, hιη]
    exact genericPoint_notMem_supp_of_coeff_eq_zero hDP
  have hH := QDivisor.isPullback_pullback hD hgenH
  set HQ := QDivisor.pullback _ hD hgenH
  have hqT := isQCartier_of_isPullback hD hpbT
  have hgenα := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' αQ
    (Divisor.toQDivisor (divisorOfForm ρ) + BT)
  have hEα := QDivisor.isPullback_pullback hqT hgenα
  have hHα : HQ = QDivisor.pullback _ hqT hgenα :=
    (QDivisor.IsQCartier.existsUnique_isPullback hD hgenH).unique hH
      (isPullback_of_hom_eq hαQ (qDivisor_isPullback_comp' ι αQ hpbT hEα
        (by rw [hαQ]; exact hgenH)))
  have hgenν : ∀ Z : irreducibleComponents NQ, νQ (componentGenericPoint NQ Z) ∉ G.supp := by
    intro Z
    rw [componentGenericPoint_eq_genericPoint, hνη]
    exact genericPoint_notMem_supp_of_coeff_eq_zero hGQ
  have hqG := isQCartier_of_isPullback hD hG
  have hHν := QDivisor.isPullback_pullback hqG hgenν
  have hHHν : HQ = QDivisor.pullback _ hqG hgenν :=
    (QDivisor.IsQCartier.existsUnique_isPullback hD hgenH).unique hH
      (qDivisor_isPullback_comp' p νQ hG hHν hgenH)
  -- the pull-back of `div τ' + B'` to `NQ` is `HQ`, and `HQ` vanishes over `U`
  have hgenν' : ∀ Z : irreducibleComponents NQ,
      νQ (componentGenericPoint NQ Z) ∉ (QDivisor.pullback _ hD' hgenG').supp := by
    rw [← hGG']; exact hgenν
  have hgenH' : ∀ Z : irreducibleComponents NQ,
      (νQ ≫ q) (componentGenericPoint NQ Z) ∉ (Divisor.toQDivisor (divisorOfForm τ') + B').supp := by
    intro Z hZ
    obtain ⟨E, hE, hzE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
    rw [componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply, hqν, hZη] at hzE
    exact hE (hU E ⟨_, hzE, hxU⟩)
  have hH' : (Divisor.toQDivisor (divisorOfForm τ') + B').IsPullback (νQ ≫ q) hgenH' HQ := by
    rw [hHHν]
    exact qDivisor_isPullback_comp' q νQ hG' (isPullback_of_eq_source (h₂ := hgenν') hGG' hHν)
      hgenH'
  -- the strict transform `CQ` of `C` on `NQ` lies over `x`
  obtain ⟨CQ, V2, hCQC, hCV2, hV2iso, hCQv⟩ :=
    exists_primeDivisor_map_genericPoint_eq hT αQ hαQb hNα C
  have hjCη : jC (genericPoint TC) = C.genericPoint := map_genericPoint_eq_of_range_eq jC C hrC
  have hkeyβ : ∀ a : TZ.presheaf.stalk (βQ CQ.genericPoint),
      algebraMap _ NQ.functionField ((βQ.stalkMap CQ.genericPoint).hom a) =
        functionFieldMap βQ (algebraMap _ TZ.functionField a) := by
    intro a
    have e1 := congrArg (fun f => f.hom a)
      (stalkSpecializes_stalkMap_algebraMap βQ CQ.genericPoint _ (specializes_refl _))
    rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at e1
    exact e1
  have hw' : βQ CQ.genericPoint = genericPoint TZ := by
    apply eq_genericPoint_of_isField_stalk
    refine ⟨⟨0, 1, zero_ne_one⟩, fun a b => mul_comm a b, fun {a} ha => ?_⟩
    have ha' : algebraMap _ TZ.functionField a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha
    have hv : CQ.divisorialValuation
        (algebraMap _ NQ.functionField ((βQ.stalkMap CQ.genericPoint).hom a)) = 1 := by
      rw [hkeyβ, hαβQ, RingHom.comp_apply, hCQv]
      exact hlamC _ ha'
    have hu : IsUnit ((βQ.stalkMap CQ.genericPoint).hom a) := by
      by_contra hnu
      have h1 := (mem_maximalIdeal_iff_divisorialValuation_lt_one CQ rfl _).1
        ((IsLocalRing.mem_maximalIdeal _).2 hnu)
      rw [hv] at h1
      exact lt_irrefl _ h1
    exact (isUnit_of_map_unit _ a hu).exists_right_inv
  -- the normalization `νC : N ⟶ NQ` of `CQ` and the lifts `α : N ⟶ T_C`, `β : N ⟶ T_Z`
  obtain ⟨N, _, νC, hNCv, hνCP, hνCη, hνCsurj⟩ := exists_normalization_primeDivisor' hNα CQ
  haveI := hνCP
  haveI : IsNormal N := hNCv.2
  have hαν : αQ (νC (genericPoint N)) = jC (genericPoint TC) := by rw [hνCη, hCQC, hjCη]
  obtain ⟨α, hα⟩ := exists_comp_eq_of_range_subset jC (νC ≫ αQ)
    (range_comp_subset_of_map_genericPoint νC αQ jC C hrC (by rw [hαν, hjCη]))
  have hαη : α (genericPoint N) = genericPoint TC := jC.isClosedEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hα, Scheme.Hom.comp_apply, hαν])
  obtain ⟨β, hβdef⟩ : ∃ β : N ⟶ TZ, β = νC ≫ βQ := ⟨_, rfl⟩
  have hβη : β (genericPoint N) = genericPoint TZ := by
    rw [hβdef, Scheme.Hom.comp_apply, hνCη, hw']
  haveI : IsDominant α := ⟨Dense.mono (s₁ := {genericPoint TC})
    (Set.singleton_subset_iff.mpr ⟨_, hαη⟩) (dense_iff_closure_eq.mpr (genericPoint_spec TC))⟩
  haveI : IsDominant β := ⟨Dense.mono (s₁ := {genericPoint TZ})
    (Set.singleton_subset_iff.mpr ⟨_, hβη⟩) (dense_iff_closure_eq.mpr (genericPoint_spec TZ))⟩
  have hpiso2 : IsIso (αQ.stalkMap (νC (genericPoint N))) :=
    MMP.isIso_stalkMap_of_mem_biregularLocus αQ
      (le_biregularLocus (f := αQ) (V := V2) hV2iso (by rw [hνCη, hCQC]; exact hCV2))
  have hαs := surjective_functionFieldMap_of_lift αQ jC νC α hα hαν hpiso2 hνCsurj
  haveI : IsProper α := by
    have : IsProper (α ≫ jC) := by rw [hα]; infer_instance
    exact IsProper.of_comp α jC
  haveI : IsProper β := by rw [hβdef]; infer_instance
  -- `β^* = α^* ∘ φ`
  letI := functionFieldAlgebra (jC ≫ ι ≫ sX)
  letI := functionFieldAlgebra (ιZ ≫ sX')
  have hψ2 : ∀ a, algebraMap _ T.functionField
      ((μ3.comp ((𝟙 TZ : TZ ⟶ TZ).stalkMap (genericPoint TZ)).hom) a) =
        lam (algebraMap _ TZ.functionField a) := by
    intro a
    rw [RingHom.comp_apply, hμ3]
    congr 1
    rw [Scheme.Hom.stalkMap_id]
    simp only [CommRingCat.hom_id, RingHom.id_apply]
    change a = (TZ.presheaf.stalkSpecializes _).hom a
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  have hαβ : functionFieldMap β = (functionFieldMap α).comp φ.toRingEquiv.toRingHom :=
    functionFieldMap_eq_comp_of_stalkMap lam αQ βQ hαβQ jC (𝟙 TZ)
      (μ3.comp ((𝟙 TZ : TZ ⟶ TZ).stalkMap (genericPoint TZ)).hom) hψ2 φ.toRingEquiv.toRingHom
      (fun a => hφ _) νC α β hα (by rw [hβdef, Category.comp_id]) (by rw [hαν])
      (by rw [hνCη, hw']; exact specializes_rfl)
  -- `N` as a normal variety over `k`, of dimension one
  have hsN2 : α ≫ jC ≫ ι ≫ sX = νC ≫ αQ ≫ ι ≫ sX := by rw [← Category.assoc, hα, Category.assoc]
  have hsβ : β ≫ ιZ ≫ sX' = α ≫ jC ≫ ι ≫ sX := by
    rw [hsN2, hβdef, Category.assoc, ← Category.assoc βQ, hβQ, Category.assoc, ← hpq, hsN]
  have hNα' : IsNormalVariety k (α ≫ jC ≫ ι ≫ sX) := hsN2 ▸ hNCv
  have hNβ : IsNormalVariety k (β ≫ ιZ ≫ sX') := hsβ ▸ hNα'
  haveI : LocallyOfFiniteType (α ≫ jC ≫ ι ≫ sX) := hNα'.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (β ≫ ιZ ≫ sX') := hNβ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian (α ≫ jC ≫ ι ≫ sX)
  haveI : CompactSpace N := by
    have := hNα'.1
    exact QuasiCompact.compactSpace_of_compactSpace (α ≫ jC ≫ ι ≫ sX)
  haveI : IsNoetherian TC := {}
  haveI : IsNoetherian TZ := {}
  have hαbij : Function.Bijective (functionFieldMap α) := ⟨(functionFieldMap α).injective, hαs⟩
  have hβbij : Function.Bijective (functionFieldMap β) := by
    rw [hαβ]
    exact hαbij.comp φ.bijective
  have hαB : IsBirationalMorphism α :=
    isBirationalMorphism_of_isBirational' α (isBirational_of_surjective_functionFieldMap α hαs)
  have hβB : IsBirationalMorphism β :=
    isBirationalMorphism_of_isBirational' β (isBirational_of_surjective_functionFieldMap β hβbij.2)
  haveI := hTC.1
  haveI := hZ.1
  haveI := hNα'.1
  haveI := hNβ.1
  have hdN : topologicalKrullDim N = (1 : ℕ) :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (jC ≫ ι ≫ sX)
      (α ≫ jC ≫ ι ≫ sX) hαB).symm.trans hdC
  have hdNβ : topologicalKrullDim N = (1 : ℕ) :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (ιZ ≫ sX')
      (β ≫ ιZ ≫ sX') hβB).symm.trans hdZ
  -- the adjunction step along `C`
  have hρ0 : ρ ≠ 0 := by
    intro h0
    rw [h0, Mori.PrimeDivisor.ordForm_zero] at hρC
    exact absurd hρC (by decide)
  have hBC1 := hjC.coeff_eq_one hrC
  have hDC : (Divisor.toQDivisor (divisorOfForm ρ) + BT).coeff C = 0 := by
    rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hρC, hBC1]
    norm_num
  obtain ⟨hgenC, hpbC⟩ := hjC.isPullback_divisorOfForm_add_of_isPoincareResidue (n := 1)
    (by rw [hdT]; norm_cast) C hrC ρ hρ0 hρC θC hθC hqT
  have hqTC := isQCartier_of_isPullback hqT hpbC
  obtain ⟨hgenZ, hpbZ'⟩ := hpbZ
  have hqZ := isQCartier_of_isPullback hD' hpbZ'
  -- `H = νC^* HQ`, computed through `T_C` and through `T_Z`
  have hHQC : HQ.coeff CQ = 0 :=
    coeff_eq_zero_of_isPullback_of_forall hD' hH' U hU CQ ⟨CQ.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
      show (νQ ≫ q) CQ.genericPoint ∈ U by
        rw [← hβQ, Scheme.Hom.comp_apply, hw', hZη]; exact hxU⟩
  have hgenνC : ∀ Z : irreducibleComponents N, νC (componentGenericPoint N Z) ∉ HQ.supp := by
    intro Z
    rw [componentGenericPoint_eq_genericPoint, hνCη]
    exact genericPoint_notMem_supp_of_coeff_eq_zero hHQC
  have hqHQ := isQCartier_of_isPullback hD hH
  have hH2 := QDivisor.isPullback_pullback hqHQ hgenνC
  set H2 := QDivisor.pullback _ hqHQ hgenνC
  -- through `T_C`
  have hgenαT : ∀ Z : irreducibleComponents N, (νC ≫ αQ) (componentGenericPoint N Z) ∉
      (Divisor.toQDivisor (divisorOfForm ρ) + BT).supp := by
    intro Z
    rw [componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply, hαν, hjCη]
    exact genericPoint_notMem_supp_of_coeff_eq_zero hDC
  have hHα2 : (Divisor.toQDivisor (divisorOfForm ρ) + BT).IsPullback (νC ≫ αQ) hgenαT H2 :=
    qDivisor_isPullback_comp' αQ νC hEα (isPullback_of_eq_source (h₂ := by
      rw [← hHα]; exact hgenνC) hHα hH2) hgenαT
  have hgenα2 := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' α
    (Divisor.toQDivisor (divisorOfForm θC) + BC)
  have hEα2 := QDivisor.isPullback_pullback hqTC hgenα2
  have hH2α : H2 = QDivisor.pullback _ hqTC hgenα2 :=
    (QDivisor.IsQCartier.existsUnique_isPullback hqT hgenαT).unique hHα2
      (isPullback_of_hom_eq hα (qDivisor_isPullback_comp' jC α hpbC hEα2
        (by rw [hα]; exact hgenαT)))
  -- through `T_Z`
  have hgenβT : ∀ Z : irreducibleComponents N, (νC ≫ νQ ≫ q) (componentGenericPoint N Z) ∉
      (Divisor.toQDivisor (divisorOfForm τ') + B').supp := by
    intro Z hZ
    obtain ⟨E, hE, hzE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
    rw [componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply, hνCη,
      ← hβQ, Scheme.Hom.comp_apply, hw', hZη] at hzE
    exact hE (hU E ⟨_, hzE, hxU⟩)
  have hHβ2 : (Divisor.toQDivisor (divisorOfForm τ') + B').IsPullback (νC ≫ νQ ≫ q) hgenβT H2 :=
    qDivisor_isPullback_comp' (νQ ≫ q) νC hH' hH2 hgenβT
  have hgenβ2 := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' β
    (Divisor.toQDivisor (divisorOfForm θZ) + BZ)
  have hEβ2 := QDivisor.isPullback_pullback hqZ hgenβ2
  have hβιZ : β ≫ ιZ = νC ≫ νQ ≫ q := by rw [hβdef, Category.assoc, hβQ]
  have hH2β : H2 = QDivisor.pullback _ hqZ hgenβ2 :=
    (QDivisor.IsQCartier.existsUnique_isPullback hD' hgenβT).unique hHβ2
      (isPullback_of_hom_eq hβιZ (qDivisor_isPullback_comp' ιZ β hpbZ' hEβ2
        (by rw [hβιZ]; exact hgenβT)))
  -- the forms `α^*θ_C` and `β^*θ_Z` on `N` have the same divisor
  have hcompatN : ∀ a, functionFieldMap β a = functionFieldMap α ((φ.toHom) a) := fun a => by
    rw [hαβ]
    rfl
  have hθC0 : θC ≠ 0 := by
    intro h0
    apply hθZ0
    have e := pluriformPullback_comp (sX := ιZ ≫ sX') (sX' := jC ≫ ι ≫ sX)
      (sX'' := ιZ ≫ sX') hdZ hdC hdZ 1
      (FunctionFieldEquiv.toHom (ιZ ≫ sX') (jC ≫ ι ≫ sX) φ.symm) φ.toHom θZ
    have h1 : (FunctionFieldEquiv.toHom (ιZ ≫ sX') (jC ≫ ι ≫ sX) φ.symm).comp φ.toHom =
        FunctionFieldEquiv.toHom (ιZ ≫ sX') (ιZ ≫ sX') 1 := by
      ext a
      exact φ.symm_apply_apply a
    rw [← hθ', h0, map_zero, h1, pluriformPullback_one hdZ] at e
    exact e.symm
  have hθα0 : pullbackRationalPluriForms (jC ≫ ι ≫ sX) α θC ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' α hαbij
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := jC ≫ ι ≫ sX) hdC) hθC0
  have hθβ0 : pullbackRationalPluriForms (ιZ ≫ sX') β θZ ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' β hβbij
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := ιZ ≫ sX') hdZ) hθZ0
  have hdivαβ : divisorOfForm (pullbackRationalPluriForms (jC ≫ ι ≫ sX) α θC) =
      divisorOfForm (pullbackRationalPluriForms (ιZ ≫ sX') β θZ) := by
    refine Finsupp.ext fun F => ?_
    change (divisorOfForm _).coeff F = (divisorOfForm _).coeff F
    rw [coeff_divisorOfForm, coeff_divisorOfForm, hθ']
    exact ordForm_pullback_pluriformPullback_eq hTC hZ hdC hdZ φ α β hαB hβB hNα' hNβ hcompatN F
      θZ
  -- the crepant boundary on `N`, and crepancy of `N ⟶ T_C` and of `N ⟶ T_Z`
  set CN : QDivisor N := H2 - Divisor.toQDivisor
    (divisorOfForm (pullbackRationalPluriForms (jC ≫ ι ≫ sX) α θC))
  have hCα : Divisor.toQDivisor (divisorOfForm
      (pullbackRationalPluriForms (jC ≫ ι ≫ sX) α θC)) + CN = H2 := add_sub_cancel _ _
  have hCβ : Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms (ιZ ≫ sX') β θZ)) +
      CN = H2 := by
    rw [← hdivαβ]
    exact hCα
  obtain ⟨eα, heα⟩ := exists_functionFieldEquiv_of_comp_eq (sT := jC ≫ ι ≫ sX) α hαbij rfl
  obtain ⟨eβ, heβ⟩ := exists_functionFieldEquiv_of_comp_eq (sT := ιZ ≫ sX') β hβbij hsβ
  have crepA : IsCrepantBirationalMap (α ≫ jC ≫ ι ≫ sX) (jC ≫ ι ≫ sX) CN BC eα :=
    isCrepantBirationalMap_of_isPullback' hTC α hαB hNα' hθC0
      (isCanonicalDivisor_divisorOfForm hTC hdC hθC0) hθα0
      (isCanonicalDivisor_divisorOfForm hNα' hdN hθα0) hqTC (by rw [hCα, hH2α]; exact hEα2)
      rfl eα heα
  have crepB : IsCrepantBirationalMap (α ≫ jC ≫ ι ≫ sX) (ιZ ≫ sX') CN BZ eβ :=
    isCrepantBirationalMap_of_isPullback' hZ β hβB hNβ hθZ0
      (isCanonicalDivisor_divisorOfForm hZ hdZ hθZ0) hθβ0
      (isCanonicalDivisor_divisorOfForm hNβ hdNβ hθβ0) hqZ (by rw [hCβ, hH2β]; exact hEβ2)
      hsβ eβ heβ
  letI := functionFieldAlgebra (α ≫ jC ≫ ι ≫ sX)
  have hφ' : eβ.trans eα.symm = φ := by
    ext a
    change eα.symm (eβ a) = φ a
    rw [AlgEquiv.symm_apply_eq, heα, heβ, hcompatN]
    rfl
  rw [← hφ']
  exact crepA.symm.trans crepB

/-- Pull-back along a `k`-isomorphism of function fields is injective. -/
private theorem pluriformPullback_injective_of_equiv {k : Type} [Field k] [CharZero k]
    {X X' : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X]
    [IsIntegral X'] [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] {d : ℕ}
    (hX : topologicalKrullDim X = d) (hX' : topologicalKrullDim X' = d)
    (σ : FunctionFieldEquiv sX sX') {m : ℕ} :
    Function.Injective (pluriformPullback sX sX' σ.toHom d m) := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra sX'
  intro a b hab
  have h1 : (FunctionFieldEquiv.toHom sX' sX σ.symm).comp σ.toHom =
      FunctionFieldEquiv.toHom sX' sX' 1 := by
    ext x
    exact σ.symm_apply_apply x
  have ea := pluriformPullback_comp (sX := sX') (sX' := sX) (sX'' := sX') hX' hX hX' m
    (FunctionFieldEquiv.toHom sX' sX σ.symm) σ.toHom a
  have eb := pluriformPullback_comp (sX := sX') (sX' := sX) (sX'' := sX') hX' hX hX' m
    (FunctionFieldEquiv.toHom sX' sX σ.symm) σ.toHom b
  rw [h1, pluriformPullback_one hX'] at ea eb
  rw [← ea, ← eb, hab]

/-- **A divisor over a surface realising a valuation, with a `dlog` frame.** In the situation of
`exists_sncPoint_of_isClosed_center`: there is a proper divisor `E` over `T`, on a model `Y`, whose
valuation is the `ē`-adic valuation `ν₀` and whose centre on `T` is `y₀`, with the identification
`e_D : k(T) ≅ k(Y)`, a lift `μ_E : k(Z) → 𝒪_{Y,E}` of `λ` whose residues exhaust `κ(E)`, a lift
`t_E` of `ē` and the pull-back
`e_D^* (c (dlog ē ∧ dlog λ(v))^N) = e_D(c) (dlog t_E ∧ dlog μ_E(v))^N`; the section `ρ₁` is nonzero
with `ord_E e_D^* ρ₁ = -m`. -/
private theorem exists_properDivisorOver_dlog_frame_of_isClosed_center {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {T TZ : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {sZ : TZ ⟶ Spec (.of k)} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [IsProper sT] [IsIntegral TZ] [IsLocallyNoetherian TZ] [IsNormal TZ] [CompactSpace TZ]
    (hT : IsNormalVariety k sT) (hdT : topologicalKrullDim T = (2 : ℕ)) {m : ℕ} (hm : 0 < m)
    (hZ : IsNormalVariety k sZ) (hdZ : topologicalKrullDim TZ = (1 : ℕ))
    (lam : TZ.functionField →+* T.functionField)
    (hlamk : letI := functionFieldAlgebra sT; letI := functionFieldAlgebra sZ
      ∀ c : k, lam (algebraMap k _ c) = algebraMap k _ c)
    (ν₀ : Valuation T.functionField ℤᵐ⁰) (hν₀k : ∀ c, c ≠ 0 → ν₀ (lam c) = 1)
    (eb : T.functionField) (hν₀e : ν₀ eb = WithZero.exp (-1))
    (hν₀res : ∀ f, ν₀ f ≤ 1 → ∃ c, ν₀ (f - lam c) < 1)
    (hS : letI := functionFieldAlgebra sT
      ∃ (S : Type) (_ : CommRing S) (_ : Algebra k S) (_ : Algebra.EssFiniteType k S)
        (φ : S →ₐ[k] T.functionField), ∀ g, ν₀ g ≤ 1 ↔ g ∈ φ.range)
    (y₀ : T) (hy₀le : ∀ a : T.presheaf.stalk y₀, ν₀ (algebraMap _ T.functionField a) ≤ 1)
    (hy₀lt : ∀ a ∈ IsLocalRing.maximalIdeal (T.presheaf.stalk y₀),
      ν₀ (algebraMap _ T.functionField a) < 1)
    (vZ : TZ.functionField) (hwZ : letI := functionFieldAlgebra sZ
      Submodule.span TZ.functionField {KaehlerDifferential.D k TZ.functionField vZ} = ⊤)
    (c₁ : TZ.functionField) (ρ₁ : RationalPluriForms sT 2 m)
    (hρ₁e : letI := functionFieldAlgebra sT
      ρ₁ = lam c₁ • formPow (exteriorPower.ιMulti T.functionField 2
        ![eb⁻¹ • KaehlerDifferential.D k _ eb, (lam vZ)⁻¹ • KaehlerDifferential.D k _ (lam vZ)]) m)
    (hc₁ : c₁ ≠ 0) :
    letI := functionFieldAlgebra sT
    letI := functionFieldAlgebra sZ
    ∃ D : MMP.Flips.ProperDivisorOver k sT,
      haveI := D.isIntegral
      haveI := D.isNormal
      haveI := D.isLocallyNoetherian
      ∃ eD : FunctionFieldEquiv (D.f ≫ sT) sT,
      letI := functionFieldAlgebra (D.f ≫ sT)
      letI := stalkAlgebra (D.f ≫ sT) D.E.genericPoint
      D.valuation = ν₀ ∧ D.f D.E.genericPoint = y₀ ∧ topologicalKrullDim D.Y = (2 : ℕ) ∧
      (∀ g, ν₀ g = D.E.divisorialValuation (eD g)) ∧
      (∀ g, D.toDivisorOver.valuation g = D.E.divisorialValuation ((eD.toHom) g)) ∧
      ∃ (μE : TZ.functionField →+* D.Y.presheaf.stalk D.E.genericPoint)
        (tE : D.Y.presheaf.stalk D.E.genericPoint),
        (∀ c, algebraMap _ D.Y.functionField (μE c) = eD (lam c)) ∧
        (∀ c : k, μE (algebraMap k _ c) = algebraMap k _ c) ∧
        (∀ a : D.Y.presheaf.stalk D.E.genericPoint,
          ∃ c, IsLocalRing.residue _ (μE c) = IsLocalRing.residue _ a) ∧
        D.E.divisorialValuation (eD eb) = WithZero.exp (-1) ∧
        algebraMap _ D.Y.functionField tE = eD eb ∧ IsUnit (μE vZ) ∧
        (∀ (c : T.functionField) (N : ℕ),
          pluriformPullback (D.f ≫ sT) sT eD.toHom 2 N (c • formPow (exteriorPower.ιMulti
            T.functionField 2 ![eb⁻¹ • KaehlerDifferential.D k _ eb,
              (lam vZ)⁻¹ • KaehlerDifferential.D k _ (lam vZ)]) N) =
          eD c • formPow (exteriorPower.ιMulti D.Y.functionField 2 fun a =>
            (algebraMap (D.Y.presheaf.stalk D.E.genericPoint) D.Y.functionField (![tE, μE vZ] a))⁻¹ •
              KaehlerDifferential.D k D.Y.functionField
                (algebraMap (D.Y.presheaf.stalk D.E.genericPoint) D.Y.functionField
                  (![tE, μE vZ] a))) N) ∧
        ρ₁ ≠ 0 ∧ D.toDivisorOver.ordPullback ρ₁ = -(m : ℤ) := by
  classical
  letI := functionFieldAlgebra sT
  letI := functionFieldAlgebra sZ
  haveI : LocallyOfFiniteType sT := hT.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI := hT.1
  -- the divisor `D` over `T` realizing `ν₀`, centred at `y₀`
  obtain ⟨ebz, -⟩ : ∃ g₀ : T.functionField, ν₀ g₀ = WithZero.exp (-1) := ⟨eb, hν₀e⟩
  obtain ⟨D, hDproj, hDv, hDx⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates_of_essFiniteType sT hS hν₀e y₀
      hy₀le hy₀lt
  -- the model `Y = D.Y` and the identification `e_D : k(T) ≅ k(Y)`
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI := D.isProper
  have hYv : IsNormalVariety k (D.f ≫ sT) := D.isNormalVariety
  haveI : LocallyOfFiniteType (D.f ≫ sT) := hYv.1.toLocallyOfFiniteType
  haveI : CompactSpace D.Y := QuasiCompact.compactSpace_of_compactSpace D.f
  haveI := hYv.1
  have hdY : topologicalKrullDim D.Y = (2 : ℕ) :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sT (D.f ≫ sT)
      D.isBirationalMorphism).symm.trans hdT
  obtain ⟨eD, heD⟩ := exists_functionFieldEquiv_of_comp_eq (sT := sT) D.f
    D.isBirationalMorphism.functionFieldMap_bijective rfl
  letI := functionFieldAlgebra (D.f ≫ sT)
  have hvE : ∀ g, ν₀ g = D.E.divisorialValuation (eD g) := by
    intro g; rw [← hDv, heD]; rfl
  have hvE' : ∀ g, D.toDivisorOver.valuation g = D.E.divisorialValuation ((eD.toHom) g) := by
    intro g; change _ = D.E.divisorialValuation (eD g); rw [heD]; rfl
  -- lifts to the local ring of `Y` along `E`
  have hinjE : Function.Injective
      (algebraMap (D.Y.presheaf.stalk D.E.genericPoint) D.Y.functionField) :=
    IsFractionRing.injective _ _
  have hliftE : ∀ c : TZ.functionField, ∃ a : D.Y.presheaf.stalk D.E.genericPoint,
      algebraMap _ D.Y.functionField a = eD (lam c) := by
    intro c
    refine exists_algebraMap_eq_of_divisorialValuation_le_one D.E rfl ?_
    rw [← hvE]
    by_cases hc : c = 0
    · rw [hc, map_zero, map_zero]; exact zero_le'
    · exact (hν₀k c hc).le
  choose μ' hμ' using hliftE
  let μE : TZ.functionField →+* D.Y.presheaf.stalk D.E.genericPoint :=
    { toFun := μ'
      map_one' := hinjE (by rw [hμ', map_one, map_one, map_one])
      map_mul' := fun a b => hinjE (by rw [map_mul, hμ', hμ', hμ', map_mul, map_mul])
      map_zero' := hinjE (by rw [hμ', map_zero, map_zero, map_zero])
      map_add' := fun a b => hinjE (by rw [map_add, hμ', hμ', hμ', map_add, map_add]) }
  have hμE : ∀ c, algebraMap _ D.Y.functionField (μE c) = eD (lam c) := hμ'
  letI := stalkAlgebra (D.f ≫ sT) D.E.genericPoint
  haveI := isScalarTower_stalk_functionField (D.f ≫ sT) D.E.genericPoint
  have hμEk : ∀ c : k, μE (algebraMap k _ c) = algebraMap k _ c := by
    intro c
    apply hinjE
    rw [hμE, hlamk, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  let μbE : TZ.functionField →ₐ[k] IsLocalRing.ResidueField (D.Y.presheaf.stalk D.E.genericPoint) :=
    { (IsLocalRing.residue (D.Y.presheaf.stalk D.E.genericPoint)).comp μE with
      commutes' := fun c => by
        change IsLocalRing.residue _ (μE (algebraMap k _ c)) = _
        rw [hμEk]; rfl }
  have hμbEs : Function.Surjective μbE := by
    intro r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    have ha : ν₀ (eD.symm (algebraMap _ D.Y.functionField a)) ≤ 1 := by
      rw [hvE, AlgEquiv.apply_symm_apply]
      exact (D.E.divisorialValuation_le_one_iff _).2 ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := hν₀res _ ha
    refine ⟨c, ?_⟩
    change IsLocalRing.residue _ (μE c) = IsLocalRing.residue _ a
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      mem_maximalIdeal_iff_divisorialValuation_lt_one D.E rfl, map_sub, hμE,
      ← Valuation.map_neg, neg_sub]
    rw [hvE, map_sub, AlgEquiv.apply_symm_apply] at hc
    exact hc
  have hwκ := span_D_eq_top_of_surjective μbE hμbEs (fun _ : Fin 1 => vZ)
    (by rw [Set.range_const]; exact hwZ)
  -- a uniformizer `t_E` along `E` and the frame `dt_E, dw_E` at its generic point
  have hebE : D.E.divisorialValuation (eD eb) = WithZero.exp (-1) := by rw [← hvE]; exact hν₀e
  obtain ⟨tE, htE⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one D.E rfl
    (f := eD eb) (by rw [hebE, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  haveI := D.E.isDiscreteValuationRing_localRing
  have hunitE : ∀ a : D.Y.presheaf.stalk D.E.genericPoint,
      D.E.divisorialValuation (algebraMap _ D.Y.functionField a) = 1 → IsUnit a := by
    intro a ha
    by_contra hnu
    have := (mem_maximalIdeal_iff_divisorialValuation_lt_one D.E rfl a).1
      ((IsLocalRing.mem_maximalIdeal _).2 hnu)
    rw [ha] at this; exact lt_irrefl _ this
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible
    (D.Y.presheaf.stalk D.E.genericPoint)
  have hϖv := D.E.divisorialValuation_algebraMap_of_irreducible hϖ
  have hϖ0 : algebraMap _ D.Y.functionField ϖ ≠ 0 := (map_ne_zero_iff _ hinjE).2 hϖ.ne_zero
  obtain ⟨w, hw⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one D.E rfl
    (f := eD eb / algebraMap _ D.Y.functionField ϖ) (by
      rw [map_div₀, hebE, hϖv, div_self (by simp)])
  have hwu : IsUnit w := hunitE w (by rw [hw, map_div₀, hebE, hϖv, div_self (by simp)])
  have htEϖ : tE = w * ϖ := hinjE (by rw [map_mul, hw, htE, div_mul_cancel₀ _ hϖ0])
  have hspan_t : Ideal.span {tE} = IsLocalRing.maximalIdeal (D.Y.presheaf.stalk D.E.genericPoint) := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, htEϖ]
    exact Ideal.span_singleton_mul_left_unit hwu ϖ
  have hEid : IdealSheafData.stalk D.E.idealSheaf D.E.genericPoint = Ideal.span {tE} := by
    rw [MMP.Resolution.Aux.stalk_idealSheaf_genericPoint D.E, hspan_t]
  have htE0 : tE ≠ 0 := fun h0 => by
    rw [h0, map_zero] at htE; rw [← htE, map_zero] at hebE
    exact WithZero.exp_ne_zero hebE.symm
  have hvZ0 : vZ ≠ 0 := by
    rintro rfl
    rw [map_zero, Submodule.span_singleton_eq_bot.2 rfl] at hwZ
    have hnt : Nontrivial (⋀[TZ.functionField]^1 Ω[TZ.functionField⁄k]) := by
      obtain ⟨b⟩ := exists_basis_topForms (sX := sZ) hdZ
      exact nontrivial_of_ne _ _ (b.ne_zero ())
    haveI : Nontrivial Ω[TZ.functionField⁄k] :=
      (exteriorPower.oneEquiv TZ.functionField Ω[TZ.functionField⁄k]).symm.toEquiv.nontrivial
    exact bot_ne_top hwZ
  have hwEu : IsUnit (μE vZ) := hunitE _ (by rw [hμE, ← hvE]; exact hν₀k _ hvZ0)
  have hregE : IsRegularSystemOfParameters (![tE] : Fin 1 → D.Y.presheaf.stalk D.E.genericPoint) := by
    refine ⟨by rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty]; exact hspan_t, ?_⟩
    rw [ringKrullDim_stalk_eq_coheight, D.E.coheight_genericPoint]; rfl
  haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hregE
  have hsmE : D.E.genericPoint ∈ Mori.smoothLocus (D.f ≫ sT) :=
    mem_smoothLocus_of_isRegularLocalRing _ D.E.genericPoint
  obtain ⟨rE, ⟨bE⟩⟩ := exists_basis_kaehler_stalk_of_mem_smoothLocus (D.f ≫ sT) hsmE
  haveI : Module.Finite (D.Y.presheaf.stalk D.E.genericPoint)
      Ω[D.Y.presheaf.stalk D.E.genericPoint⁄k] := Module.Finite.of_basis bE
  have hspanE' := span_D_sum_eq_top_of_span_eq_maximalIdeal (k := k) (![tE] : Fin 1 → _)
    (by rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty]; exact hspan_t)
    (fun _ : Fin 1 => μE vZ) hwκ
  have hspanE : Submodule.span (D.Y.presheaf.stalk D.E.genericPoint) (Set.range fun a : Fin 2 =>
      KaehlerDifferential.D k (D.Y.presheaf.stalk D.E.genericPoint) (![tE, μE vZ] a)) = ⊤ := by
    rw [eq_top_iff, ← hspanE', Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rcases a with (a | a)
    · fin_cases a; exact Submodule.subset_span ⟨0, rfl⟩
    · exact Submodule.subset_span ⟨1, rfl⟩
  have hordE := ordForm_formPow_dlog_eq_of_isUnit (sX := D.f ≫ sT) hdY 1 ![tE, μE vZ]
    (fun a => by fin_cases a; exact htE0; exact hwEu.ne_zero) hspanE {0} (fun _ => D.E)
    (Set.injOn_singleton _ _)
    (fun _ _ => by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
    (fun a ha => by rw [ha]; exact hEid)
    (fun a ha => by
      fin_cases a
      · exact absurd rfl ha
      · exact hwEu) D.E (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
  rw [if_pos ⟨0, rfl, rfl⟩] at hordE
  -- the pull-back of `ω_T` to `Y`
  have hωfun : (![eb⁻¹ • KaehlerDifferential.D k _ eb,
      (lam vZ)⁻¹ • KaehlerDifferential.D k _ (lam vZ)] : Fin 2 → Ω[T.functionField⁄k]) =
      fun a => (![eb, lam vZ] a)⁻¹ • KaehlerDifferential.D k T.functionField (![eb, lam vZ] a) := by
    funext a; fin_cases a <;> rfl
  have hpull : ∀ (c : T.functionField) (N : ℕ),
      pluriformPullback (D.f ≫ sT) sT eD.toHom 2 N (c • formPow (exteriorPower.ιMulti
        T.functionField 2 ![eb⁻¹ • KaehlerDifferential.D k _ eb,
          (lam vZ)⁻¹ • KaehlerDifferential.D k _ (lam vZ)]) N) =
      eD c • formPow (exteriorPower.ιMulti D.Y.functionField 2 fun a =>
        (algebraMap (D.Y.presheaf.stalk D.E.genericPoint) D.Y.functionField (![tE, μE vZ] a))⁻¹ •
          KaehlerDifferential.D k D.Y.functionField
            (algebraMap (D.Y.presheaf.stalk D.E.genericPoint) D.Y.functionField
              (![tE, μE vZ] a))) N := by
    intro c N
    have hfun2 : (fun i => ((FunctionFieldEquiv.toHom _ _ eD) (![eb, lam vZ] i))⁻¹ •
        KaehlerDifferential.D k D.Y.functionField ((FunctionFieldEquiv.toHom _ _ eD)
          (![eb, lam vZ] i))) = fun a =>
        (algebraMap (D.Y.presheaf.stalk D.E.genericPoint) D.Y.functionField (![tE, μE vZ] a))⁻¹ •
          KaehlerDifferential.D k D.Y.functionField
            (algebraMap (D.Y.presheaf.stalk D.E.genericPoint) D.Y.functionField
              (![tE, μE vZ] a)) := by
      funext a; fin_cases a
      · show (eD eb)⁻¹ • KaehlerDifferential.D k D.Y.functionField (eD eb) =
          (algebraMap _ D.Y.functionField tE)⁻¹ •
            KaehlerDifferential.D k D.Y.functionField (algebraMap _ D.Y.functionField tE)
        rw [htE]
      · show (eD (lam vZ))⁻¹ • KaehlerDifferential.D k D.Y.functionField (eD (lam vZ)) =
          (algebraMap _ D.Y.functionField (μE vZ))⁻¹ •
            KaehlerDifferential.D k D.Y.functionField (algebraMap _ D.Y.functionField (μE vZ))
        rw [hμE]
    rw [hωfun, pluriformPullback_smul_formPow_dlog hdY hdT eD.toHom (![eb, lam vZ]) N c, hfun2]
    rfl
  -- `ord_E` of the pulled-back section is `-m`
  have hωY0 : (exteriorPower.ιMulti D.Y.functionField 2 fun a =>
      (algebraMap (D.Y.presheaf.stalk D.E.genericPoint) D.Y.functionField (![tE, μE vZ] a))⁻¹ •
        KaehlerDifferential.D k D.Y.functionField
          (algebraMap (D.Y.presheaf.stalk D.E.genericPoint) D.Y.functionField
            (![tE, μE vZ] a))) ≠ 0 := by
    intro h0
    rw [h0] at hordE
    have : (show RationalPluriForms (D.f ≫ sT) 2 1 from formPow (0 : ⋀[D.Y.functionField]^2
        Ω[D.Y.functionField⁄k]) 1) = 0 := formPow_zero_of_pos one_pos
    rw [this, Mori.PrimeDivisor.ordForm_zero] at hordE
    exact absurd hordE (by decide)
  have hlc1 : eD (lam c₁) ≠ 0 := by
    rw [map_ne_zero]; exact (map_ne_zero lam).2 hc₁
  have hordlc : D.Y.ord (eD (lam c₁)) D.E.genericPoint = 0 := by
    have h2 := D.E.divisorialValuation_eq_exp_neg_ord hlc1
    rw [← hvE, hν₀k c₁ hc₁] at h2
    have h3 : WithZero.exp (0 : ℤ) = WithZero.exp (-D.Y.ord (eD (lam c₁)) D.E.genericPoint) := by
      rw [WithZero.exp_zero]; exact h2
    have := WithZero.exp_injective h3
    omega
  have hY1 : D.E.ordForm (pluriformPullback (D.f ≫ sT) sT eD.toHom 2 m ρ₁) = -(m : ℤ) := by
    rw [hρ₁e, hpull, ordForm_smul_formPow hdY D.E hωY0 hlc1 m, hordlc]
    have := hordE
    change D.E.ordForm (show RationalPluriForms (D.f ≫ sT) 2 1 from formPow _ 1) = -1 at this
    rw [this]; ring
  have hρ₁0 : ρ₁ ≠ 0 := by
    intro h0
    rw [h0, map_zero, Mori.PrimeDivisor.ordForm_zero] at hY1
    have : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    omega
  have hord1 : D.toDivisorOver.ordPullback ρ₁ = -(m : ℤ) := by
    rw [← ordForm_pluriformPullback_eq_ordPullback hYv hT hdY hdT eD D.E D.toDivisorOver hvE' ρ₁]
    exact hY1
  exact ⟨D, eD, hDv, hDx, hdY, hvE, hvE', μE, tE, hμE, hμEk,
    fun a => hμbEs (IsLocalRing.residue _ a), hebE, htE, hwEu, hpull, hρ₁0, hord1⟩

/-- **A horizontal log canonical place centred at a point.** Let `(T, B_T)` be a projective dlt
surface whose function field is `k(T) = K(ē)`, `K = λ(k(Z))` the function field of a curve `Z`,
with `ē` transcendental, and let the `ē`-adic valuation `ν₀` be centred at a closed point `y₀`. If
some section `λ(c) (dlog ē ∧ dlog λ(v))^m` of `m(K_T + B_T)` is nonzero, then `ν₀` is a log
canonical place, so `y₀` is a zero-dimensional stratum with snc coordinates `y₁, y₂`, and the
sections `λ(c_i) (dlog ē ∧ dlog λ(v))^m` are `h_i (dlog y₁ ∧ dlog y₂)^m` with `h_i` regular at
`y₀`; moreover there is a generator `W` of `k(Z)` with `c_i (dlog v)^m = h_i(y₀) (dlog W)^m`. -/
private theorem exists_sncPoint_of_isClosed_center {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {T TZ : Scheme.{0}} {sT : T ⟶ Spec (.of k)} {sZ : TZ ⟶ Spec (.of k)}
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] [IsProper sT]
    [IsIntegral TZ] [IsLocallyNoetherian TZ] [IsNormal TZ] [CompactSpace TZ]
    (hT : IsNormalVariety k sT) (hdT : topologicalKrullDim T = (2 : ℕ))
    {BT : QDivisor T} {KT : Divisor T} (hdlt : MMP.Intersection.IsDltPair sT BT)
    (hKT : KT.IsCanonicalDivisor sT 2) {m : ℕ} (hm : 0 < m)
    (hmK : ((m : ℤ) • (Divisor.toQDivisor KT + BT)).IsCartierDivisor)
    (hZ : IsNormalVariety k sZ) (hdZ : topologicalKrullDim TZ = (1 : ℕ))
    (lam : TZ.functionField →+* T.functionField)
    (hlamk : letI := functionFieldAlgebra sT; letI := functionFieldAlgebra sZ
      ∀ c : k, lam (algebraMap k _ c) = algebraMap k _ c)
    (ν₀ : Valuation T.functionField ℤᵐ⁰) (hν₀k : ∀ c, c ≠ 0 → ν₀ (lam c) = 1)
    (eb : T.functionField) (hν₀e : ν₀ eb = WithZero.exp (-1))
    (hν₀res : ∀ f, ν₀ f ≤ 1 → ∃ c, ν₀ (f - lam c) < 1)
    (hS : letI := functionFieldAlgebra sT
      ∃ (S : Type) (_ : CommRing S) (_ : Algebra k S) (_ : Algebra.EssFiniteType k S)
        (φ : S →ₐ[k] T.functionField), ∀ g, ν₀ g ≤ 1 ↔ g ∈ φ.range)
    (y₀ : T) (hy₀le : ∀ a : T.presheaf.stalk y₀, ν₀ (algebraMap _ T.functionField a) ≤ 1)
    (hy₀lt : ∀ a ∈ IsLocalRing.maximalIdeal (T.presheaf.stalk y₀),
      ν₀ (algebraMap _ T.functionField a) < 1)
    (hcl : IsClosed ({y₀} : Set T)) (hcoh : Order.coheight y₀ = 2)
    (vZ : TZ.functionField) (hwZ : letI := functionFieldAlgebra sZ
      Submodule.span TZ.functionField {KaehlerDifferential.D k TZ.functionField vZ} = ⊤)
    (c₁ : TZ.functionField) (ρ₁ : RationalPluriForms sT 2 m)
    (hρ₁ : ρ₁ ∈ logPluricanonicalSections sT 2 m BT)
    (hρ₁e : letI := functionFieldAlgebra sT
      ρ₁ = lam c₁ • formPow (exteriorPower.ιMulti T.functionField 2
        ![eb⁻¹ • KaehlerDifferential.D k _ eb, (lam vZ)⁻¹ • KaehlerDifferential.D k _ (lam vZ)]) m)
    (hc₁ : c₁ ≠ 0) :
    letI := functionFieldAlgebra sT
    letI := functionFieldAlgebra sZ
    ∃ (y : Fin 2 → T.presheaf.stalk y₀) (L : Fin 2 → Mori.PrimeDivisor T),
      IsRegularSystemOfParameters y ∧ y₀ ∈ Mori.smoothLocus sT ∧ Function.Injective L ∧
      (∀ a, y₀ ∈ (L a).support) ∧
      (∀ a, IdealSheafData.stalk (L a).idealSheaf y₀ = Ideal.span {y a}) ∧
      (∀ E : Mori.PrimeDivisor T, y₀ ∈ E.support → BT.coeff E ≠ 0 → E ∈ Set.range L) ∧
      (∀ a, BT.coeff (L a) = 1) ∧
      (Divisor.toQDivisor (divisorOfForm (show RationalPluriForms sT 2 ((1 : ℕ) : ℤ) from
        formPow (exteriorPower.ιMulti T.functionField 2 fun a =>
          (algebraMap (T.presheaf.stalk y₀) T.functionField (y a))⁻¹ • KaehlerDifferential.D k
            T.functionField (algebraMap (T.presheaf.stalk y₀) T.functionField (y a))) 1)) +
          BT).IsQCartier ∧
      ∃ W : TZ.functionField, IntermediateField.adjoin k ({W} : Set TZ.functionField) = ⊤ ∧
        ∀ (c : TZ.functionField) (ρ : RationalPluriForms sT 2 m),
          ρ ∈ logPluricanonicalSections sT 2 m BT →
          ρ = lam c • formPow (exteriorPower.ιMulti T.functionField 2
            ![eb⁻¹ • KaehlerDifferential.D k _ eb,
              (lam vZ)⁻¹ • KaehlerDifferential.D k _ (lam vZ)]) m →
          ∃ h : T.presheaf.stalk y₀, ρ = algebraMap _ T.functionField h •
            (show RationalPluriForms sT 2 m from formPow (exteriorPower.ιMulti T.functionField 2
              fun a => (algebraMap (T.presheaf.stalk y₀) T.functionField (y a))⁻¹ •
                KaehlerDifferential.D k T.functionField
                  (algebraMap (T.presheaf.stalk y₀) T.functionField (y a))) m) ∧
            ∀ a : k, (letI := stalkAlgebra sT y₀
              h - algebraMap k _ a ∈ IsLocalRing.maximalIdeal (T.presheaf.stalk y₀)) →
              c • (formPow (exteriorPower.ιMulti
                TZ.functionField 1 fun _ => vZ⁻¹ • KaehlerDifferential.D k TZ.functionField vZ) m :
                  RationalPluriForms sZ 1 m) =
              algebraMap k TZ.functionField a • (formPow (exteriorPower.ιMulti TZ.functionField 1
                  fun _ => W⁻¹ • KaehlerDifferential.D k TZ.functionField W) m :
                    RationalPluriForms sZ 1 m) := by
  classical
  letI := functionFieldAlgebra sT
  letI := functionFieldAlgebra sZ
  haveI : LocallyOfFiniteType sT := hT.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI := hT.1
  -- the divisor `D` over `T` realizing `ν₀`, centred at `y₀`, with its `dlog` frame
  obtain ⟨D, eD, hDv, hDx, hdY, hvE, hvE', μE, tE, hμE, hμEk, hμbEs, hebE, htE, hwEu, hpull, hρ₁0,
    hord1⟩ := exists_properDivisorOver_dlog_frame_of_isClosed_center hT hdT hm hZ hdZ lam hlamk ν₀
    hν₀k eb hν₀e hν₀res hS y₀ hy₀le hy₀lt vZ hwZ c₁ ρ₁ hρ₁e hc₁
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI := D.isProper
  have hYv : IsNormalVariety k (D.f ≫ sT) := D.isNormalVariety
  haveI : LocallyOfFiniteType (D.f ≫ sT) := hYv.1.toLocallyOfFiniteType
  haveI : CompactSpace D.Y := QuasiCompact.compactSpace_of_compactSpace D.f
  haveI := hYv.1
  letI := functionFieldAlgebra (D.f ≫ sT)
  letI := stalkAlgebra (D.f ≫ sT) D.E.genericPoint
  haveI := isScalarTower_stalk_functionField (D.f ≫ sT) D.E.genericPoint
  haveI := D.E.isDiscreteValuationRing_localRing
  replace hpull : ∀ (c : T.functionField) (N : ℕ),
      pluriformPullback (D.f ≫ sT) sT eD.toHom 2 N (c • formPow (exteriorPower.ιMulti
        T.functionField 2 ![eb⁻¹ • KaehlerDifferential.D k _ eb,
          (lam vZ)⁻¹ • KaehlerDifferential.D k _ (lam vZ)]) N) =
      eD c • formPow (exteriorPower.ιMulti D.Y.functionField 2 fun a =>
        (algebraMap (D.Y.presheaf.stalk D.E.genericPoint) D.Y.functionField (![tE, μE vZ] a))⁻¹ •
          KaehlerDifferential.D k D.Y.functionField
            (algebraMap (D.Y.presheaf.stalk D.E.genericPoint) D.Y.functionField
              (![tE, μE vZ] a))) N := hpull
  -- `ν₀` is a log canonical place: its discrepancy is `-1`
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hPT : MMP.Mori.IsPair sT BT := ⟨hT, 2, KT, hKT, ⟨m, hm0, hmK⟩⟩
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPT hKT D.toDivisorOver
  have hlc := hdlt.1.2.2 2 D.toDivisorOver (1 + a)
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha D.isProper)
  have ha' : MMP.Mori.IsDiscrepancy sT 2 KT BT D.toDivisorOver (-(-a)) := by simpa using ha
  have hub := ordPullback_add_floor_nonneg hT hKT hm hmK D.toDivisorOver hρ₁ hρ₁0 ha'
  rw [hord1] at hub
  have ha1 : a = -1 := by
    have h1 : (m : ℤ) ≤ ⌊((m : ℤ) • (-a) : ℚ)⌋ := by linarith
    rw [Int.le_floor, zsmul_eq_mul] at h1
    have hmq : (0 : ℚ) < m := by exact_mod_cast hm
    have h2 : (1 : ℚ) ≤ -a := by
      push_cast at h1
      exact le_of_mul_le_mul_left (by linarith) hmq
    have h3 : (-1 : ℝ) ≤ (a : ℝ) := by linarith
    have h4 : (-1 : ℚ) ≤ a := by exact_mod_cast h3
    linarith
  rw [ha1] at ha
  have hPW : MMP.Mori.IsPairWith sT 2 KT BT := ⟨hT, hKT, ⟨m, hm0, hmK⟩⟩
  obtain ⟨c, y, L, α, hy, hL, hLx, hLz, hBL, hL1, hsm, hα, hyv, hmono⟩ :=
    exists_sncCoordinates_of_isDiscrepancy_neg_one hdlt hPW D.toDivisorOver D.isProper ha
  subst hDx
  have hc2 : c = 2 := by
    have h1 := hy.2
    rw [ringKrullDim_stalk_eq_coheight, hcoh] at h1
    have h2 : (((2 : ℕ∞) : WithBot ℕ∞)) = ((c : ℕ∞) : WithBot ℕ∞) := h1
    exact_mod_cast (WithBot.coe_injective h2).symm
  subst hc2
  -- the point `y₀`: residue field `k`, smoothness
  have hresk := exists_sub_mem_maximalIdeal_of_isClosed sT _ hcl
  have hres := surjective_algebraMap_residueField_of_isClosed sT _ hcl
  letI := stalkAlgebra sT (D.f D.E.genericPoint)
  haveI := isScalarTower_stalk_functionField sT (D.f D.E.genericPoint)
  obtain ⟨r0, ⟨b0⟩⟩ := exists_basis_kaehler_stalk_of_mem_smoothLocus sT hsm
  haveI : Module.Finite (T.presheaf.stalk (D.f D.E.genericPoint))
      Ω[T.presheaf.stalk (D.f D.E.genericPoint)⁄k] := Module.Finite.of_basis b0
  have hwy := span_D_eq_top_of_span_eq_maximalIdeal hres y hy.1
  have hy0 : ∀ a, y a ≠ 0 := by
    haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hy
    exact fun a => MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hy a
  -- the reduced divisor `E` and the monomial frame along it
  haveI := D.E.integral
  have hrE : Set.range D.E.idealSheaf.subschemeι.base = (D.E.support : Set D.Y) := by
    rw [Scheme.IdealSheafData.range_subschemeι]
  have hdER : topologicalKrullDim D.E.idealSheaf.subscheme = (1 : ℕ) :=
    topologicalKrullDim_eq_of_range_eq_support (D.f ≫ sT) _ D.E hrE hdY
  letI := functionFieldAlgebra (D.E.idealSheaf.subschemeι ≫ D.f ≫ sT)
  haveI : LocallyOfFiniteType (D.E.idealSheaf.subschemeι ≫ D.f ≫ sT) := inferInstance
  obtain ⟨t, e, he, ht, hfr, hgenE⟩ := exists_monomialFrame_two (sX := D.f ≫ sT) (sX' := sT)
    D.E.idealSheaf.subschemeι D.E rfl eD y α hy0
    (fun r => by rw [← hvE']; change D.valuation _ ≤ 1; rw [hDv]; exact hy₀le r)
    (fun r hr => by rw [← hvE']; change D.valuation _ < 1; rw [hDv]; exact hy₀lt r hr)
    (fun a => by rw [← hvE']; exact hyv a)
    (fun f hf => by
      obtain ⟨M, hM, hMv⟩ := hmono f hf
      exact ⟨M, hM, by rw [← hvE']; exact hMv⟩) hresk
  -- the field isomorphism `χ : k(Z) ≅ k(E)`
  have hφE : ∃ φE : D.Y.presheaf.stalk D.E.genericPoint →+* D.E.idealSheaf.subscheme.functionField,
      φE = (D.E.idealSheaf.subschemeι.stalkMap (genericPoint _)).hom := ⟨_, rfl⟩
  obtain ⟨φE, hφEdef⟩ := hφE
  have hφEs : Function.Surjective φE := by
    rw [hφEdef]; exact D.E.idealSheaf.subschemeι.stalkMap_surjective (genericPoint _)
  have hkerE : ∀ a, φE a = 0 ↔ a ∈ IsLocalRing.maximalIdeal (D.Y.presheaf.stalk D.E.genericPoint) := by
    intro a
    have h1 := ker_stalkMap_eq_stalk_idealSheaf D.E.idealSheaf.subschemeι D.E hrE
      (genericPoint D.E.idealSheaf.subscheme)
    have h2 := MMP.Resolution.Aux.stalk_idealSheaf_genericPoint D.E
    have hker : RingHom.ker φE =
        IsLocalRing.maximalIdeal (D.Y.presheaf.stalk D.E.genericPoint) := by
      rw [hφEdef]; exact h1.trans h2
    rw [← RingHom.mem_ker, hker]
  have hφEk : ∀ c : k, φE (algebraMap k _ c) = algebraMap k D.E.idealSheaf.subscheme.functionField c := by
    intro c; rw [hφEdef]
    exact stalkMap_algebraMap_const (D.f ≫ sT) D.E.idealSheaf.subschemeι _ c
  obtain ⟨χ0, hχ0⟩ : ∃ χ0 : TZ.functionField →+* D.E.idealSheaf.subscheme.functionField,
      χ0 = φE.comp μE := ⟨_, rfl⟩
  have hχ0a : ∀ c, χ0 c = φE (μE c) := fun _ => by rw [hχ0]; rfl
  have hχ0s : Function.Surjective χ0 := by
    intro b
    obtain ⟨a, rfl⟩ := hφEs b
    obtain ⟨c, hc⟩ := hμbEs a
    refine ⟨c, ?_⟩
    rw [hχ0a, ← sub_eq_zero, ← map_sub]
    refine (hkerE _).2 ?_
    have : IsLocalRing.residue _ (μE c) = IsLocalRing.residue _ a := hc
    rwa [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at this
  have hχ0k : ∀ c : k, χ0 (algebraMap k TZ.functionField c) =
      algebraMap k D.E.idealSheaf.subscheme.functionField c := by
    intro c
    rw [hχ0a, hμEk, hφEk]
  obtain ⟨χ, hχ⟩ : ∃ χ : FunctionFieldEquiv (D.E.idealSheaf.subschemeι ≫ D.f ≫ sT) sZ,
      ∀ c, χ c = χ0 c :=
    ⟨AlgEquiv.ofBijective { χ0 with commutes' := hχ0k } ⟨χ0.injective, hχ0s⟩, fun _ => rfl⟩
  obtain ⟨W, hW⟩ := hχ0s (φE (e 0))
  have hWgen : IntermediateField.adjoin k ({W} : Set TZ.functionField) = ⊤ := by
    have h1 : IntermediateField.adjoin k ({χ W} : Set D.E.idealSheaf.subscheme.functionField) =
        ⊤ := by
      rw [← hgenE, hχ, hW, hφEdef]
      congr 1
      ext b
      simp only [Set.mem_singleton_iff, Set.mem_range]
      constructor
      · rintro rfl; exact ⟨0, rfl⟩
      · rintro ⟨i, rfl⟩; fin_cases i; rfl
    rw [eq_top_iff]
    intro x _
    have hx : χ x ∈ IntermediateField.adjoin k ({χ W} : Set _) := by rw [h1]; trivial
    have h2 : IntermediateField.adjoin k ({χ W} : Set D.E.idealSheaf.subscheme.functionField) =
        (IntermediateField.adjoin k ({W} : Set TZ.functionField)).map (χ : _ →ₐ[k] _) := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]; rfl
    rw [h2] at hx
    obtain ⟨y', hy', hyx⟩ := hx
    rw [show y' = x from χ.injective hyx] at hy'
    exact hy'
  have hΘ1 := ordForm_formPow_dlog_eq hdT 1 y hy0 hwy L hL hLx hLz (L 0) (hLx 0)
  rw [if_pos ⟨0, rfl⟩] at hΘ1
  have hΘ0 : (show RationalPluriForms sT 2 ((1 : ℕ) : ℤ) from
      formPow (exteriorPower.ιMulti T.functionField 2 fun a =>
        (algebraMap (T.presheaf.stalk (D.f D.E.genericPoint)) T.functionField (y a))⁻¹ •
          KaehlerDifferential.D k T.functionField
            (algebraMap (T.presheaf.stalk (D.f D.E.genericPoint)) T.functionField (y a))) 1) ≠ 0 := by
    intro h0
    rw [h0, Mori.PrimeDivisor.ordForm_zero] at hΘ1
    exact absurd hΘ1 (by decide)
  have hQy := (show (Divisor.toQDivisor KT + BT).IsQCartier from ⟨_, hm0, hmK⟩).add_of_linearlyEquivalent
    (by simpa using (MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hT hKT hΘ0).symm)
  refine ⟨y, L, hy, hsm, hL, hLx, hLz, hBL, hL1, hQy, W, hWgen, fun c ρ hρ hρe => ?_⟩
  obtain ⟨h, hh⟩ := exists_algebraMap_smul_of_mem_logPluricanonicalSections hdT (by norm_num) y
    hy0 hwy L hL hLx hLz hBL hL1 hm ρ hρ
  refine ⟨h, hh, fun a ha => ?_⟩
  -- the residue of `e_D^*ρ` along `E`, in the frame `dlog t_E ∧ dlog w_E`
  have heb0 : eD eb ≠ 0 := by
    intro h0; rw [h0, map_zero] at hebE; exact WithZero.exp_ne_zero hebE.symm
  have htE1 : D.Y.ord (algebraMap _ D.Y.functionField tE)
      (D.E.idealSheaf.subschemeι (genericPoint D.E.idealSheaf.subscheme)) = 1 := by
    have h2 := D.E.divisorialValuation_eq_exp_neg_ord heb0
    rw [hebE] at h2
    rw [htE]
    have := WithZero.exp_injective h2
    change D.Y.ord (eD eb) D.E.genericPoint = 1
    omega
  have hres1 := isPoincareResidue_formPow_dlog (D.f ≫ sT) D.E.idealSheaf.subschemeι (n := 1) m
    tE ![μE vZ] (fun a => by fin_cases a; exact hwEu) htE1
  have hr1 := IsPoincareResidue.smul_stalk hres1 (μE c)
  have hpull1 : pluriformPullback (D.f ≫ sT) sT eD.toHom 2 m ρ =
      algebraMap _ D.Y.functionField (μE c) •
        formPow (exteriorPower.ιMulti D.Y.functionField (1 + 1)
          (Fin.cons ((algebraMap _ D.Y.functionField tE)⁻¹ •
            KaehlerDifferential.D k D.Y.functionField (algebraMap _ _ tE))
            fun i => (algebraMap _ D.Y.functionField (![μE vZ] i))⁻¹ •
              KaehlerDifferential.D k D.Y.functionField (algebraMap _ _ (![μE vZ] i)))) m := by
    simp only [hρe, hpull, hμE]
    congr 3
    funext a; fin_cases a <;> rfl
  -- and in the frame `dlog t ∧ dlog e` of the monomial frame
  obtain ⟨hE', hhE'⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one D.E rfl
    (f := eD (algebraMap _ T.functionField h)) (by rw [← hvE]; exact hy₀le h)
  have hres2 := isPoincareResidue_formPow_dlog (D.f ≫ sT) D.E.idealSheaf.subschemeι (n := 1) m
    t e he ht
  have hr2 := IsPoincareResidue.smul_stalk hres2 hE'
  have hpull2 : pluriformPullback (D.f ≫ sT) sT eD.toHom 2 m ρ =
      algebraMap _ D.Y.functionField hE' •
        formPow (exteriorPower.ιMulti D.Y.functionField (1 + 1)
          (Fin.cons ((algebraMap _ D.Y.functionField t)⁻¹ •
            KaehlerDifferential.D k D.Y.functionField (algebraMap _ _ t))
            fun i => (algebraMap _ D.Y.functionField (e i))⁻¹ •
              KaehlerDifferential.D k D.Y.functionField (algebraMap _ _ (e i)))) m := by
    have hh' : ρ = algebraMap _ T.functionField h • (formPow (exteriorPower.ιMulti
        T.functionField 2 fun a => (algebraMap (T.presheaf.stalk (D.f D.E.genericPoint))
          T.functionField (y a))⁻¹ • KaehlerDifferential.D k T.functionField
            (algebraMap (T.presheaf.stalk (D.f D.E.genericPoint)) T.functionField (y a))) m :
              RationalPluriForms sT 2 m) := hh
    rw [hh', pluriformPullback_smul_formPow_dlog hdY hdT eD.toHom
      (fun a => algebraMap _ T.functionField (y a)) m (algebraMap _ T.functionField h)]
    rw [show (FunctionFieldEquiv.toHom (D.f ≫ sT) sT eD) (algebraMap _ T.functionField h) =
      algebraMap _ D.Y.functionField hE' from hhE'.symm]
    congr 2
  have hr1' : IsPoincareResidue (D.f ≫ sT) D.E.idealSheaf.subschemeι 1 m
      (pluriformPullback (D.f ≫ sT) sT eD.toHom 2 m ρ)
      ((D.E.idealSheaf.subschemeι.stalkMap (genericPoint _)).hom (μE c) •
        formPow (exteriorPower.ιMulti D.E.idealSheaf.subscheme.functionField 1 fun i =>
          ((D.E.idealSheaf.subschemeι.stalkMap (genericPoint _)).hom (![μE vZ] i))⁻¹ •
            KaehlerDifferential.D k D.E.idealSheaf.subscheme.functionField
              ((D.E.idealSheaf.subschemeι.stalkMap (genericPoint _)).hom (![μE vZ] i))) m) := by
    simp only [hpull1]; exact hr1
  have hr2' : IsPoincareResidue (D.f ≫ sT) D.E.idealSheaf.subschemeι 1 m
      (pluriformPullback (D.f ≫ sT) sT eD.toHom 2 m ρ)
      ((D.E.idealSheaf.subschemeι.stalkMap (genericPoint _)).hom hE' •
        formPow (exteriorPower.ιMulti D.E.idealSheaf.subscheme.functionField 1 fun i =>
          ((D.E.idealSheaf.subschemeι.stalkMap (genericPoint _)).hom (e i))⁻¹ •
            KaehlerDifferential.D k D.E.idealSheaf.subscheme.functionField
              ((D.E.idealSheaf.subschemeι.stalkMap (genericPoint _)).hom (e i))) m) := by
    simp only [hpull2]; exact hr2
  have huniq := IsPoincareResidue.unique_of_isClosedImmersion D.E rfl hr1' hr2'
  simp only [← hφEdef] at huniq
  -- the residue of `h` is the constant `a`
  have hhEa : φE hE' = algebraMap k _ a := by
    have hlt1 := hy₀lt _ ha
    have hmem : hE' - algebraMap k _ a ∈
        IsLocalRing.maximalIdeal (D.Y.presheaf.stalk D.E.genericPoint) := by
      rw [mem_maximalIdeal_iff_divisorialValuation_lt_one D.E rfl, map_sub, hhE',
        ← IsScalarTower.algebraMap_apply k (D.Y.presheaf.stalk D.E.genericPoint) D.Y.functionField,
        ← AlgEquiv.commutes eD, ← map_sub, ← hvE]
      rw [map_sub, ← IsScalarTower.algebraMap_apply] at hlt1
      exact hlt1
    have h0 := (hkerE _).2 hmem
    rw [map_sub, sub_eq_zero, hφEk] at h0
    exact h0
  -- transport to `k(Z)` along `χ`
  apply pluriformPullback_injective_of_equiv hdER hdZ χ
  simp only [pluriformPullback_smul_formPow_dlog hdER hdZ χ.toHom (fun _ => vZ) m c,
    pluriformPullback_smul_formPow_dlog hdER hdZ χ.toHom (fun _ => W) m (algebraMap k _ a)]
  have e1 : (fun _ : Fin 1 => ((FunctionFieldEquiv.toHom _ _ χ) vZ)⁻¹ •
      KaehlerDifferential.D k D.E.idealSheaf.subscheme.functionField
        ((FunctionFieldEquiv.toHom _ _ χ) vZ)) =
      fun i => (φE (![μE vZ] i))⁻¹ • KaehlerDifferential.D k
        D.E.idealSheaf.subscheme.functionField (φE (![μE vZ] i)) := by
    funext i; fin_cases i
    show (χ vZ)⁻¹ • KaehlerDifferential.D k _ (χ vZ) =
      (φE (μE vZ))⁻¹ • KaehlerDifferential.D k _ (φE (μE vZ))
    rw [hχ, hχ0a]
  have e2 : (fun _ : Fin 1 => ((FunctionFieldEquiv.toHom _ _ χ) W)⁻¹ •
      KaehlerDifferential.D k D.E.idealSheaf.subscheme.functionField
        ((FunctionFieldEquiv.toHom _ _ χ) W)) =
      fun i => (φE (e i))⁻¹ • KaehlerDifferential.D k
        D.E.idealSheaf.subscheme.functionField (φE (e i)) := by
    funext i; fin_cases i
    show (χ W)⁻¹ • KaehlerDifferential.D k _ (χ W) =
      (φE (e 0))⁻¹ • KaehlerDifferential.D k _ (φE (e 0))
    rw [hχ, hW]
  have hc' : (FunctionFieldEquiv.toHom _ _ χ) c = φE (μE c) := (hχ c).trans (hχ0a c)
  have ha' : (FunctionFieldEquiv.toHom _ _ χ) (algebraMap k _ a) = φE hE' :=
    (χ.commutes a).trans hhEa.symm
  simp only [hc', ha', e1, e2]
  exact huniq

/-- **The point step along a rational floor curve, from a log section.** Let `(C, B_C)` be a
projective dlt curve whose function field is generated by `w`, such that a nonzero constant
multiple of `(dlog w)^{⊗N}` is a section of `N(K_C + B_C)`. Then there is an adjunction step
`T_q ⟶ C` onto a zero `q` of `w`, at which the residue of `(dlog w)^{⊗m}` is `1`. -/
private theorem exists_isAdjunctionStep_residue_dlog_of_curve_of_mem {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {C : Scheme.{0}} {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C]
    [IsNormal C] (hC : IsNormalVariety k sC) [IsProper sC] (hd : topologicalKrullDim C = (1 : ℕ))
    {BC : QDivisor C} (hdlt : MMP.Intersection.IsDltPair sC BC) (w : C.functionField)
    (hw : w ≠ 0)
    (hgen : letI := functionFieldAlgebra sC
      IntermediateField.adjoin k ({w} : Set C.functionField) = ⊤)
    {N : ℕ} (hN : 0 < N) {c₀ : k} (hc₀ : c₀ ≠ 0)
    (hlog : letI := functionFieldAlgebra sC
      (algebraMap k C.functionField c₀ • (formPow (exteriorPower.ιMulti C.functionField 1
        ![w⁻¹ • KaehlerDifferential.D k _ w]) N : RationalPluriForms sC 1 N)) ∈
        logPluricanonicalSections sC 1 N BC) :
    letI := functionFieldAlgebra sC
    ∃ (Tq : Scheme.{0}) (ιq : Tq ⟶ C) (Bq : QDivisor Tq) (_ : IsAdjunctionStep sC BC ιq Bq)
      (_ : IsIntegral Tq), topologicalKrullDim Tq = (0 : ℕ) ∧
      ∀ m : ℕ, letI := functionFieldAlgebra (ιq ≫ sC)
        IsPoincareResidue sC ιq 0 m
          (formPow (exteriorPower.ιMulti C.functionField 1 ![w⁻¹ • KaehlerDifferential.D k _ w]) m)
          (formPow (exteriorPower.ιMulti Tq.functionField 0 ![]) m) := by
  classical
  letI := functionFieldAlgebra sC
  haveI : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  have htr := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sC) hd
  -- `w` is not a constant
  have hnc : ∀ c : k, w ≠ algebraMap k C.functionField c := by
    intro c hc
    have hbot : IntermediateField.adjoin k ({w} : Set C.functionField) = ⊥ :=
      IntermediateField.adjoin_simple_eq_bot_iff.2 (by rw [hc]; exact IntermediateField.algebraMap_mem _ c)
    rw [hgen] at hbot
    haveI : Algebra.IsAlgebraic k C.functionField := by
      refine ⟨fun x => ?_⟩
      have hx : x ∈ (⊥ : IntermediateField k C.functionField) := by rw [← hbot]; trivial
      obtain ⟨c', rfl⟩ := IntermediateField.mem_bot.1 hx
      exact isAlgebraic_algebraMap c'
    rw [trdeg_eq_zero (R := k) (A := C.functionField)] at htr
    simp at htr
  -- a zero `q` of `w`
  obtain ⟨q, hq⟩ : ∃ q : Mori.PrimeDivisor C, 0 < C.ord w q.genericPoint := by
    by_contra hcon
    push Not at hcon
    have hinv : ∀ Γ : Mori.PrimeDivisor C, 0 ≤ C.ord w⁻¹ Γ.genericPoint := by
      intro Γ
      have e1 := Γ.divisorialValuation_eq_exp_neg_ord (inv_ne_zero hw)
      have e2 := Γ.divisorialValuation_eq_exp_neg_ord hw
      rw [map_inv₀, e2, ← WithZero.exp_neg, WithZero.exp_inj] at e1
      linarith [hcon Γ]
    obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_forall_zero_le_ord sC w⁻¹ hinv
    exact hnc c⁻¹ (by rw [map_inv₀, ← hc, inv_inv])
  have hq1 := ord_eq_one_of_adjoin_simple_eq_top sC q hw hgen hq
  -- `q` has coefficient at least one
  have hqc : 1 ≤ BC.coeff q := by
    have hcl : IsClosed ({q.genericPoint} : Set C) := by
      haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
      exact isClosed_singleton_of_le_coheight (d := 1) hd.le (by rw [q.coheight_genericPoint]; rfl)
    obtain ⟨w', hw'⟩ := exists_algebraMap_eq_of_zero_le_ord q rfl hw hq.le
    have hw'0 : w' ≠ 0 := by rintro rfl; rw [map_zero] at hw'; exact hw hw'.symm
    have hm := maximalIdeal_eq_span_of_ord_eq_one q hw'0 (by rw [hw']; exact hq1)
    have hspan : Ideal.span (Set.range ![w']) =
        IsLocalRing.maximalIdeal (C.presheaf.stalk q.genericPoint) := by
      rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty, hm]
    letI := stalkAlgebra sC q.genericPoint
    have hres : Function.Surjective (algebraMap k
        (IsLocalRing.ResidueField (C.presheaf.stalk q.genericPoint))) := by
      intro y
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨c, hc⟩ := exists_sub_mem_maximalIdeal_of_isClosed sC q.genericPoint hcl r
      refine ⟨c, ?_⟩
      have h0 := (IsLocalRing.residue_eq_zero_iff _).2 hc
      rw [map_sub, sub_eq_zero] at h0
      rw [IsScalarTower.algebraMap_apply k (C.presheaf.stalk q.genericPoint)
        (IsLocalRing.ResidueField (C.presheaf.stalk q.genericPoint)),
        IsLocalRing.ResidueField.algebraMap_eq, ← h0]
    obtain ⟨r, ⟨b⟩⟩ := exists_basis_kaehler_stalk_of_mem_smoothLocus sC
      (MMP.Threefold.Mori.CanonUniq.genericPoint_mem_smoothLocus hC.1 q)
    haveI : Module.Finite (C.presheaf.stalk q.genericPoint) Ω[C.presheaf.stalk q.genericPoint⁄k] :=
      Module.Finite.of_basis b
    have hspD := span_D_eq_top_of_span_eq_maximalIdeal hres ![w'] hspan
    have hLz : IdealSheafData.stalk q.idealSheaf q.genericPoint = Ideal.span {(![w'] : Fin 1 → _) 0} := by
      rw [MMP.Resolution.Aux.stalk_idealSheaf_genericPoint]
      exact hm
    have hmem : q.genericPoint ∈ q.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    have h1 := ordForm_formPow_dlog_eq (sX := sC) hd 1 ![w'] (fun a => by fin_cases a; exact hw'0)
      hspD ![q] (fun a b _ => Subsingleton.elim a b) (fun a => by fin_cases a; exact hmem)
      (fun a => by fin_cases a; exact hLz) q hmem
    have hN1 := ordForm_formPow_dlog_eq (sX := sC) hd N ![w'] (fun a => by fin_cases a; exact hw'0)
      hspD ![q] (fun a b _ => Subsingleton.elim a b) (fun a => by fin_cases a; exact hmem)
      (fun a => by fin_cases a; exact hLz) q hmem
    have e : (fun a : Fin 1 => (algebraMap (C.presheaf.stalk q.genericPoint) C.functionField
        ((![w'] : Fin 1 → _) a))⁻¹ • KaehlerDifferential.D k C.functionField
          (algebraMap (C.presheaf.stalk q.genericPoint) C.functionField ((![w'] : Fin 1 → _) a))) =
        ![w⁻¹ • KaehlerDifferential.D k _ w] := by
      funext a; fin_cases a; simp [hw']
    rw [e] at hN1
    rw [if_pos ⟨0, rfl⟩] at hN1
    have hc0' : algebraMap k C.functionField c₀ ≠ 0 := (map_ne_zero _).2 hc₀
    have hω10 : (exteriorPower.ιMulti C.functionField 1
        ![w⁻¹ • KaehlerDifferential.D k _ w]) ≠ 0 := by
      intro h0
      have h1' := h1
      rw [e] at h1'
      rw [h0] at h1'
      have : (show RationalPluriForms sC 1 1 from formPow (0 : ⋀[C.functionField]^1
          Ω[C.functionField⁄k]) 1) = 0 := formPow_zero_of_pos one_pos
      rw [this, Mori.PrimeDivisor.ordForm_zero, if_pos ⟨0, rfl⟩] at h1'
      exact absurd h1' (by decide)
    have hne := smul_formPow_ne_zero hd hω10 hc0' N
    have h2 := (mem_pluricanonicalSections_of_ne_bot top_ne_bot).1 hlog q
      ⟨q.genericPoint, hmem, trivial⟩ hne
    have hord0 : C.ord (algebraMap k C.functionField c₀) q.genericPoint = 0 := by
      letI := stalkAlgebra sC q.genericPoint
      haveI := isScalarTower_stalk_functionField sC q.genericPoint
      rw [IsScalarTower.algebraMap_apply k (C.presheaf.stalk q.genericPoint)]
      exact q.ord_algebraMap_of_isUnit ((IsUnit.mk0 _ hc₀).map _)
    have h1'' := h1
    rw [e, if_pos ⟨0, rfl⟩] at h1''
    rw [ordForm_smul_formPow hd q hω10 hc0' N, hord0, h1'', DivisorWithCoeffs.coeff_roundDown,
      DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h2
    have h4 : (N : ℤ) ≤ ⌊(N : ℚ) * BC.coeff q⌋ := by push_cast at h2 ⊢; linarith
    have h5 := Int.le_floor.1 h4
    have hNq : (0 : ℚ) < N := by exact_mod_cast hN
    push_cast at h5
    nlinarith
  -- the adjunction step onto `q`
  obtain ⟨Tq, ιq, Bq, -, hιq, hTq, hrq, hdq⟩ :=
    exists_isAdjunctionStep_of_isDltPair hC hdlt (e := 0) (by simpa using hd) q hqc
  rw [Category.id_comp] at hιq
  refine ⟨Tq, ιq, Bq, hιq, hTq, by exact_mod_cast hdq, fun m => ?_⟩
  have hP := map_genericPoint_eq_of_range_eq ιq q hrq
  obtain ⟨t, ht⟩ := exists_algebraMap_eq_of_zero_le_ord q hP hw (by rw [hP]; exact hq.le)
  letI := functionFieldAlgebra (ιq ≫ sC)
  set f0 : Fin 0 → C.presheaf.stalk (ιq (genericPoint Tq)) := Fin.elim0 with hf0
  have hres := isPoincareResidue_formPow_dlog sC ιq m t (n := 0) f0 (fun i => i.elim0)
    (by rw [ht, hP]; exact hq1)
  have e1 : (formPow (exteriorPower.ιMulti C.functionField 1 ![w⁻¹ • KaehlerDifferential.D k _ w]) m :
      RationalPluriForms sC (0 + 1) m) = formPow (exteriorPower.ιMulti C.functionField (0 + 1)
        (Fin.cons ((algebraMap _ C.functionField t)⁻¹ •
            KaehlerDifferential.D k C.functionField (algebraMap _ _ t))
          fun i => (algebraMap _ C.functionField (f0 i))⁻¹ •
            KaehlerDifferential.D k C.functionField (algebraMap _ C.functionField (f0 i)))) m := by
    congr 2
    funext a; fin_cases a; simp [ht]
  have e2 : (formPow (exteriorPower.ιMulti Tq.functionField 0 ![]) m :
      RationalPluriForms (ιq ≫ sC) 0 m) = formPow (exteriorPower.ιMulti Tq.functionField 0
        fun i => ((ιq.stalkMap (genericPoint Tq)).hom (f0 i))⁻¹ •
          KaehlerDifferential.D k Tq.functionField ((ιq.stalkMap (genericPoint Tq)).hom
            (f0 i))) m := by
    congr 2
    funext a; exact a.elim0
  rw [e1, e2]
  exact hres

end CurveHelpers

variable {k : Type} [Field k] {I : Type*} {X : I → Scheme.{0}} {sX : ∀ i, X i ⟶ Spec (.of k)}
  [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
  {B : ∀ i, QDivisor (X i)} {n m : ℕ}

/-- The zero form has residue zero along an adjunction step. -/
private theorem isPoincareResidue_zero {k : Type u} [Field k] [PerfectField k] {Y T : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T]
    [LocallyOfFiniteType sY] {j : T ⟶ Y} {BY : QDivisor Y} {BT : QDivisor T}
    (hj : IsAdjunctionStep sY BY j BT) {e m : ℕ} :
    IsPoincareResidue sY j e m 0 0 := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra sY
  obtain ⟨hdvr, -, -, -, hcoh, -⟩ := hj.stalk_facts
  obtain ⟨ϖ, hϖ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk (j (genericPoint T)))
  have h0 : algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  refine ⟨ϖ, 0, 0, (Scheme.ord_eq_iff hcoh h0).mpr (Ring.ordFrac_irreducible hϖ), ?_, ?_⟩ <;>
    simp <;> rfl

/-- In the stratified setting each component `X_i` carries a canonical divisor `K` of dimension
`n` with `m(K + B_i)` Cartier. -/
private theorem exists_canonical_cartier (R : ResidueRestriction sX B n m) (i : I) :
    ∃ K : Divisor (X i), K.IsCanonicalDivisor (sX i) n ∧
      ((m : ℤ) • (Divisor.toQDivisor K + B i)).IsCartierDivisor := by
  obtain ⟨d, K, hK, hmK⟩ := R.setting.isCartierDivisor i (.refl (R.setting.isPair i).isPair)
  rw [Category.id_comp] at hK
  have hd : d = n := by
    have h := hK.topologicalKrullDim_eq.symm.trans (R.setting.topologicalKrullDim_eq i)
    exact_mod_cast h
  subst hd
  exact ⟨K, hK, hmK⟩

/-- **Residues vanishing along first steps vanish along all proper strata.** If a section `w`
of `m(K_{X_i} + B_i)` has residue restriction zero along every flag of length one, then every
iterated residue of `w` along a flag of positive length is zero. -/
private theorem eq_zero_of_isIteratedResidueRec (R : ResidueRestriction sX B n m) (i : I)
    (w : logPluricanonicalSections (sX i) n m (B i))
    (hw : ∀ {T : Scheme.{0}} {j : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
      (hj : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) j BT) (e : ℕ),
      topologicalKrullDim T = e → R.toFun i (.step (.refl h) j BT hj) e w = 0)
    {S : Scheme.{0}} {ι : S ⟶ X i} {BS : QDivisor S}
    (F : StratumAdjunctionData (sX i) (B i) ι BS) (hF : 0 < F.length) {e : ℕ}
    {ρ : @RationalPluriForms k _ S (ι ≫ sX i) F.isIntegral_stratum e m}
    (hρ : IsIteratedResidueRec (w : RationalPluriForms (sX i) n m) F e ρ) : ρ = 0 := by
  have hP := R.setting.isPair i
  have := hP.charZero
  induction F generalizing e with
  | refl h => simp [StratumAdjunctionData.length] at hF
  | @step S T ι BS F j BT hj ih =>
    obtain ⟨ρ₀, h₀, ρ', hr, hρρ⟩ := hρ
    rcases Nat.eq_zero_or_pos F.length with h0 | h0
    · cases F with
      | step => simp [StratumAdjunctionData.length] at h0
      | refl h =>
        haveI : IsIntegral T := hj.1.1.toIsIntegral
        haveI : LocallyOfFiniteType (j ≫ 𝟙 (X i) ≫ sX i) := hj.1.1.toLocallyOfFiniteType
        have hne := h₀.1
        have hT := topologicalKrullDim_eq_toNat_trdeg (j ≫ 𝟙 (X i) ≫ sX i)
        have hdl := StratumAdjunctionData.dim_add_length (R.setting.topologicalKrullDim_eq i)
          (StratumAdjunctionData.step (.refl h) j BT hj) hT
        simp only [StratumAdjunctionData.length] at hdl
        have hdim : topologicalKrullDim T = e := by
          rw [hT]
          exact_mod_cast (by omega : _ = e)
        have key := (R.isIteratedResidue i (.step (.refl h) j BT hj) e w hdim).rec'
        have hρ : IsIteratedResidueRec (w : RationalPluriForms (sX i) n m)
            (StratumAdjunctionData.step (.refl h) j BT hj) e ρ := ⟨ρ₀, h₀, ρ', hr, hρρ⟩
        have hu := IsIteratedResidueRec.unique _ hρ key
        rw [hu, hw h hj e hdim]
    · haveI := F.isIntegral_stratum
      haveI := F.isNormal_stratum
      haveI := F.isLocallyNoetherian_stratum
      haveI : IsIntegral T := hj.1.1.toIsIntegral
      haveI : LocallyOfFiniteType (ι ≫ sX i) := F.isNormalVariety.1.toLocallyOfFiniteType
      have h1 := ih h0 h₀
      subst h1
      have h2 := IsPoincareResidue.unique hj hr (isPoincareResidue_zero hj)
      subst h2
      exact eq_of_heq hρρ

/-- The pull-back of a section of `m(K_{X_j} + B_j)` along a crepant birational map
`(X_i, B_i) ⇢ (X_j, B_j)` is a section of `m(K_{X_i} + B_i)`. -/
private theorem pluriformPullback_mem_logPluricanonicalSections (R : ResidueRestriction sX B n m)
    {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    (s : logPluricanonicalSections (sX j) n m (B j)) :
    pluriformPullback (sX i) (sX j) σ.toHom n m s ∈ logPluricanonicalSections (sX i) n m (B i) := by
  have hP := R.setting.isPair i
  have := hP.isAlgClosed
  have := hP.charZero
  obtain ⟨K, hK, hmK⟩ := exists_canonical_cartier R i
  obtain ⟨K', hK', hmK'⟩ := exists_canonical_cartier R j
  exact pluriformPullback_mem_logPluricanonicalSections_of_isCrepantBirationalMap
    hP.isPair.1 (R.setting.isPair j).isPair.1 hK hK' R.setting.pos hmK hmK' hσ s.2

/-- **Crepant maps induce crepant maps on floor divisors**, for the components of the
stratified setting. -/
private theorem isCrepantBirationalMap_of_stalk_ringEquiv (R : ResidueRestriction sX B n m)
    {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T T' : Scheme.{0}} [IsIntegral T] [IsIntegral T'] [IsLocallyNoetherian T] [IsNormal T]
    [IsLocallyNoetherian T'] [IsNormal T'] {ι : T ⟶ X i} {ι' : T' ⟶ X j} {BT : QDivisor T}
    {BT' : QDivisor T'} (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT)
    (hι' : IsAdjunctionStep (𝟙 (X j) ≫ sX j) (B j) ι' BT') {e : ℕ} (hn1 : e + 1 = n)
    (P : Mori.PrimeDivisor (X i)) (P' : Mori.PrimeDivisor (X j))
    (hrP : Set.range ι.base = (P.support : Set (X i)))
    (hrP' : Set.range ι'.base = (P'.support : Set (X j)))
    (hP' : ∀ g, P'.divisorialValuation g = P.divisorialValuation ((σ.toHom) g))
    (ψ : (X j).presheaf.stalk (ι' (genericPoint T')) ≃+* (X i).presheaf.stalk (ι (genericPoint T)))
    (hψ : ∀ a, algebraMap _ (X i).functionField (ψ a) =
      (σ.toHom) (algebraMap _ (X j).functionField a))
    (hord : ∀ a, (X i).ord (algebraMap _ (X i).functionField (ψ a)) (ι (genericPoint T)) =
      (X j).ord (algebraMap _ (X j).functionField a) (ι' (genericPoint T')))
    (σT : FunctionFieldEquiv (ι ≫ sX i) (ι' ≫ sX j))
    (hσT : ∀ a, (σT.toHom) ((ι'.stalkMap (genericPoint T')).hom a) =
      (ι.stalkMap (genericPoint T)).hom (ψ a)) :
    IsCrepantBirationalMap ((ι ≫ 𝟙 (X i)) ≫ sX i) ((ι' ≫ 𝟙 (X j)) ≫ sX j) BT BT'
      (σT : FunctionFieldEquiv ((ι ≫ 𝟙 (X i)) ≫ sX i) ((ι' ≫ 𝟙 (X j)) ≫ sX j)) := by
  have hPi := R.setting.isPair i
  have hPj := R.setting.isPair j
  have := hPi.isAlgClosed
  have := hPi.charZero
  have hX := hPi.isPair.1
  have hXj := hPj.isPair.1
  haveI := hX.1
  haveI := hXj.1
  haveI : LocallyOfFiniteType (sX i) := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (sX j) := hXj.1.toLocallyOfFiniteType
  haveI : CompactSpace (X i) := QuasiCompact.compactSpace_of_compactSpace (sX i)
  haveI : CompactSpace (X j) := QuasiCompact.compactSpace_of_compactSpace (sX j)
  haveI : IsProper (sX i) :=
    isProper_of_isProjectiveMorphism _ (R.setting.isProjectiveVariety i).isProjective
  haveI : IsProper (sX j) :=
    isProper_of_isProjectiveMorphism _ (R.setting.isProjectiveVariety j).isProjective
  obtain ⟨K, hK, hmK⟩ := exists_canonical_cartier R i
  obtain ⟨K', hK', hmK'⟩ := exists_canonical_cartier R j
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast R.setting.pos.ne'
  subst hn1
  obtain ⟨-, -, -, -, hci, -⟩ := id hι
  obtain ⟨-, -, -, -, hci', -⟩ := id hι'
  haveI : LocallyOfFiniteType (ι ≫ sX i) := hι.1.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (ι' ≫ sX j) := hι'.1.1.toLocallyOfFiniteType
  haveI := hι.1.1
  haveI := hι'.1.1
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (ι ≫ sX i)
  haveI : CompactSpace T' := QuasiCompact.compactSpace_of_compactSpace (ι' ≫ sX j)
  exact isCrepantBirationalMap_of_isAdjunctionStep hX hXj (R.setting.topologicalKrullDim_eq i)
    (R.setting.topologicalKrullDim_eq j) hK hK' ⟨_, hm0, hmK⟩ ⟨_, hm0, hmK'⟩ σ hσ
    (hι : IsAdjunctionStep (sX i) (B i) ι BT) (hι' : IsAdjunctionStep (sX j) (B j) ι' BT')
    P P' hrP hrP' hP' ψ.toRingHom hψ hord σT hσT

/-- The floor-divisor comparison when the valuation of the floor divisor `P` of `X_i` is carried
by `σ` to the valuation of a prime divisor `P'` of `X_j`. -/
private theorem toFun_step_refl_eq_of_divisorialValuation_eq (hn : n ≤ 3)
    (R : ResidueRestriction sX B n m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {s : ∀ l, logPluricanonicalSections (sX l) n m (B l)} (hs : s ∈ preadmissibleSections R)
    (u : logPluricanonicalSections (sX i) n m (B i))
    (hu : (u : RationalPluriForms (sX i) n m) = pluriformPullback (sX i) (sX j) σ.toHom n m (s j))
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) (e : ℕ)
    (he : topologicalKrullDim T = e) [IsIntegral T] (P : MMP.Mori.PrimeDivisor (X i))
    (hP : ι (genericPoint T) = P.genericPoint) (hP1 : 1 ≤ (B i).coeff P)
    (hrange : Set.range ι.base = (P.support : Set (X i))) (P' : MMP.Mori.PrimeDivisor (X j))
    (hP' : ∀ g, P'.divisorialValuation g = P.divisorialValuation ((σ.toHom) g)) :
    R.toFun i (.step (.refl h) ι BT hι) e u = R.toFun i (.step (.refl h) ι BT hι) e (s i) := by
  have hPi := R.setting.isPair i
  have hPj := R.setting.isPair j
  have := hPi.isAlgClosed
  have := hPi.charZero
  have hX := hPi.isPair.1
  have hXj := hPj.isPair.1
  obtain ⟨K, hK, -⟩ := exists_canonical_cartier R i
  obtain ⟨K', hK', -⟩ := exists_canonical_cartier R j
  have hcoeff : (B j).coeff P' = (B i).coeff P := by
    set DΓ := DivisorOver.ofPrimeDivisor k hX P
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPi.isPair hK DΓ
    have hc' : c = -(B i).coeff P := hc.eq_neg_coeff_of_ofPrimeDivisor hX
    have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
      (show IsProper (𝟙 (X i)) by infer_instance)
    obtain ⟨n', D, hDv, hDlog⟩ := (hσ DΓ.valuation (1 + c)).mp ⟨n, DΓ, rfl, hlog⟩
    set DΓ' := DivisorOver.ofPrimeDivisor k hXj P'
    obtain ⟨c2, hc2⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPj.isPair hK' DΓ'
    have hc2' : c2 = -(B j).coeff P' := hc2.eq_neg_coeff_of_ofPrimeDivisor hXj
    have hlog2 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc2
      (show IsProper (𝟙 (X j)) by infer_instance)
    have hval : D.valuation = DΓ'.valuation := by
      ext g
      rw [hDv]
      change P.divisorialValuation (functionFieldMap (𝟙 (X i)) ((σ.toHom) g)) =
        P'.divisorialValuation (functionFieldMap (𝟙 (X j)) g)
      rw [functionFieldMap_id_apply, functionFieldMap_id_apply, hP']
    have h1 := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq_of_isPair hPj.isPair
      hDlog hlog2 hval
    have h2 : c = c2 := by exact_mod_cast (by linarith : (c : ℝ) = c2)
    linarith
  have hP1' : 1 ≤ (B j).coeff P' := hcoeff ▸ hP1
  have hn1 : e + 1 = n := by
    have := (StratumAdjunctionData.step (.refl h) ι BT hι).dim_add_length
      (R.setting.topologicalKrullDim_eq i) he
    simpa [StratumAdjunctionData.length] using this
  subst hn1
  have hdimXi : topologicalKrullDim (X i) = (e + 1 : ℕ) := R.setting.topologicalKrullDim_eq i
  have hdimXj : topologicalKrullDim (X j) = (e + 1 : ℕ) := R.setting.topologicalKrullDim_eq j
  haveI : LocallyOfFiniteType (sX j) := hXj.1.toLocallyOfFiniteType
  obtain ⟨T', j'', BT', h', hj'', _, hr', hdimT'⟩ :=
    exists_isAdjunctionStep_of_isDltPair hXj (R.setting.isDltPair j) hdimXj P' hP1'
  haveI : LocallyOfFiniteType (sX i) := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (ι ≫ sX i) := hι.1.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (j'' ≫ sX j) := hj''.1.1.toLocallyOfFiniteType
  haveI : IsNormal T := hι.1.2
  haveI : IsNormal T' := hj''.1.2
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sX i)
  haveI : IsLocallyNoetherian T' := LocallyOfFiniteType.isLocallyNoetherian (j'' ≫ sX j)
  have hP'gen : j'' (genericPoint T') = P'.genericPoint :=
    map_genericPoint_eq_of_range_eq j'' P' hr'
  obtain ⟨ψ, hψ, hord⟩ :=
    exists_stalk_ringEquiv_of_divisorialValuation_eq σ P P' hP' hP hP'gen
  obtain ⟨σT, hσT⟩ := exists_functionFieldEquiv_of_stalk_ringEquiv σ
    (hι : IsAdjunctionStep (sX i) (B i) ι BT) (hj'' : IsAdjunctionStep (sX j) (B j) j'' BT')
    ψ hψ
  have hcrep := isCrepantBirationalMap_of_stalk_ringEquiv R σ hσ hι hj'' rfl P P' hrange hr'
    hP' ψ hψ hord σT hσT
  have hpre := hs i j (.step (.refl h) ι BT hι) (.step (.refl h') j'' BT' hj'') e
    (by simp [StratumAdjunctionData.length]) (by simp [StratumAdjunctionData.length]) he
    hdimT' σT hcrep
  obtain ⟨ρ₀, ⟨-, hρ₀⟩, ρ', hr, hρ'⟩ :=
    (R.isIteratedResidue i (.step (.refl h) ι BT hι) e u he).rec'
  obtain ⟨ρ₀', ⟨-, hρ₀'⟩, ρ'', hr'', hρ''⟩ :=
    (R.isIteratedResidue j (.step (.refl h') j'' BT' hj'') e (s j) hdimT').rec'
  have e1 : ρ₀ = (u : RationalPluriForms (sX i) (e + 1) m) := eq_of_heq hρ₀
  have e2 : ρ₀' = (s j : RationalPluriForms (sX j) (e + 1) m) := eq_of_heq hρ₀'
  have e3 : R.toFun i (.step (.refl h) ι BT hι) e u = ρ' := eq_of_heq hρ'
  have e4 : R.toFun j (.step (.refl h') j'' BT' hj'') e (s j) = ρ'' := eq_of_heq hρ''
  have hfun := isPoincareResidue_pluriformPullback (sX := sX i) (sX' := sX j) ι j''
    hdimXi hdimXj he hdimT' σ.toHom σT.toHom ψ.toRingHom hψ (fun a => (hσT a).symm) hord hr''
  have hu' : pluriformPullback (sX i) (sX j) σ.toHom (e + 1) m ρ₀' = ρ₀ := by
    rw [e1, e2, hu]
  rw [hu'] at hfun
  have huniq := IsPoincareResidue.unique hι hr hfun
  rw [e3, huniq, ← e4]
  exact hpre

/-- A variety of dimension `n` with an exceptional divisor over it has `n ≥ 2`. -/
private theorem two_le_of_isExceptional {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    {D : DivisorOver k sX} (hD : D.IsExceptional) : 2 ≤ n := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    (D.f D.E.genericPoint)
  rw [hn] at h
  have h0 : 0 ≤ topologicalKrullDim (closure {D.f D.E.genericPoint} : Set X) :=
    Order.krullDim_nonneg_iff.mpr ⟨⟨closure {⟨_, subset_closure rfl⟩},
      isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have : ((Order.coheight (D.f D.E.genericPoint) : ℕ∞) : WithBot ℕ∞) ≤ n :=
    h ▸ le_add_of_nonneg_left h0
  exact_mod_cast ((MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight
    hX D).mp hD).trans (WithBot.coe_le_coe.mp this)

/-- **Floor divisors centred at a point stratum.** Let `P` be a floor divisor of `X_i` whose
valuation is that of a divisor `D` over `X_j` of discrepancy `-1` centred at a closed point `x`,
with snc coordinates `z₁, z₂, z₃` at `x`. The residue `θ` of `σ^*(dlog z₁ ∧ dlog z₂ ∧ dlog z₃)`
along `P` is a log generator of `(T, B_T)`, and writing `s_j = g_j τ^m` and `σ⁻¹^* s_i = g' τ^m`
near `x`, the residues of `σ^* s_j` and of `s_i` along `P` are `g_j(x) θ^m` and `g'(x) θ^m`. The
point residues along a flag through `P` to a point stratum, and along a flag of `X_j` to `x`, are
`g'(x)` and `g_j(x)`, which preadmissibility identifies. -/
private theorem toFun_step_refl_eq_of_isExceptional_of_point
    (R : ResidueRestriction sX B 3 m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {s : ∀ l, logPluricanonicalSections (sX l) 3 m (B l)} (hs : s ∈ preadmissibleSections R)
    (u : logPluricanonicalSections (sX i) 3 m (B i))
    (hu : (u : RationalPluriForms (sX i) 3 m) =
      pluriformPullback (sX i) (sX j) σ.toHom 3 m (s j))
    (u' : logPluricanonicalSections (sX j) 3 m (B j))
    (hσσ : pluriformPullback (sX i) (sX j) σ.toHom 3 m (u' : RationalPluriForms (sX j) 3 m) =
      (s i : RationalPluriForms (sX i) 3 m))
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) (e : ℕ)
    (he : topologicalKrullDim T = e) [IsIntegral T] (P : Mori.PrimeDivisor (X i))
    (hP : ι (genericPoint T) = P.genericPoint) (hP1 : (B i).coeff P = 1)
    (hrange : Set.range ι.base = (P.support : Set (X i))) (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g))
    (z : Fin 3 → (X j).presheaf.stalk (D.f D.E.genericPoint))
    (L : Fin 3 → Mori.PrimeDivisor (X j)) (α : Fin 3 → ℕ)
    (hz : IsRegularSystemOfParameters z) (hL : Function.Injective L)
    (hLx : ∀ a, D.f D.E.genericPoint ∈ (L a).support)
    (hLz : ∀ a, IdealSheafData.stalk (L a).idealSheaf (D.f D.E.genericPoint) = Ideal.span {z a})
    (hBL : ∀ E : Mori.PrimeDivisor (X j), D.f D.E.genericPoint ∈ E.support →
      (B j).coeff E ≠ 0 → E ∈ Set.range L)
    (hL1 : ∀ a, (B j).coeff (L a) = 1) (hsm : D.f D.E.genericPoint ∈ Mori.smoothLocus (sX j))
    (hα : ∀ a, 0 < α a)
    (hzv : ∀ a, D.valuation (algebraMap _ (X j).functionField (z a)) = WithZero.exp (-(α a : ℤ)))
    (hmono : ∀ f : (X j).presheaf.stalk (D.f D.E.genericPoint), f ≠ 0 → ∃ M : ℕ,
      f ∈ weightedMonomialIdeal z α M ∧
      D.valuation (algebraMap _ (X j).functionField f) = WithZero.exp (-(M : ℤ))) :
    R.toFun i (.step (.refl h) ι BT hι) e u = R.toFun i (.step (.refl h) ι BT hι) e (s i) := by
  classical
  have hPi := R.setting.isPair i
  have hPj := R.setting.isPair j
  have := hPi.isAlgClosed
  have := hPi.charZero
  have hX := hPi.isPair.1
  have hXj := hPj.isPair.1
  haveI := hX.1
  haveI := hXj.1
  haveI : LocallyOfFiniteType (sX i) := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (sX j) := hXj.1.toLocallyOfFiniteType
  haveI : CompactSpace (X i) := QuasiCompact.compactSpace_of_compactSpace (sX i)
  haveI : CompactSpace (X j) := QuasiCompact.compactSpace_of_compactSpace (sX j)
  haveI : IsProper (sX i) :=
    isProper_of_isProjectiveMorphism _ (R.setting.isProjectiveVariety i).isProjective
  haveI : IsProper (sX j) :=
    isProper_of_isProjectiveMorphism _ (R.setting.isProjectiveVariety j).isProjective
  obtain ⟨K, hK, hmK⟩ := exists_canonical_cartier R i
  obtain ⟨K', hK', hmK'⟩ := exists_canonical_cartier R j
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast R.setting.pos.ne'
  have hni := R.setting.topologicalKrullDim_eq i
  have hnj := R.setting.topologicalKrullDim_eq j
  letI := functionFieldAlgebra (sX i)
  letI := functionFieldAlgebra (sX j)
  have hιs : IsAdjunctionStep (sX i) (B i) ι BT := hι
  have hTnv : IsNormalVariety k (ι ≫ sX i) := hιs.1
  haveI : IsNormal T := hTnv.2
  haveI : LocallyOfFiniteType (ι ≫ sX i) := hTnv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sX i)
  obtain ⟨-, -, -, -, hci, -⟩ := id hιs
  haveI := hci
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace ι
  have hdT : topologicalKrullDim T = (2 : ℕ) :=
    topologicalKrullDim_eq_of_range_eq_support (sX i) ι P hrange hni
  -- the centre is a closed point with residue field `k`
  have hcoh : Order.coheight (D.f D.E.genericPoint) = 3 := by
    have h1 := hz.2
    rw [ringKrullDim_stalk_eq_coheight] at h1
    have h2 : ((Order.coheight (D.f D.E.genericPoint) : ℕ∞) : WithBot ℕ∞) =
      ((3 : ℕ∞) : WithBot ℕ∞) := h1
    exact WithBot.coe_injective h2
  have hxcl : IsClosed ({D.f D.E.genericPoint} : Set (X j)) :=
    isClosed_singleton_of_le_coheight (d := 3) hnj.le (by rw [hcoh]; rfl)
  have hresk := exists_sub_mem_maximalIdeal_of_isClosed (sX j) (D.f D.E.genericPoint) hxcl
  have hres := surjective_algebraMap_residueField_of_isClosed (sX j) (D.f D.E.genericPoint) hxcl
  have hz0 : ∀ a, z a ≠ 0 := by
    haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
    exact fun a => MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz a
  letI := stalkAlgebra (sX j) (D.f D.E.genericPoint)
  obtain ⟨r0, ⟨b0⟩⟩ := exists_basis_kaehler_stalk_of_mem_smoothLocus (sX j) hsm
  haveI : Module.Finite ((X j).presheaf.stalk (D.f D.E.genericPoint))
      Ω[(X j).presheaf.stalk (D.f D.E.genericPoint)⁄k] := Module.Finite.of_basis b0
  have hw := span_D_eq_top_of_span_eq_maximalIdeal hres z hz.1
  -- the snc log generator `τ'` at the centre, and an open on which it generates
  obtain ⟨U, hxU, hU⟩ := exists_open_coeff_divisorOfForm_add_eq_zero hnj z hz hsm hres L hL hLx
    hLz hBL hL1
  set τ' : RationalPluriForms (sX j) 3 ((1 : ℕ) : ℤ) := formPow (exteriorPower.ιMulti
    (X j).functionField 3 fun a => (algebraMap _ (X j).functionField (z a))⁻¹ •
      KaehlerDifferential.D k _ (algebraMap _ (X j).functionField (z a))) 1 with hτ'
  have hτ'0 : τ' ≠ 0 := by
    intro h0
    have := ordForm_formPow_dlog_eq hnj 1 z hz0 hw L hL hLx hLz (L 0) (hLx 0)
    rw [if_pos ⟨0, rfl⟩] at this
    change (L 0).ordForm τ' = _ at this
    rw [h0, Mori.PrimeDivisor.ordForm_zero] at this
    exact absurd this (by decide)
  have hDU : (D.center : Set (X j)) ⊆ U := by
    rw [D.center_eq_closure_genericPoint, hxcl.closure_eq, Set.singleton_subset_iff]
    exact hxU
  obtain ⟨hτP, hθall⟩ := divisorOfForm_add_eq_zero_of_center_subset (n := 2) hX hXj hni hnj
    (by norm_num) hK hK' ⟨_, hm0, hmK⟩ ⟨_, hm0, hmK'⟩ σ hσ hιs P hrange hP1 D hDv hτ'0 U hDU hU
  -- the monomial frame along `P`
  have hvD : ∀ r : (X j).presheaf.stalk (D.f D.E.genericPoint),
      D.valuation (algebraMap _ (X j).functionField r) ≤ 1 := by
    intro r
    by_cases hr : r = 0
    · rw [hr, map_zero, map_zero]; exact zero_le'
    obtain ⟨M, -, hM⟩ := hmono r hr
    rw [hM, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hle : ∀ r : (X j).presheaf.stalk (D.f D.E.genericPoint),
      P.divisorialValuation ((σ.toHom) (algebraMap _ (X j).functionField r)) ≤ 1 :=
    fun r => by rw [← hDv]; exact hvD r
  have hlt : ∀ r ∈ IsLocalRing.maximalIdeal ((X j).presheaf.stalk (D.f D.E.genericPoint)),
      P.divisorialValuation ((σ.toHom) (algebraMap _ (X j).functionField r)) < 1 := by
    intro r hr
    rw [← hDv]
    have h1 : r ∈ weightedMonomialIdeal z α 1 := by
      have := span_range_le_weightedMonomialIdeal_one z α hα
      rw [hz.1] at this
      exact this hr
    have h2 := valuation_le_of_mem_weightedMonomialIdeal z α D.valuation hvD hzv h1
    refine h2.trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  obtain ⟨t, e', he', ht, hfr, hgen⟩ := exists_monomialFrame ι P hP σ z α hz0 hle hlt
    (fun a => by rw [← hDv]; exact hzv a)
    (fun f hf => by
      obtain ⟨M, hM, hMv⟩ := hmono f hf
      exact ⟨M, hM, by rw [← hDv]; exact hMv⟩) hresk
  have hpullm : ∀ (m' : ℕ) (c : (X j).functionField),
      pluriformPullback (sX i) (sX j) σ.toHom 3 m' (c • formPow (exteriorPower.ιMulti
        (X j).functionField 3 fun a => (algebraMap _ (X j).functionField (z a))⁻¹ •
          KaehlerDifferential.D k _ (algebraMap _ (X j).functionField (z a))) m') =
      ((σ.toHom : FunctionFieldHom (sX i) (sX j)) c) • formPow (exteriorPower.ιMulti
        (X i).functionField (2 + 1)
        (Fin.cons ((algebraMap _ (X i).functionField t)⁻¹ •
          KaehlerDifferential.D k _ (algebraMap _ (X i).functionField t))
          fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ (X i).functionField (e' b)))) m' := by
    intro m' c
    rw [pluriformPullback_smul_formPow_dlog hni hnj σ.toHom (fun a => algebraMap _ _ (z a)) m' c,
      hfr]
  -- the residue `θ` of `σ^*τ'` along `P` is a log generator of `(T, B_T)`
  have hres3 := isPoincareResidue_formPow_dlog (sX i) ι 1 t e' he' ht
  have hpull1 : pluriformPullback (sX i) (sX j) σ.toHom 3 1 τ' =
      formPow (exteriorPower.ιMulti (X i).functionField (2 + 1)
        (Fin.cons ((algebraMap _ (X i).functionField t)⁻¹ •
          KaehlerDifferential.D k _ (algebraMap _ (X i).functionField t))
          fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ (X i).functionField (e' b)))) 1 := by
    have h1 := hpullm 1 1
    rw [one_smul, map_one, one_smul] at h1
    exact h1
  have hθ0 := hθall _ (by rw [hpull1]; exact hres3)
  letI := functionFieldAlgebra (ι ≫ sX i)
  have hθ : ∀ Γ : Mori.PrimeDivisor T, (Γ.ordForm (show RationalPluriForms (ι ≫ sX i) 2
      ((1 : ℕ) : ℤ) from formPow (exteriorPower.ιMulti T.functionField 2 fun b =>
        ((ι.stalkMap (genericPoint T)).hom (e' b))⁻¹ • KaehlerDifferential.D k _
          ((ι.stalkMap (genericPoint T)).hom (e' b))) 1) : ℚ) + BT.coeff Γ = 0 := by
    intro Γ
    have := congrArg (fun G : QDivisor T => G.coeff Γ) hθ0
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm,
      DivisorWithCoeffs.coeff_zero] at this
    exact this
  obtain ⟨Sq, ιq, Bq, Fq, hlenq, hdimq, hrecq⟩ := exists_flag_isIteratedResidueRec_of_frame
    (R.setting.isDltPair i) h P hP1.ge hι hrange hdT t e' he' ht hgen hθ m
  -- coefficients of `s_j` and of `u'` at the centre
  obtain ⟨gj, hgj⟩ := exists_algebraMap_smul_of_mem_logPluricanonicalSections hnj (by norm_num) z
    hz0 hw L hL hLx hLz hBL hL1 R.setting.pos (s j : RationalPluriForms (sX j) 3 m) (s j).2
  obtain ⟨g', hg'⟩ := exists_algebraMap_smul_of_mem_logPluricanonicalSections hnj (by norm_num) z
    hz0 hw L hL hLx hLz hBL hL1 R.setting.pos (u' : RationalPluriForms (sX j) 3 m) u'.2
  dsimp only at hgj hg'
  obtain ⟨cj, hcj⟩ := hresk gj
  obtain ⟨c', hc'⟩ := hresk g'
  -- their pull-backs along `P`
  haveI := isScalarTower_stalk_functionField (sX j) (D.f D.E.genericPoint)
  letI := stalkAlgebra (sX i) (ι (genericPoint T))
  haveI := isScalarTower_stalk_functionField (sX i) (ι (genericPoint T))
  have hkerP : ∀ (y : X i) (hy : y = P.genericPoint),
      IdealSheafData.stalk P.idealSheaf y = IsLocalRing.maximalIdeal ((X i).presheaf.stalk y) := by
    rintro y rfl; exact MMP.Resolution.Aux.stalk_idealSheaf_genericPoint P
  have hker : RingHom.ker (ι.stalkMap (genericPoint T)).hom =
      IsLocalRing.maximalIdeal ((X i).presheaf.stalk (ι (genericPoint T))) := by
    rw [ker_stalkMap_eq_stalk_idealSheaf ι P hrange (genericPoint T), hkerP _ hP]
  have hgP : ∀ (g : (X j).presheaf.stalk (D.f D.E.genericPoint)) (c : k),
      g - algebraMap k _ c ∈ IsLocalRing.maximalIdeal _ →
      ∃ gP : (X i).presheaf.stalk (ι (genericPoint T)),
        algebraMap _ (X i).functionField gP =
          (σ.toHom : FunctionFieldHom (sX i) (sX j)) (algebraMap _ (X j).functionField g) ∧
        (ι.stalkMap (genericPoint T)).hom gP = algebraMap k T.functionField c := by
    intro g c hgc
    obtain ⟨gP, hgP⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one P hP (hle g)
    refine ⟨gP, hgP, ?_⟩
    have hmem : gP - algebraMap k _ c ∈
        IsLocalRing.maximalIdeal ((X i).presheaf.stalk (ι (genericPoint T))) := by
      rw [mem_maximalIdeal_iff_divisorialValuation_lt_one P hP]
      have h1 := hlt _ hgc
      rw [map_sub, map_sub, ← IsScalarTower.algebraMap_apply, AlgHom.commutes] at h1
      rw [map_sub, hgP, ← IsScalarTower.algebraMap_apply]
      exact h1
    have h0 : (ι.stalkMap (genericPoint T)).hom (gP - algebraMap k _ c) = 0 := by
      rw [← RingHom.mem_ker, hker]; exact hmem
    rw [map_sub, sub_eq_zero, stalkMap_algebraMap_const (sX i) ι (genericPoint T) c] at h0
    exact h0
  obtain ⟨gPj, hgPj, hgPjc⟩ := hgP gj cj hcj
  obtain ⟨gP', hgP', hgP'c⟩ := hgP g' c' hc'
  have hu2 : (u : RationalPluriForms (sX i) 3 m) = algebraMap _ (X i).functionField gPj •
      formPow (exteriorPower.ιMulti (X i).functionField (2 + 1)
        (Fin.cons ((algebraMap _ (X i).functionField t)⁻¹ •
          KaehlerDifferential.D k _ (algebraMap _ (X i).functionField t))
          fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ (X i).functionField (e' b)))) m := by
    have h1 := hpullm m (algebraMap _ _ gj)
    rw [← hgPj] at h1
    rw [hu, hgj]
    exact h1
  have hsi2 : (s i : RationalPluriForms (sX i) 3 m) = algebraMap _ (X i).functionField gP' •
      formPow (exteriorPower.ιMulti (X i).functionField (2 + 1)
        (Fin.cons ((algebraMap _ (X i).functionField t)⁻¹ •
          KaehlerDifferential.D k _ (algebraMap _ (X i).functionField t))
          fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ (X i).functionField (e' b)))) m := by
    have h1 := hpullm m (algebraMap _ _ g')
    rw [← hgP'] at h1
    rw [← hσσ, hg']
    exact h1
  -- the point residues of `s_i` on `X_i` and of `s_j` on `X_j`
  haveI := Fq.isIntegral_stratum
  haveI := Fq.isNormal_stratum
  haveI := Fq.isLocallyNoetherian_stratum
  letI := functionFieldAlgebra (ιq ≫ sX i)
  have hRsi : R.toFun i Fq 0 (s i) = c' • (show RationalPluriForms (ιq ≫ sX i) 0 m from
      formPow (exteriorPower.ιMulti Sq.functionField 0 ![]) m) := by
    have h1 := hrecq gP' c' hgP'c
    have h2 : IsIteratedResidueRec (s i : RationalPluriForms (sX i) 3 m) Fq 0
        (c' • (show RationalPluriForms (ιq ≫ sX i) 0 m from
          formPow (exteriorPower.ιMulti Sq.functionField 0 ![]) m)) := by
      rw [hsi2]; exact h1
    exact IsIteratedResidueRec.unique Fq (R.isIteratedResidue i Fq 0 (s i) hdimq).rec' h2
  have hQj : (Divisor.toQDivisor (divisorOfForm (show RationalPluriForms (sX j) 3 ((1 : ℕ) : ℤ)
      from formPow (exteriorPower.ιMulti (X j).functionField 3 fun a =>
        (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField (z a))⁻¹ •
          KaehlerDifferential.D k (X j).functionField (algebraMap ((X j).presheaf.stalk
            (D.f D.E.genericPoint)) (X j).functionField (z a))) 1)) + B j).IsQCartier :=
    (show (Divisor.toQDivisor K' + B j).IsQCartier from ⟨_, hm0, hmK'⟩).add_of_linearlyEquivalent
      (by simpa using (MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXj hK' hτ'0).symm)
  obtain ⟨ρj, hρj⟩ := exists_heq_rationalPluriForms (Category.id_comp (sX j)).symm
    (s j : RationalPluriForms (sX j) 3 m)
  obtain ⟨Sx, ιx, Bx, Fx, hlenx, hdimx, hrecx⟩ := exists_flag_isIteratedResidueRec_of_sncPoint
    (s j : RationalPluriForms (sX j) 3 m) 3 (.refl (R.setting.isPair j).isPair) (sX j)
    (Category.id_comp _) hXj (R.setting.isDltPair j) hnj (D.f D.E.genericPoint) hxcl z hz hsm L hL
    hLx hLz hBL hL1 hQj gj cj hcj ⟨ρj, ⟨rfl, hρj.symm⟩, hρj.symm.trans (heq_of_eq hgj)⟩
  haveI := Fx.isIntegral_stratum
  haveI := Fx.isNormal_stratum
  haveI := Fx.isLocallyNoetherian_stratum
  letI := functionFieldAlgebra (ιx ≫ sX j)
  have hRsj : R.toFun j Fx 0 (s j) = cj • (show RationalPluriForms (ιx ≫ sX j) 0 m from
      formPow (exteriorPower.ιMulti Sx.functionField 0 ![]) m) :=
    IsIteratedResidueRec.unique Fx (R.isIteratedResidue j Fx 0 (s j) hdimx).rec' hrecx
  -- preadmissibility at the two points
  haveI : LocallyOfFiniteType (ιq ≫ sX i) := Fq.isNormalVariety.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (ιx ≫ sX j) := Fx.isNormalVariety.1.toLocallyOfFiniteType
  haveI := Fq.isNormalVariety.1
  haveI := Fx.isNormalVariety.1
  haveI : CompactSpace Sq := QuasiCompact.compactSpace_of_compactSpace (ιq ≫ sX i)
  haveI : CompactSpace Sx := QuasiCompact.compactSpace_of_compactSpace (ιx ≫ sX j)
  obtain ⟨σpt⟩ := nonempty_functionFieldEquiv_of_topologicalKrullDim_eq_zero (ιq ≫ sX i)
    (ιx ≫ sX j) hdimq hdimx
  have hσpt := isCrepantBirationalMap_of_topologicalKrullDim_eq_zero (k := k) hdimq hdimx Bq Bx σpt
  have hpre := hs i j Fq Fx 0 (by rw [hlenq]; norm_num) (by rw [hlenx]; norm_num) hdimq hdimx
    σpt hσpt
  rw [hRsj, hRsi, pluriformPullback_smul_formPow_ιMulti_zero hdimq hdimx] at hpre
  have hcc : cj = c' := by
    letI := functionFieldAlgebra (ιq ≫ sX i)
    have h0 : (algebraMap k Sq.functionField cj - algebraMap k Sq.functionField c') •
        (show RationalPluriForms (ιq ≫ sX i) 0 m from
          formPow (exteriorPower.ιMulti Sq.functionField 0 ![]) m) = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.2 hpre
    rcases smul_eq_zero.1 h0 with h | h
    · exact (algebraMap k Sq.functionField).injective (sub_eq_zero.1 h)
    · exact absurd h (formPow_ιMulti_zero_ne_zero m)
  -- the residues along `P` agree
  subst hcc
  have he2 : e = 2 := by
    have := he.symm.trans hdT
    exact_mod_cast this
  subst he2
  have hres_m := isPoincareResidue_formPow_dlog (sX i) ι m t e' he' ht
  set θm : RationalPluriForms (ι ≫ sX i) 2 m := formPow (exteriorPower.ιMulti T.functionField 2
    fun b => ((ι.stalkMap (genericPoint T)).hom (e' b))⁻¹ •
      KaehlerDifferential.D k T.functionField ((ι.stalkMap (genericPoint T)).hom (e' b))) m
    with hθm
  have hRu1 : IsPoincareResidue (sX i) ι 2 m (u : RationalPluriForms (sX i) 3 m) (cj • θm) := by
    have h1 := IsPoincareResidue.smul_stalk hres_m gPj
    rw [hgPjc] at h1
    rw [hu2]
    exact h1
  have hRs1 : IsPoincareResidue (sX i) ι 2 m (s i : RationalPluriForms (sX i) 3 m) (cj • θm) := by
    have h1 := IsPoincareResidue.smul_stalk hres_m gP'
    rw [hgP'c] at h1
    rw [hsi2]
    exact h1
  have hs1 : sX i = 𝟙 (X i) ≫ sX i := (Category.id_comp _).symm
  have hs1' : ι ≫ sX i = ι ≫ 𝟙 (X i) ≫ sX i := by rw [Category.id_comp]
  have hs2 : ι ≫ sX i = (ι ≫ 𝟙 (X i)) ≫ sX i := by simp
  obtain ⟨ρ1, hρ1⟩ := exists_heq_rationalPluriForms hs1' (cj • θm)
  obtain ⟨X1, hX1⟩ := exists_heq_rationalPluriForms hs2 (cj • θm)
  have hrec : ∀ ω : logPluricanonicalSections (sX i) 3 m (B i),
      IsPoincareResidue (sX i) ι 2 m (ω : RationalPluriForms (sX i) 3 m) (cj • θm) →
      IsIteratedResidueRec (ω : RationalPluriForms (sX i) 3 m) (.step (.refl h) ι BT hι) 2 X1 := by
    intro ω hω
    obtain ⟨ρ0, hρ0⟩ := exists_heq_rationalPluriForms hs1 (ω : RationalPluriForms (sX i) 3 m)
    exact ⟨ρ0, ⟨rfl, hρ0.symm⟩, ρ1, IsPoincareResidue.congr_structure hs1 hω hρ0 hρ1,
      hX1.symm.trans hρ1⟩
  rw [IsIteratedResidueRec.unique _ (R.isIteratedResidue i _ 2 u hdT).rec' (hrec u hRu1),
    IsIteratedResidueRec.unique _ (R.isIteratedResidue i _ 2 (s i) hdT).rec' (hrec (s i) hRs1)]

/-- A rational pluriform `(dlog w)^m` on a curve is nonzero when `dw` spans `Ω_{k(Y)/k}`. -/
private theorem stalkMapExc_formPow_dlog_ne_zero {k : Type} [Field k] [CharZero k]
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] (hd : topologicalKrullDim Y = (1 : ℕ))
    {w : Y.functionField}
    (hw : letI := functionFieldAlgebra sY
      Submodule.span Y.functionField {KaehlerDifferential.D k Y.functionField w} = ⊤) (m : ℕ) :
    letI := functionFieldAlgebra sY
    (formPow (exteriorPower.ιMulti Y.functionField 1 fun _ =>
      w⁻¹ • KaehlerDifferential.D k Y.functionField w) m : RationalPluriForms sY 1 m) ≠ 0 := by
  letI := functionFieldAlgebra sY
  refine (exists_basis_topForms (sX := sY) hd).elim fun b => ?_
  haveI : Nontrivial (⋀[Y.functionField]^1 Ω[Y.functionField⁄k]) :=
    nontrivial_of_ne _ _ (b.ne_zero ())
  haveI : Nontrivial Ω[Y.functionField⁄k] :=
    (exteriorPower.oneEquiv Y.functionField Ω[Y.functionField⁄k]).symm.toEquiv.nontrivial
  have := smul_formPow_ne_zero hd (ιMulti_one_dlog_ne_zero hw) one_ne_zero m
  rwa [one_smul] at this

/-- A ring homomorphism into `L` whose values all lie in the image of an injective ring
homomorphism `g : B → L` factors through `g`. -/
private theorem stalkMapExc_exists_ringHom_lift {A B L : Type*} [CommRing A] [CommRing B]
    [CommRing L] (f : A →+* L) (g : B →+* L) (hg : Function.Injective g)
    (hf : ∀ a, ∃ b, g b = f a) : ∃ φ : A →+* B, ∀ a, g (φ a) = f a := by
  choose φ hφ using hf
  refine ⟨{ toFun := φ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hφ⟩
  · exact hg (by rw [hφ, map_one, map_one])
  · exact fun a b => hg (by rw [map_mul, hφ, hφ, hφ, map_mul])
  · exact hg (by rw [hφ, map_zero, map_zero])
  · exact fun a b => hg (by rw [map_add, hφ, hφ, hφ, map_add])

/-- The curve case of `stalkMap_eq_of_isExceptional_of_curve`, first half: when the centre `y₀`
of `ν₀` has coheight one it is the generic point of a prime divisor `C` of `T` with `ν₀ = v_C`;
the residue `dlog ē ∧ dlog v̄` of the frame has a simple pole along `C`, and `C` has coefficient
at least one in `B_T`. -/
private theorem stalkMapExc_exists_curve_centre
    (R : ResidueRestriction sX B 3 m) {i j : I} [CharZero k] [IsAlgClosed k]
    [LocallyOfFiniteType (sX i)] [CompactSpace (X i)]
    {s : ∀ l, logPluricanonicalSections (sX l) 3 m (B l)}
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T}
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T] [IsNormal T]
    [IsLocallyNoetherian T] [LocallyOfFiniteType (ι ≫ sX i)] [IsClosedImmersion ι]
    [CompactSpace T]
    (P : Mori.PrimeDivisor (X i)) (hrange : Set.range ι.base = (P.support : Set (X i)))
    (D : DivisorOver k (sX j)) (v : (X j).presheaf.stalk (D.f D.E.genericPoint)) (hvu : IsUnit v)
    (t : (X i).presheaf.stalk (ι (genericPoint T)))
    (e' : Fin 2 → (X i).presheaf.stalk (ι (genericPoint T))) (he' : ∀ b, IsUnit (e' b))
    (ht : (X i).ord (algebraMap _ (X i).functionField t) (ι (genericPoint T)) = 1)
    (gj g' : (X j).presheaf.stalk (D.f D.E.genericPoint))
    (u : logPluricanonicalSections (sX i) 3 m (B i))
    (gPj gP' : (X i).presheaf.stalk (ι (genericPoint T)))
    (hu2 : letI := functionFieldAlgebra (sX i)
      (u : RationalPluriForms (sX i) 3 m) = algebraMap _ (X i).functionField gPj •
        formPow (exteriorPower.ιMulti (X i).functionField (2 + 1)
          (Fin.cons ((algebraMap _ (X i).functionField t)⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ (X i).functionField t))
            fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
              KaehlerDifferential.D k _ (algebraMap _ (X i).functionField (e' b)))) m)
    (hsi2 : letI := functionFieldAlgebra (sX i)
      (s i : RationalPluriForms (sX i) 3 m) = algebraMap _ (X i).functionField gP' •
        formPow (exteriorPower.ιMulti (X i).functionField (2 + 1)
          (Fin.cons ((algebraMap _ (X i).functionField t)⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ (X i).functionField t))
            fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
              KaehlerDifferential.D k _ (algebraMap _ (X i).functionField (e' b)))) m)
    {TZ : Scheme.{0}} {ιZ : TZ ⟶ X j} [IsIntegral TZ] [IsNormal TZ] [IsLocallyNoetherian TZ]
    [LocallyOfFiniteType (ιZ ≫ sX j)] [IsClosedImmersion ιZ] [CompactSpace TZ]
    (resZ : (X j).presheaf.stalk (D.f D.E.genericPoint) →+* TZ.functionField)
    (hwZ' : letI := functionFieldAlgebra (ιZ ≫ sX j)
      Submodule.span TZ.functionField {KaehlerDifferential.D k TZ.functionField (resZ v)} = ⊤)
    (lam : TZ.functionField →+* T.functionField)
    (hlamk : letI := functionFieldAlgebra (ι ≫ sX i); letI := functionFieldAlgebra (ιZ ≫ sX j)
      ∀ c : k, lam (algebraMap k _ c) = algebraMap k _ c)
    (hlamv : lam (resZ v) = (ι.stalkMap (genericPoint T)).hom (e' 1))
    (hgPjl : (ι.stalkMap (genericPoint T)).hom gPj = lam (resZ gj))
    (hgP'l : (ι.stalkMap (genericPoint T)).hom gP' = lam (resZ g'))
    (hzero : ¬((ι.stalkMap (genericPoint T)).hom gPj = 0 ∧
      (ι.stalkMap (genericPoint T)).hom gP' = 0))
    (ν₀ : Valuation T.functionField ℤᵐ⁰) (hν₀k : ∀ c, c ≠ 0 → ν₀ (lam c) = 1)
    (eb : T.functionField) (heb : eb = (ι.stalkMap (genericPoint T)).hom (e' 0))
    (hν₀e : ν₀ eb = WithZero.exp (-1)) (hν₀res : ∀ f, ν₀ f ≤ 1 → ∃ c, ν₀ (f - lam c) < 1)
    (y₀ : T) (hy₀le : ∀ a : T.presheaf.stalk y₀, ν₀ (algebraMap _ T.functionField a) ≤ 1)
    (hy₀lt : ∀ a ∈ IsLocalRing.maximalIdeal (T.presheaf.stalk y₀),
      ν₀ (algebraMap _ T.functionField a) < 1)
    (hA : Order.coheight y₀ = 1) :
    letI := functionFieldAlgebra (ι ≫ sX i)
    ∃ C : Mori.PrimeDivisor T, C.genericPoint = y₀ ∧ ν₀ = C.divisorialValuation ∧
      1 ≤ BT.coeff C ∧
      C.ordForm (show RationalPluriForms (ι ≫ sX i) 2 1 from formPow
        (exteriorPower.ιMulti T.functionField 2 fun b : Fin 2 =>
          ((ι.stalkMap (genericPoint T)).hom (e' b))⁻¹ •
            KaehlerDifferential.D k T.functionField ((ι.stalkMap (genericPoint T)).hom (e' b)))
        1) = -1 ∧
      exteriorPower.ιMulti T.functionField 2 (fun b : Fin 2 =>
        ((ι.stalkMap (genericPoint T)).hom (e' b))⁻¹ •
          KaehlerDifferential.D k T.functionField ((ι.stalkMap (genericPoint T)).hom (e' b)))
        ≠ 0 := by
  classical
  have hPi := R.setting.isPair i
  have hX := hPi.isPair.1
  haveI := hX.1
  have hni := R.setting.topologicalKrullDim_eq i
  letI := functionFieldAlgebra (sX i)
  letI := functionFieldAlgebra (ι ≫ sX i)
  letI := functionFieldAlgebra (ιZ ≫ sX j)
  have hιs : IsAdjunctionStep (sX i) (B i) ι BT := hι
  have hdT : topologicalKrullDim T = (2 : ℕ) :=
    topologicalKrullDim_eq_of_range_eq_support (sX i) ι P hrange hni
  obtain ⟨C, hCη⟩ : ∃ C : Mori.PrimeDivisor T, C.genericPoint = y₀ :=
    ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hA,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hA⟩
  have hν₀C : ν₀ = C.divisorialValuation := by
    refine eq_of_isEquiv_of_exp_neg_one' ?_ ⟨eb, hν₀e⟩ ?_
    · refine Valuation.isEquiv_iff_val_le_one.2 fun {f} => ?_
      constructor
      · intro hf
        by_contra hC
        push Not at hC
        have hf0 : f ≠ 0 := by rintro rfl; simp at hC
        have hinv : C.divisorialValuation f⁻¹ < 1 := by
          rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hC
        obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one C hCη.symm hinv.le
        have hcm : c ∈ IsLocalRing.maximalIdeal _ :=
          (mem_maximalIdeal_iff_divisorialValuation_lt_one C hCη.symm c).2 (by rw [hc]; exact hinv)
        have h1 := hy₀lt c hcm
        rw [hc, map_inv₀] at h1
        have hne : ν₀ f ≠ 0 := (Valuation.ne_zero_iff _).2 hf0
        have h2 : (1 : ℤᵐ⁰) < 1 := calc
          (1 : ℤᵐ⁰) = ν₀ f * (ν₀ f)⁻¹ := (mul_inv_cancel₀ hne).symm
          _ ≤ 1 * (ν₀ f)⁻¹ := mul_le_mul' hf le_rfl
          _ < 1 := by rw [one_mul]; exact h1
        exact lt_irrefl _ h2
      · intro hf
        obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one C hCη.symm hf
        rw [← hc]; exact hy₀le c
    · haveI := C.isDiscreteValuationRing_localRing
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible C.localRing
      exact ⟨_, C.divisorialValuation_algebraMap_of_irreducible hϖ⟩
  have hy₀C : y₀ ∈ C.support := by
    rw [← hCη, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  -- `λ` lands in the local ring of `C`, and induces `k(Z) ↠ κ(C)`
  have hlam1 : ∀ c : TZ.functionField, c ≠ 0 → ν₀ (lam c) = 1 := fun c hc => hν₀k c hc
  have hlamle : ∀ c : TZ.functionField, C.divisorialValuation (lam c) ≤ 1 := by
    intro c
    rw [← hν₀C]
    by_cases hc : c = 0
    · rw [hc, map_zero, map_zero]; exact zero_le'
    · exact (hlam1 c hc).le
  have hinj : Function.Injective (algebraMap (T.presheaf.stalk y₀) T.functionField) :=
    IsFractionRing.injective _ _
  refine (stalkMapExc_exists_ringHom_lift lam (algebraMap (T.presheaf.stalk y₀) T.functionField)
    hinj fun c => exists_algebraMap_eq_of_divisorialValuation_le_one C hCη.symm
      (hlamle c)).elim fun μ'' hμ'' => ?_
  letI := stalkAlgebra (ι ≫ sX i) y₀
  haveI := isScalarTower_stalk_functionField (ι ≫ sX i) y₀
  let μ : TZ.functionField →ₐ[k] IsLocalRing.ResidueField (T.presheaf.stalk y₀) :=
    { (IsLocalRing.residue (T.presheaf.stalk y₀)).comp μ'' with
      commutes' := fun c => by
        change IsLocalRing.residue _ (μ'' (algebraMap k _ c)) = _
        have : μ'' (algebraMap k _ c) = algebraMap k (T.presheaf.stalk y₀) c := hinj (by
          rw [hμ'', hlamk, ← IsScalarTower.algebraMap_apply])
        rw [this]; rfl }
  have hμs : Function.Surjective μ := by
    intro r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    have ha : ν₀ (algebraMap _ T.functionField a) ≤ 1 := hy₀le a
    obtain ⟨c, hc⟩ := hν₀res _ ha
    refine ⟨c, ?_⟩
    change IsLocalRing.residue _ (μ'' c) = IsLocalRing.residue _ a
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      mem_maximalIdeal_iff_divisorialValuation_lt_one C hCη.symm, ← hν₀C, map_sub, hμ'',
      ← Valuation.map_neg, neg_sub]
    exact hc
  -- the frame `dē, dv̄` at the generic point of `C`
  have hwκ := span_D_eq_top_of_surjective μ hμs (fun _ : Fin 1 => resZ v)
    (by rw [Set.range_const]; exact hwZ')
  -- lifts of `ē` and `v̄` to `𝒪_{T,C}`
  have hebC : C.divisorialValuation eb = WithZero.exp (-1) := by rw [← hν₀C]; exact hν₀e
  obtain ⟨ebC, hebC'⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one C hCη.symm
    (by rw [hebC, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have hvZ0 : resZ v ≠ 0 := (hvu.map resZ).ne_zero
  haveI := C.isDiscreteValuationRing_localRing
  have hDVR : ∀ (y : T) (hy : y = C.genericPoint), IsDiscreteValuationRing (T.presheaf.stalk y) := by
    rintro y rfl; exact C.isDiscreteValuationRing_localRing
  haveI := hDVR y₀ hCη.symm
  have hle1 : ∀ a : T.presheaf.stalk y₀, C.divisorialValuation (algebraMap _ T.functionField a) ≤ 1 :=
    fun a => hν₀C ▸ hy₀le a
  have hunitC : ∀ a : T.presheaf.stalk y₀,
      C.divisorialValuation (algebraMap _ T.functionField a) = 1 → IsUnit a := by
    intro a ha
    by_contra hnu
    have := (mem_maximalIdeal_iff_divisorialValuation_lt_one C hCη.symm a).1
      ((IsLocalRing.mem_maximalIdeal _).2 hnu)
    rw [ha] at this; exact lt_irrefl _ this
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (T.presheaf.stalk y₀)
  have hvirr : ∀ (y : T) (hy : y = C.genericPoint) (p : T.presheaf.stalk y), Irreducible p →
      C.divisorialValuation (algebraMap _ T.functionField p) = WithZero.exp (-1) := by
    rintro y rfl p hp; exact C.divisorialValuation_algebraMap_of_irreducible hp
  have hϖv := hvirr y₀ hCη.symm ϖ hϖ
  have hϖ0 : algebraMap _ T.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  obtain ⟨w, hw⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one C hCη.symm
    (f := eb / algebraMap _ T.functionField ϖ) (by
      rw [map_div₀, hebC, hϖv, div_self (by simp)])
  have hwu : IsUnit w := hunitC w (by rw [hw, map_div₀, hebC, hϖv, div_self (by simp)])
  have hebϖ : ebC = w * ϖ := hinj (by rw [map_mul, hw, hebC', div_mul_cancel₀ _ hϖ0])
  have hspan_eb : Ideal.span {ebC} = IsLocalRing.maximalIdeal (T.presheaf.stalk y₀) := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, hebϖ]
    exact Ideal.span_singleton_mul_left_unit hwu ϖ
  have hkerC : ∀ (y : T) (hy : y = C.genericPoint), IdealSheafData.stalk C.idealSheaf y =
      IsLocalRing.maximalIdeal (T.presheaf.stalk y) := by
    rintro y rfl; exact MMP.Resolution.Aux.stalk_idealSheaf_genericPoint C
  have hCid : IdealSheafData.stalk C.idealSheaf y₀ = Ideal.span {ebC} := by
    rw [hkerC y₀ hCη.symm, hspan_eb]
  set vC := μ'' (resZ v) with hvCdef
  have hvCu : IsUnit vC := hunitC vC (by rw [hμ'', ← hν₀C]; exact hlam1 _ hvZ0)
  -- smoothness of `T` at the generic point of `C`
  have hregC : IsRegularSystemOfParameters (![ebC] : Fin 1 → T.presheaf.stalk y₀) := by
    refine ⟨by rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty]; exact hspan_eb, ?_⟩
    rw [ringKrullDim_stalk_eq_coheight, hA]; rfl
  haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hregC
  have hsmC : y₀ ∈ Mori.smoothLocus (ι ≫ sX i) := mem_smoothLocus_of_isRegularLocalRing _ y₀
  obtain ⟨rC, ⟨bC⟩⟩ := exists_basis_kaehler_stalk_of_mem_smoothLocus (ι ≫ sX i) hsmC
  haveI : Module.Finite (T.presheaf.stalk y₀) Ω[T.presheaf.stalk y₀⁄k] := Module.Finite.of_basis bC
  have hspanC' := span_D_sum_eq_top_of_span_eq_maximalIdeal (k := k) (![ebC] : Fin 1 → _)
    (by rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty]; exact hspan_eb)
    (fun _ : Fin 1 => vC) hwκ
  have hspanC : Submodule.span (T.presheaf.stalk y₀) (Set.range fun a : Fin 2 =>
      KaehlerDifferential.D k (T.presheaf.stalk y₀) (![ebC, vC] a)) = ⊤ := by
    rw [eq_top_iff, ← hspanC', Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rcases a with (a | a)
    · fin_cases a; exact Submodule.subset_span ⟨0, rfl⟩
    · exact Submodule.subset_span ⟨1, rfl⟩
  have hebC0 : ebC ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hebC'; rw [← hebC', map_zero] at hebC
    exact WithZero.exp_ne_zero hebC.symm
  have hordθ := ordForm_formPow_dlog_eq_of_isUnit (sX := ι ≫ sX i) hdT 1 ![ebC, vC]
    (fun a => by fin_cases a; exact hebC0; exact hvCu.ne_zero) hspanC {0} (fun _ => C)
    (Set.injOn_singleton _ _) (fun _ _ => hy₀C) (fun a ha => by rw [ha]; exact hCid)
    (fun a ha => by
      fin_cases a
      · exact absurd rfl ha
      · exact hvCu) C hy₀C
  rw [if_pos ⟨0, rfl, rfl⟩] at hordθ
  -- the residue `θ` of `σ^*τ` along `P` is `dlog ē ∧ dlog v̄`
  have hθfun : (fun b : Fin 2 => ((ι.stalkMap (genericPoint T)).hom (e' b))⁻¹ •
      KaehlerDifferential.D k T.functionField ((ι.stalkMap (genericPoint T)).hom (e' b))) =
      fun a => (algebraMap _ T.functionField (![ebC, vC] a))⁻¹ •
        KaehlerDifferential.D k T.functionField (algebraMap _ T.functionField (![ebC, vC] a)) := by
    have h1 : algebraMap _ T.functionField vC = (ι.stalkMap (genericPoint T)).hom (e' 1) := by
      rw [hvCdef, hμ'', hlamv]
    have h0 : algebraMap _ T.functionField ebC = (ι.stalkMap (genericPoint T)).hom (e' 0) := by
      rw [hebC', heb]
    funext b; fin_cases b
    · show _ = (algebraMap _ T.functionField ebC)⁻¹ •
        KaehlerDifferential.D k T.functionField (algebraMap _ T.functionField ebC)
      rw [h0]; rfl
    · show _ = (algebraMap _ T.functionField vC)⁻¹ •
        KaehlerDifferential.D k T.functionField (algebraMap _ T.functionField vC)
      rw [h1]; rfl
  set ωT : ⋀[T.functionField]^2 Ω[T.functionField⁄k] := exteriorPower.ιMulti T.functionField 2
    (fun b : Fin 2 => ((ι.stalkMap (genericPoint T)).hom (e' b))⁻¹ •
      KaehlerDifferential.D k T.functionField ((ι.stalkMap (genericPoint T)).hom (e' b)))
    with hωT
  have hordωT : C.ordForm (show RationalPluriForms (ι ≫ sX i) 2 1 from formPow ωT 1) = -1 := by
    rw [hωT, hθfun]; exact hordθ
  have hωT0 : ωT ≠ 0 := by
    intro h0
    rw [h0] at hordωT
    have : (show RationalPluriForms (ι ≫ sX i) 2 1 from formPow (0 : ⋀[T.functionField]^2
        Ω[T.functionField⁄k]) 1) = 0 := formPow_zero_of_pos one_pos
    rw [this, Mori.PrimeDivisor.ordForm_zero] at hordωT
    exact absurd hordωT (by decide)
  -- residues along `P` of log sections written in the frame
  have hres_m := isPoincareResidue_formPow_dlog (sX i) ι m t e' he' ht
  obtain ⟨K, hK, hmK⟩ := exists_canonical_cartier R i
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast R.setting.pos.ne'
  have hcoeff_of : ∀ (ω : logPluricanonicalSections (sX i) 3 m (B i))
      (g : (X i).presheaf.stalk (ι (genericPoint T))) (c : TZ.functionField),
      (ω : RationalPluriForms (sX i) 3 m) = algebraMap _ (X i).functionField g •
        formPow (exteriorPower.ιMulti (X i).functionField (2 + 1)
          (Fin.cons ((algebraMap _ (X i).functionField t)⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ (X i).functionField t))
            fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
              KaehlerDifferential.D k _ (algebraMap _ (X i).functionField (e' b)))) m →
      (ι.stalkMap (genericPoint T)).hom g = lam c → c ≠ 0 → 1 ≤ BT.coeff C := by
    intro ω g c hω hgc hc0
    obtain ⟨ρω, hρω, hρωlog⟩ := exists_isPoincareResidue_mem_logPluricanonicalSections hX
      (d := 2) (by rw [hni]) (R.setting.isDltPair i).2.1 hK ⟨_, hm0, hmK⟩ hιs
      (by norm_num) R.setting.pos ω.2
    have hr0 := IsPoincareResidue.smul_stalk hres_m g
    have hr : IsPoincareResidue (sX i) ι 2 m (ω : RationalPluriForms (sX i) 3 m)
        ((ι.stalkMap (genericPoint T)).hom g • formPow ωT m) := by
      rw [hω]; exact hr0
    have heq := IsPoincareResidue.unique hιs hρω hr
    have hgc0 : (ι.stalkMap (genericPoint T)).hom g ≠ 0 := by
      rw [hgc]; exact (map_ne_zero lam).2 hc0
    have hne : ρω ≠ 0 := by
      rw [heq]
      exact smul_formPow_ne_zero hdT hωT0 hgc0 m
    have h1 := (mem_pluricanonicalSections_of_ne_bot top_ne_bot).1 hρωlog C
      ⟨C.genericPoint, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
        trivial⟩ hne
    rw [heq, ordForm_smul_formPow hdT C hωT0 hgc0 m, hordωT] at h1
    have hord0 : T.ord ((ι.stalkMap (genericPoint T)).hom g) C.genericPoint = 0 := by
      have h2 := C.divisorialValuation_eq_exp_neg_ord hgc0
      rw [← hν₀C, hgc, hlam1 c hc0] at h2
      have h3 : WithZero.exp (0 : ℤ) = WithZero.exp (-T.ord (lam c) C.genericPoint) := by
        rw [WithZero.exp_zero]; exact h2
      rw [hgc]
      have := WithZero.exp_injective h3
      omega
    rw [hord0, DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul,
      zsmul_eq_mul] at h1
    have h4 : (m : ℤ) ≤ ⌊((m : ℤ) : ℚ) * BT.coeff C⌋ := by linarith
    have h5 := (Int.le_floor.1 h4)
    have hmq : (0 : ℚ) < m := by exact_mod_cast R.setting.pos
    push_cast at h5
    exact (le_mul_iff_one_le_right hmq).1 h5
  have hBC : 1 ≤ BT.coeff C := by
    rcases not_and_or.1 hzero with h0 | h0
    · exact hcoeff_of u gPj (resZ gj) hu2 hgPjl (fun hc => h0 (by rw [hgPjl, hc, map_zero]))
    · exact hcoeff_of (s i) gP' (resZ g') hsi2 hgP'l
        (fun hc => h0 (by rw [hgP'l, hc, map_zero]))
  exact ⟨C, hCη, hν₀C, hBC, hordωT, hωT0⟩

/-- The lift `ψ : 𝒪_{X_j, Z} → 𝒪_{X_i, P}` of `σ` on local rings, compatible with `λ`. -/
private theorem stalkMapExc_exists_stalk_lift {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    {T : Scheme.{0}} {ι : T ⟶ X i} [IsIntegral T] (P : Mori.PrimeDivisor (X i))
    (hP : ι (genericPoint T) = P.genericPoint) (D : DivisorOver k (sX j))
    (hle : ∀ r : (X j).presheaf.stalk (D.f D.E.genericPoint),
      P.divisorialValuation ((σ.toHom) (algebraMap _ (X j).functionField r)) ≤ 1)
    {TZ : Scheme.{0}} {ιZ : TZ ⟶ X j} [IsIntegral TZ]
    (hgenZ : ιZ (genericPoint TZ) = D.f D.E.genericPoint)
    (resZ : (X j).presheaf.stalk (D.f D.E.genericPoint) →+* TZ.functionField)
    (hstalkZ : ∀ (hsp : D.f D.E.genericPoint ⤳ ιZ (genericPoint TZ))
      (a : (X j).presheaf.stalk (ιZ (genericPoint TZ))),
      resZ (((X j).presheaf.stalkSpecializes hsp).hom a) = (ιZ.stalkMap (genericPoint TZ)).hom a)
    (lam : TZ.functionField →+* T.functionField)
    (hlamσ : ∀ (r : (X j).presheaf.stalk (D.f D.E.genericPoint))
      (a : (X i).presheaf.stalk (ι (genericPoint T))),
      algebraMap _ (X i).functionField a = (σ.toHom) (algebraMap _ (X j).functionField r) →
      lam (resZ r) = (ι.stalkMap (genericPoint T)).hom a) :
    ∃ ψ : (X j).presheaf.stalk (ιZ (genericPoint TZ)) →+*
        (X i).presheaf.stalk (ι (genericPoint T)),
      (∀ a, algebraMap _ (X i).functionField (ψ a) =
        (σ.toHom) (algebraMap _ (X j).functionField a)) ∧
      ∀ a, lam ((ιZ.stalkMap (genericPoint TZ)).hom a) =
        (ι.stalkMap (genericPoint T)).hom (ψ a) := by
  have hlift : ∀ r : (X j).presheaf.stalk (D.f D.E.genericPoint),
      ∃ a : (X i).presheaf.stalk (ι (genericPoint T)),
        algebraMap _ (X i).functionField a = (σ.toHom) (algebraMap _ (X j).functionField r) :=
    fun r => exists_algebraMap_eq_of_divisorialValuation_le_one P hP (hle r)
  choose ψ0 hψ0 using hlift
  have hinjX : Function.Injective
      (algebraMap ((X i).presheaf.stalk (ι (genericPoint T))) (X i).functionField) :=
    IsFractionRing.injective _ _
  let ψx : (X j).presheaf.stalk (D.f D.E.genericPoint) →+*
      (X i).presheaf.stalk (ι (genericPoint T)) :=
    { toFun := ψ0
      map_one' := hinjX (by rw [hψ0, map_one, map_one, map_one])
      map_mul' := fun a b => hinjX (by rw [map_mul, hψ0, hψ0, hψ0, map_mul, map_mul])
      map_zero' := hinjX (by rw [hψ0, map_zero, map_zero, map_zero])
      map_add' := fun a b => hinjX (by rw [map_add, hψ0, hψ0, hψ0, map_add, map_add]) }
  have hψx : ∀ r, algebraMap _ (X i).functionField (ψx r) =
      (σ.toHom) (algebraMap _ (X j).functionField r) := hψ0
  have hspec : D.f D.E.genericPoint ⤳ ιZ (genericPoint TZ) := by rw [hgenZ]
  have hψ : ∀ a, algebraMap _ (X i).functionField
      ((ψx.comp ((X j).presheaf.stalkSpecializes hspec).hom) a) =
        (σ.toHom) (algebraMap _ (X j).functionField a) := by
    intro a
    rw [RingHom.comp_apply, hψx]
    congr 1
    change ((X j).presheaf.stalkSpecializes hspec ≫ (X j).presheaf.stalkSpecializes _).hom a =
      ((X j).presheaf.stalkSpecializes _).hom a
    rw [TopCat.Presheaf.stalkSpecializes_comp]
  have hlamψ : ∀ a, lam ((ιZ.stalkMap (genericPoint TZ)).hom a) =
      (ι.stalkMap (genericPoint T)).hom
        ((ψx.comp ((X j).presheaf.stalkSpecializes hspec).hom) a) := by
    intro a
    rw [← hstalkZ hspec a]
    exact hlamσ _ _ (by rw [RingHom.comp_apply]; exact hψx _)
  exact ⟨_, hψ, hlamψ⟩

/-- The curve case of `stalkMap_eq_of_isExceptional_of_curve`, second half: given the curve
`C` of `T` centring `ν₀`, the adjunction step onto `C`, the isomorphism `k(Z) ≅ k(C)` induced
by `λ`, its crepancy and the preadmissibility of `s` give the equality of the restricted
coefficients. -/
private theorem stalkMapExc_eq_of_curve_centre
    (R : ResidueRestriction sX B 3 m) {i j : I} [CharZero k] [IsAlgClosed k]
    [CompactSpace (X i)] [IsProper (sX i)] [IsProper (sX j)]
    (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {s : ∀ l, logPluricanonicalSections (sX l) 3 m (B l)} (hs : s ∈ preadmissibleSections R)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    [IsNormal T] [IsLocallyNoetherian T] [LocallyOfFiniteType (ι ≫ sX i)] [IsClosedImmersion ι]
    [CompactSpace T]
    (P : Mori.PrimeDivisor (X i))
    (hP1 : (B i).coeff P = 1)
    (hrange : Set.range ι.base = (P.support : Set (X i))) (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g))
    (z : Fin 2 → (X j).presheaf.stalk (D.f D.E.genericPoint))
    (v : (X j).presheaf.stalk (D.f D.E.genericPoint)) (hvu : IsUnit v)
    [CompactSpace (X j)]
    (U : (X j).Opens) (hxU : D.f D.E.genericPoint ∈ U)
    (hU : letI := functionFieldAlgebra (sX j)
      ∀ E : Mori.PrimeDivisor (X j), (E.support ∩ (U : Set (X j))).Nonempty →
      (Divisor.toQDivisor (divisorOfForm (show RationalPluriForms (sX j) 3 ((1 : ℕ) : ℤ) from
        formPow (exteriorPower.ιMulti (X j).functionField 3 fun a =>
          (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
            (![z 0, z 1, v] a))⁻¹ • KaehlerDifferential.D k (X j).functionField
              (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
                (![z 0, z 1, v] a))) 1)) + B j).coeff E = 0)
    (t : (X i).presheaf.stalk (ι (genericPoint T)))
    (e' : Fin 2 → (X i).presheaf.stalk (ι (genericPoint T))) (he' : ∀ b, IsUnit (e' b))
    (ht : (X i).ord (algebraMap _ (X i).functionField t) (ι (genericPoint T)) = 1)
    (hfr : letI := functionFieldAlgebra (sX i); letI := functionFieldAlgebra (sX j)
      exteriorPower.ιMulti (X i).functionField 3 (fun a =>
          ((σ.toHom) (algebraMap _ (X j).functionField (![z 0, z 1, v] a)))⁻¹ •
            KaehlerDifferential.D k (X i).functionField
              ((σ.toHom) (algebraMap _ (X j).functionField (![z 0, z 1, v] a)))) =
        exteriorPower.ιMulti (X i).functionField 3 (Fin.cons
          ((algebraMap _ (X i).functionField t)⁻¹ • KaehlerDifferential.D k _ (algebraMap _ _ t))
          fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ _ (e' b))))
    (gj g' : (X j).presheaf.stalk (D.f D.E.genericPoint))
    (hgj : letI := functionFieldAlgebra (sX j)
      (s j : RationalPluriForms (sX j) 3 m) = algebraMap _ (X j).functionField gj •
        (show RationalPluriForms (sX j) 3 m from formPow (exteriorPower.ιMulti (X j).functionField 3
          fun a => (algebraMap _ (X j).functionField (![z 0, z 1, v] a))⁻¹ •
            KaehlerDifferential.D k (X j).functionField
              (algebraMap _ (X j).functionField (![z 0, z 1, v] a))) m))
    (gPj gP' : (X i).presheaf.stalk (ι (genericPoint T)))
    (hsi2 : letI := functionFieldAlgebra (sX i)
      (s i : RationalPluriForms (sX i) 3 m) = algebraMap _ (X i).functionField gP' •
        formPow (exteriorPower.ιMulti (X i).functionField (2 + 1)
          (Fin.cons ((algebraMap _ (X i).functionField t)⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ (X i).functionField t))
            fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
              KaehlerDifferential.D k _ (algebraMap _ (X i).functionField (e' b)))) m)
    {TZ : Scheme.{0}} {ιZ : TZ ⟶ X j} [IsIntegral TZ] [IsNormal TZ] [IsLocallyNoetherian TZ]
    [LocallyOfFiniteType (ιZ ≫ sX j)] [IsClosedImmersion ιZ] [CompactSpace TZ]
    (resZ : (X j).presheaf.stalk (D.f D.E.genericPoint) →+* TZ.functionField)
    {BZ : QDivisor TZ} (FZ : StratumAdjunctionData (sX j) (B j) ιZ BZ)
    (hdimZ : topologicalKrullDim TZ = (1 : ℕ))
    (hrecZ : letI := functionFieldAlgebra (sX j); letI := functionFieldAlgebra (ιZ ≫ sX j)
      ∀ (g : (X j).presheaf.stalk (D.f D.E.genericPoint)) (m : ℕ), IsIteratedResidueRec
        (show RationalPluriForms (sX j) 3 m from algebraMap _ (X j).functionField g •
          formPow (exteriorPower.ιMulti (X j).functionField 3 fun a =>
            (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
              (![z 0, z 1, v] a))⁻¹ • KaehlerDifferential.D k (X j).functionField
                (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
                  (![z 0, z 1, v] a))) m)
        FZ 1 (resZ g • (show RationalPluriForms (ιZ ≫ sX j) 1 m from
          formPow (exteriorPower.ιMulti TZ.functionField 1
            fun _ => (resZ v)⁻¹ • KaehlerDifferential.D k TZ.functionField (resZ v)) m)))
    (hlenZ : FZ.length = 2) (hgenZ : ιZ (genericPoint TZ) = D.f D.E.genericPoint)
    (hpbZ : letI := functionFieldAlgebra (sX j); letI := functionFieldAlgebra (ιZ ≫ sX j)
      ∃ hgen, (Divisor.toQDivisor (divisorOfForm
        (show RationalPluriForms (sX j) 3 ((1 : ℕ) : ℤ) from
          formPow (exteriorPower.ιMulti (X j).functionField 3 fun a =>
            (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
              (![z 0, z 1, v] a))⁻¹ • KaehlerDifferential.D k (X j).functionField
                (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
                  (![z 0, z 1, v] a))) 1)) +
        B j).IsPullback ιZ hgen (Divisor.toQDivisor (divisorOfForm
          (show RationalPluriForms (ιZ ≫ sX j) 1 ((1 : ℕ) : ℤ) from
            formPow (exteriorPower.ιMulti TZ.functionField 1
              fun _ => (resZ v)⁻¹ • KaehlerDifferential.D k TZ.functionField (resZ v)) 1)) +
          BZ))
    (hwZ' : letI := functionFieldAlgebra (ιZ ≫ sX j)
      Submodule.span TZ.functionField {KaehlerDifferential.D k TZ.functionField (resZ v)} = ⊤)
    (lam : TZ.functionField →+* T.functionField)
    (hlamk : letI := functionFieldAlgebra (ι ≫ sX i); letI := functionFieldAlgebra (ιZ ≫ sX j)
      ∀ c : k, lam (algebraMap k _ c) = algebraMap k _ c)
    (hlamv : lam (resZ v) = (ι.stalkMap (genericPoint T)).hom (e' 1))
    (hgPjl : (ι.stalkMap (genericPoint T)).hom gPj = lam (resZ gj))
    (hgP'l : (ι.stalkMap (genericPoint T)).hom gP' = lam (resZ g'))
    (ψ : (X j).presheaf.stalk (ιZ (genericPoint TZ)) →+* (X i).presheaf.stalk (ι (genericPoint T)))
    (hψ : ∀ a, algebraMap _ (X i).functionField (ψ a) =
      (σ.toHom) (algebraMap _ (X j).functionField a))
    (hlamψ : ∀ a, lam ((ιZ.stalkMap (genericPoint TZ)).hom a) =
      (ι.stalkMap (genericPoint T)).hom (ψ a))
    (ν₀ : Valuation T.functionField ℤᵐ⁰) (hν₀k : ∀ c, c ≠ 0 → ν₀ (lam c) = 1)
    (eb : T.functionField) (heb : eb = (ι.stalkMap (genericPoint T)).hom (e' 0))
    (hν₀e : ν₀ eb = WithZero.exp (-1)) (hν₀res : ∀ f, ν₀ f ≤ 1 → ∃ c, ν₀ (f - lam c) < 1)
    (y₀ : T) (hy₀le : ∀ a : T.presheaf.stalk y₀, ν₀ (algebraMap _ T.functionField a) ≤ 1)
    (C : Mori.PrimeDivisor T) (hCη : C.genericPoint = y₀) (hν₀C : ν₀ = C.divisorialValuation)
    (hBC : 1 ≤ BT.coeff C)
    (hordωT : letI := functionFieldAlgebra (ι ≫ sX i)
      C.ordForm (show RationalPluriForms (ι ≫ sX i) 2 1 from formPow
        (exteriorPower.ιMulti T.functionField 2 fun b : Fin 2 =>
          ((ι.stalkMap (genericPoint T)).hom (e' b))⁻¹ •
            KaehlerDifferential.D k T.functionField ((ι.stalkMap (genericPoint T)).hom (e' b)))
        1) = -1)
    (hωT0 : letI := functionFieldAlgebra (ι ≫ sX i)
      exteriorPower.ιMulti T.functionField 2 (fun b : Fin 2 =>
        ((ι.stalkMap (genericPoint T)).hom (e' b))⁻¹ •
          KaehlerDifferential.D k T.functionField ((ι.stalkMap (genericPoint T)).hom (e' b)))
        ≠ 0) :
    (ι.stalkMap (genericPoint T)).hom gPj = (ι.stalkMap (genericPoint T)).hom gP' := by
  classical
  have hPi := R.setting.isPair i
  have hPj := R.setting.isPair j
  have hX := hPi.isPair.1
  have hXj := hPj.isPair.1
  haveI := hX.1
  haveI := hXj.1
  have hni := R.setting.topologicalKrullDim_eq i
  have hnj := R.setting.topologicalKrullDim_eq j
  letI := functionFieldAlgebra (sX i)
  letI := functionFieldAlgebra (sX j)
  letI := functionFieldAlgebra (ι ≫ sX i)
  letI := functionFieldAlgebra (ιZ ≫ sX j)
  have hιs : IsAdjunctionStep (sX i) (B i) ι BT := hι
  have hTnv : IsNormalVariety k (ι ≫ sX i) := hιs.1
  have hdT : topologicalKrullDim T = (2 : ℕ) :=
    topologicalKrullDim_eq_of_range_eq_support (sX i) ι P hrange hni
  have hres_m := isPoincareResidue_formPow_dlog (sX i) ι m t e' he' ht
  obtain ⟨K, hK, hmK⟩ := exists_canonical_cartier R i
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast R.setting.pos.ne'
  have hlam1 : ∀ c : TZ.functionField, c ≠ 0 → ν₀ (lam c) = 1 := hν₀k
  have hlamle : ∀ c : TZ.functionField, C.divisorialValuation (lam c) ≤ 1 := by
    intro c
    rw [← hν₀C]
    by_cases hc : c = 0
    · rw [hc, map_zero, map_zero]; exact zero_le'
    · exact (hlam1 c hc).le
  haveI := C.isDiscreteValuationRing_localRing
  have hinj : Function.Injective (algebraMap (T.presheaf.stalk y₀) T.functionField) :=
    IsFractionRing.injective _ _
  refine (stalkMapExc_exists_ringHom_lift lam (algebraMap (T.presheaf.stalk y₀) T.functionField)
    hinj fun c => exists_algebraMap_eq_of_divisorialValuation_le_one C hCη.symm
      (hlamle c)).elim fun μ'' hμ'' => ?_
  have hebC : C.divisorialValuation eb = WithZero.exp (-1) := by rw [← hν₀C]; exact hν₀e
  have hvZ0 : resZ v ≠ 0 := (hvu.map resZ).ne_zero
  have hkerC : ∀ (y : T) (hy : y = C.genericPoint), IdealSheafData.stalk C.idealSheaf y =
      IsLocalRing.maximalIdeal (T.presheaf.stalk y) := by
    rintro y rfl; exact MMP.Resolution.Aux.stalk_idealSheaf_genericPoint C
  set ωT : ⋀[T.functionField]^2 Ω[T.functionField⁄k] := exteriorPower.ιMulti T.functionField 2
    (fun b : Fin 2 => ((ι.stalkMap (genericPoint T)).hom (e' b))⁻¹ •
      KaehlerDifferential.D k T.functionField ((ι.stalkMap (genericPoint T)).hom (e' b)))
    with hωT
  -- the adjunction step onto `C`
  have hdltT := isDltPair_of_isAdjunctionStep (R.setting.isDltPair i) h hι P hP1.ge hrange
  obtain ⟨TC, jC, BC, hpairT, hCstep, hTCi, hrC, hdC⟩ :=
    exists_isAdjunctionStep_of_isDltPair hTnv hdltT (e := 1) hdT C hBC
  have hCstep' : IsAdjunctionStep (ι ≫ sX i) BT jC BC := by
    have := hCstep; rwa [Category.id_comp] at this
  have hCstep'' : IsAdjunctionStep ((ι ≫ 𝟙 (X i)) ≫ sX i) BT jC BC := by
    rw [Category.comp_id]; exact hCstep'
  have hTCnv : IsNormalVariety k (jC ≫ ι ≫ sX i) := hCstep'.1
  haveI : IsNormal TC := hTCnv.2
  haveI : LocallyOfFiniteType (jC ≫ ι ≫ sX i) := hTCnv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian TC := LocallyOfFiniteType.isLocallyNoetherian (jC ≫ ι ≫ sX i)
  obtain ⟨-, -, -, -, hciC, -⟩ := id hCstep'
  haveI := hciC
  have hjCη : jC (genericPoint TC) = C.genericPoint := map_genericPoint_eq_of_range_eq jC C hrC
  haveI := hTCi
  -- lifts to the local ring of `T` along `C`
  obtain ⟨μ3, hμ3, hμ3s⟩ : ∃ μ3 : TZ.functionField →+* T.presheaf.stalk (jC (genericPoint TC)),
      (∀ c, algebraMap _ T.functionField (μ3 c) = lam c) ∧
      ∀ a : T.presheaf.stalk (jC (genericPoint TC)), ∃ c,
        μ3 c - a ∈ IsLocalRing.maximalIdeal (T.presheaf.stalk (jC (genericPoint TC))) := by
    have hy : jC (genericPoint TC) = y₀ := hjCη.trans hCη
    generalize jC (genericPoint TC) = y at hy ⊢
    subst hy
    refine ⟨μ'', hμ'', fun a => ?_⟩
    obtain ⟨c, hc⟩ := hν₀res _ (hy₀le a)
    refine ⟨c, ?_⟩
    rw [mem_maximalIdeal_iff_divisorialValuation_lt_one C hCη.symm, ← hν₀C, map_sub, hμ'',
      ← Valuation.map_neg, neg_sub]
    exact hc
  have hkerjC : ∀ a, (jC.stalkMap (genericPoint TC)).hom a = 0 ↔
      a ∈ IsLocalRing.maximalIdeal (T.presheaf.stalk (jC (genericPoint TC))) := by
    intro a
    rw [← RingHom.mem_ker, ker_stalkMap_eq_stalk_idealSheaf jC C hrC (genericPoint TC),
      hkerC _ hjCη]
  -- the field isomorphism `φ : k(Z) ≅ k(C)`
  obtain ⟨φ0, hφ0⟩ : ∃ φ0 : TZ.functionField →+* TC.functionField,
      φ0 = (jC.stalkMap (genericPoint TC)).hom.comp μ3 := ⟨_, rfl⟩
  have hφ0a : ∀ c, φ0 c = (jC.stalkMap (genericPoint TC)).hom (μ3 c) := fun _ => by rw [hφ0]; rfl
  have hφ0s : Function.Surjective φ0 := by
    intro b
    obtain ⟨a, rfl⟩ := jC.stalkMap_surjective (genericPoint TC) b
    obtain ⟨c, hc⟩ := hμ3s a
    refine ⟨c, ?_⟩
    rw [hφ0a, ← sub_eq_zero, ← map_sub]
    exact (hkerjC _).2 hc
  have hφ0b : Function.Bijective φ0 := ⟨φ0.injective, hφ0s⟩
  have hsC : jC ≫ ι ≫ sX i = (jC ≫ ι ≫ 𝟙 (X i)) ≫ sX i := by simp
  have halgEq : ∀ (s₁ s₂ : TC ⟶ Spec (.of k)), s₁ = s₂ → ∀ c : k,
      (letI := functionFieldAlgebra s₁; algebraMap k TC.functionField c) =
        (letI := functionFieldAlgebra s₂; algebraMap k TC.functionField c) := by
    rintro s₁ s₂ rfl c; rfl
  have hφ0k : ∀ c : k, φ0 (algebraMap k TZ.functionField c) =
      (letI := functionFieldAlgebra ((jC ≫ ι ≫ 𝟙 (X i)) ≫ sX i);
        algebraMap k TC.functionField c) := by
    intro c
    have h1 : μ3 (algebraMap k TZ.functionField c) =
        (letI := stalkAlgebra (ι ≫ sX i) (jC (genericPoint TC)); algebraMap k _ c) := by
      letI := stalkAlgebra (ι ≫ sX i) (jC (genericPoint TC))
      haveI := isScalarTower_stalk_functionField (ι ≫ sX i) (jC (genericPoint TC))
      apply IsFractionRing.injective (T.presheaf.stalk (jC (genericPoint TC))) T.functionField
      rw [hμ3, hlamk, ← IsScalarTower.algebraMap_apply]
    rw [hφ0a, h1, stalkMap_algebraMap_const (ι ≫ sX i) jC (genericPoint TC) c]
    exact halgEq _ _ hsC c
  obtain ⟨φ, hφdef⟩ : ∃ φ : FunctionFieldEquiv ((jC ≫ ι ≫ 𝟙 (X i)) ≫ sX i) (ιZ ≫ sX j),
      ∀ c, φ c = φ0 c := by
    letI := functionFieldAlgebra ((jC ≫ ι ≫ 𝟙 (X i)) ≫ sX i)
    exact ⟨AlgEquiv.ofBijective { φ0 with commutes' := hφ0k } hφ0b, fun _ => rfl⟩
  haveI := FZ.isNormal_stratum
  haveI := FZ.isLocallyNoetherian_stratum
  -- the residue along `C` of `g θ^m`
  obtain ⟨tC, htC⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one C hjCη
    (f := eb) (by rw [hebC, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have heb0 : eb ≠ 0 := by
    intro h0; rw [h0, map_zero] at hebC; exact WithZero.exp_ne_zero hebC.symm
  have htC1 : T.ord (algebraMap _ T.functionField tC) (jC (genericPoint TC)) = 1 := by
    have h2 := C.divisorialValuation_eq_exp_neg_ord heb0
    rw [hebC] at h2
    rw [htC, hjCη]
    have := WithZero.exp_injective h2
    omega
  have hvC3u : IsUnit (μ3 (resZ v)) := by
    by_contra hnu
    have h1 := (mem_maximalIdeal_iff_divisorialValuation_lt_one C hjCη _).1
      ((IsLocalRing.mem_maximalIdeal _).2 hnu)
    rw [hμ3, ← hν₀C, hlam1 _ hvZ0] at h1
    exact lt_irrefl _ h1
  have hres2 := isPoincareResidue_formPow_dlog (ι ≫ sX i) jC (n := 1) m tC ![μ3 (resZ v)]
    (fun a => by fin_cases a; exact hvC3u) htC1
  have hframe : (Fin.cons ((algebraMap _ T.functionField tC)⁻¹ •
      KaehlerDifferential.D k T.functionField (algebraMap _ _ tC))
      fun a => (algebraMap _ T.functionField (![μ3 (resZ v)] a))⁻¹ •
        KaehlerDifferential.D k T.functionField (algebraMap _ _ (![μ3 (resZ v)] a)) :
        Fin (1 + 1) → Ω[T.functionField⁄k]) =
      fun b : Fin 2 => ((ι.stalkMap (genericPoint T)).hom (e' b))⁻¹ •
        KaehlerDifferential.D k T.functionField ((ι.stalkMap (genericPoint T)).hom (e' b)) := by
    have h1 : algebraMap _ T.functionField (μ3 (resZ v)) =
        (ι.stalkMap (genericPoint T)).hom (e' 1) := by
      rw [hμ3, hlamv]
    funext b; fin_cases b
    · show (algebraMap _ T.functionField tC)⁻¹ •
        KaehlerDifferential.D k T.functionField (algebraMap _ T.functionField tC) = _
      rw [htC, heb]; rfl
    · show (algebraMap _ T.functionField (μ3 (resZ v)))⁻¹ •
        KaehlerDifferential.D k T.functionField (algebraMap _ T.functionField (μ3 (resZ v))) = _
      rw [h1]; rfl
  rw [hframe] at hres2
  haveI : LocallyOfFiniteType ((jC ≫ ι ≫ 𝟙 (X i)) ≫ sX i) := by
    rw [← hsC]; infer_instance
  have hrecC : ∀ (ω : logPluricanonicalSections (sX i) 3 m (B i))
      (g : (X i).presheaf.stalk (ι (genericPoint T))) (c : TZ.functionField),
      (ω : RationalPluriForms (sX i) 3 m) = algebraMap _ (X i).functionField g •
        formPow (exteriorPower.ιMulti (X i).functionField (2 + 1)
          (Fin.cons ((algebraMap _ (X i).functionField t)⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ (X i).functionField t))
            fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
              KaehlerDifferential.D k _ (algebraMap _ (X i).functionField (e' b)))) m →
      (ι.stalkMap (genericPoint T)).hom g = lam c →
      R.toFun i (.step (.step (.refl h) ι BT hι) jC BC hCstep'') 1 ω =
        (letI := functionFieldAlgebra ((jC ≫ ι ≫ 𝟙 (X i)) ≫ sX i);
          φ0 c • (show RationalPluriForms ((jC ≫ ι ≫ 𝟙 (X i)) ≫ sX i) 1 m from
            formPow (exteriorPower.ιMulti TC.functionField 1 fun _ =>
              (φ0 (resZ v))⁻¹ • KaehlerDifferential.D k TC.functionField (φ0 (resZ v))) m)) := by
    intro ω g c hω hgc
    have r1 : IsPoincareResidue (sX i) ι (1 + 1) m (ω : RationalPluriForms (sX i) (1 + 2) m)
        ((ι.stalkMap (genericPoint T)).hom g • formPow ωT m) := by
      rw [hω]; exact IsPoincareResidue.smul_stalk hres_m g
    have r2 := IsPoincareResidue.smul_stalk hres2 (μ3 c)
    rw [hμ3, ← hgc] at r2
    have hrec := isIteratedResidueRec_step_step h hι hCstep'' (e := 1) r1 r2
      (letI := functionFieldAlgebra ((jC ≫ ι ≫ 𝟙 (X i)) ≫ sX i);
          φ0 c • (show RationalPluriForms ((jC ≫ ι ≫ 𝟙 (X i)) ≫ sX i) 1 m from
            formPow (exteriorPower.ιMulti TC.functionField 1 fun _ =>
              (φ0 (resZ v))⁻¹ • KaehlerDifferential.D k TC.functionField (φ0 (resZ v))) m))
      (by
        rw [hφ0a]
        exact (heq_smul_formPow_ιMulti_dlog_of_eq hsC _ _ _
          (fun a => by fin_cases a; rw [hφ0a]; rfl) m).symm)
    exact IsIteratedResidueRec.unique _ (R.isIteratedResidue i _ 1 ω hdC).rec' hrec
  -- crepancy of `φ`
  obtain ⟨K', hK', hmK'⟩ := exists_canonical_cartier R j
  haveI := FZ.isClosedImmersion
  haveI : CompactSpace TZ := QuasiCompact.compactSpace_of_compactSpace ιZ
  haveI : CompactSpace TC := QuasiCompact.compactSpace_of_compactSpace jC
  -- the forms
  have hpull1 : pluriformPullback (sX i) (sX j) σ.toHom 3 1
      (show RationalPluriForms (sX j) 3 ((1 : ℕ) : ℤ) from formPow (exteriorPower.ιMulti
        (X j).functionField 3 fun a =>
          (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
            (![z 0, z 1, v] a))⁻¹ • KaehlerDifferential.D k (X j).functionField
              (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
                (![z 0, z 1, v] a))) 1) =
      formPow (exteriorPower.ιMulti (X i).functionField (2 + 1)
        (Fin.cons ((algebraMap _ (X i).functionField t)⁻¹ •
          KaehlerDifferential.D k _ (algebraMap _ (X i).functionField t))
          fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ (X i).functionField (e' b)))) 1 := by
    have h1 := pluriformPullback_smul_formPow_dlog hni hnj σ.toHom
      (fun a => algebraMap _ (X j).functionField (![z 0, z 1, v] a)) 1 1
    rw [one_smul, map_one, one_smul, hfr] at h1
    exact h1
  have hres1 := isPoincareResidue_formPow_dlog (sX i) ι 1 t e' he' ht
  have hρres : IsPoincareResidue (sX i) ι 2 1 (pluriformPullback (sX i) (sX j) σ.toHom 3 1
      (show RationalPluriForms (sX j) 3 ((1 : ℕ) : ℤ) from formPow (exteriorPower.ιMulti
        (X j).functionField 3 fun a =>
          (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
            (![z 0, z 1, v] a))⁻¹ • KaehlerDifferential.D k (X j).functionField
              (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
                (![z 0, z 1, v] a))) 1))
      (show RationalPluriForms (ι ≫ sX i) 2 1 from formPow ωT 1) := by
    rw [hpull1]; exact hres1
  have hωT10 : (show RationalPluriForms (ι ≫ sX i) 2 1 from formPow ωT 1) ≠ 0 := by
    have := smul_formPow_ne_zero hdT hωT0 one_ne_zero 1
    rwa [one_smul] at this
  have hτ'0 : (show RationalPluriForms (sX j) 3 ((1 : ℕ) : ℤ) from formPow (exteriorPower.ιMulti
        (X j).functionField 3 fun a =>
          (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
            (![z 0, z 1, v] a))⁻¹ • KaehlerDifferential.D k (X j).functionField
              (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
                (![z 0, z 1, v] a))) 1) ≠ 0 := by
    intro h0
    have h1 := hρres
    rw [h0, map_zero] at h1
    exact hωT10 (IsPoincareResidue.unique hιs (isPoincareResidue_zero hιs) h1).symm
  have hres21 := isPoincareResidue_formPow_dlog (ι ≫ sX i) jC (n := 1) 1 tC ![μ3 (resZ v)]
    (fun a => by fin_cases a; exact hvC3u) htC1
  rw [hframe] at hres21
  -- `θ_Z ≠ 0`
  have hθZ0 : (show RationalPluriForms (ιZ ≫ sX j) 1 ((1 : ℕ) : ℤ) from
      formPow (exteriorPower.ιMulti TZ.functionField 1
        fun _ => (resZ v)⁻¹ • KaehlerDifferential.D k TZ.functionField (resZ v)) 1) ≠ 0 :=
    stalkMapExc_formPow_dlog_ne_zero hdimZ hwZ' 1
  have hφ : IsCrepantBirationalMap ((jC ≫ ι ≫ 𝟙 (X i)) ≫ sX i) (ιZ ≫ sX j) BC BZ φ :=
    isCrepantBirationalMap_of_residue_curve hX hXj hni hnj hK hK' ⟨_, hm0, hmK⟩ ⟨_, hm0, hmK'⟩
      σ hσ hιs P hrange hP1 D hDv hτ'0 U hxU hU hρres hCstep' C hrC hordωT hres21 FZ.isNormalVariety
      hdimZ hgenZ hθZ0 hpbZ lam ψ hψ hlamψ
      (fun c hc => by rw [← hν₀C]; exact hlam1 c hc) μ3 hμ3 hsC φ
      (fun c => by rw [hφdef, hφ0a])
      (by
        have h1 := pluriformPullback_smul_formPow_dlog hdC hdimZ φ.toHom (fun _ => resZ v) 1 1
        rw [one_smul, map_one, one_smul] at h1
        exact (heq_formPow_ιMulti_dlog_of_eq hsC _ (fun _ => φ (resZ v))
          (fun a => by fin_cases a; rw [hφdef, hφ0a]; rfl) 1).trans (heq_of_eq h1.symm))
  -- the residue of `s_j` along the flag to `Z`
  have hRsj : R.toFun j FZ 1 (s j) = resZ gj • (formPow (exteriorPower.ιMulti
      TZ.functionField 1 fun _ => (resZ v)⁻¹ • KaehlerDifferential.D k TZ.functionField
        (resZ v)) m : RationalPluriForms (ιZ ≫ sX j) 1 m) := by
    have h2 : IsIteratedResidueRec (s j : RationalPluriForms (sX j) 3 m) FZ 1
        (resZ gj • (formPow (exteriorPower.ιMulti TZ.functionField 1
            fun _ => (resZ v)⁻¹ • KaehlerDifferential.D k TZ.functionField (resZ v)) m :
            RationalPluriForms (ιZ ≫ sX j) 1 m)) := by
      rw [hgj]; exact hrecZ gj m
    exact IsIteratedResidueRec.unique FZ (R.isIteratedResidue j FZ 1 (s j) hdimZ).rec' h2
  have hRsi := hrecC (s i) gP' (resZ g') hsi2 hgP'l
  have hFlen : 1 ≤ (StratumAdjunctionData.step (.step (.refl h) ι BT hι) jC BC
      hCstep'').length :=
    Nat.le_add_left 1 _
  -- preadmissibility along `φ`
  have hpre := hs i j (.step (.step (.refl h) ι BT hι) jC BC hCstep'') FZ 1 hFlen
    (by rw [hlenZ]; exact one_le_two) hdC hdimZ φ hφ
  rw [hRsj, hRsi, pluriformPullback_smul_formPow_dlog hdC hdimZ φ.toHom (fun _ => resZ v) m
    (resZ gj)] at hpre
  have hφh : ∀ c, (FunctionFieldEquiv.toHom _ _ φ) c = φ0 c := fun c => hφdef c
  simp only [hφh] at hpre
  letI := functionFieldAlgebra ((jC ≫ ι ≫ 𝟙 (X i)) ≫ sX i)
  have hW : (show RationalPluriForms ((jC ≫ ι ≫ 𝟙 (X i)) ≫ sX i) 1 m from
      formPow (exteriorPower.ιMulti TC.functionField 1 fun _ =>
        (φ0 (resZ v))⁻¹ • KaehlerDifferential.D k TC.functionField (φ0 (resZ v))) m) ≠ 0 := by
    have hspan := span_D_eq_top_of_surjective φ.toAlgHom
      (fun b => by obtain ⟨c, hc⟩ := hφ0s b; exact ⟨c, by rw [← hc]; exact hφdef c⟩)
      (fun _ : Fin 1 => resZ v) (by rw [Set.range_const]; exact hwZ')
    rw [Set.range_const] at hspan
    have hspan' : Submodule.span TC.functionField
        {KaehlerDifferential.D k TC.functionField (φ0 (resZ v))} = ⊤ := by
      rw [← hspan, ← hφdef]; rfl
    exact stalkMapExc_formPow_dlog_ne_zero hdC hspan' m
  have hφeq : φ0 (resZ gj) = φ0 (resZ g') := by
    by_contra hne
    have h0 : (φ0 (resZ gj) - φ0 (resZ g')) •
        (show RationalPluriForms ((jC ≫ ι ≫ 𝟙 (X i)) ≫ sX i) 1 m from
          formPow (exteriorPower.ιMulti TC.functionField 1 fun _ =>
            (φ0 (resZ v))⁻¹ • KaehlerDifferential.D k TC.functionField (φ0 (resZ v))) m) = 0 := by
      rw [sub_smul]; exact sub_eq_zero.2 hpre
    rcases smul_eq_zero.1 h0 with h1 | h1
    · exact hne (sub_eq_zero.1 h1)
    · exact hW h1
  rw [hgPjl, hgP'l, φ0.injective hφeq]

/-- The point case of `stalkMap_eq_of_isExceptional_of_curve`: when the centre `y₀` of `ν₀` is a
closed point of `T`, it is a zero-dimensional stratum with snc coordinates, and comparing the
point residues of `s_i` and `s_j` there gives the equality of the restricted coefficients. -/
private theorem stalkMapExc_eq_of_point_centre
    (R : ResidueRestriction sX B 3 m) {i j : I} [CharZero k] [IsAlgClosed k]
    [CompactSpace (X i)] [IsProper (sX i)] [IsProper (sX j)]
    {s : ∀ l, logPluricanonicalSections (sX l) 3 m (B l)} (hs : s ∈ preadmissibleSections R)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (P : Mori.PrimeDivisor (X i))
    [IsNormal T] [IsLocallyNoetherian T] [LocallyOfFiniteType (ι ≫ sX i)] [IsClosedImmersion ι]
    [CompactSpace T]
    (hP1 : (B i).coeff P = 1)
    (hrange : Set.range ι.base = (P.support : Set (X i))) (D : DivisorOver k (sX j))
    (z : Fin 2 → (X j).presheaf.stalk (D.f D.E.genericPoint))
    (v : (X j).presheaf.stalk (D.f D.E.genericPoint))
    [CompactSpace (X j)]
    (t : (X i).presheaf.stalk (ι (genericPoint T)))
    (e' : Fin 2 → (X i).presheaf.stalk (ι (genericPoint T))) (he' : ∀ b, IsUnit (e' b))
    (ht : (X i).ord (algebraMap _ (X i).functionField t) (ι (genericPoint T)) = 1)
    (gj g' : (X j).presheaf.stalk (D.f D.E.genericPoint))
    (hgj : letI := functionFieldAlgebra (sX j)
      (s j : RationalPluriForms (sX j) 3 m) = algebraMap _ (X j).functionField gj •
        (show RationalPluriForms (sX j) 3 m from formPow (exteriorPower.ιMulti (X j).functionField 3
          fun a => (algebraMap _ (X j).functionField (![z 0, z 1, v] a))⁻¹ •
            KaehlerDifferential.D k (X j).functionField
              (algebraMap _ (X j).functionField (![z 0, z 1, v] a))) m))
    (u' : logPluricanonicalSections (sX j) 3 m (B j))
    (hg' : letI := functionFieldAlgebra (sX j)
      (u' : RationalPluriForms (sX j) 3 m) = algebraMap _ (X j).functionField g' •
        (show RationalPluriForms (sX j) 3 m from formPow (exteriorPower.ιMulti (X j).functionField 3
          fun a => (algebraMap _ (X j).functionField (![z 0, z 1, v] a))⁻¹ •
            KaehlerDifferential.D k (X j).functionField
              (algebraMap _ (X j).functionField (![z 0, z 1, v] a))) m))
    (u : logPluricanonicalSections (sX i) 3 m (B i))
    (gPj gP' : (X i).presheaf.stalk (ι (genericPoint T)))
    (hu2 : letI := functionFieldAlgebra (sX i)
      (u : RationalPluriForms (sX i) 3 m) = algebraMap _ (X i).functionField gPj •
        formPow (exteriorPower.ιMulti (X i).functionField (2 + 1)
          (Fin.cons ((algebraMap _ (X i).functionField t)⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ (X i).functionField t))
            fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
              KaehlerDifferential.D k _ (algebraMap _ (X i).functionField (e' b)))) m)
    (hsi2 : letI := functionFieldAlgebra (sX i)
      (s i : RationalPluriForms (sX i) 3 m) = algebraMap _ (X i).functionField gP' •
        formPow (exteriorPower.ιMulti (X i).functionField (2 + 1)
          (Fin.cons ((algebraMap _ (X i).functionField t)⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ (X i).functionField t))
            fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
              KaehlerDifferential.D k _ (algebraMap _ (X i).functionField (e' b)))) m)
    {TZ : Scheme.{0}} {ιZ : TZ ⟶ X j} [IsIntegral TZ] [IsNormal TZ] [IsLocallyNoetherian TZ]
    [LocallyOfFiniteType (ιZ ≫ sX j)] [IsClosedImmersion ιZ] [CompactSpace TZ]
    (resZ : (X j).presheaf.stalk (D.f D.E.genericPoint) →+* TZ.functionField)
    {BZ : QDivisor TZ} (FZ : StratumAdjunctionData (sX j) (B j) ιZ BZ)
    (hdimZ : topologicalKrullDim TZ = (1 : ℕ))
    (hrecZ : letI := functionFieldAlgebra (sX j); letI := functionFieldAlgebra (ιZ ≫ sX j)
      ∀ (g : (X j).presheaf.stalk (D.f D.E.genericPoint)) (m : ℕ), IsIteratedResidueRec
        (show RationalPluriForms (sX j) 3 m from algebraMap _ (X j).functionField g •
          formPow (exteriorPower.ιMulti (X j).functionField 3 fun a =>
            (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
              (![z 0, z 1, v] a))⁻¹ • KaehlerDifferential.D k (X j).functionField
                (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
                  (![z 0, z 1, v] a))) m)
        FZ 1 (resZ g • (show RationalPluriForms (ιZ ≫ sX j) 1 m from
          formPow (exteriorPower.ιMulti TZ.functionField 1
            fun _ => (resZ v)⁻¹ • KaehlerDifferential.D k TZ.functionField (resZ v)) m)))
    (hdltZ : MMP.Intersection.IsDltPair (ιZ ≫ sX j) BZ)
    (hLRZ : ∀ m : ℕ, 0 < m → ∀ K : Divisor (X j), K.IsCanonicalDivisor (sX j) 3 →
      ((m : ℤ) • (Divisor.toQDivisor K + B j)).IsCartierDivisor →
      (∀ {S : Scheme.{0}} {ιS : S ⟶ X j} {BS : QDivisor S}
        (F' : StratumAdjunctionData (sX j) (B j) ιS BS),
        haveI := F'.isIntegral_stratum
        haveI := F'.isNormal_stratum
        haveI := F'.isLocallyNoetherian_stratum
        ∃ (d : ℕ) (KS : Divisor S), KS.IsCanonicalDivisor (ιS ≫ sX j) d ∧
          ((m : ℤ) • (Divisor.toQDivisor KS + BS)).IsCartierDivisor) →
      letI := functionFieldAlgebra (sX j); letI := functionFieldAlgebra (ιZ ≫ sX j)
      ∀ ω : RationalPluriForms (sX j) 3 m, ω ∈ logPluricanonicalSections (sX j) 3 m (B j) →
      ∀ g : (X j).presheaf.stalk (D.f D.E.genericPoint), ω = algebraMap _ (X j).functionField g •
        (show RationalPluriForms (sX j) 3 m from formPow (exteriorPower.ιMulti (X j).functionField 3
          fun a => (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
            (![z 0, z 1, v] a))⁻¹ • KaehlerDifferential.D k (X j).functionField
              (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
                (![z 0, z 1, v] a))) m) →
      (show RationalPluriForms (ιZ ≫ sX j) 1 m from resZ g •
        formPow (exteriorPower.ιMulti TZ.functionField 1
          fun _ => (resZ v)⁻¹ • KaehlerDifferential.D k TZ.functionField (resZ v)) m) ∈
        logPluricanonicalSections (ιZ ≫ sX j) 1 m BZ)
    (hwZ' : letI := functionFieldAlgebra (ιZ ≫ sX j)
      Submodule.span TZ.functionField {KaehlerDifferential.D k TZ.functionField (resZ v)} = ⊤)
    (lam : TZ.functionField →+* T.functionField)
    (hlamk : letI := functionFieldAlgebra (ι ≫ sX i); letI := functionFieldAlgebra (ιZ ≫ sX j)
      ∀ c : k, lam (algebraMap k _ c) = algebraMap k _ c)
    (hlamv : lam (resZ v) = (ι.stalkMap (genericPoint T)).hom (e' 1))
    (hgPjl : (ι.stalkMap (genericPoint T)).hom gPj = lam (resZ gj))
    (hgP'l : (ι.stalkMap (genericPoint T)).hom gP' = lam (resZ g'))
    (hzero : ¬((ι.stalkMap (genericPoint T)).hom gPj = 0 ∧
      (ι.stalkMap (genericPoint T)).hom gP' = 0))
    (ν₀ : Valuation T.functionField ℤᵐ⁰) (hν₀k : ∀ c, c ≠ 0 → ν₀ (lam c) = 1)
    (eb : T.functionField) (heb : eb = (ι.stalkMap (genericPoint T)).hom (e' 0))
    (hν₀e : ν₀ eb = WithZero.exp (-1)) (hν₀res : ∀ f, ν₀ f ≤ 1 → ∃ c, ν₀ (f - lam c) < 1)
    (y₀ : T) (hy₀le : ∀ a : T.presheaf.stalk y₀, ν₀ (algebraMap _ T.functionField a) ≤ 1)
    (hy₀lt : ∀ a ∈ IsLocalRing.maximalIdeal (T.presheaf.stalk y₀),
      ν₀ (algebraMap _ T.functionField a) < 1)
    (hSν : letI := functionFieldAlgebra (ι ≫ sX i)
      ∃ (S : Type) (_ : CommRing S) (_ : Algebra k S) (_ : Algebra.EssFiniteType k S)
        (φ : S →ₐ[k] T.functionField), ∀ g, ν₀ g ≤ 1 ↔ g ∈ φ.range)
    (hc2 : Order.coheight y₀ = 2) :
    (ι.stalkMap (genericPoint T)).hom gPj = (ι.stalkMap (genericPoint T)).hom gP' := by
  classical
  have hPi := R.setting.isPair i
  have hX := hPi.isPair.1
  haveI := hX.1
  have hni := R.setting.topologicalKrullDim_eq i
  letI := functionFieldAlgebra (sX i)
  letI := functionFieldAlgebra (sX j)
  letI := functionFieldAlgebra (ι ≫ sX i)
  letI := functionFieldAlgebra (ιZ ≫ sX j)
  have hιs : IsAdjunctionStep (sX i) (B i) ι BT := hι
  have hTnv : IsNormalVariety k (ι ≫ sX i) := hιs.1
  have hdT : topologicalKrullDim T = (2 : ℕ) :=
    topologicalKrullDim_eq_of_range_eq_support (sX i) ι P hrange hni
  haveI : IsProper (ι ≫ sX i) := inferInstance
  have hcl : IsClosed ({y₀} : Set T) :=
    isClosed_singleton_of_le_coheight (d := 2) hdT.le (by rw [hc2]; rfl)
  obtain ⟨K, hK, hmK⟩ := exists_canonical_cartier R i
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast R.setting.pos.ne'
  have hres_m := isPoincareResidue_formPow_dlog (sX i) ι m t e' he' ht
  have hωfun : (fun b : Fin 2 => ((ι.stalkMap (genericPoint T)).hom (e' b))⁻¹ •
      KaehlerDifferential.D k T.functionField ((ι.stalkMap (genericPoint T)).hom (e' b))) =
      ![eb⁻¹ • KaehlerDifferential.D k _ eb,
        (lam (resZ v))⁻¹ • KaehlerDifferential.D k _ (lam (resZ v))] := by
    funext b; fin_cases b
    · show ((ι.stalkMap (genericPoint T)).hom (e' 0))⁻¹ • KaehlerDifferential.D k
        T.functionField ((ι.stalkMap (genericPoint T)).hom (e' 0)) =
        eb⁻¹ • KaehlerDifferential.D k _ eb
      rw [heb]
    · show ((ι.stalkMap (genericPoint T)).hom (e' 1))⁻¹ • KaehlerDifferential.D k
        T.functionField ((ι.stalkMap (genericPoint T)).hom (e' 1)) =
        (lam (resZ v))⁻¹ • KaehlerDifferential.D k _ (lam (resZ v))
      rw [hlamv]
  have hlogres : ∀ (ω : logPluricanonicalSections (sX i) 3 m (B i))
      (g : (X i).presheaf.stalk (ι (genericPoint T))) (c : TZ.functionField),
      (ω : RationalPluriForms (sX i) 3 m) = algebraMap _ (X i).functionField g •
        formPow (exteriorPower.ιMulti (X i).functionField (2 + 1)
          (Fin.cons ((algebraMap _ (X i).functionField t)⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ (X i).functionField t))
            fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
              KaehlerDifferential.D k _ (algebraMap _ (X i).functionField (e' b)))) m →
      (ι.stalkMap (genericPoint T)).hom g = lam c →
      ∃ ρ : RationalPluriForms (ι ≫ sX i) 2 m, IsPoincareResidue (sX i) ι 2 m ω ρ ∧
        ρ ∈ logPluricanonicalSections (ι ≫ sX i) 2 m BT ∧
        ρ = lam c • formPow (exteriorPower.ιMulti T.functionField 2
          ![eb⁻¹ • KaehlerDifferential.D k _ eb,
            (lam (resZ v))⁻¹ • KaehlerDifferential.D k _ (lam (resZ v))]) m := by
    intro ω g c hω hgc
    obtain ⟨ρω, hρω, hρωlog⟩ := exists_isPoincareResidue_mem_logPluricanonicalSections hX
      (d := 2) (by rw [hni]) (R.setting.isDltPair i).2.1 hK ⟨_, hm0, hmK⟩ hιs
      (by norm_num) R.setting.pos ω.2
    have hr : IsPoincareResidue (sX i) ι 2 m (ω : RationalPluriForms (sX i) 3 m)
        ((ι.stalkMap (genericPoint T)).hom g • formPow (exteriorPower.ιMulti T.functionField 2
          fun b => ((ι.stalkMap (genericPoint T)).hom (e' b))⁻¹ •
            KaehlerDifferential.D k T.functionField
              ((ι.stalkMap (genericPoint T)).hom (e' b))) m) := by
      rw [hω]; exact IsPoincareResidue.smul_stalk hres_m g
    refine ⟨ρω, hρω, hρωlog, ?_⟩
    rw [IsPoincareResidue.unique hιs hρω hr, hgc, hωfun]
  obtain ⟨ρu, -, hρu, hρue⟩ := hlogres u gPj (resZ gj) hu2 hgPjl
  obtain ⟨ρs, hρs_res, hρs, hρse⟩ := hlogres (s i) gP' (resZ g') hsi2 hgP'l
  -- the adjunction data of `T`
  obtain ⟨d₁, KT, hKT, hKTc⟩ := R.setting.isCartierDivisor i (.step (.refl h) ι BT hι)
  have hKT' : KT.IsCanonicalDivisor (ι ≫ sX i) d₁ := by simpa using hKT
  have hd₁ : d₁ = 2 := by
    have := hKT'.topologicalKrullDim_eq
    rw [hdT] at this
    exact_mod_cast this.symm
  subst hd₁
  have hdltT := isDltPair_of_isAdjunctionStep (R.setting.isDltPair i) h hι P hP1.ge hrange
  -- a section with nonzero coefficient, and the snc structure at `y₀`
  obtain ⟨c₁, ρ₁, hρ₁, hρ₁e, hc₁⟩ : ∃ (c₁ : TZ.functionField)
      (ρ₁ : RationalPluriForms (ι ≫ sX i) 2 m),
      ρ₁ ∈ logPluricanonicalSections (ι ≫ sX i) 2 m BT ∧
      ρ₁ = lam c₁ • formPow (exteriorPower.ιMulti T.functionField 2
        ![eb⁻¹ • KaehlerDifferential.D k _ eb,
          (lam (resZ v))⁻¹ • KaehlerDifferential.D k _ (lam (resZ v))]) m ∧ c₁ ≠ 0 := by
    rcases not_and_or.1 hzero with h0 | h0
    · exact ⟨_, _, hρu, hρue, fun hc => h0 (by rw [hgPjl, hc, map_zero])⟩
    · exact ⟨_, _, hρs, hρse, fun hc => h0 (by rw [hgP'l, hc, map_zero])⟩
  obtain ⟨y, Ly, hy, hsmy, hLy, hLyx, hLyz, hBLy, hL1y, hQy, W, hW, hform⟩ :=
    exists_sncPoint_of_isClosed_center hTnv hdT hdltT hKT' R.setting.pos hKTc
      FZ.isNormalVariety hdimZ lam hlamk ν₀ (fun c hc => hν₀k c hc) eb hν₀e
      (fun f hf => hν₀res f hf) hSν y₀ hy₀le hy₀lt hcl hc2 (resZ v) hwZ' c₁ ρ₁ hρ₁ hρ₁e hc₁
  obtain ⟨hu_h, hρu_h, hu_res⟩ := hform (resZ gj) ρu hρu hρue
  obtain ⟨hs_h, hρs_h, hs_res⟩ := hform (resZ g') ρs hρs hρse
  have hresk := exists_sub_mem_maximalIdeal_of_isClosed (ι ≫ sX i) y₀ hcl
  obtain ⟨au, hau⟩ := hresk hu_h
  obtain ⟨as, has⟩ := hresk hs_h
  have hTu := hu_res au hau
  have hTs := hs_res as has
  -- the point residues agree
  have hθv0 : (formPow (exteriorPower.ιMulti TZ.functionField 1 fun _ =>
      (resZ v)⁻¹ • KaehlerDifferential.D k TZ.functionField (resZ v)) m :
        RationalPluriForms (ιZ ≫ sX j) 1 m) ≠ 0 :=
    stalkMapExc_formPow_dlog_ne_zero hdimZ hwZ' m
  have haus : au = as := by
    by_cases hboth : au = 0 ∧ as = 0
    · rw [hboth.1, hboth.2]
    obtain ⟨K', hK', hmK'⟩ := exists_canonical_cartier R j
    -- `W ≠ 0`
    have hW0 : W ≠ 0 := by
      rintro rfl
      have hz0 : (formPow (exteriorPower.ιMulti TZ.functionField 1 fun _ =>
          (0 : TZ.functionField)⁻¹ • KaehlerDifferential.D k TZ.functionField 0) m :
            RationalPluriForms (ιZ ≫ sX j) 1 m) = 0 := by
        simp only [map_zero, smul_zero]
        rw [show (fun _ : Fin 1 => (0 : Ω[TZ.functionField⁄k])) = 0 from rfl,
          AlternatingMap.map_zero]
        exact formPow_zero_of_pos R.setting.pos
      rw [hz0, smul_zero] at hTu hTs
      rcases smul_eq_zero.1 hTu with h1 | h1
      · rcases smul_eq_zero.1 hTs with h2 | h2
        · exact hzero ⟨by rw [hgPjl, h1, map_zero], by rw [hgP'l, h2, map_zero]⟩
        · exact hθv0 h2
      · exact hθv0 h1
    -- a point stratum `x₀` of `Z`: a zero of `W`
    have hfunW : (fun _ : Fin 1 => W⁻¹ • KaehlerDifferential.D k TZ.functionField W) =
        ![W⁻¹ • KaehlerDifferential.D k TZ.functionField W] := by
      funext i; fin_cases i; rfl
    obtain ⟨c₀, hc₀, hlog⟩ : ∃ c₀ : k, c₀ ≠ 0 ∧ (algebraMap k TZ.functionField c₀ •
        (formPow (exteriorPower.ιMulti TZ.functionField 1
          ![W⁻¹ • KaehlerDifferential.D k _ W]) m : RationalPluriForms (ιZ ≫ sX j) 1 m)) ∈
        logPluricanonicalSections (ιZ ≫ sX j) 1 m BZ := by
      rcases not_and_or.1 hboth with h0 | h0
      · refine ⟨au, h0, ?_⟩
        have := hLRZ m R.setting.pos K' hK' hmK' (R.setting.isCartierDivisor j)
          (s j : RationalPluriForms (sX j) 3 m) (s j).2 gj hgj
        rw [hTu, hfunW] at this
        exact this
      · refine ⟨as, h0, ?_⟩
        have := hLRZ m R.setting.pos K' hK' hmK' (R.setting.isCartierDivisor j)
          (u' : RationalPluriForms (sX j) 3 m) u'.2 g' hg'
        rw [hTs, hfunW] at this
        exact this
    haveI : IsProper (ιZ ≫ sX j) := inferInstance
    obtain ⟨Tq, ιq, Bq, hιq, hTq, hdq, hresq⟩ :=
      exists_isAdjunctionStep_residue_dlog_of_curve_of_mem FZ.isNormalVariety hdimZ hdltZ W hW0
        hW R.setting.pos hc₀ hlog
    -- the point flag on `X_j` through `Z`, and the point residue of `s_j` there
    haveI : AlgebraicGeometry.IsIntegral Tq := hTq
    have hsq : (ιq ≫ ιZ) ≫ sX j = ιq ≫ ιZ ≫ sX j := Category.assoc _ _ _
    letI := functionFieldAlgebra ((ιq ≫ ιZ) ≫ sX j)
    letI := functionFieldAlgebra (ιq ≫ ιZ ≫ sX j)
    have hrecq : IsIteratedResidueRec (s j : RationalPluriForms (sX j) 3 m)
        (StratumAdjunctionData.step FZ ιq Bq hιq) 0
        (au • (show RationalPluriForms ((ιq ≫ ιZ) ≫ sX j) 0 m from
          formPow (exteriorPower.ιMulti Tq.functionField 0 ![]) m)) := by
      have h2 : IsIteratedResidueRec (s j : RationalPluriForms (sX j) 3 m) FZ 1
          (resZ gj • (formPow (exteriorPower.ιMulti TZ.functionField 1
            fun _ => (resZ v)⁻¹ • KaehlerDifferential.D k TZ.functionField (resZ v)) m :
              RationalPluriForms (ιZ ≫ sX j) 1 m)) := by
        rw [hgj]; exact hrecZ gj m
      have hr := IsPoincareResidue.smul_const (hresq m) au
      refine ⟨_, h2, _, ?_, heq_smul_formPow_ιMulti_zero hsq au m⟩
      rw [hTu, hfunW]
      exact hr
    have hdq' : topologicalKrullDim Tq = ((0 : ℕ) : WithBot ℕ∞) := hdq
    have hRsj : R.toFun j (StratumAdjunctionData.step FZ ιq Bq hιq) 0 (s j) =
        au • (show RationalPluriForms ((ιq ≫ ιZ) ≫ sX j) 0 m from
          formPow (exteriorPower.ιMulti Tq.functionField 0 ![]) m) :=
      IsIteratedResidueRec.unique _
        (R.isIteratedResidue j (StratumAdjunctionData.step FZ ιq Bq hιq) 0 (s j) hdq').rec'
        hrecq
    -- the point flag on `X_i` through `T` to `y₀`, and the point residue of `s_i` there
    have hs1 : sX i = 𝟙 (X i) ≫ sX i := (Category.id_comp _).symm
    have hs1' : ι ≫ sX i = ι ≫ 𝟙 (X i) ≫ sX i := by rw [Category.id_comp]
    have hs2 : ι ≫ sX i = (ι ≫ 𝟙 (X i)) ≫ sX i := by simp
    obtain ⟨ρ1, hρ1⟩ := exists_heq_rationalPluriForms hs1' ρs
    obtain ⟨X1, hX1⟩ := exists_heq_rationalPluriForms hs2 ρs
    obtain ⟨ρ0, hρ0⟩ := exists_heq_rationalPluriForms hs1 (s i : RationalPluriForms (sX i) 3 m)
    have hrecs : IsIteratedResidueRec (s i : RationalPluriForms (sX i) 3 m)
        (.step (.refl h) ι BT hι) 2 X1 :=
      ⟨ρ0, ⟨rfl, hρ0.symm⟩, ρ1, IsPoincareResidue.congr_structure hs1 hρs_res hρ0 hρ1,
        hX1.symm.trans hρ1⟩
    obtain ⟨S', ιS', BS', F', hlen', hdim', hrec'⟩ := exists_flag_isIteratedResidueRec_of_sncPoint
      (s i : RationalPluriForms (sX i) 3 m) 2 (.step (.refl h) ι BT hι) (ι ≫ sX i) (by simp)
      hTnv hdltT hdT y₀ hcl y hy hsmy Ly hLy hLyx hLyz hBLy hL1y hQy hs_h as has
      ⟨X1, hrecs, hX1.symm.trans (heq_of_eq hρs_h)⟩
    haveI := F'.isIntegral_stratum
    haveI := F'.isNormal_stratum
    haveI := F'.isLocallyNoetherian_stratum
    letI := functionFieldAlgebra (ιS' ≫ sX i)
    have hRsi : R.toFun i F' 0 (s i) = as • (show RationalPluriForms (ιS' ≫ sX i) 0 m from
        formPow (exteriorPower.ιMulti S'.functionField 0 ![]) m) :=
      IsIteratedResidueRec.unique F' (R.isIteratedResidue i F' 0 (s i) hdim').rec' hrec'
    -- preadmissibility at the two points
    haveI : LocallyOfFiniteType (ιS' ≫ sX i) := F'.isNormalVariety.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType ((ιq ≫ ιZ) ≫ sX j) :=
      (StratumAdjunctionData.step FZ ιq Bq hιq).isNormalVariety.1.toLocallyOfFiniteType
    haveI := F'.isNormalVariety.1
    haveI := (StratumAdjunctionData.step FZ ιq Bq hιq).isNormalVariety.1
    haveI : CompactSpace S' := QuasiCompact.compactSpace_of_compactSpace (ιS' ≫ sX i)
    haveI : CompactSpace Tq := QuasiCompact.compactSpace_of_compactSpace ((ιq ≫ ιZ) ≫ sX j)
    haveI := (StratumAdjunctionData.step FZ ιq Bq hιq).isNormal_stratum
    haveI := (StratumAdjunctionData.step FZ ιq Bq hιq).isLocallyNoetherian_stratum
    obtain ⟨σpt⟩ := nonempty_functionFieldEquiv_of_topologicalKrullDim_eq_zero (ιS' ≫ sX i)
      ((ιq ≫ ιZ) ≫ sX j) hdim' hdq'
    have hσpt := isCrepantBirationalMap_of_topologicalKrullDim_eq_zero (k := k) hdim' hdq' BS' Bq
      σpt
    have hpre := hs i j F' (StratumAdjunctionData.step FZ ιq Bq hιq) 0
      (by rw [hlen']; exact le_add_left one_le_two)
      (Nat.le_add_left 1 _) hdim' hdq' σpt hσpt
    rw [hRsj, hRsi, pluriformPullback_smul_formPow_ιMulti_zero hdim' hdq'] at hpre
    have h0 : (algebraMap k S'.functionField au - algebraMap k S'.functionField as) •
        (show RationalPluriForms (ιS' ≫ sX i) 0 m from
          formPow (exteriorPower.ιMulti S'.functionField 0 ![]) m) = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.2 hpre
    rcases smul_eq_zero.1 h0 with h1 | h1
    · exact (algebraMap k S'.functionField).injective (sub_eq_zero.1 h1)
    · exact absurd h1 (formPow_ιMulti_zero_ne_zero m)
  have hfin : resZ gj = resZ g' := by
    have h1 : (resZ gj - resZ g') • (formPow (exteriorPower.ιMulti TZ.functionField 1 fun _ =>
        (resZ v)⁻¹ • KaehlerDifferential.D k TZ.functionField (resZ v)) m :
          RationalPluriForms (ιZ ≫ sX j) 1 m) = 0 := by
      rw [sub_smul, hTu, hTs, haus, sub_self]
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact sub_eq_zero.1 h2
    · exact absurd h2 hθv0
  rw [hgPjl, hgP'l, hfin]

/-- **Coefficients along a curve stratum agree.** In the situation of
`toFun_step_refl_eq_of_isExceptional_of_curve`: the restrictions to `k(T)` of the coefficients
`g_j` of `s_j` and `g'` of `σ⁻¹^* s_i` at the generic point `x` of the curve agree. -/
private theorem stalkMap_eq_of_isExceptional_of_curve
    (R : ResidueRestriction sX B 3 m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {s : ∀ l, logPluricanonicalSections (sX l) 3 m (B l)} (hs : s ∈ preadmissibleSections R)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (P : Mori.PrimeDivisor (X i))
    (hP : ι (genericPoint T) = P.genericPoint) (hP1 : (B i).coeff P = 1)
    (hrange : Set.range ι.base = (P.support : Set (X i))) (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g))
    (z : Fin 2 → (X j).presheaf.stalk (D.f D.E.genericPoint))
    (L : Fin 2 → Mori.PrimeDivisor (X j)) (hz : IsRegularSystemOfParameters z)
    (hL : Function.Injective L)
    (hLx : ∀ a, D.f D.E.genericPoint ∈ (L a).support)
    (hLz : ∀ a, IdealSheafData.stalk (L a).idealSheaf (D.f D.E.genericPoint) = Ideal.span {z a})
    (hBL : ∀ E : Mori.PrimeDivisor (X j), D.f D.E.genericPoint ∈ E.support →
      (B j).coeff E ≠ 0 → E ∈ Set.range L)
    (hL1 : ∀ a, (B j).coeff (L a) = 1)
    (v : (X j).presheaf.stalk (D.f D.E.genericPoint)) (hvu : IsUnit v)
    (hw : letI := stalkAlgebra (sX j) (D.f D.E.genericPoint)
      Submodule.span ((X j).presheaf.stalk (D.f D.E.genericPoint)) (Set.range fun a : Fin 3 =>
        KaehlerDifferential.D k ((X j).presheaf.stalk (D.f D.E.genericPoint))
          (![z 0, z 1, v] a)) = ⊤) [CompactSpace (X j)] [LocallyOfFiniteType (sX j)]
    (hQj : letI := functionFieldAlgebra (sX j)
      (Divisor.toQDivisor (divisorOfForm (show RationalPluriForms (sX j) 3 ((1 : ℕ) : ℤ) from
        formPow (exteriorPower.ιMulti (X j).functionField 3 fun a =>
          (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
            (![z 0, z 1, v] a))⁻¹ • KaehlerDifferential.D k (X j).functionField
              (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
                (![z 0, z 1, v] a))) 1)) + B j).IsQCartier)
    (U : (X j).Opens) (hxU : D.f D.E.genericPoint ∈ U)
    (hU : letI := functionFieldAlgebra (sX j)
      ∀ E : Mori.PrimeDivisor (X j), (E.support ∩ (U : Set (X j))).Nonempty →
      (Divisor.toQDivisor (divisorOfForm (show RationalPluriForms (sX j) 3 ((1 : ℕ) : ℤ) from
        formPow (exteriorPower.ιMulti (X j).functionField 3 fun a =>
          (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
            (![z 0, z 1, v] a))⁻¹ • KaehlerDifferential.D k (X j).functionField
              (algebraMap ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField
                (![z 0, z 1, v] a))) 1)) + B j).coeff E = 0)
    (hle : ∀ r : (X j).presheaf.stalk (D.f D.E.genericPoint),
      P.divisorialValuation ((σ.toHom) (algebraMap _ (X j).functionField r)) ≤ 1)
    (hlt : ∀ r ∈ IsLocalRing.maximalIdeal ((X j).presheaf.stalk (D.f D.E.genericPoint)),
      P.divisorialValuation ((σ.toHom) (algebraMap _ (X j).functionField r)) < 1)
    (t : (X i).presheaf.stalk (ι (genericPoint T)))
    (e' : Fin 2 → (X i).presheaf.stalk (ι (genericPoint T))) (he' : ∀ b, IsUnit (e' b))
    (ht : (X i).ord (algebraMap _ (X i).functionField t) (ι (genericPoint T)) = 1)
    (hfr : letI := functionFieldAlgebra (sX i); letI := functionFieldAlgebra (sX j)
      exteriorPower.ιMulti (X i).functionField 3 (fun a =>
          ((σ.toHom) (algebraMap _ (X j).functionField (![z 0, z 1, v] a)))⁻¹ •
            KaehlerDifferential.D k (X i).functionField
              ((σ.toHom) (algebraMap _ (X j).functionField (![z 0, z 1, v] a)))) =
        exteriorPower.ιMulti (X i).functionField 3 (Fin.cons
          ((algebraMap _ (X i).functionField t)⁻¹ • KaehlerDifferential.D k _ (algebraMap _ _ t))
          fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ _ (e' b))))
    (he'1 : algebraMap _ (X i).functionField (e' 1) =
      (σ.toHom) (algebraMap _ (X j).functionField v))
    (hgen : letI := functionFieldAlgebra (ι ≫ sX i)
      IntermediateField.adjoin k (Set.range (fun r : (X j).presheaf.stalk (D.f D.E.genericPoint) =>
        residueAlong ι P hP ((σ.toHom) (algebraMap _ (X j).functionField r))) ∪
          {(ι.stalkMap (genericPoint T)).hom (e' 0)}) = ⊤)
    (gj g' : (X j).presheaf.stalk (D.f D.E.genericPoint))
    (hgj : letI := functionFieldAlgebra (sX j)
      (s j : RationalPluriForms (sX j) 3 m) = algebraMap _ (X j).functionField gj •
        (show RationalPluriForms (sX j) 3 m from formPow (exteriorPower.ιMulti (X j).functionField 3
          fun a => (algebraMap _ (X j).functionField (![z 0, z 1, v] a))⁻¹ •
            KaehlerDifferential.D k (X j).functionField
              (algebraMap _ (X j).functionField (![z 0, z 1, v] a))) m))
    (u' : logPluricanonicalSections (sX j) 3 m (B j))
    (hg' : letI := functionFieldAlgebra (sX j)
      (u' : RationalPluriForms (sX j) 3 m) = algebraMap _ (X j).functionField g' •
        (show RationalPluriForms (sX j) 3 m from formPow (exteriorPower.ιMulti (X j).functionField 3
          fun a => (algebraMap _ (X j).functionField (![z 0, z 1, v] a))⁻¹ •
            KaehlerDifferential.D k (X j).functionField
              (algebraMap _ (X j).functionField (![z 0, z 1, v] a))) m))
    (u : logPluricanonicalSections (sX i) 3 m (B i))
    (gPj gP' : (X i).presheaf.stalk (ι (genericPoint T)))
    (hgPj : algebraMap _ (X i).functionField gPj = (σ.toHom) (algebraMap _ (X j).functionField gj))
    (hgP' : algebraMap _ (X i).functionField gP' = (σ.toHom) (algebraMap _ (X j).functionField g'))
    (hu2 : letI := functionFieldAlgebra (sX i)
      (u : RationalPluriForms (sX i) 3 m) = algebraMap _ (X i).functionField gPj •
        formPow (exteriorPower.ιMulti (X i).functionField (2 + 1)
          (Fin.cons ((algebraMap _ (X i).functionField t)⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ (X i).functionField t))
            fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
              KaehlerDifferential.D k _ (algebraMap _ (X i).functionField (e' b)))) m)
    (hsi2 : letI := functionFieldAlgebra (sX i)
      (s i : RationalPluriForms (sX i) 3 m) = algebraMap _ (X i).functionField gP' •
        formPow (exteriorPower.ιMulti (X i).functionField (2 + 1)
          (Fin.cons ((algebraMap _ (X i).functionField t)⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ (X i).functionField t))
            fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
              KaehlerDifferential.D k _ (algebraMap _ (X i).functionField (e' b)))) m) :
    (ι.stalkMap (genericPoint T)).hom gPj = (ι.stalkMap (genericPoint T)).hom gP' := by
  classical
  have hPi := R.setting.isPair i
  have hPj := R.setting.isPair j
  have := hPi.isAlgClosed
  have := hPi.charZero
  have hX := hPi.isPair.1
  have hXj := hPj.isPair.1
  haveI := hX.1
  haveI := hXj.1
  haveI : LocallyOfFiniteType (sX i) := hX.1.toLocallyOfFiniteType
  haveI : CompactSpace (X i) := QuasiCompact.compactSpace_of_compactSpace (sX i)
  haveI : IsProper (sX i) :=
    isProper_of_isProjectiveMorphism _ (R.setting.isProjectiveVariety i).isProjective
  haveI : IsProper (sX j) :=
    isProper_of_isProjectiveMorphism _ (R.setting.isProjectiveVariety j).isProjective
  have hni := R.setting.topologicalKrullDim_eq i
  have hnj := R.setting.topologicalKrullDim_eq j
  have hnj' : topologicalKrullDim (X j) = ((3 : ℕ) : WithBot ℕ∞) := hnj
  letI := functionFieldAlgebra (sX i)
  letI := functionFieldAlgebra (sX j)
  have hιs : IsAdjunctionStep (sX i) (B i) ι BT := hι
  have hTnv : IsNormalVariety k (ι ≫ sX i) := hιs.1
  haveI : IsNormal T := hTnv.2
  haveI : LocallyOfFiniteType (ι ≫ sX i) := hTnv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sX i)
  obtain ⟨-, -, -, -, hci, -⟩ := id hιs
  haveI := hci
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace ι
  have hdT : topologicalKrullDim T = (2 : ℕ) :=
    topologicalKrullDim_eq_of_range_eq_support (sX i) ι P hrange hni
  letI := functionFieldAlgebra (ι ≫ sX i)
  -- the flag to the curve on `X_j`
  obtain ⟨TZ, ιZ, BZ, FZ, hlenZ, hdimZ, hgenZ, resZ, hresZs, hresZm, hresZk, hrecZ, hstalkZ,
    hpbZ, hdltZ, hLRZ⟩ :=
    exists_flag_isIteratedResidueRec_of_curve hXj hPj.isPair (R.setting.isDltPair j) hnj' z hz v
      hvu hw L hL hLx hLz hBL hL1 hQj
  haveI := FZ.isIntegral_stratum
  haveI : LocallyOfFiniteType (ιZ ≫ sX j) := FZ.isNormalVariety.1.toLocallyOfFiniteType
  letI := functionFieldAlgebra (ιZ ≫ sX j)
  -- the residue map along `P` and the embedding `λ : k(Z) → k(T)`
  have hres1 : residueAlong ι P hP 1 = 1 := by
    rw [← map_one (algebraMap ((X i).presheaf.stalk (ι (genericPoint T))) (X i).functionField),
      residueAlong_algebraMap, map_one]
  let ρ : (X j).presheaf.stalk (D.f D.E.genericPoint) →+* T.functionField :=
    { toFun := fun r => residueAlong ι P hP ((σ.toHom) (algebraMap _ (X j).functionField r))
      map_one' := by simp only [map_one]; exact hres1
      map_mul' := fun r r' => by
        simp only [map_mul]; exact residueAlong_mul ι P hP (hle r) (hle r')
      map_zero' := by
        simp only [map_zero]
        exact residueAlong_eq_zero_of_lt_one ι P hP (by simp)
      map_add' := fun r r' => by
        simp only [map_add]; exact residueAlong_add ι P hP (hle r) (hle r') }
  have hρ : ∀ r, ρ r = residueAlong ι P hP ((σ.toHom) (algebraMap _ (X j).functionField r)) :=
    fun _ => rfl
  have hker : RingHom.ker resZ ≤ RingHom.ker ρ := by
    intro r hr
    rw [RingHom.mem_ker] at hr ⊢
    have hm : r ∈ IsLocalRing.maximalIdeal ((X j).presheaf.stalk (D.f D.E.genericPoint)) := by
      by_contra hnm
      have hu : IsUnit r := by
        by_contra hnu; exact hnm ((IsLocalRing.mem_maximalIdeal _).2 hnu)
      have := hu.map resZ
      rw [hr] at this
      exact not_isUnit_zero this
    rw [hρ]
    exact residueAlong_eq_zero_of_lt_one ι P hP (hlt r hm)
  obtain ⟨lam, hlam⟩ : ∃ l : TZ.functionField →+* T.functionField,
      l = (resZ.liftOfSurjective hresZs) ⟨ρ, hker⟩ := ⟨_, rfl⟩
  have hlamZ : ∀ r, lam (resZ r) = ρ r := fun r => by
    rw [hlam]; exact RingHom.liftOfSurjective_comp_apply resZ hresZs ⟨ρ, hker⟩ r
  -- `λ` is a `k`-algebra map
  have hρk : ∀ c : k, ρ (letI := stalkAlgebra (sX j) (D.f D.E.genericPoint)
      algebraMap k _ c) = algebraMap k T.functionField c := by
    intro c
    letI := stalkAlgebra (sX j) (D.f D.E.genericPoint)
    haveI := isScalarTower_stalk_functionField (sX j) (D.f D.E.genericPoint)
    letI := stalkAlgebra (sX i) (ι (genericPoint T))
    haveI := isScalarTower_stalk_functionField (sX i) (ι (genericPoint T))
    rw [hρ, ← IsScalarTower.algebraMap_apply, AlgHom.commutes,
      IsScalarTower.algebraMap_apply k ((X i).presheaf.stalk (ι (genericPoint T)))
        (X i).functionField c, residueAlong_algebraMap]
    exact stalkMap_algebraMap_const (sX i) ι (genericPoint T) c
  have hlamk : ∀ c : k, lam (algebraMap k TZ.functionField c) = algebraMap k T.functionField c := by
    intro c
    rw [← hresZk c, hlamZ, hρk]
  letI : Algebra TZ.functionField T.functionField := lam.toAlgebra
  haveI : IsScalarTower k TZ.functionField T.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (hlamk c).symm
  have hlamalg : ∀ a, algebraMap TZ.functionField T.functionField a = lam a := fun _ => rfl
  -- `k(T) = k(Z)(ē)` with `ē` transcendental
  obtain ⟨eb, heb⟩ : ∃ eb : T.functionField, eb = (ι.stalkMap (genericPoint T)).hom (e' 0) :=
    ⟨_, rfl⟩
  rw [← heb] at hgen
  have hgen' : IntermediateField.adjoin TZ.functionField {eb} = ⊤ := by
    have hle' : IntermediateField.adjoin k (Set.range (fun r : (X j).presheaf.stalk
        (D.f D.E.genericPoint) => residueAlong ι P hP ((σ.toHom) (algebraMap _ (X j).functionField
          r))) ∪ {eb}) ≤ (IntermediateField.adjoin TZ.functionField {eb}).restrictScalars k := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ (⟨r, rfl⟩ | h)
      · change ρ r ∈ _
        rw [← hlamZ, ← hlamalg]
        exact (IntermediateField.mem_restrictScalars k).2
          (IntermediateField.algebraMap_mem (IntermediateField.adjoin TZ.functionField {eb})
            (resZ r))
      · rw [Set.mem_singleton_iff.1 h]
        exact (IntermediateField.mem_restrictScalars k).2
          (IntermediateField.mem_adjoin_simple_self TZ.functionField eb)
    have hle'' : (⊤ : IntermediateField k T.functionField) ≤
        (IntermediateField.adjoin TZ.functionField {eb}).restrictScalars k :=
      (le_of_eq hgen.symm).trans hle'
    exact eq_top_iff.2 fun y _ => (IntermediateField.mem_restrictScalars k).1
      (hle'' IntermediateField.mem_top)
  have htr : Transcendental TZ.functionField eb := by
    intro halg
    have hint : IsIntegral TZ.functionField eb := halg.isIntegral
    haveI := IntermediateField.adjoin.finiteDimensional hint
    have hfin : FiniteDimensional TZ.functionField T.functionField := by
      have e1 := (IntermediateField.equivOfEq hgen').trans
        (IntermediateField.topEquiv (F := TZ.functionField) (E := T.functionField))
      exact LinearEquiv.finiteDimensional e1.toLinearEquiv
    haveI : Algebra.IsAlgebraic TZ.functionField T.functionField := Algebra.IsAlgebraic.of_finite _ _
    have h1 := trdeg_add_eq (R := k) (S := TZ.functionField) (A := T.functionField)
    rw [trdeg_eq_zero (R := TZ.functionField) (A := T.functionField), add_zero] at h1
    have h2 := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := ιZ ≫ sX j) hdimZ
    have h3 := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := ι ≫ sX i) hdT
    rw [h1] at h2
    omega
  -- the `ē`-adic valuation `ν₀` and its centre on `T`
  haveI : Algebra.EssFiniteType k TZ.functionField := essFiniteType_functionField (sX := ιZ ≫ sX j)
  obtain ⟨ν₀, hν₀k, hν₀e, hν₀res, hSν⟩ :=
    exists_valuation_of_transcendental (k := k) htr hgen'
  haveI : IsProper (ι ≫ sX i) := inferInstance
  obtain ⟨y₀, hy₀le, hy₀lt⟩ := exists_dominates_of_isProper_of_trivial (sX := ι ≫ sX i)
    inferInstance ν₀ (fun c hc => by
      have e1 : (((Scheme.ΓSpecIso (.of k)).inv ≫ (ι ≫ sX i).appTop ≫
          T.presheaf.germ ⊤ (genericPoint T) trivial).hom) c = algebraMap k T.functionField c := rfl
      rw [e1, IsScalarTower.algebraMap_apply k TZ.functionField T.functionField]
      exact hν₀k _ ((map_ne_zero _).2 hc))
  -- `y₀` is a curve or a closed point of `T`
  have hy₀ne : y₀ ≠ genericPoint T := by
    rintro rfl
    letI : Algebra (T.presheaf.stalk (genericPoint T)) T.functionField :=
      AlgebraicGeometry.stalkFunctionFieldAlgebra T (genericPoint T)
    have hfield : IsField (T.presheaf.stalk (genericPoint T)) := Field.toIsField T.functionField
    obtain ⟨a, ha⟩ := (IsFractionRing.surjective_iff_isField.2 hfield) eb⁻¹
    have h1 := hy₀le a
    rw [ha, map_inv₀, hν₀e, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at h1
    omega
  have hcoh1 : 1 ≤ Order.coheight y₀ := by
    by_contra hlt
    push Not at hlt
    have h0 : Order.coheight y₀ = 0 := ENat.lt_one_iff_eq_zero.1 hlt
    rw [Order.coheight_eq_zero] at h0
    apply hy₀ne
    have h1 : y₀ ≤ genericPoint T :=
      (Scheme.le_iff_specializes).2 ((genericPoint_spec T).specializes trivial)
    exact ((Scheme.le_iff_specializes).1 (h0 h1)).antisymm
      ((Scheme.le_iff_specializes).1 h1) |>.eq
  have hcoh2 : Order.coheight y₀ ≤ 2 := by
    have h4 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (ι ≫ sX i) y₀
    rw [hdT] at h4
    have h0 : 0 ≤ topologicalKrullDim (closure {y₀} : Set T) :=
      Order.krullDim_nonneg_iff.mpr ⟨⟨closure {⟨_, subset_closure rfl⟩},
        isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have h5 : ((Order.coheight y₀ : ℕ∞) : WithBot ℕ∞) ≤ (2 : ℕ) :=
      h4 ▸ le_add_of_nonneg_left h0
    exact_mod_cast WithBot.coe_le_coe.mp h5
  have hlamσ : ∀ (r : (X j).presheaf.stalk (D.f D.E.genericPoint))
      (a : (X i).presheaf.stalk (ι (genericPoint T))),
      algebraMap _ (X i).functionField a = (σ.toHom) (algebraMap _ (X j).functionField r) →
      lam (resZ r) = (ι.stalkMap (genericPoint T)).hom a := fun r a ha => by
    rw [hlamZ, hρ, ← ha, residueAlong_algebraMap]
  -- if both coefficients restrict to zero there is nothing to prove
  by_cases hzero : (ι.stalkMap (genericPoint T)).hom gPj = 0 ∧
      (ι.stalkMap (genericPoint T)).hom gP' = 0
  · rw [hzero.1, hzero.2]
  have hgPjl : (ι.stalkMap (genericPoint T)).hom gPj = lam (resZ gj) := (hlamσ gj gPj hgPj).symm
  have hgP'l : (ι.stalkMap (genericPoint T)).hom gP' = lam (resZ g') :=
    (hlamσ g' gP' hgP').symm
  have hlamv : lam (resZ v) = (ι.stalkMap (genericPoint T)).hom (e' 1) := hlamσ v (e' 1) he'1
  -- the frame `dv̄` on `Z`
  have hwZ' : Submodule.span TZ.functionField {(KaehlerDifferential.D k TZ.functionField
      (resZ v))} = ⊤ := by
    have hzm : ∀ a, z a ∈ IsLocalRing.maximalIdeal ((X j).presheaf.stalk (D.f D.E.genericPoint)) :=
      fun a => hz.1 ▸ Ideal.subset_span ⟨a, rfl⟩
    letI := stalkAlgebra (sX j) (D.f D.E.genericPoint)
    let resZk : (X j).presheaf.stalk (D.f D.E.genericPoint) →ₐ[k] TZ.functionField :=
      { resZ with commutes' := hresZk }
    have hwZ := span_D_eq_top_of_surjective resZk hresZs _ hw
    rw [eq_top_iff, ← hwZ, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    fin_cases a
    · change KaehlerDifferential.D k _ (resZ (z 0)) ∈ _
      rw [hresZm _ (hzm 0), map_zero]; exact Submodule.zero_mem _
    · change KaehlerDifferential.D k _ (resZ (z 1)) ∈ _
      rw [hresZm _ (hzm 1), map_zero]; exact Submodule.zero_mem _
    · exact Submodule.subset_span rfl
  haveI := FZ.isNormal_stratum
  haveI := FZ.isLocallyNoetherian_stratum
  haveI := FZ.isClosedImmersion
  haveI : CompactSpace TZ := QuasiCompact.compactSpace_of_compactSpace ιZ
  by_cases hA : Order.coheight y₀ = 1
  · -- the centre of `ν₀` is a curve `C` of `T`
    refine (stalkMapExc_exists_stalk_lift σ P hP D hle hgenZ resZ hstalkZ lam hlamσ).elim
      fun ψ hψ => ?_
    exact (stalkMapExc_exists_curve_centre R (hι := hι) (P := P) (hrange := hrange)
      (D := D) (v := v) (hvu := hvu) (t := t) (e' := e') (he' := he') (ht := ht) (gj := gj)
      (g' := g') (u := u) (gPj := gPj) (gP' := gP') (hu2 := hu2) (hsi2 := hsi2) (resZ := resZ)
      (hwZ' := hwZ') (lam := lam) (hlamk := hlamk) (hlamv := hlamv) (hgPjl := hgPjl)
      (hgP'l := hgP'l) (hzero := hzero) (ν₀ := ν₀) (hν₀k := fun c hc => hν₀k c hc) (eb := eb)
      (heb := heb) (hν₀e := hν₀e) (hν₀res := fun f hf => hν₀res f hf) (y₀ := y₀)
      (hy₀le := hy₀le) (hy₀lt := hy₀lt) (hA := hA)).elim fun C hC =>
      stalkMapExc_eq_of_curve_centre R σ (hσ := hσ) (hs := hs) (h := h) (hι := hι) (P := P)
        (hP1 := hP1) (hrange := hrange) (D := D) (hDv := hDv) (z := z) (v := v)
        (hvu := hvu) (U := U) (hxU := hxU) (hU := hU) (t := t) (e' := e')
        (he' := he') (ht := ht) (hfr := hfr) (gj := gj) (g' := g') (hgj := hgj) (gPj := gPj)
        (gP' := gP') (hsi2 := hsi2) (resZ := resZ) (FZ := FZ) (hdimZ := hdimZ) (hrecZ := hrecZ)
        (hlenZ := hlenZ) (hgenZ := hgenZ) (hpbZ := hpbZ) (hwZ' := hwZ')
        (lam := lam) (hlamk := hlamk) (hlamv := hlamv) (hgPjl := hgPjl) (hgP'l := hgP'l)
        (ψ := ψ) (hψ := hψ.1) (hlamψ := hψ.2) (ν₀ := ν₀) (hν₀k := fun c hc => hν₀k c hc)
        (eb := eb) (heb := heb)
        (hν₀e := hν₀e) (hν₀res := fun f hf => hν₀res f hf) (y₀ := y₀) (hy₀le := hy₀le)
        (C := C) (hCη := hC.1) (hν₀C := hC.2.1) (hBC := hC.2.2.1) (hordωT := hC.2.2.2.1)
        (hωT0 := hC.2.2.2.2)
  · -- the centre of `ν₀` is a closed point of `T`
    have hc2 : Order.coheight y₀ = 2 := by
      have hfin : Order.coheight y₀ ≠ ⊤ := ne_top_of_le_ne_top (by decide) hcoh2
      obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hfin
      rw [← hc] at hcoh1 hcoh2 hA ⊢
      norm_cast at hcoh1 hcoh2 hA ⊢
      omega
    exact stalkMapExc_eq_of_point_centre R (hs := hs) (h := h) (hι := hι) (P := P) (hP1 := hP1)
      (hrange := hrange) (D := D) (z := z) (v := v) (t := t) (e' := e') (he' := he') (ht := ht)
      (gj := gj) (g' := g') (hgj := hgj) (u' := u') (hg' := hg') (u := u) (gPj := gPj)
      (gP' := gP') (hu2 := hu2) (hsi2 := hsi2) (resZ := resZ) (FZ := FZ) (hdimZ := hdimZ)
      (hrecZ := hrecZ) (hdltZ := hdltZ) (hLRZ := hLRZ) (hwZ' := hwZ') (lam := lam)
      (hlamk := hlamk) (hlamv := hlamv) (hgPjl := hgPjl) (hgP'l := hgP'l) (hzero := hzero)
      (ν₀ := ν₀) (hν₀k := fun c hc => hν₀k c hc) (eb := eb) (heb := heb) (hν₀e := hν₀e)
      (hν₀res := fun f hf => hν₀res f hf) (y₀ := y₀) (hy₀le := hy₀le) (hy₀lt := hy₀lt)
      (hSν := hSν) (hc2 := hc2)

/-- Monomials in two coordinates are monomials in three, the third of weight zero. -/
private theorem weightedMonomialIdeal_le_snoc {R : Type*} [CommRing R] (z : Fin 2 → R)
    (α : Fin 2 → ℕ) (v : R) (M : ℕ) :
    weightedMonomialIdeal z α M ≤ weightedMonomialIdeal ![z 0, z 1, v] ![α 0, α 1, 0] M := by
  unfold weightedMonomialIdeal
  rw [Ideal.span_le]
  rintro _ ⟨β, hβ, rfl⟩
  refine Ideal.subset_span ⟨![β 0, β 1, 0], ?_, ?_⟩
  · simpa [Fin.sum_univ_three, Fin.sum_univ_two] using hβ
  · simp [Fin.prod_univ_three, Fin.prod_univ_two]

/-- **Floor divisors centred at a curve stratum.** Let `P` be a floor divisor of `X_i` whose
valuation is that of a divisor `D` over `X_j` of discrepancy `-1` centred at the generic point `x`
of a curve, with snc coordinates `z₁, z₂` at `x`. Completing them by a unit `v` to the frame
`τ = dlog z₁ ∧ dlog z₂ ∧ dlog v`, write `s_j = g_j τ^m` and `σ⁻¹^* s_i = g' τ^m` near `x`. The
residues of `σ^* s_j` and of `s_i` along `P` are `ḡ_j θ^m` and `ḡ' θ^m` for the residue `θ` of
`σ^* τ`, and the restrictions `ḡ_j`, `ḡ'` of `g_j`, `g'` to the curve agree. -/
private theorem toFun_step_refl_eq_of_isExceptional_of_curve
    (R : ResidueRestriction sX B 3 m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {s : ∀ l, logPluricanonicalSections (sX l) 3 m (B l)} (hs : s ∈ preadmissibleSections R)
    (u : logPluricanonicalSections (sX i) 3 m (B i))
    (hu : (u : RationalPluriForms (sX i) 3 m) =
      pluriformPullback (sX i) (sX j) σ.toHom 3 m (s j))
    (u' : logPluricanonicalSections (sX j) 3 m (B j))
    (hσσ : pluriformPullback (sX i) (sX j) σ.toHom 3 m (u' : RationalPluriForms (sX j) 3 m) =
      (s i : RationalPluriForms (sX i) 3 m))
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) (e : ℕ)
    (he : topologicalKrullDim T = e) [IsIntegral T] (P : Mori.PrimeDivisor (X i))
    (hP : ι (genericPoint T) = P.genericPoint) (hP1 : (B i).coeff P = 1)
    (hrange : Set.range ι.base = (P.support : Set (X i))) (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g))
    (z : Fin 2 → (X j).presheaf.stalk (D.f D.E.genericPoint))
    (L : Fin 2 → Mori.PrimeDivisor (X j)) (α : Fin 2 → ℕ)
    (hz : IsRegularSystemOfParameters z) (hL : Function.Injective L)
    (hLx : ∀ a, D.f D.E.genericPoint ∈ (L a).support)
    (hLz : ∀ a, IdealSheafData.stalk (L a).idealSheaf (D.f D.E.genericPoint) = Ideal.span {z a})
    (hBL : ∀ E : Mori.PrimeDivisor (X j), D.f D.E.genericPoint ∈ E.support →
      (B j).coeff E ≠ 0 → E ∈ Set.range L)
    (hL1 : ∀ a, (B j).coeff (L a) = 1) (hsm : D.f D.E.genericPoint ∈ Mori.smoothLocus (sX j))
    (hα : ∀ a, 0 < α a)
    (hzv : ∀ a, D.valuation (algebraMap _ (X j).functionField (z a)) = WithZero.exp (-(α a : ℤ)))
    (hmono : ∀ f : (X j).presheaf.stalk (D.f D.E.genericPoint), f ≠ 0 → ∃ M : ℕ,
      f ∈ weightedMonomialIdeal z α M ∧
      D.valuation (algebraMap _ (X j).functionField f) = WithZero.exp (-(M : ℤ))) :
    R.toFun i (.step (.refl h) ι BT hι) e u = R.toFun i (.step (.refl h) ι BT hι) e (s i) := by
  classical
  have hPi := R.setting.isPair i
  have hPj := R.setting.isPair j
  have := hPi.isAlgClosed
  have := hPi.charZero
  have hX := hPi.isPair.1
  have hXj := hPj.isPair.1
  haveI := hX.1
  haveI := hXj.1
  haveI : LocallyOfFiniteType (sX i) := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (sX j) := hXj.1.toLocallyOfFiniteType
  haveI : CompactSpace (X i) := QuasiCompact.compactSpace_of_compactSpace (sX i)
  haveI : CompactSpace (X j) := QuasiCompact.compactSpace_of_compactSpace (sX j)
  haveI : IsProper (sX i) :=
    isProper_of_isProjectiveMorphism _ (R.setting.isProjectiveVariety i).isProjective
  haveI : IsProper (sX j) :=
    isProper_of_isProjectiveMorphism _ (R.setting.isProjectiveVariety j).isProjective
  obtain ⟨K, hK, hmK⟩ := exists_canonical_cartier R i
  obtain ⟨K', hK', hmK'⟩ := exists_canonical_cartier R j
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast R.setting.pos.ne'
  have hni := R.setting.topologicalKrullDim_eq i
  have hnj := R.setting.topologicalKrullDim_eq j
  have hnj' : topologicalKrullDim (X j) = ((3 : ℕ) : WithBot ℕ∞) := hnj
  letI := functionFieldAlgebra (sX i)
  letI := functionFieldAlgebra (sX j)
  have hιs : IsAdjunctionStep (sX i) (B i) ι BT := hι
  have hTnv : IsNormalVariety k (ι ≫ sX i) := hιs.1
  haveI : IsNormal T := hTnv.2
  haveI : LocallyOfFiniteType (ι ≫ sX i) := hTnv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sX i)
  obtain ⟨-, -, -, -, hci, -⟩ := id hιs
  haveI := hci
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace ι
  have hdT : topologicalKrullDim T = (2 : ℕ) :=
    topologicalKrullDim_eq_of_range_eq_support (sX i) ι P hrange hni
  have hz0 : ∀ a, z a ≠ 0 := by
    haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
    exact fun a => MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz a
  -- the frame `τ = dlog z₁ ∧ dlog z₂ ∧ dlog v` at the centre
  obtain ⟨v, hvu, hw⟩ := exists_isUnit_span_D_eq_top_of_mem_smoothLocus (sX := sX j) hnj' hsm z hz
  set z3 : Fin 3 → (X j).presheaf.stalk (D.f D.E.genericPoint) := ![z 0, z 1, v] with hz3
  have hz30 : ∀ a, z3 a ≠ 0 := by
    intro a; fin_cases a
    · exact hz0 0
    · exact hz0 1
    · exact hvu.ne_zero
  set S3 : Set (Fin 3) := {0, 1} with hS3
  set L3 : Fin 3 → Mori.PrimeDivisor (X j) := ![L 0, L 1, L 0] with hL3def
  have hS3a : ∀ a ∈ S3, ∃ b : Fin 2, L3 a = L b ∧ z3 a = z b := by
    intro a ha
    rcases ha with rfl | rfl
    · exact ⟨0, rfl, rfl⟩
    · exact ⟨1, rfl, rfl⟩
  have hL3 : Set.InjOn L3 S3 := by
    intro a ha a' ha' haa
    rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl
    · rfl
    · exact absurd (hL haa) (by decide)
    · exact absurd (hL haa) (by decide)
    · rfl
  have hL3x : ∀ a ∈ S3, D.f D.E.genericPoint ∈ (L3 a).support := fun a ha => by
    obtain ⟨b, hb, -⟩ := hS3a a ha; rw [hb]; exact hLx b
  have hL3z : ∀ a ∈ S3, IdealSheafData.stalk (L3 a).idealSheaf (D.f D.E.genericPoint) = Ideal.span {z3 a} :=
    fun a ha => by obtain ⟨b, hb, hb'⟩ := hS3a a ha; rw [hb, hb']; exact hLz b
  have hu3 : ∀ a ∉ S3, IsUnit (z3 a) := by
    intro a ha
    fin_cases a
    · exact absurd (Or.inl rfl) ha
    · exact absurd (Or.inr rfl) ha
    · exact hvu
  have hBL3 : ∀ E : Mori.PrimeDivisor (X j), D.f D.E.genericPoint ∈ E.support → (B j).coeff E ≠ 0 → E ∈ L3 '' S3 := by
    intro E hE h0
    obtain ⟨b, rfl⟩ := hBL E hE h0
    fin_cases b
    · exact ⟨0, Or.inl rfl, rfl⟩
    · exact ⟨1, Or.inr rfl, rfl⟩
  have hL13 : ∀ a ∈ S3, (B j).coeff (L3 a) = 1 := fun a ha => by
    obtain ⟨b, hb, -⟩ := hS3a a ha; rw [hb]; exact hL1 b
  obtain ⟨U, hxU, hU⟩ := exists_open_coeff_divisorOfForm_add_eq_zero_of_isUnit hnj' z3 hz30 hw S3
    L3 hL3 hL3x hL3z hu3 hBL3 hL13
  -- the monomial frame along `P`
  have hvD : ∀ r : (X j).presheaf.stalk (D.f D.E.genericPoint),
      D.valuation (algebraMap _ (X j).functionField r) ≤ 1 := by
    intro r
    by_cases hr : r = 0
    · rw [hr, map_zero, map_zero]; exact zero_le'
    obtain ⟨M, -, hM⟩ := hmono r hr
    rw [hM, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hle : ∀ r : (X j).presheaf.stalk (D.f D.E.genericPoint),
      P.divisorialValuation ((σ.toHom) (algebraMap _ (X j).functionField r)) ≤ 1 :=
    fun r => by rw [← hDv]; exact hvD r
  have hlt : ∀ r ∈ IsLocalRing.maximalIdeal ((X j).presheaf.stalk (D.f D.E.genericPoint)),
      P.divisorialValuation ((σ.toHom) (algebraMap _ (X j).functionField r)) < 1 := by
    intro r hr
    rw [← hDv]
    have h1 : r ∈ weightedMonomialIdeal z α 1 := by
      have := span_range_le_weightedMonomialIdeal_one z α hα
      rw [hz.1] at this
      exact this hr
    have h2 := valuation_le_of_mem_weightedMonomialIdeal z α D.valuation hvD hzv h1
    refine h2.trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hvP : P.divisorialValuation ((σ.toHom) (algebraMap _ (X j).functionField v)) = 1 := by
    obtain ⟨w, hw1⟩ := hvu.exists_right_inv
    have h1 := hle v
    have h2 := hle w
    have h3 : P.divisorialValuation ((σ.toHom) (algebraMap _ (X j).functionField v)) *
        P.divisorialValuation ((σ.toHom) (algebraMap _ (X j).functionField w)) = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, hw1, map_one, map_one, map_one]
    refine le_antisymm h1 ?_
    calc (1 : ℤᵐ⁰) = _ := h3.symm
      _ ≤ P.divisorialValuation ((σ.toHom) (algebraMap _ (X j).functionField v)) * 1 :=
        mul_le_mul' le_rfl h2
      _ = _ := mul_one _
  set α3 : Fin 3 → ℕ := ![α 0, α 1, 0] with hα3
  have hzv3 : ∀ a, P.divisorialValuation ((σ.toHom) (algebraMap _ (X j).functionField (z3 a))) =
      WithZero.exp (-(α3 a : ℤ)) := by
    intro a
    fin_cases a
    · rw [← hDv]; exact hzv 0
    · rw [← hDv]; exact hzv 1
    · change P.divisorialValuation ((σ.toHom) (algebraMap _ (X j).functionField v)) = _
      rw [hvP]; simp [α3]
  have hmono3 : ∀ f : (X j).presheaf.stalk (D.f D.E.genericPoint), f ≠ 0 → ∃ M : ℕ,
      f ∈ weightedMonomialIdeal z3 α3 M ∧
      P.divisorialValuation ((σ.toHom) (algebraMap _ (X j).functionField f)) =
        WithZero.exp (-(M : ℤ)) := by
    intro f hf
    obtain ⟨M, hM, hMv⟩ := hmono f hf
    exact ⟨M, weightedMonomialIdeal_le_snoc z α v M hM, by rw [← hDv]; exact hMv⟩
  obtain ⟨t, e', he', ht, hfr, he'1, hgen⟩ := exists_monomialFrame_of_unit ι P hP σ z3 α3 rfl
    hz30 hle hlt hzv3 hmono3
  have hpullm : ∀ (m' : ℕ) (c : (X j).functionField),
      pluriformPullback (sX i) (sX j) σ.toHom 3 m' (c • formPow (exteriorPower.ιMulti
        (X j).functionField 3 fun a => (algebraMap _ (X j).functionField (z3 a))⁻¹ •
          KaehlerDifferential.D k _ (algebraMap _ (X j).functionField (z3 a))) m') =
      ((σ.toHom : FunctionFieldHom (sX i) (sX j)) c) • formPow (exteriorPower.ιMulti
        (X i).functionField (2 + 1)
        (Fin.cons ((algebraMap _ (X i).functionField t)⁻¹ •
          KaehlerDifferential.D k _ (algebraMap _ (X i).functionField t))
          fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ (X i).functionField (e' b)))) m' := by
    intro m' c
    rw [pluriformPullback_smul_formPow_dlog hni hnj σ.toHom (fun a => algebraMap _ _ (z3 a)) m' c,
      hfr]
  -- coefficients of `s_j` and of `u'` at the centre, and their lifts along `P`
  obtain ⟨gj, hgj⟩ := exists_algebraMap_smul_of_mem_logPluricanonicalSections_of_isUnit hnj' z3
    hz30 hw S3 L3 hL3 hL3x hL3z hu3 ⟨0, Or.inl rfl⟩ hBL3 hL13 R.setting.pos
    (s j : RationalPluriForms (sX j) 3 m) (s j).2
  obtain ⟨g', hg'⟩ := exists_algebraMap_smul_of_mem_logPluricanonicalSections_of_isUnit hnj' z3
    hz30 hw S3 L3 hL3 hL3x hL3z hu3 ⟨0, Or.inl rfl⟩ hBL3 hL13 R.setting.pos
    (u' : RationalPluriForms (sX j) 3 m) u'.2
  dsimp only at hgj hg'
  obtain ⟨gPj, hgPj⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one P hP (hle gj)
  obtain ⟨gP', hgP'⟩ := exists_algebraMap_eq_of_divisorialValuation_le_one P hP (hle g')
  have hu2 : (u : RationalPluriForms (sX i) 3 m) = algebraMap _ (X i).functionField gPj •
      formPow (exteriorPower.ιMulti (X i).functionField (2 + 1)
        (Fin.cons ((algebraMap _ (X i).functionField t)⁻¹ •
          KaehlerDifferential.D k _ (algebraMap _ (X i).functionField t))
          fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ (X i).functionField (e' b)))) m := by
    have h1 := hpullm m (algebraMap _ _ gj)
    rw [← hgPj] at h1
    rw [hu, hgj]
    exact h1
  have hsi2 : (s i : RationalPluriForms (sX i) 3 m) = algebraMap _ (X i).functionField gP' •
      formPow (exteriorPower.ιMulti (X i).functionField (2 + 1)
        (Fin.cons ((algebraMap _ (X i).functionField t)⁻¹ •
          KaehlerDifferential.D k _ (algebraMap _ (X i).functionField t))
          fun b => (algebraMap _ (X i).functionField (e' b))⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ (X i).functionField (e' b)))) m := by
    have h1 := hpullm m (algebraMap _ _ g')
    rw [← hgP'] at h1
    rw [← hσσ, hg']
    exact h1
  -- the restrictions of `g_j` and `g'` to the curve agree
  have hkey : (ι.stalkMap (genericPoint T)).hom gPj = (ι.stalkMap (genericPoint T)).hom gP' := by
    have hτ1L := ordForm_formPow_dlog_eq_of_isUnit hnj' 1 z3 hz30 hw S3 L3 hL3 hL3x hL3z hu3 (L 0)
      (hLx 0)
    rw [if_pos ⟨0, Or.inl rfl, rfl⟩] at hτ1L
    have hτ10 : (show RationalPluriForms (sX j) 3 ((1 : ℕ) : ℤ) from formPow
        (exteriorPower.ιMulti (X j).functionField 3 fun a =>
          (algebraMap _ (X j).functionField (z3 a))⁻¹ •
            KaehlerDifferential.D k _ (algebraMap _ (X j).functionField (z3 a))) 1) ≠ 0 := by
      intro h0
      rw [h0, Mori.PrimeDivisor.ordForm_zero] at hτ1L
      exact absurd hτ1L (by decide)
    have hQj := (show (Divisor.toQDivisor K' + B j).IsQCartier from
      ⟨_, hm0, hmK'⟩).add_of_linearlyEquivalent
      (by simpa using (MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXj hK' hτ10).symm)
    exact stalkMap_eq_of_isExceptional_of_curve R σ hσ hs h hι P hP hP1 hrange D hDv z L hz hL
      hLx hLz hBL hL1 v hvu hw hQj U hxU hU hle hlt t e' he' ht hfr he'1 hgen gj g' hgj u' hg' u
      gPj gP' hgPj hgP' hu2 hsi2
  -- the residues along `P` agree
  have he2 : e = 2 := by
    have := he.symm.trans hdT
    exact_mod_cast this
  subst he2
  have hres_m := isPoincareResidue_formPow_dlog (sX i) ι m t e' he' ht
  letI := functionFieldAlgebra (ι ≫ sX i)
  set θm : RationalPluriForms (ι ≫ sX i) 2 m := formPow (exteriorPower.ιMulti T.functionField 2
    fun b => ((ι.stalkMap (genericPoint T)).hom (e' b))⁻¹ •
      KaehlerDifferential.D k T.functionField ((ι.stalkMap (genericPoint T)).hom (e' b))) m
    with hθm
  set c₀ := (ι.stalkMap (genericPoint T)).hom gPj with hc₀
  have hRu1 : IsPoincareResidue (sX i) ι 2 m (u : RationalPluriForms (sX i) 3 m) (c₀ • θm) := by
    have h1 := IsPoincareResidue.smul_stalk hres_m gPj
    rw [hu2]
    exact h1
  have hRs1 : IsPoincareResidue (sX i) ι 2 m (s i : RationalPluriForms (sX i) 3 m) (c₀ • θm) := by
    have h1 := IsPoincareResidue.smul_stalk hres_m gP'
    rw [← hkey] at h1
    rw [hsi2]
    exact h1
  have hs1 : sX i = 𝟙 (X i) ≫ sX i := (Category.id_comp _).symm
  have hs1' : ι ≫ sX i = ι ≫ 𝟙 (X i) ≫ sX i := by rw [Category.id_comp]
  have hs2 : ι ≫ sX i = (ι ≫ 𝟙 (X i)) ≫ sX i := by simp
  obtain ⟨ρ1, hρ1⟩ := exists_heq_rationalPluriForms hs1' (c₀ • θm)
  obtain ⟨X1, hX1⟩ := exists_heq_rationalPluriForms hs2 (c₀ • θm)
  have hrec : ∀ ω : logPluricanonicalSections (sX i) 3 m (B i),
      IsPoincareResidue (sX i) ι 2 m (ω : RationalPluriForms (sX i) 3 m) (c₀ • θm) →
      IsIteratedResidueRec (ω : RationalPluriForms (sX i) 3 m) (.step (.refl h) ι BT hι) 2 X1 := by
    intro ω hω
    obtain ⟨ρ0, hρ0⟩ := exists_heq_rationalPluriForms hs1 (ω : RationalPluriForms (sX i) 3 m)
    exact ⟨ρ0, ⟨rfl, hρ0.symm⟩, ρ1, IsPoincareResidue.congr_structure hs1 hω hρ0 hρ1,
      hX1.symm.trans hρ1⟩
  rw [IsIteratedResidueRec.unique _ (R.isIteratedResidue i _ 2 u hdT).rec' (hrec u hRu1),
    IsIteratedResidueRec.unique _ (R.isIteratedResidue i _ 2 (s i) hdT).rec' (hrec (s i) hRs1)]

/-- The floor-divisor comparison when the valuation of the floor divisor `P` of `X_i` is carried
by `σ` to the valuation of a divisor `D` exceptional over `X_j`. Write `w = σ^* s_j - s_i`; the
residue of `w` along `P` vanishes once `ord_P w ≥ 1 - m`, and `ord_P w = ord_D w'` for
`w' = s_j - σ⁻¹^* s_i`. If a coefficient-one prime `L` of `X_j` through the centre of `D` is not
exceptional over `X_i`, the comparison along `L` for `σ⁻¹` gives `ord_L w' ≥ 1 - m`, and this
vanishing passes to `D`, whose discrepancy is `-1`. -/
private theorem toFun_step_refl_eq_of_isExceptional (hn : n ≤ 3)
    (R : ResidueRestriction sX B n m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {s : ∀ l, logPluricanonicalSections (sX l) n m (B l)} (hs : s ∈ preadmissibleSections R)
    (u : logPluricanonicalSections (sX i) n m (B i))
    (hu : (u : RationalPluriForms (sX i) n m) = pluriformPullback (sX i) (sX j) σ.toHom n m (s j))
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) (e : ℕ)
    (he : topologicalKrullDim T = e) [IsIntegral T] (P : MMP.Mori.PrimeDivisor (X i))
    (hP : ι (genericPoint T) = P.genericPoint) (hP1 : 1 ≤ (B i).coeff P)
    (hrange : Set.range ι.base = (P.support : Set (X i))) (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) (hD : D.IsExceptional)
    {n' : ℕ} {c : ℚ} (hc : c = -(B i).coeff P)
    (hDlog : MMP.Intersection.IsLogDiscrepancy (sX j) n' (QDivisor.toRDivisor (B j)) D (1 + c)) :
    R.toFun i (.step (.refl h) ι BT hι) e u = R.toFun i (.step (.refl h) ι BT hι) e (s i) := by
  by_cases h2 : n = 2
  · subst h2
    exact (MMP.Fourfold.ResidueRestriction.exists_preadmissible_pluriformPullback_and_toFun_eq R
      (fun l => fun P => (R.setting.isDltPair l).1.2.1 P) σ hσ hs).2 u hu
      (.step (.refl h) ι BT hι) e (by simp [StratumAdjunctionData.length]) he
  have hPi := R.setting.isPair i
  have hPj := R.setting.isPair j
  have := hPi.isAlgClosed
  have := hPi.charZero
  have hX := hPi.isPair.1
  have hXj := hPj.isPair.1
  haveI : LocallyOfFiniteType (sX i) := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (sX j) := hXj.1.toLocallyOfFiniteType
  letI := functionFieldAlgebra (sX i)
  letI := functionFieldAlgebra (sX j)
  obtain ⟨K', hK', hmK'⟩ := exists_canonical_cartier R j
  have hnn : n' = n := by
    have := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hDlog).symm.trans
      (R.setting.topologicalKrullDim_eq j)
    exact_mod_cast this
  rw [hnn] at hDlog
  have hP1' : (B i).coeff P = 1 := le_antisymm ((R.setting.isDltPair i).2.1 P) hP1
  -- `D` has discrepancy `-1` over `(X_j, B_j)`
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPj.isPair hK' D
  have h1 := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha hDlog
  have hac : a = -1 := by
    have : a = c := by exact_mod_cast (by linarith : (a : ℝ) = c)
    rw [this, hc, hP1']
  rw [hac] at ha
  have hni := R.setting.topologicalKrullDim_eq i
  have hnj := R.setting.topologicalKrullDim_eq j
  have hn1 : e + 1 = n := by
    have := (StratumAdjunctionData.step (.refl h) ι BT hι).dim_add_length hni he
    simpa [StratumAdjunctionData.length] using this
  have he0 : 0 < e := by
    have := two_le_of_isExceptional hXj hnj hD
    omega
  -- snc coordinates at the centre of `D`
  have hm0' : (m : ℤ) ≠ 0 := by exact_mod_cast R.setting.pos.ne'
  obtain ⟨cc, z, L, α, hz, hL, hLx, hLz, hBL, hL1, hsm, hα, hzv, hmono⟩ :=
    exists_sncCoordinates_of_isDiscrepancy_neg_one (R.setting.isDltPair j)
      ⟨hXj, hK', ⟨_, hm0', hmK'⟩⟩ D hDlog.2.1 ha
  by_cases hc3 : cc = 3
  · subst hc3
    obtain rfl : n = 3 := by omega
    let u' : logPluricanonicalSections (sX j) 3 m (B j) :=
      ⟨_, pluriformPullback_mem_logPluricanonicalSections R σ.symm hσ.symm (s i)⟩
    have hσσ : pluriformPullback (sX i) (sX j) σ.toHom 3 m (u' : RationalPluriForms (sX j) 3 m) =
        (s i : RationalPluriForms (sX i) 3 m) := by
      have e1 := pluriformPullback_comp (sX := sX i) (sX' := sX j) (sX'' := sX i) hni hnj hni m
        σ.toHom (FunctionFieldEquiv.toHom (sX j) (sX i) σ.symm)
        (s i : RationalPluriForms (sX i) 3 m)
      have e2 : (σ.toHom).comp (FunctionFieldEquiv.toHom (sX j) (sX i) σ.symm) =
          FunctionFieldEquiv.toHom (sX i) (sX i) 1 := by
        ext a
        exact σ.apply_symm_apply a
      rw [e2, pluriformPullback_one hni] at e1
      exact e1
    exact toFun_step_refl_eq_of_isExceptional_of_point R σ hσ hs u hu u' hσσ h hι e he P hP hP1'
      hrange D hDv z L α hz hL hLx hLz hBL hL1 hsm hα hzv hmono
  -- the centre is a curve
  have hcc : cc = 2 := by
    have h1 := hz.2
    rw [ringKrullDim_stalk_eq_coheight] at h1
    have h2 : ((Order.coheight (D.f D.E.genericPoint) : ℕ∞) : WithBot ℕ∞) =
        ((cc : ℕ∞) : WithBot ℕ∞) := h1
    have hc : Order.coheight (D.f D.E.genericPoint) = cc := WithBot.coe_injective h2
    have h3 := (MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight
      hXj D).mp hD
    have h4 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (sX j)
      (D.f D.E.genericPoint)
    rw [hnj] at h4
    have h0 : 0 ≤ topologicalKrullDim (closure {D.f D.E.genericPoint} : Set (X j)) :=
      Order.krullDim_nonneg_iff.mpr ⟨⟨closure {⟨_, subset_closure rfl⟩},
        isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have h5 : ((Order.coheight (D.f D.E.genericPoint) : ℕ∞) : WithBot ℕ∞) ≤ n :=
      h4 ▸ le_add_of_nonneg_left h0
    rw [hc] at h3 h5
    have h6 : cc ≤ n := by exact_mod_cast (WithBot.coe_le_coe.mp h5)
    have h7 : 2 ≤ cc := by exact_mod_cast h3
    omega
  subst hcc
  obtain rfl : n = 3 := by omega
  let u' : logPluricanonicalSections (sX j) 3 m (B j) :=
    ⟨_, pluriformPullback_mem_logPluricanonicalSections R σ.symm hσ.symm (s i)⟩
  have hσσ : pluriformPullback (sX i) (sX j) σ.toHom 3 m (u' : RationalPluriForms (sX j) 3 m) =
      (s i : RationalPluriForms (sX i) 3 m) := by
    have e1 := pluriformPullback_comp (sX := sX i) (sX' := sX j) (sX'' := sX i) hni hnj hni m
      σ.toHom (FunctionFieldEquiv.toHom (sX j) (sX i) σ.symm)
      (s i : RationalPluriForms (sX i) 3 m)
    have e2 : (σ.toHom).comp (FunctionFieldEquiv.toHom (sX j) (sX i) σ.symm) =
        FunctionFieldEquiv.toHom (sX i) (sX i) 1 := by
      ext a
      exact σ.apply_symm_apply a
    rw [e2, pluriformPullback_one hni] at e1
    exact e1
  exact toFun_step_refl_eq_of_isExceptional_of_curve R σ hσ hs u hu u' hσσ h hι e he P hP hP1'
    hrange D hDv z L α hz hL hLx hLz hBL hL1 hsm hα hzv hmono

/-- **Crepant pull-back does not change residues along floor divisors.** If `s` is
preadmissible and `u = σ^* s_j` for a crepant birational map `σ : (X_i, B_i) ⇢ (X_j, B_j)`, then
the residues of `u` and of `s_i` along every component of `⌊B_i⌋` (a flag of length one) agree. -/
private theorem toFun_step_refl_eq_of_eq_pluriformPullback (hn : n ≤ 3)
    (R : ResidueRestriction sX B n m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {s : ∀ l, logPluricanonicalSections (sX l) n m (B l)} (hs : s ∈ preadmissibleSections R)
    (u : logPluricanonicalSections (sX i) n m (B i))
    (hu : (u : RationalPluriForms (sX i) n m) = pluriformPullback (sX i) (sX j) σ.toHom n m (s j))
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) (e : ℕ)
    (he : topologicalKrullDim T = e) :
    R.toFun i (.step (.refl h) ι BT hι) e u = R.toFun i (.step (.refl h) ι BT hι) e (s i) := by
  have hPi := R.setting.isPair i
  have := hPi.isAlgClosed
  have := hPi.charZero
  have hX := hPi.isPair.1
  have hXj := (R.setting.isPair j).isPair.1
  obtain ⟨K, hK, -⟩ := exists_canonical_cartier R i
  haveI : IsIntegral T := hι.1.1.toIsIntegral
  obtain ⟨-, P, hP1, hrange, -⟩ := id hι
  have hP := map_genericPoint_eq_of_range_eq ι P hrange
  set DΓ := DivisorOver.ofPrimeDivisor k hX P
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPi.isPair hK DΓ
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
    (show IsProper (𝟙 (X i)) by infer_instance)
  obtain ⟨n', D, hDv, hDlog⟩ := (hσ DΓ.valuation (1 + c)).mp ⟨n, DΓ, rfl, hlog⟩
  have hv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g) := by
    intro g
    rw [hDv]
    change P.divisorialValuation (functionFieldMap (𝟙 (X i)) _) = _
    rw [functionFieldMap_id_apply]
    rfl
  by_cases hD : D.IsExceptional
  · exact toFun_step_refl_eq_of_isExceptional hn R σ hσ hs u hu h hι e he P hP hP1 hrange D hv hD
      (hc.eq_neg_coeff_of_ofPrimeDivisor hX) hDlog
  · obtain ⟨P', hP'⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hXj D hD
    refine toFun_step_refl_eq_of_divisorialValuation_eq hn R σ hσ hs u hu h hι e he P hP hP1 hrange P'
      fun g => ?_
    rw [← hv, hP']
    change _ = P'.divisorialValuation (functionFieldMap (𝟙 (X j)) g)
    rw [functionFieldMap_id_apply]

/-- **Crepant pull-back does not change proper-stratum residues.** If `s` is preadmissible and
`u = σ^* s_j` for a crepant birational map `σ : (X_i, B_i) ⇢ (X_j, B_j)`, then the iterated
residues of `u` and of `s_i` along every flag of positive length agree. -/
private theorem toFun_eq_of_eq_pluriformPullback (hn : n ≤ 3) (R : ResidueRestriction sX B n m)
    {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {s : ∀ l, logPluricanonicalSections (sX l) n m (B l)} (hs : s ∈ preadmissibleSections R)
    (u : logPluricanonicalSections (sX i) n m (B i))
    (hu : (u : RationalPluriForms (sX i) n m) = pluriformPullback (sX i) (sX j) σ.toHom n m (s j))
    {S : Scheme.{0}} {ι : S ⟶ X i} {BS : QDivisor S}
    (F : StratumAdjunctionData (sX i) (B i) ι BS) (e : ℕ) (hF : 0 < F.length)
    (he : topologicalKrullDim S = e) :
    R.toFun i F e u = R.toFun i F e (s i) := by
  haveI := F.isIntegral_stratum
  have hdiff := eq_zero_of_isIteratedResidueRec R i (u - s i)
    (fun h hι e' he' => by
      rw [map_sub, toFun_step_refl_eq_of_eq_pluriformPullback hn R σ hσ hs u hu h hι e' he',
        sub_self])
    F hF (R.isIteratedResidue i F e (u - s i) he).rec'
  rw [map_sub] at hdiff
  exact sub_eq_zero.mp hdiff

/-- Changing one entry of a preadmissible system without changing its proper-stratum residues
gives a preadmissible system. -/
private theorem update_mem_preadmissibleSections [DecidableEq I] (R : ResidueRestriction sX B n m)
    {s : ∀ l, logPluricanonicalSections (sX l) n m (B l)} (hs : s ∈ preadmissibleSections R)
    (i : I) (u : logPluricanonicalSections (sX i) n m (B i))
    (hu : ∀ {S : Scheme.{0}} {ι : S ⟶ X i} {BS : QDivisor S}
      (F : StratumAdjunctionData (sX i) (B i) ι BS) (e : ℕ), 0 < F.length →
      topologicalKrullDim S = e → R.toFun i F e u = R.toFun i F e (s i)) :
    Function.update s i u ∈ preadmissibleSections R := by
  have key : ∀ (l : I) {S : Scheme.{0}} {ι : S ⟶ X l} {BS : QDivisor S}
      (F : StratumAdjunctionData (sX l) (B l) ι BS) (e : ℕ), 1 ≤ F.length →
      topologicalKrullDim S = e →
      R.toFun l F e (Function.update s i u l) = R.toFun l F e (s l) := by
    intro l S ι BS F e hF he
    by_cases hl : l = i
    · subst hl
      rw [Function.update_self]
      exact hu F e hF he
    · rw [Function.update_of_ne hl]
  intro l l' S S' ι ι' BS BS' F F' e h₁ h₂ h₃ h₄ σ hσ
  rw [key l F e h₁ h₃, key l' F' e h₂ h₄]
  exact hs l l' F F' e h₁ h₂ h₃ h₄ σ hσ

private theorem solution :
    ∀ {k : Type} [Field k] {I : Type*} {X : I → Scheme.{0}} {sX : ∀ i, X i ⟶ Spec (.of k)}
    [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    (B : ∀ i, QDivisor (X i)) {n : ℕ} (hn : n ≤ 3),
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, m₀ ∣ m → ∀ R : ResidueRestriction sX B n m,
      (∀ (i j : I) (σ : FunctionFieldEquiv (sX i) (sX j)),
        IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ →
        ∀ s ∈ preadmissibleSections R, ∃ t ∈ preadmissibleSections R,
          ((t i : logPluricanonicalSections (sX i) n m (B i)) :
              Mori.RationalPluriForms (sX i) n m) =
            pluriformPullback (sX i) (sX j) σ.toHom n m (s j) ∧ ∀ l, l ≠ i → t l = s l) ∧
      (∀ (i j : I) (σ : FunctionFieldEquiv (sX i) (sX j)),
        IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ →
        ∀ s ∈ preadmissibleSections R, ∀ t ∈ preadmissibleSections R,
          ((t i : logPluricanonicalSections (sX i) n m (B i)) :
              Mori.RationalPluriForms (sX i) n m) =
            pluriformPullback (sX i) (sX j) σ.toHom n m (s j) →
          ∀ {S : Scheme.{0}} {ι : S ⟶ X i} {BS : QDivisor S}
            (F : StratumAdjunctionData (sX i) (B i) ι BS) (e : ℕ), 0 < F.length →
            topologicalKrullDim S = e → R.toFun i F e (t i) = R.toFun i F e (s i)) := by
  intro k _ I X sX _ _ _ B n hn
  classical
  refine ⟨1, one_pos, fun m _ R => ⟨?_, ?_⟩⟩
  · intro i j σ hσ s hs
    let u : logPluricanonicalSections (sX i) n m (B i) :=
      ⟨_, pluriformPullback_mem_logPluricanonicalSections R σ hσ (s j)⟩
    refine ⟨Function.update s i u, update_mem_preadmissibleSections R hs i u
      (fun F e hF he => toFun_eq_of_eq_pluriformPullback hn R σ hσ hs u rfl F e hF he), ?_,
      fun l hl => Function.update_of_ne hl _ _⟩
    rw [Function.update_self]
  · intro i j σ hσ s hs t _ ht S ι BS F e hF he
    exact toFun_eq_of_eq_pluriformPullback hn R σ hσ hs (t i) ht F e hF he

end

end Proof_lem_fourfold_preadmissible_stratum_restrictions_fixed

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

/-- **Crepant birational identifications preserve preadmissible systems and fix their
proper-stratum restrictions.** For a finite collection of projective rational dlt pairs
`(X_i, B_i)` of dimension `n ≤ 3`, there is `m₀ > 0` with the following property for every
residue-restriction datum `R` in a degree `m` divisible by `m₀`. Let
`σ : (X_i, B_i) ⇢ (X_j, B_j)` be a crepant birational map (`MMP.Fourfold.IsCrepantBirationalMap`)
and `s ∈ preadmissibleSections R`.
* Replacing the `i`-th entry of `s` by `σ^* s_j` gives a preadmissible system.
* For every preadmissible system `t` with `t_i = σ^* s_j`, and every flag `F` of positive length
  with final stratum `S`, the residue restrictions satisfy `t_i|_S = s_i|_S` in degree
  `dim S`. -/
@[mmp "lem_fourfold_preadmissible_stratum_restrictions_fixed"]
public theorem exists_preadmissibleSections_update_pluriformPullback_of_isCrepantBirationalMap
    {k : Type} [Field k] {I : Type*} {X : I → Scheme.{0}} {sX : ∀ i, X i ⟶ Spec (.of k)}
    [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    (B : ∀ i, QDivisor (X i)) {n : ℕ} (hn : n ≤ 3) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, m₀ ∣ m → ∀ R : ResidueRestriction sX B n m,
      (∀ (i j : I) (σ : FunctionFieldEquiv (sX i) (sX j)),
        IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ →
        ∀ s ∈ preadmissibleSections R, ∃ t ∈ preadmissibleSections R,
          ((t i : logPluricanonicalSections (sX i) n m (B i)) :
              Mori.RationalPluriForms (sX i) n m) =
            pluriformPullback (sX i) (sX j) σ.toHom n m (s j) ∧ ∀ l, l ≠ i → t l = s l) ∧
      (∀ (i j : I) (σ : FunctionFieldEquiv (sX i) (sX j)),
        IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ →
        ∀ s ∈ preadmissibleSections R, ∀ t ∈ preadmissibleSections R,
          ((t i : logPluricanonicalSections (sX i) n m (B i)) :
              Mori.RationalPluriForms (sX i) n m) =
            pluriformPullback (sX i) (sX j) σ.toHom n m (s j) →
          ∀ {S : Scheme.{0}} {ι : S ⟶ X i} {BS : QDivisor S}
            (F : StratumAdjunctionData (sX i) (B i) ι BS) (e : ℕ), 0 < F.length →
            topologicalKrullDim S = e → R.toFun i F e (t i) = R.toFun i F e (s i)) :=
  Proof_lem_fourfold_preadmissible_stratum_restrictions_fixed.solution B hn

end MMP.Fourfold
