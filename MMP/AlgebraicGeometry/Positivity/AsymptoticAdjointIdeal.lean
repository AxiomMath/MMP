module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.AdjointIdeal.ReducedSncBoundary
public import MMP.RingTheory.Kaehler.PluriformProduct
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
import MMP.AlgebraicGeometry.MMP.Fourfold.PairSingularities
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.EffectiveIdealSheaf
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Singularities.Adjunction.PoincareResidueSmoothDivisor
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Local
import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations
import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
import MMP.AlgebraicGeometry.Resolution.Surface.FamilyBettiBound
import MMP.AlgebraicGeometry.Analytic.AnalyticMapOpenSubscheme
import MMP.AlgebraicGeometry.Analytic.PluriformIntegrableGauge
import MMP.AlgebraicGeometry.Analytic.FiniteCochainsBetti
import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Projective
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
import MMP.AlgebraicGeometry.Singularities.CyclicCover.Divisorial
import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.Divisor.SmallModelPushforward
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
public import MMP.AlgebraicGeometry.Morphisms.HProjective

/-!
# Asymptotic adjoint ideals and cyclic covers of subklt surface pluriforms

Let `f : X ⟶ Z` be projective, `X` smooth over an algebraically closed field of characteristic
zero, `Z` affine, `Δ` a reduced snc divisor and `V_•` a graded linear series of a Cartier divisor
`D`. The asymptotic adjoint ideal `𝒥_{Δ,cV_•} = ⋃_{p ∈ bℤ_{>0}} 𝒥_{Δ,(c/p)V_p}` is a coherent
ideal sheaf equal to a single term `𝒥_{Δ,(c/p)V_p}` for `p` divisible enough, and it decreases as
`c` and `Δ` increase. If the stable base locus of `D` contains no stratum of `Δ` and `S` is a
component of `Δ`, restrictions to `S` of sections of `𝒪_X(D)` are sections of
`𝒥_{Θ,‖D‖_S} ⊗ 𝒪_S(D|_S)`, `Θ = (Δ - S)|_S`.

Let `X` be a smooth projective complex surface, `B` an snc `ℚ`-divisor with coefficients less than
one and `m > 0` with `mB` integral. For `s = f η^{⊗m} ∈ H⁰(X, m(K_X + B))` nonzero, the cyclic
covers `z^m = f` have resolutions `Y_s` of uniformly bounded second Betti number, on which the
root form `z · p^*η` is a holomorphic two-form with `m`-th power `p^* s`.

## Main results

* `MMP.Fourfold.isAsymptoticAdjointIdeal_operations`: `𝒥_{Δ,cV_•}` is coherent and equals one
  term `𝒥_{Δ,(c/p)V_p}`, it decreases in `(Δ, c)`, and it bounds restrictions to a component `S`.
* `MMP.Fourfold.exists_cyclicCover_resolution_finrank_le`: the resolved cyclic covers `z^m = f`
  of subklt surface pluriforms have uniformly bounded second Betti number.
* `MMP.Mori.PrimeDivisor.ord_restrict_eq_sum_intersectionLength_mul_ord`: the order along a
  prime divisor `Q` of a smooth `T ⊆ X` of the restriction of `u` is `∑_E length_Q(E) · ord_E(u)`.

## Implementation notes

* Ideals are subsets of `K(X)` given by their sections over the opens; coherence is: regular
  functions, given on non-empty affine opens by one `AlgebraicGeometry.Scheme.IdealSheafData`.
  The restriction to `S` uses a representative of `D` with `D.coeff S = 0`.
* The adjoint ideal of a linear series is described by orders along *all* divisors `G` over `X`:
  `g` is a section over `U` when for every `G` centred in `U`, with `a = a(G, X, Δ)`, some nonzero
  `g' ∈ V` and `w ≥ ord_G(g') + ord_G(D)` give `v_G(g) ≤ exp (⌈a - c w⌉ - 1 + [a = 0])`. This
  replaces the source's common resolutions; stabilization follows along `p = b · m!` from
  Noetherianity on a finite affine cover.
* `Y_s` is given by its components `Yᵢ`, dominating `X`. Being a resolution of the cyclic cover is
  stated on generic algebras: `k(X)[z]/(z^m - f) ≅ ∏ᵢ k(Yᵢ)`, `z ↦ (zᵢ)`, `ωᵢ = zᵢ · pᵢ^*η`.
  Holomorphic two-forms are `MMP.Fourfold.logPluricanonicalSections (pᵢ ≫ s_X) 2 1 0`.
* Holomorphy of the root form is proved by orders along prime divisors, not by square
  integrability: in snc coordinates `s = g (dw₁ ∧ dw₂)^{⊗m}` with `g ∏ w_j^{m-1}` regular, so
  `ord_Γ(p^* s) ≥ 1 - m`. The bounded family is a finite union of divisorial cyclic covers over
  affine spaces `𝔸^r_ℂ` of affine families of rational functions.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][kollar-mori], § 2.4, § 5.2.
-/

universe u

/-! ## Asymptotic adjoint ideals -/

section AsymptoticAdjointIdeal

open CategoryTheory AlgebraicGeometry TopologicalSpace Pointwise MMP.Mori

namespace MMP.Fourfold

/-! ### Log discrepancies under adding a Cartier divisor, and valuative bounds -/

section Toolkit

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- Adding `c • C` to the boundary, for a Cartier divisor `C` with pull-back `C'` along the model,
lowers a log discrepancy by `c` times the coefficient of `C'` along the divisor. -/
private theorem isLogDiscrepancy_add_smul {n : ℕ} {B : RDivisor X} {F : DivisorOver k sX}
    {a : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B F a) {C : Divisor X}
    (hC : C.IsCartier) (c : ℝ) :
    haveI := F.isLocallyNoetherian
    haveI := F.isNormal
    ∀ (C' : Divisor F.Y) (hCs : ∀ Z : irreducibleComponents F.Y,
        F.f (componentGenericPoint F.Y Z) ∉ C.supp), C.IsPullback F.f hCs C' →
      MMP.Intersection.IsLogDiscrepancy sX n (B + c • Divisor.toRDivisor C) F
        (a - c * (C'.coeff F.E : ℝ)) := by
  classical
  intro C' hCs hC'
  obtain ⟨hnv, hprop, ω, hω0, hK, m, r, C₁, C₁', hC₁, hrel, hpb, ha⟩ := h
  refine ⟨hnv, hprop, ω, hω0, hK, m + 1, Fin.snoc r c, Fin.snoc C₁ C, Fin.snoc C₁' C', ?_, ?_,
    ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hC
    · simpa using hC₁ j
  · intro Γ
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, DivisorWithCoeffs.coeff_add, ← hrel Γ,
      DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
    ring
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · refine ⟨by simpa using hCs, ?_⟩
      simpa using hC'
    · simpa using hpb j
  · rw [Fin.sum_univ_castSucc, ha]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring

/-- **A valuative bound from orders near the centre.** If `ord_Γ(g) ≥ coeff_Γ(C)` along every
prime divisor `Γ` through the centre of `F`, for a Cartier divisor `C` with pull-back `C'`, then
`v_F(g) ≤ exp (-coeff_F(C'))`. -/
private theorem valuation_le_exp_of_isPullback {F : DivisorOver k sX} {C : Divisor X}
    (hC : C.IsCartier) {g : X.functionField}
    (hg : ∀ Γ : MMP.Mori.PrimeDivisor X, F.f F.E.genericPoint ∈ Γ.support →
      Γ.divisorialValuation g ≤ WithZero.exp (-C.coeff Γ)) :
    haveI := F.isLocallyNoetherian
    haveI := F.isNormal
    ∀ (C' : Divisor F.Y) (hCs : ∀ Z : irreducibleComponents F.Y,
        F.f (componentGenericPoint F.Y Z) ∉ C.supp), C.IsPullback F.f hCs C' →
      F.valuation g ≤ WithZero.exp (-C'.coeff F.E) := by
  intro C' hCs hC'
  have := F.isIntegral
  have := F.isLocallyNoetherian
  have := F.isNormal
  have := F.isDominant
  rcases eq_or_ne g 0 with rfl | hg0
  · simp
  set x := F.f F.E.genericPoint with hx
  obtain ⟨U, hxU, φ, hφ⟩ := hC x
  let Z0 : irreducibleComponents X := MMP.Mori.pointComponent x
  set h := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : MMP.Mori.RationalFunctions X) with hhdef
  have hh : h ≠ 0 := (φ.isUnit.map _).ne_zero
  have hcoef := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hC' hφ F.E hxU Z0
  have hordh : ∀ Γ : MMP.Mori.PrimeDivisor X, x ∈ Γ.support →
      X.ord h Γ.genericPoint = C.coeff Γ := by
    intro Γ hΓ
    rw [hφ Γ ⟨x, hΓ, hxU⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
    rw [show Γ.component = Z0 from
      Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _]
  have hg' : g * h ^ (-1 : ℤ) ≠ 0 := mul_ne_zero hg0 (zpow_ne_zero _ hh)
  have hord : ∀ Γ : MMP.Mori.PrimeDivisor X, x ∈ Γ.support →
      0 ≤ X.ord (g * h ^ (-1 : ℤ)) Γ.genericPoint := by
    intro Γ hΓ
    have h1 := hg Γ hΓ
    rw [Γ.divisorialValuation_eq_exp_neg_ord hg0, WithZero.exp_le_exp] at h1
    rw [Scheme.ord_mul hg0 (zpow_ne_zero _ hh), MMP.Mori.ord_zpow _ hh, hordh Γ hΓ]
    omega
  obtain ⟨r, hr⟩ :=
    MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg x hg' hord
  have hY0 := MMP.Threefold.Mori.Helpers.ord_functionFieldMap_nonneg F hg' r hr
  have hfg : functionFieldMap F.f g ≠ 0 := (map_ne_zero _).mpr hg0
  have hfh : functionFieldMap F.f h ≠ 0 := (map_ne_zero _).mpr hh
  rw [map_mul, map_zpow₀, Scheme.ord_mul hfg (zpow_ne_zero _ hfh), MMP.Mori.ord_zpow _ hfh]
    at hY0
  change F.E.divisorialValuation (functionFieldMap F.f g) ≤ _
  rw [F.E.divisorialValuation_eq_exp_neg_ord hfg, WithZero.exp_le_exp, hcoef, ← hhdef]
  omega

/-- Log discrepancies exist on a smooth variety, at the index `n = dim X`. -/
private theorem exists_isLogDiscrepancy [PerfectField k] (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} (hn : topologicalKrullDim X = n) (B : QDivisor X)
    (F : DivisorOver k sX) (hF : IsProper F.f) :
    ∃ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) F a := by
  haveI : MMP.Mori.IsVariety k sX := hX.1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme sX hsm hn
  have hP : MMP.Mori.IsPair sX B :=
    ⟨hX, n, K, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK F
  exact ⟨_, MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hF⟩

/-- The pull-back of a Cartier divisor which is effective near the centre of `F` has a
nonnegative coefficient along `F`. -/
private theorem coeff_isPullback_nonneg {F : DivisorOver k sX} {C : Divisor X}
    (hC : C.IsCartier)
    (hC0 : ∀ Γ : MMP.Mori.PrimeDivisor X, F.f F.E.genericPoint ∈ Γ.support → 0 ≤ C.coeff Γ) :
    haveI := F.isLocallyNoetherian
    haveI := F.isNormal
    ∀ (C' : Divisor F.Y) (hCs : ∀ Z : irreducibleComponents F.Y,
        F.f (componentGenericPoint F.Y Z) ∉ C.supp), C.IsPullback F.f hCs C' →
      0 ≤ C'.coeff F.E := by
  intro C' hCs hC'
  have := F.isIntegral
  have := F.isLocallyNoetherian
  have := F.isNormal
  have := F.isDominant
  have hn := hC'.zsmul hC (-1)
    (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp F.f _)
  have h1 := valuation_le_exp_of_isPullback (F := F) (hC.zsmul (-1)) (g := 1) (fun Γ hΓ => by
      rw [map_one, DivisorWithCoeffs.coeff_smul, smul_eq_mul, neg_one_mul, neg_neg,
        ← WithZero.exp_zero, WithZero.exp_le_exp]
      exact hC0 Γ hΓ) _ _ hn
  rwa [map_one, DivisorWithCoeffs.coeff_smul, smul_eq_mul, neg_one_mul, neg_neg,
    ← WithZero.exp_zero, WithZero.exp_le_exp] at h1

/-- The inclusion of an open subscheme `U` is biregular over `U`. -/
private theorem isBiregular_ι_self {W : Scheme.{u}} (U : W.Opens) : IsBiregular U.ι U := by
  have h1 : U.ι ∣_ U = (U.ι ⁻¹ᵁ U).ι := by
    rw [← cancel_mono U.ι, morphismRestrict_ι]
  show IsIso (U.ι ∣_ U)
  rw [h1, U.ι_preimage_self, isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun y => ?_⟩⟩
  change y ∈ Set.range (⊤ : U.toScheme.Opens).ι
  rw [Scheme.Opens.range_ι]
  trivial

/-- On the open `W° = sncComplement T S`, a reduced effective divisor `T` restricts to the sum of
its components containing `S`. -/
private theorem toRDivisor_restrictOpen_sncComplement {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {T : Divisor W}
    (hT : MMP.Intersection.IsReducedEffective T) (S : Set W) :
    QDivisor.toRDivisor ((Divisor.toQDivisor T).restrictOpen (sncComplement T S)) =
      Divisor.toRDivisor (inverseTransformDivisor (sncComplement T S).ι
        (MMP.Intersection.reducedDivisorOf (sncIndexSet T S))) := by
  classical
  set U := sncComplement T S
  have hbireg : ∀ y : U.toScheme, U.ι y ∈ biregularLocus U.ι :=
    fun y => le_biregularLocus (isBiregular_ι_self U) y.2
  refine Finsupp.ext fun F => ?_
  set P := OpenWeilRestriction.primeDivisorMap U.ι F with hPdef
  have hinv : inverseTransformPrimeDivisor U.ι P = some F :=
    MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι F).symm (hbireg _)
  have huniq : ∀ P'', inverseTransformPrimeDivisor U.ι P'' = some F → P'' = P := by
    intro P'' hP''
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    rw [hPdef, OpenWeilRestriction.genericPoint_primeDivisorMap]
    exact (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
      hP'').1.symm
  have e1 : (QDivisor.toRDivisor ((Divisor.toQDivisor T).restrictOpen U)) F =
      ((T P : ℤ) : ℝ) := by
    change (((T P : ℤ) : ℚ) : ℝ) = _
    push_cast
    rfl
  have e2 : (Divisor.toRDivisor (inverseTransformDivisor U.ι
      (MMP.Intersection.reducedDivisorOf (sncIndexSet T S)))) F =
      (((MMP.Intersection.reducedDivisorOf (sncIndexSet T S)) P : ℤ) : ℝ) := by
    change ((DivisorWithCoeffs.mapPrimeDivisors (inverseTransformPrimeDivisor U.ι) _ F : ℤ) : ℝ) = _
    rw [MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hinv huniq]
  rw [e1, e2]
  congr 1
  have hc' := MMP.Intersection.coeff_reducedDivisorOf (sncIndexSet T S) P
  rw [DivisorWithCoeffs.coeff_apply] at hc'
  rw [hc']
  have hPU : P.genericPoint ∈ U := by
    rw [hPdef, OpenWeilRestriction.genericPoint_primeDivisorMap]
    exact F.genericPoint.2
  have hPmem := MMP.Flips.primeDivisor_genericPoint_mem_support P
  have hmem : ∀ E ∈ T.support, ¬ S ⊆ E.support → P.genericPoint ∉ E.support := by
    have : P.genericPoint ∈ (sncComplement T S : Set W) := hPU
    simpa [sncComplement] using this
  by_cases hPT : P ∈ T.support
  · have hPJ : P ∈ sncIndexSet T S := by
      refine Finset.mem_filter.2 ⟨hPT, ?_⟩
      by_contra hZP
      exact hmem P hPT hZP hPmem
    rw [if_pos hPJ]
    have hT1 : T.coeff P = 1 := (hT P).resolve_left (Finsupp.mem_support_iff.1 hPT)
    rwa [DivisorWithCoeffs.coeff_apply] at hT1
  · have hPJ : P ∉ sncIndexSet T S := fun h => hPT (Finset.mem_filter.1 h).1
    rw [if_neg hPJ]
    exact Finsupp.notMem_support_iff.1 hPT

open Classical in
/-- If the coheight of `x` is at most the number of components of a reduced snc divisor `Δ`
containing `closure {x}`, then `closure {x}` is a stratum of `Δ`. -/
private theorem isSNCStratum_closure_of_coheight_le_card {Δ : Divisor X}
    (hΔ : IsReducedSNC sX Δ) {x : X} {m₀ : ℕ} (hcx : Order.coheight x = m₀)
    (hcJ : m₀ ≤ (sncIndexSet Δ (closure {x})).card) : IsSNCStratum Δ (closure {x}) := by
  set J := sncIndexSet Δ (closure {x}) with hJdef
  refine ⟨J, Finset.filter_subset _ _, ⟨isIrreducible_singleton.closure, ?_⟩, ?_⟩
  · intro z hz
    simp only [Set.mem_iInter]
    intro E hE
    exact (Finset.mem_filter.1 hE).2 hz
  · rintro T' ⟨hT'irr, hT'sub⟩ hZT'
    have hWsub : closure T' ⊆ ⋂ E ∈ J, (E.support : Set X) := by
      refine closure_minimal hT'sub (isClosed_biInter fun E _ => ?_)
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure E]
      exact isClosed_closure
    obtain ⟨w, hw⟩ := QuasiSober.sober hT'irr.closure isClosed_closure
    have hxw : w ⤳ x := hw.specializes (subset_closure (hZT' (subset_closure rfl)))
    have hwmem : w ∈ closure T' := hw.mem
    obtain ⟨mw, zw, jw, hzw, hjw, -⟩ := hΔ.2.2 w
    have hJw : J.card ≤ mw := by
      let ι : J → Fin mw := fun E => jw ⟨E.1, (Finset.mem_filter.1 E.2).1, by
        have := hWsub hwmem
        simp only [Set.mem_iInter] at this
        exact this E.1 E.2⟩
      have hι : Function.Injective ι := by
        intro E₁ E₂ h
        have h' := congrArg Subtype.val (hjw h)
        exact Subtype.ext (by simpa using h')
      simpa using Fintype.card_le_of_injective ι hι
    have hcw : Order.coheight w = mw := by
      exact_mod_cast (ringKrullDim_stalk_eq_coheight w).symm.trans hzw.2
    have hwx : w = x := by
      by_contra hne
      have hlt : x < w := lt_of_le_not_ge hxw (fun h => hne (hxw.antisymm h).eq)
      have h1 := Order.coheight_add_one_le hlt
      rw [hcw, hcx] at h1
      have h2 : mw + 1 ≤ m₀ := by exact_mod_cast h1
      omega
    have hcl : closure T' = closure {x} := by
      rw [← hw.def, hwx]
    exact (subset_closure).trans hcl.le

open Classical in
/-- A divisor over a reduced snc pair on a smooth variety with log discrepancy zero has reduced
snc discrepancy zero. -/
private theorem isReducedSNCDiscrepancy_of_isLogDiscrepancy_eq_zero [IsAlgClosed k] [CharZero k]
    (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) {Δ : Divisor X}
    (hΔ : IsReducedSNC sX Δ) {n : ℕ} {F : DivisorOver k sX}
    (h0 : MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) F 0) :
    IsReducedSNCDiscrepancy sX Δ F.valuation 0 := by
  haveI : MMP.Mori.IsVariety k sX := hX.1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hF : IsProper F.f := h0.2.1
  set x := F.f F.E.genericPoint with hxdef
  have hn := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq h0
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme sX hsm hn
  have hPW : MMP.Mori.IsPairWith sX n K (Divisor.toQDivisor Δ) :=
    ⟨hX, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPW.isPair hK F
  have h0' : MMP.Intersection.IsLogDiscrepancy sX n
      (QDivisor.toRDivisor (Divisor.toQDivisor Δ)) F 0 := by
    rwa [QDivisor.toRDivisor_toQDivisor]
  have hc1 : (0 : ℝ) = 1 + c :=
    MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc h0'
  set Z := F.center with hZdef
  have hZx : (Z : Set X) = closure {x} := F.center_eq_closure_genericPoint
  have hxZ : x ∈ (Z : Set X) := by
    rw [hZx]
    exact subset_closure rfl
  have hsuppZ : ∀ E : MMP.Mori.PrimeDivisor X, x ∈ E.support → (Z : Set X) ⊆ E.support := by
    intro E hxE
    rw [hZx, AlgebraicGeometry.PrimeDivisor.support_eq_closure E]
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure E] at hxE
    exact closure_minimal (Set.singleton_subset_iff.mpr hxE) isClosed_closure
  set U := sncComplement Δ (Z : Set X) with hUdef
  have hxU : x ∈ U := by
    change x ∈ (sncComplement Δ (Z : Set X) : Set X)
    simp only [sncComplement, TopologicalSpace.Opens.coe_mk, Set.mem_compl_iff,
      Set.mem_iUnion, Finset.mem_filter, not_exists, not_and]
    intro E hE hxE
    exact hE.2 (hsuppZ E hxE)
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  obtain ⟨hYU, hfU, E', -, hvU, hiff⟩ :=
    MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff hPW F U ⟨x, hxZ, hxU⟩
  have hcU := (hiff c).1 hc
  haveI : IsProper F.f := hF
  have hpU : IsProper (F.f ∣_ U) := inferInstance
  have hLU := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hcU hpU
  rw [toRDivisor_restrictOpen_sncComplement hΔ.1, ← hc1] at hLU
  have hcen : MMP.Intersection.IsCentre k sX F.valuation Z := ⟨F, hF, rfl, rfl⟩
  exact ⟨hX.1, hsm, hΔ.1, hΔ.2, Z, hcen, ⟨⟨x, hxU⟩⟩, n, _, hpU, hvU, hLU⟩

open Classical in
/-- **Zero places of a reduced snc pair have strata as centres.** If `Δ` is a reduced snc
divisor on a smooth variety and `a(F, X, Δ) = 0`, then the centre of `F` is a stratum of `Δ`;
hence its generic point lies outside every set which is stable under specialization and contains
no stratum of `Δ`. -/
private theorem notMem_of_isLogDiscrepancy_eq_zero [IsAlgClosed k] [CharZero k]
    (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) {Δ : Divisor X}
    (hΔ : IsReducedSNC sX Δ) {T : Set X} (hT : ∀ x ∈ T, closure {x} ⊆ T)
    (hns : ContainsNoStratum Δ T)
    {n : ℕ} {F : DivisorOver k sX}
    (h0 : MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) F 0) :
    F.f F.E.genericPoint ∉ T := by
  haveI : MMP.Mori.IsVariety k sX := hX.1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hF : IsProper F.f := h0.2.1
  have he := isReducedSNCDiscrepancy_of_isLogDiscrepancy_eq_zero hX hsm hΔ h0
  set x := F.f F.E.genericPoint with hxdef
  set Z := F.center with hZdef
  have hZx : (Z : Set X) = closure {x} := F.center_eq_closure_genericPoint
  have hcen : MMP.Intersection.IsCentre k sX F.valuation Z := ⟨F, hF, rfl, rfl⟩
  -- the codimension of the centre
  obtain ⟨m₀, z₀, j₀, hz₀, -, -⟩ := hΔ.2.2 x
  have hcx : Order.coheight x = m₀ := by
    exact_mod_cast (ringKrullDim_stalk_eq_coheight x).symm.trans hz₀.2
  have hc₀ : codimension Z = m₀ := by
    rw [hZdef, MMP.Positivity.DivisorOver.codimension_center, hcx]
  have hsub := IsReducedSNCDiscrepancy.sub_card_sncIndexSet_le he hcen hc₀
  have hcJ : m₀ ≤ (sncIndexSet Δ (Z : Set X)).card := by
    exact_mod_cast (show (m₀ : ℝ) ≤ (sncIndexSet Δ (Z : Set X)).card by linarith)
  -- the centre is a stratum
  have hstr : IsSNCStratum Δ (Z : Set X) := by
    rw [hZx] at hcJ ⊢
    exact isSNCStratum_closure_of_coheight_le_card hΔ hcx hcJ
  intro hxT
  refine hns _ hstr ?_
  rw [hZx]
  exact hT x hxT

/-- Adding `∑_{P ∈ s} c_P P` to the boundary on a smooth variety lowers a log discrepancy by
`∑_{P ∈ s} c_P e_P`, where `e_P` is the coefficient of the pull-back of `P` along the divisor. -/
private theorem isLogDiscrepancy_add_sum (hsm : IsSmoothScheme sX) {n : ℕ} {B : RDivisor X}
    {F : DivisorOver k sX} {a : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B F a)
    (s : Finset (MMP.Mori.PrimeDivisor X)) (c : MMP.Mori.PrimeDivisor X → ℝ)
    (e : MMP.Mori.PrimeDivisor X → ℤ)
    (he : haveI := F.isLocallyNoetherian
      haveI := F.isNormal
      ∀ P ∈ s, ∀ (P' : Divisor F.Y) (hB : ∀ Z : irreducibleComponents F.Y,
          F.f (componentGenericPoint F.Y Z) ∉
            DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor X)),
        Divisor.IsPullback F.f (Finsupp.single P 1 : Divisor X) hB P' → P'.coeff F.E = e P) :
    MMP.Intersection.IsLogDiscrepancy sX n
      (B + ∑ P ∈ s, c P • Divisor.toRDivisor (Finsupp.single P 1 : Divisor X)) F
      (a - ∑ P ∈ s, c P * e P) := by
  classical
  have := F.isLocallyNoetherian
  have := F.isNormal
  have := F.isIntegral
  have := F.isBirationalMorphism.isDominant
  have : CompactSpace F.Y := (F.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  induction s using Finset.induction_on with
  | empty => simpa using h
  | insert P s hP ih =>
    have hC : Divisor.IsCartier (Finsupp.single P 1 : Divisor X) :=
      MMP.Fourfold.isCartier_of_isSmoothScheme hsm _
    have hB := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp F.f
      (Finsupp.single P (1 : ℤ) : Divisor X)
    obtain ⟨P', hP'⟩ := hC.exists_isPullback hB
    have h' := isLogDiscrepancy_add_smul (ih fun Q hQ => he Q (Finset.mem_insert_of_mem hQ)) hC
      (c P) P' hB hP'
    rw [he P (Finset.mem_insert_self _ _) P' hB hP'] at h'
    have e1 : B + ∑ Q ∈ insert P s, c Q • Divisor.toRDivisor (Finsupp.single Q 1 : Divisor X) =
        B + ∑ Q ∈ s, c Q • Divisor.toRDivisor (Finsupp.single Q 1 : Divisor X) +
          c P • Divisor.toRDivisor (Finsupp.single P 1 : Divisor X) := by
      rw [Finset.sum_insert hP]
      abel
    have e2 : a - ∑ Q ∈ insert P s, c Q * e Q = a - ∑ Q ∈ s, c Q * e Q - c P * e P := by
      rw [Finset.sum_insert hP]
      ring
    rwa [e1, e2]

end Toolkit

/-! ### The arithmetic of the comparison on a log resolution -/

/-- If `A₀ = t + ∑ a₀ᵢ eᵢ` vanishes, all `eᵢ ≥ 0`, and `αᵢ = Gᵢ = 0` whenever `a₀ᵢ = 0`, then
`∑ Gᵢ eᵢ = 0` and `A = t + ∑ αᵢ eᵢ = 0`. -/
private theorem sum_mul_eq_zero_of_eq_zero {ι : Type*} (s : Finset ι) (a₀ : ι → ℕ) (α : ι → ℝ)
    (e G : ι → ℤ) (t : ℕ) {A₀ A : ℝ} (he : ∀ i ∈ s, 0 ≤ e i)
    (hz : ∀ i ∈ s, a₀ i = 0 → α i = 0) (hGz : ∀ i ∈ s, a₀ i = 0 → G i = 0)
    (hA₀ : A₀ = t + ∑ i ∈ s, (a₀ i : ℝ) * e i) (hA : A = t + ∑ i ∈ s, α i * e i)
    (hA0 : A₀ = 0) : ∑ i ∈ s, G i * e i = 0 ∧ A = 0 := by
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hnn : ∀ i ∈ s, 0 ≤ (a₀ i : ℝ) * e i := fun i hi =>
    mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast he i hi)
  have hsum0 : ∑ i ∈ s, (a₀ i : ℝ) * e i = 0 := by linarith [Finset.sum_nonneg hnn]
  have ht0 : (t : ℝ) = 0 := by linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0
  have hGe : ∀ i ∈ s, (G i : ℝ) * e i = 0 ∧ α i * e i = 0 := by
    intro i hi
    by_cases h0 : a₀ i = 0
    · simp [hGz i hi h0, hz i hi h0]
    · have he0 : (e i : ℝ) = 0 := by
        rcases mul_eq_zero.mp (hzero i hi) with h | h
        · exact absurd (by exact_mod_cast h) h0
        · exact h
      simp [he0]
  have hS : ∑ i ∈ s, (G i : ℝ) * e i = 0 := Finset.sum_eq_zero fun i hi => (hGe i hi).1
  refine ⟨by exact_mod_cast hS, ?_⟩
  rw [hA, ht0, Finset.sum_eq_zero fun i hi => (hGe i hi).2]
  simp

/-- If `A₀ = t + ∑ a₀ᵢ eᵢ` and `A = t + ∑ αᵢ eᵢ` with `t, eᵢ ≥ 0`, `a₀ᵢ ∈ ℕ`, `αᵢ = 0` whenever
`a₀ᵢ = 0`, and `Gᵢ = ⌈αᵢ⌉ - 1 + [a₀ᵢ = 0]`, then `∑ Gᵢ eᵢ ≤ ⌈A⌉ - 1 + [A₀ = 0]`. -/
private theorem sum_mul_le_ceil {ι : Type*} (s : Finset ι) (a₀ : ι → ℕ) (α : ι → ℝ)
    (e G : ι → ℤ) (t : ℕ) {A₀ A : ℝ} (he : ∀ i ∈ s, 0 ≤ e i)
    (hz : ∀ i ∈ s, a₀ i = 0 → α i = 0)
    (hG : ∀ i ∈ s, G i = ⌈α i⌉ - 1 + if ((a₀ i : ℕ) : ℝ) = 0 then 1 else 0)
    (hA₀ : A₀ = t + ∑ i ∈ s, (a₀ i : ℝ) * e i) (hA : A = t + ∑ i ∈ s, α i * e i) :
    ∑ i ∈ s, G i * e i ≤ ⌈A⌉ - 1 + if A₀ = 0 then 1 else 0 := by
  have hGz : ∀ i ∈ s, a₀ i = 0 → G i = 0 := by
    intro i hi h0
    rw [hG i hi, hz i hi h0]
    simp [h0]
  have hGpos : ∀ i ∈ s, a₀ i ≠ 0 → (G i : ℝ) < α i := by
    intro i hi h0
    rw [hG i hi, if_neg (by exact_mod_cast h0)]
    push_cast
    linarith [Int.ceil_lt_add_one (α i)]
  have hterm : ∀ i ∈ s, 0 ≤ (α i - G i) * e i := by
    intro i hi
    by_cases h0 : a₀ i = 0
    · simp [hz i hi h0, hGz i hi h0]
    · exact mul_nonneg (by linarith [hGpos i hi h0]) (by exact_mod_cast he i hi)
  have hdiff : A - ∑ i ∈ s, (G i : ℝ) * e i = t + ∑ i ∈ s, (α i - G i) * e i := by
    rw [hA]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  by_cases hA0 : A₀ = 0
  · obtain ⟨hS', hA'⟩ := sum_mul_eq_zero_of_eq_zero s a₀ α e G t he hz hGz hA₀ hA hA0
    rw [if_pos hA0, hS', hA']
    simp
  · rw [if_neg hA0]
    have hlt : ((∑ i ∈ s, G i * e i : ℤ) : ℝ) < A := by
      push_cast
      by_contra! hle
      have hsnn := Finset.sum_nonneg hterm
      have ht0 : (t : ℝ) = 0 := by linarith
      have hs0 : ∑ i ∈ s, (α i - G i) * e i = 0 := by linarith
      have hz2 := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hs0
      apply hA0
      rw [hA₀, ht0, zero_add]
      refine Finset.sum_eq_zero fun i hi => ?_
      by_cases h0 : a₀ i = 0
      · simp [h0]
      · rcases mul_eq_zero.mp (hz2 i hi) with h | h
        · exact absurd h (by linarith [hGpos i hi h0])
        · simp [h]
    have : (∑ i ∈ s, G i * e i : ℤ) < ⌈A⌉ := by exact_mod_cast hlt.trans_le (Int.le_ceil A)
    omega

/-- `⌈a⌉ - 1 + [a₀ = 0] ≤ 0` when `a ≤ a₀ ∈ {0, 1}`. -/
private theorem ceil_sub_one_add_ite_nonpos {a₀ a : ℝ} (h01 : a₀ = 0 ∨ a₀ = 1) (hle : a ≤ a₀) :
    ⌈a⌉ - 1 + (if a₀ = 0 then 1 else 0) ≤ 0 := by
  rcases h01 with h | h
  · rw [if_pos h]
    have := Int.ceil_le.mpr (show a ≤ ((0 : ℤ) : ℝ) by push_cast; linarith)
    omega
  · rw [if_neg (by rw [h]; norm_num)]
    have := Int.ceil_le.mpr (show a ≤ ((1 : ℤ) : ℝ) by push_cast; linarith)
    omega

/-- The exponent `⌈a⌉ - 1 + [a₀ = 0]` decreases when the integral `a₀ ∈ ℕ` drops by `c₁ ≥ 0` to
`a₀ - c₁ ∈ ℕ` and `a` drops by at least `c₁`. -/
private theorem ceil_add_ite_le_of_le {a₀ a c₁ c₂ : ℝ} {p p' : ℕ} (hp : a₀ = p)
    (hp' : a₀ - 1 * c₁ = p') (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    ⌈a - 1 * c₁ - c₂⌉ - 1 + (if a₀ - 1 * c₁ = 0 then 1 else 0) ≤
      ⌈a⌉ - 1 + (if a₀ = 0 then 1 else 0) := by
  have hmono : ⌈a - 1 * c₁ - c₂⌉ ≤ ⌈a⌉ := Int.ceil_mono (by linarith)
  split_ifs with h1 h2 h2
  · omega
  · have hp1 : (1 : ℝ) ≤ p := by
      have hp0 : p ≠ 0 := by
        rintro rfl
        exact h2 (by rw [hp]; simp)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp0
    have h3 : ⌈a - 1 * c₁ - c₂⌉ ≤ ⌈a - 1⌉ := Int.ceil_mono (by linarith)
    rw [Int.ceil_sub_one] at h3
    omega
  · exfalso
    apply h1
    have : (0 : ℝ) ≤ p' := Nat.cast_nonneg _
    linarith
  · omega

/-! ### Divisors over `X` realized over a proper birational model -/

section Model

variable {k : Type u} [Field k]

/-- **The centre of a divisorial valuation on a proper model.** Let `π : W ⟶ X` be a proper
dominant morphism of integral schemes and `D` a divisor over `X`. A valuation `ξ` of `k(W)`
restricting to `ord_D` on `k(X)` dominates the local ring of some point of `W`. -/
private theorem exists_dominated_point {X W : Scheme.{u}} [IsIntegral X]
    [IsIntegral W] {sX : X ⟶ Spec (.of k)} (π : W ⟶ X) [IsDominant π] (hπ : IsProper π)
    (D : DivisorOver k sX) (ξ : Valuation W.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ.comap (functionFieldMap π) = D.valuation) :
    ∃ x : W, (∀ a : W.presheaf.stalk x, ξ (algebraMap _ W.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk x),
        ξ (algebraMap _ W.functionField a) < 1 := by
  set y := D.f D.E.genericPoint
  have hw : ∀ b : X.presheaf.stalk y,
      ξ (functionFieldMap π (algebraMap _ X.functionField b)) =
        D.valuation (algebraMap _ X.functionField b) := by
    intro b
    simpa only [Valuation.comap_apply] using
      congrArg (fun v => v (algebraMap _ X.functionField b)) h
  let R := ξ.valuationSubring
  let φ : X.presheaf.stalk y →+* R :=
    ((functionFieldMap π).comp (algebraMap (X.presheaf.stalk y) X.functionField)).codRestrict R
      fun b => (ξ.mem_valuationSubring_iff _).2 (by
        rw [RingHom.comp_apply, hw]
        exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D y rfl _)
  have hgen : genericPoint X ⤳ y := (genericPoint_spec X).specializes trivial
  have hex : ValuativeCriterion.Existence π := by
    have h : @IsProper _ _ π := hπ
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq π :=
    { R := R
      K := W.functionField
      i₁ := W.fromSpecStalk (genericPoint W)
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk y
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk π,
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R W.functionField)) ≫ l =
      W.fromSpecStalk (genericPoint W) := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint W ⤳ x := (genericPoint_spec W).specializes trivial
  let f := Scheme.stalkClosedPointTo l
  have hf : f ≫ CommRingCat.ofHom (algebraMap R W.functionField) =
      W.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (W.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hfa : ∀ a : W.presheaf.stalk x,
      algebraMap _ W.functionField a = ((f.hom a : R) : W.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hf).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hfa]
    exact (f.hom a).2
  · rw [hfa]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit f.hom a hu))

/-- **Divisors over `X` are realized over a proper birational model.** For a proper birational
morphism `π : W ⟶ X` of normal varieties and a divisor `D` over `X`, some divisor `D'` over `W`,
proper over `W`, induces the valuation of `D` on `k(X) ≅ k(W)`, and its centre on `W` maps to
the centre of `D` on `X`. -/
private theorem exists_divisorOver_model {X W : Scheme.{u}} [IsIntegral X] [IsIntegral W]
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX) (π : W ⟶ X) (hπ : IsProper π)
    (hbir : IsBirationalMorphism π) (hW : IsNormalVariety k (π ≫ sX)) (D : DivisorOver k sX) :
    haveI : IsDominant π := hbir.isDominant
    ∃ D' : DivisorOver k (π ≫ sX), IsProper D'.f ∧
      D.valuation = D'.valuation.comap (functionFieldMap π) ∧
      π (D'.f D'.E.genericPoint) = D.f D.E.genericPoint := by
  haveI : IsDominant π := hbir.isDominant
  have hbij := hbir.functionFieldMap_bijective
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (π ≫ sX)
  let eπ := functionFieldAlgEquiv sX π hbij
  let ξ := D.valuation.comap (eπ.symm : W.functionField →+* X.functionField)
  have hξ : ξ.comap (functionFieldMap π) = D.valuation := by
    ext t
    change D.valuation (eπ.symm (eπ t)) = D.valuation t
    rw [eπ.symm_apply_apply]
  obtain ⟨x, h1, h2⟩ := exists_dominated_point π hπ D ξ hξ
  haveI : AlgebraicGeometry.IsVariety k (π ≫ sX) := hW.1
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k (π ≫ sX) ξ := by
    haveI := D.isIntegral
    haveI := D.isNormal
    haveI := D.isLocallyNoetherian
    haveI := D.isDominant
    refine ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, ?_⟩
    letI := functionFieldAlgebra (D.f ≫ sX)
    let eD := functionFieldAlgEquiv sX D.f D.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eπ.symm.trans eD, ?_⟩
    ext t
    rfl
  obtain ⟨D', -, hv, hDx⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (π ≫ sX) hdiv x h1 h2
  have hval : D.valuation = D'.toDivisorOver.valuation.comap (functionFieldMap π) := by
    rw [← hξ, ← hv]
  refine ⟨D'.toDivisorOver, D'.isProper, hval, ?_⟩
  -- the centres agree: compare `D` with `D'` regarded as a divisor over `X`
  have hcomp := MMP.Mori.valuation_compDivisorOver π hW hbir D'.toDivisorOver
  have hcen := MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX
    (hcomp.trans hval.symm)
  have e1 := (MMP.Mori.compDivisorOver π hW hbir D'.toDivisorOver).center_eq_closure_genericPoint
  have e2 := D.center_eq_closure_genericPoint
  rw [← hcen, e1] at e2
  have hins : Inseparable ((MMP.Mori.compDivisorOver π hW hbir D'.toDivisorOver).f
      (MMP.Mori.compDivisorOver π hW hbir D'.toDivisorOver).E.genericPoint)
      (D.f D.E.genericPoint) := inseparable_iff_closure_eq.mpr e2
  exact hins.eq

end Model

/-! ### Push-forwards with values in `𝒪_X` are ideal sheaves -/

section Ideal

variable {X X' : Scheme.{u}} [IsIntegral X] [IsIntegral X'] [IsLocallyNoetherian X']
  [IsNormal X'] (μ : X' ⟶ X) [IsDominant μ]

/-- The valuation `v_P(μ^* ·)` on the stalk of `X` at the centre `μ(η_P)` is at most `1`. -/
private theorem val_stalk_le_one (P : MMP.Mori.PrimeDivisor X')
    (a : X.presheaf.stalk (μ P.genericPoint)) :
    P.valuationOver μ (algebraMap _ X.functionField a) ≤ 1 := by
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply,
    MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff,
    MMP.Mori.functionFieldMap_algebraMap_stalk]
  exact ⟨_, rfl⟩

/-- A non-unit of the stalk of `X` at the centre `μ(η_P)` has `v_P(μ^* ·) < 1`. -/
private theorem val_stalk_lt_one (P : MMP.Mori.PrimeDivisor X')
    (a : X.presheaf.stalk (μ P.genericPoint)) (ha : ¬ IsUnit a) :
    P.valuationOver μ (algebraMap _ X.functionField a) < 1 := by
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.functionFieldMap_algebraMap_stalk,
    MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff]
  exact (IsLocalRing.mem_maximalIdeal _).mpr fun h => ha (isUnit_of_map_unit _ _ h)

/-- The regular functions `a` on `U` with `v_P(μ^* a) ≤ exp (coeff_P G)` at every prime divisor
`P` whose generic point maps into `U`. -/
private def valIdeal (G : Divisor X') (U : X.Opens) : Ideal Γ(X, U) where
  carrier := {a | ∀ (P : MMP.Mori.PrimeDivisor X') (hP : μ P.genericPoint ∈ U),
    P.valuationOver μ (algebraMap _ X.functionField (X.presheaf.germ U _ hP a)) ≤
      WithZero.exp (G.coeff P)}
  add_mem' {a b} ha hb P hP := by
    rw [map_add, map_add]
    exact (Valuation.map_add _ _ _).trans (max_le (ha P hP) (hb P hP))
  zero_mem' P hP := by simp
  smul_mem' c a ha P hP := by
    rw [smul_eq_mul, map_mul, map_mul, Valuation.map_mul]
    exact (mul_le_of_le_one_left' (val_stalk_le_one μ P _)).trans (ha P hP)

/-- Some `m : ℕ` bounds every coefficient of `G` from below by `-m`. -/
private theorem exists_neg_le_coeff (G : Divisor X') : ∃ m : ℕ, ∀ P, -(m : ℤ) ≤ G.coeff P := by
  refine ⟨∑ P ∈ G.support, (G.coeff P).natAbs, fun P => ?_⟩
  by_cases hP : P ∈ G.support
  · have := Finset.single_le_sum (f := fun P => (G.coeff P).natAbs) (fun _ _ => Nat.zero_le _) hP
    omega
  · rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.notMem_support_iff.mp hP]; omega

/-- If `y|_{D(f)} = f ^ n b` with `b` in the ideal on `D(f)`, then `f ^ m y` lies in the ideal on
`U` as soon as `-m` bounds the coefficients of `G` from below. -/
private theorem pow_mul_mem_valIdeal {G : Divisor X'} {U : X.Opens} {f y : Γ(X, U)}
    {b : Γ(X, X.basicOpen f)} {n m : ℕ} (hb : b ∈ valIdeal μ G (X.basicOpen f))
    (hy : y |_ X.basicOpen f = (f |_ X.basicOpen f) ^ n * b) (hm : ∀ P, -(m : ℤ) ≤ G.coeff P) :
    f ^ m * y ∈ valIdeal μ G U := by
  intro P hP
  rw [map_mul, map_mul, Valuation.map_mul, map_pow, map_pow, Valuation.map_pow]
  by_cases hf : μ P.genericPoint ∈ X.basicOpen f
  · refine (mul_le_of_le_one_left' (pow_le_one' (val_stalk_le_one μ P _) m)).trans ?_
    have h2 : X.presheaf.germ _ _ hP y = X.presheaf.germ _ _ hP f ^ n *
        X.presheaf.germ _ _ hf b := by
      rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (X.basicOpen_le f)) _ hf,
        ← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (X.basicOpen_le f)) _ hf,
        ← map_pow, ← map_mul]
      exact congrArg _ hy
    rw [h2, map_mul, Valuation.map_mul, map_pow, Valuation.map_pow]
    exact (mul_le_of_le_one_left' (pow_le_one' (val_stalk_le_one μ P _) n)).trans (hb P hf)
  · have hlt := val_stalk_lt_one μ P (X.presheaf.germ _ _ hP f)
      (by rwa [← X.mem_basicOpen f _ hP])
    have hle : P.valuationOver μ (algebraMap _ X.functionField (X.presheaf.germ _ _ hP f)) ≤
        WithZero.exp (-1) := (WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero).mp
      (by rwa [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero])
    refine (mul_le_of_le_one_right' (val_stalk_le_one μ P _)).trans
      ((pow_le_pow_left₀ zero_le' hle m).trans ?_)
    rw [← WithZero.exp_nsmul, WithZero.exp_le_exp]
    simpa using hm P

/-- The ideal sheaf of `X` whose ideal on an affine open `U` is `valIdeal μ G U`. -/
private def valIdealSheaf (G : Divisor X') : X.IdealSheafData where
  ideal U := valIdeal μ G U
  map_ideal_basicOpen U f := by
    change _ = valIdeal μ G (X.basicOpen f)
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha P hP
      change P.valuationOver μ (algebraMap _ X.functionField
        (X.presheaf.germ _ _ hP ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom a))) ≤ _
      rw [TopCat.Presheaf.germ_res_apply]
      exact ha P (X.basicOpen_le f hP)
    · intro b hb
      obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen X U U.2 f b
      obtain ⟨m, hm⟩ := exists_neg_le_coeff G
      have hin := Ideal.mem_map_of_mem (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
        (pow_mul_mem_valIdeal μ hb hy hm)
      rw [map_mul, map_pow] at hin
      change _ * (y |_ X.basicOpen f) ∈ _ at hin
      rw [hy, ← mul_assoc] at hin
      have hu := X.toRingedSpace.isUnit_res_basicOpen f
      exact (Ideal.unit_mul_mem_iff_mem _ ((hu.pow m).mul (hu.pow n))).mp hin

/-- **A push-forward with values in `𝒪_X` is an ideal sheaf.** If the sections of
`μ_*𝒪_{X'}(G)` over every non-empty open are regular functions, then on every non-empty affine
open they are the ideal of an ideal sheaf of `X`. -/
private theorem exists_idealSheafData_of_subset_range [IsLocallyNoetherian X] [IsNormal X]
    (G : Divisor X')
    (hsub : ∀ (U : X.Opens) [Nonempty U],
      MMP.Intersection.multiplierIdealSections μ G U ⊆ Set.range (X.germToFunctionField U)) :
    ∃ I : X.IdealSheafData, ∀ (U : X.affineOpens) [Nonempty (U : X.Opens)],
      MMP.Intersection.multiplierIdealSections μ G U =
        X.germToFunctionField (U : X.Opens) '' (I.ideal U : Set Γ(X, U)) := by
  refine ⟨valIdealSheaf μ G, fun U _ => ?_⟩
  have hne : μ ⁻¹ᵁ (U : X.Opens) ≠ ⊥ := by
    obtain ⟨u⟩ := ‹Nonempty (U : X.Opens)›
    obtain ⟨_, hx', x', rfl⟩ :=
      μ.denseRange.inter_open_nonempty _ (U : X.Opens).isOpen ⟨u.1, u.2⟩
    exact (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mpr ⟨x', hx'⟩
  ext g
  constructor
  · intro hg
    obtain ⟨a, rfl⟩ := hsub U hg
    refine ⟨a, fun P hP => ?_, rfl⟩
    have := hg.2 P (MMP.Intersection.support_inter_nonempty_of_genericPoint_mem P
      (V := μ ⁻¹ᵁ (U : X.Opens)) hP)
    rwa [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hP] at this
  · rintro ⟨a, ha, rfl⟩
    refine ⟨fun h => absurd h hne, fun P hP => ?_⟩
    have hη : μ P.genericPoint ∈ (U : X.Opens) :=
      MMP.Intersection.genericPoint_mem_of_support_inter_nonempty P hP
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hη]
    exact ha P hη

end Ideal

/-! ### Divisors on a log resolution -/

section Main

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- `∑_{P ∈ s} c_P P = B` when `B` has coefficient `c_P` along `P ∈ s` and vanishes off `s`. -/
private theorem sum_smul_single_eq (s : Finset (MMP.Mori.PrimeDivisor X))
    (c : MMP.Mori.PrimeDivisor X → ℝ) (B : RDivisor X) (hin : ∀ Q ∈ s, B.coeff Q = c Q)
    (hout : ∀ Q ∉ s, B.coeff Q = 0) :
    ∑ P ∈ s, c P • Divisor.toRDivisor (Finsupp.single P 1 : Divisor X) = B := by
  classical
  refine Finsupp.ext fun Q => ?_
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  have h1 : ∀ P, (Divisor.toRDivisor (Finsupp.single P (1 : ℤ) : Divisor X)) Q =
      if P = Q then 1 else 0 := by
    intro P
    rw [← DivisorWithCoeffs.coeff_apply, Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply,
      Finsupp.single_apply]
    split_ifs <;> simp
  simp only [h1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq]
  rw [← DivisorWithCoeffs.coeff_apply B]
  by_cases hQ : Q ∈ s
  · rw [if_pos hQ, hin Q hQ]
  · rw [if_neg hQ, hout Q hQ]

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- `∑_{P ∈ s} P + ∑_{P ∈ s} c_P P = B` when `B` has coefficient `1 + c_P` along `P ∈ s` and
vanishes off `s`. -/
private theorem toRDivisor_add_sum_eq (s : Finset (MMP.Mori.PrimeDivisor X))
    (c : MMP.Mori.PrimeDivisor X → ℝ) (B : RDivisor X) (hin : ∀ Q ∈ s, B.coeff Q = 1 + c Q)
    (hout : ∀ Q ∉ s, B.coeff Q = 0) :
    Divisor.toRDivisor (MMP.Intersection.reducedDivisorOf s) +
      ∑ P ∈ s, c P • Divisor.toRDivisor (Finsupp.single P 1 : Divisor X) = B := by
  classical
  have hT : Divisor.toRDivisor (MMP.Intersection.reducedDivisorOf s) =
      ∑ P ∈ s, (1 : ℝ) • Divisor.toRDivisor (Finsupp.single P 1 : Divisor X) := by
    refine (sum_smul_single_eq s (fun _ => 1) _ (fun Q hQ => ?_) (fun Q hQ => ?_)).symm
    · rw [Divisor.coeff_toRDivisor, MMP.Intersection.coeff_reducedDivisorOf, if_pos hQ]; simp
    · rw [Divisor.coeff_toRDivisor, MMP.Intersection.coeff_reducedDivisorOf, if_neg hQ]; simp
  rw [hT, ← Finset.sum_add_distrib]
  simp_rw [← add_smul]
  exact sum_smul_single_eq s (fun P => 1 + c P) B hin hout

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- An snc closed subset of a smooth scheme is the union of the components of an snc divisor. -/
private theorem exists_finset_of_isSNCSubset [LocallyOfFinitePresentation sX]
    (hsm : IsSmoothScheme sX) {S : Closeds X} (h : IsSNCSubset sX S) :
    ∃ s : Finset (MMP.Mori.PrimeDivisor X), (⋃ E ∈ s, E.support) = (S : Set X) ∧
      DivisorWithCoeffs.IsSNC sX (∑ E ∈ s, Finsupp.single E (1 : ℤ)) := by
  rcases h with h | h
  · refine ⟨∅, by simp [h], ?_⟩
    simpa using DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℤ) sX hsm
  · exact h

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- A variety has finite dimension. -/
private theorem exists_topologicalKrullDim_eq [IsIntegral X] (hX : MMP.Mori.IsVariety k sX) :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  haveI : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have h := Stacks.Chow.topologicalKrullDim_closure_singleton_eq k sX (genericPoint X)
  rw [(genericPoint_spec X).def] at h
  exact ⟨_, (IsHomeomorph.topologicalKrullDim_eq _
    (Homeomorph.Set.univ X).isHomeomorph).symm.trans h⟩

/-- The log discrepancy of a prime divisor `Q` of the smooth `X` is `1 - coeff_Q B`. -/
private theorem isLogDiscrepancy_ofPrimeDivisor [PerfectField k] (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} (hn : topologicalKrullDim X = n) (B : QDivisor X)
    (Q : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B)
      (DivisorOver.ofPrimeDivisor k hX Q) (1 - B.coeff Q) := by
  haveI : MMP.Mori.IsVariety k sX := hX.1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme sX hsm hn
  have hP : MMP.Mori.IsPair sX B :=
    ⟨hX, n, K, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK
    (DivisorOver.ofPrimeDivisor k hX Q)
  have h := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
    (show IsProper (𝟙 X) from inferInstance)
  rw [MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX hc] at h
  convert h using 1
  push_cast
  ring

/-- The valuation of a prime divisor of `X`, regarded as a divisor over `X`. -/
private theorem valuation_ofPrimeDivisor (hX : IsNormalVariety k sX)
    (Q : MMP.Mori.PrimeDivisor X) (g : X.functionField) :
    (DivisorOver.ofPrimeDivisor k hX Q).valuation g = Q.divisorialValuation g := by
  change Q.divisorialValuation (functionFieldMap (𝟙 X) g) = _
  rw [MMP.Mori.functionFieldMap_id_apply]

/-- A prime divisor of a proper birational model which is not exceptional and whose centre lies
off `Supp B` has log discrepancy `1` with respect to `B`. -/
private theorem isLogDiscrepancy_one_of_notMem [PerfectField k] (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} (hn : topologicalKrullDim X = n) {Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {μ : Y ⟶ X}
    (hY : IsNormalVariety k (μ ≫ sX)) (hμ : IsBirationalMorphism μ) (hμp : IsProper μ)
    (B : QDivisor X) (P : MMP.Mori.PrimeDivisor Y)
    (hexc : P.genericPoint ∉ (exceptionalSet μ : Set Y))
    (hB : μ P.genericPoint ∉ (DivisorWithCoeffs.supp (QDivisor.toRDivisor B) : Set X)) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) ⟨Y, μ, hY, hμ, P⟩ 1 := by
  haveI : MMP.Mori.IsVariety k sX := hX.1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme sX hsm hn
  have hPW : MMP.Mori.IsPairWith sX n K B :=
    ⟨hX, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩
  set FP : DivisorOver k sX := ⟨Y, μ, hY, hμ, P⟩ with hFPdef
  have hPmem := MMP.Flips.primeDivisor_genericPoint_mem_support P
  have hne : ¬ FP.IsExceptional := fun hexc' =>
    hexc (MMP.Positivity.support_subset_exceptionalSet P hexc' hPmem)
  obtain ⟨Q, hQc, hQd⟩ := MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hPW FP hne
  have hηQ : μ P.genericPoint = Q.genericPoint := by
    have e1 := FP.center_eq_closure_genericPoint
    rw [hQc, AlgebraicGeometry.PrimeDivisor.support_eq_closure Q] at e1
    exact (inseparable_iff_closure_eq.mpr e1.symm).eq
  have hQmem := MMP.Flips.primeDivisor_genericPoint_mem_support Q
  have hQ0 : B.coeff Q = 0 := by
    by_contra hne'
    apply hB
    rw [hηQ]
    exact DivisorWithCoeffs.support_subset_supp
      (by rwa [QDivisor.coeff_toRDivisor, Rat.cast_ne_zero]) hQmem
  rw [hQ0, neg_zero] at hQd
  have hl := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hQd hμp
  convert hl using 1
  simp

end Main

/-! ### Valuations of regular functions and of local equations -/

section Valuations

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A rational function with nonnegative order along every prime divisor through the centre of a
divisor `G` over `X` has `v_G ≤ 1`. -/
private theorem valuation_le_one_of_forall_ord_nonneg (G : DivisorOver k sX)
    {u : X.functionField}
    (h : ∀ Γ : MMP.Mori.PrimeDivisor X, G.f G.E.genericPoint ∈ Γ.support →
      0 ≤ X.ord u Γ.genericPoint) : G.valuation u ≤ 1 := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  obtain ⟨r, hr⟩ :=
    MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg _ hu h
  rw [← hr]
  exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one G _ rfl r

/-- A nonzero rational function of order zero along every prime divisor through the centre of a
divisor `G` over `X` has `v_G = 1`. -/
private theorem valuation_eq_one_of_forall_ord_eq_zero (G : DivisorOver k sX)
    {u : X.functionField} (hu : u ≠ 0)
    (h : ∀ Γ : MMP.Mori.PrimeDivisor X, G.f G.E.genericPoint ∈ Γ.support →
      X.ord u Γ.genericPoint = 0) : G.valuation u = 1 := by
  apply le_antisymm (valuation_le_one_of_forall_ord_nonneg G fun Γ hΓ => (h Γ hΓ).ge)
  have h2 := valuation_le_one_of_forall_ord_nonneg G (u := u ^ (-1 : ℤ)) fun Γ hΓ => by
    rw [MMP.Mori.ord_zpow _ hu, h Γ hΓ]; simp
  rw [map_zpow₀, zpow_neg_one] at h2
  have hpos : 0 < G.valuation u := zero_lt_iff.mpr ((map_ne_zero _).mpr hu)
  exact (inv_le_one₀ hpos).mp h2

/-- The order of a local equation `φ` of `D` on `U` along a prime divisor meeting `U` is the
coefficient of `D`. -/
private theorem ord_evalFF_of_isLocalEquation {D : Divisor X} {U : X.Opens}
    {φ : (MMP.Mori.RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ)
    (Z : irreducibleComponents X) (Γ : MMP.Mori.PrimeDivisor X) (hΓ : (Γ.support ∩ U).Nonempty) :
    X.ord (MMP.Threefold.Mori.Helpers.evalFF Z (φ : MMP.Mori.RationalFunctions X))
      Γ.genericPoint = D.coeff Γ := by
  rw [hφ Γ hΓ, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord,
    show Γ.component = Z from
      Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _]

private theorem evalFF_ne_zero (Z : irreducibleComponents X)
    (φ : (MMP.Mori.RationalFunctions X)ˣ) :
    MMP.Threefold.Mori.Helpers.evalFF Z (φ : MMP.Mori.RationalFunctions X) ≠ 0 :=
  (φ.isUnit.map _).ne_zero

/-- A section `g` of `𝒪_X(D)` has `ord_Γ(g) + coeff_Γ(D) ≥ 0`. -/
private theorem ord_add_coeff_nonneg {D : Divisor X} {g : X.functionField}
    (hg : g ∈ sectionsIn D) (hg0 : g ≠ 0) (Γ : MMP.Mori.PrimeDivisor X) :
    0 ≤ X.ord g Γ.genericPoint + D.coeff Γ := by
  have h := hg Γ
  rw [Γ.divisorialValuation_eq_exp_neg_ord hg0, WithZero.exp_le_exp] at h
  omega

/-- A section `g` of `𝒪_X(D)` times a local equation of `D` near the centre of `G` has
`v_G ≤ 1`. -/
private theorem valuation_mul_evalFF_le_one (G : DivisorOver k sX) {D : Divisor X}
    {g : X.functionField} (hg : g ∈ sectionsIn D) {U : X.Opens}
    {φ : (MMP.Mori.RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ)
    (hx : G.f G.E.genericPoint ∈ U) (Z : irreducibleComponents X) :
    G.valuation (g * MMP.Threefold.Mori.Helpers.evalFF Z (φ : MMP.Mori.RationalFunctions X)) ≤
      1 := by
  rcases eq_or_ne g 0 with rfl | hg0
  · simp
  refine valuation_le_one_of_forall_ord_nonneg G fun Γ hΓ => ?_
  rw [Scheme.ord_mul hg0 (evalFF_ne_zero Z φ),
    ord_evalFF_of_isLocalEquation hφ Z Γ ⟨_, hΓ, hx⟩]
  exact ord_add_coeff_nonneg hg hg0 Γ

/-- An integer `w` with `exp (-w) ≤ v_G(g' φ)` for every local equation `φ` of `D` near the centre
of `G`, where `g'` is a section of `𝒪_X(D)`, is nonnegative. -/
private theorem nonneg_of_forall_exp_neg_le (G : DivisorOver k sX) {D : Divisor X}
    (hDc : D.IsCartier) {g' : X.functionField} (hg' : g' ∈ sectionsIn D) {w : ℤ}
    (hw : ∀ (U : X.Opens) (φ : (MMP.Mori.RationalFunctions X)ˣ) (Z : irreducibleComponents X),
      D.IsLocalEquation U φ → G.f G.E.genericPoint ∈ U →
      WithZero.exp (-w) ≤ G.valuation (g' * MMP.Threefold.Mori.Helpers.evalFF Z
        (φ : MMP.Mori.RationalFunctions X))) :
    0 ≤ w := by
  obtain ⟨U, hxU, φ, hφ⟩ := hDc (G.f G.E.genericPoint)
  have h1 := (hw U φ (MMP.Mori.pointComponent (genericPoint X)) hφ hxU).trans
    (valuation_mul_evalFF_le_one G hg' hφ hxU _)
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

/-- Along a prime divisor `P` of `Y` centred in `U`, a local equation of `D` on `U` has
`v_P(μ^*φ) = exp (-coeff_P(μ^*D))`. -/
private theorem valuationOver_evalFF_eq {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {μ : Y ⟶ X} [IsDominant μ] {D : Divisor X}
    {hD : ∀ Z : irreducibleComponents Y, μ (componentGenericPoint Y Z) ∉ D.supp}
    {Dμ : Divisor Y} (h : D.IsPullback μ hD Dμ) {U : X.Opens}
    {φ : (MMP.Mori.RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ)
    (P : MMP.Mori.PrimeDivisor Y) (hP : μ P.genericPoint ∈ U) (Z : irreducibleComponents X) :
    P.valuationOver μ (MMP.Threefold.Mori.Helpers.evalFF Z (φ : MMP.Mori.RationalFunctions X)) =
      WithZero.exp (-Dμ.coeff P) := by
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply,
    P.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).mpr (evalFF_ne_zero Z φ)),
    MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h hφ P hP Z]

end Valuations

/-! ### Base loci and fixed divisors -/

section Fixed

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The base locus of a linear series is closed under specialization. -/
private theorem closure_subset_baseLocusIn {V : Set X.functionField} {D : Divisor X} {x : X}
    (hx : x ∈ baseLocusIn V D) : closure {x} ⊆ baseLocusIn V D := by
  intro z hz g hg hg0
  obtain ⟨P, hxP, hlt⟩ := hx g hg hg0
  refine ⟨P, ?_, hlt⟩
  have hcl : IsClosed (P.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  exact hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hxP) hz

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {μ : Y ⟶ X}
  [IsDominant μ] {D : Divisor X}
  {hD : ∀ Z : irreducibleComponents Y, μ (componentGenericPoint Y Z) ∉ D.supp} {Dμ : Divisor Y}

/-- `v_P(μ^*(g φ)) = v_P(μ^*g) · exp (-coeff_P(μ^*D))` for a local equation `φ` of `D` near the
centre of `P`. -/
private theorem valuationOver_mul_evalFF (h : D.IsPullback μ hD Dμ) (hDc : D.IsCartier)
    (P : MMP.Mori.PrimeDivisor Y) (g : X.functionField) :
    ∃ (U : X.Opens) (φ : (MMP.Mori.RationalFunctions X)ˣ), D.IsLocalEquation U φ ∧
      μ P.genericPoint ∈ U ∧ ∀ Z : irreducibleComponents X,
        P.valuationOver μ (g * MMP.Threefold.Mori.Helpers.evalFF Z
          (φ : MMP.Mori.RationalFunctions X)) =
          P.valuationOver μ g * WithZero.exp (-Dμ.coeff P) := by
  obtain ⟨U, hxU, φ, hφ⟩ := hDc (μ P.genericPoint)
  refine ⟨U, φ, hφ, hxU, fun Z => ?_⟩
  rw [Valuation.map_mul, valuationOver_evalFF_eq h hφ P hxU Z]

/-- The fixed divisor of a series of sections of `𝒪_X(D)` pulled back to `Y` is effective. -/
private theorem coeff_nonneg_of_isFixedDivisorOfPullback (hDc : D.IsCartier)
    {V : Set X.functionField} (hVs : V ⊆ sectionsIn D) (h : D.IsPullback μ hD Dμ)
    {F : Divisor Y} (hF : IsFixedDivisorOfPullback μ V Dμ F) (P : MMP.Mori.PrimeDivisor Y)
    (hY : IsNormalVariety k (μ ≫ sX)) (hμ : IsBirationalMorphism μ) :
    0 ≤ F.coeff P := by
  obtain ⟨g, hgV, -, hgeq⟩ := (hF P).2
  obtain ⟨U, φ, hφ, hxU, hval⟩ := valuationOver_mul_evalFF h hDc P g
  set Z : irreducibleComponents X := MMP.Mori.pointComponent (genericPoint X)
  have h1 := valuation_mul_evalFF_le_one (⟨Y, μ, hY, hμ, P⟩ : DivisorOver k sX) (hVs hgV) hφ
    hxU Z
  change P.valuationOver μ _ ≤ 1 at h1
  rw [hval Z, hgeq, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

/-- The fixed divisor vanishes along a prime divisor whose centre lies off the base locus. -/
private theorem coeff_nonpos_of_notMem_baseLocusIn (hDc : D.IsCartier)
    {V : Set X.functionField} (hVs : V ⊆ sectionsIn D) (h : D.IsPullback μ hD Dμ)
    {F : Divisor Y} (hF : IsFixedDivisorOfPullback μ V Dμ F) (P : MMP.Mori.PrimeDivisor Y)
    (hY : IsNormalVariety k (μ ≫ sX)) (hμ : IsBirationalMorphism μ)
    (hx : μ P.genericPoint ∉ baseLocusIn V D) : F.coeff P ≤ 0 := by
  simp only [baseLocusIn, Set.mem_setOf_eq, not_forall, not_exists, not_and, not_lt] at hx
  obtain ⟨g, hgV, hg0, hge⟩ := hx
  obtain ⟨U, φ, hφ, hxU, hval⟩ := valuationOver_mul_evalFF h hDc P g
  set Z : irreducibleComponents X := MMP.Mori.pointComponent (genericPoint X)
  have h1 := valuation_eq_one_of_forall_ord_eq_zero (⟨Y, μ, hY, hμ, P⟩ : DivisorOver k sX)
    (u := g * MMP.Threefold.Mori.Helpers.evalFF Z (φ : MMP.Mori.RationalFunctions X))
    (mul_ne_zero hg0 (evalFF_ne_zero Z φ)) fun Γ hΓ => by
      rw [Scheme.ord_mul hg0 (evalFF_ne_zero Z φ),
        ord_evalFF_of_isLocalEquation hφ Z Γ ⟨_, hΓ, hxU⟩]
      have h2 := hge Γ hΓ
      rw [Γ.divisorialValuation_eq_exp_neg_ord hg0, WithZero.exp_le_exp] at h2
      have h3 := ord_add_coeff_nonneg (hVs hgV) hg0 Γ
      omega
  change P.valuationOver μ _ = 1 at h1
  have h4 := (hF P).1 g hgV
  rw [hval Z] at h1
  have h5 : P.valuationOver μ g * WithZero.exp (-Dμ.coeff P) ≤
      WithZero.exp (Dμ.coeff P - F.coeff P) * WithZero.exp (-Dμ.coeff P) :=
    mul_le_mul_left h4 _
  rw [h1, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp] at h5
  omega

end Fixed

/-! ### The adjoint ideal of a linear series by orders along all divisors over `X` -/

section SeriesMain

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The valuative condition at a divisor `G` over `X` with `a = a(G, X, Δ)`: some nonzero
`g' ∈ V` and some integer `w` bounding `ord_G(g') + ord_G(D)` from above (through every local
equation of `D` near the centre of `G`) give `v_G(g) ≤ exp (⌈a - c w⌉ - 1 + [a = 0])`. -/
private def SeriesCond (D : Divisor X) (V : Set X.functionField) (c : ℚ) (G : DivisorOver k sX)
    (a : ℝ) (g : X.functionField) : Prop :=
  ∃ g' ∈ V, g' ≠ 0 ∧ ∃ w : ℤ,
    (∀ (U : X.Opens) (φ : (MMP.Mori.RationalFunctions X)ˣ) (Z : irreducibleComponents X),
      D.IsLocalEquation U φ → G.f G.E.genericPoint ∈ U →
      WithZero.exp (-w) ≤ G.valuation (g' * MMP.Threefold.Mori.Helpers.evalFF Z
        (φ : MMP.Mori.RationalFunctions X))) ∧
    G.valuation g ≤ WithZero.exp (⌈a - (c : ℝ) * w⌉ - 1 + if a = 0 then 1 else 0)

/-- The sections over `U` of `𝒥_{Δ,cV}` described valuatively: the rational functions satisfying
`SeriesCond` at every divisor over `X` centred in `U`. -/
private def seriesSet (Δ D : Divisor X) (V : Set X.functionField) (c : ℚ) (U : X.Opens) :
    Set X.functionField :=
  {g | (U = ⊥ → g = 0) ∧ ∀ (n : ℕ) (G : DivisorOver k sX) (a : ℝ),
    G.f G.E.genericPoint ∈ U →
    MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) G a →
    SeriesCond sX D V c G a g}

/-- A rational function satisfying the valuative condition `SeriesCond` at every divisor over
`X` centred in `U` is a section over `U` of `μ_*𝒪_Y(G)`, when `G` has the coefficient
`⌈a₀ - c F_P⌉ - 1 + [a₀ = 0]` along each prime divisor `P` of `Y` of log discrepancy `a₀`. -/
private theorem mem_multiplierIdealSections_of_mem_seriesSet {Δ D : Divisor X}
    {V : AddSubgroup X.functionField} {c : ℚ} {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {μ : Y ⟶ X} [IsDominant μ]
    (hY : IsNormalVariety k (μ ≫ sX)) (hμ : IsBirationalMorphism μ) (hDc : D.IsCartier)
    {hD : ∀ Z : irreducibleComponents Y, μ (componentGenericPoint Y Z) ∉ D.supp}
    {Dμ F G : Divisor Y} (hDμ : D.IsPullback μ hD Dμ)
    (hfix : IsFixedDivisorOfPullback μ (V : Set X.functionField) Dμ F) (hc : 0 ≤ c)
    (hG : ∀ P : MMP.Mori.PrimeDivisor Y, ∃ n a₀ : ℕ,
      MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) ⟨Y, μ, hY, hμ, P⟩ a₀ ∧
      G.coeff P = ⌈(a₀ : ℝ) - c * F.coeff P⌉ - 1 + if ((a₀ : ℕ) : ℝ) = 0 then 1 else 0)
    {U : X.Opens} {g : X.functionField} (hg : g ∈ seriesSet sX Δ D V c U) :
    g ∈ MMP.Intersection.multiplierIdealSections μ G U := by
  obtain ⟨hg0, hg⟩ := hg
  have hc0 : (0 : ℝ) ≤ c := by exact_mod_cast hc
  refine ⟨fun hU => hg0 ?_, fun P hP => ?_⟩
  · by_contra hne
    obtain ⟨u, hu⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty U).mp hne
    obtain ⟨_, hx', x', rfl⟩ := μ.denseRange.inter_open_nonempty _ U.isOpen ⟨u, hu⟩
    have hx'' : x' ∈ μ ⁻¹ᵁ U := hx'
    rwa [hU] at hx''
  have hxU := MMP.Intersection.genericPoint_mem_of_support_inter_nonempty P hP
  obtain ⟨n, a₀, ha₀, hGP⟩ := hG P
  obtain ⟨g', hg'V, -, w, hw, hv⟩ := hg n ⟨Y, μ, hY, hμ, P⟩ a₀ hxU ha₀
  obtain ⟨U', φ, hφ, hxU', hvalφ⟩ := valuationOver_mul_evalFF hDμ hDc P g'
  set Z₀ : irreducibleComponents X := MMP.Mori.pointComponent (genericPoint X)
  have h1 := hw U' φ Z₀ hφ hxU'
  change _ ≤ P.valuationOver μ _ at h1
  rw [hvalφ Z₀] at h1
  have h2 := (hfix P).1 g' hg'V
  have h3 : WithZero.exp (-w) ≤ WithZero.exp (-F.coeff P) := by
    refine h1.trans ((mul_le_mul_left h2 _).trans_eq ?_)
    rw [← WithZero.exp_add]
    congr 1
    ring
  rw [WithZero.exp_le_exp] at h3
  change P.valuationOver μ g ≤ _ at hv
  rw [hGP]
  refine hv.trans (WithZero.exp_le_exp.mpr ?_)
  have hFw : (F.coeff P : ℝ) ≤ w := by exact_mod_cast (show F.coeff P ≤ w by omega)
  have : ⌈(a₀ : ℝ) - c * w⌉ ≤ ⌈(a₀ : ℝ) - c * F.coeff P⌉ := Int.ceil_mono (by nlinarith)
  omega

/-- A section over `U` of `μ_*𝒪_Y(G)` satisfies the valuative condition `SeriesCond` at every
divisor over `X` centred in `U`, when `μ` is a log resolution and `G` has the coefficient
`⌈a₀ - c F_P⌉ - 1 + [a₀ = 0]` along each prime divisor `P` of `Y` of log discrepancy `a₀`. -/
private theorem mem_seriesSet_of_mem_multiplierIdealSections [IsAlgClosed k] [CharZero k]
    {Δ D : Divisor X} {V : AddSubgroup X.functionField} {c : ℚ} {Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {μ : Y ⟶ X} [IsDominant μ]
    (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) (hY : IsNormalVariety k (μ ≫ sX))
    (hμ : IsBirationalMorphism μ) (hlog : IsLogResolution sX (Divisor.toQDivisor Δ) μ)
    {hD : ∀ Z : irreducibleComponents Y, μ (componentGenericPoint Y Z) ∉ D.supp}
    {Dμ F G : Divisor Y} (hDμ : D.IsPullback μ hD Dμ)
    (hfree : IsFreeModuloFixedDivisor μ (V : Set X.functionField) Dμ F)
    {s : Finset (MMP.Mori.PrimeDivisor Y)}
    (hsnc : DivisorWithCoeffs.IsSNC (μ ≫ sX) (∑ E ∈ s, Finsupp.single E 1 : Divisor Y))
    (hcoef : ∀ n : ℕ, topologicalKrullDim X = n → ∀ P : MMP.Mori.PrimeDivisor Y,
      ∃ a₀ : ℕ,
        MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) ⟨Y, μ, hY, hμ, P⟩ a₀ ∧
        G.coeff P = ⌈(a₀ : ℝ) - c * F.coeff P⌉ - 1 +
          (if ((a₀ : ℕ) : ℝ) = 0 then 1 else 0) ∧
        (a₀ = 0 → F.coeff P = 0) ∧ (P ∉ s → a₀ = 1 ∧ F.coeff P = 0))
    {U : X.Opens} {g : X.functionField}
    (hg : g ∈ MMP.Intersection.multiplierIdealSections μ G U) :
    g ∈ seriesSet sX Δ D V c U := by
  classical
  haveI : MMP.Mori.IsVariety k sX := hX.1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsProper μ := hlog.isProper
  haveI : MMP.Mori.IsVariety k (μ ≫ sX) := hY.1
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (μ ≫ sX)
  haveI : LocallyOfFiniteType (μ ≫ sX) := hY.1.toLocallyOfFiniteType
  have hsmY : IsSmoothScheme (μ ≫ sX) := hlog.isSmoothScheme
  obtain ⟨hg0, hgP⟩ := hg
  refine ⟨fun hU => hg0 (by rw [hU]; rfl), fun n F₀ a hx ha => ?_⟩
  have hn := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
  obtain ⟨F', hF'p, hval, hcen⟩ := exists_divisorOver_model hX.1 μ hlog.isProper hμ hY F₀
  set y := F'.f F'.E.genericPoint with hy
  have hyU : y ∈ μ ⁻¹ᵁ U := by
    show μ y ∈ U
    rw [hcen]
    exact hx
  have hnY : topologicalKrullDim Y = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (μ ≫ sX) hμ).symm.trans
      hn
  have hval' : ∀ t, F₀.valuation t = F'.valuation (functionFieldMap μ t) := fun t => by
    rw [hval]; rfl
  obtain ⟨g', hg'V, hg'0, hfr⟩ := hfree y
  have := F'.isLocallyNoetherian
  have := F'.isNormal
  have := F'.isIntegral
  have := F'.isBirationalMorphism.isDominant
  have : CompactSpace F'.Y :=
    (F'.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  have hFc : F.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsmY _
  have hBF := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp F'.f F
  obtain ⟨F'', hF''⟩ := hFc.exists_isPullback hBF
  refine ⟨g', hg'V, hg'0, F''.coeff F'.E, ?_, ?_⟩
  · /- `w = ord_{F'}(F)` bounds `ord(g') + ord(D)`, by freeness at the centre. -/
    intro U' φ Z hφ hxU'
    rw [hval']
    set t := functionFieldMap μ (g' * MMP.Threefold.Mori.Helpers.evalFF Z
      (φ : MMP.Mori.RationalFunctions X)) with htdef
    have ht0 : t ≠ 0 := (map_ne_zero _).mpr (mul_ne_zero hg'0 (evalFF_ne_zero Z φ))
    have hnegc : ((-1 : ℤ) • F).IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsmY _
    have hBn := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp F'.f
      ((-1 : ℤ) • F)
    have hpn := hF''.zsmul hFc (-1) hBn
    have hle := valuation_le_exp_of_isPullback (F := F') hnegc (g := t⁻¹) (fun Γ' hΓ' => by
        have hsp : Γ'.genericPoint ⤳ y := by
          rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact hΓ'
        have hμΓ : μ Γ'.genericPoint ∈ U' :=
          (hsp.map μ.continuous).mem_open U'.isOpen (by show μ y ∈ U'; rw [hcen]; exact hxU')
        have e1 : Γ'.divisorialValuation t = WithZero.exp (-F.coeff Γ') := by
          rw [htdef, ← MMP.Mori.PrimeDivisor.valuationOver_apply, Valuation.map_mul,
            hfr Γ' hΓ', valuationOver_evalFF_eq hDμ hφ Γ' hμΓ Z, ← WithZero.exp_add]
          congr 1; ring
        rw [map_inv₀, e1, DivisorWithCoeffs.coeff_smul, smul_eq_mul, ← WithZero.exp_neg]
        simp) _ hBn hpn
    rw [map_inv₀, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at hle
    have hpos : 0 < F'.valuation t := zero_lt_iff.mpr ((map_ne_zero _).mpr ht0)
    have := (inv_le_comm₀ hpos (zero_lt_iff.mpr WithZero.exp_ne_zero)).mp hle
    rw [← WithZero.exp_neg] at this
    simpa using this
  · /- the valuation bound -/
    rcases eq_or_ne g 0 with rfl | hgne
    · simp
    obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme sX hsm hn
    obtain ⟨KY, hKY⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (μ ≫ sX) hsmY hnY
    have hP0 : MMP.Mori.IsPair sX (Divisor.toQDivisor Δ) :=
      ⟨hX, n, K, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩
    obtain ⟨B₀, hB₀⟩ :=
      (MMP.Mori.IsPair.existsUnique_isCrepantBoundary hP0 hK μ hY hμ).1.exists
    have hcr0 := (MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP0 μ hY hμ hK hKY
      (Or.inl hB₀)).2 F' F₀ hval
    obtain ⟨c₀, hc₀⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP0 hK F₀
    have ha₀c : a = 1 + c₀ :=
      MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc₀
        (by rwa [QDivisor.toRDivisor_toQDivisor])
    have hY0 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy
      ((hcr0 c₀).2 hc₀) hF'p
    -- the reduced snc divisor `T = ∑_{P ∈ s} P` on `Y` and `t = a(F', Y, T) ∈ ℕ`
    have hTred : MMP.Intersection.IsReducedEffective (MMP.Intersection.reducedDivisorOf s) :=
      fun P => by rw [MMP.Intersection.coeff_reducedDivisorOf]; split_ifs <;> simp
    obtain ⟨tr, htr⟩ := exists_isLogDiscrepancy hY hsmY hnY
      (Divisor.toQDivisor (MMP.Intersection.reducedDivisorOf s)) F' hF'p
    rw [QDivisor.toRDivisor_toQDivisor] at htr
    obtain ⟨t, rfl⟩ := MMP.Intersection.IsLogDiscrepancy.exists_nat_eq_of_isSNC (μ ≫ sX) hY.1
      hsmY hTred hsnc htr
    choose a₀P ha₀P hGP hzP houtP using hcoef n hn
    have hcart : ∀ P : MMP.Mori.PrimeDivisor Y,
        Divisor.IsCartier (Finsupp.single P (1 : ℤ) : Divisor Y) := fun P =>
      MMP.Fourfold.isCartier_of_isSmoothScheme hsmY _
    choose P' hP' using fun P : MMP.Mori.PrimeDivisor Y => (hcart P).exists_isPullback
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp F'.f
        (Finsupp.single P (1 : ℤ) : Divisor Y))
    set e : MMP.Mori.PrimeDivisor Y → ℤ := fun P => (P' P).coeff F'.E with hedef
    have he : ∀ P ∈ s, ∀ (Q' : Divisor F'.Y) (hB : ∀ Z : irreducibleComponents F'.Y,
          F'.f (componentGenericPoint F'.Y Z) ∉
            DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor Y)),
        Divisor.IsPullback F'.f (Finsupp.single P 1 : Divisor Y) hB Q' →
          Q'.coeff F'.E = e P := by
      intro P _ Q' hB hQ'
      rw [hQ'.eq (hcart P) (hP' P)]
    have he0 : ∀ P ∈ s, 0 ≤ e P := fun P _ =>
      coeff_isPullback_nonneg (F := F') (hcart P) (fun Γ _ => by
        rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]; split_ifs <;> simp) _ _
        (hP' P)
    -- the crepant boundary in terms of the coefficients
    have hB₀Q : ∀ Q, ((B₀.coeff Q : ℚ) : ℝ) = 1 - a₀P Q := by
      intro Q
      have hl := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hB₀ Q)
        hlog.isProper
      rw [QDivisor.toRDivisor_toQDivisor] at hl
      have := MMP.Threefold.Bridges.IsLogDiscrepancy.unique (ha₀P Q) hl
      push_cast at this
      linarith
    have hb0 := toRDivisor_add_sum_eq s (fun P => -(a₀P P : ℝ)) (QDivisor.toRDivisor B₀)
      (fun Q _ => by rw [QDivisor.coeff_toRDivisor, hB₀Q Q]; ring)
      (fun Q hQ => by rw [QDivisor.coeff_toRDivisor, hB₀Q Q, (houtP Q hQ).1]; simp)
    have hsum0 := isLogDiscrepancy_add_sum hsmY htr s (fun P => -(a₀P P : ℝ)) e he
    rw [hb0] at hsum0
    have hA₀ : a = t + ∑ P ∈ s, (a₀P P : ℝ) * e P := by
      have := MMP.Threefold.Bridges.IsLogDiscrepancy.unique hY0 hsum0
      rw [ha₀c, this]
      simp only [neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]
    -- `ord_{F'}(F) = ∑ F_P e_P`
    have hlF1 := isLogDiscrepancy_add_smul htr hFc (1 : ℝ) F'' hBF hF''
    have hlF2 := isLogDiscrepancy_add_sum hsmY htr s (fun P => (F.coeff P : ℝ)) e he
    have hbF : (1 : ℝ) • Divisor.toRDivisor F =
        ∑ P ∈ s, (F.coeff P : ℝ) • Divisor.toRDivisor (Finsupp.single P 1 : Divisor Y) := by
      refine (sum_smul_single_eq s _ _ (fun Q _ => ?_) (fun Q hQ => ?_)).symm
      · rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor]; simp
      · rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, (houtP Q hQ).2]; simp
    rw [hbF] at hlF1
    have hFe : (F''.coeff F'.E : ℝ) = ∑ P ∈ s, (F.coeff P : ℝ) * e P := by
      have := MMP.Threefold.Bridges.IsLogDiscrepancy.unique hlF1 hlF2
      linarith
    -- `v_F(g) ≤ exp (∑ G_P e_P)`
    have hGcart : Divisor.IsCartier (-G) := MMP.Fourfold.isCartier_of_isSmoothScheme hsmY _
    have hBG := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp F'.f (-G)
    obtain ⟨G', hG'⟩ := hGcart.exists_isPullback hBG
    have hR := valuation_le_exp_of_isPullback (F := F') hGcart (g := functionFieldMap μ g)
      (fun Γ hΓ => by
        rw [DivisorWithCoeffs.coeff_neg, neg_neg]
        exact hgP Γ ⟨y, hΓ, hyU⟩) G' hBG hG'
    have hl1 := isLogDiscrepancy_add_smul htr hGcart (1 : ℝ) G' hBG hG'
    have hl2 := isLogDiscrepancy_add_sum hsmY htr s (fun P => -(G.coeff P : ℝ)) e he
    have hG0 : ∀ Q ∉ s, G.coeff Q = 0 := by
      intro Q hQ
      rw [hGP Q, (houtP Q hQ).1, (houtP Q hQ).2]
      simp
    have hbG : (1 : ℝ) • Divisor.toRDivisor (-G) =
        ∑ P ∈ s, (-(G.coeff P : ℝ)) • Divisor.toRDivisor (Finsupp.single P 1 : Divisor Y) := by
      refine (sum_smul_single_eq s _ _ (fun Q _ => ?_) (fun Q hQ => ?_)).symm
      · rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
          DivisorWithCoeffs.coeff_neg]
        simp
      · rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
          DivisorWithCoeffs.coeff_neg, hG0 Q hQ]
        simp
    rw [hbG] at hl1
    have hGe : (G'.coeff F'.E : ℝ) = -∑ P ∈ s, (G.coeff P : ℝ) * e P := by
      have := MMP.Threefold.Bridges.IsLogDiscrepancy.unique hl1 hl2
      simp only [one_mul, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add] at this
      linarith
    have hGe' : G'.coeff F'.E = -∑ P ∈ s, G.coeff P * e P := by exact_mod_cast hGe
    rw [hval']
    refine hR.trans ?_
    rw [hGe', neg_neg, WithZero.exp_le_exp]
    refine sum_mul_le_ceil s a₀P (fun P => (a₀P P : ℝ) - c * F.coeff P) e
      G.coeff t he0 (fun P _ h0 => by simp [h0, hzP P h0])
      (fun P _ => hGP P) hA₀ ?_
    rw [hFe, hA₀, Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun P _ => ?_
    ring

/-- **The adjoint ideal of a linear series is computed by orders along all divisors over `X`.**
The sections of `μ_*𝒪_Y(E - ⌊cF⌋)`, for a log resolution `μ` of `Δ` and of the series `V` with
fixed divisor `F`, are the rational functions satisfying the valuative condition
`SeriesCond` at every divisor over `X` centred in the open set. -/
private theorem eq_seriesSet [IsAlgClosed k] [CharZero k] {Δ D : Divisor X}
    {V : AddSubgroup X.functionField} {c : ℚ} {Y : Scheme.{u}} {μ : Y ⟶ X}
    {J : X.Opens → Set X.functionField}
    (h : IsSeriesAdjointIdealOn sX Δ D V c μ J) : J = seriesSet sX Δ D V c := by
  classical
  obtain ⟨hX, hsm, hΔ, hDc, hVs, hVns, hc, _, _, _, _, hY, hμ, hD, Dμ, F, Γ, E, hDμ,
    ⟨hlog, hfix, hfree, hsncF⟩, hΓ, hE, rfl⟩ := h
  haveI : MMP.Mori.IsVariety k sX := hX.1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsProper μ := hlog.isProper
  haveI : MMP.Mori.IsVariety k (μ ≫ sX) := hY.1
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (μ ≫ sX)
  haveI : LocallyOfFiniteType (μ ≫ sX) := hY.1.toLocallyOfFiniteType
  have hsmY : IsSmoothScheme (μ ≫ sX) := hlog.isSmoothScheme
  obtain ⟨s, hs, hsnc⟩ := exists_finset_of_isSNCSubset (μ ≫ sX) hsmY hsncF
  set G := E - MMP.Intersection.WeilRDivisor.roundDown ((c : ℝ) • Divisor.toRDivisor F)
    with hGdef
  have hVs' : (V : Set X.functionField) ⊆ sectionsIn D := hVs
  /- The coefficients along the prime divisors of `Y`. -/
  have hcoef : ∀ n : ℕ, topologicalKrullDim X = n → ∀ P : MMP.Mori.PrimeDivisor Y,
      ∃ a₀ : ℕ,
        MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) ⟨Y, μ, hY, hμ, P⟩ a₀ ∧
        G.coeff P = ⌈(a₀ : ℝ) - c * F.coeff P⌉ - 1 +
          (if ((a₀ : ℕ) : ℝ) = 0 then 1 else 0) ∧
        (a₀ = 0 → F.coeff P = 0) ∧ (P ∉ s → a₀ = 1 ∧ F.coeff P = 0) := by
    intro n hn P
    set FP : DivisorOver k sX := ⟨Y, μ, hY, hμ, P⟩ with hFPdef
    have hFPp : IsProper FP.f := hlog.isProper
    obtain ⟨n', a', hla', hEP⟩ := hE P
    obtain ⟨a₀r, ha₀r⟩ := exists_isLogDiscrepancy hX hsm hn (Divisor.toQDivisor Δ) FP hFPp
    rw [QDivisor.toRDivisor_toQDivisor] at ha₀r
    have ha' : a' = a₀r := MMP.Threefold.Bridges.IsLogDiscrepancy.unique hla' ha₀r
    obtain ⟨a₀, rfl⟩ :=
      MMP.Intersection.IsLogDiscrepancy.exists_nat_eq_of_isSNC sX hX.1 hsm hΔ.1 hΔ.2 ha₀r
    have hF0 : 0 ≤ F.coeff P :=
      coeff_nonneg_of_isFixedDivisorOfPullback hDc hVs' hDμ hfix P hY hμ
    refine ⟨a₀, ha₀r, ?_, ?_, ?_⟩
    · have hΓP : Γ.coeff P = if ((a₀ : ℕ) : ℝ) = 0 then 1 else 0 := by
        rcases hΓ.1 P with h0 | h1
        · rw [h0]
          split_ifs with ha0
          · exfalso
            have : Γ.coeff P = 1 := (hΓ.2 P).2 ⟨n, by rwa [ha0] at ha₀r⟩
            omega
          · rfl
        · rw [h1]
          split_ifs with ha0
          · rfl
          · exfalso
            obtain ⟨n'', h''⟩ := (hΓ.2 P).1 h1
            exact ha0 (MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha₀r h'')
      have hE' : E.coeff P = (a₀ : ℤ) - 1 + Γ.coeff P := by
        rw [ha'] at hEP
        exact_mod_cast hEP
      have hfl : ⌊(c : ℝ) * F.coeff P⌋ = (a₀ : ℤ) - ⌈(a₀ : ℝ) - c * F.coeff P⌉ := by
        have e : (c : ℝ) * F.coeff P = ((a₀ : ℤ) : ℝ) + -((a₀ : ℝ) - c * F.coeff P) := by
          push_cast; ring
        conv_lhs => rw [e]
        rw [Int.floor_intCast_add, Int.floor_neg]
        ring
      rw [hGdef, DivisorWithCoeffs.coeff_sub, MMP.Intersection.WeilRDivisor.coeff_roundDown,
        DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul, hfl, hE', hΓP]
      split_ifs <;> ring
    · intro h0
      subst h0
      have hx := notMem_of_isLogDiscrepancy_eq_zero hX hsm hΔ
        (fun x hx => closure_subset_baseLocusIn hx) hVns (F := FP) (by simpa using ha₀r)
      exact le_antisymm (coeff_nonpos_of_notMem_baseLocusIn hDc hVs' hDμ hfix P hY hμ hx) hF0
    · intro hPs
      have hPmem := MMP.Flips.primeDivisor_genericPoint_mem_support P
      have hnot : P.genericPoint ∉ (⋃ E ∈ s, E.support) := by
        intro hz
        obtain ⟨E', hE's, hPE'⟩ := Set.mem_iUnion₂.mp hz
        exact hPs (by rwa [← MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hPE'])
      rw [hs, Closeds.coe_sup, Closeds.coe_sup, Set.mem_union, Set.mem_union, not_or,
        not_or] at hnot
      obtain ⟨⟨hexc, hsuppΔ⟩, hsuppF⟩ := hnot
      have hsuppΔ' : μ P.genericPoint ∉ (DivisorWithCoeffs.supp
          (QDivisor.toRDivisor (Divisor.toQDivisor Δ)) : Set X) := by
        intro hmem
        apply hsuppΔ
        obtain ⟨Γ', hΓ', hxΓ'⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
        refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨Γ', ?_, hxΓ'⟩
        rw [QDivisor.coeff_toRDivisor, Divisor.coeff_toQDivisor] at hΓ'
        exact_mod_cast hΓ'
      have h1 := isLogDiscrepancy_one_of_notMem sX hX hsm hn hY hμ hlog.isProper
        (Divisor.toQDivisor Δ) P hexc hsuppΔ'
      rw [QDivisor.toRDivisor_toQDivisor] at h1
      have := MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha₀r h1
      refine ⟨by exact_mod_cast this, ?_⟩
      by_contra hne
      exact hsuppF (DivisorWithCoeffs.support_subset_supp hne hPmem)
  funext U
  ext g
  refine ⟨mem_seriesSet_of_mem_multiplierIdealSections sX hX hsm hY hμ hlog hDμ hfree hsnc
    hcoef, fun hg => mem_multiplierIdealSections_of_mem_seriesSet sX hY hμ hDc hDμ hfix hc
    (fun P => ?_) hg⟩
  obtain ⟨n, a, hla, -⟩ := hE P
  obtain ⟨a₀, ha₀, hGP, -⟩ :=
    hcoef n (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hla) P
  exact ⟨n, a₀, ha₀, hGP⟩

end SeriesMain

/-! ### Operations on the valuative description -/

section SeriesOps

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

omit [IsNormal X] in
/-- `v_z(a b⁻¹) = v_z(a) - v_z(b)`. -/
private theorem ord_mul_inv {a b : X.functionField} (ha : a ≠ 0) (hb : b ≠ 0) (z : X) :
    X.ord (a * b⁻¹) z = X.ord a z - X.ord b z := by
  rw [← zpow_neg_one b, Scheme.ord_mul ha (zpow_ne_zero _ hb), MMP.Mori.ord_zpow _ hb]
  ring

/-- **Passing to a multiple of the series.** If `g ^ m ∈ V'` for every `g ∈ V`, the
valuative description for `(D, V, c)` is contained in the one for `(mD, V', c/m)`. -/
private theorem seriesSet_subset_nsmul {Δ D : Divisor X} {V V' : Set X.functionField} {c : ℚ}
    {m : ℕ} (hm : 0 < m) (hDc : D.IsCartier) (hV : ∀ g ∈ V, g ^ m ∈ V') (U : X.Opens) :
    seriesSet sX Δ D V c U ⊆ seriesSet sX Δ ((m : ℤ) • D) V' (c / m) U := by
  rintro g ⟨hg0, hg⟩
  refine ⟨hg0, fun n G a hx ha => ?_⟩
  obtain ⟨g', hg'V, hg'0, w, hw, hv⟩ := hg n G a hx ha
  refine ⟨g' ^ m, hV _ hg'V, pow_ne_zero _ hg'0, m * w, fun U' φ' Z hφ' hxU' => ?_, ?_⟩
  · obtain ⟨U'', hxU'', φ, hφ⟩ := hDc (G.f G.E.genericPoint)
    have h1 := hw U'' φ Z hφ hxU''
    have hφm := hφ.zsmul (m : ℤ)
    rw [zpow_natCast] at hφm
    set e := MMP.Threefold.Mori.Helpers.evalFF Z (φ : MMP.Mori.RationalFunctions X)
    set e' := MMP.Threefold.Mori.Helpers.evalFF Z (φ' : MMP.Mori.RationalFunctions X)
    have he : e ≠ 0 := evalFF_ne_zero Z φ
    have he' : e' ≠ 0 := evalFF_ne_zero Z φ'
    have hem : MMP.Threefold.Mori.Helpers.evalFF Z ((φ ^ m : (MMP.Mori.RationalFunctions X)ˣ) :
        MMP.Mori.RationalFunctions X) = e ^ m := by
      rw [Units.val_pow_eq_pow_val, map_pow]
    have hu : G.valuation (e' * (e ^ m)⁻¹) = 1 := by
      refine valuation_eq_one_of_forall_ord_eq_zero G (mul_ne_zero he' (inv_ne_zero
        (pow_ne_zero _ he))) fun Γ hΓ => ?_
      rw [ord_mul_inv he' (pow_ne_zero _ he), ord_evalFF_of_isLocalEquation hφ' Z Γ ⟨_, hΓ, hxU'⟩,
        ← hem, ord_evalFF_of_isLocalEquation hφm Z Γ ⟨_, hΓ, hxU''⟩]
      ring
    have e2 : g' ^ m * e' = (g' * e) ^ m * (e' * (e ^ m)⁻¹) := by
      field_simp
      ring
    have e3 : WithZero.exp (-((m : ℤ) * w)) = WithZero.exp (-w) ^ m := by
      rw [← WithZero.exp_nsmul]
      congr 1
      simp
    rw [e2, Valuation.map_mul, hu, mul_one, Valuation.map_pow, e3]
    exact pow_le_pow_left₀ zero_le' h1 m
  · have e1 : ((c / m : ℚ) : ℝ) * (((m : ℤ) * w : ℤ) : ℝ) = (c : ℝ) * w := by
      have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      push_cast
      field_simp
    rw [e1]
    exact hv

/-- **Antitonicity in the boundary and the coefficient.** For `Δ ≤ Δ'` reduced snc and
`0 ≤ c ≤ c'`, the valuative description for `(Δ', c')` is contained in the one for `(Δ, c)`. -/
private theorem seriesSet_anti (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    {Δ Δ' D : Divisor X} (hΔ : IsReducedSNC sX Δ) (hΔ' : IsReducedSNC sX Δ') (hle : Δ ≤ Δ')
    {V : Set X.functionField} (hVs : V ⊆ sectionsIn D) (hDc : D.IsCartier) {c c' : ℚ}
    (hc : 0 ≤ c) (hcc : c ≤ c') [IsAlgClosed k] [CharZero k] (U : X.Opens) :
    seriesSet sX Δ' D V c' U ⊆ seriesSet sX Δ D V c U := by
  rintro g ⟨hg0, hg⟩
  refine ⟨hg0, fun n G a hx ha => ?_⟩
  have := G.isLocallyNoetherian
  have := G.isNormal
  have := G.isIntegral
  have := G.isBirationalMorphism.isDominant
  have : CompactSpace G.Y := (G.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  have hC₁ : Divisor.IsCartier (Δ' - Δ) := MMP.Fourfold.isCartier_of_isSmoothScheme hsm _
  have hB₁ := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp G.f (Δ' - Δ)
  obtain ⟨C₁', hC₁'⟩ := hC₁.exists_isPullback hB₁
  have hc1 : 0 ≤ C₁'.coeff G.E := coeff_isPullback_nonneg hC₁ (fun Γ _ => by
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_apply,
      DivisorWithCoeffs.coeff_apply]
    linarith [hle Γ]) C₁' hB₁ hC₁'
  have ha' := isLogDiscrepancy_add_smul ha hC₁ 1 C₁' hB₁ hC₁'
  have e1 : Divisor.toRDivisor Δ + (1 : ℝ) • Divisor.toRDivisor (Δ' - Δ) =
      Divisor.toRDivisor Δ' := by
    rw [one_smul, map_sub]; abel
  rw [e1] at ha'
  obtain ⟨g', hg'V, hg'0, w, hw, hv⟩ := hg n G _ hx ha'
  refine ⟨g', hg'V, hg'0, w, hw, hv.trans (WithZero.exp_le_exp.mpr ?_)⟩
  have hw0 := nonneg_of_forall_exp_neg_le _ hDc (hVs hg'V) hw
  obtain ⟨p, hp⟩ :=
    MMP.Intersection.IsLogDiscrepancy.exists_nat_eq_of_isSNC sX hX.1 hsm hΔ.1 hΔ.2 ha
  obtain ⟨p', hp'⟩ :=
    MMP.Intersection.IsLogDiscrepancy.exists_nat_eq_of_isSNC sX hX.1 hsm hΔ'.1 hΔ'.2 ha'
  have key := ceil_add_ite_le_of_le (a := a - c * w) hp hp' (by exact_mod_cast hc1)
    (c₂ := ((c' : ℝ) - c) * w) (mul_nonneg (by exact_mod_cast sub_nonneg.mpr hcc)
      (by exact_mod_cast hw0))
  rw [show a - 1 * (C₁'.coeff G.E : ℝ) - (c' : ℝ) * w =
    a - c * w - 1 * (C₁'.coeff G.E : ℝ) - ((c' : ℝ) - c) * w by ring]
  exact key

/-- **The valuative description consists of regular functions.** -/
private theorem seriesSet_subset_range [PerfectField k] (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {Δ D : Divisor X} (hΔ : IsReducedSNC sX Δ)
    {V : Set X.functionField} (hVs : V ⊆ sectionsIn D) (hDc : D.IsCartier) {c : ℚ}
    (hc : 0 ≤ c) (U : X.Opens) [Nonempty U] :
    seriesSet sX Δ D V c U ⊆ Set.range (X.germToFunctionField U) := by
  intro g hg
  rcases eq_or_ne g 0 with rfl | hg0
  · exact ⟨0, map_zero _⟩
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq sX hX.1
  refine (MMP.Intersection.exists_germToFunctionField_eq_iff_forall_zero_le_ord U hg0).mpr
    fun Q hQ => ?_
  have hxU : (DivisorOver.ofPrimeDivisor k hX Q).f
      (DivisorOver.ofPrimeDivisor k hX Q).E.genericPoint ∈ U :=
    MMP.Intersection.genericPoint_mem_of_support_inter_nonempty Q hQ
  have h0 := isLogDiscrepancy_ofPrimeDivisor sX hX hsm hn (Divisor.toQDivisor Δ) Q
  rw [QDivisor.toRDivisor_toQDivisor] at h0
  obtain ⟨g', hg'V, -, w, hw, hv⟩ := hg.2 n _ _ hxU h0
  have hw0 := nonneg_of_forall_exp_neg_le _ hDc (hVs hg'V) hw
  rw [valuation_ofPrimeDivisor] at hv
  have hle1 : Q.divisorialValuation g ≤ 1 := by
    refine hv.trans ?_
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    refine ceil_sub_one_add_ite_nonpos ?_ ?_
    · rw [Divisor.coeff_toQDivisor]
      rcases hΔ.1 Q with h | h <;> rw [h] <;> norm_num
    · have : (0 : ℝ) ≤ (c : ℝ) * w :=
        mul_nonneg (by exact_mod_cast hc) (by exact_mod_cast hw0)
      linarith
  rw [Q.divisorialValuation_eq_exp_neg_ord hg0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    at hle1
  omega

/-- The valuative description restricts to smaller non-empty opens. -/
private theorem seriesSet_mono_open {Δ D : Divisor X} {V : Set X.functionField} {c : ℚ}
    {U W : X.Opens} (hWU : W ≤ U) (hW : W ≠ ⊥) :
    seriesSet sX Δ D V c U ⊆ seriesSet sX Δ D V c W :=
  fun _ hg => ⟨fun h => absurd h hW, fun n G a hx => hg.2 n G a (hWU hx)⟩

/-- **The valuative description is local.** A comparison of two valuative descriptions on the
non-empty affine opens inside `U` gives the comparison on `U`. -/
private theorem seriesSet_subset_of_affine {Δ Δ' D D' : Divisor X} {V V' : Set X.functionField}
    {c c' : ℚ} {U : X.Opens}
    (h : ∀ W : X.affineOpens, (W : X.Opens) ≤ U → Nonempty (W : X.Opens) →
      seriesSet sX Δ D V c W ⊆ seriesSet sX Δ' D' V' c' W) :
    seriesSet sX Δ D V c U ⊆ seriesSet sX Δ' D' V' c' U := by
  intro g hg
  refine ⟨hg.1, fun n G a hx ha => ?_⟩
  obtain ⟨W, hW, hxW, hWU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (Scheme.isBasis_affineOpens X)) hx
  have hW0 : (W : X.Opens) ≠ ⊥ :=
    (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mpr ⟨_, hxW⟩
  exact (h ⟨W, hW⟩ hWU ⟨⟨_, hxW⟩⟩ (seriesSet_mono_open sX hWU hW0 hg)).2 n G a hxW ha

end SeriesOps

/-! ### Stabilization of the asymptotic adjoint ideal -/

section Asymptotic

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {Z : Scheme.{u}} (f : X ⟶ Z)

/-- In a graded linear series, `g ∈ V_p` gives `g ^ m ∈ V_{pm}`. -/
private theorem pow_mem_of_isGradedLinearSeries {D : Divisor X}
    {V : ℕ → AddSubgroup X.functionField} (hV : IsGradedLinearSeries f D V) {p : ℕ}
    {g : X.functionField} (hg : g ∈ V p) (m : ℕ) : g ^ m ∈ V (p * m) := by
  induction m with
  | zero => simpa using hV.2.2.1
  | succ m ih =>
    rw [pow_succ, Nat.mul_succ]
    exact hV.2.2.2 _ _ _ _ ih hg

/-- **The valuative descriptions increase along divisibility.** For a graded linear series `V_•`
of the Cartier divisor `D` and `p ∣ q`, the description of `𝒥_{Δ,(c/p)V_p}` is contained in the
one of `𝒥_{Δ,(c/q)V_q}`. -/
private theorem seriesSet_subset_of_dvd {Δ D : Divisor X} {V : ℕ → AddSubgroup X.functionField}
    (hV : IsGradedLinearSeries f D V) (hDc : D.IsCartier) {c : ℚ} {p q : ℕ} (hp : 0 < p)
    (hq : 0 < q) (hpq : p ∣ q) (U : X.Opens) :
    seriesSet sX Δ ((p : ℤ) • D) (V p) (c / p) U ⊆
      seriesSet sX Δ ((q : ℤ) • D) (V q) (c / q) U := by
  obtain ⟨m, rfl⟩ := hpq
  have hm : 0 < m := Nat.pos_of_mul_pos_left hq
  have h := seriesSet_subset_nsmul sX (Δ := Δ) (V := (V p : Set X.functionField))
    (V' := (V (p * m) : Set X.functionField)) (c := c / p) hm (hDc.zsmul p)
    (fun g hg => pow_mem_of_isGradedLinearSeries f hV hg m) U
  have e1 : (m : ℤ) • ((p : ℤ) • D) = (((p * m : ℕ) : ℤ)) • D := by
    rw [smul_smul]; push_cast; ring_nf
  have e2 : c / (p : ℚ) / (m : ℚ) = c / ((p * m : ℕ) : ℚ) := by
    push_cast; rw [div_div]
  rwa [e1, e2] at h

/-- **Stabilization.** For the asymptotic adjoint ideal `𝒥_{Δ,cV_•}`, some `p₀ ∈ bℤ_{>0}` has the
valuative description of `𝒥_{Δ,(c/q)V_q}` independent of `q` for all positive multiples `q` of
`p₀`, and that description is given on non-empty affine opens by an ideal sheaf. -/
private theorem exists_seriesSet_stabilizes [IsAlgClosed k] [CharZero k] {Δ D : Divisor X}
    {V : ℕ → AddSubgroup X.functionField} {b : ℕ} {c : ℚ} {J : X.Opens → Set X.functionField}
    (h : IsAsymptoticAdjointIdeal sX f Δ D V b c J) :
    ∃ p₀ : ℕ, 0 < p₀ ∧ b ∣ p₀ ∧
      (∃ I : X.IdealSheafData, ∀ (U : X.affineOpens) [Nonempty (U : X.Opens)],
        seriesSet sX Δ ((p₀ : ℤ) • D) (V p₀) (c / p₀) U =
          X.germToFunctionField (U : X.Opens) '' (I.ideal U : Set Γ(X, U))) ∧
      ∀ q : ℕ, 0 < q → p₀ ∣ q → ∀ (U : X.Opens), Nonempty U →
        seriesSet sX Δ ((q : ℤ) • D) (V q) (c / q) U =
          seriesSet sX Δ ((p₀ : ℤ) • D) (V p₀) (c / p₀) U := by
  classical
  obtain ⟨-, -, hX, hsm, hΔ, hDc, hgr, hb, -, -, hc, Jp, hJp, -⟩ := h
  haveI : MMP.Mori.IsVariety k sX := hX.1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  set S : ℕ → X.Opens → Set X.functionField :=
    fun p => seriesSet sX Δ ((p : ℤ) • D) (V p) (c / p) with hSdef
  have hS : ∀ p, 0 < p → b ∣ p → Jp p = S p := fun p hp hbp => by
    obtain ⟨Y, μ, hOn⟩ := hJp p hp hbp
    exact eq_seriesSet sX hOn
  have hrange : ∀ p, 0 < p → ∀ (U : X.Opens) [Nonempty U],
      S p U ⊆ Set.range (X.germToFunctionField U) := fun p hp U _ =>
    seriesSet_subset_range sX hX hsm hΔ (hgr.1 p) (hDc.zsmul p)
      (div_nonneg hc.le (Nat.cast_nonneg _)) U
  have hI : ∀ p, 0 < p → b ∣ p → ∃ I : X.IdealSheafData, ∀ (U : X.affineOpens)
      [Nonempty (U : X.Opens)], S p U = X.germToFunctionField (U : X.Opens) ''
        (I.ideal U : Set Γ(X, U)) := by
    intro p hp hbp
    obtain ⟨Y, μ, hOn⟩ := hJp p hp hbp
    obtain ⟨-, -, -, -, -, -, -, i1, i2, i3, i4, -, -, -, Dμ, F, Γ, E, -, -, -, -, hJeq⟩ := hOn
    obtain ⟨I, hIeq⟩ := exists_idealSheafData_of_subset_range μ _ (fun U _ => by
      rw [← hJeq, hS p hp hbp]; exact hrange p hp U)
    exact ⟨I, fun U _ => by rw [← hS p hp hbp, hJeq]; exact hIeq U⟩
  -- the chain `p_m = b · m!`
  set pm : ℕ → ℕ := fun m => b * m.factorial with hpmdef
  have hpm0 : ∀ m, 0 < pm m := fun m => Nat.mul_pos hb (Nat.factorial_pos m)
  have hbpm : ∀ m, b ∣ pm m := fun m => dvd_mul_right b _
  choose I hIeq using hI
  set Im : ℕ → X.IdealSheafData := fun m => I (pm m) (hpm0 m) (hbpm m) with hImdef
  have hmono : ∀ (U : X.affineOpens), Nonempty (U : X.Opens) → ∀ m,
      (Im m).ideal U ≤ (Im (m + 1)).ideal U := by
    intro U hU m a ha
    have h1 : X.germToFunctionField (U : X.Opens) a ∈ S (pm m) U := by
      rw [hIeq (pm m) (hpm0 m) (hbpm m) U]; exact ⟨a, ha, rfl⟩
    have h2 := seriesSet_subset_of_dvd sX f hgr hDc (hpm0 m) (hpm0 (m + 1))
      (mul_dvd_mul_left b (Nat.factorial_dvd_factorial (Nat.le_succ m))) U h1
    change _ ∈ S (pm (m + 1)) U at h2
    rw [hIeq (pm (m + 1)) (hpm0 (m + 1)) (hbpm (m + 1)) U] at h2
    obtain ⟨a', ha', he⟩ := h2
    rwa [← Scheme.germToFunctionField_injective X (U : X.Opens) he]
  -- a finite affine cover
  have hcov : ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) := fun x => by
    obtain ⟨W, hW, hxW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (Scheme.isBasis_affineOpens X)) (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨⟨W, hW⟩, hxW⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U : Set X))
    (fun U => (U : X.Opens).isOpen) (fun x _ => Set.mem_iUnion.mpr (hcov x))
  have hstab : ∀ (U : X.affineOpens) (hU : Nonempty (U : X.Opens)), ∃ n, ∀ m, n ≤ m →
      (Im n).ideal U = (Im m).ideal U := fun U hU =>
    (monotone_stabilizes_iff_noetherian (R := Γ(X, U)) (M := Γ(X, U))).mpr
      (IsLocallyNoetherian.component_noetherian U)
      ⟨fun m => (Im m).ideal U, monotone_nat_of_le_succ (hmono U hU)⟩
  set Ng : X.affineOpens → ℕ := fun U => if hU : Nonempty (U : X.Opens) then
    (hstab U hU).choose else 0 with hNgdef
  set N := t.sup Ng with hNdef
  have hIN : ∀ m, N ≤ m → Im m = Im N := by
    intro m hm
    refine Scheme.IdealSheafData.ext_of_iSup_eq_top (ι := {U : X.affineOpens //
      U ∈ t ∧ Nonempty (U : X.Opens)}) (fun i => i.1) ?_ fun i => ?_
    · refine eq_top_iff.mpr fun x _ => ?_
      obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hUt, ⟨⟨x, hxU⟩⟩⟩, hxU⟩
    · obtain ⟨U, hUt, hU⟩ := i
      have hle : Ng U ≤ N := Finset.le_sup hUt
      have hNg : Ng U = (hstab U hU).choose := by rw [hNgdef]; exact dif_pos hU
      have h1 := (hstab U hU).choose_spec m (hNg ▸ hle.trans hm)
      have h2 := (hstab U hU).choose_spec N (hNg ▸ hle)
      exact h1.symm.trans h2
  refine ⟨pm N, hpm0 N, hbpm N, ⟨Im N, fun U _ => hIeq (pm N) (hpm0 N) (hbpm N) U⟩,
    fun q hq hNq U hU => ?_⟩
  have hbq : b ∣ q := (hbpm N).trans hNq
  set M := max N q
  have hqM : q ∣ pm M := dvd_mul_of_dvd_right (Nat.dvd_factorial hq (le_max_right N q)) b
  have haff : ∀ W : X.affineOpens, Nonempty (W : X.Opens) → S q W = S (pm N) W := by
    intro W hW
    refine le_antisymm (fun g hg => ?_)
      (seriesSet_subset_of_dvd sX f hgr hDc (hpm0 N) hq hNq W)
    have h1 := seriesSet_subset_of_dvd sX f hgr hDc hq (hpm0 M) hqM W hg
    change g ∈ S (pm M) W at h1
    have hIM : I (pm M) (hpm0 M) (hbpm M) = I (pm N) (hpm0 N) (hbpm N) :=
      hIN M (le_max_left N q)
    rw [hIeq (pm M) (hpm0 M) (hbpm M) W, hIM] at h1
    change g ∈ S (pm N) W
    rwa [hIeq (pm N) (hpm0 N) (hbpm N) W]
  exact le_antisymm (seriesSet_subset_of_affine sX fun W _ hW => (haff W hW).le)
    (seriesSet_subset_of_affine sX fun W _ hW => (haff W hW).ge)

end Asymptotic

/-! ### Restriction of a principal divisor to a smooth prime divisor -/

section Restriction

variable {k : Type u} [Field k] {X T : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [Smooth sX] (j : T ⟶ X) [IsClosedImmersion j]
  [IsIntegral T] [IsLocallyNoetherian T] [Smooth (j ≫ sX)]

omit [IsNormal X] [Smooth sX] [IsClosedImmersion j] [IsLocallyNoetherian T]
  [Smooth (j ≫ sX)] in
/-- An element of the stalk at `j(η_Q)` whose generization to `j(η_T)` is a unit has nonzero
restriction to `𝒪_{T,Q}`. -/
private theorem stalkMap_ne_zero_of_isUnit (Q : MMP.Mori.PrimeDivisor T)
    (hsp : j (genericPoint T) ⤳ j Q.genericPoint) (r : X.presheaf.stalk (j Q.genericPoint))
    (hr : IsUnit ((X.presheaf.stalkSpecializes hsp).hom r)) :
    (j.stalkMap Q.genericPoint).hom r ≠ 0 := by
  intro h0
  have h1 := Scheme.Hom.stalkSpecializes_stalkMap_apply j (genericPoint T) Q.genericPoint
    (genericPoint_specializes Q.genericPoint) r
  rw [h0, map_zero] at h1
  exact (hr.map (j.stalkMap (genericPoint T)).hom).ne_zero h1

include sX in
/-- **The restriction of a principal divisor.** Let `j : T ⟶ X` be a smooth integral closed
subscheme of a smooth `X`, `u ∈ K(X)` a unit at the generic point of `T`, and `u|_T` its
restriction. For every prime divisor `Q` of `T`,
`ord_Q(u|_T) = ∑_E length(𝒪_{T,Q}/I_E 𝒪_{T,Q}) · ord_E(u)`, the sum over any finite set of prime
divisors `E` of `X` containing those along which `u` has nonzero order. -/
public theorem _root_.MMP.Mori.PrimeDivisor.ord_restrict_eq_sum_intersectionLength_mul_ord
    (a : X.presheaf.stalk (j (genericPoint T))) (ha : IsUnit a)
    (Q : MMP.Mori.PrimeDivisor T) (s : Finset (MMP.Mori.PrimeDivisor X))
    (hs : ∀ E : MMP.Mori.PrimeDivisor X,
      X.ord (algebraMap _ X.functionField a) E.genericPoint ≠ 0 → E ∈ s) :
    T.ord ((j.stalkMap (genericPoint T)).hom a) Q.genericPoint =
      ∑ E ∈ s, (E.intersectionLength j Q : ℤ) *
        X.ord (algebraMap _ X.functionField a) E.genericPoint := by
  classical
  have hsp : j (genericPoint T) ⤳ j Q.genericPoint :=
    (genericPoint_specializes Q.genericPoint).map j.continuous
  have hmem : j (genericPoint T) ∈ Set.range (X.fromSpecStalk (j Q.genericPoint)) := by
    rwa [Scheme.range_fromSpecStalk]
  obtain ⟨q, hq⟩ := hmem
  letI : Algebra (X.presheaf.stalk (j Q.genericPoint)) (X.presheaf.stalk (j (genericPoint T))) :=
    (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
  haveI := Stacks.Chow.isLocalization_stalk_of_specializes hsp q hq
  obtain ⟨⟨r₁, s₂⟩, hrs⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl a
  change IsLocalization.mk' _ r₁ s₂ = a at hrs
  set r₂ : X.presheaf.stalk (j Q.genericPoint) := s₂.1 with hr₂
  have hspec : a * (X.presheaf.stalkSpecializes hsp).hom r₂ =
      (X.presheaf.stalkSpecializes hsp).hom r₁ := by
    have := IsLocalization.mk'_spec (X.presheaf.stalk (j (genericPoint T))) r₁ s₂
    rwa [hrs] at this
  have hu₂ : IsUnit ((X.presheaf.stalkSpecializes hsp).hom r₂) :=
    IsLocalization.map_units (X.presheaf.stalk (j (genericPoint T))) s₂
  have hu₁ : IsUnit ((X.presheaf.stalkSpecializes hsp).hom r₁) := hspec ▸ ha.mul hu₂
  have hn₁ := stalkMap_ne_zero_of_isUnit j Q hsp r₁ hu₁
  have hn₂ := stalkMap_ne_zero_of_isUnit j Q hsp r₂ hu₂
  -- the comparison on `X`
  set u := algebraMap _ X.functionField a with hu
  have hX₁ : algebraMap _ X.functionField r₁ = u * algebraMap _ X.functionField r₂ := by
    rw [← MMP.Mori.algebraMap_stalkSpecializes hsp, ← MMP.Mori.algebraMap_stalkSpecializes hsp,
      ← hspec, map_mul]
  have hne : ∀ b : X.presheaf.stalk (j (genericPoint T)), IsUnit b →
      algebraMap _ X.functionField b ≠ 0 := fun b hb => (hb.map _).ne_zero
  have hu0 : u ≠ 0 := hne a ha
  have hr₂0 : algebraMap _ X.functionField r₂ ≠ 0 := by
    rw [← MMP.Mori.algebraMap_stalkSpecializes hsp]; exact hne _ hu₂
  have hordX : ∀ E : MMP.Mori.PrimeDivisor X,
      X.ord u E.genericPoint = X.ord (algebraMap _ X.functionField r₁) E.genericPoint -
        X.ord (algebraMap _ X.functionField r₂) E.genericPoint := by
    intro E
    rw [hX₁, Scheme.ord_mul hu0 hr₂0]
    ring
  -- the comparison on `T`
  set uT := (j.stalkMap (genericPoint T)).hom a with huT
  have hT₁ : algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom r₁) =
      uT * algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom r₂) := by
    change (T.presheaf.stalkSpecializes _).hom _ = uT * (T.presheaf.stalkSpecializes _).hom _
    rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply, ← Scheme.Hom.stalkSpecializes_stalkMap_apply,
      huT, ← map_mul, hspec]
  have huT0 : uT ≠ 0 := (ha.map (j.stalkMap (genericPoint T)).hom).ne_zero
  have hT₂0 : algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom r₂) ≠ 0 := by
    change (T.presheaf.stalkSpecializes _).hom _ ≠ 0
    rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply]
    exact (hu₂.map (j.stalkMap (genericPoint T)).hom).ne_zero
  have hordT : T.ord uT Q.genericPoint =
      T.ord (algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom r₁)) Q.genericPoint -
        T.ord (algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom r₂))
          Q.genericPoint := by
    rw [hT₁, Scheme.ord_mul huT0 hT₂0]
    ring
  obtain ⟨S₁, hS₁, hf₁⟩ := Q.ord_stalkMap_eq_sum_intersectionLength_mul_ord sX j r₁ hn₁
  obtain ⟨S₂, hS₂, hf₂⟩ := Q.ord_stalkMap_eq_sum_intersectionLength_mul_ord sX j r₂ hn₂
  set Sa := s ∪ S₁ ∪ S₂ with hSa
  have hite : ∀ (r : X.presheaf.stalk (j Q.genericPoint)) (E : MMP.Mori.PrimeDivisor X),
      (if j Q.genericPoint ∈ E.support then (E.intersectionLength j Q : ℤ) *
        X.ord (algebraMap _ X.functionField r) E.genericPoint else 0) =
      (E.intersectionLength j Q : ℤ) * X.ord (algebraMap _ X.functionField r) E.genericPoint := by
    intro r E
    split_ifs with hE
    · rfl
    · rw [MMP.Mori.PrimeDivisor.intersectionLength_eq_zero_of_notMem j E hE]; simp
  have e₁ := hf₁ Sa (by intro E hE; simp [Sa, hE])
  have e₂ := hf₂ Sa (by intro E hE; simp [Sa, hE])
  simp only [hite] at e₁ e₂
  rw [hordT, e₁, e₂, ← Finset.sum_sub_distrib]
  rw [← Finset.sum_subset (s₁ := s) (s₂ := Sa) (by intro E hE; simp [Sa, hE]) (by
    intro E _ hE
    by_contra hne'
    exact hE (hs E (by
      intro h0
      apply hne'
      rw [hordX E] at h0
      rw [← mul_sub, h0, mul_zero])))]
  · refine Finset.sum_congr rfl fun E _ => ?_
    rw [hordX E, mul_sub]

end Restriction

/-! ### The image of restriction -/

section Image

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **The image of restriction lies in the twisted asymptotic adjoint ideal.** On a smooth `X`,
let `S` be a prime divisor, `D` a Cartier divisor of which `S` is not a component, and
`𝒥 = 𝒥_{Θ,‖D‖_S}`. The restriction `h ∈ K(S)` of a section `g` of `𝒪_X(D)` is, near every point
of `S`, a section of `𝒪_S(D|_S) ⊗ 𝒥`. -/
private theorem exists_mem_span_of_isRestrictionAlong [IsAlgClosed k] [CharZero k]
    {Z : Scheme.{u}} (f : X ⟶ Z) (hsm : IsSmoothScheme sX) (Δ D : Divisor X)
    (S : MMP.Mori.PrimeDivisor X) (b : ℕ) :
    haveI := S.integral
    ∀ [IsLocallyNoetherian S.idealSheaf.subscheme] [IsNormal S.idealSheaf.subscheme]
      (J : S.idealSheaf.subscheme.Opens → Set S.idealSheaf.subscheme.functionField),
      D.IsCartier → D.coeff S = 0 → IsRestrictedAsymptoticAdjointIdeal sX f Δ D S b 1 J →
      ∀ g ∈ sectionsIn D, ∀ h : S.idealSheaf.subscheme.functionField, IsRestrictionAlong S g h →
        ∀ x : S.idealSheaf.subscheme, ∃ W : S.idealSheaf.subscheme.Opens, x ∈ W ∧
          h ∈ Submodule.span ℤ (MMP.Intersection.multiplierIdealSections
            (𝟙 S.idealSheaf.subscheme) (D.restrictPrimeDivisor S) W * J W) := by
  haveI := S.integral
  intro _ _ J hDc hDS hJ g hg h hres x
  classical
  rcases eq_or_ne h 0 with rfl | hh0
  · exact ⟨⊤, trivial, Submodule.zero_mem _⟩
  obtain ⟨hcX, hLN, hN, φ, hφS, hasym⟩ := hJ
  obtain ⟨-, -, hXT, hsmT, hΘ, hD₁c, -, hb, -, -, -, Jp, hJp, hJT⟩ := hasym
  set D₁ := D + principalDivisor φ with hD₁def
  haveI : Smooth sX := MMP.Mori.IsSmoothScheme.smooth hsm
  haveI : Smooth (S.idealSheaf.subschemeι ≫ sX) := MMP.Mori.IsSmoothScheme.smooth hsmT
  haveI : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  set Z₀ : irreducibleComponents X := MMP.Mori.pointComponent (genericPoint X)
  set ZT : irreducibleComponents S.idealSheaf.subscheme :=
    MMP.Mori.pointComponent (genericPoint S.idealSheaf.subscheme)
  /- `φ` is a unit at the generic point of `S`; its restriction `φ_T`. -/
  have hφ0 : S.ord φ = 0 := by
    have := hφS
    rwa [DivisorWithCoeffs.coeff_add, hDS, zero_add, coeff_principalDivisor] at this
  set φX := MMP.Threefold.Mori.Helpers.evalFF Z₀ (φ : MMP.Mori.RationalFunctions X) with hφXdef
  have hφX0 : φX ≠ 0 := evalFF_ne_zero Z₀ φ
  have hordφ : ∀ E : MMP.Mori.PrimeDivisor X, X.ord φX E.genericPoint = E.ord φ := by
    intro E
    rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord,
      show E.component = Z₀ from
        Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _]
  have hηS : S.idealSheaf.subschemeι (genericPoint S.idealSheaf.subscheme) = S.genericPoint := rfl
  have hnn : ∀ (u : X.functionField), X.ord u S.genericPoint = 0 →
      ∀ Γ : MMP.Mori.PrimeDivisor X,
        S.idealSheaf.subschemeι (genericPoint S.idealSheaf.subscheme) ∈ Γ.support →
          0 ≤ X.ord u Γ.genericPoint :=
    fun u hu Γ hΓ => by
      rw [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hΓ, hu]
  obtain ⟨aφ, haφ⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
    (S.idealSheaf.subschemeι (genericPoint S.idealSheaf.subscheme)) hφX0
    (hnn φX (by rw [hordφ, hφ0]))
  obtain ⟨aφ', haφ'⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
    (S.idealSheaf.subschemeι (genericPoint S.idealSheaf.subscheme)) (inv_ne_zero hφX0) (hnn φX⁻¹ (by
      rw [← zpow_neg_one, MMP.Mori.ord_zpow _ hφX0, hordφ, hφ0]; simp))
  have hmul : aφ * aφ' = 1 := IsFractionRing.injective _ X.functionField (by
    rw [map_mul, haφ, haφ', map_one, mul_inv_cancel₀ hφX0])
  have hunit : IsUnit aφ := ⟨⟨aφ, aφ', hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
  set φT : S.idealSheaf.subscheme.functionField :=
    (S.idealSheaf.subschemeι.stalkMap (genericPoint S.idealSheaf.subscheme)).hom aφ with hφTdef
  have hφT' :
      (S.idealSheaf.subschemeι.stalkMap (genericPoint S.idealSheaf.subscheme)).hom aφ' = φT⁻¹ := by
    refine (eq_inv_of_mul_eq_one_right ?_)
    rw [hφTdef, ← map_mul, hmul, map_one]
  have hφT0 : φT ≠ 0 :=
    (hunit.map (S.idealSheaf.subschemeι.stalkMap (genericPoint S.idealSheaf.subscheme)).hom).ne_zero
  /- The restriction formula `D₁|_S = D|_S + div(φ_T)`. -/
  have hrestr : ∀ Q : MMP.Mori.PrimeDivisor S.idealSheaf.subscheme,
      (D₁.restrictPrimeDivisor S).coeff Q =
      (D.restrictPrimeDivisor S).coeff Q + S.idealSheaf.subscheme.ord φT Q.genericPoint := by
    intro Q
    have hpS : (principalDivisor φ).coeff S = 0 := by rw [coeff_principalDivisor, hφ0]
    rw [DivisorWithCoeffs.coeff_restrictPrimeDivisor _ S hφS Q,
      DivisorWithCoeffs.coeff_restrictPrimeDivisor _ S hDS Q, hD₁def,
      Finsupp.sum_add_index' (fun _ => smul_zero _) (fun _ _ _ => smul_add _ _ _)]
    congr 1
    rw [hφTdef, MMP.Mori.PrimeDivisor.ord_restrict_eq_sum_intersectionLength_mul_ord sX
      S.idealSheaf.subschemeι aφ hunit Q
      (principalDivisor φ).support (fun E hE => by
        rw [haφ, hordφ] at hE
        exact Finsupp.mem_support_iff.mpr hE), Finsupp.sum]
    refine Finset.sum_congr rfl fun E _ => ?_
    rw [haφ, hordφ, nsmul_eq_mul, ← DivisorWithCoeffs.coeff_apply, coeff_principalDivisor]
  /- The restriction `h₁ = h φ_T⁻¹` of the section `g φ⁻¹` of `𝒪_X(D₁)`. -/
  obtain ⟨ag, hag1, hag2⟩ := hres
  set h₁ := h * φT⁻¹ with hh₁def
  have hsec : (g * φX⁻¹) ^ b ∈ sectionsIn ((b : ℤ) • D₁) := by
    intro P
    rw [Valuation.map_pow, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
      show ((b : ℤ) * D₁.coeff P) = b • D₁.coeff P by simp, WithZero.exp_nsmul]
    refine pow_le_pow_left₀ zero_le' ?_ b
    rw [Valuation.map_mul, map_inv₀, P.divisorialValuation_eq_exp_neg_ord hφX0, hordφ,
      ← WithZero.exp_neg, neg_neg, hD₁def, DivisorWithCoeffs.coeff_add,
      coeff_principalDivisor, WithZero.exp_add]
    exact mul_le_mul_left (hg P) _
  have hw : h₁ ^ b ∈ imageSeries D₁ S b := by
    refine AddSubgroup.subset_closure ⟨(g * φX⁻¹) ^ b, hsec, (ag * aφ') ^ b, ?_, ?_⟩
    · show algebraMap _ X.functionField ((ag * aφ') ^ b) = (g * φX⁻¹) ^ b
      rw [map_pow, map_mul, haφ', ← hag1]
      rfl
    · rw [map_pow, map_mul, hag2, hφT']
  /- A local equation `ψ` of `D₁|_S` near `x`. -/
  obtain ⟨W, hxW, ψ, hψ⟩ := hD₁c x
  set ψT := MMP.Threefold.Mori.Helpers.evalFF ZT
    (ψ : MMP.Mori.RationalFunctions S.idealSheaf.subscheme) with hψTdef
  have hψT0 : ψT ≠ 0 := evalFF_ne_zero ZT ψ
  set s := φT * ψT⁻¹ with hsdef
  set t := h₁ * ψT with htdef
  have hst : h = s * t := by
    rw [hsdef, htdef, hh₁def]
    field_simp
  refine ⟨W, hxW, ?_⟩
  rw [hst]
  refine Submodule.subset_span (Set.mul_mem_mul ⟨fun hW => ?_, fun Q hQ => ?_⟩ ?_)
  · exfalso
    have hx' : x ∈ (𝟙 S.idealSheaf.subscheme) ⁻¹ᵁ W := hxW
    rw [hW] at hx'
    exact hx'
  · -- `s` is a section of `𝒪_T(D|_S)` on `W`
    have hQW : (Q.support ∩ W).Nonempty := hQ
    have hs0 : s ≠ 0 := mul_ne_zero hφT0 (inv_ne_zero hψT0)
    rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.functionFieldMap_id_apply,
      Q.divisorialValuation_eq_exp_neg_ord hs0, WithZero.exp_le_exp, hsdef,
      ord_mul_inv hφT0 hψT0, ord_evalFF_of_isLocalEquation hψ ZT Q hQW, hrestr Q]
    omega
  · -- `t` is a section of `𝒥` on `W`
    rw [hJT W t]
    refine ⟨fun hW => ?_, fun y hy => ⟨W, hy, le_rfl, b, hb, dvd_refl b, ?_⟩⟩
    · exfalso
      have hx' := hxW
      rw [hW] at hx'
      exact hx'
    obtain ⟨Y, μ, hOn⟩ := hJp b hb (dvd_refl b)
    obtain ⟨-, -, -, -, -, -, -, i1, i2, i3, i4, hY, hμ, hD, Dμ, F, Γ, E, hDμ, ⟨-, hfix, -, -⟩,
      hΓ, hE, hJeq⟩ := hOn
    rw [hJeq]
    have ht0 : t ≠ 0 := mul_ne_zero (mul_ne_zero hh0 (inv_ne_zero hφT0)) hψT0
    refine ⟨fun hW => ?_, fun P hP => ?_⟩
    · exfalso
      obtain ⟨_, hx', x', rfl⟩ := μ.denseRange.inter_open_nonempty _ W.isOpen ⟨x, hxW⟩
      have hx'' : x' ∈ μ ⁻¹ᵁ W := hx'
      rw [hW] at hx''
      exact hx''
    have hμP := MMP.Intersection.genericPoint_mem_of_support_inter_nonempty P hP
    -- `E_P ≥ 0`
    have hE0 : 0 ≤ E.coeff P := by
      obtain ⟨n, a, hla, hEP⟩ := hE P
      obtain ⟨m, rfl⟩ := MMP.Intersection.IsLogDiscrepancy.exists_nat_eq_of_isSNC
        (S.idealSheaf.subschemeι ≫ sX)
        hXT.1 hsmT hΘ.1 hΘ.2 hla
      have hEP' : E.coeff P = (m : ℤ) - 1 + Γ.coeff P := by exact_mod_cast hEP
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        have : Γ.coeff P = 1 := (hΓ.2 P).2 ⟨n, by simpa using hla⟩
        omega
      · rcases hΓ.1 P with h0 | h1 <;> omega
    -- the fixed divisor along `P`
    have hψb := hψ.zsmul (b : ℤ)
    rw [zpow_natCast] at hψb
    have hv1 := valuationOver_evalFF_eq hDμ hψb P hμP ZT
    rw [Units.val_pow_eq_pow_val, map_pow] at hv1
    have hv2 := (hfix P).1 (h₁ ^ b) hw
    have hvt : P.valuationOver μ t ^ b ≤ WithZero.exp (-F.coeff P) := by
      rw [← Valuation.map_pow, htdef, mul_pow, Valuation.map_mul, hv1]
      refine (mul_le_mul_left hv2 _).trans_eq ?_
      rw [← WithZero.exp_add]
      congr 1; ring
    have hvt0 : P.valuationOver μ t ≠ 0 := (map_ne_zero _).mpr ht0
    rw [← WithZero.exp_log hvt0] at hvt ⊢
    rw [← WithZero.exp_nsmul, WithZero.exp_le_exp, nsmul_eq_mul] at hvt
    rw [WithZero.exp_le_exp, DivisorWithCoeffs.coeff_sub,
      MMP.Intersection.WeilRDivisor.coeff_roundDown, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toRDivisor, smul_eq_mul]
    have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
    have hfl : ⌊((1 / b : ℚ) : ℝ) * (F.coeff P : ℝ)⌋ ≤ -WithZero.log (P.valuationOver μ t) := by
      have hle : ((1 / b : ℚ) : ℝ) * (F.coeff P : ℝ) ≤
          ((-WithZero.log (P.valuationOver μ t) : ℤ) : ℝ) := by
        have h1 : (F.coeff P : ℝ) ≤ b * ((-WithZero.log (P.valuationOver μ t) : ℤ) : ℝ) := by
          have : F.coeff P ≤ b * (-WithZero.log (P.valuationOver μ t)) := by
            have := hvt; push_cast at this ⊢; linarith
          exact_mod_cast this
        push_cast at h1 ⊢
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hbpos]
        linarith
      exact (Int.floor_le_floor hle).trans (by rw [Int.floor_intCast])
    omega

end Image

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- An asymptotic adjoint ideal consists of regular functions, is given by an ideal sheaf on
non-empty affine opens, and equals `𝒥_{Δ,(c/p)V_p}` for every positive `p` divisible enough. -/
public theorem IsAsymptoticAdjointIdeal.isCoherent_and_stabilizes {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {Z : Scheme.{u}} {f : X ⟶ Z}
    {Δ D : Divisor X} {V : ℕ → AddSubgroup X.functionField} {b : ℕ} {c : ℚ}
    {J : X.Opens → Set X.functionField} (h : IsAsymptoticAdjointIdeal sX f Δ D V b c J) :
    (∀ (U : X.Opens) [Nonempty U], J U ⊆ Set.range (X.germToFunctionField U)) ∧
      (∃ I : X.IdealSheafData, ∀ (U : X.affineOpens) [Nonempty (U : X.Opens)],
        J U = X.germToFunctionField (U : X.Opens) '' (I.ideal U : Set Γ(X, U))) ∧
      ∃ p₀ : ℕ, 0 < p₀ ∧ b ∣ p₀ ∧ ∀ p : ℕ, 0 < p → p₀ ∣ p →
        ∀ Jp : X.Opens → Set X.functionField,
          IsSeriesAdjointIdeal sX Δ ((p : ℤ) • D) (V p) (c / p) Jp →
          ∀ (U : X.Opens) [Nonempty U], Jp U = J U := by
  classical
  obtain ⟨p₀, hp₀, hbp₀, ⟨I, hI⟩, hst⟩ := exists_seriesSet_stabilizes sX f h
  obtain ⟨-, -, hX, hsm, hΔ, hDc, hgr, hb, -, -, hc, Jp, hJp, hJ⟩ := h
  have hS : ∀ p, 0 < p → b ∣ p → Jp p = seriesSet sX Δ ((p : ℤ) • D) (V p) (c / p) :=
    fun p hp hbp => by
      obtain ⟨Y, μ, hOn⟩ := hJp p hp hbp
      exact eq_seriesSet sX hOn
  have hJeq : ∀ (U : X.Opens), Nonempty U →
      J U = seriesSet sX Δ ((p₀ : ℤ) • D) (V p₀) (c / p₀) U := by
    intro U hU
    ext g
    rw [hJ U g]
    constructor
    · rintro ⟨h0, hloc⟩
      refine ⟨h0, fun n G a hx ha => ?_⟩
      obtain ⟨W, hxW, -, p, hp, hbp, hgW⟩ := hloc _ hx
      rw [hS p hp hbp] at hgW
      have hW : Nonempty W := ⟨⟨_, hxW⟩⟩
      have h1 := seriesSet_subset_of_dvd sX f hgr hDc hp (Nat.mul_pos hp hp₀)
        (dvd_mul_right p p₀) W hgW
      rw [hst (p * p₀) (Nat.mul_pos hp hp₀) (dvd_mul_left p₀ p) W hW] at h1
      exact h1.2 n G a hxW ha
    · intro hg
      exact ⟨hg.1, fun x hx => ⟨U, hx, le_rfl, p₀, hp₀, hbp₀, by rwa [hS p₀ hp₀ hbp₀]⟩⟩
  refine ⟨fun U _ => ?_, ⟨I, fun U _ => ?_⟩, p₀, hp₀, hbp₀, fun p hp hp₀p Jp' hJp' U _ => ?_⟩
  · rw [hJeq U ‹_›]
    exact seriesSet_subset_range sX hX hsm hΔ (hgr.1 p₀) (hDc.zsmul _)
      (div_nonneg hc.le (Nat.cast_nonneg _)) U
  · rw [hJeq U ‹_›, hI U]
  · obtain ⟨Y, μ, hOn⟩ := hJp'
    rw [eq_seriesSet sX hOn, hJeq U ‹_›, hst p hp hp₀p U ‹_›]

/-- If `Δ ≤ Δ'` and `c ≤ c'`, the asymptotic adjoint ideal `J'` of `(Δ', c')` is contained in
the one `J` of `(Δ, c)`. -/
public theorem IsAsymptoticAdjointIdeal.subset_of_le {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {Z : Scheme.{u}} {f : X ⟶ Z}
    {Δ Δ' D : Divisor X} {V : ℕ → AddSubgroup X.functionField} {b b' : ℕ} {c c' : ℚ}
    {J J' : X.Opens → Set X.functionField} (h : IsAsymptoticAdjointIdeal sX f Δ D V b c J)
    (h' : IsAsymptoticAdjointIdeal sX f Δ' D V b' c' J') (hΔΔ' : Δ ≤ Δ') (hcc' : c ≤ c')
    (U : X.Opens) : J' U ⊆ J U := by
  classical
  intro g hg
  obtain ⟨-, -, hX, hsm, hΔ, hDc, hgr, hb, -, -, hc, Jp, hJp, hJ⟩ := h
  obtain ⟨-, -, -, -, hΔ', -, -, -, -, -, -, Jp', hJp', hJ'⟩ := h'
  rw [hJ' U g] at hg
  rw [hJ U g]
  obtain ⟨h0, hloc⟩ := hg
  refine ⟨h0, fun x hx => ?_⟩
  obtain ⟨W, hxW, hWU, p, hp, hbp, hgW⟩ := hloc x hx
  refine ⟨W, hxW, hWU, p * b, Nat.mul_pos hp hb, dvd_mul_left b p, ?_⟩
  obtain ⟨Y', μ', hOn'⟩ := hJp' p hp hbp
  rw [eq_seriesSet sX hOn'] at hgW
  obtain ⟨Y, μ, hOn⟩ := hJp (p * b) (Nat.mul_pos hp hb) (dvd_mul_left b p)
  rw [eq_seriesSet sX hOn]
  have h1 := seriesSet_subset_of_dvd sX f hgr hDc hp (Nat.mul_pos hp hb) (dvd_mul_right p b) W
    hgW
  exact seriesSet_anti sX hX hsm hΔ hΔ' hΔΔ' (hgr.1 _) (hDc.zsmul _)
    (div_nonneg hc.le (Nat.cast_nonneg _)) (div_le_div_of_nonneg_right hcc' (Nat.cast_nonneg _))
    W h1

/-- **Stabilization of asymptotic adjoint ideals and the image of restriction.** Let `X` be a
normal integral locally Noetherian scheme over an algebraically closed field `k` of
characteristic zero, and `f : X ⟶ Z`.
1. `𝒥_{Δ,cV_•}` consists of regular functions, is the ideal sheaf of an
   `AlgebraicGeometry.Scheme.IdealSheafData` on every non-empty affine open, and there is
   `p₀ ∈ bℤ_{>0}` with `𝒥_{Δ,(c/p)V_p} = 𝒥_{Δ,cV_•}` for every positive `p` divisible
   by `p₀`.
2. If `Δ ≤ Δ'` and `c ≤ c'`, then `𝒥_{Δ',c'V_•} ⊆ 𝒥_{Δ,cV_•}`.
3. If `X` is a smooth normal variety, `f` projective, `Z` affine, `Δ` reduced snc, `S` a component
   of `Δ`, `D` Cartier with `S` not a component of `D`, and the stable base locus of `D` contains
   no stratum of `Δ`, then the restriction to `S` of every section of `𝒪_X(D)` is a global section
   of `𝒥_{Θ,‖D‖_S} ⊗ 𝒪_S(D|_S)`. -/
@[mmp "lem_fourfold_asymptotic_adjoint_operations"]
public theorem isAsymptoticAdjointIdeal_operations {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {Z : Scheme.{u}} (f : X ⟶ Z) :
    -- 1. coherence and stabilization
    (∀ (Δ D : Divisor X) (V : ℕ → AddSubgroup X.functionField) (b : ℕ) (c : ℚ)
      (J : X.Opens → Set X.functionField), IsAsymptoticAdjointIdeal sX f Δ D V b c J →
      (∀ (U : X.Opens) [Nonempty U], J U ⊆ Set.range (X.germToFunctionField U)) ∧
      (∃ I : X.IdealSheafData, ∀ (U : X.affineOpens) [Nonempty (U : X.Opens)],
        J U = X.germToFunctionField (U : X.Opens) '' (I.ideal U : Set Γ(X, U))) ∧
      ∃ p₀ : ℕ, 0 < p₀ ∧ b ∣ p₀ ∧ ∀ p : ℕ, 0 < p → p₀ ∣ p →
        ∀ Jp : X.Opens → Set X.functionField,
          IsSeriesAdjointIdeal sX Δ ((p : ℤ) • D) (V p) (c / p) Jp →
          ∀ (U : X.Opens) [Nonempty U], Jp U = J U) ∧
    -- 2. antitone in the coefficient and in the reduced boundary
    (∀ (Δ Δ' D : Divisor X) (V : ℕ → AddSubgroup X.functionField) (b b' : ℕ) (c c' : ℚ)
      (J J' : X.Opens → Set X.functionField),
      IsAsymptoticAdjointIdeal sX f Δ D V b c J → IsAsymptoticAdjointIdeal sX f Δ' D V b' c' J' →
      Δ ≤ Δ' → c ≤ c' → ∀ U, J' U ⊆ J U) ∧
    -- 3. the image of restriction lies in the twisted asymptotic ideal
    (∀ (Δ D : Divisor X) (S : MMP.Mori.PrimeDivisor X) (b : ℕ),
      haveI := S.integral
      ∀ [IsLocallyNoetherian S.idealSheaf.subscheme] [IsNormal S.idealSheaf.subscheme]
        (J : S.idealSheaf.subscheme.Opens → Set S.idealSheaf.subscheme.functionField),
      IsNormalVariety k sX → IsSmoothScheme sX → IsProjectiveMorphism f → IsAffine Z →
      IsReducedSNC sX Δ → Δ.coeff S = 1 → D.IsCartier →
      ContainsNoStratum Δ (⋂ (m : ℕ) (_ : 0 < m),
        baseLocusIn (sectionsIn ((m : ℤ) • D)) ((m : ℤ) • D)) →
      D.coeff S = 0 → IsRestrictedAsymptoticAdjointIdeal sX f Δ D S b 1 J →
      ∀ g ∈ sectionsIn D, ∀ h : S.idealSheaf.subscheme.functionField, IsRestrictionAlong S g h →
        ∀ x : S.idealSheaf.subscheme, ∃ W : S.idealSheaf.subscheme.Opens, x ∈ W ∧
          h ∈ Submodule.span ℤ (MMP.Intersection.multiplierIdealSections
            (𝟙 S.idealSheaf.subscheme) (D.restrictPrimeDivisor S) W * J W)) := by
  refine ⟨fun Δ D V b c J h => h.isCoherent_and_stabilizes,
    fun Δ Δ' D V b b' c c' J J' h h' hΔΔ' hcc' U => h.subset_of_le h' hΔΔ' hcc' U, ?_⟩
  · -- 3. the image of restriction lies in the twisted asymptotic ideal
    intro Δ D S b
    haveI := S.integral
    intro _ _ J hX hsm _ _ _ _ hDc _ hDS hJ
    exact exists_mem_span_of_isRestrictionAlong sX f hsm Δ D S b J hDc hDS hJ

end MMP.Fourfold

end AsymptoticAdjointIdeal

/-! ## Cyclic covers of subklt surface pluriforms -/

section CyclicCover

open CategoryTheory AlgebraicGeometry MMP.Analytic.ComplexPoints MMP MMP.Mori

namespace MMP.Fourfold

/-! ### Two-forms over a ring -/

section TwoForms

open KaehlerDifferential

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

private theorem vecTwo_eq_update_zero {M : Type*} [Zero M] (u w : M) :
    (![u, w] : Fin 2 → M) = Function.update ![0, w] 0 u := by
  funext i
  fin_cases i <;> simp

private theorem vecTwo_eq_update_one {M : Type*} [Zero M] (u w : M) :
    (![u, w] : Fin 2 → M) = Function.update ![u, 0] 1 w := by
  funext i
  fin_cases i <;> simp

/-- The wedge product `(u, w) ↦ u ∧ w` of one-forms, as a bilinear map. -/
private noncomputable def wedgeTwo : Ω[A⁄k] →ₗ[A] Ω[A⁄k] →ₗ[A] ⋀[A]^2 Ω[A⁄k] :=
  LinearMap.mk₂ A (fun u w => exteriorPower.ιMulti A 2 ![u, w])
    (fun u₁ u₂ w => by
      rw [vecTwo_eq_update_zero (u₁ + u₂), vecTwo_eq_update_zero u₁, vecTwo_eq_update_zero u₂,
        AlternatingMap.map_update_add])
    (fun c u w => by
      rw [vecTwo_eq_update_zero (c • u), vecTwo_eq_update_zero u, AlternatingMap.map_update_smul])
    (fun u w₁ w₂ => by
      rw [vecTwo_eq_update_one u (w₁ + w₂), vecTwo_eq_update_one u w₁, vecTwo_eq_update_one u w₂,
        AlternatingMap.map_update_add])
    (fun c u w => by
      rw [vecTwo_eq_update_one u (c • w), vecTwo_eq_update_one u w,
        AlternatingMap.map_update_smul])

private theorem wedgeTwo_apply (u w : Ω[A⁄k]) :
    wedgeTwo u w = exteriorPower.ιMulti A 2 ![u, w] := rfl

private theorem wedgeTwo_self (u : Ω[A⁄k]) : wedgeTwo (k := k) u u = 0 :=
  (exteriorPower.ιMulti A 2).map_eq_zero_of_eq ![u, u] (i := 0) (j := 1) rfl (by decide)

/-- `d(t^{n+1} e) = t^n ((n + 1) e dt + t de)`. -/
private theorem D_pow_succ_mul (t e : A) (n : ℕ) :
    D k A (t ^ (n + 1) * e) = t ^ n • (((n + 1 : ℕ) : A) • e • D k A t + t • D k A e) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, Nat.add_sub_cancel, pow_succ]
  module

/-- **A two-form `d f ∧ θ` with `f = t^{n+1} e`** is divisible by `t^n`. -/
private theorem exists_wedgeTwo_D_left_eq_pow_smul (t e : A) (n : ℕ) (θ : Ω[A⁄k]) :
    ∃ ω : ⋀[A]^2 Ω[A⁄k], wedgeTwo (D k A (t ^ (n + 1) * e)) θ = t ^ n • ω :=
  ⟨wedgeTwo (((n + 1 : ℕ) : A) • e • D k A t + t • D k A e) θ, by
    rw [D_pow_succ_mul, map_smul, LinearMap.smul_apply]⟩

/-- **A two-form `d f ∧ d g` with `f = t^{n+1} e`, `g = t^{n'+1} e'`** is divisible by
`t^{n+n'+1}`: the terms `dt ∧ dt` cancel. -/
private theorem exists_wedgeTwo_D_D_eq_pow_smul (t e e' : A) (n n' : ℕ) :
    ∃ ω : ⋀[A]^2 Ω[A⁄k],
      wedgeTwo (D k A (t ^ (n + 1) * e)) (D k A (t ^ (n' + 1) * e')) = t ^ (n + n' + 1) • ω := by
  refine ⟨((n + 1 : ℕ) : A) • e • wedgeTwo (D k A t) (D k A e') +
      ((n' + 1 : ℕ) : A) • e' • wedgeTwo (D k A e) (D k A t) +
      t • wedgeTwo (D k A e) (D k A e'), ?_⟩
  rw [D_pow_succ_mul, D_pow_succ_mul]
  simp only [map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply, wedgeTwo_self,
    smul_zero, zero_add, smul_add, smul_smul]
  rw [pow_add, pow_succ]
  module

end TwoForms

/-! ### Bases of differentials adapted to regular parameters -/

section AdaptedBasis

open IsLocalRing KaehlerDifferential TensorProduct

variable {R A : Type*} [CommRing R] [CommRing A] [IsLocalRing A] [Algebra R A]

/-- **Differentials of regular parameters extend to a basis.** Let `A` be a Noetherian local
ring, formally smooth and essentially of finite type over `R`, with residue field formally smooth
over `R` and `Ω_{A/R}` of rank two. For a regular system of parameters `z₁, …, z_d` of `A`, there
are at most two parameters and `dz₁, …, dz_d` extend to a basis of `Ω_{A/R}`. -/
private theorem exists_basis_extending_D [IsNoetherianRing A] [Algebra.FormallySmooth R A]
    [Algebra.EssFiniteType R A] [Algebra.FormallySmooth R (ResidueField A)]
    (hn : Module.finrank A Ω[A⁄R] = 2) {d : ℕ} {z : Fin d → A}
    (hz : MMP.Mori.IsRegularSystemOfParameters z) :
    ∃ (hd : d ≤ 2) (b : Module.Basis (Fin 2) A Ω[A⁄R]),
      ∀ i : Fin d, b (Fin.castLE hd i) = D R A (z i) := by
  classical
  let κ := ResidueField A
  have : Module.Finite A Ω[A⁄R] := KaehlerDifferential.finite R A
  have : Module.Projective A Ω[A⁄R] := ((Algebra.formallySmooth_iff R A).mp inferInstance).1
  have : Module.Free A Ω[A⁄R] := Module.free_of_flat_of_isLocalRing
  let v : Fin d → κ ⊗[A] Ω[A⁄R] := fun i => (1 : κ) ⊗ₜ[A] D R A (z i)
  have hv : LinearIndependent κ v := by
    refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
    choose a ha using fun j => IsLocalRing.residue_surjective (g j)
    have hsum : ∑ j, a j • v j = 0 := by
      rw [← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← ha j]
      exact (algebraMap_smul κ (a j) (v j)).symm
    rw [← ha i]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr
      (MMP.Intersection.mem_maximalIdeal_of_sum_smul_tmul_D_eq_zero hz a hsum i)
  have hκ : Module.finrank κ (κ ⊗[A] Ω[A⁄R]) = 2 := by rw [Module.finrank_baseChange, hn]
  have hd : d ≤ 2 := by simpa [hκ] using hv.fintype_card_le_finrank
  refine ⟨hd, ?_⟩
  obtain rfl | rfl | rfl : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  · exact ⟨Module.finBasisOfFinrankEq A Ω[A⁄R] hn, fun i => i.elim0⟩
  · have hv0 : v 0 ≠ 0 := hv.ne_zero 0
    have hlt : Submodule.span κ {v 0} ≠ ⊤ := by
      intro h
      have := finrank_span_singleton (K := κ) hv0
      rw [h, finrank_top, hκ] at this
      exact absurd this (by norm_num)
    obtain ⟨e, -, he⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hlt)
    obtain ⟨θ, hθ⟩ := TensorProduct.mk_surjective A Ω[A⁄R] κ IsLocalRing.residue_surjective e
    let w : Fin 2 → Ω[A⁄R] := ![D R A (z 0), θ]
    have hu : LinearIndependent κ ![v 0, e] := by
      refine (LinearIndependent.pair_iff' hv0).mpr fun a ha => he ?_
      rw [← ha]
      exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)
    let bκ := basisOfLinearIndependentOfCardEqFinrank hu (by rw [hκ, Fintype.card_fin])
    have hspan : Submodule.span A (Set.range w) = ⊤ :=
      IsLocalRing.span_eq_top_of_tmul_eq_basis w bκ fun i => by
        fin_cases i
        · simp [bκ, w, v]
        · simp [bκ, w, ← hθ]
    have hli : LinearIndependent A w :=
      linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (by rw [hn, Fintype.card_fin])
    refine ⟨Module.Basis.mk hli hspan.ge, fun i => ?_⟩
    fin_cases i
    simp [w]
  · obtain ⟨b, hb⟩ := MMP.Intersection.exists_basis_D_of_isRegularSystemOfParameters hn hz
    exact ⟨b, fun i => by rw [hb]; rfl⟩

end AdaptedBasis

/-! ### Additive valuations -/

section MulVal

variable {L : Type*} [Field L] {v : L → ℤ} (hmul : ∀ x y : L, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)

include hmul

private theorem mulVal_one : v 1 = 0 := by
  have := hmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at this
  omega

private theorem mulVal_prod {ι : Type*} (S : Finset ι) (f : ι → L) (hf : ∀ i, f i ≠ 0) :
    v (∏ i ∈ S, f i) = ∑ i ∈ S, v (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using mulVal_one hmul
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      hmul _ _ (hf a) (Finset.prod_ne_zero_iff.mpr fun i _ => hf i), ih]

private theorem mulVal_pow {x : L} (hx : x ≠ 0) (n : ℕ) : v (x ^ n) = n * v x := by
  have := mulVal_prod hmul (Finset.univ : Finset (Fin n)) (fun _ => x) (fun _ => hx)
  simpa [Finset.prod_const, Finset.sum_const] using this

private theorem mulVal_inv {x : L} (hx : x ≠ 0) : v x⁻¹ = -v x := by
  have := hmul x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, mulVal_one hmul] at this
  omega

end MulVal

/-- The order of a power is the multiple of the order. -/
private theorem ord_pow {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z]
    {f : Z.functionField} (hf : f ≠ 0) (n : ℕ) (z : Z) :
    Z.ord (f ^ n) z = n * Z.ord f z := by
  simpa using MMP.Mori.ord_zpow z hf n

/-! ### Orders along prime divisors -/

section Orders

variable {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]

/-- Elements of `𝒪_{Z,E}` have nonnegative order along `E`. -/
private theorem ord_algebraMap_localRing_nonneg (E : MMP.Mori.PrimeDivisor Z) (a : E.localRing)
    (ha : a ≠ 0) : 0 ≤ Z.ord (algebraMap E.localRing Z.functionField a) E.genericPoint := by
  have h0 : algebraMap E.localRing Z.functionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective E.localRing Z.functionField)).mpr ha
  have hv := (E.divisorialValuation_le_one_iff (algebraMap E.localRing Z.functionField a)).mpr
    ⟨a, rfl⟩
  rw [E.divisorialValuation_eq_exp_neg_ord h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hv
  omega

/-- A uniformizer of `𝒪_{Z,E}` has order one along `E`. -/
private theorem ord_algebraMap_irreducible (E : MMP.Mori.PrimeDivisor Z) {ϖ : E.localRing}
    (hϖ : Irreducible ϖ) : Z.ord (algebraMap E.localRing Z.functionField ϖ) E.genericPoint = 1 := by
  have h0 : algebraMap E.localRing Z.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective E.localRing Z.functionField)).mpr hϖ.ne_zero
  have hv := E.divisorialValuation_algebraMap_of_irreducible hϖ
  rw [E.divisorialValuation_eq_exp_neg_ord h0] at hv
  have := WithZero.exp_injective hv
  omega

/-- `u ϖⁿ`, `u` a unit and `ϖ` a uniformizer of `𝒪_{Z,E}`, has order `n` along `E`. -/
private theorem ord_algebraMap_unit_mul_pow (E : MMP.Mori.PrimeDivisor Z) (u : E.localRingˣ)
    {ϖ : E.localRing} (hϖ : Irreducible ϖ) (n : ℕ) :
    Z.ord (algebraMap E.localRing Z.functionField (u * ϖ ^ n)) E.genericPoint = n := by
  have hinj := IsFractionRing.injective E.localRing Z.functionField
  have hϖ0 : algebraMap E.localRing Z.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  have hu0 : algebraMap E.localRing Z.functionField u ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr u.ne_zero
  rw [map_mul, map_pow, Scheme.ord_mul hu0 (pow_ne_zero _ hϖ0),
    MMP.Mori.PrimeDivisor.ord_algebraMap_of_isUnit E u.isUnit, zero_add, ord_pow hϖ0,
    ord_algebraMap_irreducible E hϖ, mul_one]

/-- Elements of the local ring at a point `x` of `E` have nonnegative order along `E`. -/
private theorem ord_algebraMap_stalk_nonneg (E : MMP.Mori.PrimeDivisor Z) {x : Z}
    (hx : x ∈ E.support) (r : Z.presheaf.stalk x)
    (hr : algebraMap (Z.presheaf.stalk x) Z.functionField r ≠ 0) :
    0 ≤ Z.ord (algebraMap (Z.presheaf.stalk x) Z.functionField r) E.genericPoint := by
  have hsp : E.genericPoint ⤳ x :=
    MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hx
  rw [← MMP.Mori.algebraMap_stalkSpecializes hsp] at hr ⊢
  exact ord_algebraMap_localRing_nonneg E _ fun h => hr (by rw [h, map_zero])

end Orders

/-! ### Local rings of a smooth surface -/

section SmoothStalk

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]

/-- A regular local ring `𝒪_{X,x}` of a scheme locally of finite type over `ℂ` is formally smooth
and essentially of finite type over `ℂ`. -/
private theorem formallySmooth_stalk (x : X) [IsRegularLocalRing (X.presheaf.stalk x)] :
    letI := stalkAlgebra sX x
    Algebra.FormallySmooth ℂ (X.presheaf.stalk x) ∧
      Algebra.EssFiniteType ℂ (X.presheaf.stalk x) := by
  let := stalkAlgebra sX x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU' : IsAffineOpen U := hU
  let x' : U := ⟨x, hxU⟩
  let := sectionAlgebra sX U
  have := finiteType_sectionAlgebra sX hU'
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf x'
  have := isScalarTower_section_stalk sX U x'
  have := hU'.isLocalization_stalk x'
  set q := (hU'.primeIdealOf x').asIdeal
  have := Algebra.isSeparableExtension_of_perfectField ℂ q.ResidueField
  have hs : Algebra.IsSmoothAt ℂ q :=
    (Algebra.isSmoothAt_iff_isRegularLocalRing q (X.presheaf.stalk x)).mpr inferInstance
  have : Algebra.EssFiniteType Γ(X, U) (X.presheaf.stalk x) := .of_isLocalization _ q.primeCompl
  refine ⟨?_, .comp ℂ Γ(X, U) (X.presheaf.stalk x)⟩
  exact Algebra.FormallySmooth.of_equiv
    ((IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
      (X.presheaf.stalk x)).restrictScalars ℂ)

omit [LocallyOfFiniteType sX] in
/-- The residue field of a local ring `𝒪_{X,x}` essentially of finite type over `ℂ` is formally
smooth over `ℂ`. -/
private theorem formallySmooth_residueField_stalk (x : X)
    (h : letI := stalkAlgebra sX x; Algebra.EssFiniteType ℂ (X.presheaf.stalk x)) :
    letI := stalkAlgebra sX x
    Algebra.FormallySmooth ℂ (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
  let := stalkAlgebra sX x
  have : Algebra.EssFiniteType (X.presheaf.stalk x)
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    (RingHom.essFiniteType_algebraMap).mp
      (RingHom.FiniteType.of_surjective (algebraMap (X.presheaf.stalk x)
        (IsLocalRing.ResidueField (X.presheaf.stalk x)))
        IsLocalRing.residue_surjective).essFiniteType
  have : Algebra.EssFiniteType ℂ (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    .comp _ (X.presheaf.stalk x) _
  exact Algebra.FormallySmooth.of_perfectField

/-- On an integral surface over `ℂ` with local ring `𝒪_{X,x}` formally smooth and essentially of
finite type over `ℂ`, the module `Ω_{𝒪_{X,x}/ℂ}` is free of rank two. -/
private theorem free_finrank_kaehlerDifferential_stalk [IsIntegral X]
    (hn : topologicalKrullDim X = 2) (x : X)
    (h : letI := stalkAlgebra sX x; Algebra.FormallySmooth ℂ (X.presheaf.stalk x))
    (hef : letI := stalkAlgebra sX x; Algebra.EssFiniteType ℂ (X.presheaf.stalk x)) :
    letI := stalkAlgebra sX x
    Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄ℂ] ∧
      Module.finrank (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄ℂ] = 2 := by
  let := stalkAlgebra sX x
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX x
  have : Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄ℂ] :=
    KaehlerDifferential.finite ℂ (X.presheaf.stalk x)
  have : Module.Projective (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄ℂ] :=
    ((Algebra.formallySmooth_iff ℂ (X.presheaf.stalk x)).mp h).1
  have : Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄ℂ] :=
    Module.free_of_flat_of_isLocalRing
  refine ⟨this, ?_⟩
  have := essFiniteType_functionField (sX := sX)
  rw [← finrank_kaehlerDifferential_eq_of_isFractionRing (K := X.functionField),
    finrank_kaehlerDifferential_eq_trdeg, toNat_trdeg_functionField_of_topologicalKrullDim_eq hn]

end SmoothStalk

/-! ### Generators of top forms at a point and along prime divisors through it -/

section Generators

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [LocallyOfFiniteType sX]

/-- **A generator at `x` generates along every prime divisor through `x`.** If `τ` generates
`Ω²_{𝒪_{X,x}/ℂ}`, its image in `Ω²_{k(X)/ℂ}` has order `0` along every prime divisor through `x`,
and so do its tensor powers. -/
private theorem ordForm_formPow_topFormsMap_eq_zero (hn : topologicalKrullDim X = 2) {x : X}
    {τ : letI := stalkAlgebra sX x; ⋀[X.presheaf.stalk x]^2 Ω[X.presheaf.stalk x⁄ℂ]}
    (hτ : letI := stalkAlgebra sX x; Submodule.span (X.presheaf.stalk x) {τ} = ⊤)
    (P : MMP.Mori.PrimeDivisor X) (hxP : x ∈ P.support) (a : ℕ) :
    letI := stalkAlgebra sX x
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX x
    P.ordForm (show RationalPluriForms sX 2 (a : ℕ) from
      formPow (topFormsMap ℂ (X.presheaf.stalk x) X.functionField 2 τ) a) = 0 := by
  let := stalkAlgebra sX x
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX x
  have hsp : P.genericPoint ⤳ x :=
    MMP.Resolution.Aux.genericPoint_specializes_of_mem_support P hxP
  let := stalkAlgebra sX P.genericPoint
  have := isScalarTower_stalk_functionField sX P.genericPoint
  let : Algebra (X.presheaf.stalk x) P.localRing := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
  have : IsScalarTower ℂ (X.presheaf.stalk x) P.localRing :=
    MMP.Threefold.Resolution.isScalarTower_stalkSpecializes sX hsp
  have : IsScalarTower (X.presheaf.stalk x) P.localRing X.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => (MMP.Mori.algebraMap_stalkSpecializes hsp r).symm
  have := MMP.Intersection.isLocalization_stalkSpecializes hsp
  set σ := topFormsMap ℂ (X.presheaf.stalk x) P.localRing 2 τ with hσdef
  have hσ : Submodule.span P.localRing {σ} = ⊤ :=
    span_singleton_topFormsMap ((IsLocalRing.maximalIdeal (X.presheaf.stalk P.genericPoint)).comap
      (X.presheaf.stalkSpecializes hsp).hom).primeCompl hτ
  have hcomp : topFormsMap ℂ P.localRing X.functionField 2 σ =
      topFormsMap ℂ (X.presheaf.stalk x) X.functionField 2 τ :=
    MMP.Threefold.Mori.Helpers.topFormsMap_comp τ
  have h0 : topFormsMap ℂ P.localRing X.functionField 2 σ ≠ 0 :=
    P.topFormsMap_ne_zero (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn) hσ
  rw [MMP.Mori.PrimeDivisor.ordForm_eq P _ hσ h0]
  have hc : formCoeff P.localRing hσ h0
      (formPow (topFormsMap ℂ (X.presheaf.stalk x) X.functionField 2 τ) a) = 1 := by
    rw [← hcomp, ← topFormsBasis_apply (A := P.localRing) hσ h0 (), ← ZTensorPower.basis_natCast]
    simp [formCoeff]
  change X.ord (formCoeff P.localRing hσ h0
      (formPow (topFormsMap ℂ (X.presheaf.stalk x) X.functionField 2 τ) a)) _ = 0
  rw [hc, ← map_one (algebraMap P.localRing X.functionField)]
  exact MMP.Mori.PrimeDivisor.ord_algebraMap_of_isUnit P isUnit_one

/-- **A local equation of a prime divisor is a uniformizer.** If `E` passes through `x` and its
ideal in `𝒪_{X,x}` is generated by `π`, then `π` has order one along `E`. -/
private theorem ord_algebraMap_eq_one_of_stalk_idealSheaf_eq_span (E : MMP.Mori.PrimeDivisor X)
    {x : X} (hxE : x ∈ E.support) {π : X.presheaf.stalk x}
    (hπ : AlgebraicGeometry.IdealSheafData.stalk E.idealSheaf x = Ideal.span {π}) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField π) E.genericPoint = 1 := by
  have hsp : E.genericPoint ⤳ x :=
    MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hxE
  obtain ⟨q, hq, hqI, -⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support E hxE
  have hprime : MMP.Intersection.primeOfSpecializes hsp = q.asIdeal := by
    have h1 := MMP.Intersection.fromSpecStalk_primeOfSpecializes hsp
    exact congrArg PrimeSpectrum.asIdeal
      ((X.fromSpecStalk x).isEmbedding.injective (h1.trans hq.symm))
  let : Algebra (X.presheaf.stalk x) E.localRing := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
  have := MMP.Intersection.isLocalization_stalkSpecializes hsp
  have := E.isDiscreteValuationRing_localRing
  have hmax : IsLocalRing.maximalIdeal E.localRing =
      Ideal.span {(X.presheaf.stalkSpecializes hsp).hom π} := by
    have h := IsLocalization.AtPrime.map_eq_maximalIdeal
      (MMP.Intersection.primeOfSpecializes hsp) E.localRing
    rw [hprime, ← hqI, hπ, Ideal.map_span, Set.image_singleton] at h
    exact h.symm
  have hirr : Irreducible ((X.presheaf.stalkSpecializes hsp).hom π) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
      (fun h0 => by
        rw [h0, Set.singleton_zero, Ideal.span_zero] at hmax
        exact (IsDiscreteValuationRing.not_a_field E.localRing) hmax) hmax
  rw [← MMP.Mori.algebraMap_stalkSpecializes hsp]
  exact ord_algebraMap_irreducible E hirr

end Generators

/-! ### A local presentation of a subklt pluriform -/

section Presentation

/-- **A local presentation of a subklt pluriform.** At a point `x` of a smooth surface `X`, with
snc subboundary `B` of coefficients less than one, choose a regular system of parameters
`z₁, …, z_d` of `𝒪_{X,x}` in which the components of `B` through `x` are coordinate hyperplanes,
and a basis of `Ω_{𝒪_{X,x}/ℂ}` extending `dz₁, …, dz_d`, with wedge `τ`. Then every nonzero
`s ∈ H⁰(X, m(K_X + B))` is `h (z₁ ⋯ z_d)^{-(m-1)} τ^{⊗m}` with `h ∈ 𝒪_{X,x}`. -/
private theorem exists_local_presentation
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hn : topologicalKrullDim X = 2) {B : QDivisor X}
    (hXB : IsSNCSubboundaryPair sX B) (hB : ∀ P, B.coeff P < 1) {m : ℕ} (hm : 0 < m)
    (s : RationalPluriForms sX 2 m) (hs : s ∈ logPluricanonicalSections sX 2 m B) (hs0 : s ≠ 0)
    (x : X) :
    letI := stalkAlgebra sX x
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX x
    ∃ (d : ℕ) (z : Fin d → X.presheaf.stalk x) (hd : d ≤ 2)
      (b : Module.Basis (Fin 2) (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄ℂ])
      (h : X.presheaf.stalk x),
      (∀ i, z i ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ∧ (∀ i, z i ≠ 0) ∧
      (∀ i : Fin d, b (Fin.castLE hd i) = KaehlerDifferential.D ℂ _ (z i)) ∧
      s = (algebraMap (X.presheaf.stalk x) X.functionField h *
          ((∏ i, algebraMap (X.presheaf.stalk x) X.functionField (z i)) ^ (m - 1))⁻¹) •
        (formPow (topFormsMap ℂ (X.presheaf.stalk x) X.functionField 2
          (exteriorPower.ιMulti (X.presheaf.stalk x) 2 b)) m : RationalPluriForms sX 2 m) := by
  classical
  let := stalkAlgebra sX x
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX x
  have : LocallyOfFiniteType sX := hXB.isProjectiveVariety.1.toLocallyOfFiniteType
  obtain ⟨d, z, j, hz, hj, hI⟩ := hXB.isSNC.2 x
  have : IsRegularLocalRing (X.presheaf.stalk x) :=
    MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  obtain ⟨hfs, hef⟩ := formallySmooth_stalk (sX := sX) x
  have hκ := formallySmooth_residueField_stalk (sX := sX) x hef
  obtain ⟨hfree, hrank⟩ := free_finrank_kaehlerDifferential_stalk hn x hfs hef
  obtain ⟨hd, b, hb⟩ := exists_basis_extending_D hrank hz
  set τ := exteriorPower.ιMulti (X.presheaf.stalk x) 2 b with hτdef
  have hτ : Submodule.span (X.presheaf.stalk x) {τ} = ⊤ :=
    (Submodule.span_singleton_eq_top_iff _ _).mpr (MMP.Intersection.bijective_smul_ιMulti_basis b).2
  set τK := topFormsMap ℂ (X.presheaf.stalk x) X.functionField 2 τ with hτKdef
  have hτK : Submodule.span X.functionField {τK} = ⊤ :=
    span_singleton_topFormsMap (nonZeroDivisors (X.presheaf.stalk x)) hτ
  have := essFiniteType_functionField (sX := sX)
  have hKrank : Module.finrank X.functionField Ω[X.functionField⁄ℂ] = 2 :=
    (finrank_kaehlerDifferential_eq_trdeg ℂ X.functionField).trans
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn)
  have : FiniteDimensional X.functionField Ω[X.functionField⁄ℂ] :=
    Module.finite_of_finrank_eq_succ hKrank
  have := nontrivial_exteriorPower_of_finrank_eq ℂ X.functionField hKrank
  have hτK0 : τK ≠ 0 := topFormsMap_ne_zero_of_span_eq_top hτ
  let bK := basisOfSpanSingleton hτK hτK0
  set g := (ZTensorPower.basis bK (m : ℤ)).repr s () with hgdef
  set ω₀ : RationalPluriForms sX 2 m := formPow τK m with hω₀
  have hsg : s = g • ω₀ := by
    have := eq_repr_smul_formPow bK s
    rwa [basisOfSpanSingleton_apply] at this
  have hg0 : g ≠ 0 := fun h0 => hs0 (by rw [hsg, h0]; exact zero_smul _ _)
  have hzm : ∀ i, z i ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := fun i =>
    hz.1 ▸ Ideal.subset_span ⟨i, rfl⟩
  have hz0 : ∀ i, z i ≠ 0 := by
    intro i hi
    have h1 := MMP.Intersection.mem_maximalIdeal_of_sum_smul_tmul_D_eq_zero (R := ℂ) hz
      (Pi.single i 1) (by
        rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
          (by simp), Pi.single_eq_same, one_smul, hi, map_zero, TensorProduct.tmul_zero]) i
    rw [Pi.single_eq_same] at h1
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hzK0 : ∀ i, algebraMap (X.presheaf.stalk x) X.functionField (z i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hz0 i)
  set Zp := ∏ i, algebraMap (X.presheaf.stalk x) X.functionField (z i) with hZpdef
  have hZp0 : Zp ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hzK0 i
  have hK0 : g * Zp ^ (m - 1) ≠ 0 := mul_ne_zero hg0 (pow_ne_zero _ hZp0)
  obtain ⟨h, hh⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg x hK0
    fun P hxP => by
      have hτm0 : ω₀ ≠ 0 := by
        rw [hω₀, ← basisOfSpanSingleton_apply hτK hτK0 (), ← ZTensorPower.basis_natCast]
        exact (ZTensorPower.basis bK (m : ℤ)).ne_zero ()
      have hF : P.ordForm ω₀ = 0 := ordForm_formPow_topFormsMap_eq_zero hn hτ P hxP m
      have hordg : X.ord g P.genericPoint = P.ordForm s := by
        rw [hsg, MMP.Mori.PrimeDivisor.ordForm_smul_of_topologicalKrullDim_eq P hn hg0 hτm0,
          hF, add_zero]
      have hsP := ((mem_logPluricanonicalSections sX).mp hs).2 P ⟨x, hxP, trivial⟩ hs0
      rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
        Int.cast_natCast] at hsP
      rw [Scheme.ord_mul hg0 (pow_ne_zero _ hZp0), ord_pow hZp0,
        mulVal_prod (v := fun f => X.ord f P.genericPoint) (fun _ _ => Scheme.ord_mul) _ _ hzK0]
      have hnn : ∀ i, 0 ≤ X.ord (algebraMap (X.presheaf.stalk x) X.functionField (z i))
          P.genericPoint := fun i => ord_algebraMap_stalk_nonneg P hxP (z i) (hzK0 i)
      have hsum0 : 0 ≤ ∑ i, X.ord (algebraMap (X.presheaf.stalk x) X.functionField (z i))
          P.genericPoint := Finset.sum_nonneg fun i _ => hnn i
      by_cases hbP : B.coeff P = 0
      · rw [hbP, mul_zero, Int.floor_zero, add_zero] at hsP
        have : (0 : ℤ) ≤ ((m - 1 : ℕ) : ℤ) * ∑ i, X.ord (algebraMap (X.presheaf.stalk x)
            X.functionField (z i)) P.genericPoint := mul_nonneg (Int.natCast_nonneg _) hsum0
        linarith
      · have hPs : P ∈ B.support := Finsupp.mem_support_iff.mpr hbP
        set i₀ := j ⟨P, hPs, hxP⟩
        have h1 : X.ord (algebraMap (X.presheaf.stalk x) X.functionField (z i₀))
            P.genericPoint = 1 :=
          ord_algebraMap_eq_one_of_stalk_idealSheaf_eq_span P hxP (hI ⟨P, hPs, hxP⟩)
        have hsum1 : 1 ≤ ∑ i, X.ord (algebraMap (X.presheaf.stalk x) X.functionField (z i))
            P.genericPoint := by
          rw [← h1]
          exact Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ i₀)
        have hfl : ⌊(m : ℚ) * B.coeff P⌋ ≤ (m : ℤ) - 1 := by
          have hlt : (m : ℚ) * B.coeff P < m := by
            have := hB P
            have hm' : (0 : ℚ) < m := by exact_mod_cast hm
            calc (m : ℚ) * B.coeff P < m * 1 := mul_lt_mul_of_pos_left this hm'
              _ = m := mul_one _
          have := Int.floor_lt.mpr (show (m : ℚ) * B.coeff P < ((m : ℤ) : ℚ) by exact_mod_cast hlt)
          omega
        have hm1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
        have h2 : ((m - 1 : ℕ) : ℤ) * 1 ≤ ((m - 1 : ℕ) : ℤ) * ∑ i, X.ord (algebraMap
            (X.presheaf.stalk x) X.functionField (z i)) P.genericPoint :=
          mul_le_mul_of_nonneg_left hsum1 (Int.natCast_nonneg _)
        linarith
  refine ⟨d, z, hd, b, h, hzm, hz0, hb, ?_⟩
  rw [hh, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hZp0), mul_one]
  exact hsg

end Presentation

/-! ### The order of the pulled-back pluriform along a prime divisor -/

section PullbackOrder

/-- **The pole bound in the local algebra.** Let `R → A` be a homomorphism from a local
`ℂ`-algebra to a discrete valuation ring, `K`, `L` their fraction fields, `b` a basis of
`Ω_{R/ℂ}` extending `dz₁, …, dz_d` for elements `zᵢ` mapping into the maximal ideal of `A`, and
`τ = b₀ ∧ b₁`. If `τ` pulls back to a generator of `Ω²_{L/ℂ}`, then for `h ∈ R` the pull-back of
`h (z₁ ⋯ z_d)^{-(m-1)} τ^{⊗m}` has order at least `1 - m` along `A`: the poles `zᵢ^{-(m-1)}` are
compensated by the zeros of `dzᵢ` on `A`, of order one less than those of `zᵢ`. -/
private theorem one_sub_le_ord_pullback_core
    {R A K L : Type*} [CommRing R] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra ℂ R] [Algebra ℂ A] [Algebra ℂ K] [Algebra ℂ L]
    [Algebra R A] [Algebra R K] [Algebra K L] [Algebra A L] [Algebra R L]
    [IsScalarTower ℂ R A] [IsScalarTower ℂ R K] [IsScalarTower ℂ K L] [IsScalarTower ℂ A L]
    [IsScalarTower ℂ R L] [IsScalarTower R K L] [IsScalarTower R A L]
    [IsFractionRing R K] [IsFractionRing A L] {m : ℕ} (hm : 0 < m)
    {d : ℕ} (hd : d ≤ 2) (z : Fin d → R) (b : Module.Basis (Fin 2) R Ω[R⁄ℂ])
    (hb : ∀ i : Fin d, b (Fin.castLE hd i) = KaehlerDifferential.D ℂ R (z i))
    (hzA : ∀ i, algebraMap R A (z i) ∈ IsLocalRing.maximalIdeal A) (hz0 : ∀ i, z i ≠ 0)
    (h : R) (hh : h ≠ 0) {σ : ⋀[A]^2 Ω[A⁄ℂ]} (hσ : Submodule.span A {σ} = ⊤)
    (hσ0 : topFormsMap ℂ A L 2 σ ≠ 0)
    (hgen : IsPullbackGenerator L (topFormsMap ℂ R K 2 (exteriorPower.ιMulti R 2 b)))
    (v : L → ℤ) (hmul : ∀ x y : L, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hnonneg : ∀ a : A, a ≠ 0 → 0 ≤ v (algebraMap A L a))
    (hunif : ∀ (u : Aˣ) {ϖ : A}, Irreducible ϖ → ∀ n : ℕ, v (algebraMap A L (u * ϖ ^ n)) = n) :
    1 - (m : ℤ) ≤ v (formCoeff A hσ hσ0 (pullbackForms (K := K) (K' := L) (m : ℤ)
      ((algebraMap R K h * ((∏ i, algebraMap R K (z i)) ^ (m - 1))⁻¹) •
        formPow (topFormsMap ℂ R K 2 (exteriorPower.ιMulti R 2 b)) m))) := by
  classical
  set τ := exteriorPower.ιMulti R 2 b with hτdef
  set τK := topFormsMap ℂ R K 2 τ with hτKdef
  rw [pullbackForms_smul_formPow hgen m]
  have hcomp : topFormsMap ℂ K L 2 τK = topFormsMap ℂ A L 2 (topFormsMap ℂ R A 2 τ) :=
    (MMP.Threefold.Mori.Helpers.topFormsMap_comp (B := K) τ).trans
      (MMP.Threefold.Mori.Helpers.topFormsMap_comp (B := A) τ).symm
  have hmem : topFormsMap ℂ R A 2 τ ∈ Submodule.span A {σ} := by
    rw [hσ]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hinjL : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  have hsmul_inj : ∀ r r' : A, r • σ = r' • σ → r = r' := by
    intro r r' hrr
    have := congrArg (topFormsMap ℂ A L 2) hrr
    rw [map_smul, map_smul, ← algebraMap_smul L r, ← algebraMap_smul L r'] at this
    exact hinjL (smul_left_injective L hσ0 this)
  have hRL : ∀ r : R, algebraMap A L (algebraMap R A r) = algebraMap K L (algebraMap R K r) :=
    fun r => by rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hRK0 : ∀ r : R, r ≠ 0 → algebraMap R A r ≠ 0 := by
    intro r hr h0
    have := congrArg (algebraMap A L) h0
    rw [hRL, map_zero, map_eq_zero_iff _ (algebraMap K L).injective,
      map_eq_zero_iff _ (IsFractionRing.injective R K)] at this
    exact hr this
  have hdec : ∀ i, ∃ (n : ℕ) (u : Aˣ), algebraMap R A (z i) = u * ϖ ^ (n + 1) := fun i => by
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hRK0 _ (hz0 i)) hϖ
    cases n with
    | zero =>
      exfalso
      rw [pow_zero, mul_one] at hu
      exact (hzA i) (hu ▸ u.isUnit)
    | succ n => exact ⟨n, u, hu⟩
  choose n u hnu using hdec
  set S := ∑ i, (n i + 1) with hSdef
  have hτA : topFormsMap ℂ R A 2 τ = wedgeTwo (KaehlerDifferential.map ℂ ℂ R A (b 0))
      (KaehlerDifferential.map ℂ ℂ R A (b 1)) := by
    rw [hτdef, topFormsMap_ιMulti, wedgeTwo_apply]
    congr 1
    funext j
    fin_cases j <;> rfl
  have hwedge : ∃ ω' : ⋀[A]^2 Ω[A⁄ℂ], topFormsMap ℂ R A 2 τ = ϖ ^ (S - 1) • ω' := by
    obtain rfl | rfl | rfl : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    · exact ⟨topFormsMap ℂ R A 2 τ, by simp [hSdef]⟩
    · have h0 : b 0 = KaehlerDifferential.D ℂ R (z 0) := hb 0
      obtain ⟨ω', hω'⟩ := exists_wedgeTwo_D_left_eq_pow_smul (k := ℂ) ϖ ((u 0 : Aˣ) : A) (n 0)
        (KaehlerDifferential.map ℂ ℂ R A (b 1))
      refine ⟨ω', ?_⟩
      rw [hτA, h0, KaehlerDifferential.map_D, hnu 0, mul_comm, hω']
      simp [hSdef]
    · have h0 : b 0 = KaehlerDifferential.D ℂ R (z 0) := hb 0
      have h1 : b 1 = KaehlerDifferential.D ℂ R (z 1) := hb 1
      obtain ⟨ω', hω'⟩ := exists_wedgeTwo_D_D_eq_pow_smul (k := ℂ) ϖ ((u 0 : Aˣ) : A)
        ((u 1 : Aˣ) : A) (n 0) (n 1)
      refine ⟨ω', ?_⟩
      have hS2 : S - 1 = n 0 + n 1 + 1 := by
        rw [hSdef, Fin.sum_univ_two]
        omega
      rw [hτA, h0, h1, KaehlerDifferential.map_D, KaehlerDifferential.map_D, hnu 0, hnu 1,
        mul_comm _ (ϖ ^ (n 0 + 1)), mul_comm _ (ϖ ^ (n 1 + 1)), hω', hS2]
  obtain ⟨ω', hω'⟩ := hwedge
  have hmem' : ω' ∈ Submodule.span A {σ} := by
    rw [hσ]; exact Submodule.mem_top
  obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.mp hmem'
  have hcc : c = ϖ ^ (S - 1) * c' := hsmul_inj _ _ (by rw [hc, hω', ← hc', smul_smul])
  have hσL : topFormsMap ℂ K L 2 τK = algebraMap A L c • topFormsBasis A hσ hσ0 () := by
    rw [hcomp, ← hc, map_smul, topFormsBasis_apply, algebraMap_smul]
  rw [hσL, formPow_smul, smul_smul, formCoeff, repr_smul_formPow]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_smul] at hσL
    exact hgen.2.2 hσL
  have hc'0 : c' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcc
    exact hc0 hcc
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hP : ∏ i, algebraMap K L (algebraMap R K (z i)) =
      ∏ i, algebraMap A L ((u i : A) * ϖ ^ (n i + 1)) :=
    Finset.prod_congr rfl fun i _ => by rw [← hRL, hnu]
  have hzL0 : ∀ i, algebraMap A L ((u i : A) * ϖ ^ (n i + 1)) ≠ 0 := fun i =>
    (map_ne_zero_iff _ hinjL).mpr (mul_ne_zero (u i).ne_zero (pow_ne_zero _ hϖ0))
  have hP0 : ∏ i, algebraMap A L ((u i : A) * ϖ ^ (n i + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hzL0 i
  have hhL0 : algebraMap A L (algebraMap R A h) ≠ 0 :=
    (map_ne_zero_iff _ hinjL).mpr (hRK0 h hh)
  have hcL0 : algebraMap A L c ≠ 0 := (map_ne_zero_iff _ hinjL).mpr hc0
  have hvP : v (∏ i, algebraMap A L ((u i : A) * ϖ ^ (n i + 1))) = S := by
    rw [mulVal_prod hmul _ _ hzL0, hSdef, Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ => hunif (u i) hϖ _
  have hvc : v (algebraMap A L c) = ((S - 1 : ℕ) : ℤ) + v (algebraMap A L c') := by
    have h1 := hunif 1 hϖ (S - 1)
    rw [Units.val_one, one_mul] at h1
    rw [hcc, map_mul, hmul _ _ ((map_ne_zero_iff _ hinjL).mpr (pow_ne_zero _ hϖ0))
      ((map_ne_zero_iff _ hinjL).mpr hc'0), h1]
  have hvh : 0 ≤ v (algebraMap A L (algebraMap R A h)) := hnonneg _ (hRK0 h hh)
  have hvc' : 0 ≤ v (algebraMap A L c') := hnonneg c' hc'0
  rw [map_mul, map_inv₀, map_pow, map_prod, hP, ← hRL,
    hmul _ _ (mul_ne_zero hhL0 (inv_ne_zero (pow_ne_zero _ hP0))) (pow_ne_zero _ hcL0),
    hmul _ _ hhL0 (inv_ne_zero (pow_ne_zero _ hP0)), mulVal_inv hmul (pow_ne_zero _ hP0),
    mulVal_pow hmul hP0, mulVal_pow hmul hcL0, hvP, hvc]
  have hmc : 0 ≤ (m : ℤ) * v (algebraMap A L c') := mul_nonneg (Int.natCast_nonneg m) hvc'
  rcases Nat.eq_zero_or_pos S with hS | hS
  · rw [hS]
    simp only [Nat.zero_sub, Nat.cast_zero, mul_zero, neg_zero, add_zero, zero_add]
    have : (0 : ℤ) < m := by exact_mod_cast hm
    linarith
  · have e1 : ((S - 1 : ℕ) : ℤ) = (S : ℤ) - 1 := by omega
    have e2 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
    rw [e1, e2]
    have key : v (algebraMap A L (algebraMap R A h)) + -(((m : ℤ) - 1) * S) +
        m * ((S : ℤ) - 1 + v (algebraMap A L c')) =
        v (algebraMap A L (algebraMap R A h)) + S - m + m * v (algebraMap A L c') := by ring
    rw [key]
    have : (1 : ℤ) ≤ S := by exact_mod_cast hS
    linarith

/-- **The pull-back of a subklt pluriform has poles of order less than `m`.** For a dominant
morphism `p : Y ⟶ X` from a smooth surface, `ord_Γ(p^* s) ≥ 1 - m` along every prime divisor `Γ`
of `Y`, for `s ∈ H⁰(X, m(K_X + B))`, `B` an snc subboundary with coefficients less than one. -/
private theorem one_sub_le_ordForm_pullback
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hn : topologicalKrullDim X = 2) {B : QDivisor X}
    (hXB : IsSNCSubboundaryPair sX B) (hB : ∀ P, B.coeff P < 1) {m : ℕ} (hm : 0 < m)
    (s : RationalPluriForms sX 2 m) (hs : s ∈ logPluricanonicalSections sX 2 m B)
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (p : Y ⟶ X) [IsDominant p] (hY : SmoothOfRelativeDimension 2 (p ≫ sX))
    (Γ : MMP.Mori.PrimeDivisor Y) :
    1 - (m : ℤ) ≤ Γ.ordForm (pullbackRationalPluriForms sX p s) := by
  classical
  by_cases hs0 : s = 0
  · subst hs0
    have h0 : pullbackRationalPluriForms sX p (0 : RationalPluriForms sX 2 m) = 0 := by
      let := functionFieldAlgebra sX
      let := functionFieldAlgebra (p ≫ sX)
      let := functionFieldMapAlgebra p
      have := isScalarTower_functionFieldMap sX p
      have := pullbackForms_smul (K := X.functionField) (K' := Y.functionField) (m := m)
        (0 : X.functionField) (0 : PluriForms ℂ X.functionField 2 m)
      rwa [zero_smul, map_zero, zero_smul] at this
    rw [h0, Γ.ordForm_zero]
    omega
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (p ≫ sX)
  let := functionFieldMapAlgebra p
  have := isScalarTower_functionFieldMap sX p
  have : LocallyOfFiniteType sX := hXB.isProjectiveVariety.1.toLocallyOfFiniteType
  have := hY
  have : Smooth (p ≫ sX) := SmoothOfRelativeDimension.smooth (n := 2) (p ≫ sX)
  have : LocallyOfFiniteType (p ≫ sX) := inferInstance
  have hdimY : topologicalKrullDim Y = 2 := by
    exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 2 (p ≫ sX)
  obtain ⟨d, z, hd, b, h, hzm, hz0, hb, hsx⟩ :=
    exists_local_presentation hn hXB hB hm s hs hs0 (p Γ.genericPoint)
  let := stalkAlgebra sX (p Γ.genericPoint)
  have := isScalarTower_stalk_functionField sX (p Γ.genericPoint)
  let := stalkAlgebra (p ≫ sX) Γ.genericPoint
  have := isScalarTower_stalk_functionField (p ≫ sX) Γ.genericPoint
  obtain ⟨σ, hσ, hσ0⟩ := Γ.exists_topForms_generator_of_topologicalKrullDim_eq (sX := p ≫ sX) hdimY
  let : Algebra (X.presheaf.stalk (p Γ.genericPoint)) Γ.localRing :=
    (p.stalkMap Γ.genericPoint).hom.toAlgebra
  have : IsScalarTower ℂ (X.presheaf.stalk (p Γ.genericPoint)) Γ.localRing :=
    MMP.Threefold.Resolution.isScalarTower_stalkMap sX p Γ.genericPoint
  let : Algebra (X.presheaf.stalk (p Γ.genericPoint)) Y.functionField :=
    ((algebraMap X.functionField Y.functionField).comp
      (algebraMap (X.presheaf.stalk (p Γ.genericPoint)) X.functionField)).toAlgebra
  have : IsScalarTower (X.presheaf.stalk (p Γ.genericPoint)) X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (X.presheaf.stalk (p Γ.genericPoint)) Γ.localRing Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => MMP.Mori.functionFieldMap_algebraMap_stalk p _ r
  have : IsScalarTower ℂ (X.presheaf.stalk (p Γ.genericPoint)) Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change _ = algebraMap X.functionField Y.functionField
        (algebraMap (X.presheaf.stalk (p Γ.genericPoint)) X.functionField
          (algebraMap ℂ (X.presheaf.stalk (p Γ.genericPoint)) c))
      rw [← IsScalarTower.algebraMap_apply ℂ (X.presheaf.stalk (p Γ.genericPoint)) X.functionField,
        ← IsScalarTower.algebraMap_apply ℂ X.functionField Y.functionField]
  have hAL : ∀ r : X.presheaf.stalk (p Γ.genericPoint),
      algebraMap X.functionField Y.functionField
        (algebraMap (X.presheaf.stalk (p Γ.genericPoint)) X.functionField r) =
      algebraMap Γ.localRing Y.functionField
        (algebraMap (X.presheaf.stalk (p Γ.genericPoint)) Γ.localRing r) :=
    fun r => MMP.Mori.functionFieldMap_algebraMap_stalk p _ r
  set τ := exteriorPower.ιMulti (X.presheaf.stalk (p Γ.genericPoint)) 2 b with hτdef
  have hτ : Submodule.span (X.presheaf.stalk (p Γ.genericPoint)) {τ} = ⊤ :=
    (Submodule.span_singleton_eq_top_iff _ _).mpr (MMP.Intersection.bijective_smul_ιMulti_basis b).2
  set τK := topFormsMap ℂ (X.presheaf.stalk (p Γ.genericPoint)) X.functionField 2 τ with hτKdef
  have hτK : Submodule.span X.functionField {τK} = ⊤ :=
    span_singleton_topFormsMap (nonZeroDivisors (X.presheaf.stalk (p Γ.genericPoint))) hτ
  have := essFiniteType_functionField (sX := sX)
  have hKrank : Module.finrank X.functionField Ω[X.functionField⁄ℂ] = 2 :=
    (finrank_kaehlerDifferential_eq_trdeg ℂ X.functionField).trans
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn)
  have : FiniteDimensional X.functionField Ω[X.functionField⁄ℂ] :=
    Module.finite_of_finrank_eq_succ hKrank
  have := nontrivial_exteriorPower_of_finrank_eq ℂ X.functionField hKrank
  have hτK0 : τK ≠ 0 := topFormsMap_ne_zero_of_span_eq_top hτ
  have hgen : IsPullbackGenerator Y.functionField τK := by
    obtain ⟨ω', hω'⟩ := exists_isPullbackGenerator_of_topologicalKrullDim_eq sX p hn hdimY
    exact MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω' hτK hτK0
  have := Γ.isDiscreteValuationRing_localRing
  have hh : h ≠ 0 := by
    rintro rfl
    apply hs0
    rw [hsx, map_zero, zero_mul]
    exact zero_smul _ _
  have hzA : ∀ i, algebraMap (X.presheaf.stalk (p Γ.genericPoint)) Γ.localRing (z i) ∈
      IsLocalRing.maximalIdeal Γ.localRing := fun i hu =>
    hzm i (isUnit_of_map_unit (p.stalkMap Γ.genericPoint).hom _ hu)
  have hpb : pullbackRationalPluriForms sX p s =
      pullbackForms (K := X.functionField) (K' := Y.functionField) (m : ℤ)
        ((algebraMap (X.presheaf.stalk (p Γ.genericPoint)) X.functionField h *
          ((∏ i, algebraMap (X.presheaf.stalk (p Γ.genericPoint)) X.functionField (z i)) ^
            (m - 1))⁻¹) • formPow τK m) := by
    rw [hsx]; rfl
  rw [MMP.Mori.PrimeDivisor.ordForm_eq Γ _ hσ hσ0, hpb]
  exact one_sub_le_ord_pullback_core hm hd z b hb hzA hz0 h hh hσ hσ0 hgen
    (fun f => Y.ord f Γ.genericPoint) (fun _ _ hx hy => Scheme.ord_mul hx hy)
    (fun a ha => ord_algebraMap_localRing_nonneg Γ a ha)
    (fun u _ hϖ n => ord_algebraMap_unit_mul_pow Γ u hϖ n)

end PullbackOrder

/-- The root form of a pluriform pulled back to a dominant smooth surface has no poles. -/
private theorem formPow_one_mem_of_formPow_eq_pullback
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hn : topologicalKrullDim X = 2) {B : QDivisor X}
    (hXB : IsSNCSubboundaryPair sX B) (hB : ∀ P, B.coeff P < 1)
    {m : ℕ} (hm : 0 < m)
    (s : RationalPluriForms sX 2 m) (hs : s ∈ logPluricanonicalSections sX 2 m B)
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (p : Y ⟶ X) [IsDominant p] (hY : SmoothOfRelativeDimension 2 (p ≫ sX)) :
    letI := functionFieldAlgebra (p ≫ sX)
    ∀ ω : ⋀[Y.functionField]^2 Ω[Y.functionField⁄ℂ],
      (formPow ω m : RationalPluriForms (p ≫ sX) 2 m) = pullbackRationalPluriForms sX p s →
      (formPow ω 1 : RationalPluriForms (p ≫ sX) 2 (1 : ℕ)) ∈
        logPluricanonicalSections (p ≫ sX) 2 1 0 := by
  let := functionFieldAlgebra (p ≫ sX)
  intro ω hω
  have : LocallyOfFiniteType sX := hXB.isProjectiveVariety.1.toLocallyOfFiniteType
  have := hY
  have : Smooth (p ≫ sX) := SmoothOfRelativeDimension.smooth (n := 2) (p ≫ sX)
  have : LocallyOfFiniteType (p ≫ sX) := inferInstance
  have hdimY : topologicalKrullDim Y = 2 := by
    exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 2 (p ≫ sX)
  set τ₁ : RationalPluriForms (p ≫ sX) 2 (1 : ℕ) := formPow ω 1 with hτ₁
  change τ₁ ∈ logPluricanonicalSections (p ≫ sX) 2 1 0
  rw [mem_logPluricanonicalSections, mem_pluricanonicalSections]
  refine ⟨fun hU => absurd hU (by simp), fun Γ _ hω0 => ?_⟩
  rw [DivisorWithCoeffs.coeff_roundDown, smul_zero, DivisorWithCoeffs.coeff_zero, Int.floor_zero,
    add_zero]
  have key := one_sub_le_ordForm_pullback hn hXB hB hm s hs p hY Γ
  rw [← hω] at key
  let := stalkAlgebra (p ≫ sX) Γ.genericPoint
  have := isScalarTower_stalk_functionField (p ≫ sX) Γ.genericPoint
  obtain ⟨σ, hσ, hσ0⟩ := Γ.exists_topForms_generator_of_topologicalKrullDim_eq (sX := p ≫ sX) hdimY
  set bσ := topFormsBasis Γ.localRing hσ hσ0 with hbσ
  set c := bσ.repr ω () with hcdef
  have hωc : ω = c • bσ () := (basis_unit_repr_smul bσ ω).symm
  have hc0 : c ≠ 0 := by
    rintro h0
    apply hω0
    rw [hτ₁, hωc, h0, zero_smul]
    change formPow (0 : ⋀[Y.functionField]^2 Ω[Y.functionField⁄ℂ]) 1 = 0
    rw [← zero_smul Y.functionField (0 : ⋀[Y.functionField]^2 Ω[Y.functionField⁄ℂ]),
      formPow_smul, zero_pow one_ne_zero, zero_smul]
  have hcoef : ∀ a : ℕ, formCoeff Γ.localRing hσ hσ0 (formPow ω a) = c ^ a := fun a => by
    rw [formCoeff, hωc, formPow_smul, repr_smul_formPow]
  have hord : ∀ a : ℕ, Γ.ordForm (show RationalPluriForms (p ≫ sX) 2 (a : ℕ) from formPow ω a) =
      a * Y.ord c Γ.genericPoint := fun a => by
    rw [MMP.Mori.PrimeDivisor.ordForm_eq Γ _ hσ hσ0]
    change Y.ord (formCoeff Γ.localRing hσ hσ0 (formPow ω a)) _ = _
    rw [hcoef, ord_pow hc0]
  have h1 := hord 1
  have hm' := hord m
  change 1 - (m : ℤ) ≤ Γ.ordForm (show RationalPluriForms (p ≫ sX) 2 (m : ℕ) from formPow ω m)
    at key
  change 0 ≤ Γ.ordForm τ₁
  rw [hm'] at key
  rw [h1, Nat.cast_one, one_mul]
  by_contra! hneg
  have : (m : ℤ) * Y.ord c Γ.genericPoint ≤ (m : ℤ) * (-1) :=
    mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg m)
  linarith

/-! ### Resolved cyclic covers -/

section ResolvedCover

/-- `f ∈ k(X)` has a *resolved cyclic cover of degree `m` with `b₂ ≤ b`*: finitely many integral
smooth projective surfaces `Yᵢ` dominating `X`, with `∑ᵢ b₂(Yᵢ) ≤ b`, and `zᵢ ∈ k(Yᵢ)` with
`zᵢ^m = f`, generating `∏ᵢ k(Yᵢ)` over `k(X)`, of total degree `m`; that is,
`k(X)[z]/(z^m - f) ≅ ∏ᵢ k(Yᵢ)`. -/
private def HasResolvedCyclicCover {X : Scheme.{0}} [IsIntegral X] (sX : X ⟶ Spec (.of ℂ))
    (m b : ℕ) (f : X.functionField) : Prop :=
  ∃ (k : ℕ) (Y : Fin k → Scheme.{0}) (_ : ∀ i, IsIntegral (Y i))
    (_ : ∀ i, IsLocallyNoetherian (Y i)) (_ : ∀ i, IsNormal (Y i))
    (p : ∀ i, Y i ⟶ X) (_ : ∀ i, IsDominant (p i)),
    (∀ i, IsProjectiveMorphism (p i ≫ sX)) ∧ (∀ i, SmoothOfRelativeDimension 2 (p i ≫ sX)) ∧
    ∑ i, Module.finrank ℚ
        (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace (p i ≫ sX)) ∅ 2) ≤ b ∧
    letI := fun i => functionFieldMapAlgebra (p i)
    ∃ z : ∀ i, (Y i).functionField,
      (∀ i, z i ^ m = algebraMap X.functionField (Y i).functionField f) ∧
      Algebra.adjoin X.functionField {z} = ⊤ ∧
      Module.finrank X.functionField (∀ i, (Y i).functionField) = m

private theorem HasResolvedCyclicCover.mono {X : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of ℂ)} {m b b' : ℕ} {f : X.functionField}
    (h : HasResolvedCyclicCover sX m b f) (hb : b ≤ b') : HasResolvedCyclicCover sX m b' f := by
  obtain ⟨k, Y, hI, hN, hNo, p, hp, hproj, hsm, hbet, hz⟩ := h
  exact ⟨k, Y, hI, hN, hNo, p, hp, hproj, hsm, hbet.trans hb, hz⟩

/-- Rescaling `f` by an `m`-th power `λ^m` of a nonzero element of `k(X)` rescales the root:
`z ↦ λ z`. -/
private theorem HasResolvedCyclicCover.pow_mul {X : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of ℂ)} {m b : ℕ} {f : X.functionField}
    (h : HasResolvedCyclicCover sX m b f) {μ : X.functionField} (hμ : μ ≠ 0) :
    HasResolvedCyclicCover sX m b (μ ^ m * f) := by
  obtain ⟨k, Y, hI, hN, hNo, p, hp, hproj, hsm, hbet, z, hz, hadj, hrank⟩ := h
  refine ⟨k, Y, hI, hN, hNo, p, hp, hproj, hsm, hbet, ?_⟩
  let := fun i => functionFieldMapAlgebra (p i)
  refine ⟨μ • z, fun i => ?_, ?_, hrank⟩
  · rw [Pi.smul_apply, Algebra.smul_def, mul_pow, hz i, ← map_pow, ← map_mul]
  · rw [eq_top_iff, ← hadj, Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    convert Subalgebra.smul_mem (Algebra.adjoin X.functionField {μ • z})
      (Algebra.subset_adjoin (Set.mem_singleton _)) μ⁻¹ using 1
    rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]

end ResolvedCover

/-! ### The algebra `R[z]/(z^m - a)` -/

section CyclicAlgebra

open Polynomial

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

/-- `R[z]/(z^m - a)` is reduced for `R ⊆ K`, `K` a field of characteristic zero, `m ≠ 0` and
`a ≠ 0`: `z^m - a` is separable over `K`. -/
private theorem isReduced_adjoinRoot_X_pow_sub_C [CharZero K]
    (hinj : Function.Injective (algebraMap R K)) {m : ℕ} (hm : m ≠ 0) {a : R} (ha : a ≠ 0) :
    IsReduced (AdjoinRoot (Polynomial.X ^ m - C a : R[X])) := by
  refine ⟨fun x ⟨n, hn⟩ => ?_⟩
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [← map_pow, AdjoinRoot.mk_eq_zero] at hn
  rw [AdjoinRoot.mk_eq_zero]
  have hmon : (Polynomial.X ^ m - C a : R[X]).Monic := monic_X_pow_sub_C a hm
  have hsep : ((Polynomial.X ^ m - C a : R[X]).map (algebraMap R K)).Separable := by
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
    exact separable_X_pow_sub_C _ (by exact_mod_cast hm) ((map_ne_zero_iff _ hinj).mpr ha)
  have hrad : IsRadical ((Polynomial.X ^ m - C a : R[X]).map (algebraMap R K)) :=
    (isRadical_iff_squarefree_of_ne_zero (hmon.map _).ne_zero).mpr hsep.squarefree
  rw [← Polynomial.map_dvd_map (algebraMap R K) hinj hmon] at hn ⊢
  rw [Polynomial.map_pow] at hn
  exact hrad n _ hn

/-- Nonzero elements of a domain `R` are nonzerodivisors on `R[z]/(z^m - a)`, which is a free
`R`-module. -/
private theorem algebraMap_mem_nonZeroDivisors_adjoinRoot [IsDomain R] {m : ℕ} (hm : m ≠ 0)
    (a : R) {r : R} (hr : r ≠ 0) :
    algebraMap R (AdjoinRoot (Polynomial.X ^ m - C a : R[X])) r ∈
      nonZeroDivisors (AdjoinRoot (Polynomial.X ^ m - C a : R[X])) := by
  have hmon : (Polynomial.X ^ m - C a : R[X]).Monic := monic_X_pow_sub_C a hm
  have : Module.Free R (AdjoinRoot (Polynomial.X ^ m - C a : R[X])) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hmon).basis
  rw [mem_nonZeroDivisors_iff_right]
  intro y hy
  rw [mul_comm, ← Algebra.smul_def] at hy
  exact (smul_eq_zero.mp hy).resolve_left hr

/-- Minimal primes of `R[z]/(z^m - a)` lie over the zero ideal of the domain `R`. -/
private theorem comap_eq_bot_of_mem_minimalPrimes_adjoinRoot [IsDomain R] {m : ℕ} (hm : m ≠ 0)
    (a : R) {P : Ideal (AdjoinRoot (Polynomial.X ^ m - C a : R[X]))} (hP : P ∈ minimalPrimes _) :
    P.comap (algebraMap R (AdjoinRoot (Polynomial.X ^ m - C a : R[X]))) = ⊥ := by
  rw [eq_bot_iff]
  intro r hr
  by_contra h0
  exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hP) hr
    (algebraMap_mem_nonZeroDivisors_adjoinRoot hm a h0)

/-- Base change `R[z]/(p) → K[z]/(p)` sends the class of `g` to the class of its image. -/
theorem adjoinRoot_map_mk (p : R[X]) (g : R[X]) :
    AdjoinRoot.map (algebraMap R K) p (p.map (algebraMap R K)) dvd_rfl (AdjoinRoot.mk p g) =
      AdjoinRoot.mk (p.map (algebraMap R K)) (g.map (algebraMap R K)) := by
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.mk p g) = _
  rw [AdjoinRoot.lift_mk, ← AdjoinRoot.aeval_eq, Polynomial.aeval_def, Polynomial.eval₂_map,
    AdjoinRoot.algebraMap_eq]

/-- For monic `p` and injective `R → K`, base change `R[z]/(p) → K[z]/(p)` is injective. -/
theorem injective_adjoinRoot_map (hinj : Function.Injective (algebraMap R K)) {p : R[X]}
    (hp : p.Monic) :
    Function.Injective (AdjoinRoot.map (algebraMap R K) p (p.map (algebraMap R K)) dvd_rfl) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [adjoinRoot_map_mk, AdjoinRoot.mk_eq_zero] at hx
  rw [AdjoinRoot.mk_eq_zero]
  exact (Polynomial.map_dvd_map (algebraMap R K) hinj hp).mp hx

/-- **The generic algebra of a cyclic cover is the product of the function fields of its
components.** Let `S ≅ R[z]/(z^m - a)` over a domain `R` with fraction field `K` of characteristic
zero, `a ≠ 0`, and let `S → Lᵢ` be maps to fields over `K` exhibiting each `Lᵢ` as the localization
of `S` at its kernel, with pairwise distinct kernels exhausting the minimal primes of `S`. Then the
images `zᵢ` of `z` generate `∏ Lᵢ` over `K`, and `∏ Lᵢ` has dimension `m`: that is,
`K[z]/(z^m - a) ≅ ∏ Lᵢ`. -/
private theorem adjoin_eq_top_and_finrank_eq_of_adjoinRoot [CharZero K] [IsDomain R]
    [IsFractionRing R K] {m : ℕ} (hm : m ≠ 0) {a : R} (ha : a ≠ 0) {S : Type*} [CommRing S]
    [Algebra R S] (eS : S ≃ₐ[R] AdjoinRoot (Polynomial.X ^ m - C a : R[X])) {ι : Type*}
    [Finite ι] (L : ι → Type*) [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    [∀ i, Algebra S (L i)]
    (hcompat : ∀ i r, algebraMap S (L i) (algebraMap R S r) = algebraMap K (L i) (algebraMap R K r))
    (P : ι → Ideal S) [∀ i, (P i).IsPrime] (hloc : ∀ i, IsLocalization.AtPrime (L i) (P i))
    (hinj : Function.Injective P) (hsurj : ∀ Q ∈ minimalPrimes S, ∃ i, P i = Q) :
    Algebra.adjoin K {fun i => algebraMap S (L i) (eS.symm (AdjoinRoot.root _))} = ⊤ ∧
      Module.finrank K (∀ i, L i) = m := by
  classical
  have := Fintype.ofFinite ι
  generalize hpdef' : (Polynomial.X ^ m - C a : R[X]) = p at eS ⊢
  have hpdef := hpdef'.symm
  have hpm : p.Monic := hpdef ▸ monic_X_pow_sub_C a hm
  set pK : K[X] := p.map (algebraMap R K) with hpKdef
  have hpK : pK = Polynomial.X ^ m - C (algebraMap R K a) := by
    rw [hpKdef, hpdef, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
  have hpK0 : pK ≠ 0 := (hpm.map _).ne_zero
  have hinjRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  let ι₀ : AdjoinRoot p →+* AdjoinRoot pK := AdjoinRoot.map (algebraMap R K) p pK dvd_rfl
  set z : ∀ i, L i := fun i => algebraMap S (L i) (eS.symm (AdjoinRoot.root p)) with hzdef
  have hzpow : ∀ i, z i ^ m = algebraMap K (L i) (algebraMap R K a) := fun i => by
    have h1 : (AdjoinRoot.root p) ^ m = AdjoinRoot.of p a := by
      have h : AdjoinRoot.mk p (Polynomial.X ^ m - C a) = 0 :=
        AdjoinRoot.mk_eq_zero.mpr (by rw [hpdef])
      rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
      exact sub_eq_zero.mp h
    rw [hzdef, ← map_pow, ← map_pow, h1, ← AdjoinRoot.algebraMap_eq, AlgEquiv.commutes,
      hcompat]
  let θ : AdjoinRoot pK →ₐ[K] (∀ i, L i) := AdjoinRoot.liftAlgHom pK (Algebra.ofId K _) z (by
    rw [hpK, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    funext i
    simp only [Pi.sub_apply, Pi.pow_apply, Pi.zero_apply, hzpow]
    change algebraMap K (L i) _ - algebraMap K (L i) _ = 0
    exact sub_self _)
  have hθroot : θ (AdjoinRoot.root pK) = z := by
    simp [θ]
  have hcomp : ∀ i s, algebraMap S (L i) s = θ (ι₀ (eS s)) i := by
    intro i
    have : (algebraMap S (L i)).comp eS.symm.toRingEquiv.toRingHom =
        (Pi.evalRingHom L i).comp (θ.toRingHom.comp ι₀) := by
      refine AdjoinRoot.ringHom_ext (RingHom.ext fun r => ?_) ?_
      · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
          AlgEquiv.coe_ringEquiv, ← AdjoinRoot.algebraMap_eq, AlgEquiv.commutes, hcompat,
          AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Pi.evalRingHom_apply]
        rw [show ι₀ (algebraMap R (AdjoinRoot p) r) = algebraMap K (AdjoinRoot pK)
          (algebraMap R K r) from by
            rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.algebraMap_eq]
            exact AdjoinRoot.map_of _ _ _ _ r, AlgHom.commutes]
        rfl
      · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
          AlgEquiv.coe_ringEquiv, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          Pi.evalRingHom_apply, ι₀, AdjoinRoot.map_root, hθroot, hzdef]
    intro s
    have h := congrArg (fun φ => φ (eS s)) this
    simpa using h
  have hfd : FiniteDimensional K (AdjoinRoot pK) := (AdjoinRoot.powerBasis hpK0).finite
  let φ : ∀ i, AdjoinRoot pK →ₐ[K] L i := fun i => (Pi.evalAlgHom K L i).comp θ
  have hφ : ∀ i x, φ i x = θ x i := fun _ _ => rfl
  -- the kernel of `S → Lᵢ` is `Pᵢ`
  have hker : ∀ i (s : S), algebraMap S (L i) s = 0 ↔ s ∈ P i := by
    intro i s
    have := hloc i
    have hloc' := IsLocalization.AtPrime.to_map_mem_maximal_iff (L i) (P i) s
    rwa [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hloc'
  -- each `θᵢ` is surjective
  have hφsurj : ∀ i, Function.Surjective (φ i) := by
    intro i y
    have := hloc i
    obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective (P i).primeCompl y
    change ∃ x, φ i x = IsLocalization.mk' (L i) s t
    have hs : algebraMap S (L i) s ∈ (φ i).range := ⟨ι₀ (eS s), (hcomp i s).symm⟩
    have ht : algebraMap S (L i) (t : S) ∈ (φ i).range := ⟨ι₀ (eS t), (hcomp i t).symm⟩
    have halg : IsAlgebraic K (algebraMap S (L i) (t : S)) := by
      obtain ⟨x, hx⟩ := ht
      rw [← hx]
      exact (Algebra.IsAlgebraic.isAlgebraic x).algHom (φ i)
    have hinv := Subalgebra.inv_mem_of_algebraic (A := (φ i).range) (x := ⟨_, ht⟩) halg
    have ht0 : algebraMap S (L i) (t : S) ≠ 0 := fun h0 => t.2 ((hker i t).mp h0)
    have hmk : IsLocalization.mk' (L i) s t =
        algebraMap S (L i) s * (algebraMap S (L i) (t : S))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ ht0, IsLocalization.mk'_spec]
    rw [hmk]
    exact (φ i).range.mul_mem hs hinv
  -- the kernels are pairwise distinct maximal ideals
  have hφker : ∀ i, (RingHom.ker (φ i)).comap (ι₀.comp eS.toRingEquiv.toRingHom) = P i := by
    intro i
    ext s
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, ← hker i s]
    change θ (ι₀ (eS s)) i = 0 ↔ _
    rw [← hcomp]
  have hmax : ∀ i, (RingHom.ker (φ i)).IsMaximal := fun i =>
    RingHom.ker_isMaximal_of_surjective _ (hφsurj i)
  have hdist : Pairwise fun i i' => RingHom.ker (φ i) ≠ RingHom.ker (φ i') := by
    intro i i' hii' h
    apply hii'
    apply hinj
    rw [← hφker i, ← hφker i', h]
  have hcop : Pairwise (Function.onFun IsCoprime fun i => RingHom.ker (φ i)) := fun i i' hii' =>
    Ideal.isCoprime_of_isMaximal (hdist hii')
  -- `θ` is surjective
  have hθsurj : Function.Surjective θ := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.pi_quotient_surjective hcop fun i =>
      (RingHom.quotientKerEquivOfSurjective (hφsurj i)).symm (y i)
    refine ⟨x, funext fun i => ?_⟩
    have := congrArg (RingHom.quotientKerEquivOfSurjective (hφsurj i)) (hx i)
    rw [RingEquiv.apply_symm_apply] at this
    rw [← this]
    rfl
  -- `θ` is injective
  have hθinj : Function.Injective θ := by
    have hred : IsReduced (AdjoinRoot pK) := by
      rw [hpK]
      exact isReduced_adjoinRoot_X_pow_sub_C (R := K) (K := K) (fun _ _ h => h) hm
        ((map_ne_zero_iff _ hinjRK).mpr ha)
    let ψ0 : S →+* AdjoinRoot pK := ι₀.comp eS.toRingEquiv.toRingHom
    have hψ0R : ∀ r : R, ψ0 (algebraMap R S r) = algebraMap K (AdjoinRoot pK) (algebraMap R K r) :=
      fun r => by
        change ι₀ (eS (algebraMap R S r)) = _
        rw [AlgEquiv.commutes, AdjoinRoot.algebraMap_eq, AdjoinRoot.algebraMap_eq]
        exact AdjoinRoot.map_of _ _ _ _ r
    have hι₀mk : ∀ g : R[X],
        ι₀ (AdjoinRoot.mk p g) = AdjoinRoot.mk pK (g.map (algebraMap R K)) :=
      adjoinRoot_map_mk p
    have hψ0inj : Function.Injective ψ0 := (injective_adjoinRoot_map hinjRK hpm).comp eS.injective
    let : Algebra S (AdjoinRoot pK) := ψ0.toAlgebra
    have hloc0 : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))
        (AdjoinRoot pK) := by
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨_, r, hr, rfl⟩
        change IsUnit (ψ0 (algebraMap R S r))
        rw [hψ0R]
        exact (IsUnit.mk0 _ ((map_ne_zero_iff _ hinjRK).mpr
          (nonZeroDivisors.ne_zero hr))).map _
      · intro x
        obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
        obtain ⟨b, hb, hg⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) g
        refine ⟨⟨eS.symm (AdjoinRoot.mk p
          (IsLocalization.integerNormalization (nonZeroDivisors R) g)),
          ⟨algebraMap R S b, b, hb, rfl⟩⟩, ?_⟩
        change AdjoinRoot.mk pK g * ψ0 (algebraMap R S b) = ψ0 (eS.symm _)
        rw [hψ0R]
        change _ = ι₀ (eS (eS.symm _))
        rw [AlgEquiv.apply_symm_apply, hι₀mk, hg, Algebra.smul_def, Polynomial.algebraMap_apply,
          map_mul, AdjoinRoot.mk_C, mul_comm, AdjoinRoot.algebraMap_eq]
      · intro x y h
        exact ⟨1, by rw [hψ0inj h]⟩
    have : Algebra.IsIntegral R (AdjoinRoot p) := by
      have : Module.Finite R (AdjoinRoot p) := (AdjoinRoot.powerBasis' hpm).finite
      exact Algebra.IsIntegral.of_finite R _
    have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_surjective eS.symm.toAlgHom
      eS.symm.surjective
    have hQ : ∀ Q : Ideal (AdjoinRoot pK), Q.IsPrime → ∃ i, Q = RingHom.ker (φ i) := by
      intro Q hQ
      have hQ'R : (Q.comap ψ0).comap (algebraMap R S) = ⊥ := by
        rw [eq_bot_iff]
        intro r hr
        by_contra h0
        rw [Ideal.mem_comap, Ideal.mem_comap, hψ0R] at hr
        exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hr ((IsUnit.mk0 _
          ((map_ne_zero_iff _ hinjRK).mpr h0)).map _))
      have : (Q.comap ψ0).IsPrime := Ideal.comap_isPrime ψ0 Q
      have hQ'min : Q.comap ψ0 ∈ minimalPrimes S := by
        refine ⟨⟨inferInstance, bot_le⟩, fun Q'' hQ'' hle => ?_⟩
        have := hQ''.1
        by_contra hne
        have hlt : Q'' < Q.comap ψ0 := lt_of_le_of_ne hle fun h => hne (h ▸ le_rfl)
        have := Ideal.IsIntegral.comap_lt_comap (R := R) hlt
        simp only [Ideal.under_def] at this
        rw [hQ'R] at this
        exact not_lt_bot this
      obtain ⟨i, hi⟩ := hsurj _ hQ'min
      refine ⟨i, ?_⟩
      have h1 := (IsLocalization.orderIsoOfPrime (Algebra.algebraMapSubmonoid S
        (nonZeroDivisors R)) (AdjoinRoot pK)).injective
        (a₁ := ⟨Q, hQ⟩) (a₂ := ⟨RingHom.ker (φ i), (hmax i).isPrime⟩)
        (Subtype.ext (by
          change Q.comap ψ0 = (RingHom.ker (φ i)).comap ψ0
          rw [← hi]
          exact (hφker i).symm))
      exact congrArg Subtype.val h1
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hxQ : ∀ Q : Ideal (AdjoinRoot pK), Q.IsPrime → x ∈ Q := fun Q hQ' => by
      obtain ⟨i, rfl⟩ := hQ Q hQ'
      rw [RingHom.mem_ker, hφ, hx]
      rfl
    have hnil : x ∈ nilradical (AdjoinRoot pK) := by
      rw [nilradical_eq_sInf]
      exact Submodule.mem_sInf.mpr fun Q hQ' => hxQ Q hQ'
    exact IsReduced.eq_zero x (mem_nilradical.mp hnil)
  have hθbij : Function.Bijective θ := ⟨hθinj, hθsurj⟩
  let eθ : AdjoinRoot pK ≃ₐ[K] (∀ i, L i) := AlgEquiv.ofBijective θ hθbij
  refine ⟨?_, ?_⟩
  · rw [← hθroot, ← Set.image_singleton, ← AlgHom.map_adjoin, AdjoinRoot.adjoinRoot_eq_top,
      Algebra.map_top, AlgHom.range_eq_top]
    exact hθsurj
  · rw [← eθ.toLinearEquiv.finrank_eq, (AdjoinRoot.powerBasis hpK0).finrank,
      AdjoinRoot.powerBasis_dim, hpK, natDegree_X_pow_sub_C]

end CyclicAlgebra

/-! ### Dimensions of closures of points -/

section ClosureDim

/-- The dimension of the closure of a point of a scheme locally of finite type over `ℂ` does not
change under an open immersion: both are the transcendence degree of the residue field. -/
private theorem topologicalKrullDim_closure_singleton_eq_of_isOpenImmersion {X' X : Scheme.{0}}
    (f : X' ⟶ X) [IsOpenImmersion f] (s : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType s] (x' : X') :
    topologicalKrullDim (closure ({x'} : Set X')) =
      topologicalKrullDim (closure ({f x'} : Set X)) := by
  rw [topologicalKrullDim_closure_singleton_eq_trdeg ℂ X' (f ≫ s),
    topologicalKrullDim_closure_singleton_eq_trdeg ℂ X s]
  let : Algebra ℂ (X'.residueField x') :=
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (f ≫ s).appTop ≫ X'.Γevaluation x').hom.toAlgebra
  let : Algebra ℂ (X.residueField (f x')) :=
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ s.appTop ≫ X.Γevaluation (f x')).hom.toAlgebra
  let e : X.residueField (f x') ≃ₐ[ℂ] X'.residueField x' :=
    { (asIso (f.residueFieldMap x')).commRingCatIsoToRingEquiv with
      commutes' := fun c => by
        change (f.residueFieldMap x').hom (((Scheme.ΓSpecIso (.of ℂ)).inv ≫ s.appTop ≫
          X.Γevaluation (f x')).hom c) = ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (f ≫ s).appTop ≫
            X'.Γevaluation x').hom c
        rw [← CommRingCat.comp_apply, Category.assoc, Category.assoc,
          Scheme.Γevaluation_naturality, Scheme.Hom.comp_appTop, Category.assoc] }
  rw [e.trdeg_eq]

/-- The closure of a point in `Spec R` has the dimension of the quotient ring. -/
private theorem topologicalKrullDim_zeroLocus {R : Type*} [CommRing R] (I : Ideal R) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (R := R) (I : Set R)) = ringKrullDim (R ⧸ I) := by
  have he := PrimeSpectrum.isClosedEmbedding_comap_of_surjective (R ⧸ I) (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  have hr : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus (R := R) (I : Set R) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    (he.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr)).isHomeomorph).symm

/-- The dimension of the closure of the generic point of an irreducible scheme is its
dimension. -/
private theorem topologicalKrullDim_closure_genericPoint (X : Scheme.{0}) [IrreducibleSpace X] :
    topologicalKrullDim (closure ({genericPoint X} : Set X)) = topologicalKrullDim X := by
  rw [(genericPoint_spec X).def]
  exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph

end ClosureDim

/-! ### Components of a normal Noetherian scheme -/

section Components

open CategoryTheory.Limits

/-- **A normal Noetherian scheme is a finite disjoint union of normal integral schemes**: there are
finitely many open immersions `Yᵢ ⟶ Y` from normal integral schemes, with pairwise disjoint images
covering `Y`. -/
private theorem exists_fin_components (Y : Scheme.{0}) [IsNormal Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] :
    ∃ (k : ℕ) (Yc : Fin k → Scheme.{0}) (_ : ∀ i, IsNormal (Yc i)) (_ : ∀ i, IsIntegral (Yc i))
      (j : ∀ i, Yc i ⟶ Y) (_ : ∀ i, IsOpenImmersion (j i)),
      (∀ i i', i ≠ i' → Disjoint (Set.range (j i)) (Set.range (j i'))) ∧
      ∀ y : Y, ∃ i, y ∈ Set.range (j i) := by
  classical
  have : IsNoetherian Y := ⟨⟩
  have : TopologicalSpace.NoetherianSpace Y := inferInstance
  have hfin : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite :=
    fun U _ => @TopologicalSpace.NoetherianSpace.finite_irreducibleComponents _ _
      (TopologicalSpace.NoetherianSpace.set _)
  obtain ⟨ι, Yc, hNo, hInt, ⟨φ⟩⟩ := (isNormal_iff_exists_iso_coproduct hfin).mp inferInstance
  let j : ∀ c, Yc c ⟶ Y := fun c => Sigma.ι Yc c ≫ φ.inv
  have hdisj : ∀ c c', c ≠ c' → Disjoint (Set.range (j c)) (Set.range (j c')) := by
    intro c c' hcc'
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨x', hx'⟩
    have h1 : (Sigma.ι Yc c') x' = (Sigma.ι Yc c) x := by
      change (Sigma.ι Yc c' ≫ φ.inv) x' = (Sigma.ι Yc c ≫ φ.inv) x at hx'
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hx'
      exact φ.inv.isOpenEmbedding.injective hx'
    have := (sigmaι_eq_iff Yc c' c x' x).mp h1
    exact hcc' (congrArg Sigma.fst this).symm
  have hcov : ∀ y : Y, ∃ c, y ∈ Set.range (j c) := by
    intro y
    obtain ⟨⟨c, x⟩, hx⟩ := (sigmaMk Yc).surjective (φ.hom y)
    refine ⟨c, x, ?_⟩
    rw [sigmaMk_mk] at hx
    change (Sigma.ι Yc c ≫ φ.inv) x = y
    rw [Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  have hopen : ∀ c, IsOpen (Set.range (j c)) := fun c => (j c).isOpenEmbedding.isOpen_range
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun c => Set.range (j c)) hopen
    (fun y _ => Set.mem_iUnion.mpr (hcov y))
  have hι : Finite ι := by
    refine Finite.of_injective (fun c : ι => (⟨c, ?_⟩ : t)) fun c c' h => congrArg Subtype.val h
    obtain ⟨x⟩ : Nonempty (Yc c) := inferInstance
    obtain ⟨c', hc', hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (j c x)))
    by_contra hct
    have hne : c ≠ c' := fun h => hct (h ▸ hc')
    exact Set.disjoint_left.mp (hdisj c c' hne) ⟨x, rfl⟩ hx
  let e := Finite.equivFin ι
  refine ⟨Nat.card ι, fun i => Yc (e.symm i), fun i => hNo _, fun i => hInt _,
    fun i => j (e.symm i), fun i => inferInstance, fun i i' hii' => hdisj _ _ ?_, fun y => ?_⟩
  · exact fun h => hii' (e.symm.injective h)
  · obtain ⟨c, hc⟩ := hcov y
    obtain ⟨i, rfl⟩ := e.symm.surjective c
    exact ⟨i, hc⟩

end Components

/-! ### Second Betti numbers of clopen pieces -/

section BettiRetract

/-- A retract has smaller cohomology: if `r ∘ ρ = id`, then `ρ^*` is surjective. -/
private theorem finrank_le_of_retraction {A B : TopCat.{0}} (ρ : A ⟶ B) (r : B ⟶ A)
    (h : ρ ≫ r = 𝟙 A)
    (hfin : Module.Finite ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) B ∅ 2)) :
    Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) A ∅ 2) ≤
      Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) B ∅ 2) := by
  have hc := relativeSingularCohomology.map_comp ℚ (.of ℚ ℚ) ρ r (A'' := ∅) (A' := ∅) (A := ∅)
    (fun _ h => h) (fun _ h => h) 2
  have hid := relativeSingularCohomology.map_id ℚ (.of ℚ ℚ) A ∅ 2
  have hsurj : Function.Surjective
      (relativeSingularCohomology.map ℚ (.of ℚ ℚ) ρ (A := ∅) (A' := ∅) (fun _ h => h) 2).hom :=
    fun x => ⟨(relativeSingularCohomology.map ℚ (.of ℚ ℚ) r (A := ∅) (A' := ∅)
        (fun _ h => h) 2).hom x, by
      rw [← ModuleCat.comp_apply, ← hc]
      simp only [h, hid]
      rfl⟩
  exact LinearMap.finrank_le_finrank_of_surjective hsurj

open MMP.Analytic MMP.Analytic.ComplexPoints in
/-- **A clopen piece has smaller second Betti number.** If `j : Y' ⟶ Y` is an open immersion over
`ℂ` with closed image, `Y'` nonempty and quasi-compact, and `H²(Y^an; ℚ)` is finite-dimensional,
then `b₂(Y') ≤ b₂(Y)`: `Y'^an` is a retract of `Y^an`. -/
private theorem finrank_le_of_isOpenImmersion_of_isClosed {Y' Y : Scheme.{0}} (j : Y' ⟶ Y)
    [IsOpenImmersion j] (hcl : IsClosed (Set.range j)) (sY : Y ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType (j ≫ sY)] [Nonempty Y'] [CompactSpace Y']
    (hfin : Module.Finite ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace sY) ∅ 2)) :
    Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace (j ≫ sY)) ∅ 2) ≤
      Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace sY) ∅ 2) := by
  classical
  -- a `ℂ`-point of `Y'`
  obtain ⟨x₀, -, hx₀⟩ := (isClosed_univ (X := Y')).exists_closed_singleton Set.univ_nonempty
  let y₀ : ComplexPoints (j ≫ sY) :=
    ⟨pointOfClosedPoint (j ≫ sY) x₀ hx₀, pointOfClosedPoint_comp _ _ _⟩
  let ρ := realize j (sX := j ≫ sY) rfl
  have hρ : Topology.IsOpenEmbedding ρ := isOpenEmbedding_realize_of_isOpenImmersion j rfl
  have hrange : Set.range ρ = {y : ComplexPoints sY | y.toScheme ∈ j.opensRange} :=
    range_realize_of_isOpenImmersion j rfl
  have hclopen : IsClopen (Set.range ρ) := by
    rw [hrange]
    exact ⟨isClosed_setOf_toScheme_mem hcl, isOpen_setOf_toScheme_mem j.opensRange.isOpen⟩
  let r : ComplexPoints sY → ComplexPoints (j ≫ sY) := fun y =>
    if hy : y ∈ Set.range ρ then hy.choose else y₀
  have hr : ∀ x, r (ρ x) = x := fun x => by
    have hy : ρ x ∈ Set.range ρ := ⟨x, rfl⟩
    simp only [r, hy, dite_true]
    exact hρ.injective hy.choose_spec
  have hrc : Continuous r := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    by_cases hy : y ∈ Set.range ρ
    · have hon : ContinuousOn r (Set.range ρ) := by
        rw [continuousOn_iff_continuous_domRestrict]
        have : (fun y : Set.range ρ => r y) = hρ.isEmbedding.toHomeomorph.symm := by
          funext ⟨y', x', hx'⟩
          subst hx'
          change r (ρ x') = hρ.isEmbedding.toHomeomorph.symm ⟨ρ x', _⟩
          rw [hr]
          exact (hρ.isEmbedding.toHomeomorph.symm_apply_eq.mpr rfl).symm
        change Continuous (fun y : Set.range ρ => r y)
        rw [this]
        exact hρ.isEmbedding.toHomeomorph.symm.continuous
      exact hon.continuousAt (hclopen.isOpen.mem_nhds hy)
    · have : r =ᶠ[nhds y] fun _ => y₀ := by
        filter_upwards [hclopen.compl.isOpen.mem_nhds hy] with y' hy'
        simp only [r]
        split_ifs with h
        · exact absurd h hy'
        · rfl
      exact (continuousAt_const).congr this.symm
  exact finrank_le_of_retraction (analyticMap j rfl) (TopCat.ofHom ⟨r, hrc⟩)
    (by ext x; exact congrArg (fun z => z.hom) (hr x)) hfin

end BettiRetract

/-! ### Maximal points -/

section MaximalPoints

/-- In a Noetherian quasi-sober space, a point without proper generizations lies in every dense
open subset: it is the generic point of an irreducible component, and a dense open meets that
component outside the others. -/
private theorem mem_of_isOpen_of_dense_of_maximal {Z : Type*} [TopologicalSpace Z] [QuasiSober Z]
    [T0Space Z] [TopologicalSpace.NoetherianSpace Z] {U : Set Z} (hUo : IsOpen U) (hUd : Dense U)
    {w : Z} (hw : ∀ y, y ⤳ w → y = w) : w ∈ U := by
  classical
  set C := closure ({w} : Set Z) with hCdef
  have hCirr : IsIrreducible C := isIrreducible_singleton.closure
  have hCmax : C ∈ irreducibleComponents Z := by
    refine ⟨hCirr, fun D hD hCD => ?_⟩
    have hDc : IsIrreducible (closure D) := hD.closure
    obtain ⟨z, hz⟩ := QuasiSober.sober hDc isClosed_closure
    have hwz : z ⤳ w := specializes_iff_mem_closure.mpr (by
      rw [hz.def]; exact subset_closure (hCD (subset_closure (Set.mem_singleton w))))
    rw [hw z hwz] at hz
    rw [hCdef, hz.def]
    exact subset_closure
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := Z)
  set O := (⋃ C' ∈ {C' ∈ irreducibleComponents Z | C' ≠ C}, C')ᶜ with hOdef
  have hOo : IsOpen O := by
    refine (Set.Finite.isClosed_biUnion (hfin.subset fun C' hC' => hC'.1) fun C' hC' =>
      isClosed_of_mem_irreducibleComponents C' hC'.1).isOpen_compl
  have hwO : w ∈ O := by
    simp only [hOdef, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro C' hC' hwC'
    have : C ⊆ C' := closure_minimal (Set.singleton_subset_iff.mpr hwC')
      (isClosed_of_mem_irreducibleComponents C' hC'.1)
    exact hC'.2 ((hCmax.2 hC'.1.1 this).antisymm this)
  obtain ⟨u, huO, huU⟩ := hUd.inter_open_nonempty O hOo ⟨w, hwO⟩
  have huC : u ∈ C := by
    by_contra huC
    have hne : irreducibleComponent u ≠ C := fun h => huC (h ▸ mem_irreducibleComponent)
    simp only [hOdef, Set.mem_compl_iff, Set.mem_iUnion, not_exists] at huO
    exact huO _ ⟨irreducibleComponent_mem_irreducibleComponents u, hne⟩ mem_irreducibleComponent
  have hgen : IsGenericPoint w C := rfl
  exact (hgen.mem_open_set_iff hUo).mpr ⟨u, huC, huU⟩

/-- A point without proper generizations corresponds, in an affine chart, to a minimal prime. -/
private theorem mem_minimalPrimes_of_maximal {F : Scheme.{0}} (V : F.Opens) {A : CommRingCat.{0}}
    (e : V.toScheme ≅ Spec A) {w : F} (hwV : w ∈ V) (hw : ∀ y, y ⤳ w → y = w) :
    (e.hom (⟨w, hwV⟩ : V.toScheme)).asIdeal ∈ minimalPrimes A := by
  set P : PrimeSpectrum A := e.hom (⟨w, hwV⟩ : V.toScheme) with hPdef
  refine ⟨⟨P.isPrime, bot_le⟩, fun Q hQ hle => ?_⟩
  let Q' : PrimeSpectrum A := ⟨Q, hQ.1⟩
  have hsp : Q' ⤳ P := (PrimeSpectrum.le_iff_specializes Q' P).mp hle
  have hee : e.inv P = ⟨w, hwV⟩ := by
    change (e.hom ≫ e.inv) _ = _
    rw [Iso.hom_inv_id]; rfl
  have hsp' : V.ι (e.inv Q') ⤳ V.ι (e.inv P) := (hsp.map e.inv.continuous).map V.ι.continuous
  have heP : V.ι (e.inv P) = w := by rw [hee]; rfl
  rw [heP] at hsp'
  have h3 : V.ι (e.inv Q') = V.ι (e.inv P) := (hw _ hsp').trans heP.symm
  have h5 : Q' = P := e.inv.isOpenEmbedding.injective (V.ι.isOpenEmbedding.injective h3)
  exact (congrArg PrimeSpectrum.asIdeal h5).ge

/-- A homeomorphism `e : A ≃ₜ B` between open subsets, induced by a map `p`, matches the points
of `A` without proper generizations with the points of `B` without proper generizations. -/
private theorem forall_specializes_eq_iff_of_homeomorph {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] (p : Y → Z) {A : Set Y} {B : Set Z} (hA : IsOpen A) (hB : IsOpen B)
    (e : A ≃ₜ B) (he : ∀ a, (e a : Z) = p a) (a : A) :
    (∀ y, y ⤳ (a : Y) → y = a) ↔ ∀ w, w ⤳ p a → w = p a := by
  constructor
  · intro h w hw
    have hwB : w ∈ B := hw.mem_open hB (he a ▸ (e a).2)
    have h1 : (⟨w, hwB⟩ : B) ⤳ e a := by
      rw [subtype_specializes_iff, he]
      exact hw
    have h2 := (subtype_specializes_iff _ _).mp (by simpa using h1.map e.symm.continuous)
    have h4 : e.symm ⟨w, hwB⟩ = a := Subtype.ext (h _ h2)
    have h5 : (⟨w, hwB⟩ : B) = e a := by rw [← h4, e.apply_symm_apply]
    rw [← he, ← h5]
  · intro h y hy
    have hyA : y ∈ A := hy.mem_open hA a.2
    have h1 : e ⟨y, hyA⟩ ⤳ e a :=
      ((subtype_specializes_iff _ _).mpr hy).map e.continuous
    have h2 := (subtype_specializes_iff _ _).mp h1
    rw [he, he] at h2
    have h3 : e ⟨y, hyA⟩ = e a := Subtype.ext (by rw [he, he]; exact h _ h2)
    exact congrArg Subtype.val (e.injective h3)

end MaximalPoints

/-! ### Schemes that are locally cyclic covers -/

section LocalCyclicCover

open CategoryTheory.Limits

/-- A section `a` with `a = ψ^m f` in `k(X)`, `ψ, f ≠ 0`, is nonzero. -/
private theorem ne_zero_of_germToFunctionField_eq {X : Scheme.{0}} [IsIntegral X] {U : X.Opens}
    [hU : Nonempty U] {a : Γ(X, U)} {ψ f : X.functionField} {m : ℕ} (hψ : ψ ≠ 0) (hf : f ≠ 0)
    (ha : X.germToFunctionField U a = ψ ^ m * f) : a ≠ 0 := by
  rintro rfl
  rw [map_zero] at ha
  exact mul_ne_zero (pow_ne_zero _ hψ) hf ha.symm

/-- An affine open `U` of `X` is a *cyclic cover chart* of `q : F ⟶ X` for `z^m = f` if there are
`a ∈ Γ(X, U)` and `ψ ∈ k(X)^×` with `a = ψ^m f` in `k(X)`, such that `q⁻¹(U) ⟶ U` is
`Spec Γ(X, U)[z]/(z^m - a) ⟶ Spec Γ(X, U)`. -/
private def IsCyclicCoverChart {F X : Scheme.{0}} [IsIntegral X] (q : F ⟶ X) (m : ℕ)
    (f : X.functionField) (U : X.Opens) : Prop :=
  ∃ (hU : IsAffineOpen U) (_ : Nonempty U) (a : Γ(X, U)) (ψ : X.functionField), ψ ≠ 0 ∧
    X.germToFunctionField U a = ψ ^ m * f ∧
    ∃ e : (q ⁻¹ᵁ U).toScheme ≅
        Spec (.of (AdjoinRoot (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, U)))),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
          (AdjoinRoot (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, U))))) =
        q ∣_ U ≫ hU.isoSpec.hom

/-- A cartesian square exhibiting `Spec Γ(X, U)[z]/(z^m - a)` as the inverse image of an affine
open `U` makes `U` a cyclic cover chart. -/
private theorem isCyclicCoverChart_of_isPullback {F X : Scheme.{0}} [IsIntegral X] {q : F ⟶ X}
    {m : ℕ} {f : X.functionField} {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    {a : Γ(X, U)} {ψ : X.functionField} (hψ : ψ ≠ 0) (ha : X.germToFunctionField U a = ψ ^ m * f)
    {j : Spec (.of (AdjoinRoot (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, U)))) ⟶ F}
    (hj : IsPullback j (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
      (AdjoinRoot (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, U)))))) q hU.fromSpec) :
    IsCyclicCoverChart q m f U := by
  have h' : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
      (AdjoinRoot (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, U))))) ≫ hU.isoSpec.inv)
      j U.ι q :=
    hj.flip.of_iso (Iso.refl _) hU.isoSpec.symm (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  let e := (isPullback_morphismRestrict q U).isoIsPullback _ _ h'
  have he : e.hom ≫ _ ≫ hU.isoSpec.inv = q ∣_ U :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  refine ⟨hU, inferInstance, a, ψ, hψ, ha, e, ?_⟩
  rw [← he]
  simp

/-- `q : F ⟶ X` is *locally the cyclic cover* `z^m = f`: cyclic cover charts cover `X`. -/
private def IsLocallyCyclicCover {F X : Scheme.{0}} [IsIntegral X] (q : F ⟶ X) (m : ℕ)
    (f : X.functionField) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsCyclicCoverChart q m f U

/-- **The sections of a cyclic cover chart.** Over a chart `U`, `q⁻¹(U)` is affine with ring of
sections `Γ(X, U)[z]/(z^m - a)`, compatibly with `q^* : Γ(X, U) → Γ(F, q⁻¹U)`. -/
private theorem exists_ringEquiv_of_isCyclicCoverChart {X F : Scheme.{0}} [IsIntegral X]
    {q : F ⟶ X} {m : ℕ} {f : X.functionField} {W : X.Opens} (h : IsCyclicCoverChart q m f W) :
    ∃ (_ : IsAffineOpen W) (_ : Nonempty W) (a : Γ(X, W)) (ψ : X.functionField), ψ ≠ 0 ∧
      X.germToFunctionField W a = ψ ^ m * f ∧
      IsAffineOpen (q ⁻¹ᵁ W) ∧
      ∃ eS : Γ(F, q ⁻¹ᵁ W) ≃+*
          AdjoinRoot (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, W)),
        ∀ r, eS ((q.app W).hom r) = algebraMap Γ(X, W) _ r := by
  obtain ⟨hWa, hne, a, ψ, hψ, ha, e, he⟩ := h
  refine ⟨hWa, hne, a, ψ, hψ, ha, ?_, ?_⟩
  · have : IsAffine (Spec (.of (AdjoinRoot (Polynomial.X ^ m - Polynomial.C a :
        Polynomial Γ(X, W))))) := inferInstance
    exact IsAffine.of_isIso e.hom
  let eS : Γ(F, q ⁻¹ᵁ W) ≃+*
      AdjoinRoot (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, W)) :=
    ((q ⁻¹ᵁ W).topIso.symm ≪≫ Scheme.Γ.mapIso e.symm.op ≪≫
      Scheme.ΓSpecIso (.of (AdjoinRoot (Polynomial.X ^ m - Polynomial.C a :
        Polynomial Γ(X, W))))).commRingCatIsoToRingEquiv
  refine ⟨eS, fun r => ?_⟩
  have he' : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W)
      (AdjoinRoot (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, W))))) =
      (q ⁻¹ᵁ W).toSpecΓ ≫ Spec.map (q.app W) := by
    rw [he, IsAffineOpen.isoSpec_hom, Scheme.Opens.toSpecΓ_naturality]
  have h1 := congrArg Scheme.Hom.appTop he'
  simp only [Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop] at h1
  have key : CommRingCat.ofHom (algebraMap Γ(X, W)
      (AdjoinRoot (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, W)))) ≫
      (Scheme.ΓSpecIso _).inv ≫ e.hom.appTop = q.app W ≫ (q ⁻¹ᵁ W).topIso.inv := by
    have n1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap Γ(X, W)
      (AdjoinRoot (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, W)))))
    have n2 := Scheme.ΓSpecIso_inv_naturality (q.app W)
    rw [reassoc_of% n1, h1]
    erw [← reassoc_of% n2, Iso.inv_hom_id_assoc]
  have k2 := congrArg (fun g => g.hom r) key
  simp only [CommRingCat.comp_apply] at k2
  have k3 : ((Scheme.ΓSpecIso (.of (AdjoinRoot (Polynomial.X ^ m - Polynomial.C a :
      Polynomial Γ(X, W))))).inv ≫ e.hom.appTop) ≫ e.inv.appTop ≫
      (Scheme.ΓSpecIso _).hom = 𝟙 _ := by
    simp only [Category.assoc]
    rw [← Scheme.Hom.comp_appTop_assoc, Iso.inv_hom_id, Scheme.Hom.id_appTop, Category.id_comp,
      Iso.inv_hom_id]
  change (Scheme.ΓSpecIso _).hom (e.inv.appTop ((q ⁻¹ᵁ W).topIso.inv ((q.app W) r))) = _
  rw [← k2, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, k3]
  rfl

/-- **Maximal points of a cyclic cover lie over the generic point.** -/
private theorem map_eq_genericPoint_of_maximal {X : Scheme.{0}} [IsIntegral X] {m : ℕ}
    (hm : 0 < m) {f : X.functionField} (hf : f ≠ 0) {F : Scheme.{0}} (q : F ⟶ X)
    (hq : IsLocallyCyclicCover q m f) {w : F} (hw : ∀ y, y ⤳ w → y = w) :
    q w = genericPoint X := by
  obtain ⟨W, hW, hWa, hne, a, ψ, hψ, ha, e, he⟩ := hq (q w)
  have ha0 : a ≠ 0 := ne_zero_of_germToFunctionField_eq (hU := hne) hψ hf ha
  have hW' : w ∈ q ⁻¹ᵁ W := hW
  have hmin := mem_minimalPrimes_of_maximal (q ⁻¹ᵁ W) e (w := w) hW' hw
  have hcomap := comap_eq_bot_of_mem_minimalPrimes_adjoinRoot hm.ne' a hmin
  let w' : ((q ⁻¹ᵁ W : F.Opens) : Scheme.{0}) := ⟨w, hW'⟩
  have h1 := congrArg (fun g => g w') he
  simp only at h1
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h1
  have h2 : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W)
      (AdjoinRoot (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, W)))))
      (e.hom w') = genericPoint (Spec Γ(X, W)) := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hcomap
  rw [h2] at h1
  have h3 : (q ∣_ W) w' = genericPoint W := by
    have := congrArg hWa.isoSpec.inv h1.symm
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id] at this
    rw [show (q ∣_ W) w' = (𝟙 _ : (W : Scheme) ⟶ _) ((q ∣_ W) w') from rfl, this,
      genericPoint_eq_of_isOpenImmersion hWa.isoSpec.inv]
  have h4 := congrArg W.ι h3
  rw [genericPoint_eq_of_isOpenImmersion W.ι] at h4
  rw [← h4]
  exact (morphismRestrict_base_coe q W w').symm

/-- **A cyclic cover of a smooth surface is a reduced surface.** -/
private theorem isReduced_and_dim_eq_of_isLocallyCyclicCover
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hn : topologicalKrullDim X = 2) {B : QDivisor X}
    (hXB : IsSNCSubboundaryPair sX B) {m : ℕ} (hm : 0 < m) {f : X.functionField} (hf : f ≠ 0)
    {F : Scheme.{0}} (q : F ⟶ X) (hq : IsLocallyCyclicCover q m f)
    [LocallyOfFiniteType (q ≫ sX)] :
    IsReduced F ∧ ∀ C ∈ irreducibleComponents (F : Scheme.{0}), topologicalKrullDim C = 2 := by
  classical
  have : LocallyOfFiniteType sX := hXB.isProjectiveVariety.1.toLocallyOfFiniteType
  choose U hxU hU using hq
  have hchart : ∀ x : X, ∃ (hUa : IsAffineOpen (U x)) (_ : Nonempty (U x)) (a : Γ(X, U x)),
      a ≠ 0 ∧ ∃ e : (q ⁻¹ᵁ U x).toScheme ≅
          Spec (.of (AdjoinRoot (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, U x)))),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U x)
          (AdjoinRoot (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, U x))))) =
          q ∣_ U x ≫ hUa.isoSpec.hom := fun x => by
    obtain ⟨hUa, hne, a, ψ, hψ, ha, e, he⟩ := hU x
    exact ⟨hUa, hne, a, ne_zero_of_germToFunctionField_eq (hU := hne) hψ hf ha, e, he⟩
  have hredS : ∀ x : X, ∀ (_ : Nonempty (U x)) (a : Γ(X, U x)), a ≠ 0 →
      IsReduced (AdjoinRoot (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, U x))) := by
    intro x _ a ha
    let := functionFieldAlgebra sX
    have : CharZero X.functionField :=
      charZero_of_injective_algebraMap (algebraMap ℂ X.functionField).injective
    exact isReduced_adjoinRoot_X_pow_sub_C (K := X.functionField)
      (X.germToFunctionField_injective (U x)) hm.ne' ha
  refine ⟨?_, fun C hC => ?_⟩
  · have : ∀ y : F, _root_.IsReduced (F.presheaf.stalk y) := fun y => by
      obtain ⟨hUa, hne, a, ha0, e, he⟩ := hchart (q y)
      have := hredS (q y) hne a ha0
      have : IsReduced (q ⁻¹ᵁ U (q y)).toScheme := isReduced_of_isOpenImmersion e.hom
      have := isReduced_stalk_of_isReduced (q ⁻¹ᵁ U (q y)).toScheme ⟨y, hxU (q y)⟩
      exact isReduced_of_injective ((q ⁻¹ᵁ U (q y)).stalkIso ⟨y, hxU (q y)⟩).inv.hom
        ((q ⁻¹ᵁ U (q y)).stalkIso ⟨y, hxU (q y)⟩).commRingCatIsoToRingEquiv.symm.injective
    exact isReduced_of_isReduced_stalk F
  · have hCirr : IsIrreducible C := hC.1
    have hCcl : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
    set η := hCirr.genericPoint with hηdef
    have hη : closure ({η} : Set F) = C := by
      rw [hCirr.isGenericPoint_genericPoint_closure, hCcl.closure_eq]
    -- `η` has no proper generizations
    have hmax : ∀ y : F, y ⤳ η → y = η := by
      intro y hy
      have h1 : C ⊆ closure ({y} : Set F) := by
        rw [← hη]
        exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hy))
          isClosed_closure
      have h2 : closure ({y} : Set F) = C :=
        (hC.2 (isIrreducible_singleton.closure) h1).antisymm h1
      exact (Inseparable.eq (inseparable_iff_closure_eq.mpr (h2.trans hη.symm)))
    rw [← hη]
    obtain ⟨hUa, hne, a, ha0, e, he⟩ := hchart (q η)
    set V := q ⁻¹ᵁ U (q η) with hVdef
    let η' : (V : Scheme.{0}) := ⟨η, hxU (q η)⟩
    have h1 := topologicalKrullDim_closure_singleton_eq_of_isOpenImmersion V.ι (q ≫ sX) η'
    have hιη : V.ι η' = η := rfl
    have h2 := topologicalKrullDim_closure_singleton_eq_of_isOpenImmersion e.inv
      (V.ι ≫ q ≫ sX) (e.hom η')
    have hee : e.inv (e.hom η') = η' := by
      change (e.hom ≫ e.inv) η' = η'
      rw [Iso.hom_inv_id]; rfl
    rw [hee] at h2
    rw [hιη] at h1
    rw [← h1, ← h2]
    set P : PrimeSpectrum (AdjoinRoot (Polynomial.X ^ m - Polynomial.C a :
      Polynomial Γ(X, U (q η)))) := e.hom η' with hPdef
    change topologicalKrullDim (closure ({P} : Set (PrimeSpectrum _))) = 2
    rw [PrimeSpectrum.closure_singleton, topologicalKrullDim_zeroLocus]
    -- `P` is a minimal prime
    have hmin := mem_minimalPrimes_of_maximal V e (hxU (q η)) hmax
    have := hne
    have hcomap := comap_eq_bot_of_mem_minimalPrimes_adjoinRoot hm.ne' a hmin
    have hmon : (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, U (q η))).Monic :=
      Polynomial.monic_X_pow_sub_C a hm.ne'
    have : Module.Finite Γ(X, U (q η))
        (AdjoinRoot (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, U (q η)))) :=
      (AdjoinRoot.powerBasis' hmon).finite
    have : Algebra.IsIntegral Γ(X, U (q η))
        (AdjoinRoot (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, U (q η)))) :=
      Algebra.IsIntegral.of_finite _ _
    have : FaithfulSMul Γ(X, U (q η))
        (AdjoinRoot (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, U (q η))) ⧸
          P.asIdeal) := by
      refine (faithfulSMul_iff_algebraMap_injective _ _).mpr ?_
      rw [injective_iff_map_eq_zero]
      intro r hr
      rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem] at hr
      have : r ∈ P.asIdeal.comap (algebraMap Γ(X, U (q η)) _) := hr
      rwa [hcomap] at this
    rw [← Algebra.IsIntegral.ringKrullDim_eq Γ(X, U (q η)),
      ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    change topologicalKrullDim (Spec Γ(X, U (q η))) = 2
    rw [← IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso hUa.isoSpec).isHomeomorph,
      ← topologicalKrullDim_closure_genericPoint,
      topologicalKrullDim_closure_singleton_eq_of_isOpenImmersion (U (q η)).ι sX,
      genericPoint_eq_of_isOpenImmersion, topologicalKrullDim_closure_genericPoint, hn]

/-- **The generic algebra of a locally cyclic cover.** Let `q : F ⟶ X` be locally the cyclic
cover `z^m = f`, and let `πᵢ : Yᵢ ⟶ F` be integral schemes whose generic points go to pairwise
distinct points of `F` without proper generizations, exhausting them, with `πᵢ` an isomorphism of
stalks there. Then `k(X)[z]/(z^m - f) ≅ ∏ᵢ k(Yᵢ)`. -/
private theorem exists_root_of_isLocallyCyclicCover
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (sX : X ⟶ Spec (.of ℂ))
    {m : ℕ} (hm : 0 < m) {f : X.functionField} (hf : f ≠ 0)
    {F : Scheme.{0}} (q : F ⟶ X) (hq : IsLocallyCyclicCover q m f)
    {k : ℕ} (Yc : Fin k → Scheme.{0}) [∀ i, IsIntegral (Yc i)] (π : ∀ i, Yc i ⟶ F)
    [∀ i, IsDominant (π i ≫ q)]
    (hiso : ∀ i, IsIso ((π i).stalkMap (genericPoint (Yc i))))
    (hmax : ∀ i y, y ⤳ π i (genericPoint (Yc i)) → y = π i (genericPoint (Yc i)))
    (hinj : Function.Injective fun i => π i (genericPoint (Yc i)))
    (hsurj : ∀ w : F, (∀ y, y ⤳ w → y = w) → ∃ i, π i (genericPoint (Yc i)) = w) :
    letI := fun i => functionFieldMapAlgebra (π i ≫ q)
    ∃ z : ∀ i, (Yc i).functionField,
      (∀ i, z i ^ m = algebraMap X.functionField (Yc i).functionField f) ∧
      Algebra.adjoin X.functionField {z} = ⊤ ∧
      Module.finrank X.functionField (∀ i, (Yc i).functionField) = m := by
  classical
  have hξ : ∀ i, q (π i (genericPoint (Yc i))) = genericPoint X := fun i =>
    map_eq_genericPoint_of_maximal hm hf q hq (hmax i)
  obtain ⟨W, hξW, hW⟩ := hq (genericPoint X)
  obtain ⟨hWa, hne, a, ψ, hψ, ha, hVa, eS, heS⟩ := exists_ringEquiv_of_isCyclicCoverChart hW
  have ha0 : a ≠ 0 := ne_zero_of_germToFunctionField_eq (hU := hne) hψ hf ha
  have hwV : ∀ i, π i (genericPoint (Yc i)) ∈ q ⁻¹ᵁ W := fun i => by
    change q _ ∈ W
    rw [hξ i]
    exact hξW
  let : Algebra Γ(X, W) Γ(F, q ⁻¹ᵁ W) := (q.app W).hom.toAlgebra
  let eA : Γ(F, q ⁻¹ᵁ W) ≃ₐ[Γ(X, W)]
      AdjoinRoot (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, W)) :=
    AlgEquiv.ofRingEquiv (f := eS) heS
  let := fun i => functionFieldMapAlgebra (π i ≫ q)
  let algS : ∀ i, Algebra Γ(F, q ⁻¹ᵁ W) (Yc i).functionField := fun i =>
    (F.presheaf.germ (q ⁻¹ᵁ W) _ (hwV i) ≫ (π i).stalkMap (genericPoint (Yc i))).hom.toAlgebra
  have : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hWa
  let := functionFieldAlgebra sX
  have : CharZero X.functionField :=
    charZero_of_injective_algebraMap (algebraMap ℂ X.functionField).injective
  have hcompat : ∀ i r, algebraMap Γ(F, q ⁻¹ᵁ W) (Yc i).functionField
      (algebraMap Γ(X, W) Γ(F, q ⁻¹ᵁ W) r) =
      algebraMap X.functionField (Yc i).functionField (algebraMap Γ(X, W) X.functionField r) := by
    intro i r
    have e1 := (π i).germ_stalkMap (q ⁻¹ᵁ W) (genericPoint (Yc i)) (hwV i)
    have e2 : ∀ h : (π i ≫ q) (genericPoint (Yc i)) ⤳ genericPoint X,
        X.presheaf.germ W (genericPoint X) hξW ≫ X.presheaf.stalkSpecializes h ≫
          (π i ≫ q).stalkMap (genericPoint (Yc i)) =
        (π i ≫ q).app W ≫ (Yc i).presheaf.germ _ _ (hwV i) := fun h => by
      rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes, Scheme.Hom.germ_stalkMap]
    have e3 : q.app W ≫ F.presheaf.germ (q ⁻¹ᵁ W) _ (hwV i) ≫
        (π i).stalkMap (genericPoint (Yc i)) =
        (π i ≫ q).app W ≫ (Yc i).presheaf.germ _ _ (hwV i) := by
      rw [e1, Scheme.Hom.comp_app]
      rfl
    have hsp : (π i ≫ q) (genericPoint (Yc i)) ⤳ genericPoint X :=
      (Inseparable.of_eq (by rw [Scheme.Hom.comp_apply, hξ i])).specializes
    have e4 := congrArg (fun g => g.hom r) (e3.trans (e2 hsp).symm)
    simp only [CommRingCat.comp_apply] at e4
    exact e4
  have hloc : ∀ i, IsLocalization.AtPrime (Yc i).functionField
      (hVa.primeIdealOf ⟨_, hwV i⟩).asIdeal := by
    intro i
    have := hiso i
    let : Algebra Γ(F, q ⁻¹ᵁ W) (F.presheaf.stalk (π i (genericPoint (Yc i)))) :=
      TopCat.Presheaf.algebra_section_stalk F.presheaf ⟨_, hwV i⟩
    have h0 := hVa.isLocalization_stalk ⟨_, hwV i⟩
    let eL : F.presheaf.stalk (π i (genericPoint (Yc i))) ≃ₐ[Γ(F, q ⁻¹ᵁ W)]
        (Yc i).functionField :=
      AlgEquiv.ofRingEquiv
        (f := (asIso ((π i).stalkMap (genericPoint (Yc i)))).commRingCatIsoToRingEquiv)
        (fun x => rfl)
    exact IsLocalization.isLocalization_of_algEquiv _ eL
  have hinjP : Function.Injective fun i => (hVa.primeIdealOf ⟨_, hwV i⟩).asIdeal := by
    intro i i' h
    apply hinj
    have h' : hVa.primeIdealOf ⟨_, hwV i⟩ = hVa.primeIdealOf ⟨_, hwV i'⟩ := PrimeSpectrum.ext h
    have := congrArg hVa.fromSpec h'
    rwa [hVa.fromSpec_primeIdealOf, hVa.fromSpec_primeIdealOf] at this
  have hsurjP : ∀ Q ∈ minimalPrimes Γ(F, q ⁻¹ᵁ W),
      ∃ i, (hVa.primeIdealOf ⟨_, hwV i⟩).asIdeal = Q := by
    intro Q hQ
    let y : PrimeSpectrum Γ(F, q ⁻¹ᵁ W) := ⟨Q, hQ.1.1⟩
    have hyV : hVa.fromSpec y ∈ (q ⁻¹ᵁ W : Set F) := by
      rw [← hVa.range_fromSpec]
      exact ⟨y, rfl⟩
    have hmaxw : ∀ z, z ⤳ hVa.fromSpec y → z = hVa.fromSpec y := by
      intro z hz
      have hzV : z ∈ Set.range hVa.fromSpec := by
        rw [hVa.range_fromSpec]
        exact hz.mem_open (q ⁻¹ᵁ W).isOpen hyV
      obtain ⟨y', rfl⟩ := hzV
      have h1 : y' ⤳ y := (hVa.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp hz
      have h2 : y'.asIdeal ≤ Q := (PrimeSpectrum.le_iff_specializes y' y).mpr h1
      have h3 : y'.asIdeal = Q := le_antisymm h2 (hQ.2 ⟨y'.isPrime, bot_le⟩ h2)
      rw [show y' = y from PrimeSpectrum.ext h3]
    obtain ⟨i, hi⟩ := hsurj _ hmaxw
    refine ⟨i, ?_⟩
    have : hVa.primeIdealOf ⟨_, hwV i⟩ = y := by
      apply hVa.fromSpec.isOpenEmbedding.injective
      rw [hVa.fromSpec_primeIdealOf]
      exact hi
    rw [this]
  obtain ⟨hadj, hrank⟩ := adjoin_eq_top_and_finrank_eq_of_adjoinRoot (K := X.functionField)
    hm.ne' ha0 eA (fun i => (Yc i).functionField) hcompat _ hloc hinjP hsurjP
  have hroot : (AdjoinRoot.root (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, W))) ^ m =
      algebraMap Γ(X, W) _ a := by
    have h := AdjoinRoot.eval₂_root (Polynomial.X ^ m - Polynomial.C a : Polynomial Γ(X, W))
    rwa [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero] at h
  set z' : ∀ i, (Yc i).functionField := fun i => algebraMap Γ(F, q ⁻¹ᵁ W) (Yc i).functionField
    (eA.symm (AdjoinRoot.root _)) with hz'def
  have hz' : ∀ i, z' i ^ m = algebraMap X.functionField (Yc i).functionField
      (ψ ^ m * f) := fun i => by
    rw [← ha, hz'def, ← map_pow, ← map_pow, hroot, AlgEquiv.commutes]
    exact hcompat i a
  set μ := ψ⁻¹
  refine ⟨μ • z', fun i => ?_, ?_, hrank⟩
  · rw [Pi.smul_apply, Algebra.smul_def, mul_pow, hz' i, ← map_pow, ← map_mul, ← mul_assoc,
      ← mul_pow, inv_mul_cancel₀ hψ, one_pow, one_mul]
  · rw [eq_top_iff, ← hadj, Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    convert Subalgebra.smul_mem (Algebra.adjoin X.functionField {μ • z'})
      (Algebra.subset_adjoin (Set.mem_singleton _)) μ⁻¹ using 1
    rw [smul_smul, inv_mul_cancel₀ (inv_ne_zero hψ), one_smul]

/-- A member of a cover of a space by pairwise disjoint open sets is closed. -/
theorem isClosed_of_isOpen_of_disjoint_of_cover {Z ι : Type*} [TopologicalSpace Z]
    {s : ι → Set Z} (hs : ∀ i, IsOpen (s i)) (hdisj : ∀ i i', i ≠ i' → Disjoint (s i) (s i'))
    (hcov : ∀ z, ∃ i, z ∈ s i) (i : ι) : IsClosed (s i) := by
  have : (s i)ᶜ = ⋃ (i' : ι) (_ : i' ≠ i), s i' := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_iUnion, exists_prop]
    constructor
    · intro hz
      obtain ⟨i', hi'⟩ := hcov z
      exact ⟨i', fun h => hz (h ▸ hi'), hi'⟩
    · rintro ⟨i', hi', hz⟩ hz'
      exact Set.disjoint_left.mp (hdisj i i' (Ne.symm hi')) hz' hz
  rw [← isOpen_compl_iff, this]
  exact isOpen_iUnion fun i' => isOpen_iUnion fun _ => hs i'

/-- A finite-dimensional product of `K`-algebras has dimension at least the number of factors. -/
theorem card_le_finrank_pi {K ι : Type*} [Field K] [Fintype ι]
    (L : ι → Type*) [∀ i, Ring (L i)] [∀ i, Nontrivial (L i)] [∀ i, Algebra K (L i)]
    [Module.Finite K (∀ i, L i)] :
    Fintype.card ι ≤ Module.finrank K (∀ i, L i) := by
  classical
  have hli : LinearIndependent K (fun i => (Pi.single i 1 : ∀ i, L i)) := by
    refine linearIndependent_iff'.mpr fun s c hs i hi => ?_
    have := congrFun hs i
    rw [Finset.sum_apply, Finset.sum_eq_single i (fun b _ hb => by
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero])
      (fun h => absurd hi h)] at this
    rwa [Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply, smul_eq_zero,
      or_iff_left one_ne_zero] at this
  exact hli.fintype_card_le_finrank

/-- The second Betti cohomology `H²(Y^an; ℚ)` of a projective `ℂ`-scheme is finite-dimensional. -/
private theorem finite_relativeSingularCohomology_two {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    (hproj : IsProjectiveMorphism sY) :
    Module.Finite ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace sY) ∅ 2) := by
  obtain ⟨-, hZ, hbc⟩ :=
    MMP.Analytic.exists_homotopyEquiv_singularChainComplex_of_isProjectiveMorphism _ hproj
  have := hZ 2
  have h1 : Module.Finite ℚ (MMP.Analytic.singularCohomology ℚ (analyticSpace sY) 2) :=
    Module.Finite.equiv (hbc 2).equiv
  rwa [← Set.compl_univ]

/-- The image of the generic point under an open immersion of an integral scheme is maximal for
specialization. -/
private theorem eq_of_specializes_genericPoint {Y Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ Y)
    [IsOpenImmersion j] {y : Y} (hy : y ⤳ j (genericPoint Z)) : y = j (genericPoint Z) := by
  obtain ⟨y', rfl⟩ : y ∈ Set.range j := hy.mem_open j.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
  have h1 : y' ⤳ genericPoint Z := j.isOpenEmbedding.isInducing.specializes_iff.mp hy
  have h2 : genericPoint Z ⤳ y' := (genericPoint_spec Z).specializes (Set.mem_univ _)
  exact congrArg _ (h1.antisymm h2).eq

/-- **A resolution of a cyclic cover is a resolved cyclic cover.** If `q : F ⟶ X` is locally the
cyclic cover `z^m = f` and `p : Y ⟶ F` is a smooth projective surface over `ℂ`, an isomorphism
over a dense open whose preimage is dense, then `f` has a resolved cyclic cover with
`b₂ ≤ m · b₂(Y)`. -/
private theorem hasResolvedCyclicCover_of_resolution
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {m : ℕ} (hm : 0 < m) {f : X.functionField} (hf : f ≠ 0)
    {F : Scheme.{0}} (q : F ⟶ X) (hq : IsLocallyCyclicCover q m f)
    [LocallyOfFiniteType (q ≫ sX)] [CompactSpace F]
    {Y : Scheme.{0}} (p : Y ⟶ F) (hproj : IsProjectiveMorphism (p ≫ q ≫ sX))
    (hsm : SmoothOfRelativeDimension 2 (p ≫ q ≫ sX))
    (hU : ∃ U : F.Opens, Dense (U : Set F) ∧ Dense ((p ⁻¹ᵁ U : Y.Opens) : Set Y) ∧
      IsIso (p ∣_ U)) :
    HasResolvedCyclicCover sX m (m * Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ)
      (analyticSpace (p ≫ q ≫ sX)) ∅ 2)) f := by
  classical
  obtain ⟨U, hUd, hpUd, hpU⟩ := hU
  have : IsLocallyNoetherian F := LocallyOfFiniteType.isLocallyNoetherian (q ≫ sX)
  have : IsNoetherian F := ⟨⟩
  have : IsProper (p ≫ q ≫ sX) := isProper_of_isProjectiveMorphism _ hproj
  have : Smooth (p ≫ q ≫ sX) := hsm.smooth
  have : IsNormal Y := isNormal_of_smooth_over_field (p ≫ q ≫ sX)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (p ≫ q ≫ sX)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (p ≫ q ≫ sX)
  have : IsNoetherian Y := ⟨⟩
  obtain ⟨k, Yc, hNo, hInt, j, hj, hdisj, hcov⟩ := exists_fin_components Y
  have hmaxY : ∀ i y, y ⤳ j i (genericPoint (Yc i)) → y = j i (genericPoint (Yc i)) :=
    fun i _ => eq_of_specializes_genericPoint (j i)
  have hmaxY' : ∀ y : Y, (∀ y', y' ⤳ y → y' = y) → ∃ i, j i (genericPoint (Yc i)) = y := by
    intro y hy
    obtain ⟨i, y', rfl⟩ := hcov y
    exact ⟨i, hy _ (((genericPoint_spec (Yc i)).specializes (Set.mem_univ y')).map
      (j i).continuous)⟩
  have hyU : ∀ i, j i (genericPoint (Yc i)) ∈ (p ⁻¹ᵁ U : Set Y) := fun i =>
    mem_of_isOpen_of_dense_of_maximal (p ⁻¹ᵁ U).isOpen hpUd (hmaxY i)
  let e : (p ⁻¹ᵁ U : Set Y) ≃ₜ (U : Set F) := Scheme.homeoOfIso (asIso (p ∣_ U))
  have he : ∀ a, (e a : F) = p a := fun a => morphismRestrict_base_coe p U a
  let π : ∀ i, Yc i ⟶ F := fun i => j i ≫ p
  have hπ : ∀ i, π i (genericPoint (Yc i)) = p (j i (genericPoint (Yc i))) := fun i =>
    Scheme.Hom.comp_apply _ _ _
  have hmaxF : ∀ i w, w ⤳ π i (genericPoint (Yc i)) → w = π i (genericPoint (Yc i)) := by
    intro i
    rw [hπ i]
    exact (forall_specializes_eq_iff_of_homeomorph p (p ⁻¹ᵁ U).isOpen U.isOpen e he
      ⟨_, hyU i⟩).mp (hmaxY i)
  have hinj : Function.Injective fun i => π i (genericPoint (Yc i)) := by
    intro i i' h
    simp only [hπ] at h
    have h1 : e ⟨_, hyU i⟩ = e ⟨_, hyU i'⟩ := Subtype.ext (by rw [he, he]; exact h)
    have h2 := congrArg Subtype.val (e.injective h1)
    by_contra hii
    exact Set.disjoint_left.mp (hdisj i i' hii) ⟨_, rfl⟩ ⟨_, h2.symm⟩
  have hsurj : ∀ w : F, (∀ y, y ⤳ w → y = w) → ∃ i, π i (genericPoint (Yc i)) = w := by
    intro w hw
    have hwU : w ∈ (U : Set F) := mem_of_isOpen_of_dense_of_maximal U.isOpen hUd hw
    have hpa : p (e.symm ⟨w, hwU⟩) = w := by rw [← he, e.apply_symm_apply]
    have hamax := (forall_specializes_eq_iff_of_homeomorph p (p ⁻¹ᵁ U).isOpen U.isOpen e he
      (e.symm ⟨w, hwU⟩)).mpr (by rwa [hpa])
    obtain ⟨i, hi⟩ := hmaxY' _ hamax
    exact ⟨i, by rw [hπ, hi, hpa]⟩
  have hpstalk : ∀ y : (p ⁻¹ᵁ U : Y.Opens), IsIso (p.stalkMap y.1) := fun y =>
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (morphismRestrictStalkMap p U y)).mp (((isIso_iff_isIso_stalkMap (p ∣_ U)).mp hpU).2 y)
  have hiso : ∀ i, IsIso ((π i).stalkMap (genericPoint (Yc i))) := fun i => by
    rw [Scheme.Hom.stalkMap_comp]
    have h1 : IsIso (p.stalkMap (j i (genericPoint (Yc i)))) := hpstalk ⟨_, hyU i⟩
    have h2 := (IsOpenImmersion.iff_isIso_stalkMap.mp (hj i)).2 (genericPoint (Yc i))
    exact IsIso.comp_isIso' h1 h2
  have hξ : ∀ i, (π i ≫ q) (genericPoint (Yc i)) = genericPoint X := fun i =>
    (Scheme.Hom.comp_apply _ _ _).trans (map_eq_genericPoint_of_maximal hm hf q hq (hmaxF i))
  have hdom : ∀ i, IsDominant (π i ≫ q) := fun i =>
    ⟨Dense.mono (Set.singleton_subset_iff.mpr ⟨_, hξ i⟩)
      (dense_iff_closure_eq.mpr (genericPoint_spec X))⟩
  obtain ⟨z, hz, hadj, hrank⟩ := exists_root_of_isLocallyCyclicCover sX hm hf q hq Yc π hiso
    hmaxF hinj hsurj
  have hrange : ∀ i, IsClosed (Set.range (j i)) :=
    isClosed_of_isOpen_of_disjoint_of_cover (fun i => (j i).isOpenEmbedding.isOpen_range)
      hdisj hcov
  have hcomp : ∀ i, ((j i ≫ p) ≫ q) ≫ sX = j i ≫ p ≫ q ≫ sX := fun i => by
    simp only [Category.assoc]
  have hfin := finite_relativeSingularCohomology_two hproj
  have hb : ∀ i, Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ)
      (analyticSpace (((j i ≫ p) ≫ q) ≫ sX)) ∅ 2) ≤ Module.finrank ℚ
      (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace (p ≫ q ≫ sX)) ∅ 2) := fun i => by
    rw [hcomp i]
    have : CompactSpace (Yc i) :=
      (Topology.IsClosedEmbedding.mk (j i).isOpenEmbedding.isEmbedding (hrange i)).compactSpace
    exact finrank_le_of_isOpenImmersion_of_isClosed (j i) (hrange i) (p ≫ q ≫ sX) hfin
  have hk : k ≤ m := by
    let := fun i => functionFieldMapAlgebra ((j i ≫ p) ≫ q)
    have : Module.Finite X.functionField (∀ i, (Yc i).functionField) :=
      Module.finite_of_finrank_pos (by rwa [hrank])
    simpa [hrank] using card_le_finrank_pi (K := X.functionField) fun i => (Yc i).functionField
  refine ⟨k, Yc, hInt, fun i => isLocallyNoetherian_of_isOpenImmersion (j i), hNo,
    fun i => (j i ≫ p) ≫ q, hdom, fun i => ?_, fun i => ?_, ?_, z, hz, hadj, hrank⟩
  · rw [hcomp i]
    have : IsClosedImmersion (j i) := IsClosedImmersion.of_isPreimmersion (j i) (hrange i)
    exact (MMP.isProjectiveMorphism_of_isClosedImmersion (j i)).comp hproj
  · rw [hcomp i]
    have := hj i
    exact (inferInstance : SmoothOfRelativeDimension (0 + 2) (j i ≫ p ≫ q ≫ sX))
  · calc _ ≤ ∑ _i : Fin k, Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ)
          (analyticSpace (p ≫ q ≫ sX)) ∅ 2) := Finset.sum_le_sum fun i _ => hb i
      _ = k * _ := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hk

/-! ### The universal cyclic cover over an affine family -/

open Opposite

/-- **Adjoining a root commutes with base change**: for `e : R' → R` and `q = e(p)`, the square
`R' → R'[z]/(p)`, `R' → R`, `R → R[z]/(q)` is a pushout of rings. -/
private theorem isPushout_adjoinRoot {R' R : CommRingCat.{0}} (e : R' ⟶ R) (p : Polynomial R')
    (q : Polynomial R) (h : p.map e.hom = q) :
    IsPushout (CommRingCat.ofHom (AdjoinRoot.of p)) e
      (CommRingCat.ofHom (AdjoinRoot.map e.hom p q h.symm.dvd))
      (CommRingCat.ofHom (AdjoinRoot.of q)) := by
  subst h
  have hw : CommRingCat.ofHom (AdjoinRoot.of p) ≫
      CommRingCat.ofHom (AdjoinRoot.map e.hom p (p.map e.hom) dvd_rfl) =
      e ≫ CommRingCat.ofHom (AdjoinRoot.of (p.map e.hom)) := by
    ext x
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
      AdjoinRoot.map_of]
  refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _ hw) ?_
  refine PushoutCocone.IsColimit.mk _ (fun s => CommRingCat.ofHom (AdjoinRoot.lift s.inr.hom
      (s.inl.hom (AdjoinRoot.root p)) ?_)) ?_ ?_ ?_
  · have hc := congrArg CommRingCat.Hom.hom s.condition
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at hc
    rw [Polynomial.eval₂_map, ← hc, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]
  · intro s
    have hc := congrArg CommRingCat.Hom.hom s.condition
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at hc
    apply CommRingCat.hom_ext
    apply AdjoinRoot.ringHom_ext
    · ext x
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
        Function.comp_apply, AdjoinRoot.map_of, AdjoinRoot.lift_of]
      exact (RingHom.congr_fun hc x).symm
    · simp [AdjoinRoot.map_root]
  · intro s
    apply CommRingCat.hom_ext
    ext x
    simp
  · intro s u hu1 hu2
    apply CommRingCat.hom_ext
    apply AdjoinRoot.ringHom_ext
    · ext x
      have := RingHom.congr_fun (congrArg CommRingCat.Hom.hom hu2) x
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
        Function.comp_apply] at this ⊢
      rw [this, AdjoinRoot.lift_of]
    · have := RingHom.congr_fun (congrArg CommRingCat.Hom.hom hu1) (AdjoinRoot.root p)
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
        Function.comp_apply, AdjoinRoot.map_root] at this
      simp only [CommRingCat.hom_ofHom, AdjoinRoot.lift_root]
      exact this

/-- **Charts of a fibre.** If `F = 𝒵 ×_S X` along `σ : X ⟶ S`, and over an affine open `W'` of
`S` the scheme `𝒵` is `Spec Γ(S, W')[z]/(z^m - v)`, then over an affine open `W ⊆ σ⁻¹(W')` the
fibre `F` is `Spec Γ(X, W)[z]/(z^m - σ^* v)`. -/
private theorem exists_isPullback_adjoinRoot_of_isPullback {𝒵 S X F : Scheme.{0}}
    {toBase : 𝒵 ⟶ S}
    {σ : X ⟶ S} {fst : F ⟶ 𝒵} {q : F ⟶ X} (hF : IsPullback fst q toBase σ)
    {W : X.Opens} (hW : IsAffineOpen W) {W' : S.Opens} (hW' : IsAffineOpen W')
    (hle : W ≤ σ ⁻¹ᵁ W') {A' : CommRingCat.{0}} {str : Γ(S, W') ⟶ A'} {ch : Spec A' ⟶ 𝒵}
    (hch : IsPullback ch (Spec.map str) toBase hW'.fromSpec) (m : ℕ) (v : Γ(S, W'))
    (eA : A' ≅ CommRingCat.of (AdjoinRoot (Polynomial.X ^ m - Polynomial.C v)))
    (heA : str ≫ eA.hom = CommRingCat.ofHom (AdjoinRoot.of _)) :
    ∃ j : Spec (.of (AdjoinRoot (Polynomial.X ^ m -
        Polynomial.C ((σ.appLE W' W hle).hom v)))) ⟶ F,
      IsPullback j (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W)
        (AdjoinRoot (Polynomial.X ^ m - Polynomial.C ((σ.appLE W' W hle).hom v)))))) q
        hW.fromSpec := by
  set e := σ.appLE W' W hle
  have hpq : (Polynomial.X ^ m - Polynomial.C v).map e.hom =
      Polynomial.X ^ m - Polynomial.C (e.hom v) := by simp
  have h1 := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_adjoinRoot e _ _ hpq)
  have h2 : IsPullback (Spec.map eA.hom ≫ ch) (Spec.map (CommRingCat.ofHom (AdjoinRoot.of _)))
      toBase hW'.fromSpec :=
    hch.of_iso (Scheme.Spec.mapIso eA.op).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [← Spec.map_comp_assoc]) (by simp [← heA, ← Spec.map_comp_assoc]) (by simp) (by simp)
  have h3 := h1.paste_horiz h2
  rw [IsAffineOpen.SpecMap_appLE_fromSpec σ hW' hW hle] at h3
  let j := hF.lift (Spec.map (CommRingCat.ofHom (AdjoinRoot.map e.hom _ _ hpq.symm.dvd)) ≫
    Spec.map eA.hom ≫ ch) (Spec.map (CommRingCat.ofHom (AdjoinRoot.of _)) ≫ hW.fromSpec)
    (by simpa only [Category.assoc] using h3.w)
  refine ⟨j, ?_⟩
  refine IsPullback.of_right ?_ (hF.lift_snd _ _ _) hF
  rw [hF.lift_fst]
  exact h3

/-- On an integral scheme, a germ at the generic point read as a rational function has, on every
component meeting the open, the germ at the component's generic point as its value. -/
public theorem rationalFunctionsEquivFunctionField_symm_germ {X : Scheme.{0}} [IsIntegral X]
    (U : X.Opens) (s : Γ(X, U))
    (h : genericPoint X ∈ U) (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ U) :
    (rationalFunctionsEquivFunctionField X).symm (X.presheaf.germ U (genericPoint X) h s) Z =
      X.presheaf.germ U (componentGenericPoint X Z) hZ s := by
  have : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have hd : Dense (U : Set X) := U.isOpen.dense ⟨_, h⟩
  let D : Stacks.Chow.DenseOpen X := ⟨U, hd⟩
  have key : (rationalFunctionsEquivFunctionField X).symm (X.presheaf.germ U (genericPoint X) h s)
      = (Stacks.Chow.rationalFunctionsEquivStalks X).1 (Stacks.Chow.ofSection X D s) := by
    rw [RingEquiv.symm_apply_eq, ← (Stacks.Chow.rationalFunctionsEquivFunctionField X).2 D s h]
    change _ = (Stacks.Chow.rationalFunctionsEquivFunctionField X).1
      ((Stacks.Chow.rationalFunctionsEquivStalks X).1.symm _)
    rw [RingEquiv.symm_apply_apply]
  rw [key]
  exact (Stacks.Chow.rationalFunctionsEquivStalks X).2 D s Z hZ

/-- **A common pole divisor.** For finitely many rational functions `gᵢ` on a normal integral
scheme on which every divisor is Cartier, there is a divisor `D` with local equations `ψ` such
that every `ψ^m gᵢ` is regular, `m > 0`. -/
private theorem exists_divisor_localEquation {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (hcart : ∀ D : Divisor X, D.IsCartier) {ι : Type}
    [Finite ι] (g : ι → X.functionField) {m : ℕ} (hm : 0 < m) :
    ∃ D : Divisor X, D.IsCartier ∧ ∀ x : X, ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧
      ∃ ψ : (RationalFunctions X)ˣ, D.IsLocalEquation W ψ ∧
        ∀ i, ∃ b : Γ(X, W), ∀ h : genericPoint X ∈ W, X.presheaf.germ W (genericPoint X) h b =
          rationalFunctionsEquivFunctionField X ψ ^ m * g i := by
  classical
  have := Fintype.ofFinite ι
  set e := rationalFunctionsEquivFunctionField X
  let u : ι → (RationalFunctions X)ˣ := fun i =>
    if h : g i = 0 then 1 else ((Ne.isUnit h).map e.symm).unit
  have hu : ∀ i, g i ≠ 0 → e (u i : RationalFunctions X) = g i := fun i h => by
    simp only [u, h, ↓reduceDIte, IsUnit.unit_spec, RingEquiv.apply_symm_apply]
  let D : Divisor X := ∑ i, (-(principalDivisor (u i)) ⊔ 0)
  have hD : ∀ i (E : MMP.Mori.PrimeDivisor X), 0 ≤ D.coeff E ∧ -E.ord (u i) ≤ D.coeff E := by
    intro i E
    have hcoeff : D.coeff E = ∑ j, max (-E.ord (u j)) 0 := by
      change (∑ i, (-(principalDivisor (u i)) ⊔ 0) : MMP.Mori.PrimeDivisor X →₀ ℤ) E = _
      rw [Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finsupp.sup_apply, Finsupp.neg_apply, Finsupp.coe_zero, Pi.zero_apply]
      rfl
    rw [hcoeff]
    refine ⟨Finset.sum_nonneg fun j _ => le_max_right _ _, ?_⟩
    exact (le_max_left _ _).trans (Finset.single_le_sum (f := fun j => max (-E.ord (u j)) 0)
      (fun j _ => le_max_right _ _) (Finset.mem_univ i))
  refine ⟨D, hcart D, fun x => ?_⟩
  obtain ⟨U, hxU, ψ, hψ⟩ := hcart D x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.2
  have hψW : D.IsLocalEquation W ψ := hψ.mono hWU
  refine ⟨W, hW, hxW, ψ, hψW, fun i => ?_⟩
  by_cases hg : g i = 0
  · exact ⟨0, fun h => by rw [map_zero, hg, mul_zero]⟩
  set w : (RationalFunctions X)ˣ := ψ ^ m * u i
  have hsec : (0 : Divisor X).IsDivisorialSection W
      (fun Z => (w : RationalFunctions X) Z.1) := by
    intro E hE
    refine Or.inr ?_
    rw [PrimeDivisor.valuation_component, DivisorWithCoeffs.coeff_zero, neg_zero,
      WithZero.exp_le_exp, PrimeDivisor.ord_mul, PrimeDivisor.ord_pow, ← hψW E hE]
    obtain ⟨h0, h1⟩ := hD i E
    have : (D.coeff E : ℤ) ≤ m • D.coeff E := by
      rw [nsmul_eq_mul]
      nlinarith
    linarith
  obtain ⟨b, hb⟩ := hsec.exists_eq
  refine ⟨b, fun h => ?_⟩
  have h1 : e.symm (X.presheaf.germ W (genericPoint X) h b) = (w : RationalFunctions X) := by
    funext Z
    have hZ : componentGenericPoint X Z ∈ W := by
      rwa [componentGenericPoint_eq_genericPoint]
    rw [rationalFunctionsEquivFunctionField_symm_germ W b h Z hZ]
    exact congrFun hb ⟨Z, hZ⟩
  rw [← e.apply_symm_apply (X.presheaf.germ W (genericPoint X) h b), h1]
  simp only [w, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hu i hg]

/-- The pull-back of a local equation of a Cartier divisor is a local equation of its
pull-back. -/
private theorem isLocalEquation_pullback_pullbackRationalFunction {S X : Scheme.{0}}
    [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (π : S ⟶ X) {D : Divisor X} (hDc : D.IsCartier)
    (hB : ∀ Z, π (componentGenericPoint S Z) ∉ D.supp) {W : X.Opens}
    {ψ : (RationalFunctions X)ˣ} (hψ : D.IsLocalEquation W ψ)
    (hψ' : ∀ Z, π (componentGenericPoint S Z) ∉ (principalDivisor ψ).supp) :
    (D.pullback hDc hB).IsLocalEquation (π ⁻¹ᵁ W) (pullbackRationalFunction π ψ hψ') := by
  intro E hE
  rw [Divisor.isPullback_pullback hDc hB W ψ hψ E hE, PrimeDivisor.ord_eq_ordUnit]
  congr 1

/-- On an integral scheme a rational function is its value on any component, generized to the
generic point. -/
private theorem rationalFunctionsEquivFunctionField_eq_stalkSpecializes {X : Scheme.{0}}
    [IsIntegral X]
    (Z : irreducibleComponents X) (u : RationalFunctions X) :
    rationalFunctionsEquivFunctionField X u = (X.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes (Set.mem_univ (componentGenericPoint X Z)))).hom
        (u Z) := by
  set e := rationalFunctionsEquivFunctionField X
  obtain ⟨U, hx, s, hs⟩ := X.presheaf.exists_germ_eq (x := genericPoint X) (e u)
  have hZ : componentGenericPoint X Z ∈ U := (componentGenericPoint_eq_genericPoint Z) ▸ hx
  have h1 : u Z = X.presheaf.germ U (componentGenericPoint X Z) hZ s := by
    rw [← rationalFunctionsEquivFunctionField_symm_germ U s hx Z hZ, hs, RingEquiv.symm_apply_apply]
  rw [h1, TopCat.Presheaf.germ_stalkSpecializes_apply, hs]

/-- The pull-back of a rational function along a dominant morphism of integral schemes is its
image under the extension of function fields. -/
public theorem rationalFunctionsEquivFunctionField_pullbackRationalFunction {S X : Scheme.{0}}
    [IsIntegral S] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian S] [IsNormal S] (π : S ⟶ X) [IsDominant π] (ψ : (RationalFunctions X)ˣ)
    (hψ' : ∀ Z, π (componentGenericPoint S Z) ∉ (principalDivisor ψ).supp) :
    rationalFunctionsEquivFunctionField S (pullbackRationalFunction π ψ hψ') =
      functionFieldMap π (rationalFunctionsEquivFunctionField X ψ) := by
  set Z : irreducibleComponents S := pointComponent (genericPoint S)
  rw [rationalFunctionsEquivFunctionField_eq_stalkSpecializes Z]
  obtain ⟨a, ha⟩ := (Divisor.isLocalEquation_principalDivisor ψ ⊤).exists_unit_stalk trivial
    (hψ' Z) (mem_pointComponent _)
  have hval : (pullbackRationalFunction π ψ hψ' : RationalFunctions S) Z =
      π.stalkMap (componentGenericPoint S Z) a :=
    congrArg Units.val (pullbackComponent_eq hψ' (Divisor.isLocalEquation_principalDivisor ψ ⊤)
      (Z := Z) trivial (mem_pointComponent _) a ha)
  rw [hval, ← CommRingCat.comp_apply, ← Scheme.Hom.stalkSpecializes_stalkMap,
    CommRingCat.comp_apply]
  set ZX := pointComponent (π (componentGenericPoint S Z))
  rw [rationalFunctionsEquivFunctionField_eq_stalkSpecializes ZX, ← ha]
  simp only [functionFieldMap, TopCat.Presheaf.stalkCongr_hom, CommRingCat.comp_apply]
  congr 1
  simp only [stalkToRationalFunctions, ← CommRingCat.comp_apply,
    TopCat.Presheaf.stalkSpecializes_comp]
  erw [TopCat.Presheaf.stalkSpecializes_comp]

/-- The extension of function fields of a dominant morphism is compatible with sections. -/
public theorem functionFieldMap_germ {S X : Scheme.{0}} [IsIntegral S] [IsIntegral X] (π : S ⟶ X)
    [IsDominant π] (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint S ∈ π ⁻¹ᵁ U)
    (s : Γ(X, U)) :
    functionFieldMap π (X.presheaf.germ U (genericPoint X) hU s) =
      S.presheaf.germ (π ⁻¹ᵁ U) (genericPoint S) hU' (π.app U s) := by
  have e1 := π.germ_stalkMap U (genericPoint S) hU'
  have e2 := congrArg (fun g => g.hom s) e1
  simp only [CommRingCat.comp_apply] at e2
  refine Eq.trans ?_ e2
  simp only [functionFieldMap, TopCat.Presheaf.stalkCongr_hom, CommRingCat.comp_apply]
  congr 1
  exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _

/-- Restricting `π^* b₀ + ∑ tᵢ π^* bᵢ` along a section `σ` of `𝔸ⁿ_X ⟶ X` substitutes `σ^* tᵢ`
for the coordinates. -/
private theorem appLE_section_eval {X : Scheme.{0}} {n : Type} (σ : X ⟶ 𝔸(n; X))
    (hσ : σ ≫ 𝔸(n; X) ↘ X = 𝟙 X) (W : X.Opens) (hle : W ≤ σ ⁻¹ᵁ ((𝔸(n; X) ↘ X) ⁻¹ᵁ W))
    (b₀ : Γ(X, W)) {ι : Type} (s : Finset ι) (k : ι → n) (b : ι → Γ(X, W)) :
    (σ.appLE ((𝔸(n; X) ↘ X) ⁻¹ᵁ W) W hle).hom ((𝔸(n; X) ↘ X).app W b₀ +
      ∑ i ∈ s, (𝔸(n; X)).presheaf.map (homOfLE le_top).op (AffineSpace.coord X (k i)) *
        (𝔸(n; X) ↘ X).app W (b i)) =
      b₀ + ∑ i ∈ s, X.presheaf.map (homOfLE le_top).op (σ.appTop (AffineSpace.coord X (k i))) *
        b i := by
  have hid : (𝟙 X : X ⟶ X).appLE W W le_rfl = 𝟙 _ := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    erw [Category.id_comp]
    exact X.presheaf.map_id _
  have h1 : ∀ c : Γ(X, W), (σ.appLE ((𝔸(n; X) ↘ X) ⁻¹ᵁ W) W hle).hom ((𝔸(n; X) ↘ X).app W c)
      = c := fun c => by
    have e := Scheme.Hom.comp_appLE σ (𝔸(n; X) ↘ X) W W hle
    have e2 := congrArg (fun g => g.hom c) e
    simp only [CommRingCat.comp_apply] at e2
    rw [← e2]
    have e3 : (σ ≫ 𝔸(n; X) ↘ X).appLE W W hle = (𝟙 X : X ⟶ X).appLE W W le_rfl := by
      congr 1
    rw [e3, hid]
    rfl
  have h2 : ∀ t : Γ(𝔸(n; X), ⊤), (σ.appLE ((𝔸(n; X) ↘ X) ⁻¹ᵁ W) W hle).hom
      ((𝔸(n; X)).presheaf.map (homOfLE le_top).op t) =
      X.presheaf.map (homOfLE le_top).op (σ.appTop t) := fun t => by
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  simp only [map_add, map_sum, map_mul, h1, h2]

/-- **The universal cyclic cover datum on `𝔸^r_X`.** For `g₀ ≠ 0, g₁, …, g_r ∈ k(X)` there are a
divisor `M` and a unit `φ = g₀ + ∑ tₖ gₖ` of `k(𝔸^r_X)` with `div φ + mM ≥ 0`, such that near every
point of `X` the divisor `M` has a local equation `g'`, the pull-back of `ψ`, with
`g'^m φ = π^*(ψ^m g₀) + ∑ tₖ π^*(ψ^m gₖ)` regular. -/
private theorem exists_cyclicCover_data {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (hcart : ∀ D : Divisor X, D.IsCartier) {m : ℕ} (hm : 0 < m)
    {r : ℕ} [IsLocallyNoetherian 𝔸(ULift.{0} (Fin r); X)] [IsNormal 𝔸(ULift.{0} (Fin r); X)]
    [CompactSpace 𝔸(ULift.{0} (Fin r); X)]
    (g₀ : X.functionField) (g : Fin r → X.functionField) (hg₀ : g₀ ≠ 0) :
    ∃ (M : Divisor 𝔸(ULift.{0} (Fin r); X)) (φ : (RationalFunctions 𝔸(ULift.{0} (Fin r); X))ˣ)
      (_ : 0 ≤ principalDivisor φ + m • M),
      ∀ x : X, ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ ∃ ψ : X.functionField, ψ ≠ 0 ∧
        ∃ g' : (RationalFunctions 𝔸(ULift.{0} (Fin r); X))ˣ,
          M.IsLocalEquation ((𝔸(ULift.{0} (Fin r); X) ↘ X) ⁻¹ᵁ W) g' ∧
        ∃ (b₀ : Γ(X, W)) (b : Fin r → Γ(X, W)),
          (∀ h : genericPoint X ∈ W, X.presheaf.germ W _ h b₀ = ψ ^ m * g₀) ∧
          (∀ k (h : genericPoint X ∈ W), X.presheaf.germ W _ h (b k) = ψ ^ m * g k) ∧
          (toRationalFunctionsPresheaf _).app (op ((𝔸(ULift.{0} (Fin r); X) ↘ X) ⁻¹ᵁ W))
            ((𝔸(ULift.{0} (Fin r); X) ↘ X).app W b₀ +
              ∑ k, (𝔸(ULift.{0} (Fin r); X)).presheaf.map (homOfLE le_top).op
                (AffineSpace.coord X ⟨k⟩) * (𝔸(ULift.{0} (Fin r); X) ↘ X).app W (b k)) =
            DivisorialCyclicCover.phiOn (g' ^ m * φ) ((𝔸(ULift.{0} (Fin r); X) ↘ X) ⁻¹ᵁ W) := by
  classical
  set n := ULift.{0} (Fin r)
  set S := 𝔸(n; X)
  set π : S ⟶ X := 𝔸(n; X) ↘ X
  have : IsDominant π := inferInstance
  obtain ⟨D, hDc, hloc⟩ := exists_divisor_localEquation hcart
    (fun i : Option (Fin r) => i.elim g₀ g) hm
  have hB : ∀ Z, π (componentGenericPoint S Z) ∉ D.supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant π D
  set M := D.pullback hDc hB
  set eS := rationalFunctionsEquivFunctionField S
  set eX := rationalFunctionsEquivFunctionField X
  set T : Fin r → S.functionField := fun k =>
    S.presheaf.germ ⊤ (genericPoint S) trivial (AffineSpace.coord X ⟨k⟩)
  set φK := functionFieldMap π g₀ + ∑ k, T k * functionFieldMap π (g k)
  have hgenW : ∀ W : X.Opens, (∃ x, x ∈ W) → genericPoint X ∈ W := fun W ⟨x, hx⟩ =>
    ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr ⟨x, trivial, hx⟩
  have hgenW' : ∀ W : X.Opens, genericPoint X ∈ W → genericPoint S ∈ π ⁻¹ᵁ W := fun W h => by
    change π (genericPoint S) ∈ W
    rwa [map_genericPoint_of_isDominant]
  -- the local identity in the function field
  have hid : ∀ (W : X.Opens) (hW : genericPoint X ∈ W) (ψu : (RationalFunctions X)ˣ)
      (b₀ : Γ(X, W)) (b : Fin r → Γ(X, W)),
      X.presheaf.germ W _ hW b₀ = eX ψu ^ m * g₀ →
      (∀ k, X.presheaf.germ W _ hW (b k) = eX ψu ^ m * g k) →
      S.presheaf.germ (π ⁻¹ᵁ W) _ (hgenW' W hW) (π.app W b₀ +
        ∑ k, S.presheaf.map (homOfLE le_top).op (AffineSpace.coord X ⟨k⟩) * π.app W (b k)) =
        functionFieldMap π (eX ψu) ^ m * φK := by
    intro W hW ψu b₀ b hb₀ hb
    have hπg : ∀ c : Γ(X, W), S.presheaf.germ (π ⁻¹ᵁ W) _ (hgenW' W hW) (π.app W c) =
        functionFieldMap π (X.presheaf.germ W _ hW c) := fun c =>
      (functionFieldMap_germ π W hW _ c).symm
    have hT : ∀ k, S.presheaf.germ (π ⁻¹ᵁ W) _ (hgenW' W hW)
        (S.presheaf.map (homOfLE le_top).op (AffineSpace.coord X ⟨k⟩)) = T k := fun k =>
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [map_add, map_sum]
    simp only [map_mul, hπg, hT, hb₀, hb, map_pow, φK, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have hφK : φK ≠ 0 := by
    intro h0
    obtain ⟨x⟩ : Nonempty X := inferInstance
    obtain ⟨W, hW, hxW, ψu, hψu, hb⟩ := hloc x
    choose b hb using hb
    have hWg := hgenW W ⟨x, hxW⟩
    have h1 := hid W hWg ψu (b none) (fun k => b (some k)) (hb none hWg)
      (fun k => hb (some k) hWg)
    rw [h0, mul_zero] at h1
    have h2 : π.app W (b none) + ∑ k, S.presheaf.map (homOfLE le_top).op
        (AffineSpace.coord X ⟨k⟩) * π.app W (b (some k)) = 0 :=
      germ_injective_of_isIntegral (X := S) _ (hgenW' W hWg) (h1.trans (map_zero _).symm)
    set σ₀ : X ⟶ S := AffineSpace.homOfVector (𝟙 X) 0
    have hσ₀ : σ₀ ≫ π = 𝟙 X := AffineSpace.homOfVector_over _ _
    have hle : W ≤ σ₀ ⁻¹ᵁ (π ⁻¹ᵁ W) := by
      rw [← Scheme.Hom.comp_preimage, hσ₀]
      exact le_rfl
    have h3 := appLE_section_eval σ₀ hσ₀ W hle (b none) Finset.univ (fun k => ⟨k⟩)
      (fun k => b (some k))
    rw [h2, map_zero] at h3
    have hcoord : ∀ k : Fin r, σ₀.appTop (AffineSpace.coord X ⟨k⟩) = 0 := fun k =>
      AffineSpace.homOfVector_appTop_coord _ _ _
    simp only [hcoord, map_zero, zero_mul, Finset.sum_const_zero, add_zero] at h3
    have h4 := hb none hWg
    rw [← h3, map_zero] at h4
    have hψ0 : eX ψu ≠ 0 := (ψu.isUnit.map eX).ne_zero
    exact hg₀ ((mul_eq_zero.mp h4.symm).resolve_left (pow_ne_zero _ hψ0))
  set φ : (RationalFunctions S)ˣ := ((Ne.isUnit hφK).map eS.symm).unit
  have heφ : eS (φ : RationalFunctions S) = φK := by
    simp only [φ, IsUnit.unit_spec, RingEquiv.apply_symm_apply]
  have hψ' : ∀ ψu : (RationalFunctions X)ˣ, ∀ Z, π (componentGenericPoint S Z) ∉
      (principalDivisor ψu).supp := fun ψu =>
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant π _
  have hdata : ∀ x : X, ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧
      ∃ ψu : (RationalFunctions X)ˣ, D.IsLocalEquation W ψu ∧
      ∃ (b₀ : Γ(X, W)) (b : Fin r → Γ(X, W)),
        (∀ h : genericPoint X ∈ W, X.presheaf.germ W _ h b₀ = eX ψu ^ m * g₀) ∧
        (∀ k (h : genericPoint X ∈ W), X.presheaf.germ W _ h (b k) = eX ψu ^ m * g k) ∧
        (toRationalFunctionsPresheaf S).app (op (π ⁻¹ᵁ W))
          (π.app W b₀ + ∑ k, S.presheaf.map (homOfLE le_top).op (AffineSpace.coord X ⟨k⟩) *
            π.app W (b k)) =
          DivisorialCyclicCover.phiOn (pullbackRationalFunction π ψu (hψ' ψu) ^ m * φ)
            (π ⁻¹ᵁ W) := by
    intro x
    obtain ⟨W, hW, hxW, ψu, hψu, hb⟩ := hloc x
    choose b hb using hb
    have hWg := hgenW W ⟨x, hxW⟩
    refine ⟨W, hW, hxW, ψu, hψu, b none, fun k => b (some k), hb none,
      fun k => hb (some k), ?_⟩
    funext ⟨Z, hZ⟩
    change S.presheaf.germ _ (componentGenericPoint S Z) hZ _ = _
    rw [← rationalFunctionsEquivFunctionField_symm_germ (π ⁻¹ᵁ W) _ (hgenW' W hWg) Z hZ]
    change eS.symm _ Z = ((pullbackRationalFunction π ψu (hψ' ψu) ^ m * φ :
      (RationalFunctions S)ˣ) : RationalFunctions S) Z
    refine congrFun ?_ Z
    apply eS.injective
    rw [RingEquiv.apply_symm_apply, hid W hWg ψu (b none) (fun k => b (some k)) (hb none hWg)
      (fun k => hb (some k) hWg), Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow,
      heφ, rationalFunctionsEquivFunctionField_pullbackRationalFunction]
  have hφ : 0 ≤ principalDivisor φ + m • M := by
    intro E
    obtain ⟨W, hW, hxW, ψu, hψu, b₀, b, -, -, hv⟩ := hdata (π E.genericPoint)
    have hE : (E.support ∩ π ⁻¹ᵁ W).Nonempty := (E.genericPoint_mem_iff (π ⁻¹ᵁ W)).mp hxW
    have hl : (principalDivisor φ + m • M).IsLocalEquation (π ⁻¹ᵁ W)
        (pullbackRationalFunction π ψu (hψ' ψu) ^ m * φ) := by
      rw [mul_comm]
      have := (isLocalEquation_pullback_pullbackRationalFunction π hDc hB hψu
        (hψ' ψu)).zsmul (m : ℤ)
      rw [natCast_zsmul, zpow_natCast] at this
      exact (Divisor.isLocalEquation_principalDivisor φ _).add this
    change 0 ≤ (principalDivisor φ + m • M).coeff E
    rw [hl E hE]
    have hsec := Divisor.isDivisorialSection_algebraMap (le_refl (0 : Divisor S)) (U := π ⁻¹ᵁ W)
      (π.app W b₀ + ∑ k, S.presheaf.map (homOfLE le_top).op (AffineSpace.coord X ⟨k⟩) *
        π.app W (b k))
    erw [hv] at hsec
    rcases hsec E hE with h0 | h1
    · exact absurd h0 (((pullbackRationalFunction π ψu (hψ' ψu) ^ m * φ).isUnit.map
        (Pi.evalRingHom _ E.component)).ne_zero)
    · change WithZero.exp _ ≤ E.valuation (((pullbackRationalFunction π ψu (hψ' ψu) ^ m * φ :
        (RationalFunctions S)ˣ) : RationalFunctions S) E.component) at h1
      rwa [PrimeDivisor.valuation_component, DivisorWithCoeffs.coeff_zero, neg_zero,
        WithZero.exp_le_exp] at h1
  refine ⟨M, φ, hφ, fun x => ?_⟩
  obtain ⟨W, hW, hxW, ψu, hψu, b₀, b, hb₀, hb, hv⟩ := hdata x
  exact ⟨W, hW, hxW, eX ψu, (ψu.isUnit.map eX).ne_zero, _,
    isLocalEquation_pullback_pullbackRationalFunction π hDc hB hψu (hψ' ψu), b₀, b, hb₀, hb, hv⟩

/-- The section `x ↦ (x, f^* v)` of `𝔸ⁿ_X` is the base change of the section `v` of `𝔸ⁿ_Y`. -/
private theorem isPullback_homOfVector {X Y : Scheme.{0}} {n : Type} (f : X ⟶ Y)
    (v : n → Γ(Y, ⊤)) :
    IsPullback (AffineSpace.homOfVector (𝟙 X) (fun i => f.appTop (v i))) f
      (AffineSpace.map n f) (AffineSpace.homOfVector (𝟙 Y) v) := by
  refine IsPullback.of_right (h₁₂ := 𝔸(n; X) ↘ X) (h₂₂ := 𝔸(n; Y) ↘ Y) ?_ ?_
    (AffineSpace.isPullback_map f).flip
  · rw [AffineSpace.homOfVector_over, AffineSpace.homOfVector_over]
    exact IsPullback.of_horiz_isIso (by simp)
  · apply AffineSpace.hom_ext
    · simp [AffineSpace.map_over, AffineSpace.homOfVector_over]
    · intro i
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        CommRingCat.comp_apply, AffineSpace.map_appTop_coord, AffineSpace.homOfVector_appTop_coord,
        AffineSpace.homOfVector_appTop_coord]

/-- The fibre of `𝒵 ⟶ S ⟶ T` over `τ` is the fibre product of `𝒵 ⟶ S` with the fibre `X` of
`S ⟶ T` over `τ`. -/
private theorem exists_isPullback_fibre {𝒵 S X T P : Scheme.{0}} (toBase : 𝒵 ⟶ S) (ρ : S ⟶ T)
    {σ : X ⟶ S} {sX : X ⟶ P} {τ : P ⟶ T} (hσ : IsPullback σ sX ρ τ) :
    ∃ q : pullback (toBase ≫ ρ) τ ⟶ X, q ≫ sX = pullback.snd _ _ ∧
      IsPullback (pullback.fst _ _) q toBase σ := by
  refine ⟨hσ.lift (pullback.fst _ _ ≫ toBase) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition]), hσ.lift_snd _ _ _, ?_⟩
  refine IsPullback.of_bot ?_ (hσ.lift_fst _ _ _).symm hσ
  rw [hσ.lift_snd]
  exact IsPullback.of_hasPullback _ _

/-- **The charts of a divisorial cyclic cover.** Over an affine open `U` on which `M` has a local
equation `g`, the cover is `Spec 𝒪(U)[z]/(z^m - g^m φ)`. -/
private theorem exists_chart_cyclicCover {S : Scheme.{0}} [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] (m : ℕ) [NeZero m] (M : Divisor S) {φ : (RationalFunctions S)ˣ}
    (hφ : 0 ≤ principalDivisor φ + m • M) {U : S.Opens} (hU : IsAffineOpen U)
    {g : (RationalFunctions S)ˣ} (hg : M.IsLocalEquation U g) :
    ∃ v : Γ(S, U), (toRationalFunctionsPresheaf S).app (op U) v =
        DivisorialCyclicCover.phiOn (g ^ m * φ) U ∧
      ∃ (A' : CommRingCat.{0}) (str : Γ(S, U) ⟶ A')
        (ch : Spec A' ⟶ DivisorialCyclicCover.cover m M hφ),
        IsPullback ch (Spec.map str) (DivisorialCyclicCover.toBase m M hφ) hU.fromSpec ∧
        ∃ eA : A' ≅ CommRingCat.of (AdjoinRoot (Polynomial.X ^ m - Polynomial.C v)),
          str ≫ eA.hom = CommRingCat.ofHom (AdjoinRoot.of _) := by
  let := ((DivisorialCyclicCover.localSubalgebra m M hφ).algebraMap U).toAlgebra
  obtain ⟨v, hv, -, e, -⟩ :=
    DivisorialCyclicCover.exists_algEquiv_adjoinRoot_of_isLocalEquation m M hφ hg
  refine ⟨v, hv, _, (DivisorialCyclicCover.situation m M hφ).algebra.hom.hom.app (op U),
    (Stacks.RelativeSpec.gluedSpectrum (DivisorialCyclicCover.situation m M hφ)).chart ⟨U, hU⟩,
    ?_, e.symm.toRingEquiv.toCommRingCatIso, ?_⟩
  · have h := (Stacks.RelativeSpec.gluedSpectrum
      (DivisorialCyclicCover.situation m M hφ)).chart_isPullback ⟨U, hU⟩
    refine h.of_iso (Iso.refl _) (Iso.refl _) hU.isoSpec (Iso.refl _) ?_ ?_ ?_ ?_
    · erw [Category.comp_id]
    · erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · erw [Category.comp_id]
    · rw [← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id]
  · ext r
    exact e.symm.commutes r

/-- A morphism which is locally on the target the spectrum of a finite ring map is finite. -/
private theorem isFinite_of_forall_isPullback {𝒵 S : Scheme.{0}} (f : 𝒵 ⟶ S)
    (H : ∀ s : S, ∃ (U : S.Opens) (hU : IsAffineOpen U), s ∈ U ∧ ∃ (A' : CommRingCat.{0})
      (str : Γ(S, U) ⟶ A') (ch : Spec A' ⟶ 𝒵),
      IsPullback ch (Spec.map str) f hU.fromSpec ∧ str.hom.Finite) : IsFinite f := by
  have : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{0}) :=
    Stacks.Morphisms.isFinite_isZariskiLocalAtTarget.{0}
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun s => ?_
  obtain ⟨U, hU, hsU, A', str, ch, hch, hfin⟩ := H s
  refine ⟨U, hsU, ?_⟩
  have h' : IsPullback ch (Spec.map str ≫ hU.isoSpec.inv) f U.ι :=
    hch.of_iso (Iso.refl _) (Iso.refl _) hU.isoSpec.symm (Iso.refl _) (by simp) (by simp)
      (by simp) (by rw [← IsAffineOpen.isoSpec_inv_ι]; simp)
  let e := (isPullback_morphismRestrict f U).flip.isoIsPullback _ _ h'
  have he : e.hom ≫ Spec.map str ≫ hU.isoSpec.inv = f ∣_ U :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  rw [← he]
  have : IsFinite (Spec.map str) := (IsFinite.SpecMap_iff _).mpr hfin
  infer_instance

/-- A finite morphism followed by a projective morphism to an affine scheme is projective. -/
private theorem isProjectiveMorphism_comp_of_isFinite {Y' Y T : Scheme.{0}} (g : Y' ⟶ Y)
    [IsFinite g] (ρ : Y ⟶ T) [IsAffine T] (hρ : IsProjectiveMorphism ρ) :
    IsProjectiveMorphism (g ≫ ρ) := by
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective ρ (Stacks.Ample.unitModule T)
    (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    (isQuasiProjective_of_isHQuasiProjective ρ hρ.isHQuasiProjective)
  have hg : IsProjectiveMorphism g :=
    isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
      ⟨isHQuasiProjective_of_isQuasiProjective g L hLa
        (AlgebraicGeometry.isQuasiProjective_of_isFinite g), inferInstance⟩
  exact hg.comp hρ

/-- **The universal cyclic cover over an affine family.** For `g₀, g₁, …, g_r ∈ k(X)` such that
`f_c = g₀ + ∑ cₖ gₖ` never vanishes, there is a projective family `𝒵 ⟶ T` over the affine space
`T = 𝔸^r_ℂ` whose fibre over the point `c` is locally the cyclic cover `z^m = f_c` of `X`. -/
private theorem exists_cyclicCover_family
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    (hXB : IsSNCSubboundaryPair sX B) {m : ℕ} (hm : 0 < m) {r : ℕ}
    (g₀ : X.functionField) (g : Fin r → X.functionField)
    (hne : ∀ c : Fin r → ℂ, letI := functionFieldAlgebra sX;
      g₀ + ∑ k, algebraMap ℂ X.functionField (c k) * g k ≠ 0) :
    letI := functionFieldAlgebra sX
    ∃ (𝒵 T : Scheme.{0}) (h : 𝒵 ⟶ T) (sZ : 𝒵 ⟶ Spec (.of ℂ)) (sT : T ⟶ Spec (.of ℂ))
      (_ : h ≫ sT = sZ) (_ : IsReduced T) (τ : (Fin r → ℂ) → (Spec (.of ℂ) ⟶ T)),
      IsQuasiProjective sT ∧ IsProjectiveMorphism h ∧ (∀ c, τ c ≫ sT = 𝟙 _) ∧
      (∀ t : Spec (.of ℂ) ⟶ T, t ≫ sT = 𝟙 _ → ∃ c, t = τ c) ∧
      ∀ c, ∃ q : pullback h (τ c) ⟶ X, q ≫ sX = pullback.snd h (τ c) ∧
        IsLocallyCyclicCover q m (g₀ + ∑ k, algebraMap ℂ X.functionField (c k) * g k) := by
  classical
  let := functionFieldAlgebra sX
  have : NeZero m := ⟨hm.ne'⟩
  have : AlgebraicGeometry.IsVariety ℂ sX := hXB.isProjectiveVariety.toIsVariety
  have : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).mp hXB.isSmoothScheme
  have hsXp : IsProjectiveMorphism sX := hXB.isProjectiveVariety.isProjective
  have : IsProper sX := isProper_of_isProjectiveMorphism sX hsXp
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : SmoothOfRelativeDimension r (𝔸(ULift.{0} (Fin r); X) ↘ X) :=
    Stacks.Chow.smoothOfRelativeDimension_affineSpaceOver X r
  have : Smooth (𝔸(ULift.{0} (Fin r); X) ↘ X) := SmoothOfRelativeDimension.smooth r _
  have : IsNormal 𝔸(ULift.{0} (Fin r); X) :=
    isNormal_of_smooth_over_field ((𝔸(ULift.{0} (Fin r); X) ↘ X) ≫ sX)
  have : IsLocallyNoetherian 𝔸(ULift.{0} (Fin r); X) :=
    LocallyOfFiniteType.isLocallyNoetherian ((𝔸(ULift.{0} (Fin r); X) ↘ X) ≫ sX)
  have : CompactSpace 𝔸(ULift.{0} (Fin r); X) :=
    QuasiCompact.compactSpace_of_compactSpace (𝔸(ULift.{0} (Fin r); X) ↘ X)
  have hg₀ : g₀ ≠ 0 := by simpa using hne 0
  obtain ⟨M, φ, hφ, hdata⟩ := exists_cyclicCover_data
    (MMP.Fourfold.isCartier_of_isSmoothScheme hXB.isSmoothScheme) hm g₀ g hg₀
  let n := ULift.{0} (Fin r)
  let π : 𝔸(n; X) ⟶ X := 𝔸(n; X) ↘ X
  let toB := DivisorialCyclicCover.toBase m M hφ
  let ρ : 𝔸(n; X) ⟶ 𝔸(n; Spec (.of ℂ)) := AffineSpace.map n sX
  let sT : 𝔸(n; Spec (.of ℂ)) ⟶ Spec (.of ℂ) := 𝔸(n; Spec (.of ℂ)) ↘ Spec (.of ℂ)
  -- the charts of the cover over the affine opens `π⁻¹ W`
  have hcharts : ∀ x : X, ∃ (W : X.Opens) (hW : IsAffineOpen W), x ∈ W ∧
      ∃ ψ : X.functionField, ψ ≠ 0 ∧ ∃ (b₀ : Γ(X, W)) (b : Fin r → Γ(X, W)),
        (∀ h : genericPoint X ∈ W, X.presheaf.germ W _ h b₀ = ψ ^ m * g₀) ∧
        (∀ k (h : genericPoint X ∈ W), X.presheaf.germ W _ h (b k) = ψ ^ m * g k) ∧
        ∃ (A' : CommRingCat.{0}) (str : Γ(𝔸(n; X), π ⁻¹ᵁ W) ⟶ A')
          (ch : Spec A' ⟶ DivisorialCyclicCover.cover m M hφ),
          IsPullback ch (Spec.map str) toB (hW.preimage π).fromSpec ∧
          ∃ eA : A' ≅ CommRingCat.of (AdjoinRoot (Polynomial.X ^ m - Polynomial.C
            (π.app W b₀ + ∑ k, (𝔸(n; X)).presheaf.map (homOfLE le_top).op
              (AffineSpace.coord X ⟨k⟩) * π.app W (b k)))),
            str ≫ eA.hom = CommRingCat.ofHom (AdjoinRoot.of _) := by
    intro x
    obtain ⟨W, hW, hxW, ψ, hψ, g', hg', b₀, b, hb₀, hb, hv⟩ := hdata x
    obtain ⟨v, hvv, A', str, ch, hch, eA, heA⟩ :=
      exists_chart_cyclicCover m M hφ (hW.preimage π) hg'
    have hveq : v = π.app W b₀ + ∑ k, (𝔸(n; X)).presheaf.map (homOfLE le_top).op
        (AffineSpace.coord X ⟨k⟩) * π.app W (b k) := by
      have h1 := hvv.trans hv.symm
      set Z₀ : irreducibleComponents 𝔸(n; X) := pointComponent (genericPoint 𝔸(n; X))
      have hZ : componentGenericPoint 𝔸(n; X) Z₀ ∈ π ⁻¹ᵁ W := by
        rw [componentGenericPoint_eq_genericPoint]
        change π (genericPoint 𝔸(n; X)) ∈ W
        rw [map_genericPoint_of_isDominant]
        exact ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr ⟨x, trivial, hxW⟩
      exact germ_injective_of_isIntegral (X := 𝔸(n; X)) _ hZ (congrFun h1 ⟨Z₀, hZ⟩)
    subst hveq
    exact ⟨W, hW, hxW, ψ, hψ, b₀, b, hb₀, hb, A', str, ch, hch, eA, heA⟩
  have hfin : IsFinite toB := isFinite_of_forall_isPullback toB fun s => by
    obtain ⟨W, hW, hxW, ψ, hψ, b₀, b, -, -, A', str, ch, hch, eA, heA⟩ := hcharts (π s)
    refine ⟨π ⁻¹ᵁ W, hW.preimage π, hxW, A', str, ch, hch, ?_⟩
    have hstr : str = CommRingCat.ofHom (AdjoinRoot.of _) ≫ eA.inv := by
      rw [← heA, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hstr, CommRingCat.hom_comp]
    refine RingHom.Finite.comp (RingHom.Finite.of_surjective _
      eA.commRingCatIsoToRingEquiv.symm.surjective) ?_
    exact RingHom.finite_algebraMap.mpr
      ((Polynomial.monic_X_pow_sub_C _ (NeZero.ne m)).finite_adjoinRoot)
  have hρ : IsProjectiveMorphism ρ := by
    have hpb := (AffineSpace.isPullback_map (n := n) sX).flip
    exact IsProjectiveMorphism.of_iso hpb.isoPullback.symm (Iso.refl _)
      (by rw [Iso.symm_hom, hpb.isoPullback_inv_snd, Iso.refl_hom, Category.comp_id])
      (hsXp.baseChange sT)
  have hh : IsProjectiveMorphism (toB ≫ ρ) := isProjectiveMorphism_comp_of_isFinite toB ρ hρ
  let τ : (Fin r → ℂ) → (Spec (.of ℂ) ⟶ 𝔸(n; Spec (.of ℂ))) := fun c =>
    AffineSpace.homOfVector (𝟙 _) (fun i => (Scheme.ΓSpecIso (.of ℂ)).inv (c i.down))
  refine ⟨DivisorialCyclicCover.cover m M hφ, 𝔸(n; Spec (.of ℂ)), toB ≫ ρ, (toB ≫ ρ) ≫ sT, sT,
    rfl, inferInstance, τ, ?_, hh, fun c => AffineSpace.homOfVector_over _ _, ?_, fun c => ?_⟩
  · exact AlgebraicGeometry.isQuasiProjective_of_isQuasiAffineHom sT inferInstance
  · intro t ht
    refine ⟨fun k => (Scheme.ΓSpecIso (.of ℂ)).hom (t.appTop (AffineSpace.coord _ ⟨k⟩)), ?_⟩
    apply AffineSpace.hom_ext
    · rw [ht, AffineSpace.homOfVector_over]
    · intro i
      rw [AffineSpace.homOfVector_appTop_coord]
      exact (Iso.hom_inv_id_apply _ _).symm
  · have hσ := isPullback_homOfVector sX
      (fun i : n => (Scheme.ΓSpecIso (.of ℂ)).inv (c i.down))
    let σ := AffineSpace.homOfVector (𝟙 X)
      (fun i : n => sX.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv (c i.down)))
    obtain ⟨q, hqs, hF⟩ := exists_isPullback_fibre toB ρ hσ
    refine ⟨q, hqs, fun x => ?_⟩
    obtain ⟨W, hW, hxW, ψ, hψ, b₀, b, hb₀, hb, A', str, ch, hch, eA, heA⟩ := hcharts x
    have hσπ : σ ≫ π = 𝟙 X := AffineSpace.homOfVector_over _ _
    have hle : W ≤ σ ⁻¹ᵁ (π ⁻¹ᵁ W) := by
      rw [← Scheme.Hom.comp_preimage, hσπ]
      exact le_rfl
    obtain ⟨j, hj⟩ := exists_isPullback_adjoinRoot_of_isPullback hF hW (hW.preimage π) hle hch m
      _ eA heA
    have : Nonempty W := ⟨⟨x, hxW⟩⟩
    have hWg : genericPoint X ∈ W :=
      ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr ⟨x, trivial, hxW⟩
    refine ⟨W, hxW, isCyclicCoverChart_of_isPullback hW hψ ?_ hj⟩
    rw [appLE_section_eval σ hσπ W hle b₀ Finset.univ (fun k => ⟨k⟩) b]
    change X.presheaf.germ W _ hWg _ = _
    rw [map_add, map_sum, hb₀ hWg]
    simp only [map_mul, hb _ hWg, TopCat.Presheaf.germ_res_apply]
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show σ.appTop (AffineSpace.coord X ⟨k⟩) =
      sX.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv (c k)) from
        AffineSpace.homOfVector_appTop_coord _ _ _, mul_left_comm]
    rfl

end LocalCyclicCover

/-- **Bounded resolved cyclic covers along an affine family of rational functions.** For
`g₀, g₁, …, g_r ∈ k(X)` such that `g₀ + ∑ cₖ gₖ` never vanishes, there is `b` such that every
`g₀ + ∑ cₖ gₖ`, `c ∈ ℂ^r`, has a resolved cyclic cover of degree `m` with `b₂ ≤ b`. -/
private theorem exists_hasResolvedCyclicCover_of_affineFamily
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hn : topologicalKrullDim X = 2) {B : QDivisor X}
    (hXB : IsSNCSubboundaryPair sX B) {m : ℕ} (hm : 0 < m) {r : ℕ}
    (g₀ : X.functionField) (g : Fin r → X.functionField)
    (hne : ∀ c : Fin r → ℂ, letI := functionFieldAlgebra sX;
      g₀ + ∑ k, algebraMap ℂ X.functionField (c k) * g k ≠ 0) :
    ∃ b : ℕ, ∀ c : Fin r → ℂ, letI := functionFieldAlgebra sX;
      HasResolvedCyclicCover sX m b (g₀ + ∑ k, algebraMap ℂ X.functionField (c k) * g k) := by
  let := functionFieldAlgebra sX
  obtain ⟨𝒵, T, h, sZ, sT, hsZ, hTred, τ, hTq, hh, hτ, hτsurj, hfib⟩ :=
    exists_cyclicCover_family hXB hm g₀ g hne
  obtain ⟨b, hb⟩ := MMP.Fourfold.exists_forall_finrank_singularCohomology_two_le_of_resolution
    h sZ sT hsZ hTq hh fun t ht => by
      obtain ⟨c, rfl⟩ := hτsurj t ht
      obtain ⟨q, hqs, hq⟩ := hfib c
      have : IsProper h := isProper_of_isProjectiveMorphism h hh
      have : LocallyOfFiniteType (q ≫ sX) := by rw [hqs]; infer_instance
      exact isReduced_and_dim_eq_of_isLocallyCyclicCover hn hXB hm (hne c) q hq
  refine ⟨m * b, fun c => ?_⟩
  obtain ⟨q, hqs, hq⟩ := hfib c
  obtain ⟨Y, p, hproj, hsm, hU, hbet⟩ := hb (τ c) (hτ c)
  rw [← hqs] at hproj hsm hbet
  have : IsProper h := isProper_of_isProjectiveMorphism h hh
  have : LocallyOfFiniteType (q ≫ sX) := by rw [hqs]; infer_instance
  have : CompactSpace ((CategoryTheory.Limits.pullback h (τ c) : Scheme.{0})) :=
    QuasiCompact.compactSpace_of_compactSpace (CategoryTheory.Limits.pullback.snd h (τ c))
  exact (hasResolvedCyclicCover_of_resolution hm (hne c) q hq p hproj hsm hU).mono
    (Nat.mul_le_mul_left m hbet)

/-- **Bounded resolved cyclic covers along a finite-dimensional space of rational functions.**
For a finite-dimensional `ℂ`-subspace `W` of `k(X)`, there is `b` such that every nonzero
`f ∈ W` has a resolved cyclic cover of degree `m` with `b₂ ≤ b`. -/
private theorem exists_hasResolvedCyclicCover_of_finiteDimensional
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hn : topologicalKrullDim X = 2) {B : QDivisor X}
    (hXB : IsSNCSubboundaryPair sX B) {m : ℕ} (hm : 0 < m)
    (W : letI := functionFieldAlgebra sX; Submodule ℂ X.functionField)
    (hW : letI := functionFieldAlgebra sX; Module.Finite ℂ W) :
    ∃ b : ℕ, ∀ f ∈ W, f ≠ 0 → HasResolvedCyclicCover sX m b f := by
  classical
  let := functionFieldAlgebra sX
  set N := Module.finrank ℂ W
  let e : Module.Basis (Fin N) ℂ W := Module.finBasis ℂ W
  have hfam : ∀ j : Fin N, ∃ b : ℕ, ∀ c : Fin N → ℂ, HasResolvedCyclicCover sX m b
      ((e j : X.functionField) + ∑ k, algebraMap ℂ X.functionField (c k) *
        (if k = j then 0 else (e k : X.functionField))) := fun j => by
    refine exists_hasResolvedCyclicCover_of_affineFamily hn hXB hm _ _ fun c h0 => ?_
    have h1 : ((e j + ∑ k, (if k = j then (0 : ℂ) else c k) • e k : W) : X.functionField) = 0 := by
      rw [← h0]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> simp [Algebra.smul_def]
    have h2 := congrArg (fun v => e.repr v j)
      (Subtype.ext h1 : e j + ∑ k, (if k = j then (0 : ℂ) else c k) • e k = 0)
    have h3 : ∀ k, e.repr ((if k = j then (0 : ℂ) else c k) • e k) j = 0 := fun k => by
      rw [map_smul, e.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
      split_ifs <;> simp_all
    simp only [map_add, map_sum, Finsupp.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
      h3, Finset.sum_const_zero, add_zero, e.repr_self, Finsupp.single_eq_same, map_zero,
      Finsupp.coe_zero, Pi.zero_apply] at h2
    exact one_ne_zero h2
  choose b hb using hfam
  refine ⟨∑ j, b j, fun f hf hf0 => ?_⟩
  set a := e.repr ⟨f, hf⟩
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra! h
    apply hf0
    have : (⟨f, hf⟩ : W) = 0 := e.repr.injective (by rw [map_zero]; ext j; exact h j)
    exact congrArg Subtype.val this
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (a j) hm
  have hμ0 : μ ≠ 0 := by rintro rfl; rw [zero_pow hm.ne'] at hμ; exact hj hμ.symm
  have hcov := ((hb j fun k => a k / a j).mono
    (Finset.single_le_sum (fun i _ => Nat.zero_le (b i)) (Finset.mem_univ j))).pow_mul
    ((map_ne_zero_iff _ (algebraMap ℂ X.functionField).injective).mpr hμ0)
  convert hcov using 1
  have hfe : f = ∑ k, algebraMap ℂ X.functionField (a k) * (e k : X.functionField) := by
    have h1 : (∑ i, a i • e i : W) = ⟨f, hf⟩ := e.sum_repr ⟨f, hf⟩
    have h2 : ∑ i, ((a i • e i : W) : X.functionField) = f := by
      rw [← Submodule.coe_sum, h1]
    rw [← h2]
    exact Finset.sum_congr rfl fun k _ => Algebra.smul_def _ _
  have haj : algebraMap ℂ X.functionField (a j) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℂ X.functionField).injective).mpr hj
  have key : ∀ k, algebraMap ℂ X.functionField (a k) * (e k : X.functionField) =
      (if k = j then algebraMap ℂ X.functionField (a j) * (e j : X.functionField) else 0) +
        algebraMap ℂ X.functionField (a j) * (algebraMap ℂ X.functionField (a k / a j) *
          if k = j then 0 else (e k : X.functionField)) := by
    intro k
    split_ifs with hk
    · subst hk; ring
    · rw [map_div₀]; field_simp; ring
  rw [hfe, Finset.sum_congr rfl fun k _ => key k, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte]
  rw [← Finset.mul_sum, ← map_pow, hμ, mul_add]

/-- **A bounded family of resolved cyclic covers of subklt pluriforms on a surface.** Let `X` be a
smooth projective complex surface, `B` an snc `ℚ`-divisor with all coefficients less than one,
and `m > 0` with `mB` integral. There is `b : ℕ` such that for every nonzero
`s ∈ H⁰(X, m(K_X + B))` there are finitely many integral smooth projective complex surfaces `Yᵢ`
with dominant morphisms `pᵢ : Yᵢ ⟶ X`, and holomorphic two-forms `ωᵢ` on `Yᵢ`, such that
* `∑ᵢ dim_ℚ H²(Yᵢ^an; ℚ) ≤ b`;
* `ωᵢ ≠ 0` and `ωᵢ^{⊗m} = pᵢ^* s`;
* `⨆ᵢ Yᵢ` resolves the degree-`m` cyclic cover `z^m = s`: for some nonzero rational
  two-form `η` on `X`, the ratios `zᵢ = ωᵢ / pᵢ^* η` generate `∏ᵢ k(Yᵢ)` as a
  `k(X)`-algebra, and `∑ᵢ [k(Yᵢ) : k(X)] = m`. -/
@[mmp "lem_fourfold_subklt_surface_cyclic_cover_family"]
public theorem exists_cyclicCover_resolution_finrank_le
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hn : topologicalKrullDim X = 2) {B : QDivisor X}
    (hXB : IsSNCSubboundaryPair sX B) (hB : ∀ P, B.coeff P < 1)
    {m : ℕ} (hm : 0 < m) (hmB : ∀ P, ∃ a : ℤ, (m : ℚ) * B.coeff P = a) :
    ∃ b : ℕ, ∀ s ∈ logPluricanonicalSections sX 2 m B, s ≠ 0 →
      ∃ (k : ℕ) (Y : Fin k → Scheme.{0}) (_ : ∀ i, IsIntegral (Y i))
        (_ : ∀ i, IsLocallyNoetherian (Y i)) (_ : ∀ i, IsNormal (Y i))
        (p : ∀ i, Y i ⟶ X) (_ : ∀ i, IsDominant (p i)),
        (∀ i, IsProjectiveMorphism (p i ≫ sX)) ∧ (∀ i, SmoothOfRelativeDimension 2 (p i ≫ sX)) ∧
        ∑ i, Module.finrank ℚ
            (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace (p i ≫ sX)) ∅ 2) ≤ b ∧
        letI := fun i => functionFieldAlgebra (p i ≫ sX)
        ∃ ω : ∀ i, ⋀[(Y i).functionField]^2 Ω[(Y i).functionField⁄ℂ],
          (∀ i, ω i ≠ 0) ∧
          (∀ i, (formPow (ω i) 1 : RationalPluriForms (p i ≫ sX) 2 (1 : ℕ)) ∈
            logPluricanonicalSections (p i ≫ sX) 2 1 0) ∧
          (∀ i, (formPow (ω i) m : RationalPluriForms (p i ≫ sX) 2 m) =
            pullbackRationalPluriForms sX (p i) s) ∧
          letI := functionFieldAlgebra sX
          letI := fun i => functionFieldMapAlgebra (p i)
          ∃ η : ⋀[X.functionField]^2 Ω[X.functionField⁄ℂ], η ≠ 0 ∧
            ∃ z : ∀ i, (Y i).functionField,
              (∀ i, (formPow (ω i) 1 : RationalPluriForms (p i ≫ sX) 2 (1 : ℕ)) =
                z i • pullbackRationalPluriForms sX (p i)
                  (show RationalPluriForms sX 2 (1 : ℕ) from formPow η 1)) ∧
              Algebra.adjoin X.functionField {z} = ⊤ ∧
              Module.finrank X.functionField (∀ i, (Y i).functionField) = m := by
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hXB.isProjectiveVariety.1.toLocallyOfFiniteType
  obtain ⟨bT⟩ := exists_basis_topForms (sX := sX) hn
  set η := bT () with hηdef
  have hη0 : η ≠ 0 := bT.ne_zero ()
  have hηspan : Submodule.span X.functionField {η} = ⊤ := by
    have := bT.span_eq
    rwa [Set.range_unique] at this
  -- the coordinate map `f ↦ f η^{⊗m}`
  set ω₀ : RationalPluriForms sX 2 m := formPow η m with hω₀
  let ℓ : X.functionField →ₗ[ℂ] RationalPluriForms sX 2 m :=
    { toFun := fun f => f • ω₀
      map_add' := fun f g => add_smul f g _
      map_smul' := fun c f => by
        simp only [RingHom.id_apply]
        rw [RationalPluriForms.smul_def sX c (f • ω₀), Algebra.smul_def, mul_smul] }
  let W : Submodule ℂ X.functionField := (logPluricanonicalSections sX 2 m B).comap ℓ
  have hWfin : Module.Finite ℂ W := by
    have := MMP.Fourfold.finite_logPluricanonicalSections (m := m) hn hXB
    have hω₀0 : ω₀ ≠ 0 := by
      rw [hω₀, hηdef, ← ZTensorPower.basis_natCast]
      exact (ZTensorPower.basis bT (m : ℤ)).ne_zero ()
    have hinj : Function.Injective ℓ := smul_left_injective _ hω₀0
    exact Module.Finite.of_injective (ℓ.restrict (p := W) (q := logPluricanonicalSections sX 2 m B)
      fun _ hx => hx) fun x y hxy => Subtype.ext (hinj (congrArg Subtype.val hxy))
  obtain ⟨b, hb⟩ := exists_hasResolvedCyclicCover_of_finiteDimensional hn hXB hm W hWfin
  refine ⟨b, fun s hs hs0 => ?_⟩
  set f : X.functionField := (ZTensorPower.basis bT (m : ℤ)).repr s () with hfdef
  have hsf : s = f • (formPow η m : RationalPluriForms sX 2 m) := eq_repr_smul_formPow bT s
  have hf0 : f ≠ 0 := fun h => hs0 (by rw [hsf, h]; exact zero_smul _ _)
  have hfW : f ∈ W := by
    change ℓ f ∈ logPluricanonicalSections sX 2 m B
    change f • (formPow η m : RationalPluriForms sX 2 m) ∈ _
    rwa [← hsf]
  obtain ⟨k, Y, hI, hN, hNo, p, hp, hproj, hsm, hbet, z, hz, hadj, hrank⟩ := hb f hfW hf0
  refine ⟨k, Y, hI, hN, hNo, p, hp, hproj, hsm, hbet, ?_⟩
  let := fun i => functionFieldAlgebra (p i ≫ sX)
  let := fun i => functionFieldMapAlgebra (p i)
  have := fun i => isScalarTower_functionFieldMap sX (p i)
  have hdimY : ∀ i, topologicalKrullDim (Y i) = 2 := fun i => by
    have := hsm i
    exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 2 (p i ≫ sX)
  have hgen : ∀ i, IsPullbackGenerator (Y i).functionField η := fun i => by
    have := isProper_of_isProjectiveMorphism _ (hproj i)
    have : LocallyOfFiniteType (p i ≫ sX) := inferInstance
    obtain ⟨ω', hω'⟩ := exists_isPullbackGenerator_of_topologicalKrullDim_eq sX (p i) hn (hdimY i)
    exact MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω' hηspan hη0
  have hz0 : ∀ i, z i ≠ 0 := fun i h => by
    have := hz i
    rw [h, zero_pow hm.ne', eq_comm] at this
    exact hf0 ((map_eq_zero_iff _
      (algebraMap X.functionField (Y i).functionField).injective).1 this)
  have hpow : ∀ i (a : ℕ) (c : X.functionField),
      pullbackRationalPluriForms sX (p i)
        (show RationalPluriForms sX 2 (a : ℕ) from c • formPow η a) =
        (algebraMap X.functionField (Y i).functionField c •
          formPow (topFormsMap ℂ X.functionField (Y i).functionField 2 η) a :
            RationalPluriForms (p i ≫ sX) 2 (a : ℕ)) := fun i a c =>
    pullbackForms_smul_formPow (hgen i) a c
  have hroot : ∀ i, (formPow (z i • topFormsMap ℂ X.functionField (Y i).functionField 2 η) m :
      RationalPluriForms (p i ≫ sX) 2 m) = pullbackRationalPluriForms sX (p i) s := fun i => by
    rw [formPow_smul, hz i, hsf]
    exact (hpow i m f).symm
  refine ⟨fun i => z i • topFormsMap ℂ X.functionField (Y i).functionField 2 η,
    fun i => smul_ne_zero (hz0 i) (hgen i).2.2,
    fun i => formPow_one_mem_of_formPow_eq_pullback hn hXB hB hm s hs (p i) (hsm i) _ (hroot i),
    hroot, η, hη0, z, fun i => ?_, hadj, hrank⟩
  have h1 := hpow i 1 1
  rw [one_smul, map_one, one_smul] at h1
  change (formPow (z i • topFormsMap ℂ X.functionField (Y i).functionField 2 η) 1 :
    RationalPluriForms (p i ≫ sX) 2 (1 : ℕ)) = _
  rw [formPow_smul, pow_one]
  exact congrArg (z i • ·) h1.symm

end MMP.Fourfold

end CyclicCover
