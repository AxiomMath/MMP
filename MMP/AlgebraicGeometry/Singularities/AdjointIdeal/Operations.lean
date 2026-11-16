module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.AdjointIdeal.ReducedSncBoundary
public import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
public import MMP.AlgebraicGeometry.MMP.Fourfold.PairSingularities
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.EffectiveIdealSheaf
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus

/-!
# Independence and elementary operations for reduced-boundary adjoint ideals

Let `X` be a smooth variety over an algebraically closed field of characteristic zero, `Δ` a
reduced snc divisor and `D` an effective `ℚ`-divisor containing no stratum of `Δ`. The
reduced-boundary adjoint ideal `𝒥_{Δ,D} = μ_*𝒪_Y(E - ⌊μ^*D⌋)`
(`MMP.Fourfold.IsReducedAdjointIdealOn`) can be computed on some projective log resolution `μ`
of `Δ + D`; it is a coherent ideal sheaf of `𝒪_X` and does not depend on `μ`. It decreases when
`D` or `Δ` increases, and for an effective integral Cartier divisor `A`,
`𝒥_{Δ,D+A} = 𝒥_{Δ,D} ⊗ 𝒪_X(-A)`. Consequently `D - A ≤ G` and `𝒥_{Δ,G} = 𝒪_X` give
`𝒪_X(-A) ⊆ 𝒥_{Δ,D}`. Finally `𝒥_{Δ,D} = 𝒪_X` exactly when every log discrepancy
`a(F, X, Δ + D)` is positive, except at the divisors `F` with `a(F, X, Δ) = 0`, where it is zero.

The key step is a description of `𝒥_{Δ,D}` by orders along *all* divisors `F` over `X`: a
rational function `g` is a section over `U` exactly when
`v_F(g) ≤ exp (⌈a(F, X, Δ + D)⌉ - 1 + [a(F, X, Δ) = 0])` for every `F` centred in `U`. This
description does not mention `μ`, which gives independence of the resolution; monotonicity, the
shift by `A`, the containment and the unit-ideal criterion are then statements about exponents.

## Main results

* `MMP.Fourfold.isReducedAdjointIdealOn_operations`: the seven assertions.

## Implementation notes

* Ideals are subsets of `K(X)` given by their sections over the opens of `X`
  (`MMP.Intersection.multiplierIdealSections`); `𝒪_X` is the image of
  `AlgebraicGeometry.Scheme.germToFunctionField`. Being a coherent ideal sheaf is rendered as:
  the sections are regular functions, and they are the sections of an
  `AlgebraicGeometry.Scheme.IdealSheafData` on every non-empty affine open.
* `𝒪_X(-A)` is `μ_*𝒪(-A)` for `μ = 𝟙 X`, and the tensor product `𝒥 ⊗ 𝒪_X(-A)` is the subsheaf
  of `K(X)` whose sections are locally finite sums of products.
* Log discrepancies are compared by adding Cartier divisors to the presentation of `K_X + B` in
  `MMP.Intersection.IsLogDiscrepancy`, and identified by their uniqueness. The source passes to a
  common log resolution and applies the projection formula; the valuative description replaces
  both, and the integral shift is proved by multiplying by a local equation of `A`.
* The instance `AlgebraicGeometry.IsVariety.toIsIntegral` is erased only around the main
  statement; the helpers are proved with it in place.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Pointwise

universe u

namespace Proof_lem_fourfold_adjoint_ideal_operations

open MMP.Mori MMP.Fourfold

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

/-- Adding a `ℚ`-divisor `D` with a Cartier multiple `D₀ = mD` lowers a log discrepancy by
`1/m` times the coefficient of the pull-back of `D₀`. -/
private theorem isLogDiscrepancy_add_of_zsmul {n : ℕ} {B : RDivisor X} {F : DivisorOver k sX}
    {a : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B F a) {D : QDivisor X} {m : ℕ}
    (hm : 0 < m) {D₀ : Divisor X} (hD₀ : Divisor.toQDivisor D₀ = (m : ℤ) • D)
    (hD₀c : D₀.IsCartier) :
    haveI := F.isLocallyNoetherian
    haveI := F.isNormal
    ∀ (D₀' : Divisor F.Y) (hCs : ∀ Z : irreducibleComponents F.Y,
        F.f (componentGenericPoint F.Y Z) ∉ D₀.supp), D₀.IsPullback F.f hCs D₀' →
      MMP.Intersection.IsLogDiscrepancy sX n (B + QDivisor.toRDivisor D) F
        (a - (D₀'.coeff F.E : ℝ) / m) := by
  intro D₀' hCs hpb
  have h1 := isLogDiscrepancy_add_smul h hD₀c (1 / (m : ℝ)) D₀' hCs hpb
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have e : B + (1 / (m : ℝ)) • Divisor.toRDivisor D₀ = B + QDivisor.toRDivisor D := by
    congr 1
    refine Finsupp.ext fun Γ => ?_
    have h2 := congrArg (fun G : QDivisor X => G.coeff Γ) hD₀
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast] at h2
    have h3 : ((D₀.coeff Γ : ℤ) : ℝ) = m * ((D.coeff Γ : ℚ) : ℝ) := by exact_mod_cast h2
    change DivisorWithCoeffs.coeff ((1 / (m : ℝ)) • Divisor.toRDivisor D₀) Γ =
      DivisorWithCoeffs.coeff (QDivisor.toRDivisor D) Γ
    rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor,
      smul_eq_mul, h3]
    field_simp
  rw [e] at h1
  convert h1 using 1
  ring

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

/-- The pull-back of a Cartier divisor whose support misses the centre of `F` has coefficient
zero along `F`. -/
private theorem coeff_isPullback_eq_zero {F : DivisorOver k sX} {C : Divisor X}
    (hC : C.IsCartier) (hx : F.f F.E.genericPoint ∉ C.supp) :
    haveI := F.isLocallyNoetherian
    haveI := F.isNormal
    ∀ (C' : Divisor F.Y) (hCs : ∀ Z : irreducibleComponents F.Y,
        F.f (componentGenericPoint F.Y Z) ∉ C.supp), C.IsPullback F.f hCs C' →
      C'.coeff F.E = 0 := by
  intro C' hCs hC'
  have := F.isIntegral
  have := F.isLocallyNoetherian
  have := F.isNormal
  have := F.isDominant
  have h0 : ∀ Γ : MMP.Mori.PrimeDivisor X, F.f F.E.genericPoint ∈ Γ.support →
      C.coeff Γ = 0 := fun Γ hΓ => by
    by_contra hne
    exact hx (DivisorWithCoeffs.support_subset_supp hne hΓ)
  have h1 := coeff_isPullback_nonneg hC (fun Γ hΓ => (h0 Γ hΓ).ge) C' hCs hC'
  have hn := hC'.zsmul hC (-1)
    (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp F.f _)
  have h2 := coeff_isPullback_nonneg (F := F) (hC.zsmul (-1)) (fun Γ hΓ => by
      simp [DivisorWithCoeffs.coeff_smul, h0 Γ hΓ]) _ _ hn
  rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul] at h2
  omega

/-- The inclusion of an open subscheme `U` is biregular over `U`. -/
private theorem isBiregular_ι_self {W : Scheme.{u}} (U : W.Opens) : IsBiregular U.ι U := by
  have h1 : U.ι ∣_ U = (U.ι ⁻¹ᵁ U).ι := by
    rw [← cancel_mono U.ι, morphismRestrict_ι]
  change IsIso (U.ι ∣_ U)
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
  have hPmem : P.genericPoint ∈ P.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
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

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
open Classical in
/-- An irreducible closed set `Z = closure {x}` is a stratum of a reduced snc divisor `Δ` when the
components of `Δ` containing `Z` number at least the codimension of `x`. -/
private theorem isSNCStratum_of_le_card {Δ : Divisor X} (hΔ : IsReducedSNC sX Δ) {Z : Set X}
    {x : X} (hZx : Z = closure {x}) {m₀ : ℕ}
    (hcx : Order.coheight x = m₀) (hcJ : m₀ ≤ (sncIndexSet Δ Z).card) : IsSNCStratum Δ Z := by
  have hZ : IsIrreducible Z := hZx ▸ isIrreducible_singleton.closure
  set J := sncIndexSet Δ Z
  have hxZ : x ∈ Z := by
    rw [hZx]
    exact subset_closure rfl
  refine ⟨sncIndexSet Δ Z, Finset.filter_subset _ _, ⟨hZ, ?_⟩, ?_⟩
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
    have hxw : w ⤳ x := hw.specializes (subset_closure (hZT' hxZ))
    have hwmem : w ∈ closure T' := hw.mem
    obtain ⟨mw, zw, jw, hzw, hjw, -⟩ := hΔ.2.2 w
    have hJw : J.card ≤ mw := by
      let ι : J → Fin mw := fun E => jw ⟨E.1, (Finset.mem_filter.1 E.2).1,
        Set.mem_iInter₂.1 (hWsub hwmem) E.1 E.2⟩
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
    have hcl : closure T' = (Z : Set X) := by
      rw [← hw.def, hwx, hZx]
    exact (subset_closure).trans hcl.le

open Classical in
/-- **Zero places of a reduced snc pair avoid closed sets containing no stratum.** If `Δ` is a
reduced snc divisor on a smooth variety and `a(F, X, Δ) = 0`, then the generic point of the centre
of `F` lies outside every closed set containing no stratum of `Δ`. -/
private theorem notMem_of_isLogDiscrepancy_eq_zero [IsAlgClosed k] [CharZero k]
    (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) {Δ : Divisor X}
    (hΔ : IsReducedSNC sX Δ) {T : Set X} (hT : IsClosed T) (hns : ContainsNoStratum Δ T)
    {n : ℕ} {F : DivisorOver k sX}
    (h0 : MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) F 0) :
    F.f F.E.genericPoint ∉ T := by
  haveI : MMP.Mori.IsVariety k sX := hX.1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI hF : IsProper F.f := h0.2.1
  set x := F.f F.E.genericPoint
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
  have hxZ : x ∈ (Z : Set X) := by rw [hZx]; exact subset_closure rfl
  have hsuppZ : ∀ E : MMP.Mori.PrimeDivisor X, x ∈ E.support → (Z : Set X) ⊆ E.support := by
    intro E hxE
    rw [hZx, AlgebraicGeometry.PrimeDivisor.support_eq_closure E]
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure E] at hxE
    exact closure_minimal (Set.singleton_subset_iff.mpr hxE) isClosed_closure
  set U := sncComplement Δ (Z : Set X)
  have hxU : x ∈ U := by
    change x ∈ (sncComplement Δ (Z : Set X) : Set X)
    simp only [sncComplement, TopologicalSpace.Opens.coe_mk, Set.mem_compl_iff, Set.mem_iUnion,
      Finset.mem_filter, not_exists, not_and]
    exact fun E hE hxE => hE.2 (hsuppZ E hxE)
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  obtain ⟨hYU, hfU, E', -, hvU, hiff⟩ :=
    MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff hPW F U ⟨x, hxZ, hxU⟩
  have hcU := (hiff c).1 hc
  have hpU : IsProper (F.f ∣_ U) := inferInstance
  have hLU := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hcU hpU
  rw [toRDivisor_restrictOpen_sncComplement hΔ.1, ← hc1] at hLU
  have hcen : MMP.Intersection.IsCentre k sX F.valuation Z := ⟨F, hF, rfl, rfl⟩
  have he : IsReducedSNCDiscrepancy sX Δ F.valuation 0 :=
    ⟨hX.1, hsm, hΔ.1, hΔ.2, Z, hcen, ⟨⟨x, hxU⟩⟩, n, _, hpU, hvU, hLU⟩
  obtain ⟨m₀, z₀, j₀, hz₀, -, -⟩ := hΔ.2.2 x
  have hcx : Order.coheight x = m₀ := by
    exact_mod_cast (ringKrullDim_stalk_eq_coheight x).symm.trans hz₀.2
  have hc₀ : codimension Z = m₀ := by
    rw [hZdef, MMP.Positivity.DivisorOver.codimension_center, hcx]
  have hsub := IsReducedSNCDiscrepancy.sub_card_sncIndexSet_le he hcen hc₀
  set J := sncIndexSet Δ (Z : Set X)
  have hcJ : m₀ ≤ J.card := by exact_mod_cast (show (m₀ : ℝ) ≤ J.card by linarith)
  intro hxT
  refine hns _ (isSNCStratum_of_le_card hΔ hZx hcx hcJ) ?_
  rw [hZx]
  exact hT.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hxT)

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

/-- **Zero places see no `D`.** If `a(F, X, Δ) = 0` for the reduced snc `Δ` and `D` contains no
stratum of `Δ`, then `a(F, X, Δ + D) = 0`. -/
private theorem eq_zero_of_isLogDiscrepancy_eq_zero [IsAlgClosed k] [CharZero k]
    (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) {Δ : Divisor X}
    (hΔ : IsReducedSNC sX Δ) {D : QDivisor X} (hns : ContainsNoStratum Δ D.supp) {n : ℕ}
    {F : DivisorOver k sX} {a : ℝ}
    (h0 : MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) F 0)
    (ha : MMP.Intersection.IsLogDiscrepancy sX n
      (Divisor.toRDivisor Δ + QDivisor.toRDivisor D) F a) : a = 0 := by
  have hx := notMem_of_isLogDiscrepancy_eq_zero hX hsm hΔ (DivisorWithCoeffs.supp D).isClosed
    hns h0
  obtain ⟨m, hm, D₀, hD₀, hD₀c⟩ := (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm D).exists_pos
  have := F.isLocallyNoetherian
  have := F.isNormal
  have := F.isIntegral
  have := F.isBirationalMorphism.isDominant
  have : CompactSpace F.Y := (F.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  have hB := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp F.f D₀
  obtain ⟨D₀', hD₀'⟩ := hD₀c.exists_isPullback hB
  have hsupp : D₀.supp = D.supp :=
    QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hD₀
  have hz := coeff_isPullback_eq_zero hD₀c (by rwa [hsupp]) D₀' hB hD₀'
  have h1 := isLogDiscrepancy_add_of_zsmul h0 hm hD₀ hD₀c D₀' hB hD₀'
  rw [hz, show (0 : ℝ) - ((0 : ℤ) : ℝ) / m = 0 by simp] at h1
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha h1

end Toolkit

/-! ### The arithmetic of the comparison on a log resolution -/

/-- If `A₀ = t + ∑ a₀ᵢ eᵢ = 0` and `A = t + ∑ αᵢ eᵢ` with `t, eᵢ ≥ 0`, `a₀ᵢ ∈ ℕ`, and `αᵢ`, `Gᵢ`
vanishing whenever `a₀ᵢ = 0`, then `∑ Gᵢ eᵢ = 0` and `A = 0`. -/
private theorem sum_mul_eq_zero_and_eq_zero_of_eq_zero {ι : Type*} (s : Finset ι) (a₀ : ι → ℕ)
    (α : ι → ℝ) (e G : ι → ℤ) (t : ℕ) {A₀ A : ℝ} (he : ∀ i ∈ s, 0 ≤ e i)
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
  exact ⟨by exact_mod_cast hS, by simp [hA, ht0, Finset.sum_eq_zero fun i hi => (hGe i hi).2]⟩

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
  · obtain ⟨hS, hA'⟩ := sum_mul_eq_zero_and_eq_zero_of_eq_zero s a₀ α e G t he hz hGz hA₀ hA hA0
    rw [if_pos hA0, hS, hA']
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
  · rw [hfa]; exact (f.hom a).2
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
private theorem valuationOver_algebraMap_stalk_le_one (P : MMP.Mori.PrimeDivisor X')
    (a : X.presheaf.stalk (μ P.genericPoint)) :
    P.valuationOver μ (algebraMap _ X.functionField a) ≤ 1 := by
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply,
    MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff,
    MMP.Mori.functionFieldMap_algebraMap_stalk]
  exact ⟨_, rfl⟩

/-- A non-unit of the stalk of `X` at the centre `μ(η_P)` has `v_P(μ^* ·) < 1`. -/
private theorem valuationOver_algebraMap_stalk_lt_one (P : MMP.Mori.PrimeDivisor X')
    (a : X.presheaf.stalk (μ P.genericPoint)) (ha : ¬ IsUnit a) :
    P.valuationOver μ (algebraMap _ X.functionField a) < 1 := by
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.functionFieldMap_algebraMap_stalk,
    MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff]
  exact (IsLocalRing.mem_maximalIdeal _).mpr fun h => ha (isUnit_of_map_unit _ _ h)

/-- In `ℤᵐ⁰`, an element below `1` is at most `exp (-1)`. -/
private theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) :
    x ≤ WithZero.exp (-1) :=
  (WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero).1
    (by rwa [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero])

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
    exact (mul_le_of_le_one_left' (valuationOver_algebraMap_stalk_le_one μ P _)).trans (ha P hP)

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
  · refine (mul_le_of_le_one_left'
      (pow_le_one' (valuationOver_algebraMap_stalk_le_one μ P _) m)).trans ?_
    have h2 : X.presheaf.germ _ _ hP y = X.presheaf.germ _ _ hP f ^ n *
        X.presheaf.germ _ _ hf b := by
      rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (X.basicOpen_le f)) _ hf,
        ← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (X.basicOpen_le f)) _ hf,
        ← map_pow, ← map_mul]
      exact congrArg _ hy
    rw [h2, map_mul, Valuation.map_mul, map_pow, Valuation.map_pow]
    exact (mul_le_of_le_one_left'
      (pow_le_one' (valuationOver_algebraMap_stalk_le_one μ P _) n)).trans (hb P hf)
  · have hle := le_exp_neg_one_of_lt_one
      (valuationOver_algebraMap_stalk_lt_one μ P (X.presheaf.germ _ _ hP f)
        (by rwa [← X.mem_basicOpen f _ hP]))
    refine (mul_le_of_le_one_right' (valuationOver_algebraMap_stalk_le_one μ P _)).trans
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

/-! ### The adjoint ideal by orders along all divisors over `X` -/

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

/-- The sections over `U` of `𝒥_{Δ,D}` described valuatively: the rational functions `g` with
`v_F(g) ≤ exp (⌈a(F, X, Δ + D)⌉ - 1 + [a(F, X, Δ) = 0])` for every divisor `F` over `X` whose
centre lies in `U`. -/
private def adjointSet (Δ : Divisor X) (D : QDivisor X) (U : X.Opens) : Set X.functionField :=
  {g | (U = ⊥ → g = 0) ∧ ∀ (n : ℕ) (F : DivisorOver k sX) (a₀ a : ℝ),
    F.f F.E.genericPoint ∈ U →
    MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) F a₀ →
    MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ + QDivisor.toRDivisor D) F a →
    F.valuation g ≤ WithZero.exp (⌈a⌉ - 1 + if a₀ = 0 then 1 else 0)}

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
  have hPmem : P.genericPoint ∈ P.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hne : ¬ FP.IsExceptional := fun hexc' =>
    hexc (MMP.Positivity.support_subset_exceptionalSet P hexc' hPmem)
  obtain ⟨Q, hQc, hQd⟩ := MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hPW FP hne
  have hηQ : μ P.genericPoint = Q.genericPoint := by
    have e1 := FP.center_eq_closure_genericPoint
    rw [hQc, AlgebraicGeometry.PrimeDivisor.support_eq_closure Q] at e1
    exact (inseparable_iff_closure_eq.mpr e1.symm).eq
  have hQmem : Q.genericPoint ∈ Q.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
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

/-- **Log discrepancy one off the snc divisor of a log resolution.** Let `μ : Y → X` be a proper
birational model and `s` the components of `Exc(μ) ∪ μ⁻¹ Supp(Δ + D)`, for `Δ` reduced and `D`
effective. A prime divisor `P ∉ s` of `Y` has log discrepancy `1` for `(X, Δ)` and `(X, Δ + D)`. -/
private theorem isLogDiscrepancy_one_of_notMem_finset [PerfectField k] (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} (hn : topologicalKrullDim X = n) {Δ : Divisor X}
    (hΔ : MMP.Intersection.IsReducedEffective Δ) {D : QDivisor X} (hD0 : ∀ P, 0 ≤ D.coeff P)
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {μ : Y ⟶ X}
    (hY : IsNormalVariety k (μ ≫ sX)) (hμ : IsBirationalMorphism μ) (hμp : IsProper μ)
    {s : Finset (MMP.Mori.PrimeDivisor Y)}
    (hs : (⋃ E ∈ s, E.support) = ((exceptionalSet μ ⊔ (DivisorWithCoeffs.supp
      (QDivisor.toRDivisor (Divisor.toQDivisor Δ + D))).preimage μ.continuous : Closeds Y) : Set Y))
    {P : MMP.Mori.PrimeDivisor Y} (hPs : P ∉ s) :
    MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) ⟨Y, μ, hY, hμ, P⟩ 1 ∧
      MMP.Intersection.IsLogDiscrepancy sX n
        (Divisor.toRDivisor Δ + QDivisor.toRDivisor D) ⟨Y, μ, hY, hμ, P⟩ 1 := by
  have hnot : P.genericPoint ∉ (⋃ E ∈ s, E.support) := by
    intro hz
    obtain ⟨E', hE's, hPE'⟩ := Set.mem_iUnion₂.mp hz
    exact hPs (by rwa [← MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hPE'])
  rw [hs, Closeds.coe_sup, Set.mem_union, not_or] at hnot
  obtain ⟨hexc, hsupp⟩ := hnot
  have hsuppΔ : μ P.genericPoint ∉ (DivisorWithCoeffs.supp
      (QDivisor.toRDivisor (Divisor.toQDivisor Δ)) : Set X) := by
    intro hmem
    apply hsupp
    obtain ⟨Γ', hΓ', hxΓ'⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨Γ', ?_, hxΓ'⟩
    rw [QDivisor.coeff_toRDivisor, Divisor.coeff_toQDivisor] at hΓ'
    rw [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor]
    have : (0 : ℝ) ≤ ((D.coeff Γ' : ℚ) : ℝ) := by exact_mod_cast hD0 Γ'
    rcases hΔ Γ' with h | h
    · rw [h] at hΓ'; simp at hΓ'
    · rw [h]; push_cast; linarith
  have h0 := isLogDiscrepancy_one_of_notMem sX hX hsm hn hY hμ hμp _ P hexc hsuppΔ
  have h1 := isLogDiscrepancy_one_of_notMem sX hX hsm hn hY hμ hμp _ P hexc hsupp
  rw [QDivisor.toRDivisor_toQDivisor] at h0
  rw [map_add, QDivisor.toRDivisor_toQDivisor] at h1
  exact ⟨h0, h1⟩

/-- The coefficient of the zero log discrepancy divisor `Γ` along `P` is `[a(P, X, Δ) = 0]`. -/
private theorem coeff_eq_ite_of_isZeroLogDiscrepancyDivisor [PerfectField k] {Δ : Divisor X}
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {μ : Y ⟶ X}
    {hY : IsNormalVariety k (μ ≫ sX)} {hμ : IsBirationalMorphism μ} {Γ : Divisor Y}
    (hΓ : IsZeroLogDiscrepancyDivisor sX μ hY hμ Δ Γ) {n a₀ : ℕ} {P : MMP.Mori.PrimeDivisor Y}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) ⟨Y, μ, hY, hμ, P⟩ a₀) :
    Γ.coeff P = if ((a₀ : ℕ) : ℝ) = 0 then 1 else 0 := by
  rcases hΓ.1 P with h0 | h1
  · rw [h0]
    split_ifs with ha0
    · have : Γ.coeff P = 1 := (hΓ.2 P).2 ⟨n, by rwa [ha0] at ha⟩
      omega
    · rfl
  · rw [h1]
    split_ifs with ha0
    · rfl
    · obtain ⟨n', h'⟩ := (hΓ.2 P).1 h1
      exact absurd (MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha h') ha0

/-- On a smooth variety, the log discrepancies of a reduced snc divisor are natural numbers. -/
private theorem exists_nat_isLogDiscrepancy_of_isReducedSNC [IsAlgClosed k] [CharZero k]
    {Δ : Divisor X} (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) (hΔ : IsReducedSNC sX Δ) (F : DivisorOver k sX)
    (hF : IsProper F.f) :
    ∃ a₀ : ℕ, MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) F a₀ := by
  have : MMP.Mori.IsVariety k sX := hX.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨a, ha⟩ := exists_isLogDiscrepancy hX hsm hn (Divisor.toQDivisor Δ) F hF
  rw [QDivisor.toRDivisor_toQDivisor] at ha
  obtain ⟨a₀, rfl⟩ :=
    MMP.Intersection.IsLogDiscrepancy.exists_nat_eq_of_isSNC sX hX.1 hsm hΔ.1 hΔ.2 ha
  exact ⟨a₀, ha⟩

/-- On a log resolution `μ : Y → X` of `Δ + D`, the coefficient of
`E - ⌊μ^*D⌋` along a prime divisor `P` of `Y` is `⌈a(P, X, Δ + D)⌉ - 1 + [a(P, X, Δ) = 0]`. -/
private theorem exists_isLogDiscrepancy_coeff_eq [IsAlgClosed k] [CharZero k] {Δ : Divisor X}
    {D : QDivisor X} (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    (hΔ : IsReducedSNC sX Δ) (hDns : ContainsNoStratum Δ D.supp)
    (hD0 : ∀ P, 0 ≤ D.coeff P) {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {μ : Y ⟶ X} (hlog : IsLogResolution sX (Divisor.toQDivisor Δ + D) μ)
    (hY : IsNormalVariety k (μ ≫ sX)) (hμ : IsBirationalMorphism μ)
    (hD : ∀ Z : irreducibleComponents Y, μ (componentGenericPoint Y Z) ∉ D.supp)
    {Γ E : Divisor Y} {F : QDivisor Y} (hΓ : IsZeroLogDiscrepancyDivisor sX μ hY hμ Δ Γ)
    (hE : IsAdjointDiscrepancyDivisor sX μ hY hμ Δ Γ E) (hF : D.IsPullback μ hD F)
    {s : Finset (MMP.Mori.PrimeDivisor Y)}
    (hs : (⋃ E ∈ s, E.support) = ((exceptionalSet μ ⊔ (DivisorWithCoeffs.supp
      (QDivisor.toRDivisor (Divisor.toQDivisor Δ + D))).preimage μ.continuous : Closeds Y) : Set Y))
    (n : ℕ) (hn : topologicalKrullDim X = n) (P : MMP.Mori.PrimeDivisor Y) :
    ∃ (a₀ : ℕ) (α : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) ⟨Y, μ, hY, hμ, P⟩ a₀ ∧
      MMP.Intersection.IsLogDiscrepancy sX n
        (Divisor.toRDivisor Δ + QDivisor.toRDivisor D) ⟨Y, μ, hY, hμ, P⟩ α ∧
      (E - MMP.Intersection.WeilRDivisor.roundDown (QDivisor.toRDivisor F)).coeff P =
        ⌈α⌉ - 1 + (if ((a₀ : ℕ) : ℝ) = 0 then 1 else 0) ∧
      (a₀ = 0 → α = 0) ∧ (P ∉ s → a₀ = 1 ∧ α = 1) := by
  classical
  haveI : MMP.Mori.IsVariety k sX := hX.1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsProper μ := hlog.isProper
  haveI : MMP.Mori.IsVariety k (μ ≫ sX) := hY.1
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (μ ≫ sX)
  haveI : LocallyOfFiniteType (μ ≫ sX) := hY.1.toLocallyOfFiniteType
  obtain ⟨m, hm, D₀, hD₀, hD₀c⟩ := (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm D).exists_pos
  set FP : DivisorOver k sX := ⟨Y, μ, hY, hμ, P⟩ with hFPdef
  have hFPp : IsProper FP.f := hlog.isProper
  obtain ⟨n', a', hla', hEP⟩ := hE P
  obtain ⟨a₀, ha₀r⟩ := exists_nat_isLogDiscrepancy_of_isReducedSNC sX hX hsm hn hΔ FP hFPp
  have ha' : a' = a₀ := MMP.Threefold.Bridges.IsLogDiscrepancy.unique hla' ha₀r
  obtain ⟨D₀', hD₀'eq, hD₀'pb⟩ := hF m hm D₀ hD₀ hD₀c
  have hα := isLogDiscrepancy_add_of_zsmul ha₀r hm hD₀ hD₀c D₀' _ hD₀'pb
  have hFP : ((D₀'.coeff P : ℤ) : ℝ) / m = ((F.coeff P : ℚ) : ℝ) := by
    have h1 := congrArg (fun G : QDivisor Y => G.coeff P) hD₀'eq
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast] at h1
    have h' : ((D₀'.coeff P : ℤ) : ℝ) = m * ((F.coeff P : ℚ) : ℝ) := by exact_mod_cast h1
    rw [h']
    field_simp
  change MMP.Intersection.IsLogDiscrepancy sX n _ FP (_ - ((D₀'.coeff P : ℤ) : ℝ) / m) at hα
  rw [hFP] at hα
  refine ⟨a₀, (a₀ : ℝ) - F.coeff P, ha₀r, hα, ?_, ?_, ?_⟩
  · have hΓP := coeff_eq_ite_of_isZeroLogDiscrepancyDivisor sX hΓ ha₀r
    have hE' : E.coeff P = (a₀ : ℤ) - 1 + Γ.coeff P := by
      rw [ha'] at hEP
      exact_mod_cast hEP
    have hfl : ⌊((F.coeff P : ℚ) : ℝ)⌋ = (a₀ : ℤ) - ⌈(a₀ : ℝ) - F.coeff P⌉ := by
      have e : ((F.coeff P : ℚ) : ℝ) = ((a₀ : ℤ) : ℝ) + -((a₀ : ℝ) - F.coeff P) := by
        push_cast; ring
      conv_lhs => rw [e]
      rw [Int.floor_intCast_add, Int.floor_neg]
      ring
    rw [DivisorWithCoeffs.coeff_sub, MMP.Intersection.WeilRDivisor.coeff_roundDown,
      QDivisor.coeff_toRDivisor, hfl, hE', hΓP]
    split_ifs <;> ring
  · intro h0
    subst h0
    exact eq_zero_of_isLogDiscrepancy_eq_zero hX hsm hΔ hDns (by simpa using ha₀r) hα
  · intro hPs
    obtain ⟨h0, h1⟩ := isLogDiscrepancy_one_of_notMem_finset sX hX hsm hn hΔ.1 hD0 hY hμ
      hlog.isProper hs hPs
    exact ⟨by exact_mod_cast MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha₀r h0,
      MMP.Threefold.Bridges.IsLogDiscrepancy.unique hα h1⟩

/-- On a smooth variety, if `ord_Γ(g) ≥ -coeff_Γ(G)` along every prime divisor `Γ` through the
centre of `F` and `G` is supported on `s`, then `v_F(g) ≤ exp (∑_{P ∈ s} coeff_P(G) e_P)`, where
`e_P` is the coefficient of the pull-back of `P` along `F`. -/
private theorem valuation_le_exp_sum [PerfectField k] (hsm : IsSmoothScheme sX) {n : ℕ}
    {B : RDivisor X} {F : DivisorOver k sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n B F a)
    (s : Finset (MMP.Mori.PrimeDivisor X)) (e : MMP.Mori.PrimeDivisor X → ℤ)
    (he : haveI := F.isLocallyNoetherian
      haveI := F.isNormal
      ∀ P ∈ s, ∀ (P' : Divisor F.Y) (hB : ∀ Z : irreducibleComponents F.Y,
          F.f (componentGenericPoint F.Y Z) ∉
            DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor X)),
        Divisor.IsPullback F.f (Finsupp.single P 1 : Divisor X) hB P' → P'.coeff F.E = e P)
    {G : Divisor X} (hG0 : ∀ Q ∉ s, G.coeff Q = 0) {g : X.functionField}
    (hg : ∀ Γ : MMP.Mori.PrimeDivisor X, F.f F.E.genericPoint ∈ Γ.support →
      Γ.divisorialValuation g ≤ WithZero.exp (G.coeff Γ)) :
    F.valuation g ≤ WithZero.exp (∑ P ∈ s, G.coeff P * e P) := by
  have := F.isLocallyNoetherian
  have := F.isNormal
  have := F.isIntegral
  have := F.isBirationalMorphism.isDominant
  have : CompactSpace F.Y := (F.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  have hGcart : Divisor.IsCartier (-G) := MMP.Fourfold.isCartier_of_isSmoothScheme hsm _
  have hBG := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp F.f (-G)
  obtain ⟨G', hG'⟩ := hGcart.exists_isPullback hBG
  have hR := valuation_le_exp_of_isPullback (F := F) hGcart (g := g)
    (fun Γ hΓ => by
      rw [DivisorWithCoeffs.coeff_neg, neg_neg]
      exact hg Γ hΓ) G' hBG hG'
  have hl1 := isLogDiscrepancy_add_smul h hGcart (1 : ℝ) G' hBG hG'
  have hl2 := isLogDiscrepancy_add_sum hsm h s (fun P => -(G.coeff P : ℝ)) e he
  have hbG : (1 : ℝ) • Divisor.toRDivisor (-G) =
      ∑ P ∈ s, (-(G.coeff P : ℝ)) • Divisor.toRDivisor (Finsupp.single P 1 : Divisor X) := by
    refine (sum_smul_single_eq s _ _ (fun Q _ => ?_) (fun Q hQ => ?_)).symm
    · rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_neg]
      simp
    · rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_neg,
        hG0 Q hQ]
      simp
  rw [hbG] at hl1
  have hGe : (G'.coeff F.E : ℝ) = -∑ P ∈ s, (G.coeff P : ℝ) * e P := by
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.unique hl1 hl2
    simp only [one_mul, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add] at this
    linarith
  have hGe' : G'.coeff F.E = -∑ P ∈ s, G.coeff P * e P := by exact_mod_cast hGe
  rwa [hGe', neg_neg] at hR

/-- A log discrepancy of `(X, Δ)` along a divisor `F₀` over `X` is the log discrepancy, with
respect to the crepant boundary of `(X, Δ)` on a model `Y`, of a proper divisor `F'` over `Y` with
the same valuation. -/
private theorem isLogDiscrepancy_of_isCrepantBoundary [IsAlgClosed k] [CharZero k] {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} (hP : MMP.Mori.IsPair sX Δ)
    (hK : K.IsCanonicalDivisor sX n) {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {μ : Y ⟶ X} [IsDominant μ] (hY : IsNormalVariety k (μ ≫ sX))
    (hμ : IsBirationalMorphism μ) {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (μ ≫ sX) n)
    {B : QDivisor Y}
    (hB : IsCrepantBoundary sX n K Δ μ hY hμ B) {F₀ : DivisorOver k sX}
    {F' : DivisorOver k (μ ≫ sX)} (hF'p : IsProper F'.f)
    (hval : F₀.valuation = Valuation.comap (functionFieldMap μ) F'.valuation) {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Δ) F₀ a) :
    MMP.Intersection.IsLogDiscrepancy (μ ≫ sX) n (QDivisor.toRDivisor B) F' a := by
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK F₀
  rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha]
  exact MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy
    (((MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP μ hY hμ hK hKY (Or.inl hB)).2 F' F₀ hval
      c).2 hc) hF'p

/-- The crepant boundary of `(X, Δ)` on a proper model has coefficient `1 - a(Q, X, Δ)` along each
prime divisor `Q` of the model. -/
private theorem coeff_isCrepantBoundary [IsAlgClosed k] [CharZero k] {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {μ : Y ⟶ X} (hμp : IsProper μ) (hY : IsNormalVariety k (μ ≫ sX))
    (hμ : IsBirationalMorphism μ) {B : QDivisor Y} (hB : IsCrepantBoundary sX n K Δ μ hY hμ B)
    {Q : MMP.Mori.PrimeDivisor Y} {α : ℝ}
    (hα : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Δ) ⟨Y, μ, hY, hμ, Q⟩ α) :
    ((B.coeff Q : ℚ) : ℝ) = 1 - α := by
  have := MMP.Threefold.Bridges.IsLogDiscrepancy.unique hα
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hB Q) hμp)
  push_cast at this
  linarith

/-- On a smooth variety, if `B` has coefficient `1 - β_P` along every prime divisor `P`, with
`β_P = 1` off `s`, then `a(F, B) = a(F, ∑_{P ∈ s} P) + ∑_{P ∈ s} β_P e_P`. -/
private theorem eq_add_sum_of_isLogDiscrepancy [PerfectField k] (hsm : IsSmoothScheme sX)
    {n : ℕ} {F : DivisorOver k sX} {s : Finset (MMP.Mori.PrimeDivisor X)} {t : ℝ}
    (htr : MMP.Intersection.IsLogDiscrepancy sX n
      (Divisor.toRDivisor (MMP.Intersection.reducedDivisorOf s)) F t)
    (e : MMP.Mori.PrimeDivisor X → ℤ)
    (he : haveI := F.isLocallyNoetherian
      haveI := F.isNormal
      ∀ P ∈ s, ∀ (P' : Divisor F.Y) (hB : ∀ Z : irreducibleComponents F.Y,
          F.f (componentGenericPoint F.Y Z) ∉
            DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor X)),
        Divisor.IsPullback F.f (Finsupp.single P 1 : Divisor X) hB P' → P'.coeff F.E = e P)
    (β : MMP.Mori.PrimeDivisor X → ℝ) {B : QDivisor X}
    (hB : ∀ Q, ((B.coeff Q : ℚ) : ℝ) = 1 - β Q) (hout : ∀ Q ∉ s, β Q = 1) {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) F a) :
    a = t + ∑ P ∈ s, β P * e P := by
  have hb := toRDivisor_add_sum_eq s (fun P => -β P) (QDivisor.toRDivisor B)
    (fun Q _ => by rw [QDivisor.coeff_toRDivisor, hB Q]; ring)
    (fun Q hQ => by rw [QDivisor.coeff_toRDivisor, hB Q, hout Q hQ]; simp)
  have hsum := isLogDiscrepancy_add_sum hsm htr s (fun P => -β P) e he
  rw [hb] at hsum
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha hsum]
  simp only [neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]

/-- On a smooth variety, the pull-back of each prime divisor `P` along a divisor `F` over it has a
nonnegative coefficient `e_P` along `F`. -/
private theorem exists_coeff_isPullback (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    (F : DivisorOver k sX) :
    ∃ e : MMP.Mori.PrimeDivisor X → ℤ, (∀ P, 0 ≤ e P) ∧
      haveI := F.isLocallyNoetherian
      haveI := F.isNormal
      ∀ P, ∀ (P' : Divisor F.Y) (hB : ∀ Z : irreducibleComponents F.Y,
          F.f (componentGenericPoint F.Y Z) ∉
            DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor X)),
        Divisor.IsPullback F.f (Finsupp.single P 1 : Divisor X) hB P' → P'.coeff F.E = e P := by
  classical
  haveI : MMP.Mori.IsVariety k sX := hX.1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have := F.isLocallyNoetherian
  have := F.isNormal
  have := F.isIntegral
  have := F.isBirationalMorphism.isDominant
  have : CompactSpace F.Y := (F.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  have hcart : ∀ P : MMP.Mori.PrimeDivisor X,
      Divisor.IsCartier (Finsupp.single P (1 : ℤ) : Divisor X) := fun P =>
    MMP.Fourfold.isCartier_of_isSmoothScheme hsm _
  choose P' hP' using fun P : MMP.Mori.PrimeDivisor X => (hcart P).exists_isPullback
    (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp F.f
      (Finsupp.single P (1 : ℤ) : Divisor X))
  refine ⟨fun P => (P' P).coeff F.E, fun P => coeff_isPullback_nonneg (hcart P) (fun Γ _ => by
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]; split_ifs <;> simp) _ _ (hP' P),
    fun P Q' hB hQ' => by rw [hQ'.eq (hcart P) (hP' P)]⟩

/-- On a smooth model `μ : Y → X` of a smooth variety, the pair `(X, Δ)` has a crepant boundary
`B` on `Y`, and a divisor over `X` realised on `Y` has the same log discrepancy for `(Y, B)`. -/
private theorem exists_isCrepantBoundary_isLogDiscrepancy [IsAlgClosed k] [CharZero k]
    (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {μ : Y ⟶ X} [IsDominant μ] [IsProper μ] (hY : IsNormalVariety k (μ ≫ sX))
    (hμ : IsBirationalMorphism μ) (hsmY : IsSmoothScheme (μ ≫ sX))
    (hnY : topologicalKrullDim Y = n) (Δ : QDivisor X) {F₀ : DivisorOver k sX}
    {F' : DivisorOver k (μ ≫ sX)} (hF'p : IsProper F'.f)
    (hval : F₀.valuation = Valuation.comap (functionFieldMap μ) F'.valuation) {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Δ) F₀ a) :
    ∃ B : QDivisor Y, (∃ K : Divisor X, IsCrepantBoundary sX n K Δ μ hY hμ B) ∧
      MMP.Intersection.IsLogDiscrepancy (μ ≫ sX) n (QDivisor.toRDivisor B) F' a := by
  have : MMP.Mori.IsVariety k sX := hX.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : MMP.Mori.IsVariety k (μ ≫ sX) := hY.1
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (μ ≫ sX)
  have : LocallyOfFiniteType (μ ≫ sX) := hY.1.toLocallyOfFiniteType
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme sX hsm hn
  obtain ⟨KY, hKY⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (μ ≫ sX) hsmY hnY
  have hP : MMP.Mori.IsPair sX Δ := ⟨hX, n, K, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩
  obtain ⟨B, hB⟩ := (MMP.Mori.IsPair.existsUnique_isCrepantBoundary hP hK μ hY hμ).1.exists
  exact ⟨B, ⟨K, hB⟩, isLogDiscrepancy_of_isCrepantBoundary sX hP hK hY hμ hKY hB hF'p hval ha⟩

/-- On a smooth variety, every divisor over it has a natural-number log discrepancy with respect
to the reduced divisor `∑_{P ∈ s} P` of an snc family `s`. -/
private theorem exists_nat_isLogDiscrepancy_reducedDivisorOf [IsAlgClosed k] [CharZero k]
    (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {s : Finset (MMP.Mori.PrimeDivisor X)}
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ s, Finsupp.single E (1 : ℤ)))
    (F : DivisorOver k sX) (hF : IsProper F.f) : ∃ t : ℕ, MMP.Intersection.IsLogDiscrepancy sX n
      (Divisor.toRDivisor (MMP.Intersection.reducedDivisorOf s)) F t := by
  have : MMP.Mori.IsVariety k sX := hX.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hTred : MMP.Intersection.IsReducedEffective (MMP.Intersection.reducedDivisorOf s) :=
    fun P => by rw [MMP.Intersection.coeff_reducedDivisorOf]; split_ifs <;> simp
  obtain ⟨tr, htr⟩ := exists_isLogDiscrepancy hX hsm hn
    (Divisor.toQDivisor (MMP.Intersection.reducedDivisorOf s)) F hF
  rw [QDivisor.toRDivisor_toQDivisor] at htr
  obtain ⟨t, rfl⟩ := MMP.Intersection.IsLogDiscrepancy.exists_nat_eq_of_isSNC sX hX.1 hsm hTred
    hsnc htr
  exact ⟨t, htr⟩

/-- A section of `μ_*𝒪_Y(G)` lies in `adjointSet`, when the coefficients of `G` along the prime
divisors of `Y` are `⌈a(P, X, Δ + D)⌉ - 1 + [a(P, X, Δ) = 0]`, and the prime divisors where these
log discrepancies differ from `1` form an snc divisor. -/
private theorem mem_adjointSet_of_mem_multiplierIdealSections [IsAlgClosed k] [CharZero k]
    {Δ : Divisor X} {D : QDivisor X} (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    (hΔ : IsReducedSNC sX Δ) (hDns : ContainsNoStratum Δ D.supp) {Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {μ : Y ⟶ X} [IsDominant μ]
    (hlog : IsLogResolution sX (Divisor.toQDivisor Δ + D) μ)
    (hY : IsNormalVariety k (μ ≫ sX)) (hμ : IsBirationalMorphism μ)
    {s : Finset (MMP.Mori.PrimeDivisor Y)}
    (hsnc : DivisorWithCoeffs.IsSNC (μ ≫ sX) (∑ E ∈ s, Finsupp.single E (1 : ℤ)))
    {G : Divisor Y} (hcoef : ∀ n : ℕ, topologicalKrullDim X = n → ∀ P : MMP.Mori.PrimeDivisor Y,
      ∃ (a₀ : ℕ) (α : ℝ),
        MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) ⟨Y, μ, hY, hμ, P⟩ a₀ ∧
        MMP.Intersection.IsLogDiscrepancy sX n
          (Divisor.toRDivisor Δ + QDivisor.toRDivisor D) ⟨Y, μ, hY, hμ, P⟩ α ∧
        G.coeff P = ⌈α⌉ - 1 + (if ((a₀ : ℕ) : ℝ) = 0 then 1 else 0) ∧
        (a₀ = 0 → α = 0) ∧ (P ∉ s → a₀ = 1 ∧ α = 1)) {U : X.Opens} {g : X.functionField}
    (hg : g ∈ MMP.Intersection.multiplierIdealSections μ G U) : g ∈ adjointSet sX Δ D U := by
  classical
  have : MMP.Mori.IsVariety k sX := hX.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsProper μ := hlog.isProper
  have : MMP.Mori.IsVariety k (μ ≫ sX) := hY.1
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (μ ≫ sX)
  have : LocallyOfFiniteType (μ ≫ sX) := hY.1.toLocallyOfFiniteType
  have hsmY : IsSmoothScheme (μ ≫ sX) := hlog.isSmoothScheme
  obtain ⟨hg0, hgP⟩ := hg
  refine ⟨fun hU => hg0 (by rw [hU]; rfl), fun n F₀ a₀ a hx ha₀ ha => ?_⟩
  rcases eq_or_ne g 0 with rfl | hgne
  · simp
  have hn := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha₀
  obtain ⟨F', hF'p, hval, hcen⟩ := exists_divisorOver_model hX.1 μ hlog.isProper hμ hY F₀
  set y := F'.f F'.E.genericPoint with hy
  have hyU : y ∈ μ ⁻¹ᵁ U := by
    change μ y ∈ U
    rwa [hcen]
  have hnY : topologicalKrullDim Y = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (μ ≫ sX) hμ).symm.trans
      hn
  obtain ⟨B₀, ⟨_, hB₀⟩, hY0⟩ := exists_isCrepantBoundary_isLogDiscrepancy sX hX hsm hn hY hμ
    hsmY hnY (Divisor.toQDivisor Δ) hF'p hval (by rwa [QDivisor.toRDivisor_toQDivisor])
  obtain ⟨B₁, ⟨_, hB₁⟩, hY1⟩ := exists_isCrepantBoundary_isLogDiscrepancy sX hX hsm hn hY hμ
    hsmY hnY (Divisor.toQDivisor Δ + D) hF'p hval
    (by rwa [map_add, QDivisor.toRDivisor_toQDivisor])
  obtain ⟨t, htr⟩ := exists_nat_isLogDiscrepancy_reducedDivisorOf (μ ≫ sX) hY hsmY hnY hsnc F' hF'p
  choose a₀P αP ha₀P hαP hGP hzP houtP using hcoef n hn
  obtain ⟨e, he0, he₁⟩ := exists_coeff_isPullback (μ ≫ sX) hY hsmY F'
  have he := fun P (_ : P ∈ s) => he₁ P
  have hA₀ : a₀ = t + ∑ P ∈ s, (a₀P P : ℝ) * e P :=
    eq_add_sum_of_isLogDiscrepancy (μ ≫ sX) hsmY htr e he (fun P => (a₀P P : ℝ))
      (fun Q => coeff_isCrepantBoundary sX hlog.isProper hY hμ hB₀
        (by rw [QDivisor.toRDivisor_toQDivisor]; exact ha₀P Q))
      (fun Q hQ => by rw [(houtP Q hQ).1, Nat.cast_one]) hY0
  have hA : a = t + ∑ P ∈ s, αP P * e P :=
    eq_add_sum_of_isLogDiscrepancy (μ ≫ sX) hsmY htr e he αP
      (fun Q => coeff_isCrepantBoundary sX hlog.isProper hY hμ hB₁
        (by rw [map_add, QDivisor.toRDivisor_toQDivisor]; exact hαP Q))
      (fun Q hQ => (houtP Q hQ).2) hY1
  have hG0 : ∀ Q ∉ s, G.coeff Q = 0 := fun Q hQ => by
    simp [hGP Q, (houtP Q hQ).1, (houtP Q hQ).2]
  have hR := valuation_le_exp_sum (μ ≫ sX) hsmY htr s e he hG0 (g := functionFieldMap μ g)
    fun Γ hΓ => hgP Γ ⟨y, hΓ, hyU⟩
  have hval' : F₀.valuation g = F'.valuation (functionFieldMap μ g) := by
    rw [hval]; rfl
  rw [hval']
  exact hR.trans (WithZero.exp_le_exp.mpr (sum_mul_le_ceil s a₀P αP e G.coeff t
    (fun P _ => he0 P) (fun P _ => hzP P) (fun P _ => hGP P) hA₀ hA))

/-- **The adjoint ideal is computed by orders along all divisors over `X`.** The sections of
`μ_*𝒪_Y(E - ⌊μ^*D⌋)` are the rational functions `g` with
`v_F(g) ≤ exp (⌈a(F, X, Δ + D)⌉ - 1 + [a(F, X, Δ) = 0])` for every divisor `F` over `X` centred
in the open set. -/
private theorem eq_adjointSet [IsAlgClosed k] [CharZero k] {Δ : Divisor X} {D : QDivisor X}
    {Y : Scheme.{u}} {μ : Y ⟶ X} {J : X.Opens → Set X.functionField}
    (h : IsReducedAdjointIdealOn sX Δ D μ J) : J = adjointSet sX Δ D := by
  obtain ⟨hX, hsm, hΔ, hD0, hDns, hlog, _, _, _, _, hY, hμ, hD, Γ, E, F, hΓ, hE, hF, rfl⟩ := h
  haveI : MMP.Mori.IsVariety k (μ ≫ sX) := hY.1
  haveI : LocallyOfFiniteType (μ ≫ sX) := hY.1.toLocallyOfFiniteType
  obtain ⟨s, hs, hsnc⟩ := exists_finset_of_isSNCSubset (μ ≫ sX) hlog.isSmoothScheme
    hlog.isSNCSubset
  have hcoef := exists_isLogDiscrepancy_coeff_eq sX hX hsm hΔ hDns hD0 hlog hY hμ hD hΓ hE hF hs
  funext U
  ext g
  refine ⟨mem_adjointSet_of_mem_multiplierIdealSections sX hX hsm hΔ hDns hlog hY hμ hsnc hcoef,
    ?_⟩
  rintro ⟨hg0, hg⟩
  refine ⟨fun hU => hg0 ?_, fun P hP => ?_⟩
  · by_contra hne
    obtain ⟨u, hu⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty U).mp hne
    obtain ⟨_, hx', x', rfl⟩ := μ.denseRange.inter_open_nonempty _ U.isOpen ⟨u, hu⟩
    have hx'' : x' ∈ μ ⁻¹ᵁ U := hx'
    rw [hU] at hx''
    exact hx''
  · have hxU := MMP.Intersection.genericPoint_mem_of_support_inter_nonempty P hP
    obtain ⟨n, a, hla, -⟩ := hE P
    have hn := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hla
    obtain ⟨a₀, α, ha₀, hα, hGP, -, -⟩ := hcoef n hn P
    rw [hGP]
    exact hg n ⟨Y, μ, hY, hμ, P⟩ a₀ α hxU ha₀ hα

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The topological Krull dimension of a variety is a natural number. -/
private theorem exists_topologicalKrullDim_eq (hX : MMP.Mori.IsVariety k sX) :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  haveI : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  refine ⟨(Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation k).dimensionFunction sX
    (genericPoint X)).toNat, ?_⟩
  rw [← Stacks.Chow.topologicalKrullDim_closure_singleton_eq k sX (genericPoint X)]
  have h : closure ({genericPoint X} : Set X) = Set.univ := (genericPoint_spec X).def
  exact (IsHomeomorph.topologicalKrullDim_eq _
    ((Homeomorph.setCongr h).trans (Homeomorph.Set.univ X)).isHomeomorph).symm

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
  have hcQ := MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX hc
  have h := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
    (show IsProper (𝟙 X) from inferInstance)
  rw [hcQ] at h
  convert h using 1
  push_cast
  ring

/-- The valuation of a prime divisor `Q` of `X`, regarded as a divisor over `X`, is the
divisorial valuation of `Q`. -/
private theorem valuation_ofPrimeDivisor (hX : IsNormalVariety k sX)
    (Q : MMP.Mori.PrimeDivisor X) (g : X.functionField) :
    (DivisorOver.ofPrimeDivisor k hX Q).valuation g = Q.divisorialValuation g := by
  change Q.divisorialValuation (functionFieldMap (𝟙 X) g) = _
  rw [MMP.Mori.functionFieldMap_id_apply]

/-- The sections of `𝒪_X(-A)` have `v_F ≤ exp (-coeff_F(A'))` along every divisor centred in the
open set, for the pull-back `A'` of the Cartier divisor `A`. -/
private theorem valuation_le_of_mem_multiplierIdealSections {F : DivisorOver k sX}
    {A : Divisor X} (hA : A.IsCartier) {V : X.Opens} (hx : F.f F.E.genericPoint ∈ V)
    {g : X.functionField} (hg : g ∈ MMP.Intersection.multiplierIdealSections (𝟙 X) (-A) V) :
    haveI := F.isLocallyNoetherian
    haveI := F.isNormal
    ∀ (A' : Divisor F.Y) (hAs : ∀ Z : irreducibleComponents F.Y,
        F.f (componentGenericPoint F.Y Z) ∉ A.supp), A.IsPullback F.f hAs A' →
      F.valuation g ≤ WithZero.exp (-A'.coeff F.E) := by
  intro A' hAs hA'
  refine valuation_le_exp_of_isPullback hA (fun Γ hΓ => ?_) A' hAs hA'
  have h := hg.2 Γ ⟨_, hΓ, hx⟩
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.functionFieldMap_id_apply,
    DivisorWithCoeffs.coeff_neg] at h
  exact h

/-- **The resolution choices exist**: a projective log resolution of `Δ + D`, the reduced sum
`Γ` of the zero places of `(X, Δ)` on it, and the divisor `E` with `K_Y + Γ = μ^*(K_X + Δ) + E`. -/
private theorem exists_isReducedAdjointIdealOn [IsAlgClosed k] [CharZero k] (Δ : Divisor X)
    (D : QDivisor X) (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    (hΔ : IsReducedSNC sX Δ) (hD0 : ∀ P, 0 ≤ D.coeff P) (hDns : ContainsNoStratum Δ D.supp) :
    ∃ (Y : Scheme.{u}) (μ : Y ⟶ X) (J : X.Opens → Set X.functionField),
      IsReducedAdjointIdealOn sX Δ D μ J := by
  classical
  haveI : MMP.Mori.IsVariety k sX := hX.1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨Y, μ, h1, h2⟩ := MMP.Mori.exists_isLogResolution_isProjectiveMorphism sX hX
    (QDivisor.toRDivisor (Divisor.toQDivisor Δ + D))
  have hlog : MMP.Fourfold.IsLogResolution sX (Divisor.toQDivisor Δ + D) μ := ⟨h1, h2⟩
  have hres := h1.toIsSmoothResolution
  obtain ⟨hY, -, -⟩ := hres.isNormalVariety hX
  haveI : IsIntegral Y := hres.isIntegral
  haveI : IsNormal Y := hres.isNormal
  haveI : LocallyOfFiniteType (μ ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (μ ≫ sX)
  have hμ := hres.isBirationalMorphism
  haveI : IsDominant μ := hμ.isDominant
  haveI : MMP.Mori.IsVariety k (μ ≫ sX) := hY.1
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (μ ≫ sX)
  obtain ⟨m, hm, D₀, hD₀, hD₀c⟩ := (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm D).exists_pos
  have hD : ∀ Z : irreducibleComponents Y, μ (componentGenericPoint Y Z) ∉ D.supp := by
    intro Z
    rw [← QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hD₀]
    exact MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp μ D₀ Z
  have hF := QDivisor.isPullback_pullback (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm D) hD
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq sX hX.1
  choose a₀ ha₀ using fun P : MMP.Mori.PrimeDivisor Y =>
    exists_nat_isLogDiscrepancy_of_isReducedSNC sX hX hsm hn hΔ ⟨Y, μ, hY, hμ, P⟩ hres.isProper
  have hsmY : IsSmoothScheme (μ ≫ sX) := hres.isSmoothScheme
  obtain ⟨s, hs, -⟩ := exists_finset_of_isSNCSubset (μ ≫ sX) hsmY hlog.isSNCSubset
  have hout : ∀ P, P ∉ s → a₀ P = 1 := fun P hPs => by
    exact_mod_cast MMP.Threefold.Bridges.IsLogDiscrepancy.unique (ha₀ P)
      (isLogDiscrepancy_one_of_notMem_finset sX hX hsm hn hΔ.1 hD0 hY hμ hres.isProper hs hPs).1
  let Γ : Divisor Y := Finsupp.ofSupportFinite (fun P => if a₀ P = 0 then (1 : ℤ) else 0)
    ((Finset.finite_toSet s).subset fun P hP =>
      Classical.byContradiction fun hPs => hP (by simp [hout P hPs]))
  have hΓc : ∀ P, Γ.coeff P = if a₀ P = 0 then 1 else 0 := fun P => rfl
  let E : Divisor Y := Finsupp.ofSupportFinite (fun P => (a₀ P : ℤ) - 1 + Γ.coeff P)
    ((Finset.finite_toSet s).subset fun P hP =>
      Classical.byContradiction fun hPs => hP (by simp [hΓc, hout P hPs]))
  have hEc : ∀ P, E.coeff P = (a₀ P : ℤ) - 1 + Γ.coeff P := fun P => rfl
  refine ⟨Y, μ, _, hX, hsm, hΔ, hD0, hDns, hlog, inferInstance, inferInstance, inferInstance,
    inferInstance, hY, hμ, hD, Γ, E, _, ⟨fun P => ?_, fun P => ?_⟩, fun P => ?_, hF, rfl⟩
  · rw [hΓc]; split_ifs <;> simp
  · rw [hΓc]
    refine ⟨fun h => ?_, fun ⟨n', hn'⟩ => ?_⟩
    · split_ifs at h with h0
      · exact ⟨n, by rw [← Nat.cast_zero (R := ℝ), ← h0]; exact ha₀ P⟩
      · simp at h
    · simp [show a₀ P = 0 by
        exact_mod_cast MMP.Threefold.Bridges.IsLogDiscrepancy.unique (ha₀ P) hn']
  · exact ⟨n, a₀ P, ha₀ P, by rw [hEc]; push_cast; ring⟩

/-- Over a non-empty open, the valuative adjoint ideal of a reduced snc pair consists of regular
functions. -/
private theorem adjointSet_subset_range [IsAlgClosed k] [CharZero k] {Δ : Divisor X}
    {D : QDivisor X} (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    (hΔ : IsReducedSNC sX Δ) (hD0 : ∀ P, 0 ≤ D.coeff P) (U : X.Opens) [Nonempty U] :
    adjointSet sX Δ D U ⊆ Set.range (X.germToFunctionField U) := by
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
  have h1 := isLogDiscrepancy_ofPrimeDivisor sX hX hsm hn (Divisor.toQDivisor Δ + D) Q
  rw [map_add, QDivisor.toRDivisor_toQDivisor] at h1
  have hv := hg.2 n _ _ _ hxU h0 h1
  rw [valuation_ofPrimeDivisor] at hv
  have hle1 : Q.divisorialValuation g ≤ 1 := by
    refine hv.trans ?_
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    refine ceil_sub_one_add_ite_nonpos ?_ ?_
    · rw [Divisor.coeff_toQDivisor]
      rcases hΔ.1 Q with h | h <;> rw [h] <;> norm_num
    · rw [DivisorWithCoeffs.coeff_add]
      push_cast
      have : (0 : ℝ) ≤ ((D.coeff Q : ℚ) : ℝ) := by exact_mod_cast hD0 Q
      linarith
  rw [Q.divisorialValuation_eq_exp_neg_ord hg0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    at hle1
  omega

/-- The valuative adjoint ideal is antitone in the boundary and in the divisor. -/
private theorem adjointSet_subset_adjointSet_of_le [IsAlgClosed k] [CharZero k] {Δ Δ' : Divisor X}
    {D D' : QDivisor X} (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    (hΔ : IsReducedSNC sX Δ) (hΔ' : IsReducedSNC sX Δ') (hΔΔ' : Δ ≤ Δ')
    (hDD' : ∀ P, D.coeff P ≤ D'.coeff P) (U : X.Opens) :
    adjointSet sX Δ' D' U ⊆ adjointSet sX Δ D U := by
  intro g hg
  refine ⟨hg.1, fun n F a₀ a hx ha₀ ha => ?_⟩
  have := F.isLocallyNoetherian
  have := F.isNormal
  have := F.isIntegral
  have := F.isBirationalMorphism.isDominant
  have : CompactSpace F.Y := (F.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  have hC₁ : Divisor.IsCartier (Δ' - Δ) := MMP.Fourfold.isCartier_of_isSmoothScheme hsm _
  have hB₁ := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp F.f (Δ' - Δ)
  obtain ⟨C₁', hC₁'⟩ := hC₁.exists_isPullback hB₁
  have hc1 : 0 ≤ C₁'.coeff F.E := coeff_isPullback_nonneg hC₁ (fun Γ _ => by
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_apply,
      DivisorWithCoeffs.coeff_apply]
    linarith [hΔΔ' Γ]) C₁' hB₁ hC₁'
  obtain ⟨m, hm, D₂, hD₂, hD₂c⟩ :=
    (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm (D' - D)).exists_pos
  have hB₂ := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp F.f D₂
  obtain ⟨D₂', hD₂'⟩ := hD₂c.exists_isPullback hB₂
  have hc2 : 0 ≤ D₂'.coeff F.E := coeff_isPullback_nonneg hD₂c (fun Γ _ => by
    have h1 := congrArg (fun G : QDivisor X => G.coeff Γ) hD₂
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_sub, zsmul_eq_mul, Int.cast_natCast] at h1
    have : (0 : ℚ) ≤ (D₂.coeff Γ : ℚ) := by
      rw [h1]; exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hDD' Γ])
    exact_mod_cast this) D₂' hB₂ hD₂'
  have ha₀' := isLogDiscrepancy_add_smul ha₀ hC₁ 1 C₁' hB₁ hC₁'
  have ha1 := isLogDiscrepancy_add_smul ha hC₁ 1 C₁' hB₁ hC₁'
  have ha2 := isLogDiscrepancy_add_of_zsmul ha1 hm hD₂ hD₂c D₂' hB₂ hD₂'
  have e1 : Divisor.toRDivisor Δ + (1 : ℝ) • Divisor.toRDivisor (Δ' - Δ) =
      Divisor.toRDivisor Δ' := by
    rw [one_smul, map_sub]; abel
  have e2 : Divisor.toRDivisor Δ + QDivisor.toRDivisor D +
      (1 : ℝ) • Divisor.toRDivisor (Δ' - Δ) + QDivisor.toRDivisor (D' - D) =
      Divisor.toRDivisor Δ' + QDivisor.toRDivisor D' := by
    rw [one_smul, map_sub, map_sub]; abel
  rw [e1] at ha₀'
  rw [e2] at ha2
  have hv := hg.2 n F _ _ hx ha₀' ha2
  refine hv.trans (WithZero.exp_le_exp.mpr ?_)
  obtain ⟨p, hp⟩ :=
    MMP.Intersection.IsLogDiscrepancy.exists_nat_eq_of_isSNC sX hX.1 hsm hΔ.1 hΔ.2 ha₀
  obtain ⟨p', hp'⟩ :=
    MMP.Intersection.IsLogDiscrepancy.exists_nat_eq_of_isSNC sX hX.1 hsm hΔ'.1 hΔ'.2 ha₀'
  exact ceil_add_ite_le_of_le hp hp' (by exact_mod_cast hc1)
    (div_nonneg (by exact_mod_cast hc2) (Nat.cast_nonneg _))

/-- `Δ + (D + A) = Δ + D + 1 • A` as `ℝ`-divisors. -/
private theorem toRDivisor_add_toQDivisor_eq (Δ A : Divisor X) (D : QDivisor X) :
    Divisor.toRDivisor Δ + QDivisor.toRDivisor (D + Divisor.toQDivisor A) =
      Divisor.toRDivisor Δ + QDivisor.toRDivisor D + (1 : ℝ) • Divisor.toRDivisor A := by
  rw [map_add, QDivisor.toRDivisor_toQDivisor, one_smul, add_assoc]

/-- A section of `𝒥_{Δ,D+A}` is locally a sum of products of local equations of `A` with sections
of `𝒥_{Δ,D}`. -/
private theorem exists_mem_span_of_mem_adjointSet_add {Δ A : Divisor X} {D : QDivisor X}
    (hAc : A.IsCartier) {U : X.Opens} {g : X.functionField}
    (hg : g ∈ adjointSet sX Δ (D + Divisor.toQDivisor A) U) :
    ∀ x ∈ U, ∃ V : X.Opens, x ∈ V ∧ V ≤ U ∧
      g ∈ Submodule.span ℤ (MMP.Intersection.multiplierIdealSections (𝟙 X) (-A) V *
        adjointSet sX Δ D V) := by
  obtain ⟨-, hg⟩ := hg
  intro x hx
  obtain ⟨Ux, hxUx, φ, hφ⟩ := hAc x
  set h := MMP.Threefold.Mori.Helpers.evalFF (MMP.Mori.pointComponent x)
    (φ : MMP.Mori.RationalFunctions X) with hhdef
  have hh : h ≠ 0 := (φ.isUnit.map _).ne_zero
  have hordh : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ Ux).Nonempty →
      X.ord h Γ.genericPoint = A.coeff Γ := fun Γ hΓ => by
    rw [hφ Γ hΓ, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, show Γ.component =
      MMP.Mori.pointComponent x from Subsingleton.elim
        (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _]
  have hxV : x ∈ U ⊓ Ux := ⟨hx, hxUx⟩
  have hVne : U ⊓ Ux ≠ ⊥ := fun hb => by rwa [hb] at hxV
  refine ⟨U ⊓ Ux, hxV, inf_le_left, Submodule.subset_span ⟨h, ⟨fun hb => ?_, fun P hP => ?_⟩,
    g * h⁻¹, ⟨fun hb => absurd hb hVne, fun n F a₀ a hxF ha₀ ha => ?_⟩, ?_⟩⟩
  · exfalso
    have hx' : x ∈ (𝟙 X) ⁻¹ᵁ (U ⊓ Ux) := hxV
    rw [hb] at hx'
    exact hx'
  · obtain ⟨z, hzP, hzV⟩ := hP
    rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.functionFieldMap_id_apply,
      P.divisorialValuation_eq_exp_neg_ord hh, DivisorWithCoeffs.coeff_neg,
      hordh P ⟨z, hzP, (show z ∈ U ⊓ Ux from hzV).2⟩]
  · have := F.isLocallyNoetherian
    have := F.isNormal
    have := F.isIntegral
    have := F.isBirationalMorphism.isDominant
    have : CompactSpace F.Y :=
      (F.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
    have hBA := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp F.f A
    obtain ⟨A', hA'⟩ := hAc.exists_isPullback hBA
    have ha' := isLogDiscrepancy_add_smul ha hAc 1 A' hBA hA'
    rw [← toRDivisor_add_toQDivisor_eq] at ha'
    have hv := hg n F a₀ _ hxF.1 ha₀ ha'
    have hvh : F.valuation h = WithZero.exp (-A'.coeff F.E) := by
      change F.E.divisorialValuation (functionFieldMap F.f h) = _
      rw [F.E.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).mpr hh),
        MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hA' hφ F.E hxF.2
          (MMP.Mori.pointComponent x), ← hhdef]
    rw [map_mul, map_inv₀, hvh, ← WithZero.exp_neg, neg_neg]
    calc F.valuation g * WithZero.exp (A'.coeff F.E)
        ≤ WithZero.exp (⌈a - 1 * (A'.coeff F.E : ℝ)⌉ - 1 + if a₀ = 0 then 1 else 0) *
            WithZero.exp (A'.coeff F.E) := mul_le_mul' hv le_rfl
      _ = WithZero.exp (⌈a⌉ - 1 + if a₀ = 0 then 1 else 0) := by
        rw [← WithZero.exp_add, one_mul, Int.ceil_sub_intCast]
        congr 1
        ring
  · beta_reduce
    field_simp

/-- A rational function which is locally a sum of products of sections of `𝒪_X(-A)` and of
`𝒥_{Δ,D}` is a section of `𝒥_{Δ,D+A}`. -/
private theorem mem_adjointSet_add_of_forall_mem_span [IsAlgClosed k] [CharZero k]
    {Δ A : Divisor X} {D : QDivisor X} (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    (hAc : A.IsCartier) {U : X.Opens} {g : X.functionField} (hg0 : U = ⊥ → g = 0)
    (hg : ∀ x ∈ U, ∃ V : X.Opens, x ∈ V ∧ V ≤ U ∧
      g ∈ Submodule.span ℤ (MMP.Intersection.multiplierIdealSections (𝟙 X) (-A) V *
        adjointSet sX Δ D V)) :
    g ∈ adjointSet sX Δ (D + Divisor.toQDivisor A) U := by
  refine ⟨hg0, fun n F a₀ a' hx ha₀ ha' => ?_⟩
  obtain ⟨V, hxV, hVU, hgV⟩ := hg _ hx
  have := F.isLocallyNoetherian
  have := F.isNormal
  have := F.isIntegral
  have := F.isBirationalMorphism.isDominant
  have : CompactSpace F.Y :=
    (F.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  have hBA := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp F.f A
  obtain ⟨A', hA'⟩ := hAc.exists_isPullback hBA
  have hn := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha₀
  obtain ⟨a, ha⟩ := exists_isLogDiscrepancy hX hsm hn (Divisor.toQDivisor Δ + D) F ha₀.2.1
  rw [map_add, QDivisor.toRDivisor_toQDivisor] at ha
  have ha'' := isLogDiscrepancy_add_smul ha hAc 1 A' hBA hA'
  rw [← toRDivisor_add_toQDivisor_eq] at ha''
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha' ha'']
  have hsub : Submodule.span ℤ (MMP.Intersection.multiplierIdealSections (𝟙 X) (-A) V *
      adjointSet sX Δ D V) ≤ (F.valuation.leAddSubgroup (WithZero.exp
        (⌈a - 1 * (A'.coeff F.E : ℝ)⌉ - 1 + if a₀ = 0 then 1 else 0))).toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, j, hj, rfl⟩
    change F.valuation (b * j) ≤ _
    rw [map_mul]
    calc F.valuation b * F.valuation j
        ≤ WithZero.exp (-A'.coeff F.E) *
            WithZero.exp (⌈a⌉ - 1 + if a₀ = 0 then 1 else 0) :=
          mul_le_mul' (valuation_le_of_mem_multiplierIdealSections sX hAc hxV hb A' hBA hA')
            (hj.2 n F a₀ a hxV ha₀ ha)
      _ = _ := by
        rw [← WithZero.exp_add, one_mul, Int.ceil_sub_intCast]
        congr 1
        ring
  exact hsub hgV

/-- If `D - A ≤ G` and `1` is a global section of `𝒥_{Δ,G}`, then `𝒪_X(-A) ⊆ 𝒥_{Δ,D}`. -/
private theorem multiplierIdealSections_subset_adjointSet [IsAlgClosed k] [CharZero k]
    {Δ A : Divisor X} {D G : QDivisor X} (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    (hΔ : IsReducedSNC sX Δ) (hDns : ContainsNoStratum Δ D.supp) (hAc : A.IsCartier)
    (hA0 : 0 ≤ A) (hDG : ∀ P, D.coeff P - A.coeff P ≤ G.coeff P)
    (h1 : (1 : X.functionField) ∈ adjointSet sX Δ G ⊤) (U : X.Opens) :
    MMP.Intersection.multiplierIdealSections (𝟙 X) (-A) U ⊆ adjointSet sX Δ D U := by
  intro g hg
  refine ⟨fun hU => hg.1 (by rw [hU]; rfl), fun n F a₀ a hx ha₀ ha => ?_⟩
  have := F.isLocallyNoetherian
  have := F.isNormal
  have := F.isIntegral
  have := F.isBirationalMorphism.isDominant
  have : CompactSpace F.Y := (F.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  have hn := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha₀
  obtain ⟨aG, haG⟩ := exists_isLogDiscrepancy hX hsm hn (Divisor.toQDivisor Δ + G) F ha₀.2.1
  rw [map_add, QDivisor.toRDivisor_toQDivisor] at haG
  have hvG := h1.2 n F a₀ aG trivial ha₀ haG
  rw [map_one, ← WithZero.exp_zero, WithZero.exp_le_exp] at hvG
  have hBA := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp F.f A
  obtain ⟨A', hA'⟩ := hAc.exists_isPullback hBA
  have hμA : 0 ≤ A'.coeff F.E := coeff_isPullback_nonneg hAc (fun Γ _ => hA0 Γ) A' hBA hA'
  have hv := valuation_le_of_mem_multiplierIdealSections sX hAc hx hg A' hBA hA'
  refine hv.trans (WithZero.exp_le_exp.mpr ?_)
  by_cases ha0 : a₀ = 0
  · have ha0' : a = 0 := eq_zero_of_isLogDiscrepancy_eq_zero hX hsm hΔ hDns
      (by rwa [ha0] at ha₀) ha
    rw [ha0', if_pos ha0]
    simp only [Int.ceil_zero, zero_sub, neg_add_cancel]
    omega
  · rw [if_neg ha0] at hvG ⊢
    have haG0 : 0 < aG := Int.ceil_pos.mp (by omega)
    obtain ⟨m, hm, C₃, hC₃, hC₃c⟩ := (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
      (G + Divisor.toQDivisor A - D)).exists_pos
    have hB₃ := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp F.f C₃
    obtain ⟨C₃', hC₃'⟩ := hC₃c.exists_isPullback hB₃
    have hc3 : 0 ≤ C₃'.coeff F.E := coeff_isPullback_nonneg hC₃c (fun Γ _ => by
      have h1 := congrArg (fun B : QDivisor X => B.coeff Γ) hC₃
      simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
        DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_add, zsmul_eq_mul,
        Int.cast_natCast] at h1
      have : (0 : ℚ) ≤ (C₃.coeff Γ : ℚ) := by
        rw [h1]; exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hDG Γ])
      exact_mod_cast this) C₃' hB₃ hC₃'
    have h3 := isLogDiscrepancy_add_of_zsmul ha hm hC₃ hC₃c C₃' hB₃ hC₃'
    have h4 := isLogDiscrepancy_add_smul haG hAc 1 A' hBA hA'
    have e : Divisor.toRDivisor Δ + QDivisor.toRDivisor D +
        QDivisor.toRDivisor (G + Divisor.toQDivisor A - D) =
        Divisor.toRDivisor Δ + QDivisor.toRDivisor G + (1 : ℝ) • Divisor.toRDivisor A := by
      rw [map_sub, map_add, QDivisor.toRDivisor_toQDivisor, one_smul]; abel
    rw [e] at h3
    have hu := MMP.Threefold.Bridges.IsLogDiscrepancy.unique h3 h4
    have hm' : (0 : ℝ) ≤ (C₃'.coeff F.E : ℝ) / m :=
      div_nonneg (by exact_mod_cast hc3) (Nat.cast_nonneg _)
    have hlt : ((-A'.coeff F.E : ℤ) : ℝ) < a := by push_cast; linarith
    have := Int.lt_ceil.mpr hlt
    omega

/-- The adjoint set is all of `𝒪_X` when every log discrepancy `a(F, X, Δ + D)` is positive,
and zero where `a(F, X, Δ) = 0`. -/
private theorem adjointSet_eq_range_of_forall [IsAlgClosed k] [CharZero k] {Δ : Divisor X}
    {D : QDivisor X} (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    (hΔ : IsReducedSNC sX Δ) (hD0 : ∀ P, 0 ≤ D.coeff P)
    (hcond : ∀ (n : ℕ) (F : DivisorOver k sX) (a a₀ : ℝ),
        MMP.Intersection.IsLogDiscrepancy sX n
          (Divisor.toRDivisor Δ + QDivisor.toRDivisor D) F a →
        MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) F a₀ →
        (a₀ = 0 → a = 0) ∧ (a₀ ≠ 0 → 0 < a))
    (U : X.Opens) [Nonempty U] : adjointSet sX Δ D U = Set.range (X.germToFunctionField U) := by
  refine (adjointSet_subset_range sX hX hsm hΔ hD0 U).antisymm ?_
  rintro _ ⟨r, rfl⟩
  refine ⟨fun hU => ?_, fun n F a₀ a hx ha₀ ha => ?_⟩
  · exfalso
    obtain ⟨u⟩ := ‹Nonempty U›
    exact (TopologicalSpace.Opens.ne_bot_iff_nonempty U).mpr ⟨u.1, u.2⟩ hU
  · have hle := MMP.Positivity.DivisorOver.valuation_algebraMap_le_one F _ rfl
      (X.presheaf.germ U _ hx r)
    rw [Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hx] at hle
    refine hle.trans ?_
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    obtain ⟨h0, hpos⟩ := hcond n F a a₀ ha ha₀
    by_cases ha0 : a₀ = 0
    · rw [h0 ha0, if_pos ha0]
      simp
    · rw [if_neg ha0]
      have := Int.ceil_pos.mpr (hpos ha0)
      omega

/-- **The unit-ideal criterion.** `𝒥_{Δ,D} = 𝒪_X` exactly when `a(F, X, Δ + D) = 0` whenever
`a(F, X, Δ) = 0`, and `a(F, X, Δ + D) > 0` otherwise. -/
private theorem adjointSet_eq_range_iff [IsAlgClosed k] [CharZero k] {Δ : Divisor X}
    {D : QDivisor X} (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    (hΔ : IsReducedSNC sX Δ) (hD0 : ∀ P, 0 ≤ D.coeff P) (hDns : ContainsNoStratum Δ D.supp) :
    (∀ (U : X.Opens) [Nonempty U], adjointSet sX Δ D U = Set.range (X.germToFunctionField U)) ↔
      ∀ (n : ℕ) (F : DivisorOver k sX) (a a₀ : ℝ),
        MMP.Intersection.IsLogDiscrepancy sX n
          (Divisor.toRDivisor Δ + QDivisor.toRDivisor D) F a →
        MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) F a₀ →
        (a₀ = 0 → a = 0) ∧ (a₀ ≠ 0 → 0 < a) := by
  constructor
  · intro hU n F a a₀ ha ha₀
    haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
    have h1 : (1 : X.functionField) ∈ adjointSet sX Δ D ⊤ := by
      rw [hU ⊤]
      exact ⟨1, map_one _⟩
    refine ⟨fun h0 => eq_zero_of_isLogDiscrepancy_eq_zero hX hsm hΔ hDns
      (by rwa [h0] at ha₀) ha, fun h0 => ?_⟩
    have hv := h1.2 n F a₀ a trivial ha₀ ha
    rw [map_one, ← WithZero.exp_zero, WithZero.exp_le_exp, if_neg h0] at hv
    exact Int.ceil_pos.mp (by omega)
  · exact fun hcond U _ => adjointSet_eq_range_of_forall sX hX hsm hΔ hD0 hcond U

end Main

end Proof_lem_fourfold_adjoint_ideal_operations

namespace MMP.Fourfold

open MMP.Mori
open Proof_lem_fourfold_adjoint_ideal_operations

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **Independence and elementary operations for reduced-boundary adjoint ideals.** Let `X` be
a normal integral locally Noetherian scheme over an algebraically closed field `k` of
characteristic zero (smooth, as `MMP.Fourfold.IsReducedAdjointIdealOn` requires).
1. If `X` is a smooth normal variety, `Δ` reduced snc and `D` an effective `ℚ`-divisor whose
   support contains no stratum of `Δ`, then `𝒥_{Δ,D}` is computed on some log resolution.
2. `𝒥_{Δ,D}` consists of regular functions and is the ideal sheaf of an
   `AlgebraicGeometry.Scheme.IdealSheafData` of `X` on every non-empty affine open.
3. `𝒥_{Δ,D}` does not depend on the log resolution.
4. If `Δ ≤ Δ'` and `D ≤ D'`, then `𝒥_{Δ',D'} ⊆ 𝒥_{Δ,D}`.
5. For an effective integral Cartier divisor `A`, `𝒥_{Δ,D+A} = 𝒥_{Δ,D} ⊗ 𝒪_X(-A)`.
6. If `A` is effective integral Cartier, `D - A ≤ G` and `𝒥_{Δ,G} = 𝒪_X`, then
   `𝒪_X(-A) ⊆ 𝒥_{Δ,D}`.
7. `𝒥_{Δ,D} = 𝒪_X` if and only if, for every divisor `F` over `X`, `a(F, X, Δ + D) = 0` when
   `a(F, X, Δ) = 0` and `a(F, X, Δ + D) > 0` otherwise. -/
@[mmp "lem_fourfold_adjoint_ideal_operations"]
public theorem isReducedAdjointIdealOn_operations {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] :
    -- 1. the resolution choices exist
    (∀ (Δ : Divisor X) (D : QDivisor X), IsNormalVariety k sX → IsSmoothScheme sX →
      IsReducedSNC sX Δ → (∀ P, 0 ≤ D.coeff P) → ContainsNoStratum Δ D.supp →
      ∃ (Y : Scheme.{u}) (μ : Y ⟶ X) (J : X.Opens → Set X.functionField),
        IsReducedAdjointIdealOn sX Δ D μ J) ∧
    -- 2. a coherent ideal subsheaf of `𝒪_X`
    (∀ (Δ : Divisor X) (D : QDivisor X) {Y : Scheme.{u}} (μ : Y ⟶ X)
      (J : X.Opens → Set X.functionField), IsReducedAdjointIdealOn sX Δ D μ J →
      (∀ (U : X.Opens) [Nonempty U], J U ⊆ Set.range (X.germToFunctionField U)) ∧
      ∃ I : X.IdealSheafData, ∀ (U : X.affineOpens) [Nonempty (U : X.Opens)],
        J U = X.germToFunctionField (U : X.Opens) '' (I.ideal U : Set Γ(X, U))) ∧
    -- 3. independence of the resolution
    (∀ (Δ : Divisor X) (D : QDivisor X) {Y Y' : Scheme.{u}} (μ : Y ⟶ X) (μ' : Y' ⟶ X)
      (J J' : X.Opens → Set X.functionField),
      IsReducedAdjointIdealOn sX Δ D μ J → IsReducedAdjointIdealOn sX Δ D μ' J' → J = J') ∧
    -- 4. antitone in the boundary and in the divisor
    (∀ (Δ Δ' : Divisor X) (D D' : QDivisor X) {Y Y' : Scheme.{u}} (μ : Y ⟶ X) (μ' : Y' ⟶ X)
      (J J' : X.Opens → Set X.functionField),
      IsReducedAdjointIdealOn sX Δ D μ J → IsReducedAdjointIdealOn sX Δ' D' μ' J' →
      Δ ≤ Δ' → (∀ P, D.coeff P ≤ D'.coeff P) → ∀ U, J' U ⊆ J U) ∧
    -- 5. the integral shift `𝒥_{Δ,D+A} = 𝒥_{Δ,D} ⊗ 𝒪_X(-A)`
    (∀ (Δ A : Divisor X) (D : QDivisor X) {Y Y' : Scheme.{u}} (μ : Y ⟶ X) (μ' : Y' ⟶ X)
      (J J' : X.Opens → Set X.functionField), A.IsCartier → 0 ≤ A →
      IsReducedAdjointIdealOn sX Δ D μ J →
      IsReducedAdjointIdealOn sX Δ (D + Divisor.toQDivisor A) μ' J' →
      ∀ U, J' U = {g | (U = ⊥ → g = 0) ∧ ∀ x ∈ U, ∃ V : X.Opens, x ∈ V ∧ V ≤ U ∧
        g ∈ Submodule.span ℤ (MMP.Intersection.multiplierIdealSections (𝟙 X) (-A) V * J V)}) ∧
    -- 6. `D - A ≤ G` and `𝒥_{Δ,G} = 𝒪_X` give `𝒪_X(-A) ⊆ 𝒥_{Δ,D}`
    (∀ (Δ A : Divisor X) (D G : QDivisor X) {Y Y' : Scheme.{u}} (μ : Y ⟶ X) (μ' : Y' ⟶ X)
      (J J' : X.Opens → Set X.functionField), A.IsCartier → 0 ≤ A →
      (∀ P, D.coeff P - A.coeff P ≤ G.coeff P) →
      IsReducedAdjointIdealOn sX Δ D μ J → IsReducedAdjointIdealOn sX Δ G μ' J' →
      (∀ (U : X.Opens) [Nonempty U], J' U = Set.range (X.germToFunctionField U)) →
      ∀ U, MMP.Intersection.multiplierIdealSections (𝟙 X) (-A) U ⊆ J U) ∧
    -- 7. the unit-ideal criterion
    (∀ (Δ : Divisor X) (D : QDivisor X) {Y : Scheme.{u}} (μ : Y ⟶ X)
      (J : X.Opens → Set X.functionField), IsReducedAdjointIdealOn sX Δ D μ J →
      ((∀ (U : X.Opens) [Nonempty U], J U = Set.range (X.germToFunctionField U)) ↔
        ∀ (n : ℕ) (F : DivisorOver k sX) (a a₀ : ℝ),
          MMP.Intersection.IsLogDiscrepancy sX n
            (Divisor.toRDivisor Δ + QDivisor.toRDivisor D) F a →
          MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) F a₀ →
          (a₀ = 0 → a = 0) ∧ (a₀ ≠ 0 → 0 < a))) := by
  classical
  have hrange : ∀ (Δ : Divisor X) (D : QDivisor X) {Y : Scheme.{u}} (μ : Y ⟶ X)
      (J : X.Opens → Set X.functionField), IsReducedAdjointIdealOn sX Δ D μ J →
      ∀ (U : X.Opens) [Nonempty U], J U ⊆ Set.range (X.germToFunctionField U) := by
    intro Δ D Y μ J h U _
    rw [eq_adjointSet sX h]
    obtain ⟨hX, hsm, hΔ, hD0, -⟩ := h
    exact adjointSet_subset_range sX hX hsm hΔ hD0 U
  refine ⟨fun Δ D hX hsm hΔ hD0 hDns => exists_isReducedAdjointIdealOn sX Δ D hX hsm hΔ hD0 hDns,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 2. a coherent ideal subsheaf of `𝒪_X`
    intro Δ D Y μ J h
    refine ⟨fun U _ => hrange Δ D μ J h U, ?_⟩
    have h' := h
    obtain ⟨-, -, -, -, -, -, _, _, _, _, -, -, -, Γ, E, F, -, -, -, rfl⟩ := h'
    exact exists_idealSheafData_of_subset_range μ _ (fun U _ => hrange Δ D μ _ h U)
  · -- 3. independence of the resolution
    intro Δ D Y Y' μ μ' J J' h h'
    exact (eq_adjointSet sX h).trans (eq_adjointSet sX h').symm
  · -- 4. antitone in the boundary and in the divisor
    intro Δ Δ' D D' Y Y' μ μ' J J' h h' hΔΔ' hDD' U
    rw [eq_adjointSet sX h', eq_adjointSet sX h]
    obtain ⟨hX, hsm, hΔ, -⟩ := h
    obtain ⟨-, -, hΔ', -⟩ := h'
    exact adjointSet_subset_adjointSet_of_le sX hX hsm hΔ hΔ' hΔΔ' hDD' U
  · -- 5. the integral shift `𝒥_{Δ,D+A} = 𝒥_{Δ,D} ⊗ 𝒪_X(-A)`
    intro Δ A D Y Y' μ μ' J J' hAc _ h h' U
    rw [eq_adjointSet sX h, eq_adjointSet sX h']
    obtain ⟨hX, hsm, -⟩ := h
    ext g
    exact ⟨fun hg => ⟨hg.1, exists_mem_span_of_mem_adjointSet_add sX hAc hg⟩,
      fun hg => mem_adjointSet_add_of_forall_mem_span sX hX hsm hAc hg.1 hg.2⟩
  · -- 6. `D - A ≤ G` and `𝒥_{Δ,G} = 𝒪_X` give `𝒪_X(-A) ⊆ 𝒥_{Δ,D}`
    intro Δ A D G Y Y' μ μ' J J' hAc hA0 hDG h h' hJ' U
    haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
    have h1 : (1 : X.functionField) ∈ adjointSet sX Δ G ⊤ := by
      rw [← eq_adjointSet sX h', hJ' ⊤]
      exact ⟨1, map_one _⟩
    rw [eq_adjointSet sX h]
    obtain ⟨hX, hsm, hΔ, -, hDns, -⟩ := h
    exact multiplierIdealSections_subset_adjointSet sX hX hsm hΔ hDns hAc hA0 hDG h1 U
  · -- 7. the unit-ideal criterion
    intro Δ D Y μ J h
    rw [eq_adjointSet sX h]
    obtain ⟨hX, hsm, hΔ, hD0, hDns, -⟩ := h
    exact adjointSet_eq_range_iff sX hX hsm hΔ hD0 hDns

end MMP.Fourfold
