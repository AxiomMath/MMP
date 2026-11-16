module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain
public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryDlt
public import MMP.AlgebraicGeometry.MMP.Fourfold.GraphDivisor
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
public import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram.GraphDivisorBranchCounts
public import MMP.AlgebraicGeometry.Divisor.Negativity.QCartierProper
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection

/-!
# Comparison divisors of fourfold step diagrams and of the bridge to the next model

For a fourfold step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)`, a finite chain of such diagrams, and the
decreased pair of a crepant junction in a stabilized small klt tail, the difference of the
pull-backs of the log canonical divisors to a common smooth projective model is effective; and two
relatively nef ends over a common base whose pull-backs differ by divisors contracted on each side
have equal pull-backs. All four results come from the negativity lemma
`MMP.Mori.QDivisor.isEffective_of_isEffective_transformDivisor_of_isRelativelyNef_neg`.

## Main results

* `MMP.Fourfold.IsGraphDivisor.nonneg`: the graph divisor `H = u^* D⁻ - v^* D⁺` of a step diagram
  is effective.
* `MMP.Fourfold.pullback_sub_pullback_nonneg_of_isFourfoldStepDiagram`: for a finite chain of
  step diagrams, `q_0^*(K_0 + Θ_0) - q_m^*(K_m + Θ_m)` is effective.
* `MMP.Fourfold.StabilizedSmallKltTail.IsDecreasedBoundary.pullback_sub_pullback_nonneg`: the
  decreased pair of a crepant junction lies above the next downstairs model,
  `q^*(K_{Y_i} + Θ_i') - r^*(K_{X_{i+1}} + B_{i+1}) ≥ 0`.
* `MMP.Fourfold.eq_of_isPullback_of_add_eq_add_of_isRelativelyNef`: two relatively nef ends with
  `A₁ + F₁ = A₂ + F₂`, `F_j ≥ 0` contracted by `q_j`, have equal pull-backs `A₁ = A₂`.

## Implementation notes

Each result's auxiliary lemmas live in a namespace under `MMP.Fourfold.ChainComparison`,
opened only for that result; the helpers shared by several results (pull-backs of negated
`ℚ`-Cartier divisors, degrees and intersection numbers of pull-backs on curves) live in
`MMP.Fourfold.ChainComparison` itself.
Pull-backs are given by their characterising property `MMP.Mori.QDivisor.IsPullback` or by
`MMP.Mori.QDivisor.pullback`; effectivity is `0 ≤ E` in the coefficientwise order.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold.ChainComparison

open MMP.Mori MMP.Fourfold

/-- The negative of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_neg {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (hD : D.IsQCartier) : (-D).IsQCartier := by
  obtain ⟨m, hm, h⟩ := hD
  exact ⟨m, hm, by rw [smul_neg]; exact h.neg⟩

/-- The pull-back of a `g`-ample Cartier divisor along `u` has nonnegative degree on every proper
curve contracted by `u ≫ g`. -/
private theorem degreeOn_nonneg_of_isPullback {W V T : Scheme.{0}} [IsIntegral W]
    [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace V]
    [IsLocallyNoetherian V] [IsNormal V] {sW : W ⟶ Spec (.of ℂ)} [QuasiCompact sW]
    {sV : V ⟶ Spec (.of ℂ)} [IsSeparated sV] [LocallyOfFiniteType sV] (u : W ⟶ V)
    (hu : u ≫ sV = sW) [IsProper u] {g : V ⟶ T} {L : Divisor V} (hL : L.IsCartier)
    (hamp : L.IsRelativelyAmple g hL)
    {hB : ∀ Z : irreducibleComponents W, u (componentGenericPoint W Z) ∉ L.supp}
    {L' : Divisor W} (hp : L.IsPullback u hB L') (C : ProperCurve sW)
    (hC : C.IsContractedBy (u ≫ g)) :
    0 ≤ L'.degreeOn ℂ sW C.ι C.dim_le (hp.isCartier hL) := by
  have := hL.isInvertibleModule_divisorialSheaf
  have := (hp.isCartier hL).isInvertibleModule_divisorialSheaf
  rw [Divisor.degreeOn, degreeOn_eq_of_iso ℂ sW C.ι C.dim_le (hp.divisorialSheafIso (hBc := hL))]
  change 0 ≤ C.degree ℂ ((Scheme.Modules.pullback u).obj L.divisorialSheaf)
  rw [C.degree_pullback u hu]
  split_ifs with h
  · refine mul_nonneg (Nat.cast_nonneg _) (le_of_lt ?_)
    refine MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy g _ hamp
      (⟨u C.point, h⟩ : ProperCurve sV) fun y hy => ?_
    have hcl : IsClosed (u '' closure {C.point}) := u.isClosedMap _ isClosed_closure
    have hsub : ({u C.point} : Set V) ⊆ u '' closure {C.point} :=
      Set.singleton_subset_iff.mpr ⟨C.point, subset_closure rfl, rfl⟩
    obtain ⟨x, hx, rfl⟩ := closure_minimal hsub hcl hy
    simpa only [Scheme.Hom.comp_apply] using hC x hx
  · exact le_rfl

/-- The pull-back of a `ℚ`-divisor with a `g`-ample multiple along `u` has nonnegative
intersection number with every proper curve contracted by `u ≫ g`. -/
private theorem intersectionNumber_nonneg_of_isPullback {W V T : Scheme.{0}} [IsIntegral W]
    [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace V]
    [IsLocallyNoetherian V] [IsNormal V] {sW : W ⟶ Spec (.of ℂ)} [QuasiCompact sW]
    {sV : V ⟶ Spec (.of ℂ)} [IsSeparated sV] [LocallyOfFiniteType sV] (u : W ⟶ V)
    (hu : u ≫ sV = sW) [IsProper u] {g : V ⟶ T} {D : QDivisor V}
    (hD : D.HasRelativelyAmpleMultiple g)
    {hB : ∀ Z : irreducibleComponents W, u (componentGenericPoint W Z) ∉ D.supp}
    {P : QDivisor W} (hp : D.IsPullback u hB P) (hPq : P.IsQCartier) (C : ProperCurve sW)
    (hC : C.IsContractedBy (u ≫ g)) :
    0 ≤ P.intersectionNumber ℂ sW C.ι C.dim_le hPq := by
  obtain ⟨m, hm, L, hL, hLq, hamp⟩ := hD
  obtain ⟨L', hL'q, hp'⟩ := hp m hm L hLq hL
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sW C.ι C.dim_le P hPq hm L' (hp'.isCartier hL)
    hL'q]
  exact div_nonneg (by exact_mod_cast degreeOn_nonneg_of_isPullback u hu hL hamp hp' C hC)
    (Nat.cast_nonneg _)

/-- If `P = u^* D`, then `-P = u^*(-D)`. -/
private theorem isPullback_neg {W V : Scheme.{0}} [IsLocallyNoetherian W] [IsNormal W]
    [IsLocallyNoetherian V] [IsNormal V] {u : W ⟶ V} {D : QDivisor V}
    {hB : ∀ Z : irreducibleComponents W, u (componentGenericPoint W Z) ∉ D.supp}
    {P : QDivisor W} (hp : D.IsPullback u hB P)
    (hB' : ∀ Z : irreducibleComponents W, u (componentGenericPoint W Z) ∉ (-D).supp) :
    (-D).IsPullback u hB' (-P) := by
  intro m hm L hLq hL
  have hq : Divisor.toQDivisor ((-1 : ℤ) • L) = (m : ℤ) • D := by
    rw [map_zsmul, hLq, smul_smul, smul_neg]
    simp
  obtain ⟨L', hL'q, hp'⟩ := hp m hm _ hq (hL.zsmul _)
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hsupp : ∀ Z : irreducibleComponents W,
      u (componentGenericPoint W Z) ∉ ((-1 : ℤ) • ((-1 : ℤ) • L)).supp := fun Z hZ => hB Z (by
    rwa [← Divisor.supp_toQDivisor, map_zsmul, hq, QDivisor.supp_zsmul (by norm_num),
      QDivisor.supp_zsmul hm'] at hZ)
  refine ⟨(-1 : ℤ) • L', by rw [map_zsmul, hL'q, smul_smul, smul_neg]; simp, ?_⟩
  exact (hp'.zsmul (hL.zsmul _) (-1) hsupp).of_eq (by rw [smul_smul]; simp)

/-! ### Degrees of pulled-back divisors on curves -/

section Pullback

variable {k : Type u} [Field k] {V T : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
  {sT : T ⟶ Spec (.of k)} [IsSeparated sT] [LocallyOfFiniteType sT]

/-- A proper curve which is not contracted by `u` does not have a point as image. -/
private theorem not_exists_range_eq_singleton (u : V ⟶ T) (Γ : ProperCurve sV)
    (h : ¬ Γ.IsContractedBy u) : ¬ ∃ t : T, Set.range (Γ.ι ≫ u) = {t} := by
  rintro ⟨t, ht⟩
  refine h fun x hx => ?_
  rw [← Γ.range_ι] at hx
  obtain ⟨y, rfl⟩ := hx
  have h1 : (Γ.ι ≫ u) y ∈ Set.range (Γ.ι ≫ u) := ⟨y, rfl⟩
  have h2 : (Γ.ι ≫ u) (genericPoint Γ.scheme) ∈ Set.range (Γ.ι ≫ u) := ⟨_, rfl⟩
  rw [ht] at h1 h2
  rw [Scheme.Hom.comp_apply] at h1 h2
  rw [Γ.ι_genericPoint] at h2
  exact h1.trans h2.symm

/-- The image of a proper curve not contracted by `u` is a proper curve. -/
private theorem isProperCurve_map (u : V ⟶ T) (hu : u ≫ sT = sV) (Γ : ProperCurve sV)
    (h : ¬ Γ.IsContractedBy u) : IsProperCurve sT (u Γ.point) := by
  set φ := Γ.ι ≫ u with hφdef
  have hφ : φ ≫ sT = Γ.ι ≫ sV := by rw [hφdef, Category.assoc, hu]
  have : IsProper (φ ≫ sT) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sT
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sT) := hφ ▸ inferInstance
  have hpt := not_exists_range_eq_singleton u Γ h
  have hcurve := isCurve_imageι_comp sT φ hpt
  have hker := Γ.ker_comp u
  rw [← hφdef] at hker
  have hdim : topologicalKrullDim (curveSubschemeAt (u Γ.point)) = 1 := by
    have h1 := hcurve.topologicalKrullDim_eq_one
    change topologicalKrullDim φ.ker.subscheme = 1 at h1
    rwa [hker] at h1
  have hprop : IsProper (curveSubschemeAtι (u Γ.point) ≫ sT) := by
    have h1 : IsProper (φ.imageι ≫ sT) := isProper_imageι_comp φ sT
    change IsProper (φ.ker.subschemeι ≫ sT) at h1
    rwa [hker] at h1
  exact ⟨hdim, hprop⟩

/-- If `u ≫ π` contracts a curve `Γ` that `u` does not contract, then `π` contracts the image
curve `u(Γ)`. -/
private theorem isContractedBy_map {S : Scheme.{u}} (u : V ⟶ T) (hu : u ≫ sT = sV) (π : T ⟶ S)
    (Γ : ProperCurve sV) (h : ¬ Γ.IsContractedBy u) (hΓ : Γ.IsContractedBy (u ≫ π)) :
    (⟨u Γ.point, isProperCurve_map u hu Γ h⟩ : ProperCurve sT).IsContractedBy π := by
  intro y hy
  change y ∈ closure {u Γ.point} at hy
  rw [← ProperCurve.range_comp u hu Γ] at hy
  obtain ⟨x, rfl⟩ := hy
  have hx : Γ.ι x ∈ closure {Γ.point} := Γ.range_ι ▸ ⟨x, rfl⟩
  have h1 := hΓ _ hx
  simp only [Scheme.Hom.comp_apply] at h1 ⊢
  exact h1

variable [QuasiCompact sV] [QuasiCompact sT] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  [IsLocallyNoetherian T] [IsNormal T]

/-- The pull-back of a Cartier divisor has degree zero on a contracted curve. -/
private theorem degreeOn_isPullback_eq_zero (u : V ⟶ T) (hu : u ≫ sT = sV) {D : Divisor T}
    (hD : D.IsCartier) {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ D.supp}
    {D' : Divisor V} (h : D.IsPullback u hB D') (Γ : ProperCurve sV) (hΓ : Γ.IsContractedBy u) :
    D'.degreeOn k sV Γ.ι Γ.dim_le (h.isCartier hD) = 0 := by
  have := QuasiCompact.compactSpace_of_compactSpace sT
  have := QuasiCompact.compactSpace_of_compactSpace sV
  obtain rfl := h.eq hD (Divisor.isPullback_pullback hD hB)
  exact Divisor.degreeOn_pullback_eq_zero_of_isContractedBy u hu hD hB Γ hΓ

/-- **Projection formula.** On a curve `Γ` not contracted by `u`, with image the proper curve
`Γ'`, `deg_Γ u^*D = [k(Γ) : k(Γ')] · deg_{Γ'} D`. -/
private theorem degreeOn_isPullback_eq_mul (u : V ⟶ T) (hu : u ≫ sT = sV) {D : Divisor T}
    (hD : D.IsCartier) {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ D.supp}
    {D' : Divisor V} (h : D.IsPullback u hB D') (Γ : ProperCurve sV) (Γ' : ProperCurve sT)
    (hΓ' : Γ'.point = u Γ.point) :
    D'.degreeOn k sV Γ.ι Γ.dim_le (h.isCartier hD) =
      (residueFieldDegree u Γ.point : ℤ) * D.degreeOn k sT Γ'.ι Γ'.dim_le hD := by
  have := QuasiCompact.compactSpace_of_compactSpace sT
  have := QuasiCompact.compactSpace_of_compactSpace sV
  obtain rfl := h.eq hD (Divisor.isPullback_pullback hD hB)
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward u hu hD hB Γ, OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos (hΓ' ▸ Γ'.isProperCurve)]
  obtain ⟨pt, hpt⟩ := Γ'
  simp only at hΓ'
  subst hΓ'
  simp [OneCycle.degree, Finsupp.linearCombination_single, ProperCurve.degree, Divisor.degreeOn]

/-- The pull-back of a `ℚ`-Cartier `ℚ`-divisor has intersection number zero with a contracted
curve. -/
private theorem intersectionNumber_isPullback_eq_zero (u : V ⟶ T) (hu : u ≫ sT = sV)
    {L : QDivisor T} (hL : L.IsQCartier)
    {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hB L') (Γ : ProperCurve sV) (hΓ : Γ.IsContractedBy u) :
    L'.intersectionNumber k sV Γ.ι Γ.dim_le (h.isQCartier hL) = 0 := by
  obtain ⟨D, D', hDc, hDB, -, hD', hp⟩ := h.exists_cartierIndex hL
  rw [QDivisor.intersectionNumber_eq_of_smul k sV Γ.ι _ _ _ (QDivisor.cartierIndex_pos hL) D'
    (hp.isCartier hDc) hD', degreeOn_isPullback_eq_zero u hu hDc hp Γ hΓ]
  simp

/-- **Projection formula** for `ℚ`-Cartier `ℚ`-divisors:
`(u^*L · Γ) = [k(Γ) : k(Γ')] · (L · Γ')` for the image curve `Γ'` of `Γ`. -/
private theorem intersectionNumber_isPullback_eq_mul (u : V ⟶ T) (hu : u ≫ sT = sV)
    {L : QDivisor T} (hL : L.IsQCartier)
    {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hB L') (Γ : ProperCurve sV) (Γ' : ProperCurve sT)
    (hΓ' : Γ'.point = u Γ.point) :
    L'.intersectionNumber k sV Γ.ι Γ.dim_le (h.isQCartier hL) =
      (residueFieldDegree u Γ.point : ℚ) * L.intersectionNumber k sT Γ'.ι Γ'.dim_le hL := by
  obtain ⟨D, D', hDc, hDB, hD, hD', hp⟩ := h.exists_cartierIndex hL
  rw [QDivisor.intersectionNumber_eq_of_smul k sV Γ.ι _ _ _ (QDivisor.cartierIndex_pos hL) D'
    (hp.isCartier hDc) hD', QDivisor.intersectionNumber_eq_of_smul k sT Γ'.ι _ _ _
    (QDivisor.cartierIndex_pos hL) D hDc hD, degreeOn_isPullback_eq_mul u hu hDc hp Γ Γ' hΓ']
  push_cast
  ring

/-- **Nefness of a pull-back.** If `L` is `π`-nef, then `u^*L` has nonnegative intersection
number with every curve contracted by `u ≫ π`: either `u` contracts the curve, or its image is a
curve contracted by `π` and the projection formula applies. -/
private theorem intersectionNumber_isPullback_nonneg {S : Scheme.{u}} (u : V ⟶ T)
    (hu : u ≫ sT = sV) (π : T ⟶ S) {L : QDivisor T} (hL : L.IsQCartier)
    (hn : L.IsRelativelyNef sT π)
    {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hB L') (Γ : ProperCurve sV)
    (hΓ : Γ.IsContractedBy (u ≫ π)) :
    0 ≤ L'.intersectionNumber k sV Γ.ι Γ.dim_le (h.isQCartier hL) := by
  by_cases hc : Γ.IsContractedBy u
  · rw [intersectionNumber_isPullback_eq_zero u hu hL h Γ hc]
  · rw [intersectionNumber_isPullback_eq_mul u hu hL h Γ ⟨_, isProperCurve_map u hu Γ hc⟩ rfl]
    exact mul_nonneg (by positivity)
      (MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sT hn hL _
        (isContractedBy_map u hu π Γ hc hΓ))

end Pullback

end MMP.Fourfold.ChainComparison

namespace MMP.Fourfold.ChainComparison.GraphDivisor

open MMP.Mori MMP.Fourfold

/-- A `ℚ`-divisor with a `g`-ample multiple is `v`-nef for every `v` whose contracted curves are
contracted by `g`: on such a curve its intersection number is a positive degree divided by a
positive integer. -/
private theorem isRelativelyNef_of_hasRelativelyAmpleMultiple {X Y W : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] {g : X ⟶ W} {v : X ⟶ Y} {D : QDivisor X}
    (hD : D.HasRelativelyAmpleMultiple g)
    (hvg : ∀ C : ProperCurve sX, C.IsContractedBy v → C.IsContractedBy g) :
    D.IsRelativelyNef sX v := by
  obtain ⟨m, hm, L, hLc, hL, hamp⟩ := hD
  have hDq : D.IsQCartier := ⟨m, by exact_mod_cast hm.ne', L, hL, hLc⟩
  refine QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hDq fun C hC => ?_
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sX C.ι C.dim_le D hDq hm L hLc hL]
  have := hLc.isInvertibleModule_divisorialSheaf
  have := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy
    g _ hamp C (hvg C hC)
  exact (div_pos (Int.cast_pos.mpr this) (Nat.cast_pos.mpr hm)).le

end MMP.Fourfold.ChainComparison.GraphDivisor

namespace MMP.Fourfold

open MMP.Fourfold.ChainComparison MMP.Fourfold.ChainComparison.GraphDivisor

open MMP.Mori

variable {Xm Xp Z G : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsLocallyNoetherian G] [IsNormal G]

/-- **The graph divisor is effective.** For a step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)` with
normalized graph `(G, u, v)` and graph divisor `H = u^* D⁻ - v^* D⁺`, we have `0 ≤ H`. -/
@[mmp "lem_oai4_c1_graph_h_effective"]
public theorem IsGraphDivisor.nonneg
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp}
    {H : QDivisor G} (h : IsGraphDivisor sXm sZ sXp K B fm fp u v H) :
    0 ≤ H := by
  have hD := h.isFourfoldStepDiagram
  have hG := h.isNormalizedGraph
  have := hG.isIntegral
  have : IsProper fm := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  have : IsProper fp := hD.isProper_plus
  have : IsFinite (Limits.pullback.lift u v hG.comp_eq) := hG.isFinite
  have : IsProper v := by
    rw [← Limits.pullback.lift_snd u v hG.comp_eq]
    infer_instance
  have : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace v
  have := hD.isNormalVariety_plus.1
  have hnef : (-H).IsRelativelyNef (v ≫ sXp) v :=
    isRelativelyNef_of_hasRelativelyAmpleMultiple _ h.hasRelativelyAmpleMultiple_neg
      fun C hC x hx => by
        rw [hG.comp_eq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]
  exact DivisorWithCoeffs.isEffective_iff_nonneg.mp <|
    QDivisor.isEffective_of_isEffective_transformDivisor_of_isRelativelyNef_neg ℂ sXp (v ≫ sXp)
      hD.isNormalVariety_plus ⟨⟨⟩, inferInstance⟩ v rfl hG.isBirationalMorphism_plus
      (by simpa using isQCartier_neg hnef.1) hnef
      (by rw [h.transformDivisor_eq_zero]; exact DivisorWithCoeffs.isEffective_zero)

end MMP.Fourfold

namespace MMP.Fourfold.ChainComparison.FiniteChain

open MMP.Mori MMP.Fourfold

/-- A morphism `u` with `u ≫ s` proper and `s` separated is proper. -/
private theorem isProper_of_comp_eq {W V : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} [IsProper sW]
    {sV : V ⟶ Spec (.of ℂ)} [IsSeparated sV] (u : W ⟶ V) (hu : u ≫ sV = sW) : IsProper u := by
  subst hu
  exact IsProper.of_comp u sV

/-- **The comparison divisor of one step is anti-nef.** Let `(X⁻, Θ⁻) → T ← (X⁺, Θ⁺)` be a step
diagram with `K⁺ + Θ⁺` the strict transform of `K⁻ + Θ⁻`, and let `q : W ⟶ X⁻`, `p : W ⟶ X⁺` be
proper with `q ≫ g = p ≫ g⁺`. Then `-(q^*(K⁻ + Θ⁻) - p^*(K⁺ + Θ⁺))` is `p`-nef: a curve contracted
by `p` is contracted by `q ≫ g = p ≫ g⁺`, and on it both `p^*(K⁺ + Θ⁺)` and `q^*(-(K⁻ + Θ⁻))` are
pull-backs of relatively ample divisors. -/
private theorem isRelativelyNef_neg_pullback_sub_pullback
    {Xm Xp T W : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
    [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {Θ : QDivisor Xm} {g : Xm ⟶ T} {gp : Xp ⟶ T}
    (hS : IsFourfoldStepDiagram sXm sT sXp K Θ g gp) {Kp : Divisor Xp} {Θp : QDivisor Xp}
    (hK : Kp = flipTransform g gp K) (hΘ : Θp = flipTransform g gp Θ)
    (sW : W ⟶ Spec (.of ℂ)) [QuasiCompact sW] {q : W ⟶ Xm} {p : W ⟶ Xp} [IsProper q] [IsProper p]
    [IsDominant q] (hqs : q ≫ sXm = sW) (hps : p ≫ sXp = sW) (hcomp : q ≫ g = p ≫ gp)
    {h₁ : ∀ Z : irreducibleComponents W,
      q (componentGenericPoint W Z) ∉ (Divisor.toQDivisor K + Θ).supp}
    {h₂ : ∀ Z : irreducibleComponents W,
      p (componentGenericPoint W Z) ∉ (Divisor.toQDivisor Kp + Θp).supp}
    {P₁ P₂ : QDivisor W} (hp₁ : (Divisor.toQDivisor K + Θ).IsPullback q h₁ P₁)
    (hp₂ : (Divisor.toQDivisor Kp + Θp).IsPullback p h₂ P₂) (hP₁ : P₁.IsQCartier)
    (hP₂ : P₂.IsQCartier) :
    (-(P₁ - P₂)).IsRelativelyNef sW p := by
  subst hK hΘ
  have := hS.isNormalVariety_minus.1
  have := hS.isNormalVariety_plus.1
  rw [show -(P₁ - P₂) = P₂ + -P₁ by abel]
  refine QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sW
    (hP₂.add (isQCartier_neg hP₁)) fun C hC => ?_
  rw [QDivisor.intersectionNumber_add' ℂ sW C.ι C.dim_le _ _ hP₂ (isQCartier_neg hP₁)]
  refine add_nonneg (intersectionNumber_nonneg_of_isPullback p hps
    hS.hasRelativelyAmpleMultiple_plus hp₂ hP₂ C fun x hx => by
      simp only [Scheme.Hom.comp_apply, hC x hx]) ?_
  refine intersectionNumber_nonneg_of_isPullback q hqs hS.hasRelativelyAmpleMultiple_minus
    (isPullback_neg hp₁
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _))
    (isQCartier_neg hP₁) C fun x hx => ?_
  rw [hcomp]
  simp only [Scheme.Hom.comp_apply, hC x hx]

/-- **One step of the chain.** For the `k`-th step diagram `(V_k, Θ_k) → T_k ← (V_{k+1}, Θ_{k+1})`
and the birational morphisms `q_k`, `q_{k+1}` from `W`, the divisor
`E = q_k^*(K_k + Θ_k) - q_{k+1}^*(K_{k+1} + Θ_{k+1})` is effective, by the negativity lemma for
`q_{k+1}`: `-E` is `q_{k+1}`-nef (`isRelativelyNef_neg_pullback_sub_pullback`) and
`(q_{k+1})_* E = 0`. -/
private theorem pullback_sub_pullback_nonneg
    {V : ℕ → Scheme.{0}} (sV : ∀ k, V k ⟶ Spec (.of ℂ)) [∀ k, IsIntegral (V k)]
    [∀ k, CompactSpace (V k)] [∀ k, IsLocallyNoetherian (V k)] [∀ k, IsNormal (V k)]
    (K : ∀ k, Divisor (V k)) (Θ : ∀ k, QDivisor (V k))
    {T : ℕ → Scheme.{0}} (sT : ∀ k, T k ⟶ Spec (.of ℂ))
    (g : ∀ k, V k ⟶ T k) (gp : ∀ k, V (k + 1) ⟶ T k) (k : ℕ)
    (hS : IsFourfoldStepDiagram (sV k) (sT k) (sV (k + 1)) (K k) (Θ k) (g k) (gp k))
    (hK : K (k + 1) = flipTransform (g k) (gp k) (K k))
    (hΘ : Θ (k + 1) = flipTransform (g k) (gp k) (Θ k))
    {W : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    (sW : W ⟶ Spec (.of ℂ)) (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hWn : IsNormalVariety ℂ sW) (q : ∀ k, W ⟶ V k) (hqs₁ : q k ≫ sV k = sW)
    (hqs₂ : q (k + 1) ≫ sV (k + 1) = sW) (hq₁ : IsBirationalMorphism (q k))
    (hq₂ : IsBirationalMorphism (q (k + 1))) (hcomp : q k ≫ g k = q (k + 1) ≫ gp k)
    (hD₁ : (Divisor.toQDivisor (K k) + Θ k).IsQCartier)
    (hD₂ : (Divisor.toQDivisor (K (k + 1)) + Θ (k + 1)).IsQCartier)
    (h₁ : ∀ Z : irreducibleComponents W,
      q k (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (K k) + Θ k).supp)
    (h₂ : ∀ Z : irreducibleComponents W,
      q (k + 1) (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (K (k + 1)) + Θ (k + 1)).supp) :
    0 ≤ (Divisor.toQDivisor (K k) + Θ k).pullback hD₁ h₁ -
      (Divisor.toQDivisor (K (k + 1)) + Θ (k + 1)).pullback hD₂ h₂ := by
  have := hS.isNormalVariety_minus.1
  have := hS.isNormalVariety_plus.1
  have := isProper_of_comp_eq (q k) hqs₁
  have := isProper_of_comp_eq (q (k + 1)) hqs₂
  have := hq₁.isDominant
  have hp₁ := QDivisor.isPullback_pullback hD₁ h₁
  have hp₂ := QDivisor.isPullback_pullback hD₂ h₂
  have hP₁ := hp₁.isQCartier hD₁
  have hP₂ := hp₂.isQCartier hD₂
  have h0 := transformDivisor_pullback_sub_pullback_eq_zero 1 (V := fun j => V (k + j))
    (fun j => sV (k + j)) (fun j => K (k + j)) (fun j => Θ (k + j)) (T := fun j => T (k + j))
    (fun j => sT (k + j)) (fun j => g (k + j)) (fun j => gp (k + j))
    (fun j hj => by obtain rfl := Nat.lt_one_iff.mp hj; exact hS)
    (fun j hj => by obtain rfl := Nat.lt_one_iff.mp hj; exact hK)
    (fun j hj => by obtain rfl := Nat.lt_one_iff.mp hj; exact hΘ)
    (fun j => q (k + j)) (fun j hj => by
      obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.mp hj
      exacts [hq₁, hq₂])
    (fun j hj => by obtain rfl := Nat.lt_one_iff.mp hj; exact hcomp) hD₁ hD₂ h₁ h₂
  exact DivisorWithCoeffs.isEffective_iff_nonneg.mp <|
    QDivisor.isEffective_of_isEffective_transformDivisor_of_isRelativelyNef_neg ℂ (sV (k + 1)) sW
      hS.isNormalVariety_plus hWn (q (k + 1)) hqs₂ hq₂
      (by rw [sub_eq_add_neg]; exact hP₁.add (isQCartier_neg hP₂))
      (isRelativelyNef_neg_pullback_sub_pullback hS hK hΘ sW hqs₁ hqs₂ hcomp hp₁ hp₂ hP₁ hP₂)
      ((congrArg (·.IsEffective) h0).mpr DivisorWithCoeffs.isEffective_zero)

end MMP.Fourfold.ChainComparison.FiniteChain

namespace MMP.Fourfold

open MMP.Fourfold.ChainComparison.FiniteChain

open MMP.Mori

/-- **The comparison divisor of a finite chain of step diagrams is effective.** For fourfold
step diagrams `(V_k, Θ_k) → T_k ← (V_{k+1}, Θ_{k+1})`, `k < m`, with transported canonical
divisors `K_{k+1} = (g_k⁺)⁻¹_* (g_k)_* K_k` and boundaries `Θ_{k+1} = (g_k⁺)⁻¹_* (g_k)_* Θ_k`, and
birational morphisms `q_k : W ⟶ V_k`, `k ≤ m`, over `ℂ` from a smooth projective variety `W` with
`q_k ≫ g_k = q_{k+1} ≫ g_k⁺`, the `ℚ`-divisor `q_0^*(K_0 + Θ_0) - q_m^*(K_m + Θ_m)` is
effective. -/
@[mmp "lem_oai4_c1_finite_program_comparison"]
public theorem pullback_sub_pullback_nonneg_of_isFourfoldStepDiagram (m : ℕ)
    {V : ℕ → Scheme.{0}} (sV : ∀ k, V k ⟶ Spec (.of ℂ)) [∀ k, IsIntegral (V k)]
    [∀ k, CompactSpace (V k)] [∀ k, IsLocallyNoetherian (V k)] [∀ k, IsNormal (V k)]
    (K : ∀ k, Divisor (V k)) (Θ : ∀ k, QDivisor (V k))
    {T : ℕ → Scheme.{0}} (sT : ∀ k, T k ⟶ Spec (.of ℂ))
    (g : ∀ k, V k ⟶ T k) (gp : ∀ k, V (k + 1) ⟶ T k)
    (hstep : ∀ k < m,
      IsFourfoldStepDiagram (sV k) (sT k) (sV (k + 1)) (K k) (Θ k) (g k) (gp k))
    (hK : ∀ k < m, K (k + 1) = flipTransform (g k) (gp k) (K k))
    (hΘ : ∀ k < m, Θ (k + 1) = flipTransform (g k) (gp k) (Θ k))
    {W : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    (sW : W ⟶ Spec (.of ℂ)) (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hWn : IsNormalVariety ℂ sW) (hWs : IsSmoothScheme sW)
    (q : ∀ k, W ⟶ V k) (hqs : ∀ k ≤ m, q k ≫ sV k = sW)
    (hq : ∀ k ≤ m, IsBirationalMorphism (q k))
    (hcomp : ∀ k < m, q k ≫ g k = q (k + 1) ≫ gp k)
    (hD₀ : (Divisor.toQDivisor (K 0) + Θ 0).IsQCartier)
    (hDₘ : (Divisor.toQDivisor (K m) + Θ m).IsQCartier)
    (h₀ : ∀ Z : irreducibleComponents W,
      q 0 (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (K 0) + Θ 0).supp)
    (hₘ : ∀ Z : irreducibleComponents W,
      q m (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (K m) + Θ m).supp) :
    0 ≤ (Divisor.toQDivisor (K 0) + Θ 0).pullback hD₀ h₀ -
      (Divisor.toQDivisor (K m) + Θ m).pullback hDₘ hₘ := by
  have hgen : ∀ k ≤ m, ∀ Z : irreducibleComponents W,
      q k (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (K k) + Θ k).supp := fun k hk => by
    have := (hq k hk).isDominant
    exact MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _
  have hQ : ∀ k ≤ m, (Divisor.toQDivisor (K k) + Θ k).IsQCartier := fun k hk => by
    rcases hk.lt_or_eq with h | rfl
    · exact (hstep k h).isQCartier_minus
    · exact hDₘ
  have key : ∀ j (hj : j ≤ m), 0 ≤ (Divisor.toQDivisor (K 0) + Θ 0).pullback hD₀ h₀ -
      (Divisor.toQDivisor (K j) + Θ j).pullback (hQ j hj) (hgen j hj) := by
    intro j
    induction j with
    | zero => intro _; exact (sub_self _).symm.le
    | succ j ih =>
      intro hj
      have h := add_nonneg (ih (by omega)) (pullback_sub_pullback_nonneg sV K Θ sT g gp j
        (hstep j hj) (hK j hj) (hΘ j hj) sW hW hWn q (hqs j (by omega)) (hqs (j + 1) hj)
        (hq j (by omega)) (hq (j + 1) hj) (hcomp j hj) (hQ j (by omega)) (hQ (j + 1) hj)
        (hgen j (by omega)) (hgen (j + 1) hj))
      rwa [sub_add_sub_cancel] at h
  exact key m le_rfl

end MMP.Fourfold

namespace MMP.Fourfold.ChainComparison.Bridge

open MMP.Mori MMP.Fourfold

open MMP.Fourfold.StabilizedSmallKltTail

/-! ### Prime divisors under birational morphisms -/

section Helpers

variable {X Y : Scheme.{0}}

/-- A separated birational morphism is injective over a point whose local ring is a valuation
ring. -/
private theorem eq_of_map_eq_of_valuationRing [IsIntegral X] [IsIntegral Y] {f : X ⟶ Y}
    [IsSeparated f] [IsDominant f] (hμ : Function.Bijective (functionFieldMap f)) {y : Y}
    [ValuationRing (Y.presheaf.stalk y)] {x₁ x₂ : X} (h₁ : f x₁ = y) (h₂ : f x₂ = y) :
    x₁ = x₂ := by
  subst h₁
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hμ x₁
  have : ValuationRing (Y.presheaf.stalk (f x₂)) := by rw [h₂]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hμ x₂
  exact MMP.Positivity.eq_of_isIso_stalkMap f hμ h₂

/-- A birational morphism onto a normal scheme is a local isomorphism at every point over the
generic point of a prime divisor. -/
private theorem isIso_stalkMap_of_map_eq_genericPoint [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} (hf : IsBirationalMorphism f)
    {x : X} {P : MMP.Mori.PrimeDivisor Y} (hx : f x = P.genericPoint) :
    IsIso (f.stalkMap x) := by
  have := P.isDiscreteValuationRing_localRing
  have := hf.isDominant
  have : ValuationRing (Y.presheaf.stalk (f x)) := by rw [hx]; infer_instance
  exact MMP.Positivity.isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective x

/-- A separated birational morphism onto a normal scheme has at most one point over the generic
point of a prime divisor. -/
private theorem eq_of_map_eq_genericPoint [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {f : X ⟶ Y} [IsSeparated f] (hf : IsBirationalMorphism f)
    {Q : MMP.Mori.PrimeDivisor Y} {x₁ x₂ : X} (h₁ : f x₁ = Q.genericPoint)
    (h₂ : f x₂ = Q.genericPoint) : x₁ = x₂ := by
  have := Q.isDiscreteValuationRing_localRing
  have := hf.isDominant
  exact eq_of_map_eq_of_valuationRing hf.functionFieldMap_bijective h₁ h₂

/-- If `f(η_E) = η_Q` and `f^♯ : 𝒪_{Y,Q} ⟶ 𝒪_{X,E}` is an isomorphism, then `v_E`, seen on
`k(Y)` through `f`, is `v_Q`. -/
private theorem valuationOver_eq_of_isIso [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsDominant f]
    (E : MMP.Mori.PrimeDivisor X) (Q : MMP.Mori.PrimeDivisor Y)
    (heq : f E.genericPoint = Q.genericPoint) [IsIso (f.stalkMap E.genericPoint)] :
    E.valuationOver f = Q.divisorialValuation := by
  refine Valuation.ext fun t => ?_
  rw [PrimeDivisor.valuationOver_apply]
  by_cases ht : t = 0
  · rw [ht, map_zero, map_zero, map_zero]
  rw [PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso f E Q heq t]

/-- Let `E ⊆ X`, `P ⊆ Y` be prime divisors with `f(η_E) = η_P` and `𝒪_{Y,P} ≅ 𝒪_{X,E}`. The
coefficient of `E` in the pull-back of a `ℚ`-Cartier `ℚ`-divisor `B` is the coefficient of `P`
in `B`. -/
private theorem coeff_eq_of_isPullback_qDivisor [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} (E : MMP.Mori.PrimeDivisor X)
    (P : MMP.Mori.PrimeDivisor Y) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] {B : QDivisor Y} (hBq : B.IsQCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : QDivisor X} (hB' : B.IsPullback f hB B') : B' E = B P := by
  have hm := QDivisor.cartierIndex_pos hBq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hBq
  obtain ⟨D', hD', hp⟩ := hB' _ hm D₀ hD₀ hD₀c
  have hc := MMP.Positivity.coeff_eq_of_isPullback E P heq hD₀c hp
  have h1 := congrArg (fun G : QDivisor X => G E) hD'
  have h2 := congrArg (fun G : QDivisor Y => G P) hD₀
  simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h1 h2
  refine mul_left_cancel₀ (by exact_mod_cast hm.ne') (h1.symm.trans (Eq.trans ?_ h2))
  exact congrArg (fun z : ℤ => (z : ℚ)) hc

/-- The transform `φ_* D` has coefficient zero at a prime divisor which is the transform of no
prime divisor. -/
private theorem mapPrimeDivisors_apply_eq_zero {R : Type*} [AddCommMonoid R]
    {φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)} {P : MMP.Mori.PrimeDivisor Y}
    (h : ∀ E, φ E ≠ some P) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ D P = 0 := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, Finsupp.add_apply, hD, hD', add_zero]
  | single E r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases hφ : φ E with _ | Q
    · rfl
    · have hQ : Q ≠ P := fun hQ => h E (hφ.trans (congrArg some hQ))
      exact Finsupp.single_eq_of_ne (Ne.symm hQ)

/-- Along a separated birational morphism onto a normal scheme, the transform of a divisor has,
at a prime divisor `Q`, the coefficient of the prime divisor `P` over it. -/
private theorem transformDivisor_apply_of_map_genericPoint [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsSeparated (Y ↘ Limits.terminal Scheme)]
    {f : X ⟶ Y} [IsSeparated f] (hf : IsBirationalMorphism f) {P : MMP.Mori.PrimeDivisor X}
    {Q : MMP.Mori.PrimeDivisor Y} (h : f P.genericPoint = Q.genericPoint) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) :
    RationalMap.transformDivisor (X := X) f.toRationalMap D Q = D P :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mpr h)
    (fun E' hE' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      eq_of_map_eq_genericPoint hf
        ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f E' Q).mp hE') h) D

/-- Over the biregular locus, the inverse transform of a divisor has, at `P`, the coefficient of
the prime divisor `Q` under `P`. -/
private theorem inverseTransformDivisor_apply_of_map_genericPoint {g : X ⟶ Y}
    {P : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (h : g P.genericPoint = Q.genericPoint) (hV : Q.genericPoint ∈ biregularLocus g)
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R Y) :
    inverseTransformDivisor g D P = D Q :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint h
      (h ▸ hV))
    (fun _ hQ' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hQ').1.symm.trans h)) D

/-- **A proper birational morphism onto a normal scheme is an isomorphism over the generic point
of every prime divisor**: the fibre over it is a single point, so it lies in the finite-fibre
locus. -/
private theorem genericPoint_mem_biregularLocus [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsProper f] (hf : IsBirationalMorphism f)
    (Q : MMP.Mori.PrimeDivisor Y) : Q.genericPoint ∈ biregularLocus f := by
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)).1 inferInstance
  refine le_biregularLocus (f := f) (V := ⟨_, hU⟩) hiso ?_
  exact Set.Subsingleton.finite fun x₁ h₁ x₂ h₂ => eq_of_map_eq_genericPoint hf h₁ h₂

/-- A morphism whose exceptional set has codimension at least two is biregular over the image
of the generic point of every prime divisor. -/
private theorem map_genericPoint_mem_biregularLocus {f : X ⟶ Y}
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f)) (P : MMP.Mori.PrimeDivisor X) :
    f P.genericPoint ∈ biregularLocus f := by
  by_contra h
  have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2 (mem_exceptionalSet.mpr h)
  rw [P.coheight_genericPoint] at this
  exact absurd this (by decide)

/-- Pull-backs of rational functions compose along dominant morphisms of integral schemes. -/
private theorem functionFieldMap_comp_apply {A B C : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] {c : A ⟶ C}
    [IsDominant c] (hc : a ≫ b = c) (t : C.functionField) :
    functionFieldMap a (functionFieldMap b t) = functionFieldMap c t := by
  subst hc
  have := Scheme.Hom.stalkMapOfEq_comp a b (genericPoint A) (genericPoint B) (genericPoint C)
    (map_genericPoint_of_isDominant a) (map_genericPoint_of_isDominant b)
    (map_genericPoint_of_isDominant (a ≫ b))
  exact (congrArg (fun φ => φ.hom t) this).symm

/-- Valuations with the same pull-back along a surjective ring map are equal. -/
private theorem valuation_eq_of_comap_eq {K L Γ₀ : Type*} [Ring K] [Ring L]
    [LinearOrderedCommGroupWithZero Γ₀] {e : K →+* L} (he : Function.Surjective e)
    {v w : Valuation L Γ₀} (h : v.comap e = w.comap e) : v = w := by
  refine Valuation.ext fun x => ?_
  obtain ⟨y, rfl⟩ := he x
  exact congrArg (fun u : Valuation K Γ₀ => u y) h

end Helpers

/-! ### The log discrepancy read on a model -/

/-- **The log discrepancy on a model with compatible canonical divisors.** Let `(X, B)` be a
normal variety with canonical divisor `K` and `K + B` `ℚ`-Cartier, `r : W ⟶ X` a proper
birational morphism from a normal variety with canonical divisor `K_W`, `r_* K_W = K`, and
`R = r^*(K + B)`. If a divisor over `X` with log discrepancy `a` has the valuation of a prime
divisor `P` of `W`, then `coeff_P R = coeff_P K_W + 1 - a`, that is,
`a = 1 + coeff_P (K_W - r^*(K + B))`. -/
private theorem coeff_isPullback_eq_of_isLogDiscrepancy {X W : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [CompactSpace W] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {d : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX d)
    {B : QDivisor X} (hKB : (Divisor.toQDivisor K + B).IsQCartier) {r : W ⟶ X} [IsProper r]
    (hr : IsBirationalMorphism r) (hW : IsNormalVariety ℂ (r ≫ sX))
    [LocallyOfFiniteType (r ≫ sX)] {KW : Divisor W} (hKW : KW.IsCanonicalDivisor (r ≫ sX) d)
    (hKX : RationalMap.transformDivisor (X := W) r.toRationalMap KW = K)
    {hR₀ : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor K + B).supp}
    {R : QDivisor W} (hR : (Divisor.toQDivisor K + B).IsPullback r hR₀ R)
    (P : MMP.Mori.PrimeDivisor W) {n : ℕ} {D : DivisorOver ℂ sX} {a : ℝ}
    (hD : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a)
    (hv : D.valuation = (⟨W, r, hW, hr, P⟩ : DivisorOver ℂ sX).valuation) :
    (R P : ℝ) = (KW P : ℝ) + 1 - a := by
  have := hr.isDominant
  obtain ⟨ω, hω0, hωK, hωW⟩ :=
    MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hX hW hr hK hKW hKX
  obtain ⟨m, hm, L, hL, hLc⟩ := hKB.exists_pos
  obtain ⟨L', hL'q, hLp⟩ := hR m hm L hL hLc
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hlog : MMP.Intersection.IsLogDiscrepancy sX d (QDivisor.toRDivisor B)
      (⟨W, r, hW, hr, P⟩ : DivisorOver ℂ sX) (1 + KW P - R P) := by
    refine ⟨hX, inferInstance, ω, hω0, ⟨K, hK, fun Γ => by rw [← hωK]; rfl⟩, 1,
      fun _ => ((m : ℝ)⁻¹), fun _ => L, fun _ => L', fun _ => hLc, fun Γ => ?_,
      fun _ => ⟨_, hLp⟩, ?_⟩
    · have h1 := congrArg (fun G : QDivisor X => G Γ) hL
      have h2 : Γ.ordForm ω = K Γ := by rw [← hωK]; rfl
      simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast, Finsupp.add_apply] at h1
      change ((L Γ : ℤ) : ℚ) = m * (((K Γ : ℤ) : ℚ) + B Γ) at h1
      simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
        QDivisor.coeff_toRDivisor, h2]
      change (((K Γ : ℤ) : ℝ)) + ((B Γ : ℚ) : ℝ) = (m : ℝ)⁻¹ * ((L Γ : ℤ) : ℝ)
      have h3 : ((L Γ : ℤ) : ℝ) = (m : ℝ) * (((K Γ : ℤ) : ℝ) + ((B Γ : ℚ) : ℝ)) := by
        exact_mod_cast h1
      rw [h3]
      field_simp
    · have h1 := congrArg (fun G : QDivisor W => G P) hL'q
      simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h1
      change ((L' P : ℤ) : ℚ) = m * R P at h1
      have h2 : DivisorOver.ordPullback (⟨W, r, hW, hr, P⟩ : DivisorOver ℂ sX) ω = KW P := by
        rw [← hωW]; rfl
      simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, h2]
      change 1 + ((KW P : ℤ) : ℝ) - ((R P : ℚ) : ℝ) =
        1 + ((KW P : ℤ) : ℝ) - (m : ℝ)⁻¹ * ((L' P : ℤ) : ℝ)
      have h3 : ((L' P : ℤ) : ℝ) = (m : ℝ) * ((R P : ℚ) : ℝ) := by exact_mod_cast h1
      rw [h3]
      field_simp
  have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hD hlog hv
  linarith

/-- **`-(A - R)` is relatively nef.** Let `q : W ⟶ Y`, `r : W ⟶ V` be proper morphisms with
`q ≫ h = r ≫ g`, `D_Y` a `ℚ`-Cartier `ℚ`-divisor on `Y` and `D_V` a `ℚ`-divisor on `V` with a
`g`-ample multiple. Then `r^* D_V - q^* D_Y` is `q`-nef: on a curve contracted by `q`, `q^* D_Y`
has degree zero, and `r^* D_V` has nonnegative degree, the curve being contracted by `r ≫ g`. -/
private theorem isRelativelyNef_neg_sub_of_isPullback {W V Y T : Scheme.{0}} [IsIntegral W]
    [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace V] [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] {sW : W ⟶ Spec (.of ℂ)}
    [QuasiCompact sW] {sV : V ⟶ Spec (.of ℂ)} [IsSeparated sV] [LocallyOfFiniteType sV]
    {sY : Y ⟶ Spec (.of ℂ)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    {q : W ⟶ Y} [IsDominant q] (hq : q ≫ sY = sW) {r : W ⟶ V} [IsProper r] (hr : r ≫ sV = sW)
    {h : Y ⟶ T} {g : V ⟶ T} (hcomp : q ≫ h = r ≫ g) {DY : QDivisor Y} (hDY : DY.IsQCartier)
    {DV : QDivisor V} (hDV : DV.IsQCartier) (hamp : DV.HasRelativelyAmpleMultiple g)
    {hA₀ : ∀ Z : irreducibleComponents W, q (componentGenericPoint W Z) ∉ DY.supp}
    {hR₀ : ∀ Z : irreducibleComponents W, r (componentGenericPoint W Z) ∉ DV.supp}
    {A R : QDivisor W} (hA : DY.IsPullback q hA₀ A) (hR : DV.IsPullback r hR₀ R) :
    (-(A - R)).IsRelativelyNef sW q := by
  have hRq := hR.isQCartier hDV
  have hnAq := isQCartier_neg (hA.isQCartier hDY)
  rw [show -(A - R) = R + -A by abel]
  refine QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sW (hRq.add hnAq) fun C hC => ?_
  rw [QDivisor.intersectionNumber_add' ℂ sW C.ι C.dim_le _ _ hRq hnAq]
  refine add_nonneg (intersectionNumber_nonneg_of_isPullback r hr hamp hR hRq C fun x hx => ?_)
    (intersectionNumber_isPullback_eq_zero q hq (isQCartier_neg hDY) (isPullback_neg hA
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _)) C hC).ge
  rw [← hcomp]
  simp only [Scheme.Hom.comp_apply, hC x hx]

/-! ### The decreased boundary -/

section DecreasedBoundary

variable {T : StabilizedSmallKltTail} {i : ℕ}
  {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
  {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {a : I → ℚ} {Θ' : QDivisor J.Y}

/-- The canonical divisor of the tail at `X_j` is a canonical divisor of dimension four. -/
private theorem isCanonicalDivisor_K (j : ℕ) : (T.K j).IsCanonicalDivisor (T.sX j) 4 := by
  obtain ⟨m, hm⟩ := (T.isFourfoldStepDiagram j).isCanonicalDivisor
  have h4 := hm.topologicalKrullDim_eq
  rw [(T.isFourfoldStepDiagram j).dim_minus] at h4
  obtain rfl : m = 4 := by exact_mod_cast h4.symm
  exact hm

/-- The decreased boundary `Θ_i' = (p_i)⁻¹_* B_i + ∑ (1 - a(s)) E_{i,s}` has coefficient
`1 - a(s)` at the marked divisor `E_{i,s}`: it is `p_i`-exceptional, so no prime divisor of
`X_i` has it as strict transform. -/
private theorem decreasedBoundary_apply_E
    (hΘ' : Θ' = inverseTransformDivisor J.p (T.B i) + ∑ s : I, Finsupp.single (J.E s) (1 - a s))
    (s : I) : Θ' (J.E s) = 1 - a s := by
  have hXi := (T.isFourfoldStepDiagram i).isNormalVariety_minus
  have := isSeparated_toTerminal_of_isNormalVariety hXi
  have hinv : inverseTransformDivisor J.p (T.B i) (J.E s) = 0 := by
    refine mapPrimeDivisors_apply_eq_zero (fun D hD => ?_) _
    have hη :=
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hD).1
    have hex := MMP.Positivity.isExceptional_toRationalMap_iff (f := J.p) (J.E s) |>.mp
      ((J.isExceptional_iff _).mpr ⟨s, rfl⟩)
    have h2 := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hex _ <|
      subset_closure ⟨(J.E s).genericPoint, by
        change (J.E s).genericPoint ∈ (J.E s).support
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl, hη⟩
    rw [D.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  rw [hΘ', Finsupp.add_apply, hinv, zero_add, Finsupp.finsetSum_apply,
    Finset.sum_eq_single s
      (fun t _ hts => Finsupp.single_eq_of_ne fun h => hts (J.injective h.symm))
      (fun h => absurd (Finset.mem_univ s) h)]
  exact Finsupp.single_eq_same

/-- At a prime divisor `Q` of `Y_i` which is not marked, lying over the prime divisor `Q₀` of
`X_i`, the decreased boundary has the coefficient of `B_i` at `Q₀`. -/
private theorem decreasedBoundary_apply_of_notMem_range
    (hΘ' : Θ' = inverseTransformDivisor J.p (T.B i) + ∑ s : I, Finsupp.single (J.E s) (1 - a s))
    {Q : MMP.Mori.PrimeDivisor J.Y} (hQE : Q ∉ Set.range J.E) {Q₀ : MMP.Mori.PrimeDivisor (T.X i)}
    (hQ₀ : J.p Q.genericPoint = Q₀.genericPoint) : Θ' Q = T.B i Q₀ := by
  have : IsProper J.p := isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism
  rw [hΘ', Finsupp.add_apply, inverseTransformDivisor_apply_of_map_genericPoint hQ₀
    (genericPoint_mem_biregularLocus J.p J.isBirationalMorphism Q₀),
    Finsupp.finsetSum_apply, Finset.sum_eq_zero (fun t _ => ?_), add_zero]
  exact Finsupp.single_eq_of_ne fun h => hQE ⟨t, h.symm⟩

end DecreasedBoundary

end MMP.Fourfold.ChainComparison.Bridge

namespace MMP.Fourfold.StabilizedSmallKltTail

open MMP.Fourfold.ChainComparison MMP.Fourfold.ChainComparison.Bridge

open MMP.Mori

variable {T : StabilizedSmallKltTail} {i : ℕ}

/-- At a marked divisor `E_{i,s}` of `Y_i` under the prime divisor `P` of `W`, the coefficient
`K_W(P) + Θ'(E_{i,s})` is that of `r^*(K_{i+1} + B_{i+1})`: `(W, r, P)` computes the log
discrepancy `a_{i+1}(s)`. -/
private theorem coeff_add_eq_of_isDecreasedBoundary_E
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ')
    {W : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    {q : W ⟶ J.Y} {r : W ⟶ T.X (i + 1)}
    [IsProper q] [IsProper r] [IsDominant q] [IsDominant r] [IsDominant J.p]
    [IsSeparated J.sY] [IsSeparated (T.sX (i + 1))] [IsSeparated (J.Y ↘ Limits.terminal Scheme)]
    [IsSeparated (T.X (i + 1) ↘ Limits.terminal Scheme)]
    [IsSeparated (T.Z i ↘ Limits.terminal Scheme)] [IsNormal (T.Z i)]
    [LocallyOfFiniteType (T.sZ i)] [IsLocallyNoetherian (T.Z i)]
    [LocallyOfFiniteType (T.sX (i + 1))] [IsProper (T.f i)] [IsProper (T.fp i)]
    [LocallyOfFiniteType (r ≫ T.sX (i + 1))]
    (hWp : MMP.Mori.IsProjectiveVariety ℂ (q ≫ J.sY))
    (hq : IsBirationalMorphism q) (hr : IsBirationalMorphism r)
    (hcomp : q ≫ J.p ≫ T.f i = r ≫ T.fp i) (hrs : r ≫ T.sX (i + 1) = q ≫ J.sY)
    {KW : Divisor W} (hKW : KW.IsCanonicalDivisor (q ≫ J.sY) 4)
    (hKX : RationalMap.transformDivisor r.toRationalMap KW = T.K (i + 1))
    {R : QDivisor W}
    {hR₀ : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).supp}
    (hR : (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).IsPullback r hR₀ R)
    {P : MMP.Mori.PrimeDivisor W} (s : I) (hPQ' : q P.genericPoint = (J.E s).genericPoint) :
    ((KW P : ℤ) : ℚ) + Θ' (J.E s) = R P := by
  have hSi := T.isFourfoldStepDiagram i
  have hXi1 := hSi.isNormalVariety_plus
  have hfps := hSi.isSmallMorphism_plus
  have hWn' : IsNormalVariety ℂ (r ≫ T.sX (i + 1)) :=
    hrs ▸ (⟨hWp.toIsVariety, inferInstance⟩ : IsNormalVariety ℂ (q ≫ J.sY))
  have hXQ : (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).IsQCartier :=
    (T.isFourfoldStepDiagram (i + 1)).isQCartier_minus
  have := isIso_stalkMap_of_map_eq_genericPoint hq hPQ'
  obtain ⟨a, ha, hΘ'eq⟩ := hΘ'
  rw [decreasedBoundary_apply_E hΘ'eq]
  obtain ⟨s', hts, n, D', -, hD'v, hD'log⟩ := ha s
  have hval : D'.valuation =
      (⟨W, r, hWn', hr, P⟩ : DivisorOver ℂ (T.sX (i + 1))).valuation := by
    rw [hD'v]
    refine valuation_eq_of_comap_eq
      hfps.isBirationalMorphism.functionFieldMap_bijective.2 (hts.trans ?_)
    refine Valuation.ext fun t => ?_
    rw [Valuation.comap_apply, Valuation.comap_apply]
    change _ = P.divisorialValuation (functionFieldMap r (functionFieldMap (T.fp i) t))
    rw [functionFieldMap_comp_apply r (T.fp i) hcomp.symm,
      ← functionFieldMap_comp_apply q (J.p ≫ T.f i) rfl,
      ← functionFieldMap_comp_apply J.p (T.f i) rfl,
      ← PrimeDivisor.valuationOver_apply, valuationOver_eq_of_isIso q P (J.E s) hPQ',
      ← J.valuation_eq s]
    rfl
  have := coeff_isPullback_eq_of_isLogDiscrepancy hXi1 (isCanonicalDivisor_K (i + 1)) hXQ hr
    hWn' (hrs ▸ hKW) hKX hR P hD'log hval
  exact_mod_cast (show (((KW P : ℚ) + (1 - a s) : ℚ) : ℝ) = ((R P : ℚ) : ℝ) by
    push_cast; linarith)

/-- At an unmarked prime divisor `Q` of `Y_i` under the prime divisor `P` of `W`, the coefficient
`K_W(P) + Θ'(Q)` is that of `r^*(K_{i+1} + B_{i+1})`: `Q` lies over a prime `Q₀` of `X_i`, whose
strict transform `Q₁` on `X_{i+1}` is the image of `P`, the step being small. -/
private theorem coeff_add_eq_of_isDecreasedBoundary_of_notMem_range
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ')
    {W : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    {q : W ⟶ J.Y} {r : W ⟶ T.X (i + 1)}
    [IsProper q] [IsProper r] [IsDominant q] [IsDominant r] [IsDominant J.p]
    [IsSeparated J.sY] [IsSeparated (T.sX (i + 1))] [IsSeparated (J.Y ↘ Limits.terminal Scheme)]
    [IsSeparated (T.X (i + 1) ↘ Limits.terminal Scheme)]
    [IsSeparated (T.Z i ↘ Limits.terminal Scheme)] [IsNormal (T.Z i)]
    [LocallyOfFiniteType (T.sZ i)] [IsLocallyNoetherian (T.Z i)]
    [LocallyOfFiniteType (T.sX (i + 1))] [IsProper (T.f i)] [IsProper (T.fp i)]
    [LocallyOfFiniteType (r ≫ T.sX (i + 1))] (hr : IsBirationalMorphism r)
    (hcomp : q ≫ J.p ≫ T.f i = r ≫ T.fp i) {KW : Divisor W}
    (hKX : RationalMap.transformDivisor r.toRationalMap KW = T.K (i + 1))
    {R : QDivisor W}
    {hR₀ : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).supp}
    (hR : (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).IsPullback r hR₀ R)
    {P : MMP.Mori.PrimeDivisor W} {Q : MMP.Mori.PrimeDivisor J.Y} (hQE : Q ∉ Set.range J.E)
    (hPQ' : q P.genericPoint = Q.genericPoint) :
    ((KW P : ℤ) : ℚ) + Θ' Q = R P := by
  have hSi := T.isFourfoldStepDiagram i
  have hXi := hSi.isNormalVariety_minus
  have hXi1 := hSi.isNormalVariety_plus
  have hZ := hSi.isNormalVariety_target
  have hfs : IsSmallMorphism (T.sX i) (T.sZ i) (T.f i) :=
    T.isStabilizedSmallKltTail.isSmallFrom_zero i (Nat.zero_le i)
  have hfps := hSi.isSmallMorphism_plus
  have hXQ : (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).IsQCartier :=
    (T.isFourfoldStepDiagram (i + 1)).isQCartier_minus
  obtain ⟨a, -, hΘ'eq⟩ := hΘ'
  obtain ⟨Q₀, hv₀⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hXi
      (⟨J.Y, J.p, J.isQFactorial.1, J.isBirationalMorphism, Q⟩ : DivisorOver ℂ (T.sX i))
      fun h => hQE ((J.isExceptional_iff Q).mp h)
  have hQ₀ : J.p Q.genericPoint = Q₀.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hXi.1 hv₀
  have hco : Order.coheight (T.f i Q₀.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus _
      (map_genericPoint_mem_biregularLocus hfs.two_le_codimension Q₀), Q₀.coheight_genericPoint]
  have hQZ : T.f i Q₀.genericPoint = (PrimeDivisor.ofCoheightOne _ hco).genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm
  obtain ⟨Q₁, hQ₁, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0}
    hZ (by rw [hSi.comp_eq_plus]; exact hXi1) hfps.isBirationalMorphism
      (PrimeDivisor.ofCoheightOne _ hco)
  have hrP : r P.genericPoint = Q₁.genericPoint := by
    refine eq_of_map_eq_genericPoint hfps.isBirationalMorphism ?_ hQ₁
    rw [← Scheme.Hom.comp_apply, ← hcomp]
    simpa only [Scheme.Hom.comp_apply, hPQ', hQ₀] using hQZ
  have := isIso_stalkMap_of_map_eq_genericPoint hr hrP
  rw [coeff_eq_of_isPullback_qDivisor P Q₁ hrP hXQ hR, decreasedBoundary_apply_of_notMem_range
    hΘ'eq hQE hQ₀]
  change _ = ((T.K (i + 1) Q₁ : ℤ) : ℚ) + T.B (i + 1) Q₁
  rw [← hKX, transformDivisor_apply_of_map_genericPoint hr hrP, T.B_eq i]
  simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [inverseTransformDivisor_apply_of_map_genericPoint hQ₁
    (hQ₁ ▸ map_genericPoint_mem_biregularLocus hfps.two_le_codimension Q₁),
    transformDivisor_apply_of_map_genericPoint hfs.isBirationalMorphism hQZ]

/-- The comparison divisor `q^*(K_Y + Θ') - r^*(K_{i+1} + B_{i+1})` pushes forward to zero on
`Y_i`. -/
private theorem transformDivisor_sub_eq_zero_of_isDecreasedBoundary
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ')
    {W : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    {q : W ⟶ J.Y} {r : W ⟶ T.X (i + 1)}
    (hWp : MMP.Mori.IsProjectiveVariety ℂ (q ≫ J.sY))
    (hq : IsBirationalMorphism q) (hr : IsBirationalMorphism r)
    (hcomp : q ≫ J.p ≫ T.f i = r ≫ T.fp i) (hrs : r ≫ T.sX (i + 1) = q ≫ J.sY)
    {KW : Divisor W} (hKW : KW.IsCanonicalDivisor (q ≫ J.sY) 4)
    {KY : Divisor J.Y} (hKY : RationalMap.transformDivisor q.toRationalMap KW = KY)
    (hKX : RationalMap.transformDivisor r.toRationalMap KW = T.K (i + 1))
    {A R : QDivisor W}
    {hA₀ : ∀ Z : irreducibleComponents W,
      q (componentGenericPoint W Z) ∉ (Divisor.toQDivisor KY + Θ').supp}
    {hR₀ : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).supp}
    (hA : (Divisor.toQDivisor KY + Θ').IsPullback q hA₀ A)
    (hR : (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).IsPullback r hR₀ R) :
    RationalMap.transformDivisor (X := W) q.toRationalMap (A - R) = 0 := by
  have hSi := T.isFourfoldStepDiagram i
  have hY : IsNormalVariety ℂ J.sY := J.isQFactorial.1
  have hWn : IsNormalVariety ℂ (q ≫ J.sY) := ⟨hWp.toIsVariety, inferInstance⟩
  have : IsProper (q ≫ J.sY) := isProper_of_isProjectiveMorphism _ hWp.isProjective
  have : IsSeparated J.sY := hY.1.toIsSeparated
  have : IsSeparated (T.sX (i + 1)) := hSi.isNormalVariety_plus.1.toIsSeparated
  have : IsProper q := IsProper.of_comp q J.sY
  have : IsProper (r ≫ T.sX (i + 1)) := hrs ▸ inferInstance
  have : IsProper r := IsProper.of_comp r (T.sX (i + 1))
  have hYQ : (Divisor.toQDivisor KY + Θ').IsQCartier :=
    isQCartier_of_isQFactorial J.sY J.isQFactorial _
  have hXi1 := hSi.isNormalVariety_plus
  have hZ := hSi.isNormalVariety_target
  have := hq.isDominant
  have := hr.isDominant
  have := J.isBirationalMorphism.isDominant
  have := isSeparated_toTerminal_of_isNormalVariety hY
  have := isSeparated_toTerminal_of_isNormalVariety hXi1
  have := isSeparated_toTerminal_of_isNormalVariety hZ
  have : IsNormal (T.Z i) := hZ.2
  have : LocallyOfFiniteType (T.sZ i) := hZ.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian (T.Z i) := LocallyOfFiniteType.isLocallyNoetherian (T.sZ i)
  have := hXi1.1.toLocallyOfFiniteType
  have hfs : IsSmallMorphism (T.sX i) (T.sZ i) (T.f i) :=
    T.isStabilizedSmallKltTail.isSmallFrom_zero i (Nat.zero_le i)
  have hfps := hSi.isSmallMorphism_plus
  have : IsProper (T.f i) := hfs.isProper
  have : IsProper (T.fp i) := hfps.isProper
  have hWn' : IsNormalVariety ℂ (r ≫ T.sX (i + 1)) := hrs ▸ hWn
  have : LocallyOfFiniteType (r ≫ T.sX (i + 1)) := hWn'.1.toLocallyOfFiniteType
  rw [RationalMap.transformDivisor]
  refine mapPrimeDivisors_eq_zero_of_forall _ fun P Q hPQ => ?_
  have hPQ' := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff q P Q).mp hPQ
  have := isIso_stalkMap_of_map_eq_genericPoint hq hPQ'
  rw [Finsupp.sub_apply, coeff_eq_of_isPullback_qDivisor P Q hPQ' hYQ hA]
  change ((KY Q : ℤ) : ℚ) + Θ' Q - R P = 0
  rw [← hKY, transformDivisor_apply_of_map_genericPoint hq hPQ' KW, sub_eq_zero]
  by_cases hQE : Q ∈ Set.range J.E
  · obtain ⟨s, rfl⟩ := hQE
    exact coeff_add_eq_of_isDecreasedBoundary_E hΘ' hWp hq hr hcomp hrs hKW hKX hR s hPQ'
  · exact coeff_add_eq_of_isDecreasedBoundary_of_notMem_range hΘ' hr hcomp hKX hR hQE hPQ'

/-- **The decreased pair lies above the next downstairs model.** Let `J = (p_i, Θ_i)` be a crepant
junction of `(X_i, B_i)` extracting `I_∞`, `Θ'` its decreased boundary, and `W` a smooth
projective variety with birational morphisms `q : W ⟶ Y_i`, `r : W ⟶ X_{i+1}` such that
`q ≫ p_i ≫ f_i = r ≫ f_i⁺`. Let `K_W` be a canonical divisor of `W` with `r_* K_W = K_{X_{i+1}}`
and `K_Y = q_* K_W`. Then for the pull-backs `A = q^*(K_Y + Θ')` and
`R = r^*(K_{X_{i+1}} + B_{i+1})`, the `ℚ`-divisor `A - R` is effective. -/
@[mmp "lem_oai4_c1_bridge_comparison"]
public theorem IsDecreasedBoundary.pullback_sub_pullback_nonneg
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (hI : (I : Set _) = T.stableLowDiscrepancySetAt i)
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ')
    {W : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    {q : W ⟶ J.Y} {r : W ⟶ T.X (i + 1)}
    (hWp : MMP.Mori.IsProjectiveVariety ℂ (q ≫ J.sY)) (hWs : IsSmoothScheme (q ≫ J.sY))
    (hq : IsBirationalMorphism q) (hr : IsBirationalMorphism r)
    (hcomp : q ≫ J.p ≫ T.f i = r ≫ T.fp i)
    {KW : Divisor W} (hKW : KW.IsCanonicalDivisor (q ≫ J.sY) 4)
    {KY : Divisor J.Y} (hKY : RationalMap.transformDivisor q.toRationalMap KW = KY)
    (hKX : RationalMap.transformDivisor r.toRationalMap KW = T.K (i + 1))
    (A R : QDivisor W)
    (hA₀ : ∀ Z : irreducibleComponents W,
      q (componentGenericPoint W Z) ∉ (Divisor.toQDivisor KY + Θ').supp)
    (hR₀ : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).supp)
    (hA : (Divisor.toQDivisor KY + Θ').IsPullback q hA₀ A)
    (hR : (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).IsPullback r hR₀ R) :
    0 ≤ A - R := by
  have hSi := T.isFourfoldStepDiagram i
  have hSi1 := T.isFourfoldStepDiagram (i + 1)
  have hY : IsNormalVariety ℂ J.sY := J.isQFactorial.1
  have hWn : IsNormalVariety ℂ (q ≫ J.sY) := ⟨hWp.toIsVariety, inferInstance⟩
  have : IsProper (q ≫ J.sY) := isProper_of_isProjectiveMorphism _ hWp.isProjective
  have : IsSeparated J.sY := hY.1.toIsSeparated
  have : IsSeparated (T.sX (i + 1)) := hSi.isNormalVariety_plus.1.toIsSeparated
  have hrs : r ≫ T.sX (i + 1) = q ≫ J.sY := by
    rw [← hSi.comp_eq_plus, ← Category.assoc, ← hcomp, FourfoldCrepantJunction.sY]
    simp only [Category.assoc, hSi.comp_eq_minus]
  have : IsProper q := IsProper.of_comp q J.sY
  have : IsProper (r ≫ T.sX (i + 1)) := hrs ▸ inferInstance
  have : IsProper r := IsProper.of_comp r (T.sX (i + 1))
  have hYQ : (Divisor.toQDivisor KY + Θ').IsQCartier :=
    isQCartier_of_isQFactorial J.sY J.isQFactorial _
  have hXQ : (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).IsQCartier :=
    hSi1.isQCartier_minus
  have hpush := transformDivisor_sub_eq_zero_of_isDecreasedBoundary hΘ' hWp hq hr hcomp hrs
    hKW hKY hKX hA hR
  have := hSi.isNormalVariety_plus.1.toLocallyOfFiniteType
  have := hY.1.toLocallyOfFiniteType
  have : QuasiCompact J.sY := hY.1.toQuasiCompact
  have := hq.isDominant
  have hamp : (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).HasRelativelyAmpleMultiple
      (T.fp i) := by
    rw [T.K_eq i, T.B_eq i]
    exact hSi.hasRelativelyAmpleMultiple_plus
  exact DivisorWithCoeffs.isEffective_iff_nonneg.mp <|
    QDivisor.isEffective_of_isEffective_transformDivisor_of_isRelativelyNef_neg ℂ J.sY
      (q ≫ J.sY) hY hWn q rfl hq
      (by rw [sub_eq_add_neg]; exact (hA.isQCartier hYQ).add (isQCartier_neg (hR.isQCartier hXQ)))
      (isRelativelyNef_neg_sub_of_isPullback rfl hrs hcomp hYQ hXQ hamp hA hR)
      ((congrArg (·.IsEffective) hpush).mpr DivisorWithCoeffs.isEffective_zero)

end MMP.Fourfold.StabilizedSmallKltTail

namespace MMP.Fourfold.ChainComparison.TwoEnds

open MMP.Mori

/-- One half of the comparison: `q₂^* D₂ ≤ q₁^* D₁`. -/
private theorem le_of_isPullback (k : Type u) [Field k] {Z V₁ V₂ W : Scheme.{u}}
    (sV₁ : V₁ ⟶ Spec (.of k)) (sV₂ : V₂ ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k))
    [QuasiCompact sV₁] [IsLocallyNoetherian V₁] [IsNormal V₁]
    [QuasiCompact sV₂] [IsLocallyNoetherian V₂] [IsNormal V₂] [AlgebraicGeometry.IsVariety k sV₂]
    [QuasiCompact sW] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (hV₁ : IsNormalVariety k sV₁) (hW : IsNormalVariety k sW)
    (π₁ : V₁ ⟶ Z) (π₂ : V₂ ⟶ Z) (q₁ : W ⟶ V₁) (q₂ : W ⟶ V₂) [IsProper q₁]
    (hq₁ : IsBirationalMorphism q₁) (hs₁ : q₁ ≫ sV₁ = sW) (hs₂ : q₂ ≫ sV₂ = sW)
    (hcomp : q₁ ≫ π₁ = q₂ ≫ π₂)
    {D₁ : QDivisor V₁} {D₂ : QDivisor V₂} (hD₁ : D₁.IsQCartier) (hD₂ : D₂.IsQCartier)
    (hn₂ : D₂.IsRelativelyNef sV₂ π₂) {A₁ A₂ : QDivisor W}
    {hA₁₀ : ∀ T : irreducibleComponents W, q₁ (componentGenericPoint W T) ∉ D₁.supp}
    {hA₂₀ : ∀ T : irreducibleComponents W, q₂ (componentGenericPoint W T) ∉ D₂.supp}
    (hA₁ : D₁.IsPullback q₁ hA₁₀ A₁) (hA₂ : D₂.IsPullback q₂ hA₂₀ A₂)
    {F₁ F₂ : QDivisor W} (hF₂ : 0 ≤ F₂)
    (hF₁₀ : RationalMap.transformDivisor (X := W) q₁.toRationalMap F₁ = 0)
    (heq : A₁ + F₁ = A₂ + F₂) :
    A₂ ≤ A₁ := by
  have : AlgebraicGeometry.IsVariety k sV₁ := hV₁.1
  have hA₁q := hA₁.isQCartier hD₁
  have hA₂q := hA₂.isQCartier hD₂
  have hEq : (A₁ - A₂).IsQCartier := by
    rw [sub_eq_add_neg]; exact hA₁q.add (isQCartier_neg hA₂q)
  have hnE := isQCartier_neg hEq
  have hE : A₁ - A₂ = F₂ - F₁ := by
    rw [sub_eq_sub_iff_add_eq_add, heq, add_comm]
  have key := QDivisor.isEffective_of_isEffective_transformDivisor_of_isRelativelyNef_neg
    k sV₁ sW hV₁ hW q₁ hs₁ hq₁ hEq
    (MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sW hnE fun Γ hΓ => by
      have h1 := QDivisor.intersectionNumber_add' k sW Γ.ι Γ.dim_le (-(A₁ - A₂)) A₁ hnE hA₁q
        (hnE.add hA₁q)
      rw [MMP.Fourfold.intersectionNumber_congr sW Γ.ι Γ.dim_le (hnE.add hA₁q) hA₂q (by abel),
        intersectionNumber_isPullback_eq_zero q₁ hs₁ hD₁ hA₁ Γ hΓ, add_zero] at h1
      exact h1 ▸ intersectionNumber_isPullback_nonneg q₂ hs₂ π₂ hD₂ hn₂ hA₂ Γ
        (hcomp ▸ fun x hx => by simp only [Scheme.Hom.comp_apply, hΓ x hx]))
    (by
      rw [DivisorWithCoeffs.isEffective_iff_nonneg, hE, map_sub, hF₁₀, sub_zero]
      exact RationalMap.transformDivisor_nonneg _ hF₂)
  exact sub_nonneg.mp (DivisorWithCoeffs.isEffective_iff_nonneg.mp key)

end MMP.Fourfold.ChainComparison.TwoEnds

namespace MMP.Fourfold

open MMP.Fourfold.ChainComparison.TwoEnds

open MMP.Mori

/-- **Two relatively nef ends have equal pull-backs.** Let `π_j : V_j ⟶ Z` (`j = 1, 2`) be
projective morphisms of normal projective varieties over `k`, `D_j` a `π_j`-nef `ℚ`-Cartier
`ℚ`-divisor on `V_j`, and `q_j : W ⟶ V_j` birational morphisms from a smooth projective variety
`W` with `q₁ ≫ π₁ = q₂ ≫ π₂`. Let `A_j = q_j^* D_j`. If `A₁ + F₁ = A₂ + F₂` for effective
`ℚ`-divisors `F_j` on `W` with `q_{j*} F_j = 0`, then `A₁ = A₂`. -/
@[mmp "lem_oai4_two_ends_b"]
public theorem eq_of_isPullback_of_add_eq_add_of_isRelativelyNef
    (k : Type u) [Field k] {Z V₁ V₂ W : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of k)) (sV₁ : V₁ ⟶ Spec (.of k)) (sV₂ : V₂ ⟶ Spec (.of k))
    [QuasiCompact sV₁] [IsLocallyNoetherian V₁] [IsNormal V₁]
    [QuasiCompact sV₂] [IsLocallyNoetherian V₂] [IsNormal V₂]
    [IsLocallyNoetherian W] [IsNormal W]
    (hZ : IsNormalVariety k sZ) (hZp : MMP.Mori.IsProjectiveVariety k sZ)
    (hV₁ : IsNormalVariety k sV₁) (hV₁p : MMP.Mori.IsProjectiveVariety k sV₁)
    (hV₂ : IsNormalVariety k sV₂) (hV₂p : MMP.Mori.IsProjectiveVariety k sV₂)
    (π₁ : V₁ ⟶ Z) (π₂ : V₂ ⟶ Z) (hπ₁ : IsProjectiveMorphism π₁) (hπ₂ : IsProjectiveMorphism π₂)
    (hsπ₁ : π₁ ≫ sZ = sV₁) (hsπ₂ : π₂ ≫ sZ = sV₂)
    {D₁ : QDivisor V₁} {D₂ : QDivisor V₂} (hD₁ : D₁.IsQCartier) (hD₂ : D₂.IsQCartier)
    (hn₁ : D₁.IsRelativelyNef sV₁ π₁) (hn₂ : D₂.IsRelativelyNef sV₂ π₂)
    (q₁ : W ⟶ V₁) (q₂ : W ⟶ V₂)
    (hWp : MMP.Mori.IsProjectiveVariety k (q₁ ≫ sV₁)) (hWs : IsSmoothScheme (q₁ ≫ sV₁))
    (hq₁ : IsBirationalMorphism q₁) (hq₂ : IsBirationalMorphism q₂)
    (hsq : q₁ ≫ sV₁ = q₂ ≫ sV₂) (hcomp : q₁ ≫ π₁ = q₂ ≫ π₂)
    {A₁ A₂ : QDivisor W}
    (hA₁₀ : ∀ T : irreducibleComponents W, q₁ (componentGenericPoint W T) ∉ D₁.supp)
    (hA₂₀ : ∀ T : irreducibleComponents W, q₂ (componentGenericPoint W T) ∉ D₂.supp)
    (hA₁ : D₁.IsPullback q₁ hA₁₀ A₁) (hA₂ : D₂.IsPullback q₂ hA₂₀ A₂)
    {F₁ F₂ : QDivisor W} (hF₁ : 0 ≤ F₁) (hF₂ : 0 ≤ F₂)
    (hF₁₀ : RationalMap.transformDivisor (X := W) q₁.toRationalMap F₁ = 0)
    (hF₂₀ : RationalMap.transformDivisor (X := W) q₂.toRationalMap F₂ = 0)
    (heq : A₁ + F₁ = A₂ + F₂) :
    A₁ = A₂ := by
  have : AlgebraicGeometry.IsVariety k sV₁ := hV₁.1
  have : AlgebraicGeometry.IsVariety k sV₂ := hV₂.1
  have : AlgebraicGeometry.IsProjectiveVariety k (q₁ ≫ sV₁) := hWp
  have : IsIntegral W := hWp.toIsVariety.toIsIntegral
  have hW : IsNormalVariety k (q₁ ≫ sV₁) := ⟨hWp.toIsVariety, inferInstance⟩
  have : IsProper (q₁ ≫ sV₁) := isProper_of_isProjectiveMorphism _ hWp.isProjective
  have : IsProper q₁ := IsProper.of_comp q₁ sV₁
  have : IsProper (q₂ ≫ sV₂) := hsq ▸ inferInstance
  have : IsProper q₂ := IsProper.of_comp q₂ sV₂
  exact le_antisymm
    (le_of_isPullback k sV₂ sV₁ (q₁ ≫ sV₁) hV₂ hW π₂ π₁ q₂ q₁ hq₂ hsq.symm rfl hcomp.symm hD₂
      hD₁ hn₁ hA₂ hA₁ hF₁ hF₂₀ heq.symm)
    (le_of_isPullback k sV₁ sV₂ (q₁ ≫ sV₁) hV₁ hW π₁ π₂ q₁ q₂ hq₁ rfl hsq.symm hcomp hD₁ hD₂
      hn₂ hA₁ hA₂ hF₂ hF₁₀ heq)

end MMP.Fourfold

end
