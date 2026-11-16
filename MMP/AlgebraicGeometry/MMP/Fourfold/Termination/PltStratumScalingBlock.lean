module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.StratumAdjunction
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.Singularities.RealPltAdjunction
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.RealKltBigScaling
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.MinimalModel.RealKltCompactification
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefAdjointTargets
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Positivity.RelativeKodairaDecomposition
import MMP.AlgebraicGeometry.Resolution.CommonLogResolution
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Morphisms.Birational.ZariskiMainTheorem
import MMP.AlgebraicGeometry.MMP.MinimalModel.CommonModelNefWeakModels
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.MMP.Contraction.CurveFactorization
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram.BadLocusDiscrepancy
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
public import MMP.AlgebraicGeometry.Morphisms.HProjective
public import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial

/-!
# A stratum block of a real plt flip has the ambient scaling threshold

Let `X ⟶ T ⟵ X⁺` be a real flip of projective `ℚ`-factorial complex fourfolds `(X, B)`, with
`(X, B)` plt, lying over a projective variety `Z`, and let `C ≥ 0` and `λ > 0` be such that
`K_X + B + λ C` is nef over `Z` and numerically trivial over `T`. Let `S` be a component of
`⌊B⌋` not contained in `Supp C`, retained by the flip as `S⁺`, with real adjunction pairs
`(S, Δ)` and `(S⁺, Δ⁺)`, and suppose the induced birational map `S ⤏ S⁺` extracts no prime
divisor and preserves the coefficients of the shared primes. Let `h : V ⟶ S` be a projective
birational morphism from a `ℚ`-factorial normal projective variety with an effective klt crepant
boundary `Δ_V` (`K_V + Δ_V = h^*(K_S + Δ)`), with `C_V = h^*(C|_S) ≥ 0`, `(V, Δ_V + λ C_V)` klt
and `Δ_V ≥ A` for an effective `ℚ`-divisor `A` big over `Z`.

Then there is a finite sequence of elementary `(K_V + Δ_V)`-negative steps over `T` (divisorial
contractions and flips of globally projective models), each having scaling threshold exactly `λ`
for nefness over `Z`, whose last model `V⁺` carries a projective birational morphism
`h⁺ : V⁺ ⟶ S⁺` over `T` which is crepant for `(S⁺, Δ⁺)`, and on which the transform of `C_V`
equals `(h⁺)^*(C⁺|_{S⁺})`.

## Main results

* `MMP.Fourfold.exists_scalingBlock_of_isRealFlipStep_of_isPlt`

## Implementation notes

* The real plt condition on `(X, B)` is written out: coefficients of `B` in `[0, 1]`, `K_X + B`
  `ℝ`-Cartier, and positive log discrepancy at every exceptional divisor over `X`.
* The adjunction boundaries are the real-affine extensions of the rational different:
  `B = ∑ₖ tₖ Bₖ` is a positive convex combination of rational boundaries and
  `Δ = ∑ₖ tₖ Diff_S(Bₖ - S)` (`MMP.Fourfold.IsAdjunctionStep`), as in
  `MMP.Fourfold.eventually_realPltFlip_stratum_divisors_stabilize`. The induced map `S ⤏ S⁺` is
  the birational map `φ` with `f⁺ ∘ φ = f` on `S`.
* Restrictions to `S`, `S⁺` and pull-backs by `h`, `h⁺` are pull-backs of `ℝ`-Cartier divisors
  (`MMP.Flips.IsRCartierPullback`). Crepancy of `h` is `K_V + Δ_V = h^*(K_S + Δ)` for a
  canonical divisor `K_S = h_* K_V`.
* The block is written as a program with scaling, indexed as in
  `MMP.Fourfold.exists_scalingProgram_and_finite_of_isRelativelyBig` (`MMP.Fourfold.modelSeq`,
  `MMP.Fourfold.modelMap`, `MMP.Fourfold.divisorSeq`), with models over `T`. The scaling
  threshold of a step is the least `t ≥ 0` for which `K + Δ + t C` is nef over `Z`.
* The morphism `h⁺` is pinned by lying over `T`: `h⁺ ≫ f⁺|_{S⁺}` is the structure morphism of
  the last model, which determines `h⁺` since `S⁺ ⟶ T` is birational onto its image.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 7
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry

namespace Proof_lem_fourfold_plt_scaling_block

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Fourfold MMP.Mori MMP.Flips

section Helpers

variable {k : Type} [Field k]

private theorem isContractedBy_comp {X Y Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {C : ProperCurve sX} {f : X ⟶ Y} (hC : C.IsContractedBy f) (g : Y ⟶ Z) :
    C.IsContractedBy (f ≫ g) := by
  intro x hx
  simp only [Scheme.Hom.comp_base, TopCat.comp_app]
  rw [hC x hx]

private theorem isNumericallyTrivialOver_of_comp {X Y Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y} {g : Y ⟶ Z}
    {N : RDivisor X} (h : IsNumericallyTrivialOver k sX (f ≫ g) N) :
    IsNumericallyTrivialOver k sX f N :=
  ⟨h.1, h.2.1, fun C hC => h.2.2 C (isContractedBy_comp hC g)⟩

private theorem transformDivisor_nonneg {X Y : Scheme.{0}} (φ : X.RationalMap Y)
    {D : RDivisor X} (h : 0 ≤ D) : 0 ≤ MMP.Mori.RationalMap.transformDivisor φ D := by
  classical
  intro E
  change 0 ≤ (Finsupp.liftAddHom _ D : RDivisor Y) E
  rw [Finsupp.liftAddHom_apply, Finsupp.sum_apply]
  refine Finset.sum_nonneg fun P _ => ?_
  dsimp only
  rcases MMP.Mori.RationalMap.transformPrimeDivisor φ P with _ | Q
  · simp
  · simp only [Option.elim_some, Finsupp.singleAddHom_apply, Finsupp.single_apply]
    split_ifs
    · exact h P
    · exact le_rfl

private theorem transformDivisor_smul {X Y : Scheme.{0}} (φ : X.RationalMap Y) (c : ℝ)
    (D : RDivisor X) : MMP.Mori.RationalMap.transformDivisor φ (c • D) =
      c • MMP.Mori.RationalMap.transformDivisor φ D :=
  MMP.Mori.DivisorWithCoeffs.mapPrimeDivisors_smul _ c D

/-- The empty presentation computes the intersection number `0 · C = 0`. -/
private theorem isRIntersectionNumber_zero {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] (C : ProperCurve sX) :
    IsRIntersectionNumber k sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → Divisor X) C 0 :=
  ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩

/-- A numerically trivial divisor is nef. -/
private theorem isRelativelyNef_of_isNumericallyTrivialOver {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {f : X ⟶ Y} {N : RDivisor X}
    (h : IsNumericallyTrivialOver k sX f N) : IsRelativelyNef k sX f N := by
  obtain ⟨m, r, L, hL, hN⟩ := h.1
  refine ⟨m, r, L, hL, by simpa only [toRDivisor_eq_mapCoeffs] using hN, fun C hC x hx => ?_⟩
  exact (h.2.2 C hC m r L x 0 _ _ 0 hx (isRIntersectionNumber_zero C)).ge

/-- An `ℝ`-Cartier divisor in the sense of coefficients is a combination of Cartier divisors. -/
private theorem isCartierCombination_of_isRCartier {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {D : RDivisor X} (h : RDivisor.IsRCartier D) : IsCartierCombination D := by
  obtain ⟨m, r, C, hC, hD⟩ := h
  refine ⟨m, r, C, hC, ?_⟩
  ext Γ
  rw [hD Γ]
  change _ = (∑ j, r j • DivisorWithCoeffs.mapCoeffs Int.cast _ (C j)) Γ
  rw [Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul]
  rfl

/-- `D · C = ∑ r_j (L_j · C)`, computed from the degrees along `C`, for a presentation
`D = ∑ r_j L_j` by Cartier divisors. -/
private theorem isRIntersectionNumber_sum_degreeOn' (k : Type) [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    (C : ProperCurve sX) {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier) :
    IsRIntersectionNumber k sX (∑ j, r j • Divisor.toRDivisor (L j)) r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) :=
  ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), rfl,
    fun j => MMP.Flips.isCartierIntersectionNumber_degreeOn k sX C (L j) (hL j), rfl⟩

private theorem isCartierCombination_of_isQFactorial {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsQFactorial sX)
    (D : RDivisor X) : IsCartierCombination D :=
  isCartierCombination_of_isRCartier (hX.isRCartier D)

/-- A contraction of relative Picard number one contracts some proper curve. -/
private theorem exists_isContractedBy_of_relativePicardNumber_eq_one
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {f : X ⟶ Y} (h : MMP.Flips.relativePicardNumber sX f = 1) :
    ∃ C : ProperCurve sX, C.IsContractedBy f := by
  by_contra hne
  push Not at hne
  have htop : relativeNumericallyTrivialDivisors sX f = ⊤ := by
    ext D
    simp only [Submodule.mem_top, iff_true]
    rw [mem_relativeNumericallyTrivialDivisors]
    intro C hC
    exact absurd hC (hne C)
  have : Subsingleton (MMP.Flips.RelativeNumericalDivisorClasses sX f) := by
    unfold MMP.Flips.RelativeNumericalDivisorClasses
    rw [htop]
    infer_instance
  unfold MMP.Flips.relativePicardNumber at h
  rw [rank_subsingleton'] at h
  simp at h

/-- A relatively ample Cartier divisor has positive degree on a contracted curve. -/
private theorem degreeOn_pos_of_isRelativelyAmpleCartier {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {f : X ⟶ Y} {L : Divisor X} (hA : IsRelativelyAmpleCartier f L)
    (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    ∃ hL : L.IsCartier, 0 < L.degreeOn ℂ sX C.ι C.dim_le hL := by
  obtain ⟨hL, hamp⟩ := hA
  refine ⟨hL, ?_⟩
  have := hL.isInvertibleModule_divisorialSheaf
  have hamp' : MMP.Mori.IsRelativelyAmple f L.divisorialSheaf := by
    intro y
    obtain ⟨V, hV, hyV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (show y ∈ (⊤ : Y.Opens) from trivial)
    exact ⟨V, hV, hyV, hamp _ hV⟩
  exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f
    L.divisorialSheaf hamp' C hC

/-- A relatively anti-ample `ℝ`-divisor is negative on a contracted curve, for a presentation by
the relatively ample summands. -/
private theorem exists_isRIntersectionNumber_neg_of_isRelativelyAntiAmple {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {f : X ⟶ Y} {E : RDivisor X} (hE : IsRelativelyAntiAmple f E)
    (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber ℂ sX E r L C x ∧ x < 0 := by
  obtain ⟨m, s, A, hm, hs, hA, hEq⟩ := hE
  choose hL hpos using fun j => degreeOn_pos_of_isRelativelyAmpleCartier (hA j) C hC
  have hx := isRIntersectionNumber_sum_degreeOn' ℂ sX C (fun j => -s j) A hL
  have hE' : E = ∑ j, (fun j => -s j) j • Divisor.toRDivisor (A j) := by
    rw [← neg_neg E, hEq, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => (neg_smul _ _).symm
  rw [← hE'] at hx
  refine ⟨m, _, A, _, hx, ?_⟩
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
  have : 0 < ∑ j, s j * ((A j).degreeOn ℂ sX C.ι C.dim_le (hL j) : ℝ) :=
    Finset.sum_pos (fun j _ => mul_pos (hs j) (by exact_mod_cast hpos j)) hne
  simp only [neg_mul, Finset.sum_neg_distrib]
  linarith

/-- **The scaling threshold of a step is the level of a null nef adjoint.** If `f` is a
`(K + Δ)`-negative extremal contraction over `T`, and `K + Δ + λC` is nef over `Z` (with
`T ⟶ Z`) and numerically trivial over `f`, then `λ` is the least `t ≥ 0` with `K + Δ + tC` nef
over `Z`. -/
private theorem isLeast_threshold {Y W T Z : Scheme.{0}} [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} [QuasiCompact sY]
    {sW : W ⟶ Spec (.of ℂ)} {fW : Y ⟶ W} {gW : W ⟶ T} {πY : Y ⟶ T} (g : T ⟶ Z)
    (hfg : fW ≫ gW = πY) {K : Divisor Y} {Δ C : RDivisor Y} {lam : ℝ} (hlam : 0 < lam)
    (hneg : IsNegativeExtremalContraction ℂ sY sW (logCanonicalDivisor K Δ) fW)
    (hnef : IsRelativelyNef ℂ sY (πY ≫ g) (logCanonicalDivisor K (Δ + lam • C)))
    (htriv : IsNumericallyTrivialOver ℂ sY fW (logCanonicalDivisor K (Δ + lam • C))) :
    IsLeast {t : ℝ | 0 ≤ t ∧
      IsRelativelyNef ℂ sY (πY ≫ g) (logCanonicalDivisor K (Δ + t • C))} lam := by
  refine ⟨⟨hlam.le, hnef⟩, fun t ⟨ht0, m₂, r₂, L₂, hL₂, hD₂, hnn⟩ => ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨γ, hγ⟩ :=
    exists_isContractedBy_of_relativePicardNumber_eq_one hneg.relativePicardNumber_eq_one
  have hγZ : γ.IsContractedBy (πY ≫ g) := by
    rw [← hfg, Category.assoc]
    exact isContractedBy_comp hγ _
  obtain ⟨m₀, r₀, L₀, a, ha, ha0⟩ :=
    exists_isRIntersectionNumber_neg_of_isRelativelyAntiAmple hneg.isRelativelyAntiAmple γ hγ
  obtain ⟨m₁, r₁, L₁, hL₁, hD₁⟩ := htriv.1
  have hx₁ := isRIntersectionNumber_sum_degreeOn' ℂ sY γ r₁ L₁ hL₁
  rw [show (∑ j, r₁ j • Divisor.toRDivisor (L₁ j)) = logCanonicalDivisor K (Δ + lam • C) by
    rw [hD₁]; simp only [toRDivisor_eq_mapCoeffs]] at hx₁
  have h0 := htriv.2.2 γ hγ m₁ r₁ L₁ _ 0 _ _ 0 hx₁ (isRIntersectionNumber_zero γ)
  have hcomb := (IsRIntersectionNumber.eq_and_linear ℂ sY γ).2 _ _ r₀ L₀ r₁ L₁ a _
    (1 - t / lam) (t / lam) ha hx₁
  have hdiv : (1 - t / lam) • logCanonicalDivisor K Δ +
      (t / lam) • logCanonicalDivisor K (Δ + lam • C) = logCanonicalDivisor K (Δ + t • C) := by
    have : (t / lam) • (Δ + lam • C) = (t / lam) • Δ + t • C := by
      rw [smul_add, smul_smul, div_mul_cancel₀ t hlam.ne']
    unfold logCanonicalDivisor
    rw [smul_add, smul_add, this]
    module
  rw [hdiv] at hcomb
  have hx₂ := isRIntersectionNumber_sum_degreeOn' ℂ sY γ r₂ L₂ hL₂
  rw [← hD₂] at hx₂
  have heq := (IsRIntersectionNumber.eq_and_linear ℂ sY γ).1 _ _ _ _ _ _ _ hcomb hx₂
  have hge := hnn γ hγZ _ hx₂
  rw [h0, ← heq] at *
  have hpos : 0 < 1 - t / lam := by
    rwa [sub_pos, div_lt_one hlam]
  nlinarith

/-- A proper dominant morphism is surjective. -/
private theorem surjective_of_isProper_of_isDominant {X Y : Scheme.{0}} (f : X ⟶ Y) [IsProper f]
    [IsDominant f] : Surjective f := by
  refine ⟨fun y => ?_⟩
  have h1 : IsClosed (Set.range f.base) := f.isClosedMap.isClosed_range
  have h2 : Set.range f.base = Set.univ := by
    rw [← h1.closure_eq, f.denseRange.closure_range]
  exact (Set.eq_univ_iff_forall.mp h2) y

/-- The target of a proper surjective morphism from a proper variety, if quasi-projective, is a
projective variety. -/
private theorem isProjectiveVariety_of_surjective {X T : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sT : T ⟶ Spec (.of ℂ)} (f : X ⟶ T) (hfT : f ≫ sT = sX) [IsProper f] [IsDominant f]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hT : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sT) :
    MMP.Mori.IsProjectiveVariety ℂ sT := by
  haveI := surjective_of_isProper_of_isDominant f
  haveI : IsProper sX := (isProper_of_isProjectiveMorphism sX hX.isProjective)
  haveI : UniversallyClosed (f ≫ sT) := by rw [hfT]; infer_instance
  haveI := UniversallyClosed.of_comp_surjective f sT
  haveI := hT.toIsVariety
  haveI : IsProper sT := ⟨⟩
  exact (AlgebraicGeometry.isProjectiveVariety_iff ℂ sT).mpr ⟨inferInstance,
    AlgebraicGeometry.isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
      ⟨(AlgebraicGeometry.isQuasiProjective_iff_isHQuasiProjective_of_isAffine sT).mp
        hT.isQuasiProjective, inferInstance⟩⟩

/-- A finite dimension and a finite coheight adding up to `n` are natural numbers. -/
private theorem exists_nat_of_add_eq {a : WithBot ℕ∞} {c : ℕ∞} {n : ℕ}
    (h : a + (c : WithBot ℕ∞) = (n : WithBot ℕ∞)) :
    ∃ a' c' : ℕ, a = a' ∧ c = c' ∧ a' + c' = n := by
  induction a using WithBot.recBotCoe with
  | bot => rw [WithBot.bot_add] at h; exact absurd h.symm (WithBot.natCast_ne_bot _)
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_add, top_add] at h
      have h4 : ((⊤ : ℕ∞) : WithBot ℕ∞) = (((n : ℕ) : ℕ∞) : WithBot ℕ∞) := by rw [h]; simp
      exact absurd (WithBot.coe_injective h4) (ENat.top_ne_coe _)
    | coe a =>
      induction c using ENat.recTopCoe with
      | top =>
        rw [← WithBot.coe_add, add_top] at h
        have h4 : ((⊤ : ℕ∞) : WithBot ℕ∞) = (((n : ℕ) : ℕ∞) : WithBot ℕ∞) := by rw [h]; simp
        exact absurd (WithBot.coe_injective h4) (ENat.top_ne_coe _)
      | coe c =>
        refine ⟨a, c, rfl, rfl, ?_⟩
        exact_mod_cast h

/-- `d + 1 = n + 1` forces `d = n` in `WithBot ℕ∞`. -/
private theorem eq_of_add_one_eq {d : WithBot ℕ∞} {n : ℕ}
    (h : d + ((1 : ℕ∞) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞)) : d = n := by
  obtain ⟨a, c, rfl, hc, hs⟩ := exists_nat_of_add_eq h
  obtain rfl : c = 1 := by exact_mod_cast hc.symm
  obtain rfl : a = n := by omega
  rfl

/-- A closed immersion onto the support of a prime divisor maps the generic point to the generic
point of the divisor. -/
private theorem map_genericPoint_eq_of_range_eq_support {A X : Scheme.{0}} [IsIntegral A]
    (ι : A ⟶ X) [IsClosedImmersion ι] {P : MMP.Mori.PrimeDivisor X}
    (hι : Set.range ι.base = (P.support : Set X)) : ι (genericPoint A) = P.genericPoint := by
  have h1 : IsGenericPoint (ι (genericPoint A)) (P.support : Set X) := by
    have := (genericPoint_spec A).image ι.base.hom.continuous
    rwa [Set.image_univ, ι.isClosedEmbedding.isClosed_range.closure_eq, hι] at this
  have h2 : IsGenericPoint P.genericPoint (P.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isGenericPoint_closure
  exact h1.eq h2

/-- A closed subscheme onto a prime divisor of an `(n + 1)`-dimensional variety has dimension
`n`. -/
private theorem topologicalKrullDim_eq_of_range_eq_support {X S : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {n : ℕ}
    (hdim : topologicalKrullDim X = (n + 1 : ℕ)) (P : MMP.Mori.PrimeDivisor X) (ι : S ⟶ X)
    [IsClosedImmersion ι] (hι : Set.range ι.base = (P.support : Set X)) :
    topologicalKrullDim S = n := by
  have h1 : topologicalKrullDim S = topologicalKrullDim (Set.range ι.base) :=
    ι.isClosedEmbedding.toIsEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq
  have h2 : (P.support : Set X) = closure {P.genericPoint} :=
    AlgebraicGeometry.PrimeDivisor.support_eq_closure P
  have h3 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX P.genericPoint
  rw [P.coheight_genericPoint, hdim] at h3
  rw [h1, hι, h2]
  exact eq_of_add_one_eq h3

/-! ### Numerical toolkit -/

section Numerics

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
  [IsNormal X]

/-- Every presentation of an `ℝ`-Cartier divisor computes an intersection number. -/
private theorem exists_isRIntersectionNumber {D : RDivisor X} {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor X} (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) (C : ProperCurve sX) :
    ∃ x, IsRIntersectionNumber k sX D r L C x := by
  rw [hD]; exact ⟨_, isRIntersectionNumber_sum_degreeOn' k sX C r L hL⟩

private theorem presentation_of_isCartierCombination {D : RDivisor X}
    (hD : IsCartierCombination D) : ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X),
      (∀ j, (L j).IsCartier) ∧ D = ∑ j, r j • Divisor.toRDivisor (L j) := by
  obtain ⟨m, r, L, hL, hD⟩ := hD
  exact ⟨m, r, L, hL, by simpa only [toRDivisor_eq_mapCoeffs] using hD⟩

private theorem isCartierCombination_of_presentation {D : RDivisor X} {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor X} (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) : IsCartierCombination D :=
  ⟨m, r, L, hL, by simpa only [toRDivisor_eq_mapCoeffs] using hD⟩

private theorem isRIntersectionNumber_eq {C : ProperCurve sX} {D : RDivisor X} {m m' : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor X} {r' : Fin m' → ℝ} {L' : Fin m' → Divisor X}
    {x x' : ℝ} (h : IsRIntersectionNumber k sX D r L C x)
    (h' : IsRIntersectionNumber k sX D r' L' C x') : x = x' :=
  (IsRIntersectionNumber.eq_and_linear k sX C).1 D r L r' L' x x' h h'

/-- Nefness, for every presentation. -/
private theorem isRelativelyNef_iff {f : X ⟶ Y} {D : RDivisor X} :
    IsRelativelyNef k sX f D ↔ IsCartierCombination D ∧ ∀ C : ProperCurve sX,
      C.IsContractedBy f → ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
        IsRIntersectionNumber k sX D r L C x → 0 ≤ x := by
  constructor
  · rintro ⟨m, r, L, hL, hD, hnn⟩
    refine ⟨isCartierCombination_of_presentation hL hD, fun C hC m' r' L' x' hx' => ?_⟩
    obtain ⟨x, hx⟩ := exists_isRIntersectionNumber hL hD C
    exact (isRIntersectionNumber_eq hx hx') ▸ hnn C hC x hx
  · rintro ⟨hD, hnn⟩
    obtain ⟨m, r, L, hL, hD⟩ := presentation_of_isCartierCombination hD
    exact ⟨m, r, L, hL, hD, fun C hC x hx => hnn C hC m r L x hx⟩

/-- Numerical triviality, for every presentation. -/
private theorem isNumericallyTrivialOver_iff {f : X ⟶ Y} {D : RDivisor X} :
    IsNumericallyTrivialOver k sX f D ↔ IsCartierCombination D ∧ ∀ C : ProperCurve sX,
      C.IsContractedBy f → ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
        IsRIntersectionNumber k sX D r L C x → x = 0 := by
  constructor
  · rintro ⟨hD, -, h⟩
    exact ⟨hD, fun C hC m r L x hx => h C hC m r L x 0 _ _ 0 hx (isRIntersectionNumber_zero C)⟩
  · rintro ⟨hD, h⟩
    refine ⟨hD, ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by ext; simp⟩,
      fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
    rw [h C hC m₁ r₁ L₁ x₁ h₁, ← isRIntersectionNumber_eq (isRIntersectionNumber_zero C) h₂]

private theorem isRIntersectionNumber_combination {C : ProperCurve sX} {D₁ D₂ : RDivisor X}
    (h₁ : IsCartierCombination D₁) (h₂ : IsCartierCombination D₂) (a b : ℝ) :
    ∃ x₁ x₂, (∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
        IsRIntersectionNumber k sX D₁ r L C x → x = x₁) ∧
      (∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
        IsRIntersectionNumber k sX D₂ r L C x → x = x₂) ∧
      (∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
        IsRIntersectionNumber k sX (a • D₁ + b • D₂) r L C x → x = a * x₁ + b * x₂) := by
  obtain ⟨m₁, r₁, L₁, hL₁, hD₁⟩ := presentation_of_isCartierCombination h₁
  obtain ⟨m₂, r₂, L₂, hL₂, hD₂⟩ := presentation_of_isCartierCombination h₂
  obtain ⟨x₁, hx₁⟩ := exists_isRIntersectionNumber hL₁ hD₁ C
  obtain ⟨x₂, hx₂⟩ := exists_isRIntersectionNumber hL₂ hD₂ C
  have hlin := (IsRIntersectionNumber.eq_and_linear k sX C).2 D₁ D₂ r₁ L₁ r₂ L₂ x₁ x₂ a b hx₁ hx₂
  exact ⟨x₁, x₂, fun m r L x hx => isRIntersectionNumber_eq hx hx₁,
    fun m r L x hx => isRIntersectionNumber_eq hx hx₂,
    fun m r L x hx => isRIntersectionNumber_eq hx hlin⟩

private theorem isCartierCombination_smul_add {D₁ D₂ : RDivisor X} (h₁ : IsCartierCombination D₁)
    (h₂ : IsCartierCombination D₂) (a b : ℝ) : IsCartierCombination (a • D₁ + b • D₂) := by
  obtain ⟨m₁, r₁, L₁, hL₁, hD₁⟩ := presentation_of_isCartierCombination h₁
  obtain ⟨m₂, r₂, L₂, hL₂, hD₂⟩ := presentation_of_isCartierCombination h₂
  refine isCartierCombination_of_presentation (r := Fin.append (a • r₁) (b • r₂))
    (L := Fin.append L₁ L₂) (fun j => Fin.addCases (fun i => by simpa using hL₁ i)
      (fun i => by simpa using hL₂ i) j) ?_
  rw [Fin.sum_univ_add, hD₁, hD₂, Finset.smul_sum, Finset.smul_sum]
  simp [smul_smul]

private theorem IsRelativelyNef.smul_add {f : X ⟶ Y} {D₁ D₂ : RDivisor X}
    (h₁ : IsRelativelyNef k sX f D₁) (h₂ : IsRelativelyNef k sX f D₂) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) : IsRelativelyNef k sX f (a • D₁ + b • D₂) := by
  rw [isRelativelyNef_iff] at h₁ h₂ ⊢
  refine ⟨isCartierCombination_smul_add h₁.1 h₂.1 a b, fun C hC m r L x hx => ?_⟩
  obtain ⟨x₁, x₂, e₁, e₂, e⟩ := isRIntersectionNumber_combination (C := C) h₁.1 h₂.1 a b
  obtain ⟨m₁, r₁, L₁, hL₁, hD₁⟩ := presentation_of_isCartierCombination h₁.1
  obtain ⟨m₂, r₂, L₂, hL₂, hD₂⟩ := presentation_of_isCartierCombination h₂.1
  obtain ⟨y₁, hy₁⟩ := exists_isRIntersectionNumber hL₁ hD₁ C
  obtain ⟨y₂, hy₂⟩ := exists_isRIntersectionNumber hL₂ hD₂ C
  rw [e m r L x hx, ← e₁ _ _ _ _ hy₁, ← e₂ _ _ _ _ hy₂]
  have := h₁.2 C hC _ _ _ _ hy₁
  have := h₂.2 C hC _ _ _ _ hy₂
  positivity

private theorem IsNumericallyTrivialOver.smul_add {f : X ⟶ Y} {D₁ D₂ : RDivisor X}
    (h₁ : IsNumericallyTrivialOver k sX f D₁) (h₂ : IsNumericallyTrivialOver k sX f D₂)
    (a b : ℝ) : IsNumericallyTrivialOver k sX f (a • D₁ + b • D₂) := by
  rw [isNumericallyTrivialOver_iff] at h₁ h₂ ⊢
  refine ⟨isCartierCombination_smul_add h₁.1 h₂.1 a b, fun C hC m r L x hx => ?_⟩
  obtain ⟨x₁, x₂, e₁, e₂, e⟩ := isRIntersectionNumber_combination (C := C) h₁.1 h₂.1 a b
  obtain ⟨m₁, r₁, L₁, hL₁, hD₁⟩ := presentation_of_isCartierCombination h₁.1
  obtain ⟨m₂, r₂, L₂, hL₂, hD₂⟩ := presentation_of_isCartierCombination h₂.1
  obtain ⟨y₁, hy₁⟩ := exists_isRIntersectionNumber hL₁ hD₁ C
  obtain ⟨y₂, hy₂⟩ := exists_isRIntersectionNumber hL₂ hD₂ C
  rw [e m r L x hx, ← e₁ _ _ _ _ hy₁, ← e₂ _ _ _ _ hy₂, h₁.2 C hC _ _ _ _ hy₁,
    h₂.2 C hC _ _ _ _ hy₂]
  ring

private theorem IsRelativelyNef.add_isNumericallyTrivialOver {f : X ⟶ Y} {D N : RDivisor X}
    (h₁ : IsRelativelyNef k sX f D) (h₂ : IsNumericallyTrivialOver k sX f N) (b : ℝ) :
    IsRelativelyNef k sX f (D + b • N) := by
  rw [isRelativelyNef_iff] at h₁ ⊢
  rw [isNumericallyTrivialOver_iff] at h₂
  have hc := isCartierCombination_smul_add h₁.1 h₂.1 1 b
  rw [one_smul] at hc
  refine ⟨hc, fun C hC m r L x hx => ?_⟩
  obtain ⟨x₁, x₂, e₁, e₂, e⟩ := isRIntersectionNumber_combination (C := C) h₁.1 h₂.1 1 b
  obtain ⟨m₁, r₁, L₁, hL₁, hD₁⟩ := presentation_of_isCartierCombination h₁.1
  obtain ⟨m₂, r₂, L₂, hL₂, hD₂⟩ := presentation_of_isCartierCombination h₂.1
  obtain ⟨y₁, hy₁⟩ := exists_isRIntersectionNumber hL₁ hD₁ C
  obtain ⟨y₂, hy₂⟩ := exists_isRIntersectionNumber hL₂ hD₂ C
  rw [← one_smul ℝ D] at hx
  rw [e m r L x hx, ← e₁ _ _ _ _ hy₁, ← e₂ _ _ _ _ hy₂, h₂.2 C hC _ _ _ _ hy₂]
  have := h₁.2 C hC _ _ _ _ hy₁
  linarith

private theorem IsNumericallyTrivialOver.isRelativelyNef_neg {f : X ⟶ Y} {N : RDivisor X}
    (h : IsNumericallyTrivialOver k sX f N) : IsRelativelyNef k sX f (-N) := by
  have := IsNumericallyTrivialOver.smul_add h h (-1) 0
  rw [neg_one_smul, zero_smul, add_zero] at this
  exact isRelativelyNef_of_isNumericallyTrivialOver this

private theorem isNumericallyTrivialOver_of_isRelativelyNef_of_neg {f : X ⟶ Y} {N : RDivisor X}
    (h₁ : IsRelativelyNef k sX f N) (h₂ : IsRelativelyNef k sX f (-N)) :
    IsNumericallyTrivialOver k sX f N := by
  rw [isRelativelyNef_iff] at h₁ h₂
  rw [isNumericallyTrivialOver_iff]
  refine ⟨h₁.1, fun C hC m r L x hx => ?_⟩
  obtain ⟨x₁, x₂, e₁, e₂, e⟩ := isRIntersectionNumber_combination (C := C) h₁.1 h₁.1 (-1) 0
  obtain ⟨m₁, r₁, L₁, hL₁, hD₁⟩ := presentation_of_isCartierCombination h₂.1
  obtain ⟨y, hy⟩ := exists_isRIntersectionNumber hL₁ hD₁ C
  have hy' := hy
  rw [show -N = (-1 : ℝ) • N + (0 : ℝ) • N by simp] at hy'
  have h1 := e _ _ _ _ hy'
  have h2 := e₁ _ _ _ _ hx
  have h3 := h₂.2 C hC _ _ _ _ hy
  have h4 := h₁.2 C hC _ _ _ _ hx
  subst h2
  linarith

/-- A principal divisor is numerically trivial over every base. -/
private theorem isNumericallyTrivialOver_principalDivisor [IsIntegral X] [CompactSpace X]
    (f : X ⟶ Y) (φ : (RationalFunctions X)ˣ) :
    IsNumericallyTrivialOver k sX f (Divisor.toRDivisor (MMP.Mori.principalDivisor φ)) := by
  have hc := MMP.Mori.Divisor.isCartier_principalDivisor φ
  have hP : Divisor.toRDivisor (MMP.Mori.principalDivisor φ) =
      ∑ j : Fin 1, (fun _ => (1 : ℝ)) j • Divisor.toRDivisor
        ((fun _ => MMP.Mori.principalDivisor φ) j) := by simp
  rw [isNumericallyTrivialOver_iff]
  refine ⟨isCartierCombination_of_presentation (fun _ => hc) hP, fun C hC m r L x hx => ?_⟩
  have hv := isRIntersectionNumber_sum_degreeOn' k sX C (m := 1) (fun _ : Fin 1 => (1 : ℝ))
    (fun _ : Fin 1 => MMP.Mori.principalDivisor φ) (fun _ => hc)
  rw [← hP] at hv
  rw [isRIntersectionNumber_eq hx hv]
  have h0 : (MMP.Mori.principalDivisor φ).LinearlyEquivalent 0 := ⟨φ, by simp⟩
  simp [MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX C.ι C.dim_le hc h0]

/-- A relatively ample `ℝ`-divisor has positive intersection with every contracted curve, for
every presentation. -/
private theorem pos_of_isRelativelyAmple {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {f : X ⟶ Y}
    {A : RDivisor X} (hA : IsRelativelyAmple f A) (C : ProperCurve sX) (hC : C.IsContractedBy f)
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber ℂ sX A r L C x) : 0 < x := by
  obtain ⟨m', s, A', hm, hs, hA', hAeq⟩ := hA
  choose hL hpos using fun j => degreeOn_pos_of_isRelativelyAmpleCartier (hA' j) C hC
  have hx' := isRIntersectionNumber_sum_degreeOn' ℂ sX C s A' hL
  rw [← hAeq] at hx'
  rw [isRIntersectionNumber_eq hx hx']
  have hne : (Finset.univ : Finset (Fin m')).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
  exact Finset.sum_pos (fun j _ => mul_pos (hs j) (by exact_mod_cast hpos j)) hne

/-- A relatively ample `ℝ`-divisor is relatively nef. -/
private theorem isRelativelyNef_of_isRelativelyAmple {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {f : X ⟶ Y}
    {A : RDivisor X} (hA : IsRelativelyAmple f A) : IsRelativelyNef ℂ sX f A := by
  obtain ⟨m, s, L, hm, hs, hL, hAeq⟩ := id hA
  exact isRelativelyNef_iff.mpr ⟨isCartierCombination_of_presentation (fun j => (hL j).1) hAeq,
    fun C hC _ _ _ _ hx => (pos_of_isRelativelyAmple hA C hC hx).le⟩

/-- Positivity on contracted curves survives adding a numerically trivial divisor. -/
private theorem pos_add_isNumericallyTrivialOver {f : X ⟶ Y} {D N : RDivisor X}
    (hD : IsCartierCombination D)
    (hpos : ∀ C : ProperCurve sX, C.IsContractedBy f → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor X) (x : ℝ), IsRIntersectionNumber k sX D r L C x → 0 < x)
    (hN : IsNumericallyTrivialOver k sX f N) (b : ℝ) :
    ∀ C : ProperCurve sX, C.IsContractedBy f → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor X) (x : ℝ), IsRIntersectionNumber k sX (D + b • N) r L C x → 0 < x := by
  rw [isNumericallyTrivialOver_iff] at hN
  intro C hC m r L x hx
  obtain ⟨x₁, x₂, e₁, e₂, e⟩ := isRIntersectionNumber_combination (C := C) hD hN.1 1 b
  obtain ⟨m₁, r₁, L₁, hL₁, hD₁⟩ := presentation_of_isCartierCombination hD
  obtain ⟨m₂, r₂, L₂, hL₂, hD₂⟩ := presentation_of_isCartierCombination hN.1
  obtain ⟨y₁, hy₁⟩ := exists_isRIntersectionNumber hL₁ hD₁ C
  obtain ⟨y₂, hy₂⟩ := exists_isRIntersectionNumber hL₂ hD₂ C
  rw [← one_smul ℝ D] at hx
  rw [e m r L x hx, ← e₁ _ _ _ _ hy₁, ← e₂ _ _ _ _ hy₂, hN.2 C hC _ _ _ _ hy₂]
  have := hpos C hC _ _ _ _ hy₁
  linarith

end Numerics

/-! ### Pull-backs of nef and numerically trivial divisors -/

/-- An `ℝ`-Cartier pull-back is an `ℝ`-Cartier combination. -/
private theorem isCartierCombination_of_isRCartierPullback {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {D : RDivisor X} {G : RDivisor Y} (h : IsRCartierPullback f D G) : IsCartierCombination G := by
  obtain ⟨m, r, L, L', hL, -, hpb, rfl⟩ := h
  choose hB hpbj using hpb
  have hL'c : ∀ j, (L' j).IsCartier := fun j => by
    rw [← Divisor.IsPullback.pullback_eq (hL j) (hpbj j)]
    exact (hL j).isCartier_pullback f (hB j)
  exact isCartierCombination_of_presentation hL'c rfl

section Pullback

variable {W Z S : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
  [IsLocallyNoetherian Z] [IsNormal Z] {sZ : Z ⟶ Spec (.of k)} [IsSeparated sZ]
  [LocallyOfFiniteType sZ] [QuasiCompact sZ]

/-- The pull-back of a divisor nef over `S` is nef over `S`. -/
private theorem IsRelativelyNef.isRCartierPullback (πZ : Z ⟶ S) (q : W ⟶ Z) [IsProper q]
    [QuasiCompact (q ≫ sZ)] {M : RDivisor Z} (hM : IsRelativelyNef k sZ πZ M) {M' : RDivisor W}
    (hM' : IsRCartierPullback q M M') : IsRelativelyNef k (q ≫ sZ) (q ≫ πZ) M' :=
  MMP.Fourfold.isRelativelyNef_of_isRCartierPullback (𝟙 S) πZ (q ≫ πZ) q (by simp) hM hM'

/-- The pull-back of a divisor numerically trivial over `S` is numerically trivial over `S`. -/
private theorem IsNumericallyTrivialOver.isRCartierPullback (πZ : Z ⟶ S) (q : W ⟶ Z)
    [IsProper q] [QuasiCompact (q ≫ sZ)] {M : RDivisor Z}
    (hM : IsNumericallyTrivialOver k sZ πZ M) {M' : RDivisor W}
    (hM' : IsRCartierPullback q M M') : IsNumericallyTrivialOver k (q ≫ sZ) (q ≫ πZ) M' := by
  have hneg := MMP.Fourfold.isRCartierPullback_smul (-1) hM'
  rw [neg_one_smul, neg_one_smul] at hneg
  exact isNumericallyTrivialOver_of_isRelativelyNef_of_neg
    (IsRelativelyNef.isRCartierPullback πZ q (isRelativelyNef_of_isNumericallyTrivialOver hM) hM')
    (IsRelativelyNef.isRCartierPullback πZ q
      (IsNumericallyTrivialOver.isRelativelyNef_neg hM) hneg)

/-- Nefness transfers along a pull-back up to numerically trivial corrections: if
`q^*(N + M) = N' + M'` with `M`, `M'` numerically trivial and `N` nef over `S`, then `N'` is nef
over `S`. -/
private theorem IsRelativelyNef.of_isRCartierPullback_add (πZ : Z ⟶ S) (q : W ⟶ Z) [IsProper q]
    [QuasiCompact (q ≫ sZ)] {N M : RDivisor Z} {N' M' : RDivisor W}
    (hpb : IsRCartierPullback q (N + M) (N' + M')) (hM : IsNumericallyTrivialOver k sZ πZ M)
    (hM' : IsNumericallyTrivialOver k (q ≫ sZ) (q ≫ πZ) M') (hN : IsRelativelyNef k sZ πZ N) :
    IsRelativelyNef k (q ≫ sZ) (q ≫ πZ) N' := by
  have h0 := IsRelativelyNef.add_isNumericallyTrivialOver hN hM 1
  rw [one_smul] at h0
  have h1 := IsRelativelyNef.add_isNumericallyTrivialOver
    (IsRelativelyNef.isRCartierPullback πZ q h0 hpb) hM' (-1)
  rwa [neg_one_smul, add_neg_cancel_right] at h1

/-- Numerical triviality transfers along a pull-back up to numerically trivial corrections. -/
private theorem IsNumericallyTrivialOver.of_isRCartierPullback_add (πZ : Z ⟶ S) (q : W ⟶ Z)
    [IsProper q] [QuasiCompact (q ≫ sZ)] {N M : RDivisor Z} {N' M' : RDivisor W}
    (hpb : IsRCartierPullback q (N + M) (N' + M')) (hM : IsNumericallyTrivialOver k sZ πZ M)
    (hM' : IsNumericallyTrivialOver k (q ≫ sZ) (q ≫ πZ) M')
    (hN : IsNumericallyTrivialOver k sZ πZ N) :
    IsNumericallyTrivialOver k (q ≫ sZ) (q ≫ πZ) N' := by
  have h0 := IsNumericallyTrivialOver.smul_add hN hM 1 1
  rw [one_smul, one_smul] at h0
  have h1 := IsNumericallyTrivialOver.smul_add
    (IsNumericallyTrivialOver.isRCartierPullback πZ q h0 hpb) hM' 1 (-1)
  rwa [one_smul, neg_one_smul, add_neg_cancel_right] at h1

/-- **Positivity transfers along a pull-back to curves which are not contracted.** If `M` has
positive intersection with every curve contracted by `π_Z`, `M' = q^* M`, and the proper curve `γ`
is contracted by `q ≫ π_Z` but not by `q`, then `M' · γ = [k(γ) : k(q γ)] (M · q γ) > 0`. -/
private theorem pos_of_isRCartierPullback (πZ : Z ⟶ S) (q : W ⟶ Z) [IsProper q]
    [QuasiCompact (q ≫ sZ)] [CompactSpace W] {M : RDivisor Z} {M' : RDivisor W}
    (hM : IsRCartierPullback q M M')
    (hpos : ∀ C : ProperCurve sZ, C.IsContractedBy πZ → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor Z) (x : ℝ), IsRIntersectionNumber k sZ M r L C x → 0 < x)
    (γ : ProperCurve (q ≫ sZ)) (hγ : γ.IsContractedBy (q ≫ πZ)) (hγq : ¬ γ.IsContractedBy q)
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W} {x : ℝ}
    (hx : IsRIntersectionNumber k (q ≫ sZ) M' r L γ x) : 0 < x := by
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  obtain ⟨m₀, r₀, L₀, L₁, hL₀, hMeq, hpb, rfl⟩ := hM
  choose hB hpbj using hpb
  have hL₁c : ∀ j, (L₁ j).IsCartier := fun j => by
    rw [← Divisor.IsPullback.pullback_eq (hL₀ j) (hpbj j)]
    exact (hL₀ j).isCartier_pullback q (hB j)
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ProperCurve sZ, C₀.point = q γ.point :=
    ⟨⟨q γ.point, MMP.Fourfold.Oai4C1.isProperCurve_map q rfl γ hγq⟩, rfl⟩
  have hC₀c : C₀.IsContractedBy πZ := by
    intro z hz
    rw [hC₀] at hz ⊢
    have hsub : closure ({q γ.point} : Set Z) ⊆ q '' closure ({γ.point} : Set W) :=
      closure_minimal (Set.singleton_subset_iff.2 ⟨γ.point, subset_closure rfl, rfl⟩)
        (q.isClosedMap _ isClosed_closure)
    obtain ⟨w, hw, rfl⟩ := hsub hz
    have := hγ w hw
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
    exact this
  have hdeg : ∀ j, (((L₁ j).degreeOn k (q ≫ sZ) γ.ι γ.dim_le (hL₁c j) : ℤ) : ℝ) =
      (residueFieldDegree q γ.point : ℝ) * (L₀ j).degreeOn k sZ C₀.ι C₀.dim_le (hL₀ j) :=
    fun j => MMP.Fourfold.degreeOn_eq_mul_of_isPullback q rfl (hL₀ j) (hpbj j) (hL₁c j) γ C₀
      hC₀.symm
  have hx' := isRIntersectionNumber_sum_degreeOn' k (q ≫ sZ) γ r₀ L₁ hL₁c
  rw [isRIntersectionNumber_eq hx hx']
  have h0 := isRIntersectionNumber_sum_degreeOn' k sZ C₀ r₀ L₀ hL₀
  rw [← hMeq] at h0
  have hp := hpos C₀ hC₀c _ _ _ _ h0
  have hrfd : (0 : ℝ) < residueFieldDegree q γ.point := by
    exact_mod_cast MMP.ProgramBaseChange.residueFieldDegree_pos_of_not_isContractedBy q rfl γ hγq
  simp only [hdeg, mul_left_comm (r₀ _), ← Finset.mul_sum]
  exact mul_pos hrfd hp

/-- The pull-back of an `ℝ`-Cartier divisor has zero intersection with every curve contracted by
the morphism. -/
private theorem eq_zero_of_isRCartierPullback_of_isContractedBy (q : W ⟶ Z) [IsProper q]
    [QuasiCompact (q ≫ sZ)] [CompactSpace W] {M : RDivisor Z} {M' : RDivisor W}
    (hM : IsRCartierPullback q M M') (γ : ProperCurve (q ≫ sZ)) (hγ : γ.IsContractedBy q)
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W} {x : ℝ}
    (hx : IsRIntersectionNumber k (q ≫ sZ) M' r L γ x) : x = 0 := by
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  obtain ⟨m₀, r₀, L₀, L₁, hL₀, -, hpb, rfl⟩ := hM
  choose hB hpbj using hpb
  obtain rfl : L₁ = fun j => (L₀ j).pullback (hL₀ j) (hB j) :=
    funext fun j => (Divisor.IsPullback.pullback_eq (hL₀ j) (hpbj j)).symm
  have hL₁c : ∀ j, ((L₀ j).pullback (hL₀ j) (hB j)).IsCartier := fun j =>
    (hL₀ j).isCartier_pullback q (hB j)
  have hx' := isRIntersectionNumber_sum_degreeOn' k (q ≫ sZ) γ r₀ _ hL₁c
  rw [isRIntersectionNumber_eq hx hx']
  have hdeg : ∀ j, ((L₀ j).pullback (hL₀ j) (hB j)).degreeOn k (q ≫ sZ) γ.ι γ.dim_le
      (hL₁c j) = 0 := fun j =>
    MMP.Mori.Divisor.degreeOn_pullback_eq_zero_of_isContractedBy q rfl (hL₀ j) (hB j) γ hγ
  simp [hdeg]

/-- **Curves contracted by one side of a crepant comparison.** If `p^* N_V = q^* N_Z` on `W`,
with `p ≫ π_V = q ≫ π_Z` and `N_Z` positive on the curves contracted by `π_Z`, then every curve
contracted by `p` is contracted by `q`. -/
private theorem isContractedBy_of_isRCartierPullback_eq {V : Scheme.{0}} [IsLocallyNoetherian V]
    [IsNormal V] {sV : V ⟶ Spec (.of k)} [IsSeparated sV] [LocallyOfFiniteType sV]
    [QuasiCompact sV] (πV : V ⟶ S) (πZ : Z ⟶ S) (p : W ⟶ V) (q : W ⟶ Z) [IsProper p]
    [IsProper q] [QuasiCompact (q ≫ sZ)] [CompactSpace W] (hpq : p ≫ πV = q ≫ πZ)
    (hps : p ≫ sV = q ≫ sZ) {NV : RDivisor V} {NZ : RDivisor Z} {D : RDivisor W}
    (hp : IsRCartierPullback p NV D) (hq : IsRCartierPullback q NZ D)
    (hpos : ∀ C : ProperCurve sZ, C.IsContractedBy πZ → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor Z) (x : ℝ), IsRIntersectionNumber k sZ NZ r L C x → 0 < x)
    (γ : ProperCurve (q ≫ sZ)) (hγ : γ.IsContractedBy p) : γ.IsContractedBy q := by
  by_contra hγq
  have hγZ : γ.IsContractedBy (q ≫ πZ) := by
    rw [← hpq]; exact isContractedBy_comp hγ πV
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  obtain ⟨m, r, L, hL, hD⟩ :=
    presentation_of_isCartierCombination (isCartierCombination_of_isRCartierPullback hq)
  obtain ⟨x, hx⟩ := exists_isRIntersectionNumber hL hD γ
  have h1 := pos_of_isRCartierPullback πZ q hq hpos γ hγZ hγq hx
  have key : ∀ (s : W ⟶ Spec (.of k)) [QuasiCompact s], s = p ≫ sV → ∀ (γ' : ProperCurve s),
      γ'.IsContractedBy p → ∀ {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W} {x : ℝ},
        IsRIntersectionNumber k s D r L γ' x → x = 0 := by
    rintro s _ rfl γ' hγ' m r L x hx
    exact eq_zero_of_isRCartierPullback_of_isContractedBy p hp γ' hγ' hx
  have h2 := key _ hps.symm γ hγ hx
  linarith

end Pullback

/-- **Nefness descends along a proper surjection.** If the pull-back of an `ℝ`-Cartier divisor `M`
along a proper surjective `q` is nef over `S`, then `M` is nef over `S`: a curve on the target is
the image of a curve on the source, and the projection formula multiplies intersection numbers
by the positive degree of the function field extension. -/
private theorem IsRelativelyNef.of_isRCartierPullback {W Y S : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    (π : Y ⟶ S) (q : W ⟶ Y) [IsProper q] [Surjective q] [LocallyOfFiniteType (q ≫ sY)]
    [QuasiCompact (q ≫ sY)] {M : RDivisor Y} (hMc : IsCartierCombination M) {M' : RDivisor W}
    (hM' : IsRCartierPullback q M M') (hnef : IsRelativelyNef k (q ≫ sY) (q ≫ π) M') :
    IsRelativelyNef k sY π M := by
  haveI : CompactSpace Y := (quasiCompact_iff_compactSpace sY).mp inferInstance
  rw [isRelativelyNef_iff] at hnef ⊢
  refine ⟨hMc, fun γ' hγ' m₂ r₂ L₂ x hx => ?_⟩
  obtain ⟨m, r, L, L', hL, hMeq, hpb, hM'eq⟩ := hM'
  choose hB hpbj using hpb
  have hL'c : ∀ j, (L' j).IsCartier := fun j => by
    rw [← Divisor.IsPullback.pullback_eq (hL j) (hpbj j)]
    exact (hL j).isCartier_pullback q (hB j)
  obtain ⟨γ, hγq, hdeg⟩ := MMP.Fourfold.exists_properCurve_map_eq (q ≫ sY) sY q rfl γ'
  have hγ : γ.IsContractedBy (q ≫ π) := by
    intro w hw
    have hw' : q w ∈ closure ({γ'.point} : Set Y) := by
      rw [← hγq, ← specializes_iff_mem_closure]
      exact (specializes_iff_mem_closure.mpr hw).map q.base.hom.continuous
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
    change π (q w) = π (q γ.point)
    rw [hγ' _ hw', hγq]
  have hx' := isRIntersectionNumber_sum_degreeOn' k (q ≫ sY) γ r L' hL'c
  rw [← hM'eq] at hx'
  have hnn := hnef.2 γ hγ _ _ _ _ hx'
  have hy := isRIntersectionNumber_sum_degreeOn' k sY γ' r L hL
  rw [← hMeq] at hy
  rw [isRIntersectionNumber_eq hx hy]
  have hproj : ∀ j, ((L' j).degreeOn k (q ≫ sY) γ.ι γ.dim_le (hL'c j) : ℝ) =
      (residueFieldDegree q γ.point : ℝ) * ((L j).degreeOn k sY γ'.ι γ'.dim_le (hL j) : ℝ) :=
    fun j => MMP.Fourfold.degreeOn_eq_mul_of_isPullback q rfl (hL j) (hpbj j) (hL'c j) γ γ' hγq
  simp_rw [hproj] at hnn
  have hpos : (0 : ℝ) < residueFieldDegree q γ.point := by exact_mod_cast Nat.pos_of_ne_zero hdeg
  have hsum : (residueFieldDegree q γ.point : ℝ) *
      ∑ j, r j * ((L j).degreeOn k sY γ'.ι γ'.dim_le (hL j) : ℝ) =
      ∑ j, r j * ((residueFieldDegree q γ.point : ℝ) *
        ((L j).degreeOn k sY γ'.ι γ'.dim_le (hL j) : ℝ)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [← hsum] at hnn
  by_contra hc
  push Not at hc
  have := mul_neg_of_pos_of_neg hpos hc
  linarith

/-- A prime divisor of the target of a proper birational morphism of normal varieties has a
unique prime divisor over it. -/
private theorem eq_of_map_genericPoint_eq {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral X] [CompactSpace X] [CompactSpace Y]
    {sY : Y ⟶ Spec (.of k)}
    (hY : IsNormalVariety k sY) {f : X ⟶ Y} (hX : IsNormalVariety k (f ≫ sY)) [IsProper f]
    (hf : IsBirationalMorphism f) (F : MMP.Mori.PrimeDivisor Y) (E₁ E₂ : MMP.Mori.PrimeDivisor X)
    (h₁ : f E₁.genericPoint = F.genericPoint) (h₂ : f E₂.genericPoint = F.genericPoint) :
    E₁ = E₂ := by
  have := hY.1
  have : IsSeparated (Y ↘ Limits.terminal Scheme) := by
    rw [show (Y ↘ Limits.terminal Scheme) = sY ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  obtain ⟨E, -, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hX hf F
  have key : ∀ E₀ : MMP.Mori.PrimeDivisor X, f E₀.genericPoint = F.genericPoint → E₀ = E := by
    intro E₀ h₀
    have h := htr (Finsupp.single E₀ (1 : ℤ))
    rw [MMP.Mori.RationalMap.transformDivisor_single_of_eq_some
      ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f E₀ F).mpr h₀)] at h
    by_contra hne
    simp [Finsupp.single_apply, Ne.symm hne] at h
  exact (key E₁ h₁).trans (key E₂ h₂).symm

/-- **Transforms through a common resolution.** If `p : W ⟶ X`, `q : W ⟶ Y` resolve a birational
map `φ = q ∘ p⁻¹` of normal varieties under which no prime divisor of `Y` is exceptional for
`φ⁻¹`, then `q_* D = φ_* (p_* D)` for every divisor `D` on `W`. -/
private theorem transformDivisor_eq_transformDivisor_transformDivisor {X Y W : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace X]
    [CompactSpace Y] [CompactSpace W]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) {φ : X.RationalMap Y}
    (hφE : ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W) [IsProper p] [IsProper q]
    (hWp : IsNormalVariety k (p ≫ sX)) (hWq : IsNormalVariety k (q ≫ sY))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (hcomp : h.compHom q = φ)
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R W) :
    MMP.Mori.RationalMap.transformDivisor q.toRationalMap D =
      MMP.Mori.RationalMap.transformDivisor φ
        (MMP.Mori.RationalMap.transformDivisor p.toRationalMap D) := by
  refine Finsupp.ext fun F => ?_
  obtain ⟨P, hP⟩ := not_forall.mp (hφE F)
  rw [not_not] at hP
  obtain ⟨E, hpE, -, hqE, -⟩ :=
    MMP.Fourfold.exists_primeDivisor_apply_eq_of_transformPrimeDivisor_eq_some hX hY p q h hWp
      hpb hqb hinv hcomp hP
  obtain ⟨E', hqE', -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hWq hqb F
  rw [htr, eq_of_map_genericPoint_eq hY hWq hqb F E' E hqE' hqE]
  change D E = DivisorWithCoeffs.mapPrimeDivisors _ _ F
  rw [MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hP ?_ _]
  · obtain ⟨E'', hpE'', -, htrp⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX hWp hpb P
    rw [htrp D, eq_of_map_genericPoint_eq hX hWp hpb P E'' E hpE'' hpE]
  · intro P' hP'
    obtain ⟨E₂, hpE₂, -, hqE₂, -⟩ :=
      MMP.Fourfold.exists_primeDivisor_apply_eq_of_transformPrimeDivisor_eq_some hX hY p q h hWp
        hpb hqb hinv hcomp hP'
    have hgen : P'.genericPoint = P.genericPoint := by
      rw [← hpE₂, ← hpE, eq_of_map_genericPoint_eq hY hWq hqb F E₂ E hqE₂ hqE]
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective hgen

/-- **The transform of a canonical divisor along a birational contraction is canonical.** Through
a common resolution `(W, p, q)`: a canonical divisor `K_W` with `p_* K_W = K` exists, `q_* K_W`
is canonical, and `q_* K_W = φ_* K`. -/
private theorem isCanonicalDivisor_transformDivisor_of_resolution {X Y W : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (hX : IsNormalVariety ℂ sX) (hY : IsNormalVariety ℂ sY) {φ : X.RationalMap Y}
    (hφE : ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W) [IsProper p] [IsProper q]
    [LocallyOfFiniteType (p ≫ sX)] [LocallyOfFiniteType (q ≫ sY)]
    (hWp : IsNormalVariety ℂ (p ≫ sX)) (hWq : IsNormalVariety ℂ (q ≫ sY))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (hcomp : h.compHom q = φ)
    (hpq : p ≫ sX = q ≫ sY)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {K' : Divisor Y}
    (hK' : K'.IsCanonicalDivisor sY n) :
    Divisor.IsCanonicalDivisor sY n (MMP.Mori.RationalMap.transformDivisor φ K) := by
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hdimW : topologicalKrullDim W = n := by
    rw [← hK.topologicalKrullDim_eq]
    haveI := hWp.1
    haveI := hX.1
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hpb).symm
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (p ≫ sX) hWp hdimW
  obtain ⟨KW, hKW, hpKW⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hX hWp hpb hK hK₀
  have hKW' : KW.IsCanonicalDivisor (q ≫ sY) n := by
    rwa [← hpq]
  have hq := MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hY hWq hqb hK' hKW'
  rw [transformDivisor_eq_transformDivisor_transformDivisor hX hY hφE p q h hWp hWq hpb hqb hinv
    hcomp KW, hpKW] at hq
  exact hq

/-- Two canonical divisors of a normal variety are linearly equivalent. -/
private theorem linearlyEquivalent_of_isCanonicalDivisor' {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] (hX : IsNormalVariety ℂ sX) {n : ℕ} {K K' : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (hK' : K'.IsCanonicalDivisor sX n) :
    K.LinearlyEquivalent K' := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hKω : divisorOfForm ω = K := Finsupp.ext fun Γ => hω Γ
  have := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK' (m := 1) hω0
  rwa [hKω, one_zsmul] at this

private theorem compHom_compHom' {X Y Z T : Scheme.{0}} (φ : X.RationalMap Y) (f : Y ⟶ Z)
    (g : Z ⟶ T) : (φ.compHom f).compHom g = φ.compHom (f ≫ g) := by
  obtain ⟨φ, rfl⟩ := φ.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap]
  congr 1

private theorem toRationalMap_compHom' {X Z T : Scheme.{0}} (f : X ⟶ Z) (g : Z ⟶ T) :
    f.toRationalMap.compHom g = (f ≫ g).toRationalMap := by
  rw [Scheme.Hom.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.Hom.toPartialMap_compHom]

private theorem isSeparated_terminal' {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsSeparated sX] :
    IsSeparated (X ↘ Limits.terminal Scheme) := by
  rw [show (X ↘ Limits.terminal Scheme) = sX ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-- **A step creating no divisor.** Let `ψ : Y ⤏ Y'` lie over `W` (`f = f⁺ ∘ ψ`), with `f`
proper birational onto the normal variety `W`. If `ψ` is defined at the generic point of every
prime divisor of `Y`, and every prime divisor `F` of `Y'` maps onto a prime divisor `Q` of `W`
over whose generic point `f⁺` has the single point `η_F`, then every prime divisor of `Y'` is the
birational transform of a prime divisor of `Y`. -/
private theorem not_isInverseExceptional_of_isOver {Y Y' W : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] {sW : W ⟶ Spec (.of ℂ)} {sY' : Y' ⟶ Spec (.of ℂ)} [IsSeparated sY']
    (hW : IsNormalVariety ℂ sW) {f : Y ⟶ W} (hY : IsNormalVariety ℂ (f ≫ sW)) [IsProper f]
    (hfb : IsBirationalMorphism f) {fp : Y' ⟶ W} {ψ : Y.RationalMap Y'}
    (hover : ψ.compHom fp = f.toRationalMap)
    (hdef : ∀ P : MMP.Mori.PrimeDivisor Y, MMP.Mori.RationalMap.DefinedAt ψ P.genericPoint)
    (hinj : ∀ F : MMP.Mori.PrimeDivisor Y', ∃ Q : MMP.Mori.PrimeDivisor W,
      fp F.genericPoint = Q.genericPoint ∧ ∀ y : Y', fp y = Q.genericPoint → y = F.genericPoint) :
    ∀ F : MMP.Mori.PrimeDivisor Y', ¬ MMP.Flips.RationalMap.IsInverseExceptional ψ F := by
  have := hW.1
  have := isSeparated_terminal' sW
  have := isSeparated_terminal' sY'
  intro F hF
  obtain ⟨Q, hQ, hinjQ⟩ := hinj F
  obtain ⟨P, hPQ, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hW hY hfb Q
  obtain ⟨g', hg'P, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp (hdef P)
  have hrat : (g'.compHom fp).toRationalMap = f.toPartialMap.toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', hover]
  have h1 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq hrat hg'P
    (show P.genericPoint ∈ f.toPartialMap.domain from trivial)
  change (g'.hom ≫ fp) ⟨P.genericPoint, hg'P⟩ = (Y.topIso.hom ≫ f) ⟨P.genericPoint, trivial⟩
    at h1
  have h2 : fp (g'.hom ⟨P.genericPoint, hg'P⟩) = Q.genericPoint := by
    rw [← hPQ]
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans (h1.trans rfl)
  exact hF P (MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hg'P
    (hinjQ _ h2).symm)

/-- A rational map which is a morphism in codimension one is defined at the generic point of
every prime divisor. -/
private theorem definedAt_of_isMorphismInCodimOne {X Y : Scheme.{0}} {φ : X.RationalMap Y}
    (hφ : MMP.Flips.RationalMap.IsMorphismInCodimOne φ) (P : MMP.Mori.PrimeDivisor X) :
    MMP.Mori.RationalMap.DefinedAt φ P.genericPoint := by
  by_contra hP
  exact MMP.Flips.genericPoint_notMem_of_two_le_closedsCodimension _ hφ P hP

/-- **The steps of a program.** A divisorial contraction or a flip `ψ : Y ⤏ Y'` over `W`, with
`W ⟶ T`, is a birational map over `T` creating no divisor. -/
private theorem step_isBirational_isOver {Y Y' W T : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral Y'] [IsLocallyNoetherian Y']
    [IsNormal Y'] [CompactSpace Y'] {sY : Y ⟶ Spec (.of ℂ)} {sY' : Y' ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} (hY' : IsNormalVariety ℂ sY') {E : RDivisor Y} {f : Y ⟶ W}
    {fp : Y' ⟶ W} (gW : W ⟶ T) {ψ : Y.RationalMap Y'}
    (hneg : IsNegativeExtremalContraction ℂ sY sW E f)
    (hcase : (IsBirationalMorphism f ∧
        (∃ Ex : MMP.Mori.PrimeDivisor Y, (MMP.Mori.exceptionalSet f : Set Y) = Ex.support) ∧
        IsIso fp ∧ IsModificationOf f fp ψ) ∨ IsFlip ℂ sY sW sY' E f fp ψ) :
    MMP.Mori.RationalMap.IsBirational ψ ∧ MMP.Flips.RationalMap.IsOver (f ≫ gW) (fp ≫ gW) ψ ∧
      ∀ F : MMP.Mori.PrimeDivisor Y', ¬ MMP.Flips.RationalMap.IsInverseExceptional ψ F := by
  have hW := hneg.isNormalVariety_target
  have hYv : IsNormalVariety ℂ (f ≫ sW) := hneg.isContraction.comp_eq ▸ hneg.isNormalVariety_source
  haveI : IsProper f := hneg.isContraction.isProper
  haveI := hW.1
  haveI : CompactSpace W := (quasiCompact_iff_compactSpace sW).mp inferInstance
  haveI := hW.2
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : IsSeparated sY' := hY'.1.toIsSeparated
  have key : ∀ (hfb : IsBirationalMorphism f) (hmod : IsModificationOf f fp ψ),
      (∀ P : MMP.Mori.PrimeDivisor Y, MMP.Mori.RationalMap.DefinedAt ψ P.genericPoint) →
      (∀ F : MMP.Mori.PrimeDivisor Y', ∃ Q : MMP.Mori.PrimeDivisor W,
        fp F.genericPoint = Q.genericPoint ∧
          ∀ y : Y', fp y = Q.genericPoint → y = F.genericPoint) →
      MMP.Mori.RationalMap.IsBirational ψ ∧
        MMP.Flips.RationalMap.IsOver (f ≫ gW) (fp ≫ gW) ψ ∧
        ∀ F : MMP.Mori.PrimeDivisor Y', ¬ MMP.Flips.RationalMap.IsInverseExceptional ψ F := by
    intro hfb hmod hdef hinj
    refine ⟨hmod.1, ?_, not_isInverseExceptional_of_isOver (sY' := sY') hW hYv hfb hmod.2 hdef
      hinj⟩
    change ψ.compHom (fp ≫ gW) = (f ≫ gW).toRationalMap
    rw [← compHom_compHom', show ψ.compHom fp = f.toRationalMap from hmod.2,
      toRationalMap_compHom']
  rcases hcase with ⟨hfb, -, hiso, hmod⟩ | hfl
  · have hψ : ψ = (f ≫ inv fp).toRationalMap := by
      calc ψ = ψ.compHom (fp ≫ inv fp) := by
            rw [IsIso.hom_inv_id]
            obtain ⟨φ₀, hφ₀⟩ := ψ.exists_rep
            rw [← hφ₀, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.compHom_id]
        _ = (f ≫ inv fp).toRationalMap := by
            rw [← compHom_compHom', show ψ.compHom fp = f.toRationalMap from hmod.2,
              toRationalMap_compHom']
    refine key hfb hmod (fun P => ?_) (fun F => ?_)
    · rw [hψ]
      exact MMP.Mori.RationalMap.definedAt_iff.mpr
        ⟨(f ≫ inv fp).toPartialMap, show _ ∈ (⊤ : Y.Opens) from trivial, rfl⟩
    · haveI : IsIso (fp ∣_ ⊤) := inferInstance
      obtain ⟨Q, hQ⟩ := MMP.Flips.exists_primeDivisor_map_genericPoint_eq fp ⊤ F trivial
      refine ⟨Q, hQ, fun y hy => ?_⟩
      exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso fp))).injective
        (hy.trans hQ.symm)
  · refine key hfl.isSmall_source.isBirationalMorphism hfl.isModificationOf
      (fun P => definedAt_of_isMorphismInCodimOne hfl.isMorphismInCodimOne P) (fun F => ?_)
    obtain ⟨W', hiso, hD, -⟩ := MMP.Flips.exists_isIso_morphismRestrict_of_isSmall hfl.isSmall
    obtain ⟨Q, hQ⟩ := MMP.Flips.exists_primeDivisor_map_genericPoint_eq fp W' F (hD F)
    refine ⟨Q, hQ, fun y hy => ?_⟩
    have hyF : fp y = fp F.genericPoint := hy.trans hQ.symm
    have hyW : y ∈ fp ⁻¹ᵁ W' := by
      change fp y ∈ W'; rw [hyF]; exact hD F
    have hFW : F.genericPoint ∈ fp ⁻¹ᵁ W' := hD F
    have hinj : Function.Injective (fp ∣_ W').base :=
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (fp ∣_ W')))).injective
    have := @hinj ⟨y, hyW⟩ ⟨F.genericPoint, hFW⟩ (Subtype.ext
      ((AlgebraicGeometry.morphismRestrict_base_coe fp W' ⟨y, hyW⟩).trans
        (hyF.trans (AlgebraicGeometry.morphismRestrict_base_coe fp W' ⟨F.genericPoint, hFW⟩).symm)))
    exact congrArg Subtype.val this

/-- The birational transform commutes with regarding a divisor as an `ℝ`-divisor. -/
private theorem transformDivisor_toRDivisor {X Y : Scheme.{0}} (φ : X.RationalMap Y)
    (D : Divisor X) : MMP.Mori.RationalMap.transformDivisor φ (Divisor.toRDivisor D) =
      Divisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor φ D) := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h h' => rw [map_add, map_add, h, h', map_add, map_add]
  | single P n =>
    have : Divisor.toRDivisor (Finsupp.single P n) = Finsupp.single P (n : ℝ) := by
      ext E
      rw [Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply]
      by_cases hPE : P = E <;> simp [Finsupp.single_apply, hPE]
    rw [this, MMP.Mori.RationalMap.transformDivisor_single,
      MMP.Mori.RationalMap.transformDivisor_single]
    rcases MMP.Mori.RationalMap.transformPrimeDivisor φ P with _ | Q
    · simp
    · simp only [Option.elim_some]
      ext E
      rw [Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply]
      by_cases hQE : Q = E <;> simp [Finsupp.single_apply, hQE]

/-- The underlying morphism of a partial isomorphism is dominant. -/
private theorem isDominant_partialIso_hom {X Y : Scheme.{0}} (e : X.PartialIso Y) :
    IsDominant e.toPartialMap.hom := by
  have : IsDominant e.target.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]; exact e.dense_target⟩
  change IsDominant (e.iso.hom ≫ e.target.ι)
  infer_instance

attribute [local instance] isDominant_partialIso_hom

/-- If `f` maps its domain into the domain of `g` through `r` and `g ∘ r` is the inclusion of the
domain of `f`, then `g ∘ f` is the identity rational map. -/
private theorem toRationalMap_comp_eq_id {X Y : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap X)
    (r : f.domain.toScheme ⟶ g.domain.toScheme) (hr : r ≫ g.domain.ι = f.hom)
    (hrg : r ≫ g.hom = f.domain.ι) :
    f.toRationalMap.comp g.toRationalMap = Scheme.RationalMap.id X := by
  have hpre : f.hom ⁻¹ᵁ g.domain = ⊤ := by
    ext x
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    rw [← hr]
    exact (r x).2
  have hdom : (f.comp g).domain = f.domain := by
    rw [Scheme.PartialMap.comp_domain, hpre, Scheme.Opens.ι_image_top]
  rw [Scheme.RationalMap.toRationalMap_comp, Scheme.RationalMap.id,
    Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨f.domain, f.dense_domain, hdom.ge, fun x _ => by simp, ?_⟩
  have h1 : f.hom ∣_ g.domain = (f.hom ⁻¹ᵁ g.domain).ι ≫ r := by
    rw [← cancel_mono g.domain.ι, morphismRestrict_ι, Category.assoc, hr]
  simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.comp_hom, h1, Category.assoc,
    hrg, Scheme.Hom.isoImage_inv_ι]
  refine (Scheme.homOfLE_ι X hdom.ge).trans ?_
  simp [Scheme.PartialMap.restrict_hom]
  exact (Scheme.homOfLE_ι X _).symm

private theorem partialIso_toRationalMap_comp_symm {X Y : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] [Nonempty Y]
    (e : X.PartialIso Y) :
    e.toRationalMap.comp e.symm.toRationalMap = Scheme.RationalMap.id X :=
  toRationalMap_comp_eq_id e.toPartialMap e.symm.toPartialMap e.iso.hom rfl
    (Iso.hom_inv_id_assoc _ _)

private theorem morphismRestrict_comp_comp {A X Y Z : Scheme.{0}} (t : A ⟶ X) (p : X ⟶ Y)
    (V : Y.Opens)
    (gh : V.toScheme ⟶ Z) (q : X ⟶ Z) (hq : (p ⁻¹ᵁ V).ι ≫ q = (p ∣_ V) ≫ gh) :
    ((t ≫ p) ∣_ V) ≫ gh = ((t ≫ p) ⁻¹ᵁ V).ι ≫ t ≫ q := by
  rw [morphismRestrict_comp]
  exact (Category.assoc _ _ _).trans (by rw [← hq]; exact morphismRestrict_ι_assoc t (p ⁻¹ᵁ V) q)

/-- The composite of a dominant morphism `p` with a partial map `g` is represented on
`p⁻¹(dom g)` by `g ∘ p`. -/
private theorem hom_toRationalMap_comp {X Y Z : Scheme.{0}} [IrreducibleSpace X] [Nonempty Y]
    (p : X ⟶ Y) [IsDominant p]
    (g : Y.PartialMap Z) (q : X ⟶ Z) (hq : (p ⁻¹ᵁ g.domain).ι ≫ q = (p ∣_ g.domain) ≫ g.hom) :
    p.toRationalMap.comp g.toRationalMap = q.toRationalMap := by
  change p.toPartialMap.toRationalMap.comp g.toRationalMap = q.toPartialMap.toRationalMap
  rw [Scheme.RationalMap.toRationalMap_comp, Scheme.PartialMap.toRationalMap_eq_iff]
  have hW : p ⁻¹ᵁ g.domain ≤ (p.toPartialMap.comp g).domain := by
    intro x hx
    exact ⟨⟨x, trivial⟩, hx, rfl⟩
  have hWd : Dense ((p ⁻¹ᵁ g.domain : X.Opens) : Set X) := by
    obtain ⟨y, hy, x, rfl⟩ :=
      p.denseRange.inter_open_nonempty _ g.domain.2 g.dense_domain.nonempty
    exact (p ⁻¹ᵁ g.domain).2.dense ⟨x, hy⟩
  refine ⟨p ⁻¹ᵁ g.domain, hWd, hW, fun x _ => by simp, ?_⟩
  simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.comp_hom]
  have key2 : (Scheme.Hom.toPartialMap p).hom ∣_ g.domain ≫ g.hom =
      ((Scheme.Hom.toPartialMap p).hom ⁻¹ᵁ g.domain).ι ≫ (Scheme.Hom.toPartialMap p).domain.ι ≫
        q :=
    morphismRestrict_comp_comp X.topIso.hom p g.domain g.hom q hq
  simp only [key2, Scheme.Hom.isoImage_inv_ι_assoc, Scheme.Hom.toPartialMap_hom,
    Scheme.topIso_hom]
  exact (Scheme.homOfLE_ι_assoc X hW q).trans (Scheme.homOfLE_ι_assoc X _ q).symm

/-- **A smooth projective common resolution of a birational map.** For a birational map
`φ : X ⤏ Y` of normal projective complex varieties compatible with the structure morphisms, there
are a smooth variety `W` and projective birational morphisms `p : W ⟶ X`, `q : W ⟶ Y` with
`q = φ ∘ p`: some inverse `h` of `p` has `h.compHom q = φ`. -/
private theorem exists_smooth_common_resolution {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
    (hXn : MMP.Mori.IsNormalVariety ℂ sX) (hYn : MMP.Mori.IsNormalVariety ℂ sY)
    (hXp : IsProjectiveMorphism sX) (hYp : IsProjectiveMorphism sY)
    {φ : X.RationalMap Y} (hφ : MMP.Mori.RationalMap.IsBirational φ)
    (hφs : φ.compHom sY = sX.toRationalMap) :
    ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W),
      MMP.Mori.IsNormalVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sX = sW ∧
        q ≫ sY = sW ∧ IsProjectiveMorphism p ∧ MMP.Mori.IsBirationalMorphism p ∧
        IsProjectiveMorphism q ∧ MMP.Mori.IsBirationalMorphism q ∧
        MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧ h.compHom q = φ := by
  obtain ⟨e, he⟩ := hφ
  have hes : e.IsOver sX sY := by
    have h1 : (e.toPartialMap.compHom sY).toRationalMap = sX.toPartialMap.toRationalMap := by
      rw [Scheme.RationalMap.compHom_toRationalMap]
      exact (congrArg (·.compHom sY) he).trans hφs
    have h2 := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp h1)
    exact (Category.assoc _ _ _).symm.trans h2
  have hbot : ∀ {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)), IsEmpty (⊥ : Z.Opens).toScheme :=
    fun _ => ⟨fun x => x.2⟩
  have hsm : MMP.Mori.IsSmoothScheme ((⊥ : X.Opens).ι ≫ sX) := by
    have := hbot sX
    exact Subsingleton.elim _ _
  have hsnc : ∀ {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (S : TopologicalSpace.Closeds
      (⊥ : Z.Opens).toScheme), MMP.Mori.IsSNCSubset ((⊥ : Z.Opens).ι ≫ sZ) S := by
    intro Z sZ S
    have := hbot sZ
    exact Or.inl (TopologicalSpace.Closeds.ext (by ext x; exact isEmptyElim x))
  have hb0 : ∀ {Z : Scheme.{0}}, MMP.Flips.IsBoundary
      (MMP.Mori.QDivisor.toRDivisor (0 : MMP.Mori.QDivisor Z)) := fun E => by simp
  obtain ⟨W, p, q, hpl, hpp, hql, hqp, hcomm, -, -⟩ :=
    MMP.Flips.exists_isLogResolution_isIso_restrict_of_partialIso sX sY hXn hYn hXp hYp 0 0
      hb0 hb0 e hes ⊥ ⊥ bot_le bot_le (by ext; simp) hsm (hsnc _ _) (hsnc _ _) (hsnc _ _)
  obtain ⟨-, hWv, hWsm, hpP, hpb, -⟩ := hpl
  obtain ⟨-, -, -, hqP, hqb, -⟩ := hql
  haveI : IsIntegral W := hWv.toIsIntegral
  obtain ⟨hWln, hWn⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWsm
  haveI : IsDominant p := hpb.isDominant
  -- `q` agrees with `φ ∘ p`, so the two structure morphisms agree
  have hpq : p ≫ sX = q ≫ sY := by
    haveI : IsDominant (p ⁻¹ᵁ e.source).ι := by
      constructor
      rw [DenseRange, Scheme.Opens.range_ι]
      obtain ⟨y, hy, x, rfl⟩ :=
        p.denseRange.inter_open_nonempty _ e.source.2 e.dense_source.nonempty
      exact (p ⁻¹ᵁ e.source).2.dense ⟨x, hy⟩
    refine ext_of_isDominant_of_isSeparated (Spec (.of ℂ) ↘ ⊤_ Scheme)
      (Limits.terminal.hom_ext _ _) (p ⁻¹ᵁ e.source).ι ?_
    rw [reassoc_of% hcomm, hes, morphismRestrict_ι_assoc]
  have hφq : p.toRationalMap.comp φ = q.toRationalMap := by
    rw [← he]
    exact hom_toRationalMap_comp p e.toPartialMap q hcomm
  obtain ⟨ep, hep⟩ := hpb
  have hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap ep.symm.toRationalMap :=
    ⟨ep, hep, rfl⟩
  refine ⟨W, inferInstance, hWln, hWn, p ≫ sX, p, q, ep.symm.toRationalMap, ⟨hWv, hWn⟩, hWsm,
    rfl, hpq.symm, hpp, ⟨ep, hep⟩, hqp, hqb, hinv, ?_⟩
  haveI : p.toRationalMap.IsDominant := by
    change (Scheme.Hom.toPartialMap p).toRationalMap.IsDominant
    infer_instance
  have hid : ep.symm.toRationalMap.comp p.toRationalMap = Scheme.RationalMap.id X := by
    rw [← hep]
    exact partialIso_toRationalMap_comp_symm ep.symm
  rw [← Scheme.RationalMap.comp_toRationalMap, ← hφq, ← Scheme.RationalMap.comp_assoc]
  have key : ∀ (a : X.RationalMap X) [a.IsDominant], a = Scheme.RationalMap.id X →
      a.comp φ = φ := by
    intro a _ ha
    subst ha
    exact Scheme.RationalMap.id_comp φ
  exact key _ hid

/-- A normal projective common resolution of a birational map of normal projective complex
varieties compatible with the structure morphisms. -/
private theorem exists_common_resolution' {X Y : Scheme.{0}}
    [IsIntegral X] [IsNormal X] [IsIntegral Y] [IsNormal Y] (sX : X ⟶ Spec (.of ℂ))
    (sY : Y ⟶ Spec (.of ℂ))
    (hXp : MMP.Mori.IsProjectiveVariety ℂ sX) (hYp : MMP.Mori.IsProjectiveVariety ℂ sY)
    {φ : X.RationalMap Y} (hφ : MMP.Mori.RationalMap.IsBirational φ)
    (hφs : φ.compHom sY = sX.toRationalMap) :
    ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W),
      IsNormalVariety ℂ sW ∧ p ≫ sX = sW ∧ q ≫ sY = sW ∧
        IsProjectiveMorphism p ∧ IsBirationalMorphism p ∧
        IsProjectiveMorphism q ∧ IsBirationalMorphism q ∧
        MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧ h.compHom q = φ := by
  obtain ⟨W, _, _, _, sW, p, q, h, hW, -, hpX, hqY, hp, hpb, hq, hqb, hinv, hcomp⟩ :=
    exists_smooth_common_resolution sX sY ⟨hXp.toIsVariety, inferInstance⟩
      ⟨hYp.toIsVariety, inferInstance⟩ ((MMP.Mori.isProjectiveVariety_iff ℂ sX).mp hXp).2
      ((MMP.Mori.isProjectiveVariety_iff ℂ sY).mp hYp).2 hφ hφs
  exact ⟨W, inferInstance, inferInstance, inferInstance, sW, p, q, h, hW, hpX, hqY, hp, hpb, hq,
    hqb, hinv, hcomp⟩

/-- **Transfer of the null nef level through one step.** Let `ψ : Y ⤏ Y'` be a birational map over
the projective variety `T` of normal `ℚ`-factorial projective varieties, creating no divisor. If
`K + D` is nef over `Z` (for `T ⟶ Z`) and numerically trivial over `T`, then so is `K' + ψ_* D`
for every canonical divisor `K'` of `Y'`: `ψ_*(K + D)` is numerically trivial over `T` and pulls
back to the same divisor as `K + D` on a common resolution, and `K' - ψ_* K` is principal. -/
private theorem level_step {Y Y' T Z : Scheme.{0}}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Y'] [CompactSpace Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    {sY : Y ⟶ Spec (.of ℂ)} {sY' : Y' ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)}
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hYq : IsQFactorial sY)
    (hY' : MMP.Mori.IsProjectiveVariety ℂ sY') (hY'q : IsQFactorial sY')
    (hT : MMP.Mori.IsProjectiveVariety ℂ sT)
    (πY : Y ⟶ T) (πY' : Y' ⟶ T) (hπY : πY ≫ sT = sY) (hπY' : πY' ≫ sT = sY') (g : T ⟶ Z)
    {ψ : Y.RationalMap Y'} (hψ : MMP.Mori.RationalMap.IsBirational ψ)
    (hψT : MMP.Flips.RationalMap.IsOver πY πY' ψ)
    (hψE : ∀ F : MMP.Mori.PrimeDivisor Y', ¬ MMP.Flips.RationalMap.IsInverseExceptional ψ F)
    {K : Divisor Y} (hK : ∃ m : ℕ, K.IsCanonicalDivisor sY m) {K' : Divisor Y'}
    (hK' : ∃ m : ℕ, K'.IsCanonicalDivisor sY' m) {D : RDivisor Y}
    (hnef : IsRelativelyNef ℂ sY (πY ≫ g) (logCanonicalDivisor K D))
    (htriv : IsNumericallyTrivialOver ℂ sY πY (logCanonicalDivisor K D)) :
    IsRelativelyNef ℂ sY' (πY' ≫ g)
        (logCanonicalDivisor K' (MMP.Mori.RationalMap.transformDivisor ψ D)) ∧
      IsNumericallyTrivialOver ℂ sY' πY'
        (logCanonicalDivisor K' (MMP.Mori.RationalMap.transformDivisor ψ D)) := by
  classical
  haveI := hY.toIsVariety
  haveI := hY'.toIsVariety
  haveI := hT.toIsVariety
  have hψs : ψ.compHom sY' = sY.toRationalMap := by
    have h1 : ψ.compHom πY' = πY.toRationalMap := hψT
    rw [← hπY', ← compHom_compHom', h1, toRationalMap_compHom', hπY]
  -- the transform of `K + D` is numerically trivial over `T`, with equal pull-backs
  obtain ⟨hN', heq⟩ := MMP.Fourfold.isNumericallyTrivialOver_transformDivisor_and_pullback_eq sY sY'
    sT hYq hY hY'q hY' hT πY πY' hπY hπY' hψ hψT hψE htriv
  obtain ⟨W, _, _, _, sW, p, q, hres, hWv, hpW, hqW, hpp, hpb, hqp, hqb, hinv, hcomp⟩ :=
    exists_common_resolution' sY sY' hY hY' hψ hψs
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqp
  haveI := hWv.1
  haveI : CompactSpace W := (quasiCompact_iff_compactSpace sW).mp inferInstance
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  -- `ψ_* K` is canonical, so `K' - ψ_* K` is principal
  obtain ⟨n, hKn⟩ := hK
  obtain ⟨n', hK'n⟩ := hK'
  have hnn' : n' = n := by
    have h1 := hKn.topologicalKrullDim_eq
    have h2 := hK'n.topologicalKrullDim_eq
    have h3 : topologicalKrullDim Y = topologicalKrullDim Y' := by
      haveI : MMP.Mori.IsVariety ℂ (p ≫ sY) := hpW ▸ hWv.1
      haveI : MMP.Mori.IsVariety ℂ (q ≫ sY') := hqW ▸ hWv.1
      rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (p ≫ sY) hpb,
        MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY' (q ≫ sY') hqb]
    rw [h1, h2] at h3
    exact_mod_cast h3.symm
  subst hnn'
  have hWp : IsNormalVariety ℂ (p ≫ sY) := hpW ▸ hWv
  have hWq : IsNormalVariety ℂ (q ≫ sY') := hqW ▸ hWv
  have hψK := isCanonicalDivisor_transformDivisor_of_resolution hYq.1 hY'q.1 hψE p q hres hWp hWq
    hpb hqb hinv hcomp (hpW.trans hqW.symm) hKn hK'n
  obtain ⟨u, hu⟩ := linearlyEquivalent_of_isCanonicalDivisor' hY'q.1 hK'n hψK
  have hG : logCanonicalDivisor K' (MMP.Mori.RationalMap.transformDivisor ψ D) =
      MMP.Mori.RationalMap.transformDivisor ψ (logCanonicalDivisor K D) +
        (1 : ℝ) • Divisor.toRDivisor (MMP.Mori.principalDivisor u) := by
    rw [← hu, one_smul, map_sub]
    unfold logCanonicalDivisor
    rw [map_add, transformDivisor_toRDivisor]
    abel
  have hP := isNumericallyTrivialOver_principalDivisor (k := ℂ) (sX := sY') πY' u
  rw [hG]
  refine ⟨?_, ?_⟩
  · -- nefness over `Z` through the common resolution
    have hNc := hN'.1
    obtain ⟨NW, hNW, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p htriv.1
    obtain ⟨NW', hNW', -⟩ := MMP.Flips.existsUnique_isRCartierPullback q hNc
    have hEq := heq W sW p q hres hWv hpW hqW hpp hpb hqp hqb hinv hcomp NW NW' hNW hNW'
    have hnefW : IsRelativelyNef ℂ (p ≫ sY) (p ≫ πY ≫ g) NW :=
      IsRelativelyNef.isRCartierPullback (πY ≫ g) p hnef hNW
    have hpq : p ≫ πY = q ≫ πY' := by
      haveI := hT.toIsVariety
      haveI : IsSeparated sT := inferInstance
      haveI := isSeparated_terminal' sT
      exact MMP.Fourfold.comp_eq_comp_of_isOver πY πY' hψT p q hres hinv hcomp
    have hnefW' : IsRelativelyNef ℂ (q ≫ sY') (q ≫ πY' ≫ g) NW' := by
      rw [← hEq]
      have e1 : (p ≫ sY) = (q ≫ sY') := hpW.trans hqW.symm
      have e2 : p ≫ πY ≫ g = q ≫ πY' ≫ g := by rw [← Category.assoc, hpq, Category.assoc]
      have key : ∀ (s : W ⟶ Spec (.of ℂ)) [QuasiCompact s] (π : W ⟶ Z), s = p ≫ sY →
          π = p ≫ πY ≫ g → IsRelativelyNef ℂ s π NW := by
        rintro s _ π rfl rfl; exact hnefW
      exact key _ _ e1.symm e2.symm
    haveI : Surjective q := surjective_of_isProper_of_isDominant q
    have hnefY' := IsRelativelyNef.of_isRCartierPullback (πY' ≫ g) q hNc hNW' hnefW'
    exact IsRelativelyNef.add_isNumericallyTrivialOver hnefY'
      (isNumericallyTrivialOver_principalDivisor _ u) 1
  · rw [← one_smul ℝ (MMP.Mori.RationalMap.transformDivisor ψ (logCanonicalDivisor K D))]
    exact IsNumericallyTrivialOver.smul_add hN' hP 1 1

/-- The pull-back of a `ℚ`-Cartier `ℚ`-divisor is its pull-back as an `ℝ`-divisor. -/
private theorem isRCartierPullback_of_isPullback {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {D : QDivisor X}
    (hD : D.IsQCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {D' : QDivisor Y} (h : D.IsPullback f hB D') :
    IsRCartierPullback f (QDivisor.toRDivisor D) (QDivisor.toRDivisor D') := by
  obtain ⟨m, hm, L, hL, hLc⟩ := hD.exists_pos
  obtain ⟨L', hL', hp⟩ := h m hm L hL hLc
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨1, fun _ => 1 / (m : ℝ), fun _ => L, fun _ => L', fun _ => hLc, ?_, fun _ => ⟨_, hp⟩,
    ?_⟩
  · rw [Fin.sum_univ_one]
    ext E
    have h1 := congrArg (fun G : QDivisor X => G.coeff E) hL
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast] at h1
    simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      smul_eq_mul]
    rw [show ((L.coeff E : ℤ) : ℝ) = ((L.coeff E : ℚ) : ℝ) by push_cast; rfl, h1]
    push_cast
    field_simp
  · rw [Fin.sum_univ_one]
    ext E
    have h1 := congrArg (fun G : QDivisor Y => G.coeff E) hL'
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast] at h1
    simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      smul_eq_mul]
    rw [show ((L'.coeff E : ℤ) : ℝ) = ((L'.coeff E : ℚ) : ℝ) by push_cast; rfl, h1]
    push_cast
    field_simp

/-- **Restriction of `K + B + E` to a floor component, up to principal divisors.** Let `(X, B)`
be a `ℚ`-factorial normal fourfold and `(S, Δ)` arise by real adjunction to the prime divisor `S`
(a positive convex combination of rational adjunction steps). For every canonical divisor `K_S`
of `S` and every `ℝ`-divisor `E` with restriction `E_S = E|_S`, there are rational functions `u`,
`v` with `(K + B + E + div u)|_S = K_S + Δ + E_S + div v`: for a rational top form `σ` with a
simple pole along `S` and residue `ρ`, `(div σ + B + E)|_S = div ρ + Δ + E_S`, with
`div σ = K + div u` and `div ρ = K_S + div v`. -/
private theorem exists_isRCartierPullback_adjunction {X TS : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral TS] [IsLocallyNoetherian TS]
    [IsNormal TS] [CompactSpace TS] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (hXv : IsNormalVariety ℂ sX) (hXq : IsQFactorial sX) (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) {B : RDivisor X}
    (S : MMP.Mori.PrimeDivisor X) (ι : TS ⟶ X) [IsClosedImmersion ι]
    (hι : Set.range ι.base = (S.support : Set X)) (hTS : IsNormalVariety ℂ (ι ≫ sX))
    {Δ : RDivisor TS}
    (hΔ : ∃ (m : ℕ) (t : Fin m → ℝ) (Bk : Fin m → QDivisor X) (Δk : Fin m → QDivisor TS),
      (∀ k, 0 < t k) ∧ ∑ k, t k = 1 ∧ B = ∑ k, t k • QDivisor.toRDivisor (Bk k) ∧
      Δ = ∑ k, t k • QDivisor.toRDivisor (Δk k) ∧ ∀ k, IsAdjunctionStep sX (Bk k) ι (Δk k))
    {KS : Divisor TS} (hKS : ∃ m : ℕ, KS.IsCanonicalDivisor (ι ≫ sX) m) {E : RDivisor X}
    {ES : RDivisor TS} (hE : IsRCartierPullback ι E ES) :
    ∃ (u : (RationalFunctions X)ˣ) (v : (RationalFunctions TS)ˣ),
      IsRCartierPullback ι
        (logCanonicalDivisor K (B + E) + Divisor.toRDivisor (MMP.Mori.principalDivisor u))
        (logCanonicalDivisor KS (Δ + ES) + Divisor.toRDivisor (MMP.Mori.principalDivisor v)) := by
  classical
  haveI : LocallyOfFiniteType (ι ≫ sX) := hTS.1.toLocallyOfFiniteType
  haveI := hXv.1
  haveI := hTS.1
  obtain ⟨m, t, Bk, Δk, -, hsum, hB, hΔ', hadj⟩ := hΔ
  have hdim' : topologicalKrullDim X = ((3 + 1 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  have hdimTS : topologicalKrullDim TS = (3 : ℕ) :=
    topologicalKrullDim_eq_of_range_eq_support (sX := sX) hdim' S ι hι
  obtain ⟨Q⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdimTS
    (by norm_num)
  obtain ⟨σ, hσ0, hσS, ρ, hρ, hρ0⟩ :=
    MMP.Fourfold.exists_ordForm_eq_neg_one_isPoincareResidue sX hXv (n := 3)
      (by rw [hdim]; rfl) ι hTS S hι Q
  have hpk : ∀ k, IsRCartierPullback ι
      (QDivisor.toRDivisor (Divisor.toQDivisor (divisorOfForm σ) + Bk k))
      (QDivisor.toRDivisor (Divisor.toQDivisor (divisorOfForm ρ) + Δk k)) := by
    intro k
    have hQC := MMP.Fourfold.isQCartier_of_isQFactorial sX hXq
      (Divisor.toQDivisor (divisorOfForm σ) + Bk k)
    obtain ⟨hgen, hp⟩ :=
      MMP.Fourfold.IsAdjunctionStep.isPullback_divisorOfForm_add_of_isPoincareResidue
        (hadj k) (n := 3) (by rw [hdim]; rfl) S hι σ hσ0 hσS ρ hρ hQC
    exact isRCartierPullback_of_isPullback hQC hp
  have hsumP := MMP.Fourfold.isRCartierPullback_sum Finset.univ _ _
    (fun k _ => MMP.Fourfold.isRCartierPullback_smul (t k) (hpk k))
  have e1 : ∑ k, t k • QDivisor.toRDivisor (Divisor.toQDivisor (divisorOfForm σ) + Bk k) =
      Divisor.toRDivisor (divisorOfForm σ) + B := by
    simp only [map_add, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hsum, one_smul,
      QDivisor.toRDivisor_toQDivisor, hB]
  have e2 : ∑ k, t k • QDivisor.toRDivisor (Divisor.toQDivisor (divisorOfForm ρ) + Δk k) =
      Divisor.toRDivisor (divisorOfForm ρ) + Δ := by
    simp only [map_add, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hsum, one_smul,
      QDivisor.toRDivisor_toQDivisor, hΔ']
  rw [e1, e2] at hsumP
  have hP := MMP.Fourfold.isRCartierPullback_add hsumP hE
  obtain ⟨n₀, hK⟩ := hK
  have hn₀ : n₀ = 3 + 1 := by
    have := hK.topologicalKrullDim_eq
    rw [hdim] at this
    exact_mod_cast this.symm
  subst hn₀
  obtain ⟨u, hu⟩ := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXv hK (m := 1) hσ0
  obtain ⟨n₁, hKS⟩ := hKS
  have hn₁ : n₁ = 3 := by
    have := hKS.topologicalKrullDim_eq
    rw [hdimTS] at this
    exact_mod_cast this.symm
  subst hn₁
  obtain ⟨v, hv⟩ := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hTS hKS (m := 1) hρ0
  refine ⟨u, v, ?_⟩
  have h1 : logCanonicalDivisor K (B + E) + Divisor.toRDivisor (MMP.Mori.principalDivisor u) =
      Divisor.toRDivisor (divisorOfForm σ) + B + E := by
    rw [← hu, one_zsmul, map_sub]
    unfold logCanonicalDivisor
    abel
  have h2 : logCanonicalDivisor KS (Δ + ES) + Divisor.toRDivisor (MMP.Mori.principalDivisor v) =
      Divisor.toRDivisor (divisorOfForm ρ) + Δ + ES := by
    rw [← hv, one_zsmul, map_sub]
    unfold logCanonicalDivisor
    abel
  rw [h1, h2]
  exact hP

/-- **Restriction of the null nef level to a floor component.** Let `(X, B)` be a `ℚ`-factorial
normal fourfold with `K + B + λC` nef over `Z` and numerically trivial over `T`, and let `(S, Δ)`
arise by real adjunction to the prime divisor `S` (a positive convex combination of rational
adjunction steps). For every canonical divisor `K_S` and every restriction `C_S = C|_S`, the
divisor `K_S + Δ + λC_S` is nef over `Z` and numerically trivial over `T`: with a rational top
form `σ` having a simple pole along `S` and residue `ρ`, `(div σ + B + λC)|_S = div ρ + Δ + λC_S`
by the residue description of the different, and `div σ ∼ K`, `div ρ ∼ K_S`. -/
private theorem level_restrict {X TS T Z : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral TS] [IsLocallyNoetherian TS] [IsNormal TS]
    [CompactSpace TS] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (hXv : IsNormalVariety ℂ sX) (hXq : IsQFactorial sX) (hdim : topologicalKrullDim X = 4)
    {f : X ⟶ T} {g : T ⟶ Z} {K : Divisor X} (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    {B C : RDivisor X} {lam : ℝ}
    (hnef : IsRelativelyNef ℂ sX (f ≫ g) (logCanonicalDivisor K (B + lam • C)))
    (hnull : IsNumericallyTrivialOver ℂ sX f (logCanonicalDivisor K (B + lam • C)))
    (S : MMP.Mori.PrimeDivisor X) (ι : TS ⟶ X) [IsClosedImmersion ι]
    (hι : Set.range ι.base = (S.support : Set X)) (hTS : IsNormalVariety ℂ (ι ≫ sX))
    {Δ : RDivisor TS}
    (hΔ : ∃ (m : ℕ) (t : Fin m → ℝ) (Bk : Fin m → QDivisor X) (Δk : Fin m → QDivisor TS),
      (∀ k, 0 < t k) ∧ ∑ k, t k = 1 ∧ B = ∑ k, t k • QDivisor.toRDivisor (Bk k) ∧
      Δ = ∑ k, t k • QDivisor.toRDivisor (Δk k) ∧ ∀ k, IsAdjunctionStep sX (Bk k) ι (Δk k))
    {KS : Divisor TS} (hKS : ∃ m : ℕ, KS.IsCanonicalDivisor (ι ≫ sX) m) {CS : RDivisor TS}
    (hCS : IsRCartierPullback ι C CS) :
    IsRelativelyNef ℂ (ι ≫ sX) (ι ≫ f ≫ g) (logCanonicalDivisor KS (Δ + lam • CS)) ∧
      IsNumericallyTrivialOver ℂ (ι ≫ sX) (ι ≫ f) (logCanonicalDivisor KS (Δ + lam • CS)) := by
  haveI := hXv.1
  haveI := hTS.1
  obtain ⟨u, v, hP⟩ := exists_isRCartierPullback_adjunction hXv hXq hdim hK S ι hι hTS hΔ hKS
    (MMP.Fourfold.isRCartierPullback_smul lam hCS)
  exact ⟨IsRelativelyNef.of_isRCartierPullback_add (f ≫ g) ι hP
      (isNumericallyTrivialOver_principalDivisor _ u)
      (isNumericallyTrivialOver_principalDivisor _ v) hnef,
    IsNumericallyTrivialOver.of_isRCartierPullback_add f ι hP
      (isNumericallyTrivialOver_principalDivisor _ u)
      (isNumericallyTrivialOver_principalDivisor _ v) hnull⟩

/-! ### Nef weak models from anti-nef sources -/

/-- **Negativity for a difference of pull-backs.** On a proper birational `q : W ⟶ Z` of normal
varieties, if `G_Z - G_Y` is `q`-nef and `G_Y`, `G_Z` have the same coefficient at every prime
divisor not exceptional over `Z`, then `G_Y - G_Z` is effective and `q`-exceptional. -/
private theorem isEffective_sub_of_isRelativelyNef {W Z : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [IsLocallyNoetherian Z] [IsNormal Z]
    {sZ : Z ⟶ Spec (.of ℂ)} [QuasiCompact sZ] (hZ : IsNormalVariety ℂ sZ) (q : W ⟶ Z)
    (hW : IsNormalVariety ℂ (q ≫ sZ)) [IsProper q] (hqb : IsBirationalMorphism q)
    {GY GZ : RDivisor W} (hGY : IsCartierCombination GY) (hGZ : IsCartierCombination GZ)
    (hnef : IsRelativelyNef ℂ (q ≫ sZ) q (GZ - GY))
    (hcoef : ∀ P, ¬ IsExceptionalPrimeDivisor sZ q P → GY.coeff P = GZ.coeff P) :
    (∀ P, 0 ≤ (GY - GZ).coeff P) ∧
      ∀ P, (GY - GZ).coeff P ≠ 0 → IsExceptionalPrimeDivisor sZ q P := by
  haveI : QuasiCompact (q ≫ sZ) := inferInstance
  have h0 : IsCartierCombination (0 : RDivisor W) :=
    isCartierCombination_of_presentation (r := Fin.elim0) (L := Fin.elim0) (fun j => j.elim0)
      (by simp)
  have hBc : IsCartierCombination (GY - GZ) := by
    have := isCartierCombination_smul_add hGY hGZ 1 (-1)
    rwa [one_smul, neg_one_smul, ← sub_eq_add_neg] at this
  refine ⟨fun P => ?_, fun P hP => ?_⟩
  · have hBG : ∀ P : MMP.Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sZ q P →
        0 ≤ (GY - GZ).coeff P := by
      intro P hP
      rw [DivisorWithCoeffs.coeff_sub, hcoef P hP, sub_self]
    have hnum : IsNumericallyEquivalentOver ℂ (q ≫ sZ) q 0 ((GZ - GY) + (GY - GZ)) := by
      rw [sub_add_sub_cancel, sub_self]
      exact ⟨h0, h0, fun C _ _ _ _ _ _ _ _ _ h₁ h₂ => isRIntersectionNumber_eq h₁ h₂⟩
    have hZ0 : IsCartierCombination (0 : RDivisor Z) :=
      isCartierCombination_of_presentation (r := Fin.elim0) (L := Fin.elim0) (fun j => j.elim0)
        (by simp)
    exact MMP.Flips.isEffective_of_isNumericallyEquivalentOver_pullback ℂ sZ (q ≫ sZ) hZ hW q rfl
      hqb hZ0 (MMP.Fourfold.isRCartierPullback_zero q)
      (isRelativelyNef_iff.mp hnef).1 hnef hBc hBG hnum P
  · by_contra h
    exact hP (by rw [DivisorWithCoeffs.coeff_sub, hcoef P h, sub_self])

/-- **A nef weak model of an anti-nef pair.** Let `(V, D)` be a pair on a normal projective
variety over `S` with `K_V + D` an `ℝ`-Cartier combination and `-(K_V + D)` nef over `S`, and let
`φ : V ⤏ Z` be a birational map over `S` to a normal projective variety, creating no divisor, with
`K_Z + D_Z = φ_*(K_V + D)` nef over `S`. Then `φ` is a nef weak model of `(V, D)`: on a smooth
common resolution, `p^*(K_V + D) - q^*(K_Z + D_Z)` is `q`-nef up to sign and vanishes at every
prime not exceptional over `Z`, so it is effective and `q`-exceptional by negativity. -/
private theorem isNefWeakModel_of_isRelativelyNef_neg {V Z S : Scheme.{0}}
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sV : V ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [QuasiCompact sZ] {sS : S ⟶ Spec (.of ℂ)}
    [IsSeparated sS] {πV : V ⟶ S} {πZ : Z ⟶ S}
    (hVn : IsNormalVariety ℂ sV) (hVp : MMP.Mori.IsProjectiveVariety ℂ sV) (hπV : πV ≫ sS = sV)
    (hZn : IsNormalVariety ℂ sZ) (hZp : MMP.Mori.IsProjectiveVariety ℂ sZ) (hπZ : πZ ≫ sS = sZ)
    {KV : Divisor V} (hK : ∃ m : ℕ, KV.IsCanonicalDivisor sV m) {D : RDivisor V}
    (hDc : IsCartierCombination (logCanonicalDivisor KV D))
    (hneg : IsRelativelyNef ℂ sV πV (-logCanonicalDivisor KV D))
    {φ : V.RationalMap Z} (hφ : MMP.Mori.RationalMap.IsBirational φ)
    (hφS : MMP.Flips.RationalMap.IsOver πV πZ φ)
    (hφE : ∀ F : MMP.Mori.PrimeDivisor Z, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    (hZnef : IsRelativelyNef ℂ sZ πZ (logCanonicalDivisor
      (MMP.Mori.RationalMap.transformDivisor φ KV) (MMP.Mori.RationalMap.transformDivisor φ D))) :
    IsNefWeakModel sV sZ sS πV πZ KV D φ := by
  classical
  refine ⟨hVn, hVp, hπV, hK, hDc, hZn, hZp, hπZ, hφ, hφS, hφE, hZnef, ?_⟩
  haveI := hVn.1
  haveI := hZn.1
  haveI : IsSeparated sZ := inferInstance
  haveI := isSeparated_terminal' sS
  have hφs : φ.compHom sZ = sV.toRationalMap := by
    have h1 : φ.compHom πZ = πV.toRationalMap := hφS
    rw [← hπZ, ← compHom_compHom', h1, toRationalMap_compHom', hπV]
  obtain ⟨W, _, _, _, sW, p, q, h, hWn, hWsm, hpV, hqZ, hpp, hpb, hqp, hqb, hinv, hcomp⟩ :=
    exists_smooth_common_resolution sV sZ hVn hZn ((MMP.Mori.isProjectiveVariety_iff ℂ sV).mp hVp).2
      ((MMP.Mori.isProjectiveVariety_iff ℂ sZ).mp hZp).2 hφ hφs
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqp
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hWp : IsNormalVariety ℂ (p ≫ sV) := hpV ▸ hWn
  have hWq : IsNormalVariety ℂ (q ≫ sZ) := hqZ ▸ hWn
  haveI : QuasiCompact (q ≫ sZ) := inferInstance
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (q ≫ sZ)
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have hZc := (isRelativelyNef_iff.mp hZnef).1
  obtain ⟨GY, hGY, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p hDc
  obtain ⟨GZ, hGZ, -⟩ := MMP.Flips.existsUnique_isRCartierPullback q hZc
  have hpq : p ≫ πV = q ≫ πZ := MMP.Fourfold.comp_eq_comp_of_isOver πV πZ hφS p q h hinv hcomp
  -- `G_Z - G_Y` is `q`-nef
  have h1 : IsRelativelyNef ℂ (q ≫ sZ) q GZ :=
    MMP.Fourfold.isRelativelyNef_of_isRCartierPullback πZ πZ q q rfl hZnef hGZ
  have hGYn : IsRCartierPullback p (-logCanonicalDivisor KV D) (-GY) := by
    have := MMP.Fourfold.isRCartierPullback_smul (-1) hGY
    rwa [neg_one_smul, neg_one_smul] at this
  have h2 : IsRelativelyNef ℂ (p ≫ sV) q (-GY) :=
    MMP.Fourfold.isRelativelyNef_of_isRCartierPullback πZ πV q p hpq.symm hneg hGYn
  have h2' : IsRelativelyNef ℂ (q ≫ sZ) q (-GY) := by
    have key : ∀ (s : W ⟶ Spec (.of ℂ)) [QuasiCompact s], s = p ≫ sV →
        IsRelativelyNef ℂ s q (-GY) := by
      rintro s _ rfl; exact h2
    exact key _ (hqZ.trans hpV.symm)
  have hnef : IsRelativelyNef ℂ (q ≫ sZ) q (GZ - GY) := by
    have := IsRelativelyNef.smul_add h1 h2' zero_le_one zero_le_one
    rwa [one_smul, one_smul, ← sub_eq_add_neg] at this
  -- the coefficients agree at every prime not exceptional over `Z`
  have hcoef : ∀ P, ¬ IsExceptionalPrimeDivisor sZ q P → GY.coeff P = GZ.coeff P := by
    intro P hP
    obtain ⟨Q, hPQ, hiso, -⟩ :=
      MMP.Fourfold.exists_transformDivisor_apply_eq_of_not_isExceptionalPrimeDivisor hZn q hWq hqb
        P hP
    haveI := hiso
    rw [MMP.Fourfold.coeff_eq_of_isRCartierPullback P Q hPQ hGZ]
    obtain ⟨PV, hPV⟩ : ∃ PV, MMP.Mori.RationalMap.transformPrimeDivisor φ PV = some Q := by
      by_contra hc
      exact hφE Q (fun P' hP' => hc ⟨P', hP'⟩)
    obtain ⟨E, hEp, hEpi, hEq, -⟩ :=
      MMP.Fourfold.exists_primeDivisor_apply_eq_of_transformPrimeDivisor_eq_some hVn hZn p q h
        hWp hpb hqb hinv hcomp hPV
    obtain rfl : E = P := eq_of_map_genericPoint_eq hZn hWq hqb Q E P hEq hPQ
    haveI := hEpi
    rw [MMP.Fourfold.coeff_eq_of_isRCartierPullback E PV hEp hGY]
    have hinj : ∀ P', MMP.Mori.RationalMap.transformPrimeDivisor φ P' = some Q → P' = PV := by
      intro P' hP'
      obtain ⟨E', hE'p, -, hE'q, -⟩ :=
        MMP.Fourfold.exists_primeDivisor_apply_eq_of_transformPrimeDivisor_eq_some hVn hZn p q h
          hWp hpb hqb hinv hcomp hP'
      obtain rfl : E' = E := eq_of_map_genericPoint_eq hZn hWq hqb Q E' E hE'q hEq
      exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hE'p.symm.trans hEp)
    have htr : logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ KV)
        (MMP.Mori.RationalMap.transformDivisor φ D) =
        MMP.Mori.RationalMap.transformDivisor φ (logCanonicalDivisor KV D) := by
      unfold logCanonicalDivisor
      rw [map_add, transformDivisor_toRDivisor]
    rw [htr]
    exact (MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hPV hinj _).symm
  obtain ⟨heff, hexc⟩ := isEffective_sub_of_isRelativelyNef hZn q hWq hqb
    (isCartierCombination_of_isRCartierPullback hGY)
    (isCartierCombination_of_isRCartierPullback hGZ)
    hnef hcoef
  exact ⟨W, inferInstance, inferInstance, inferInstance, sW, p, q, h, hWn.1, hWsm, hpV, hqZ, hpp,
    hqp, hpb, hqb, hinv, hcomp, GY, GZ, hGY, hGZ, heff, hexc⟩

/-- **Changing the canonical divisor of a nef weak model.** If `φ` is a nef weak model of
`(Y, C)` with canonical divisor `K_Y`, it is one with every canonical divisor
`K_Y' = K_Y + div u`: on a resolution `p, q` of `φ`, `div u` pulls back to `div (p^* u)` and
`φ_* div u = div u'` for the function `u'` with `q^* u' = p^* u`, so both pull-backs move by the
same principal divisor and the comparison does not change. -/
private theorem IsNefWeakModel.of_eq_add_principalDivisor {Y Z S : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [QuasiCompact sZ] {sS : S ⟶ Spec (.of ℂ)}
    {πY : Y ⟶ S} {πZ : Z ⟶ S} {KY : Divisor Y} {C : RDivisor Y} {φ : Y.RationalMap Z}
    (hφ : IsNefWeakModel sY sZ sS πY πZ KY C φ) {KY' : Divisor Y}
    (hK' : ∃ m : ℕ, KY'.IsCanonicalDivisor sY m) (u : (RationalFunctions Y)ˣ)
    (hu : KY' = KY + MMP.Mori.principalDivisor u) :
    IsNefWeakModel sY sZ sS πY πZ KY' C φ := by
  classical
  haveI := hφ.isNormalVariety_source.1
  haveI := hφ.isNormalVariety_target.1
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  obtain ⟨W, _, _, _, sW, p, q, h, hWv, hWsm, hpY, hqZ, hpp, hqp, hpb, hqb, hinv, hcomp, GY, GZ,
    hGY, hGZ, heff, hexc⟩ := hφ.exists_resolution
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqp
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  haveI : QuasiCompact sW := hpY ▸ inferInstance
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have hWp : IsNormalVariety ℂ (p ≫ sY) := hpY ▸ ⟨hWv, inferInstance⟩
  have hWq : IsNormalVariety ℂ (q ≫ sZ) := hqZ ▸ ⟨hWv, inferInstance⟩
  have hgu := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant p
    (MMP.Mori.principalDivisor u)
  set uW := pullbackRationalFunction p u hgu
  obtain ⟨u', hu', hqu'⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hqb uW
  -- `φ_* div u = div u'`
  have hpu : MMP.Mori.RationalMap.transformDivisor p.toRationalMap (MMP.Mori.principalDivisor uW) =
      MMP.Mori.principalDivisor u :=
    MMP.Positivity.transformDivisor_principalDivisor_pullback hφ.isNormalVariety_source hWp hpb u
      hgu
  have hqu : MMP.Mori.RationalMap.transformDivisor q.toRationalMap (MMP.Mori.principalDivisor uW) =
      MMP.Mori.principalDivisor u' := by
    rw [← hqu']
    exact MMP.Positivity.transformDivisor_principalDivisor_pullback hφ.isNormalVariety_target hWq
      hqb u' hu'
  have hφu : MMP.Mori.RationalMap.transformDivisor φ (MMP.Mori.principalDivisor u) =
      MMP.Mori.principalDivisor u' := by
    rw [← hpu, ← hqu]
    exact (transformDivisor_eq_transformDivisor_transformDivisor hφ.isNormalVariety_source
      hφ.isNormalVariety_target hφ.not_isInverseExceptional p q h hWp hWq hpb hqb hinv hcomp _).symm
  have hsrc : logCanonicalDivisor KY' C = logCanonicalDivisor KY C +
      (1 : ℝ) • Divisor.toRDivisor (MMP.Mori.principalDivisor u) := by
    rw [hu, one_smul]
    unfold logCanonicalDivisor
    rw [map_add]
    abel
  have htgt : logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ KY')
      (MMP.Mori.RationalMap.transformDivisor φ C) =
      logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ KY)
        (MMP.Mori.RationalMap.transformDivisor φ C) +
      (1 : ℝ) • Divisor.toRDivisor (MMP.Mori.principalDivisor u') := by
    rw [hu, map_add, hφu, one_smul]
    unfold logCanonicalDivisor
    rw [map_add]
    abel
  have hpbu : IsRCartierPullback p (Divisor.toRDivisor (MMP.Mori.principalDivisor u))
      (Divisor.toRDivisor (MMP.Mori.principalDivisor uW)) :=
    MMP.Fourfold.isRCartierPullback_toRDivisor (Divisor.isCartier_principalDivisor u) hgu
      (Divisor.isPullback_principalDivisor u hgu)
  have hqbu : IsRCartierPullback q (Divisor.toRDivisor (MMP.Mori.principalDivisor u'))
      (Divisor.toRDivisor (MMP.Mori.principalDivisor uW)) := by
    rw [← hqu']
    exact MMP.Fourfold.isRCartierPullback_toRDivisor (Divisor.isCartier_principalDivisor u') hu'
      (Divisor.isPullback_principalDivisor u' hu')
  have hP : IsNumericallyTrivialOver ℂ sZ πZ
      (Divisor.toRDivisor (MMP.Mori.principalDivisor u')) :=
    isNumericallyTrivialOver_principalDivisor (k := ℂ) (sX := sZ) πZ u'
  refine
    { hφ with
      isCanonicalDivisor := hK'
      isCartierCombination := by
        rw [hsrc, one_smul]
        have := isCartierCombination_smul_add hφ.isCartierCombination
          (isCartierCombination_of_presentation (m := 1) (r := fun _ => 1)
            (D := Divisor.toRDivisor (MMP.Mori.principalDivisor u))
            (L := fun _ => MMP.Mori.principalDivisor u)
            (fun _ => Divisor.isCartier_principalDivisor u) (by simp)) 1 1
        rwa [one_smul, one_smul] at this
      isRelativelyNef := by
        rw [htgt]
        exact IsRelativelyNef.add_isNumericallyTrivialOver hφ.isRelativelyNef hP 1
      exists_resolution := ?_ }
  refine ⟨W, inferInstance, inferInstance, inferInstance, sW, p, q, h, hWv, hWsm, hpY, hqZ, hpp,
    hqp, hpb, hqb, hinv, hcomp, GY + Divisor.toRDivisor (MMP.Mori.principalDivisor uW),
    GZ + Divisor.toRDivisor (MMP.Mori.principalDivisor uW), ?_, ?_, ?_, ?_⟩
  · rw [hsrc, one_smul]
    exact MMP.Fourfold.isRCartierPullback_add hGY hpbu
  · rw [htgt, one_smul]
    exact MMP.Fourfold.isRCartierPullback_add hGZ hqbu
  · intro P
    rw [add_sub_add_right_eq_sub]
    exact heff P
  · intro P hP
    rw [add_sub_add_right_eq_sub] at hP
    exact hexc P hP

/-- A curve is contracted by `f ≫ e` for an isomorphism `e` exactly when it is contracted by
`f`. -/
private theorem isContractedBy_comp_isIso_iff {X W W' : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (C : ProperCurve sX) (f : X ⟶ W) (e : W ⟶ W') [IsIso e] :
    C.IsContractedBy (f ≫ e) ↔ C.IsContractedBy f := by
  refine ⟨fun h x hx => ?_, fun h => isContractedBy_comp h e⟩
  have := h x hx
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
  exact (ConcreteCategory.injective_of_mono_of_preservesPullback e.base) this

/-- **An extremal contraction followed by an isomorphism.** If `f : X ⟶ W` is a negative
extremal contraction and `e : W ⟶ W'` an isomorphism of `k`-schemes onto a normal variety, then
`f ≫ e` is a negative extremal contraction for the same divisor. -/
private theorem IsNegativeExtremalContraction.comp_isIso {X W W' : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} {sW' : W' ⟶ Spec (.of ℂ)} {E : RDivisor X} {f : X ⟶ W}
    (hf : IsNegativeExtremalContraction ℂ sX sW E f) (e : W ⟶ W') [IsIso e]
    (he : e ≫ sW' = sW) (hW' : IsNormalVariety ℂ sW') :
    IsNegativeExtremalContraction ℂ sX sW' E (f ≫ e) := by
  have hc := hf.isContraction
  haveI := hc.isProper
  have hS : MMP.Flips.relativeNumericallyTrivialDivisors sX (f ≫ e) =
      MMP.Flips.relativeNumericallyTrivialDivisors sX f := by
    ext D
    simp only [MMP.Flips.mem_relativeNumericallyTrivialDivisors]
    exact forall_congr' fun C => imp_congr_left (isContractedBy_comp_isIso_iff C f e)
  refine ⟨hf.isNormalVariety_source, hW', hf.isCartierCombination,
    ⟨hW'.1, hc.isVariety_source, by rw [Category.assoc, he, hc.comp_eq], inferInstance,
      fun U => ?_⟩, ?_, ?_⟩
  · rw [Scheme.Hom.comp_app]
    exact @IsIso.comp_isIso _ _ _ _ _ (e.app U) _ inferInstance (hc.isIso_app _)
  · obtain ⟨m, r, L, hm, hr, hL, hE⟩ := hf.isRelativelyAntiAmple
    refine ⟨m, r, L, hm, hr, fun j => ?_, hE⟩
    obtain ⟨hcj, ha⟩ := hL j
    exact ⟨hcj, fun U hU => ha (e ⁻¹ᵁ U) (hU.preimage e)⟩
  · have h1 := hf.relativePicardNumber_eq_one
    unfold MMP.Flips.relativePicardNumber MMP.Flips.RelativeNumericalDivisorClasses at h1 ⊢
    rw [hS]
    exact h1

/-- `φ ∘ 𝟙 = φ` for a rational map. -/
private theorem compHom_id' {X Y : Scheme.{0}} (φ : X.RationalMap Y) : φ.compHom (𝟙 Y) = φ := by
  obtain ⟨φ, rfl⟩ := φ.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.compHom_id]

/-- **A nef weak model survives a step of a program.** Let `φ : Y ⤏ Z` be a nef weak model of
`(Y, C)` over `S`, and let `Y ⟶ W ⟵ Y⁺` be a `(K_Y + C)`-negative step over `S`: a divisorial
contraction `f : Y ⟶ W` with `Y⁺ ≅ W`, or a flip. Then `φ ∘ ψ⁻¹ : Y⁺ ⤏ Z` is a nef weak model of
`(Y⁺, ψ_* C)` with canonical divisor `ψ_* K_Y`, and `(φ ∘ ψ⁻¹)_* ψ_* N = φ_* N` for every
divisor `N` of `Y`. -/
private theorem IsNefWeakModel.exists_of_programStep {Y Y' Z S Wd : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y']
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [QuasiCompact sZ] {sS : S ⟶ Spec (.of ℂ)}
    [IsSeparated sS] {πY : Y ⟶ S} {πZ : Z ⟶ S} {KY : Divisor Y} {C : RDivisor Y}
    {φ : Y.RationalMap Z} (hφ : IsNefWeakModel sY sZ sS πY πZ KY C φ)
    {sY' : Y' ⟶ Spec (.of ℂ)} {πY' : Y' ⟶ S} (hY'p : MMP.Mori.IsProjectiveVariety ℂ sY')
    (hY'q : IsQFactorial sY') (hπY' : πY' ≫ sS = sY') {sWd : Wd ⟶ Spec (.of ℂ)}
    (fW : Y ⟶ Wd) (gW : Wd ⟶ S) (fpW : Y' ⟶ Wd) (ψ : Y.RationalMap Y')
    (hfg : fW ≫ gW = πY) (hfpg : fpW ≫ gW = πY')
    (hneg : IsNegativeExtremalContraction ℂ sY sWd (logCanonicalDivisor KY C) fW)
    (hcase : (IsBirationalMorphism fW ∧
        (∃ E : MMP.Mori.PrimeDivisor Y,
          (MMP.Mori.exceptionalSet fW : Set Y) = E.support) ∧
        IsIso fpW ∧ IsModificationOf fW fpW ψ) ∨
      IsFlip ℂ sY sWd sY' (logCanonicalDivisor KY C) fW fpW ψ) :
    ∃ φ' : Y'.RationalMap Z, IsNefWeakModel sY' sZ sS πY' πZ
      (MMP.Mori.RationalMap.transformDivisor ψ KY) (MMP.Mori.RationalMap.transformDivisor ψ C)
      φ' ∧ ∀ {R : Type} [AddCommMonoid R] (N : DivisorWithCoeffs R Y),
        MMP.Mori.RationalMap.transformDivisor φ' (MMP.Mori.RationalMap.transformDivisor ψ N) =
          MMP.Mori.RationalMap.transformDivisor φ N := by
  classical
  have hψb : MMP.Mori.RationalMap.IsBirational ψ := by
    rcases hcase with ⟨-, -, -, hmod⟩ | hfl
    · exact hmod.1
    · exact hfl.isModificationOf.1
  haveI : ψ.IsDominant := MMP.Fourfold.Crepant.isDominant_of_isBirational hψb
  obtain ⟨ψi, hψi⟩ := hψb.exists_isInverse
  haveI : ψi.IsDominant :=
    MMP.Fourfold.Crepant.isDominant_of_isBirational hψi.isBirational_inverse
  haveI : Nonempty Y' := by
    obtain ⟨e, -⟩ := hψb
    exact ⟨(e.target.ι) (Classical.choice (Set.Nonempty.to_subtype e.dense_target.nonempty))⟩
  refine ⟨ψi.comp φ, ?_⟩
  have hcomp : ψ.comp (ψi.comp φ) = φ := by
    rw [← Scheme.RationalMap.comp_assoc]
    have key : ∀ (a : Y.RationalMap Y) [a.IsDominant], a = Scheme.RationalMap.id Y →
        a.comp φ = φ := by
      intro a _ ha
      subst ha
      exact Scheme.RationalMap.id_comp φ
    exact key _ (MMP.Fourfold.Crepant.comp_eq_id_of_isInverse hψi)
  have hYv := hφ.isNormalVariety_source
  haveI := hYv.1
  haveI := isSeparated_terminal' sS
  rcases hcase with ⟨hfWb, -, hiso, hmod⟩ | hfl
  · -- a divisorial contraction, read as the morphism `fW ≫ fpW⁻¹ : Y ⟶ Y⁺`
    haveI := hiso
    haveI : IsDominant fW := hfWb.isDominant
    have hc := hneg.isContraction
    haveI := hc.isProper
    have hY'n : IsNormalVariety ℂ sY' := hY'q.1
    haveI := hY'n.1
    haveI : IsSeparated (Spec (.of ℂ) ↘ Limits.terminal Scheme) := inferInstance
    haveI : IsIntegral Wd := hneg.isNormalVariety_target.1.toIsIntegral
    haveI := isSeparated_terminal' sY
    have hπY : πY ≫ sS = sY := hφ.comp_eq_source
    have hgW : gW ≫ sS = sWd := by
      refine ext_of_isDominant_of_isSeparated (Spec (.of ℂ) ↘ Limits.terminal Scheme)
        (Limits.terminal.hom_ext _ _) fW ?_
      rw [reassoc_of% hfg, hπY]
      exact hc.comp_eq.symm
    have he : inv fpW ≫ sY' = sWd := by
      rw [IsIso.inv_comp_eq, ← hπY', ← hfpg, Category.assoc, hgW]
    set f : Y ⟶ Y' := fW ≫ inv fpW with hf_def
    have hf : IsNegativeExtremalContraction ℂ sY sY' (logCanonicalDivisor KY C) f :=
      IsNegativeExtremalContraction.comp_isIso hneg (inv fpW) he hY'n
    have hfb : IsBirationalMorphism f :=
      MMP.Fourfold.Crepant.isBirationalMorphism_comp hfWb (isBirationalMorphism_of_isIso _)
    have hfY : f ≫ πY' = πY := by
      rw [hf_def, Category.assoc, ← hfpg, IsIso.inv_hom_id_assoc, hfg]
    have hψf : f.toRationalMap = ψ := by
      have h1 : ψ.compHom fpW = fW.toRationalMap := hmod.2
      rw [hf_def, ← toRationalMap_compHom', ← h1, compHom_compHom', IsIso.hom_inv_id, compHom_id']
    haveI : IsProper f := hf.isContraction.isProper
    obtain ⟨W₀, _, _, _, sW₀, p₀, q₀, h₀, hW₀, -, hp₀Y, hq₀Z, hp₀, hq₀, hp₀b, hq₀b, hinv₀, hhq₀,
      GY₀, GZ₀, hGY₀, hGZ₀, hA₀, hA₀q⟩ := hφ.exists_resolution
    subst hψf
    refine (fun H => ⟨H.1, H.2.1⟩) (hφ.isNefWeakModel_of_step_over hW₀ hp₀Y hq₀Z hp₀ hq₀ hp₀b hq₀b
      hinv₀ hhq₀ hGY₀ hGZ₀ hA₀ hA₀q hY'p hY'q hπY' hcomp hfb hY'n f (𝟙 Y') hfb
      (isBirationalMorphism_of_isIso _) hf.isContraction.comp_eq (Category.id_comp _) hfY
      (Category.id_comp _) (by rw [compHom_id'])
      (fun D => (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint D).le) ?_)
    intro G P₀ hP₀ h0
    exact MMP.Fourfold.not_isExceptional_of_coeff_eq_zero hφ f hfY hf hfb p₀ q₀ h₀ hW₀ hp₀Y hq₀Z
      hp₀ hq₀ hp₀b hq₀b hinv₀ hhq₀ hGY₀ hGZ₀ G P₀
      ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p₀ P₀ G).mpr hP₀) h0
  · -- a flip
    haveI : IsProper fW := hneg.isContraction.isProper
    haveI : IsProper fpW := hfl.isProper
    haveI : IsSeparated sWd := hneg.isNormalVariety_target.1.toIsSeparated
    haveI := isSeparated_terminal' sWd
    haveI := hY'q.1.1
    haveI := isSeparated_terminal' sY'
    obtain ⟨W₀, _, _, _, sW₀, p₀, q₀, h₀, hW₀, -, hp₀Y, hq₀Z, hp₀, hq₀, hp₀b, hq₀b, hinv₀, hhq₀,
      GY₀, GZ₀, hGY₀, hGZ₀, hA₀, hA₀q⟩ := hφ.exists_resolution
    refine (fun H => ⟨H.1, H.2.1⟩) (hφ.isNefWeakModel_of_step_over hW₀ hp₀Y hq₀Z hp₀ hq₀ hp₀b hq₀b
      hinv₀ hhq₀ hGY₀ hGZ₀ hA₀ hA₀q hY'p hY'q hπY' hcomp hfl.isModificationOf.1
      hneg.isNormalVariety_target fW fpW hfl.isSmall_source.isBirationalMorphism
      hfl.isSmall.isBirationalMorphism hneg.isContraction.comp_eq hfl.isSmall.comp_eq hfg hfpg
      hfl.isModificationOf.2 ?_ (fun G _ _ _ => MMP.Fourfold.not_isExceptional_of_isFlip
        hfl.isSmall_source hfl.isSmall hfl.isModificationOf.2 G))
    intro D
    obtain ⟨Q, hQ⟩ := MMP.Flips.exists_primeDivisor_map_genericPoint_eq_of_isSmall hfl.isSmall D
    rw [hQ]
    exact (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q).le

/-- Associativity bookkeeping: `a ≫ (i ≫ P ≫ k) = r ≫ (m ≫ k)` from `P = j ≫ m` and
`a ≫ i ≫ j = r`. -/
private theorem comp_assoc_aux {A B C D E F : Scheme.{0}} {a : A ⟶ B} {i : B ⟶ C} {P : C ⟶ E}
    {j : C ⟶ D} {m : D ⟶ E} {k : E ⟶ F} {r : A ⟶ D} (hP : P = j ≫ m)
    (h2 : a ≫ i ≫ j = r) : a ≫ (i ≫ P ≫ k) = r ≫ (m ≫ k) := by
  subst hP
  rw [← h2]
  simp only [Category.assoc]

/-- Cancelling a monomorphism: `a ≫ i ≫ j = r` from `j ≫ u = w`, `i ≫ w = d`, `a ≫ d = r ≫ u`. -/
private theorem eq_of_comp_mono_aux {A B C D E : Scheme.{0}} {a : A ⟶ B} {i : B ⟶ C}
    {j : C ⟶ D} {r : A ⟶ D} (u : D ⟶ E) [Mono u] {w : C ⟶ E} {d : B ⟶ E} (h1 : j ≫ u = w)
    (h2 : i ≫ w = d) (h3 : a ≫ d = r ≫ u) : a ≫ i ≫ j = r := by
  rw [← cancel_mono u, Category.assoc, Category.assoc, h1, h2, h3]

/-- The partial map `g ∘ p` on `p⁻¹(dom g)`, for a dominant morphism `p` and a partial map `g`. -/
private noncomputable def homCompPartialMap {X Y Z : Scheme.{0}} [IrreducibleSpace X]
    [Nonempty Y] (p : X ⟶ Y) [IsDominant p] (g : Y.PartialMap Z) : X.PartialMap Z where
  domain := p ⁻¹ᵁ g.domain
  dense_domain := by
    obtain ⟨y, hy, x, rfl⟩ :=
      p.denseRange.inter_open_nonempty _ g.domain.2 g.dense_domain.nonempty
    exact (p ⁻¹ᵁ g.domain).2.dense ⟨x, hy⟩
  hom := (p ∣_ g.domain) ≫ g.hom

/-- `homCompPartialMap p g` represents the composite `g ∘ p`. -/
private theorem toRationalMap_homCompPartialMap {X Y Z : Scheme.{0}} [IrreducibleSpace X]
    [Nonempty Y] (p : X ⟶ Y) [IsDominant p] (g : Y.PartialMap Z) :
    p.toRationalMap.comp g.toRationalMap = (homCompPartialMap p g).toRationalMap := by
  change p.toPartialMap.toRationalMap.comp g.toRationalMap = _
  rw [Scheme.RationalMap.toRationalMap_comp, Scheme.PartialMap.toRationalMap_eq_iff]
  have hW : p ⁻¹ᵁ g.domain ≤ (p.toPartialMap.comp g).domain := by
    intro x hx
    exact ⟨⟨x, trivial⟩, hx, rfl⟩
  refine ⟨p ⁻¹ᵁ g.domain, (homCompPartialMap p g).dense_domain, hW, fun x hx => hx, ?_⟩
  change X.homOfLE hW ≫ ((Scheme.Hom.isoImage (Scheme.Hom.toPartialMap p).domain.ι
      ((Scheme.Hom.toPartialMap p).hom ⁻¹ᵁ g.domain)).inv ≫
      (Scheme.Hom.toPartialMap p).hom ∣_ g.domain ≫ g.hom) =
    X.homOfLE (le_refl (p ⁻¹ᵁ g.domain)) ≫ ((p ∣_ g.domain) ≫ g.hom)
  have key : (Scheme.Hom.toPartialMap p).hom ∣_ g.domain =
      (X.topIso.hom ∣_ (p ⁻¹ᵁ g.domain)) ≫ (p ∣_ g.domain) :=
    morphismRestrict_comp X.topIso.hom p g.domain
  have h1 : (X.topIso.hom ∣_ (p ⁻¹ᵁ g.domain)) ≫ (p ⁻¹ᵁ g.domain).ι =
      ((Scheme.Hom.toPartialMap p).hom ⁻¹ᵁ g.domain).ι ≫ (Scheme.Hom.toPartialMap p).domain.ι :=
    (morphismRestrict_ι X.topIso.hom (p ⁻¹ᵁ g.domain)).trans
      (congrArg (fun t => (X.topIso.hom ⁻¹ᵁ (p ⁻¹ᵁ g.domain)).ι ≫ t) (Scheme.topIso_hom X))
  have key2 := eq_of_comp_mono_aux (p ⁻¹ᵁ g.domain).ι h1
    (Scheme.Hom.isoImage_inv_ι (Scheme.Hom.toPartialMap p).domain.ι
      ((Scheme.Hom.toPartialMap p).hom ⁻¹ᵁ g.domain))
    ((Scheme.homOfLE_ι X hW).trans (Scheme.homOfLE_ι X (le_refl (p ⁻¹ᵁ g.domain))).symm)
  exact comp_assoc_aux key key2

/-- A partial map whose morphism is a dominant open immersion represents a birational map. -/
private theorem isBirational_of_isOpenImmersion' {X Y : Scheme.{0}} (c : X.PartialMap Y)
    [IsOpenImmersion c.hom] [IsDominant c.hom] :
    MMP.Mori.RationalMap.IsBirational c.toRationalMap := by
  refine ⟨⟨c.domain, c.dense_domain, c.hom.opensRange, ?_, c.hom.isoOpensRange⟩, ?_⟩
  · rw [Scheme.Hom.coe_opensRange]
    exact c.hom.denseRange
  · change Scheme.PartialMap.toRationalMap ⟨c.domain, c.dense_domain,
      c.hom.isoOpensRange.hom ≫ c.hom.opensRange.ι⟩ = _
    rw [Scheme.Hom.isoOpensRange_hom_ι]

/-- A composite of birational maps is birational. -/
private theorem isBirational_comp {X Y Z : Scheme.{0}} [IrreducibleSpace X] [Nonempty Y]
    {f : X.RationalMap Y} [f.IsDominant] {g : Y.RationalMap Z}
    (hf : MMP.Mori.RationalMap.IsBirational f) (hg : MMP.Mori.RationalMap.IsBirational g) :
    MMP.Mori.RationalMap.IsBirational (f.comp g) := by
  obtain ⟨e₁, rfl⟩ := hf
  obtain ⟨e₂, rfl⟩ := hg
  have key : ∀ (a : X.RationalMap Y) [a.IsDominant], a = e₁.toRationalMap →
      MMP.Mori.RationalMap.IsBirational (a.comp e₂.toRationalMap) := by
    intro a _ ha
    subst ha
    rw [Scheme.RationalMap.toRationalMap_comp]
    have h1 : IsOpenImmersion ((e₁.iso.hom ≫ e₁.target.ι) ∣_ e₂.source) := by
      haveI : IsOpenImmersion ((e₁.iso.hom ≫ e₁.target.ι) ∣_ e₂.source ≫ e₂.source.ι) := by
        rw [morphismRestrict_ι]; infer_instance
      exact IsOpenImmersion.of_comp _ e₂.source.ι
    have h3 : IsOpenImmersion ((e₁.iso.hom ≫ e₁.target.ι) ∣_ e₂.source ≫
        (e₂.iso.hom ≫ e₂.target.ι)) := @IsOpenImmersion.comp _ _ _ _ _ h1 inferInstance
    haveI : IsOpenImmersion (e₁.toPartialMap.comp e₂.toPartialMap).hom :=
      @IsOpenImmersion.comp _ _ _ (Scheme.Hom.isoImage e₁.toPartialMap.domain.ι
        (e₁.toPartialMap.hom ⁻¹ᵁ e₂.toPartialMap.domain)).inv _ inferInstance h3
    haveI : IsDominant e₂.toPartialMap.hom := isDominant_partialIso_hom e₂
    exact isBirational_of_isOpenImmersion' _
  exact key _ rfl

/-- **Strict transforms through a composite with a morphism.** If `h` maps the generic point of
`P_X` to that of `P` and `φ_* P = Q`, then `(φ ∘ h)_* P_X = Q`. -/
private theorem transformPrimeDivisor_hom_comp_eq_some {X Y Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsSeparated (Z ↘ Limits.terminal Scheme)] (h : X ⟶ Y) [IsDominant h]
    {φ : Y.RationalMap Z} {PX : MMP.Mori.PrimeDivisor X} {P : MMP.Mori.PrimeDivisor Y}
    {Q : MMP.Mori.PrimeDivisor Z} (hPX : h PX.genericPoint = P.genericPoint)
    (hPQ : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q) :
    MMP.Mori.RationalMap.transformPrimeDivisor (h.toRationalMap.comp φ) PX = some Q := by
  obtain ⟨hdef, -⟩ := MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hPQ
  obtain ⟨g, hgP, hg⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  have hQ := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hPQ g hg hgP
  have hmem : PX.genericPoint ∈ (homCompPartialMap h g).domain := by
    change h PX.genericPoint ∈ g.domain
    rwa [hPX]
  refine MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq (homCompPartialMap h g)
    (by rw [← toRationalMap_homCompPartialMap, hg]) hmem ?_
  rw [hQ]
  change _ = g.hom ((h ∣_ g.domain) ⟨PX.genericPoint, hmem⟩)
  congr 1
  exact Subtype.ext
    (hPX.symm.trans (morphismRestrict_base_coe h g.domain ⟨PX.genericPoint, hmem⟩).symm)

/-- **Strict transforms of prime divisors are injective** under a birational map of normal
projective complex varieties compatible with the structure morphisms: two prime divisors with the
same transform have the same strict transform on a common resolution. -/
private theorem eq_of_transformPrimeDivisor_eq_some {X Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hXn : IsNormalVariety ℂ sX)
    (hXp : MMP.Mori.IsProjectiveVariety ℂ sX) (hZn : IsNormalVariety ℂ sZ)
    (hZp : MMP.Mori.IsProjectiveVariety ℂ sZ) {φ : X.RationalMap Z}
    (hφ : MMP.Mori.RationalMap.IsBirational φ) (hφs : φ.compHom sZ = sX.toRationalMap)
    {P₁ P₂ : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Z}
    (h₁ : MMP.Mori.RationalMap.transformPrimeDivisor φ P₁ = some Q)
    (h₂ : MMP.Mori.RationalMap.transformPrimeDivisor φ P₂ = some Q) : P₁ = P₂ := by
  haveI := hZn.1
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  obtain ⟨W, _, _, _, sW, p, q, h, hWn, -, hpX, hqZ, hpp, hpb, hqp, hqb, hinv, hcomp⟩ :=
    exists_smooth_common_resolution sX sZ hXn hZn ((MMP.Mori.isProjectiveVariety_iff ℂ sX).mp hXp).2
      ((MMP.Mori.isProjectiveVariety_iff ℂ sZ).mp hZp).2 hφ hφs
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqp
  haveI := hWn.1
  haveI : CompactSpace W := (quasiCompact_iff_compactSpace sW).mp inferInstance
  have hWp : IsNormalVariety ℂ (p ≫ sX) := hpX ▸ hWn
  have hWq : IsNormalVariety ℂ (q ≫ sZ) := hqZ ▸ hWn
  obtain ⟨E₁, hE₁p, -, hE₁q, -⟩ :=
    MMP.Fourfold.exists_primeDivisor_apply_eq_of_transformPrimeDivisor_eq_some hXn hZn p q h hWp hpb
      hqb hinv hcomp h₁
  obtain ⟨E₂, hE₂p, -, hE₂q, -⟩ :=
    MMP.Fourfold.exists_primeDivisor_apply_eq_of_transformPrimeDivisor_eq_some hXn hZn p q h hWp hpb
      hqb hinv hcomp h₂
  obtain rfl : E₁ = E₂ := eq_of_map_genericPoint_eq hZn hWq hqb Q E₁ E₂ hE₁q hE₂q
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hE₁p.symm.trans hE₂p)

/-- A morphism of reduced schemes into a separated scheme is determined by its rational map. -/
private theorem hom_eq_of_toRationalMap_eq' {X Y : Scheme.{0}} [IsReduced X]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] {f g : X ⟶ Y}
    (h : f.toRationalMap = g.toRationalMap) : f = g := by
  have := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := Limits.terminal Scheme)
    (f := f.toPartialMap) (g := g)).mp (Scheme.PartialMap.toRationalMap_eq_iff.mp h)
  change X.topIso.hom ≫ f = (⊤ : X.Opens).ι ≫ g at this
  rw [← Scheme.topIso_hom] at this
  exact (cancel_epi _).mp this

/-- A closed immersion contracts no proper curve. -/
private theorem not_isContractedBy_of_isClosedImmersion {A X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} (ι : A ⟶ X) [IsClosedImmersion ι] [IsSeparated (ι ≫ sX)]
    (C : ProperCurve (ι ≫ sX)) : ¬ C.IsContractedBy ι := by
  intro hc
  let C' : ProperCurve (𝟙 A ≫ ι ≫ sX) := ⟨C.point, by simpa using C.isProperCurve⟩
  refine ProperCurve.not_isProperCurve_of_forall_eq (𝟙 A) C' (y := C.point) (fun z => ?_)
    (by simpa using C.isProperCurve)
  have hz : (C'.ι.base z) ∈ closure ({C.point} : Set A) := by
    have h1 : Set.range (curveSubschemeAtι C.point).base = closure ({C.point} : Set A) := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    rw [← h1]
    exact ⟨z, rfl⟩
  have := hc _ hz
  simp only [Scheme.Hom.comp_base, TopCat.comp_app, Scheme.Hom.id_base, TopCat.id_app]
  exact ι.isClosedEmbedding.injective this

/-- **The pull-back of an `ℝ`-Cartier divisor along a composite** is the iterated pull-back. -/
private theorem isRCartierPullback_comp' {A B C : Scheme.{0}} [IsIntegral A]
    [IsLocallyNoetherian A] [IsNormal A] [CompactSpace A] [IsIntegral B] [IsLocallyNoetherian B]
    [IsNormal B] [CompactSpace B] [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    [CompactSpace C] (f : A ⟶ B) (g : B ⟶ C) [IsDominant f] [IsDominant g] {N : RDivisor C}
    {G : RDivisor B} {G' : RDivisor A} (h₁ : IsRCartierPullback g N G)
    (h₂ : IsRCartierPullback f G G') : IsRCartierPullback (f ≫ g) N G' := by
  obtain ⟨m, r, L, L', hL, hN, hpb, hG⟩ := h₁
  choose hB hpbj using hpb
  have hL'c : ∀ j, (L' j).IsCartier := fun j => by
    rw [← Divisor.IsPullback.pullback_eq (hL j) (hpbj j)]
    exact (hL j).isCartier_pullback g (hB j)
  have hB' := fun j => MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f (L' j)
  have hB'' := fun j =>
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (f ≫ g) (L j)
  let L'' : Fin m → Divisor A := fun j => (L' j).pullback (hL'c j) (hB' j)
  have hp2 : ∀ j, (L' j).IsPullback f (hB' j) (L'' j) := fun j =>
    Divisor.isPullback_pullback (hL'c j) _
  have hp3 : ∀ j, (L j).IsPullback (f ≫ g) (hB'' j) (L'' j) := fun j =>
    MMP.ProgramBaseChange.divisor_isPullback_comp rfl (hpbj j) (hp2 j) (hB'' j)
  have hG'' : IsRCartierPullback f G (∑ j, r j • Divisor.toRDivisor (L'' j)) :=
    ⟨m, r, L', L'', hL'c, hG, fun j => ⟨hB' j, hp2 j⟩, rfl⟩
  have heq := MMP.Flips.IsRCartierPullback.eq f h₂ hG''
  exact ⟨m, r, L, L'', hL, hN, fun j => ⟨hB'' j, hp3 j⟩, heq⟩

/-- **Pull-backs along a proper birational morphism are injective**: the coefficient of `A` at a
prime divisor is that of its pull-back at the strict transform. -/
private theorem eq_of_isRCartierPullback_of_isBirationalMorphism {V W : Scheme.{0}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [IsLocallyNoetherian V] [IsNormal V]
    {sV : V ⟶ Spec (.of ℂ)} (hVn : IsNormalVariety ℂ sV) (p : W ⟶ V)
    (hWn : IsNormalVariety ℂ (p ≫ sV)) [IsProper p] (hpb : IsBirationalMorphism p)
    {A A' : RDivisor V} {G : RDivisor W} (h₁ : IsRCartierPullback p A G)
    (h₂ : IsRCartierPullback p A' G) : A = A' := by
  ext E
  obtain ⟨E', heq, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hVn hWn hpb E
  haveI := hiso
  change A.coeff E = A'.coeff E
  rw [← MMP.Fourfold.coeff_eq_of_isRCartierPullback E' E heq h₁,
    MMP.Fourfold.coeff_eq_of_isRCartierPullback E' E heq h₂]

/-- **The identity is a nef weak model of a nef pair**: on a smooth resolution `p = q` of `Y`,
the comparison vanishes. -/
private theorem isNefWeakModel_id {Y S : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {sY : Y ⟶ Spec (.of ℂ)} [QuasiCompact sY]
    {sS : S ⟶ Spec (.of ℂ)} {πY : Y ⟶ S} (hYn : IsNormalVariety ℂ sY)
    (hYp : MMP.Mori.IsProjectiveVariety ℂ sY) (hπY : πY ≫ sS = sY) {K : Divisor Y}
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sY m) {D : RDivisor Y}
    (hnef : IsRelativelyNef ℂ sY πY (logCanonicalDivisor K D)) :
    IsNefWeakModel sY sY sS πY πY K D (Scheme.RationalMap.id Y) := by
  classical
  haveI := hYn.1
  haveI := isSeparated_terminal' sY
  have htr : ∀ {R : Type} [AddCommMonoid R] (N : DivisorWithCoeffs R Y),
      MMP.Mori.RationalMap.transformDivisor (Scheme.RationalMap.id Y) N = N := by
    intro R _ N
    ext Q
    exact MMP.Fourfold.Oai4C1.transformDivisor_apply_of_map_genericPoint (f := 𝟙 Y)
      (isBirationalMorphism_of_isIso _) rfl N
  have hid : MMP.Mori.RationalMap.IsBirational (Scheme.RationalMap.id Y) :=
    MMP.Mori.RationalMap.isBirational_id
  have hover : ∀ {T : Scheme.{0}} (π : Y ⟶ T),
      (Scheme.RationalMap.id Y).compHom π = π.toRationalMap := by
    intro T π
    rw [Scheme.RationalMap.id, ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.id_compHom]
  have hE : ∀ F : MMP.Mori.PrimeDivisor Y,
      ¬ MMP.Flips.RationalMap.IsInverseExceptional (Scheme.RationalMap.id Y) F := fun F hF =>
    hF F ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff (𝟙 Y) F F).mpr rfl)
  have hc := (isRelativelyNef_iff.mp hnef).1
  refine ⟨hYn, hYp, hπY, hK, hc, hYn, hYp, hπY, hid, hover πY, hE,
    by rw [htr, htr]; exact hnef, ?_⟩
  obtain ⟨W, _, _, _, sW, p, q, h, hWn, hWsm, hpY, hqY, hpp, hpb, hqp, hqb, hinv, hcomp⟩ :=
    exists_smooth_common_resolution sY sY hYn hYn ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hYp).2
      ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hYp).2 hid (hover sY)
  haveI : IsDominant p := hpb.isDominant
  haveI : p.toRationalMap.IsDominant := by
    change (Scheme.Hom.toPartialMap p).toRationalMap.IsDominant
    infer_instance
  haveI : h.IsDominant := MMP.Fourfold.Crepant.isDominant_of_isBirational hinv.isBirational_inverse
  haveI := hWn.1
  have hpq : p = q := by
    refine hom_eq_of_toRationalMap_eq' ?_
    have e1 : p.toRationalMap.comp h = Scheme.RationalMap.id W :=
      MMP.Fourfold.Crepant.comp_eq_id_of_isInverse hinv
    have key : ∀ (a : W.RationalMap W) [a.IsDominant], a = Scheme.RationalMap.id W →
        a.comp q.toRationalMap = q.toRationalMap := by
      intro a _ ha
      subst ha
      exact Scheme.RationalMap.id_comp _
    rw [← key _ e1, Scheme.RationalMap.comp_assoc, Scheme.RationalMap.comp_toRationalMap, hcomp,
      Scheme.RationalMap.comp_id]
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  obtain ⟨GY, hGY, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p hc
  refine ⟨W, inferInstance, inferInstance, inferInstance, sW, p, q, h, hWn.1, hWsm, hpY, hqY, hpp,
    hqp, hpb, hqb, hinv, hcomp, GY, GY, hGY, ?_, ?_, ?_⟩
  · rwa [htr, htr, ← hpq]
  · intro P; simp
  · intro P hP; simp at hP

/-! ### Uniqueness of pull-backs along arbitrary morphisms -/

/-- The Cartier divisors on `X` whose support avoids the generic points of `Y` under `f`: the
divisors that can be pulled back along `f`. -/
private def genericCartierSubgroup {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    (f : Y ⟶ X) : AddSubgroup (Divisor X) where
  carrier :=
    {L | L.IsCartier ∧ ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ L.supp}
  zero_mem' := ⟨Divisor.isCartier_zero, fun Z h => by
    rw [DivisorWithCoeffs.supp_zero] at h
    exact absurd (show _ ∈ ((⊥ : TopologicalSpace.Closeds X) : Set X) from h) (by simp)⟩
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun Z h => by
    rcases DivisorWithCoeffs.supp_add_le a b h with h | h
    · exact ha.2 Z h
    · exact hb.2 Z h⟩
  neg_mem' := fun {a} ha => ⟨ha.1.neg, fun Z h => ha.2 Z (by rwa [DivisorWithCoeffs.supp_neg] at h)⟩

/-- The pull-back along `f`, as an additive map on the divisors that can be pulled back. -/
private noncomputable def genericPullbackHom {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (f : Y ⟶ X) :
    genericCartierSubgroup f →+ Divisor Y where
  toFun L := (L : Divisor X).pullback L.2.1 L.2.2
  map_zero' := Divisor.IsPullback.pullback_eq Divisor.isCartier_zero (Divisor.isPullback_zero _)
  map_add' L₁ L₂ := Divisor.IsPullback.pullback_eq (L₁ + L₂).2.1
    (Divisor.IsPullback.add L₁.2.1 L₂.2.1 _ (Divisor.isPullback_pullback _ _)
      (Divisor.isPullback_pullback _ _))

/-- **Uniqueness of the pull-back of an `ℝ`-Cartier divisor** along an arbitrary morphism: two
presentations of `D` by Cartier divisors avoiding the image of the generic points agree in
`Ca ⊗ ℝ` (`ℝ` is flat over `ℤ`), so their pull-backs agree. -/
private theorem IsRCartierPullback.eq' {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (f : Y ⟶ X) {D : RDivisor X}
    {G₁ G₂ : RDivisor Y} (h₁ : IsRCartierPullback f D G₁) (h₂ : IsRCartierPullback f D G₂) :
    G₁ = G₂ := by
  classical
  obtain ⟨m, r, L, L', hL, hD₁, hp₁, rfl⟩ := h₁
  obtain ⟨m', s, M, M', hM, hD₂, hp₂, rfl⟩ := h₂
  choose hB₁ hpb₁ using hp₁
  choose hB₂ hpb₂ using hp₂
  let ℓ : Fin m → genericCartierSubgroup f := fun j => ⟨L j, hL j, hB₁ j⟩
  let μ : Fin m' → genericCartierSubgroup f := fun k => ⟨M k, hM k, hB₂ k⟩
  have hinj : Function.Injective (MMP.Flips.rDivisorTensorMap (genericCartierSubgroup f).subtype) :=
    (Divisor.tensorEquiv ℝ X).injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have ht : ∑ j, (ℓ j ⊗ₜ[ℤ] r j) = ∑ k, (μ k ⊗ₜ[ℤ] s k) := by
    apply hinj
    simp only [map_sum, MMP.Flips.rDivisorTensorMap_tmul, AddSubgroup.coe_subtype]
    exact hD₁.symm.trans hD₂
  have h := congrArg (MMP.Flips.rDivisorTensorMap (genericPullbackHom f)) ht
  simp only [map_sum, MMP.Flips.rDivisorTensorMap_tmul] at h
  have e₁ : ∀ j, genericPullbackHom f (ℓ j) = L' j := fun j =>
    Divisor.IsPullback.pullback_eq (hL j) (hpb₁ j)
  have e₂ : ∀ k, genericPullbackHom f (μ k) = M' k := fun k =>
    Divisor.IsPullback.pullback_eq (hM k) (hpb₂ k)
  simpa only [e₁, e₂] using h

/-- The support of a pull-back maps into the support: off `Supp L`, the constant `1` is a local
equation of `L`, so `g^* L` has coefficient `0` along every prime divisor through a point mapping
off `Supp L`. -/
private theorem map_mem_supp_of_mem_supp_pullback {A B : Scheme.{0}} [IsLocallyNoetherian A]
    [IsNormal A] [IsLocallyNoetherian B] [IsNormal B] {g : A ⟶ B} {L : Divisor B}
    {hB : ∀ Z : irreducibleComponents A, g (componentGenericPoint A Z) ∉ L.supp} {L' : Divisor A}
    (h : L.IsPullback g hB L') {a : A} (ha : a ∈ L'.supp) : g a ∈ L.supp := by
  by_contra hga
  obtain ⟨E, hE, haE⟩ := DivisorWithCoeffs.mem_supp_iff.mp ha
  let U : B.Opens := ⟨(L.supp : Set B)ᶜ, L.supp.isClosed.isOpen_compl⟩
  have hφ : L.IsLocalEquation U 1 := by
    intro E' hE'
    rw [MMP.Mori.PrimeDivisor.ord_one]
    by_contra hne
    obtain ⟨y, hy1, hy2⟩ := hE'
    exact hy2 (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E', hne, hy1⟩)
  have hEU : (E.support ∩ g ⁻¹ᵁ U).Nonempty := ⟨a, haE, hga⟩
  apply hE
  rw [h U 1 hφ E hEU, pullbackComponent_eq hB hφ _ (mem_pointComponent _) 1 (by simp), map_one,
    MMP.Mori.PrimeDivisor.ordUnit_one]

/-- **Iterated pull-backs along arbitrary morphisms.** If `N = ∑ r_j L_j` with the `L_j`
pulling back along `g`, their pull-backs along `f`, and along `f ≫ g`, then `f^*(g^* N)` is
`(f ≫ g)^* N`. -/
private theorem eq_of_isRCartierPullback_comp {A B C : Scheme.{0}} [IsIntegral A]
    [IsLocallyNoetherian A] [IsNormal A] [CompactSpace A] [IsIntegral B] [IsLocallyNoetherian B]
    [IsNormal B] [CompactSpace B]
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C] (f : A ⟶ B)
    (g : B ⟶ C) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor C} (hL : ∀ j, (L j).IsCartier)
    (hgB : ∀ j, ∀ Z : irreducibleComponents B, g (componentGenericPoint B Z) ∉ (L j).supp)
    (hfgB : ∀ j, ∀ Z : irreducibleComponents A, (f ≫ g) (componentGenericPoint A Z) ∉ (L j).supp)
    {N : RDivisor C} (hN : N = ∑ j, r j • Divisor.toRDivisor (L j)) {G G' G'' : RDivisor _}
    (h₁ : IsRCartierPullback g N G) (h₂ : IsRCartierPullback f G G')
    (h₃ : IsRCartierPullback (f ≫ g) N G'') : G' = G'' := by
  let L' : Fin m → Divisor B := fun j => (L j).pullback (hL j) (hgB j)
  have hL'c : ∀ j, (L' j).IsCartier := fun j => (hL j).isCartier_pullback g (hgB j)
  have hfB : ∀ j, ∀ Z : irreducibleComponents A, f (componentGenericPoint A Z) ∉ (L' j).supp :=
    fun j Z hZ => hfgB j Z (map_mem_supp_of_mem_supp_pullback
      (Divisor.isPullback_pullback (hL j) (hgB j)) hZ)
  let L'' : Fin m → Divisor A := fun j => (L' j).pullback (hL'c j) (hfB j)
  have hG : G = ∑ j, r j • Divisor.toRDivisor (L' j) := IsRCartierPullback.eq' g h₁
    ⟨m, r, L, L', hL, hN, fun j => ⟨hgB j, Divisor.isPullback_pullback (hL j) _⟩, rfl⟩
  have hG' : G' = ∑ j, r j • Divisor.toRDivisor (L'' j) := IsRCartierPullback.eq' f h₂
    ⟨m, r, L', L'', hL'c, hG, fun j => ⟨hfB j, Divisor.isPullback_pullback (hL'c j) _⟩, rfl⟩
  have hG'' : G'' = ∑ j, r j • Divisor.toRDivisor (L'' j) := IsRCartierPullback.eq' (f ≫ g) h₃
    ⟨m, r, L, L'', hL, hN, fun j => ⟨hfgB j, MMP.ProgramBaseChange.divisor_isPullback_comp rfl
      (Divisor.isPullback_pullback (hL j) (hgB j)) (Divisor.isPullback_pullback (hL'c j) _)
      (hfgB j)⟩, rfl⟩
  exact hG'.trans hG''.symm

/-- **Coefficients of the flip transform.** For a real flip step `X ⟶ T ⟵ X⁺`, a prime divisor
`P` of `X` and a prime divisor `Q` of `X⁺` with the same image in `T` carry the same coefficient
in a divisor and in its flip transform: the image of `Q` lies in the common biregular locus. -/
private theorem IsRealFlipStep.flipTransform_apply_of_map_eq {X Xp T : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] {sX : X ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor X} {B : RDivisor X} {Kp : Divisor Xp}
    {Bp : RDivisor Xp} {f : X ⟶ T} {fp : Xp ⟶ T} (hflip : IsRealFlipStep sX sT sXp K B Kp Bp f fp)
    (hXp : IsNormalVariety ℂ sXp)
    {P : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Xp}
    (hPQ : f P.genericPoint = fp Q.genericPoint) {R : Type} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) : flipTransform f fp D Q = D P := by
  classical
  have hneg := hflip.isNegativeExtremalContraction
  have hTn := hneg.isNormalVariety_target
  have hfc := hneg.isContraction
  haveI := hTn.1
  haveI := hTn.2
  haveI := hXp.1
  haveI : IsIntegral T := hTn.1.toIsIntegral
  haveI := hfc.isProper
  haveI : IsProper fp := hflip.isSmall_flip.isProper
  have hfb := hflip.isBirationalMorphism
  have hfpb := hflip.isBirationalMorphism_flip
  haveI : IsDominant f := hfb.isDominant
  haveI : IsDominant fp := hfpb.isDominant
  haveI := isSeparated_terminal' sT
  set U := MMP.Fourfold.commonBiregularLocus f fp
  obtain ⟨V, hfV, hfpV, -, hX'V⟩ := hflip.exists_opens_isIso
  have hVU : V ≤ U := (MMP.Fourfold.isBiregular_and_isBiregular_iff f fp).mp ⟨hfV, hfpV⟩
  have hy : fp Q.genericPoint ∈ U :=
    hVU (hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q).le)
  have hUfp : U ≤ MMP.Mori.biregularLocus fp :=
    MMP.Mori.le_biregularLocus (MMP.Fourfold.isBiregular_commonBiregularLocus_right f fp)
  have hcy : Order.coheight (fp Q.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hUfp hy)]
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q
  let QT := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcy
  have hQT : QT.genericPoint = fp Q.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcy
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  haveI : ValuationRing (T.presheaf.stalk QT.genericPoint) :=
    MMP.Fourfold.valuationRing_stalk_of_coheight_le_one (by rw [hQT, hcy])
  haveI : Surjective fp := surjective_of_isProper_of_isDominant fp
  exact flipTransform_apply_of_map_genericPoint hfb.functionFieldMap_bijective fp.surjective
    (P := P) (Pp := Q) (Q := QT)
    (by change f (AlgebraicGeometry.PrimeDivisor.genericPoint P) =
          AlgebraicGeometry.PrimeDivisor.genericPoint QT; rw [hPQ, hQT]) hQT.symm
    (by change AlgebraicGeometry.PrimeDivisor.genericPoint QT ∈ _; rw [hQT]; exact hUfp hy) D

/-- Every prime divisor `Q` of the flipped model `X⁺` of a real flip step lies over the image of
a prime divisor `P` of `X`, in the common biregular locus. -/
private theorem IsRealFlipStep.exists_map_eq {X Xp T : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] {sX : X ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor X} {B : RDivisor X} {Kp : Divisor Xp}
    {Bp : RDivisor Xp} {f : X ⟶ T} {fp : Xp ⟶ T} (hflip : IsRealFlipStep sX sT sXp K B Kp Bp f fp)
    (hXp : IsNormalVariety ℂ sXp)
    (Q : MMP.Mori.PrimeDivisor Xp) : ∃ P : MMP.Mori.PrimeDivisor X,
      f P.genericPoint = fp Q.genericPoint ∧
        f P.genericPoint ∈ MMP.Fourfold.commonBiregularLocus f fp := by
  have hneg := hflip.isNegativeExtremalContraction
  have hTn := hneg.isNormalVariety_target
  haveI := hTn.1
  haveI := hXp.1
  set U := MMP.Fourfold.commonBiregularLocus f fp
  haveI hfU : IsIso (f ∣_ U) := MMP.Fourfold.isBiregular_commonBiregularLocus_left f fp
  obtain ⟨V, hfV, hfpV, -, hX'V⟩ := hflip.exists_opens_isIso
  have hVU : V ≤ U := (MMP.Fourfold.isBiregular_and_isBiregular_iff f fp).mp ⟨hfV, hfpV⟩
  have hy : fp Q.genericPoint ∈ U :=
    hVU (hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q).le)
  have hUfp : U ≤ MMP.Mori.biregularLocus fp :=
    MMP.Mori.le_biregularLocus (MMP.Fourfold.isBiregular_commonBiregularLocus_right f fp)
  have hUf : U ≤ MMP.Mori.biregularLocus f :=
    MMP.Mori.le_biregularLocus (MMP.Fourfold.isBiregular_commonBiregularLocus_left f fp)
  have hcy : Order.coheight (fp Q.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hUfp hy)]
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q
  let z := inv (f ∣_ U) ⟨_, hy⟩
  let x : X := (f ⁻¹ᵁ U).ι z
  have hfx : f x = fp Q.genericPoint := by
    have h1 : (f ∣_ U) z = ⟨_, hy⟩ := by
      change (inv (f ∣_ U) ≫ (f ∣_ U)) ⟨_, hy⟩ = _
      rw [IsIso.inv_hom_id]; rfl
    have h2 : U.ι ((f ∣_ U) z) = f x := by
      change ((f ∣_ U) ≫ U.ι) z = ((f ⁻¹ᵁ U).ι ≫ f) z
      rw [morphismRestrict_ι]
    rw [← h2, h1]; rfl
  have hcx : Order.coheight x = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus f (by rw [hfx]; exact hUf hy), hfx,
      hcy]
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hcx, ?_, ?_⟩
  · change f (AlgebraicGeometry.PrimeDivisor.genericPoint _) = _
    rwa [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  · change f (AlgebraicGeometry.PrimeDivisor.genericPoint _) ∈ _
    rwa [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hfx]

/-- **The flip as a birational map.** For a real flip step `X ⟶ T ⟵ X⁺`, the composite
`χ = (f⁺)⁻¹ ∘ f : X ⤏ X⁺`, with `(f⁺)⁻¹` the inverse of `f⁺` over the common biregular locus `U`
of `f` and `f⁺`, is birational over `T`, transforms divisors by `(f⁺)⁻¹_* f_*`, and every prime
divisor of `X⁺` is a transform. -/
private theorem IsRealFlipStep.exists_flipMap {X Xp T : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] {sX : X ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor X} {B : RDivisor X} {Kp : Divisor Xp}
    {Bp : RDivisor Xp} {f : X ⟶ T} {fp : Xp ⟶ T} (hflip : IsRealFlipStep sX sT sXp K B Kp Bp f fp)
    (hXp : IsNormalVariety ℂ sXp) :
    ∃ χ : X.RationalMap Xp, MMP.Mori.RationalMap.IsBirational χ ∧
      MMP.Flips.RationalMap.IsOver f fp χ ∧
      (∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
        MMP.Mori.RationalMap.transformDivisor χ D = flipTransform f fp D) ∧
      ∀ Q : MMP.Mori.PrimeDivisor Xp, ¬ MMP.Flips.RationalMap.IsInverseExceptional χ Q := by
  classical
  have hneg := hflip.isNegativeExtremalContraction
  have hTn := hneg.isNormalVariety_target
  have hXn := hneg.isNormalVariety_source
  have hfc := hneg.isContraction
  haveI := hTn.1
  haveI := hTn.2
  haveI := hXp.1
  haveI : IsIntegral T := hTn.1.toIsIntegral
  haveI := hfc.isProper
  have hfb := hflip.isBirationalMorphism
  have hfpb := hflip.isBirationalMorphism_flip
  haveI : IsDominant f := hfb.isDominant
  haveI : IsDominant fp := hfpb.isDominant
  haveI := isSeparated_terminal' sT
  haveI := isSeparated_terminal' sXp
  set U := MMP.Fourfold.commonBiregularLocus f fp
  haveI hfpU : IsIso (fp ∣_ U) := MMP.Fourfold.isBiregular_commonBiregularLocus_right f fp
  haveI hfU : IsIso (f ∣_ U) := MMP.Fourfold.isBiregular_commonBiregularLocus_left f fp
  obtain ⟨V, hfV, hfpV, hXV, hX'V⟩ := hflip.exists_opens_isIso
  have hVU : V ≤ U := (MMP.Fourfold.isBiregular_and_isBiregular_iff f fp).mp ⟨hfV, hfpV⟩
  have hXU : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ U := fun x hx => hVU (hXV x hx)
  have hX'U : ∀ x : Xp, Order.coheight x ≤ 1 → fp x ∈ U := fun x hx => hVU (hX'V x hx)
  have hUd : Dense (U : Set T) := by
    refine U.2.dense ⟨_, hXU (genericPoint X) ?_⟩
    rw [Order.coheight_eq_zero.mpr]
    · exact zero_le_one
    · intro y _
      exact (genericPoint_specializes y)
  -- the inverse of `f⁺` over `U`
  let g : T.PartialMap Xp := ⟨U, hUd, inv (fp ∣_ U) ≫ (fp ⁻¹ᵁ U).ι⟩
  haveI : IsOpenImmersion g.hom := by change IsOpenImmersion (inv (fp ∣_ U) ≫ _); infer_instance
  haveI : IsDominant g.hom := by
    constructor
    change DenseRange (inv (fp ∣_ U) ≫ (fp ⁻¹ᵁ U).ι).base
    rw [DenseRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      (ConcreteCategory.bijective_of_isIso (inv (fp ∣_ U)).base).2.range_eq, Set.image_univ,
      Scheme.Opens.range_ι]
    refine (fp ⁻¹ᵁ U).2.dense ⟨_, hX'U (genericPoint Xp) ?_⟩
    rw [Order.coheight_eq_zero.mpr]
    · exact zero_le_one
    · intro y _
      exact (genericPoint_specializes y)
  have hgb : MMP.Mori.RationalMap.IsBirational g.toRationalMap := isBirational_of_isOpenImmersion' g
  haveI : f.toRationalMap.IsDominant := by
    change (Scheme.Hom.toPartialMap f).toRationalMap.IsDominant
    infer_instance
  haveI : g.toRationalMap.IsDominant := inferInstance
  have hover : MMP.Flips.RationalMap.IsOver f fp (f.toRationalMap.comp g.toRationalMap) := by
    change (f.toRationalMap.comp g.toRationalMap).compHom fp = f.toRationalMap
    rw [← Scheme.RationalMap.comp_toRationalMap, Scheme.RationalMap.comp_assoc,
      Scheme.RationalMap.comp_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap]
    have key : inv (fp ∣_ U) ≫ (fp ⁻¹ᵁ U).ι ≫ fp = U.ι := by
      rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    have hg : (g.compHom fp).toRationalMap = Scheme.Hom.toRationalMap (𝟙 T) := by
      rw [Scheme.PartialMap.toRationalMap_eq_iff]
      refine ⟨U, hUd, le_rfl, fun x _ => trivial, ?_⟩
      change T.homOfLE le_rfl ≫ ((inv (fp ∣_ U) ≫ (fp ⁻¹ᵁ U).ι) ≫ fp) =
        T.homOfLE _ ≫ T.topIso.hom ≫ 𝟙 T
      rw [Category.assoc, key, Scheme.homOfLE_rfl, Category.id_comp, Category.comp_id,
        Scheme.topIso_hom]
      exact (Scheme.homOfLE_ι T _).symm
    rw [hg, Scheme.RationalMap.comp_toRationalMap, compHom_id']
  have htr : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
      MMP.Mori.RationalMap.transformDivisor (f.toRationalMap.comp g.toRationalMap) D =
        flipTransform f fp D := fun D =>
    MMP.Mori.transformDivisor_eq_flipTransform_of_isIso_restrict (k := ℂ) hTn
      (hfc.comp_eq ▸ hXn) hfb U hXU hX'U hover D
  refine ⟨f.toRationalMap.comp g.toRationalMap, isBirational_comp hfb hgb, hover, htr, ?_⟩
  intro Q hQ
  obtain ⟨P, hPQ, -⟩ := IsRealFlipStep.exists_map_eq hflip hXp Q
  have h1 := IsRealFlipStep.flipTransform_apply_of_map_eq hflip hXp hPQ (Finsupp.single P (1 : ℤ))
  rw [← htr, Finsupp.single_eq_same, MMP.Mori.RationalMap.transformDivisor_single] at h1
  rcases hχP : MMP.Mori.RationalMap.transformPrimeDivisor (f.toRationalMap.comp g.toRationalMap) P
    with _ | E
  · rw [hχP] at h1; simp at h1
  · rw [hχP] at h1
    simp only [Option.elim_some, Finsupp.single_apply] at h1
    split_ifs at h1 with hEQ
    · exact hQ P (by rw [hχP, hEQ])
    · exact absurd h1 zero_ne_one

/-- The generic point of a prime divisor `E` lies in the support of `D` exactly when `E` has a
nonzero coefficient in `D`. -/
private theorem genericPoint_mem_supp_iff {Y : Scheme.{0}} (D : Divisor Y)
    (E : MMP.Mori.PrimeDivisor Y) : E.genericPoint ∈ D.supp ↔ D E ≠ 0 := by
  rw [DivisorWithCoeffs.mem_supp_iff]
  constructor
  · rintro ⟨E', hE', hmem⟩
    have h := MMP.Mori.PrimeDivisor.eq_genericPoint_of_mem_support E' hmem
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E)
    rwa [AlgebraicGeometry.PrimeDivisor.genericPoint_injective h]
  · intro h
    refine ⟨E, h, ?_⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

/-- Over an open `U` over which `g` is an isomorphism, specializations lift along `g`. -/
private theorem specializes_of_isIso_restrict {Y T : Scheme.{0}} (g : Y ⟶ T) (U : T.Opens)
    [IsIso (g ∣_ U)] {a b : Y} (ha : g a ∈ U) (hb : g b ∈ U) (h : g a ⤳ g b) : a ⤳ b := by
  obtain ⟨a', rfl⟩ : a ∈ Set.range (g ⁻¹ᵁ U).ι.base := by rwa [Scheme.Opens.range_ι]
  obtain ⟨b', rfl⟩ : b ∈ Set.range (g ⁻¹ᵁ U).ι.base := by rwa [Scheme.Opens.range_ι]
  have R : ∀ y, U.ι ((g ∣_ U) y) = g ((g ⁻¹ᵁ U).ι y) := fun y => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have h1 : (g ∣_ U) a' ⤳ (g ∣_ U) b' := by
    rw [← U.ι.isOpenEmbedding.toIsInducing.specializes_iff]
    change U.ι ((g ∣_ U) a') ⤳ U.ι ((g ∣_ U) b')
    rwa [R, R]
  have e : ∀ y, (inv (g ∣_ U)) ((g ∣_ U) y) = y := fun y => by
    change ((g ∣_ U) ≫ inv (g ∣_ U)) y = y
    rw [IsIso.hom_inv_id]; rfl
  have h2 := h1.map (inv (g ∣_ U)).continuous
  rw [e, e] at h2
  exact h2.map (g ⁻¹ᵁ U).ι.continuous

/-- For a closed immersion `a` onto a prime divisor `E` and `g` an isomorphism over `U` with
`g(η_E) ∈ U`, a point `t ∈ U` lies in `g(E)` exactly when it is a specialization of `g(η_E)`. -/
private theorem mem_range_comp_iff_specializes {A Y T : Scheme.{0}} (a : A ⟶ Y) (g : Y ⟶ T)
    (U : T.Opens) [IsIso (g ∣_ U)] {E : MMP.Mori.PrimeDivisor Y}
    (ha : Set.range a.base = (E.support : Set Y)) (hE : g E.genericPoint ∈ U) {t : T}
    (ht : t ∈ U) : t ∈ Set.range (a ≫ g).base ↔ g E.genericPoint ⤳ t := by
  constructor
  · rintro ⟨w, rfl⟩
    have hw : a w ∈ (E.support : Set Y) := ha ▸ ⟨w, rfl⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hw
    exact (specializes_iff_mem_closure.mpr hw).map g.continuous
  · intro h
    let y : Y := (g ⁻¹ᵁ U).ι ((inv (g ∣_ U)) ⟨t, ht⟩)
    have hy : g y = t := by
      have h1 : (g ∣_ U) ((inv (g ∣_ U)) ⟨t, ht⟩) = ⟨t, ht⟩ := by
        change (inv (g ∣_ U) ≫ (g ∣_ U)) ⟨t, ht⟩ = _
        rw [IsIso.inv_hom_id]; rfl
      have h2 : U.ι ((g ∣_ U) ((inv (g ∣_ U)) ⟨t, ht⟩)) = g y := by
        change ((g ∣_ U) ≫ U.ι) _ = ((g ⁻¹ᵁ U).ι ≫ g) _
        rw [morphismRestrict_ι]
      rw [← h2, h1]; rfl
    have hsp := specializes_of_isIso_restrict g U hE (hy ▸ ht) (hy ▸ h)
    have hyE : y ∈ (E.support : Set Y) := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact specializes_iff_mem_closure.mp hsp
    rw [← ha] at hyE
    obtain ⟨w, hw⟩ := hyE
    exact ⟨w, by rw [Scheme.Hom.comp_apply, hw, hy]⟩

/-- **Pull-backs to subvarieties matched over a common biregular open agree.** Let
`f : X ⟶ T ⟵ X⁺ : f⁺` be isomorphisms over an open `U₀ ⊆ T`, and `a : A ⟶ X`, `b : B ⟶ X⁺`
closed immersions of integral normal schemes whose images agree over `U₀`. If the Cartier
divisors `L` on `X` and `L'` on `X⁺` have the same coefficients along prime divisors with the
same image in `U₀`, then the pull-backs `a^*L` and `b^*L'` have the same coefficient along prime
divisors `P` of `A` and `Q` of `B` with the same image in `U₀`: over `U₀` the two closed
subschemes are identified by an isomorphism under which `L` and `L'` agree. -/
private theorem coeff_isPullback_eq_of_isIso_restrict {X Xp T A B : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Xp] [IsLocallyNoetherian Xp] [IsNormal Xp] [CompactSpace Xp]
    [IsIntegral A] [IsLocallyNoetherian A] [IsNormal A] [CompactSpace A]
    [IsIntegral B] [IsLocallyNoetherian B] [IsNormal B] [CompactSpace B]
    (f : X ⟶ T) (fp : Xp ⟶ T) (U₀ : T.Opens) [IsIso (f ∣_ U₀)] [IsIso (fp ∣_ U₀)]
    (a : A ⟶ X) (b : B ⟶ Xp) [IsClosedImmersion a] [IsClosedImmersion b]
    (hab : ∀ t ∈ U₀, t ∈ Set.range (a ≫ f).base ↔ t ∈ Set.range (b ≫ fp).base)
    {L : Divisor X} {L' : Divisor Xp} (hLc : L.IsCartier) (hL'c : L'.IsCartier)
    (hLL' : ∀ (E : MMP.Mori.PrimeDivisor X) (E' : MMP.Mori.PrimeDivisor Xp),
      f E.genericPoint = fp E'.genericPoint → f E.genericPoint ∈ U₀ → L E = L' E')
    {hA : ∀ Z : irreducibleComponents A, a (componentGenericPoint A Z) ∉ L.supp}
    {LA : Divisor A} (hLA : L.IsPullback a hA LA)
    {hB : ∀ Z : irreducibleComponents B, b (componentGenericPoint B Z) ∉ L'.supp}
    {LB : Divisor B} (hLB : L'.IsPullback b hB LB)
    (P : MMP.Mori.PrimeDivisor A) (Q : MMP.Mori.PrimeDivisor B)
    (hPQ : f (a P.genericPoint) = fp (b Q.genericPoint)) (hU : f (a P.genericPoint) ∈ U₀) :
    LA P = LB Q := by
  classical
  set XU := f ⁻¹ᵁ U₀ with hXU
  set XpU := fp ⁻¹ᵁ U₀ with hXpU
  let e : XU.toScheme ≅ XpU.toScheme := asIso (f ∣_ U₀) ≪≫ (asIso (fp ∣_ U₀)).symm
  have he : e.hom ≫ XpU.ι ≫ fp = XU.ι ≫ f := by
    simp only [e, Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, Category.assoc]
    rw [← morphismRestrict_ι fp U₀, IsIso.inv_hom_id_assoc, morphismRestrict_ι]
  have hep : ∀ x, fp (XpU.ι (e.hom x)) = f (XU.ι x) := fun x => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      ← Category.assoc, Category.assoc, he, Scheme.Hom.comp_apply]
  have R3 : ∀ y, U₀.ι ((fp ∣_ U₀) y) = fp (XpU.ι y) := fun y => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hinj : ∀ x₁ x₂ : Xp, fp x₁ ∈ U₀ → fp x₂ ∈ U₀ → fp x₁ = fp x₂ → x₁ = x₂ := by
    intro x₁ x₂ h₁ h₂ h
    obtain ⟨y₁, rfl⟩ : x₁ ∈ Set.range XpU.ι.base := by rwa [Scheme.Opens.range_ι]
    obtain ⟨y₂, rfl⟩ : x₂ ∈ Set.range XpU.ι.base := by rwa [Scheme.Opens.range_ι]
    congr 1
    refine (fp ∣_ U₀).isOpenEmbedding.injective (U₀.ι.isOpenEmbedding.injective ?_)
    rwa [R3, R3]
  have hagen : a (genericPoint A) ∉ L.supp := by
    have := hA (pointComponent (genericPoint A))
    rwa [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at this
  have hbgen : b (genericPoint B) ∉ L'.supp := by
    have := hB (pointComponent (genericPoint B))
    rwa [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at this
  -- the open pieces of `A` and `B`
  set AU := a ⁻¹ᵁ XU with hAU
  set BU := b ⁻¹ᵁ XpU with hBU
  have hPAU : P.genericPoint ∈ AU := hU
  have hQBU : Q.genericPoint ∈ BU := show fp (b Q.genericPoint) ∈ U₀ from hPQ ▸ hU
  haveI : Nonempty AU := ⟨⟨_, hPAU⟩⟩
  haveI : Nonempty BU := ⟨⟨_, hQBU⟩⟩
  haveI : Nonempty XU := ⟨⟨_, hU⟩⟩
  haveI : Nonempty XpU := ⟨⟨_, show fp (b Q.genericPoint) ∈ U₀ from hPQ ▸ hU⟩⟩
  haveI : IsIntegral AU := isIntegral_of_isOpenImmersion AU.ι
  haveI : IsIntegral BU := isIntegral_of_isOpenImmersion BU.ι
  haveI : IsIntegral XU := isIntegral_of_isOpenImmersion XU.ι
  haveI : IsIntegral XpU := isIntegral_of_isOpenImmersion XpU.ι
  haveI : IsNoetherian A := {}
  haveI : IsNoetherian B := {}
  haveI : IsNoetherian X := {}
  haveI : IsNoetherian Xp := {}
  haveI : CompactSpace AU :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  haveI : CompactSpace BU :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  haveI : CompactSpace XU :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  haveI : CompactSpace XpU :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  -- the images of `A` and `B` agree over `U₀`
  have R1 : ∀ y, XpU.ι ((b ∣_ XpU) y) = b (BU.ι y) := fun y => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have R2 : ∀ y, XU.ι ((a ∣_ XU) y) = a (AU.ι y) := fun y => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hr : Set.range (a ∣_ XU ≫ e.hom).base = Set.range (b ∣_ XpU).base := by
    ext z
    have ht : fp (XpU.ι z) ∈ U₀ := z.2
    constructor
    · rintro ⟨w, rfl⟩
      have hz1 : fp (XpU.ι ((a ∣_ XU ≫ e.hom) w)) = (a ≫ f) (AU.ι w) := by
        rw [Scheme.Hom.comp_apply (a ∣_ XU) e.hom, hep, R2, Scheme.Hom.comp_apply]
      obtain ⟨v, hv⟩ := (hab _ ht).mp ⟨AU.ι w, hz1.symm⟩
      have hvU : fp (b v) ∈ U₀ := by
        rwa [← Scheme.Hom.comp_apply, hv]
      obtain ⟨v', hv'⟩ : v ∈ Set.range BU.ι.base := by
        rwa [Scheme.Opens.range_ι]
      refine ⟨v', XpU.ι.isOpenEmbedding.injective ?_⟩
      change XpU.ι ((b ∣_ XpU) v') = _
      rw [R1, hv']
      exact hinj _ _ hvU ht (by rw [← Scheme.Hom.comp_apply, hv])
    · rintro ⟨v, rfl⟩
      have ht' : fp (b (BU.ι v)) ∈ U₀ := v.2
      obtain ⟨w, hw⟩ := (hab _ ht').mpr ⟨BU.ι v, rfl⟩
      have hwU : f (a w) ∈ U₀ := by
        rwa [← Scheme.Hom.comp_apply, hw]
      obtain ⟨w', hw'⟩ : w ∈ Set.range AU.ι.base := by
        rwa [Scheme.Opens.range_ι]
      refine ⟨w', XpU.ι.isOpenEmbedding.injective (hinj _ _ ((a ∣_ XU ≫ e.hom) w').2
        ((b ∣_ XpU) v).2 ?_)⟩
      change fp (XpU.ι ((a ∣_ XU ≫ e.hom) w')) = fp (XpU.ι ((b ∣_ XpU) v))
      rw [Scheme.Hom.comp_apply (a ∣_ XU) e.hom, hep, R2, hw', R1, ← Scheme.Hom.comp_apply a f,
        hw]
  have hker : (a ∣_ XU ≫ e.hom).ker = (b ∣_ XpU).ker := by
    rw [(a ∣_ XU ≫ e.hom).ker_eq_vanishingIdeal_closure_range,
      (b ∣_ XpU).ker_eq_vanishingIdeal_closure_range, hr]
  let j := IsClosedImmersion.lift (b ∣_ XpU) (a ∣_ XU ≫ e.hom) hker.symm.le
  have hj : j ≫ (b ∣_ XpU) = a ∣_ XU ≫ e.hom := IsClosedImmersion.lift_fac _ _ _
  haveI : IsIso j := IsClosedImmersion.isIso_of_ker_eq (a ∣_ XU ≫ e.hom) (b ∣_ XpU) j hj hker
  let k : AU.toScheme ⟶ B := j ≫ BU.ι
  have hk : a ∣_ XU ≫ e.hom ≫ XpU.ι = k ≫ b := by
    simp only [k, Category.assoc]
    rw [← morphismRestrict_ι b XpU, reassoc_of% hj]
  haveI : IsDominant k := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion k
  haveI : IsDominant (e.hom ≫ XpU.ι) :=
    MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  haveI : IsDominant XU.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  haveI : IsDominant AU.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  -- the prime divisor `P₀` of `AU` with closure `P`
  obtain ⟨P₀, hP₀⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff AU.ι P).mpr
    ⟨⟨_, hPAU⟩, rfl⟩
  have hP₀g : AU.ι P₀.genericPoint = P.genericPoint := by
    rw [← hP₀]
    exact (OpenWeilRestriction.genericPoint_primeDivisorMap AU.ι P₀).symm
  have hkP : k P₀.genericPoint = Q.genericPoint := by
    have h1 : b (k P₀.genericPoint) = XpU.ι (e.hom ((a ∣_ XU) P₀.genericPoint)) := by
      rw [← Scheme.Hom.comp_apply k b, ← hk]
      rfl
    have h2 : fp (b (k P₀.genericPoint)) = fp (b Q.genericPoint) := by
      rw [h1, hep, ← hPQ, ← hP₀g]
      change f ((a ∣_ XU) P₀.genericPoint).1 = _
      rw [morphismRestrict_base_coe]
      rfl
    exact b.isClosedEmbedding.injective (hinj _ _ (h2 ▸ hQBU) hQBU h2)
  -- the pull-backs
  have hLAc : LA.IsCartier := by
    rw [← hLA.pullback_eq hLc]; exact hLc.isCartier_pullback a hA
  have hLBc : LB.IsCartier := by
    rw [← hLB.pullback_eq hL'c]; exact hL'c.isCartier_pullback b hB
  obtain ⟨LA', hLA'⟩ := hLAc.exists_isPullback (f := AU.ι)
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant AU.ι LA)
  obtain ⟨LB', hLB'⟩ := hLBc.exists_isPullback (f := k)
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant k LB)
  have hdomX := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant XU.ι L
  obtain ⟨LXU, hLXU⟩ := hLc.exists_isPullback (f := XU.ι) hdomX
  have hLXUc : LXU.IsCartier := by
    rw [← hLXU.pullback_eq hLc]; exact hLc.isCartier_pullback _ hdomX
  obtain ⟨M, hM⟩ := hL'c.exists_isPullback (f := e.hom ≫ XpU.ι)
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant _ L')
  have hMeq : M = LXU := by
    ext E
    rw [MMP.Positivity.coeff_eq_of_isPullback E
        (OpenWeilRestriction.primeDivisorMap (e.hom ≫ XpU.ι) E)
        (OpenWeilRestriction.genericPoint_primeDivisorMap _ E).symm hL'c hM,
      MMP.Positivity.coeff_eq_of_isPullback E (OpenWeilRestriction.primeDivisorMap XU.ι E)
        (OpenWeilRestriction.genericPoint_primeDivisorMap _ E).symm hLc hLXU]
    refine (hLL' _ _ ?_ ?_).symm
    · change f (OpenWeilRestriction.primeDivisorMap XU.ι E).genericPoint =
        fp (OpenWeilRestriction.primeDivisorMap (e.hom ≫ XpU.ι) E).genericPoint
      rw [OpenWeilRestriction.genericPoint_primeDivisorMap,
        OpenWeilRestriction.genericPoint_primeDivisorMap, Scheme.Hom.comp_apply, hep]
    · change f (OpenWeilRestriction.primeDivisorMap XU.ι E).genericPoint ∈ U₀
      rw [OpenWeilRestriction.genericPoint_primeDivisorMap]
      exact (AlgebraicGeometry.PrimeDivisor.genericPoint E).2
  have hM' : L'.IsPullback (e.hom ≫ XpU.ι) _ LXU := hMeq ▸ hM
  have hBN : ∀ Z : irreducibleComponents AU, (a ∣_ XU) (componentGenericPoint AU Z) ∉
      LXU.supp := fun Z hZ => hagen (by
    have h1 := map_mem_supp_of_mem_supp_pullback hLXU hZ
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at h1
    rw [← map_genericPoint_of_isDominant AU.ι]
    convert h1 using 1
    exact (R2 _).symm)
  obtain ⟨N, hN⟩ := hLXUc.exists_isPullback (f := a ∣_ XU) hBN
  have hX1 : ∀ Z : irreducibleComponents AU, (AU.ι ≫ a) (componentGenericPoint AU Z) ∉
      L.supp := fun Z => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply,
      map_genericPoint_of_isDominant AU.ι]
    exact hagen
  have hX2 : ∀ Z : irreducibleComponents AU, (k ≫ b) (componentGenericPoint AU Z) ∉
      L'.supp := fun Z => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply,
      map_genericPoint_of_isDominant k]
    exact hbgen
  have c2 : L.IsPullback (AU.ι ≫ a) hX1 N :=
    MMP.ProgramBaseChange.divisor_isPullback_comp (morphismRestrict_ι a XU) hLXU hN hX1
  have c3 : L.IsPullback (AU.ι ≫ a) hX1 LA' :=
    MMP.ProgramBaseChange.divisor_isPullback_comp rfl hLA hLA' hX1
  have c4 : L'.IsPullback (k ≫ b) hX2 N :=
    MMP.ProgramBaseChange.divisor_isPullback_comp hk hM' hN hX2
  have c5 : L'.IsPullback (k ≫ b) hX2 LB' :=
    MMP.ProgramBaseChange.divisor_isPullback_comp rfl hLB hLB' hX2
  have e1 : LA' P₀ = LA P := MMP.Positivity.coeff_eq_of_isPullback P₀ P hP₀g hLAc hLA'
  have e2 : LB' P₀ = LB Q := MMP.Positivity.coeff_eq_of_isPullback P₀ Q hkP hLBc hLB'
  rw [← e1, ← e2, ← c2.eq hLc c3, c4.eq hL'c c5]

/-- **Restriction of a flip transform to the flipped component.** Let `X ⟶ T ⟵ X⁺` be a real
flip step with `X⁺` `ℚ`-factorial, `S` a prime divisor of `X` with flip transform `S⁺`, and
`ι : T_S ⟶ X`, `ι⁺ : T_{S⁺} ⟶ X⁺` closed immersions onto them. If `C_S = C|_S`, then the flip
transform `C⁺` of `C` restricts to `S⁺` (writing `C = ∑ rⱼ Lⱼ`, a multiple `μⱼ Lⱼ⁺` of each
transform is Cartier and does not contain `S⁺`), and the restrictions agree along prime divisors
of `T_S` and `T_{S⁺}` with the same image in the common biregular locus. -/
private theorem IsRealFlipStep.exists_isRCartierPullback_flipTransform
    {X Xp T TS TSp : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    [IsIntegral TS] [IsLocallyNoetherian TS] [IsNormal TS] [CompactSpace TS] [IsIntegral TSp]
    [IsLocallyNoetherian TSp] [IsNormal TSp] [CompactSpace TSp] {sX : X ⟶ Spec (.of ℂ)}
    {sT : T ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor X} {B : RDivisor X}
    {Kp : Divisor Xp} {Bp : RDivisor Xp} {f : X ⟶ T} {fp : Xp ⟶ T}
    (hflip : IsRealFlipStep sX sT sXp K B Kp Bp f fp) (hXpq : IsQFactorial sXp)
    {S : MMP.Mori.PrimeDivisor X} {Sp : MMP.Mori.PrimeDivisor Xp}
    (hS : flipTransformPrimeDivisor f fp S = some Sp) (ι : TS ⟶ X) (ιp : TSp ⟶ Xp)
    [IsClosedImmersion ι] [IsClosedImmersion ιp] (hι : Set.range ι.base = (S.support : Set X))
    (hιp : Set.range ιp.base = (Sp.support : Set Xp)) {C : RDivisor X} {CS : RDivisor TS}
    (hCS : IsRCartierPullback ι C CS) :
    ∃ CSp : RDivisor TSp, IsRCartierPullback ιp (flipTransform f fp C) CSp ∧
      ∀ (P : MMP.Mori.PrimeDivisor TS) (Q : MMP.Mori.PrimeDivisor TSp),
        f (ι P.genericPoint) = fp (ιp Q.genericPoint) →
        f (ι P.genericPoint) ∈ MMP.Fourfold.commonBiregularLocus f fp → CS P = CSp Q := by
  classical
  have hXp := hXpq.1
  set U := MMP.Fourfold.commonBiregularLocus f fp
  haveI hfU : IsIso (f ∣_ U) := MMP.Fourfold.isBiregular_commonBiregularLocus_left f fp
  haveI hfpU : IsIso (fp ∣_ U) := MMP.Fourfold.isBiregular_commonBiregularLocus_right f fp
  obtain ⟨V, hfV, hfpV, hXV, -⟩ := hflip.exists_opens_isIso
  have hVU : V ≤ U := (MMP.Fourfold.isBiregular_and_isBiregular_iff f fp).mp ⟨hfV, hfpV⟩
  have hft : ∀ Q : MMP.Mori.PrimeDivisor Xp, ∃ P : MMP.Mori.PrimeDivisor X,
      f P.genericPoint = fp Q.genericPoint ∧ ∀ (D : Divisor X),
        flipTransform f fp D Q = D P := fun Q => by
    obtain ⟨P, hPQ, -⟩ := IsRealFlipStep.exists_map_eq hflip hXp Q
    exact ⟨P, hPQ, fun D => IsRealFlipStep.flipTransform_apply_of_map_eq hflip hXp hPQ D⟩
  -- `S⁺` lies over the image of `S`
  have hSSp : fp Sp.genericPoint = f S.genericPoint := by
    obtain ⟨S', hS'1, hS'2⟩ := hft Sp
    have h1 := hS'2 (Finsupp.single S (1 : ℤ))
    rw [MMP.Fourfold.flipTransform_single_of_eq_some hS, Finsupp.single_eq_same,
      Finsupp.single_apply] at h1
    split_ifs at h1 with hSS'
    · rw [← hS'1, hSS']
    · exact absurd h1.symm zero_ne_one
  have hSp' : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
      flipTransform f fp D Sp = D S := fun D =>
    IsRealFlipStep.flipTransform_apply_of_map_eq hflip hXp hSSp.symm D
  have hSU : f S.genericPoint ∈ U :=
    hVU (hXV _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint S).le)
  have hsmul : ∀ (r : ℝ) (D : RDivisor X),
      flipTransform f fp (r • D) = r • flipTransform f fp D := by
    intro r D
    refine Finsupp.ext fun Q => ?_
    obtain ⟨P, hPQ, -⟩ := hft Q
    rw [Finsupp.smul_apply, IsRealFlipStep.flipTransform_apply_of_map_eq hflip hXp hPQ,
      IsRealFlipStep.flipTransform_apply_of_map_eq hflip hXp hPQ, Finsupp.smul_apply]
  have htoR : ∀ L : Divisor X, flipTransform f fp (Divisor.toRDivisor L) =
      Divisor.toRDivisor (flipTransform f fp L) := by
    intro L
    refine Finsupp.ext fun Q => ?_
    obtain ⟨P, hPQ, hP⟩ := hft Q
    rw [IsRealFlipStep.flipTransform_apply_of_map_eq hflip hXp hPQ]
    change (Divisor.toRDivisor L).coeff P = (Divisor.toRDivisor _).coeff Q
    rw [Divisor.coeff_toRDivisor, Divisor.coeff_toRDivisor]
    exact congrArg (fun z : ℤ => (z : ℝ)) (hP L).symm
  -- the generic points of the floor components
  have hjS : ι (genericPoint TS) = S.genericPoint :=
    map_genericPoint_eq_of_range_eq_support ι hι
  have hjSp : ιp (genericPoint TSp) = Sp.genericPoint :=
    map_genericPoint_eq_of_range_eq_support ιp hιp
  -- a presentation of `C`, and Cartier multiples of the transforms
  obtain ⟨m, r, L, L', hL, hCeq, hpb, hCSeq⟩ := hCS
  choose hBL hpbL using hpb
  choose μ hμ hμc using fun j => hXpq.2 (flipTransform f fp (L j))
  have hLS : ∀ j, L j S = 0 := fun j => by
    have h := hBL j (pointComponent (genericPoint TS))
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, hjS, genericPoint_mem_supp_iff] at h
    exact not_not.mp h
  have hBp : ∀ j, ∀ Z : irreducibleComponents TSp,
      ιp (componentGenericPoint TSp Z) ∉ ((μ j : ℤ) • flipTransform f fp (L j)).supp := by
    intro j Z
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, hjSp, genericPoint_mem_supp_iff,
      not_not, Finsupp.smul_apply, hSp', hLS j, smul_zero]
  have hBμ : ∀ j, ∀ Z : irreducibleComponents TS,
      ι (componentGenericPoint TS Z) ∉ ((μ j : ℤ) • L j).supp := by
    intro j Z
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, hjS, genericPoint_mem_supp_iff,
      not_not, Finsupp.smul_apply, hLS j, smul_zero]
  choose Lp' hLp' using fun j => (hμc j).exists_isPullback (f := ιp) (hBp j)
  have hμ0 : ∀ j, (μ j : ℝ) ≠ 0 := fun j => by exact_mod_cast (hμ j).ne'
  refine ⟨∑ j, (r j / μ j) • Divisor.toRDivisor (Lp' j),
    ⟨m, fun j => r j / μ j, fun j => (μ j : ℤ) • flipTransform f fp (L j), Lp', hμc, ?_,
      fun j => ⟨hBp j, hLp' j⟩, rfl⟩, ?_⟩
  · rw [hCeq, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsmul, htoR, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
    congr 1
    push_cast
    field_simp [hμ0 j]
  · intro P Q hPQ hU
    have hab : ∀ t ∈ U, t ∈ Set.range (ι ≫ f).base ↔ t ∈ Set.range (ιp ≫ fp).base :=
      fun t ht => by
        rw [mem_range_comp_iff_specializes ι f U hι hSU ht,
          mem_range_comp_iff_specializes ιp fp U hιp (hSSp ▸ hSU) ht, hSSp]
    have key : ∀ j, ((μ j : ℤ) • L' j) P = Lp' j Q := fun j =>
      coeff_isPullback_eq_of_isIso_restrict f fp U ι ιp hab ((hL j).zsmul (μ j)) (hμc j)
        (fun E E' hEE' _ => by
          rw [Finsupp.smul_apply, Finsupp.smul_apply,
            IsRealFlipStep.flipTransform_apply_of_map_eq hflip hXp hEE'])
        ((hpbL j).zsmul (hL j) (μ j) (hBμ j)) (hLp' j) P Q hPQ hU
    rw [hCSeq, Finsupp.finset_sum_apply, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hk := key j
    rw [Finsupp.smul_apply, smul_eq_mul] at hk
    rw [Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
    change r j * (Divisor.toRDivisor (L' j)).coeff P =
      r j / μ j * (Divisor.toRDivisor (Lp' j)).coeff Q
    rw [Divisor.coeff_toRDivisor, Divisor.coeff_toRDivisor]
    change r j * ((L' j P : ℤ) : ℝ) = r j / μ j * ((Lp' j Q : ℤ) : ℝ)
    rw [← hk]
    push_cast
    field_simp [hμ0 j]

/-- A morphism to an irreducible scheme whose image contains the generic point is dominant. -/
private theorem isDominant_of_map_eq_genericPoint {A B : Scheme.{0}} [IrreducibleSpace B]
    (g : A ⟶ B) {x : A} (h : g x = genericPoint B) : IsDominant g :=
  ⟨Dense.mono (Set.singleton_subset_iff.mpr ⟨x, h⟩)
    (dense_iff_closure_eq.mpr (genericPoint_spec B))⟩

/-- **A finite morphism does not raise the dimension of a closed subset.** If `g` is finite and
maps the closed subset `A` into `T`, then `dim A ≤ dim T`. -/
private theorem topologicalKrullDim_le_of_isFinite' {Y' Y : Scheme.{0}} (g : Y' ⟶ Y)
    [IsFinite g] {A : Set Y'} (hA : IsClosed A) {T : Set Y} (hT : ∀ a ∈ A, g a ∈ T) :
    topologicalKrullDim A ≤ topologicalKrullDim T := by
  haveI : QuasiSober A := hA.isClosedEmbedding_subtypeVal.quasiSober
  let φ : A → T := fun a => ⟨g a.1, hT a.1 a.2⟩
  have hφ : Continuous φ := (g.continuous.comp continuous_subtype_val).subtype_mk _
  refine Order.krullDim_le_of_strictMono (TopologicalSpace.IrreducibleCloseds.map φ hφ)
    fun A₁ B₁ hAB => ?_
  refine lt_of_le_of_ne (TopologicalSpace.IrreducibleCloseds.map_mono hφ hAB.le) fun heq => ?_
  obtain ⟨a, ha⟩ := QuasiSober.sober A₁.isIrreducible A₁.isClosed
  obtain ⟨b, hb⟩ := QuasiSober.sober B₁.isIrreducible B₁.isClosed
  have hfa := ha.image hφ
  have hfb := hb.image hφ
  have hcl : closure (φ '' (A₁ : Set A)) = closure (φ '' (B₁ : Set A)) :=
    congrArg (fun Z : TopologicalSpace.IrreducibleCloseds T => (Z : Set T)) heq
  rw [hcl] at hfa
  have h1 : φ a = φ b := hfa.eq hfb
  have hba : b ⤳ a := hb.specializes (hAB.le ha.mem)
  have hab : b = a := Subtype.ext (MMP.Fourfold.eq_of_specializes_of_isFinite g
    (hba.map continuous_subtype_val) (congrArg Subtype.val h1).symm)
  refine hAB.ne (SetLike.coe_injective ?_)
  rw [← ha.def, ← hb.def, hab]

/-- A closed immersion identifies the closure of a point with the closure of its image. -/
private theorem topologicalKrullDim_closure_map_eq {A X : Scheme.{0}} (a : A ⟶ X)
    [IsClosedImmersion a] (q : A) :
    topologicalKrullDim (closure {a q} : Set X) = topologicalKrullDim (closure {q} : Set A) := by
  have himg : closure ({a q} : Set X) = a '' closure {q} := by
    rw [← Set.image_singleton, a.isClosedEmbedding.closure_image_eq]
  have hmem : ∀ z : (closure {q} : Set A), a z.1 ∈ closure ({a q} : Set X) := fun z => by
    rw [himg]; exact ⟨z.1, z.2, rfl⟩
  let g : (closure {q} : Set A) → (closure {a q} : Set X) :=
    Set.codRestrict (fun z => a z.1) _ hmem
  have hg : IsHomeomorph g := by
    rw [isHomeomorph_iff_isEmbedding_surjective]
    refine ⟨(a.isClosedEmbedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal).codRestrict
      _ hmem, ?_⟩
    rintro ⟨w, hw⟩
    rw [himg] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    exact ⟨⟨z, hz⟩, rfl⟩
  exact (IsHomeomorph.topologicalKrullDim_eq g hg).symm

/-- If `g ≫ h` and the finite morphism `h` are birational, so is `g`: `g` maps the generic point
to the generic point, and `g^* ∘ h^* = (g ≫ h)^*` is onto. -/
private theorem isBirationalMorphism_of_comp_of_isFinite {A B C : Scheme.{0}} [IsIntegral A]
    [IsIntegral B] [IsIntegral C] (g : A ⟶ B) (h : B ⟶ C) [IsFinite h] [LocallyOfFiniteType g]
    (hh : IsBirationalMorphism h) (hgh : IsBirationalMorphism (g ≫ h)) :
    IsBirationalMorphism g := by
  haveI := hh.isDominant
  haveI := hgh.isDominant
  have hg : g (genericPoint A) = genericPoint B := by
    have h1 : h (g (genericPoint A)) = h (genericPoint B) := by
      rw [← Scheme.Hom.comp_apply, map_genericPoint_of_isDominant,
        map_genericPoint_of_isDominant]
    exact (MMP.Fourfold.eq_of_specializes_of_isFinite h (genericPoint_specializes _)
      h1.symm).symm
  haveI : IsDominant g := isDominant_of_map_eq_genericPoint g hg
  refine MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_of_isBirational g
    (AlgebraicGeometry.isBirational_of_surjective_functionFieldMap g fun t => ?_)
  obtain ⟨z, hz⟩ := hgh.functionFieldMap_bijective.2 t
  exact ⟨functionFieldMap h z, by rwa [MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply g h rfl]⟩

/-- The two sides of a real flip step are small morphisms. -/
private theorem IsRealFlipStep.isSmallMorphism {X Xp T : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] {sX : X ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor X} {B : RDivisor X} {Kp : Divisor Xp}
    {Bp : RDivisor Xp} {f : X ⟶ T} {fp : Xp ⟶ T} (hflip : IsRealFlipStep sX sT sXp K B Kp Bp f fp)
    (hXp : IsNormalVariety ℂ sXp) (hfT : f ≫ sT = sX) (hfpT : fp ≫ sT = sXp) :
    MMP.Fourfold.IsSmallMorphism sX sT f ∧ MMP.Fourfold.IsSmallMorphism sXp sT fp := by
  have hneg := hflip.isNegativeExtremalContraction
  obtain ⟨V, hfV, hfpV, hXV, hX'V⟩ := hflip.exists_opens_isIso
  have hVf : V ≤ MMP.Mori.biregularLocus f := MMP.Mori.le_biregularLocus hfV
  have hVfp : V ≤ MMP.Mori.biregularLocus fp := MMP.Mori.le_biregularLocus hfpV
  refine ⟨⟨hneg.isNormalVariety_source, hneg.isNormalVariety_target, hfT,
    hneg.isContraction.isProper, hflip.isBirationalMorphism, ?_⟩,
    ⟨hXp, hneg.isNormalVariety_target, hfpT, hflip.isSmall_flip.isProper,
    hflip.isBirationalMorphism_flip, ?_⟩⟩
  · exact MMP.Flips.le_closedsCodimension_iff_le_coheight.mpr fun x hx =>
      not_lt.mp fun hlt => hx (hVf (hXV x (Order.le_of_lt_succ hlt)))
  · exact MMP.Flips.le_closedsCodimension_iff_le_coheight.mpr fun x hx =>
      not_lt.mp fun hlt => hx (hVfp (hX'V x (Order.le_of_lt_succ hlt)))

/-- If the strict transform of `P` under `φ : A ⤏ B` is `Q`, and `φ` lies over morphisms
`a : A ⟶ T`, `b : B ⟶ T`, then `a(η_P) = b(η_Q)`. -/
private theorem map_genericPoint_eq_of_transformPrimeDivisor_eq_some {A B T : Scheme.{0}}
    [IsReduced A] [IsSeparated (B ↘ Limits.terminal Scheme)]
    [IsSeparated (T ↘ Limits.terminal Scheme)] {φ : A.RationalMap B} {a : A ⟶ T} {b : B ⟶ T}
    (hφ : φ.compHom b = a.toRationalMap) {P : MMP.Mori.PrimeDivisor A}
    {Q : MMP.Mori.PrimeDivisor B}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q) :
    a P.genericPoint = b Q.genericPoint := by
  obtain ⟨hdef, -⟩ := MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h
  obtain ⟨g', hP, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  have hQ := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hP
  have h1 : (g'.compHom b).toRationalMap = a.toPartialMap.toRationalMap := by
    rwa [Scheme.RationalMap.compHom_toRationalMap, hg']
  have h2 := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h1)
  have h4 : g'.hom ≫ b = g'.domain.ι ≫ a := h2
  have h3 : b (g'.hom ⟨P.genericPoint, hP⟩) = a P.genericPoint :=
    congrArg (fun m : g'.domain.toScheme ⟶ T => m ⟨P.genericPoint, hP⟩) h4
  rw [hQ, h3]

/-- Dimension bookkeeping for the exclusion of a Mori fibre space at the end of the program. -/
private theorem false_of_dims {a b c d : WithBot ℕ∞} (h1 : a + 3 = 3) (h2 : b + c = 3)
    (h3 : c ≤ d) (h4 : d < 3) (h5 : b ≤ a) : False := by
  have h34 : c < 3 := lt_of_le_of_lt h3 h4
  have h3c : (3 : WithBot ℕ∞) = ((3 : ℕ∞) : WithBot ℕ∞) := rfl
  rw [h3c] at h1 h2 h34
  induction a using WithBot.recBotCoe with
  | bot => simp at h1
  | coe a =>
  induction b using WithBot.recBotCoe with
  | bot => simp at h2
  | coe b =>
  induction c using WithBot.recBotCoe with
  | bot => simp at h2
  | coe c =>
  rw [← WithBot.coe_add, WithBot.coe_inj] at h1 h2
  rw [WithBot.coe_le_coe] at h5
  rw [WithBot.coe_lt_coe] at h34
  have h3n : (3 : ℕ∞) = ((3 : ℕ) : ℕ∞) := rfl
  rw [h3n] at h1 h2 h34
  induction a using ENat.recTopCoe with
  | top => rw [top_add] at h1; exact absurd h1 (ENat.top_ne_coe _)
  | coe a =>
  induction b using ENat.recTopCoe with
  | top => exact absurd h5 (by simp)
  | coe b =>
  induction c using ENat.recTopCoe with
  | top => exact absurd h34 (by simp)
  | coe c =>
  rw [← ENat.coe_add, ENat.coe_inj] at h1 h2
  rw [ENat.coe_le_coe] at h5
  rw [ENat.coe_lt_coe] at h34
  omega

/-- A subspace of a subspace has at most its dimension. -/
private theorem topologicalKrullDim_mono {Z : Type*} [TopologicalSpace Z] {A B : Set Z}
    (h : A ⊆ B) : topologicalKrullDim A ≤ topologicalKrullDim B :=
  (Topology.IsInducing.of_comp (continuous_inclusion h) continuous_subtype_val
    Topology.IsInducing.subtypeVal).topologicalKrullDim_le

/-- Birational varieties have the same dimension. -/
private theorem topologicalKrullDim_eq_of_isBirational {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sY] [IrreducibleSpace X] [IrreducibleSpace Y] {φ : X.RationalMap Y}
    (hφ : MMP.Mori.RationalMap.IsBirational φ) :
    topologicalKrullDim X = topologicalKrullDim Y := by
  obtain ⟨e, -⟩ := hφ
  rw [AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ X sX _ e.source.isOpen
      e.dense_source.nonempty,
    AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ Y sY _ e.target.isOpen
      e.dense_target.nonempty]
  exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e.iso)).isHomeomorph.topologicalKrullDim_eq

/-- An immersion with dense image into a reduced scheme is an open immersion. -/
private theorem isOpenImmersion_of_isImmersion_of_denseRange {X Y : Scheme.{0}} [IsReduced Y]
    (a : X ⟶ Y) [IsImmersion a] (ha : DenseRange a.base) : IsOpenImmersion a := by
  have hfac := a.liftCoborder_ι
  have hdense : DenseRange a.liftCoborder.base := by
    have h1 := ha.preimage a.coborderRange.ι.isOpenEmbedding.isOpenMap
    have h2 : (⇑a.coborderRange.ι) ⁻¹' Set.range a.base = Set.range a.liftCoborder.base := by
      ext x
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨y, a.coborderRange.ι.isOpenEmbedding.injective ?_⟩
        rw [← hy, ← Scheme.Hom.comp_apply, hfac]
      · rintro ⟨y, rfl⟩
        exact ⟨y, by rw [← Scheme.Hom.comp_apply, hfac]⟩
    rwa [h2] at h1
  haveI : Surjective a.liftCoborder := by
    refine ⟨fun y => ?_⟩
    have hcl : IsClosed (Set.range a.liftCoborder.base) :=
      a.liftCoborder.isClosedEmbedding.isClosed_range
    have : Set.range a.liftCoborder.base = Set.univ := by
      rw [← hcl.closure_eq, hdense.closure_range]
    exact (Set.eq_univ_iff_forall.mp this) y
  haveI := isIso_of_isClosedImmersion_of_surjective a.liftCoborder
  rw [← hfac]
  infer_instance

/-- **The normalization of the image of a subvariety.** Let `a : A ⟶ T` be a morphism from a
normal integral scheme of finite type into a variety, with image in a prime divisor `Γ` of `T`
and `a(η_A) = η_Γ`, which is an immersion over an open `U ∋ η_Γ`. Then `a` factors as `σ ≫ κ`
through the normalization `Γ^ν` of `Γ`, with `κ : Γ^ν ⟶ T` finite and `σ` birational. -/
private theorem exists_isFinite_isBirationalMorphism_factorization {A T : Scheme.{0}}
    [IsIntegral A] [IsNormal A] {sT : T ⟶ Spec (.of ℂ)} (hT : MMP.Mori.IsVariety ℂ sT)
    (a : A ⟶ T) [LocallyOfFiniteType (a ≫ sT)] (Γ : MMP.Mori.PrimeDivisor T)
    (hrange : Set.range a.base ⊆ (Γ.support : Set T))
    (hgen : a (genericPoint A) = Γ.genericPoint) (U : T.Opens) (hΓU : Γ.genericPoint ∈ U)
    [IsImmersion ((a ⁻¹ᵁ U).ι ≫ a)] :
    ∃ (Sg : Scheme.{0}) (_ : IsIntegral Sg) (_ : IsLocallyNoetherian Sg) (_ : IsNormal Sg)
      (σ : A ⟶ Sg) (κ : Sg ⟶ T), IsNormalVariety ℂ (κ ≫ sT) ∧ IsFinite κ ∧
        IsBirationalMorphism σ ∧ σ ≫ κ = a := by
  classical
  haveI : MMP.Mori.IsVariety ℂ sT := hT
  haveI := Γ.integral
  set iZ := Γ.idealSheaf.subschemeι with hiZ
  have hrZ : Set.range iZ.base = (Γ.support : Set T) := Γ.idealSheaf.range_subschemeι
  haveI : MMP.Mori.IsVariety ℂ (iZ ≫ sT) :=
    (MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance,
      inferInstance⟩
  have hker : iZ.ker ≤ a.ker := by
    rw [iZ.ker_eq_vanishingIdeal_closure_range, a.ker_eq_vanishingIdeal_closure_range]
    refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
    change closure (Set.range a.base) ⊆ closure (Set.range iZ.base)
    exact closure_mono (hrZ ▸ hrange)
  let ρ := IsClosedImmersion.lift iZ a hker
  have hρ : ρ ≫ iZ = a := IsClosedImmersion.lift_fac _ _ _
  have hρgen : ρ (genericPoint A) = genericPoint Γ.idealSheaf.subscheme := by
    apply iZ.isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hρ, hgen]
    rfl
  haveI : IsDominant ρ := isDominant_of_map_eq_genericPoint ρ hρgen
  -- `ρ` is birational: over `U` it is an open immersion
  set U' : A.Opens := a ⁻¹ᵁ U
  have hU' : genericPoint A ∈ U' := show a (genericPoint A) ∈ U by rwa [hgen]
  have hU'd : Dense (U' : Set A) := U'.isOpen.dense ⟨_, hU'⟩
  haveI : IsImmersion ((U'.ι ≫ ρ) ≫ iZ) := by rw [Category.assoc, hρ]; infer_instance
  haveI : IsImmersion (U'.ι ≫ ρ) := IsImmersion.of_comp _ iZ
  haveI : IsOpenImmersion (U'.ι ≫ ρ) := by
    refine isOpenImmersion_of_isImmersion_of_denseRange _ ?_
    refine Dense.mono (Set.singleton_subset_iff.mpr ⟨⟨_, hU'⟩, ?_⟩)
      (dense_iff_closure_eq.mpr (genericPoint_spec _))
    exact hρgen
  have hρb : IsBirationalMorphism ρ :=
    MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_of_isOpenImmersion _ U' hU'd
  -- the normalization of `Γ`
  obtain ⟨⟨hZvar, hZnorm, hfin, -, hνbir⟩, -, hlift, -⟩ :=
    MMP.Threefold.normalization_spec (iZ ≫ sT)
  generalize Γ.idealSheaf.subscheme.normalization _ = ν at hZvar hfin hνbir hlift
  generalize Γ.idealSheaf.subscheme.normalizationScheme _ = Sg at ν hZvar hZnorm hlift
  haveI : IsIntegral Sg := hZvar.toIsIntegral
  haveI : LocallyOfFiniteType (ν ≫ iZ ≫ sT) := hZvar.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Sg := LocallyOfFiniteType.isLocallyNoetherian (ν ≫ iZ ≫ sT)
  obtain ⟨σ, hσ, -⟩ := hlift A ρ
  haveI : LocallyOfFiniteType (σ ≫ ν ≫ iZ ≫ sT) := by
    rw [reassoc_of% hσ, reassoc_of% hρ]; infer_instance
  haveI : LocallyOfFiniteType σ := locallyOfFiniteType_of_comp σ (ν ≫ iZ ≫ sT)
  have hσb : IsBirationalMorphism σ :=
    isBirationalMorphism_of_comp_of_isFinite σ ν hνbir (hσ ▸ hρb)
  refine ⟨Sg, inferInstance, inferInstance, hZnorm, σ, ν ≫ iZ,
    ⟨by rw [Category.assoc]; exact hZvar, hZnorm⟩, inferInstance, hσb, ?_⟩
  rw [reassoc_of% hσ, hρ]

/-- Numerical triviality only depends on the structure morphism and the morphism through
their values. -/
private theorem IsNumericallyTrivialOver.of_eq {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {s₁ s₂ : X ⟶ Spec (.of ℂ)} [QuasiCompact s₁] [QuasiCompact s₂] {f₁ f₂ : X ⟶ Y}
    {N : RDivisor X} (hs : s₁ = s₂) (hf : f₁ = f₂) (h : IsNumericallyTrivialOver ℂ s₁ f₁ N) :
    IsNumericallyTrivialOver ℂ s₂ f₂ N := by
  subst hs hf
  exact h

end Helpers

private theorem solution
    {X Xp T Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    (sX : X ⟶ Spec (.of ℂ)) (sXp : Xp ⟶ Spec (.of ℂ)) (sT : T ⟶ Spec (.of ℂ))
    (sZ : Z ⟶ Spec (.of ℂ)) (f : X ⟶ T) (fp : Xp ⟶ T) (g : T ⟶ Z)
    (hfT : f ≫ sT = sX) (hfpT : fp ≫ sT = sXp) (hgZ : g ≫ sZ = sT)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXp : MMP.Mori.IsProjectiveVariety ℂ sXp)
    (hXq : IsQFactorial sX) (hXpq : IsQFactorial sXp)
    (hdim : topologicalKrullDim X = 4) (hdimp : topologicalKrullDim Xp = 4)
    (K : Divisor X) (Kp : Divisor Xp) (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (B : RDivisor X) (Bp : RDivisor Xp)
    (hflip : IsRealFlipStep sX sT sXp K B Kp Bp f fp)
    (hplt : (∀ P, 0 ≤ B.coeff P ∧ B.coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor K + B) ∧
      ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy sX m B E a → 0 < a)
    (C : RDivisor X) (hC : 0 ≤ C) (lam : ℝ) (hlam : 0 < lam)
    (hnef : IsRelativelyNef ℂ sX (f ≫ g) (logCanonicalDivisor K (B + lam • C)))
    (hnull : IsNumericallyTrivialOver ℂ sX f (logCanonicalDivisor K (B + lam • C)))
    (S : MMP.Mori.PrimeDivisor X) (Sp : MMP.Mori.PrimeDivisor Xp)
    (hSB : B.coeff S = 1) (hSC : C.coeff S = 0) (hS : flipTransformPrimeDivisor f fp S = some Sp)
    {TS TSp : Scheme.{0}} [IsIntegral TS] [IsLocallyNoetherian TS] [IsNormal TS]
    [CompactSpace TS] [IsIntegral TSp] [IsLocallyNoetherian TSp] [IsNormal TSp]
    [CompactSpace TSp]
    (ι : TS ⟶ X) (ιp : TSp ⟶ Xp)
    (hι : Set.range ι.base = (S.support : Set X)) (hιp : Set.range ιp.base = (Sp.support : Set Xp))
    (Δ : RDivisor TS) (Δp : RDivisor TSp)
    (hΔ : ∃ (m : ℕ) (t : Fin m → ℝ) (Bk : Fin m → QDivisor X) (Δk : Fin m → QDivisor TS),
      (∀ k, 0 < t k) ∧ ∑ k, t k = 1 ∧ B = ∑ k, t k • QDivisor.toRDivisor (Bk k) ∧
      Δ = ∑ k, t k • QDivisor.toRDivisor (Δk k) ∧ ∀ k, IsAdjunctionStep sX (Bk k) ι (Δk k))
    (hΔp : ∃ (m : ℕ) (t : Fin m → ℝ) (Bk : Fin m → QDivisor Xp) (Δk : Fin m → QDivisor TSp),
      (∀ k, 0 < t k) ∧ ∑ k, t k = 1 ∧ Bp = ∑ k, t k • QDivisor.toRDivisor (Bk k) ∧
      Δp = ∑ k, t k • QDivisor.toRDivisor (Δk k) ∧ ∀ k, IsAdjunctionStep sXp (Bk k) ιp (Δk k))
    (φ : TS.RationalMap TSp) (hφ : MMP.Mori.RationalMap.IsBirational φ)
    (hφf : φ.compHom (ιp ≫ fp) = (ι ≫ f).toRationalMap)
    (hφex : ∀ Q : MMP.Mori.PrimeDivisor TSp, ∃ P : MMP.Mori.PrimeDivisor TS,
      MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q)
    (hφcoeff : ∀ (P : MMP.Mori.PrimeDivisor TS) (Q : MMP.Mori.PrimeDivisor TSp),
      MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q → Δ.coeff P = Δp.coeff Q)
    {V : Scheme.{0}} [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    (h : V ⟶ TS) (hh : IsProjectiveMorphism h) (hhb : IsBirationalMorphism h)
    (hV : MMP.Mori.IsProjectiveVariety ℂ (h ≫ ι ≫ sX)) (hVq : IsQFactorial (h ≫ ι ≫ sX))
    (KV : Divisor V) (hKV : ∃ m : ℕ, KV.IsCanonicalDivisor (h ≫ ι ≫ sX) m)
    (ΔV : RDivisor V) (hΔV : 0 ≤ ΔV) (hΔVklt : IsRealKltPair (h ≫ ι ≫ sX) ΔV)
    (hcrep : ∃ KS : Divisor TS, (∃ m : ℕ, KS.IsCanonicalDivisor (ι ≫ sX) m) ∧
      MMP.Mori.RationalMap.transformDivisor h.toRationalMap KV = KS ∧
      IsRCartierPullback h (logCanonicalDivisor KS Δ) (logCanonicalDivisor KV ΔV))
    (CS : RDivisor TS) (hCS : IsRCartierPullback ι C CS)
    (CV : RDivisor V) (hCV : IsRCartierPullback h CS CV) (hCV0 : 0 ≤ CV)
    (hupklt : IsRealKltPair (h ≫ ι ≫ sX) (ΔV + lam • CV))
    (hA : ∃ A : QDivisor V, (∀ P, 0 ≤ A.coeff P) ∧ A.IsRelativelyBig (h ≫ ι ≫ f ≫ g) ∧
      QDivisor.toRDivisor A ≤ ΔV) :
    ∃ (n : ℕ) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
        (_ : ∀ i, IsIntegral (Y i)) (_ : ∀ i, CompactSpace (Y i))
        (_ : ∀ i, IsLocallyNoetherian (Y i)) (_ : ∀ i, IsNormal (Y i))
        (πY : ∀ i, Y i ⟶ T) (KY : ∀ i, Divisor (Y i)) (ΔY CY : ∀ i, RDivisor (Y i))
        (W : ℕ → Scheme.{0}) (sW : ∀ i, W i ⟶ Spec (.of ℂ))
        (fW : ∀ i, modelSeq V Y i ⟶ W i) (gW : ∀ i, W i ⟶ T) (fpW : ∀ i, Y i ⟶ W i)
        (ψ : ∀ i, (modelSeq V Y i).RationalMap (Y i)),
      -- the models are globally projective `ℚ`-factorial klt models over `T`
      (∀ i ≤ n,
        modelMap (h ≫ ι ≫ f) πY i ≫ sT = modelStr (h ≫ ι ≫ sX) sY i ∧
        MMP.Mori.IsProjectiveVariety ℂ (modelStr (h ≫ ι ≫ sX) sY i) ∧
        IsQFactorial (modelStr (h ≫ ι ≫ sX) sY i) ∧
        (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr (h ≫ ι ≫ sX) sY i) m
          (divisorSeq KV KY i)) ∧
        0 ≤ divisorSeq ΔV ΔY i ∧
        IsRealKltPair (modelStr (h ≫ ι ≫ sX) sY i) (divisorSeq ΔV ΔY i)) ∧
      -- every step is an elementary `(K + Δ)`-negative step with scaling threshold `λ` over `Z`
      (∀ i < n,
        IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr (h ≫ ι ≫ sX) sY i)
          (modelMap (h ≫ ι ≫ f) πY i ≫ g)
          (logCanonicalDivisor (divisorSeq KV KY i) (divisorSeq ΔV ΔY i + t • divisorSeq CV CY i))}
          lam ∧
        MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧ fW i ≫ gW i = modelMap (h ≫ ι ≫ f) πY i ∧
        fpW i ≫ gW i = πY i ∧
        IsNegativeExtremalContraction ℂ (modelStr (h ≫ ι ≫ sX) sY i) (sW i)
          (logCanonicalDivisor (divisorSeq KV KY i) (divisorSeq ΔV ΔY i)) (fW i) ∧
        IsNumericallyTrivialOver ℂ (modelStr (h ≫ ι ≫ sX) sY i) (fW i)
          (logCanonicalDivisor (divisorSeq KV KY i)
            (divisorSeq ΔV ΔY i + lam • divisorSeq CV CY i)) ∧
        ((IsBirationalMorphism (fW i) ∧
            (∃ E : MMP.Mori.PrimeDivisor (modelSeq V Y i),
              (MMP.Mori.exceptionalSet (fW i) : Set (modelSeq V Y i)) = E.support) ∧
            IsIso (fpW i) ∧ IsModificationOf (fW i) (fpW i) (ψ i)) ∨
          IsFlip ℂ (modelStr (h ≫ ι ≫ sX) sY i) (sW i) (sY i)
            (logCanonicalDivisor (divisorSeq KV KY i) (divisorSeq ΔV ΔY i)) (fW i) (fpW i)
            (ψ i)) ∧
        ΔY i = MMP.Mori.RationalMap.transformDivisor (ψ i) (divisorSeq ΔV ΔY i) ∧
        CY i = MMP.Mori.RationalMap.transformDivisor (ψ i) (divisorSeq CV CY i)) ∧
      -- the endpoint maps crepantly to `S⁺`, and its scaling divisor is `(h⁺)^*(C⁺|_{S⁺})`
      ∃ hp : modelSeq V Y n ⟶ TSp,
        IsProjectiveMorphism hp ∧ IsBirationalMorphism hp ∧
        hp ≫ ιp ≫ fp = modelMap (h ≫ ι ≫ f) πY n ∧
        (∃ KSp : Divisor TSp, (∃ m : ℕ, KSp.IsCanonicalDivisor (ιp ≫ sXp) m) ∧
          MMP.Mori.RationalMap.transformDivisor hp.toRationalMap (divisorSeq KV KY n) = KSp ∧
          IsRCartierPullback hp (logCanonicalDivisor KSp Δp)
            (logCanonicalDivisor (divisorSeq KV KY n) (divisorSeq ΔV ΔY n))) ∧
        ∃ CSp : RDivisor TSp, IsRCartierPullback ιp (flipTransform f fp C) CSp ∧
          IsRCartierPullback hp CSp (divisorSeq CV CY n) := by
  classical
  -- the threefold `V` over the contraction base `T`
  have hπV : (h ≫ ι ≫ f) ≫ sT = h ≫ ι ≫ sX := by simp only [Category.assoc, hfT]
  have hTp : MMP.Mori.IsProjectiveVariety ℂ sT := by
    haveI : IsProper f := isProper_of_isProjectiveMorphism f hflip.isProjectiveMorphism
    haveI : IsDominant f := hflip.isBirationalMorphism.isDominant
    exact isProjectiveVariety_of_surjective f hfT hX hflip.isQuasiProjectiveVariety_target
  -- `ι` is a closed immersion onto `S`, so `T_S` and `V` are threefolds
  obtain ⟨mΔ, tΔ, BkΔ, ΔkΔ, htΔ, hsumΔ, -, -, hadjΔ⟩ := id hΔ
  have hm0 : 0 < mΔ := by
    rcases Nat.eq_zero_or_pos mΔ with h0 | h0
    · subst h0; simp at hsumΔ
    · exact h0
  obtain ⟨hTSnv, P0, -, hP0, hci, -⟩ := hadjΔ ⟨0, hm0⟩
  haveI := hci
  haveI := hX.toIsVariety
  haveI : LocallyOfFiniteType sX := inferInstance
  have hdimTS : topologicalKrullDim TS = (3 : ℕ) :=
    topologicalKrullDim_eq_of_range_eq_support (sX := sX) (n := 3) (by rw [hdim]; rfl) S ι hι
  haveI : MMP.Mori.IsVariety ℂ (ι ≫ sX) := hTSnv.1
  haveI : MMP.Mori.IsVariety ℂ (h ≫ ι ≫ sX) := hV.toIsVariety
  have hdimV : topologicalKrullDim V = (3 : ℕ) := by
    rw [← hdimTS]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (ι ≫ sX)
      (h ≫ ι ≫ sX) hhb).symm
  have hK3 : KV.IsCanonicalDivisor (h ≫ ι ≫ sX) 3 := by
    obtain ⟨m, hm⟩ := hKV
    have := hm.topologicalKrullDim_eq
    rw [hdimV] at this
    have hm3 : m = 3 := by exact_mod_cast this.symm
    exact hm3 ▸ hm
  have hΔVc : IsCartierCombination ΔV := isCartierCombination_of_isQFactorial hVq ΔV
  have hCVc : IsCartierCombination (lam • CV) := isCartierCombination_of_isQFactorial hVq _
  have hlev0 : IsRelativelyNef ℂ (h ≫ ι ≫ sX) ((h ≫ ι ≫ f) ≫ g)
        (logCanonicalDivisor KV (ΔV + lam • CV)) ∧
      IsNumericallyTrivialOver ℂ (h ≫ ι ≫ sX) (h ≫ ι ≫ f)
        (logCanonicalDivisor KV (ΔV + lam • CV)) := by
    obtain ⟨KS, hKS, -, hKSpb⟩ := hcrep
    have hLS := level_restrict hXq.1 hXq hdim hK hnef hnull S ι hι hTSnv hΔ hKS hCS
    have hpb : IsRCartierPullback h (logCanonicalDivisor KS (Δ + lam • CS))
        (logCanonicalDivisor KV (ΔV + lam • CV)) := by
      have := MMP.Fourfold.isRCartierPullback_add hKSpb
        (MMP.Fourfold.isRCartierPullback_smul lam hCV)
      simpa only [logCanonicalDivisor, add_assoc] using this
    haveI : IsProper h := isProper_of_isProjectiveMorphism h hh
    haveI := hTSnv.1
    refine ⟨?_, ?_⟩
    · have := IsRelativelyNef.isRCartierPullback (ι ≫ f ≫ g) h hLS.1 hpb
      simpa only [Category.assoc] using this
    · exact IsNumericallyTrivialOver.isRCartierPullback (ι ≫ f) h hLS.2 hpb
  have hnefT : IsRelativelyNef ℂ (h ≫ ι ≫ sX) (h ≫ ι ≫ f)
      (logCanonicalDivisor KV (ΔV + lam • CV)) :=
    isRelativelyNef_of_isNumericallyTrivialOver hlev0.2
  have hAT : ∃ A : QDivisor V, (∀ P, 0 ≤ A.coeff P) ∧ A.IsRelativelyBig (h ≫ ι ≫ f) ∧
      QDivisor.toRDivisor A ≤ ΔV := by
    -- `V ⟶ T` is birational onto its image
    have hbirIm : IsBirationalMorphism (h ≫ ι ≫ f).toImage := by
      obtain ⟨Uh, hUh, hUhi⟩ :=
        MMP.Fourfold.Oai4C1.CommonModel.exists_isOpenImmersion_of_isBirationalMorphism hhb
      obtain ⟨V₀, W₀, hV₀, -, h₀, hiso₀⟩ := hflip.isSmall.exists_isIso
      have hjT : ι (genericPoint TS) = S.genericPoint :=
        map_genericPoint_eq_of_range_eq_support ι hι
      haveI : IsDominant h := hhb.isDominant
      have hhV : h (genericPoint V) = genericPoint TS := map_genericPoint_of_isDominant h
      let O₀ : X.Opens := V₀.compl
      let O₁ : T.Opens := W₀.compl
      have h₀' : O₀ ≤ f ⁻¹ᵁ O₁ := h₀
      haveI : IsIso (f.resLE O₁ O₀ h₀') := hiso₀
      let U' : V.Opens := Uh ⊓ (h ≫ ι) ⁻¹ᵁ O₀
      have hgen : genericPoint V ∈ U' := by
        refine ⟨?_, ?_⟩
        · exact (genericPoint_spec V).mem_open_set_iff Uh.isOpen |>.mpr
            (by simpa using hUh.nonempty)
        · change (h ≫ ι) (genericPoint V) ∈ O₀
          rw [Scheme.Hom.comp_apply, hhV, hjT]
          exact MMP.Flips.genericPoint_notMem_of_two_le_closedsCodimension V₀ hV₀ S
      have hU'd : Dense (U' : Set V) := U'.isOpen.dense ⟨_, hgen⟩
      haveI : IsOpenImmersion (U'.ι ≫ h) := by
        rw [← V.homOfLE_ι (inf_le_left : U' ≤ Uh), Category.assoc]
        infer_instance
      haveI : IsImmersion (U'.ι ≫ h ≫ ι) := by rw [← Category.assoc]; infer_instance
      have hr : Set.range (U'.ι ≫ h ≫ ι).base ⊆ Set.range O₀.ι.base := by
        rintro _ ⟨x, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact x.2.2
      let a := IsOpenImmersion.lift O₀.ι (U'.ι ≫ h ≫ ι) hr
      have ha : a ≫ O₀.ι = U'.ι ≫ h ≫ ι := IsOpenImmersion.lift_fac _ _ _
      haveI : IsImmersion a := by
        haveI : IsImmersion (a ≫ O₀.ι) := by rw [ha]; infer_instance
        exact IsImmersion.of_comp a O₀.ι
      haveI : IsImmersion (U'.ι ≫ (h ≫ ι ≫ f)) := by
        have e : U'.ι ≫ (h ≫ ι ≫ f) = a ≫ f.resLE O₁ O₀ h₀' ≫ O₁.ι := by
          rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc a, ha]
          simp only [Category.assoc]
        rw [e]
        infer_instance
      haveI : IsImmersion (U'.ι ≫ (h ≫ ι ≫ f).toImage) := by
        haveI : IsImmersion ((U'.ι ≫ (h ≫ ι ≫ f).toImage) ≫ (h ≫ ι ≫ f).imageι) := by
          rw [Category.assoc, Scheme.Hom.toImage_imageι]
          infer_instance
        exact IsImmersion.of_comp _ (h ≫ ι ≫ f).imageι
      haveI : IsReduced (h ≫ ι ≫ f).image := inferInstance
      haveI : IsProper h := isProper_of_isProjectiveMorphism h hh
      haveI : IsProper f := isProper_of_isProjectiveMorphism f hflip.isProjectiveMorphism
      haveI : QuasiCompact (h ≫ ι ≫ f) := inferInstance
      haveI : IsOpenImmersion (U'.ι ≫ (h ≫ ι ≫ f).toImage) := by
        refine isOpenImmersion_of_isImmersion_of_denseRange _ ?_
        have hd := ((h ≫ ι ≫ f).toImage).denseRange.dense_image
          (h ≫ ι ≫ f).toImage.base.hom.continuous hU'd
        rw [Scheme.Hom.comp_base, TopCat.coe_comp, DenseRange, Set.range_comp,
          Scheme.Opens.range_ι]
        exact hd
      exact MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_of_isOpenImmersion _ U' hU'd
    obtain ⟨A, hA0, -, hAle⟩ := hA
    refine ⟨A, hA0, ?_, hAle⟩
    exact MMP.Mori.QDivisor.isRelativelyBig_of_isBirationalMorphism_toImage hV hTp hπV hbirIm
      (MMP.Fourfold.isQCartier_of_isQFactorial _ hVq A)
  have hCV0' : ∀ P, 0 ≤ (lam • CV).coeff P := fun P => by
    change 0 ≤ (lam • CV) P
    rw [Finsupp.smul_apply, smul_eq_mul]
    exact mul_nonneg hlam.le (hCV0 P)
  obtain ⟨⟨n, Y, sY, iI, iC, iL, iN, πY, KY, BY, CY, lamS, W, sW, fW, gW, fpW, ψ, hmod, hstep,
      hend⟩, -⟩ :=
    exists_scalingProgram_and_finite_of_isRelativelyBig (h ≫ ι ≫ sX) sT (h ≫ ι ≫ f) hπV hV hTp
      hVq KV hK3 ΔV (lam • CV) (fun P => hΔV P) hCV0' hΔVc hCVc hupklt hnefT hAT
  set CY' : ∀ i, RDivisor (Y i) := fun i => lam⁻¹ • CY i with hCY'
  have hseqC : ∀ i, divisorSeq (lam • CV) CY i = lam • divisorSeq CV CY' i := by
    intro i
    cases i with
    | zero => rfl
    | succ i => exact (smul_inv_smul₀ hlam.ne' (CY i)).symm
  have hΔeff : ∀ i ≤ n, 0 ≤ divisorSeq ΔV BY i := by
    intro i
    induction i with
    | zero => intro _; exact hΔV
    | succ i ih =>
      intro hi
      have := (hstep i (by omega)).2.2.2.2.2.2.2.1
      change 0 ≤ BY i
      rw [this]
      exact transformDivisor_nonneg _ (ih (by omega))
  have hlev : ∀ i ≤ n,
      IsRelativelyNef ℂ (modelStr (h ≫ ι ≫ sX) sY i) (modelMap (h ≫ ι ≫ f) πY i ≫ g)
        (logCanonicalDivisor (divisorSeq KV KY i)
          (divisorSeq ΔV BY i + lam • divisorSeq CV CY' i)) ∧
      IsNumericallyTrivialOver ℂ (modelStr (h ≫ ι ≫ sX) sY i) (modelMap (h ≫ ι ≫ f) πY i)
        (logCanonicalDivisor (divisorSeq KV KY i)
          (divisorSeq ΔV BY i + lam • divisorSeq CV CY' i)) := by
    haveI := iI
    haveI := iC
    haveI := iL
    haveI := iN
    intro i
    induction i with
    | zero => intro _; exact hlev0
    | succ i ih =>
      intro hi
      obtain ⟨hπi, hpi, hqi, hKi, -⟩ := hmod i (by omega)
      obtain ⟨hπi', hpi', hqi', hKi', -⟩ := hmod (i + 1) hi
      obtain ⟨-, -, hfg, hfpg, hneg, -, hcase, hBY, hCY⟩ := hstep i (by omega)
      obtain ⟨hψb, hψT₀, hψE⟩ := step_isBirational_isOver hqi'.1 (gW i) hneg hcase
      have hψT : MMP.Flips.RationalMap.IsOver (modelMap (h ≫ ι ≫ f) πY i) (πY i) (ψ i) := by
        unfold MMP.Flips.RationalMap.IsOver at hψT₀ ⊢
        rw [← hfg, ← hfpg]
        exact hψT₀
      have hl := level_step hpi hqi hpi' hqi' hTp (modelMap (h ≫ ι ≫ f) πY i) (πY i) hπi hπi' g
        hψb hψT hψE hKi hKi' (ih (by omega)).1 (ih (by omega)).2
      have htr : MMP.Mori.RationalMap.transformDivisor (ψ i)
          (divisorSeq ΔV BY i + lam • divisorSeq CV CY' i) = BY i + lam • CY' i := by
        rw [map_add, transformDivisor_smul, ← hBY]
        congr 1
        rw [show CY' i = lam⁻¹ • CY i from rfl, hCY, hseqC i, transformDivisor_smul,
          smul_inv_smul₀ hlam.ne']
      have e : (divisorSeq ΔV BY (i + 1) + lam • divisorSeq CV CY' (i + 1) :
          RDivisor (modelSeq V Y (i + 1))) = MMP.Mori.RationalMap.transformDivisor (ψ i)
            (divisorSeq ΔV BY i + lam • divisorSeq CV CY' i) := htr.symm
      rw [e]
      exact hl
  refine ⟨n, Y, sY, iI, iC, iL, iN, πY, KY, BY, CY', W, sW, fW, gW, fpW, ψ, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨h1, h2, h3, h4, h5⟩ := hmod i hi
    exact ⟨h1, h2, h3, h4, hΔeff i hi, h5⟩
  · intro i hi
    obtain ⟨-, h2, h3, h4, h5, -, h7, h8, h9⟩ := hstep i hi
    refine ⟨?_, h2, h3, h4, h5, ?_, h7, h8, ?_⟩
    · have := (hlev i hi.le).2
      rw [← h3] at this
      exact isLeast_threshold g h3 hlam h5 (hlev i hi.le).1
        (isNumericallyTrivialOver_of_comp this)
    · have := (hlev i hi.le).2
      rw [← h3] at this
      exact isNumericallyTrivialOver_of_comp this
    · change lam⁻¹ • CY i = _
      rw [h9, hseqC i, transformDivisor_smul, inv_smul_smul₀ hlam.ne']
  · -- the endpoint of the program
    haveI := iI
    haveI := iC
    haveI := iL
    haveI := iN
    -- every step is surjective, so all models have the same image in `T`
    have hsurjstep : ∀ i < n, Surjective (fW i) ∧ Surjective (fpW i) := by
      intro i hi
      obtain ⟨-, -, -, -, hneg, -, hcase, -, -⟩ := hstep i hi
      haveI : IsProper (fW i) := hneg.isContraction.isProper
      rcases hcase with ⟨hfb, -, hiso, -⟩ | hfl
      · haveI := hfb.isDominant
        exact ⟨surjective_of_isProper_of_isDominant _, inferInstance⟩
      · haveI := hfl.isSmall_source.isBirationalMorphism.isDominant
        haveI : IsProper (fpW i) := hfl.isProper
        haveI := hfl.isSmall.isBirationalMorphism.isDominant
        exact ⟨surjective_of_isProper_of_isDominant _, surjective_of_isProper_of_isDominant _⟩
    have hrange : ∀ i ≤ n, Set.range (modelMap (h ≫ ι ≫ f) πY i).base =
        Set.range (h ≫ ι ≫ f).base := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ i ih =>
        intro hi
        obtain ⟨-, -, hfg, hfpg, -⟩ := hstep i (by omega)
        obtain ⟨hs1, hs2⟩ := hsurjstep i (by omega)
        rw [← ih (by omega)]
        change Set.range (πY i).base = Set.range (modelMap (h ≫ ι ≫ f) πY i).base
        rw [← hfpg, ← hfg, Scheme.Hom.comp_base, Scheme.Hom.comp_base, TopCat.coe_comp,
          TopCat.coe_comp, Set.range_comp, Set.range_comp, Set.range_eq_univ.mpr hs1.surj,
          Set.range_eq_univ.mpr hs2.surj]
    -- the image `f(S)` of `V` in `T` is a threefold
    have hjT : ι (genericPoint TS) = S.genericPoint :=
      map_genericPoint_eq_of_range_eq_support ι hι
    have hgenV : (h ≫ ι ≫ f) (genericPoint V) = f S.genericPoint := by
      haveI : IsDominant h := hhb.isDominant
      have hhV : h (genericPoint V) = genericPoint TS := map_genericPoint_of_isDominant h
      simp only [Scheme.Hom.comp_apply]
      rw [hhV, hjT]
    haveI := hTp.toIsVariety
    have hdimR : topologicalKrullDim (closure (Set.range (h ≫ ι ≫ f).base)) = (3 : ℕ) := by
      rw [MMP.Flips.closure_range_eq_closure_genericPoint, hgenV]
      haveI : IsIntegral T := hTp.toIsVariety.toIsIntegral
      obtain ⟨W', hiso, hD, -⟩ := MMP.Flips.exists_isIso_morphismRestrict_of_isSmall hflip.isSmall
      have hcoh := MMP.Flips.coheight_map_eq_of_isIso_morphismRestrict f W' (hD S)
      have h2 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sT (f S.genericPoint)
      haveI : IsIntegral T := hTp.toIsVariety.toIsIntegral
      have hdimT : topologicalKrullDim T = ((3 + 1 : ℕ) : WithBot ℕ∞) := by
        rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sT sX
          hflip.isBirationalMorphism, hdim]
        rfl
      rw [hcoh, S.coheight_genericPoint, hdimT] at h2
      exact eq_of_add_one_eq h2
    -- the end is not a Mori fibre space
    have hnefn : IsRelativelyNef ℂ (modelStr (h ≫ ι ≫ sX) sY n) (modelMap (h ≫ ι ≫ f) πY n)
        (logCanonicalDivisor (divisorSeq KV KY n) (divisorSeq ΔV BY n)) := by
      rcases hend with hn | ⟨T₁, sT₁, h₁, gT, -, -, hgT, hneg₁, -, hlt⟩
      · exact hn
      · exfalso
        obtain ⟨hπn, hpn, hqn, hKn, -⟩ := hmod n le_rfl
        have hdimn : topologicalKrullDim (modelSeq V Y n) = (3 : ℕ) := by
          have key : ∀ i ≤ n, topologicalKrullDim (modelSeq V Y i) = (3 : ℕ) := by
            intro i
            induction i with
            | zero => intro _; exact hdimV
            | succ i ih =>
              intro hi
              obtain ⟨-, hpi, -⟩ := hmod i (by omega)
              obtain ⟨-, hpi', hqi', -⟩ := hmod (i + 1) hi
              obtain ⟨-, -, -, -, hneg, -, hcase, -, -⟩ := hstep i (by omega)
              obtain ⟨hψb, -, -⟩ := step_isBirational_isOver hqi'.1 (gW i) hneg hcase
              haveI := hpi.toIsVariety
              haveI := hpi'.toIsVariety
              rw [← topologicalKrullDim_eq_of_isBirational (sX := modelStr (h ≫ ι ≫ sX) sY i)
                (sY := modelStr (h ≫ ι ≫ sX) sY (i + 1)) hψb]
              exact ih (by omega)
          exact key n le_rfl
        haveI := hpn.toIsVariety
        haveI := hneg₁.isNormalVariety_target.1
        have hc₁ := hneg₁.isContraction.comp_eq
        have e1 := MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range
          (modelMap (h ≫ ι ≫ f) πY n) ℂ (modelStr (h ≫ ι ≫ sX) sY n) sT hπn
        have e2 := MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range h₁ ℂ
          (modelStr (h ≫ ι ≫ sX) sY n) sT₁ hc₁
        rw [hrange n le_rfl, hdimR, hdimn] at e1
        rw [hdimn] at e2 hlt
        simp only [Nat.cast_ofNat] at e1 e2 hlt
        refine false_of_dims e1.symm e2.symm (topologicalKrullDim_subspace_le _ _) hlt ?_
        -- the generic fibre of `h₁` lies in that of `π_n`
        have hsub : (⇑h₁ ⁻¹' {h₁ (genericPoint (modelSeq V Y n))}) ⊆
            (⇑(modelMap (h ≫ ι ≫ f) πY n) ⁻¹'
              {(modelMap (h ≫ ι ≫ f) πY n) (genericPoint (modelSeq V Y n))}) := by
          intro y hy
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
          rw [← hgT, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
        rw [(h₁.fiberHomeo _).isHomeomorph.topologicalKrullDim_eq,
          ((modelMap (h ≫ ι ≫ f) πY n).fiberHomeo _).isHomeomorph.topologicalKrullDim_eq]
        exact topologicalKrullDim_mono hsub
    -- the floor component `T_{S⁺}` of the flipped fourfold
    obtain ⟨mΔp, tΔp, BkΔp, ΔkΔp, -, hsumΔp, -, -, hadjΔp⟩ := id hΔp
    have hm0p : 0 < mΔp := by
      rcases Nat.eq_zero_or_pos mΔp with h0 | h0
      · subst h0; simp at hsumΔp
      · exact h0
    obtain ⟨hTSpnv, -, -, -, hcip, -⟩ := hadjΔp ⟨0, hm0p⟩
    haveI := hcip
    haveI := hXp.toIsVariety
    haveI : MMP.Mori.IsVariety ℂ (ιp ≫ sXp) := hTSpnv.1
    have hTSpp : MMP.Mori.IsProjectiveVariety ℂ (ιp ≫ sXp) :=
      (MMP.Mori.isProjectiveVariety_iff ℂ _).mpr ⟨hTSpnv.1,
        (MMP.isProjectiveMorphism_of_isClosedImmersion ιp).comp
          ((MMP.Mori.isProjectiveVariety_iff ℂ sXp).mp hXp).2⟩
    -- `-(K_V + Δ_V)` is nef over `T`
    have hnegV : IsRelativelyNef ℂ (h ≫ ι ≫ sX) (h ≫ ι ≫ f) (-logCanonicalDivisor KV ΔV) := by
      obtain ⟨KS, hKS, -, hKSpb⟩ := hcrep
      obtain ⟨u, v, hpb⟩ := exists_isRCartierPullback_adjunction hXq.1 hXq hdim hK S ι hι hTSnv hΔ
        hKS (MMP.Fourfold.isRCartierPullback_zero ι)
      simp only [add_zero] at hpb
      have hpbn := MMP.Fourfold.isRCartierPullback_smul (-1) hpb
      rw [neg_one_smul, neg_one_smul, neg_add, neg_add] at hpbn
      have hnegX : IsRelativelyNef ℂ sX f (-logCanonicalDivisor K B) :=
        isRelativelyNef_of_isRelativelyAmple
          hflip.isNegativeExtremalContraction.isRelativelyAntiAmple
      have hu := IsNumericallyTrivialOver.smul_add (isNumericallyTrivialOver_principalDivisor
        (k := ℂ) (sX := sX) f u) (isNumericallyTrivialOver_principalDivisor (k := ℂ) (sX := sX) f u)
        (-1) 0
      rw [neg_one_smul, zero_smul, add_zero] at hu
      have hv := IsNumericallyTrivialOver.smul_add (isNumericallyTrivialOver_principalDivisor
        (k := ℂ) (sX := ι ≫ sX) (ι ≫ f) v) (isNumericallyTrivialOver_principalDivisor (k := ℂ)
          (sX := ι ≫ sX) (ι ≫ f) v) (-1) 0
      rw [neg_one_smul, zero_smul, add_zero] at hv
      have hnegS := IsRelativelyNef.of_isRCartierPullback_add f ι hpbn hu hv hnegX
      have hKSn := MMP.Fourfold.isRCartierPullback_smul (-1) hKSpb
      rw [neg_one_smul, neg_one_smul] at hKSn
      haveI : IsProper h := isProper_of_isProjectiveMorphism h hh
      have := IsRelativelyNef.isRCartierPullback (ι ≫ f) h hnegS hKSn
      simpa only [Category.assoc] using this
    -- the initial nef weak model `V ⇢ T_{S⁺}`
    haveI : IsDominant h := hhb.isDominant
    have hW0 : ∃ φ₀ : V.RationalMap TSp,
        IsNefWeakModel (h ≫ ι ≫ sX) (ιp ≫ sXp) sT (h ≫ ι ≫ f) (ιp ≫ fp) KV ΔV φ₀ ∧
        MMP.Mori.RationalMap.transformDivisor φ₀ ΔV = Δp ∧
        ∀ Q : MMP.Mori.PrimeDivisor TSp, ∃ P : MMP.Mori.PrimeDivisor TS,
          MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q ∧
            MMP.Mori.RationalMap.transformDivisor φ₀ CV Q = CS P := by
      haveI : (h.toRationalMap).IsDominant := by
        change (Scheme.Hom.toPartialMap h).toRationalMap.IsDominant
        infer_instance
      haveI : φ.IsDominant := MMP.Fourfold.Crepant.isDominant_of_isBirational hφ
      haveI : IsSeparated sT := hTp.toIsVariety.toIsSeparated
      haveI : IsSeparated (ιp ≫ sXp) := hTSpnv.1.toIsSeparated
      haveI := isSeparated_terminal' (ιp ≫ sXp)
      haveI : IsProper h := isProper_of_isProjectiveMorphism h hh
      have hVn : IsNormalVariety ℂ (h ≫ ι ≫ sX) := ⟨hV.toIsVariety, inferInstance⟩
      have hπSp : (ιp ≫ fp) ≫ sT = ιp ≫ sXp := by simp only [Category.assoc, hfpT]
      have hdimTSp : topologicalKrullDim TSp = (3 : ℕ) :=
        topologicalKrullDim_eq_of_range_eq_support (sX := sXp) (n := 3) (by rw [hdimp]; rfl) Sp ιp
          hιp
      let φ₀ : V.RationalMap TSp := h.toRationalMap.comp φ
      have hφ₀b : MMP.Mori.RationalMap.IsBirational φ₀ := isBirational_comp hhb hφ
      have hφ₀T : MMP.Flips.RationalMap.IsOver (h ≫ ι ≫ f) (ιp ≫ fp) φ₀ := by
        change (h.toRationalMap.comp φ).compHom (ιp ≫ fp) = _
        rw [← Scheme.RationalMap.comp_toRationalMap, Scheme.RationalMap.comp_assoc,
          Scheme.RationalMap.comp_toRationalMap, hφf, Scheme.RationalMap.comp_toRationalMap,
          toRationalMap_compHom']
      have hφ₀s : φ₀.compHom (ιp ≫ sXp) = (h ≫ ι ≫ sX).toRationalMap := by
        have h1 : φ₀.compHom (ιp ≫ fp) = (h ≫ ι ≫ f).toRationalMap := hφ₀T
        rw [← hπSp, ← compHom_compHom', h1, toRationalMap_compHom', hπV]
      -- the strict transform on `V` of a prime divisor of `T_S`
      have hstr : ∀ P : MMP.Mori.PrimeDivisor TS, ∃ PV : MMP.Mori.PrimeDivisor V,
          h PV.genericPoint = P.genericPoint ∧ IsIso (h.stalkMap PV.genericPoint) ∧
          ∀ D : Divisor V, MMP.Mori.RationalMap.transformDivisor h.toRationalMap D P = D PV := by
        intro P
        obtain ⟨PV, h1, h2, h3⟩ :=
          MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hTSnv
            (f := h) hVn hhb P
        exact ⟨PV, h1, h2, fun D => h3 D⟩
      have hφ₀E : ∀ Q : MMP.Mori.PrimeDivisor TSp,
          ∃ PV : MMP.Mori.PrimeDivisor V, ∃ P : MMP.Mori.PrimeDivisor TS,
            MMP.Mori.RationalMap.transformPrimeDivisor φ₀ PV = some Q ∧
            MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q ∧
            h PV.genericPoint = P.genericPoint ∧ IsIso (h.stalkMap PV.genericPoint) ∧
            ∀ D : Divisor V, MMP.Mori.RationalMap.transformDivisor h.toRationalMap D P = D PV := by
        intro Q
        obtain ⟨P, hPQ⟩ := hφex Q
        obtain ⟨PV, h1, h2, h3⟩ := hstr P
        exact ⟨PV, P, transformPrimeDivisor_hom_comp_eq_some h h1 hPQ, hPQ, h1, h2, h3⟩
      -- `φ₀_* Δ_V = Δ⁺`
      obtain ⟨KS, hKS, hKSV, hKSpb⟩ := hcrep
      have hΔ : MMP.Mori.RationalMap.transformDivisor φ₀ ΔV = Δp := by
        ext Q
        obtain ⟨PV, P, hPVQ, hPQ, h1, h2, h3⟩ := hφ₀E Q
        haveI := h2
        refine (MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hPVQ (fun P' hP' =>
          eq_of_transformPrimeDivisor_eq_some hVn hV hTSpnv hTSpp hφ₀b hφ₀s hP' hPVQ) ΔV).trans ?_
        have hc := MMP.Fourfold.coeff_eq_of_isRCartierPullback PV P h1 hKSpb
        have hk : KS P = KV PV := by rw [← hKSV]; exact h3 KV
        have e1 : ΔV PV = (logCanonicalDivisor KV ΔV).coeff PV -
            (Divisor.toRDivisor KV).coeff PV := by
          unfold logCanonicalDivisor
          rw [DivisorWithCoeffs.coeff_add, add_sub_cancel_left]
          rfl
        have e2 : (logCanonicalDivisor KS Δ).coeff P - (Divisor.toRDivisor KS).coeff P =
            Δ.coeff P := by
          unfold logCanonicalDivisor
          rw [DivisorWithCoeffs.coeff_add, add_sub_cancel_left]
        have e3 : (Divisor.toRDivisor KV).coeff PV = (Divisor.toRDivisor KS).coeff P := by
          rw [Divisor.coeff_toRDivisor, Divisor.coeff_toRDivisor]
          exact_mod_cast hk.symm
        rw [e1, hc, e3, e2]
        exact hφcoeff P Q hPQ
      have hφ₀E' : ∀ F : MMP.Mori.PrimeDivisor TSp,
          ¬ MMP.Flips.RationalMap.IsInverseExceptional φ₀ F := fun Q hQ => by
        obtain ⟨PV, -, hPVQ, -⟩ := hφ₀E Q
        exact hQ PV hPVQ
      -- `φ₀_* K_V` is a canonical divisor of `T_{S⁺}`
      obtain ⟨K₀, hK₀⟩ :=
        MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (ιp ≫ sXp) hTSpnv hdimTSp
      have hKφ₀ : Divisor.IsCanonicalDivisor (ιp ≫ sXp) 3
          (MMP.Mori.RationalMap.transformDivisor φ₀ KV) := by
        obtain ⟨W₁, _, _, _, sW₁, p₁, q₁, h₁, hW₁, -, hp₁V, hq₁S, hp₁p, hp₁b, hq₁p, hq₁b, hinv₁,
          hcomp₁⟩ := exists_smooth_common_resolution (h ≫ ι ≫ sX) (ιp ≫ sXp) hVn hTSpnv
            ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hV).2
            ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hTSpp).2 hφ₀b hφ₀s
        haveI : IsProper p₁ := isProper_of_isProjectiveMorphism p₁ hp₁p
        haveI : IsProper q₁ := isProper_of_isProjectiveMorphism q₁ hq₁p
        haveI := hW₁.1
        haveI : CompactSpace W₁ := (quasiCompact_iff_compactSpace sW₁).mp inferInstance
        have hW₁p : IsNormalVariety ℂ (p₁ ≫ h ≫ ι ≫ sX) := hp₁V ▸ hW₁
        have hW₁q : IsNormalVariety ℂ (q₁ ≫ ιp ≫ sXp) := hq₁S ▸ hW₁
        haveI : LocallyOfFiniteType (p₁ ≫ h ≫ ι ≫ sX) := hW₁p.1.toLocallyOfFiniteType
        haveI : LocallyOfFiniteType (q₁ ≫ ιp ≫ sXp) := hW₁q.1.toLocallyOfFiniteType
        haveI : LocallyOfFiniteType (h ≫ ι ≫ sX) := hVn.1.toLocallyOfFiniteType
        haveI : LocallyOfFiniteType (ιp ≫ sXp) := hTSpnv.1.toLocallyOfFiniteType
        exact isCanonicalDivisor_transformDivisor_of_resolution hVn hTSpnv hφ₀E' p₁ q₁ h₁ hW₁p
          hW₁q hp₁b hq₁b hinv₁ hcomp₁ (hp₁V.trans hq₁S.symm) hK3 hK₀
      -- `K_{S⁺} + Δ⁺` is nef over `T`, by adjunction from the `f⁺`-ample `K⁺ + B⁺`
      obtain ⟨u, v, hpb⟩ := exists_isRCartierPullback_adjunction hXpq.1 hXpq hdimp
        hflip.isCanonicalDivisor_flip Sp ιp hιp hTSpnv hΔp ⟨3, hKφ₀⟩
        (MMP.Fourfold.isRCartierPullback_zero ιp)
      simp only [add_zero] at hpb
      have hnefXp : IsRelativelyNef ℂ sXp fp (logCanonicalDivisor Kp Bp) :=
        isRelativelyNef_of_isRelativelyAmple hflip.isRelativelyAmple_flip
      have hnefSp := IsRelativelyNef.of_isRCartierPullback_add fp ιp hpb
        (isNumericallyTrivialOver_principalDivisor (k := ℂ) (sX := sXp) fp u)
        (isNumericallyTrivialOver_principalDivisor (k := ℂ) (sX := ιp ≫ sXp) (ιp ≫ fp) v) hnefXp
      -- `φ₀_* C_V` has the coefficients of `C_S`
      have hC : ∀ Q : MMP.Mori.PrimeDivisor TSp, ∃ P : MMP.Mori.PrimeDivisor TS,
          MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q ∧
            MMP.Mori.RationalMap.transformDivisor φ₀ CV Q = CS P := fun Q => by
        obtain ⟨PV, P, hPVQ, hPQ, h1, h2, -⟩ := hφ₀E Q
        haveI := h2
        refine ⟨P, hPQ, (MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hPVQ (fun P' hP' =>
          eq_of_transformPrimeDivisor_eq_some hVn hV hTSpnv hTSpp hφ₀b hφ₀s hP' hPVQ) CV).trans ?_⟩
        exact MMP.Fourfold.coeff_eq_of_isRCartierPullback PV P h1 hCV
      refine ⟨φ₀, isNefWeakModel_of_isRelativelyNef_neg hVn hV hπV hTSpnv hTSpp hπSp hKV
        (isCartierCombination_of_isQFactorial hVq _) hnegV hφ₀b hφ₀T hφ₀E' ?_, hΔ, hC⟩
      rw [hΔ]
      exact hnefSp
    obtain ⟨φ₀, hW0, hφ₀Δ, hφ₀C⟩ := hW0
    -- the weak model survives every step of the program
    have hprop : ∀ i ≤ n, ∃ φi : (modelSeq V Y i).RationalMap TSp,
        IsNefWeakModel (modelStr (h ≫ ι ≫ sX) sY i) (ιp ≫ sXp) sT (modelMap (h ≫ ι ≫ f) πY i)
          (ιp ≫ fp) (divisorSeq KV KY i) (divisorSeq ΔV BY i) φi ∧
        MMP.Mori.RationalMap.transformDivisor φi (divisorSeq ΔV BY i) = Δp ∧
        MMP.Mori.RationalMap.transformDivisor φi (divisorSeq CV CY' i) =
          MMP.Mori.RationalMap.transformDivisor φ₀ CV := by
      haveI : IsSeparated sT := hTp.toIsVariety.toIsSeparated
      intro i
      induction i with
      | zero => intro _; exact ⟨φ₀, hW0, hφ₀Δ, rfl⟩
      | succ i ih =>
        intro hi
        obtain ⟨φi, hWi, hΔi, hCi⟩ := ih (by omega)
        obtain ⟨hπi', hpi', hqi', hKi', -⟩ := hmod (i + 1) hi
        obtain ⟨-, -, hfg, hfpg, hneg, -, hcase, hBY, hCY⟩ := hstep i (by omega)
        obtain ⟨φ', hW', htr⟩ := IsNefWeakModel.exists_of_programStep hWi hpi' hqi' hπi' (fW i)
          (gW i) (fpW i) (ψ i) hfg hfpg hneg hcase
        have hCYi : CY' i = MMP.Mori.RationalMap.transformDivisor (ψ i) (divisorSeq CV CY' i) := by
          change lam⁻¹ • CY i = _
          rw [hCY, hseqC i, transformDivisor_smul, inv_smul_smul₀ hlam.ne']
        obtain ⟨m₁, hm₁⟩ := hW'.isCanonicalDivisor
        obtain ⟨m₂, hm₂⟩ := hKi'
        have hm : m₂ = m₁ := by
          have e1 := hm₁.topologicalKrullDim_eq
          have e2 := hm₂.topologicalKrullDim_eq
          rw [e1] at e2
          exact_mod_cast e2.symm
        subst hm
        obtain ⟨u, hu⟩ := linearlyEquivalent_of_isCanonicalDivisor' hqi'.1 hm₂ hm₁
        have hKeq : divisorSeq KV KY (i + 1) =
            MMP.Mori.RationalMap.transformDivisor (Y := modelSeq V Y (i + 1)) (ψ i)
              (divisorSeq KV KY i) + MMP.Mori.principalDivisor u := by
          rw [← hu]
          abel
        have hW'' : IsNefWeakModel (modelStr (h ≫ ι ≫ sX) sY (i + 1)) (ιp ≫ sXp) sT
            (modelMap (h ≫ ι ≫ f) πY (i + 1)) (ιp ≫ fp)
            (MMP.Mori.RationalMap.transformDivisor (Y := modelSeq V Y (i + 1)) (ψ i)
              (divisorSeq KV KY i)) (divisorSeq ΔV BY (i + 1)) φ' := by
          have e : divisorSeq ΔV BY (i + 1) =
              MMP.Mori.RationalMap.transformDivisor (Y := modelSeq V Y (i + 1)) (ψ i)
                (divisorSeq ΔV BY i) := hBY
          rw [e]
          exact hW'
        refine ⟨φ', IsNefWeakModel.of_eq_add_principalDivisor hW'' ⟨m₂, hm₂⟩ u hKeq, ?_, ?_⟩
        · exact (congrArg (MMP.Mori.RationalMap.transformDivisor φ') hBY).trans
            ((htr _).trans hΔi)
        · exact (congrArg (MMP.Mori.RationalMap.transformDivisor φ') hCYi).trans
            ((htr _).trans hCi)
    obtain ⟨φn, hWn, hφnΔ, hφnC⟩ := hprop n le_rfl
    -- the endpoint `V⁺ = V_n` and its comparison with `T_{S⁺}`
    obtain ⟨hπn, hpn, hqn, hKn, -⟩ := hmod n le_rfl
    haveI := hpn.toIsVariety
    haveI : IsSeparated sT := hTp.toIsVariety.toIsSeparated
    haveI := isSeparated_terminal' sT
    haveI : IsSeparated (ιp ≫ sXp) := hTSpnv.1.toIsSeparated
    haveI := isSeparated_terminal' (ιp ≫ sXp)
    have hVnn : IsNormalVariety ℂ (modelStr (h ≫ ι ≫ sX) sY n) := ⟨hpn.toIsVariety, inferInstance⟩
    have hπSp : (ιp ≫ fp) ≫ sT = ιp ≫ sXp := by simp only [Category.assoc, hfpT]
    have hIdn := isNefWeakModel_id (sS := sT) hVnn hpn hπn hKn hnefn
    haveI := isSeparated_terminal' (modelStr (h ≫ ι ≫ sX) sY n)
    have hφns : φn.compHom (ιp ≫ sXp) = (modelStr (h ≫ ι ≫ sX) sY n).toRationalMap := by
      have h1 : φn.compHom (ιp ≫ fp) = (modelMap (h ≫ ι ≫ f) πY n).toRationalMap := hWn.isOver
      rw [← hπSp, ← compHom_compHom', h1, toRationalMap_compHom', hπn]
    obtain ⟨W₂, _, _, _, sW₂, p, q, h', hWv, -, hpV, hqS, hpp, hpb, hqp, hqb, hinv, hcomp⟩ :=
      exists_smooth_common_resolution _ _ hVnn hTSpnv
        ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hpn).2
        ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hTSpp).2 hWn.isBirational hφns
    subst hqS
    haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
    haveI : IsProper q := isProper_of_isProjectiveMorphism q hqp
    haveI : IsDominant p := hpb.isDominant
    haveI : IsDominant q := hqb.isDominant
    haveI := hWv.1
    haveI : CompactSpace W₂ := QuasiCompact.compactSpace_of_compactSpace (q ≫ ιp ≫ sXp)
    have hWp : IsNormalVariety ℂ (p ≫ modelStr (h ≫ ι ≫ sX) sY n) := hpV ▸ hWv
    -- `φ_{n*} K_n` is a canonical divisor of `T_{S⁺}`
    obtain ⟨mn, hmn⟩ := hKn
    have hdimTSp : topologicalKrullDim TSp = (mn : ℕ) := by
      rw [← hmn.topologicalKrullDim_eq]
      exact (topologicalKrullDim_eq_of_isBirational (sX := modelStr (h ≫ ι ≫ sX) sY n)
        (sY := ιp ≫ sXp) hWn.isBirational).symm
    obtain ⟨K₀, hK₀⟩ :=
      MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (ιp ≫ sXp) hTSpnv hdimTSp
    haveI : LocallyOfFiniteType (p ≫ modelStr (h ≫ ι ≫ sX) sY n) := hWp.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (ιp ≫ sXp) := hTSpnv.1.toLocallyOfFiniteType
    have hKφn : Divisor.IsCanonicalDivisor (ιp ≫ sXp) mn
        (MMP.Mori.RationalMap.transformDivisor φn (divisorSeq KV KY n)) :=
      isCanonicalDivisor_transformDivisor_of_resolution hVnn hTSpnv hWn.not_isInverseExceptional p
        q h' hWp hWv hpb hqb hinv hcomp hpV hmn hK₀
    -- equal pull-backs of the two adjoints
    have htrid : ∀ {R : Type} [AddCommMonoid R] (N : DivisorWithCoeffs R (modelSeq V Y n)),
        MMP.Mori.RationalMap.transformDivisor (Scheme.RationalMap.id _) N = N := by
      intro R _ N
      haveI := isSeparated_terminal' (modelStr (h ≫ ι ≫ sX) sY n)
      ext Q
      exact MMP.Fourfold.Oai4C1.transformDivisor_apply_of_map_genericPoint (f := 𝟙 _)
        (isBirationalMorphism_of_isIso _) rfl N
    obtain ⟨D₁, hD₁, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p
      (isRelativelyNef_iff.mp hIdn.isRelativelyNef).1
    obtain ⟨D₂, hD₂, -⟩ := MMP.Flips.existsUnique_isRCartierPullback q
      (isRelativelyNef_iff.mp hWn.isRelativelyNef).1
    have hD := (IsNefWeakModel.eq_of_isRCartierPullback_and_isNefModelEquivalent hIdn hWn).1
      (q ≫ ιp ≫ sXp) p q h' hWv.1 hpV rfl hpp hqp hpb hqb
      (MMP.Fourfold.Crepant.compHom_eq_of_isInverse hinv) hcomp hD₁ hD₂
    rw [htrid, htrid, hD] at hD₁
    rw [hφnΔ] at hD₂
    -- the adjoint of `T_{S⁺}` is positive on the curves contracted over `T`
    have hposSp : ∀ C : ProperCurve (ιp ≫ sXp), C.IsContractedBy (ιp ≫ fp) →
        ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor TSp) (x : ℝ),
          IsRIntersectionNumber ℂ (ιp ≫ sXp) (logCanonicalDivisor
            (MMP.Mori.RationalMap.transformDivisor φn (divisorSeq KV KY n)) Δp) r L C x →
              0 < x := by
      intro C hC m r L x hx
      obtain ⟨u, v, hpbuv⟩ := exists_isRCartierPullback_adjunction hXpq.1 hXpq hdimp
        hflip.isCanonicalDivisor_flip Sp ιp hιp hTSpnv hΔp ⟨mn, hKφn⟩
        (MMP.Fourfold.isRCartierPullback_zero ιp)
      simp only [add_zero] at hpbuv
      rw [← one_smul ℝ (Divisor.toRDivisor (MMP.Mori.principalDivisor u)),
        ← one_smul ℝ (Divisor.toRDivisor (MMP.Mori.principalDivisor v))] at hpbuv
      have hposX := pos_add_isNumericallyTrivialOver (k := ℂ) (sX := sXp) (f := fp)
        (isRelativelyNef_iff.mp (isRelativelyNef_of_isRelativelyAmple (sX := sXp)
          hflip.isRelativelyAmple_flip)).1
        (fun C hC _ _ _ _ hx => pos_of_isRelativelyAmple hflip.isRelativelyAmple_flip C hC hx)
        (isNumericallyTrivialOver_principalDivisor (k := ℂ) (sX := sXp) fp u) 1
      have hcN := isCartierCombination_of_isRCartierPullback hpbuv
      have key := pos_add_isNumericallyTrivialOver (k := ℂ) (sX := ιp ≫ sXp) (f := ιp ≫ fp) hcN
        (fun C hC _ _ _ _ hx => pos_of_isRCartierPullback fp ιp hpbuv hposX C hC
          (not_isContractedBy_of_isClosedImmersion ιp C) hx)
        (isNumericallyTrivialOver_principalDivisor (k := ℂ) (sX := ιp ≫ sXp) (ιp ≫ fp) v) (-1)
      refine key C hC m r L x ?_
      rw [neg_one_smul, one_smul, add_neg_cancel_right]
      exact hx
    -- rigidity: `q` factors through `p`
    have hpq : p ≫ modelMap (h ≫ ι ≫ f) πY n = q ≫ ιp ≫ fp :=
      MMP.Fourfold.comp_eq_comp_of_isOver _ _ hWn.isOver p q h' hinv hcomp
    have hcurve : ∀ γ : ProperCurve (q ≫ ιp ≫ sXp), γ.IsContractedBy p → γ.IsContractedBy q :=
      fun γ hγ => isContractedBy_of_isRCartierPullback_eq (modelMap (h ≫ ι ≫ f) πY n) (ιp ≫ fp) p q
        hpq hpV hD₁ hD₂ hposSp γ hγ
    have hO := (MMP.Mori.zariskiMain_of_isProper_of_isBirationalMorphism
      (modelStr (h ≫ ι ≫ sX) sY n) p hpn.toIsVariety hWp.1 hpb).2.2.1
    haveI : ∀ U : (modelSeq V Y n).Opensᵒᵖ, IsIso (p.c.app U) := fun U => hO U.unop
    haveI : IsIso p.c := NatIso.isIso_of_isIso_app p.c
    haveI : Surjective p := surjective_of_isProper_of_isDominant p
    have hWpr : MMP.Mori.IsProjectiveVariety ℂ (q ≫ ιp ≫ sXp) :=
      (MMP.Mori.isProjectiveVariety_iff ℂ _).mpr ⟨hWv.1,
        hqp.comp ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hTSpp).2⟩
    obtain ⟨hp, hphp, -⟩ := MMP.Mori.existsUnique_comp_eq_of_isContractedBy hWpr hpn hTSpp hpp hpV
      rfl hcurve
    have hφhp : hp.toRationalMap = φn := by
      rw [← hcomp, ← hphp, ← compHom_compHom', MMP.Fourfold.Crepant.compHom_eq_of_isInverse hinv,
        toRationalMap_compHom', Category.id_comp]
    have hpS : hp ≫ ιp ≫ sXp = modelStr (h ≫ ι ≫ sX) sY n :=
      ext_of_isDominant_of_isSeparated (Spec (.of ℂ) ↘ Limits.terminal Scheme)
        (Limits.terminal.hom_ext _ _) p (by rw [reassoc_of% hphp, ← hpV])
    have hpb' : IsBirationalMorphism hp := by
      change MMP.Mori.RationalMap.IsBirational hp.toRationalMap
      rw [hφhp]
      exact hWn.isBirational
    haveI : IsDominant hp := hpb'.isDominant
    have hpproj : IsProjectiveMorphism hp := IsProjectiveMorphism.of_comp hp (ιp ≫ sXp)
      (hpS ▸ ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hpn).2)
    have hpπ : hp ≫ ιp ≫ fp = modelMap (h ≫ ι ≫ f) πY n :=
      ext_of_isDominant_of_isSeparated (T ↘ Limits.terminal Scheme)
        (Limits.terminal.hom_ext _ _) p (by rw [reassoc_of% hphp]; exact hpq.symm)
    have hcrepn : IsRCartierPullback hp (logCanonicalDivisor
        (MMP.Mori.RationalMap.transformDivisor φn (divisorSeq KV KY n)) Δp)
        (logCanonicalDivisor (divisorSeq KV KY n) (divisorSeq ΔV BY n)) := by
      have hNc : IsCartierCombination (logCanonicalDivisor
          (MMP.Mori.RationalMap.transformDivisor φn (divisorSeq KV KY n)) Δp) := by
        have := (isRelativelyNef_iff.mp hWn.isRelativelyNef).1
        rwa [hφnΔ] at this
      obtain ⟨G, hG, -⟩ := MMP.Flips.existsUnique_isRCartierPullback hp hNc
      obtain ⟨G', hG', -⟩ := MMP.Flips.existsUnique_isRCartierPullback p
        (isCartierCombination_of_isRCartierPullback hG)
      have h1 := isRCartierPullback_comp' p hp hG hG'
      rw [hphp] at h1
      have h2 : G' = D₂ := MMP.Flips.IsRCartierPullback.eq q h1 hD₂
      rw [h2] at hG'
      have h3 := eq_of_isRCartierPullback_of_isBirationalMorphism hVnn p hWp hpb hG' hD₁
      rw [← h3]
      exact hG
    refine ⟨hp, hpproj, hpb', hpπ,
      ⟨MMP.Mori.RationalMap.transformDivisor hp.toRationalMap (divisorSeq KV KY n),
        ⟨mn, by rw [hφhp]; exact hKφn⟩, rfl, by rw [hφhp]; exact hcrepn⟩, ?_⟩
    -- the restriction `C⁺|_{S⁺}` and its pull-back `G` to `V⁺`
    haveI : IsProper hp := isProper_of_isProjectiveMorphism hp hpproj
    have hXpn : IsNormalVariety ℂ sXp := hXpq.1
    obtain ⟨CSp, hCSp, hCScomp⟩ :=
      IsRealFlipStep.exists_isRCartierPullback_flipTransform hflip hXpq hS ι ιp hι hιp hCS
    refine ⟨CSp, hCSp, ?_⟩
    obtain ⟨G, hG, -⟩ := MMP.Flips.existsUnique_isRCartierPullback hp
      (isCartierCombination_of_isRCartierPullback hCSp)
    suffices hCG : divisorSeq CV CY' n = G by rwa [hCG]
    -- the flip step and its common biregular locus
    have hneg := hflip.isNegativeExtremalContraction
    have hTn := hneg.isNormalVariety_target
    have hfc := hneg.isContraction
    haveI := hfc.isProper
    haveI : IsProper fp := hflip.isSmall_flip.isProper
    have hfb := hflip.isBirationalMorphism
    have hfpb := hflip.isBirationalMorphism_flip
    set U := MMP.Fourfold.commonBiregularLocus f fp with hUdef
    haveI hfU : IsIso (f ∣_ U) := MMP.Fourfold.isBiregular_commonBiregularLocus_left f fp
    haveI hfpU : IsIso (fp ∣_ U) := MMP.Fourfold.isBiregular_commonBiregularLocus_right f fp
    obtain ⟨V₁, hfV₁, hfpV₁, hXV₁, hX'V₁⟩ := hflip.exists_opens_isIso
    have hVU : V₁ ≤ U := (MMP.Fourfold.isBiregular_and_isBiregular_iff f fp).mp ⟨hfV₁, hfpV₁⟩
    have hUfp : U ≤ MMP.Mori.biregularLocus fp :=
      MMP.Mori.le_biregularLocus (MMP.Fourfold.isBiregular_commonBiregularLocus_right f fp)
    -- the level `K⁺ + B⁺ + λ C⁺` is numerically trivial over `T`
    obtain ⟨χ, hχb, hχT, hχtr, hχE⟩ := IsRealFlipStep.exists_flipMap hflip hXpn
    have hnullp := (isNumericallyTrivialOver_transformDivisor_and_pullback_eq sX sXp sT hXq hX
      hXpq hXp hTp f fp hfT hfpT hχb hχT hχE hnull).1
    have e1 : flipTransform f fp (Divisor.toRDivisor K) =
        Divisor.toRDivisor (flipTransform f fp K) := by
      rw [← hχtr, ← hχtr, transformDivisor_toRDivisor]
    have e2 : flipTransform f fp (lam • C) = lam • flipTransform f fp C := by
      rw [← hχtr, ← hχtr, transformDivisor_smul]
    have hnullp' : IsNumericallyTrivialOver ℂ sXp fp
        (logCanonicalDivisor (flipTransform f fp K) (Bp + lam • flipTransform f fp C)) := by
      have e : MMP.Mori.RationalMap.transformDivisor χ (logCanonicalDivisor K (B + lam • C)) =
          logCanonicalDivisor (flipTransform f fp K) (Bp + lam • flipTransform f fp C) := by
        rw [hχtr]
        simp only [logCanonicalDivisor, map_add, e1, e2, hflip.eq_flipTransform]
      rwa [e] at hnullp
    obtain ⟨mK, hmK⟩ := hK
    have hKp : ∃ m : ℕ, Divisor.IsCanonicalDivisor sXp m (flipTransform f fp K) := by
      haveI := hfV₁
      haveI := hfpV₁
      have hmK' : K.IsCanonicalDivisor (f ≫ sT) mK := by rwa [hfT]
      have := MMP.Mori.isCanonicalDivisor_flipTransform_of_isIso_restrict (k := ℂ) hTn
        (by rw [hfT]; exact hXq.1) (by rw [hfpT]; exact hXpn) hfb hfpb V₁ hXV₁ hX'V₁ hmK'
      rw [hfpT] at this
      exact ⟨mK, this⟩
    obtain ⟨u, v, hpbuv⟩ := exists_isRCartierPullback_adjunction hXpq.1 hXpq hdimp hKp Sp ιp hιp
      hTSpnv hΔp ⟨mn, hKφn⟩ (MMP.Fourfold.isRCartierPullback_smul lam hCSp)
    have hSpnull := IsNumericallyTrivialOver.of_isRCartierPullback_add fp ιp hpbuv
      (isNumericallyTrivialOver_principalDivisor (k := ℂ) (sX := sXp) fp u)
      (isNumericallyTrivialOver_principalDivisor (k := ℂ) (sX := ιp ≫ sXp) (ιp ≫ fp) v) hnullp'
    have hpb2 : IsRCartierPullback hp (logCanonicalDivisor
        (MMP.Mori.RationalMap.transformDivisor φn (divisorSeq KV KY n)) (Δp + lam • CSp))
        (logCanonicalDivisor (divisorSeq KV KY n) (divisorSeq ΔV BY n) + lam • G) := by
      have := MMP.Fourfold.isRCartierPullback_add hcrepn
        (MMP.Fourfold.isRCartierPullback_smul lam hG)
      simpa only [logCanonicalDivisor, add_assoc] using this
    have hVnull := IsNumericallyTrivialOver.isRCartierPullback (ιp ≫ fp) hp hSpnull hpb2
    have hVnull' := IsNumericallyTrivialOver.of_eq hpS hpπ hVnull
    -- hence `F = C_{V⁺} - G` is numerically trivial over `T`
    have hF := IsNumericallyTrivialOver.smul_add (hlev n le_rfl).2 hVnull' lam⁻¹ (-lam⁻¹)
    have hFeq : lam⁻¹ • logCanonicalDivisor (divisorSeq KV KY n)
          (divisorSeq ΔV BY n + lam • divisorSeq CV CY' n) +
        (-lam⁻¹) • (logCanonicalDivisor (divisorSeq KV KY n) (divisorSeq ΔV BY n) + lam • G) =
        divisorSeq CV CY' n - G := by
      simp only [logCanonicalDivisor, smul_add, smul_smul, neg_mul, inv_mul_cancel₀ hlam.ne',
        neg_smul, one_smul]
      abel
    rw [hFeq] at hF
    -- the normalization `Σ` of the image of `S⁺` in `T`
    have hjSp : ιp (genericPoint TSp) = Sp.genericPoint :=
      map_genericPoint_eq_of_range_eq_support ιp hιp
    have ht₀U : fp Sp.genericPoint ∈ U :=
      hVU (hX'V₁ _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Sp).le)
    have hct₀ : Order.coheight (fp Sp.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hUfp ht₀U)]
      exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Sp
    obtain ⟨Γ, hΓ⟩ : ∃ Γ : MMP.Mori.PrimeDivisor T, Γ.genericPoint = fp Sp.genericPoint :=
      ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hct₀,
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hct₀⟩
    have hrange : Set.range (ιp ≫ fp).base ⊆ (Γ.support : Set T) := by
      rintro _ ⟨w, rfl⟩
      have hw : ιp w ∈ (Sp.support : Set Xp) := hιp ▸ ⟨w, rfl⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hw ⊢
      change fp (ιp w) ∈ closure {AlgebraicGeometry.PrimeDivisor.genericPoint Γ}
      rw [show AlgebraicGeometry.PrimeDivisor.genericPoint Γ = fp Sp.genericPoint from hΓ]
      exact specializes_iff_mem_closure.mp
        ((specializes_iff_mem_closure.mpr hw).map fp.continuous)
    have hgenΓ : (ιp ≫ fp) (genericPoint TSp) = Γ.genericPoint := by
      rw [Scheme.Hom.comp_apply, hjSp, hΓ]
    haveI : IsImmersion (((ιp ≫ fp) ⁻¹ᵁ U).ι ≫ ιp ≫ fp) := by
      have e : ((ιp ≫ fp) ⁻¹ᵁ U).ι ≫ ιp ≫ fp = (ιp ∣_ (fp ⁻¹ᵁ U)) ≫ (fp ∣_ U) ≫ U.ι := by
        rw [morphismRestrict_ι, morphismRestrict_ι_assoc]
        rfl
      rw [e]
      haveI : IsOpenImmersion ((fp ∣_ U) ≫ U.ι) := inferInstance
      haveI : IsImmersion ((fp ∣_ U) ≫ U.ι) := inferInstance
      haveI : IsClosedImmersion (ιp ∣_ (fp ⁻¹ᵁ U)) := inferInstance
      haveI : IsImmersion (ιp ∣_ (fp ⁻¹ᵁ U)) := inferInstance
      exact IsImmersion.comp (ιp ∣_ (fp ⁻¹ᵁ U)) ((fp ∣_ U) ≫ U.ι)
    haveI : LocallyOfFiniteType ((ιp ≫ fp) ≫ sT) := by
      rw [Category.assoc, hfpT]; exact hTSpnv.1.toLocallyOfFiniteType
    obtain ⟨Sg, _, _, _, σSp, κ, hκnv, hκfin, hσSpb, hσκ⟩ :=
      exists_isFinite_isBirationalMorphism_factorization hTp.toIsVariety (ιp ≫ fp) Γ hrange
        hgenΓ U (hΓ ▸ ht₀U)
    haveI : IsDominant σSp := hσSpb.isDominant
    set σ := hp ≫ σSp with hσdef
    have hσb : IsBirationalMorphism σ :=
      MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hpb' hσSpb
    have hσκ' : σ ≫ κ = modelMap (h ≫ ι ≫ f) πY n := by
      rw [hσdef, Category.assoc, hσκ, hpπ]
    haveI : IsProper (σ ≫ κ) := by rw [hσdef, Category.assoc, hσκ]; infer_instance
    haveI : IsProper σ := IsProper.of_comp σ κ
    have hσs : σ ≫ κ ≫ sT = modelStr (h ≫ ι ≫ sX) sY n := by
      rw [← Category.assoc, hσκ', hπn]
    haveI : MMP.Mori.IsVariety ℂ (κ ≫ sT) := hκnv.1
    haveI : MMP.Mori.IsVariety ℂ (σSp ≫ κ ≫ sT) := by
      rw [reassoc_of% hσκ, hfpT]; exact hTSpnv.1
    have hdimTSp : topologicalKrullDim TSp = ((2 + 1 : ℕ) : WithBot ℕ∞) :=
      topologicalKrullDim_eq_of_range_eq_support (sX := sXp) (n := 3) (by rw [hdimp]; rfl) Sp ιp
        hιp
    have hdimSg : topologicalKrullDim Sg = ((2 + 1 : ℕ) : WithBot ℕ∞) := by
      rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (κ ≫ sT)
        (σSp ≫ κ ≫ sT) hσSpb]
      exact hdimTSp
    have hdimT4 : topologicalKrullDim T = ((3 + 1 : ℕ) : WithBot ℕ∞) := by
      rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sT sX hfb, hdim]
      rfl
    have hdimXp4 : topologicalKrullDim Xp = ((3 + 1 : ℕ) : WithBot ℕ∞) := by rw [hdimp]; rfl
    haveI : IsIntegral T := hTn.1.toIsIntegral
    have hsm := IsRealFlipStep.isSmallMorphism hflip hXpn hfT hfpT
    have hbad := MMP.Fourfold.topologicalKrullDim_badLocusBase_le_one_of_isSmallMorphism hdim hdimp
      hsm.1 hsm.2
    -- `F` vanishes along the prime divisors of `V⁺` which are not exceptional over `Σ`
    have hFzero : ∀ P' : MMP.Mori.PrimeDivisor (modelSeq V Y n),
        ¬ IsExceptionalPrimeDivisor (κ ≫ sT) σ P' → (divisorSeq CV CY' n - G) P' = 0 := by
      intro P' hP'
      have hYσ : IsNormalVariety ℂ (σ ≫ κ ≫ sT) := by rwa [hσs]
      obtain ⟨PS, -, hPS, -⟩ := ProperDivisorOver.exists_primeDivisor_of_not_isExceptional hκnv
        (ProperDivisorOver.mk ⟨_, σ, hYσ, hσb, P'⟩ inferInstance)
        (fun hE => hP' ⟨hYσ, hσb, inferInstance, hE⟩)
      change σ P'.genericPoint = PS.genericPoint at hPS
      set y := σ P'.genericPoint with hy
      have hcy : Order.coheight y = 1 := by
        rw [hPS]; exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint PS
      have hdy : topologicalKrullDim (closure {y} : Set Sg) = (2 : ℕ) := by
        have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (κ ≫ sT) y
        rw [hcy, hdimSg] at h1
        exact eq_of_add_one_eq h1
      set t := κ y with ht
      have hyt : t = modelMap (h ≫ ι ≫ f) πY n P'.genericPoint := by
        rw [ht, hy, ← Scheme.Hom.comp_apply, hσκ']
      have hcl : ∀ z ∈ closure ({y} : Set Sg), κ z ∈ closure ({t} : Set T) := fun z hz =>
        specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hz).map κ.continuous)
      -- `t` lies in the common biregular locus, by the dimension of the bad locus
      have htU : t ∈ U := by
        by_contra htU
        have hsub : ∀ z ∈ closure ({y} : Set Sg),
            κ z ∈ (MMP.Fourfold.badLocusBase f fp : Set T) := fun z hz =>
          closure_minimal (Set.singleton_subset_iff.mpr
            (show t ∈ (MMP.Fourfold.badLocusBase f fp : Set T) from htU))
            (MMP.Fourfold.badLocusBase f fp).isClosed (hcl z hz)
        have h1 := (topologicalKrullDim_le_of_isFinite' κ isClosed_closure hsub).trans hbad
        rw [hdy] at h1
        exact absurd h1 (by norm_num)
      have hdt : ((2 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({t} : Set T)) :=
        hdy ▸ topologicalKrullDim_le_of_isFinite' κ isClosed_closure hcl
      -- the image `q'` of the generic point of `P'` in `T_{S⁺}` has coheight one
      set q' := hp P'.genericPoint with hq'
      have hxt : fp (ιp q') = t := by
        rw [hyt, ← hpπ]; rfl
      have hcx : Order.coheight (ιp q') = Order.coheight t := by
        rw [← hxt]
        exact (MMP.Positivity.coheight_map_of_mem_biregularLocus fp
          (hUfp (by rw [hxt]; exact htU))).symm
      have hd1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sT t
      rw [hdimT4] at hd1
      have hd2 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sXp (ιp q')
      rw [hdimXp4, hcx] at hd2
      have hd3 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (ιp ≫ sXp) q'
      rw [hdimTSp, ← topologicalKrullDim_closure_map_eq ιp q'] at hd3
      obtain ⟨a1, c1, ha1, hc1, hs1⟩ := exists_nat_of_add_eq hd1
      obtain ⟨a2, c2, ha2, hc2, hs2⟩ := exists_nat_of_add_eq hd2
      obtain ⟨a3, c3, ha3, hc3, hs3⟩ := exists_nat_of_add_eq hd3
      have ec : c1 = c2 := by exact_mod_cast hc1.symm.trans hc2
      have ea : a2 = a3 := by exact_mod_cast ha2.symm.trans ha3
      have e2 : 2 ≤ a1 := by rw [ha1] at hdt; exact_mod_cast hdt
      have hq1 : Order.coheight q' ≤ 1 := by
        rw [hc3]; exact_mod_cast (by omega : c3 ≤ 1)
      have hq0 : Order.coheight q' ≠ 0 := by
        intro h0
        have hqg : q' = genericPoint TSp := by
          have hmax := Order.coheight_eq_zero.mp h0
          have hle : q' ≤ genericPoint TSp := genericPoint_specializes q'
          exact (Specializes.antisymm (hmax hle) (genericPoint_specializes q')).eq
        have hκgen : κ (genericPoint Sg) = t := by
          rw [← hxt, hqg]
          change κ (genericPoint Sg) = (ιp ≫ fp) (genericPoint TSp)
          rw [← hσκ, Scheme.Hom.comp_apply, map_genericPoint_of_isDominant σSp]
        have hyg : genericPoint Sg = y :=
          MMP.Fourfold.eq_of_specializes_of_isFinite κ (genericPoint_specializes y) hκgen
        have h00 : Order.coheight y = 0 := by
          rw [← hyg]
          exact Order.coheight_eq_zero.mpr fun z _ => genericPoint_specializes z
        rw [h00] at hcy
        exact zero_ne_one hcy
      have hcq : Order.coheight q' = 1 := le_antisymm hq1 (ENat.one_le_iff_ne_zero.mpr hq0)
      obtain ⟨Q, hQ⟩ : ∃ Q : MMP.Mori.PrimeDivisor TSp, Q.genericPoint = q' :=
        ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne q' hcq,
          AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne q' hcq⟩
      -- `P'` is the strict transform of `Q` on `V⁺`
      have hVnp : IsNormalVariety ℂ (hp ≫ ιp ≫ sXp) := by rwa [hpS]
      obtain ⟨PV, hPV1, hPV2, -⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hTSpnv (f := hp)
          hVnp hpb' Q
      have hφns' : hp.toRationalMap.compHom (ιp ≫ sXp) =
          (modelStr (h ≫ ι ≫ sX) sY n).toRationalMap := by rwa [hφhp]
      have hpbir : MMP.Mori.RationalMap.IsBirational hp.toRationalMap := hpb'
      have hP'Q : MMP.Mori.RationalMap.transformPrimeDivisor hp.toRationalMap P' = some Q :=
        (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff hp P' Q).mpr (by rw [hQ])
      have hPVQ : MMP.Mori.RationalMap.transformPrimeDivisor hp.toRationalMap PV = some Q :=
        (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff hp PV Q).mpr hPV1
      have hPV : PV = P' :=
        eq_of_transformPrimeDivisor_eq_some hVnn hpn hTSpnv hTSpp hpbir hφns' hPVQ hP'Q
      rw [hPV] at hPV1 hPV2
      haveI := hPV2
      have hGP : G P' = CSp Q := MMP.Fourfold.coeff_eq_of_isRCartierPullback P' Q hPV1 hG
      have hCP : divisorSeq CV CY' n P' = MMP.Mori.RationalMap.transformDivisor φ₀ CV Q := by
        rw [← hφnC, ← hφhp]
        exact (MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hP'Q (fun P'' hP'' =>
          eq_of_transformPrimeDivisor_eq_some hVnn hpn hTSpnv hTSpp hpbir hφns' hP'' hP'Q) _).symm
      -- comparison with `C_S` through the induced map `T_S ⇢ T_{S⁺}`
      obtain ⟨P, hPQ, hCVQ⟩ := hφ₀C Q
      have hmap : f (ι P.genericPoint) = fp (ιp Q.genericPoint) := by
        have := map_genericPoint_eq_of_transformPrimeDivisor_eq_some hφf hPQ
        simpa only [Scheme.Hom.comp_apply] using this
      have hmapU : f (ι P.genericPoint) ∈ U := by rwa [hmap, hQ, hxt]
      have hCSQ := hCScomp P Q hmap hmapU
      rw [Finsupp.sub_apply, hCP, hCVQ, hGP, hCSQ, sub_self]
    -- negativity over `Σ`, in both directions
    have hFσ : IsNumericallyTrivialOver ℂ (modelStr (h ≫ ι ≫ sX) sY n) σ
        (divisorSeq CV CY' n - G) :=
      isNumericallyTrivialOver_of_comp (g := κ) (by rw [hσκ']; exact hF)
    have heff : ∀ D : RDivisor (modelSeq V Y n),
        IsNumericallyTrivialOver ℂ (modelStr (h ≫ ι ≫ sX) sY n) σ D →
        (∀ P', ¬ IsExceptionalPrimeDivisor (κ ≫ sT) σ P' → D P' = 0) → D.IsEffective := by
      intro D hD hD0
      have h0 : IsNumericallyTrivialOver ℂ (modelStr (h ≫ ι ≫ sX) sY n) σ
          (0 : RDivisor (modelSeq V Y n)) := by
        have := IsNumericallyTrivialOver.smul_add hD hD 0 0
        rwa [zero_smul, add_zero] at this
      have hc0 : IsCartierCombination (0 : RDivisor Sg) :=
        ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
      exact isEffective_of_isNumericallyEquivalentOver_pullback ℂ (κ ≫ sT) _ hκnv hVnn σ hσs hσb
        hc0 (MMP.Fourfold.isRCartierPullback_zero σ) h0.1
        (isRelativelyNef_of_isNumericallyTrivialOver h0) hD.1 (fun P' hP' => (hD0 P' hP').ge)
        ⟨h0.1, by rw [zero_add]; exact hD.1, fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ =>
          (hD.2.2 C hC m₂ r₂ L₂ x₂ m₁ r₁ L₁ x₁ (by rwa [zero_add] at h₂) h₁).symm⟩
    have hFσn : IsNumericallyTrivialOver ℂ (modelStr (h ≫ ι ≫ sX) sY n) σ
        (-(divisorSeq CV CY' n - G)) := by
      have := IsNumericallyTrivialOver.smul_add hFσ hFσ (-1) 0
      rwa [neg_one_smul, zero_smul, add_zero] at this
    have h1 := heff _ hFσ hFzero
    have h2 := heff _ hFσn (fun P' hP' => by rw [Finsupp.neg_apply, hFzero P' hP', neg_zero])
    rw [← sub_eq_zero]
    ext P'
    have a1 : 0 ≤ (divisorSeq CV CY' n - G) P' := h1 P'
    have a2 : 0 ≤ -((divisorSeq CV CY' n - G) P') := h2 P'
    change (divisorSeq CV CY' n - G) P' = 0
    linarith

end Proof_lem_fourfold_plt_scaling_block

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **A stratum block of a real plt flip has the ambient scaling threshold.** Let
`f : X ⟶ T ⟵ X⁺ : f⁺` be a real flip (`MMP.Fourfold.IsRealFlipStep`) of projective
`ℚ`-factorial complex fourfolds with `(X, B)` plt, over a projective variety `Z` by `g : T ⟶ Z`,
and let `C ≥ 0`, `λ > 0` with `K_X + B + λ C` nef over `Z` and numerically trivial over `f`.
Let `S` be a prime divisor with `coeff_S B = 1`, `coeff_S C = 0`, flip transform `S⁺`, with
normal closed subvarieties `ι : T_S ⟶ X`, `ι⁺ : T_{S⁺} ⟶ X⁺` and real adjunction boundaries `Δ`,
`Δ⁺`, and let `φ : T_S ⤏ T_{S⁺}` be the induced birational map; suppose `φ` extracts no prime
divisor and `coeff_P Δ = coeff_{φ(P)} Δ⁺`. Let `h : V ⟶ T_S` be projective birational from a
`ℚ`-factorial normal projective variety, `Δ_V ≥ 0` klt with `K_V + Δ_V = h^*(K_S + Δ)`,
`C_V = h^*(C|_S) ≥ 0`, `(V, Δ_V + λ C_V)` klt, and `Δ_V ≥ A` for an effective `ℚ`-divisor `A` big
over `Z`. Then there is a finite `(K_V + Δ_V)`-program over `T` with scaling of `C_V`, of
projective models, each step a divisorial contraction or a flip with scaling threshold `λ` for
nefness over `Z`, and a projective birational morphism `h⁺` from its last model to `T_{S⁺}` over
`T` with `K_{V⁺} + Δ_{V⁺} = (h⁺)^*(K_{S⁺} + Δ⁺)` and `C_{V⁺} = (h⁺)^*(C⁺|_{S⁺})`. -/
@[mmp "lem_fourfold_plt_scaling_block"]
public theorem exists_scalingBlock_of_isRealFlipStep_of_isPlt
    {X Xp T Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    (sX : X ⟶ Spec (.of ℂ)) (sXp : Xp ⟶ Spec (.of ℂ)) (sT : T ⟶ Spec (.of ℂ))
    (sZ : Z ⟶ Spec (.of ℂ)) (f : X ⟶ T) (fp : Xp ⟶ T) (g : T ⟶ Z)
    (hfT : f ≫ sT = sX) (hfpT : fp ≫ sT = sXp) (hgZ : g ≫ sZ = sT)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXp : MMP.Mori.IsProjectiveVariety ℂ sXp)
    (hXq : IsQFactorial sX) (hXpq : IsQFactorial sXp)
    (hdim : topologicalKrullDim X = 4) (hdimp : topologicalKrullDim Xp = 4)
    (K : Divisor X) (Kp : Divisor Xp) (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (B : RDivisor X) (Bp : RDivisor Xp)
    (hflip : IsRealFlipStep sX sT sXp K B Kp Bp f fp)
    (hplt : (∀ P, 0 ≤ B.coeff P ∧ B.coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor K + B) ∧
      ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy sX m B E a → 0 < a)
    (C : RDivisor X) (hC : 0 ≤ C) (lam : ℝ) (hlam : 0 < lam)
    (hnef : IsRelativelyNef ℂ sX (f ≫ g) (logCanonicalDivisor K (B + lam • C)))
    (hnull : IsNumericallyTrivialOver ℂ sX f (logCanonicalDivisor K (B + lam • C)))
    (S : MMP.Mori.PrimeDivisor X) (Sp : MMP.Mori.PrimeDivisor Xp)
    (hSB : B.coeff S = 1) (hSC : C.coeff S = 0) (hS : flipTransformPrimeDivisor f fp S = some Sp)
    {TS TSp : Scheme.{0}} [IsIntegral TS] [IsLocallyNoetherian TS] [IsNormal TS]
    [CompactSpace TS] [IsIntegral TSp] [IsLocallyNoetherian TSp] [IsNormal TSp]
    [CompactSpace TSp]
    (ι : TS ⟶ X) (ιp : TSp ⟶ Xp)
    (hι : Set.range ι.base = (S.support : Set X)) (hιp : Set.range ιp.base = (Sp.support : Set Xp))
    (Δ : RDivisor TS) (Δp : RDivisor TSp)
    (hΔ : ∃ (m : ℕ) (t : Fin m → ℝ) (Bk : Fin m → QDivisor X) (Δk : Fin m → QDivisor TS),
      (∀ k, 0 < t k) ∧ ∑ k, t k = 1 ∧ B = ∑ k, t k • QDivisor.toRDivisor (Bk k) ∧
      Δ = ∑ k, t k • QDivisor.toRDivisor (Δk k) ∧ ∀ k, IsAdjunctionStep sX (Bk k) ι (Δk k))
    (hΔp : ∃ (m : ℕ) (t : Fin m → ℝ) (Bk : Fin m → QDivisor Xp) (Δk : Fin m → QDivisor TSp),
      (∀ k, 0 < t k) ∧ ∑ k, t k = 1 ∧ Bp = ∑ k, t k • QDivisor.toRDivisor (Bk k) ∧
      Δp = ∑ k, t k • QDivisor.toRDivisor (Δk k) ∧ ∀ k, IsAdjunctionStep sXp (Bk k) ιp (Δk k))
    (φ : TS.RationalMap TSp) (hφ : MMP.Mori.RationalMap.IsBirational φ)
    (hφf : φ.compHom (ιp ≫ fp) = (ι ≫ f).toRationalMap)
    (hφex : ∀ Q : MMP.Mori.PrimeDivisor TSp, ∃ P : MMP.Mori.PrimeDivisor TS,
      MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q)
    (hφcoeff : ∀ (P : MMP.Mori.PrimeDivisor TS) (Q : MMP.Mori.PrimeDivisor TSp),
      MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q → Δ.coeff P = Δp.coeff Q)
    {V : Scheme.{0}} [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    (h : V ⟶ TS) (hh : IsProjectiveMorphism h) (hhb : IsBirationalMorphism h)
    (hV : MMP.Mori.IsProjectiveVariety ℂ (h ≫ ι ≫ sX)) (hVq : IsQFactorial (h ≫ ι ≫ sX))
    (KV : Divisor V) (hKV : ∃ m : ℕ, KV.IsCanonicalDivisor (h ≫ ι ≫ sX) m)
    (ΔV : RDivisor V) (hΔV : 0 ≤ ΔV) (hΔVklt : IsRealKltPair (h ≫ ι ≫ sX) ΔV)
    (hcrep : ∃ KS : Divisor TS, (∃ m : ℕ, KS.IsCanonicalDivisor (ι ≫ sX) m) ∧
      MMP.Mori.RationalMap.transformDivisor h.toRationalMap KV = KS ∧
      IsRCartierPullback h (logCanonicalDivisor KS Δ) (logCanonicalDivisor KV ΔV))
    (CS : RDivisor TS) (hCS : IsRCartierPullback ι C CS)
    (CV : RDivisor V) (hCV : IsRCartierPullback h CS CV) (hCV0 : 0 ≤ CV)
    (hupklt : IsRealKltPair (h ≫ ι ≫ sX) (ΔV + lam • CV))
    (hA : ∃ A : QDivisor V, (∀ P, 0 ≤ A.coeff P) ∧ A.IsRelativelyBig (h ≫ ι ≫ f ≫ g) ∧
      QDivisor.toRDivisor A ≤ ΔV) :
    ∃ (n : ℕ) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
        (_ : ∀ i, IsIntegral (Y i)) (_ : ∀ i, CompactSpace (Y i))
        (_ : ∀ i, IsLocallyNoetherian (Y i)) (_ : ∀ i, IsNormal (Y i))
        (πY : ∀ i, Y i ⟶ T) (KY : ∀ i, Divisor (Y i)) (ΔY CY : ∀ i, RDivisor (Y i))
        (W : ℕ → Scheme.{0}) (sW : ∀ i, W i ⟶ Spec (.of ℂ))
        (fW : ∀ i, modelSeq V Y i ⟶ W i) (gW : ∀ i, W i ⟶ T) (fpW : ∀ i, Y i ⟶ W i)
        (ψ : ∀ i, (modelSeq V Y i).RationalMap (Y i)),
      -- the models are globally projective `ℚ`-factorial klt models over `T`
      (∀ i ≤ n,
        modelMap (h ≫ ι ≫ f) πY i ≫ sT = modelStr (h ≫ ι ≫ sX) sY i ∧
        MMP.Mori.IsProjectiveVariety ℂ (modelStr (h ≫ ι ≫ sX) sY i) ∧
        IsQFactorial (modelStr (h ≫ ι ≫ sX) sY i) ∧
        (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr (h ≫ ι ≫ sX) sY i) m
          (divisorSeq KV KY i)) ∧
        0 ≤ divisorSeq ΔV ΔY i ∧
        IsRealKltPair (modelStr (h ≫ ι ≫ sX) sY i) (divisorSeq ΔV ΔY i)) ∧
      -- every step is an elementary `(K + Δ)`-negative step with scaling threshold `λ` over `Z`
      (∀ i < n,
        IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr (h ≫ ι ≫ sX) sY i)
          (modelMap (h ≫ ι ≫ f) πY i ≫ g)
          (logCanonicalDivisor (divisorSeq KV KY i) (divisorSeq ΔV ΔY i + t • divisorSeq CV CY i))}
          lam ∧
        MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧ fW i ≫ gW i = modelMap (h ≫ ι ≫ f) πY i ∧
        fpW i ≫ gW i = πY i ∧
        IsNegativeExtremalContraction ℂ (modelStr (h ≫ ι ≫ sX) sY i) (sW i)
          (logCanonicalDivisor (divisorSeq KV KY i) (divisorSeq ΔV ΔY i)) (fW i) ∧
        IsNumericallyTrivialOver ℂ (modelStr (h ≫ ι ≫ sX) sY i) (fW i)
          (logCanonicalDivisor (divisorSeq KV KY i)
            (divisorSeq ΔV ΔY i + lam • divisorSeq CV CY i)) ∧
        ((IsBirationalMorphism (fW i) ∧
            (∃ E : MMP.Mori.PrimeDivisor (modelSeq V Y i),
              (MMP.Mori.exceptionalSet (fW i) : Set (modelSeq V Y i)) = E.support) ∧
            IsIso (fpW i) ∧ IsModificationOf (fW i) (fpW i) (ψ i)) ∨
          IsFlip ℂ (modelStr (h ≫ ι ≫ sX) sY i) (sW i) (sY i)
            (logCanonicalDivisor (divisorSeq KV KY i) (divisorSeq ΔV ΔY i)) (fW i) (fpW i)
            (ψ i)) ∧
        ΔY i = MMP.Mori.RationalMap.transformDivisor (ψ i) (divisorSeq ΔV ΔY i) ∧
        CY i = MMP.Mori.RationalMap.transformDivisor (ψ i) (divisorSeq CV CY i)) ∧
      -- the endpoint maps crepantly to `S⁺`, and its scaling divisor is `(h⁺)^*(C⁺|_{S⁺})`
      ∃ hp : modelSeq V Y n ⟶ TSp,
        IsProjectiveMorphism hp ∧ IsBirationalMorphism hp ∧
        hp ≫ ιp ≫ fp = modelMap (h ≫ ι ≫ f) πY n ∧
        (∃ KSp : Divisor TSp, (∃ m : ℕ, KSp.IsCanonicalDivisor (ιp ≫ sXp) m) ∧
          MMP.Mori.RationalMap.transformDivisor hp.toRationalMap (divisorSeq KV KY n) = KSp ∧
          IsRCartierPullback hp (logCanonicalDivisor KSp Δp)
            (logCanonicalDivisor (divisorSeq KV KY n) (divisorSeq ΔV ΔY n))) ∧
        ∃ CSp : RDivisor TSp, IsRCartierPullback ιp (flipTransform f fp C) CSp ∧
          IsRCartierPullback hp CSp (divisorSeq CV CY n) :=
            by revert X Xp T Z sX sXp sT sZ f fp g hfT hfpT hgZ hZ hX hXp hXq hXpq hdim hdimp K Kp hK B Bp hflip hplt C hC lam hlam hnef hnull S Sp hSB hSC hS TS TSp ι ιp hι hιp Δ Δp hΔ hΔp φ hφ hφf hφex hφcoeff V h hh hhb hV hVq KV hKV ΔV hΔV hΔVklt hcrep CS hCS CV hCV hCV0 hupklt hA; exact Proof_lem_fourfold_plt_scaling_block.solution

end MMP.Fourfold
