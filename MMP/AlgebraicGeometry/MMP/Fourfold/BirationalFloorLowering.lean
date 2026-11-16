module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Singularities.BoundaryLowering
public import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
public import MMP.AlgebraicGeometry.MMP.ScalingProgram.IndependentScalingBoundary
public import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
public import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.Curves.NormalizationLiftInvertible
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
public import MMP.AlgebraicGeometry.MMP.Fourfold.Scaling.BirationalTermination
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.RayLength
public import MMP.AlgebraicGeometry.MMP.Contraction.LineBundleDescent
public import MMP.AlgebraicGeometry.MMP.BasepointFree.UniformRelativeFreeness
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
public import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.Combinatorics.WeightedGraph.ChainDeterminant
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
public import MMP.AlgebraicGeometry.Resolution.StrongResolution.QuasiProjective
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
public import MMP.AlgebraicGeometry.Divisor.PullbackExistence
public import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
public import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
public import MMP.AlgebraicGeometry.Positivity.RelativeKodairaDecomposition

/-!
# A crepant floor-lowering program for nef dlt fourfolds over a birational base

Let `g : X ⟶ Z` be a projective birational morphism of normal projective complex fourfolds, and
let `(X, B)` be a `ℚ`-factorial dlt pair with rational boundary whose adjoint `D = K_X + B` is
nef over `Z`. Put `T = ⌊B⌋`. Then for some rational `t₀ > 0` there is a finite program over `Z`
for the klt perturbation `(X, B - t₀T)`, every step of which is negative for `K + B - t₀T` and
null for the transform of `D`, ending at a model `X'` on which, writing `B'` and `T'` for the
birational transforms of `B` and `T`:

* `(X', B')` is lc and `(X', B' - t₀T')` is klt;
* `D' = K_{X'} + B'` is nef over `Z`, and `D` and `D'` have the same pull-back to a common
  resolution of `X` and `X'`;
* `D' - tT'` is semiample over `Z` for every rational `0 < t ≤ t₀`;
* the birational map `X ⤏ X'` extracts no prime divisor.

## Main results

* `MMP.Fourfold.IsDltPair.exists_relativeDltProgram_sub_smul_roundDown`.

## Implementation notes

The program is a `MMP.Fourfold.RelativeDltProgram` over `Z` for the lowered boundary
`B - t₀⌊B⌋`: its steps are divisorial contractions and flips of `(K_i + B_i - t₀T_i)`-negative
extremal rays `R_i` of `NE̅(X_i/Z)`. The unlowered boundaries `B_i` are the iterated birational
transforms of `B`; nullity of a step for `D` is the vanishing of the form `z ↦ (K_i + B_i) · z`
on `R_i`. The map `φ : X ⤏ X'` is the birational map over `Z`, which is unique since `Z` is
birational to `X'`; `B' = φ_* B` and `T' = φ_* T`. The canonical divisor `K'` of `X'` is the
program's, and the common resolution (`MMP.Fourfold.IsLogComparisonResolution`) pins it to be
cut out by the same rational top form as `K`; identical pull-backs is `GX = GY` there.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], 3.31
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Proof_lem_fourfold_nef_dlt_birational_floor_lowering

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Fourfold MMP.Mori MMP.Flips

/-- Lowering the reduced part of a `ℚ`-factorial dlt boundary by any `0 < t ≤ 1` gives a klt
pair: the lowered boundary is effective, at most `B`, and has every coefficient below one. -/
private theorem isKltPair_sub_smul_roundDown {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hQ : IsQFactorial sX)
    {B : QDivisor X} (hB : MMP.Intersection.IsDltPair sX B) {t : ℚ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) :
    IsKltPair sX (B - t • Divisor.toQDivisor B.roundDown) := by
  have hcoeff : ∀ P, (B - t • Divisor.toQDivisor B.roundDown).coeff P =
      B.coeff P - t * ⌊B.coeff P⌋ := by
    intro P
    simp
  have h0 : ∀ P, 0 ≤ B.coeff P := hB.1.2.1
  have h1 : ∀ P, B.coeff P ≤ 1 := hB.2.1
  have hfl : ∀ P, (⌊B.coeff P⌋ : ℚ) = if B.coeff P = 1 then 1 else 0 := by
    intro P
    split_ifs with h
    · simp [h]
    · have : B.coeff P < 1 := lt_of_le_of_ne (h1 P) h
      rw [Int.floor_eq_zero_iff.mpr ⟨h0 P, this⟩]
      simp
  refine MMP.Intersection.IsDltPair.isKltPair_of_forall_coeff_lt_one
    (MMP.Intersection.IsDltPair.of_le sX hB (fun P => ?_) (fun P => ?_)
      (isQCartier_of_isQFactorial sX hQ _)) (fun P => ?_)
  · change (0 : ℚ) ≤ (B - t • Divisor.toQDivisor B.roundDown).coeff P
    rw [hcoeff, hfl]
    split_ifs with h
    · rw [h]; linarith
    · simpa using h0 P
  · change (B - t • Divisor.toQDivisor B.roundDown).coeff P ≤ B.coeff P
    rw [hcoeff, hfl]
    split_ifs <;> simp; linarith
  · rw [hcoeff, hfl]
    split_ifs with h
    · rw [h]; linarith
    · simpa using lt_of_le_of_ne (h1 P) h

/-- The iterated birational transforms `D₀ = D`, `D_{i+1} = (φ_i)_* D_i` of a divisor along a
sequence of rational maps `φ_i : X_i ⤏ X_{i+1}`. -/
private noncomputable def iterTransform {R : Type*} [AddCommMonoid R] {X : Scheme.{0}}
    {Y : ℕ → Scheme.{0}} (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i))
    (D : DivisorWithCoeffs R X) : ∀ i, DivisorWithCoeffs R (modelSeq X Y i)
  | 0 => D
  | i + 1 => MMP.Mori.RationalMap.transformDivisor (φ i) (iterTransform φ D i)

/-- Replacing the last divisor of a sequence leaves the earlier terms unchanged. -/
private theorem divisorSeq_ite_of_lt {R : Type*} [Zero R] {X : Scheme.{0}} {Y : ℕ → Scheme.{0}}
    (D : DivisorWithCoeffs R X) (E : ∀ i, DivisorWithCoeffs R (Y i))
    (F : ∀ i, DivisorWithCoeffs R (modelSeq X Y i)) {n j : ℕ} (hj : j < n) :
    divisorSeq D (fun i => if i + 1 = n then F (i + 1) else E i) j = divisorSeq D E j := by
  cases j with
  | zero => rfl
  | succ i => exact if_neg (by omega)

/-- The last divisor of a sequence with replaced last term. -/
private theorem divisorSeq_ite_self {R : Type*} [Zero R] {X : Scheme.{0}} {Y : ℕ → Scheme.{0}}
    (D : DivisorWithCoeffs R X) (E : ∀ i, DivisorWithCoeffs R (Y i))
    (F : ∀ i, DivisorWithCoeffs R (modelSeq X Y i)) (hF : F 0 = D) (n : ℕ) :
    divisorSeq D (fun i => if i + 1 = n then F (i + 1) else E i) n = F n := by
  cases n with
  | zero => exact hF.symm
  | succ i => exact if_pos rfl

/-- A sequence of divisors is the sequence of its tail, started at its head. -/
private theorem divisorSeq_succ {R : Type*} [Zero R] {X : Scheme.{0}} {Y : ℕ → Scheme.{0}}
    {D : DivisorWithCoeffs R X} (F : ∀ i, DivisorWithCoeffs R (modelSeq X Y i)) (hF : F 0 = D)
    (j : ℕ) : divisorSeq D (fun i => F (i + 1)) j = F j := by
  cases j with
  | zero => exact hF.symm
  | succ i => rfl

/-- The invariants carried along the floor-lowering program on a model `X₁` over `Z`, for the
transforms `K₁`, `B₁`, `T₁` of `K`, `B`, `⌊B⌋` and the real boundary `Δ₁` of the scaling
program: `m D₁` is Cartier for `D₁ = K₁ + B₁`, `K₁` is canonical, `D₁` is nef over `Z`,
`(X₁, B₁ - T₁)` is klt, `(X₁, B₁)` is lc, `0 ≤ T₁ ≤ B₁`, the coefficients of `B₁ - T₁` are
less than one and `Δ₁ = B₁ - t₀ T₁`. -/
private structure FloorInv {X₁ Z : Scheme.{0}} [IsIntegral X₁] [CompactSpace X₁]
    [IsLocallyNoetherian X₁] [IsNormal X₁] (s₁ : X₁ ⟶ Spec (.of ℂ)) (π₁ : X₁ ⟶ Z) (m : ℕ)
    (t₀ : ℚ) (K₁ : Divisor X₁) (B₁ T₁ : QDivisor X₁) (Δ₁ : RDivisor X₁) : Prop where
  exists_cartier : ∃ Dm : Divisor X₁, Dm.IsCartier ∧
    Divisor.toQDivisor Dm = (m : ℤ) • (Divisor.toQDivisor K₁ + B₁)
  isCanonicalDivisor : K₁.IsCanonicalDivisor s₁ 4
  isRelativelyNef : QDivisor.IsRelativelyNef s₁ π₁ (Divisor.toQDivisor K₁ + B₁)
  isKltPair_sub : IsKltPair s₁ (B₁ - T₁)
  isLogCanonicalPair : MMP.Intersection.IsLogCanonicalPair s₁ B₁
  floor_nonneg : ∀ P, 0 ≤ T₁.coeff P
  coeff_bounds : ∀ P, 0 ≤ (B₁ - T₁).coeff P ∧ (B₁ - T₁).coeff P < 1 ∧ B₁.coeff P ≤ 1
  toRDivisor_eq : QDivisor.toRDivisor (B₁ - t₀ • T₁) = Δ₁

/-- The birational transform of divisors commutes with regarding a `ℚ`-divisor as an
`ℝ`-divisor. -/
private theorem transformDivisor_toRDivisor {X Y : Scheme.{0}} (φ : X.RationalMap Y)
    (D : QDivisor X) :
    MMP.Mori.RationalMap.transformDivisor φ (QDivisor.toRDivisor D) =
      QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor φ D) := by
  classical
  have hs : ∀ {Z : Scheme.{0}} (Q : MMP.Mori.PrimeDivisor Z) (r : ℚ),
      QDivisor.toRDivisor (Finsupp.single Q r) = Finsupp.single Q (r : ℝ) :=
    fun Q r => Finsupp.mapRange_single (hf := map_zero (Rat.castHom ℝ).toAddMonoidHom)
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add D D' h h' => simp only [map_add, h, h']
  | single P r =>
    rw [hs, MMP.Mori.RationalMap.transformDivisor_single,
      MMP.Mori.RationalMap.transformDivisor_single]
    cases MMP.Mori.RationalMap.transformPrimeDivisor φ P with
    | none => exact (map_zero _).symm
    | some E => exact (hs E r).symm

/-- The adjoint `K + Δ` of a `ℚ`-boundary, regarded as an `ℝ`-divisor. -/
private theorem logCanonicalDivisor_toRDivisor {X : Scheme.{0}} (K : Divisor X) (Δ : QDivisor X) :
    logCanonicalDivisor K (QDivisor.toRDivisor Δ) =
      QDivisor.toRDivisor (Divisor.toQDivisor K + Δ) := by
  rw [logCanonicalDivisor, map_add, QDivisor.toRDivisor_toQDivisor]

/-- On a `ℚ`-factorial variety, an effective `ℚ`-boundary which is klt as a real boundary is
klt. -/
private theorem isKltPair_of_isRealKltPair {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {s : X ⟶ Spec (.of ℂ)} (hQ : IsQFactorial s)
    {Δ : QDivisor X} (h0 : ∀ P, 0 ≤ Δ.coeff P) (h : IsRealKltPair s (QDivisor.toRDivisor Δ)) :
    IsKltPair s Δ := by
  obtain ⟨hX, -, ⟨n, K, hK, -⟩, hpos⟩ := h
  exact ⟨⟨inferInstance, inferInstance, ⟨hX, n, K, hK, isQCartier_of_isQFactorial s hQ _⟩, h0⟩,
    hpos⟩

/-- An effective klt `ℚ`-boundary is dlt. -/
private theorem isDltPair_of_isKltPair {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {s : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor s n) {Δ : QDivisor X} (h0 : ∀ P, 0 ≤ Δ.coeff P)
    (h : IsKltPair s Δ) : MMP.Intersection.IsDltPair s Δ :=
  (MMP.Threefold.Bridges.isDltPair_iff_isDltPair s hK Δ).2
    (MMP.Threefold.Mori.IsKltPair.isDltPair ((isKltPair_iff_mori_isKltPair s hK h.1).1 h) h0).1

/-- A morphism of projective complex varieties is projective. -/
private theorem isProjectiveMorphism_of_isProjectiveVariety {W V : Scheme.{0}}
    {sW : W ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hV : MMP.Mori.IsProjectiveVariety ℂ sV) (q : W ⟶ V) (hq : q ≫ sV = sW) :
    IsProjectiveMorphism q :=
  haveI : IsSeparated sV := hV.toIsSeparated
  IsProjectiveMorphism.of_comp q sV (hq ▸ hW.isProjective)

/-- Under the invariants, the lowered boundary `B₁ - t T₁` is effective for `t ≤ 1`. -/
private theorem FloorInv.coeff_sub_smul_nonneg {X₁ Z : Scheme.{0}} [IsIntegral X₁]
    [CompactSpace X₁] [IsLocallyNoetherian X₁] [IsNormal X₁] {s₁ : X₁ ⟶ Spec (.of ℂ)}
    {π₁ : X₁ ⟶ Z} {m : ℕ} {t₀ : ℚ} {K₁ : Divisor X₁} {B₁ T₁ : QDivisor X₁} {Δ₁ : RDivisor X₁}
    (h : FloorInv s₁ π₁ m t₀ K₁ B₁ T₁ Δ₁) {t : ℚ} (ht : t ≤ 1) (P : MMP.Mori.PrimeDivisor X₁) :
    0 ≤ (B₁ - t • T₁).coeff P := by
  have h1 := h.floor_nonneg P
  have h2 := (h.coeff_bounds P).1
  simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at h2 ⊢
  nlinarith

/-- Under the invariants, on a `ℚ`-factorial model whose real scaling boundary `Δ₁` is klt, the
`ℚ`-boundary `B₁ - t₀ T₁` is klt. -/
private theorem FloorInv.isKltPair {X₁ Z : Scheme.{0}} [IsIntegral X₁]
    [CompactSpace X₁] [IsLocallyNoetherian X₁] [IsNormal X₁] {s₁ : X₁ ⟶ Spec (.of ℂ)}
    {π₁ : X₁ ⟶ Z} {m : ℕ} {t₀ : ℚ} {K₁ : Divisor X₁} {B₁ T₁ : QDivisor X₁} {Δ₁ : RDivisor X₁}
    (h : FloorInv s₁ π₁ m t₀ K₁ B₁ T₁ Δ₁) (ht : t₀ ≤ 1) (hQ : IsQFactorial s₁)
    (hk : IsRealKltPair s₁ Δ₁) : IsKltPair s₁ (B₁ - t₀ • T₁) :=
  isKltPair_of_isRealKltPair hQ (h.coeff_sub_smul_nonneg ht) (h.toRDivisor_eq ▸ hk)

section KltConvex

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- For a pair `(X, Δ)`, a canonical divisor `K = div(ω)` and a divisor `(Y, f, E)` over `X`,
`m(K + Δ)` is a Cartier divisor `M` with a pull-back `M'` to `Y`, for some `m > 0`. -/
private theorem exists_cartier_presentation [PerfectField k] {Δ : QDivisor X}
    (hP : MMP.Mori.IsPair sX Δ) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (D : DivisorOver k sX) :
    haveI := D.isLocallyNoetherian
    haveI := D.isNormal
    ∃ (m : ℕ) (M : Divisor X) (M' : Divisor D.Y), 0 < m ∧ M.IsCartier ∧
      (∀ Γ, (M.coeff Γ : ℝ) = m * (K.coeff Γ + Δ.coeff Γ)) ∧
      ∃ hC, M.IsPullback D.f hC M' := by
  obtain ⟨-, -, -, m, hm, ⟨M, hM, hMc⟩, -⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : CompactSpace D.Y := by
    have := D.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (D.f ≫ sX)
  obtain ⟨M', hM'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f hMc
  refine ⟨m, M, M', hm, hMc, fun Γ => ?_, _, hM'⟩
  have := congrArg (fun G : QDivisor X => G.coeff Γ) hM
  simp only [Divisor.coeff_toQDivisor, smul_add, natCast_zsmul, DivisorWithCoeffs.coeff_add,
    DivisorWithCoeffs.coeff_smul, nsmul_eq_mul] at this
  exact_mod_cast (by linear_combination this : (M.coeff Γ : ℚ) = m * (K.coeff Γ + Δ.coeff Γ))

/-- **The log discrepancy is affine in the boundary.** Fix a nonzero rational top form `ω`
with `K = div(ω)` and a divisor `E` over `X`. If `K + Bᵢ = (1 / mᵢ) Mᵢ` with `Mᵢ` Cartier, pulled
back to `M'ᵢ`, and `B = ∑ᵢ wᵢ Bᵢ` with `∑ᵢ wᵢ = 1`, then
`a(E, X, B) = ∑ᵢ wᵢ (1 + ord_E(f^*ω) - (1 / mᵢ) coeff_E(M'ᵢ))`, computed with the presentation
`K + B = ∑ᵢ (wᵢ / mᵢ) Mᵢ`. -/
private theorem isLogDiscrepancy_sum {n : ℕ} {D : DivisorOver k sX}
    (hX : MMP.Mori.IsNormalVariety k sX) (hf : IsProper D.f)
    {ω : MMP.Mori.RationalPluriForms sX n 1} (hω0 : ω ≠ 0) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (hKω : ∀ Γ, K.coeff Γ = Γ.ordForm ω)
    {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∑ i, w i = 1) {Bi : ι → RDivisor X}
    {B : RDivisor X} (hB : ∀ Γ, B.coeff Γ = ∑ i, w i * (Bi i).coeff Γ)
    {m : ι → ℕ} (hm : ∀ i, 0 < m i) {M : ι → Divisor X}
    {M' : haveI := D.isLocallyNoetherian; haveI := D.isNormal; ι → Divisor D.Y}
    (hMc : ∀ i, (M i).IsCartier)
    (hM : ∀ i Γ, ((M i).coeff Γ : ℝ) = m i * (K.coeff Γ + (Bi i).coeff Γ))
    (hpb : haveI := D.isLocallyNoetherian; haveI := D.isNormal;
      ∀ i, ∃ hC, (M i).IsPullback D.f hC (M' i)) :
    haveI := D.isLocallyNoetherian
    haveI := D.isNormal
    MMP.Intersection.IsLogDiscrepancy sX n B D
      (∑ i, w i * (1 + (D.ordPullback ω : ℝ) - (1 / (m i : ℝ)) * (M' i).coeff D.E)) := by
  have hm0 i : (m i : ℝ) ≠ 0 := by exact_mod_cast (hm i).ne'
  let e := Fintype.equivFin ι
  refine ⟨hX, hf, ω, hω0, ⟨K, hK, hKω⟩, Fintype.card ι, fun j => w (e.symm j) / m (e.symm j),
    fun j => M (e.symm j), fun j => M' (e.symm j), fun _ => hMc _, fun Γ => ?_, fun _ => hpb _, ?_⟩
  · dsimp only
    rw [Equiv.sum_comp e.symm (fun i => w i / m i * ((M i).coeff Γ : ℝ)), hB, ← hKω]
    have h i : w i / m i * ((M i).coeff Γ : ℝ) = w i * K.coeff Γ + w i * (Bi i).coeff Γ := by
      rw [hM]; field_simp [hm0 i]
    simp [h, Finset.sum_add_distrib, ← Finset.sum_mul, hw]
  · dsimp only
    rw [Equiv.sum_comp e.symm (fun i => w i / m i * ((M' i).coeff D.E : ℝ))]
    simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      hw, mul_one, one_mul, ← mul_assoc, mul_one_div]

end KltConvex

/-- **Boundaries between an lc and a klt boundary are klt.** If `(X, B₀)` is lc and `(X, B₁)` is
klt, every effective boundary `B = (1 - w) B₀ + w B₁` with `0 < w ≤ 1` and `K + B` `ℚ`-Cartier is
klt: the log discrepancy is affine in the boundary. -/
private theorem isKltPair_of_isLogCanonicalPair_of_isKltPair {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {s : X ⟶ Spec (.of ℂ)} {B₀ B₁ B : QDivisor X}
    (h₀ : MMP.Intersection.IsLogCanonicalPair s B₀) (h₁ : IsKltPair s B₁) {w : ℝ}
    (hw0 : 0 < w) (hB : ∀ Γ, (QDivisor.toRDivisor B).coeff Γ =
      (1 - w) * (QDivisor.toRDivisor B₀).coeff Γ + w * (QDivisor.toRDivisor B₁).coeff Γ)
    (hP : MMP.Mori.IsPair s B) (hB0 : ∀ P, 0 ≤ B.coeff P) (hw1 : w ≤ 1) :
    IsKltPair s B := by
  refine ⟨⟨inferInstance, inferInstance, hP, hB0⟩, fun n D a ha => ?_⟩
  obtain ⟨hX, hf, ω, hω0, ⟨K, hK, hKω⟩, -⟩ := id ha
  obtain ⟨m₀, M₀, M₀', hm₀, hM₀c, hM₀, hpb₀⟩ := exists_cartier_presentation h₀.1 hK D
  obtain ⟨m₁, M₁, M₁', hm₁, hM₁c, hM₁, hpb₁⟩ := exists_cartier_presentation h₁.1.isPair hK D
  have ha₀ : 0 ≤ 1 + (D.ordPullback ω : ℝ) - (1 / (m₀ : ℝ)) * M₀'.coeff D.E := by
    simpa using h₀.2.2 n D _ <| isLogDiscrepancy_sum (ι := Unit) hX hf hω0 hK hKω
      (w := 1) (by simp) (Bi := fun _ => QDivisor.toRDivisor B₀) (by simp) (fun _ => hm₀)
      (fun _ => hM₀c) (fun _ Γ => by rw [QDivisor.coeff_toRDivisor, hM₀]) fun _ => hpb₀
  have ha₁ : 0 < 1 + (D.ordPullback ω : ℝ) - (1 / (m₁ : ℝ)) * M₁'.coeff D.E := by
    simpa using h₁.2 n D _ <| isLogDiscrepancy_sum (ι := Unit) hX hf hω0 hK hKω
      (w := 1) (by simp) (Bi := fun _ => QDivisor.toRDivisor B₁) (by simp) (fun _ => hm₁)
      (fun _ => hM₁c) (fun _ Γ => by rw [QDivisor.coeff_toRDivisor, hM₁]) fun _ => hpb₁
  have hsum := isLogDiscrepancy_sum hX hf hω0 hK hKω (ι := Fin 2) (w := ![1 - w, w])
    (by simp) (Bi := ![QDivisor.toRDivisor B₀, QDivisor.toRDivisor B₁])
    (B := QDivisor.toRDivisor B)
    (fun Γ => by simp [Fin.sum_univ_two, hB Γ]) (m := ![m₀, m₁])
    (fun i => match i with | ⟨0, _⟩ => hm₀ | ⟨1, _⟩ => hm₁) (M := ![M₀, M₁])
    (M' := ![M₀', M₁'])
    (fun i => match i with | ⟨0, _⟩ => hM₀c | ⟨1, _⟩ => hM₁c)
    (fun i Γ => match i with
      | ⟨0, _⟩ => by simpa [QDivisor.coeff_toRDivisor] using hM₀ Γ
      | ⟨1, _⟩ => by simpa [QDivisor.coeff_toRDivisor] using hM₁ Γ)
    (fun i => match i with | ⟨0, _⟩ => hpb₀ | ⟨1, _⟩ => hpb₁)
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha hsum]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  nlinarith

/-- The invariants hold on the starting model. -/
private theorem floorInv_zero {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {g : X ⟶ Z}
    (hQ : IsQFactorial sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X}
    (hB : MMP.Intersection.IsDltPair sX B) {m : ℕ}
    (hmD : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) {t₀ : ℚ}
    (hD : QDivisor.IsRelativelyNef sX g (Divisor.toQDivisor K + B)) :
    FloorInv sX g m t₀ K B (Divisor.toQDivisor B.roundDown)
      (QDivisor.toRDivisor (B - t₀ • Divisor.toQDivisor B.roundDown)) := by
  obtain ⟨Dm, hDm, hDmc⟩ := hmD
  have hcoeff : ∀ P, (Divisor.toQDivisor B.roundDown).coeff P = ⌊B.coeff P⌋ := fun P => by simp
  refine ⟨⟨Dm, hDmc, hDm⟩, hK, hD, ?_, hB.1, fun P => ?_, fun P => ?_, rfl⟩
  · simpa using isKltPair_sub_smul_roundDown hQ hB one_pos le_rfl
  · rw [hcoeff]; exact_mod_cast Int.floor_nonneg.mpr (hB.1.2.1 P)
  · simp only [DivisorWithCoeffs.coeff_sub, hcoeff]
    exact ⟨sub_nonneg.mpr (Int.floor_le _), Int.fract_lt_one (B.coeff P), hB.2.1 P⟩

/-! ### The ray of a negative extremal contraction -/

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

/-- An `f`-ample Cartier divisor has an `f`-ample divisorial sheaf. -/
private theorem isRelativelyAmple_divisorialSheaf {X W : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ W} {L : Divisor X}
    (hL : MMP.Flips.IsRelativelyAmpleCartier f L) :
    haveI := hL.1.isInvertibleModule_divisorialSheaf
    MMP.Mori.IsRelativelyAmple f L.divisorialSheaf := by
  intro y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  exact ⟨V, hV, hyV, hL.2 V hV⟩

/-- An `f`-ample Cartier divisor has positive degree on every curve contracted by `f`. -/
private theorem degreeOn_pos_of_isRelativelyAmpleCartier {X W : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] {f : X ⟶ W} {L : Divisor X} (hL : MMP.Flips.IsRelativelyAmpleCartier f L)
    (C : ProperCurve sX) (hC : C.IsContractedBy f) : 0 < L.degreeOn ℂ sX C.ι C.dim_le hL.1 :=
  haveI := hL.1.isInvertibleModule_divisorialSheaf
  MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _
    (isRelativelyAmple_divisorialSheaf hL) C hC

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
  -- `A'` has positive degree on every contracted curve
  have hpos : ∀ C : ProperCurve sX, C.IsContractedBy f →
      0 < C.degree ℂ (MMP.CartierDivisor.sheaf A') := by
    intro C hC
    have := degreeOn_pos_of_isRelativelyAmpleCartier (hL ⟨0, hm1⟩) C hC
    rwa [Divisor.degreeOn, degreeOn_eq_of_iso ℂ sX C.ι C.dim_le eA] at this
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

/-- A `ℚ`-divisor `D` with `Dm = m D` is `(1 / m) Dm` as an `ℝ`-divisor. -/
private theorem toRDivisor_eq_sum_of_toQDivisor_eq {X : Scheme.{0}} {D : QDivisor X}
    {Dm : Divisor X} {m : ℕ} (hm : 0 < m) (h : Divisor.toQDivisor Dm = (m : ℤ) • D) :
    QDivisor.toRDivisor D = ∑ _j : Fin 1, ((m : ℝ)⁻¹) • Divisor.toRDivisor Dm := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Fin.sum_univ_one]
  ext P
  have := congrArg (fun T : QDivisor X => T.coeff P) h
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
    Int.cast_natCast] at this
  simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
    smul_eq_mul]
  rw [show ((Dm.coeff P : ℤ) : ℝ) = (((Dm.coeff P : ℤ) : ℚ) : ℝ) by push_cast; rfl, this]
  push_cast
  field_simp

/-- The intersection number of a `ℚ`-Cartier divisor `D` with `-toRDivisor D` `f`-ample is
negative on every curve contracted by `f`. -/
private theorem intersectionNumber_neg_of_isRelativelyAntiAmple {X W : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {f : X ⟶ W} {D : QDivisor X} (hD : D.IsQCartier)
    (hamp : MMP.Flips.IsRelativelyAntiAmple f (QDivisor.toRDivisor D)) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) : D.intersectionNumber ℂ sX C.ι C.dim_le hD < 0 := by
  obtain ⟨m, r, L, hm1, hr, hL, hE⟩ := hamp
  have hLc : ∀ j, (L j).IsCartier := fun j => (hL j).1
  -- the value `∑ rⱼ deg_C Lⱼ` of `(-D) · C` is positive
  have hpos : ∀ j, 0 < (L j).degreeOn ℂ sX C.ι C.dim_le (hLc j) := fun j =>
    degreeOn_pos_of_isRelativelyAmpleCartier (hL j) C hC
  have hsum : 0 < ∑ j, r j * ((L j).degreeOn ℂ sX C.ι C.dim_le (hLc j) : ℝ) := by
    haveI : Nonempty (Fin m) := ⟨⟨0, hm1⟩⟩
    exact Finset.sum_pos (fun j _ => mul_pos (hr j) (by exact_mod_cast hpos j))
      Finset.univ_nonempty
  -- two presentations of `-D`
  set hF := QDivisor.isCartierDivisor_cartierIndex_smul hD
  set N := D.cartierIndex hD
  have hpres : -QDivisor.toRDivisor D =
      ∑ _j : Fin 1, (-(N : ℝ)⁻¹) • Divisor.toRDivisor hF.toDivisor := by
    rw [toRDivisor_eq_sum_of_toQDivisor_eq (QDivisor.cartierIndex_pos hD) hF.toQDivisor_toDivisor]
    simp only [Fin.sum_univ_one, neg_smul]
    rfl
  have h1 : MMP.Flips.IsRIntersectionNumber ℂ sX (-QDivisor.toRDivisor D) r L C
      (∑ j, r j * ((L j).degreeOn ℂ sX C.ι C.dim_le (hLc j) : ℝ)) :=
    ⟨hLc, fun j => (L j).degreeOn ℂ sX C.ι C.dim_le (hLc j), hE,
      fun j => isCartierIntersectionNumber_degreeOn C (L j) (hLc j), rfl⟩
  have h2 : MMP.Flips.IsRIntersectionNumber ℂ sX (-QDivisor.toRDivisor D)
      (fun _ : Fin 1 => -(N : ℝ)⁻¹) (fun _ : Fin 1 => hF.toDivisor) C
      (-(D.intersectionNumber ℂ sX C.ι C.dim_le hD : ℝ)) := by
    refine ⟨fun _ => hF.isCartier_toDivisor, fun _ => hF.toDivisor.degreeOn ℂ sX C.ι C.dim_le
      hF.isCartier_toDivisor, hpres,
      fun _ => isCartierIntersectionNumber_degreeOn C _ hF.isCartier_toDivisor, ?_⟩
    simp only [Fin.sum_univ_one, QDivisor.intersectionNumber]
    push_cast
    ring
  have := (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r L _ _ _ _ h1 h2
  have h3 : (D.intersectionNumber ℂ sX C.ι C.dim_le hD : ℝ) < 0 := by linarith
  exact_mod_cast h3

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
    have := intersectionNumber_neg_of_isRelativelyAntiAmple (isQCartier_of_isQFactorial sX hQ D)
      hneg.isRelativelyAntiAmple C₀ hC₀
    exact mul_neg_of_pos_of_neg hc0 (by exact_mod_cast this)
  · rw [hmemR]
    exact hkey C
  · rw [himR]
    exact hrayX.1
  · rw [himR]
    exact hkey C

variable {k : Type} [Field k] {X : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] in
/-- Intersection numbers of adjoints `K + Δ` only depend on the linear equivalence class of
`K`. -/
private theorem intersectionNumber_add_eq_of_linearlyEquivalent {C : Scheme.{0}} (i : C ⟶ X)
    [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) {K₁ K₂ : Divisor X}
    (h : K₁.LinearlyEquivalent K₂) (Δ : QDivisor X) (h₁ : (Divisor.toQDivisor K₁ + Δ).IsQCartier)
    (h₂ : (Divisor.toQDivisor K₂ + Δ).IsQCartier) :
    (Divisor.toQDivisor K₁ + Δ).intersectionNumber k sX i hdim h₁ =
      (Divisor.toQDivisor K₂ + Δ).intersectionNumber k sX i hdim h₂ := by
  obtain ⟨D', hD', hD'c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul h₂
  set m := (Divisor.toQDivisor K₂ + Δ).cartierIndex h₂
  have hm := QDivisor.cartierIndex_pos h₂
  obtain ⟨φ, hφ⟩ := h
  set a : Additive (RationalFunctions X)ˣ := (m : ℤ) • Additive.ofMul φ with ha
  set G := D' + principalDivisorHom a with hG_def
  have hGc : G.IsCartier := hD'c.add (Divisor.isCartier_principalDivisor _)
  have hG : Divisor.toQDivisor G = (m : ℤ) • (Divisor.toQDivisor K₁ + Δ) := by
    have e : principalDivisorHom a = (m : ℤ) • (K₁ - K₂) := by
      rw [ha, map_zsmul, principalDivisorHom_apply, toMul_ofMul, hφ]
    rw [hG_def, e, map_add, hD', map_zsmul, map_sub, ← smul_add]
    congr 1
    abel
  have hGD : G.LinearlyEquivalent D' := ⟨a.toMul, by
    rw [hG_def, add_sub_cancel_left, principalDivisorHom_apply]⟩
  rw [QDivisor.intersectionNumber_eq_of_smul k sX i hdim _ h₁ hm G hGc hG,
    QDivisor.intersectionNumber_eq_of_smul k sX i hdim _ h₂ hm D' hD'c hD']
  congr 2
  have := hGc.isInvertibleModule_divisorialSheaf
  have := hD'c.isInvertibleModule_divisorialSheaf
  exact degreeOn_eq_of_iso k sX i hdim hGD.divisorialSheafIso

/-- **The steps are `D`-null.** Let `R` be the extremal ray of `NE̅(X/Z)` contracted by a
`(K + B - t₀ T)`-negative extremal contraction `f` of a `ℚ`-factorial projective fourfold, where
`D = K + B` is nef over `Z` with `m D` Cartier, `(X, B - T)` is klt with `B - T` effective and
`0 < t₀ < 1/(2(8m + 1))`. Then `D` is numerically trivial on `R`: the length bound
`(K + B - T) · C ≥ -8` for a rational curve `C` spanning `R` makes `D · C ≥ 1/m` impossible. -/
private theorem exists_forall_relativeCurveForm_eq_zero {X W Z : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    {f : X ⟶ W} {gW : W ⟶ Z} {π : X ⟶ Z} (hfg : f ≫ gW = π) {K KS : Divisor X}
    (hK : K.IsCanonicalDivisor sX 4) (hKS : ∃ n, KS.IsCanonicalDivisor sX n) {B T : QDivisor X}
    {m : ℕ} {t₀ : ℚ} (hm : 0 < m) (ht₀ : 0 < t₀) (ht₀m : t₀ * (2 * (8 * m + 1)) < 1)
    (hDm : ∃ Dm : Divisor X, Dm.IsCartier ∧
      Divisor.toQDivisor Dm = (m : ℤ) • (Divisor.toQDivisor K + B))
    (hnef : QDivisor.IsRelativelyNef sX π (Divisor.toQDivisor K + B))
    (hklt : IsKltPair sX (B - T)) (hBT : ∀ P, 0 ≤ (B - T).coeff P)
    (hneg : IsNegativeExtremalContraction ℂ sX sW
      (QDivisor.toRDivisor (Divisor.toQDivisor KS + (B - t₀ • T))) f)
    {R : Set (RelativeNumericalCurveClasses sX π)}
    (hface : IsContractionOfFace ℂ sX sW (relativeToAbsolute sX π '' R) f)
    (hray : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (relativeToAbsolute sX π '' R))
    {C₀ : ProperCurve sX} (hC₀ : C₀.IsContractedBy f)
    (hR₀ : relativeToAbsolute sX π '' R =
      {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C₀.cycle ℝ) = w}) :
    (∃ h : (Divisor.toQDivisor KS + B).IsQCartier,
      ∀ u ∈ R, QDivisor.relativeCurveForm sX π (Divisor.toQDivisor KS + B) h u = 0) ∧
    IsNegativeExtremalRayOf sX (Divisor.toQDivisor KS + (B - T)) (relativeToAbsolute sX π '' R) ∧
    ∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ relativeToAbsolute sX π '' R →
      haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
      (Divisor.toQDivisor K + B).intersectionNumber ℂ sX C.ι C.dim_le
        (isQCartier_of_isQFactorial sX hQ _) = 0 := by
  classical
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  have hXn : IsNormalVariety ℂ sX := hQ.1
  obtain ⟨n, hKSn⟩ := hKS
  have hn : n = 4 := by
    have h1 := hKSn.topologicalKrullDim_eq
    rw [hK.topologicalKrullDim_eq] at h1
    exact_mod_cast h1.symm
  subst hn
  have hlin : KS.LinearlyEquivalent K :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hXn hKSn hK
  have hq : ∀ D : QDivisor X, D.IsQCartier := isQCartier_of_isQFactorial sX hQ
  -- intersection numbers with curves
  set ι := fun (D : QDivisor X) (C : ProperCurve sX) =>
    (D.intersectionNumber ℂ sX C.ι C.dim_le (hq D) : ℝ) with hι
  have hι_add : ∀ D D' C, ι (D + D') C = ι D C + ι D' C := fun D D' C => by
    simp only [hι]
    rw [QDivisor.intersectionNumber_add' ℂ sX C.ι C.dim_le D D' (hq D) (hq D') (hq _)]
    push_cast; ring
  have hι_smul : ∀ (q : ℚ) D C, ι (q • D) C = q * ι D C := fun q D C => by
    simp only [hι]
    rw [MMP.Fourfold.intersectionNumber_smul sX C.ι C.dim_le D (hq D) q (hq _)]
    push_cast; ring
  set Dt := Divisor.toQDivisor KS + (B - t₀ • T)
  set D' := Divisor.toQDivisor KS + B
  set E := Divisor.toQDivisor KS + (B - T)
  have hdecomp : Dt = (1 - t₀) • D' + t₀ • E := by
    simp only [Dt, D', E, sub_smul, one_smul, smul_add, smul_sub]
    abel
  have hDtC : ∀ C : ProperCurve sX, C.IsContractedBy f → ι Dt C < 0 := fun C hC => by
    have := intersectionNumber_neg_of_isRelativelyAntiAmple (hq Dt)
      hneg.isRelativelyAntiAmple C hC
    simp only [hι]
    exact_mod_cast this
  have hπC : ∀ C : ProperCurve sX, C.IsContractedBy f → C.IsContractedBy π := fun C hC x hx => by
    rw [← hfg, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]
  have hD'C : ∀ C : ProperCurve sX, C.IsContractedBy f → 0 ≤ ι D' C := fun C hC => by
    have h1 := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hnef
      (hq _) C (hπC C hC)
    have h2 := intersectionNumber_add_eq_of_linearlyEquivalent (sX := sX) C.ι C.dim_le hlin B
      (hq D') (hq _)
    simp only [hι]
    rw [h2]
    exact_mod_cast h1
  have hEC : ∀ C : ProperCurve sX, C.IsContractedBy f → ι E C < 0 := fun C hC => by
    have h := hDtC C hC
    rw [hdecomp, hι_add, hι_smul, hι_smul] at h
    have h' := hD'C C hC
    push_cast at h
    have h1 : (0 : ℝ) ≤ 1 - t₀ := by
      have : (t₀ : ℝ) * (2 * (8 * m + 1)) < 1 := by exact_mod_cast ht₀m
      have hm' : (1 : ℝ) ≤ 2 * (8 * m + 1) := by
        have : (0 : ℝ) ≤ m := by positivity
        linarith
      nlinarith
    have : (0 : ℝ) < t₀ := by exact_mod_cast ht₀
    nlinarith [mul_nonneg h1 h']
  -- the ray `F` is `E`-negative
  set F := relativeToAbsolute sX π '' R
  have hEneg : IsNegativeExtremalRayOf sX E F := by
    refine ⟨hq E, hray, fun u hu hu0 => ?_⟩
    rw [hR₀] at hu
    obtain ⟨c, hc, rfl⟩ := hu
    have hc0 : 0 < c := lt_of_le_of_ne hc (fun h => hu0 (by rw [← h, zero_smul]))
    rw [map_smul, smul_eq_mul, MMP.ProgramBaseChange.curveForm_numericalClass_cycle]
    exact mul_neg_of_pos_of_neg hc0 (hEC C₀ hC₀)
  have hkltM : MMP.Mori.IsKltPair sX 4 KS (B - T) :=
    (isKltPair_iff_mori_isKltPair sX hKSn hklt.1).1 hklt
  obtain ⟨T', -, hFT, -, hle⟩ :=
    MMP.Fourfold.exists_isRationalCurve_eq_ray_of_isNegativeExtremalRayOf_of_isAlgClosed sX hkltM
      hBT hEneg
  have hT'F : OneCycle.numericalClass sX (T'.cycle ℝ) ∈ F := by
    rw [hFT]; exact ⟨1, zero_le_one, one_smul _ _⟩
  have hT'f : T'.IsContractedBy f := (hface.isContractedBy_iff T').mpr hT'F
  have hET : -8 ≤ ι E T' := by
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle] at hle
    simp only [hι]
    push_cast at hle
    linarith
  -- `D · T' = 0`
  obtain ⟨Dm, hDmc, hDm⟩ := hDm
  have hD'T : ι D' T' = 0 := by
    have hDT := MMP.Mori.QDivisor.intersectionNumber_eq_of_smul ℂ sX T'.ι T'.dim_le _ (hq _) hm
      Dm hDmc hDm
    have h2 := intersectionNumber_add_eq_of_linearlyEquivalent (sX := sX) T'.ι T'.dim_le hlin B
      (hq D') (hq _)
    have h0 := hD'C T' hT'f
    simp only [hι] at h0 ⊢
    rw [h2, hDT] at h0 ⊢
    set d := Dm.degreeOn ℂ sX T'.ι T'.dim_le hDmc
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    by_contra hne
    have hd0 : (0 : ℝ) ≤ d := by
      push_cast at h0
      exact (div_nonneg_iff.mp h0).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hmR))
    have hd1 : (1 : ℝ) ≤ d := by
      have : (d : ℝ) ≠ 0 := fun h => hne (by push_cast; rw [h, zero_div])
      have hd : (0 : ℤ) ≤ d := by exact_mod_cast hd0
      have : (1 : ℤ) ≤ d := by
        rcases hd.lt_or_eq with h | h
        · exact h
        · exact absurd (by exact_mod_cast h.symm) this
      exact_mod_cast this
    have h := hDtC T' hT'f
    rw [hdecomp, hι_add, hι_smul, hι_smul] at h
    simp only [hι] at h
    rw [h2, hDT] at h
    push_cast at h
    have ht : (t₀ : ℝ) * (2 * (8 * m + 1)) < 1 := by exact_mod_cast ht₀m
    have ht0 : (0 : ℝ) < t₀ := by exact_mod_cast ht₀
    have hdm : 1 / (m : ℝ) ≤ d / m := div_le_div_of_nonneg_right hd1 hmR.le
    have key : 0 < (1 - (t₀ : ℝ)) * (d / m) + t₀ * (ι E T') := by
      have h1m : 1 / (m : ℝ) * m = 1 := by field_simp
      have : (1 - (t₀ : ℝ)) * (1 / m) - 8 * t₀ > 0 := by
        rw [gt_iff_lt, ← mul_lt_mul_iff_of_pos_right hmR]
        have : ((1 - (t₀ : ℝ)) * (1 / m) - 8 * t₀) * m = 1 - t₀ - 8 * t₀ * m := by
          field_simp
        rw [this]
        nlinarith
      have h1t : (0 : ℝ) ≤ 1 - t₀ := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hdm h1t, mul_le_mul_of_nonneg_left hET ht0.le]
    simp only [hι] at key
    linarith
  refine ⟨⟨hq D', fun u hu => ?_⟩, hEneg, fun C hC => ?_⟩
  · have hu' : relativeToAbsolute sX π u ∈ F := ⟨u, hu, rfl⟩
    rw [hFT] at hu'
    obtain ⟨c, -, hc⟩ := hu'
    rw [relativeCurveForm_eq_comp, LinearMap.comp_apply, ← hc, map_smul,
      MMP.ProgramBaseChange.curveForm_numericalClass_cycle, smul_eq_mul]
    simp only [hι] at hD'T
    rw [hD'T, mul_zero]
  · have hC' := hC
    rw [hFT] at hC'
    obtain ⟨c, -, hc⟩ := hC'
    have h1 := MMP.ProgramBaseChange.curveForm_numericalClass_cycle sX D' (hq D') C
    rw [← hc, map_smul, MMP.ProgramBaseChange.curveForm_numericalClass_cycle, smul_eq_mul] at h1
    simp only [hι] at hD'T
    rw [hD'T, mul_zero] at h1
    have h2 := intersectionNumber_add_eq_of_linearlyEquivalent (sX := sX) C.ι C.dim_le hlin B
      (hq D') (isQCartier_of_isQFactorial sX hQ _)
    rw [← h2]
    exact_mod_cast h1.symm

/-- Two morphisms to an affine scheme agreeing after a morphism `f` with `Γ(f)` bijective
agree. -/
private theorem eq_of_comp_eq_of_isIso_app_top {X W Y : Scheme.{0}} [IsAffine Y] (f : X ⟶ W)
    (hf : IsIso (f.app ⊤)) {a b : W ⟶ Y} (h : f ≫ a = f ≫ b) : a = b := by
  apply ext_of_isAffine
  have := congrArg Scheme.Hom.appTop h
  simp only [Scheme.Hom.comp_appTop] at this
  exact (cancel_mono (f.app ⊤)).mp this

/-! ### Transforms of divisors along the steps -/

/-- If `g'` represents `φ` at the generic point of `P` and sends it to the generic point of `E`,
then the transform of `P` under `φ` is `E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq' {X Y : Scheme.{0}}
    [IsReduced X] [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y}
    {P : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : MMP.Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [MMP.Flips.coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [MMP.Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- A representative of a rational map `ψ` with `fp ∘ ψ = f` satisfies `fp ∘ g' = f` pointwise on
its domain. -/
private theorem apply_hom_eq_of_compHom_eq {X Y W : Scheme.{0}} [IsReduced X]
    [IsSeparated (W ↘ ⊤_ Scheme)] {ψ : X.RationalMap Y} {fp : Y ⟶ W} {f : X ⟶ W}
    (h : ψ.compHom fp = f.toRationalMap) (g' : X.PartialMap Y) (hg' : g'.toRationalMap = ψ)
    (x : g'.domain) : fp (g'.hom x) = f x := by
  have h1 : (g'.compHom fp).equiv f.toPartialMap := by
    rw [← Scheme.PartialMap.toRationalMap_eq_iff, Scheme.RationalMap.compHom_toRationalMap, hg',
      h]
  have h2 := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp h1
  have h3 := congrArg (fun φ => φ.base x) h2
  simp only [Scheme.PartialMap.compHom] at h3
  exact h3

/-- The coefficient of a transform at `Q` is the coefficient at the unique prime sent to `Q`. -/
private theorem transformDivisor_apply_of_forall_iff {X Y : Scheme.{0}} {ψ : X.RationalMap Y}
    {Q : MMP.Mori.PrimeDivisor Y} {E : MMP.Mori.PrimeDivisor X}
    (h : ∀ E' : MMP.Mori.PrimeDivisor X,
      MMP.Mori.RationalMap.transformPrimeDivisor ψ E' = some Q ↔ E' = E)
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor ψ D Q = D E := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hD, hD']
  | single P r =>
    rw [MMP.Mori.RationalMap.transformDivisor_single]
    by_cases hP : P = E
    · subst hP
      rw [(h P).mpr rfl]
      simp
    · rw [Finsupp.single_apply, if_neg hP]
      rcases hψ : MMP.Mori.RationalMap.transformPrimeDivisor ψ P with _ | Q'
      · rfl
      · have hQ' : Q' ≠ Q := fun e => hP ((h P).mp (by rw [hψ, e]))
        simp [Finsupp.single_apply, hQ']

/-- Over the generic point of a prime divisor of a normal scheme, a separated birational morphism
has at most one point. -/
private theorem eq_of_apply_eq_genericPoint {X₂ W : Scheme.{0}} [IsIntegral X₂] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (fp : X₂ ⟶ W) [IsSeparated fp] [IsDominant fp]
    (hfp : IsBirationalMorphism fp) (P' : MMP.Mori.PrimeDivisor W) {x y : X₂}
    (hx : fp x = P'.genericPoint) (hy : fp y = P'.genericPoint) : x = y := by
  have := P'.isDiscreteValuationRing_localRing
  haveI : ValuationRing (W.presheaf.stalk (fp x)) := by rw [hx]; infer_instance
  haveI : ValuationRing (W.presheaf.stalk (fp y)) := by rw [hy]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing fp hfp.functionFieldMap_bijective x
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing fp hfp.functionFieldMap_bijective y
  exact MMP.Positivity.eq_of_isIso_stalkMap fp hfp.functionFieldMap_bijective (hy.trans hx.symm)

/-- A separated variety is separated over the terminal scheme. -/
private theorem isSeparated_terminal {k : Type} [Field k] {X : Scheme.{0}}
    {s : X ⟶ Spec (.of k)} (h : IsNormalVariety k s) : IsSeparated (X ↘ ⊤_ Scheme) := by
  haveI := h.1
  rw [show (X ↘ ⊤_ Scheme) = s ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

section StepTransforms

variable {k : Type} [Field k] {X₁ X₂ W : Scheme.{0}} [IsIntegral X₁] [CompactSpace X₁]
  [IsLocallyNoetherian X₁] [IsNormal X₁] [IsIntegral X₂] [CompactSpace X₂]
  [IsLocallyNoetherian X₂] [IsNormal X₂] [IsIntegral W] [CompactSpace W]
  [IsLocallyNoetherian W] [IsNormal W] {s₁ : X₁ ⟶ Spec (.of k)} {s₂ : X₂ ⟶ Spec (.of k)}
  {sW : W ⟶ Spec (.of k)}

/-- **Coefficients of transforms along a step.** Let `f : X₁ ⟶ W` and `fp : X₂ ⟶ W` be proper
birational morphisms of normal varieties and `ψ : X₁ ⤏ X₂` a rational map with `fp ∘ ψ = f`. If
`fp` maps the generic point of a prime divisor `Q` of `X₂` to the generic point of a prime divisor
`P'` of `W`, the coefficient of `ψ_* D` along `Q` is the coefficient of `D` along the prime
divisor of `X₁` over `P'`. -/
private theorem exists_transformDivisor_apply_eq_of_compHom_eq (hX₁ : IsNormalVariety k s₁)
    (hX₂ : IsNormalVariety k s₂) (hW : IsNormalVariety k sW) {f : X₁ ⟶ W} {fp : X₂ ⟶ W}
    (hfW : f ≫ sW = s₁) (hfpW : fp ≫ sW = s₂) [IsProper f] [IsProper fp]
    (hf : IsBirationalMorphism f) (hfp : IsBirationalMorphism fp) {ψ : X₁.RationalMap X₂}
    (hψ : ψ.compHom fp = f.toRationalMap) (P' : MMP.Mori.PrimeDivisor W)
    (Q : MMP.Mori.PrimeDivisor X₂) (hQ : fp Q.genericPoint = P'.genericPoint) :
    ∃ E : MMP.Mori.PrimeDivisor X₁, f E.genericPoint = P'.genericPoint ∧
      ∀ {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R X₁),
        MMP.Mori.RationalMap.transformDivisor ψ D Q = D E := by
  classical
  haveI := hW.1
  haveI := isSeparated_terminal hX₂
  haveI := isSeparated_terminal hW
  haveI : IsSeparated f := IsSeparated.of_comp f sW
  haveI : IsSeparated fp := IsSeparated.of_comp fp sW
  haveI : IsDominant f := hf.isDominant
  haveI : IsDominant fp := hfp.isDominant
  obtain ⟨E, hE, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hW (hfW ▸ hX₁) hf P'
  refine ⟨E, hE, fun D => transformDivisor_apply_of_forall_iff (fun E' => ⟨fun h => ?_, ?_⟩) D⟩
  · obtain ⟨hdef, -⟩ := MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h
    obtain ⟨g', hP, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
    have h1 := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hP
    have h2 := apply_hom_eq_of_compHom_eq hψ g' hg' ⟨E'.genericPoint, hP⟩
    rw [← h1, hQ] at h2
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_apply_eq_genericPoint f hf P' h2.symm hE)
  · intro hE'
    rw [hE']
    have hdom : E.genericPoint ∈ ψ.domain := MMP.Flips.RationalMap.mem_domain_of_coheight_le_one
      f fp ψ hψ E.coheight_genericPoint.le
    obtain ⟨g', hP, hg'⟩ := Scheme.RationalMap.mem_domain.mp hdom
    refine transformPrimeDivisor_eq_some_of_genericPoint_eq' g' hg' hP ?_
    have h2 := apply_hom_eq_of_compHom_eq hψ g' hg' ⟨E.genericPoint, hP⟩
    rw [hE] at h2
    exact eq_of_apply_eq_genericPoint fp hfp P' hQ h2

/-- **Transforms along a step over the base of its contraction.** In the setting of
`exists_transformDivisor_apply_eq_of_compHom_eq`, `fp_* ψ_* D = f_* D` for every divisor `D` on
`X₁`. -/
private theorem transformDivisor_transformDivisor_of_compHom_eq (hX₁ : IsNormalVariety k s₁)
    (hX₂ : IsNormalVariety k s₂) (hW : IsNormalVariety k sW) {f : X₁ ⟶ W} {fp : X₂ ⟶ W}
    (hfW : f ≫ sW = s₁) (hfpW : fp ≫ sW = s₂) [IsProper f] [IsProper fp]
    (hf : IsBirationalMorphism f) (hfp : IsBirationalMorphism fp) {ψ : X₁.RationalMap X₂}
    (hψ : ψ.compHom fp = f.toRationalMap) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X₁) :
    MMP.Mori.RationalMap.transformDivisor (X := X₂) fp.toRationalMap
        (MMP.Mori.RationalMap.transformDivisor ψ D) =
      MMP.Mori.RationalMap.transformDivisor (X := X₁) f.toRationalMap D := by
  haveI := hW.1
  haveI : IsSeparated f := IsSeparated.of_comp f sW
  haveI : IsSeparated fp := IsSeparated.of_comp fp sW
  haveI : IsDominant f := hf.isDominant
  haveI : IsDominant fp := hfp.isDominant
  refine Finsupp.ext fun P' => ?_
  obtain ⟨E, hE, -, htrE⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hW (hfW ▸ hX₁) hf P'
  obtain ⟨Q, hQ, -, htrQ⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hW (hfpW ▸ hX₂) hfp P'
  obtain ⟨E', hE', htr⟩ :=
    exists_transformDivisor_apply_eq_of_compHom_eq hX₁ hX₂ hW hfW hfpW hf hfp hψ P' Q hQ
  rw [htrE, htrQ, htr, AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_apply_eq_genericPoint f hf P' hE' hE)]

end StepTransforms

variable {k : Type} [Field k] {X₂ W : Scheme.{0}} [IsIntegral X₂] [CompactSpace X₂]
  [IsLocallyNoetherian X₂] [IsNormal X₂] [IsIntegral W] [CompactSpace W]
  [IsLocallyNoetherian W] [IsNormal W] {s₂ : X₂ ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} in
/-- Push-forward along a proper birational morphism mapping the generic point of every prime
divisor to the generic point of a prime divisor is injective on divisors. -/
private theorem transformDivisor_injective_of_forall_exists (hX₂ : IsNormalVariety k s₂)
    (hW : IsNormalVariety k sW) {fp : X₂ ⟶ W} (hfpW : fp ≫ sW = s₂) [IsProper fp]
    (hfp : IsBirationalMorphism fp)
    (hfpQ : ∀ Q : MMP.Mori.PrimeDivisor X₂, ∃ P' : MMP.Mori.PrimeDivisor W,
      fp Q.genericPoint = P'.genericPoint)
    {R : Type*} [AddCommMonoid R] {D₁ D₂ : DivisorWithCoeffs R X₂}
    (h : MMP.Mori.RationalMap.transformDivisor (X := X₂) fp.toRationalMap D₁ =
      MMP.Mori.RationalMap.transformDivisor (X := X₂) fp.toRationalMap D₂) : D₁ = D₂ := by
  haveI := hW.1
  haveI : IsSeparated fp := IsSeparated.of_comp fp sW
  haveI : IsDominant fp := hfp.isDominant
  refine Finsupp.ext fun Q => ?_
  obtain ⟨P', hP'⟩ := hfpQ Q
  obtain ⟨Q', hQ', -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hW (hfpW ▸ hX₂) hfp P'
  have hQQ : Q' = Q := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_apply_eq_genericPoint fp hfp P' hQ' hP')
  subst hQQ
  have := congrArg (fun D => D P') h
  rw [htr, htr] at this
  exact this

/-- If `fp` is an open immersion off a closed subset `V` of codimension at least two, it maps the
generic point of every prime divisor to the generic point of a prime divisor. -/
private theorem exists_genericPoint_eq_of_isOpenImmersion {X₂ W : Scheme.{0}} (fp : X₂ ⟶ W)
    (V : TopologicalSpace.Closeds X₂) (hV : 2 ≤ closedsCodimension V)
    (hU : IsOpenImmersion (Scheme.Opens.ι (V.compl : X₂.Opens) ≫ fp))
    (Q : MMP.Mori.PrimeDivisor X₂) :
    ∃ P' : MMP.Mori.PrimeDivisor W, fp Q.genericPoint = P'.genericPoint := by
  have hQV : Q.genericPoint ∈ (V.compl : X₂.Opens) := by
    by_contra hnd
    have h2 := le_closedsCodimension_iff.mp hV
      (IrreducibleCloseds.closureSingleton Q.genericPoint)
      (closure_minimal (Set.singleton_subset_iff.mpr (by by_contra h; exact hnd h)) V.isClosed)
    rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton Q.genericPoint =
      (irreducibleSetEquivPoints (α := X₂)).symm Q.genericPoint from rfl,
      Order.coheight_orderIso, Q.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  set u : (V.compl : X₂.Opens) := ⟨Q.genericPoint, hQV⟩
  have h1 : Order.coheight ((Scheme.Opens.ι (V.compl : X₂.Opens) ≫ fp) u) = 1 := by
    have e1 := coheight_eq_of_isOpenImmersion (x := u) (Scheme.Opens.ι (V.compl : X₂.Opens) ≫ fp)
    have e2 := coheight_eq_of_isOpenImmersion (x := u) (Scheme.Opens.ι (V.compl : X₂.Opens))
    exact e1.trans (e2.symm.trans Q.coheight_genericPoint)
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1).symm⟩

section ResidueDegree

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]

/-- A proper curve which is not contracted by `g` does not have a point as image. -/
private theorem not_exists_range_eq_singleton' (g : X ⟶ Y) (Γ : ProperCurve sX)
    (h : ¬ Γ.IsContractedBy g) : ¬ ∃ y : Y, Set.range (Γ.ι ≫ g) = {y} := by
  rintro ⟨y, hy⟩
  refine h fun x hx => ?_
  rw [← Γ.range_ι] at hx
  obtain ⟨c, rfl⟩ := hx
  have h1 : (Γ.ι ≫ g) c ∈ Set.range (Γ.ι ≫ g) := ⟨c, rfl⟩
  have h2 : (Γ.ι ≫ g) (genericPoint Γ.scheme) ∈ Set.range (Γ.ι ≫ g) := ⟨_, rfl⟩
  rw [hy] at h1 h2
  rw [Scheme.Hom.comp_apply] at h1 h2
  rw [Γ.ι_genericPoint] at h2
  exact h1.trans h2.symm

/-- A morphism over `k` which does not contract a proper curve has positive residue degree at
its generic point: `k(C)` is a finite extension of the function field of the image curve. -/
private theorem residueFieldDegree_pos_of_not_isContractedBy' (g : X ⟶ Y) (hg : g ≫ sY = sX)
    (Γ : ProperCurve sX) (h : ¬ Γ.IsContractedBy g) : 0 < residueFieldDegree g Γ.point := by
  have hnc := not_exists_range_eq_singleton' g Γ h
  set φ := Γ.ι ≫ g with hφdef
  have hφ : φ ≫ sY = Γ.ι ≫ sX := by rw [hφdef, Category.assoc, hg]
  have : IsProper (φ ≫ sY) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sY
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sY) := hφ ▸ inferInstance
  have hdeg : residueFieldDegree g Γ.point = degreeOver φ.toImage := by
    have h1 := residueDegree_comp Γ.ι g (genericPoint Γ.scheme)
    rw [Γ.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion Γ.ι, mul_one]
      at h1
    have h2 := residueDegree_comp φ.toImage φ.imageι (genericPoint Γ.scheme)
    rw [Scheme.Hom.toImage_imageι,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ.imageι,
      one_mul, residueDegree_genericPoint_eq_degreeOver φ.toImage] at h2
    exact h1.symm.trans h2
  rw [hdeg]
  letI := (functionFieldMap φ.toImage).toAlgebra
  have hfin : Module.Finite φ.image.functionField Γ.scheme.functionField :=
    finite_functionField_image sY φ hnc
  have heq : functionFieldMap φ.toImage = dominantFunctionFieldMap φ.toImage :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target φ.toImage (genericPoint Γ.scheme)
        (map_genericPoint_of_isDominant φ.toImage))).symm
  rw [degreeOver_eq_finrank φ.toImage heq]
  exact Module.finrank_pos

end ResidueDegree

/-! ### Cartier descent along the contraction -/

/-- On an integral Noetherian normal scheme every Cartier divisor has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (A : X.CartierDivisor) :
    ∃ w : Divisor X, MMP.Intersection.IsWeilDivisorOfCartier A w := by
  letI : IsNoetherian X := ⟨⟩
  have h0 : ∀ s ∈ MMP.Intersection.cartierSupport A, Order.coheight s = 0 → False := by
    intro s hs h0
    have : Ring.KrullDimLE 0 (X.presheaf.stalk s) := krullDimLE_of_coheight_le (by simp [h0])
    have : IsArtinianRing (X.presheaf.stalk s) := isArtinianRing_iff_krullDimLE_zero.mpr this
    exact MMP.Intersection.notMem_cartierSupport_of_isArtinianRing A s hs
  have hfin := finite_setOf_genericPoint_mem
    (MMP.Intersection.isClosed_cartierSupport A) h0
  refine ⟨Finsupp.ofSupportFinite (fun P => MMP.Intersection.primeDivisorOrder P A)
    (hfin.subset fun P hP => ?_), fun P => ?_⟩
  · by_contra h
    have hg : (MMP.Intersection.primeDivisorSubvariety P).genericPoint = P.genericPoint := rfl
    refine hP ((MMP.Intersection.isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset
      fun h' => h ?_)
    show P.genericPoint ∈ MMP.Intersection.cartierSupport A
    rw [← hg]
    exact MMP.Intersection.genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact MMP.Intersection.isOrderAlong_primeDivisorOrder A P

/-- A dominant morphism of integral schemes maps the generic point outside every divisor. -/
private theorem forall_map_componentGenericPoint_notMem_supp {X W : Scheme.{0}} [IsIntegral X]
    [IsIntegral W] {f : X ⟶ W} [IsDominant f] {R : Type*} [Zero R]
    (G : DivisorWithCoeffs R W) :
    ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ G.supp := fun Z => by
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant f]
  exact MMP.Fourfold.genericPoint_notMem_supp G

/-- **Cartier descent along a contraction of a negative face.** Let `f` be the contraction of a
`(K + Δ)`-negative extremal face `F` of a klt pair on a projective variety, `f` birational, and
let `D` be a Cartier divisor of degree zero on every curve with class in `F`. Then `D = f^* G` for
a Cartier divisor `G` on the target. -/
private theorem exists_isPullback_of_isContractionOfFace {X W : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W] [CompactSpace W]
    [IsLocallyNoetherian W] [IsNormal W] {sX : X ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : MMP.Mori.IsKltPair sX n K Δ) (hΔ : Δ.IsEffective)
    {F : Set (NumericalCurveClasses sX)}
    (hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) F)
    {f : X ⟶ W} (hface : IsContractionOfFace ℂ sX sW F f) (hfb : IsBirationalMorphism f)
    {Dm : Divisor X} (hDmc : Dm.IsCartier)
    (hdeg : ∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ F →
      haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
      Dm.degreeOn ℂ sX C.ι C.dim_le hDmc = 0) :
    ∃ (G : Divisor W) (_ : G.IsCartier) (hB : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ G.supp), G.IsPullback f hB Dm := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  haveI : IsDominant f := hfb.isDominant
  haveI := hDmc.isInvertibleModule_divisorialSheaf
  obtain ⟨LZ, hLZ, ⟨e⟩⟩ := MMP.Mori.exists_isInvertible_iso_pullback_of_isContractionOfFace hklt
    hΔ hF hface Dm.divisorialSheaf (fun C hC => hdeg C hC)
  haveI := hLZ
  obtain ⟨EW, ⟨eW⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf LZ
  obtain ⟨w, hw⟩ := exists_isWeilDivisorOfCartier EW
  have hwc : w.IsCartier := hw.isCartier
  obtain ⟨eW'⟩ := hw.nonempty_sheaf_iso_divisorialSheaf
  have hBw := forall_map_componentGenericPoint_notMem_supp (f := f) w
  obtain ⟨ep⟩ := MMP.Mori.Divisor.nonempty_divisorialSheaf_pullback_iso hwc f hBw
  have α : Dm.divisorialSheaf ≅ (w.pullback hwc hBw).divisorialSheaf :=
    e ≪≫ (Scheme.Modules.pullback f).mapIso (eW ≪≫ eW') ≪≫ ep.symm
  obtain ⟨φ, hφ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso α
  obtain ⟨φW, hφW, hpb⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hfb φ
  have hGc : (w + principalDivisor φW).IsCartier :=
    hwc.add (Divisor.isCartier_principalDivisor _)
  refine ⟨w + principalDivisor φW, hGc,
    forall_map_componentGenericPoint_notMem_supp (f := f) _, ?_⟩
  have h1 := Divisor.isPullback_pullback hwc hBw
  have h2 := Divisor.isPullback_principalDivisor φW hφW
  have h3 := Divisor.IsPullback.add hwc (Divisor.isCartier_principalDivisor _)
    (forall_map_componentGenericPoint_notMem_supp (f := f) _) h1 h2
  rw [hpb, ← hφ] at h3
  convert h3 using 1
  abel

/-- The birational transform of divisors commutes with regarding a divisor as a `ℚ`-divisor. -/
private theorem transformDivisor_toQDivisor {X Y : Scheme.{0}} (φ : X.RationalMap Y)
    (D : Divisor X) :
    MMP.Mori.RationalMap.transformDivisor φ (Divisor.toQDivisor D) =
      Divisor.toQDivisor (MMP.Mori.RationalMap.transformDivisor φ D) := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h h' => rw [map_add, map_add, h, h', map_add, map_add]
  | single P n =>
    have hP : Divisor.toQDivisor (Finsupp.single P n) = Finsupp.single P (n : ℚ) := by
      ext E
      change ((Finsupp.single P n E : ℤ) : ℚ) = Finsupp.single P (n : ℚ) E
      rw [Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp
    rw [hP, MMP.Mori.RationalMap.transformDivisor_single,
      MMP.Mori.RationalMap.transformDivisor_single]
    cases MMP.Mori.RationalMap.transformPrimeDivisor φ P with
    | none => simp
    | some E =>
      ext F
      change Finsupp.single E (n : ℚ) F = ((Finsupp.single E n F : ℤ) : ℚ)
      rw [Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp

variable {k : Type} [Field k] {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X] in
/-- A `ℚ`-Cartier `ℚ`-divisor with nonnegative intersection number on every curve contracted by
`f` is `f`-nef. -/
private theorem isRelativelyNef_of_intersectionNumber_nonneg {f : X ⟶ Y} {D : QDivisor X}
    (hD : D.IsQCartier)
    (h : ∀ C : ProperCurve sX, C.IsContractedBy f →
      0 ≤ D.intersectionNumber k sX C.ι C.dim_le hD) :
    D.IsRelativelyNef sX f := by
  refine ⟨hD, fun C hC => ?_⟩
  have key := h C hC
  rw [QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX C.ι C.dim_le D hD _
    (D.cartierIndexSMul hD).2 (QDivisor.toQDivisor_cartierIndexSMul D hD)] at key
  have hm : (0 : ℚ) < D.cartierIndex hD := by exact_mod_cast QDivisor.cartierIndex_pos hD
  have hdeg : (0 : ℚ) ≤ ((D.cartierIndexSMul hD : Divisor X).degreeOn k sX C.ι C.dim_le
      (D.cartierIndexSMul hD).2 : ℚ) := by
    have := mul_nonneg key hm.le
    rwa [div_mul_cancel₀ _ hm.ne'] at this
  rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
    Finsupp.sum_single_index (by simp)]
  have hdeg' : (0 : ℝ) ≤ ((D.cartierIndexSMul hD : Divisor X).degreeOn k sX C.ι C.dim_le
      (D.cartierIndexSMul hD).2 : ℝ) := by exact_mod_cast hdeg
  have hm' : (0 : ℝ) ≤ (((1 / (D.cartierIndex hD : ℚ)) • (1 : ℚ) : ℚ) : ℝ) := by
    simp only [smul_eq_mul, mul_one, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    positivity
  exact mul_nonneg hm' hdeg'

/-- **Nefness passes to the next model.** Let `f : X₁ ⟶ W` and `fp : X₂ ⟶ W` be proper morphisms
over `Z` (by `gW`), `f` surjective, and `G` a Cartier divisor on `W` with pull-backs `m D₁` and
`m D₂`. If `D₁` is nef over `Z`, so is `D₂`: a curve of `X₂` over a point of `Z` either is
contracted by `fp`, or maps onto a curve of `W` over a point of `Z`, which lifts to `X₁`. -/
private theorem isRelativelyNef_of_isPullback {X₁ X₂ W Z : Scheme.{0}} [IsIntegral X₁]
    [CompactSpace X₁] [IsLocallyNoetherian X₁] [IsNormal X₁] [IsIntegral X₂] [CompactSpace X₂]
    [IsLocallyNoetherian X₂] [IsNormal X₂] [IsIntegral W] [CompactSpace W]
    [IsLocallyNoetherian W] [IsNormal W] {s₁ : X₁ ⟶ Spec (.of ℂ)} {s₂ : X₂ ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} (hW : IsNormalVariety ℂ sW) (hX₁ : IsNormalVariety ℂ s₁)
    (hX₂ : IsNormalVariety ℂ s₂) {f : X₁ ⟶ W} {fp : X₂ ⟶ W} {gW : W ⟶ Z}
    (hfW : f ≫ sW = s₁) (hfpW : fp ≫ sW = s₂) [IsProper f] [IsProper fp] [Surjective f]
    {G : Divisor W} (hGc : G.IsCartier) {Dm₁ : Divisor X₁}
    {hB₁ : ∀ Z' : irreducibleComponents X₁, f (componentGenericPoint X₁ Z') ∉ G.supp}
    (h₁ : G.IsPullback f hB₁ Dm₁) {Dm₂ : Divisor X₂}
    {hB₂ : ∀ Z' : irreducibleComponents X₂, fp (componentGenericPoint X₂ Z') ∉ G.supp}
    (h₂ : G.IsPullback fp hB₂ Dm₂) {m : ℕ} (hm : 0 < m) {D₁ : QDivisor X₁}
    {D₂ : QDivisor X₂} (hD₁ : Divisor.toQDivisor Dm₁ = (m : ℤ) • D₁)
    (hD₂ : Divisor.toQDivisor Dm₂ = (m : ℤ) • D₂)
    (hnef : QDivisor.IsRelativelyNef s₁ (f ≫ gW) D₁) :
    QDivisor.IsRelativelyNef s₂ (fp ≫ gW) D₂ := by
  subst hfW
  haveI : QuasiCompact (f ≫ sW) := hX₁.1.toQuasiCompact
  haveI : QuasiCompact s₂ := hX₂.1.toQuasiCompact
  haveI := hW.1
  haveI : IsSeparated sW := hW.1.toIsSeparated
  haveI : LocallyOfFiniteType sW := hW.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (f ≫ sW) := hX₁.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType s₂ := hX₂.1.toLocallyOfFiniteType
  have hDm₁c : Dm₁.IsCartier := h₁.pullback_eq hGc ▸ hGc.isCartier_pullback f hB₁
  have hDm₂c : Dm₂.IsCartier := h₂.pullback_eq hGc ▸ hGc.isCartier_pullback fp hB₂
  have hq₁ : D₁.IsQCartier := ⟨m, by exact_mod_cast hm.ne', Dm₁, hD₁, hDm₁c⟩
  have hq₂ : D₂.IsQCartier := ⟨m, by exact_mod_cast hm.ne', Dm₂, hD₂, hDm₂c⟩
  haveI := hGc.isInvertibleModule_divisorialSheaf
  haveI := hDm₁c.isInvertibleModule_divisorialSheaf
  haveI := hDm₂c.isInvertibleModule_divisorialSheaf
  obtain ⟨e₁⟩ := MMP.Mori.Divisor.nonempty_divisorialSheaf_pullback_iso hGc f hB₁
  obtain ⟨e₂⟩ := MMP.Mori.Divisor.nonempty_divisorialSheaf_pullback_iso hGc fp hB₂
  rw [h₁.pullback_eq hGc] at e₁
  rw [h₂.pullback_eq hGc] at e₂
  refine isRelativelyNef_of_intersectionNumber_nonneg s₂ hq₂ fun Γ hΓ => ?_
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ s₂ Γ.ι Γ.dim_le _ hq₂ hm Dm₂ hDm₂c hD₂]
  refine div_nonneg ?_ (by positivity)
  have hΓdeg : Dm₂.degreeOn ℂ s₂ Γ.ι Γ.dim_le hDm₂c =
      Γ.degree ℂ ((Scheme.Modules.pullback fp).obj G.divisorialSheaf) :=
    degreeOn_eq_of_iso ℂ s₂ Γ.ι Γ.dim_le e₂
  rw [hΓdeg, MMP.Mori.ProperCurve.degree_pullback fp hfpW Γ G.divisorialSheaf]
  split_ifs with hcurve
  swap
  · simp
  obtain ⟨C₁, hC₁, hC₁img⟩ := MMP.Mori.ProperCurve.exists_map_eq (f ≫ sW) sW f rfl
    (⟨fp Γ.point, hcurve⟩ : ProperCurve sW)
  -- `C₁` lies over a point of `Z`
  have hC₁Z : C₁.IsContractedBy (f ≫ gW) := by
    have hcl : closure ({fp Γ.point} : Set W) ⊆ fp.base '' closure {Γ.point} :=
      closure_minimal (Set.singleton_subset_iff.mpr ⟨Γ.point, subset_closure rfl, rfl⟩)
        (fp.isClosedMap _ isClosed_closure)
    intro x hx
    have hfx : f x ∈ closure ({fp Γ.point} : Set W) := by
      rw [← hC₁img]; exact ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hx'e⟩ := hcl hfx
    have hpt : f C₁.point ∈ closure ({fp Γ.point} : Set W) := by
      rw [hC₁]; exact subset_closure rfl
    obtain ⟨y', hy', hy'e⟩ := hcl hpt
    simp only [Scheme.Hom.comp_apply]
    rw [← hx'e, ← hy'e]
    exact (hΓ x' hx').trans (hΓ y' hy').symm
  have hn₁ := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg (f ≫ sW) hnef hq₁
    C₁ hC₁Z
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ (f ≫ sW) C₁.ι C₁.dim_le _ hq₁ hm Dm₁ hDm₁c hD₁]
    at hn₁
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm
  have hd₁ : (0 : ℤ) ≤ Dm₁.degreeOn ℂ (f ≫ sW) C₁.ι C₁.dim_le hDm₁c := by
    have := (div_nonneg_iff.mp hn₁).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hmq))
    exact_mod_cast this
  have hC₁deg : Dm₁.degreeOn ℂ (f ≫ sW) C₁.ι C₁.dim_le hDm₁c =
      C₁.degree ℂ ((Scheme.Modules.pullback f).obj G.divisorialSheaf) :=
    degreeOn_eq_of_iso ℂ (f ≫ sW) C₁.ι C₁.dim_le e₁
  rw [hC₁deg, MMP.Mori.ProperCurve.degree_pullback f rfl C₁ G.divisorialSheaf] at hd₁
  have hcurve₁ : IsProperCurve sW (f C₁.point) := by rw [hC₁]; exact hcurve
  rw [dif_pos hcurve₁] at hd₁
  have hCW : (⟨f C₁.point, hcurve₁⟩ : ProperCurve sW) = ⟨fp Γ.point, hcurve⟩ := by
    congr 1
  rw [hCW] at hd₁
  have hnc : ¬ C₁.IsContractedBy f := by
    intro h
    refine MMP.Mori.ProperCurve.not_isProperCurve_of_forall_eq f C₁ (y := f C₁.point)
      (fun z => ?_) hcurve₁
    rw [Scheme.Hom.comp_apply]
    exact h _ (by rw [← C₁.range_ι]; exact ⟨z, rfl⟩)
  have hres := residueFieldDegree_pos_of_not_isContractedBy' f rfl C₁ hnc
  have hdW : (0 : ℤ) ≤ (⟨fp Γ.point, hcurve⟩ : ProperCurve sW).degree ℂ G.divisorialSheaf := by
    by_contra hneg
    push Not at hneg
    have : (residueFieldDegree f C₁.point : ℤ) *
        (⟨fp Γ.point, hcurve⟩ : ProperCurve sW).degree ℂ G.divisorialSheaf < 0 :=
      mul_neg_of_pos_of_neg (by exact_mod_cast hres) hneg
    omega
  have : (0 : ℤ) ≤ (residueFieldDegree fp Γ.point : ℤ) *
      (⟨fp Γ.point, hcurve⟩ : ProperCurve sW).degree ℂ G.divisorialSheaf :=
    mul_nonneg (by positivity) hdW
  exact_mod_cast this

/-- A pull-back `m D = f^* G` of one Cartier multiple `G = m D_W` is a pull-back of `ℚ`-divisors
`D = f^* D_W`: any Cartier multiple `D''` of `D_W` has `m D'' = m' G`, and pull-backs are
additive. -/
private theorem qDivisor_isPullback_of_isPullback {X W : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] {f : X ⟶ W} {G : Divisor W} (hGc : G.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ G.supp} {Dm : Divisor X}
    (h : G.IsPullback f hB Dm) {m : ℕ} (hm : 0 < m) {DW : QDivisor W} {D : QDivisor X}
    (hDW : Divisor.toQDivisor G = (m : ℤ) • DW) (hD : Divisor.toQDivisor Dm = (m : ℤ) • D)
    (hB' : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ DW.supp) :
    DW.IsPullback f hB' D := by
  intro m' hm' D'' hD'' hD''c
  have hB'' : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D''.supp :=
    fun Z hZ => hB' Z (by
      rwa [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm'.ne') hD''] at hZ)
  refine ⟨D''.pullback hD''c hB'', ?_, Divisor.isPullback_pullback hD''c hB''⟩
  have hmm : (m : ℤ) • D'' = (m' : ℤ) • G := by
    apply Divisor.toQDivisor_injective
    rw [map_zsmul, map_zsmul, hD'', hDW, smul_smul, smul_smul, mul_comm]
  have hsupp : ((m : ℤ) • D'').supp = D''.supp := by
    rw [← Divisor.supp_toQDivisor, map_zsmul, QDivisor.supp_zsmul (by exact_mod_cast hm.ne'),
      Divisor.supp_toQDivisor]
  have hBm : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ ((m : ℤ) • D'').supp := fun Z => by
    rw [hsupp]; exact hB'' Z
  have h1 := (Divisor.isPullback_pullback hD''c hB'').zsmul hD''c (m : ℤ) hBm
  have h2 := h.zsmul hGc (m' : ℤ) (by rw [← hmm]; exact hBm)
  have h3 : (m : ℤ) • D''.pullback hD''c hB'' = (m' : ℤ) • Dm :=
    (Divisor.IsPullback.of_eq hmm h1).eq (hGc.zsmul _) h2
  have h4 := congrArg Divisor.toQDivisor h3
  rw [map_zsmul, map_zsmul, hD, smul_smul, mul_comm, ← smul_smul] at h4
  exact smul_right_injective _ (by exact_mod_cast hm.ne' : ((m : ℤ) : ℚ) ≠ 0)
    (by simpa only [Int.cast_smul_eq_zsmul] using h4)

/-- **Log canonicity passes along a crepant step.** Let `f : X₁ ⟶ W` and `fp : X₂ ⟶ W` be proper
birational morphisms of normal varieties with `K₁ + B₁ = f^*(K_W + B_W)` and
`K₂ + B₂ = fp^*(K_W + B_W)` for compatible canonical divisors. If `(X₁, B₁)` is lc, so is
`(X₂, B₂)`: a divisor over `X₂` is read as a divisor over `W`, whose discrepancy is that of a
divisor over `X₁` with the same valuation. -/
private theorem isLogCanonicalPair_of_isPullback_of_isPullback {X₁ X₂ W : Scheme.{0}}
    [IsIntegral X₁] [CompactSpace X₁] [IsLocallyNoetherian X₁] [IsNormal X₁] [IsIntegral X₂]
    [CompactSpace X₂] [IsLocallyNoetherian X₂] [IsNormal X₂] [IsIntegral W] [CompactSpace W]
    [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of ℂ)} {f : X₁ ⟶ W} {fp : X₂ ⟶ W}
    (hX₁ : IsNormalVariety ℂ (f ≫ sW)) (hX₂ : IsNormalVariety ℂ (fp ≫ sW)) [IsProper f]
    [IsProper fp] (hfb : IsBirationalMorphism f) (hfpb : IsBirationalMorphism fp)
    {K₁ : Divisor X₁} {K₂ : Divisor X₂} {KW : Divisor W} (hK₁ : K₁.IsCanonicalDivisor (f ≫ sW) 4)
    (hK₂ : K₂.IsCanonicalDivisor (fp ≫ sW) 4) (hKW : KW.IsCanonicalDivisor sW 4)
    (hfK : MMP.Mori.RationalMap.transformDivisor (X := X₁) f.toRationalMap K₁ = KW)
    (hfpK : MMP.Mori.RationalMap.transformDivisor (X := X₂) fp.toRationalMap K₂ = KW)
    {B₁ : QDivisor X₁} {B₂ : QDivisor X₂} {BW : QDivisor W} (hpair : MMP.Mori.IsPair sW BW)
    (hpb₁ : ∃ hB, (Divisor.toQDivisor KW + BW).IsPullback f hB (Divisor.toQDivisor K₁ + B₁))
    (hpb₂ : ∃ hB, (Divisor.toQDivisor KW + BW).IsPullback fp hB (Divisor.toQDivisor K₂ + B₂))
    (hlc : MMP.Intersection.IsLogCanonicalPair (f ≫ sW) B₁) (hB₂ : ∀ P, 0 ≤ B₂.coeff P) :
    MMP.Intersection.IsLogCanonicalPair (fp ≫ sW) B₂ := by
  haveI : LocallyOfFiniteType (f ≫ sW) := hX₁.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fp ≫ sW) := hX₂.1.toLocallyOfFiniteType
  haveI : IsDominant f := hfb.isDominant
  haveI : IsDominant fp := hfpb.isDominant
  obtain ⟨-, hc₁⟩ := hpair.isDiscrepancy_iff_of_crepant f hX₁ hfb hKW hK₁
    (Or.inr ⟨inferInstance, hfK, hpb₁⟩)
  obtain ⟨hP₂, hc₂⟩ := hpair.isDiscrepancy_iff_of_crepant fp hX₂ hfpb hKW hK₂
    (Or.inr ⟨inferInstance, hfpK, hpb₂⟩)
  refine ⟨hP₂, hB₂, fun n' D a ha => ?_⟩
  have hn' : n' = 4 := by
    have h1 := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
    rw [hK₂.topologicalKrullDim_eq] at h1
    exact_mod_cast h1.symm
  subst hn'
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP₂ hK₂ D
  have ha' := ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc a).mp ha).2
  have hcW := (hc₂ D (MMP.Mori.compDivisorOver fp hX₂ hfpb D)
    (MMP.Mori.valuation_compDivisorOver fp hX₂ hfpb D) c).mp hc
  obtain ⟨D₁, hD₁⟩ := MMP.Mori.exists_divisorOver_comap_eq hX₁ hfb
    (MMP.Mori.compDivisorOver fp hX₂ hfpb D)
  obtain ⟨E₁, hE₁⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hX₁ D₁
  have hc₁' := (hc₁ E₁.toDivisorOver (MMP.Mori.compDivisorOver fp hX₂ hfpb D)
    (by rw [hD₁]; exact congrArg (fun v => v.comap (functionFieldMap f)) hE₁.symm) c).mpr hcW
  have hl := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc₁' E₁.isProper
  rw [ha']
  exact hlc.2.2 4 E₁.toDivisorOver (1 + c) hl

/-- **One step of the floor-lowering program.** A step of the klt program with scaling for
`B₁ - t₀ T₁`, from a model satisfying `FloorInv`, contracts a `(K₁ + B₁)`-null negative extremal
ray of `NE̅(X₁/Z)`, and the invariants pass to the next model with the transformed divisors; the
Cartier divisor `m D₁` and its transform `m D₂` are pull-backs of one Cartier divisor on the
base of the contraction. -/
private theorem step {X₁ X₂ W Z : Scheme.{0}} [IsIntegral X₁] [CompactSpace X₁]
    [IsLocallyNoetherian X₁] [IsNormal X₁] [IsIntegral X₂] [CompactSpace X₂]
    [IsLocallyNoetherian X₂] [IsNormal X₂] {s₁ : X₁ ⟶ Spec (.of ℂ)} {s₂ : X₂ ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {π₁ : X₁ ⟶ Z} {π₂ : X₂ ⟶ Z}
    {f : X₁ ⟶ W} {gW : W ⟶ Z} {fp : X₂ ⟶ W} {ψ : X₁.RationalMap X₂}
    {KS₁ K₁ : Divisor X₁} {B₁ T₁ : QDivisor X₁} {Δ₁ : RDivisor X₁} {Δ₂ : RDivisor X₂} {m : ℕ}
    {t₀ : ℚ} (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (h1 : π₁ ≫ sZ = s₁) (hp1 : MMP.Mori.IsProjectiveVariety ℂ s₁) (hq1 : IsQFactorial s₁)
    (hKS₁ : ∃ n, KS₁.IsCanonicalDivisor s₁ n)
    (h2 : π₂ ≫ sZ = s₂) (hp2 : MMP.Mori.IsProjectiveVariety ℂ s₂) (hq2 : IsQFactorial s₂)
    (hklt2 : IsRealKltPair s₂ Δ₂)
    (hW : MMP.Mori.IsProjectiveVariety ℂ sW) (hfg : f ≫ gW = π₁) (hfpg : fp ≫ gW = π₂)
    (hneg : IsNegativeExtremalContraction ℂ s₁ sW (logCanonicalDivisor KS₁ Δ₁) f)
    (hdf : (IsBirationalMorphism f ∧
        (∃ E : MMP.Mori.PrimeDivisor X₁, (MMP.Mori.exceptionalSet f : Set X₁) = E.support) ∧
        IsIso fp ∧ IsModificationOf f fp ψ) ∨
      MMP.Flips.IsFlip ℂ s₁ sW s₂ (logCanonicalDivisor KS₁ Δ₁) f fp ψ)
    (hΔ₂ : Δ₂ = MMP.Mori.RationalMap.transformDivisor ψ Δ₁)
    (hm : 0 < m) (ht₀ : 0 < t₀) (ht₀m : t₀ * (2 * (8 * m + 1)) < 1)
    (hinv : FloorInv s₁ π₁ m t₀ K₁ B₁ T₁ Δ₁) :
    (∃ R : Set (RelativeNumericalCurveClasses s₁ π₁),
      IsNegativeRelativeRayContraction s₁ π₁ sW (Divisor.toQDivisor KS₁ + (B₁ - t₀ • T₁)) R f gW ∧
      ∃ h : (Divisor.toQDivisor KS₁ + B₁).IsQCartier,
        ∀ u ∈ R, QDivisor.relativeCurveForm s₁ π₁ (Divisor.toQDivisor KS₁ + B₁) h u = 0) ∧
    FloorInv s₂ π₂ m t₀ (MMP.Mori.RationalMap.transformDivisor ψ K₁)
      (MMP.Mori.RationalMap.transformDivisor ψ B₁) (MMP.Mori.RationalMap.transformDivisor ψ T₁)
      Δ₂ ∧
    (IsBirationalMorphism f ∧ IsBirationalMorphism fp ∧ IsProper fp ∧ IsProper f ∧
      ψ.compHom fp = f.toRationalMap ∧ gW ≫ sZ = sW ∧ IsNormalVariety ℂ sW ∧
      (∀ Q : MMP.Mori.PrimeDivisor X₂, ∃ P' : MMP.Mori.PrimeDivisor W,
        fp Q.genericPoint = P'.genericPoint) ∧
      ∃ (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W) (_ : CompactSpace W),
      ∀ Dm₁ : Divisor X₁, Dm₁.IsCartier →
        Divisor.toQDivisor Dm₁ = (m : ℤ) • (Divisor.toQDivisor K₁ + B₁) →
        ∃ (G : Divisor W) (_ : G.IsCartier)
          (hB₁ : ∀ Z' : irreducibleComponents X₁, f (componentGenericPoint X₁ Z') ∉ G.supp)
          (hB₂ : ∀ Z' : irreducibleComponents X₂, fp (componentGenericPoint X₂ Z') ∉ G.supp)
          (Dm₂ : Divisor X₂), Divisor.toQDivisor Dm₂ = (m : ℤ) •
            (Divisor.toQDivisor (MMP.Mori.RationalMap.transformDivisor ψ K₁) +
              MMP.Mori.RationalMap.transformDivisor ψ B₁) ∧
          G.IsPullback f hB₁ Dm₁ ∧ G.IsPullback fp hB₂ Dm₂) := by
  obtain rfl := hinv.toRDivisor_eq
  obtain ⟨hDm, hK₁, hnef, hklt, hlc, hT0, hBT0, -⟩ := id hinv
  have hfW : f ≫ sW = s₁ := hneg.isContraction.comp_eq
  have hgW : gW ≫ sZ = sW := eq_of_comp_eq_of_isIso_app_top f (hneg.isContraction.isIso_app ⊤)
    (by rw [← Category.assoc, hfg, h1, hfW])
  rw [logCanonicalDivisor_toRDivisor] at hneg hdf
  obtain ⟨R, hRc, hface, hray, C₀, hC₀, hR₀⟩ :=
    exists_isNegativeRelativeRayContraction hp1 hW hZ hq1 hfg hgW hneg
  obtain ⟨⟨hDq, hnull⟩, hEneg, hD0⟩ := exists_forall_relativeCurveForm_eq_zero hp1 hq1 hfg hK₁
    hKS₁ hm ht₀ ht₀m hDm hnef hklt (fun P => (hBT0 P).1) hneg hface hray hC₀ hR₀
  refine ⟨⟨R, hRc, hDq, hnull⟩, ?_⟩
  subst hfW
  have hfpW : fp ≫ sW = s₂ := by rw [← h2, ← hfpg, Category.assoc, hgW]
  subst hfpW
  -- the setting of the step
  have hX₁n : IsNormalVariety ℂ (f ≫ sW) := hq1.1
  have hX₂n : IsNormalVariety ℂ (fp ≫ sW) := hq2.1
  have hWn : IsNormalVariety ℂ sW := hneg.isNormalVariety_target
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI : LocallyOfFiniteType sW := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : QuasiCompact sW := hWn.1.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : IsProper f := hneg.isContraction.isProper
  have hcase : IsBirationalMorphism f ∧ IsBirationalMorphism fp ∧ IsProper fp ∧
      ψ.compHom fp = f.toRationalMap ∧ ∃ V : TopologicalSpace.Closeds X₂,
        2 ≤ closedsCodimension V ∧ IsOpenImmersion (Scheme.Opens.ι (V.compl : X₂.Opens) ≫ fp) := by
    rcases hdf with ⟨hfb, -, hiso, hmod⟩ | hflip
    · refine ⟨hfb, isBirationalMorphism_of_isIso fp, inferInstance, hmod.2, ⊥,
        le_closedsCodimension_iff.mpr fun W' hW' => ?_, inferInstance⟩
      obtain ⟨x, hx⟩ := W'.isIrreducible.nonempty
      exact absurd (hW' hx) (by simp)
    · refine ⟨hflip.isSmall_source.isBirationalMorphism, hflip.isSmall.isBirationalMorphism,
        hflip.isProper, hflip.isModificationOf.2, ?_⟩
      obtain ⟨V, W', hV, -, hle, hiso⟩ := hflip.isSmall.exists_isIso
      refine ⟨V, hV, ?_⟩
      rw [← Scheme.Hom.resLE_comp_ι fp hle]
      infer_instance
  obtain ⟨hfb, hfpb, hfpP, hψ, V, hV, hVimm⟩ := hcase
  haveI := hfpP
  haveI : IsDominant f := hfb.isDominant
  haveI : IsDominant fp := hfpb.isDominant
  have hfpQ := exists_genericPoint_eq_of_isOpenImmersion fp V hV hVimm
  have hT1 : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X₁),
      MMP.Mori.RationalMap.transformDivisor (X := X₂) fp.toRationalMap
          (MMP.Mori.RationalMap.transformDivisor ψ D) =
        MMP.Mori.RationalMap.transformDivisor (X := X₁) f.toRationalMap D := fun D =>
    transformDivisor_transformDivisor_of_compHom_eq hX₁n hX₂n hWn rfl rfl hfb hfpb hψ D
  have hcoef : ∀ Q : MMP.Mori.PrimeDivisor X₂, ∃ E : MMP.Mori.PrimeDivisor X₁,
      ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X₁),
        MMP.Mori.RationalMap.transformDivisor ψ D Q = D E := fun Q => by
    obtain ⟨P', hP'⟩ := hfpQ Q
    obtain ⟨E, -, hE⟩ := exists_transformDivisor_apply_eq_of_compHom_eq hX₁n hX₂n hWn rfl rfl
      hfb hfpb hψ P' Q hP'
    exact ⟨E, hE⟩
  -- dimensions and canonical divisors
  have hdim₁ : topologicalKrullDim X₁ = 4 := hK₁.topologicalKrullDim_eq
  haveI : AlgebraicGeometry.IsVariety ℂ sW := hWn.1
  haveI : AlgebraicGeometry.IsVariety ℂ (f ≫ sW) := hX₁n.1
  haveI : AlgebraicGeometry.IsVariety ℂ (fp ≫ sW) := hX₂n.1
  have hdimW : topologicalKrullDim W = 4 :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sW (f ≫ sW) hfb).trans hdim₁
  have hdim₂ : topologicalKrullDim X₂ = 4 :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sW (fp ≫ sW) hfpb).symm.trans
      hdimW
  obtain ⟨KW₀, hKW₀⟩ := MMP.Mori.exists_isCanonicalDivisor sW hWn (n := 4) (by exact_mod_cast hdimW)
  have hKW : Divisor.IsCanonicalDivisor sW 4
      (MMP.Mori.RationalMap.transformDivisor (X := X₁) f.toRationalMap K₁) :=
    MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hWn hX₁n hfb hKW₀ hK₁
  obtain ⟨K₂₀, hK₂₀⟩ := MMP.Mori.exists_isCanonicalDivisor (fp ≫ sW) hX₂n (n := 4)
    (by exact_mod_cast hdim₂)
  obtain ⟨K'', hK'', hK''eq⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq
      hWn hX₂n hfpb hKW hK₂₀
  have hK₂eq : MMP.Mori.RationalMap.transformDivisor ψ K₁ = K'' :=
    transformDivisor_injective_of_forall_exists hX₂n hWn rfl hfpb hfpQ (by rw [hT1, hK''eq])
  have hK₂ : Divisor.IsCanonicalDivisor (fp ≫ sW) 4 (MMP.Mori.RationalMap.transformDivisor ψ K₁) :=
    hK₂eq ▸ hK''
  -- Cartier descent of `m D₁`
  obtain ⟨n₁, hKSn⟩ := hKS₁
  have hn₁ : n₁ = 4 := by
    have h1 := hKSn.topologicalKrullDim_eq
    rw [hdim₁] at h1
    exact_mod_cast h1.symm
  subst hn₁
  have hkltM : MMP.Mori.IsKltPair (f ≫ sW) 4 KS₁ (B₁ - T₁) :=
    (isKltPair_iff_mori_isKltPair (f ≫ sW) hKSn hklt.1).1 hklt
  obtain ⟨hEq, hEray, hEneg'⟩ := hEneg
  have hFneg : IsNegativeExtremalFace ℝ (closedConeOfCurves (f ≫ sW) :
      Set (NumericalCurveClasses (f ≫ sW)))
      (MMP.Fourfold.QDivisor.curveForm (f ≫ sW) (Divisor.toQDivisor KS₁ + (B₁ - T₁))
        hkltM.1.2.2) (relativeToAbsolute (f ≫ sW) π₁ '' R) :=
    ⟨hEray.1, hEray.1.2.2.1, fun z hz hz0 => hEneg' z hz hz0⟩
  haveI : QuasiCompact (f ≫ sW) := hX₁n.1.toQuasiCompact
  have hdesc : ∀ Dm₁ : Divisor X₁, Dm₁.IsCartier →
      Divisor.toQDivisor Dm₁ = (m : ℤ) • (Divisor.toQDivisor K₁ + B₁) →
      ∃ (G : Divisor W) (_ : G.IsCartier)
        (hB₁ : ∀ Z' : irreducibleComponents X₁, f (componentGenericPoint X₁ Z') ∉ G.supp)
        (hB₂ : ∀ Z' : irreducibleComponents X₂, fp (componentGenericPoint X₂ Z') ∉ G.supp)
        (Dm₂ : Divisor X₂), Divisor.toQDivisor Dm₂ = (m : ℤ) •
          (Divisor.toQDivisor (MMP.Mori.RationalMap.transformDivisor ψ K₁) +
            MMP.Mori.RationalMap.transformDivisor ψ B₁) ∧
        G.IsPullback f hB₁ Dm₁ ∧ G.IsPullback fp hB₂ Dm₂ := by
    intro Dm₁ hDm₁c hDm₁
    have hdeg : ∀ C : ProperCurve (f ≫ sW), OneCycle.numericalClass (f ≫ sW) (C.cycle ℝ) ∈
        relativeToAbsolute (f ≫ sW) π₁ '' R → Dm₁.degreeOn ℂ (f ≫ sW) C.ι C.dim_le hDm₁c = 0 := by
      intro C hC
      have h0 := hD0 C hC
      rw [QDivisor.intersectionNumber_eq_of_smul ℂ (f ≫ sW) C.ι C.dim_le _ _ hm Dm₁ hDm₁c hDm₁,
        div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · exact_mod_cast h0
      · exact absurd h0 (by exact_mod_cast hm.ne')
    obtain ⟨G, hGc, hB₁, hpb₁⟩ := exists_isPullback_of_isContractionOfFace hp1 hkltM
      (fun P => (hBT0 P).1) hFneg hface hfb hDm₁c hdeg
    have hB₂ := forall_map_componentGenericPoint_notMem_supp (f := fp) G
    have hpb₂ := Divisor.isPullback_pullback hGc hB₂
    have hfG : MMP.Mori.RationalMap.transformDivisor (X := X₁) f.toRationalMap Dm₁ = G :=
      MMP.Positivity.transformDivisor_of_isPullback_divisor hWn hX₁n hfb hGc hpb₁
    have hfpG : MMP.Mori.RationalMap.transformDivisor (X := X₂) fp.toRationalMap
        (G.pullback hGc hB₂) = G :=
      MMP.Positivity.transformDivisor_of_isPullback_divisor hWn hX₂n hfpb hGc hpb₂
    have hDm₂eq : MMP.Mori.RationalMap.transformDivisor ψ Dm₁ = G.pullback hGc hB₂ :=
      transformDivisor_injective_of_forall_exists hX₂n hWn rfl hfpb hfpQ (by rw [hT1, hfG, hfpG])
    refine ⟨G, hGc, hB₁, hB₂, G.pullback hGc hB₂, ?_, hpb₁, hpb₂⟩
    rw [← hDm₂eq, ← transformDivisor_toQDivisor, hDm₁, map_zsmul, map_add,
      transformDivisor_toQDivisor]
  obtain ⟨Dm₁, hDm₁c, hDm₁⟩ := hDm
  obtain ⟨G, hGc, hB₁, hB₂, Dm₂, hDm₂, hpb₁, hpb₂⟩ := hdesc Dm₁ hDm₁c hDm₁
  have hDm₂c : Dm₂.IsCartier := hpb₂.pullback_eq hGc ▸ hGc.isCartier_pullback fp hB₂
  have hfG : MMP.Mori.RationalMap.transformDivisor (X := X₁) f.toRationalMap Dm₁ = G :=
    MMP.Positivity.transformDivisor_of_isPullback_divisor hWn hX₁n hfb hGc hpb₁
  -- coefficients of the transformed boundaries
  have hBT₂ : ∀ Q, 0 ≤ (MMP.Mori.RationalMap.transformDivisor ψ B₁ -
      MMP.Mori.RationalMap.transformDivisor ψ T₁).coeff Q ∧
      (MMP.Mori.RationalMap.transformDivisor ψ B₁ -
        MMP.Mori.RationalMap.transformDivisor ψ T₁).coeff Q < 1 ∧
      (MMP.Mori.RationalMap.transformDivisor ψ B₁).coeff Q ≤ 1 := fun Q => by
    obtain ⟨E, hE⟩ := hcoef Q
    rw [← map_sub]
    change (0 : ℚ) ≤ MMP.Mori.RationalMap.transformDivisor ψ (B₁ - T₁) Q ∧
      MMP.Mori.RationalMap.transformDivisor ψ (B₁ - T₁) Q < 1 ∧
      MMP.Mori.RationalMap.transformDivisor ψ B₁ Q ≤ 1
    rw [hE, hE]
    exact hBT0 E
  have hT₂ : ∀ Q, 0 ≤ (MMP.Mori.RationalMap.transformDivisor ψ T₁).coeff Q := fun Q => by
    obtain ⟨E, hE⟩ := hcoef Q
    change (0 : ℚ) ≤ MMP.Mori.RationalMap.transformDivisor ψ T₁ Q
    rw [hE]
    exact hT0 E
  have hBt₂ : ∀ Q, 0 ≤ (MMP.Mori.RationalMap.transformDivisor ψ B₁ -
      t₀ • MMP.Mori.RationalMap.transformDivisor ψ T₁).coeff Q := fun Q => by
    obtain ⟨E, hE⟩ := hcoef Q
    have hsm := (MMP.Mori.RationalMap.transformDivisorₗ ℚ ψ).map_smul t₀ T₁
    simp only [MMP.Mori.RationalMap.transformDivisorₗ_apply] at hsm
    rw [← hsm, ← map_sub]
    change (0 : ℚ) ≤ MMP.Mori.RationalMap.transformDivisor ψ (B₁ - t₀ • T₁) Q
    rw [hE]
    exact hinv.coeff_sub_smul_nonneg (by nlinarith) E
  have hB₂0 : ∀ Q, 0 ≤ (MMP.Mori.RationalMap.transformDivisor ψ B₁).coeff Q := fun Q => by
    obtain ⟨E, hE⟩ := hcoef Q
    change (0 : ℚ) ≤ MMP.Mori.RationalMap.transformDivisor ψ B₁ Q
    rw [hE]
    exact hlc.2.1 E
  have hΔ₂' : QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor ψ B₁ -
      t₀ • MMP.Mori.RationalMap.transformDivisor ψ T₁) = Δ₂ := by
    have hsm := (MMP.Mori.RationalMap.transformDivisorₗ ℚ ψ).map_smul t₀ T₁
    simp only [MMP.Mori.RationalMap.transformDivisorₗ_apply] at hsm
    rw [hΔ₂, transformDivisor_toRDivisor]
    congr 1
    rw [map_sub, hsm]
  -- klt, by lowering the klt boundary `B₂ - t₀ T₂`
  have hk2Q : IsKltPair (fp ≫ sW) (MMP.Mori.RationalMap.transformDivisor ψ B₁ -
      t₀ • MMP.Mori.RationalMap.transformDivisor ψ T₁) :=
    isKltPair_of_isRealKltPair hq2 hBt₂ (hΔ₂' ▸ hklt2)
  have hdlt2 := isDltPair_of_isKltPair hK₂ hBt₂ hk2Q
  have hklt₂ : IsKltPair (fp ≫ sW) (MMP.Mori.RationalMap.transformDivisor ψ B₁ -
      MMP.Mori.RationalMap.transformDivisor ψ T₁) := by
    refine MMP.Intersection.IsDltPair.isKltPair_of_forall_coeff_lt_one
      (MMP.Intersection.IsDltPair.of_le (fp ≫ sW) hdlt2 (fun P => (hBT₂ P).1) (fun P => ?_)
        (isQCartier_of_isQFactorial (fp ≫ sW) hq2 _)) (fun P => (hBT₂ P).2.1)
    change (MMP.Mori.RationalMap.transformDivisor ψ B₁ -
      MMP.Mori.RationalMap.transformDivisor ψ T₁).coeff P ≤
        (MMP.Mori.RationalMap.transformDivisor ψ B₁ -
          t₀ • MMP.Mori.RationalMap.transformDivisor ψ T₁).coeff P
    have := hT₂ P
    have ht1 : t₀ ≤ 1 := by nlinarith
    simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    nlinarith
  -- lc, by crepant invariance through `W`
  have hGq : Divisor.toQDivisor G = (m : ℤ) •
      (Divisor.toQDivisor (MMP.Mori.RationalMap.transformDivisor (X := X₁) f.toRationalMap K₁) +
        MMP.Mori.RationalMap.transformDivisor (X := X₁) f.toRationalMap B₁) := by
    rw [← hfG, ← transformDivisor_toQDivisor, hDm₁, map_zsmul, map_add,
      transformDivisor_toQDivisor]
  have hpairW : MMP.Mori.IsPair sW
      (MMP.Mori.RationalMap.transformDivisor (X := X₁) f.toRationalMap B₁) :=
    ⟨hWn, 4, _, hKW, ⟨m, by exact_mod_cast hm.ne', G, hGq, hGc⟩⟩
  have hlc₂ : MMP.Intersection.IsLogCanonicalPair (fp ≫ sW)
      (MMP.Mori.RationalMap.transformDivisor ψ B₁) :=
    isLogCanonicalPair_of_isPullback_of_isPullback hX₁n hX₂n hfb hfpb hK₁ hK₂ hKW rfl
      (hT1 K₁) hpairW
      ⟨_, qDivisor_isPullback_of_isPullback hGc hpb₁ hm hGq hDm₁
        (forall_map_componentGenericPoint_notMem_supp (f := f) _)⟩
      ⟨_, qDivisor_isPullback_of_isPullback hGc hpb₂ hm hGq hDm₂
        (forall_map_componentGenericPoint_notMem_supp (f := fp) _)⟩ hlc hB₂0
  -- nef
  haveI : Surjective f := by
    refine ⟨Set.range_eq_univ.mp ?_⟩
    rw [← f.isClosedMap.isClosed_range.closure_eq]
    exact f.denseRange.closure_range
  have hnef₂ := isRelativelyNef_of_isPullback (gW := gW) hWn hX₁n hX₂n rfl rfl hGc hpb₁ hpb₂ hm
    hDm₁ hDm₂ (by rw [hfg]; exact hnef)
  rw [hfpg] at hnef₂
  exact ⟨⟨⟨Dm₂, hDm₂c, hDm₂⟩, hK₂, hnef₂, hklt₂, hlc₂, hT₂, hBT₂, hΔ₂'⟩,
    ⟨hfb, hfpb, hfpP, inferInstance, hψ, hgW, hWn, hfpQ, inferInstance, inferInstance,
      inferInstance, inferInstance, hdesc⟩⟩

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

/-- An ample `ℝ`-Cartier divisor on a proper variety is nef over any base. -/
private theorem isRelativelyNef_of_isRelativelyAmple_spec {X Z : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] {A : RDivisor X} (h : MMP.Flips.IsRelativelyAmple sX A) (g : X ⟶ Z) :
    MMP.Flips.IsRelativelyNef ℂ sX g A := by
  obtain ⟨m, r, L, -, hr, hL, hA⟩ := h
  refine ⟨m, r, L, fun j => (hL j).1, hA, fun C _ x hx => ?_⟩
  obtain ⟨hL', d, -, hd, rfl⟩ := hx
  refine Finset.sum_nonneg fun j _ => mul_nonneg (hr j).le ?_
  rw [MMP.Fourfold.Oai4C1.Negativity.eq_degreeOn_of_isCartierIntersectionNumber (hd j)]
  exact_mod_cast (degreeOn_pos_of_isRelativelyAmpleCartier (hL j) C
    fun x _ => Subsingleton.elim _ _).le

/-- An ample scaling boundary for a klt pair over a birational base: an effective `ℝ`-Cartier
`C` with `(X, Δ + C)` klt and `K + Δ + C` nef over `Z`. -/
private theorem exists_scalingBoundary {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    (hQ : IsQFactorial sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {g : X ⟶ Z}
    (hgZ : g ≫ sZ = sX) {Δ : QDivisor X} (hΔ : IsKltPair sX Δ) :
    ∃ C : RDivisor X, (∀ P, 0 ≤ C.coeff P) ∧ IsCartierCombination C ∧
      IsRealKltPair sX (QDivisor.toRDivisor Δ + C) ∧
      MMP.Flips.IsRelativelyNef ℂ sX g (logCanonicalDivisor K (QDivisor.toRDivisor Δ + C)) := by
  classical
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  have hΔ0 : ∀ P, 0 ≤ (QDivisor.toRDivisor Δ).coeff P := fun P => by
    rw [QDivisor.coeff_toRDivisor]; exact_mod_cast hΔ.1.nonneg P
  have hreal : IsRealKltPair sX (QDivisor.toRDivisor Δ) := by
    have hmori := (isKltPair_iff_mori_isKltPair sX hK hΔ.1).1 hΔ
    have hlt := roundDown_nonpos_iff.mp hmori.2.2
    obtain ⟨n', r, L, hL, hpres⟩ := isCartierCombination_of_isQFactorial hQ
      (Divisor.toRDivisor K + QDivisor.toRDivisor Δ)
    refine ⟨hQ.1, fun P => by rw [QDivisor.coeff_toRDivisor]; exact_mod_cast hlt P,
      ⟨4, K, hK, n', r, L, hL, fun Γ => ?_⟩, hΔ.2⟩
    have h := congrArg (fun D : RDivisor X => D.coeff Γ) hpres
    change DivisorWithCoeffs.coeff (Divisor.toRDivisor K + QDivisor.toRDivisor Δ) Γ = _
    rw [h]
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul]
    rfl
  have hdim2 : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X := by rw [hdim]; norm_num
  obtain ⟨l, P, E, h, -, -, -, -, -, hh, -, hklt, hamp⟩ :=
    IsRealKltPair.exists_isRelativelyAmple_add_linearIndependent hQ hX hdim2 hΔ0 hreal
  set H : RDivisor X := ∑ j, h j • Divisor.toRDivisor (Finsupp.single (P j) 1)
  refine ⟨H, fun Q => ?_, ?_, hklt, ?_⟩
  · change (0 : ℝ) ≤ (∑ j, h j • Divisor.toRDivisor (Finsupp.single (P j) 1)) Q
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_nonneg fun j _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul]
    refine mul_nonneg (hh j).1.le ?_
    change (0 : ℝ) ≤ ((Finsupp.single (P j) (1 : ℤ) Q : ℤ) : ℝ)
    rw [Finsupp.single_apply]; split_ifs <;> norm_num
  · obtain ⟨n', r, L, hL, hpres⟩ := isCartierCombination_of_isQFactorial hQ H
    exact ⟨n', r, L, hL, by simpa only [toRDivisor_eq_mapCoeffs] using hpres⟩
  · have h := hamp 4 K hK
    rw [show logCanonicalDivisor K (QDivisor.toRDivisor Δ + H) =
      Divisor.toRDivisor K + QDivisor.toRDivisor Δ + H from (add_assoc _ _ _).symm]
    exact isRelativelyNef_of_isRelativelyAmple_spec h g

/-! ### Birational maps through a common model -/

/-- Let `p : W ⟶ X` and `q : W ⟶ Y` be birational morphisms out of an irreducible scheme. Then
`p` has an inverse `h : X ⤏ W` with `p ∘ h = id` and `q ∘ h : X ⤏ Y` birational: on a dense open
`V ⊆ W` where both `p` and `q` are open immersions, `h` is `(p|_V)⁻¹` and `q ∘ h` is
`q|_V ∘ (p|_V)⁻¹`. -/
private theorem exists_isInverse_and_isBirational_compHom {W X Y : Scheme.{0}}
    [IrreducibleSpace W] {p : W ⟶ X} {q : W ⟶ Y} (hp : IsBirationalMorphism p)
    (hq : IsBirationalMorphism q) :
    ∃ h : X.RationalMap W, MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧
      MMP.Mori.RationalMap.IsBirational (h.compHom q) ∧
      h.compHom p = Scheme.Hom.toRationalMap (𝟙 X) := by
  haveI : Nonempty W := (IrreducibleSpace.isIrreducible_univ W).nonempty.to_subtype.map (·.1)
  haveI := hp.isDominant
  haveI := hq.isDominant
  obtain ⟨A, hA, hAo⟩ := hp.exists_isOpenImmersion
  obtain ⟨B, hB, hBo⟩ := hq.exists_isOpenImmersion
  set V : W.Opens := A ⊓ B
  have hV : (V : Set W).Nonempty := by
    obtain ⟨a, ha, hb⟩ := (IrreducibleSpace.isIrreducible_univ W).isPreirreducible A B A.isOpen
      B.isOpen (by simpa using hA) (by simpa using hB)
    exact ⟨a, hb⟩
  have hVd : Dense (V : Set W) := V.isOpen.dense hV
  haveI : IsOpenImmersion (V.ι ≫ p) := by
    rw [← W.homOfLE_ι (inf_le_left : V ≤ A), Category.assoc]; infer_instance
  haveI : IsOpenImmersion (V.ι ≫ q) := by
    rw [← W.homOfLE_ι (inf_le_right : V ≤ B), Category.assoc]; infer_instance
  haveI : IsDominant V.ι := Opens.isDominant_ι hVd
  let G : W.PartialIso X :=
    { source := V
      dense_source := hVd
      target := (V.ι ≫ p).opensRange
      dense_target := by rw [Scheme.Hom.coe_opensRange]; exact (V.ι ≫ p).denseRange
      iso := (V.ι ≫ p).isoOpensRange }
  let Gq : W.PartialIso Y :=
    { source := V
      dense_source := hVd
      target := (V.ι ≫ q).opensRange
      dense_target := by rw [Scheme.Hom.coe_opensRange]; exact (V.ι ≫ q).denseRange
      iso := (V.ι ≫ q).isoOpensRange }
  have hG : G.toRationalMap = p.toRationalMap := by
    rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
    refine ⟨V, hVd, le_rfl, le_top, ?_⟩
    change W.homOfLE le_rfl ≫ (Scheme.Hom.isoOpensRange (V.ι ≫ p)).hom ≫
        (V.ι ≫ p).opensRange.ι = W.homOfLE (le_top : V ≤ ⊤) ≫ W.topIso.hom ≫ p
    rw [Scheme.Hom.isoOpensRange_hom_ι, Scheme.topIso_hom, Scheme.homOfLE_ι_assoc,
      Scheme.homOfLE_ι_assoc]
  refine ⟨G.symm.toRationalMap, ⟨G, hG, rfl⟩, ⟨G.symm.trans' Gq rfl, ?_⟩, ?_⟩
  · rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
    refine ⟨(V.ι ≫ p).opensRange, G.dense_target, le_rfl, le_rfl, ?_⟩
    change X.homOfLE le_rfl ≫ ((V.ι ≫ p).isoOpensRange.symm ≪≫ W.isoOfEq rfl ≪≫
        (V.ι ≫ q).isoOpensRange).hom ≫ (V.ι ≫ q).opensRange.ι =
      X.homOfLE le_rfl ≫ ((V.ι ≫ p).isoOpensRange.inv ≫ V.ι) ≫ q
    simp [Scheme.Hom.isoOpensRange_hom_ι]
  · rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.Hom.toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff]
    refine ⟨(V.ι ≫ p).opensRange, G.dense_target, le_rfl, le_top, ?_⟩
    change X.homOfLE le_rfl ≫ ((V.ι ≫ p).isoOpensRange.inv ≫ V.ι) ≫ p =
      X.homOfLE (le_top : (V.ι ≫ p).opensRange ≤ ⊤) ≫ X.topIso.hom ≫ 𝟙 X
    have e : (V.ι ≫ p).isoOpensRange.inv ≫ (V.ι ≫ p) = (V.ι ≫ p).opensRange.ι := by
      rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
    rw [Category.assoc, e]
    simp [Scheme.topIso_hom]

/-- The rational map of a composite of morphisms. -/
private theorem toRationalMap_compHom {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f.toRationalMap.compHom g = (f ≫ g).toRationalMap := by
  rw [Scheme.Hom.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap]
  congr 1

/-- `(φ ∘ f) ∘ g = φ ∘ (g ∘ f)` for a rational map `φ` and morphisms `f`, `g`. -/
private theorem compHom_compHom {X Y Z T : Scheme.{0}} (φ : X.RationalMap Y) (f : Y ⟶ Z)
    (g : Z ⟶ T) : (φ.compHom f).compHom g = φ.compHom (f ≫ g) := by
  obtain ⟨φ', rfl⟩ := φ.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap]
  rfl

/-! ### Transforms along composites -/

/-- Partial maps on prime divisors compose along their linear extensions. -/
private theorem mapPrimeDivisors_comp {X Y Z : Scheme.{0}} {R : Type*} [AddCommMonoid R]
    {φ₁ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)}
    {φ₂ : MMP.Mori.PrimeDivisor Y → Option (MMP.Mori.PrimeDivisor Z)}
    {ψ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Z)}
    (h : ∀ E, ψ E = (φ₁ E).bind φ₂) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors ψ D =
      DivisorWithCoeffs.mapPrimeDivisors φ₂ (DivisorWithCoeffs.mapPrimeDivisors φ₁ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | single E r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single, h E]
    rcases φ₁ E with _ | E'
    · simp
    · simp only [Option.bind_some, Option.elim_some]
      rw [DivisorWithCoeffs.mapPrimeDivisors_single]

/-- The transform of a prime divisor along `q ∘ h`, at a prime divisor that `h` sends to a prime
divisor `E'`, is the transform of `E'` along `q`. -/
private theorem transformPrimeDivisor_compHom_of_eq_some {X W Y : Scheme.{0}} [IsReduced X]
    [IsReduced W] [IsSeparated (W ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)]
    {h : X.RationalMap W} (q : W ⟶ Y) {E : MMP.Mori.PrimeDivisor X}
    {E' : MMP.Mori.PrimeDivisor W} (hE : MMP.Mori.RationalMap.transformPrimeDivisor h E = some E') :
    MMP.Mori.RationalMap.transformPrimeDivisor (h.compHom q) E =
      MMP.Mori.RationalMap.transformPrimeDivisor q.toRationalMap E' := by
  obtain ⟨hdef, -⟩ := MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hE
  obtain ⟨g', hP, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  have h1 := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hE g' hg' hP
  have hg'' : (g'.compHom q).toRationalMap = h.compHom q := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg']
  have hP' : E.genericPoint ∈ (g'.compHom q).domain := hP
  have hval : (g'.compHom q).hom ⟨E.genericPoint, hP'⟩ = q E'.genericPoint := by
    rw [h1]; rfl
  have hq1 : E'.genericPoint ∈ q.toPartialMap.domain := trivial
  have hval' : q.toPartialMap.hom ⟨E'.genericPoint, hq1⟩ = q E'.genericPoint := rfl
  rcases hQ : MMP.Mori.RationalMap.transformPrimeDivisor q.toRationalMap E' with _ | Q
  · rcases hL : MMP.Mori.RationalMap.transformPrimeDivisor (h.compHom q) E with _ | Q
    · rfl
    · exfalso
      have h2 := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hL _ hg'' hP'
      rw [hval] at h2
      have h3 : MMP.Mori.RationalMap.transformPrimeDivisor q.toRationalMap E' = some Q :=
        transformPrimeDivisor_eq_some_of_genericPoint_eq' q.toPartialMap rfl hq1
          (by rw [hval', h2])
      rw [hQ] at h3
      exact absurd h3 (by simp)
  · have h2 := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hQ _ rfl hq1
    exact transformPrimeDivisor_eq_some_of_genericPoint_eq' _ hg'' hP'
      (by rw [hval, h2, hval'])

/-- If `h` sends every prime divisor to a prime divisor, transforms along `q ∘ h` are transforms
along `h` followed by transforms along `q`. -/
private theorem transformDivisor_compHom_of_forall {X W Y : Scheme.{0}} [IsReduced X]
    [IsReduced W] [IsSeparated (W ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)]
    {h : X.RationalMap W} (q : W ⟶ Y)
    (hh : ∀ E : MMP.Mori.PrimeDivisor X,
      ∃ E', MMP.Mori.RationalMap.transformPrimeDivisor h E = some E')
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor (h.compHom q) D =
      MMP.Mori.RationalMap.transformDivisor (X := W) q.toRationalMap
        (MMP.Mori.RationalMap.transformDivisor h D) :=
  mapPrimeDivisors_comp (fun E => by
    obtain ⟨E', hE'⟩ := hh E
    rw [hE', Option.bind_some]
    exact transformPrimeDivisor_compHom_of_eq_some q hE') D

/-- Transforms along the identity are the identity. -/
private theorem transformDivisor_id {X : Scheme.{0}} [IsReduced X] [IsSeparated (X ↘ ⊤_ Scheme)]
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor (X := X) (Scheme.Hom.toRationalMap (𝟙 X)) D = D := by
  have hid : ∀ E : MMP.Mori.PrimeDivisor X,
      MMP.Mori.RationalMap.transformPrimeDivisor (X := X) (Scheme.Hom.toRationalMap (𝟙 X)) E =
        some E :=
    fun E => (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff (𝟙 X) E E).mpr
      (by simp)
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h₁ h₂ => rw [map_add, h₁, h₂]
  | single E r => exact MMP.Mori.RationalMap.transformDivisor_single_of_eq_some (hid E) r

/-- **Sections of a proper birational morphism in codimension one.** If `p : W ⟶ X` is a proper
birational morphism of normal varieties and `h : X ⤏ W` satisfies `p ∘ h = id`, then `h` sends
every prime divisor `E` of `X` to the prime divisor `E'` of `W` over it. -/
private theorem exists_transformPrimeDivisor_eq_some_of_compHom_eq_id {k : Type} [Field k]
    {X W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {p : W ⟶ X} (hW : IsNormalVariety k (p ≫ sX)) [IsProper p]
    (hp : IsBirationalMorphism p) {ρ : X.RationalMap W}
    (hρ : ρ.compHom p = Scheme.Hom.toRationalMap (𝟙 X)) (E : MMP.Mori.PrimeDivisor X) :
    ∃ E' : MMP.Mori.PrimeDivisor W, MMP.Mori.RationalMap.transformPrimeDivisor ρ E = some E' ∧
      p E'.genericPoint = E.genericPoint := by
  haveI := hX.1
  haveI := isSeparated_terminal hX
  haveI := isSeparated_terminal hW
  haveI : IsSeparated p := IsSeparated.of_comp p sX
  haveI : IsDominant p := hp.isDominant
  have hdef : E.genericPoint ∈ ρ.domain :=
    MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 X) p ρ hρ
      E.coheight_genericPoint.le
  obtain ⟨g', hP, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  have h1 : p (g'.hom ⟨E.genericPoint, hP⟩) = E.genericPoint :=
    (apply_hom_eq_of_compHom_eq hρ g' hg' ⟨E.genericPoint, hP⟩).trans (by simp)
  obtain ⟨E', hE', -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX hW hp E
  have h2 : g'.hom ⟨E.genericPoint, hP⟩ = E'.genericPoint :=
    eq_of_apply_eq_genericPoint p hp E h1 hE'
  exact ⟨E', transformPrimeDivisor_eq_some_of_genericPoint_eq' g' hg' hP h2.symm, hE'⟩

variable {k : Type} [Field k] {V X₁ X₂ W : Scheme.{0}} [IsIntegral V] [CompactSpace V]
  [IsLocallyNoetherian V] [IsNormal V] [IsIntegral X₁] [CompactSpace X₁]
  [IsLocallyNoetherian X₁] [IsNormal X₁] [IsIntegral X₂] [CompactSpace X₂]
  [IsLocallyNoetherian X₂] [IsNormal X₂] [IsIntegral W] [CompactSpace W]
  [IsLocallyNoetherian W] [IsNormal W] {sV : V ⟶ Spec (.of k)} {s₁ : X₁ ⟶ Spec (.of k)}
  {s₂ : X₂ ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} in
/-- **Transforms along a step, read on a common model.** In the setting of
`transformDivisor_transformDivisor_of_compHom_eq`, let `fp` send the generic point of every prime
divisor to the generic point of a prime divisor, and let `a : V ⟶ X₁`, `b : V ⟶ X₂` be proper
birational morphisms with `f ∘ a = fp ∘ b`. Then `b_* D = ψ_* a_* D` for every divisor `D` on
`V`. -/
private theorem transformDivisor_eq_transformDivisor_of_comp_eq (hV : IsNormalVariety k sV)
    (hX₁ : IsNormalVariety k s₁) (hX₂ : IsNormalVariety k s₂) (hW : IsNormalVariety k sW)
    {f : X₁ ⟶ W} {fp : X₂ ⟶ W} (hfW : f ≫ sW = s₁) (hfpW : fp ≫ sW = s₂) [IsProper f]
    [IsProper fp] (hf : IsBirationalMorphism f) (hfp : IsBirationalMorphism fp)
    {ψ : X₁.RationalMap X₂} (hψ : ψ.compHom fp = f.toRationalMap)
    (hfpQ : ∀ Q : MMP.Mori.PrimeDivisor X₂, ∃ P' : MMP.Mori.PrimeDivisor W,
      fp Q.genericPoint = P'.genericPoint)
    {a : V ⟶ X₁} {b : V ⟶ X₂} [IsProper a] [IsProper b] (ha : IsBirationalMorphism a)
    (hb : IsBirationalMorphism b) (haV : a ≫ s₁ = sV) (hab : a ≫ f = b ≫ fp)
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R V) :
    MMP.Mori.RationalMap.transformDivisor (X := V) b.toRationalMap D =
      MMP.Mori.RationalMap.transformDivisor ψ
        (MMP.Mori.RationalMap.transformDivisor (X := V) a.toRationalMap D) := by
  have hbV : b ≫ s₂ = sV := by
    rw [← hfpW, ← Category.assoc, ← hab, Category.assoc, hfW, haV]
  refine transformDivisor_injective_of_forall_exists hX₂ hW hfpW hfp hfpQ ?_
  rw [transformDivisor_transformDivisor_of_compHom_eq hX₁ hX₂ hW hfW hfpW hf hfp hψ,
    transformDivisor_transformDivisor_of_compHom_eq hV hX₂ hW (f := b ≫ fp)
      (by rw [Category.assoc, hfpW, hbV]) hfpW (MMP.Mori.isBirationalMorphism_comp hb hfp) hfp
      (toRationalMap_compHom b fp),
    transformDivisor_transformDivisor_of_compHom_eq hV hX₁ hW (f := a ≫ f)
      (by rw [Category.assoc, hfW, haV]) hfW (MMP.Mori.isBirationalMorphism_comp ha hf) hf
      (toRationalMap_compHom a f), hab]

/-- Transforms of the zero divisor along the program vanish. -/
private theorem iterTransform_zero {R : Type*} [AddCommMonoid R] {X : Scheme.{0}}
    {Y : ℕ → Scheme.{0}} (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i)) :
    ∀ j, iterTransform φ (0 : DivisorWithCoeffs R X) j = 0
  | 0 => rfl
  | j + 1 => by
    change MMP.Mori.RationalMap.transformDivisor (φ j) (iterTransform φ 0 j) = 0
    rw [iterTransform_zero φ j, map_zero]

/-! ### Relative nefness of `ℚ`- and `ℝ`-divisors -/

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X] in
/-- **`ℚ`-nefness is `ℝ`-nefness.** A `ℚ`-Cartier `ℚ`-divisor which is nef over `Y` is, as an
`ℝ`-divisor, `ℝ`-Cartier and nef over `Y`. -/
private theorem isRelativelyNef_toRDivisor {f : X ⟶ Y} {D : QDivisor X}
    (h : QDivisor.IsRelativelyNef sX f D) :
    MMP.Flips.IsRelativelyNef k sX f (QDivisor.toRDivisor D) := by
  obtain ⟨hD, hh⟩ := h
  set N := D.cartierIndex hD
  set L : Divisor X := (D.cartierIndexSMul hD : Divisor X)
  have hLc : L.IsCartier := (D.cartierIndexSMul hD).2
  refine ⟨1, fun _ => ((1 / N : ℚ) : ℝ), fun _ => L, fun _ => hLc, ?_, fun C hC x hx => ?_⟩
  · rw [toRDivisor_eq_sum_of_toQDivisor_eq (QDivisor.cartierIndex_pos hD)
      (QDivisor.toQDivisor_cartierIndexSMul D hD)]
    simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_inv, one_div]
    rfl
  · obtain ⟨hL', d, -, hd, rfl⟩ := hx
    have key := hh C hC
    rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
      Finsupp.sum_single_index (by simp)] at key
    simp only [smul_eq_mul, mul_one] at key
    rw [Fin.sum_univ_one,
      MMP.Fourfold.Oai4C1.Negativity.eq_degreeOn_of_isCartierIntersectionNumber (hd 0)]
    exact (by exact_mod_cast key :
      (0 : ℝ) ≤ ((1 / N : ℚ) : ℝ) * (L.degreeOn k sX C.ι C.dim_le hLc : ℝ))

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] in
/-- An `ℚ`-Cartier `ℚ`-divisor which is nef over `Y` as an `ℝ`-divisor has nonnegative
intersection number with every proper curve contracted to a point of `Y`. -/
private theorem intersectionNumber_nonneg_of_isRelativelyNef_toRDivisor {f : X ⟶ Y}
    {D : QDivisor X} (hD : D.IsQCartier)
    (h : MMP.Flips.IsRelativelyNef k sX f (QDivisor.toRDivisor D)) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) : 0 ≤ D.intersectionNumber k sX C.ι C.dim_le hD := by
  obtain ⟨m, r, L, hL, hpres, hnn⟩ := h
  have hx : MMP.Flips.IsRIntersectionNumber k sX (QDivisor.toRDivisor D) r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) :=
    ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), hpres,
      fun j => isCartierIntersectionNumber_degreeOn C (L j) (hL j), rfl⟩
  have h0 := hnn C hC _ hx
  set N := D.cartierIndex hD
  set Lc : Divisor X := (D.cartierIndexSMul hD : Divisor X)
  have hLc : Lc.IsCartier := (D.cartierIndexSMul hD).2
  have hpres1 : QDivisor.toRDivisor D =
      ∑ _j : Fin 1, ((1 / N : ℚ) : ℝ) • Divisor.toRDivisor Lc := by
    rw [toRDivisor_eq_sum_of_toQDivisor_eq (QDivisor.cartierIndex_pos hD)
      (QDivisor.toQDivisor_cartierIndexSMul D hD)]
    simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_inv, one_div]
    rfl
  have h1 : MMP.Flips.IsRIntersectionNumber k sX (QDivisor.toRDivisor D)
      (fun _ : Fin 1 => ((1 / N : ℚ) : ℝ)) (fun _ => Lc) C
      (∑ _j : Fin 1, ((1 / N : ℚ) : ℝ) * (Lc.degreeOn k sX C.ι C.dim_le hLc : ℝ)) :=
    ⟨fun _ => hLc, fun _ => Lc.degreeOn k sX C.ι C.dim_le hLc, hpres1,
      fun _ => isCartierIntersectionNumber_degreeOn C Lc hLc, rfl⟩
  have heq := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx h1
  rw [heq, Fin.sum_univ_one] at h0
  rw [QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX C.ι C.dim_le D hD _ hLc
    (QDivisor.toQDivisor_cartierIndexSMul D hD)]
  have h2 : (0 : ℚ) ≤ (1 / N) * (Lc.degreeOn k sX C.ι C.dim_le hLc : ℚ) := by exact_mod_cast h0
  rw [div_eq_mul_one_div, mul_comm]
  exact h2

/-! ### Relative semiampleness from a relatively free Cartier multiple -/

section Conversion

open MMP.Intersection

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

/-- `KCartierDivisor.realization` depends only on the divisor. -/
private theorem realization_congr {X : Scheme.{0}} {c c' : KCartierDivisor ℚ X}
    (e : c = c') (h : ∀ D, ∃ n : ℤ, c D = n) (h' : ∀ D, ∃ n : ℤ, c' D = n) :
    KCartierDivisor.realization c h = KCartierDivisor.realization c' h' := by
  subst e; rfl

/-- A `ℚ`-divisor `Q` with `nQ` the Weil divisor of an `f`-free Cartier divisor is semiample over
the base. -/
private theorem isRelativelySemiample_of_isRelativelyFreeCartier {X Z : Scheme.{0}}
    [IsLocallyNoetherian X] (f : X ⟶ Z) (Q : QDivisor X) (n : ℕ) (hn : 0 < n) (D' : Divisor X)
    (hQ : ∀ P, (D'.coeff P : ℚ) = n * Q.coeff P) (E : X.CartierDivisor)
    (hE : IsWeilDivisorOfCartier E D') (hfree : IsRelativelyFreeCartier f E) :
    QDivisor.IsRelativelySemiample f Q := by
  classical
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨Finsupp.single E ((n : ℚ)⁻¹), fun P => ?_, n, hn, ?_⟩
  · rw [Finsupp.sum_single_index (by simp),
      (isOrderAlong_primeDivisorOrder E P).unique (hE P), hQ P]
    field_simp
  · have hc : (n : ℚ) • Finsupp.single E ((n : ℚ)⁻¹) =
        (Finsupp.single E (1 : ℤ)).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero := by
      rw [Finsupp.smul_single, Finsupp.mapRange_single, smul_eq_mul, mul_inv_cancel₀ hn',
        Int.cast_one]
    refine ⟨fun D => ⟨(Finsupp.single E (1 : ℤ)) D, by rw [hc]; rfl⟩, ?_⟩
    rw [realization_congr hc _ (fun D => ⟨(Finsupp.single E (1 : ℤ)) D, rfl⟩),
      KCartierDivisor.realization_eq_sum, Finsupp.sum_single_index (by simp), one_smul]
    exact hfree

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

/-- A `ℚ`-divisor with a relatively free Cartier multiple is relatively semiample. -/
private theorem isRelativelySemiample_of_isRelativelyFreeDivisor {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (f : X ⟶ Z)
    (D : QDivisor X)
    (h : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • D ∧ L.IsCartier ∧
      IsRelativelyFreeDivisor f L) :
    QDivisor.IsRelativelySemiample f D := by
  obtain ⟨m, hm, L, hL, hLc, hfree⟩ := h
  obtain ⟨E, hE⟩ := exists_isWeilDivisorOfCartier_of_isCartier hLc
  obtain ⟨e⟩ := hE.nonempty_sheaf_iso_divisorialSheaf
  refine isRelativelySemiample_of_isRelativelyFreeCartier f D m hm L (fun P => ?_) E hE
    (epi_counit_of_iso f e hfree)
  have := congrArg (fun Q : QDivisor X => Q.coeff P) hL
  simpa [zsmul_eq_mul] using this

end Conversion

/-- A birational morphism of integral schemes, locally of finite type, is birational onto its
scheme-theoretic image. -/
private theorem isBirationalMorphism_toImage {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [LocallyOfFiniteType f] [QuasiCompact f] (hfb : IsBirationalMorphism f) :
    IsBirationalMorphism f.toImage := by
  have hb := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents Z) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hb (Or.inl ⟨inferInstance, inferInstance⟩)
  have hUV' : U ≤ f.toImage ⁻¹ᵁ (f.imageι ⁻¹ᵁ V) := by
    intro x hx
    change (f.toImage ≫ f.imageι) x ∈ V
    rw [Scheme.Hom.toImage_imageι]
    exact hUV hx
  have hcomp : f.toImage.resLE (f.imageι ⁻¹ᵁ V) U hUV' ≫
      f.imageι.resLE V (f.imageι ⁻¹ᵁ V) le_rfl = f.resLE V U hUV := by
    rw [Scheme.Hom.resLE_comp_resLE]
    simp only [Scheme.Hom.toImage_imageι]
  have hmono : Mono (f.imageι.resLE V (f.imageι ⁻¹ᵁ V) le_rfl) := inferInstance
  have hsplit : IsSplitEpi (f.imageι.resLE V (f.imageι ⁻¹ᵁ V) le_rfl) :=
    ⟨⟨⟨inv (f.resLE V U hUV) ≫ f.toImage.resLE (f.imageι ⁻¹ᵁ V) U hUV', by
      rw [Category.assoc, hcomp, IsIso.inv_hom_id]⟩⟩⟩
  have hiso₂ : IsIso (f.imageι.resLE V (f.imageι ⁻¹ᵁ V) le_rfl) := isIso_of_mono_of_isSplitEpi _
  have hiso₁ : IsIso (f.toImage.resLE (f.imageι ⁻¹ᵁ V) U hUV') := by
    have : IsIso (f.toImage.resLE (f.imageι ⁻¹ᵁ V) U hUV' ≫
        f.imageι.resLE V (f.imageι ⁻¹ᵁ V) le_rfl) := by rw [hcomp]; exact hiso
    exact IsIso.of_isIso_comp_right _ (f.imageι.resLE V (f.imageι ⁻¹ᵁ V) le_rfl)
  obtain ⟨x, hx⟩ := hU.nonempty
  haveI : IrreducibleSpace f.image := by
    have h1 : IsIrreducible (Set.range f.toImage) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ X).image _ f.toImage.continuous.continuousOn
    have h2 := h1.closure
    rw [f.toImage.denseRange.closure_range] at h2
    exact (irreducibleSpace_def _).mpr h2
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE f.toImage U (f.imageι ⁻¹ᵁ V) ⟨x, hx⟩
    ⟨f.toImage x, hUV' hx⟩ hUV' hiso₁

/-- **Semiampleness at the end of the floor-lowering program.** On a `ℚ`-factorial projective
model `X₁` birational over a normal projective `Z`, carrying the invariants `FloorInv` with klt
real scaling boundary `Δ₁` and `K + Δ₁` nef over `Z`, the divisor `K₁ + B₁ - t T₁` is semiample
over `Z` for every rational `0 < t ≤ t₀`. The pair `(X₁, B₁ - t T₁)` is klt as a boundary between
the lc `B₁` and the klt `B₁ - t₀ T₁`, `K₁ + B₁ - t T₁` is a convex combination of the nef `K₁ + B₁`
and `K₁ + B₁ - t₀ T₁`, and the klt basepoint-free theorem with the zero divisor as relatively big
core makes a multiple free. -/
private theorem FloorInv.isRelativelySemiample_sub_smul {X₁ Z : Scheme.{0}} [IsIntegral X₁]
    [CompactSpace X₁] [IsLocallyNoetherian X₁] [IsNormal X₁] {s₁ : X₁ ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {π₁ : X₁ ⟶ Z} {m : ℕ} {t₀ : ℚ} {K₁ KS₁ : Divisor X₁}
    {B₁ T₁ : QDivisor X₁} {Δ₁ : RDivisor X₁} (hI : FloorInv s₁ π₁ m t₀ K₁ B₁ T₁ Δ₁)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ) (hc : π₁ ≫ sZ = s₁)
    (hp : MMP.Mori.IsProjectiveVariety ℂ s₁) (hq' : IsQFactorial s₁)
    (hπb : IsBirationalMorphism π₁) (hKS : ∃ d, KS₁.IsCanonicalDivisor s₁ d)
    (hk' : IsRealKltPair s₁ Δ₁)
    (hnef : MMP.Flips.IsRelativelyNef ℂ s₁ π₁ (logCanonicalDivisor KS₁ Δ₁))
    (ht₀ : 0 < t₀) (ht₀1 : t₀ ≤ 1) {t : ℚ} (ht : 0 < t) (htt : t ≤ t₀) :
    QDivisor.IsRelativelySemiample π₁ (Divisor.toQDivisor K₁ + B₁ - t • T₁) := by
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZn.1
  haveI : IsNormal Z := hZn.2
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  rw [← hI.toRDivisor_eq, logCanonicalDivisor_toRDivisor] at hnef
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ s₁ := hp
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZ
  haveI : QuasiCompact s₁ := hp.toIsVariety.toQuasiCompact
  have hq : ∀ D : QDivisor X₁, D.IsQCartier := isQCartier_of_isQFactorial s₁ hq'
  have hw0 : 0 < t / t₀ := div_pos ht ht₀
  have hw1 : t / t₀ ≤ 1 := (div_le_one ht₀).mpr htt
  have ht₀0 : t₀ ≠ 0 := ht₀.ne'
  -- the boundary `B' - t T'` is klt
  have hklt₀ : IsKltPair s₁ (B₁ - t₀ • T₁) := hI.isKltPair ht₀1 hq' hk'
  have hBt0 : ∀ P, 0 ≤ (B₁ - t • T₁).coeff P := hI.coeff_sub_smul_nonneg (htt.trans ht₀1)
  have hklt : IsKltPair s₁ (B₁ - t • T₁) := by
    refine isKltPair_of_isLogCanonicalPair_of_isKltPair hI.isLogCanonicalPair hklt₀
      (w := ((t / t₀ : ℚ) : ℝ)) (by exact_mod_cast hw0) (fun Γ => ?_)
      ⟨hq'.1, 4, K₁, hI.isCanonicalDivisor, hq _⟩ hBt0 (by exact_mod_cast hw1)
    simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    have ht₀R : (t₀ : ℝ) ≠ 0 := by exact_mod_cast ht₀0
    push_cast
    field_simp
    ring
  -- `K' + B' - t T'` is nef over `Z`
  obtain ⟨d, hKSd⟩ := hKS
  have hd : d = 4 := by
    have h1 := hKSd.topologicalKrullDim_eq
    rw [hI.isCanonicalDivisor.topologicalKrullDim_eq] at h1
    exact_mod_cast h1.symm
  subst hd
  have hlin : Divisor.LinearlyEquivalent (KS₁) (K₁) :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor s₁
      (hq'.1) hKSd hI.isCanonicalDivisor
  have hnefQ : QDivisor.IsRelativelyNef s₁ (π₁)
      (Divisor.toQDivisor (K₁) + (B₁ - t • T₁)) := by
    refine isRelativelyNef_of_intersectionNumber_nonneg s₁ (hq _)
      fun C hC => ?_
    set ι := fun D : QDivisor X₁ =>
      D.intersectionNumber ℂ s₁ C.ι C.dim_le (hq D) with hι
    have hι_add : ∀ D D', ι (D + D') = ι D + ι D' := fun D D' => by
      simp only [hι]
      rw [QDivisor.intersectionNumber_add' ℂ s₁ C.ι C.dim_le D D' (hq D)
        (hq D') (hq _)]
    have hι_smul : ∀ (a : ℚ) D, ι (a • D) = a * ι D := fun a D => by
      simp only [hι]
      rw [MMP.Fourfold.intersectionNumber_smul s₁ C.ι C.dim_le D (hq D) a
        (hq _)]
    have h1 : 0 ≤ ι (Divisor.toQDivisor (K₁) + B₁) :=
      MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg s₁
        hI.isRelativelyNef (hq _) C hC
    have h2 : 0 ≤ ι (Divisor.toQDivisor (K₁) + (B₁ - t₀ • T₁)) := by
      have h3 := intersectionNumber_nonneg_of_isRelativelyNef_toRDivisor (hq _) hnef C hC
      rwa [intersectionNumber_add_eq_of_linearlyEquivalent (sX := s₁) C.ι
        C.dim_le hlin (B₁ - t₀ • T₁) (hq _) (hq _)] at h3
    have hdec : Divisor.toQDivisor (K₁) + (B₁ - t • T₁) =
        (1 - t / t₀) • (Divisor.toQDivisor (K₁) + B₁) +
          (t / t₀) • (Divisor.toQDivisor (K₁) + (B₁ - t₀ • T₁)) := by
      ext P
      simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
        DivisorWithCoeffs.coeff_smul, Finsupp.coe_add, Finsupp.coe_sub, Finsupp.coe_smul,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    show 0 ≤ ι _
    rw [hdec, hι_add, hι_smul, hι_smul]
    exact add_nonneg (mul_nonneg (by linarith) h1) (mul_nonneg hw0.le h2)
  have hnefR := isRelativelyNef_toRDivisor (k := ℂ) hnefQ
  rw [← logCanonicalDivisor_toRDivisor] at hnefR
  -- uniform freeness with the zero divisor as relatively big core
  haveI : IsProper (π₁) := isProper_of_isProjectiveMorphism _
    (isProjectiveMorphism_of_isProjectiveVariety hp hZ _ hc)
  have hbig : (0 : QDivisor X₁).IsRelativelyBig (π₁) :=
    (MMP.Fourfold.isRelativelyPseudoEffective_and_isRelativelyBig_zero_of_isBirationalMorphism_toImage
      s₁ sZ (π₁) hp hq' hZ hZn hc
      (isBirationalMorphism_toImage _ (hπb))).2
  obtain ⟨VQ, -, -, hΔVQ, -, ⟨b, hb, hfree⟩, -⟩ :=
    MMP.Fourfold.QDivisor.IsRelativelyBig.exists_isRelativelyFreeDivisor_nsmul_of_isRelativelyNef
      s₁ sZ hq' (π₁) hc ⟨4, hI.isCanonicalDivisor⟩ hbig
      (fun P => by simp) {B₁ - t • T₁}
      (fun Γ hΓ => by rw [Finset.mem_singleton] at hΓ; subst hΓ; exact hBt0)
      (fun Γ hΓ P => by
        rw [Finset.mem_singleton] at hΓ
        subst hΓ
        have h1 := (hI.coeff_bounds P).2.2
        have h2 := hI.floor_nonneg P
        simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul,
          smul_eq_mul] at h1 h2 ⊢
        nlinarith)
      (fun Γ hΓ => by
        rw [Finset.mem_singleton] at hΓ
        subst hΓ
        refine Finsupp.le_def.mpr fun P => ?_
        simpa [DivisorWithCoeffs.coeff_apply] using hBt0 P)
      (fun Γ hΓ => by rw [Finset.mem_singleton] at hΓ; subst hΓ; exact hklt)
      (Δ := QDivisor.toRDivisor (B₁ - t • T₁))
      (subset_convexHull ℝ _ ⟨B₁ - t • T₁, by simp, rfl⟩) hnefR
  have hNpos := QDivisor.cartierIndex_pos (hq (Divisor.toQDivisor (K₁) + (B₁ - t • T₁)))
  obtain ⟨N, hN⟩ : ∃ N, N = (Divisor.toQDivisor (K₁) + (B₁ - t • T₁)).cartierIndex
      (hq _) := ⟨_, rfl⟩
  rw [← hN] at hNpos
  obtain ⟨Dc, hDc, hDcQ⟩ : ∃ Dc : Divisor X₁, Dc.IsCartier ∧
      Divisor.toQDivisor Dc = (N : ℤ) • (Divisor.toQDivisor (K₁) + (B₁ - t • T₁)) :=
    ⟨_, ((Divisor.toQDivisor (K₁) + (B₁ - t • T₁)).cartierIndexSMul (hq _)).2,
      hN ▸ QDivisor.toQDivisor_cartierIndexSMul _ _⟩
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hcD : (N : ℝ) • (Divisor.toRDivisor (K₁) + QDivisor.toRDivisor (B₁ - t • T₁)) =
      Divisor.toRDivisor Dc := by
    have e1 : Divisor.toRDivisor (K₁) + QDivisor.toRDivisor (B₁ - t • T₁) =
        QDivisor.toRDivisor (Divisor.toQDivisor (K₁) + (B₁ - t • T₁)) :=
      logCanonicalDivisor_toRDivisor _ _
    rw [e1, toRDivisor_eq_sum_of_toQDivisor_eq hNpos hDcQ, Fin.sum_univ_one, smul_smul,
      mul_inv_cancel₀ hN0, one_smul]
  have hfreeD := hfree _ hΔVQ (N : ℝ) (by exact_mod_cast hNpos) Dc hDc hcD
  rw [add_sub_assoc]
  exact isRelativelySemiample_of_isRelativelyFreeDivisor (π₁) _
    ⟨b * N, Nat.mul_pos hb hNpos, (b : ℤ) • Dc,
      by rw [map_zsmul, hDcQ, smul_smul, Nat.cast_mul], hDc.zsmul _, hfreeD⟩

private theorem solution
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    (hQ : IsQFactorial sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X}
    (hB : MMP.Intersection.IsDltPair sX B)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    (hdimZ : topologicalKrullDim Z = 4)
    {g : X ⟶ Z} (hgZ : g ≫ sZ = sX) (hg : IsProjectiveMorphism g) (hgb : IsBirationalMorphism g)
    (hD : QDivisor.IsRelativelyNef sX g (Divisor.toQDivisor K + B)) :
    ∃ t₀ : ℚ, 0 < t₀ ∧
    ∃ (P : RelativeDltProgram sX sZ g K (B - t₀ • Divisor.toQDivisor B.roundDown))
      (BU : ∀ i, QDivisor (P.Y i)),
      P.n ≠ ⊤ ∧ P.IsProjective ∧ ¬ P.hasFinal ∧
      (∀ i : ℕ, (i : ℕ∞) < P.n →
        BU i = MMP.Mori.RationalMap.transformDivisor (P.φ i) (divisorSeq B BU i)) ∧
      (∀ i : ℕ, (i : ℕ∞) ≤ P.n →
        MMP.Intersection.IsLogCanonicalPair (modelStr sX P.sY i) (divisorSeq B BU i) ∧
          IsKltPair (modelStr sX P.sY i)
            (divisorSeq (B - t₀ • Divisor.toQDivisor B.roundDown) P.BY i)) ∧
      (∀ i : ℕ, (i : ℕ∞) < P.n →
        ∃ h : (Divisor.toQDivisor (divisorSeq K P.KY i) + divisorSeq B BU i).IsQCartier,
          ∀ u ∈ P.R i, QDivisor.relativeCurveForm (modelStr sX P.sY i) (modelMap g P.πY i)
            (Divisor.toQDivisor (divisorSeq K P.KY i) + divisorSeq B BU i) h u = 0) ∧
      QDivisor.IsRelativelyNef (modelStr sX P.sY P.n.toNat) (modelMap g P.πY P.n.toNat)
        (Divisor.toQDivisor (divisorSeq K P.KY P.n.toNat) + divisorSeq B BU P.n.toNat) ∧
      ∃ φ : X.RationalMap (modelSeq X P.Y P.n.toNat),
        MMP.Mori.RationalMap.IsBirational φ ∧
        MMP.Flips.RationalMap.IsOver g (modelMap g P.πY P.n.toNat) φ ∧
        (∀ Q : MMP.Mori.PrimeDivisor (modelSeq X P.Y P.n.toNat),
          ∃ E : MMP.Mori.PrimeDivisor X, MMP.Mori.RationalMap.transformPrimeDivisor φ E = some Q) ∧
        divisorSeq B BU P.n.toNat = MMP.Mori.RationalMap.transformDivisor φ B ∧
        divisorSeq (B - t₀ • Divisor.toQDivisor B.roundDown) P.BY P.n.toNat =
          divisorSeq B BU P.n.toNat -
            t₀ • MMP.Mori.RationalMap.transformDivisor φ (Divisor.toQDivisor B.roundDown) ∧
        (∀ t : ℚ, 0 < t → t ≤ t₀ →
          QDivisor.IsRelativelySemiample (modelMap g P.πY P.n.toNat)
            (Divisor.toQDivisor (divisorSeq K P.KY P.n.toNat) + divisorSeq B BU P.n.toNat -
              t • MMP.Mori.RationalMap.transformDivisor φ (Divisor.toQDivisor B.roundDown))) ∧
        haveI : LocallyOfFiniteType sX := hQ.1.1.toLocallyOfFiniteType
        ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
          (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ X) (q : W ⟶ modelSeq X P.Y P.n.toNat)
          (h : X.RationalMap W) (G : RDivisor W),
          IsLogComparisonResolution sX (modelStr sX P.sY P.n.toNat) sW φ K
            (QDivisor.toRDivisor B) (divisorSeq K P.KY P.n.toNat)
            (QDivisor.toRDivisor (divisorSeq B BU P.n.toNat)) p q h G G
 := by
  classical
  have hDq := hD.1
  obtain ⟨m, hm, hmD⟩ := hDq.exists_pos
  set T : QDivisor X := Divisor.toQDivisor B.roundDown with hT
  set t₀ : ℚ := 1 / (4 * (8 * m + 1)) with ht₀def
  have ht₀ : 0 < t₀ := by positivity
  have ht₀1 : t₀ ≤ 1 := by
    rw [ht₀def, div_le_one (by positivity)]
    have : (1 : ℚ) ≤ m := by exact_mod_cast hm
    linarith
  have hklt : IsKltPair sX (B - t₀ • T) := isKltPair_sub_smul_roundDown hQ hB ht₀ ht₀1
  obtain ⟨C, hC0, hCc, hCklt, hCnef⟩ :=
    exists_scalingBoundary hX hdim hQ hK hgZ hklt
  obtain ⟨⟨n, Y, sY, iI, iC, iL, iN, πY, KY, BY, CY, lam, W, sW, f, gW, fp, φ, hmod, hstep,
    hnef⟩, -⟩ :=
    exists_scalingProgram_and_finite_of_isBirationalMorphism sX sZ g hgZ hX hZ hZn hg hgb hQ K hK
      (QDivisor.toRDivisor (B - t₀ • T)) C
      (fun P => by
        rw [QDivisor.coeff_toRDivisor]
        exact_mod_cast
          (floorInv_zero (g := g) (t₀ := t₀) hQ hK hB hmD hD).coeff_sub_smul_nonneg ht₀1 P)
      hC0 (by
        obtain ⟨n', r, L, hL, hpres⟩ := isCartierCombination_of_isQFactorial hQ
          (QDivisor.toRDivisor (B - t₀ • T))
        exact ⟨n', r, L, hL, by simpa only [toRDivisor_eq_mapCoeffs] using hpres⟩)
      hCc hCklt hCnef
  -- the iterated transforms of `B`, `T = ⌊B⌋` and `K` along the program
  set BB : ∀ i, QDivisor (modelSeq X Y i) := iterTransform φ B with hBB
  set TT : ∀ i, QDivisor (modelSeq X Y i) := iterTransform φ T with hTT
  set KK : ∀ i, Divisor (modelSeq X Y i) := iterTransform φ K with hKK
  -- the invariants carried along the program
  have ht₀m : t₀ * (2 * (8 * m + 1)) < 1 := by
    rw [ht₀def, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    have : (0 : ℚ) < 8 * m + 1 := by positivity
    linarith
  -- one step of the program, from a model carrying the invariants
  have hstepI := fun i (hi : i < n) (h : FloorInv (modelStr sX sY i) (modelMap g πY i) m t₀
      (KK i) (BB i) (TT i) (divisorSeq (QDivisor.toRDivisor (B - t₀ • T)) BY i)) => by
    obtain ⟨hc1, hp1, hq1, hK1, -⟩ := hmod i hi.le
    obtain ⟨hc2, hp2, hq2, -, hk2⟩ := hmod (i + 1) hi
    obtain ⟨-, hW, hfg, hfpg, hneg, -, hdf, hBY, -⟩ := hstep i hi
    exact step (X₂ := Y i) hZ hc1 hp1 hq1 hK1 hc2 hp2 hq2 hk2 hW hfg hfpg hneg hdf hBY hm ht₀ ht₀m h
  have hinv : ∀ j : ℕ, j ≤ n → FloorInv (modelStr sX sY j) (modelMap g πY j) m t₀ (KK j) (BB j)
      (TT j) (divisorSeq (QDivisor.toRDivisor (B - t₀ • T)) BY j) := by
    intro j
    induction j with
    | zero => intro _; exact floorInv_zero hQ hK hB hmD hD
    | succ i ih => intro hi; exact (hstepI i hi (ih (by omega))).2.1
  -- every step is the contraction of a `D`-null negative extremal ray of `NE̅(X_i/Z)`
  have hR := fun i (hi : i < n) => (hstepI i hi (hinv i hi.le)).1
  choose! Rr hRr using hR
  -- the program's canonical divisors: the scaling program's, except the last, which is the
  -- transform of `K`
  let KY' : ∀ i, Divisor (Y i) := fun i => if i + 1 = n then KK (i + 1) else KY i
  have hKY'lt : ∀ j : ℕ, j < n → divisorSeq K KY' j = divisorSeq K KY j :=
    fun j hj => divisorSeq_ite_of_lt K KY KK hj
  have hKY'n : divisorSeq K KY' n = KK n := divisorSeq_ite_self K KY KK rfl n
  have hBTseq : ∀ j, divisorSeq (Y := Y) (B - t₀ • T) (fun i => BB (i + 1) - t₀ • TT (i + 1)) j =
      BB j - t₀ • TT j := divisorSeq_succ (fun j => BB j - t₀ • TT j) rfl
  let P : RelativeDltProgram sX sZ g K (B - t₀ • T) :=
    { n := (n : ℕ∞)
      Y := Y
      sY := sY
      πY := πY
      KY := KY'
      BY := fun i => BB (i + 1) - t₀ • TT (i + 1)
      R := Rr
      Z := W
      sZ := sW
      f := f
      gZ := gW
      fp := fp
      φ := φ
      isRelativeDltModel := fun i hi => by
        have hi' : i ≤ n := ENat.coe_le_coe.mp hi
        obtain ⟨hc, hp, hq, hKc, hk⟩ := hmod i hi'
        have h := hinv i hi'
        have h0 : ∀ P, 0 ≤ (BB i - t₀ • TT i).coeff P := h.coeff_sub_smul_nonneg ht₀1
        have hKc' : ∃ m, Divisor.IsCanonicalDivisor (modelStr sX sY i) m (divisorSeq K KY' i) := by
          rcases hi'.lt_or_eq with hlt | rfl
          · rw [hKY'lt i hlt]; exact hKc
          · rw [hKY'n]; exact ⟨4, h.isCanonicalDivisor⟩
        obtain ⟨m', hm'⟩ := hKc'
        haveI := hZ
        haveI := hp
        exact { isQuasiProjectiveVariety_base := IsProjectiveVariety.isQuasiProjectiveVariety ℂ sZ
                isQuasiProjectiveVariety :=
                  IsProjectiveVariety.isQuasiProjectiveVariety ℂ (modelStr sX sY i)
                comp_eq := hc
                isProjectiveMorphism := isProjectiveMorphism_of_isProjectiveVariety hp hZ _ hc
                isQFactorial := hq
                isCanonicalDivisor := ⟨m', hm'⟩
                isDltPair := hBTseq i ▸ isDltPair_of_isKltPair hm' h0 (h.isKltPair ht₀1 hq hk) }
      isElementaryDltStep := fun i hi => by
        have hi' : i < n := ENat.coe_lt_coe.mp hi
        obtain ⟨hRc, -⟩ := hRr i hi'
        obtain ⟨-, -, -, hfpg, -, -, hdf, -⟩ := hstep i hi'
        rw [← (hinv i hi'.le).toRDivisor_eq, logCanonicalDivisor_toRDivisor] at hdf
        suffices h : ∀ Δ, Δ = BB i - t₀ • TT i → ∀ K', K' = divisorSeq K KY i →
            IsElementaryDltStep (modelStr sX sY i) (modelMap g πY i) (sW i) (sY i) (πY i) K' Δ
              (Rr i) (f i) (gW i) (fp i) (φ i) from h _ (hBTseq i) _ (hKY'lt i hi')
        rintro Δ rfl K' rfl
        exact ⟨hRc, hfpg, hdf⟩
      BY_eq := fun i hi => by
        have hBi : divisorSeq (B - t₀ • T) (fun i => BB (i + 1) - t₀ • TT (i + 1)) i =
            BB i - t₀ • TT i := hBTseq i
        show BB (i + 1) - t₀ • TT (i + 1) = MMP.Mori.RationalMap.transformDivisor (φ i)
          (divisorSeq (B - t₀ • T) (fun i => BB (i + 1) - t₀ • TT (i + 1)) i)
        have hsm := (MMP.Mori.RationalMap.transformDivisorₗ ℚ (φ i)).map_smul t₀ (TT i)
        simp only [MMP.Mori.RationalMap.transformDivisorₗ_apply] at hsm
        rw [hBi, map_sub, hsm]
        rfl
      hasFinal := False
      finalRay := ∅
      T := Z
      sT := sZ
      gT := 𝟙 Z
      g := modelMap g πY n
      final_spec := False.elim }
  have hBBseq : ∀ j, divisorSeq (Y := Y) B (fun i => BB (i + 1)) j = BB j :=
    divisorSeq_succ BB rfl
  refine ⟨t₀, ht₀, P, fun i => BB (i + 1), ENat.coe_ne_top n, ⟨hZ, fun i hi => ?_⟩, id,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
  · exact (hmod i (ENat.coe_le_coe.mp hi)).2.1
  · show BB (i + 1) = MMP.Mori.RationalMap.transformDivisor (φ i)
      (divisorSeq (Y := Y) B (fun i => BB (i + 1)) i)
    rw [hBBseq]; rfl
  · have hi' : i ≤ n := ENat.coe_le_coe.mp hi
    have h := hinv i hi'
    obtain ⟨-, -, hq, -, hk⟩ := hmod i hi'
    refine ⟨?_, ?_⟩
    · show MMP.Intersection.IsLogCanonicalPair (modelStr sX sY i)
        (divisorSeq (Y := Y) B (fun i => BB (i + 1)) i)
      rw [hBBseq]; exact h.isLogCanonicalPair
    · show IsKltPair (modelStr sX sY i)
        (divisorSeq (Y := Y) (B - t₀ • T) (fun i => BB (i + 1) - t₀ • TT (i + 1)) i)
      rw [hBTseq]
      exact h.isKltPair ht₀1 hq hk
  · have hi' : i < n := ENat.coe_lt_coe.mp hi
    obtain ⟨-, h⟩ := hRr i hi'
    show ∃ h : (Divisor.toQDivisor (divisorSeq K KY' i) +
        divisorSeq (Y := Y) B (fun i => BB (i + 1)) i).IsQCartier,
      ∀ u ∈ Rr i, QDivisor.relativeCurveForm (modelStr sX sY i) (modelMap g πY i)
        (Divisor.toQDivisor (divisorSeq K KY' i) + divisorSeq (Y := Y) B (fun i => BB (i + 1)) i)
          h u = 0
    rw [hBBseq, hKY'lt i hi']
    exact h
  · show QDivisor.IsRelativelyNef (modelStr sX sY n) (modelMap g πY n)
      (Divisor.toQDivisor (divisorSeq K KY' n) + divisorSeq (Y := Y) B (fun i => BB (i + 1)) n)
    rw [hKY'n, hBBseq]
    exact (hinv n le_rfl).isRelativelyNef
  · -- the facts of each step
    have hsf := fun i (hi : i < n) => (hstepI i hi (hinv i hi.le)).2.2
    -- the models are birational over `Z`
    haveI : IsIntegral Z := hZn.1.toIsIntegral
    have hlft : ∀ i : ℕ, i < n → LocallyOfFiniteType (gW i) := fun i hi => by
      obtain ⟨-, -, -, -, -, hgWs, hWn, -⟩ := hsf i hi
      haveI := hWn.1.toLocallyOfFiniteType
      haveI : LocallyOfFiniteType (gW i ≫ sZ) := by rw [hgWs]; infer_instance
      exact LocallyOfFiniteType.of_comp (g := sZ) this
    have hπb : ∀ j : ℕ, j ≤ n → IsBirationalMorphism (modelMap g πY j) := by
      intro j
      induction j with
      | zero => intro _; exact hgb
      | succ i ih =>
        intro hi
        obtain ⟨hfb, hfpb, -, -, -, -, hWn, -⟩ := hsf i (by omega)
        obtain ⟨-, -, hfg, hfpg, -⟩ := hstep i (by omega)
        haveI := hWn.1.toIsIntegral
        haveI := hlft i (by omega)
        have hgWb : IsBirationalMorphism (gW i) :=
          MMP.Fourfold.Oai4C1.Main.isBirationalMorphism_of_comp_left (f i) (gW i) hfb
            (hfg ▸ ih (by omega))
        have := MMP.Mori.isBirationalMorphism_comp hfpb hgWb
        rw [hfpg] at this
        exact this
    have hgWb : ∀ i : ℕ, i < n → IsBirationalMorphism (gW i) := fun i hi => by
      obtain ⟨hfb, -, -, -, -, -, hWn, -⟩ := hsf i hi
      obtain ⟨-, -, hfg, -, -⟩ := hstep i hi
      haveI := hWn.1.toIsIntegral
      haveI := hlft i hi
      exact MMP.Fourfold.Oai4C1.Main.isBirationalMorphism_of_comp_left (f i) (gW i) hfb
        (hfg ▸ hπb i hi.le)
    -- a common smooth projective model of all the models over `Z`
    haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZn.1
    haveI : IsNormal Z := hZn.2
    have hXn : ∀ j : Fin (n + 1), IsNormalVariety ℂ (modelMap g πY j ≫ sZ) := fun j => by
      rw [(hmod j (Nat.lt_succ_iff.mp j.isLt)).1]
      exact (hmod j (Nat.lt_succ_iff.mp j.isLt)).2.2.1.1
    haveI : ∀ j : Fin (n + 1), IsProper (modelMap g πY j) := fun j =>
      isProper_of_isProjectiveMorphism _ (isProjectiveMorphism_of_isProjectiveVariety
        (hmod j (Nat.lt_succ_iff.mp j.isLt)).2.1 hZ _ (hmod j (Nat.lt_succ_iff.mp j.isLt)).1)
    obtain ⟨W', w', hW'n, hw'b, p, hW's, hw'p, hp, -, hW'proj⟩ :=
      MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq sZ
        (X := fun j : Fin (n + 1) => modelSeq X Y j) (fun j => modelMap g πY j)
        (fun j => hπb j (Nat.lt_succ_iff.mp j.isLt)) hXn (κ := Empty) Empty.elim
        (fun j => j.elim)
    -- the common model `W'` and its morphisms `pr j : W' ⟶ X_j`
    haveI : IsIntegral W' := hW'n.1.toIsIntegral
    haveI : IsNormal W' := hW'n.2
    haveI : LocallyOfFiniteType (w' ≫ sZ) := hW'n.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian W' := LocallyOfFiniteType.isLocallyNoetherian (w' ≫ sZ)
    haveI : QuasiCompact (w' ≫ sZ) := hW'n.1.toQuasiCompact
    haveI : CompactSpace W' := QuasiCompact.compactSpace_of_compactSpace (w' ≫ sZ)
    haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : LocallyOfFiniteType sX := hQ.1.1.toLocallyOfFiniteType
    let pr : ∀ j : ℕ, j ≤ n → (W' ⟶ modelSeq X Y j) := fun j hj =>
      p ⟨j, Nat.lt_succ_of_le hj⟩
    have hprw : ∀ j (hj : j ≤ n), pr j hj ≫ modelMap g πY j = w' := fun j hj =>
      (hp ⟨j, Nat.lt_succ_of_le hj⟩).1
    have hprP : ∀ j (hj : j ≤ n), IsProjectiveMorphism (pr j hj) := fun j hj =>
      (hp ⟨j, Nat.lt_succ_of_le hj⟩).2.1
    have hprb : ∀ j (hj : j ≤ n), IsBirationalMorphism (pr j hj) := fun j hj =>
      (hp ⟨j, Nat.lt_succ_of_le hj⟩).2.2
    haveI : ∀ j (hj : j ≤ n), IsProper (pr j hj) := fun j hj =>
      isProper_of_isProjectiveMorphism _ (hprP j hj)
    have hprs : ∀ j (hj : j ≤ n), pr j hj ≫ modelStr sX sY j = w' ≫ sZ := fun j hj => by
      rw [← (hmod j hj).1, ← Category.assoc, hprw j hj]
    have hXjn : ∀ j, j ≤ n → IsNormalVariety ℂ (modelStr sX sY j) := fun j hj =>
      (hmod j hj).2.2.1.1
    have hW'j : ∀ j (hj : j ≤ n), IsNormalVariety ℂ (pr j hj ≫ modelStr sX sY j) :=
      fun j hj => by rw [hprs j hj]; exact hW'n
    haveI hPn : IsProper (pr n le_rfl) := isProper_of_isProjectiveMorphism _ (hprP n le_rfl)
    haveI := isSeparated_terminal hW'n
    haveI := isSeparated_terminal hQ.1
    haveI : IsSeparated (modelSeq X Y 0 ↘ ⊤_ Scheme) := isSeparated_terminal hQ.1
    haveI := isSeparated_terminal (hXjn n le_rfl)
    have h0n : 0 ≤ n := Nat.zero_le n
    -- instances for `pr 0 : W' ⟶ X`, read with target `X`
    haveI : @IsProper W' X (pr 0 h0n) := isProper_of_isProjectiveMorphism _ (hprP 0 h0n)
    haveI : @IsDominant W' X (pr 0 h0n) := (hprb 0 h0n).isDominant
    haveI : IsSeparated (pr 0 h0n ≫ sX) := (hW'j 0 h0n).1.toIsSeparated
    haveI : @IsSeparated W' X (pr 0 h0n) := IsSeparated.of_comp (pr 0 h0n) sX
    haveI : LocallyOfFiniteType (@CategoryStruct.comp Scheme _ W' X _ (pr 0 h0n) sX) :=
      (hW'j 0 h0n).1.toLocallyOfFiniteType
    -- the models of the common resolution commute with the steps
    have hcomm : ∀ i (hi : i < n), pr i hi.le ≫ f i = pr (i + 1) hi ≫ fp i := by
      intro i hi
      obtain ⟨hfb, hfpb, hfpP, hfP, hψ, hgWs, hWn, hfpQ, hWI, hWL, hWN, hWC, -⟩ := hsf i hi
      obtain ⟨-, hW, hfg, hfpg, -⟩ := hstep i hi
      haveI : IsProper (gW i) := isProper_of_isProjectiveMorphism _
        (isProjectiveMorphism_of_isProjectiveVariety hW hZ _ hgWs)
      haveI : IsDominant ((pr i hi.le ≫ f i) ≫ gW i) := by
        rw [Category.assoc, hfg, hprw i hi.le]; exact hw'b.isDominant
      refine MMP.Fourfold.Oai4C1.Main.eq_of_comp_eq (hgWb i hi) ?_
      have e1 : (pr i hi.le ≫ f i) ≫ gW i = w' := by rw [Category.assoc, hfg, hprw i hi.le]
      have e2 : pr (i + 1) hi ≫ (fp i ≫ gW i) = w' :=
        (congrArg (fun x => pr (i + 1) hi ≫ x) hfpg).trans (hprw (i + 1) hi)
      exact e1.trans ((Category.assoc (pr (i + 1) hi) (fp i) (gW i)).trans e2).symm
    -- transforms along the program are read on `W'`
    have hpush : ∀ i (hi : i < n) {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R W'),
        MMP.Mori.RationalMap.transformDivisor (pr (i + 1) hi).toRationalMap D =
          MMP.Mori.RationalMap.transformDivisor (φ i)
            (MMP.Mori.RationalMap.transformDivisor (pr i hi.le).toRationalMap D) := by
      intro i hi R _ D
      obtain ⟨hfb, hfpb, hfpP, hfP, hψ, hgWs, hWn, hfpQ, hWI, hWL, hWN, hWC, -⟩ := hsf i hi
      obtain ⟨-, -, hfg, hfpg, -⟩ := hstep i hi
      haveI : IsProper (pr i hi.le) := isProper_of_isProjectiveMorphism _ (hprP i hi.le)
      haveI : IsProper (pr (i + 1) hi) := isProper_of_isProjectiveMorphism _ (hprP (i + 1) hi)
      haveI : @IsProper (modelSeq X Y (i + 1)) (W i) (fp i) := hfpP
      have hfW : f i ≫ sW i = modelStr sX sY i := by
        rw [← hgWs, ← Category.assoc, hfg]; exact (hmod i hi.le).1
      have hfpW : fp i ≫ sW i = sY i := by
        rw [← hgWs, ← Category.assoc, hfpg]; exact (hmod (i + 1) hi).1
      exact transformDivisor_eq_transformDivisor_of_comp_eq hW'n (hXjn i hi.le) (hXjn (i + 1) hi)
        hWn hfW hfpW hfb hfpb hψ hfpQ (hprb i hi.le) (hprb (i + 1) hi) (hprs i hi.le)
        (hcomm i hi) D
    have hchain : ∀ j (hj : j ≤ n) {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R W'),
        MMP.Mori.RationalMap.transformDivisor (pr j hj).toRationalMap D =
          iterTransform φ (MMP.Mori.RationalMap.transformDivisor (pr 0 h0n).toRationalMap D) j := by
      intro j
      induction j with
      | zero => intro hj R _ D; rfl
      | succ i ih =>
        intro hj R _ D
        rw [hpush i hj D, ih (Nat.le_of_succ_le hj) D]
        rfl
    -- the inverse `ρ : X ⤏ W'` of `pr 0` and the birational map `φ' = pr n ∘ ρ : X ⤏ X'`
    obtain ⟨ρ, hρinv, hρb, hρid⟩ := exists_isInverse_and_isBirational_compHom (X := X)
      (hprb 0 h0n) (hprb n le_rfl)
    have hρE := exists_transformPrimeDivisor_eq_some_of_compHom_eq_id hQ.1 (hW'j 0 h0n)
      (hprb 0 h0n) hρid
    have hρpush : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
        MMP.Mori.RationalMap.transformDivisor (pr 0 h0n).toRationalMap
          (MMP.Mori.RationalMap.transformDivisor ρ D) = D := by
      intro R _ D
      exact (transformDivisor_transformDivisor_of_compHom_eq hQ.1 (hW'j 0 h0n) hQ.1
        (Category.id_comp sX) rfl (isBirationalMorphism_of_isIso (𝟙 X)) (hprb 0 h0n) hρid
        D).trans (transformDivisor_id D)
    obtain ⟨φ', hφ'⟩ : ∃ φ' : X.RationalMap (modelSeq X Y n), φ' = ρ.compHom (pr n le_rfl) :=
      ⟨_, rfl⟩
    have hφ'D : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
        MMP.Mori.RationalMap.transformDivisor φ' D = iterTransform φ D n := by
      intro R _ D
      rw [hφ', transformDivisor_compHom_of_forall _ (fun E => (hρE E).imp fun _ h => h.1),
        hchain n le_rfl, hρpush]
    haveI : IsDominant (pr 0 h0n) := (hprb 0 h0n).isDominant
    haveI : IsSeparated (pr 0 h0n) := IsSeparated.of_comp (pr 0 h0n) sX
    have hnoext : ∀ Q : MMP.Mori.PrimeDivisor (modelSeq X Y n), ∃ E : MMP.Mori.PrimeDivisor X,
        MMP.Mori.RationalMap.transformPrimeDivisor φ' E = some Q := by
      intro Q
      obtain ⟨E', hE', -, -⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0}
          (hXjn n le_rfl) (hW'j n le_rfl) (hprb n le_rfl) Q
      have hQ' : MMP.Mori.RationalMap.transformPrimeDivisor (pr n le_rfl).toRationalMap E' =
          some Q := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff _ E' Q).mpr hE'
      rcases h0 : MMP.Mori.RationalMap.transformPrimeDivisor (pr 0 h0n).toRationalMap E' with
        _ | E
      · exfalso
        have h1 := hchain n le_rfl (Finsupp.single E' (1 : ℤ))
        have h2 : MMP.Mori.RationalMap.transformDivisor (pr 0 h0n).toRationalMap
            (Finsupp.single E' (1 : ℤ)) = 0 :=
          DivisorWithCoeffs.mapPrimeDivisors_single_of_eq_none h0 1
        rw [MMP.Mori.RationalMap.transformDivisor_single_of_eq_some hQ', h2] at h1
        exact one_ne_zero (Finsupp.single_eq_zero.mp (h1.trans (iterTransform_zero φ n)))
      · have hE := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff _ E' E).mp h0
        obtain ⟨E'', hE'', hpE''⟩ := hρE E
        have : E'' = E' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
          (eq_of_apply_eq_genericPoint (pr 0 h0n) (hprb 0 h0n) E hpE'' hE)
        subst this
        refine ⟨E, ?_⟩
        rw [hφ', transformPrimeDivisor_compHom_of_eq_some _ hE'', hQ']
    have hover : MMP.Flips.RationalMap.IsOver g (modelMap g πY n) φ' := by
      show φ'.compHom (modelMap g πY n) = g.toRationalMap
      have hρid' : ρ.compHom (pr 0 h0n) =
          (Scheme.Hom.toRationalMap (𝟙 X) : X.RationalMap (modelSeq X Y 0)) := hρid
      rw [hφ', compHom_compHom, hprw n le_rfl, ← hprw 0 h0n, ← compHom_compHom, hρid']
      exact (toRationalMap_compHom (𝟙 X) g).trans (by rw [Category.id_comp])
    have hBn : BB n = MMP.Mori.RationalMap.transformDivisor φ' B := (hφ'D B).symm
    have hTn : TT n = MMP.Mori.RationalMap.transformDivisor φ' T := (hφ'D T).symm
    -- a canonical divisor of `W'` compatible with `K` and with `K'`
    haveI : AlgebraicGeometry.IsVariety ℂ sX := hQ.1.1
    haveI : AlgebraicGeometry.IsVariety ℂ (pr 0 h0n ≫ sX) := (hW'j 0 h0n).1
    obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor (pr 0 h0n ≫ sX) (hW'j 0 h0n) (n := 4)
      (by
        rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (pr 0 h0n ≫ sX)
          (hprb 0 h0n)]
        exact_mod_cast hdim)
    haveI : LocallyOfFiniteType (pr 0 h0n ≫ sX) := (hW'j 0 h0n).1.toLocallyOfFiniteType
    obtain ⟨KW, hKW, hKWp⟩ := MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq
      hQ.1 (f := pr 0 h0n) (hW'j 0 h0n) (hprb 0 h0n) hK hK₀
    have hKWn : MMP.Mori.RationalMap.transformDivisor (pr n le_rfl).toRationalMap KW = KK n := by
      rw [hchain n le_rfl]
      exact congrArg (fun D => iterTransform φ D n) hKWp
    -- the pull-backs of `m (K + B)` and of `m (K' + B')` to `W'` agree
    obtain ⟨Dm₀, hDm₀c, hDm₀⟩ := (hinv 0 h0n).exists_cartier
    obtain ⟨G₀, hG₀⟩ :=
      MMP.Threefold.Bridges.exists_isPullback_of_isDominant (pr 0 h0n) hDm₀c
    have hpbchain : ∀ j (hj : j ≤ n), ∃ Dm : Divisor (modelSeq X Y j), Dm.IsCartier ∧
        Divisor.toQDivisor Dm = (m : ℤ) • (Divisor.toQDivisor (KK j) + BB j) ∧
        ∃ hB, Dm.IsPullback (pr j hj) hB G₀ := by
      intro j
      induction j with
      | zero => intro hj; exact ⟨Dm₀, hDm₀c, hDm₀, _, hG₀⟩
      | succ i ih =>
        intro hj
        obtain ⟨Dm, hDmc, hDmq, hB, hpb⟩ := ih (Nat.le_of_succ_le hj)
        obtain ⟨-, hfpb, -, -, -, -, -, -, hWI, hWL, hWN, hWC, hdesc⟩ := hsf i hj
        obtain ⟨Gi, hGic, hB₁, hB₂, Dm', hDm'q, hpf, hpfp⟩ := hdesc Dm hDmc hDmq
        have hDm'c : Dm'.IsCartier := hpfp.pullback_eq hGic ▸ hGic.isCartier_pullback (fp i) hB₂
        haveI : IsDominant (pr (i + 1) hj) := (hprb _ hj).isDominant
        haveI : IsDominant (fp i) := hfpb.isDominant
        haveI : @IsDominant (modelSeq X Y (i + 1)) (W i) (fp i) := hfpb.isDominant
        obtain ⟨G', hG'⟩ :=
          MMP.Threefold.Bridges.exists_isPullback_of_isDominant (pr (i + 1) hj) hDm'c
        haveI : IsDominant (pr (i + 1) hj ≫ fp i) :=
          (MMP.Mori.isBirationalMorphism_comp (hprb (i + 1) hj) hfpb).isDominant
        have hBe := forall_map_componentGenericPoint_notMem_supp (f := pr (i + 1) hj ≫ fp i) Gi
        have e1 := MMP.ProgramBaseChange.divisor_isPullback_comp (hcomm i hj) hpf hpb hBe
        have e2 := MMP.ProgramBaseChange.divisor_isPullback_comp rfl hpfp hG' hBe
        have e3 : G₀ = G' := Divisor.IsPullback.eq hGic e1 e2
        subst e3
        exact ⟨Dm', hDm'c, hDm'q, _, hG'⟩
    -- semiampleness of `K' + B' - t T'` for `0 < t ≤ t₀`
    -- the conclusion
    obtain ⟨Dmn, hDmnc, hDmnq, hBn', hpbn⟩ := hpbchain n le_rfl
    have hRl : MMP.Flips.IsRCartierPullback (pr 0 h0n)
        (MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor B))
        (((m : ℝ)⁻¹) • Divisor.toRDivisor G₀) :=
      ⟨1, fun _ => (m : ℝ)⁻¹, fun _ => Dm₀, fun _ => G₀, fun _ => hDm₀c,
        (logCanonicalDivisor_toRDivisor K B).trans (toRDivisor_eq_sum_of_toQDivisor_eq hm hDm₀),
        fun _ => ⟨_, hG₀⟩, by rw [Fin.sum_univ_one]⟩
    have hRr : MMP.Flips.IsRCartierPullback (pr n le_rfl)
        (MMP.Flips.logCanonicalDivisor (KK n) (QDivisor.toRDivisor (BB n)))
        (((m : ℝ)⁻¹) • Divisor.toRDivisor G₀) :=
      ⟨1, fun _ => (m : ℝ)⁻¹, fun _ => Dmn, fun _ => G₀, fun _ => hDmnc,
        (logCanonicalDivisor_toRDivisor (KK n) (BB n)).trans
          (toRDivisor_eq_sum_of_toQDivisor_eq hm hDmnq),
        fun _ => ⟨_, hpbn⟩, by rw [Fin.sum_univ_one]⟩
    refine ⟨φ', hφ' ▸ hρb, hover, hnoext, ?_, ?_, fun t ht htt => ?_, ?_⟩
    · show divisorSeq (Y := Y) B (fun i => BB (i + 1)) n = _
      rw [hBBseq]
      exact hBn
    · show divisorSeq (Y := Y) (B - t₀ • T) (fun i => BB (i + 1) - t₀ • TT (i + 1)) n =
        divisorSeq (Y := Y) B (fun i => BB (i + 1)) n -
          t₀ • MMP.Mori.RationalMap.transformDivisor φ' T
      rw [hBTseq, hBBseq, ← hTn]
    · show QDivisor.IsRelativelySemiample (modelMap g πY n)
        (Divisor.toQDivisor (divisorSeq K KY' n) + divisorSeq (Y := Y) B (fun i => BB (i + 1)) n -
          t • MMP.Mori.RationalMap.transformDivisor φ' T)
      rw [hKY'n, hBBseq, ← hTn]
      obtain ⟨hc', hp', hq', hKS, hk'⟩ := hmod n le_rfl
      exact (hinv n le_rfl).isRelativelySemiample_sub_smul hZ hZn hc' hp' hq' (hπb n le_rfl) hKS
        hk' hnef ht₀ ht₀1 ht htt
    · refine ⟨W', inferInstance, inferInstance, inferInstance, w' ≫ sZ, pr 0 h0n, pr n le_rfl, ρ,
        ((m : ℝ)⁻¹) • Divisor.toRDivisor G₀, ?_⟩
      have hKWc : KW.IsCanonicalDivisor (w' ≫ sZ) 4 := by
        rw [← hprs 0 h0n]; exact hKW
      have hRr' : MMP.Flips.IsRCartierPullback (pr n le_rfl)
          (MMP.Flips.logCanonicalDivisor (divisorSeq K KY' n)
            (QDivisor.toRDivisor (divisorSeq (Y := Y) B (fun i => BB (i + 1)) n)))
          (((m : ℝ)⁻¹) • Divisor.toRDivisor G₀) := by
        rw [hKY'n, hBBseq]; exact hRr
      exact
        { isVariety := hW'n.1
          isSmoothScheme := hW's
          comp_eq_left := hprs 0 h0n
          comp_eq_right := hprs n le_rfl
          isProjectiveMorphism_left := hprP 0 h0n
          isProjectiveMorphism_right := hprP n le_rfl
          isBirationalMorphism_left := hprb 0 h0n
          isBirationalMorphism_right := hprb n le_rfl
          isInverse := hρinv
          compHom_eq := hφ'.symm
          exists_canonicalDivisor := ⟨4, KW, hKWc, hKWp, hKWn.trans hKY'n.symm⟩
          isRCartierPullback_left := hRl
          isRCartierPullback_right := hRr'
          effective := fun P => by simp
          isExceptional := fun P hP => absurd (by simp) hP }

end Proof_lem_fourfold_nef_dlt_birational_floor_lowering

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **A crepant floor-lowering program with semiample small perturbations.** Let
`g : X ⟶ Z` be a projective birational morphism of normal projective complex fourfolds, `(X, B)`
a `ℚ`-factorial dlt pair with canonical divisor `K` and `K + B` nef over `Z`, and `T = ⌊B⌋`.
There are a rational `t₀ > 0`, a finite projective relative dlt program `P` over `Z` for
`(X, B - t₀T)`, with no fibre-type end, and birational transforms `B_i` of `B` on its models,
such that
* every `(X_i, B_i)` is lc and every `(X_i, B_i - t₀T_i)` is klt;
* every step is null for `K_i + B_i`;
* on the last model `X'`, `K' + B'` is nef over `Z`;
* the birational map `φ : X ⤏ X'` over `Z` extracts no prime divisor, `B' = φ_* B`, the lowered
  boundary is `B' - t₀T'` with `T' = φ_* T`, `K' + B' - tT'` is semiample over `Z` for every
  rational `0 < t ≤ t₀`, and `K + B` and `K' + B'` have the same pull-back to a common
  resolution. -/
@[mmp "lem_fourfold_nef_dlt_birational_floor_lowering"]
public theorem IsDltPair.exists_relativeDltProgram_sub_smul_roundDown
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    (hQ : IsQFactorial sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X}
    (hB : MMP.Intersection.IsDltPair sX B)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    (hdimZ : topologicalKrullDim Z = 4)
    {g : X ⟶ Z} (hgZ : g ≫ sZ = sX) (hg : IsProjectiveMorphism g) (hgb : IsBirationalMorphism g)
    (hD : QDivisor.IsRelativelyNef sX g (Divisor.toQDivisor K + B)) :
    ∃ t₀ : ℚ, 0 < t₀ ∧
    ∃ (P : RelativeDltProgram sX sZ g K (B - t₀ • Divisor.toQDivisor B.roundDown))
      (BU : ∀ i, QDivisor (P.Y i)),
      P.n ≠ ⊤ ∧ P.IsProjective ∧ ¬ P.hasFinal ∧
      (∀ i : ℕ, (i : ℕ∞) < P.n →
        BU i = MMP.Mori.RationalMap.transformDivisor (P.φ i) (divisorSeq B BU i)) ∧
      (∀ i : ℕ, (i : ℕ∞) ≤ P.n →
        MMP.Intersection.IsLogCanonicalPair (modelStr sX P.sY i) (divisorSeq B BU i) ∧
          IsKltPair (modelStr sX P.sY i)
            (divisorSeq (B - t₀ • Divisor.toQDivisor B.roundDown) P.BY i)) ∧
      (∀ i : ℕ, (i : ℕ∞) < P.n →
        ∃ h : (Divisor.toQDivisor (divisorSeq K P.KY i) + divisorSeq B BU i).IsQCartier,
          ∀ u ∈ P.R i, QDivisor.relativeCurveForm (modelStr sX P.sY i) (modelMap g P.πY i)
            (Divisor.toQDivisor (divisorSeq K P.KY i) + divisorSeq B BU i) h u = 0) ∧
      QDivisor.IsRelativelyNef (modelStr sX P.sY P.n.toNat) (modelMap g P.πY P.n.toNat)
        (Divisor.toQDivisor (divisorSeq K P.KY P.n.toNat) + divisorSeq B BU P.n.toNat) ∧
      ∃ φ : X.RationalMap (modelSeq X P.Y P.n.toNat),
        MMP.Mori.RationalMap.IsBirational φ ∧
        MMP.Flips.RationalMap.IsOver g (modelMap g P.πY P.n.toNat) φ ∧
        (∀ Q : MMP.Mori.PrimeDivisor (modelSeq X P.Y P.n.toNat),
          ∃ E : MMP.Mori.PrimeDivisor X, MMP.Mori.RationalMap.transformPrimeDivisor φ E = some Q) ∧
        divisorSeq B BU P.n.toNat = MMP.Mori.RationalMap.transformDivisor φ B ∧
        divisorSeq (B - t₀ • Divisor.toQDivisor B.roundDown) P.BY P.n.toNat =
          divisorSeq B BU P.n.toNat -
            t₀ • MMP.Mori.RationalMap.transformDivisor φ (Divisor.toQDivisor B.roundDown) ∧
        (∀ t : ℚ, 0 < t → t ≤ t₀ →
          QDivisor.IsRelativelySemiample (modelMap g P.πY P.n.toNat)
            (Divisor.toQDivisor (divisorSeq K P.KY P.n.toNat) + divisorSeq B BU P.n.toNat -
              t • MMP.Mori.RationalMap.transformDivisor φ (Divisor.toQDivisor B.roundDown))) ∧
        haveI : LocallyOfFiniteType sX := hQ.1.1.toLocallyOfFiniteType
        ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
          (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ X) (q : W ⟶ modelSeq X P.Y P.n.toNat)
          (h : X.RationalMap W) (G : RDivisor W),
          IsLogComparisonResolution sX (modelStr sX P.sY P.n.toNat) sW φ K
            (QDivisor.toRDivisor B) (divisorSeq K P.KY P.n.toNat)
            (QDivisor.toRDivisor (divisorSeq B BU P.n.toNat)) p q h G G :=
              by revert X Z sX sZ hX hdim hQ K hK B hB hZ hZn hdimZ g hgZ hg hgb hD; first | exact Proof_lem_fourfold_nef_dlt_birational_floor_lowering.solution | exact Proof_lem_fourfold_nef_dlt_birational_floor_lowering.solution _ | exact Proof_lem_fourfold_nef_dlt_birational_floor_lowering.solution _ _ | exact Proof_lem_fourfold_nef_dlt_birational_floor_lowering.solution _ _ _ | exact Proof_lem_fourfold_nef_dlt_birational_floor_lowering.solution _ _ _ _

end MMP.Fourfold

