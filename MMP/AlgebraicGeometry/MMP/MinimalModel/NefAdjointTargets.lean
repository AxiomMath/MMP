module

public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
import MMP.AlgebraicGeometry.Divisor.Negativity.CodimTwoCentres
import MMP.AlgebraicGeometry.Intersection.NumericallyTrivialTrace
import MMP.AlgebraicGeometry.MMP.Abundance.FiniteRepresentationGeneration
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationProperProjective
import MMP.Combinatorics.WeightedGraph.ChainDeterminant

/-!
# Klt perturbations, numerically trivial transforms and nef adjoint targets

Four consequences of log resolutions and the negativity lemma for the fourfold chapter. Effective
`ℚ`-Cartier perturbations `Δ + εE` of a klt pair stay klt for `0 ≤ ε < ε₀`. For a birational
contraction `φ : X ⤏ Y` over `Z` of normal `ℚ`-factorial projective varieties, a divisor
numerically trivial over `Z` has a numerically trivial transform with the same pull-back to every
common resolution. Two nef lc targets of `X` over `Z` contracting the same prime divisors of `X`
have equal adjoint pull-backs to every common model. For a log minimal model `φ` of `(X/Z, B)`
with `K_X + B ≡_Z M ≥ 0`, every prime divisor contracted by `φ` is a component of `M`.

## Main results

* `MMP.Fourfold.exists_pos_forall_isKawamataLogTerminal_add_smul`: effective perturbations of a
  klt pair stay klt on an interval.
* `MMP.Fourfold.eq_of_isRCartierPullback_of_isExceptional_iff`: nef lc targets contracting the
  same source primes are crepant.
* `MMP.Fourfold.isNumericallyTrivialOver_transformDivisor_and_pullback_eq`: numerical triviality
  across a birational contraction.
* `MMP.Fourfold.coeff_ne_zero_of_isRealLogMinimalModel_of_isExceptional`: an effective numerical
  adjoint contains every contracted prime.

## Implementation notes

Log resolutions come from `MMP.Mori.exists_isLogResolution`; the comparison on a common model is
`MMP.Fourfold.nonneg_sub_of_nonneg_transformDivisor_sub`, and the numerical-triviality transport
is `MMP.Fourfold.isNumericallyTrivialOver_transformDivisor_and_isRCartierPullback`. The auxiliary
lemmas of each proof live in the namespace `Proof_<tag>` of its card.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 15
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.30, 2.32
* [C. Birkar, *Existence of log canonical flips and a special LMMP*][BirkarLC], Section 2
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u v

namespace Proof_lem_fourfold_fa15_effective_klt_perturbation

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP MMP.Mori

/-! ### Small rational parameters -/

/-- Finitely many strict inequalities `a i < 1` survive adding `c b i` with `b i ≥ 0` for all
`0 ≤ c ≤ c₀`, for some rational `c₀ > 0`. -/
private theorem exists_pos_forall_add_mul_lt_one {ι : Type*} (s : Finset ι) (a b : ι → ℚ)
    (ha : ∀ i ∈ s, a i < 1) (hb : ∀ i ∈ s, 0 ≤ b i) :
    ∃ c₀ : ℚ, 0 < c₀ ∧ ∀ c, 0 ≤ c → c ≤ c₀ → ∀ i ∈ s, a i + c * b i < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun _ _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert j s hj ih =>
    obtain ⟨c₁, hc₁, h₁⟩ := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
      (fun i hi => hb i (Finset.mem_insert_of_mem hi))
    have haj := ha j (Finset.mem_insert_self j s)
    have hbj := hb j (Finset.mem_insert_self j s)
    refine ⟨min c₁ ((1 - a j) / (2 * (b j + 1))),
      lt_min hc₁ (div_pos (by linarith) (by linarith)), fun c hc0 hc i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have h2 : c ≤ (1 - a i) / (2 * (b i + 1)) := hc.trans (min_le_right _ _)
      have h3 : c * (2 * (b i + 1)) ≤ 1 - a i := (le_div_iff₀ (by linarith)).mp h2
      nlinarith
    · exact h₁ c hc0 (hc.trans (min_le_left _ _)) i hi

/-! ### `ℚ`-divisors as `ℝ`-divisors -/

section Coefficients

variable {X : Scheme.{v}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- Regarding a `ℚ`-divisor as an `ℝ`-divisor commutes with rational scalars. -/
private theorem toRDivisor_qsmul (q : ℚ) (E : QDivisor X) :
    QDivisor.toRDivisor (q • E) = (q : ℝ) • QDivisor.toRDivisor E :=
  DivisorWithCoeffs.ext' fun P => by simp [DivisorWithCoeffs.coeff_smul]

/-- A `ℚ`-Cartier `ℚ`-divisor `E` is `(1/m) C` for a Cartier divisor `C` and an integer `m > 0`,
with `C` effective when `E` is. -/
private theorem exists_toRDivisor_eq_inv_smul {E : QDivisor X} (hE : E.IsQCartier) :
    ∃ (m : ℕ) (C : Divisor X), 0 < m ∧ C.IsCartier ∧ (E.IsEffective → C.IsEffective) ∧
      QDivisor.toRDivisor E = (m : ℝ)⁻¹ • Divisor.toRDivisor C := by
  obtain ⟨m, hm, C, hCE, hC⟩ := hE.exists_pos
  have hCP : ∀ P, (C.coeff P : ℝ) = m * E.coeff P := fun P => by
    have := congrArg (fun F : QDivisor X => ((F.coeff P : ℚ) : ℝ)) hCE
    simpa [DivisorWithCoeffs.coeff_smul] using this
  refine ⟨m, C, hm, hC, fun hEe P => ?_, DivisorWithCoeffs.ext' fun P => ?_⟩
  · have : (0 : ℝ) ≤ C.coeff P := by
      rw [hCP]; exact mul_nonneg (by positivity) (by exact_mod_cast hEe P)
    exact_mod_cast this
  · have : (m : ℝ) ≠ 0 := by positivity
    simp [DivisorWithCoeffs.coeff_smul, hCP]
    field_simp

end Coefficients

/-! ### Discrepancies are affine in the boundary -/

section Affine

variable {k : Type v} [Field k] {X : Scheme.{v}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- Adding `t C` for a Cartier divisor `C` to the boundary changes a log discrepancy of `D` by
`-t · coeff_D(f^*C)`, for one pull-back `f^*C` independent of `t`. -/
private theorem exists_forall_isLogDiscrepancy_add_smul {n : ℕ} {B : RDivisor X}
    {D : DivisorOver k sX} {a : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B D a)
    {C : Divisor X} (hC : C.IsCartier) :
    ∃ e : ℝ, ∀ t : ℝ,
      MMP.Intersection.IsLogDiscrepancy sX n (B + t • Divisor.toRDivisor C) D (a - t * e) := by
  classical
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isIntegral
  have := D.isBirationalMorphism.isDominant
  have : CompactSpace D.Y := (D.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  obtain ⟨hnv, hprop, ω, hω0, hK, m, r, C₁, C₁', hC₁, hrel, hpb, ha⟩ := h
  obtain ⟨C', hC'⟩ := hC.exists_isPullback
    (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f C)
  refine ⟨C'.coeff D.E, fun t => ⟨hnv, hprop, ω, hω0, hK, m + 1, Fin.snoc r t, Fin.snoc C₁ C,
    Fin.snoc C₁' C', ?_, ?_, ?_, ?_⟩⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hC
    · simpa using hC₁ j
  · intro Γ
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul, ← hrel Γ]
    ring
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hB := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f C
      refine ⟨by simpa using hB, ?_⟩
      simpa using hC'
    · simpa using hpb j
  · rw [Fin.sum_univ_castSucc, ha]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring

/-- **Discrepancies are affine on a segment of boundaries.** For a `ℚ`-Cartier `E` and a divisor
`D` over `X` with proper model, `a(D, X, Δ + qE) = (1 - q) a(D, X, Δ) + q a(D, X, Δ + E)`. -/
private theorem isDiscrepancy_add_smul_eq [PerfectField k] {n : ℕ} {K : Divisor X}
    {Δ E : QDivisor X} (hE : E.IsQCartier) {D : DivisorOver k sX} (hD : IsProper D.f) {q : ℚ}
    {a₀ a₁ a : ℚ} (h₀ : IsDiscrepancy sX n K Δ D a₀) (h₁ : IsDiscrepancy sX n K (Δ + E) D a₁)
    (h : IsDiscrepancy sX n K (Δ + q • E) D a) : a = (1 - q) * a₀ + q * a₁ := by
  obtain ⟨m, C, -, hC, -, hEC⟩ := exists_toRDivisor_eq_inv_smul hE
  have hR : ∀ s : ℚ, QDivisor.toRDivisor (Δ + s • E) =
      QDivisor.toRDivisor Δ + ((s : ℝ) * (m : ℝ)⁻¹) • Divisor.toRDivisor C := fun s => by
    rw [map_add, toRDivisor_qsmul, hEC, smul_smul]
  have l₀ := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy h₀ _).2 ⟨hD, rfl⟩
  obtain ⟨e, he⟩ := exists_forall_isLogDiscrepancy_add_smul l₀ hC
  have l₁ := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy h₁ _).2 ⟨hD, rfl⟩
  have l := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy h _).2 ⟨hD, rfl⟩
  rw [show Δ + E = Δ + (1 : ℚ) • E by rw [one_smul], hR] at l₁
  rw [hR] at l
  have e₁ := MMP.Threefold.Bridges.IsLogDiscrepancy.unique l₁ (he _)
  have e₂ := MMP.Threefold.Bridges.IsLogDiscrepancy.unique l (he _)
  have : (a : ℝ) = (1 - q) * a₀ + q * a₁ := by
    push_cast at e₁
    linear_combination e₂ - (q : ℝ) * e₁
  exact_mod_cast this

end Affine

section FlipsAffine

variable {k : Type v} [Field k] {X : Scheme.{v}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- Adding `t C` for an effective Cartier divisor `C` to the boundary changes a discrepancy
computed with choices by `-t e`, for one `e = coeff_E(f^*C) ≥ 0` independent of `t`. -/
private theorem exists_forall_isDiscrepancyWith_add_smul {n : ℕ} {D : RDivisor X}
    {ω : RationalPluriForms sX n 1} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    {E : Flips.ProperDivisorOver k sX} {a : ℝ} (h : Flips.IsDiscrepancyWith sX n D ω r L E a)
    {C : Divisor X} (hC : C.IsCartier) (hCe : C.IsEffective) :
    ∃ e : ℝ, 0 ≤ e ∧ ∀ t : ℝ, Flips.IsDiscrepancyWith sX n (D + t • Divisor.toRDivisor C) ω
      (Fin.snoc r t : Fin (m + 1) → ℝ) (Fin.snoc L C : Fin (m + 1) → Divisor X) E
      (a - t * e) := by
  obtain ⟨hX, hn, hω, hLc, hsum, L', hpb, rfl⟩ := h
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  haveI := E.isProper
  haveI : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  obtain ⟨C', hC'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f hC
  refine ⟨C'.coeff E.E, ?_, fun t => ⟨hX, hn, hω, ?_, ?_, Fin.snoc L' C', ?_, ?_⟩⟩
  · exact_mod_cast MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (V := ⊤) hC
      (fun P _ => hCe P) hC' E.E ((E.E.genericPoint_mem_iff _).mp trivial)
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hC
    · simpa using hLc j
  · rw [Fin.sum_univ_castSucc, ← add_assoc, hsum]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hB := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp E.f C
      refine ⟨by simpa using hB, ?_⟩
      simpa using hC'
    · simpa using hpb j
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring

/-- **Klt is convex along an effective Cartier direction.** If `(X, D)` and `(X, D + cC)` are klt
for an effective Cartier divisor `C`, then so is `(X, D + εC)` for every `0 ≤ ε < c`: a log
discrepancy with respect to `D + εC` is `((c - ε) a_ℓ(F, D) + ε a_ℓ(F, D + cC)) / c`. -/
private theorem IsKawamataLogTerminal.add_smul_of_lt {n : ℕ} {K : Divisor X} {D : RDivisor X}
    {C : Divisor X} (hC : C.IsCartier) (hCe : C.IsEffective) {c ε : ℝ} (hε0 : 0 ≤ ε)
    (hεc : ε < c) (h₀ : Flips.IsKawamataLogTerminal sX n K D)
    (h₁ : Flips.IsKawamataLogTerminal sX n K (D + c • Divisor.toRDivisor C)) :
    Flips.IsKawamataLogTerminal sX n K (D + ε • Divisor.toRDivisor C) := by
  obtain ⟨⟨hX, hBd⟩, hK, hKD, hpos⟩ := h₀
  obtain ⟨⟨-, hBd₁⟩, -, hKc, hpos₁⟩ := h₁
  have hrel : ∀ t : ℝ, D + ε • Divisor.toRDivisor C + t • Divisor.toRDivisor C =
      D + (ε + t) • Divisor.toRDivisor C := fun t => by rw [add_assoc, ← add_smul]
  refine ⟨⟨hX, fun P => ?_⟩, hK, ?_, ?_⟩
  · have hCP : (0 : ℝ) ≤ C.coeff P := by exact_mod_cast hCe P
    have h₁P := (hBd₁ P).2
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
      Divisor.coeff_toRDivisor] at h₁P ⊢
    exact ⟨add_nonneg (hBd P).1 (mul_nonneg hε0 hCP), by nlinarith⟩
  · obtain ⟨m, r, L, hL, hsum⟩ := hKD
    refine ⟨m + 1, Fin.snoc r ε, Fin.snoc L C, Fin.lastCases (by simpa using hC)
      (fun j => by simpa using hL j), ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [← hsum, ← Flips.toRDivisor_eq_mapCoeffs, add_assoc]
  · rintro F hF b ⟨a, ⟨-, -, -, E', ω, m, r, L, hE'F, hω, hw⟩, rfl⟩
    obtain ⟨e, -, he⟩ := exists_forall_isDiscrepancyWith_add_smul hw hC hCe
    have h0 := he (-ε)
    rw [hrel, add_neg_cancel, zero_smul, add_zero] at h0
    have h1 := he (c - ε)
    rw [hrel, add_sub_cancel] at h1
    have b0 := hpos F hF _ ⟨_, ⟨hK, hKD, hF, E', ω, _, _, _, hE'F, hω, h0⟩, rfl⟩
    have b1 := hpos₁ F hF _ ⟨_, ⟨hK, hKc, hF, E', ω, _, _, _, hE'F, hω, h1⟩, rfl⟩
    have key : c * (1 + a) = (c - ε) * (1 + (a - -ε * e)) + ε * (1 + (a - (c - ε) * e)) := by
      ring
    have : 0 < c * (1 + a) := by
      rw [key]; nlinarith [mul_pos (sub_pos.mpr hεc) b0, mul_nonneg hε0 b1.le]
    exact pos_of_mul_pos_right this (by linarith)

end FlipsAffine

/-! ### The crepant boundary on a log resolution -/

section Resolution

variable {k : Type v} [Field k] {X W : Scheme.{v}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

omit [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] in
/-- The generic point of a prime divisor lies on it. -/
private theorem genericPoint_mem_support (F : Mori.PrimeDivisor W) :
    F.genericPoint ∈ F.support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl

omit [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] in
/-- A prime divisor whose generic point lies on a prime divisor `E` is `E`. -/
private theorem eq_of_genericPoint_mem_support {E F : Mori.PrimeDivisor W}
    (hF : F.genericPoint ∈ E.support) : F = E := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hF
  have hs : E.genericPoint ⤳ F.genericPoint := specializes_iff_mem_closure.mpr hF
  by_contra hne
  have := Order.coheight_add_one_le (a := E.genericPoint) (b := F.genericPoint) ?_
  · rw [E.coheight_genericPoint, F.coheight_genericPoint] at this
    norm_num at this
  · refine lt_of_le_not_ge hs fun h' => hne ?_
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (Inseparable.eq (Specializes.antisymm (h' : F.genericPoint ⤳ E.genericPoint) hs))

/-- **The support of a crepant boundary.** Every prime divisor `F` of `W` along which the crepant
boundary of `(X, B)` has nonzero coefficient lies in `Ex(π) ∪ π⁻¹(Supp D)`, for any `ℝ`-divisor
`D` whose support contains that of `B`. -/
private theorem support_subset_of_coeff_ne_zero [PerfectField k] (hX : IsNormalVariety k sX)
    {B : QDivisor X} {D : RDivisor X} (hBD : ∀ P, B.coeff P ≠ 0 → D.coeff P ≠ 0) {π : W ⟶ X}
    (hW : IsNormalVariety k (π ≫ sX)) (hbir : IsBirationalMorphism π) {n : ℕ} {K : Divisor X}
    {BW : QDivisor W} (hBW : IsCrepantBoundary sX n K B π hW hbir BW) (F : Mori.PrimeDivisor W)
    (hF : BW.coeff F ≠ 0) :
    F.support ⊆ ((exceptionalSet π ⊔ D.supp.preimage π.continuous : Closeds W) : Set W) := by
  rw [Closeds.coe_sup]
  by_cases hE : (⟨W, π, hW, hbir, F⟩ : DivisorOver k sX).IsExceptional
  · exact (MMP.Positivity.support_subset_exceptionalSet F hE).trans Set.subset_union_left
  obtain ⟨m, hm, hC, -⟩ := (hBW F).2.2
  obtain ⟨P, hPc, hPd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff
    ⟨hX, (hBW F).2.1, ⟨m, by exact_mod_cast hm.ne', hC⟩⟩ _ hE
  have hBP : D.coeff P ≠ 0 := hBD P fun h => hF (by linarith [(hBW F).eq hPd])
  have hη : π F.genericPoint ∈ (P.support : Set X) := by
    rw [← hPc, DivisorOver.center_eq_closure_genericPoint]
    exact subset_closure rfl
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  refine Set.Subset.trans ?_ Set.subset_union_right
  exact ((Closeds.isClosed (D.supp.preimage π.continuous)).closure_subset_iff.mpr
    (Set.singleton_subset_iff.mpr (DivisorWithCoeffs.support_subset_supp hBP hη)))

end Resolution

/-! ### A rational perturbation -/

section Rational

variable {k : Type v} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{v}}
  {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **Klt survives a small rational effective perturbation** (Kollár–Mori sense). If `(X, Δ)` is
klt with `Δ ≥ 0` and `E ≥ 0` is `ℚ`-Cartier, then `(X, Δ + cE)` is klt for some rational
`c > 0`. -/
private theorem exists_pos_isKltPair_add_smul {n : ℕ} {K : Divisor X} {Δ E : QDivisor X}
    (hΔ : IsKltPair sX n K Δ) (hΔe : Δ.IsEffective) (hE : E.IsEffective) (hEC : E.IsQCartier) :
    ∃ c : ℚ, 0 < c ∧ IsKltPair sX n K (Δ + c • E) := by
  classical
  obtain ⟨⟨hX, hK, hKΔ⟩, hdisc, hround⟩ := hΔ
  have hcoef := roundDown_nonpos_iff.mp hround
  haveI : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  -- a log resolution of `(X, Δ + E)`
  obtain ⟨W, π, hπ⟩ := MMP.Mori.exists_isLogResolution sX hX (QDivisor.toRDivisor (Δ + E))
  obtain ⟨hW, hdimW, -⟩ := hπ.toIsSmoothResolution.isNormalVariety hX
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : LocallyOfFiniteType (π ≫ sX) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX)
  haveI : IsNormal W := hW.2
  haveI : IsProper π := hπ.isProper
  haveI : AlgebraicGeometry.IsVariety k (π ≫ sX) := hW.1
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (π ≫ sX)
  have hπb := hπ.isBirationalMorphism
  have hPq : ∀ q : ℚ, IsPairWith sX n K (Δ + q • E) := fun q =>
    ⟨hX, hK, by rw [← add_assoc]; exact hKΔ.add (Flips.QDivisor.IsQCartier.qsmul hEC q)⟩
  have hP : ∀ q : ℚ, IsPair sX (Δ + q • E) := fun q => ⟨hX, n, K, hK, (hPq q).2.2⟩
  -- the crepant boundaries of `(X, Δ)` and `(X, Δ + E)`, and of `(X, Δ + qE)`
  obtain ⟨B₀, hB₀, -⟩ := ((hP 0).existsUnique_isCrepantBoundary hK π hW hπb).1
  obtain ⟨B₁, hB₁, -⟩ := ((hP 1).existsUnique_isCrepantBoundary hK π hW hπb).1
  rw [zero_smul, add_zero] at hB₀
  rw [one_smul] at hB₁
  have hBq : ∀ q : ℚ,
      IsCrepantBoundary sX n K (Δ + q • E) π hW hπb ((1 - q) • B₀ + q • B₁) := by
    intro q F
    obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy (hP q) hK
      (⟨W, π, hW, hπb, F⟩ : DivisorOver k sX)
    have h := isDiscrepancy_add_smul_eq hEC (D := ⟨W, π, hW, hπb, F⟩) hπ.isProper (hB₀ F)
      (hB₁ F) ha
    convert ha using 1
    rw [h, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_smul, smul_eq_mul, smul_eq_mul]
    ring
  -- the coefficients of `B₀` are `< 1`, and `B₀ ≤ B₁`
  have hB₀lt : ∀ F, B₀.coeff F < 1 := by
    intro F
    by_cases hexc : (⟨W, π, hW, hπb, F⟩ : DivisorOver k sX).IsExceptional
    · have h := lt_of_lt_of_le hdisc (discrep_le hexc (hB₀ F))
      rw [show (-1 : EReal) = ((-1 : ℝ) : EReal) by simp, EReal.coe_lt_coe_iff] at h
      have : (-1 : ℚ) < -B₀.coeff F := by exact_mod_cast h
      linarith
    · obtain ⟨P, -, hPd⟩ :=
        DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff ⟨hX, hK, hKΔ⟩ _ hexc
      have := (hB₀ F).eq hPd
      linarith [hcoef P]
  have hB₀₁ : ∀ F, B₀.coeff F ≤ B₁.coeff F := fun F => by
    have := MMP.Threefold.Mori.discrepancy_antitone_of_add ⟨hX, hK, hKΔ⟩ hE hEC _ (hB₀ F)
      (hB₁ F)
    linarith
  -- the choice of `c`
  obtain ⟨c₁, hc₁, h₁⟩ := exists_pos_forall_add_mul_lt_one (B₀.support ∪ B₁.support)
    B₀.coeff (fun F => B₁.coeff F - B₀.coeff F) (fun F _ => hB₀lt F)
    (fun F _ => by linarith [hB₀₁ F])
  obtain ⟨c₂, hc₂, h₂⟩ := exists_pos_forall_add_mul_lt_one E.support Δ.coeff
    E.coeff (fun P _ => hcoef P) (fun P _ => hE P)
  set c := min c₁ c₂
  have hc : 0 < c := lt_min hc₁ hc₂
  set Bc := (1 - c) • B₀ + c • B₁ with hBc_def
  have hBc : ∀ F, Bc.coeff F < 1 := by
    intro F
    have e : Bc.coeff F = B₀.coeff F + c * (B₁.coeff F - B₀.coeff F) := by
      rw [hBc_def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
        DivisorWithCoeffs.coeff_smul, smul_eq_mul, smul_eq_mul]
      ring
    rw [e]
    by_cases hF : F ∈ B₀.support ∪ B₁.support
    · exact h₁ c hc.le (min_le_left _ _) F hF
    · have h0 : B₀.coeff F = 0 := by
        rw [DivisorWithCoeffs.coeff_apply]
        exact Finsupp.notMem_support_iff.mp fun h => hF (Finset.mem_union_left _ h)
      have h1 : B₁.coeff F = 0 := by
        rw [DivisorWithCoeffs.coeff_apply]
        exact Finsupp.notMem_support_iff.mp fun h => hF (Finset.mem_union_right _ h)
      rw [h0, h1]
      norm_num
  have hΔc : ∀ P, (Δ + c • E).coeff P < 1 := by
    intro P
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    by_cases hP' : P ∈ E.support
    · exact h₂ c hc.le (min_le_right _ _) P hP'
    · have h0 : E.coeff P = 0 := by
        rw [DivisorWithCoeffs.coeff_apply]
        exact Finsupp.notMem_support_iff.mp hP'
      rw [h0, mul_zero, add_zero]
      exact hcoef P
  -- `B_c` is snc
  have hsuppD : ∀ P, (Δ + c • E).coeff P ≠ 0 → (QDivisor.toRDivisor (Δ + E)).coeff P ≠ 0 := by
    intro P h
    rw [QDivisor.coeff_toRDivisor, Rat.cast_ne_zero]
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at h
    rw [DivisorWithCoeffs.coeff_add]
    intro h'
    have h1 := hΔe P
    have h2 := hE P
    have h3 : Δ.coeff P = 0 := by linarith
    have h4 : E.coeff P = 0 := by linarith
    exact h (by rw [h3, h4]; ring)
  have hsupp : ∀ F, Bc.coeff F ≠ 0 → F.support ⊆ ((exceptionalSet π ⊔
      (QDivisor.toRDivisor (Δ + E)).supp.preimage π.continuous : Closeds W) : Set W) :=
    fun F hF => support_subset_of_coeff_ne_zero hX hsuppD hW hπb (hBq c) F hF
  have hsncBc : DivisorWithCoeffs.IsSNC (π ≫ sX) Bc := by
    rcases hπ.isSNCSubset with h | ⟨s, hs, hsnc⟩
    · refine (DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℤ) _
        hπ.isSmoothScheme).of_support_subset fun F hF => ?_
      exfalso
      have hF' : Bc.coeff F ≠ 0 := by
        rwa [DivisorWithCoeffs.coeff_apply, ← Finsupp.mem_support_iff]
      have h1 := hsupp F hF'
      rw [h] at h1
      exact h1 (genericPoint_mem_support F)
    · refine hsnc.of_support_subset fun F hF => ?_
      have hF' : Bc.coeff F ≠ 0 := by
        rwa [DivisorWithCoeffs.coeff_apply, ← Finsupp.mem_support_iff]
      have h1 := hsupp F hF'
      rw [← hs] at h1
      obtain ⟨G, hG, hηG⟩ := Set.mem_iUnion₂.mp (h1 (genericPoint_mem_support F))
      rw [eq_of_genericPoint_mem_support hηG]
      simpa [Finsupp.finsetSum_apply, Finsupp.single_apply] using hG
  -- `(W, B_c)` is klt
  have hdimWn : topologicalKrullDim W = n := hdimW.trans hK.topologicalKrullDim_eq
  obtain ⟨KW, hKW⟩ :=
    exists_isCanonicalDivisor_of_isSmoothScheme (π ≫ sX) hπ.isSmoothScheme hdimWn
  have hkltW := isKltPair_of_isSNC (π ≫ sX) hW hπ.isSmoothScheme hKW hsncBc hBc
  -- a uniform bound on the coefficients of `B_c`
  obtain ⟨δ, hδ, hδ'⟩ := exists_pos_forall_add_mul_lt_one Bc.support Bc.coeff
    (fun _ => 1) (fun F _ => hBc F) (fun _ _ => zero_le_one)
  set δ' := min δ (1 / 2)
  have hδ'0 : 0 < δ' := lt_min hδ (by norm_num)
  have hlow : ∀ F, Bc.coeff F ≤ 1 - δ' := by
    intro F
    by_cases hF : F ∈ Bc.support
    · have := hδ' δ' hδ'0.le (min_le_left _ _) F hF
      simp only [mul_one] at this
      linarith
    · have h0 : Bc.coeff F = 0 := by
        rw [DivisorWithCoeffs.coeff_apply]
        exact Finsupp.notMem_support_iff.mp hF
      have : δ' ≤ 1 / 2 := min_le_right _ _
      linarith
  -- the discrepancy of `(X, Δ + cE)`
  have hdiscc : -1 < discrep sX n K (Δ + c • E) := by
    rw [IsCrepantBoundary.discrep_eq_min (hP c) hK hKW (hBq c)]
    refine lt_min hkltW.2.1 ?_
    refine lt_of_lt_of_le (b := (((-1 + δ' : ℚ) : ℝ) : EReal)) ?_ (le_sInf ?_)
    · rw [show (-1 : EReal) = ((-1 : ℝ) : EReal) by simp, EReal.coe_lt_coe_iff]
      have : (0 : ℝ) < δ' := by exact_mod_cast hδ'0
      push_cast
      linarith
    · rintro _ ⟨F, a, -, ha, rfl⟩
      have := ha.eq (hBq c F)
      rw [EReal.coe_le_coe_iff]
      exact_mod_cast (by linarith [hlow F] : (-1 + δ' : ℚ) ≤ a)
  exact ⟨c, hc, hPq c, hdiscc, roundDown_nonpos_iff.mpr hΔc⟩

end Rational

end Proof_lem_fourfold_fa15_effective_klt_perturbation

namespace MMP.Fourfold

open MMP.Mori

open Proof_lem_fourfold_fa15_effective_klt_perturbation

/-- **Effective perturbations preserve klt on a definite interval.** Let `X` be a normal variety
of dimension `n` over an algebraically closed field of characteristic zero, with canonical divisor
`K`, let `Δ` be a `ℚ`-divisor with `(X, Δ)` Kawamata log terminal, and let `E` be an effective
`ℚ`-Cartier `ℚ`-divisor. Then there is `ε₀ > 0` such that `(X, Δ + εE)` is Kawamata log terminal
for every real `0 ≤ ε < ε₀`. -/
@[mmp "lem_fourfold_fa15_effective_klt_perturbation"]
public theorem exists_pos_forall_isKawamataLogTerminal_add_smul {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] (n : ℕ)
    (K : Divisor X) (Δ E : QDivisor X)
    (hΔ : Flips.IsKawamataLogTerminal sX n K (QDivisor.toRDivisor Δ))
    (hE : E.IsEffective) (hEC : E.IsQCartier) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      Flips.IsKawamataLogTerminal sX n K
        (QDivisor.toRDivisor Δ + ε • QDivisor.toRDivisor E) := by
  obtain ⟨⟨hX, hBd⟩, hK, hKΔ, -⟩ := id hΔ
  have hΔe : Δ.IsEffective := fun P => by
    exact_mod_cast (QDivisor.coeff_toRDivisor Δ P) ▸ (hBd P).1
  have hKΔQ : (Divisor.toQDivisor K + Δ).IsQCartier :=
    Flips.QDivisor.isQCartier_of_isCartierCombination
      (by rwa [map_add, QDivisor.toRDivisor_toQDivisor])
  have hMΔ := (MMP.Fourfold.isKawamataLogTerminal_iff_isKltPair sX n K Δ hX hK hBd hKΔQ).1 hΔ
  obtain ⟨c, hc0, hc⟩ := exists_pos_isKltPair_add_smul hMΔ hΔe hE hEC
  have hBc : Flips.IsBoundary (QDivisor.toRDivisor (Δ + c • E)) := fun P => by
    have := (roundDown_nonpos_iff.mp hc.2.2) P
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
      QDivisor.coeff_toRDivisor] at this ⊢
    exact ⟨by exact_mod_cast add_nonneg (hΔe P) (mul_nonneg hc0.le (hE P)),
      by exact_mod_cast this.le⟩
  have hFc := (MMP.Fourfold.isKawamataLogTerminal_iff_isKltPair sX n K (Δ + c • E) hX hK hBc
    hc.1.2.2).2 hc
  obtain ⟨m, C, hm, hC, hCe, hER⟩ := exists_toRDivisor_eq_inv_smul hEC
  have hsmul : ∀ t : ℝ, t • QDivisor.toRDivisor E = (t * (m : ℝ)⁻¹) • Divisor.toRDivisor C :=
    fun t => by rw [hER, smul_smul]
  rw [map_add, toRDivisor_qsmul, hsmul] at hFc
  refine ⟨c, by exact_mod_cast hc0, fun ε hε0 hεc => ?_⟩
  rw [hsmul]
  exact IsKawamataLogTerminal.add_smul_of_lt hC (hCe hE) (by positivity)
    (mul_lt_mul_of_pos_right hεc (by positivity)) hΔ hFc

/-! ### Points of coheight at most one -/

/-- At a point of coheight at most one of a normal integral scheme the local ring is a valuation
ring. -/
public theorem valuationRing_stalk_of_coheight_le_one {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {y : Y} (hy : Order.coheight y ≤ 1) :
    ValuationRing (Y.presheaf.stalk y) := by
  rcases lt_or_eq_of_le hy with h | h
  · have hmax : IsMax y := Order.coheight_eq_zero.mp (Order.lt_one_iff.mp h)
    have hgen : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes trivial
    have hy' : y ⤳ genericPoint Y := hmax (show y ≤ genericPoint Y from hgen)
    obtain rfl : genericPoint Y = y := (hgen.antisymm hy').eq
    change ValuationRing Y.functionField
    infer_instance
  · have hdim : ringKrullDim (Y.presheaf.stalk y) = 1 := by
      rw [ringKrullDim_stalk_eq_coheight, h]; rfl
    have h5 : IsNoetherianRing (Y.presheaf.stalk y) ∧ IsLocalRing (Y.presheaf.stalk y) ∧
        IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y) ∧
        ringKrullDim (Y.presheaf.stalk y) = 1 :=
      ⟨inferInstance, inferInstance, inferInstance, IsNormal.stalk_normal y, hdim⟩
    have h1 : ∃ _ : IsDomain (Y.presheaf.stalk y), IsDiscreteValuationRing (Y.presheaf.stalk y) :=
      ((isDiscreteValuationRing_tfae (Y.presheaf.stalk y)).out 5 1).mp h5
    have := h1.choose_spec
    infer_instance

/-- **Divisorial images.** If `f : W ⟶ Y` is a dominant morphism of normal integral schemes
inducing an isomorphism of function fields and `f(η_P)` has coheight at most one, then `f(η_P)`
is the generic point of a prime divisor `Q` of `Y` and `𝒪_{Y,Q} ≅ 𝒪_{W,P}`. -/
public theorem exists_primeDivisor_of_coheight_le_one {W Y : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : W ⟶ Y) [IsDominant f] (hf : Function.Bijective (functionFieldMap f))
    (P : MMP.Mori.PrimeDivisor W) (hP : Order.coheight (f P.genericPoint) ≤ 1) :
    ∃ Q : MMP.Mori.PrimeDivisor Y, f P.genericPoint = Q.genericPoint ∧
      IsIso (f.stalkMap P.genericPoint) := by
  have := valuationRing_stalk_of_coheight_le_one hP
  have hiso := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf P.genericPoint
  have hco : Order.coheight (f P.genericPoint) = 1 := by
    have h1 : ringKrullDim (W.presheaf.stalk P.genericPoint) =
        ringKrullDim (Y.presheaf.stalk (f P.genericPoint)) :=
      (ringKrullDim_eq_of_ringEquiv
        (asIso (f.stalkMap P.genericPoint)).commRingCatIsoToRingEquiv).symm
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight,
      P.coheight_genericPoint] at h1
    exact_mod_cast h1.symm
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco, ?_, hiso⟩
  exact (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm

end MMP.Fourfold

namespace Proof_lem_fourfold_nef_lc_targets_same_source_primes

open CategoryTheory AlgebraicGeometry

open MMP.Mori MMP.Fourfold

open MMP.Flips (coe_transform_eq_closure_singleton genericPoint_eq_of_transformPrimeDivisor_eq_some
  transformPrimeDivisor_eq_some_of_genericPoint_eq mapPrimeDivisors_apply_eq_zero_of_forall_ne)

section Generalities

private theorem isSeparated_toTerminal {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- `(φ ∘ f) ∘ g = φ ∘ (g ∘ f)` for a rational map `φ` and morphisms `f`, `g`. -/
private theorem compHom_compHom {X Y Z T : Scheme.{u}} (φ : X.RationalMap Y) (f : Y ⟶ Z)
    (g : Z ⟶ T) : (φ.compHom f).compHom g = φ.compHom (f ≫ g) := by
  obtain ⟨φ', rfl⟩ := φ.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap]
  rfl

open Classical in
/-- The coefficient of `single E r` pushed along `φ` at `P` is `r` if `φ E = P` and `0`
otherwise. -/
private theorem mapPrimeDivisors_single_apply {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y))
    (E : MMP.Mori.PrimeDivisor X) (P : MMP.Mori.PrimeDivisor Y) (r : R) :
    DivisorWithCoeffs.mapPrimeDivisors φ (Finsupp.single E r) P =
      if φ E = some P then r else 0 := by
  classical
  rw [DivisorWithCoeffs.mapPrimeDivisors_single]
  rcases hE : φ E with _ | E'
  · simp
  · by_cases hP : E' = P
    · subst hP
      simp
    · rw [if_neg (mt Option.some.inj hP)]
      exact Finsupp.single_eq_of_ne' hP

/-- Two partial maps on prime divisors that send the same prime divisors to `P₁` and to `P₂`
give the same coefficient at `P₁` and at `P₂` to the push-forward of any divisor. -/
private theorem mapPrimeDivisors_apply_eq_of_iff {X Y₁ Y₂ : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] {φ₁ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y₁)}
    {φ₂ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y₂)}
    {P₁ : MMP.Mori.PrimeDivisor Y₁} {P₂ : MMP.Mori.PrimeDivisor Y₂}
    (h : ∀ E, φ₁ E = some P₁ ↔ φ₂ E = some P₂) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ₁ D P₁ = DivisorWithCoeffs.mapPrimeDivisors φ₂ D P₂ := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, map_add, Finsupp.add_apply, Finsupp.add_apply, hD, hD']
  | single E r =>
    rw [mapPrimeDivisors_single_apply, mapPrimeDivisors_single_apply]
    by_cases hE : φ₁ E = some P₁
    · simp only [hE, (h E).mp hE, if_true]
    · have hE' : ¬ φ₂ E = some P₂ := fun h' => hE ((h E).mpr h')
      simp only [hE, hE', if_false]

/-- Two points over the same point of coheight at most one coincide, for a separated dominant
morphism of normal integral schemes inducing an isomorphism of function fields. -/
private theorem eq_of_apply_eq_of_coheight_le_one {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsSeparated f]
    [IsDominant f] (hf : Function.Bijective (functionFieldMap f)) {x₁ x₂ : X}
    (h : f x₂ = f x₁) (hx : Order.coheight (f x₁) ≤ 1) : x₁ = x₂ := by
  have hv := valuationRing_stalk_of_coheight_le_one hx
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x₁
  have : ValuationRing (Y.presheaf.stalk (f x₂)) := by rwa [h]
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x₂
  exact MMP.Positivity.eq_of_isIso_stalkMap f hf h

end Generalities

section Model

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- Along a prime divisor `P` of `W` over a prime divisor `Γ` of `Y` (for a proper birational
`f : W ⟶ Y`), the pull-back of `K_Y + B` has coefficient `coeff_P K_W + coeff_Γ B`, where
`K_Y = f_* K_W`. -/
private theorem coeff_isRCartierPullback_logCanonicalDivisor {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (hYn : IsNormalVariety k sY) (f : W ⟶ Y) [IsProper f]
    (hWn : IsNormalVariety k (f ≫ sY)) (hfb : IsBirationalMorphism f) {KW : Divisor W}
    {K : Divisor Y} (hK : RationalMap.transformDivisor (X := W) f.toRationalMap KW = K)
    {B : RDivisor Y} {G : RDivisor W}
    (hG : MMP.Flips.IsRCartierPullback f (MMP.Flips.logCanonicalDivisor K B) G)
    {P : MMP.Mori.PrimeDivisor W} {Γ : MMP.Mori.PrimeDivisor Y}
    (hPΓ : f P.genericPoint = Γ.genericPoint) :
    G.coeff P = KW.coeff P + B.coeff Γ := by
  have : IsDominant f := hfb.isDominant
  have := hYn.1
  have := hWn.1
  have : IsSeparated f := IsSeparated.of_comp f sY
  obtain ⟨E, heq, hiso, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hYn hWn hfb Γ
  have hEP : E = P := by
    have := isSeparated_toTerminal sY
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_apply_eq_of_coheight_le_one f hfb.functionFieldMap_bijective (hPΓ.trans heq.symm)
        (by rw [heq]; exact Γ.coheight_genericPoint.le))
  subst hEP
  rw [coeff_eq_of_isRCartierPullback E Γ heq hG, MMP.Flips.logCanonicalDivisor,
    DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, ← hK,
    DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply, htr KW]
  rfl

/-- The log discrepancy of a prime divisor `E` on a model `f : W ⟶ Y` is
`1 + ord_E(f^*ω) - coeff_E(f^*(K + B))`, for a rational top form `ω` with `div_Y(ω) = K`
canonical. -/
private theorem isLogDiscrepancy_of_ordForm {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (hYn : IsNormalVariety k sY) (f : W ⟶ Y) [IsProper f]
    [IsDominant f] (hWn : IsNormalVariety k (f ≫ sY)) (hfb : IsBirationalMorphism f) {n : ℕ}
    {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n) {B : RDivisor Y}
    (ω : RationalPluriForms sY n 1) (hω0 : ω ≠ 0)
    (hωK : ∀ Γ : MMP.Mori.PrimeDivisor Y, Γ.ordForm ω = K.coeff Γ) {G : RDivisor W}
    (hG : MMP.Flips.IsRCartierPullback f (MMP.Flips.logCanonicalDivisor K B) G)
    (E : MMP.Mori.PrimeDivisor W) :
    MMP.Intersection.IsLogDiscrepancy sY n B ⟨W, f, hWn, hfb, E⟩
      (1 + (E.ordForm (pullbackRationalPluriForms sY f ω) : ℝ) - G.coeff E) := by
  obtain ⟨m, r, L, L', hLc, hD, hpbL, rfl⟩ := hG
  refine ⟨hYn, inferInstanceAs (IsProper f), ω, hω0, ⟨K, hK, fun Γ => (hωK Γ).symm⟩, m, r, L, L',
    hLc, fun Γ => ?_, hpbL, ?_⟩
  · have := congrArg (fun D : RDivisor Y => D.coeff Γ) hD
    simp only [MMP.Flips.logCanonicalDivisor, DivisorWithCoeffs.coeff_add,
      Divisor.coeff_toRDivisor, MMP.Flips.coeff_sum_smul_toRDivisor] at this
    rw [← this, hωK]
  · rw [MMP.Flips.coeff_sum_smul_toRDivisor]
    rfl

end Model

/-- A prime divisor with a divisorial transform is not exceptional. -/
private theorem not_isExceptional_of_transformPrimeDivisor_eq_some {X Y : Scheme.{u}}
    {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X} {F : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some F) :
    ¬ MMP.Mori.RationalMap.IsExceptional φ P := by
  rw [MMP.Mori.RationalMap.isExceptional_iff]
  intro hex
  have h2 := hex (MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight,
    ← MMP.Mori.RationalMap.support_transformPrimeDivisor h] at h2
  have h3 := h2 F.genericPoint
    (Proof_lem_fourfold_fa15_effective_klt_perturbation.genericPoint_mem_support F)
  rw [F.coheight_genericPoint] at h3
  exact absurd h3 (by decide)

/-- A prime divisor `R` of `X` goes to a prime divisor `F` of `Y` under `φ = q ∘ h` exactly when
`h(η_R)` is the generic point of the prime divisor `E` of `W` over `F`, for a separated dominant
`q : W ⟶ Y` of normal integral schemes inducing an isomorphism of function fields. -/
private theorem transformPrimeDivisor_eq_some_iff_apply_eq {X W Y : Scheme.{u}} [IsReduced X]
    [IsIntegral W] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (q : W ⟶ Y) [IsSeparated q] [IsDominant q]
    (hq : Function.Bijective (functionFieldMap q)) {h : X.RationalMap W} {φ : X.RationalMap Y}
    (hφ : h.compHom q = φ) (F : MMP.Mori.PrimeDivisor Y) (E : MMP.Mori.PrimeDivisor W)
    (hE : q E.genericPoint = F.genericPoint) (R : MMP.Mori.PrimeDivisor X) (g : X.PartialMap W)
    (hg : g.toRationalMap = h) (hR : R.genericPoint ∈ g.domain) :
    MMP.Mori.RationalMap.transformPrimeDivisor φ R = some F ↔
      g.hom ⟨R.genericPoint, hR⟩ = E.genericPoint := by
  have hgq : (g.compHom q).toRationalMap = φ := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg, hφ]
  refine ⟨fun hRF => ?_, fun hw => ?_⟩
  · have h1 := genericPoint_eq_of_transformPrimeDivisor_eq_some hRF (g.compHom q) hgq hR
    change F.genericPoint = q (g.hom ⟨R.genericPoint, hR⟩) at h1
    exact (eq_of_apply_eq_of_coheight_le_one q hq (h1.symm.trans hE.symm)
      (by rw [hE]; exact F.coheight_genericPoint.le)).symm
  · refine transformPrimeDivisor_eq_some_of_genericPoint_eq (g.compHom q) hgq hR ?_
    change F.genericPoint = q (g.hom ⟨R.genericPoint, hR⟩)
    rw [hw, hE]

/-- If `P` is not exceptional for `φ = q ∘ g`, then `q(g(η_P))` has coheight at most one. -/
private theorem coheight_apply_le_one_of_not_isExceptional {X W Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (q : W ⟶ Y) {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    (g : X.PartialMap W) (hg : (g.compHom q).toRationalMap = φ) (hP : P.genericPoint ∈ g.domain)
    (hnex : ¬ MMP.Mori.RationalMap.IsExceptional φ P) :
    Order.coheight (q (g.hom ⟨P.genericPoint, hP⟩)) ≤ 1 := by
  by_contra h2
  refine hnex (Or.inr ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨_, hP, hg⟩, ?_⟩)
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
  intro x hx
  have hx' : x ∈ (MMP.Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) := hx
  rw [coe_transform_eq_closure_singleton (g.compHom q) hg P hP] at hx'
  have h3 : 2 ≤ Order.coheight (q (g.hom ⟨P.genericPoint, hP⟩)) := by
    simpa [one_add_one_eq_two] using Order.add_one_le_of_lt (not_le.mp h2)
  exact h3.trans (Order.coheight_anti
    (Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hx')))

open Classical in
/-- **One half of the comparison.** With the hypotheses of the statement, the comparison
`q₁^*(K_{Y₁} + B₁) - q₂^*(K_{Y₂} + B₂)` is effective. -/
private theorem nonneg_sub {k : Type u} [Field k] [PerfectField k] {X Y₁ Y₂ Z : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y₁] [IsLocallyNoetherian Y₁] [IsNormal Y₁]
    [IsIntegral Y₂] [IsLocallyNoetherian Y₂] [IsNormal Y₂]
    {s₁ : Y₁ ⟶ Spec (.of k)} {s₂ : Y₂ ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {π : X ⟶ Z} {π₁ : Y₁ ⟶ Z} {π₂ : Y₂ ⟶ Z}
    {B : RDivisor X} {KY₁ : Divisor Y₁} {B₁ : RDivisor Y₁} {KY₂ : Divisor Y₂} {B₂ : RDivisor Y₂}
    {φ₁ : X.RationalMap Y₁} {φ₂ : X.RationalMap Y₂}
    (hπ₂ : π₂ ≫ sZ = s₂)
    (hY₁ : IsNormalVariety k s₁) (hY₁p : MMP.Mori.IsProjectiveVariety k s₁)
    (hY₂ : IsNormalVariety k s₂) (hY₂p : MMP.Mori.IsProjectiveVariety k s₂)
    (hK₂ : ∃ n : ℕ, KY₂.IsCanonicalDivisor s₂ n)
    (hlc₂ : IsRealLcPair s₂ B₂)
    (hnef₁ : MMP.Flips.IsRelativelyNef k s₁ π₁ (MMP.Flips.logCanonicalDivisor KY₁ B₁))
    (hnef₂ : MMP.Flips.IsRelativelyNef k s₂ π₂ (MMP.Flips.logCanonicalDivisor KY₂ B₂))
    (hφ₂Z : MMP.Flips.RationalMap.IsOver π π₂ φ₂)
    (hB₁ : ∀ F : MMP.Mori.PrimeDivisor Y₁,
      B₁.coeff F = (MMP.Mori.RationalMap.transformDivisor φ₁ B).coeff F +
        if MMP.Flips.RationalMap.IsInverseExceptional φ₁ F then 1 else 0)
    (hB₂ : ∀ F : MMP.Mori.PrimeDivisor Y₂,
      B₂.coeff F = (MMP.Mori.RationalMap.transformDivisor φ₂ B).coeff F +
        if MMP.Flips.RationalMap.IsInverseExceptional φ₂ F then 1 else 0)
    (hcontr : ∀ P : MMP.Mori.PrimeDivisor X,
      MMP.Mori.RationalMap.IsExceptional φ₁ P ↔ MMP.Mori.RationalMap.IsExceptional φ₂ P)
    {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sW : W ⟶ Spec (.of k)} {q₁ : W ⟶ Y₁} {q₂ : W ⟶ Y₂} {h : X.RationalMap W}
    (hW : MMP.Mori.IsVariety k sW) (hq₁s : q₁ ≫ s₁ = sW) (hq₂s : q₂ ≫ s₂ = sW)
    (hqZ : q₁ ≫ π₁ = q₂ ≫ π₂)
    (hq₁ : IsProjectiveMorphism q₁) (hq₂ : IsProjectiveMorphism q₂)
    (hq₁b : IsBirationalMorphism q₁) (hq₂b : IsBirationalMorphism q₂)
    (hh₁ : h.compHom q₁ = φ₁) (hh₂ : h.compHom q₂ = φ₂)
    {n : ℕ} {KW : Divisor W} (hKW : KW.IsCanonicalDivisor sW n)
    (hKW₁ : MMP.Mori.RationalMap.transformDivisor q₁.toRationalMap KW = KY₁)
    (hKW₂ : MMP.Mori.RationalMap.transformDivisor q₂.toRationalMap KW = KY₂)
    {G₁ G₂ : RDivisor W}
    (hG₁ : MMP.Flips.IsRCartierPullback q₁ (MMP.Flips.logCanonicalDivisor KY₁ B₁) G₁)
    (hG₂ : MMP.Flips.IsRCartierPullback q₂ (MMP.Flips.logCanonicalDivisor KY₂ B₂) G₂) :
    0 ≤ G₁ - G₂ := by
  classical
  -- the varieties and morphisms
  have hY₁v := (MMP.Mori.isProjectiveVariety_iff k s₁).mp hY₁p
  have hY₂v := (MMP.Mori.isProjectiveVariety_iff k s₂).mp hY₂p
  have := hY₁v.1
  have := hY₂v.1
  have := hW
  have : IsProper s₁ := isProper_of_isProjectiveMorphism s₁ hY₁v.2
  have : IsProper s₂ := isProper_of_isProjectiveMorphism s₂ hY₂v.2
  have hsep₁ := isSeparated_toTerminal s₁
  have hsep₂ := isSeparated_toTerminal s₂
  have hWn : IsNormalVariety k sW := ⟨hW, inferInstance⟩
  have hWn₁ : IsNormalVariety k (q₁ ≫ s₁) := by rwa [hq₁s]
  have hWn₂ : IsNormalVariety k (q₂ ≫ s₂) := by rwa [hq₂s]
  have := hWn₁.1
  have := hWn₂.1
  have hWp : MMP.Mori.IsProjectiveVariety k sW := by
    rw [← hq₁s]
    exact (MMP.Mori.isProjectiveVariety_iff k _).mpr ⟨hWn₁.1, IsProjectiveMorphism.comp hq₁ hY₁v.2⟩
  have : IsProper sW := isProper_of_isProjectiveMorphism sW
    ((MMP.Mori.isProjectiveVariety_iff k sW).mp hWp).2
  have : IsProper q₁ := isProper_of_isProjectiveMorphism q₁ hq₁
  have : IsProper q₂ := isProper_of_isProjectiveMorphism q₂ hq₂
  have : IsSeparated q₁ := IsSeparated.of_comp q₁ s₁
  have : IsSeparated q₂ := IsSeparated.of_comp q₂ s₂
  have : IsDominant q₁ := hq₁b.isDominant
  have : IsDominant q₂ := hq₂b.isDominant
  have hq₁bij := hq₁b.functionFieldMap_bijective
  have hq₂bij := hq₂b.functionFieldMap_bijective
  have : CompactSpace Y₂ := QuasiCompact.compactSpace_of_compactSpace s₂
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have : LocallyOfFiniteType s₂ := hY₂v.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (q₂ ≫ s₂) := hWn₂.1.toLocallyOfFiniteType
  -- `h` is defined at the generic point of every prime divisor of `X`
  have hsW : h.compHom sW = (π ≫ sZ).toRationalMap := by
    rw [← hq₂s, ← compHom_compHom, hh₂, ← hπ₂, ← compHom_compHom, hφ₂Z,
      ← Scheme.RationalMap.compHom_toRationalMap, Scheme.Hom.toPartialMap_compHom]
  have hrep : ∀ R : MMP.Mori.PrimeDivisor X, ∃ g : X.PartialMap W,
      g.toRationalMap = h ∧ R.genericPoint ∈ g.domain := by
    intro R
    obtain ⟨g, hg, hg'⟩ := Scheme.RationalMap.mem_domain.mp
      (MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (π ≫ sZ) sW h hsW
        R.coheight_genericPoint.le)
    exact ⟨g, hg', hg⟩
  -- canonical forms on `Y₂`
  obtain ⟨n₂, hKY₂⟩ := hK₂
  have hdim₂ : topologicalKrullDim W = topologicalKrullDim Y₂ :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism s₂ (q₂ ≫ s₂) hq₂b).symm
  obtain rfl : n₂ = n := by
    exact_mod_cast hKY₂.topologicalKrullDim_eq.symm.trans
      (hdim₂.symm.trans hKW.topologicalKrullDim_eq)
  have hKWq : KW.IsCanonicalDivisor (q₂ ≫ s₂) n₂ := by rwa [hq₂s]
  obtain ⟨ω, hω0, hωY, hωW⟩ :=
    MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hY₂ hWn₂ hq₂b hKY₂ hKWq hKW₂
  have hlog : ∀ E : MMP.Mori.PrimeDivisor W, 0 ≤ 1 + (KW.coeff E : ℝ) - G₂.coeff E := by
    intro E
    have ha := isLogDiscrepancy_of_ordForm hY₂ q₂ hWn₂ hq₂b hKY₂ ω hω0
      (fun Γ => by rw [← hωY]; rfl) hG₂ E
    have hord : E.ordForm (pullbackRationalPluriForms s₂ q₂ ω) = KW.coeff E := by
      rw [← hωW]; rfl
    rw [hord] at ha
    exact hlc₂.2.2.2 n₂ _ _ ha
  -- the push-forward of the comparison to `Y₁` is effective
  have hpush : 0 ≤ RationalMap.transformDivisor (X := W) q₁.toRationalMap (G₁ - G₂) := by
    refine Finsupp.le_def.mpr fun F => ?_
    obtain ⟨FW, hFW, hFWiso, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hY₁ hWn₁ hq₁b F
    rw [htr]
    change (0 : ℝ) ≤ (G₁ - G₂).coeff FW
    rw [DivisorWithCoeffs.coeff_sub, sub_nonneg,
      coeff_isRCartierPullback_logCanonicalDivisor hY₁ q₁ hWn₁ hq₁b hKW₁ hG₁ hFW]
    by_cases hF : MMP.Flips.RationalMap.IsInverseExceptional φ₁ F
    · -- a new prime of `Y₁`: compare with the log discrepancy over `(Y₂, B₂)`
      have hB : B₁.coeff F = 1 := by
        rw [hB₁ F, if_pos hF]
        have : (MMP.Mori.RationalMap.transformDivisor φ₁ B).coeff F = 0 :=
          mapPrimeDivisors_apply_eq_zero_of_forall_ne hF B
        rw [this, zero_add]
      rw [hB]
      linarith [hlog FW]
    · -- a prime of `Y₁` coming from `X`: it is retained on `Y₂`
      obtain ⟨P, hP⟩ : ∃ P, MMP.Mori.RationalMap.transformPrimeDivisor φ₁ P = some F := by
        by_contra hne
        push Not at hne
        exact hF hne
      obtain ⟨gP, hgP, hPg⟩ := hrep P
      have hwP :=
        (transformPrimeDivisor_eq_some_iff_apply_eq q₁ hq₁bij hh₁ F FW hFW P gP hgP hPg).mp hP
      have hnex₂ : ¬ MMP.Mori.RationalMap.IsExceptional φ₂ P :=
        (hcontr P).not.mp (not_isExceptional_of_transformPrimeDivisor_eq_some hP)
      have hco : Order.coheight (q₂ FW.genericPoint) ≤ 1 := by
        rw [← hwP]
        exact coheight_apply_le_one_of_not_isExceptional q₂ gP
          (by rw [Scheme.RationalMap.compHom_toRationalMap, hgP, hh₂]) hPg hnex₂
      obtain ⟨F', hF', -⟩ := exists_primeDivisor_of_coheight_le_one q₂ hq₂bij FW hco
      have hiff : ∀ R, MMP.Mori.RationalMap.transformPrimeDivisor φ₁ R = some F ↔
          MMP.Mori.RationalMap.transformPrimeDivisor φ₂ R = some F' := by
        intro R
        obtain ⟨gR, hgR, hRg⟩ := hrep R
        rw [transformPrimeDivisor_eq_some_iff_apply_eq q₁ hq₁bij hh₁ F FW hFW R gR hgR hRg,
          transformPrimeDivisor_eq_some_iff_apply_eq q₂ hq₂bij hh₂ F' FW hF' R gR hgR hRg]
      have hP' : MMP.Mori.RationalMap.transformPrimeDivisor φ₂ P = some F' := (hiff P).mp hP
      have hB₁F : B₁.coeff F = (MMP.Mori.RationalMap.transformDivisor φ₁ B).coeff F := by
        rw [hB₁ F, if_neg hF, add_zero]
      have hB₂F : B₂.coeff F' = (MMP.Mori.RationalMap.transformDivisor φ₂ B).coeff F' := by
        rw [hB₂ F',
          if_neg (fun h' : MMP.Flips.RationalMap.IsInverseExceptional φ₂ F' => h' P hP'), add_zero]
      have htrB : (MMP.Mori.RationalMap.transformDivisor φ₁ B).coeff F =
          (MMP.Mori.RationalMap.transformDivisor φ₂ B).coeff F' :=
        mapPrimeDivisors_apply_eq_of_iff hiff B
      rw [coeff_isRCartierPullback_logCanonicalDivisor hY₂ q₂ hWn₂ hq₂b hKW₂ hG₂ hF', hB₁F,
        hB₂F, htrB]
  -- the comparison is effective
  have hL : MMP.Flips.IsCartierCombination (MMP.Flips.logCanonicalDivisor KY₁ B₁) := by
    obtain ⟨m, r, L, hLc, heq, -⟩ := hnef₁
    exact ⟨m, r, L, hLc, by rw [heq]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  exact MMP.Fourfold.nonneg_sub_of_nonneg_transformDivisor_sub sW s₁ s₂ hWn hWp hY₁ hY₁p hY₂
    hY₂p π₁ π₂ q₁ q₂ hq₁s hq₂s hqZ hq₁ hq₁b hq₂ hq₂b hL hnef₂ hG₁ hG₂ hpush

end Proof_lem_fourfold_nef_lc_targets_same_source_primes

namespace MMP.Fourfold

open MMP.Mori

open Proof_lem_fourfold_nef_lc_targets_same_source_primes

open Classical in
/-- **Nef lc targets contracting the same source primes are crepant.** Let `φ₁ : X ⤏ Y₁` and
`φ₂ : X ⤏ Y₂` be birational maps over `Z`, with `Y_i` normal `ℚ`-factorial projective varieties
over a perfect field `k`, canonical divisors `K_{Y_i}` and boundaries `B_i` such that `(Y_i, B_i)`
is lc, `K_{Y_i} + B_i` is nef over `Z`, and `B_i` is the birational transform `φ_{i*} B` of an
`ℝ`-divisor `B` of `X` plus every prime divisor of `Y_i` exceptional over `X` with coefficient one.
If `φ₁` and `φ₂` contract the same prime divisors of `X`, then for every common model
`q₁ : W ⟶ Y₁`, `q₂ : W ⟶ Y₂` over `Z` (projective birational, with `q_i ∘ h = φ_i` for a rational
map `h : X ⤏ W`) and every canonical divisor `K_W` of `W` with `q_{i*} K_W = K_{Y_i}`, the
pull-backs `q₁^*(K_{Y₁} + B₁)` and `q₂^*(K_{Y₂} + B₂)` are equal. -/
@[mmp "lem_fourfold_nef_lc_targets_same_source_primes"]
public theorem eq_of_isRCartierPullback_of_isExceptional_iff
    {k : Type u} [Field k] [PerfectField k] {X Y₁ Y₂ Z : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y₁] [IsLocallyNoetherian Y₁] [IsNormal Y₁]
    [IsIntegral Y₂] [IsLocallyNoetherian Y₂] [IsNormal Y₂]
    {s₁ : Y₁ ⟶ Spec (.of k)} {s₂ : Y₂ ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {π : X ⟶ Z} {π₁ : Y₁ ⟶ Z} {π₂ : Y₂ ⟶ Z}
    {B : RDivisor X} {KY₁ : Divisor Y₁} {B₁ : RDivisor Y₁} {KY₂ : Divisor Y₂} {B₂ : RDivisor Y₂}
    {φ₁ : X.RationalMap Y₁} {φ₂ : X.RationalMap Y₂}
    (hπ₁ : π₁ ≫ sZ = s₁) (hπ₂ : π₂ ≫ sZ = s₂)
    (hY₁ : IsNormalVariety k s₁) (hY₁p : MMP.Mori.IsProjectiveVariety k s₁)
    (hY₁q : IsQFactorial s₁)
    (hY₂ : IsNormalVariety k s₂) (hY₂p : MMP.Mori.IsProjectiveVariety k s₂)
    (hY₂q : IsQFactorial s₂)
    (hK₁ : ∃ n : ℕ, KY₁.IsCanonicalDivisor s₁ n) (hK₂ : ∃ n : ℕ, KY₂.IsCanonicalDivisor s₂ n)
    (hlc₁ : IsRealLcPair s₁ B₁) (hlc₂ : IsRealLcPair s₂ B₂)
    (hnef₁ : MMP.Flips.IsRelativelyNef k s₁ π₁ (MMP.Flips.logCanonicalDivisor KY₁ B₁))
    (hnef₂ : MMP.Flips.IsRelativelyNef k s₂ π₂ (MMP.Flips.logCanonicalDivisor KY₂ B₂))
    (hφ₁ : MMP.Mori.RationalMap.IsBirational φ₁) (hφ₂ : MMP.Mori.RationalMap.IsBirational φ₂)
    (hφ₁Z : MMP.Flips.RationalMap.IsOver π π₁ φ₁) (hφ₂Z : MMP.Flips.RationalMap.IsOver π π₂ φ₂)
    (hB₁ : ∀ F : MMP.Mori.PrimeDivisor Y₁,
      B₁.coeff F = (MMP.Mori.RationalMap.transformDivisor φ₁ B).coeff F +
        if MMP.Flips.RationalMap.IsInverseExceptional φ₁ F then 1 else 0)
    (hB₂ : ∀ F : MMP.Mori.PrimeDivisor Y₂,
      B₂.coeff F = (MMP.Mori.RationalMap.transformDivisor φ₂ B).coeff F +
        if MMP.Flips.RationalMap.IsInverseExceptional φ₂ F then 1 else 0)
    (hcontr : ∀ P : MMP.Mori.PrimeDivisor X,
      MMP.Mori.RationalMap.IsExceptional φ₁ P ↔ MMP.Mori.RationalMap.IsExceptional φ₂ P)
    {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sW : W ⟶ Spec (.of k)} {q₁ : W ⟶ Y₁} {q₂ : W ⟶ Y₂} {h : X.RationalMap W}
    (hW : MMP.Mori.IsVariety k sW) (hq₁s : q₁ ≫ s₁ = sW) (hq₂s : q₂ ≫ s₂ = sW)
    (hqZ : q₁ ≫ π₁ = q₂ ≫ π₂)
    (hq₁ : IsProjectiveMorphism q₁) (hq₂ : IsProjectiveMorphism q₂)
    (hq₁b : IsBirationalMorphism q₁) (hq₂b : IsBirationalMorphism q₂)
    (hh₁ : h.compHom q₁ = φ₁) (hh₂ : h.compHom q₂ = φ₂)
    {n : ℕ} {KW : Divisor W} (hKW : KW.IsCanonicalDivisor sW n)
    (hKW₁ : MMP.Mori.RationalMap.transformDivisor q₁.toRationalMap KW = KY₁)
    (hKW₂ : MMP.Mori.RationalMap.transformDivisor q₂.toRationalMap KW = KY₂)
    {G₁ G₂ : RDivisor W}
    (hG₁ : MMP.Flips.IsRCartierPullback q₁ (MMP.Flips.logCanonicalDivisor KY₁ B₁) G₁)
    (hG₂ : MMP.Flips.IsRCartierPullback q₂ (MMP.Flips.logCanonicalDivisor KY₂ B₂) G₂) :
    G₁ = G₂ := by
  have h₁₂ : 0 ≤ G₁ - G₂ := nonneg_sub hπ₂ hY₁ hY₁p hY₂ hY₂p hK₂ hlc₂ hnef₁ hnef₂ hφ₂Z hB₁ hB₂
    hcontr hW hq₁s hq₂s hqZ hq₁ hq₂ hq₁b hq₂b hh₁ hh₂ hKW hKW₁ hKW₂ hG₁ hG₂
  have h₂₁ : 0 ≤ G₂ - G₁ := nonneg_sub hπ₁ hY₂ hY₂p hY₁ hY₁p hK₁ hlc₁ hnef₂ hnef₁ hφ₁Z hB₂ hB₁
    (fun P => (hcontr P).symm) hW hq₂s hq₁s hqZ.symm hq₂ hq₁ hq₂b hq₁b hh₂ hh₁ hKW hKW₂ hKW₁
    hG₂ hG₁
  exact le_antisymm (sub_nonneg.mp h₂₁) (sub_nonneg.mp h₁₂)

end MMP.Fourfold

namespace Proof_lem_fourfold_numerically_trivial_birational_contraction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Mori MMP.Fourfold

open Proof_lem_fourfold_nef_lc_targets_same_source_primes (isSeparated_toTerminal)

/-! ### Generalities -/

/-- The rational map of a morphism, composed with a morphism, is the rational map of the
composite. -/
private theorem toRationalMap_compHom {X Z T : Scheme.{u}} (f : X ⟶ Z) (g : Z ⟶ T) :
    f.toRationalMap.compHom g = (f ≫ g).toRationalMap := by
  rw [Scheme.Hom.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.Hom.toPartialMap_compHom]

/-! ### Function fields along a common resolution -/

private theorem partialMap_fromFunctionField_eq {X Y : Scheme.{u}} [IrreducibleSpace X]
    (g : X.PartialMap Y) (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

/-- If a dominant morphism `a : A ⟶ X` of integral schemes is lifted, over the domain `U` of a
partial map `g : X ⇢ Y`, by `p' : A ⟶ Y` (`p' = g ∘ a` on `a⁻¹ U`), then
`Spec k(A) ⟶ Spec k(X) ⟶ Y` is `Spec k(A) ⟶ A ⟶ Y`. -/
private theorem specMap_functionFieldMap_fromFunctionField {X Y A : Scheme.{u}} [IsIntegral X]
    [IsIntegral A] (a : A ⟶ X) [IsDominant a] (g : X.PartialMap Y) (p' : A ⟶ Y)
    (hcomm : (a ⁻¹ᵁ g.domain).ι ≫ p' = (a ∣_ g.domain) ≫ g.hom) :
    Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ g.fromFunctionField =
      A.fromSpecStalk (genericPoint A) ≫ p' := by
  have hx : genericPoint X ∈ g.domain :=
    (genericPoint_specializes _).mem_open g.domain.2 g.dense_domain.nonempty.choose_spec
  have hA : genericPoint A ∈ a ⁻¹ᵁ g.domain := by
    change a (genericPoint A) ∈ g.domain
    rw [map_genericPoint_of_isDominant]
    exact hx
  rw [partialMap_fromFunctionField_eq g hx]
  have c1 : Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫
      g.domain.fromSpecStalkOfMem (genericPoint X) hx =
      (a ⁻¹ᵁ g.domain).fromSpecStalkOfMem (genericPoint A) hA ≫ (a ∣_ g.domain) := by
    rw [← cancel_mono g.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    exact functionFieldMap_fromSpecStalk a
  rw [← Category.assoc, c1, Category.assoc, ← hcomm, ← Category.assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- For a partial isomorphism `e` representing a dominant morphism `p : W ⟶ X` of integral
schemes, `Spec k(W) ⟶ Spec k(X) ⟶ W` along `e⁻¹` is the canonical map. -/
private theorem specMap_functionFieldMap_fromFunctionField_symm {W X : Scheme.{u}} [IsIntegral X]
    [IsIntegral W] (p : W ⟶ X) [IsDominant p] (e : W.PartialIso X)
    (he : e.toRationalMap = p.toRationalMap) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ e.symm.toRationalMap.fromFunctionField =
      W.fromSpecStalk (genericPoint W) := by
  have hW : genericPoint W ∈ e.source :=
    (genericPoint_specializes _).mem_open e.source.2 e.dense_source.nonempty.choose_spec
  have hX : genericPoint X ∈ e.target :=
    (genericPoint_specializes _).mem_open e.target.2 e.dense_target.nonempty.choose_spec
  have h1 := congrArg Scheme.RationalMap.fromFunctionField he
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hW] at h1
  have h1' : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom ≫ e.target.ι =
      W.fromSpecStalk (genericPoint W) ≫ p :=
    h1.trans (Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap p _)
  have c1 : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom =
      Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
        e.target.fromSpecStalkOfMem (genericPoint X) hX := by
    rw [← cancel_mono e.target.ι, Category.assoc, h1', Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι]
    exact (functionFieldMap_fromSpecStalk p).symm
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hX]
  change Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
    e.target.fromSpecStalkOfMem (genericPoint X) hX ≫ e.iso.inv ≫ e.source.ι = _
  rw [← Category.assoc, ← c1, Category.assoc, Iso.hom_inv_id_assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- On a common resolution `p : W ⟶ X`, `q : W ⟶ Y` of `φ : X ⤏ Y` (with `h` inverse to `p`
and `q = φ ∘ h`), `Spec k(W) ⟶ Spec k(X) ⟶ Y` along `φ` is `Spec k(W) ⟶ W ⟶ Y`. -/
private theorem specMap_functionFieldMap_fromFunctionField_of_isInverse {X Y W : Scheme.{u}}
    [IsIntegral X] [IsIntegral W] (φ : X.RationalMap Y) (p : W ⟶ X) (q : W ⟶ Y)
    (h : X.RationalMap W) [IsDominant p]
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (hcomp : h.compHom q = φ) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q := by
  obtain ⟨e, he1, he2⟩ := hinv
  rw [← hcomp, ← he2, MMP.Flips.RationalMap.fromFunctionField_compHom, ← Category.assoc,
    specMap_functionFieldMap_fromFunctionField_symm p e he1]

/-! ### Comparison of the two composites to the base -/

/-- On a common resolution `p : W ⟶ X`, `q : W ⟶ Y` of a map `φ` over `Z`, the two composites
`W ⟶ Z` agree. -/
private theorem comp_eq_comp_of_isOver {X Y Z W : Scheme.{u}} [IsIntegral X] [IsIntegral W]
    [IsSeparated (Z ↘ ⊤_ Scheme)] (πX : X ⟶ Z) (πY : Y ⟶ Z) {φ : X.RationalMap Y}
    (hφZ : MMP.Flips.RationalMap.IsOver πX πY φ) (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W)
    [IsDominant p] (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h)
    (hcomp : h.compHom q = φ) : p ≫ πX = q ≫ πY := by
  have h1 := specMap_functionFieldMap_fromFunctionField_of_isInverse φ p q h hinv hcomp
  have h2 : (p ≫ πX).toRationalMap = (q ≫ πY).toRationalMap := by
    refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
    rw [MMP.Flips.RationalMap.fromFunctionField_hom, MMP.Flips.RationalMap.fromFunctionField_hom]
    calc W.fromSpecStalk (genericPoint W) ≫ p ≫ πX
        = Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
            X.fromSpecStalk (genericPoint X) ≫ πX := by
          rw [← Category.assoc (Spec.map _), functionFieldMap_fromSpecStalk, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField ≫ πY := by
          rw [← MMP.Flips.RationalMap.fromFunctionField_compHom, hφZ,
            MMP.Flips.RationalMap.fromFunctionField_hom]
      _ = W.fromSpecStalk (genericPoint W) ≫ q ≫ πY := by
          rw [← Category.assoc, h1, Category.assoc]
  have H := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h2)
  rw [Scheme.Hom.toPartialMap_hom] at H
  exact (cancel_epi _).mp H

/-! ### Strict transforms on a common resolution -/

private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{u}} [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- **The strict transform on a resolution.** Let `p : W ⟶ X` be a proper birational morphism
of normal varieties with inverse `h`, and `P` a prime divisor of `X`. Then `h` is defined at the
codimension-one point `η_P` (properness of `p`) by some `h'`, and `h'(η_P)` is the generic point
of a prime divisor `E` of `W` with `p(η_E) = η_P`, along which `p` induces an isomorphism of local
rings. -/
private theorem exists_strictTransform {k : Type u} [Field k] {X W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (hX : IsNormalVariety k sX) (p : W ⟶ X)
    (h : X.RationalMap W) [IsProper p] (hWnp : IsNormalVariety k (p ≫ sX))
    (hpb : IsBirationalMorphism p) (hinv : RationalMap.IsInverse p.toRationalMap h)
    (P : MMP.Mori.PrimeDivisor X) :
    ∃ (E : MMP.Mori.PrimeDivisor W) (h' : X.PartialMap W) (hP : P.genericPoint ∈ h'.domain),
      h'.toRationalMap = h ∧ E.genericPoint = h'.hom ⟨P.genericPoint, hP⟩ ∧
      p E.genericPoint = P.genericPoint ∧ IsIso (p.stalkMap E.genericPoint) := by
  have := hX.1
  have := hWnp.1
  have : IsDominant p := hpb.isDominant
  have := isSeparated_toTerminal sX
  have : IsSeparated p := IsSeparated.of_comp p sX
  obtain ⟨E, heq, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hX hWnp hpb P
  obtain ⟨e, he1, he2⟩ := id hinv
  have hhp : h.compHom p = Scheme.Hom.toRationalMap (𝟙 X) := by
    rw [← he2, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ p = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq p e he1, Iso.inv_hom_id_assoc, Category.comp_id]
  obtain ⟨h', hh'P, hh'⟩ := Scheme.RationalMap.mem_domain.mp
    (MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 X) p h hhp
      P.coheight_genericPoint.le)
  have hpw : p (h'.hom ⟨P.genericPoint, hh'P⟩) = P.genericPoint :=
    apply_hom_eq_of_isInverse p e he1 h' (hh'.trans he2.symm) hh'P
  have := valuationRing_stalk_of_coheight_le_one P.coheight_genericPoint.le
  have : ValuationRing (X.presheaf.stalk (p E.genericPoint)) := by rwa [heq]
  have : ValuationRing (X.presheaf.stalk (p (h'.hom ⟨P.genericPoint, hh'P⟩))) := by
    rwa [hpw]
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing p hpb.functionFieldMap_bijective
    (h'.hom ⟨P.genericPoint, hh'P⟩)
  exact ⟨E, h', hh'P, hh', MMP.Positivity.eq_of_isIso_stalkMap p hpb.functionFieldMap_bijective
    (hpw.trans heq.symm), heq, hiso⟩

end Proof_lem_fourfold_numerically_trivial_birational_contraction

namespace MMP.Fourfold

open CategoryTheory AlgebraicGeometry MMP.Mori

open Proof_lem_fourfold_numerically_trivial_birational_contraction

open Proof_lem_fourfold_nef_lc_targets_same_source_primes (isSeparated_toTerminal)

/-- **Strict transforms on a common resolution.** Let `p : W ⟶ X`, `q : W ⟶ Y` be proper
birational morphisms of normal varieties with `q ∘ p⁻¹ = φ`. If the birational transform of a
prime divisor `P` of `X` under `φ` is the prime divisor `F` of `Y`, then the strict transform `E`
of `P` on `W` maps generically onto both, by isomorphisms of local rings: `p(η_E) = η_P` and
`q(η_E) = η_F`. -/
public theorem exists_primeDivisor_apply_eq_of_transformPrimeDivisor_eq_some {k : Type u}
    [Field k] {X Y W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) {φ : X.RationalMap Y}
    (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W) [IsProper p] [IsProper q]
    (hWnp : IsNormalVariety k (p ≫ sX)) (hpb : IsBirationalMorphism p)
    (hqb : IsBirationalMorphism q) (hinv : RationalMap.IsInverse p.toRationalMap h)
    (hcomp : h.compHom q = φ) {P : MMP.Mori.PrimeDivisor X} {F : MMP.Mori.PrimeDivisor Y}
    (hPF : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some F) :
    ∃ E : MMP.Mori.PrimeDivisor W, p E.genericPoint = P.genericPoint ∧
      IsIso (p.stalkMap E.genericPoint) ∧ q E.genericPoint = F.genericPoint ∧
      IsIso (q.stalkMap E.genericPoint) := by
  have := hY.1
  have : IsDominant q := hqb.isDominant
  have := isSeparated_toTerminal sY
  obtain ⟨E, h', hh'P, hh', hwE, heq, hiso⟩ := exists_strictTransform hX p h hWnp hpb hinv P
  -- `q ∘ h'` represents `φ`, so `q(η_E) = η_F`
  obtain ⟨hdef, -⟩ := MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hPF
  obtain ⟨g', hg'P, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  have hqE : q E.genericPoint = F.genericPoint := by
    rw [hwE, MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hPF g' hg' hg'P]
    have hrat : (h'.compHom q).toRationalMap = g'.toRationalMap := by
      rw [Scheme.RationalMap.compHom_toRationalMap, hh', hcomp, hg']
    exact MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq hrat hh'P hg'P
  have := valuationRing_stalk_of_coheight_le_one F.coheight_genericPoint.le
  have : ValuationRing (Y.presheaf.stalk (q E.genericPoint)) := by rw [hqE]; infer_instance
  exact ⟨E, heq, hiso, hqE,
    MMP.Positivity.isIso_stalkMap_of_valuationRing q hqb.functionFieldMap_bijective _⟩

/-! ### The transform of a pull-back -/

/-- On a common resolution of a birational contraction `φ`, the transform `q_* p^* N` of the
pull-back of an `ℝ`-Cartier divisor `N` is `φ_* N`. -/
public theorem transformDivisor_eq_of_isRCartierPullback {k : Type u} [Field k]
    {X Y W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) {φ : X.RationalMap Y}
    (hφE : ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W) [IsProper p] [IsProper q]
    (hWp : IsNormalVariety k (p ≫ sX)) (hWq : IsNormalVariety k (q ≫ sY))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (hcomp : h.compHom q = φ)
    {N : RDivisor X} {NW : RDivisor W} (hNW : MMP.Flips.IsRCartierPullback p N NW) :
    MMP.Mori.RationalMap.transformDivisor q.toRationalMap NW =
      MMP.Mori.RationalMap.transformDivisor φ N := by
  have := hY.1
  have : IsDominant q := hqb.isDominant
  have := isSeparated_toTerminal sY
  -- the strict transform on `W` of a prime divisor of `Y` is the only prime divisor over it
  have huniq : ∀ (F : MMP.Mori.PrimeDivisor Y) (E₁ E₂ : MMP.Mori.PrimeDivisor W),
      q E₁.genericPoint = F.genericPoint → q E₂.genericPoint = F.genericPoint → E₁ = E₂ := by
    intro F E₁ E₂ h₁ h₂
    obtain ⟨E, -, -, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hWq hqb F
    have key : ∀ E₀ : MMP.Mori.PrimeDivisor W, q E₀.genericPoint = F.genericPoint → E₀ = E := by
      intro E₀ h₀
      have h := htr (Finsupp.single E₀ (1 : ℤ))
      rw [MMP.Mori.RationalMap.transformDivisor_single_of_eq_some
        ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff q E₀ F).mpr h₀)] at h
      by_contra hne
      simp [Finsupp.single_apply, Ne.symm hne] at h
    exact (key E₁ h₁).trans (key E₂ h₂).symm
  refine Finsupp.ext fun F => ?_
  obtain ⟨P, hP⟩ := not_forall.mp (hφE F)
  rw [not_not] at hP
  obtain ⟨E, hpE, hpiso, hqE, -⟩ :=
    exists_primeDivisor_apply_eq_of_transformPrimeDivisor_eq_some hX hY p q h hWp hpb hqb hinv
      hcomp hP
  obtain ⟨E', hqE', -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hWq hqb F
  rw [htr, ← huniq F E E' hqE hqE']
  change NW E = DivisorWithCoeffs.mapPrimeDivisors _ N F
  rw [MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hP ?_ N]
  · exact MMP.Fourfold.coeff_eq_of_isRCartierPullback E P hpE hNW
  · intro P' hP'
    obtain ⟨E₂, hpE₂, -, hqE₂, -⟩ :=
      exists_primeDivisor_apply_eq_of_transformPrimeDivisor_eq_some hX hY p q h hWp hpb hqb hinv
        hcomp hP'
    have hgen : P'.genericPoint = P.genericPoint := by
      rw [← hpE₂, ← hpE, huniq F E₂ E hqE₂ hqE]
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective hgen

end MMP.Fourfold

namespace Proof_lem_fourfold_numerically_trivial_birational_contraction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Mori MMP.Fourfold

open Proof_lem_fourfold_nef_lc_targets_same_source_primes (isSeparated_toTerminal)

/-! ### The graph of a birational map -/

/-- A closed immersion followed by an H-projective morphism is H-projective. -/
private theorem isProjectiveMorphism_comp_of_isClosedImmersion {H X S : Scheme.{u}} (ι : H ⟶ X)
    [IsClosedImmersion ι] {f : X ⟶ S} (hf : IsProjectiveMorphism f) :
    IsProjectiveMorphism (ι ≫ f) := by
  obtain ⟨n, j, hj, rfl⟩ := hf
  have := hj
  exact ⟨n, ι ≫ j, inferInstance, Category.assoc _ _ _⟩

/-- **The closure of the graph of a partial isomorphism.** Let `e : U ≅ V` be an isomorphism of
dense opens `U ⊆ X`, `V ⊆ Y` of projective varieties over `k`, compatible with the structure
morphisms. The scheme-theoretic closure `Γ ⊆ Y ×_k X` of its graph is a projective variety over
`k` whose projection `p_X : Γ ⟶ X` is an isomorphism over `U`, on which the projection
`p_Y : Γ ⟶ Y` is `e ∘ p_X`. -/
private theorem exists_graph {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hXp : MMP.Mori.IsProjectiveVariety k sX) (hYp : MMP.Mori.IsProjectiveVariety k sY)
    (e : X.PartialIso Y) (he : e.source.ι ≫ sX = e.iso.hom ≫ e.target.ι ≫ sY) :
    ∃ (Γ : Scheme.{u}) (_ : IsIntegral Γ) (pX : Γ ⟶ X) (pY : Γ ⟶ Y),
      AlgebraicGeometry.IsVariety k (pX ≫ sX) ∧ IsProjectiveMorphism (pX ≫ sX) ∧
        pX ≫ sX = pY ≫ sY ∧
        IsIso (pX ∣_ e.source) ∧
        ∀ {T : Scheme.{u}} (a : T ⟶ Γ) (b : T ⟶ e.source), a ≫ pX = b ≫ e.source.ι →
          a ≫ pY = b ≫ e.iso.hom ≫ e.target.ι := by
  have := hXp.toIsVariety
  have := hYp.toIsVariety
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := (quasiCompact_iff_compactSpace sX).mp inferInstance
  have : IsNoetherian X := {}
  set U := e.source
  set V := e.target
  have hcond : (e.iso.hom ≫ V.ι) ≫ sY = U.ι ≫ sX := (Category.assoc _ _ _).trans he.symm
  let γ : U.toScheme ⟶ pullback sY sX := pullback.lift (e.iso.hom ≫ V.ι) U.ι hcond
  have hγ : γ ≫ pullback.snd sY sX = U.ι := pullback.lift_snd _ _ _
  have hγ' : γ ≫ pullback.fst sY sX = e.iso.hom ≫ V.ι := pullback.lift_fst _ _ _
  have : QuasiCompact γ := inferInstance
  let i := γ.imageι
  have hfactor : γ.toImage ≫ i = γ := Scheme.Hom.toImage_imageι γ
  -- the closure of the graph is integral
  have : Nonempty U := by
    obtain ⟨x, hx⟩ := e.dense_source.nonempty
    exact ⟨⟨x, hx⟩⟩
  have : IrreducibleSpace U.toScheme := inferInstance
  have : IrreducibleSpace γ.image := by
    apply (irreducibleSpace_def _).mpr
    have h1 : IsIrreducible (Set.range γ.toImage) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ U.toScheme).image _
        γ.toImage.continuous.continuousOn
    have h2 := h1.closure
    rwa [(inferInstance : IsDominant γ.toImage).denseRange.closure_range] at h2
  have : IsIntegral γ.image := isIntegral_of_irreducibleSpace_of_isReduced _
  let pX : γ.image ⟶ X := i ≫ pullback.snd sY sX
  let pY : γ.image ⟶ Y := i ≫ pullback.fst sY sX
  have hIso : IsIso (pullback.snd pX U.ι) :=
    AlgebraicGeometry.isIso_pullback_snd_imageι_comp_of_section (pullback.snd sY sX) U
      (fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _) γ hγ
  -- the graph identity on the pull-back of `U`
  have key : pullback.fst pX U.ι ≫ pY = pullback.snd pX U.ι ≫ e.iso.hom ≫ V.ι := by
    let t : U.toScheme ⟶ pullback pX U.ι :=
      pullback.lift γ.toImage (𝟙 _) (by
        simp only [pX, Category.id_comp, ← Category.assoc, hfactor, hγ])
    have ht : t ≫ pullback.snd pX U.ι = 𝟙 _ := pullback.lift_snd _ _ _
    have hte : t = inv (pullback.snd pX U.ι) := by
      apply (cancel_mono (pullback.snd pX U.ι)).1
      simp [ht]
    apply (cancel_epi (inv (pullback.snd pX U.ι))).1
    rw [← hte]
    simpa only [t, pY, ← Category.assoc, pullback.lift_fst, pullback.lift_snd, hfactor,
      Category.id_comp] using hγ'
  refine ⟨γ.image, inferInstance, pX, pY, ?_, ?_, ?_, ?_, ?_⟩
  · have : IsSeparated (pX ≫ sX) := by simp only [pX, Category.assoc]; infer_instance
    have : LocallyOfFiniteType (pX ≫ sX) := by simp only [pX, Category.assoc]; infer_instance
    have : QuasiCompact (pX ≫ sX) := by simp only [pX, Category.assoc]; infer_instance
    exact {}
  · simp only [pX, Category.assoc]
    exact isProjectiveMorphism_comp_of_isClosedImmersion i
      ((hYp.isProjective.baseChange sX).comp hXp.isProjective)
  · simp only [pX, pY, Category.assoc, pullback.condition]
  · change IsIso ((pullbackRestrictIsoRestrict pX U).inv ≫ pullback.snd pX U.ι)
    infer_instance
  · intro T a b hab
    have h1 := pullback.lift a b hab ≫= key
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at h1

/-! ### A common resolution -/

/-- **A normal projective common resolution of a birational map.** For a birational map
`φ : X ⤏ Y` of normal projective varieties over a field `k`, compatible with the structure
morphisms, there are a normal variety `W` and projective birational morphisms `p : W ⟶ X`,
`q : W ⟶ Y` with `q = φ ∘ p`: some inverse `h` of `p` has `h.compHom q = φ`. -/
private theorem exists_common_resolution {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IsIntegral X] [IsNormal X] [IsIntegral Y] [IsNormal Y] (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hXp : MMP.Mori.IsProjectiveVariety k sX) (hYp : MMP.Mori.IsProjectiveVariety k sY)
    {φ : X.RationalMap Y} (hφ : MMP.Mori.RationalMap.IsBirational φ)
    (hφs : φ.compHom sY = sX.toRationalMap) :
    ∃ (W : Scheme.{u}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (sW : W ⟶ Spec (.of k)) (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W),
      IsNormalVariety k sW ∧ p ≫ sX = sW ∧ q ≫ sY = sW ∧
        IsProjectiveMorphism p ∧ IsBirationalMorphism p ∧
        IsProjectiveMorphism q ∧ IsBirationalMorphism q ∧
        MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧ h.compHom q = φ := by
  have := hXp.toIsVariety
  have := hYp.toIsVariety
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  obtain ⟨e, he⟩ := hφ
  -- `e` is compatible with the structure morphisms
  have hes : e.source.ι ≫ sX = e.iso.hom ≫ e.target.ι ≫ sY := by
    have := isSeparated_toTerminal sX
    have h1 : (e.toPartialMap.compHom sY).toRationalMap = sX.toPartialMap.toRationalMap := by
      rw [Scheme.RationalMap.compHom_toRationalMap]
      exact (congrArg (·.compHom sY) he).trans hφs
    have h2 := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp h1)
    exact h2.symm.trans (Category.assoc _ _ _)
  obtain ⟨Γ, _, pX, pY, hΓv, hΓp, hΓXY, hiso, hG'⟩ := exists_graph sX sY hXp hYp e hes
  set U := e.source
  set V := e.target
  have hG : (pX ⁻¹ᵁ U).ι ≫ pY = (pX ∣_ U) ≫ e.iso.hom ≫ V.ι :=
    hG' _ _ (morphismRestrict_ι pX U).symm
  set sΓ := pX ≫ sX
  -- the normalization of the graph
  let W := normalizationSchemeOverField k sΓ
  let ν : W ⟶ Γ := normalizationOverField k sΓ
  have hWv : AlgebraicGeometry.IsVariety k (ν ≫ sΓ) := isVariety_normalizationOverField k sΓ
  have : IsIntegral W := hWv.toIsIntegral
  have : IsNormal W := Scheme.isNormal_normalizationScheme Γ
    (finite_irreducibleComponents_of_locallyOfFiniteType k sΓ)
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (ν ≫ sΓ)
  have : IsProper sΓ := isProper_of_isProjectiveMorphism sΓ hΓp
  have hWp : IsProjectiveMorphism (ν ≫ sΓ) :=
    (isProjective_iff_isProjectiveMorphism_of_isAffine _).mp
      ((isProper_and_isProjective_normalizationOverField k sΓ).2
        ((isProjective_iff_isProjectiveMorphism_of_isAffine _).mpr hΓp))
  let p : W ⟶ X := ν ≫ pX
  let q : W ⟶ Y := ν ≫ pY
  have hpX : p ≫ sX = ν ≫ sΓ := Category.assoc _ _ _
  have hqY : q ≫ sY = ν ≫ sΓ := by
    simp only [q, sΓ, Category.assoc, hΓXY]
  have hp : IsProjectiveMorphism p := IsProjectiveMorphism.of_comp p sX (hpX ▸ hWp)
  have hq : IsProjectiveMorphism q := IsProjectiveMorphism.of_comp q sY (hqY ▸ hWp)
  have : IsProper p := isProper_of_isProjectiveMorphism p hp
  have : IsProper q := isProper_of_isProjectiveMorphism q hq
  -- birationality of the two projections of the graph
  obtain ⟨u, hu⟩ := e.dense_source.nonempty
  have hO : ((pX ⁻¹ᵁ U : Γ.Opens) : Set Γ).Nonempty :=
    ⟨(inv (pX ∣_ U) ⟨u, hu⟩).1, (inv (pX ∣_ U) ⟨u, hu⟩).2⟩
  have hres : pX.resLE U (pX ⁻¹ᵁ U) le_rfl = pX ∣_ U := by
    rw [← cancel_mono U.ι, Scheme.Hom.resLE_comp_ι, morphismRestrict_ι]
  have hpXb : IsBirationalMorphism pX :=
    MMP.Flips.isBirationalMorphism_of_isIso_resLE pX (pX ⁻¹ᵁ U) U hO ⟨u, hu⟩ le_rfl
      (by rw [hres]; exact hiso)
  have hOV : pX ⁻¹ᵁ U ≤ pY ⁻¹ᵁ V := by
    intro x hx
    have h := congrArg (fun f : (pX ⁻¹ᵁ U).toScheme ⟶ Y => f ⟨x, hx⟩) hG
    have h' : pY x = V.ι (e.iso.hom ((pX ∣_ U) ⟨x, hx⟩)) := h
    show pY x ∈ V
    rw [h']
    exact (e.iso.hom ((pX ∣_ U) ⟨x, hx⟩)).2
  have hresY : pY.resLE V (pX ⁻¹ᵁ U) hOV = (pX ∣_ U) ≫ e.iso.hom := by
    rw [← cancel_mono V.ι, Scheme.Hom.resLE_comp_ι, hG, Category.assoc]
  have hpYb : IsBirationalMorphism pY :=
    MMP.Flips.isBirationalMorphism_of_isIso_resLE pY (pX ⁻¹ᵁ U) V hO
      (e.dense_target.nonempty) hOV (by rw [hresY]; infer_instance)
  have hν : IsBirational ν := Scheme.isBirational_normalization Γ _
  have hpb : IsBirationalMorphism p := by
    have := MMP.Mori.isBirationalMorphism_comp_of_isBirational p (𝟙 W)
      (hν.comp (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hpXb))
      (isBirational_of_isIso (𝟙 W))
    simpa using this
  have hqb : IsBirationalMorphism q := by
    have := MMP.Mori.isBirationalMorphism_comp_of_isBirational q (𝟙 W)
      (hν.comp (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hpYb))
      (isBirational_of_isIso (𝟙 W))
    simpa using this
  -- the inverse of `p`, and `q = φ ∘ p`
  obtain ⟨ep, hep⟩ := id hpb
  have : IsDominant p := hpb.isDominant
  refine ⟨W, inferInstance, inferInstance, inferInstance, ν ≫ sΓ, p, q, ep.symm.toRationalMap,
    ⟨hWv, inferInstance⟩, hpX, hqY, hp, hpb, hq, hqb, ⟨ep, hep, rfl⟩, ?_⟩
  have hcomm : (p ⁻¹ᵁ e.toPartialMap.domain).ι ≫ q =
      (p ∣_ e.toPartialMap.domain) ≫ e.toPartialMap.hom := by
    have h := hG' ((p ⁻¹ᵁ U).ι ≫ ν) (p ∣_ U) (by
      rw [Category.assoc]; exact (morphismRestrict_ι p U).symm)
    rw [Category.assoc] at h
    exact h
  have hbij := hpb.functionFieldMap_bijective
  have : IsIso (CommRingCat.ofHom (functionFieldMap p)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom (functionFieldMap p))),
    MMP.Flips.RationalMap.fromFunctionField_compHom, ← Category.assoc,
    specMap_functionFieldMap_fromFunctionField_symm p ep hep, ← he]
  exact (specMap_functionFieldMap_fromFunctionField p e.toPartialMap q hcomm).symm

/-! ### The conclusion on a common resolution -/

/-- **Numerical triviality on a common resolution.** On a common resolution `p : W ⟶ X`,
`q : W ⟶ Y` of the birational contraction `φ`, with `N_W = p^* N`, the transform `φ_* N` is
numerically trivial over `Z` and `q^* φ_* N = N_W`. -/
private theorem isNumericallyTrivialOver_and_isRCartierPullback_of_commonResolution {k : Type u}
    [Field k] {W X Y Z : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sW : W ⟶ Spec (.of k)} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} [QuasiCompact sX] [QuasiCompact sY]
    (hX : IsQFactorial sX) (hXp : MMP.Mori.IsProjectiveVariety k sX)
    (hY : IsQFactorial sY) (hYp : MMP.Mori.IsProjectiveVariety k sY)
    (hZp : MMP.Mori.IsProjectiveVariety k sZ)
    {πX : X ⟶ Z} {πY : Y ⟶ Z} (hπX : πX ≫ sZ = sX) (hπY : πY ≫ sZ = sY)
    {φ : X.RationalMap Y} (hφZ : MMP.Flips.RationalMap.IsOver πX πY φ)
    (hφE : ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    {N : RDivisor X} (hN : MMP.Flips.IsNumericallyTrivialOver k sX πX N)
    (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W) (hW : IsNormalVariety k sW)
    (hpX : p ≫ sX = sW) (hqY : q ≫ sY = sW)
    (hp : IsProjectiveMorphism p) (hpb : IsBirationalMorphism p)
    (hq : IsProjectiveMorphism q) (hqb : IsBirationalMorphism q)
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (hcomp : h.compHom q = φ)
    {NW : RDivisor W} (hNW : MMP.Flips.IsRCartierPullback p N NW) :
    MMP.Flips.IsNumericallyTrivialOver k sY πY (MMP.Mori.RationalMap.transformDivisor φ N) ∧
      MMP.Flips.IsRCartierPullback q (MMP.Mori.RationalMap.transformDivisor φ N) NW := by
  have : IsProper p := isProper_of_isProjectiveMorphism p hp
  have : IsProper q := isProper_of_isProjectiveMorphism q hq
  have : IsDominant p := hpb.isDominant
  have := isSeparated_toTerminal sZ
  rw [← transformDivisor_eq_of_isRCartierPullback hX.1 hY.1 hφE p q h (hpX ▸ hW) (hqY ▸ hW)
    hpb hqb hinv hcomp hNW]
  exact isNumericallyTrivialOver_transformDivisor_and_isRCartierPullback sW sX sY sZ hW
    ((AlgebraicGeometry.isProjectiveVariety_iff k sW).mpr ⟨hW.1, hpX ▸ hp.comp hXp.isProjective⟩)
    hX.1 hXp hY hYp hZp πX πY hπX hπY p q hpX hqY
    (comp_eq_comp_of_isOver πX πY hφZ p q h hinv hcomp) hp hpb hq hqb hN hNW

/-- The source of a normal variety over a field is compact. -/
private theorem compactSpace_of_isNormalVariety {k : Type u} [Field k] {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} (hW : IsNormalVariety k sW) : CompactSpace W := by
  have := hW.1
  exact (quasiCompact_iff_compactSpace sW).mp inferInstance

/-! ### The main theorem -/

end Proof_lem_fourfold_numerically_trivial_birational_contraction

namespace MMP.Fourfold

open MMP.Mori

open Proof_lem_fourfold_numerically_trivial_birational_contraction

open Proof_lem_fourfold_nef_lc_targets_same_source_primes (compHom_compHom)

/-- **Numerical triviality across a birational contraction.** Let `X`, `Y` be normal
`ℚ`-factorial projective varieties over a field `k`, over a projective variety `Z` via `πX`,
`πY`, and let `φ : X ⤏ Y` be a birational map over `Z` such that no prime divisor of `Y` is
exceptional for `φ⁻¹`. If `N` is an `ℝ`-Cartier divisor on `X` numerically trivial over `Z`, then
`N_Y = φ_* N` is numerically trivial over `Z`, and for every common resolution `p : W ⟶ X`,
`q : W ⟶ Y` (projective birational, `q = φ ∘ p`) the pullbacks `p^*N` and `q^*N_Y` agree. -/
@[mmp "lem_fourfold_numerically_trivial_birational_contraction"]
public theorem isNumericallyTrivialOver_transformDivisor_and_pullback_eq
    {k : Type u} [Field k] {X Y Z : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [QuasiCompact sX] [QuasiCompact sY]
    (hX : IsQFactorial sX) (hXp : MMP.Mori.IsProjectiveVariety k sX)
    (hY : IsQFactorial sY) (hYp : MMP.Mori.IsProjectiveVariety k sY)
    (hZp : MMP.Mori.IsProjectiveVariety k sZ)
    (πX : X ⟶ Z) (πY : Y ⟶ Z) (hπX : πX ≫ sZ = sX) (hπY : πY ≫ sZ = sY)
    {φ : X.RationalMap Y} (hφ : MMP.Mori.RationalMap.IsBirational φ)
    (hφZ : MMP.Flips.RationalMap.IsOver πX πY φ)
    (hφE : ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    {N : RDivisor X} (hN : MMP.Flips.IsNumericallyTrivialOver k sX πX N) :
    MMP.Flips.IsNumericallyTrivialOver k sY πY (MMP.Mori.RationalMap.transformDivisor φ N) ∧
      ∀ (W : Scheme.{u}) [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
        (sW : W ⟶ Spec (.of k)) (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W),
        IsNormalVariety k sW → p ≫ sX = sW → q ≫ sY = sW →
        IsProjectiveMorphism p → IsBirationalMorphism p →
        IsProjectiveMorphism q → IsBirationalMorphism q →
        MMP.Mori.RationalMap.IsInverse p.toRationalMap h → h.compHom q = φ →
        ∀ NW NWY : RDivisor W, MMP.Flips.IsRCartierPullback p N NW →
          MMP.Flips.IsRCartierPullback q (MMP.Mori.RationalMap.transformDivisor φ N) NWY →
          NW = NWY := by
  refine ⟨?_, fun W _ _ _ sW p q h hW hpX hqY hp hpb hq hqb hinv hcomp NW NWY hNW hNWY => ?_⟩
  · obtain ⟨W, _, _, _, sW, p, q, h, hW, hpX, hqY, hp, hpb, hq, hqb, hinv, hcomp⟩ :=
      exists_common_resolution sX sY hXp hYp hφ (by
        rw [← hπY, ← hπX, ← compHom_compHom, hφZ, toRationalMap_compHom])
    have : IsDominant p := hpb.isDominant
    have := compactSpace_of_isNormalVariety hW
    obtain ⟨NW, hNW, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p hN.1
    exact (isNumericallyTrivialOver_and_isRCartierPullback_of_commonResolution hX hXp hY hYp hZp
      hπX hπY hφZ hφE hN p q h hW hpX hqY hp hpb hq hqb hinv hcomp hNW).1
  · have : IsDominant q := hqb.isDominant
    have := compactSpace_of_isNormalVariety hW
    exact MMP.Flips.IsRCartierPullback.eq q
      (isNumericallyTrivialOver_and_isRCartierPullback_of_commonResolution hX hXp hY hYp hZp
        hπX hπY hφZ hφE hN p q h hW hpX hqY hp hpb hq hqb hinv hcomp hNW).2 hNWY

end MMP.Fourfold

namespace Proof_lem_fourfold_effective_adjoint_contracts_only_its_support

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Mori MMP.Fourfold MMP.Flips

/-! ### Exceptional prime divisors -/

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
private theorem exists_topologicalKrullDim_eq_natCast {k : Type u} [Field k] {X : Scheme.{u}}
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

/-- A prime divisor `F` of `Y` whose image `g(η_F)` has coheight one in the normal variety `X`
is not exceptional over `X`. -/
private theorem not_isExceptionalPrimeDivisor_of_coheight_eq_one {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (g : Y ⟶ X)
    (F : MMP.Mori.PrimeDivisor Y) (hF : Order.coheight (g F.genericPoint) = 1) :
    ¬ IsExceptionalPrimeDivisor sX g F := by
  rintro ⟨hY, hg, hp, hexc⟩
  have : IsIntegral X := hX.1.toIsIntegral
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast sX
  unfold ProperDivisorOver.IsExceptional at hexc
  rw [ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint, hn] at hexc
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (g F.genericPoint)
  rw [hn] at hd
  have h2 := (withBot_add_two_le_iff hd).mp hexc
  change 2 ≤ Order.coheight (g F.genericPoint) at h2
  rw [hF] at h2
  exact absurd h2 (by decide)

/-! ### Intersection numbers -/

/-- Every Cartier divisor has an intersection number with a proper curve: the normalization
of the curve is a regular proper curve birational to it. -/
private theorem exists_isCartierIntersectionNumber (k : Type u) [Field k] {Y : Scheme}
    (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (C : MMP.Mori.ProperCurve sY) (L : MMP.Mori.Divisor Y)
    (hL : L.IsCartier) : ∃ d, MMP.Flips.IsCartierIntersectionNumber k sY C L hL d := by
  let p := C.ι ≫ sY
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
  exact ⟨_, _, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le,
    rfl⟩

/-- The empty presentation of `0` computes `0 · C = 0`. -/
private theorem isRIntersectionNumber_zero {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    (C : ProperCurve sX) :
    IsRIntersectionNumber k sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → Divisor X) C 0 :=
  ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩

/-- A difference of real combinations of Cartier divisors is one. -/
private theorem isCartierCombination_sub {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D₁ D₂ : RDivisor X} (h₁ : IsCartierCombination D₁) (h₂ : IsCartierCombination D₂) :
    IsCartierCombination (D₁ - D₂) := by
  obtain ⟨m₁, r₁, L₁, hL₁, rfl⟩ := h₁
  obtain ⟨m₂, r₂, L₂, hL₂, rfl⟩ := h₂
  refine ⟨m₁ + m₂, Fin.append r₁ (-r₂), Fin.append L₁ L₂, fun j => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa using hL₁ i
    · simpa using hL₂ i
  · rw [Fin.sum_univ_add]
    simp [sub_eq_add_neg, neg_smul, Finset.sum_neg_distrib]

/-- If `D ≡_f M`, then `D - M` is numerically trivial over the base. -/
private theorem isNumericallyTrivialOver_sub {k : Type u} [Field k] {X Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {f : X ⟶ Z} {D M : RDivisor X} (h : IsNumericallyEquivalentOver k sX f D M) :
    IsNumericallyTrivialOver k sX f (D - M) := by
  obtain ⟨hD, hM, hnum⟩ := h
  refine ⟨isCartierCombination_sub hD hM, ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  have hx₂ : x₂ = 0 := (IsRIntersectionNumber.eq_and_linear k sX C).1 0 r₂ L₂ Fin.elim0
    Fin.elim0 x₂ 0 h₂ (isRIntersectionNumber_zero sX C)
  obtain ⟨mM, rM, LM, hLM, hMeq⟩ := hM
  choose d hd using fun j => exists_isCartierIntersectionNumber k sX C (LM j) (hLM j)
  have hxM : IsRIntersectionNumber k sX M rM LM C (∑ j, rM j * d j) :=
    ⟨hLM, d, by simpa only [toRDivisor_eq_mapCoeffs] using hMeq, hd, rfl⟩
  have hsum := (IsRIntersectionNumber.eq_and_linear k sX C).2 (D - M) M r₁ L₁ rM LM x₁ _ 1 1
    h₁ hxM
  rw [one_smul, one_smul, sub_add_cancel] at hsum
  have := hnum C hC _ _ _ _ _ _ _ _ hsum hxM
  linarith

/-! ### Real Cartier divisors and their pull-backs -/

/-- A real combination of Cartier divisors is `ℝ`-Cartier. -/
private theorem isRCartier_of_isCartierCombination {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {D : RDivisor X} (h : IsCartierCombination D) : RDivisor.IsRCartier D := by
  obtain ⟨m, r, L, hL, rfl⟩ := h
  exact ⟨m, r, L, hL, fun Γ => by
    simpa only [← toRDivisor_eq_mapCoeffs] using MMP.Flips.coeff_sum_smul_toRDivisor r L Γ⟩

/-- A divisor with a pull-back is `ℝ`-Cartier. -/
private theorem isRCartier_of_isRCartierPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {D : RDivisor X}
    {G : RDivisor Y} (h : IsRCartierPullback f D G) :
    RDivisor.IsRCartier D := by
  obtain ⟨m, r, L, -, hL, rfl, -⟩ := h
  exact isRCartier_of_isCartierCombination ⟨m, r, L, hL, by simp only [toRDivisor_eq_mapCoeffs]⟩

/-- A difference of pull-backs is a pull-back of the difference. -/
private theorem isRCartierPullback_sub {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {D₁ D₂ : RDivisor X} {G₁ G₂ : RDivisor Y}
    (h₁ : IsRCartierPullback f D₁ G₁) (h₂ : IsRCartierPullback f D₂ G₂) :
    IsRCartierPullback f (D₁ - D₂) (G₁ - G₂) := by
  simpa [sub_eq_add_neg, neg_one_smul] using
    isRCartierPullback_add h₁ (isRCartierPullback_smul (-1) h₂)

/-- **Push-forward along a `q`-exceptional comparison.** Let `q : W ⟶ Y` be a proper birational
morphism of normal varieties, `G = q^*D` and `G'` with `G' - G` exceptional over `Y`. Then for
every effective `M` on `W` the push-forward `q_*(G' - M)` is at most `D`: along a prime `F` of
`Y`, the coefficient of `D - q_*(G' - M)` is that of `M` along the strict transform of `F`. -/
private theorem transformDivisor_sub_le {k : Type u} [Field k] {Y W : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (hY : IsNormalVariety k sY) {q : W ⟶ Y}
    (hW : IsNormalVariety k (q ≫ sY)) [IsProper q] (hq : IsBirationalMorphism q) {D : RDivisor Y}
    {G G' M : RDivisor W} (hG : IsRCartierPullback q D G)
    (hexc : ∀ E, (G' - G).coeff E ≠ 0 → IsExceptionalPrimeDivisor sY q E) (hM : 0 ≤ M) :
    0 ≤ D - MMP.Mori.RationalMap.transformDivisor q.toRationalMap (G' - M) := by
  intro F
  obtain ⟨E, hE, hiso, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hW hq F
  have hD := coeff_eq_of_isRCartierPullback E F hE hG
  have hE0 : (G' - G).coeff E = 0 := by
    by_contra hne
    exact not_isExceptionalPrimeDivisor_of_coheight_eq_one hY q E
      (by rw [hE]; exact F.coheight_genericPoint) (hexc E hne)
  have hME := hM E
  have htrE := htr (G' - M)
  simp only [DivisorWithCoeffs.coeff, Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_zero,
    Pi.zero_apply] at hD hE0 hME htrE ⊢
  rw [htrE]
  linarith

/-! ### The main theorem -/

end Proof_lem_fourfold_effective_adjoint_contracts_only_its_support

namespace MMP.Fourfold

open MMP.Mori

open Proof_lem_fourfold_effective_adjoint_contracts_only_its_support

open Proof_lem_fourfold_nef_lc_targets_same_source_primes (isSeparated_toTerminal)

open Proof_lem_fourfold_numerically_trivial_birational_contraction
  (comp_eq_comp_of_isOver exists_strictTransform)

/-- **An effective numerical adjoint bounds the contracted primes.** Let `φ : X ⤏ Y` be a log
minimal model of the real pair `(X/Z, B)`, with `X` `ℚ`-factorial projective over the projective
base `Z`. If `K_X + B ≡_Z M` with `M` an effective `ℝ`-divisor, then every prime divisor of `X`
contracted by `φ` is a component of `M`. -/
@[mmp "lem_fourfold_effective_adjoint_contracts_only_its_support"]
public theorem coeff_ne_zero_of_isRealLogMinimalModel_of_isExceptional
    {k : Type u} [Field k] {X Y Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX]
    [QuasiCompact sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sY]
    (hXp : MMP.Mori.IsProjectiveVariety k sX) (hZp : MMP.Mori.IsProjectiveVariety k sZ)
    {π : X ⟶ Z} {πY : Y ⟶ Z} {KX : Divisor X} {KY : Divisor Y}
    {B M : RDivisor X} {BY : RDivisor Y} {φ : X.RationalMap Y}
    (hY : IsRealLogMinimalModel sX sY sZ π πY KX B KY BY φ) (hQ : IsQFactorial sX)
    (hM : ∀ P, 0 ≤ M.coeff P)
    (hnum : MMP.Flips.IsNumericallyEquivalentOver k sX π
      (MMP.Flips.logCanonicalDivisor KX B) M)
    (P : MMP.Mori.PrimeDivisor X) (hP : MMP.Mori.RationalMap.IsExceptional φ P) :
    M.coeff P ≠ 0 := by
  obtain ⟨W, _, _, _, sW, p, q, h, GX, GY, hR, hpos⟩ := hY.exists_resolution_pos
  have hXn : IsNormalVariety k sX := hY.isRealLcPair.1
  have hWn : IsNormalVariety k sW := ⟨hR.isVariety, inferInstance⟩
  have hWnp : IsNormalVariety k (p ≫ sX) := hR.comp_eq_left ▸ hWn
  have hWnq : IsNormalVariety k (q ≫ sY) := hR.comp_eq_right ▸ hWn
  have hWp : MMP.Mori.IsProjectiveVariety k sW :=
    (AlgebraicGeometry.isProjectiveVariety_iff k sW).mpr
      ⟨hWn.1, hR.comp_eq_left ▸ hR.isProjectiveMorphism_left.comp hXp.isProjective⟩
  have := isProper_of_isProjectiveMorphism p hR.isProjectiveMorphism_left
  have := isProper_of_isProjectiveMorphism q hR.isProjectiveMorphism_right
  have : IsDominant p := hR.isBirationalMorphism_left.isDominant
  have : IsDominant q := hR.isBirationalMorphism_right.isDominant
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have := hZp.toIsVariety
  have := hR.isVariety
  have := isSeparated_toTerminal sZ
  have := isSeparated_toTerminal sW
  -- `M_W = p^*M ≥ 0` and `p^*N = G_X - M_W` for the numerically trivial `N = K_X + B - M`
  obtain ⟨MW, hMW, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p hnum.2.1
  have hMW0 : 0 ≤ MW := (isEffective_of_isRCartierPullback p
    (isRCartier_of_isCartierCombination hnum.2.1) hM).2 MW hMW
  have hfull := isNumericallyTrivialOver_transformDivisor_and_isRCartierPullback sW sX sY sZ hWn
    hWp hXn hXp hY.isQFactorial hY.isProjectiveVariety_model hZp π πY hY.comp_eq
    hY.comp_eq_model p q hR.comp_eq_left hR.comp_eq_right
    (comp_eq_comp_of_isOver π πY hY.isOver p q h hR.isInverse hR.compHom_eq)
    hR.isProjectiveMorphism_left hR.isBirationalMorphism_left hR.isProjectiveMorphism_right
    hR.isBirationalMorphism_right (isNumericallyTrivialOver_sub hnum)
    (isRCartierPullback_sub hR.isRCartierPullback_left hMW)
  -- `T = (K_Y + B_Y) - q_* p^* N ≥ 0`, so `q^*T = G_Y - (G_X - M_W) ≥ 0`
  have hqT := isRCartierPullback_sub hR.isRCartierPullback_right hfull.2
  have hqT0 := (isEffective_of_isRCartierPullback q
    (isRCartier_of_isRCartierPullback hqT)
    (transformDivisor_sub_le hY.isNormalVariety_model hWnq
      hR.isBirationalMorphism_right hR.isRCartierPullback_right hR.isExceptional hMW0)).2 _ hqT
  -- at the strict transform `E` of `P`, the comparison is `p^*M - q^*T > 0`
  obtain ⟨E, h', hh'P, hh', hE, hpE, hiso⟩ := exists_strictTransform hXn p h
    hWnp hR.isBirationalMorphism_left hR.isInverse P
  have hposE :=
    hpos P hP E (MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq h' hh' hh'P hE)
  have hME := coeff_eq_of_isRCartierPullback E P hpE hMW
  have hq0 := hqT0 E
  simp only [DivisorWithCoeffs.coeff, Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_zero,
    Pi.zero_apply] at hposE hME hq0 ⊢
  intro hMP
  linarith

end MMP.Fourfold

end
