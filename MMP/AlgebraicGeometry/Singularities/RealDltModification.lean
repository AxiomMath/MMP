module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
import MMP.AlgebraicGeometry.MMP.MinimalModel.DltModification
import MMP.AlgebraicGeometry.Divisor.SmallAffineMovingDivisors
import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
import MMP.AlgebraicGeometry.Singularities.BoundaryLowering
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.RealKltPolytope
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryAlgebra
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.MMP.Abundance.Curve.AdmissibleSectionsGenerate
import MMP.AlgebraicGeometry.MMP.Contraction.SmallContractionBasics
import MMP.AlgebraicGeometry.MMP.MinimalModel.RealKltCompactification
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction

/-!
# Real dlt modifications of lc pairs on a nonfactorial source

Assume the projective floor-program inputs `P(n)`, `n ≥ 3`. Let `(X, B)` be an effective lc pair
with real boundary on a normal projective complex variety `X` of dimension `n`; `X` need not be
`ℚ`-factorial. Then `(X, B)` has a projective crepant `ℚ`-factorial dlt modification: a projective
birational morphism `p : V ⟶ X` from a `ℚ`-factorial normal projective variety such that, with
`B_V = p⁻¹_* B + ∑ F` (the sum over the `p`-exceptional prime divisors `F`), the pair `(V, B_V)`
is dlt and `K_V + B_V = p^*(K_X + B)`. Every prime divisor extracted by `p` has log discrepancy
zero with respect to `(X, B)`.

## Main results

* `MMP.Fourfold.exists_isQFactorial_dltModification_of_isRealLcPair`

## Implementation notes

The boundary `B_V` is described coefficientwise: its coefficient is one along every
`p`-exceptional prime divisor (`MMP.Mori.RationalMap.IsExceptional`) and that of the strict
transform `p⁻¹_* B` elsewhere. The crepant identity is stated for a canonical divisor `K_V` of `V`
with `p_* K_V = K_X` (both cut out by one rational top form) and the pull-back of `ℝ`-Cartier
divisors `MMP.Flips.IsRCartierPullback`. The log discrepancy of an extracted prime `F` is that of
`F` regarded as a divisor over `X`.
-/

@[expose] public noncomputable section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open CategoryTheory AlgebraicGeometry Filter Topology

namespace MMP.RealDltModificationNormalSource

open MMP MMP.Mori MMP.Fourfold

/-! ### Real combinations of Cartier divisors, coefficientwise -/

section CartierCombination

variable {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]

/-- A real combination of Cartier divisors, given coefficientwise. -/
private theorem isCartierCombination_of_forall_coeff {D : RDivisor X} {m : ℕ} {r : Fin m → ℝ}
    {C : Fin m → Divisor X} (hC : ∀ i, (C i).IsCartier)
    (h : ∀ Γ, D.coeff Γ = ∑ i, r i * ((C i).coeff Γ : ℝ)) : MMP.Flips.IsCartierCombination D :=
  ⟨m, r, C, hC, by
    simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs]
    exact DivisorWithCoeffs.ext' fun Γ => by rw [h, MMP.Flips.coeff_sum_smul_toRDivisor]⟩

/-- The coefficients of a real combination of Cartier divisors. -/
private theorem exists_forall_coeff_of_isCartierCombination {D : RDivisor X}
    (h : MMP.Flips.IsCartierCombination D) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (C : Fin m → Divisor X), (∀ i, (C i).IsCartier) ∧
      ∀ Γ, D.coeff Γ = ∑ i, r i * ((C i).coeff Γ : ℝ) := by
  obtain ⟨m, r, C, hC, hD⟩ := h
  refine ⟨m, r, C, hC, fun Γ => ?_⟩
  simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs] at hD
  rw [hD, MMP.Flips.coeff_sum_smul_toRDivisor]

/-- A difference of real combinations of Cartier divisors is one. -/
private theorem isCartierCombination_sub {D₁ D₂ : RDivisor X}
    (h₁ : MMP.Flips.IsCartierCombination D₁) (h₂ : MMP.Flips.IsCartierCombination D₂) :
    MMP.Flips.IsCartierCombination (D₁ - D₂) := by
  obtain ⟨m₁, r₁, C₁, hC₁, e₁⟩ := exists_forall_coeff_of_isCartierCombination h₁
  obtain ⟨m₂, r₂, C₂, hC₂, e₂⟩ := exists_forall_coeff_of_isCartierCombination h₂
  refine isCartierCombination_of_forall_coeff (r := Fin.append r₁ (-r₂))
    (C := Fin.append C₁ C₂)
    (fun i => Fin.addCases (fun j => by simpa using hC₁ j) (fun j => by simpa using hC₂ j) i)
    fun Γ => ?_
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  rw [DivisorWithCoeffs.coeff_sub, e₁, e₂]
  ring

end CartierCombination

/-! ### Affine functions along the smallest rational affine hull -/

section Hull

variable {p : ℕ}

/-- **An affine function that is nonnegative near `t_b` on an affine subspace vanishes at `t_b`
exactly when it vanishes at a nearby point `t_*`.** Reflecting `t_*` through `t_b`, and `t_b`
through `t_*`, stays in the subspace and in the neighbourhood. -/
private theorem eq_zero_iff_of_forall_nonneg {H : AffineSubspace ℝ (Fin p → ℝ)}
    {tb ts : Fin p → ℝ} (htb : tb ∈ H) (hts : ts ∈ H) {ε : ℝ} (hd : dist ts tb < ε / 2)
    (a : ℝ) (μ : Fin p → ℝ)
    (hnn : ∀ t ∈ H, dist t tb < ε → 0 ≤ a - ∑ j, (t j - tb j) * μ j) :
    a = 0 ↔ a - ∑ j, (ts j - tb j) * μ j = 0 := by
  set L := ∑ j, (ts j - tb j) * μ j with hL
  have hε : 0 < ε := by linarith [dist_nonneg (x := ts) (y := tb)]
  have h1 : (2 : ℝ) • tb - ts ∈ H := by
    have := H.smul_vsub_vadd_mem (1 : ℝ) htb hts htb
    convert this using 1
    ext j
    simp only [vsub_eq_sub, vadd_eq_add, one_smul, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  have h2 : (2 : ℝ) • ts - tb ∈ H := by
    have := H.smul_vsub_vadd_mem (1 : ℝ) hts htb hts
    convert this using 1
    ext j
    simp only [vsub_eq_sub, vadd_eq_add, one_smul, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  have d1 : dist ((2 : ℝ) • tb - ts) tb < ε := by
    rw [dist_eq_norm, show (2 : ℝ) • tb - ts - tb = -(ts - tb) by module, norm_neg,
      ← dist_eq_norm]
    linarith
  have d2 : dist ((2 : ℝ) • ts - tb) tb < ε := by
    rw [dist_eq_norm, show (2 : ℝ) • ts - tb - tb = (2 : ℝ) • (ts - tb) by module, norm_smul,
      ← dist_eq_norm, Real.norm_two]
    linarith
  have e1 : a - ∑ j, (((2 : ℝ) • tb - ts) j - tb j) * μ j = a + L := by
    rw [hL, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have e2 : a - ∑ j, (((2 : ℝ) • ts - tb) j - tb j) * μ j = a - 2 * L := by
    rw [hL, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have g0 : 0 ≤ a := by simpa using hnn tb htb (by simpa using hε)
  have g1 := hnn _ h1 d1
  have g2 := hnn _ h2 d2
  have gs := hnn ts hts (by linarith)
  constructor <;> intro ha <;> linarith

/-- Rational points are dense in the smallest rational affine hull. -/
private theorem exists_rat_mem_rationalAffineHull_dist_lt {tb t : Fin p → ℝ}
    (ht : t ∈ rationalAffineHull tb) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : Fin p → ℚ, (fun j => (q j : ℝ)) ∈ rationalAffineHull tb ∧
      dist (fun j => (q j : ℝ)) t < δ := by
  obtain ⟨m, p₀, e, -, -, hiff⟩ := exists_rational_frame tb
  obtain ⟨s, rfl⟩ := (hiff t).1 ht
  set F : (Fin m → ℝ) → (Fin p → ℝ) := fun s j => (p₀ j : ℝ) + ∑ i, s i * (e i j : ℝ) with hF
  have hFc : Continuous F := by
    rw [hF]
    fun_prop
  obtain ⟨η, hη, hηF⟩ := Metric.continuous_iff.mp hFc s δ hδ
  choose q hq using fun i => exists_rat_btwn (show s i - η < s i by linarith)
  refine ⟨fun j => p₀ j + ∑ i, q i * e i j, ?_, ?_⟩
  · rw [hiff]
    exact ⟨fun i => (q i : ℝ), funext fun j => by push_cast; rfl⟩
  · have := hηF (fun i => (q i : ℝ)) (by
      rw [dist_pi_lt_iff hη]
      intro i
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [(hq i).1, (hq i).2])
    convert this using 2
    funext j
    push_cast
    rfl

/-- **An affine function with rational values at rational points that vanishes at `t_b`
vanishes on the smallest rational affine hull of `t_b`.** -/
private theorem eq_zero_of_mem_rationalAffineHull {tb : Fin p → ℝ} (g : (Fin p → ℝ) → ℝ)
    (hg : ∃ (A : ℝ) (μ : Fin p → ℝ), ∀ t, g t = A - ∑ j, t j * μ j)
    (hq : ∀ q : Fin p → ℚ, ∃ c : ℚ, g (fun j => (q j : ℝ)) = c) (h0 : g tb = 0)
    {t : Fin p → ℝ} (ht : t ∈ rationalAffineHull tb) : g t = 0 := by
  classical
  obtain ⟨A, μ, hgA⟩ := hg
  obtain ⟨c₀, hc₀⟩ := hq 0
  choose c hc using fun j => hq (Pi.single j 1)
  have hA : A = c₀ := by simpa [hgA] using hc₀
  have hμ : ∀ j, μ j = c₀ - c j := fun j => by
    have := hc j
    rw [hgA] at this
    simp only [Pi.single_apply, apply_ite (fun q : ℚ => (q : ℝ)), Rat.cast_one, Rat.cast_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rw [← hA]
    linarith
  have hf : ∀ x, ratAffineForm (fun j => c j - c₀, c₀) x = g x := fun x => by
    have e : ∑ j, ((c j : ℝ) - c₀) * x j = -∑ j, x j * ((c₀ : ℝ) - c j) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [ratAffineForm, hgA, hA, hμ]
    push_cast
    linarith [e]
  rw [← hf]
  exact ht _ (by rwa [hf])

/-- Two affine functions on `ℝ^p` that agree at the rational points agree everywhere. -/
private theorem eq_of_forall_rat {g h : (Fin p → ℝ) → ℝ}
    (hg : ∃ (A : ℝ) (μ : Fin p → ℝ), ∀ t, g t = A - ∑ j, t j * μ j)
    (hh : ∃ (A : ℝ) (μ : Fin p → ℝ), ∀ t, h t = A - ∑ j, t j * μ j)
    (hq : ∀ q : Fin p → ℚ, g (fun j => (q j : ℝ)) = h (fun j => (q j : ℝ))) (t : Fin p → ℝ) :
    g t = h t := by
  classical
  obtain ⟨A, μ, hgA⟩ := hg
  obtain ⟨A', μ', hhA⟩ := hh
  have h0 : A = A' := by simpa [hgA, hhA] using hq 0
  have hμ : ∀ j, μ j = μ' j := fun j => by
    have := hq (Pi.single j 1)
    rw [hgA, hhA] at this
    simp only [Pi.single_apply, apply_ite (fun q : ℚ => (q : ℝ)), Rat.cast_one, Rat.cast_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    linarith
  rw [hgA, hhA, h0]
  simp [hμ]

/-- The function `t ↦ a - ∑ⱼ (tⱼ - sⱼ) μⱼ` is affine. -/
private theorem exists_affine_sub_sum (a : ℝ) (s μ : Fin p → ℝ) :
    ∃ (A : ℝ) (μ' : Fin p → ℝ), ∀ t : Fin p → ℝ,
      a - ∑ j, (t j - s j) * μ j = A - ∑ j, t j * μ' j :=
  ⟨a + ∑ j, s j * μ j, μ, fun t => by
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring⟩

/-- An affine function with rational values at rational points that is nonnegative at `t_b` is
nonnegative near `t_b` on the smallest rational affine hull of `t_b`. -/
private theorem eventually_nonneg_of_mem_rationalAffineHull {tb : Fin p → ℝ} {a : ℝ}
    (μ : Fin p → ℝ)
    (hrat : ∀ q : Fin p → ℚ, ∃ c : ℚ, a - ∑ j, ((fun j => (q j : ℝ)) j - tb j) * μ j = c)
    (h0 : 0 ≤ a) :
    ∀ᶠ t in 𝓝 tb, t ∈ rationalAffineHull tb → 0 ≤ a - ∑ j, (t j - tb j) * μ j := by
  rcases h0.eq_or_lt with h | h
  · refine Filter.Eventually.of_forall fun t ht => ?_
    rw [eq_zero_of_mem_rationalAffineHull (fun t => a - ∑ j, (t j - tb j) * μ j)
      (exists_affine_sub_sum _ _ _) hrat (by simp [← h]) ht]
  · have hc : Continuous fun t : Fin p → ℝ => a - ∑ j, (t j - tb j) * μ j := by fun_prop
    have := hc.tendsto tb
    simp only [sub_self, zero_mul, Finset.sum_const_zero, sub_zero] at this
    filter_upwards [this.eventually (lt_mem_nhds h)] with t ht _ using ht.le

end Hull

/-! ### Log discrepancies along a family of boundaries with Cartier directions -/

section Affine

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- **Log discrepancies move affinely along Cartier directions.** If `B_t - B_s = ∑ⱼ (tⱼ - sⱼ) Wⱼ`
with every `Wⱼ` a real combination of Cartier divisors, then for a divisor `D` over `X` there are
`μⱼ` such that a log discrepancy `a` of `D` for `(X, B_s)` gives the log discrepancy
`a - ∑ⱼ (tⱼ - sⱼ) μⱼ` for `(X, B_t)`. -/
private theorem exists_isLogDiscrepancy_affine {p : ℕ} (Bt : (Fin p → ℝ) → RDivisor X)
    (W : Fin p → RDivisor X) (hW : ∀ j, MMP.Flips.IsCartierCombination (W j))
    (hBt : ∀ t s Γ, (Bt t).coeff Γ = (Bt s).coeff Γ + ∑ j, (t j - s j) * (W j).coeff Γ)
    (D : DivisorOver ℂ sX) :
    ∃ μ : Fin p → ℝ, ∀ (n : ℕ) (s : Fin p → ℝ) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n (Bt s) D a → ∀ t,
        MMP.Intersection.IsLogDiscrepancy sX n (Bt t) D (a - ∑ j, (t j - s j) * μ j) := by
  classical
  choose m r L hL hWeq using hW
  let C : (Σ j, Fin (m j)) → Divisor X := fun x => L x.1 x.2
  obtain ⟨μ, hμ⟩ := exists_isLogDiscrepancy_add_sum C (fun x => hL x.1 x.2) D
  refine ⟨fun j => ∑ k, r j k * μ ⟨j, k⟩, fun n s a ha t => ?_⟩
  have hWc : ∀ j Γ, (W j).coeff Γ = ∑ k, r j k * ((L j k).coeff Γ : ℝ) := fun j Γ => by
    rw [hWeq j]
    simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs]
    exact MMP.Flips.coeff_sum_smul_toRDivisor (r j) (L j) Γ
  have := hμ n (Bt s) (Bt t) (fun x => (t x.1 - s x.1) * r x.1 x.2) a ha (fun Γ => by
    rw [hBt t s Γ, Fintype.sum_sigma]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hWc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [C]
    ring)
  convert this using 2
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The dimension index of a log discrepancy is the dimension of the base. -/
private theorem eq_of_isLogDiscrepancy {n m : ℕ} {B : RDivisor X} {D : DivisorOver ℂ sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n B D a) (hm : topologicalKrullDim X = m) :
    n = m := by
  exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq h).symm.trans hm

/-- `K + (∑ᵢ rᵢ Cᵢ - K) = ∑ᵢ rᵢ Cᵢ`, coefficientwise: the crepant boundary of a model. -/
private theorem coeff_add_coeff_sum_smul_sub {m : ℕ} (r : Fin m → ℝ) (C : Fin m → Divisor X)
    (K : Divisor X) (Γ : Mori.PrimeDivisor X) :
    (K.coeff Γ : ℝ) + (∑ i, r i • Divisor.toRDivisor (C i) - Divisor.toRDivisor K).coeff Γ =
      ∑ i, r i * (C i).coeff Γ := by
  rw [DivisorWithCoeffs.coeff_sub, MMP.Flips.coeff_sum_smul_toRDivisor, Divisor.coeff_toRDivisor]
  ring

end Affine

/-! ### Log discrepancies on a proper birational model -/

section Comparison

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]

/-- **Log discrepancies of the prime divisors of a model.** Let `K = div ω` be a canonical divisor
of `X`, `K + B = ∑ rᵢ Cᵢ` with Cartier `Cᵢ`, and `p : V ⟶ X` proper birational with pull-backs
`C'ᵢ = p^* Cᵢ`. A prime divisor `F` of `V` has log discrepancy
`1 + ord_F(p^*ω) - ∑ rᵢ coeff_F(C'ᵢ)` with respect to `(X, B)`. -/
private theorem isLogDiscrepancy_primeDivisor_of_model (hX : IsNormalVariety ℂ sX) {n : ℕ}
    {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (hKω : ∀ Γ, K.coeff Γ = Γ.ordForm ω) {Bv : RDivisor X}
    {m : ℕ} {r : Fin m → ℝ} {C : Fin m → Divisor X} (hC : ∀ i, (C i).IsCartier)
    (hsum : ∀ Γ : Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) + Bv.coeff Γ = ∑ i, r i * (C i).coeff Γ)
    {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] (p : V ⟶ X)
    [IsProper p] (hV : IsNormalVariety ℂ (p ≫ sX)) (hp : IsBirationalMorphism p)
    [IsDominant p] {C' : Fin m → Divisor V}
    (hC' : ∀ i, (C i).IsPullback p
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp p (C i)) (C' i))
    (F : Mori.PrimeDivisor V) :
    MMP.Intersection.IsLogDiscrepancy sX n Bv (⟨V, p, hV, hp, F⟩ : DivisorOver ℂ sX)
      (1 + F.ordForm (pullbackRationalPluriForms sX p ω) - ∑ i, r i * (C' i).coeff F) :=
  ⟨hX, ‹IsProper p›, ω, hω0, ⟨K, hK, hKω⟩, m, r, C, C', hC, hsum, fun i => ⟨_, hC' i⟩, rfl⟩

/-- **Crepant comparison of log discrepancies.** In the situation of
`isLogDiscrepancy_primeDivisor_of_model`, let `K_V = div(p^*ω)` be canonical and `B_V` the
`ℝ`-divisor with `K_V + B_V = ∑ rᵢ C'ᵢ = p^*(K + B)`. Then every proper divisor `D` over `V` has a
log discrepancy with respect to `(V, B_V)` which is also its log discrepancy, as a divisor over
`X`, with respect to `(X, B)`. -/
private theorem exists_isLogDiscrepancy_model_and_base (hX : IsNormalVariety ℂ sX) {n : ℕ}
    {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (hKω : ∀ Γ, K.coeff Γ = Γ.ordForm ω) {Bv : RDivisor X}
    {m : ℕ} {r : Fin m → ℝ} {C : Fin m → Divisor X} (hC : ∀ i, (C i).IsCartier)
    (hsum : ∀ Γ : Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) + Bv.coeff Γ = ∑ i, r i * (C i).coeff Γ)
    {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] (p : V ⟶ X)
    [IsProper p] (hV : IsNormalVariety ℂ (p ≫ sX)) (hp : IsBirationalMorphism p)
    [IsDominant p] [LocallyOfFiniteType (p ≫ sX)] [CompactSpace V] {C' : Fin m → Divisor V}
    (hC' : ∀ i, (C i).IsPullback p
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp p (C i)) (C' i))
    (hKV : (divisorOfForm (pullbackRationalPluriForms sX p ω)).IsCanonicalDivisor (p ≫ sX) n)
    {BV : RDivisor V}
    (hBV : ∀ Γ : Mori.PrimeDivisor V, (Γ.ordForm (pullbackRationalPluriForms sX p ω) : ℝ) +
      BV.coeff Γ = ∑ i, r i * (C' i).coeff Γ)
    (D : DivisorOver ℂ (p ≫ sX)) (hD : IsProper D.f) :
    ∃ a : ℝ, MMP.Intersection.IsLogDiscrepancy (p ≫ sX) n BV D a ∧
      MMP.Intersection.IsLogDiscrepancy sX n Bv (compDivisorOver p hV hp D) a := by
  classical
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  haveI := hD
  haveI : CompactSpace D.Y := QuasiCompact.compactSpace_of_compactSpace D.f
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX)
    hK.topologicalKrullDim_eq
  have hC'c : ∀ i, (C' i).IsCartier := fun i => isCartier_of_isPullback p (hC i) (hC' i)
  choose C'' hC'' using fun i =>
    MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f (hC'c i)
  have hωV0 : pullbackRationalPluriForms sX p ω ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' p
      hp.functionFieldMap_bijective hd hω0
  refine ⟨1 + D.ordPullback (pullbackRationalPluriForms sX p ω) - ∑ i, r i * (C'' i).coeff D.E,
    ⟨hV, hD, _, hωV0, ⟨divisorOfForm (pullbackRationalPluriForms sX p ω), hKV,
      fun Γ => coeff_divisorOfForm _ Γ⟩, m, r, C', C'', hC'c, hBV,
      fun i => ⟨_, hC'' i⟩, rfl⟩,
    ⟨hX, inferInstanceAs (IsProper (D.f ≫ p)), ω, hω0, ⟨K, hK, hKω⟩, m, r, C, C'', hC, hsum,
      fun i => ⟨_, MMP.ProgramBaseChange.divisor_isPullback_comp rfl (hC' i) (hC'' i)
        (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ p) (C i))⟩, ?_⟩⟩
  have hcomp := MMP.Flips.pullbackRationalPluriForms_comp (sX := sX) p D.f
    hp.functionFieldMap_bijective D.isBirationalMorphism.functionFieldMap_bijective hd ω
  have : (compDivisorOver p hV hp D).ordPullback ω =
      D.ordPullback (pullbackRationalPluriForms sX p ω) := by
    change D.E.ordForm (pullbackRationalPluriForms sX (D.f ≫ p) ω) =
      D.E.ordForm (pullbackRationalPluriForms (p ≫ sX) D.f (pullbackRationalPluriForms sX p ω))
    rw [hcomp]
    rfl
  rw [this]
  rfl

/-- **Crepant coefficients at non-exceptional primes.** In the situation of
`isLogDiscrepancy_primeDivisor_of_model`, for a prime divisor `F` of `V` with `p(η_F) = η_Q`,
`∑ rᵢ coeff_F(C'ᵢ) - ord_F(p^*ω) = coeff_Q(B)`: `p` is an isomorphism near `η_F`. -/
private theorem sum_sub_ordForm_eq_coeff (hX : IsNormalVariety ℂ sX) {n : ℕ}
    {ω : RationalPluriForms sX n 1} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {Bv : RDivisor X} {m : ℕ} {r : Fin m → ℝ} {C : Fin m → Divisor X} (hC : ∀ i, (C i).IsCartier)
    (hsum : ∀ Γ : Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) + Bv.coeff Γ = ∑ i, r i * (C i).coeff Γ)
    {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] (p : V ⟶ X)
    [IsProper p] (hV : IsNormalVariety ℂ (p ≫ sX)) (hp : IsBirationalMorphism p)
    [IsDominant p] [LocallyOfFiniteType (p ≫ sX)] [CompactSpace V] {C' : Fin m → Divisor V}
    (hC' : ∀ i, (C i).IsPullback p
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp p (C i)) (C' i))
    {F : Mori.PrimeDivisor V} {Q : Mori.PrimeDivisor X} (hFQ : p F.genericPoint = Q.genericPoint) :
    ∑ i, r i * ((C' i).coeff F : ℝ) - F.ordForm (pullbackRationalPluriForms sX p ω) =
      Bv.coeff Q := by
  obtain ⟨E, hE, hEiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX hV hp Q
  haveI : IsSeparated (p ≫ sX) := hV.1.toIsSeparated
  haveI : IsSeparated p := IsSeparated.of_comp p sX
  have hEF : E = F := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Fourfold.Oai4C1.eq_of_map_eq_genericPoint hp hE hFQ)
  subst hEF
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX)
    hK.topologicalKrullDim_eq
  rw [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p hp.functionFieldMap_bijective
    hd E Q hFQ ω]
  have : ∀ i, ((C' i).coeff E : ℝ) = (C i).coeff Q := fun i => by
    exact_mod_cast MMP.Positivity.coeff_eq_of_isPullback E Q hFQ (hC i) (hC' i)
  simp only [this]
  linarith [hsum Q]

end Comparison

/-! ### Lc boundaries near a real lc boundary along its rational hull -/

section LcNeighbourhood

/-- The coefficient vector `b₀ + ∑ⱼ tⱼ wⱼ` of the point `t` of the rational Cartier locus. -/
private def coeffVec {ι : Type} {p : ℕ} (b₀ : ι → ℚ) (w : Fin p → ι → ℚ) (t : Fin p → ℝ) :
    ι → ℝ :=
  fun i => b₀ i + ∑ j, t j * w j i

/-- The rational coefficient vector `b₀ + ∑ⱼ qⱼ wⱼ` of a rational point `q`. -/
private def coeffVecQ {ι : Type} {p : ℕ} (b₀ : ι → ℚ) (w : Fin p → ι → ℚ) (q : Fin p → ℚ) :
    ι → ℚ :=
  fun i => b₀ i + ∑ j, q j * w j i

private theorem coeffVec_cast {ι : Type} {p : ℕ} (b₀ : ι → ℚ) (w : Fin p → ι → ℚ)
    (q : Fin p → ℚ) (i : ι) :
    coeffVec b₀ w (fun j => (q j : ℝ)) i = (coeffVecQ b₀ w q i : ℝ) := by
  simp [coeffVec, coeffVecQ]

private theorem continuous_coeffVec {ι : Type} {p : ℕ} (b₀ : ι → ℚ) (w : Fin p → ι → ℚ) (i : ι) :
    Continuous fun t : Fin p → ℝ => coeffVec b₀ w t i := by
  unfold coeffVec
  fun_prop

/-- A coefficient `c(t)ᵢ ≤ 1` at `t_b` stays `≤ 1` near `t_b` on the rational hull of `t_b`. -/
private theorem eventually_coeffVec_le_one {ι : Type} {p : ℕ} (b₀ : ι → ℚ) (w : Fin p → ι → ℚ)
    {tb : Fin p → ℝ} {i : ι} (hle : coeffVec b₀ w tb i ≤ 1) :
    ∀ᶠ t in 𝓝 tb, t ∈ rationalAffineHull tb → coeffVec b₀ w t i ≤ 1 := by
  rcases hle.eq_or_lt with h | h
  · refine Filter.Eventually.of_forall fun t ht => le_of_eq ?_
    have := eq_zero_of_mem_rationalAffineHull (fun t => coeffVec b₀ w t i - 1)
      ⟨(b₀ i : ℝ) - 1, fun j => -(w j i : ℝ), fun t => by
        simp only [coeffVec, mul_neg, Finset.sum_neg_distrib]
        ring⟩
      (fun q => ⟨coeffVecQ b₀ w q i - 1, by simp [coeffVec_cast]⟩) (by simp [h]) ht
    linarith
  · filter_upwards [((continuous_coeffVec b₀ w i).tendsto tb).eventually (gt_mem_nhds h)]
      with t ht _ using ht.le

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The coefficient of `∑ᵢ yᵢ Pᵢ` along `P i`, for an injective family `P`. -/
private theorem coeff_sum_single_self {ι : Type} [Fintype ι] {R : Type*} [AddCommMonoid R]
    {P : ι → Mori.PrimeDivisor X} (hP : Function.Injective P) (y : ι → R) (i : ι) :
    (∑ i, Finsupp.single (P i) (y i) : DivisorWithCoeffs R X).coeff (P i) = y i := by
  classical
  rw [coeff_sum_single, Finset.sum_eq_single i (fun j _ hj => if_neg (fun h => hj (hP h)))
    (by simp)]
  simp

/-- The coefficient of `∑ᵢ yᵢ Pᵢ` along a prime divisor that is no `P i` vanishes. -/
private theorem coeff_sum_single_of_forall_ne {ι : Type} [Fintype ι] {R : Type*}
    [AddCommMonoid R] {P : ι → Mori.PrimeDivisor X} (y : ι → R) {Γ : Mori.PrimeDivisor X}
    (hΓ : ∀ i, P i ≠ Γ) :
    (∑ i, Finsupp.single (P i) (y i) : DivisorWithCoeffs R X).coeff Γ = 0 := by
  classical
  rw [coeff_sum_single]
  exact Finset.sum_eq_zero fun i _ => if_neg (hΓ i)

/-- `∑ᵢ yᵢ Pᵢ` with nonzero coefficients has support `{P i}`. -/
private theorem support_sum_single {ι : Type} [Fintype ι] {R : Type*} [AddCommMonoid R]
    [DecidableEq (Mori.PrimeDivisor X)] {P : ι → Mori.PrimeDivisor X}
    (hP : Function.Injective P) (y : ι → R) (hy : ∀ i, y i ≠ 0) :
    Finsupp.support (∑ i, Finsupp.single (P i) (y i) : DivisorWithCoeffs R X) =
      Finset.univ.image P := by
  classical
  ext Γ
  rw [Finsupp.mem_support_iff, Finset.mem_image]
  change (∑ i, Finsupp.single (P i) (y i) : DivisorWithCoeffs R X).coeff Γ ≠ 0 ↔ _
  by_cases h : ∃ i, P i = Γ
  · obtain ⟨i, rfl⟩ := h
    rw [coeff_sum_single_self hP]
    exact ⟨fun _ => ⟨i, Finset.mem_univ _, rfl⟩, fun _ => hy i⟩
  · push Not at h
    rw [coeff_sum_single_of_forall_ne y h]
    simp only [ne_eq, not_true_eq_false, Finset.mem_univ, true_and, false_iff, not_exists]
    exact h

/-- An `ℝ`-divisor is the sum over its support of its coefficients. -/
private theorem sum_single_support_eq (B : RDivisor X) :
    (∑ i : B.support, Finsupp.single i.1 (B i.1) : RDivisor X) = B := by
  refine DivisorWithCoeffs.ext' fun Γ => ?_
  by_cases hΓ : Γ ∈ B.support
  · rw [show Γ = (Subtype.val ⟨Γ, hΓ⟩ : Mori.PrimeDivisor X) from rfl,
      coeff_sum_single_self Subtype.val_injective]
    rfl
  · rw [coeff_sum_single_of_forall_ne (fun i : B.support => B i.1)
      (fun i h => hΓ (by rw [← h]; exact i.2)), DivisorWithCoeffs.coeff_apply,
      Finsupp.notMem_support_iff.mp hΓ]

/-- Two divisors with the same support have the same support set. -/
private theorem supp_eq_of_support_eq {R R' : Type*} [Zero R] [Zero R']
    {D : DivisorWithCoeffs R X} {D' : DivisorWithCoeffs R' X}
    (h : Finsupp.support D = Finsupp.support D') : D.supp = D'.supp := by
  unfold DivisorWithCoeffs.supp
  rw [h]

/-- The exceptional prime divisors of a log resolution are among finitely many. -/
private theorem exists_finset_isExceptional {k : Type} [Field k] {sX : X ⟶ Spec (.of k)}
    {D : RDivisor X} {Y : Scheme.{0}} {f : Y ⟶ X} (hf : MMP.Mori.IsLogResolution sX D f) :
    ∃ S : Finset (Mori.PrimeDivisor Y), ∀ F : Mori.PrimeDivisor Y,
      RationalMap.IsExceptional (X := Y) f.toRationalMap F → F ∈ S := by
  classical
  have hmem : ∀ F : Mori.PrimeDivisor Y,
      RationalMap.IsExceptional (X := Y) f.toRationalMap F →
        F.genericPoint ∈ ((exceptionalSet f ⊔ D.supp.preimage f.continuous :
          TopologicalSpace.Closeds Y) : Set Y) := fun F hF =>
    Or.inl (MMP.Positivity.support_subset_exceptionalSet F hF
      (MMP.Flips.primeDivisor_genericPoint_mem_support F))
  rcases hf.isSNCSubset with h0 | ⟨s, hs, -⟩
  · refine ⟨∅, fun F hF => ?_⟩
    simpa [h0] using hmem F hF
  · refine ⟨s, fun F hF => ?_⟩
    have := hmem F hF
    rw [← hs] at this
    obtain ⟨E, hE, hgen⟩ := Set.mem_iUnion₂.mp this
    rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen] at hE

/-- The coefficients of `∑ᵢ (b₀ + ∑ⱼ tⱼ wⱼ)ᵢ Pᵢ` move affinely in `t`. -/
private theorem coeff_family_eq {ι : Type} [Fintype ι] (P : ι → Mori.PrimeDivisor X) {p : ℕ}
    (b₀ : ι → ℚ) (w : Fin p → ι → ℚ) (t s : Fin p → ℝ) (Γ : Mori.PrimeDivisor X) :
    (∑ i, Finsupp.single (P i) (coeffVec b₀ w t i) : RDivisor X).coeff Γ =
      (∑ i, Finsupp.single (P i) (coeffVec b₀ w s i) : RDivisor X).coeff Γ +
        ∑ j, (t j - s j) * (∑ i, Finsupp.single (P i) ((w j i : ℚ) : ℝ) : RDivisor X).coeff Γ := by
  classical
  simp only [coeff_sum_single, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin p)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · simp only [coeffVec, mul_one, sub_mul, Finset.sum_sub_distrib]
    ring
  · simp

/-- The rational point `q` gives the `ℚ`-divisor with the same coefficients. -/
private theorem toRDivisor_family {ι : Type} [Fintype ι] (P : ι → Mori.PrimeDivisor X) {p : ℕ}
    (b₀ : ι → ℚ) (w : Fin p → ι → ℚ) (q : Fin p → ℚ) :
    QDivisor.toRDivisor (∑ i, Finsupp.single (P i) (coeffVecQ b₀ w q i) : QDivisor X) =
      ∑ i, Finsupp.single (P i) (coeffVec b₀ w (fun j => (q j : ℝ)) i) := by
  classical
  refine DivisorWithCoeffs.ext' fun Γ => ?_
  rw [QDivisor.coeff_toRDivisor, coeff_sum_single, coeff_sum_single]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [coeffVec_cast]

variable [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]

/-- **Lc boundaries near `B` along its rational hull** (the log resolution step). Let
`B = ∑ᵢ bᵢ Pᵢ` be an effective lc boundary lying in a rational Cartier locus
`c(t) = b₀ + ∑ⱼ tⱼ wⱼ`, `b = c(t_b)`, and let `f : Y ⟶ X` be a projective log resolution of
`(X, B)`. Then near `t_b` along the smallest rational affine hull of `t_b` every `c(t)` is
positive, and every rational point gives an lc pair `(X, ∑ᵢ c(q)ᵢ Pᵢ)`: its crepant boundary on
`Y` has coefficients at most one, since the log discrepancies of the finitely many exceptional
primes of `Y` are rational affine functions of `t`, nonnegative at `t_b`, and the coefficients
equal to one at `t_b` stay equal to one on the hull. -/
private theorem exists_pos_forall_isLogCanonicalPair (hXv : IsNormalVariety ℂ sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {ω : RationalPluriForms sX n 1}
    (hω0 : ω ≠ 0) (hKω : ∀ Γ, K.coeff Γ = Γ.ordForm ω) {ι : Type} [Fintype ι]
    {P : ι → Mori.PrimeDivisor X} (hP : Function.Injective P) {p : ℕ} (b₀ : ι → ℚ)
    (w : Fin p → ι → ℚ)
    (hQC : ∀ q : Fin p → ℚ, (Divisor.toQDivisor K +
      ∑ i, Finsupp.single (P i) (coeffVecQ b₀ w q i)).IsQCartier)
    (hW : ∀ j, MMP.Flips.IsCartierCombination
      (∑ i, Finsupp.single (P i) ((w j i : ℚ) : ℝ) : RDivisor X))
    {tb : Fin p → ℝ} (hpos : ∀ i, 0 < coeffVec b₀ w tb i)
    {mB : ℕ} {rB : Fin mB → ℝ} {CB : Fin mB → Divisor X} (hCB : ∀ i, (CB i).IsCartier)
    (hsumB : ∀ Γ : Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) +
      (∑ i, Finsupp.single (P i) (coeffVec b₀ w tb i) : RDivisor X).coeff Γ =
        ∑ i, rB i * (CB i).coeff Γ)
    (hlc : ∀ (n' : ℕ) (D : DivisorOver ℂ sX) (a : ℝ), MMP.Intersection.IsLogDiscrepancy sX n'
      (∑ i, Finsupp.single (P i) (coeffVec b₀ w tb i)) D a → 0 ≤ a)
    {Y : Scheme.{0}} {f : Y ⟶ X}
    (hf : MMP.Mori.IsLogResolution sX (∑ i, Finsupp.single (P i) (coeffVec b₀ w tb i)) f)
    (hfp : IsProjectiveMorphism f) :
    ∃ ε > 0, ∀ t ∈ rationalAffineHull tb, dist t tb < ε → (∀ i, 0 < coeffVec b₀ w t i) ∧
      ∀ q : Fin p → ℚ, (fun j => (q j : ℝ)) = t →
        MMP.Intersection.IsLogCanonicalPair sX
          (∑ i, Finsupp.single (P i) (coeffVecQ b₀ w q i) : QDivisor X) := by
  classical
  set Bt : (Fin p → ℝ) → RDivisor X := fun t => ∑ i, Finsupp.single (P i) (coeffVec b₀ w t i)
  set ΔQ : (Fin p → ℚ) → QDivisor X :=
    fun q => ∑ i, Finsupp.single (P i) (coeffVecQ b₀ w q i)
  set W : Fin p → RDivisor X := fun j => ∑ i, Finsupp.single (P i) ((w j i : ℚ) : ℝ)
  have hBtQ : ∀ q, QDivisor.toRDivisor (ΔQ q) = Bt (fun j => (q j : ℝ)) := fun q =>
    toRDivisor_family P b₀ w q
  have hBt : ∀ t s Γ, (Bt t).coeff Γ = (Bt s).coeff Γ + ∑ j, (t j - s j) * (W j).coeff Γ :=
    fun t s Γ => coeff_family_eq P b₀ w t s Γ
  have hPair : ∀ q, MMP.Mori.IsPair sX (ΔQ q) := fun q => ⟨hXv, n, K, hK, hQC q⟩
  have hPairW : ∀ q, MMP.Mori.IsPairWith sX n K (ΔQ q) := fun q => ⟨hXv, hK, hQC q⟩
  -- the log resolution
  have hres := hf.toIsSmoothResolution
  obtain ⟨hY, -, -⟩ := hres.isNormalVariety hXv
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : IsNormal Y := hY.2
  haveI : IsProper f := hres.isProper
  have hfb : IsBirationalMorphism f := hres.isBirationalMorphism
  haveI : IsDominant f := hfb.isDominant
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  choose C' hC' using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant f (hCB i)
  let DF : Mori.PrimeDivisor Y → DivisorOver ℂ sX := fun F => ⟨Y, f, hY, hfb, F⟩
  set aF : Mori.PrimeDivisor Y → ℝ := fun F =>
    1 + F.ordForm (pullbackRationalPluriForms sX f ω) - ∑ i, rB i * (C' i).coeff F
  have haF : ∀ F, MMP.Intersection.IsLogDiscrepancy sX n (Bt tb) (DF F) (aF F) := fun F =>
    isLogDiscrepancy_primeDivisor_of_model hXv hω0 hK hKω hCB hsumB f hY hfb hC' F
  obtain ⟨S, hS⟩ := exists_finset_isExceptional hf
  choose μ hμ using fun F => exists_isLogDiscrepancy_affine Bt W hW hBt (DF F)
  have hgF : ∀ F t, MMP.Intersection.IsLogDiscrepancy sX n (Bt t) (DF F)
      (aF F - ∑ j, (t j - tb j) * μ F j) := fun F t => hμ F n tb (aF F) (haF F) t
  have hrat : ∀ F (q : Fin p → ℚ), ∃ c : ℚ,
      aF F - ∑ j, ((fun j => (q j : ℝ)) j - tb j) * μ F j = c := by
    intro F q
    obtain ⟨d, hd⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy (hPair q) hK (DF F)
    have h1 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hd
      (inferInstanceAs (IsProper f))
    rw [hBtQ] at h1
    refine ⟨1 + d, ?_⟩
    push_cast
    exact MMP.Threefold.Bridges.IsLogDiscrepancy.unique (hgF F _) h1
  -- the coefficients `bᵢ` are at most one
  have hle1 : ∀ i, coeffVec b₀ w tb i ≤ 1 := by
    intro i
    obtain ⟨n₀, h₀⟩ := MMP.Fourfold.isLogDiscrepancy_ofPrimeDivisor hXv (hPair 0) (P i)
    obtain rfl := eq_of_isLogDiscrepancy h₀ hK.topologicalKrullDim_eq
    rw [hBtQ] at h₀
    obtain ⟨μ₀, hμ₀⟩ := exists_isLogDiscrepancy_affine Bt W hW hBt
      (DivisorOver.ofPrimeDivisor ℂ hXv (P i))
    have key := hμ₀ n₀ _ _ h₀
    have hagree : ∀ t, (1 - ((ΔQ 0).coeff (P i) : ℝ)) -
        ∑ j, (t j - (fun j => (((0 : Fin p → ℚ) j : ℚ) : ℝ)) j) * μ₀ j =
          1 - coeffVec b₀ w t i := by
      refine eq_of_forall_rat (exists_affine_sub_sum _ _ _)
        ⟨1 - b₀ i, fun j => (w j i : ℝ), fun t => by simp only [coeffVec]; ring⟩ fun q => ?_
      obtain ⟨nq, hq⟩ := MMP.Fourfold.isLogDiscrepancy_ofPrimeDivisor hXv (hPair q) (P i)
      rw [hBtQ] at hq
      rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique (key _) hq, coeff_sum_single_self hP,
        coeffVec_cast]
    have := hlc n₀ _ _ (key tb)
    rw [hagree] at this
    linarith
  have hev_pos : ∀ i, ∀ᶠ t in 𝓝 tb, 0 < coeffVec b₀ w t i := fun i =>
    ((continuous_coeffVec b₀ w i).tendsto tb).eventually (lt_mem_nhds (hpos i))
  have hev : ∀ᶠ t in 𝓝 tb, (∀ F ∈ S, t ∈ rationalAffineHull tb →
      0 ≤ aF F - ∑ j, (t j - tb j) * μ F j) ∧ (∀ i, 0 < coeffVec b₀ w t i) ∧
      (∀ i, t ∈ rationalAffineHull tb → coeffVec b₀ w t i ≤ 1) :=
    ((Filter.eventually_all_finset S).2 fun F _ =>
      eventually_nonneg_of_mem_rationalAffineHull (μ F) (hrat F) (hlc n _ _ (haF F))).and
      ((Filter.eventually_all.2 hev_pos).and
        (Filter.eventually_all.2 fun i => eventually_coeffVec_le_one b₀ w (hle1 i)))
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, fun t ht hdt => ⟨(hεP hdt).2.1, fun q hq => ?_⟩⟩
  obtain ⟨hFS, hposi, hlei⟩ := hεP hdt
  subst hq
  -- the rational pair `(X, Δ_q)` is lc
  have hnn : ∀ Γ, 0 ≤ (ΔQ q).coeff Γ := by
    intro Γ
    rw [coeff_sum_single]
    refine Finset.sum_nonneg fun i _ => ?_
    split_ifs
    · have := hposi i
      rw [coeffVec_cast] at this
      exact_mod_cast this.le
    · exact le_rfl
  have hP4 : MMP.Fourfold.IsPair sX (ΔQ q) := ⟨inferInstance, inferInstance, hPair q, hnn⟩
  have hsupp : (QDivisor.toRDivisor (ΔQ q)).supp = (Bt tb).supp := by
    rw [hBtQ]
    apply supp_eq_of_support_eq
    rw [support_sum_single hP _ (fun i => (hposi i).ne'),
      support_sum_single hP _ (fun i => (hpos i).ne')]
  have hπ : MMP.Fourfold.IsLogResolution sX (ΔQ q) f :=
    { toIsLogResolution :=
        { toIsSmoothResolution := hres
          isPureCodimOne_exceptionalSet := hf.isPureCodimOne_exceptionalSet
          isSNCSubset := by
            rw [hsupp]
            exact hf.isSNCSubset }
      isProjectiveMorphism := hfp }
  obtain ⟨⟨BW, hBW, -⟩, -⟩ := MMP.Mori.IsPair.existsUnique_isCrepantBoundary (hPair q) hK f hY hfb
  rw [isLogCanonicalPair_iff_forall_coeff_le_one sX hP4 hπ hY hBW]
  intro F
  by_cases hex : (DF F).IsExceptional
  · have h1 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hBW F)
      (inferInstanceAs (IsProper f))
    rw [hBtQ] at h1
    have h2 := MMP.Threefold.Bridges.IsLogDiscrepancy.unique (hgF F _) h1
    have h3 := hFS F (hS F hex) ht
    have : ((BW.coeff F : ℚ) : ℝ) ≤ 1 := by
      push_cast at h2
      linarith
    exact_mod_cast this
  · obtain ⟨Q, -, hQ⟩ :=
      MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff (hPairW q) (DF F) hex
    have := MMP.Mori.IsDiscrepancy.eq (hBW F) hQ
    have hBWF : BW.coeff F = (ΔQ q).coeff Q := by linarith
    rw [hBWF]
    by_cases hQi : ∃ i, P i = Q
    · obtain ⟨i, rfl⟩ := hQi
      rw [coeff_sum_single_self hP]
      have := hlei i ht
      rw [coeffVec_cast] at this
      exact_mod_cast this
    · push Not at hQi
      rw [coeff_sum_single_of_forall_ne _ hQi]
      norm_num

/-- **Lc boundaries at the real points near `t_b`.** If the rational points of the hull of `t_b`
near `t_b` give lc boundaries, so do the real ones: a log discrepancy at a real point `t` is the
limit of the log discrepancies at nearby rational points, by
`exists_isLogDiscrepancy_affine`. -/
private theorem nonneg_of_isLogDiscrepancy_of_mem_rationalAffineHull
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {p : ℕ} (Bt : (Fin p → ℝ) → RDivisor X)
    (W : Fin p → RDivisor X) (hW : ∀ j, MMP.Flips.IsCartierCombination (W j))
    (hBt : ∀ t s Γ, (Bt t).coeff Γ = (Bt s).coeff Γ + ∑ j, (t j - s j) * (W j).coeff Γ)
    {tb : Fin p → ℝ} {ε : ℝ}
    (hlcq : ∀ q : Fin p → ℚ, (fun j => (q j : ℝ)) ∈ rationalAffineHull tb →
      dist (fun j => (q j : ℝ)) tb < ε → ∀ (n : ℕ) (D : DivisorOver ℂ sX) (a : ℝ),
        MMP.Intersection.IsLogDiscrepancy sX n (Bt fun j => (q j : ℝ)) D a → 0 ≤ a)
    {t : Fin p → ℝ} (ht : t ∈ rationalAffineHull tb) (hdt : dist t tb < ε) {n : ℕ}
    {D : DivisorOver ℂ sX} {a : ℝ} (ha : MMP.Intersection.IsLogDiscrepancy sX n (Bt t) D a) :
    0 ≤ a := by
  obtain ⟨μ, hμ⟩ := exists_isLogDiscrepancy_affine Bt W hW hBt D
  by_contra hneg
  push Not at hneg
  set M : ℝ := ∑ j, |μ j| + 1 with hM
  have hM0 : 0 < M := by positivity
  set δ : ℝ := min (ε - dist t tb) (-a / M)
  have hδ0 : 0 < δ := lt_min (by linarith) (div_pos (by linarith) hM0)
  obtain ⟨q, hqH, hqd⟩ := exists_rat_mem_rationalAffineHull_dist_lt ht hδ0
  have hq1 : dist (fun j => (q j : ℝ)) tb < ε := by
    have := dist_triangle (fun j => (q j : ℝ)) t tb
    have := min_le_left (ε - dist t tb) (-a / M)
    linarith
  have h := hlcq q hqH hq1 n D _ (hμ n t a ha _)
  have hbound : |∑ j, ((q j : ℝ) - t j) * μ j| ≤ dist (fun j => (q j : ℝ)) t * M := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hM, mul_add, mul_one, Finset.mul_sum]
    have : ∑ j, |((q j : ℝ) - t j) * μ j| ≤ ∑ j, dist (fun j => (q j : ℝ)) t * |μ j| :=
      Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        have := dist_le_pi_dist (fun j => (q j : ℝ)) t j
        rwa [Real.dist_eq] at this
    linarith [dist_nonneg (x := (fun j => (q j : ℝ))) (y := t)]
  have hlt : dist (fun j => (q j : ℝ)) t * M < -a := by
    have := min_le_right (ε - dist t tb) (-a / M)
    calc dist (fun j => (q j : ℝ)) t * M < δ * M := by gcongr
      _ ≤ -a / M * M := by gcongr
      _ = -a := by field_simp
  have := neg_abs_le (∑ j, ((q j : ℝ) - t j) * μ j)
  linarith

end LcNeighbourhood

/-- **Real dlt modification with a nonfactorial source.** Assume `P(n)`
(`MMP.Fourfold.ProjectiveFloorProgramInputs`). Let `X` be a normal projective complex variety of
dimension `n` with canonical divisor `K`, and `B` an `ℝ`-divisor with `(X, B)` an effective lc pair
(`MMP.Fourfold.IsRealLcPair`). Then there are a projective birational morphism `p : V ⟶ X` from a
`ℚ`-factorial normal projective variety and an `ℝ`-divisor `B_V` on `V`, equal to `p⁻¹_* B` away
from the `p`-exceptional prime divisors and with coefficient one along each of them, such that
`(V, B_V)` is dlt (`MMP.Fourfold.IsRealDltPair`), `K_V + B_V = p^*(K + B)` for a canonical divisor
`K_V` of `V` with `p_* K_V = K`, and every `p`-exceptional prime divisor has log discrepancy zero
with respect to `(X, B)`. -/
@[mmp "lem_fourfold_real_dlt_modification_normal_source"]
public theorem _root_.MMP.Fourfold.exists_isQFactorial_dltModification_of_isRealLcPair
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (n : ℕ) (hP : ProjectiveFloorProgramInputs n)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = n)
    (K : Divisor X) (hK : K.IsCanonicalDivisor sX n)
    (B : RDivisor X) (hlc : IsRealLcPair sX B) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (p : V ⟶ X) (hV : IsQFactorial (p ≫ sX)) (hp : IsBirationalMorphism p) (BV : RDivisor V),
      MMP.Mori.IsProjectiveVariety ℂ (p ≫ sX) ∧ IsProjectiveMorphism p ∧
      (∀ P : MMP.Mori.PrimeDivisor V, RationalMap.IsExceptional (X := V) p.toRationalMap P →
        BV.coeff P = 1) ∧
      (∀ P : MMP.Mori.PrimeDivisor V, ¬ RationalMap.IsExceptional (X := V) p.toRationalMap P →
        BV.coeff P = (inverseTransformDivisor p B).coeff P) ∧
      IsRealDltPair (p ≫ sX) BV ∧
      (∃ KV : Divisor V, KV.IsCanonicalDivisor (p ≫ sX) n ∧
        RationalMap.transformDivisor p.toRationalMap KV = K ∧
        MMP.Flips.IsRCartierPullback p (MMP.Flips.logCanonicalDivisor K B)
          (MMP.Flips.logCanonicalDivisor KV BV)) ∧
      ∀ P : MMP.Mori.PrimeDivisor V, RationalMap.IsExceptional (X := V) p.toRationalMap P →
        MMP.Intersection.IsLogDiscrepancy sX n B (⟨V, p, hV.1, hp, P⟩ : DivisorOver ℂ sX) 0 := by
  classical
  obtain ⟨hXv, hBnn, ⟨n₀, K₀, hK₀, hR⟩, hlog⟩ := hlc
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hXv.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  /- `B = ∑ bᵢ Pᵢ` over its support, and `K + B` as a real combination of Cartier divisors. -/
  let P : B.support → Mori.PrimeDivisor X := Subtype.val
  have hPinj : Function.Injective P := Subtype.val_injective
  let b : B.support → ℝ := fun i => B i.1
  have hBsum : (∑ i, Finsupp.single (P i) (b i) : RDivisor X) = B := sum_single_support_eq B
  have hbpos : ∀ i, 0 < b i := fun i =>
    lt_of_le_of_ne (hBnn i.1) (Ne.symm (Finsupp.mem_support_iff.mp i.2))
  obtain ⟨φ, hφ⟩ := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hXv hK hK₀
  obtain ⟨m₀, r₀, C₀, hC₀, hR'⟩ := hR
  let rB : Fin (m₀ + 1) → ℝ := Fin.cons 1 r₀
  let CB : Fin (m₀ + 1) → Divisor X := Fin.cons (principalDivisor φ) C₀
  have hCB : ∀ i, (CB i).IsCartier := fun i =>
    Fin.cases (Divisor.isCartier_principalDivisor φ) hC₀ i
  have hKB : ∀ Γ, (K.coeff Γ : ℝ) + B.coeff Γ = ∑ i, rB i * ((CB i).coeff Γ : ℝ) := by
    intro Γ
    have h1 := hR' Γ
    rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor] at h1
    have h2 : ((principalDivisor φ).coeff Γ : ℝ) = K.coeff Γ - K₀.coeff Γ := by
      rw [← hφ]
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.sub_apply, Int.cast_sub]
    rw [Fin.sum_univ_succ]
    simp only [rB, CB, Fin.cons_zero, Fin.cons_succ, one_mul]
    rw [h2, ← h1]
    ring
  have hb : MMP.Flips.IsCartierCombination
      (Divisor.toRDivisor K + ∑ i, Finsupp.single (P i) (b i)) :=
    isCartierCombination_of_forall_coeff hCB fun Γ => by
      rw [hBsum, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, hKB]
  /- The rational Cartier locus `V = b₀ + span(w)` through `b`. -/
  obtain ⟨V, b₀, p, w, hVeq, hbV, hcartR, hcartQ, -⟩ :=
    exists_rat_affineSubspace_isCartierCombination_and_coeff_pullback_affine sX hXv hK P b hb
  have hmemV : ∀ t : Fin p → ℝ, coeffVec b₀ w t ∈ V := by
    intro t
    rw [hVeq, AffineSubspace.mem_mk', Submodule.mem_span_range_iff_exists_fun]
    refine ⟨t, funext fun i => ?_⟩
    simp [coeffVec, Finset.sum_apply]
  obtain ⟨tb, htb⟩ : ∃ tb : Fin p → ℝ, coeffVec b₀ w tb = b := by
    rw [hVeq, AffineSubspace.mem_mk', Submodule.mem_span_range_iff_exists_fun] at hbV
    obtain ⟨t, ht⟩ := hbV
    refine ⟨t, funext fun i => ?_⟩
    have := congrFun ht i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vsub_eq_sub, Pi.sub_apply] at this
    simp only [coeffVec]
    linarith
  set Bt : (Fin p → ℝ) → RDivisor X := fun t => ∑ i, Finsupp.single (P i) (coeffVec b₀ w t i)
    with hBt_def
  set ΔQ : (Fin p → ℚ) → QDivisor X :=
    fun q => ∑ i, Finsupp.single (P i) (coeffVecQ b₀ w q i)
  set W : Fin p → RDivisor X := fun j => ∑ i, Finsupp.single (P i) ((w j i : ℚ) : ℝ)
  have hBtb : Bt tb = B := by
    rw [← hBsum]
    simp only [hBt_def, htb]
  have hBtQ : ∀ q, QDivisor.toRDivisor (ΔQ q) = Bt (fun j => (q j : ℝ)) := fun q =>
    toRDivisor_family P b₀ w q
  have hBtc : ∀ t s Γ, (Bt t).coeff Γ = (Bt s).coeff Γ + ∑ j, (t j - s j) * (W j).coeff Γ :=
    fun t s Γ => coeff_family_eq P b₀ w t s Γ
  have hcartΦ : ∀ t, MMP.Flips.IsCartierCombination (Divisor.toRDivisor K + Bt t) := fun t =>
    hcartR _ (hmemV t)
  have hW : ∀ j, MMP.Flips.IsCartierCombination (W j) := by
    intro j
    convert isCartierCombination_sub (hcartΦ (Pi.single j 1)) (hcartΦ 0) using 1
    refine DivisorWithCoeffs.ext' fun Γ => ?_
    have := hBtc (Pi.single j 1) 0 Γ
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.sub_apply, Finsupp.add_apply] at this ⊢
    rw [this]
    simp only [Pi.single_apply, Pi.zero_apply, sub_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hQC : ∀ q : Fin p → ℚ, (Divisor.toQDivisor K +
      ∑ i, Finsupp.single (P i) (coeffVecQ b₀ w q i)).IsQCartier := by
    intro q
    refine (MMP.Mori.QDivisor.isCartierCombination_iff_isQCartier _).mp (hcartQ _ ?_)
    convert hmemV (fun j => (q j : ℝ)) using 1
    funext i
    exact (coeffVec_cast b₀ w q i).symm
  /- A rational top form with `K = div ω`, and a projective log resolution of `(X, B)`. -/
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXv hK
  have hsumB : ∀ Γ : Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) + (Bt tb).coeff Γ =
      ∑ i, rB i * (CB i).coeff Γ := fun Γ => by
    rw [hωK Γ, hBtb]
    exact hKB Γ
  have hlcB : ∀ (n' : ℕ) (D : DivisorOver ℂ sX) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n' (Bt tb) D a → 0 ≤ a := by
    rw [hBtb]
    exact hlog
  obtain ⟨Y, f, hf, hfp⟩ := MMP.Mori.exists_isLogResolution_isProjectiveMorphism sX hXv (Bt tb)
  have hpos : ∀ i, 0 < coeffVec b₀ w tb i := by
    rw [htb]
    exact hbpos
  obtain ⟨ε, hε, hεP⟩ := exists_pos_forall_isLogCanonicalPair hXv hK hω0
    (fun Γ => (hωK Γ).symm) hPinj b₀ w hQC hW hpos hCB hsumB hlcB hf hfp
  /- Lc boundaries at the real points of the hull near `t_b`. -/
  have hlcR : ∀ t ∈ rationalAffineHull tb, dist t tb < ε → ∀ (n' : ℕ) (D : DivisorOver ℂ sX)
      (a : ℝ), MMP.Intersection.IsLogDiscrepancy sX n' (Bt t) D a → 0 ≤ a := by
    intro t ht hdt n' D a ha
    refine nonneg_of_isLogDiscrepancy_of_mem_rationalAffineHull Bt W hW hBtc
      (fun q hq hqd n'' D' a' ha' => ?_) ht hdt ha
    have hlcq := (hεP _ hq hqd).2 q rfl
    exact hlcq.2.2 n'' D' a' (by rwa [hBtQ])
  /- The rational witness `Δ = Δ_{q_*}` for a rational point `q_*` close to `t_b`. -/
  obtain ⟨qs, hqsH, hqsd⟩ := exists_rat_mem_rationalAffineHull_dist_lt
    (self_mem_rationalAffineHull tb) (half_pos hε)
  have hΔlc : MMP.Intersection.IsLogCanonicalPair sX (ΔQ qs) :=
    (hεP _ hqsH (by linarith)).2 qs rfl
  /- `(X, Δ)` and `(X, B)` have the same zero places. -/
  have hzero : ∀ (D : DivisorOver ℂ sX) (a a' : ℝ) (n₁ n₂ : ℕ),
      MMP.Intersection.IsLogDiscrepancy sX n₁ (Bt tb) D a →
      MMP.Intersection.IsLogDiscrepancy sX n₂ (Bt fun j => (qs j : ℝ)) D a' →
      (a = 0 ↔ a' = 0) := by
    intro D a a' n₁ n₂ ha ha'
    obtain ⟨μ, hμ⟩ := exists_isLogDiscrepancy_affine Bt W hW hBtc D
    have key := (eq_zero_iff_of_forall_nonneg (H := rationalAffineHull tb)
      (self_mem_rationalAffineHull tb) hqsH hqsd a μ fun t ht hdt =>
        hlcR t ht hdt n₁ D _ (hμ n₁ tb a ha t))
    rw [key, MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha' (hμ n₁ tb a ha _)]
  /- The rational projective dlt modification of `(X, Δ)`. -/
  obtain ⟨V', _, _, _, pV, hpV, hV'Q, ΔV, hproj, hdlt, hcrep, hexc⟩ :=
    hP.exists_crepant_dltModification sX hX hdim hΔlc
  have hV'n : IsNormalVariety ℂ (pV ≫ sX) := hV'Q.1
  haveI : IsProper pV := isProper_of_isProjectiveMorphism pV hproj
  haveI : IsDominant pV := hpV.isDominant
  haveI : LocallyOfFiniteType (pV ≫ sX) := hV'n.1.toLocallyOfFiniteType
  haveI : CompactSpace V' := QuasiCompact.compactSpace_of_compactSpace pV
  have hdimV : topologicalKrullDim V' = n := by
    haveI := hXv.1
    haveI := hV'n.1
    rw [← hdim]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (pV ≫ sX) hpV).symm
  /- Compatible canonical divisors `K = div ω'` and `K_V = div(p^*ω')`. -/
  obtain ⟨n', K', hK', -⟩ := hdlt.1.1.2
  have hn' : n' = n := by
    have := hK'.topologicalKrullDim_eq.symm.trans hdimV
    exact_mod_cast this
  subst hn'
  obtain ⟨KV, hKV, hKVt⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hXv hV'n hpV hK hK'
  obtain ⟨ω', hω'0, hω'K, hω'KV⟩ :=
    MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hXv hV'n hpV hK hKV hKVt
  have hKω' : ∀ Γ, K.coeff Γ = Γ.ordForm ω' := fun Γ => by rw [← hω'K]; rfl
  have hKVω' : ∀ Γ, KV.coeff Γ = Γ.ordForm (pullbackRationalPluriForms sX pV ω') := fun Γ => by
    rw [← hω'KV]; rfl
  have hKV' : (divisorOfForm (pullbackRationalPluriForms sX pV ω')).IsCanonicalDivisor
      (pV ≫ sX) n' := hω'KV ▸ hKV
  /- Presentations of `K + B` and `K + Δ`, and their pull-backs to `V`. -/
  have hsumB' : ∀ Γ : Mori.PrimeDivisor X, (Γ.ordForm ω' : ℝ) + B.coeff Γ =
      ∑ i, rB i * (CB i).coeff Γ := fun Γ => by
    rw [← hKω']
    exact hKB Γ
  obtain ⟨mΔ, rΔ, CΔ, hCΔ, eΔ⟩ :=
    exists_forall_coeff_of_isCartierCombination (hcartΦ fun j => (qs j : ℝ))
  have hsumΔ : ∀ Γ : Mori.PrimeDivisor X, (Γ.ordForm ω' : ℝ) +
      (QDivisor.toRDivisor (ΔQ qs)).coeff Γ = ∑ i, rΔ i * (CΔ i).coeff Γ := fun Γ => by
    rw [← eΔ Γ, hBtQ, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, hKω']
  choose CBV hCBV using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant pV (hCB i)
  choose CΔV hCΔV using fun i =>
    MMP.Threefold.Bridges.exists_isPullback_of_isDominant pV (hCΔ i)
  set BV : RDivisor V' := ∑ i, rB i • Divisor.toRDivisor (CBV i) - Divisor.toRDivisor KV
    with hBV_def
  set BΔ : RDivisor V' := ∑ i, rΔ i • Divisor.toRDivisor (CΔV i) - Divisor.toRDivisor KV
  have hBVsum : ∀ Γ : Mori.PrimeDivisor V', (Γ.ordForm (pullbackRationalPluriForms sX pV ω') : ℝ) +
      BV.coeff Γ = ∑ i, rB i * (CBV i).coeff Γ := fun Γ => by
    rw [← hKVω']
    exact coeff_add_coeff_sum_smul_sub rB CBV KV Γ
  have hBΔsum : ∀ Γ : Mori.PrimeDivisor V', (Γ.ordForm (pullbackRationalPluriForms sX pV ω') : ℝ) +
      BΔ.coeff Γ = ∑ i, rΔ i * (CΔV i).coeff Γ := fun Γ => by
    rw [← hKVω']
    exact coeff_add_coeff_sum_smul_sub rΔ CΔV KV Γ
  /- Log discrepancies of the primes of `V` and of divisors over `V`. -/
  have hC1B : ∀ F : Mori.PrimeDivisor V', MMP.Intersection.IsLogDiscrepancy sX n' B
      (⟨V', pV, hV'n, hpV, F⟩ : DivisorOver ℂ sX) (1 - BV.coeff F) := fun F => by
    have := isLogDiscrepancy_primeDivisor_of_model hXv hω'0 hK hKω' hCB hsumB' pV hV'n hpV hCBV F
    convert this using 1
    linarith [hBVsum F]
  have hC1Δ : ∀ F : Mori.PrimeDivisor V', MMP.Intersection.IsLogDiscrepancy sX n'
      (QDivisor.toRDivisor (ΔQ qs)) (⟨V', pV, hV'n, hpV, F⟩ : DivisorOver ℂ sX)
        (1 - BΔ.coeff F) := fun F => by
    have := isLogDiscrepancy_primeDivisor_of_model hXv hω'0 hK hKω' hCΔ hsumΔ pV hV'n hpV hCΔV F
    convert this using 1
    linarith [hBΔsum F]
  have hΔV : ∀ F, (ΔV.coeff F : ℝ) = BΔ.coeff F := fun F => by
    have h1 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hcrep K hK F)
      (inferInstanceAs (IsProper pV))
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.unique h1 (hC1Δ F)
    push_cast at this
    linarith
  have hΔVeq : QDivisor.toRDivisor ΔV = BΔ :=
    DivisorWithCoeffs.ext' fun F => by rw [QDivisor.coeff_toRDivisor, hΔV]
  have hC2B := fun D hD => exists_isLogDiscrepancy_model_and_base hXv hω'0 hK hKω' hCB hsumB' pV
    hV'n hpV hCBV hKV' hBVsum D hD
  have hC2Δ := fun D hD => exists_isLogDiscrepancy_model_and_base hXv hω'0 hK hKω' hCΔ hsumΔ pV
    hV'n hpV hCΔV hKV' hBΔsum D hD
  /- The extracted primes have log discrepancy zero for `(X, B)`. -/
  have hexcB : ∀ F : Mori.PrimeDivisor V', RationalMap.IsExceptional (X := V') pV.toRationalMap F →
      BV.coeff F = 1 := by
    intro F hF
    have h0 := (hexc F hF).1
    have := (hzero _ _ 0 n' n' (by rw [hBtb]; exact hC1B F) (by rw [← hBtQ]; exact h0)).2 rfl
    linarith
  /- At a non-exceptional prime, the coefficients are those of the image prime. -/
  have hnexc : ∀ F : Mori.PrimeDivisor V',
      ¬ RationalMap.IsExceptional (X := V') pV.toRationalMap F →
      ∃ Q : Mori.PrimeDivisor X, pV F.genericPoint = Q.genericPoint ∧ BV.coeff F = B.coeff Q ∧
        (ΔV.coeff F : ℝ) = (QDivisor.toRDivisor (ΔQ qs)).coeff Q := by
    intro F hF
    obtain ⟨Q, hv⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hXv
      (⟨V', pV, hV'n, hpV, F⟩ : DivisorOver ℂ sX) hF
    have hFQ : pV F.genericPoint = Q.genericPoint :=
      MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hXv.1 hv
    refine ⟨Q, hFQ, ?_, ?_⟩
    · linarith [hBVsum F, sum_sub_ordForm_eq_coeff hXv hK hCB hsumB' pV hV'n hpV hCBV hFQ]
    · linarith [hΔV F, hBΔsum F, sum_sub_ordForm_eq_coeff hXv hK hCΔ hsumΔ pV hV'n hpV hCΔV hFQ]
  have hposqs : ∀ i, 0 < coeffVec b₀ w (fun j => (qs j : ℝ)) i :=
    (hεP _ hqsH (by linarith)).1
  /- `(V, B_V)` is lc: its log discrepancies are those of `(X, B)`. -/
  have hlogV : ∀ (n'' : ℕ) (D : DivisorOver ℂ (pV ≫ sX)) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy (pV ≫ sX) n'' BV D a → 0 ≤ a := by
    intro n'' D a ha
    obtain rfl := eq_of_isLogDiscrepancy ha hdimV
    obtain ⟨a', ha'V, ha'X⟩ := hC2B D ha.2.1
    rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha ha'V]
    exact hlog _ _ _ ha'X
  /- `B_V` and `Δ_V` have the same support. -/
  have hsupp : ∀ F, BV.coeff F ≠ 0 → ΔV.coeff F ≠ 0 := by
    intro F hF0
    by_cases hF : RationalMap.IsExceptional (X := V') pV.toRationalMap F
    · rw [(hexc F hF).2]
      norm_num
    · obtain ⟨Q, -, hBVF, hΔVF⟩ := hnexc F hF
      rw [hBVF] at hF0
      have hQ : Q ∈ B.support := Finsupp.mem_support_iff.mpr (by
        rwa [DivisorWithCoeffs.coeff_apply] at hF0)
      have : (ΔV.coeff F : ℝ) ≠ 0 := by
        rw [hΔVF, hBtQ, show Q = P ⟨Q, hQ⟩ from rfl, coeff_sum_single_self hPinj]
        exact (hposqs ⟨Q, hQ⟩).ne'
      exact_mod_cast this
  refine ⟨V', inferInstance, inferInstance, inferInstance, pV, hV'Q, hpV, BV, ?_, hproj, hexcB,
    ?_, ?_, ⟨KV, hKV, hKVt, ?_⟩, ?_⟩
  · rw [MMP.Mori.isProjectiveVariety_iff] at hX ⊢
    exact ⟨hV'n.1, hproj.comp hX.2⟩
  · intro F hF
    obtain ⟨Q, hFQ, hBVF, -⟩ := hnexc F hF
    rw [hBVF, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
      MMP.Fourfold.Oai4C1.inverseTransformDivisor_apply_of_map_genericPoint hFQ
        (MMP.Fourfold.Oai4C1.genericPoint_mem_biregularLocus pV hpV Q) B]
  · obtain ⟨-, -, Z, hZsm, hZsnc, hZpos⟩ := hdlt
    have hle1 : ∀ F, BV.coeff F ≤ 1 := fun F => by
      have := hlog _ _ _ (hC1B F)
      linarith
    have hnn : ∀ F, 0 ≤ BV.coeff F := by
      intro F
      by_cases hF : RationalMap.IsExceptional (X := V') pV.toRationalMap F
      · rw [hexcB F hF]
        norm_num
      · obtain ⟨Q, -, hBVF, -⟩ := hnexc F hF
        rw [hBVF]
        exact hBnn Q
    refine ⟨⟨hV'n, hnn, ⟨n', KV, hKV, MMP.Fourfold.IsQFactorial.isRCartier hV'Q _⟩, hlogV⟩, hle1,
      Z, hZsm, ?_, ?_⟩
    · refine hZsnc.of_support_subset ?_
      rw [MMP.Mori.inverseTransformDivisor_ι_eq_restrictOpen,
        MMP.Mori.inverseTransformDivisor_ι_eq_restrictOpen]
      intro G hG
      rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply,
        DivisorWithCoeffs.coeff_restrictOpen] at hG ⊢
      exact hsupp _ hG
    · intro n'' D hDZ a ha
      obtain rfl := eq_of_isLogDiscrepancy ha hdimV
      obtain ⟨a', ha'V, ha'X⟩ := hC2B D ha.2.1
      obtain ⟨aΔ, haΔV, haΔX⟩ := hC2Δ D ha.2.1
      rw [← hΔVeq] at haΔV
      have hposΔ := hZpos n'' D hDZ aΔ haΔV
      rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha ha'V]
      have h0 := hlog _ _ _ ha'X
      have hne : a' ≠ 0 := fun h => hposΔ.ne' ((hzero _ a' aΔ n'' n''
        (by rw [hBtb]; exact ha'X) (by rw [← hBtQ]; exact haΔX)).1 h)
      exact lt_of_le_of_ne h0 (Ne.symm hne)
  · refine ⟨m₀ + 1, rB, CB, CBV, hCB, ?_, fun i => ⟨_, hCBV i⟩, ?_⟩
    · refine DivisorWithCoeffs.ext' fun Γ => ?_
      rw [MMP.Flips.logCanonicalDivisor, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor,
        MMP.Flips.coeff_sum_smul_toRDivisor]
      exact hKB Γ
    · rw [MMP.Flips.logCanonicalDivisor, hBV_def]
      abel
  · intro F hF
    have := hC1B F
    rwa [hexcB F hF, sub_self] at this

end MMP.RealDltModificationNormalSource
