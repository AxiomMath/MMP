module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
public import MMP.AlgebraicGeometry.Positivity.AmplePlusNefSum
public import MMP.AlgebraicGeometry.Divisor.SmoothDivisorRestriction
public import MMP.AlgebraicGeometry.Positivity.NefTopIntersectionPositive
public import MMP.AlgebraicGeometry.MMP.Threefold.Basic
public import MMP.AlgebraicGeometry.Positivity.CartierTwistEulerPolynomial
public import MMP.AlgebraicGeometry.Divisor.RegularWeilCartier
public import MMP.AlgebraicGeometry.Positivity.SerreAmpleCartier
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
public import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
public import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
public import MMP.AlgebraicGeometry.MMP.Steps
public import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
public import MMP.AlgebraicGeometry.Positivity.BigNefCartier
public import MMP.AlgebraicGeometry.Intersection.CartierRestriction

@[expose] public section

section

/-!
# Divisors of high multiplicity for a smooth non-vanishing datum

Let `(X, D, G, a)` be a smooth non-vanishing datum of dimension `d ≥ 1` with `D` not numerically
trivial and `x` a closed point of `X`. Choose `e₀ ≥ 1` with `e₀ a ∈ ℤ` and `e₀ G` integral; then
`H = e₀(aD + G - K_X)` is an ample divisor, and for an integer `q ≥ a` the divisor
`N_q = e₀(qD + G - K_X) = e₀(q - a) D + H` is ample, with
`(N_q^d) ≥ d e₀ (q - a) (D · H^{d-1})` and `(D · H^{d-1}) > 0`. For `q` large,
`(N_q^d) > κ (2 d e₀)^d`, where `κ = [κ(x) : k]`.

By Serre vanishing and the very weak Riemann–Roch theorem, `h⁰(X, kN_q)` grows like
`(N_q^d) k^d / d!`, while `dim_k 𝒪_{X,x} / 𝔪_x^ℓ = κ · binom(ℓ + d - 1, d)` for the regular local
ring `𝒪_{X,x}` of dimension `d`. With `ℓ = 2 d k e₀ + 1` this is at most
`κ (2 d e₀ k + d)^d / d!`, so for some `k` there is a nonzero section `φ` of `𝒪_X(kN_q)` whose
local expression at `x` lies in `𝔪_x^ℓ`. Its divisor of zeros `M'` is effective, linearly
equivalent to `kN_q`, and its multiplicity at `x` is the order of a local equation, at least
`ℓ > 2 d e` for `e = k e₀`.

## Main results

* `MMP.Mori.IsSmoothNonvanishingDatum.exists_multiplicityAt_gt`: the divisors of high
  multiplicity exist.

## Implementation notes

The ground field is arbitrary: the residue field `κ(x)` of the closed point `x` is a finite
extension of `k`, and its degree enters the choice of `q₀`. Serre vanishing replaces the
Kawamata–Viehweg vanishing of the source, since `N_q` is ample.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.4, 3.5 Step 2
-/

open CategoryTheory AlgebraicGeometry

namespace MMP.FourfoldProofs.Km3aNonvanishingHighMultiplicityDivisorProof

open MMP.Mori MMP.Intersection

/-! ### Asymptotics -/

/-- If `κ αⁿ < I` and `f` eventually exceeds `c kⁿ` for every `c < I`, then for some `k ≥ 1`,
`κ (α k + β)ⁿ < f k`. -/
private theorem exists_lt_of_eventually_le (κ α β I : ℝ) (n : ℕ) (hlt : κ * α ^ n < I)
    (f : ℕ → ℝ) (hf : ∀ c : ℝ, c < I → ∃ k₁ : ℕ, ∀ k : ℕ, k₁ ≤ k → c * (k : ℝ) ^ n ≤ f k) :
    ∃ k : ℕ, 1 ≤ k ∧ κ * (α * k + β) ^ n < f k := by
  set c := (κ * α ^ n + I) / 2 with hc
  have hcI : c < I := by rw [hc]; linarith
  have hcκ : κ * α ^ n < c := by rw [hc]; linarith
  obtain ⟨k₁, hk₁⟩ := hf c hcI
  have ht : Filter.Tendsto (fun k : ℕ => κ * (α + β / k) ^ n) Filter.atTop
      (nhds (κ * α ^ n)) := by
    simpa using (((tendsto_const_nhds (x := α)).add
      (tendsto_const_div_atTop_nhds_zero_nat β)).pow n).const_mul κ
  obtain ⟨k₂, hk₂⟩ := Filter.eventually_atTop.1 (ht.eventually (gt_mem_nhds hcκ))
  refine ⟨max (max k₁ k₂) 1, le_max_right _ _, ?_⟩
  set k := max (max k₁ k₂) 1
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast le_max_right _ _
  have hkpos : (0 : ℝ) < k := by linarith
  calc κ * (α * k + β) ^ n = (k : ℝ) ^ n * (κ * (α + β / k) ^ n) := by
        rw [show α * k + β = k * (α + β / k) by field_simp, mul_pow]
        ring
    _ < (k : ℝ) ^ n * c :=
        mul_lt_mul_of_pos_left (hk₂ k (le_trans (le_max_right _ _) (le_max_left _ _)))
          (by positivity)
    _ = c * k ^ n := mul_comm _ _
    _ ≤ f k := hk₁ k (le_trans (le_max_left _ _) (le_max_left _ _))

/-! ### Local algebra -/

open IsLocalRing in
/-- `dim_k R ⧸ 𝔪^{ℓ+1} = dim_k R ⧸ 𝔪^ℓ + dim_k 𝔪^ℓ ⧸ 𝔪^{ℓ+1}`, as ranks. -/
private theorem rank_quotient_pow_succ {k : Type*} [Field k] {R : Type*} [CommRing R]
    [IsLocalRing R] [Algebra k R] (ℓ : ℕ) :
    Module.rank k (R ⧸ maximalIdeal R ^ (ℓ + 1)) = Module.rank k (R ⧸ maximalIdeal R ^ ℓ) +
      Module.rank k (↥(maximalIdeal R ^ ℓ) ⧸
        (maximalIdeal R • ⊤ : Submodule R ↥(maximalIdeal R ^ ℓ))) := by
  set m := maximalIdeal R
  have hJI : m ^ (ℓ + 1) ≤ m ^ ℓ := Ideal.pow_le_pow_right (Nat.le_succ ℓ)
  let π : (R ⧸ m ^ (ℓ + 1)) →ₗ[k] (R ⧸ m ^ ℓ) := (Ideal.Quotient.factorₐ k hJI).toLinearMap
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective hJI
  let ι : ↥(m ^ ℓ) →ₗ[R] R ⧸ m ^ (ℓ + 1) := (Submodule.mkQ (m ^ (ℓ + 1))) ∘ₗ (m ^ ℓ).subtype
  have hmap : Submodule.map (m ^ ℓ).subtype (m • ⊤ : Submodule R ↥(m ^ ℓ)) = m ^ (ℓ + 1) := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top, Ideal.smul_eq_mul, pow_succ']
  have hker : LinearMap.ker ι = (m • ⊤ : Submodule R ↥(m ^ ℓ)) := by
    ext ⟨y, hy⟩
    simp only [LinearMap.mem_ker, ι, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [← hmap, Submodule.mem_map]
    refine ⟨fun ⟨z, hz, hzy⟩ => ?_, fun h => ⟨_, h, rfl⟩⟩
    rwa [← (Subtype.ext hzy : z = ⟨y, hy⟩)]
  have hrange : (ι.restrictScalars k).range = LinearMap.ker π := by
    ext z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp only [LinearMap.mem_range, LinearMap.mem_ker, π, AlgHom.toLinearMap_apply,
      Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · rintro ⟨⟨y, hy⟩, hyr⟩
      have h1 : Ideal.Quotient.mk (m ^ (ℓ + 1)) y = Ideal.Quotient.mk (m ^ (ℓ + 1)) r := hyr
      rw [Ideal.Quotient.eq] at h1
      simpa using (m ^ ℓ).sub_mem hy (hJI h1)
    · intro h
      exact ⟨⟨r, h⟩, rfl⟩
  have e1 := LinearMap.rank_range_add_rank_ker π
  rw [LinearMap.range_eq_top.2 hπ, rank_top, ← hrange] at e1
  have e2 : Module.rank k ↥(ι.restrictScalars k).range =
      Module.rank k (↥(m ^ ℓ) ⧸ (m • ⊤ : Submodule R ↥(m ^ ℓ))) := by
    rw [← ((ι.restrictScalars k).quotKerEquivRange).rank_eq]
    have hk : LinearMap.ker (ι.restrictScalars k) =
        (m • ⊤ : Submodule R ↥(m ^ ℓ)).restrictScalars k := by
      rw [← hker]; rfl
    rw [hk]
    exact (Submodule.Quotient.restrictScalarsEquiv k _).rank_eq
  rw [← e1, e2]

open IsLocalRing in
/-- In a regular local `k`-algebra `R` of dimension `n ≥ 1` with residue field finite over `k`,
`R ⧸ 𝔪^ℓ` is finite-dimensional over `k`, of dimension `[R ⧸ 𝔪 : k] · binom(ℓ + n - 1, n)`. -/
private theorem finrank_quotient_pow_eq {k : Type*} [Field k] {R : Type*} [CommRing R]
    [IsRegularLocalRing R] [Algebra k R] {n : ℕ} (hn : 1 ≤ n) (hdim : ringKrullDim R = n)
    (hκ : Module.Finite k (R ⧸ maximalIdeal R)) (ℓ : ℕ) :
    Module.Finite k (R ⧸ maximalIdeal R ^ ℓ) ∧
      Module.finrank k (R ⧸ maximalIdeal R ^ ℓ) =
        Module.finrank k (R ⧸ maximalIdeal R) * (ℓ + n - 1).choose n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  set m := maximalIdeal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  induction ℓ with
  | zero =>
    have : Subsingleton (R ⧸ m ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]; infer_instance
    refine ⟨inferInstance, ?_⟩
    rw [Module.finrank_zero_of_subsingleton]
    simp
  | succ ℓ ih =>
    obtain ⟨hfin, hrk⟩ := ih
    have hg := MMP.Foundation.finrank_pow_maximalIdeal_quotient_smul_top (R := R) hn hdim ℓ
    set Q := ↥(m ^ ℓ) ⧸ (m • ⊤ : Submodule R ↥(m ^ ℓ))
    have hQpos : 0 < Module.finrank (R ⧸ m) Q := by
      rw [hg]; exact Nat.choose_pos (by omega)
    have hQfin : Module.Finite (R ⧸ m) Q := Module.finite_of_finrank_pos hQpos
    have hQk : Module.Finite k Q := Module.Finite.trans (R ⧸ m) Q
    have hQrk : Module.finrank k Q = Module.finrank k (R ⧸ m) * (ℓ + n').choose n' := by
      rw [← Module.finrank_mul_finrank k (R ⧸ m) Q, hg,
        show ℓ + (n' + 1) - 1 = ℓ + n' by omega, show n' + 1 - 1 = n' by omega]
    have hrank := rank_quotient_pow_succ (k := k) (R := R) ℓ
    rw [← Module.finrank_eq_rank k (R ⧸ m ^ ℓ), ← Module.finrank_eq_rank k Q,
      ← Nat.cast_add] at hrank
    have hfin' : Module.Finite k (R ⧸ m ^ (ℓ + 1)) :=
      Module.rank_lt_aleph0_iff.mp (by rw [hrank]; exact Cardinal.natCast_lt_aleph0)
    refine ⟨hfin', ?_⟩
    rw [← Module.finrank_eq_rank k (R ⧸ m ^ (ℓ + 1))] at hrank
    rw [Nat.cast_injective hrank, hrk, hQrk, ← mul_add]
    congr 1
    rw [show ℓ + 1 + (n' + 1) - 1 = (ℓ + n') + 1 by omega, Nat.choose_succ_succ',
      show ℓ + (n' + 1) - 1 = ℓ + n' by omega]
    ring

/-! ### Riemann–Roch and Serre vanishing for an ample Cartier divisor -/

section RiemannRoch

open MMP.CartierDivisor Opposite

variable {k : Type} [Field k] {X : Scheme.{0}}

private theorem scalarsToGlobalSections_eq (sX : X ⟶ Spec (.of k)) :
    scalarsToGlobalSections k sX =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ ⊤ (by simp)).hom := by
  have : sX.appLE ⊤ ⊤ (by simp) = sX.appTop := by
    simp [Scheme.Hom.appLE]
    exact Category.comp_id _
  rw [this]; rfl

/-- `h⁰(D)` is the dimension of `H⁰(X, 𝒪_X(D))`. -/
private theorem cartierH0_eq_finrank (sX : X ⟶ Spec (.of k)) (D : X.CartierDivisor) :
    cartierH0 k sX D = Module.finrank k (cohomologyOverField k sX (sheaf D) 0) := by
  rw [(cohomologyOverFieldZeroLinearIso k sX (sheaf D)).toLinearEquiv.finrank_eq, cartierH0,
    scalarsToGlobalSections_eq]
  rfl

open Stacks.RelativeVeryAmple (tensorModules tensorModulesMapIso) in
/-- `𝒪_X(qA + rD) ≅ 𝒪_X(rD) ⊗ 𝒪_X(A)^{⊗ q}`. -/
private theorem nonempty_sheaf_iso_tensorModules (A D : X.CartierDivisor) (q : ℕ) (r : ℤ) :
    Nonempty (sheaf ((q : ℤ) • A + r • D) ≅
      tensorModules X (MMP.CartierDivisor.sheaf (r • D)) (Stacks.Ample.tensorPowModule X
          (MMP.CartierDivisor.sheaf A) q)) := by
  obtain ⟨e₁⟩ := MMP.Resolution.Bridges.lineBundle_nsmul_iso_tensorPow A q
  obtain ⟨e₂⟩ :=
    MMP.Resolution.Bridges.nonempty_tensorPow_iso_tensorPowModule X (MMP.CartierDivisor.sheaf A) q
  have e₃ : tensorModules X (MMP.CartierDivisor.sheaf (r • D)) (Stacks.Ample.tensorPowModule X
      (MMP.CartierDivisor.sheaf A) q) ≅
      tensorModules X (MMP.CartierDivisor.sheaf (r • D)) (MMP.CartierDivisor.sheaf (q • A)) :=
    tensorModulesMapIso X (Iso.refl _) (e₁ ≪≫ e₂).symm
  have e₄ : MonoidalCategory.tensorObj (MMP.CartierDivisor.sheaf (r • D))
      (MMP.CartierDivisor.sheaf (q • A)) ≅
      sheaf ((q : ℤ) • A + r • D) :=
    MMP.CartierDivisorSheaf.sheafMulIso (r • D) (q • A) ≪≫ eqToIso (by rw [add_comm, natCast_zsmul])
  exact ⟨(e₃ ≪≫ e₄).symm⟩

/-- Serre vanishing: for `q ≫ 0`, `h⁰(qA + rD) = χ(qA + rD)`. -/
private theorem eventually_cartierH0_eq_eulerChar {sX : X ⟶ Spec (.of k)} [IsProper sX]
    {A : X.CartierDivisor} (hA : Stacks.Ample.IsAmple X (sheaf A)) (D : X.CartierDivisor)
    (r : ℤ) : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      (cartierH0 k sX ((q : ℤ) • A + r • D) : ℤ) =
        MMP.Threefold.Mori.eulerCharCartierCombination k sX ![A, D] ![(q : ℤ), r] := by
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k sX
    (MMP.CartierDivisor.sheaf (r • D)) 1
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist sX
      (MMP.CartierDivisor.sheaf (r • D)) _ hA
  refine ⟨d₀, fun q hq => ?_⟩
  obtain ⟨e⟩ := nonempty_sheaf_iso_tensorModules A D q r
  have hvan : ∀ j, 0 < j → Module.finrank k
      (cohomologyOverField k sX (sheaf ((q : ℤ) • A + r • D)) j) = 0 := by
    intro j hj
    have hz := (hd₀ q j hq hj).of_iso ((Hfunctor X.ringCatSheaf ⊤ j).mapIso e)
    haveI : Subsingleton (Hgroup X.ringCatSheaf ⊤ j (sheaf ((q : ℤ) • A + r • D))) :=
      AddCommGrpCat.subsingleton_of_isZero hz
    haveI : Subsingleton (cohomologyOverField k sX (sheaf ((q : ℤ) • A + r • D)) j) :=
      (cohomologyOverFieldAddEquivHgroup k sX _ j).subsingleton_congr.2 inferInstance
    exact Module.finrank_zero_of_subsingleton
  have hsum : ∑ i, ![(q : ℤ), r] i • ![A, D] i = (q : ℤ) • A + r • D := by
    simp [Fin.sum_univ_two]
  rw [MMP.Threefold.Mori.eulerCharCartierCombination, hsum,
    finsum_eq_single _ 0 (fun j hj => by rw [hvan j (Nat.pos_of_ne_zero hj)]; simp),
    cartierH0_eq_finrank]
  simp

open Filter Topology in
/-- A polynomial `P(q, r)` of total degree `≤ n`, divided by `qⁿ`, tends to its `qⁿ`-coefficient as
`q → ∞`, for each fixed `r`. -/
private theorem tendsto_eval_div_pow (P : MvPolynomial (Fin 2) ℚ) {n : ℕ}
    (hP : P.totalDegree ≤ n) (r : ℚ) :
    Tendsto (fun q : ℕ => ((MvPolynomial.eval ![(q : ℚ), r] P : ℚ) : ℝ) / (q : ℝ) ^ n) atTop
      (𝓝 ((P.coeff (Finsupp.single (0 : Fin 2) n) : ℚ) : ℝ)) := by
  classical
  have key : ∀ d ∈ P.support, Tendsto (fun q : ℕ =>
      ((P.coeff d * ((q : ℚ) ^ d 0 * r ^ d 1) : ℚ) : ℝ) / (q : ℝ) ^ n) atTop
        (𝓝 (if d = Finsupp.single 0 n then ((P.coeff d : ℚ) : ℝ) else 0)) := by
    intro d hd
    have hdeg : d 0 + d 1 ≤ n := by
      have h1 := MvPolynomial.le_totalDegree hd
      have h2 : d.sum (fun _ e => e) = d 0 + d 1 := by
        rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
      omega
    by_cases h : d 0 = n
    · have h1 : d 1 = 0 := by omega
      have hd' : d = Finsupp.single 0 n := by
        ext i; fin_cases i <;> simp [h, h1]
      rw [if_pos hd']
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with q hq
      have hq' : (q : ℝ) ≠ 0 := by positivity
      push_cast; rw [h, h1]; field_simp
    · have hne : d ≠ Finsupp.single 0 n := by rintro rfl; simp at h
      rw [if_neg hne]
      have ht : Tendsto (fun q : ℕ => ((q : ℝ) ^ (n - d 0))⁻¹) atTop (𝓝 0) :=
        ((tendsto_pow_atTop (by omega)).comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
      have ht' := ht.const_mul (((P.coeff d : ℚ) : ℝ) * (r : ℝ) ^ d 1)
      rw [mul_zero] at ht'
      refine ht'.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with q hq
      have hq' : (q : ℝ) ≠ 0 := by positivity
      have hpow : (q : ℝ) ^ n = (q : ℝ) ^ d 0 * (q : ℝ) ^ (n - d 0) := by
        rw [← pow_add]; congr 1; omega
      push_cast; rw [hpow]; field_simp
  have hsum := tendsto_finset_sum _ key
  have hlim : (∑ d ∈ P.support, if d = Finsupp.single 0 n then ((P.coeff d : ℚ) : ℝ) else 0) =
      ((P.coeff (Finsupp.single (0 : Fin 2) n) : ℚ) : ℝ) := by
    rw [Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · simp [MvPolynomial.notMem_support_iff.1 hmem]
  rw [hlim] at hsum
  refine hsum.congr' (Eventually.of_forall fun q => ?_)
  simp only
  rw [MvPolynomial.eval_eq', Rat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [Fin.prod_univ_two]

/-- The value at `(1, 0)` of the degree-`n` part of `P` is the coefficient of `X₀ⁿ`. -/
private theorem eval_homogeneousComponent_one_zero (P : MvPolynomial (Fin 2) ℚ) (n : ℕ) :
    MvPolynomial.eval (fun i => ((![1, 0] : Fin 2 → ℤ) i : ℚ))
      (MvPolynomial.homogeneousComponent n P) = P.coeff (Finsupp.single 0 n) := by
  classical
  rw [MvPolynomial.homogeneousComponent_apply, map_sum]
  rw [Finset.sum_eq_single (Finsupp.single 0 n)]
  · rw [MvPolynomial.eval_monomial, Finsupp.prod_single_index (by simp)]
    simp
  · intro d hd hne
    rw [Finset.mem_filter] at hd
    have hd1 : d 1 ≠ 0 := by
      intro h1
      apply hne
      have h2 : d.degree = d 0 + d 1 := by simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]
      ext i; fin_cases i <;> simp <;> omega
    rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    simp [zero_pow hd1]
  · intro h
    rw [Finset.mem_filter, not_and_or] at h
    rcases h with h | h
    · simp [MvPolynomial.notMem_support_iff.1 h]
    · simp at h

/-- **Riemann–Roch growth of `h⁰`.** For an ample Cartier divisor `A` on a proper integral
`k`-scheme of dimension `n` and any `c < (Aⁿ)`, eventually `c qⁿ ≤ n! h⁰(qA)`. -/
private theorem exists_le_factorial_mul_cartierH0 [IsIntegral X] {sX : X ⟶ Spec (.of k)}
    [IsProper sX] {n : ℕ} (hn : topologicalKrullDim X = n)
    {A : X.CartierDivisor} (hA : Stacks.Ample.IsAmple X (sheaf A)) {c : ℝ}
    (hc : c < (MMP.Mori.sheafSelfIntersectionNumber k sX (𝟙 X) n hn.le (sheaf A) : ℝ)) :
    ∃ q₁ : ℕ, ∀ q : ℕ, q₁ ≤ q →
      c * (q : ℝ) ^ n ≤ n.factorial * (cartierH0 k sX ((q : ℤ) • A) : ℝ) := by
  obtain ⟨P, hPdeg, hP⟩ :=
    MMP.Resolution.Bridges.exists_polynomial_eulerChar_cartierSheaf_sum k sX n hn ![A, A]
  have hP' : ∀ m : Fin 2 → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) P =
      MMP.Threefold.Mori.eulerCharCartierCombination k sX ![A, A] m := fun m => by
    rw [hP m, MMP.Threefold.Mori.eulerCharCartierCombination]
    have h2 := (Int.castAddHom ℚ).map_finsum_of_injective Int.cast_injective
      (fun j : ℕ => (-1 : ℤ) ^ j * (Module.finrank k (cohomologyOverField k sX
        (sheaf (∑ i, m i • ![A, A] i)) j) : ℤ))
    simpa using h2.symm
  have hlead := MMP.Threefold.Mori.eval_homogeneousComponent_of_eulerChar k sX hn ![A, A] P hP'
    ![1, 0]
  have hsumA : ∑ i, (![1, 0] : Fin 2 → ℤ) i • ![A, A] i = A := by simp [Fin.sum_univ_two]
  rw [eval_homogeneousComponent_one_zero, hsumA] at hlead
  set c₀ : ℚ := P.coeff (Finsupp.single 0 n) with hc₀
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hcc₀ : c / n.factorial < (c₀ : ℝ) := by
    rw [hlead]; push_cast
    exact div_lt_div_of_pos_right hc hfac
  have ht := tendsto_eval_div_pow P hPdeg (0 : ℚ)
  obtain ⟨q₁, hq₁⟩ := Filter.eventually_atTop.1
    ((ht.eventually (lt_mem_nhds hcc₀)).and (Filter.eventually_ge_atTop 1))
  obtain ⟨q₀, hq₀⟩ := eventually_cartierH0_eq_eulerChar (k := k) (sX := sX) hA A 0
  refine ⟨max q₁ q₀, fun q hq => ?_⟩
  obtain ⟨h1, h2⟩ := hq₁ q (le_trans (le_max_left _ _) hq)
  have hh0 := hq₀ q (le_trans (le_max_right _ _) hq)
  have hqpos : (0 : ℝ) < (q : ℝ) ^ n := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast h2
    positivity
  have h3 := (lt_div_iff₀ hqpos).1 h1
  have h4 : MvPolynomial.eval ![(q : ℚ), (0 : ℚ)] P =
      MMP.Threefold.Mori.eulerCharCartierCombination k sX ![A, A] ![(q : ℤ), 0] := by
    rw [← hP']; congr 2; funext i; fin_cases i <;> simp
  rw [h4] at h3
  rw [zero_smul, add_zero] at hh0
  have h5 : (MMP.Threefold.Mori.eulerCharCartierCombination k sX ![A, A] ![(q : ℤ), 0] : ℝ) =
      (cartierH0 k sX ((q : ℤ) • A) : ℝ) := by
    rw [← hh0]; norm_cast
  push_cast at h3
  rw [h5] at h3
  have h6 : c * (q : ℝ) ^ n = n.factorial * (c / n.factorial * (q : ℝ) ^ n) := by
    field_simp
  rw [h6]
  exact mul_le_mul_of_nonneg_left h3.le hfac.le

open IsLocalRing in
/-- **Sections against the local count.** Let `A` be an ample Cartier divisor on a proper integral
`k`-scheme of dimension `n ≥ 1`, and `R` a regular local `k`-algebra of dimension `n` whose residue
field has degree `κ` over `k`. If `κ αⁿ < (Aⁿ)`, then for some `m ≥ 1`,
`dim_k R ⧸ 𝔪^{αm + 1} < h⁰(mA)`. -/
private theorem exists_finrank_quotient_pow_lt_cartierH0 [IsIntegral X] {sX : X ⟶ Spec (.of k)}
    [IsProper sX] {n : ℕ} (hn1 : 1 ≤ n) (hn : topologicalKrullDim X = n)
    {A : X.CartierDivisor} (hA : Stacks.Ample.IsAmple X (sheaf A))
    {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra k R] (hdim : ringKrullDim R = n)
    (hκ : Module.Finite k (R ⧸ maximalIdeal R)) (α : ℕ)
    (hI : ((Module.finrank k (R ⧸ maximalIdeal R) * α ^ n : ℕ) : ℤ) <
      MMP.Mori.sheafSelfIntersectionNumber k sX (𝟙 X) n hn.le (sheaf A)) :
    ∃ m : ℕ, 1 ≤ m ∧ Module.Finite k (R ⧸ maximalIdeal R ^ (α * m + 1)) ∧
      Module.finrank k (R ⧸ maximalIdeal R ^ (α * m + 1)) < cartierH0 k sX (m • A) := by
  set κ := Module.finrank k (R ⧸ maximalIdeal R)
  obtain ⟨m, hm, hlt⟩ := exists_lt_of_eventually_le (κ : ℝ) α n _ n
    (by exact_mod_cast hI) (fun m => n.factorial * (cartierH0 k sX ((m : ℤ) • A) : ℝ))
    (fun c hc => exists_le_factorial_mul_cartierH0 hn hA hc)
  obtain ⟨hfin, hrk⟩ := finrank_quotient_pow_eq (k := k) hn1 hdim hκ (α * m + 1)
  refine ⟨m, hm, hfin, ?_⟩
  have hch : ((α * m + n).choose n : ℝ) * n.factorial ≤ ((α * m + n : ℕ) : ℝ) ^ n :=
    (le_div_iff₀ (by positivity)).1 (Nat.choose_le_pow_div _ _)
  rw [natCast_zsmul] at hlt
  rw [hrk, show α * m + 1 + n - 1 = α * m + n by omega, ← Nat.cast_lt (α := ℝ)]
  push_cast at hch hlt ⊢
  have := mul_le_mul_of_nonneg_left hch (Nat.cast_nonneg (α := ℝ) κ)
  nlinarith [Nat.factorial_pos n]

end RiemannRoch

/-! ### Weil divisors and Cartier divisors on a smooth scheme -/

section WeilCartier

open MMP.CartierDivisor Opposite

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

/-- On a smooth `k`-scheme every Weil divisor is the Weil divisor of a Cartier divisor. -/
private theorem exists_isWeilDivisorOfCartier_of_isSmoothScheme {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] (hsm : IsSmoothScheme sX) (w : Divisor X) :
    ∃ A : X.CartierDivisor, IsWeilDivisorOfCartier A w := by
  haveI := MMP.Resolution.Aux.smooth_of_isSmoothScheme' sX hsm
  have hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) := fun x =>
    haveI := isRegularLocalRing_stalk_of_smooth_over_field sX x
    IsRegularLocalRing.uniqueFactorizationMonoid _
  exact MMP.Resolution.Bridges.exists_isOrderAlong_of_weilDivisor hX
    (⟨w, (AlgebraicGeometry.mem_weilDivisor_iff _).mpr fun x =>
      ⟨Set.univ, Filter.univ_mem, w.support.finite_toSet.subset fun Z hZ => by
        by_cases h : w Z = 0
        · simp [h] at hZ
        · simpa using h⟩⟩ : AlgebraicGeometry.WeilDivisor X)

private theorem isWeilDivisorOfCartier_add {A B : X.CartierDivisor} {v w : Divisor X}
    (hA : IsWeilDivisorOfCartier A v) (hB : IsWeilDivisorOfCartier B w) :
    IsWeilDivisorOfCartier (A + B) (v + w) := fun P => (hA P).add (hB P)

private theorem isWeilDivisorOfCartier_nsmul {A : X.CartierDivisor} {v : Divisor X}
    (hA : IsWeilDivisorOfCartier A v) {t : ℕ} (ht : 1 ≤ t) :
    IsWeilDivisorOfCartier (t • A) (t • v) := by
  induction t, ht using Nat.le_induction with
  | base => simpa using hA
  | succ t _ ih => simpa [succ_nsmul] using isWeilDivisorOfCartier_add ih hA

variable [IsNormal X] [CompactSpace X]

/-- A Cartier lift of a Weil divisor is ample iff the Weil divisor is. -/
private theorem isAmple_sheaf_iff_of_isWeilDivisorOfCartier {A : X.CartierDivisor}
    {w : Divisor X} (hA : IsWeilDivisorOfCartier A w) (hw : w.IsCartier) :
    Stacks.Ample.IsAmple X (sheaf A) ↔ w.IsAmple hw := by
  obtain ⟨e⟩ := hA.nonempty_sheaf_iso_divisorialSheaf
  haveI := hw.isInvertibleModule_divisorialSheaf
  exact Stacks.RelativeVeryAmple.isAmple_congr _ _ e

variable {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]

/-- A nef Weil divisor has a nef Cartier lift. -/
private theorem isNef_sheaf_of_isWeilDivisorOfCartier {A : X.CartierDivisor} {w : Divisor X}
    (hA : IsWeilDivisorOfCartier A w) (hnef : w.IsNef k sX) :
    MMP.Mori.IsNef k sX (sheaf A) := by
  obtain ⟨hw, h⟩ := hnef
  obtain ⟨e⟩ := hA.nonempty_sheaf_iso_divisorialSheaf
  haveI := hw.isInvertibleModule_divisorialSheaf
  intro C i _ _ _ hC
  rw [degreeOn_eq_of_iso k sX i hC.le e]
  exact h C i hC

/-- A Cartier lift of a Weil divisor whose sheaf is not numerically trivial is not numerically
trivial. -/
private theorem not_isNumericallyTrivial_sheaf_of_isWeilDivisorOfCartier {A : X.CartierDivisor}
    {w : Divisor X} (hA : IsWeilDivisorOfCartier A w) (hw : w.IsCartier)
    (hnt : haveI := hw.isInvertibleModule_divisorialSheaf
      ¬ MMP.Mori.IsNumericallyTrivial k sX w.divisorialSheaf) :
    ¬ MMP.Mori.IsNumericallyTrivial k sX (sheaf A) := by
  obtain ⟨e⟩ := hA.nonempty_sheaf_iso_divisorialSheaf
  haveI := hw.isInvertibleModule_divisorialSheaf
  intro h
  refine hnt fun C i _ _ _ hC => ?_
  rw [← degreeOn_eq_of_iso k sX i hC.le e]
  exact h C i hC

end WeilCartier

/-! ### Ample multiples and sections -/

section AmpleSections

open MMP.CartierDivisor Opposite

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X]

/-- If `m E = m' D` with `m, m' > 0` and `D` ample, then `E` is ample, on a scheme where every
Weil divisor is the Weil divisor of a Cartier divisor. -/
private theorem isAmple_of_nsmul_eq_nsmul
    (hlift : ∀ w : Divisor X, ∃ A : X.CartierDivisor, IsWeilDivisorOfCartier A w)
    {E D : Divisor X} (hE : E.IsCartier) (hD : D.IsCartier) (hamp : D.IsAmple hD) {m m' : ℕ}
    (hm : 0 < m) (hm' : 0 < m') (h : m • E = m' • D) : E.IsAmple hE := by
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨Ec, hEc⟩ := hlift E
  obtain ⟨Dc, hDc⟩ := hlift D
  have h3 := (MMP.Resolution.Bridges.isAmple_lineBundle_iff_nsmul Dc m' hm').1
    ((isAmple_sheaf_iff_of_isWeilDivisorOfCartier hDc hD).2 hamp)
  obtain ⟨e1⟩ := (isWeilDivisorOfCartier_nsmul hDc hm').nonempty_sheaf_iso_divisorialSheaf
  obtain ⟨e2⟩ := (isWeilDivisorOfCartier_nsmul hEc hm).nonempty_sheaf_iso_divisorialSheaf
  rw [← h] at e1
  exact (isAmple_sheaf_iff_of_isWeilDivisorOfCartier hEc hE).1
    ((MMP.Resolution.Bridges.isAmple_lineBundle_iff_nsmul Ec m hm).2
      ((Stacks.RelativeVeryAmple.isAmple_congr _ _ (e1 ≪≫ e2.symm)).1 h3))

private theorem finrank_compHom_eq {R : Type} [CommRing R] (φ : k →+* R) {M N : Type}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g : M ≃ₗ[R] N) :
    (letI := Module.compHom M φ; Module.finrank k M) =
      (letI := Module.compHom N φ; Module.finrank k N) := by
  letI := Module.compHom M φ
  letI := Module.compHom N φ
  let g' : M ≃ₗ[k] N :=
    { g.toEquiv with map_add' := g.map_add, map_smul' := fun c x => g.map_smul (φ c) x }
  exact g'.finrank_eq

/-- `h⁰` of a Weil divisor is `h⁰` of a Cartier lift. -/
private theorem finrank_divisorialSubmodule_eq_cartierH0 (sX : X ⟶ Spec (.of k))
    {A : X.CartierDivisor} {w : Divisor X} (hA : IsWeilDivisorOfCartier A w) :
    (letI := Module.compHom (w.divisorialSubmodule ⊤) (scalarsToGlobalSections k sX);
      Module.finrank k (w.divisorialSubmodule ⊤)) = cartierH0 k sX A := by
  obtain ⟨e⟩ := hA.nonempty_sheaf_iso_divisorialSheaf
  exact (finrank_compHom_eq _
    ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso e).toLinearEquiv).symm

end AmpleSections

/-! ### Orders in a regular local ring -/

section Order

open IsLocalRing

/-- A nonzero element of `𝔪^ℓ` has order at least `ℓ`. -/
private theorem le_maximalIdealOrder {S : Type*} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] {φ : S} (hφ : φ ≠ 0) {ℓ : ℕ} (h : φ ∈ maximalIdeal S ^ ℓ) :
    ℓ ≤ MMP.Flips.maximalIdealOrder S φ := by
  by_contra hlt
  exact (MMP.Flips.maximalIdealOrder_spec hφ).2 (Ideal.pow_le_pow_right (not_le.mp hlt) h)

/-- A unit has order zero. -/
private theorem maximalIdealOrder_of_isUnit {S : Type*} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] {u : S} (hu : IsUnit u) : MMP.Flips.maximalIdealOrder S u = 0 := by
  by_contra hne
  have h := (MMP.Flips.maximalIdealOrder_spec hu.ne_zero).1
  exact (mem_maximalIdeal _).1 (Ideal.pow_le_self hne h) hu

/-- The order of `∏ fᵢ^{aᵢ}` in a regular local ring is `∑ aᵢ ord(fᵢ)`. -/
private theorem maximalIdealOrder_prod_pow {S : Type*} [CommRing S] [IsRegularLocalRing S]
    {ι : Type*} (s : Finset ι) (f : ι → S) (a : ι → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) :
    MMP.Flips.maximalIdealOrder S (∏ i ∈ s, f i ^ a i) =
      ∑ i ∈ s, a i * MMP.Flips.maximalIdealOrder S (f i) := by
  classical
  haveI := IsRegularLocalRing.isDomain S
  have hpow : ∀ g : S, g ≠ 0 → ∀ n : ℕ,
      MMP.Flips.maximalIdealOrder S (g ^ n) = n * MMP.Flips.maximalIdealOrder S g := by
    intro g hg n
    induction n with
    | zero => simpa using maximalIdealOrder_of_isUnit (S := S) isUnit_one
    | succ n ih =>
      rw [pow_succ, MMP.Flips.maximalIdealOrder_mul (pow_ne_zero _ hg) hg, ih]; ring
  induction s using Finset.induction_on with
  | empty => simpa using maximalIdealOrder_of_isUnit (S := S) isUnit_one
  | insert i s hi ih =>
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hfs : ∀ j ∈ s, f j ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      MMP.Flips.maximalIdealOrder_mul (pow_ne_zero _ hfi)
        (Finset.prod_ne_zero_iff.2 fun j hj => pow_ne_zero _ (hfs j hj)),
      hpow _ hfi, ih hfs]

/-- Associated elements of a regular local ring have the same order. -/
private theorem maximalIdealOrder_eq_of_associated {S : Type*} [CommRing S]
    [IsRegularLocalRing S] {a b : S} (ha : a ≠ 0) (h : Associated a b) :
    MMP.Flips.maximalIdealOrder S a = MMP.Flips.maximalIdealOrder S b := by
  obtain ⟨u, rfl⟩ := h
  rw [MMP.Flips.maximalIdealOrder_mul ha u.isUnit.ne_zero, maximalIdealOrder_of_isUnit u.isUnit,
    add_zero]

end Order

/-! ### Local equations of effective divisors on a smooth variety -/

section LocalEquation

open Opposite

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X]

/-- Near any point `q`, a prime divisor `P` of a smooth variety has a local equation which is a
regular function `f` on an open `W ∋ q`, whose germ at `q` generates the ideal of `P`. -/
private theorem exists_localEquation_single (sX : X ⟶ Spec (.of k)) [IsSmoothVariety k sX]
    (P : MMP.Mori.PrimeDivisor X) (q : X) :
    ∃ (W : X.Opens) (hq : q ∈ W) (f : Γ(X, W)) (φ : (RationalFunctions X)ˣ),
      Divisor.IsLocalEquation (Finsupp.single P 1 : Divisor X) W φ ∧
      (∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ W),
        (φ : RationalFunctions X) Z = (X.presheaf.germ W _ hZ).hom f) ∧
      IdealSheafData.stalk P.idealSheaf q = Ideal.span {(X.presheaf.germ W q hq).hom f} := by
  have hd := Divisor.cartier_weil_dictionary_of_isSmoothVariety k sX
  obtain ⟨U, hqU, g, φ, hφ, hloc, hideal⟩ := hd.2.1 P q
  refine ⟨U, hqU, g, φ, hloc, hφ, ?_⟩
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ P.idealSheaf q U hqU, hideal,
    Ideal.map_span, Set.image_singleton]

private theorem ord_prod {s : Finset (MMP.Mori.PrimeDivisor X)} (E : MMP.Mori.PrimeDivisor X)
    (φ : MMP.Mori.PrimeDivisor X → (RationalFunctions X)ˣ) :
    E.ord (∏ P ∈ s, φ P) = ∑ P ∈ s, E.ord (φ P) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, PrimeDivisor.ord_mul, ih]

/-- Near any point `q`, an effective divisor `D` on a smooth variety has a local equation `φ`
which is a regular function `f` on an open `W ∋ q`, whose germ at `q` generates
`I_{D,q} = ∏_E I_{E,q}^{d_E}`. -/
private theorem exists_localEquation_span_eq_localIdeal (sX : X ⟶ Spec (.of k))
    [IsSmoothVariety k sX] (D : Divisor X) (hD : 0 ≤ D) (q : X) :
    ∃ (W : X.Opens) (hq : q ∈ W) (f : Γ(X, W)) (φ : (RationalFunctions X)ˣ),
      D.IsLocalEquation W φ ∧
      (∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ W),
        (φ : RationalFunctions X) Z = (X.presheaf.germ W _ hZ).hom f) ∧
      Ideal.span {(X.presheaf.germ W q hq).hom f} = localIdeal q D := by
  classical
  choose W' hq' f' φ' hloc' hφ' hst' using fun P => exists_localEquation_single sX P q
  set V : X.Opens := D.support.inf W' with hV
  have hqV : q ∈ V := by
    rw [← SetLike.mem_coe, hV, TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf]
    simp only [Function.comp_apply, Set.iInf_eq_iInter, Set.mem_iInter, SetLike.mem_coe]
    exact fun P _ => hq' P
  have hle : ∀ P ∈ D.support, V ≤ W' P := fun P hP => Finset.inf_le (f := W') hP
  let n : MMP.Mori.PrimeDivisor X → ℕ := fun P => (D P).toNat
  let g : D.support → Γ(X, V) := fun P => X.presheaf.map (homOfLE (hle P.1 P.2)).op (f' P.1)
  have hgerm : ∀ (P : D.support) (y : X) (hy : y ∈ V),
      (X.presheaf.germ V y hy).hom (g P) =
        (X.presheaf.germ (W' P.1) y (hle P.1 P.2 hy)).hom (f' P.1) :=
    fun P y hy => X.presheaf.germ_res_apply _ _ _ _
  refine ⟨V, hqV, ∏ P ∈ D.support.attach, g P ^ n P, ∏ P ∈ D.support, φ' P ^ n P,
    ?_, ?_, ?_⟩
  · rintro E ⟨y, hyE, hyV⟩
    rw [ord_prod]
    simp only [PrimeDivisor.ord_pow]
    have hE : ∀ P ∈ D.support, E.ord (φ' P) = if P = E then 1 else 0 := by
      intro P hP
      rw [← hloc' P E ⟨y, hyE, hle P hP hyV⟩]
      by_cases h : P = E
      · subst h; simp [DivisorWithCoeffs.coeff_single_self]
      · rw [if_neg h, DivisorWithCoeffs.coeff_single_of_ne h]
    rw [Finset.sum_congr rfl fun P hP => by rw [hE P hP]]
    simp only [nsmul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
    rw [DivisorWithCoeffs.coeff_apply]
    split_ifs with h
    · exact (Int.toNat_of_nonneg (hD E)).symm
    · exact Finsupp.notMem_support_iff.1 h
  · intro Z hZ
    rw [Units.coe_prod, Finset.prod_apply, map_prod, ← Finset.prod_attach]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [Units.val_pow_eq_pow_val, Pi.pow_apply, map_pow, hgerm, hφ']
  · rw [map_prod, ← Ideal.prod_span_singleton, localIdeal,
      ← Finset.prod_attach D.support (fun E => IdealSheafData.stalk E.idealSheaf q ^ (D E).toNat)]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [map_pow, ← Ideal.span_singleton_pow, hgerm, hst']

end LocalEquation

/-! ### Sections vanishing to high order at a point -/

section Sections

open IsLocalRing Opposite

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X]

/-- The local expression `ψ σ` at `x` of a global section `σ` of `𝒪_X(N)`, for a local equation
`ψ` of `N` on a neighbourhood of `x`, is the image of an element of `𝒪_{X,x}`. -/
private theorem exists_stalk_eq_mul (N : Divisor X) {U : X.Opens} {x : X} (hxU : x ∈ U)
    {ψ : (RationalFunctions X)ˣ} (hψ : N.IsLocalEquation U ψ) {Z : irreducibleComponents X}
    (hxZ : x ∈ Z.1) (σ : N.divisorialSubmodule ⊤) :
    ∃ r : X.presheaf.stalk x, (stalkToRationalFunctions X hxZ).hom r =
      (ψ : RationalFunctions X) Z * σ.1 ⟨Z, trivial⟩ := by
  let φU : ToType ((rationalFunctionsPresheaf X).obj (op U)) :=
    fun Z' => (ψ : RationalFunctions X) Z'.1 * σ.1 ⟨Z'.1, trivial⟩
  have h0 : (0 : Divisor X).IsDivisorialSection U φU := by
    intro E hE
    have hψE : E.OrdGE (E.ord ψ) ((ψ : RationalFunctions X) E.component) :=
      Or.inr (E.valuation_component ψ).ge
    have hσE := σ.2 E (by obtain ⟨y, hy, -⟩ := hE; exact ⟨y, hy, trivial⟩)
    refine (hψE.mul hσE).mono (le_of_eq ?_)
    rw [DivisorWithCoeffs.coeff_zero, hψ E hE]; ring
  exact h0.exists_stalk_eq hxU hxZ

/-- The evaluation in the function field of a rational function whose `Z`-component comes from
`𝒪_{X,x}` is the image of that element. -/
private theorem evalFF_eq_algebraMap {x : X} {Z : irreducibleComponents X} (hxZ : x ∈ Z.1)
    (w : RationalFunctions X) (t : X.presheaf.stalk x)
    (h : w Z = (stalkToRationalFunctions X hxZ).hom t) :
    MMP.Threefold.Mori.Helpers.evalFF Z w = algebraMap (X.presheaf.stalk x) X.functionField t := by
  change (X.presheaf.stalkSpecializes _).hom (w Z) = _
  rw [h, stalkToRationalFunctions]
  change (X.presheaf.stalkSpecializes _ ≫ X.presheaf.stalkSpecializes _).hom t =
    (X.presheaf.stalkSpecializes _).hom t
  rw [TopCat.Presheaf.stalkSpecializes_comp]

/-- On an integral scheme every prime divisor lies on the unique irreducible component. -/
private theorem component_eq (E : MMP.Mori.PrimeDivisor X) (Z : irreducibleComponents X) :
    E.component = Z := by
  have h := irreducibleComponents_eq_singleton (X := X)
  have h1 : (E.component : Set X) ∈ ({Set.univ} : Set (Set X)) := h ▸ E.component.2
  have h2 : (Z : Set X) ∈ ({Set.univ} : Set (Set X)) := h ▸ Z.2
  exact Subtype.ext ((Set.mem_singleton_iff.1 h1).trans (Set.mem_singleton_iff.1 h2).symm)

/-- If `h⁰(X, N) > dim_k 𝒪_{X,x} / 𝔪_x^ℓ`, some nonzero global section of `𝒪_X(N)` has local
expression at `x` a nonzero element of `𝔪_x^ℓ`. -/
private theorem exists_ne_zero_localExpression_mem_pow (sX : X ⟶ Spec (.of k)) {x : X}
    (N : Divisor X) {U : X.Opens} (hxU : x ∈ U) {ψ : (RationalFunctions X)ˣ}
    (hψ : N.IsLocalEquation U ψ) {Z : irreducibleComponents X} (hxZ : x ∈ Z.1) (ℓ : ℕ)
    (hfin : letI := stalkAlgebra sX x
      FiniteDimensional k (X.presheaf.stalk x ⧸ maximalIdeal (X.presheaf.stalk x) ^ ℓ))
    (hlt : letI := stalkAlgebra sX x
      letI := Module.compHom (N.divisorialSubmodule ⊤) (scalarsToGlobalSections k sX)
      Module.finrank k (X.presheaf.stalk x ⧸ maximalIdeal (X.presheaf.stalk x) ^ ℓ) <
        Module.finrank k (N.divisorialSubmodule ⊤)) :
    ∃ (σ : N.divisorialSubmodule ⊤) (hσ0 : σ ≠ 0) (s : X.presheaf.stalk x),
      (stalkToRationalFunctions X hxZ).hom s = (ψ : RationalFunctions X) Z * σ.1 ⟨Z, trivial⟩ ∧
      s ≠ 0 ∧ s ∈ maximalIdeal (X.presheaf.stalk x) ^ ℓ := by
  letI := stalkAlgebra sX x
  letI := Module.compHom (N.divisorialSubmodule ⊤) (scalarsToGlobalSections k sX)
  have hj : Function.Injective (stalkToRationalFunctions X hxZ).hom :=
    stalkToRationalFunctions_injective hxZ
  choose r hr using exists_stalk_eq_mul N hxU hψ hxZ
  have hgerm : ∀ g : Γ(X, ⊤), (stalkToRationalFunctions X hxZ).hom
      ((X.presheaf.germ ⊤ x trivial).hom g) =
        (X.presheaf.germ ⊤ (componentGenericPoint X Z) trivial).hom g :=
    fun g => TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf
      (show x ∈ (⊤ : X.Opens) from trivial) _ g
  let T : N.divisorialSubmodule ⊤ →ₗ[k] X.presheaf.stalk x ⧸ maximalIdeal _ ^ ℓ :=
    { toFun := fun σ => Ideal.Quotient.mk _ (r σ)
      map_add' := fun σ τ => by
        rw [← map_add]
        congr 1
        apply hj
        rw [map_add, hr, hr, hr]
        exact mul_add _ _ _
      map_smul' := fun c σ => by
        change _ = Ideal.Quotient.mk _ (c • r σ)
        congr 1
        apply hj
        rw [Algebra.smul_def, map_mul, hr, hr]
        change (ψ : RationalFunctions X) Z *
            ((scalarsToGlobalSections k sX c) • σ.1) ⟨Z, trivial⟩ =
          (stalkToRationalFunctions X hxZ).hom
            ((X.presheaf.germ ⊤ x trivial).hom (scalarsToGlobalSections k sX c)) *
            ((ψ : RationalFunctions X) Z * σ.1 ⟨Z, trivial⟩)
        rw [rationalFunctions_smul_apply, hgerm]
        exact mul_left_comm _ _ _ }
  have hker : LinearMap.ker T ≠ ⊥ := by
    intro hbot
    have := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.1 hbot)
    omega
  obtain ⟨σ, hσmem, hσ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨σ, hσ0, r σ, hr σ, fun h0 => ?_, Ideal.Quotient.eq_zero_iff_mem.1 hσmem⟩
  have h1 := hr σ
  rw [h0, map_zero] at h1
  have hψu : IsUnit ((ψ : RationalFunctions X) Z) := (Pi.isUnit_iff.mp ψ.isUnit) Z
  have hφu : IsUnit (σ.1 ⟨Z, trivial⟩) :=
    (Pi.isUnit_iff.mp (Divisor.isUnit_sectionToRationalFunctions hσ0).unit.isUnit) Z
  exact (hψu.mul hφu).ne_zero h1.symm

/-- On a smooth variety, if a nonzero `s ∈ 𝔪_x^ℓ` is a unit multiple of a local generator of the
ideal of an effective divisor `M'` at `x`, then `mult_x M' ≥ ℓ`. -/
private theorem le_multiplicityAt_of_isUnit_mul_mem_pow (sX : X ⟶ Spec (.of k))
    [IsSmoothVariety k sX] (hsm : IsSmoothScheme sX) {x : X} {M' : Divisor X} (heff : 0 ≤ M')
    {W : X.Opens} (hxW : x ∈ W) {f : Γ(X, W)}
    (hspan : Ideal.span {(X.presheaf.germ W x hxW).hom f} = localIdeal x M')
    {a s : X.presheaf.stalk x} (ha : IsUnit a) (haf : a * (X.presheaf.germ W x hxW).hom f = s)
    (hs0 : s ≠ 0) {ℓ : ℕ} (hs : s ∈ maximalIdeal (X.presheaf.stalk x) ^ ℓ) :
    (ℓ : ℤ) ≤ M'.multiplicityAt x := by
  haveI := MMP.Resolution.Aux.smooth_of_isSmoothScheme' sX hsm
  haveI : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth_over_field sX x
  haveI := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  have hf0 : (X.presheaf.germ W x hxW).hom f ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at haf
    exact hs0 haf.symm
  have hpi : ∀ E : MMP.Mori.PrimeDivisor X, MMP.Mori.SurfaceAux.piOf sX hsm x E ≠ 0 := by
    intro E
    by_cases h : x ∈ E.support
    · exact (MMP.Mori.SurfaceAux.prime_piOf h).ne_zero
    · rw [MMP.Mori.SurfaceAux.piOf_of_notMem h]
      exact one_ne_zero
  have hass := Ideal.span_singleton_eq_span_singleton.1 (hspan.trans
    (MMP.Mori.SurfaceAux.localIdeal_eq_span (sY := sX) (hsm := hsm) (q := x) M'))
  have hmult := MMP.Mori.SurfaceAux.divisor_multiplicityAt_eq (sY := sX) (hsm := hsm) (q := x)
    (fun E => MMP.Flips.maximalIdealOrder _ (MMP.Mori.SurfaceAux.piOf sX hsm x E))
    (fun E => MMP.Flips.maximalIdealOrder_spec (hpi E)) M'
    (DivisorWithCoeffs.isEffective_iff_nonneg.2 heff)
  rw [hmult]
  have hℓ := le_maximalIdealOrder hs0 hs
  rw [← haf, MMP.Flips.maximalIdealOrder_mul ha.ne_zero hf0, maximalIdealOrder_of_isUnit ha,
    zero_add, maximalIdealOrder_eq_of_associated hf0 hass,
    maximalIdealOrder_prod_pow _ _ _ fun E _ => hpi E] at hℓ
  exact_mod_cast hℓ

/-- **A section vanishing to high order.** On a smooth variety `X`, let `N` be a Cartier divisor
and `x ∈ X` a point. If `h⁰(X, N) > dim_k 𝒪_{X,x} / 𝔪_x^ℓ`, then some effective `M' ∼ N` has
`mult_x M' ≥ ℓ`. -/
private theorem exists_le_multiplicityAt_of_finrank_lt (sX : X ⟶ Spec (.of k))
    [IsSmoothVariety k sX] (hsm : IsSmoothScheme sX) {x : X} (N : Divisor X) (hN : N.IsCartier)
    (ℓ : ℕ)
    (hfin : letI := stalkAlgebra sX x
      FiniteDimensional k (X.presheaf.stalk x ⧸ maximalIdeal (X.presheaf.stalk x) ^ ℓ))
    (hlt : letI := stalkAlgebra sX x
      letI := Module.compHom (N.divisorialSubmodule ⊤) (scalarsToGlobalSections k sX)
      Module.finrank k (X.presheaf.stalk x ⧸ maximalIdeal (X.presheaf.stalk x) ^ ℓ) <
        Module.finrank k (N.divisorialSubmodule ⊤)) :
    ∃ M' : Divisor X, M'.IsEffective ∧ M'.LinearlyEquivalent N ∧
      (ℓ : ℤ) ≤ M'.multiplicityAt x := by
  obtain ⟨U, hxU, ψ, hψ⟩ := hN x
  obtain ⟨Z, hxZ⟩ := exists_mem_irreducibleComponents x
  obtain ⟨σ, hσ0, s, hs, hs0, hsℓ⟩ :=
    exists_ne_zero_localExpression_mem_pow sX N hxU hψ hxZ ℓ hfin hlt
  have heff : 0 ≤ N.zeroDivisor σ hσ0 := Divisor.zeroDivisor_nonneg N σ hσ0
  refine ⟨N.zeroDivisor σ hσ0, DivisorWithCoeffs.isEffective_iff_nonneg.2 heff,
    ⟨(Divisor.isUnit_sectionToRationalFunctions hσ0).unit, by
      rw [Divisor.zeroDivisor_eq, add_sub_cancel_right]⟩, ?_⟩
  set M' := N.zeroDivisor σ hσ0 with hM'
  set φ := (Divisor.isUnit_sectionToRationalFunctions hσ0).unit
  have hM'U : M'.IsLocalEquation U (ψ * φ) := by
    intro E hE
    rw [hM', Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
      hψ E hE, PrimeDivisor.ord_mul]
    ring
  obtain ⟨W, hxW, f, φ', hloc, hφ', hspan⟩ :=
    exists_localEquation_span_eq_localIdeal sX M' heff x
  have hu : ∀ E : MMP.Mori.PrimeDivisor X, x ∈ E.support → E.ord (ψ * φ * φ'⁻¹) = 0 := by
    intro E hxE
    rw [PrimeDivisor.ord_mul, PrimeDivisor.ord_inv, ← hM'U E ⟨x, hxE, hxU⟩,
      ← hloc E ⟨x, hxE, hxW⟩]
    ring
  set ev := MMP.Threefold.Mori.Helpers.evalFF Z
  have hne : ev ((ψ * φ * φ'⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) ≠ 0 :=
    ((ψ * φ * φ'⁻¹).isUnit.map ev).ne_zero
  obtain ⟨a, ha, hau⟩ := MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero x hne
    fun E hxE => by
      have := MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord E (ψ * φ * φ'⁻¹)
      rw [component_eq E Z] at this
      rw [← this]
      exact hu E hxE
  have hr' : algebraMap (X.presheaf.stalk x) X.functionField s =
      ev ((ψ * φ : (RationalFunctions X)ˣ) : RationalFunctions X) :=
    (evalFF_eq_algebraMap hxZ _ _ (by rw [hs]; rfl)).symm
  have hf' : algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.germ W x hxW).hom f) =
      ev (φ' : RationalFunctions X) := by
    refine (evalFF_eq_algebraMap hxZ _ _ ?_).symm
    rw [hφ' Z ((genericPoint_mem_iff Z W).mpr ⟨x, hxW, hxZ⟩), stalkToRationalFunctions,
      TopCat.Presheaf.germ_stalkSpecializes_apply]
  have haf : a * (X.presheaf.germ W x hxW).hom f = s := by
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [map_mul, hau, hf', hr', ← map_mul]
    congr 1
    simp
  exact le_multiplicityAt_of_isUnit_mul_mem_pow sX hsm heff hxW hspan ha haf hs0 hsℓ

end Sections

/-! ### Integral multiples -/

section Integral

variable {X : Scheme.{0}}

private theorem exists_int_eq_mul_of_den_dvd {r : ℚ} {L : ℕ} (h : r.den ∣ L) :
    ∃ z : ℤ, (L : ℚ) * r = z := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨c * r.num, ?_⟩
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

/-- Some positive integer `e₀` makes `e₀ a` an integer and `e₀ G` an integral divisor. -/
private theorem exists_nat_mul_isIntegral (G : QDivisor X) (a : ℚ) :
    ∃ e₀ : ℕ, 0 < e₀ ∧ ∃ z : ℤ, (e₀ : ℚ) * a = z ∧
      ∃ G₀ : MMP.Mori.Divisor X, Divisor.toQDivisor G₀ = (e₀ : ℚ) • G := by
  classical
  set L : ℕ := a.den * ∏ P ∈ G.support, (G P).den
  have hLpos : 0 < L := Nat.mul_pos a.den_pos (Finset.prod_pos fun P _ => (G P).den_pos)
  obtain ⟨z, hz⟩ := exists_int_eq_mul_of_den_dvd (r := a) (L := L) (Dvd.intro _ rfl)
  refine ⟨L, hLpos, z, hz, ?_⟩
  have hmem : (L : ℚ) • G ∈ Set.range (Divisor.toQDivisor (X := X)) := by
    rw [QDivisor.mem_range_toQDivisor_iff]
    intro E
    rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    by_cases hE : E ∈ G.support
    · exact exists_int_eq_mul_of_den_dvd
        (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun P => (G P).den) hE) _)
    · rw [DivisorWithCoeffs.coeff_apply, Finsupp.notMem_support_iff.1 hE, mul_zero]
      exact ⟨0, by simp⟩
  exact hmem

/-- If `e₀ a = z` with `e₀ ≥ 1` and `⌈a⌉ + B + 1 ≤ q`, then `e₀ q - z` is a natural number
`t ≥ B + 1`. -/
private theorem exists_natCast_eq_mul_sub_of_ceil_add_le {e₀ : ℕ} (he₀ : 0 < e₀) {a : ℚ}
    {z : ℤ} (hz : (e₀ : ℚ) * a = z) {B : ℕ} {q : ℤ} (hq : ⌈a⌉ + B + 1 ≤ q) :
    ∃ t : ℕ, (t : ℤ) = e₀ * q - z ∧ B + 1 ≤ t := by
  have hqa : (B : ℚ) + 1 ≤ q - a := by
    have h1 : ((⌈a⌉ + B + 1 : ℤ) : ℚ) ≤ q := by exact_mod_cast hq
    have h2 := Int.le_ceil a
    push_cast at h1
    linarith
  have he : (1 : ℚ) ≤ e₀ := by exact_mod_cast he₀
  have h : (((B : ℤ) + 1 : ℤ) : ℚ) ≤ ((e₀ * q - z : ℤ) : ℚ) := by
    push_cast
    rw [← hz]
    nlinarith
  have h' : (B : ℤ) + 1 ≤ e₀ * q - z := Int.cast_le.1 h
  exact ⟨(e₀ * q - z).toNat, Int.toNat_of_nonneg (by omega), by omega⟩

end Integral

/-! ### The divisors of high multiplicity -/

/-- If `D` is nef and `H` is ample, then `t D + H` is ample, on a scheme where every Weil divisor
is the Weil divisor of a Cartier divisor. -/
private theorem isAmple_nsmul_add {k : Type} [Field k] {X : Scheme.{0}}
    [AlgebraicGeometry.IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX] [QuasiCompact sX]
    (hlift : ∀ w : MMP.Mori.Divisor X, ∃ A : X.CartierDivisor, IsWeilDivisorOfCartier A w)
    (hcart : ∀ w : MMP.Mori.Divisor X, w.IsCartier)
    (hqcart : ∀ w : MMP.Mori.QDivisor X, w.IsQCartier) {D H : MMP.Mori.Divisor X}
    (hD : (Divisor.toQDivisor D).IsNef k sX) (hH : H.IsAmple (hcart H)) (t : ℕ) :
    (t • D + H).IsAmple (hcart _) := by
  have hHq : (Divisor.toQDivisor H).IsAmple := ⟨1, one_pos, H, by simp, hcart H, hH⟩
  have hNq : Divisor.toQDivisor (t • D + H) =
      Divisor.toQDivisor H + ∑ _i ∈ Finset.range t, Divisor.toQDivisor D := by
    rw [map_add, map_nsmul, Finset.sum_const, Finset.card_range, add_comm]
  obtain ⟨m, hm, N₁, hN₁, hN₁c, hN₁a⟩ :=
    QDivisor.isAmple_of_numericallyEquivalent_add_sum_of_isNef sX (Finset.range t)
      (B := Divisor.toQDivisor (t • D + H)) (fun _ => Divisor.toQDivisor D) hHq (fun _ _ => hD)
      (by rw [hNq]; exact QDivisor.NumericallyEquivalent.refl (hqcart _))
  refine isAmple_of_nsmul_eq_nsmul hlift (hcart _) hN₁c hN₁a hm one_pos ?_
  apply Divisor.toQDivisor_injective
  rw [map_nsmul, one_nsmul, hN₁, Nat.cast_smul_eq_nsmul]

open MMP.CartierDivisor in
private theorem exists_multiplicityAt_gt_of_isSmoothNonvanishingDatum {k : Type} [Field k]
    {X : Scheme.{0}} [AlgebraicGeometry.IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ}
    {K D : MMP.Mori.Divisor X} {G : MMP.Mori.QDivisor X} {a : ℚ}
    (h : MMP.Mori.IsSmoothNonvanishingDatum sX n K D G a) (hd : 1 ≤ n)
    (hD : ¬ (MMP.Mori.Divisor.toQDivisor D).IsNumericallyTrivial k sX)
    {x : X} (hx : IsClosed ({x} : Set X)) (_hxG : x ∉ (G.supp : Set X)) :
    ∃ q₀ : ℤ, a ≤ q₀ ∧ ∀ q : ℤ, q₀ ≤ q →
      ∃ (e : ℤ) (G' M' : MMP.Mori.Divisor X), 1 ≤ e ∧ MMP.Mori.Divisor.toQDivisor G' = e • G ∧
        M'.IsEffective ∧ M'.LinearlyEquivalent ((e * q) • D + G' - e • K) ∧
        2 * n * e < M'.multiplicityAt x := by
  -- the standing structure of `X`
  haveI hproj : AlgebraicGeometry.IsProjectiveVariety k sX := h.isProjectiveVariety
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hproj.isProjective
  have hsm : IsSmoothScheme sX := h.isSmoothScheme
  haveI : Smooth sX := MMP.Resolution.Aux.smooth_of_isSmoothScheme' sX hsm
  haveI : IsSmoothVariety k sX := ⟨⟩
  haveI : IsNoetherian X := ⟨⟩
  have hdim : topologicalKrullDim X = n := h.isKltPair.1.2.1.topologicalKrullDim_eq
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hdict := Divisor.cartier_weil_dictionary_of_isSmoothVariety k sX
  have hcart : ∀ w : MMP.Mori.Divisor X, w.IsCartier := hdict.1
  have hqcart : ∀ w : MMP.Mori.QDivisor X, w.IsQCartier := hdict.2.2.2.2.2
  have hlift : ∀ w : MMP.Mori.Divisor X, ∃ A : X.CartierDivisor, IsWeilDivisorOfCartier A w :=
    exists_isWeilDivisorOfCartier_of_isSmoothScheme hsm
  -- the local ring at `x`
  letI := stalkAlgebra sX x
  haveI : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth_over_field sX x
  have hdimx : ringKrullDim (X.presheaf.stalk x) = (n' + 1 : ℕ) := by
    rw [← topologicalKrullDimAt_eq_krullDimOfRing_stalk k X sX x hx,
      ← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X sX x, hdim]
  have hκ : Module.Finite k (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :=
    finite_residueField_over_field_of_isClosed k sX x hx
  set κ : ℕ := Module.finrank k (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
  -- `e₀` and `H = e₀ (aD + G - K)`
  obtain ⟨e₀, he₀, z, hz, G₀, hG₀⟩ := exists_nat_mul_isIntegral G a
  set A : MMP.Mori.QDivisor X :=
    a • Divisor.toQDivisor D + G - Divisor.toQDivisor K with hA
  set H : MMP.Mori.Divisor X := z • D + G₀ - (e₀ : ℤ) • K with hH
  have hHq : Divisor.toQDivisor H = (e₀ : ℚ) • A := by
    rw [hH, map_sub, map_add, map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ,
      ← Int.cast_smul_eq_zsmul ℚ, hG₀, hA, smul_sub, smul_add, smul_smul, hz]
    push_cast; rfl
  have hHamp : H.IsAmple (hcart H) := by
    obtain ⟨m, hm, H₁, hH₁, hH₁c, hH₁a⟩ := h.isAmple
    refine isAmple_of_nsmul_eq_nsmul hlift (hcart H) hH₁c hH₁a hm he₀ ?_
    apply Divisor.toQDivisor_injective
    rw [map_nsmul, map_nsmul, hHq, hH₁, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_smul, smul_smul, mul_comm]
  have hDnef : (Divisor.toQDivisor D).IsNef k sX :=
    (QDivisor.isNef_toQDivisor_iff D (hcart D)).2 h.isNef
  -- Cartier lifts of `D` and `H`
  obtain ⟨Dc, hDc⟩ := hlift D
  obtain ⟨Hc, hHc⟩ := hlift H
  have hDcnef : MMP.Mori.IsNef k sX (sheaf Dc) := isNef_sheaf_of_isWeilDivisorOfCartier hDc h.isNef
  have hDcnt : ¬ MMP.Mori.IsNumericallyTrivial k sX (sheaf Dc) :=
    not_isNumericallyTrivial_sheaf_of_isWeilDivisorOfCartier hDc (hcart D)
      (Divisor.not_isNumericallyTrivial_divisorialSheaf (hcart D) hD)
  have hHcamp : Stacks.Ample.IsAmple X (sheaf Hc) :=
    (isAmple_sheaf_iff_of_isWeilDivisorOfCartier hHc (hcart H)).2 hHamp
  have hc₀ : 0 < intersectionNumber k sX (𝟙 X) (n' + 1) hdim.le
      (fun j => sheaf ((Fin.cons Dc fun _ => Hc : Fin (n' + 1) → X.CartierDivisor) j)) := by
    convert MMP.Mori.intersectionNumber_cons_pos_of_isNef_of_isAmple k sX n' hdim
      (sheaf Dc) (sheaf Hc) hDcnef hDcnt hHcamp using 2
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  set c₀ := intersectionNumber k sX (𝟙 X) (n' + 1) hdim.le
    (fun j => sheaf ((Fin.cons Dc fun _ => Hc : Fin (n' + 1) → X.CartierDivisor) j))
  -- the threshold
  set B : ℕ := κ * (2 * (n' + 1) * e₀) ^ (n' + 1)
  refine ⟨⌈a⌉ + B + 1, ?_, fun q hq => ?_⟩
  · have := Int.le_ceil a
    push_cast
    linarith [(Nat.cast_nonneg B : (0 : ℚ) ≤ B)]
  -- `t = e₀ (q - a)` and `N = e₀ (qD + G - K) = tD + H`
  obtain ⟨t, ht, htB⟩ := exists_natCast_eq_mul_sub_of_ceil_add_le he₀ hz hq
  have ht1 : 1 ≤ t := by omega
  set N : MMP.Mori.Divisor X := t • D + H with hN
  have hNamp : N.IsAmple (hcart N) := isAmple_nsmul_add sX hlift hcart hqcart hDnef hHamp t
  set τ : X.CartierDivisor := t • Dc + Hc
  have hτN : IsWeilDivisorOfCartier τ N :=
    isWeilDivisorOfCartier_add (isWeilDivisorOfCartier_nsmul hDc ht1) hHc
  have hτamp : Stacks.Ample.IsAmple X (sheaf τ) :=
    (isAmple_sheaf_iff_of_isWeilDivisorOfCartier hτN (hcart N)).2 hNamp
  -- the top self-intersection of `τ`
  have hgrow := MMP.Mori.mul_intersectionNumber_cons_le_intersectionNumber_smul_add k sX hdim
    Dc Hc hDcnef hHcamp t
  set I : ℤ := MMP.Mori.sheafSelfIntersectionNumber k sX (𝟙 X) (n' + 1) hdim.le (sheaf τ)
  have hIeq : I = intersectionNumber k sX (𝟙 X) (n' + 1) hdim.le fun _ => sheaf τ :=
    MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber k sX (𝟙 X) (n' + 1) hdim.le _
  have hIB : (B : ℤ) < I := by
    have h1 : (1 : ℤ) ≤ c₀ := hc₀
    have h4 : (B : ℤ) + 1 ≤ t := by exact_mod_cast htB
    calc (B : ℤ) < (n' + 1 : ℕ) * t * c₀ := by
          push_cast; nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℤ) ≤ n' * t)]
      _ ≤ I := hIeq ▸ hgrow
  -- Riemann–Roch against the local count
  obtain ⟨k₁, hk₁, hfinℓ, hcount⟩ := exists_finrank_quotient_pow_lt_cartierH0 (by omega) hdim
    hτamp hdimx hκ (2 * (n' + 1) * e₀) hIB
  set ℓ : ℕ := 2 * (n' + 1) * e₀ * k₁ + 1 with hℓ
  -- the section and its divisor of zeros
  have hkτ := isWeilDivisorOfCartier_nsmul hτN hk₁
  rw [← finrank_divisorialSubmodule_eq_cartierH0 sX hkτ] at hcount
  obtain ⟨M', hM'eff, hM'lin, hM'mult⟩ := exists_le_multiplicityAt_of_finrank_lt sX hsm
    (k₁ • N) (hcart _) ℓ hfinℓ hcount
  refine ⟨k₁ * e₀, k₁ • G₀, M', ?_, ?_, hM'eff, ?_, ?_⟩
  · have : (1 : ℤ) ≤ k₁ := by exact_mod_cast hk₁
    have : (1 : ℤ) ≤ e₀ := by exact_mod_cast he₀
    nlinarith
  · rw [map_nsmul, hG₀, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, ← Int.cast_smul_eq_zsmul ℚ]
    push_cast; rfl
  · refine hM'lin.trans ?_
    have e1 : k₁ • N = ((k₁ * e₀ : ℤ) * q) • D + k₁ • G₀ - ((k₁ * e₀ : ℕ) : ℤ) • K := by
      rw [hN, hH, ← natCast_zsmul D t, ht, ← natCast_zsmul _ k₁, ← natCast_zsmul G₀ k₁]
      module
    rw [e1]
    push_cast
    exact Divisor.LinearlyEquivalent.refl _
  · have : (2 * (n' + 1 : ℕ) * (k₁ * e₀ : ℕ) : ℤ) < ℓ := by rw [hℓ]; push_cast; ring_nf; omega
    push_cast at this ⊢
    linarith

end MMP.FourfoldProofs.Km3aNonvanishingHighMultiplicityDivisorProof

end

section

/-!
# Divisors of high multiplicity for a smooth non-vanishing datum

Let `(X, D, G, a)` be a smooth non-vanishing datum of dimension `d ≥ 1` with `D` not numerically
trivial, and let `x ∈ X \ Supp G` be a closed point. Since `aD + G - K_X` is ample and `D` is nef
and not numerically trivial, the top self-intersection of `e₀(qD + G - K_X)` grows linearly in
`q`. For `q` large, a Riemann–Roch count then beats the dimension of `𝒪_{X,x} / 𝔪_x^ℓ`, and a
nonzero section of a multiple of `qD + G - K_X` vanishes to high order at `x`. Hence there is
`q₀ ≥ a` such that for every integer `q ≥ q₀` there are an integer `e ≥ 1` with `eG` integral and
an effective divisor `M' ∼ e(qD + G - K_X)` with `mult_x M' > 2de`.

## Main results

* `MMP.Mori.IsSmoothNonvanishingDatum.exists_multiplicityAt_gt`: the divisors `M'` of high
  multiplicity exist.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.4, 3.5 Step 2
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

open MMP.FourfoldProofs.Km3aNonvanishingHighMultiplicityDivisorProof in
/-- **Divisors of high multiplicity** (Kollár–Mori 3.5, Step 2). Let `(X, D, G, a)` be a smooth
non-vanishing datum of dimension `d ≥ 1` with `D` not numerically trivial, and let `x ∉ Supp G`
be a closed point. Then there is an integer `q₀ ≥ a` such that for every integer `q ≥ q₀` there
are an integer `e ≥ 1` with `eG` integral and an effective divisor `M' ∼ e(qD + G - K_X)` with
`mult_x M' > 2de`. -/
@[mmp "lem_km3a_nonvanishing_high_multiplicity_divisor"]
public theorem IsSmoothNonvanishingDatum.exists_multiplicityAt_gt
    {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    {n : ℕ} {K D : Divisor X} {G : QDivisor X} {a : ℚ}
    (h : IsSmoothNonvanishingDatum sX n K D G a) (hd : 1 ≤ n)
    (hD : ¬ (Divisor.toQDivisor D).IsNumericallyTrivial k sX)
    {x : X} (hx : IsClosed ({x} : Set X)) (hxG : x ∉ (G.supp : Set X)) :
    ∃ q₀ : ℤ, a ≤ q₀ ∧ ∀ q : ℤ, q₀ ≤ q →
      ∃ (e : ℤ) (G' M' : Divisor X), 1 ≤ e ∧ Divisor.toQDivisor G' = e • G ∧
        M'.IsEffective ∧ M'.LinearlyEquivalent ((e * q) • D + G' - e • K) ∧
        2 * n * e < M'.multiplicityAt x :=
  exists_multiplicityAt_gt_of_isSmoothNonvanishingDatum h hd hD hx hxG

end MMP.Mori

end
