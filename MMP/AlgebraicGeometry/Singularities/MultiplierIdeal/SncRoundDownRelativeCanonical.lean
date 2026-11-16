module
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Jacobian
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Composite
public import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors

/-!
# The round-down of the pull-back of an SNC divisor with coefficients below one

Let `X` be a non-singular variety over a field `k`, `D = ∑ᵢ aᵢ Dᵢ` an `ℝ`-divisor on `X` with
simple normal crossing support and every `aᵢ < 1`, and `μ : X' → X` a proper birational morphism
from a non-singular variety. Then `⌊μ^*D⌋ ≤ K_{X'/X}`: for every prime divisor `E ⊆ X'`,
`ord_E ⌊μ^*D⌋ ≤ ord_E K_{X'/X}`.

Writing `mᵢ = ord_E(μ^*Dᵢ) ≥ 0`, one has `ord_E K_{X'/X} ≥ ∑_{mᵢ > 0} mᵢ - 1` when some `mᵢ > 0`
(a local computation of the Jacobian in coordinates adapted to the SNC divisor), while
`ord_E(μ^*D) = ∑ᵢ aᵢ mᵢ < ∑_{mᵢ > 0} mᵢ`.

## Main results

* `MMP.Intersection.IsRelativeCanonicalDivisor.roundDown_le_of_hasSNCSupport`

## Implementation notes

* As in `MMP.Foundations.Intersection.Singularities.Resolution`, a non-singular variety over `k`
  is `MMP.Mori.IsVariety` together with `MMP.Mori.IsSmoothScheme`, `X'` being a `k`-scheme
  through `μ ≫ s_X`. `K_{X'/X}` is a Cartier divisor `K` with
  `MMP.Intersection.IsRelativeCanonicalDivisor`, read through its Weil divisor `wK`
  (`MMP.Intersection.IsWeilDivisorOfCartier`); `μ^*D` is read through the Weil `ℝ`-divisor `F`
  of a pull-back (`MMP.Intersection.IsWeilPullback`), and the SNC hypothesis and the bound on
  the coefficients through the Weil `ℝ`-divisor `wD` of `D`.
* The base field `k` is assumed perfect, generalizing the source's `ℂ`: over an imperfect field
  the description of `K_{X'/X}` by the Jacobian of `μ` fails (on the affine line over
  `𝔽_p(t)`, `d(T^p - t) = 0`).
* Only `aᵢ < 1` is assumed: the source also assumes `aᵢ ≥ 0`, which the argument does not use,
  since `aᵢ mᵢ < mᵢ` for `mᵢ > 0` whatever the sign of `aᵢ`.

## References

* R. Lazarsfeld, *Positivity in algebraic geometry*, II, proof of Lemma 9.2.19, (9.10)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry UniqueFactorizationMonoid

namespace MMP.Intersection

open MMP.Mori (Divisor RDivisor)

/-- The floor estimate: if `a_P < 1` for every `P` and `c ≠ 0` has natural coefficients, then
`⌊∑ a_P c_P⌋ ≤ ∑ c_P - 1`. -/
private theorem floor_sum_mul_le {ι : Type*} (a : ι → ℝ) (ha : ∀ i, a i < 1) (c : ι →₀ ℕ)
    (hc : c ≠ 0) : ⌊c.sum (fun i m => a i * m)⌋ ≤ (c.sum fun _ m => (m : ℤ)) - 1 := by
  refine Int.le_sub_one_iff.mpr (Int.floor_lt.mpr ?_)
  have hlt : c.sum (fun i m => a i * m) < c.sum (fun _ m => (m : ℝ)) := by
    unfold Finsupp.sum
    apply Finset.sum_lt_sum_of_nonempty (Finsupp.support_nonempty_iff.mpr hc)
    intro i hi
    have : (0 : ℝ) < c i := by exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    nlinarith [ha i]
  exact hlt.trans_eq (by simp [Finsupp.sum])

/-- An order function on a factorial domain, additive on the divisors of `r` and zero on units,
is the sum of its values on the normalized prime factors of `r`. -/
private theorem eq_sum_normalizedFactors {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [NormalizationMonoid R] {r : R} (hr : r ≠ 0) (g : R → ℕ)
    (hmul : ∀ x y, x * y ∣ r → g (x * y) = g x + g y) (hunit : ∀ u, IsUnit u → g u = 0) :
    g r = ((normalizedFactors r).map g).sum := by
  have aux : ∀ s : Multiset R, s.prod ∣ r → g s.prod = (s.map g).sum := by
    intro s
    induction s using Multiset.induction_on with
    | empty => exact fun _ => by simpa using hunit 1 isUnit_one
    | cons a s ih =>
      intro h
      rw [Multiset.prod_cons] at h
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, hmul a _ h,
        ih (dvd_of_mul_left_dvd h)]
  obtain ⟨u, hu⟩ := prod_normalizedFactors hr
  have hd : (normalizedFactors r).prod * (u : R) ∣ r := ⟨1, by rw [mul_one, hu]⟩
  rw [show g r = g ((normalizedFactors r).prod * (u : R)) from congrArg g hu.symm,
    hmul _ _ hd, hunit _ u.isUnit, add_zero, aux _ (dvd_of_mul_right_dvd hd)]

/-- A sum over the normalized prime factors of `r`, grouped by multiplicity. -/
private theorem sum_map_normalizedFactors_eq_sum_count {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [NormalizationMonoid R] [DecidableEq R] (r : R) (g : R → ℕ)
    {P : Finset R} (hP : (normalizedFactors r).toFinset ⊆ P) :
    ((normalizedFactors r).map g).sum = ∑ p ∈ P, (normalizedFactors r).count p * g p := by
  rw [Finset.sum_multiset_map_count]
  refine Finset.sum_subset hP fun p _ hp => ?_
  rw [Multiset.count_eq_zero.mpr (fun h => hp (Multiset.mem_toFinset.mpr h)), zero_smul]

/-- The multiplicity of `p` in a multiset, as a sum of indicators. -/
private theorem sum_map_ite_eq_count {R : Type*} [DecidableEq R] (s : Multiset R) (p : R) :
    (s.map fun q => if q = p then 1 else 0).sum = s.count p := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.count_cons]
    by_cases h : a = p
    · simp [h, add_comm]
    · simp [h, Ne.symm h]

/-- `d(z^e b) = z^{e-1} (e b dz + z db)` for `e ≥ 1`. -/
private theorem D_pow_mul_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (z b : S)
    {e : ℕ} (he : 1 ≤ e) :
    KaehlerDifferential.D R S (z ^ e * b) =
      z ^ (e - 1) • (((e : S) * b) • KaehlerDifferential.D R S z +
        z • KaehlerDifferential.D R S b) := by
  obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  rw [Derivation.leibniz, Derivation.leibniz_pow, Nat.add_sub_cancel, pow_succ]
  simp only [smul_add, smul_smul, nsmul_eq_mul]
  push_cast
  module

/-- If `uᵢ = sᵢ t + z βᵢ` for `i ∈ I`, then `⋀ᵢ uᵢ ∈ z^{|I|-1} ⋀ⁿ M`: in the expansion, a term
with two factors `sᵢ t, sⱼ t` vanishes, and every other term has at least `|I| - 1` factors in
`z M`. -/
private theorem exists_ιMulti_eq_pow_smul_aux {S M : Type*} [CommRing S] [AddCommGroup M]
    [Module S M] {n : ℕ} (u : Fin n → M) (z : S) (t : M) (I : Finset (Fin n))
    (s : Fin n → S) (β : Fin n → M) (hu : ∀ i ∈ I, u i = s i • t + z • β i) :
    ∃ ω, exteriorPower.ιMulti S n u = z ^ (I.card - 1) • ω := by
  classical
  set f := (exteriorPower.ιMulti S n (M := M))
  let α : Fin n → M := fun i => if i ∈ I then s i • t else 0
  let γ : Fin n → M := fun i => if i ∈ I then z • β i else u i
  have hsplit : u = α + γ := by
    funext i
    by_cases hi : i ∈ I
    · simp [α, γ, hi, hu i hi]
    · simp [α, γ, hi]
  have key : ∀ T : Finset (Fin n), ∃ ω, f (T.piecewise α γ) = z ^ (I.card - 1) • ω := by
    intro T
    by_cases hTI : T ⊆ I
    · by_cases hT : ∃ i ∈ T, ∃ j ∈ T, i ≠ j
      · obtain ⟨i, hi, j, hj, hij⟩ := hT
        refine ⟨0, ?_⟩
        rw [smul_zero]
        set v := T.piecewise α γ
        have hvi : v i = s i • t := by simp [v, hi, α, hTI hi]
        have hvj : v j = s j • t := by simp [v, hj, α, hTI hj]
        have e1 : f v = s i • f (Function.update v i t) := by
          conv_lhs => rw [← Function.update_eq_self i v, hvi]
          exact f.map_update_smul v i (s i) t
        have hwj : Function.update v i t j = s j • t := by
          rw [Function.update_of_ne hij.symm, hvj]
        have e2 : f (Function.update v i t) =
            s j • f (Function.update (Function.update v i t) j t) := by
          conv_lhs => rw [← Function.update_eq_self j (Function.update v i t), hwj]
          exact f.map_update_smul _ j (s j) t
        have e3 : f (Function.update (Function.update v i t) j t) = 0 := by
          refine f.map_eq_zero_of_eq _ (i := i) (j := j) ?_ hij
          rw [Function.update_of_ne hij, Function.update_self, Function.update_self]
        rw [e1, e2, e3, smul_zero, smul_zero]
      · push Not at hT
        have hcard : T.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb => hT a ha b hb
        let c : Fin n → S := fun i => if i ∈ I \ T then z else 1
        let v : Fin n → M := fun i => if i ∈ T then α i else if i ∈ I then β i else u i
        have hv : T.piecewise α γ = fun i => c i • v i := by
          funext i
          by_cases hiT : i ∈ T
          · simp [c, v, hiT]
          · by_cases hiI : i ∈ I <;> simp [c, v, hiT, hiI, γ]
        have hprod : ∏ i, c i = z ^ (I \ T).card := by
          rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ I \ T),
            Finset.prod_congr rfl (fun i hi => if_pos (Finset.mem_filter.mp hi).2),
            Finset.prod_congr rfl (fun i hi => if_neg (Finset.mem_filter.mp hi).2),
            Finset.prod_const, Finset.prod_const_one, mul_one, Finset.filter_mem_eq_inter,
            Finset.univ_inter]
        have hle : I.card - 1 ≤ (I \ T).card := by
          rw [Finset.card_sdiff_of_subset hTI]
          omega
        refine ⟨z ^ ((I \ T).card - (I.card - 1)) • f v, ?_⟩
        rw [hv, f.map_smul_univ, hprod, smul_smul, ← pow_add, Nat.add_sub_cancel' hle]
    · refine ⟨0, ?_⟩
      rw [smul_zero]
      obtain ⟨i, hiT, hiI⟩ := Finset.not_subset.mp hTI
      exact f.map_coord_zero i (by simp [hiT, α, hiI])
  choose ω hω using key
  refine ⟨∑ T, ω T, ?_⟩
  rw [hsplit, Finset.smul_sum]
  have := f.toMultilinearMap.map_add_univ α γ
  simp only [AlternatingMap.coe_multilinearMap] at this
  rw [this]
  exact Finset.sum_congr rfl fun T _ => hω T

/-- **The wedge estimate.** If `uᵢ = z^{eᵢ-1} (sᵢ t + z βᵢ)` with `eᵢ ≥ 1` for `i` in a non-empty
set `I`, then `⋀ᵢ uᵢ ∈ z^{∑_{i ∈ I} eᵢ - 1} ⋀ⁿ M`. -/
private theorem exists_ιMulti_eq_pow_smul {S M : Type*} [CommRing S] [AddCommGroup M]
    [Module S M] {n : ℕ} (u : Fin n → M) (z : S) (t : M) (I : Finset (Fin n))
    (hI : I.Nonempty) (e : Fin n → ℕ) (he : ∀ i ∈ I, 1 ≤ e i) (s : Fin n → S) (β : Fin n → M)
    (hu : ∀ i ∈ I, u i = z ^ (e i - 1) • (s i • t + z • β i)) :
    ∃ ω, exteriorPower.ιMulti S n u = z ^ (∑ i ∈ I, e i - 1) • ω := by
  classical
  let c : Fin n → S := fun i => if i ∈ I then z ^ (e i - 1) else 1
  let u' : Fin n → M := fun i => if i ∈ I then s i • t + z • β i else u i
  have hu' : u = fun i => c i • u' i := by
    funext i
    by_cases hi : i ∈ I
    · simp [c, u', hi, hu i hi]
    · simp [c, u', hi]
  obtain ⟨ω, hω⟩ := exists_ιMulti_eq_pow_smul_aux u' z t I s β (fun i hi => by simp [u', hi])
  have hprod : ∏ i, c i = z ^ (∑ i ∈ I, (e i - 1)) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ I)]
    rw [Finset.prod_congr rfl (fun i hi => if_pos (Finset.mem_filter.mp hi).2),
      Finset.prod_congr rfl (fun i hi => if_neg (Finset.mem_filter.mp hi).2),
      Finset.prod_const_one, mul_one, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hsum : ∑ i ∈ I, e i = ∑ i ∈ I, (e i - 1) + I.card := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i hi => by have := he i hi; omega
  have hcard : 1 ≤ I.card := Finset.card_pos.mpr hI
  refine ⟨ω, ?_⟩
  rw [hu', (exteriorPower.ιMulti S n).map_smul_univ, hprod, hω, smul_smul, ← pow_add, hsum]
  congr 2
  omega

/-- The prime of a generization is determined by the point. -/
private theorem primeOfSpecializes_congr {Y : Scheme.{u}} {x ξ ξ' : Y} (e : ξ = ξ')
    (h : ξ ⤳ x) (h' : ξ' ⤳ x) : primeOfSpecializes h = primeOfSpecializes h' := by
  subst e
  rfl

/-- The prime of the generization `fromSpecStalk x q ⤳ x` is `q`. -/
private theorem primeOfSpecializes_fromSpecStalk {Y : Scheme.{u}} {x : Y}
    (q : PrimeSpectrum (Y.presheaf.stalk x)) {ξ : Y} (hξ : ξ = Y.fromSpecStalk x q)
    (h : ξ ⤳ x) : primeOfSpecializes h = q.asIdeal := by
  subst hξ
  exact comap_maximalIdeal_stalkSpecializes_fromSpecStalk x q

/-- Every prime element `p` of `𝒪_{Y,x}` is a local equation at `x` of a prime divisor `Q`
through `x`: the prime of the generization `η_Q ⤳ x` is `(p)`. -/
private theorem exists_primeDivisor_primeOfSpecializes_eq {Y : Scheme.{u}} {x : Y}
    [IsDomain (Y.presheaf.stalk x)] [IsNoetherianRing (Y.presheaf.stalk x)]
    {p : Y.presheaf.stalk x} (hp : Prime p) :
    ∃ (Q : MMP.Mori.PrimeDivisor Y) (h : Q.genericPoint ⤳ x),
      primeOfSpecializes h = Ideal.span {p} := by
  let q : Spec (Y.presheaf.stalk x) :=
    (⟨Ideal.span {p}, (Ideal.span_singleton_prime hp.ne_zero).2 hp⟩ : PrimeSpectrum _)
  have hcoh : Order.coheight (Y.fromSpecStalk x q) = 1 := by
    rw [Stacks.Chow.coheight_fromSpecStalk_eq_height]
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hp.ne_zero) hp.not_unit
  have hQ : (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh).genericPoint =
      Y.fromSpecStalk x q := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh
  have h : (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh).genericPoint ⤳ x := by
    rw [hQ]
    exact fromSpecStalk_specializes x q
  exact ⟨_, h, primeOfSpecializes_fromSpecStalk q hQ h⟩

/-- The local ring at the generic point of a prime divisor has dimension at most one. -/
private theorem krullDimLE_one_stalk_primeDivisor {Y : Scheme.{u}}
    (P : MMP.Mori.PrimeDivisor Y) :
    Ring.KrullDimLE 1 (Y.presheaf.stalk (primeDivisorSubvariety P).genericPoint) :=
  krullDimLE_of_coheight_le (by
    rw [show (primeDivisorSubvariety P).genericPoint = P.genericPoint from rfl,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
    simp)

/-- An order along `V` from a fraction `a/b` representing a local equation at a specialization
`x` of the generic point of `V`. -/
private theorem isOrderAlong_of_specializes {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {A : Y.CartierDivisor} {V : Scheme.Subvariety Y}
    [Ring.KrullDimLE 1 (Y.presheaf.stalk V.genericPoint)] {x : Y} (h : V.genericPoint ⤳ x)
    {g : Y.totalQuotientSheaf.presheaf.stalk x} (hg : IsLocalEquationAt A x g)
    {a b : Y.presheaf.stalk x} (ha : a ≠ 0) (hb : b ≠ 0) (hab : IsFraction g a b) :
    IsOrderAlong A V ((Ring.ord _ (Y.presheaf.stalkSpecializes h a)).toNat -
      (Ring.ord _ (Y.presheaf.stalkSpecializes h b)).toNat) :=
  isOrderAlong_of_isFraction (hg.stalkSpecializes h)
    (mem_nonZeroDivisors_of_ne_zero (stalkSpecializes_ne_zero h ha))
    (mem_nonZeroDivisors_of_ne_zero (stalkSpecializes_ne_zero h hb)) (hab.stalkSpecializes h)

/-- The order at a generization, as a natural number, is additive. -/
private theorem toNat_ord_stalkSpecializes_mul {Y : Scheme.{u}} [IsIntegral Y] {ξ x : Y}
    (h : ξ ⤳ x) [IsNoetherianRing (Y.presheaf.stalk ξ)] [Ring.KrullDimLE 1 (Y.presheaf.stalk ξ)]
    {c d : Y.presheaf.stalk x} (hc : c ≠ 0) (hd : d ≠ 0) :
    (Ring.ord _ (Y.presheaf.stalkSpecializes h (c * d))).toNat =
      (Ring.ord _ (Y.presheaf.stalkSpecializes h c)).toNat +
        (Ring.ord _ (Y.presheaf.stalkSpecializes h d)).toNat := by
  rw [ord_stalkSpecializes_mul h c hd, ENat.toNat_add
    (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero (stalkSpecializes_ne_zero h hc)))
    (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero (stalkSpecializes_ne_zero h hd)))]

/-- At a generization whose prime is `(p)`, `p` normalized prime, the order of a non-zero
element is the multiplicity of `p` in its factorization. -/
private theorem toNat_ord_stalkSpecializes_eq_count {Y : Scheme.{u}} [IsIntegral Y]
    {ξ x : Y} (h : ξ ⤳ x) [IsNoetherianRing (Y.presheaf.stalk ξ)]
    [Ring.KrullDimLE 1 (Y.presheaf.stalk ξ)]
    [UniqueFactorizationMonoid (Y.presheaf.stalk x)] [NormalizationMonoid (Y.presheaf.stalk x)]
    [DecidableEq (Y.presheaf.stalk x)] {p : Y.presheaf.stalk x} (hp : Prime p)
    (hpn : normalize p = p) (hξ : primeOfSpecializes h = Ideal.span {p})
    {r : Y.presheaf.stalk x} (hr : r ≠ 0) :
    (Ring.ord _ (Y.presheaf.stalkSpecializes h r)).toNat = (normalizedFactors r).count p := by
  rw [eq_sum_normalizedFactors hr (fun r => (Ring.ord _ (Y.presheaf.stalkSpecializes h r)).toNat)
    (fun c d hcd => toNat_ord_stalkSpecializes_mul h
      (left_ne_zero_of_mul (ne_zero_of_dvd_ne_zero hr hcd))
      (right_ne_zero_of_mul (ne_zero_of_dvd_ne_zero hr hcd)))
    (fun u hu => by rw [ord_stalkSpecializes_of_isUnit h hu]; rfl)]
  rw [← sum_map_ite_eq_count]
  congr 1
  refine Multiset.map_congr rfl fun q hq => ?_
  have hq' := prime_of_normalized_factor q hq
  split_ifs with he
  · subst he; rw [ord_stalkSpecializes_eq_one h hξ]; rfl
  · rw [ord_stalkSpecializes_of_notMem h]
    · rfl
    rw [hξ, Ideal.mem_span_singleton]
    exact fun hd => he ((hp.associated_of_dvd hq' hd).eq_of_normalized hpn
      (normalize_normalized_factor q hq)).symm

/-- **The exceptional-case computation** (Lazarsfeld, proof of Lemma 9.2.19). For a prime
divisor `E ⊆ X'` there are multiplicities `c P` on finitely many prime divisors `P` of `X` with
`ord_E(μ^*D) = ∑ ord_P(D) c P` and, if some `c P ≠ 0`, `∑ c P - 1 ≤ ord_E K_{X'/X}`. At a closed
point `y ∈ E` over `x = μ(y)`, write the local equations `aⱼ/bⱼ` of a representation
`D = ∑ cⱼ Aⱼ` at `x` as products of primes `p` of the factorial ring `𝒪_{X,x}`; each `p` cuts out
a prime divisor `Q_p` through `x`, and `c Q_p` is the order along `E` of `μ^♯p`, for the `Q_p`
among the components of `D`. Those `p` are associated to members `wᵢ` of a regular system of
parameters at `x`; with `z₁` a prime generator of the ideal of `E` at `y` and
`μ^♯wᵢ = z₁^{eᵢ} bᵢ`, the wedge estimate puts the Jacobian `J` of `μ` in
`z₁^{∑ eᵢ - 1} 𝒪_{X',y}`, and `J` is a local equation of `K_{X'/X}` at `y`. -/
private theorem exists_coeff_weilPullback_eq_sum {k : Type u} [Field k]
    [PerfectField k] {X X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [MMP.Mori.IsVariety k sX] (hX : MMP.Mori.IsSmoothScheme sX) {μ : X' ⟶ X}
    [MMP.Mori.IsVariety k (μ ≫ sX)] (hX' : MMP.Mori.IsSmoothScheme (μ ≫ sX)) [IsProper μ]
    (hμ : MMP.Mori.IsBirationalMorphism μ) {D : RCartierDivisor X} {wD : RDivisor X}
    (hwD : IsWeilRDivisorOf D wD) (hsnc : HasSNCSupport sX wD)
    {K : X'.CartierDivisor} (hK : IsRelativeCanonicalDivisor sX μ K) {wK : Divisor X'}
    (hwK : IsWeilDivisorOfCartier K wK) {F : RDivisor X'} (hF : IsWeilPullback μ D F)
    (E : MMP.Mori.PrimeDivisor X') :
    ∃ c : MMP.Mori.PrimeDivisor X →₀ ℕ,
      F.coeff E = c.sum (fun P m => wD.coeff P * m) ∧
        (c ≠ 0 → (c.sum fun _ m => (m : ℤ)) - 1 ≤ wK.coeff E) := by
  classical
  /- Instances. -/
  haveI : LocallyOfFiniteType sX := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (μ ≫ sX) := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : LocallyOfFinitePresentation sX :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  haveI : LocallyOfFinitePresentation (μ ≫ sX) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (μ ≫ sX)
  haveI : IsIntegral X := AlgebraicGeometry.IsVariety.toIsIntegral sX
  haveI : IsIntegral X' := AlgebraicGeometry.IsVariety.toIsIntegral (μ ≫ sX)
  haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff _).mp hX
  haveI : Smooth (μ ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).mp hX'
  haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace (μ ≫ sX)
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  letI : X'.Over (Spec (.of k)) := ⟨μ ≫ sX⟩
  haveI : MMP.Mori.IsVariety k (X ↘ Spec (.of k)) := ‹MMP.Mori.IsVariety k sX›
  haveI : MMP.Mori.IsVariety k (X' ↘ Spec (.of k)) := ‹MMP.Mori.IsVariety k (μ ≫ sX)›
  haveI : Smooth (X' ↘ Spec (.of k)) := ‹Smooth (μ ≫ sX)›
  haveI : μ.IsOver (Spec (.of k)) := ⟨rfl⟩
  /- A closed point `y ∈ E` and its image `x = μ(y)`, a closed point of `X`. -/
  obtain ⟨y, hyE, hy⟩ : ∃ y ∈ E.support, IsClosed ({y} : Set X') := by
    refine IsClosed.exists_closed_singleton ?_ ⟨E.genericPoint, ?_⟩
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hx : IsClosed ({μ y} : Set X) := by
    have := μ.isClosedMap _ hy
    rwa [Set.image_singleton] at this
  have hη : E.genericPoint ⤳ y := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hyE
  /- The local rings. -/
  haveI : IsRegularLocalRing (X.presheaf.stalk (μ y)) :=
    isRegularLocalRing_stalk_of_smooth_over_field sX (μ y)
  haveI : IsRegularLocalRing (X'.presheaf.stalk y) :=
    isRegularLocalRing_stalk_of_smooth_over_field (μ ≫ sX) y
  haveI : UniqueFactorizationMonoid (X.presheaf.stalk (μ y)) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  haveI : UniqueFactorizationMonoid (X'.presheaf.stalk y) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  letI : NormalizationMonoid (X.presheaf.stalk (μ y)) :=
    UniqueFactorizationMonoid.normalizationMonoid.toNormalizationMonoid
  letI : NormalizationMonoid (X'.presheaf.stalk y) :=
    UniqueFactorizationMonoid.normalizationMonoid.toNormalizationMonoid
  haveI : Ring.KrullDimLE 1 (X'.presheaf.stalk E.genericPoint) :=
    krullDimLE_one_stalk_primeDivisor E
  haveI : Ring.KrullDimLE 1 (X'.presheaf.stalk (primeDivisorSubvariety E).genericPoint) :=
    krullDimLE_one_stalk_primeDivisor E
  /- The orders `v` along `E` (computed in `𝒪_{X',y}`) and the representation of `D`. -/
  set ψ := μ.stalkMap y with hψdef
  let v : X'.presheaf.stalk y → ℕ := fun s =>
    (Ring.ord (X'.presheaf.stalk E.genericPoint) (X'.presheaf.stalkSpecializes hη s)).toNat
  have hvmul : ∀ {s t : X'.presheaf.stalk y}, s ≠ 0 → t ≠ 0 → v (s * t) = v s + v t :=
    fun hs ht => toNat_ord_stalkSpecializes_mul hη hs ht
  have hvunit : ∀ {s : X'.presheaf.stalk y}, IsUnit s → v s = 0 := fun hs => by
    simp only [v, ord_stalkSpecializes_of_isUnit hη hs]; rfl
  obtain ⟨m, c, A, D', ⟨hrep, -, A', hrep', hA'⟩, hD'⟩ := hF
  choose a b hab using fun j => (hA' j).2 y
  have hψa : ∀ j, ψ (a j) ≠ 0 := fun j => nonZeroDivisors.ne_zero (hab j).2.1
  have hψb : ∀ j, ψ (b j) ≠ 0 := fun j => nonZeroDivisors.ne_zero (hab j).2.2.1
  have ha0 : ∀ j, a j ≠ 0 := fun j h => hψa j (by rw [h, map_zero])
  have hb0 : ∀ j, b j ≠ 0 := fun j h => hψb j (by rw [h, map_zero])
  /- `ord_E(μ^*D) = ∑ⱼ cⱼ (v(μ^♯aⱼ) - v(μ^♯bⱼ))`. -/
  have hFE : F.coeff E = ∑ j, (((v (ψ (a j)) : ℤ) - v (ψ (b j)) : ℤ) : ℝ) * c j := by
    rw [hD'.coeff_eq_primeDivisorOrderR E, hrep', primeDivisorOrderR_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨g', hg', hfr'⟩ := (hab j).2.2.2
    rw [(isOrderAlong_of_specializes (V := primeDivisorSubvariety E) hη hg' (hψa j) (hψb j)
      hfr').primeDivisorOrder_eq]
    rfl
  /- `ord_Q(D) = ∑ⱼ cⱼ (ord_Q(aⱼ) - ord_Q(bⱼ))` for a prime divisor `Q` through `x`. -/
  have hwDQ : ∀ (Q : MMP.Mori.PrimeDivisor X) (hQ : Q.genericPoint ⤳ μ y),
      wD.coeff Q = ∑ j, (((Ring.ord _ (X.presheaf.stalkSpecializes hQ (a j))).toNat : ℤ) -
        (Ring.ord _ (X.presheaf.stalkSpecializes hQ (b j))).toNat : ℝ) * c j := by
    intro Q hQ
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk (primeDivisorSubvariety Q).genericPoint) :=
      krullDimLE_one_stalk_primeDivisor Q
    rw [hwD.coeff_eq_primeDivisorOrderR Q, hrep, primeDivisorOrderR_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨g, hg, hfr⟩ := (hab j).1
    rw [(isOrderAlong_of_specializes (V := primeDivisorSubvariety Q) hQ hg (ha0 j) (hb0 j)
      hfr).primeDivisorOrder_eq]
    push_cast; rfl
  /- The normalized prime factors `𝒫` of the `aⱼ, bⱼ` in the factorial ring `𝒪_{X,x}`. -/
  let P : Finset (X.presheaf.stalk (μ y)) := Finset.univ.biUnion fun j =>
    (normalizedFactors (a j)).toFinset ∪ (normalizedFactors (b j)).toFinset
  have hPa : ∀ j, (normalizedFactors (a j)).toFinset ⊆ P := fun j p hp =>
    Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_union_left _ hp⟩
  have hPb : ∀ j, (normalizedFactors (b j)).toFinset ⊆ P := fun j p hp =>
    Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_union_right _ hp⟩
  have hP : ∀ p ∈ P, Prime p ∧ normalize p = p ∧ ψ p ≠ 0 := by
    intro p hp
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hp
    rcases Finset.mem_union.mp hj with h | h <;> rw [Multiset.mem_toFinset] at h
    · refine ⟨prime_of_normalized_factor p h, normalize_normalized_factor p h, fun h0 => hψa j ?_⟩
      obtain ⟨d, hd⟩ := dvd_of_mem_normalizedFactors h
      rw [hd, map_mul, h0, zero_mul]
    · refine ⟨prime_of_normalized_factor p h, normalize_normalized_factor p h, fun h0 => hψb j ?_⟩
      obtain ⟨d, hd⟩ := dvd_of_mem_normalizedFactors h
      rw [hd, map_mul, h0, zero_mul]
  /- `v(μ^♯r) = ∑_{p ∈ 𝒫} mult_p(r) v(μ^♯p)` for `r = aⱼ, bⱼ`. -/
  have hvsum : ∀ r : X.presheaf.stalk (μ y), ψ r ≠ 0 → (normalizedFactors r).toFinset ⊆ P →
      v (ψ r) = ∑ p ∈ P, (normalizedFactors r).count p * v (ψ p) := by
    intro r hr hrP
    have hr0 : r ≠ 0 := fun h => hr (by rw [h, map_zero])
    rw [eq_sum_normalizedFactors hr0 (fun r => v (ψ r)) (fun s t hst => ?_)
      (fun u hu => hvunit (hu.map _)), sum_map_normalizedFactors_eq_sum_count _ _ hrP]
    have h0 : ψ (s * t) ≠ 0 := fun h => hr (by
      obtain ⟨d, hd⟩ := hst; rw [hd, map_mul, h, zero_mul])
    rw [map_mul] at h0 ⊢
    exact hvmul (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0)
  /- Each `p ∈ 𝒫` is a local equation of a prime divisor `Q_p` through `x`. -/
  choose Qf hQf hQp using fun p : P => exists_primeDivisor_primeOfSpecializes_eq (hP p.1 p.2).1
  have hcount : ∀ (p : P) (r : X.presheaf.stalk (μ y)), r ≠ 0 →
      (Ring.ord _ (X.presheaf.stalkSpecializes (hQf p) r)).toNat =
        (normalizedFactors r).count p.1 := by
    intro p r hr
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk (Qf p).genericPoint) :=
      krullDimLE_one_stalk_primeDivisor (Qf p)
    exact toNat_ord_stalkSpecializes_eq_count (hQf p) (hP p.1 p.2).1 (hP p.1 p.2).2.1 (hQp p) hr
  /- `ord_E(μ^*D) = ∑_{p ∈ 𝒫} ord_{Q_p}(D) v(μ^♯p)`. -/
  have hFE' : F.coeff E = ∑ p : P, wD.coeff (Qf p) * v (ψ p) := by
    have e1 : ∀ p : P, wD.coeff (Qf p) = ∑ j, (((normalizedFactors (a j)).count p.1 : ℝ) -
        (normalizedFactors (b j)).count p.1) * c j := by
      intro p
      rw [hwDQ (Qf p) (hQf p)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hcount p _ (ha0 j), hcount p _ (hb0 j)]
      push_cast; rfl
    simp only [e1]
    rw [hFE]
    have e2 : ∀ j, ((((v (ψ (a j)) : ℤ) - v (ψ (b j)) : ℤ) : ℝ)) = ∑ p : P,
        (((normalizedFactors (a j)).count p.1 : ℝ) - (normalizedFactors (b j)).count p.1) *
          v (ψ p) := by
      intro j
      rw [hvsum _ (hψa j) (hPa j), hvsum _ (hψb j) (hPb j)]
      push_cast
      rw [← Finset.sum_coe_sort P, ← Finset.sum_coe_sort P, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    simp only [e2, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => by ring
  /- Only the `Q_p` among the components of `D` contribute. -/
  let P' : Finset P := Finset.univ.filter fun p => Qf p ∈ wD.support
  have hFE'' : F.coeff E = ∑ p ∈ P', wD.coeff (Qf p) * v (ψ p) := by
    rw [hFE', Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with h
    · rfl
    · rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.notMem_support_iff.mp h, zero_mul]
  let cf : MMP.Mori.PrimeDivisor X →₀ ℕ := ∑ p ∈ P', Finsupp.single (Qf p) (v (ψ p))
  have hcf1 : cf.sum (fun P m => wD.coeff P * m) = ∑ p ∈ P', wD.coeff (Qf p) * v (ψ p) := by
    rw [← Finsupp.sum_finset_sum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
    exact Finset.sum_congr rfl fun p _ => Finsupp.sum_single_index (by simp)
  have hcf2 : cf.sum (fun _ m => (m : ℤ)) = ∑ p ∈ P', (v (ψ p) : ℤ) := by
    rw [← Finsupp.sum_finset_sum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
    exact Finset.sum_congr rfl fun p _ => Finsupp.sum_single_index (by simp)
  refine ⟨cf, hFE''.trans hcf1.symm, fun hc => ?_⟩
  rw [hcf2]
  have hex : ∃ p ∈ P', v (ψ p) ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hc (Finset.sum_eq_zero fun p hp => by rw [hne p hp, Finsupp.single_zero])
  /- Regular systems of parameters `z` at `y` and `w` at `x`, adapted to the components. -/
  obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (X'.presheaf.stalk y)
  have hn' : topologicalKrullDim X' = n := by
    rw [AlgebraicGeometry.topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X'
      (μ ≫ sX) y, AlgebraicGeometry.topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point
      (μ ≫ sX) y hy, hz.2]
  obtain ⟨nw, w, σ, hw, hσ, hσw⟩ := IsSNCDivisor.exists_isRegularSystemOfParameters hsnc (μ y) hx
  have hnw : n = nw := by
    have h1 := AlgebraicGeometry.topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X
      sX (μ y)
    rw [AlgebraicGeometry.topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point sX (μ y) hx,
      hw.2, topologicalKrullDim_eq_of_isBirationalMorphism sX (μ ≫ sX) hμ, hn'] at h1
    exact_mod_cast h1
  subst hnw
  /- The prime of `E` in `𝒪_{X',y}` is `(z₁)`, `z₁` a normalized prime. -/
  obtain ⟨qE, hqE, -, hqE1⟩ := exists_stalk_idealSheaf_eq_of_mem_support E hyE
  have hPη : primeOfSpecializes hη = qE.asIdeal :=
    primeOfSpecializes_fromSpecStalk qE hqE.symm hη
  obtain ⟨π, hπq, hπ⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot qE.isPrime
    (Ideal.ne_bot_of_height_eq_one hqE1)
  have hz₁ : Prime (normalize π) := (associated_normalize π).prime hπ
  have hz₁n : normalize (normalize π) = normalize π := normalize_idem π
  have hz₁q : normalize π ∈ qE.asIdeal := by
    obtain ⟨u, hu⟩ := associated_normalize π
    rw [← hu]; exact qE.asIdeal.mul_mem_right _ hπq
  have hEz : primeOfSpecializes hη = Ideal.span {normalize π} := by
    rw [hPη]; haveI := qE.isPrime; exact Ideal.eq_span_singleton_of_height_eq_one hqE1 hz₁q hz₁
  have hvcount : ∀ s : X'.presheaf.stalk y, s ≠ 0 →
      v s = (normalizedFactors s).count (normalize π) :=
    fun s hs => toNat_ord_stalkSpecializes_eq_count hη hz₁ hz₁n hEz hs
  have hpow : ∀ s : X'.presheaf.stalk y, s ≠ 0 → normalize π ^ v s ∣ s := by
    intro s hs
    apply pow_dvd_of_le_emultiplicity
    rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hz₁.irreducible hs,
      hz₁n, hvcount s hs]
  have hpow' : ∀ s : X'.presheaf.stalk y, s ≠ 0 → ∀ e : ℕ, normalize π ^ e ∣ s → e ≤ v s := by
    intro s hs e he
    have := le_emultiplicity_of_pow_dvd he
    rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hz₁.irreducible hs,
      hz₁n, ← hvcount s hs] at this
    exact_mod_cast this
  /- Each `Q_p`, `p ∈ 𝒫'`, is a component of `D` through `x`, with local equation `w_{σ(Q_p)}`. -/
  have hmemred : ∀ p ∈ P', Qf p ∈ (reducedDivisor wD).support ∧ μ y ∈ (Qf p).support := by
    intro p hp
    refine ⟨?_, ?_⟩
    · show Qf p ∈ (reducedDivisorOf wD.support).support
      rw [support_reducedDivisorOf]; exact (Finset.mem_filter.mp hp).2
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
      exact hQf p
  let idx : P' → Fin n := fun p => σ ⟨Qf p.1, hmemred p.1 p.2⟩
  have hassoc : ∀ p : P', Associated (w (idx p)) (p.1.1 : X.presheaf.stalk (μ y)) := by
    intro p
    obtain ⟨q, hq, hstalk, -⟩ :=
      exists_stalk_idealSheaf_eq_of_mem_support (Qf p.1) (hmemred p.1 p.2).2
    rw [← Ideal.span_singleton_eq_span_singleton, ← hσw ⟨Qf p.1, hmemred p.1 p.2⟩, hstalk,
      ← primeOfSpecializes_fromSpecStalk q hq.symm (hQf p.1), hQp p.1]
  have hidx : Function.Injective idx := by
    intro p p' h
    have hQ : Qf p.1 = Qf p'.1 := congrArg Subtype.val (hσ h)
    have e := (hQp p.1).symm.trans ((primeOfSpecializes_congr (by rw [hQ]) (hQf p.1)
      (hQf p'.1)).trans (hQp p'.1))
    rw [Ideal.span_singleton_eq_span_singleton] at e
    exact Subtype.ext (Subtype.ext (e.eq_of_normalized (hP _ p.1.2).2.1 (hP _ p'.1.2).2.1))
  have hψw : ∀ p : P', ψ (w (idx p)) ≠ 0 ∧ v (ψ (w (idx p))) = v (ψ p.1.1) := by
    intro p
    obtain ⟨u, hu⟩ := (hassoc p).symm
    have hu' : IsUnit (ψ (u : X.presheaf.stalk (μ y))) := u.isUnit.map ψ.hom
    rw [← hu, map_mul]
    exact ⟨mul_ne_zero (hP _ p.1.2).2.2 hu'.ne_zero,
      by rw [hvmul (hP _ p.1.2).2.2 hu'.ne_zero, hvunit hu', add_zero]⟩
  let e : Fin n → ℕ := fun i => v (ψ (w i))
  let I' : Finset (Fin n) := (Finset.univ.image idx).filter fun i => 1 ≤ e i
  have hsumI : ∑ p ∈ P', (v (ψ p) : ℤ) = ∑ i ∈ I', (e i : ℤ) := by
    rw [Finset.sum_filter_of_ne (fun i _ hi => Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hi))]
    rw [Finset.sum_image (fun p _ p' _ h => hidx h), ← Finset.sum_coe_sort P']
    exact Finset.sum_congr rfl fun p _ => by simp only [e, (hψw p).2]
  have hI' : I'.Nonempty := by
    obtain ⟨p, hp, hvp⟩ := hex
    refine ⟨idx ⟨p, hp⟩, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩⟩
    simp only [e, (hψw ⟨p, hp⟩).2]; omega
  have hdec : ∀ i ∈ I', ∃ bi, ψ (w i) = normalize π ^ e i * bi := by
    intro i hi
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hi).1
    exact hpow _ (hψw p).1
  choose! bi hbi using hdec
  /- The Jacobian `J` of `μ` in the coordinates `w` and `z`, a local equation of `K_{X'/X}`. -/
  have hn : Scheme.dimension X' = n := hn'
  have hsX : MMP.Mori.IsSmoothScheme (X ↘ Spec (.of k)) := hX
  have hsX' : MMP.Mori.IsSmoothScheme (X' ↘ Spec (.of k)) := hX'
  have hK' : IsRelativeCanonicalDivisor (X ↘ Spec (.of k)) μ K := hK
  obtain ⟨J, hJ, -⟩ := existsUnique_jacobian hsX' μ hn y hz w
  have hJloc :=
    IsRelativeCanonicalDivisor.isLocalEquationAt_jacobian hsX hsX' hμ hK' hn y hz hw J hJ
  /- `J ∈ z₁^{γ-1} 𝒪_{X',y}`, `γ = ∑ eᵢ`, by the wedge estimate. -/
  letI := Stacks.RelativeDifferentialStalkMap.algebraStalkMap (X' ↘ Spec (.of k)) y
  let T := ToType (X'.sheaf.presheaf.stalk y)
  let z₁ : T := (normalize π : X'.presheaf.stalk y)
  let cb : Fin n → T := fun i => (((e i : X'.presheaf.stalk y) * bi i : X'.presheaf.stalk y) : T)
  let bT : Fin n → T := fun i => (bi i : T)
  let dz : Fin n → T := fun i => (μ.stalkMap y (w i) : T)
  obtain ⟨ω, hω⟩ := exists_ιMulti_eq_pow_smul (S := T)
    (fun i => KaehlerDifferential.D
      (ToType ((Spec (.of k)).presheaf.stalk ((X' ↘ Spec (.of k)) y))) T (dz i))
    z₁ (KaehlerDifferential.D
      (ToType ((Spec (.of k)).presheaf.stalk ((X' ↘ Spec (.of k)) y))) T z₁) I' hI' e
    (fun i hi => (Finset.mem_filter.mp hi).2) cb
    (fun i => KaehlerDifferential.D
      (ToType ((Spec (.of k)).presheaf.stalk ((X' ↘ Spec (.of k)) y))) T (bT i))
    (fun i hi => by
      have e' : dz i = z₁ ^ e i * bT i := hbi i hi
      simp only [e']
      rw [D_pow_mul_eq _ _ (Finset.mem_filter.mp hi).2]
      simp only [cb, bT]
      norm_cast)
  have hbij := bijective_smul_ιMulti_D_stalk_of_isVariety (X' ↘ Spec (.of k)) hn' y hz
  obtain ⟨J', hJ'⟩ := hbij.2 ω
  have hJeq : J = z₁ ^ (∑ i ∈ I', e i - 1) * J' := by
    apply hbij.1
    simp only
    rw [← hJ, hω, ← hJ', smul_smul]
  /- `ord_E K_{X'/X} = v(J) ≥ γ - 1`. -/
  haveI : Nontrivial T := (inferInstance : IsDomain (X'.presheaf.stalk y)).toNontrivial
  have hJne : J ≠ 0 :=
    nonZeroDivisors.ne_zero (mem_nonZeroDivisors_of_isUnit_stalkToTotalQuotient hJloc.isUnit)
  have h1 : IsFraction (stalkToTotalQuotient y J) J 1 :=
    ⟨by rw [map_one]; exact isUnit_one, by rw [map_one, one_mul]⟩
  have hKE := (hwK E).unique (isOrderAlong_of_specializes (V := primeDivisorSubvariety E) hη
    hJloc hJne one_ne_zero h1)
  have hv1 : v 1 = 0 := hvunit isUnit_one
  have hvJ : ∑ i ∈ I', e i - 1 ≤ v J := hpow' J hJne _ ⟨J', hJeq⟩
  have hγ : 1 ≤ ∑ i ∈ I', e i := by
    obtain ⟨i, hi⟩ := hI'
    exact (Finset.mem_filter.mp hi).2.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi)
  rw [hsumI, hKE, ← Nat.cast_sum]
  change ((∑ i ∈ I', e i : ℕ) : ℤ) - 1 ≤ (v J : ℤ) - (v 1 : ℤ)
  omega

variable {k : Type u} [Field k] [PerfectField k] {X X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- **Round-down below the relative canonical divisor** (Lazarsfeld, proof of Lemma 9.2.19,
(9.10)). Let `D` be an `ℝ`-divisor on the non-singular variety `X` whose Weil divisor `wD` has
simple normal crossing support and all coefficients `< 1`, and `μ : X' ⟶ X` a proper birational
morphism from a non-singular variety. Then `⌊μ^*D⌋ ≤ K_{X'/X}`. -/
@[mmp "lem_p09a_snc_round_down_below_relative_canonical"]
public theorem IsRelativeCanonicalDivisor.roundDown_le_of_hasSNCSupport
    [MMP.Mori.IsVariety k sX] (hX : MMP.Mori.IsSmoothScheme sX) {μ : X' ⟶ X}
    [MMP.Mori.IsVariety k (μ ≫ sX)] (hX' : MMP.Mori.IsSmoothScheme (μ ≫ sX)) [IsProper μ]
    (hμ : MMP.Mori.IsBirationalMorphism μ) {D : RCartierDivisor X} {wD : RDivisor X}
    (hwD : IsWeilRDivisorOf D wD) (hsnc : HasSNCSupport sX wD)
    (hlt : ∀ P : MMP.Mori.PrimeDivisor X, wD.coeff P < 1)
    {K : X'.CartierDivisor} (hK : IsRelativeCanonicalDivisor sX μ K) {wK : Divisor X'}
    (hwK : IsWeilDivisorOfCartier K wK) {F : RDivisor X'} (hF : IsWeilPullback μ D F) :
    WeilRDivisor.roundDown F ≤ wK := by
  haveI : LocallyOfFiniteType (μ ≫ sX) := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (μ ≫ sX)
  have hKeff : ∀ E : MMP.Mori.PrimeDivisor X', 0 ≤ wK.coeff E := fun E =>
    (hwK E).nonneg_of_isEffective (hK.isEffective sX hμ)
  refine Finsupp.le_def.mpr fun E => ?_
  change (WeilRDivisor.roundDown F).coeff E ≤ wK.coeff E
  rw [WeilRDivisor.coeff_roundDown]
  by_cases hE : (E.support : Set X') ⊆ exceptionalLocus μ
  · obtain ⟨c, hcF, hcK⟩ := exists_coeff_weilPullback_eq_sum hX hX' hμ hwD
      hsnc hK hwK hF E
    rw [hcF]
    by_cases hc : c = 0
    · simpa [hc] using hKeff E
    · exact (floor_sum_mul_le _ hlt c hc).trans (hcK hc)
  · obtain ⟨P, -, hP⟩ := MMP.Positivity.exists_primeDivisor_coeff_weilPullback_eq hX hX' hμ E hE
    rw [hP D wD F hwD hF]
    have h1 : ⌊wD.coeff P⌋ ≤ (1 : ℤ) - 1 :=
      Int.le_sub_one_iff.mpr (Int.floor_lt.mpr (by simpa using hlt P))
    exact h1.trans (by simpa using hKeff E)

end MMP.Intersection
