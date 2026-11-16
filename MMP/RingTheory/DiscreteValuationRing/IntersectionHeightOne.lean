module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Height-one primes of an intersection of discrete valuation rings

Let `T ⊆ K` be the intersection of a family `(Vᵢ)` of discrete valuation rings of a field `K`
with finite character: each non-zero element of `T` lies in the maximal ideal of only finitely
many `Vᵢ`. Then every height-one prime of `T` is the centre `T ∩ 𝔪ᵢ` of one of the `Vᵢ`. This is
the part of the theory of Krull domains saying that the essential valuations of `T` belong to
every defining family of `T`.

## Main results

* `MMP.ValuationSubring.exists_pow_div_mem`: in a discrete valuation ring a power of an element
  of the maximal ideal is divisible by any non-zero element.
* `MMP.ValuationSubring.exists_eq_comap_maximalIdeal`: a height-one prime of `T` is the centre
  of one of the `Vᵢ`.
* `MMP.ValuationSubring.exists_iff_mem_maximalIdeal_of_injective`: the same for a ring embedded
  in `K` with image `T`.

## References

* [N. Bourbaki, *Commutative algebra*, VII §1 no. 3, Theorem 3]
* [H. Matsumura, *Commutative ring theory*, Theorem 12.3]
-/

@[expose] public section

open IsLocalRing

namespace MMP.ValuationSubring

variable {K : Type*} [Field K]

/-- In a discrete valuation ring `V` of `K`, a power of any element of the maximal ideal is
divisible in `V` by any given non-zero element of `V`. -/
theorem exists_pow_div_mem (V : ValuationSubring K) [IsDiscreteValuationRing V] {x y : K}
    (hx0 : x ≠ 0) (hx : x ∈ V) (hy : y ∈ V) (hym : (⟨y, hy⟩ : V) ∈ maximalIdeal V) :
    ∃ N : ℕ, y ^ N / x ∈ V := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hx0' : (⟨x, hx⟩ : V) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0' hϖ
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hym
  obtain ⟨w, hw⟩ := hym
  refine ⟨n, ?_⟩
  have hxK : x = ((u : V) : K) * (ϖ : K) ^ n := by
    simpa using congrArg Subtype.val hu
  have hyK : y = (ϖ : K) * (w : K) := by simpa using congrArg Subtype.val hw
  have hϖ0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hu0 : ((u : V) : K) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
  have : y ^ n / x = (((u⁻¹ : Vˣ) : V) * w ^ n : V) := by
    rw [hxK, hyK]
    have hui : ((u⁻¹ : Vˣ) : V) * (u : V) = 1 := u.inv_mul
    have hui' : (((u⁻¹ : Vˣ) : V) : K) * ((u : V) : K) = 1 := by
      change ((((u⁻¹ : Vˣ) : V) * (u : V) : V) : K) = ((1 : V) : K)
      rw [hui]
    push_cast
    field_simp
    rw [mul_pow]
    linear_combination (-((ϖ : K) ^ n * (w : K) ^ n)) * hui'
  rw [this]
  exact SetLike.coe_mem _

/-- **Height-one primes of an intersection of discrete valuation rings.** Let `T ⊆ K` be the
intersection of a family `(Vᵢ)` of discrete valuation rings of `K` with finite character: every
non-zero `x ∈ T` lies in the maximal ideal of only finitely many `Vᵢ`. Then every height-one prime
`q` of `T` is the centre `T ∩ 𝔪ᵢ` of one of the `Vᵢ`. -/
theorem exists_eq_comap_maximalIdeal {ι : Type*} (T : Subring K) (V : ι → ValuationSubring K)
    [∀ i, IsDiscreteValuationRing (V i)] (hT : ∀ i, T ≤ (V i).toSubring)
    (hTV : ∀ x : K, (∀ i, x ∈ V i) → x ∈ T)
    (hfin : ∀ x : T, x ≠ 0 → {i | Subring.inclusion (hT i) x ∈ maximalIdeal (V i)}.Finite)
    (q : Ideal T) [q.IsPrime] (hq0 : q ≠ ⊥)
    (hq : ∀ p : Ideal T, p.IsPrime → p ≠ ⊥ → p ≤ q → p = q) :
    ∃ i, q = (maximalIdeal (V i)).comap (Subring.inclusion (hT i)) := by
  classical
  obtain ⟨x, hxq, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq0
  set S := (hfin x hx0).toFinset with hS
  let p : ι → Ideal T := fun i => (maximalIdeal (V i)).comap (Subring.inclusion (hT i))
  suffices h : ∃ i ∈ S, p i ≤ q by
    obtain ⟨i, hi, hpq⟩ := h
    refine ⟨i, (hq (p i) (Ideal.comap_isPrime _ _) ?_ hpq).symm⟩
    refine fun h => hx0 ?_
    rw [hS, Set.Finite.mem_toFinset] at hi
    have : x ∈ p i := hi
    rw [h] at this
    exact (Submodule.mem_bot _).mp this
  by_contra hne
  push Not at hne
  choose! y hyp hyq using fun i hi => Set.not_subset.mp (hne i hi)
  set z : T := ∏ i ∈ S, y i with hz
  have hzq : z ∉ q := by
    rw [hz]
    intro hmem
    obtain ⟨i, hi, h⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hyq i hi h
  have hzm : ∀ i ∈ S, Subring.inclusion (hT i) z ∈ maximalIdeal (V i) := by
    intro i hi
    rw [hz, map_prod, ← Finset.mul_prod_erase S _ hi]
    exact Ideal.mul_mem_right _ _ (hyp i hi)
  have hxK0 : (x : K) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hN : ∀ i ∈ S, ∃ N : ℕ, (z : K) ^ N / x ∈ V i := fun i hi =>
    exists_pow_div_mem (V i) hxK0 (hT i x.2) (hT i z.2) (hzm i hi)
  choose! N hNmem using hN
  set M := ∑ i ∈ S, N i with hM
  have hmem : ∀ i, (z : K) ^ M / x ∈ V i := by
    intro i
    by_cases hi : i ∈ S
    · have hle : N i ≤ M := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
      have : (z : K) ^ M / x = (z : K) ^ (M - N i) * ((z : K) ^ N i / x) := by
        rw [mul_div_assoc', ← pow_add, Nat.sub_add_cancel hle]
      rw [this]
      exact mul_mem (pow_mem (hT i z.2) _) (hNmem i hi)
    · have hxu : IsUnit (Subring.inclusion (hT i) x) := by
        by_contra hxu
        exact hi ((hfin x hx0).mem_toFinset.mpr (mem_maximalIdeal _ |>.mpr hxu))
      obtain ⟨u, hu⟩ := hxu
      have hinv : (x : K)⁻¹ = (((u⁻¹ : (V i)ˣ) : V i) : K) := by
        refine (eq_inv_of_mul_eq_one_left ?_).symm
        have h1 : (((u⁻¹ : (V i)ˣ) : V i) * (u : V i) : V i) = 1 := u.inv_mul
        rw [hu] at h1
        exact congrArg (fun a : V i => (a : K)) h1
      rw [div_eq_mul_inv, hinv]
      exact mul_mem (pow_mem (hT i z.2) _) (SetLike.coe_mem _)
  have hwT : (z : K) ^ M / x ∈ T := hTV _ hmem
  have hzM : z ^ M = ⟨_, hwT⟩ * x := Subtype.ext (by
    change (z : K) ^ M = (z : K) ^ M / x * x
    rw [div_mul_cancel₀ _ hxK0])
  exact hzq ((inferInstance : q.IsPrime).mem_of_pow_mem M (hzM ▸ Ideal.mul_mem_left _ _ hxq))

/-- **Height-one primes of a ring embedded as an intersection of discrete valuation rings.** If
an injective `θ : R → K` has image the intersection of a family of discrete valuation rings `Vᵢ`
of `K` with finite character, then every height-one prime of `R` is the preimage of the maximal
ideal of one of the `Vᵢ`. -/
theorem exists_iff_mem_maximalIdeal_of_injective {R : Type*} [CommRing R] {ι : Type*}
    (θ : R →+* K) (hθ : Function.Injective θ) (V : ι → ValuationSubring K)
    [∀ i, IsDiscreteValuationRing (V i)] (hT : ∀ i x, θ x ∈ V i)
    (hTV : ∀ x : K, (∀ i, x ∈ V i) → x ∈ θ.range)
    (hfin : ∀ x : K, x ≠ 0 → {i | x⁻¹ ∉ V i}.Finite)
    (q : Ideal R) [q.IsPrime] (hq0 : q ≠ ⊥)
    (hq : ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≤ q → p = q) :
    ∃ i, ∀ x, x ∈ q ↔ (⟨θ x, hT i x⟩ : V i) ∈ maximalIdeal (V i) := by
  have hT' : ∀ i, θ.range ≤ (V i).toSubring := by
    rintro i _ ⟨x, rfl⟩; exact hT i x
  have hfin' : ∀ x : θ.range, x ≠ 0 →
      {i | (Subring.inclusion (hT' i) x) ∈ maximalIdeal (V i)}.Finite := by
    intro x hx0
    have hx0' : (x : K) ≠ 0 := fun h => hx0 (Subtype.ext h)
    refine (hfin _ hx0').subset fun i hi hinv => ?_
    refine (mem_maximalIdeal _).mp hi (isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext ?_⟩)
    change (x : K) * (x : K)⁻¹ = 1
    exact mul_inv_cancel₀ hx0'
  let e : R ≃+* θ.range := RingEquiv.ofBijective θ.rangeRestrict
    ⟨fun x y h => hθ (congrArg Subtype.val h), θ.rangeRestrict_surjective⟩
  have : (q.map e).IsPrime := Ideal.map_isPrime_of_equiv e
  have hcm : ∀ I : Ideal R, (I.map e).comap e = I := fun I =>
    Ideal.comap_map_of_bijective e e.bijective
  have hmc : ∀ I : Ideal θ.range, (I.comap e).map e = I := fun I =>
    Ideal.map_comap_of_surjective e e.surjective I
  have hq0' : q.map e ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective e.injective]; exact hq0
  have hq' : ∀ p : Ideal θ.range, p.IsPrime → p ≠ ⊥ → p ≤ q.map e → p = q.map e := by
    intro p hp hp0 hpq
    have hc : p.comap e = q := by
      refine hq _ (Ideal.comap_isPrime e p) (fun h => hp0 ?_) ?_
      · rw [← hmc p, h, Ideal.map_bot]
      · rw [← hcm q]; exact Ideal.comap_mono hpq
    rw [← hc, hmc]
  obtain ⟨i, hi⟩ := exists_eq_comap_maximalIdeal θ.range V hT' (fun x hx => hTV x hx) hfin'
    (q.map e) hq0' hq'
  refine ⟨i, fun x => ?_⟩
  have hmem : x ∈ q ↔ e x ∈ q.map e := by
    conv_lhs => rw [← hcm q]
    rfl
  rw [hmem, hi, Ideal.mem_comap]
  rfl

end MMP.ValuationSubring
