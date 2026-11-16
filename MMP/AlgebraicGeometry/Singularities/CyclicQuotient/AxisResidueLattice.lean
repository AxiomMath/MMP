module

public import MMP.AlgebraicGeometry.Singularities.CyclicQuotientClassGroup
import MMP.AlgebraicGeometry.Singularities.CyclicQuotient.ModelIndices

/-!
# The residue lattice along the axis of a formal cyclic quotient

Let `K` be an algebraically closed field of characteristic zero, `m ≥ 1`, `gcd(q, m) = 1`, and
`R = K[[x, y]]^{μ_m}` the invariant ring for the weights `(1, q)`. Let `I = (x) ∩ R` be the ideal
of the reduced image `D` of the axis `(x = 0)`, `ω_R = H^{-2}(K_R)` the canonical module given by
a normalized dualizing complex `K_R`, and `M = Hom_R(I, ω_R)`. We show that `R ⧸ I` is a discrete
valuation ring, that the reflexive power `(⨂ᵐ M)^{∨∨}` is free, and that the residue map
`δ_m : ⨂ᵐ ω_D → (R ⧸ I) ⊗ (⨂ᵐ M)^{∨∨}` is injective with cokernel of length `m - 1`: the
different of `D` has coefficient `(m - 1)/m`.

## Main results

* `MMP.Flips.length_cokernel_residue_cyclicInvariants`: the residue lattice computation.

## Implementation notes

That `R` is a Noetherian local ring is not a hypothesis: it is supplied inside the statement,
from `IsCyclicQuotientSetting K m q`, by `MMP.Flips.isNoetherianRing_cyclicInvariants` and by
`MMP.Flips.exists_addEquiv_weilDivisorClassGroup_cyclicQuotientModel`. Those two facts are
needed to state that `K_R` is a normalized dualizing complex, so the data `K_R`, `W`, `ρ`, `δ`
are quantified after them in the statement.
-/

universe u

namespace MMP.Flips

open MvPowerSeries CategoryTheory
open scoped TensorProduct
open scoped Stacks.SmallDerivedModel

attribute [-instance] NoetherianKoszulProIso.instHasDerivedCategoryModuleCat_stacksFrontier

section Weights

variable {K : Type u} [Field K] {m : ℕ} {q : ℤ}

/-- `f` is supported on monomials `x^a y^b` with `a + q b ≡ w (mod m)`. -/
private def HasWt (m : ℕ) (q : ℤ) (w : ℤ) (f : MvPowerSeries (Fin 2) K) : Prop :=
  ∀ d : Fin 2 →₀ ℕ, coeff d f ≠ 0 → (m : ℤ) ∣ (d 0 : ℤ) + q * d 1 - w

private theorem HasWt.mul {w₁ w₂ : ℤ} {f g : MvPowerSeries (Fin 2) K} (hf : HasWt m q w₁ f)
    (hg : HasWt m q w₂ g) : HasWt m q (w₁ + w₂) (f * g) := fun n hn => by
  rw [coeff_mul] at hn
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hx : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have e : (n 0 : ℤ) + q * n 1 - (w₁ + w₂) =
      ((x.1 0 : ℤ) + q * x.1 1 - w₁) + ((x.2 0 : ℤ) + q * x.2 1 - w₂) := by
    rw [← hx]; simp only [Finsupp.coe_add, Pi.add_apply]; push_cast; ring
  rw [e]
  exact dvd_add (hf _ (left_ne_zero_of_mul hne)) (hg _ (right_ne_zero_of_mul hne))

private theorem HasWt.congr {w w' : ℤ} (hw : (m : ℤ) ∣ w - w') {f : MvPowerSeries (Fin 2) K}
    (hf : HasWt m q w f) : HasWt m q w' f := fun n hn => by
  have := dvd_add (hf n hn) hw
  rwa [sub_add_sub_cancel] at this

private theorem hasWt_one : HasWt m q 0 (1 : MvPowerSeries (Fin 2) K) := fun n hn => by
  classical
  rw [coeff_one] at hn
  split_ifs at hn with he
  · subst he; simp
  · exact absurd rfl hn

private theorem HasWt.pow {w : ℤ} {f : MvPowerSeries (Fin 2) K} (hf : HasWt m q w f) (k : ℕ) :
    HasWt m q (k * w) (f ^ k) := by
  induction k with
  | zero => simpa using hasWt_one
  | succ k ih =>
    rw [pow_succ]
    exact (ih.mul hf).congr ⟨0, by push_cast; ring⟩

private theorem HasWt.prod {w : ℤ} {ι : Type*} (s : Finset ι) {f : ι → MvPowerSeries (Fin 2) K}
    (hf : ∀ i ∈ s, HasWt m q w (f i)) : HasWt m q (s.card * w) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasWt_one
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.card_insert_of_notMem has]
    exact ((hf a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))).congr ⟨0, by push_cast; ring⟩

/-- The weight of the variable `X i`: `1` for `x`, `q` for `y`. -/
private def varWt (q : ℤ) (i : Fin 2) : ℤ := if i = 0 then 1 else q

private theorem weight_add_single (q : ℤ) (i : Fin 2) (d : Fin 2 →₀ ℕ) (k : ℕ) :
    ((d + Finsupp.single i k) 0 : ℤ) + q * (d + Finsupp.single i k) 1 =
      ((d 0 : ℤ) + q * d 1) + k * varWt q i := by
  fin_cases i <;> simp [varWt, Finsupp.single_apply] <;> ring

private theorem coeff_X_pow_mul_add (i : Fin 2) (k : ℕ) (d : Fin 2 →₀ ℕ)
    (g : MvPowerSeries (Fin 2) K) :
    coeff (d + Finsupp.single i k) (X i ^ k * g) = coeff d g := by
  rw [X_pow_eq, coeff_monomial_mul, if_pos (by simp), one_mul]
  congr 1
  ext j; simp

private theorem hasWt_X_pow (i : Fin 2) (k : ℕ) :
    HasWt m q (k * varWt q i) (X i ^ k : MvPowerSeries (Fin 2) K) := fun n hn => by
  classical
  rw [X_pow_eq, coeff_monomial] at hn
  split_ifs at hn with he
  · subst he; fin_cases i <;> simp [varWt, Finsupp.single_apply, mul_comm]
  · exact absurd rfl hn

private theorem HasWt.of_X_pow_mul {w : ℤ} (i : Fin 2) (k : ℕ) {g : MvPowerSeries (Fin 2) K}
    (hg : HasWt m q w (X i ^ k * g)) : HasWt m q (w - k * varWt q i) g := fun d hd => by
  have := hg (d + Finsupp.single i k) (by rwa [coeff_X_pow_mul_add])
  rw [weight_add_single] at this
  convert this using 1; ring

/-- Divisibility by a power of one variable ignores a power of the other. -/
private theorem X_pow_dvd_of_dvd_X_pow_mul {i j : Fin 2} (hij : i ≠ j) {k n : ℕ}
    {f : MvPowerSeries (Fin 2) K} (h : X i ^ k ∣ X j ^ n * f) : X i ^ k ∣ f := by
  rw [X_pow_dvd_iff] at h ⊢
  intro d hd
  have := h (d + Finsupp.single j n) (by simpa [Finsupp.single_apply, hij] using hd)
  rwa [coeff_X_pow_mul_add] at this

private theorem prod_cyclicWeights_pow (ζ : rootsOfUnity m K) (n : Fin 2 →₀ ℕ) :
    (n.prod fun s k => cyclicWeights K m q ζ s ^ k) =
      (((ζ : Kˣ) ^ ((n 0 : ℤ) + q * n 1) : Kˣ) : K) := by
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simp [Fin.prod_univ_two, cyclicWeights, zpow_add, zpow_mul, zpow_natCast]

private theorem exists_isPrimitiveRoot (h : IsCyclicQuotientSetting K m q) :
    ∃ ζ : rootsOfUnity m K, IsPrimitiveRoot (ζ : Kˣ) m := by
  have := h.isAlgClosed
  have := h.charZero
  have : NeZero m := ⟨by have := h.one_le; omega⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K m
  exact ⟨rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one, by
    rw [← IsPrimitiveRoot.coe_units_iff]; simpa using hζ⟩

/-- A twisted invariance condition is a weight condition on the coefficients. -/
private theorem forall_smul_rescale_eq_iff (h : IsCyclicQuotientSetting K m q) (c : ℤ)
    (f : MvPowerSeries (Fin 2) K) :
    (∀ ζ : rootsOfUnity m K, (((ζ : Kˣ) ^ c : Kˣ) : K) •
      MvPowerSeries.rescale (cyclicWeights K m q ζ) f = f) ↔ HasWt m q (-c) f := by
  constructor
  · intro hf n hn
    obtain ⟨ζ', hζ'⟩ := exists_isPrimitiveRoot h
    have h1 := congrArg (coeff n) (hf ζ')
    rw [MvPowerSeries.coeff_smul, coeff_rescale, prod_cyclicWeights_pow,
      ← mul_assoc, ← Units.val_mul, ← zpow_add] at h1
    have h2 : (((ζ' : Kˣ) ^ (c + ((n 0 : ℤ) + q * n 1)) : Kˣ) : K) = 1 :=
      mul_right_cancel₀ hn (h1.trans (one_mul _).symm)
    have := (hζ'.zpow_eq_one_iff_dvd _).mp (Units.val_eq_one.mp h2)
    rw [sub_neg_eq_add]
    convert this using 1; ring
  · intro hf ζ
    ext n
    rw [MvPowerSeries.coeff_smul, coeff_rescale, prod_cyclicWeights_pow,
      ← mul_assoc, ← Units.val_mul, ← zpow_add]
    by_cases hn : coeff n f = 0
    · simp [hn]
    obtain ⟨k, hk⟩ := hf n hn
    have : ((ζ : Kˣ) ^ (c + ((n 0 : ℤ) + q * n 1))) = 1 := by
      rw [show c + ((n 0 : ℤ) + q * n 1) = (n 0 : ℤ) + q * n 1 - -c by ring, hk,
        zpow_mul, zpow_natCast]
      simp [(mem_rootsOfUnity _ _).mp ζ.2]
    simp [this]

private theorem mem_cyclicInvariants_iff_hasWt (h : IsCyclicQuotientSetting K m q)
    (f : MvPowerSeries (Fin 2) K) : f ∈ cyclicInvariants K m q ↔ HasWt m q 0 f := by
  rw [mem_cyclicInvariants_iff, ← neg_zero, ← forall_smul_rescale_eq_iff h 0]
  simp

end Weights

section RingFacts

open RingTheory.Sequence Pointwise

variable {K : Type u} [Field K] {m : ℕ} {q : ℤ}

private theorem mem_of_hasWt (h : IsCyclicQuotientSetting K m q) {w : ℤ} (hw : (m : ℤ) ∣ w)
    {f : MvPowerSeries (Fin 2) K} (hf : HasWt m q w f) : f ∈ cyclicInvariants K m q :=
  (mem_cyclicInvariants_iff_hasWt h f).mpr (hf.congr (by simpa using hw))

private theorem hasWt_of_mem (h : IsCyclicQuotientSetting K m q) {f : MvPowerSeries (Fin 2) K}
    (hf : f ∈ cyclicInvariants K m q) : HasWt m q 0 f :=
  (mem_cyclicInvariants_iff_hasWt h f).mp hf

/-- An invariant power series without constant term lies in the maximal ideal of `R`. -/
private theorem mem_maximalIdeal_of_constantCoeff_eq_zero [IsLocalRing (cyclicInvariants K m q)]
    {a : cyclicInvariants K m q} (ha : constantCoeff (a : MvPowerSeries (Fin 2) K) = 0) :
    a ∈ IsLocalRing.maximalIdeal (cyclicInvariants K m q) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := (hu.map (cyclicInvariants K m q).subtype).map
    (constantCoeff (σ := Fin 2) (R := K))
  simp [ha] at this

/-- The component of `f` in the monomials `x^a y^b` with `a ≡ p.1`, `b ≡ p.2 (mod m)`, divided by
`x^{p.1} y^{p.2}`: a series in `x^m, y^m`. -/
private noncomputable def cyclicComponent (m : ℕ) (p : ℕ × ℕ)
    (f : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 2) K :=
  fun e => if m ∣ e 0 ∧ m ∣ e 1 then coeff (e + (Finsupp.single 0 p.1 + Finsupp.single 1 p.2)) f
    else 0

private theorem cyclicComponent_mem (h : IsCyclicQuotientSetting K m q) (p : ℕ × ℕ)
    (f : MvPowerSeries (Fin 2) K) : cyclicComponent m p f ∈ cyclicInvariants K m q := by
  refine (mem_cyclicInvariants_iff_hasWt h _).mpr fun n hn => ?_
  change (if m ∣ n 0 ∧ m ∣ n 1 then _ else _) ≠ 0 at hn
  split_ifs at hn with hd
  · rw [sub_zero]
    exact dvd_add (Int.natCast_dvd_natCast.mpr hd.1)
      (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hd.2) _)
  · exact absurd rfl hn

private theorem sum_monomial_mul_cyclicComponent (hm : 0 < m) (f : MvPowerSeries (Fin 2) K) :
    ∑ p ∈ Finset.range m ×ˢ Finset.range m,
      monomial (Finsupp.single 0 p.1 + Finsupp.single 1 p.2) 1 * cyclicComponent m p f = f := by
  ext n
  rw [map_sum]
  simp only [coeff_monomial_mul, one_mul]
  rw [Finset.sum_eq_single (n 0 % m, n 1 % m)]
  · have hle : Finsupp.single 0 (n 0 % m) + Finsupp.single 1 (n 1 % m) ≤ n := by
      rw [Finsupp.le_def]; intro i; fin_cases i <;> simp [Nat.mod_le]
    rw [if_pos hle]
    change (if m ∣ (n - _) 0 ∧ m ∣ (n - _) 1 then _ else _) = _
    rw [if_pos, tsub_add_cancel_of_le hle]
    simp [Nat.dvd_sub_mod]
  · intro p hp hne
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    split_ifs with hle
    · change (if m ∣ (n - _) 0 ∧ m ∣ (n - _) 1 then _ else _) = _
      rw [if_neg]
      rintro ⟨h0, h1⟩
      apply hne
      rw [Finsupp.le_def] at hle
      have hle0 := hle 0; have hle1 := hle 1
      simp at h0 h1 hle0 hle1
      have e0 := ((Nat.modEq_iff_dvd' hle0).mpr h0)
      have e1 := ((Nat.modEq_iff_dvd' hle1).mpr h1)
      unfold Nat.ModEq at e0 e1
      rw [Nat.mod_eq_of_lt hp.1] at e0
      rw [Nat.mod_eq_of_lt hp.2] at e1
      exact Prod.ext e0 e1
    · rfl
  · intro hn
    exact absurd (by simp [Nat.mod_lt _ hm]) hn

private theorem module_finite_cyclicInvariants (h : IsCyclicQuotientSetting K m q) :
    Module.Finite (cyclicInvariants K m q) (MvPowerSeries (Fin 2) K) := by
  classical
  have hm : 0 < m := h.one_le
  let gens : Finset (MvPowerSeries (Fin 2) K) := (Finset.range m ×ˢ Finset.range m).image
    fun p : ℕ × ℕ => monomial (Finsupp.single 0 p.1 + Finsupp.single 1 p.2) (1 : K)
  refine ⟨⟨gens, ?_⟩⟩
  refine eq_top_iff.mpr fun f _ => ?_
  rw [← sum_monomial_mul_cyclicComponent hm f]
  refine Submodule.sum_mem _ fun p hp => ?_
  have hg : monomial (Finsupp.single 0 p.1 + Finsupp.single 1 p.2) (1 : K) ∈
      Submodule.span (cyclicInvariants K m q) (gens : Set (MvPowerSeries (Fin 2) K)) :=
    Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem
      (fun p : ℕ × ℕ => monomial (Finsupp.single 0 p.1 + Finsupp.single 1 p.2) (1 : K)) hp))
  have := Submodule.smul_mem _
    (⟨_, cyclicComponent_mem h p f⟩ : cyclicInvariants K m q) hg
  rwa [Subring.smul_def, smul_eq_mul, mul_comm] at this

private theorem ringKrullDim_cyclicInvariants (h : IsCyclicQuotientSetting K m q) :
    ringKrullDim (cyclicInvariants K m q) = 2 := by
  haveI := module_finite_cyclicInvariants h
  rw [Algebra.IsIntegral.ringKrullDim_eq (cyclicInvariants K m q) (MvPowerSeries (Fin 2) K),
    MvPowerSeries.ringKrullDim_eq]
  rfl

/-- `x^m` as an element of `R`. -/
private noncomputable def xm (h : IsCyclicQuotientSetting K m q) : cyclicInvariants K m q :=
  ⟨X 0 ^ m, mem_of_hasWt h (w := m * varWt q 0) (dvd_mul_right _ _) (hasWt_X_pow 0 m)⟩

/-- `y^m` as an element of `R`. -/
private noncomputable def ym (h : IsCyclicQuotientSetting K m q) : cyclicInvariants K m q :=
  ⟨X 1 ^ m, mem_of_hasWt h (w := m * varWt q 1) (dvd_mul_right _ _) (hasWt_X_pow 1 m)⟩

private theorem coe_xm (h : IsCyclicQuotientSetting K m q) :
    (xm h : MvPowerSeries (Fin 2) K) = X 0 ^ m := rfl

private theorem coe_ym (h : IsCyclicQuotientSetting K m q) :
    (ym h : MvPowerSeries (Fin 2) K) = X 1 ^ m := rfl

private theorem xm_ne_zero (h : IsCyclicQuotientSetting K m q) : xm h ≠ 0 := fun e => by
  have := congrArg Subtype.val e
  simp [coe_xm] at this
  have h1 := congrArg (coeff (Finsupp.single (0 : Fin 2) 1)) this.1
  simp [coeff_X] at h1

/-- If `X i ^ k` divides `r ∈ R` in `K[[x, y]]` and `m ∣ k · wt(X i)`, the quotient lies in `R`. -/
private theorem exists_eq_X_pow_mul_of_X_pow_dvd (h : IsCyclicQuotientSetting K m q)
    (i : Fin 2) (k : ℕ) (hk : (m : ℤ) ∣ k * varWt q i) {r : cyclicInvariants K m q}
    (hr : X i ^ k ∣ (r : MvPowerSeries (Fin 2) K)) :
    ∃ c : cyclicInvariants K m q,
      (r : MvPowerSeries (Fin 2) K) = X i ^ k * (c : MvPowerSeries (Fin 2) K) := by
  obtain ⟨c, hc⟩ := hr
  have hw : HasWt m q 0 (X i ^ k * c) := by rw [← hc]; exact hasWt_of_mem h r.2
  exact ⟨⟨c, mem_of_hasWt h (w := 0 - k * varWt q i) (by simpa using hk)
    (hw.of_X_pow_mul i k)⟩, hc⟩

private theorem mem_maximalIdeal_of_mem_xm_ym (h : IsCyclicQuotientSetting K m q)
    [IsLocalRing (cyclicInvariants K m q)] :
    ∀ r ∈ [xm h, ym h], r ∈ IsLocalRing.maximalIdeal (cyclicInvariants K m q) := by
  have hm : m ≠ 0 := by
    have := h.one_le
    omega
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl) <;>
    exact mem_maximalIdeal_of_constantCoeff_eq_zero (by simp [coe_xm, coe_ym, hm])

private theorem isRegular_xm_ym (h : IsCyclicQuotientSetting K m q)
    [IsLocalRing (cyclicInvariants K m q)] :
    IsRegular (cyclicInvariants K m q) [xm h, ym h] := by
  refine ⟨?_, ?_⟩
  · rw [isWeaklyRegular_cons_iff, isWeaklyRegular_cons_iff]
    refine ⟨IsSMulRegular.of_ne_zero (xm_ne_zero h), ?_, IsWeaklyRegular.nil _ _⟩
    change IsSMulRegular (cyclicInvariants K m q ⧸
      (xm h • (⊤ : Submodule (cyclicInvariants K m q) (cyclicInvariants K m q)))) (ym h)
    refine (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr fun r hr => ?_
    obtain ⟨b, -, hb⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp hr
    have hb' : X 1 ^ m * (r : MvPowerSeries (Fin 2) K) = X 0 ^ m *
        (b : MvPowerSeries (Fin 2) K) :=
      by simpa [coe_xm, coe_ym] using (congrArg Subtype.val hb).symm
    have hdvd : X 0 ^ m ∣ (r : MvPowerSeries (Fin 2) K) :=
      X_pow_dvd_of_dvd_X_pow_mul (i := 0) (j := 1) (by decide) ⟨_, hb'⟩
    obtain ⟨c, hc⟩ := exists_eq_X_pow_mul_of_X_pow_dvd h 0 m (dvd_mul_right _ _) hdvd
    refine Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mpr ⟨c, trivial, ?_⟩
    exact Subtype.ext (by simp [coe_xm, hc])
  · intro htop
    have hle : Ideal.ofList [xm h, ym h] • (⊤ : Submodule (cyclicInvariants K m q)
        (cyclicInvariants K m q)) ≤ IsLocalRing.maximalIdeal (cyclicInvariants K m q) :=
      Submodule.smul_le.mpr fun r hr n _ => Ideal.mul_mem_right _ _
        (Ideal.span_le.mpr (fun a ha => mem_maximalIdeal_of_mem_xm_ym h a ha) hr)
    have h1 : (1 : cyclicInvariants K m q) ∈ IsLocalRing.maximalIdeal _ :=
      hle (htop ▸ Submodule.mem_top)
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

private theorem isCohenMacaulayLocalRing_cyclicInvariants (h : IsCyclicQuotientSetting K m q)
    [IsLocalRing (cyclicInvariants K m q)] [IsNoetherianRing (cyclicInvariants K m q)] :
    IsCohenMacaulayLocalRing (cyclicInvariants K m q) := by
  have hge : (2 : ℕ∞) ≤ Module.depthSup (cyclicInvariants K m q)
      (IsLocalRing.maximalIdeal (cyclicInvariants K m q)) (cyclicInvariants K m q) :=
    le_sSup ⟨[xm h, ym h], rfl, mem_maximalIdeal_of_mem_xm_ym h, isRegular_xm_ym h⟩
  have hle := depthSup_le_supportDim (R := cyclicInvariants K m q) (M := cyclicInvariants K m q)
  rw [Module.supportDim_self_eq_ringKrullDim, ringKrullDim_cyclicInvariants h] at hle
  change (Module.depthSup _ _ _ : WithBot ℕ∞) = Module.supportDim _ _
  rw [Module.supportDim_self_eq_ringKrullDim, ringKrullDim_cyclicInvariants h]
  refine le_antisymm hle ?_
  rw [show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl]
  exact WithBot.coe_le_coe.mpr hge

private theorem localRingDimension_cyclicInvariants (h : IsCyclicQuotientSetting K m q)
    [IsLocalRing (cyclicInvariants K m q)] [IsNoetherianRing (cyclicInvariants K m q)] :
    Dualizing.localRingDimension (cyclicInvariants K m q) = 2 := by
  have h1 : ((IsLocalRing.maximalIdeal (cyclicInvariants K m q)).height : WithBot ℕ∞) = 2 := by
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ringKrullDim_cyclicInvariants h]
  have h2 : (IsLocalRing.maximalIdeal (cyclicInvariants K m q)).height = 2 := by
    rw [show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl] at h1
    exact WithBot.coe_injective h1
  simp [Dualizing.localRingDimension, h2]

end RingFacts

section ModelComparison

/-- On a Grothendieck abelian category the cohomology functors of the standard model and of the
locally small model of the derived category agree, along the comparison equivalence (which is the
identity on objects). -/
private noncomputable def homologyModelIso (C : Type (u + 1)) [Category.{u} C] [Abelian C]
    [IsGrothendieckAbelian.{u} C] (n : ℤ) :
    (Stacks.Injectives.grothendieckModelEquiv.{u} C).functor ⋙
      @DerivedCategory.homologyFunctor C _ _
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} C) n ≅
    @DerivedCategory.homologyFunctor C _ _ (HasDerivedCategory.standard C) n :=
  (Localization.whiskeringLeftFunctor' (@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C))
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) C).preimageIso
    ((Functor.associator _ _ _).symm ≪≫
      (@DerivedCategory.homologyFunctorFactors C _ _
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} C) n) ≪≫
      (@DerivedCategory.homologyFunctorFactors C _ _ (HasDerivedCategory.standard C) n).symm)

end ModelComparison

section Canonical

attribute [local instance 10000] HasDerivedCategory.standard

variable {K : Type u} [Field K] {m : ℕ} {q : ℤ}

private theorem isNormalizedDualizingComplex_of_ulift_zero {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {ω : DerivedCategory (ModuleCat.{u} A)}
    (h : Dualizing.IsNormalizedDualizingComplex.{u, 0} ω) :
    Dualizing.IsNormalizedDualizingComplex.{u, u} ω :=
  let eU : ULift.{0} (IsLocalRing.ResidueField A) ≃ₗ[IsLocalRing.ResidueField A]
      ULift.{u} (IsLocalRing.ResidueField A) := ULift.moduleEquiv.trans ULift.moduleEquiv.symm
  ⟨h.1, h.2.map fun e => e.trans
    ((DerivedCategory.singleFunctor (ModuleCat.{u} (IsLocalRing.ResidueField A)) 0).mapIso
      (LinearEquiv.toModuleIso eU))⟩

/-- The canonical module `H^{-2}(K_R)` of the normalized dualizing complex is the module of
invariant forms `f dx ∧ dy`, i.e. of series of weight `-(1 + q)`. -/
private theorem exists_linearEquiv_homology (h : IsCyclicQuotientSetting K m q)
    [IsLocalRing (cyclicInvariants K m q)] [IsNoetherianRing (cyclicInvariants K m q)]
    (KR : DerivedCategory (ModuleCat.{u} (cyclicInvariants K m q)))
    (hKR : Dualizing.IsNormalizedDualizingComplex.{u, u} KR) :
    ∃ ω : Submodule (cyclicInvariants K m q) (MvPowerSeries (Fin 2) K),
      (∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) ∧
      Nonempty ((@DerivedCategory.homologyFunctor (ModuleCat.{u} (cyclicInvariants K m q)) _ _
        ModuleCat.hasDerivedCategory (-2)).obj KR ≃ₗ[cyclicInvariants K m q] ω) := by
  obtain ⟨_, _, _, ⟨ω, hω, hdual⟩, _⟩ := cyclicQuotientModel_invariants h
  obtain ⟨_, n, hn⟩ := hdual
  have hN := Dualizing.isNormalizedDualizingComplex_single_neg_localRingDimension
    (isCohenMacaulayLocalRing_cyclicInvariants h) (ModuleCat.of _ ω) n hn
  rw [localRingDimension_cyclicInvariants h] at hN
  obtain ⟨e⟩ := Dualizing.IsNormalizedDualizingComplex.nonempty_iso hKR
    (isNormalizedDualizingComplex_of_ulift_zero hN)
  refine ⟨ω, fun f => (hω f).trans (forall_smul_rescale_eq_iff h _ f), ⟨?_⟩⟩
  exact (((homologyModelIso (ModuleCat.{u} (cyclicInvariants K m q)) (-2)).app KR) ≪≫
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (cyclicInvariants K m q)) (-2)).mapIso e
    ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} (cyclicInvariants K m q)) (-2)).app (ModuleCat.of _ ω))).toLinearEquiv

end Canonical

section Arith

variable {K : Type u} [Field K] {m : ℕ} {q : ℤ}

private theorem exists_nat_dvd_one_add_mul (h : IsCyclicQuotientSetting K m q) :
    ∃ b : ℕ, (m : ℤ) ∣ 1 + q * b := by
  have hm : (0 : ℤ) < m := by have := h.one_le; omega
  have hg := Int.gcd_eq_gcd_ab q m
  rw [h.gcd_eq_one, Nat.cast_one] at hg
  refine ⟨((-(Int.gcdA q m)) % m).toNat, ?_⟩
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm.ne'), Int.emod_def]
  exact ⟨Int.gcdB q m - q * (-(Int.gcdA q m) / m), by linear_combination hg⟩

private theorem exists_nat_dvd_add (h : IsCyclicQuotientSetting K m q) :
    ∃ a : ℕ, (m : ℤ) ∣ a + q := by
  have hm : (0 : ℤ) < m := by have := h.one_le; omega
  refine ⟨((-q) % m).toNat, ?_⟩
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm.ne'), Int.emod_def]
  exact ⟨-(-q / m), by ring⟩

private theorem dvd_of_dvd_q_mul (h : IsCyclicQuotientSetting K m q) {j : ℤ}
    (hj : (m : ℤ) ∣ q * j) : (m : ℤ) ∣ j :=
  Int.dvd_of_dvd_mul_right_of_gcd_one hj (by rw [Int.gcd_comm]; exact h.gcd_eq_one)

end Arith

section Hom

/-- The ideal `I = (x) ∩ R` of the reduced image of the axis `x = 0`. -/
private noncomputable abbrev axisIdeal (K : Type u) [Field K] (m : ℕ) (q : ℤ) :
    Ideal (cyclicInvariants K m q) :=
  (Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants K m q).subtype

variable {K : Type u} [Field K] {m : ℕ} {q : ℤ}

private theorem mem_axisIdeal_iff (a : cyclicInvariants K m q) :
    a ∈ axisIdeal K m q ↔ X 0 ∣ (a : MvPowerSeries (Fin 2) K) := by
  simp [Ideal.mem_comap, Ideal.mem_span_singleton]

private theorem coe_smul_submodule
    {ω : Submodule (cyclicInvariants K m q) (MvPowerSeries (Fin 2) K)} (r : cyclicInvariants K m q)
    (x : ω) :
    ((r • x : ω) : MvPowerSeries (Fin 2) K) = (r : MvPowerSeries (Fin 2) K) *
        (x : MvPowerSeries (Fin 2) K) := rfl

private theorem coe_smul_axisIdeal (r : cyclicInvariants K m q) (a : axisIdeal K m q) :
    (((r • a : axisIdeal K m q) : cyclicInvariants K m q) : MvPowerSeries (Fin 2) K) =
    (r : MvPowerSeries (Fin 2) K) * ((a : cyclicInvariants K m q) : MvPowerSeries (Fin 2) K) :=
  rfl

/-- `x^m ∈ I`. -/
private noncomputable def xmI (h : IsCyclicQuotientSetting K m q) : (axisIdeal K m q) :=
  ⟨xm h, (mem_axisIdeal_iff _).mpr (dvd_pow_self _ (by have := h.one_le; omega))⟩

private theorem coe_xmI (h : IsCyclicQuotientSetting K m q) :
    (((xmI h : (axisIdeal K m q)) : cyclicInvariants K m q) : MvPowerSeries (Fin 2) K) =
      X 0 ^ m := rfl

private theorem coe_a1_mem (h : IsCyclicQuotientSetting K m q) :
    X 0 * X 1 ^ (exists_nat_dvd_one_add_mul h).choose ∈ cyclicInvariants K m q := by
  have h1 := (hasWt_X_pow (m := m) (q := q) (K := K) 0 1).mul
    (hasWt_X_pow (m := m) (q := q) (K := K) 1 (exists_nat_dvd_one_add_mul h).choose)
  rw [pow_one] at h1
  refine mem_of_hasWt h ?_ h1
  have := (exists_nat_dvd_one_add_mul h).choose_spec
  simp only [varWt, Nat.cast_one, one_mul, if_pos rfl, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
    if_false]
  convert this using 1
  simp [varWt]; ring

/-- `x y^b ∈ I`, for `1 + q b ≡ 0 (mod m)`. -/
private noncomputable def a1 (h : IsCyclicQuotientSetting K m q) :
    (axisIdeal K m q) :=
  ⟨⟨X 0 * X 1 ^ (exists_nat_dvd_one_add_mul h).choose, coe_a1_mem h⟩,
    (mem_axisIdeal_iff _).mpr (dvd_mul_right _ _)⟩

private theorem coe_a1 (h : IsCyclicQuotientSetting K m q) :
    (((a1 h : (axisIdeal K m q)) : cyclicInvariants K m q) : MvPowerSeries (Fin 2) K) =
      X 0 * X 1 ^ (exists_nat_dvd_one_add_mul h).choose := rfl

variable {N : Type u} [AddCommGroup N] [Module (cyclicInvariants K m q) N]
    {ω : Submodule (cyclicInvariants K m q) (MvPowerSeries (Fin 2) K)}

/-- The value at `x^m`, a series divisible by `x^{m-1}`. -/
private noncomputable def evXm (h : IsCyclicQuotientSetting K m q)
    (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
    (φ : (axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N) : (MvPowerSeries (Fin 2) K) :=
  (e (φ (xmI h)) : MvPowerSeries (Fin 2) K)

private theorem X_pow_mul_ev (h : IsCyclicQuotientSetting K m q)
    (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
    (φ : (axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N) (a : (axisIdeal K m q)) :
    X 0 ^ m * (e (φ a) : MvPowerSeries (Fin 2) K) =
        ((a : cyclicInvariants K m q) : MvPowerSeries (Fin 2) K) * evXm h e φ := by
  have hc : (xm h) • a = (a : cyclicInvariants K m q) • xmI h := Subtype.ext (by
    change (xm h : cyclicInvariants K m q) * a = (a : cyclicInvariants K m q) * xm h; ring)
  have := congrArg (fun z => (e (φ z) : MvPowerSeries (Fin 2) K)) hc
  simp only [map_smul, coe_smul_submodule, coe_xm] at this
  exact this

private theorem X_ne_zero_fin_two (i : Fin 2) : (X i : MvPowerSeries (Fin 2) K) ≠ 0 := by
  intro h0
  have h1 := congrArg (coeff (Finsupp.single i 1)) h0
  simp [coeff_X] at h1

private theorem X_pow_ne_zero_fin_two (i : Fin 2) (k : ℕ) :
    (X i : MvPowerSeries (Fin 2) K) ^ k ≠ 0 :=
  pow_ne_zero _ (X_ne_zero_fin_two i)

private theorem X_pow_pred_dvd_evXm (h : IsCyclicQuotientSetting K m q)
    (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
    (φ : (axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N) : X 0 ^ (m - 1) ∣ evXm h e φ := by
  have hA := X_pow_mul_ev h e φ (a1 h)
  rw [coe_a1] at hA
  have hB : X 0 ^ (m - 1) * (e (φ (a1 h)) : MvPowerSeries (Fin 2) K) =
      X 1 ^ (exists_nat_dvd_one_add_mul h).choose * evXm h e φ := by
    apply mul_left_cancel₀ (X_ne_zero_fin_two (K := K) 0)
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel h.one_le, hA]
    ring
  exact X_pow_dvd_of_dvd_X_pow_mul (i := 0) (j := 1) (by decide) ⟨_, hB.symm⟩

/-- The numerator `ν(φ)` of `φ : I → ω`, viewed as the form `ν(φ) dx/x ∧ dy`:
`x · φ(a) = a · ν(φ)` for every `a ∈ I`. -/
private noncomputable def numer (h : IsCyclicQuotientSetting K m q)
    (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
    (φ : (axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N) : (MvPowerSeries (Fin 2) K) :=
  (X_pow_pred_dvd_evXm h e φ).choose

private theorem evXm_eq (h : IsCyclicQuotientSetting K m q) (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
    (φ : (axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N) :
    evXm h e φ = X 0 ^ (m - 1) * numer h e φ :=
  (X_pow_pred_dvd_evXm h e φ).choose_spec

private theorem X_mul_apply (h : IsCyclicQuotientSetting K m q)
    (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
    (φ : (axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N) (a : (axisIdeal K m q)) :
    X 0 * (e (φ a) : MvPowerSeries (Fin 2) K) =
        ((a : cyclicInvariants K m q) : MvPowerSeries (Fin 2) K) * numer h e φ := by
  have hA := X_pow_mul_ev h e φ a
  rw [evXm_eq] at hA
  apply mul_left_cancel₀ (X_pow_ne_zero_fin_two (K := K) 0 (m - 1))
  rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel h.one_le, hA]
  ring

/-- If `x · φ(x^m) = x^m · g`, then `numer φ = g`. -/
private theorem numer_eq_of_X_mul_eq (h : IsCyclicQuotientSetting K m q)
    (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
    (φ : (axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N) (g : MvPowerSeries (Fin 2) K)
        (hg : X 0 * (e (φ (xmI h)) : MvPowerSeries (Fin 2) K) = X 0 ^ m * g) :
    numer h e φ = g := by
  have := X_mul_apply h e φ (xmI h)
  rw [coe_xmI, hg] at this
  exact (mul_left_cancel₀ (X_pow_ne_zero_fin_two (K := K) 0 m) this).symm

private theorem hasWt_numer (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
        (φ : (axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N) :
    HasWt m q (-q) (numer h e φ) := by
  have h1 : HasWt m q (-(1 + q)) (X 0 ^ (m - 1) * numer h e φ) := by
    rw [← evXm_eq]; exact (hω _).mp (e (φ (xmI h))).2
  refine (h1.of_X_pow_mul 0 (m - 1)).congr ⟨-1, ?_⟩
  rw [Nat.cast_pred h.one_le]
  simp [varWt]
  ring

private theorem numer_add (h : IsCyclicQuotientSetting K m q) (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
    (φ ψ : (axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N) :
    numer h e (φ + ψ) = numer h e φ + numer h e ψ := by
  refine numer_eq_of_X_mul_eq h e _ _ ?_
  rw [LinearMap.add_apply, map_add, Submodule.coe_add, mul_add, X_mul_apply h e, X_mul_apply h e,
    coe_xmI]
  ring

private theorem numer_smul (h : IsCyclicQuotientSetting K m q)
    (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
    (r : cyclicInvariants K m q) (φ : (axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N) :
    numer h e (r • φ) = (r : MvPowerSeries (Fin 2) K) * numer h e φ := by
  refine numer_eq_of_X_mul_eq h e _ _ ?_
  rw [LinearMap.smul_apply, map_smul, coe_smul_submodule, ← mul_assoc, mul_comm (X 0)
      (r : MvPowerSeries (Fin 2) K),
    mul_assoc, X_mul_apply h e, coe_xmI]
  ring

private theorem numer_sub (h : IsCyclicQuotientSetting K m q)
    (e : N ≃ₗ[cyclicInvariants K m q] ω) (φ ψ : axisIdeal K m q →ₗ[cyclicInvariants K m q] N) :
    numer h e (φ - ψ) = numer h e φ - numer h e ψ := by
  rw [eq_sub_iff_add_eq, ← numer_add, sub_add_cancel]

private theorem numer_injective (h : IsCyclicQuotientSetting K m q)
    (e : N ≃ₗ[(cyclicInvariants K m q)] ω) :
    Function.Injective (numer h e) := by
  intro φ ψ hφψ
  have h0 : numer h e (φ - ψ) = 0 := by rw [numer_sub, hφψ, sub_self]
  rw [← sub_eq_zero]
  ext a
  have := X_mul_apply h e (φ - ψ) a
  rw [h0, mul_zero] at this
  have h2 : (e ((φ - ψ) a) : MvPowerSeries (Fin 2) K) = 0 := (mul_eq_zero.mp this).resolve_left
      (X_ne_zero_fin_two 0)
  have h3 : e ((φ - ψ) a) = 0 := Subtype.ext h2
  have h4 : (φ - ψ) a = 0 := e.injective (h3.trans (map_zero e).symm)
  simpa using h4

/-- The quotient `a / x` for `a ∈ I`. -/
private noncomputable def divX (a : (axisIdeal K m q)) : (MvPowerSeries (Fin 2) K) :=
  ((mem_axisIdeal_iff _).mp a.2).choose

private theorem divX_spec (a : (axisIdeal K m q)) :
    ((a : cyclicInvariants K m q) : MvPowerSeries (Fin 2) K) = X 0 * divX a :=
  ((mem_axisIdeal_iff _).mp a.2).choose_spec

private theorem divX_add (a b : (axisIdeal K m q)) : divX (a + b) = divX a + divX b := by
  apply mul_left_cancel₀ (X_ne_zero_fin_two (K := K) 0)
  rw [mul_add, ← divX_spec, ← divX_spec, ← divX_spec]; rfl

private theorem divX_smul (r : cyclicInvariants K m q) (a : (axisIdeal K m q)) : divX (r • a) =
    (r : MvPowerSeries (Fin 2) K) * divX a := by
  apply mul_left_cancel₀ (X_ne_zero_fin_two (K := K) 0)
  rw [← divX_spec, coe_smul_axisIdeal, divX_spec a]; ring

private theorem hasWt_divX (h : IsCyclicQuotientSetting K m q) (a : (axisIdeal K m q)) :
    HasWt m q (-1) (divX a) := by
  have h1 : HasWt m q 0 (X 0 ^ 1 * divX a) := by
    rw [pow_one, ← divX_spec]; exact hasWt_of_mem h (a : cyclicInvariants K m q).2
  simpa [varWt] using h1.of_X_pow_mul 0 1

/-- The homomorphism `a ↦ (a / x) g`, for `g` of weight `-q`. -/
private noncomputable def homOf (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
        (g : MvPowerSeries (Fin 2) K)
    (hg : HasWt m q (-q) g) : (axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N where
  toFun a := e.symm ⟨divX a * g, (hω _).mpr ((hasWt_divX h a).mul hg |>.congr (by ring_nf; simp))⟩
  map_add' a b := by
    rw [← map_add]; congr 1; ext1; simp [divX_add, add_mul]
  map_smul' r a := by
    rw [RingHom.id_apply, ← map_smul]; congr 1; ext1
    simp only [divX_smul, coe_smul_submodule]; ring

private theorem coe_e_homOf (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
        (g : MvPowerSeries (Fin 2) K)
    (hg : HasWt m q (-q) g) (a : (axisIdeal K m q)) :
        (e (homOf h hω e g hg a) : MvPowerSeries (Fin 2) K) = divX a * g := by
  simp [homOf]

private theorem numer_homOf (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
        (g : MvPowerSeries (Fin 2) K)
    (hg : HasWt m q (-q) g) : numer h e (homOf h hω e g hg) = g := by
  refine numer_eq_of_X_mul_eq h e _ _ ?_
  rw [coe_e_homOf, ← mul_assoc, ← divX_spec, coe_xmI]

/-- The numerator of the restriction `a ↦ a • n` of `n` is `x · n`. -/
private theorem numer_restrict (h : IsCyclicQuotientSetting K m q)
    (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
    (n : N) : numer h e (LinearMap.lcomp (cyclicInvariants K m q) _ (axisIdeal K m q).subtype
      ((LinearMap.ringLmapEquivSelf (cyclicInvariants K m q) (cyclicInvariants K m q) N).symm n)) =
          X 0 * (e n : MvPowerSeries (Fin 2) K) := by
  refine numer_eq_of_X_mul_eq h e _ _ ?_
  simp only [LinearMap.lcomp_apply', LinearMap.ringLmapEquivSelf_symm_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, LinearMap.smulRight_apply, Module.End.one_apply, map_smul,
    coe_smul_submodule, coe_xmI]
  ring

end Hom

section Quot

variable {K : Type u} [Field K] {m : ℕ} {q : ℤ}

private theorem mk_axisIdeal_eq_zero_iff (r : cyclicInvariants K m q) :
    Ideal.Quotient.mk (axisIdeal K m q) r = 0 ↔ X 0 ∣ (r : (MvPowerSeries (Fin 2) K)) := by
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_axisIdeal_iff]

private theorem isUnit_of_constantCoeff_ne_zero (a : (cyclicInvariants K m q))
    (ha : constantCoeff (a : (MvPowerSeries (Fin 2) K)) ≠ 0) : IsUnit a := by
  have hinv : (a : (MvPowerSeries (Fin 2) K))⁻¹ ∈ cyclicInvariants K m q := by
    intro ζ
    have h2 := congrArg (MvPowerSeries.rescale (cyclicWeights K m q ζ))
      (MvPowerSeries.mul_inv_cancel _ ha)
    rw [map_mul, map_one, (mem_cyclicInvariants_iff K m q _).mp a.2 ζ] at h2
    change MvPowerSeries.rescale (cyclicWeights K m q ζ) _ = _
    exact (MvPowerSeries.eq_inv_iff_mul_eq_one ha).mpr (by rwa [mul_comm])
  exact IsUnit.of_mul_eq_one (b := ⟨_, hinv⟩) (Subtype.ext (MvPowerSeries.mul_inv_cancel _ ha))

/-- The restriction to the axis of an invariant series not divisible by `x` is a unit times a
power of `y^m`, modulo `x`. -/
private theorem exists_isUnit_X_pow_dvd_sub (h : IsCyclicQuotientSetting K m q)
    (r : (cyclicInvariants K m q))
    (hr : ¬ X 0 ∣ (r : (MvPowerSeries (Fin 2) K))) :
    ∃ (k : ℕ) (u : (cyclicInvariants K m q)), IsUnit u ∧
      X 0 ∣ (r : MvPowerSeries (Fin 2) K) - X 1 ^ (m * k) * (u : MvPowerSeries (Fin 2) K) := by
  classical
  have hex : ∃ j : ℕ, coeff (Finsupp.single 1 j) (r : (MvPowerSeries (Fin 2) K)) ≠ 0 := by
    have hr' : ¬ X 0 ^ 1 ∣ (r : (MvPowerSeries (Fin 2) K)) := by rwa [pow_one]
    rw [X_pow_dvd_iff] at hr'
    push Not at hr'
    obtain ⟨d, hd0, hd⟩ := hr'
    refine ⟨d 1, ?_⟩
    have : d = Finsupp.single 1 (d 1) := by
      ext i; fin_cases i <;> simp_all
    rwa [← this]
  set j0 := Nat.find hex
  have hj0spec := Nat.find_spec hex
  have hdvd : (m : ℤ) ∣ j0 := by
    have := hasWt_of_mem h r.2 _ hj0spec
    have h' : (m : ℤ) ∣ q * j0 := by simpa [Finsupp.single_apply] using this
    exact dvd_of_dvd_q_mul h h'
  obtain ⟨k, hk⟩ : ∃ k, j0 = m * k := by exact_mod_cast hdvd
  let u : (MvPowerSeries (Fin 2) K) := fun d => if d 0 = 0 then coeff
      (d + Finsupp.single 1 (m * k)) (r : (MvPowerSeries (Fin 2) K)) else 0
  have hu : ∀ d, coeff d u = if d 0 = 0 then coeff (d + Finsupp.single 1 (m * k))
      (r : (MvPowerSeries (Fin 2) K))
      else 0 := fun d => rfl
  have humem : u ∈ cyclicInvariants K m q := by
    refine mem_of_hasWt h (w := 0) (dvd_zero _) fun d hd => ?_
    rw [hu] at hd
    split_ifs at hd with hd0
    · have := hasWt_of_mem h r.2 _ hd
      rw [weight_add_single] at this
      have h2 : (m : ℤ) ∣ ((m * k : ℕ) : ℤ) * varWt q 1 := by
        push_cast; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
      have := (Int.dvd_add_left h2).mp (by simpa using this)
      simpa using this
    · exact absurd rfl hd
  refine ⟨k, ⟨u, humem⟩, isUnit_of_constantCoeff_ne_zero _ ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply]
    change coeff 0 u ≠ 0
    rw [hu, if_pos (by simp), zero_add, ← hk]
    exact hj0spec
  · rw [← pow_one (X 0 : (MvPowerSeries (Fin 2) K)), X_pow_dvd_iff]
    intro d hd
    have hd0 : d 0 = 0 := by omega
    rw [map_sub, X_pow_eq, coeff_monomial_mul]
    split_ifs with hle
    · change coeff d (r : (MvPowerSeries (Fin 2) K)) - 1 * coeff (d - _) u = 0
      rw [hu, if_pos (by simp [hd0]), tsub_add_cancel_of_le hle, one_mul, sub_self]
    · have hlt : d 1 < j0 := by
        rw [hk]; by_contra hc; push Not at hc
        exact hle (by rw [Finsupp.single_le_iff]; exact hc)
      have : d = Finsupp.single 1 (d 1) := by
        ext i; fin_cases i <;> simp_all
      rw [sub_zero, this]
      exact not_not.mp (Nat.find_min hex hlt)

/-- The uniformizer `ϖ`, the class of `y^m`. -/
private noncomputable def unif (h : IsCyclicQuotientSetting K m q) :
    (cyclicInvariants K m q ⧸ axisIdeal K m q) :=
  Ideal.Quotient.mk (axisIdeal K m q) (ym h)

private theorem unif_pow_ne_zero (h : IsCyclicQuotientSetting K m q) (k : ℕ) :
    unif h ^ k ≠ 0 := by
  rw [unif, ← map_pow, Ne, mk_axisIdeal_eq_zero_iff, SubmonoidClass.coe_pow, coe_ym, ← pow_mul,
    ← pow_one (X 0 : (MvPowerSeries (Fin 2) K)), X_pow_dvd_iff]
  push Not
  exact ⟨Finsupp.single 1 (m * k), by simp [Finsupp.single_apply], by
    rw [X_pow_eq, coeff_monomial, if_pos rfl]; exact one_ne_zero⟩

private theorem not_isUnit_unif (h : IsCyclicQuotientSetting K m q) : ¬ IsUnit (unif h) := by
  rintro ⟨v, hv⟩
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (I := (axisIdeal K m q))
      (v⁻¹ : (cyclicInvariants K m q ⧸ axisIdeal K m q)ˣ)
  have h1 : Ideal.Quotient.mk (axisIdeal K m q) (ym h * z - 1) = 0 := by
    rw [map_sub, map_mul, hz, map_one, ← unif, ← hv, Units.mul_inv, sub_self]
  rw [mk_axisIdeal_eq_zero_iff] at h1
  have h2 : coeff 0 ((ym h * z - 1 : (cyclicInvariants K m q)) : (MvPowerSeries (Fin 2) K)) = 0 :=
    X_pow_dvd_iff.mp (by rwa [pow_one]) 0 (by simp)
  have hm : m ≠ 0 := by have := h.one_le; omega
  simp [coe_ym, coeff_zero_eq_constantCoeff_apply, hm] at h2

private theorem exists_eq_unif_pow_mul (h : IsCyclicQuotientSetting K m q)
    (z : (cyclicInvariants K m q ⧸ axisIdeal K m q))
    (hz : z ≠ 0) : ∃ (k : ℕ) (v : (cyclicInvariants K m q ⧸ axisIdeal K m q)ˣ),
    z = unif h ^ k * v := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hr : ¬ X 0 ∣ (r : MvPowerSeries (Fin 2) K) := fun hc =>
    hz ((mk_axisIdeal_eq_zero_iff r).mpr hc)
  obtain ⟨k, u, hu, hdvd⟩ := exists_isUnit_X_pow_dvd_sub h r hr
  refine ⟨k, (hu.map (Ideal.Quotient.mk (axisIdeal K m q))).unit, ?_⟩
  rw [IsUnit.unit_spec, unif, ← map_pow, ← map_mul, ← sub_eq_zero, ← map_sub,
    mk_axisIdeal_eq_zero_iff]
  convert hdvd using 2
  simp [coe_ym, pow_mul]

private theorem isDomain_quot (h : IsCyclicQuotientSetting K m q) : IsDomain
    (cyclicInvariants K m q ⧸ axisIdeal K m q) := by
  haveI : Nontrivial (cyclicInvariants K m q ⧸ axisIdeal K m q) :=
      ⟨⟨1, 0, by simpa using unif_pow_ne_zero h 0⟩⟩
  haveI : NoZeroDivisors (cyclicInvariants K m q ⧸ axisIdeal K m q) := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hc
    push Not at hc
    obtain ⟨i, v, rfl⟩ := exists_eq_unif_pow_mul h a hc.1
    obtain ⟨j, w, rfl⟩ := exists_eq_unif_pow_mul h b hc.2
    have : unif h ^ (i + j) *
        ((v * w : (cyclicInvariants K m q ⧸ axisIdeal K m q)ˣ) :
        (cyclicInvariants K m q ⧸ axisIdeal K m q)) = 0 := by
      rw [pow_add, Units.val_mul]; rw [← hab]; ring
    exact unif_pow_ne_zero h (i + j) ((Units.mul_left_eq_zero _).mp this)
  exact NoZeroDivisors.to_isDomain _

private theorem irreducible_unif (h : IsCyclicQuotientSetting K m q) :
    Irreducible (unif h) := by
  haveI := isDomain_quot h
  refine ⟨not_isUnit_unif h, fun a b hab => ?_⟩
  have ha : a ≠ 0 := by rintro rfl; exact unif_pow_ne_zero h 1 (by simpa using hab)
  have hb : b ≠ 0 := by rintro rfl; exact unif_pow_ne_zero h 1 (by simpa using hab)
  obtain ⟨i, v, rfl⟩ := exists_eq_unif_pow_mul h a ha
  obtain ⟨j, w, rfl⟩ := exists_eq_unif_pow_mul h b hb
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · left; simp
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · right; simp
  exfalso
  apply not_isUnit_unif h
  have e1 : unif h * (1 - unif h ^ (i + j - 1) *
      ((v * w : (cyclicInvariants K m q ⧸ axisIdeal K m q)ˣ) :
        (cyclicInvariants K m q ⧸ axisIdeal K m q))) = 0 := by
    have : unif h ^ (i + j) = unif h * unif h ^ (i + j - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [mul_sub, mul_one, ← mul_assoc, ← this, Units.val_mul]
    nth_rewrite 1 [hab]; ring
  have e2 := (mul_eq_zero.mp e1).resolve_left (unif_pow_ne_zero h 1 ∘ by simp)
  have e3 : unif h * (unif h ^ (i + j - 2) *
      ((v * w : (cyclicInvariants K m q ⧸ axisIdeal K m q)ˣ) :
        (cyclicInvariants K m q ⧸ axisIdeal K m q))) = 1 := by
    have : unif h ^ (i + j - 1) = unif h * unif h ^ (i + j - 2) := by
      rw [← pow_succ']; congr 1; omega
    rw [← mul_assoc, ← this]; exact (sub_eq_zero.mp e2).symm
  exact IsUnit.of_mul_eq_one _ e3

private theorem isDiscreteValuationRing_quot (h : IsCyclicQuotientSetting K m q)
    [IsDomain (cyclicInvariants K m q ⧸ axisIdeal K m q)] : IsDiscreteValuationRing
        (cyclicInvariants K m q ⧸ axisIdeal K m q) := by
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨unif h, irreducible_unif h, fun {z} hz => ?_⟩
  obtain ⟨k, v, rfl⟩ := exists_eq_unif_pow_mul h z hz
  exact ⟨k, v, rfl⟩

end Quot

section Lattice

variable {K : Type u} [Field K] {m : ℕ} {q : ℤ}
variable {N : Type u} [AddCommGroup N] [Module (cyclicInvariants K m q) N]
    {ω : Submodule (cyclicInvariants K m q) (MvPowerSeries (Fin 2) K)}

/-- The kernel of the adjunction `ρ` consists of the forms without pole along the axis. -/
private theorem rho_eq_zero_iff (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
    {W : Type u} [AddCommGroup W] [Module (cyclicInvariants K m q) W]
        (ρ : ((axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N) →ₗ[(cyclicInvariants K m q)] W)
    (hρex : Function.Exact (LinearMap.lcomp (cyclicInvariants K m q) _ (axisIdeal K m q).subtype ∘ₗ
      (LinearMap.ringLmapEquivSelf (cyclicInvariants K m q) (cyclicInvariants K m q)
          N).symm.toLinearMap) ρ)
    (φ : (axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N) : ρ φ = 0 ↔ X 0 ∣ numer h e φ := by
  rw [hρex φ]
  constructor
  · rintro ⟨n, rfl⟩
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, numer_restrict]
    exact dvd_mul_right _ _
  · rintro ⟨g, hg⟩
    have hw : HasWt m q (-q) (X 0 ^ 1 * g) := by rw [pow_one, ← hg]; exact hasWt_numer h hω e φ
    have hgω : g ∈ ω := (hω g).mpr ((hw.of_X_pow_mul 0 1).congr ⟨0, by simp [varWt]; ring⟩)
    refine ⟨e.symm ⟨g, hgω⟩, numer_injective h e ?_⟩
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, numer_restrict, LinearEquiv.apply_symm_apply, hg]

/-- `y^{m-1}`, the numerator of the generator `y^{m-1} dx/x ∧ dy` of `ω_R(D)` modulo `ω_R`. -/
private theorem hasWt_X_one_pow_pred (h : IsCyclicQuotientSetting K m q) :
    HasWt m q (-q) (X 1 ^ (m - 1) : (MvPowerSeries (Fin 2) K)) := by
  refine (hasWt_X_pow 1 (m - 1)).congr ⟨q, ?_⟩
  rw [Nat.cast_pred h.one_le]
  simp [varWt]
  ring

/-- The homomorphism `φ₀` with numerator `y^{m-1}`. -/
private noncomputable def gen0 (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[(cyclicInvariants K m q)] ω) :
        ((axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N) :=
  homOf h hω e _ (hasWt_X_one_pow_pred h)

private theorem numer_gen0 (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[(cyclicInvariants K m q)] ω) :
    numer h e (gen0 h hω e) = X 1 ^ (m - 1) :=
  numer_homOf h hω e _ _

/-- Every value of `ρ` is a multiple of `ρ φ₀`, where `numer φ₀ = y^{m-1}`. -/
private theorem exists_eq_smul_rho (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
    {W : Type u} [AddCommGroup W] [Module (cyclicInvariants K m q) W]
        (ρ : ((axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N) →ₗ[(cyclicInvariants K m q)] W)
    (hρex : Function.Exact (LinearMap.lcomp (cyclicInvariants K m q) _ (axisIdeal K m q).subtype ∘ₗ
      (LinearMap.ringLmapEquivSelf (cyclicInvariants K m q) (cyclicInvariants K m q)
          N).symm.toLinearMap) ρ)
    (φ : (axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N) :
    ∃ c : cyclicInvariants K m q, ρ φ = c • ρ (gen0 h hω e) := by
  classical
  set g := numer h e φ
  have hgw : HasWt m q (-q) g := hasWt_numer h hω e φ
  let c : (MvPowerSeries (Fin 2) K) := fun d => if d 0 = 0 then coeff
      (d + Finsupp.single 1 (m - 1)) g else 0
  have hc : ∀ d, coeff d c = if d 0 = 0 then coeff (d + Finsupp.single 1 (m - 1)) g else 0 :=
    fun d => rfl
  have hcmem : c ∈ cyclicInvariants K m q := by
    refine mem_of_hasWt h (w := 0) (dvd_zero _) fun d hd => ?_
    rw [hc] at hd
    split_ifs at hd with hd0
    · have := hgw _ hd
      rw [weight_add_single, Nat.cast_pred h.one_le] at this
      rw [show (d 0 : ℤ) + q * d 1 - 0 =
          ((d 0 : ℤ) + q * d 1 + (m - 1) * varWt q 1 - -q) - m * q by simp [varWt]; ring]
      exact dvd_sub this (dvd_mul_right _ _)
    · exact absurd rfl hd
  refine ⟨⟨c, hcmem⟩, ?_⟩
  rw [← sub_eq_zero, ← map_smul, ← map_sub, rho_eq_zero_iff h hω e ρ hρex]
  have hsub :
      numer h e (φ - (⟨c, hcmem⟩ : cyclicInvariants K m q) • gen0 h hω e) =
      g - X 1 ^ (m - 1) * c := by
    rw [numer_sub, numer_smul, numer_gen0, mul_comm]
  rw [hsub, ← pow_one (X 0 : (MvPowerSeries (Fin 2) K)), X_pow_dvd_iff]
  intro d hd
  have hd0 : d 0 = 0 := by omega
  rw [map_sub, X_pow_eq, coeff_monomial_mul]
  split_ifs with hle
  · rw [one_mul, hc, if_pos (by simp [hd0]), tsub_add_cancel_of_le hle, sub_self]
  · rw [sub_zero]
    have hlt : d 1 < m - 1 :=
      lt_of_not_ge fun hcon => hle (Finsupp.single_le_iff.mpr hcon)
    by_contra hne
    have := hgw d hne
    rw [hd0, Nat.cast_zero, zero_add, sub_neg_eq_add, ← mul_add_one] at this
    have := Int.le_of_dvd (by positivity) (dvd_of_dvd_q_mul h this)
    omega

private theorem prod_numer_update [DecidableEq (Fin m)] (h : IsCyclicQuotientSetting K m q)
    (e : N ≃ₗ[cyclicInvariants K m q] ω)
    (f : Fin m → (axisIdeal K m q →ₗ[cyclicInvariants K m q] N)) (i : Fin m)
    (x : axisIdeal K m q →ₗ[cyclicInvariants K m q] N) :
    ∏ j, numer h e (Function.update f i x j) =
      numer h e x * ∏ j ∈ Finset.univ \ {i}, numer h e (f j) := by
  rw [show (fun j => numer h e (Function.update f i x j)) =
      Function.update (fun j => numer h e (f j)) i (numer h e x) from
    funext (Function.apply_update (fun _ => numer h e) f i x)]
  exact Finset.prod_update_of_mem (Finset.mem_univ i) (fun j => numer h e (f j)) _

/-- The product of the numerators, the pairing `⨂ᵐ ω_R(D) → R` dual to `(dx/x ∧ dy)^{⊗m}`. -/
private noncomputable def prodNumer (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[(cyclicInvariants K m q)] ω) :
    MultilinearMap (cyclicInvariants K m q)
        (fun _ : Fin m => (axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N)
        (cyclicInvariants K m q) where
  toFun f := ⟨∏ i, numer h e (f i), mem_of_hasWt h (w := (Finset.univ : Finset (Fin m)).card * -q)
    (by simp) (HasWt.prod _ fun i _ => hasWt_numer h hω e (f i))⟩
  map_update_add' f i x y := Subtype.ext <| by
    change ∏ j, numer h e (Function.update f i (x + y) j) =
      (∏ j, numer h e (Function.update f i x j)) + ∏ j, numer h e (Function.update f i y j)
    rw [prod_numer_update, prod_numer_update, prod_numer_update, numer_add, add_mul]
  map_update_smul' f i r x := Subtype.ext <| by
    change ∏ j, numer h e (Function.update f i (r • x) j) =
      (r : MvPowerSeries (Fin 2) K) * ∏ j, numer h e (Function.update f i x j)
    rw [prod_numer_update, prod_numer_update, numer_smul, mul_assoc]

private theorem coe_prodNumer (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
    (f : Fin m → (axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N) :
        (prodNumer h hω e f : (MvPowerSeries (Fin 2) K)) = ∏ i, numer h e (f i) := rfl

/-- `⨂ᵐ W` is generated by `⊗ ρ(φ₀)`. -/
private theorem exists_eq_smul_tprod_rho_gen0 (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[cyclicInvariants K m q] ω)
    {W : Type u} [AddCommGroup W] [Module (cyclicInvariants K m q ⧸ axisIdeal K m q) W]
    [Module (cyclicInvariants K m q) W]
    [IsScalarTower (cyclicInvariants K m q) (cyclicInvariants K m q ⧸ axisIdeal K m q) W]
    (ρ : (axisIdeal K m q →ₗ[cyclicInvariants K m q] N) →ₗ[cyclicInvariants K m q] W)
    (hρ : Function.Surjective ρ)
    (hρex : Function.Exact (LinearMap.lcomp (cyclicInvariants K m q) _ (axisIdeal K m q).subtype ∘ₗ
      (LinearMap.ringLmapEquivSelf (cyclicInvariants K m q) (cyclicInvariants K m q)
          N).symm.toLinearMap) ρ)
    (z : TensorPower (cyclicInvariants K m q ⧸ axisIdeal K m q) m W) :
    ∃ a : cyclicInvariants K m q ⧸ axisIdeal K m q,
      z = a • PiTensorProduct.tprod _ fun _ : Fin m => ρ (gen0 h hω e) := by
  have hz : z ∈ Submodule.span (cyclicInvariants K m q ⧸ axisIdeal K m q)
      (Set.range (PiTensorProduct.tprod (cyclicInvariants K m q ⧸ axisIdeal K m q))) := by
    rw [PiTensorProduct.span_tprod_eq_top]; trivial
  refine Submodule.mem_span_singleton.mp (Submodule.span_le.mpr ?_ hz) |>.imp fun _ => Eq.symm
  rintro _ ⟨w, rfl⟩
  have hc : ∀ i, ∃ c : cyclicInvariants K m q, w i = c • ρ (gen0 h hω e) := fun i => by
    obtain ⟨φ, hφ⟩ := hρ (w i)
    exact hφ ▸ exists_eq_smul_rho h hω e ρ hρex φ
  choose c hc using hc
  have : w = fun i => Ideal.Quotient.mk (axisIdeal K m q) (c i) • ρ (gen0 h hω e) := by
    funext i; rw [hc i, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  rw [this, MultilinearMap.map_smul_univ]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end Lattice

section Dual

variable {K : Type u} [Field K] {m : ℕ} {q : ℤ}
variable {N : Type u} [AddCommGroup N] [Module (cyclicInvariants K m q) N]
    {ω : Submodule (cyclicInvariants K m q) (MvPowerSeries (Fin 2) K)}

/-- The pairing `⨂ᵐ ω_R(D) → R`, `⊗ φᵢ ↦ ∏ numer φᵢ`. -/
private noncomputable def pairing (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[(cyclicInvariants K m q)] ω) :
    Module.Dual (cyclicInvariants K m q)
        (TensorPower (cyclicInvariants K m q) m
        ((axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N)) :=
  PiTensorProduct.lift (prodNumer h hω e)

private theorem pairing_tprod (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
        (f : Fin m → ((axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N)) :
    pairing h hω e (PiTensorProduct.tprod (cyclicInvariants K m q) f) = prodNumer h hω e f :=
  PiTensorProduct.lift.tprod f

/-- Testing a functional on `⨂ᵐ ω_R(D)` against a power of one generator. -/
private theorem pow_mul_apply_tprod (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
        (g : (MvPowerSeries (Fin 2) K))
    (hg : HasWt m q (-q) g) (hg0 : g ≠ 0)
    (Ψ : Module.Dual (cyclicInvariants K m q)
        (TensorPower (cyclicInvariants K m q) m ((axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N)))
    (f : Fin m → (axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N) :
    g ^ m * (Ψ (PiTensorProduct.tprod (cyclicInvariants K m q) f) : (MvPowerSeries (Fin 2) K)) =
      (prodNumer h hω e f : (MvPowerSeries (Fin 2) K)) *
        (Ψ (PiTensorProduct.tprod (cyclicInvariants K m q) (fun _ => homOf h hω e g hg)) :
            (MvPowerSeries (Fin 2) K)) := by
  have hgm : g ^ m = g ^ (m - 1) * g := by rw [← pow_succ, Nat.sub_add_cancel h.one_le]
  let s : (cyclicInvariants K m q) :=
      ⟨g ^ m, mem_of_hasWt h (w := m * -q) (dvd_mul_right _ _) (hg.pow m)⟩
  let c : Fin m → (cyclicInvariants K m q) := fun i => ⟨numer h e (f i) * g ^ (m - 1),
    mem_of_hasWt h (w := -q + (m - 1 : ℕ) * -q) ⟨-q, by rw [Nat.cast_pred h.one_le]; ring⟩
      ((hasWt_numer h hω e (f i)).mul (hg.pow (m - 1)))⟩
  have hsf : (fun i => s • f i) = fun i => c i • homOf h hω e g hg := by
    funext i
    apply numer_injective h e
    rw [numer_smul, numer_smul, numer_homOf]
    change g ^ m * _ = numer h e (f i) * g ^ (m - 1) * g
    rw [hgm]; ring
  have h1 := (Ψ.compMultilinearMap (PiTensorProduct.tprod (cyclicInvariants K m q))).map_smul_univ
      (fun _ => s) f
  have h2 := (Ψ.compMultilinearMap (PiTensorProduct.tprod (cyclicInvariants K m q))).map_smul_univ c
    (fun _ => homOf h hω e g hg)
  simp only [LinearMap.compMultilinearMap_apply] at h1 h2
  rw [hsf, h2] at h1
  have h3 := congrArg (fun z : (cyclicInvariants K m q) => (z : (MvPowerSeries (Fin 2) K))) h1
  simp only [smul_eq_mul, Subring.coe_mul, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, SubmonoidClass.coe_finset_prod, SubmonoidClass.coe_pow] at h3
  have hs : (s : (MvPowerSeries (Fin 2) K)) = g ^ m := rfl
  rw [hs] at h3
  have hc : ∏ i, (c i : (MvPowerSeries (Fin 2) K)) =
      (prodNumer h hω e f : (MvPowerSeries (Fin 2) K)) * (g ^ (m - 1)) ^ m := by
    rw [coe_prodNumer]
    change ∏ i, (numer h e (f i) * g ^ (m - 1)) = _
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hc] at h3
  have hne : (g ^ m) ^ (m - 1) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hg0)
  apply mul_left_cancel₀ hne
  have e1 : (g ^ m) ^ (m - 1) * g ^ m = (g ^ m) ^ m := by
    rw [← pow_succ, Nat.sub_add_cancel h.one_le]
  have e2 : (g ^ (m - 1)) ^ m = (g ^ m) ^ (m - 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [← mul_assoc, e1, ← h3, e2]
  ring

/-- Every functional on `⨂ᵐ Hom_R(I, ω)` is a multiple of `pairing`. -/
private theorem exists_eq_smul_pairing (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[(cyclicInvariants K m q)] ω)
    (Ψ : Module.Dual (cyclicInvariants K m q)
        (TensorPower (cyclicInvariants K m q) m
        ((axisIdeal K m q) →ₗ[(cyclicInvariants K m q)] N))) :
    ∃ c : (cyclicInvariants K m q), Ψ = c • pairing h hω e := by
  obtain ⟨a, ha⟩ := exists_nat_dvd_add h
  have hga : HasWt m q (-q) (X 0 ^ a : (MvPowerSeries (Fin 2) K)) :=
    (hasWt_X_pow 0 a).congr (by simpa [varWt] using ha)
  have hP : (prodNumer h hω e (fun _ => gen0 h hω e) : MvPowerSeries (Fin 2) K) =
      (X 1 ^ (m - 1)) ^ m := by
    simp only [coe_prodNumer, numer_gen0, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have key := pow_mul_apply_tprod h hω e _ hga (X_pow_ne_zero_fin_two 0 a) Ψ (fun _ => gen0 h hω e)
  rw [hP, ← pow_mul, ← pow_mul] at key
  have hdvd : X 1 ^ ((m - 1) * m) ∣
      (Ψ (PiTensorProduct.tprod _ fun _ => gen0 h hω e) : MvPowerSeries (Fin 2) K) :=
    X_pow_dvd_of_dvd_X_pow_mul (i := 1) (j := 0) (by decide) ⟨_, key⟩
  obtain ⟨c, hc⟩ := exists_eq_X_pow_mul_of_X_pow_dvd h 1 ((m - 1) * m)
    (by push_cast; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _) hdvd
  refine ⟨c, PiTensorProduct.ext (MultilinearMap.ext fun f => ?_)⟩
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.smul_apply, pairing_tprod,
    smul_eq_mul]
  apply Subtype.ext
  have k2 := pow_mul_apply_tprod h hω e _ (hasWt_X_one_pow_pred h)
    (X_pow_ne_zero_fin_two 1 (m - 1)) Ψ f
  unfold gen0 at hc
  rw [hc, ← pow_mul] at k2
  apply mul_left_cancel₀ (X_pow_ne_zero_fin_two (K := K) 1 ((m - 1) * m))
  rw [k2, Subring.coe_mul]; ring

/-- `pairing (⊗ φ₀) = (y^{m-1})^m`. -/
private theorem coe_pairing_tprod_gen0 (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[cyclicInvariants K m q] ω) :
    (pairing h hω e (PiTensorProduct.tprod _ fun _ : Fin m => gen0 h hω e) :
      MvPowerSeries (Fin 2) K) = X 1 ^ ((m - 1) * m) := by
  simp [pairing_tprod, coe_prodNumer, numer_gen0, pow_mul]

/-- `Hom_R(⨂ᵐ ω_R(D), R)` is free on `pairing`. -/
private theorem bijective_toSpanSingleton_pairing (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[cyclicInvariants K m q] ω) :
    Function.Bijective
      (LinearMap.toSpanSingleton (cyclicInvariants K m q) _ (pairing h hω e)) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun c hc => Subtype.ext ?_,
    fun Ψ => (exists_eq_smul_pairing h hω e Ψ).imp fun _ => Eq.symm⟩
  have := congrArg Subtype.val
    (LinearMap.congr_fun hc (PiTensorProduct.tprod _ fun _ : Fin m => gen0 h hω e))
  simp only [LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.zero_apply, Subring.coe_mul, coe_pairing_tprod_gen0, ZeroMemClass.coe_zero] at this
  exact (mul_eq_zero.mp this).resolve_right (X_pow_ne_zero_fin_two 1 _)

/-- The reflexive power `(⨂ᵐ ω_R(D))^{∨∨}` is `R`, by evaluation at `pairing`. -/
private noncomputable def doubleDualEquiv (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[cyclicInvariants K m q] ω) :
    Module.Dual (cyclicInvariants K m q) (Module.Dual (cyclicInvariants K m q)
      (TensorPower (cyclicInvariants K m q) m (axisIdeal K m q →ₗ[cyclicInvariants K m q] N)))
      ≃ₗ[cyclicInvariants K m q] cyclicInvariants K m q :=
  (LinearEquiv.ofBijective _ (bijective_toSpanSingleton_pairing h hω e)).dualMap.trans
    (LinearMap.ringLmapEquivSelf _ _ _)

private theorem doubleDualEquiv_apply (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[cyclicInvariants K m q] ω)
    (ψ : Module.Dual (cyclicInvariants K m q) (Module.Dual (cyclicInvariants K m q)
      (TensorPower (cyclicInvariants K m q) m (axisIdeal K m q →ₗ[cyclicInvariants K m q] N)))) :
    doubleDualEquiv h hω e ψ = ψ (pairing h hω e) := by
  change ψ (LinearMap.toSpanSingleton _ _ (pairing h hω e) 1) = _
  rw [LinearMap.toSpanSingleton_apply, one_smul]

/-- `(R ⧸ I) ⊗ (⨂ᵐ ω_R(D))^{∨∨} ≅ R ⧸ I`, by evaluation at `pairing`. -/
private noncomputable def residueEquiv (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[cyclicInvariants K m q] ω) :
    (cyclicInvariants K m q ⧸ axisIdeal K m q) ⊗[cyclicInvariants K m q]
      Module.Dual (cyclicInvariants K m q) (Module.Dual (cyclicInvariants K m q)
        (TensorPower (cyclicInvariants K m q) m (axisIdeal K m q →ₗ[cyclicInvariants K m q] N)))
      ≃ₗ[cyclicInvariants K m q ⧸ axisIdeal K m q] cyclicInvariants K m q ⧸ axisIdeal K m q :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) (doubleDualEquiv h hω e)).trans
    (TensorProduct.AlgebraTensorModule.rid _ _ _)

private theorem residueEquiv_one_tmul (h : IsCyclicQuotientSetting K m q)
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[cyclicInvariants K m q] ω)
    (ψ : Module.Dual (cyclicInvariants K m q) (Module.Dual (cyclicInvariants K m q)
      (TensorPower (cyclicInvariants K m q) m (axisIdeal K m q →ₗ[cyclicInvariants K m q] N)))) :
    residueEquiv h hω e ((1 : cyclicInvariants K m q ⧸ axisIdeal K m q) ⊗ₜ ψ) =
      Ideal.Quotient.mk (axisIdeal K m q) (ψ (pairing h hω e)) := by
  simp [residueEquiv, doubleDualEquiv_apply, Algebra.smul_def]

end Dual

section Main

/-- Over a discrete valuation ring `A`, a map `δ : M → P` from a module generated by one element
`t` to a module `P ≅ A`, sending `t` to `ϖ^n` for a uniformizer `ϖ`, is injective with cokernel
of length `n`. -/
private theorem injective_and_length_quotient_range {A M P : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [AddCommGroup M] [Module A M] [AddCommGroup P] [Module A P]
    {t : M} (ht : ∀ z : M, ∃ a : A, z = a • t) (δ : M →ₗ[A] P) (Θ : P ≃ₗ[A] A) {ϖ : A}
    (hϖ : Irreducible ϖ) {n : ℕ} (hδ : Θ (δ t) = ϖ ^ n) :
    Function.Injective δ ∧ Module.length A (P ⧸ LinearMap.range δ) = n := by
  have hΘδ (a : A) : Θ (δ (a • t)) = a * ϖ ^ n := by rw [map_smul, map_smul, hδ, smul_eq_mul]
  refine ⟨(injective_iff_map_eq_zero δ).mpr fun z hz => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := ht z
    have := hΘδ a
    rw [hz, map_zero, eq_comm, mul_eq_zero] at this
    rw [this.resolve_right (pow_ne_zero _ hϖ.ne_zero), zero_smul]
  have hrange : (LinearMap.range δ).map Θ.toLinearMap = Ideal.span {ϖ ^ n} := by
    refine le_antisymm ?_ ((Ideal.span_le).mpr ?_)
    · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
      obtain ⟨a, rfl⟩ := ht z
      exact (hΘδ a).symm ▸ Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    · rintro _ rfl
      exact ⟨_, ⟨t, rfl⟩, hδ⟩
  rw [(Submodule.Quotient.equiv _ _ Θ hrange).length_eq, ← Ideal.span_singleton_pow,
    ← (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖ,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

variable {K : Type u} [Field K] {m : ℕ} {q : ℤ}

/-- `length_cokernel_residue_cyclicInvariants` with `H^{-2}(K_R)` replaced by any module
`N ≅ ω`. -/
private theorem length_cokernel_residue_of_linearEquiv (h : IsCyclicQuotientSetting K m q)
    {N : Type u} [AddCommGroup N] [Module (cyclicInvariants K m q) N]
    {ω : Submodule (cyclicInvariants K m q) (MvPowerSeries (Fin 2) K)}
    (hω : ∀ f, f ∈ ω ↔ HasWt m q (-(1 + q)) f) (e : N ≃ₗ[cyclicInvariants K m q] ω)
    (W : Type u) [AddCommGroup W] [Module (cyclicInvariants K m q ⧸ axisIdeal K m q) W]
    [Module (cyclicInvariants K m q) W]
    [IsScalarTower (cyclicInvariants K m q) (cyclicInvariants K m q ⧸ axisIdeal K m q) W]
    (ρ : (axisIdeal K m q →ₗ[cyclicInvariants K m q] N) →ₗ[cyclicInvariants K m q] W)
    (hρ : Function.Surjective ρ)
    (hρex : Function.Exact (LinearMap.lcomp (cyclicInvariants K m q) _ (axisIdeal K m q).subtype ∘ₗ
      (LinearMap.ringLmapEquivSelf (cyclicInvariants K m q) (cyclicInvariants K m q)
          N).symm.toLinearMap) ρ)
    (δ : TensorPower (cyclicInvariants K m q ⧸ axisIdeal K m q) m W
      →ₗ[cyclicInvariants K m q ⧸ axisIdeal K m q]
      (cyclicInvariants K m q ⧸ axisIdeal K m q) ⊗[cyclicInvariants K m q]
        Module.Dual (cyclicInvariants K m q) (Module.Dual (cyclicInvariants K m q)
          (TensorPower (cyclicInvariants K m q) m (axisIdeal K m q →ₗ[cyclicInvariants K m q] N))))
    (hδ : ∀ f : Fin m → (axisIdeal K m q →ₗ[cyclicInvariants K m q] N),
      δ (PiTensorProduct.tprod _ fun i => ρ (f i)) =
        (1 : cyclicInvariants K m q ⧸ axisIdeal K m q) ⊗ₜ[cyclicInvariants K m q]
          Module.Dual.eval (cyclicInvariants K m q) _ (PiTensorProduct.tprod _ f)) :
    (∃ _ : IsDomain (cyclicInvariants K m q ⧸ axisIdeal K m q),
      IsDiscreteValuationRing (cyclicInvariants K m q ⧸ axisIdeal K m q)) ∧
    Module.Free (cyclicInvariants K m q) (Module.Dual (cyclicInvariants K m q)
      (Module.Dual (cyclicInvariants K m q)
        (TensorPower (cyclicInvariants K m q) m (axisIdeal K m q →ₗ[cyclicInvariants K m q] N)))) ∧
    Function.Injective δ ∧
    Module.length (cyclicInvariants K m q ⧸ axisIdeal K m q) (_ ⧸ LinearMap.range δ) =
      (m - 1 : ℕ) := by
  haveI := isDomain_quot h
  haveI := isDiscreteValuationRing_quot h
  have hΘ : residueEquiv h hω e (δ (PiTensorProduct.tprod _ fun _ : Fin m => ρ (gen0 h hω e))) =
      unif h ^ (m - 1) := by
    rw [hδ, residueEquiv_one_tmul, Module.Dual.eval_apply, unif, ← map_pow]
    congr 1
    exact Subtype.ext (by
      rw [coe_pairing_tprod_gen0, SubmonoidClass.coe_pow, coe_ym, ← pow_mul, mul_comm])
  exact ⟨⟨inferInstance, inferInstance⟩, Module.Free.of_equiv (doubleDualEquiv h hω e).symm,
    injective_and_length_quotient_range (exists_eq_smul_tprod_rho_gen0 h hω e ρ hρ hρex) δ
      (residueEquiv h hω e) (irreducible_unif h) hΘ⟩

end Main

/-- **The residue lattice along the axis of a formal cyclic quotient.** Let
`R = K[[x, y]]^{μ_m}` with weights `(1, q)`, `gcd(q, m) = 1`, over an algebraically closed field
`K` of characteristic zero, and let `I = (x) ∩ R` be the ideal of the reduced image `D` of
`(x = 0)`. Let `ω_R = H^{-2}(K_R)` for a normalized dualizing complex `K_R` of `R`,
`M = Hom_R(I, ω_R)`, let `ρ : M → W` be the canonical adjunction onto the canonical module `W` of
`R ⧸ I` (a surjection whose kernel is the image of the restriction `x ↦ (a ↦ a • x)`), and let
`δ : ⨂ᵐ W → (R ⧸ I) ⊗ (⨂ᵐ M)^{∨∨}` be the map induced by the products. Then `R ⧸ I` is a
discrete valuation ring, `(⨂ᵐ M)^{∨∨}` is free, `δ` is injective, and its cokernel has length
`m - 1`; that is, the different of `D` has coefficient `(m - 1)/m`. -/
@[mmp "lem_mmp_foundation_one_axis_cyclic_residue_lattice"]
public theorem length_cokernel_residue_cyclicInvariants
    {K : Type u} [Field K] {m : ℕ} {q : ℤ} (h : IsCyclicQuotientSetting K m q) :
    haveI : IsNoetherianRing (cyclicInvariants K m q) := isNoetherianRing_cyclicInvariants h
    haveI : IsLocalRing (cyclicInvariants K m q) :=
      (exists_addEquiv_weilDivisorClassGroup_cyclicQuotientModel h).2.1
    ∀ (KR : DerivedCategory (ModuleCat.{u} (cyclicInvariants K m q)))
    (hKR : Dualizing.IsNormalizedDualizingComplex.{u, u} KR)
    -- the canonical adjunction onto the canonical module `W` of `R ⧸ I`, `I = (x) ∩ R`
    (W : Type u) [AddCommGroup W]
    [Module (cyclicInvariants K m q ⧸
      (Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants K m q).subtype) W]
    [Module (cyclicInvariants K m q) W]
    [IsScalarTower (cyclicInvariants K m q) (cyclicInvariants K m q ⧸
      (Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants K m q).subtype) W]
    (ρ : ((Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants K m q).subtype →ₗ[
        cyclicInvariants K m q]
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (cyclicInvariants K m q)) (-2)).obj KR)
        →ₗ[cyclicInvariants K m q] W)
    (hρ : Function.Surjective ρ)
    (hρex : Function.Exact
      (LinearMap.lcomp (cyclicInvariants K m q) _
          ((Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap
              (cyclicInvariants K m q).subtype).subtype
        ∘ₗ (LinearMap.ringLmapEquivSelf (cyclicInvariants K m q) (cyclicInvariants K m q)
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} (cyclicInvariants K m q)) (-2)).obj
            KR)).symm.toLinearMap) ρ)
    -- the map `δ_m` induced by the products into the reflexive power
    (δ : TensorPower (cyclicInvariants K m q ⧸
        (Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants K m q).subtype) m W
      →ₗ[cyclicInvariants K m q ⧸
        (Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants K m q).subtype]
      (cyclicInvariants K m q ⧸
        (Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants K m q).subtype)
        ⊗[cyclicInvariants K m q]
        Module.Dual (cyclicInvariants K m q) (Module.Dual (cyclicInvariants K m q)
          (TensorPower (cyclicInvariants K m q) m
            ((Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants K m q).subtype
              →ₗ[cyclicInvariants K m q]
              (DerivedCategory.homologyFunctor (ModuleCat.{u} (cyclicInvariants K m q)) (-2)).obj
                KR))))
    (hδ : ∀ f : Fin m → ((Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap
        (cyclicInvariants K m q).subtype →ₗ[cyclicInvariants K m q]
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (cyclicInvariants K m q)) (-2)).obj KR),
      δ (PiTensorProduct.tprod _ fun i => ρ (f i)) =
        (1 : cyclicInvariants K m q ⧸
          (Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants K m q).subtype)
          ⊗ₜ[cyclicInvariants K m q]
          Module.Dual.eval (cyclicInvariants K m q) _ (PiTensorProduct.tprod _ f)),
    (∃ _ : IsDomain (cyclicInvariants K m q ⧸
        (Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants K m q).subtype),
      IsDiscreteValuationRing (cyclicInvariants K m q ⧸
        (Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants K m q).subtype)) ∧
    Module.Free (cyclicInvariants K m q) (Module.Dual (cyclicInvariants K m q)
      (Module.Dual (cyclicInvariants K m q) (TensorPower (cyclicInvariants K m q) m
        ((Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants K m q).subtype
          →ₗ[cyclicInvariants K m q]
          (DerivedCategory.homologyFunctor (ModuleCat.{u} (cyclicInvariants K m q)) (-2)).obj
            KR)))) ∧
    Function.Injective δ ∧
    Module.length (cyclicInvariants K m q ⧸
        (Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants K m q).subtype)
      (_ ⧸ LinearMap.range δ) = (m - 1 : ℕ) := by
  haveI := isNoetherianRing_cyclicInvariants h
  haveI := (exists_addEquiv_weilDivisorClassGroup_cyclicQuotientModel h).2.1
  intro KR hKR W _ _ _ _ ρ hρ hρex δ hδ
  exact (exists_linearEquiv_homology h KR hKR).elim fun _ hω =>
    hω.2.elim fun e => length_cokernel_residue_of_linearEquiv h hω.1 e W ρ hρ hρex δ hδ

end MMP.Flips

