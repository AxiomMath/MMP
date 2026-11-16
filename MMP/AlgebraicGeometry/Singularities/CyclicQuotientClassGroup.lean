module
public import StacksFrontier.RingTheory.KrullDimension.IntegralExtension
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
public import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
public import MMP.AlgebraicGeometry.Resolution.Blowup.StrictTransform
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechDerivedSupportImmersion
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.RankOneWeilClassSurjective
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.AffineReflexivePowerTilde

/-!
# Formal cyclic quotients and smooth-centre blow-ups

This file collects two results used in the study of threefold singularities.

## Characters classify the divisor classes of a formal cyclic quotient

Let `K` be an algebraically closed field of characteristic zero, `m ≥ 1` and `gcd(q, m) = 1`,
and let `G = μ_m` act on `A = K[[x, y]]` by `ζ · f(x, y) = f(ζx, ζ^q y)`
(`MMP.Flips.cyclicAction`). The invariant ring `R = A^G` (`MMP.Flips.cyclicInvariants`) is a
normal Noetherian local domain of dimension two, `A` is finite over `R`, and over the punctured
spectrum `Spec R ∖ {𝔪}` the cover `Spec A ⟶ Spec R` is a finite étale `G`-torsor: at every
non-maximal prime `𝔭` of `R`, `R_𝔭 → A_𝔭` is étale and the map
`A ⊗_R A → ∏_{g ∈ G} A`, `a ⊗ b ↦ (a · g(b))_g` becomes bijective after localizing at `𝔭`.

The character group `Hom(G, Kˣ)` is identified with the Weil divisor class group
`Cl(T_{m,q})` of `T_{m,q} = Spec R` (`AlgebraicGeometry.weilDivisorClassGroup`) by the
isomorphism sending the character `ζ ↦ ζ` of the semi-invariant `x` to the class of the reduced
image `C^{(1)}_{m,q}` of `(x = 0)`, which is a prime divisor. As that character generates the
cyclic group `Hom(G, Kˣ)` of order `m`, the class `[C^{(1)}_{m,q}]` generates `Cl(T_{m,q})` and
has order `m`.

Since `Cl(T_{m,q})` is killed by `m` and is the group of rank one reflexive modules on `T_{m,q}`
under `ℱ, 𝒢 ↦ (ℱ ⊗ 𝒢)^∨∨` [Stacks, Tag 0EBM], the `m`-th reflexive power of every finite
reflexive `R`-module of rank one is free.

## Main results

* `MMP.Flips.exists_addEquiv_weilDivisorClassGroup_cyclicQuotientModel`: the invariant ring, the
  punctured torsor, and `Hom(μ_m, Kˣ) ≃ Cl(T_{m,q})`.
* `MMP.Flips.nsmul_eq_zero_weilDivisorClassGroup_cyclicQuotientModel`: `Cl(T_{m,q})` is killed
  by `m`.
* `MMP.Flips.nonempty_linearEquiv_reflexivePower_of_nsmul_eq_zero`: over a Noetherian normal
  domain whose class group is killed by `n`, the `n`-th reflexive power of a finite reflexive
  module of rank one is free.
* `MMP.Flips.nsmul_eq_zero_of_nonempty_linearEquiv_reflexivePower`: conversely, if the `n`-th
  reflexive power of every finite reflexive module of rank one is free, the class group is killed
  by `n`.
* `MMP.Flips.weilDivisorClassGroupEquivOfIso`: the class group is invariant under isomorphisms
  of Noetherian integral schemes.
* `MMP.Flips.nsmul_eq_zero_weilDivisorClassGroup_of_ringEquiv`: the class group of any ring
  isomorphic to `R` is killed by `m`.
* `MMP.Flips.nonempty_linearEquiv_reflexivePower_of_ringEquiv`,
  `MMP.Flips.nonempty_linearEquiv_reflexivePower_cyclicInvariants`: the `m`-th reflexive power
  of a finite reflexive rank one module over `R`, or over any ring isomorphic to `R`, is free.
* `MMP.Threefold.Resolution.exists_isSNC_single_exceptional_add_inverseTransformDivisor`: generic
  snc compatibility of the blow-up of a smooth centre with an snc divisor.

## Implementation notes

* The torsor property over the punctured spectrum is stated stalkwise, at the non-maximal primes
  `𝔭` of `R`: the canonical `R`-algebra map `A ⊗_R A → (G → A)` is
  `Algebra.TensorProduct.productMap` of the inclusion `A → (G → A)` of constants and of
  `a ↦ (a(ζx, ζ^q y))_ζ` (each component `MvPowerSeries.rescale (cyclicWeights K m q ζ)`, an
  `R`-algebra map because `R` is fixed), and its localization at `𝔭` is bijective;
  `R_𝔭 → A_𝔭` is étale, with `A_𝔭` the localization of `A` at the image of `R ∖ 𝔭`.
  Finiteness is the stronger global statement that `A` is a finite `R`-module.
* The isomorphism `Hom(G, Kˣ) ≅ Cl(T_{m,q})` is pinned by its value on the character
  `(rootsOfUnity m K).subtype` of `x`: it sends the character of a semi-invariant `f` to the
  class of the divisor whose pull-back is `div(f)`. Since that character generates `Hom(G, Kˣ)`,
  this determines the isomorphism.
* The Weil divisor class group needs `T_{m,q}` integral and locally Noetherian. Integrality comes
  from `R ⊆ K[[x, y]]` having no zero divisors; the Noetherian property of `R` is part of the
  conclusion, so it is the witness of an existential under which the rest is stated.
* The Weil divisor `[C^{(1)}_{m,q}]` is the coefficient family `Pi.single C 1` of the prime
  divisor `C` whose ideal sheaf is the vanishing ideal of the reduced image of `(x = 0)`
  (`MMP.Flips.cyclicQuotientImage`), so that `C.idealSheaf.subscheme` is
  `MMP.Flips.cyclicQuotientCurveOne`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.6
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.31, 0.4(8)
* [Stacks Project, Tag 0EBM](https://stacks.math.columbia.edu/tag/0EBM)
-/

section

universe u w

open AlgebraicGeometry MMP.Flips
open MvPowerSeries
open scoped TensorProduct
open Order CategoryTheory

namespace MMP.Proofs.lem_mmp_formal_cyclic_quotient_character_classes

/-- An invariant series with nonzero constant term has an invariant inverse, so the invariant
ring is local. -/
private theorem isLocalRing_cyclicInvariants (K : Type w) [Field K] (m : ℕ) (q : ℤ) :
    IsLocalRing (cyclicInvariants K m q) := by
  have key : ∀ a : cyclicInvariants K m q,
      MvPowerSeries.constantCoeff (a : MvPowerSeries (Fin 2) K) ≠ 0 → IsUnit a := by
    intro a ha
    have hinv : (a : MvPowerSeries (Fin 2) K)⁻¹ ∈ cyclicInvariants K m q := by
      intro ζ
      have h1 : (a : MvPowerSeries (Fin 2) K) * (a : MvPowerSeries (Fin 2) K)⁻¹ = 1 :=
        MvPowerSeries.mul_inv_cancel _ ha
      have h2 := congrArg (MvPowerSeries.rescale (cyclicWeights K m q ζ)) h1
      rw [map_mul, map_one, (mem_cyclicInvariants_iff K m q _).mp a.2 ζ] at h2
      change MvPowerSeries.rescale (cyclicWeights K m q ζ) _ = _
      calc _ = MvPowerSeries.rescale (cyclicWeights K m q ζ) (a : MvPowerSeries (Fin 2) K)⁻¹ *
            ((a : MvPowerSeries (Fin 2) K) * (a : MvPowerSeries (Fin 2) K)⁻¹) := by rw [h1, mul_one]
        _ = (a : MvPowerSeries (Fin 2) K)⁻¹ := by rw [← mul_assoc, mul_comm _ (a : MvPowerSeries
            (Fin 2) K), h2, one_mul]
    refine IsUnit.of_mul_eq_one (b := ⟨_, hinv⟩) ?_
    exact Subtype.ext (MvPowerSeries.mul_inv_cancel _ ha)
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases ha : MvPowerSeries.constantCoeff (a : MvPowerSeries (Fin 2) K) = 0
  · right
    apply key
    simp [ha]
  · exact Or.inl (key a ha)

section RingTheory

/-- The averaging projection: keep the monomials of weight divisible by `m`. -/
private noncomputable def cyclicAverage (K : Type w) [Field K] (m : ℕ) (q : ℤ)
    (f : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 2) K :=
  fun n => if (m : ℤ) ∣ (n 0 : ℤ) + q * n 1 then coeff n f else 0

private theorem coeff_cyclicAverage (K : Type w) [Field K] (m : ℕ) (q : ℤ)
    (f : MvPowerSeries (Fin 2) K) (n : Fin 2 →₀ ℕ) :
    coeff n (cyclicAverage K m q f) =
      if (m : ℤ) ∣ (n 0 : ℤ) + q * n 1 then coeff n f else 0 := rfl

private theorem cyclicAverage_add (K : Type w) [Field K] (m : ℕ) (q : ℤ)
    (f g : MvPowerSeries (Fin 2) K) :
    cyclicAverage K m q (f + g) = cyclicAverage K m q f + cyclicAverage K m q g := by
  ext n; simp only [coeff_cyclicAverage, map_add]; split_ifs <;> simp

/-- Multiplication by a series supported in weights divisible by `m` commutes with averaging. -/
private theorem cyclicAverage_mul (K : Type w) [Field K] (m : ℕ) (q : ℤ)
    (r f : MvPowerSeries (Fin 2) K)
    (hr : ∀ n : Fin 2 →₀ ℕ, coeff n r ≠ 0 → (m : ℤ) ∣ (n 0 : ℤ) + q * n 1) :
    cyclicAverage K m q (r * f) = r * cyclicAverage K m q f := by
  ext n
  rw [coeff_cyclicAverage, coeff_mul, coeff_mul]
  split_ifs with hn
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hp : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [coeff_cyclicAverage]
    by_cases ha : coeff p.1 r = 0
    · simp [ha]
    have h1 := hr _ ha
    have h2 : (m : ℤ) ∣ (p.2 0 : ℤ) + q * p.2 1 := by
      have e : ((n 0 : ℤ) + q * n 1) = ((p.1 0 : ℤ) + q * p.1 1) + ((p.2 0 : ℤ) + q * p.2 1) := by
        rw [← hp]; simp; ring
      exact (Int.dvd_add_right h1).mp (e ▸ hn)
    simp [h2]
  · symm
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [coeff_cyclicAverage]
    by_cases ha : coeff p.1 r = 0
    · simp [ha]
    have h1 := hr _ ha
    have h2 : ¬ (m : ℤ) ∣ (p.2 0 : ℤ) + q * p.2 1 := by
      intro h2; apply hn
      have e : ((n 0 : ℤ) + q * n 1) = ((p.1 0 : ℤ) + q * p.1 1) + ((p.2 0 : ℤ) + q * p.2 1) := by
        rw [← hp]; simp; ring
      rw [e]; exact dvd_add h1 h2
    simp [h2]

private theorem prod_cyclicWeights_pow (K : Type w) [Field K] (m : ℕ) (q : ℤ) (ζ : rootsOfUnity m K)
    (n : Fin 2 →₀ ℕ) :
    (n.prod fun s k => cyclicWeights K m q ζ s ^ k) =
      (((ζ : Kˣ) ^ ((n 0 : ℤ) + q * n 1) : Kˣ) : K) := by
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simp [Fin.prod_univ_two, cyclicWeights, zpow_add, zpow_mul, zpow_natCast]

/-- The order `m` of the group is nonzero. -/
private theorem neZero_of_isCyclicQuotientSetting {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) : NeZero m :=
  ⟨by have := h.one_le; omega⟩

/-- `μ_m` has a generator. -/
private theorem exists_isPrimitiveRoot_rootsOfUnity {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) : ∃ ζ : rootsOfUnity m K, IsPrimitiveRoot (ζ : Kˣ) m := by
  have := h.isAlgClosed; have := h.charZero
  have := neZero_of_isCyclicQuotientSetting h
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K m
  exact ⟨rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one, by
    rw [← IsPrimitiveRoot.coe_units_iff]; simpa using hζ⟩

private theorem mem_cyclicInvariants_iff_coeff {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) (f : MvPowerSeries (Fin 2) K) :
    f ∈ cyclicInvariants K m q ↔
      ∀ n : Fin 2 →₀ ℕ, coeff n f ≠ 0 → (m : ℤ) ∣ (n 0 : ℤ) + q * n 1 := by
  rw [mem_cyclicInvariants_iff]
  constructor
  · intro hf n hn
    obtain ⟨ζ', hζ'⟩ := exists_isPrimitiveRoot_rootsOfUnity h
    have h1 := congrArg (coeff n) (hf ζ')
    rw [coeff_rescale, prod_cyclicWeights_pow] at h1
    have h2 : (((ζ' : Kˣ) ^ ((n 0 : ℤ) + q * n 1) : Kˣ) : K) = 1 :=
      mul_right_cancel₀ hn (h1.trans (one_mul _).symm)
    exact (hζ'.zpow_eq_one_iff_dvd _).mp (Units.val_eq_one.mp h2)
  · intro hf ζ
    ext n
    rw [coeff_rescale, prod_cyclicWeights_pow]
    by_cases hn : coeff n f = 0
    · simp [hn]
    obtain ⟨k, hk⟩ := hf n hn
    have : ((ζ : Kˣ) ^ ((n 0 : ℤ) + q * n 1)) = 1 := by
      rw [hk, zpow_mul, zpow_natCast]
      simp [(mem_rootsOfUnity _ _).mp ζ.2]
    simp [this]

private theorem cyclicAverage_mem {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) (f : MvPowerSeries (Fin 2) K) :
    cyclicAverage K m q f ∈ cyclicInvariants K m q := by
  rw [mem_cyclicInvariants_iff_coeff h]
  intro n hn
  rw [coeff_cyclicAverage] at hn
  by_contra hc; exact hn (if_neg hc)

private theorem cyclicAverage_eq_self {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) {f : MvPowerSeries (Fin 2) K}
    (hf : f ∈ cyclicInvariants K m q) : cyclicAverage K m q f = f := by
  rw [mem_cyclicInvariants_iff_coeff h] at hf
  ext n
  rw [coeff_cyclicAverage]
  split_ifs with hn
  · rfl
  · by_contra hc; exact hn (hf n (Ne.symm hc))

private theorem comap_map_cyclicInvariants {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) (I : Ideal (cyclicInvariants K m q)) :
    (I.map (cyclicInvariants K m q).subtype).comap (cyclicInvariants K m q).subtype = I := by
  refine le_antisymm (fun x hx => ?_) Ideal.le_comap_map
  have key : ∀ y ∈ I.map (cyclicInvariants K m q).subtype, ∀ a : MvPowerSeries (Fin 2) K,
      ∃ i ∈ I, (i : MvPowerSeries (Fin 2) K) = cyclicAverage K m q (a * y) := by
    intro y hy
    rw [Ideal.map, Ideal.span] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      intro a
      refine ⟨j * ⟨_, cyclicAverage_mem h a⟩, I.mul_mem_right _ hj, ?_⟩
      rw [mul_comm a, cyclicAverage_mul]
      · rfl
      · exact (mem_cyclicInvariants_iff_coeff h _).mp j.2
    | zero =>
      intro a
      refine ⟨0, I.zero_mem, ?_⟩
      ext n; simp [coeff_cyclicAverage]
    | add y z _ _ hy hz =>
      intro a
      obtain ⟨i, hi, hi'⟩ := hy a
      obtain ⟨j, hj, hj'⟩ := hz a
      exact ⟨i + j, I.add_mem hi hj, by rw [mul_add, cyclicAverage_add, ← hi', ← hj']; rfl⟩
    | smul b y _ hy =>
      intro a
      obtain ⟨i, hi, hi'⟩ := hy (a * b)
      exact ⟨i, hi, by rw [hi', smul_eq_mul, mul_assoc]⟩
  obtain ⟨i, hi, hi'⟩ := key _ hx 1
  rw [one_mul, Subring.subtype_apply, cyclicAverage_eq_self h x.2] at hi'
  exact (Subtype.ext hi' : i = x) ▸ hi

private theorem isNoetherianRing_cyclicInvariants {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) : IsNoetherianRing (cyclicInvariants K m q) := by
  have hmono : StrictMono fun I : Ideal (cyclicInvariants K m q) =>
      I.map (cyclicInvariants K m q).subtype := by
    refine Monotone.strictMono_of_injective (fun I J hIJ => Ideal.map_mono hIJ) fun I J hIJ => ?_
    rw [← comap_map_cyclicInvariants h I, ← comap_map_cyclicInvariants h J]
    exact congrArg _ hIJ
  rw [isNoetherianRing_iff, isNoetherian_iff']
  exact hmono.wellFoundedGT

/-- The exponent `(i, j)` as a monomial. -/
private noncomputable abbrev expo (p : ℕ × ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 p.1 + Finsupp.single 1 p.2

/-- The component of `f` in the monomials `x^a y^b` with `a ≡ p.1`, `b ≡ p.2 (mod m)`, divided by
`x^{p.1} y^{p.2}`: a series in `x^m, y^m`. -/
private noncomputable def cyclicComponent (K : Type w) [Field K] (m : ℕ) (p : ℕ × ℕ)
    (f : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 2) K :=
  fun e => if m ∣ e 0 ∧ m ∣ e 1 then coeff (e + expo p) f else 0

private theorem cyclicComponent_mem {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) (p : ℕ × ℕ) (f : MvPowerSeries (Fin 2) K) :
    cyclicComponent K m p f ∈ cyclicInvariants K m q := by
  rw [mem_cyclicInvariants_iff_coeff h]
  intro n hn
  change (if m ∣ n 0 ∧ m ∣ n 1 then _ else _) ≠ 0 at hn
  split_ifs at hn with hd
  · exact dvd_add (Int.natCast_dvd_natCast.mpr hd.1)
      (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hd.2) _)
  · exact absurd rfl hn

private theorem sum_monomial_mul_cyclicComponent {K : Type w} [Field K] {m : ℕ} (hm : 0 < m)
    (f : MvPowerSeries (Fin 2) K) :
    ∑ p ∈ Finset.range m ×ˢ Finset.range m, monomial (expo p) 1 * cyclicComponent K m p f = f := by
  ext n
  rw [map_sum]
  simp only [coeff_monomial_mul, one_mul]
  rw [Finset.sum_eq_single (n 0 % m, n 1 % m)]
  · have hle : expo (n 0 % m, n 1 % m) ≤ n := by
      rw [Finsupp.le_def]; intro i; fin_cases i <;> simp [Nat.mod_le]
    rw [if_pos hle]
    change (if m ∣ (n - expo _) 0 ∧ m ∣ (n - expo _) 1 then _ else _) = _
    rw [if_pos, tsub_add_cancel_of_le hle]
    simp [Nat.dvd_sub_mod]
  · intro p hp hne
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    split_ifs with hle
    · change (if m ∣ (n - expo _) 0 ∧ m ∣ (n - expo _) 1 then _ else _) = _
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

private theorem module_finite_cyclicInvariants {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) :
    Module.Finite (cyclicInvariants K m q) (MvPowerSeries (Fin 2) K) := by
  classical
  have hm : 0 < m := h.one_le
  refine ⟨⟨(Finset.range m ×ˢ Finset.range m).image fun p => monomial (expo p) (1 : K), ?_⟩⟩
  refine eq_top_iff.mpr fun f _ => ?_
  rw [← sum_monomial_mul_cyclicComponent hm f]
  refine Submodule.sum_mem _ fun p hp => ?_
  have := Submodule.smul_mem (Submodule.span (cyclicInvariants K m q)
    (((Finset.range m ×ˢ Finset.range m).image fun p => monomial (expo p) (1 : K)) :
      Set (MvPowerSeries (Fin 2) K)))
    (⟨_, cyclicComponent_mem h p f⟩ : cyclicInvariants K m q)
    (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hp)))
  rwa [Subring.smul_def, smul_eq_mul, mul_comm] at this

private theorem isRegularLocalRing_mvPowerSeries_two (K : Type w) [Field K] :
    IsRegularLocalRing (MvPowerSeries (Fin 2) K) :=
  MvPowerSeries.isRegularLocalRing K 2

private theorem ringKrullDim_cyclicInvariants {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) : ringKrullDim (cyclicInvariants K m q) = 2 := by
  haveI := module_finite_cyclicInvariants h
  rw [Algebra.IsIntegral.ringKrullDim_eq (cyclicInvariants K m q) (MvPowerSeries (Fin 2) K),
    MvPowerSeries.ringKrullDim_eq]
  rfl

private theorem isIntegrallyClosed_cyclicInvariants {K : Type w} [Field K] {m : ℕ} {q : ℤ} :
    letI : IsDomain (cyclicInvariants K m q) := NoZeroDivisors.to_isDomain _
    IsIntegrallyClosed (cyclicInvariants K m q) := by
  letI : IsDomain (cyclicInvariants K m q) := NoZeroDivisors.to_isDomain _
  haveI := isRegularLocalRing_mvPowerSeries_two K
  haveI : IsDomain (MvPowerSeries (Fin 2) K) := IsRegularLocalRing.isDomain _
  haveI : UniqueFactorizationMonoid (MvPowerSeries (Fin 2) K) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  let FA := FractionRing (MvPowerSeries (Fin 2) K)
  let g : (cyclicInvariants K m q) →+* FA := (algebraMap (MvPowerSeries (Fin 2) K) FA).comp
      (cyclicInvariants K m q).subtype
  have hg : Function.Injective g :=
    (IsFractionRing.injective (MvPowerSeries (Fin 2) K) FA).comp Subtype.val_injective
  let φ : FractionRing (cyclicInvariants K m q) →ₐ[(cyclicInvariants K m q)] FA :=
    { IsFractionRing.lift hg with
      commutes' := fun r => IsFractionRing.lift_algebraMap hg r }
  rw [isIntegrallyClosed_iff (FractionRing (cyclicInvariants K m q))]
  intro x hx
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (cyclicInvariants K m q)) x
  have hφ : φ (IsLocalization.mk' (FractionRing (cyclicInvariants K m q)) a b) = g a / g b :=
    IsFractionRing.lift_mk' hg a b
  have hint : IsIntegral (MvPowerSeries (Fin 2) K) (φ (IsLocalization.mk' (FractionRing
      (cyclicInvariants K m q)) a b)) :=
    (hx.map φ).tower_top
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hb0 : g b ≠ 0 := fun h0 => nonZeroDivisors.coe_ne_zero b (hg (h0.trans (map_zero g).symm))
  have hcb : c * (b : (MvPowerSeries (Fin 2) K)) = a := by
    apply IsFractionRing.injective (MvPowerSeries (Fin 2) K) FA
    rw [map_mul, hc, hφ]
    exact div_mul_cancel₀ _ hb0
  have hbA : ((b : (cyclicInvariants K m q)) : (MvPowerSeries (Fin 2) K)) ≠ 0 := fun h0 =>
      nonZeroDivisors.coe_ne_zero b (Subtype.ext h0)
  have hcR : c ∈ (cyclicInvariants K m q) := by
    refine (mem_cyclicInvariants_iff K m q c).mpr fun ζ => ?_
    have e := congrArg (MvPowerSeries.rescale (cyclicWeights K m q ζ)) hcb
    rw [map_mul, (mem_cyclicInvariants_iff K m q _).mp (b : (cyclicInvariants K m q)).2 ζ,
      (mem_cyclicInvariants_iff K m q _).mp a.2 ζ, ← hcb] at e
    exact mul_right_cancel₀ hbA e
  refine ⟨⟨c, hcR⟩, φ.toRingHom.injective ?_⟩
  change φ (algebraMap (cyclicInvariants K m q) (FractionRing (cyclicInvariants K m q)) ⟨c, hcR⟩)
      = _
  rw [φ.commutes]
  change _ = φ (IsLocalization.mk' _ a b)
  rw [← hc, IsScalarTower.algebraMap_apply (cyclicInvariants K m q) (MvPowerSeries (Fin 2) K) FA]
  rfl

end RingTheory

/-- `x^m` and `y^m` are invariant. -/
private theorem X_pow_mem_cyclicInvariants {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) (i : Fin 2) :
    MvPowerSeries.X i ^ m ∈ cyclicInvariants K m q := by
  classical
  rw [mem_cyclicInvariants_iff_coeff h]
  intro n hn
  rw [MvPowerSeries.coeff_X_pow] at hn
  split_ifs at hn with he
  · subst he
    fin_cases i <;> simp
  · exact absurd rfl hn

/-- Every non-maximal prime of the invariant ring misses `x^m` or `y^m`: a prime containing both
lies under a prime of `K[[x, y]]` containing `x` and `y`, which is maximal. -/
private theorem X_pow_notMem_or_of_not_isMaximal {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) (𝔭 : Ideal (cyclicInvariants K m q)) [𝔭.IsPrime]
    (h𝔭 : ¬ 𝔭.IsMaximal) :
    (⟨_, X_pow_mem_cyclicInvariants h 0⟩ : cyclicInvariants K m q) ∉ 𝔭 ∨
      (⟨_, X_pow_mem_cyclicInvariants h 1⟩ : cyclicInvariants K m q) ∉ 𝔭 := by
  haveI := module_finite_cyclicInvariants h
  by_contra hc
  push Not at hc
  obtain ⟨P, -, hP, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔭
    (⊥ : Ideal (MvPowerSeries (Fin 2) K)) (by simp)
  have hX : ∀ i : Fin 2, MvPowerSeries.X i ∈ P := by
    intro i
    refine hP.mem_of_pow_mem m ?_
    have : (algebraMap (cyclicInvariants K m q) (MvPowerSeries (Fin 2) K)
        ⟨_, X_pow_mem_cyclicInvariants h i⟩) ∈ P := by
      rw [← Ideal.mem_comap, ← Ideal.under_def, hPc]
      fin_cases i
      · exact hc.1
      · exact hc.2
    exact this
  have hmax : P.IsMaximal := by
    have hle : IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) K) ≤ P := by
      rw [MvPowerSeries.maximalIdeal_eq_span_range_X, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hX i
    rw [← (IsLocalRing.maximalIdeal.isMaximal _).eq_of_le hP.ne_top hle]
    exact IsLocalRing.maximalIdeal.isMaximal _
  exact h𝔭 (hPc ▸ Ideal.isMaximal_under_of_isIntegral_of_isMaximal P)

section Eigenspaces

/-- The weight-`i` component of `f`: the monomials `x^a y^b` with `a + q b ≡ i (mod m)`. -/
private noncomputable def cyclicWeightComponent (K : Type w) [Field K] (m : ℕ) (q : ℤ)
    (i : ZMod m) (f : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 2) K :=
  fun n => if (((n 0 : ℤ) + q * n 1 : ℤ) : ZMod m) = i then coeff n f else 0

private theorem coeff_cyclicWeightComponent (K : Type w) [Field K] (m : ℕ) (q : ℤ)
    (i : ZMod m) (f : MvPowerSeries (Fin 2) K) (n : Fin 2 →₀ ℕ) :
    coeff n (cyclicWeightComponent K m q i f) =
      if (((n 0 : ℤ) + q * n 1 : ℤ) : ZMod m) = i then coeff n f else 0 := rfl

private theorem sum_cyclicWeightComponent (K : Type w) [Field K] (m : ℕ) [NeZero m] (q : ℤ)
    (f : MvPowerSeries (Fin 2) K) :
    ∑ i : ZMod m, cyclicWeightComponent K m q i f = f := by
  ext n
  rw [map_sum]
  simp only [coeff_cyclicWeightComponent]
  rw [Finset.sum_ite_eq]
  simp

/-- The weight-`i` component is an eigenvector of character `ζ ↦ ζ^i`. -/
private theorem rescale_cyclicWeightComponent (K : Type w) [Field K] (m : ℕ) [NeZero m] (q : ℤ)
    (ζ : rootsOfUnity m K) (i : ZMod m) (f : MvPowerSeries (Fin 2) K) :
    rescale (cyclicWeights K m q ζ) (cyclicWeightComponent K m q i f) =
      C (((ζ : Kˣ) : K) ^ i.val) * cyclicWeightComponent K m q i f := by
  ext n
  rw [coeff_rescale, prod_cyclicWeights_pow, coeff_C_mul, coeff_cyclicWeightComponent]
  split_ifs with hw
  · have hd : (m : ℤ) ∣ ((n 0 : ℤ) + q * n 1) - (i.val : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast at hw ⊢
      rw [hw, ZMod.natCast_zmod_val, sub_self]
    obtain ⟨k, hk⟩ := hd
    have e : (ζ : Kˣ) ^ ((n 0 : ℤ) + q * n 1) = (ζ : Kˣ) ^ i.val := by
      rw [show ((n 0 : ℤ) + q * n 1) = (i.val : ℤ) + m * k by linarith, zpow_add, zpow_mul,
        zpow_natCast, zpow_natCast, (mem_rootsOfUnity _ _).mp ζ.2, one_zpow, mul_one]
    rw [e, Units.val_pow_eq_pow_val]
  · simp

/-- If `u` has character `ζ ↦ ζ`, then `u^{m - i}` times the weight-`i` component is
invariant. -/
private theorem pow_mul_cyclicWeightComponent_mem {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    [NeZero m] {u : MvPowerSeries (Fin 2) K}
    (hu : ∀ ζ : rootsOfUnity m K, MvPowerSeries.rescale (cyclicWeights K m q ζ) u =
      MvPowerSeries.C ((ζ : Kˣ) : K) * u)
    (i : ZMod m) (f : MvPowerSeries (Fin 2) K) :
    u ^ (m - i.val) * cyclicWeightComponent K m q i f ∈ cyclicInvariants K m q := by
  refine (mem_cyclicInvariants_iff K m q _).mpr fun ζ => ?_
  rw [map_mul, map_pow, hu, rescale_cyclicWeightComponent, mul_pow, ← map_pow]
  have e : ((ζ : Kˣ) : K) ^ (m - i.val) * ((ζ : Kˣ) : K) ^ i.val = 1 := by
    rw [← pow_add, Nat.sub_add_cancel (ZMod.val_lt i).le, ← Units.val_pow_eq_pow_val,
      (mem_rootsOfUnity _ _).mp ζ.2, Units.val_one]
  calc _ = C (((ζ : Kˣ) : K) ^ (m - i.val) * ((ζ : Kˣ) : K) ^ i.val) *
        (u ^ (m - i.val) * cyclicWeightComponent K m q i f) := by rw [map_mul]; ring
    _ = _ := by rw [e, map_one, one_mul]

/-- **Eigenspace decomposition after inverting `u`**, for `u` of character `ζ ↦ ζ` (such as
`x`): every series becomes, after multiplication by `u^m`, an `R`-combination of
`1, u, …, u^{m-1}`. -/
private theorem exists_pow_mul_eq_sum {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    [NeZero m] {u : MvPowerSeries (Fin 2) K}
    (hu : ∀ ζ : rootsOfUnity m K, MvPowerSeries.rescale (cyclicWeights K m q ζ) u =
      MvPowerSeries.C ((ζ : Kˣ) : K) * u)
    (f : MvPowerSeries (Fin 2) K) :
    ∃ r : ZMod m → cyclicInvariants K m q,
      u ^ m * f = ∑ i : ZMod m, u ^ i.val * (r i : MvPowerSeries (Fin 2) K) := by
  refine ⟨fun i => ⟨_, pow_mul_cyclicWeightComponent_mem hu i f⟩, ?_⟩
  conv_lhs => rw [← sum_cyclicWeightComponent K m q f]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change _ = u ^ i.val * (u ^ (m - i.val) * _)
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' (ZMod.val_lt i).le]

end Eigenspaces

/-- **Orthogonality of the characters of `μ_m`.** -/
private theorem sum_rootsOfUnity_zpow {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) [Fintype (rootsOfUnity m K)] (k : ℤ) :
    ∑ ζ : rootsOfUnity m K, (((ζ : Kˣ) ^ k : Kˣ) : K) = if (m : ℤ) ∣ k then (m : K) else 0 := by
  classical
  haveI := h.isAlgClosed; haveI := h.charZero
  haveI := neZero_of_isCyclicQuotientSetting h
  split_ifs with hk
  · obtain ⟨j, rfl⟩ := hk
    have : ∀ ζ : rootsOfUnity m K, (((ζ : Kˣ) ^ ((m : ℤ) * j) : Kˣ) : K) = 1 := by
      intro ζ
      rw [zpow_mul, zpow_natCast, (mem_rootsOfUnity _ _).mp ζ.2]; simp
    rw [Finset.sum_congr rfl fun ζ _ => this ζ, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, HasEnoughRootsOfUnity.natCard_rootsOfUnity]
    simp
  · let f : rootsOfUnity m K →* K :=
      (Units.coeHom K).comp ((zpowGroupHom k).comp (rootsOfUnity m K).subtype)
    refine sum_hom_units_eq_zero f fun hf => hk ?_
    obtain ⟨ζ', hζ'⟩ := exists_isPrimitiveRoot_rootsOfUnity h
    have e := DFunLike.congr_fun hf ζ'
    refine (hζ'.zpow_eq_one_iff_dvd k).mp (Units.val_eq_one.mp ?_)
    simpa [f] using e

open scoped Classical in
/-- The geometric sum of a root of unity. -/
private theorem sum_range_rootsOfUnity_pow {K : Type w} [Field K] {m : ℕ}
    (ω : rootsOfUnity m K) :
    ∑ j ∈ Finset.range m, ((ω : Kˣ) : K) ^ j = if ω = 1 then (m : K) else 0 := by
  split_ifs with hω
  · simp [hω]
  · have h1 : ((ω : Kˣ) : K) - 1 ≠ 0 := by
      rw [sub_ne_zero]
      intro e; apply hω
      exact Subtype.ext (Units.ext (by simpa using e))
    have h2 := geom_sum_mul ((ω : Kˣ) : K) m
    rw [show ((ω : Kˣ) : K) ^ m = 1 by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp ω.2, Units.val_one], sub_self]
      at h2
    exact (mul_eq_zero.mp h2).resolve_right h1

/-- The weight of `x` is the root of unity itself. -/
private theorem rescale_X_zero_pow (K : Type w) [Field K] (m : ℕ) (q : ℤ) (ζ : rootsOfUnity m K)
    (j : ℕ) : MvPowerSeries.rescale (cyclicWeights K m q ζ) (MvPowerSeries.X 0 ^ j) =
      MvPowerSeries.C (((ζ : Kˣ) : K) ^ j) * MvPowerSeries.X 0 ^ j := by
  classical
  ext n
  rw [MvPowerSeries.coeff_rescale, prod_cyclicWeights_pow, MvPowerSeries.coeff_C_mul,
    MvPowerSeries.coeff_X_pow]
  split_ifs with hn
  · subst hn; simp
  · simp

/-- The coordinates are nonzero. -/
private theorem X_ne_zero (K : Type w) [Field K] (i : Fin 2) :
    (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) ≠ 0 := fun e => by
  classical
  simpa [MvPowerSeries.coeff_X] using congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) e

/-- Powers of a series of character `ζ ↦ ζ`. -/
private theorem rescale_pow_of_rescale_eq {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    {u : MvPowerSeries (Fin 2) K}
    (hu : ∀ ζ : rootsOfUnity m K, MvPowerSeries.rescale (cyclicWeights K m q ζ) u =
      MvPowerSeries.C ((ζ : Kˣ) : K) * u)
    (ζ : rootsOfUnity m K) (j : ℕ) :
    MvPowerSeries.rescale (cyclicWeights K m q ζ) (u ^ j) =
      MvPowerSeries.C (((ζ : Kˣ) : K) ^ j) * u ^ j := by
  rw [map_pow, hu, mul_pow, ← map_pow]

/-- The `m`-th power of a series of character `ζ ↦ ζ` is invariant. -/
private theorem pow_mem_cyclicInvariants_of_rescale_eq {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    {u : MvPowerSeries (Fin 2) K}
    (hu : ∀ ζ : rootsOfUnity m K, MvPowerSeries.rescale (cyclicWeights K m q ζ) u =
      MvPowerSeries.C ((ζ : Kˣ) : K) * u) :
    u ^ m ∈ cyclicInvariants K m q := by
  refine (mem_cyclicInvariants_iff K m q _).mpr fun ζ => ?_
  rw [rescale_pow_of_rescale_eq hu, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp ζ.2,
    Units.val_one, map_one, one_mul]

/-- The map `A ⊗_R A → ∏_{μ_m} A`, `a ⊗ b ↦ (a · ζ(b))_ζ`, of the torsor. -/
private noncomputable def cyclicTorsorMap (K : Type w) [Field K] (m : ℕ) (q : ℤ) :
    MvPowerSeries (Fin 2) K ⊗[cyclicInvariants K m q] MvPowerSeries (Fin 2) K →ₐ[cyclicInvariants
        K m q]
      (rootsOfUnity m K → MvPowerSeries (Fin 2) K) :=
  Algebra.TensorProduct.productMap
    ((Algebra.ofId (MvPowerSeries (Fin 2) K)
      (rootsOfUnity m K → MvPowerSeries (Fin 2) K)).restrictScalars (cyclicInvariants K m q))
    (Pi.algHom (cyclicInvariants K m q) (fun _ : rootsOfUnity m K => MvPowerSeries (Fin 2) K)
      fun ζ => AlgHom.mk (MvPowerSeries.rescale (cyclicWeights K m q ζ))
        fun r => (mem_cyclicInvariants_iff K m q r).mp r.2 ζ)

private theorem cyclicTorsorMap_tmul (K : Type w) [Field K] (m : ℕ) (q : ℤ)
    (a b : MvPowerSeries (Fin 2) K) (ζ : rootsOfUnity m K) :
    cyclicTorsorMap K m q (a ⊗ₜ b) ζ = a * MvPowerSeries.rescale (cyclicWeights K m q ζ) b := by
  rw [cyclicTorsorMap, Algebra.TensorProduct.productMap_apply_tmul]
  rfl

open scoped Classical in
/-- **The cokernel of the torsor map is killed by `x^m`.** -/
private theorem exists_cyclicTorsorMap_eq_pow_mul {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) [Fintype (rootsOfUnity m K)]
    {u : MvPowerSeries (Fin 2) K}
    (hu : ∀ ζ : rootsOfUnity m K, MvPowerSeries.rescale (cyclicWeights K m q ζ) u =
      MvPowerSeries.C ((ζ : Kˣ) : K) * u)
    (v : rootsOfUnity m K → MvPowerSeries (Fin 2) K) :
    ∃ t, cyclicTorsorMap K m q t = fun ζ => u ^ m * v ζ := by
  haveI := h.charZero
  refine ⟨∑ ζ₀ : rootsOfUnity m K, ∑ j ∈ Finset.range m,
    (MvPowerSeries.C ((m : K)⁻¹ * ((ζ₀⁻¹ : rootsOfUnity m K) : Kˣ) ^ j) * v ζ₀ *
      u ^ (m - j)) ⊗ₜ (u ^ j), ?_⟩
  funext ζ
  simp only [map_sum, Finset.sum_apply]
  have hterm : ∀ ζ₀ : rootsOfUnity m K, ∀ j ∈ Finset.range m,
      MvPowerSeries.C ((m : K)⁻¹ * ((ζ₀⁻¹ : rootsOfUnity m K) : Kˣ) ^ j) * v ζ₀ *
        u ^ (m - j) * (MvPowerSeries.C (((ζ : Kˣ) : K) ^ j) *
          u ^ j) =
      MvPowerSeries.C ((m : K)⁻¹ * ((((ζ₀⁻¹ * ζ : rootsOfUnity m K) : Kˣ) : K) ^ j)) *
        (u ^ m * v ζ₀) := by
    intro ζ₀ j hj
    have hj : j ≤ m := (Finset.mem_range.mp hj).le
    have hX : u ^ (m - j) * u ^ j =
        u ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hj]
    have hc : (m : K)⁻¹ * ((((ζ₀⁻¹ * ζ : rootsOfUnity m K) : Kˣ) : K) ^ j) =
        (m : K)⁻¹ * (((ζ₀⁻¹ : rootsOfUnity m K) : Kˣ) : K) ^ j * (((ζ : Kˣ) : K) ^ j) := by
      push_cast; rw [mul_pow]; ring
    rw [hc, ← hX]
    simp only [map_mul]
    ring
  have key : ∀ ζ₀ : rootsOfUnity m K, ∀ j ∈ Finset.range m,
      cyclicTorsorMap K m q ((MvPowerSeries.C ((m : K)⁻¹ * ((ζ₀⁻¹ : rootsOfUnity m K) : Kˣ) ^ j) *
        v ζ₀ * u ^ (m - j)) ⊗ₜ (u ^ j)) ζ =
      MvPowerSeries.C ((m : K)⁻¹ * ((((ζ₀⁻¹ * ζ : rootsOfUnity m K) : Kˣ) : K) ^ j)) *
        (u ^ m * v ζ₀) := fun ζ₀ j hj => by
    rw [← hterm ζ₀ j hj, ← rescale_pow_of_rescale_eq hu ζ j]; rfl
  rw [Finset.sum_congr rfl fun ζ₀ _ => Finset.sum_congr rfl (key ζ₀)]
  simp only [← Finset.sum_mul, ← map_sum, ← Finset.mul_sum, sum_range_rootsOfUnity_pow]
  rw [Finset.sum_eq_single ζ]
  · rw [if_pos (inv_mul_cancel ζ), inv_mul_cancel₀ (Nat.cast_ne_zero.mpr
      (by have := h.one_le; omega)), map_one, one_mul]
  · intro ζ₀ _ hne
    rw [if_neg (fun e => hne (inv_mul_eq_one.mp e)), mul_zero, map_zero, zero_mul]
  · intro hn; exact absurd (Finset.mem_univ _) hn

/-- After multiplication by `x^m`, every tensor is `∑_{i<m} c_i ⊗ x^i`. -/
private theorem exists_smul_eq_sum_tmul {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    [NeZero m] {u : MvPowerSeries (Fin 2) K}
    (hu : ∀ ζ : rootsOfUnity m K, MvPowerSeries.rescale (cyclicWeights K m q ζ) u =
      MvPowerSeries.C ((ζ : Kˣ) : K) * u)
    (t : MvPowerSeries (Fin 2) K ⊗[cyclicInvariants K m q] MvPowerSeries (Fin 2) K) :
    ∃ c : ZMod m → MvPowerSeries (Fin 2) K,
      (⟨u ^ m, pow_mem_cyclicInvariants_of_rescale_eq hu⟩ : cyclicInvariants K m q) • t =
        ∑ i : ZMod m, c i ⊗ₜ (u ^ i.val) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a b =>
    obtain ⟨r, hr⟩ := exists_pow_mul_eq_sum hu b
    refine ⟨fun i => r i • a, ?_⟩
    rw [← TensorProduct.tmul_smul, Subring.smul_def, smul_eq_mul]
    change a ⊗ₜ (u ^ m * b) = _
    rw [hr, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul, Subring.smul_def, smul_eq_mul, mul_comm]
  | add x y hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, by rw [smul_add, hc, hd, ← Finset.sum_add_distrib]; simp [TensorProduct.add_tmul]⟩

/-- **Orthogonality of the eigencomponents**: if `∑_i ζ^i c_i u^i = 0` for every `ζ ∈ μ_m`, with
`u ≠ 0`, then every `c_i` vanishes. -/
private theorem eq_zero_of_forall_sum_rescale_eq_zero {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) [Fintype (rootsOfUnity m K)] [NeZero m]
    {u : MvPowerSeries (Fin 2) K} (hu0 : u ≠ 0) (c : ZMod m → MvPowerSeries (Fin 2) K)
    (hΦ : ∀ ζ : rootsOfUnity m K,
      ∑ i : ZMod m, MvPowerSeries.C (((ζ : Kˣ) : K) ^ i.val) * (c i * u ^ i.val) = 0) :
    ∀ k : ZMod m, c k = 0 := by
  haveI := h.charZero
  intro k
  have hsum : ∑ ζ : rootsOfUnity m K, MvPowerSeries.C ((((ζ : Kˣ) ^ (-(k.val : ℤ)) : Kˣ) : K)) *
      ∑ i : ZMod m, MvPowerSeries.C (((ζ : Kˣ) : K) ^ i.val) *
        (c i * u ^ i.val) = 0 := by
    simp only [hΦ, mul_zero, Finset.sum_const_zero]
  simp only [Finset.mul_sum, ← mul_assoc, ← map_mul] at hsum
  rw [Finset.sum_comm] at hsum
  simp only [← Finset.sum_mul, ← map_sum] at hsum
  have hpow : ∀ (ζ : rootsOfUnity m K) (i : ZMod m),
      (((ζ : Kˣ) ^ (-(k.val : ℤ)) : Kˣ) : K) * ((ζ : Kˣ) : K) ^ i.val =
        (((ζ : Kˣ) ^ ((i.val : ℤ) - k.val) : Kˣ) : K) := by
    intro ζ i
    rw [sub_eq_neg_add, zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
  simp only [hpow, sum_rootsOfUnity_zpow h] at hsum
  rw [Finset.sum_eq_single k] at hsum
  · rw [if_pos (by simp)] at hsum
    rcases mul_eq_zero.mp hsum with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 fun e => (Nat.cast_ne_zero.mpr (NeZero.ne m) : (m : K) ≠ 0)
          (MvPowerSeries.C_injective (e.trans (map_zero _).symm))
      · exact h2
    · exact absurd h1 (pow_ne_zero _ hu0)
  · intro i _ hik
    rw [if_neg, map_zero, zero_mul, zero_mul]
    intro hd
    apply hik
    rw [← ZMod.natCast_zmod_val i, ← ZMod.natCast_zmod_val k]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr hd
    push_cast at this
    exact (sub_eq_zero.mp this)
  · intro hk; exact absurd (Finset.mem_univ _) hk

/-- **The kernel of the torsor map is killed by `x^m`.** -/
private theorem smul_eq_zero_of_cyclicTorsorMap_eq_zero {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) [Fintype (rootsOfUnity m K)]
    {u : MvPowerSeries (Fin 2) K}
    (hu : ∀ ζ : rootsOfUnity m K, MvPowerSeries.rescale (cyclicWeights K m q ζ) u =
      MvPowerSeries.C ((ζ : Kˣ) : K) * u) (hu0 : u ≠ 0)
    (t : MvPowerSeries (Fin 2) K ⊗[cyclicInvariants K m q] MvPowerSeries (Fin 2) K)
    (ht : cyclicTorsorMap K m q t = 0) :
    (⟨u ^ m, pow_mem_cyclicInvariants_of_rescale_eq hu⟩ : cyclicInvariants K m q) • t = 0 := by
  haveI := h.charZero
  haveI := neZero_of_isCyclicQuotientSetting h
  obtain ⟨c, hc⟩ := exists_smul_eq_sum_tmul hu t
  have hΦ : ∀ ζ : rootsOfUnity m K,
      ∑ i : ZMod m, MvPowerSeries.C (((ζ : Kˣ) : K) ^ i.val) *
        (c i * u ^ i.val) = 0 := by
    intro ζ
    have e := congrFun (congrArg (cyclicTorsorMap K m q) hc) ζ
    rw [map_smul, ht, smul_zero, map_sum, Finset.sum_apply] at e
    refine (Eq.trans (Finset.sum_congr rfl fun i _ => ?_) e.symm)
    rw [cyclicTorsorMap_tmul, rescale_pow_of_rescale_eq hu]; ring
  have hc0 : ∀ k : ZMod m, c k = 0 := eq_zero_of_forall_sum_rescale_eq_zero h hu0 c hΦ
  rw [hc]
  simp [hc0]

/-- A linear map whose kernel and cokernel are killed by an element `s` of `S` becomes bijective
after localizing at `S`. -/
private theorem bijective_localizedModuleMap_of_smul {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (S : Submonoid R)
    (f : M →ₗ[R] N) {s : R} (hs : s ∈ S) (hker : ∀ z, f z = 0 → s • z = 0)
    (hcok : ∀ w, ∃ z, f z = s • w) : Function.Bijective (LocalizedModule.map S f) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_, fun x => ?_⟩
  · induction x using LocalizedModule.induction_on with
    | h z t =>
      rw [LocalizedModule.map_mk, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hx
      obtain ⟨u, hu⟩ := hx
      rw [smul_zero, smul_zero, one_smul, Submonoid.smul_def, ← map_smul] at hu
      have h1 := hker _ hu
      rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
      refine ⟨⟨s, hs⟩ * u, ?_⟩
      rw [smul_zero, smul_zero, one_smul, Submonoid.smul_def, Submonoid.coe_mul, mul_smul]
      exact h1
  · induction x using LocalizedModule.induction_on with
    | h w t =>
      obtain ⟨z, hz⟩ := hcok w
      refine ⟨LocalizedModule.mk z (⟨s, hs⟩ * t), ?_⟩
      rw [LocalizedModule.map_mk, hz]
      exact LocalizedModule.mk_cancel_common_left ⟨s, hs⟩ t w

/-- **The torsor map is bijective over the chart `u ≠ 0`**, for `u ≠ 0` of character `ζ ↦ ζ`. -/
private theorem bijective_localizedModuleMap_cyclicTorsorMap_of_pow {K : Type w} [Field K]
    {m : ℕ} {q : ℤ} (h : IsCyclicQuotientSetting K m q) (𝔭 : Ideal (cyclicInvariants K m q))
    [𝔭.IsPrime] {u : MvPowerSeries (Fin 2) K}
    (hu : ∀ ζ : rootsOfUnity m K, MvPowerSeries.rescale (cyclicWeights K m q ζ) u =
      MvPowerSeries.C ((ζ : Kˣ) : K) * u) (hu0 : u ≠ 0)
    (hs : (⟨u ^ m, pow_mem_cyclicInvariants_of_rescale_eq hu⟩ : cyclicInvariants K m q) ∉ 𝔭) :
    Function.Bijective
      (LocalizedModule.map 𝔭.primeCompl (cyclicTorsorMap K m q).toLinearMap) := by
  haveI := neZero_of_isCyclicQuotientSetting h
  haveI := Fintype.ofFinite (rootsOfUnity m K)
  refine bijective_localizedModuleMap_of_smul _ _ hs
    (fun z hz => smul_eq_zero_of_cyclicTorsorMap_eq_zero h hu hu0 z hz)
    (exists_cyclicTorsorMap_eq_pow_mul h hu)

/-- `y^{q'}`, with `q q' ≡ 1 (mod m)`, has the character `ζ ↦ ζ` of `x`. -/
private theorem exists_rescale_X_one_pow {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) :
    ∃ q' : ℕ, ∀ ζ : rootsOfUnity m K,
      MvPowerSeries.rescale (cyclicWeights K m q ζ) (MvPowerSeries.X 1 ^ q') =
        MvPowerSeries.C ((ζ : Kˣ) : K) * MvPowerSeries.X 1 ^ q' := by
  have hm : (m : ℤ) ≠ 0 := by have := h.one_le; omega
  set a := Int.gcdA q m
  have hg : (1 : ℤ) = q * a + m * Int.gcdB q m := by
    rw [← Int.gcd_eq_gcd_ab, h.gcd_eq_one, Nat.cast_one]
  set q' := (a % m).toNat
  have hq' : (q' : ℤ) = a - m * (a / m) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm), Int.emod_def]
  have hd : q * q' = 1 + m * (-(Int.gcdB q m + q * (a / m))) := by
    linear_combination q * hq' - hg
  refine ⟨q', fun ζ => ?_⟩
  classical
  have e : (ζ : Kˣ) ^ (q * q') = ζ := by
    rw [hd, zpow_add, zpow_one, zpow_mul, zpow_natCast, (mem_rootsOfUnity _ _).mp ζ.2,
      one_zpow, mul_one]
  ext n
  rw [MvPowerSeries.coeff_rescale, prod_cyclicWeights_pow, MvPowerSeries.coeff_C_mul,
    MvPowerSeries.coeff_X_pow]
  split_ifs with hn
  · subst hn
    simp [e]
  · simp

/-- **Charts of the punctured spectrum.** A non-maximal prime of `R` misses `u^m` for some
`u ≠ 0` of character `ζ ↦ ζ`: either `u = x`, or `u = y^{q'}` with `q q' ≡ 1 (mod m)`. -/
private theorem exists_chart_of_not_isMaximal {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) (𝔭 : Ideal (cyclicInvariants K m q)) [𝔭.IsPrime]
    (h𝔭 : ¬ 𝔭.IsMaximal) :
    ∃ (u : MvPowerSeries (Fin 2) K)
      (hu : ∀ ζ : rootsOfUnity m K, MvPowerSeries.rescale (cyclicWeights K m q ζ) u =
        MvPowerSeries.C ((ζ : Kˣ) : K) * u), u ≠ 0 ∧
      (⟨u ^ m, pow_mem_cyclicInvariants_of_rescale_eq hu⟩ : cyclicInvariants K m q) ∉ 𝔭 := by
  rcases X_pow_notMem_or_of_not_isMaximal h 𝔭 h𝔭 with hx | hy
  · exact ⟨_, fun ζ => by simpa using rescale_X_zero_pow K m q ζ 1, X_ne_zero K _, hx⟩
  · obtain ⟨q', hu⟩ := exists_rescale_X_one_pow h
    refine ⟨_, hu, pow_ne_zero _ (X_ne_zero K _), fun hmem => hy ?_⟩
    refine (‹𝔭.IsPrime›).mem_of_pow_mem q' ?_
    convert hmem using 1
    ext1
    simp only [SubmonoidClass.coe_pow]
    rw [← pow_mul, ← pow_mul, mul_comm]

/-- **A Kummer algebra is étale.** If `S` is free over `R` with basis `1, ξ, …, ξ^{m-1}`, where
`ξ^m = v` for a unit `v` and `m` is invertible in `R`, then `S ≅ R[z]/(z^m - v)` is standard
étale over `R`. -/
private theorem etale_of_basis_pow {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Nontrivial R] {m : ℕ} (hm : m ≠ 0) (hmu : IsUnit (m : R)) {v : R} (hv : IsUnit v) (ξ : S)
    (hξ : ξ ^ m = algebraMap R S v)
    (hli : LinearIndependent R (fun i : Fin m => ξ ^ (i : ℕ)))
    (hsp : ⊤ ≤ Submodule.span R (Set.range (fun i : Fin m => ξ ^ (i : ℕ)))) :
    Algebra.Etale R S := by
  have hmon : (Polynomial.X ^ m - Polynomial.C v : Polynomial R).Monic :=
    Polynomial.monic_X_pow_sub_C v hm
  let P : StandardEtalePair R :=
    { f := Polynomial.X ^ m - Polynomial.C v
      monic_f := hmon
      g := 1
      cond := by
        obtain ⟨μ, hμ⟩ := hmu
        obtain ⟨ν, hν⟩ := hv
        refine ⟨Polynomial.C (↑(μ * ν)⁻¹ : R) * Polynomial.X, -Polynomial.C (↑ν⁻¹ : R), 0, ?_⟩
        rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
          sub_zero, pow_zero]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
        simp only [Nat.succ_sub_one, Nat.cast_succ]
        have e1 : ((k : R) + 1) * (↑(μ * ν)⁻¹ : R) = ↑ν⁻¹ := by
          rw [← Nat.cast_succ, ← hμ, mul_inv_rev, Units.val_mul, mul_comm (↑ν⁻¹ : R), ← mul_assoc,
            Units.mul_inv, one_mul]
        have e2 : v * (↑ν⁻¹ : R) = 1 := by rw [← hν, Units.mul_inv]
        calc Polynomial.C ((k : R) + 1) * Polynomial.X ^ k *
                (Polynomial.C (↑(μ * ν)⁻¹ : R) * Polynomial.X) +
              (Polynomial.X ^ (k + 1) - Polynomial.C v) * -Polynomial.C (↑ν⁻¹ : R)
            = Polynomial.C (((k : R) + 1) * (↑(μ * ν)⁻¹ : R)) * Polynomial.X ^ (k + 1) -
                Polynomial.C (↑ν⁻¹ : R) * Polynomial.X ^ (k + 1)
              + Polynomial.C (v * (↑ν⁻¹ : R)) := by simp only [map_mul, pow_succ]; ring
          _ = 1 := by rw [e1, e2, sub_self, zero_add, map_one] }
  have hroot : Polynomial.eval₂ ((Algebra.ofId R S : R →ₐ[R] S) : R →+* S) ξ
      (Polynomial.X ^ m - Polynomial.C v) = 0 := by
    simp [hξ]
  let ψ : AdjoinRoot (Polynomial.X ^ m - Polynomial.C v) →ₐ[R] S :=
    AdjoinRoot.liftAlgHom (Polynomial.X ^ m - Polynomial.C v) (Algebra.ofId R S) ξ hroot
  have hψr : ψ (AdjoinRoot.root _) = ξ := AdjoinRoot.liftAlgHom_root _ _ _ hroot
  let pb := AdjoinRoot.powerBasis' hmon
  have hdim : pb.dim = m := by
    rw [AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_X_pow_sub_C]
  let bS := Module.Basis.mk hli hsp
  have hψ : ψ.toLinearMap = (pb.basis.equiv bS (finCongr hdim)).toLinearMap := by
    refine pb.basis.ext fun i => ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Module.Basis.mk_apply, PowerBasis.coe_basis]
    simp only [AlgHom.toLinearMap_apply, map_pow, pb, AdjoinRoot.powerBasis'_gen, hψr]
    simp
  have hbij : Function.Bijective ψ := by
    have : (ψ : AdjoinRoot _ → S) = pb.basis.equiv bS (finCongr hdim) :=
      congrArg DFunLike.coe hψ
    rw [this]; exact (pb.basis.equiv bS (finCongr hdim)).bijective
  have : IsLocalization.Away (AdjoinRoot.mk P.f P.g) (AdjoinRoot P.f) :=
    IsLocalization.away_of_isUnit_of_bijective _ (by simp [P]) Function.bijective_id
  let e3 : Localization.Away (AdjoinRoot.mk P.f P.g) ≃ₐ[R] AdjoinRoot P.f :=
    (IsLocalization.algEquiv (Submonoid.powers (AdjoinRoot.mk P.f P.g)) _ _).restrictScalars R
  have : Algebra.IsStandardEtale R S :=
    Algebra.IsStandardEtale.of_equiv ((P.equivAwayAdjoinRoot.trans e3).trans
      (AlgEquiv.ofBijective ψ hbij))
  infer_instance

/-- `m` is a unit of the invariant ring: its inverse is the constant series `1/m`. -/
private theorem isUnit_natCast_cyclicInvariants {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) : IsUnit (m : cyclicInvariants K m q) := by
  have := h.charZero
  have hm : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr (by have := h.one_le; omega)
  have hmem : MvPowerSeries.C (m : K)⁻¹ ∈ cyclicInvariants K m q := by
    rw [mem_cyclicInvariants_iff_coeff h]
    intro n hn
    rw [MvPowerSeries.coeff_C] at hn
    split_ifs at hn with h0
    · subst h0; simp
    · exact absurd rfl hn
  refine IsUnit.of_mul_eq_one (b := ⟨_, hmem⟩) (Subtype.ext ?_)
  change ((m : cyclicInvariants K m q) : MvPowerSeries (Fin 2) K) * MvPowerSeries.C (m : K)⁻¹ = 1
  rw [Subring.coe_natCast, ← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := K)), ← map_mul,
    mul_inv_cancel₀ hm, map_one]

/-- **The cover is étale over the chart `u ≠ 0`**, for `u ≠ 0` of character `ζ ↦ ζ`: there
`A_𝔭` is free over `R_𝔭` with basis `1, u, …, u^{m-1}` and `u^m` is a unit, so
`A_𝔭 = R_𝔭[z]/(z^m - u^m)`. -/
private theorem etale_localization_of_pow {K : Type w} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) (𝔭 : Ideal (cyclicInvariants K m q)) [𝔭.IsPrime]
    {u : MvPowerSeries (Fin 2) K}
    (hu : ∀ ζ : rootsOfUnity m K, MvPowerSeries.rescale (cyclicWeights K m q ζ) u =
      MvPowerSeries.C ((ζ : Kˣ) : K) * u) (hu0 : u ≠ 0)
    (hs : (⟨u ^ m, pow_mem_cyclicInvariants_of_rescale_eq hu⟩ : cyclicInvariants K m q) ∉ 𝔭) :
    Algebra.Etale (Localization.AtPrime 𝔭)
      (Localization (Algebra.algebraMapSubmonoid (MvPowerSeries (Fin 2) K) 𝔭.primeCompl)) := by
  have := neZero_of_isCyclicQuotientSetting h
  have := Fintype.ofFinite (rootsOfUnity m K)
  set um : cyclicInvariants K m q := ⟨u ^ m, pow_mem_cyclicInvariants_of_rescale_eq hu⟩ with hum
  have hRA : ∀ x : cyclicInvariants K m q,
      algebraMap (Localization.AtPrime 𝔭)
        (Localization (Algebra.algebraMapSubmonoid (MvPowerSeries (Fin 2) K) 𝔭.primeCompl))
        (algebraMap (cyclicInvariants K m q) (Localization.AtPrime 𝔭) x) =
      algebraMap (MvPowerSeries (Fin 2) K)
        (Localization (Algebra.algebraMapSubmonoid (MvPowerSeries (Fin 2) K) 𝔭.primeCompl))
        (x : MvPowerSeries (Fin 2) K) := fun x => by
    rw [← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (cyclicInvariants K m q) (MvPowerSeries (Fin 2) K)]
    rfl
  set ξ := algebraMap (MvPowerSeries (Fin 2) K)
    (Localization (Algebra.algebraMapSubmonoid (MvPowerSeries (Fin 2) K) 𝔭.primeCompl)) u
    with hξdef
  have hinj : Function.Injective (algebraMap (MvPowerSeries (Fin 2) K)
      (Localization (Algebra.algebraMapSubmonoid (MvPowerSeries (Fin 2) K) 𝔭.primeCompl))) := by
    refine IsLocalization.injective (M := Algebra.algebraMapSubmonoid (MvPowerSeries (Fin 2) K)
      𝔭.primeCompl) _ (le_nonZeroDivisors_of_noZeroDivisors ?_)
    rintro ⟨t, ht, ht0⟩
    have : t = 0 := Subtype.ext ht0
    exact ht (this ▸ 𝔭.zero_mem)
  let e : Fin m ≃ ZMod m :=
    { toFun := fun i => (i : ℕ)
      invFun := fun k => ⟨k.val, ZMod.val_lt k⟩
      left_inv := fun i => Fin.ext (by simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.2])
      right_inv := fun k => by simp }
  have he : ∀ i : Fin m, (e i).val = i := fun i => by
    simp [e, ZMod.val_natCast, Nat.mod_eq_of_lt i.2]
  refine etale_of_basis_pow (NeZero.ne m) ?_
    (IsLocalization.map_units (Localization.AtPrime 𝔭) (⟨um, hs⟩ : 𝔭.primeCompl)) ξ ?_ ?_ ?_
  · rw [← map_natCast (algebraMap (cyclicInvariants K m q) (Localization.AtPrime 𝔭))]
    exact (isUnit_natCast_cyclicInvariants h).map _
  · rw [hRA, hξdef, ← map_pow]
  · rw [Fintype.linearIndependent_iff]
    intro g hg j
    obtain ⟨⟨t, ht⟩, hint⟩ :=
      IsLocalization.exist_integer_multiples 𝔭.primeCompl (Finset.univ : Finset (Fin m)) g
    choose r hr using fun i => hint i (Finset.mem_univ i)
    have hsum : (∑ i : Fin m, (r i : MvPowerSeries (Fin 2) K) * u ^ (i : ℕ)) = 0 := by
      apply hinj
      rw [map_zero, map_sum]
      have := congrArg (fun z => algebraMap (Localization.AtPrime 𝔭)
        (Localization (Algebra.algebraMapSubmonoid (MvPowerSeries (Fin 2) K) 𝔭.primeCompl))
        (algebraMap (cyclicInvariants K m q) (Localization.AtPrime 𝔭) t) * z) hg
      simp only [mul_zero, Finset.mul_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, ← hRA, hr i, Algebra.smul_def, Algebra.smul_def, map_mul, ← hξdef]
      ring
    have hΦ : ∀ ζ : rootsOfUnity m K, ∑ k : ZMod m, MvPowerSeries.C (((ζ : Kˣ) : K) ^ k.val) *
        ((r (e.symm k) : MvPowerSeries (Fin 2) K) * u ^ k.val) = 0 := by
      intro ζ
      have h1 := congrArg (MvPowerSeries.rescale (cyclicWeights K m q ζ)) hsum
      rw [map_zero, map_sum] at h1
      rw [← h1, ← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, (mem_cyclicInvariants_iff K m q _).mp (r i).2 ζ,
        rescale_pow_of_rescale_eq hu, Equiv.symm_apply_apply, he]
      ring
    have h0 := eq_zero_of_forall_sum_rescale_eq_zero h hu0 _ hΦ (e j)
    rw [Equiv.symm_apply_apply] at h0
    have hrj : r j = 0 := Subtype.ext h0
    have := hr j
    rw [hrj, map_zero, Algebra.smul_def] at this
    exact ((IsLocalization.map_units (Localization.AtPrime 𝔭)
      (⟨t, ht⟩ : 𝔭.primeCompl)).mul_right_eq_zero).mp this.symm
  · rintro y -
    obtain ⟨⟨a, s⟩, hy⟩ := IsLocalization.mk'_surjective
      (Algebra.algebraMapSubmonoid (MvPowerSeries (Fin 2) K) 𝔭.primeCompl) y
    rw [← hy]
    change IsLocalization.mk' _ a s ∈ _
    obtain ⟨t, ht, hts⟩ := s.2
    obtain ⟨r, hr⟩ := exists_pow_mul_eq_sum hu a
    have htu : t * um ∈ 𝔭.primeCompl := 𝔭.primeCompl.mul_mem ht hs
    have key : IsLocalization.mk' _ a s =
        ∑ k : ZMod m, IsLocalization.mk' (Localization.AtPrime 𝔭) (r k) ⟨t * um, htu⟩ •
          ξ ^ k.val := by
      have hunit := IsLocalization.map_units
        (Localization (Algebra.algebraMapSubmonoid (MvPowerSeries (Fin 2) K) 𝔭.primeCompl))
        (⟨_, Algebra.mem_algebraMapSubmonoid_of_mem (⟨t * um, htu⟩ : 𝔭.primeCompl)⟩ :
          Algebra.algebraMapSubmonoid (MvPowerSeries (Fin 2) K) 𝔭.primeCompl)
      refine hunit.mul_left_inj.mp ?_
      simp only [Finset.sum_mul, Algebra.smul_def]
      have hts' : (algebraMap (cyclicInvariants K m q) (MvPowerSeries (Fin 2) K) (t * um)) =
          (s : MvPowerSeries (Fin 2) K) * u ^ m := by
        rw [map_mul, hts]; rfl
      rw [hts', map_mul, ← mul_assoc, IsLocalization.mk'_spec, ← map_mul, mul_comm a, hr,
        map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hmk := IsLocalization.mk'_spec (Localization.AtPrime 𝔭) (r k)
        (⟨t * um, htu⟩ : 𝔭.primeCompl)
      have hc := congrArg (algebraMap (Localization.AtPrime 𝔭)
        (Localization (Algebra.algebraMapSubmonoid (MvPowerSeries (Fin 2) K) 𝔭.primeCompl))) hmk
      rw [map_mul, hRA, hRA] at hc
      rw [map_mul, map_pow, ← hξdef]
      have hsu : algebraMap (MvPowerSeries (Fin 2) K)
            (Localization (Algebra.algebraMapSubmonoid (MvPowerSeries (Fin 2) K) 𝔭.primeCompl))
            (s : MvPowerSeries (Fin 2) K) *
          algebraMap (MvPowerSeries (Fin 2) K)
            (Localization (Algebra.algebraMapSubmonoid (MvPowerSeries (Fin 2) K) 𝔭.primeCompl))
            (u ^ m) =
          algebraMap (MvPowerSeries (Fin 2) K)
            (Localization (Algebra.algebraMapSubmonoid (MvPowerSeries (Fin 2) K) 𝔭.primeCompl))
            (((⟨t * um, htu⟩ : 𝔭.primeCompl) : cyclicInvariants K m q) :
              MvPowerSeries (Fin 2) K) := by
        rw [← map_mul, ← hts']; rfl
      rw [hsu, ← hc]
      ring
    rw [key]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨e.symm k, rfl⟩

open scoped Classical in
/-- Over the punctured spectrum, `K[[x, y]]` is a finite étale `μ_m`-torsor over `R`. -/
private theorem cyclicInvariants_puncturedTorsor
    {K : Type w} [Field K] {m : ℕ} {q : ℤ} (h : IsCyclicQuotientSetting K m q) :
    ∀ (𝔭 : Ideal (cyclicInvariants K m q)) [𝔭.IsPrime], ¬ 𝔭.IsMaximal →
        (letI := localizationAlgebra 𝔭.primeCompl (MvPowerSeries (Fin 2) K)
            (Rₘ := Localization.AtPrime 𝔭)
            (Sₘ := Localization (Algebra.algebraMapSubmonoid (MvPowerSeries (Fin 2) K)
              𝔭.primeCompl));
          Algebra.Etale (Localization.AtPrime 𝔭)
            (Localization (Algebra.algebraMapSubmonoid (MvPowerSeries (Fin 2) K)
              𝔭.primeCompl))) ∧
        Function.Bijective (LocalizedModule.map 𝔭.primeCompl
          (Algebra.TensorProduct.productMap
            ((Algebra.ofId (MvPowerSeries (Fin 2) K)
              (rootsOfUnity m K → MvPowerSeries (Fin 2) K)).restrictScalars
                (cyclicInvariants K m q))
            (Pi.algHom (cyclicInvariants K m q) (fun _ : rootsOfUnity m K =>
                MvPowerSeries (Fin 2) K)
              fun ζ => AlgHom.mk (MvPowerSeries.rescale (cyclicWeights K m q ζ))
                fun r => (mem_cyclicInvariants_iff K m q r).mp r.2 ζ)).toLinearMap) := by
  intro 𝔭 _ h𝔭
  obtain ⟨u, hu, hu0, hs⟩ := exists_chart_of_not_isMaximal h 𝔭 h𝔭
  exact ⟨etale_localization_of_pow h 𝔭 hu hu0 hs,
    bijective_localizedModuleMap_cyclicTorsorMap_of_pow h 𝔭 hu hu0 hs⟩

section CharacterClasses

variable {K : Type w} [Field K] {m : ℕ} {q : ℤ}

/-- `f` is a semi-invariant of weight `w`: `ζ · f = ζ^w f`. -/
private def SemiInv (K : Type w) [Field K] (m : ℕ) (q : ℤ) (w : ℤ) (f : MvPowerSeries (Fin 2) K) :
    Prop :=
  ∀ ζ : rootsOfUnity m K, MvPowerSeries.rescale (cyclicWeights K m q ζ) f =
    MvPowerSeries.C ((((ζ : Kˣ) ^ w : Kˣ)) : K) * f

private theorem SemiInv.mul {w₁ w₂ : ℤ} {f g : MvPowerSeries (Fin 2) K} (hf : SemiInv K m q w₁ f)
    (hg : SemiInv K m q w₂ g) : SemiInv K m q (w₁ + w₂) (f * g) := fun ζ => by
  rw [map_mul, hf, hg, zpow_add, Units.val_mul, map_mul]; ring

private theorem SemiInv.pow {w : ℤ} {f : MvPowerSeries (Fin 2) K} (hf : SemiInv K m q w f) (n : ℕ) :
    SemiInv K m q (n * w) (f ^ n) := by
  induction n with
  | zero => intro ζ; simp
  | succ n ih =>
    have := ih.mul hf
    rw [pow_succ]; convert this using 1; push_cast; ring

private theorem semiInv_of_mem {f : MvPowerSeries (Fin 2) K} (hf : f ∈ cyclicInvariants K m q) :
    SemiInv K m q 0 f := fun ζ => by
  rw [(mem_cyclicInvariants_iff K m q f).mp hf ζ]; simp

private theorem SemiInv.congr {w w' : ℤ} (hw : (m : ℤ) ∣ w - w') {f : MvPowerSeries (Fin 2) K}
    (hf : SemiInv K m q w f) : SemiInv K m q w' f := fun ζ => by
  obtain ⟨k, hk⟩ := hw
  rw [hf, show w = w' + m * k by linarith, zpow_add, zpow_mul, zpow_natCast,
    (mem_rootsOfUnity _ _).mp ζ.2, one_zpow, mul_one]

private theorem SemiInv.mem {w : ℤ} (hw : (m : ℤ) ∣ w) {f : MvPowerSeries (Fin 2) K}
    (hf : SemiInv K m q w f) : f ∈ cyclicInvariants K m q := by
  refine (mem_cyclicInvariants_iff K m q f).mpr fun ζ => ?_
  rw [(hf.congr (w' := 0) (by simpa using hw)) ζ]; simp

private theorem SemiInv.cancel {w w₁ : ℤ} {f g : MvPowerSeries (Fin 2) K}
    (hfg : SemiInv K m q w (f * g)) (hf : SemiInv K m q w₁ f) (hf0 : f ≠ 0) :
    SemiInv K m q (w - w₁) g := fun ζ => by
  have h1 := hfg ζ
  rw [map_mul, hf] at h1
  apply mul_left_cancel₀ hf0
  have e : (((ζ : Kˣ) ^ w : Kˣ) : K) = (((ζ : Kˣ) ^ w₁ : Kˣ) : K) * (((ζ : Kˣ) ^ (w - w₁) : Kˣ) :
      K) := by
    rw [← Units.val_mul, ← zpow_add, add_sub_cancel]
  have hC : (MvPowerSeries.C ((((ζ : Kˣ) ^ w₁ : Kˣ)) : K) : MvPowerSeries (Fin 2) K) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ MvPowerSeries.C_injective]; exact Units.ne_zero _
  apply mul_left_cancel₀ hC
  calc MvPowerSeries.C ((((ζ : Kˣ) ^ w₁ : Kˣ)) : K) *
        (f * MvPowerSeries.rescale (cyclicWeights K m q ζ) g)
      = MvPowerSeries.C ((((ζ : Kˣ) ^ w : Kˣ)) : K) * (f * g) := by rw [← h1]; ring
    _ = _ := by rw [e, map_mul]; ring

private theorem semiInv_X_zero_pow (n : ℕ) : SemiInv K m q n (MvPowerSeries.X 0 ^ n) := fun ζ => by
  rw [rescale_X_zero_pow]; simp

private theorem semiInv_cyclicWeightComponent [NeZero m] (i : ZMod m) (f : MvPowerSeries (Fin 2)
    K) :
    SemiInv K m q ((i.val : ℕ) : ℤ) (cyclicWeightComponent K m q i f) := fun ζ => by
  rw [rescale_cyclicWeightComponent, zpow_natCast, Units.val_pow_eq_pow_val]

/-- A semi-invariant unit has trivial weight. -/
private theorem SemiInv.dvd_of_isUnit (h : IsCyclicQuotientSetting K m q) {w : ℤ}
    {u : MvPowerSeries (Fin 2) K} (hu : SemiInv K m q w u) (hunit : IsUnit u) : (m : ℤ) ∣ w := by
  obtain ⟨ζ', hζ'⟩ := exists_isPrimitiveRoot_rootsOfUnity h
  have h1 := congrArg (MvPowerSeries.coeff 0) (hu ζ')
  rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C_mul] at h1
  have h0 : MvPowerSeries.coeff 0 u ≠ 0 := by
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (MvPowerSeries.isUnit_iff_constantCoeff.mp hunit).ne_zero
  simp only [Finsupp.prod_zero_index, one_mul] at h1
  have h2 : (((ζ' : Kˣ) ^ w : Kˣ) : K) = 1 := mul_right_cancel₀ h0 (h1.symm.trans (one_mul _).symm)
  exact (hζ'.zpow_eq_one_iff_dvd _).mp (Units.val_eq_one.mp h2)

/-- `ζ ↦ rescale ζ` is an action. -/
private theorem rescale_rescale_cyclic (ζ ξ : rootsOfUnity m K) (f : MvPowerSeries (Fin 2) K) :
    MvPowerSeries.rescale (cyclicWeights K m q ζ) (MvPowerSeries.rescale (cyclicWeights K m q ξ)
        f) =
      MvPowerSeries.rescale (cyclicWeights K m q (ζ * ξ)) f := by
  rw [MvPowerSeries.rescale_rescale, map_mul, mul_comm]

private theorem rescale_cyclic_one (f : MvPowerSeries (Fin 2) K) :
    MvPowerSeries.rescale (cyclicWeights K m q 1) f = f := by
  rw [map_one, MvPowerSeries.rescale_one, RingHom.id_apply]

private theorem rescale_cyclic_injective (ζ : rootsOfUnity m K) :
    Function.Injective (MvPowerSeries.rescale (cyclicWeights K m q ζ)) := fun f g hfg => by
  have := congrArg (MvPowerSeries.rescale (cyclicWeights K m q ζ⁻¹)) hfg
  rwa [rescale_rescale_cyclic, rescale_rescale_cyclic, inv_mul_cancel, rescale_cyclic_one,
    rescale_cyclic_one] at this

/-- The weight-`i` component is the twisted average `m⁻¹ ∑_ζ ζ^{-i} ζ · f`. -/
private theorem cyclicWeightComponent_eq_average (h : IsCyclicQuotientSetting K m q)
    [Fintype (rootsOfUnity m K)] [NeZero m] (i : ZMod m) (f : MvPowerSeries (Fin 2) K) :
    cyclicWeightComponent K m q i f = MvPowerSeries.C (m : K)⁻¹ *
      ∑ ζ : rootsOfUnity m K, MvPowerSeries.C ((((ζ : Kˣ) ^ (-((i.val : ℕ) : ℤ)) : Kˣ)) : K) *
        MvPowerSeries.rescale (cyclicWeights K m q ζ) f := by
  have := h.charZero
  have hm : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  ext n
  rw [coeff_cyclicWeightComponent, MvPowerSeries.coeff_C_mul, map_sum]
  simp only [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_rescale, prod_cyclicWeights_pow]
  have hs : ∀ ζ : rootsOfUnity m K, (((ζ : Kˣ) ^ (-((i.val : ℕ) : ℤ)) : Kˣ) : K) *
      ((((ζ : Kˣ) ^ ((n 0 : ℤ) + q * n 1) : Kˣ) : K) * MvPowerSeries.coeff n f) =
      (((ζ : Kˣ) ^ ((n 0 : ℤ) + q * n 1 - ((i.val : ℕ) : ℤ)) : Kˣ) : K) *
        MvPowerSeries.coeff n f := fun ζ => by
    rw [← mul_assoc, ← Units.val_mul, ← zpow_add]; ring_nf
  simp only [hs, ← Finset.sum_mul, sum_rootsOfUnity_zpow h]
  have hiff : (((n 0 : ℤ) + q * n 1 : ℤ) : ZMod m) = i ↔
      (m : ℤ) ∣ (n 0 : ℤ) + q * n 1 - ((i.val : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]
    simp
  split_ifs with hw hd hd
  · rw [← mul_assoc, inv_mul_cancel₀ hm, one_mul]
  · exact absurd (hiff.mp hw) hd
  · exact absurd (hiff.mpr hd) hw
  · rw [zero_mul, mul_zero]

/-- **A semi-invariant generator.** If the principal ideal `(g)` is stable under `μ_m`, one of
the weight components of `g` generates it. -/
private theorem exists_cyclicWeightComponent_eq_mul_unit (h : IsCyclicQuotientSetting K m q)
    [NeZero m] {g : MvPowerSeries (Fin 2) K}
    (hg : ∀ ζ : rootsOfUnity m K, g ∣ MvPowerSeries.rescale (cyclicWeights K m q ζ) g)
    (hg0 : g ≠ 0) :
    ∃ (i : ZMod m) (v : MvPowerSeries (Fin 2) K), IsUnit v ∧
      cyclicWeightComponent K m q i g = g * v := by
  classical
  have := Fintype.ofFinite (rootsOfUnity m K)
  have hdvd : ∀ i : ZMod m, g ∣ cyclicWeightComponent K m q i g := fun i => by
    rw [cyclicWeightComponent_eq_average h]
    exact Dvd.dvd.mul_left (Finset.dvd_sum fun ζ _ => Dvd.dvd.mul_left (hg ζ) _) _
  choose c hc using hdvd
  have hsum : g * ∑ i : ZMod m, c i = g * 1 := by
    rw [Finset.mul_sum, mul_one]
    conv_rhs => rw [← sum_cyclicWeightComponent K m q g]
    exact Finset.sum_congr rfl fun i _ => (hc i).symm
  have h1 := mul_left_cancel₀ hg0 hsum
  by_contra hno
  push Not at hno
  have hmem : ∀ i : ZMod m, c i ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) K) :=
    fun i => (IsLocalRing.mem_maximalIdeal _).mpr fun hu => hno i (c i) hu (hc i)
  have : (1 : MvPowerSeries (Fin 2) K) ∈ IsLocalRing.maximalIdeal _ :=
    h1 ▸ Ideal.sum_mem _ fun i _ => hmem i
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr this)

/-- For `s ≠ 0` of weight `a` and `u` of weight `1`, `t = s u^{m - k}` with
`k ≡ a (mod m)` is invariant, and every invariant multiple `r` of `s` satisfies
`r u^m = t w` with `w` invariant. -/
private theorem mul_pow_mem_cyclicInvariants_and_exists_mul_pow_eq
    (h : IsCyclicQuotientSetting K m q) {a : ℤ} {s u : MvPowerSeries (Fin 2) K}
    (hs : SemiInv K m q a s) (hs0 : s ≠ 0) (hu : SemiInv K m q 1 u) :
    s * u ^ (m - (a % m).toNat) ∈ cyclicInvariants K m q ∧
      ∀ r : cyclicInvariants K m q, s ∣ (r : MvPowerSeries (Fin 2) K) →
        ∃ w : cyclicInvariants K m q, (r : MvPowerSeries (Fin 2) K) * u ^ m =
          s * u ^ (m - (a % m).toNat) * w := by
  have hm : (m : ℤ) ≠ 0 := by have := h.one_le; omega
  have hk0 : 0 ≤ a % m := Int.emod_nonneg _ hm
  have hkm : a % m < m := Int.emod_lt_of_pos _ (by have := h.one_le; omega)
  have hk : (((a % m).toNat : ℕ) : ℤ) = a % m := Int.toNat_of_nonneg hk0
  have hle : (a % m).toNat ≤ m := by omega
  refine ⟨?_, fun r ⟨b, hb⟩ => ?_⟩
  · refine (hs.mul (hu.pow _)).mem ?_
    rw [Nat.cast_sub hle, hk, mul_one]
    exact ⟨1 + a / m, by rw [Int.emod_def]; ring⟩
  · have hb' : SemiInv K m q (0 - a) b := (hb ▸ semiInv_of_mem r.2).cancel hs hs0
    have hw : b * u ^ (a % m).toNat ∈ cyclicInvariants K m q := by
      refine (hb'.mul (hu.pow _)).mem ?_
      rw [hk, mul_one]
      exact ⟨-(a / m), by rw [Int.emod_def]; ring⟩
    refine ⟨⟨_, hw⟩, ?_⟩
    change _ = _ * (b * u ^ (a % m).toNat)
    rw [hb]
    calc s * b * u ^ m = s * b * u ^ (m - (a % m).toNat + (a % m).toNat) := by
          rw [Nat.sub_add_cancel hle]
      _ = _ := by ring

private theorem prime_X_zero : Prime (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) := by
  let _ : IsDomain (MvPowerSeries (Fin 1) K) := NoZeroDivisors.to_isDomain _
  let e := MvPowerSeries.finSuccEquiv K 1
  apply (MulEquiv.prime_iff e.toMulEquiv).mp
  change Prime (MvPowerSeries.finSuccEquiv K 1 (MvPowerSeries.X 0))
  rw [MvPowerSeries.finSuccEquiv_X_zero]
  exact PowerSeries.X_prime

private theorem X_zero_not_dvd_X_one_pow (n : ℕ) :
    ¬ (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ∣ MvPowerSeries.X 1 ^ n := by
  classical
  rw [MvPowerSeries.X_dvd_iff]
  intro hd
  have := hd (Finsupp.single 1 n) (by simp)
  simp [MvPowerSeries.coeff_X_pow] at this

/-- In a Noetherian local domain of dimension two, a nonzero non-maximal prime has height
one. -/
private theorem height_eq_one_of_dim_two {S : Type*} [CommRing S] [IsDomain S] [IsLocalRing S]
    [IsNoetherianRing S] (hd : ringKrullDim S = 2) (P : Ideal S) [P.IsPrime] (h0 : P ≠ ⊥)
    (h1 : ¬ P.IsMaximal) : P.height = 1 := by
  have hlt : P < IsLocalRing.maximalIdeal S :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›))
      (fun e => h1 (e ▸ IsLocalRing.maximalIdeal.isMaximal S))
  have h2 := Ideal.height_strict_mono_of_isPrime hlt
  have hm : (IsLocalRing.maximalIdeal S).height = 2 := by
    have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := S)
    rw [hd] at this; exact WithBot.coe_injective (this.trans rfl)
  rw [hm] at h2
  have hne : P.height ≠ 0 := fun e => h0 (Ideal.height_eq_zero_iff_eq_bot.mp e)
  have hfin : P.height ≠ ⊤ := ne_top_of_lt h2
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hn] at h2 hne ⊢
  have : n < 2 := by exact_mod_cast h2
  have : n ≠ 0 := by rintro rfl; exact hne rfl
  obtain rfl : n = 1 := by omega
  rfl

/-- Two height-one primes, one inside the other, are equal. -/
private theorem eq_of_le_of_height_eq_one {S : Type*} [CommRing S] {P P' : Ideal S}
    [P.IsPrime] [P'.IsPrime] (hP : P.height = 1) (hP' : P'.height = 1) (hle : P ≤ P') :
    P = P' := by
  have : P.FiniteHeight := ⟨.inr (by simp [hP])⟩
  exact Ideal.eq_of_le_of_height_le P hle (hP'.trans hP.symm).le

/-- The ideal `(x) ∩ R` of invariants divisible by `x`. -/
private noncomputable def xIdeal (K : Type w) [Field K] (m : ℕ) (q : ℤ) : Ideal (cyclicInvariants
    K m q) :=
  (Ideal.span {MvPowerSeries.X 0}).comap (cyclicInvariants K m q).subtype

private theorem mem_xIdeal {r : cyclicInvariants K m q} :
    r ∈ xIdeal K m q ↔ MvPowerSeries.X 0 ∣ (r : MvPowerSeries (Fin 2) K) := by
  rw [xIdeal, Ideal.mem_comap, Ideal.mem_span_singleton]; rfl

private theorem xIdeal_isPrime : (xIdeal K m q).IsPrime :=
  have : (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)}).IsPrime :=
    (Ideal.span_singleton_prime prime_X_zero.ne_zero).mpr prime_X_zero
  Ideal.comap_isPrime _ _

attribute [local instance] xIdeal_isPrime

/-- **Radical criterion.** If `s ≠ 0` is semi-invariant and `s^m` lies in a prime `P'` of `R`,
then every invariant multiple of `s` lies in `P'`. -/
private theorem mem_of_dvd_of_pow_mem {a : ℤ}
    {s : MvPowerSeries (Fin 2) K} (hs : SemiInv K m q a s) (hs0 : s ≠ 0)
    (P' : Ideal (cyclicInvariants K m q)) [P'.IsPrime]
    (hsm : ∀ hmem : s ^ m ∈ cyclicInvariants K m q, (⟨_, hmem⟩ : cyclicInvariants K m q) ∈ P')
    (r : cyclicInvariants K m q) (hr : s ∣ (r : MvPowerSeries (Fin 2) K)) : r ∈ P' := by
  obtain ⟨b, hb⟩ := hr
  have hb' : SemiInv K m q (0 - a) b := (hb ▸ semiInv_of_mem r.2).cancel hs hs0
  have hsmem : s ^ m ∈ cyclicInvariants K m q := (hs.pow m).mem ⟨a, by ring⟩
  have hbmem : b ^ m ∈ cyclicInvariants K m q := (hb'.pow m).mem ⟨0 - a, by ring⟩
  have e : r ^ m = (⟨_, hsmem⟩ : cyclicInvariants K m q) * ⟨_, hbmem⟩ := by
    ext1; simp only [SubmonoidClass.coe_pow, Subring.coe_mul]; rw [hb, mul_pow]
  exact (‹P'.IsPrime›).mem_of_pow_mem m (e ▸ P'.mul_mem_right _ (hsm hsmem))

private theorem not_isMaximal_of_height_eq_one (h : IsCyclicQuotientSetting K m q)
    (P : Ideal (cyclicInvariants K m q)) [P.IsPrime] (hP : P.height = 1) : ¬ P.IsMaximal := by
  have := isLocalRing_cyclicInvariants K m q
  intro hmax
  have e : P = IsLocalRing.maximalIdeal _ := IsLocalRing.eq_maximalIdeal hmax
  have h2 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := cyclicInvariants K m q)
  rw [← e, hP, ringKrullDim_cyclicInvariants h] at h2
  exact absurd h2 (by decide)

/-- **A semi-invariant generator of a height-one prime.** Every height-one prime `P` of
`R = K[[x, y]]^{μ_m}` is the set of invariants divisible by a single semi-invariant `s ≠ 0`. -/
private theorem exists_semiInv_generator (h : IsCyclicQuotientSetting K m q)
    (P : Ideal (cyclicInvariants K m q)) [P.IsPrime] (hP : P.height = 1) :
    ∃ (a : ℤ) (s : MvPowerSeries (Fin 2) K), SemiInv K m q a s ∧ s ≠ 0 ∧
      ∀ r : cyclicInvariants K m q, s ∣ (r : MvPowerSeries (Fin 2) K) ↔ r ∈ P := by
  classical
  have := neZero_of_isCyclicQuotientSetting h
  have := Fintype.ofFinite (rootsOfUnity m K)
  have := isRegularLocalRing_mvPowerSeries_two K
  have : IsDomain (MvPowerSeries (Fin 2) K) := IsRegularLocalRing.isDomain _
  have : UniqueFactorizationMonoid (MvPowerSeries (Fin 2) K) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  have := module_finite_cyclicInvariants h
  have hdimA : ringKrullDim (MvPowerSeries (Fin 2) K) = 2 := by
    rw [MvPowerSeries.ringKrullDim_eq]; rfl
  let _ : NormalizationMonoid (MvPowerSeries (Fin 2) K) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid.toNormalizationMonoid
  let _ := UniqueFactorizationMonoid.toNormalizedGCDMonoid (MvPowerSeries (Fin 2) K)
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hP
  have hPmax := not_isMaximal_of_height_eq_one h P hP
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P
    (⊥ : Ideal (MvPowerSeries (Fin 2) K)) (by simp)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply hP0
    rw [← hQP]
    exact Ideal.comap_bot_of_injective _ Subtype.val_injective
  have hQmax : ¬ Q.IsMaximal := fun hm =>
    hPmax (hQP ▸ Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q)
  have hQh := height_eq_one_of_dim_two hdimA Q hQ0 hQmax
  obtain ⟨π, hπ⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hQh).principal
  have hmemQ : ∀ f, f ∈ Q ↔ π ∣ f := fun f => by
    rw [hπ, Ideal.submodule_span_eq, Ideal.mem_span_singleton]
  have hmemP : ∀ r : cyclicInvariants K m q, r ∈ P ↔ π ∣ (r : MvPowerSeries (Fin 2) K) :=
    fun r => by rw [← hQP, Ideal.mem_comap, hmemQ]; rfl
  have hπ0 : π ≠ 0 := by
    rintro rfl
    apply hQ0
    rw [hπ]; simp
  set g := (Finset.univ : Finset (rootsOfUnity m K)).lcm
    (fun ζ => MvPowerSeries.rescale (cyclicWeights K m q ζ) π) with hgdef
  have hgr : ∀ r : cyclicInvariants K m q, g ∣ (r : MvPowerSeries (Fin 2) K) ↔ r ∈ P := by
    intro r
    rw [hmemP, Finset.lcm_dvd_iff]
    refine ⟨fun hd => ?_, fun hd ζ _ => ?_⟩
    · simpa [rescale_cyclic_one] using hd 1 (Finset.mem_univ _)
    · have := map_dvd (MvPowerSeries.rescale (cyclicWeights K m q ζ)) hd
      rwa [(mem_cyclicInvariants_iff K m q _).mp r.2 ζ] at this
  have hgst : ∀ ξ : rootsOfUnity m K, g ∣ MvPowerSeries.rescale (cyclicWeights K m q ξ) g := by
    intro ξ
    rw [hgdef, Finset.lcm_dvd_iff]
    intro ζ _
    have h1 : MvPowerSeries.rescale (cyclicWeights K m q (ξ⁻¹ * ζ)) π ∣ g :=
      Finset.dvd_lcm (Finset.mem_univ _)
    have h2 := map_dvd (MvPowerSeries.rescale (cyclicWeights K m q ξ)) h1
    rwa [rescale_rescale_cyclic, mul_inv_cancel_left] at h2
  have hg0 : g ≠ 0 := by
    rw [hgdef, Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨ζ, -, hζ⟩
    exact hπ0 (rescale_cyclic_injective ζ (hζ.trans (map_zero _).symm))
  obtain ⟨i, v, hv, hiv⟩ := exists_cyclicWeightComponent_eq_mul_unit h hgst hg0
  refine ⟨_, _, semiInv_cyclicWeightComponent i g, ?_, fun r => ?_⟩
  · rw [hiv]; exact mul_ne_zero hg0 hv.ne_zero
  · rw [hiv, hv.mul_right_dvd]
    exact hgr r

/-- **Local parameter.** For a height-one prime `P` cut out by divisibility by a semi-invariant
`s` of weight `a`, and a semi-invariant `u` of weight `1` with `u^m ∉ P`, the invariant
`t = s u^{m-k}` lies in `P` and generates `P R_P`, and `t^m = s^m (u^m)^{m-k}`. -/
private theorem exists_localParameter (h : IsCyclicQuotientSetting K m q)
    (P : Ideal (cyclicInvariants K m q)) [P.IsPrime] {a : ℤ} {s u : MvPowerSeries (Fin 2) K}
    (hs : SemiInv K m q a s) (hs0 : s ≠ 0)
    (hsP : ∀ r : cyclicInvariants K m q, s ∣ (r : MvPowerSeries (Fin 2) K) ↔ r ∈ P)
    (hu : SemiInv K m q 1 u)
    (huP : (⟨u ^ m, (hu.pow m).mem ⟨1, by ring⟩⟩ : cyclicInvariants K m q) ∉ P) :
    ∃ t : cyclicInvariants K m q, (t : MvPowerSeries (Fin 2) K) = s * u ^ (m - (a % m).toNat) ∧
      t ∈ P ∧ (∀ r ∈ P, ∃ w d : cyclicInvariants K m q, d ∉ P ∧ r * d = t * w) ∧
      (∀ hsm : s ^ m ∈ cyclicInvariants K m q,
        t ^ m = ⟨_, hsm⟩ * ⟨u ^ m, (hu.pow m).mem ⟨1, by ring⟩⟩ ^ (m - (a % m).toNat)) := by
  obtain ⟨ht, hgen⟩ := mul_pow_mem_cyclicInvariants_and_exists_mul_pow_eq h hs hs0 hu
  refine ⟨⟨_, ht⟩, rfl, (hsP _).mp (Dvd.intro _ rfl), fun r hr => ?_, fun hsm => ?_⟩
  · obtain ⟨w, hw⟩ := hgen r ((hsP r).mpr hr)
    exact ⟨w, _, huP, Subtype.ext (by simpa using hw)⟩
  · ext1
    simp only [SubmonoidClass.coe_pow, Subring.coe_mul]
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm m]

section Geometry

section Affine

variable {R : CommRingCat.{w}}

private theorem coheight_eq_one_iff (x : Spec R) :
    coheight x = 1 ↔ (x : PrimeSpectrum R).asIdeal.height = 1 := by
  let _ : Algebra R ((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk x) (x : PrimeSpectrum R).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R x
  have h1 := ringKrullDim_stalk_eq_coheight x
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (x : PrimeSpectrum R).asIdeal] at h1
  constructor
  · intro h; rw [h] at h1; exact_mod_cast h1
  · intro h; rw [h] at h1; exact_mod_cast h1.symm

variable [IsDomain R]

private theorem algebraMap_stalk_functionField (x : Spec R) (r : R) :
    letI : Algebra R ((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x
    algebraMap ((Spec R).presheaf.stalk x) (Spec R).functionField
      (algebraMap R _ r) = algebraMap R (Spec R).functionField r := by
  let _ : Algebra R ((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x
  exact StructureSheaf.toStalk_stalkSpecializes_apply
    ((genericPoint_spec (Spec R)).specializes (Set.mem_univ x)) r

private theorem ord_algebraMap_eq_zero [IsNoetherianRing R] (x : Spec R) {r : R}
    (hr : r ∉ (x : PrimeSpectrum R).asIdeal) :
    Scheme.ord (algebraMap R (Spec R).functionField r) x = 0 := by
  by_cases hx : coheight x = 1
  · let _ : Algebra R ((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x
    have : IsLocalization.AtPrime ((Spec R).presheaf.stalk x) (x : PrimeSpectrum R).asIdeal :=
      StructureSheaf.IsLocalization.to_stalk R x
    have hr0 : r ≠ 0 := fun h => hr (h ▸ Ideal.zero_mem _)
    have hne : algebraMap R (Spec R).functionField r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R _)).mpr hr0
    rw [Scheme.ord_eq_iff hx hne, ← algebraMap_stalk_functionField]
    have : Ring.KrullDimLE 1 ((Spec R).presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    exact Ring.ordFrac_of_isUnit (IsLocalization.map_units _
      (⟨r, hr⟩ : (x : PrimeSpectrum R).asIdeal.primeCompl))
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx _

private theorem ord_algebraMap_eq_one [IsNoetherianRing R] [IsNormal (Spec R)] (x : Spec R)
    (hx : coheight x = 1) {t : R} (ht : t ∈ (x : PrimeSpectrum R).asIdeal)
    (hgen : ∀ r ∈ (x : PrimeSpectrum R).asIdeal, ∃ w d : R,
      d ∉ (x : PrimeSpectrum R).asIdeal ∧ r * d = t * w) :
    Scheme.ord (algebraMap R (Spec R).functionField t) x = 1 := by
  let _ : Algebra R ((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk x) (x : PrimeSpectrum R).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R x
  have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk hx
  rw [← algebraMap_stalk_functionField]
  have key := ord_algebraMap_eq_of_span_eq_maximalIdeal_pow x hx
    (algebraMap R ((Spec R).presheaf.stalk x) t) 1 ?_
  · exact_mod_cast key
  rw [pow_one, ← IsLocalization.AtPrime.map_eq_maximalIdeal (x : PrimeSpectrum R).asIdeal]
  apply le_antisymm
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ ht
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    obtain ⟨w, d, hd, hrd⟩ := hgen r hr
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    have hu := IsLocalization.map_units ((Spec R).presheaf.stalk x)
      (⟨d, hd⟩ : (x : PrimeSpectrum R).asIdeal.primeCompl)
    refine ⟨algebraMap R _ w * hu.unit⁻¹, ?_⟩
    rw [← mul_assoc, ← map_mul, ← hrd, map_mul, mul_assoc]
    change _ = _ * (hu.unit * hu.unit⁻¹ : (_ : Type w)ˣ).val
    simp

private theorem exists_eq_germ_top (s : Γ(Spec R, ⊤)) :
    ∃ r : R, (Spec R).presheaf.germ ⊤ (genericPoint _) trivial s =
      algebraMap R (Spec R).functionField r := by
  obtain ⟨r, rfl⟩ : ∃ r, (Scheme.ΓSpecIso R).inv r = s :=
    ⟨(Scheme.ΓSpecIso R).hom s, by simp⟩
  refine ⟨r, ?_⟩
  rw [Scheme.ΓSpecIso_inv]
  exact StructureSheaf.algebraMap_germ_apply _ _ _ _

end Affine

section Divisors

variable {X : Scheme.{w}} [IsIntegral X] [IsLocallyNoetherian X]

private theorem exists_ratUnit (z : X.functionField) (hz : z ≠ 0) :
    ∃ v : (Stacks.Chow.rationalFunctions X)ˣ,
      (Stacks.Chow.rationalFunctionsEquivFunctionField X).1 v = z :=
  ⟨Units.mk0 ((Stacks.Chow.rationalFunctionsEquivFunctionField X).1.symm z) (by simpa using hz),
    by simp⟩

/-- The principal Weil divisor of a nonzero element of the function field. -/
private noncomputable def divOf (z : X.functionField) (hz : z ≠ 0) : AlgebraicGeometry.WeilDivisor
    X :=
  principalDivisor X (exists_ratUnit z hz).choose

private theorem divOf_apply (z : X.functionField) (hz : z ≠ 0) (Z : PrimeDivisor X) :
    (divOf z hz).val Z = Scheme.ord z Z.genericPoint := by
  rw [divOf, principalDivisor_apply, (exists_ratUnit z hz).choose_spec]

private theorem exists_of_mk_eq_zero (D : AlgebraicGeometry.WeilDivisor X) (hD : (D :
    weilDivisorClassGroup X) = 0) :
    ∃ (z : X.functionField) (hz : z ≠ 0), divOf z hz = D := by
  obtain ⟨f, hf⟩ := (mk_eq_zero_iff X D).mp hD
  refine ⟨(Stacks.Chow.rationalFunctionsEquivFunctionField X).1 f, by simp, ?_⟩
  rw [← hf]
  apply Subtype.ext; funext Z
  rw [divOf_apply, principalDivisor_apply]

private theorem mk_divOf (z : X.functionField) (hz : z ≠ 0) :
    ((divOf z hz : AlgebraicGeometry.WeilDivisor X) : weilDivisorClassGroup X) = 0 :=
  (mk_eq_zero_iff X _).mpr ⟨_, rfl⟩

private theorem ord_inv {f : X.functionField} (hf : f ≠ 0) (x : X) :
    Scheme.ord f⁻¹ x = - Scheme.ord f x := by
  have h1 := Scheme.ord_mul (x := x) hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf] at h1
  have h0 := Scheme.ord_pow (X := X) (one_ne_zero (α := X.functionField)) 0 x
  simp only [pow_zero, Nat.cast_zero, zero_mul] at h0
  omega

private theorem ord_div {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) (x : X) :
    Scheme.ord (f / g) x = Scheme.ord f x - Scheme.ord g x := by
  rw [div_eq_mul_inv, Scheme.ord_mul hf (inv_ne_zero hg), ord_inv hg]; ring

open scoped Classical in
private theorem single_mem_weilDivisor (Z : PrimeDivisor X) (n : ℤ) :
    (Pi.single Z n : PrimeDivisor X → ℤ) ∈ AlgebraicGeometry.WeilDivisor X := by
  intro x
  refine ⟨Set.univ, Filter.univ_mem, (Set.finite_singleton Z).subset ?_⟩
  intro W hW
  by_contra hne
  simp only [Set.mem_singleton_iff] at hne
  simp [Pi.single_apply, hne] at hW

end Divisors

end Geometry

section Assembly

/-- `R` as a commutative ring, kept opaque so that instances on `Spec R` are found. -/
private noncomputable def invariantRingCat (K : Type w) [Field K] (m : ℕ) (q : ℤ) :
    CommRingCat.{w} :=
  CommRingCat.of (cyclicInvariants K m q)

/-- The point of `Spec R` at a prime of `R`. -/
private def ptOf (P : Ideal (cyclicInvariants K m q)) [P.IsPrime] : Spec (invariantRingCat K m q) :=
  (⟨P, inferInstance⟩ : PrimeSpectrum (cyclicInvariants K m q))

/-- The prime of `R` at a point of `Spec R`. -/
private def idealOf (y : Spec (invariantRingCat K m q)) : Ideal (cyclicInvariants K m q) :=
  (y : PrimeSpectrum (invariantRingCat K m q)).asIdeal

private theorem idealOf_isPrime (y : Spec (invariantRingCat K m q)) : (idealOf y).IsPrime :=
  (y : PrimeSpectrum (invariantRingCat K m q)).isPrime

attribute [local instance] idealOf_isPrime

private theorem ptOf_idealOf (y : Spec (invariantRingCat K m q)) : ptOf (idealOf y) = y := rfl

private theorem ptOf_congr {P P' : Ideal (cyclicInvariants K m q)} [P.IsPrime] [P'.IsPrime]
    (e : P = P') : ptOf P = ptOf P' := by subst e; rfl

/-- `x^m` as an invariant. -/
private noncomputable def xm (h : IsCyclicQuotientSetting K m q) : cyclicInvariants K m q :=
  ⟨_, X_pow_mem_cyclicInvariants h 0⟩

private theorem semiInv_X_zero : SemiInv K m q 1 (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) := by
  simpa using semiInv_X_zero_pow (K := K) (m := m) (q := q) 1

private theorem xm_ne_zero (h : IsCyclicQuotientSetting K m q) : xm h ≠ 0 := fun e => by
  have := congrArg Subtype.val e
  exact pow_ne_zero m (X_ne_zero K 0) this

private theorem height_xIdeal (h : IsCyclicQuotientSetting K m q)
    [IsDomain (cyclicInvariants K m q)] [IsNoetherianRing (cyclicInvariants K m q)] :
    (xIdeal K m q).height = 1 := by
  have := isLocalRing_cyclicInvariants K m q
  refine height_eq_one_of_dim_two (ringKrullDim_cyclicInvariants h) _ ?_ ?_
  · intro e
    have : xm h ∈ xIdeal K m q := mem_xIdeal.mpr (dvd_pow_self _ (by have := h.one_le; omega))
    rw [e, Ideal.mem_bot] at this
    exact xm_ne_zero h this
  · intro hmax
    set ym : cyclicInvariants K m q := ⟨_, X_pow_mem_cyclicInvariants h 1⟩
    have hym : ym ∈ IsLocalRing.maximalIdeal _ := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hu' := hu.map (cyclicInvariants K m q).subtype
      have := MvPowerSeries.isUnit_iff_constantCoeff.mp hu'
      have hm1 : m ≠ 0 := by have := h.one_le; omega
      simp [ym, hm1] at this
    rw [← IsLocalRing.eq_maximalIdeal hmax, mem_xIdeal] at hym
    exact X_zero_not_dvd_X_one_pow m hym

private theorem eq_xIdeal_of_xm_mem (h : IsCyclicQuotientSetting K m q)
    [IsDomain (cyclicInvariants K m q)] [IsNoetherianRing (cyclicInvariants K m q)]
    (P : Ideal (cyclicInvariants K m q)) [P.IsPrime] (hP : P.height = 1) (hx : xm h ∈ P) :
    P = xIdeal K m q := by
  have hle : xIdeal K m q ≤ P := fun r hr =>
    mem_of_dvd_of_pow_mem semiInv_X_zero (X_ne_zero K 0) P (fun _ => hx) r (mem_xIdeal.mp hr)
  exact (eq_of_le_of_height_eq_one (height_xIdeal h) hP hle).symm

variable [IsDomain (invariantRingCat K m q)] [IsNoetherianRing (cyclicInvariants K m q)]

private theorem isDomain_of_invariantRingCat : IsDomain (cyclicInvariants K m q) :=
  ‹IsDomain (invariantRingCat K m q)›

private theorem isNoetherianRing_invariantRingCat : IsNoetherianRing (invariantRingCat K m q) :=
  ‹IsNoetherianRing (cyclicInvariants K m q)›

attribute [local instance] isNoetherianRing_invariantRingCat

private theorem isNormal_spec (h : IsCyclicQuotientSetting K m q) :
    IsNormal (Spec (invariantRingCat K m q)) := by
  have := isDomain_of_invariantRingCat (K := K) (m := m) (q := q)
  have : IsIntegrallyClosed (cyclicInvariants K m q) := isIntegrallyClosed_cyclicInvariants
  exact isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed _)

private theorem height_idealOf {y : Spec (invariantRingCat K m q)} (hy : coheight y = 1) :
    (idealOf y).height = 1 :=
  (coheight_eq_one_iff _).mp hy

private theorem coheight_ptOf {P : Ideal (cyclicInvariants K m q)} [P.IsPrime] (hP : P.height = 1) :
    coheight (ptOf P) = 1 :=
  (coheight_eq_one_iff _).mpr hP

/-- The function field of `Spec R` as a field of fractions of `R`. -/
private noncomputable def toFF (K : Type w) [Field K] (m : ℕ) (q : ℤ)
    [IsDomain (invariantRingCat K m q)] :
    cyclicInvariants K m q →+* (Spec (invariantRingCat K m q)).functionField :=
  algebraMap (invariantRingCat K m q) (Spec (invariantRingCat K m q)).functionField

private theorem toFF_injective : Function.Injective (toFF K m q) :=
  IsFractionRing.injective (invariantRingCat K m q) (Spec (invariantRingCat K m q)).functionField

private theorem toFF_ne_zero {r : cyclicInvariants K m q} (hr : r ≠ 0) : toFF K m q r ≠ 0 :=
  (map_ne_zero_iff _ toFF_injective).mpr hr

private theorem ord_toFF_eq_zero (P : Ideal (cyclicInvariants K m q)) [P.IsPrime]
    {r : cyclicInvariants K m q} (hr : r ∉ P) :
    Scheme.ord (toFF K m q r) (ptOf P) = 0 :=
  ord_algebraMap_eq_zero (R := invariantRingCat K m q) (ptOf P) hr

private theorem ord_toFF_eq_one (h : IsCyclicQuotientSetting K m q) (P : Ideal (cyclicInvariants K
    m q))
    [P.IsPrime] (hP : P.height = 1) {t : cyclicInvariants K m q} (ht : t ∈ P)
    (hgen : ∀ r ∈ P, ∃ w d : cyclicInvariants K m q, d ∉ P ∧ r * d = t * w) :
    Scheme.ord (toFF K m q t) (ptOf P) = 1 :=
  have := isNormal_spec h
  ord_algebraMap_eq_one (R := invariantRingCat K m q) (ptOf P) (coheight_ptOf hP) ht hgen

/-- `ord_C(x^m) = m`. -/
private theorem ord_xm_ptOf_xIdeal (h : IsCyclicQuotientSetting K m q) :
    Scheme.ord (toFF K m q (xm h)) (ptOf (xIdeal K m q)) = m := by
  have := isDomain_of_invariantRingCat (K := K) (m := m) (q := q)
  obtain ⟨q', hq'⟩ := exists_rescale_X_one_pow h
  have hu : SemiInv K m q 1 (MvPowerSeries.X 1 ^ q' : MvPowerSeries (Fin 2) K) := fun ζ => by
    rw [hq' ζ]; simp
  have huP : (⟨(MvPowerSeries.X 1 ^ q') ^ m, (hu.pow m).mem ⟨1, by ring⟩⟩ :
      cyclicInvariants K m q) ∉ xIdeal K m q := by
    rw [mem_xIdeal]; simp only; rw [← pow_mul]; exact X_zero_not_dvd_X_one_pow _
  obtain ⟨t, -, htP, hgen, hpow⟩ := exists_localParameter h (xIdeal K m q) semiInv_X_zero
    (X_ne_zero K 0) (fun r => mem_xIdeal.symm) hu huP
  have h1 := ord_toFF_eq_one h (xIdeal K m q) (height_xIdeal h) htP hgen
  have h0 := ord_toFF_eq_zero (xIdeal K m q) huP
  have hpow' : t ^ m = xm h * _ := hpow (X_pow_mem_cyclicInvariants h 0)
  have hum0 : (⟨(MvPowerSeries.X 1 ^ q') ^ m, (hu.pow m).mem ⟨1, by ring⟩⟩ :
      cyclicInvariants K m q) ≠ 0 := fun e => huP (e ▸ Ideal.zero_mem _)
  have ht0 : t ≠ 0 := by
    intro e
    rw [e, zero_pow (by have := h.one_le; omega)] at hpow'
    exact mul_ne_zero (xm_ne_zero h) (pow_ne_zero _ hum0) hpow'.symm
  have key := congrArg (fun z => Scheme.ord z (ptOf (xIdeal K m q))) (congrArg (toFF K m q) hpow')
  simp only [map_mul, map_pow] at key
  rw [Scheme.ord_pow (toFF_ne_zero ht0), Scheme.ord_mul (toFF_ne_zero (xm_ne_zero h))
    (pow_ne_zero _ (toFF_ne_zero hum0)), Scheme.ord_pow (toFF_ne_zero hum0), h1, h0] at key
  linarith

/-- Away from `C`, `x^m` has order zero. -/
private theorem ord_xm_eq_zero (h : IsCyclicQuotientSetting K m q) (P : Ideal (cyclicInvariants K
    m q))
    [P.IsPrime] (hP : P.height = 1) (hPx : P ≠ xIdeal K m q) :
    Scheme.ord (toFF K m q (xm h)) (ptOf P) = 0 := by
  have := isDomain_of_invariantRingCat (K := K) (m := m) (q := q)
  exact ord_toFF_eq_zero P fun hx => hPx (eq_xIdeal_of_xm_mem h P hP hx)

/-- **A local equation away from `C`.** For a height-one prime `P ≠ (x) ∩ R` there is an
invariant of order one at `P` and of order zero at every other height-one prime but `(x) ∩ R`. -/
private theorem exists_local_equation (h : IsCyclicQuotientSetting K m q)
    (P : Ideal (cyclicInvariants K m q)) [P.IsPrime] (hP : P.height = 1)
    (hPx : P ≠ xIdeal K m q) :
    ∃ t : cyclicInvariants K m q, t ≠ 0 ∧ Scheme.ord (toFF K m q t) (ptOf P) = 1 ∧
      ∀ (P' : Ideal (cyclicInvariants K m q)) [P'.IsPrime], P'.height = 1 → P' ≠ P →
        P' ≠ xIdeal K m q → Scheme.ord (toFF K m q t) (ptOf P') = 0 := by
  have := isDomain_of_invariantRingCat (K := K) (m := m) (q := q)
  obtain ⟨a, s, hs, hs0, hsP⟩ := exists_semiInv_generator h P hP
  have huP : (⟨MvPowerSeries.X 0 ^ m, (semiInv_X_zero.pow m).mem ⟨1, by ring⟩⟩ :
      cyclicInvariants K m q) ∉ P := fun hx => hPx (eq_xIdeal_of_xm_mem h P hP hx)
  obtain ⟨t, htv, htP, hgen, -⟩ := exists_localParameter h P hs hs0 hsP semiInv_X_zero huP
  have ht0 : t ≠ 0 := fun e => by
    have := congrArg Subtype.val e
    rw [htv] at this
    exact mul_ne_zero hs0 (pow_ne_zero _ (X_ne_zero K 0)) this
  refine ⟨t, ht0, ord_toFF_eq_one h P hP htP hgen, fun P' _ hP' hne hnx => ?_⟩
  refine ord_toFF_eq_zero P' fun htP' => ?_
  have hsm : s ^ m ∈ cyclicInvariants K m q := (hs.pow m).mem ⟨a, by ring⟩
  have hm0 : m ≠ 0 := by have := h.one_le; omega
  have e : t ^ m = (⟨_, hsm⟩ : cyclicInvariants K m q) *
      ⟨MvPowerSeries.X 0 ^ m, (semiInv_X_zero.pow m).mem ⟨1, by ring⟩⟩ ^ (m - (a % m).toNat) := by
    ext1; simp only [SubmonoidClass.coe_pow, Subring.coe_mul, htv]
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm m]
  have htm : t ^ m ∈ P' := P'.pow_mem_of_mem htP' m (Nat.pos_of_ne_zero hm0)
  rw [e] at htm
  rcases (‹P'.IsPrime›).mem_or_mem htm with hs' | hx'
  · exact hne (eq_of_le_of_height_eq_one hP hP' fun r hr =>
      mem_of_dvd_of_pow_mem hs hs0 P' (fun _ => hs') r ((hsP r).mpr hr)).symm
  · exact hnx (eq_xIdeal_of_xm_mem h P' hP' ((‹P'.IsPrime›).mem_of_pow_mem _ hx'))

end Assembly

section ClassGroup

attribute [local instance] idealOf_isPrime isNoetherianRing_invariantRingCat

variable [IsDomain (invariantRingCat K m q)] [IsNoetherianRing (cyclicInvariants K m q)]

private theorem coheight_ptOf_xIdeal (h : IsCyclicQuotientSetting K m q) :
    coheight (ptOf (xIdeal K m q)) = 1 :=
  have := isDomain_of_invariantRingCat (K := K) (m := m) (q := q)
  coheight_ptOf (height_xIdeal h)

private theorem toFF_div_surjective (z : (Spec (invariantRingCat K m q)).functionField) :
    ∃ a b : cyclicInvariants K m q, b ≠ 0 ∧ toFF K m q a / toFF K m q b = z := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (invariantRingCat K m q) z
  exact ⟨a, b, nonZeroDivisors.ne_zero hb, hab⟩

private theorem exists_toFF_eq_germ_top (s : Γ(Spec (invariantRingCat K m q), ⊤)) :
    ∃ r : cyclicInvariants K m q,
      (Spec (invariantRingCat K m q)).presheaf.germ ⊤ (genericPoint _) trivial s =
        toFF K m q r := by
  obtain ⟨r, hr⟩ := exists_eq_germ_top (R := invariantRingCat K m q) s
  exact ⟨r, hr⟩

/-- The prime divisor `C = (x = 0)` of `Spec R`. -/
private noncomputable def primeC (h : IsCyclicQuotientSetting K m q) :
    PrimeDivisor (Spec (invariantRingCat K m q)) :=
  PrimeDivisor.ofCoheightOne (ptOf (xIdeal K m q)) (coheight_ptOf_xIdeal h)

private theorem genericPoint_primeC (h : IsCyclicQuotientSetting K m q) :
    (primeC h).genericPoint = ptOf (xIdeal K m q) :=
  PrimeDivisor.genericPoint_ofCoheightOne _ _

private theorem ne_xIdeal_of_ne (h : IsCyclicQuotientSetting K m q)
    {W : PrimeDivisor (Spec (invariantRingCat K m q))} (hW : W ≠ primeC h) :
    idealOf W.genericPoint ≠ xIdeal K m q := fun e =>
  hW (PrimeDivisor.genericPoint_injective (by
    rw [genericPoint_primeC, ← ptOf_idealOf W.genericPoint]; exact ptOf_congr e))

private theorem eq_primeC_of_genericPoint (h : IsCyclicQuotientSetting K m q)
    {W : PrimeDivisor (Spec (invariantRingCat K m q))} (hW : W.genericPoint = ptOf (xIdeal K m q)) :
    W = primeC h :=
  PrimeDivisor.genericPoint_injective (by rw [hW, genericPoint_primeC])

open scoped Classical in
/-- The Weil divisor `1 · W` of a prime divisor. -/
private noncomputable def singleW (W : PrimeDivisor (Spec (invariantRingCat K m q))) :
    AlgebraicGeometry.WeilDivisor (Spec (invariantRingCat K m q)) :=
  ⟨(Pi.single W (1 : ℤ) : PrimeDivisor (Spec (invariantRingCat K m q)) → ℤ),
    single_mem_weilDivisor _ _⟩

open scoped Classical in
private theorem singleW_apply (W V : PrimeDivisor (Spec (invariantRingCat K m q))) :
    (singleW W).val V = if V = W then 1 else 0 := by
  simp [singleW, Pi.single_apply]

open scoped Classical in
/-- **`m [C] = div(x^m)`.** -/
private theorem divOf_xm (h : IsCyclicQuotientSetting K m q) :
    divOf (toFF K m q (xm h)) (toFF_ne_zero (xm_ne_zero h)) = m • singleW (primeC h) := by
  apply Subtype.ext; funext W
  rw [divOf_apply, AddSubgroup.coe_nsmul, Pi.smul_apply]
  rw [singleW_apply]
  split_ifs with hW
  · subst hW
    rw [genericPoint_primeC, ord_xm_ptOf_xIdeal]; simp
  · rw [smul_zero, ← ptOf_idealOf W.genericPoint]
    exact ord_xm_eq_zero h _ (height_idealOf W.coheight_genericPoint) (ne_xIdeal_of_ne h hW)

private theorem nsmul_mk_primeC (h : IsCyclicQuotientSetting K m q) :
    m • ((singleW (primeC h) : AlgebraicGeometry.WeilDivisor (Spec (invariantRingCat K m q))) :
      weilDivisorClassGroup (Spec (invariantRingCat K m q))) = 0 := by
  rw [← QuotientAddGroup.mk_nsmul, ← divOf_xm h]
  exact mk_divOf _ _

/-- **`k [C]` principal forces `m ∣ k`.** -/
private theorem dvd_of_nsmul_mk_primeC (h : IsCyclicQuotientSetting K m q) (k : ℕ)
    (hk : k • ((singleW (primeC h) :
      AlgebraicGeometry.WeilDivisor (Spec (invariantRingCat K m q))) :
      weilDivisorClassGroup (Spec (invariantRingCat K m q))) = 0) : m ∣ k := by
  classical
  have := isDomain_of_invariantRingCat (K := K) (m := m) (q := q)
  have := isNormal_spec h
  have := isRegularLocalRing_mvPowerSeries_two K
  have : IsDomain (MvPowerSeries (Fin 2) K) := IsRegularLocalRing.isDomain _
  have : UniqueFactorizationMonoid (MvPowerSeries (Fin 2) K) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  have hm0 : m ≠ 0 := by have := h.one_le; omega
  rw [← QuotientAddGroup.mk_nsmul] at hk
  obtain ⟨z, hz, hzk⟩ := exists_of_mk_eq_zero _ hk
  have hordz : ∀ y : Spec (invariantRingCat K m q), coheight y = 1 →
      Scheme.ord z y = if y = ptOf (xIdeal K m q) then (k : ℤ) else 0 := by
    intro y hy
    have e := congrArg (fun D : AlgebraicGeometry.WeilDivisor _ => D.val
        (PrimeDivisor.ofCoheightOne y hy)) hzk
    simp only [divOf_apply, PrimeDivisor.genericPoint_ofCoheightOne, AddSubgroup.coe_nsmul,
      Pi.smul_apply] at e
    rw [e, singleW_apply]
    by_cases hy' : y = ptOf (xIdeal K m q)
    · rw [if_pos (eq_primeC_of_genericPoint h (by
        rw [PrimeDivisor.genericPoint_ofCoheightOne, hy'])), if_pos hy']; simp
    · have : PrimeDivisor.ofCoheightOne y hy ≠ primeC h := fun e' => hy' (by
        rw [← genericPoint_primeC h, ← e', PrimeDivisor.genericPoint_ofCoheightOne])
      rw [if_neg this, if_neg hy']; simp
  set xF := toFF K m q (xm h)
  have hxF : xF ≠ 0 := toFF_ne_zero (xm_ne_zero h)
  set W := z ^ m / xF ^ k with hW
  have hW0 : W ≠ 0 := div_ne_zero (pow_ne_zero _ hz) (pow_ne_zero _ hxF)
  have hordW : ∀ y : Spec (invariantRingCat K m q), coheight y = 1 → Scheme.ord W y = 0 := by
    intro y hy
    rw [hW, ord_div (pow_ne_zero _ hz) (pow_ne_zero _ hxF), Scheme.ord_pow hz, Scheme.ord_pow hxF,
      hordz y hy]
    by_cases hy' : y = ptOf (xIdeal K m q)
    · rw [if_pos hy', hy', ord_xm_ptOf_xIdeal]; ring
    · rw [if_neg hy']
      have hne : idealOf y ≠ xIdeal K m q :=
        fun e => hy' (by rw [← ptOf_idealOf y]; exact ptOf_congr e)
      rw [← ptOf_idealOf y, ord_xm_eq_zero h _ (height_idealOf hy) hne]; ring
  obtain ⟨s, hs⟩ :=
    Stacks.AlgebraicGeometry.UnitsNormalProper.exists_globalUnit_of_forall_ord_eq_zero
      (Units.mk0 W hW0) hordW
  obtain ⟨w, hw⟩ := exists_toFF_eq_germ_top (s : Γ(Spec (invariantRingCat K m q), ⊤))
  obtain ⟨w', hw'⟩ := exists_toFF_eq_germ_top (↑s⁻¹ : Γ(Spec (invariantRingCat K m q), ⊤))
  have hww' : w * w' = 1 := by
    apply toFF_injective
    rw [map_mul, ← hw, ← hw', ← map_mul, Units.mul_inv, map_one, map_one]
  have hwW : toFF K m q w = W := by
    rw [← hw, hs]; rfl
  obtain ⟨a, b, hb0, hab'⟩ := toFF_div_surjective z
  have heq : a ^ m = b ^ m * xm h ^ k * w := by
    apply toFF_injective
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, hwW, hW, ← hab']
    have hb' := toFF_ne_zero (K := K) (m := m) (q := q) hb0
    have hb'' := pow_ne_zero m hb'
    have hx'' := pow_ne_zero k hxF
    rw [div_pow]
    change _ = _ * xF ^ k * _
    field_simp
  have heqA : (a : MvPowerSeries (Fin 2) K) ^ m =
      ((b : MvPowerSeries (Fin 2) K) * MvPowerSeries.X 0 ^ k) ^ m *
        (w : MvPowerSeries (Fin 2) K) := by
    have := congrArg Subtype.val heq
    simp only [SubmonoidClass.coe_pow, Subring.coe_mul] at this
    rw [this, mul_pow, ← pow_mul, mul_comm k m, pow_mul]; rfl
  have hwu : IsUnit (w : MvPowerSeries (Fin 2) K) :=
    IsUnit.of_mul_eq_one (b := (w' : MvPowerSeries (Fin 2) K))
      (by rw [← Subring.coe_mul, hww']; rfl)
  set c := (b : MvPowerSeries (Fin 2) K) * MvPowerSeries.X 0 ^ k
  have hc0 : c ≠ 0 := mul_ne_zero (fun e => hb0 (Subtype.ext e)) (pow_ne_zero _ (X_ne_zero K 0))
  have h1 : c ∣ (a : MvPowerSeries (Fin 2) K) :=
    (IsIntegrallyClosed.pow_dvd_pow_iff hm0).mp ⟨_, heqA⟩
  have h2 : (a : MvPowerSeries (Fin 2) K) ∣ c := by
    refine (IsIntegrallyClosed.pow_dvd_pow_iff hm0).mp ⟨((hwu.unit⁻¹ : _) : MvPowerSeries _ _), ?_⟩
    rw [heqA, mul_assoc, IsUnit.mul_val_inv, mul_one]
  obtain ⟨v, hv⟩ := associated_of_dvd_dvd h1 h2
  have hcw : SemiInv K m q k c := by
    simpa using (semiInv_of_mem b.2).mul
      (semiInv_X_zero_pow (K := K) (m := m) (q := q) k)
  have hvw : SemiInv K m q (0 - k) (v : MvPowerSeries (Fin 2) K) :=
    (hv ▸ semiInv_of_mem a.2).cancel hcw hc0
  have := hvw.dvd_of_isUnit h v.isUnit
  rw [zero_sub, dvd_neg] at this
  exact_mod_cast this

end ClassGroup

section Generation

attribute [local instance] idealOf_isPrime isNoetherianRing_invariantRingCat

variable [IsDomain (invariantRingCat K m q)] [IsNoetherianRing (cyclicInvariants K m q)]

/-- The class `[C]`. -/
private noncomputable def classC (h : IsCyclicQuotientSetting K m q) :
    weilDivisorClassGroup (Spec (invariantRingCat K m q)) :=
  ((singleW (primeC h) : AlgebraicGeometry.WeilDivisor (Spec (invariantRingCat K m q))) :
    weilDivisorClassGroup _)

open scoped Classical in
/-- **Every prime divisor is a multiple of `C` in the class group.** -/
private theorem mk_singleW_mem (h : IsCyclicQuotientSetting K m q)
    (W : PrimeDivisor (Spec (invariantRingCat K m q))) :
    ((singleW W : AlgebraicGeometry.WeilDivisor (Spec (invariantRingCat K m q))) :
      weilDivisorClassGroup _) ∈ AddSubgroup.zmultiples (classC h) := by
  by_cases hWC : W = primeC h
  · subst hWC; exact AddSubgroup.mem_zmultiples _
  have hP := height_idealOf W.coheight_genericPoint
  have hPx := ne_xIdeal_of_ne h hWC
  obtain ⟨t, ht0, ht1, ht⟩ := exists_local_equation h (idealOf W.genericPoint) hP hPx
  have htF := toFF_ne_zero (K := K) (m := m) (q := q) ht0
  have hxF := toFF_ne_zero (K := K) (m := m) (q := q) (xm_ne_zero h)
  set f := toFF K m q t / toFF K m q (xm h)
  have hf : f ≠ 0 := div_ne_zero htF hxF
  set c := Scheme.ord f (primeC h).genericPoint
  have hdiv : divOf f hf = singleW W + c • singleW (primeC h) := by
    apply Subtype.ext; funext V
    rw [divOf_apply, AddSubgroup.coe_add, AddSubgroup.coe_zsmul, Pi.add_apply, Pi.smul_apply]
    change _ = (singleW W).val V + c • (singleW (primeC h)).val V
    rw [singleW_apply, singleW_apply]
    by_cases hVC : V = primeC h
    · subst hVC; rw [if_neg (Ne.symm hWC), if_pos rfl]; simp [c]
    rw [if_neg hVC, smul_zero, add_zero, ord_div htF hxF, ← ptOf_idealOf V.genericPoint,
      ord_xm_eq_zero h _ (height_idealOf V.coheight_genericPoint) (ne_xIdeal_of_ne h hVC)]
    by_cases hVW : V = W
    · subst hVW; rw [if_pos rfl, ht1]; simp
    · rw [if_neg hVW]
      have hne : idealOf V.genericPoint ≠ idealOf W.genericPoint := fun e =>
        hVW (PrimeDivisor.genericPoint_injective (by
          rw [← ptOf_idealOf V.genericPoint, ← ptOf_idealOf W.genericPoint]; exact ptOf_congr e))
      rw [ht _ (height_idealOf V.coheight_genericPoint) hne (ne_xIdeal_of_ne h hVC)]; simp
  have hmk := mk_divOf f hf
  rw [hdiv, QuotientAddGroup.mk_add, QuotientAddGroup.mk_zsmul] at hmk
  refine ⟨-c, ?_⟩
  change -c • classC h = _
  rw [neg_smul, neg_eq_iff_add_eq_zero, add_comm]
  exact hmk

/-- **`[C]` generates the class group.** -/
private theorem zmultiples_classC (h : IsCyclicQuotientSetting K m q) :
    AddSubgroup.zmultiples (classC h) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro g -
  induction g using QuotientAddGroup.induction_on with
  | H D' =>
  have hfin : {Z : PrimeDivisor (Spec (invariantRingCat K m q)) | D'.val Z ≠ 0}.Finite := by
    refine (LocallyFinite.finite_nonempty_of_compact D'.2).subset fun Z hZ => ?_
    simp only [Set.mem_setOf_eq] at hZ ⊢
    rw [if_neg hZ, PrimeDivisor.support_eq_closure]
    exact ⟨_, subset_closure rfl⟩
  suffices key : ∀ (S : Finset (PrimeDivisor (Spec (invariantRingCat K m q)))) (D' :
      AlgebraicGeometry.WeilDivisor _),
      (∀ Z, D'.val Z ≠ 0 → Z ∈ S) →
        ((D' : AlgebraicGeometry.WeilDivisor _) : weilDivisorClassGroup _) ∈
            AddSubgroup.zmultiples (classC h) from
    key hfin.toFinset D' fun Z hZ => hfin.mem_toFinset.mpr hZ
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro D' hD'
    have : D' = 0 := Subtype.ext (funext fun Z => by
      by_contra hne; exact absurd (hD' Z hne) (Finset.notMem_empty _))
    rw [this, QuotientAddGroup.mk_zero]; exact zero_mem _
  | insert Z S hZS ih =>
    intro D' hD'
    set D'' := D' - D'.val Z • singleW Z
    have hD'' : ∀ V, D''.val V ≠ 0 → V ∈ S := by
      intro V hV
      have hV' : V ≠ Z := by
        rintro rfl
        apply hV
        simp only [D'', AddSubgroup.coe_sub, AddSubgroup.coe_zsmul, Pi.sub_apply, Pi.smul_apply]
        change D'.val V - D'.val V • (singleW V).val V = 0
        rw [singleW_apply, if_pos rfl]; simp
      have : D'.val V ≠ 0 := by
        intro h0; apply hV
        simp only [D'', AddSubgroup.coe_sub, AddSubgroup.coe_zsmul, Pi.sub_apply, Pi.smul_apply]
        change D'.val V - D'.val Z • (singleW Z).val V = 0
        rw [singleW_apply, if_neg hV', h0]; simp
      exact (Finset.mem_insert.mp (hD' V this)).resolve_left hV'
    have e : D' = D'' + D'.val Z • singleW Z := by simp [D'']
    rw [e, QuotientAddGroup.mk_add, QuotientAddGroup.mk_zsmul]
    exact add_mem (ih D'' hD'') (zsmul_mem (mk_singleW_mem h Z) _)

/-- The closure of `C`'s generic point is the image of `(x = 0)`. -/
private theorem closure_ptOf_xIdeal (h : IsCyclicQuotientSetting K m q) :
    (TopologicalSpace.Closeds.closure {ptOf (xIdeal K m q)} :
      TopologicalSpace.Closeds (Spec (invariantRingCat K m q))) =
      cyclicQuotientImage h (MvPowerSeries.X 0) := by
  have hP0 : (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)}).IsPrime :=
    (Ideal.span_singleton_prime prime_X_zero.ne_zero).mpr prime_X_zero
  apply TopologicalSpace.Closeds.ext
  change closure ({ptOf (xIdeal K m q)} : Set (Spec (invariantRingCat K m q))) =
    closure ((cyclicQuotientMap h).base '' (PrimeSpectrum.zeroLocus {MvPowerSeries.X 0} :
      Set (PrimeSpectrum (MvPowerSeries (Fin 2) K))))
  have hsub : (cyclicQuotientMap h).base '' (PrimeSpectrum.zeroLocus {MvPowerSeries.X 0} :
      Set (PrimeSpectrum (MvPowerSeries (Fin 2) K))) ⊆
        closure ({ptOf (xIdeal K m q)} : Set (Spec (invariantRingCat K m q))) := by
    rintro _ ⟨P, hP, rfl⟩
    change PrimeSpectrum.comap (cyclicInvariants K m q).subtype P ∈
      closure ({(⟨xIdeal K m q, inferInstance⟩ : PrimeSpectrum (cyclicInvariants K m q))} : Set _)
    rw [← PrimeSpectrum.le_iff_mem_closure]
    intro r hr
    have hX : MvPowerSeries.X 0 ∈ P.asIdeal := hP (Set.mem_singleton _)
    obtain ⟨b, hb⟩ := mem_xIdeal.mp hr
    change (r : MvPowerSeries (Fin 2) K) ∈ P.asIdeal
    rw [hb]; exact P.asIdeal.mul_mem_right _ hX
  have hpt : ptOf (xIdeal K m q) ∈ (cyclicQuotientMap h).base ''
      (PrimeSpectrum.zeroLocus {MvPowerSeries.X 0} :
        Set (PrimeSpectrum (MvPowerSeries (Fin 2) K))) := by
    refine ⟨⟨_, hP0⟩, fun _ hx => ?_, ?_⟩
    · rw [Set.mem_singleton_iff.mp hx]; exact Ideal.subset_span rfl
    · rfl
  exact le_antisymm (closure_mono (Set.singleton_subset_iff.mpr hpt))
    (closure_minimal hsub isClosed_closure)

end Generation

section Characters

variable {K : Type w} [Field K] {m : ℕ} {q : ℤ}

/-- **The characters of `μ_m`.** `k ↦ (ζ ↦ ζ^k)` identifies `ZMod m` with `Hom(μ_m, Kˣ)`. -/
private theorem exists_addEquiv_characters (h : IsCyclicQuotientSetting K m q) :
    ∃ α : ZMod m ≃+ Additive (rootsOfUnity m K →* Kˣ),
      α 1 = Additive.ofMul (rootsOfUnity m K).subtype := by
  have := h.isAlgClosed; have := h.charZero
  have := neZero_of_isCyclicQuotientSetting h
  obtain ⟨ζ', hζ'⟩ := exists_isPrimitiveRoot_rootsOfUnity h
  have hpow : (rootsOfUnity m K).subtype ^ (m : ℤ) = 1 := by
    ext ξ; simp [(mem_rootsOfUnity _ _).mp ξ.2]
  let α := ZMod.lift m (A := Additive (rootsOfUnity m K →* Kˣ))
    ⟨zmultiplesHom _ (Additive.ofMul (rootsOfUnity m K).subtype), by
      rw [zmultiplesHom_apply, ← ofMul_zpow, hpow]; rfl⟩
  have hα : ∀ n : ℤ, α n = Additive.ofMul ((rootsOfUnity m K).subtype ^ n) := fun n => by
    rw [ZMod.lift_coe]
    change zmultiplesHom _ _ n = _
    rw [zmultiplesHom_apply, ofMul_zpow]
  have hζm : ζ' ^ m = 1 := Subtype.ext (by
    simpa using (mem_rootsOfUnity _ _).mp ζ'.2)
  have hinj : Function.Injective α := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
    rw [hα] at hx
    have h0 : (rootsOfUnity m K).subtype ^ n = 1 :=
      Additive.ofMul.injective (hx.trans ofMul_one.symm)
    have h1 := DFunLike.congr_fun h0 ζ'
    simp only [MonoidHom.zpow_apply, Subgroup.coe_subtype, MonoidHom.one_apply] at h1
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd n m).mpr ((hζ'.zpow_eq_one_iff_dvd n).mp h1)
  have hζK : IsPrimitiveRoot (((ζ' : Kˣ)) : K) m := IsPrimitiveRoot.coe_units_iff.mpr hζ'
  have hsurj : Function.Surjective α := by
    intro χ
    have hχ : (((Additive.toMul χ) ζ' : Kˣ) : K) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hζm, map_one, Units.val_one]
    obtain ⟨i, -, hi⟩ := hζK.eq_pow_of_pow_eq_one hχ
    refine ⟨(i : ℤ), ?_⟩
    rw [hα]
    apply Additive.toMul.injective
    rw [toMul_ofMul]
    ext ξ
    have hξm : (((ξ : Kˣ)) : K) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp ξ.2, Units.val_one]
    obtain ⟨j, -, hj⟩ := hζK.eq_pow_of_pow_eq_one hξm
    have hξ : ξ = ζ' ^ j := Subtype.ext (Units.ext (by simpa using hj.symm))
    rw [hξ]
    simp only [MonoidHom.zpow_apply, Subgroup.coe_subtype, map_pow, zpow_natCast,
      Units.val_pow_eq_pow_val, ← hi]
    simp only [MonoidHom.pow_apply, Subgroup.coe_subtype, Units.val_pow_eq_pow_val,
      SubgroupClass.coe_pow, ← pow_mul, mul_comm]
  refine ⟨AddEquiv.ofBijective α ⟨hinj, hsurj⟩, ?_⟩
  have := hα 1
  rw [Int.cast_one, zpow_one] at this
  exact this

end Characters

section Final

attribute [local instance] idealOf_isPrime isNoetherianRing_invariantRingCat

variable {K : Type w} [Field K] {m : ℕ} {q : ℤ}
variable [IsDomain (invariantRingCat K m q)] [IsNoetherianRing (cyclicInvariants K m q)]

open scoped Classical in
/-- **The class group of `Spec R`**: `[C]` has order `m`, generates, and the characters of
`μ_m` identify with it, the character of `x` going to `[C]`. -/
private theorem exists_addEquiv_weilDivisorClassGroup_spec
    (h : IsCyclicQuotientSetting K m q) :
    ∃ (C : PrimeDivisor (Spec (invariantRingCat K m q)))
      (D : AlgebraicGeometry.WeilDivisor (Spec (invariantRingCat K m q))),
      C.idealSheaf =
          Scheme.IdealSheafData.vanishingIdeal (cyclicQuotientImage h (MvPowerSeries.X 0)) ∧
        (D : PrimeDivisor (Spec (invariantRingCat K m q)) → ℤ) = Pi.single C 1 ∧
        (∃ e : Additive (rootsOfUnity m K →* Kˣ) ≃+
            weilDivisorClassGroup (Spec (invariantRingCat K m q)),
          e (Additive.ofMul (rootsOfUnity m K).subtype) = D) ∧
        addOrderOf (D : weilDivisorClassGroup (Spec (invariantRingCat K m q))) = m ∧
        AddSubgroup.zmultiples (D : weilDivisorClassGroup (Spec (invariantRingCat K m q))) = ⊤ := by
  have hm : 0 < m := h.one_le
  have F1 := nsmul_mk_primeC h
  have F2 := dvd_of_nsmul_mk_primeC h
  have F3 := zmultiples_classC h
  refine ⟨primeC h, singleW (primeC h), ?_, rfl, ?_, ?_, F3⟩
  · change Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure {ptOf (xIdeal K m q)}) = _
    rw [closure_ptOf_xIdeal h]
    rfl
  · obtain ⟨α, hα⟩ := exists_addEquiv_characters h
    let β := ZMod.lift m (A := weilDivisorClassGroup (Spec (invariantRingCat K m q)))
      ⟨zmultiplesHom _ (classC h), by
        rw [zmultiplesHom_apply, natCast_zsmul]; exact F1⟩
    have hβ : ∀ n : ℤ, β n = n • classC h := fun n => by
      rw [ZMod.lift_coe]; rfl
    have hinj : Function.Injective β := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
      rw [hβ] at hx
      have hn : n.natAbs • classC h = 0 := by
        rcases Int.natAbs_eq n with e | e
        · rw [← natCast_zsmul, ← e]; exact hx
        · rw [← natCast_zsmul, show ((n.natAbs : ℕ) : ℤ) = -n by omega, neg_smul, hx, neg_zero]
      have := F2 _ hn
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd n m).mpr (Int.natCast_dvd.mpr this)
    have hsurj : Function.Surjective β := by
      intro g
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (F3 ▸ AddSubgroup.mem_top g)
      exact ⟨n, by rw [hβ, hn]⟩
    refine ⟨α.symm.trans (AddEquiv.ofBijective β ⟨hinj, hsurj⟩), ?_⟩
    rw [AddEquiv.trans_apply, ← hα, AddEquiv.symm_apply_apply]
    change β 1 = _
    have := hβ 1
    rw [Int.cast_one, one_zsmul] at this
    exact this
  · rw [addOrderOf_eq_iff hm]
    refine ⟨F1, fun k hk hk0 hkd => ?_⟩
    exact absurd (Nat.le_of_dvd hk0 (F2 k hkd)) (by omega)

end Final

end CharacterClasses

open scoped Classical in
/-- The character group of `μ_m` is the Weil divisor class group of `Spec R`, the character
of `x` going to the class of the reduced image of `(x = 0)`, which generates it with order `m`. -/
private theorem cyclicInvariants_characterClasses
    {K : Type w} [Field K] {m : ℕ} {q : ℤ} (h : IsCyclicQuotientSetting K m q) :
    letI : IsDomain (cyclicInvariants K m q) := NoZeroDivisors.to_isDomain _
    letI : IsIntegral (cyclicQuotientModel K m q h) := (affine_isIntegral_iff _).mpr this
    ∀ hR : IsNoetherianRing (cyclicInvariants K m q),
      letI : IsLocallyNoetherian (cyclicQuotientModel K m q h) := isLocallyNoetherian_Spec.mpr hR
      ∃ (C : PrimeDivisor (cyclicQuotientModel K m q h))
        (D : AlgebraicGeometry.WeilDivisor (cyclicQuotientModel K m q h)),
        C.idealSheaf =
            Scheme.IdealSheafData.vanishingIdeal (cyclicQuotientImage h (MvPowerSeries.X 0)) ∧
          (D : PrimeDivisor (cyclicQuotientModel K m q h) → ℤ) = Pi.single C 1 ∧
          (∃ e : Additive (rootsOfUnity m K →* Kˣ) ≃+
              weilDivisorClassGroup (cyclicQuotientModel K m q h),
            e (Additive.ofMul (rootsOfUnity m K).subtype) = D) ∧
          addOrderOf (D : weilDivisorClassGroup (cyclicQuotientModel K m q h)) = m ∧
          AddSubgroup.zmultiples
              (D : weilDivisorClassGroup (cyclicQuotientModel K m q h)) = ⊤ := by
  intro hR
  have : IsDomain (invariantRingCat K m q) :=
    (NoZeroDivisors.to_isDomain (cyclicInvariants K m q) : _)
  exact exists_addEquiv_weilDivisorClassGroup_spec h

end MMP.Proofs.lem_mmp_formal_cyclic_quotient_character_classes

namespace MMP.Flips

open scoped Classical in
open MMP.Proofs.lem_mmp_formal_cyclic_quotient_character_classes in
/-- **Characters classify the divisor classes of a formal cyclic quotient.** In the setting of
`MMP.Flips.IsCyclicQuotientSetting`, the invariant ring `R = K[[x, y]]^{μ_m}` is a normal
Noetherian local domain of dimension two over which `K[[x, y]]` is finite; over the punctured
spectrum `K[[x, y]]` is a finite étale `μ_m`-torsor; and there is an isomorphism from the
character group `Hom(μ_m, Kˣ)` to the Weil divisor class group of `T_{m,q} = Spec R` sending the
character `ζ ↦ ζ` of `x` to the class of the prime divisor `C^{(1)}_{m,q}`, the reduced image of
`(x = 0)`, whose class has order `m` and generates the class group. -/
@[mmp "lem_mmp_formal_cyclic_quotient_character_classes"]
public theorem exists_addEquiv_weilDivisorClassGroup_cyclicQuotientModel
    {K : Type u} [Field K] {m : ℕ} {q : ℤ} (h : IsCyclicQuotientSetting K m q) :
    letI : IsDomain (cyclicInvariants K m q) := NoZeroDivisors.to_isDomain _
    letI : IsIntegral (cyclicQuotientModel K m q h) := (affine_isIntegral_iff _).mpr this
    ∃ hR : IsNoetherianRing (cyclicInvariants K m q),
      letI : IsLocallyNoetherian (cyclicQuotientModel K m q h) := isLocallyNoetherian_Spec.mpr hR
      IsLocalRing (cyclicInvariants K m q) ∧ IsDomain (cyclicInvariants K m q) ∧
      IsIntegrallyClosed (cyclicInvariants K m q) ∧
      ringKrullDim (cyclicInvariants K m q) = 2 ∧
      Module.Finite (cyclicInvariants K m q) (MvPowerSeries (Fin 2) K) ∧
      (∀ (𝔭 : Ideal (cyclicInvariants K m q)) [𝔭.IsPrime], ¬ 𝔭.IsMaximal →
        (letI := localizationAlgebra 𝔭.primeCompl (MvPowerSeries (Fin 2) K)
            (Rₘ := Localization.AtPrime 𝔭)
            (Sₘ := Localization (Algebra.algebraMapSubmonoid (MvPowerSeries (Fin 2) K)
              𝔭.primeCompl));
          Algebra.Etale (Localization.AtPrime 𝔭)
            (Localization (Algebra.algebraMapSubmonoid (MvPowerSeries (Fin 2) K)
              𝔭.primeCompl))) ∧
        Function.Bijective (LocalizedModule.map 𝔭.primeCompl
          (Algebra.TensorProduct.productMap
            ((Algebra.ofId (MvPowerSeries (Fin 2) K)
              (rootsOfUnity m K → MvPowerSeries (Fin 2) K)).restrictScalars
                (cyclicInvariants K m q))
            (Pi.algHom (cyclicInvariants K m q) (fun _ : rootsOfUnity m K =>
                MvPowerSeries (Fin 2) K)
              fun ζ => AlgHom.mk (MvPowerSeries.rescale (cyclicWeights K m q ζ))
                fun r => (mem_cyclicInvariants_iff K m q r).mp r.2 ζ)).toLinearMap)) ∧
      ∃ (C : PrimeDivisor (cyclicQuotientModel K m q h))
        (D : AlgebraicGeometry.WeilDivisor (cyclicQuotientModel K m q h)),
        C.idealSheaf =
            Scheme.IdealSheafData.vanishingIdeal (cyclicQuotientImage h (MvPowerSeries.X 0)) ∧
          (D : PrimeDivisor (cyclicQuotientModel K m q h) → ℤ) = Pi.single C 1 ∧
          (∃ e : Additive (rootsOfUnity m K →* Kˣ) ≃+
              weilDivisorClassGroup (cyclicQuotientModel K m q h),
            e (Additive.ofMul (rootsOfUnity m K).subtype) = D) ∧
          addOrderOf (D : weilDivisorClassGroup (cyclicQuotientModel K m q h)) = m ∧
          AddSubgroup.zmultiples
              (D : weilDivisorClassGroup (cyclicQuotientModel K m q h)) = ⊤ := by
  have hR := isNoetherianRing_cyclicInvariants h
  exact ⟨hR, isLocalRing_cyclicInvariants K m q, NoZeroDivisors.to_isDomain _,
    isIntegrallyClosed_cyclicInvariants, ringKrullDim_cyclicInvariants h,
    module_finite_cyclicInvariants h, cyclicInvariants_puncturedTorsor h,
    cyclicInvariants_characterClasses h hR⟩

/-! ### Reflexive powers of rank one reflexive modules -/

section ReflexivePowers

open CoherentReflexive
open Stacks.AlgebraicGeometry.ReflexiveModules (reflexiveHullFunctor)
open Stacks.AlgebraicGeometry.ReflexiveHull (CoherentReflexiveModules inclusion)
open Stacks.AlgebraicGeometry.ModuleReflexivePower (reflexivePower)

attribute [local instance] rankOneSkeletonCommMonoid

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The reflexive powers `ℱ^{[n]}` of a rank one coherent reflexive module, taken in the
subcategory of rank one modules: `ℱ^{[0]} = 𝒪_X` and `ℱ^{[n + 1]} = (ℱ ⊗ ℱ^{[n]})^∨∨`. -/
private noncomputable def rankOnePow (F : RankOneReflexiveModules X) :
    ℕ → RankOneReflexiveModules X
  | 0 => rankOneUnitObj X
  | n + 1 => rankOneTensorObj F (rankOnePow F n)

/-- `rankOnePow` is the reflexive power of the underlying `𝒪_X`-module. -/
private noncomputable def rankOnePowIso (F : RankOneReflexiveModules X) : (n : ℕ) →
    ((rankOnePow F n).obj.obj.obj ≅
      Stacks.AlgebraicGeometry.ReflexivePowers.reflexivePower F.obj.obj.obj n)
  | 0 => Iso.refl _
  | 1 => (inclusion X ⋙ ObjectProperty.ι _).mapIso (tensorObjUnit F.obj)
  | n + 2 => (reflexiveHullFunctor X).mapIso
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F.obj.obj.obj).mapIso
          (rankOnePowIso F (n + 1)))

/-- The class of `ℱ^{[n]}` is the `n`-th power of the class of `ℱ`. -/
private theorem toSkeleton_rankOnePow (F : RankOneReflexiveModules X) (n : ℕ) :
    toSkeleton (rankOnePow F n) = toSkeleton F ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', ← ih]
    exact (rankOneSkeletonMul_toSkeleton F _).symm

/-- **Reflexive powers on a normal domain with `n`-torsion class group.** Let `R` be a
Noetherian domain with `Spec R` normal and `Cl(Spec R)` killed by `n`. Then the `n`-th reflexive
power of every finite reflexive `R`-module of rank one is free of rank one (via the
identification of `Cl(Spec R)` with rank one reflexive modules, [Stacks, Tag 0EBM]). -/
public theorem nonempty_linearEquiv_reflexivePower_of_nsmul_eq_zero {R : CommRingCat.{u}}
    [IsDomain R] [IsNoetherianRing R] [IsNormal (Spec R)] {n : ℕ}
    (hn : ∀ c : weilDivisorClassGroup (Spec R), n • c = 0) (N : ModuleCat.{u} R)
    [Module.Finite R N] [Module.IsReflexive R N] (hN : Module.rank R N = 1) :
    Nonempty (reflexivePower N n ≃ₗ[R] R) := by
  have : (tilde N).IsCoherent := tilde_isCoherent_of_finite N
  have hrk : HasRankOne (⟨⟨tilde N, this⟩, isReflexive_tilde N⟩ :
      CoherentReflexiveModules (Spec R)) := by
    change Scheme.Modules.fiberRank (tilde N) _ = 1
    rw [Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk]
    exact Module.finrank_eq_of_rank_eq ((rank_stalk_tilde N _).trans (by simpa using hN))
  let F : RankOneReflexiveModules (Spec R) := ⟨_, hrk⟩
  have h1 : toSkeleton (rankOnePow F n) = toSkeleton (rankOneUnitObj (Spec R)) := by
    rw [toSkeleton_rankOnePow]
    apply rankOneSkeletonMulEquivWeilDivisorClass.injective
    rw [map_pow, rankOneSkeletonMulEquivWeilDivisorClass_apply, ← ofAdd_nsmul, hn, ofAdd_zero]
    exact (map_one rankOneSkeletonMulEquivWeilDivisorClass).symm
  obtain ⟨e⟩ := toSkeleton_eq_toSkeleton_iff.1 h1
  let e' := (rankOnePowIso F n).symm ≪≫
    (ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ ObjectProperty.ι _).mapIso e ≪≫ tildeSelf.symm
  exact ⟨((tilde.functor R).preimageIso
    ((reflexivePowerTildeIso R N n).symm ≪≫ e')).toLinearEquiv⟩

/-- **A normal domain whose rank one reflexive modules have free `n`-th reflexive powers has
`n`-torsion class group.** If the `n`-th reflexive power of every finite reflexive `R`-module
of rank one is free, then `Cl(Spec R)` is killed by `n`. This is the converse of
`MMP.Flips.nonempty_linearEquiv_reflexivePower_of_nsmul_eq_zero`. -/
public theorem nsmul_eq_zero_of_nonempty_linearEquiv_reflexivePower {R : CommRingCat.{u}}
    [IsDomain R] [IsNoetherianRing R] [IsNormal (Spec R)] {n : ℕ}
    (h : ∀ (N : ModuleCat.{u} R) [Module.Finite R N] [Module.IsReflexive R N],
      Module.rank R N = 1 → Nonempty (reflexivePower N n ≃ₗ[R] R))
    (c : weilDivisorClassGroup (Spec R)) : n • c = 0 := by
  obtain ⟨s, rfl⟩ := rankOneSkeletonToWeilClass_surjective c
  rw [← toSkeleton_fromSkeleton_obj s]
  set F := (fromSkeleton _).obj s
  let G : (Spec R).Modules := F.obj.obj.obj
  have : G.IsCoherent := F.obj.obj.property
  obtain ⟨_, _⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G
  let N := moduleSpecΓFunctor.obj G
  have : Module.Finite R N := Stacks.AlgebraicGeometry.PushforwardCoherent.finite_moduleSpecΓ G
  let e : tilde N ≅ G :=
    @asIso _ _ _ _ G.fromTildeΓ ((isQuasicoherent_iff_isIso_fromTildeΓ G).mp ‹_›)
  have : Module.IsReflexive R N := by
    have hj : IsIso (Stacks.AlgebraicGeometry.ReflexiveModules.toDoubleDual (tilde N)) :=
      Stacks.AlgebraicGeometry.ReflexiveModules.isReflexive_of_iso e.symm F.obj.property
    have : IsIso ((tilde.functor R).map (ModuleCat.ofHom (Module.Dual.eval R N))) := by
      change IsIso (tilde.map _)
      rw [← toDoubleDual_reflexiveHullTildeIso]; infer_instance
    have : IsIso (ModuleCat.ofHom (Module.Dual.eval R N)) :=
      isIso_of_reflects_iso _ (tilde.functor R)
    exact ⟨(asIso (ModuleCat.ofHom (Module.Dual.eval R N))).toLinearEquiv.bijective⟩
  have hcoh : (tilde N).IsCoherent := tilde_isCoherent_of_finite N
  have hrk : HasRankOne (⟨⟨tilde N, hcoh⟩, isReflexive_tilde N⟩ :
      CoherentReflexiveModules (Spec R)) :=
    (Scheme.Modules.fiberRank_eq_of_iso e _).trans F.property
  have hN : Module.rank R N = 1 := by
    have h1 : Module.finrank _ _ = 1 :=
      (Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk (tilde N)).symm.trans hrk
    exact (rank_stalk_tilde N _).symm.trans (Module.rank_eq_one_iff_finrank_eq_one.mpr h1)
  let F' : RankOneReflexiveModules (Spec R) := ⟨_, hrk⟩
  have hF : toSkeleton F' = toSkeleton F := toSkeleton_eq_toSkeleton_iff.2
    ⟨(ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ ObjectProperty.ι _).preimageIso e⟩
  obtain ⟨ℓ⟩ := h N hN
  have h1 : toSkeleton (rankOnePow F' n) = toSkeleton (rankOneUnitObj (Spec R)) :=
    toSkeleton_eq_toSkeleton_iff.2 ⟨(ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙
      ObjectProperty.ι _).preimageIso (rankOnePowIso F' n ≪≫ reflexivePowerTildeIso R N n ≪≫
        (tilde.functor R).mapIso ℓ.toModuleIso ≪≫ tildeSelf)⟩
  rw [toSkeleton_rankOnePow, hF] at h1
  apply_fun rankOneSkeletonMulEquivWeilDivisorClass at h1
  rw [map_pow, rankOneSkeletonMulEquivWeilDivisorClass_apply, ← ofAdd_nsmul] at h1
  exact Multiplicative.ofAdd.injective
    (h1.trans (map_one rankOneSkeletonMulEquivWeilDivisorClass))

end ReflexivePowers

/-- The invariant ring `K[[x, y]]^{μ_m}` is Noetherian. -/
public theorem isNoetherianRing_cyclicInvariants {K : Type u} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) : IsNoetherianRing (cyclicInvariants K m q) :=
  MMP.Proofs.lem_mmp_formal_cyclic_quotient_character_classes.isNoetherianRing_cyclicInvariants h

/-- **The class group of `T_{m,q}` is killed by `m`.** -/
public theorem nsmul_eq_zero_weilDivisorClassGroup_cyclicQuotientModel {K : Type u} [Field K]
    {m : ℕ} {q : ℤ} (h : IsCyclicQuotientSetting K m q) :
    letI : IsDomain (cyclicInvariants K m q) := NoZeroDivisors.to_isDomain _
    letI : IsIntegral (cyclicQuotientModel K m q h) := (affine_isIntegral_iff _).mpr this
    letI : IsLocallyNoetherian (cyclicQuotientModel K m q h) :=
      isLocallyNoetherian_Spec.mpr (isNoetherianRing_cyclicInvariants h)
    ∀ c : weilDivisorClassGroup (cyclicQuotientModel K m q h), m • c = 0 := by
  intro c
  obtain ⟨_, -, -, -, -, -, -, _, D, -, -, -, hD, hgen⟩ :=
    exists_addEquiv_weilDivisorClassGroup_cyclicQuotientModel h
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgen ▸ AddSubgroup.mem_top c)
  rw [smul_comm, addOrderOf_dvd_iff_nsmul_eq_zero.mp hD.dvd, smul_zero]

section ClassGroupIso

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNoetherian X] [IsNoetherian Y]

/-- **The class group is invariant under isomorphisms.** An isomorphism `e : X ≅ Y` of
Noetherian integral schemes induces `Cl(Y) ≃+ Cl(X)`, given by restricting classes along
`e.hom`. -/
@[expose] public noncomputable def weilDivisorClassGroupEquivOfIso (e : X ≅ Y) :
    weilDivisorClassGroup Y ≃+ weilDivisorClassGroup X :=
  AddEquiv.ofBijective (OpenWeilRestriction.restrictClass e.hom)
    ⟨by
      rw [← AddMonoidHom.ker_eq_bot_iff, OpenWeilRestriction.ker_restrictClass e.hom
        (ι := Empty) Empty.elim (fun a => a.elim) fun Z => ?_]
      · simp
      · simp only [Set.range_eq_empty, Set.mem_empty_iff_false, iff_false, not_not]
        refine (OpenWeilRestriction.mem_range_primeDivisorMap_iff e.hom Z).mpr ?_
        exact ⟨e.inv Z.genericPoint, by simp [← Scheme.Hom.comp_apply]⟩,
      OpenWeilRestriction.surjective_restrictClass e.hom⟩

/-- The isomorphism `weilDivisorClassGroupEquivOfIso e` sends a class to its restriction along
`e.hom`. -/
@[simp] public theorem weilDivisorClassGroupEquivOfIso_apply (e : X ≅ Y)
    (c : weilDivisorClassGroup Y) :
    weilDivisorClassGroupEquivOfIso e c = OpenWeilRestriction.restrictClass e.hom c :=
  rfl

end ClassGroupIso

/-- **The class group of a ring isomorphic to `K[[x, y]]^{μ_m}` is killed by `m`.** For a ring
isomorphism `φ : K[[x, y]]^{μ_m} ≃+* T`, `Spec φ` is an isomorphism `Spec T ≅ T_{m,q}`, so
`Cl(Spec T) ≅ Cl(T_{m,q})` (`MMP.Flips.weilDivisorClassGroupEquivOfIso`) is killed by `m`
(`MMP.Flips.nsmul_eq_zero_weilDivisorClassGroup_cyclicQuotientModel`). -/
public theorem nsmul_eq_zero_weilDivisorClassGroup_of_ringEquiv {K : Type u} [Field K] {m : ℕ}
    {q : ℤ} (h : IsCyclicQuotientSetting K m q) {T : Type u} [CommRing T]
    (φ : cyclicInvariants K m q ≃+* T) :
    letI : IsDomain (cyclicInvariants K m q) := NoZeroDivisors.to_isDomain _
    letI : IsDomain T := φ.symm.toMulEquiv.isDomain _
    letI : IsIntegral (Spec (CommRingCat.of T)) := (affine_isIntegral_iff _).mpr this
    letI : IsLocallyNoetherian (Spec (CommRingCat.of T)) :=
      haveI := isNoetherianRing_cyclicInvariants h
      isLocallyNoetherian_Spec.mpr (isNoetherianRing_of_ringEquiv _ φ)
    ∀ c : weilDivisorClassGroup (Spec (CommRingCat.of T)), m • c = 0 := by
  have : IsDomain (cyclicInvariants K m q) := NoZeroDivisors.to_isDomain _
  have : IsDomain T := φ.symm.toMulEquiv.isDomain _
  have := isNoetherianRing_cyclicInvariants h
  have : IsNoetherianRing T := isNoetherianRing_of_ringEquiv _ φ
  intro c
  let e : Spec (CommRingCat.of T) ≅ cyclicQuotientModel K m q h :=
    Scheme.Spec.mapIso φ.toCommRingCatIso.op
  obtain ⟨c, rfl⟩ := (weilDivisorClassGroupEquivOfIso e).surjective c
  rw [← map_nsmul, nsmul_eq_zero_weilDivisorClassGroup_cyclicQuotientModel h, map_zero]

/-- **Reflexive powers over a ring isomorphic to `K[[x, y]]^{μ_m}`.** For a ring isomorphism
`φ : K[[x, y]]^{μ_m} ≃+* T` and every finite reflexive `T`-module `N` of rank one, `N^{[m]}` is
isomorphic to `T`: `T` is a Noetherian normal domain, being isomorphic to one, and its class
group is killed by `m` (`MMP.Flips.nsmul_eq_zero_weilDivisorClassGroup_of_ringEquiv`). -/
public theorem nonempty_linearEquiv_reflexivePower_of_ringEquiv {K : Type u} [Field K] {m : ℕ}
    {q : ℤ} (h : IsCyclicQuotientSetting K m q) {T : Type u} [CommRing T]
    (φ : cyclicInvariants K m q ≃+* T) (N : Type u) [AddCommGroup N] [Module T N]
    [Module.Finite T N] [Module.IsReflexive T N] (hN : Module.rank T N = 1) :
    Nonempty (Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePower
      (ModuleCat.of (CommRingCat.of T) N) m ≃ₗ[T] T) := by
  have : IsDomain (cyclicInvariants K m q) := NoZeroDivisors.to_isDomain _
  have : IsDomain T := φ.symm.toMulEquiv.isDomain _
  have := isNoetherianRing_cyclicInvariants h
  have : IsNoetherianRing T := isNoetherianRing_of_ringEquiv _ φ
  have : IsIntegrallyClosed (cyclicInvariants K m q) :=
    (exists_addEquiv_weilDivisorClassGroup_cyclicQuotientModel h).2.2.2.1
  have : IsIntegrallyClosed T := IsIntegrallyClosed.of_equiv φ
  have : IsNormal (Spec (CommRingCat.of T)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed _)
  exact nonempty_linearEquiv_reflexivePower_of_nsmul_eq_zero
    (nsmul_eq_zero_weilDivisorClassGroup_of_ringEquiv h φ) _ hN

/-- **The `m`-th reflexive power of a rank one reflexive module over `K[[x, y]]^{μ_m}` is
free.** For every finite reflexive module `N` of rank one over `R = K[[x, y]]^{μ_m}`, the
reflexive power `N^{[m]}` (`N^{[1]} = N`, `N^{[k + 1]} = (N ⊗_R N^{[k]})^∨∨`) is isomorphic to
`R`: the class group `Cl(T_{m,q})` is killed by `m`
(`MMP.Flips.nsmul_eq_zero_weilDivisorClassGroup_cyclicQuotientModel`). This is
`MMP.Flips.nonempty_linearEquiv_reflexivePower_of_ringEquiv` for the identity of `R`. -/
public theorem nonempty_linearEquiv_reflexivePower_cyclicInvariants {K : Type u} [Field K]
    {m : ℕ} {q : ℤ} (h : IsCyclicQuotientSetting K m q) (N : Type u) [AddCommGroup N]
    [Module (cyclicInvariants K m q) N] [Module.Finite (cyclicInvariants K m q) N]
    [Module.IsReflexive (cyclicInvariants K m q) N]
    (hN : Module.rank (cyclicInvariants K m q) N = 1) :
    Nonempty (Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePower
        (ModuleCat.of (CommRingCat.of (cyclicInvariants K m q)) N) m ≃ₗ[cyclicInvariants K m q]
      cyclicInvariants K m q) :=
  nonempty_linearEquiv_reflexivePower_of_ringEquiv h (RingEquiv.refl _) N hN

end MMP.Flips

end

/-!
## Generic snc compatibility for the blow-up of a smooth centre

Let `Y` be a smooth variety over a field `k`, `D` an snc divisor on `Y`, and `Z = V(I)` a smooth
irreducible closed subscheme of codimension `c ≥ 2` with generic point `η`. At most `c`
components of `D` contain `Z`: the snc condition at `η` embeds the components through `η` into a
regular system of parameters of `𝒪_{Y,η}`, whose length is `dim 𝒪_{Y,η} = c`. Each component
containing `Z` is smooth, in particular at `η`. After shrinking `Y` to an open set meeting `Z`
and only the components containing `Z`, the blow-up is smooth and the exceptional divisor
together with the strict transforms is snc. The restriction of `D` to `U` is the transform
`MMP.Mori.inverseTransformDivisor U.ι D`; the snc conclusion is stated for `a F + π⁻¹_*(D|_U)`
with an arbitrary coefficient `a` of the exceptional divisor `F`.
-/

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP MMP.Mori MMP.Resolution

variable {k : Type u} [Field k] {Y : Scheme.{u}}

namespace MMP.Proofs.lem_mmp_threefold_smooth_blowup_generic_snc

/-- The generic point of an irreducible closed set lies on a closed set exactly when the whole
set does. -/
private theorem genericPoint_mem_iff {S : Set Y} (hS : IsIrreducible S) (hcl : IsClosed S)
    {T : Set Y} (hT : IsClosed T) : hS.genericPoint ∈ T ↔ S ⊆ T :=
  (hS.isGenericPoint_genericPoint hcl).mem_closed_set_iff hT

open Classical in
/-- At most `c` components of an snc divisor contain an irreducible closed subset of
codimension `c`. -/
private theorem card_filter_le_codimension {R : Type*} [AddCommMonoid R]
    {D : DivisorWithCoeffs R Y} (sY : Y ⟶ Spec (.of k)) (hD : D.IsSNC sY)
    (I : Y.IdealSheafData) (hirr : IsIrreducible (I.support : Set Y)) :
    ((D.support.filter fun E => (I.support : Set Y) ⊆ E.support).card : ℕ∞) ≤
      codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) := by
  set η := hirr.genericPoint
  obtain ⟨n, z, j, hz, hj, -⟩ := hD.2 η
  have hcard : (D.support.filter fun E => (I.support : Set Y) ⊆ E.support).card ≤ n := by
    let g : (D.support.filter fun E => (I.support : Set Y) ⊆ E.support) →
        {E : MMP.Mori.PrimeDivisor Y // E ∈ D.support ∧ η ∈ E.support} := fun E =>
      ⟨E.1, (Finset.mem_filter.mp E.2).1, (genericPoint_mem_iff hirr I.support.isClosed
        E.1.idealSheaf.support.isClosed).mpr (Finset.mem_filter.mp E.2).2⟩
    have hg : Function.Injective g := fun a b h => Subtype.ext (congrArg (fun x => x.1) h :)
    simpa using Fintype.card_le_of_injective _ (hj.comp hg)
  have hcodim : codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) =
      n := by
    have heq : (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) =
        IrreducibleCloseds.closureSingleton η := by
      ext1; exact (hirr.isGenericPoint_genericPoint I.support.isClosed).symm
    have h2 := hz.2
    rw [ringKrullDim_stalk_eq_coheight] at h2
    rw [heq, Stacks.Divisors.PrimeDivisor.codimension_closureSingleton]
    exact_mod_cast h2
  rw [hcodim]; exact_mod_cast hcard

/-- A component of an snc divisor containing an irreducible closed subset `Z` is smooth at the
generic point of `Z`. -/
private theorem exists_mem_smoothLocus_genericPoint {R : Type*} [AddCommMonoid R]
    {D : DivisorWithCoeffs R Y} (sY : Y ⟶ Spec (.of k)) (hD : D.IsSNC sY)
    (I : Y.IdealSheafData) (hirr : IsIrreducible (I.support : Set Y)) :
    ∀ E ∈ D.support, (I.support : Set Y) ⊆ E.support →
      ∃ ζ : E.idealSheaf.subscheme, E.idealSheaf.subschemeι ζ = hirr.genericPoint ∧
        ζ ∈ smoothLocus (E.idealSheaf.subschemeι ≫ sY) := by
  intro E hE hsub
  have hmem : hirr.genericPoint ∈ (E.idealSheaf.support : Set Y) :=
    (genericPoint_mem_iff hirr I.support.isClosed E.idealSheaf.support.isClosed).mpr hsub
  rw [← E.idealSheaf.range_subschemeι] at hmem
  obtain ⟨ζ, hζ⟩ := hmem
  refine ⟨ζ, hζ, ?_⟩
  have h := hD.1 E hE
  unfold IsSmoothScheme at h
  rw [h]; trivial

open Classical in
/-- The complement of the components of `D` not containing `Z` is an open set meeting `Z`, and
every component of `D` meeting it contains `Z`. -/
private theorem exists_open_forall_subset {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Y) (I : Y.IdealSheafData) (hirr : IsIrreducible (I.support : Set Y)) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ I.support).Nonempty ∧
      ∀ E ∈ D.support, ((E.support : Set Y) ∩ U).Nonempty →
        (I.support : Set Y) ⊆ E.support := by
  set T := D.support.filter fun E => ¬ (I.support : Set Y) ⊆ E.support
  have hT : IsClosed (⋃ E ∈ T, (E.idealSheaf.support : Set Y)) :=
    T.finite_toSet.isClosed_biUnion fun E _ => E.idealSheaf.support.isClosed
  refine ⟨⟨_, hT.isOpen_compl⟩, ⟨hirr.genericPoint, ?_, ?_⟩, fun E hE ⟨x, hxE, hxU⟩ => ?_⟩
  · simp only [Opens.coe_mk, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro E hE hmem
    exact (Finset.mem_filter.mp hE).2 ((genericPoint_mem_iff hirr I.support.isClosed
      E.idealSheaf.support.isClosed).mp hmem)
  · exact (hirr.isGenericPoint_genericPoint I.support.isClosed).mem
  · by_contra hn
    exact hxU (Set.mem_biUnion (Finset.mem_filter.mpr ⟨hE, hn⟩) hxE)

/-- A morphism smooth at every point is smooth. -/
private theorem smooth_of_isSmoothScheme {X S : Scheme.{u}} {f : X ⟶ S}
    (h : IsSmoothScheme f) : Smooth f := by
  have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
    (fun U : {U : X.Opens // Smooth (U.ι ≫ f)} => U.1) ?_ fun U => U.2
  rw [← h, MMP.Mori.smoothLocus, sSup_eq_iSup']
  rfl

/-- A smooth blow-up restricts to a smooth blow-up over an open subscheme. -/
private theorem isSmoothBlowup_comap (sY : Y ⟶ Spec (.of k)) (I : Y.IdealSheafData)
    (h : IsSmoothBlowup sY I) (U : Y.Opens) : IsSmoothBlowup (U.ι ≫ sY) (I.comap U.ι) := by
  have : Smooth sY := smooth_of_isSmoothScheme h.1
  have : Smooth (I.subschemeι ≫ sY) := smooth_of_isSmoothScheme h.2
  refine ⟨top_le_iff.mp (MMP.Mori.le_smoothLocus _ (U := ⊤) inferInstance), ?_⟩
  have : LocallyOfFinitePresentation (I.subschemeι ≫ sY) :=
    instLocallyOfFinitePresentationOfSmooth _
  have h2 : MMP.Mori.smoothLocus (I.subschemeι ≫ sY) = ⊤ := h.2
  rw [MMP.Mori.smoothLocus_eq_smoothLocus] at h2
  exact (MMP.Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff U.ι sY I
    (I.comap U.ι) rfl).mpr fun z _ => by
      change z ∈ ((I.subschemeι ≫ sY).smoothLocus : Set _); rw [h2]; trivial

/-- The centre `Z ∩ U` of the restricted blow-up is irreducible. -/
private theorem isIrreducible_support_comap (I : Y.IdealSheafData)
    (hirr : IsIrreducible (I.support : Set Y)) (U : Y.Opens)
    (hU : ((U : Set Y) ∩ I.support).Nonempty) :
    IsIrreducible ((I.comap U.ι).support : Set U) := by
  rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]
  obtain ⟨y, hyU, hyZ⟩ := hU
  refine ⟨⟨⟨y, hyU⟩, hyZ⟩, ?_⟩
  exact hirr.2.preimage U.ι.isOpenEmbedding

/-- The restricted centre `Z ∩ U` has codimension at least one in `U` when `Z` has codimension at
least one in the integral scheme `Y`. -/
private theorem one_le_codimension_support_comap [IsIntegral Y] (I : Y.IdealSheafData)
    (hirr : IsIrreducible (I.support : Set Y))
    (hc : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (U : Y.Opens) (hU : ((U : Set Y) ∩ I.support).Nonempty)
    (hirr' : IsIrreducible ((I.comap U.ι).support : Set U)) :
    1 ≤ codimension (⟨(I.comap U.ι).support, hirr', (I.comap U.ι).support.isClosed⟩ :
      IrreducibleCloseds U) := by
  obtain ⟨y, hyU, -⟩ := hU
  have hne : Nonempty {x // x ∈ (U : Set Y)} := ⟨⟨y, hyU⟩⟩
  have hUirr : IrreducibleSpace U :=
    (IsOpen.isOpenEmbedding_subtypeVal U.isOpen).irreducibleSpace
  refine ENat.one_le_iff_ne_zero.mpr fun h0 => ?_
  have hmax := Order.coheight_eq_zero.mp h0
  have hle := hmax (b := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩)
    (fun x _ => trivial)
  have hsub : (U : Set Y) ⊆ I.support := fun x hx => by
    have : (⟨x, hx⟩ : U) ∈ ((I.comap U.ι).support : Set U) := hle (Set.mem_univ _)
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage] at this
    exact this
  have hall : (I.support : Set Y) = Set.univ := by
    have hd : Dense (U : Set Y) := U.isOpen.dense ⟨y, hyU⟩
    exact Set.eq_univ_of_univ_subset
      (hd.closure_eq ▸ closure_minimal hsub I.support.isClosed)
  refine absurd hc (not_le.mpr ?_)
  have : codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) = 0 :=
    Order.coheight_eq_zero.mpr fun b _ => fun x _ => by
      change x ∈ (I.support : Set Y); rw [hall]; trivial
  rw [this]; exact zero_lt_one

/-- **Partial parameters extend to generators of a regular quotient.** Let `R` be a regular local
ring, `x₁, …, x_l, w₁, …, w_n` a regular system of parameters and `J ⊇ (x₁, …, x_l)` an ideal with
`R / J` regular. Then there are `y₁, …, y_k` and `t₁, …, t_m` such that
`x₁, …, x_l, y₁, …, y_k, t₁, …, t_m` is a regular system of parameters and
`J = (x₁, …, x_l, y₁, …, y_k)`. -/
private theorem exists_isRegularSystemOfParameters_append_span_eq {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {l n : ℕ} {x : Fin l → R} {w : Fin n → R}
    (hx : MMP.Mori.IsRegularSystemOfParameters (Fin.append x w)) {J : Ideal R}
    (hxJ : Ideal.span (Set.range x) ≤ J) (hJ : IsRegularLocalRing (R ⧸ J)) :
    ∃ (k m : ℕ) (y : Fin k → R) (t : Fin m → R),
      MMP.Mori.IsRegularSystemOfParameters (Fin.append (Fin.append x y) t) ∧
        Ideal.span (Set.range (Fin.append x y)) = J := by
  set I := Ideal.span (Set.range x)
  obtain ⟨hreg, hdimI, -⟩ :=
    MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_of_isRegularSystemOfParameters_append hx
  have hIne : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  have hcomap : ∀ K : Ideal R, I ≤ K →
      (K.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = K := fun K hK => by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hK]
  set J' := J.map (Ideal.Quotient.mk I)
  let e : (R ⧸ I) ⧸ J' ≃+* R ⧸ J := DoubleQuot.quotQuotEquivQuotOfLE hxJ
  have hJ' : IsRegularLocalRing ((R ⧸ I) ⧸ J') := IsRegularLocalRing.of_ringEquiv e.symm
  obtain ⟨k, h', hh'J, hk'dim⟩ :=
      MMP.Flips.ResolutionInputs.exists_fin_span_eq_of_isRegularLocalRing_quotient J' hJ'
  obtain ⟨m, t', htt⟩ := (MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_and_add_eq_iff
      h').mp
    ⟨by rw [hh'J]; exact hJ', by rw [hh'J]; exact hk'dim⟩
  choose y hy using fun i => Ideal.Quotient.mk_surjective (I := I) (h' i)
  choose t ht using fun j => Ideal.Quotient.mk_surjective (I := I) (t' j)
  have hmapx : (Ideal.span (Set.range x)).map (Ideal.Quotient.mk I) = ⊥ :=
    Ideal.map_quotient_self I
  have hmapy : (Ideal.span (Set.range y)).map (Ideal.Quotient.mk I) =
      Ideal.span (Set.range h') := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    exact hy i
  have hmapt : (Ideal.span (Set.range t)).map (Ideal.Quotient.mk I) =
      Ideal.span (Set.range t') := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext j
    exact ht j
  have hIxy : I ≤ Ideal.span (Set.range (Fin.append x y)) := by
    rw [MMP.Flips.ResolutionInputs.span_range_append]; exact le_sup_left
  have hxyJ : Ideal.span (Set.range (Fin.append x y)) = J := by
    rw [← hcomap _ hIxy, ← hcomap _ hxJ]
    congr 1
    rw [MMP.Flips.ResolutionInputs.span_range_append, Ideal.map_sup, hmapx, bot_sup_eq, hmapy, hh'J]
  refine ⟨k, m, y, t, ⟨?_, ?_⟩, hxyJ⟩
  · have hIK : I ≤ Ideal.span (Set.range (Fin.append (Fin.append x y) t)) := by
      rw [MMP.Flips.ResolutionInputs.span_range_append]; exact le_sup_of_le_left hIxy
    rw [← hcomap _ hIK, ← hcomap _ (IsLocalRing.le_maximalIdeal hIne),
      IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, ← htt.1]
    congr 1
    rw [MMP.Flips.ResolutionInputs.span_range_append,
        MMP.Flips.ResolutionInputs.span_range_append, Ideal.map_sup, Ideal.map_sup, hmapx,
      bot_sup_eq, hmapy, hmapt, MMP.Flips.ResolutionInputs.span_range_append]
  · rw [← hdimI, htt.2]
    push_cast
    ring

/-- A regular system of parameters stays one after reindexing by an equivalence. -/
private theorem isRegularSystemOfParameters_comp_equiv {R : Type*} [CommRing R] [IsLocalRing R]
    {n m : ℕ} {z : Fin n → R} (hz : MMP.Mori.IsRegularSystemOfParameters z) (τ : Fin m ≃ Fin n) :
    MMP.Mori.IsRegularSystemOfParameters (z ∘ τ) := by
  have hmn : m = n := by simpa using Fintype.card_congr τ
  refine ⟨?_, ?_⟩
  · rw [Set.range_comp, τ.range_eq_univ, Set.image_univ]; exact hz.1
  · rw [hz.2, hmn]

/-- **Coordinates adapted to a smooth centre.** Let `z` be a regular system of parameters of a
regular local ring `R`, `j : S → Fin n` injective, and `J` an ideal containing the `z (j s)` with
`R / J` regular. Then there is a regular system of parameters `v` containing the `z (j s)` such
that `J` is generated by a subfamily of `v`. -/
private theorem exists_coordinates_extend {R : Type*} [CommRing R] [IsRegularLocalRing R]
    {S : Type*} [Fintype S] {n : ℕ} {z : Fin n → R} (hz : MMP.Mori.IsRegularSystemOfParameters z)
    {j : S → Fin n} (hj : Function.Injective j) {J : Ideal R} (hJ : ∀ s, z (j s) ∈ J)
    (hreg : IsRegularLocalRing (R ⧸ J)) :
    ∃ (N : ℕ) (v : Fin N → R) (c : S → Fin N) (T : Finset (Fin N)),
      MMP.Mori.IsRegularSystemOfParameters v ∧ Function.Injective c ∧
        (∀ s, v (c s) = z (j s)) ∧ J = Ideal.span (v '' (T : Set (Fin N))) := by
  classical
  set l := Fintype.card S
  let e : S ≃ Fin l := Fintype.equivFin S
  let W := {i : Fin n // i ∉ Set.range j}
  let m := Fintype.card W
  let e' : W ≃ Fin m := Fintype.equivFin W
  let σ : Fin l ⊕ Fin m → Fin n := Sum.elim (fun a => j (e.symm a)) (fun b => (e'.symm b).1)
  have hσ : Function.Bijective σ := by
    constructor
    · rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (e.symm.injective (hj h))
      · exact absurd ⟨_, h⟩ (e'.symm b).2
      · exact absurd ⟨_, h.symm⟩ (e'.symm a).2
      · exact congrArg Sum.inr (e'.symm.injective (Subtype.ext h))
    · intro i
      by_cases hi : i ∈ Set.range j
      · obtain ⟨s, rfl⟩ := hi
        exact ⟨Sum.inl (e s), by simp [σ]⟩
      · exact ⟨Sum.inr (e' ⟨i, hi⟩), by simp [σ]⟩
  let τ : Fin (l + m) ≃ Fin n := finSumFinEquiv.symm.trans (Equiv.ofBijective σ hσ)
  let x : Fin l → R := fun a => z (j (e.symm a))
  let w : Fin m → R := fun b => z (e'.symm b).1
  have happ : Fin.append x w = z ∘ τ := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp [τ, σ, x, w]
  have hxw : MMP.Mori.IsRegularSystemOfParameters (Fin.append x w) :=
    happ ▸ isRegularSystemOfParameters_comp_equiv hz τ
  have hxJ : Ideal.span (Set.range x) ≤ J :=
    Ideal.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact hJ _)
  obtain ⟨k, m', y, t, hv, hspan⟩ :=
    exists_isRegularSystemOfParameters_append_span_eq hxw hxJ hreg
  refine ⟨l + k + m', Fin.append (Fin.append x y) t,
    fun s => Fin.castAdd m' (Fin.castAdd k (e s)), Finset.univ.image (Fin.castAdd m'), hv,
    fun a b h => by simpa using h, fun s => by simp [x], ?_⟩
  rw [← hspan, Finset.coe_image, Finset.coe_univ, Set.image_univ, ← Set.range_comp]
  congr 2
  funext i
  simp [Fin.append_left]

/-- A closed subscheme smooth over a field is reduced. -/
private theorem isReduced_subscheme_of_isSmoothScheme {X : Scheme.{u}} (s : X ⟶ Spec (.of k))
    (T : X.IdealSheafData) (hT : IsSmoothScheme (T.subschemeι ≫ s)) : IsReduced T.subscheme := by
  have : Smooth (T.subschemeι ≫ s) := smooth_of_isSmoothScheme hT
  have hreg := isRegular_of_smooth_over_field (T.subschemeι ≫ s)
  have : ∀ x : T.subscheme, _root_.IsReduced (T.subscheme.presheaf.stalk x) := fun x => by
    have := hreg.isRegularLocalRing_stalk x
    have := IsRegularLocalRing.isDomain (T.subscheme.presheaf.stalk x)
    exact isReduced_of_noZeroDivisors
  exact isReduced_of_isReduced_stalk _

/-- An ideal sheaf whose closed subscheme is smooth over a field contains the ideal sheaf of every
closed subscheme whose support contains its support. -/
private theorem le_of_support_subset {X : Scheme.{u}} (s : X ⟶ Spec (.of k))
    (T : X.IdealSheafData) (hT : IsSmoothScheme (T.subschemeι ≫ s)) (E : X.IdealSheafData)
    (h : (T.support : Set X) ⊆ E.support) : E ≤ T := by
  have := isReduced_subscheme_of_isSmoothScheme s T hT
  rw [← MMP.Mori.vanishingIdeal_support_eq_self T]
  exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp h

/-- The second projection of `X ×_Y Z` is an isomorphism when `f : X ⟶ Y` is a monomorphism
through which `g : Z ⟶ Y` factors. -/
private theorem isIso_pullback_snd_of_factors {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
    [Mono f] (h : Z ⟶ X) (hh : h ≫ f = g) : IsIso (Limits.pullback.snd f g) := by
  subst hh; infer_instance

/-- If `E ≤ Z`, the centre `Z` restricted to the closed subscheme `E` is smooth when `Z` is. -/
private theorem isSmoothScheme_comap_subschemeι {X : Scheme.{u}} (s : X ⟶ Spec (.of k))
    (Z E : X.IdealSheafData) (hZ : IsSmoothScheme (Z.subschemeι ≫ s)) (hEZ : E ≤ Z) :
    IsSmoothScheme ((Z.comap E.subschemeι).subschemeι ≫ E.subschemeι ≫ s) := by
  have hiso := isIso_pullback_snd_of_factors E.subschemeι Z.subschemeι
    (Scheme.IdealSheafData.inclusion hEZ) (Scheme.IdealSheafData.inclusion_subschemeι hEZ)
  have e : (Z.comap E.subschemeι).subschemeι ≫ E.subschemeι ≫ s =
      ((Z.comapIso E.subschemeι).hom ≫ Limits.pullback.snd _ _) ≫ Z.subschemeι ≫ s := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Category.assoc,
      Limits.pullback.condition_assoc]
  rw [e]
  have : Smooth (Z.subschemeι ≫ s) := smooth_of_isSmoothScheme hZ
  exact MMP.Resolution.isSmoothScheme_of_smooth _

/-- **The strict transform of a smooth integral subscheme along a smooth centre is smooth**, over
any field. Let `Z ⊆ X` be a closed subscheme smooth over `k` and `E ⊆ X` an integral closed
subscheme smooth over `k` with `E ≤ Z` (so `Z ⊆ E`) and `E ⊄ Z`. Then the closure of
`π⁻¹(E ∖ Z)` in the blow-up `π : B_Z X → X`, with its reduced structure, is smooth over `k`: it is
the blow-up of `E` along `Z`. -/
private theorem isSmoothScheme_strictTransform {X : Scheme.{u}} (s : X ⟶ Spec (.of k))
    (Z E : X.IdealSheafData) (hZ : IsSmoothScheme (Z.subschemeι ≫ s)) [IsIntegral E.subscheme]
    (hE : IsSmoothScheme (E.subschemeι ≫ s)) (hEZ : E ≤ Z)
    (hnot : ¬ (E.support : Set X) ⊆ Z.support) :
    IsSmoothScheme ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
      (blowUpToBase Z ⁻¹' ((E.support : Set X) \ Z.support)))).subschemeι ≫
        blowUpToBase Z ≫ s) := by
  obtain ⟨-, hker⟩ :=
    MMP.Resolution.Bridges.range_canonicalLift_eq_closure_and_ker_eq_vanishingIdeal
      E.subschemeι Z (by rwa [E.range_subschemeι])
  rw [E.range_subschemeι] at hker
  rw [← hker]
  set f := MMP.Resolution.canonicalLift E.subschemeι Z
  have : IsClosedImmersion f := MMP.Resolution.Bridges.isClosedImmersion_canonicalLift _ Z
  have hb : IsSmoothBlowup (E.subschemeι ≫ s) (Z.comap E.subschemeι) :=
    ⟨hE, isSmoothScheme_comap_subschemeι s Z E hZ hEZ⟩
  have hsm := (MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup
    _ _ hb).1
  have e : f.ker.subschemeι ≫ blowUpToBase Z ≫ s =
      inv f.toImage ≫ blowUpToBase (Z.comap E.subschemeι) ≫ E.subschemeι ≫ s := by
    rw [IsIso.eq_inv_comp, ← Category.assoc (blowUpToBase _) E.subschemeι s,
      ← MMP.Resolution.canonicalLift_comp_blowUpToBase, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun g => (g ≫ blowUpToBase Z) ≫ s) (Scheme.Hom.toImage_imageι f)
  rw [e]
  exact MMP.Resolution.isSmoothScheme_of_smooth _

/-- The inclusion of an open subscheme is biregular over that open. -/
private theorem le_biregularLocus_ι (U : Y.Opens) : U ≤ MMP.Mori.biregularLocus U.ι := by
  refine MMP.Mori.le_biregularLocus ?_
  change IsIso (U.ι ∣_ U)
  rw [isIso_iff_isOpenImmersion_and_epi_base]
  refine ⟨inferInstance, (TopCat.epi_iff_surjective _).mpr ?_⟩
  intro v
  have hv : v ∈ U.ι ⁻¹ᵁ U := by rw [Scheme.Opens.ι_preimage_self]; trivial
  let p : (U.ι ⁻¹ᵁ U).toScheme := ⟨v, hv⟩
  refine ⟨p, U.ι.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  rfl

/-- The transform of a closed set under the inverse of the inclusion of an open is its
preimage. -/
private theorem coe_inverseTransform_ι (U : Y.Opens) (Q : Closeds Y) :
    (MMP.Mori.inverseTransform U.ι Q : Set U) = U.ι ⁻¹' (Q : Set Y) := by
  have h : U.ι ⁻¹' ((Q : Set Y) ∩ MMP.Mori.biregularLocus U.ι) = U.ι ⁻¹' (Q : Set Y) := by
    ext u
    exact ⟨fun h => h.1, fun h => ⟨h, le_biregularLocus_ι U u.2⟩⟩
  rw [MMP.Mori.inverseTransform, Closeds.coe_closure, h,
    (Q.isClosed.preimage U.ι.continuous).closure_eq]

/-- The transform of an irreducible closed set `A ⊄ Z` under the inverse of the blow-up of `Z` is
the closure of the preimage of `A ∖ Z`. -/
private theorem coe_inverseTransform_blowUpToBase {X : Scheme.{u}} (Z : X.IdealSheafData)
    (A : Closeds X) (hA : IsIrreducible (A : Set X)) (hnot : ¬ (A : Set X) ⊆ Z.support) :
    (MMP.Mori.inverseTransform (blowUpToBase Z) A : Set (blowUp Z)) =
      closure (blowUpToBase Z ⁻¹' ((A : Set X) \ Z.support)) := by
  have hZB : ∀ x, x ∉ (Z.support : Set X) → x ∈ MMP.Mori.biregularLocus (blowUpToBase Z) :=
    fun x hx => MMP.Mori.le_biregularLocus (isIso_blowUp_restrict_compl_support Z) hx
  rw [MMP.Mori.inverseTransform, Closeds.coe_closure]
  apply subset_antisymm
  · refine closure_minimal ?_ isClosed_closure
    rintro w ⟨hwA, hwB⟩
    have hg := hA.isGenericPoint_genericPoint A.isClosed
    have hηw : hA.genericPoint ⤳ blowUpToBase Z w := hg.specializes hwA
    have hηZ : hA.genericPoint ∉ (Z.support : Set X) := fun h =>
      hnot ((hg.mem_closed_set_iff Z.support.isClosed).mp h)
    have hηB : hA.genericPoint ∈ MMP.Mori.biregularLocus (blowUpToBase Z) :=
      hηw.mem_open (MMP.Mori.biregularLocus (blowUpToBase Z)).isOpen hwB
    obtain ⟨ξ, hξ⟩ := exists_blowUpToBase_eq_of_notMem_support Z hηZ
    have hξw : ξ ⤳ w := MMP.Threefold.Resolution.specializes_of_mem_biregularLocus
      (blowUpToBase Z) (by rw [hξ]; exact hηB) hwB (by rw [hξ]; exact hηw)
    have hξT : ξ ∈ blowUpToBase Z ⁻¹' ((A : Set X) \ Z.support) := by
      change blowUpToBase Z ξ ∈ (A : Set X) \ Z.support
      rw [hξ]
      exact ⟨hg.mem, hηZ⟩
    exact closure_mono (Set.singleton_subset_iff.mpr hξT)
      (specializes_iff_mem_closure.mp hξw)
  · exact closure_mono fun w hw => ⟨hw.1, hZB _ hw.2⟩

private theorem mem_support_comap_ι (U : Y.Opens) (T : Y.IdealSheafData) (u : U.toScheme) :
    u ∈ (T.comap U.ι).support ↔ U.ι u ∈ T.support := by
  rw [Scheme.IdealSheafData.support_comap]
  rfl

private theorem stalk_comap_ι (U : Y.Opens) (T : Y.IdealSheafData) (u : U.toScheme) :
    IdealSheafData.stalk (T.comap U.ι) u =
      (IdealSheafData.stalk T (U.ι u)).map
        (MMP.Threefold.Mori.OpenRestriction.stalkEquivOfOpenImmersion U.ι u) := by
  rw [MMP.Threefold.Mori.OpenRestriction.stalkEquivOfOpenImmersion_coe,
    MMP.Threefold.Mori.OpenRestriction.stalk_comap_eq_map]

/-- The components of `D` meeting `U`, restricted to `U`. -/
private noncomputable def compFamily {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R Y)
    (U : Y.Opens) :
    {Q : MMP.Mori.PrimeDivisor Y // Q ∈ D.support ∧ ((Q.support : Set Y) ∩ U).Nonempty} →
      U.toScheme.IdealSheafData :=
  fun Q => Q.1.idealSheaf.comap U.ι

/-- Local coordinates for the restriction of an snc divisor to an open. -/
private theorem exists_coordinates_compFamily (sY : Y ⟶ Spec (.of k)) {R : Type*}
    [AddCommMonoid R] {D : DivisorWithCoeffs R Y} (hD : D.IsSNC sY) (U : Y.Opens)
    (u : U.toScheme) :
    ∃ (n : ℕ) (z : Fin n → U.toScheme.presheaf.stalk u)
      (c : {i // u ∈ (compFamily D U i).support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (compFamily D U i.1) u = Ideal.span {z (c i)}) ∧
          Function.Injective c := by
  obtain ⟨n, z, j, hz, hj, hI⟩ := hD.2 (U.ι u)
  let φ := MMP.Threefold.Mori.OpenRestriction.stalkEquivOfOpenImmersion U.ι u
  let g : {i // u ∈ (compFamily D U i).support} →
      {E : MMP.Mori.PrimeDivisor Y // E ∈ D.support ∧ U.ι u ∈ E.support} :=
    fun i => ⟨i.1.1, i.1.2.1, (mem_support_comap_ι U _ u).mp i.2⟩
  refine ⟨n, fun a => φ (z a), fun i => j (g i),
    MMP.Resolution.isRegularSystemOfParameters_map_ringEquiv φ hz, fun i => ?_, ?_⟩
  · rw [compFamily, stalk_comap_ι, hI (g i), Ideal.map_span, Set.image_singleton]
  · intro a b hab
    have := hj hab
    exact Subtype.ext (Subtype.ext (congrArg (fun E => E.1) this))

/-- The restriction of an snc divisor to an open is an snc family there. -/
private theorem isSNCFamily_compFamily (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    {R : Type*} [AddCommMonoid R] {D : DivisorWithCoeffs R Y} (hD : D.IsSNC sY)
    (U : Y.Opens) : IsSNCFamily (U.ι ≫ sY) (compFamily D U) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hpar : ∀ i, ∀ y ∈ (compFamily D U i).support,
      ∃ (m : ℕ) (w : Fin m → U.toScheme.presheaf.stalk y) (j : Fin m),
        MMP.Mori.IsRegularSystemOfParameters w ∧
          IdealSheafData.stalk (compFamily D U i) y = Ideal.span {w j} := by
    intro i y hy
    obtain ⟨n, z, c, hz, hc, -⟩ := exists_coordinates_compFamily sY hD U y
    exact ⟨n, z, c ⟨i, hy⟩, hz, hc ⟨i, hy⟩⟩
  refine ⟨fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hpar i),
    isPureCodimOne_support_of_stalk_eq_span_parameter _ (hpar i), ?_⟩,
    exists_coordinates_compFamily sY hD U⟩
  have : LocallyOfFinitePresentation (i.1.idealSheaf.subschemeι ≫ sY) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType
      (f := i.1.idealSheaf.subschemeι ≫ sY)).mpr inferInstance
  have h2 : MMP.Mori.smoothLocus (i.1.idealSheaf.subschemeι ≫ sY) = ⊤ := hD.1 i.1 i.2.1
  rw [MMP.Mori.smoothLocus_eq_smoothLocus] at h2
  exact (MMP.Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff U.ι sY i.1.idealSheaf
    (compFamily D U i) rfl).mpr fun z _ => by
      change z ∈ ((i.1.idealSheaf.subschemeι ≫ sY).smoothLocus : Set _)
      rw [h2]; trivial

/-- The centre restricted to `U` has simple normal crossings with the restriction of `D`, when
every component of `D` meeting `U` contains the centre. -/
private theorem hasSNCWith_compFamily (sY : Y ⟶ Spec (.of k)) (I : Y.IdealSheafData)
    (h : IsSmoothBlowup sY I) {R : Type*} [AddCommMonoid R] {D : DivisorWithCoeffs R Y}
    (hD : D.IsSNC sY) (U : Y.Opens)
    (hUD : ∀ E ∈ D.support, ((E.support : Set Y) ∩ U).Nonempty →
      (I.support : Set Y) ⊆ E.support) :
    HasSNCWith (compFamily D U) (I.comap U.ι) := by
  classical
  intro u hu
  have hy : U.ι u ∈ I.support := (mem_support_comap_ι U I u).mp hu
  obtain ⟨n, z, j, hz, hj, hI⟩ := hD.2 (U.ι u)
  have : Finite {E : MMP.Mori.PrimeDivisor Y // E ∈ D.support ∧ U.ι u ∈ E.support} :=
    Finite.of_injective (fun E => (⟨E.1, E.2.1⟩ : D.support))
      fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)
  have := Fintype.ofFinite {E : MMP.Mori.PrimeDivisor Y // E ∈ D.support ∧ U.ι u ∈ E.support}
  have : Smooth sY := smooth_of_isSmoothScheme h.1
  have : IsRegularLocalRing (Y.presheaf.stalk (U.ι u)) :=
    (isRegular_of_smooth_over_field sY).isRegularLocalRing_stalk _
  have hRJ : IsRegularLocalRing
      (Y.presheaf.stalk (U.ι u) ⧸ IdealSheafData.stalk I (U.ι u)) := by
    obtain ⟨ζ, hζ⟩ : ∃ ζ, I.subschemeι ζ = U.ι u := by
      rw [← SetLike.mem_coe, ← I.range_subschemeι] at hy
      exact hy
    have : Smooth (I.subschemeι ≫ sY) := smooth_of_isSmoothScheme h.2
    have := (isRegular_of_smooth_over_field (I.subschemeι ≫ sY)).isRegularLocalRing_stalk ζ
    rw [← hζ]
    exact IsRegularLocalRing.of_ringEquiv
      (MMP.Flips.ResolutionInputs.stalkQuotientEquiv I ζ).symm
  have hJ : ∀ E, z (j E) ∈ IdealSheafData.stalk I (U.ι u) := fun E => by
    have hle := le_of_support_subset sY I h.2 E.1.idealSheaf
      (hUD E.1 E.2.1 ⟨U.ι u, E.2.2, u.2⟩)
    refine MMP.Flips.ResolutionInputs.stalk_mono hle (U.ι u) ?_
    rw [hI E]
    exact Ideal.subset_span rfl
  obtain ⟨N, v, c, T, hv, hc, hvc, hT⟩ := exists_coordinates_extend hz hj hJ hRJ
  let φ := MMP.Threefold.Mori.OpenRestriction.stalkEquivOfOpenImmersion U.ι u
  let g : {i // u ∈ (compFamily D U i).support} →
      {E : MMP.Mori.PrimeDivisor Y // E ∈ D.support ∧ U.ι u ∈ E.support} :=
    fun i => ⟨i.1.1, i.1.2.1, (mem_support_comap_ι U _ u).mp i.2⟩
  refine ⟨N, fun a => φ (v a), fun i => c (g i), T,
    MMP.Resolution.isRegularSystemOfParameters_map_ringEquiv φ hv, fun i => ?_, ?_, ?_⟩
  · rw [compFamily, stalk_comap_ι, hI (g i), ← hvc, Ideal.map_span, Set.image_singleton]
  · intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun E => E.1) (hc hab)))
  · rw [stalk_comap_ι, hT, Ideal.map_span, Set.image_image]

/-- A prime divisor in the support of a transform of divisors is the transform of a prime divisor
in the support. -/
private theorem exists_of_mem_support_mapPrimeDivisors {X X' : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor X'))
    (D : DivisorWithCoeffs R X) {P : MMP.Mori.PrimeDivisor X'}
    (hP : P ∈ (MMP.Mori.DivisorWithCoeffs.mapPrimeDivisors φ D).support) :
    ∃ Q ∈ D.support, φ Q = some P := by
  classical
  by_contra hne
  push Not at hne
  refine (Finsupp.mem_support_iff.mp hP) ?_
  rw [MMP.Mori.DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply, Finsupp.sum,
    Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun Q hQ => ?_
  cases hφ : φ Q with
  | none => simp
  | some P₀ =>
    have hne' : P₀ ≠ P := fun e => hne Q hQ (e ▸ hφ)
    simp [hne']

/-- The transform of a component `Q` of `D` along the inclusion of `U` is the restriction of `Q`
to `U`, and `Q` meets `U`. -/
private theorem idealSheaf_eq_compFamily (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    {R : Type*} [AddCommMonoid R] {D : DivisorWithCoeffs R Y} (hD : D.IsSNC sY) (U : Y.Opens)
    {Q : MMP.Mori.PrimeDivisor Y} (hQ : Q ∈ D.support) {P' : MMP.Mori.PrimeDivisor U.toScheme}
    (hP' : MMP.Mori.inverseTransformPrimeDivisor U.ι Q = some P') :
    ∃ hQU : ((Q.support : Set Y) ∩ U).Nonempty,
      P'.idealSheaf = compFamily D U ⟨Q, hQ, hQU⟩ := by
  have hsupp : (P'.support : Set U.toScheme) = U.ι ⁻¹' (Q.support : Set Y) := by
    rw [MMP.Mori.support_inverseTransformPrimeDivisor hP']
    exact coe_inverseTransform_ι U _
  have hQU : ((Q.support : Set Y) ∩ U).Nonempty := by
    have hmem : P'.genericPoint ∈ (P'.support : Set U.toScheme) := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    rw [hsupp] at hmem
    exact ⟨_, hmem, P'.genericPoint.2⟩
  refine ⟨hQU, ?_⟩
  have := ((isSNCFamily_compFamily sY hD U).1 ⟨Q, hQ, hQU⟩).1
  rw [(MMP.Mori.inverseTransformPrimeDivisor_eq_some_iff.mp hP').2,
    MMP.Mori.inverseTransformIdeal,
    ← MMP.Mori.vanishingIdeal_support_eq_self (compFamily D U ⟨Q, hQ, hQU⟩)]
  congr 1
  apply Closeds.ext
  rw [coe_inverseTransform_ι, compFamily, Scheme.IdealSheafData.support_comap,
    Closeds.coe_preimage]

/-- A component of `D` meeting `U` and containing the centre `Z` of codimension `≥ 2` is not
contained in `Z` on `U`. -/
private theorem not_subset_support_compFamily {R : Type*} [AddCommMonoid R]
    {D : DivisorWithCoeffs R Y} (U : Y.Opens) (I : Y.IdealSheafData)
    (hirr : IsIrreducible (I.support : Set Y))
    (hc : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (hUD : ∀ E ∈ D.support, ((E.support : Set Y) ∩ U).Nonempty →
      (I.support : Set Y) ⊆ E.support)
    (l : {Q : MMP.Mori.PrimeDivisor Y // Q ∈ D.support ∧ ((Q.support : Set Y) ∩ U).Nonempty}) :
    ¬ ((compFamily D U l).support : Set U.toScheme) ⊆ (I.comap U.ι).support := by
  intro hsub
  obtain ⟨y, hyQ, hyU⟩ := l.2.2
  have hηy : l.1.genericPoint ⤳ y := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hyQ
  have hηU : l.1.genericPoint ∈ U := hηy.mem_open U.isOpen hyU
  obtain ⟨u, hu⟩ : l.1.genericPoint ∈ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
  have huQ : u ∈ (compFamily D U l).support := by
    rw [compFamily, mem_support_comap_ι, hu]
    change l.1.genericPoint ∈ (l.1.support : Set Y)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hηI : l.1.genericPoint ∈ (I.support : Set Y) := by
    have := (mem_support_comap_ι U I u).mp (hsub huQ)
    rwa [hu] at this
  have hQI : (l.1.support : Set Y) ⊆ I.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact (I.support.isClosed.closure_subset_iff).mpr (Set.singleton_subset_iff.mpr hηI)
  have heq : (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) =
      IrreducibleCloseds.closureSingleton l.1.genericPoint := by
    ext1
    change (I.support : Set Y) = closure {l.1.genericPoint}
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_antisymm (hUD l.1 l.2.1 l.2.2) hQI
  rw [heq, l.1.codimension_closureSingleton_genericPoint] at hc
  norm_num at hc

/-- **Snc of the exceptional divisor and the strict transforms.** Let `U` be an open set meeting
`Z` such that every component of `D` meeting `U` contains `Z`, and `F` the exceptional prime
divisor of the blow-up of `Z ∩ U`. Then `a F` plus the strict transform of `D|_U` is snc for
every `a`: at a point of `Z ∩ U` the components of `D` through it contain `Z`, so their
equations `x₁, …, x_l` extend to a regular system of parameters in which `Z = (x₁, …, x_c)`, and
on the blow-up chart of `x_j` the divisors through a point are coordinate hyperplanes of
`x_j, x_i / x_j`. -/
private theorem isSNC_single_add_inverseTransformDivisor
    (sY : Y ⟶ Spec (.of k)) (hY : MMP.Mori.IsVariety k sY)
    (I : Y.IdealSheafData) (h : IsSmoothBlowup sY I) (hirr : IsIrreducible (I.support : Set Y))
    (hc : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    {R : Type*} [AddCommMonoid R] {D : DivisorWithCoeffs R Y} (hD : D.IsSNC sY) (U : Y.Opens)
    (hUD : ∀ E ∈ D.support, ((E.support : Set Y) ∩ U).Nonempty →
      (I.support : Set Y) ⊆ E.support)
    (F : MMP.Mori.PrimeDivisor (blowUp (I.comap U.ι)))
    (hF : F.idealSheaf = exceptionalIdeal (I.comap U.ι)) (a : R) :
    DivisorWithCoeffs.IsSNC (blowUpToBase (I.comap U.ι) ≫ U.ι ≫ sY)
      (Finsupp.single F a + inverseTransformDivisor (blowUpToBase (I.comap U.ι))
        (inverseTransformDivisor U.ι D)) := by
  classical
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : QuasiCompact sY := hY.toQuasiCompact
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := {}
  have : CompactSpace U.toScheme :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (U : Set Y))
  have hb := isSmoothBlowup_comap sY I h U
  have hfam := isSNCFamily_compFamily sY hD U
  have hZ := hasSNCWith_compFamily sY I h hD U hUD
  have hcases : ∀ P ∈ (Finsupp.single F a + inverseTransformDivisor (blowUpToBase (I.comap U.ι))
        (inverseTransformDivisor U.ι D)).support,
      P = F ∨ ∃ l, ∃ P' : MMP.Mori.PrimeDivisor U.toScheme,
      P'.idealSheaf = compFamily D U l ∧
        MMP.Mori.inverseTransformPrimeDivisor (blowUpToBase (I.comap U.ι)) P' = some P := by
    intro P hP
    rcases Finset.mem_union.1 (Finsupp.support_add hP) with h1 | h1
    · exact Or.inl (Finset.mem_singleton.1 (Finsupp.support_single_subset h1))
    · obtain ⟨P', hP', hP'P⟩ := exists_of_mem_support_mapPrimeDivisors
        (MMP.Mori.inverseTransformPrimeDivisor (blowUpToBase (I.comap U.ι))) _ h1
      obtain ⟨Q, hQ, hQP'⟩ := exists_of_mem_support_mapPrimeDivisors
        (MMP.Mori.inverseTransformPrimeDivisor U.ι) _ hP'
      obtain ⟨hQU, hP'eq⟩ := idealSheaf_eq_compFamily sY hD U hQ hQP'
      exact Or.inr ⟨⟨Q, hQ, hQU⟩, P', hP'eq, hP'P⟩
  have hstrict : ∀ l (P' : MMP.Mori.PrimeDivisor U.toScheme)
      (P : MMP.Mori.PrimeDivisor (blowUp (I.comap U.ι))), P'.idealSheaf = compFamily D U l →
      MMP.Mori.inverseTransformPrimeDivisor (blowUpToBase (I.comap U.ι)) P' = some P →
      P.idealSheaf = blowUpTransformFamily (compFamily D U) (I.comap U.ι) (Sum.inl l) := by
    intro l P' P hP' hP
    have hA : IsIrreducible (P'.idealSheaf.support : Set U.toScheme) := by
      change IsIrreducible (P'.support : Set U.toScheme)
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isIrreducible_singleton.closure
    have hnot : ¬ (P'.idealSheaf.support : Set U.toScheme) ⊆ (I.comap U.ι).support := by
      rw [hP']
      exact not_subset_support_compFamily U I hirr hc hUD l
    rw [(MMP.Mori.inverseTransformPrimeDivisor_eq_some_iff.mp hP).2,
      MMP.Mori.inverseTransformIdeal, blowUpTransformFamily, Sum.elim_inl]
    congr 1
    apply Closeds.ext
    rw [coe_inverseTransform_blowUpToBase (I.comap U.ι) _ hA hnot, Closeds.coe_closure, hP']
  have hsmooth : ∀ P ∈ (Finsupp.single F a + inverseTransformDivisor (blowUpToBase (I.comap U.ι))
        (inverseTransformDivisor U.ι D)).support,
      IsSmoothScheme (P.idealSheaf.subschemeι ≫ blowUpToBase (I.comap U.ι) ≫ U.ι ≫ sY) := by
    intro P hP
    rcases hcases P hP with hPF | ⟨l, P', hP', hPP'⟩
    · rw [hPF, hF]
      haveI := (MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup
        _ _ hb).2.1
      exact MMP.Resolution.isSmoothScheme_of_smooth _
    · rw [hstrict l P' P hP' hPP', blowUpTransformFamily, Sum.elim_inl]
      have : IsIntegral (compFamily D U l).subscheme := hP' ▸ P'.integral
      have hsubZ : ((I.comap U.ι).support : Set U.toScheme) ⊆ (compFamily D U l).support :=
        fun u hu =>
        (mem_support_comap_ι U _ u).mpr
          (hUD l.1 l.2.1 l.2.2 ((mem_support_comap_ι U I u).mp hu))
      exact isSmoothScheme_strictTransform (U.ι ≫ sY) (I.comap U.ι) (compFamily D U l) hb.2
        (hfam.1 l).2.2 (le_of_support_subset (U.ι ≫ sY) (I.comap U.ι) hb.2 _ hsubZ)
        (not_subset_support_compFamily U I hirr hc hUD l)
  have hidx : ∀ P ∈ (Finsupp.single F a + inverseTransformDivisor (blowUpToBase (I.comap U.ι))
        (inverseTransformDivisor U.ι D)).support,
      ∃ i, blowUpTransformFamily (compFamily D U) (I.comap U.ι) i = P.idealSheaf := by
    intro P hP
    rcases hcases P hP with hPF | ⟨l, P', hP', hPP'⟩
    · exact ⟨Sum.inr (), by rw [hPF, hF]; rfl⟩
    · exact ⟨Sum.inl l, (hstrict l P' P hP' hPP').symm⟩
  refine ⟨hsmooth, fun x => ?_⟩
  choose g hg using hidx
  obtain ⟨N, w, c, hw, hc', hinj⟩ := exists_coordinates_blowUpTransformFamily hfam hZ x
  have hmem : ∀ P : {P : MMP.Mori.PrimeDivisor (blowUp (I.comap U.ι)) //
        P ∈ (Finsupp.single F a + inverseTransformDivisor (blowUpToBase (I.comap U.ι))
          (inverseTransformDivisor U.ι D)).support ∧ x ∈ P.support},
      x ∈ (blowUpTransformFamily (compFamily D U) (I.comap U.ι) (g P.1 P.2.1)).support := by
    intro P
    rw [hg]
    exact P.2.2
  refine ⟨N, w, fun P => c ⟨_, hmem P⟩, hw, fun P P' hPP' => ?_, fun P => ?_⟩
  · have h1 : g P.1 P.2.1 = g P'.1 P'.2.1 := congrArg Subtype.val (hinj hPP')
    have h2 : P.1.idealSheaf = P'.1.idealSheaf := by
      rw [← hg P.1 P.2.1, ← hg P'.1 P'.2.1, h1]
    exact Subtype.ext (MMP.Mori.PrimeDivisor.ext_idealSheaf h2)
  · have := hc' ⟨_, hmem P⟩
    rwa [hg] at this

/-- **Snc after the blow-up of a smooth centre.** Let `U` be an open set meeting `Z` such that
every component of `D` meeting `U` contains `Z`. Then the blow-up of the smooth centre `Z ∩ U`
is smooth, its exceptional divisor is a prime divisor `F`, and `a F` plus the strict transform of
`D|_U` is snc for every `a`. -/
private theorem isSNC_blowUp_of_forall_subset
    (sY : Y ⟶ Spec (.of k)) (hY : MMP.Mori.IsVariety k sY)
    (I : Y.IdealSheafData) (h : IsSmoothBlowup sY I) (hirr : IsIrreducible (I.support : Set Y))
    (hc : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    {R : Type*} [AddCommMonoid R] {D : DivisorWithCoeffs R Y} (hD : D.IsSNC sY) (U : Y.Opens)
    (hU : ((U : Set Y) ∩ I.support).Nonempty)
    (hUD : ∀ E ∈ D.support, ((E.support : Set Y) ∩ U).Nonempty →
      (I.support : Set Y) ⊆ E.support) :
    Smooth (blowUpToBase (I.comap U.ι) ≫ U.ι ≫ sY) ∧
      ∃ F : MMP.Mori.PrimeDivisor (blowUp (I.comap U.ι)),
        F.idealSheaf = exceptionalIdeal (I.comap U.ι) ∧
        ∀ a : R, DivisorWithCoeffs.IsSNC (blowUpToBase (I.comap U.ι) ≫ U.ι ≫ sY)
          (Finsupp.single F a + inverseTransformDivisor (blowUpToBase (I.comap U.ι))
            (inverseTransformDivisor U.ι D)) := by
  refine ⟨(MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup _ _
    (isSmoothBlowup_comap sY I h U)).1, ?_⟩
  have := hY.toIsIntegral
  have hirr' := isIrreducible_support_comap I hirr U hU
  have hc1 := one_le_codimension_support_comap I hirr (le_trans (by norm_num) hc) U hU hirr'
  refine ⟨exceptionalPrimeDivisor (U.ι ≫ sY) (I.comap U.ι) (isSmoothBlowup_comap sY I h U)
    hirr' hc1, rfl, isSNC_single_add_inverseTransformDivisor sY hY I h hirr hc hD U hUD _ rfl⟩

end MMP.Proofs.lem_mmp_threefold_smooth_blowup_generic_snc

namespace MMP.Threefold.Resolution

open Classical in
open MMP.Proofs.lem_mmp_threefold_smooth_blowup_generic_snc in
/-- **Generic snc compatibility for a smooth-centre blow-up.** Let `Y` be a smooth variety over
`k`, `D` an snc divisor on `Y`, and `Z = V(I)` a smooth irreducible closed subscheme of
codimension `c ≥ 2`. There is an open `U` meeting `Z` such that every component of `D` meeting
`U` contains `Z`, the blow-up `π : Bl_{Z ∩ U} U ⟶ U` is smooth over `k`, its exceptional divisor
is a prime divisor `F`, and `a F + π⁻¹_*(D|_U)` is snc for every coefficient `a`. Moreover at
most `c` components of `D` contain `Z`, and each of them is smooth over `k` at the generic point
of `Z`. -/
@[mmp "lem_mmp_threefold_smooth_blowup_generic_snc"]
public theorem exists_isSNC_single_exceptional_add_inverseTransformDivisor
    {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (hY : Mori.IsVariety k sY)
    (I : Y.IdealSheafData) (h : IsSmoothBlowup sY I) (hirr : IsIrreducible (I.support : Set Y))
    (hc : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    {R : Type*} [AddCommMonoid R] {D : DivisorWithCoeffs R Y} (hD : D.IsSNC sY) :
    (∃ U : Y.Opens, ((U : Set Y) ∩ I.support).Nonempty ∧
      (∀ E ∈ D.support, ((E.support : Set Y) ∩ U).Nonempty →
        (I.support : Set Y) ⊆ E.support) ∧
      Smooth (blowUpToBase (I.comap U.ι) ≫ U.ι ≫ sY) ∧
      ∃ F : Mori.PrimeDivisor (blowUp (I.comap U.ι)),
        F.idealSheaf = exceptionalIdeal (I.comap U.ι) ∧
        ∀ a : R, DivisorWithCoeffs.IsSNC (blowUpToBase (I.comap U.ι) ≫ U.ι ≫ sY)
          (Finsupp.single F a + inverseTransformDivisor (blowUpToBase (I.comap U.ι))
            (inverseTransformDivisor U.ι D))) ∧
    ((D.support.filter fun E => (I.support : Set Y) ⊆ E.support).card : ℕ∞) ≤
      codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) ∧
    ∀ E ∈ D.support, (I.support : Set Y) ⊆ E.support →
      ∃ ζ : E.idealSheaf.subscheme, E.idealSheaf.subschemeι ζ = hirr.genericPoint ∧
        ζ ∈ smoothLocus (E.idealSheaf.subschemeι ≫ sY) := by
  obtain ⟨U, hU, hUD⟩ := exists_open_forall_subset D I hirr
  exact ⟨⟨U, hU, hUD, isSNC_blowUp_of_forall_subset sY hY I h hirr hc hD U hU hUD⟩,
    card_filter_le_codimension sY hD I hirr, exists_mem_smoothLocus_genericPoint sY hD I hirr⟩

end MMP.Threefold.Resolution

end
