module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.FieldTheory.Separable

/-!
# Derivations of a power series ring over a separable extension

Let `k` be a field, `K/k` a separable algebraic extension (for instance a finite extension, when
`k` has characteristic `0`) and `R = K[[x_1, …, x_n]]`. Every `k`-derivation of `R` kills `K`
and is determined by its values on the `x_i`: `Der_k(R)` is the free `R`-module on the formal
partial derivatives `∂/∂x_1, …, ∂/∂x_n`.

## Main results

* `MMP.Resolution.Kollar.exists_basis_derivation_mvPowerSeries`: the formal partial derivatives
  form a basis of `Der_k(K[[x_1, …, x_n]])`.
* `MMP.Resolution.Kollar.derivativeIdealOfRing_span_range_mvPowerSeries`: for `n ≠ 0` and an
  ideal `J = (f_i)` of `K[[x_1, …, x_n]]`, the derivative ideal is
  `D(J) = (f_i, ∂f_i/∂x_j)`.

## Implementation notes

Kollár needs this for `k` of characteristic `0` and `K/k` finite. The argument only uses that
the minimal polynomial over `k` of every element of `K` is separable, so the statement is made
for a separable algebraic extension `K/k` (`Algebra.IsSeparable k K`); a finite extension of a
field of characteristic `0` is one, and the instance is found automatically. The formal partial
derivatives are Mathlib's `MvPowerSeries.pderiv`, `K`-derivations, viewed as `k`-derivations by
restriction of scalars.

Kollár states the description of `D(J)` for finitely many generators `f_1, …, f_s`; the argument
works verbatim for an arbitrary family of generators, and the statement is made for one.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.74(5), 3.94]
-/

@[expose] public noncomputable section

namespace MMP.Resolution.Kollar

open MvPowerSeries

private lemma coeff_X_mul_eq_ite {σ R : Type*} [Semiring R] (i : σ) (g : MvPowerSeries σ R)
    (d : σ →₀ ℕ) :
    coeff d (X i * g) = if Finsupp.single i 1 ≤ d then coeff (d - Finsupp.single i 1) g else 0 := by
  rw [show (X i : MvPowerSeries σ R) = monomial (Finsupp.single i 1) 1 from rfl,
    coeff_monomial_mul]
  simp

private lemma sum_eq_sum_tsub_single_add_one {n : ℕ} (i : Fin n) (d : Fin n →₀ ℕ)
    (h : Finsupp.single i 1 ≤ d) :
    ∑ j, d j = ∑ j, (d - Finsupp.single i 1 : Fin n →₀ ℕ) j + 1 := by
  have hd : d = (d - Finsupp.single i 1) + Finsupp.single i 1 := (tsub_add_cancel_of_le h).symm
  conv_lhs => rw [hd]
  simp [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply]

private lemma exists_eq_sum_X_mul_of_coeff_zero_eq_zero {n : ℕ} {K : Type*} [Semiring K]
    (f : MvPowerSeries (Fin n) K) (h0 : coeff 0 f = 0) :
    ∃ g : Fin n → MvPowerSeries (Fin n) K, f = ∑ i, X i * g i ∧
      ∀ M, (∀ d : Fin n →₀ ℕ, ∑ j, d j < M + 1 → coeff d f = 0) →
        ∀ i, ∀ d : Fin n →₀ ℕ, ∑ j, d j < M → coeff d (g i) = 0 := by
  classical
  let g : Fin n → MvPowerSeries (Fin n) K := fun i d =>
    if (∀ j, j < i → d j = 0) then coeff (d + Finsupp.single i 1) f else 0
  have hgc : ∀ i d, coeff d (g i) =
      if (∀ j, j < i → d j = 0) then coeff (d + Finsupp.single i 1) f else 0 := fun _ _ => rfl
  refine ⟨g, ?_, ?_⟩
  · ext d
    rw [map_sum]
    simp_rw [coeff_X_mul_eq_ite]
    by_cases hd : d = 0
    · subst hd
      simp [h0]
    · have hne : (Finset.univ.filter (fun i => d i ≠ 0)).Nonempty := by
        by_contra hcon
        exact hd (Finsupp.ext fun j => not_not.mp fun hj => hcon ⟨j, by simpa using hj⟩)
      set i0 := (Finset.univ.filter (fun i => d i ≠ 0)).min' hne
      have hi0mem : d i0 ≠ 0 := by simpa using Finset.min'_mem _ hne
      have hmin : ∀ j, j < i0 → d j = 0 := by
        intro j hj
        by_contra hjne
        exact absurd hj (not_lt.mpr (Finset.min'_le _ _ (by simpa using hjne)))
      rw [Finset.sum_eq_single i0]
      · have hle : Finsupp.single i0 1 ≤ d := by
          intro j
          by_cases hj : j = i0
          · subst hj
            simp only [Finsupp.single_eq_same]
            omega
          · simp [Ne.symm hj]
        rw [ite_eq_left hle]
        have hg : coeff (d - Finsupp.single i0 1) (g i0) = coeff d f := by
          rw [hgc, ite_eq_left]
          · rw [tsub_add_cancel_of_le hle]
          · intro j hj
            simp [Ne.symm (ne_of_lt hj), hmin j hj]
        exact hg.symm
      · intro i _ hi
        by_cases hle : Finsupp.single i 1 ≤ d
        · rw [ite_eq_left hle]
          have hi' : d i ≠ 0 := by
            have := hle i
            simp only [Finsupp.single_eq_same] at this
            omega
          have hlt : i0 < i := by
            have : i0 ≤ i := Finset.min'_le _ _ (by simpa using hi')
            exact lt_of_le_of_ne this (Ne.symm hi)
          rw [hgc, ite_eq_right]
          exact fun hall => hi0mem (by simpa [hi] using hall i0 hlt)
        · rw [ite_eq_right hle]
      · exact fun h => absurd (Finset.mem_univ _) h
  · intro M hM i d hd
    rw [hgc]
    split_ifs
    · apply hM
      have : ∑ j, (d + Finsupp.single i 1 : Fin n →₀ ℕ) j = ∑ j, d j + 1 := by
        simp [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply]
      omega
    · rfl

private lemma coeff_derivation_eq_zero_of_apply_X_eq_zero {n : ℕ} {k K : Type*} [Field k]
    [Field K] [Algebra k K] (D : Derivation k (MvPowerSeries (Fin n) K) (MvPowerSeries (Fin n) K))
    (hX : ∀ i, D (X i) = 0) (M : ℕ) (f : MvPowerSeries (Fin n) K)
    (hf : ∀ d : Fin n →₀ ℕ, ∑ j, d j < M → coeff d f = 0) :
    ∀ d : Fin n →₀ ℕ, ∑ j, d j + 1 < M → coeff d (D f) = 0 := by
  induction M generalizing f with
  | zero => intro d hd; omega
  | succ M ih =>
    intro d hd
    have h0 : coeff 0 f = 0 := hf 0 (by simp)
    obtain ⟨g, hfg, hg⟩ := exists_eq_sum_X_mul_of_coeff_zero_eq_zero f h0
    have hgM := hg M (fun d hd => hf d (by omega))
    have hDf : D f = ∑ i, X i * D (g i) := by
      conv_lhs => rw [hfg]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Derivation.leibniz, hX]
      simp [smul_eq_mul]
    rw [hDf, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [coeff_X_mul_eq_ite]
    split_ifs with hle
    · apply ih (g i) (hgM i)
      have := sum_eq_sum_tsub_single_add_one i d hle
      omega
    · rfl

private lemma derivation_apply_C_eq_zero {n : ℕ} {k K : Type*} [Field k]
    [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (D : Derivation k (MvPowerSeries (Fin n) K) (MvPowerSeries (Fin n) K)) (a : K) :
    D (C a) = 0 := by
  have := Algebra.FormallyUnramified.of_isSeparable k K
  have : Subsingleton (Ω[K⁄k]) := Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  have h := congrArg (fun D' : Derivation k K _ => D' a)
    (Subsingleton.elim (D.compAlgebraMap K).liftKaehlerDifferential 0 ▸
      (D.compAlgebraMap K).liftKaehlerDifferential_comp)
  simpa [MvPowerSeries.algebraMap_apply] using h.symm

private lemma derivation_apply_coe_eq_zero_of_apply_X_eq_zero {n : ℕ} {k K : Type*} [Field k]
    [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (D : Derivation k (MvPowerSeries (Fin n) K) (MvPowerSeries (Fin n) K))
    (hX : ∀ i, D (X i) = 0) (q : MvPolynomial (Fin n) K) :
    D (q : MvPowerSeries (Fin n) K) = 0 := by
  induction q using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.coe_C]; exact derivation_apply_C_eq_zero D a
  | add p q hp hq => rw [MvPolynomial.coe_add, map_add, hp, hq, add_zero]
  | mul_X p i hp =>
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, Derivation.leibniz, hp, hX]
    simp

private lemma derivation_eq_zero_of_apply_X_eq_zero {n : ℕ} {k K : Type*} [Field k]
    [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (D : Derivation k (MvPowerSeries (Fin n) K) (MvPowerSeries (Fin n) K))
    (hX : ∀ i, D (X i) = 0) : D = 0 := by
  classical
  ext f : 1
  ext d : 1
  set M := ∑ j, d j + 2 with hM
  let S : Finset (Fin n →₀ ℕ) := Finset.Iic (Finsupp.equivFunOnFinite.symm (fun _ => M))
  let q : MvPolynomial (Fin n) K := ∑ e ∈ S, MvPolynomial.monomial e (coeff e f)
  have hq : ∀ e : Fin n →₀ ℕ, ∑ j, e j < M → coeff e (q : MvPowerSeries (Fin n) K) = coeff e f := by
    intro e he
    rw [MvPolynomial.coeff_coe]
    simp only [q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single e]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hnot
      exfalso; apply hnot
      simp only [S, Finset.mem_Iic]
      intro j
      have : e j ≤ ∑ j, e j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
      omega
  have hDq := derivation_apply_coe_eq_zero_of_apply_X_eq_zero D hX q
  have hsub : D f = D (f - q) := by rw [map_sub, hDq, sub_zero]
  rw [hsub]
  apply coeff_derivation_eq_zero_of_apply_X_eq_zero D hX M (f - q)
  · intro e he
    rw [map_sub, hq e he, sub_self]
  · omega

private lemma sum_smul_pderiv_apply {n : ℕ} {k K : Type*} [Field k] [Field K] [Algebra k K]
    (g : Fin n → MvPowerSeries (Fin n) K) (x : MvPowerSeries (Fin n) K) :
    (∑ i, g i • ((MvPowerSeries.pderiv (R := K) i).restrictScalars k :
      Derivation k (MvPowerSeries (Fin n) K) (MvPowerSeries (Fin n) K))) x =
    ∑ i, g i * MvPowerSeries.pderiv (R := K) i x := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

/-- **Derivations of a power series ring** (Kollár 3.74(5), 3.94). Let `k` be a field, `K/k` a
separable algebraic extension (e.g. a finite extension, `k` of characteristic `0`) and
`R = K[[x_1, …, x_n]]`. Then `Der_k(R)` is the free `R`-module on the formal partial derivatives
`∂/∂x_1, …, ∂/∂x_n`. -/
@[mmp "lem_kr3d_derivations_power_series_ring"]
theorem exists_basis_derivation_mvPowerSeries (k K : Type*) [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparable k K] (n : ℕ) :
    ∃ e : Module.Basis (Fin n) (MvPowerSeries (Fin n) K)
        (Derivation k (MvPowerSeries (Fin n) K) (MvPowerSeries (Fin n) K)),
      ∀ i, e i = (MvPowerSeries.pderiv (R := K) i).restrictScalars k := by
  classical
  have hli : LinearIndependent (MvPowerSeries (Fin n) K)
      (fun i => (MvPowerSeries.pderiv (R := K) i).restrictScalars k :
        Fin n → Derivation k (MvPowerSeries (Fin n) K) (MvPowerSeries (Fin n) K)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (fun D => D (X i : MvPowerSeries (Fin n) K)) hg
    rw [sum_smul_pderiv_apply] at this
    simpa [MvPowerSeries.pderiv_X, Pi.single_apply] using this
  have hsp : ⊤ ≤ Submodule.span (MvPowerSeries (Fin n) K)
      (Set.range (fun i => (MvPowerSeries.pderiv (R := K) i).restrictScalars k :
        Fin n → Derivation k (MvPowerSeries (Fin n) K) (MvPowerSeries (Fin n) K))) := by
    intro D _
    have hD : D = ∑ i, D (X i) • ((MvPowerSeries.pderiv (R := K) i).restrictScalars k :
        Derivation k (MvPowerSeries (Fin n) K) (MvPowerSeries (Fin n) K)) := by
      rw [← sub_eq_zero]
      apply derivation_eq_zero_of_apply_X_eq_zero
      intro j
      rw [Derivation.sub_apply, sum_smul_pderiv_apply]
      simp [MvPowerSeries.pderiv_X, Pi.single_apply]
    rw [hD]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun i => by simp⟩

/-- **Derivative ideals of a power series ring in terms of generators** (Kollár 3.74(5)). Let `k`
be a field, `K/k` a separable algebraic extension (e.g. a finite extension, `k` of characteristic
`0`), `R = K[[x_1, …, x_n]]` with `n ≠ 0`, and `J = (f_i)_{i ∈ ι}` an ideal of `R`. Then the
derivative ideal `D(J) = D_{R/k}(J)` is generated by the `f_i` and their formal partial
derivatives `∂f_i/∂x_j`. -/
@[mmp "lem_kr3d_power_series_derivative_ideal_generators"]
theorem derivativeIdealOfRing_span_range_mvPowerSeries (k : Type*) {K : Type*} [Field k]
    [Field K] [Algebra k K] [Algebra.IsSeparable k K] {ι : Type*} {n : ℕ} (hn : n ≠ 0)
    (f : ι → MvPowerSeries (Fin n) K) :
    derivativeIdealOfRing k (Ideal.span (Set.range f)) =
      Ideal.span (Set.range f ∪
        Set.range fun ij : ι × Fin n => MvPowerSeries.pderiv (R := K) ij.2 (f ij.1)) := by
  classical
  set J : Ideal (MvPowerSeries (Fin n) K) := Ideal.span (Set.range f)
  set T : Ideal (MvPowerSeries (Fin n) K) := Ideal.span (Set.range f ∪
        Set.range fun ij : ι × Fin n => MvPowerSeries.pderiv (R := K) ij.2 (f ij.1))
  have hfT : ∀ i, f i ∈ T := fun i => Ideal.subset_span (Or.inl ⟨i, rfl⟩)
  have hdT : ∀ i j, MvPowerSeries.pderiv (R := K) j (f i) ∈ T :=
    fun i j => Ideal.subset_span (Or.inr ⟨(i, j), rfl⟩)
  have key : ∀ h ∈ J, h ∈ T ∧ ∀ j, MvPowerSeries.pderiv (R := K) j h ∈ T := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨hfT i, hdT i⟩
    | zero => exact ⟨T.zero_mem, fun j => by simp⟩
    | add x y _ _ hx hy =>
      exact ⟨T.add_mem hx.1 hy.1, fun j => by rw [map_add]; exact T.add_mem (hx.2 j) (hy.2 j)⟩
    | smul a x _ hx =>
      refine ⟨T.mul_mem_left a hx.1, fun j => ?_⟩
      rw [smul_eq_mul, Derivation.leibniz]
      simp only [smul_eq_mul]
      exact T.add_mem (T.mul_mem_left a (hx.2 j)) (T.mul_mem_right _ hx.1)
  have hD : ∀ i j, MvPowerSeries.pderiv (R := K) j (f i) ∈ derivativeIdealOfRing k J := fun i j =>
    Ideal.subset_span ⟨(MvPowerSeries.pderiv (R := K) j).restrictScalars k, f i,
      Ideal.subset_span ⟨i, rfl⟩, rfl⟩
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨δ, h, hh, rfl⟩
    obtain ⟨e, he⟩ := exists_basis_derivation_mvPowerSeries k K n
    have hδ : δ = ∑ i, e.repr δ i • e i := (e.sum_repr δ).symm
    have : δ h = ∑ i, e.repr δ i * MvPowerSeries.pderiv (R := K) i h := by
      conv_lhs => rw [hδ]
      simp only [he]
      exact sum_smul_pderiv_apply _ _
    rw [this]
    exact T.sum_mem fun i _ => T.mul_mem_left _ ((key h hh).2 i)
  · refine Ideal.span_le.mpr ?_
    rintro _ (⟨i, rfl⟩ | ⟨⟨i, j⟩, rfl⟩)
    · let j : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
      have h1 : MvPowerSeries.pderiv (R := K) j (MvPowerSeries.X j * f i) ∈ derivativeIdealOfRing k J :=
        Ideal.subset_span ⟨(MvPowerSeries.pderiv (R := K) j).restrictScalars k, _,
          J.mul_mem_left _ (Ideal.subset_span ⟨i, rfl⟩), rfl⟩
      have h2 := Ideal.mul_mem_left (derivativeIdealOfRing k J) (MvPowerSeries.X j) (hD i j)
      have h3 := Ideal.sub_mem _ h1 h2
      convert h3 using 1
      rw [Derivation.leibniz]
      simp
    · exact hD i j

end MMP.Resolution.Kollar
