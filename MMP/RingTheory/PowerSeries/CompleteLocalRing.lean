/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParametersCharZero
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Basic
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.CompleteLocalRing.Regular
public import StacksFrontier.RingTheory.MvPowerSeries.AdicTopology
public import StacksFrontier.RingTheory.MvPowerSeries.HomExt
public import StacksFrontier.RingTheory.MvPowerSeries.PolynomialTruncation

/-!
# Power series rings and completed local rings

Four facts about complete local rings and formal power series rings that resolution of
singularities uses.

* Let `K` be a field and `R = K[[x₁, …, xₙ]]` with maximal ideal `𝔪`. For `g₁, …, gₙ ∈ 𝔪` the
  substitution `f ↦ f(g₁, …, gₙ)` is a local `K`-algebra endomorphism of `R`, continuous for the
  `𝔪`-adic topology, sending `xᵢ` to `gᵢ`, and it is the only `K`-algebra endomorphism of `R`
  doing so. Modulo `𝔪ᴺ` it is computed by substituting into the part of `f` of degree `< N`.
* Let `(A, 𝔪)` be a complete local ring, for instance the completion `R̂` of a Noetherian local
  ring `R`. A polynomial `f ∈ A[y]` whose reduction modulo `𝔪` has a simple root `ᾱ` has exactly
  one root in `A` reducing to `ᾱ` (Newton's method). No monicity is needed.
* Let `(R, 𝔪)` be a Noetherian local ring with a regular system of parameters `x₁, …, xₙ`, and let
  `k' ⊆ R̂` be a field of representatives of its completion. Then every `k'`-algebra homomorphism
  `k'[[t₁, …, tₙ]] → R̂` with `tᵢ ↦ xᵢ` is an isomorphism, and there is one. This applies to the
  local ring `𝒪_{p,X}` of a smooth scheme over a field, which is regular.
* Let `X` be a scheme of finite type over a field `k` of characteristic zero and `p ∈ X` a closed
  point. The completed local ring `𝒪̂_{p,X}` has exactly one field of representatives containing
  `k`, and every `k`-algebra endomorphism of `𝒪̂_{p,X}` inducing the identity on `κ(p)` fixes it
  pointwise.

## Main results

* `MMP.Flips.ResolutionInputs.isLocalHom_substAlgHom`,
  `MMP.Flips.ResolutionInputs.continuous_substAlgHom`,
  `MMP.Flips.ResolutionInputs.eq_substAlgHom_of_X`,
  `MMP.Flips.ResolutionInputs.substAlgHom_sub_sum_mem_pow`: substitution by elements of the
  maximal ideal.
* `MMP.Flips.ResolutionInputs.existsUnique_eval_eq_zero_of_isAdicComplete`,
  `MMP.Flips.ResolutionInputs.existsUnique_eval_eq_zero_evalOneₐ_eq`: simple roots lift uniquely
  to a complete local ring, resp. to the completion of a Noetherian local ring.
* `MMP.Flips.ResolutionInputs.bijective_of_isFieldOfRepresentatives`,
  `MMP.Flips.ResolutionInputs.exists_algHom_X_eq_of_isFieldOfRepresentatives`: the power series
  ring over a given field of representatives, on a given regular system of parameters, is the
  completion; `MMP.Flips.ResolutionInputs.existsUnique_algHom_X_eq_bijective_stalk` for the
  completed local ring at a point of a locally Noetherian scheme.
* `MMP.Flips.ResolutionInputs.existsUnique_isFieldOfRepresentatives`,
  `MMP.Flips.ResolutionInputs.eq_self_of_isFieldOfRepresentatives`: uniqueness and rigidity of
  the coefficient field containing `k` of a complete local `k`-algebra with finite separable
  residue field; `MMP.Flips.ResolutionInputs.existsUnique_isFieldOfRepresentatives_completion`
  and `MMP.Flips.ResolutionInputs.eq_self_of_isFieldOfRepresentatives_completion` at a closed
  point of a scheme of finite type over a field of characteristic zero.

## Implementation notes

* The substitution is Mathlib's `MvPowerSeries.substAlgHom`. The `𝔪`-adic topology is
  `Ideal.adicTopology`, given explicitly to `Continuous`. The limit formula
  `f(g) = lim_N ∑_{|c| < N} a_c g^c` is stated as: for every finite set `S` of exponents
  containing all `c` with `|c| < N`, the difference `f(g) - ∑_{c ∈ S} a_c g^c` lies in `𝔪ᴺ`.
  Uniqueness holds among all `K`-algebra endomorphisms with `xᵢ ↦ gᵢ`, continuous or not, since
  any ring map sends `𝔪ᴺ = (x₁, …, xₙ)ᴺ` into `(g₁, …, gₙ)ᴺ`.
* The projection `ρ : R̂ → R/𝔪` is `AdicCompletion.evalOneₐ`. The root-lifting lemma is proved
  for any surjection `π : A → B` out of a complete local ring with kernel the maximal ideal, so
  that it covers both `ρ` and the residue map `A → κ(A)`.
* The field of representatives is `MMP.Resolution.IsFieldOfRepresentatives`, a subring that is a
  field mapping bijectively onto the residue field. The power-series isomorphism holds for any
  Noetherian local ring with a regular system of parameters; in particular neither smoothness,
  nor closedness of the point, nor the condition `k ⊆ k'` is used, and the scheme statement is
  given for a locally Noetherian scheme.
* In the coefficient-field statement, "containing `k`" is `Set.range (algebraMap k Â) ⊆ K`.
  Uniqueness and rigidity hold for any complete local `k`-algebra whose residue field is
  separable algebraic over `k`; existence uses a primitive element and so a finite residue
  field. The endomorphism is only assumed to induce the identity on the residue field; locality
  follows from that.
* At a point of a scheme, the `k`-algebra structure of `𝒪_{p,X}` is `MMP.Mori.stalkAlgebra`, and
  `𝒪̂_{p,X}` is a `k`-algebra through it. The scheme statements carry `[IsLocallyNoetherian X]`,
  which `[LocallyOfFiniteType sX]` implies, so that the completion is a local ring in the
  statement itself.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Def. 3.55 and Notation 3.93]
* [Stacks Project, Tag 0C0S](https://stacks.math.columbia.edu/tag/0C0S)
* [Stacks Project, Tag 04GG](https://stacks.math.columbia.edu/tag/04GG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing Polynomial

universe u

namespace MMP.Flips.ResolutionInputs

/-! ### Substitution into a power series ring over a field -/

section Substitution

variable {K : Type*} [Field K] {n : ℕ}

/-- An element of the maximal ideal of `K[[x₁, …, xₙ]]` has constant coefficient zero. -/
theorem constantCoeff_eq_zero_of_mem_maximalIdeal {g : MvPowerSeries (Fin n) K}
    (hg : g ∈ maximalIdeal (MvPowerSeries (Fin n) K)) : MvPowerSeries.constantCoeff g = 0 := by
  rwa [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero, not_not] at hg

/-- Elements of the maximal ideal of `K[[x₁, …, xₙ]]` may be substituted for the variables. -/
theorem hasSubst_of_mem_maximalIdeal {g : Fin n → MvPowerSeries (Fin n) K}
    (hg : ∀ i, g i ∈ maximalIdeal (MvPowerSeries (Fin n) K)) : MvPowerSeries.HasSubst g :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
    constantCoeff_eq_zero_of_mem_maximalIdeal (hg i)

/-- A constant power series is the image of the scalar under the algebra map. -/
theorem mvPowerSeries_C_eq_algebraMap {σ R : Type*} [CommSemiring R] (r : R) :
    (MvPowerSeries.C r : MvPowerSeries σ R) = algebraMap R (MvPowerSeries σ R) r := by
  rw [MvPowerSeries.c_eq_algebraMap]

/-- **Substitution is a local homomorphism.** For `g₁, …, gₙ` in the maximal ideal of
`K[[x₁, …, xₙ]]`, the substitution `f ↦ f(g₁, …, gₙ)` is a local ring homomorphism. -/
@[mmp "lem_mmp_foundation_power_series_substitution"]
theorem isLocalHom_substAlgHom {g : Fin n → MvPowerSeries (Fin n) K}
    (hg : ∀ i, g i ∈ maximalIdeal (MvPowerSeries (Fin n) K)) :
    IsLocalHom (MvPowerSeries.substAlgHom (R := K) (hasSubst_of_mem_maximalIdeal hg)) := by
  set φ := MvPowerSeries.substAlgHom (R := K) (hasSubst_of_mem_maximalIdeal hg)
  have hcomp : (MvPowerSeries.constantCoeff (σ := Fin n) (R := K)).comp φ.toRingHom =
      MvPowerSeries.constantCoeff := by
    refine mvPowerSeries_hom_ext (⊥ : Ideal K) n _ _ (fun r => ?_) (fun i => ?_) (fun i => ?_)
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
        Function.comp_apply, mvPowerSeries_C_eq_algebraMap, AlgHom.commutes]
    all_goals simp [φ, MvPowerSeries.subst_X (hasSubst_of_mem_maximalIdeal hg),
      constantCoeff_eq_zero_of_mem_maximalIdeal (hg i)]
  refine ⟨fun f hf => ?_⟩
  rw [MvPowerSeries.isUnit_iff_constantCoeff] at hf ⊢
  exact RingHom.congr_fun hcomp f ▸ hf

/-- **Substitution sends `𝔪ᴺ` into `𝔪ᴺ`.** -/
theorem substAlgHom_mem_pow {g : Fin n → MvPowerSeries (Fin n) K}
    (hg : ∀ i, g i ∈ maximalIdeal (MvPowerSeries (Fin n) K)) {N : ℕ}
    {f : MvPowerSeries (Fin n) K} (hf : f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ N) :
    MvPowerSeries.substAlgHom (R := K) (hasSubst_of_mem_maximalIdeal hg) f ∈
      maximalIdeal (MvPowerSeries (Fin n) K) ^ N := by
  set φ := (MvPowerSeries.substAlgHom (R := K) (hasSubst_of_mem_maximalIdeal hg)).toRingHom
  have : IsLocalHom φ := ⟨fun a ha => (isLocalHom_substAlgHom hg).map_nonunit a ha⟩
  have hle : Ideal.map φ (maximalIdeal (MvPowerSeries (Fin n) K) ^ N) ≤
      maximalIdeal (MvPowerSeries (Fin n) K) ^ N := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (map_maximalIdeal_le φ) N
  exact hle (Ideal.mem_map_of_mem φ hf)

/-- **Substitution is `𝔪`-adically continuous.** -/
@[mmp "lem_mmp_foundation_power_series_substitution"]
theorem continuous_substAlgHom {g : Fin n → MvPowerSeries (Fin n) K}
    (hg : ∀ i, g i ∈ maximalIdeal (MvPowerSeries (Fin n) K)) :
    @Continuous _ _ (maximalIdeal (MvPowerSeries (Fin n) K)).adicTopology
      (maximalIdeal (MvPowerSeries (Fin n) K)).adicTopology
      (MvPowerSeries.substAlgHom (R := K) (hasSubst_of_mem_maximalIdeal hg)) := by
  set φ := (MvPowerSeries.substAlgHom (R := K) (hasSubst_of_mem_maximalIdeal hg)).toRingHom
  have : IsLocalHom φ := ⟨fun a ha => (isLocalHom_substAlgHom hg).map_nonunit a ha⟩
  exact RingHom.continuous_adic_of_isLocalHom φ

/-- **Substitution is the only `K`-algebra endomorphism with `xᵢ ↦ gᵢ`.** Any `K`-algebra
endomorphism of `K[[x₁, …, xₙ]]` sending each `xᵢ` to `gᵢ ∈ 𝔪` is the substitution; in
particular this holds among the `𝔪`-adically continuous ones. -/
@[mmp "lem_mmp_foundation_power_series_substitution"]
theorem eq_substAlgHom_of_X {g : Fin n → MvPowerSeries (Fin n) K}
    (hg : ∀ i, g i ∈ maximalIdeal (MvPowerSeries (Fin n) K))
    (φ : MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K)
    (hφ : ∀ i, φ (MvPowerSeries.X i) = g i) :
    φ = MvPowerSeries.substAlgHom (R := K) (hasSubst_of_mem_maximalIdeal hg) := by
  have h := mvPowerSeries_hom_ext (maximalIdeal (MvPowerSeries (Fin n) K)) n φ.toRingHom
    (MvPowerSeries.substAlgHom (R := K) (hasSubst_of_mem_maximalIdeal hg)).toRingHom
    (fun r => by
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, mvPowerSeries_C_eq_algebraMap,
        AlgHom.commutes])
    (fun i => by
      rw [AlgHom.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_coe, hφ,
        MvPowerSeries.substAlgHom_X])
    (fun i => by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hφ]
      exact hg i)
  exact AlgHom.ext fun f => congrArg (fun ψ => ψ f) h

/-- **The substitution as a limit of polynomial substitutions.** Modulo `𝔪ᴺ`, `f(g₁, …, gₙ)` is
`∑_c a_c g^c` over any finite set of exponents `c` containing those of total degree `< N`. -/
@[mmp "lem_mmp_foundation_power_series_substitution"]
theorem substAlgHom_sub_sum_mem_pow {g : Fin n → MvPowerSeries (Fin n) K}
    (hg : ∀ i, g i ∈ maximalIdeal (MvPowerSeries (Fin n) K)) (f : MvPowerSeries (Fin n) K)
    (N : ℕ) (S : Finset (Fin n →₀ ℕ)) (hS : ∀ c : Fin n →₀ ℕ, ∑ i, c i < N → c ∈ S) :
    MvPowerSeries.substAlgHom (R := K) (hasSubst_of_mem_maximalIdeal hg) f -
        ∑ c ∈ S, MvPowerSeries.coeff c f • c.prod (fun i e => g i ^ e) ∈
      maximalIdeal (MvPowerSeries (Fin n) K) ^ N := by
  have hmem : f - ∑ c ∈ S, MvPowerSeries.monomial c (MvPowerSeries.coeff c f) ∈
      maximalIdeal (MvPowerSeries (Fin n) K) ^ N := by
    rw [MvPowerSeries.maximalIdeal_eq_span_range_X,
      Stacks.MvPowerSeries.RegularParameters.mem_pow_span_range_X_iff]
    intro d hd
    rw [map_sub, map_sum]
    simp only [MvPowerSeries.coeff_monomial]
    rw [Finset.sum_ite_eq S d]
    simp [hS d hd]
  convert substAlgHom_mem_pow hg hmem using 1
  rw [map_sub, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [MvPowerSeries.substAlgHom_monomial, Algebra.smul_def]

end Substitution

/-! ### Lifting simple roots to a complete local ring -/

section SimpleRoot

/-- **A Newton step squares the error.** If `f'(x)` is a unit and `f(x) ∈ Iⁿ⁺¹`, then the Newton
iterate `y = x - f(x) / f'(x)` satisfies `f(y) ∈ Iⁿ⁺²`. -/
theorem eval_newton_step_mem_pow {A : Type*} [CommRing A] (I : Ideal A) (f : A[X]) (x : A)
    (hx : IsUnit ((derivative f).eval x)) {n : ℕ} (h : f.eval x ∈ I ^ (n + 1)) :
    f.eval (x - f.eval x * Ring.inverse ((derivative f).eval x)) ∈ I ^ (n + 1 + 1) := by
  set y := x - f.eval x * Ring.inverse ((derivative f).eval x) with hy
  rw [← taylor_eval_sub x, hy, sub_eq_add_neg, sub_eq_add_neg, add_neg_cancel_comm]
  rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
    Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
  swap
  · intro i
    rw [zero_mul]
  refine Ideal.add_mem _ ?_ ?_
  · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
      taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
      mul_left_comm, Ring.mul_inverse_cancel _ hx, mul_one, add_neg_cancel]
    exact Ideal.zero_mem _
  · refine Submodule.sum_mem _ ?_
    simp only [Finset.mem_Ico]
    rintro i ⟨h2i, _⟩
    have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith only [h2i]
    refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
    rw [pow_mul']
    exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ h) _

/-- **Newton's method in an `I`-adically complete ring.** If `f(a₀) ∈ I` and `f'` is a unit at
every point congruent to `a₀` modulo `I`, then `f` has a root congruent to `a₀` modulo `I`.
Monicity is not needed. -/
theorem exists_eval_eq_zero_sub_mem_of_isAdicComplete {A : Type*} [CommRing A] (I : Ideal A)
    [IsAdicComplete I A] (f : A[X]) (a₀ : A) (h₁ : f.eval a₀ ∈ I)
    (hunit : ∀ x, x - a₀ ∈ I → IsUnit ((derivative f).eval x)) :
    ∃ a : A, f.eval a = 0 ∧ a - a₀ ∈ I := by
  let f' := derivative f
  let c : ℕ → A := fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * Ring.inverse (f'.eval b)
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * Ring.inverse (f'.eval (c n)) := fun n => rfl
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      change f.eval a₀ ∈ I ^ (0 + 1)
      simpa only [zero_add, pow_one] using h₁
    | succ n ih =>
      rw [hc]
      exact eval_newton_step_mem_pow I f _ (hunit _ (SModEq.sub_mem.mp (hc_mod n))) ih
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal A)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => rw [add_zero]
    | succ k ih =>
      rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rw [add_assoc]
      exact le_self_add
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  refine ⟨a, ?_, ?_⟩
  · suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal A)] from IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · have h := ha 1
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, pow_one] at h
    exact SModEq.sub_mem.mp (h.symm.trans (hc_mod 1))

/-- **Simple roots lift uniquely to a complete local ring.** Let `A` be a local ring complete for
its maximal ideal `𝔪`, and `π : A → B` a surjection with kernel `𝔪`. If `f ∈ A[y]` and the image
`πf` of `f` has a simple root `b`, then `f` has exactly one root `a ∈ A` with `π a = b`.
Monicity is not needed. -/
theorem existsUnique_eval_eq_zero_of_isAdicComplete {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [CommRing B] (π : A →+* B)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = maximalIdeal A) (f : A[X]) (b : B)
    (h0 : (f.map π).eval b = 0) (h1 : (f.map π).derivative.eval b ≠ 0) :
    ∃! a : A, f.eval a = 0 ∧ π a = b := by
  have hmem : ∀ x : A, x ∈ maximalIdeal A ↔ π x = 0 := fun x => by rw [← hker, RingHom.mem_ker]
  have hev : ∀ (g : A[X]) (x : A), π (g.eval x) = (g.map π).eval (π x) := fun g x =>
    (eval_map_apply π x).symm
  have hunit : ∀ x : A, π x = b → IsUnit ((derivative f).eval x) := by
    intro x hx
    by_contra hnu
    have : (derivative f).eval x ∈ maximalIdeal A := (mem_maximalIdeal _).2 hnu
    rw [hmem, hev, hx, ← derivative_map] at this
    exact h1 this
  obtain ⟨a₀, ha₀⟩ := hπ b
  have hπ₀ : ∀ x, x - a₀ ∈ maximalIdeal A ↔ π x = b := fun x => by
    rw [hmem, map_sub, sub_eq_zero, ha₀]
  obtain ⟨a, hroot, ha⟩ := exists_eval_eq_zero_sub_mem_of_isAdicComplete (maximalIdeal A) f a₀
    (by rw [hmem, hev, ha₀, h0]) fun x hx => hunit x ((hπ₀ x).1 hx)
  have hres : π a = b := (hπ₀ a).1 ha
  refine ⟨a, ⟨hroot, hres⟩, fun a' ⟨ha'0, ha'b⟩ => ?_⟩
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub ha'0 hroot ?_ (hunit _ ha'b)
  exact (mem_maximalIdeal _).1 (by rw [hmem, map_sub, ha'b, hres, sub_self])

/-- **Simple roots lift uniquely to the completion.** Let `(R, 𝔪)` be a Noetherian local ring,
`R̂` its completion and `ρ : R̂ → R/𝔪` the projection. If `f ∈ R̂[y]` and `ᾱ ∈ R/𝔪` satisfy
`(ρf)(ᾱ) = 0` and `(ρf)'(ᾱ) ≠ 0`, then there is exactly one `α ∈ R̂` with `f(α) = 0` and
`ρ(α) = ᾱ`. -/
@[mmp "lem_mmp_foundation_complete_local_simple_root_lifting"]
theorem existsUnique_eval_eq_zero_evalOneₐ_eq {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (f : (AdicCompletion (maximalIdeal R) R)[X]) (b : R ⧸ maximalIdeal R)
    (h0 : (f.map (AdicCompletion.evalOneₐ (maximalIdeal R)).toRingHom).eval b = 0)
    (h1 : (f.map (AdicCompletion.evalOneₐ (maximalIdeal R)).toRingHom).derivative.eval b ≠ 0) :
    ∃! a : AdicCompletion (maximalIdeal R) R,
      f.eval a = 0 ∧ AdicCompletion.evalOneₐ (maximalIdeal R) a = b := by
  have hs : Function.Surjective (AdicCompletion.evalOneₐ (maximalIdeal R)).toRingHom :=
    AdicCompletion.evalOneₐ_surjective _
  exact existsUnique_eval_eq_zero_of_isAdicComplete _ hs
    (IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (K := ResidueField R) _ hs))
    f b h0 h1

/-- **Simple roots of a polynomial over a field `k` lift uniquely** to a complete local
`k`-algebra `A`: if `P ∈ k[y]` has a simple root `b` in the residue field of `A`, then `P` has
exactly one root in `A` with residue `b`. -/
theorem existsUnique_aeval_eq_zero_residue_eq {k A : Type*} [Field k] [CommRing A]
    [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] [Algebra k A] (P : k[X])
    (b : ResidueField A) (hb : aeval b P = 0) (hb' : aeval b (derivative P) ≠ 0) :
    ∃! a : A, aeval a P = 0 ∧ residue A a = b := by
  have hmap : (P.map (algebraMap k A)).map (residue A) = P.map (algebraMap k (ResidueField A)) := by
    rw [Polynomial.map_map, IsScalarTower.algebraMap_eq k A (ResidueField A)]
    rfl
  have h := existsUnique_eval_eq_zero_of_isAdicComplete (residue A) residue_surjective
    (ker_residue) (P.map (algebraMap k A)) b
    (by rw [hmap, eval_map_algebraMap]; exact hb)
    (by rw [hmap, derivative_map, eval_map_algebraMap]; exact hb')
  simpa only [eval_map_algebraMap] using h

end SimpleRoot

/-! ### The power series ring on a regular system of parameters -/

section RegularCompletion

/-- A surjection out of a ring without zero divisors of Krull dimension at most `n` onto a ring
of Krull dimension at least `n` is injective. -/
theorem injective_of_surjective_of_ringKrullDim_le {A B : Type*} [CommRing A]
    [NoZeroDivisors A] [CommRing B] {n : ℕ} (F : A →+* B) (hF : Function.Surjective F)
    (hA : ringKrullDim A ≤ (n : WithBot ℕ∞)) (hB : (n : WithBot ℕ∞) ≤ ringKrullDim B) :
    Function.Injective F := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  have hle : Ideal.span {r} ≤ RingHom.ker F := Ideal.span_le.2 (by simpa using hr)
  have hquot : (n : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ Ideal.span {r}) := by
    refine hB.trans ?_
    rw [← ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hF)]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle)
  have hcontra : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
    push_cast
    calc (n : WithBot ℕ∞) + 1 ≤ ringKrullDim (A ⧸ Ideal.span {r}) + 1 := by gcongr
      _ ≤ ringKrullDim A :=
          ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hr0)
      _ ≤ (n : WithBot ℕ∞) := hA
  rw [Nat.cast_le] at hcontra
  omega

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The images in `R̂` of a regular system of parameters of `R` generate the maximal ideal of
`R̂`. -/
theorem span_range_algebraMap_eq_maximalIdeal {n : ℕ} {x : Fin n → R}
    (hx : MMP.Mori.IsRegularSystemOfParameters x) :
    Ideal.span (Set.range fun i => algebraMap R (AdicCompletion (maximalIdeal R) R) (x i)) =
      maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← hx.1, Ideal.map_span, ← Set.range_comp]
  rfl

/-- **The power series ring over a field of representatives, on a regular system of
parameters, is the completion.** Let `(R, 𝔪)` be a Noetherian local ring with a regular system of
parameters `x₁, …, xₙ` and `k' ⊆ R̂` a field of representatives of its completion. Then every
`k'`-algebra homomorphism `k'[[t₁, …, tₙ]] → R̂` with `tᵢ ↦ xᵢ` is bijective. -/
@[mmp "lem_mmp_foundation_regular_completion_with_given_coefficient_field"]
theorem bijective_of_isFieldOfRepresentatives {n : ℕ} {x : Fin n → R}
    (hx : MMP.Mori.IsRegularSystemOfParameters x)
    (K : Subring (AdicCompletion (maximalIdeal R) R))
    (hK : MMP.Resolution.IsFieldOfRepresentatives K)
    (F : MvPowerSeries (Fin n) K →ₐ[K] AdicCompletion (maximalIdeal R) R)
    (hF : ∀ i, F (MvPowerSeries.X i) = algebraMap R (AdicCompletion (maximalIdeal R) R) (x i)) :
    Function.Bijective F := by
  set Â := AdicCompletion (maximalIdeal R) R
  have hspan := span_range_algebraMap_eq_maximalIdeal hx
  obtain ⟨F₀, hF₀s, hF₀X, hF₀C⟩ :=
    Stacks.CompleteLocalRing.CohenStructure.exists_surjective_eval₂Hom (maximalIdeal Â)
      (fun i => algebraMap R Â (x i)) hspan K.subtype hK.2.2
  have hFeq : F.toRingHom = F₀ := by
    refine mvPowerSeries_hom_ext (maximalIdeal Â) n _ _ (fun r => ?_) (fun i => ?_) (fun i => ?_)
    · rw [hF₀C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, mvPowerSeries_C_eq_algebraMap,
        AlgHom.commutes]
      rfl
    · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hF, hF₀X]
    · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hF, ← hspan]
      exact Ideal.subset_span ⟨i, rfl⟩
  have hsurj : Function.Surjective F := by
    rw [show (F : MvPowerSeries (Fin n) K → Â) = F₀ from congrArg DFunLike.coe hFeq]
    exact hF₀s
  refine ⟨?_, hsurj⟩
  let : Field K := hK.1.toField
  exact injective_of_surjective_of_ringKrullDim_le F.toRingHom hsurj
    (MvPowerSeries.ringKrullDim_le K n) (by rw [← ringKrullDim_adicCompletion_maximalIdeal, hx.2])

/-- **The map `k'[[t₁, …, tₙ]] → R̂`, `tᵢ ↦ xᵢ`, exists**, for any field of representatives `k'`
of the completion and any regular system of parameters `x₁, …, xₙ` of `R`. -/
@[mmp "lem_mmp_foundation_regular_completion_with_given_coefficient_field"]
theorem exists_algHom_X_eq_of_isFieldOfRepresentatives {n : ℕ} {x : Fin n → R}
    (hx : MMP.Mori.IsRegularSystemOfParameters x)
    (K : Subring (AdicCompletion (maximalIdeal R) R))
    (hK : MMP.Resolution.IsFieldOfRepresentatives K) :
    ∃ F : MvPowerSeries (Fin n) K →ₐ[K] AdicCompletion (maximalIdeal R) R,
      ∀ i, F (MvPowerSeries.X i) = algebraMap R (AdicCompletion (maximalIdeal R) R) (x i) := by
  set Â := AdicCompletion (maximalIdeal R) R
  obtain ⟨F₀, -, hF₀X, hF₀C⟩ :=
    Stacks.CompleteLocalRing.CohenStructure.exists_surjective_eval₂Hom (maximalIdeal Â)
      (fun i => algebraMap R Â (x i)) (span_range_algebraMap_eq_maximalIdeal hx) K.subtype
      hK.2.2
  refine ⟨{ F₀ with commutes' := fun r => ?_ }, hF₀X⟩
  change F₀ (algebraMap K (MvPowerSeries (Fin n) K) r) = r
  rw [← mvPowerSeries_C_eq_algebraMap, hF₀C]
  rfl

/-- **The completed local ring at a point is the power series ring on a regular system of
parameters over a given field of representatives.** Let `X` be a locally Noetherian scheme (for
instance a scheme smooth over a field), `p ∈ X`, `x₁, …, xₙ` a regular system of parameters of
`𝒪_{p,X}` and `k' ⊆ 𝒪̂_{p,X}` a field of representatives. Then among the `k'`-algebra homomorphisms
`k'[[t₁, …, tₙ]] → 𝒪̂_{p,X}` with `tᵢ ↦ xᵢ`, there is exactly one that is bijective. -/
@[mmp "lem_mmp_foundation_regular_completion_with_given_coefficient_field"]
theorem existsUnique_algHom_X_eq_bijective_stalk {X : Scheme.{u}} [IsLocallyNoetherian X]
    (p : X) {n : ℕ} {x : Fin n → X.presheaf.stalk p}
    (hx : MMP.Mori.IsRegularSystemOfParameters x)
    (K : Subring (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)))
    (hK : MMP.Resolution.IsFieldOfRepresentatives K) :
    ∃! F : MvPowerSeries (Fin n) K →ₐ[K]
        AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p),
      (∀ i, F (MvPowerSeries.X i) = algebraMap (X.presheaf.stalk p) _ (x i)) ∧
        Function.Bijective F := by
  obtain ⟨F, hF⟩ := exists_algHom_X_eq_of_isFieldOfRepresentatives hx K hK
  refine ⟨F, ⟨hF, bijective_of_isFieldOfRepresentatives hx K hK F hF⟩, fun G ⟨hG, _⟩ => ?_⟩
  have h := mvPowerSeries_hom_ext (maximalIdeal (AdicCompletion
      (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))) n G.toRingHom F.toRingHom
    (fun r => by
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, mvPowerSeries_C_eq_algebraMap,
        AlgHom.commutes])
    (fun i => by rw [AlgHom.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      RingHom.coe_coe, hF, hG])
    (fun i => by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hG, ← span_range_algebraMap_eq_maximalIdeal hx]
      exact Ideal.subset_span ⟨i, rfl⟩)
  exact AlgHom.ext fun f => congrArg (fun ψ => ψ f) h

end RegularCompletion

/-! ### The coefficient field in characteristic zero -/

section CoefficientField

variable {k A : Type*} [Field k] [CommRing A] [IsLocalRing A]
  [IsAdicComplete (maximalIdeal A) A] [Algebra k A]

omit [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] in
/-- A subring containing `k` contains the values at its elements of polynomials over `k`. -/
theorem aeval_mem_of_range_subset (K : Subring A) (hk : Set.range (algebraMap k A) ⊆ K)
    {y : A} (hy : y ∈ K) (Q : k[X]) : aeval y Q ∈ K := by
  let S : Subalgebra k A := { K with algebraMap_mem' := fun c => hk ⟨c, rfl⟩ }
  exact Subalgebra.aeval_coe S ⟨y, hy⟩ Q ▸ (aeval (⟨y, hy⟩ : S) Q).2

omit [IsAdicComplete (maximalIdeal A) A] in
/-- Residue commutes with evaluating polynomials over `k`. -/
theorem residue_aeval (y : A) (Q : k[X]) : residue A (aeval y Q) = aeval (residue A y) Q :=
  (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom k A (ResidueField A)) y Q).symm

omit [IsAdicComplete (maximalIdeal A) A] in
/-- In a field of representatives containing `k`, every element `y` is a root of the minimal
polynomial over `k` of its residue. -/
theorem aeval_minpoly_residue_eq_zero (K : Subring A) (hk : Set.range (algebraMap k A) ⊆ K)
    (hK : MMP.Resolution.IsFieldOfRepresentatives K) {y : A} (hy : y ∈ K) :
    aeval y (minpoly k (residue A y)) = 0 := by
  have hmem := aeval_mem_of_range_subset K hk hy (minpoly k (residue A y))
  have h0 : residue A (aeval y (minpoly k (residue A y))) = 0 := by
    rw [residue_aeval, minpoly.aeval]
  have := hK.2.1 (a₁ := ⟨_, hmem⟩) (a₂ := 0) (by simpa using h0)
  simpa using congrArg Subtype.val this

/-- If the residue `b` of `y` is separable over `k`, then `y` is the only root of the minimal
polynomial of `b` with residue `b`. -/
theorem eq_of_aeval_minpoly_eq_zero {y z : A} (hsep : IsSeparable k (residue A y))
    (hy : aeval y (minpoly k (residue A y)) = 0) (hz : aeval z (minpoly k (residue A y)) = 0)
    (hzy : residue A z = residue A y) : z = y := by
  obtain ⟨a, -, ha⟩ := existsUnique_aeval_eq_zero_residue_eq (minpoly k (residue A y))
    (residue A y) (minpoly.aeval _ _)
    (hsep.aeval_derivative_ne_zero (minpoly.aeval _ _))
  exact (ha z ⟨hz, hzy⟩).trans (ha y ⟨hy, rfl⟩).symm

/-- **Rigidity of the coefficient field.** Let `A` be a complete local `k`-algebra whose residue
field is separable algebraic over `k`, and `K ⊆ A` a field of representatives containing `k`.
Every `k`-algebra endomorphism of `A` inducing the identity on the residue field is the identity
on `K`. -/
@[mmp "lem_mmp_foundation_char_zero_closed_point_coefficient_field"]
theorem eq_self_of_isFieldOfRepresentatives [Algebra.IsSeparable k (ResidueField A)]
    (K : Subring A) (hk : Set.range (algebraMap k A) ⊆ K)
    (hK : MMP.Resolution.IsFieldOfRepresentatives K) (φ : A →ₐ[k] A)
    (hφ : ∀ y, residue A (φ y) = residue A y) {a : A} (ha : a ∈ K) : φ a = a := by
  refine eq_of_aeval_minpoly_eq_zero (Algebra.IsSeparable.isSeparable k _)
    (aeval_minpoly_residue_eq_zero K hk hK ha) ?_ (hφ a)
  rw [Polynomial.aeval_algHom_apply, aeval_minpoly_residue_eq_zero K hk hK ha, map_zero]

/-- A field of representatives containing `k` of a complete local `k`-algebra with separable
residue field is contained in any other such field of representatives. -/
theorem le_of_isFieldOfRepresentatives [Algebra.IsSeparable k (ResidueField A)]
    (K K' : Subring A) (hk : Set.range (algebraMap k A) ⊆ K)
    (hK : MMP.Resolution.IsFieldOfRepresentatives K) (hk' : Set.range (algebraMap k A) ⊆ K')
    (hK' : MMP.Resolution.IsFieldOfRepresentatives K') : K ≤ K' := by
  intro y hy
  obtain ⟨⟨z, hz⟩, hzy⟩ := hK'.2.2 (residue A y)
  change residue A z = residue A y at hzy
  have hz0 : aeval z (minpoly k (residue A y)) = 0 := by
    rw [← hzy]
    exact aeval_minpoly_residue_eq_zero K' hk' hK' hz
  rw [← eq_of_aeval_minpoly_eq_zero (Algebra.IsSeparable.isSeparable k _)
    (aeval_minpoly_residue_eq_zero K hk hK hy) hz0 hzy]
  exact hz

/-- **Existence of the coefficient field.** A complete local `k`-algebra whose residue field is
finite and separable over `k` has a field of representatives containing `k`: the subring
`k[a]` generated by the root `a` lifting a primitive element of the residue field. -/
theorem exists_isFieldOfRepresentatives [Module.Finite k (ResidueField A)]
    [Algebra.IsSeparable k (ResidueField A)] :
    ∃ K : Subring A, Set.range (algebraMap k A) ⊆ K ∧
      MMP.Resolution.IsFieldOfRepresentatives K := by
  obtain ⟨b, hb⟩ := Field.exists_primitive_element k (ResidueField A)
  set P := minpoly k b
  have hint : IsIntegral k b := Algebra.IsIntegral.isIntegral b
  have hsep : IsSeparable k b := Algebra.IsSeparable.isSeparable k b
  obtain ⟨a, ⟨ha0, hab⟩, -⟩ := existsUnique_aeval_eq_zero_residue_eq P b (minpoly.aeval k b)
    (hsep.aeval_derivative_ne_zero (minpoly.aeval k b))
  have : Fact (Irreducible P) := ⟨minpoly.irreducible hint⟩
  let ψ : AdjoinRoot P →ₐ[k] A := AdjoinRoot.liftAlgHom P (Algebra.ofId k A) a (by
    rw [← ha0, aeval_def]; rfl)
  let e : AdjoinRoot P ≃ₐ[k] ψ.range := AlgEquiv.ofInjective ψ ψ.toRingHom.injective
  refine ⟨ψ.range.toSubring, fun _ ⟨c, hc⟩ => hc ▸ ψ.range.algebraMap_mem c, ?_, ?_, ?_⟩
  · exact MulEquiv.isField (Field.toIsField (AdjoinRoot P)) e.symm.toMulEquiv
  · intro y₁ y₂ h
    obtain ⟨w₁, rfl⟩ := e.surjective y₁
    obtain ⟨w₂, rfl⟩ := e.surjective y₂
    have h' : ((IsScalarTower.toAlgHom k A (ResidueField A)).comp ψ).toRingHom w₁ =
        ((IsScalarTower.toAlgHom k A (ResidueField A)).comp ψ).toRingHom w₂ := h
    rw [((IsScalarTower.toAlgHom k A (ResidueField A)).comp ψ).toRingHom.injective h']
  · intro z
    let θ := (IsScalarTower.toAlgHom k A (ResidueField A)).comp ψ
    have hθroot : θ (AdjoinRoot.root P) = b := by
      simp [θ, ψ, hab]
    have hadj : Algebra.adjoin k {b} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hb]
      rfl
    have hz : z ∈ θ.range := by
      have : Algebra.adjoin k {b} ≤ θ.range :=
        Algebra.adjoin_le (Set.singleton_subset_iff.2 ⟨_, hθroot⟩)
      exact this (hadj ▸ Algebra.mem_top)
    obtain ⟨w, rfl⟩ := hz
    exact ⟨⟨ψ w, ⟨w, rfl⟩⟩, rfl⟩

/-- **The coefficient field containing `k` is unique.** A complete local `k`-algebra whose residue
field is finite and separable over `k` has exactly one field of representatives containing
`k`. -/
@[mmp "lem_mmp_foundation_char_zero_closed_point_coefficient_field"]
theorem existsUnique_isFieldOfRepresentatives [Module.Finite k (ResidueField A)]
    [Algebra.IsSeparable k (ResidueField A)] :
    ∃! K : Subring A, Set.range (algebraMap k A) ⊆ K ∧
      MMP.Resolution.IsFieldOfRepresentatives K := by
  obtain ⟨K, hk, hK⟩ := exists_isFieldOfRepresentatives (k := k) (A := A)
  exact ⟨K, ⟨hk, hK⟩, fun K' ⟨hk', hK'⟩ => le_antisymm
    (le_of_isFieldOfRepresentatives K' K hk' hK' hk hK)
    (le_of_isFieldOfRepresentatives K K' hk hK hk' hK')⟩

end CoefficientField

/-- If the residue field of a Noetherian local `k`-algebra `R` is finite over `k`, so is the
residue field of its completion. -/
theorem finite_residueField_adicCompletion {k R : Type*} [Field k] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra k R] (h : Module.Finite k (ResidueField R)) :
    Module.Finite k (ResidueField (AdicCompletion (maximalIdeal R) R)) := by
  set Â := AdicCompletion (maximalIdeal R) R
  let ρ : ResidueField R →ₐ[k] ResidueField Â :=
    { ResidueField.map (algebraMap R Â) with
      commutes' := fun c => by
        change ResidueField.map (algebraMap R Â) (residue R (algebraMap k R c)) =
          residue Â (algebraMap k Â c)
        rw [ResidueField.map_residue, IsScalarTower.algebraMap_apply k R Â] }
  let ρe : ResidueField R ≃ₐ[k] ResidueField Â :=
    AlgEquiv.ofBijective ρ (AdicCompletion.residueField_map_bijective R)
  exact Module.Finite.equiv ρe.toLinearEquiv

section ClosedPoint

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [LocallyOfFiniteType sX] [IsLocallyNoetherian X]

/-- **The coefficient field of `𝒪̂_{p,X}` containing `k` is unique** at a closed point `p` of a
scheme `X` locally of finite type over a field `k` of characteristic zero: there is exactly one
subring of `𝒪̂_{p,X}` containing the image of `k` that is a field mapping isomorphically onto
`κ(p)`. The instance `[IsLocallyNoetherian X]` follows from `[LocallyOfFiniteType sX]`
(`LocallyOfFiniteType.isLocallyNoetherian`); it is carried so that `𝒪̂_{p,X}` is a local ring in
the statement. -/
@[mmp "lem_mmp_foundation_char_zero_closed_point_coefficient_field"]
theorem existsUnique_isFieldOfRepresentatives_completion (p : X) (hp : IsClosed ({p} : Set X)) :
    letI := MMP.Mori.stalkAlgebra sX p
    ∃! K : Subring (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)),
      Set.range (algebraMap k
        (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))) ⊆ K ∧
      MMP.Resolution.IsFieldOfRepresentatives K := by
  let := MMP.Mori.stalkAlgebra sX p
  have : Module.Finite k (ResidueField
      (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))) :=
    finite_residueField_adicCompletion (finite_residueField_of_isClosed sX p hp)
  have : Algebra.IsSeparable k (ResidueField
      (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact existsUnique_isFieldOfRepresentatives

/-- **Endomorphisms fix the coefficient field.** At a closed point `p` of a scheme locally of
finite type over a field `k` of characteristic zero, every `k`-algebra endomorphism of `𝒪̂_{p,X}`
inducing the identity on `κ(p)` (hence local) is the identity on the field of representatives
containing `k`. -/
@[mmp "lem_mmp_foundation_char_zero_closed_point_coefficient_field"]
theorem eq_self_of_isFieldOfRepresentatives_completion (p : X) (hp : IsClosed ({p} : Set X)) :
    letI := MMP.Mori.stalkAlgebra sX p
    ∀ K : Subring (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)),
      Set.range (algebraMap k
        (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))) ⊆ K →
      MMP.Resolution.IsFieldOfRepresentatives K →
      ∀ φ : AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) →ₐ[k]
          AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p),
        (∀ y, residue _ (φ y) = residue _ y) → ∀ a ∈ K, φ a = a := by
  let := MMP.Mori.stalkAlgebra sX p
  have : Module.Finite k (ResidueField
      (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))) :=
    finite_residueField_adicCompletion (finite_residueField_of_isClosed sX p hp)
  have : Algebra.IsSeparable k (ResidueField
      (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  intro K hk hK φ hφ a ha
  exact eq_self_of_isFieldOfRepresentatives K hk hK φ hφ ha

end ClosedPoint

end MMP.Flips.ResolutionInputs
