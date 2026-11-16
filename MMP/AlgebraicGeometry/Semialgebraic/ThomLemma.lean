module

public import MMP.AlgebraicGeometry.Semialgebraic.PolynomialSignTransfer
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Thom's lemma

Let `p` be a real polynomial and `ε` a sequence of signs. The set of `x ∈ ℝ` at which every
derivative `p⁽ⁿ⁾(x)` has the sign `εₙ` is an interval (possibly empty or a point): by induction
on the degree, the set `I` of points where the derivatives `p⁽ⁿ⁾`, `n ≥ 1`, have the prescribed
signs is an interval on which `p'` keeps one sign, so `p` is monotone on `I` and the points of
`I` where `p` has a given sign again form an interval.

Consequently, for a finite family of real polynomials closed under derivation, every sign
condition on the family defines an interval. In particular a zero of a member is determined by
the signs of the family at it, and the points with given signs avoiding all the zeros lie in one
band between consecutive zeros.

## Main results

* `MMP.ordConnected_setOf_sign_iterate_derivative`: Thom's lemma.
* `MMP.ordConnected_setOf_sign_eval_eq`: sign conditions on a family closed under
  derivation define intervals.

## References

* [J. Bochnak, M. Coste, M.-F. Roy, *Real algebraic geometry*][bochnak1998], Proposition 2.5.4.
-/

@[expose] public section

open Polynomial Set

namespace MMP

/-- On an interval where `p'` keeps one sign, the points where `p` has a given sign form an
interval. -/
theorem ordConnected_inter_setOf_sign_eval_eq {p : ℝ[X]} {I : Set ℝ} (hI : I.OrdConnected)
    {s : SignType} (hs : ∀ x ∈ I, SignType.sign ((derivative p).eval x) = s) (e : SignType) :
    (I ∩ {x | SignType.sign (p.eval x) = e}).OrdConnected := by
  refine ordConnected_def.2 fun x hx z hz y hy ↦ ⟨hI.out hx.1 hz.1 hy, ?_⟩
  simp only [mem_setOf_eq] at hx hz ⊢
  rcases eq_or_lt_of_le hy.1 with rfl | hxy
  · exact hx.2
  rcases eq_or_lt_of_le hy.2 with rfl | hyz
  · exact hz.2
  obtain ⟨c₁, hc₁, h₁⟩ := exists_eval_sub_eq_derivative_mul p hxy
  obtain ⟨c₂, hc₂, h₂⟩ := exists_eval_sub_eq_derivative_mul p hyz
  have e₁ := hs c₁ (hI.out hx.1 hz.1 ⟨hc₁.1.le, hc₁.2.le.trans hyz.le⟩)
  have e₂ := hs c₂ (hI.out hx.1 hz.1 ⟨hxy.le.trans hc₂.1.le, hc₂.2.le⟩)
  have hpos₁ : 0 < y - x := sub_pos.2 hxy
  have hpos₂ : 0 < z - y := sub_pos.2 hyz
  have hbetween : (p.eval x ≤ p.eval y ∧ p.eval y ≤ p.eval z) ∨
      (p.eval z ≤ p.eval y ∧ p.eval y ≤ p.eval x) := by
    rcases s with _ | _ | _
    · left
      change SignType.sign _ = 0 at e₁ e₂
      rw [sign_eq_zero_iff] at e₁ e₂
      constructor <;> nlinarith
    · right
      change SignType.sign _ = -1 at e₁ e₂
      rw [sign_eq_neg_one_iff] at e₁ e₂
      constructor <;> nlinarith
    · left
      change SignType.sign _ = 1 at e₁ e₂
      rw [sign_eq_one_iff] at e₁ e₂
      constructor <;> nlinarith
  rcases hbetween with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact le_antisymm (hz.2 ▸ SignType.sign.monotone h₂) (hx.2 ▸ SignType.sign.monotone h₁)
  · exact le_antisymm (hx.2 ▸ SignType.sign.monotone h₂) (hz.2 ▸ SignType.sign.monotone h₁)

/-- **Thom's lemma.** The set of points at which every derivative of a real polynomial has a
prescribed sign is an interval. -/
theorem ordConnected_setOf_sign_iterate_derivative (p : ℝ[X]) (ε : ℕ → SignType) :
    {x | ∀ n, SignType.sign ((derivative^[n] p).eval x) = ε n}.OrdConnected := by
  induction h : p.natDegree using Nat.strong_induction_on generalizing p ε with
  | _ d IH =>
  have hsplit : {x | ∀ n, SignType.sign ((derivative^[n] p).eval x) = ε n} =
      {x | ∀ n, SignType.sign ((derivative^[n] (derivative p)).eval x) = ε (n + 1)} ∩
        {x | SignType.sign (p.eval x) = ε 0} := by
    ext x
    simp only [mem_inter_iff, mem_setOf_eq, ← Function.iterate_succ_apply]
    exact ⟨fun H ↦ ⟨fun n ↦ H (n + 1), H 0⟩, fun ⟨H, H0⟩ n ↦ by cases n <;> simp_all⟩
  rw [hsplit]
  refine ordConnected_inter_setOf_sign_eval_eq ?_ (s := ε 1) (fun x hx ↦ by simpa using hx 0) _
  by_cases hd : d = 0
  · have hp' : derivative p = 0 := by
      rw [eq_C_of_natDegree_eq_zero (h.trans hd), derivative_C]
    simp only [hp', Function.iterate_fixed (derivative_zero (R := ℝ)), eval_zero, sign_zero]
    exact ordConnected_def.2 fun _ hx _ _ _ _ ↦ hx
  · exact IH _ (h ▸ natDegree_derivative_lt (h ▸ hd)) _ _ rfl

/-- **Thom's lemma for a family.** For a finite family of real polynomials closed under
derivation, every sign condition on the family defines an interval. -/
theorem ordConnected_setOf_sign_eval_eq {ι : Type*} {f : ι → ℝ[X]}
    (hder : ∀ i, ∃ j, f j = derivative (f i)) (ε : ι → SignType) :
    {x | ∀ i, SignType.sign ((f i).eval x) = ε i}.OrdConnected := by
  have hit : ∀ i n, ∃ j, f j = derivative^[n] (f i) := fun i n ↦ by
    induction n with
    | zero => exact ⟨i, rfl⟩
    | succ n ih =>
      obtain ⟨j, hj⟩ := ih
      obtain ⟨j', hj'⟩ := hder j
      exact ⟨j', by rw [hj', hj, Function.iterate_succ_apply']⟩
  choose J hJ using hit
  by_cases hne : {x | ∀ i, SignType.sign ((f i).eval x) = ε i}.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    have heq : {x | ∀ i, SignType.sign ((f i).eval x) = ε i} =
        ⋂ i, {x | ∀ n, SignType.sign ((derivative^[n] (f i)).eval x) = ε (J i n)} := by
      ext x
      simp only [mem_setOf_eq, mem_iInter]
      refine ⟨fun hx i n ↦ by rw [← hJ, hx], fun hx i ↦ ?_⟩
      have h0 := hx i 0
      rw [← hJ, ← hx₀ (J i 0), hJ] at h0
      simp only [Function.iterate_zero_apply] at h0
      rw [h0, hx₀ i]
    rw [heq]
    exact ordConnected_iInter fun i ↦ ordConnected_setOf_sign_iterate_derivative _ _
  · rw [not_nonempty_iff_eq_empty.1 hne]
    exact ordConnected_empty

end MMP
