module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryAlgebra
public import MMP.AlgebraicGeometry.Divisor.Basic

/-!
# Exceptional support along a rational affine hull

Let `E_t = ∑ᵢ eᵢ(t) Pᵢ` be a family of real divisors on finitely many fixed prime divisors `Pᵢ`,
whose coefficients `eᵢ` are rational affine functions of the parameter `t ∈ ℝ^s`. If `E_δ ≥ 0`
and `W` is the smallest rational affine subspace containing `δ`, then on a neighbourhood of `δ`
in `W` every `E_t` is effective and has the same prime support as `E_δ`.

## Main results

* `MMP.Fourfold.exceptional_support_rational_hull`: the statement above, together with the
  inclusion of `W` in every rational affine subspace containing `δ`.

## Implementation notes

The finite divisor coefficient space is `ℝ^s` (coordinates `Fin s → ℝ`), `W` is
`MMP.Fourfold.rationalAffineHull δ`, and rational affine subspaces are
`MMP.Fourfold.IsRationalAffineSubspace`. In the case where the parameter is itself the coefficient
vector of a divisor supported on `P₁, …, Pₙ`, `W` is the set of coefficient vectors of the divisors
in `MMP.Fourfold.IsInSmallestRationalAffineHull` of the divisor of `δ`.
-/

@[expose] public noncomputable section

open Filter Topology MMP.Mori

universe u

namespace MMP.Fourfold

variable {X : AlgebraicGeometry.Scheme.{u}} {s n : ℕ}

/-- **Exceptional support along a rational affine hull.** Let `P : Fin n → PrimeDivisor X` be
prime divisors and `E t` a family of real divisors supported on them whose coefficient
along `Pᵢ` is the rational affine function `fᵢ(t)`. Let `V ⊆ ℝ^s` be a rational affine subspace
containing `δ` with `E δ ≥ 0`. Then the smallest rational affine subspace `W` containing `δ` lies
in `V`, and near `δ` in `W` every `E t` is effective with the same support as `E δ`. -/
@[mmp "lem_fourfold_exceptional_support_rational_hull"]
theorem exceptional_support_rational_hull (P : Fin n → PrimeDivisor X)
    (f : Fin n → (Fin s → ℚ) × ℚ) (E : (Fin s → ℝ) → RDivisor X)
    (hE : ∀ t i, (E t).coeff (P i) = ratAffineForm (f i) t)
    (hsupp : ∀ t, ↑(E t).support ⊆ Set.range P)
    {V : Set (Fin s → ℝ)} (hV : IsRationalAffineSubspace V) {δ : Fin s → ℝ} (hδV : δ ∈ V)
    (hδ : 0 ≤ E δ) :
    (rationalAffineHull δ : Set (Fin s → ℝ)) ⊆ V ∧
      ∀ᶠ t in 𝓝[(rationalAffineHull δ : Set (Fin s → ℝ))] δ,
        0 ≤ E t ∧ (E t).support = (E δ).support := by
  refine ⟨rationalAffineHull_le hV hδV, ?_⟩
  have key : ∀ᶠ t in 𝓝[(rationalAffineHull δ : Set (Fin s → ℝ))] δ,
      ∀ i, (0 < ratAffineForm (f i) δ → 0 < ratAffineForm (f i) t) ∧
        (ratAffineForm (f i) δ = 0 → ratAffineForm (f i) t = 0) := by
    refine (Filter.eventually_all.2 fun i => ?_)
    refine Filter.Eventually.and ?_ ?_
    · by_cases h : 0 < ratAffineForm (f i) δ
      · have := (continuous_ratAffineForm (f i)).continuousAt.eventually (lt_mem_nhds h)
        exact nhdsWithin_le_nhds (this.mono fun x hx _ => hx)
      · exact Filter.Eventually.of_forall fun x hx => absurd hx h
    · exact eventually_nhdsWithin_of_forall fun x hx h0 => hx (f i) h0
  filter_upwards [key] with t ht
  have hnn : ∀ i, 0 ≤ ratAffineForm (f i) δ := fun i => by
    rw [← hE]; exact hδ _
  have hcoef : ∀ i, 0 ≤ ratAffineForm (f i) t := fun i => by
    rcases (hnn i).eq_or_lt with h | h
    · rw [(ht i).2 h.symm]
    · exact ((ht i).1 h).le
  have outside : ∀ u, ∀ Q, Q ∉ Set.range P → (E u).coeff Q = 0 := fun u Q hQ => by
    by_contra h
    exact hQ (hsupp u (Finsupp.mem_support_iff.2 h))
  refine ⟨fun Q => ?_, ?_⟩
  · by_cases hQ : Q ∈ Set.range P
    · obtain ⟨i, rfl⟩ := hQ
      have := hcoef i
      rw [← hE] at this
      exact this
    · have := outside t Q hQ
      exact this.ge
  · ext Q
    simp only [Finsupp.mem_support_iff]
    by_cases hQ : Q ∈ Set.range P
    · obtain ⟨i, rfl⟩ := hQ
      have h1 := hE t i
      have h2 := hE δ i
      change (E t).coeff (P i) ≠ 0 ↔ (E δ).coeff (P i) ≠ 0
      rw [h1, h2]
      rcases (hnn i).eq_or_lt with h | h
      · rw [(ht i).2 h.symm, ← h]
      · exact ⟨fun _ => h.ne', fun _ => ((ht i).1 h).ne'⟩
    · have a := outside t Q hQ
      have b := outside δ Q hQ
      change (E t).coeff Q ≠ 0 ↔ (E δ).coeff Q ≠ 0
      rw [a, b]

end MMP.Fourfold
