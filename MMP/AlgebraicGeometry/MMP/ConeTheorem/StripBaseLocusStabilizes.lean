module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.Rationality.StripBaseLocusMonotone

@[expose] public section

/-!
# The strip base loci stabilize

Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r > 0` of `H` with respect to
`K_X + Δ`, and let `ε > 0`. Then the `(r, ε)`-strip has a stable base locus: a closed subset
`Z ⊆ X` with `L(p, q) = Z` for all integers `p, q ≥ N` with `0 < aq - rp < ε`, for some `N`.
If the strip has only finitely many positive lattice points, any `Z` works; otherwise a minimal
member `L(p₀, q₀)` of the strip base loci exists because `X` is noetherian, and monotonicity
(`MMP.Mori.IsRationalityDatum.exists_stripBaseLocus_le`) forces `L(p', q') = L(p₀, q₀)` far out.

## Main results

* `MMP.Mori.IsRationalityDatum.exists_isStableStripBaseLocus`

## Implementation notes

`L(p, q)` is `MMP.Mori.stripBaseLocus K Δ a H p q`, a closed subset of `X`, and "stable base
locus of the `(r, ε)`-strip" is `MMP.Mori.IsStableStripBaseLocus K Δ a H r ε`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Claim 3.20
-/

public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

/-- **The strip base loci stabilize** (Kollár–Mori, Claim 3.20). Let `(X, Δ, a, H)` be a
rationality datum with nef threshold `r > 0` of `H` with respect to `K_X + Δ`, and let `ε > 0`.
Then there is a stable base locus of the `(r, ε)`-strip: a closed subset `Z ⊆ X` and `N` with
`L(p, q) = Z` for all integers `p, q ≥ N` with `0 < aq - rp < ε`. -/
@[mmp "lem_km3b_base_locus_stabilizes"]
public theorem IsRationalityDatum.exists_isStableStripBaseLocus {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} {a : ℤ} {H : Divisor X}
    (hD : IsRationalityDatum sX n K Δ a H) {r : ℝ}
    (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r)
    (hr0 : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    ∃ Z : TopologicalSpace.Closeds X, IsStableStripBaseLocus K Δ a H r ε Z := by
  haveI : IsNoetherian X := ⟨⟩
  let S : Set (ℤ × ℤ) := {pq | 0 < pq.1 ∧ 0 < pq.2 ∧ 0 < (a * pq.2 : ℝ) - r * pq.1 ∧
    (a * pq.2 : ℝ) - r * pq.1 < ε}
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨⊤, 1, fun p q hp hq h1 h2 => ?_⟩
    have : (p, q) ∈ S := ⟨by omega, by omega, h1, h2⟩
    simp [hS] at this
  obtain ⟨_, ⟨⟨p₀, q₀⟩, hm, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := TopologicalSpace.Closeds X)).has_min
      ((fun pq : ℤ × ℤ => stripBaseLocus K Δ a H pq.1 pq.2) '' S) (hS.image _)
  obtain ⟨hp₀, hq₀, h₀, -⟩ := hm
  obtain ⟨N, hN⟩ := hD.exists_stripBaseLocus_le hr hr0 hε hp₀ hq₀ h₀
  refine ⟨stripBaseLocus K Δ a H p₀ q₀, max N 1, fun p q hp hq h1 h2 => ?_⟩
  exact eq_of_le_of_not_lt (hN p q (le_of_max_le_left hp) (le_of_max_le_left hq) h1 h2)
    (hmin _ ⟨(p, q), ⟨by omega, by omega, h1, h2⟩, rfl⟩)

end MMP.Mori
