module

public import MMP.AlgebraicGeometry.MMP.BasepointFree.StableBaseLocusEmpty

@[expose] public section

/-!
# The basepoint-free theorem

Let `(X, Δ)` be a proper klt pair over an algebraically closed field of characteristic zero,
with `Δ` effective, and let `D` be a nef Cartier divisor on `X` such that `aD - K_X - Δ` is nef
and big for some rational `a > 0`. Then the linear system `|bD|` is basepoint free for every
sufficiently large integer `b`.

The proof shows that the stable base loci `B_2` and `B_3` of `D` are empty; since `2` and `3`
are coprime, `|bD|` is then free for all large `b`.

## Main results

* `MMP.Mori.IsBasepointFreeDatum.exists_isBasepointFree_nsmul`: the basepoint-free theorem.

## Implementation notes

The hypotheses are bundled as `MMP.Mori.IsBasepointFreeDatum`, whose fields are exactly those
of the theorem (with `aD - K_X - Δ` also asserted to be `ℚ`-Cartier, which is how its nefness
and bigness are defined). The canonical divisor `K` and the dimension `n` are explicit, as in
`MMP.Mori.IsKltPair`. Basepoint freeness of `|bD|` is `MMP.Mori.Divisor.IsBasepointFree`, the
vanishing of the base locus `Bs|bD|`; for `b ≥ 0` the divisor `bD` is `b • D` with `b : ℕ`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 3.3,
  proof in 3.2
-/

open AlgebraicGeometry

namespace MMP.Mori

/-- **The basepoint-free theorem** (Kollár–Mori 3.3). Let `(X, Δ)` be a proper klt pair over an
algebraically closed field of characteristic zero with `Δ` effective, `D` a nef Cartier divisor
and `a > 0` rational with `aD - K_X - Δ` nef and big. Then there is `b₀` such that `|bD|` is
basepoint free for every `b ≥ b₀`. -/
@[mmp "thm_km3a_basepoint_free"]
public theorem IsBasepointFreeDatum.exists_isBasepointFree_nsmul
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : Divisor X} {a : ℚ}
    (h : IsBasepointFreeDatum sX n K Δ D a) :
    ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b → (b • D).IsBasepointFree :=
  D.exists_isBasepointFree_nsmul_of_coprime (by norm_num : Nat.Coprime 2 3)
    (h.stableBaseLocusOfPowers_eq_bot le_rfl) (h.stableBaseLocusOfPowers_eq_bot (by norm_num))

end MMP.Mori
