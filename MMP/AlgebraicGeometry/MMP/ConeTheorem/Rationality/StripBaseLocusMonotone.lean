module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.Rationality.SectorBasepointFree

/-!
# Strip base loci far out in a thin strip lie in a given one

Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r > 0` of `H` with respect to
`K_X + Δ`, let `ε > 0`, and let `p, q > 0` be integers with `aq - rp > 0`. Then there is `N`
such that the strip base locus `L(p', q')` is contained in `L(p, q)` for every `(p', q') ∈ ℤ²`
with `p', q' ≥ N` and `0 < aq' - rp' < ε`. Writing `(p', q') = k(p, q) + (x, y)` with
`k = ⌊θp'⌋` for a small `θ > 0`, the point `(x, y)` lies in a sector strictly inside the nef cone,
where `|xH + ya(K_X + Δ)|` is basepoint free; hence
`L(p', q') ⊆ L(kp, kq) ∪ L(x, y) = L(kp, kq) ⊆ L(p, q)`.

## Main results

* `MMP.Mori.IsRationalityDatum.exists_stripBaseLocus_le`

## Implementation notes

`L(p, q)` is `MMP.Mori.stripBaseLocus K Δ a H p q`, a closed subset of `X`, and containment is
the order on `TopologicalSpace.Closeds X`. The inequalities `aq - rp > 0` and `0 < aq' - rp' < ε`
are read in `ℝ`, in the form of `MMP.Mori.IsStableStripBaseLocus`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Claim 3.20
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.Km3bStripBaseLocusMonotoneProof

section

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (K : Divisor X) (Δ : QDivisor X) (a : ℤ) (H : Divisor X)

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] in
/-- `pH + qa(K_X + Δ)` is additive in `(p, q)`. -/
private theorem stripDivisor_add (p₁ q₁ p₂ q₂ : ℤ) :
    stripDivisor K Δ a H (p₁ + p₂) (q₁ + q₂) =
      stripDivisor K Δ a H p₁ q₁ + stripDivisor K Δ a H p₂ q₂ := by
  unfold stripDivisor
  rw [add_smul, add_smul]
  abel

/-- `L(p₁ + p₂, q₁ + q₂) ⊆ L(p₁, q₁) ∪ L(p₂, q₂)`. -/
private theorem stripBaseLocus_add_le (p₁ q₁ p₂ q₂ : ℤ) :
    stripBaseLocus K Δ a H (p₁ + p₂) (q₁ + q₂) ≤
      stripBaseLocus K Δ a H p₁ q₁ ⊔ stripBaseLocus K Δ a H p₂ q₂ := by
  unfold stripBaseLocus
  rw [stripDivisor_add]
  exact MMP.Positivity.baseLocus_add_le _ _

/-- `L((m + 1)p, (m + 1)q) ⊆ L(p, q)` for every `m : ℕ`. -/
private theorem stripBaseLocus_mul_le (p q : ℤ) (m : ℕ) :
    stripBaseLocus K Δ a H ((m + 1 : ℕ) * p) ((m + 1 : ℕ) * q) ≤ stripBaseLocus K Δ a H p q := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ (m + 1), add_one_mul, add_one_mul]
    exact (stripBaseLocus_add_le K Δ a H _ _ p q).trans (sup_le ih le_rfl)

end

/-- The arithmetic of the decomposition: for `r, ε > 0` and `p > 0` with `aq - rp > 0` there is
`0 < δ < r / 2` such that for every `N₀`, every `(p', q')` with `p' ≫ 0` and
`0 < aq' - rp' < ε` is `k(p, q) + (x, y)` with `k ≥ 1`, `x ≥ N₀` and `δx ≤ ay ≤ (r - δ)x`. -/
private theorem exists_sector_decomposition {a p q : ℤ} {r ε : ℝ} (hr0 : 0 < r)
    (hp : 0 < p) (hpq : 0 < (a * q : ℝ) - r * p) :
    ∃ δ : ℝ, 0 < δ ∧ δ < r / 2 ∧ ∀ N₀ : ℤ, ∃ N : ℤ, ∀ p' q' : ℤ, N ≤ p' →
      0 < (a * q' : ℝ) - r * p' → (a * q' : ℝ) - r * p' < ε →
      ∃ m : ℕ, ∃ x y : ℤ, p' = (m + 1 : ℕ) * p + x ∧ q' = (m + 1 : ℕ) * q + y ∧ N₀ ≤ x ∧
        δ * x ≤ (a * y : ℝ) ∧ (a * y : ℝ) ≤ (r - δ) * x := by
  obtain ⟨s, hs, hs0⟩ : ∃ s : ℝ, s = a * q - r * p ∧ 0 < s := ⟨_, rfl, hpq⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hsrp : 0 < s + r * p := by positivity
  obtain ⟨θ, hθ0, hθp, hθs⟩ : ∃ θ : ℝ, 0 < θ ∧ θ * p ≤ 1 / 2 ∧ θ * (s + r * p) ≤ r / 2 := by
    refine ⟨min (1 / (2 * (p : ℝ))) (r / (2 * (s + r * p))),
      lt_min (by positivity) (by positivity), ?_, ?_⟩
    · calc min (1 / (2 * (p : ℝ))) (r / (2 * (s + r * p))) * p ≤ 1 / (2 * p) * p := by
            gcongr; exact min_le_left _ _
        _ = 1 / 2 := by field_simp
    · calc min (1 / (2 * (p : ℝ))) (r / (2 * (s + r * p))) * (s + r * p)
            ≤ r / (2 * (s + r * p)) * (s + r * p) := by gcongr; exact min_le_right _ _
        _ = r / 2 := by field_simp
  obtain ⟨δ, hδ0, hδr, hδs⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ r / 4 ∧ δ ≤ θ * s / 2 :=
    ⟨min (r / 4) (θ * s / 2), lt_min (by positivity) (by positivity), min_le_left _ _,
      min_le_right _ _⟩
  have hθs0 : 0 < θ * s := mul_pos hθ0 hs0
  have hθsδ : 0 < θ * s - δ := by linarith
  refine ⟨δ, hδ0, by linarith, fun N₀ => ?_⟩
  refine ⟨max (max (2 * N₀) ⌈1 / θ⌉) ⌈(s + ε) / (θ * s - δ)⌉, fun p' q' hN he0 heε => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := by simpa only [max_le_iff] using hN
  have h2' : 1 / θ ≤ (p' : ℝ) := Int.ceil_le.mp h2
  have h3' : (s + ε) / (θ * s - δ) ≤ (p' : ℝ) := Int.ceil_le.mp h3
  have h1' : (2 * N₀ : ℝ) ≤ p' := by exact_mod_cast h1
  have hθP : 1 ≤ θ * p' := by
    rw [div_le_iff₀ hθ0] at h2'; linarith
  have hP3 : s + ε ≤ p' * (θ * s - δ) := (div_le_iff₀ hθsδ).mp h3'
  have hP0 : (0 : ℝ) < p' := lt_of_lt_of_le (by positivity) h2'
  -- `k = ⌊θp'⌋ ≥ 1` and `(x, y) = (p' - kp, q' - kq)`
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = ⌊θ * p'⌋ := ⟨_, rfl⟩
  have hk1 : 1 ≤ k := hk ▸ Int.le_floor.mpr (by simpa using hθP)
  have hkle : (k : ℝ) ≤ θ * p' := hk ▸ Int.floor_le _
  have hklt : θ * p' - 1 < k := by have := Int.lt_floor_add_one (θ * p'); rw [hk]; linarith
  have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast (show (0 : ℤ) ≤ k by omega)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = (m + 1 : ℕ) := ⟨(k - 1).toNat, by omega⟩
  refine ⟨m, p' - k * p, q' - k * q, by rw [hm]; ring, by rw [hm]; ring, ?_⟩
  push_cast
  have hkp : (k : ℝ) * p ≤ θ * p' * p := mul_le_mul_of_nonneg_right hkle hpR.le
  have hxlow : (p' : ℝ) * (1 - θ * p) ≤ p' - k * p := by linarith
  have hxP : (p' : ℝ) - k * p ≤ p' := by nlinarith
  have hkey : r * (p' - k * p) - a * (q' - k * q) = k * s - (a * q' - r * p') := by
    rw [hs]; ring
  refine ⟨?_, ?_, ?_⟩
  · -- `x ≥ p'(1 - θp) ≥ p' / 2 ≥ N₀`
    have h := mul_le_mul_of_nonneg_left hθp hP0.le
    have : (N₀ : ℝ) ≤ p' - k * p := by linarith
    exact_mod_cast this
  · -- `rx - ay < θsp' ≤ (r/2 - θrp)p' ≤ (r - δ)(1 - θp)p' ≤ (r - δ)x`
    have hks : (k : ℝ) * s ≤ θ * p' * s := mul_le_mul_of_nonneg_right hkle hs0.le
    have hA : θ * s * p' ≤ (r / 2 - θ * r * p) * p' :=
      mul_le_mul_of_nonneg_right (by linarith) hP0.le
    have hδθp : 0 ≤ δ * θ * p := mul_nonneg (mul_nonneg hδ0.le hθ0.le) hpR.le
    have hB : (r / 2 - θ * r * p) ≤ (r - δ) * (1 - θ * p) := by linarith
    have hC : (r - δ) * ((p' : ℝ) * (1 - θ * p)) ≤ (r - δ) * (p' - k * p) :=
      mul_le_mul_of_nonneg_left hxlow (by linarith)
    have hB' := mul_le_mul_of_nonneg_right hB hP0.le
    linarith
  · -- `rx - ay > (θp' - 1)s - ε ≥ δp' ≥ δx`
    have hks : (θ * p' - 1) * s < k * s := mul_lt_mul_of_pos_right hklt hs0
    have hx := mul_le_mul_of_nonneg_left hxP hδ0.le
    linarith

end MMP.FourfoldProofs.Km3bStripBaseLocusMonotoneProof

open MMP.FourfoldProofs.Km3bStripBaseLocusMonotoneProof

namespace MMP.Mori

/-- **Monotonicity of strip base loci** (Kollár–Mori, proof of Claim 3.20). Let `(X, Δ, a, H)`
be a rationality datum with nef threshold `r > 0` of `H` with respect to `K_X + Δ`, let `ε > 0`,
and let `p, q > 0` be integers with `0 < aq - rp`. Then there is `N` such that
`L(p', q') ⊆ L(p, q)` for all integers `p', q' ≥ N` with `0 < aq' - rp' < ε`. -/
@[mmp "lem_km3b_strip_base_locus_monotone"]
public theorem IsRationalityDatum.exists_stripBaseLocus_le {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} {a : ℤ} {H : Divisor X}
    (hD : IsRationalityDatum sX n K Δ a H) {r : ℝ}
    (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r)
    (hr0 : 0 < r) {ε : ℝ} (_hε : 0 < ε) {p q : ℤ} (hp : 0 < p) (_hq : 0 < q)
    (hpq : 0 < (a * q : ℝ) - r * p) :
    ∃ N : ℤ, ∀ p' q' : ℤ, N ≤ p' → N ≤ q' → 0 < (a * q' : ℝ) - r * p' →
      (a * q' : ℝ) - r * p' < ε → stripBaseLocus K Δ a H p' q' ≤ stripBaseLocus K Δ a H p q := by
  obtain ⟨δ, hδ0, hδr, hdec⟩ := exists_sector_decomposition hr0 hp hpq
  obtain ⟨N₀, hN₀⟩ := hD.exists_isBasepointFree_stripDivisor hr hr0 hδ0 hδr
  obtain ⟨N, hN⟩ := hdec N₀
  refine ⟨N, fun p' q' hp' _ h0 hε' => ?_⟩
  obtain ⟨m, x, y, rfl, rfl, hx, h₁, h₂⟩ := hN p' q' hp' h0 hε'
  exact (stripBaseLocus_add_le K Δ a H _ _ _ _).trans
    (sup_le (stripBaseLocus_mul_le K Δ a H p q m) ((hN₀ x y hx h₁ h₂).le.trans bot_le))

end MMP.Mori
