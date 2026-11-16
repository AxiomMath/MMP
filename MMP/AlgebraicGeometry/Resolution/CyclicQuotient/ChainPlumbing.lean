module
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops

/-!
# The formal chain plumbing is a cyclic quotient

Let `K` be algebraically closed of characteristic zero, `r ≥ 1` and `b₁, …, b_r ≥ 2`. The formal
plumbing of the chain is glued from the charts `Spec K[x_j, y_j]`, `0 ≤ j ≤ r`, by
`x_i = x_{i-1}^{b_i} y_{i-1}`, `y_i = x_{i-1}⁻¹`, and completed along the exceptional chain,
whose ideal is `(y_0)` in the first chart, `(x_j y_j)` in an interior chart and `(x_r)` in the
last. Its ring of global functions is the ring of invariants `K[[u, v]]^{μ_m}` of a cyclic group
acting with weights `(1, q)`, `m ≥ 2`, `gcd(q, m) = 1`; the two end markings `x_0 = 0` and
`y_r = 0` correspond to the invariants vanishing on the axes `u = 0` and `v = 0`, and either end
marking may be chosen to become `u = 0`.

## Main results

* `MMP.Flips.exists_ringHom_cyclicInvariants_chainPlumbing`: the global ring of the formal chain
  plumbing is `MMP.Flips.cyclicInvariants K m q`, compatibly with the marking ideals.

## Implementation notes

Mathlib has no formal schemes. A global function on the completed plumbing is written out as a
family `(f_j)_{0 ≤ j ≤ r}` of power series in `K[[x, y]]` such that `f_j` lies in the completion
of `K[x, y]` along the exceptional ideal of chart `j` (for every `n`, only finitely many
monomials of `f_j` have exceptional order `< n`), and such that the coefficient functions of
consecutive charts, extended by zero to `ℤ²`, agree under the monomial transition
`x_{i-1}^a y_{i-1}^c = x_i^c y_i^{b_i c - a}`. Such a family is exactly a compatible family of
sections on the completed charts and their completed overlaps. A marking ideal is the ideal of
global functions whose restriction to the relevant end chart lies in the ideal of the marking.

## References

* [J. Kollár, *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

namespace MMP.Flips

open MvPowerSeries

namespace ChainPlumbing

noncomputable section

/-! ### The lattice recurrence -/

section Lattice

variable (bb : ℕ → ℤ)

/-- One step of the chain recurrence: `(x, y) ↦ (y, b y - x)`. -/
private def step (b : ℤ) : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) where
  toFun w := ![w 1, b * w 1 - w 0]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring

/-- The inverse step: `(x, y) ↦ (b x - y, x)`. -/
private def stepInv (b : ℤ) : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) where
  toFun w := ![b * w 0 - w 1, w 0]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring

private def tau : ℕ → (Fin 2 → ℤ) →+ (Fin 2 → ℤ)
  | 0 => AddMonoidHom.id _
  | k + 1 => (step (bb k)).comp (tau k)

private def tauInv : ℕ → (Fin 2 → ℤ) →+ (Fin 2 → ℤ)
  | 0 => AddMonoidHom.id _
  | k + 1 => (tauInv k).comp (stepInv (bb k))

private lemma tau_succ_zero (k w) : tau bb (k + 1) w 0 = tau bb k w 1 := rfl

private lemma tauInv_tau (k w) : tauInv bb k (tau bb k w) = w := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    change tauInv bb k (stepInv (bb k) (step (bb k) (tau bb k w))) = w
    have : stepInv (bb k) (step (bb k) (tau bb k w)) = tau bb k w := by
      ext i; fin_cases i <;> simp [step, stepInv]
    rw [this, ih]

private lemma tau_tauInv (k w) : tau bb k (tauInv bb k w) = w := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    change step (bb k) (tau bb k (tauInv bb k (stepInv (bb k) w))) = w
    rw [ih]; ext i; fin_cases i <;> simp [step, stepInv]

/-- The pairing `s_k` of a character with the `k`-th ray. -/
private abbrev s (k : ℕ) (w : Fin 2 → ℤ) : ℤ := tau bb k w 0

private lemma s_succ_succ (k w) : s bb (k + 2) w = bb k * s bb (k + 1) w - s bb k w := rfl

private lemma s_linear (k) (w : Fin 2 → ℤ) :
    s bb k w = w 0 * s bb k ![1, 0] + w 1 * s bb k ![0, 1] := by
  have hw : w = w 0 • ![1, 0] + w 1 • ![0, 1] := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [hw]
  simp only [s, map_add, map_zsmul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

variable {bb} (hbb : ∀ i, 2 ≤ bb i)

include hbb

/-- Once the sequence decreases to a nonpositive value, it stays strictly decreasing. -/
private lemma propagate (k : ℕ) (w : Fin 2 → ℤ) (h1 : s bb (k + 1) w < s bb k w)
    (h2 : s bb (k + 1) w ≤ 0) (n : ℕ) :
    s bb (k + n + 1) w < s bb (k + n) w ∧ s bb (k + n + 1) w ≤ 0 := by
  induction n with
  | zero => exact ⟨h1, h2⟩
  | succ n ih =>
    have := s_succ_succ bb (k + n) w
    have hb := hbb (k + n)
    rw [show k + (n + 1) + 1 = k + n + 2 by ring, show k + (n + 1) = k + n + 1 by ring]
    constructor <;> nlinarith [ih.1, ih.2]

private lemma neg_of_decrease (r : ℕ) (k : ℕ) (hk : k + 1 ≤ r) (w : Fin 2 → ℤ)
    (h1 : s bb (k + 1) w < s bb k w) (h2 : s bb (k + 1) w ≤ 0) : s bb (r + 1) w < 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, r = k + n + 1 := ⟨r - k - 1, by omega⟩
  have h := propagate hbb k w h1 h2 (n + 1)
  have h' := propagate hbb k w h1 h2 n
  rw [show k + (n + 1) + 1 = k + n + 1 + 1 by ring, show k + (n + 1) = k + n + 1 by ring]
    at h
  linarith [h.1, h'.2]

/-- **Strict cone fact.** A nonzero character with nonnegative boundary pairings has strictly
positive interior pairings. -/
private lemma s_pos (r : ℕ) (w : Fin 2 → ℤ) (hw : w ≠ 0) (h0 : 0 ≤ s bb 0 w)
    (hr1 : 0 ≤ s bb (r + 1) w) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r) : 0 < s bb k w := by
  induction k, hk1 using Nat.le_induction with
  | base =>
    by_contra hneg
    push Not at hneg
    by_cases hlt : s bb 1 w < s bb 0 w
    · exact absurd hr1 (not_le.mpr (neg_of_decrease hbb r 0 hkr w hlt hneg))
    · apply hw
      have e0 : w 0 = 0 := by change s bb 0 w = 0; omega
      have e1 : w 1 = 0 := by change s bb 1 w = 0; omega
      ext i; fin_cases i <;> simp [e0, e1]
  | succ k hk ih =>
    have hpos := ih (by omega)
    by_contra hneg
    push Not at hneg
    exact absurd hr1 (not_le.mpr (neg_of_decrease hbb r k hkr w (by omega) hneg))

/-- **Cone fact.** A character with nonnegative boundary pairings pairs nonnegatively with every
ray of the chain. -/
private lemma s_nonneg (r : ℕ) (w : Fin 2 → ℤ) (h0 : 0 ≤ s bb 0 w)
    (hr1 : 0 ≤ s bb (r + 1) w) (k : ℕ) (hk : k ≤ r + 1) : 0 ≤ s bb k w := by
  by_cases hw : w = 0
  · subst hw; simp [s]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact h0
  rcases eq_or_lt_of_le hk with rfl | hk'
  · exact hr1
  exact (s_pos hbb r w hw h0 hr1 k hk0 (by omega)).le

private lemma B_growth (k : ℕ) :
    (k : ℤ) ≤ s bb k ![0, 1] ∧ s bb k ![0, 1] + 1 ≤ s bb (k + 1) ![0, 1] := by
  induction k with
  | zero => simp [s, tau, step]
  | succ k ih =>
    have := s_succ_succ bb k ![0, 1]
    have hb := hbb k
    push_cast
    constructor <;> nlinarith [ih.1, ih.2]

omit hbb in
private lemma det_eq_one (k : ℕ) :
    s bb k ![1, 0] * s bb (k + 1) ![0, 1] - s bb (k + 1) ![1, 0] * s bb k ![0, 1] = 1 := by
  induction k with
  | zero => simp [s, tau, step]
  | succ k ih =>
    rw [s_succ_succ, s_succ_succ]; linear_combination ih

end Lattice

/-! ### The boundary pairings and the invariant lattice -/

section Boundary

variable (bb : ℕ → ℤ) (r : ℕ) (σ : Equiv.Perm (Fin 2))

/-- The boundary pairings `(s₀, s_{r+1})` of a character, placed at the coordinates `σ 0` and
`σ 1`. -/
private def boundaryMap : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) where
  toFun w i := if i = σ 0 then w 0 else tau bb r w 1
  map_zero' := by ext i; simp
  map_add' x y := by ext i; by_cases h : i = σ 0 <;> simp [h]

private lemma fin_two_cases (x : Fin 2) : x = 0 ∨ x = 1 := by fin_cases x <;> simp

private lemma boundaryMap_apply_zero_one (w : Fin 2 → ℤ) :
    (σ 0 = 0 ∧ boundaryMap bb r σ w 0 = w 0 ∧ boundaryMap bb r σ w 1 = s bb (r + 1) w) ∨
      (σ 0 = 1 ∧ boundaryMap bb r σ w 0 = s bb (r + 1) w ∧ boundaryMap bb r σ w 1 = w 0) := by
  rcases fin_two_cases (σ 0) with h | h
  · left; simp [boundaryMap, h]; rfl
  · right; simp [boundaryMap, h]; rfl

private lemma boundaryMap_apply_σ_zero (w : Fin 2 → ℤ) : boundaryMap bb r σ w (σ 0) = w 0 := by
  simp [boundaryMap]

private lemma boundaryMap_apply_σ_one (w : Fin 2 → ℤ) :
    boundaryMap bb r σ w (σ 1) = s bb (r + 1) w := by
  simp [boundaryMap, σ.injective.ne (show (1 : Fin 2) ≠ 0 by decide)]; rfl

private lemma boundaryMap_nonneg_iff (w : Fin 2 → ℤ) :
    (0 ≤ boundaryMap bb r σ w 0 ∧ 0 ≤ boundaryMap bb r σ w 1) ↔ (0 ≤ w 0 ∧ 0 ≤ s bb (r + 1) w) := by
  rcases boundaryMap_apply_zero_one bb r σ w with ⟨-, h0, h1⟩ | ⟨-, h0, h1⟩ <;> rw [h0, h1]
  exact and_comm

/-- The order `m` of the cyclic group. -/
private abbrev cyclicOrder : ℤ := s bb (r + 1) ![0, 1]

/-- The weight `q` of the second coordinate. -/
private def qq : ℤ := if σ 0 = 0 then s bb r ![0, 1] else -s bb (r + 1) ![1, 0]

variable {bb} (hbb : ∀ i, 2 ≤ bb i)

include hbb

private lemma two_le_cyclicOrder (hr : 1 ≤ r) : 2 ≤ cyclicOrder bb r := by
  have := (B_growth hbb (r + 1)).1; push_cast at this; simp only [cyclicOrder]; omega

private lemma boundaryMap_injective (hr : 1 ≤ r) : Function.Injective (boundaryMap bb r σ) := by
  refine (injective_iff_map_eq_zero _).mpr fun w hw => ?_
  have h0 := boundaryMap_apply_σ_zero bb r σ w
  have h1 := boundaryMap_apply_σ_one bb r σ w
  rw [hw] at h0 h1
  have hl := s_linear bb (r + 1) w
  have hM := two_le_cyclicOrder r hbb hr
  simp only [Pi.zero_apply] at h0 h1
  have hw1 : w 1 = 0 := by
    have : w 1 * cyclicOrder bb r = 0 := by simp only [cyclicOrder]; rw [← h0] at hl; linarith
    exact (mul_eq_zero.mp this).resolve_right (by omega)
  ext i; fin_cases i <;> simp [← h0, hw1]

omit hbb in
private lemma exists_boundaryMap_eq_iff (d : Fin 2 → ℤ) :
    (∃ w, boundaryMap bb r σ w = d) ↔ cyclicOrder bb r ∣ d 0 + qq bb r σ * d 1 := by
  have hdet := det_eq_one (bb := bb) r
  have hl := s_linear bb (r + 1)
  rcases fin_two_cases (σ 0) with h | h
  · simp only [qq, h, if_true]
    constructor
    · rintro ⟨w, rfl⟩
      rcases boundaryMap_apply_zero_one bb r σ w with ⟨-, h0, h1⟩ | ⟨h', -, -⟩
      · rw [h0, h1, hl]
        exact ⟨w 0 * s bb r ![1, 0] + s bb r ![0, 1] * w 1, by linear_combination (-w 0) * hdet⟩
      · exact absurd (h.symm.trans h') (by decide)
    · rintro ⟨k, hk⟩
      refine ⟨![d 0, d 1 * s bb r ![1, 0] - s bb (r + 1) ![1, 0] * k], ?_⟩
      funext i
      rcases boundaryMap_apply_zero_one bb r σ
          ![d 0, d 1 * s bb r ![1, 0] - s bb (r + 1) ![1, 0] * k]
        with ⟨-, h0, h1⟩ | ⟨h', -, -⟩
      · rcases fin_two_cases i with rfl | rfl
        · rw [h0]; rfl
        · rw [h1, hl]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linear_combination (d 1) * hdet + s bb (r + 1) ![1, 0] * hk
      · exact absurd (h.symm.trans h') (by decide)
  · simp only [qq, h, show (1 : Fin 2) ≠ 0 by decide, if_false]
    constructor
    · rintro ⟨w, rfl⟩
      rcases boundaryMap_apply_zero_one bb r σ w with ⟨h', -, -⟩ | ⟨-, h0, h1⟩
      · exact absurd (h.symm.trans h') (by decide)
      · rw [h0, h1, hl]
        exact ⟨w 1, by ring⟩
    · rintro ⟨k, hk⟩
      refine ⟨![d 1, k], ?_⟩
      funext i
      rcases boundaryMap_apply_zero_one bb r σ ![d 1, k] with ⟨h', -, -⟩ | ⟨-, h0, h1⟩
      · exact absurd (h.symm.trans h') (by decide)
      · rcases fin_two_cases i with rfl | rfl
        · rw [h0, hl]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linear_combination (-1 : ℤ) * hk
        · rw [h1]; rfl

omit hbb in
private lemma isCoprime_qq : IsCoprime (qq bb r σ) (cyclicOrder bb r) := by
  have hdet := det_eq_one (bb := bb) r
  unfold qq
  split_ifs
  · exact ⟨-s bb (r + 1) ![1, 0], s bb r ![1, 0], by
      simp only [cyclicOrder]; linear_combination hdet⟩
  · exact ⟨s bb r ![0, 1], s bb r ![1, 0], by simp only [cyclicOrder]; linear_combination hdet⟩

/-- Interior pairings control the boundary pairings. -/
private lemma boundary_le (hr : 1 ≤ r) (w : Fin 2 → ℤ) (h0 : 0 ≤ s bb 0 w)
    (hr1 : 0 ≤ s bb (r + 1) w) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r) :
    s bb 0 w ≤ cyclicOrder bb r * s bb k w ∧ s bb (r + 1) w ≤ cyclicOrder bb r * s bb k w := by
  have hM := two_le_cyclicOrder r hbb hr
  set w' : Fin 2 → ℤ := ![cyclicOrder bb r, -s bb (r + 1) ![1, 0]]
  have hw'0 : w' ≠ 0 := fun h => by
    have := congrFun h 0; simp [w'] at this; omega
  have hl := s_linear bb
  have hs0w' : s bb 0 w' = cyclicOrder bb r := rfl
  have hsrw' : s bb (r + 1) w' = 0 := by rw [hl]; simp [w', cyclicOrder]; ring
  have hα := s_pos hbb r w' hw'0 (by omega) hsrw'.ge k hk1 hkr
  have hB := s_pos hbb r ![0, 1] (by simp) (by simp [s, tau])
    (by simp only [cyclicOrder] at hM; omega) k hk1 hkr
  have hwk := hl k w
  have hw'k := hl k w'
  have hwr := hl (r + 1) w
  simp only [w', Matrix.cons_val_zero, Matrix.cons_val_one] at hw'k
  have h0' : s bb 0 w = w 0 := rfl
  have key : cyclicOrder bb r * s bb k w =
      s bb 0 w * s bb k w' + s bb (r + 1) w * s bb k ![0, 1] := by
    rw [hwk, hw'k, hwr, h0']; simp only [cyclicOrder]; ring
  constructor <;> nlinarith

end Boundary

/-! ### Coefficients on the lattice and monomial reindexing -/

section Series

variable {K : Type*} [Field K]

/-- The coefficient of `x^a y^c`, extended by zero to all of `ℤ²`. -/
private def czF (f : MvPowerSeries (Fin 2) K) (a c : ℤ) : K :=
  if 0 ≤ a ∧ 0 ≤ c then coeff (Finsupp.single 0 a.toNat + Finsupp.single 1 c.toNat) f else 0

private abbrev czV (f : MvPowerSeries (Fin 2) K) (d : Fin 2 → ℤ) : K := czF f (d 0) (d 1)

private def ι (e : Fin 2 →₀ ℕ) : Fin 2 → ℤ := ![(e 0 : ℤ), (e 1 : ℤ)]

private def toFin (d : Fin 2 → ℤ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (d 0).toNat + Finsupp.single 1 (d 1).toNat

private lemma toFin_ι (e : Fin 2 →₀ ℕ) : toFin (ι e) = e := by
  ext i; fin_cases i <;> simp [toFin, ι]

private lemma ι_toFin {d : Fin 2 → ℤ} (h0 : 0 ≤ d 0) (h1 : 0 ≤ d 1) : ι (toFin d) = d := by
  ext i; fin_cases i <;> simp [toFin, ι, h0, h1]

private lemma ι_zero : ι 0 = 0 := by ext i; fin_cases i <;> simp [ι]

private lemma ι_injective : Function.Injective ι := fun a b h => by
  rw [← toFin_ι a, h, toFin_ι]

private lemma ι_add (a b : Fin 2 →₀ ℕ) : ι (a + b) = ι a + ι b := by
  ext i; fin_cases i <;> simp [ι]

private lemma ι_nonneg (e : Fin 2 →₀ ℕ) : 0 ≤ ι e 0 ∧ 0 ≤ ι e 1 := by simp [ι]

private lemma czV_eq (f : MvPowerSeries (Fin 2) K) (d : Fin 2 → ℤ) :
    czV f d = if 0 ≤ d 0 ∧ 0 ≤ d 1 then coeff (toFin d) f else 0 := rfl

private lemma czV_ι (f : MvPowerSeries (Fin 2) K) (e : Fin 2 →₀ ℕ) :
    czV f (ι e) = coeff e f := by
  rw [czV_eq, if_pos (ι_nonneg e), toFin_ι]

private lemma nonneg_of_czV_ne_zero {f : MvPowerSeries (Fin 2) K} {d : Fin 2 → ℤ}
    (h : czV f d ≠ 0) : 0 ≤ d 0 ∧ 0 ≤ d 1 := by
  rw [czV_eq] at h; split_ifs at h with h'; exacts [h', absurd rfl h]

private lemma nonneg_of_czV_mul_ne_zero {f g : MvPowerSeries (Fin 2) K} {a b : Fin 2 → ℤ}
    (h : czV f a * czV g b ≠ 0) : (0 ≤ a 0 ∧ 0 ≤ a 1) ∧ (0 ≤ b 0 ∧ 0 ≤ b 1) :=
  ⟨nonneg_of_czV_ne_zero (left_ne_zero_of_mul h), nonneg_of_czV_ne_zero (right_ne_zero_of_mul h)⟩

/-- The pull-back of a power series along a lattice map of exponents. -/
private def pull (Φ : (Fin 2 → ℤ) →+ (Fin 2 → ℤ)) (g : MvPowerSeries (Fin 2) K) :
    MvPowerSeries (Fin 2) K := fun e => czV g (Φ (ι e))

private lemma coeff_pull (Φ : (Fin 2 → ℤ) →+ (Fin 2 → ℤ)) (g : MvPowerSeries (Fin 2) K) (e) :
    coeff e (pull Φ g) = czV g (Φ (ι e)) := rfl

private lemma pull_add (Φ : (Fin 2 → ℤ) →+ (Fin 2 → ℤ)) (g h : MvPowerSeries (Fin 2) K) :
    pull Φ (g + h) = pull Φ g + pull Φ h := by
  ext e; simp only [coeff_pull, map_add, czV_eq]; split_ifs <;> simp

private lemma pull_C (Φ : (Fin 2 → ℤ) →+ (Fin 2 → ℤ)) (hΦ : Function.Injective Φ) (k : K) :
    pull Φ (C k) = C k := by
  ext e
  rw [coeff_pull, coeff_C, czV_eq]
  by_cases he : e = 0
  · subst he
    rw [ι_zero, map_zero]
    simp [toFin]
  · rw [if_neg he]
    split_ifs with h1
    · rw [coeff_C, if_neg]
      intro h2
      apply he
      have := ι_toFin h1.1 h1.2
      rw [h2, ι_zero, ← map_zero Φ] at this
      exact ι_injective (hΦ this.symm |>.trans ι_zero.symm)
    · rfl

/-- Pulling back along an injective lattice map is multiplicative on series supported in its
image. -/
private lemma pull_mul (Φ : (Fin 2 → ℤ) →+ (Fin 2 → ℤ)) (hΦ : Function.Injective Φ)
    (g h : MvPowerSeries (Fin 2) K)
    (hg : ∀ d, coeff d g ≠ 0 → ∃ e, Φ (ι e) = ι d)
    (hh : ∀ d, coeff d h ≠ 0 → ∃ e, Φ (ι e) = ι d) :
    pull Φ (g * h) = pull Φ g * pull Φ h := by
  classical
  ext e
  rw [coeff_pull, coeff_mul]
  simp only [coeff_pull]
  by_cases hD : 0 ≤ Φ (ι e) 0 ∧ 0 ≤ Φ (ι e) 1
  · rw [czV_eq, if_pos hD, coeff_mul]
    symm
    refine Finset.sum_bij_ne_zero (fun p _ _ => (toFin (Φ (ι p.1)), toFin (Φ (ι p.2))))
      ?_ ?_ ?_ ?_
    · intro p hp hne
      obtain ⟨h1, h2⟩ := nonneg_of_czV_mul_ne_zero hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
      apply ι_injective
      rw [ι_add, ι_toFin h1.1 h1.2, ι_toFin h2.1 h2.2, ι_toFin hD.1 hD.2, ← map_add, ← ι_add, hp]
    · intro p _ hne p' _ hne' heq
      obtain ⟨h1, h2⟩ := nonneg_of_czV_mul_ne_zero hne
      obtain ⟨h1', h2'⟩ := nonneg_of_czV_mul_ne_zero hne'
      simp only [Prod.mk.injEq] at heq
      have e1 := congrArg ι heq.1
      have e2 := congrArg ι heq.2
      rw [ι_toFin h1.1 h1.2, ι_toFin h1'.1 h1'.2] at e1
      rw [ι_toFin h2.1 h2.2, ι_toFin h2'.1 h2'.2] at e2
      exact Prod.ext (ι_injective (hΦ e1)) (ι_injective (hΦ e2))
    · intro p hp hne
      obtain ⟨e1, he1⟩ := hg p.1 (left_ne_zero_of_mul hne)
      obtain ⟨e2, he2⟩ := hh p.2 (right_ne_zero_of_mul hne)
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have hsum : e1 + e2 = e := by
        apply ι_injective; apply hΦ
        rw [ι_add, map_add, he1, he2, ← ι_add, hp, ι_toFin hD.1 hD.2]
      refine ⟨(e1, e2), Finset.HasAntidiagonal.mem_antidiagonal.mpr hsum, ?_, ?_⟩
      · simpa only [he1, he2, czV_ι] using hne
      · simp only [he1, he2, toFin_ι]
    · intro p _ hne
      obtain ⟨h1, h2⟩ := nonneg_of_czV_mul_ne_zero hne
      rw [czV_eq, if_pos h1, czV_eq, if_pos h2]
  · rw [czV_eq, if_neg hD]
    symm
    refine Finset.sum_eq_zero fun p hp => ?_
    by_contra hne
    obtain ⟨h1, h2⟩ := nonneg_of_czV_mul_ne_zero hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    apply hD
    rw [← hp, ι_add, map_add]
    simp only [Pi.add_apply]
    omega

end Series

/-! ### The invariants of the cyclic action -/

section Invariants

variable {K : Type*} [Field K]

private lemma coeff_rescale_cyclicWeights (m : ℕ) (q : ℤ) (ζ : rootsOfUnity m K)
    (g : MvPowerSeries (Fin 2) K) (d : Fin 2 →₀ ℕ) :
    coeff d (rescale (cyclicWeights K m q ζ) g) =
      ((ζ : Kˣ) : K) ^ ((d 0 : ℤ) + q * d 1) * coeff d g := by
  rw [coeff_rescale, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  change (((ζ : Kˣ) : K) ^ d 0 * (((ζ : Kˣ) ^ q : Kˣ) : K) ^ d 1) * _ = _
  have hu : ((ζ : Kˣ) : K) ≠ 0 := Units.ne_zero _
  rw [Units.val_zpow_eq_zpow_val, zpow_add₀ hu, zpow_mul, zpow_natCast, zpow_natCast]

private lemma mem_cyclicInvariants_iff_dvd [IsAlgClosed K] [CharZero K] (m : ℕ) (hm : m ≠ 0)
    (q : ℤ) (g : MvPowerSeries (Fin 2) K) :
    g ∈ cyclicInvariants K m q ↔ ∀ d, coeff d g ≠ 0 → (m : ℤ) ∣ d 0 + q * d 1 := by
  haveI : NeZero m := ⟨hm⟩
  rw [mem_cyclicInvariants_iff]
  constructor
  · intro H d hd
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K m
    have := congrArg (coeff d) (H hζ.toRootsOfUnity)
    rw [coeff_rescale_cyclicWeights, hζ.val_toRootsOfUnity_coe] at this
    have h1 : ζ ^ ((d 0 : ℤ) + q * d 1) = 1 := mul_right_cancel₀ hd (this.trans (one_mul _).symm)
    exact (hζ.zpow_eq_one_iff_dvd _).mp h1
  · intro H ζ
    ext d
    rw [coeff_rescale_cyclicWeights]
    by_cases hd : coeff d g = 0
    · rw [hd, mul_zero]
    obtain ⟨t, ht⟩ := H d hd
    have hζ : ((ζ : Kˣ) : K) ^ (m : ℕ) = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity m _).mp ζ.2, Units.val_one]
    rw [ht, zpow_mul, zpow_natCast, hζ, one_zpow, one_mul]

end Invariants

/-! ### The chart maps -/

section Charts

/-- The weights of the chain, extended by `2` beyond `r`. -/
private def bbOf {r : ℕ} (b : Fin r → ℕ) : ℕ → ℤ := fun i => if h : i < r then (b ⟨i, h⟩ : ℤ) else 2

private lemma bbOf_ge {r : ℕ} (b : Fin r → ℕ) (hb : ∀ i, 2 ≤ b i) (i : ℕ) : 2 ≤ bbOf b i := by
  unfold bbOf; split_ifs with h
  · exact_mod_cast hb _
  · exact le_rfl

private lemma bbOf_val {r : ℕ} (b : Fin r → ℕ) (i : Fin r) : bbOf b i = b i := by simp [bbOf, i.2]

variable (bb : ℕ → ℤ) (r : ℕ) (σ : Equiv.Perm (Fin 2))

/-- The exponent map of chart `j`: chart exponents to exponents of `K[[u, v]]`. -/
private def chartExpMap (j : ℕ) : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) :=
  (boundaryMap bb r σ).comp (tauInv bb j)

private lemma chartExpMap_apply (j : ℕ) (x) :
    chartExpMap bb r σ j x = boundaryMap bb r σ (tauInv bb j x) := rfl

variable {K : Type*} [Field K]

private lemma czF_pull (Ψ : (Fin 2 → ℤ) →+ (Fin 2 → ℤ)) (g : MvPowerSeries (Fin 2) K) (a c : ℤ) :
    czF (pull Ψ g) a c = if 0 ≤ a ∧ 0 ≤ c then czV g (Ψ ![a, c]) else 0 := by
  unfold czF
  split_ifs with h
  · change czV g (Ψ (ι (toFin ![a, c]))) = _
    rw [ι_toFin h.1 h.2]
  · rfl

private lemma toFin_apply (d : Fin 2 → ℤ) (i : Fin 2) : toFin d i = (d i).toNat := by
  fin_cases i <;> simp [toFin]

private lemma ι_apply (e : Fin 2 →₀ ℕ) (i : Fin 2) : ι e i = e i := by
  fin_cases i <;> rfl

variable {bb} (hbb : ∀ i, 2 ≤ bb i)

include hbb

private lemma chartExpMap_injective (hr : 1 ≤ r) (j : ℕ) :
    Function.Injective (chartExpMap bb r σ j) :=
  (boundaryMap_injective r σ hbb hr).comp (Function.LeftInverse.injective (g := tau bb j)
    (tau_tauInv bb j))

private lemma support_of_czV (g : MvPowerSeries (Fin 2) K) (w : Fin 2 → ℤ)
    (h : czV g (boundaryMap bb r σ w) ≠ 0) (k : ℕ) (hk : k ≤ r + 1) : 0 ≤ s bb k w := by
  have := (boundaryMap_nonneg_iff bb r σ w).mp (nonneg_of_czV_ne_zero h)
  exact s_nonneg hbb r w this.1 this.2 k hk

private lemma exists_chartExpMap_eq [IsAlgClosed K] [CharZero K] (hr : 1 ≤ r)
    (g : MvPowerSeries (Fin 2) K)
    (hg : g ∈ cyclicInvariants K (cyclicOrder bb r).toNat (qq bb r σ)) (j : ℕ) (hj : j ≤ r)
    (d : Fin 2 →₀ ℕ) (hd : coeff d g ≠ 0) : ∃ e, chartExpMap bb r σ j (ι e) = ι d := by
  have hM := two_le_cyclicOrder r hbb hr
  have hm : ((cyclicOrder bb r).toNat : ℤ) = cyclicOrder bb r := Int.toNat_of_nonneg (by omega)
  have hdvd := (mem_cyclicInvariants_iff_dvd _ (by omega) _ g).mp hg d hd
  rw [hm, show (d 0 : ℤ) = ι d 0 from rfl, show (d 1 : ℤ) = ι d 1 from rfl,
    ← exists_boundaryMap_eq_iff (bb := bb) r σ] at hdvd
  obtain ⟨w, hw⟩ := hdvd
  have hn := (boundaryMap_nonneg_iff bb r σ w).mp (hw ▸ ι_nonneg d)
  have h0 := s_nonneg hbb r w hn.1 hn.2 j (by omega)
  have h1 := s_nonneg hbb r w hn.1 hn.2 (j + 1) (by omega)
  refine ⟨toFin (tau bb j w), ?_⟩
  rw [ι_toFin h0 h1, chartExpMap_apply, tauInv_tau, hw]

private lemma compat (g : MvPowerSeries (Fin 2) K) (i : ℕ) (hi : i < r) (a c : ℤ) :
    czF (pull (chartExpMap bb r σ i) g) a c =
      czF (pull (chartExpMap bb r σ (i + 1)) g) c (bb i * c - a) := by
  rw [czF_pull, czF_pull]
  have hΦ : chartExpMap bb r σ (i + 1) ![c, bb i * c - a] = chartExpMap bb r σ i ![a, c] := by
    rw [chartExpMap_apply, chartExpMap_apply]
    change boundaryMap bb r σ (tauInv bb i (stepInv (bb i) _)) = _
    congr 2
    ext k; fin_cases k <;> simp [stepInv]
  rw [hΦ, chartExpMap_apply]
  set w := tauInv bb i ![a, c]
  by_cases hV : czV g (boundaryMap bb r σ w) = 0
  · simp [hV]
  have ht : tau bb i w = ![a, c] := tau_tauInv bb i _
  have ha : a = s bb i w := by rw [s, ht]; rfl
  have hc : c = s bb (i + 1) w := by rw [s, tau_succ_zero, ht]; rfl
  have hbc : bb i * c - a = s bb (i + 2) w := by rw [s_succ_succ, ← hc, ← ha]
  have hs := support_of_czV r σ hbb g w hV
  rw [if_pos ⟨by rw [ha]; exact hs i (by omega), by rw [hc]; exact hs (i + 1) (by omega)⟩,
    if_pos ⟨by rw [hc]; exact hs (i + 1) (by omega), by rw [hbc]; exact hs (i + 2) (by omega)⟩]

private lemma finite_support (hr : 1 ≤ r) (g : MvPowerSeries (Fin 2) K) (j : ℕ) (hj : j ≤ r)
    (n : ℕ) :
    {e : Fin 2 →₀ ℕ | coeff e (pull (chartExpMap bb r σ j) g) ≠ 0 ∧
      (if j = 0 then e 1 else if j = r then e 0 else min (e 0) (e 1)) < n}.Finite := by
  have hM := two_le_cyclicOrder r hbb hr
  refine ((Set.finite_Icc (0 : Fin 2 → ℤ) (fun _ => cyclicOrder bb r * n)).preimage
    ((chartExpMap_injective r σ hbb hr j).comp ι_injective).injOn).subset ?_
  rintro e ⟨hne, hord⟩
  rw [coeff_pull, chartExpMap_apply] at hne
  set w := tauInv bb j (ι e)
  have hn := (boundaryMap_nonneg_iff bb r σ w).mp (nonneg_of_czV_ne_zero hne)
  have ht : tau bb j w = ι e := tau_tauInv bb j _
  have he0 : s bb j w = e 0 := by rw [s, ht]; rfl
  have he1 : s bb (j + 1) w = e 1 := by rw [s, tau_succ_zero, ht]; rfl
  obtain ⟨k, hk1, hkr, hkn⟩ : ∃ k, 1 ≤ k ∧ k ≤ r ∧ s bb k w < n := by
    split_ifs at hord with h0 hr'
    · exact ⟨1, le_rfl, hr, by rw [h0] at he1; rw [he1]; exact_mod_cast hord⟩
    · exact ⟨r, hr, le_rfl, by rw [hr'] at he0; rw [he0]; exact_mod_cast hord⟩
    · rcases min_lt_iff.mp hord with h | h
      · exact ⟨j, by omega, hj, by rw [he0]; exact_mod_cast h⟩
      · exact ⟨j + 1, by omega, by omega, by rw [he1]; exact_mod_cast h⟩
  have hb := boundary_le r hbb hr w hn.1 hn.2 k hk1 hkr
  have h0w : s bb 0 w = w 0 := rfl
  simp only [Set.mem_preimage, Function.comp_apply, Set.mem_Icc]
  rw [chartExpMap_apply]
  constructor <;> intro i <;>
    rcases boundaryMap_apply_zero_one bb r σ w with ⟨-, h0, h1⟩ | ⟨-, h0, h1⟩ <;>
    rcases fin_two_cases i with rfl | rfl <;> simp only [h0, h1, Pi.zero_apply] <;> nlinarith

omit hbb in
private lemma dvd_X_iff (Ψ : (Fin 2 → ℤ) →+ (Fin 2 → ℤ)) (g : MvPowerSeries (Fin 2) K)
    (hg : ∀ d, coeff d g ≠ 0 → ∃ e, Ψ (ι e) = ι d) (i₀ i₁ : Fin 2)
    (hrel : ∀ e, Ψ (ι e) i₁ = e i₀) : X i₀ ∣ pull Ψ g ↔ X i₁ ∣ g := by
  rw [X_dvd_iff, X_dvd_iff]
  constructor
  · intro H d hd
    by_contra hne
    obtain ⟨e, he⟩ := hg d hne
    have := H e (by have := hrel e; rw [he, ι_apply, hd] at this; omega)
    rw [coeff_pull, he, czV_ι] at this
    exact hne this
  · intro H e he
    rw [coeff_pull]
    by_contra hne
    have hn := nonneg_of_czV_ne_zero hne
    rw [czV_eq, if_pos hn] at hne
    apply hne (H _ _)
    rw [toFin_apply, hrel e, he]; rfl

end Charts

/-- The ring map from the invariant ring to the families of chart functions. -/
private def psi {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {r : ℕ} (hr : 1 ≤ r)
    (b : Fin r → ℕ) (hb : ∀ i, 2 ≤ b i) (σ : Equiv.Perm (Fin 2)) :
    cyclicInvariants K (cyclicOrder (bbOf b) r).toNat (qq (bbOf b) r σ) →+*
      (Fin (r + 1) → MvPowerSeries (Fin 2) K) where
  toFun g j := pull (chartExpMap (bbOf b) r σ j) (g : MvPowerSeries (Fin 2) K)
  map_one' := by
    funext j
    change pull _ (1 : MvPowerSeries (Fin 2) K) = 1
    rw [← map_one (C (σ := Fin 2) (R := K)),
      pull_C _ (chartExpMap_injective r σ (bbOf_ge b hb) hr j)]
  map_mul' g h := funext fun j => pull_mul _ (chartExpMap_injective r σ (bbOf_ge b hb) hr j) _ _
    (exists_chartExpMap_eq r σ (bbOf_ge b hb) hr _ g.2 j (by omega))
    (exists_chartExpMap_eq r σ (bbOf_ge b hb) hr _ h.2 j (by omega))
  map_zero' := by
    funext j; ext e
    change czV (0 : MvPowerSeries (Fin 2) K) _ = 0
    simp [czV_eq]
  map_add' g h := funext fun j => pull_add _ _ _

/-- A chart family determines the invariant: chart `0` already sees every monomial. -/
private lemma psi_injective
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {r : ℕ} (hr : 1 ≤ r)
    (b : Fin r → ℕ) (hb : ∀ i, 2 ≤ b i) (σ : Equiv.Perm (Fin 2)) :
    Function.Injective (psi (K := K) hr b hb σ) := by
  set bb := bbOf b
  have hbb : ∀ i, 2 ≤ bb i := bbOf_ge b hb
  refine (injective_iff_map_eq_zero _).mpr fun g hg => Subtype.ext ?_
  ext d
  by_contra hd
  obtain ⟨e, he⟩ := exists_chartExpMap_eq r σ hbb hr _ g.2 0 (Nat.zero_le _) d hd
  have := congrArg (coeff e) (congrFun hg 0)
  rw [Pi.zero_apply, map_zero] at this
  change czV (g : MvPowerSeries (Fin 2) K) (chartExpMap bb r σ 0 (ι e)) = 0 at this
  rw [he, czV_ι] at this
  exact hd this

/-- Along the chain, the coefficients of a compatible family are those of chart `0`. -/
private lemma czV_tau_eq {K : Type*} [Field K] {r : ℕ} (b : Fin r → ℕ)
    (f : Fin (r + 1) → MvPowerSeries (Fin 2) K)
    (hcomp : ∀ (i : Fin r) (a c : ℤ),
      czF (f i.castSucc) a c = czF (f i.succ) c ((b i : ℤ) * c - a))
    (j : ℕ) (hj : j < r + 1) (w : Fin 2 → ℤ) :
    czV (f ⟨j, hj⟩) (tau (bbOf b) j w) = czV (f 0) w := by
  induction j generalizing w with
  | zero => rfl
  | succ j ih =>
    rw [← ih (by omega) w]
    change czF (f ⟨j + 1, hj⟩) (tau (bbOf b) j w 1)
        (bbOf b j * tau (bbOf b) j w 1 - tau (bbOf b) j w 0) =
      czF (f ⟨j, by omega⟩) (tau (bbOf b) j w 0) (tau (bbOf b) j w 1)
    rw [show bbOf b j = b ⟨j, by omega⟩ from bbOf_val b ⟨j, by omega⟩]
    exact (hcomp ⟨j, by omega⟩ _ _).symm

/-- **Gluing.** A family of chart series satisfying the transition rule on coefficients is the
family of pull-backs of a single invariant series. -/
private lemma exists_psi_eq
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {r : ℕ} (hr : 1 ≤ r)
    (b : Fin r → ℕ) (hb : ∀ i, 2 ≤ b i) (σ : Equiv.Perm (Fin 2))
    (f : Fin (r + 1) → MvPowerSeries (Fin 2) K)
    (hcomp : ∀ (i : Fin r) (a c : ℤ),
      czF (f i.castSucc) a c = czF (f i.succ) c ((b i : ℤ) * c - a)) :
    ∃ g, psi hr b hb σ g = f := by
  classical
  set bb := bbOf b
  have hbb : ∀ i, 2 ≤ bb i := bbOf_ge b hb
  have hM := two_le_cyclicOrder r hbb hr
  have hm : ((cyclicOrder bb r).toNat : ℤ) = cyclicOrder bb r := Int.toNat_of_nonneg (by omega)
  let g : MvPowerSeries (Fin 2) K := fun d =>
    if h : ∃ w, boundaryMap bb r σ w = ι d then czV (f 0) h.choose else 0
  have hg : g ∈ cyclicInvariants K (cyclicOrder bb r).toNat (qq bb r σ) := by
    rw [mem_cyclicInvariants_iff_dvd _ (by omega)]
    intro d hd
    change (if h : ∃ w, boundaryMap bb r σ w = ι d then czV (f 0) h.choose else 0) ≠ 0 at hd
    split_ifs at hd with h
    · rw [hm]
      exact (exists_boundaryMap_eq_iff (bb := bb) r σ (ι d)).mp h
    · exact absurd rfl hd
  refine ⟨⟨g, hg⟩, ?_⟩
  funext j
  ext e
  change czV g (boundaryMap bb r σ (tauInv bb j (ι e))) = _
  set w := tauInv bb j (ι e)
  have ht : tau bb j w = ι e := tau_tauInv bb j _
  have hfj : coeff e (f j) = czV (f 0) w := by
    rw [← czV_ι, ← ht]; exact czV_tau_eq b f hcomp j j.2 w
  rw [hfj]
  by_cases hD : 0 ≤ boundaryMap bb r σ w 0 ∧ 0 ≤ boundaryMap bb r σ w 1
  · rw [czV_eq, if_pos hD]
    have hex : ∃ w', boundaryMap bb r σ w' = ι (toFin (boundaryMap bb r σ w)) :=
      ⟨w, (ι_toFin hD.1 hD.2).symm⟩
    change (if h : ∃ w', boundaryMap bb r σ w' = ι (toFin (boundaryMap bb r σ w)) then
      czV (f 0) h.choose else 0) = _
    rw [dif_pos hex]
    have h2 : boundaryMap bb r σ hex.choose = boundaryMap bb r σ w :=
      hex.choose_spec.trans (ι_toFin hD.1 hD.2)
    rw [boundaryMap_injective r σ hbb hr h2]
  · rw [czV_eq, if_neg hD]
    by_contra hF
    apply hD
    rw [boundaryMap_nonneg_iff]
    refine ⟨(nonneg_of_czV_ne_zero (Ne.symm hF)).1, ?_⟩
    rw [← czV_tau_eq b f hcomp r (by omega) w] at hF
    exact (nonneg_of_czV_ne_zero (Ne.symm hF)).2

/-- The first end marking: chart `0` vanishes on `x = 0` exactly when the invariant vanishes on
`X (σ 0) = 0`. -/
private lemma psi_zero_mem_span_iff
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {r : ℕ} (hr : 1 ≤ r)
    (b : Fin r → ℕ) (hb : ∀ i, 2 ≤ b i) (σ : Equiv.Perm (Fin 2))
    (g : cyclicInvariants K (cyclicOrder (bbOf b) r).toNat (qq (bbOf b) r σ)) :
    psi hr b hb σ g 0 ∈ Ideal.span {X 0} ↔
      (g : MvPowerSeries (Fin 2) K) ∈ Ideal.span {X (σ 0)} := by
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  refine dvd_X_iff _ _
    (exists_chartExpMap_eq r σ (bbOf_ge b hb) hr _ g.2 0 (Nat.zero_le _)) 0 (σ 0) fun e => ?_
  rw [chartExpMap_apply, boundaryMap_apply_σ_zero]; rfl

/-- The second end marking: chart `r` vanishes on `y = 0` exactly when the invariant vanishes
on `X (σ 1) = 0`. -/
private lemma psi_last_mem_span_iff
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {r : ℕ} (hr : 1 ≤ r)
    (b : Fin r → ℕ) (hb : ∀ i, 2 ≤ b i) (σ : Equiv.Perm (Fin 2))
    (g : cyclicInvariants K (cyclicOrder (bbOf b) r).toNat (qq (bbOf b) r σ)) :
    psi hr b hb σ g (Fin.last r) ∈ Ideal.span {X 1} ↔
      (g : MvPowerSeries (Fin 2) K) ∈ Ideal.span {X (σ 1)} := by
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  refine dvd_X_iff _ _
    (exists_chartExpMap_eq r σ (bbOf_ge b hb) hr _ g.2 r le_rfl) 1 (σ 1) fun e => ?_
  rw [chartExpMap_apply, boundaryMap_apply_σ_one, s, tau_succ_zero, tau_tauInv]; rfl

end

end ChainPlumbing

open ChainPlumbing in
/-- **The formal chain plumbing is a cyclic quotient.** Let `K` be algebraically closed of
characteristic zero, `r ≥ 1`, and `b₀, …, b_{r-1} ≥ 2`. Let `S` be the ring of global functions
on the completed formal plumbing: families `f : Fin (r + 1) → K[[x, y]]` with each `f j` in the
completion of `K[x, y]` along the exceptional ideal of chart `j` (`(y)`, `(x y)` or `(x)`,
measured by `ord j`), and with the coefficients of `f i` and `f (i + 1)` agreeing under
`x_i^a y_i^c = x_{i+1}^c y_{i+1}^{b_i c - a}`. Then for each assignment `σ` of the two end
markings `x_0 = 0` and `y_r = 0` to the two axes there are `m ≥ 2`, `q` coprime to `m` and an
injective ring map `ψ : MMP.Flips.cyclicInvariants K m q → ∏_j K[[x, y]]` with image `S`, sending
constants to constants, under which the first end-marking ideal is the invariants in `(X (σ 0))`,
the second is the invariants in `(X (σ 1))`, and the union-marking ideal is the invariants in
their intersection. -/
@[mmp "lem_mmp_foundation_chain_plumbing_cyclic_invariant_ring"]
public theorem exists_ringHom_cyclicInvariants_chainPlumbing
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] {r : ℕ} (hr : 1 ≤ r)
    (b : Fin r → ℕ) (hb : ∀ i, 2 ≤ b i) :
    let coeffZ : MvPowerSeries (Fin 2) K → ℤ → ℤ → K := fun f a c =>
      if 0 ≤ a ∧ 0 ≤ c then coeff (Finsupp.single 0 a.toNat + Finsupp.single 1 c.toNat) f
      else 0
    let ord : Fin (r + 1) → (Fin 2 →₀ ℕ) → ℕ := fun j e =>
      if (j : ℕ) = 0 then e 1 else if (j : ℕ) = r then e 0 else min (e 0) (e 1)
    let S : Set (Fin (r + 1) → MvPowerSeries (Fin 2) K) :=
      {f | (∀ j n, {e : Fin 2 →₀ ℕ | coeff e (f j) ≠ 0 ∧ ord j e < n}.Finite) ∧
        ∀ (i : Fin r) (a c : ℤ),
          coeffZ (f i.castSucc) a c = coeffZ (f i.succ) c ((b i : ℤ) * c - a)}
    ∀ σ : Equiv.Perm (Fin 2), ∃ m : ℕ, 2 ≤ m ∧ ∃ q : ℤ, Int.gcd q m = 1 ∧
      ∃ ψ : cyclicInvariants K m q →+* (Fin (r + 1) → MvPowerSeries (Fin 2) K),
        Function.Injective ψ ∧ Set.range ψ = S ∧
        (∀ (k : K) (g : cyclicInvariants K m q), (g : MvPowerSeries (Fin 2) K) = C k →
          ψ g = fun _ => C k) ∧
        (∀ g : cyclicInvariants K m q, ψ g 0 ∈ Ideal.span {X 0} ↔
          (g : MvPowerSeries (Fin 2) K) ∈ Ideal.span {X (σ 0)}) ∧
        (∀ g : cyclicInvariants K m q, ψ g (Fin.last r) ∈ Ideal.span {X 1} ↔
          (g : MvPowerSeries (Fin 2) K) ∈ Ideal.span {X (σ 1)}) ∧
        (∀ g : cyclicInvariants K m q,
          (ψ g 0 ∈ Ideal.span {X 0} ∧ ψ g (Fin.last r) ∈ Ideal.span {X 1}) ↔
            (g : MvPowerSeries (Fin 2) K) ∈ Ideal.span {X (σ 0)} ⊓ Ideal.span {X (σ 1)}) := by
  intro coeffZ ord S σ
  set bb := bbOf b
  have hbb : ∀ i, 2 ≤ bb i := bbOf_ge b hb
  have hM := two_le_cyclicOrder r hbb hr
  refine ⟨(cyclicOrder bb r).toNat, by omega, qq bb r σ, ?_, psi hr b hb σ,
    psi_injective hr b hb σ, ?_,
    fun k g hg => funext fun j => ?_, psi_zero_mem_span_iff hr b hb σ,
    psi_last_mem_span_iff hr b hb σ, fun g => (and_congr (psi_zero_mem_span_iff hr b hb σ g)
      (psi_last_mem_span_iff hr b hb σ g)).trans Submodule.mem_inf.symm⟩
  · rw [← Int.isCoprime_iff_gcd_eq_one, Int.toNat_of_nonneg (by omega)]
    exact isCoprime_qq (bb := bb) r σ
  · ext f
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨fun j n => finite_support r σ hbb hr _ j (by omega) n, fun i a c => ?_⟩
      have := compat r σ hbb (g : MvPowerSeries (Fin 2) K) i i.2 a c
      rwa [show bb i = b i from bbOf_val b i] at this
    · rintro ⟨-, hcomp⟩
      exact exists_psi_eq hr b hb σ f hcomp
  · change pull _ (g : MvPowerSeries (Fin 2) K) = _
    rw [hg, pull_C _ (chartExpMap_injective r σ hbb hr j)]

end MMP.Flips
