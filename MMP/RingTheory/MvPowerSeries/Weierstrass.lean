module

public import MMP.Attr
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import StacksFrontier.RingTheory.MvPowerSeries.RegularLocal

/-!
# The general Hensel lemma and the Weierstrass theorems (Kollár 1.87–1.93)

Kollár, *Lectures on resolution of singularities*, 1.87–1.93: factorizations of power series over
an arbitrary commutative ring lifting a coprime factorization of the constant term (the general
Hensel lemma), and its consequences over a field, the Weierstrass preparation and division
theorems.

## Main statements

* `MMP.Resolution.Kollar.exists_mul_eq_of_isCoprime`: (Thm. 1.92) if `F ∈ R[[x₁, …, xₙ]]` has
  constant term `gh` with `gR + hR = R`, then `F = GH` with `G(0) = g`, `H(0) = h`.
* `MMP.Resolution.Kollar.existsUnique_mul_eq_of_isCoprime`: (Thm. 1.92, "Moreover", corrected)
  if moreover `g` is a non-zero-divisor and `S` (Kollár's `𝓡*`) is a set of representatives of
  `R / gR`, the factorization with the non-constant coefficients of `G` in `S` is unique.
* `MMP.Resolution.Kollar.exists_weierstrass_preparation`: (Thm. 1.93) for
  `F ∈ K[[x₁, …, xₙ, y]]` with `F(0, …, 0, y)` of `y`-adic order `m`,
  `F = (yᵐ + g_{m-1}(𝐱) y^{m-1} + ⋯ + g₀(𝐱)) · u` with `u` a unit.
* `MMP.Resolution.Kollar.exists_weierstrass_preparation_two_variables`: (Cor. 1.88) the case of
  `K[[x, y]]`.
* `MMP.Resolution.Kollar.existsUnique_weierstrass_division`: the Weierstrass division theorem in
  `K[[x, y]]`.

## Implementation notes

The ring `K[[x₁, …, xₙ, y]]` is `PowerSeries (MvPowerSeries (Fin n) K)`, power series in the
variable `y` with coefficients in `K[[x₁, …, xₙ]]`; likewise `K[[x, y]]` is
`PowerSeries (PowerSeries K)` and `K[[x]][y]` is `Polynomial (PowerSeries K)`. Under these
identifications `F(0, …, 0, y)` is the image of `F` under the constant-coefficient map of the
coefficient ring, and `G(0)` for `G ∈ R[[x₁, …, xₙ]]` is `MvPowerSeries.constantCoeff G`.
The condition `gR + hR = R` is `IsCoprime g h`.
-/

@[expose] public section

namespace MMP.Resolution.Kollar

section Hensel

variable {R : Type*} [CommRing R] {n : ℕ}

section HenselAux

open MvPowerSeries

private theorem coeff_mul_eq_zero_of_degree_lt (P Q : MvPowerSeries (Fin n) R) (k : ℕ)
    (hP : ∀ β : Fin n →₀ ℕ, β.degree < k → coeff β P = 0) (α : Fin n →₀ ℕ)
    (hα : α.degree < k) : coeff α (P * Q) = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have : p.1.degree ≤ α.degree := by
    rw [← h, map_add]
    omega
  rw [hP _ (lt_of_le_of_lt this hα), zero_mul]

private theorem coeff_mul_eq_of_degree_eq (P Q : MvPowerSeries (Fin n) R) (k : ℕ)
    (hP : ∀ β : Fin n →₀ ℕ, β.degree < k → coeff β P = 0) (α : Fin n →₀ ℕ)
    (hα : α.degree = k) : coeff α (P * Q) = coeff α P * constantCoeff Q := by
  rw [coeff_mul, Finset.sum_eq_single (α, 0)]
  · simp
  · intro p hp hne
    have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    have h2 : p.2 ≠ 0 := by
      rintro h0
      rw [h0, add_zero] at h
      exact hne (Prod.ext h h0)
    have h3 : 0 < p.2.degree := Nat.pos_of_ne_zero (mt (Finsupp.degree_eq_zero_iff _).1 h2)
    have hlt : p.1.degree < k := by
      rw [← hα, ← h, map_add]
      omega
    rw [hP _ hlt, zero_mul]
  · simp

/-- The degree-`d + 1` part of a family of coefficients. -/
private noncomputable def henselDelta (f : (Fin n →₀ ℕ) → R) (d : ℕ) : MvPowerSeries (Fin n) R :=
  fun α => if α.degree = d + 1 then f α else 0

private theorem coeff_henselDelta (f : (Fin n →₀ ℕ) → R) (d : ℕ) (α : Fin n →₀ ℕ) :
    coeff α (henselDelta f d) = if α.degree = d + 1 then f α else 0 := rfl

private theorem coeff_henselDelta_of_ne (f : (Fin n →₀ ℕ) → R) (d : ℕ) (α : Fin n →₀ ℕ)
    (h : α.degree ≠ d + 1) : coeff α (henselDelta f d) = 0 := by
  simp [coeff_henselDelta, h]

private theorem constantCoeff_henselDelta (f : (Fin n →₀ ℕ) → R) (d : ℕ) :
    constantCoeff (henselDelta f d) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_henselDelta_of_ne]
  simp

private noncomputable def henselStep (F : MvPowerSeries (Fin n) R) (c : R → R × R) (d : ℕ)
    (P : MvPowerSeries (Fin n) R × MvPowerSeries (Fin n) R) :
    MvPowerSeries (Fin n) R × MvPowerSeries (Fin n) R :=
  (P.1 + henselDelta (fun α => (c (coeff α F - coeff α (P.1 * P.2))).1) d,
   P.2 + henselDelta (fun α => (c (coeff α F - coeff α (P.1 * P.2))).2) d)

private noncomputable def henselSeq (F : MvPowerSeries (Fin n) R) (c : R → R × R) (g h : R) :
    ℕ → MvPowerSeries (Fin n) R × MvPowerSeries (Fin n) R
  | 0 => (C g, C h)
  | d + 1 => henselStep F c d (henselSeq F c g h d)

private theorem henselSeq_invariant (F : MvPowerSeries (Fin n) R) {g h : R}
    (hF : constantCoeff F = g * h) (c : R → R × R)
    (hc : ∀ Φ, g * (c Φ).2 + h * (c Φ).1 = Φ) (d : ℕ) :
    constantCoeff (henselSeq F c g h d).1 = g ∧ constantCoeff (henselSeq F c g h d).2 = h ∧
    (∀ α : Fin n →₀ ℕ, α.degree ≤ d →
      coeff α ((henselSeq F c g h d).1 * (henselSeq F c g h d).2) = coeff α F) ∧
    (∀ α : Fin n →₀ ℕ, α ≠ 0 → α.degree ≤ d → ∃ Φ, coeff α (henselSeq F c g h d).1 = (c Φ).1) ∧
    (∀ α : Fin n →₀ ℕ, d < α.degree →
      coeff α (henselSeq F c g h d).1 = 0 ∧ coeff α (henselSeq F c g h d).2 = 0) := by
  induction d with
  | zero =>
    refine ⟨by simp [henselSeq], by simp [henselSeq], ?_, ?_, ?_⟩
    · intro α hα
      obtain rfl : α = 0 := (Finsupp.degree_eq_zero_iff _).1 (Nat.le_zero.1 hα)
      simp [henselSeq, ← map_mul, hF]
    · intro α hα hd
      exact absurd ((Finsupp.degree_eq_zero_iff _).1 (Nat.le_zero.1 hd)) hα
    · intro α hα
      have : α ≠ 0 := by
        rintro rfl
        simp at hα
      simp [henselSeq, coeff_C, this]
  | succ d ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    set P := henselSeq F c g h d
    rw [show henselSeq F c g h (d + 1) = henselStep F c d P from rfl]
    simp only [henselStep]
    set ΔG := henselDelta (fun α => (c (coeff α F - coeff α (P.1 * P.2))).1) d with hΔG
    set ΔH := henselDelta (fun α => (c (coeff α F - coeff α (P.1 * P.2))).2) d with hΔH
    have hG0 : ∀ β : Fin n →₀ ℕ, β.degree < d + 1 → coeff β ΔG = 0 := fun β hβ =>
      coeff_henselDelta_of_ne _ _ _ (by omega)
    have hH0 : ∀ β : Fin n →₀ ℕ, β.degree < d + 1 → coeff β ΔH = 0 := fun β hβ =>
      coeff_henselDelta_of_ne _ _ _ (by omega)
    have hcG : constantCoeff ΔG = 0 := constantCoeff_henselDelta _ _
    have hcH : constantCoeff ΔH = 0 := constantCoeff_henselDelta _ _
    refine ⟨by simp [h1, hcG], by simp [h2, hcH], ?_, ?_, ?_⟩
    · intro α hα
      rw [show (P.1 + ΔG) * (P.2 + ΔH) = P.1 * P.2 + ΔG * (P.2 + ΔH) + ΔH * P.1 by ring,
        map_add, map_add]
      rcases Nat.lt_or_eq_of_le hα with hlt | heq
      · rw [coeff_mul_eq_zero_of_degree_lt ΔG _ (d + 1) hG0 α hlt,
          coeff_mul_eq_zero_of_degree_lt ΔH _ (d + 1) hH0 α hlt, add_zero, add_zero]
        exact h3 α (by omega)
      · rw [coeff_mul_eq_of_degree_eq ΔG _ (d + 1) hG0 α heq,
          coeff_mul_eq_of_degree_eq ΔH _ (d + 1) hH0 α heq]
        have e1 : coeff α ΔG = (c (coeff α F - coeff α (P.1 * P.2))).1 := by
          simp [hΔG, coeff_henselDelta, heq]
        have e2 : coeff α ΔH = (c (coeff α F - coeff α (P.1 * P.2))).2 := by
          simp [hΔH, coeff_henselDelta, heq]
        rw [e1, e2, map_add, h2, hcH, h1, add_zero]
        linear_combination hc (coeff α F - coeff α (P.1 * P.2))
    · intro α hα hd
      rcases Nat.lt_or_eq_of_le hd with hlt | heq
      · rw [map_add, hG0 α hlt, add_zero]
        exact h4 α hα (by omega)
      · refine ⟨coeff α F - coeff α (P.1 * P.2), ?_⟩
        rw [map_add, (h5 α (by omega)).1, zero_add, hΔG, coeff_henselDelta]
        simp [heq]
    · intro α hα
      refine ⟨?_, ?_⟩
      · rw [map_add, (h5 α (by omega)).1, zero_add]
        exact coeff_henselDelta_of_ne _ _ _ (by omega)
      · rw [map_add, (h5 α (by omega)).2, zero_add]
        exact coeff_henselDelta_of_ne _ _ _ (by omega)

private theorem exists_mul_eq_of_choice (F : MvPowerSeries (Fin n) R) {g h : R}
    (hF : constantCoeff F = g * h) (c : R → R × R)
    (hc : ∀ Φ, g * (c Φ).2 + h * (c Φ).1 = Φ) :
    ∃ G H : MvPowerSeries (Fin n) R, F = G * H ∧ constantCoeff G = g ∧ constantCoeff H = h ∧
      ∀ α : Fin n →₀ ℕ, α ≠ 0 → ∃ Φ, coeff α G = (c Φ).1 := by
  set S := henselSeq F c g h
  have inv := henselSeq_invariant F hF c hc
  have step1 : ∀ (d : ℕ) (α : Fin n →₀ ℕ), α.degree ≤ d →
      coeff α (S (d + 1)).1 = coeff α (S d).1 ∧ coeff α (S (d + 1)).2 = coeff α (S d).2 := by
    intro d α hd
    rw [show S (d + 1) = henselStep F c d (S d) from rfl]
    simp only [henselStep, map_add]
    rw [coeff_henselDelta_of_ne _ _ _ (by omega), coeff_henselDelta_of_ne _ _ _ (by omega)]
    simp
  set G : MvPowerSeries (Fin n) R := fun α => coeff α (S α.degree).1
  set H : MvPowerSeries (Fin n) R := fun α => coeff α (S α.degree).2
  have hG : ∀ (d : ℕ) (α : Fin n →₀ ℕ), α.degree ≤ d →
      coeff α (S d).1 = coeff α G ∧ coeff α (S d).2 = coeff α H := by
    intro d α hd
    induction d, hd using Nat.le_induction with
    | base => exact ⟨rfl, rfl⟩
    | succ d hd ih => exact ⟨(step1 d α hd).1.trans ih.1, (step1 d α hd).2.trans ih.2⟩
  refine ⟨G, H, ?_, ?_, ?_, ?_⟩
  · ext α
    rw [coeff_mul]
    have key : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal α,
        coeff p.1 G * coeff p.2 H =
          coeff p.1 (S α.degree).1 * coeff p.2 (S α.degree).2 := by
      intro p hp
      have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      have d1 : p.1.degree ≤ α.degree := by
        rw [← h, map_add]
        omega
      have d2 : p.2.degree ≤ α.degree := by
        rw [← h, map_add]
        omega
      rw [← (hG _ _ d1).1, ← (hG _ _ d2).2]
    rw [Finset.sum_congr rfl key, ← coeff_mul]
    exact ((inv α.degree).2.2.1 α le_rfl).symm
  · rw [← coeff_zero_eq_constantCoeff_apply, ← (hG 0 0 (by simp)).1,
      coeff_zero_eq_constantCoeff_apply]
    exact (inv 0).1
  · rw [← coeff_zero_eq_constantCoeff_apply, ← (hG 0 0 (by simp)).2,
      coeff_zero_eq_constantCoeff_apply]
    exact (inv 0).2.1
  · intro α hα
    rw [← (hG α.degree α le_rfl).1]
    exact (inv α.degree).2.2.2.1 α hα le_rfl

private theorem eq_of_mul_eq_of_coeff_mem {g h : R} (hgh : IsCoprime g h)
    (hg : g ∈ nonZeroDivisors R) (S : Set R)
    (hS : ∀ c : R ⧸ Ideal.span {g}, ∃! s : R, s ∈ S ∧ Ideal.Quotient.mk _ s = c)
    {F G H G' H' : MvPowerSeries (Fin n) R}
    (e1 : F = G * H) (e2 : F = G' * H')
    (c1 : constantCoeff G = g) (c2 : constantCoeff H = h)
    (c3 : constantCoeff G' = g) (c4 : constantCoeff H' = h)
    (s1 : ∀ α : Fin n →₀ ℕ, α ≠ 0 → coeff α G ∈ S)
    (s2 : ∀ α : Fin n →₀ ℕ, α ≠ 0 → coeff α G' ∈ S) : G = G' ∧ H = H' := by
  obtain ⟨a, b, hab⟩ := hgh
  have claim : ∀ k : ℕ, ∀ α : Fin n →₀ ℕ, α.degree = k →
      coeff α (G - G') = 0 ∧ coeff α (H - H') = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro α hα
      by_cases h0 : α = 0
      · subst h0
        simp only [coeff_zero_eq_constantCoeff_apply, map_sub, c1, c2, c3, c4, sub_self, and_self]
      · have v1 : ∀ β : Fin n →₀ ℕ, β.degree < k → coeff β (G - G') = 0 :=
          fun β hβ => (ih _ hβ β rfl).1
        have v2 : ∀ β : Fin n →₀ ℕ, β.degree < k → coeff β (H - H') = 0 :=
          fun β hβ => (ih _ hβ β rfl).2
        have hexp : (G - G') * H + (H - H') * G' = 0 := by
          linear_combination e1.symm.trans e2
        have E := congrArg (coeff α) hexp
        rw [map_add, coeff_mul_eq_of_degree_eq _ _ k v1 α hα,
          coeff_mul_eq_of_degree_eq _ _ k v2 α hα, c2, c3, map_zero] at E
        have hmem : coeff α G - coeff α G' ∈ Ideal.span {g} := by
          rw [Ideal.mem_span_singleton']
          refine ⟨a * coeff α (G - G') - b * coeff α (H - H'), ?_⟩
          rw [map_sub] at E ⊢
          linear_combination (coeff α G - coeff α G') * hab - b * E
        have heq : coeff α G = coeff α G' :=
          (hS (Ideal.Quotient.mk _ (coeff α G))).unique ⟨s1 α h0, rfl⟩
            ⟨s2 α h0, (Ideal.Quotient.eq.2 hmem).symm⟩
        have h1 : coeff α (G - G') = 0 := by rw [map_sub, heq, sub_self]
        refine ⟨h1, ?_⟩
        rw [h1, zero_mul, zero_add] at E
        exact (mem_nonZeroDivisors_iff.1 hg).2 _ E
  exact ⟨MvPowerSeries.ext fun α => sub_eq_zero.1 (claim _ α rfl).1,
    MvPowerSeries.ext fun α => sub_eq_zero.1 (claim _ α rfl).2⟩

end HenselAux

/-- **Kollár, Theorem 1.92** (general Hensel lemma). Let `R` be a ring and
`F = ∑ r_α x^α ∈ R[[x₁, …, xₙ]]` with `r₀ = gh` for `g, h ∈ R` with `gR + hR = R`. Then there
are `G, H ∈ R[[x₁, …, xₙ]]` with `F = GH`, `G(0) = g` and `H(0) = h`. -/
@[mmp "thm_kr1d_general_hensel_existence"]
theorem exists_mul_eq_of_isCoprime (F : MvPowerSeries (Fin n) R) {g h : R}
    (hF : MvPowerSeries.constantCoeff F = g * h) (hgh : IsCoprime g h) :
    ∃ G H : MvPowerSeries (Fin n) R, F = G * H ∧
      MvPowerSeries.constantCoeff G = g ∧ MvPowerSeries.constantCoeff H = h := by
  obtain ⟨a, b, hab⟩ := hgh
  obtain ⟨G, H, h1, h2, h3, -⟩ := exists_mul_eq_of_choice F hF (fun Φ => (b * Φ, a * Φ))
    (fun Φ => by linear_combination Φ * hab)
  exact ⟨G, H, h1, h2, h3⟩

/-- **Kollár, Theorem 1.92, "Moreover"** (corrected: `g` must be a non-zero-divisor). In the
setting of `exists_mul_eq_of_isCoprime`, assume moreover that `g` is a non-zero-divisor of `R`,
and let `S ⊆ R` (Kollár's `𝓡*`) contain exactly one element of each residue class of `R / gR`.
Then there is exactly one pair `(G, H)` with `F = GH`, `G(0) = g`, `H(0) = h` and all
coefficients of `G` at the monomials `x^α`, `α ≠ 0`, in `S`. -/
@[mmp "thm_kr1d_general_hensel_uniqueness"]
theorem existsUnique_mul_eq_of_isCoprime (F : MvPowerSeries (Fin n) R) {g h : R}
    (hF : MvPowerSeries.constantCoeff F = g * h) (hgh : IsCoprime g h)
    (hg : g ∈ nonZeroDivisors R) (S : Set R)
    (hS : ∀ c : R ⧸ Ideal.span {g}, ∃! s : R, s ∈ S ∧ Ideal.Quotient.mk _ s = c) :
    ∃! GH : MvPowerSeries (Fin n) R × MvPowerSeries (Fin n) R, F = GH.1 * GH.2 ∧
      MvPowerSeries.constantCoeff GH.1 = g ∧ MvPowerSeries.constantCoeff GH.2 = h ∧
      ∀ α : Fin n →₀ ℕ, α ≠ 0 → MvPowerSeries.coeff α GH.1 ∈ S := by
  obtain ⟨a, b, hab⟩ := hgh
  have key : ∀ Φ : R, ∃ p : R × R, p.1 ∈ S ∧ g * p.2 + h * p.1 = Φ := by
    intro Φ
    obtain ⟨s, ⟨hsS, hs⟩, -⟩ := hS (Ideal.Quotient.mk _ (b * Φ))
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hs)
    exact ⟨(s, a * Φ - h * t), hsS, by linear_combination Φ * hab - h * ht⟩
  choose c hc1 hc2 using key
  obtain ⟨G, H, h1, h2, h3, h4⟩ := exists_mul_eq_of_choice F hF c hc2
  have hGS : ∀ α : Fin n →₀ ℕ, α ≠ 0 → MvPowerSeries.coeff α G ∈ S :=
    fun α hα => (h4 α hα).elim fun Φ hΦ => hΦ ▸ hc1 Φ
  refine ⟨(G, H), ⟨h1, h2, h3, hGS⟩, ?_⟩
  rintro ⟨G', H'⟩ ⟨e, c1, c2, hs⟩
  obtain ⟨rfl, rfl⟩ := eq_of_mul_eq_of_coeff_mem ⟨a, b, hab⟩ hg S hS h1 e h2 h3 c1 c2 hGS hs
  rfl

end Hensel

section Weierstrass

variable {K : Type*} [Field K]

section WeierstrassAux

open IsLocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A]

private theorem order_map_residue_eq (φ : A →+* K) (hφ : RingHom.ker φ = maximalIdeal A)
    (F : PowerSeries A) :
    (PowerSeries.map (residue A) F).order = (PowerSeries.map φ F).order := by
  let ψ : ResidueField A →+* K :=
    Ideal.Quotient.lift (maximalIdeal A) φ (fun a ha => by rwa [← hφ] at ha)
  have e : ∀ i, PowerSeries.coeff i (PowerSeries.map φ F) =
      ψ (PowerSeries.coeff i (PowerSeries.map (residue A) F)) := fun _ => rfl
  have hG := PowerSeries.order_eq.1 (rfl : (PowerSeries.map (residue A) F).order = _)
  refine (PowerSeries.order_eq.2 ⟨fun i hi => ?_, fun i hi => ?_⟩).symm <;>
    simp only [e, ne_eq, map_eq_zero_iff ψ ψ.injective]
  exacts [hG.1 i hi, hG.2 i hi]

private theorem exists_weierstrass_preparation_of_ker_eq [IsAdicComplete (maximalIdeal A) A]
    (φ : A →+* K) (hφ : RingHom.ker φ = maximalIdeal A) (F : PowerSeries A) {m : ℕ}
    (hF : (PowerSeries.map φ F).order = m) :
    ∃ (g : Fin m → A) (u : (PowerSeries A)ˣ),
      F = (PowerSeries.X ^ m + ∑ i : Fin m, PowerSeries.C (g i) * PowerSeries.X ^ (i : ℕ)) *
        (u : PowerSeries A) := by
  have hord : (PowerSeries.map (residue A) F).order = m := by
    rw [order_map_residue_eq φ hφ, hF]
  have hne : PowerSeries.map (residue A) F ≠ 0 := fun h => by
    simp [h] at hord
  obtain ⟨f, h, H⟩ := PowerSeries.exists_isWeierstrassFactorization hne
  have hdeg : f.natDegree = m := by
    rw [H.natDegree_eq_toNat_order_map, hord]
    rfl
  have hmon : f.Monic := H.isDistinguishedAt.monic
  refine ⟨fun i => f.coeff i, H.isUnit.unit, ?_⟩
  have hsum := hmon.as_sum
  rw [hdeg] at hsum
  have hcast : (f : PowerSeries A) = PowerSeries.X ^ m +
      ∑ i : Fin m, PowerSeries.C (f.coeff i) * PowerSeries.X ^ (i : ℕ) := by
    conv_lhs => rw [hsum]
    rw [Fin.sum_univ_eq_sum_range (fun i => PowerSeries.C (f.coeff i) * PowerSeries.X ^ i) m,
      Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X]
    congr 1
    refine (map_sum (Polynomial.coeToPowerSeries.ringHom (R := A))
      (fun i => Polynomial.C (f.coeff i) * Polynomial.X ^ i) (Finset.range m)).trans
      (Finset.sum_congr rfl fun i _ => ?_)
    simp
  exact H.eq_mul.trans (by rw [hcast]; rfl)

end WeierstrassAux

/-- **Kollár, Theorem 1.93** (Weierstrass preparation theorem). Let `K` be a field and
`F ∈ K[[x₁, …, xₙ, y]]` such that `F(0, …, 0, y) ≠ 0` has `y`-adic order `m`. Then there are
`g₀, …, g_{m-1} ∈ K[[𝐱]]` and a unit `u` of `K[[𝐱, y]]` with
`F = (yᵐ + g_{m-1}(𝐱) y^{m-1} + ⋯ + g₀(𝐱)) · u`. -/
@[mmp "thm_kr1d_weierstrass_preparation"]
theorem exists_weierstrass_preparation {n m : ℕ} (F : PowerSeries (MvPowerSeries (Fin n) K))
    (hF : (PowerSeries.map MvPowerSeries.constantCoeff F).order = m) :
    ∃ (g : Fin m → MvPowerSeries (Fin n) K) (u : (PowerSeries (MvPowerSeries (Fin n) K))ˣ),
      F = (PowerSeries.X ^ m + ∑ i : Fin m, PowerSeries.C (g i) * PowerSeries.X ^ (i : ℕ)) *
        (u : PowerSeries _) := by
  have hφ : RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n) K →+* K) =
      IsLocalRing.maximalIdeal _ := by
    rw [maximalIdeal_mvPowerSeries_eq_span_X, MvPowerSeries.span_X_eq_ker_constantCoeff]
  have : IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) K))
      (MvPowerSeries (Fin n) K) := by
    rw [maximalIdeal_mvPowerSeries_eq_span_X]
    infer_instance
  exact exists_weierstrass_preparation_of_ker_eq _ hφ F hF

/-- **Kollár, Corollary 1.88** (Weierstrass preparation theorem in two variables). Let `K` be a
field and `F ∈ K[[x, y]]` such that `F(0, y) ≠ 0` has `y`-adic order `n`. Then there are
`g₀, …, g_{n-1} ∈ K[[x]]` and a unit `u` of `K[[x, y]]` with
`F = (yⁿ + g_{n-1}(x) y^{n-1} + ⋯ + g₀(x)) · u`. -/
@[mmp "prop_kr1d_weierstrass_preparation_two_variables"]
theorem exists_weierstrass_preparation_two_variables {n : ℕ} (F : PowerSeries (PowerSeries K))
    (hF : (PowerSeries.map PowerSeries.constantCoeff F).order = n) :
    ∃ (g : Fin n → PowerSeries K) (u : (PowerSeries (PowerSeries K))ˣ),
      F = (PowerSeries.X ^ n + ∑ i : Fin n, PowerSeries.C (g i) * PowerSeries.X ^ (i : ℕ)) *
        (u : PowerSeries _) := by
  have : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries K)) (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  exact exists_weierstrass_preparation_of_ker_eq _ PowerSeries.ker_coeff_eq_max_ideal F hF

/-- **Weierstrass division theorem** (used in Kollár 1.96). Let `K` be a field and
`F ∈ K[[x, y]]` such that `F(0, y) ≠ 0` has `y`-adic order `n`. Then for every `G ∈ K[[x, y]]`
there is exactly one pair `(Q, R)` with `Q ∈ K[[x, y]]`, `R ∈ K[[x]][y]` of `y`-degree `< n`
and `G = QF + R`. -/
@[mmp "thm_kr1d_weierstrass_division"]
theorem existsUnique_weierstrass_division {n : ℕ} (F : PowerSeries (PowerSeries K))
    (hF : (PowerSeries.map PowerSeries.constantCoeff F).order = n)
    (G : PowerSeries (PowerSeries K)) :
    ∃! QR : PowerSeries (PowerSeries K) × Polynomial (PowerSeries K),
      QR.2.degree < n ∧ G = QR.1 * F + (QR.2 : PowerSeries (PowerSeries K)) := by
  have hφ : RingHom.ker (PowerSeries.constantCoeff : PowerSeries K →+* K) =
      IsLocalRing.maximalIdeal _ := PowerSeries.ker_coeff_eq_max_ideal
  have : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries K)) (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  have hord : (PowerSeries.map (IsLocalRing.residue (PowerSeries K)) F).order = n := by
    rw [order_map_residue_eq _ hφ, hF]
  have hne : PowerSeries.map (IsLocalRing.residue (PowerSeries K)) F ≠ 0 := fun h => by
    simp [h] at hord
  have hn : (PowerSeries.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (PowerSeries K))) F
      ).order.toNat = n :=
    congrArg ENat.toNat hord
  refine ⟨(G /ʷ F, G %ʷ F), ⟨?_, ?_⟩, ?_⟩
  · have := (PowerSeries.isWeierstrassDivision_weierstrassDiv_weierstrassMod G hne).degree_lt
    rwa [hn] at this
  · simpa [mul_comm] using PowerSeries.eq_mul_weierstrassDiv_add_weierstrassMod G hne
  · rintro ⟨Q, R⟩ ⟨h1, h2⟩
    have H : G.IsWeierstrassDivision F Q R := ⟨by rwa [hn], by simpa [mul_comm] using h2⟩
    obtain ⟨e1, e2⟩ := H.unique hne
    simp [e1, e2]

end Weierstrass

end MMP.Resolution.Kollar
