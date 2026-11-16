module

public import MMP.AlgebraicGeometry.DeRham.FrobeniusLift
public import MMP.AlgebraicGeometry.DeRham.LogCartierGlobal

/-!
# The one-forms `F̃^* / p` of a Frobenius lift

Let `p` be a prime and `π : R → L` a surjective ring map with kernel `pR`, such that every
element of `R` killed by `p` lies in `pR` (`MMP.DeRham.IsReductionModP`); the main case is
`R` flat over `W₂(k)` and `L = R ⧸ pR`. Let `F` be a Frobenius lift on `R`
(`MMP.DeRham.IsFrobeniusLift`), so `F a = a ^ p + p c` for some `c`; the class
`δ(a) = π(c)` is well defined (`MMP.DeRham.frobeniusDefect`). It satisfies
`δ(ab) = a^p δ(b) + b^p δ(a)` and `δ(a + b) = δ(a) + δ(b) - Q(a, b)`, where
`Q = ((X + Y)^p - X^p - Y^p) / p`, and `δ(a + p c) = δ(a) + π(c)^p`.

For a ring `k` of characteristic `p` which is perfect and an `L`-algebra structure over `k`,
these identities say that `π a ↦ π(a)^{p-1} dπ(a) + dδ(a)` is a well-defined derivation of `L`
over `k` into the closed one-forms, with `L` acting through its Frobenius. It induces the
Frobenius-semilinear map

`φ_F : Ω¹_{L/k} → Ω¹_{L/k}`, `x dπ(a) ↦ x^p (π(a)^{p-1} dπ(a) + dδ(a))`

(`MMP.DeRham.frobeniusLiftForm`), "`F^*/p`" of Deligne–Illusie. Every `φ_F ω` is closed and
represents the inverse Cartier image of `ω` (`MMP.DeRham.isInvCartierRep_frobeniusLiftForm`). If
`F t = t ^ p` then `φ_F (dlog π t) = dlog π t`, and when the elements of a ring `B → L` have lifts
whose defect comes from `B`, `φ_F` preserves the logarithmic one-forms of `B` with poles along
such `π t` (`MMP.DeRham.frobeniusLiftForm_mem_closedLogForms`).

For two Frobenius lifts `F₁, F₂` the difference `h(π a) = δ₂(a) - δ₁(a)` is the class of
`(F₂ a - F₁ a) / p` when `p² = 0` in `R` (`MMP.DeRham.frobeniusDefect_sub_frobeniusDefect`) and
a derivation into `L` with the Frobenius action; it induces the Frobenius-semilinear map
`η₁₂ : Ω¹_{L/k} → Ω⁰_{L/k}`, `x dπ(a) ↦ x^p h(π a)` (`MMP.DeRham.frobeniusLiftHomotopy`), with

* `φ_{F₂} - φ_{F₁} = d ∘ η₁₂` (`MMP.DeRham.frobeniusLiftForm_sub_frobeniusLiftForm`),
* `η₁₂ + η₂₃ = η₁₃` and `η₁₁ = 0`,
* `η₁₂ (dlog π t) = 0` when `F₁ t = F₂ t`.

These are the local data for gluing the maps `φ_F` along a cover in Čech cohomology.

## Main definitions

* `MMP.DeRham.IsReductionModP`: `π : R → L` is reduction modulo `p`, and the `p`-torsion of `R`
  lies in `pR`.
* `MMP.DeRham.frobeniusDefect`: `δ(a) = π((F a - a ^ p) / p)`.
* `MMP.DeRham.frobeniusLiftForm`: the Frobenius-semilinear map `φ_F` on one-forms.
* `MMP.DeRham.frobeniusLiftHomotopy`: the Frobenius-semilinear map `η₁₂` from one-forms to
  functions.

## Main results

* `MMP.DeRham.frobeniusLiftForm_ιMulti_D`: `φ_F (dπ a) = π(a)^{p-1} dπ(a) + dδ(a)`.
* `MMP.DeRham.deRhamDifferential_frobeniusLiftForm`: `φ_F ω` is closed.
* `MMP.DeRham.isInvCartierRep_frobeniusLiftForm`: `φ_F ω` represents `C⁻¹ ω`.
* `MMP.DeRham.frobeniusLiftForm_dlog`: `φ_F (dlog π t) = dlog π t` when `F t = t ^ p`.
* `MMP.DeRham.frobeniusLiftForm_mem_closedLogForms`: `φ_F` maps logarithmic one-forms to
  closed logarithmic one-forms.
* `MMP.DeRham.frobeniusLiftForm_sub_frobeniusLiftForm`: `φ_{F₂} - φ_{F₁} = d ∘ η₁₂`.
* `MMP.DeRham.frobeniusLiftHomotopy_add_frobeniusLiftHomotopy`,
  `MMP.DeRham.frobeniusLiftHomotopy_self`: the cocycle relations.
* `MMP.DeRham.frobeniusLiftHomotopy_mem_logForms`: `η₁₂` maps logarithmic one-forms to
  functions coming from `B`.
* `MMP.DeRham.exists_isFrobeniusLift_isLocalization_away`: a Frobenius lift with `F f = f ^ p`
  extends to `A[1/f]`.

## Implementation notes

The forms are those of `L` over `k`, all of them rather than only the logarithmic ones: in the
geometric application `L` is the ring of functions on the complement of the divisor in an affine
chart, `R` its lift, and a Frobenius lift with `F tⱼ = tⱼ ^ p` on the chart extends to `R`
because it sends `∏ tⱼ` to `(∏ tⱼ)^p`. The logarithmic forms are then a `B`-submodule which
`φ_F` preserves. Over `L` itself the formulas `φ_F` and `η₁₂` need no logarithmic poles.

The hypothesis that `k` is perfect makes every additive map `L → M` satisfying the Leibniz rule
`k`-linear (`k` consists of `p`-th powers, killed by such a map when `p M = 0`); this is how the
derivations above become derivations over `k`.

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987)][DeligneIllusie1987], §1, §2 and §4.2.
-/

@[expose] public noncomputable section

open KaehlerDifferential KaehlerDifferential.Cartier exteriorPower

universe u

namespace MMP.DeRham

/-! ### Reduction modulo `p` and the defect of a Frobenius lift -/

section Defect

variable {p : ℕ} {R L : Type*} [CommRing R] [CommRing L]

variable (p) in
/-- `π : R → L` is **reduction modulo `p`**: it is surjective with kernel `pR`, and every element
of `R` killed by `p` lies in `pR` (as for `R` flat over `W₂(k)`). -/
structure IsReductionModP (π : R →+* L) : Prop where
  surjective : Function.Surjective π
  ker_eq : RingHom.ker π = Ideal.span {(p : R)}
  mem_span_of_mul_eq_zero : ∀ a : R, (p : R) * a = 0 → a ∈ Ideal.span {(p : R)}

variable {π : R →+* L} {F F₁ F₂ : R →+* R}

namespace IsReductionModP

variable (hπ : IsReductionModP p π)

include hπ

/-- An element of `R` reduces to zero exactly when it lies in `pR`. -/
theorem map_eq_zero_iff {a : R} : π a = 0 ↔ a ∈ Ideal.span {(p : R)} := by
  rw [← RingHom.mem_ker, hπ.ker_eq]

/-- The reduction of `p` is zero. -/
theorem map_natCast_eq_zero : π p = 0 :=
  hπ.map_eq_zero_iff.2 (Ideal.subset_span rfl)

/-- Cancelling `p`: if `p a = p b` then `π a = π b`. -/
theorem map_eq_of_natCast_mul_eq {a b : R} (h : (p : R) * a = p * b) : π a = π b := by
  rw [← sub_eq_zero, ← map_sub, hπ.map_eq_zero_iff]
  exact hπ.mem_span_of_mul_eq_zero _ (by rw [mul_sub, h, sub_self])

/-- A Frobenius lift reduces to the Frobenius: `π (F a) = π(a)^p`. -/
theorem map_frobenius (hF : IsFrobeniusLift p F) (a : R) : π (F a) = π a ^ p := by
  rw [← map_pow, ← sub_eq_zero, ← map_sub, hπ.map_eq_zero_iff]
  exact hF a

end IsReductionModP

variable [hp : Fact p.Prime]

variable (π) in
/-- **The defect of a Frobenius lift**: `δ(a) = π((F a - a ^ p) / p)`, the reduction of any `c`
with `F a = a ^ p + p c` (`MMP.DeRham.frobeniusDefect_eq`). -/
def frobeniusDefect (hF : IsFrobeniusLift p F) (a : R) : L :=
  π (Ideal.mem_span_singleton'.1 (hF a)).choose

omit hp in
/-- There is `c` with `F a = a ^ p + p c` whose reduction is `δ(a)`. -/
theorem exists_eq_frobeniusDefect (hF : IsFrobeniusLift p F) (a : R) :
    ∃ c : R, F a = a ^ p + p * c ∧ frobeniusDefect π hF a = π c := by
  have hc := (Ideal.mem_span_singleton'.1 (hF a)).choose_spec
  exact ⟨_, by linear_combination -hc, rfl⟩

/-- `(a + b)^p = a^p + b^p + p Q(a, b)` with `Q = ((X + Y)^p - X^p - Y^p) / p`. -/
theorem add_pow_eq_aeval_addPowQuotient {S : Type*} [CommRing S] (a b : S) :
    (a + b) ^ p = a ^ p + b ^ p + p * MvPolynomial.aeval ![a, b] (addPowQuotient p) := by
  have h := congrArg (MvPolynomial.aeval (R := ℤ) ![a, b]) (add_pow_eq_addPowQuotient p)
  simpa using h

variable (hπ : IsReductionModP p π)

include hπ

omit hp in
/-- If `F a = a ^ p + p c`, then `δ(a) = π(c)`. -/
theorem frobeniusDefect_eq (hF : IsFrobeniusLift p F) {a c : R} (h : F a = a ^ p + p * c) :
    frobeniusDefect π hF a = π c := by
  obtain ⟨c₀, h₀, e₀⟩ := exists_eq_frobeniusDefect (π := π) hF a
  rw [e₀]
  exact hπ.map_eq_of_natCast_mul_eq (by linear_combination h - h₀)

omit hp in
/-- If `F a = a ^ p`, then `δ(a) = 0`. -/
theorem frobeniusDefect_eq_zero (hF : IsFrobeniusLift p F) {a : R} (h : F a = a ^ p) :
    frobeniusDefect π hF a = 0 := by
  rw [frobeniusDefect_eq hπ hF (c := 0) (by rw [h, mul_zero, add_zero]), map_zero]

omit hp in
/-- `δ(ab) = a^p δ(b) + b^p δ(a)`. -/
theorem frobeniusDefect_mul (hF : IsFrobeniusLift p F) (a b : R) :
    frobeniusDefect π hF (a * b) =
      π a ^ p * frobeniusDefect π hF b + π b ^ p * frobeniusDefect π hF a := by
  obtain ⟨c, hc, ec⟩ := exists_eq_frobeniusDefect (π := π) hF a
  obtain ⟨d, hd, ed⟩ := exists_eq_frobeniusDefect (π := π) hF b
  rw [ec, ed, frobeniusDefect_eq hπ hF (c := a ^ p * d + b ^ p * c + p * c * d)
    (by rw [map_mul, hc, hd]; ring)]
  simp only [map_add, map_mul, map_pow, hπ.map_natCast_eq_zero]
  ring

/-- `δ(a + b) = δ(a) + δ(b) - Q(a, b)`. -/
theorem frobeniusDefect_add (hF : IsFrobeniusLift p F) (a b : R) :
    frobeniusDefect π hF (a + b) = frobeniusDefect π hF a + frobeniusDefect π hF b -
      MvPolynomial.aeval ![π a, π b] (addPowQuotient p) := by
  obtain ⟨c, hc, ec⟩ := exists_eq_frobeniusDefect (π := π) hF a
  obtain ⟨d, hd, ed⟩ := exists_eq_frobeniusDefect (π := π) hF b
  have hQ := add_pow_eq_aeval_addPowQuotient (p := p) a b
  rw [ec, ed, frobeniusDefect_eq hπ hF
    (c := c + d - MvPolynomial.aeval ![a, b] (addPowQuotient p))
    (by rw [map_add, hc, hd, hQ]; ring)]
  have : π (MvPolynomial.aeval ![a, b] (addPowQuotient p)) =
      MvPolynomial.aeval ![π a, π b] (addPowQuotient p) := by
    have h := MvPolynomial.comp_aeval_apply ![a, b] π.toIntAlgHom (addPowQuotient p)
    refine h.trans (congrArg (fun v => MvPolynomial.aeval v (addPowQuotient p)) ?_)
    funext i
    fin_cases i <;> rfl
  rw [map_sub, map_add, this]

/-- `δ(a + p c) = δ(a) + π(c)^p`: the defect depends on the lift only up to `p`-th powers. -/
theorem frobeniusDefect_add_natCast_mul (hF : IsFrobeniusLift p F) (a c : R) :
    frobeniusDefect π hF (a + p * c) = frobeniusDefect π hF a + π c ^ p := by
  obtain ⟨c₀, h₀, e₀⟩ := exists_eq_frobeniusDefect (π := π) hF a
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out a (p * c)
  have hp2 : 2 ≤ p := hp.out.two_le
  obtain ⟨m, hm⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
  have hpow : ((p : R) * c) ^ p = p * (p * (p : R) ^ m * c ^ p) := by
    rw [mul_pow, hm]; push_cast; ring
  rw [e₀, frobeniusDefect_eq hπ hF (c := c₀ + F c - (p * (p : R) ^ m * c ^ p + a * c * r * p))
    (by rw [map_add, map_mul, map_natCast, h₀, hr, hpow]; ring)]
  simp only [map_add, map_sub, map_mul, map_pow, hπ.map_natCast_eq_zero, hπ.map_frobenius hF]
  ring

/-- Two lifts of the same element have defects differing by a `p`-th power. -/
theorem exists_frobeniusDefect_eq_add_pow (hF : IsFrobeniusLift p F) {a b : R} (h : π a = π b) :
    ∃ c : R, frobeniusDefect π hF b = frobeniusDefect π hF a + π c ^ p := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hπ.map_eq_zero_iff.1
    (show π (b - a) = 0 by rw [map_sub, h, sub_self]))
  refine ⟨c, ?_⟩
  rw [← frobeniusDefect_add_natCast_mul hπ hF, show b = a + p * c by linear_combination -hc]

omit hp in
/-- Two Frobenius lifts agreeing at `a` have the same defect at `a`. -/
theorem frobeniusDefect_eq_of_eq (h₁ : IsFrobeniusLift p F₁) (h₂ : IsFrobeniusLift p F₂)
    {a : R} (ha : F₁ a = F₂ a) : frobeniusDefect π h₁ a = frobeniusDefect π h₂ a := by
  obtain ⟨c, hc, ec⟩ := exists_eq_frobeniusDefect (π := π) h₂ a
  rw [ec]
  exact frobeniusDefect_eq hπ h₁ (by rw [ha, hc])

omit hp in
/-- `δ₂(a) - δ₁(a) = π c` when `F₂ a - F₁ a = p c`. -/
theorem frobeniusDefect_sub_frobeniusDefect_eq (h₁ : IsFrobeniusLift p F₁)
    (h₂ : IsFrobeniusLift p F₂) {a c : R} (h : F₂ a - F₁ a = p * c) :
    frobeniusDefect π h₂ a - frobeniusDefect π h₁ a = π c := by
  obtain ⟨c₁, hc₁, ec₁⟩ := exists_eq_frobeniusDefect (π := π) h₁ a
  obtain ⟨c₂, hc₂, ec₂⟩ := exists_eq_frobeniusDefect (π := π) h₂ a
  rw [ec₁, ec₂, ← map_sub]
  exact hπ.map_eq_of_natCast_mul_eq (by linear_combination hc₁ - hc₂ + h)

omit hp in
/-- The difference of the defects of two Frobenius lifts is the reduction of
`(F₂ - F₁) / p` (`MMP.DeRham.frobeniusLiftDiff`). -/
theorem frobeniusDefect_sub_frobeniusDefect (hp2 : (p : R) ^ 2 = 0)
    (h₁ : IsFrobeniusLift p F₁) (h₂ : IsFrobeniusLift p F₂) (a : R) :
    frobeniusDefect π h₂ a - frobeniusDefect π h₁ a =
      Ideal.Quotient.lift _ π (fun _ hx => (hπ.map_eq_zero_iff).2 hx)
        (frobeniusLiftDiff h₁ h₂ (Ideal.Quotient.mk _ a)) := by
  obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {(p : R)})
    (frobeniusLiftDiff h₁ h₂ (Ideal.Quotient.mk _ a))
  have key := mulNatCastQuot_frobeniusLiftDiff hp2 h₁ h₂ a
  rw [← hd, mulNatCastQuot_mk] at key
  rw [← hd, Ideal.Quotient.lift_mk]
  exact frobeniusDefect_sub_frobeniusDefect_eq hπ h₁ h₂ (by linear_combination -key)

/-- The difference of the defects of two Frobenius lifts depends only on `π a`. -/
theorem frobeniusDefect_sub_frobeniusDefect_of_map_eq (h₁ : IsFrobeniusLift p F₁)
    (h₂ : IsFrobeniusLift p F₂) {a b : R} (h : π a = π b) :
    frobeniusDefect π h₂ b - frobeniusDefect π h₁ b =
      frobeniusDefect π h₂ a - frobeniusDefect π h₁ a := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hπ.map_eq_zero_iff.1
    (show π (b - a) = 0 by rw [map_sub, h, sub_self]))
  rw [show b = a + p * c by linear_combination -hc, frobeniusDefect_add_natCast_mul hπ h₂,
    frobeniusDefect_add_natCast_mul hπ h₁]
  ring

end Defect

/-! ### Derivations over a perfect base -/

section Perfect

variable (p : ℕ) (k : Type*) {L : Type*} [CommRing k] [CommRing L] [Algebra k L]
  [CharP L p] [ExpChar k p] [PerfectRing k p] {M : Type*} [AddCommGroup M] [Module L M]

include p

/-- Over a perfect ring `k` of characteristic `p`, an additive map `L → M` satisfying the
Leibniz rule kills `k`: the elements of `k` are `p`-th powers. -/
theorem map_algebraMap_eq_zero_of_leibniz (f : L →+ M)
    (hf : ∀ x y : L, f (x * y) = x • f y + y • f x) (c : k) : f (algebraMap k L c) = 0 := by
  let D' : Derivation ℤ L M := Derivation.mk' f.toIntLinearMap hf
  have h := D'.leibniz_pow (algebraMap k L ((frobeniusEquiv k p).symm c)) p
  rw [← map_pow, frobeniusEquiv_symm_pow_p, ← Nat.cast_smul_eq_nsmul L, CharP.cast_eq_zero,
    zero_smul] at h
  exact h

/-- The `L`-linear map `Ω[L⁄k] → M` induced by an additive map `f : L → M` satisfying the Leibniz
rule, `k` being perfect of characteristic `p`. -/
def liftKaehlerOfLeibniz (f : L →+ M) (hf : ∀ x y : L, f (x * y) = x • f y + y • f x) :
    Ω[L⁄k] →ₗ[L] M :=
  letI : Module k M := Module.compHom M (algebraMap k L)
  haveI : IsScalarTower k L M := ⟨fun a b m => by
    change (a • b) • m = algebraMap k L a • b • m
    rw [Algebra.smul_def, mul_smul]⟩
  (Derivation.mk'
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c x => by
        change f (c • x) = algebraMap k L c • f x
        rw [Algebra.smul_def, hf, map_algebraMap_eq_zero_of_leibniz p k f hf, smul_zero,
          add_zero] } hf).liftKaehlerDifferential

/-- The map induced by `f` sends `d x` to `f x`. -/
@[simp]
theorem liftKaehlerOfLeibniz_D (f : L →+ M) (hf : ∀ x y : L, f (x * y) = x • f y + y • f x)
    (x : L) : liftKaehlerOfLeibniz p k f hf (D k L x) = f x :=
  letI : Module k M := Module.compHom M (algebraMap k L)
  haveI : IsScalarTower k L M := ⟨fun a b m => by
    change (a • b) • m = algebraMap k L a • b • m
    rw [Algebra.smul_def, mul_smul]⟩
  Derivation.liftKaehlerDifferential_comp_D _ x

end Perfect

/-! ### The one-forms `F^* / p` -/

section Form

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] (k : Type u) {L : Type u}
  [CommRing k] [CommRing L] [Algebra k L] [CharP L p] [ExpChar k p] [PerfectRing k p]
  {π : R →+* L} {F : R →+* R}

omit [ExpChar k p] [PerfectRing k p] in
/-- The one-form `π(a)^{p-1} dπ(a) + dδ(a)` depends only on `π a`. -/
theorem pow_pred_smul_D_add_D_frobeniusDefect_of_map_eq (hπ : IsReductionModP p π)
    (hF : IsFrobeniusLift p F) {a b : R} (h : π a = π b) :
    π b ^ (p - 1) • D k L (π b) + D k L (frobeniusDefect π hF b) =
      π a ^ (p - 1) • D k L (π a) + D k L (frobeniusDefect π hF a) := by
  obtain ⟨c, hc⟩ := exists_frobeniusDefect_eq_add_pow hπ hF h
  rw [hc, map_add, D_pow_char, add_zero, h]

omit [ExpChar k p] [PerfectRing k p] in
/-- The one-form `π(a)^{p-1} dπ(a) + dδ(a)` is unchanged when `a` is replaced by the chosen
preimage of `π a`. -/
theorem pow_pred_smul_D_add_D_frobeniusDefect_surjInv (hπ : IsReductionModP p π)
    (hF : IsFrobeniusLift p F) (a : R) :
    π (Function.surjInv hπ.surjective (π a)) ^ (p - 1) •
        D k L (π (Function.surjInv hπ.surjective (π a))) +
      D k L (frobeniusDefect π hF (Function.surjInv hπ.surjective (π a))) =
      π a ^ (p - 1) • D k L (π a) + D k L (frobeniusDefect π hF a) :=
  pow_pred_smul_D_add_D_frobeniusDefect_of_map_eq k hπ hF
    (Function.surjInv_eq hπ.surjective _).symm

omit [ExpChar k p] [PerfectRing k p] in
/-- The one-form `π(a)^{p-1} dπ(a) + dδ(a)` is additive in `a`. -/
theorem pow_pred_smul_D_add_D_frobeniusDefect_add (hπ : IsReductionModP p π)
    (hF : IsFrobeniusLift p F) (a b : R) :
    π (a + b) ^ (p - 1) • D k L (π (a + b)) + D k L (frobeniusDefect π hF (a + b)) =
      (π a ^ (p - 1) • D k L (π a) + D k L (frobeniusDefect π hF a)) +
        (π b ^ (p - 1) • D k L (π b) + D k L (frobeniusDefect π hF b)) := by
  rw [frobeniusDefect_add hπ hF, map_add π, pow_pred_smul_D_add p, map_sub, map_add]
  abel

omit [ExpChar k p] [PerfectRing k p] in
/-- The one-form `ω(a) = π(a)^{p-1} dπ(a) + dδ(a)` satisfies
`ω(ab) = π(a)^p ω(b) + π(b)^p ω(a)`. -/
theorem pow_pred_smul_D_add_D_frobeniusDefect_mul (hπ : IsReductionModP p π)
    (hF : IsFrobeniusLift p F) (a b : R) :
    π (a * b) ^ (p - 1) • D k L (π (a * b)) + D k L (frobeniusDefect π hF (a * b)) =
      π a ^ p • (π b ^ (p - 1) • D k L (π b) + D k L (frobeniusDefect π hF b)) +
        π b ^ p • (π a ^ (p - 1) • D k L (π a) + D k L (frobeniusDefect π hF a)) := by
  have hp1 : 1 ≤ p := hp.out.one_le
  rw [frobeniusDefect_mul hπ hF, map_add, Derivation.leibniz, Derivation.leibniz,
    D_pow_char, D_pow_char, smul_zero, smul_zero, add_zero, add_zero, map_mul,
    Derivation.leibniz]
  simp only [smul_add, smul_smul]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel, mul_pow, pow_succ]
  rw [show π a ^ q * π b ^ q * π a = π a ^ q * π a * π b ^ q by ring,
    show π a ^ q * π b ^ q * π b = π b ^ q * π b * π a ^ q by ring]
  abel

variable (p) in
/-- The derivation `π a ↦ π(a)^{p-1} dπ(a) + dδ(a)` of `L` into the one-forms with the
Frobenius action, as an additive map. -/
def frobeniusLiftFormAddHom (hπ : IsReductionModP p π) (hF : IsFrobeniusLift p F) :
    L →+ twistedForms p k L 1 :=
  AddMonoidHom.mk' (fun x => twist p (ιMulti L 1 fun _ =>
      π (Function.surjInv hπ.surjective x) ^ (p - 1) •
          D k L (π (Function.surjInv hπ.surjective x)) +
        D k L (frobeniusDefect π hF (Function.surjInv hπ.surjective x)))) fun x y => by
    obtain ⟨a, rfl⟩ := hπ.surjective x
    obtain ⟨b, rfl⟩ := hπ.surjective y
    rw [← map_add, pow_pred_smul_D_add_D_frobeniusDefect_surjInv k hπ hF,
      pow_pred_smul_D_add_D_frobeniusDefect_surjInv k hπ hF,
      pow_pred_smul_D_add_D_frobeniusDefect_surjInv k hπ hF,
      pow_pred_smul_D_add_D_frobeniusDefect_add k hπ hF, ιMulti_one_add, map_add]

omit [ExpChar k p] [PerfectRing k p] in
/-- The value of `MMP.DeRham.frobeniusLiftFormAddHom` at `π a` is
`π(a)^{p-1} dπ(a) + dδ(a)`. -/
theorem frobeniusLiftFormAddHom_apply (hπ : IsReductionModP p π) (hF : IsFrobeniusLift p F)
    (a : R) : frobeniusLiftFormAddHom p k hπ hF (π a) =
      twist p (ιMulti L 1 fun _ =>
        π a ^ (p - 1) • D k L (π a) + D k L (frobeniusDefect π hF a)) := by
  change twist p (ιMulti L 1 fun _ => _) = _
  rw [pow_pred_smul_D_add_D_frobeniusDefect_surjInv k hπ hF]

omit [ExpChar k p] [PerfectRing k p] in
/-- `MMP.DeRham.frobeniusLiftFormAddHom` satisfies the Leibniz rule. -/
theorem frobeniusLiftFormAddHom_mul (hπ : IsReductionModP p π) (hF : IsFrobeniusLift p F)
    (x y : L) : frobeniusLiftFormAddHom p k hπ hF (x * y) =
      x • frobeniusLiftFormAddHom p k hπ hF y + y • frobeniusLiftFormAddHom p k hπ hF x := by
  obtain ⟨a, rfl⟩ := hπ.surjective x
  obtain ⟨b, rfl⟩ := hπ.surjective y
  rw [← map_mul, frobeniusLiftFormAddHom_apply, frobeniusLiftFormAddHom_apply,
    frobeniusLiftFormAddHom_apply, smul_twist, smul_twist, ← map_add,
    pow_pred_smul_D_add_D_frobeniusDefect_mul k hπ hF, ιMulti_one_add, ιMulti_one_smul,
    ιMulti_one_smul]

/-- **The one-forms `F^*/p` of a Frobenius lift**: the Frobenius-semilinear map
`φ_F : Ω¹_{L/k} → Ω¹_{L/k}` with `φ_F (dπ(a)) = π(a)^{p-1} dπ(a) + dδ(a)`
(`MMP.DeRham.frobeniusLiftForm_ιMulti_D`), where `δ` is the defect of `F`. -/
def frobeniusLiftForm (hπ : IsReductionModP p π) (hF : IsFrobeniusLift p F) :
    ⋀[L]^1 (Ω[L⁄k]) →ₛₗ[frobenius L p] ⋀[L]^1 (Ω[L⁄k]) where
  toFun ω := (twist p).symm (liftKaehlerOfLeibniz p k (frobeniusLiftFormAddHom p k hπ hF)
    (frobeniusLiftFormAddHom_mul k hπ hF) (oneEquiv L (Ω[L⁄k]) ω))
  map_add' ω η := by rw [map_add, map_add, map_add]
  map_smul' c ω := by rw [map_smul, map_smul, twist_symm_smul, frobenius_def]

/-- `φ_F` is Frobenius-semilinear: `φ_F (c ω) = c^p φ_F ω`. -/
theorem frobeniusLiftForm_smul (hπ : IsReductionModP p π) (hF : IsFrobeniusLift p F) (c : L)
    (ω : ⋀[L]^1 (Ω[L⁄k])) :
    frobeniusLiftForm k hπ hF (c • ω) = c ^ p • frobeniusLiftForm k hπ hF ω := by
  rw [LinearMap.map_smulₛₗ, frobenius_def]

/-- **The value of `φ_F` on an exact form**: `φ_F (dπ(a)) = π(a)^{p-1} dπ(a) + dδ(a)`. -/
theorem frobeniusLiftForm_ιMulti_D (hπ : IsReductionModP p π) (hF : IsFrobeniusLift p F)
    (a : R) : frobeniusLiftForm k hπ hF (ιMulti L 1 fun _ => D k L (π a)) =
      ιMulti L 1 fun _ => π a ^ (p - 1) • D k L (π a) + D k L (frobeniusDefect π hF a) := by
  change (twist p).symm (liftKaehlerOfLeibniz p k _ _ (oneEquiv L (Ω[L⁄k]) _)) = _
  rw [oneEquiv_ιMulti, liftKaehlerOfLeibniz_D, frobeniusLiftFormAddHom_apply,
    AddEquiv.symm_apply_apply]

/-- **Induction on one-forms**: a property of one-forms which holds for `0` and the forms
`dx`, and is stable under sums and multiplication by functions, holds for all one-forms. -/
theorem oneForms_induction {P : ⋀[L]^1 (Ω[L⁄k]) → Prop} (h0 : P 0)
    (hadd : ∀ ω η, P ω → P η → P (ω + η)) (hsmul : ∀ (c : L) ω, P ω → P (c • ω))
    (hD : ∀ x : L, P (ιMulti L 1 fun _ => D k L x)) (ω : ⋀[L]^1 (Ω[L⁄k])) : P ω := by
  obtain ⟨w, rfl⟩ := (oneEquiv L (Ω[L⁄k])).symm.surjective ω
  have hw : w ∈ Submodule.span L (Set.range (D k L)) := by
    rw [span_range_derivation]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    rw [oneEquiv_symm_apply]
    exact hD y
  | zero => rw [map_zero]; exact h0
  | add x y _ _ hx hy => rw [map_add]; exact hadd _ _ hx hy
  | smul c x _ hx => rw [map_smul]; exact hsmul c _ hx

/-- **`φ_F ω` is closed.** -/
theorem deRhamDifferential_frobeniusLiftForm (hπ : IsReductionModP p π)
    (hF : IsFrobeniusLift p F) (ω : ⋀[L]^1 (Ω[L⁄k])) :
    deRhamDifferential (A := k) 1 (frobeniusLiftForm k hπ hF ω) = 0 := by
  induction ω using oneForms_induction (k := k) with
  | h0 => rw [map_zero, map_zero]
  | hadd ω η hω hη => rw [map_add, map_add, hω, hη, add_zero]
  | hsmul c ω hω => rw [frobeniusLiftForm_smul, deRhamDifferential_pow_smul, hω, smul_zero]
  | hD x =>
    obtain ⟨a, rfl⟩ := hπ.surjective x
    rw [frobeniusLiftForm_ιMulti_D, ιMulti_one_add, map_add, ιMulti_one_smul,
      deRhamDifferential_pow_pred_smul_D, deRhamDifferential_ιMulti_one_D, add_zero]

/-- **`φ_F` lifts the inverse Cartier map**: `φ_F ω` is a closed form representing `C⁻¹ ω`. -/
theorem isInvCartierRep_frobeniusLiftForm (hπ : IsReductionModP p π)
    (hF : IsFrobeniusLift p F) (ω : ⋀[L]^1 (Ω[L⁄k])) :
    IsInvCartierRep p 1 ω (frobeniusLiftForm k hπ hF ω) := by
  induction ω using oneForms_induction (k := k) with
  | h0 => rw [map_zero]; exact IsInvCartierRep.zero
  | hadd ω η hω hη => rw [map_add]; exact hω.add hη
  | hsmul c ω hω => rw [frobeniusLiftForm_smul]; exact hω.smul c
  | hD x =>
    obtain ⟨a, rfl⟩ := hπ.surjective x
    have h := isInvCartierRep_ιMulti_D (p := p) (A := k) (fun _ : Fin 1 => π a)
    refine h.of_sub_mem_exactForms ?_
    rw [frobeniusLiftForm_ιMulti_D, ιMulti_one_add, add_sub_cancel_left]
    exact twist_ιMulti_one_D_mem_exactForms p _

omit [CharP L p] in
/-- `x⁻¹^p x^{p-1} = x⁻¹`, where `x⁻¹` is `Ring.inverse x` (zero for a non-unit). -/
theorem ringInverse_pow_mul_pow_pred (x : L) :
    Ring.inverse x ^ p * x ^ (p - 1) = Ring.inverse x := by
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.one_le; omega⟩
  by_cases hx : IsUnit x
  · obtain ⟨v, rfl⟩ := hx
    rw [Ring.inverse_unit, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul, hq, Nat.add_sub_cancel]
    congr 1
    group
  · rw [Ring.inverse_non_unit x hx, hq, zero_pow (Nat.succ_ne_zero q), zero_mul]

/-- **`φ_F` fixes `dlog π(t)` when `F t = t ^ p`.** Here `dlog x = x⁻¹ dx`, which is `0` when `x`
is not a unit. -/
theorem frobeniusLiftForm_dlog (hπ : IsReductionModP p π) (hF : IsFrobeniusLift p F) {t : R}
    (ht : F t = t ^ p) :
    frobeniusLiftForm k hπ hF (ιMulti L 1 fun _ => Ring.inverse (π t) • D k L (π t)) =
      ιMulti L 1 fun _ => Ring.inverse (π t) • D k L (π t) := by
  rw [ιMulti_one_smul, frobeniusLiftForm_smul, frobeniusLiftForm_ιMulti_D,
    frobeniusDefect_eq_zero hπ hF ht, map_zero, add_zero, ιMulti_one_smul, smul_smul,
    ringInverse_pow_mul_pow_pred]

/-- **`φ_F` preserves logarithmic forms.** Let `B → L` be a ring map and `uⱼ ∈ B`. Suppose every
`b ∈ B` has a lift `b̃` to `R` with `F b̃ = b̃ ^ p + p c` where `π c` comes from `B`, and every
`uⱼ` has a lift `t` with `F t = t ^ p`. Then `φ_F` maps the logarithmic one-forms of `B` with
poles along the `uⱼ` to closed logarithmic one-forms. -/
theorem frobeniusLiftForm_mem_closedLogForms {B : Type u} [CommRing B] [Algebra B L]
    {ι : Type*} {u : ι → B} (hπ : IsReductionModP p π) (hF : IsFrobeniusLift p F)
    (hB : ∀ b : B, ∃ b' c : R, π b' = algebraMap B L b ∧ F b' = b' ^ p + p * c ∧
      π c ∈ Set.range (algebraMap B L))
    (hu : ∀ j, ∃ t : R, π t = algebraMap B L (u j) ∧ F t = t ^ p)
    (ω : ⋀[L]^1 (Ω[L⁄k])) (hω : (ω : ExteriorAlgebra L (Ω[L⁄k])) ∈ logForms k L u 1) :
    ((frobeniusLiftForm k hπ hF ω : ⋀[L]^1 (Ω[L⁄k])) : ExteriorAlgebra L (Ω[L⁄k])) ∈
      closedLogForms k L u 1 := by
  refine ⟨?_, _, rfl, deRhamDifferential_frobeniusLiftForm k hπ hF ω⟩
  let S : Submodule B (⋀[L]^1 (Ω[L⁄k])) :=
    { carrier := {ω | ((frobeniusLiftForm k hπ hF ω : ⋀[L]^1 (Ω[L⁄k])) :
        ExteriorAlgebra L (Ω[L⁄k])) ∈ logForms k L u 1}
      zero_mem' := by simp
      add_mem' := by
        intro ω η hω hη
        simpa only [Set.mem_ofPred_eq, map_add, Submodule.coe_add] using add_mem hω hη
      smul_mem' := by
        intro b ω hω
        simp only [Set.mem_ofPred_eq] at hω ⊢
        rw [← algebraMap_smul L b ω, frobeniusLiftForm_smul, ← map_pow, algebraMap_smul,
          Submodule.coe_smul_of_tower]
        exact Submodule.smul_mem _ _ hω }
  refine mem_of_mem_logForms S (fun v hv => ?_) ω hω
  have hv' : v = fun _ => v 0 := funext fun i => congrArg v (Subsingleton.elim i 0)
  change ((frobeniusLiftForm k hπ hF _ : ⋀[L]^1 (Ω[L⁄k])) : ExteriorAlgebra L (Ω[L⁄k])) ∈
    logForms k L u 1
  rw [hv']
  rcases hv 0 with ⟨b, hb⟩ | ⟨j, hj⟩
  · obtain ⟨b', c, hb', hc, b'', hb''⟩ := hB b
    rw [← hb]
    dsimp only
    rw [← hb', frobeniusLiftForm_ιMulti_D, frobeniusDefect_eq hπ hF hc, ← hb'',
      ιMulti_one_add, ιMulti_one_smul, hb', ← map_pow, Submodule.coe_add, algebraMap_smul,
      Submodule.coe_smul_of_tower]
    refine add_mem (Submodule.smul_mem (logForms k L u 1) _ ?_) ?_
    · rw [ιMulti_apply_coe]
      exact ιMulti_mem_logForms _ fun _ => D_mem_logGenerators u b
    · rw [ιMulti_apply_coe]
      exact ιMulti_mem_logForms _ fun _ => D_mem_logGenerators u b''
  · obtain ⟨t, ht, hFt⟩ := hu j
    rw [← hj]
    dsimp only
    rw [← ht, frobeniusLiftForm_dlog k hπ hF hFt, ιMulti_apply_coe, ht]
    exact ιMulti_mem_logForms _ fun _ => dlog_mem_logGenerators u j

end Form

/-! ### The homotopy between the forms of two Frobenius lifts -/

section Homotopy

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] (k : Type u) {L : Type u}
  [CommRing k] [CommRing L] [Algebra k L] [CharP L p] [ExpChar k p] [PerfectRing k p]
  {π : R →+* L} {F₁ F₂ F₃ : R →+* R}

variable (p) in
/-- The derivation `π a ↦ δ₂(a) - δ₁(a)` of `L` into the functions with the Frobenius action,
for two Frobenius lifts with defects `δ₁, δ₂`, as an additive map. -/
def frobeniusLiftHomotopyAddHom (hπ : IsReductionModP p π) (h₁ : IsFrobeniusLift p F₁)
    (h₂ : IsFrobeniusLift p F₂) : L →+ twistedForms p k L 0 :=
  AddMonoidHom.mk' (fun x => twist p ((zeroEquiv L (Ω[L⁄k])).symm
      (frobeniusDefect π h₂ (Function.surjInv hπ.surjective x) -
        frobeniusDefect π h₁ (Function.surjInv hπ.surjective x)))) fun x y => by
    obtain ⟨a, rfl⟩ := hπ.surjective x
    obtain ⟨b, rfl⟩ := hπ.surjective y
    have e : ∀ c : R, frobeniusDefect π h₂ (Function.surjInv hπ.surjective (π c)) -
        frobeniusDefect π h₁ (Function.surjInv hπ.surjective (π c)) =
          frobeniusDefect π h₂ c - frobeniusDefect π h₁ c := fun c =>
      frobeniusDefect_sub_frobeniusDefect_of_map_eq hπ h₁ h₂
        (Function.surjInv_eq hπ.surjective _).symm
    rw [← map_add, e, e, e, ← map_add, ← map_add, frobeniusDefect_add hπ h₂,
      frobeniusDefect_add hπ h₁]
    congr 2
    ring

omit [ExpChar k p] [PerfectRing k p] in
/-- The value of `MMP.DeRham.frobeniusLiftHomotopyAddHom` at `π a` is `δ₂(a) - δ₁(a)`. -/
theorem frobeniusLiftHomotopyAddHom_apply (hπ : IsReductionModP p π) (h₁ : IsFrobeniusLift p F₁)
    (h₂ : IsFrobeniusLift p F₂) (a : R) :
    frobeniusLiftHomotopyAddHom p k hπ h₁ h₂ (π a) =
      twist p ((zeroEquiv L (Ω[L⁄k])).symm (frobeniusDefect π h₂ a - frobeniusDefect π h₁ a)) := by
  change twist p ((zeroEquiv L (Ω[L⁄k])).symm _) = _
  rw [frobeniusDefect_sub_frobeniusDefect_of_map_eq hπ h₁ h₂
    (Function.surjInv_eq hπ.surjective _).symm]

omit [ExpChar k p] [PerfectRing k p] in
/-- `MMP.DeRham.frobeniusLiftHomotopyAddHom` satisfies the Leibniz rule. -/
theorem frobeniusLiftHomotopyAddHom_mul (hπ : IsReductionModP p π) (h₁ : IsFrobeniusLift p F₁)
    (h₂ : IsFrobeniusLift p F₂) (x y : L) :
    frobeniusLiftHomotopyAddHom p k hπ h₁ h₂ (x * y) =
      x • frobeniusLiftHomotopyAddHom p k hπ h₁ h₂ y +
        y • frobeniusLiftHomotopyAddHom p k hπ h₁ h₂ x := by
  obtain ⟨a, rfl⟩ := hπ.surjective x
  obtain ⟨b, rfl⟩ := hπ.surjective y
  rw [← map_mul, frobeniusLiftHomotopyAddHom_apply, frobeniusLiftHomotopyAddHom_apply,
    frobeniusLiftHomotopyAddHom_apply, smul_twist, smul_twist, ← map_add, ← map_smul, ← map_smul,
    ← map_add, frobeniusDefect_mul hπ h₂, frobeniusDefect_mul hπ h₁, smul_eq_mul, smul_eq_mul]
  congr 2
  ring

/-- **The homotopy between the forms of two Frobenius lifts**: the Frobenius-semilinear map
`η₁₂ : Ω¹_{L/k} → Ω⁰_{L/k}` with `η₁₂ (dπ(a)) = δ₂(a) - δ₁(a)`
(`MMP.DeRham.frobeniusLiftHomotopy_ιMulti_D`), the class of `(F₂ a - F₁ a) / p` when `p² = 0`
in `R` (`MMP.DeRham.frobeniusDefect_sub_frobeniusDefect`). -/
def frobeniusLiftHomotopy (hπ : IsReductionModP p π) (h₁ : IsFrobeniusLift p F₁)
    (h₂ : IsFrobeniusLift p F₂) :
    ⋀[L]^1 (Ω[L⁄k]) →ₛₗ[frobenius L p] ⋀[L]^0 (Ω[L⁄k]) where
  toFun ω := (twist p).symm (liftKaehlerOfLeibniz p k (frobeniusLiftHomotopyAddHom p k hπ h₁ h₂)
    (frobeniusLiftHomotopyAddHom_mul k hπ h₁ h₂) (oneEquiv L (Ω[L⁄k]) ω))
  map_add' ω η := by rw [map_add, map_add, map_add]
  map_smul' c ω := by rw [map_smul, map_smul, twist_symm_smul, frobenius_def]

/-- `η₁₂` is Frobenius-semilinear: `η₁₂ (c ω) = c^p η₁₂ ω`. -/
theorem frobeniusLiftHomotopy_smul (hπ : IsReductionModP p π) (h₁ : IsFrobeniusLift p F₁)
    (h₂ : IsFrobeniusLift p F₂) (c : L) (ω : ⋀[L]^1 (Ω[L⁄k])) :
    frobeniusLiftHomotopy k hπ h₁ h₂ (c • ω) = c ^ p • frobeniusLiftHomotopy k hπ h₁ h₂ ω := by
  rw [LinearMap.map_smulₛₗ, frobenius_def]

/-- `η₁₂ (dπ(a)) = δ₂(a) - δ₁(a)`. -/
theorem frobeniusLiftHomotopy_ιMulti_D (hπ : IsReductionModP p π) (h₁ : IsFrobeniusLift p F₁)
    (h₂ : IsFrobeniusLift p F₂) (a : R) :
    frobeniusLiftHomotopy k hπ h₁ h₂ (ιMulti L 1 fun _ => D k L (π a)) =
      (zeroEquiv L (Ω[L⁄k])).symm (frobeniusDefect π h₂ a - frobeniusDefect π h₁ a) := by
  change (twist p).symm (liftKaehlerOfLeibniz p k _ _ (oneEquiv L (Ω[L⁄k]) _)) = _
  rw [oneEquiv_ιMulti, liftKaehlerOfLeibniz_D, frobeniusLiftHomotopyAddHom_apply,
    AddEquiv.symm_apply_apply]

/-- **`φ_{F₂} - φ_{F₁} = d ∘ η₁₂`.** -/
theorem frobeniusLiftForm_sub_frobeniusLiftForm (hπ : IsReductionModP p π)
    (h₁ : IsFrobeniusLift p F₁) (h₂ : IsFrobeniusLift p F₂) (ω : ⋀[L]^1 (Ω[L⁄k])) :
    frobeniusLiftForm k hπ h₂ ω - frobeniusLiftForm k hπ h₁ ω =
      deRhamDifferential (A := k) 0 (frobeniusLiftHomotopy k hπ h₁ h₂ ω) := by
  induction ω using oneForms_induction (k := k) with
  | h0 => simp only [map_zero, sub_zero]
  | hadd ω η hω hη => rw [map_add, map_add, map_add, map_add, ← hω, ← hη]; abel
  | hsmul c ω hω =>
    rw [frobeniusLiftForm_smul, frobeniusLiftForm_smul, frobeniusLiftHomotopy_smul,
      deRhamDifferential_pow_smul, ← hω, smul_sub]
  | hD x =>
    obtain ⟨a, rfl⟩ := hπ.surjective x
    rw [frobeniusLiftForm_ιMulti_D, frobeniusLiftForm_ιMulti_D, frobeniusLiftHomotopy_ιMulti_D,
      zeroEquiv_symm_apply, deRhamDifferential_zero_smul_ιMulti]
    simp only [← oneEquiv_symm_apply]
    rw [← map_sub, map_sub (D k L)]
    congr 1
    abel

/-- **The cocycle relation** `η₁₂ + η₂₃ = η₁₃`. -/
theorem frobeniusLiftHomotopy_add_frobeniusLiftHomotopy (hπ : IsReductionModP p π)
    (h₁ : IsFrobeniusLift p F₁) (h₂ : IsFrobeniusLift p F₂) (h₃ : IsFrobeniusLift p F₃)
    (ω : ⋀[L]^1 (Ω[L⁄k])) :
    frobeniusLiftHomotopy k hπ h₁ h₂ ω + frobeniusLiftHomotopy k hπ h₂ h₃ ω =
      frobeniusLiftHomotopy k hπ h₁ h₃ ω := by
  induction ω using oneForms_induction (k := k) with
  | h0 => simp only [map_zero, add_zero]
  | hadd ω η hω hη => rw [map_add, map_add, map_add, ← hω, ← hη]; abel
  | hsmul c ω hω =>
    rw [frobeniusLiftHomotopy_smul, frobeniusLiftHomotopy_smul, frobeniusLiftHomotopy_smul, ← hω,
      smul_add]
  | hD x =>
    obtain ⟨a, rfl⟩ := hπ.surjective x
    rw [frobeniusLiftHomotopy_ιMulti_D, frobeniusLiftHomotopy_ιMulti_D,
      frobeniusLiftHomotopy_ιMulti_D, ← map_add]
    congr 1
    ring

/-- `η₁₁ = 0`. -/
@[simp]
theorem frobeniusLiftHomotopy_self (hπ : IsReductionModP p π) (h₁ : IsFrobeniusLift p F₁)
    (ω : ⋀[L]^1 (Ω[L⁄k])) : frobeniusLiftHomotopy k hπ h₁ h₁ ω = 0 :=
  add_eq_left.mp (frobeniusLiftHomotopy_add_frobeniusLiftHomotopy k hπ h₁ h₁ h₁ ω)

/-- `η₁₂ (dlog π(t)) = 0` when `F₁ t = F₂ t`. -/
theorem frobeniusLiftHomotopy_dlog (hπ : IsReductionModP p π) (h₁ : IsFrobeniusLift p F₁)
    (h₂ : IsFrobeniusLift p F₂) {t : R} (ht : F₁ t = F₂ t) :
    frobeniusLiftHomotopy k hπ h₁ h₂
      (ιMulti L 1 fun _ => Ring.inverse (π t) • D k L (π t)) = 0 := by
  rw [ιMulti_one_smul, frobeniusLiftHomotopy_smul, frobeniusLiftHomotopy_ιMulti_D,
    frobeniusDefect_eq_of_eq hπ h₁ h₂ ht, sub_self, map_zero, smul_zero]

/-- **`η₁₂` maps logarithmic one-forms to functions on `B`.** Let `B → L` be a ring map and
`uⱼ ∈ B`. Suppose every `b ∈ B` has a lift `b̃` to `R` with `F₂ b̃ - F₁ b̃ = p c` where `π c`
comes from `B`, and every `uⱼ` has a lift `t` with `F₁ t = F₂ t`. Then `η₁₂` maps the logarithmic
one-forms to the image of `B` in `Ω⁰_{L/k} = L`. -/
theorem frobeniusLiftHomotopy_mem_logForms {B : Type u} [CommRing B] [Algebra B L]
    {ι : Type*} {u : ι → B} (hπ : IsReductionModP p π) (h₁ : IsFrobeniusLift p F₁)
    (h₂ : IsFrobeniusLift p F₂)
    (hB : ∀ b : B, ∃ b' c : R, π b' = algebraMap B L b ∧ F₂ b' - F₁ b' = p * c ∧
      π c ∈ Set.range (algebraMap B L))
    (hu : ∀ j, ∃ t : R, π t = algebraMap B L (u j) ∧ F₁ t = F₂ t)
    (ω : ⋀[L]^1 (Ω[L⁄k])) (hω : (ω : ExteriorAlgebra L (Ω[L⁄k])) ∈ logForms k L u 1) :
    ((frobeniusLiftHomotopy k hπ h₁ h₂ ω : ⋀[L]^0 (Ω[L⁄k])) : ExteriorAlgebra L (Ω[L⁄k])) ∈
      logForms k L u 0 := by
  let S : Submodule B (⋀[L]^1 (Ω[L⁄k])) :=
    { carrier := {ω | ((frobeniusLiftHomotopy k hπ h₁ h₂ ω : ⋀[L]^0 (Ω[L⁄k])) :
        ExteriorAlgebra L (Ω[L⁄k])) ∈ logForms k L u 0}
      zero_mem' := by simp
      add_mem' := by
        intro ω η hω hη
        simpa only [Set.mem_ofPred_eq, map_add, Submodule.coe_add] using add_mem hω hη
      smul_mem' := by
        intro b ω hω
        simp only [Set.mem_ofPred_eq] at hω ⊢
        rw [← algebraMap_smul L b ω, frobeniusLiftHomotopy_smul, ← map_pow, algebraMap_smul,
          Submodule.coe_smul_of_tower]
        exact Submodule.smul_mem _ _ hω }
  refine mem_of_mem_logForms S (fun v hv => ?_) ω hω
  have hv' : v = fun _ => v 0 := funext fun i => congrArg v (Subsingleton.elim i 0)
  change ((frobeniusLiftHomotopy k hπ h₁ h₂ _ : ⋀[L]^0 (Ω[L⁄k])) : ExteriorAlgebra L (Ω[L⁄k])) ∈
    logForms k L u 0
  rw [hv']
  rcases hv 0 with ⟨b, hb⟩ | ⟨j, hj⟩
  · obtain ⟨b', c, hb', hc, b'', hb''⟩ := hB b
    rw [← hb]
    dsimp only
    rw [← hb', frobeniusLiftHomotopy_ιMulti_D, frobeniusDefect_sub_frobeniusDefect_eq hπ h₁ h₂ hc,
      ← hb'', zeroEquiv_symm_apply, algebraMap_smul, Submodule.coe_smul_of_tower]
    refine Submodule.smul_mem (logForms k L u 0) _ ?_
    rw [ιMulti_apply_coe]
    exact ιMulti_mem_logForms _ fun m => m.elim0
  · obtain ⟨t, ht, hFt⟩ := hu j
    rw [← hj]
    dsimp only
    rw [← ht, frobeniusLiftHomotopy_dlog k hπ h₁ h₂ hFt, Submodule.coe_zero]
    exact zero_mem _

end Homotopy

/-! ### Reduction modulo `p` and Frobenius lifts on localizations -/

section Localization

variable {p : ℕ} {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

/-- The quotient map `R → R ⧸ pR` is reduction modulo `p` when the `p`-torsion lies in `pR`. -/
theorem isReductionModP_mk (hflat : ∀ a : R, (p : R) * a = 0 → a ∈ Ideal.span {(p : R)}) :
    IsReductionModP p (Ideal.Quotient.mk (Ideal.span {(p : R)})) :=
  ⟨Ideal.Quotient.mk_surjective, Ideal.mk_ker, hflat⟩

variable (f : A) [IsLocalization.Away f R]

/-- **A Frobenius lift extends to a localization** `A[1/f]` when `F f = f ^ p`. -/
theorem exists_isFrobeniusLift_isLocalization_away {F : A →+* A} (hF : IsFrobeniusLift p F)
    (hf : F f = f ^ p) :
    ∃ F' : R →+* R, IsFrobeniusLift p F' ∧
      ∀ a : A, F' (algebraMap A R a) = algebraMap A R (F a) := by
  have hu : IsUnit ((algebraMap A R).comp F f) := by
    rw [RingHom.comp_apply, hf, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit f).pow p
  refine ⟨IsLocalization.Away.lift f hu, fun x => ?_, fun a => IsLocalization.Away.lift_eq f hu a⟩
  obtain ⟨n, a, hx⟩ := IsLocalization.Away.surj f x
  have h1 := congrArg (IsLocalization.Away.lift f hu) hx
  rw [map_mul, map_pow, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq,
    RingHom.comp_apply, RingHom.comp_apply, hf, map_pow] at h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hF a)
  obtain ⟨v, hv⟩ := (IsLocalization.Away.algebraMap_isUnit (S := R) f).pow (p * n)
  refine Ideal.mem_span_singleton'.2 ⟨algebraMap A R c * ↑v⁻¹, ?_⟩
  have key : (IsLocalization.Away.lift f hu x - x ^ p) * ↑v = algebraMap A R c * p := by
    have e1 : IsLocalization.Away.lift f hu x * algebraMap A R f ^ (p * n) =
        algebraMap A R (F a) := by rw [pow_mul, h1]
    have e2 : x ^ p * algebraMap A R f ^ (p * n) = algebraMap A R (a ^ p) := by
      rw [pow_mul', ← mul_pow, hx, map_pow]
    rw [hv, sub_mul, e1, e2, ← map_sub, ← hc, map_mul, map_natCast]
  calc algebraMap A R c * ↑v⁻¹ * p = (algebraMap A R c * p) * ↑v⁻¹ := by ring
    _ = _ := by rw [← key, mul_assoc, Units.mul_inv, mul_one]

end Localization

end MMP.DeRham
