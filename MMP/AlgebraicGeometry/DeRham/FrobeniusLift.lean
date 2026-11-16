module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.RingTheory.WittVector.Domain
public import Mathlib.RingTheory.WittVector.Identities
public import Mathlib.RingTheory.WittVector.Truncated

/-!
# Frobenius lifts along étale coordinates, and the difference of two lifts

Let `p` be a prime and `S` a commutative ring. A **Frobenius lift** on `S` is a ring endomorphism
`F` with `F a ≡ a ^ p` modulo `p` for every `a` (`MMP.DeRham.IsFrobeniusLift`).

**Existence.** Let `R` be a ring in which `p` is nilpotent, with an endomorphism `σ` lifting the
Frobenius modulo `p`, and let `S` be an `R`-algebra with elements `x₁, …` such that
`R[X₁, …] → S`, `Xⱼ ↦ xⱼ`, is formally smooth (for instance étale). On `R[X]` the map acting by
`σ` on coefficients with `Xⱼ ↦ Xⱼ ^ p` is a Frobenius lift. Twisting the `R[X]`-algebra
structure of `S` by it, the `p`-th power map `S → S ⧸ pS` becomes a map of `R[X]`-algebras, and
lifting it along the nilpotent thickening `S → S ⧸ pS` by formal smoothness gives a Frobenius
lift `F` of `S`, `σ`-semilinear over `R`, with `F xⱼ = xⱼ ^ p`. The main case is
`R = W_n(k)`, the truncated Witt vectors of a perfect ring `k` of characteristic `p`, with `σ`
the Witt vector Frobenius (`MMP.DeRham.truncatedWittFrobenius`); there `p ^ n = 0`.

**Comparison.** Suppose `p ^ 2 = 0` in `S` and the annihilator of `p` is `pS`, as for a flat
`W₂(k)`-algebra. Then multiplication by `p` is an injection `S ⧸ pS → S` with image `pS`
(`MMP.DeRham.mulNatCastQuot`), so two Frobenius lifts `F₁, F₂` differ by `F₂ - F₁ = p · h` for a
unique `h : S ⧸ pS → S ⧸ pS`. This `h` is additive and satisfies
`h (a b) = a ^ p h(b) + b ^ p h(a)`: it is a derivation of `S ⧸ pS` into its Frobenius
pushforward. The differences of three lifts satisfy the cocycle relation.

## Main definitions

* `MMP.DeRham.IsFrobeniusLift`: `F a ≡ a ^ p` modulo `p` for all `a`.
* `MMP.DeRham.powModP`: the ring homomorphism `S → S ⧸ pS`, `a ↦ a ^ p`.
* `MMP.DeRham.truncatedWittFrobenius`: the Witt vector Frobenius of `W_n(k)`, `char k = p`.
* `MMP.DeRham.mulNatCastQuot`: multiplication by `p`, `S ⧸ pS → S`, when `p ^ 2 = 0`.
* `MMP.DeRham.frobeniusLiftDiff`: `(F₂ - F₁) / p` as a function on `S ⧸ pS`.

## Main results

* `MMP.DeRham.exists_isFrobeniusLift_of_formallySmooth`: existence of a `σ`-semilinear
  Frobenius lift with `F xⱼ = xⱼ ^ p` along formally smooth coordinates.
* `MMP.DeRham.exists_isFrobeniusLift_truncatedWittVector`: the same over `W_n(k)`, `k` perfect.
* `MMP.DeRham.mem_span_natCast_of_natCast_mul_eq_zero_of_flat`: over a flat `W₂(k)`-algebra an
  element killed by `p` lies in `pS`.
* `MMP.DeRham.existsUnique_sub_eq_mulNatCastQuot`: two Frobenius lifts differ by `p` times a
  unique function `h` on `S ⧸ pS`;
  `MMP.DeRham.frobeniusLiftDiff_add`, `MMP.DeRham.frobeniusLiftDiff_mul`: `h` is a Frobenius
  derivation; `MMP.DeRham.frobeniusLiftDiff_add_frobeniusLiftDiff`: the cocycle relation.

## Implementation notes

The setting is commutative algebra throughout: `S` plays the ring of functions of an affine open
of a smooth lifting over `W₂(k)`, and `S ⧸ pS` that of the corresponding open of the special
fibre. Formal smoothness of the coordinates suffices for existence; formal étaleness would also
give uniqueness of the lift, which is not needed here. The flatness hypothesis of the comparison
is used only through the annihilator of `p`, which is how it is stated.

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987)][DeligneIllusie1987], §1 and §2.
-/

@[expose] public noncomputable section

open MvPolynomial

open scoped TensorProduct

namespace MMP.DeRham

section General

variable {S : Type*} [CommRing S]

/-- A ring endomorphism `F` of `S` lifts the Frobenius modulo `p` if `F a ≡ a ^ p` modulo `p`
for every `a`. -/
def IsFrobeniusLift (p : ℕ) (F : S →+* S) : Prop :=
  ∀ a : S, F a - a ^ p ∈ Ideal.span {(p : S)}

/-- The `p`-th power map `S → S ⧸ pS`, a ring homomorphism. -/
def powModP (p : ℕ) [hp : Fact p.Prime] (S : Type*) [CommRing S] :
    S →+* S ⧸ Ideal.span {(p : S)} where
  toFun a := Ideal.Quotient.mk _ (a ^ p)
  map_one' := by simp
  map_mul' a b := by simp [mul_pow]
  map_zero' := by simp [hp.out.ne_zero]
  map_add' a b := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out a b
    have : Ideal.Quotient.mk (Ideal.span {(p : S)}) (p * a * b * r) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
        (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))))
    simp [hr, this]

/-- `powModP p S` sends `a` to the class of `a ^ p` modulo `p`. -/
@[simp]
theorem powModP_apply (p : ℕ) [Fact p.Prime] (a : S) :
    powModP p S a = Ideal.Quotient.mk _ (a ^ p) := rfl

/-- `F` is a Frobenius lift if and only if its reduction modulo `p` is the `p`-th power map
`MMP.DeRham.powModP`. -/
theorem isFrobeniusLift_iff (p : ℕ) [Fact p.Prime] (F : S →+* S) :
    IsFrobeniusLift p F ↔ (Ideal.Quotient.mk _).comp F = powModP p S := by
  simp only [IsFrobeniusLift, RingHom.ext_iff, RingHom.comp_apply, powModP_apply,
    Ideal.Quotient.eq]

/-- Lifting along a nilpotent thickening `T → T ⧸ J` a ring map out of a formally smooth
`P`-algebra whose restriction to `P` is lifted by a given `φ : P →+* T`. -/
private theorem exists_lift_of_formallySmooth {P S T : Type*} [CommRing P] [CommRing S]
    [CommRing T] [Algebra P S] [Algebra.FormallySmooth P S] (φ : P →+* T) (J : Ideal T)
    (hJ : IsNilpotent J) (g : S →+* T ⧸ J)
    (hg : g.comp (algebraMap P S) = (Ideal.Quotient.mk J).comp φ) :
    ∃ f : S →+* T, f.comp (algebraMap P S) = φ ∧ (Ideal.Quotient.mk J).comp f = g := by
  let : Algebra P T := φ.toAlgebra
  obtain ⟨f, hf⟩ := Algebra.FormallySmooth.exists_lift (R := P) J hJ
    { g with commutes' := fun r => congr($hg r) }
  exact ⟨f.toRingHom, RingHom.ext f.commutes, RingHom.ext fun a => congr($hf a)⟩

/-- **Frobenius lifts along formally smooth coordinates.** Let `p` be nilpotent in `R`, `σ` an
endomorphism of `R` lifting the Frobenius modulo `p`, and `x : ι → S` such that
`R[X] → S`, `Xⱼ ↦ xⱼ`, is formally smooth. Then `S` has a Frobenius lift `F`, `σ`-semilinear
over `R`, with `F xⱼ = xⱼ ^ p`. -/
theorem exists_isFrobeniusLift_of_formallySmooth {R : Type*} [CommRing R] [Algebra R S]
    {ι : Type*} (p : ℕ) [Fact p.Prime] (hpR : IsNilpotent (p : R)) (σ : R →+* R)
    (hσ : IsFrobeniusLift p σ) (x : ι → S)
    (hx : (MvPolynomial.aeval (R := R) x).toRingHom.FormallySmooth) :
    ∃ F : S →+* S, IsFrobeniusLift p F ∧ (∀ (r : R) (a : S), F (r • a) = σ r • F a) ∧
      ∀ j, F (x j) = x j ^ p := by
  let FP : MvPolynomial ι R →+* MvPolynomial ι R := eval₂Hom (C.comp σ) fun j => X j ^ p
  let e : MvPolynomial ι R →+* S := (MvPolynomial.aeval (R := R) x).toRingHom
  let : Algebra (MvPolynomial ι R) S := e.toAlgebra
  have : Algebra.FormallySmooth (MvPolynomial ι R) S := hx
  have hI : IsNilpotent (Ideal.span {(p : S)}) := by
    obtain ⟨n, hn⟩ := hpR
    refine ⟨n, ?_⟩
    rw [Ideal.span_singleton_pow, ← map_natCast (algebraMap R S), ← map_pow, hn, map_zero,
      Ideal.span_singleton_eq_bot.2 rfl, Ideal.zero_eq_bot]
  have hg : (powModP p S).comp (algebraMap (MvPolynomial ι R) S) =
      (Ideal.Quotient.mk _).comp (e.comp FP) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, powModP_apply, FP, eval₂Hom_C, e]
      rw [Ideal.Quotient.eq]
      change algebraMap (MvPolynomial ι R) S (C r) ^ p - aeval x (C (σ r)) ∈ _
      have := Ideal.mem_map_of_mem (algebraMap R S) (hσ r)
      rw [Ideal.map_span, Set.image_singleton, map_natCast] at this
      rw [← Ideal.neg_mem_iff, neg_sub]
      convert this using 1
      simp [e, RingHom.algebraMap_toAlgebra]
    · simp [powModP_apply, FP, e, RingHom.algebraMap_toAlgebra]
  obtain ⟨F, hFe, hFp⟩ := exists_lift_of_formallySmooth (e.comp FP) _ hI _ hg
  refine ⟨F, (isFrobeniusLift_iff p F).2 hFp, fun r a => ?_, fun j => ?_⟩
  · have h := congr($hFe (C r))
    simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra, FP, eval₂Hom_C, e,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C] at h
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, h]
  · simpa [FP, e, RingHom.algebraMap_toAlgebra] using congr($hFe (X j))

section Comparison

variable {p : ℕ}

variable (p) in
/-- Multiplication by `p` from `S ⧸ pS` to `S`, well defined when `p ^ 2 = 0`; its image is
`pS`, and it is injective when the annihilator of `p` is `pS`
(`MMP.DeRham.mulNatCastQuot_injective`). -/
def mulNatCastQuot (hp2 : (p : S) ^ 2 = 0) : S ⧸ Ideal.span {(p : S)} →ₗ[S] S :=
  (Ideal.span {(p : S)}).liftQ (LinearMap.mulLeft S (p : S)) <| by
    rw [Ideal.span, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      LinearMap.mem_ker, LinearMap.mulLeft_apply, ← pow_two, hp2]

/-- `MMP.DeRham.mulNatCastQuot` sends the class of `a` to `p * a`. -/
@[simp]
theorem mulNatCastQuot_mk (hp2 : (p : S) ^ 2 = 0) (a : S) :
    mulNatCastQuot p hp2 (Ideal.Quotient.mk _ a) = p * a := rfl

/-- Multiplication by `p` from `S ⧸ pS` to `S` is injective when the annihilator of `p` is
contained in `pS`. -/
theorem mulNatCastQuot_injective (hp2 : (p : S) ^ 2 = 0)
    (hflat : ∀ a : S, (p : S) * a = 0 → a ∈ Ideal.span {(p : S)}) :
    Function.Injective (mulNatCastQuot p hp2) := by
  refine (injective_iff_map_eq_zero _).2 fun q hq => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact Ideal.Quotient.eq_zero_iff_mem.2 (hflat a hq)

variable {F₁ F₂ F₃ : S →+* S}

/-- Two Frobenius lifts agree modulo `p`: `F₂ a - F₁ a ∈ pS`. -/
theorem IsFrobeniusLift.sub_mem (h₁ : IsFrobeniusLift p F₁) (h₂ : IsFrobeniusLift p F₂)
    (a : S) : F₂ a - F₁ a ∈ Ideal.span {(p : S)} := by
  simpa using _root_.sub_mem (h₂ a) (h₁ a)

/-- The difference of two Frobenius lifts `F₁, F₂` divided by `p`, as a function
`h : S ⧸ pS → S ⧸ pS` with `F₂ a - F₁ a = p · h(a mod p)`
(`MMP.DeRham.mulNatCastQuot_frobeniusLiftDiff`). When `p ^ 2 = 0` and the annihilator of `p` is
contained in `pS` it is the unique such function, and a Frobenius derivation:
`h (a b) = a ^ p h b + b ^ p h a`. -/
def frobeniusLiftDiff (h₁ : IsFrobeniusLift p F₁) (h₂ : IsFrobeniusLift p F₂) :
    S ⧸ Ideal.span {(p : S)} → S ⧸ Ideal.span {(p : S)} := fun q =>
  Ideal.Quotient.mk _ (Ideal.mem_span_singleton'.1
    (h₁.sub_mem h₂ (Function.surjInv Ideal.Quotient.mk_surjective q))).choose

/-- `p · h(a mod p) = F₂ a - F₁ a`, where `h` is `MMP.DeRham.frobeniusLiftDiff`. -/
theorem mulNatCastQuot_frobeniusLiftDiff (hp2 : (p : S) ^ 2 = 0) (h₁ : IsFrobeniusLift p F₁)
    (h₂ : IsFrobeniusLift p F₂) (a : S) :
    mulNatCastQuot p hp2 (frobeniusLiftDiff h₁ h₂ (Ideal.Quotient.mk _ a)) = F₂ a - F₁ a := by
  set a' := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {(p : S)}))
    (Ideal.Quotient.mk _ a)
  have ha' : Ideal.Quotient.mk (Ideal.span {(p : S)}) a' = Ideal.Quotient.mk _ a :=
    Function.surjInv_eq _ _
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 ha'.symm)
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (h₁.sub_mem h₂ b)
  have hc := (Ideal.mem_span_singleton'.1 (h₁.sub_mem h₂ a')).choose_spec
  have ha : a = a' + b * p := by linear_combination -hb
  have e₁ : F₁ a = F₁ a' + F₁ b * p := by rw [ha, map_add, map_mul, map_natCast]
  have e₂ : F₂ a = F₂ a' + F₂ b * p := by rw [ha, map_add, map_mul, map_natCast]
  simp only [frobeniusLiftDiff, mulNatCastQuot_mk]
  rw [e₁, e₂]
  linear_combination hc + (p : S) * hd - d * hp2

/-- **Two Frobenius lifts differ by `p` times a unique function modulo `p`.** If `p ^ 2 = 0`
in `S` and every element killed by `p` lies in `pS`, then for Frobenius lifts `F₁, F₂` there is
a unique `h : S ⧸ pS → S ⧸ pS` with `F₂ a - F₁ a = p · h (a mod p)`. -/
theorem existsUnique_sub_eq_mulNatCastQuot (hp2 : (p : S) ^ 2 = 0)
    (hflat : ∀ a : S, (p : S) * a = 0 → a ∈ Ideal.span {(p : S)})
    (h₁ : IsFrobeniusLift p F₁) (h₂ : IsFrobeniusLift p F₂) :
    ∃! h : S ⧸ Ideal.span {(p : S)} → S ⧸ Ideal.span {(p : S)},
      ∀ a : S, F₂ a - F₁ a = mulNatCastQuot p hp2 (h (Ideal.Quotient.mk _ a)) := by
  refine ⟨frobeniusLiftDiff h₁ h₂, fun a => (mulNatCastQuot_frobeniusLiftDiff hp2 h₁ h₂ a).symm,
    fun h hh => funext fun q => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  apply mulNatCastQuot_injective hp2 hflat
  rw [← hh, mulNatCastQuot_frobeniusLiftDiff]

variable (hp2 : (p : S) ^ 2 = 0) (hflat : ∀ a : S, (p : S) * a = 0 → a ∈ Ideal.span {(p : S)})

include hp2 hflat

/-- The difference of two Frobenius lifts is additive. -/
theorem frobeniusLiftDiff_add (h₁ : IsFrobeniusLift p F₁) (h₂ : IsFrobeniusLift p F₂)
    (x y : S ⧸ Ideal.span {(p : S)}) :
    frobeniusLiftDiff h₁ h₂ (x + y) = frobeniusLiftDiff h₁ h₂ x + frobeniusLiftDiff h₁ h₂ y := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  apply mulNatCastQuot_injective hp2 hflat
  rw [map_add, ← map_add, mulNatCastQuot_frobeniusLiftDiff, mulNatCastQuot_frobeniusLiftDiff,
    mulNatCastQuot_frobeniusLiftDiff, map_add, map_add]
  ring

/-- **The difference of two Frobenius lifts is a Frobenius derivation:**
`h (x y) = x ^ p h y + y ^ p h x`. -/
theorem frobeniusLiftDiff_mul (h₁ : IsFrobeniusLift p F₁) (h₂ : IsFrobeniusLift p F₂)
    (x y : S ⧸ Ideal.span {(p : S)}) :
    frobeniusLiftDiff h₁ h₂ (x * y) =
      x ^ p * frobeniusLiftDiff h₁ h₂ y + y ^ p * frobeniusLiftDiff h₁ h₂ x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  apply mulNatCastQuot_injective hp2 hflat
  have hsmul : ∀ (c : S) (q : S ⧸ Ideal.span {(p : S)}),
      mulNatCastQuot p hp2 (Ideal.Quotient.mk _ c * q) = c * mulNatCastQuot p hp2 q := by
    intro c q
    rw [← Ideal.Quotient.algebraMap_eq, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  rw [← map_mul, ← map_pow, ← map_pow, map_add, hsmul, hsmul, mulNatCastQuot_frobeniusLiftDiff,
    mulNatCastQuot_frobeniusLiftDiff, mulNatCastQuot_frobeniusLiftDiff]
  obtain ⟨u₁, hu₁⟩ := Ideal.mem_span_singleton'.1 (h₁ a)
  obtain ⟨u₂, hu₂⟩ := Ideal.mem_span_singleton'.1 (h₂ a)
  obtain ⟨v₁, hv₁⟩ := Ideal.mem_span_singleton'.1 (h₁ b)
  obtain ⟨v₂, hv₂⟩ := Ideal.mem_span_singleton'.1 (h₂ b)
  rw [map_mul, map_mul, show F₁ a = a ^ p + u₁ * p by linear_combination -hu₁,
    show F₂ a = a ^ p + u₂ * p by linear_combination -hu₂,
    show F₁ b = b ^ p + v₁ * p by linear_combination -hv₁,
    show F₂ b = b ^ p + v₂ * p by linear_combination -hv₂]
  linear_combination (u₂ * v₂ - u₁ * v₁) * hp2

/-- The difference of two Frobenius lifts vanishes on the class of an element on which they
agree. -/
theorem frobeniusLiftDiff_eq_zero_of_eq (h₁ : IsFrobeniusLift p F₁) (h₂ : IsFrobeniusLift p F₂)
    {a : S} (ha : F₁ a = F₂ a) : frobeniusLiftDiff h₁ h₂ (Ideal.Quotient.mk _ a) = 0 := by
  apply mulNatCastQuot_injective hp2 hflat
  rw [mulNatCastQuot_frobeniusLiftDiff, ha, sub_self, map_zero]

/-- The difference of a Frobenius lift with itself is zero. -/
theorem frobeniusLiftDiff_self (h₁ : IsFrobeniusLift p F₁) :
    frobeniusLiftDiff h₁ h₁ = 0 := funext fun x => by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact frobeniusLiftDiff_eq_zero_of_eq hp2 hflat h₁ h₁ rfl

/-- The differences of Frobenius lifts satisfy the cocycle relation. -/
theorem frobeniusLiftDiff_add_frobeniusLiftDiff (h₁ : IsFrobeniusLift p F₁)
    (h₂ : IsFrobeniusLift p F₂) (h₃ : IsFrobeniusLift p F₃) :
    frobeniusLiftDiff h₁ h₂ + frobeniusLiftDiff h₂ h₃ = frobeniusLiftDiff h₁ h₃ :=
  funext fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply mulNatCastQuot_injective hp2 hflat
    rw [Pi.add_apply, map_add, mulNatCastQuot_frobeniusLiftDiff,
      mulNatCastQuot_frobeniusLiftDiff, mulNatCastQuot_frobeniusLiftDiff]
    ring

end Comparison

end General

section Witt

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (k : Type*) [CommRing k] [CharP k p]

/-- The Witt vector Frobenius `σ` of the truncated Witt vectors `W_n(k)` of a ring of
characteristic `p`: the reduction of `WittVector.frobenius`, acting on coefficients by
`a ↦ a ^ p`. -/
def truncatedWittFrobenius : TruncatedWittVector p n k →+* TruncatedWittVector p n k :=
  (WittVector.truncate n).liftOfSurjective (WittVector.truncate_surjective p n k)
    ⟨(WittVector.truncate n).comp WittVector.frobenius, fun x hx => by
      rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, WittVector.mem_ker_truncate]
      rw [WittVector.mem_ker_truncate] at hx
      intro i hi
      rw [WittVector.coeff_frobenius_charP, hx i hi, zero_pow hp.out.ne_zero]⟩

variable {p n k}

/-- The Witt vector Frobenius of `W_n(k)` commutes with truncation:
`σ (truncate n x) = truncate n (frobenius x)`. -/
@[simp]
theorem truncatedWittFrobenius_truncate (x : WittVector p k) :
    truncatedWittFrobenius p n k (WittVector.truncate n x) =
      WittVector.truncate n (WittVector.frobenius x) :=
  (WittVector.truncate n).liftOfSurjective_comp_apply (WittVector.truncate_surjective p n k) _ x

/-- The Witt vector Frobenius of `W_n(k)` raises each coefficient to the `p`-th power. -/
@[simp]
theorem coeff_truncatedWittFrobenius (x : TruncatedWittVector p n k) (i : Fin n) :
    (truncatedWittFrobenius p n k x).coeff i = x.coeff i ^ p := by
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p n k x
  rw [truncatedWittFrobenius_truncate, WittVector.coeff_truncate, WittVector.coeff_truncate,
    WittVector.coeff_frobenius_charP]

variable (p n k) in
/-- In `W_n(k)`, `p ^ n = 0`. -/
theorem natCast_pow_eq_zero_truncatedWittVector :
    (p : TruncatedWittVector p n k) ^ n = 0 := by
  rw [← map_natCast (WittVector.truncate (p := p) (R := k) n), ← map_pow, ← RingHom.mem_ker,
    WittVector.mem_ker_truncate]
  intro i hi
  exact WittVector.coeff_p_pow_eq_zero p k hi.ne

/-- For `k` perfect, the Witt vector Frobenius of `W_n(k)` is a Frobenius lift. -/
theorem isFrobeniusLift_truncatedWittFrobenius [PerfectRing k p] :
    IsFrobeniusLift p (truncatedWittFrobenius p n k) := fun w => by
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p n k w
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1
    ((WittVector.mem_span_p_iff_coeff_zero_eq_zero (WittVector.frobenius y - y ^ p)).2 (by
      rw [← WittVector.constantCoeff_apply]
      simp only [map_sub, map_pow, WittVector.constantCoeff_apply,
        WittVector.coeff_frobenius_charP, sub_self]))
  rw [truncatedWittFrobenius_truncate, ← map_pow, ← map_sub, ← hv, map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

/-- In `W₂(k)`, `k` perfect, an element killed by `p` is divisible by `p`. -/
theorem exists_eq_natCast_mul_of_natCast_mul_eq_zero [PerfectRing k p]
    {w : TruncatedWittVector p 2 k} (hw : (p : TruncatedWittVector p 2 k) * w = 0) :
    ∃ v, w = p * v := by
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p 2 k w
  have h1 : y.coeff 0 = 0 := by
    rw [← map_natCast (WittVector.truncate (p := p) (R := k) 2), ← map_mul, ← RingHom.mem_ker,
      WittVector.mem_ker_truncate, mul_comm, ← WittVector.verschiebung_frobenius] at hw
    have := hw 1 (by norm_num)
    rw [WittVector.verschiebung_coeff_add_one, WittVector.coeff_frobenius_charP] at this
    exact (injective_frobenius k p) (by rw [map_zero, frobenius_def]; simpa using this)
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1
    ((WittVector.mem_span_p_iff_coeff_zero_eq_zero y).2 h1)
  exact ⟨WittVector.truncate 2 v, by rw [← hv, map_mul, map_natCast, mul_comm]⟩

variable (p n k) in
/-- **Frobenius lifts along étale coordinates over `W_n(k)`.** Let `k` be a perfect ring of
characteristic `p`, `σ` the Witt vector Frobenius of `W_n(k)`, and `S` a `W_n(k)`-algebra with
elements `x₁, …` such that `W_n(k)[X₁, …] → S`, `Xⱼ ↦ xⱼ`, is formally smooth (for instance
étale). Then `S` has a ring endomorphism `F` lifting the Frobenius modulo `p`, `σ`-semilinear over
`W_n(k)`, with `F xⱼ = xⱼ ^ p`. -/
theorem exists_isFrobeniusLift_truncatedWittVector [PerfectRing k p] {S ι : Type*} [CommRing S]
    [Algebra (TruncatedWittVector p n k) S] (x : ι → S)
    (hx : (MvPolynomial.aeval (R := TruncatedWittVector p n k) x).toRingHom.FormallySmooth) :
    ∃ F : S →+* S, IsFrobeniusLift p F ∧
      (∀ (w : TruncatedWittVector p n k) (a : S),
        F (w • a) = truncatedWittFrobenius p n k w • F a) ∧
      ∀ j, F (x j) = x j ^ p :=
  exists_isFrobeniusLift_of_formallySmooth p ⟨n, natCast_pow_eq_zero_truncatedWittVector p n k⟩
    _ isFrobeniusLift_truncatedWittFrobenius x hx

variable (p k) in
/-- If `S` is flat over `W₂(k)`, `k` perfect, then an element of `S` killed by `p` is divisible
by `p`. -/
theorem mem_span_natCast_of_natCast_mul_eq_zero_of_flat [PerfectRing k p] {S : Type*}
    [CommRing S] [Algebra (TruncatedWittVector p 2 k) S]
    [Module.Flat (TruncatedWittVector p 2 k) S] {a : S} (ha : (p : S) * a = 0) :
    a ∈ Ideal.span {(p : S)} := by
  set W := TruncatedWittVector p 2 k
  let f : W →ₗ[W] W := LinearMap.mulLeft W (p : W)
  have hf : Function.Exact f f := by
    intro w
    simp only [f, LinearMap.mulLeft_apply, Set.mem_range]
    refine ⟨fun hw => ?_, ?_⟩
    · exact (exists_eq_natCast_mul_of_natCast_mul_eq_zero hw).imp fun _ => Eq.symm
    · rintro ⟨v, rfl⟩
      rw [← mul_assoc, ← pow_two, natCast_pow_eq_zero_truncatedWittVector, zero_mul]
  have hzero : f.lTensor S (a ⊗ₜ 1) = 0 := by
    rw [LinearMap.lTensor_tmul, LinearMap.mulLeft_apply,
      show (p : W) * 1 = (p : W) • (1 : W) from (smul_eq_mul ..).symm, ← TensorProduct.smul_tmul,
      Algebra.smul_def, map_natCast, ha, TensorProduct.zero_tmul]
  obtain ⟨u, hu⟩ := (Module.Flat.lTensor_exact S hf _).1 hzero
  have key : ∀ u : S ⊗[W] W, TensorProduct.rid W S (f.lTensor S u) ∈ Ideal.span {(p : S)} := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul s w =>
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
      simp only [f, LinearMap.mulLeft_apply, mul_smul]
      rw [Algebra.smul_def (p : W), map_natCast]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    | add x y hx hy => simpa only [map_add] using add_mem hx hy
  simpa only [hu, TensorProduct.rid_tmul, one_smul] using key u

end Witt

end MMP.DeRham
