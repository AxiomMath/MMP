module

public import MMP.Attr
public import MMP.RingTheory.Kaehler.PluriformProduct
public import MMP.RingTheory.NoetherNormalization.CoordinateChange

/-!
# Residues lift at a codimension-one point of a normal prime divisor

Let `X` be a normal variety of dimension `n + 1` over a field `k` of characteristic zero,
`S ⊂ X` a normal prime divisor and `Q` a codimension-one point of `S`, with image `x ∈ X`.
The stalk at `x` of `ω_X(S) = Hom(𝓘_S, ω_X)` consists of the rational top forms `τ` with at
most a simple pole along `S` and no pole along any other prime divisor through `x`; the stalk
`ω_{S,Q}` consists of the rational top forms on `S` without pole at `Q`. The Poincaré residue
maps the first onto the second.

First a form `σ` is built with a simple pole along `S`, no other pole through `x`, and a nonzero
residue `ρ_σ` without zero at `Q`. Since the top forms on `S` are a line, `ρ = g ρ_σ` with
`ord_Q g ≥ 0`; then `g` lies in `𝒪_{T,Q}`, lifts to `b ∈ 𝒪_{X,x}` along the closed immersion, and
`τ = b σ` has residue `b̄ ρ_σ = ρ` and the required orders, `b` being regular at `x`.

## Main results

* `MMP.Fourfold.exists_isPoincareResidue_of_le_ordForm_of_charZero`: every rational top form on
  `S` regular at `Q` is the Poincaré residue of a rational top form on `X` which is a section of
  `ω_X(S)` near `x`.
* `MMP.Fourfold.exists_isPoincareResidue_of_le_ordForm`: the same for `k = ℂ`.
* `MMP.Fourfold.exists_form_of_residue_order`: a rational top form with a simple pole along `S`,
  no other pole through `x` and a nonzero residue without zero at `Q`.
* `MMP.Fourfold.exists_ordForm_eq_neg_one_isPoincareResidue`: over `ℂ`, a form `σ ≠ 0` with
  `ord_S σ = -1` and a nonzero Poincaré residue.

## Implementation notes

Both reflexive sheaves are described through their stalks inside the rational forms: on a normal
scheme a rational form is a section of `ω_X(S)` near `x` exactly when its orders along the prime
divisors through `x` are bounded below by minus their multiplicity in `S`. The residue map is the
Poincaré residue `MMP.Fourfold.IsPoincareResidue`, which is unique when it exists.

The source obtains the surjectivity of the residue from duality: `Ext¹(𝒪_X, ω_X) = 0` for the
Cohen–Macaulay `𝒪_{X,x}` makes `Hom(𝓘_S, ω_X) → Ext¹(𝒪_S, ω_X) = ω_S` onto. Here the form `σ`
is built by the trace instead. On an affine chart `Spec R ∋ x`, a Noether normalization
`k[X₀, …, X_n] → R` is chosen with `S ∩ k[X] = (X₀)` and `𝔪_x ∩ k[X] = (X₀, w)`. Over the
regular local ring `C = k[X]_{(X₀, w)}`, the normalization `B` of `C` in `𝒪_{X,x}` is free.
A functional `φ : B → C` lifting `Tr_{(B/𝔭)/(C/X₀)}(u t · -) / w̄`, for a uniformizer `t` at `Q`,
is `Tr(F ·)` for some `F` in the function field (nondegeneracy of the trace form in characteristic
zero). Then `σ = F dX₀ ∧ ⋯ ∧ dX_n` has the required orders: the tame bound on the codifferent and
the tame different `dX₀ ∧ ⋯ ∧ dX_n = t_E^{e_E - 1}·(unit)·(generator)` along every prime divisor
`E` through `x` cancel against each other.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 16
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP MMP.Mori

/-! ### Traces in finite extensions of discrete valuation rings -/

/-- A maximal ideal `E` with `E ⊔ J = ⊤` does not contain `J`. -/
private theorem not_le_of_sup_eq_top {S : Type*} [CommRing S] {E J : Ideal S} [E.IsMaximal]
    (h : E ⊔ J = ⊤) : ¬ J ≤ E := fun hJ =>
  Ideal.IsMaximal.ne_top ‹_› (by rwa [sup_eq_left.mpr hJ] at h)

/-- Every maximal ideal of an integral extension of a local ring `O` contains `𝔪_O`. -/
theorem map_maximalIdeal_le {O S : Type*} [CommRing O] [IsLocalRing O] [CommRing S]
    [Algebra O S] [Algebra.IsIntegral O S] (M : Ideal S) [M.IsMaximal] :
    (IsLocalRing.maximalIdeal O).map (algebraMap O S) ≤ M := by
  rw [Ideal.map_le_iff_le_comap]
  exact (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) M)).ge

/-- **The `E`-primary part of `𝔪_O S`.** For a Dedekind domain `S` free of finite rank over a local
domain `O` which is not a field, and a maximal ideal `E` of `S`, `𝔪_O S = E ^ c J` with `c ≠ 0`
and `J` coprime to `E`. -/
private theorem exists_map_maximalIdeal_eq_pow_mul {O S : Type*} [CommRing O] [IsDomain O]
    [IsLocalRing O] [CommRing S] [IsDomain S] [IsDedekindDomain S] [Algebra O S]
    [Module.Free O S] [Module.Finite O S] (hO : IsLocalRing.maximalIdeal O ≠ ⊥)
    (E : Ideal S) [E.IsMaximal] :
    ∃ c ≠ 0, ∃ J : Ideal S, E ⊔ J = ⊤ ∧
      (IsLocalRing.maximalIdeal O).map (algebraMap O S) = E ^ c * J := by
  haveI : Algebra.IsIntegral O S := Algebra.IsIntegral.of_finite O S
  have hI0 : (IsLocalRing.maximalIdeal O).map (algebraMap O S) ≠ ⊥ := by
    rwa [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective O S)]
  obtain ⟨J, hEJ, hIJ⟩ := Ideal.eq_prime_pow_mul_coprime hI0 E
  refine ⟨_, fun hc => not_le_of_sup_eq_top hEJ ?_, J, hEJ, hIJ⟩
  rw [hc, pow_zero, one_mul] at hIJ
  exact hIJ ▸ map_maximalIdeal_le E

/-- **The tame bound on the codifferent.** Let `S` be a Dedekind domain, free of finite rank over
a local domain `O` whose maximal ideal is `(ϖ) ≠ 0` and whose residue field has characteristic
zero. If `y ∈ S` has `Tr_{S/O}(y s) ∈ 𝔪_O ^ k` for every `s ∈ S` (with `k ≥ 1`), and
`𝔪_O S ⊆ E ^ e` for a maximal ideal `E` of `S`, then `y ∈ E ^ ((k - 1) e + 1)`. -/
theorem mem_pow_of_trace_mul_mem {O S : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
    [CommRing S] [IsDomain S] [IsDedekindDomain S] [Algebra O S] [Module.Free O S]
    [Module.Finite O S] [CharZero (O ⧸ IsLocalRing.maximalIdeal O)] {ϖ : O} (hϖ0 : ϖ ≠ 0)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) (E : Ideal S) [E.IsMaximal] {e : ℕ}
    (he : (IsLocalRing.maximalIdeal O).map (algebraMap O S) ≤ E ^ e) {y : S} {k : ℕ} (hk : 1 ≤ k)
    (hy : ∀ s : S, Algebra.trace O S (y * s) ∈ IsLocalRing.maximalIdeal O ^ k) :
    y ∈ E ^ ((k - 1) * e + 1) := by
  classical
  by_contra hyE
  have hy0 : y ≠ 0 := by rintro rfl; exact hyE (zero_mem _)
  obtain ⟨c, hc, J, hEJ, hIJ⟩ := exists_map_maximalIdeal_eq_pow_mul (S := S)
    (by rwa [hϖ, Ne, Ideal.span_singleton_eq_bot]) E
  set I := (IsLocalRing.maximalIdeal O).map (algebraMap O S) with hIdef
  have hyS0 : Ideal.span {y} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨r, Jy, hEJy, hyJ⟩ : ∃ (r : ℕ) (J : Ideal S), E ⊔ J = ⊤ ∧ Ideal.span {y} = E ^ r * J := by
    obtain ⟨J, hEJ, hIJ⟩ := Ideal.eq_prime_pow_mul_coprime hyS0 E
    exact ⟨_, J, hEJ, hIJ⟩
  have hyEr : y ∈ E ^ r := by
    have h1 : y ∈ Ideal.span {y} := Ideal.mem_span_singleton_self y
    rw [hyJ] at h1
    exact (Ideal.mul_le_left (I := E ^ r) (J := Jy)) h1
  have hr : r ≤ (k - 1) * e := by
    by_contra hr
    push Not at hr
    exact hyE ((Ideal.pow_le_pow_right (I := E) hr) hyEr)
  -- the CRT element
  have hcop : IsCoprime (E ^ c) (J * Jy) :=
    ((Ideal.isCoprime_iff_sup_eq.mpr hEJ).mul_right (Ideal.isCoprime_iff_sup_eq.mpr hEJy)).pow_left
  obtain ⟨a, ha, z, hz, haz⟩ := Ideal.isCoprime_iff_exists.mp hcop
  -- `ϖ^{k-1} z` is a multiple of `y`
  have hϖE : algebraMap O S ϖ ^ (k - 1) ∈ E ^ r := by
    have h1 : algebraMap O S ϖ ∈ E ^ e :=
      he (Ideal.mem_map_of_mem _ (hϖ ▸ Ideal.mem_span_singleton_self ϖ))
    have h2 : algebraMap O S ϖ ^ (k - 1) ∈ E ^ (e * (k - 1)) := by
      rw [pow_mul]; exact Ideal.pow_mem_pow h1 _
    exact Ideal.pow_le_pow_right (by rwa [mul_comm]) h2
  have hmem : algebraMap O S ϖ ^ (k - 1) * z ∈ Ideal.span {y} := by
    have hc1 : IsCoprime (E ^ r) Jy := (Ideal.isCoprime_iff_sup_eq.mpr hEJy).pow_left
    rw [hyJ, Ideal.mul_eq_inf_of_coprime (Ideal.isCoprime_iff_sup_eq.mp hc1)]
    exact ⟨Ideal.mul_mem_right _ _ hϖE,
      Ideal.mul_mem_left _ _ ((Ideal.mul_le_right (I := J) (J := Jy)) hz)⟩
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hmem
  have htr := hy s
  rw [mul_comm y s, hs, ← map_pow, ← Algebra.smul_def, LinearMap.map_smul_of_tower, smul_eq_mul,
    hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at htr
  obtain ⟨t, ht⟩ := htr
  have htz : Algebra.trace O S z = ϖ * t := by
    have : ϖ ^ (k - 1) * Algebra.trace O S z = ϖ ^ (k - 1) * (ϖ * t) := by
      rw [ht, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hk]
    exact mul_left_cancel₀ (pow_ne_zero _ hϖ0) this
  have hzm : Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) (Algebra.trace O S z) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, htz, hϖ]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ)
  rw [← Algebra.trace_quotient_mk] at hzm
  -- the trace on `S / I = S / E^c × S / J`
  have hle1 : IsLocalRing.maximalIdeal O ≤ (E ^ c * J).comap (algebraMap O S) := by
    rw [← hIJ, ← Ideal.map_le_iff_le_comap]
  have hle2 : IsLocalRing.maximalIdeal O ≤ (E ^ c).comap (algebraMap O S) :=
    hle1.trans (Ideal.comap_mono (Ideal.mul_le_left (I := E ^ c) (J := J)))
  have hle3 : IsLocalRing.maximalIdeal O ≤ J.comap (algebraMap O S) :=
    hle1.trans (Ideal.comap_mono (Ideal.mul_le_right (I := E ^ c) (J := J)))
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal O)
  letI : Algebra (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ E ^ c) :=
    Ideal.Quotient.algebraQuotientOfLEComap hle2
  letI : Algebra (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap hle3
  haveI : IsScalarTower O (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ E ^ c) := .of_algebraMap_eq' rfl
  haveI : IsScalarTower O (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ J) := .of_algebraMap_eq' rfl
  haveI : Module.Finite (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ E ^ c) :=
    Module.Finite.of_restrictScalars_finite O _ _
  haveI : Module.Finite (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ J) :=
    Module.Finite.of_restrictScalars_finite O _ _
  have hcopEJ : IsCoprime (E ^ c) J := (Ideal.isCoprime_iff_sup_eq.mpr hEJ).pow_left
  let eqv : (S ⧸ I) ≃ₐ[O ⧸ IsLocalRing.maximalIdeal O] ((S ⧸ E ^ c) × S ⧸ J) :=
    { __ := (Ideal.quotEquivOfEq hIJ).trans (Ideal.quotientMulEquivQuotientProd _ _ hcopEJ),
      commutes' := Quotient.ind fun _ ↦ rfl }
  rw [← Algebra.trace_eq_of_algEquiv eqv, Algebra.trace_prod_apply] at hzm
  have h1 : (eqv (Ideal.Quotient.mk I z)).1 = 1 := by
    change Ideal.Quotient.mk (E ^ c) z = 1
    rw [← map_one (Ideal.Quotient.mk (E ^ c)), Ideal.Quotient.eq, ← haz]
    simpa using ha
  have h2 : (eqv (Ideal.Quotient.mk I z)).2 = 0 := by
    change Ideal.Quotient.mk J z = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (Ideal.mul_le_left (I := J) (J := Jy)) hz
  rw [h1, h2, map_zero, add_zero,
    ← map_one (algebraMap (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ E ^ c)),
    Algebra.trace_algebraMap, nsmul_eq_mul, mul_one, Nat.cast_eq_zero] at hzm
  haveI : Nontrivial (S ⧸ E ^ c) := Ideal.Quotient.nontrivial_iff.mpr (by
    intro htop
    rw [Ideal.pow_eq_top_iff] at htop
    exact (Ideal.IsMaximal.ne_top inferInstance) (htop.resolve_right hc))
  exact (Module.finrank_pos (R := O ⧸ IsLocalRing.maximalIdeal O) (M := S ⧸ E ^ c)).ne' hzm

/-- **The trace on a nilpotent thickening of a separable field extension.** Let `𝔄` be a finite
commutative `κ`-algebra and `π : 𝔄 → L` a surjective `κ`-algebra map onto a finite separable field
extension, with nilpotent kernel. Then there is `N > 0` with `Tr_{𝔄/κ}(a) = N · Tr_{L/κ}(π a)`. -/
private theorem exists_trace_eq_nsmul_trace_of_isNilpotent_ker {κ 𝔄 L : Type*} [Field κ]
    [CommRing 𝔄]
    [Field L] [Algebra κ 𝔄] [Algebra κ L] [Module.Finite κ 𝔄] [Algebra.IsSeparable κ L]
    [FiniteDimensional κ L] (π : 𝔄 →ₐ[κ] L) (hπ : Function.Surjective π)
    (hnil : IsNilpotent (RingHom.ker π)) :
    ∃ N : ℕ, 0 < N ∧ ∀ a : 𝔄, Algebra.trace κ 𝔄 a = N • Algebra.trace κ L (π a) := by
  classical
  -- a section of `π`
  haveI : Algebra.FormallyEtale κ L := Algebra.FormallyEtale.of_isSeparable κ L
  haveI : Algebra.FormallySmooth κ L := inferInstance
  let e : (𝔄 ⧸ RingHom.ker π) ≃ₐ[κ] L := Ideal.quotientKerAlgEquivOfSurjective hπ
  let s : L →ₐ[κ] 𝔄 := Algebra.FormallySmooth.lift (RingHom.ker π) hnil e.symm.toAlgHom
  have hs : ∀ ℓ, π (s ℓ) = ℓ := by
    intro ℓ
    have h := Algebra.FormallySmooth.mk_lift (RingHom.ker π) hnil e.symm.toAlgHom ℓ
    have h' := congrArg e h
    have h2 : e ((e.symm : L →ₐ[κ] 𝔄 ⧸ RingHom.ker π) ℓ) = ℓ := e.apply_symm_apply ℓ
    rw [h2] at h'
    exact (show π (s ℓ) = e (Ideal.Quotient.mk _ (s ℓ)) from rfl).trans h'
  letI : Algebra L 𝔄 := s.toRingHom.toAlgebra
  haveI : IsScalarTower κ L 𝔄 := .of_algebraMap_eq fun c => (s.commutes c).symm
  haveI : Module.Finite L 𝔄 := Module.Finite.of_restrictScalars_finite κ L 𝔄
  haveI : Nontrivial 𝔄 := π.toRingHom.domain_nontrivial
  refine ⟨Module.finrank L 𝔄, Module.finrank_pos, fun a => ?_⟩
  have hdiff : a - s (π a) ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_sub, hs, sub_self]
  have hnilp : IsNilpotent (a - s (π a)) := by
    obtain ⟨k, hk⟩ := hnil
    refine ⟨k, ?_⟩
    have : (a - s (π a)) ^ k ∈ RingHom.ker π ^ k := Ideal.pow_mem_pow hdiff k
    rw [hk] at this
    simpa using this
  have htr0 : Algebra.trace κ 𝔄 (a - s (π a)) = 0 := by
    rw [Algebra.trace_apply]
    exact (LinearMap.isNilpotent_trace_of_isNilpotent (hnilp.map (Algebra.lmul κ 𝔄))).eq_zero
  have hsa : Algebra.trace κ 𝔄 (s (π a)) = Module.finrank L 𝔄 • Algebra.trace κ L (π a) := by
    rw [← Algebra.trace_trace (S := L)]
    change Algebra.trace κ L (Algebra.trace L 𝔄 (algebraMap L 𝔄 (π a))) = _
    rw [Algebra.trace_algebraMap, map_nsmul]
  rw [← hsa, ← sub_eq_zero, ← map_sub, htr0]

/-- In a finite algebra over a field, the trace vanishes on the Jacobson radical. -/
theorem trace_eq_zero_of_mem_jacobson {κ 𝔄 : Type*} [Field κ] [CommRing 𝔄] [Algebra κ 𝔄]
    [Module.Finite κ 𝔄] {a : 𝔄} (ha : a ∈ Ideal.jacobson ⊥) : Algebra.trace κ 𝔄 a = 0 := by
  haveI : IsArtinianRing 𝔄 := IsArtinianRing.of_finite κ 𝔄
  have hnil : IsNilpotent a := by
    rw [IsArtinianRing.jacobson_eq_radical, Ideal.mem_radical_iff] at ha
    obtain ⟨n, hn⟩ := ha
    exact ⟨n, by simpa using hn⟩
  rw [Algebra.trace_apply]
  exact (LinearMap.isNilpotent_trace_of_isNilpotent (hnil.map (Algebra.lmul κ 𝔄))).eq_zero

/-- **The trace modulo the maximal ideal, near one prime.** Let `S` be a Dedekind domain, free of
finite rank over a local domain `O` with residue field of characteristic zero, and `P` a maximal
ideal of `S`. There is `N > 0` such that for every `y ∈ S` lying in all other maximal ideals,
`Tr_{S/O}(y) ≡ N · Tr_{(S/P)/κ}(y mod P)` modulo `𝔪_O`. -/
private theorem exists_mk_trace_eq_nsmul {O S : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
    [CommRing S] [IsDomain S] [IsDedekindDomain S] [Algebra O S] [Module.Free O S]
    [Module.Finite O S] [CharZero (O ⧸ IsLocalRing.maximalIdeal O)]
    (hO : IsLocalRing.maximalIdeal O ≠ ⊥)
    (P : Ideal S) [P.IsMaximal] (hP : IsLocalRing.maximalIdeal O ≤ P.comap (algebraMap O S)) :
    letI : Algebra (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ P) :=
      Ideal.Quotient.algebraQuotientOfLEComap hP
    ∃ N : ℕ, 0 < N ∧ ∀ y : S, (∀ E : Ideal S, E.IsMaximal → E ≠ P → y ∈ E) →
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) (Algebra.trace O S y) =
        N • Algebra.trace (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ P) (Ideal.Quotient.mk P y) := by
  classical
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal O)
  letI : Algebra (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ P) :=
    Ideal.Quotient.algebraQuotientOfLEComap hP
  obtain ⟨c, hc, J, hPJ, hIJ⟩ := exists_map_maximalIdeal_eq_pow_mul (S := S) hO P
  set I := (IsLocalRing.maximalIdeal O).map (algebraMap O S) with hIdef
  have hle1 : IsLocalRing.maximalIdeal O ≤ (P ^ c * J).comap (algebraMap O S) := by
    rw [← hIJ, ← Ideal.map_le_iff_le_comap]
  have hle2 : IsLocalRing.maximalIdeal O ≤ (P ^ c).comap (algebraMap O S) :=
    hle1.trans (Ideal.comap_mono (Ideal.mul_le_left (I := P ^ c) (J := J)))
  have hle3 : IsLocalRing.maximalIdeal O ≤ J.comap (algebraMap O S) :=
    hle1.trans (Ideal.comap_mono (Ideal.mul_le_right (I := P ^ c) (J := J)))
  letI : Algebra (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ P ^ c) :=
    Ideal.Quotient.algebraQuotientOfLEComap hle2
  letI : Algebra (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap hle3
  haveI : IsScalarTower O (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ P ^ c) := .of_algebraMap_eq' rfl
  haveI : IsScalarTower O (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ J) := .of_algebraMap_eq' rfl
  haveI : IsScalarTower O (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ P) := .of_algebraMap_eq' rfl
  haveI : Module.Finite (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ P ^ c) :=
    Module.Finite.of_restrictScalars_finite O _ _
  haveI : Module.Finite (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ J) :=
    Module.Finite.of_restrictScalars_finite O _ _
  haveI : Module.Finite (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ P) :=
    Module.Finite.of_restrictScalars_finite O _ _
  letI := Ideal.Quotient.field P
  -- the factor map `S / P^c → S / P`
  have hPc : P ^ c ≤ P := Ideal.pow_le_self hc
  let π : (S ⧸ P ^ c) →ₐ[O ⧸ IsLocalRing.maximalIdeal O] (S ⧸ P) :=
    { Ideal.Quotient.factor hPc with commutes' := Quotient.ind fun _ ↦ rfl }
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective hPc
  have hnil : IsNilpotent (RingHom.ker π) := by
    refine ⟨c, ?_⟩
    have hker : RingHom.ker π = P.map (Ideal.Quotient.mk (P ^ c)) := by
      ext x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [RingHom.mem_ker, Ideal.mem_quotient_iff_mem hPc]
      change Ideal.Quotient.mk P s = 0 ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem]
    rw [hker, ← Ideal.map_pow, Ideal.map_quotient_self, Ideal.zero_eq_bot]
  obtain ⟨N, hN, hNtr⟩ := exists_trace_eq_nsmul_trace_of_isNilpotent_ker π hπ hnil
  refine ⟨N, hN, fun y hy => ?_⟩
  have hcopPJ : IsCoprime (P ^ c) J := (Ideal.isCoprime_iff_sup_eq.mpr hPJ).pow_left
  let eqv : (S ⧸ I) ≃ₐ[O ⧸ IsLocalRing.maximalIdeal O] ((S ⧸ P ^ c) × S ⧸ J) :=
    { __ := (Ideal.quotEquivOfEq hIJ).trans (Ideal.quotientMulEquivQuotientProd _ _ hcopPJ),
      commutes' := Quotient.ind fun _ ↦ rfl }
  rw [← Algebra.trace_quotient_mk, ← Algebra.trace_eq_of_algEquiv eqv, Algebra.trace_prod_apply]
  have h2 : Algebra.trace (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ J)
      (eqv (Ideal.Quotient.mk I y)).2 = 0 := by
    apply trace_eq_zero_of_mem_jacobson
    change Ideal.Quotient.mk J y ∈ _
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro M ⟨-, hM⟩
    have hE : (M.comap (Ideal.Quotient.mk J)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have hJE : J ≤ M.comap (Ideal.Quotient.mk J) := by
      intro a ha
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact zero_mem _
    have hne : M.comap (Ideal.Quotient.mk J) ≠ P := by
      rintro h
      exact not_le_of_sup_eq_top hPJ (h ▸ hJE)
    exact hy _ hE hne
  rw [h2, add_zero]
  exact hNtr _

/-- `exists_mk_trace_eq_nsmul` for an ideal `I` equal to the maximal ideal. -/
private theorem exists_mk_trace_eq_nsmul' {O S : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
    [CommRing S] [IsDomain S] [IsDedekindDomain S] [Algebra O S] [Module.Free O S]
    [Module.Finite O S] (I : Ideal O) (hI : I = IsLocalRing.maximalIdeal O) [CharZero (O ⧸ I)]
    (hO : I ≠ ⊥) (P : Ideal S) [P.IsMaximal] (hP : I ≤ P.comap (algebraMap O S)) :
    letI : Algebra (O ⧸ I) (S ⧸ P) := Ideal.Quotient.algebraQuotientOfLEComap hP
    ∃ N : ℕ, 0 < N ∧ ∀ y : S, (∀ E : Ideal S, E.IsMaximal → E ≠ P → y ∈ E) →
      Ideal.Quotient.mk I (Algebra.trace O S y) =
        N • Algebra.trace (O ⧸ I) (S ⧸ P) (Ideal.Quotient.mk P y) := by
  subst hI
  exact exists_mk_trace_eq_nsmul hO P hP

/-- **An element of one maximal ideal and of all the others with trace in `𝔪`.** Let `S` be free
of finite rank over a local ring `O`, `Q` a maximal ideal of `S` and `t ∈ Q`. There is `a ∉ Q` with
`a t` in every maximal ideal of `S`, so that `Tr_{S/O}(a t s) ∈ 𝔪_O` for every `s`. -/
private theorem exists_not_mem_trace_mul_mem {O S : Type*} [CommRing O] [IsLocalRing O]
    [CommRing S] [Algebra O S] [Module.Free O S] [Module.Finite O S] (Q : Ideal S) [Q.IsMaximal]
    {t : S} (ht : t ∈ Q) :
    ∃ a : S, a ∉ Q ∧ ∀ s : S, Algebra.trace O S (a * t * s) ∈ IsLocalRing.maximalIdeal O := by
  classical
  set I := (IsLocalRing.maximalIdeal O).map (algebraMap O S) with hIdef
  haveI : Algebra.IsIntegral O S := Algebra.IsIntegral.of_finite O S
  -- every maximal ideal of `S` contains `I`
  have hIM : ∀ M : Ideal S, M.IsMaximal → I ≤ M := fun M _ => map_maximalIdeal_le M
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal O)
  haveI : Module.Finite (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ I) :=
    Module.Finite.of_restrictScalars_finite O _ _
  haveI : IsArtinianRing (S ⧸ I) := IsArtinianRing.of_finite (O ⧸ IsLocalRing.maximalIdeal O) _
  -- the finitely many maximal ideals other than `Q`
  have hfin : {M : Ideal S | M.IsMaximal ∧ M ≠ Q}.Finite := by
    refine Set.Finite.of_finite_image (f := Ideal.map (Ideal.Quotient.mk I)) ?_ ?_
    · refine (IsArtinianRing.setOf_isMaximal_finite (S ⧸ I)).subset ?_
      rintro _ ⟨M, ⟨hM, -⟩, rfl⟩
      haveI := hM
      exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hIM M hM)
    · intro M hM M' hM' h
      have h1 := congrArg (Ideal.comap (Ideal.Quotient.mk I)) h
      rwa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
        Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
        sup_eq_left.mpr (hIM M hM.1), sup_eq_left.mpr (hIM M' hM'.1)] at h1
  set s := hfin.toFinset
  have hnle : ¬ s.inf id ≤ Q := by
    intro h
    obtain ⟨M, hMs, hMQ⟩ := (Ideal.IsPrime.inf_le' (Ideal.IsMaximal.isPrime inferInstance)).mp h
    rw [Set.Finite.mem_toFinset] at hMs
    exact hMs.2 (hMs.1.eq_of_le (Ideal.IsMaximal.ne_top inferInstance) hMQ)
  obtain ⟨a, ha, haQ⟩ := SetLike.not_le_iff_exists.mp hnle
  refine ⟨a, haQ, fun r => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_mk]
  apply trace_eq_zero_of_mem_jacobson
  rw [Ideal.jacobson, Ideal.mem_sInf]
  rintro M ⟨-, hM⟩
  have hE : (M.comap (Ideal.Quotient.mk I)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  change a * t * r ∈ M.comap (Ideal.Quotient.mk I)
  apply Ideal.mul_mem_right
  by_cases hMQ : M.comap (Ideal.Quotient.mk I) = Q
  · rw [hMQ]; exact Ideal.mul_mem_left _ _ ht
  · have hMs : M.comap (Ideal.Quotient.mk I) ∈ s := by
      rw [Set.Finite.mem_toFinset]; exact ⟨hE, hMQ⟩
    exact Ideal.mul_mem_right _ _ (Finset.inf_le (f := id) hMs ha)

/-- **The tame bound on the codifferent, divided out.** In the situation of
`mem_pow_of_trace_mul_mem`, if `Tr(y s) ∈ 𝔪_O ^ k` for all `s` then `y s = ϖ ^ (k - 1) a` for some
`s ∉ E` and `a ∈ E`: the quotient `y / ϖ ^ (k - 1)` lies in the maximal ideal of `S_E`. -/
theorem exists_mul_eq_pow_mul_of_trace_mul_mem {O S : Type*} [CommRing O] [IsDomain O]
    [IsLocalRing O] [CommRing S] [IsDomain S] [IsDedekindDomain S] [Algebra O S]
    [Module.Free O S] [Module.Finite O S] [CharZero (O ⧸ IsLocalRing.maximalIdeal O)] {ϖ : O}
    (hϖ0 : ϖ ≠ 0) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) (E : Ideal S) [E.IsMaximal]
    {y : S}
    {k : ℕ} (hk : 1 ≤ k)
    (hy : ∀ s : S, Algebra.trace O S (y * s) ∈ IsLocalRing.maximalIdeal O ^ k) :
    ∃ s : S, s ∉ E ∧ ∃ a ∈ E, y * s = algebraMap O S ϖ ^ (k - 1) * a := by
  classical
  obtain ⟨c, -, J, hEJ, hIJ⟩ := exists_map_maximalIdeal_eq_pow_mul (S := S)
    (by rwa [hϖ, Ne, Ideal.span_singleton_eq_bot]) E
  set I := (IsLocalRing.maximalIdeal O).map (algebraMap O S) with hIdef
  have hyE := mem_pow_of_trace_mul_mem hϖ0 hϖ E (e := c)
    (by rw [← hIdef, hIJ]; exact Ideal.mul_le_left (I := E ^ c) (J := J)) hk hy
  -- an element of `J ^ (k - 1)` outside `E`
  have hJE : ¬ J ^ (k - 1) ≤ E := fun h =>
    not_le_of_sup_eq_top hEJ ((Ideal.IsMaximal.isPrime inferInstance).le_of_pow_le h)
  obtain ⟨s, hsJ, hsE⟩ := SetLike.not_le_iff_exists.mp hJE
  refine ⟨s, hsE, ?_⟩
  have hmem : y * s ∈ E * Ideal.span {algebraMap O S ϖ ^ (k - 1)} := by
    have h1 : y * s ∈ E ^ ((k - 1) * c + 1) * J ^ (k - 1) := Ideal.mul_mem_mul hyE hsJ
    have h2 : E ^ ((k - 1) * c + 1) * J ^ (k - 1) =
        E * Ideal.span {algebraMap O S ϖ ^ (k - 1)} := by
      have hIϖ : I = Ideal.span {algebraMap O S ϖ} := by
        rw [hIdef, hϖ, Ideal.map_span, Set.image_singleton]
      rw [← Ideal.span_singleton_pow, ← hIϖ, hIJ, mul_pow, ← pow_mul, pow_succ', mul_assoc,
        mul_comm c]
    rwa [h2] at h1
  rw [mul_comm, Ideal.mem_span_singleton_mul] at hmem
  obtain ⟨a, ha, hya⟩ := hmem
  exact ⟨a, ha, by rw [← hya]⟩

open nonZeroDivisors in
/-- **Representing a functional by the trace form.** Let `B` be free of finite rank over a domain
`C`, with fraction fields `K / F` separable. Every `C`-linear `φ : B → C` is
`b ↦ Tr_{K/F}(f b)` for some `f ∈ K`. -/
private theorem exists_trace_mul_eq {C B F K : Type*} [CommRing C] [IsDomain C] [CommRing B]
    [Algebra C B] [Module.Free C B] [Module.Finite C B] [Field F] [Algebra C F]
    [IsFractionRing C F] [Field K] [Algebra B K] [Algebra F K] [Algebra C K]
    [IsScalarTower C F K] [IsScalarTower C B K]
    [IsLocalization (Algebra.algebraMapSubmonoid B C⁰) K] [Algebra.IsSeparable F K]
    [FiniteDimensional F K] (φ : B →ₗ[C] C) :
    ∃ f : K, ∀ b : B, Algebra.trace F K (f * algebraMap B K b) = algebraMap C F (φ b) := by
  classical
  let bas := Module.Free.chooseBasis C B
  let bK : Module.Basis _ F K := bas.localizationLocalization F C⁰ K
  let φF : K →ₗ[F] F := bK.constr F fun i => algebraMap C F (φ (bas i))
  have hnd := traceForm_nondegenerate F K
  refine ⟨((Algebra.traceForm F K).toDual hnd).symm φF, fun b => ?_⟩
  have h1 := LinearMap.BilinForm.apply_toDual_symm_apply (B := Algebra.traceForm F K) (hB := hnd)
    φF (algebraMap B K b)
  rw [Algebra.traceForm_apply] at h1
  rw [h1]
  -- `φF` extends `φ`
  have hlin : (φF.restrictScalars C) ∘ₗ (IsScalarTower.toAlgHom C B K).toLinearMap =
      (Algebra.linearMap C F) ∘ₗ φ := by
    refine bas.ext fun i => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      IsScalarTower.coe_toAlgHom', LinearMap.restrictScalars_apply, Algebra.linearMap_apply, φF]
    rw [← Module.Basis.localizationLocalization_apply F C⁰ K bas i]
    exact bK.constr_basis F _ i
  exact LinearMap.congr_fun hlin b

open nonZeroDivisors in
/-- The localization of a Noetherian domain at a nonzero principal prime `(π)` is a discrete
valuation ring. -/
private theorem isDiscreteValuationRing_localization {C : Type*} [CommRing C] [IsDomain C]
    [IsNoetherianRing C] (q : Ideal C) [q.IsPrime] {π : C} (hπ : q = Ideal.span {π})
    (hπ0 : π ≠ 0) : IsDiscreteValuationRing (Localization.AtPrime q) := by
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime q) =
      Ideal.span {algebraMap C (Localization.AtPrime q) π} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal,
      congrArg (Ideal.map (algebraMap C (Localization.AtPrime q))) hπ,
      Ideal.map_span, Set.image_singleton]
  have hne : algebraMap C (Localization.AtPrime q) π ≠ 0 := fun h =>
    hπ0 ((IsLocalization.injective (Localization.AtPrime q)
      q.primeCompl_le_nonZeroDivisors) (by rw [h, map_zero]))
  have hnf : ¬ IsField (Localization.AtPrime q) := by
    rwa [IsLocalRing.isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
  have hp : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).IsPrincipal := ⟨⟨_, hmax⟩⟩
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q) hnf).out 1 5).mpr hp

open nonZeroDivisors in
/-- The localization data at a height-one prime: `C_q` is local with maximal ideal `(π)`, and
`B_q` is a Dedekind domain, free of finite rank over it. -/
private theorem localization_facts {C B : Type*} [CommRing C] [IsDomain C] [IsNoetherianRing C]
    [IsIntegrallyClosed C] [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    [Algebra C B] [Module.Free C B] [Module.Finite C B] [FaithfulSMul C B]
    (q : Ideal C) [q.IsPrime] {π : C} (hπ : q = Ideal.span {π}) (hπ0 : π ≠ 0) :
    let O := Localization.AtPrime q
    let S := Localization (Algebra.algebraMapSubmonoid B q.primeCompl)
    IsLocalRing.maximalIdeal O = Ideal.span {algebraMap C O π} ∧ algebraMap C O π ≠ 0 ∧
      IsDomain S ∧ Module.Free O S ∧ Module.Finite O S ∧ IsDedekindDomain S := by
  intro O S
  have hinj : Function.Injective (algebraMap C B) := FaithfulSMul.algebraMap_injective C B
  have hle : Algebra.algebraMapSubmonoid B q.primeCompl ≤ B⁰ := Submonoid.map_le_of_le_comap _
    (q.primeCompl_le_nonZeroDivisors.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Localization.AtPrime.map_eq_maximalIdeal, congrArg (Ideal.map (algebraMap C O)) hπ,
      Ideal.map_span, Set.image_singleton]
  · intro h
    exact hπ0 ((IsLocalization.injective O q.primeCompl_le_nonZeroDivisors) (by rw [h, map_zero]))
  · exact IsLocalization.isDomain_localization hle
  · exact Module.Free.of_basis ((Module.Free.chooseBasis C B).localizationLocalization O
      q.primeCompl S)
  · exact Module.Finite.of_basis ((Module.Free.chooseBasis C B).localizationLocalization O
      q.primeCompl S)
  · haveI : IsDomain S := IsLocalization.isDomain_localization hle
    haveI : IsNoetherianRing S :=
      IsLocalization.isNoetherianRing (Algebra.algebraMapSubmonoid B q.primeCompl) S inferInstance
    haveI : IsIntegrallyClosed S :=
      isIntegrallyClosed_of_isLocalization (R := B) (S := S) _ hle
    haveI : IsDiscreteValuationRing O := isDiscreteValuationRing_localization q hπ hπ0
    haveI : Module.Finite O S := Module.Finite.of_basis
      ((Module.Free.chooseBasis C B).localizationLocalization O q.primeCompl S)
    haveI : Algebra.IsIntegral O S := Algebra.IsIntegral.of_finite O S
    haveI : Ring.DimensionLEOne S := Ring.DimensionLEOne.of_isIntegral (R := O) S
    exact { }

open nonZeroDivisors in
/-- **The tame codifferent bound at a height-one prime, over the base.** Let `B` be a Noetherian
normal domain, free of finite rank over a Noetherian normal domain `C`, `q = (π) ⊆ C` a nonzero
prime and `E ⊆ B` a prime over it, with `C_q` of residue characteristic zero. If `y₀ ∈ B` and
`δ ≠ 0` satisfy `Tr(y₀ b) ∈ δ C` for all `b ∈ B`, then `y₀ π s = δ a` for some `s ∉ E`, `a ∈ E`. -/
private theorem exists_mul_mul_eq_of_trace_mem {C B : Type*} [CommRing C] [IsDomain C]
    [IsNoetherianRing C] [IsIntegrallyClosed C] [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] [Algebra C B] [Module.Free C B] [Module.Finite C B] [FaithfulSMul C B]
    (q : Ideal C) [q.IsPrime] {π : C} (hπ : q = Ideal.span {π}) (hπ0 : π ≠ 0)
    [CharZero (Localization.AtPrime q ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime q))]
    (E : Ideal B) [E.IsPrime] (hE : E.comap (algebraMap C B) = q) {y₀ : B} {δ : C} (hδ : δ ≠ 0)
    (hy : ∀ b : B, ∃ c : C, Algebra.trace C B (y₀ * b) = δ * c) :
    ∃ s : B, s ∉ E ∧ ∃ a ∈ E, y₀ * algebraMap C B π * s = algebraMap C B δ * a := by
  classical
  let O := Localization.AtPrime q
  let S := Localization (Algebra.algebraMapSubmonoid B q.primeCompl)
  obtain ⟨hmax, hπO, hSdom, hfree, hfin, hded⟩ := localization_facts (B := B) q hπ hπ0
  haveI := isDiscreteValuationRing_localization q hπ hπ0
  -- `δ = π ^ m · c₁` with `c₁ ∉ q`
  have hπu : ¬ IsUnit π := fun h => (Ideal.IsPrime.ne_top (inferInstance : q.IsPrime))
    (by rwa [hπ, Ideal.span_singleton_eq_top])
  obtain ⟨m, c₁, hc₁d, hδm⟩ := WfDvdMonoid.max_power_factor' hδ hπu
  have hc₁ : c₁ ∉ q := by rw [hπ, Ideal.mem_span_singleton]; exact hc₁d
  have hinj : Function.Injective (algebraMap C B) := FaithfulSMul.algebraMap_injective C B
  set M := Algebra.algebraMapSubmonoid B q.primeCompl with hMdef
  have hMle : M ≤ B⁰ := Submonoid.map_le_of_le_comap _
    (q.primeCompl_le_nonZeroDivisors.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj))
  have hιinj : Function.Injective (algebraMap B S) := IsLocalization.injective S hMle
  have hMdisj : Disjoint (M : Set B) (E : Set B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨t, ht, rfl⟩ htE
    exact ht (by rwa [← hE])
  haveI hE'p : (E.map (algebraMap B S)).IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M S E
    inferInstance hMdisj
  have hπE : algebraMap C B π ∈ E := by
    rw [← Ideal.mem_comap, hE, hπ]; exact Ideal.mem_span_singleton_self π
  have hE'0 : E.map (algebraMap B S) ≠ ⊥ := by
    intro h
    have : algebraMap B S (algebraMap C B π) ∈ E.map (algebraMap B S) := Ideal.mem_map_of_mem _ hπE
    rw [h, Ideal.mem_bot, map_eq_zero_iff _ hιinj, map_eq_zero_iff _ hinj] at this
    exact hπ0 this
  haveI hE'm : (E.map (algebraMap B S)).IsMaximal := hE'p.isMaximal hE'0
  -- the trace condition in `S`
  have htow : ∀ c : C, algebraMap O S (algebraMap C O c) = algebraMap B S (algebraMap C B c) :=
    fun c => by rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hyS : ∀ s : S, Algebra.trace O S (algebraMap B S (y₀ * algebraMap C B π) * s) ∈
      IsLocalRing.maximalIdeal O ^ (m + 1) := by
    intro s
    obtain ⟨⟨b, t⟩, hbt⟩ := IsLocalization.surj M s
    simp only at hbt
    obtain ⟨t₀, ht₀, ht₀e⟩ := t.2
    obtain ⟨c', hc'⟩ := hy b
    have htr : Algebra.trace C B (y₀ * algebraMap C B π * b) = π ^ (m + 1) * (c₁ * c') := by
      have h1 : y₀ * algebraMap C B π * b = π • (y₀ * b) := by rw [Algebra.smul_def]; ring
      rw [h1, LinearMap.map_smul_of_tower, hc', smul_eq_mul, hδm]
      ring
    have hu : IsUnit (algebraMap C O t₀) := IsLocalization.map_units O ⟨t₀, ht₀⟩
    have hx : algebraMap C O t₀ • (algebraMap B S (y₀ * algebraMap C B π) * s) =
        algebraMap B S (y₀ * algebraMap C B π * b) := by
      rw [Algebra.smul_def, htow, ht₀e, mul_comm, mul_assoc, hbt, ← map_mul]
    have key := congrArg (Algebra.trace O S) hx
    rw [LinearMap.map_smul_of_tower, smul_eq_mul,
      Algebra.trace_localization (R := C) (Rₘ := O) (Sₘ := S) q.primeCompl, htr] at key
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨hu.unit⁻¹ * algebraMap C O (c₁ * c'), ?_⟩
    rw [← map_pow, mul_left_comm, ← map_mul, ← key, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  haveI : IsDomain S := hSdom
  haveI : IsDedekindDomain S := hded
  haveI : Module.Free O S := hfree
  haveI : Module.Finite O S := hfin
  obtain ⟨s', hs'E, a', ha'E, hya⟩ := exists_mul_eq_pow_mul_of_trace_mul_mem hπO hmax
    (E.map (algebraMap B S)) (k := m + 1) (by omega) hyS
  rw [Nat.add_sub_cancel, htow] at hya
  -- clearing denominators
  obtain ⟨⟨s₁, t₁⟩, hst⟩ := IsLocalization.surj M s'
  obtain ⟨⟨⟨a₁, ha₁⟩, t₂⟩, ht₂⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp ha'E
  simp only at hst ht₂
  have hunit : ∀ t : M, IsUnit (algebraMap B S (t : B)) := fun t => IsLocalization.map_units S t
  have hs₁ : s₁ ∉ E := by
    intro h
    apply hs'E
    have h1 : s' * algebraMap B S (t₁ : B) ∈ E.map (algebraMap B S) := by
      rw [hst]; exact Ideal.mem_map_of_mem _ h
    have h2 := Ideal.mul_mem_right (((hunit t₁).unit⁻¹ : Sˣ) : S) _ h1
    rwa [mul_assoc, IsUnit.mul_val_inv, mul_one] at h2
  obtain ⟨t₂₀, ht₂₀, ht₂e⟩ := t₂.2
  have ht₂E : (t₂ : B) ∉ E := fun h => ht₂₀ (by
    show t₂₀ ∈ q
    rwa [← hE, Ideal.mem_comap, ht₂e])
  have hc₁E : algebraMap C B c₁ ∉ E := fun h => hc₁ (by rwa [← hE, Ideal.mem_comap])
  have hEp : E.IsPrime := inferInstance
  refine ⟨s₁ * t₂ * algebraMap C B c₁, hEp.mul_notMem (hEp.mul_notMem hs₁ ht₂E) hc₁E,
    a₁ * t₁, Ideal.mul_mem_right _ _ ha₁, ?_⟩
  have hB : y₀ * algebraMap C B π * s₁ * t₂ = algebraMap C B π ^ m * a₁ * t₁ := by
    apply hιinj
    have h1 := congrArg (· * (algebraMap B S (t₁ : B) * algebraMap B S (t₂ : B))) hya
    simp only [map_mul, map_pow] at h1 ⊢
    rw [← hst, ← ht₂]
    linear_combination h1
  rw [hδm, map_mul, map_pow]
  linear_combination (algebraMap C B c₁) * hB

/-- **The lifted functional.** Let `B` be free of finite rank over `C`, `g ∈ C` with `C̄ = C/(g)`
local with maximal ideal `(w̄) ≠ 0`, and `p ⊆ B` a prime over `(g)` with `R = B/p` free of finite
rank over `C̄`. For `u ∈ R` with `Tr_{R/C̄}(u R) ⊆ 𝔪_{C̄}` there is a `C`-linear `φ : B → C` with
`φ(p) ⊆ (g)` and `w̄ · φ̄(b) = Tr_{R/C̄}(u b̄)`. -/
private theorem exists_linearMap_trace_eq {C B : Type*} [CommRing C] [CommRing B] [Algebra C B]
    [Module.Free C B] [Module.Finite C B] {g w : C} [IsDomain (C ⧸ Ideal.span {g})]
    [IsLocalRing (C ⧸ Ideal.span {g})]
    (hw : IsLocalRing.maximalIdeal (C ⧸ Ideal.span {g}) = Ideal.span {Ideal.Quotient.mk _ w})
    (hw0 : Ideal.Quotient.mk (Ideal.span {g}) w ≠ 0)
    (p : Ideal B) [p.IsPrime] (hp : Ideal.span {g} ≤ p.comap (algebraMap C B))
    (u : letI := Ideal.Quotient.algebraQuotientOfLEComap hp; B ⧸ p)
    (hu : letI := Ideal.Quotient.algebraQuotientOfLEComap hp
      ∀ r : B ⧸ p, Algebra.trace (C ⧸ Ideal.span {g}) (B ⧸ p) (u * r) ∈
        IsLocalRing.maximalIdeal (C ⧸ Ideal.span {g})) :
    letI := Ideal.Quotient.algebraQuotientOfLEComap hp
    ∃ φ : B →ₗ[C] C, (∀ b ∈ p, φ b ∈ Ideal.span {g}) ∧
      ∀ b : B, Ideal.Quotient.mk _ w * Ideal.Quotient.mk _ (φ b) =
        Algebra.trace (C ⧸ Ideal.span {g}) (B ⧸ p) (u * Ideal.Quotient.mk p b) := by
  classical
  letI := Ideal.Quotient.algebraQuotientOfLEComap hp
  set C' := C ⧸ Ideal.span {g}
  -- `ψ₀(r) = Tr(u r) / w̄`
  have hdiv : ∀ r : B ⧸ p, ∃ c : C', Ideal.Quotient.mk _ w * c =
      Algebra.trace C' (B ⧸ p) (u * r) := by
    intro r
    have := hu r
    rw [hw, Ideal.mem_span_singleton] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc.symm⟩
  choose ψ₀ hψ₀ using hdiv
  have hcancel : ∀ a b : C', Ideal.Quotient.mk _ w * a = Ideal.Quotient.mk _ w * b → a = b :=
    fun a b h => mul_left_cancel₀ hw0 h
  let ψ : (B ⧸ p) →ₗ[C'] C' :=
    { toFun := ψ₀
      map_add' := fun r s => hcancel _ _ (by rw [mul_add, hψ₀, hψ₀, hψ₀, mul_add, map_add])
      map_smul' := fun c r => hcancel _ _ (by
        rw [RingHom.id_apply, smul_eq_mul, mul_left_comm, hψ₀, hψ₀, mul_smul_comm,
          LinearMap.map_smul, smul_eq_mul]) }
  haveI : IsScalarTower C C' (B ⧸ p) := .of_algebraMap_eq' rfl
  let ψ' : B →ₗ[C] C' := (ψ.restrictScalars C) ∘ₗ
    (Ideal.Quotient.mkₐ C p).toLinearMap
  -- lift along a basis
  let bas := Module.Free.chooseBasis C B
  have hsurj : ∀ c : C', ∃ c' : C, Ideal.Quotient.mk _ c' = c := Ideal.Quotient.mk_surjective
  choose lift hlift using hsurj
  let φ : B →ₗ[C] C := bas.constr C fun i => lift (ψ' (bas i))
  have hφ : (Algebra.linearMap C C') ∘ₗ φ = ψ' := by
    refine bas.ext fun i => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, φ, Module.Basis.constr_basis,
      Algebra.linearMap_apply]
    exact hlift _
  have hφb : ∀ b, Ideal.Quotient.mk (Ideal.span {g}) (φ b) = ψ₀ (Ideal.Quotient.mk p b) :=
    fun b => LinearMap.congr_fun hφ b
  refine ⟨φ, fun b hb => ?_, fun b => ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, hφb, Ideal.Quotient.eq_zero_iff_mem.mpr hb]
    exact ψ.map_zero
  · rw [hφb, hψ₀]

open nonZeroDivisors in
/-- **The trace modulo a height-one prime `(g)`, near one prime above it.** Let `B` be a Noetherian
normal domain, free of finite rank over a Noetherian normal domain `C`, `(g)` a nonzero prime of
`C` with residue characteristic zero at its generic point, and `p` a prime of `B` over `(g)` with
`B / p` free of finite rank over `C / (g)`. There is `N > 0` such that
`Tr_{B/C}(y) ≡ N · Tr_{(B/p)/(C/(g))}(ȳ)` modulo `g` for every `y` in all other primes over
`(g)`. -/
theorem exists_mk_trace_eq_nsmul_of_comap_eq {C B : Type*} [CommRing C] [IsDomain C]
    [IsNoetherianRing C] [IsIntegrallyClosed C] [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] [Algebra C B] [Module.Free C B] [Module.Finite C B] [FaithfulSMul C B]
    (q : Ideal C) [q.IsPrime] {g : C} (hqdef : q = Ideal.span {g}) (hg0 : g ≠ 0)
    [CharZero (Localization.AtPrime q ⧸ q.map (algebraMap C (Localization.AtPrime q)))]
    (p : Ideal B) [p.IsPrime] (hp : p.comap (algebraMap C B) = q)
    [letI := Ideal.Quotient.algebraQuotientOfLEComap hp.ge; Module.Free (C ⧸ q) (B ⧸ p)]
    [letI := Ideal.Quotient.algebraQuotientOfLEComap hp.ge; Module.Finite (C ⧸ q) (B ⧸ p)] :
    letI := Ideal.Quotient.algebraQuotientOfLEComap hp.ge
    ∃ N : ℕ, 0 < N ∧ ∀ y : B, (∀ E : Ideal B, E.IsPrime →
      E.comap (algebraMap C B) = q → E ≠ p → y ∈ E) →
      Ideal.Quotient.mk q (Algebra.trace C B y) =
        N • Algebra.trace (C ⧸ q) (B ⧸ p) (Ideal.Quotient.mk p y) := by
  classical
  letI := Ideal.Quotient.algebraQuotientOfLEComap hp.ge
  let O := Localization.AtPrime q
  let S := Localization (Algebra.algebraMapSubmonoid B q.primeCompl)
  obtain ⟨hmax, hgO, hSdom, hfree, hfin, hded⟩ := localization_facts (B := B) q hqdef hg0
  haveI := isDiscreteValuationRing_localization q hqdef hg0
  haveI : IsDomain S := hSdom
  haveI : IsDedekindDomain S := hded
  haveI : Module.Free O S := hfree
  haveI : Module.Finite O S := hfin
  have hinj : Function.Injective (algebraMap C B) := FaithfulSMul.algebraMap_injective C B
  set M := Algebra.algebraMapSubmonoid B q.primeCompl with hMdef
  have hMle : M ≤ B⁰ := Submonoid.map_le_of_le_comap _
    (q.primeCompl_le_nonZeroDivisors.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj))
  have hιinj : Function.Injective (algebraMap B S) := IsLocalization.injective S hMle
  have hdisj : ∀ E : Ideal B, E.comap (algebraMap C B) = q → Disjoint (M : Set B) (E : Set B) := by
    intro E hE
    rw [Set.disjoint_left]
    rintro _ ⟨t, ht, rfl⟩ htE
    exact ht (by rwa [← hE])
  set I := q.map (algebraMap C O) with hIdef
  have hI : I = IsLocalRing.maximalIdeal O := Localization.AtPrime.map_eq_maximalIdeal
  have hI0 : I ≠ ⊥ := by
    rwa [hI, hmax, Ne, Ideal.span_singleton_eq_bot]
  set P := p.map (algebraMap B S) with hPdef
  haveI hPp : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M S p inferInstance
    (hdisj p hp)
  have hPcomap : P.comap (algebraMap B S) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint M S (I := p) inferInstance (hdisj p hp)
  have hP0 : P ≠ ⊥ := by
    intro h
    have hgp : algebraMap C B g ∈ p := by
      rw [← Ideal.mem_comap, hp, hqdef]; exact Ideal.mem_span_singleton_self g
    have : algebraMap B S (algebraMap C B g) ∈ P := Ideal.mem_map_of_mem _ hgp
    rw [h, Ideal.mem_bot, map_eq_zero_iff _ hιinj, map_eq_zero_iff _ hinj] at this
    exact hg0 this
  haveI hPm : P.IsMaximal := hPp.isMaximal hP0
  have hIP : I ≤ P.comap (algebraMap O S) := by
    rw [hIdef, Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq C B S, ← Ideal.comap_comap, hPcomap, hp]
  haveI : CharZero (O ⧸ I) := ‹_›
  obtain ⟨N, hN, key⟩ := exists_mk_trace_eq_nsmul' I hI hI0 P hIP
  refine ⟨N, hN, fun y hy => ?_⟩
  -- the hypothesis of `key` in `S`
  have hyS : ∀ E'' : Ideal S, E''.IsMaximal → E'' ≠ P → algebraMap B S y ∈ E'' := by
    intro E'' hE'' hne
    haveI : Algebra.IsIntegral O S := Algebra.IsIntegral.of_finite O S
    have h1 : E''.comap (algebraMap O S) = IsLocalRing.maximalIdeal O :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) E'')
    have hEq : (E''.comap (algebraMap B S)).comap (algebraMap C B) = q := by
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq C O S,
        ← Ideal.comap_comap, h1]
      exact Localization.AtPrime.comap_maximalIdeal (I := q)
    have hEp : E''.comap (algebraMap B S) ≠ p := fun h => hne (by
      rw [← IsLocalization.map_comap M S E'']
      exact congrArg (Ideal.map (algebraMap B S)) h)
    exact hy _ (Ideal.comap_isPrime _ _) hEq hEp
  have hk := key (algebraMap B S y) hyS
  rw [Algebra.trace_localization C q.primeCompl y] at hk
  -- the comparison maps
  have hqI : I.comap (algebraMap C O) ≤ q := le_of_eq
    (IsLocalization.comap_map_of_isPrime_disjoint q.primeCompl O (I := q) inferInstance
      (by rw [Set.disjoint_left]; intro a ha h; exact ha h))
  let φ₁ : (C ⧸ q) →+* (O ⧸ I) := Ideal.quotientMap I (algebraMap C O) Ideal.le_comap_map
  have hφ₁ : Function.Injective φ₁ := Ideal.quotientMap_injective' hqI
  letI : Algebra (C ⧸ q) (O ⧸ I) := φ₁.toAlgebra
  letI : Algebra (O ⧸ I) (S ⧸ P) := Ideal.Quotient.algebraQuotientOfLEComap hIP
  let φ₂ : (B ⧸ p) →+* (S ⧸ P) := Ideal.quotientMap P (algebraMap B S) Ideal.le_comap_map
  letI : Algebra (B ⧸ p) (S ⧸ P) := φ₂.toAlgebra
  letI : Algebra (C ⧸ q) (S ⧸ P) := ((algebraMap (O ⧸ I) (S ⧸ P)).comp φ₁).toAlgebra
  haveI : IsScalarTower (C ⧸ q) (O ⧸ I) (S ⧸ P) := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (C ⧸ q) (B ⧸ p) (S ⧸ P) := .of_algebraMap_eq fun x => by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk P (algebraMap O S (algebraMap C O c)) =
      φ₂ (Ideal.Quotient.mk p (algebraMap C B c))
    rw [Ideal.quotientMap_mk, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  set Mb := q.primeCompl.map (Ideal.Quotient.mk q) with hMb
  haveI : IsLocalization Mb (O ⧸ I) := IsLocalization.of_surjective q.primeCompl O
    (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective (by ext c; rfl) (by rw [Ideal.mk_ker, Ideal.mk_ker])
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (B ⧸ p) Mb) (S ⧸ P) := by
    have h := IsLocalization.of_surjective M S (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective (S' := S ⧸ P) (by ext b; rfl)
      (by rw [Ideal.mk_ker, Ideal.mk_ker])
    have hsub : M.map (Ideal.Quotient.mk p) = Algebra.algebraMapSubmonoid (B ⧸ p) Mb := by
      ext x
      constructor <;> rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩ <;> exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    rwa [hsub] at h
  have htr := Algebra.trace_localization (C ⧸ q) Mb (Rₘ := O ⧸ I) (Sₘ := S ⧸ P)
    (Ideal.Quotient.mk p y)
  apply hφ₁
  rw [map_nsmul]
  change Ideal.Quotient.mk I (algebraMap C O (Algebra.trace C B y)) = _
  rw [hk]
  exact congrArg (N • ·) htr

open nonZeroDivisors in
/-- **The trace-dual data.** In the situation of `exists_linearMap_trace_eq`, with fraction fields
`K / F` separable, `φ` is `b ↦ Tr(y₀ b) / δ` for some `y₀ ∈ B` and `δ ≠ 0`: the element
`y₀ / δ ∈ K` is trace-dual to `φ`. -/
private theorem exists_trace_mul_eq_mul {C B F K : Type*} [CommRing C] [IsDomain C] [CommRing B]
    [IsDomain B] [Algebra C B] [Module.Free C B] [Module.Finite C B] [FaithfulSMul C B] [Field F]
    [Algebra C F] [IsFractionRing C F] [Field K] [Algebra B K] [Algebra F K] [Algebra C K]
    [IsScalarTower C F K] [IsScalarTower C B K]
    [IsLocalization (Algebra.algebraMapSubmonoid B C⁰) K] [Algebra.IsSeparable F K]
    [FiniteDimensional F K] (φ : B →ₗ[C] C) :
    ∃ (y₀ : B) (δ : C), δ ≠ 0 ∧ ∀ b : B, Algebra.trace C B (y₀ * b) = δ * φ b := by
  classical
  obtain ⟨f, hf⟩ := exists_trace_mul_eq (F := F) (K := K) φ
  obtain ⟨⟨y₀, ⟨_, δ, hδ, rfl⟩⟩, hy⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B C⁰) f
  simp only at hy
  refine ⟨y₀, δ, nonZeroDivisors.ne_zero hδ, fun b => ?_⟩
  apply IsFractionRing.injective C F
  calc algebraMap C F (Algebra.trace C B (y₀ * b))
      = Algebra.trace F K (algebraMap B K (y₀ * b)) :=
        (Algebra.trace_localization (R := C) (Rₘ := F) (Sₘ := K) C⁰ (y₀ * b)).symm
    _ = Algebra.trace F K (algebraMap F K (algebraMap C F δ) * (f * algebraMap B K b)) := by
        rw [map_mul, ← hy, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        ring_nf
    _ = algebraMap C F δ * Algebra.trace F K (f * algebraMap B K b) := by
        rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
    _ = algebraMap C F (δ * φ b) := by rw [hf, map_mul]

/-- **Clearing a denominator prime to `q`.** Let `B` be integral over `C`, `K` the fraction field
of `B`, `q` a prime of `C` and `x ∈ K`. If for every prime `E` of `B` over `q` some `s ∉ E` has
`x s ∈ B`, then `x d ∈ B` for some `d ∈ C ∖ q`. -/
theorem exists_mul_mem_of_forall_liesOver {C B K : Type*} [CommRing C] [CommRing B]
    [Algebra C B] [Algebra.IsIntegral C B] [Field K] [Algebra B K] (q : Ideal C) [q.IsPrime]
    (x : K) (h : ∀ E : Ideal B, E.IsPrime → E.comap (algebraMap C B) = q →
      ∃ s : B, s ∉ E ∧ ∃ a : B, x * algebraMap B K s = algebraMap B K a) :
    ∃ d : C, d ∉ q ∧ ∃ a : B, x * algebraMap B K (algebraMap C B d) = algebraMap B K a := by
  classical
  let J : Ideal B :=
    { carrier := {s | ∃ a : B, x * algebraMap B K s = algebraMap B K a}
      add_mem' := by
        rintro s t ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a + b, by rw [map_add, mul_add, ha, hb, map_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c s ⟨a, ha⟩
        exact ⟨c * a, by rw [smul_eq_mul, map_mul, mul_left_comm, ha, map_mul]⟩ }
  by_contra hcon
  push Not at hcon
  have hle : J.comap (algebraMap C B) ≤ q := by
    intro d hd
    by_contra hdq
    obtain ⟨a, ha⟩ := hd
    exact hcon d hdq a ha
  obtain ⟨E, hJE, hEp, hEq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral q J hle
  obtain ⟨s, hsE, a, ha⟩ := h E hEp hEq
  exact hsE (hJE ⟨a, ha⟩)

/-- **The codifferent bound along `(g)` for multiples.** In the situation of
`exists_mul_mul_eq_of_trace_mem` at `q = (g)`, if `y₀` is trace-dual to `φ` up to `δ` and
`φ(b' B) ⊆ q`, then at every prime `E` over `q`, `y₀ b' s = δ a` for some `s ∉ E`, `a ∈ E`. -/
private theorem exists_mul_mul_eq_of_mem_of_trace_mem {C B : Type*} [CommRing C] [IsDomain C]
    [IsNoetherianRing C] [IsIntegrallyClosed C] [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] [Algebra C B] [Module.Free C B] [Module.Finite C B] [FaithfulSMul C B]
    (q : Ideal C) [q.IsPrime] {g : C} (hqdef : q = Ideal.span {g}) (hg0 : g ≠ 0)
    [CharZero (Localization.AtPrime q ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime q))]
    {y₀ : B} {δ : C} (hδ : δ ≠ 0) {φ : B →ₗ[C] C}
    (hy : ∀ b, Algebra.trace C B (y₀ * b) = δ * φ b) {b' : B} (hb' : ∀ b, φ (b' * b) ∈ q)
    (E : Ideal B) [E.IsPrime] (hE : E.comap (algebraMap C B) = q) :
    ∃ s : B, s ∉ E ∧ ∃ a ∈ E, y₀ * b' * s = algebraMap C B δ * a := by
  have hgB : algebraMap C B g ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective C B)).mpr hg0
  have hy' : ∀ b : B, ∃ c : C, Algebra.trace C B (y₀ * b' * b) = (δ * g) * c := by
    intro b
    have h1 := hb' b
    rw [hqdef, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, by rw [mul_assoc, hy, ← hc]; ring⟩
  obtain ⟨s, hs, a, ha, h⟩ := exists_mul_mul_eq_of_trace_mem q hqdef hg0 E hE
    (mul_ne_zero hδ hg0) hy'
  refine ⟨s, hs, a, ha, mul_left_cancel₀ hgB ?_⟩
  rw [map_mul] at h
  linear_combination h

/-- **The residue of the trace-dual element.** In the situation of `exists_trace_mul_eq_mul` at
the height-one prime `q = (g)` below `p`, with `p` locally principal generated by `b₀`, the
trace-dual element `x = y₀ / δ` has `x d = y₁ ∈ B` for some `d ∉ q`, and there is `N > 0` with
`d̄ · φ̄(b) = N · Tr_{(B/p)/(C/q)}(ȳ₁ b̄)` for all `b`. -/
theorem exists_mk_mul_mk_eq_nsmul_trace {C B : Type*} [CommRing C] [IsDomain C]
    [IsNoetherianRing C] [IsIntegrallyClosed C] [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] [Algebra C B] [Module.Free C B] [Module.Finite C B] [FaithfulSMul C B]
    (q : Ideal C) [q.IsPrime] {g : C} (hqdef : q = Ideal.span {g}) (hg0 : g ≠ 0)
    [CharZero (Localization.AtPrime q ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime q))]
    [CharZero (Localization.AtPrime q ⧸ q.map (algebraMap C (Localization.AtPrime q)))]
    (p : Ideal B) [p.IsPrime] (hp : p.comap (algebraMap C B) = q)
    [letI := Ideal.Quotient.algebraQuotientOfLEComap hp.ge; Module.Free (C ⧸ q) (B ⧸ p)]
    [letI := Ideal.Quotient.algebraQuotientOfLEComap hp.ge; Module.Finite (C ⧸ q) (B ⧸ p)]
    {y₀ : B} {δ : C} (hδ : δ ≠ 0) {φ : B →ₗ[C] C}
    (hy : ∀ b, Algebra.trace C B (y₀ * b) = δ * φ b) (hφp : ∀ b ∈ p, φ b ∈ q)
    {b₀ : B} (hb₀ : b₀ ≠ 0) (hb₀p : b₀ ∈ p)
    (hgen : ∀ a ∈ p, ∃ s : B, s ∉ p ∧ ∃ a' : B, a * s = b₀ * a') :
    letI := Ideal.Quotient.algebraQuotientOfLEComap hp.ge
    ∃ d : C, d ∉ q ∧ ∃ y₁ : B, y₁ * algebraMap C B δ = algebraMap C B d * y₀ ∧
      ∃ N : ℕ, 0 < N ∧ ∀ b : B, Ideal.Quotient.mk q d * Ideal.Quotient.mk q (φ b) =
        N • Algebra.trace (C ⧸ q) (B ⧸ p) (Ideal.Quotient.mk p (y₁ * b)) := by
  classical
  letI := Ideal.Quotient.algebraQuotientOfLEComap hp.ge
  have hinj : Function.Injective (algebraMap C B) := FaithfulSMul.algebraMap_injective C B
  have hgB : algebraMap C B g ≠ 0 := (map_ne_zero_iff _ hinj).mpr hg0
  have hδB : algebraMap C B δ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hδ
  -- the codifferent bound at every prime over `q`, for multiples by elements of `p`
  have hloc : ∀ (E : Ideal B) [E.IsPrime], E.comap (algebraMap C B) = q → ∀ b' ∈ p,
      ∃ s : B, s ∉ E ∧ ∃ a ∈ E, y₀ * b' * s = algebraMap C B δ * a :=
    fun E _ hE b' hb' => exists_mul_mul_eq_of_mem_of_trace_mem q hqdef hg0 hδ hy
      (fun b => hφp _ (Ideal.mul_mem_right _ _ hb')) E hE
  haveI : Algebra.IsIntegral C B := Algebra.IsIntegral.of_finite C B
  have hpE : ∀ (E : Ideal B) [E.IsPrime], E.comap (algebraMap C B) = q → E ≠ p →
      ∃ b' ∈ p, b' ∉ E := by
    intro E _ hE hne
    by_contra h
    push Not at h
    have hlt : p < E := lt_of_le_of_ne (fun b hb => h b hb) (Ne.symm hne)
    have := Ideal.IntegralClosure.comap_lt_comap (R := C) hlt
    rw [Ideal.under_def, Ideal.under_def, hp, hE] at this
    exact lt_irrefl _ this
  let K := FractionRing B
  have hδK : algebraMap B K (algebraMap C B δ) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B K)).mpr hδB
  set x : K := algebraMap B K y₀ / algebraMap B K (algebraMap C B δ) with hx
  have hxa : ∀ s a : B, y₀ * s = algebraMap C B δ * a →
      x * algebraMap B K s = algebraMap B K a := by
    intro s a h
    rw [hx, div_mul_eq_mul_div, div_eq_iff hδK, ← map_mul, ← map_mul, h, mul_comm]
  have hcrit : ∀ E : Ideal B, E.IsPrime → E.comap (algebraMap C B) = q →
      ∃ s : B, s ∉ E ∧ ∃ a : B, x * algebraMap B K s = algebraMap B K a := by
    intro E hEp hE
    by_cases hEq : E = p
    · subst hEq
      obtain ⟨s, hs, a, ha, h1⟩ := hloc E hE b₀ hb₀p
      obtain ⟨s'', hs'', a', h2⟩ := hgen a ha
      refine ⟨s * s'', hEp.mul_notMem hs hs'', a', hxa _ _ (mul_left_cancel₀ hb₀ ?_)⟩
      linear_combination s'' * h1 + algebraMap C B δ * h2
    · obtain ⟨b', hb'p, hb'E⟩ := hpE E hE hEq
      obtain ⟨s, hs, a, ha, h1⟩ := hloc E hE b' hb'p
      exact ⟨b' * s, hEp.mul_notMem hb'E hs, a, hxa _ _ (by linear_combination h1)⟩
  obtain ⟨d, hdq, y₁, hy₁⟩ := exists_mul_mem_of_forall_liesOver q x hcrit
  have hy₁' : y₁ * algebraMap C B δ = algebraMap C B d * y₀ := by
    apply IsFractionRing.injective B K
    rw [map_mul, map_mul, ← hy₁, hx, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hδK]
    ring
  have hy₁E : ∀ (E : Ideal B), E.IsPrime → E.comap (algebraMap C B) = q → E ≠ p → y₁ ∈ E := by
    intro E hEp hE hne
    obtain ⟨b', hb'p, hb'E⟩ := hpE E hE hne
    obtain ⟨s, hs, a, ha, h1⟩ := hloc E hE b' hb'p
    have h2 : y₁ * (b' * s) = algebraMap C B d * a := by
      apply mul_left_cancel₀ hδB
      linear_combination (b' * s) * hy₁' + algebraMap C B d * h1
    have h3 : y₁ * (b' * s) ∈ E := h2 ▸ Ideal.mul_mem_left _ _ ha
    exact (hEp.mem_or_mem h3).resolve_right (hEp.mul_notMem hb'E hs)
  have htr : ∀ b, Algebra.trace C B (y₁ * b) = d * φ b := by
    intro b
    apply mul_left_cancel₀ hδ
    have h1 : algebraMap C B δ * (y₁ * b) = d • (y₀ * b) := by
      rw [Algebra.smul_def]; linear_combination b * hy₁'
    rw [← smul_eq_mul δ, ← LinearMap.map_smul_of_tower, Algebra.smul_def, h1,
      LinearMap.map_smul_of_tower, hy, smul_eq_mul]
    ring
  obtain ⟨N, hN, key⟩ := exists_mk_trace_eq_nsmul_of_comap_eq q hqdef hg0 p hp
  refine ⟨d, hdq, y₁, hy₁', N, hN, fun b => ?_⟩
  rw [← map_mul, ← htr]
  exact key (y₁ * b) fun E hE hEq hne => Ideal.mul_mem_right _ _ (hy₁E E hE hEq hne)

/-- **Nondegeneracy of the trace form over a domain.** If `R` is free of finite rank over a domain
`A` and some basis has nonzero discriminant, then `Tr(x r) = 0` for all `r` forces `x = 0`. -/
private theorem eq_zero_of_forall_trace_mul_eq_zero {A R : Type*} [CommRing A] [IsDomain A]
    [CommRing R]
    [Algebra A R] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A R)
    (hdisc : Algebra.discr A b ≠ 0) {x : R} (h : ∀ r : R, Algebra.trace A R (x * r) = 0) :
    x = 0 := by
  classical
  set c := b.equivFun x with hc
  have hmul : (Algebra.traceMatrix A b).mulVec c = 0 := by
    funext j
    simp only [Matrix.mulVec, dotProduct, Algebra.traceMatrix_apply, Algebra.traceForm_apply,
      Pi.zero_apply]
    have hx : x = ∑ i, c i • b i := (b.sum_equivFun x).symm
    have := h (b j)
    rw [hx, Finset.sum_mul, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, LinearMap.map_smul, smul_eq_mul, mul_comm (b j) (b i), mul_comm]
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero (by rwa [← Algebra.discr_def]) hmul
  rw [← b.sum_equivFun x, ← hc, hc0]
  simp

/-- Two elements whose trace pairings are proportional through a common functional are
proportional: if `d ψ(r) = N Tr(y r)` and `w ψ(r) = Tr(u r)` for all `r`, then `N w y = d u`. -/
private theorem natCast_mul_algebraMap_mul_eq {A R : Type*} [CommRing A] [IsDomain A] [CommRing R]
    [Algebra A R] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A R)
    (hdisc : Algebra.discr A b ≠ 0) {N : ℕ} {w d : A} {y u : R} {ψ : R → A}
    (h₁ : ∀ r, d * ψ r = N • Algebra.trace A R (y * r))
    (h₂ : ∀ r, w * ψ r = Algebra.trace A R (u * r)) :
    (N : R) * algebraMap A R w * y = algebraMap A R d * u := by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_trace_mul_eq_zero b hdisc
  intro r
  have e1 : ((N : R) * algebraMap A R w * y - algebraMap A R d * u) * r =
      ((N : A) * w) • (y * r) - d • (u * r) := by
    simp only [Algebra.smul_def, map_mul, map_natCast]; ring
  rw [e1, map_sub, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, smul_eq_mul,
    smul_eq_mul, ← h₂]
  have h3 := h₁ r
  rw [nsmul_eq_mul] at h3
  linear_combination (-w) * h3

open nonZeroDivisors in
/-- **The discriminant of a finite extension of domains in characteristic zero is nonzero.** -/
private theorem discr_ne_zero_of_charZero {A S : Type*} [CommRing A] [IsDomain A] [CharZero A]
    [CommRing S] [IsDomain S] [Algebra A S] [Module.Finite A S] [FaithfulSMul A S] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A S) : Algebra.discr A b ≠ 0 := by
  classical
  let F := FractionRing A
  let L := FractionRing S
  letI : Algebra F L := FractionRing.liftAlgebra A L
  haveI : IsScalarTower A F L := FractionRing.isScalarTower_liftAlgebra A L
  haveI : Algebra.IsAlgebraic A S := Algebra.IsAlgebraic.of_finite A S
  let bL := b.localizationLocalization F A⁰ L
  haveI : Module.Finite F L := Module.Finite.of_basis bL
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective A F)
  have h := Algebra.discr_localizationLocalization A A⁰ L b (Rₘ := F)
  intro h0
  apply Algebra.discr_not_zero_of_basis F bL
  rw [h, h0, map_zero]

/-- A domain `S` that is a finite faithful algebra over a discrete valuation ring `A` is a free
`A`-module. -/
theorem free_of_isDiscreteValuationRing {A S : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing S] [IsDomain S] [Algebra A S] [Module.Finite A S]
    [FaithfulSMul A S] : Module.Free A S := by
  haveI : Module.IsTorsionFree A S := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro r m h
    rw [Algebra.smul_def, mul_eq_zero, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective A S)]
      at h
    exact h
  exact Module.free_of_finite_type_torsion_free'

/-- An irreducible element `ϖ` of a domain does not lie in `(ϖ)²`. -/
private theorem notMem_span_singleton_sq_of_irreducible {R : Type*} [CommRing R] [IsDomain R]
    {ϖ : R} (hϖ : Irreducible ϖ) : ϖ ∉ Ideal.span {ϖ} ^ 2 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  intro h
  exact hϖ.not_isUnit
    (isUnit_of_dvd_one ((mul_dvd_mul_iff_left hϖ.ne_zero).mp (by simpa [pow_two] using h)))

/-- In a local algebra over a field of characteristic zero, `e u + t c` is a unit for `e ≠ 0`, a
unit `u` and a non-unit `t`. -/
private theorem isUnit_natCast_mul_add_mul (k : Type*) {O : Type*} [Field k] [CharZero k]
    [CommRing O] [IsLocalRing O] [Algebra k O] {e : ℕ} (he : e ≠ 0) {u t : O} (hu : IsUnit u)
    (ht : ¬ IsUnit t) (c : O) : IsUnit ((e : O) * u + t * c) := by
  have he' : IsUnit (e : O) := by
    rw [← map_natCast (algebraMap k O)]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.mpr he)).map _
  by_contra h
  have h3 := sub_mem ((IsLocalRing.mem_maximalIdeal _).mpr h)
    (Ideal.mul_mem_right c _ ((IsLocalRing.mem_maximalIdeal _).mpr ht))
  rw [add_sub_cancel_right, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h3
  exact h3 (he'.mul hu)

/-! ### Noether normalization with a prescribed coordinate -/

section NoetherNormalization

open MvPolynomial

/-- Reconstruction from `finSuccEquiv`: `F = ∑ⱼ (coeff of Tʲ) X₀ʲ`, as an evaluation. -/
private theorem eval₂_finSuccEquiv {k : Type*} [CommRing k] {n : ℕ}
    (F : MvPolynomial (Fin (n + 1)) k) :
    Polynomial.eval₂ (rename Fin.succ).toRingHom (X 0) (finSuccEquiv k n F) = F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply]
  | add p q hp hq => rw [map_add, Polynomial.eval₂_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.eval₂_mul, hp]
    congr 1
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [finSuccEquiv_X_zero, Polynomial.eval₂_X]
    · rw [finSuccEquiv_X_succ, Polynomial.eval₂_C]
      simp

/-- If `F - c X₀ᵈ` has `X₀`-degree `< d` with `c ≠ 0`, then `F`, as a polynomial in `X₀` over
`k[X₁, …, Xₙ]`, has leading coefficient `c` and degree `d`. -/
private theorem leadingCoeff_finSuccEquiv_and_natDegree {k : Type*} [Field k] {n : ℕ}
    (F : MvPolynomial (Fin (n + 1)) k) {c : k} (hc : c ≠ 0) {d : ℕ}
    (hF : degreeOf 0 (F - C c * X 0 ^ d) < d) :
    (finSuccEquiv k n F).leadingCoeff = C c ∧ (finSuccEquiv k n F).natDegree = d := by
  classical
  set P := finSuccEquiv k n F with hP
  have hPd : (P - Polynomial.C (C c) * Polynomial.X ^ d).natDegree < d := by
    have := natDegree_finSuccEquiv (F - C c * X 0 ^ d)
    rw [map_sub, map_mul, map_pow, finSuccEquiv_X_zero] at this
    rw [show finSuccEquiv k n (C c) = Polynomial.C (C c) by simp [finSuccEquiv_apply]] at this
    rw [this]; exact hF
  have hCc : (C c : MvPolynomial (Fin n) k) ≠ 0 := by simpa using hc
  have hdeg : (P - Polynomial.C (C c) * Polynomial.X ^ d).degree <
      (Polynomial.C (C c) * Polynomial.X ^ d : Polynomial (MvPolynomial (Fin n) k)).degree := by
    rw [Polynomial.degree_C_mul_X_pow d hCc]
    exact (Polynomial.degree_le_natDegree).trans_lt (by exact_mod_cast hPd)
  have hsum : P = Polynomial.C (C c) * Polynomial.X ^ d +
      (P - Polynomial.C (C c) * Polynomial.X ^ d) := by ring
  constructor
  · rw [hsum, Polynomial.leadingCoeff_add_of_degree_lt' hdeg]
    simp
  · rw [hsum, Polynomial.natDegree_add_eq_left_of_degree_lt hdeg]
    exact Polynomial.natDegree_C_mul_X_pow d _ hCc

/-- If `F - c X₀ᵈ` has `X₀`-degree `< d` with `c ≠ 0`, then `F` has `X₀`-degree `d`. -/
private theorem degreeOf_zero_eq_of_degreeOf_sub_lt {k : Type*} [Field k] {n : ℕ}
    (F : MvPolynomial (Fin (n + 1)) k) {c : k} (hc : c ≠ 0) {d : ℕ}
    (hF : degreeOf 0 (F - C c * X 0 ^ d) < d) : degreeOf 0 F = d := by
  rw [← natDegree_finSuccEquiv]
  exact (leadingCoeff_finSuccEquiv_and_natDegree F hc hF).2

/-- **Making a polynomial a coordinate is integral.** If `F ∈ k[X₀, …, Xₙ]` is, as a polynomial in
`X₀`, `c X₀ᵈ` plus terms of lower degree with `c ≠ 0`, `d ≥ 1`, then `k[X]` is integral over its
subalgebra `k[F, X₁, …, Xₙ]`: the map `X₀ ↦ F`, `Xᵢ ↦ Xᵢ` is integral. -/
private theorem isIntegral_aeval_cases {k : Type*} [Field k] {n : ℕ}
    (F : MvPolynomial (Fin (n + 1)) k)
    {c : k} (hc : c ≠ 0) {d : ℕ} (hd : 1 ≤ d)
    (hF : degreeOf 0 (F - C c * X 0 ^ d) < d) :
    (aeval (Fin.cases F fun i => X i.succ) :
      MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k).toRingHom.IsIntegral := by
  classical
  set ψ : MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
    aeval (Fin.cases F fun i => X i.succ) with hψ
  letI : Algebra (MvPolynomial (Fin (n + 1)) k) (MvPolynomial (Fin (n + 1)) k) :=
    ψ.toRingHom.toAlgebra
  have hψsucc : ψ.toRingHom.comp (rename Fin.succ).toRingHom = (rename Fin.succ).toRingHom := by
    ext j
    · simp [hψ]
    · simp [hψ]
  have hPlead := leadingCoeff_finSuccEquiv_and_natDegree F hc hF
  set P := finSuccEquiv k n F with hP
  set Q : Polynomial (MvPolynomial (Fin (n + 1)) k) :=
    P.map (rename Fin.succ).toRingHom - Polynomial.C (X 0) with hQ
  have hmapc : (rename (Fin.succ : Fin n → Fin (n + 1)) :
      MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin (n + 1)) k).toRingHom (C c) = C c := by simp
  have hlc0 : (rename (Fin.succ : Fin n → Fin (n + 1)) :
      MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin (n + 1)) k).toRingHom P.leadingCoeff ≠ 0 := by
    rw [hPlead.1, hmapc]; simpa using hc
  have hmapdeg : (P.map (rename Fin.succ).toRingHom).natDegree = d := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlc0, hPlead.2]
  have hQdeg : (Polynomial.C (X 0 : MvPolynomial (Fin (n + 1)) k)).degree <
      (P.map (rename Fin.succ).toRingHom).degree := by
    have hne : P.map (rename Fin.succ).toRingHom ≠ 0 := by
      intro h0; rw [h0, Polynomial.natDegree_zero] at hmapdeg; omega
    rw [Polynomial.degree_eq_natDegree hne, hmapdeg]
    exact (Polynomial.degree_C_le).trans_lt (by exact_mod_cast hd)
  have hQlead : Q.leadingCoeff = C c := by
    rw [hQ, Polynomial.leadingCoeff_sub_of_degree_lt hQdeg,
      Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hlc0, hPlead.1, hmapc]
  have hQ0 : Polynomial.aeval (X 0 : MvPolynomial (Fin (n + 1)) k) Q = 0 := by
    rw [hQ, map_sub, Polynomial.aeval_C, Polynomial.aeval_def, Polynomial.eval₂_map,
      RingHom.algebraMap_toAlgebra, hψsucc, eval₂_finSuccEquiv]
    simp [hψ]
  have hX0 : IsIntegral (MvPolynomial (Fin (n + 1)) k) (X 0 : MvPolynomial (Fin (n + 1)) k) := by
    have hmon : (Polynomial.C (C c⁻¹ : MvPolynomial (Fin (n + 1)) k) * Q).Monic := by
      have hne : (C c⁻¹ : MvPolynomial (Fin (n + 1)) k) * Q.leadingCoeff ≠ 0 := by
        rw [hQlead, ← map_mul, inv_mul_cancel₀ hc, map_one]; exact one_ne_zero
      rw [Polynomial.Monic, Polynomial.leadingCoeff_mul' (by rwa [Polynomial.leadingCoeff_C]),
        Polynomial.leadingCoeff_C, hQlead, ← map_mul, inv_mul_cancel₀ hc, map_one]
    refine ⟨_, hmon, ?_⟩
    rw [← Polynomial.aeval_def, map_mul, hQ0, mul_zero]
  have hall : ∀ i, IsIntegral (MvPolynomial (Fin (n + 1)) k)
      (X i : MvPolynomial (Fin (n + 1)) k) := by
    refine Fin.cases hX0 fun j => ?_
    have : (X j.succ : MvPolynomial (Fin (n + 1)) k) =
        algebraMap (MvPolynomial (Fin (n + 1)) k) _ (X j.succ) := by
      simp [RingHom.algebraMap_toAlgebra, hψ]
    rw [this]; exact isIntegral_algebraMap
  intro x
  show IsIntegral (MvPolynomial (Fin (n + 1)) k) x
  induction x using MvPolynomial.induction_on with
  | C a =>
    have : (C a : MvPolynomial (Fin (n + 1)) k) =
        algebraMap (MvPolynomial (Fin (n + 1)) k) _ (C a) := by
      simp [RingHom.algebraMap_toAlgebra, hψ]
    rw [this]; exact isIntegral_algebraMap
  | add p q hp hq => exact hp.add hq
  | mul_X p i hp => exact hp.mul (hall i)

/-- `X₀ ↦ F`, `Xᵢ ↦ Xᵢ` is injective when `F` has positive degree in `X₀`: under `finSuccEquiv`
it is composition with `F` viewed as a polynomial in `X₀`. -/
private theorem injective_aeval_cases {k : Type*} [Field k] {n : ℕ}
    (F : MvPolynomial (Fin (n + 1)) k)
    (hF : 0 < degreeOf 0 F) :
    Function.Injective (aeval (Fin.cases F fun i => X i.succ) :
      MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k) := by
  classical
  set ψ : MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
    aeval (Fin.cases F fun i => X i.succ) with hψ
  set P := finSuccEquiv k n F with hP
  have hX : ∀ i, finSuccEquiv k n (ψ (X i)) = (finSuccEquiv k n (X i)).comp P := by
    refine Fin.cases ?_ (fun j => ?_)
    · rw [hψ, aeval_X, Fin.cases_zero, finSuccEquiv_X_zero, Polynomial.X_comp]
    · rw [hψ, aeval_X, Fin.cases_succ, finSuccEquiv_X_succ, Polynomial.C_comp]
  have hcomp : ∀ G, finSuccEquiv k n (ψ G) = (finSuccEquiv k n G).comp P := by
    intro G
    induction G using MvPolynomial.induction_on with
    | C a =>
      rw [hψ, aeval_C, MvPolynomial.algebraMap_eq,
        show finSuccEquiv k n (C a) = Polynomial.C (C a) by simp [finSuccEquiv_apply],
        Polynomial.C_comp]
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, Polynomial.add_comp]
    | mul_X p i hp =>
      rw [map_mul ψ, map_mul (finSuccEquiv k n), hp, hX i, map_mul (finSuccEquiv k n),
        Polynomial.mul_comp]
  have hPdeg : 0 < P.natDegree := by rw [hP, natDegree_finSuccEquiv]; exact hF
  rw [injective_iff_map_eq_zero]
  intro G hG
  have h1 := hcomp G
  rw [hG, map_zero] at h1
  have h2 := (Polynomial.comp_eq_zero_iff.mp h1.symm)
  rcases h2 with h2 | ⟨-, h2⟩
  · exact (finSuccEquiv k n).injective (by rw [h2, map_zero])
  · exfalso
    have := congrArg Polynomial.natDegree h2
    rw [Polynomial.natDegree_C] at this
    omega

/-- **Noether normalization with a prescribed coordinate.** Over an infinite field, every
polynomial `h ∈ k[X₀, …, Xₙ]` of positive degree is the image of `X₀` under an injective integral
`k`-algebra endomorphism of `k[X₀, …, Xₙ]`. -/
private theorem exists_algHom_injective_isIntegral_X_zero_eq {k : Type*} [Field k] [Infinite k]
    {n : ℕ} (h : MvPolynomial (Fin (n + 1)) k) (hh : 1 ≤ h.totalDegree) :
    ∃ φ : MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k,
      Function.Injective φ ∧ φ.toRingHom.IsIntegral ∧ φ (X 0) = h := by
  classical
  have hττ : ∀ p : MvPolynomial (Fin (n + 1)) k,
      rename (Equiv.swap (0 : Fin (n + 1)) (Fin.last n))
        (rename (Equiv.swap (0 : Fin (n + 1)) (Fin.last n)) p) = p := fun p => by
    rw [rename_rename]
    convert rename_id_apply p
    funext i
    exact Equiv.swap_apply_self _ _ _
  have hh' : 1 ≤ (rename (Equiv.swap (0 : Fin (n + 1)) (Fin.last n)) h).totalDegree :=
    le_trans hh (by
      calc h.totalDegree = (rename (Equiv.swap (0 : Fin (n + 1)) (Fin.last n))
            (rename (Equiv.swap (0 : Fin (n + 1)) (Fin.last n)) h)).totalDegree := by rw [hττ]
        _ ≤ _ := totalDegree_rename_le _ _)
  obtain ⟨a, c, hc, hdeg⟩ := MMP.Resolution.Kollar.exists_linear_change_degreeOf_lt _ hh'
  let L : MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
    aeval fun i =>
      Fin.lastCases (X (Fin.last n)) (fun i => X i.castSucc + C (a i) * X (Fin.last n)) i
  let L' : MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
    aeval fun i =>
      Fin.lastCases (X (Fin.last n)) (fun i => X i.castSucc - C (a i) * X (Fin.last n)) i
  have hLL' : L'.comp L = AlgHom.id k _ := by
    refine algHom_ext fun i => Fin.lastCases ?_ (fun j => ?_) i
    · simp [L, L']
    · simp only [L, L', AlgHom.comp_apply, aeval_X, Fin.lastCases_castSucc, map_add, map_mul,
        aeval_C, Fin.lastCases_last, AlgHom.id_apply, algebraMap_eq]
      ring
  have hL'L : L.comp L' = AlgHom.id k _ := by
    refine algHom_ext fun i => Fin.lastCases ?_ (fun j => ?_) i
    · simp [L, L']
    · simp only [L, L', AlgHom.comp_apply, aeval_X, Fin.lastCases_castSucc, map_sub, map_mul,
        aeval_C, Fin.lastCases_last, AlgHom.id_apply, algebraMap_eq]
      ring
  let σ : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k :=
    ((renameEquiv k (Equiv.swap (0 : Fin (n + 1)) (Fin.last n))).trans
      (AlgEquiv.ofAlgHom L L' hL'L hLL')).trans
        (renameEquiv k (Equiv.swap (0 : Fin (n + 1)) (Fin.last n)))
  have hσ : ∀ p, σ p = rename (Equiv.swap (0 : Fin (n + 1)) (Fin.last n))
      (L (rename (Equiv.swap (0 : Fin (n + 1)) (Fin.last n)) p)) := fun p => rfl
  have hF : degreeOf 0 (σ h - C c * X 0 ^
        (rename (Equiv.swap (0 : Fin (n + 1)) (Fin.last n)) h).totalDegree) <
      (rename (Equiv.swap (0 : Fin (n + 1)) (Fin.last n)) h).totalDegree := by
    have h1 : σ h - C c * X 0 ^ (rename (Equiv.swap (0 : Fin (n + 1)) (Fin.last n)) h).totalDegree =
        rename (Equiv.swap (0 : Fin (n + 1)) (Fin.last n))
          (L (rename (Equiv.swap (0 : Fin (n + 1)) (Fin.last n)) h) - C c * X (Fin.last n) ^
            (rename (Equiv.swap (0 : Fin (n + 1)) (Fin.last n)) h).totalDegree) := by
      rw [hσ, map_sub, map_mul, map_pow, rename_C, rename_X, Equiv.swap_apply_right]
    have h2 := degreeOf_rename_of_injective (R := k)
      (Equiv.injective (Equiv.swap (0 : Fin (n + 1)) (Fin.last n))) (Fin.last n)
      (p := L (rename (Equiv.swap (0 : Fin (n + 1)) (Fin.last n)) h) - C c * X (Fin.last n) ^
            (rename (Equiv.swap (0 : Fin (n + 1)) (Fin.last n)) h).totalDegree)
    rw [Equiv.swap_apply_right] at h2
    rwa [h1, h2]
  have hF0 : 0 < degreeOf 0 (σ h) := by
    rw [degreeOf_zero_eq_of_degreeOf_sub_lt (σ h) hc hF]; omega
  refine ⟨σ.symm.toAlgHom.comp (aeval (Fin.cases (σ h) fun i => X i.succ)),
    σ.symm.injective.comp (injective_aeval_cases (σ h) hF0), ?_, ?_⟩
  · exact RingHom.IsIntegral.trans _ _ (isIntegral_aeval_cases (σ h) hc hh' hF)
      (RingHom.isIntegral_of_surjective _ σ.symm.surjective)
  · simp

/-- **Going down, one step.** For an integral extension `C ⊆ B` of domains with `C` integrally
closed, if every prime strictly inside the prime `P` of `B` is zero, so is every prime strictly
inside `P ∩ C`. -/
private theorem eq_bot_of_lt_comap {C B : Type*} [CommRing C] [IsDomain C] [IsIntegrallyClosed C]
    [CommRing B] [IsDomain B] [Algebra C B] [Algebra.IsIntegral C B] [FaithfulSMul C B]
    (P : Ideal B) [P.IsPrime] (hP : ∀ Q : Ideal B, Q.IsPrime → Q < P → Q = ⊥)
    (𝔞 : Ideal C) [𝔞.IsPrime] (h𝔞 : 𝔞 < P.comap (algebraMap C B)) : 𝔞 = ⊥ := by
  haveI : P.LiesOver (P.comap (algebraMap C B)) := ⟨rfl⟩
  obtain ⟨Q, hQle, hQprime, hQlies⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := 𝔞) P h𝔞.le
  have hQP : Q ≠ P := by
    rintro rfl
    exact h𝔞.ne hQlies.over
  rw [hQlies.over, hP Q hQprime (lt_of_le_of_ne hQle hQP)]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective C B)

/-- A nonzero prime of a factorial domain with only `0` strictly inside it is principal. -/
private theorem exists_eq_span_singleton_of_forall_lt {D : Type*} [CommRing D] [IsDomain D]
    [UniqueFactorizationMonoid D] (𝔞 : Ideal D) [𝔞.IsPrime] (h0 : 𝔞 ≠ ⊥)
    (h : ∀ 𝔟 : Ideal D, 𝔟.IsPrime → 𝔟 < 𝔞 → 𝔟 = ⊥) : ∃ π : D, π ≠ 0 ∧ 𝔞 = Ideal.span {π} := by
  have hh : 𝔞.height = 1 := by
    apply le_antisymm
    · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
      intro 𝔟 h𝔟 hlt
      rw [h 𝔟 h𝔟 hlt, (Ideal.height_eq_zero_iff_eq_bot).mpr rfl]
      exact zero_lt_one
    · rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      exact h0
  obtain ⟨π, hπ⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh).principal
  refine ⟨π, fun h' => h0 (by rw [hπ, h']; simp), ?_⟩
  rw [hπ]

/-- The specialisation `X₀ ↦ 0`, `X_{i+1} ↦ X_i`. -/
private noncomputable abbrev dropZero (k : Type*) [CommRing k] (s : ℕ) :
    MvPolynomial (Fin (s + 1)) k →ₐ[k] MvPolynomial (Fin s) k :=
  aeval (Fin.cases 0 X)

private theorem dropZero_rename (k : Type*) [CommRing k] {s : ℕ} (a : MvPolynomial (Fin s) k) :
    dropZero k s (rename Fin.succ a) = a := by
  rw [dropZero, aeval_rename]
  convert aeval_X_left_apply a
  funext i
  simp

private theorem sub_rename_dropZero_mem (k : Type*) [CommRing k] {s : ℕ}
    (d : MvPolynomial (Fin (s + 1)) k) :
    d - rename Fin.succ (dropZero k s d) ∈ Ideal.span {(X 0 : MvPolynomial (Fin (s + 1)) k)} := by
  induction d using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [dropZero, aeval_X, Fin.cases_zero, map_zero, mul_zero, sub_zero]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · simp only [dropZero, aeval_X, Fin.cases_succ, rename_X]
      rw [← sub_mul]
      exact Ideal.mul_mem_right _ _ hp

private theorem eq_zero_of_rename_mem (k : Type*) [CommRing k] {s : ℕ} {a : MvPolynomial (Fin s) k}
    (h : rename Fin.succ a ∈ Ideal.span {(X 0 : MvPolynomial (Fin (s + 1)) k)}) : a = 0 := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  have := congrArg (dropZero k s) hc
  rw [dropZero_rename, map_mul] at this
  rw [← this]
  simp [dropZero]

/-- Going down along an integral injective ring map `f : D → R` with `D` integrally closed: the
contraction of a nonzero prime `P` of the domain `R` with only `0` strictly inside it is nonzero,
with only `0` strictly inside it. -/
private theorem comap_ne_bot_and_eq_bot_of_lt {D R : Type*} [CommRing D] [IsDomain D]
    [IsIntegrallyClosed D] [CommRing R] [IsDomain R] (f : D →+* R) (hf : Function.Injective f)
    (hint : f.IsIntegral) (P : Ideal R) [P.IsPrime] (hP0 : P ≠ ⊥)
    (hP : ∀ Q : Ideal R, Q.IsPrime → Q < P → Q = ⊥) :
    P.comap f ≠ ⊥ ∧ ∀ 𝔞 : Ideal D, 𝔞.IsPrime → 𝔞 < P.comap f → 𝔞 = ⊥ := by
  letI := f.toAlgebra
  haveI : Algebra.IsIntegral D R := ⟨hint⟩
  haveI : FaithfulSMul D R := (faithfulSMul_iff_algebraMap_injective D R).mpr hf
  refine ⟨?_, fun 𝔞 h𝔞 hlt => eq_bot_of_lt_comap P hP 𝔞 hlt⟩
  obtain ⟨r, hrP, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  exact Ideal.comap_ne_bot_of_integral_mem hr0 hrP (Algebra.IsIntegral.isIntegral r)

/-- **Noether normalization adapted to a flag `p ⊂ 𝔮`.** Let `R` be a domain of finite type over
an infinite field `k`, and `p ⊂ 𝔮` primes of `R` with `p ≠ 0`, no prime strictly between `0` and
`p`, and none strictly between `p` and `𝔮`. Then there is a finite injective
`ν : k[X₀, …, X_s] → R` with `p ∩ k[X] = (X₀)` and `𝔮 ∩ k[X] = (X₀, w)` for some
`w = w'(X₁, …, X_s)`, `w' ≠ 0`, and `w(X₁, …, X_s) ∈ 𝔮` exactly for `a ∈ (w')`. -/
private theorem exists_finite_comap_eq_span_X_zero {k R : Type*} [Field k] [Infinite k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (p 𝔮 : Ideal R) [p.IsPrime] [𝔮.IsPrime] (hp0 : p ≠ ⊥) (hpq : p < 𝔮)
    (hbelow : ∀ c : Ideal R, c.IsPrime → c < p → c = ⊥)
    (habove : ∀ c : Ideal R, c.IsPrime → p < c → c ≤ 𝔮 → c = 𝔮) :
    ∃ (s : ℕ) (ν : MvPolynomial (Fin (s + 1)) k →ₐ[k] R), Function.Injective ν ∧
      ν.toRingHom.IsIntegral ∧
      p.comap ν.toRingHom = Ideal.span {X 0} ∧ ∃ w' : MvPolynomial (Fin s) k, w' ≠ 0 ∧
        rename Fin.succ w' ∉ Ideal.span {(X 0 : MvPolynomial (Fin (s + 1)) k)} ∧
        𝔮.comap ν.toRingHom = Ideal.span {X 0, rename Fin.succ w'} ∧
        ∀ a, rename Fin.succ a ∈ 𝔮.comap ν.toRingHom ↔ a ∈ Ideal.span {w'} := by
  classical
  obtain ⟨s₀, ν₀, hν₀, hfin₀⟩ := exists_finite_inj_algHom_of_fg k R
  have hint₀ : ν₀.toRingHom.IsIntegral := hfin₀.to_isIntegral
  obtain ⟨hne₀, hlt₀⟩ := comap_ne_bot_and_eq_bot_of_lt ν₀.toRingHom hν₀ hint₀ p hp0 hbelow
  obtain ⟨h, hh0, hph⟩ := exists_eq_span_singleton_of_forall_lt _ hne₀ hlt₀
  -- `h` is not constant
  have hdeg : 1 ≤ h.totalDegree := by
    by_contra hd
    push Not at hd
    have h1 : h = C (h.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp (by omega)
    have hc : h.coeff 0 ≠ 0 := fun hc => hh0 (by rw [h1, hc, map_zero])
    have hu : IsUnit h := by rw [h1]; exact (IsUnit.mk0 _ hc).map C
    have : p.comap ν₀.toRingHom = ⊤ := by rw [hph, Ideal.span_singleton_eq_top]; exact hu
    exact (Ideal.IsPrime.ne_top (Ideal.comap_isPrime _ _)) this
  obtain _ | s := s₀
  · exfalso
    have : h.totalDegree = 0 := by
      rw [totalDegree_eq_zero_iff_eq_C]
      exact eq_C_of_isEmpty h
    omega
  obtain ⟨φ, hφ, hφint, hφX⟩ := exists_algHom_injective_isIntegral_X_zero_eq h hdeg
  set ν : MvPolynomial (Fin (s + 1)) k →ₐ[k] R := ν₀.comp φ with hνdef
  have hνinj : Function.Injective ν := hν₀.comp hφ
  have hνint : ν.toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hφint hint₀
  -- `p ∩ k[X] = (X₀)`
  obtain ⟨hne, hlt⟩ := comap_ne_bot_and_eq_bot_of_lt ν.toRingHom hνinj hνint p hp0 hbelow
  have hX0prime : (Ideal.span {(X 0 : MvPolynomial (Fin (s + 1)) k)}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime X_prime
  have hX0p : Ideal.span {(X 0 : MvPolynomial (Fin (s + 1)) k)} ≤ p.comap ν.toRingHom := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change ν₀ (φ (X 0)) ∈ p
    rw [hφX]
    change h ∈ p.comap ν₀.toRingHom
    rw [hph]; exact Ideal.mem_span_singleton_self h
  have hpX : p.comap ν.toRingHom = Ideal.span {X 0} := by
    rcases hX0p.lt_or_eq with hlt' | heq
    · exfalso
      have := hlt _ hX0prime hlt'
      rw [Ideal.span_singleton_eq_bot] at this
      exact X_ne_zero _ this
    · exact heq.symm
  -- `𝔮 / p` over `k[X₁, …, X_s]`
  set ψ : MvPolynomial (Fin s) k →+* R ⧸ p :=
    (Ideal.Quotient.mk p).comp (ν.toRingHom.comp (rename Fin.succ).toRingHom) with hψdef
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    apply eq_zero_of_rename_mem k
    rw [← hpX, Ideal.mem_comap]
    exact Ideal.Quotient.eq_zero_iff_mem.mp ha
  have hcomp : (Ideal.Quotient.mk p).comp ν.toRingHom = ψ.comp (dropZero k s).toRingHom := by
    ext d
    · simp only [RingHom.comp_apply, hψdef]
      rw [Ideal.Quotient.eq]
      have := sub_rename_dropZero_mem k (C d : MvPolynomial (Fin (s + 1)) k)
      rw [← hpX] at this
      simpa using this
    · simp only [RingHom.comp_apply, hψdef]
      rw [Ideal.Quotient.eq, ← map_sub]
      have := sub_rename_dropZero_mem k (X d : MvPolynomial (Fin (s + 1)) k)
      rw [← hpX] at this
      exact this
  have hψint : ψ.IsIntegral := by
    apply RingHom.IsIntegral.tower_top (dropZero k s).toRingHom ψ
    rw [← hcomp]
    exact RingHom.IsIntegral.trans _ _ hνint
      (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
  set Q := 𝔮.map (Ideal.Quotient.mk p) with hQdef
  have hker : RingHom.ker (Ideal.Quotient.mk p) ≤ 𝔮 := by rw [Ideal.mk_ker]; exact hpq.le
  haveI hQp : Q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hQcomap : Q.comap (Ideal.Quotient.mk p) = 𝔮 := by
    rw [hQdef, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hpq.le]
  have hQ0 : Q ≠ ⊥ := by
    intro h0
    apply hpq.ne
    rw [← hQcomap, h0, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hQbelow : ∀ Q' : Ideal (R ⧸ p), Q'.IsPrime → Q' < Q → Q' = ⊥ := by
    intro Q' hQ' hlt'
    have h1 : p ≤ Q'.comap (Ideal.Quotient.mk p) := by
      intro a ha
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact Q'.zero_mem
    have h2 : Q'.comap (Ideal.Quotient.mk p) < 𝔮 := by
      rw [← hQcomap]
      refine lt_of_le_of_ne (Ideal.comap_mono hlt'.le) fun h4 => hlt'.ne ?_
      rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q', h4,
        Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q]
    rcases h1.lt_or_eq with h3 | h3
    · exact absurd (habove _ (Ideal.comap_isPrime _ _) h3 h2.le) h2.ne
    · rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q', ← h3,
        Ideal.map_quotient_self]
  obtain ⟨hne', hlt''⟩ := comap_ne_bot_and_eq_bot_of_lt ψ hψinj hψint Q hQ0 hQbelow
  obtain ⟨w', hw'0, hw'⟩ := exists_eq_span_singleton_of_forall_lt _ hne' hlt''
  have hiff : ∀ a, rename Fin.succ a ∈ 𝔮.comap ν.toRingHom ↔ a ∈ Ideal.span {w'} := by
    intro a
    rw [← hw', Ideal.mem_comap, Ideal.mem_comap, hψdef, RingHom.comp_apply, hQdef,
      Ideal.mem_quotient_iff_mem hpq.le]
    rfl
  have hX0q : (X 0 : MvPolynomial (Fin (s + 1)) k) ∈ 𝔮.comap ν.toRingHom :=
    Ideal.comap_mono hpq.le (hX0p (Ideal.mem_span_singleton_self _))
  refine ⟨s, ν, hνinj, hνint, hpX, w', hw'0, fun h' => hw'0 (eq_zero_of_rename_mem k h'), ?_,
    hiff⟩
  apply le_antisymm
  · intro d hd
    have h1 := sub_rename_dropZero_mem k d
    have h2 : rename Fin.succ (dropZero k s d) ∈ 𝔮.comap ν.toRingHom := by
      have : d - (d - rename Fin.succ (dropZero k s d)) ∈ 𝔮.comap ν.toRingHom :=
        sub_mem hd (Ideal.comap_mono hpq.le (hX0p h1))
      simpa using this
    have h3 := (hiff _).mp h2
    rw [← sub_add_cancel d (rename Fin.succ (dropZero k s d))]
    refine add_mem ?_ ?_
    · exact (Ideal.span_mono (by simp)) h1
    · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h3
      rw [← hc, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact hX0q
    · exact (hiff w').mpr (Ideal.mem_span_singleton_self _)

end NoetherNormalization

/-! ### Freeness of a finite normal extension of a regular local ring of dimension two -/

/-- In a domain integral over an integrally closed domain `C`, when `(g)` is prime and
`w ∉ (g)`, the element `w` does not map into any height-one prime containing `g`. -/
private theorem algebraMap_notMem_of_height_eq_one {C B : Type u} [CommRing C] [IsDomain C]
    [IsIntegrallyClosed C] [CommRing B] [IsDomain B] [Algebra C B] [Algebra.IsIntegral C B]
    [FaithfulSMul C B] {g w : C} (hg : g ≠ 0) (hgprime : (Ideal.span {g}).IsPrime)
    (hw : w ∉ Ideal.span {g}) (𝔓 : Ideal B) [𝔓.IsPrime] (h𝔓 : 𝔓.height = 1)
    (hg𝔓 : algebraMap C B g ∈ 𝔓) : algebraMap C B w ∉ 𝔓 := by
  intro hw𝔓
  -- `𝔓` lies over a prime containing `(g)` strictly
  have hle : Ideal.span {g} ≤ 𝔓.comap (algebraMap C B) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hg𝔓
  have hlt : Ideal.span {g} < 𝔓.comap (algebraMap C B) :=
    lt_of_le_of_ne hle fun h => hw (h ▸ hw𝔓)
  haveI : 𝔓.LiesOver (𝔓.comap (algebraMap C B)) := ⟨rfl⟩
  obtain ⟨𝔔, h𝔔le, h𝔔prime, h𝔔lies⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := Ideal.span {g}) 𝔓 hle
  have h𝔔lt : 𝔔 < 𝔓 := by
    refine lt_of_le_of_ne h𝔔le fun h => hlt.ne ?_
    rw [h𝔔lies.over, h]
  have h1 : 𝔓.height ≤ ((1 : ℕ) : ℕ∞) := by rw [h𝔓]; rfl
  rw [Ideal.height_le_iff] at h1
  have h2 := h1 𝔔 h𝔔prime h𝔔lt
  have h3 : 𝔔.height = 0 := by
    have : 𝔔.height < 1 := by exact_mod_cast h2
    exact ENat.lt_one_iff_eq_zero.mp this
  have h4 : 𝔔 = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp h3
  have hg𝔔 : g ∈ 𝔔.comap (algebraMap C B) := by
    change g ∈ 𝔔.under C
    rw [← h𝔔lies.over]; exact Ideal.mem_span_singleton_self g
  rw [h4, Ideal.mem_comap, Ideal.mem_bot,
    map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective C B)] at hg𝔔
  exact hg hg𝔔

/-- `w` is regular on `B / g B` for `B` Noetherian normal (Serre's `S₂`, through algebraic
Hartogs). -/
private theorem exists_eq_mul_of_mul_eq_mul {C B : Type u} [CommRing C] [IsDomain C]
    [IsIntegrallyClosed C] [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    [Algebra C B] [Algebra.IsIntegral C B] [FaithfulSMul C B] {g w : C} (hg : g ≠ 0)
    (hgprime : (Ideal.span {g}).IsPrime) (hw : w ∉ Ideal.span {g}) {b b' : B}
    (h : algebraMap C B w * b = algebraMap C B g * b') : ∃ c : B, b = algebraMap C B g * c := by
  have hinj := FaithfulSMul.algebraMap_injective C B
  have hg' : algebraMap C B g ≠ 0 := (map_ne_zero_iff _ hinj).mpr hg
  let K := FractionRing B
  have hgK : algebraMap B K (algebraMap C B g) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B K)).mpr hg'
  obtain ⟨r, hr⟩ :=
    Stacks.AlgebraicGeometry.UnitsNormalProper.exists_algebraMap_eq_of_forall_height_eq_one
    (R := B) K (z := algebraMap B K b / algebraMap B K (algebraMap C B g)) fun q hq => by
      by_cases hgq : algebraMap C B g ∈ q.asIdeal
      · have hwq : algebraMap C B w ∉ q.asIdeal :=
          algebraMap_notMem_of_height_eq_one hg hgprime hw q.asIdeal hq hgq
        refine ⟨b', algebraMap C B w, hwq, ?_⟩
        have hwK : algebraMap B K (algebraMap C B w) ≠ 0 := by
          refine (map_ne_zero_iff _ (IsFractionRing.injective B K)).mpr fun h0 => hwq ?_
          rw [h0]; exact q.asIdeal.zero_mem
        rw [div_mul_eq_mul_div, div_eq_iff hgK, ← map_mul, ← map_mul, mul_comm b, h, mul_comm]
      · exact ⟨b, algebraMap C B g, hgq, div_mul_cancel₀ _ hgK⟩
  refine ⟨r, IsFractionRing.injective B K ?_⟩
  rw [map_mul, hr, mul_div_cancel₀ _ hgK]

/-- **A finite normal extension of a two-dimensional local ring with a DVR divisor is free.**
Let `C` be a Noetherian local integrally closed domain, `g ∈ 𝔪_C` with `(g)` prime and `C / (g)`
a discrete valuation ring with uniformizer the image of `w`, and `B` a finite extension of `C`
which is a Noetherian integrally closed domain. Then `B` is a free `C`-module. -/
theorem free_of_isDiscreteValuationRing_quotient {C B : Type u} [CommRing C] [IsDomain C]
    [IsLocalRing C] [IsNoetherianRing C] [IsIntegrallyClosed C] [CommRing B] [IsDomain B]
    [IsNoetherianRing B] [IsIntegrallyClosed B] [Algebra C B] [Module.Finite C B]
    [FaithfulSMul C B] {g w : C} (hg : g ≠ 0) (hgm : g ∈ IsLocalRing.maximalIdeal C)
    (hgprime : (Ideal.span {g}).IsPrime) (hw : w ∉ Ideal.span {g})
    [IsDiscreteValuationRing (C ⧸ Ideal.span {g})]
    (hwirr : Irreducible (Ideal.Quotient.mk (Ideal.span {g}) w)) : Module.Free C B := by
  have hinj := FaithfulSMul.algebraMap_injective C B
  have hreg : IsSMulRegular B g := by
    intro x y hxy
    simp only [Algebra.smul_def] at hxy
    exact mul_left_cancel₀ ((map_ne_zero_iff _ hinj).mpr hg) hxy
  have hjac : g ∈ (⊥ : Ideal C).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact hgm
  haveI : Module.FinitePresentation C B := Module.finitePresentation_of_finite C B
  rw [← Module.free_quotSMulTop_iff_free C B hjac hreg]
  haveI : Module.IsTorsionFree (C ⧸ Ideal.span {g}) (QuotSMulTop g B) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    have hbase : ∀ x : QuotSMulTop g B,
        Ideal.Quotient.mk (Ideal.span {g}) w • x = 0 → x = 0 := by
      intro x hx
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change (Submodule.Quotient.mk (w • b) : QuotSMulTop g B) = 0 at hx
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at hx
      obtain ⟨b', -, hb'⟩ := hx
      obtain ⟨c, hc⟩ := exists_eq_mul_of_mul_eq_mul hg hgprime hw (b := b) (b' := b')
        (by rw [← Algebra.smul_def, ← Algebra.smul_def]; exact hb'.symm)
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨c, Submodule.mem_top, by rw [hc, Algebra.smul_def]⟩
    have hpow : ∀ (n : ℕ) (x : QuotSMulTop g B),
        Ideal.Quotient.mk (Ideal.span {g}) w ^ n • x = 0 → x = 0 := by
      intro n
      induction n with
      | zero => intro x hx; simpa using hx
      | succ n ih =>
        intro x hx
        rw [pow_succ, mul_smul] at hx
        exact hbase x (ih _ hx)
    intro r x hrx
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hwirr
    apply hpow n
    have := congrArg (fun y => (↑v⁻¹ : C ⧸ Ideal.span {g}) • y) hrx
    simpa [smul_smul, ← mul_assoc] using this
  haveI : Module.Finite (C ⧸ Ideal.span {g}) (QuotSMulTop g B) :=
    Module.Finite.of_restrictScalars_finite C _ _
  exact Module.free_of_finite_type_torsion_free'

open nonZeroDivisors in
/-- **The trace-dual element of a lifted residue functional.** Let `C` be a Noetherian local
normal domain over a field `k` of characteristic zero, `g ∈ 𝔪_C` with `(g)` prime and `C / (g)` a
discrete valuation ring with uniformizer `w̄`, and `B` a finite normal extension of `C` with
separable fraction field extension `K / F`. Let `p_B` be a prime of `B` over `(g)`, locally
generated by `b₀`, and `t` in a maximal ideal `Q_B` of `B / p_B`. Then there are `y₀ ∈ B` and
`δ ∈ C ∖ 0` such that `x = y₀ / δ` satisfies the codifferent bounds `x π ∈ E B_E` at every prime
`E` over a principal prime `(π)` of `C`, `x b' ∈ E B_E` at every prime `E` over `(g)` for
`b' ∈ p_B`, and `x d = y₁ ∈ B` with `d ∉ (g)` and `N w̄ ȳ₁ = d̄ a t` in `B / p_B` for some
`N > 0` and `a ∉ Q_B`. -/
theorem exists_trace_dual_data (k : Type*) [Field k] [CharZero k] {C B F K : Type u}
    [CommRing C] [IsDomain C] [IsLocalRing C] [IsNoetherianRing C] [IsIntegrallyClosed C]
    [Algebra k C] [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    [Algebra C B] [Module.Finite C B] [FaithfulSMul C B] [Field F] [Algebra C F]
    [IsFractionRing C F] [Field K] [Algebra B K] [Algebra F K] [Algebra C K]
    [IsScalarTower C F K] [IsScalarTower C B K]
    [IsLocalization (Algebra.algebraMapSubmonoid B C⁰) K] [Algebra.IsSeparable F K]
    [FiniteDimensional F K] {g w : C} (hg : g ≠ 0) (hgm : g ∈ IsLocalRing.maximalIdeal C)
    (hgprime : (Ideal.span {g}).IsPrime) (hwg : w ∉ Ideal.span {g})
    [IsDiscreteValuationRing (C ⧸ Ideal.span {g})]
    (hwirr : Irreducible (Ideal.Quotient.mk (Ideal.span {g}) w))
    (hmax : IsLocalRing.maximalIdeal (C ⧸ Ideal.span {g}) = Ideal.span {Ideal.Quotient.mk _ w})
    (pB : Ideal B) [pB.IsPrime] (hpB : pB.comap (algebraMap C B) = Ideal.span {g})
    {b₀ : B} (hb₀ : b₀ ≠ 0) (hb₀p : b₀ ∈ pB)
    (hgen : ∀ a ∈ pB, ∃ s : B, s ∉ pB ∧ ∃ a' : B, a * s = b₀ * a')
    (QB : Ideal (B ⧸ pB)) [QB.IsMaximal] {t : B ⧸ pB} (ht : t ∈ QB) :
    ∃ (y₀ : B) (δ : C), δ ≠ 0 ∧
      (∀ (E : Ideal B) [E.IsPrime] (π : C), E.comap (algebraMap C B) = Ideal.span {π} → π ≠ 0 →
        ∃ s : B, s ∉ E ∧ ∃ a ∈ E, y₀ * algebraMap C B π * s = algebraMap C B δ * a) ∧
      (∀ (E : Ideal B) [E.IsPrime], E.comap (algebraMap C B) = Ideal.span {g} → ∀ b' ∈ pB,
        ∃ s : B, s ∉ E ∧ ∃ a ∈ E, y₀ * b' * s = algebraMap C B δ * a) ∧
      ∃ d : C, d ∉ Ideal.span {g} ∧ ∃ y₁ : B, y₁ * algebraMap C B δ = algebraMap C B d * y₀ ∧
        ∃ (N : ℕ) (a : B ⧸ pB), 0 < N ∧ a ∉ QB ∧
          (N : B ⧸ pB) * Ideal.Quotient.mk pB (algebraMap C B w) * Ideal.Quotient.mk pB y₁ =
            Ideal.Quotient.mk pB (algebraMap C B d) * (a * t) := by
  classical
  have hcz : ∀ (R' : Type u) [CommRing R'] [Nontrivial R'] [Algebra C R'], CharZero R' :=
    fun R' _ _ _ =>
      charZero_of_injective_ringHom ((algebraMap C R').comp (algebraMap k C)).injective
  haveI : Module.Free C B := free_of_isDiscreteValuationRing_quotient hg hgm hgprime hwg hwirr
  set q := Ideal.span {g} with hqdef
  letI : Algebra (C ⧸ q) (B ⧸ pB) := Ideal.Quotient.algebraQuotientOfLEComap hpB.ge
  haveI : IsScalarTower C (C ⧸ q) (B ⧸ pB) := .of_algebraMap_eq' rfl
  haveI : Module.Finite (C ⧸ q) (B ⧸ pB) := Module.Finite.of_restrictScalars_finite C _ _
  haveI : FaithfulSMul (C ⧸ q) (B ⧸ pB) := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (Ideal.quotientMap_injective' hpB.le)
  haveI : Module.Free (C ⧸ q) (B ⧸ pB) := free_of_isDiscreteValuationRing
  have hw0 : Ideal.Quotient.mk q w ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨a, haQ, hu⟩ := exists_not_mem_trace_mul_mem (O := C ⧸ q) QB ht
  obtain ⟨φ, hφp, hφ⟩ := exists_linearMap_trace_eq hmax hw0 pB hpB.ge (a * t) hu
  obtain ⟨y₀, δ, hδ, hy⟩ := exists_trace_mul_eq_mul (F := F) (K := K) φ
  haveI : CharZero (Localization.AtPrime q ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime q)) :=
    hcz _
  haveI : CharZero (Localization.AtPrime q ⧸ q.map (algebraMap C (Localization.AtPrime q))) := by
    haveI : Nontrivial (Localization.AtPrime q ⧸ q.map (algebraMap C (Localization.AtPrime q))) :=
      Ideal.Quotient.nontrivial_iff.mpr (by
        rw [Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.IsMaximal.ne_top inferInstance)
    exact hcz _
  refine ⟨y₀, δ, hδ, fun E _ π hE hπ => ?_, fun E _ hE b' hb' => ?_, ?_⟩
  · haveI : (Ideal.span {π}).IsPrime := hE ▸ Ideal.comap_isPrime _ _
    haveI : CharZero (Localization.AtPrime (Ideal.span {π}) ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {π}))) := hcz _
    exact exists_mul_mul_eq_of_trace_mem (Ideal.span {π}) rfl hπ E hE hδ fun b => ⟨φ b, hy b⟩
  · exact exists_mul_mul_eq_of_mem_of_trace_mem q rfl hg hδ hy
      (fun b => hφp _ (Ideal.mul_mem_right _ _ hb')) E hE
  · obtain ⟨d, hdq, y₁, hy₁, N, hN, key⟩ :=
      exists_mk_mul_mk_eq_nsmul_trace q rfl hg pB hpB hδ hy hφp hb₀ hb₀p hgen
    refine ⟨d, hdq, y₁, hy₁, N, a, hN, haQ, ?_⟩
    haveI : CharZero (C ⧸ q) := by
      haveI : Nontrivial (C ⧸ q) := Ideal.Quotient.nontrivial_iff.mpr hgprime.ne_top
      exact hcz _
    let bas := Module.Free.chooseBasis (C ⧸ q) (B ⧸ pB)
    have hdisc := discr_ne_zero_of_charZero bas
    let ψ : B ⧸ pB → C ⧸ q := fun r =>
      Ideal.Quotient.mk q (φ (Ideal.Quotient.mk_surjective r).choose)
    have hψ : ∀ b, ψ (Ideal.Quotient.mk pB b) = Ideal.Quotient.mk q (φ b) := by
      intro b
      simp only [ψ]
      rw [Ideal.Quotient.eq, ← map_sub]
      apply hφp
      rw [← Ideal.Quotient.eq]
      exact (Ideal.Quotient.mk_surjective (Ideal.Quotient.mk pB b)).choose_spec
    have h₁ : ∀ r, Ideal.Quotient.mk q d * ψ r =
        N • Algebra.trace (C ⧸ q) (B ⧸ pB) (Ideal.Quotient.mk pB y₁ * r) := by
      intro r
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective r
      rw [hψ, key, map_mul]
    have h₂ : ∀ r, Ideal.Quotient.mk q w * ψ r =
        Algebra.trace (C ⧸ q) (B ⧸ pB) (a * t * r) := by
      intro r
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective r
      rw [hψ, hφ]
    exact natCast_mul_algebraMap_mul_eq bas hdisc h₁ h₂

/-- **The localization at `(x₀, w)`.** Let `D` be a domain, `x₀ ≠ 0` generating a prime, and
`w ∉ (x₀)` with `v = (x₀, w)` prime. In `C = D_v` the element `g = x₀` is a nonzero element of
`𝔪_C` generating a prime, `w ∉ (g)` and `𝔪_C = (g, w)`. -/
theorem localization_span_pair_facts {D : Type*} [CommRing D] [IsDomain D] {x₀ w : D}
    (hx₀ : x₀ ≠ 0) (hx₀p : (Ideal.span {x₀}).IsPrime) (hw : w ∉ Ideal.span {x₀})
    [(Ideal.span {x₀, w} : Ideal D).IsPrime] (C : Type*) [CommRing C] [IsLocalRing C]
    [Algebra D C] [IsLocalization.AtPrime C (Ideal.span {x₀, w} : Ideal D)] :
    algebraMap D C x₀ ≠ 0 ∧ algebraMap D C x₀ ∈ IsLocalRing.maximalIdeal C ∧
      (Ideal.span {algebraMap D C x₀}).IsPrime ∧ algebraMap D C w ∉ Ideal.span {algebraMap D C x₀} ∧
      IsLocalRing.maximalIdeal C = Ideal.span {algebraMap D C x₀, algebraMap D C w} := by
  have hXv : x₀ ∈ (Ideal.span {x₀, w} : Ideal D) := Ideal.subset_span (by simp)
  have hdisj : Disjoint ((Ideal.span {x₀, w} : Ideal D).primeCompl : Set D)
      ((Ideal.span {x₀} : Ideal D) : Set D) := by
    rw [Set.disjoint_left]
    intro a ha h
    exact ha ((Ideal.span_le.mpr (by simpa using hXv)) h)
  have hinj : Function.Injective (algebraMap D C) :=
    IsLocalization.injective C (Ideal.span {x₀, w} : Ideal D).primeCompl_le_nonZeroDivisors
  have hgspan : Ideal.span {algebraMap D C x₀} = (Ideal.span {x₀}).map (algebraMap D C) := by
    rw [Ideal.map_span, Set.image_singleton]
  have hcomap : (Ideal.span {algebraMap D C x₀}).comap (algebraMap D C) = Ideal.span {x₀} := by
    rw [hgspan]; exact IsLocalization.comap_map_of_isPrime_disjoint _ C hx₀p hdisj
  refine ⟨fun h => hx₀ (hinj (by rwa [map_zero])),
    (IsLocalization.AtPrime.to_map_mem_maximal_iff C _ _).mpr hXv, ?_, fun h => hw ?_, ?_⟩
  · rw [hgspan]; exact IsLocalization.isPrime_of_isPrime_disjoint _ C _ hx₀p hdisj
  · rw [← hcomap]; exact h
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {x₀, w} : Ideal D) C,
      Ideal.map_span, Set.image_pair]

/-- **A quotient of a local ring that is a discrete valuation ring.** If `C` is a Noetherian local
ring, `(g)` a prime and `𝔪_C = (g, w)` with `w ∉ (g)`, then `C / (g)` is a discrete valuation ring
with uniformizer `w̄`. -/
theorem isDiscreteValuationRing_quotient_span {C : Type*} [CommRing C] [IsLocalRing C]
    [IsNoetherianRing C] {g w : C} [(Ideal.span {g}).IsPrime]
    (hmaxC : IsLocalRing.maximalIdeal C = Ideal.span {g, w}) (hwg : w ∉ Ideal.span {g}) :
    ∃ _ : IsLocalRing (C ⧸ Ideal.span {g}),
      IsLocalRing.maximalIdeal (C ⧸ Ideal.span {g}) = Ideal.span {Ideal.Quotient.mk _ w} ∧
      IsDiscreteValuationRing (C ⧸ Ideal.span {g}) ∧
      Irreducible (Ideal.Quotient.mk (Ideal.span {g}) w) := by
  have hgprime : (Ideal.span {g}).IsPrime := inferInstance
  haveI : IsLocalRing (C ⧸ Ideal.span {g}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hmax : IsLocalRing.maximalIdeal (C ⧸ Ideal.span {g}) =
      Ideal.span {Ideal.Quotient.mk _ w} := by
    have h1 : ((IsLocalRing.maximalIdeal C).map (Ideal.Quotient.mk (Ideal.span {g}))).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by
        rw [Ideal.mk_ker]
        exact IsLocalRing.le_maximalIdeal hgprime.ne_top)
    rw [← IsLocalRing.eq_maximalIdeal h1, hmaxC, Ideal.map_span, Set.image_pair,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self g), Ideal.span_insert_zero]
  have hw0 : Ideal.Quotient.mk (Ideal.span {g}) w ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hnf : ¬ IsField (C ⧸ Ideal.span {g}) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]; exact hw0
  have hp : (IsLocalRing.maximalIdeal (C ⧸ Ideal.span {g})).IsPrincipal := ⟨⟨_, hmax⟩⟩
  have hdvr : IsDiscreteValuationRing (C ⧸ Ideal.span {g}) :=
    ((IsDiscreteValuationRing.TFAE (C ⧸ Ideal.span {g}) hnf).out 1 5).mpr hp
  exact ⟨inferInstance, hmax, hdvr,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer
      (Ideal.Quotient.mk (Ideal.span {g}) w)).mpr hmax⟩

/-- A local ring `A` that is a localization of `R` at a prime is also the localization of any
subring `B ⊆ A` containing the image of `R`, at the contraction of `𝔪_A`. -/
theorem isLocalization_atPrime_comap_maximalIdeal {R B A : Type*} [CommRing R] [CommRing B]
    [CommRing A] [IsLocalRing A] [Algebra R A] [Algebra B A] (𝔮 : Ideal R) [𝔮.IsPrime]
    [IsLocalization.AtPrime A 𝔮] (hB : Function.Injective (algebraMap B A))
    (hR : ∀ r, ∃ b, algebraMap B A b = algebraMap R A r) :
    IsLocalization.AtPrime A ((IsLocalRing.maximalIdeal A).comap (algebraMap B A)) where
  map_units b := by
    by_contra h
    exact b.2 ((IsLocalRing.mem_maximalIdeal _).mpr h)
  surj z := by
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj 𝔮.primeCompl z
    obtain ⟨br, hbr⟩ := hR r
    obtain ⟨bs, hbs⟩ := hR s
    have hs : IsUnit (algebraMap R A s) := IsLocalization.map_units A s
    refine ⟨⟨br, ⟨bs, fun h => ?_⟩⟩, ?_⟩
    · rw [SetLike.mem_coe, Ideal.mem_comap, hbs, IsLocalRing.mem_maximalIdeal,
        mem_nonunits_iff] at h
      exact h hs
    · simp only
      rw [hbs, hbr]; exact hrs
  exists_of_eq h := ⟨1, by simp [hB h]⟩

/-- A prime strictly inside a prime `E` with `A_E` a discrete valuation ring is zero. -/
private theorem eq_bot_of_lt_of_isDiscreteValuationRing {A : Type*} [CommRing A] [IsDomain A]
    (E : Ideal A) [E.IsPrime] (hE : IsDiscreteValuationRing (Localization.AtPrime E))
    (P : Ideal A) [P.IsPrime] (hPE : P < E) : P = ⊥ := by
  have hdisj : Disjoint (E.primeCompl : Set A) (P : Set A) := by
    rw [Set.disjoint_left]; exact fun a ha hP => ha (hPE.le hP)
  have hP' := IsLocalization.isPrime_of_isPrime_disjoint E.primeCompl (Localization.AtPrime E) P
    inferInstance hdisj
  have hcomap := IsLocalization.comap_map_of_isPrime_disjoint E.primeCompl
    (Localization.AtPrime E) (I := P) inferInstance hdisj
  by_cases h0 : P.map (algebraMap A (Localization.AtPrime E)) = ⊥
  · rw [← hcomap, h0]
    exact Ideal.comap_bot_of_injective _
      (IsLocalization.injective _ E.primeCompl_le_nonZeroDivisors)
  · have hmax := hP'.isMaximal h0
    have h1 := IsLocalRing.eq_maximalIdeal hmax
    rw [h1, Localization.AtPrime.comap_maximalIdeal] at hcomap
    exact absurd hcomap.symm hPE.ne

/-- **The contraction of a height-one prime to a factorial base is principal.** Let `A` be the
localization of a domain `R`, integral over a factorial domain `D`, at a prime. For a prime `E` of
`A` with `A_E` a discrete valuation ring, `E ∩ D = (π)` with `π ≠ 0`, and every prime of `D`
strictly
inside `E ∩ D` is zero. -/
theorem exists_comap_eq_span_singleton {D R A : Type*} [CommRing D] [IsDomain D]
    [UniqueFactorizationMonoid D] [CommRing R] [IsDomain R] [Algebra D R]
    [Algebra.IsIntegral D R] [FaithfulSMul D R] [CommRing A] [IsDomain A] [IsLocalRing A]
    [Algebra D A] [Algebra R A] [IsScalarTower D R A] (𝔮 : Ideal R) [𝔮.IsPrime]
    [IsLocalization.AtPrime A 𝔮] (E : Ideal A) [E.IsPrime]
    (hE : IsDiscreteValuationRing (Localization.AtPrime E)) :
    ∃ π : D, π ≠ 0 ∧ E.comap (algebraMap D A) = Ideal.span {π} ∧
      ∀ 𝔞 : Ideal D, 𝔞.IsPrime → 𝔞 < E.comap (algebraMap D A) → 𝔞 = ⊥ := by
  classical
  have hRA : Function.Injective (algebraMap R A) :=
    IsLocalization.injective A 𝔮.primeCompl_le_nonZeroDivisors
  set ER := E.comap (algebraMap R A) with hERdef
  have hq' : E.comap (algebraMap D A) = ER.comap (algebraMap D R) := by
    rw [hERdef, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  -- `E ≠ ⊥`
  have hE0 : E ≠ ⊥ := by
    intro h
    apply IsDiscreteValuationRing.not_a_field (Localization.AtPrime E)
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    rw [eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro x hx
    have hx0 : x = 0 := by rw [h] at hx; exact hx
    rw [hx0]; exact zero_mem _
  have hER : ER ≤ 𝔮 := by
    intro r hr
    by_contra h
    have hu : IsUnit (algebraMap R A r) := IsLocalization.map_units A (⟨r, h⟩ : 𝔮.primeCompl)
    exact (Ideal.IsPrime.ne_top inferInstance)
      (Ideal.eq_top_of_isUnit_mem E (Ideal.mem_comap.mp hr) hu)
  have hdisjR : ∀ P : Ideal R, P ≤ ER → Disjoint (𝔮.primeCompl : Set R) (P : Set R) :=
    fun P hP => by
      rw [Set.disjoint_left]; exact fun a ha h => ha (hER (hP h))
  -- `E ∩ R ≠ ⊥`
  have hER0 : ER ≠ ⊥ := by
    intro h
    apply hE0
    rw [← IsLocalization.map_comap 𝔮.primeCompl A E]
    show Ideal.map _ ER = ⊥
    rw [h, Ideal.map_bot]
  obtain ⟨r, hrE, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hER0
  have hq'0 : E.comap (algebraMap D A) ≠ ⊥ := by
    rw [hq']; exact Ideal.comap_ne_bot_of_integral_mem hr0 hrE (Algebra.IsIntegral.isIntegral r)
  -- no prime strictly inside
  have hmin : ∀ 𝔞 : Ideal D, 𝔞.IsPrime → 𝔞 < E.comap (algebraMap D A) → 𝔞 = ⊥ := by
    intro 𝔞 h𝔞 hlt
    haveI : ER.LiesOver (ER.comap (algebraMap D R)) := ⟨rfl⟩
    obtain ⟨P, hPle, hPprime, hPlies⟩ :=
      Ideal.exists_ideal_le_liesOver_of_le (p := 𝔞) ER (hq' ▸ hlt.le)
    have hPne : P ≠ ER := by
      rintro rfl
      apply hlt.ne
      rw [hq']
      exact hPlies.over
    have hPA := IsLocalization.isPrime_of_isPrime_disjoint 𝔮.primeCompl A P hPprime
      (hdisjR P hPle)
    have hPAc := IsLocalization.comap_map_of_isPrime_disjoint 𝔮.primeCompl A (I := P) hPprime
      (hdisjR P hPle)
    have hlt' : P.map (algebraMap R A) < E := by
      refine lt_of_le_of_ne ?_ fun h => hPne ?_
      · rw [Ideal.map_le_iff_le_comap]; exact hPle
      · rw [← hPAc, h]
    have h0 := eq_bot_of_lt_of_isDiscreteValuationRing E hE _ hlt'
    have hP0 : P = ⊥ := by
      rw [← hPAc, h0]
      exact Ideal.comap_bot_of_injective _ hRA
    rw [hPlies.over, hP0]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective D R)
  obtain ⟨π, hπ0, hπ⟩ := exists_eq_span_singleton_of_forall_lt _ hq'0 hmin
  exact ⟨π, hπ0, hπ, hmin⟩

/-- The prime `p` of a domain `A` with `A_p` a discrete valuation ring is nonzero. -/
private theorem ne_bot_of_isDiscreteValuationRing_localization {A : Type*} [CommRing A]
    [IsDomain A] (p : Ideal A) [p.IsPrime] (hp : IsDiscreteValuationRing (Localization.AtPrime p)) :
    p ≠ ⊥ := by
  rintro rfl
  apply IsDiscreteValuationRing.not_a_field (Localization.AtPrime (⊥ : Ideal A))
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_bot]

/-- A prime `c ⊇ p` of a local ring `A` with `A / p` a discrete valuation ring is `p` or the
maximal ideal. -/
private theorem eq_or_eq_maximalIdeal_of_le {A : Type*} [CommRing A] [IsLocalRing A]
    (p : Ideal A) [p.IsPrime] [IsDomain (A ⧸ p)] [IsDiscreteValuationRing (A ⧸ p)]
    (c : Ideal A) [c.IsPrime] (hpc : p ≤ c) : c = p ∨ c = IsLocalRing.maximalIdeal A := by
  have hker : RingHom.ker (Ideal.Quotient.mk p) ≤ c := by rw [Ideal.mk_ker]; exact hpc
  haveI : (c.map (Ideal.Quotient.mk p)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hcomap : (c.map (Ideal.Quotient.mk p)).comap (Ideal.Quotient.mk p) = c := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hpc]
  rcases (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime (A ⧸ p)).mp inferInstance with
    ⟨-, ⟨P, ⟨hP0, hPp⟩, huniq⟩⟩
  by_cases h0 : c.map (Ideal.Quotient.mk p) = ⊥
  · left
    rw [← hcomap, h0, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  · right
    have hmax : (c.map (Ideal.Quotient.mk p)).IsMaximal := by
      have h1 := huniq _ ⟨h0, inferInstance⟩
      have h2 := huniq (IsLocalRing.maximalIdeal (A ⧸ p))
        ⟨IsDiscreteValuationRing.not_a_field _, inferInstance⟩
      rw [h1, ← h2]; exact IsLocalRing.maximalIdeal.isMaximal _
    rw [← hcomap]
    exact IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _
      Ideal.Quotient.mk_surjective)

/-- **Noether normalization adapted to a local flag.** Let `R` be a domain of finite type over an
infinite field `k`, `A = R_𝔮`, and `p` a prime of `A` with `A_p` and `A / p` discrete valuation
rings. Then there is a finite injective `ν : k[X₀, …, X_s] → R` with `p ∩ k[X] = (X₀)` and
`𝔪_A ∩ k[X] = (X₀, w(X₁, …, X_s))`, `w ≠ 0`, where `w(X₁, …, X_s) ∈ 𝔪_A` exactly for
`a ∈ (w)`. -/
private theorem exists_finite_comap_eq_span_X_zero_of_isLocalization {k R A : Type*} [Field k]
    [Infinite k] [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R] [CommRing A]
    [IsDomain A] [IsLocalRing A] [Algebra R A] (𝔮 : Ideal R) [𝔮.IsPrime]
    [IsLocalization.AtPrime A 𝔮] (p : Ideal A) [p.IsPrime]
    (hpA : IsDiscreteValuationRing (Localization.AtPrime p)) [IsDomain (A ⧸ p)]
    [IsDiscreteValuationRing (A ⧸ p)] :
    ∃ (s : ℕ) (ν : MvPolynomial (Fin (s + 1)) k →ₐ[k] R), Function.Injective ν ∧
      ν.toRingHom.IsIntegral ∧
      p.comap ((algebraMap R A).comp ν.toRingHom) = Ideal.span {MvPolynomial.X 0} ∧
      ∃ w' : MvPolynomial (Fin s) k, w' ≠ 0 ∧
        MvPolynomial.rename Fin.succ w' ∉
          Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (s + 1)) k)} ∧
        (IsLocalRing.maximalIdeal A).comap ((algebraMap R A).comp ν.toRingHom) =
          Ideal.span {MvPolynomial.X 0, MvPolynomial.rename Fin.succ w'} ∧
        ∀ a, MvPolynomial.rename Fin.succ a ∈ (IsLocalRing.maximalIdeal A).comap
          ((algebraMap R A).comp ν.toRingHom) ↔ a ∈ Ideal.span {w'} := by
  classical
  have hm : (IsLocalRing.maximalIdeal A).comap (algebraMap R A) = 𝔮 :=
    IsLocalization.AtPrime.comap_maximalIdeal A 𝔮
  have hdisj : ∀ c : Ideal R, c ≤ 𝔮 → Disjoint (𝔮.primeCompl : Set R) (c : Set R) := fun c hc => by
    rw [Set.disjoint_left]; exact fun a ha h => ha (hc h)
  set pR := p.comap (algebraMap R A) with hpR
  haveI : pR.IsPrime := Ideal.comap_isPrime _ _
  have hpm : p ≤ IsLocalRing.maximalIdeal A :=
    IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  have hpRq : pR ≤ 𝔮 := hm ▸ Ideal.comap_mono hpm
  have hmapR : ∀ c : Ideal A, (c.comap (algebraMap R A)).map (algebraMap R A) = c :=
    fun c => IsLocalization.map_comap 𝔮.primeCompl A c
  have hp0 := ne_bot_of_isDiscreteValuationRing_localization p hpA
  have hpR0 : pR ≠ ⊥ := fun h => hp0 (by rw [← hmapR p, ← hpR, h, Ideal.map_bot])
  have hpmax : p ≠ IsLocalRing.maximalIdeal A := by
    intro h
    apply IsDiscreteValuationRing.not_a_field (A ⧸ p)
    have : (IsLocalRing.maximalIdeal (A ⧸ p)) = (IsLocalRing.maximalIdeal A).map
        (Ideal.Quotient.mk p) := by
      symm
      apply IsLocalRing.eq_maximalIdeal
      exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker, h])
    rw [this, ← h, Ideal.map_quotient_self]
  have hpRlt : pR < 𝔮 := by
    refine lt_of_le_of_ne hpRq fun h => hpmax ?_
    rw [← hmapR p, ← hpR, h, ← hm, hmapR]
  have hbelow : ∀ c : Ideal R, c.IsPrime → c < pR → c = ⊥ := by
    intro c hc hlt
    have hc' := IsLocalization.isPrime_of_isPrime_disjoint 𝔮.primeCompl A c hc
      (hdisj c (hlt.le.trans hpRq))
    have hcc := IsLocalization.comap_map_of_isPrime_disjoint 𝔮.primeCompl A (I := c) hc
      (hdisj c (hlt.le.trans hpRq))
    have hlt' : c.map (algebraMap R A) < p := by
      refine lt_of_le_of_ne (by rw [Ideal.map_le_iff_le_comap]; exact hlt.le) fun h => hlt.ne ?_
      rw [← hcc, h]
    have := eq_bot_of_lt_of_isDiscreteValuationRing p hpA _ hlt'
    rw [← hcc, this]
    exact Ideal.comap_bot_of_injective _
      (IsLocalization.injective A 𝔮.primeCompl_le_nonZeroDivisors)
  have habove : ∀ c : Ideal R, c.IsPrime → pR < c → c ≤ 𝔮 → c = 𝔮 := by
    intro c hc hlt hcq
    have hc' := IsLocalization.isPrime_of_isPrime_disjoint 𝔮.primeCompl A c hc (hdisj c hcq)
    have hcc := IsLocalization.comap_map_of_isPrime_disjoint 𝔮.primeCompl A (I := c) hc
      (hdisj c hcq)
    have hle : p ≤ c.map (algebraMap R A) := by
      rw [← hmapR p]; exact Ideal.map_mono hlt.le
    rcases eq_or_eq_maximalIdeal_of_le p (c.map (algebraMap R A)) hle with h | h
    · exfalso; apply hlt.ne'; rw [← hcc, h]
    · rw [← hcc, h]; exact hm
  obtain ⟨s, ν, hν, hνint, hpX, w', hw'0, hw'X, hv, hiff⟩ :=
    exists_finite_comap_eq_span_X_zero (k := k) pR 𝔮 hpR0 hpRlt hbelow habove
  refine ⟨s, ν, hν, hνint, ?_, w', hw'0, hw'X, ?_, ?_⟩
  · rw [← Ideal.comap_comap]; exact hpX
  · rw [← Ideal.comap_comap, hm]; exact hv
  · intro a; rw [← Ideal.comap_comap, hm]; exact hiff a

open nonZeroDivisors in
/-- **The ring-level residue lift.** Let `A` be a normal local domain over a field `k` of
characteristic zero, the localization of a domain `R` finite over a factorial Noetherian domain
`D`, with fraction field `K`. Let `p ⊆ A` be a prime with `A_p` and `A / p` discrete valuation
rings, `x₀ ∈ D` generating a prime with `p ∩ D = (x₀)` and `𝔪_A ∩ D = (x₀, w)`, `w ∉ (x₀)`. Then
there is `F ∈ K` such that `F π` lies in `E A_E` at every other prime `E` of `A` with `A_E` a
discrete valuation ring and `E ∩ D = (π)`, `F x₀ = a / s` with `s ∉ p`, and
`N w̄ ā = s̄ u` in `A / p` for some `N > 0` and some uniformizer `u` of `A / p`. -/
theorem exists_residue_lift_ring (k : Type u) [Field k] [CharZero k]
    {D R A K : Type u} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D]
    [IsNoetherianRing D] [Algebra k D] [CommRing R] [IsDomain R] [Algebra D R]
    [Module.Finite D R] [FaithfulSMul D R] [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegrallyClosed A] [Algebra D A] [Algebra R A] [IsScalarTower D R A]
    (𝔮 : Ideal R) [𝔮.IsPrime] [IsLocalization.AtPrime A 𝔮] [Field K] [Algebra A K]
    [IsFractionRing A K] [Algebra D K] [IsScalarTower D A K] [Algebra R K] [IsScalarTower R A K]
    [IsFractionRing R K]
    (p : Ideal A) [p.IsPrime] (hpA : IsDiscreteValuationRing (Localization.AtPrime p))
    [IsDiscreteValuationRing (A ⧸ p)] {x₀ w : D} (hx₀ : x₀ ≠ 0)
    (hx₀p : (Ideal.span {x₀}).IsPrime) (hpX : p.comap (algebraMap D A) = Ideal.span {x₀})
    (hw : w ∉ Ideal.span {x₀})
    (hv : (IsLocalRing.maximalIdeal A).comap (algebraMap D A) = Ideal.span {x₀, w}) :
    ∃ F : K,
      (∀ (E : Ideal A) [E.IsPrime], IsDiscreteValuationRing (Localization.AtPrime E) → E ≠ p →
        ∃ π : D, π ≠ 0 ∧ E.comap (algebraMap D A) = Ideal.span {π} ∧
          ∃ s ∉ E, ∃ a ∈ E, F * algebraMap D K π * algebraMap A K s = algebraMap A K a) ∧
      ∃ s a : A, s ∉ p ∧ F * algebraMap D K x₀ * algebraMap A K s = algebraMap A K a ∧
        ∃ (N : ℕ) (u : A ⧸ p), 0 < N ∧ u ∈ IsLocalRing.maximalIdeal (A ⧸ p) ∧
          u ∉ IsLocalRing.maximalIdeal (A ⧸ p) ^ 2 ∧
          (N : A ⧸ p) * Ideal.Quotient.mk p (algebraMap D A w) * Ideal.Quotient.mk p a =
            Ideal.Quotient.mk p s * u := by
  classical
  -- injectivity
  have hRA : Function.Injective (algebraMap R A) :=
    IsLocalization.injective A 𝔮.primeCompl_le_nonZeroDivisors
  have hDR : Function.Injective (algebraMap D R) := FaithfulSMul.algebraMap_injective D R
  have hDA : Function.Injective (algebraMap D A) := by
    rw [IsScalarTower.algebraMap_eq D R A]; exact hRA.comp hDR
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  -- the regular base `C = D_v`
  haveI : (Ideal.span {x₀, w} : Ideal D).IsPrime := hv ▸ Ideal.comap_isPrime _ _
  let C := Localization.AtPrime (Ideal.span {x₀, w} : Ideal D)
  have hunits : ∀ s : (Ideal.span {x₀, w} : Ideal D).primeCompl, IsUnit (algebraMap D A s) :=
    fun s => by
      by_contra h
      have h1 : (s : D) ∈ (IsLocalRing.maximalIdeal A).comap (algebraMap D A) :=
        (IsLocalRing.mem_maximalIdeal _).mpr h
      rw [hv] at h1
      exact s.2 h1
  letI : Algebra C A := (IsLocalization.lift hunits).toAlgebra
  haveI : IsScalarTower D C A :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunits x).symm
  letI : Algebra C K := ((algebraMap A K).comp (algebraMap C A)).toAlgebra
  haveI : IsScalarTower C A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower D C K := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply D A K, IsScalarTower.algebraMap_apply D C A]; rfl
  haveI : IsNoetherianRing C :=
    IsLocalization.isNoetherianRing (Ideal.span {x₀, w} : Ideal D).primeCompl C inferInstance
  haveI : IsIntegrallyClosed C := isIntegrallyClosed_of_isLocalization C
    (Ideal.span {x₀, w} : Ideal D).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)
  have hCA : Function.Injective (algebraMap C A) :=
    (IsLocalization.lift_injective_iff hunits).mpr fun x y =>
      (IsLocalization.injective C
        (Ideal.span {x₀, w} : Ideal D).primeCompl_le_nonZeroDivisors).eq_iff.trans
        hDA.eq_iff.symm
  obtain ⟨hg0, hgm, hgprime, hwg, hmaxC⟩ := localization_span_pair_facts hx₀ hx₀p hw C
  haveI := hgprime
  obtain ⟨_, hmax, hdvr, hwirr⟩ := isDiscreteValuationRing_quotient_span hmaxC hwg
  haveI := hdvr
  -- the fraction field `F` of `D` and of `C`
  let F := FractionRing D
  have hDK : Function.Injective (algebraMap D K) := by
    rw [IsScalarTower.algebraMap_eq D A K]; exact hAK.comp hDA
  haveI : FaithfulSMul D K := (faithfulSMul_iff_algebraMap_injective D K).mpr hDK
  letI : Algebra F K := FractionRing.liftAlgebra D K
  haveI : IsScalarTower D F K := FractionRing.isScalarTower_liftAlgebra D K
  have hunitsF : ∀ s : (Ideal.span {x₀, w} : Ideal D).primeCompl, IsUnit (algebraMap D F s) :=
    fun s => IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective D F)).mpr
      (nonZeroDivisors.ne_zero ((Ideal.primeCompl_le_nonZeroDivisors _) s.2)))
  letI : Algebra C F := (IsLocalization.lift hunitsF).toAlgebra
  haveI : IsScalarTower D C F :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunitsF x).symm
  haveI : IsFractionRing C F := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Ideal.span {x₀, w} : Ideal D).primeCompl C F
  have hCFK : (algebraMap F K).comp (algebraMap C F) = algebraMap C K :=
    IsLocalization.ringHom_ext (Ideal.span {x₀, w} : Ideal D).primeCompl (RingHom.ext fun x => by
      simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply])
  haveI : IsScalarTower C F K :=
    IsScalarTower.of_algebraMap_eq fun c => (RingHom.congr_fun hCFK c).symm
  haveI : IsScalarTower D R K := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply R A K, ← IsScalarTower.algebraMap_apply D R A,
      ← IsScalarTower.algebraMap_apply D A K]
  haveI : Algebra.IsAlgebraic D R := Algebra.IsAlgebraic.of_finite D R
  haveI : Module.Finite F K := Module.Finite.of_isLocalization D R (Rₚ := F) (Sₚ := K) D⁰
  haveI : CharZero F :=
    charZero_of_injective_ringHom ((algebraMap D F).comp (algebraMap k D)).injective
  haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.of_finite F K
  haveI : Algebra.IsSeparable F K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  -- the integral closure `B` of `C` in `A`
  let B := integralClosure C A
  have hBA : Function.Injective (algebraMap B A) := Subtype.val_injective
  have hBK : Function.Injective (algebraMap B K) := hAK.comp hBA
  haveI : IsIntegralClosure B C K := by
    refine ⟨hBK, fun {x} => ⟨fun hx => ?_, ?_⟩⟩
    · obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hx.tower_top (A := A))
      exact ⟨⟨a, (isIntegral_algHom_iff (IsScalarTower.toAlgHom C A K) hAK).mp hx⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact b.2.map (IsScalarTower.toAlgHom C A K)
  haveI : Module.Finite C B := IsIntegralClosure.finite C F K B
  haveI : IsFractionRing B K := IsIntegralClosure.isFractionRing_of_finite_extension C F K B
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B C⁰) K :=
    IsIntegralClosure.isLocalization C F K B
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing C B
  haveI : Algebra.IsIntegral C B := Algebra.IsIntegral.of_finite C B
  haveI : IsIntegrallyClosed B := (isIntegrallyClosed_iff K).mpr fun {x} hx =>
    IsIntegralClosure.isIntegral_iff.mp (isIntegral_trans (R := C) x hx)
  haveI : FaithfulSMul C B := (faithfulSMul_iff_algebraMap_injective C B).mpr fun x y h => hCA (by
    rw [IsScalarTower.algebraMap_apply C B A, h, ← IsScalarTower.algebraMap_apply])
  -- `A` is the localization of `B` at `𝔐 = 𝔪_A ∩ B`
  set 𝔐 := (IsLocalRing.maximalIdeal A).comap (algebraMap B A) with h𝔐def
  have hRB : ∀ r : R, ∃ b : B, algebraMap B A b = algebraMap R A r := fun r =>
    ⟨⟨algebraMap R A r, ((Algebra.IsIntegral.isIntegral (R := D) r).map
      (IsScalarTower.toAlgHom D R A)).tower_top⟩, rfl⟩
  haveI : IsLocalization.AtPrime A 𝔐 := isLocalization_atPrime_comap_maximalIdeal 𝔮 hBA hRB
  -- the prime `p_B` of `B` below `p`, over `(g)`
  set pB := p.comap (algebraMap B A) with hpBdef
  have hpCA : p.comap (algebraMap C A) = Ideal.span {algebraMap D C x₀} := by
    rw [← IsLocalization.map_comap (Ideal.span {x₀, w} : Ideal D).primeCompl C
      (p.comap (algebraMap C A)), Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
      hpX, Ideal.map_span, Set.image_singleton]
  have hpB : pB.comap (algebraMap C B) = Ideal.span {algebraMap D C x₀} := by
    rw [hpBdef, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, hpCA]
  -- a local generator `b₀` of `p_B`
  haveI : IsLocalization.AtPrime (Localization.AtPrime p) pB :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization 𝔐.primeCompl
      (Localization.AtPrime p) p
  have hBT : Function.Injective (algebraMap B (Localization.AtPrime p)) :=
    IsLocalization.injective _ pB.primeCompl_le_nonZeroDivisors
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
  obtain ⟨⟨b₀, s₀⟩, hb₀s⟩ := IsLocalization.mk'_surjective pB.primeCompl ϖ
  simp only at hb₀s
  have hb₀T : algebraMap B (Localization.AtPrime p) b₀ =
      ϖ * algebraMap B (Localization.AtPrime p) s₀ := by
    rw [← hb₀s, IsLocalization.mk'_spec]
  have hs₀u : IsUnit (algebraMap B (Localization.AtPrime p) s₀) :=
    IsLocalization.map_units _ s₀
  have hb₀ : b₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hb₀T
    exact hϖ.ne_zero ((mul_eq_zero.mp hb₀T.symm).resolve_right hs₀u.ne_zero)
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := hϖ.not_isUnit
  have hb₀p : b₀ ∈ pB := by
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) pB, hb₀T]
    exact Ideal.mul_mem_right _ _ hϖm
  have hgen : ∀ a ∈ pB, ∃ s : B, s ∉ pB ∧ ∃ a' : B, a * s = b₀ * a' := by
    intro a ha
    have h1 : algebraMap B (Localization.AtPrime p) a ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) pB a).mpr ha
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
      Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    obtain ⟨⟨b₂, s₂⟩, hb₂s⟩ := IsLocalization.mk'_surjective pB.primeCompl c
    simp only at hb₂s
    refine ⟨s₂ * s₀, pB.primeCompl.mul_mem s₂.2 s₀.2, b₂, hBT ?_⟩
    rw [map_mul, map_mul, map_mul, hb₀T, ← hc, ← hb₂s, ← IsLocalization.mk'_spec
      (Localization.AtPrime p) b₂ s₂]
    ring
  -- `𝔐` is maximal
  have hmCA : (IsLocalRing.maximalIdeal A).comap (algebraMap C A) = IsLocalRing.maximalIdeal C := by
    rw [← IsLocalization.map_comap (Ideal.span {x₀, w} : Ideal D).primeCompl C
      ((IsLocalRing.maximalIdeal A).comap (algebraMap C A)), Ideal.under, Ideal.comap_comap,
      ← IsScalarTower.algebraMap_eq, hv, Localization.AtPrime.map_eq_maximalIdeal]
  haveI h𝔐max : 𝔐.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := C)
    rw [Ideal.under_def, h𝔐def, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, hmCA]
    exact IsLocalRing.maximalIdeal.isMaximal C
  have hpB𝔐 : pB ≤ 𝔐 :=
    Ideal.comap_mono (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
  set QB := 𝔐.map (Ideal.Quotient.mk pB) with hQBdef
  haveI : QB.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by rwa [Ideal.mk_ker])
  -- an element `t ∈ Q_B` mapping to a uniformizer of `A / p` times a unit
  let φBA : B ⧸ pB →+* A ⧸ p := Ideal.quotientMap p (algebraMap B A) le_rfl
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible (A ⧸ p)
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective ϖ'
  obtain ⟨⟨b', s'⟩, hb's⟩ := IsLocalization.surj 𝔐.primeCompl a'
  simp only at hb's
  have hs'u : IsUnit (Ideal.Quotient.mk p (algebraMap B A s')) :=
    (IsLocalization.map_units A s').map _
  have hφt : φBA (Ideal.Quotient.mk pB b') =
      Ideal.Quotient.mk p a' * Ideal.Quotient.mk p (algebraMap B A s') := by
    rw [Ideal.quotientMap_mk, ← hb's, map_mul]
  have ht : Ideal.Quotient.mk pB b' ∈ QB := by
    refine Ideal.mem_map_of_mem _ ?_
    show algebraMap B A b' ∈ IsLocalRing.maximalIdeal A
    rw [← hb's]
    refine Ideal.mul_mem_right _ _ ?_
    by_contra h
    have hu : IsUnit a' := (IsLocalRing.notMem_maximalIdeal.mp h)
    exact hϖ'.not_isUnit (hu.map _)
  -- the trace-dual data
  obtain ⟨y₀, δ, hδ, H1, H2, d, hdq, y₁, hy₁, N, a₁, hN, ha₁, hrel⟩ :=
    exists_trace_dual_data k (F := F) (K := K) hg0 hgm hgprime hwg hwirr hmax pB hpB hb₀ hb₀p
      hgen QB ht
  have hδK : algebraMap C K δ ≠ 0 := by
    intro h; apply hδ; apply hCA; apply hAK; rw [map_zero, map_zero]; exact h
  have hx₀K : algebraMap D K x₀ ≠ 0 := (map_ne_zero_iff _ hDK).mpr hx₀
  have hCBK : ∀ c : C, algebraMap B K (algebraMap C B c) = algebraMap C K c :=
    fun c => (IsScalarTower.algebraMap_apply C B K c).symm
  have hDCK : ∀ x : D, algebraMap C K (algebraMap D C x) = algebraMap D K x :=
    fun x => (IsScalarTower.algebraMap_apply D C K x).symm
  have hcomapEB : ∀ E : Ideal A, ((E.comap (algebraMap B A)).comap (algebraMap C B)).comap
      (algebraMap D C) = E.comap (algebraMap D A) := fun E => by
    ext x
    simp only [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
  have hspanEB : ∀ (E : Ideal A) [E.IsPrime] (π : D), E.comap (algebraMap D A) = Ideal.span {π} →
      (E.comap (algebraMap B A)).comap (algebraMap C B) = Ideal.span {algebraMap D C π} := by
    intro E _ π hπ
    rw [← IsLocalization.map_comap (Ideal.span {x₀, w} : Ideal D).primeCompl C
      ((E.comap (algebraMap B A)).comap (algebraMap C B)), Ideal.under, hcomapEB, hπ,
      Ideal.map_span, Set.image_singleton]
  refine ⟨algebraMap B K y₀ / (algebraMap C K δ * algebraMap D K x₀), fun E _ hEdvr hEp => ?_, ?_⟩
  · obtain ⟨π, hπ0, hπ, hmin⟩ := exists_comap_eq_span_singleton (D := D) 𝔮 E hEdvr
    by_cases hq : E.comap (algebraMap D A) = Ideal.span {x₀}
    · -- `E` lies over `(g)`, like `p`
      have hEBg := hspanEB E x₀ hq
      have hne : E.comap (algebraMap B A) ≠ pB := fun h => hEp (by
        rw [← IsLocalization.map_comap 𝔐.primeCompl A E,
          ← IsLocalization.map_comap 𝔐.primeCompl A p]
        exact congrArg (Ideal.map (algebraMap B A)) h)
      obtain ⟨b', hb'p, hb'E⟩ : ∃ b' ∈ pB, b' ∉ E.comap (algebraMap B A) := by
        by_contra h
        push Not at h
        have hlt : pB < E.comap (algebraMap B A) :=
          lt_of_le_of_ne (fun b hb => h b hb) (Ne.symm hne)
        have := Ideal.IntegralClosure.comap_lt_comap (R := C) hlt
        rw [Ideal.under_def, Ideal.under_def, hpB, hEBg] at this
        exact lt_irrefl _ this
      obtain ⟨s, hs, a, ha, h⟩ := H2 (E.comap (algebraMap B A)) hEBg b' hb'p
      refine ⟨x₀, hx₀, hq, algebraMap B A (b' * s), fun hmem =>
        (Ideal.IsPrime.mul_notMem inferInstance hb'E hs) hmem, algebraMap B A a, ha, ?_⟩
      have h' := congrArg (algebraMap B K) h
      simp only [map_mul, hCBK] at h'
      show algebraMap B K y₀ / (algebraMap C K δ * algebraMap D K x₀) * algebraMap D K x₀ *
        algebraMap B K (b' * s) = algebraMap B K a
      rw [map_mul, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hδK hx₀K)]
      linear_combination (algebraMap D K x₀) * h'
    · -- `E` lies over another prime `(π)`, away from `x₀`
      have hx₀E : algebraMap D A x₀ ∉ E := by
        intro hx
        have hle : Ideal.span {x₀} ≤ E.comap (algebraMap D A) := by
          rw [Ideal.span_le, Set.singleton_subset_iff]; exact hx
        rcases hle.lt_or_eq with hlt | heq
        · exact hx₀ (Ideal.span_singleton_eq_bot.mp (hmin _ hx₀p hlt))
        · exact hq heq.symm
      have hπC : algebraMap D C π ≠ 0 := (map_ne_zero_iff _ (IsLocalization.injective C
        (Ideal.span {x₀, w} : Ideal D).primeCompl_le_nonZeroDivisors)).mpr hπ0
      obtain ⟨s, hs, a, ha, h⟩ := H1 (E.comap (algebraMap B A)) (algebraMap D C π)
        (hspanEB E π hπ) hπC
      refine ⟨π, hπ0, hπ, algebraMap D A x₀ * algebraMap B A s,
        Ideal.IsPrime.mul_notMem inferInstance hx₀E hs, algebraMap B A a, ha, ?_⟩
      have h' := congrArg (algebraMap B K) h
      simp only [map_mul, hCBK, hDCK] at h'
      show algebraMap B K y₀ / (algebraMap C K δ * algebraMap D K x₀) * algebraMap D K π *
        algebraMap A K (algebraMap D A x₀ * algebraMap B A s) = algebraMap B K a
      rw [map_mul, ← IsScalarTower.algebraMap_apply, div_mul_eq_mul_div, div_mul_eq_mul_div,
        div_eq_iff (mul_ne_zero hδK hx₀K)]
      linear_combination (algebraMap D K x₀) * h'
  · have hdB : algebraMap C B d ∉ pB := fun h => hdq (by rwa [← hpB])
    obtain ⟨b₁, rfl⟩ := Ideal.Quotient.mk_surjective a₁
    have hb₁ : b₁ ∉ 𝔐 := fun h => ha₁ (Ideal.mem_map_of_mem _ h)
    have hb₁u : IsUnit (φBA (Ideal.Quotient.mk pB b₁)) := by
      rw [Ideal.quotientMap_mk]
      exact (IsLocalization.map_units A (⟨b₁, hb₁⟩ : 𝔐.primeCompl)).map _
    have hu : φBA (Ideal.Quotient.mk pB b₁ * Ideal.Quotient.mk pB b') =
        (φBA (Ideal.Quotient.mk pB b₁) * Ideal.Quotient.mk p (algebraMap B A s')) *
          Ideal.Quotient.mk p a' := by
      rw [map_mul, hφt]; ring
    refine ⟨algebraMap B A (algebraMap C B d), algebraMap B A y₁, hdB, ?_, N,
      φBA (Ideal.Quotient.mk pB b₁ * Ideal.Quotient.mk pB b'), hN, ?_, ?_, ?_⟩
    · have h' := congrArg (algebraMap B K) hy₁
      simp only [map_mul, hCBK] at h'
      show algebraMap B K y₀ / (algebraMap C K δ * algebraMap D K x₀) * algebraMap D K x₀ *
        algebraMap B K (algebraMap C B d) = algebraMap B K y₁
      rw [hCBK, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hδK hx₀K)]
      linear_combination (-(algebraMap D K x₀)) * h'
    · rw [hu]
      exact Ideal.mul_mem_left _ _ hϖ'.not_isUnit
    · rw [hu]
      intro hmem
      obtain ⟨v, hv'⟩ := (hb₁u.mul hs'u)
      have h2 : Ideal.Quotient.mk p a' ∈ IsLocalRing.maximalIdeal (A ⧸ p) ^ 2 := by
        have := Ideal.mul_mem_left _ (↑v⁻¹ : A ⧸ p) hmem
        rwa [← mul_assoc, ← hv', Units.inv_mul, one_mul] at this
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖ'] at h2
      exact notMem_span_singleton_sq_of_irreducible hϖ' h2
    · have e1 : ∀ b : B, φBA (Ideal.Quotient.mk pB b) = Ideal.Quotient.mk p (algebraMap B A b) :=
        fun b => Ideal.quotientMap_mk
      have := congrArg φBA hrel
      simp only [map_mul, map_natCast, e1] at this ⊢
      simp only [← IsScalarTower.algebraMap_apply] at this
      exact this

/-! ### Top differential forms along a discrete valuation ring -/

open TensorProduct in
/-- **Differentials of a uniformizer and of residually independent elements form a basis.** Let `O`
be a local domain, formally smooth over `k` with `Ω_{O/k}` free of rank `N + 1`, `O → L` a
surjection onto a field with kernel `(t)`, `t ∉ (t)²`, and `y₁, …, y_N ∈ O` whose differentials in
`Ω_{L/k}` are linearly independent. Then `dt, dy₁, …, dy_N` is a basis of `Ω_{O/k}`: it spans
(`linearIndependent_cons_D` gives the independence). -/
private theorem span_cons_D_eq_top {k O L : Type*} [Field k] [CommRing O] [IsDomain O]
    [IsLocalRing O] [Algebra k O] [Field L] [Algebra k L] [Algebra O L] [IsScalarTower k O L]
    [Algebra.FormallySmooth k O] [Module.Free O Ω[O⁄k]] [Module.Finite O Ω[O⁄k]]
    [Subsingleton (Algebra.H1Cotangent k L)] (hπ : Function.Surjective (algebraMap O L))
    {t : O} (hker : RingHom.ker (algebraMap O L) = Ideal.span {t})
    (ht2 : t ∉ RingHom.ker (algebraMap O L) ^ 2) {N : ℕ} (y : Fin N → O)
    (hy : LinearIndependent L fun i => KaehlerDifferential.D k L (algebraMap O L (y i)))
    (hN : N + 1 = Module.finrank O Ω[O⁄k]) :
    Submodule.span O (Set.range (Fin.cons (KaehlerDifferential.D k O t)
      fun i => KaehlerDifferential.D k O (y i) : Fin (N + 1) → Ω[O⁄k])) = ⊤ := by
  classical
  set v : Fin (N + 1) → Ω[O⁄k] :=
    Fin.cons (KaehlerDifferential.D k O t) fun i => KaehlerDifferential.D k O (y i) with hv
  have ht : t ∈ RingHom.ker (algebraMap O L) := hker ▸ Ideal.mem_span_singleton_self t
  -- `1 ⊗ dt ≠ 0`
  have hinj := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := k) hπ).mpr
    inferInstance
  have hv0 : (1 : L) ⊗ₜ[O] KaehlerDifferential.D k O t ≠ 0 := by
    have hx : Ideal.toCotangent (RingHom.ker (algebraMap O L)) ⟨t, ht⟩ ≠ 0 := by
      rw [Ne, Ideal.toCotangent_eq_zero]; exact ht2
    have := (map_ne_zero_iff _ hinj).mpr hx
    rwa [KaehlerDifferential.kerCotangentToTensor_toCotangent] at this
  -- the images in `L ⊗ Ω_O` are independent
  let w : Fin (N + 1) → L ⊗[O] Ω[O⁄k] := fun i => (1 : L) ⊗ₜ v i
  have hw : LinearIndependent L w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hf := congrArg (KaehlerDifferential.mapBaseChange k O L) hc
    rw [map_sum, map_zero, Fin.sum_univ_succ] at hf
    have h0 : KaehlerDifferential.mapBaseChange k O L (c 0 • w 0) = 0 := by
      simp only [w, hv, Fin.cons_zero, map_smul, KaehlerDifferential.mapBaseChange_tmul, one_smul,
        KaehlerDifferential.map_D, RingHom.mem_ker.mp ht, map_zero, smul_zero]
    rw [h0, zero_add] at hf
    have hrest : ∑ i : Fin N, c i.succ • KaehlerDifferential.D k L (algebraMap O L (y i)) = 0 := by
      rw [← hf]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [w, hv, Fin.cons_succ, map_smul, KaehlerDifferential.mapBaseChange_tmul, one_smul,
        KaehlerDifferential.map_D]
    have hsucc := (Fintype.linearIndependent_iff.mp hy) _ hrest
    intro i
    refine Fin.cases ?_ hsucc i
    have hc0 : c 0 • w 0 = 0 := by
      have := hc
      rw [Fin.sum_univ_succ] at this
      simpa [hsucc] using this
    exact (smul_eq_zero.mp hc0).resolve_right (by simpa [w, hv] using hv0)
  -- they form a basis of `L ⊗ Ω_O`, so `v` spans `Ω_O` (Nakayama)
  have hcard : Fintype.card (Fin (N + 1)) = Module.finrank L (L ⊗[O] Ω[O⁄k]) := by
    rw [Module.finrank_baseChange, Fintype.card_fin, hN]
  let bw := basisOfLinearIndependentOfCardEqFinrank hw hcard
  have hm : RingHom.ker (algebraMap O L) = IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hπ)
  let ψ : L ≃ₐ[O] IsLocalRing.ResidueField O :=
    ((Ideal.quotientKerAlgEquivOfSurjective (R₁ := O) (f := Algebra.ofId O L) hπ).symm.trans
      (Ideal.quotientEquivAlgOfEq O hm))
  let e : L ⊗[O] Ω[O⁄k] ≃ₗ[O] IsLocalRing.ResidueField O ⊗[O] Ω[O⁄k] :=
    TensorProduct.congr ψ.toLinearEquiv (LinearEquiv.refl O _)
  have hspan : Submodule.span O (Set.range v) = ⊤ := by
    rw [← IsLocalRing.map_tensorProduct_mk_eq_top]
    have h1 : (Submodule.span O (Set.range v)).map (TensorProduct.mk O L Ω[O⁄k] 1) = ⊤ := by
      rw [Submodule.map_span, ← Submodule.restrictScalars_span O L hπ, ← Set.range_comp]
      have : (TensorProduct.mk O L Ω[O⁄k] 1 ∘ v) = bw := by
        funext i; simp [bw, w]
      rw [this, bw.span_eq, Submodule.restrictScalars_top]
    have h2 := congrArg (Submodule.map e.toLinearMap) h1
    rw [Submodule.map_top, LinearEquiv.range, ← Submodule.map_comp] at h2
    convert h2 using 2
    ext x
    simp [e, ψ]
  exact hspan

/-- The independence half of `span_cons_D_eq_top`. -/
private theorem linearIndependent_cons_D {k O L : Type*} [Field k] [CommRing O] [IsDomain O]
    [IsLocalRing O] [Algebra k O] [Field L] [Algebra k L] [Algebra O L] [IsScalarTower k O L]
    [Algebra.FormallySmooth k O] [Module.Free O Ω[O⁄k]] [Module.Finite O Ω[O⁄k]]
    [Subsingleton (Algebra.H1Cotangent k L)] (hπ : Function.Surjective (algebraMap O L))
    {t : O} (hker : RingHom.ker (algebraMap O L) = Ideal.span {t})
    (ht2 : t ∉ RingHom.ker (algebraMap O L) ^ 2) {N : ℕ} (y : Fin N → O)
    (hy : LinearIndependent L fun i => KaehlerDifferential.D k L (algebraMap O L (y i)))
    (hN : N + 1 = Module.finrank O Ω[O⁄k]) :
    LinearIndependent O (Fin.cons (KaehlerDifferential.D k O t)
      fun i => KaehlerDifferential.D k O (y i) : Fin (N + 1) → Ω[O⁄k]) :=
  linearIndependent_of_top_le_span_of_card_eq_finrank
    (span_cons_D_eq_top hπ hker ht2 y hy hN).ge (by simpa using hN)

open exteriorPower in
/-- The top wedge of `d(u tᵉ), dy₁, …, dy_N` is `tᵉ⁻¹ (e u + t c)` times that of
`dt, dy₁, …, dy_N`, when the latter form a basis. -/
private theorem ιMulti_cons_D_mul_pow_eq {k O : Type*} [Field k] [CommRing O] [Algebra k O]
    {N : ℕ} (t u : O) (y : Fin N → O) {e : ℕ} (he : 1 ≤ e)
    (hb : LinearIndependent O (Fin.cons (KaehlerDifferential.D k O t)
      fun i => KaehlerDifferential.D k O (y i) : Fin (N + 1) → Ω[O⁄k]))
    (hspan : Submodule.span O (Set.range (Fin.cons (KaehlerDifferential.D k O t)
      fun i => KaehlerDifferential.D k O (y i) : Fin (N + 1) → Ω[O⁄k])) = ⊤) :
    ∃ c : O, ιMulti O (N + 1) (Fin.cons (KaehlerDifferential.D k O (u * t ^ e))
        fun i => KaehlerDifferential.D k O (y i) : Fin (N + 1) → Ω[O⁄k]) =
      (t ^ (e - 1) * (e * u + t * c)) • ιMulti O (N + 1) (Fin.cons (KaehlerDifferential.D k O t)
        fun i => KaehlerDifferential.D k O (y i) : Fin (N + 1) → Ω[O⁄k]) := by
  classical
  set v : Fin (N + 1) → Ω[O⁄k] :=
    Fin.cons (KaehlerDifferential.D k O t) fun i => KaehlerDifferential.D k O (y i) with hvdef
  let b : Module.Basis (Fin (N + 1)) O Ω[O⁄k] := Module.Basis.mk hb hspan.ge
  have hbv : ∀ i, b i = v i := fun i => Module.Basis.mk_apply hb hspan.ge i
  set c : Fin (N + 1) → O := ⇑(b.repr (KaehlerDifferential.D k O u)) with hc
  refine ⟨c 0, ?_⟩
  have hDu : KaehlerDifferential.D k O u = ∑ i, c i • v i := by
    conv_lhs => rw [← (b.sum_repr (KaehlerDifferential.D k O u))]
    simp [hbv, hc]
  have hD : KaehlerDifferential.D k O (u * t ^ e) =
      t ^ e • ∑ i, c i • v i + ((e : O) * u * t ^ (e - 1)) • v 0 := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, add_comm, hDu]
    congr 1
    have hv0 : v 0 = KaehlerDifferential.D k O t := by simp [hvdef]
    rw [hv0, ← Nat.cast_smul_eq_nsmul O]
    module
  have hcons : (Fin.cons (KaehlerDifferential.D k O (u * t ^ e))
      fun i => KaehlerDifferential.D k O (y i) : Fin (N + 1) → Ω[O⁄k]) =
      Function.update v 0 (KaehlerDifferential.D k O (u * t ^ e)) := by
    rw [hvdef, ← Fin.update_cons_zero]
  rw [hcons, hD, AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
    AlternatingMap.map_update_smul, AlternatingMap.map_update_sum]
  have hzero : ∀ i ∈ Finset.univ, i ≠ 0 →
      ιMulti O (N + 1) (Function.update v 0 (c i • v i)) = 0 := by
    intro i _ hi
    rw [AlternatingMap.map_update_smul]
    rw [(ιMulti O (N + 1)).map_eq_zero_of_eq (Function.update v 0 (v i)) (i := 0) (j := i)
      (by simp [Function.update_self, Function.update_of_ne hi]) (Ne.symm hi), smul_zero]
  rw [Finset.sum_eq_single 0 hzero (by simp), AlternatingMap.map_update_smul,
    Function.update_eq_self, smul_smul, ← add_smul]
  congr 1
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  push_cast
  ring

/-- The wedge of a spanning family of `n` vectors generates the `n`-th exterior power. -/
private theorem span_singleton_ιMulti_eq_top {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {n : ℕ} (v : Fin n → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span R {exteriorPower.ιMulti R n v} = ⊤ := by
  refine eq_top_iff.mpr ((exteriorPower.ιMulti_span_of_span R n M hv).symm.le.trans ?_)
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  have : ∀ i, ∃ j, v j = a i := fun i => ha (Set.mem_range_self i)
  choose g hg using this
  have ha' : a = v ∘ g := funext fun i => (hg i).symm
  subst ha'
  by_cases hinj : Function.Injective g
  · let σ := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hinj)
    have : v ∘ g = v ∘ σ := rfl
    rw [this, AlternatingMap.map_perm]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.mem_span_singleton_self _)
  · simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    rw [AlternatingMap.map_eq_zero_of_eq _ _ (show (v ∘ g) i = (v ∘ g) j by simp [hij]) hne]
    exact Submodule.zero_mem _

/-- Two generators of a torsion-free module over a domain differ by a unit. -/
private theorem exists_isUnit_smul_eq_of_span_eq_top {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] [Nontrivial M] {σ ω : M}
    (hσ : Submodule.span R {σ} = ⊤) (hω : Submodule.span R {ω} = ⊤) :
    ∃ a : R, IsUnit a ∧ σ = a • ω := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hω ▸ Submodule.mem_top (x := σ))
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hσ ▸ Submodule.mem_top (x := ω))
  have hω0 : ω ≠ 0 := by
    rintro rfl
    rw [Submodule.span_singleton_eq_bot.mpr rfl] at hω
    exact bot_ne_top hω
  have h1 : (b * a - 1) • ω = 0 := by rw [sub_smul, mul_smul, ha, hb, one_smul, sub_self]
  have h2 : b * a = 1 := sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hω0)
  exact ⟨a, isUnit_iff_exists_inv'.mpr ⟨b, h2⟩, ha.symm⟩

open exteriorPower in
/-- `topFormsMap` of a wedge of differentials is the wedge of their images. -/
private theorem topFormsMap_ιMulti_cons_D {k O O' : Type*} [CommRing k] [CommRing O] [CommRing O']
    [Algebra k O] [Algebra k O'] [Algebra O O'] [IsScalarTower k O O'] {N : ℕ} (w : O)
    (y : Fin N → O) :
    topFormsMap k O O' (N + 1) (ιMulti O (N + 1) (Fin.cons (KaehlerDifferential.D k O w)
      fun i => KaehlerDifferential.D k O (y i))) =
      ιMulti O' (N + 1) (Fin.cons (KaehlerDifferential.D k O' (algebraMap O O' w))
        fun i => KaehlerDifferential.D k O' (algebraMap O O' (y i))) := by
  rw [topFormsMap_ιMulti]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [KaehlerDifferential.map_D]

open exteriorPower in
/-- **The tame different of an extension of discrete valuation rings.** Let `O → O'` be a local
homomorphism of discrete valuation rings over a field `k` of characteristic zero, both formally
smooth over `k` with `Ω` free of the same rank `N + 1`, with residue fields formally smooth over
`k` and `κ'` algebraic over `κ`. If a uniformizer `w` of `O` is `u tᵉ` in `O'`, `t` a
uniformizer and `u` a unit, then every generator `σ` of `Ω^{N+1}_{O/k}` maps to `t^{e-1} c σ'`
for a generator `σ'` of `Ω^{N+1}_{O'/k}` and a unit `c`. -/
private theorem exists_topFormsMap_eq_pow_mul_smul {k O O' : Type*} [Field k] [CharZero k]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra k O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra k O']
    [Algebra O O'] [IsScalarTower k O O'] [IsLocalHom (algebraMap O O')]
    [Algebra.FormallySmooth k O] [Module.Free O Ω[O⁄k]] [Module.Finite O Ω[O⁄k]]
    [Algebra.FormallySmooth k O'] [Module.Free O' Ω[O'⁄k]] [Module.Finite O' Ω[O'⁄k]]
    [Subsingleton (Algebra.H1Cotangent k (IsLocalRing.ResidueField O))]
    [Subsingleton (Algebra.H1Cotangent k (IsLocalRing.ResidueField O'))]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')]
    {N : ℕ} (hN : N + 1 = Module.finrank O Ω[O⁄k]) (hN' : N + 1 = Module.finrank O' Ω[O'⁄k])
    {w : O} (hw : Irreducible w) {t : O'} (ht : Irreducible t) {u : O'} (hu : IsUnit u) {e : ℕ}
    (hwt : algebraMap O O' w = u * t ^ e)
    {σ : ⋀[O]^(N + 1) Ω[O⁄k]} (hσ : Submodule.span O {σ} = ⊤) :
    ∃ σ' : ⋀[O']^(N + 1) Ω[O'⁄k], Submodule.span O' {σ'} = ⊤ ∧ ∃ c : O', IsUnit c ∧
      topFormsMap k O O' (N + 1) σ = (t ^ (e - 1) * c) • σ' := by
  classical
  set κ := IsLocalRing.ResidueField O
  set κ' := IsLocalRing.ResidueField O'
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · rw [pow_zero, mul_one] at hwt
      exact absurd ((isUnit_map_iff (algebraMap O O') w).mp (hwt ▸ hu)) hw.not_isUnit
    · exact h
  -- data at `O`
  have hsurj : Function.Surjective (algebraMap O κ) := IsLocalRing.residue_surjective
  have hker : RingHom.ker (algebraMap O κ) = Ideal.span {w} := by
    change RingHom.ker (IsLocalRing.residue O) = _
    rw [IsLocalRing.ker_residue, (IsDiscreteValuationRing.irreducible_iff_uniformizer w).mp hw]
  have hw2 : w ∉ RingHom.ker (algebraMap O κ) ^ 2 :=
    hker ▸ notMem_span_singleton_sq_of_irreducible hw
  haveI : Module.Finite κ Ω[κ⁄k] := Module.Finite.of_surjective _
    (KaehlerDifferential.mapBaseChange_surjective k O κ hsurj)
  have hfr := finrank_kaehlerDifferential_add_one (k := k) hsurj hker hw2
  have hκ : Module.finrank κ Ω[κ⁄k] = N := by omega
  obtain ⟨b, hbsub, hbspan, hbli⟩ :=
    exists_linearIndependent κ (Set.range (KaehlerDifferential.D k κ))
  rw [KaehlerDifferential.span_range_derivation] at hbspan
  let Bκ : Module.Basis b κ Ω[κ⁄k] := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan])
  haveI : Fintype b := FiniteDimensional.fintypeBasisIndex Bκ
  have hcard : Fintype.card b = N := by rw [← Module.finrank_eq_card_basis Bκ, hκ]
  let eb : Fin N ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hx : ∀ i, ∃ x : κ, KaehlerDifferential.D k κ x = (eb i).1 := fun i => hbsub (eb i).2
  choose x hx using hx
  choose y hy using fun i => hsurj (x i)
  have hyli : LinearIndependent κ fun i => KaehlerDifferential.D k κ (algebraMap O κ (y i)) := by
    have : (fun i => KaehlerDifferential.D k κ (algebraMap O κ (y i))) = fun i => Bκ (eb i) := by
      funext i; rw [hy, hx]; simp [Bκ]
    rw [this]
    exact Bκ.linearIndependent.comp _ eb.injective
  have hspanO := span_cons_D_eq_top hsurj hker hw2 y hyli hN
  have hliO := linearIndependent_of_top_le_span_of_card_eq_finrank hspanO.ge (by simpa using hN)
  -- the generator `ω = dw ∧ dy` of `Ω^{N+1}_{O/k}`
  have hω := span_singleton_ιMulti_eq_top _ hspanO
  let bO : Module.Basis (Fin (N + 1)) O Ω[O⁄k] := Module.Basis.mk hliO hspanO.ge
  haveI : Module.Free O (⋀[O]^(N + 1) Ω[O⁄k]) := Module.Free.of_basis (bO.exteriorPower (N + 1))
  haveI : Nontrivial (⋀[O]^(N + 1) Ω[O⁄k]) := by
    apply Module.nontrivial_of_finrank_pos (R := O)
    rw [exteriorPower.finrank_eq, ← hN, Nat.choose_self]; exact one_pos
  obtain ⟨a, ha, hσa⟩ := exists_isUnit_smul_eq_of_span_eq_top hσ hω
  -- data at `O'`
  have hsurj' : Function.Surjective (algebraMap O' κ') := IsLocalRing.residue_surjective
  have hker' : RingHom.ker (algebraMap O' κ') = Ideal.span {t} := by
    change RingHom.ker (IsLocalRing.residue O') = _
    rw [IsLocalRing.ker_residue, (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht]
  have ht2 : t ∉ RingHom.ker (algebraMap O' κ') ^ 2 :=
    hker' ▸ notMem_span_singleton_sq_of_irreducible ht
  -- the residue extension is formally étale
  haveI : CharZero κ := charZero_of_injective_algebraMap (algebraMap k κ).injective
  haveI : Algebra.IsSeparable κ κ' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyEtale κ κ' := Algebra.FormallyEtale.of_isSeparable κ κ'
  have hres : ∀ z : O, algebraMap O' κ' (algebraMap O O' z) = algebraMap κ κ' (algebraMap O κ z) :=
    fun z => (IsLocalRing.ResidueField.map_residue _ z).symm
  haveI : IsScalarTower k κ κ' := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k O κ, ← hres, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  let Bκ' := (KaehlerDifferential.isBaseChange_of_formallyEtale k κ κ').basis Bκ
  have hyli' : LinearIndependent κ' fun i =>
      KaehlerDifferential.D k κ' (algebraMap O' κ' (algebraMap O O' (y i))) := by
    have : (fun i => KaehlerDifferential.D k κ' (algebraMap O' κ' (algebraMap O O' (y i)))) =
        fun i => Bκ' (eb i) := by
      funext i
      rw [hres, ← KaehlerDifferential.map_D k k κ κ', hy, hx, IsBaseChange.basis_apply]
      simp [Bκ]
    rw [this]
    exact Bκ'.linearIndependent.comp _ eb.injective
  have hspanO' := span_cons_D_eq_top hsurj' hker' ht2 (fun i => algebraMap O O' (y i)) hyli' hN'
  have hliO' := linearIndependent_of_top_le_span_of_card_eq_finrank hspanO'.ge (by simpa using hN')
  obtain ⟨c₀, hc₀⟩ := ιMulti_cons_D_mul_pow_eq (k := k) t u (fun i => algebraMap O O' (y i)) he
    hliO' hspanO'
  refine ⟨_, span_singleton_ιMulti_eq_top _ hspanO', algebraMap O O' a * ((e : O') * u + t * c₀),
    (ha.map _).mul (isUnit_natCast_mul_add_mul k (by omega) hu ht.not_isUnit c₀), ?_⟩
  rw [hσa, map_smul, topFormsMap_ιMulti_cons_D, hwt, hc₀, ← algebraMap_smul O', smul_smul]
  congr 1
  ring

section TameDifferent

open MvPolynomial

universe w in
/-- A domain algebraic over `k[X₁, …, X_s]` has transcendence degree `s`. -/
private theorem trdeg_eq_of_isAlgebraic {k L : Type w} [Field k] [CommRing L] [IsDomain L]
    [Algebra k L] {s : ℕ} [Algebra (MvPolynomial (Fin s) k) L]
    [IsScalarTower k (MvPolynomial (Fin s) k) L] [FaithfulSMul (MvPolynomial (Fin s) k) L]
    [Algebra.IsAlgebraic (MvPolynomial (Fin s) k) L] :
    (Algebra.trdeg k L).toNat = s := by
  have h := trdeg_add_eq k (MvPolynomial (Fin s) k) (A := L)
  rw [MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero, add_zero] at h
  rw [← h]
  simp

/-- The residue of an element integral over `D` is integral over the residue field. -/
private theorem isIntegral_residue {D O O' : Type*} [CommRing D] [CommRing O] [IsLocalRing O]
    [CommRing O'] [IsLocalRing O'] [Algebra D O] [Algebra O O'] [IsLocalHom (algebraMap O O')]
    (ν : D →+* O') (hν : ∀ d, algebraMap O O' (algebraMap D O d) = ν d) {a : O'}
    (ha : ν.IsIntegralElem a) :
    IsIntegral (IsLocalRing.ResidueField O) (IsLocalRing.residue O' a) := by
  obtain ⟨p, hp, hpa⟩ := ha
  refine ⟨p.map ((IsLocalRing.residue O).comp (algebraMap D O)), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have : (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')).comp
      ((IsLocalRing.residue O).comp (algebraMap D O)) = (IsLocalRing.residue O').comp ν := by
    ext d
    simp only [RingHom.comp_apply]
    rw [IsLocalRing.ResidueField.algebraMap_residue, hν]
  rw [this, ← Polynomial.hom_eval₂, hpa, map_zero]

open exteriorPower in
/-- **The tame order of the coordinate forms along a discrete valuation ring.** Let
`ν : k[X₀, …, X_N] → O'` be injective into a discrete valuation ring essentially of finite type and
formally smooth over `k` (characteristic zero), with `𝔪_{O'} ∩ k[X] = (f)` and `O'` a ring of
fractions of elements integral over `k[X]`. Then `ν f = u tᵉ` with `e ≥ 1`, and
`dX₀ ∧ ⋯ ∧ dX_N = t^{e-1} c σ'` for a unit `c` and a generator `σ'` of `Ω^{N+1}_{O'/k}`. -/
private theorem exists_ιMulti_D_eq_smul {k O' : Type*} [Field k] [CharZero k] [CommRing O']
    [IsDomain O']
    [IsDiscreteValuationRing O'] [Algebra k O'] [Algebra.FormallySmooth k O']
    [Module.Free O' Ω[O'⁄k]] [Module.Finite O' Ω[O'⁄k]] [Algebra.EssFiniteType k O'] {N : ℕ}
    (hN' : N + 1 = Module.finrank O' Ω[O'⁄k])
    (ν : MvPolynomial (Fin (N + 1)) k →ₐ[k] O') (hν : Function.Injective ν)
    {f : MvPolynomial (Fin (N + 1)) k} (hf0 : f ≠ 0)
    (hf : (IsLocalRing.maximalIdeal O').comap ν = Ideal.span {f})
    (halg : ∀ y : O', ∃ a b : O', (ν : MvPolynomial (Fin (N + 1)) k →+* O').IsIntegralElem a ∧
      (ν : MvPolynomial (Fin (N + 1)) k →+* O').IsIntegralElem b ∧ IsUnit b ∧ y * b = a) :
    ∃ σ' : ⋀[O']^(N + 1) Ω[O'⁄k], Submodule.span O' {σ'} = ⊤ ∧
      ∃ (t u c : O') (e : ℕ), Irreducible t ∧ IsUnit u ∧ IsUnit c ∧ 1 ≤ e ∧ ν f = u * t ^ e ∧
        ιMulti O' (N + 1) (fun i => KaehlerDifferential.D k O' (ν (X i))) =
          (t ^ (e - 1) * c) • σ' := by
  classical
  haveI : (Ideal.span {f}).IsPrime :=
    hf ▸ Ideal.comap_isPrime (ν : MvPolynomial (Fin (N + 1)) k →+* O') _
  let q : Ideal (MvPolynomial (Fin (N + 1)) k) := Ideal.span {f}
  let O := Localization.AtPrime q
  haveI : IsDiscreteValuationRing O := isDiscreteValuationRing_localization q rfl hf0
  have hmem : ∀ d : MvPolynomial (Fin (N + 1)) k, d ∈ q ↔ ν d ∈ IsLocalRing.maximalIdeal O' :=
      fun d => by
    change d ∈ Ideal.span {f} ↔ _
    rw [← hf]; rfl
  have hunits : ∀ s : q.primeCompl, IsUnit (ν s) := fun s => by
    by_contra h
    exact s.2 ((hmem _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h))
  letI : Algebra O O' := (IsLocalization.lift (M := q.primeCompl) (S := O) hunits).toAlgebra
  have hlift : ∀ d, algebraMap O O' (algebraMap (MvPolynomial (Fin (N + 1)) k) O d) = ν d :=
      fun d =>
    IsLocalization.lift_eq hunits d
  haveI : IsScalarTower k O O' := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin (N + 1)) k) O, hlift, AlgHom.commutes]
  haveI : IsLocalHom (algebraMap O O') := ⟨fun z hz => by
    obtain ⟨⟨d, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
    have h1 : algebraMap O O' (IsLocalization.mk' O d s) * ν s = ν d := by
      rw [← hlift, ← hlift, ← map_mul, IsLocalization.mk'_spec]
    have hdu : IsUnit (ν d) := h1 ▸ hz.mul (hunits s)
    have hd : d ∈ q.primeCompl := fun hd =>
      ((IsLocalRing.mem_maximalIdeal _).mp ((hmem d).mp hd)) hdu
    have h2 : IsLocalization.mk' O d s * algebraMap (MvPolynomial (Fin (N + 1)) k) O s =
        algebraMap (MvPolynomial (Fin (N + 1)) k) O d :=
      IsLocalization.mk'_spec O d s
    exact isUnit_of_mul_isUnit_left (h2 ▸ IsLocalization.map_units O (⟨d, hd⟩ : q.primeCompl))⟩
  -- `O` is formally smooth, with `Ω_O` free on the `dXᵢ`
  haveI : Algebra.FormallySmooth (MvPolynomial (Fin (N + 1)) k) O :=
    Algebra.FormallySmooth.of_isLocalization q.primeCompl
  haveI : Algebra.FormallySmooth k O :=
    Algebra.FormallySmooth.comp k (MvPolynomial (Fin (N + 1)) k) O
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin (N + 1)) k) O :=
    Algebra.FormallyEtale.of_isLocalization q.primeCompl
  have ibc := KaehlerDifferential.isBaseChange_of_formallyEtale k (MvPolynomial (Fin (N + 1)) k) O
  let bO := ibc.basis (KaehlerDifferential.mvPolynomialBasis k (Fin (N + 1)))
  have hbO : (fun i => KaehlerDifferential.D k O
      (algebraMap (MvPolynomial (Fin (N + 1)) k) O (X i))) = bO := by
    funext i
    simp only [bO, IsBaseChange.basis_apply, KaehlerDifferential.mvPolynomialBasis_apply,
      KaehlerDifferential.map_D]
  haveI : Module.Free O Ω[O⁄k] := .of_basis bO
  haveI : Module.Finite O Ω[O⁄k] := .of_basis bO
  have hN : N + 1 = Module.finrank O Ω[O⁄k] := by
    rw [Module.finrank_eq_card_basis bO, Fintype.card_fin]
  -- the residue fields
  haveI : Algebra.EssFiniteType (MvPolynomial (Fin (N + 1)) k) O :=
    .of_isLocalization O q.primeCompl
  haveI : Algebra.EssFiniteType k O := .comp k (MvPolynomial (Fin (N + 1)) k) O
  haveI : Algebra.EssFiniteType k (IsLocalRing.ResidueField O) :=
    .of_surjective (IsScalarTower.toAlgHom k O _) IsLocalRing.residue_surjective
  haveI : Algebra.EssFiniteType k (IsLocalRing.ResidueField O') :=
    .of_surjective (IsScalarTower.toAlgHom k O' _) IsLocalRing.residue_surjective
  haveI : Algebra.FormallySmooth k (IsLocalRing.ResidueField O) :=
    Algebra.FormallySmooth.of_perfectField
  haveI : Algebra.FormallySmooth k (IsLocalRing.ResidueField O') :=
    Algebra.FormallySmooth.of_perfectField
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O') :=
      ⟨fun z => by
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨a, b, ha, hb, hbu, hyb⟩ := halg y
    have h1 := isIntegral_residue (O := O) (ν : (MvPolynomial (Fin (N + 1)) k) →+* O') hlift ha
    have h2 := isIntegral_residue (O := O) (ν : (MvPolynomial (Fin (N + 1)) k) →+* O') hlift hb
    have hb0 : IsLocalRing.residue O' b ≠ 0 := (hbu.map _).ne_zero
    have : IsLocalRing.residue O' y = IsLocalRing.residue O' a * (IsLocalRing.residue O' b)⁻¹ := by
      rw [← hyb, map_mul, mul_inv_cancel_right₀ hb0]
    rw [this]
    exact h1.isAlgebraic.mul h2.isAlgebraic.inv⟩
  -- the uniformizers
  have hνf : ν f ≠ 0 := fun h => hf0 (hν (by rw [h, map_zero]))
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible O'
  obtain ⟨e, u, hue⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hνf ht
  have hmaxO : IsLocalRing.maximalIdeal O =
      Ideal.span {algebraMap (MvPolynomial (Fin (N + 1)) k) O f} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact (Ideal.map_span _ _).trans (by rw [Set.image_singleton])
  have hw : Irreducible (algebraMap (MvPolynomial (Fin (N + 1)) k) O f) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmaxO
  have hσ := span_singleton_ιMulti_eq_top (R := O)
    (fun i => KaehlerDifferential.D k O (algebraMap (MvPolynomial (Fin (N + 1)) k) O (X i)))
    (by rw [hbO]; exact bO.span_eq)
  obtain ⟨σ', hσ', c, hc, heq⟩ := exists_topFormsMap_eq_pow_mul_smul (k := k) hN hN' hw ht
    u.isUnit (by rw [hlift, hue]) hσ
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · exfalso
      have : ν f ∈ IsLocalRing.maximalIdeal O' := (hmem f).mp (Ideal.mem_span_singleton_self f)
      rw [hue, pow_zero, mul_one] at this
      exact (IsLocalRing.mem_maximalIdeal _).mp this u.isUnit
    · exact h
  refine ⟨σ', hσ', t, u, c, e, ht, u.isUnit, hc, he, hue, ?_⟩
  rw [← heq, topFormsMap_ιMulti]
  congr 1
  funext i
  rw [KaehlerDifferential.map_D, hlift]

end TameDifferent

/-- Generization to the generic point commutes with generization between stalks. -/
private theorem algebraMap_stalkSpecializes' (X : Scheme.{u}) [IsIntegral X] {x x' : X} (h : x ⤳ x')
    (z : X.presheaf.stalk x') :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.stalkSpecializes h z) =
      algebraMap (X.presheaf.stalk x') X.functionField z := by
  change (X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes _).hom z = _
  rw [TopCat.Presheaf.stalkSpecializes_comp]
  rfl

/-- A closed immersion of an irreducible scheme onto the support of a prime divisor maps the
generic point to the generic point of the divisor. -/
private theorem map_genericPoint_eq {X T : Scheme.{u}} (j : T ⟶ X) [IsClosedImmersion j]
    [IrreducibleSpace T] (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X)) :
    j (genericPoint T) = P.genericPoint := by
  have h1 : IsGenericPoint (j (genericPoint T)) (P.support : Set X) := by
    have := (genericPoint_spec T).image j.base.hom.continuous
    rwa [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq, hP] at this
  have h2 : IsGenericPoint P.genericPoint (P.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isGenericPoint_closure
  exact h1.eq h2

/-- An element of the local ring at a prime divisor has nonnegative order. -/
private theorem ord_algebraMap_nonneg {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y]
    (P : Mori.PrimeDivisor Y) (a : Y.presheaf.stalk P.genericPoint) :
    0 ≤ Y.ord (algebraMap _ Y.functionField a) P.genericPoint := by
  by_cases ha : algebraMap _ Y.functionField a = 0
  · rw [ha, Scheme.ord_zero]; rfl
  have h := (P.divisorialValuation_le_one_iff _).mpr ⟨a, rfl⟩
  rw [P.divisorialValuation_eq_exp_neg_ord ha, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

/-- `ord (f ^ k) = k ord f`. -/
private theorem ord_pow' {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {f : Y.functionField}
    (hf : f ≠ 0) (k : ℕ) (z : Y) : Y.ord (f ^ k) z = k * Y.ord f z := by
  simpa using MMP.Mori.ord_zpow z hf k

/-- `ord f⁻¹ = - ord f`. -/
private theorem ord_inv' {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {f : Y.functionField}
    (hf : f ≠ 0) (z : Y) : Y.ord f⁻¹ z = -Y.ord f z := by
  simpa using MMP.Mori.ord_zpow z hf (-1)

/-- A unit of the local ring at a prime divisor has order zero. -/
private theorem ord_algebraMap_eq_zero_of_isUnit {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y]
    (P : Mori.PrimeDivisor Y) {x : Y} (hx : x = P.genericPoint) {b : Y.presheaf.stalk x}
    (hb : IsUnit b) : Y.ord (algebraMap _ Y.functionField b) P.genericPoint = 0 := by
  subst hx
  exact P.ord_algebraMap_of_isUnit hb

/-! ### Poincaré residues along a prime divisor -/

section ResidueAlongPrimeDivisor

variable {k : Type u} [Field k] {Y T : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] {j : T ⟶ Y}

/-- The residue of `b τ`, for `b` in the local ring at the generic point of `T`, is `b̄ Res τ`. -/
private theorem IsPoincareResidue.algebraMap_smul {n m : ℕ} {τ : RationalPluriForms sY (n + 1) m}
    {ρ : RationalPluriForms (j ≫ sY) n m} (h : IsPoincareResidue sY j n m τ ρ)
    (b : Y.presheaf.stalk (j (genericPoint T))) :
    IsPoincareResidue sY j n m (algebraMap _ Y.functionField b • τ)
      ((j.stalkMap (genericPoint T)).hom b • ρ) := by
  obtain ⟨t, g, x, ht, hτ, hρ⟩ := h
  refine ⟨t, b * g, x, ht, ?_, ?_⟩
  · subst hτ
    rw [map_mul, mul_smul]
    rfl
  · subst hρ
    rw [map_mul, mul_smul]
    rfl

end ResidueAlongPrimeDivisor

/-- An element of order `≥ 0` along a prime divisor lies in its local ring. -/
private theorem exists_algebraMap_eq_of_ord_nonneg {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (P : Mori.PrimeDivisor Y) {f : Y.functionField}
    (hf : f ≠ 0) (h : 0 ≤ Y.ord f P.genericPoint) :
    ∃ a : Y.presheaf.stalk P.genericPoint, algebraMap _ Y.functionField a = f := by
  have h1 : P.divisorialValuation f ≤ 1 := by
    rw [P.divisorialValuation_eq_exp_neg_ord hf, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  obtain ⟨a, ha⟩ := (P.divisorialValuation_le_one_iff f).mp h1
  exact ⟨a, ha⟩

/-- An element of order `0` along a prime divisor is a unit of its local ring. -/
private theorem exists_isUnit_algebraMap_eq_of_ord_eq_zero {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (P : Mori.PrimeDivisor Y) {f : Y.functionField}
    (hf : f ≠ 0) (h : Y.ord f P.genericPoint = 0) :
    ∃ a : Y.presheaf.stalk P.genericPoint, IsUnit a ∧ algebraMap _ Y.functionField a = f := by
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_ord_nonneg P hf h.ge
  have hinv : 0 ≤ Y.ord f⁻¹ P.genericPoint := by rw [ord_inv' hf, h, neg_zero]
  obtain ⟨a', ha'⟩ := exists_algebraMap_eq_of_ord_nonneg P (inv_ne_zero hf) hinv
  refine ⟨a, isUnit_iff_exists_inv.mpr ⟨a', IsFractionRing.injective _ Y.functionField ?_⟩, ha⟩
  rw [map_mul, ha, ha', mul_inv_cancel₀ hf, map_one]

/-- The algebra map from the stalk at the generic point to the function field is the identity. -/
private theorem algebraMap_stalk_genericPoint (T : Scheme.{u}) [IsIntegral T]
    (z : T.presheaf.stalk (genericPoint T)) :
    @algebraMap (T.presheaf.stalk (genericPoint T)) T.functionField _ _
      (stalkFunctionFieldAlgebra T (genericPoint T)) z = z := by
  change (T.presheaf.stalkSpecializes _).hom z = z
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-! ### Local algebra at a point of codimension two -/

/-- A generization `z` of `x` is determined by the prime `𝔪_z ∩ 𝒪_{X,x}`. -/
private theorem eq_of_comap_maximalIdeal_stalkSpecializes_eq {X : Scheme.{u}} {x y y' : X}
    (h : y ⤳ x) (h' : y' ⤳ x)
    (heq : (IsLocalRing.maximalIdeal (X.presheaf.stalk y)).comap
        (X.presheaf.stalkSpecializes h).hom =
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y')).comap
        (X.presheaf.stalkSpecializes h').hom) :
    y = y' := by
  have key : ∀ {z : X} (hz : z ⤳ x), X.fromSpecStalk x
      (show Spec (X.presheaf.stalk x) from ⟨(IsLocalRing.maximalIdeal (X.presheaf.stalk z)).comap
        (X.presheaf.stalkSpecializes hz).hom, inferInstance⟩) = z := by
    intro z hz
    have := congrArg (fun f => f.base (IsLocalRing.closedPoint (X.presheaf.stalk z)))
      (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hz)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
    rw [Scheme.fromSpecStalk_closedPoint] at this
    exact this
  have e := key h
  rw [show (show Spec (X.presheaf.stalk x) from ⟨(IsLocalRing.maximalIdeal
        (X.presheaf.stalk y)).comap (X.presheaf.stalkSpecializes h).hom, inferInstance⟩) =
      (show Spec (X.presheaf.stalk x) from ⟨(IsLocalRing.maximalIdeal
        (X.presheaf.stalk y')).comap (X.presheaf.stalkSpecializes h').hom, inferInstance⟩) from
      PrimeSpectrum.ext heq, key h'] at e
  exact e.symm

/-- The kernel of the restriction `𝒪_{X,j(t)} → 𝒪_{T,t}` along a closed immersion of an integral
scheme is the prime of the generic point of `T`. -/
private theorem ker_stalkMap_eq_comap_stalkSpecializes {X T : Scheme.{u}} [IsIntegral T]
    (j : T ⟶ X) [IsClosedImmersion j] (t : T) (h : j (genericPoint T) ⤳ j t) :
    RingHom.ker (j.stalkMap t).hom = (IsLocalRing.maximalIdeal
      (X.presheaf.stalk (j (genericPoint T)))).comap (X.presheaf.stalkSpecializes h).hom := by
  have h' : genericPoint T ⤳ t := genericPoint_specializes t
  have hsq : ∀ a, (j.stalkMap (genericPoint T)).hom (X.presheaf.stalkSpecializes h a) =
      T.presheaf.stalkSpecializes h' ((j.stalkMap t).hom a) := fun a =>
    Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ h' a
  have hsurj : Function.Surjective (j.stalkMap (genericPoint T)).hom :=
    SurjectiveOnStalks.stalkMap_surjective j (genericPoint T)
  have hker : RingHom.ker (j.stalkMap (genericPoint T)).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (j (genericPoint T))) := by
    haveI : IsField (T.presheaf.stalk (genericPoint T)) := Semifield.toIsField T.functionField
    exact IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)
  have hinj : Function.Injective (T.presheaf.stalkSpecializes h').hom :=
    IsFractionRing.injective (T.presheaf.stalk t) T.functionField
  ext a
  rw [RingHom.mem_ker, Ideal.mem_comap, ← hker, RingHom.mem_ker, hsq]
  constructor
  · intro ha; rw [ha, map_zero]
  · intro ha; exact hinj (by rw [ha, map_zero])

/-- If the stalk at a generization `y` of `x` is a discrete valuation ring, so is the localization
of `𝒪_{X,x}` at `𝔪_y ∩ 𝒪_{X,x}`. -/
private theorem isDiscreteValuationRing_localization_comap {X : Scheme.{u}} [IsIntegral X]
    {x y : X} (h : y ⤳ x) [IsDiscreteValuationRing (X.presheaf.stalk y)] :
    IsDiscreteValuationRing (Localization.AtPrime ((IsLocalRing.maximalIdeal
      (X.presheaf.stalk y)).comap (X.presheaf.stalkSpecializes h).hom)) := by
  letI := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  haveI := MMP.Intersection.isLocalization_stalkSpecializes h
  set q := (IsLocalRing.maximalIdeal (X.presheaf.stalk y)).comap
    (X.presheaf.stalkSpecializes h).hom
  haveI : IsDomain (Localization.AtPrime q) := IsLocalization.isDomain_localization
    q.primeCompl_le_nonZeroDivisors
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (IsLocalization.algEquiv q.primeCompl (X.presheaf.stalk y) (Localization.AtPrime q))

/-- `F aᵉ z = F (b a^{e+1}) v z a⁻¹` when `v b = 1`. -/
private theorem mul_pow_mul_eq_of_mul_eq_one {K : Type*} [Field K] (F a b v z : K) (e : ℕ)
    (hvb : v * b = 1) (ha : a ≠ 0) :
    F * (a ^ e * z) = F * (b * a ^ (e + 1)) * v * z * a⁻¹ := by
  symm
  calc F * (b * a ^ (e + 1)) * v * z * a⁻¹ = F * (a ^ e * z) * (v * b) * (a * a⁻¹) := by ring
    _ = F * (a ^ e * z) := by rw [hvb, mul_inv_cancel₀ ha, mul_one, mul_one]

/-- `(c v)^{⊗1} = c v^{⊗1}`. -/
private theorem tprod_fin_one_smul {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (c : R) (v : M) :
    PiTensorProduct.tprod R (fun _ : Fin 1 => c • v) =
      c • PiTensorProduct.tprod R (fun _ : Fin 1 => v) := by
  have := MultilinearMap.map_smul_univ (PiTensorProduct.tprod R) (fun _ : Fin 1 => c)
    (fun _ => v)
  simpa using this

/-- The coordinate of `c • ω^{⊗1}` along the generator `ω` is `c`. -/
private theorem formCoeff_smul_tprod {k A K : Type*} [Field k] [CommRing A] [Algebra k A]
    [Field K] [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K] {d : ℕ}
    {ω : ⋀[A]^d Ω[A⁄k]} (hω : Submodule.span A {ω} = ⊤) (h0 : topFormsMap k A K d ω ≠ 0)
    (c : K) :
    formCoeff (m := 1) A hω h0 ((c • PiTensorProduct.tprod K
      (fun _ : Fin 1 => topFormsMap k A K d ω) : TensorPower K 1 (⋀[K]^d Ω[K⁄k])) :
        PluriForms k K d 1) =
        c := by
  have hb : (ZTensorPower.basis (topFormsBasis A hω h0) 1 () : PluriForms k K d 1) =
      (PiTensorProduct.tprod K (fun _ : Fin 1 => topFormsMap k A K d ω) :
        TensorPower K 1 (⋀[K]^d Ω[K⁄k])) := by
    have := ZTensorPower.basis_ofNat (topFormsBasis A hω h0) 1
    rw [topFormsBasis_apply] at this
    exact this
  have e : ((c • PiTensorProduct.tprod K (fun _ : Fin 1 => topFormsMap k A K d ω) :
      TensorPower K 1 (⋀[K]^d Ω[K⁄k])) : PluriForms k K d 1) =
      c • (ZTensorPower.basis (topFormsBasis A hω h0) 1 () : PluriForms k K d 1) := by
    rw [hb]; rfl
  rw [e, formCoeff_smul, formCoeff, Module.Basis.repr_self, Finsupp.single_eq_same, mul_one]

/-- **The order of `f ω` along a prime divisor `Γ`**, for a generator `ω` of the top forms of the
local ring at a point `y = η_Γ`: it is `ord_Γ f`. -/
private theorem ordForm_smul_tprod_of_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] {d : ℕ}
    (Γ : Mori.PrimeDivisor X)
    {y : X} (hy : y = Γ.genericPoint) :
    letI := stalkAlgebra sX y
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX y
    ∀ {ω : ⋀[X.presheaf.stalk y]^d Ω[(X.presheaf.stalk y)⁄k]}
      (_ : Submodule.span (X.presheaf.stalk y) {ω} = ⊤)
      (_ : topFormsMap k (X.presheaf.stalk y) X.functionField d ω ≠ 0) (f : X.functionField),
      Γ.ordForm (m := 1) ((f • PiTensorProduct.tprod X.functionField
        (fun _ : Fin 1 => topFormsMap k (X.presheaf.stalk y) X.functionField d ω) :
          TensorPower X.functionField 1 (⋀[X.functionField]^d Ω[X.functionField⁄k])) :
          RationalPluriForms sX d 1) = X.ord f Γ.genericPoint := by
  subst hy
  intro ω hω h0 f
  letI := stalkAlgebra sX Γ.genericPoint
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
  exact (Γ.ordForm_eq _ hω h0).trans
    (congrArg (fun g => X.ord g Γ.genericPoint) (formCoeff_smul_tprod hω h0 f))

/-- An irreducible element of the stalk at a point of coheight one has order one. -/
theorem ord_algebraMap_eq_one_of_irreducible {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {y : X} (hy : Order.coheight y = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk y)] {t : X.presheaf.stalk y} (ht : Irreducible t) :
    X.ord (algebraMap _ X.functionField t) y = 1 := by
  have ht0 : algebraMap (X.presheaf.stalk y) X.functionField t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ht.ne_zero
  rw [Scheme.ord_eq_iff hy ht0]
  exact Ring.ordFrac_irreducible ht

/-- A nonzero element of the maximal ideal of the local ring along a prime divisor has
positive order. -/
private theorem one_le_ord_of_mem_maximalIdeal {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (Γ : Mori.PrimeDivisor X)
    {a : X.presheaf.stalk Γ.genericPoint} (ha0 : a ≠ 0)
    (ha : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk Γ.genericPoint)) :
    1 ≤ X.ord (algebraMap _ X.functionField a) Γ.genericPoint := by
  have h0 : algebraMap (X.presheaf.stalk Γ.genericPoint) X.functionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ha0
  have hnn := ord_algebraMap_nonneg Γ a
  by_contra hlt
  obtain ⟨b, hb, hba⟩ := exists_isUnit_algebraMap_eq_of_ord_eq_zero Γ h0 (by omega)
  have : b = a := IsFractionRing.injective _ X.functionField hba
  exact (IsLocalRing.mem_maximalIdeal _).mp ha (this ▸ hb)

/-- The generization maps between stalks are `k`-algebra maps. -/
private theorem isScalarTower_stalkSpecializes' {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {x x' : X} (h : x' ⤳ x) :
    letI := stalkAlgebra sX x
    letI := stalkAlgebra sX x'
    letI := (X.presheaf.stalkSpecializes h).hom.toAlgebra
    IsScalarTower k (X.presheaf.stalk x) (X.presheaf.stalk x') := by
  let := stalkAlgebra sX x
  let := stalkAlgebra sX x'
  let := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  have : (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ x' (TopologicalSpace.Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top _)) ≫
          X.presheaf.stalkSpecializes h := by
    simp
  exact congrArg CommRingCat.Hom.hom this

open exteriorPower in
/-- **The order of `f dX₀ ∧ ⋯ ∧ dX_N` along a prime divisor.** Let `E` be a prime divisor of a
normal variety over `k` of dimension `N + 1`, and `ν : k[X₀, …, X_N] → 𝒪_{X,E}` injective, with
`𝔪_E ∩ k[X] = (π)` and `𝒪_{X,E}` a ring of fractions of elements integral over `k[X]`. Then
`ν π = u tᵉ` with `t` a uniformizer, `u` a unit and `e ≥ 1`, the form `dX₀ ∧ ⋯ ∧ dX_N` is nonzero,
and `ord_E (f dX₀ ∧ ⋯ ∧ dX_N) = ord_E f + e - 1`. -/
theorem exists_ordForm_smul_tprod_ιMulti_eq {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X]
    [LocallyOfFiniteType sX] {N : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = N + 1)
    (E : Mori.PrimeDivisor X) :
    letI := stalkAlgebra sX E.genericPoint
    letI := functionFieldAlgebra sX
    ∀ (ν : MvPolynomial (Fin (N + 1)) k →ₐ[k] X.presheaf.stalk E.genericPoint),
      Function.Injective ν → ∀ {π : MvPolynomial (Fin (N + 1)) k}, π ≠ 0 →
      (IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint)).comap ν = Ideal.span {π} →
      (∀ y : X.presheaf.stalk E.genericPoint, ∃ a b : X.presheaf.stalk E.genericPoint,
        (ν : MvPolynomial (Fin (N + 1)) k →+* _).IsIntegralElem a ∧
        (ν : MvPolynomial (Fin (N + 1)) k →+* _).IsIntegralElem b ∧ IsUnit b ∧ y * b = a) →
      ∃ (t u : X.presheaf.stalk E.genericPoint) (e : ℕ), Irreducible t ∧ IsUnit u ∧ 1 ≤ e ∧
        ν π = u * t ^ e ∧
        ιMulti X.functionField (N + 1) (fun i => KaehlerDifferential.D k X.functionField
          (algebraMap _ X.functionField (ν (MvPolynomial.X i)))) ≠ 0 ∧
        ∀ f : X.functionField, f ≠ 0 →
          E.ordForm (m := 1) ((f • PiTensorProduct.tprod X.functionField (fun _ : Fin 1 =>
            ιMulti X.functionField (N + 1) (fun i => KaehlerDifferential.D k X.functionField
              (algebraMap _ X.functionField (ν (MvPolynomial.X i))))) :
            TensorPower X.functionField 1 (⋀[X.functionField]^(N + 1) Ω[X.functionField⁄k])) :
              RationalPluriForms sX (N + 1) 1) = X.ord f E.genericPoint + ((e : ℤ) - 1) := by
  letI := stalkAlgebra sX E.genericPoint
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_stalk_functionField sX E.genericPoint
  intro ν hν π hπ0 hf halg
  obtain ⟨hsm, hess⟩ := E.formallySmooth_localRing (sX := sX)
  obtain ⟨hfree, hfin⟩ := E.free_kaehlerDifferential_localRing (sX := sX)
  haveI := E.isDiscreteValuationRing_localRing
  have hN' : N + 1 = Module.finrank (X.presheaf.stalk E.genericPoint)
      Ω[(X.presheaf.stalk E.genericPoint)⁄k] :=
    ((E.finrank_kaehlerDifferential_localRing (sX := sX)).trans hd).symm
  obtain ⟨σ'', hσ'', t, u, c, e, ht, hu, hc, he, hπ, hι⟩ :=
    exists_ιMulti_D_eq_smul hN' ν hν hπ0 hf halg
  have h0 := E.topFormsMap_ne_zero (sX := sX) hd hσ''
  have hω : ιMulti X.functionField (N + 1) (fun i => KaehlerDifferential.D k X.functionField
      (algebraMap _ X.functionField (ν (MvPolynomial.X i)))) =
      algebraMap _ X.functionField (t ^ (e - 1) * c) •
        topFormsMap k (X.presheaf.stalk E.genericPoint) X.functionField (N + 1) σ'' := by
    rw [algebraMap_smul, ← map_smul, ← hι, topFormsMap_ιMulti]
    congr 1
    funext i
    rw [KaehlerDifferential.map_D]
  have ht0 : algebraMap (X.presheaf.stalk E.genericPoint) X.functionField t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ht.ne_zero
  have hc0' : algebraMap (X.presheaf.stalk E.genericPoint) X.functionField c ≠ 0 :=
    (hc.map _).ne_zero
  refine ⟨t, u, e, ht, hu, he, hπ, ?_, fun f hf0 => ?_⟩
  · rw [hω, map_mul, map_pow]
    exact smul_ne_zero (mul_ne_zero (pow_ne_zero _ ht0) hc0') h0
  have hσ : ((f • PiTensorProduct.tprod X.functionField (fun _ : Fin 1 =>
      ιMulti X.functionField (N + 1) (fun i => KaehlerDifferential.D k X.functionField
        (algebraMap _ X.functionField (ν (MvPolynomial.X i))))) :
      TensorPower X.functionField 1 (⋀[X.functionField]^(N + 1) Ω[X.functionField⁄k])) :
        RationalPluriForms sX (N + 1) 1) =
      (((f * algebraMap _ X.functionField (t ^ (e - 1) * c)) •
        PiTensorProduct.tprod X.functionField (fun _ : Fin 1 =>
          topFormsMap k (X.presheaf.stalk E.genericPoint) X.functionField (N + 1) σ'') :
        TensorPower X.functionField 1 (⋀[X.functionField]^(N + 1) Ω[X.functionField⁄k])) :
          RationalPluriForms sX (N + 1) 1) := by
    rw [hω, tprod_fin_one_smul, smul_smul]
  rw [hσ, ordForm_smul_tprod_of_eq E rfl hσ'' h0]
  have ht1 := ord_algebraMap_eq_one_of_irreducible E.coheight_genericPoint ht
  rw [map_mul, map_pow, Scheme.ord_mul hf0 (mul_ne_zero (pow_ne_zero _ ht0) hc0'),
    Scheme.ord_mul (pow_ne_zero _ ht0) hc0', E.ord_algebraMap_of_isUnit hc, ord_pow' ht0, ht1]
  push_cast [Nat.cast_sub he]
  ring

open exteriorPower in
/-- **No pole along the other prime divisors.** Let `E` be a prime divisor of a normal variety
`X` over `k` of dimension `n + 1`, and `ν : k[X₀, …, X_n] → 𝒪_{X,E}` injective, with
`𝔪_E ∩ k[X] = (π)` and `𝒪_{X,E}` a ring of fractions of elements integral over `k[X]`. If
`F π s = a` with `s` a unit and `a ∈ 𝔪_E`, then `F dX₀ ∧ ⋯ ∧ dX_n` has no pole along `E`: the
tame different `dX₀ ∧ ⋯ ∧ dX_n = t^{e-1} c σ'` (`exists_ιMulti_D_eq_smul`), `π = u tᵉ`, makes up
for the pole `ord_E F ≥ 1 - e`. -/
private theorem zero_le_ordForm_of_mul_mem_maximalIdeal {k : Type} [Field k] [CharZero k]
    {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X]
    [LocallyOfFiniteType sX] {n : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = n + 1)
    (E : Mori.PrimeDivisor X) :
    letI := stalkAlgebra sX E.genericPoint
    letI := functionFieldAlgebra sX
    ∀ (ν : MvPolynomial (Fin (n + 1)) k →ₐ[k] X.presheaf.stalk E.genericPoint),
      Function.Injective ν → ∀ {π : MvPolynomial (Fin (n + 1)) k}, π ≠ 0 →
      (IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint)).comap ν = Ideal.span {π} →
      (∀ y : X.presheaf.stalk E.genericPoint, ∃ a b : X.presheaf.stalk E.genericPoint,
        (ν : MvPolynomial (Fin (n + 1)) k →+* _).IsIntegralElem a ∧
        (ν : MvPolynomial (Fin (n + 1)) k →+* _).IsIntegralElem b ∧ IsUnit b ∧ y * b = a) →
      ∀ {F : X.functionField} {s a : X.presheaf.stalk E.genericPoint}, F ≠ 0 → IsUnit s →
        a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint) →
        F * algebraMap _ X.functionField (ν π) * algebraMap _ X.functionField s =
          algebraMap _ X.functionField a →
        0 ≤ E.ordForm (m := 1) ((F • PiTensorProduct.tprod X.functionField (fun _ : Fin 1 =>
          ιMulti X.functionField (n + 1) (fun i => KaehlerDifferential.D k X.functionField
            (algebraMap _ X.functionField (ν (MvPolynomial.X i))))) :
          TensorPower X.functionField 1 (⋀[X.functionField]^(n + 1) Ω[X.functionField⁄k])) :
            RationalPluriForms sX (n + 1) 1) := by
  letI := stalkAlgebra sX E.genericPoint
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_stalk_functionField sX E.genericPoint
  intro ν hν π hπ0 hf halg F s a hF0 hs ha hFa
  obtain ⟨t, u, e, ht, hu, he, hπ, -, hord⟩ :=
    exists_ordForm_smul_tprod_ιMulti_eq sX hd E ν hν hπ0 hf halg
  rw [hord F hF0]
  haveI := E.isDiscreteValuationRing_localRing
  have ht1 := ord_algebraMap_eq_one_of_irreducible E.coheight_genericPoint ht
  have ht0 : algebraMap (X.presheaf.stalk E.genericPoint) X.functionField t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ht.ne_zero
  have hne : ∀ {b : X.presheaf.stalk E.genericPoint}, IsUnit b →
      algebraMap (X.presheaf.stalk E.genericPoint) X.functionField b ≠ 0 :=
    fun hb => (hb.map _).ne_zero
  have hπ0' : algebraMap (X.presheaf.stalk E.genericPoint) X.functionField (ν π) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ((map_ne_zero_iff _ hν).mpr hπ0)
  have hπord : X.ord (algebraMap _ X.functionField (ν π)) E.genericPoint = e := by
    rw [hπ, map_mul, map_pow, Scheme.ord_mul (hne hu) (pow_ne_zero _ ht0),
      E.ord_algebraMap_of_isUnit hu, ord_pow' ht0, ht1]
    simp
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hFa
    exact mul_ne_zero (mul_ne_zero hF0 hπ0') (hne hs) hFa
  have haord := one_le_ord_of_mem_maximalIdeal E ha0 ha
  rw [← hFa, Scheme.ord_mul (mul_ne_zero hF0 hπ0') (hne hs), Scheme.ord_mul hF0 hπ0', hπord,
    E.ord_algebraMap_of_isUnit hs] at haord
  omega

open exteriorPower in
/-- **The top form `F dy₀ ∧ ⋯ ∧ dy_n` with `y₀ = u ϖᵉ`.** If `d(u ϖᵉ) ∧ dy = ϖ^{e-1} (e u + ϖ c)
dϖ ∧ dy` and `F y₀ = g₀`, then `F dy₀ ∧ ⋯ ∧ dy_n = g ϖ⁻¹ dϖ ∧ dy₁ ∧ ⋯ ∧ dy_n` in `Ω_K`, with
`g = g₀ u⁻¹ (e u + ϖ c)`. -/
private theorem smul_tprod_ιMulti_eq_of_eq_unit_mul_pow {k A K : Type*} [Field k] [CommRing A]
    [Algebra k A] [Field K] [Algebra k K] [Algebra A K] [IsScalarTower k A K] {n e : ℕ}
    (he : 1 ≤ e) (y : Fin (n + 1) → A) (ϖ c g₀ : A) (u : Aˣ) (hue : y 0 = u * ϖ ^ e)
    (hc : ιMulti A (n + 1) (Fin.cons (KaehlerDifferential.D k A (u * ϖ ^ e))
        fun i => KaehlerDifferential.D k A (y i.succ) : Fin (n + 1) → Ω[A⁄k]) =
      (ϖ ^ (e - 1) * (e * u + ϖ * c)) • ιMulti A (n + 1) (Fin.cons (KaehlerDifferential.D k A ϖ)
        fun i => KaehlerDifferential.D k A (y i.succ) : Fin (n + 1) → Ω[A⁄k]))
    (hϖ : algebraMap A K ϖ ≠ 0) {F : K} (hFg : F * algebraMap A K (y 0) = algebraMap A K g₀) :
    (F • PiTensorProduct.tprod K (fun _ : Fin 1 =>
        ιMulti K (n + 1) (fun i => KaehlerDifferential.D k K (algebraMap A K (y i)))) :
      TensorPower K 1 (⋀[K]^(n + 1) Ω[K⁄k])) =
    ((algebraMap A K (g₀ * ↑u⁻¹ * (e * u + ϖ * c)) * (algebraMap A K ϖ)⁻¹) •
        PiTensorProduct.tprod K (fun _ : Fin 1 => topFormsMap k A K (n + 1)
          (ιMulti A (n + 1) (Fin.cons (KaehlerDifferential.D k A ϖ)
            fun i => KaehlerDifferential.D k A (y i.succ))))) := by
  have hcons : (fun i => KaehlerDifferential.D k A (y i)) =
      (Fin.cons (KaehlerDifferential.D k A ((u : A) * ϖ ^ e))
        fun i => KaehlerDifferential.D k A (y i.succ) : Fin (n + 1) → Ω[A⁄k]) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [Fin.cons_zero, hue]
    · rw [Fin.cons_succ]
  have hωK : ιMulti K (n + 1) (fun i => KaehlerDifferential.D k K (algebraMap A K (y i))) =
      algebraMap A K (ϖ ^ (e - 1) * ((e : A) * u + ϖ * c)) •
        topFormsMap k A K (n + 1) (ιMulti A (n + 1) (Fin.cons (KaehlerDifferential.D k A ϖ)
          fun i => KaehlerDifferential.D k A (y i.succ))) := by
    rw [algebraMap_smul, ← map_smul, ← hc, ← hcons, topFormsMap_ιMulti]
    congr 1
    funext i
    rw [KaehlerDifferential.map_D]
  have hcoef : F * algebraMap A K (ϖ ^ (e - 1) * ((e : A) * u + ϖ * c)) =
      algebraMap A K (g₀ * ↑u⁻¹ * (e * u + ϖ * c)) * (algebraMap A K ϖ)⁻¹ := by
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have hg₀ : algebraMap A K g₀ = F * (algebraMap A K (u : A) * algebraMap A K ϖ ^ (e' + 1)) := by
      rw [← hFg, hue, map_mul, map_pow]
    have hu' : algebraMap A K (↑u⁻¹ : A) * algebraMap A K (u : A) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    simp only [map_mul, map_pow]
    rw [hg₀, Nat.add_sub_cancel]
    exact mul_pow_mul_eq_of_mul_eq_one _ _ _ _ _ e' hu' hϖ
  rw [hωK, tprod_fin_one_smul, smul_smul, hcoef]

open exteriorPower in
/-- `g ϖ⁻¹ (dϖ ∧ dx)^{⊗1}`, pushed to `K`, is `g (dϖ/ϖ ∧ dx)^{⊗1}`. -/
private theorem smul_tprod_topFormsMap_cons_eq {k A K : Type*} [Field k] [CommRing A]
    [Algebra k A] [Field K] [Algebra k K] [Algebra A K] [IsScalarTower k A K] {n : ℕ}
    (ϖ g : A) (x : Fin n → A) :
    ((algebraMap A K g * (algebraMap A K ϖ)⁻¹) •
        PiTensorProduct.tprod K (fun _ : Fin 1 => topFormsMap k A K (n + 1)
          (ιMulti A (n + 1) (Fin.cons (KaehlerDifferential.D k A ϖ)
            fun i => KaehlerDifferential.D k A (x i)))) :
      TensorPower K 1 (⋀[K]^(n + 1) Ω[K⁄k])) =
    algebraMap A K g • PiTensorProduct.tprod K (fun _ : Fin 1 => (algebraMap A K ϖ)⁻¹ •
      ιMulti K (n + 1) (Fin.cons (KaehlerDifferential.D k K (algebraMap A K ϖ))
        fun i => KaehlerDifferential.D k K (algebraMap A K (x i)))) := by
  rw [tprod_fin_one_smul, smul_smul, topFormsMap_ιMulti_cons_D]

/-- `g₀ u⁻¹ (e u + ϖ c)` maps to `e ḡ₀` when `ϖ` maps to zero. -/
private theorem map_mul_inv_mul_add_eq {A L : Type*} [CommRing A] [Field L] (φ : A →+* L)
    (e : ℕ) (g₀ ϖ c : A) (u : Aˣ) (hϖ : φ ϖ = 0) :
    φ (g₀ * ↑u⁻¹ * ((e : A) * u + ϖ * c)) = (e : L) * φ g₀ := by
  have h2 : φ (↑u⁻¹ : A) * φ (u : A) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [map_mul, map_mul, map_add, map_mul, map_mul, map_natCast, hϖ]
  linear_combination ((e : L) * φ g₀) * h2

open exteriorPower in
/-- **The residue of `F dX₀ ∧ ⋯ ∧ dX_n` along `T`.** Let `T ⊂ X` be closed integral, with generic
point that of a prime divisor `P` of the normal variety `X` over `k` of dimension `n + 1`, and
`ν : k[X₀, …, X_n] → 𝒪_{X,P}` with `ν X₀ ∈ 𝔪_P` nonzero and `dX̄₁, …, dX̄_n` independent in
`Ω_{k(T)}`. If `F X₀ = g₀ ∈ 𝒪_{X,P}`, then `F dX₀ ∧ ⋯ ∧ dX_n` has the Poincaré residue
`e ḡ₀ dX̄₁ ∧ ⋯ ∧ dX̄_n`, where `X₀ = u tᵉ`, and a simple pole along `P` when `g₀` is a unit. -/
theorem exists_isPoincareResidue_smul_tprod_ιMulti {k : Type} [Field k] [CharZero k]
    {X T : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X]
    [LocallyOfFiniteType sX] {n : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [LocallyOfFiniteType (j ≫ sX)]
    (P : Mori.PrimeDivisor X) (hjT : j (genericPoint T) = P.genericPoint) :
    letI := stalkAlgebra sX (j (genericPoint T))
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (j ≫ sX)
    ∀ (ν : MvPolynomial (Fin (n + 1)) k →ₐ[k] X.presheaf.stalk (j (genericPoint T))),
      ν (MvPolynomial.X 0) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (j (genericPoint T))) →
      ν (MvPolynomial.X 0) ≠ 0 →
      LinearIndependent T.functionField (fun i : Fin n => KaehlerDifferential.D k T.functionField
        ((j.stalkMap (genericPoint T)).hom (ν (MvPolynomial.X i.succ)))) →
      ∀ {F : X.functionField} {g₀ : X.presheaf.stalk (j (genericPoint T))},
        F * algebraMap _ X.functionField (ν (MvPolynomial.X 0)) = algebraMap _ X.functionField g₀ →
        ∃ e : ℕ, 0 < e ∧
          IsPoincareResidue sX j n 1 ((F • PiTensorProduct.tprod X.functionField (fun _ : Fin 1 =>
            ιMulti X.functionField (n + 1) (fun i => KaehlerDifferential.D k X.functionField
              (algebraMap _ X.functionField (ν (MvPolynomial.X i))))) :
            TensorPower X.functionField 1 (⋀[X.functionField]^(n + 1) Ω[X.functionField⁄k])) :
              RationalPluriForms sX (n + 1) 1)
            ((((e : T.functionField) * (j.stalkMap (genericPoint T)).hom g₀) •
              PiTensorProduct.tprod T.functionField (fun _ : Fin 1 =>
                ιMulti T.functionField n (fun i => KaehlerDifferential.D k T.functionField
                  ((j.stalkMap (genericPoint T)).hom (ν (MvPolynomial.X i.succ))))) :
              TensorPower T.functionField 1 (⋀[T.functionField]^n Ω[T.functionField⁄k])) :
                RationalPluriForms (j ≫ sX) n 1) ∧
          (IsUnit g₀ → P.ordForm (m := 1) ((F • PiTensorProduct.tprod X.functionField
            (fun _ : Fin 1 => ιMulti X.functionField (n + 1)
              (fun i => KaehlerDifferential.D k X.functionField
                (algebraMap _ X.functionField (ν (MvPolynomial.X i))))) :
            TensorPower X.functionField 1 (⋀[X.functionField]^(n + 1) Ω[X.functionField⁄k])) :
              RationalPluriForms sX (n + 1) 1) = -1) := by
  letI := stalkAlgebra sX (j (genericPoint T))
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (j ≫ sX)
  letI : Algebra (X.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  haveI := isScalarTower_stalk_functionField sX (j (genericPoint T))
  obtain ⟨hdvr, hfree, hfin, hsm, hcoh, hrank⟩ := stalk_facts_of_eq_genericPoint (sY := sX) P hjT
  obtain ⟨htow, hsurj⟩ := stalkMap_facts_of_isClosedImmersion (sY := sX) (j := j)
  obtain ⟨ϖ, r, hϖ0, hr, hker, hϖ2, -⟩ := exists_uniformizer_of_eq_genericPoint (sY := sX) P hjT
  have := essFiniteType_functionField (sX := j ≫ sX)
  intro ν hX0m hX00 hy F g₀ hFg
  have hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk (j (genericPoint T))) = Ideal.span {ϖ} :=
    (IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)).symm.trans hker
  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hmax
  obtain ⟨e, u, hue⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hX00 hϖirr
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · rw [pow_zero, mul_one] at hue
      exact absurd (hue ▸ u.isUnit) ((IsLocalRing.mem_maximalIdeal _).mp hX0m)
    · exact h
  have hN : n + 1 = Module.finrank (X.presheaf.stalk (j (genericPoint T))) Ω[(X.presheaf.stalk (j
      (genericPoint T)))⁄k] := by rw [hrank, hd]
  have hspan := span_cons_D_eq_top hsurj hker hϖ2 (fun i => ν (MvPolynomial.X i.succ)) hy hN
  have hli := linearIndependent_cons_D hsurj hker hϖ2 (fun i => ν (MvPolynomial.X i.succ)) hy hN
  obtain ⟨c, hc⟩ := ιMulti_cons_D_mul_pow_eq (k := k) ϖ (u : (X.presheaf.stalk (j (genericPoint
      T))))
    (fun i => ν (MvPolynomial.X i.succ)) he hli hspan
  have hϖK : algebraMap (X.presheaf.stalk (j (genericPoint T))) X.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖirr.ne_zero
  -- `F dX₀ ∧ ⋯ ∧ dX_n = g ϖ⁻¹ dϖ ∧ dX₁ ∧ ⋯ ∧ dX_n`, with `g = g₀ u⁻¹ (e u + ϖ c)`
  have hσ := smul_tprod_ιMulti_eq_of_eq_unit_mul_pow (k := k) (K := X.functionField) he
    (fun i => ν (MvPolynomial.X i)) ϖ c g₀ u hue hc hϖK hFg
  refine ⟨e, he, ⟨ϖ, g₀ * ↑u⁻¹ * ((e : (X.presheaf.stalk (j (genericPoint T)))) * u + ϖ * c),
    fun i => ν (MvPolynomial.X i.succ), ord_algebraMap_eq_one_of_irreducible hcoh hϖirr,
    hσ.trans (smul_tprod_topFormsMap_cons_eq ϖ _ _), ?_⟩, fun hg₀ => ?_⟩
  · rw [map_mul_inv_mul_add_eq (j.stalkMap (genericPoint T)).hom e g₀ ϖ c u hϖ0]
  · -- the simple pole along `P`
    have hω₀' := span_singleton_ιMulti_eq_top _ hspan
    obtain ⟨b₀⟩ := exists_basis_topForms (sX := sX) (d := n + 1)
      (by rw [topologicalKrullDim_eq_toNat_trdeg sX, hd])
    haveI : Nontrivial (⋀[X.functionField]^(n + 1) Ω[X.functionField⁄k]) :=
      ⟨⟨b₀ (), 0, b₀.ne_zero ()⟩⟩
    have h0 := topFormsMap_ne_zero_of_span_eq_top (K := X.functionField) hω₀'
    rw [hσ, ordForm_smul_tprod_of_eq P hjT hω₀' h0]
    have hgu : IsUnit (g₀ * ↑u⁻¹ * ((e : (X.presheaf.stalk (j (genericPoint T)))) * u + ϖ * c)) :=
      (hg₀.mul (Units.isUnit _)).mul
        (isUnit_natCast_mul_add_mul k (by omega) u.isUnit hϖirr.not_isUnit c)
    rw [Scheme.ord_mul (hgu.map _).ne_zero (inv_ne_zero hϖK),
      ord_algebraMap_eq_zero_of_isUnit P hjT hgu, ord_inv' hϖK, ← hjT,
      ord_algebraMap_eq_one_of_irreducible hcoh hϖirr, zero_add]

/-- **Rings of fractions of integral elements.** Let `ν : D → R` be integral, `A = R_𝔮`, and
`φ : A → B` such that every `y ∈ B` has `y φ(a₂) = φ(a₁)` with `φ(a₂)` a unit. Then every
`y ∈ B` is `a / b` with `a, b` integral over `D` and `b` a unit. -/
theorem exists_isIntegralElem_mul_eq {D R A B : Type*} [CommRing D] [CommRing R]
    [CommRing A] [CommRing B] [Algebra R A] (𝔮 : Ideal R) [𝔮.IsPrime]
    [IsLocalization.AtPrime A 𝔮] (ν : D →+* R) (hν : ν.IsIntegral) (φ : A →+* B)
    (hB : ∀ y : B, ∃ a₁ a₂ : A, IsUnit (φ a₂) ∧ y * φ a₂ = φ a₁) :
    ∀ y : B, ∃ a b : B, ((φ.comp (algebraMap R A)).comp ν).IsIntegralElem a ∧
      ((φ.comp (algebraMap R A)).comp ν).IsIntegralElem b ∧ IsUnit b ∧ y * b = a := by
  intro y
  obtain ⟨a₁, a₂, ha₂, hy⟩ := hB y
  obtain ⟨⟨r₁, s₁⟩, h₁⟩ := IsLocalization.surj 𝔮.primeCompl a₁
  obtain ⟨⟨r₂, s₂⟩, h₂⟩ := IsLocalization.surj 𝔮.primeCompl a₂
  simp only at h₁ h₂
  have hu : ∀ s : 𝔮.primeCompl, IsUnit (φ (algebraMap R A s)) :=
    fun s => (IsLocalization.map_units A s).map φ
  have hint : ∀ r : R, ((φ.comp (algebraMap R A)).comp ν).IsIntegralElem
      (φ (algebraMap R A r)) := fun r => (hν r).map _
  refine ⟨φ (algebraMap R A (r₁ * s₂)), φ (algebraMap R A (r₂ * s₁)), hint _, hint _, ?_, ?_⟩
  · rw [map_mul, map_mul, ← h₂, map_mul]
    exact (ha₂.mul (hu s₂)).mul (hu s₁)
  · rw [map_mul, map_mul, map_mul, map_mul, ← h₁, ← h₂, map_mul, map_mul, ← hy]
    ring

/-- A variety with a prime divisor has positive dimension: at the prime divisor `Q`,
`dim_{κ(Q)} Ω_{κ(Q)} + 1 = rank Ω_{𝒪_{Y,Q}}`. -/
private theorem one_le_trdeg_of_primeDivisor {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [LocallyOfFiniteType sY] (Q : Mori.PrimeDivisor Y) :
    1 ≤ (letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat) := by
  letI := stalkAlgebra sY Q.genericPoint
  obtain ⟨hsm, hess⟩ := Q.formallySmooth_localRing (sX := sY)
  obtain ⟨hfree, hfin⟩ := Q.free_kaehlerDifferential_localRing (sX := sY)
  haveI := Q.isDiscreteValuationRing_localRing
  haveI : Algebra.EssFiniteType k (IsLocalRing.ResidueField (Y.presheaf.stalk Q.genericPoint)) :=
    .of_surjective (IsScalarTower.toAlgHom k (Y.presheaf.stalk Q.genericPoint) _)
      IsLocalRing.residue_surjective
  haveI : Algebra.FormallySmooth k
      (IsLocalRing.ResidueField (Y.presheaf.stalk Q.genericPoint)) :=
    Algebra.FormallySmooth.of_perfectField
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk Q.genericPoint)
  have hsurj : Function.Surjective (algebraMap (Y.presheaf.stalk Q.genericPoint)
      (IsLocalRing.ResidueField (Y.presheaf.stalk Q.genericPoint))) :=
    IsLocalRing.residue_surjective
  have hker : RingHom.ker (algebraMap (Y.presheaf.stalk Q.genericPoint)
      (IsLocalRing.ResidueField (Y.presheaf.stalk Q.genericPoint))) = Ideal.span {ϖ} := by
    change RingHom.ker (IsLocalRing.residue _) = _
    rw [IsLocalRing.ker_residue, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
  have hϖ2 : ϖ ∉ RingHom.ker (algebraMap (Y.presheaf.stalk Q.genericPoint)
      (IsLocalRing.ResidueField (Y.presheaf.stalk Q.genericPoint))) ^ 2 :=
    hker ▸ notMem_span_singleton_sq_of_irreducible hϖ
  have h := finrank_kaehlerDifferential_add_one (k := k) hsurj hker hϖ2
  rw [Q.finrank_kaehlerDifferential_localRing (sX := sY)] at h
  omega

/-- In a discrete valuation ring, an element of `𝔪 ∖ 𝔪²` is irreducible. -/
private theorem irreducible_of_mem_maximalIdeal_of_notMem_sq {V : Type*} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] {u : V} (hu : u ∈ IsLocalRing.maximalIdeal V)
    (hu2 : u ∉ IsLocalRing.maximalIdeal V ^ 2) : Irreducible u := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hu0 : u ≠ 0 := by rintro rfl; exact hu2 (zero_mem _)
  obtain ⟨k, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hu0 hϖ
  rcases k with _ | _ | k
  · exact absurd (by simpa using v.isUnit) ((IsLocalRing.mem_maximalIdeal _).mp hu)
  · simpa using (irreducible_isUnit_mul v.isUnit).mpr hϖ
  · exfalso
    apply hu2
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨v * ϖ ^ k, by ring⟩

/-- The restriction maps of stalks along a morphism over `k` are `k`-algebra maps. -/
private theorem stalkMap_algebraMap {k : Type u} [Field k] {X T : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (j : T ⟶ X) (t : T) (c : k) :
    (j.stalkMap t).hom (letI := stalkAlgebra sX (j t); algebraMap k _ c) =
      (letI := stalkAlgebra (j ≫ sX) t; algebraMap k _ c) := by
  have h : (Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ sX).appTop ≫
        T.presheaf.germ ⊤ t (TopologicalSpace.Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ (j t) (TopologicalSpace.Opens.mem_top _)) ≫ j.stalkMap t := by
    simp only [Category.assoc, Scheme.Hom.germ_stalkMap, Scheme.Hom.comp_appTop]
    rfl
  exact (congrArg (fun f => f.hom c) h).symm

open exteriorPower in
/-- **A Noether-normalization chart at a codimension-one point of a normal prime divisor.** Let
`X` be a normal variety over `k` of dimension `n + 1`, `j : T ⟶ X` the inclusion of a normal prime
divisor `P`, `Q` a prime divisor of `T`, `x = j(η_Q)` and `p ⊂ 𝒪_{X,x}` the prime of `P`. Then
`n = n' + 1`, and there are an affine open `U ∋ x` and a finite injective
`ν : k[X₀, …, X_n] → Γ(X, U)` with `p ∩ k[X] = (X₀)` and `𝔪_x ∩ k[X] = (X₀, w)`,
`w = w'(X₁, …, X_n) ∉ (X₀)` (`exists_finite_comap_eq_span_X_zero_of_isLocalization`), where
`𝒪_{X,x,p}` and `𝒪_{X,x} / p = 𝒪_{T,Q}` are discrete valuation rings. Moreover:
* `ν` induces compatible charts `k[X] → 𝒪_{X,z}` at every generization `z` of `x`;
* the residue chart `ν_T : k[X₁, …, X_n] → 𝒪_{T,Q}` is injective, with
  `𝔪_Q ∩ k[X₁, …, X_n] = (w')`, `𝒪_{T,Q}` a ring of fractions of elements integral over it,
  `ν_T w' = u tᵉ` for a uniformizer `t` and a unit `u`, and
  `ord_Q (f dX̄₁ ∧ ⋯ ∧ dX̄_n) = ord_Q f + e - 1` (`exists_ordForm_smul_tprod_ιMulti_eq`);
* along `P`, `X₀ ∈ 𝔪_P` is nonzero, and the restricted coordinates `dX̄₁, …, dX̄_n` are those of
  `ν_T`, linearly independent in `Ω_{k(T)}`. -/
theorem exists_noetherNormalization_chart_of_primeDivisor
    {k : Type} [Field k] [CharZero k] {X T : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (Q : Mori.PrimeDivisor T) :
    letI := functionFieldAlgebra sX
    letI := stalkAlgebra (j ≫ sX) Q.genericPoint
    letI := functionFieldAlgebra (j ≫ sX)
    ∃ n' : ℕ, n = n' + 1 ∧ ∃ (U : X.Opens) (_ : IsAffineOpen U) (hxU : j Q.genericPoint ∈ U),
    letI := sectionAlgebra sX U
    letI : Algebra Γ(X, U) (X.presheaf.stalk (j Q.genericPoint)) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨_, hxU⟩
    ∃ ν : MvPolynomial (Fin (n' + 1 + 1)) k →ₐ[k] Γ(X, U), Function.Injective ν ∧
      ν.toRingHom.IsIntegral ∧
      IsDiscreteValuationRing (Localization.AtPrime ((IsLocalRing.maximalIdeal (X.presheaf.stalk (j (genericPoint T)))).comap
          (X.presheaf.stalkSpecializes
            (j.base.hom.map_specializes (genericPoint_specializes Q.genericPoint))).hom)) ∧
      IsDiscreteValuationRing (X.presheaf.stalk (j Q.genericPoint) ⧸ ((IsLocalRing.maximalIdeal (X.presheaf.stalk (j (genericPoint T)))).comap
          (X.presheaf.stalkSpecializes
            (j.base.hom.map_specializes (genericPoint_specializes Q.genericPoint))).hom)) ∧
      (∀ a, (j.stalkMap Q.genericPoint).hom a = 0 ↔ a ∈ ((IsLocalRing.maximalIdeal (X.presheaf.stalk (j (genericPoint T)))).comap
          (X.presheaf.stalkSpecializes
            (j.base.hom.map_specializes (genericPoint_specializes Q.genericPoint))).hom)) ∧
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk (j (genericPoint T)))).comap
          (X.presheaf.stalkSpecializes
            (j.base.hom.map_specializes (genericPoint_specializes Q.genericPoint))).hom).comap
        ((algebraMap Γ(X, U) (X.presheaf.stalk (j Q.genericPoint))).comp ν.toRingHom) =
          Ideal.span {MvPolynomial.X 0} ∧
      ∃ w' : MvPolynomial (Fin (n' + 1)) k, w' ≠ 0 ∧
        MvPolynomial.rename Fin.succ w' ∉
          Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n' + 1 + 1)) k)} ∧
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (j Q.genericPoint))).comap
          ((algebraMap Γ(X, U) (X.presheaf.stalk (j Q.genericPoint))).comp ν.toRingHom) =
          Ideal.span {MvPolynomial.X 0, MvPolynomial.rename Fin.succ w'} ∧
        (∀ a, MvPolynomial.rename Fin.succ a ∈ (IsLocalRing.maximalIdeal (X.presheaf.stalk (j Q.genericPoint))).comap
          ((algebraMap Γ(X, U) (X.presheaf.stalk (j Q.genericPoint))).comp ν.toRingHom) ↔ a ∈ Ideal.span {w'}) ∧
        (∀ (z : X) (hz : z ⤳ j Q.genericPoint), ∃ νz : (letI := stalkAlgebra sX z;
          MvPolynomial (Fin (n' + 1 + 1)) k →ₐ[k] X.presheaf.stalk z), ∀ d, νz d =
            (X.presheaf.stalkSpecializes hz).hom (algebraMap Γ(X, U) (X.presheaf.stalk (j Q.genericPoint)) (ν d))) ∧
        (∀ (z : X) (hz : z ⤳ j Q.genericPoint) (νz : (letI := stalkAlgebra sX z;
          MvPolynomial (Fin (n' + 1 + 1)) k →ₐ[k] X.presheaf.stalk z)), (∀ d, νz d =
            (X.presheaf.stalkSpecializes hz).hom (algebraMap Γ(X, U) (X.presheaf.stalk (j Q.genericPoint)) (ν d))) → ∀ d,
          algebraMap (X.presheaf.stalk z) X.functionField (νz d) =
            algebraMap (X.presheaf.stalk (j Q.genericPoint)) X.functionField (algebraMap Γ(X, U) (X.presheaf.stalk (j Q.genericPoint)) (ν d))) ∧
        ∃ νT : MvPolynomial (Fin (n' + 1)) k →ₐ[k] T.presheaf.stalk Q.genericPoint,
          (∀ a, νT a = (j.stalkMap Q.genericPoint).hom
            (algebraMap Γ(X, U) (X.presheaf.stalk (j Q.genericPoint)) (ν (MvPolynomial.rename Fin.succ a)))) ∧
          Function.Injective νT ∧
          (IsLocalRing.maximalIdeal (T.presheaf.stalk Q.genericPoint)).comap νT =
            Ideal.span {w'} ∧
          (∀ y : T.presheaf.stalk Q.genericPoint, ∃ a b : T.presheaf.stalk Q.genericPoint,
            (νT : MvPolynomial (Fin (n' + 1)) k →+* _).IsIntegralElem a ∧
            (νT : MvPolynomial (Fin (n' + 1)) k →+* _).IsIntegralElem b ∧ IsUnit b ∧ y * b = a) ∧
          (∃ (tQ uQ : T.presheaf.stalk Q.genericPoint) (eQ : ℕ), Irreducible tQ ∧ IsUnit uQ ∧
            1 ≤ eQ ∧ νT w' = uQ * tQ ^ eQ ∧
            ιMulti T.functionField (n' + 1) (fun i => KaehlerDifferential.D k T.functionField
              (algebraMap _ T.functionField (νT (MvPolynomial.X i)))) ≠ 0 ∧
            ∀ f : T.functionField, f ≠ 0 →
              Q.ordForm (m := 1) ((f • PiTensorProduct.tprod T.functionField (fun _ : Fin 1 =>
                ιMulti T.functionField (n' + 1) (fun i => KaehlerDifferential.D k T.functionField
                  (algebraMap _ T.functionField (νT (MvPolynomial.X i))))) :
                TensorPower T.functionField 1 (⋀[T.functionField]^(n' + 1)
                  Ω[T.functionField⁄k])) : RationalPluriForms (j ≫ sX) (n' + 1) 1) =
                T.ord f Q.genericPoint + ((eQ : ℤ) - 1)) ∧
          ∀ νy : (letI := stalkAlgebra sX (j (genericPoint T));
            MvPolynomial (Fin (n' + 1 + 1)) k →ₐ[k] X.presheaf.stalk (j (genericPoint T))),
            (∀ d, νy d = (X.presheaf.stalkSpecializes
              (j.base.hom.map_specializes (genericPoint_specializes Q.genericPoint))).hom
                (algebraMap Γ(X, U) (X.presheaf.stalk (j Q.genericPoint)) (ν d))) →
            νy (MvPolynomial.X 0) ∈
              IsLocalRing.maximalIdeal (X.presheaf.stalk (j (genericPoint T))) ∧
            νy (MvPolynomial.X 0) ≠ 0 ∧
            (fun i : Fin (n' + 1) => KaehlerDifferential.D k T.functionField
              (algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
                (νT (MvPolynomial.X i)))) =
              (fun i => KaehlerDifferential.D k T.functionField
                ((j.stalkMap (genericPoint T)).hom (νy (MvPolynomial.X i.succ)))) ∧
            LinearIndependent T.functionField (fun i : Fin (n' + 1) =>
              KaehlerDifferential.D k T.functionField
                ((j.stalkMap (genericPoint T)).hom (νy (MvPolynomial.X i.succ)))) := by
  classical
  have hlft : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
  letI := functionFieldAlgebra sX
  have hd : (Algebra.trdeg k X.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
  have hjT := map_genericPoint_eq j P hP
  have hdT : (letI := functionFieldAlgebra (j ≫ sX); (Algebra.trdeg k T.functionField).toNat) =
      n := by
    have := trdeg_add_one_of_eq_genericPoint (sY := sX) (j := j) P hjT
    omega
  -- the points `y = η_P` and `x = j(η_Q)`
  have hyx : j (genericPoint T) ⤳ j Q.genericPoint :=
    j.base.hom.map_specializes (genericPoint_specializes _)
  obtain ⟨hdvrY, hfreeY, hfinY, hsmY, hcohY, hrankY⟩ :=
    stalk_facts_of_eq_genericPoint (sY := sX) P hjT
  -- an affine chart `U ∋ x`
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (j Q.genericPoint)) isOpen_univ
  have hU' : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  letI := sectionAlgebra sX U
  haveI := finiteType_sectionAlgebra sX hU'
  letI : Algebra Γ(X, U) (X.presheaf.stalk (j Q.genericPoint)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨_, hxU⟩
  haveI := hU'.isLocalization_stalk ⟨_, hxU⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU'
  haveI := functionField_isScalarTower X U ⟨_, hxU⟩
  haveI : IsIntegrallyClosed (X.presheaf.stalk (j Q.genericPoint)) :=
    IsNormal.stalk_normal (j Q.genericPoint)
  set 𝔮 := (hU'.primeIdealOf ⟨_, hxU⟩).asIdeal with h𝔮
  -- the prime `p` of `P` in `𝒪_{X,x}`, with `𝒪_{X,x} / p = 𝒪_{T,Q}`
  set p := (IsLocalRing.maximalIdeal (X.presheaf.stalk (j (genericPoint T)))).comap
    (X.presheaf.stalkSpecializes hyx).hom with hpdef
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  haveI := hdvrY
  have hpA : IsDiscreteValuationRing (Localization.AtPrime p) :=
    isDiscreteValuationRing_localization_comap hyx
  have hkerp := ker_stalkMap_eq_comap_stalkSpecializes j Q.genericPoint hyx
  let eT : (X.presheaf.stalk (j Q.genericPoint) ⧸ p) ≃+* T.presheaf.stalk Q.genericPoint :=
    (Ideal.quotEquivOfEq hkerp.symm).trans (RingHom.quotientKerEquivOfSurjective
      (SurjectiveOnStalks.stalkMap_surjective j Q.genericPoint))
  haveI : IsDomain (X.presheaf.stalk (j Q.genericPoint) ⧸ p) := Ideal.Quotient.isDomain p
  haveI : IsDiscreteValuationRing (X.presheaf.stalk (j Q.genericPoint) ⧸ p) := by
    haveI := Q.isDiscreteValuationRing_localRing
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eT.symm
  -- Noether normalization adapted to `p ⊂ 𝔪_x`
  obtain ⟨s, ν, hν, hνint, hpX, w', hw'0, hw'X, hv, hiff⟩ :=
    exists_finite_comap_eq_span_X_zero_of_isLocalization (k := k) 𝔮 p hpA
  -- the base `D = k[X₀, …, X_s]` and its algebra structures
  letI : Algebra (MvPolynomial (Fin (s + 1)) k) Γ(X, U) := ν.toRingHom.toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin (s + 1)) k) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq fun c => (ν.commutes c).symm
  haveI : Algebra.IsIntegral (MvPolynomial (Fin (s + 1)) k) Γ(X, U) := ⟨hνint⟩
  haveI : Algebra.FiniteType (MvPolynomial (Fin (s + 1)) k) Γ(X, U) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  haveI : Module.Finite (MvPolynomial (Fin (s + 1)) k) Γ(X, U) := Algebra.IsIntegral.finite
  haveI : FaithfulSMul (MvPolynomial (Fin (s + 1)) k) Γ(X, U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hν
  letI : Algebra (MvPolynomial (Fin (s + 1)) k) (X.presheaf.stalk (j Q.genericPoint)) :=
    ((algebraMap Γ(X, U) (X.presheaf.stalk (j Q.genericPoint))).comp
      (algebraMap (MvPolynomial (Fin (s + 1)) k) Γ(X, U))).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin (s + 1)) k) Γ(X, U)
      (X.presheaf.stalk (j Q.genericPoint)) := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra (MvPolynomial (Fin (s + 1)) k) X.functionField :=
    ((algebraMap Γ(X, U) X.functionField).comp
      (algebraMap (MvPolynomial (Fin (s + 1)) k) Γ(X, U))).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin (s + 1)) k) Γ(X, U) X.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower (MvPolynomial (Fin (s + 1)) k) (X.presheaf.stalk (j Q.genericPoint))
      X.functionField := IsScalarTower.of_algebraMap_eq fun d => by
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin (s + 1)) k) Γ(X, U) X.functionField,
      IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk (j Q.genericPoint))
        X.functionField]
    rfl
  -- `s = n`, by transcendence degree
  have hsn : s = n := by
    haveI : IsScalarTower k (MvPolynomial (Fin (s + 1)) k) X.functionField :=
      IsScalarTower.of_algebraMap_eq fun c => by
        haveI := isScalarTower_section_functionField sX U
        rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin (s + 1)) k) Γ(X, U) X.functionField,
          ← IsScalarTower.algebraMap_apply k (MvPolynomial (Fin (s + 1)) k) Γ(X, U),
          ← IsScalarTower.algebraMap_apply k Γ(X, U) X.functionField]
    haveI : FaithfulSMul (MvPolynomial (Fin (s + 1)) k) X.functionField :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr
        ((IsFractionRing.injective Γ(X, U) X.functionField).comp hν)
    haveI : Algebra.IsAlgebraic (MvPolynomial (Fin (s + 1)) k) X.functionField := ⟨fun z => by
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) z
      have hint : ∀ r : Γ(X, U), IsIntegral (MvPolynomial (Fin (s + 1)) k)
          (algebraMap Γ(X, U) X.functionField r) := fun r =>
        (hνint r).map _
      exact (hint a).isAlgebraic.mul (hint b).isAlgebraic.inv⟩
    have := trdeg_eq_of_isAlgebraic (k := k) (L := X.functionField) (s := s + 1)
    omega
  subst s
  -- `n ≥ 1`, since `T` has the prime divisor `Q`
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 :=
    ⟨n - 1, by have := one_le_trdeg_of_primeDivisor (j ≫ sX) Q; omega⟩
  -- notation-free facts on the base
  have hDA : ∀ d, algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k)
      (X.presheaf.stalk (j Q.genericPoint)) d =
      algebraMap Γ(X, U) (X.presheaf.stalk (j Q.genericPoint)) (ν d) := fun d => rfl
  have hDK : ∀ d, algebraMap (X.presheaf.stalk (j Q.genericPoint)) X.functionField
      (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) (X.presheaf.stalk (j Q.genericPoint)) d) =
      algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) X.functionField d := fun d =>
    (IsScalarTower.algebraMap_apply _ _ _ d).symm
  have hDKinj : Function.Injective (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k)
      X.functionField) := (IsFractionRing.injective Γ(X, U) X.functionField).comp hν
  have hCA : ∀ c : k, algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k)
      (X.presheaf.stalk (j Q.genericPoint)) (MvPolynomial.C c) =
      (letI := stalkAlgebra sX (j Q.genericPoint); algebraMap k _ c) := by
    intro c
    letI := stalkAlgebra sX (j Q.genericPoint)
    haveI := isScalarTower_section_stalk sX U ⟨_, hxU⟩
    rw [hDA, ← MvPolynomial.algebraMap_eq, ν.commutes]
    exact (IsScalarTower.algebraMap_apply k Γ(X, U) (X.presheaf.stalk (j Q.genericPoint)) c).symm
  -- the base maps to the stalks at the generizations of `x`
  have mkν : ∀ (z : X) (hz : z ⤳ j Q.genericPoint), ∃ νz : (letI := stalkAlgebra sX z;
      MvPolynomial (Fin (n' + 1 + 1)) k →ₐ[k] X.presheaf.stalk z), ∀ d, νz d =
        (X.presheaf.stalkSpecializes hz).hom (algebraMap _
          (X.presheaf.stalk (j Q.genericPoint)) d) := by
    intro z hz
    letI := stalkAlgebra sX z
    letI := stalkAlgebra sX (j Q.genericPoint)
    letI := (X.presheaf.stalkSpecializes hz).hom.toAlgebra
    haveI := isScalarTower_stalkSpecializes' sX hz
    refine ⟨⟨(X.presheaf.stalkSpecializes hz).hom.comp (algebraMap _ _), fun c => ?_⟩,
      fun d => rfl⟩
    change (X.presheaf.stalkSpecializes hz).hom (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k)
      (X.presheaf.stalk (j Q.genericPoint)) (MvPolynomial.C c)) = _
    rw [hCA]
    exact (IsScalarTower.algebraMap_apply k (X.presheaf.stalk (j Q.genericPoint))
      (X.presheaf.stalk z) c).symm
  have hνK : ∀ (z : X) (hz : z ⤳ j Q.genericPoint) (νz : (letI := stalkAlgebra sX z;
      MvPolynomial (Fin (n' + 1 + 1)) k →ₐ[k] X.presheaf.stalk z)), (∀ d, νz d =
        (X.presheaf.stalkSpecializes hz).hom (algebraMap _
          (X.presheaf.stalk (j Q.genericPoint)) d)) → ∀ d,
      algebraMap (X.presheaf.stalk z) X.functionField (νz d) =
        algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) X.functionField d := by
    intro z hz νz hνz d
    rw [hνz, algebraMap_stalkSpecializes', hDK]
  -- the residue chart `k[X₁, …, X_n] → 𝒪_{T,Q}`
  letI := stalkAlgebra (j ≫ sX) Q.genericPoint
  letI := functionFieldAlgebra (j ≫ sX)
  obtain ⟨νT, hνT⟩ : ∃ νT : MvPolynomial (Fin (n' + 1)) k →ₐ[k] T.presheaf.stalk Q.genericPoint,
      ∀ a, νT a = (j.stalkMap Q.genericPoint).hom (algebraMap _
        (X.presheaf.stalk (j Q.genericPoint)) (MvPolynomial.rename Fin.succ a)) :=
    ⟨⟨(j.stalkMap Q.genericPoint).hom.comp ((algebraMap _ _).comp
      (MvPolynomial.rename Fin.succ).toRingHom), fun c => by
        change (j.stalkMap Q.genericPoint).hom (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k)
          (X.presheaf.stalk (j Q.genericPoint)) (MvPolynomial.rename Fin.succ
            (MvPolynomial.C c))) = _
        rw [MvPolynomial.rename_C, hCA]
        exact stalkMap_algebraMap sX j Q.genericPoint c⟩, fun a => rfl⟩
  have hX0p : algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k)
      (X.presheaf.stalk (j Q.genericPoint)) (MvPolynomial.X 0) ∈ p := by
    have : (MvPolynomial.X 0 : MvPolynomial (Fin (n' + 1 + 1)) k) ∈
        p.comap ((algebraMap Γ(X, U) (X.presheaf.stalk (j Q.genericPoint))).comp ν.toRingHom) := by
      rw [hpX]; exact Ideal.mem_span_singleton_self _
    exact this
  have hkerT : ∀ a, (j.stalkMap Q.genericPoint).hom a = 0 ↔ a ∈ p := fun a => by
    rw [← RingHom.mem_ker, hkerp]
  have hνTinj : Function.Injective νT := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    rw [hνT, hkerT] at ha
    apply eq_zero_of_rename_mem k
    rwa [← hpX]
  have hfT : (IsLocalRing.maximalIdeal (T.presheaf.stalk Q.genericPoint)).comap νT =
      Ideal.span {w'} := by
    ext a
    rw [Ideal.mem_comap, hνT, ← Ideal.mem_comap,
      IsLocalRing.maximalIdeal_comap (j.stalkMap Q.genericPoint).hom]
    exact hiff a
  have hcompT : ((j.stalkMap Q.genericPoint).hom.comp
      (algebraMap Γ(X, U) (X.presheaf.stalk (j Q.genericPoint)))).comp ν.toRingHom =
      (νT : MvPolynomial (Fin (n' + 1)) k →+* _).comp (dropZero k (n' + 1)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hνT,
        AlgHom.coe_toRingHom, dropZero, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
        MvPolynomial.rename_C]
      rfl
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          AlgHom.coe_toRingHom, dropZero, MvPolynomial.aeval_X, Fin.cases_zero, map_zero]
        exact (hkerT _).mpr hX0p
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          AlgHom.coe_toRingHom, dropZero, MvPolynomial.aeval_X, Fin.cases_succ, hνT,
          MvPolynomial.rename_X]
        rfl
  have halgT : ∀ y : T.presheaf.stalk Q.genericPoint, ∃ a b : T.presheaf.stalk Q.genericPoint,
      (νT : MvPolynomial (Fin (n' + 1)) k →+* _).IsIntegralElem a ∧
      (νT : MvPolynomial (Fin (n' + 1)) k →+* _).IsIntegralElem b ∧ IsUnit b ∧ y * b = a := by
    intro y
    obtain ⟨a, b, ha, hb, hbu, hyb⟩ := exists_isIntegralElem_mul_eq 𝔮 ν.toRingHom hνint
      (j.stalkMap Q.genericPoint).hom (fun y => by
        obtain ⟨a, rfl⟩ := SurjectiveOnStalks.stalkMap_surjective j Q.genericPoint y
        exact ⟨a, 1, by rw [map_one]; exact isUnit_one, by rw [map_one, mul_one]⟩) y
    rw [hcompT] at ha hb
    exact ⟨a, b, ha.of_comp, hb.of_comp,
      hbu, hyb⟩
  obtain ⟨tQ, uQ, eQ, htQ, huQ, heQ, hwQ, hιT, hordT⟩ :=
    exists_ordForm_smul_tprod_ιMulti_eq (j ≫ sX) hdT Q νT hνTinj hw'0 hfT halgT
  refine ⟨n', rfl, U, hU', hxU, ν, hν, hνint, hpA, ‹_›, hkerT, hpX, w', hw'0, hw'X, hv, hiff,
    fun z hz => mkν z hz, fun z hz νz hνz d => (hνK z hz νz hνz d).trans (hDK d).symm, νT, hνT,
    hνTinj, hfT, halgT, ⟨tQ, uQ, eQ, htQ, huQ, heQ, hwQ, hιT, hordT⟩, fun νy hνy' => ?_⟩
  have hνy : ∀ d, νy d = (X.presheaf.stalkSpecializes hyx).hom (algebraMap _
      (X.presheaf.stalk (j Q.genericPoint)) d) := hνy'
  -- the restricted coordinates `X̄₁, …, X̄_n`
  have hsqT : ∀ a, algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
      ((j.stalkMap Q.genericPoint).hom a) =
      (j.stalkMap (genericPoint T)).hom ((X.presheaf.stalkSpecializes hyx).hom a) := fun a =>
    (Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ (genericPoint_specializes _) a).symm
  have hfamT : (fun i : Fin (n' + 1) => KaehlerDifferential.D k T.functionField
      (algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField (νT (MvPolynomial.X i)))) =
      (fun i => KaehlerDifferential.D k T.functionField
        ((j.stalkMap (genericPoint T)).hom (νy (MvPolynomial.X i.succ)))) := by
    funext i
    rw [hνT, hνy, MvPolynomial.rename_X, hsqT]
  refine ⟨?_, ?_, hfamT, ?_⟩
  · rw [hνy]; exact hX0p
  · intro h
    have := congrArg (algebraMap _ X.functionField) h
    rw [hνK _ hyx νy hνy, map_zero] at this
    exact MvPolynomial.X_ne_zero 0 (hDKinj (this.trans (map_zero _).symm))
  · rw [← hfamT]
    by_contra h
    exact hιT (AlternatingMap.map_linearDependent _ _ h)

/-- **A rational top form with a simple pole along a normal prime divisor and a nonzero
residue.** Let `X` be a normal variety of dimension `n + 1` over a field `k` of characteristic
zero, `j : T ⟶ X` the inclusion of a normal prime divisor `P` and `Q` a prime divisor of `T`, with
`x = j(η_Q)`. There is a rational top form `σ ≠ 0` on `X` with `ord_P σ = -1`, no pole along any
other prime divisor through `x`, and a nonzero Poincaré residue `ρ_σ` along `T` without zero
at `Q`. It is `F dX₀ ∧ ⋯ ∧ dX_n` for a Noether normalization adapted to `P ∋ x`
(`exists_noetherNormalization_chart_of_primeDivisor`) and the trace-dual lift `F` of a
uniformizer at `Q` (`exists_residue_lift_ring`). -/
theorem exists_form_of_residue_order
    {k : Type} [Field k] [CharZero k] {X T : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (Q : Mori.PrimeDivisor T) :
    ∃ σ : RationalPluriForms sX (n + 1) 1, σ ≠ 0 ∧ P.ordForm σ = -1 ∧
      (∀ E : Mori.PrimeDivisor X, j Q.genericPoint ∈ E.support → E ≠ P → 0 ≤ E.ordForm σ) ∧
      ∃ ρσ : RationalPluriForms (j ≫ sX) n 1, IsPoincareResidue sX j n 1 σ ρσ ∧ ρσ ≠ 0 ∧
        Q.ordForm ρσ ≤ 0 := by
  classical
  have hlft : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
  letI := functionFieldAlgebra sX
  have hjT := map_genericPoint_eq j P hP
  -- the point `y = η_P` specializing to `x = j(η_Q)`
  have hyx : j (genericPoint T) ⤳ j Q.genericPoint :=
    j.base.hom.map_specializes (genericPoint_specializes _)
  -- the prime `p` of `P` in `𝒪_{X,x}`, with `𝒪_{X,x} / p = 𝒪_{T,Q}`
  set p := (IsLocalRing.maximalIdeal (X.presheaf.stalk (j (genericPoint T)))).comap
    (X.presheaf.stalkSpecializes hyx).hom with hpdef
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  -- the Noether-normalization chart
  obtain ⟨n', rfl, U, hU', hxU, ν, hν, hνint, hpA, hdvrQ, hkerT, hpX, w', hw'0, hw'X, hv, -,
    mkν₀, hνK₀, νT, hνT₀, -, -, -, ⟨tQ, uQ, eQ, htQ, huQ, heQ, hwQ, hιT, hordT⟩, hνyfacts⟩ :=
    exists_noetherNormalization_chart_of_primeDivisor sX hX hdim j hT P hP Q
  have hd : (Algebra.trdeg k X.functionField).toNat = n' + 1 + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  letI := sectionAlgebra sX U
  letI : Algebra Γ(X, U) (X.presheaf.stalk (j Q.genericPoint)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨_, hxU⟩
  haveI := hU'.isLocalization_stalk ⟨_, hxU⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU'
  haveI := functionField_isScalarTower X U ⟨_, hxU⟩
  haveI : IsIntegrallyClosed (X.presheaf.stalk (j Q.genericPoint)) :=
    IsNormal.stalk_normal (j Q.genericPoint)
  set 𝔮 := (hU'.primeIdealOf ⟨_, hxU⟩).asIdeal with h𝔮
  haveI := hdvrQ
  have hkerp : RingHom.ker (j.stalkMap Q.genericPoint).hom = p := by
    ext a; rw [RingHom.mem_ker]; exact hkerT a
  let eT : (X.presheaf.stalk (j Q.genericPoint) ⧸ p) ≃+* T.presheaf.stalk Q.genericPoint :=
    (Ideal.quotEquivOfEq hkerp.symm).trans (RingHom.quotientKerEquivOfSurjective
      (SurjectiveOnStalks.stalkMap_surjective j Q.genericPoint))
  -- the base `D = k[X₀, …, X_n]` and its algebra structures
  letI : Algebra (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U) := ν.toRingHom.toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq fun c => (ν.commutes c).symm
  haveI : Algebra.IsIntegral (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U) := ⟨hνint⟩
  haveI := finiteType_sectionAlgebra sX hU'
  haveI : Algebra.FiniteType (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  haveI : Module.Finite (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U) := Algebra.IsIntegral.finite
  haveI : FaithfulSMul (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hν
  letI : Algebra (MvPolynomial (Fin (n' + 1 + 1)) k) (X.presheaf.stalk (j Q.genericPoint)) :=
    ((algebraMap Γ(X, U) (X.presheaf.stalk (j Q.genericPoint))).comp
      (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U))).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U)
      (X.presheaf.stalk (j Q.genericPoint)) := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra (MvPolynomial (Fin (n' + 1 + 1)) k) X.functionField :=
    ((algebraMap Γ(X, U) X.functionField).comp
      (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U))).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U) X.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower (MvPolynomial (Fin (n' + 1 + 1)) k) (X.presheaf.stalk (j Q.genericPoint))
      X.functionField := IsScalarTower.of_algebraMap_eq fun d => by
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U) X.functionField,
      IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk (j Q.genericPoint))
        X.functionField]
    rfl
  -- the trace-dual lift `F`
  obtain ⟨F, hFE, s₀, a₀, hs₀, hFP, N, u, hN, hum, hum2, hrel⟩ :=
    exists_residue_lift_ring k (D := MvPolynomial (Fin (n' + 1 + 1)) k) (R := Γ(X, U))
      (A := X.presheaf.stalk (j Q.genericPoint)) (K := X.functionField) 𝔮 p hpA
      (x₀ := MvPolynomial.X 0) (w := MvPolynomial.rename Fin.succ w') (MvPolynomial.X_ne_zero 0)
      (Ideal.isPrime_span_singleton_of_prime MvPolynomial.X_prime) hpX hw'X hv
  -- the chart in the notation of the base
  have hDK : ∀ d, algebraMap (X.presheaf.stalk (j Q.genericPoint)) X.functionField
      (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) (X.presheaf.stalk (j Q.genericPoint)) d) =
      algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) X.functionField d := fun d =>
    (IsScalarTower.algebraMap_apply _ _ _ d).symm
  have hDKinj : Function.Injective (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k)
      X.functionField) := (IsFractionRing.injective Γ(X, U) X.functionField).comp hν
  have mkν : ∀ (z : X) (hz : z ⤳ j Q.genericPoint), ∃ νz : (letI := stalkAlgebra sX z;
      MvPolynomial (Fin (n' + 1 + 1)) k →ₐ[k] X.presheaf.stalk z), ∀ d, νz d =
        (X.presheaf.stalkSpecializes hz).hom (algebraMap _
          (X.presheaf.stalk (j Q.genericPoint)) d) := mkν₀
  have hνK : ∀ (z : X) (hz : z ⤳ j Q.genericPoint) (νz : (letI := stalkAlgebra sX z;
      MvPolynomial (Fin (n' + 1 + 1)) k →ₐ[k] X.presheaf.stalk z)), (∀ d, νz d =
        (X.presheaf.stalkSpecializes hz).hom (algebraMap _
          (X.presheaf.stalk (j Q.genericPoint)) d)) → ∀ d,
      algebraMap (X.presheaf.stalk z) X.functionField (νz d) =
        algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) X.functionField d := fun z hz νz hνz d =>
    (hνK₀ z hz νz hνz d).trans (hDK d)
  letI := stalkAlgebra (j ≫ sX) Q.genericPoint
  letI := functionFieldAlgebra (j ≫ sX)
  have hνT : ∀ a, νT a = (j.stalkMap Q.genericPoint).hom (algebraMap _
      (X.presheaf.stalk (j Q.genericPoint)) (MvPolynomial.rename Fin.succ a)) := hνT₀
  obtain ⟨νy, hνy⟩ := mkν _ hyx
  obtain ⟨hX0m, hX00, hfamT, hy⟩ := hνyfacts νy hνy
  -- the residue along `P`
  -- the restricted coordinates `X̄₁, …, X̄_n`
  have hsqT : ∀ a, algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
      ((j.stalkMap Q.genericPoint).hom a) =
      (j.stalkMap (genericPoint T)).hom ((X.presheaf.stalkSpecializes hyx).hom a) := fun a =>
    (Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ (genericPoint_specializes _) a).symm
  have hs₀u : IsUnit ((X.presheaf.stalkSpecializes hyx).hom s₀) := by
    by_contra h
    exact hs₀ ((IsLocalRing.mem_maximalIdeal _).mpr h)
  set g₀ := (X.presheaf.stalkSpecializes hyx).hom a₀ * ↑hs₀u.unit⁻¹ with hg₀def
  have hinvs : algebraMap (X.presheaf.stalk (j (genericPoint T))) X.functionField
      (↑hs₀u.unit⁻¹ : X.presheaf.stalk (j (genericPoint T))) *
      algebraMap (X.presheaf.stalk (j Q.genericPoint)) X.functionField s₀ = 1 := by
    rw [← algebraMap_stalkSpecializes' X hyx s₀, ← map_mul]
    simp
  have hFg : F * algebraMap _ X.functionField (νy (MvPolynomial.X 0)) =
      algebraMap _ X.functionField g₀ := by
    rw [hνK _ hyx νy hνy, hg₀def, map_mul, algebraMap_stalkSpecializes' X hyx a₀, ← hFP]
    linear_combination (-(F * algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) X.functionField
      (MvPolynomial.X 0))) * hinvs
  obtain ⟨e, he, hres, hPord⟩ :=
    exists_isPoincareResidue_smul_tprod_ιMulti sX hd j P hjT νy hX0m hX00 hy hFg
  -- the order of the residue at `Q`
  haveI := Q.isDiscreteValuationRing_localRing
  have hQcoh := Q.coheight_genericPoint
  set πQ := (j.stalkMap Q.genericPoint).hom with hπQ
  set algT := algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField with halgT
  have hinjT : Function.Injective algT := IsFractionRing.injective _ _
  have hπQs : πQ s₀ ≠ 0 := fun h => hs₀ ((hkerT s₀).mp h)
  have hβ : algT (πQ s₀) ≠ 0 := (map_ne_zero_iff _ hinjT).mpr hπQs
  have heTmk : ∀ a, eT (Ideal.Quotient.mk p a) = πQ a := fun a => rfl
  have hrelT := congrArg (fun z => algT (eT z)) hrel
  simp only [map_mul, map_natCast, heTmk] at hrelT
  have hwν : πQ (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k)
      (X.presheaf.stalk (j Q.genericPoint)) (MvPolynomial.rename Fin.succ w')) = νT w' :=
    (hνT w').symm
  rw [hwν, hwQ, map_mul, map_pow] at hrelT
  have huirr : Irreducible (eT u) :=
    (MulEquiv.irreducible_iff eT.toMulEquiv).mpr
      (irreducible_of_mem_maximalIdeal_of_notMem_sq hum hum2)
  have htQ0 : algT tQ ≠ 0 := (map_ne_zero_iff _ hinjT).mpr htQ.ne_zero
  have hu0 : algT (eT u) ≠ 0 := (map_ne_zero_iff _ hinjT).mpr huirr.ne_zero
  haveI : CharZero T.functionField :=
    charZero_of_injective_algebraMap (algebraMap k T.functionField).injective
  have hN0 : (N : T.functionField) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hα : algT (πQ a₀) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hrelT
    exact mul_ne_zero hβ hu0 hrelT.symm
  have hordNat : ∀ n : ℕ, n ≠ 0 → T.ord (n : T.functionField) Q.genericPoint = 0 := by
    intro n hn
    have : (n : T.functionField) = algT (n : T.presheaf.stalk Q.genericPoint) := by simp
    rw [this]
    refine Q.ord_algebraMap_of_isUnit ?_
    rw [← map_natCast (algebraMap k (T.presheaf.stalk Q.genericPoint))]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hn)).map _
  have hordu := ord_algebraMap_eq_one_of_irreducible hQcoh huirr
  have hordt := ord_algebraMap_eq_one_of_irreducible hQcoh htQ
  have horduQ := Q.ord_algebraMap_of_isUnit huQ
  have huQ0 : algT uQ ≠ 0 := (huQ.map _).ne_zero
  have hordrel := congrArg (fun f => T.ord f Q.genericPoint) hrelT
  rw [Scheme.ord_mul (mul_ne_zero hN0 (mul_ne_zero huQ0 (pow_ne_zero _ htQ0))) hα,
    Scheme.ord_mul hN0 (mul_ne_zero huQ0 (pow_ne_zero _ htQ0)),
    Scheme.ord_mul huQ0 (pow_ne_zero _ htQ0), Scheme.ord_mul hβ hu0, hordNat N hN.ne', horduQ,
    ord_pow' htQ0, hordt, hordu] at hordrel
  -- `ḡ₀ = ā₀ / s̄₀`
  have hg₀T : (j.stalkMap (genericPoint T)).hom g₀ * algT (πQ s₀) = algT (πQ a₀) := by
    rw [hsqT, hsqT, hg₀def, map_mul, mul_assoc, ← map_mul, ← map_mul, hs₀u.val_inv_mul, mul_one]
  have hg₀0 : (j.stalkMap (genericPoint T)).hom g₀ ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hg₀T; exact hα hg₀T.symm
  have he0 : (e : T.functionField) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  have hordg := congrArg (fun f => T.ord f Q.genericPoint) hg₀T
  rw [Scheme.ord_mul hg₀0 hβ] at hordg
  have hQord := hordT _ (mul_ne_zero he0 hg₀0)
  rw [hfamT, Scheme.ord_mul he0 hg₀0, hordNat e he.ne'] at hQord
  -- `g₀` is a unit, so `σ` has a simple pole along `P`
  have hg₀u : IsUnit g₀ := by
    by_contra h
    apply hg₀0
    obtain ⟨-, hsurj⟩ := stalkMap_facts_of_isClosedImmersion (sY := sX) (j := j)
    have hker : RingHom.ker (j.stalkMap (genericPoint T)).hom =
        IsLocalRing.maximalIdeal (X.presheaf.stalk (j (genericPoint T))) :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)
    rw [← RingHom.mem_ker, hker]
    exact (IsLocalRing.mem_maximalIdeal _).mpr h
  have hσP := hPord hg₀u
  obtain ⟨σ, hσdef⟩ : ∃ σ : RationalPluriForms sX (n' + 1 + 1) 1,
      σ = ((F • PiTensorProduct.tprod X.functionField (fun _ : Fin 1 =>
        exteriorPower.ιMulti X.functionField (n' + 1 + 1) (fun i =>
          KaehlerDifferential.D k X.functionField
            (algebraMap _ X.functionField (νy (MvPolynomial.X i))))) :
        TensorPower X.functionField 1
          (⋀[X.functionField]^(n' + 1 + 1) Ω[X.functionField⁄k])) :
            RationalPluriForms sX (n' + 1 + 1) 1) := ⟨_, rfl⟩
  rw [← hσdef] at hσP hres
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    rw [PrimeDivisor.ordForm_zero] at hσP
    exact absurd hσP (by decide)
  have hF0 : F ≠ 0 := by
    rintro rfl
    apply hσ0
    rw [hσdef, zero_smul]
    rfl
  -- no pole along the other prime divisors through `x`
  have hEσ : ∀ E : Mori.PrimeDivisor X, j Q.genericPoint ∈ E.support → E ≠ P →
      0 ≤ E.ordForm σ := by
    intro E hE hEP
    have hEx : E.genericPoint ⤳ j Q.genericPoint := by
      rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    obtain ⟨νE, hνE⟩ := mkν _ hEx
    haveI := E.isDiscreteValuationRing_localRing
    obtain ⟨EA, hEAdef⟩ : ∃ EA : Ideal (X.presheaf.stalk (j Q.genericPoint)),
        EA = (IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint)).comap
          (X.presheaf.stalkSpecializes hEx).hom := ⟨_, rfl⟩
    haveI : EA.IsPrime := hEAdef ▸ Ideal.comap_isPrime _ _
    have hdvrE : IsDiscreteValuationRing (Localization.AtPrime EA) := by
      subst hEAdef; exact isDiscreteValuationRing_localization_comap hEx
    have hne : EA ≠ p := by
      intro h
      apply hEP
      rw [hEAdef] at h
      have := eq_of_comap_maximalIdeal_stalkSpecializes_eq hEx hyx h
      rw [hjT] at this
      exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective this
    obtain ⟨π, hπ0, hπ, sE, hsE, aE, haE, hFπ⟩ := hFE EA hdvrE hne
    have hfam : (fun i => KaehlerDifferential.D k X.functionField
        (algebraMap _ X.functionField (νE (MvPolynomial.X i)))) =
        (fun i => KaehlerDifferential.D k X.functionField
          (algebraMap _ X.functionField (νy (MvPolynomial.X i)))) := by
      funext i; rw [hνK _ hEx νE hνE, hνK _ hyx νy hνy]
    rw [hσdef, ← hfam]
    letI := stalkAlgebra sX E.genericPoint
    have hνEinj : Function.Injective νE := fun a b h => hDKinj (by
      rw [← hνK _ hEx νE hνE, ← hνK _ hEx νE hνE, h])
    have hfE : (IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint)).comap νE =
        Ideal.span {π} := by
      ext d
      rw [← hπ, Ideal.mem_comap, Ideal.mem_comap, hνE, hEAdef]
      exact Iff.rfl
    have hνEeq : (νE : MvPolynomial (Fin (n' + 1 + 1)) k →+* _) =
        (((X.presheaf.stalkSpecializes hEx).hom.comp
          (algebraMap Γ(X, U) (X.presheaf.stalk (j Q.genericPoint)))).comp ν.toRingHom) :=
      RingHom.ext hνE
    have halgE : ∀ y : X.presheaf.stalk E.genericPoint, ∃ a b : X.presheaf.stalk E.genericPoint,
        (νE : MvPolynomial (Fin (n' + 1 + 1)) k →+* _).IsIntegralElem a ∧
        (νE : MvPolynomial (Fin (n' + 1 + 1)) k →+* _).IsIntegralElem b ∧ IsUnit b ∧
          y * b = a := by
      rw [hνEeq]
      refine exists_isIntegralElem_mul_eq 𝔮 ν.toRingHom hνint _ fun y => ?_
      letI := (X.presheaf.stalkSpecializes hEx).hom.toAlgebra
      haveI := MMP.Intersection.isLocalization_stalkSpecializes hEx
      obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj ((IsLocalRing.maximalIdeal
        (X.presheaf.stalk E.genericPoint)).comap (X.presheaf.stalkSpecializes hEx).hom).primeCompl y
      exact ⟨a, s, IsLocalization.map_units _ s, h⟩
    have hsEu : IsUnit ((X.presheaf.stalkSpecializes hEx).hom sE) := by
      by_contra h
      exact hsE (hEAdef ▸ (IsLocalRing.mem_maximalIdeal _).mpr h)
    have haEm : (X.presheaf.stalkSpecializes hEx).hom aE ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint) := by
      rw [hEAdef] at haE; exact haE
    refine zero_le_ordForm_of_mul_mem_maximalIdeal sX hd E νE hνEinj hπ0 hfE halgE hF0 hsEu
      haEm ?_
    rwa [hνK _ hEx νE hνE, algebraMap_stalkSpecializes', algebraMap_stalkSpecializes']
  -- the residue
  have hιT' := hιT
  rw [hfamT] at hιT'
  refine ⟨σ, hσ0, hσP, hEσ, _, hres, ?_, ?_⟩
  · intro h
    rcases smul_eq_zero.mp h with h1 | h2
    · exact mul_ne_zero he0 hg₀0 h1
    · apply hιT'
      apply tprod_fin_one_injective (F := T.functionField)
      exact h2.trans (MultilinearMap.map_coord_zero _ (0 : Fin 1) rfl).symm
  · rw [hQord]
    omega

/-- **Residues lift at a codimension-one point of a normal prime divisor**, over a field `k` of
characteristic zero. Let `X` be a normal variety over `k` of dimension `n + 1`, `j : T ⟶ X` the
inclusion of a normal prime divisor `P` and `Q` a prime divisor of `T`. Every rational top form
`ρ` on `T` without pole at `Q` is the Poincaré residue (`MMP.Fourfold.IsPoincareResidue`) of a
rational top form `τ` on `X` with at most a simple pole along `P` and no pole along any other
prime divisor through `j(η_Q)`. Over `k = ℂ` this is `exists_isPoincareResidue_of_le_ordForm`. -/
theorem exists_isPoincareResidue_of_le_ordForm_of_charZero
    {k : Type} [Field k] [CharZero k] {X T : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (Q : Mori.PrimeDivisor T) (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : 0 ≤ Q.ordForm ρ) :
    ∃ τ : RationalPluriForms sX (n + 1) 1, -1 ≤ P.ordForm τ ∧
      (∀ E : Mori.PrimeDivisor X, j Q.genericPoint ∈ E.support → E ≠ P → 0 ≤ E.ordForm τ) ∧
      IsPoincareResidue sX j n 1 τ ρ := by
  classical
  have : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
  have hjT := map_genericPoint_eq j P hP
  obtain ⟨σ, hσ0, hσP, hσE, ρσ, hρσ, hρσ0, hρσQ⟩ :=
    exists_form_of_residue_order sX hX hdim j hT P hP Q
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (j ≫ sX)
  have hd : (Algebra.trdeg k X.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
  have hdT : (Algebra.trdeg k T.functionField).toNat = n := by
    have := trdeg_add_one_of_eq_genericPoint (sY := sX) (j := j) P hjT
    omega
  -- the top forms on `T` are a line
  have hrank : Module.finrank T.functionField (RationalPluriForms (j ≫ sX) n 1) = 1 := by
    have := essFiniteType_functionField (sX := j ≫ sX)
    have hK : Module.finrank T.functionField Ω[T.functionField⁄k] = n :=
      (finrank_kaehlerDifferential_eq_trdeg k T.functionField).trans hdT
    have : FiniteDimensional T.functionField Ω[T.functionField⁄k] :=
      (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k T.functionField).1
    have h1 : Module.finrank T.functionField (⋀[T.functionField]^n Ω[T.functionField⁄k]) = 1 := by
      rw [exteriorPower.finrank_eq, hK, Nat.choose_self]
    let b₀ := (Module.finBasisOfFinrankEq _ _ h1).reindex (Equiv.ofUnique (Fin 1) Unit)
    let bb : Module.Basis Unit T.functionField (RationalPluriForms (j ≫ sX) n 1) :=
      ZTensorPower.basis b₀ 1
    rw [Module.finrank_eq_card_basis bb, Fintype.card_unit]
  -- `ρ = g ρσ` with `g` regular at `Q`
  obtain ⟨g, hg⟩ := (finrank_eq_one_iff_of_nonzero' ρσ hρσ0).mp hrank ρ
  obtain ⟨a, ha⟩ : ∃ a : T.presheaf.stalk Q.genericPoint,
      algebraMap _ T.functionField a = g := by
    by_cases hg0 : g = 0
    · exact ⟨0, by rw [map_zero, hg0]⟩
    refine exists_algebraMap_eq_of_ord_nonneg Q hg0 ?_
    have := Q.ordForm_smul (sX := j ≫ sX) hdT hg0 hρσ0
    rw [hg] at this
    omega
  -- lift `g` to `b ∈ 𝒪_{X,x}`
  obtain ⟨b, hb⟩ := SurjectiveOnStalks.stalkMap_surjective j Q.genericPoint a
  have h' : genericPoint T ⤳ Q.genericPoint := genericPoint_specializes _
  have hyx : j (genericPoint T) ⤳ j Q.genericPoint := j.base.hom.map_specializes h'
  set b₁ := X.presheaf.stalkSpecializes hyx b with hb₁def
  have hb₁ : (j.stalkMap (genericPoint T)).hom b₁ = g := by
    rw [hb₁def, Scheme.Hom.stalkSpecializes_stalkMap_apply, hb]
    · exact (algebraMap_stalk_genericPoint T _).symm.trans
        ((algebraMap_stalkSpecializes' T h' a).trans ha)
    · exact h'
  have hres := IsPoincareResidue.algebraMap_smul hρσ b₁
  rw [hb₁, hg] at hres
  set f := algebraMap _ X.functionField b₁ with hfdef
  have hf : ∀ E : Mori.PrimeDivisor X, j Q.genericPoint ∈ E.support →
      0 ≤ X.ord f E.genericPoint := by
    intro E hE
    have hEx : E.genericPoint ⤳ j Q.genericPoint := by
      rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    rw [hfdef, hb₁def, algebraMap_stalkSpecializes', ← algebraMap_stalkSpecializes' X hEx]
    exact ord_algebraMap_nonneg E _
  have hxP : j Q.genericPoint ∈ P.support := by
    have : j Q.genericPoint ∈ Set.range j.base := ⟨_, rfl⟩
    rw [hP] at this
    exact this
  refine ⟨f • σ, ?_, fun E hE hEP => ?_, hres⟩
  · by_cases hf0 : f = 0
    · rw [hf0, zero_smul, PrimeDivisor.ordForm_zero]; omega
    rw [P.ordForm_smul (sX := sX) hd hf0 hσ0, hσP]
    have := hf P hxP
    omega
  · by_cases hf0 : f = 0
    · rw [hf0, zero_smul, PrimeDivisor.ordForm_zero]
    rw [E.ordForm_smul (sX := sX) hd hf0 hσ0]
    have := hf E hE
    have := hσE E hE hEP
    omega

/-- **Residues lift at a codimension-one point of a normal prime divisor.** Let `X` be a normal
complex variety of dimension `n + 1`, `j : T ⟶ X` the inclusion of a normal prime divisor `P` and
`Q` a prime divisor of `T`. Every rational top form `ρ` on `T` without pole at `Q` is the Poincaré
residue (`MMP.Fourfold.IsPoincareResidue`) of a rational top form `τ` on `X` with at most a
simple pole along `P` and no pole along any other prime divisor through `j(η_Q)`, i.e. of a
section of `ω_X(P)` near `j(η_Q)`. -/
@[mmp "lem_fourfold_normal_prime_residue_lift"]
theorem exists_isPoincareResidue_of_le_ordForm
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety ℂ (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (Q : Mori.PrimeDivisor T) (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : 0 ≤ Q.ordForm ρ) :
    ∃ τ : RationalPluriForms sX (n + 1) 1, -1 ≤ P.ordForm τ ∧
      (∀ E : Mori.PrimeDivisor X, j Q.genericPoint ∈ E.support → E ≠ P → 0 ≤ E.ordForm τ) ∧
      IsPoincareResidue sX j n 1 τ ρ :=
  exists_isPoincareResidue_of_le_ordForm_of_charZero sX hX hdim j hT P hP Q ρ hρ

/-- **A form with a simple pole along a normal prime divisor and a nonzero residue**, over `ℂ`.
Let `X` be a normal complex variety of dimension `n + 1`, `j : T ⟶ X` the inclusion of a normal
prime divisor `P` and `Q` a prime divisor of `T`. There is a rational top form `σ ≠ 0` on `X` with
`ord_P σ = -1` and a nonzero Poincaré residue along `T`. This is the input of the adjunction
results along a normal prime divisor; see `exists_form_of_residue_order` for the general field
of characteristic zero and the orders at `Q` and along the other prime divisors. -/
theorem exists_ordForm_eq_neg_one_isPoincareResidue
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety ℂ (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (Q : Mori.PrimeDivisor T) :
    ∃ σ : RationalPluriForms sX (n + 1) 1, σ ≠ 0 ∧ P.ordForm σ = -1 ∧
      ∃ ρσ : RationalPluriForms (j ≫ sX) n 1, IsPoincareResidue sX j n 1 σ ρσ ∧ ρσ ≠ 0 := by
  obtain ⟨σ, hσ0, hσP, -, ρσ, hρσ, hρσ0, -⟩ := exists_form_of_residue_order sX hX hdim j hT P hP Q
  exact ⟨σ, hσ0, hσP, ρσ, hρσ, hρσ0⟩

end MMP.Fourfold
