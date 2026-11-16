module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# The Koszul complex of two elements

For elements `a b` of a commutative ring `R` and an `R`-module `M`, the Koszul complex is
`M → M × M → M`, `x ↦ (-b x, a x)`, `(x, y) ↦ a x + b y`.  If `(a, b)` is `M`-regular it is exact
at the two left places and `H₀ = M / (a, b) M`; if `a` or `b` is a unit it is exact everywhere.

## Main definitions

* `MMP.Chow.koszulTwoD₂`, `MMP.Chow.koszulTwoD₁`: the two differentials.

## Main results

* `MMP.Chow.koszulTwoD₁_comp_koszulTwoD₂`: the composite vanishes.
* `MMP.Chow.koszulTwoD₂_injective`, `MMP.Chow.ker_koszulTwoD₁_eq_range`,
  `MMP.Chow.range_koszulTwoD₁`: exactness for a weakly regular pair.
* `MMP.Chow.koszulTwo_exact_of_isUnit`: exactness everywhere if a coefficient is a unit.
* `MMP.Chow.isWeaklyRegular_universalPair`: for an `R`-module `M` and `x : Fin N → R`, the two
  equations `u₀ + ∑ xᵢ uᵢ₊₁` and `v₀ + ∑ xᵢ vᵢ₊₁` in independent variable blocks form a weakly
  regular sequence on `R[u, v] ⊗ M`: each is monic in a coefficient of its own block.
* `MMP.Chow.isWeaklyRegular_X_add_X_add`: the general form for `X a + p`, `X b + q` with `p`, `q`
  not involving `X a`, `X b`.

## Implementation notes

Regularity is Mathlib's `RingTheory.Sequence.IsWeaklyRegular`.  For variables the proof computes in
the description of `R[σ] ⊗ M` as finitely supported `M`-valued functions on monomials, in which a
variable acts by an injective shift; triangular substitutions reduce `X a + p` to a variable.
-/

@[expose] public section

namespace MMP.Chow

section Koszul

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The first differential `x ↦ (-b x, a x)` of the Koszul complex of `a, b` on `M`. -/
def koszulTwoD₂ (a b : R) (M : Type*) [AddCommGroup M] [Module R M] : M →ₗ[R] M × M :=
  LinearMap.prod ((-b) • LinearMap.id) (a • LinearMap.id)

/-- The second differential `(x, y) ↦ a x + b y` of the Koszul complex of `a, b` on `M`. -/
def koszulTwoD₁ (a b : R) (M : Type*) [AddCommGroup M] [Module R M] : M × M →ₗ[R] M :=
  a • LinearMap.fst R M M + b • LinearMap.snd R M M

/-- `koszulTwoD₂ a b M` sends `x` to `(-(b • x), a • x)`. -/
@[simp] lemma koszulTwoD₂_apply (a b : R) (x : M) : koszulTwoD₂ a b M x = (-(b • x), a • x) := by
  simp [koszulTwoD₂]

/-- `koszulTwoD₁ a b M` sends `p` to `a • p.1 + b • p.2`. -/
@[simp] lemma koszulTwoD₁_apply (a b : R) (p : M × M) :
    koszulTwoD₁ a b M p = a • p.1 + b • p.2 := by
  simp [koszulTwoD₁]

/-- The composite of the two differentials of the Koszul complex of `a, b` is zero. -/
lemma koszulTwoD₁_comp_koszulTwoD₂ (a b : R) :
    (koszulTwoD₁ a b M).comp (koszulTwoD₂ a b M) = 0 := by
  ext x
  simp [smul_comm a b x]

/-- The range of `koszulTwoD₂ a b M` lies in the kernel of `koszulTwoD₁ a b M`. -/
lemma range_koszulTwoD₂_le_ker (a b : R) :
    LinearMap.range (koszulTwoD₂ a b M) ≤ LinearMap.ker (koszulTwoD₁ a b M) :=
  LinearMap.range_le_ker_iff.2 (koszulTwoD₁_comp_koszulTwoD₂ a b)

/-- If `a` is `M`-regular, the first differential `koszulTwoD₂ a b M` is injective. -/
lemma koszulTwoD₂_injective {a b : R} (ha : IsSMulRegular M a) :
    Function.Injective (koszulTwoD₂ a b M) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  simp only [koszulTwoD₂_apply, Prod.mk_eq_zero] at hx
  exact ha (by simpa using hx.2)

/-- For an `M`-weakly regular pair `(a, b)` the Koszul complex is exact in the middle. -/
lemma ker_koszulTwoD₁_eq_range {a b : R} (h : RingTheory.Sequence.IsWeaklyRegular M [a, b]) :
    LinearMap.ker (koszulTwoD₁ a b M) = LinearMap.range (koszulTwoD₂ a b M) := by
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_cons_iff] at h
  obtain ⟨ha, hb, -⟩ := h
  refine le_antisymm ?_ (range_koszulTwoD₂_le_ker a b)
  rintro ⟨x, y⟩ hxy
  simp only [LinearMap.mem_ker, koszulTwoD₁_apply] at hxy
  have hy : (Submodule.Quotient.mk y : QuotSMulTop a M) = 0 := by
    apply hb
    change b • (Submodule.Quotient.mk y : QuotSMulTop a M) = b • 0
    rw [← Submodule.Quotient.mk_smul, smul_zero, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨-x, Submodule.mem_top, by rw [smul_neg, neg_eq_of_add_eq_zero_right hxy]⟩
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at hy
  obtain ⟨z, -, rfl⟩ := hy
  have : a • (x + b • z) = a • 0 := by rwa [smul_add, smul_comm a b z, smul_zero]
  exact ⟨z, by simp [eq_neg_of_add_eq_zero_left (ha this)]⟩

/-- The range of the second differential `koszulTwoD₁ a b M` is `(a, b) M`. -/
lemma range_koszulTwoD₁ (a b : R) :
    LinearMap.range (koszulTwoD₁ a b M) = Ideal.span {a, b} • (⊤ : Submodule R M) := by
  rw [Ideal.span_insert, Submodule.sup_smul, Submodule.ideal_span_singleton_smul,
    Submodule.ideal_span_singleton_smul]
  ext x
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨⟨y, z⟩, rfl⟩
    exact ⟨a • y, Submodule.smul_mem_pointwise_smul _ _ _ trivial,
      b • z, Submodule.smul_mem_pointwise_smul _ _ _ trivial, rfl⟩
  · rintro ⟨_, hy, _, hz, rfl⟩
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
    exact ⟨(y, z), by simp⟩

/-- If `a` or `b` is a unit, the Koszul complex of `a, b` is exact everywhere. -/
lemma koszulTwo_exact_of_isUnit {a b : R} (h : IsUnit a ∨ IsUnit b) :
    Function.Injective (koszulTwoD₂ a b M) ∧
      LinearMap.ker (koszulTwoD₁ a b M) = LinearMap.range (koszulTwoD₂ a b M) ∧
      Function.Surjective (koszulTwoD₁ a b M) := by
  have hcomp := range_koszulTwoD₂_le_ker (M := M) a b
  rcases h with ha | hb
  · obtain ⟨c, hc⟩ := ha.exists_left_inv
    have hac : ∀ y : M, a • c • y = y := fun y => by rw [smul_smul, mul_comm, hc, one_smul]
    have hca : ∀ y : M, c • a • y = y := fun y => by rw [smul_smul, hc, one_smul]
    refine ⟨koszulTwoD₂_injective (ha.isSMulRegular M), le_antisymm ?_ hcomp,
      fun x => ⟨(c • x, 0), by simp [hac]⟩⟩
    rintro ⟨x, y⟩ hxy
    simp only [LinearMap.mem_ker, koszulTwoD₁_apply] at hxy
    refine ⟨c • y, ?_⟩
    have hx : x = -(b • c • y) := by
      have : a • x = -(b • y) := eq_neg_of_add_eq_zero_left hxy
      calc x = c • a • x := (hca x).symm
        _ = -(b • c • y) := by rw [this, smul_neg, smul_comm c b y]
    simp only [koszulTwoD₂_apply, Prod.mk.injEq]
    exact ⟨by rw [hx], hac y⟩
  · obtain ⟨c, hc⟩ := hb.exists_left_inv
    have hbc : ∀ y : M, b • c • y = y := fun y => by rw [smul_smul, mul_comm, hc, one_smul]
    have hcb : ∀ y : M, c • b • y = y := fun y => by rw [smul_smul, hc, one_smul]
    refine ⟨?_, le_antisymm ?_ hcomp, fun x => ⟨(0, c • x), by simp [hbc]⟩⟩
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      simp only [koszulTwoD₂_apply, Prod.mk_eq_zero, neg_eq_zero] at hx
      rw [← hcb x, hx.1, smul_zero]
    · rintro ⟨x, y⟩ hxy
      simp only [LinearMap.mem_ker, koszulTwoD₁_apply] at hxy
      refine ⟨-(c • x), ?_⟩
      have hy : y = a • (-(c • x)) := by
        have : b • y = -(a • x) := eq_neg_of_add_eq_zero_right hxy
        calc y = c • b • y := (hcb y).symm
          _ = a • (-(c • x)) := by rw [this, smul_neg, smul_neg, smul_comm c a x]
      simp [hy, hbc]

end Koszul

section UniversalEquations

open MvPolynomial TensorProduct
open scoped Pointwise

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {σ : Type*}

open scoped Classical in
/-- The coefficient description `MvPolynomial σ R ⊗ M ≃ (monomials →₀ M)` of polynomials with
coefficients in `M`. -/
noncomputable def polyTensorEquiv : MvPolynomial σ R ⊗[R] M ≃ₗ[R] ((σ →₀ ℕ) →₀ M) :=
  (TensorProduct.congr (MvPolynomial.basisMonomials σ R).repr (LinearEquiv.refl R M)).trans
    (TensorProduct.finsuppScalarLeft R M (σ →₀ ℕ))

/-- `polyTensorEquiv` sends `monomial u r ⊗ₜ m` to the single function `u ↦ r • m`. -/
lemma polyTensorEquiv_monomial_tmul (u : σ →₀ ℕ) (r : R) (m : M) :
    polyTensorEquiv (monomial u r ⊗ₜ[R] m) = Finsupp.single u (r • m) := by
  have h : (monomial u r : MvPolynomial σ R) = r • MvPolynomial.basisMonomials σ R u := by
    simp [MvPolynomial.coe_basisMonomials, smul_monomial]
  have h1 :
      polyTensorEquiv ((MvPolynomial.basisMonomials σ R u) ⊗ₜ[R] m) = Finsupp.single u m := by
    simp only [polyTensorEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
      Module.Basis.repr_self, LinearEquiv.refl_apply, TensorProduct.finsuppScalarLeft_apply_tmul]
    rw [Finsupp.sum_single_index (by simp), one_smul]
  rw [h, ← TensorProduct.smul_tmul', map_smul, h1, Finsupp.smul_single]

/-- Under `polyTensorEquiv`, multiplication by `X a` is the shift of monomials by
`Finsupp.single a 1`. -/
lemma polyTensorEquiv_X_smul (a : σ) (z : MvPolynomial σ R ⊗[R] M) :
    polyTensorEquiv ((X a : MvPolynomial σ R) • z) =
      Finsupp.mapDomain (· + Finsupp.single a 1) (polyTensorEquiv z) := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro p m
    induction p using MvPolynomial.induction_on' with
    | monomial u r =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, X, monomial_mul_monomial,
        polyTensorEquiv_monomial_tmul, polyTensorEquiv_monomial_tmul, Finsupp.mapDomain_single,
        one_mul, add_comm]
    | add p q hp hq =>
      simp only [TensorProduct.add_tmul, smul_add, map_add, hp, hq, Finsupp.mapDomain_add]
  · intro x y hx hy
    simp [smul_add, hx, hy, Finsupp.mapDomain_add]

/-- A variable `X a` is a nonzerodivisor on `MvPolynomial σ R ⊗[R] M`. -/
lemma isSMulRegular_X (a : σ) :
    IsSMulRegular (MvPolynomial σ R ⊗[R] M) (X a : MvPolynomial σ R) := by
  intro z w h
  apply polyTensorEquiv.injective
  apply Finsupp.mapDomain_injective (add_left_injective (Finsupp.single a 1))
  simpa only [← polyTensorEquiv_X_smul] using congrArg polyTensorEquiv h

/-- For distinct variables `a ≠ b`, if `X b • z` lies in `X a • ⊤` then so does `z`. -/
lemma mem_X_smul_top_of_X_smul {a b : σ} (hab : a ≠ b) {z : MvPolynomial σ R ⊗[R] M}
    (hz : (X b : MvPolynomial σ R) • z ∈
      (X a : MvPolynomial σ R) • (⊤ : Submodule (MvPolynomial σ R) (MvPolynomial σ R ⊗[R] M))) :
    z ∈ (X a : MvPolynomial σ R) •
      (⊤ : Submodule (MvPolynomial σ R) (MvPolynomial σ R ⊗[R] M)) := by
  classical
  obtain ⟨n, -, hn⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
  have h1 : Finsupp.mapDomain (· + Finsupp.single a 1) (polyTensorEquiv n) =
      Finsupp.mapDomain (· + Finsupp.single b 1) (polyTensorEquiv z) := by
    rw [← polyTensorEquiv_X_smul, ← polyTensorEquiv_X_smul, hn]
  have hsupp : ↑(polyTensorEquiv z).support ⊆ Set.range (· + Finsupp.single a 1) := by
    intro k hk
    have hk' : k + Finsupp.single b 1 ∈
        (Finsupp.mapDomain (· + Finsupp.single b 1) (polyTensorEquiv z)).support := by
      rw [Finsupp.mapDomain_support_of_injective (add_left_injective (Finsupp.single b 1))]
      exact Finset.mem_image_of_mem _ hk
    rw [← h1, Finsupp.mapDomain_support_of_injective (add_left_injective (Finsupp.single a 1))]
      at hk'
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hk'
    have hja := congrArg (fun f => f a) hj
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hab] at hja
    have hle : Finsupp.single a 1 ≤ k := by
      rw [Finsupp.single_le_iff]
      omega
    exact ⟨k - Finsupp.single a 1, tsub_add_cancel_of_le hle⟩
  have hinj := add_left_injective (Finsupp.single a 1)
  have h2 := Finsupp.mapDomain_comapDomain _ hinj (polyTensorEquiv z) hsupp
  refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨polyTensorEquiv.symm
    (Finsupp.comapDomain _ (polyTensorEquiv z) hinj.injOn), Submodule.mem_top, ?_⟩
  apply polyTensorEquiv.injective
  rw [polyTensorEquiv_X_smul, LinearEquiv.apply_symm_apply, h2]

/-- Two distinct variables `X a, X b` form a weakly regular sequence on
`MvPolynomial σ R ⊗[R] M`. -/
lemma isWeaklyRegular_X_X {a b : σ} (hab : a ≠ b) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ R ⊗[R] M)
      [(X a : MvPolynomial σ R), X b] := by
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff]
  refine ⟨isSMulRegular_X a, ?_⟩
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff]
  refine ⟨?_, ?_⟩
  · intro x y h
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    simp only at h
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at h
    exact (Submodule.Quotient.eq _).2 (mem_X_smul_top_of_X_smul hab (by rwa [smul_sub]))
  · exact RingTheory.Sequence.IsWeaklyRegular.nil _ _

section Subst

variable [DecidableEq σ] (a b : σ) (p q : MvPolynomial σ R)

/-- The substitution `X a ↦ sa`, `X b ↦ sb` (for `a ≠ b`), fixing all other variables. -/
noncomputable def substPair (sa sb : MvPolynomial σ R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun v => if v = a then sa else if v = b then sb else X v

/-- `substPair a b sa sb` sends `X a` to `sa`. -/
@[simp] lemma substPair_X_a (sa sb : MvPolynomial σ R) : substPair a b sa sb (X a) = sa := by
  simp [substPair]

/-- For `a ≠ b`, `substPair a b sa sb` sends `X b` to `sb`. -/
lemma substPair_X_b (hab : a ≠ b) (sa sb : MvPolynomial σ R) :
    substPair a b sa sb (X b) = sb := by
  simp [substPair, hab.symm]

/-- `substPair a b sa sb` fixes every variable `X v` with `v ≠ a` and `v ≠ b`. -/
lemma substPair_X_of_ne {v : σ} (h1 : v ≠ a) (h2 : v ≠ b) (sa sb : MvPolynomial σ R) :
    substPair a b sa sb (X v) = X v := by
  simp [substPair, h1, h2]

/-- For `a ≠ b`, the triangular substitution `X a ↦ X a + p`, `X b ↦ X b + q` is an algebra
automorphism, with inverse `X a ↦ X a - p`, `X b ↦ X b - q`. -/
noncomputable def substEquiv (hab : a ≠ b)
    (hp : ∀ θ : σ → MvPolynomial σ R, (∀ v, v ≠ a → v ≠ b → θ v = X v) → aeval θ p = p)
    (hq : ∀ θ : σ → MvPolynomial σ R, (∀ v, v ≠ a → v ≠ b → θ v = X v) → aeval θ q = q) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (substPair a b (X a + p) (X b + q)) (substPair a b (X a - p) (X b - q))
    (by
      refine MvPolynomial.algHom_ext fun v => ?_
      by_cases h1 : v = a
      · subst h1
        simp only [AlgHom.comp_apply, AlgHom.id_apply, substPair_X_a]
        rw [map_sub]
        have : substPair v b (X v + p) (X b + q) p = p := hp _ fun w hw1 hw2 => by
          simp [hw1, hw2]
        rw [substPair_X_a, this]
        ring
      by_cases h2 : v = b
      · subst h2
        simp only [AlgHom.comp_apply, AlgHom.id_apply]
        rw [substPair_X_b a v hab, map_sub, substPair_X_b a v hab]
        have : substPair a v (X a + p) (X v + q) q = q := hq _ fun w hw1 hw2 => by
          simp [hw1, hw2]
        rw [this]
        ring
      · simp [substPair_X_of_ne a b h1 h2])
    (by
      refine MvPolynomial.algHom_ext fun v => ?_
      by_cases h1 : v = a
      · subst h1
        simp only [AlgHom.comp_apply, AlgHom.id_apply, substPair_X_a]
        rw [map_add]
        have : substPair v b (X v - p) (X b - q) p = p := hp _ fun w hw1 hw2 => by
          simp [hw1, hw2]
        rw [substPair_X_a, this]
        ring
      by_cases h2 : v = b
      · subst h2
        simp only [AlgHom.comp_apply, AlgHom.id_apply]
        rw [substPair_X_b a v hab, map_add, substPair_X_b a v hab]
        have : substPair a v (X a - p) (X v - q) q = q := hq _ fun w hw1 hw2 => by
          simp [hw1, hw2]
        rw [this]
        ring
      · simp [substPair_X_of_ne a b h1 h2])

end Subst

/-- For distinct variables `a ≠ b` and polynomials `p`, `q` fixed by every substitution that
fixes all variables other than `X a`, `X b`, the pair `X a + p, X b + q` is weakly regular on
`MvPolynomial σ R ⊗[R] M`. -/
lemma isWeaklyRegular_X_add_X_add {a b : σ} (hab : a ≠ b) (p q : MvPolynomial σ R)
    (hp : ∀ θ : σ → MvPolynomial σ R, (∀ v, v ≠ a → v ≠ b → θ v = X v) → aeval θ p = p)
    (hq : ∀ θ : σ → MvPolynomial σ R, (∀ v, v ≠ a → v ≠ b → θ v = X v) → aeval θ q = q) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ R ⊗[R] M)
      [(X a + p : MvPolynomial σ R), X b + q] := by
  classical
  set φ := substEquiv a b p q hab hp hq
  let Ψ : (MvPolynomial σ R ⊗[R] M) ≃+ (MvPolynomial σ R ⊗[R] M) :=
    (TensorProduct.congr φ.toLinearEquiv (LinearEquiv.refl R M)).toAddEquiv
  have hΨ : ∀ (t : MvPolynomial σ R) (z : MvPolynomial σ R ⊗[R] M), Ψ (t • z) = φ t • Ψ z := by
    intro t z
    refine TensorProduct.inductionOn z ?_ ?_
    · intro r m
      simp [Ψ, TensorProduct.smul_tmul', smul_eq_mul]
    · intro x y hx hy
      simp [smul_add, hx, hy]
  have hφa : φ (X a) = X a + p := substPair_X_a a b _ _
  have hφb : φ (X b) = X b + q := substPair_X_b a b hab _ _
  refine (AddEquiv.isWeaklyRegular_congr (e := Ψ) (as := [X a, X b])
    (bs := [(X a + p : MvPolynomial σ R), X b + q]) ?_).1 (isWeaklyRegular_X_X hab)
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
  · exact fun x => by rw [hΨ, hφa]
  · exact fun x => by rw [hΨ, hφb]

/-- **The universal pair of equations is a regular sequence.**  Let `M` be an `R`-module,
`x : Fin N → R`, and give `R[u₀, …, u_N, v₀, …, v_N]` the two independent blocks of variables
`inl` (the `u`) and `inr` (the `v`).  Then `f = u₀ + ∑ xᵢ uᵢ₊₁` is a nonzerodivisor on
`R[u, v] ⊗ M`, and `g = v₀ + ∑ xᵢ vᵢ₊₁` is a nonzerodivisor on the quotient by `f`: each of the two
equations is monic in its own coefficient (`u₀`, resp. `v₀`).  In other words `(f, g)` is
`R[u, v] ⊗ M`-weakly regular. -/
theorem isWeaklyRegular_universalPair (M : Type*) [AddCommGroup M] [Module R M] (N : ℕ)
    (x : Fin N → R) :
    RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) R ⊗[R] M)
      [X (Sum.inl 0) + ∑ i : Fin N, C (x i) * X (Sum.inl i.succ),
        X (Sum.inr 0) + ∑ i : Fin N, C (x i) * X (Sum.inr i.succ)] := by
  refine isWeaklyRegular_X_add_X_add (a := Sum.inl 0) (b := Sum.inr 0) (by simp) _ _ ?_ ?_
  · intro θ hθ
    simp only [map_sum, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hθ _ (by simp [Fin.succ_ne_zero]) (by simp), ← C_eq_smul_one]
  · intro θ hθ
    simp only [map_sum, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hθ _ (by simp) (by simp [Fin.succ_ne_zero]), ← C_eq_smul_one]

end UniversalEquations

end MMP.Chow
