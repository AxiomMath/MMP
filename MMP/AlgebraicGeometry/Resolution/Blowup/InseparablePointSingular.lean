module
public import MMP.AlgebraicGeometry.Resolution.Blowup.Charts
public import MMP.AlgebraicGeometry.Analytic.ComplexRealizationHausdorff
public import StacksFrontier.RingTheory.NodalChart.Regularity

/-!
# The blow-up of an inseparable point is geometrically singular

Let `K` be a field of characteristic `p > 0` and `v ∈ K` an element which is not a `p`-th power,
for instance `K = k(u, v)`. The ideal `(x, yᵖ - v)` of `K[x, y]` is maximal, so it defines a
closed point `P` of `𝔸²_K`, and the blow-up `B_P𝔸²_K` is a regular surface. It is nevertheless
not smooth over `K`: after base change to any extension `L` of `K` containing a `p`-th root
`c` of `v`, for instance `L = K̄`, the chart `t ≠ 0` of the blow-up becomes
`Spec L[x, y₁, σ]/(xσ - y₁ᵖ)` with `y₁ = y - c`, which is singular at the origin.

## Main results

* `MMP.Resolution.exists_not_isRegularLocalRing_of_isPullback_blowUp`: a fibre product
  `B_P𝔸²_K ×_K L` has a point whose local ring is not regular.

## Implementation notes

The point `P` is given by its closed set `V(x, yᵖ - v) = {P}` in `Spec K[x, y]`, and `B_P𝔸²_K`
is `AlgebraicGeometry.blowUp` of the reduced ideal sheaf of that closed set; this is the
blow-up of the reduced point `P`. The statement is proved over any field `K` of characteristic
`p` and any `v ∈ K` which is not a `p`-th power, and for any extension `L` of `K` in which `v`
is a `p`-th power, not only for `K = k(u, v)` and `L = K̄`. The fibre product is any scheme
`Y` with a pullback square (`CategoryTheory.IsPullback`), not a chosen `Limits.pullback`. A
scheme is regular when all its local rings are, so "not regular" is the existence of a point
with non-regular local ring.

## References

* [Kollár, *Lectures on resolution of singularities*, 1.49][kollar2007]
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace MMP.Resolution

/-- The coordinate ring `L[x, y₁, σ]/(xσ - y₁ᵖ)` of the chart `t ≠ 0` after base change. -/
private abbrev ChartRing (L : Type u) [Field L] (p : ℕ) : Type u :=
  MvPolynomial (Fin 3) L ⧸ Ideal.span {(X 0 * X 2 - X 1 ^ p : MvPolynomial (Fin 3) L)}

/-- The ideal `(x, y₁, σ)` of the chart ring. -/
private noncomputable abbrev originIdeal (L : Type u) [Field L] (p : ℕ) : Ideal (ChartRing L p) :=
  Ideal.map (Ideal.Quotient.mk _) (Ideal.span (Set.range X))

/-- The equation `xσ - y₁ᵖ` lies in the ideal `(x, y₁, σ)`. -/
private theorem span_equation_le (L : Type u) [Field L] (p : ℕ) [Fact p.Prime] :
    Ideal.span {(X 0 * X 2 - X 1 ^ p : MvPolynomial (Fin 3) L)} ≤
      Ideal.span (Set.range X) := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  refine Ideal.sub_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨0, rfl⟩)) ?_
  exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_range_self 1)) p
    (Fact.out : p.Prime).pos

/-- The ideal `(x, y₁, σ)` of the chart ring is prime. -/
private theorem originIdeal_isPrime (L : Type u) [Field L] (p : ℕ) [Fact p.Prime] :
    (originIdeal L p).IsPrime := by
  haveI : (Ideal.span (Set.range (X : Fin 3 → MvPolynomial (Fin 3) L))).IsPrime :=
    MMP.MvPolynomial.isPrime_span_range_X
  exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (Ideal.mk_ker.trans_le (span_equation_le L p))

open IsLocalRing in
/-- If `I ≤ 𝔪²` in a Noetherian local ring `R`, then the maximal ideal of `R ⧸ I`
needs at least as many generators as that of `R`. -/
theorem spanFinrank_maximalIdeal_le_quotient_of_le_sq {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {I : Ideal R} [IsLocalRing (R ⧸ I)] (hI : I ≤ maximalIdeal R ^ 2) :
    (maximalIdeal R).spanFinrank ≤ (maximalIdeal (R ⧸ I)).spanFinrank := by
  set Q := R ⧸ I
  set π := Ideal.Quotient.mk I
  have hIm : I ≤ maximalIdeal R := hI.trans (Ideal.pow_le_self two_ne_zero)
  have hloc : ∀ r ∈ maximalIdeal R, π r ∈ maximalIdeal Q := by
    intro r hr hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    have h1 : r * b' - 1 ∈ I := Ideal.Quotient.eq.mp (by simpa [π] using hb)
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr
      (by simpa using Ideal.sub_mem _ (Ideal.mul_mem_right b' _ hr) (hIm h1)))
  obtain ⟨T, hTc, hT⟩ :=
    Submodule.FG.exists_span_set_encard_eq_spanFinrank (maximalIdeal Q).fg_of_isNoetherianRing
  have hTf : T.Finite := Set.finite_of_encard_eq_coe hTc
  let s := Function.surjInv (Ideal.Quotient.mk_surjective (I := I))
  have hs : ∀ q, π (s q) = q := Function.surjInv_eq _
  set T' := s '' T
  have hT'sub : Ideal.span T' ≤ maximalIdeal R := by
    rw [Ideal.span_le]
    rintro _ ⟨t, ht, rfl⟩
    have : π (s t) ∈ maximalIdeal Q := by
      rw [hs]
      exact hT ▸ Submodule.subset_span ht
    exact fun hu ↦ this (hu.map π)
  have hle : maximalIdeal R ≤ Ideal.span T' ⊔ maximalIdeal R • maximalIdeal R := by
    intro r hr
    have h1 : π r ∈ Ideal.map π (Ideal.span T') := by
      rw [Ideal.map_span, Set.image_image]
      simp only [hs, Set.image_id']
      change π r ∈ Submodule.span Q T
      rw [hT]
      exact hloc r hr
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker] at h1
    exact (sup_le_sup_left (show I ≤ maximalIdeal R • maximalIdeal R by
      rwa [Ideal.smul_eq_mul, ← sq]) _) h1
  have heq : maximalIdeal R ≤ Ideal.span T' :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (maximalIdeal R).fg_of_isNoetherianRing
      (maximalIdeal_le_jacobson _) hle
  have h4 : T.ncard = (maximalIdeal Q).spanFinrank := by
    rw [Set.ncard_def, hTc, ENat.toNat_coe]
  rw [← h4, le_antisymm heq hT'sub]
  exact (Submodule.spanFinrank_span_le_ncard_of_finite (hTf.image s)).trans
    (Set.ncard_image_le hTf)

open IsLocalRing in
/-- The local ring `L[x,y₁,σ]_{(x,y₁,σ)}/(xσ - y₁ᵖ)` of the chart at the origin is not a regular
local ring. -/
private theorem not_isRegularLocalRing_localization_originIdeal (L : Type u) [Field L] (p : ℕ)
    [Fact p.Prime] [(originIdeal L p).IsPrime] :
    ¬ IsRegularLocalRing (Localization.AtPrime (originIdeal L p)) := by
  intro hA
  haveI : (Ideal.span (Set.range (X : Fin 3 → MvPolynomial (Fin 3) L))).IsPrime :=
    MMP.MvPolynomial.isPrime_span_range_X
  set 𝔫 := Ideal.span (Set.range (X : Fin 3 → MvPolynomial (Fin 3) L))
  set g : MvPolynomial (Fin 3) L := X 0 * X 2 - X 1 ^ p
  let O := Localization.AtPrime 𝔫
  obtain ⟨hreg, -, hmax⟩ :=
    MMP.MvPolynomial.isRegularLocalRing_of_isLocalization_atPrime_span_X L (Fin 3) 𝔫 rfl O
  have hX : ∀ i, algebraMap (MvPolynomial (Fin 3) L) O (X i) ∈ maximalIdeal O := fun i ↦
    hmax ▸ Ideal.subset_span ⟨i, rfl⟩
  have hg0 : algebraMap (MvPolynomial (Fin 3) L) O g ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (MvPolynomial (Fin 3) L) O),
      (IsLocalization.injective O 𝔫.primeCompl_le_nonZeroDivisors).eq_iff]
    intro h
    have := congrArg (MvPolynomial.eval ![1, 0, 1]) h
    simp [g, zero_pow (Fact.out : p.Prime).ne_zero] at this
  have hg2 : algebraMap (MvPolynomial (Fin 3) L) O g ∈ maximalIdeal O ^ 2 := by
    simp only [g, map_sub, map_mul, map_pow]
    refine Ideal.sub_mem _ (sq (maximalIdeal O) ▸ Ideal.mul_mem_mul (hX 0) (hX 2)) ?_
    exact Ideal.pow_le_pow_right (Fact.out : p.Prime).two_le (Ideal.pow_mem_pow (hX 1) p)
  have hM : Algebra.algebraMapSubmonoid (ChartRing L p) 𝔫.primeCompl =
      (originIdeal L p).primeCompl := by
    ext x
    refine ⟨?_, fun hx ↦ ?_⟩
    · rintro ⟨m, hm, rfl⟩ hx
      obtain ⟨a, ha, hax⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hx
      exact hm (by simpa using 𝔫.sub_mem ha (span_equation_le L p (Ideal.Quotient.eq.mp hax)))
    · obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨m, fun hm ↦ hx (Ideal.mem_map_of_mem _ hm), rfl⟩
  let I' := (Ideal.span {g}).map (algebraMap (MvPolynomial (Fin 3) L) O)
  haveI : IsLocalization (originIdeal L p).primeCompl (O ⧸ I') := hM ▸ inferInstance
  let e₁ := IsLocalization.algEquiv (originIdeal L p).primeCompl
    (Localization.AtPrime (originIdeal L p)) (O ⧸ I')
  let e₂ : O ⧸ I' ≃+* O ⧸ Ideal.span {algebraMap (MvPolynomial (Fin 3) L) O g} :=
    Ideal.quotEquivOfEq (by simp only [I', Ideal.map_span, Set.image_singleton])
  exact Stacks.not_isRegularLocalRing_quotient_span_singleton_of_mem_sq
    (mem_nonZeroDivisors_of_ne_zero hg0) hg2
    (IsRegularLocalRing.of_ringEquiv (e₁.toRingEquiv.trans e₂))

section

variable {K : Type u} [Field K]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The substitution `x ↦ 0` on `K[x, y]`. -/
private noncomputable abbrev killX : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
  aeval ![0, X 1]

/-- `f - f(0, y)` is divisible by `x`. -/
private theorem sub_killX_mem (f : MvPolynomial (Fin 2) K) :
    f - killX f ∈ Ideal.span {(X 0 : MvPolynomial (Fin 2) K)} := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg =>
    have := Ideal.add_mem _ hf hg
    rwa [map_add, add_sub_add_comm]
  | mul_X f i hf =>
    have : f * X i - killX (f * X i) = (f - killX f) * X i + killX f * (X i - ![0, X 1] i) := by
      simp only [map_mul, aeval_X]
      ring
    rw [this]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ ?_)
    fin_cases i
    · simpa using Ideal.subset_span rfl
    · simp

/-- If `v` is not a `p`-th power, then `(x, yᵖ - v)` is prime in `K[x, y]`. -/
private theorem isPrime_span_X_zero_X_one_pow_sub_C (p : ℕ) [hp : Fact p.Prime] (v : K)
    (hv : ¬ ∃ c : K, c ^ p = v) :
    (Ideal.span {X 0, X 1 ^ p - C v} : Ideal (MvPolynomial (Fin 2) K)).IsPrime := by
  haveI : Fact (Irreducible (Polynomial.X ^ p - Polynomial.C v)) :=
    ⟨X_pow_sub_C_irreducible_of_prime hp.out fun b hb ↦ hv ⟨b, hb⟩⟩
  set q : Polynomial K := Polynomial.X ^ p - Polynomial.C v
  let π : MvPolynomial (Fin 2) K →ₐ[K] AdjoinRoot q := aeval ![0, AdjoinRoot.root q]
  let ρ : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K := aeval ![0, Polynomial.X]
  let ι : Polynomial K →ₐ[K] MvPolynomial (Fin 2) K := Polynomial.aeval (X 1)
  have hkill : killX = ι.comp ρ := MvPolynomial.algHom_ext fun i ↦ by fin_cases i <;> simp [ι, ρ]
  have hπι : π.comp ι = AdjoinRoot.mkₐ q := Polynomial.algHom_ext (by simp [π, ι, AdjoinRoot.mk_X])
  have hπk : π.comp killX = π := MvPolynomial.algHom_ext fun i ↦ by fin_cases i <;> simp [π]
  suffices h : Ideal.span {X 0, X 1 ^ p - C v} = RingHom.ker π.toRingHom from
    h ▸ RingHom.ker_isPrime _
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    · simp [π]
    · simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        map_sub, map_pow, aeval_X, aeval_C, π]
      simpa [q, AdjoinRoot.algebraMap_eq] using AdjoinRoot.eval₂_root q
  · intro f hf
    rw [RingHom.mem_ker] at hf
    have h1 : AdjoinRoot.mk q (ρ f) = 0 := by
      have := congrArg (fun φ : _ →ₐ[K] _ ↦ φ (ρ f)) hπι
      simp only [AlgHom.comp_apply] at this
      rw [show AdjoinRoot.mk q (ρ f) = π (ι (ρ f)) from this.symm, ← AlgHom.comp_apply ι ρ,
        ← hkill, ← AlgHom.comp_apply, hπk]
      exact hf
    obtain ⟨r, hr⟩ := AdjoinRoot.mk_eq_zero.mp h1
    have h2 : killX f = (X 1 ^ p - C v) * ι r := by
      rw [hkill, AlgHom.comp_apply, hr, map_mul]
      simp [q, ι]
    simpa using Ideal.add_mem (Ideal.span {X 0, X 1 ^ p - C v})
      (Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) (sub_killX_mem f))
      (show killX f ∈ _ from h2 ▸ Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

/-- The sequence `x, yᵖ - v` of `K[x, y]` is `H₁`-regular: every relation between them is a
multiple of the Koszul relation. -/
private theorem isH1Regular_X_zero_X_one_pow_sub_C (p : ℕ) [hp : Fact p.Prime] (v : K)
    (hv0 : v ≠ 0) :
    Koszul.IsH1Regular ![(X 0 : MvPolynomial (Fin 2) K), X 1 ^ p - C v] := by
  rw [Koszul.isH1Regular_iff_forall]
  intro a ha
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at ha
  have hg : (X 1 ^ p - C v : MvPolynomial (Fin 2) K) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval 0) h
    simp [zero_pow hp.out.ne_zero, hv0] at this
  have hk : killX (a 1) = 0 := by
    have := congrArg killX ha
    simp only [map_add, map_mul, map_zero, map_sub, map_pow, aeval_X, aeval_C,
      Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_add] at this
    exact (mul_eq_zero.mp this).resolve_right (by simpa using hg)
  have h1 := sub_killX_mem (a 1)
  rw [hk, sub_zero] at h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
  have h0 : a 0 = -(c * (X 1 ^ p - C v)) := by
    apply mul_right_cancel₀ (X_ne_zero 0 : (X 0 : MvPolynomial (Fin 2) K) ≠ 0)
    rw [← hc] at ha
    linear_combination ha
  have : a = c • Koszul.trivRel ![(X 0 : MvPolynomial (Fin 2) K), X 1 ^ p - C v] 0 1 := by
    funext i
    fin_cases i <;> simp [Koszul.trivRel, h0, ← hc] <;> ring
  rw [this]
  exact Submodule.smul_mem _ _ (Koszul.trivRel_mem_relSpan _ 0 1)

/-- On the affine open `⊤` of `Spec K[x, y]`, the ideal of the reduced point `V(x, yᵖ - v)` is
`(x, yᵖ - v)`, read in `Γ(Spec K[x, y], ⊤)`, provided that ideal is prime. -/
private theorem ideal_vanishingIdeal_top (p : ℕ) (v : K)
    (hP : (Ideal.span {X 0, X 1 ^ p - C v} : Ideal (MvPolynomial (Fin 2) K)).IsPrime) :
    (Scheme.IdealSheafData.vanishingIdeal
      (X := Spec (CommRingCat.of (MvPolynomial (Fin 2) K)))
      ⟨PrimeSpectrum.zeroLocus {X 0, X 1 ^ p - C v}, PrimeSpectrum.isClosed_zeroLocus _⟩).ideal
        ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 2) K))).inv.hom (X 0),
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 2) K))).inv.hom (X 1 ^ p - C v)} := by
  set ψ :=
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 2) K))).commRingCatIsoToRingEquiv.symm
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  simp only [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  change PrimeSpectrum.vanishingIdeal (PrimeSpectrum.comap ψ.toRingHom ⁻¹'
    PrimeSpectrum.zeroLocus {X 0, X 1 ^ p - C v}) = _
  rw [PrimeSpectrum.preimage_comap_zeroLocus, ← PrimeSpectrum.zeroLocus_span,
    PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, Set.image_pair]
  have : ((Ideal.span {X 0, X 1 ^ p - C v}).map ψ).IsPrime := Ideal.map_isPrime_of_equiv ψ
  rw [Ideal.map_span, Set.image_pair] at this
  exact this.radical

/-- The change of variables `K[x, y, σ] ≃ R'[σ]` sending `x, y` to `ψ(x), ψ(y)` and `σ` to `σ`,
for a ring isomorphism `ψ : K[x, y] ≃ R'`. -/
private theorem exists_ringEquiv_mvPolynomial_fin_three {R' : Type u} [CommRing R']
    (ψ : MvPolynomial (Fin 2) K ≃+* R') :
    ∃ θ : MvPolynomial (Fin 3) K ≃+* MvPolynomial (Fin 1) R',
      θ (X 0) = C (ψ (X 0)) ∧ θ (X 1) = C (ψ (X 1)) ∧ θ (X 2) = X 0 ∧
        ∀ k, θ (C k) = C (ψ (C k)) := by
  let θf : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 1) R' :=
    eval₂Hom ((C : R' →+* _).comp (ψ.toRingHom.comp C)) ![C (ψ (X 0)), C (ψ (X 1)), X 0]
  let θ₀ : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 3) K := eval₂Hom C ![X 0, X 1]
  let θi : MvPolynomial (Fin 1) R' →+* MvPolynomial (Fin 3) K :=
    eval₂Hom (θ₀.comp ψ.symm.toRingHom) fun _ ↦ X 2
  have hθ₀ : θf.comp θ₀ = (C : R' →+* _).comp ψ.toRingHom :=
    MvPolynomial.ringHom_ext (fun k ↦ by simp [θf, θ₀]) fun i ↦ by fin_cases i <;> simp [θf, θ₀]
  have h1 : θi.comp θf = RingHom.id _ :=
    MvPolynomial.ringHom_ext (fun k ↦ by simp [θf, θi, θ₀])
      fun i ↦ by fin_cases i <;> simp [θf, θi, θ₀]
  have h2 : θf.comp θi = RingHom.id _ :=
    MvPolynomial.ringHom_ext (fun r ↦ by simpa [θi] using RingHom.congr_fun hθ₀ (ψ.symm r))
      fun i ↦ by fin_cases i; simp [θf, θi]
  exact ⟨RingEquiv.ofRingHom θf θi h2 h1, by simp [θf], by simp [θf], by simp [θf],
    fun k ↦ by simp [θf]⟩

/-- If `ψ(x), ψ(yᵖ - v)` is `H₁`-regular and generates `J`, the affine blow-up algebra
`R'[J/ψ(x)]` is `K[x, y, σ]/(xσ - (yᵖ - v))`, compatibly with the maps from `K`. -/
private theorem exists_ringEquiv_affineBlowupAlgebra {R' : Type u} [CommRing R']
    (ψ : MvPolynomial (Fin 2) K ≃+* R') (p : ℕ) (v : K)
    (hreg : Koszul.IsH1Regular ![ψ (X 0), ψ (X 1 ^ p - C v)]) (J : Ideal R')
    (hJ : J = Ideal.span {ψ (X 0), ψ (X 1 ^ p - C v)}) :
    ∃ e : (MvPolynomial (Fin 3) K ⧸ Ideal.span {(X 0 * X 2 - (X 1 ^ p - C v) :
        MvPolynomial (Fin 3) K)}) ≃+* affineBlowupAlgebra J (ψ (X 0)) (Localization.Away (ψ (X 0))),
      ∀ k : K, e (algebraMap K _ k) = algebraMap R' _ (ψ (C k)) := by
  set a := ψ (X 0)
  set b := ψ (X 1 ^ p - C v)
  set B := affineBlowupAlgebra J a (Localization.Away a)
  have hreg' : Koszul.IsH1Regular
      (Fin.cases a (fun j ↦ ![b] (Equiv.refl (Fin 1) j)) : Fin 2 → R') := by
    convert hreg using 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨hsurj, hker⟩ := MMP.Flips.ResolutionInputs.aeval_mk'_range_and_ker_of_isH1Regular
    (Equiv.refl (Fin 1)) a ![b] hreg'
  have hJ' : Ideal.span (insert a (Set.range ![b])) = J := by
    rw [hJ]
    simp [Set.pair_comm]
  rw [hJ'] at hsurj
  set Φ : MvPolynomial (Fin 1) R' →ₐ[R'] Localization.Away a := MvPolynomial.aeval fun i ↦
    IsLocalization.mk' (Localization.Away a) (![b] i) (⟨a, Submonoid.mem_powers a⟩ :
      Submonoid.powers a)
  have hrange : ∀ q, Φ q ∈ B := by
    intro q
    have : Φ q ∈ Φ.range := ⟨q, rfl⟩
    rw [MvPolynomial.aeval_range] at this
    refine Algebra.adjoin_mono ?_ this
    rintro _ ⟨i, rfl⟩
    refine ⟨![b] i, ?_, rfl⟩
    fin_cases i
    exact hJ ▸ Ideal.subset_span (by simp [b])
  let Φ' : MvPolynomial (Fin 1) R' →ₐ[R'] B := Φ.codRestrict B hrange
  have hΦ'surj : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    obtain ⟨q, hq⟩ := hsurj y hy
    exact ⟨q, Subtype.ext hq⟩
  have hΦ'ker : RingHom.ker Φ' = RingHom.ker Φ := by
    ext q
    simp [Φ', RingHom.mem_ker, Subtype.ext_iff]
  let e₁ := (Ideal.quotientEquivAlgOfEq R' (hker.symm.trans hΦ'ker.symm)).trans
    (Ideal.quotientKerAlgEquivOfSurjective hΦ'surj)
  obtain ⟨θ, hθ0, hθ1, hθ2, hθC⟩ := exists_ringEquiv_mvPolynomial_fin_three ψ
  have hθ : Ideal.span (Set.range fun i : Fin 1 ↦ C (![b] i) - X i * C a) =
      (Ideal.span {(X 0 * X 2 - (X 1 ^ p - C v) : MvPolynomial (Fin 3) K)}).map θ := by
    rw [Ideal.map_span, Set.image_singleton, Set.range_unique, ← Ideal.span_singleton_neg]
    congr 2
    simp [hθ0, hθ1, hθ2, hθC, a, b, map_sub, map_pow]
    ring
  let e₂ := Ideal.quotientEquiv _ _ θ hθ
  refine ⟨e₂.trans e₁.toRingEquiv, fun k ↦ ?_⟩
  apply Subtype.ext
  change Φ (θ (C k)) = algebraMap R' (Localization.Away a) (ψ (C k))
  simp [Φ, hθC]

/-- Base change of the chart: `K[x, y, σ]/(xσ - (yᵖ - v)) ⊗_K L ≃ L[x, y₁, σ]/(xσ - y₁ᵖ)`, by
`y₁ = y - c` where `cᵖ = v`. -/
private theorem exists_ringEquiv_tensor_chartRing (p : ℕ) [Fact p.Prime] (v : K)
    (L : Type u) [Field L] [Algebra K L] [CharP L p] (c : L) (hc : c ^ p = algebraMap K L v) :
    Nonempty (TensorProduct K (MvPolynomial (Fin 3) K ⧸ Ideal.span {(X 0 * X 2 - (X 1 ^ p - C v) :
        MvPolynomial (Fin 3) K)}) L ≃+*
      ChartRing L p) := by
  set F : MvPolynomial (Fin 3) K := X 0 * X 2 - (X 1 ^ p - C v)
  set FL : MvPolynomial (Fin 3) L := X 0 * X 2 - (X 1 ^ p - C (algebraMap K L v))
  let e₁ := Algebra.TensorProduct.quotientTensorEquiv (R := K) K L (MvPolynomial (Fin 3) K)
    (Ideal.span {F})
  let eP := Algebra.IsPushout.equiv K (MvPolynomial (Fin 3) K) L (MvPolynomial (Fin 3) L)
  have hP : ((Ideal.span {F}).map (algebraMap (MvPolynomial (Fin 3) K)
      (TensorProduct K (MvPolynomial (Fin 3) K) L))).map eP = Ideal.span {FL} := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    congr 2
    rw [AlgEquiv.commutes, MvPolynomial.algebraMap_def]
    simp [F, FL]
  let e₂ := Ideal.quotientEquiv _ _ eP.toRingEquiv hP.symm
  -- the change of coordinates `y₁ = y - c`
  let s : MvPolynomial (Fin 3) L →ₐ[L] MvPolynomial (Fin 3) L := aeval ![X 0, X 1 - C c, X 2]
  let s' : MvPolynomial (Fin 3) L →ₐ[L] MvPolynomial (Fin 3) L := aeval ![X 0, X 1 + C c, X 2]
  have hs : s.comp s' = AlgHom.id _ _ :=
    MvPolynomial.algHom_ext fun i ↦ by fin_cases i <;> simp [s, s']
  have hs' : s'.comp s = AlgHom.id _ _ :=
    MvPolynomial.algHom_ext fun i ↦ by fin_cases i <;> simp [s, s']
  let σ : MvPolynomial (Fin 3) L ≃ₐ[L] MvPolynomial (Fin 3) L := AlgEquiv.ofAlgHom s s' hs hs'
  have hσ : Ideal.span {FL} =
      (Ideal.span {(X 0 * X 2 - X 1 ^ p : MvPolynomial (Fin 3) L)}).map σ := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    simp [σ, s, FL, sub_pow_char, ← hc]
  exact ⟨(e₁.toRingEquiv.trans e₂).trans (Ideal.quotientEquiv _ _ σ.toRingEquiv hσ).symm⟩

end

/-- The standard chart of the blow-up at the section `x`: `Spec K[x, y, σ]/(xσ - (yᵖ - v))` is
an open subscheme of `B_P𝔸²_K`, compatibly with the maps to `Spec K`. -/
private theorem exists_isOpenImmersion_spec_quotient_blowUp
    {K : Type u} [Field K] (p : ℕ) [Fact p.Prime] (v : K) (hv : ¬ ∃ c : K, c ^ p = v) :
    ∃ j : Spec (CommRingCat.of (MvPolynomial (Fin 3) K ⧸
        Ideal.span {(X 0 * X 2 - (X 1 ^ p - C v) : MvPolynomial (Fin 3) K)})) ⟶
      blowUp (Scheme.IdealSheafData.vanishingIdeal
        (X := Spec (CommRingCat.of (MvPolynomial (Fin 2) K)))
        ⟨PrimeSpectrum.zeroLocus {X 0, X 1 ^ p - C v}, PrimeSpectrum.isClosed_zeroLocus _⟩),
      IsOpenImmersion j ∧ j ≫ blowUpToBase _ ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 2) K))) =
          Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 3) K ⧸
            Ideal.span {(X 0 * X 2 - (X 1 ^ p - C v) : MvPolynomial (Fin 3) K)}))) := by
  have hv0 : v ≠ 0 := fun h0 ↦ hv ⟨0, by simp [h0, zero_pow (Fact.out : p.Prime).ne_zero]⟩
  set ψ :=
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 2) K))).commRingCatIsoToRingEquiv.symm
  let I := Scheme.IdealSheafData.vanishingIdeal
      (X := Spec (CommRingCat.of (MvPolynomial (Fin 2) K)))
      ⟨PrimeSpectrum.zeroLocus {X 0, X 1 ^ p - C v}, PrimeSpectrum.isClosed_zeroLocus _⟩
  let U : (Spec (CommRingCat.of (MvPolynomial (Fin 2) K))).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hI : I.ideal U = Ideal.span {ψ (X 0), ψ (X 1 ^ p - C v)} :=
    ideal_vanishingIdeal_top p v (isPrime_span_X_zero_X_one_pow_sub_C p v hv)
  have hreg : Koszul.IsH1Regular ![ψ (X 0), ψ (X 1 ^ p - C v)] := by
    have := isH1Regular_map_ringEquiv ψ _ (isH1Regular_X_zero_X_one_pow_sub_C p v hv0)
    convert this using 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨e, he⟩ := exists_ringEquiv_affineBlowupAlgebra ψ p v hreg (I.ideal U) hI
  let a : I.ideal U := ⟨ψ (X 0), hI ▸ Ideal.subset_span (Set.mem_insert _ _)⟩
  let C₀ := MvPolynomial (Fin 3) K ⧸
    Ideal.span {(X 0 * X 2 - (X 1 ^ p - C v) : MvPolynomial (Fin 3) K)}
  let j : Spec (CommRingCat.of C₀) ⟶ blowUp I :=
    Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ blowUpAffineChart I U a
  haveI : IsOpenImmersion j := by
    haveI : IsIso (CommRingCat.ofHom e.symm.toRingHom) := e.symm.toCommRingCatIso.isIso_hom
    infer_instance
  have hj : j ≫ blowUpToBase I ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 2) K))) =
      Spec.map (CommRingCat.ofHom (algebraMap K C₀)) := by
    have h1 := blowUpAffineChart_comp_blowUpToBase I U a
    have h2 : U.2.isoSpec.inv ≫ U.1.ι =
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 2) K))).inv :=
      (IsAffineOpen.fromSpec_top (X := Spec (CommRingCat.of (MvPolynomial (Fin 2) K)))).trans
        (Scheme.isoSpec_Spec_inv _)
    have h3 : j ≫ blowUpToBase I = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap
          ((Spec (CommRingCat.of (MvPolynomial (Fin 2) K))).presheaf.obj (Opposite.op U.1))
          (blowUpAffineChartRing I U a))) ≫
          Spec.map (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 2) K))).inv := by
      simp only [j, Category.assoc, h1, h2]
    rw [← Category.assoc, h3]
    simp only [Category.assoc, ← Spec.map_comp]
    congr 1
    ext k
    change e.symm (algebraMap _ _ (ψ (algebraMap K _ k))) = algebraMap K C₀ k
    exact e.symm_apply_eq.mpr (he k).symm
  exact ⟨j, inferInstance, hj⟩

/-- Given a pullback square exhibiting `Y` as `X ×_{Spec K} Spec L` and an open immersion
`Spec A ⟶ X` over `Spec K`, there is an open immersion `Spec (A ⊗[K] L) ⟶ Y`. -/
theorem exists_isOpenImmersion_spec_tensorProduct_of_isPullback {K A L : Type u} [CommRing K]
    [CommRing A] [CommRing L] [Algebra K A] [Algebra K L] {X Y : Scheme.{u}} {f : Y ⟶ X}
    {g : Y ⟶ Spec (CommRingCat.of L)} {s : X ⟶ Spec (CommRingCat.of K)}
    (h : IsPullback f g s (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ s = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    ∃ ι : Spec (CommRingCat.of (TensorProduct K A L)) ⟶ Y, IsOpenImmersion ι := by
  have hP := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct K A L)
  let ι := h.lift (Spec.map (CommRingCat.ofHom (S := TensorProduct K A L)
      Algebra.TensorProduct.includeLeftRingHom) ≫ j)
    (Spec.map (CommRingCat.ofHom (S := TensorProduct K A L)
      Algebra.TensorProduct.includeRight.toRingHom))
    (by rw [Category.assoc, hj, hP.w])
  have hsq : IsPullback (Spec.map (CommRingCat.ofHom (S := TensorProduct K A L)
      Algebra.TensorProduct.includeLeftRingHom)) ι j f := by
    refine IsPullback.of_bot ?_ (h.lift_fst _ _ _).symm h
    rw [h.lift_snd, hj]
    exact hP
  exact ⟨ι, MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq inferInstance⟩

/-- **Kollár 1.49.** Let `K` be a field of characteristic `p` and `v ∈ K` not a `p`-th power, so
that `P = V(x, yᵖ - v)` is a closed point of `𝔸²_K = Spec K[x, y]`. For every field extension
`L` of `K` in which `v` has a `p`-th root (for instance `L = K̄`), the base change
`Y = B_P𝔸²_K ×_K L` of the blow-up of `P` is not regular: it has a point whose local ring is not a
regular local ring. -/
@[mmp "prop_kr1b_imperfect_blowup_p_geometrically_singular"]
public theorem exists_not_isRegularLocalRing_of_isPullback_blowUp
    {K : Type u} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (v : K)
    (hv : ¬ ∃ c : K, c ^ p = v)
    (L : Type u) [Field L] [Algebra K L] (hL : ∃ c : L, c ^ p = algebraMap K L v)
    {Y : Scheme.{u}}
    (f : Y ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal
      (X := Spec (CommRingCat.of (MvPolynomial (Fin 2) K)))
      ⟨PrimeSpectrum.zeroLocus {X 0, X 1 ^ p - C v}, PrimeSpectrum.isClosed_zeroLocus _⟩))
    (g : Y ⟶ Spec (CommRingCat.of L))
    (h : IsPullback f g
      (blowUpToBase _ ≫ Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 2) K))))
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :
    ∃ z : Y, ¬ IsRegularLocalRing (Y.presheaf.stalk z) := by
  haveI := originIdeal_isPrime L p
  obtain ⟨ι, hι⟩ : ∃ ι : Spec (CommRingCat.of (ChartRing L p)) ⟶ Y, IsOpenImmersion ι := by
    obtain ⟨c, hc⟩ := hL
    haveI : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
    obtain ⟨j, hj, hjK⟩ := exists_isOpenImmersion_spec_quotient_blowUp p v hv
    obtain ⟨ι, hι⟩ := exists_isOpenImmersion_spec_tensorProduct_of_isPullback h j hjK
    obtain ⟨eT⟩ := exists_ringEquiv_tensor_chartRing p v L c hc
    haveI : IsIso (CommRingCat.ofHom eT.toRingHom) := eT.toCommRingCatIso.isIso_hom
    exact ⟨Spec.map (CommRingCat.ofHom eT.toRingHom) ≫ ι, inferInstance⟩
  let x : Spec (CommRingCat.of (ChartRing L p)) := ⟨originIdeal L p, inferInstance⟩
  haveI : IsIso (ι.stalkMap x) := (IsOpenImmersion.iff_isIso_stalkMap.mp hι).2 x
  exact ⟨ι x, fun hreg ↦ not_isRegularLocalRing_localization_originIdeal L p
    (IsRegularLocalRing.of_ringEquiv ((asIso (ι.stalkMap x)).commRingCatIsoToRingEquiv.trans
      (Spec.stalkIso _ x).commRingCatIsoToRingEquiv))⟩

end MMP.Resolution

end
