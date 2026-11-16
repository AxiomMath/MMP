module

public import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo

/-!
# The different on a normal prime divisor in a cyclic quotient chart

Let `X` be a normal complex variety, `S ⊂ X` a normal prime divisor and `P ∈ S` a point of
codimension one of `S` whose completed strict henselization is `K[[x, y]]^{μ_m}`, with `I_S`
going to the ideal of the image of the axis `x = 0`. The Kummer cover
`O = 𝒪_{X,P}[f^{1/m}, g f^{-a/m}]` of the cyclic chart is a regular local ring with maximal ideal
`(t, y)`, by flat descent from `O ⊗ R ≅ K[[x, y]]`, and it is unramified away from `S`. The
order of a comparison form along a prime divisor through `P` other than `S` is read off on the
cover, where it is étale, and along `S` from the frame `dϖ, dY, dz`. This gives the coefficient
`(m - 1)/m` of the different of `K_X + S` at `P`, and with it the coefficient
`1 - 1/m + ∑ r_i b_i / m` of the residue different of `K_X + S + ∑ b_i B_i`.

## Main results

* `MMP.Fourfold.coeff_residueDifferent_eq_of_cyclicInvariants_of_charZero`: over an
  algebraically closed field `k` of characteristic zero
* `MMP.Fourfold.coeff_residueDifferent_eq_of_cyclicInvariants`: the case `k = ℂ`

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.6
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace MMP.CyclicChartDifferent

open MMP MMP.Mori MMP.Flips MMP.Fourfold

/-! ### The cyclic cover at a cyclic quotient point -/

section CyclicCover

universe u v

namespace KummerCover

open Polynomial (eval₂ eval₂_sub eval₂_X_pow eval₂_C eval₂_mul monic_X_pow_sub_C
  natDegree_X_pow_sub_C coeff_zero coeff_eq_zero_of_natDegree_lt eval₂_eq_sum_range' natDegree_one
  natDegree)

theorem irreducible_X_pow_sub_C_of_sum_eq_zero {A KA P : Type*} [CommRing A] [IsDomain A]
    [Field KA] [Algebra A KA] [IsFractionRing A KA] [CommRing P] [IsDomain P]
    (ψ : A →+* P) (hψ : Function.Injective ψ) {m : ℕ} (hm : 0 < m) (f : A) (x' : P)
    (hx : x' ^ m = ψ f)
    (hind : ∀ c : ℕ → A, ∑ i ∈ Finset.range m, ψ (c i) * x' ^ i = 0 → ∀ i < m, c i = 0) :
    Irreducible (Polynomial.X ^ m - Polynomial.C (algebraMap A KA f)) := by
  classical
  set FP := FractionRing P
  let ι : KA →+* FP := IsFractionRing.lift (g := (algebraMap P FP).comp ψ)
    ((IsFractionRing.injective P FP).comp hψ)
  have hι : ∀ a : A, ι (algebraMap A KA a) = algebraMap P FP (ψ a) := fun a =>
    IsFractionRing.lift_algebraMap _ a
  set z := algebraMap P FP x'
  have hmon : (Polynomial.X ^ m - Polynomial.C (algebraMap A KA f)).Monic := monic_X_pow_sub_C _ hm.ne'
  have hdeg : (Polynomial.X ^ m - Polynomial.C (algebraMap A KA f)).natDegree = m := natDegree_X_pow_sub_C
  have hno : ∀ g : Polynomial KA, g ≠ 0 → g.natDegree < m → eval₂ ι z g ≠ 0 := by
    intro g hg hgd h0
    obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
      (g.support.image g.coeff)
    choose c hc using fun i : g.support => hs (g.coeff i) (Finset.mem_image_of_mem _ i.2)
    let c' : ℕ → A := fun i => if h : i ∈ g.support then c ⟨i, h⟩ else 0
    have hc' : ∀ i, algebraMap A KA (c' i) = (s : A) • g.coeff i := by
      intro i
      by_cases h : i ∈ g.support
      · simp only [c', dif_pos h]; exact hc ⟨i, h⟩
      · simp only [c', dif_neg h, map_zero]
        rw [Polynomial.notMem_support_iff.1 h, smul_zero]
    have hsum : ∑ i ∈ Finset.range m, ψ (c' i) * x' ^ i = 0 := by
      apply IsFractionRing.injective P FP
      rw [map_zero, map_sum]
      have : eval₂ ι z g = ∑ i ∈ Finset.range m, ι (g.coeff i) * z ^ i := by
        rw [eval₂_eq_sum_range' _ hgd]
      have h2 : ι (algebraMap A KA s) * eval₂ ι z g = 0 := by rw [h0, mul_zero]
      rw [this, Finset.mul_sum] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, ← hι, hc', Algebra.smul_def, map_mul, mul_assoc]
    have hzero := hind c' hsum
    apply hg
    ext i
    rw [coeff_zero]
    by_cases hi : i < m
    · have h1 := hc' i
      rw [hzero i hi, map_zero, Algebra.smul_def] at h1
      have hs0 : algebraMap A KA s ≠ 0 :=
        IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ le_rfl s.2
      exact (mul_eq_zero.1 h1.symm).resolve_left hs0
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hroot : eval₂ ι z (Polynomial.X ^ m - Polynomial.C (algebraMap A KA f)) = 0 := by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hι, ← map_pow, hx, sub_self]
  rw [hmon.irreducible_iff_natDegree]
  refine ⟨fun h1 => by
    have := congrArg natDegree h1; rw [hdeg, natDegree_one] at this; omega,
    fun g h hg hh hgh => ?_⟩
  have h0 : eval₂ ι z g * eval₂ ι z h = 0 := by rw [← eval₂_mul, hgh, hroot]
  have hdg := congrArg natDegree hgh
  rw [hg.natDegree_mul hh, hdeg] at hdg
  rcases mul_eq_zero.1 h0 with h1 | h1
  · by_contra hne
    push Not at hne
    exact hno g hg.ne_zero (by omega) h1
  · by_contra hne
    push Not at hne
    exact hno h hh.ne_zero (by omega) h1

open TensorProduct in
theorem injective_lift_of_sum_eq_zero {A KA L R P : Type*} [CommRing A] [IsDomain A] [Field KA]
    [Algebra A KA] [IsFractionRing A KA] [Field L] [Algebra KA L] [Algebra A L]
    [IsScalarTower A KA L] [CommRing R] [Algebra A R] [Module.Flat A R] [CommRing P]
    [Algebra A P] (O : Subalgebra A L) (pb : PowerBasis KA L) (ht : pb.gen ∈ O)
    (τ : O →ₐ[A] P) (ρ : R →ₐ[A] P)
    (hind : ∀ r : Fin pb.dim → R,
      ∑ i : Fin pb.dim, ρ (r i) * τ ⟨pb.gen, ht⟩ ^ (i : ℕ) = 0 → r = 0) :
    Function.Injective (Algebra.TensorProduct.lift τ ρ fun _ _ => Commute.all _ _) := by
  classical
  set Φ := Algebra.TensorProduct.lift τ ρ fun _ _ => Commute.all _ _
  set t : O := ⟨pb.gen, ht⟩
  have hdec : ∀ ξ : O ⊗[A] R, ∃ s : A, s ≠ 0 ∧ ∃ r : Fin pb.dim → R,
      s • ξ = ∑ i : Fin pb.dim, (t ^ (i : ℕ)) ⊗ₜ r i := by
    intro ξ
    induction ξ using TensorProduct.induction_on with
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | tmul o r =>
      obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors A)
        (Finset.univ : Finset (Fin pb.dim)) (pb.basis.repr (o : L))
      choose a ha using fun i => hs i (Finset.mem_univ i)
      refine ⟨s, nonZeroDivisors.ne_zero s.2, fun i => a i • r, ?_⟩
      have ho : (s : A) • o = ∑ i : Fin pb.dim, a i • t ^ (i : ℕ) := by
        apply Subtype.ext
        simp only [SetLike.val_smul, AddSubmonoidClass.coe_finset_sum, SubmonoidClass.coe_pow]
        conv_lhs => rw [← pb.basis.sum_repr (o : L), Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pb.basis_eq_pow, ← algebraMap_smul KA (a i), ha i, smul_assoc]
      rw [smul_tmul', ho, sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_tmul]
    | add ξ η hξ hη =>
      obtain ⟨s₁, hs₁, r₁, h₁⟩ := hξ
      obtain ⟨s₂, hs₂, r₂, h₂⟩ := hη
      refine ⟨s₁ * s₂, mul_ne_zero hs₁ hs₂, fun i => s₂ • r₁ i + s₁ • r₂ i, ?_⟩
      rw [smul_add, mul_comm, mul_smul, h₁, mul_comm, mul_smul, h₂, Finset.smul_sum,
        Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [tmul_add, ← tmul_smul, ← tmul_smul]
  have htf : ∀ (s : A) (ξ : O ⊗[A] R), s ≠ 0 → s • ξ = 0 → ξ = 0 := by
    intro s ξ hs h
    set incl : O →ₗ[A] L := O.val.toLinearMap
    have hinj : Function.Injective (incl.rTensor R) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
    apply hinj
    rw [map_zero]
    have h2 : (algebraMap A L s) • (incl.rTensor R ξ) = 0 := by
      rw [algebraMap_smul, ← map_smul, h, map_zero]
    have hsL : algebraMap A L s ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply A KA L]
      exact (map_ne_zero _).2 (IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ le_rfl
        (mem_nonZeroDivisors_of_ne_zero hs))
    have := congrArg ((algebraMap A L s)⁻¹ • ·) h2
    rwa [smul_zero, smul_smul, inv_mul_cancel₀ hsL, one_smul] at this
  intro ξ η hξη
  rw [← sub_eq_zero]
  obtain ⟨s, hs, r, hr⟩ := hdec (ξ - η)
  have h0 : Φ (s • (ξ - η)) = 0 := by rw [map_smul, map_sub, hξη, sub_self, smul_zero]
  rw [hr, map_sum] at h0
  simp only [Φ, Algebra.TensorProduct.lift_tmul, map_pow] at h0
  have h1 : ∑ i : Fin pb.dim, ρ (r i) * τ t ^ (i : ℕ) = 0 := by
    rw [← h0]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hr0 := hind r h1
  apply htf s _ hs
  rw [hr, hr0]; simp

open TensorProduct in
theorem span_D_eq_top_of_maximalIdeal {k O : Type*} [Field k] [CommRing O] [IsLocalRing O]
    [Algebra k O] [Module.Finite O Ω[O⁄k]] {t y : O}
    (hmax : IsLocalRing.maximalIdeal O = Ideal.span {t, y}) {d : ℕ} (z : Fin d → O)
    (hz : Submodule.span (IsLocalRing.ResidueField O) (Set.range fun i =>
      KaehlerDifferential.D k (IsLocalRing.ResidueField O) (IsLocalRing.residue O (z i))) = ⊤) :
    Submodule.span O ({KaehlerDifferential.D k O t, KaehlerDifferential.D k O y} ∪
      Set.range fun i => KaehlerDifferential.D k O (z i)) = ⊤ := by
  set N := Submodule.span O ({KaehlerDifferential.D k O t, KaehlerDifferential.D k O y} ∪
      Set.range fun i => KaehlerDifferential.D k O (z i))
  set κ := IsLocalRing.ResidueField O
  have hsurj : Function.Surjective (algebraMap O κ) := IsLocalRing.residue_surjective
  have hex := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k O κ hsurj
  have hker : RingHom.ker (algebraMap O κ) = IsLocalRing.maximalIdeal O := IsLocalRing.ker_residue
  suffices hle : (⊤ : Submodule O Ω[O⁄k]) ≤ N ⊔ IsLocalRing.maximalIdeal O • ⊤ by
    exact top_le_iff.1 (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson _) hle)
  have hDt : KaehlerDifferential.D k O t ∈ N := Submodule.subset_span (Or.inl (by simp))
  have hDy : KaehlerDifferential.D k O y ∈ N := Submodule.subset_span (Or.inl (by simp))
  have hsm : ∀ (a : O) (w : Ω[O⁄k]),
      (1 : κ) ⊗ₜ[O] (a • w) = algebraMap O κ a • ((1 : κ) ⊗ₜ[O] w) := by
    intro a w
    rw [← TensorProduct.smul_tmul, smul_tmul', Algebra.smul_def, mul_one, Algebra.smul_def,
      mul_one, Algebra.algebraMap_self, RingHom.id_apply]
  intro ω _
  have hω : KaehlerDifferential.mapBaseChange k O κ (1 ⊗ₜ ω) ∈ Submodule.span κ
      (Set.range fun i => KaehlerDifferential.D k κ (IsLocalRing.residue O (z i))) := by
    rw [hz]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun κ).1 hω
  choose c' hc' using fun i => hsurj (c i)
  set ω₁ := ∑ i, c' i • KaehlerDifferential.D k O (z i)
  have hω₁ : ω₁ ∈ N := Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨i, rfl⟩))
  have h0 : KaehlerDifferential.mapBaseChange k O κ ((1 : κ) ⊗ₜ (ω - ω₁)) = 0 := by
    rw [tmul_sub, map_sub, ← hc, sub_eq_zero]
    simp only [ω₁, tmul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsm, map_smul, KaehlerDifferential.mapBaseChange_tmul, one_smul,
      KaehlerDifferential.map_D, hc' i]
    rfl
  obtain ⟨e, he⟩ := (hex _).1 h0
  obtain ⟨⟨a, ha⟩, rfl⟩ := Ideal.toCotangent_surjective _ e
  rw [KaehlerDifferential.kerCotangentToTensor_toCotangent] at he
  have ha' : a ∈ Ideal.span {t, y} := hmax ▸ hker ▸ ha
  obtain ⟨p, r, rfl⟩ := Ideal.mem_span_pair.1 ha'
  have ht0 : algebraMap O κ t = 0 := by
    rw [← RingHom.mem_ker, hker, hmax]; exact Ideal.subset_span (by simp)
  have hy0 : algebraMap O κ y = 0 := by
    rw [← RingHom.mem_ker, hker, hmax]; exact Ideal.subset_span (by simp)
  set ω₂ := ω - ω₁ - (p • KaehlerDifferential.D k O t + r • KaehlerDifferential.D k O y)
  have h1 : (1 : κ) ⊗ₜ[O] ω₂ = 0 := by
    have he' : (1 : κ) ⊗ₜ[O] (ω - ω₁) = (1 : κ) ⊗ₜ[O] (p • KaehlerDifferential.D k O t +
        r • KaehlerDifferential.D k O y) := by
      rw [← he]
      simp only [map_add, Derivation.leibniz, tmul_add, hsm, ht0, hy0, zero_smul, add_zero]
    simp only [ω₂, tmul_sub, he', sub_self]
  have h2 : ω₂ ∈ IsLocalRing.maximalIdeal O • (⊤ : Submodule O Ω[O⁄k]) := by
    have h1' : ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) 1 :
        O ⧸ IsLocalRing.maximalIdeal O) ⊗ₜ[O] ω₂) = 0 := h1
    have := congrArg (quotTensorEquivQuotSMul Ω[O⁄k] (IsLocalRing.maximalIdeal O)) h1'
    rw [quotTensorEquivQuotSMul_mk_tmul, one_smul, map_zero] at this
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  have : ω = (ω₁ + (p • KaehlerDifferential.D k O t + r • KaehlerDifferential.D k O y)) + ω₂ := by
    simp only [ω₂]; abel
  rw [this]
  exact Submodule.add_mem_sup (N.add_mem hω₁ (N.add_mem (N.smul_mem _ hDt) (N.smul_mem _ hDy))) h2

theorem derivation_eq_zero_of_adjoin {A₀ C L B M : Type*} [CommRing A₀] [CommRing C]
    [CommRing L] [CommRing B] [Algebra A₀ L] [Algebra C B] [AddCommGroup M] [Module B M]
    [Module C M] [IsScalarTower C B M]
    (O : Subalgebra A₀ L) [Algebra O B] (S : Submonoid O) [IsLocalization S B]
    (φ : A₀ →+* C) (hφ : ∀ a : A₀, algebraMap O B (algebraMap A₀ O a) = algebraMap C B (φ a))
    {t y : L} (hO : O = Algebra.adjoin A₀ {t, y}) (ht : t ∈ O) (hy : y ∈ O)
    (D : Derivation C B M) (hDt : D (algebraMap O B ⟨t, ht⟩) = 0)
    (hDy : D (algebraMap O B ⟨y, hy⟩) = 0) : D = 0 := by
  have hO' : ∀ o : O, D (algebraMap O B o) = 0 := by
    rintro ⟨o, ho⟩
    have ho' : o ∈ Algebra.adjoin A₀ {t, y} := hO ▸ ho
    induction ho' using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hDt
      · exact hDy
    | algebraMap a =>
      have : (⟨algebraMap A₀ L a, ho⟩ : O) = algebraMap A₀ O a := rfl
      rw [this, hφ, D.map_algebraMap]
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, ho⟩ : O) = ⟨x, hO ▸ hx⟩ + ⟨y, hO ▸ hy⟩ := rfl
      rw [this, map_add, map_add, ihx, ihy, add_zero]
    | mul x y hx hy ihx ihy =>
      have : (⟨x * y, ho⟩ : O) = ⟨x, hO ▸ hx⟩ * ⟨y, hO ▸ hy⟩ := rfl
      rw [this, map_mul, D.leibniz, ihx, ihy, smul_zero, smul_zero, add_zero]
  ext b
  obtain ⟨⟨o, s⟩, rfl⟩ := IsLocalization.mk'_surjective S b
  have hs : IsUnit (algebraMap O B s) := IsLocalization.map_units B s
  have h1 : D (IsLocalization.mk' B o s * algebraMap O B s) = 0 := by
    rw [IsLocalization.mk'_spec, hO']
  rw [D.leibniz, hO', smul_zero, zero_add] at h1
  rw [Derivation.zero_apply]
  obtain ⟨u, hu⟩ := hs
  have := congrArg (fun z => (↑u⁻¹ : B) • z) h1
  simp only [smul_zero] at this
  rwa [← hu, smul_smul, Units.inv_mul, one_smul] at this

/-- A spanning family of `Ω_{O/k}` maps to a spanning family of `Ω_{B/k}` for a localization `B`
of `O`. -/
theorem span_map_eq_top_of_isLocalization {k O B : Type*} [CommRing k] [CommRing O] [CommRing B]
    [Algebra k O] [Algebra k B] [Algebra O B] [IsScalarTower k O B] (M : Submonoid O)
    [IsLocalization M B] {ι : Type*} (s : ι → O)
    (hs : Submodule.span O (Set.range fun i => KaehlerDifferential.D k O (s i)) = ⊤) :
    Submodule.span B (Set.range fun i => KaehlerDifferential.D k B (algebraMap O B (s i))) = ⊤ := by
  set N := Submodule.span B (Set.range fun i => KaehlerDifferential.D k B (algebraMap O B (s i)))
  have hO : ∀ o : O, KaehlerDifferential.D k B (algebraMap O B o) ∈ N := by
    intro o
    have ho : KaehlerDifferential.D k O o ∈ Submodule.span O
        (Set.range fun i => KaehlerDifferential.D k O (s i)) := hs ▸ trivial
    have hm := Submodule.mem_map_of_mem
      (f := (KaehlerDifferential.map k k O B).restrictScalars O) ho
    rw [Submodule.map_span] at hm
    simp only [LinearMap.coe_restrictScalars, KaehlerDifferential.map_D] at hm
    refine Submodule.span_le_restrictScalars O B _ (Submodule.span_mono ?_ hm)
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by simp [KaehlerDifferential.map_D]⟩
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation k B, Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  obtain ⟨⟨o, u⟩, rfl⟩ := IsLocalization.mk'_surjective M b
  have hu : IsUnit (algebraMap O B u) := IsLocalization.map_units B u
  have h1 : KaehlerDifferential.D k B (IsLocalization.mk' B o u * algebraMap O B u) ∈ N := by
    rw [IsLocalization.mk'_spec]; exact hO o
  rw [Derivation.leibniz] at h1
  have h2 : algebraMap O B u • KaehlerDifferential.D k B (IsLocalization.mk' B o u) ∈ N := by
    have := N.sub_mem h1 (N.smul_mem (IsLocalization.mk' B o u) (hO u))
    rwa [add_sub_cancel_left] at this
  obtain ⟨v, hv⟩ := hu
  have := N.smul_mem (↑v⁻¹ : B) h2
  rwa [← hv, smul_smul, Units.inv_mul, one_smul] at this

end KummerCover

namespace CyclicChart

open MvPowerSeries

variable {K : Type*} [Field K]

theorem coeff_X_one_mul (b : MvPowerSeries (Fin 2) K) :
    coeff (Finsupp.single 1 1) (X 1 * b) = constantCoeff b := by
  have e := coeff_add_monomial_mul (Finsupp.single (1 : Fin 2) 1) 0 b (1 : K)
  rw [add_zero] at e
  rw [X_def, e, one_mul, coeff_zero_eq_constantCoeff_apply]

theorem exists_eq_X_mul_add_X_mul {γ : MvPowerSeries (Fin 2) K} (hγ : constantCoeff γ = 0) :
    ∃ α β : MvPowerSeries (Fin 2) K, γ = X 0 * α + X 1 * β ∧
      constantCoeff β = coeff (Finsupp.single 1 1) γ := by
  classical
  let g : MvPowerSeries (Fin 2) K := fun d => if d 0 = 0 then coeff d γ else 0
  have hg : ∀ d, coeff d g = if d 0 = 0 then coeff d γ else 0 := fun d => rfl
  have h0 : X 0 ∣ γ - g := by
    rw [X_dvd_iff]; intro d hd; simp [hg, hd]
  have h1 : X 1 ∣ g := by
    rw [X_dvd_iff]; intro d hd
    rw [hg]
    split_ifs with h
    · have : d = 0 := by ext i; fin_cases i <;> simp_all
      subst this; simpa using hγ
    · rfl
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  refine ⟨a, b, by rw [← ha, ← hb]; ring, ?_⟩
  have := congrArg (coeff (Finsupp.single 1 1)) hb
  rw [hg, if_pos (by simp)] at this
  rw [this, coeff_X_one_mul]

theorem mem_span_range_X_of_constantCoeff_eq_zero {f : MvPowerSeries (Fin 2) K}
    (hf : constantCoeff f = 0) :
    f ∈ Ideal.span (Set.range (X : Fin 2 → MvPowerSeries (Fin 2) K)) := by
  obtain ⟨a, b, rfl, -⟩ := exists_eq_X_mul_add_X_mul hf
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨0, rfl⟩))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨1, rfl⟩))

theorem exists_pow_eq_of_isUnit [IsAlgClosed K] [CharZero K] {m : ℕ} (hm : 0 < m)
    {v : MvPowerSeries (Fin 2) K} (hv : IsUnit v) : ∃ w, w ^ m = v := by
  set I : Ideal (MvPowerSeries (Fin 2) K) := Ideal.span (Set.range X)
  have hc : constantCoeff v ≠ 0 := by
    have := (isUnit_iff_constantCoeff (φ := v)).1 hv
    exact this.ne_zero
  obtain ⟨c0, hc0⟩ := IsAlgClosed.exists_pow_nat_eq (constantCoeff v) hm
  have hc00 : c0 ≠ 0 := by rintro rfl; rw [zero_pow hm.ne'] at hc0; exact hc hc0.symm
  have hH : HenselianRing (MvPowerSeries (Fin 2) K) I := IsAdicComplete.henselianRing _ _
  obtain ⟨w, hw, -⟩ := hH.is_henselian (Polynomial.X ^ m - Polynomial.C v)
    (Polynomial.monic_X_pow_sub_C v hm.ne') (C c0) (by
      apply mem_span_range_X_of_constantCoeff_eq_zero
      simp [hc0]) (by
      apply IsUnit.map
      rw [isUnit_iff_constantCoeff]
      simp [Polynomial.derivative_X_pow, hc00, hm.ne'])
  refine ⟨w, ?_⟩
  have := hw.eq_zero
  simp at this
  exact sub_eq_zero.1 this

theorem eq_one_of_pow_eq_one [CharZero K] {m : ℕ} (hm : 0 < m) {u : MvPowerSeries (Fin 2) K}
    (hu : u ^ m = 1) (h1 : constantCoeff u = 1) : u = 1 := by
  have hs : (u - 1) * (∑ i ∈ Finset.range m, u ^ i) = 0 := by
    rw [mul_comm, geom_sum_mul, hu, sub_self]
  have hunit : IsUnit (∑ i ∈ Finset.range m, u ^ i) := by
    rw [isUnit_iff_constantCoeff, map_sum]
    simp only [map_pow, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact isUnit_iff_ne_zero.2 (by exact_mod_cast hm.ne')
  exact sub_eq_zero.1 ((hunit.mul_left_eq_zero).1 hs)

theorem constantCoeff_rescale (a : Fin 2 → K) (f : MvPowerSeries (Fin 2) K) :
    constantCoeff (rescale a f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale]
  simp

theorem coeff_X_zero_mul_single_one (b : MvPowerSeries (Fin 2) K) :
    coeff (Finsupp.single 1 1) (X 0 * b) = 0 := by
  have : X 0 ∣ X 0 * b := dvd_mul_right _ _
  rw [X_dvd_iff] at this
  exact this _ (by simp)

theorem coeff_mul_of_X_pow_dvd {a : ℕ} {h r : MvPowerSeries (Fin 2) K} (hd : X 0 ^ a ∣ h)
    (h0 : coeff (Finsupp.single 0 a) h = 0) :
    coeff (Finsupp.single 0 a + Finsupp.single 1 1) (r * h) =
      constantCoeff r * coeff (Finsupp.single 0 a + Finsupp.single 1 1) h := by
  obtain ⟨h', rfl⟩ := hd
  have hX : (X 0 ^ a : MvPowerSeries (Fin 2) K) = monomial (Finsupp.single 0 a) 1 :=
    MvPowerSeries.X_pow_eq 0 a
  have hc : ∀ g : MvPowerSeries (Fin 2) K, coeff (Finsupp.single 0 a + Finsupp.single 1 1)
      (X 0 ^ a * g) = coeff (Finsupp.single 1 1) g := fun g => by
    rw [hX, coeff_add_monomial_mul, one_mul]
  have h00 : constantCoeff h' = 0 := by
    have e := coeff_add_monomial_mul (Finsupp.single (0 : Fin 2) a) 0 h' (1 : K)
    rw [add_zero, ← hX] at e
    rw [e, one_mul, coeff_zero_eq_constantCoeff_apply] at h0
    exact h0
  obtain ⟨α, β, rfl, hβ⟩ := exists_eq_X_mul_add_X_mul h00
  rw [mul_left_comm, hc, hc, mul_add, map_add, map_add, mul_left_comm, mul_left_comm r,
    coeff_X_zero_mul_single_one, coeff_X_zero_mul_single_one, coeff_X_one_mul,
    coeff_X_one_mul, map_mul, zero_add, zero_add]

theorem maximalIdeal_eq_span_X_X :
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) K) = Ideal.span {X 0, X 1} := by
  apply le_antisymm
  · intro f hf
    have h0 : constantCoeff f = 0 := by
      by_contra h
      exact (IsLocalRing.mem_maximalIdeal _).1 hf
        ((isUnit_iff_constantCoeff).2 (isUnit_iff_ne_zero.2 h))
    obtain ⟨a, b, hab, -⟩ := exists_eq_X_mul_add_X_mul h0
    rw [hab, mul_comm (X 0), mul_comm (X 1)]
    exact Ideal.mem_span_pair.2 ⟨a, b, rfl⟩
  · rw [Ideal.span_le]
    intro f hf
    rcases hf with rfl | rfl <;>
    · rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        isUnit_iff_constantCoeff]
      simp

theorem span_eq_span_X_X {w α β : MvPowerSeries (Fin 2) K} (hw : IsUnit w) (hβ : IsUnit β) :
    Ideal.span {w * X 0, X 0 * α + X 1 * β} = Ideal.span {X 0, X 1} := by
  obtain ⟨w', hw'⟩ := hw.exists_left_inv
  obtain ⟨β', hβ'⟩ := hβ.exists_left_inv
  apply le_antisymm
  · rw [Ideal.span_le]
    intro f hf
    rcases hf with rfl | rfl
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  · rw [Ideal.span_le]
    have hx : X 0 ∈ Ideal.span {w * X 0, X 0 * α + X 1 * β} := by
      have h := Ideal.mul_mem_left (Ideal.span {w * X 0, X 0 * α + X 1 * β}) w'
        (Ideal.subset_span (s := {w * X 0, X 0 * α + X 1 * β}) (Set.mem_insert _ _))
      rwa [← mul_assoc, hw', one_mul] at h
    intro f hf
    rcases hf with rfl | rfl
    · exact hx
    · have h := Ideal.mul_mem_left (Ideal.span {w * X 0, X 0 * α + X 1 * β}) β'
        (Ideal.sub_mem _ (Ideal.subset_span (s := {w * X 0, X 0 * α + X 1 * β})
          (Set.mem_insert_of_mem _ rfl)) (Ideal.mul_mem_right α _ hx))
      rwa [add_sub_cancel_left, mul_left_comm, hβ', mul_one] at h

theorem weight_X_zero (d : Fin 2 →₀ ℕ) : Finsupp.weight ![1, 0] d = d 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fin.sum_univ_two]

theorem X_zero_pow_dvd_iff_le_weightedOrder {k : ℕ} {f : MvPowerSeries (Fin 2) K} :
    X 0 ^ k ∣ f ↔ (k : ℕ∞) ≤ weightedOrder ![1, 0] f := by
  rw [X_pow_dvd_iff]
  constructor
  · intro h
    refine le_weightedOrder _ fun d hd => ?_
    apply h
    rw [← weight_X_zero]
    exact_mod_cast hd
  · intro h d hd
    by_contra hne
    have := weightedOrder_le ![1, 0] hne
    rw [weight_X_zero] at this
    exact not_le.2 hd (by exact_mod_cast h.trans this)

theorem X_zero_pow_dvd_of_dvd_mul {k : ℕ} {f g : MvPowerSeries (Fin 2) K}
    (hf : ¬ X 0 ∣ f) (h : X 0 ^ k ∣ f * g) : X 0 ^ k ∣ g := by
  rw [X_zero_pow_dvd_iff_le_weightedOrder, weightedOrder_mul] at h
  rw [X_zero_pow_dvd_iff_le_weightedOrder]
  have hf' : weightedOrder ![1, 0] f = 0 := by
    by_contra hne
    apply hf
    rw [← pow_one (X 0), X_zero_pow_dvd_iff_le_weightedOrder]
    exact ENat.one_le_iff_ne_zero.2 hne
  rwa [hf', zero_add] at h

variable {m : ℕ} {q : ℤ}

theorem mem_cyclicInvariants_of_pow_eq [CharZero K] (hm : 0 < m) {w : MvPowerSeries (Fin 2) K}
    (hw : IsUnit w) (hwv : w ^ m ∈ cyclicInvariants K m q) : w ∈ cyclicInvariants K m q := by
  rw [mem_cyclicInvariants_iff] at hwv ⊢
  intro ζ
  obtain ⟨w', hw'⟩ := hw.exists_right_inv
  have h := hwv ζ
  set z := rescale (cyclicWeights K m q ζ) w
  have hu : (z * w') ^ m = 1 := by
    rw [mul_pow, ← map_pow, h, ← mul_pow, hw', one_pow]
  have hc : constantCoeff (z * w') = 1 := by
    rw [map_mul, constantCoeff_rescale, ← map_mul, hw', map_one]
  have := eq_one_of_pow_eq_one hm hu hc
  calc z = z * (w' * w) := by rw [mul_comm w', hw', mul_one]
    _ = (z * w') * w := by ring
    _ = w := by rw [this, one_mul]

theorem rescale_X_zero (ζ : rootsOfUnity m K) :
    rescale (cyclicWeights K m q ζ) (X 0 : MvPowerSeries (Fin 2) K) = C ((ζ : Kˣ) : K) * X 0 := by
  ext d
  rw [coeff_rescale, coeff_C_mul, coeff_X]
  split_ifs with h
  · subst h; simp [cyclicWeights]
  · simp

theorem rescale_mul_pow_X_zero (ζ : rootsOfUnity m K) {w r : MvPowerSeries (Fin 2) K}
    (hw : w ∈ cyclicInvariants K m q) (hr : r ∈ cyclicInvariants K m q) (i : ℕ) :
    rescale (cyclicWeights K m q ζ) (r * (w * X 0) ^ i) =
      C (((ζ : Kˣ) : K) ^ i) * (r * (w * X 0) ^ i) := by
  rw [map_mul, map_pow, map_mul, (mem_cyclicInvariants_iff _ _ _ _).1 hr ζ,
    (mem_cyclicInvariants_iff _ _ _ _).1 hw ζ, rescale_X_zero, map_pow]
  ring

theorem X_pow_mul_X_pow_mem_cyclicInvariants {i j : ℕ} (h : (m : ℤ) ∣ i + q * j) :
    (X 0 ^ i * X 1 ^ j : MvPowerSeries (Fin 2) K) ∈ cyclicInvariants K m q := by
  rw [mem_cyclicInvariants_iff]
  intro ζ
  have h1 : ∀ k : Fin 2, rescale (cyclicWeights K m q ζ) (X k : MvPowerSeries (Fin 2) K) =
      C (cyclicWeights K m q ζ k) * X k := by
    intro k; ext d
    rw [coeff_rescale, coeff_C_mul, coeff_X]
    split_ifs with h
    · subst h; simp
    · simp
  rw [map_mul, map_pow, map_pow, h1, h1, mul_pow, mul_pow, mul_mul_mul_comm, ← map_pow, ← map_pow,
    ← map_mul]
  have hζ : ((ζ : Kˣ) : K) ^ i * (((ζ : Kˣ) ^ q : Kˣ) : K) ^ j = 1 := by
    obtain ⟨c, hc⟩ := h
    have hm : (ζ : Kˣ) ^ (m : ℤ) = 1 := by rw [zpow_natCast]; exact ζ.2
    have : (ζ : Kˣ) ^ ((i : ℤ) + q * j) = 1 := by rw [hc, zpow_mul, hm, one_zpow]
    have e : ((ζ : Kˣ) : K) ^ i * (((ζ : Kˣ) ^ q : Kˣ) : K) ^ j =
        (((ζ : Kˣ) ^ ((i : ℤ) + q * j) : Kˣ) : K) := by
      rw [zpow_add, zpow_mul, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val,
        zpow_natCast, Units.val_pow_eq_pow_val]
    rw [e, this, Units.val_one]
  simp only [cyclicWeights, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [hζ, map_one, one_mul]

theorem dvd_of_coeff_ne_zero [IsAlgClosed K] [CharZero K] (hm : 0 < m)
    {h : MvPowerSeries (Fin 2) K} (hh : h ∈ cyclicInvariants K m q) {d : Fin 2 →₀ ℕ}
    (hd : coeff d h ≠ 0) : (m : ℤ) ∣ d 0 + q * d 1 := by
  have : NeZero (m : K) := ⟨by exact_mod_cast hm.ne'⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K m
  have : NeZero m := ⟨hm.ne'⟩
  set ζ : rootsOfUnity m K := hζ₀.toRootsOfUnity
  have e := congrArg (coeff d) ((mem_cyclicInvariants_iff _ _ _ _).1 hh ζ)
  rw [coeff_rescale] at e
  have e2 : (d.prod fun s n => (cyclicWeights K m q ζ s) ^ n) =
      (((ζ : Kˣ) ^ ((d 0 : ℤ) + q * d 1) : Kˣ) : K) := by
    rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    simp only [cyclicWeights, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [zpow_add, zpow_mul, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val,
      zpow_natCast, Units.val_pow_eq_pow_val]
  rw [e2] at e
  have h1 : (((ζ : Kˣ) ^ ((d 0 : ℤ) + q * d 1) : Kˣ) : K) = 1 :=
    mul_right_cancel₀ hd (e.trans (one_mul _).symm)
  have h2 : (ζ : Kˣ) ^ ((d 0 : ℤ) + q * d 1) = 1 := Units.val_eq_one.1 h1
  have hprim : IsPrimitiveRoot (ζ : Kˣ) m :=
    IsPrimitiveRoot.coe_units_iff.1 (by simpa [ζ] using hζ₀)
  exact (hprim.zpow_eq_one_iff_dvd _).1 h2

theorem eq_zero_of_sum_eq_zero_of_rescale [CharZero K] (hm : 0 < m) {ζ₀ : K}
    (hζ : IsPrimitiveRoot ζ₀ m) {e : ℕ → MvPowerSeries (Fin 2) K}
    (he : ∀ (ζ : rootsOfUnity m K) i, rescale (cyclicWeights K m q ζ) (e i) =
      C (((ζ : Kˣ) : K) ^ i) * e i)
    (hs : ∑ i ∈ Finset.range m, e i = 0) : ∀ j < m, e j = 0 := by
  have : NeZero m := ⟨hm.ne'⟩
  set ζr : rootsOfUnity m K := hζ.toRootsOfUnity
  have hζr : ∀ l : ℕ, (((ζr ^ l : rootsOfUnity m K) : Kˣ) : K) = ζ₀ ^ l := fun l => by
    simp [ζr]
  have hl : ∀ l : ℕ, ∑ i ∈ Finset.range m, C ((ζ₀ ^ l) ^ i) * e i = 0 := by
    intro l
    have := congrArg (rescale (cyclicWeights K m q (ζr ^ l))) hs
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [he, hζr]
  intro j hj
  have key : ∑ l ∈ Finset.range m, C ((ζ₀ ^ l) ^ (m - j)) *
      (∑ i ∈ Finset.range m, C ((ζ₀ ^ l) ^ i) * e i) = C (m : K) * e j := by
    simp_rw [Finset.mul_sum, ← mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← map_sum]
    rw [Finset.sum_eq_single j]
    · congr 1
      rw [show (∑ l ∈ Finset.range m, (ζ₀ ^ l) ^ (m - j) * (ζ₀ ^ l) ^ j) =
          ∑ l ∈ Finset.range m, (1 : K) from Finset.sum_congr rfl fun l _ => by
        rw [← pow_add, Nat.sub_add_cancel hj.le, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one,
          one_pow]]
      simp
    · intro i hi hij
      have hne : ζ₀ ^ (m - j + i) ≠ 1 := by
        intro h1
        have hd := (hζ.pow_eq_one_iff_dvd _).1 h1
        have hi' := Finset.mem_range.1 hi
        rcases Nat.lt_or_gt_of_ne hij with h | h
        · exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
        · obtain ⟨c, hc⟩ := hd
          have : m < m - j + i := by omega
          have : m - j + i < 2 * m := by omega
          have h1 : 1 < c := by nlinarith
          have h2 : c < 2 := by nlinarith
          omega
      have : ∑ l ∈ Finset.range m, (ζ₀ ^ l) ^ (m - j) * (ζ₀ ^ l) ^ i = 0 := by
        have h' : ∑ l ∈ Finset.range m, (ζ₀ ^ (m - j + i)) ^ l = 0 := by
          rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self,
            zero_div]
        rw [← h']
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← pow_add, ← pow_mul, ← pow_mul, mul_comm]
      rw [this, map_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_range.2 hj) h
  have h0 : C (m : K) * e j = 0 := by
    rw [← key]; exact Finset.sum_eq_zero fun l _ => by rw [hl l, mul_zero]
  have hmK : (m : K) ≠ 0 := by exact_mod_cast hm.ne'
  have hu : IsUnit (C (m : K) : MvPowerSeries (Fin 2) K) := by
    rw [isUnit_iff_constantCoeff]; simpa using hmK
  exact (hu.mul_right_eq_zero).1 h0

theorem eq_top_of_span_eq_maximalIdeal (R S : Subring (MvPowerSeries (Fin 2) K)) [IsLocalRing R]
    [Module.Finite R (MvPowerSeries (Fin 2) K)] (hRS : R ≤ S) (hC : ∀ c : K, C c ∈ R)
    {x' y' : MvPowerSeries (Fin 2) K} (hx : x' ∈ S) (hy : y' ∈ S)
    (hspan : Ideal.span {x', y'} = IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) K))
    {N : ℕ} (hxR : x' ^ N ∈ R) (hxN : (⟨_, hxR⟩ : R) ∈ IsLocalRing.maximalIdeal R)
    (hyR : y' ^ N ∈ R) (hyN : (⟨_, hyR⟩ : R) ∈ IsLocalRing.maximalIdeal R) :
    S = ⊤ := by
  have hconst : ∀ p : MvPowerSeries (Fin 2) K, p - C (constantCoeff p) ∈ Ideal.span {x', y'} := by
    intro p
    rw [hspan, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff]
    simp
  have hxI : x' ∈ Ideal.span {x', y'} := Ideal.subset_span (by simp)
  have hyI : y' ∈ Ideal.span {x', y'} := Ideal.subset_span (by simp)
  -- every element of `I^k` is congruent to an element of `S ∩ I^k` modulo `I^(k+1)`
  have hstep : ∀ k : ℕ, ∀ z ∈ Ideal.span {x', y'} ^ k, ∃ s ∈ S,
      s ∈ Ideal.span {x', y'} ^ k ∧ z - s ∈ Ideal.span {x', y'} ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro z _
      exact ⟨C (constantCoeff z), hRS (hC _), by simp, by simpa using hconst z⟩
    | succ k ih =>
      intro z hz
      rw [pow_succ'] at hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro a ha b hb
        obtain ⟨sb, hsb, hsbk, hib⟩ := ih b hb
        obtain ⟨p1, p2, rfl⟩ := Ideal.mem_span_pair.1 ha
        refine ⟨(C (constantCoeff p1) * x' + C (constantCoeff p2) * y') * sb,
          S.mul_mem (S.add_mem (S.mul_mem (hRS (hC _)) hx) (S.mul_mem (hRS (hC _)) hy)) hsb,
          ?_, ?_⟩
        · rw [pow_succ']
          refine Ideal.mul_mem_mul ?_ hsbk
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hxI) (Ideal.mul_mem_left _ _ hyI)
        · have e : (p1 * x' + p2 * y') * b - (C (constantCoeff p1) * x' +
              C (constantCoeff p2) * y') * sb =
              ((p1 - C (constantCoeff p1)) * x' + (p2 - C (constantCoeff p2)) * y') * sb +
                (p1 * x' + p2 * y') * (b - sb) := by ring
          rw [e]
          refine Ideal.add_mem _ ?_ ?_
          · rw [show k + 1 + 1 = 2 + k by ring, pow_add]
            refine Ideal.mul_mem_mul ?_ hsbk
            rw [pow_two]
            exact Ideal.add_mem _ (Ideal.mul_mem_mul (hconst p1) hxI)
              (Ideal.mul_mem_mul (hconst p2) hyI)
          · rw [show k + 1 + 1 = 1 + (k + 1) by ring, pow_add, pow_one]
            exact Ideal.mul_mem_mul (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hxI)
              (Ideal.mul_mem_left _ _ hyI)) hib
      · rintro z₁ z₂ ⟨s₁, hs₁, hk₁, h₁⟩ ⟨s₂, hs₂, hk₂, h₂⟩
        refine ⟨s₁ + s₂, S.add_mem hs₁ hs₂, Ideal.add_mem _ hk₁ hk₂, ?_⟩
        rw [show z₁ + z₂ - (s₁ + s₂) = (z₁ - s₁) + (z₂ - s₂) by ring]
        exact Ideal.add_mem _ h₁ h₂
  have happrox : ∀ k : ℕ, ∀ h : MvPowerSeries (Fin 2) K, ∃ s ∈ S,
      h - s ∈ Ideal.span {x', y'} ^ k := by
    intro k
    induction k with
    | zero => intro h; exact ⟨0, S.zero_mem, by simp⟩
    | succ k ih =>
      intro h
      obtain ⟨s, hs, hk⟩ := ih h
      obtain ⟨s', hs', -, hk'⟩ := hstep k _ hk
      refine ⟨s + s', S.add_mem hs hs', ?_⟩
      rwa [show h - (s + s') = h - s - s' by ring]
  -- the `R`-submodule `S`
  let SM : Submodule R (MvPowerSeries (Fin 2) K) :=
    { carrier := S
      add_mem' := S.add_mem
      zero_mem' := S.zero_mem
      smul_mem' := fun r s hs => S.mul_mem (hRS r.2) hs }
  have hle : (⊤ : Submodule R (MvPowerSeries (Fin 2) K)) ≤
      SM ⊔ IsLocalRing.maximalIdeal R • ⊤ := by
    intro h _
    obtain ⟨s, hs, hk⟩ := happrox (N + N) h
    have hk' : h - s ∈ Ideal.span {x' ^ N} ⊔ Ideal.span {y' ^ N} := by
      have h1 : Ideal.span {x', y'} = Ideal.span {x'} ⊔ Ideal.span {y'} := by
        rw [← Ideal.span_union]; rfl
      have := (Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {x'}) (J := Ideal.span {y'})
        (n := N) (m := N))
      rw [← h1, Ideal.span_singleton_pow, Ideal.span_singleton_pow] at this
      exact this hk
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hk'
    obtain ⟨p1, rfl⟩ := Ideal.mem_span_singleton'.1 hu
    obtain ⟨p2, rfl⟩ := Ideal.mem_span_singleton'.1 hv
    have : h = s + ((⟨_, hxR⟩ : R) • p1 + (⟨_, hyR⟩ : R) • p2) := by
      rw [Subring.smul_def, Subring.smul_def, smul_eq_mul, smul_eq_mul]
      rw [← sub_eq_iff_eq_add', ← huv]; ring
    rw [this]
    exact Submodule.add_mem_sup hs (Submodule.add_mem _ (Submodule.smul_mem_smul hxN trivial)
      (Submodule.smul_mem_smul hyN trivial))
  have htop : (⊤ : Submodule R (MvPowerSeries (Fin 2) K)) ≤ SM :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top)
      (IsLocalRing.maximalIdeal_le_jacobson _) hle
  exact eq_top_iff.2 fun h _ => htop (Submodule.mem_top (x := h))

theorem mem_cyclicInvariants_of_mul_mem {a y : MvPowerSeries (Fin 2) K}
    (ha : a ∈ cyclicInvariants K m q) (ha0 : a ≠ 0) (hay : a * y ∈ cyclicInvariants K m q) :
    y ∈ cyclicInvariants K m q := by
  rw [mem_cyclicInvariants_iff] at ha hay ⊢
  intro ζ
  have h := hay ζ
  rw [map_mul, ha ζ] at h
  exact mul_left_cancel₀ ha0 h

theorem prime_X_zero : Prime (X 0 : MvPowerSeries (Fin 2) K) := by
  refine ⟨fun h => by
    have := congrArg (coeff (Finsupp.single (0 : Fin 2) 1)) h
    simp at this, fun h => ?_, fun a b hab => ?_⟩
  · rw [isUnit_iff_constantCoeff] at h; simp at h
  · by_contra hn
    push Not at hn
    exact hn.2 (by simpa using X_zero_pow_dvd_of_dvd_mul (k := 1) hn.1 (by simpa using hab))

theorem coeff_add_X_zero_pow_mul (a : ℕ) (d : Fin 2 →₀ ℕ) (h : MvPowerSeries (Fin 2) K) :
    coeff (Finsupp.single 0 a + d) (X 0 ^ a * h) = coeff d h := by
  rw [MvPowerSeries.X_pow_eq, coeff_add_monomial_mul, one_mul]

theorem coeff_X_zero_pow_mul (a : ℕ) (h : MvPowerSeries (Fin 2) K) :
    coeff (Finsupp.single 0 a) (X 0 ^ a * h) = constantCoeff h := by
  have := coeff_add_X_zero_pow_mul a 0 h
  rwa [add_zero, coeff_zero_eq_constantCoeff_apply] at this

theorem coeff_single_mul_of_X_pow_dvd {a : ℕ} {h r : MvPowerSeries (Fin 2) K}
    (hd : X 0 ^ a ∣ h) :
    coeff (Finsupp.single 0 a) (r * h) = constantCoeff r * coeff (Finsupp.single 0 a) h := by
  obtain ⟨h', rfl⟩ := hd
  rw [mul_left_comm, coeff_X_zero_pow_mul, coeff_X_zero_pow_mul, map_mul]

theorem coeff_X_zero_pow_mul_X_one (a : ℕ) :
    coeff (Finsupp.single 0 a + Finsupp.single 1 1)
      (X 0 ^ a * X 1 : MvPowerSeries (Fin 2) K) = 1 := by
  rw [coeff_add_X_zero_pow_mul, coeff_X, if_pos rfl]

theorem isUnit_of_isUnit_coe {r : cyclicInvariants K m q}
    (hr : IsUnit (r : MvPowerSeries (Fin 2) K)) : IsUnit r := by
  obtain ⟨s, hs⟩ := hr.exists_right_inv
  have hsR : s ∈ cyclicInvariants K m q := by
    rw [mem_cyclicInvariants_iff]
    intro ζ
    have h1 := congrArg (rescale (cyclicWeights K m q ζ)) hs
    rw [map_mul, map_one, (mem_cyclicInvariants_iff _ _ _ _).1 r.2 ζ] at h1
    have h2 : (r : MvPowerSeries (Fin 2) K) ≠ 0 := by
      rintro h0; rw [h0, zero_mul] at hs; exact zero_ne_one hs
    exact mul_left_cancel₀ h2 (h1.trans hs.symm)
  exact IsUnit.of_mul_eq_one (⟨s, hsR⟩ : cyclicInvariants K m q) (Subtype.ext hs)

theorem constantCoeff_eq_zero_of_mem_maximalIdeal [IsLocalRing (cyclicInvariants K m q)]
    {r : cyclicInvariants K m q} (hr : r ∈ IsLocalRing.maximalIdeal (cyclicInvariants K m q)) :
    constantCoeff (r : MvPowerSeries (Fin 2) K) = 0 := by
  by_contra h
  exact (IsLocalRing.mem_maximalIdeal _).1 hr
    (isUnit_of_isUnit_coe ((isUnit_iff_constantCoeff).2 (isUnit_iff_ne_zero.2 h)))

theorem mem_maximalIdeal_of_constantCoeff_eq_zero [IsLocalRing (cyclicInvariants K m q)]
    {r : cyclicInvariants K m q} (hr : constantCoeff (r : MvPowerSeries (Fin 2) K) = 0) :
    r ∈ IsLocalRing.maximalIdeal (cyclicInvariants K m q) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := (isUnit_iff_constantCoeff).1 (hu.map (cyclicInvariants K m q).subtype)
  rw [show (cyclicInvariants K m q).subtype r = (r : MvPowerSeries (Fin 2) K) from rfl, hr] at this
  exact not_isUnit_zero this

end CyclicChart

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- On `Spec R'` for a Noetherian normal domain `R'`, an element of `R'` has positive order along a
prime divisor `Z` exactly when it lies in the prime ideal of `Z`. -/
theorem pos_ord_iff_mem_asIdeal (R' : Type v) [CommRing R'] [IsDomain R'] [IsNoetherianRing R']
    [IsIntegrallyClosed R'] (Z : MMP.Mori.PrimeDivisor (Spec (CommRingCat.of R')))
    (y : Spec (CommRingCat.of R')) (hy : Z.genericPoint ⤳ y) {r : R'} (hr : r ≠ 0) :
    letI : Algebra R' ((Spec (CommRingCat.of R')).presheaf.stalk y) :=
      StructureSheaf.stalkAlgebra R' y
    (0 < (Spec (CommRingCat.of R')).ord (algebraMap _ (Spec (CommRingCat.of R')).functionField
      (algebraMap R' ((Spec (CommRingCat.of R')).presheaf.stalk y) r)) Z.genericPoint ↔
      r ∈ (Z.genericPoint : PrimeSpectrum R').asIdeal) := by
  haveI : IsNormal (Spec (CommRingCat.of R')) := isNormal_spec_of_isIntegrallyClosed R'
  letI : Algebra R' ((Spec (CommRingCat.of R')).presheaf.stalk y) :=
    StructureSheaf.stalkAlgebra R' y
  letI : Algebra R' ((Spec (CommRingCat.of R')).presheaf.stalk Z.genericPoint) :=
    StructureSheaf.stalkAlgebra R' Z.genericPoint
  haveI : (Z.genericPoint : PrimeSpectrum R').asIdeal.IsPrime := PrimeSpectrum.isPrime _
  haveI hloc : IsLocalization.AtPrime ((Spec (CommRingCat.of R')).presheaf.stalk Z.genericPoint)
      (Z.genericPoint : PrimeSpectrum R').asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R' Z.genericPoint
  have hsp : ((Spec (CommRingCat.of R')).presheaf.stalkSpecializes hy).hom
      (algebraMap R' ((Spec (CommRingCat.of R')).presheaf.stalk y) r) =
      algebraMap R' ((Spec (CommRingCat.of R')).presheaf.stalk Z.genericPoint) r :=
    congrArg (fun φ => φ.hom r) (StructureSheaf.toStalk_stalkSpecializes (R := R') hy)
  rw [← MMP.Mori.algebraMap_stalkSpecializes hy, hsp]
  have hb : algebraMap R' ((Spec (CommRingCat.of R')).presheaf.stalk Z.genericPoint) r ≠ 0 := by
    intro h0
    exact hr (IsLocalization.injective ((Spec (CommRingCat.of R')).presheaf.stalk Z.genericPoint)
      (Ideal.primeCompl_le_nonZeroDivisors (Z.genericPoint : PrimeSpectrum R').asIdeal)
      (h0.trans (map_zero _).symm))
  have hbK : algebraMap _ (Spec (CommRingCat.of R')).functionField
      (algebraMap R' ((Spec (CommRingCat.of R')).presheaf.stalk Z.genericPoint) r) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hb
  have h1 := MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff Z
    (algebraMap R' ((Spec (CommRingCat.of R')).presheaf.stalk Z.genericPoint) r)
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord Z hbK, ← WithZero.exp_zero,
    WithZero.exp_lt_exp, neg_lt_zero] at h1
  rw [h1]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ r

end

section

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **Elements of the completion divisible by a power of the prime of `B` lie in the extended
symbolic power.** Let `φ : 𝒪_{X,x} → R'` be flat local into a Noetherian normal local domain, with
the extension `D'` of the prime of `B` prime and nonzero. If `z^M u = φ(π)^{cM} r` with `u ∉ D'`,
then `z` lies in the extension of `{a | ord_B a ≥ c}`. -/
theorem mem_map_ordIdeal_of_pow_mul_eq (x : X) (R' : Type v) [CommRing R'] [IsDomain R']
    [IsLocalRing R'] [IsNoetherianRing R'] [IsIntegrallyClosed R']
    (φ : X.presheaf.stalk x →+* R') (hφ : φ.Flat) [IsLocalHom φ]
    (B : MMP.Mori.PrimeDivisor X) (hxB : x ∈ B.support)
    {π : X.presheaf.stalk x} (hπ : π ≠ 0)
    (hπ1 : X.ord (algebraMap _ X.functionField π) B.genericPoint = 1)
    (hD : ((ordIdeal B 1 hxB).map φ).IsPrime) (hD0 : (ordIdeal B 1 hxB).map φ ≠ ⊥)
    {c M : ℕ} (hM : 0 < M) {z u r : R'} (hz : z ≠ 0) (hu : u ∉ (ordIdeal B 1 hxB).map φ)
    (h : z ^ M * u = φ π ^ (c * M) * r) :
    z ∈ (ordIdeal B c hxB).map φ := by
  classical
  haveI : IsNormal (Spec (CommRingCat.of R')) := isNormal_spec_of_isIntegrallyClosed R'
  set y0 : Spec (CommRingCat.of R') := IsLocalRing.closedPoint R'
  have hy0 : ∀ Z : MMP.Mori.PrimeDivisor (Spec (CommRingCat.of R')), y0 ∈ Z.support := fun Z =>
    (IsLocalRing.specializes_closedPoint (R := R') Z.genericPoint).mem_closed
      (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure)
      (MMP.Flips.primeDivisor_genericPoint_mem_support Z)
  letI : Algebra R' ((Spec (CommRingCat.of R')).presheaf.stalk y0) :=
    StructureSheaf.stalkAlgebra R' y0
  haveI hloc : IsLocalization.AtPrime ((Spec (CommRingCat.of R')).presheaf.stalk y0)
      (IsLocalRing.maximalIdeal R') :=
    StructureSheaf.IsLocalization.to_stalk R' y0
  have hflat2 : (algebraMap R' ((Spec (CommRingCat.of R')).presheaf.stalk y0)).Flat := by
    rw [RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat _ (IsLocalRing.maximalIdeal R').primeCompl
  haveI hlh2 : IsLocalHom (algebraMap R' ((Spec (CommRingCat.of R')).presheaf.stalk y0)) := by
    refine ⟨fun r hr => ?_⟩
    have := (IsLocalization.AtPrime.isUnit_to_map_iff
      ((Spec (CommRingCat.of R')).presheaf.stalk y0) (IsLocalRing.maximalIdeal R') r).1 hr
    by_contra hn
    exact this ((IsLocalRing.mem_maximalIdeal _).2 hn)
  haveI : Module.Flat R' ((Spec (CommRingCat.of R')).presheaf.stalk y0) := by
    rwa [← RingHom.flat_algebraMap_iff]
  haveI : Module.FaithfullyFlat R' ((Spec (CommRingCat.of R')).presheaf.stalk y0) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  set ι := algebraMap R' ((Spec (CommRingCat.of R')).presheaf.stalk y0)
  set ψ : X.presheaf.stalk x →+* (Spec (CommRingCat.of R')).presheaf.stalk y0 := ι.comp φ
  letI : Algebra (X.presheaf.stalk x) ((Spec (CommRingCat.of R')).presheaf.stalk y0) := ψ.toAlgebra
  haveI : Module.Flat (X.presheaf.stalk x) ((Spec (CommRingCat.of R')).presheaf.stalk y0) := by
    have : ψ.Flat := hφ.comp hflat2
    exact this
  haveI : IsLocalHom (algebraMap (X.presheaf.stalk x)
      ((Spec (CommRingCat.of R')).presheaf.stalk y0)) := by
    change IsLocalHom (ι.comp φ)
    infer_instance
  haveI : Module.FaithfullyFlat (X.presheaf.stalk x)
      ((Spec (CommRingCat.of R')).presheaf.stalk y0) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinjA : Function.Injective (algebraMap (X.presheaf.stalk x)
      ((Spec (CommRingCat.of R')).presheaf.stalk y0)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hinjι : Function.Injective ι := FaithfulSMul.algebraMap_injective _ _
  have hinjφ : Function.Injective φ := fun a b hab => hinjA (by
    change ι (φ a) = ι (φ b); rw [hab])
  have injA := IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  set vB : X.presheaf.stalk x → ℕ :=
    fun a => (X.ord (algebraMap _ X.functionField a) B.genericPoint).toNat
  have hvBmul : ∀ a b : X.presheaf.stalk x, a ≠ 0 → b ≠ 0 → vB (a * b) = vB a + vB b := by
    intro a b ha hb
    simp only [vB]
    rw [map_mul, Scheme.ord_mul ((map_ne_zero_iff _ injA).2 ha) ((map_ne_zero_iff _ injA).2 hb)]
    exact Int.toNat_add (ord_nonneg_of_mem_support B hxB a) (ord_nonneg_of_mem_support B hxB b)
  have hvBπ : vB π = 1 := by simp only [vB, hπ1]; rfl
  have hfact : ∀ a : X.presheaf.stalk x, a ≠ 0 → ∃ s b : X.presheaf.stalk x, s ≠ 0 ∧ b ≠ 0 ∧
      vB s = 0 ∧ vB b = 0 ∧ s * a = π ^ vB a * b := by
    intro a ha
    obtain ⟨s, b, hs, hb, hs0, hb0, h⟩ := exists_mul_eq_pow_mul B hxB hπ hπ1 ha
    exact ⟨s, b, hs, hb, by simp [vB, hs0], by simp [vB, hb0], h⟩
  have hJ1 : ∀ a, a ∈ ordIdeal B 1 hxB ↔ a = 0 ∨ 1 ≤ vB a := mem_ordIdeal_iff B hxB 1
  have hJ : ∀ a, a ∈ ordIdeal B c hxB ↔ a = 0 ∨ c ≤ vB a := mem_ordIdeal_iff B hxB c
  -- along a component over `B`, `u` has order zero
  have hu0 : ∀ Z : MMP.Mori.PrimeDivisor (Spec (CommRingCat.of R')), (∀ a : X.presheaf.stalk x, a ≠ 0 →
      (0 < (Spec (CommRingCat.of R')).ord (algebraMap _ (Spec (CommRingCat.of R')).functionField
        (algebraMap (X.presheaf.stalk x) ((Spec (CommRingCat.of R')).presheaf.stalk y0) a)) Z.genericPoint ↔
        0 < vB a)) →
      (Spec (CommRingCat.of R')).ord (algebraMap _ (Spec (CommRingCat.of R')).functionField (ι u)) Z.genericPoint = 0 := by
    intro Z hO
    haveI : (Z.genericPoint : PrimeSpectrum R').asIdeal.IsPrime := PrimeSpectrum.isPrime _
    have hle : (ordIdeal B 1 hxB).map φ ≤ (Z.genericPoint : PrimeSpectrum R').asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rcases (hJ1 a).1 ha with rfl | ha1
      · rw [Ideal.mem_comap, map_zero]; exact zero_mem _
      by_cases ha0 : a = 0
      · rw [ha0, Ideal.mem_comap, map_zero]; exact zero_mem _
      rw [Ideal.mem_comap]
      have := (hO a ha0).2 (by omega)
      exact (pos_ord_iff_mem_asIdeal R' Z y0 (IsLocalRing.specializes_closedPoint (R := R') Z.genericPoint)
        (fun h0 => ha0 (hinjφ (h0.trans (map_zero _).symm)))).1 this
    have hht : ((Z.genericPoint : PrimeSpectrum R').asIdeal).height = 1 := by
      letI : Algebra R' ((Spec (CommRingCat.of R')).presheaf.stalk Z.genericPoint) :=
        StructureSheaf.stalkAlgebra R' Z.genericPoint
      haveI hlocZ : IsLocalization.AtPrime ((Spec (CommRingCat.of R')).presheaf.stalk Z.genericPoint)
          (Z.genericPoint : PrimeSpectrum R').asIdeal :=
        StructureSheaf.IsLocalization.to_stalk R' Z.genericPoint
      have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height
        (Z.genericPoint : PrimeSpectrum R').asIdeal ((Spec (CommRingCat.of R')).presheaf.stalk Z.genericPoint)
      rw [ringKrullDim_stalk_eq_coheight, Z.coheight_genericPoint] at h1
      exact_mod_cast h1.symm
    have heq : (ordIdeal B 1 hxB).map φ = (Z.genericPoint : PrimeSpectrum R').asIdeal := by
      by_contra hne
      have hlt := lt_of_le_of_ne hle hne
      haveI : ((Z.genericPoint : PrimeSpectrum R').asIdeal).FiniteHeight :=
        (Ideal.finiteHeight_iff _).2 (Or.inr (by rw [hht]; exact ENat.one_ne_top))
      have h2 := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
      rw [hht] at h2
      have h3 : ((ordIdeal B 1 hxB).map φ).height = 0 := ENat.lt_one_iff_eq_zero.1 h2
      exact hD0 (Ideal.height_eq_zero_iff_eq_bot.1 h3)
    have hu' : u ∉ (Z.genericPoint : PrimeSpectrum R').asIdeal := heq ▸ hu
    have hu0' : u ≠ 0 := fun h => hu (h ▸ zero_mem _)
    have h4 : ¬ (0 < (Spec (CommRingCat.of R')).ord (algebraMap _
        (Spec (CommRingCat.of R')).functionField (ι u)) Z.genericPoint) :=
      (pos_ord_iff_mem_asIdeal R' Z y0 (IsLocalRing.specializes_closedPoint (R := R')
        Z.genericPoint) hu0').not.2 hu'
    have h5 := ord_nonneg_of_mem_support Z (hy0 Z) (ι u)
    omega
  have hιz : ι z ≠ 0 := fun h0 => hz (hinjι (h0.trans (map_zero _).symm))
  have hu0' : u ≠ 0 := fun h => hu (h ▸ zero_mem _)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact mul_ne_zero (pow_ne_zero _ hz) hu0' h
  have hπ0 : φ π ≠ 0 := fun h0 => hπ (hinjφ (h0.trans (map_zero _).symm))
  have hKne : ∀ w : R', w ≠ 0 → algebraMap _ (Spec (CommRingCat.of R')).functionField (ι w) ≠ 0 :=
    fun w hw => (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
      (fun h0 => hw (hinjι (h0.trans (map_zero _).symm)))
  have hz' : ∀ Z : MMP.Mori.PrimeDivisor (Spec (CommRingCat.of R')), (∀ a : X.presheaf.stalk x,
      a ≠ 0 → (0 < (Spec (CommRingCat.of R')).ord (algebraMap _
        (Spec (CommRingCat.of R')).functionField
        (algebraMap (X.presheaf.stalk x) ((Spec (CommRingCat.of R')).presheaf.stalk y0) a))
        Z.genericPoint ↔ 0 < vB a)) →
      (c : ℤ) * (Spec (CommRingCat.of R')).ord (algebraMap _
        (Spec (CommRingCat.of R')).functionField
        (algebraMap (X.presheaf.stalk x) ((Spec (CommRingCat.of R')).presheaf.stalk y0) π))
        Z.genericPoint ≤ (Spec (CommRingCat.of R')).ord (algebraMap _
        (Spec (CommRingCat.of R')).functionField (ι z)) Z.genericPoint := by
    intro Z hO
    have hu := hu0 Z hO
    have e := congrArg (fun w => (Spec (CommRingCat.of R')).ord
      (algebraMap _ (Spec (CommRingCat.of R')).functionField (ι w)) Z.genericPoint) h
    simp only [map_mul, map_pow] at e
    rw [Scheme.ord_mul (pow_ne_zero _ (hKne z hz)) (hKne u hu0'),
      Scheme.ord_mul (pow_ne_zero _ (hKne _ hπ0)) (hKne r hr0), Aux.ord_pow' (hKne z hz),
      Aux.ord_pow' (hKne _ hπ0), hu] at e
    have h1 := ord_nonneg_of_mem_support Z (hy0 Z) (ι r)
    have hM' : (0 : ℤ) < M := by exact_mod_cast hM
    change (c : ℤ) * (Spec (CommRingCat.of R')).ord (algebraMap _
      (Spec (CommRingCat.of R')).functionField (ι (φ π))) Z.genericPoint ≤ _
    push_cast at e
    nlinarith
  have hstalk := mem_map_of_ord_le (A := X.presheaf.stalk x)
    (R := (Spec (CommRingCat.of R')).presheaf.stalk y0)
    (K := (Spec (CommRingCat.of R')).functionField)
    (fun (Z : MMP.Mori.PrimeDivisor (Spec (CommRingCat.of R'))) w =>
      (Spec (CommRingCat.of R')).ord w Z.genericPoint)
    (fun Z _ _ hx hy => Scheme.ord_mul hx hy)
    (fun Z r _ => ord_nonneg_of_mem_support Z (hy0 Z) r)
    (fun w hw h => MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg y0 hw
      fun Γ _ => h Γ)
    (fun _ _ => finite_ord_ne_zero)
    (fun a ha h0 => ha (hinjA (h0.trans (map_zero _).symm)))
    vB hvBmul π hπ hvBπ hfact
    (fun J s hs c hc => mem_map_of_algebraMap_mul_mem_map J hs hc) c (ordIdeal B c hxB) hJ (ι z)
    hιz hz'
  have hmap : (ordIdeal B c hxB).map (algebraMap (X.presheaf.stalk x)
      ((Spec (CommRingCat.of R')).presheaf.stalk y0)) = ((ordIdeal B c hxB).map φ).map ι := by
    rw [Ideal.map_map]; rfl
  rw [hmap] at hstalk
  have := Ideal.comap_map_eq_self_of_faithfullyFlat ((ordIdeal B c hxB).map φ)
    (B := (Spec (CommRingCat.of R')).presheaf.stalk y0)
  rw [← this]
  exact hstalk

end

section

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- An element of the local ring at the generic point of a prime divisor lies in the maximal
ideal exactly when it is zero or has positive order. -/
theorem mem_maximalIdeal_iff_ord (P : MMP.Mori.PrimeDivisor X) {y : X} (hy : y = P.genericPoint)
    (b : X.presheaf.stalk y) :
    b ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) ↔
      b = 0 ∨ 1 ≤ (X.ord (algebraMap _ X.functionField b) P.genericPoint).toNat := by
  subst hy
  by_cases hb : b = 0
  · simp [hb]
  have hbK : algebraMap _ X.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hb
  have h1 := MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff P b
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord P hbK, ← WithZero.exp_zero,
    WithZero.exp_lt_exp, neg_lt_zero] at h1
  rw [← h1]
  simp only [hb, false_or]
  omega

/-- The ideal of `S` in `𝒪_{X,x}`, for `x` a point of `S = j(T)` and `P` the prime divisor
`S`, is the ideal of elements of positive order along `P`. -/
theorem ker_stalkMap_eq_ordIdeal {T : Scheme.{u}} (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T]
    (P : MMP.Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (w : T) (hxP : j.base w ∈ P.support) :
    RingHom.ker (j.stalkMap w).hom = ordIdeal P 1 hxP := by
  ext a
  rw [RingHom.mem_ker, mem_ordIdeal_iff]
  have hy := Aux.map_genericPoint_eq j P hP
  have hTw : genericPoint T ⤳ w := (genericPoint_spec T).specializes trivial
  have hζ : j (genericPoint T) ⤳ j w := hTw.map j.base.hom.continuous
  have key := Scheme.Hom.stalkSpecializes_stalkMap_apply j (genericPoint T) w hTw a
  letI : Field (T.presheaf.stalk (genericPoint T)) := inferInstanceAs (Field T.functionField)
  have hmax : RingHom.ker (j.stalkMap (genericPoint T)).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (j (genericPoint T))) :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective _ (j.stalkMap_surjective (genericPoint T)))
  have hinjT : Function.Injective (algebraMap (T.presheaf.stalk w) T.functionField) :=
    IsFractionRing.injective _ _
  constructor
  · intro h0
    have h1 : (j.stalkMap (genericPoint T)).hom ((X.presheaf.stalkSpecializes hζ).hom a) = 0 := by
      rw [key, h0, map_zero]
    have h2 := (mem_maximalIdeal_iff_ord P hy _).1 (hmax ▸ (RingHom.mem_ker.2 h1))
    rcases h2 with h2 | h2
    · left
      exact MMP.Intersection.stalkSpecializes_injective hζ (h2.trans (map_zero _).symm)
    · right
      rwa [MMP.Mori.algebraMap_stalkSpecializes hζ] at h2
  · intro h
    have h2 : (X.presheaf.stalkSpecializes hζ).hom a ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk (j (genericPoint T))) := by
      rw [mem_maximalIdeal_iff_ord P hy, MMP.Mori.algebraMap_stalkSpecializes hζ]
      rcases h with rfl | h
      · exact Or.inl (map_zero _)
      · exact Or.inr h
    rw [← hmax, RingHom.mem_ker, key] at h2
    exact hinjT (h2.trans (map_zero _).symm)

end

section

open MvPowerSeries

/-- The ring map `𝒪_{X,x} → R` to the formal cyclic chart is flat, local, injective, and extends
the maximal ideal to the maximal ideal. -/
theorem chart_map_facts_of_field {k : Type} [Field k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [LocallyOfFiniteType sX] (x : X)
    (κsep : Type) [Field κsep] [Algebra (ResidueField (X.presheaf.stalk x)) κsep]
    [IsSepClosure (ResidueField (X.presheaf.stalk x)) κsep]
    (H : Type) [CommRing H] [IsLocalRing H] [Algebra (X.presheaf.stalk x) H]
    [IsHenselization (X.presheaf.stalk x) κsep H]
    {K : Type*} [Field K] {m : ℕ} {q : ℤ} [IsLocalRing (cyclicInvariants K m q)]
    (e : AdicCompletion (maximalIdeal H) H ≃+* cyclicInvariants K m q) :
    let φ : X.presheaf.stalk x →+* cyclicInvariants K m q :=
      e.toRingHom.comp ((algebraMap H (AdicCompletion (maximalIdeal H) H)).comp
        (algebraMap (X.presheaf.stalk x) H))
    φ.Flat ∧ IsLocalHom φ ∧ (maximalIdeal (X.presheaf.stalk x)).map φ =
      maximalIdeal (cyclicInvariants K m q) ∧ Function.Injective φ := by
  intro φ
  letI := MMP.Mori.stalkAlgebra sX x
  haveI := essFiniteType_stalk' sX x
  haveI : IsIntegrallyClosed (X.presheaf.stalk x) := IsNormal.stalk_normal x
  obtain ⟨-, ⟨hlocAH, hffAH, hmAH⟩, hlocR, -, ⟨hlocHR, hffHR, hmHR⟩, -⟩ :=
    MMP.Foundations.isNoetherianRing_strictHenselization_adicCompletion k (X.presheaf.stalk x)
      κsep H
  have hφ : φ.Flat := by
    refine RingHom.Flat.comp (RingHom.Flat.comp ?_ ?_) (RingHom.Flat.of_bijective e.bijective)
    · rw [RingHom.flat_algebraMap_iff]; infer_instance
    · rw [RingHom.flat_algebraMap_iff]; infer_instance
  haveI : IsLocalHom e.toRingHom := ⟨fun a ha => by
    have := ha.map e.symm.toRingHom
    simpa using this⟩
  haveI : IsLocalHom ((algebraMap H (AdicCompletion (maximalIdeal H) H)).comp
      (algebraMap (X.presheaf.stalk x) H)) := @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ hlocHR hlocAH
  haveI hlφ : IsLocalHom φ := RingHom.isLocalHom_comp _ _
  have hmax : (maximalIdeal (X.presheaf.stalk x)).map φ = maximalIdeal (cyclicInvariants K m q) := by
    have h1 : (maximalIdeal (X.presheaf.stalk x)).map φ =
        ((maximalIdeal (AdicCompletion (maximalIdeal H) H))).map e.toRingHom := by
      simp only [φ, ← Ideal.map_map, hmAH, hmHR]
    rw [h1]
    haveI : (Ideal.map e.toRingHom (maximalIdeal (AdicCompletion (maximalIdeal H) H))).IsMaximal :=
      Ideal.map_isMaximal_of_equiv e
    exact IsLocalRing.eq_maximalIdeal this
  refine ⟨hφ, hlφ, hmax, ?_⟩
  letI : Algebra (X.presheaf.stalk x) (cyclicInvariants K m q) := φ.toAlgebra
  haveI : Module.Flat (X.presheaf.stalk x) (cyclicInvariants K m q) := hφ
  haveI : IsLocalHom (algebraMap (X.presheaf.stalk x) (cyclicInvariants K m q)) := hlφ
  haveI : Module.FaithfullyFlat (X.presheaf.stalk x) (cyclicInvariants K m q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective (X.presheaf.stalk x) (cyclicInvariants K m q)

end

section

open MvPowerSeries

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The prime of `P` in the cyclic chart: elements of `𝒪_{X,x}` of order zero along `P` map to
power series not divisible by `x`, a uniformizer `π` maps to `x γ` with `x ∤ γ`, and elements of
order `≥ c` map into `x^c K[[x, y]]`. -/
theorem chart_pi_facts {x : X} {K : Type*} [Field K] {m : ℕ} {q : ℤ} [IsLocalRing (cyclicInvariants K m q)]
    (hK : IsCyclicQuotientSetting K m q)
    (φ : X.presheaf.stalk x →+* cyclicInvariants K m q) (hφ : φ.Flat) [IsLocalHom φ]
    (P : MMP.Mori.PrimeDivisor X) (hxP : x ∈ P.support)
    (hD : (ordIdeal P 1 hxP).map φ =
      (Ideal.span {MvPowerSeries.X 0}).comap (cyclicInvariants K m q).subtype)
    {π : X.presheaf.stalk x} (hπ : π ≠ 0)
    (hπ1 : X.ord (algebraMap _ X.functionField π) P.genericPoint = 1) :
    (∀ s : X.presheaf.stalk x, s ≠ 0 →
      X.ord (algebraMap _ X.functionField s) P.genericPoint = 0 → ¬ MvPowerSeries.X 0 ∣ (φ s : MvPowerSeries (Fin 2) K)) ∧
    (∀ (c : ℕ) (a : X.presheaf.stalk x), a ∈ ordIdeal P c hxP →
      MvPowerSeries.X 0 ^ c ∣ (φ a : MvPowerSeries (Fin 2) K)) ∧
    ∃ γπ : MvPowerSeries (Fin 2) K, (φ π : MvPowerSeries (Fin 2) K) = MvPowerSeries.X 0 * γπ ∧ ¬ MvPowerSeries.X 0 ∣ γπ := by
  classical
  letI : Algebra (X.presheaf.stalk x) (cyclicInvariants K m q) := φ.toAlgebra
  haveI : Module.Flat (X.presheaf.stalk x) (cyclicInvariants K m q) := hφ
  haveI : IsLocalHom (algebraMap (X.presheaf.stalk x) (cyclicInvariants K m q)) := ‹_›
  haveI : Module.FaithfullyFlat (X.presheaf.stalk x) (cyclicInvariants K m q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have injA := IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  set vB : X.presheaf.stalk x → ℕ :=
    fun a => (X.ord (algebraMap _ X.functionField a) P.genericPoint).toNat
  have hJ1 : ∀ a, a ∈ ordIdeal P 1 hxP ↔ a = 0 ∨ 1 ≤ vB a := mem_ordIdeal_iff P hxP 1
  have hJ : ∀ c a, a ∈ ordIdeal P c hxP ↔ a = 0 ∨ c ≤ vB a := fun c => mem_ordIdeal_iff P hxP c
  have hmemD : ∀ r : cyclicInvariants K m q,
      r ∈ (Ideal.span {MvPowerSeries.X 0}).comap (cyclicInvariants K m q).subtype ↔
        MvPowerSeries.X 0 ∣ (r : MvPowerSeries (Fin 2) K) := fun r => by
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]; rfl
  -- order-zero elements
  have hS1 : ∀ s : X.presheaf.stalk x, s ≠ 0 →
      X.ord (algebraMap _ X.functionField s) P.genericPoint = 0 →
        ¬ MvPowerSeries.X 0 ∣ (φ s : MvPowerSeries (Fin 2) K) := by
    intro s hs hs0 hdvd
    have h1 : φ s ∈ (ordIdeal P 1 hxP).map φ := by rw [hD, hmemD]; exact hdvd
    have h2 : s ∈ ordIdeal P 1 hxP := by
      rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (ordIdeal P 1 hxP)
        (B := cyclicInvariants K m q)]
      exact h1
    rcases (hJ1 s).1 h2 with h | h
    · exact hs h
    · simp only [vB, hs0] at h; omega
  -- `π ↦ x γ`
  have hπD : MvPowerSeries.X 0 ∣ (φ π : MvPowerSeries (Fin 2) K) := by
    rw [← hmemD, ← hD]
    exact Ideal.mem_map_of_mem _ ((hJ1 π).2 (Or.inr (by simp [vB, hπ1])))
  obtain ⟨γπ, hγπ⟩ := hπD
  -- elements of order `≥ c`
  have hS2 : ∀ (c : ℕ) (a : X.presheaf.stalk x), a ∈ ordIdeal P c hxP →
      MvPowerSeries.X 0 ^ c ∣ (φ a : MvPowerSeries (Fin 2) K) := by
    intro c a ha
    rcases (hJ c a).1 ha with rfl | hca
    · rw [map_zero]; exact dvd_zero _
    by_cases ha0 : a = 0
    · rw [ha0, map_zero]; exact dvd_zero _
    obtain ⟨s, b, hs, hb, hs0, -, hsab⟩ := exists_mul_eq_pow_mul P hxP hπ hπ1 ha0
    have e := congrArg (fun z => (φ z : MvPowerSeries (Fin 2) K)) hsab
    simp only [map_mul, map_pow, Subring.coe_mul, SubmonoidClass.coe_pow, hγπ] at e
    refine (pow_dvd_pow _ hca).trans (CyclicChart.X_zero_pow_dvd_of_dvd_mul (hS1 s hs hs0) ?_)
    rw [e, mul_pow]
    exact (dvd_mul_right _ _).mul_right _
  refine ⟨hS1, hS2, γπ, hγπ, fun hdvd => ?_⟩
  -- otherwise all of `D` would lie in `x² K[[x,y]]`
  have hD2 : ∀ r ∈ (ordIdeal P 1 hxP).map φ, MvPowerSeries.X 0 ^ 2 ∣ (r : MvPowerSeries (Fin 2) K) := by
    intro r hr
    refine Submodule.span_induction (fun r hr => ?_) (by simp) (fun r r' _ _ h h' => ?_)
      (fun c r _ h => ?_) hr
    · obtain ⟨a, ha, rfl⟩ := hr
      rcases (hJ1 a).1 ha with rfl | ha1
      · simp
      by_cases ha0 : a = 0
      · simp [ha0]
      obtain ⟨s, b, hs, hb, hs0, -, hsab⟩ := exists_mul_eq_pow_mul P hxP hπ hπ1 ha0
      have e := congrArg (fun z => (φ z : MvPowerSeries (Fin 2) K)) hsab
      simp only [map_mul, map_pow, Subring.coe_mul, SubmonoidClass.coe_pow, hγπ] at e
      refine CyclicChart.X_zero_pow_dvd_of_dvd_mul (hS1 s hs hs0) ?_
      rw [e]
      obtain ⟨k, hk⟩ : ∃ k, vB a = k + 1 := ⟨vB a - 1, by omega⟩
      have hk' : (X.ord (algebraMap _ X.functionField a) P.genericPoint).toNat = k + 1 := hk
      rw [hk']
      obtain ⟨δ, hδ⟩ := hdvd
      rw [hδ]
      exact ⟨δ * (MvPowerSeries.X 0 * (MvPowerSeries.X 0 * δ)) ^ k *
        (φ b : MvPowerSeries (Fin 2) K), by ring⟩
    · simpa using dvd_add h h'
    · simpa [Subring.coe_mul, smul_eq_mul] using h.mul_left (c : MvPowerSeries (Fin 2) K)
  -- the invariant `x y^b`
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (m : ℤ) ∣ 1 + q * b := by
    have hg := hK.gcd_eq_one
    obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, q * u + m * v = 1 := by
      have := Int.gcd_eq_gcd_ab q m
      rw [hg] at this
      exact ⟨Int.gcdA q m, Int.gcdB q m, by push_cast at this; linarith⟩
    have hm : (0 : ℤ) < m := by exact_mod_cast hK.one_le
    refine ⟨((-u) % m).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm.ne')]
    have hc := Int.mul_ediv_add_emod (-u) m
    refine ⟨v - q * ((-u) / m), ?_⟩
    have : (-u) % m = -u - m * ((-u) / m) := by linarith
    rw [this]; linear_combination (-1 : ℤ) * huv
  have hmem : (MvPowerSeries.X 0 ^ 1 * MvPowerSeries.X 1 ^ b : MvPowerSeries (Fin 2) K) ∈ cyclicInvariants K m q :=
    CyclicChart.X_pow_mul_X_pow_mem_cyclicInvariants (by simpa using hb)
  have hD' : (⟨_, hmem⟩ : cyclicInvariants K m q) ∈ (ordIdeal P 1 hxP).map φ := by
    rw [hD, hmemD]; exact ⟨MvPowerSeries.X 1 ^ b, by ring⟩
  have h2 : MvPowerSeries.X 0 ^ 2 ∣ (MvPowerSeries.X 0 ^ 1 * MvPowerSeries.X 1 ^ b :
      MvPowerSeries (Fin 2) K) := hD2 _ hD'
  rw [MvPowerSeries.X_pow_dvd_iff] at h2
  have := h2 (Finsupp.single 0 1 + Finsupp.single 1 b) (by simp)
  rw [pow_one, X_def, X_pow_eq, monomial_mul_monomial, one_mul, coeff_monomial_same] at this
  exact one_ne_zero this

end

section

open MvPowerSeries

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The extension `D` of the prime of `P` is a nonzero prime, and `γπ^m` is an invariant not in
it. -/
theorem chart_D_facts {x : X} {K : Type*} [Field K] {m : ℕ} {q : ℤ}
    (hK : IsCyclicQuotientSetting K m q)
    (φ : X.presheaf.stalk x →+* cyclicInvariants K m q)
    (P : MMP.Mori.PrimeDivisor X) (hxP : x ∈ P.support)
    (hD : (ordIdeal P 1 hxP).map φ =
      (Ideal.span {MvPowerSeries.X 0}).comap (cyclicInvariants K m q).subtype)
    {π : X.presheaf.stalk x} {γπ : MvPowerSeries (Fin 2) K}
    (hγπ : (φ π : MvPowerSeries (Fin 2) K) = MvPowerSeries.X 0 * γπ)
    (hγπX : ¬ MvPowerSeries.X 0 ∣ γπ) :
    ((ordIdeal P 1 hxP).map φ).IsPrime ∧ (ordIdeal P 1 hxP).map φ ≠ ⊥ ∧
      ∃ hγR : γπ ^ m ∈ cyclicInvariants K m q,
        (⟨_, hγR⟩ : cyclicInvariants K m q) ∉ (ordIdeal P 1 hxP).map φ ∧
        (∀ r : cyclicInvariants K m q, r ∈ (ordIdeal P 1 hxP).map φ ↔
          MvPowerSeries.X 0 ∣ (r : MvPowerSeries (Fin 2) K)) := by
  have hm := hK.one_le
  have hXmR : (MvPowerSeries.X 0 ^ m : MvPowerSeries (Fin 2) K) ∈ cyclicInvariants K m q := by
    have := CyclicChart.X_pow_mul_X_pow_mem_cyclicInvariants (K := K) (m := m) (q := q)
      (i := m) (j := 0) (by simp)
    simpa using this
  have hXm0 : (MvPowerSeries.X 0 ^ m : MvPowerSeries (Fin 2) K) ≠ 0 :=
    pow_ne_zero _ CyclicChart.prime_X_zero.ne_zero
  have hmemD : ∀ r : cyclicInvariants K m q,
      r ∈ (ordIdeal P 1 hxP).map φ ↔ MvPowerSeries.X 0 ∣ (r : MvPowerSeries (Fin 2) K) :=
    fun r => by rw [hD, Ideal.mem_comap, Ideal.mem_span_singleton]; rfl
  haveI : (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)}).IsPrime :=
    (Ideal.span_singleton_prime CyclicChart.prime_X_zero.ne_zero).2 CyclicChart.prime_X_zero
  have hDprime : ((ordIdeal P 1 hxP).map φ).IsPrime := by rw [hD]; infer_instance
  have hD0 : (ordIdeal P 1 hxP).map φ ≠ ⊥ := by
    intro h
    have : (⟨_, hXmR⟩ : cyclicInvariants K m q) ∈ (ordIdeal P 1 hxP).map φ := by
      rw [hmemD]; exact dvd_pow_self _ (by omega)
    rw [h, Ideal.mem_bot] at this
    exact hXm0 (congrArg Subtype.val this)
  have hγR : γπ ^ m ∈ cyclicInvariants K m q := by
    refine CyclicChart.mem_cyclicInvariants_of_mul_mem hXmR hXm0 ?_
    rw [← mul_pow, ← hγπ]
    exact (φ π ^ m).2
  refine ⟨hDprime, hD0, hγR, ?_, hmemD⟩
  rw [hmemD]
  exact fun h => hγπX (CyclicChart.prime_X_zero.dvd_of_dvd_pow h)

end

section

open MvPowerSeries

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **The local equation of `mS` in the chart.** If `f` has order `m` along `P` and order zero
along the other prime divisors through `x`, its image in the chart is `(w x)^m` for an invariant
unit `w`. -/
theorem chart_unit_root {x : X} {K : Type*} [Field K] {m : ℕ} {q : ℤ}
    [IsLocalRing (cyclicInvariants K m q)] [IsNoetherianRing (cyclicInvariants K m q)]
    [IsDomain (cyclicInvariants K m q)] [IsIntegrallyClosed (cyclicInvariants K m q)]
    (hK : IsCyclicQuotientSetting K m q)
    (φ : X.presheaf.stalk x →+* cyclicInvariants K m q) (hφ : φ.Flat) [IsLocalHom φ]
    (P : MMP.Mori.PrimeDivisor X) (hxP : x ∈ P.support)
    (hD : (ordIdeal P 1 hxP).map φ =
      (Ideal.span {MvPowerSeries.X 0}).comap (cyclicInvariants K m q).subtype)
    {f : X.presheaf.stalk x} (hf0 : f ≠ 0)
    (hfP : X.ord (algebraMap _ X.functionField f) P.genericPoint = m)
    (hfE : ∀ E : MMP.Mori.PrimeDivisor X, x ∈ E.support → E ≠ P →
      X.ord (algebraMap _ X.functionField f) E.genericPoint = 0) :
    ∃ w : MvPowerSeries (Fin 2) K, w ∈ cyclicInvariants K m q ∧ IsUnit w ∧
      (φ f : MvPowerSeries (Fin 2) K) = (w * MvPowerSeries.X 0) ^ m := by
  classical
  haveI := hK.isAlgClosed
  haveI := hK.charZero
  have hm := hK.one_le
  obtain ⟨π, hπ, hπ1⟩ := exists_ord_eq_one_stalk P hxP
  obtain ⟨hS1, hS2, γπ, hγπ, hγπX⟩ := chart_pi_facts hK φ hφ P hxP hD hπ hπ1
  have injA := IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  -- `{ord_P ≥ m} = (f)`
  have hJm : ordIdeal P m hxP = Ideal.span {f} := by
    apply le_antisymm
    · intro a ha
      rcases (mem_ordIdeal_iff P hxP m a).1 ha with rfl | ham
      · exact zero_mem _
      by_cases ha0 : a = 0
      · rw [ha0]; exact zero_mem _
      have haK : algebraMap _ X.functionField a ≠ 0 := (map_ne_zero_iff _ injA).2 ha0
      have hfK : algebraMap _ X.functionField f ≠ 0 := (map_ne_zero_iff _ injA).2 hf0
      obtain ⟨b, hb⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
        x (mul_ne_zero haK (inv_ne_zero hfK)) fun Γ hΓ => by
          have hinv : X.ord (algebraMap _ X.functionField f)⁻¹ Γ.genericPoint =
              - X.ord (algebraMap _ X.functionField f) Γ.genericPoint := by
            have := Scheme.ord_mul (x := Γ.genericPoint) hfK (inv_ne_zero hfK)
            rw [mul_inv_cancel₀ hfK, Aux.ord_one'] at this; omega
          rw [Scheme.ord_mul haK (inv_ne_zero hfK), hinv]
          have hna := ord_nonneg_of_mem_support Γ hΓ a
          by_cases hΓP : Γ = P
          · subst hΓP
            rw [hfP]
            have : (m : ℤ) ≤ (X.ord (algebraMap _ X.functionField a) Γ.genericPoint).toNat := by
              exact_mod_cast ham
            rw [Int.toNat_of_nonneg hna] at this
            omega
          · rw [hfE Γ hΓ hΓP]; omega
      refine Ideal.mem_span_singleton'.2 ⟨b, injA ?_⟩
      rw [map_mul, hb, inv_mul_cancel_right₀ hfK]
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact (mem_ordIdeal_iff P hxP m f).2 (Or.inr (by rw [hfP]; simp))
  have hXmR : (MvPowerSeries.X 0 ^ m : MvPowerSeries (Fin 2) K) ∈ cyclicInvariants K m q := by
    have := CyclicChart.X_pow_mul_X_pow_mem_cyclicInvariants (K := K) (m := m) (q := q)
      (i := m) (j := 0) (by simp)
    simpa using this
  have hXm0 : (MvPowerSeries.X 0 ^ m : MvPowerSeries (Fin 2) K) ≠ 0 :=
    pow_ne_zero _ CyclicChart.prime_X_zero.ne_zero
  obtain ⟨hDprime, hD0, hγR, hu, -⟩ := chart_D_facts hK φ P hxP hD hγπ hγπX
  have hz := mem_map_ordIdeal_of_pow_mul_eq x (cyclicInvariants K m q) φ hφ P hxP hπ hπ1
    hDprime hD0 (c := m) (M := 1) one_pos (z := ⟨_, hXmR⟩) (u := ⟨_, hγR⟩) (r := 1)
    (fun h => hXm0 (congrArg Subtype.val h)) hu (by
      apply Subtype.ext
      simp only [pow_one, mul_one, Subring.coe_mul, SubmonoidClass.coe_pow, hγπ]
      ring)
  rw [hJm, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hz
  obtain ⟨r', hr'⟩ := hz
  have hr'' : r' * φ f = (MvPowerSeries.X 0 ^ m : MvPowerSeries (Fin 2) K) :=
    congrArg Subtype.val hr'
  obtain ⟨v, hv⟩ := hS2 m f ((mem_ordIdeal_iff P hxP m f).2 (Or.inr (by rw [hfP]; simp)))
  have hvR : v ∈ cyclicInvariants K m q :=
    CyclicChart.mem_cyclicInvariants_of_mul_mem hXmR hXm0 (hv ▸ (φ f).2)
  have hvu : IsUnit v := by
    refine IsUnit.of_mul_eq_one (r' : MvPowerSeries (Fin 2) K) ?_
    apply mul_left_cancel₀ hXm0
    rw [mul_one, ← mul_assoc, ← hv, mul_comm, hr'']
  obtain ⟨w, hw⟩ := CyclicChart.exists_pow_eq_of_isUnit (by omega : 0 < m) hvu
  have hwu : IsUnit w := (isUnit_pow_iff (by omega : m ≠ 0)).1 (hw ▸ hvu)
  refine ⟨w, CyclicChart.mem_cyclicInvariants_of_pow_eq (by omega) hwu (hw ▸ hvR), hwu, ?_⟩
  rw [hv, ← hw, mul_pow, mul_comm]

end

section

open MvPowerSeries

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A unit of the local ring at a point of a prime divisor has order zero along it. -/
theorem ord_eq_zero_of_isUnit_stalk (P : MMP.Mori.PrimeDivisor X) {x : X} (hxP : x ∈ P.support)
    {u : X.presheaf.stalk x} (hu : IsUnit u) :
    X.ord (algebraMap _ X.functionField u) P.genericPoint = 0 := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have injA := IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  have hu0 : u ≠ 0 := hu.ne_zero
  have hv0 : v ≠ 0 := right_ne_zero_of_mul_eq_one hv
  have h := Scheme.ord_mul (x := P.genericPoint) ((map_ne_zero_iff _ injA).2 hu0)
    ((map_ne_zero_iff _ injA).2 hv0)
  rw [← map_mul, hv, map_one, Aux.ord_one'] at h
  have h1 := ord_nonneg_of_mem_support P hxP u
  have h2 := ord_nonneg_of_mem_support P hxP v
  omega

/-- **The second coordinate in the chart.** There are `a ≡ -q (mod m)`, `0 ≤ a < m`, and
`g ∈ 𝔪_{X,x}` with `ord_P g ≥ a` whose image in the chart is `x^a γ` with `γ` vanishing at the
origin and with nonzero `y`-coefficient. -/
theorem chart_y_coordinate {x : X} {K : Type*} [Field K] {m : ℕ} {q : ℤ}
    [IsLocalRing (cyclicInvariants K m q)] [IsNoetherianRing (cyclicInvariants K m q)]
    [IsDomain (cyclicInvariants K m q)] [IsIntegrallyClosed (cyclicInvariants K m q)]
    (hK : IsCyclicQuotientSetting K m q)
    (φ : X.presheaf.stalk x →+* cyclicInvariants K m q) (hφ : φ.Flat) [IsLocalHom φ]
    (hmax : (maximalIdeal (X.presheaf.stalk x)).map φ = maximalIdeal (cyclicInvariants K m q))
    (P : MMP.Mori.PrimeDivisor X) (hxP : x ∈ P.support)
    (hD : (ordIdeal P 1 hxP).map φ =
      (Ideal.span {MvPowerSeries.X 0}).comap (cyclicInvariants K m q).subtype) :
    ∃ (a : ℕ) (g : X.presheaf.stalk x) (γ : MvPowerSeries (Fin 2) K), a < m ∧
      (m : ℤ) ∣ a + q ∧ g ∈ ordIdeal P a hxP ∧ g ∈ maximalIdeal (X.presheaf.stalk x) ∧
      (φ g : MvPowerSeries (Fin 2) K) = MvPowerSeries.X 0 ^ a * γ ∧ constantCoeff γ = 0 ∧
      coeff (Finsupp.single 1 1) γ ≠ 0 := by
  classical
  haveI := hK.isAlgClosed
  haveI := hK.charZero
  have hm := hK.one_le
  obtain ⟨π, hπ, hπ1⟩ := exists_ord_eq_one_stalk P hxP
  obtain ⟨hS1, hS2, γπ, hγπ, hγπX⟩ := chart_pi_facts hK φ hφ P hxP hD hπ hπ1
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  set a : ℕ := ((-q) % m).toNat with ha_def
  have ha : (a : ℤ) = (-q) % m := Int.toNat_of_nonneg (Int.emod_nonneg _ hmZ.ne')
  have ham : a < m := by
    have := Int.emod_lt_of_pos (-q) hmZ
    omega
  have haq : (m : ℤ) ∣ a + q := by
    rw [ha]
    have := Int.mul_ediv_add_emod (-q) m
    exact ⟨-((-q) / m), by linarith⟩
  -- the invariant `x^a y`
  have hzR : (MvPowerSeries.X 0 ^ a * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ∈
      cyclicInvariants K m q := by
    have := CyclicChart.X_pow_mul_X_pow_mem_cyclicInvariants (K := K) (i := a) (j := 1)
      (by simpa using haq)
    simpa using this
  set z : cyclicInvariants K m q := ⟨_, hzR⟩
  -- the coefficient of `x^a` of an invariant series in the maximal ideal vanishes
  have hc0 : ∀ h : MvPowerSeries (Fin 2) K, h ∈ cyclicInvariants K m q → constantCoeff h = 0 →
      coeff (Finsupp.single 0 a) h = 0 := by
    intro h hh hh0
    by_contra hne
    have := CyclicChart.dvd_of_coeff_ne_zero (by omega) hh hne
    have e0 : (Finsupp.single (0 : Fin 2) a) 0 = a := Finsupp.single_eq_same
    have e1 : (Finsupp.single (0 : Fin 2) a) 1 = 0 := Finsupp.single_eq_of_ne (by decide)
    rw [e0, e1, Nat.cast_zero, mul_zero, add_zero] at this
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · rw [h0, Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply] at hne
      exact hne hh0
    · exact absurd (Int.le_of_dvd (by exact_mod_cast hpos) this) (by push_cast; omega)
  -- the ideal `J`
  set J : Ideal (X.presheaf.stalk x) :=
    if m = 1 then maximalIdeal (X.presheaf.stalk x) else ordIdeal P a hxP with hJdef
  have hJsub : ∀ g ∈ J, g ∈ ordIdeal P a hxP ∧ g ∈ maximalIdeal (X.presheaf.stalk x) := by
    intro g hg
    by_cases h1 : m = 1
    · simp only [hJdef, if_pos h1] at hg
      have : a = 0 := by omega
      refine ⟨(mem_ordIdeal_iff P hxP a g).2 (Or.inr (by omega)), hg⟩
    · simp only [hJdef, if_neg h1] at hg
      refine ⟨hg, ?_⟩
      have ha1 : 1 ≤ a := by
        by_contra h0
        have : a = 0 := by omega
        rw [this] at haq
        have hg := hK.gcd_eq_one
        have hmq : (m : ℤ) ∣ q := by simpa using haq
        have h2 : (m : ℤ) ∣ (Int.gcd q m : ℤ) := Int.dvd_coe_gcd hmq (dvd_refl _)
        rw [hg] at h2
        exact h1 (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h2)
      rcases (mem_ordIdeal_iff P hxP a g).1 hg with rfl | hga
      · exact zero_mem _
      by_contra hu
      have := ord_eq_zero_of_isUnit_stalk P hxP ((IsLocalRing.mem_maximalIdeal _).not.1 hu |> not_not.1)
      simp only [this] at hga
      omega
  obtain ⟨hDprime, hD0, hγR, hγD, hmemD⟩ := chart_D_facts hK φ P hxP hD hγπ hγπX
  -- `z ∈ J R`
  have hzJ : z ∈ J.map φ := by
    by_cases h1 : m = 1
    · simp only [hJdef, if_pos h1]
      rw [hmax]
      apply CyclicChart.mem_maximalIdeal_of_constantCoeff_eq_zero
      change constantCoeff (MvPowerSeries.X 0 ^ a * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0
      simp
    · simp only [hJdef, if_neg h1]
      have hX1R : (MvPowerSeries.X 1 ^ m : MvPowerSeries (Fin 2) K) ∈ cyclicInvariants K m q := by
        have := CyclicChart.X_pow_mul_X_pow_mem_cyclicInvariants (K := K) (m := m) (q := q)
          (i := 0) (j := m) ⟨q, by push_cast; ring⟩
        simpa using this
      have hu : (⟨_, hγR⟩ : cyclicInvariants K m q) ^ a ∉ (ordIdeal P 1 hxP).map φ :=
        fun h => hγD (hDprime.mem_of_pow_mem _ h)
      refine mem_map_ordIdeal_of_pow_mul_eq x (cyclicInvariants K m q) φ hφ P hxP hπ hπ1
        hDprime hD0 (c := a) (M := m) (by omega) (z := z) (u := _) (r := ⟨_, hX1R⟩)
        (fun h => ?_) hu ?_
      · have := congrArg (fun r : cyclicInvariants K m q => (r : MvPowerSeries (Fin 2) K)) h
        simp only [z, ZeroMemClass.coe_zero] at this
        have hc := congrArg (coeff (Finsupp.single 0 a + Finsupp.single 1 1)) this
        rw [CyclicChart.coeff_X_zero_pow_mul_X_one, map_zero] at hc
        exact one_ne_zero hc
      · apply Subtype.ext
        simp only [z, Subring.coe_mul, SubmonoidClass.coe_pow, hγπ]
        ring
  -- the coefficient of `x^a y`
  set c := coeff (Finsupp.single (0 : Fin 2) a + Finsupp.single 1 1) (R := K) with hc_def
  have hgen : ∃ g ∈ J, c (φ g : MvPowerSeries (Fin 2) K) ≠ 0 := by
    by_contra hall
    push Not at hall
    have key : ∀ h ∈ J.map φ, MvPowerSeries.X 0 ^ a ∣ (h : MvPowerSeries (Fin 2) K) ∧
        coeff (Finsupp.single 0 a) (h : MvPowerSeries (Fin 2) K) = 0 ∧
        c (h : MvPowerSeries (Fin 2) K) = 0 := by
      intro h hh
      refine Submodule.span_induction (fun h hh => ?_) (by simp) (fun h h' _ _ ih ih' => ?_)
        (fun r h _ ih => ?_) hh
      · obtain ⟨g, hg, rfl⟩ := hh
        obtain ⟨hga, hgm⟩ := hJsub g hg
        refine ⟨hS2 a g hga, hc0 _ (φ g).2 ?_, hall g hg⟩
        exact CyclicChart.constantCoeff_eq_zero_of_mem_maximalIdeal (map_nonunit φ g hgm)
      · simp only [Subring.coe_add, map_add]
        exact ⟨dvd_add ih.1 ih'.1, by rw [ih.2.1, ih'.2.1, add_zero],
          by rw [ih.2.2, ih'.2.2, add_zero]⟩
      · simp only [smul_eq_mul, Subring.coe_mul]
        refine ⟨ih.1.mul_left _, ?_, ?_⟩
        · rw [CyclicChart.coeff_single_mul_of_X_pow_dvd ih.1, ih.2.1, mul_zero]
        · rw [hc_def, CyclicChart.coeff_mul_of_X_pow_dvd ih.1 ih.2.1, ← hc_def, ih.2.2, mul_zero]
    have := (key z hzJ).2.2
    simp only [hc_def, z] at this
    rw [CyclicChart.coeff_X_zero_pow_mul_X_one] at this
    exact one_ne_zero this
  obtain ⟨g, hgJ, hgc⟩ := hgen
  obtain ⟨hga, hgm⟩ := hJsub g hgJ
  obtain ⟨γ, hγ⟩ := hS2 a g hga
  refine ⟨a, g, γ, ham, haq, hga, hgm, hγ, ?_, ?_⟩
  · rw [← CyclicChart.coeff_X_zero_pow_mul, ← hγ]
    exact hc0 _ (φ g).2 (CyclicChart.constantCoeff_eq_zero_of_mem_maximalIdeal (map_nonunit φ g hgm))
  · rw [← CyclicChart.coeff_add_X_zero_pow_mul a, ← hγ]
    exact hgc

end

section CoverRing

open MvPowerSeries

/-- The Vandermonde property of the chart coordinate `x' = w x`: an `R`-linear relation among
`1, x', …, x'^{m-1}` is trivial. -/
theorem eq_zero_of_sum_mul_pow_eq_zero {K : Type*} [Field K] {m : ℕ} {q : ℤ}
    (hK : IsCyclicQuotientSetting K m q) {w : MvPowerSeries (Fin 2) K}
    (hw : w ∈ cyclicInvariants K m q) (hwu : IsUnit w) (r : ℕ → MvPowerSeries (Fin 2) K)
    (hr : ∀ i, r i ∈ cyclicInvariants K m q)
    (h : ∑ i ∈ Finset.range m, r i * (w * MvPowerSeries.X 0) ^ i = 0) :
    ∀ i < m, r i = 0 := by
  haveI := hK.isAlgClosed
  haveI := hK.charZero
  have hm := hK.one_le
  haveI : NeZero (m : K) := ⟨by exact_mod_cast (show m ≠ 0 by omega)⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K m
  have h0 := CyclicChart.eq_zero_of_sum_eq_zero_of_rescale (q := q) (by omega) hζ₀
    (e := fun i => r i * (w * MvPowerSeries.X 0) ^ i)
    (fun ζ i => CyclicChart.rescale_mul_pow_X_zero ζ hw (hr i) i) h
  intro i hi
  have := h0 i hi
  have hx : (w * MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ i ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero hwu.ne_zero CyclicChart.prime_X_zero.ne_zero)
  exact (mul_eq_zero.1 this).resolve_right hx

end CoverRing

section CoverRing2

open MvPowerSeries
open scoped TensorProduct

/-- **The Kummer cover of `S` in the cyclic chart.** Over a Noetherian local domain `A` with a
flat local injective map `φ` to the chart `R = K[[x, y]]^{μ_m}` sending `f` to `(w x)^m` and `g`
to `x^a γ` (with `γ(0) = 0` and nonzero `y`-coefficient), the field `L = K_A(f^{1/m})` contains
the ring `O = A[t, y]`, `t = f^{1/m}`, `y = g / t^a`, which is a regular local ring of dimension
two with maximal ideal `(t, y)`, faithfully flat under the map to `K[[x, y]]` sending `t` to `w x`
and `y` to `w^{-a} γ`. -/
theorem exists_cover_ring {A KA : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Field KA] [Algebra A KA] [IsFractionRing A KA]
    {K : Type*} [Field K] {m : ℕ} {q : ℤ} (hK : IsCyclicQuotientSetting K m q)
    [IsLocalRing (cyclicInvariants K m q)]
    [Module.Finite (cyclicInvariants K m q) (MvPowerSeries (Fin 2) K)]
    (φ : A →+* cyclicInvariants K m q) (hφ : φ.Flat) (hφinj : Function.Injective φ)
    [IsLocalHom φ] {f g Y : A} {a : ℕ} {w γ wi : MvPowerSeries (Fin 2) K}
    (hw : w ∈ cyclicInvariants K m q) (hwi : wi * w = 1)
    (hf : (φ f : MvPowerSeries (Fin 2) K) = (w * MvPowerSeries.X 0) ^ m)
    (hg : (φ g : MvPowerSeries (Fin 2) K) = MvPowerSeries.X 0 ^ a * γ)
    (hγ0 : constantCoeff γ = 0) (hγ1 : coeff (Finsupp.single 1 1) γ ≠ 0)
    (hY : Y * f ^ a = g ^ m) (hYm : Y ∈ maximalIdeal A) (hfm : f ∈ maximalIdeal A) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra KA L) (_ : Algebra A L) (_ : IsScalarTower A KA L)
      (O : Subalgebra A L) (t y : L) (ht : t ∈ O) (hy : y ∈ O)
      (τ : O →+* MvPowerSeries (Fin 2) K),
      O = Algebra.adjoin A {t, y} ∧ t ^ m = algebraMap A L f ∧ y * t ^ a = algebraMap A L g ∧
      y ^ m = algebraMap A L Y ∧ Module.finrank KA L = m ∧
      τ ⟨t, ht⟩ = w * MvPowerSeries.X 0 ∧ τ ⟨y, hy⟩ = wi ^ a * γ ∧
      (∀ b : A, τ (algebraMap A O b) = φ b) ∧
      (letI := τ.toAlgebra; Module.FaithfullyFlat O (MvPowerSeries (Fin 2) K)) ∧
      ∃ (_ : IsLocalRing O) (_ : IsNoetherianRing O), IsRegularLocalRing O ∧
        maximalIdeal O = Ideal.span {⟨t, ht⟩, ⟨y, hy⟩} ∧ Module.Finite A O ∧
      ∀ l : L, ∃ (o : L) (s : A), o ∈ O ∧ s ≠ 0 ∧ algebraMap A L s * l = o := by
  classical
  haveI : IsDomain (MvPowerSeries (Fin 2) K) := NoZeroDivisors.to_isDomain _
  have hm := hK.one_le
  have hwu : IsUnit w := IsUnit.of_mul_eq_one wi (by rw [mul_comm]; exact hwi)
  set x' : MvPowerSeries (Fin 2) K := w * MvPowerSeries.X 0 with hx'
  set ψ : A →+* MvPowerSeries (Fin 2) K := (cyclicInvariants K m q).subtype.comp φ with hψ
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp hφinj
  have hψR : ∀ b, ψ b ∈ cyclicInvariants K m q := fun b => (φ b).2
  -- irreducibility of `T^m - f`
  have hirr : Irreducible (Polynomial.X ^ m - Polynomial.C (algebraMap A KA f)) :=
    KummerCover.irreducible_X_pow_sub_C_of_sum_eq_zero ψ hψinj (by omega) f x' hf.symm
      fun c hc => by
        have := eq_zero_of_sum_mul_pow_eq_zero hK hw hwu (fun i => ψ (c i)) (fun i => hψR _) hc
        exact fun i hi => hψinj ((this i hi).trans (map_zero ψ).symm)
  set p : Polynomial KA := Polynomial.X ^ m - Polynomial.C (algebraMap A KA f) with hp
  haveI : Fact (Irreducible p) := ⟨hirr⟩
  have hp0 : p ≠ 0 := hirr.ne_zero
  haveI : IsScalarTower A KA (AdjoinRoot p) := inferInstance
  set t : AdjoinRoot p := AdjoinRoot.root p with ht_def
  have injA := IsFractionRing.injective A KA
  have hf0 : f ≠ 0 := by
    rintro rfl
    have : (w * MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ m = 0 := by rw [← hf]; simp
    exact pow_ne_zero _ (mul_ne_zero hwu.ne_zero CyclicChart.prime_X_zero.ne_zero) this
  have htm : t ^ m = algebraMap A (AdjoinRoot p) f := by
    have h := AdjoinRoot.eval₂_root p
    rw [hp, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero] at h
    exact h
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at htm
    have : algebraMap A (AdjoinRoot p) f ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply A KA (AdjoinRoot p)]
      exact (map_ne_zero _).2 ((map_ne_zero_iff _ injA).2 hf0)
    exact this htm.symm
  set y : AdjoinRoot p := algebraMap A (AdjoinRoot p) g * t⁻¹ ^ a with hy_def
  have hyt : y * t ^ a = algebraMap A (AdjoinRoot p) g := by
    rw [hy_def, mul_assoc, ← mul_pow, inv_mul_cancel₀ ht0, one_pow, mul_one]
  have hym : y ^ m = algebraMap A (AdjoinRoot p) Y := by
    have h1 : (y * t ^ a) ^ m = algebraMap A (AdjoinRoot p) Y * (t ^ m) ^ a := by
      rw [hyt, htm, ← map_pow, ← map_pow, ← map_mul, hY]
    rw [mul_pow, ← pow_mul, mul_comm a m, pow_mul] at h1
    exact mul_right_cancel₀ (pow_ne_zero _ (pow_ne_zero _ ht0)) h1
  -- the embedding into the fraction field of `K[[x, y]]`
  set FP := FractionRing (MvPowerSeries (Fin 2) K)
  let ι : KA →+* FP := IsFractionRing.lift (g := (algebraMap _ FP).comp ψ)
    ((IsFractionRing.injective _ FP).comp hψinj)
  have hι : ∀ b : A, ι (algebraMap A KA b) = algebraMap _ FP (ψ b) := fun b =>
    IsFractionRing.lift_algebraMap _ b
  let τL : AdjoinRoot p →+* FP := AdjoinRoot.lift ι (algebraMap _ FP x') (by
    rw [hp, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hι, ← map_pow,
      ← hf]
    exact sub_self _)
  have hτt : τL t = algebraMap _ FP x' := AdjoinRoot.lift_root _
  have hτA : ∀ b : A, τL (algebraMap A (AdjoinRoot p) b) = algebraMap _ FP (ψ b) := fun b => by
    rw [IsScalarTower.algebraMap_apply A KA (AdjoinRoot p), AdjoinRoot.algebraMap_eq,
      AdjoinRoot.lift_of, hι]
  have hx'0 : x' ≠ 0 := mul_ne_zero hwu.ne_zero CyclicChart.prime_X_zero.ne_zero
  have hτy : τL y = algebraMap _ FP (wi ^ a * γ) := by
    have hx'F : algebraMap _ FP x' ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ FP)).2 hx'0
    have hg' : ψ g = wi ^ a * γ * x' ^ a := by
      change (φ g : MvPowerSeries (Fin 2) K) = _
      rw [hg, hx', mul_pow]
      calc MvPowerSeries.X 0 ^ a * γ = (wi * w) ^ a * (MvPowerSeries.X 0 ^ a * γ) := by
            rw [hwi, one_pow, one_mul]
        _ = _ := by ring
    rw [hy_def, map_mul, map_pow, map_inv₀, hτt, hτA, inv_pow, ← div_eq_mul_inv,
      div_eq_iff (pow_ne_zero _ hx'F), ← map_pow, ← map_mul, hg']
  -- the ring `O = A[t, y]` and its map to `K[[x, y]]`
  set O : Subalgebra A (AdjoinRoot p) := Algebra.adjoin A {t, y} with hO
  have htO : t ∈ O := Algebra.subset_adjoin (by simp)
  have hyO : y ∈ O := Algebra.subset_adjoin (by simp)
  have hrange : ∀ o ∈ O, τL o ∈ (algebraMap (MvPowerSeries (Fin 2) K) FP).range := by
    intro o ho
    induction ho using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with rfl | rfl
      · exact ⟨x', hτt.symm⟩
      · exact ⟨_, hτy.symm⟩
    | algebraMap b => exact ⟨ψ b, (hτA b).symm⟩
    | add z z' _ _ hz hz' =>
      rw [map_add]; exact Subring.add_mem _ hz hz'
    | mul z z' _ _ hz hz' =>
      rw [map_mul]; exact Subring.mul_mem _ hz hz'
  have hinjF : Function.Injective (algebraMap (MvPowerSeries (Fin 2) K) FP) :=
    IsFractionRing.injective _ FP
  let e : MvPowerSeries (Fin 2) K ≃+* (algebraMap (MvPowerSeries (Fin 2) K) FP).range :=
    RingEquiv.ofBijective (algebraMap _ FP).rangeRestrict
      ⟨fun a b h => hinjF (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let τ : O →+* MvPowerSeries (Fin 2) K :=
    e.symm.toRingHom.comp ((τL.comp O.val.toRingHom).codRestrict _ fun o => hrange o o.2)
  have hτ : ∀ o : O, algebraMap _ FP (τ o) = τL o := fun o => by
    have h1 : ((e (τ o)) : FP) = algebraMap _ FP (τ o) := rfl
    rw [← h1]
    simp only [τ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply, RingHom.codRestrict_apply]
    rfl
  have hτ' : ∀ (o : O) (z : MvPowerSeries (Fin 2) K), algebraMap _ FP z = τL o → τ o = z :=
    fun o z h => hinjF ((hτ o).trans h.symm)
  have hτt' : τ ⟨t, htO⟩ = x' := hτ' _ _ hτt.symm
  have hτy' : τ ⟨y, hyO⟩ = wi ^ a * γ := hτ' _ _ hτy.symm
  have hτA' : ∀ b : A, τ (algebraMap A O b) = ψ b := fun b => hτ' _ _ (hτA b).symm
  -- the tensor product `O ⊗_A R`
  letI : Algebra A (cyclicInvariants K m q) := φ.toAlgebra
  letI : Algebra A (MvPowerSeries (Fin 2) K) := ψ.toAlgebra
  haveI : Module.Flat A (cyclicInvariants K m q) := hφ
  let τA : O →ₐ[A] MvPowerSeries (Fin 2) K := { τ with commutes' := hτA' }
  let ρA : cyclicInvariants K m q →ₐ[A] MvPowerSeries (Fin 2) K :=
    { (cyclicInvariants K m q).subtype with commutes' := fun _ => rfl }
  let Φ := Algebra.TensorProduct.lift τA ρA fun _ _ => Commute.all _ _
  have hdim : (AdjoinRoot.powerBasis hp0).dim = m := by
    rw [AdjoinRoot.powerBasis_dim, hp, Polynomial.natDegree_X_pow_sub_C]
  have hgenO : (AdjoinRoot.powerBasis hp0).gen ∈ O := by
    rwa [AdjoinRoot.powerBasis_gen]
  have hΦinj : Function.Injective Φ := by
    refine KummerCover.injective_lift_of_sum_eq_zero O (AdjoinRoot.powerBasis hp0) hgenO τA ρA ?_
    intro r hr
    have hgen' : (⟨(AdjoinRoot.powerBasis hp0).gen, hgenO⟩ : O) = ⟨t, htO⟩ :=
      Subtype.ext (AdjoinRoot.powerBasis_gen hp0)
    have hτg : τA ⟨(AdjoinRoot.powerBasis hp0).gen, hgenO⟩ = x' := by
      rwa [hgen']
    rw [hτg] at hr
    funext i
    set r' : ℕ → MvPowerSeries (Fin 2) K := fun k =>
      if hk : k < (AdjoinRoot.powerBasis hp0).dim then (r ⟨k, hk⟩ : MvPowerSeries (Fin 2) K)
      else 0
    have hr'R : ∀ k, r' k ∈ cyclicInvariants K m q := fun k => by
      simp only [r']; split_ifs
      · exact (r _).2
      · exact zero_mem _
    have hsum : ∑ k ∈ Finset.range m, r' k * x' ^ k = 0 := by
      rw [← hdim, Finset.sum_range, ← hr]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [r', dif_pos k.2]
      rfl
    have := eq_zero_of_sum_mul_pow_eq_zero hK hw hwu r' hr'R hsum i (hdim ▸ i.2)
    simp only [r', dif_pos i.2] at this
    exact Subtype.ext this
  have hΦt : Φ (⟨t, htO⟩ ⊗ₜ 1) = x' := by
    simp only [Φ, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    exact hτt'
  have hΦy : Φ (⟨y, hyO⟩ ⊗ₜ 1) = wi ^ a * γ := by
    simp only [Φ, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    exact hτy'
  have hΦR : ∀ r : cyclicInvariants K m q, Φ (1 ⊗ₜ r) = r := by
    intro r; simp only [Φ, Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
  have hΦsurj : Function.Surjective Φ := by
    have hS : Φ.range.toSubring = ⊤ := by
      obtain ⟨α, β, hαβ, hβ⟩ := CyclicChart.exists_eq_X_mul_add_X_mul hγ0
      have hwiu : IsUnit wi := IsUnit.of_mul_eq_one w hwi
      have hβu : IsUnit (wi ^ a * β) := by
        refine (hwiu.pow a).mul ?_
        rw [isUnit_iff_constantCoeff, hβ]; exact isUnit_iff_ne_zero.2 hγ1
      have hspan : Ideal.span {x', wi ^ a * γ} =
          IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) K) := by
        rw [CyclicChart.maximalIdeal_eq_span_X_X, ← CyclicChart.span_eq_span_X_X hwu hβu (α := wi ^ a * α)]
        congr 2
        rw [hαβ]; ring_nf
      have hxm : x' ^ m = ψ f := by rw [← hf]; rfl
      have hym' : (wi ^ a * γ) ^ m = ψ Y := by
        rw [← hτy', ← map_pow, ← hτA']
        congr 1
        exact Subtype.ext hym
      refine CyclicChart.eq_top_of_span_eq_maximalIdeal (cyclicInvariants K m q) Φ.range.toSubring
        (fun r hr => ⟨1 ⊗ₜ ⟨r, hr⟩, hΦR _⟩) (fun c => ?_) ⟨_, hΦt⟩ ⟨_, hΦy⟩ hspan
        (N := m) (hxm ▸ (φ f).2) ?_ (hym' ▸ (φ Y).2) ?_
      · rw [mem_cyclicInvariants_iff]
        intro ζ
        ext d
        rw [coeff_rescale, coeff_C]
        split_ifs with h
        · subst h; simp
        · simp
      · have : (⟨x' ^ m, hxm ▸ (φ f).2⟩ : cyclicInvariants K m q) = φ f := Subtype.ext hxm
        rw [this]; exact map_nonunit φ f hfm
      · have : (⟨(wi ^ a * γ) ^ m, hym' ▸ (φ Y).2⟩ : cyclicInvariants K m q) = φ Y :=
          Subtype.ext hym'
        rw [this]; exact map_nonunit φ Y hYm
    intro z
    have : z ∈ Φ.range.toSubring := hS ▸ Subring.mem_top z
    exact this
  -- faithful flatness of `O → K[[x, y]]`
  letI alg : Algebra O (MvPowerSeries (Fin 2) K) := τ.toAlgebra
  let eL : O ⊗[A] cyclicInvariants K m q ≃ₗ[O] MvPowerSeries (Fin 2) K :=
    LinearEquiv.ofBijective
      { toFun := Φ
        map_add' := map_add Φ
        map_smul' := fun o ξ => by
          induction ξ using TensorProduct.induction_on with
          | zero => simp
          | tmul o' r =>
            rw [RingHom.id_apply, TensorProduct.smul_tmul', smul_eq_mul]
            simp only [Φ, Algebra.TensorProduct.lift_tmul, map_mul, Algebra.smul_def]
            rw [mul_assoc]
            rfl
          | add ξ η hξ hη => rw [smul_add, map_add, hξ, hη, map_add, smul_add] }
      ⟨hΦinj, hΦsurj⟩
  haveI : IsLocalHom (algebraMap A (cyclicInvariants K m q)) := ‹IsLocalHom φ›
  haveI : Module.FaithfullyFlat A (cyclicInvariants K m q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  haveI hFF : Module.FaithfullyFlat O (MvPowerSeries (Fin 2) K) :=
    Module.FaithfullyFlat.of_linearEquiv _ _ eL.symm
  haveI : IsLocalRing O := Module.FaithfullyFlat.isLocalRing O (MvPowerSeries (Fin 2) K)
  -- finiteness and noetherianity
  have htI : IsIntegral A t := ⟨Polynomial.X ^ m - Polynomial.C f,
    Polynomial.monic_X_pow_sub_C _ (by omega), by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, htm, sub_self]⟩
  have hyI : IsIntegral A y := ⟨Polynomial.X ^ m - Polynomial.C Y,
    Polynomial.monic_X_pow_sub_C _ (by omega), by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hym, sub_self]⟩
  haveI hfin : Module.Finite A O :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.toFinite _) (by
      rintro z (rfl | rfl)
      · exact htI
      · exact hyI)
  haveI : IsNoetherianRing O := IsNoetherianRing.of_finite A O
  haveI : IsRegularLocalRing (MvPowerSeries (Fin 2) K) := MvPowerSeries.isRegularLocalRing K 2
  haveI : IsLocalHom (algebraMap O (MvPowerSeries (Fin 2) K)) :=
    Module.FaithfullyFlat.isLocalHom O (MvPowerSeries (Fin 2) K)
  have hreg : IsRegularLocalRing O := IsRegularLocalRing.of_flat_of_isLocalHom
    (MvPowerSeries (Fin 2) K)
  -- the maximal ideal
  have hmaxO : maximalIdeal O = Ideal.span {⟨t, htO⟩, ⟨y, hyO⟩} := by
    apply le_antisymm
    · have h1 : (Ideal.span {(⟨t, htO⟩ : O), ⟨y, hyO⟩}).map (algebraMap O
          (MvPowerSeries (Fin 2) K)) = maximalIdeal (MvPowerSeries (Fin 2) K) := by
        rw [Ideal.map_span, Set.image_pair]
        change Ideal.span {τ ⟨t, htO⟩, τ ⟨y, hyO⟩} = _
        rw [hτt', hτy']
        obtain ⟨α, β, hαβ, hβ⟩ := CyclicChart.exists_eq_X_mul_add_X_mul hγ0
        have hwiu : IsUnit wi := IsUnit.of_mul_eq_one w hwi
        have hβu : IsUnit (wi ^ a * β) := by
          refine (hwiu.pow a).mul ?_
          rw [isUnit_iff_constantCoeff, hβ]; exact isUnit_iff_ne_zero.2 hγ1
        rw [CyclicChart.maximalIdeal_eq_span_X_X,
          ← CyclicChart.span_eq_span_X_X hwu hβu (α := wi ^ a * α)]
        congr 2
        rw [hαβ]; ring_nf
      rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (Ideal.span {(⟨t, htO⟩ : O), ⟨y, hyO⟩})
        (B := MvPowerSeries (Fin 2) K), h1]
      intro o ho
      rw [Ideal.mem_comap]
      exact map_nonunit (algebraMap O (MvPowerSeries (Fin 2) K)) o ho
    · rw [Ideal.span_le]
      rintro z (rfl | rfl)
      · rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        have := hu.map τ
        rw [hτt', hx', isUnit_iff_constantCoeff, map_mul, MvPowerSeries.constantCoeff_X,
          mul_zero] at this
        exact not_isUnit_zero this
      · rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        have := hu.map τ
        rw [hτy', isUnit_iff_constantCoeff, map_mul, hγ0, mul_zero] at this
        exact not_isUnit_zero this
  have hfrac : ∀ l : AdjoinRoot p, ∃ (o : AdjoinRoot p) (s : A), o ∈ O ∧ s ≠ 0 ∧
      algebraMap A (AdjoinRoot p) s * l = o := by
    intro l
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective l
    obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) q
    refine ⟨Polynomial.aeval t (IsLocalization.integerNormalization (nonZeroDivisors A) q), b,
      ?_, nonZeroDivisors.ne_zero hbM, ?_⟩
    · exact Algebra.adjoin_mono (by simp) (Polynomial.aeval_mem_adjoin_singleton A t)
    · have e : Polynomial.aeval t (IsLocalization.integerNormalization (nonZeroDivisors A) q) =
          Polynomial.aeval t ((IsLocalization.integerNormalization (nonZeroDivisors A) q).map
            (algebraMap A KA)) := (Polynomial.aeval_map_algebraMap KA t _).symm
      rw [e, hb, Algebra.smul_def, map_mul, Polynomial.algebraMap_apply, Polynomial.aeval_C,
        ← IsScalarTower.algebraMap_apply, AdjoinRoot.aeval_eq]
  refine ⟨AdjoinRoot p, inferInstance, inferInstance, inferInstance, inferInstance, O, t, y, htO,
    hyO, τ, rfl, htm, hyt, hym, ?_, hτt', hτy', hτA', hFF, inferInstance, inferInstance, hreg,
    hmaxO, hfin, hfrac⟩
  rw [(AdjoinRoot.powerBasis hp0).finrank, hdim]

end CoverRing2

section Unramified

/-- **An unramified extension of discrete valuation rings preserves orders of forms.** Let
`C → B` be a local, essentially finite type, formally unramified map of discrete valuation rings
over `k` (characteristic zero), with fraction fields `F ⊆ L`, and `dϖ, dx` a frame of `Ω_{C/k}`
with `ϖ` a uniformizer. For a valuation `v` on `F` normalized by `ϖ`, the order along `B` of the
pull-back of an `m`-canonical form equals its order along `C`. -/
theorem ordAt_pullbackForms_eq_of_formallyUnramified {k C B F L : Type*} [Field k] [CharZero k]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra C B] [IsLocalHom (algebraMap C B)]
    [Algebra.EssFiniteType C B] [Algebra.FormallyUnramified C B]
    [Field F] [Field L] [Algebra C F] [IsFractionRing C F] [Algebra B L] [IsFractionRing B L]
    [Algebra F L] [Algebra k C] [Algebra k B] [Algebra k F] [Algebra k L]
    [IsScalarTower k C F] [IsScalarTower k B L] [IsScalarTower k F L] [IsScalarTower k C B]
    (hcomp : ∀ c : C, algebraMap F L (algebraMap C F c) = algebraMap B L (algebraMap C B c))
    {d : ℕ} [Nontrivial (⋀[F]^(d + 1) Ω[F⁄k])] [Nontrivial (⋀[L]^(d + 1) Ω[L⁄k])]
    {ϖ : C} (hϖ : Irreducible ϖ) {x : Fin d → C}
    (hx : Submodule.span C (Set.range (Fin.cons (KaehlerDifferential.D k C ϖ)
      fun i => KaehlerDifferential.D k C (x i) : Fin (d + 1) → Ω[C⁄k])) = ⊤)
    {v : F → ℤ} (hmul : ∀ x y : F, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ a : C, IsUnit a → v (algebraMap C F a) = 0) (hvϖ : v (algebraMap C F ϖ) = 1)
    (m : ℕ) (ω : PluriForms k F (d + 1) m) (hω : ω ≠ 0) :
    ordAt B (fun c => WithZero.log (Ring.ordFrac B c)) (pullbackForms (K' := L) (m : ℤ) ω) =
      ordAt C v ω ∧ ∀ f : F, f ≠ 0 → WithZero.log (Ring.ordFrac B (algebraMap F L f)) = v f := by
  classical
  set ϖ' := algebraMap C B ϖ
  -- `ϖ` stays a uniformizer
  have hmaxC : IsLocalRing.maximalIdeal C = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hmaxB : IsLocalRing.maximalIdeal B = Ideal.span {ϖ'} := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := C) (S := B), hmaxC, Ideal.map_span,
      Set.image_singleton]
  have hϖ' : Irreducible ϖ' := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ').2 hmaxB
  -- the frame of `Ω_{B/k}`
  have hx' : Submodule.span B (Set.range (Fin.cons (KaehlerDifferential.D k B ϖ')
      fun i => KaehlerDifferential.D k B (algebraMap C B (x i)) : Fin (d + 1) → Ω[B⁄k])) = ⊤ := by
    have hsurj : Function.Surjective (KaehlerDifferential.mapBaseChange k C B) := by
      intro w
      have := (KaehlerDifferential.exact_mapBaseChange_map k C B w).1
        (Subsingleton.elim _ _)
      exact this
    rw [eq_top_iff]
    rintro w -
    obtain ⟨ξ, rfl⟩ := hsurj w
    induction ξ using TensorProduct.induction_on with
    | zero => simp
    | add ξ η h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
    | tmul b ω' =>
      rw [KaehlerDifferential.mapBaseChange_tmul]
      refine Submodule.smul_mem _ b ?_
      have hω' : ω' ∈ Submodule.span C (Set.range (Fin.cons (KaehlerDifferential.D k C ϖ)
          fun i => KaehlerDifferential.D k C (x i) : Fin (d + 1) → Ω[C⁄k])) := hx ▸ trivial
      have hm := Submodule.mem_map_of_mem
        (f := (KaehlerDifferential.map k k C B).restrictScalars C) hω'
      rw [Submodule.map_span] at hm
      refine Submodule.span_le_restrictScalars C B _ (Submodule.span_mono ?_ hm)
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · exact ⟨0, by simp [ϖ', KaehlerDifferential.map_D]⟩
      · exact ⟨i.succ, by simp [KaehlerDifferential.map_D]⟩
  -- valuations
  have hv' : ∀ x y : L, x ≠ 0 → y ≠ 0 → WithZero.log (Ring.ordFrac B (x * y)) =
      WithZero.log (Ring.ordFrac B x) + WithZero.log (Ring.ordFrac B y) := by
    intro x y hx hy
    rw [map_mul, WithZero.log_mul ((map_ne_zero _).2 hx) ((map_ne_zero _).2 hy)]
  have hunit' : ∀ a : B, IsUnit a → WithZero.log (Ring.ordFrac B (algebraMap B L a)) = 0 := by
    intro a ha; rw [Ring.ordFrac_of_isUnit (K := L) ha, WithZero.log_one]
  have hvϖ' : WithZero.log (Ring.ordFrac B (algebraMap B L ϖ')) = 1 := by
    rw [Ring.ordFrac_irreducible (K := L) hϖ', WithZero.log_exp]
  -- the two valuations agree on `F`
  have hC : ∀ r : C, r ≠ 0 → v (algebraMap C F r) =
      WithZero.log (Ring.ordFrac B (algebraMap F L (algebraMap C F r))) := by
    intro r hr
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
    have hϖF : algebraMap C F ϖ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective C F)).2 hϖ.ne_zero
    have hpow : ∀ n : ℕ, v (algebraMap C F ϖ ^ n) = n := by
      intro n
      induction n with
      | zero =>
        have := hunit 1 isUnit_one
        simpa using this
      | succ n ih => rw [pow_succ, hmul _ _ (pow_ne_zero _ hϖF) hϖF, ih, hvϖ]; push_cast; ring
    have huF : algebraMap C F u ≠ 0 := ((u.isUnit).map _).ne_zero
    have e : algebraMap F L (algebraMap C F (↑u * ϖ ^ n)) =
        algebraMap B L (algebraMap C B ↑u) * algebraMap B L ϖ' ^ n := by
      rw [hcomp, map_mul, map_pow, map_mul, map_pow]
    rw [e, map_mul, map_pow, map_mul, map_pow, hmul _ _ huF (pow_ne_zero _ hϖF), hunit _ u.isUnit,
      hpow, Ring.ordFrac_of_isUnit (K := L) (u.isUnit.map _),
      Ring.ordFrac_irreducible (K := L) hϖ', one_mul, ← WithZero.exp_nsmul, WithZero.log_exp]
    simp
  have hvv : ∀ f : F, f ≠ 0 → WithZero.log (Ring.ordFrac B (algebraMap F L f)) = v f := by
    intro f hf
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := C) f
    have hr : r ≠ 0 := by
      rintro rfl
      simp at hf
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hrF : algebraMap C F r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective C F)).2 hr
    have hsF : algebraMap C F s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective C F)).2 hs0
    have e1 := hmul (algebraMap C F r / algebraMap C F s) (algebraMap C F s)
      (div_ne_zero hrF hsF) hsF
    rw [div_mul_cancel₀ _ hsF] at e1
    have e2 := hv' (algebraMap F L (algebraMap C F r / algebraMap C F s))
      (algebraMap F L (algebraMap C F s)) ((map_ne_zero _).2 (div_ne_zero hrF hsF))
      ((map_ne_zero _).2 hsF)
    rw [← map_mul, div_mul_cancel₀ _ hsF] at e2
    rw [hC r hr, hC s hs0] at e1
    linarith
  have := ordAt_pullbackForms_eq_of_ramification (v' := fun c => WithZero.log (Ring.ordFrac B c))
    hcomp hx hx'
    (hϖ'.not_isUnit |> (IsLocalRing.mem_maximalIdeal _).2) hϖ'.ne_zero isUnit_one (e := 0)
    (by rw [zero_add, pow_one, one_mul]) hmul hunit hv' hunit' hvϖ'
    (fun f hf => by rw [hvv f hf]; push_cast; ring) m ω hω
  refine ⟨?_, hvv⟩
  rw [this]
  ring

end Unramified

section ChartY

open MvPowerSeries

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **The element `Y = g^m / f^a`.** -/
theorem chart_Y {x : X} {K : Type*} [Field K] {m : ℕ} {q : ℤ} (hm : 0 < m)
    [IsLocalRing (cyclicInvariants K m q)]
    (φ : X.presheaf.stalk x →+* cyclicInvariants K m q) [IsLocalHom φ]
    (P : MMP.Mori.PrimeDivisor X) (hxP : x ∈ P.support)
    {f g : X.presheaf.stalk x} {a : ℕ} (hf0 : f ≠ 0)
    (hfP : X.ord (algebraMap _ X.functionField f) P.genericPoint = m)
    (hfE : ∀ E : MMP.Mori.PrimeDivisor X, x ∈ E.support → E ≠ P →
      X.ord (algebraMap _ X.functionField f) E.genericPoint = 0)
    (hga : g ∈ ordIdeal P a hxP) {w γ : MvPowerSeries (Fin 2) K} (hwu : IsUnit w)
    (hfw : (φ f : MvPowerSeries (Fin 2) K) = (w * MvPowerSeries.X 0) ^ m)
    (hgγ : (φ g : MvPowerSeries (Fin 2) K) = MvPowerSeries.X 0 ^ a * γ)
    (hγ0 : constantCoeff γ = 0) :
    ∃ Y : X.presheaf.stalk x, Y * f ^ a = g ^ m ∧ Y ∈ maximalIdeal (X.presheaf.stalk x) ∧
      (φ Y : MvPowerSeries (Fin 2) K) * w ^ (m * a) = γ ^ m := by
  classical
  have injA := IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  have hfK : algebraMap _ X.functionField f ≠ 0 := (map_ne_zero_iff _ injA).2 hf0
  obtain ⟨Y, hY⟩ : ∃ Y : X.presheaf.stalk x, Y * f ^ a = g ^ m := by
    by_cases hg0 : g = 0
    · exact ⟨0, by rw [hg0, zero_pow (by omega), zero_mul]⟩
    have hgK : algebraMap _ X.functionField g ≠ 0 := (map_ne_zero_iff _ injA).2 hg0
    obtain ⟨Y, hYK⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
      x (mul_ne_zero (pow_ne_zero m hgK) (inv_ne_zero (pow_ne_zero a hfK))) fun Γ hΓ => by
        have hinv : X.ord ((algebraMap _ X.functionField f) ^ a)⁻¹ Γ.genericPoint =
            - X.ord ((algebraMap _ X.functionField f) ^ a) Γ.genericPoint := by
          have := Scheme.ord_mul (x := Γ.genericPoint) (pow_ne_zero a hfK)
            (inv_ne_zero (pow_ne_zero a hfK))
          rw [mul_inv_cancel₀ (pow_ne_zero a hfK), Aux.ord_one'] at this; omega
        rw [Scheme.ord_mul (pow_ne_zero m hgK) (inv_ne_zero (pow_ne_zero a hfK)), hinv,
          Aux.ord_pow' hgK, Aux.ord_pow' hfK]
        have hng := ord_nonneg_of_mem_support Γ hΓ g
        by_cases hΓP : Γ = P
        · subst hΓP
          rw [hfP]
          rcases (mem_ordIdeal_iff Γ hxP a g).1 hga with h | h
          · exact absurd h hg0
          have : (a : ℤ) ≤ (X.ord (algebraMap _ X.functionField g) Γ.genericPoint).toNat := by
            exact_mod_cast h
          rw [Int.toNat_of_nonneg hng] at this
          nlinarith
        · rw [hfE Γ hΓ hΓP]; nlinarith
    refine ⟨Y, injA ?_⟩
    rw [map_mul, hYK, map_pow, map_pow, inv_mul_cancel_right₀ (pow_ne_zero a hfK)]
  -- `Y` vanishes at the closed point of the chart
  have e1 := congrArg (fun z => (φ z : MvPowerSeries (Fin 2) K)) hY
  simp only [map_mul, map_pow, Subring.coe_mul, SubmonoidClass.coe_pow, hfw, hgγ] at e1
  have e2 : (φ Y : MvPowerSeries (Fin 2) K) * w ^ (m * a) = γ ^ m := by
    have hX : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ (a * m) ≠ 0 :=
      pow_ne_zero _ CyclicChart.prime_X_zero.ne_zero
    apply mul_left_cancel₀ hX
    calc MvPowerSeries.X 0 ^ (a * m) * ((φ Y : MvPowerSeries (Fin 2) K) * w ^ (m * a))
        = (φ Y : MvPowerSeries (Fin 2) K) * ((w * MvPowerSeries.X 0) ^ m) ^ a := by ring
      _ = (MvPowerSeries.X 0 ^ a * γ) ^ m := e1
      _ = _ := by ring
  refine ⟨Y, hY, ?_, e2⟩
  have e3 := congrArg constantCoeff e2
  rw [map_mul, map_pow, map_pow, hγ0, zero_pow (by omega)] at e3
  have hwc : constantCoeff w ^ (m * a) ≠ 0 := pow_ne_zero _ ((isUnit_iff_constantCoeff.1 hwu).ne_zero)
  have hY0 : constantCoeff (φ Y : MvPowerSeries (Fin 2) K) = 0 :=
    (mul_eq_zero.1 e3).resolve_right hwc
  have hYmR := CyclicChart.mem_maximalIdeal_of_constantCoeff_eq_zero hY0
  by_contra hYu
  exact (IsLocalRing.mem_maximalIdeal _).1 hYmR
    ((IsLocalRing.notMem_maximalIdeal.1 hYu).map φ)

end ChartY

namespace CyclicChart

open MvPowerSeries MMP.Flips

variable {K : Type*} [Field K] {m : ℕ} {q : ℤ}

theorem weight_two_mul (m : ℕ) (d : Fin 2 →₀ ℕ) :
    Finsupp.weight ![2 * m, 1] d = 2 * m * d 0 + d 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fin.sum_univ_two, mul_comm]

theorem le_weightedOrder_of_mem_cyclicInvariants (hK : IsCyclicQuotientSetting K m q)
    {r : MvPowerSeries (Fin 2) K} (hr : r ∈ cyclicInvariants K m q) (h0 : constantCoeff r = 0) :
    (m : ℕ∞) ≤ weightedOrder ![2 * m, 1] r := by
  haveI := hK.isAlgClosed
  haveI := hK.charZero
  have hm := hK.one_le
  refine le_weightedOrder _ fun d hd => ?_
  by_contra hne
  have hw : Finsupp.weight ![2 * m, 1] d < m := by exact_mod_cast hd
  rw [weight_two_mul] at hw
  have hd0 : d 0 = 0 := by
    by_contra h
    have : 1 ≤ d 0 := Nat.one_le_iff_ne_zero.2 h
    nlinarith
  have hdv := dvd_of_coeff_ne_zero (by omega) hr hne
  rw [hd0, Nat.cast_zero, zero_add] at hdv
  have hc : IsCoprime (m : ℤ) q := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact hK.gcd_eq_one
  have h1 : (m : ℤ) ∣ (d 1 : ℤ) := hc.dvd_of_dvd_mul_left hdv
  have hd1 : d 1 = 0 := Nat.eq_zero_of_dvd_of_lt (Int.natCast_dvd_natCast.1 h1) (by omega)
  have hd : d = 0 := by
    ext i; fin_cases i
    · exact hd0
    · exact hd1
  rw [hd, coeff_zero_eq_constantCoeff_apply, h0] at hne
  exact hne rfl

/-- The ideal of power series of `![2m, 1]`-weighted order at least `2m`. -/
def weightIdeal (m : ℕ) : Ideal (MvPowerSeries (Fin 2) K) where
  carrier := {r | ((2 * m : ℕ) : ℕ∞) ≤ weightedOrder ![2 * m, 1] r}
  add_mem' ha hb := le_trans (le_min ha hb) (min_weightedOrder_le_add _)
  zero_mem' := by simp
  smul_mem' c r hr := by
    show ((2 * m : ℕ) : ℕ∞) ≤ weightedOrder ![2 * m, 1] (c * r)
    exact le_trans (le_trans hr le_add_self) (weightedOrder_mul_ge _)

theorem X_zero_mul_mem_weightIdeal (s : MvPowerSeries (Fin 2) K) :
    MvPowerSeries.X 0 * s ∈ weightIdeal (K := K) m := by
  show ((2 * m : ℕ) : ℕ∞) ≤ weightedOrder ![2 * m, 1] (MvPowerSeries.X 0 * s)
  have hX : ((2 * m : ℕ) : ℕ∞) ≤ weightedOrder ![2 * m, 1] (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) := by
    refine le_weightedOrder _ fun d hd => ?_
    rw [coeff_X]
    split_ifs with h
    · exfalso
      subst h
      have hw : Finsupp.weight ![2 * m, 1] (Finsupp.single (0 : Fin 2) 1) < 2 * m := by
        exact_mod_cast hd
      rw [weight_two_mul] at hw
      simp at hw
    · rfl
  exact le_trans (le_trans hX le_self_add) (weightedOrder_mul_ge _)

theorem weightedOrder_pow_eq (w : Fin 2 → ℕ) (γ : MvPowerSeries (Fin 2) K) (n : ℕ) :
    weightedOrder w (γ ^ n) = n • weightedOrder w γ := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, weightedOrder_mul, ih, succ_nsmul]

/-- **`Y` is a uniformizer of `𝒪_{T,Q}`, in the chart.** If `φ(Y) w^k = γ^m` with `w` a unit and
`γ` vanishing at the origin with nonzero `y`-coefficient, then `Y ∉ I + 𝔪²` for every ideal `I`
mapping into `(x)`. -/
theorem notMem_sup_sq {A : Type*} [CommRing A] [IsLocalRing A] (hK : IsCyclicQuotientSetting K m q)
    [IsLocalRing (cyclicInvariants K m q)]
    (φ : A →+* cyclicInvariants K m q) [IsLocalHom φ] (I : Ideal A)
    (hI : I.map φ ≤ (Ideal.span {MvPowerSeries.X 0}).comap (cyclicInvariants K m q).subtype)
    {Y : A} {w γ : MvPowerSeries (Fin 2) K} {k : ℕ} (hY : (φ Y : MvPowerSeries (Fin 2) K) * w ^ k = γ ^ m)
    (hγ1 : coeff (Finsupp.single 1 1) γ ≠ 0) :
    Y ∉ I ⊔ maximalIdeal A ^ 2 := by
  classical
  haveI : IsDomain (MvPowerSeries (Fin 2) K) := NoZeroDivisors.to_isDomain _
  have hm := hK.one_le
  set J : Ideal (cyclicInvariants K m q) :=
    (weightIdeal (K := K) m).comap (cyclicInvariants K m q).subtype with hJ
  have hIJ : I ≤ J.comap φ := by
    rw [← Ideal.map_le_iff_le_comap]
    refine hI.trans fun r hr => ?_
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hr)
    change (r : MvPowerSeries (Fin 2) K) ∈ weightIdeal m
    have hs' : (r : MvPowerSeries (Fin 2) K) = MvPowerSeries.X 0 * s := by
      rw [mul_comm]; exact hs.symm
    rw [hs']
    exact X_zero_mul_mem_weightIdeal s
  have hmR : maximalIdeal (cyclicInvariants K m q) ^ 2 ≤ J := by
    rw [pow_two, Ideal.mul_le]
    intro a ha b hb
    have ha' := le_weightedOrder_of_mem_cyclicInvariants hK a.2
      (CyclicChart.constantCoeff_eq_zero_of_mem_maximalIdeal ha)
    have hb' := le_weightedOrder_of_mem_cyclicInvariants hK b.2
      (CyclicChart.constantCoeff_eq_zero_of_mem_maximalIdeal hb)
    show ((2 * m : ℕ) : ℕ∞) ≤ weightedOrder ![2 * m, 1]
      ((a : MvPowerSeries (Fin 2) K) * (b : MvPowerSeries (Fin 2) K))
    refine le_trans ?_ (weightedOrder_mul_ge _)
    have := add_le_add ha' hb'
    refine le_trans (le_of_eq ?_) this
    push_cast; ring
  have hmA : maximalIdeal A ^ 2 ≤ J.comap φ := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    refine le_trans (Ideal.pow_right_mono ?_ 2) hmR
    exact Ideal.map_le_iff_le_comap.2 fun a ha =>
      (IsLocalRing.mem_maximalIdeal _).2 fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha
        (isUnit_of_map_unit φ a hu)
  intro hYm
  have hYJ : (φ Y : MvPowerSeries (Fin 2) K) ∈ weightIdeal (K := K) m :=
    sup_le hIJ hmA hYm
  have h1 : ((2 * m : ℕ) : ℕ∞) ≤ weightedOrder ![2 * m, 1] (γ ^ m) := by
    rw [← hY]
    exact le_trans (le_trans hYJ le_self_add) (weightedOrder_mul_ge _)
  have h2 : weightedOrder ![2 * m, 1] γ ≤ 1 := by
    have := weightedOrder_le ![2 * m, 1] hγ1
    rwa [weight_two_mul, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide)] at this
  have h3 : weightedOrder ![2 * m, 1] (γ ^ m) = m • weightedOrder ![2 * m, 1] γ :=
    weightedOrder_pow_eq _ γ m
  rw [h3] at h1
  have h4 : m • weightedOrder ![2 * m, 1] γ ≤ (m : ℕ∞) := by
    calc m • weightedOrder ![2 * m, 1] γ ≤ m • (1 : ℕ∞) := nsmul_le_nsmul_right h2 m
      _ = m := by simp
  have h5 := h1.trans h4
  have : 2 * m ≤ m := by exact_mod_cast h5
  omega

end CyclicChart

namespace KummerCover

open TensorProduct in
/-- **A frame through a generator of the maximal ideal.** If the maximal ideal of a local ring
`O` is `(t)`, `O → κ` is surjective with kernel the maximal ideal, `Ω_{O/k}` is finite and the
`d s̄ᵢ` span `Ω_{κ/k}`, then `dt, ds₁, …, dsₙ` span `Ω_{O/k}`. -/
theorem span_insert_D_eq_top_of_surjective {k O κ : Type*} [Field k] [CommRing O] [IsLocalRing O]
    [Algebra k O] [Module.Finite O Ω[O⁄k]] [CommRing κ] [Algebra O κ] [Algebra k κ]
    [IsScalarTower k O κ] (hπ : Function.Surjective (algebraMap O κ))
    (hker : RingHom.ker (algebraMap O κ) = IsLocalRing.maximalIdeal O) {t : O}
    (hmax : IsLocalRing.maximalIdeal O = Ideal.span {t}) {n : ℕ} (s : Fin n → O)
    (hs : Submodule.span κ (Set.range fun i => KaehlerDifferential.D k κ (algebraMap O κ (s i))) =
      ⊤) :
    Submodule.span O (insert (KaehlerDifferential.D k O t) (Set.range fun i =>
      KaehlerDifferential.D k O (s i))) = ⊤ := by
  set N := Submodule.span O (insert (KaehlerDifferential.D k O t) (Set.range fun i =>
      KaehlerDifferential.D k O (s i)))
  have hex := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k O κ hπ
  suffices hle : (⊤ : Submodule O Ω[O⁄k]) ≤ N ⊔ IsLocalRing.maximalIdeal O • ⊤ by
    exact top_le_iff.1 (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson _) hle)
  have hDt : KaehlerDifferential.D k O t ∈ N := Submodule.subset_span (Set.mem_insert _ _)
  have hsm : ∀ (a : O) (w : Ω[O⁄k]),
      (1 : κ) ⊗ₜ[O] (a • w) = algebraMap O κ a • ((1 : κ) ⊗ₜ[O] w) := by
    intro a w
    rw [← TensorProduct.smul_tmul, smul_tmul', Algebra.smul_def, mul_one, Algebra.smul_def,
      mul_one, Algebra.algebraMap_self, RingHom.id_apply]
  intro ω _
  have hω : KaehlerDifferential.mapBaseChange k O κ (1 ⊗ₜ ω) ∈ Submodule.span κ
      (Set.range fun i => KaehlerDifferential.D k κ (algebraMap O κ (s i))) := by
    rw [hs]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun κ).1 hω
  choose c' hc' using fun i => hπ (c i)
  set ω₁ := ∑ i, c' i • KaehlerDifferential.D k O (s i)
  have hω₁ : ω₁ ∈ N := Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
  have h0 : KaehlerDifferential.mapBaseChange k O κ ((1 : κ) ⊗ₜ (ω - ω₁)) = 0 := by
    rw [tmul_sub, map_sub, ← hc, sub_eq_zero]
    simp only [ω₁, tmul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsm, map_smul, KaehlerDifferential.mapBaseChange_tmul, one_smul,
      KaehlerDifferential.map_D, hc' i]
  obtain ⟨e, he⟩ := (hex _).1 h0
  obtain ⟨⟨a, ha⟩, rfl⟩ := Ideal.toCotangent_surjective _ e
  rw [KaehlerDifferential.kerCotangentToTensor_toCotangent] at he
  have ha' : a ∈ Ideal.span {t} := hmax ▸ hker ▸ ha
  obtain ⟨p, rfl⟩ := Ideal.mem_span_singleton'.1 ha'
  have ht0 : algebraMap O κ t = 0 := by
    rw [← RingHom.mem_ker, hker, hmax]; exact Ideal.subset_span (by simp)
  set ω₂ := ω - ω₁ - p • KaehlerDifferential.D k O t
  have h1 : (1 : κ) ⊗ₜ[O] ω₂ = 0 := by
    have he' : (1 : κ) ⊗ₜ[O] (ω - ω₁) = (1 : κ) ⊗ₜ[O] (p • KaehlerDifferential.D k O t) := by
      rw [← he]
      simp only [Derivation.leibniz, tmul_add, hsm, ht0, zero_smul, add_zero]
    simp only [ω₂, tmul_sub, he', sub_self]
  have h2 : ω₂ ∈ IsLocalRing.maximalIdeal O • (⊤ : Submodule O Ω[O⁄k]) := by
    have h1' : ((Ideal.Quotient.mk (RingHom.ker (algebraMap O κ)) 1 :
        O ⧸ RingHom.ker (algebraMap O κ)) ⊗ₜ[O] ω₂) = 0 := by
      have := congrArg (LinearMap.rTensor Ω[O⁄k]
        (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId O κ) hπ).symm.toLinearMap) h1
      rw [LinearMap.rTensor_tmul, map_zero, AlgEquiv.toLinearMap_apply, map_one] at this
      rw [map_one]
      exact this
    have := congrArg (quotTensorEquivQuotSMul Ω[O⁄k] (RingHom.ker (algebraMap O κ))) h1'
    rw [quotTensorEquivQuotSMul_mk_tmul, one_smul, map_zero] at this
    rw [← hker]
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  have : ω = (ω₁ + p • KaehlerDifferential.D k O t) + ω₂ := by
    simp only [ω₂]; abel
  rw [this]
  exact Submodule.add_mem_sup (N.add_mem hω₁ (N.smul_mem _ hDt)) h2

end KummerCover

section FrameOrd

open MMP MMP.Mori MMP.Flips MMP.Fourfold

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X]

/-- The order along a prime divisor `Γ` of `a • ω^{⊗m}`, for `ω` the wedge of a frame of
`Ω_{𝒪_{X,Γ}/k}`, is `ord_Γ(a)`. -/
theorem ordForm_eq_of_frame (Γ : MMP.Mori.PrimeDivisor X) {y : X} (hy : y = Γ.genericPoint)
    {d m : ℕ} (w : Fin d → (letI := stalkAlgebra sX y; Ω[(X.presheaf.stalk y)⁄k]))
    (hw : letI := stalkAlgebra sX y; Submodule.span (X.presheaf.stalk y) (Set.range w) = ⊤)
    (h0 : letI := stalkAlgebra sX y; letI := functionFieldAlgebra sX
      haveI := isScalarTower_stalk_functionField sX y
      topFormsMap k (X.presheaf.stalk y) X.functionField d (exteriorPower.ιMulti _ d w) ≠ 0)
    (a : X.functionField) (τ : RationalPluriForms sX d m)
    (hτ : letI := stalkAlgebra sX y; letI := functionFieldAlgebra sX
      haveI := isScalarTower_stalk_functionField sX y
      τ = (a • PiTensorProduct.tprod X.functionField (fun _ : Fin m =>
        topFormsMap k (X.presheaf.stalk y) X.functionField d (exteriorPower.ιMulti _ d w)) :
        TensorPower X.functionField m (⋀[X.functionField]^d Ω[X.functionField⁄k]))) :
    Γ.ordForm τ = X.ord a Γ.genericPoint := by
  subst hy
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  have hσ := MMP.Fourfold.span_singleton_ιMulti_eq_top w hw
  rw [MMP.Mori.PrimeDivisor.ordForm_eq Γ τ hσ h0]
  congr 1
  have h1 : τ = a • ZTensorPower.basis (topFormsBasis (X.presheaf.stalk Γ.genericPoint) hσ h0)
      (m : ℤ) () := by
    have hb := ZTensorPower.basis_ofNat (topFormsBasis (X.presheaf.stalk Γ.genericPoint) hσ h0) m
    simp only [topFormsBasis_apply] at hb
    rw [hτ]
    exact congrArg (fun t => a • t) hb.symm
  rw [h1, formCoeff_smul]
  simp [formCoeff]

end FrameOrd

namespace KummerCover

/-- Under a surjection `π : A → C` of local rings onto a discrete valuation ring, the image of
`Y ∈ 𝔪_A \ (ker π + 𝔪_A²)` is a uniformizer. -/
theorem irreducible_of_notMem_sup_sq {A C : Type*} [CommRing A] [IsLocalRing A] [CommRing C]
    [IsDomain C] [IsDiscreteValuationRing C] (π : A →+* C) (hπ : Function.Surjective π) {Y : A}
    (hYm : Y ∈ IsLocalRing.maximalIdeal A)
    (hY : Y ∉ RingHom.ker π ⊔ IsLocalRing.maximalIdeal A ^ 2) : Irreducible (π Y) := by
  classical
  have hmap : (IsLocalRing.maximalIdeal A).map π = IsLocalRing.maximalIdeal C := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      refine (IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_
      obtain ⟨c, hc⟩ := hu.exists_right_inv
      obtain ⟨b, rfl⟩ := hπ c
      have h1 : 1 - a * b ∈ RingHom.ker π := by
        rw [RingHom.mem_ker, map_sub, map_one, map_mul, hc, sub_self]
      have h2 : IsUnit (1 - a * b) := by
        by_contra hn
        have h3 := Ideal.add_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hn)
          (Ideal.mul_mem_right b _ ha)
        rw [sub_add_cancel] at h3
        exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).2 h3)
      have h4 := h2.map π
      rw [RingHom.mem_ker.1 h1] at h4
      exact not_isUnit_zero h4
    · intro c hc
      obtain ⟨a, rfl⟩ := hπ c
      refine Ideal.mem_map_of_mem π ((IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_)
      exact (IsLocalRing.mem_maximalIdeal _).1 hc (hu.map π)
  have hYC : π Y ∈ IsLocalRing.maximalIdeal C := hmap ▸ Ideal.mem_map_of_mem π hYm
  have hYC2 : π Y ∉ IsLocalRing.maximalIdeal C ^ 2 := by
    intro h
    rw [← hmap, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective π hπ] at h
    obtain ⟨b, hb, hbY⟩ := h
    apply hY
    have : Y = (Y - b) + b := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (RingHom.mem_ker.2 (by rw [map_sub, hbY, sub_self])))
      (Ideal.mem_sup_right hb)
  have hY0 : π Y ≠ 0 := fun h => hYC2 (h ▸ Ideal.zero_mem _)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible C
  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hY0 hϖ
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal C := hϖ.not_isUnit
  rcases k with _ | _ | k
  · exfalso
    rw [pow_zero, mul_one] at hk
    exact (IsLocalRing.mem_maximalIdeal _).1 hYC (hk ▸ u.isUnit)
  · rw [zero_add, pow_one] at hk
    rw [hk]
    exact Associated.irreducible ⟨u, mul_comm _ _⟩ hϖ
  · exfalso
    apply hYC2
    rw [hk]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow hϖm _))

theorem ιMulti_cons_cons_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (a b : R) (v₀ v₁ : M) (w : Fin n → M) :
    exteriorPower.ιMulti R (n + 1 + 1) (Fin.cons (a • v₀) (Fin.cons (b • v₁) w) :
      Fin (n + 1 + 1) → M) =
      (a * b) • exteriorPower.ιMulti R (n + 1 + 1) (Fin.cons v₀ (Fin.cons v₁ w) :
        Fin (n + 1 + 1) → M) := by
  have h := (exteriorPower.ιMulti R (n + 1 + 1)).toMultilinearMap.map_smul_univ
    (Fin.cons a (Fin.cons b fun _ => 1) : Fin (n + 1 + 1) → R)
    (Fin.cons v₀ (Fin.cons v₁ w) : Fin (n + 1 + 1) → M)
  rw [Fin.prod_cons, Fin.prod_cons] at h
  simp only [Finset.prod_const_one, mul_one] at h
  have e : (fun i => (Fin.cons a (Fin.cons b fun _ => 1) : Fin (n + 1 + 1) → R) i •
      (Fin.cons v₀ (Fin.cons v₁ w) : Fin (n + 1 + 1) → M) i) =
      (Fin.cons (a • v₀) (Fin.cons (b • v₁) w) : Fin (n + 1 + 1) → M) := by
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;> simp
  rw [e] at h
  exact h

/-- **The frame `dt, dy, dz` of the cover.** Let `O = A[t, y]` be local with maximal ideal
`(t, y)` over a local `A`, `π : A → C` onto a local ring and `dπ(Y), dz̄` a frame of `Ω_{C/k}` with
`Y ∈ 𝔪_A`, `z̄ = π(z)`. Then `dt, dy, dz` span `Ω_{O/k}`. -/
theorem span_D_eq_top_of_cover {k A C L : Type*} [Field k] [CommRing A] [IsLocalRing A]
    [Algebra k A] [CommRing C] [IsLocalRing C] [Algebra k C] (π : A →+* C)
    (hπ : Function.Surjective π) (hπk : ∀ c, π (algebraMap k A c) = algebraMap k C c)
    [CommRing L] [Algebra A L] (O : Subalgebra A L) [IsLocalRing O] [Algebra k O]
    [IsScalarTower k A O] [Module.Finite O Ω[O⁄k]] [IsLocalHom (algebraMap A O)]
    {t y : L} (ht : t ∈ O) (hy : y ∈ O) (hO : O = Algebra.adjoin A {t, y})
    (hmaxO : IsLocalRing.maximalIdeal O = Ideal.span {⟨t, ht⟩, ⟨y, hy⟩})
    (hker : RingHom.ker π ≤ IsLocalRing.maximalIdeal A) {Y : A}
    (hYm : Y ∈ IsLocalRing.maximalIdeal A) {d : ℕ} (z : Fin d → A)
    (hzC : Submodule.span C (Set.range (Fin.cons (KaehlerDifferential.D k C (π Y))
      fun i => KaehlerDifferential.D k C (π (z i)) : Fin (d + 1) → Ω[C⁄k])) = ⊤) :
    Submodule.span O (Set.range (Fin.cons (KaehlerDifferential.D k O ⟨t, ht⟩)
      (Fin.cons (KaehlerDifferential.D k O ⟨y, hy⟩) fun i =>
        KaehlerDifferential.D k O (algebraMap A O (z i))) : Fin (d + 1 + 1) → Ω[O⁄k])) = ⊤ := by
  classical
  set κ := IsLocalRing.ResidueField O
  set ρ : A →+* κ := (IsLocalRing.residue O).comp (algebraMap A O) with hρ
  have hρm : ∀ a ∈ IsLocalRing.maximalIdeal A, ρ a = 0 := fun a ha => by
    rw [hρ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    exact map_nonunit (algebraMap A O) a ha
  -- `A → κ(O)` is surjective
  have hρs : Function.Surjective ρ := by
    intro w
    obtain ⟨⟨o, ho⟩, rfl⟩ := IsLocalRing.residue_surjective w
    have ho' : o ∈ Algebra.adjoin A {t, y} := hO ▸ ho
    induction ho' using Algebra.adjoin_induction with
    | mem p hp =>
      refine ⟨0, ?_⟩
      rw [map_zero, eq_comm, IsLocalRing.residue_eq_zero_iff, hmaxO]
      rcases hp with rfl | rfl
      · exact Ideal.subset_span (by simp)
      · exact Ideal.subset_span (by simp)
    | algebraMap a => exact ⟨a, rfl⟩
    | add p q hp hq ihp ihq =>
      obtain ⟨a, ha⟩ := ihp (hO ▸ hp)
      obtain ⟨b, hb⟩ := ihq (hO ▸ hq)
      refine ⟨a + b, ?_⟩
      rw [map_add, ha, hb, ← map_add]; rfl
    | mul p q hp hq ihp ihq =>
      obtain ⟨a, ha⟩ := ihp (hO ▸ hp)
      obtain ⟨b, hb⟩ := ihq (hO ▸ hq)
      refine ⟨a * b, ?_⟩
      rw [map_mul, ha, hb, ← map_mul]; rfl
  -- the map `C → κ(O)`
  let ψ : C →+* κ := (Ideal.Quotient.lift (RingHom.ker π) ρ fun a ha => hρm a (hker ha)).comp
    (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hψ : ∀ a, ψ (π a) = ρ a := fun a => by
    simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [show (RingHom.quotientKerEquivOfSurjective hπ).symm (π a) = Ideal.Quotient.mk _ a from
      (RingHom.quotientKerEquivOfSurjective hπ).symm_apply_eq.2 rfl]
    rfl
  letI : Algebra C κ := ψ.toAlgebra
  have : IsScalarTower k C κ := IsScalarTower.of_algebraMap_eq fun c => by
    change _ = ψ (algebraMap k C c)
    rw [← hπk, hψ, hρ, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply k A O]
    rfl
  have hψs : Function.Surjective (algebraMap C κ) := fun w => by
    obtain ⟨a, rfl⟩ := hρs w
    exact ⟨π a, hψ a⟩
  have hres := MMP.Fourfold.span_range_D_algebraMap_eq_top (k := k) hψs
    (show algebraMap C κ (π Y) = 0 by change ψ _ = 0; rw [hψ]; exact hρm Y hYm) hzC
  have hz : Submodule.span κ (Set.range fun i => KaehlerDifferential.D k κ
      (IsLocalRing.residue O (algebraMap A O (z i)))) = ⊤ := by
    rw [← hres]
    congr 2
    funext i
    change _ = KaehlerDifferential.D k κ (ψ (π (z i)))
    rw [hψ]
    rfl
  have h := KummerCover.span_D_eq_top_of_maximalIdeal (k := k) hmaxO (fun i => algebraMap A O (z i)) hz
  rw [Set.insert_union, Set.singleton_union] at h
  rw [Fin.range_cons, Fin.range_cons]
  exact h

end KummerCover

section Unramified2

open MvPowerSeries
open scoped TensorProduct

/-- `u^*(a ω^{⊗m}) = u(a) (u^*ω)^{⊗m}` for every top form `ω`, once the line of top forms has a
pull-back generator `ω₀`. -/
theorem pullbackForms_smul_formPow' {k : Type u} [Field k] {K K' : Type u} [Field K]
    [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}
    {ω₀ : ⋀[K]^d Ω[K⁄k]} (hω₀ : IsPullbackGenerator K' ω₀) (m : ℕ) (a : K)
    (ω : ⋀[K]^d Ω[K⁄k]) :
    pullbackForms (K' := K') (m : ℤ) (a • MMP.Fourfold.formPow ω m) =
      algebraMap K K' a • MMP.Fourfold.formPow (topFormsMap k K K' d ω) m := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hω₀.1 ▸ Submodule.mem_top (x := ω))
  rw [MMP.Fourfold.formPow_smul, smul_smul, MMP.Fourfold.pullbackForms_smul_formPow hω₀,
    LinearMap.map_smul, ← algebraMap_smul K' c (topFormsMap k K K' d ω₀),
    MMP.Fourfold.formPow_smul, smul_smul, map_mul, map_pow]

/-- **A Kummer cover is unramified where its radicands are units.** Let `B` be a localization of
`O = A₀[t, y]`, an algebra over `C` compatibly with `A₀ → C`, with `t^m = f` and `y t^a = g` for
`f, g ∈ A₀`. If `t` and `m` are units of `B`, then `C → B` is formally unramified. -/
theorem formallyUnramified_of_isLocalization_adjoin {A₀ C L B : Type*} [CommRing A₀]
    [CommRing C] [CommRing L] [CommRing B] [Algebra A₀ L] [Algebra C B]
    (O : Subalgebra A₀ L) [Algebra O B] (S : Submonoid O) [IsLocalization S B]
    (φ : A₀ →+* C) (hφ : ∀ a : A₀, algebraMap O B (algebraMap A₀ O a) = algebraMap C B (φ a))
    {t y : L} (hO : O = Algebra.adjoin A₀ {t, y}) (ht : t ∈ O) (hy : y ∈ O)
    {f g : A₀} {a m : ℕ} (htm : t ^ m = algebraMap A₀ L f) (hyt : y * t ^ a = algebraMap A₀ L g)
    (hmB : IsUnit ((m : ℕ) : B)) (htB : IsUnit (algebraMap O B ⟨t, ht⟩)) :
    Algebra.FormallyUnramified C B := by
  have hDt0 : KaehlerDifferential.D C B (algebraMap O B ⟨t, ht⟩) = 0 := by
    have h1 : KaehlerDifferential.D C B ((algebraMap O B ⟨t, ht⟩) ^ m) = 0 := by
      have : (algebraMap O B ⟨t, ht⟩) ^ m = algebraMap C B (φ f) := by
        rw [← map_pow, ← hφ]
        congr 1; exact Subtype.ext (by simp [htm])
      rw [this, Derivation.map_algebraMap]
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul B, smul_smul] at h1
    exact ((hmB.mul (htB.pow _)).smul_eq_zero).1 h1
  have hDy0 : KaehlerDifferential.D C B (algebraMap O B ⟨y, hy⟩) = 0 := by
    have h1 : KaehlerDifferential.D C B
        (algebraMap O B ⟨y, hy⟩ * (algebraMap O B ⟨t, ht⟩) ^ a) = 0 := by
      have : algebraMap O B ⟨y, hy⟩ * (algebraMap O B ⟨t, ht⟩) ^ a = algebraMap C B (φ g) := by
        rw [← map_pow, ← map_mul, ← hφ]
        congr 1; exact Subtype.ext (by simp [hyt])
      rw [this, Derivation.map_algebraMap]
    rw [Derivation.leibniz, Derivation.leibniz_pow, hDt0, smul_zero, smul_zero, smul_zero,
      zero_add] at h1
    exact ((htB.pow _).smul_eq_zero).1 h1
  refine ⟨⟨fun ω ω' => ?_⟩⟩
  have hD := KummerCover.derivation_eq_zero_of_adjoin (M := Ω[B⁄C]) O S φ hφ hO ht hy
    (KaehlerDifferential.D C B) hDt0 hDy0
  have h1 : ∀ w : Ω[B⁄C], w = 0 := by
    intro w
    have hw : w ∈ Submodule.span B (Set.range (KaehlerDifferential.D C B)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    rw [hD] at hw
    simpa using hw
  rw [h1 ω, h1 ω']

/-- A map `C → B` from the localization `C = A_𝔮` is local once every `a ∈ A` that becomes a unit
in `B` lies outside `𝔮`. -/
theorem isLocalHom_of_isLocalization_atPrime {A C B : Type*} [CommRing A] [CommRing C]
    [CommRing B] [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B] (𝔮 : Ideal A)
    [𝔮.IsPrime] (hloc : IsLocalization.AtPrime C 𝔮)
    (h : ∀ a : A, IsUnit (algebraMap A B a) → a ∈ 𝔮.primeCompl) : IsLocalHom (algebraMap C B) := by
  refine ⟨fun e he => ?_⟩
  obtain ⟨⟨a', s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl e
  have hs : IsUnit (algebraMap A B s) := by
    rw [IsScalarTower.algebraMap_apply A C B]
    exact (IsLocalization.map_units C s).map _
  have h1 : algebraMap C B (IsLocalization.mk' C a' s) * algebraMap A B s = algebraMap A B a' := by
    rw [IsScalarTower.algebraMap_apply A C B s, ← map_mul, IsLocalization.mk'_spec,
      ← IsScalarTower.algebraMap_apply]
  have ha' := h a' (h1 ▸ he.mul hs)
  have h3 := IsLocalization.mk'_spec C a' s
  exact isUnit_of_mul_isUnit_left (h3 ▸ IsLocalization.map_units C ⟨a', ha'⟩)

/-- A local, essentially finite type, formally unramified extension `B` of a discrete valuation
ring `C` which is a noetherian domain and not a field is a discrete valuation ring, with the
uniformizer of `C` as uniformizer. -/
theorem isDiscreteValuationRing_of_formallyUnramified {C B : Type*} [CommRing C]
    [CommRing B] [IsDomain B] [Algebra C B] [IsLocalRing C] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra.FormallyUnramified C B] [Algebra.EssFiniteType C B] [IsLocalHom (algebraMap C B)]
    {ϖ : C} (hmax : IsLocalRing.maximalIdeal C = Ideal.span {ϖ}) (h0 : algebraMap C B ϖ ≠ 0) :
    IsDiscreteValuationRing B := by
  have hmaxB : IsLocalRing.maximalIdeal B = Ideal.span {algebraMap C B ϖ} := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := C) (S := B), hmax, Ideal.map_span,
      Set.image_singleton]
  have hnf : ¬ IsField B := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmaxB, Ideal.span_singleton_eq_bot]
    exact h0
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 1 5).2
    (⟨⟨_, hmaxB⟩⟩ : (IsLocalRing.maximalIdeal B).IsPrincipal)
/-- The order of the pull-back of `θ = (df ∧ dY ∧ dz)^{⊗m}` along the localization `B` of a
Kummer cover `O = A[t, y]` over a prime where `t` and `m` are units: there
`df ∧ dY ∧ dz = m² (t y)^{m-1} dt ∧ dy ∧ dz`, so the order is `(m - 1) v(Y)` for a valuation
`v` of `K` that `B` extends. -/
theorem ordAt_pullbackForms_eq_of_kummerCover_of_charZero {k : Type} [Field k] [CharZero k]
    {A C K L B : Type} [CommRing A] [IsDomain A]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Field K] [Field L]
    [Algebra k A] [Algebra k C] [Algebra k K] [Algebra A C] [Algebra A K] [Algebra C K]
    [IsFractionRing A K] [IsFractionRing C K] [IsScalarTower A C K] [IsScalarTower k A K]
    [IsScalarTower k C K] [IsScalarTower k A C]
    (𝔮 : Ideal A) [𝔮.IsPrime] [IsLocalization.AtPrime C 𝔮]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    [Algebra k L] [IsScalarTower k K L] [IsScalarTower k A L]
    (O : Subalgebra A L) [IsLocalRing O] [IsNoetherianRing O] [Module.Finite A O]
    [Algebra k O] [IsScalarTower k A O] [IsScalarTower k O L]
    (𝔔 : Ideal O) [𝔔.IsPrime]
    [CommRing B] [IsDomain B] [Algebra O B] [IsLocalization.AtPrime B 𝔔]
    [Algebra B L] [IsScalarTower O B L] [IsFractionRing B L] [Algebra k B] [IsScalarTower k O B]
    [IsScalarTower k B L] [Algebra A B] [IsScalarTower A O B] [IsScalarTower A B L]
    [Algebra C B] [IsScalarTower A C B] [IsScalarTower k C B]
    {t y : L} (ht : t ∈ O) (hy : y ∈ O)
    {f Y : A} {m : ℕ} (hm : 0 < m) (hY0 : Y ≠ 0) (htm : t ^ m = algebraMap A L f)
    (hym : y ^ m = algebraMap A L Y) (htB : IsUnit (algebraMap O B ⟨t, ht⟩))
    (hmB : IsUnit ((m : ℕ) : B)) {d : ℕ} (z : Fin d → A)
    (hframe : Submodule.span O (Set.range (Fin.cons (KaehlerDifferential.D k O ⟨t, ht⟩)
        (Fin.cons (KaehlerDifferential.D k O ⟨y, hy⟩) fun i =>
          KaehlerDifferential.D k O (algebraMap _ O (z i))) : Fin (d + 1 + 1) → Ω[O⁄k])) = ⊤)
    [FiniteDimensional K Ω[K⁄k]]
    {v : K → ℤ} (θ : PluriForms k K (d + 1 + 1) m)
    (hθ : θ = (PiTensorProduct.tprod K (fun _ : Fin m =>
        exteriorPower.ιMulti K (d + 1 + 1)
          (Fin.cons (KaehlerDifferential.D k K (algebraMap _ K f))
            fun i => KaehlerDifferential.D k K (algebraMap _ K
              ((Fin.cons Y z : Fin (d + 1) → A) i)))) :
        TensorPower K m (⋀[K]^(d + 1 + 1) Ω[K⁄k])))
    {ω₀ : ⋀[K]^(d + 1 + 1) Ω[K⁄k]} (hω₀ : IsPullbackGenerator (k := k) L ω₀)
    [IsNoetherianRing B] [IsDiscreteValuationRing B] [Nontrivial (⋀[K]^(d + 1 + 1) Ω[K⁄k])]
    [Nontrivial (⋀[L]^(d + 1 + 1) Ω[L⁄k])]
    (hvv : ∀ f : K, f ≠ 0 → WithZero.log (Ring.ordFrac B (algebraMap K L f)) = v f) :
    ordAt (k := k) B (fun c => WithZero.log (Ring.ordFrac B c))
      (pullbackForms (K' := L) (m : ℤ) θ) = (m - 1 : ℕ) * v (algebraMap A K Y) := by
  have hinjAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective _ _)
  -- the frame `dt, dy, dz` of `Ω_{B/k}`
  have hsO : Submodule.span O (Set.range fun i => KaehlerDifferential.D k O
      ((Fin.cons ⟨t, ht⟩ (Fin.cons ⟨y, hy⟩ fun i => algebraMap _ O (z i)) :
        Fin (d + 1 + 1) → O) i)) = ⊤ := by
    rw [← hframe]
    congr 2
    funext i
    refine Fin.cases rfl (fun i => Fin.cases rfl (fun i => rfl) i) i
  have hsB := KummerCover.span_map_eq_top_of_isLocalization (k := k) (B := B)
    𝔔.primeCompl _ hsO
  have hσB := MMP.Fourfold.span_singleton_ιMulti_eq_top _ hsB
  have h0B := topFormsMap_ne_zero_of_span_eq_top (K := L) hσB
  have hmul' : ∀ a b : L, a ≠ 0 → b ≠ 0 →
      WithZero.log (Ring.ordFrac (B) (a * b)) =
        WithZero.log (Ring.ordFrac (B) a) +
          WithZero.log (Ring.ordFrac (B) b) := fun a b ha hb => by
    rw [map_mul]
    exact WithZero.log_mul ((map_ne_zero _).2 ha) ((map_ne_zero _).2 hb)
  have hunit' : ∀ c : B, IsUnit c →
      WithZero.log (Ring.ordFrac (B) (algebraMap _ L c)) = 0 :=
    fun c hc => by rw [Ring.ordFrac_of_isUnit (K := L) hc, WithZero.log_one]
  rw [ordAt_eq hmul' hunit' hσB h0B]
  -- the pull-back of `θ`
  have htL : algebraMap (B) L (algebraMap O _ ⟨t, ht⟩) = t := by
    rw [← IsScalarTower.algebraMap_apply]; rfl
  have hyL : algebraMap (B) L (algebraMap O _ ⟨y, hy⟩) = y := by
    rw [← IsScalarTower.algebraMap_apply]; rfl
  have hzL : ∀ a : A, algebraMap (B) L
      (algebraMap O _ (algebraMap _ O a)) = algebraMap (A) L a := fun a => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hKL : ∀ a : A, algebraMap K L (algebraMap _ _ a) =
      algebraMap (A) L a := fun a =>
    (IsScalarTower.algebraMap_apply (A) K L a).symm
  have hω0L : topFormsMap k K L (d + 1 + 1)
      (exteriorPower.ιMulti K (d + 1 + 1)
        (Fin.cons (KaehlerDifferential.D k K (algebraMap _ K f))
          fun i => KaehlerDifferential.D k K (algebraMap _ K
            ((Fin.cons Y z : Fin (d + 1) → A) i)))) =
      algebraMap (B) L
        (((m : ℕ) * (algebraMap O _ ⟨t, ht⟩) ^ (m - 1)) *
          ((m : ℕ) * (algebraMap O _ ⟨y, hy⟩) ^ (m - 1))) •
      topFormsMap k (B) L (d + 1 + 1)
        (exteriorPower.ιMulti _ (d + 1 + 1) fun i => KaehlerDifferential.D k _
          (algebraMap O (B)
            ((Fin.cons ⟨t, ht⟩ (Fin.cons ⟨y, hy⟩ fun i => algebraMap _ O (z i)) :
              Fin (d + 1 + 1) → O) i))) := by
    rw [topFormsMap_ιMulti, topFormsMap_ιMulti]
    have hv : (fun i => KaehlerDifferential.map k k K L
        ((Fin.cons (KaehlerDifferential.D k K (algebraMap _ K f))
          fun i => KaehlerDifferential.D k K (algebraMap _ K
            ((Fin.cons Y z : Fin (d + 1) → A) i)) :
              Fin (d + 1 + 1) → Ω[K⁄k]) i)) =
        (Fin.cons (((m : ℕ) * t ^ (m - 1)) • KaehlerDifferential.D k L t)
          (Fin.cons (((m : ℕ) * y ^ (m - 1)) • KaehlerDifferential.D k L y)
            fun i => KaehlerDifferential.D k L (algebraMap (A) L (z i))) :
          Fin (d + 1 + 1) → Ω[L⁄k]) := by
      funext i
      refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
      · simp only [Fin.cons_zero, KaehlerDifferential.map_D, hKL, ← htm, Derivation.leibniz_pow,
          ← Nat.cast_smul_eq_nsmul L, smul_smul]
      · simp only [Fin.cons_succ, Fin.cons_zero, KaehlerDifferential.map_D, hKL, ← hym,
          Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul L, smul_smul]
      · simp only [Fin.cons_succ, KaehlerDifferential.map_D, hKL]
    have hv' : (fun i => KaehlerDifferential.map k k (B) L
        (KaehlerDifferential.D k _ (algebraMap O (B)
          ((Fin.cons ⟨t, ht⟩ (Fin.cons ⟨y, hy⟩ fun i => algebraMap _ O (z i)) :
            Fin (d + 1 + 1) → O) i)))) =
        (Fin.cons (KaehlerDifferential.D k L t) (Fin.cons (KaehlerDifferential.D k L y)
            fun i => KaehlerDifferential.D k L (algebraMap (A) L (z i))) :
          Fin (d + 1 + 1) → Ω[L⁄k]) := by
      funext i
      refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
      · simp only [Fin.cons_zero, KaehlerDifferential.map_D, htL]
      · simp only [Fin.cons_succ, Fin.cons_zero, KaehlerDifferential.map_D, hyL]
      · simp only [Fin.cons_succ, KaehlerDifferential.map_D, hzL]
    rw [hv, hv', KummerCover.ιMulti_cons_cons_smul]
    congr 1
    simp only [map_mul, map_pow, map_natCast, htL, hyL]
  have hθ' : θ = (1 : K) • MMP.Fourfold.formPow
      (exteriorPower.ιMulti K (d + 1 + 1)
        (Fin.cons (KaehlerDifferential.D k K (algebraMap _ K f))
          fun i => KaehlerDifferential.D k K (algebraMap _ K
            ((Fin.cons Y z : Fin (d + 1) → A) i)))) m := by
    rw [one_smul, hθ]; rfl
  rw [hθ', pullbackForms_smul_formPow' hω₀ m 1, map_one, one_smul, hω0L,
    MMP.Fourfold.formPow_smul, formCoeff_smul]
  have hfc : ∀ (σ : ⋀[B]^(d + 1 + 1) Ω[B⁄k])
      (hσ : Submodule.span (B) {σ} = ⊤)
      (h0 : topFormsMap k (B) L (d + 1 + 1) σ ≠ 0),
      formCoeff (k := k) (m := (m : ℤ)) (B) hσ h0
        (MMP.Fourfold.formPow (topFormsMap k (B) L (d + 1 + 1) σ) m) = 1 := by
    intro σ hσ h0
    have hb := ZTensorPower.basis_ofNat (topFormsBasis (B) hσ h0) m
    simp only [topFormsBasis_apply] at hb
    have h1 : MMP.Fourfold.formPow (topFormsMap k (B) L (d + 1 + 1) σ) m =
        ZTensorPower.basis (topFormsBasis (B) hσ h0) (m : ℤ) () := hb.symm
    rw [h1]
    simp [formCoeff]
  rw [hfc _ hσB h0B, mul_one]
  -- the valuation of `B`
  have hyB0 : algebraMap (B) L (algebraMap O _ ⟨y, hy⟩) ≠ 0 := by
    rw [hyL]
    intro h0
    apply hY0
    apply hinjAL
    rw [← hym, h0, zero_pow (by omega), map_zero]
  have hYv := hvv (algebraMap _ K Y)
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hY0)
  rw [hKL, ← hym, ← hyL, map_pow (Ring.ordFrac (B)), WithZero.log_pow]
    at hYv
  have hc : algebraMap (B) L
      (((m : ℕ) * (algebraMap O _ ⟨t, ht⟩) ^ (m - 1)) *
        ((m : ℕ) * (algebraMap O _ ⟨y, hy⟩) ^ (m - 1))) =
      algebraMap (B) L
        ((m : ℕ) * (algebraMap O _ ⟨t, ht⟩) ^ (m - 1) * (m : ℕ)) *
      algebraMap (B) L (algebraMap O _ ⟨y, hy⟩) ^ (m - 1) := by
    rw [← map_pow (algebraMap (B) L),
      ← map_mul (algebraMap (B) L)]
    congr 1; ring
  have hu0 : IsUnit ((m : ℕ) * (algebraMap O (B) ⟨t, ht⟩) ^ (m - 1) *
      (m : ℕ)) := (hmB.mul (htB.pow _)).mul hmB
  rw [map_pow (Ring.ordFrac (B)), WithZero.log_pow, hc,
    hmul' _ _ ((hu0.map _).ne_zero) (pow_ne_zero _ hyB0), hunit' _ hu0, zero_add,
    map_pow (Ring.ordFrac (B)), WithZero.log_pow, ← hYv]
  simp only [nsmul_eq_mul]
  ring

/-- **The order along `C` of the comparison form of a Kummer cover**, from its order along the
localization `B` of the cover, which is a discrete valuation ring unramified over `C`. -/
theorem ordAt_eq_of_kummerCover_localization_of_charZero {k : Type} [Field k] [CharZero k]
    {A C K L B : Type} [CommRing A] [IsDomain A]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Field K] [Field L]
    [Algebra k A] [Algebra k C] [Algebra k K] [Algebra A C] [Algebra A K] [Algebra C K]
    [IsFractionRing A K] [IsFractionRing C K] [IsScalarTower A C K] [IsScalarTower k A K]
    [IsScalarTower k C K] [IsScalarTower k A C]
    (𝔮 : Ideal A) [𝔮.IsPrime] [IsLocalization.AtPrime C 𝔮]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    [Algebra k L] [IsScalarTower k K L] [IsScalarTower k A L]
    (O : Subalgebra A L) [IsLocalRing O] [IsNoetherianRing O] [Module.Finite A O]
    [Algebra k O] [IsScalarTower k A O] [IsScalarTower k O L]
    (𝔔 : Ideal O) [𝔔.IsPrime] (h𝔔𝔮 : 𝔔.comap (algebraMap A O) = 𝔮)
    [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra O B] [IsLocalization.AtPrime B 𝔔]
    [Algebra B L] [IsScalarTower O B L] [IsFractionRing B L] [Algebra k B] [IsScalarTower k O B]
    [IsScalarTower k B L] [Algebra A B] [IsScalarTower A O B] [IsScalarTower A B L]
    [Algebra C B] [IsScalarTower A C B] [IsScalarTower k C B]
    (hcomp : ∀ e : C, algebraMap K L (algebraMap C K e) = algebraMap B L (algebraMap C B e))
    {t y : L} (ht : t ∈ O) (hy : y ∈ O) (hO : O = Algebra.adjoin A {t, y})
    {f g Y : A} {a m : ℕ} (hm : 0 < m) (hY0 : Y ≠ 0)
    (htm : t ^ m = algebraMap A L f) (hyt : y * t ^ a = algebraMap A L g)
    (hym : y ^ m = algebraMap A L Y) (htB : IsUnit (algebraMap O B ⟨t, ht⟩))
    (hmB : IsUnit ((m : ℕ) : B)) {d : ℕ} (z : Fin d → A)
    (hframe : Submodule.span O (Set.range (Fin.cons (KaehlerDifferential.D k O ⟨t, ht⟩)
        (Fin.cons (KaehlerDifferential.D k O ⟨y, hy⟩) fun i =>
          KaehlerDifferential.D k O (algebraMap _ O (z i))) : Fin (d + 1 + 1) → Ω[O⁄k])) = ⊤)
    (hKrank : Module.finrank K Ω[K⁄k] = d + 1 + 1) [FiniteDimensional K Ω[K⁄k]]
    {v : K → ℤ} (θ : PluriForms k K (d + 1 + 1) m)
    (hθ : θ = (PiTensorProduct.tprod K (fun _ : Fin m =>
        exteriorPower.ιMulti K (d + 1 + 1)
          (Fin.cons (KaehlerDifferential.D k K (algebraMap _ K f))
            fun i => KaehlerDifferential.D k K (algebraMap _ K
              ((Fin.cons Y z : Fin (d + 1) → A) i)))) :
        TensorPower K m (⋀[K]^(d + 1 + 1) Ω[K⁄k])))
    {ϖE : C} (hϖE : Irreducible ϖE) {xE : Fin (d + 1) → C}
    (hxE : Submodule.span C (Set.range (Fin.cons (KaehlerDifferential.D k C ϖE)
      fun i => KaehlerDifferential.D k C (xE i) : Fin (d + 1 + 1) → Ω[C⁄k])) = ⊤)
    (hmul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ c : C, IsUnit c → v (algebraMap C K c) = 0) (hvϖ : v (algebraMap C K ϖE) = 1)
    (hθ0 : θ ≠ 0) :
    ordAt (k := k) C v θ = (m - 1 : ℕ) * v (algebraMap A K Y) := by
  -- `C → B` is formally unramified, local and essentially of finite type
  have hunr : Algebra.FormallyUnramified C B :=
    formallyUnramified_of_isLocalization_adjoin O 𝔔.primeCompl (algebraMap A C)
      (fun a => by
        rw [← IsScalarTower.algebraMap_apply A O B]
        exact IsScalarTower.algebraMap_apply A C B a)
      hO ht hy htm hyt hmB htB
  have : IsLocalHom (algebraMap C B) :=
    isLocalHom_of_isLocalization_atPrime 𝔮 inferInstance fun a h2 => by
      rw [IsScalarTower.algebraMap_apply A O B, IsLocalization.AtPrime.isUnit_to_map_iff _ 𝔔] at h2
      exact fun h => h2 (by rwa [← h𝔔𝔮] at h)
  have : Algebra.EssFiniteType A B := by
    have : Algebra.EssFiniteType O B := Algebra.EssFiniteType.of_isLocalization _ 𝔔.primeCompl
    exact Algebra.EssFiniteType.comp _ O _
  have : Algebra.EssFiniteType C B := Algebra.EssFiniteType.of_comp A _ _
  -- `B` is a discrete valuation ring with uniformizer that of `C`
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing 𝔔.primeCompl _ inferInstance
  have hmaxE := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖE).1 hϖE
  have hϖB0 : algebraMap C B ϖE ≠ 0 := by
    intro h0
    have := hcomp ϖE
    rw [h0, map_zero] at this
    exact (map_ne_zero_iff _ (algebraMap K L).injective).2
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hϖE.ne_zero) this
  haveI : IsDiscreteValuationRing B := isDiscreteValuationRing_of_formallyUnramified hmaxE hϖB0
  -- top forms of `K` and `L`
  have : Nontrivial (⋀[K]^(d + 1 + 1) Ω[K⁄k]) := nontrivial_exteriorPower_of_finrank_eq k K hKrank
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable _ _
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_formallyEtale (k := k) (K' := L) hKrank
  have : Nontrivial (⋀[L]^(d + 1 + 1) Ω[L⁄k]) := ⟨⟨_, 0, hω₀.2.2⟩⟩
  obtain ⟨key, hvv⟩ := ordAt_pullbackForms_eq_of_formallyUnramified (k := k)
    (C := C) (B := B) (F := K) (L := L) hcomp hϖE hxE hmul hunit hvϖ m θ hθ0
  exact key.symm.trans (ordAt_pullbackForms_eq_of_kummerCover_of_charZero (C := C) 𝔮 O 𝔔 ht hy hm
      hY0 htm
    hym htB hmB z hframe θ hθ hω₀ hvv)

/-- **The comparison form along a divisor where a Kummer cover is étale**, for an abstract
discrete valuation ring. Let `C = A_𝔮` be a discrete valuation ring with fraction field `K`,
`O = A[t, y] ⊆ L` a finite local cover of `A` with `t^m = f`, `y t^a = g`, `y^m = Y` and a frame
`dt, dy, dz` of `Ω_{O/k}`, and `f ∉ 𝔮`. For a valuation `v` of `K` normalized by a uniformizer
`ϖ` of `C` with `dϖ, dx` a frame of `Ω_{C/k}`, the form `θ = (df ∧ dY ∧ dz)^{⊗m}` has order
`(m - 1) v(Y)` along `C`: the localization `B` of `O` over `𝔮` is unramified over `C`, and in
`B` one has `df ∧ dY ∧ dz = m² (t y)^{m-1} dt ∧ dy ∧ dz`. -/
theorem ordAt_eq_of_unramifiedCover_of_charZero {k : Type} [Field k] [CharZero k]
    {A C K L : Type} [CommRing A] [IsDomain A]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Field K] [Field L]
    [Algebra k A] [Algebra k C] [Algebra k K] [Algebra A C] [Algebra A K] [Algebra C K]
    [IsFractionRing A K] [IsFractionRing C K] [IsScalarTower A C K] [IsScalarTower k A K]
    [IsScalarTower k C K] [IsScalarTower k A C]
    (𝔮 : Ideal A) [𝔮.IsPrime] [IsLocalization.AtPrime C 𝔮]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (O : Subalgebra A L) [IsLocalRing O] [IsNoetherianRing O] [Module.Finite A O]
    {t y : L} (ht : t ∈ O) (hy : y ∈ O) (hO : O = Algebra.adjoin A {t, y})
    (hfrac : ∀ l : L, ∃ (o : L) (s : A), o ∈ O ∧ s ≠ 0 ∧ algebraMap A L s * l = o)
    {f g Y : A} {a m : ℕ} (hm : 0 < m) (hf𝔮 : f ∉ 𝔮) (hY0 : Y ≠ 0)
    (htm : t ^ m = algebraMap A L f) (hyt : y * t ^ a = algebraMap A L g)
    (hym : y ^ m = algebraMap A L Y) {d : ℕ} (z : Fin d → A)
    (hframe : letI : Algebra k O := ((algebraMap A O).comp (algebraMap k A)).toAlgebra
      Submodule.span O (Set.range (Fin.cons (KaehlerDifferential.D k O ⟨t, ht⟩)
        (Fin.cons (KaehlerDifferential.D k O ⟨y, hy⟩) fun i =>
          KaehlerDifferential.D k O (algebraMap _ O (z i))) : Fin (d + 1 + 1) → Ω[O⁄k])) = ⊤)
    (hKrank : Module.finrank K Ω[K⁄k] = d + 1 + 1) [FiniteDimensional K Ω[K⁄k]]
    {ϖE : C} (hϖE : Irreducible ϖE) {xE : Fin (d + 1) → C}
    (hxE : Submodule.span C (Set.range (Fin.cons (KaehlerDifferential.D k C ϖE)
      fun i => KaehlerDifferential.D k C (xE i) : Fin (d + 1 + 1) → Ω[C⁄k])) = ⊤)
    {v : K → ℤ} (hmul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ c : C, IsUnit c → v (algebraMap C K c) = 0) (hvϖ : v (algebraMap C K ϖE) = 1)
    (θ : PluriForms k K (d + 1 + 1) m)
    (hθ : θ = (PiTensorProduct.tprod K (fun _ : Fin m =>
        exteriorPower.ιMulti K (d + 1 + 1)
          (Fin.cons (KaehlerDifferential.D k K (algebraMap _ K f))
            fun i => KaehlerDifferential.D k K (algebraMap _ K
              ((Fin.cons Y z : Fin (d + 1) → A) i)))) :
        TensorPower K m (⋀[K]^(d + 1 + 1) Ω[K⁄k])))
    (hθ0 : θ ≠ 0) :
    ordAt (k := k) C v θ = (m - 1 : ℕ) * v (algebraMap A K Y) := by
  classical
  letI : Algebra k O := ((algebraMap A O).comp (algebraMap k A)).toAlgebra
  have : IsScalarTower k A O := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k A L := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply k A K]
    rfl
  have : IsScalarTower k O L := IsScalarTower.of_algebraMap_eq fun c => by
    change _ = algebraMap A L (algebraMap k _ c)
    rw [← IsScalarTower.algebraMap_apply k A L]
  -- a prime `𝔔` of `O` over `𝔮`
  have hinjAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective _ _)
  have hinjAO : Function.Injective (algebraMap A O) := fun a b h =>
    hinjAL (congrArg Subtype.val h)
  have : Algebra.IsIntegral A O := Algebra.IsIntegral.of_finite _ _
  obtain ⟨𝔔, -, h𝔔, h𝔔𝔮⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔮 (⊥ : Ideal O) (by
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_bot, ← map_zero (algebraMap A O)] at ha
    rw [hinjAO ha]; exact 𝔮.zero_mem)
  -- the localization `B = O_𝔔`
  have hO0 : ∀ s : 𝔔.primeCompl, IsUnit (algebraMap O L s) := fun s => by
    refine isUnit_iff_ne_zero.2 fun h => s.2 ?_
    have : (s : O) = 0 := Subtype.ext h
    rw [this]; exact 𝔔.zero_mem
  letI : Algebra (Localization.AtPrime 𝔔) L :=
    (IsLocalization.lift (M := 𝔔.primeCompl) (S := Localization.AtPrime 𝔔) hO0).toAlgebra
  have : IsScalarTower O (Localization.AtPrime 𝔔) L :=
    IsScalarTower.of_algebraMap_eq fun o => (IsLocalization.lift_eq hO0 o).symm
  have : IsScalarTower k (Localization.AtPrime 𝔔) L := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k O (Localization.AtPrime 𝔔),
      ← IsScalarTower.algebraMap_apply O (Localization.AtPrime 𝔔) L,
      ← IsScalarTower.algebraMap_apply k O L]
  have : IsScalarTower A (Localization.AtPrime 𝔔) L :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply A O (Localization.AtPrime 𝔔),
        ← IsScalarTower.algebraMap_apply O (Localization.AtPrime 𝔔) L,
        ← IsScalarTower.algebraMap_apply A O L]
  have : FaithfulSMul O L := (faithfulSMul_iff_algebraMap_injective O L).2 Subtype.val_injective
  have : IsFractionRing O L := IsFractionRing.of_field O L fun l => by
    obtain ⟨o, s, ho, hs, hsl⟩ := hfrac l
    refine ⟨⟨o, ho⟩, algebraMap _ O s, ?_⟩
    have hs' : algebraMap A L s ≠ 0 := (map_ne_zero_iff _ hinjAL).2 hs
    change l = o / algebraMap A L s
    rw [eq_div_iff hs', mul_comm, hsl]
  have : IsFractionRing (Localization.AtPrime 𝔔) L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔔.primeCompl _ L
  -- `C → B`
  have hAE : ∀ s : 𝔮.primeCompl, IsUnit (algebraMap A (Localization.AtPrime 𝔔) s) := fun s => by
    rw [IsScalarTower.algebraMap_apply A O (Localization.AtPrime 𝔔)]
    refine (IsLocalization.AtPrime.isUnit_to_map_iff _ 𝔔 _).2 fun h => s.2 ?_
    have h' : (s : A) ∈ 𝔔.under A := h
    rwa [h𝔔𝔮] at h'
  letI : Algebra C (Localization.AtPrime 𝔔) :=
    (IsLocalization.lift (M := 𝔮.primeCompl) (S := C) hAE).toAlgebra
  have : IsScalarTower A C (Localization.AtPrime 𝔔) :=
    IsScalarTower.of_algebraMap_eq fun a => (IsLocalization.lift_eq hAE a).symm
  have : IsScalarTower k C (Localization.AtPrime 𝔔) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k A C, ← IsScalarTower.algebraMap_apply A C,
        IsScalarTower.algebraMap_apply A O (Localization.AtPrime 𝔔),
        IsScalarTower.algebraMap_apply k O (Localization.AtPrime 𝔔)]
      rfl
  have hcomp : ∀ e : C, algebraMap K L (algebraMap C K e) =
      algebraMap (Localization.AtPrime 𝔔) L (algebraMap C (Localization.AtPrime 𝔔) e) := by
    intro e
    have h := IsLocalization.ringHom_ext 𝔮.primeCompl
      (j := (algebraMap K L).comp (algebraMap C K))
      (k := (algebraMap (Localization.AtPrime 𝔔) L).comp (algebraMap C (Localization.AtPrime 𝔔)))
      (by
        ext a
        simp only [RingHom.comp_apply]
        rw [← IsScalarTower.algebraMap_apply A C K, ← IsScalarTower.algebraMap_apply A C
          (Localization.AtPrime 𝔔), ← IsScalarTower.algebraMap_apply A K L,
          ← IsScalarTower.algebraMap_apply A (Localization.AtPrime 𝔔) L])
    exact congrArg (fun φ => φ e) h
  -- `t` is a unit along `C`
  have htE : (⟨t, ht⟩ : O) ∉ 𝔔 := by
    intro htQ
    have hfQ : algebraMap A O f ∈ 𝔔 := by
      have : algebraMap A O f = (⟨t, ht⟩ : O) ^ m := Subtype.ext (by simp [htm])
      rw [this]; exact Ideal.pow_mem_of_mem 𝔔 htQ m (by omega)
    exact hf𝔮 (by rwa [← h𝔔𝔮])
  have htB : IsUnit (algebraMap O (Localization.AtPrime 𝔔) ⟨t, ht⟩) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff _ 𝔔 _).2 htE
  have hmB : IsUnit ((m : ℕ) : Localization.AtPrime 𝔔) := by
    have h : ((m : ℕ) : Localization.AtPrime 𝔔) = algebraMap k _ ((m : ℕ) : k) := by simp
    rw [h]
    exact (IsUnit.mk0 _ (by exact_mod_cast (show m ≠ 0 by omega))).map _
  exact ordAt_eq_of_kummerCover_localization_of_charZero 𝔮 O 𝔔 h𝔔𝔮 hcomp ht hy hO hm hY0 htm hyt
      hym htB
    hmB z hframe hKrank θ hθ hϖE hxE hmul hunit hvϖ hθ0

/-- **The comparison form along a divisor where the cover is étale.** Let `O = A[t, y] ⊆ L` be a
cover of `A = 𝒪_{X,x}` with `t^m = f`, `y t^a = g`, `y^m = Y` and a frame `dt, dy, dz` of
`Ω_{O/k}`. Along a prime divisor `E ∋ x` on which `f` is a unit, the form
`θ = (df ∧ dY ∧ dz)^{⊗m}` has order `(m - 1) ord_E Y`: the cover is unramified over `E`, and
there `df ∧ dY ∧ dz = m² (t y)^{m-1} dt ∧ dy ∧ dz`. -/
theorem ordForm_eq_of_unramifiedCover_of_charZero {k : Type} [Field k] [CharZero k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [IsNormal X] [IsLocallyNoetherian X] [LocallyOfFiniteType sX] {d : ℕ}
    (hd : (letI := functionFieldAlgebra sX; Algebra.trdeg k X.functionField).toNat = d + 1 + 1)
    (x : X) {L : Type} [Field L] [Algebra X.functionField L] [Algebra (X.presheaf.stalk x) L]
    [IsScalarTower (X.presheaf.stalk x) X.functionField L] [FiniteDimensional X.functionField L]
    (O : Subalgebra (X.presheaf.stalk x) L) [IsLocalRing O] [IsNoetherianRing O]
    [Module.Finite (X.presheaf.stalk x) O]
    {t y : L} (ht : t ∈ O) (hy : y ∈ O) (hO : O = Algebra.adjoin (X.presheaf.stalk x) {t, y})
    (hfrac : ∀ l : L, ∃ (o : L) (s : X.presheaf.stalk x), o ∈ O ∧ s ≠ 0 ∧
      algebraMap _ L s * l = o)
    {f g Y : X.presheaf.stalk x} {a m : ℕ} (hm : 0 < m) (hf0 : f ≠ 0) (hY0 : Y ≠ 0)
    (htm : t ^ m = algebraMap _ L f) (hyt : y * t ^ a = algebraMap _ L g)
    (hym : y ^ m = algebraMap _ L Y) (z : Fin d → X.presheaf.stalk x)
    (hframe : letI := stalkAlgebra sX x
      letI : Algebra k O := ((algebraMap (X.presheaf.stalk x) O).comp (algebraMap k _)).toAlgebra
      Submodule.span O (Set.range (Fin.cons (KaehlerDifferential.D k O ⟨t, ht⟩)
        (Fin.cons (KaehlerDifferential.D k O ⟨y, hy⟩) fun i =>
          KaehlerDifferential.D k O (algebraMap _ O (z i))) : Fin (d + 1 + 1) → Ω[O⁄k])) = ⊤)
    (E : MMP.Mori.PrimeDivisor X) (hE : x ∈ E.support)
    (hfE : X.ord (algebraMap _ X.functionField f) E.genericPoint = 0)
    (θ : RationalPluriForms sX (d + 1 + 1) m)
    (hθ : letI := functionFieldAlgebra sX
      θ = (PiTensorProduct.tprod X.functionField (fun _ : Fin m =>
        exteriorPower.ιMulti X.functionField (d + 1 + 1)
          (Fin.cons (KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField f))
            fun i => KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField
              ((Fin.cons Y z : Fin (d + 1) → X.presheaf.stalk x) i)))) :
        TensorPower X.functionField m (⋀[X.functionField]^(d + 1 + 1) Ω[X.functionField⁄k])))
    (hθ0 : θ ≠ 0) :
    E.ordForm θ = (m - 1 : ℕ) * X.ord (algebraMap _ X.functionField Y) E.genericPoint := by
  classical
  letI := stalkAlgebra sX x
  letI := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX x
  -- the local ring `A_E = 𝒪_{X,E}` and the prime of `A` below it
  have hsp : E.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hE
  letI := stalkAlgebra sX E.genericPoint
  have := isScalarTower_stalk_functionField sX E.genericPoint
  letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk E.genericPoint) :=
    (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
  have := MMP.Fourfold.isScalarTower_stalkSpecializes (sY := sX) hsp
  have : IsScalarTower (X.presheaf.stalk x) (X.presheaf.stalk E.genericPoint) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => (MMP.Mori.algebraMap_stalkSpecializes hsp a).symm
  have hlocE := MMP.Intersection.isLocalization_stalkSpecializes hsp
  set 𝔮 := (IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint)).comap
    (X.presheaf.stalkSpecializes hsp).hom with h𝔮
  haveI : 𝔮.IsPrime := Ideal.comap_isPrime _ _
  haveI : IsLocalization.AtPrime (X.presheaf.stalk E.genericPoint) 𝔮 := hlocE
  have hdvrE : IsDiscreteValuationRing E.localRing := E.isDiscreteValuationRing_localRing
  have hf𝔮 : f ∉ 𝔮 := by
    intro hf𝔮
    rcases (mem_maximalIdeal_iff_ord E rfl _).1 hf𝔮 with h | h
    · exact hf0 (MMP.Intersection.stalkSpecializes_injective hsp (h.trans (map_zero _).symm))
    · rw [MMP.Mori.algebraMap_stalkSpecializes hsp, hfE] at h; simp at h
  -- a frame `dϖ_E, dx_E` of `Ω_{A_E/k}`
  obtain ⟨ϖE, hϖE⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  have hmaxE := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖE).1 hϖE
  -- a frame `dϖ_E, dx_E` of `Ω_{A_E/k}`
  obtain ⟨hfreeE, hfinE⟩ := E.free_kaehlerDifferential_localRing (sX := sX)
  obtain ⟨hfsE, hessE⟩ := E.formallySmooth_localRing (sX := sX)
  have hrankE := E.finrank_kaehlerDifferential_localRing (sX := sX)
  rw [hd] at hrankE
  have : Algebra.EssFiniteType k (IsLocalRing.ResidueField E.localRing) :=
    Algebra.EssFiniteType.of_surjective (IsScalarTower.toAlgHom k E.localRing _)
      IsLocalRing.residue_surjective
  have hkerκ : RingHom.ker (algebraMap E.localRing (IsLocalRing.ResidueField E.localRing)) =
      IsLocalRing.maximalIdeal E.localRing := IsLocalRing.ker_residue
  have hϖE2 : ϖE ∉ IsLocalRing.maximalIdeal E.localRing ^ 2 := by
    rw [hmaxE, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    have h1 : ϖE * 1 = ϖE * (ϖE * c) := by rw [mul_one, ← mul_assoc, ← pow_two]; exact hc
    exact hϖE.not_isUnit (IsUnit.of_mul_eq_one c (mul_left_cancel₀ hϖE.ne_zero h1).symm)
  obtain ⟨rE, hrE⟩ := MMP.Fourfold.exists_retraction_D (k := k)
    (L := IsLocalRing.ResidueField E.localRing) IsLocalRing.residue_surjective
    (by rw [hkerκ]; exact hϖE.not_isUnit) (by rwa [hkerκ])
  obtain ⟨xE, hxE⟩ := MMP.Fourfold.exists_span_cons_D_eq_top hrankE hrE
  -- the valuation of `E`
  have hvϖ : X.ord (algebraMap E.localRing X.functionField ϖE) E.genericPoint = 1 :=
    (Scheme.ord_eq_iff E.coheight_genericPoint
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hϖE.ne_zero)).mpr
      (Ring.ordFrac_irreducible (K := X.functionField) hϖE)
  -- top forms of `k(X)` and `L`
  have hKrank : Module.finrank X.functionField Ω[X.functionField⁄k] = d + 1 + 1 := by
    have := essFiniteType_functionField (sX := sX)
    exact (finrank_kaehlerDifferential_eq_trdeg k X.functionField).trans hd
  have : FiniteDimensional X.functionField Ω[X.functionField⁄k] := by
    have := essFiniteType_functionField (sX := sX)
    exact (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k X.functionField).1
  exact ordAt_eq_of_unramifiedCover_of_charZero 𝔮 O ht hy hO hfrac hm hf𝔮 hY0 htm hyt hym z hframe
      hKrank
    hϖE hxE (v := fun f => X.ord f E.genericPoint) (fun a b ha hb => Scheme.ord_mul ha hb)
    (fun a ha => E.ord_algebraMap_of_isUnit ha) hvϖ θ hθ hθ0

end Unramified2

/-- The scalar of the residue form: if `ε = c f^m Y^{m-1}` and `f = u ϖ^m` in a field `K`, then
`c (ϖ^{m-1} V)^m = (ε Y^{-(m-1)} u^{-m} V^m) ϖ^{-m}`. -/
theorem mul_pow_eq_of_eq_mul_pow {R K : Type*} [CommRing R] [Field K] (ι : R →+* K)
    {c fK YK : K} {e Yr ur yi ui V ϖ : R} {M m : ℕ} (hM : m = M + 1)
    (hε : ι e = c * fK ^ m * YK ^ (m - 1)) (hf : fK = ι ur * ι ϖ ^ m) (hY : ι Yr = YK)
    (hyi : yi * Yr = 1) (hui : ui * ur = 1) (hϖ : ι ϖ ≠ 0) :
    c * (ι (ϖ ^ (m - 1) * V)) ^ m = ι (e * yi ^ M * ui ^ m * V ^ m) * (ι ϖ)⁻¹ ^ m := by
  subst hM hY hf
  have hyi' : ι yi * ι Yr = 1 := by rw [← map_mul, hyi, map_one]
  have hui' : ι ui * ι ur = 1 := by rw [← map_mul, hui, map_one]
  have hs : (ι yi * ι Yr) ^ M * (ι ui * ι ur) ^ (M + 1) * ((ι ϖ)⁻¹ * ι ϖ) ^ (M + 1) = 1 := by
    simp only [hyi', hui', inv_mul_cancel₀ hϖ, one_pow, mul_one]
  simp only [map_mul, map_pow, hε, Nat.add_sub_cancel]
  linear_combination (-(c * (ι ϖ ^ M * ι V) ^ (M + 1))) * hs

/-- The image of the residue scalar: if `ψ ϖ = 0`, then
`ψ(e y^M u^{-m} (m u + ϖ b)^m) = ψ(e) ψ(Y)^{-M} m^m` for `y = Y⁻¹`. -/
theorem map_mul_pow_eq_of_map_eq_zero {R K : Type*} [CommRing R] [Field K] (ψ : R →+* K)
    {e yi ui u ϖ b Yr : R} {M m : ℕ} (hϖ : ψ ϖ = 0) (hyi : yi * Yr = 1) (hui : ui * u = 1)
    (hu : ψ u ≠ 0) :
    ψ (e * yi ^ M * ui ^ m * ((m : ℕ) * u + ϖ * b) ^ m) =
      ψ e * (ψ Yr)⁻¹ ^ M * ((m : ℕ) : K) ^ m := by
  have hyi' : ψ yi = (ψ Yr)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← map_mul, hyi, map_one])
  have hui' : ψ ui = (ψ u)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← map_mul, hui, map_one])
  simp only [map_mul, map_pow, map_add, map_natCast, hϖ, zero_mul, add_zero, hyi', hui']
  have hu1 : (ψ u)⁻¹ ^ m * (ψ u) ^ m = 1 := by rw [← mul_pow, inv_mul_cancel₀ hu, one_pow]
  linear_combination (ψ e * (ψ Yr)⁻¹ ^ M * ((m : ℕ) : K) ^ m) * hu1

/-- The order along `Q` of `ε Ȳ^{-M} m^m`, for `ε` a unit and `Ȳ` a uniformizer of `𝒪_{T,Q}`,
is `-M = 1 - m`. -/
theorem ord_mul_inv_pow_mul_natCast_pow {T : Scheme.{u}} [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] (Q : MMP.Mori.PrimeDivisor T) {Yc εc : Q.localRing}
    (hYirr : Irreducible Yc) (hεc : IsUnit εc) {M m : ℕ} (hM : m = M + 1)
    (hmC : IsUnit ((m : ℕ) : Q.localRing)) :
    T.ord (algebraMap Q.localRing T.functionField εc *
      (algebraMap Q.localRing T.functionField Yc)⁻¹ ^ M * ((m : ℕ) : T.functionField) ^ m)
        Q.genericPoint = 1 - m := by
  haveI : IsDiscreteValuationRing Q.localRing := Q.isDiscreteValuationRing_localRing
  have hYT0 : algebraMap Q.localRing T.functionField Yc ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hYirr.ne_zero
  have hεT := Q.ord_algebraMap_of_isUnit hεc
  have hYord : T.ord (algebraMap Q.localRing T.functionField Yc) Q.genericPoint = 1 :=
    (Scheme.ord_eq_iff Q.coheight_genericPoint hYT0).mpr
      (Ring.ordFrac_irreducible (K := T.functionField) hYirr)
  have hYinv : T.ord (algebraMap Q.localRing T.functionField Yc)⁻¹ Q.genericPoint = -1 := by
    have h := Scheme.ord_mul (x := Q.genericPoint) hYT0 (inv_ne_zero hYT0)
    rw [mul_inv_cancel₀ hYT0, Aux.ord_one', hYord] at h
    linarith only [h]
  have hmord : T.ord ((m : ℕ) : T.functionField) Q.genericPoint = 0 := by
    have := Q.ord_algebraMap_of_isUnit hmC
    rwa [map_natCast] at this
  have hmT : ((m : ℕ) : T.functionField) ≠ 0 := by
    rw [← map_natCast (algebraMap Q.localRing T.functionField)]
    exact (hmC.map _).ne_zero
  have hεT0 : algebraMap Q.localRing T.functionField εc ≠ 0 := (hεc.map _).ne_zero
  rw [Scheme.ord_mul (mul_ne_zero hεT0 (pow_ne_zero _ (inv_ne_zero hYT0))) (pow_ne_zero _ hmT),
    Scheme.ord_mul hεT0 (pow_ne_zero _ (inv_ne_zero hYT0)), Aux.ord_pow' (inv_ne_zero hYT0),
    Aux.ord_pow' hmT, hεT, hYinv, hmord, hM]
  push_cast
  ring

/-- Over the fraction field: if `f = u ϖ^m` and `dϖ, dx` frame `Ω_{C'/k}`, then
`df ∧ dx = ϖ^{m-1} (m u + ϖ a) · (dϖ ∧ dx)` in the top forms of `K`, for some `a`. -/
theorem exists_ιMulti_cons_D_eq_smul_topFormsMap {k C' K : Type*} [Field k] [CommRing C']
    [Field K] [Algebra k C'] [Algebra k K] [Algebra C' K] [IsScalarTower k C' K] {d : ℕ}
    {ϖ' : C'} {x' : Fin d → C'}
    (hspan : Submodule.span C' (Set.range (Fin.cons (KaehlerDifferential.D k C' ϖ')
      fun i => KaehlerDifferential.D k C' (x' i) : Fin (d + 1) → Ω[C'⁄k])) = ⊤)
    (u : C') {m : ℕ} (hm : 0 < m) {fK : K} (hf : algebraMap C' K (u * ϖ' ^ m) = fK)
    {xK : Fin d → K} (hx : ∀ i, algebraMap C' K (x' i) = xK i) :
    ∃ a : C', exteriorPower.ιMulti K (d + 1)
        (Fin.cons (KaehlerDifferential.D k K fK) fun i => KaehlerDifferential.D k K (xK i)) =
      algebraMap C' K (ϖ' ^ (m - 1) * ((m : ℕ) * u + ϖ' * a)) •
        topFormsMap k C' K (d + 1) (exteriorPower.ιMulti C' (d + 1)
          (Fin.cons (KaehlerDifferential.D k C' ϖ') fun i =>
            KaehlerDifferential.D k C' (x' i))) := by
  obtain ⟨b, hb⟩ := exists_ιMulti_cons_D_mul_pow hspan u (m - 1)
  rw [Nat.sub_add_cancel hm] at hb
  refine ⟨b, ?_⟩
  rw [algebraMap_smul, ← map_smul, ← hb, topFormsMap_ιMulti]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.cons_zero, KaehlerDifferential.map_D, hf]
  · simp only [Fin.cons_succ, KaehlerDifferential.map_D, hx]

/-- In a local ring, `a u + ϖ b` is a unit for units `a, u` and `ϖ` in the maximal ideal. -/
theorem isUnit_mul_add_mul_of_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    {a u ϖ : R} (ha : IsUnit a) (hu : IsUnit u) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal R) (b : R) :
    IsUnit (a * u + ϖ * b) := by
  by_contra hn
  have h1 := (IsLocalRing.mem_maximalIdeal _).mpr hn
  have h2 : a * u ∈ IsLocalRing.maximalIdeal R := by
    have := sub_mem h1 (Ideal.mul_mem_right b _ hϖ)
    simpa using this
  exact (IsLocalRing.mem_maximalIdeal _).mp h2 (ha.mul hu)

/-- `c (a^m x^{⊗m}) = g (w x)^{⊗m}` when `c a^m = g w^m`. -/
theorem smul_tprod_eq_of_eq {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {m : ℕ}
    {c a g w : K} {x : M} (h : c * a ^ m = g * w ^ m) :
    c • (a ^ m • PiTensorProduct.tprod K (fun _ : Fin m => x)) =
      g • PiTensorProduct.tprod K (fun _ : Fin m => w • x) := by
  rw [smul_smul, h, mul_smul, tprod_const_smul]

/-- **The residue of `σ` along `S` at a cyclic quotient point.** Let `θ = (df ∧ dY ∧ dz)^{⊗m}`,
which along `S` is `(ϖ^{m-1} V)^m (dϖ ∧ dY ∧ dz)^{⊗m}` with `f = u ϖ^m` and `V` a unit, and let
`σ = c θ` with `c f^m Y^{m-1} = ε` a unit at `x`. If `dȲ, dz̄` frame `Ω_{𝒪_{T,Q}/k}` and `Ȳ` is a
uniformizer of `𝒪_{T,Q}`, then the Poincaré residue of `σ` along `S` is
`ε̄ m^m Ȳ^{1-m} (dȲ ∧ dz̄)^{⊗m}`, of order `1 - m` along `Q`. -/
theorem ordForm_eq_one_sub_of_eq_smul_frame_of_charZero {k : Type} [Field k] [CharZero k]
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [LocallyOfFiniteType sX]
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [LocallyOfFiniteType (j ≫ sX)]
    (P : MMP.Mori.PrimeDivisor X) (hjT : j (genericPoint T) = P.genericPoint)
    (Q : MMP.Mori.PrimeDivisor T) {d m : ℕ} (hm : 1 ≤ m)
    (hdT : (letI := functionFieldAlgebra (j ≫ sX); Algebra.trdeg k T.functionField).toNat = d + 1)
    {f Y : X.presheaf.stalk (j.base Q.genericPoint)} (hY0 : Y ≠ 0)
    (hYP : X.ord (algebraMap _ X.functionField Y) P.genericPoint = 0)
    (hYirr : Irreducible ((j.stalkMap Q.genericPoint).hom Y))
    (z : Fin d → X.presheaf.stalk (j.base Q.genericPoint)) (zC : Fin d → Q.localRing)
    (hz : ∀ i, (j.stalkMap Q.genericPoint).hom (z i) = zC i)
    (hzC : letI := stalkAlgebra (j ≫ sX) Q.genericPoint
      Submodule.span Q.localRing (Set.range (Fin.cons (KaehlerDifferential.D k Q.localRing
        ((j.stalkMap Q.genericPoint).hom Y)) fun i => KaehlerDifferential.D k Q.localRing (zC i) :
          Fin (d + 1) → Ω[Q.localRing⁄k])) = ⊤)
    (hζ : j (genericPoint T) ⤳ j.base Q.genericPoint)
    {ϖ b : X.presheaf.stalk (j (genericPoint T))} (hϖ : Irreducible ϖ)
    (u : (X.presheaf.stalk (j (genericPoint T)))ˣ)
    (hfu : (X.presheaf.stalkSpecializes hζ).hom f = u * ϖ ^ m)
    {σ θ : RationalPluriForms sX (d + 1 + 1) m} {c : X.functionField} (hc : c • θ = σ)
    (hθF : letI := stalkAlgebra sX (j (genericPoint T)); letI := functionFieldAlgebra sX
      haveI := isScalarTower_stalk_functionField sX (j (genericPoint T))
      θ = ((algebraMap (X.presheaf.stalk (j (genericPoint T))) X.functionField
        (ϖ ^ (m - 1) * ((m : ℕ) * (u : X.presheaf.stalk (j (genericPoint T))) + ϖ * b))) ^ m •
      PiTensorProduct.tprod X.functionField (fun _ : Fin m =>
        topFormsMap k (X.presheaf.stalk (j (genericPoint T))) X.functionField (d + 1 + 1)
          (exteriorPower.ιMulti _ (d + 1 + 1) (Fin.cons (KaehlerDifferential.D k _ ϖ)
            fun i => KaehlerDifferential.D k _ ((X.presheaf.stalkSpecializes hζ).hom
              ((Fin.cons Y z : Fin (d + 1) → X.presheaf.stalk (j.base Q.genericPoint)) i))))) :
        TensorPower X.functionField m (⋀[X.functionField]^(d + 1 + 1) Ω[X.functionField⁄k])))
    {ε : X.presheaf.stalk (j.base Q.genericPoint)} (hεu : IsUnit ε)
    (hε : algebraMap _ X.functionField ε =
      c * algebraMap _ X.functionField f ^ m * algebraMap _ X.functionField Y ^ (m - 1))
    {ρσ : RationalPluriForms (j ≫ sX) (d + 1) m} (hres : IsPoincareResidue sX j (d + 1) m σ ρσ) :
    Q.ordForm ρσ = 1 - m := by
  have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm
  letI := stalkAlgebra (j ≫ sX) Q.genericPoint
  letI := functionFieldAlgebra (j ≫ sX)
  letI := functionFieldAlgebra sX
  letI := stalkAlgebra sX (j (genericPoint T))
  have := isScalarTower_stalk_functionField sX (j (genericPoint T))
  obtain ⟨hdvrF, -, -, -, hcohF, -⟩ := MMP.Fourfold.stalk_facts (sY := sX) (j := j) hjT
  have hTQ : genericPoint T ⤳ Q.genericPoint := (genericPoint_spec T).specializes trivial
  have hspK : ∀ a, algebraMap _ X.functionField ((X.presheaf.stalkSpecializes hζ).hom a) =
      algebraMap _ X.functionField a := fun a => MMP.Mori.algebraMap_stalkSpecializes hζ a
  have hspT : ∀ a, (j.stalkMap (genericPoint T)).hom ((X.presheaf.stalkSpecializes hζ).hom a) =
      algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
        ((j.stalkMap Q.genericPoint).hom a) := fun a =>
    Scheme.Hom.stalkSpecializes_stalkMap_apply j (genericPoint T) Q.genericPoint hTQ a
  have hϖK : algebraMap _ X.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hϖ.ne_zero
  have hϖord : X.ord (algebraMap _ X.functionField ϖ) P.genericPoint = 1 := by
    rw [← hjT]
    exact (Scheme.ord_eq_iff hcohF hϖK).mpr (Ring.ordFrac_irreducible (K := X.functionField) hϖ)
  have hYK : algebraMap _ X.functionField Y ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hY0
  have := isScalarTower_stalk_functionField (j ≫ sX) Q.genericPoint
  letI : Algebra (X.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  obtain ⟨-, hsurjF⟩ := MMP.Fourfold.stalkMap_facts (sY := sX) (j := j)
  have hkerF : RingHom.ker (algebraMap (X.presheaf.stalk (j (genericPoint T))) T.functionField) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (j (genericPoint T))) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurjF)
  set sC : Fin (d + 1) → Q.localRing :=
    Fin.cons ((j.stalkMap Q.genericPoint).hom Y) zC with hsC_def
  set sA : Fin (d + 1) → X.presheaf.stalk (j.base Q.genericPoint) := Fin.cons Y z with hsA_def
  have hsAC : ∀ i, (j.stalkMap Q.genericPoint).hom (sA i) = sC i := fun i => by
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · simp only [hsA_def, hsC_def, Fin.cons_succ, hz]
  -- the residue of `σ` along `S`
  have hYFu : IsUnit ((X.presheaf.stalkSpecializes hζ).hom Y) := by
    refine IsLocalRing.notMem_maximalIdeal.1 fun hm' => ?_
    rcases (mem_maximalIdeal_iff_ord P hjT _).1 hm' with h | h
    · exact hY0 (MMP.Intersection.stalkSpecializes_injective hζ (h.trans (map_zero _).symm))
    · rw [hspK, hYP] at h; simp at h
  obtain ⟨M, hM⟩ : ∃ M, m = M + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
  have hM1 : m - 1 = M := by rw [hM, Nat.add_sub_cancel]
  obtain ⟨gF, hgF⟩ : ∃ gF : X.presheaf.stalk (j (genericPoint T)), gF =
      (X.presheaf.stalkSpecializes hζ).hom ε * ((hYFu.unit⁻¹ : _ˣ) :
        X.presheaf.stalk (j (genericPoint T))) ^ M *
        ((u⁻¹ : _ˣ) : X.presheaf.stalk (j (genericPoint T))) ^ m *
        ((m : ℕ) * (u : X.presheaf.stalk (j (genericPoint T))) + ϖ * b) ^ m := ⟨_, rfl⟩
  have e1 : ((hYFu.unit⁻¹ : _ˣ) : X.presheaf.stalk (j (genericPoint T))) *
      (X.presheaf.stalkSpecializes hζ).hom Y = 1 := by
    have h := Units.inv_mul hYFu.unit
    rwa [IsUnit.unit_spec] at h
  have e2 : ((u⁻¹ : _ˣ) : X.presheaf.stalk (j (genericPoint T))) *
      (u : X.presheaf.stalk (j (genericPoint T))) = 1 := Units.inv_mul u
  have hscal : c * (algebraMap (X.presheaf.stalk (j (genericPoint T))) X.functionField
        (ϖ ^ (m - 1) * ((m : ℕ) * (u : X.presheaf.stalk (j (genericPoint T))) + ϖ * b))) ^ m =
      algebraMap _ X.functionField gF *
        ((algebraMap (X.presheaf.stalk (j (genericPoint T))) X.functionField ϖ)⁻¹) ^ m := by
    rw [hgF]
    exact mul_pow_eq_of_eq_mul_pow (algebraMap _ X.functionField) hM
      ((hspK ε).trans hε) ((hspK f).symm.trans (by rw [hfu, map_mul, map_pow])) (hspK Y) e1 e2 hϖK
  have hframeK : topFormsMap k (X.presheaf.stalk (j (genericPoint T))) X.functionField (d + 1 + 1)
      (exteriorPower.ιMulti _ (d + 1 + 1) (Fin.cons (KaehlerDifferential.D k _ ϖ)
        fun i => KaehlerDifferential.D k _ ((X.presheaf.stalkSpecializes hζ).hom (sA i)))) =
      exteriorPower.ιMulti X.functionField (d + 1 + 1)
        (Fin.cons (KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField ϖ))
          fun i => KaehlerDifferential.D k X.functionField
            (algebraMap _ X.functionField ((X.presheaf.stalkSpecializes hζ).hom (sA i)))) := by
    rw [topFormsMap_ιMulti]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero, KaehlerDifferential.map_D]
    · simp only [Fin.cons_succ, KaehlerDifferential.map_D]
  obtain ⟨ρ', hρ'_def⟩ : ∃ ρ' : RationalPluriForms (j ≫ sX) (d + 1) m, ρ' =
      ((j.stalkMap (genericPoint T)).hom gF • PiTensorProduct.tprod T.functionField
        (fun _ : Fin m => exteriorPower.ιMulti T.functionField (d + 1)
          fun i => KaehlerDifferential.D k T.functionField
            ((j.stalkMap (genericPoint T)).hom ((X.presheaf.stalkSpecializes hζ).hom (sA i)))) :
        TensorPower T.functionField m (⋀[T.functionField]^(d + 1) Ω[T.functionField⁄k])) :=
    ⟨_, rfl⟩
  have hres' : IsPoincareResidue sX j (d + 1) m σ ρ' := by
    refine ⟨ϖ, gF, fun i => (X.presheaf.stalkSpecializes hζ).hom (sA i), ?_, ?_, hρ'_def⟩
    · have h := hϖord
      rw [← hjT] at h
      exact h
    · rw [← hc, hθF, hframeK]
      exact smul_tprod_eq_of_eq hscal
  have hρσ : ρσ = ρ' := MMP.Fourfold.isPoincareResidue_unique (sY := sX) hjT hres hres'
  -- the order of the residue along `Q`
  rw [hρσ]
  have := essFiniteType_functionField (sX := j ≫ sX)
  have hKrT : Module.finrank T.functionField Ω[T.functionField⁄k] = d + 1 :=
    (finrank_kaehlerDifferential_eq_trdeg k T.functionField).trans hdT
  have : FiniteDimensional T.functionField Ω[T.functionField⁄k] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k T.functionField).1
  have := nontrivial_exteriorPower_of_finrank_eq k T.functionField hKrT
  have hσC := MMP.Fourfold.span_singleton_ιMulti_eq_top _ hzC
  have h0C := topFormsMap_ne_zero_of_span_eq_top (K := T.functionField) hσC
  have hρ'C : ρ' = ((j.stalkMap (genericPoint T)).hom gF •
      PiTensorProduct.tprod T.functionField (fun _ : Fin m =>
        topFormsMap k Q.localRing T.functionField (d + 1)
          (exteriorPower.ιMulti _ (d + 1) (Fin.cons (KaehlerDifferential.D k Q.localRing
            ((j.stalkMap Q.genericPoint).hom Y))
              fun i => KaehlerDifferential.D k Q.localRing (zC i)))) :
      TensorPower T.functionField m (⋀[T.functionField]^(d + 1) Ω[T.functionField⁄k])) := by
    rw [hρ'_def, topFormsMap_ιMulti]
    have hfun : (fun i => KaehlerDifferential.D k T.functionField ((j.stalkMap (genericPoint T)).hom
        ((X.presheaf.stalkSpecializes hζ).hom (sA i)))) = fun i =>
          KaehlerDifferential.map k k Q.localRing T.functionField
            ((Fin.cons (KaehlerDifferential.D k Q.localRing ((j.stalkMap Q.genericPoint).hom Y))
              fun i => KaehlerDifferential.D k Q.localRing (zC i) : Fin (d + 1) → _) i) := by
      funext i
      rw [hspT, hsAC]
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [hsC_def, Fin.cons_zero, KaehlerDifferential.map_D]
      · simp only [hsC_def, Fin.cons_succ, KaehlerDifferential.map_D]
    rw [hfun]
  rw [ordForm_eq_of_frame (sX := j ≫ sX) Q rfl _ hzC h0C _ ρ' hρ'C]
  have hϖT : (j.stalkMap (genericPoint T)).hom ϖ = 0 := by
    have : ϖ ∈ RingHom.ker (algebraMap (X.presheaf.stalk (j (genericPoint T))) T.functionField) :=
      hkerF ▸ hϖ.not_isUnit
    exact this
  have huT : (j.stalkMap (genericPoint T)).hom (u : X.presheaf.stalk (j (genericPoint T))) ≠ 0 :=
    (u.isUnit.map _).ne_zero
  have ha : (j.stalkMap (genericPoint T)).hom gF =
      algebraMap Q.localRing T.functionField ((j.stalkMap Q.genericPoint).hom ε) *
        ((algebraMap Q.localRing T.functionField ((j.stalkMap Q.genericPoint).hom Y))⁻¹) ^ M *
          ((m : ℕ) : T.functionField) ^ m := by
    rw [hgF, map_mul_pow_eq_of_map_eq_zero _ hϖT e1 e2 huT, hspT, hspT]
  have hmC : IsUnit ((m : ℕ) : Q.localRing) := by
    have h : ((m : ℕ) : Q.localRing) = algebraMap k Q.localRing ((m : ℕ) : k) := by simp
    rw [h]
    exact (IsUnit.mk0 _ (by exact_mod_cast hm0)).map _
  rw [ha]
  exact ord_mul_inv_pow_mul_natCast_pow Q hYirr (hεu.map _) hM hmC

section Main

open MvPowerSeries

open Classical in
/-- **The different of the zero boundary at a cyclic quotient point.** If `σ` generates
`𝒪_X(m(K_X + S))` at `x = j(η_Q)`, that is `ord_E σ = -m [E = S]` along every prime divisor
`E` through `x`, then its Poincaré residue along `S` has order `1 - m` along `Q`: the different
of `K_X + S` has coefficient `(m - 1)/m` at `Q`, computed on the one-axis residue lattice of the
formal cyclic quotient and transported along the flat map `𝒪_{X,x} → R`. -/
theorem ordForm_eq_of_isPoincareResidue_of_cyclicInvariants_of_charZero {k : Type} [Field k]
    [CharZero k]
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX))
    (P : MMP.Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (τ : RationalPluriForms sX (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : IsPoincareResidue sX j n 1 τ ρ)
    (Q : MMP.Mori.PrimeDivisor T)
    (κsep : Type) [Field κsep]
    [Algebra (ResidueField (X.presheaf.stalk (j.base Q.genericPoint))) κsep]
    [IsSepClosure (ResidueField (X.presheaf.stalk (j.base Q.genericPoint))) κsep]
    (H : Type) [CommRing H] [IsLocalRing H] [Algebra (X.presheaf.stalk (j.base Q.genericPoint)) H]
    [IsHenselization (X.presheaf.stalk (j.base Q.genericPoint)) κsep H]
    {K : Type*} [Field K] {m : ℕ} {q : ℤ} (hK : IsCyclicQuotientSetting K m q)
    (e : AdicCompletion (maximalIdeal H) H ≃+* cyclicInvariants K m q)
    (he : ((RingHom.ker (j.stalkMap Q.genericPoint).hom).map
        (algebraMap (X.presheaf.stalk (j.base Q.genericPoint))
          (AdicCompletion (maximalIdeal H) H))).map e =
      (Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants K m q).subtype)
    (σ : RationalPluriForms sX (n + 1) m) (hσ0 : σ ≠ 0)
    (hσ : ∀ E : MMP.Mori.PrimeDivisor X, j.base Q.genericPoint ∈ E.support →
      E.ordForm σ = if E = P then -(m : ℤ) else 0)
    (ρσ : RationalPluriForms (j ≫ sX) n m) (hres : IsPoincareResidue sX j n m σ ρσ) :
    Q.ordForm ρσ = 1 - m := by
  classical
  -- the chart
  letI := MMP.Mori.stalkAlgebra sX (j.base Q.genericPoint)
  haveI := essFiniteType_stalk' sX (j.base Q.genericPoint)
  haveI : IsIntegrallyClosed (X.presheaf.stalk (j.base Q.genericPoint)) := IsNormal.stalk_normal (j.base Q.genericPoint)
  obtain ⟨hR, hlocR, hdomR, hicR, -, hfinR, -, -⟩ :=
    MMP.Flips.exists_addEquiv_weilDivisorClassGroup_cyclicQuotientModel hK
  haveI := hR; haveI := hlocR; haveI := hdomR; haveI := hicR; haveI := hfinR
  obtain ⟨hφ, hlφ, hmaxφ, hinjφ⟩ := chart_map_facts_of_field sX (j.base Q.genericPoint) κsep H e
  set φ : X.presheaf.stalk (j.base Q.genericPoint) →+* cyclicInvariants K m q :=
    e.toRingHom.comp ((algebraMap H (AdicCompletion (maximalIdeal H) H)).comp
      (algebraMap (X.presheaf.stalk (j.base Q.genericPoint)) H)) with hφ_def
  have hxP : j.base Q.genericPoint ∈ P.support := by
    have : j.base Q.genericPoint ∈ (P.support : Set X) := hP ▸ ⟨_, rfl⟩
    exact this
  have hD : (ordIdeal P 1 hxP).map φ =
      (Ideal.span {MvPowerSeries.X 0}).comap (cyclicInvariants K m q).subtype := by
    rw [← ker_stalkMap_eq_ordIdeal j P hP Q.genericPoint hxP, ← he]
    change _ = Ideal.map e.toRingHom (Ideal.map (algebraMap (X.presheaf.stalk (j.base Q.genericPoint))
      (AdicCompletion (maximalIdeal H) H)) _)
    rw [Ideal.map_map, IsScalarTower.algebraMap_eq (X.presheaf.stalk (j.base Q.genericPoint)) H
      (AdicCompletion (maximalIdeal H) H)]
  have hm := hK.one_le
  have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm
  obtain ⟨f, hf0, hfP, hfE⟩ :=
    exists_stalk_ord_eq_of_cyclicInvariants sX (j.base Q.genericPoint) κsep H hK e P hxP
  haveI : IsLocalHom φ := hlφ
  obtain ⟨w, hwR, hwu, hfw⟩ := chart_unit_root hK φ hφ P hxP hD hf0 hfP hfE
  obtain ⟨a, g, γ, ham, haq, hga, hgm, hgγ, hγ0, hγ1⟩ :=
    chart_y_coordinate hK φ hφ hmaxφ P hxP hD
  obtain ⟨wi, hwi⟩ := hwu.exists_left_inv
  obtain ⟨Y, hY, hYm, hYγ⟩ := chart_Y hm φ P hxP hf0 hfP hfE hga hwu hfw hgγ hγ0
  have hfm : f ∈ maximalIdeal (X.presheaf.stalk (j.base Q.genericPoint)) := by
    by_contra hfu
    have := ord_eq_zero_of_isUnit_stalk P hxP (IsLocalRing.notMem_maximalIdeal.1 hfu)
    rw [hfP] at this; exact hm0 (by exact_mod_cast this)
  obtain ⟨L, _, _, _, _, O, t, y, htO, hyO, τO, hO, htm, hyt, hym, hfr, hτt, hτy, hτA, hFF,
    hlocO, hnoethO, hregO, hmaxO, hfinO, hfracO⟩ :=
    exists_cover_ring (A := X.presheaf.stalk (j.base Q.genericPoint)) (KA := X.functionField)
      hK φ hφ hinjφ hwR hwi hfw hgγ hγ0 hγ1 hY hYm hfm
  -- `Ȳ` is a uniformizer of `𝒪_{T,Q}`
  have hsurjQ : Function.Surjective (j.stalkMap Q.genericPoint).hom := j.stalkMap_surjective _
  haveI : IsDiscreteValuationRing Q.localRing := Q.isDiscreteValuationRing_localRing
  have hYnot : Y ∉ RingHom.ker (j.stalkMap Q.genericPoint).hom ⊔
      maximalIdeal (X.presheaf.stalk (j.base Q.genericPoint)) ^ 2 := by
    rw [ker_stalkMap_eq_ordIdeal j P hP Q.genericPoint hxP]
    exact CyclicChart.notMem_sup_sq hK φ _ hD.le hYγ hγ1
  have hYirr : Irreducible ((j.stalkMap Q.genericPoint).hom Y) :=
    KummerCover.irreducible_of_notMem_sup_sq _ hsurjQ hYm hYnot
  -- a frame `dȲ, dz̄` of `Ω_{𝒪_{T,Q}/k}`
  have : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
  have hjT := Aux.map_genericPoint_eq j P hP
  letI := stalkAlgebra (j ≫ sX) Q.genericPoint
  letI := functionFieldAlgebra (j ≫ sX)
  letI := functionFieldAlgebra sX
  have hdT : (Algebra.trdeg k T.functionField).toNat = n := by
    have h1 := Aux.trdeg_add_one_of_eq_genericPoint (sY := sX) (j := j) P hjT
    have h2 : (Algebra.trdeg k X.functionField).toNat = n + 1 :=
      toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
    linarith only [h1, h2]
  obtain ⟨hfsC, hessC⟩ := Q.formallySmooth_localRing (sX := j ≫ sX)
  obtain ⟨hfreeC, hfinC⟩ := Q.free_kaehlerDifferential_localRing (sX := j ≫ sX)
  have hrankC := Q.finrank_kaehlerDifferential_localRing (sX := j ≫ sX)
  rw [hdT] at hrankC
  have : Algebra.EssFiniteType k (IsLocalRing.ResidueField Q.localRing) :=
    Algebra.EssFiniteType.of_surjective (IsScalarTower.toAlgHom k Q.localRing _)
      IsLocalRing.residue_surjective
  have hkerκ : RingHom.ker (algebraMap Q.localRing (IsLocalRing.ResidueField Q.localRing)) =
      IsLocalRing.maximalIdeal Q.localRing := IsLocalRing.ker_residue
  have hYmC : (j.stalkMap Q.genericPoint).hom Y ∈ IsLocalRing.maximalIdeal Q.localRing :=
    hYirr.not_isUnit
  have hYm2C : (j.stalkMap Q.genericPoint).hom Y ∉ IsLocalRing.maximalIdeal Q.localRing ^ 2 := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hYirr,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    have h1 : (j.stalkMap Q.genericPoint).hom Y * 1 =
        (j.stalkMap Q.genericPoint).hom Y * ((j.stalkMap Q.genericPoint).hom Y * c) := by
      rw [mul_one, ← mul_assoc, ← pow_two]; exact hc
    have h2 := mul_left_cancel₀ hYirr.ne_zero h1
    exact hYirr.not_isUnit (IsUnit.of_mul_eq_one c h2.symm)
  obtain ⟨r, hr⟩ := MMP.Fourfold.exists_retraction_D (k := k)
    (L := IsLocalRing.ResidueField Q.localRing) IsLocalRing.residue_surjective
    (by rwa [hkerκ]) (by rwa [hkerκ])
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := by
    rcases n with _ | d
    · exfalso
      have : Subsingleton Ω[Q.localRing⁄k] := (Module.finrank_eq_zero_iff_of_free _ _).1 hrankC
      rw [Subsingleton.elim (KaehlerDifferential.D k Q.localRing
        ((j.stalkMap Q.genericPoint).hom Y)) 0, map_zero] at hr
      exact zero_ne_one hr
    · exact ⟨d, rfl⟩
  obtain ⟨zC, hzC⟩ := MMP.Fourfold.exists_span_cons_D_eq_top hrankC hr
  choose z hz using fun i => hsurjQ (zC i)
  -- the discrete valuation ring `F = 𝒪_{X,S}` and `f = u ϖ^m` in it
  letI := stalkAlgebra sX (j (genericPoint T))
  have := isScalarTower_stalk_functionField sX (j (genericPoint T))
  obtain ⟨hdvrF, hfreeF, hfinF, hsmF, hcohF, hrankF⟩ :=
    MMP.Fourfold.stalk_facts (sY := sX) (j := j) hjT
  have hTQ : genericPoint T ⤳ Q.genericPoint := (genericPoint_spec T).specializes trivial
  have hζ : j (genericPoint T) ⤳ j.base Q.genericPoint := hTQ.map j.base.hom.continuous
  have hspK : ∀ a, algebraMap _ X.functionField ((X.presheaf.stalkSpecializes hζ).hom a) =
      algebraMap _ X.functionField a := fun a => MMP.Mori.algebraMap_stalkSpecializes hζ a
  have hspT : ∀ a, (j.stalkMap (genericPoint T)).hom ((X.presheaf.stalkSpecializes hζ).hom a) =
      algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
        ((j.stalkMap Q.genericPoint).hom a) := fun a =>
    Scheme.Hom.stalkSpecializes_stalkMap_apply j (genericPoint T) Q.genericPoint hTQ a
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible
    (X.presheaf.stalk (j (genericPoint T)))
  have hfF0 : (X.presheaf.stalkSpecializes hζ).hom f ≠ 0 := fun h =>
    hf0 (MMP.Intersection.stalkSpecializes_injective hζ (h.trans (map_zero _).symm))
  obtain ⟨k₀, u, hfu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hfF0 hϖ
  have hϖK : algebraMap _ X.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hϖ.ne_zero
  have hϖord : X.ord (algebraMap _ X.functionField ϖ) P.genericPoint = 1 := by
    rw [← hjT]
    exact (Scheme.ord_eq_iff hcohF hϖK).mpr (Ring.ordFrac_irreducible (K := X.functionField) hϖ)
  have hjTP : j (genericPoint T) ∈ P.support := by
    rw [hjT, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have huord : X.ord (algebraMap _ X.functionField (u : X.presheaf.stalk (j (genericPoint T))))
      P.genericPoint = 0 := ord_eq_zero_of_isUnit_stalk P hjTP u.isUnit
  have hk : k₀ = m := by
    have h := hfP
    rw [← hspK f, hfu, map_mul, map_pow, Scheme.ord_mul ((u.isUnit.map _).ne_zero)
      (pow_ne_zero _ hϖK), huord, Aux.ord_pow' hϖK, hϖord] at h
    have : (k₀ : ℤ) = m := by linarith only [h]
    exact_mod_cast this
  rw [hk] at hfu
  -- a frame `dϖ, dY, dz` of `Ω_{F/k}`
  have := isScalarTower_stalk_functionField (j ≫ sX) Q.genericPoint
  letI : Algebra (X.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  obtain ⟨htowF, hsurjF⟩ := MMP.Fourfold.stalkMap_facts (sY := sX) (j := j)
  have hkerF : RingHom.ker (algebraMap (X.presheaf.stalk (j (genericPoint T))) T.functionField) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (j (genericPoint T))) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurjF)
  have hmaxF := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  set sC : Fin (d + 1) → Q.localRing :=
    Fin.cons ((j.stalkMap Q.genericPoint).hom Y) zC with hsC_def
  set sA : Fin (d + 1) → X.presheaf.stalk (j.base Q.genericPoint) := Fin.cons Y z with hsA_def
  have hsAC : ∀ i, (j.stalkMap Q.genericPoint).hom (sA i) = sC i := fun i => by
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · simp only [hsA_def, hsC_def, Fin.cons_succ, hz]
  have hsC : Submodule.span Q.localRing
      (Set.range fun i => KaehlerDifferential.D k Q.localRing (sC i)) = ⊤ := by
    rw [← hzC]
    congr 2
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  have hsK := KummerCover.span_map_eq_top_of_isLocalization (k := k) (B := T.functionField)
    (nonZeroDivisors Q.localRing) sC hsC
  have hsK' : Submodule.span T.functionField (Set.range fun i => KaehlerDifferential.D k
      T.functionField (algebraMap (X.presheaf.stalk (j (genericPoint T))) T.functionField
        ((X.presheaf.stalkSpecializes hζ).hom (sA i)))) = ⊤ := by
    rw [← hsK]
    congr 2
    funext i
    change KaehlerDifferential.D k T.functionField ((j.stalkMap (genericPoint T)).hom _) = _
    rw [hspT, hsAC]
  have hframeF := KummerCover.span_insert_D_eq_top_of_surjective (k := k) hsurjF hkerF hmaxF
    (fun i => (X.presheaf.stalkSpecializes hζ).hom (sA i)) hsK'
  rw [← Fin.range_cons] at hframeF
  -- `ω₀ = df ∧ dY ∧ dz = ϖ^{m-1} V (dϖ ∧ dY ∧ dz)` with `V` a unit
  obtain ⟨b, hω0⟩ : ∃ b : X.presheaf.stalk (j (genericPoint T)),
    exteriorPower.ιMulti X.functionField (d + 1 + 1)
      (Fin.cons (KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField f))
        fun i => KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField (sA i))) =
      algebraMap (X.presheaf.stalk (j (genericPoint T))) X.functionField
        (ϖ ^ (m - 1) * ((m : ℕ) * (u : X.presheaf.stalk (j (genericPoint T))) + ϖ * b)) •
      topFormsMap k (X.presheaf.stalk (j (genericPoint T))) X.functionField (d + 1 + 1)
        (exteriorPower.ιMulti _ (d + 1 + 1) (Fin.cons (KaehlerDifferential.D k _ ϖ)
          fun i => KaehlerDifferential.D k _ ((X.presheaf.stalkSpecializes hζ).hom (sA i)))) :=
    exists_ιMulti_cons_D_eq_smul_topFormsMap (k := k) hframeF _ hm (by rw [← hfu, hspK])
      (xK := fun i => algebraMap _ X.functionField (sA i)) fun i => hspK (sA i)
  have hmF : IsUnit ((m : ℕ) : X.presheaf.stalk (j (genericPoint T))) := by
    have h : ((m : ℕ) : X.presheaf.stalk (j (genericPoint T))) =
        algebraMap k (X.presheaf.stalk (j (genericPoint T))) ((m : ℕ) : k) := by simp
    rw [h]
    exact (IsUnit.mk0 _ (by exact_mod_cast hm0)).map _
  have hVu : IsUnit ((m : ℕ) * (u : X.presheaf.stalk (j (genericPoint T))) + ϖ * b) :=
    isUnit_mul_add_mul_of_mem_maximalIdeal hmF u.isUnit hϖ.not_isUnit b
  -- the top forms of `F` and of `k(X)`
  have hKrank : Module.finrank X.functionField Ω[X.functionField⁄k] = d + 1 + 1 := by
    have := essFiniteType_functionField (sX := sX)
    refine (finrank_kaehlerDifferential_eq_trdeg k X.functionField).trans ?_
    exact toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX)
      (by rw [hdim]; norm_cast)
  have : FiniteDimensional X.functionField Ω[X.functionField⁄k] := by
    have := essFiniteType_functionField (sX := sX)
    exact (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k X.functionField).1
  have : Nontrivial (⋀[X.functionField]^(d + 1 + 1) Ω[X.functionField⁄k]) :=
    nontrivial_exteriorPower_of_finrank_eq k X.functionField hKrank
  have hσF := MMP.Fourfold.span_singleton_ιMulti_eq_top _ hframeF
  have h0F := topFormsMap_ne_zero_of_span_eq_top (K := X.functionField) hσF
  obtain ⟨θ, hθ_def⟩ : ∃ θ : RationalPluriForms sX (d + 1 + 1) m,
      θ = (PiTensorProduct.tprod X.functionField (fun _ : Fin m =>
        exteriorPower.ιMulti X.functionField (d + 1 + 1)
          (Fin.cons (KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField f))
            fun i => KaehlerDifferential.D k X.functionField
              (algebraMap _ X.functionField (sA i)))) :
        TensorPower X.functionField m (⋀[X.functionField]^(d + 1 + 1) Ω[X.functionField⁄k])) :=
    ⟨_, rfl⟩
  have hθF : θ = ((algebraMap (X.presheaf.stalk (j (genericPoint T))) X.functionField
        (ϖ ^ (m - 1) * ((m : ℕ) * (u : X.presheaf.stalk (j (genericPoint T))) + ϖ * b))) ^ m •
      PiTensorProduct.tprod X.functionField (fun _ : Fin m =>
        topFormsMap k (X.presheaf.stalk (j (genericPoint T))) X.functionField (d + 1 + 1)
          (exteriorPower.ιMulti _ (d + 1 + 1) (Fin.cons (KaehlerDifferential.D k _ ϖ)
            fun i => KaehlerDifferential.D k _ ((X.presheaf.stalkSpecializes hζ).hom (sA i))))) :
        TensorPower X.functionField m (⋀[X.functionField]^(d + 1 + 1) Ω[X.functionField⁄k])) :=
    hθ_def.trans ((congrArg (fun w : ⋀[X.functionField]^(d + 1 + 1) Ω[X.functionField⁄k] =>
      PiTensorProduct.tprod X.functionField fun _ : Fin m => w) hω0).trans
        (tprod_const_smul _ _))
  have hcoefK : algebraMap (X.presheaf.stalk (j (genericPoint T))) X.functionField
      (ϖ ^ (m - 1) * ((m : ℕ) * (u : X.presheaf.stalk (j (genericPoint T))) + ϖ * b)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
      (mul_ne_zero (pow_ne_zero _ hϖ.ne_zero) hVu.ne_zero)
  have hθ0 : θ ≠ 0 := by
    rw [hθF]
    refine smul_ne_zero (pow_ne_zero _ hcoefK) ?_
    have hb := ZTensorPower.basis_ofNat
      (topFormsBasis (X.presheaf.stalk (j (genericPoint T))) hσF h0F) m
    simp only [topFormsBasis_apply] at hb
    rw [← hb]
    exact (ZTensorPower.basis _ _).ne_zero ()
  -- `σ = c θ`
  have hrank : Module.finrank X.functionField (RationalPluriForms sX (d + 1 + 1) m) = 1 := by
    obtain ⟨b₀⟩ := exists_basis_topForms (sX := sX) (d := d + 1 + 1) (by rw [hdim]; norm_cast)
    let bb : Module.Basis Unit X.functionField (RationalPluriForms sX (d + 1 + 1) m) :=
      ZTensorPower.basis b₀ m
    rw [Module.finrank_eq_card_basis bb, Fintype.card_unit]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' θ hθ0).mp hrank σ
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hσ0 hc.symm
  -- orders along the prime divisors through `x`
  have hd : (Algebra.trdeg k X.functionField).toNat = d + 1 + 1 := by
    have := essFiniteType_functionField (sX := sX)
    rw [← hKrank, finrank_kaehlerDifferential_eq_trdeg]
  have injA := IsFractionRing.injective (X.presheaf.stalk (j.base Q.genericPoint)) X.functionField
  have hfK : algebraMap _ X.functionField f ≠ 0 := (map_ne_zero_iff _ injA).2 hf0
  have hY0 : Y ≠ 0 := by
    rintro rfl
    exact hYirr.ne_zero (map_zero _)
  have hYK : algebraMap _ X.functionField Y ≠ 0 := (map_ne_zero_iff _ injA).2 hY0
  have hYP : X.ord (algebraMap _ X.functionField Y) P.genericPoint = 0 := by
    have h1 : Y ∉ ordIdeal P 1 hxP := fun h => hYnot (Ideal.mem_sup_left
      ((ker_stalkMap_eq_ordIdeal j P hP Q.genericPoint hxP).symm ▸ h))
    rw [mem_ordIdeal_iff] at h1
    push Not at h1
    have h2 := ord_nonneg_of_mem_support P hxP Y
    exact le_antisymm (Int.toNat_eq_zero.mp (Nat.lt_one_iff.mp h1.2)) h2
  have key := ordForm_eq_of_frame (sX := sX) (y := j (genericPoint T)) P hjT _ hframeF h0F
    ((algebraMap (X.presheaf.stalk (j (genericPoint T))) X.functionField
        (ϖ ^ (m - 1) * ((m : ℕ) * (u : X.presheaf.stalk (j (genericPoint T))) + ϖ * b))) ^ m)
    θ hθF
  have hθP : P.ordForm θ = m * (m - 1 : ℕ) := by
    rw [key, Aux.ord_pow' hcoefK,
      map_mul, map_pow, Scheme.ord_mul (pow_ne_zero _ hϖK) ((hVu.map _).ne_zero),
      Aux.ord_pow' hϖK, hϖord, ord_eq_zero_of_isUnit_stalk P hjTP hVu]
    push_cast; ring
  have hθE : ∀ E : MMP.Mori.PrimeDivisor X, j.base Q.genericPoint ∈ E.support → E ≠ P →
      E.ordForm θ = (m - 1 : ℕ) * X.ord (algebraMap _ X.functionField Y) E.genericPoint := by
    intro E hE hEP
    have : FiniteDimensional X.functionField L :=
      Module.finite_of_finrank_pos (by rw [hfr]; exact hm)
    -- `A → O` is local
    have : IsLocalHom (algebraMap (X.presheaf.stalk (j.base Q.genericPoint)) O) := by
      refine ⟨fun a ha => ?_⟩
      have h1 := ha.map τO
      rw [hτA] at h1
      exact isUnit_of_map_unit φ a (CyclicChart.isUnit_of_isUnit_coe h1)
    letI : Algebra k O :=
      ((algebraMap (X.presheaf.stalk (j.base Q.genericPoint)) O).comp (algebraMap k _)).toAlgebra
    have : IsScalarTower k (X.presheaf.stalk (j.base Q.genericPoint)) O :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : Algebra.EssFiniteType k O :=
      Algebra.EssFiniteType.comp k (X.presheaf.stalk (j.base Q.genericPoint)) O
    letI : Algebra (X.presheaf.stalk (j.base Q.genericPoint)) Q.localRing :=
      (j.stalkMap Q.genericPoint).hom.toAlgebra
    have htowQ := MMP.Fourfold.isScalarTower_stalkMap (sY := sX) (j := j) Q.genericPoint
    have hzC' : Submodule.span Q.localRing (Set.range (Fin.cons (KaehlerDifferential.D k
        Q.localRing ((j.stalkMap Q.genericPoint).hom Y)) fun i => KaehlerDifferential.D k
          Q.localRing ((j.stalkMap Q.genericPoint).hom (z i)) : Fin (d + 1) → Ω[Q.localRing⁄k])) =
        ⊤ := by
      simpa only [hz] using hzC
    have hframe := KummerCover.span_D_eq_top_of_cover (k := k) (j.stalkMap Q.genericPoint).hom
        hsurjQ
      (fun c => (IsScalarTower.algebraMap_apply k (X.presheaf.stalk (j.base Q.genericPoint))
        Q.localRing c).symm) O htO hyO hO hmaxO
      (fun a ha => (IsLocalRing.mem_maximalIdeal _).2 fun hu => by
        have := hu.map (j.stalkMap Q.genericPoint).hom
        rw [RingHom.mem_ker.1 ha] at this
        exact not_isUnit_zero this) hYm z hzC'
    exact ordForm_eq_of_unramifiedCover_of_charZero sX hd (j.base Q.genericPoint) O htO hyO hO
        hfracO
      hm hf0 hY0 htm hyt hym z hframe E hE (hfE E hE hEP) θ hθ_def hθ0
  have hh0 : c * algebraMap _ X.functionField f ^ m * algebraMap _ X.functionField Y ^ (m - 1)
      ≠ 0 := mul_ne_zero (mul_ne_zero hc0 (pow_ne_zero _ hfK)) (pow_ne_zero _ hYK)
  obtain ⟨ε, hεu, hε⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero
    (j.base Q.genericPoint) hh0 fun E hE => by
      have hσE := hσ E hE
      rw [← hc, E.ordForm_smul (sX := sX) hd hc0 hθ0] at hσE
      rw [Scheme.ord_mul (mul_ne_zero hc0 (pow_ne_zero _ hfK)) (pow_ne_zero _ hYK),
        Scheme.ord_mul hc0 (pow_ne_zero _ hfK), Aux.ord_pow' hfK, Aux.ord_pow' hYK]
      have hm1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := Nat.cast_pred hm
      by_cases hEP : E = P
      · subst hEP
        rw [if_pos rfl, hθP, hm1] at hσE
        rw [hfP, hYP, hm1]
        linarith only [hσE]
      · rw [if_neg hEP, hθE E hE hEP, hm1] at hσE
        rw [hfE E hE hEP, hm1]
        linarith only [hσE]
  exact ordForm_eq_one_sub_of_eq_smul_frame_of_charZero sX j P hjT Q hm hdT hY0 hYP hYirr z zC hz
      hzC hζ hϖ u
    hfu hc hθF hεu hε hres

end Main

end CyclicCover

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u v

/-- **The different of `K_X + S` at `P`.** The restriction to `S` of any local equation `φ₀`
of `m(K_X + S)` near `x = j(η_Q)` has order `m · ord_Q(ρ) + (m - 1)` along `Q`: the different of
the zero boundary has coefficient `(m - 1)/m`, computed on the one-axis residue lattice of the
formal cyclic quotient and transported along the flat map `𝒪_{X,x} → R`. -/
theorem ordUnit_pullbackComponent_eq_of_cyclicInvariants_of_charZero {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k]
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX))
    (P : MMP.Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (τ : RationalPluriForms sX (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : IsPoincareResidue sX j n 1 τ ρ)
    (Q : MMP.Mori.PrimeDivisor T)
    (κsep : Type) [Field κsep]
    [Algebra (ResidueField (X.presheaf.stalk (j.base Q.genericPoint))) κsep]
    [IsSepClosure (ResidueField (X.presheaf.stalk (j.base Q.genericPoint))) κsep]
    (H : Type) [CommRing H] [IsLocalRing H] [Algebra (X.presheaf.stalk (j.base Q.genericPoint)) H]
    [IsHenselization (X.presheaf.stalk (j.base Q.genericPoint)) κsep H]
    {K : Type*} [Field K] {m : ℕ} {q : ℤ} (hK : IsCyclicQuotientSetting K m q)
    (e : AdicCompletion (maximalIdeal H) H ≃+* cyclicInvariants K m q)
    (he : ((RingHom.ker (j.stalkMap Q.genericPoint).hom).map
        (algebraMap (X.presheaf.stalk (j.base Q.genericPoint))
          (AdicCompletion (maximalIdeal H) H))).map e =
      (Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants K m q).subtype)
    {U : X.Opens} (hxU : j.base Q.genericPoint ∈ U) {φ₀ : (RationalFunctions X)ˣ}
    (hφ₀ : Divisor.IsLocalEquation ((m : ℤ) • (divisorOfForm τ + Finsupp.single P (1 : ℤ))) U φ₀)
    (hG : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
      DivisorWithCoeffs.supp ((m : ℤ) • (divisorOfForm τ + Finsupp.single P (1 : ℤ))))
    (hQU : j (componentGenericPoint T Q.component) ∈ U) :
    Q.ordUnit (pullbackComponent j hG hφ₀ Q.component hQU) = m * Q.ordForm ρ + (m - 1) := by
  classical
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by have := hK.one_le; omega⟩
  have : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
  have hjT := Aux.map_genericPoint_eq j P hP
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (j ≫ sX)
  have hd : (Algebra.trdeg k X.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
  have hdT : (Algebra.trdeg k T.functionField).toNat = n := by
    have := Aux.trdeg_add_one_of_eq_genericPoint (sY := sX) (j := j) P hjT
    omega
  have hdim' : topologicalKrullDim X = ((n + 1 : ℕ) : WithBot ℕ∞) := by rw [hdim]; norm_cast
  have hdimT := MMP.Fourfold.topologicalKrullDim_eq_of_range_eq_support sX hdim j P hP
  have hρ0 := Aux.isPoincareResidue_ne_zero sX hX hdim j hT P hP τ hτ0 hτ ρ hρ Q
  -- a unit of `𝒪_{X, j(η_T)}` representing `φ₀`
  have hc := MMP.Fourfold.componentGenericPoint_eq_genericPoint (X := T) Q.component
  have hgU : j (genericPoint T) ∈ U := by rw [← hc]; exact hQU
  have hgs : j (genericPoint T) ∉
      DivisorWithCoeffs.supp (((M + 1 : ℕ) : ℤ) • (divisorOfForm τ + Finsupp.single P (1 : ℤ))) := by
    have := hG Q.component
    rwa [hc] at this
  obtain ⟨a₀, ha₀⟩ := hφ₀.exists_unit_stalk hgU hgs (mem_pointComponent _)
  -- the restriction of `φ₀` to `S`
  have hordT : Q.ordUnit (pullbackComponent j hG hφ₀ Q.component hQU) =
      T.ord ((j.stalkMap (genericPoint T)).hom a₀.val) Q.genericPoint := by
    have h₀ : componentGenericPoint T Q.component ⤳ genericPoint T := specializes_of_eq hc
    have h₁ : j (componentGenericPoint T Q.component) ⤳ j (genericPoint T) :=
      j.base.hom.map_specializes h₀
    have hW : j (componentGenericPoint T Q.component) ∈
        (pointComponent (j (genericPoint T))).1 := by
      rw [hc]; exact mem_pointComponent _
    let a' : (X.presheaf.stalk (j (componentGenericPoint T Q.component)))ˣ :=
      Units.map (X.presheaf.stalkSpecializes h₁).hom.toMonoidHom a₀
    have ha' : (stalkToRationalFunctions X hW).hom a' =
        (φ₀ : RationalFunctions X) (pointComponent (j (genericPoint T))) := by
      rw [← ha₀]
      change (X.presheaf.stalkSpecializes h₁ ≫ X.presheaf.stalkSpecializes _).hom a₀.val = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      rfl
    rw [pullbackComponent_eq hG hφ₀ _ hW a' ha', Aux.ordUnit_eq_ord, Units.coe_map]
    change T.ord ((MMP.Positivity.componentToFunctionField Q.component).hom
      ((j.stalkMap _).hom ((X.presheaf.stalkSpecializes h₁).hom a₀.val))) _ = _
    rw [Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ h₀,
      Aux.componentToFunctionField_stalkSpecializes T _ h₀, Aux.algebraMap_stalk_genericPoint T]
  -- orders of `φ₀` on `X` near `x`
  have hordX : ∀ E : MMP.Mori.PrimeDivisor X, j.base Q.genericPoint ∈ E.support →
      DivisorWithCoeffs.coeff (((M + 1 : ℕ) : ℤ) • (divisorOfForm τ + Finsupp.single P (1 : ℤ))) E =
        X.ord (algebraMap _ X.functionField a₀.val) E.genericPoint := fun E hE => by
    rw [hφ₀ E ⟨_, hE, hxU⟩]
    exact Aux.ord_eq_ord_algebraMap_of_stalk φ₀ _ _ _ ha₀ E
  -- the inverse unit
  have hXa : algebraMap _ X.functionField a₀.val ≠ 0 := (a₀.isUnit.map _).ne_zero
  have hXb : algebraMap _ X.functionField (↑a₀⁻¹ : X.presheaf.stalk (j (genericPoint T))) ≠ 0 :=
    ((a₀⁻¹).isUnit.map _).ne_zero
  have hXab : ∀ z : X, X.ord (algebraMap _ X.functionField
      (↑a₀⁻¹ : X.presheaf.stalk (j (genericPoint T)))) z =
        -X.ord (algebraMap _ X.functionField a₀.val) z := fun z => by
    have h := Scheme.ord_mul (x := z) hXa hXb
    rw [← map_mul, Units.mul_inv, map_one, Aux.ord_one'] at h
    omega
  have hTa : ((j.stalkMap (genericPoint T)).hom a₀.val : T.functionField) ≠ 0 :=
    ((a₀.isUnit.map (j.stalkMap (genericPoint T)).hom)).ne_zero
  have hTb : ((j.stalkMap (genericPoint T)).hom
      (↑a₀⁻¹ : X.presheaf.stalk (j (genericPoint T))) : T.functionField) ≠ 0 :=
    (((a₀⁻¹).isUnit.map (j.stalkMap (genericPoint T)).hom)).ne_zero
  have hTab : ∀ z : T, T.ord ((j.stalkMap (genericPoint T)).hom
      (↑a₀⁻¹ : X.presheaf.stalk (j (genericPoint T))) : T.functionField) z =
        -T.ord ((j.stalkMap (genericPoint T)).hom a₀.val : T.functionField) z := fun z => by
    have h := Scheme.ord_mul (x := z) hTa hTb
    have e : ((j.stalkMap (genericPoint T)).hom a₀.val : T.functionField) *
        (j.stalkMap (genericPoint T)).hom (↑a₀⁻¹ : X.presheaf.stalk (j (genericPoint T))) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [e, Aux.ord_one'] at h
    omega
  have hτM := Aux.pluriPow_ne_zero hdim' hτ0 M
  have hρM := Aux.pluriPow_ne_zero hdimT hρ0 M
  -- the generator `σ = φ₀⁻¹ τ^{⊗m}` and its residue
  have key := ordForm_eq_of_isPoincareResidue_of_cyclicInvariants_of_charZero sX hX hdim j hT P hP
      τ hτ0 hτ
    ρ hρ Q κsep H hK e he
    (algebraMap _ X.functionField (↑a₀⁻¹ : X.presheaf.stalk (j (genericPoint T))) •
      Aux.pluriPow τ M) (smul_ne_zero hXb hτM) (fun E hE => by
      rw [E.ordForm_smul (sX := sX) hd hXb hτM, Aux.ordForm_pluriPow hdim' hτ0 E M, hXab,
        ← hordX E hE, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
        coeff_divisorOfForm, smul_eq_mul]
      by_cases hEP : E = P
      · subst hEP
        rw [DivisorWithCoeffs.coeff_single_self, if_pos rfl]
        ring
      · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hEP), if_neg hEP]
        ring)
    (((j.stalkMap (genericPoint T)).hom (↑a₀⁻¹ : X.presheaf.stalk (j (genericPoint T))) :
      T.functionField) • Aux.pluriPow ρ M)
    (Aux.IsPoincareResidue.algebraMap_smul (Aux.isPoincareResidue_pluriPow P hjT hdim hρ M) _)
  rw [Q.ordForm_smul (sX := j ≫ sX) hdT hTb hρM, Aux.ordForm_pluriPow hdimT hρ0 Q M, hTab,
    ← hordT] at key
  push_cast at key ⊢
  linarith

/-- **A local equation of `m(K_X + S)` at `P`**, with the order of its restriction to `S`. -/
theorem exists_isLocalEquation_ordUnit_eq_of_charZero {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k]
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX))
    (P : MMP.Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (τ : RationalPluriForms sX (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : IsPoincareResidue sX j n 1 τ ρ)
    (Q : MMP.Mori.PrimeDivisor T)
    (κsep : Type) [Field κsep]
    [Algebra (ResidueField (X.presheaf.stalk (j.base Q.genericPoint))) κsep]
    [IsSepClosure (ResidueField (X.presheaf.stalk (j.base Q.genericPoint))) κsep]
    (H : Type) [CommRing H] [IsLocalRing H] [Algebra (X.presheaf.stalk (j.base Q.genericPoint)) H]
    [IsHenselization (X.presheaf.stalk (j.base Q.genericPoint)) κsep H]
    {K : Type*} [Field K] {m : ℕ} {q : ℤ} (hK : IsCyclicQuotientSetting K m q)
    (e : AdicCompletion (maximalIdeal H) H ≃+* cyclicInvariants K m q)
    (he : ((RingHom.ker (j.stalkMap Q.genericPoint).hom).map
        (algebraMap (X.presheaf.stalk (j.base Q.genericPoint))
          (AdicCompletion (maximalIdeal H) H))).map e =
      (Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants K m q).subtype) :
    ∃ U : X.Opens, j.base Q.genericPoint ∈ U ∧ ∃ φ₀ : (RationalFunctions X)ˣ,
      ∃ hφ₀ : Divisor.IsLocalEquation ((m : ℤ) • (divisorOfForm τ + Finsupp.single P (1 : ℤ)))
        U φ₀,
      ∀ (hG : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
          DivisorWithCoeffs.supp ((m : ℤ) • (divisorOfForm τ + Finsupp.single P (1 : ℤ))))
        (hQU : j (componentGenericPoint T Q.component) ∈ U),
        Q.ordUnit (pullbackComponent j hG hφ₀ Q.component hQU) =
          m * Q.ordForm ρ + (m - 1) := by
  obtain ⟨φ₀, hφ₀⟩ := exists_forall_mem_support_coeff_nsmul_eq_ord sX (j.base Q.genericPoint)
    κsep H hK e (divisorOfForm τ + Finsupp.single P (1 : ℤ))
  obtain ⟨U, hxU, hU⟩ := exists_isLocalEquation_of_forall_mem_support _ φ₀ _ hφ₀
  exact ⟨U, hxU, φ₀, hU, fun hG hQU =>
      ordUnit_pullbackComponent_eq_of_cyclicInvariants_of_charZero sX hX
    hdim j hT P hP τ hτ0 hτ ρ hρ Q κsep H hK e he hxU hU hG hQU⟩

/-- **The different of a plt pair is klt.** If `(X, S + B)` is plt then the residue different
`B_S` has coefficient `< 1` at every prime divisor of `S` (forward adjunction). -/
theorem coeff_lt_one_of_isPltPair_of_charZero {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX))
    (P : MMP.Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (τ : RationalPluriForms sX (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : IsPoincareResidue sX j n 1 τ ρ)
    (Q : MMP.Mori.PrimeDivisor T) (B : QDivisor X) (hB : B.IsEffective) (hBP : B.coeff P = 0)
    (hplt : IsPltPair sX (n + 1) (divisorOfForm τ) (Finsupp.single P 1 + B))
    (BS : QDivisor T)
    (hBS : ∃ hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
        (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).supp,
      (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsPullback j hgen
        (Divisor.toQDivisor (divisorOfForm ρ) + BS)) :
    BS.coeff Q < 1 := by
  have : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
  have hdimT := MMP.Fourfold.topologicalKrullDim_eq_of_range_eq_support sX hdim j P hP
  obtain ⟨KS, hKS⟩ := MMP.Mori.exists_isCanonicalDivisor (j ≫ sX) hT hdimT
  exact Aux.coeff_lt_one_of_isPltPair' sX hX hdim j hT hdimT P hP τ hτ0 hτ ρ hρ Q B hB hBP hplt BS
    hBS KS hKS (fun h => MMP.Fourfold.isCartierDivisor_of_forall_generatesOn hT hKS h)
    (fun K hK KS hKS B hB hBP hD BS hBS F =>
      MMP.Fourfold.exists_isExceptional_isDiscrepancy_iff_of_isPoincareResidue sX hX n K hK P
        j hT hP KS hKS B hB hBP hD BS hBS F)

end

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **The different on a normal prime divisor in a cyclic quotient chart.** Let `X` be a normal
variety of dimension `n + 1` over an algebraically closed field `k` of characteristic zero,
`j : T ⟶ X` the inclusion of a normal prime divisor `S`,
`τ` a rational top form with `ord_S τ = -1` and `ρ` its Poincaré residue along `T`. Let `Q` be a
prime divisor of `T` with generic point `P`, and suppose the adic completion of a strict
henselization `H` of `𝒪_{X,P}` is isomorphic to `K[[x, y]]^{μ_m}` (`MMP.Flips.cyclicInvariants`,
in the setting `MMP.Flips.IsCyclicQuotientSetting K m q`) by an isomorphism sending `I_S` to
`(x) ∩ K[[x, y]]^{μ_m}`. Let `B_i` (`i : ι`) be prime divisors of `X` other than `S`. Then there
are `r : ι → ℕ`, with `r i = 0` whenever `P ∉ B_i`, such that for every `b : ι → ℚ`, `b ≥ 0`,
with `D = div τ + S + ∑ b_i B_i` `ℚ`-Cartier: every `ℚ`-divisor `B_S` on `T` with
`div ρ + B_S = D|_T` has coefficient `1 - 1/m + ∑ r_i b_i / m` at `Q`, and if the pair
`(X, S + ∑ b_i B_i)` is plt then `∑ r_i b_i < 1`. -/
public theorem _root_.MMP.Fourfold.coeff_residueDifferent_eq_of_cyclicInvariants_of_charZero
    {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k]
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (τ : RationalPluriForms sX (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : IsPoincareResidue sX j n 1 τ ρ)
    -- the codimension-one point of `S` and the cyclic chart of its completed strict local ring
    (Q : Mori.PrimeDivisor T)
    (κsep : Type) [Field κsep]
    [Algebra (ResidueField (X.presheaf.stalk (j.base Q.genericPoint))) κsep]
    [IsSepClosure (ResidueField (X.presheaf.stalk (j.base Q.genericPoint))) κsep]
    (H : Type) [CommRing H] [IsLocalRing H] [Algebra (X.presheaf.stalk (j.base Q.genericPoint)) H]
    [IsHenselization (X.presheaf.stalk (j.base Q.genericPoint)) κsep H]
    {K : Type*} [Field K] {m : ℕ} {q : ℤ} (hK : IsCyclicQuotientSetting K m q)
    (e : AdicCompletion (maximalIdeal H) H ≃+* cyclicInvariants K m q)
    (he : ((RingHom.ker (j.stalkMap Q.genericPoint).hom).map
        (algebraMap (X.presheaf.stalk (j.base Q.genericPoint))
          (AdicCompletion (maximalIdeal H) H))).map e =
      (Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants K m q).subtype)
    -- the prime components of the boundary
    {ι : Type*} [Fintype ι] (Bi : ι → Mori.PrimeDivisor X) (hBi : ∀ i, Bi i ≠ P) :
    ∃ r : ι → ℕ, (∀ i, j.base Q.genericPoint ∉ ((Bi i).support : Set X) → r i = 0) ∧
      ∀ b : ι → ℚ, (∀ i, 0 ≤ b i) →
        (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 +
          ∑ i, b i • Finsupp.single (Bi i) 1).IsQCartier →
        (∀ BS : QDivisor T,
          (∃ hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
              (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 +
                ∑ i, b i • Finsupp.single (Bi i) 1).supp,
            (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 +
                ∑ i, b i • Finsupp.single (Bi i) 1).IsPullback j hgen
              (Divisor.toQDivisor (divisorOfForm ρ) + BS)) →
          BS.coeff Q = 1 - 1 / m + ∑ i, (r i : ℚ) * b i / m) ∧
        (IsPltPair sX (n + 1) (divisorOfForm τ)
            (Finsupp.single P 1 + ∑ i, b i • Finsupp.single (Bi i) 1) →
          ∑ i, (r i : ℚ) * b i < 1) := by

  classical
  have hm : 0 < m := hK.one_le
  -- local equations of the `m B_i` near `x`
  have hloc : ∀ i, ∃ U : X.Opens, j.base Q.genericPoint ∈ U ∧ ∃ h : (RationalFunctions X)ˣ,
      Divisor.IsLocalEquation ((m : ℤ) • Finsupp.single (Bi i) (1 : ℤ)) U h ∧
        (j.base Q.genericPoint ∉ ((Bi i).support : Set X) → h = 1) := by
    intro i
    by_cases hxi : j.base Q.genericPoint ∈ ((Bi i).support : Set X)
    · obtain ⟨U, hxU, h, hh⟩ :=
        exists_isLocalEquation_nsmul_single sX (j.base Q.genericPoint) κsep H hK e (Bi i)
      exact ⟨U, hxU, h, hh, fun h' => absurd hxi h'⟩
    · exact ⟨_, hxi, 1, isLocalEquation_one_compl _ _, fun _ => rfl⟩
  choose Ui hxUi h hh hh1 using hloc
  obtain ⟨U₀, hxU₀, φ₀, hφ₀, hcoef₀⟩ := exists_isLocalEquation_ordUnit_eq_of_charZero sX hX hdim j
      hT P hP τ
    hτ0 hτ ρ hρ Q κsep H hK e he
  -- the common neighbourhood
  let U : X.Opens := ⟨(U₀ : Set X) ∩ ⋂ i, (Ui i : Set X),
    U₀.isOpen.inter (isOpen_iInter_of_finite fun i => (Ui i).isOpen)⟩
  have hUU₀ : U ≤ U₀ := fun y hy => hy.1
  have hUi : ∀ i, U ≤ Ui i := fun i y hy => Set.mem_iInter.mp hy.2 i
  have hxU : j.base Q.genericPoint ∈ U := ⟨hxU₀, Set.mem_iInter.mpr hxUi⟩
  have hQU : j (componentGenericPoint T Q.component) ∈ U :=
    (map_specializes_genericPoint j Q).mem_open U.isOpen hxU
  have hQU₀ : j (componentGenericPoint T Q.component) ∈ U₀ := hUU₀ hQU
  have hG : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
      DivisorWithCoeffs.supp ((m : ℤ) • (divisorOfForm τ + Finsupp.single P (1 : ℤ))) :=
    map_componentGenericPoint_notMem_supp j P hP (by
      rw [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
        DivisorWithCoeffs.coeff_single_self, coeff_divisorOfForm, hτ]
      simp)
  have hB : ∀ i, ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
      DivisorWithCoeffs.supp ((m : ℤ) • Finsupp.single (Bi i) (1 : ℤ)) := fun i =>
    map_componentGenericPoint_notMem_supp j P hP (by
      rw [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_single_of_ne (hBi i), smul_zero])
  have hφU := hφ₀.mono hUU₀
  have hhU : ∀ i, Divisor.IsLocalEquation ((m : ℤ) • Finsupp.single (Bi i) (1 : ℤ)) U (h i) :=
    fun i => (hh i).mono (hUi i)
  set o : ι → ℤ := fun i => Q.ordUnit (pullbackComponent j (hB i) (hhU i) Q.component hQU)
    with hodef
  have ho : ∀ i, 0 ≤ o i := fun i =>
    ordUnit_pullbackComponent_nonneg j Q (fun E => by
      rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul]
      exact mul_nonneg (by positivity) (by
        rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]; split_ifs <;> simp))
      hxU (hhU i) (hB i) hQU
  have h0 : Q.ordUnit (pullbackComponent j hG hφU Q.component hQU) =
      m * Q.ordForm ρ + (m - 1) := hcoef₀ hG hQU₀
  refine ⟨fun i => (o i).toNat, fun i hi => ?_, fun b hb hD => ?_⟩
  · simp only [hodef, Int.toNat_eq_zero]
    exact (ordUnit_pullbackComponent_one j Q (hh1 i hi) (hhU i) (hB i) hQU).le
  have hcast : ∀ i, (((o i).toNat : ℕ) : ℚ) = (o i : ℚ) := fun i => by
    exact_mod_cast Int.toNat_of_nonneg (ho i)
  have hDG : Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 +
      ∑ i, b i • Finsupp.single (Bi i) 1 =
      Divisor.toQDivisor (divisorOfForm τ + Finsupp.single P (1 : ℤ)) +
        ∑ i, b i • Finsupp.single (Bi i) 1 := by
    rw [map_add]
    congr 2
    refine DivisorWithCoeffs.ext' fun E => ?_
    rw [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
      Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp
  -- the coefficient formula
  have hformula : ∀ BS : QDivisor T,
      (∃ hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
          (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 +
            ∑ i, b i • Finsupp.single (Bi i) 1).supp,
        (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 +
            ∑ i, b i • Finsupp.single (Bi i) 1).IsPullback j hgen
          (Divisor.toQDivisor (divisorOfForm ρ) + BS)) →
      BS.coeff Q = 1 - 1 / m + ∑ i, ((o i).toNat : ℚ) * b i / m := by
    rintro BS ⟨hgen, hBS⟩
    have key := mul_coeff_isPullback_eq j Q _ Bi b hm hxU hφU hhU hG hB hQU hDG hD hBS
    rw [h0, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm] at key
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    simp only [hcast]
    rw [← Finset.sum_div]
    field_simp
    push_cast at key
    have hs : ∑ i, (o i : ℚ) * b i = ∑ i, b i * (o i : ℚ) :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hs]
    simp only [hodef] at key ⊢
    linear_combination key
  refine ⟨hformula, fun hplt => ?_⟩
  -- the different exists, and its coefficient is `< 1`
  have hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
      (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 +
        ∑ i, b i • Finsupp.single (Bi i) 1).supp :=
    map_componentGenericPoint_notMem_supp j P hP (by
      rw [hDG, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_add,
        DivisorWithCoeffs.coeff_single_self, coeff_divisorOfForm, hτ, DivisorWithCoeffs.coeff_apply,
        Finsupp.finset_sum_apply]
      simp [Finsupp.single_apply, Ne.symm (hBi _)])
  obtain ⟨R₀, hR₀, -⟩ := hD.existsUnique_isPullback hgen
  set BS := R₀ - Divisor.toQDivisor (divisorOfForm ρ)
  have hBS : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 +
      ∑ i, b i • Finsupp.single (Bi i) 1).IsPullback j hgen
        (Divisor.toQDivisor (divisorOfForm ρ) + BS) := by
    rwa [add_sub_cancel]
  have hlt := coeff_lt_one_of_isPltPair_of_charZero sX hX hdim j hT P hP τ hτ0 hτ ρ hρ Q
    (∑ i, b i • Finsupp.single (Bi i) 1) (fun E => by
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
      exact Finset.sum_nonneg fun i _ => by
        rw [Finsupp.smul_apply, smul_eq_mul]
        exact mul_nonneg (hb i) (by rw [Finsupp.single_apply]; split_ifs <;> simp))
    (by
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
      simp [Finsupp.single_apply, Ne.symm (hBi _)])
    hplt BS ⟨hgen, hBS⟩
  rw [hformula BS ⟨hgen, hBS⟩] at hlt
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  rw [← Finset.sum_div] at hlt
  have : (∑ i, ((o i).toNat : ℚ) * b i) / m < 1 / m := by linarith
  exact (div_lt_div_iff_of_pos_right hm').mp this

end

end MMP.CyclicChartDifferent

open CategoryTheory AlgebraicGeometry IsLocalRing

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **The different on a normal prime divisor in a cyclic quotient chart.** Let `X` be a normal
complex variety of dimension `n + 1`, `j : T ⟶ X` the inclusion of a normal prime divisor `S`,
`τ` a rational top form with `ord_S τ = -1` and `ρ` its Poincaré residue along `T`. Let `Q` be a
prime divisor of `T` with generic point `P`, and suppose the adic completion of a strict
henselization `H` of `𝒪_{X,P}` is isomorphic to `K[[x, y]]^{μ_m}` (`MMP.Flips.cyclicInvariants`,
in the setting `MMP.Flips.IsCyclicQuotientSetting K m q`) by an isomorphism sending `I_S` to
`(x) ∩ K[[x, y]]^{μ_m}`. Let `B_i` (`i : ι`) be prime divisors of `X` other than `S`. Then there
are `r : ι → ℕ`, with `r i = 0` whenever `P ∉ B_i`, such that for every `b : ι → ℚ`, `b ≥ 0`,
with `D = div τ + S + ∑ b_i B_i` `ℚ`-Cartier: every `ℚ`-divisor `B_S` on `T` with
`div ρ + B_S = D|_T` has coefficient `1 - 1/m + ∑ r_i b_i / m` at `Q`, and if the pair
`(X, S + ∑ b_i B_i)` is plt then `∑ r_i b_i < 1`. -/
@[mmp "lem_fourfold_normal_prime_cyclic_chart_different"]
public theorem coeff_residueDifferent_eq_of_cyclicInvariants
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety ℂ (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (τ : RationalPluriForms sX (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : IsPoincareResidue sX j n 1 τ ρ)
    -- the codimension-one point of `S` and the cyclic chart of its completed strict local ring
    (Q : Mori.PrimeDivisor T)
    (κsep : Type) [Field κsep]
    [Algebra (ResidueField (X.presheaf.stalk (j.base Q.genericPoint))) κsep]
    [IsSepClosure (ResidueField (X.presheaf.stalk (j.base Q.genericPoint))) κsep]
    (H : Type) [CommRing H] [IsLocalRing H] [Algebra (X.presheaf.stalk (j.base Q.genericPoint)) H]
    [IsHenselization (X.presheaf.stalk (j.base Q.genericPoint)) κsep H]
    {K : Type*} [Field K] {m : ℕ} {q : ℤ} (hK : IsCyclicQuotientSetting K m q)
    (e : AdicCompletion (maximalIdeal H) H ≃+* cyclicInvariants K m q)
    (he : ((RingHom.ker (j.stalkMap Q.genericPoint).hom).map
        (algebraMap (X.presheaf.stalk (j.base Q.genericPoint))
          (AdicCompletion (maximalIdeal H) H))).map e =
      (Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants K m q).subtype)
    -- the prime components of the boundary
    {ι : Type*} [Fintype ι] (Bi : ι → Mori.PrimeDivisor X) (hBi : ∀ i, Bi i ≠ P) :
    ∃ r : ι → ℕ, (∀ i, j.base Q.genericPoint ∉ ((Bi i).support : Set X) → r i = 0) ∧
      ∀ b : ι → ℚ, (∀ i, 0 ≤ b i) →
        (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 +
          ∑ i, b i • Finsupp.single (Bi i) 1).IsQCartier →
        (∀ BS : QDivisor T,
          (∃ hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
              (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 +
                ∑ i, b i • Finsupp.single (Bi i) 1).supp,
            (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 +
                ∑ i, b i • Finsupp.single (Bi i) 1).IsPullback j hgen
              (Divisor.toQDivisor (divisorOfForm ρ) + BS)) →
          BS.coeff Q = 1 - 1 / m + ∑ i, (r i : ℚ) * b i / m) ∧
        (IsPltPair sX (n + 1) (divisorOfForm τ)
            (Finsupp.single P 1 + ∑ i, b i • Finsupp.single (Bi i) 1) →
          ∑ i, (r i : ℚ) * b i < 1) :=
  coeff_residueDifferent_eq_of_cyclicInvariants_of_charZero sX hX hdim j hT P hP τ hτ0 hτ ρ hρ Q
      κsep H
    hK e he Bi hBi

end MMP.Fourfold

end
