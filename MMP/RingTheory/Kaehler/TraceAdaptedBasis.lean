module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Smooth.Field

/-!
# Traces of elements vanishing over the closed point, and adapted bases of differentials

Two pieces of local algebra for the trace of forms along a finite cover.

**Traces.** Let `A` be a local ring with maximal ideal `𝔪` and `B` a finite free `A`-algebra. If
`y ∈ B` lies in every prime of `B` over `𝔪`, then `Tr_{B/A}(y) ∈ 𝔪`. Indeed the image of `y` in
the finite-dimensional `κ(𝔪)`-algebra `B/𝔪B` lies in every prime ideal, hence is nilpotent, and
the trace of a nilpotent endomorphism of a vector space vanishes; the trace commutes with the
base change `A → κ(𝔪)`. Applied to `y = t x` for a uniformizer `t` of a discrete valuation ring
`A`, this says that an element `x` of a finite extension with `v_q(x) ≥ 1 - e_q` at every place
`q` over `𝔪` has an integral trace: the tame trace estimate.

**Adapted bases.** Let `R` be a local `k`-algebra, `k` a perfect field, which is formally smooth
and essentially of finite type over `k`, with `Ω_{R/k}` free of finite rank, and let `s` generate
the maximal ideal of `R`, `R` not a field. Then `Ω_{R/k}` has a basis `ds, dy₁, …, dyₙ` for some
`yᵢ ∈ R`. The residue field `κ` is formally smooth over the perfect field `k`, so the conormal map
`𝔪/𝔪² → κ ⊗ Ω_{R/k}` is injective and `1 ⊗ ds ≠ 0`; complete it by classes `1 ⊗ dyᵢ` to a basis
of `κ ⊗ Ω_{R/k}` and lift by Nakayama's lemma.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.trace_mem_maximalIdeal_of_forall_mem`:
  `Tr_{B/A}(y) ∈ 𝔪` for `y` in every prime over `𝔪`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_algebraMap_eq_trace_of_forall_isMaximal`: the
  tame trace estimate `Tr_{L/K}(x) ∈ A`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_basis_of_linearIndependent_tmul`: a family of a
  free module of finite rank over a local ring, of the right cardinality, whose classes are
  linearly independent modulo `𝔪`, is a basis.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_basis_D_cons`: the basis `ds, dy₁, …, dyₙ`.

## References

* [J.-P. Serre, *Corps locaux*][Serre1962], Chapitre III
-/

@[expose] public section

open TensorProduct KaehlerDifferential IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

section Trace

variable {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
  [Module.Free A B] [Module.Finite A B]

/-- **Traces of elements vanishing over the closed point.** If `y` lies in every prime of the
finite free `A`-algebra `B` lying over the maximal ideal of the local ring `A`, then its trace
lies in the maximal ideal. -/
theorem trace_mem_maximalIdeal_of_forall_mem {y : B}
    (hy : ∀ Q : Ideal B, Q.IsPrime → Q.comap (algebraMap A B) = maximalIdeal A → y ∈ Q) :
    Algebra.trace A B y ∈ maximalIdeal A := by
  classical
  let κ := ResidueField A
  let φ : B →ₐ[A] κ ⊗[A] B := Algebra.TensorProduct.includeRight
  -- the image of `y` in `κ ⊗ B` lies in every prime, so it is nilpotent
  have hnil : IsNilpotent ((1 : κ) ⊗ₜ[A] y) := by
    rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
    intro P hP
    have hP' : Ideal.IsPrime P := hP
    have hc : Ideal.comap (algebraMap A B) (Ideal.comap φ.toRingHom P) = maximalIdeal A := by
      rw [Ideal.comap_comap, show φ.toRingHom.comp (algebraMap A B) =
        (algebraMap κ (κ ⊗[A] B)).comp (algebraMap A κ) from
          φ.comp_algebraMap.trans (IsScalarTower.algebraMap_eq _ _ _), ← Ideal.comap_comap,
        Ideal.eq_bot_of_prime (Ideal.comap (algebraMap κ (κ ⊗[A] B)) P),
        ← RingHom.ker_eq_comap_bot]
      exact ker_residue
    exact hy _ (Ideal.comap_isPrime _ _) hc
  -- the trace commutes with the base change to `κ`
  have hb : (Algebra.lmul A B y).baseChange κ = Algebra.lmul κ (κ ⊗[A] B) ((1 : κ) ⊗ₜ[A] y) := by
    ext b
    simp
  have htr : algebraMap A κ (Algebra.trace A B y) = 0 := by
    rw [Algebra.trace_apply, ← LinearMap.trace_baseChange, hb]
    exact (LinearMap.isNilpotent_trace_of_isNilpotent
      (hnil.map (Algebra.lmul κ (κ ⊗[A] B)))).eq_zero
  rwa [← ker_residue, RingHom.mem_ker]

/-- The fraction field of a domain `B` integral over a domain `A` is its localization at the
nonzero elements of `A`. -/
theorem isLocalization_algebraMapSubmonoid_of_isFractionRing {A B L : Type*} [CommRing A]
    [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B]
    (hinj : Function.Injective (algebraMap A B)) [CommRing L] [Algebra B L] [IsFractionRing B L] :
    IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (Algebra.algebraMapSubmonoid B
    (nonZeroDivisors A)) (nonZeroDivisors B) ?_ ?_).2 inferInstance
  · rintro _ ⟨a, ha, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero fun h =>
      nonZeroDivisors.ne_zero ha (hinj (h.trans (map_zero _).symm))
  · intro c hc
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Ideal.comap_ne_bot_of_integral_mem (nonZeroDivisors.ne_zero hc)
        (Ideal.mem_span_singleton_self c) (Algebra.IsIntegral.isIntegral (R := A) c))
    exact ⟨algebraMap A B a, ⟨a, mem_nonZeroDivisors_of_ne_zero ha0, rfl⟩,
      Ideal.mem_span_singleton.1 ha⟩

/-- An element `y` of an algebra `L` over `B` which is brought into `B` by a multiplier outside
each maximal ideal of `B` lies in the image of `B`. -/
theorem exists_algebraMap_eq_of_forall_isMaximal {B L : Type*} [CommRing B] [CommRing L]
    [Algebra B L] (y : L)
    (hy : ∀ Q : Ideal B, Q.IsMaximal → ∃ c ∉ Q, ∃ b, algebraMap B L c * y = algebraMap B L b) :
    ∃ b, y = algebraMap B L b := by
  let J : Ideal B :=
    { carrier := {c | ∃ b, algebraMap B L c * y = algebraMap B L b}
      add_mem' := fun {c c'} ⟨b, hb⟩ ⟨b', hb'⟩ => ⟨b + b', by rw [map_add, add_mul, hb, hb',
        map_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := fun r {c} ⟨b, hb⟩ => ⟨r * b, by rw [smul_eq_mul, map_mul, mul_assoc, hb,
        map_mul]⟩ }
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQ, hJQ⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨c, hc, hcb⟩ := hy Q hQ
    exact hc (hJQ hcb)
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, algebraMap B L 1 * y = algebraMap B L b₀ :=
    (show (1 : B) ∈ J from hJ ▸ trivial)
  exact ⟨b₀, by rwa [map_one, one_mul] at hb₀⟩

variable {K L : Type*} [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]

/-- **The tame trace estimate.** Let `A` be a local domain whose maximal ideal is generated by
`t ≠ 0`, `B` a domain which is a finite free `A`-algebra, `K ⊆ L` their fraction fields. If
`x ∈ L` is such that `t x` lies in the maximal ideal of `B_Q` for every maximal ideal `Q` of `B`
(`v_Q(x) ≥ 1 - e_Q` for a discrete valuation ring `B_Q`), then `Tr_{L/K}(x) ∈ A`. -/
theorem exists_algebraMap_eq_trace_of_forall_isMaximal [IsDomain A] [IsDomain B]
    (hinj : Function.Injective (algebraMap A B)) {t : A} (ht : t ≠ 0)
    (hm : maximalIdeal A = Ideal.span {t}) (x : L)
    (hx : ∀ Q : Ideal B, Q.IsMaximal → ∃ b ∈ Q, ∃ c ∉ Q,
      algebraMap B L c * (algebraMap A L t * x) = algebraMap B L b) :
    ∃ a : A, algebraMap A K a = Algebra.trace K L x := by
  classical
  set y := algebraMap A L t * x with hy
  -- `y` lies in `B`
  obtain ⟨b₀, hb₀⟩ := exists_algebraMap_eq_of_forall_isMaximal y fun Q hQ => by
    obtain ⟨b, -, c, hc, hcb⟩ := hx Q hQ
    exact ⟨c, hc, b, hcb⟩
  -- `b₀` lies in every prime of `B` over the maximal ideal of `A`
  have hb₀Q : ∀ Q : Ideal B, Q.IsPrime → Q.comap (algebraMap A B) = maximalIdeal A → b₀ ∈ Q := by
    intro Q hQ hQA
    have hQm : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) Q
      (by rw [Ideal.under_def, hQA]; exact maximalIdeal.isMaximal A)
    obtain ⟨b, hb, c, hc, hcb⟩ := hx Q hQm
    rw [hb₀, ← map_mul] at hcb
    exact (hQ.mem_or_mem (IsFractionRing.injective B L hcb ▸ hb)).resolve_left hc
  have htr := trace_mem_maximalIdeal_of_forall_mem hb₀Q
  rw [hm, Ideal.mem_span_singleton] at htr
  obtain ⟨a, ha⟩ := htr
  refine ⟨a, ?_⟩
  have := isLocalization_algebraMapSubmonoid_of_isFractionRing (L := L) hinj
  have hL := Algebra.trace_localization A (nonZeroDivisors A) b₀ (Rₘ := K) (Sₘ := L)
  rw [← hb₀, hy, ha] at hL
  have h1 : Algebra.trace K L (algebraMap A L t * x) = algebraMap A K t * Algebra.trace K L x := by
    rw [IsScalarTower.algebraMap_apply A K L, ← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [h1, map_mul] at hL
  exact (mul_left_cancel₀ (by rwa [Ne, IsFractionRing.to_map_eq_zero_iff]) hL).symm

end Trace

/-- A family of `#ι` vectors spanning a module with a basis indexed by `ι` is linearly
independent. -/
theorem linearIndependent_of_span_eq_top_of_card_eq {R M ι ι' : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Fintype ι] [Fintype ι'] (b : Module.Basis ι R M)
    (v : ι' → M) (hspan : Submodule.span R (Set.range v) = ⊤)
    (hcard : Fintype.card ι' = Fintype.card ι) : LinearIndependent R v := by
  nontriviality R
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge
    (by rw [hcard, Module.finrank_eq_card_basis b])

section Nakayama

variable {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]

/-- **Lifting bases by Nakayama's lemma.** Let `M` be a free module of finite rank over a local
ring with a basis indexed by `ι`, and `v` a family indexed by `ι'` with `#ι' = #ι` whose classes
are linearly independent in `κ ⊗ M`. Then `v` is a basis of `M`. -/
theorem exists_basis_of_linearIndependent_tmul {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (b : Module.Basis ι R M) (v : ι' → M)
    (hv : LinearIndependent (ResidueField R) fun i => (1 : ResidueField R) ⊗ₜ[R] v i)
    (hcard : Fintype.card ι' = Fintype.card ι) :
    ∃ c : Module.Basis ι' R M, ⇑c = v := by
  classical
  have : Module.Finite R M := Module.Finite.of_basis b
  -- the classes of `v` are a basis of `κ ⊗ M`
  have hspan : Submodule.span R (Set.range v) = ⊤ := by
    rcases isEmpty_or_nonempty ι' with h | h
    · have : IsEmpty ι := Fintype.card_eq_zero_iff.1 (hcard ▸ Fintype.card_eq_zero)
      rw [eq_top_iff]
      intro m _
      rw [← b.sum_repr m]
      simp
    · let bred := basisOfLinearIndependentOfCardEqFinrank hv
        (by rw [Module.finrank_eq_card_basis (b.baseChange (ResidueField R)), hcard])
      exact span_eq_top_of_tmul_eq_basis v bred fun i => by
        simp [bred, coe_basisOfLinearIndependentOfCardEqFinrank]
  exact ⟨Module.Basis.mk (linearIndependent_of_span_eq_top_of_card_eq b v hspan hcard)
    hspan.ge, by simp⟩

end Nakayama

section AdaptedBasis

/-- A non-unit `s` of a local ring with `s ∈ (s)²` is zero. -/
theorem eq_zero_of_mem_span_singleton_sq {R : Type*} [CommRing R] [IsLocalRing R] {s : R}
    (hs : s ∈ maximalIdeal R) (h : s ∈ Ideal.span {s} ^ 2) : s = 0 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  obtain ⟨r, hr⟩ := h
  have : s * (1 - s * r) = 0 := by rw [mul_sub, mul_one, ← mul_assoc, ← pow_two, ← hr, sub_self]
  have hu : IsUnit (1 - s * r) := by
    refine (isUnit_or_isUnit_of_add_one (a := s * r) (b := 1 - s * r) (by ring)).resolve_left ?_
    intro hu
    exact (maximalIdeal.isMaximal R).ne_top
      (Ideal.eq_top_of_isUnit_mem _ (Ideal.mul_mem_right r _ hs) hu)
  exact (hu.mul_left_eq_zero).1 this

/-- The classes `1 ⊗ dr`, `r ∈ R`, span `A ⊗_R Ω_{R/k}` over any `R`-algebra `A`. -/
theorem top_le_span_range_one_tmul_D (k : Type*) {R : Type*} [CommRing k] [CommRing R]
    [Algebra k R] (A : Type*) [CommRing A] [Algebra R A] :
    ⊤ ≤ Submodule.span A (Set.range fun r : R => (1 : A) ⊗ₜ[R] D k R r) := by
  have := Submodule.baseChange_span (R := R) A (Set.range (D k R))
  rw [span_range_derivation, Submodule.baseChange_top, ← Set.range_comp] at this
  exact this.le

variable (k : Type*) [Field k] {R : Type*} [CommRing R] [IsLocalRing R] [Algebra k R]

/-- For `R` formally smooth over the perfect field `k` with maximal ideal generated by `s ≠ 0`,
the class `1 ⊗ ds` in `κ ⊗_R Ω_{R/k}` is nonzero. -/
theorem one_tmul_D_ne_zero [PerfectField k] [Algebra.FormallySmooth k R]
    [Algebra.EssFiniteType k R] {s : R} (hm : maximalIdeal R = Ideal.span {s}) (hs : s ≠ 0) :
    (1 : ResidueField R) ⊗ₜ[R] D k R s ≠ 0 := by
  let κ := ResidueField R
  have hsurj : Function.Surjective (algebraMap R κ) := residue_surjective
  have : Algebra.EssFiniteType k κ :=
    Algebra.EssFiniteType.of_surjective (IsScalarTower.toAlgHom k R κ) hsurj
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := k) (P := R) (A := κ)
    hsurj).1 inferInstance
  have hker : RingHom.ker (algebraMap R κ) = Ideal.span {s} := by
    rw [ResidueField.algebraMap_eq, ker_residue, hm]
  have hsm : s ∈ RingHom.ker (algebraMap R κ) := hker ▸ Ideal.mem_span_singleton_self s
  intro h0
  have h1 : Ideal.toCotangent _ ⟨s, hsm⟩ = 0 := by
    have := congrArg l (KaehlerDifferential.kerCotangentToTensor_toCotangent k R κ ⟨s, hsm⟩)
    rw [h0, map_zero] at this
    have h2 := congrArg (fun f => f (Ideal.toCotangent _ ⟨s, hsm⟩)) hl
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply] at h2
    rw [← h2, this]
  rw [Ideal.toCotangent_eq_zero] at h1
  exact hs (eq_zero_of_mem_span_singleton_sq (hm ▸ Ideal.mem_span_singleton_self s)
    (by rwa [← hker]))

/-- **An adapted basis of the differentials.** Let `R` be a local `k`-algebra, formally smooth and
essentially of finite type over the perfect field `k`, with `Ω_{R/k}` free of finite rank, and let
`s ≠ 0` generate the maximal ideal. Then `Ω_{R/k}` has a basis `ds, dy₁, …, dyₙ`. -/
theorem exists_basis_D_cons [PerfectField k] [Algebra.FormallySmooth k R]
    [Algebra.EssFiniteType k R] {ι : Type*} [Finite ι] (b : Module.Basis ι R Ω[R⁄k]) {s : R}
    (hm : maximalIdeal R = Ideal.span {s}) (hs : s ≠ 0) :
    ∃ (n : ℕ) (y : Fin n → R) (c : Module.Basis (Fin (n + 1)) R Ω[R⁄k]),
      ∀ i, c i = D k R ((Fin.cons s y : Fin (n + 1) → R) i) := by
  classical
  have := Fintype.ofFinite ι
  let κ := ResidueField R
  -- extend `1 ⊗ ds` to a basis among the classes `1 ⊗ dr`
  have hT := top_le_span_range_one_tmul_D k (R := R) κ
  have hs0 : LinearIndepOn κ id ({(1 : κ) ⊗ₜ[R] D k R s} : Set (κ ⊗[R] Ω[R⁄k])) :=
    (linearIndepOn_singleton_iff κ).2 (one_tmul_D_ne_zero k hm hs)
  have hst : ({(1 : κ) ⊗ₜ[R] D k R s} : Set (κ ⊗[R] Ω[R⁄k])) ⊆
      Set.range fun r : R => (1 : κ) ⊗ₜ[R] D k R r :=
    Set.singleton_subset_iff.2 ⟨s, rfl⟩
  let bE := Module.Basis.extendLe hs0 hst hT
  let J := hs0.extend hst
  have : Finite J := Module.Finite.finite_basis bE
  have : Fintype J := Fintype.ofFinite J
  have hJT : ∀ j : J, ∃ r : R, (1 : κ) ⊗ₜ[R] D k R r = j := fun j =>
    Module.Basis.extendLe_subset hs0 hst hT ⟨j, by rw [Module.Basis.coe_extendLe]⟩
  choose rr hrr using hJT
  have hj0 : (1 : κ) ⊗ₜ[R] D k R s ∈ J := by
    have := Module.Basis.subset_extendLe hs0 hst hT rfl
    rw [Module.Basis.coe_extendLe] at this
    obtain ⟨j, hj⟩ := this
    exact hj ▸ j.2
  let j0 : J := ⟨_, hj0⟩
  -- reindex `J` by `Fin (n + 1)` with `j0` first
  have hcardJ : Fintype.card J = Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis bE, Module.finrank_eq_card_basis (b.baseChange κ)]
  have : Nonempty J := ⟨j0⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := J))
  let e₀ : J ≃ Fin (n + 1) := (Fintype.equivFin J).trans (finCongr hn)
  let σ : J ≃ Fin (n + 1) := e₀.trans (Equiv.swap (e₀ j0) 0)
  have hσ : σ.symm 0 = j0 := by
    simp [σ, Equiv.swap_apply_right]
  let y : Fin n → R := fun i => rr (σ.symm i.succ)
  have hred : (fun i => (1 : κ) ⊗ₜ[R] D k R ((Fin.cons s y : Fin (n + 1) → R) i)) =
      bE ∘ σ.symm := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero, Function.comp_apply, hσ]
      rw [Module.Basis.coe_extendLe]
    · simp only [Fin.cons_succ, Function.comp_apply, y, hrr]
      rw [Module.Basis.coe_extendLe]
  obtain ⟨c, hc⟩ := exists_basis_of_linearIndependent_tmul b
    (fun i => D k R ((Fin.cons s y : Fin (n + 1) → R) i))
    (by
      rw [hred]
      exact bE.linearIndependent.comp _ σ.symm.injective)
    (by rw [Fintype.card_fin, ← hcardJ, hn])
  exact ⟨n, y, c, congrFun hc⟩

end AdaptedBasis

end MMP.FourfoldProofs.FractionalLogComplexProof
