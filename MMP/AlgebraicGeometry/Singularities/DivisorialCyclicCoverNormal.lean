module

public import MMP.AlgebraicGeometry.Morphisms.FinrankChart
public import MMP.AlgebraicGeometry.Singularities.CyclicCover.IndexOneCover
public import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.S2
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
public import MMP.AlgebraicGeometry.Divisor.SmallModelPushforward

/-!
# The divisorial cyclic cover of a trivialized multiple is normal

Let `X` be a normal variety over a field `k` of characteristic zero, `D` a Weil divisor on `X`,
`m ≥ 1` and `φ ∈ K(X)^×` with `div(φ) + mD = 0`. The cyclic cover
`p : X' = Spec_X 𝒜 → X` of the algebra `𝒜 = ⊕_{i=0}^{m-1} 𝒪_X(-iD)`, with multiplication by
`φ` on crossing degree `m`, is finite, normal, of degree `m` at the generic point of `X`, and
surjective. It is étale over a neighbourhood of a point `x` if and only if `D` is Cartier at
`x`. The reflexive Weil pull-back `p^w(𝒪_X(D))` is principal, and `X` is the quotient of `X'` by
the grading action of `μ_m`: `𝒪_X → p_* 𝒪_{X'} = 𝒜` is injective with image the invariants of
the grading, the degree-`0` summand `𝒪_X(-0·D) = 𝒪_X` of `𝒜`.

## Main results

* `MMP.Mori.DivisorialCyclicCover.isNormal_cover_of_principalDivisor_add_smul_eq_zero`

## Implementation notes

The action of `μ_m` is recorded by the `ℤ/m`-grading of `𝒜` (the coaction of the group scheme
`μ_m`), whose invariants are the degree-`0` part; no roots of unity are needed in `Γ(X, 𝒪_X)`.
A section of `p_* 𝒪_{X'}` over `U` is the image of a section `a` of `𝒜(U)` under
`Stacks.RelativeSpec.universalAlgebraMap`, an isomorphism `𝒜 ≅ p_* 𝒪_{X'}`, and its degree-`i`
part is `MMP.Mori.DivisorialCyclicCover.coeffEquiv` of `a` at `i`. The quotient statement says
that the image of `p^♯` is the set of such sections with vanishing components in every degree
`i ≠ 0`. The generic degree is `AlgebraicGeometry.Scheme.Hom.finrank` at the generic point,
where `𝒪_{X,η} = K(X)` is a field. The reflexive pull-back is `MMP.Flips.weilPullback` of the
Weil divisorial subsheaf whose sections are those of `𝒪_X(D)`; a principal subsheaf of
`K(X')` is one whose sections over every open `U'` are the `Γ(X', U')`-multiples of a single
unit `ψ` of `K(X')`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.3
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.52, 5.19
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Order MMP.Mori
  MMP.Mori.DivisorialCyclicCover

universe u

namespace MMP.Mori.DivisorialCyclicCover

namespace CoverNormality

section Rank

open Module in
/-- Rank at the generic point of a module `M` that localizes to a finite free `K`-module. -/
private theorem rankAtStalk_bot_eq_finrank {R M E K : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [CommRing K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup E] [Module K E] [Module R E] [IsScalarTower R K E] (f : M →ₗ[R] E)
    [IsLocalizedModule (nonZeroDivisors R) f] :
    Module.rankAtStalk (R := R) M ⟨⊥, Ideal.isPrime_bot⟩ = Module.finrank K E := by
  classical
  set p : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hM : p.asIdeal.primeCompl = nonZeroDivisors R := by
    simp [p, Ideal.primeCompl_bot]
  have : IsLocalization p.asIdeal.primeCompl K := by rw [hM]; infer_instance
  have : IsLocalizedModule p.asIdeal.primeCompl f := by rw [hM]; infer_instance
  let Rp := Localization.AtPrime p.asIdeal
  let e : Rp ≃ₐ[R] K := IsLocalization.algEquiv p.asIdeal.primeCompl Rp K
  let g := IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) f
  unfold Module.rankAtStalk Module.finrank
  have hc : ∀ (r : Rp) (x : LocalizedModule p.asIdeal.primeCompl M),
      g.toAddEquiv (r • x) = e r • g.toAddEquiv x := by
    intro r x
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl r
    have hs : IsUnit (algebraMap R K (s : R)) := IsLocalization.map_units K s
    have hr : algebraMap R Rp (s : R) * IsLocalization.mk' Rp a s = algebraMap R Rp a := by
      rw [mul_comm]; exact IsLocalization.mk'_spec Rp a s
    have hL : (s : R) • (IsLocalization.mk' Rp a s • x) = a • x := by
      rw [← smul_assoc, Algebra.smul_def, hr, algebraMap_smul]
    have hR : (s : R) • (e (IsLocalization.mk' Rp a s) • g.toAddEquiv x) =
        a • g.toAddEquiv x := by
      rw [← smul_assoc, Algebra.smul_def, ← e.commutes, ← map_mul, hr, e.commutes, algebraMap_smul]
    have hc1 : (s : R) • g.toAddEquiv ((IsLocalization.mk' Rp a s) • x) =
        (s : R) • (e (IsLocalization.mk' Rp a s) • g.toAddEquiv x) := by
      rw [hR]
      change (s : R) • g ((IsLocalization.mk' Rp a s) • x) = _
      rw [← map_smul, hL, map_smul]
      rfl
    rw [← algebraMap_smul K (s : R), ← algebraMap_smul K (s : R)] at hc1
    exact hs.smul_left_cancel.mp hc1
  simpa using (congr_arg Cardinal.toNat
    (lift_rank_eq_of_equiv_equiv (R := Rp) (R' := K) e g.toAddEquiv e.bijective hc))

private theorem rankAtStalk_bot_twist {R R0 A S E K : Type*} [CommRing R] [IsDomain R] [CommRing R0]
    [IsDomain R0] [CommRing A] [Algebra R A] [CommRing S] [Algebra R0 S]
    [CommRing K] [Algebra R K] [IsFractionRing R K]
    [CommRing E] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
    (ι : A →+* E) (hι : Function.Injective ι) (hιalg : ∀ r, ι (algebraMap R A r) = algebraMap R E r)
    (hsurj : ∀ z : E, ∃ s ∈ nonZeroDivisors R, ∃ a : A, ι a = algebraMap R E s * z)
    (ε : R ≃+* R0) (Φ : A ≃+* S) (hΦ : ∀ r, Φ (algebraMap R A r) = algebraMap R0 S (ε r)) :
    Module.rankAtStalk (R := R0) S ⟨⊥, Ideal.isPrime_bot⟩ = Module.finrank K E := by
  letI : Algebra R0 K := ((algebraMap R K).comp ε.symm.toRingHom).toAlgebra
  have hKR : ∀ r0 : R0, algebraMap R0 K r0 = algebraMap R K (ε.symm r0) := fun _ => rfl
  have hfr : IsFractionRing R0 K := by
    refine ⟨fun y => ?_, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
    · rw [hKR]
      refine IsLocalization.map_units K ⟨ε.symm y, mem_nonZeroDivisors_of_ne_zero ?_⟩
      intro h0
      exact nonZeroDivisors.coe_ne_zero y (by simpa using congrArg ε h0)
    · obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) z
      refine ⟨(ε a, ⟨ε b, mem_nonZeroDivisors_of_ne_zero ?_⟩), ?_⟩
      · intro h0
        exact nonZeroDivisors.coe_ne_zero b (by simpa using h0)
      · simpa [hKR] using hab
    · have : ε.symm x = ε.symm y :=
        IsFractionRing.injective R K (by simpa [hKR] using h)
      simp [ε.symm.injective this]
  let : Algebra R0 E := ((algebraMap K E).comp (algebraMap R0 K)).toAlgebra
  have : IsScalarTower R0 K E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hER : ∀ r0 : R0, algebraMap R0 E r0 = algebraMap R E (ε.symm r0) := fun r0 => by
    rw [IsScalarTower.algebraMap_apply R0 K E, hKR, ← IsScalarTower.algebraMap_apply R K E]
  let f : S →ₗ[R0] E :=
    { toFun := fun s => ι (Φ.symm s)
      map_add' := fun x y => by simp
      map_smul' := fun r0 s => by
        have h1 : Φ.symm (algebraMap R0 S r0) = algebraMap R A (ε.symm r0) := by
          rw [Φ.symm_apply_eq, hΦ]; simp
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul, h1, hιalg, hER] }
  have : IsLocalizedModule (nonZeroDivisors R0) f := by
    refine ⟨fun s => ?_, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
    · rw [Module.End.isUnit_iff]
      have hu : IsUnit (algebraMap R0 E (s : R0)) := by
        rw [IsScalarTower.algebraMap_apply R0 K E]
        exact (IsLocalization.map_units K s).map _
      obtain ⟨u, hu'⟩ := hu
      have hb : Function.Bijective fun y => (u : E) * y := (Units.mulLeft u).bijective
      rw [hu'] at hb
      convert hb using 1
    · obtain ⟨s, hs, a, ha⟩ := hsurj z
      have hs0 : ε s ≠ 0 := fun h0 => (nonZeroDivisors.ne_zero hs) (by simpa using h0)
      refine ⟨(Φ a, ⟨ε s, mem_nonZeroDivisors_of_ne_zero hs0⟩), ?_⟩
      change algebraMap R0 E (ε s) * z = ι (Φ.symm (Φ a))
      simp only [hER, RingEquiv.symm_apply_apply]
      exact ha.symm
    · have : x = y := Φ.symm.injective (hι h)
      rw [this]
  exact rankAtStalk_bot_eq_finrank f

end Rank

section KummerAlgebra

open Polynomial
open Module in
private theorem trace_mem_range_of_subalgebra {R K E : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing E]
    [Algebra K E] [Algebra R E] [IsScalarTower R K E] [Module.Finite K E]
    (S : Subalgebra R E) [Module.Finite R S] (hS : Submodule.span K (S : Set E) = ⊤)
    (c : E) (hc : c ∈ S) :
    Algebra.trace K E c ∈ Set.range (algebraMap R K) := by
  have : NoZeroSMulDivisors R E := by
    refine ⟨fun {r x} h => ?_⟩
    rw [← algebraMap_smul K r x] at h
    rcases smul_eq_zero.mp h with h | h
    · exact Or.inl ((map_eq_zero_iff _ (IsFractionRing.injective R K)).mp h)
    · exact Or.inr h
  have : Module.Free R S := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis R S
  haveI : Fintype (Module.Free.ChooseBasisIndex R S) := inferInstance
  have hind : LinearIndependent K (fun i => ((b i : S) : E)) := by
    refine (LinearIndependent.iff_fractionRing (R := R) (K := K)).mp ?_
    exact b.linearIndependent.map' (Subalgebra.val S).toLinearMap
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hsum : ∀ s : S, ((s : S) : E) = ∑ i, b.repr s i • ((b i : S) : E) := fun s => by
    calc ((s : S) : E) = Subalgebra.val S (∑ i, b.repr s i • b i) := by rw [b.sum_repr]; rfl
      _ = _ := by rw [map_sum]; rfl
  have hspan : ⊤ ≤ Submodule.span K (Set.range fun i => ((b i : S) : E)) := by
    rw [← hS]
    refine Submodule.span_le.mpr fun s hs => ?_
    rw [SetLike.mem_coe] at hs
    rw [show s = ((⟨s, hs⟩ : S) : E) from rfl, hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩)
  let b' : Basis (Module.Free.ChooseBasisIndex R S) K E := Basis.mk hind hspan
  have hb' : ∀ i, b' i = ((b i : S) : E) := fun i => Basis.mk_apply _ _ i
  have hrepr : ∀ (s : S) i, b'.repr (s : E) i = algebraMap R K (b.repr s i) := by
    intro s i
    have : (s : E) = ∑ j, algebraMap R K (b.repr s j) • b' j := by
      rw [hsum s]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [algebraMap_smul, hb' j]
    rw [this, Basis.repr_sum_self]
  rw [Algebra.trace_eq_matrix_trace b']
  refine ⟨∑ i, b.repr ⟨c * ((b i : S) : E), S.mul_mem hc (b i).2⟩ i, ?_⟩
  rw [map_sum, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, hb']
  exact (hrepr ⟨c * ((b i : S) : E), S.mul_mem hc (b i).2⟩ i).symm

/- The Kummer algebra over an abstract basis `1, w, …, wᵐ⁻¹` with `wᵐ = v`. -/
namespace KummerBasis

section

variable {R K E : Type*} [CommRing R] [Field K] [Algebra R K] [CommRing E] [Algebra K E]
  [Algebra R E] [IsScalarTower R K E] (m : ℕ) [NeZero m] (v : R) (w : E)
  (hw : w ^ m = algebraMap R E v) (B : Module.Basis (Fin m) K E) (hB : ∀ i, B i = w ^ (i : ℕ))

include hw in
private theorem pow_eq (n : ℕ) :
    w ^ n = algebraMap K E (algebraMap R K (v ^ (n / m))) * w ^ (n % m) := by
  conv_lhs => rw [← Nat.div_add_mod n m]
  rw [pow_add, pow_mul, hw, ← IsScalarTower.algebraMap_apply R K E, map_pow]

include hB in
private theorem repr_smul (c : K) (i j : Fin m) :
    B.repr (algebraMap K E c * B i) j = if i = j then c else 0 := by
  rw [← Algebra.smul_def, map_smul, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

include hw hB in
private theorem repr_pow (n : ℕ) (j : Fin m) :
    B.repr (w ^ n) j = if (n % m : ℕ) = (j : ℕ) then algebraMap R K (v ^ (n / m)) else 0 := by
  have hlt : n % m < m := Nat.mod_lt _ (NeZero.pos m)
  have : w ^ (n % m) = B ⟨n % m, hlt⟩ := (hB ⟨n % m, hlt⟩).symm
  rw [pow_eq (K := K) m v w hw, this, repr_smul m w B hB]
  simp [Fin.ext_iff]

include hw hB in
private theorem trace_pow_lt (k : ℕ) (hk : k < m) :
    Algebra.trace K E (w ^ k) = if k = 0 then (m : K) else 0 := by
  classical
  rw [Algebra.trace_eq_matrix_trace B, Matrix.trace]
  have hj : ∀ j : Fin m, Matrix.diag (Algebra.leftMulMatrix B (w ^ k)) j =
      if k = 0 then 1 else 0 := by
    intro j
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, hB, ← pow_add, repr_pow m v w hw B hB]
    have hjm : (j : ℕ) < m := j.2
    by_cases hk0 : k = 0
    · subst hk0
      simp [Nat.mod_eq_of_lt hjm, Nat.div_eq_of_lt hjm]
    · rw [if_neg hk0, if_neg]
      intro h
      by_cases hc : k + j < m
      · rw [Nat.mod_eq_of_lt hc] at h
        omega
      · have : (k + j) % m = k + j - m := by
          rw [Nat.mod_eq_sub_mod (not_lt.mp hc), Nat.mod_eq_of_lt (by omega)]
        omega
  simp only [hj]
  by_cases hk0 : k = 0 <;> simp [hk0]

include hw hB in
private theorem trace_pow (n : ℕ) :
    Algebra.trace K E (w ^ n) =
      if n % m = 0 then (m : K) * algebraMap R K (v ^ (n / m)) else 0 := by
  rw [pow_eq (K := K) m v w hw, ← Algebra.smul_def, map_smul, trace_pow_lt m v w hw B hB _
      (Nat.mod_lt _ (NeZero.pos m))]
  by_cases h : n % m = 0
  · simp [h, mul_comm]
  · simp [h]

end

variable {R K E : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing E] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
  (m : ℕ) [NeZero m]

/-- **The coordinates of an integral element** of the Kummer algebra over a PID. -/
private theorem coords_mem (hm : IsUnit (m : R)) (v : R) (hv : IsUnit v) (w : E)
    (hw : w ^ m = algebraMap R E v) (B : Module.Basis (Fin m) K E) (hB : ∀ i, B i = w ^ (i : ℕ))
    (b : E) (hb : IsIntegral R b) (j : Fin m) :
    ∃ r : R, B.repr b j = algebraMap R K r := by
  classical
  have hwI : IsIntegral R w := by
    refine ⟨Polynomial.X ^ m - Polynomial.C v, monic_X_pow_sub_C v (NeZero.ne m), ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hw, sub_self]
  let S : Subalgebra R E := Algebra.adjoin R {b, w}
  have : Module.Finite R S := Algebra.finite_adjoin_of_finite_of_isIntegral
    (Set.toFinite _) (by
      rintro x (rfl | rfl)
      exacts [hb, hwI])
  have : Module.Finite K E := Module.Finite.of_basis B
  have hS : Submodule.span K (S : Set E) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← B.span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    rw [hB]
    exact S.pow_mem (Algebra.subset_adjoin (Or.inr rfl)) _
  have hjm : (j : ℕ) < m := j.2
  set k : ℕ := (m - j) % m with hk
  have hbk : b * w ^ k ∈ S := S.mul_mem (Algebra.subset_adjoin (Or.inl rfl))
    (S.pow_mem (Algebra.subset_adjoin (Or.inr rfl)) _)
  obtain ⟨r, hr⟩ := trace_mem_range_of_subalgebra (R := R) (K := K) (E := E) S hS _ hbk
  have hsum : b * w ^ k = ∑ i, B.repr b i • w ^ ((i : ℕ) + k) := by
    conv_lhs => rw [← B.sum_repr b]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, hB, pow_add]
  have hkm : k < m := Nat.mod_lt _ (NeZero.pos m)
  have hcond : ∀ i : ℕ, i < m → ((i + k) % m = 0 ↔ i = j) := by
    intro i hi
    by_cases hj0 : (j : ℕ) = 0
    · have : k = 0 := by simp [hk, hj0, Nat.mod_eq_of_lt (NeZero.pos m)]
      rw [this, add_zero, Nat.mod_eq_of_lt hi]
      omega
    · have : k = m - j := by rw [hk, Nat.mod_eq_of_lt (by omega)]
      constructor
      · intro h
        by_cases hc : i + k < m
        · rw [Nat.mod_eq_of_lt hc] at h
          omega
        · rw [Nat.mod_eq_sub_mod (not_lt.mp hc), Nat.mod_eq_of_lt (by omega)] at h
          omega
      · intro h
        rw [h, this, show (j : ℕ) + (m - j) = m by omega, Nat.mod_self]
  have htr : Algebra.trace K E (b * w ^ k) =
      B.repr b j * ((m : K) * algebraMap R K v ^ (if (j : ℕ) = 0 then 0 else 1)) := by
    rw [hsum, map_sum]
    simp_rw [map_smul, trace_pow m v w hw B hB, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · congr 1
      rw [if_pos ((hcond j hjm).mpr rfl)]
      by_cases hj0 : (j : ℕ) = 0
      · have : k = 0 := by simp [hk, hj0, Nat.mod_eq_of_lt (NeZero.pos m)]
        rw [if_pos hj0, this, hj0]
        simp
      · have : k = m - j := by rw [hk, Nat.mod_eq_of_lt (by omega)]
        rw [if_neg hj0, this, show (j : ℕ) + (m - j) = m by omega, Nat.div_self (NeZero.pos m)]
        simp
    · intro i _ hij
      have hi : (i : ℕ) < m := i.2
      rw [if_neg (fun h => hij (Fin.ext ((hcond i hi).mp h))), mul_zero]
    · simp
  rw [htr] at hr
  obtain ⟨μ, hμ'⟩ := hm.mul (hv.pow (if (j : ℕ) = 0 then 0 else 1))
  refine ⟨r * ↑μ⁻¹, ?_⟩
  have h2 : B.repr b j * algebraMap R K ((m : R) * v ^ (if (j : ℕ) = 0 then 0 else 1))
      = algebraMap R K r := by
    rw [map_mul, map_pow, map_natCast]
    exact hr.symm
  rw [← hμ'] at h2
  calc B.repr b j = B.repr b j * algebraMap R K (↑μ * ↑μ⁻¹) := by
        rw [Units.mul_inv, map_one, mul_one]
    _ = _ := by rw [map_mul, ← mul_assoc, h2, map_mul]

end KummerBasis

end KummerAlgebra

section Coherence

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

private theorem componentGenericPoint_eq' (Z : irreducibleComponents X) :
    componentGenericPoint X Z = genericPoint X := by
  have h1 := isGenericPoint_componentGenericPoint X Z
  have hZ : Z.1 = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using Z.2
  rw [hZ] at h1
  exact h1.eq (genericPoint_spec X)

private theorem primeDivisor_genericPoint_ne (E : MMP.Mori.PrimeDivisor X) :
    E.genericPoint ≠ genericPoint X := by
  intro h
  have := E.coheight_genericPoint
  rw [h] at this
  have h0 : coheight (genericPoint X) = 0 := by
    rw [Order.coheight_eq_zero]
    intro b _
    exact ((genericPoint_spec X).specializes (Set.mem_univ b)).ge
  simp [h0] at this

private theorem exists_section_vanishing {U : X.Opens} (hU : IsAffineOpen U)
    (hηU : genericPoint X ∈ U) (E : MMP.Mori.PrimeDivisor X) :
    ∃ a : Γ(X, U), genericPoint X ∈ X.basicOpen a ∧
      (E.genericPoint ∈ U → E.genericPoint ∉ X.basicOpen a) := by
  by_cases hE : E.genericPoint ∈ U
  · let V : X.Opens := U ⊓ ⟨(closure {E.genericPoint})ᶜ, isClosed_closure.isOpen_compl⟩
    have hηV : genericPoint X ∈ V := by
      refine ⟨hηU, fun hc => primeDivisor_genericPoint_ne E ?_⟩
      exact (specializes_iff_mem_closure.mpr hc).antisymm
        ((genericPoint_spec X).specializes (Set.mem_univ _)) |>.eq
    obtain ⟨f, hfV, hηf⟩ := hU.exists_basicOpen_le ⟨_, hηV⟩ hηU
    exact ⟨f, hηf, fun _ hEf => (hfV hEf).2 (subset_closure rfl)⟩
  · exact ⟨1, by rwa [Scheme.basicOpen_one], fun h => absurd h hE⟩

/-- A regular function on an affine open `U ∋ η` that is invertible at the generic point and
vanishes at the generic point of each of finitely many prime divisors meeting `U`. -/
private theorem exists_section_vanishing_finset {U : X.Opens} (hU : IsAffineOpen U)
    (hηU : genericPoint X ∈ U) (S : Finset (MMP.Mori.PrimeDivisor X)) :
    ∃ a : Γ(X, U), genericPoint X ∈ X.basicOpen a ∧
      ∀ E ∈ S, E.genericPoint ∈ U → E.genericPoint ∉ X.basicOpen a := by
  classical
  choose g hgη hgE using exists_section_vanishing hU hηU
  refine ⟨∏ E ∈ S, g E, ?_, fun E hE hEU hEa => ?_⟩
  · induction S using Finset.induction_on with
    | empty => rwa [Finset.prod_empty, Scheme.basicOpen_one]
    | insert E s hE ih => rw [Finset.prod_insert hE, Scheme.basicOpen_mul]; exact ⟨hgη E, ih⟩
  · rw [← Finset.mul_prod_erase _ _ hE, Scheme.basicOpen_mul] at hEa
    exact hgE E hEU hEa.1

/-- **Divisorial sheaves are coherent**: on an integral locally Noetherian normal scheme, the
sections of `𝒪_X(D)` over an affine open `U` form a finite `Γ(X, U)`-module. -/
private theorem finite_divisorialSubmodule [CompactSpace X] (D : Divisor X) {U : X.Opens}
    (hU : IsAffineOpen U) : Module.Finite Γ(X, U) (D.divisorialSubmodule U) := by
  classical
  have := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  by_cases hηU : genericPoint X ∈ U
  swap
  · have : IsEmpty {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U} :=
      ⟨fun Z => hηU (componentGenericPoint_eq' Z.1 ▸ Z.2)⟩
    have : Subsingleton (D.divisorialSubmodule U) :=
      ⟨fun _ _ => Subtype.ext (funext isEmptyElim)⟩
    exact Module.Finite.of_finite
  obtain ⟨a, hηa, hEa⟩ := exists_section_vanishing_finset hU hηU D.support
  let N : ℕ := D.support.sup fun E => (D.coeff E).toNat
  -- multiplication by `a ^ N` maps `𝒪_X(D)(U)` into `𝒪_X(0)(U)`
  have hmem : ∀ φ : D.divisorialSubmodule U,
      (0 : Divisor X).IsDivisorialSection U (a ^ N • φ.1) := by
    intro φ E hEU
    have hηE := E.componentGenericPoint_mem_of_nonempty hEU
    have hEgU := E.genericPoint_mem_of_nonempty hEU
    have hgerm : X.presheaf.germ U _ hηE a = E.toComponent.hom (X.presheaf.germ U _ hEgU a) :=
      (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hEgU
        E.specializes_genericPoint a).symm
    have h0 : (0 : Divisor X).coeff E = 0 := rfl
    rw [rationalFunctions_smul_apply, map_pow, hgerm, h0, neg_zero]
    by_cases hc : 0 < D.coeff E
    · have hE : E ∈ D.support := Finsupp.mem_support_iff.mpr hc.ne'
      have hmax : X.presheaf.germ U _ hEgU a ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint) := fun hunit =>
        hEa E hE hEgU ((Scheme.mem_basicOpen X a _ hEgU).mpr hunit)
      refine (((E.ordGE_one_toComponent hmax).pow N).mul (φ.2 E hEU)).mono ?_
      have hN : (D.coeff E).toNat ≤ N :=
        Finset.le_sup (f := fun E => (D.coeff E).toNat) hE
      have := Int.toNat_of_nonneg hc.le
      omega
    · rw [← map_pow]
      exact ((φ.2 E hEU).toComponent_mul _).mono (by omega)
  let L : D.divisorialSubmodule U →ₗ[Γ(X, U)] (0 : Divisor X).divisorialSubmodule U :=
    { toFun := fun φ => ⟨a ^ N • φ.1, hmem φ⟩
      map_add' := fun φ ψ => Subtype.ext (smul_add _ _ _)
      map_smul' := fun r φ => Subtype.ext (smul_comm _ _ _) }
  have hL : Function.Injective L := by
    intro φ ψ h
    refine Subtype.ext (funext fun Z => ?_)
    have h1 := congrFun (congrArg Subtype.val h) Z
    change (a ^ N • φ.1) Z = (a ^ N • ψ.1) Z at h1
    rw [rationalFunctions_smul_apply, rationalFunctions_smul_apply] at h1
    have hu : IsUnit (X.presheaf.germ U _ Z.2 (a ^ N)) := by
      rw [map_pow]
      exact ((Scheme.mem_basicOpen X a _ Z.2).mp (by rw [componentGenericPoint_eq']; exact hηa)).pow
          N
    exact hu.mul_left_cancel h1
  -- `𝒪_X(0)(U)` is a quotient of `Γ(X, U)`
  let one : (0 : Divisor X).divisorialSubmodule U :=
    ⟨1, Divisor.IsDivisorialSection.one le_rfl U⟩
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton Γ(X, U) _ one) := by
    intro φ
    obtain ⟨s, hs⟩ := Divisor.IsDivisorialSection.exists_eq φ.2
    refine ⟨s, Subtype.ext (funext fun Z => ?_)⟩
    change X.presheaf.germ U _ Z.2 s * 1 = φ.1 Z
    rw [mul_one, ← hs]
    rfl
  have := isNoetherian_of_surjective _ (LinearMap.range_eq_top.mpr hsurj)
  have := isNoetherian_of_injective L hL
  infer_instance

end Coherence

section GenericFibre

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- Every divisorial sheaf has a nonzero regular section on an affine open containing the generic
point: a power of a function vanishing along the relevant prime divisors. -/
private theorem exists_regular_divisorialSection (M : Divisor X) {U : X.Opens}
    (hU : IsAffineOpen U) (hηU : genericPoint X ∈ U) :
    ∃ a : Γ(X, U), genericPoint X ∈ X.basicOpen a ∧
      M.IsDivisorialSection U ((toRationalFunctionsPresheaf X).app (op U) a) := by
  classical
  obtain ⟨a, hηa, hEa⟩ := exists_section_vanishing_finset hU hηU M.support
  let N : ℕ := M.support.sup fun E => (M.coeff E).natAbs
  refine ⟨a ^ (N + 1), ?_, ?_⟩
  · rw [Scheme.basicOpen_pow _ _ (Nat.succ_pos N)]
    exact hηa
  · intro E hEU
    have hηE := E.componentGenericPoint_mem_of_nonempty hEU
    have hEgU := E.genericPoint_mem_of_nonempty hEU
    have hgerm : X.presheaf.germ U _ hηE (a ^ (N + 1)) =
        E.toComponent.hom (X.presheaf.germ U _ hEgU (a ^ (N + 1))) :=
      (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hEgU
        E.specializes_genericPoint _).symm
    change E.OrdGE (-M.coeff E) (X.presheaf.germ U _ hηE (a ^ (N + 1)))
    rw [hgerm]
    by_cases hc : M.coeff E < 0
    · have hE : E ∈ M.support := Finsupp.mem_support_iff.mpr hc.ne
      have hmax : X.presheaf.germ U _ hEgU a ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint) := fun hunit =>
        hEa E hE hEgU ((Scheme.mem_basicOpen X a _ hEgU).mpr hunit)
      have hN : (M.coeff E).natAbs ≤ N :=
        Finset.le_sup (f := fun E => (M.coeff E).natAbs) hE
      rw [map_pow, map_pow]
      refine ((E.ordGE_one_toComponent hmax).pow (N + 1)).mono ?_
      push_cast
      omega
    · have h1 : E.OrdGE 0 (1 : X.presheaf.stalk (componentGenericPoint X E.component)) :=
        Or.inr (by simp)
      have := h1.toComponent_mul (X.presheaf.germ U _ hEgU (a ^ (N + 1)))
      rw [mul_one] at this
      exact this.mono (by omega)

end GenericFibre

section Fibre

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The unique irreducible component of an integral scheme. -/
private noncomputable def theComponent (X : Scheme.{u}) [IsIntegral X] : irreducibleComponents X :=
  ⟨Set.univ, by simp [irreducibleComponents_eq_singleton]⟩

private theorem eq_theComponent (Z : irreducibleComponents X) : Z = theComponent X := by
  have h' := Z.2
  simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h'
  exact Subtype.ext h'

private theorem componentGenericPoint_mem {U : X.Opens} (hU : genericPoint X ∈ U)
    (Z : irreducibleComponents X) : componentGenericPoint X Z ∈ U := by
  rw [componentGenericPoint_eq' Z]
  exact hU

@[instance_reducible]
private noncomputable def uniqueComponent {U : X.Opens} (hU : genericPoint X ∈ U) :
    Unique {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U} where
  default := ⟨theComponent X, componentGenericPoint_mem hU _⟩
  uniq Z := Subtype.ext (eq_theComponent Z.1)

/-- The germ at the generic point makes the stalk the fraction field of the sections over an
affine open. -/
private theorem isFractionRing_germ {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x = genericPoint X) (hxU : x ∈ U) :
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
    IsFractionRing Γ(X, U) (X.presheaf.stalk x) := by
  subst hx
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  exact functionField_isFractionRing_of_isAffineOpen X U hU

/-- The sections of `𝒦_X` over an affine open containing the generic point form the fraction
field of the sections of `𝒪_X`. -/
private theorem isFractionRing_rationalFunctions {U : X.Opens} (hU : IsAffineOpen U)
    (hηU : genericPoint X ∈ U) :
    IsFractionRing Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)) := by
  letI := uniqueComponent hηU
  have hZ := componentGenericPoint_mem hηU (theComponent X)
  letI : Algebra Γ(X, U) (X.presheaf.stalk (componentGenericPoint X (theComponent X))) :=
    (X.presheaf.germ U _ hZ).hom.toAlgebra
  have := isFractionRing_germ hU (componentGenericPoint_eq' (theComponent X)) hZ
  let e : ((rationalFunctionsPresheaf X).obj (op U)) ≃ₐ[Γ(X, U)]
      X.presheaf.stalk (componentGenericPoint X (theComponent X)) :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.piUnique (R := fun Z : {Z : irreducibleComponents X //
      componentGenericPoint X Z ∈ U} => X.presheaf.stalk (componentGenericPoint X Z.1)))
      (fun r => rfl)
  exact IsFractionRing.of_algEquiv e.symm

end Fibre

section Ambient

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  (m : ℕ) [NeZero m] (φ : (RationalFunctions X)ˣ)

/-- `𝓛(U)` is a `𝒦_X(U)`-algebra. -/
private noncomputable instance ambientAlgebraK (U : X.Opens) :
    Algebra ((rationalFunctionsPresheaf X).obj (op U)) ((ambient m φ).obj (op U)) :=
  ((ofRationalFunctions m φ).app (op U)).hom.toAlgebra

/-- `𝓛(U)` is a `Γ(X, U)`-algebra. -/
private noncomputable instance ambientAlgebraR (U : X.Opens) :
    Algebra Γ(X, U) ((ambient m φ).obj (op U)) :=
  ((structureMap m φ).app (op U)).hom.toAlgebra

private instance ambientTower (U : X.Opens) :
    IsScalarTower Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U))
      ((ambient m φ).obj (op U)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private theorem coeff_algebraMap_mul (U : X.Opens)
    (c : (rationalFunctionsPresheaf X).obj (op U)) (y : (ambient m φ).obj (op U)) (n : ℕ) :
    coeff m φ U n (algebraMap _ _ c * y) = c * coeff m φ U n y := by
  funext Z
  change (AdjoinRoot.modByMonicHom (poly_monic m φ Z.1)
      (AdjoinRoot.of _ (c Z) * y Z)).coeff n = c Z * _
  rw [← AdjoinRoot.algebraMap_eq, ← Algebra.smul_def, map_smul, Polynomial.coeff_smul,
    smul_eq_mul]
  rfl

/-- `𝓛(U) ≅ 𝒦_X(U)ᵐ` as `𝒦_X(U)`-modules, through the coefficients of `1, t, …, tᵐ⁻¹`. -/
private noncomputable def ambientEquivPi (U : X.Opens) :
    (ambient m φ).obj (op U) ≃ₗ[(rationalFunctionsPresheaf X).obj (op U)]
      (Fin m → (rationalFunctionsPresheaf X).obj (op U)) where
  toFun y i := coeff m φ U i y
  invFun a := reduce m φ U (∑ i : Fin m, Polynomial.monomial (i : ℕ) (a i))
  map_add' y y' := funext fun i => map_add (coeff m φ U i) y y'
  map_smul' c y := funext fun i => coeff_algebraMap_mul m φ U c y i
  left_inv y := by
    change reduce m φ U (∑ i : Fin m, Polynomial.monomial (i : ℕ) (coeff m φ U i y)) = y
    rw [Fin.sum_univ_eq_sum_range (fun n => Polynomial.monomial n (coeff m φ U n y))]
    exact reduce_sum_coeff m φ y
  right_inv a := funext fun i => by
    change coeff m φ U i (reduce m φ U (∑ i : Fin m, Polynomial.monomial (i : ℕ) (a i))) = a i
    rw [coeff_reduce_sum, dite_eq_left i.2]

private theorem finrank_ambient {U : X.Opens} (hU : IsAffineOpen U) (hηU : genericPoint X ∈ U) :
    Module.finrank ((rationalFunctionsPresheaf X).obj (op U)) ((ambient m φ).obj (op U)) = m := by
  have : IsFractionRing Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)) :=
    isFractionRing_rationalFunctions hU hηU
  have : Nontrivial Γ(X, U) := by
    have : Nonempty U := ⟨⟨_, hηU⟩⟩
    infer_instance
  have : Nontrivial ((rationalFunctionsPresheaf X).obj (op U)) :=
    (IsFractionRing.injective Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U))).nontrivial
  rw [(ambientEquivPi m φ U).finrank_eq, Module.finrank_fin_fun]

end Ambient

section CarrierLocalization

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (m : ℕ) [NeZero m] (D : Divisor X) {φ : (RationalFunctions X)ˣ}
  (hφ : 0 ≤ principalDivisor φ + m • D)

include hφ in
/-- After multiplying by a nonzero regular function, every element of `𝓛(U)` lies in `𝒜(U)`. -/
private theorem exists_smul_mem_carrier {U : X.Opens} (hU : IsAffineOpen U)
    (hηU : genericPoint X ∈ U) (z : (ambient m φ).obj (op U)) :
    ∃ (s : Γ(X, U)) (hs : s ∈ nonZeroDivisors Γ(X, U)) (a : (localSubalgebra m D hφ).carrier U),
      a.1 = algebraMap Γ(X, U) _ s * z := by
  classical
  have : IsFractionRing Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)) :=
    isFractionRing_rationalFunctions hU hηU
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have : IsDomain Γ(X, U) := IsIntegral.component_integral U
  set c : Fin m → (rationalFunctionsPresheaf X).obj (op U) := fun i => coeff m φ U i z with hc
  choose p hp using fun i => IsLocalization.surj (nonZeroDivisors Γ(X, U)) (c i)
  choose ρ hρη hρ using fun i : Fin m =>
    exists_regular_divisorialSection ((i : ℕ) • -D) hU hηU
  have hρne : ∀ i, ρ i ≠ 0 := fun i h0 => by
    have := hρη i
    rwa [h0, Scheme.basicOpen_zero] at this
  let si : Fin m → Γ(X, U) := fun i => (p i).2 * ρ i
  have hsi : ∀ i, si i ≠ 0 := fun i => mul_ne_zero (nonZeroDivisors.coe_ne_zero _) (hρne i)
  let s : Γ(X, U) := ∏ i, si i
  have hs0 : s ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hsi i
  have hmem : ∀ i : Fin m, algebraMap Γ(X, U) _ s * c i ∈
      ((i : ℕ) • -D).divisorialSubmodule U := by
    intro i
    have hs : s = si i * ∏ j ∈ Finset.univ.erase i, si j :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    have key : algebraMap Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)) s * c i =
        ((∏ j ∈ Finset.univ.erase i, si j) * (p i).1) •
          (toRationalFunctionsPresheaf X).app (op U) (ρ i) := by
      have h1 := hp i
      rw [Algebra.smul_def]
      change _ = algebraMap Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)) _ *
        algebraMap Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)) (ρ i)
      rw [hs, map_mul, map_mul, map_mul, ← h1]
      simp only [si, map_mul]
      ring
    rw [key]
    exact Submodule.smul_mem _ _ (hρ i)
  refine ⟨s, mem_nonZeroDivisors_of_ne_zero hs0, ⟨reduce m φ U
    (∑ i : Fin m, Polynomial.monomial (i : ℕ) (algebraMap Γ(X, U) _ s * c i)), ?_⟩, ?_⟩
  · refine (mem_carrier_iff m D hφ).mpr fun n => ?_
    rw [coeff_reduce_sum]
    split_ifs with hn
    · exact hmem ⟨n, hn⟩
    · exact Submodule.zero_mem _
  · refine (ambientEquivPi m φ U).injective (funext fun i => ?_)
    change coeff m φ U i (reduce m φ U
      (∑ j : Fin m, Polynomial.monomial (j : ℕ) (algebraMap Γ(X, U) _ s * c j))) =
      coeff m φ U i (algebraMap Γ(X, U) _ s * z)
    rw [coeff_reduce_sum, dif_pos i.2]
    exact (coeff_structureMap_mul m φ s z i).symm

end CarrierLocalization

section EtaleKummer

open Polynomial

/-- The Kummer algebra `R[X]/(Xᵐ - v)` is étale over `R` when `m` and `v` are units. -/
private theorem algebra_etale_adjoinRoot {R : Type*} [CommRing R] (m : ℕ) [NeZero m]
    (hm : IsUnit (m : R)) (v : R) (hv : IsUnit v) :
    Algebra.Etale R (AdjoinRoot (Polynomial.X ^ m - Polynomial.C v)) := by
  obtain ⟨mu, hmu⟩ := hm
  obtain ⟨vu, hvu⟩ := hv
  have hcond : ∃ p₁ p₂ n, derivative (Polynomial.X ^ m - Polynomial.C v) * p₁ +
      (Polynomial.X ^ m - Polynomial.C v) * p₂ = (1 : R[X]) ^ n := by
    refine ⟨Polynomial.C (((mu⁻¹ : Rˣ) : R) * ((vu⁻¹ : Rˣ) : R)) * Polynomial.X, -Polynomial.C
        (↑vu⁻¹), 0, ?_⟩
    have hm1 : (Polynomial.X : R[X]) ^ (m - 1) * Polynomial.X = Polynomial.X ^ m := by
      rw [← pow_succ, Nat.sub_add_cancel (NeZero.pos m)]
    have h1 : derivative (Polynomial.X ^ m - Polynomial.C v) =
        Polynomial.C (m : R) * Polynomial.X ^ (m - 1) := by
      rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero]
    rw [h1, pow_zero]
    have e1 : Polynomial.C (m : R) * Polynomial.C (((mu⁻¹ : Rˣ) : R) * ((vu⁻¹ : Rˣ) : R)) =
        Polynomial.C (((vu⁻¹ : Rˣ)) : R) := by
      rw [← map_mul, ← hmu, ← mul_assoc, Units.mul_inv, one_mul]
    have e2 : Polynomial.C (((vu⁻¹ : Rˣ)) : R) * Polynomial.C v = 1 := by
      rw [← map_mul, ← hvu, Units.inv_mul, map_one]
    calc Polynomial.C (m : R) * Polynomial.X ^ (m - 1) *
          (Polynomial.C (((mu⁻¹ : Rˣ) : R) * ((vu⁻¹ : Rˣ) : R)) * Polynomial.X) +
        (Polynomial.X ^ m - Polynomial.C v) * -Polynomial.C (((vu⁻¹ : Rˣ)) : R)
        = (Polynomial.C (m : R) * Polynomial.C (((mu⁻¹ : Rˣ) : R) * ((vu⁻¹ : Rˣ) : R))) *
            (Polynomial.X ^ (m - 1) * Polynomial.X)
          - Polynomial.C (((vu⁻¹ : Rˣ)) : R) * Polynomial.X ^ m + Polynomial.C (((vu⁻¹ : Rˣ)) : R) *
              Polynomial.C v := by ring
      _ = 1 := by rw [e1, hm1, e2]; ring
  let P : StandardEtalePair R := ⟨Polynomial.X ^ m - Polynomial.C v,
    monic_X_pow_sub_C v (NeZero.ne m), 1, hcond⟩
  have : IsLocalization (Submonoid.powers (AdjoinRoot.mk P.f P.g))
      (AdjoinRoot (Polynomial.X ^ m - Polynomial.C v)) := by
    refine IsLocalization.of_le_isUnit ?_
    rintro x ⟨n, rfl⟩
    have : AdjoinRoot.mk P.f P.g = 1 := by
      change AdjoinRoot.mk _ 1 = 1
      exact map_one _
    change IsUnit ((AdjoinRoot.mk P.f P.g) ^ n)
    rw [this, one_pow]
    exact isUnit_one
  let e : P.Ring ≃ₐ[R] AdjoinRoot (Polynomial.X ^ m - Polynomial.C v) :=
    P.equivAwayAdjoinRoot.trans ((IsLocalization.algEquiv (Submonoid.powers (AdjoinRoot.mk P.f P.g))
        _ _).restrictScalars R)
  exact Algebra.Etale.of_equiv e

end EtaleKummer

section LocalDVR

open Polynomial

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

private theorem ordGE_zero_iff_range (E : MMP.Mori.PrimeDivisor X)
    (c : X.presheaf.stalk (componentGenericPoint X E.component)) :
    E.OrdGE 0 c ↔ ∃ r : E.localRing, E.toComponent.hom r = c := by
  constructor
  · rintro (rfl | hc)
    · exact ⟨0, map_zero _⟩
    · exact E.exists_toComponent_eq_of_one_le_valuation (by simpa using hc)
  · rintro ⟨r, rfl⟩
    by_cases hr : r = 0
    · exact Or.inl (by rw [hr, map_zero])
    · exact Or.inr (by simpa using E.one_le_valuation_toComponent hr)

private theorem ordGE_unit_mul (E : MMP.Mori.PrimeDivisor X)
    {u c : X.presheaf.stalk (componentGenericPoint X E.component)} {d n : ℤ}
    (hv : E.valuation u = WithZero.exp d) (hc : E.OrdGE n c) : E.OrdGE (n + d) (u * c) := by
  rcases hc with rfl | hc
  · exact Or.inl (mul_zero _)
  · refine Or.inr ?_
    calc WithZero.exp (n + d) = WithZero.exp d * WithZero.exp n := by
          rw [WithZero.exp_add, mul_comm]
      _ ≤ E.valuation u * E.valuation c := by rw [hv]; gcongr
      _ = E.valuation (u * c) := (map_mul _ _ _).symm

private theorem valuation_inv_eq (E : MMP.Mori.PrimeDivisor X)
    {u u' : X.presheaf.stalk (componentGenericPoint X E.component)} (huu : u * u' = 1) {d : ℤ}
    (hv : E.valuation u = WithZero.exp d) : E.valuation u' = WithZero.exp (-d) := by
  have h1 : E.valuation u * E.valuation u' = 1 := by rw [← map_mul, huu, map_one]
  rw [hv] at h1
  have h2 : WithZero.exp d * WithZero.exp (-d) = (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  exact mul_left_cancel₀ (WithZero.exp_ne_zero) (h1.trans h2.symm)

variable [IsIntegral X] [CompactSpace X] (m : ℕ) [NeZero m] {φ : (RationalFunctions X)ˣ}

/-- The basis `1, t, …, tᵐ⁻¹` of the fibre algebra over the function field of a component. -/
private noncomputable def kbasis (Z : irreducibleComponents X) :
    Module.Basis (Fin m) (X.presheaf.stalk (componentGenericPoint X Z)) (Fiber m φ Z) :=
  (AdjoinRoot.powerBasis' (poly_monic m φ Z)).basis.reindex
    (finCongr (by unfold poly; exact natDegree_X_pow_sub_C))

private theorem kbasis_repr (Z : irreducibleComponents X) (x : Fiber m φ Z) (j : Fin m) :
    (kbasis m (φ := φ) Z).repr x j =
      (AdjoinRoot.modByMonicHom (poly_monic m φ Z) x).coeff j := by
  unfold kbasis
  rw [Module.Basis.repr_reindex]
  exact AdjoinRoot.powerBasisAux'_repr_apply_to_fun _ _ _

private theorem kbasis_apply (Z : irreducibleComponents X) (j : Fin m) :
    kbasis m (φ := φ) Z j = AdjoinRoot.root (poly m φ Z) ^ (j : ℕ) := by
  unfold kbasis
  rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

variable (D : Divisor X)

/-- **Local integrality at a prime divisor.** An element `b` of `𝓛(U)` that is integral over
`𝒜(U)` has its `tⁿ`-coefficient of order `≥ n · d_E` along every prime divisor `E` meeting `U`
(here `d_E` is the coefficient of `E` in `D`), when `div φ + mD = 0` and `m` is invertible. -/
private theorem ordGE_coeff_of_integral
    (hm : ∀ x : X, IsUnit (m : X.presheaf.stalk x))
    (h : principalDivisor φ + m • D = 0) {U : X.Opens} (E : MMP.Mori.PrimeDivisor X)
    (hEU : (E.support ∩ U).Nonempty)
    (b : (ambient m φ).obj (op U)) (p : ((ambient m φ).obj (op U))[X]) (hp : p.Monic)
    (hpc : ∀ i, p.coeff i ∈ carrier m D U) (hb : p.eval b = 0) (n : Fin m) :
    E.OrdGE (n * D.coeff E)
      (coeff m φ U n b ⟨E.component, E.componentGenericPoint_mem_of_nonempty hEU⟩) := by
  classical
  have hφ : 0 ≤ principalDivisor φ + m • D := h.ge
  set Z := E.component with hZ
  set zi : {Z' : irreducibleComponents X // componentGenericPoint X Z' ∈ U} :=
    ⟨Z, E.componentGenericPoint_mem_of_nonempty hEU⟩ with hzi
  let ev : (ambient m φ).obj (op U) →+* Fiber m φ Z := Pi.evalRingHom
    (fun Z' : {Z' : irreducibleComponents X // componentGenericPoint X Z' ∈ U} =>
      Fiber m φ Z'.1) zi
  letI : Field (X.presheaf.stalk (componentGenericPoint X Z)) :=
    (RationalFunctions.isField_stalk X Z).toField
  letI : Algebra E.localRing (X.presheaf.stalk (componentGenericPoint X Z)) :=
    E.toComponent.hom.toAlgebra
  haveI : IsFractionRing E.localRing (X.presheaf.stalk (componentGenericPoint X Z)) :=
    isFractionRing_stalkToRationalFunctions E.genericPoint_mem_component
  haveI := E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := MMP.Positivity.PrimeDivisor.exists_ord_eq_one E
  set g : (RationalFunctions X)ˣ := ϖ ^ (D.coeff E) with hg
  have hgord : E.ord g = D.coeff E := by rw [hg, E.ord_zpow, hϖ]; simp
  set g0 : X.presheaf.stalk (componentGenericPoint X Z) := (g : RationalFunctions X) Z with hg0def
  have hg0v : E.valuation g0 = WithZero.exp (D.coeff E) := by
    have := E.valuation_component g
    rwa [hgord] at this
  have hg0 : g0 ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hg0v
    exact WithZero.exp_ne_zero hg0v.symm
  set φ0 : X.presheaf.stalk (componentGenericPoint X Z) := (φ : RationalFunctions X) Z with hφ0
  have hφ0v : E.valuation φ0 = WithZero.exp (E.ord φ) := E.valuation_component φ
  have hE0 : E.ord φ + (m : ℤ) * D.coeff E = 0 := by
    have := congrArg (fun D' : Divisor X => D'.coeff E) h
    simpa [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, coeff_principalDivisor]
      using this
  have hu0v : E.valuation (g0 ^ m * φ0) = 1 := by
    rw [map_mul, map_pow, hg0v, hφ0v, ← WithZero.exp_nsmul, ← WithZero.exp_add]
    simp only [nsmul_eq_mul]
    rw [add_comm, hE0, WithZero.exp_zero]
  have hu0 : g0 ^ m * φ0 ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hu0v
    exact zero_ne_one hu0v
  obtain ⟨v, hv⟩ := E.exists_toComponent_eq_of_one_le_valuation (f := g0 ^ m * φ0) hu0v.ge
  obtain ⟨v', hv'⟩ := E.exists_toComponent_eq_of_one_le_valuation (f := (g0 ^ m * φ0)⁻¹)
    (by rw [map_inv₀, hu0v]; simp)
  have hvunit : IsUnit v := by
    refine IsUnit.of_mul_eq_one v' (a := v) (IsFractionRing.injective E.localRing
      (X.presheaf.stalk (componentGenericPoint X Z)) ?_)
    change E.toComponent.hom (v * v') = E.toComponent.hom 1
    rw [map_mul, hv, hv', map_one]
    exact mul_inv_cancel₀ hu0
  have hmunit : IsUnit (m : E.localRing) := hm E.genericPoint
  let w : Fiber m φ Z := algebraMap _ (Fiber m φ Z) g0 * AdjoinRoot.root (poly m φ Z)
  have hw : w ^ m = algebraMap E.localRing (Fiber m φ Z) v := by
    have h1 : algebraMap E.localRing (X.presheaf.stalk (componentGenericPoint X Z)) v =
        g0 ^ m * φ0 := hv
    rw [IsScalarTower.algebraMap_apply E.localRing (X.presheaf.stalk (componentGenericPoint X Z))
      (Fiber m φ Z), h1, mul_pow, root_pow_m, map_mul, map_pow]
    rfl
  let gU : (X.presheaf.stalk (componentGenericPoint X Z))ˣ := Units.mk0 g0 hg0
  let B := (kbasis m (φ := φ) Z).unitsSMul (fun i => gU ^ (i : ℕ))
  have hB : ∀ i, B i = w ^ (i : ℕ) := fun i => by
    rw [Module.Basis.unitsSMul_apply, kbasis_apply, Units.smul_def, Algebra.smul_def, mul_pow,
      Units.val_pow_eq_pow_val, map_pow]
    rfl
  have hwI : IsIntegral E.localRing w := by
    refine ⟨Polynomial.X ^ m - Polynomial.C v, monic_X_pow_sub_C v (NeZero.ne m), ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hw, sub_self]
  have hBrepr : ∀ (x : Fiber m φ Z) (j : Fin m), B.repr x j =
      (g0 ^ (j : ℕ))⁻¹ * (kbasis m (φ := φ) Z).repr x j := by
    intro x j
    have := congrArg (fun f => f x) (Module.Basis.coord_unitsSMul (kbasis m (φ := φ) Z)
      (fun i => gU ^ (i : ℕ)) j)
    simp only [Module.Basis.coord_apply, LinearMap.smul_apply] at this
    refine this.trans ?_
    rw [Units.smul_def, smul_eq_mul]
    simp [gU]
  have hkrepr : ∀ (a : (ambient m φ).obj (op U)) (j : Fin m),
      (kbasis m (φ := φ) Z).repr (ev a) j = coeff m φ U j a zi := fun a j => by
    rw [kbasis_repr]; rfl
  have hord : ∀ a ∈ carrier m D U, ∀ j : Fin m,
      E.OrdGE (j * D.coeff E) (coeff m φ U j a zi) := fun a ha j => by
    have hmem := (mem_carrier_iff m D hφ).mp ha j
    have := hmem E hEU
    have e1 : -(((j : ℕ) • -D).coeff E) = (j : ℤ) * D.coeff E := by
      simp [DivisorWithCoeffs.coeff_smul]
    rwa [e1] at this
  have hg0pow : ∀ j : ℕ, E.valuation (g0 ^ j) = WithZero.exp ((j : ℤ) * D.coeff E) := fun j => by
    rw [map_pow, hg0v, ← WithZero.exp_nsmul]
    simp
  have hg0inv : ∀ j : ℕ, E.valuation ((g0 ^ j)⁻¹) = WithZero.exp (-((j : ℤ) * D.coeff E)) :=
    fun j => valuation_inv_eq E (mul_inv_cancel₀ (pow_ne_zero j hg0)) (hg0pow j)
  have hcoord : ∀ a ∈ carrier m D U, ∀ j : Fin m,
      ∃ r : E.localRing, B.repr (ev a) j = algebraMap E.localRing _ r := fun a ha j => by
    have h1 := ordGE_unit_mul E (hg0inv j) (hord a ha j)
    rw [add_neg_cancel, ordGE_zero_iff_range] at h1
    obtain ⟨r, hr⟩ := h1
    exact ⟨r, by rw [hBrepr, hkrepr]; exact hr.symm⟩
  have hI : ∀ a ∈ carrier m D U, IsIntegral E.localRing (ev a) := fun a ha => by
    choose r hr using hcoord a ha
    rw [← B.sum_repr (ev a)]
    refine IsIntegral.sum _ fun j _ => ?_
    rw [hr j, hB, algebraMap_smul _, Algebra.smul_def]
    exact isIntegral_algebraMap.mul (hwI.pow _)
  have hbI : IsIntegral E.localRing (ev b) := by
    set q : (Fiber m φ Z)[X] := p.map ev with hq
    have hqm : q.Monic := hp.map ev
    have hqe : q.eval (ev b) = 0 := by
      rw [hq, Polynomial.eval_map]
      have := Polynomial.hom_eval₂ p (RingHom.id _) ev b
      rw [RingHom.comp_id] at this
      rw [← this]
      change ev (p.eval b) = 0
      rw [hb, map_zero]
    by_cases hdeg : q.natDegree = 0
    · have h1 : q = 1 := (Polynomial.Monic.natDegree_eq_zero hqm).mp hdeg
      rw [h1, Polynomial.eval_one] at hqe
      have : ev b = 0 := (subsingleton_of_zero_eq_one hqe.symm).elim _ _
      rw [this]
      exact isIntegral_zero
    · refine IsIntegral.of_aeval_monic_of_isIntegral_coeff hqm hdeg (by rw [hqe]; exact
        isIntegral_zero) fun i => ?_
      rw [hq, Polynomial.coeff_map]
      exact hI _ (hpc i)
  obtain ⟨r, hr⟩ := KummerBasis.coords_mem m hmunit v hvunit w hw B hB (ev b) hbI n
  have h3 : (kbasis m (φ := φ) Z).repr (ev b) n = g0 ^ (n : ℕ) * algebraMap E.localRing _ r := by
    rw [← hr, hBrepr, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hg0), one_mul]
  rw [hkrepr] at h3
  have h4 : E.OrdGE 0 (algebraMap E.localRing (X.presheaf.stalk (componentGenericPoint X Z)) r) :=
    (ordGE_zero_iff_range E _).mpr ⟨r, rfl⟩
  have h5 := ordGE_unit_mul E (hg0pow n) h4
  rw [zero_add, ← h3] at h5
  exact h5

end LocalDVR

section Normality

open Polynomial

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (m : ℕ) [NeZero m] (D : Divisor X) {φ : (RationalFunctions X)ˣ}

/-- `𝒜(U)` is a subalgebra of `𝓛(U)`. -/
private noncomputable instance carrierAlgebra (U : X.Opens) :
    Algebra ↥(carrier (φ := φ) m D U) ((ambient m φ).obj (op U)) :=
  (carrier (φ := φ) m D U).subtype.toAlgebra

/-- `𝒜(U)` is integrally closed in `𝓛(U)`. -/
private theorem mem_carrier_of_integral (hm : ∀ x : X, IsUnit (m : X.presheaf.stalk x))
    (h : principalDivisor φ + m • D = 0) {U : X.Opens} (b : (ambient m φ).obj (op U))
    (p : ((ambient m φ).obj (op U))[X]) (hp : p.Monic) (hpc : ∀ i, p.coeff i ∈ carrier m D U)
    (hb : p.eval b = 0) : b ∈ carrier m D U := by
  rw [mem_carrier_iff m D h.ge]
  intro n
  by_cases hn : n < m
  · intro E hEU
    have := ordGE_coeff_of_integral m D hm h E hEU b p hp hpc hb ⟨n, hn⟩
    have e1 : -(((n : ℕ) • -D).coeff E) = (((⟨n, hn⟩ : Fin m) : ℕ) : ℤ) * D.coeff E := by
      simp [DivisorWithCoeffs.coeff_smul]
    rw [e1]
    exact this
  · rw [coeff_eq_zero_of_le m φ b (not_lt.mp hn)]
    exact zero_mem _

private theorem isIntegrallyClosedIn_carrier (hm : ∀ x : X, IsUnit (m : X.presheaf.stalk x))
    (h : principalDivisor φ + m • D = 0) (U : X.Opens) :
    IsIntegrallyClosedIn ↥(carrier (φ := φ) m D U) ((ambient m φ).obj (op U)) := by
  refine (isIntegrallyClosedIn_iff (R := carrier (φ := φ) m D U) (A := (ambient m φ).obj (op
      U))).mpr
    ⟨Subtype.val_injective, fun {b} hb => ?_⟩
  obtain ⟨p, hp, hpe⟩ := hb
  have hb' : b ∈ carrier m D U := by
    refine mem_carrier_of_integral m D hm h b (p.map (algebraMap (carrier (φ := φ) m D U) _))
        (hp.map _)
      (fun i => ?_) (by rw [Polynomial.eval_map]; exact hpe)
    rw [Polynomial.coeff_map]
    exact (p.coeff i).2
  exact ⟨⟨b, hb'⟩, rfl⟩

/-- `𝓛(U)` is an Artinian ring. -/
private theorem isArtinianRing_ambient (U : X.Opens) :
    IsArtinianRing ((ambient m φ).obj (op U)) := by
  have : ∀ Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U},
      IsArtinianRing (Fiber m φ Z.1) := fun Z => by
    letI : Field (X.presheaf.stalk (componentGenericPoint X Z.1)) :=
      (RationalFunctions.isField_stalk X Z.1).toField
    have : Module.Finite (X.presheaf.stalk (componentGenericPoint X Z.1)) (Fiber m φ Z.1) :=
      (poly_monic m φ Z.1).finite_adjoinRoot
    exact IsArtinianRing.of_finite (X.presheaf.stalk (componentGenericPoint X Z.1)) _
  have : Finite {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U} := by
    have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
    have : Finite (irreducibleComponents X) :=
      (NoetherianSpace.finite_irreducibleComponents (α := X)).to_subtype
    infer_instance
  exact (inferInstance : IsArtinianRing (∀ Z : {Z : irreducibleComponents X //
    componentGenericPoint X Z ∈ U}, Fiber m φ Z.1))

/-- `𝓛(U)` is a reduced ring. -/
private theorem isReduced_ambient (hm : ∀ x : X, IsUnit (m : X.presheaf.stalk x))
    (U : X.Opens) : IsReduced ((ambient m φ).obj (op U)) := by
  have : ∀ Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U},
      IsReduced (Fiber m φ Z.1) := fun Z => by
    letI : Field (X.presheaf.stalk (componentGenericPoint X Z.1)) :=
      (RationalFunctions.isField_stalk X Z.1).toField
    have hv : IsUnit ((φ : RationalFunctions X) Z.1) := φ.isUnit.map (Pi.evalRingHom _ Z.1)
    haveI : Algebra.Etale (X.presheaf.stalk (componentGenericPoint X Z.1)) (Fiber m φ Z.1) :=
      algebra_etale_adjoinRoot m (hm _) _ hv
    exact Algebra.FormallyUnramified.isReduced_of_field
      (X.presheaf.stalk (componentGenericPoint X Z.1)) (Fiber m φ Z.1)
  exact (inferInstance : IsReduced (∀ Z : {Z : irreducibleComponents X //
    componentGenericPoint X Z ∈ U}, Fiber m φ Z.1))

/-- `𝓛(U)` is the total ring of fractions of `𝒜(U)`. -/
private theorem isLocalization_carrier (h : principalDivisor φ + m • D = 0) {U : X.Opens}
    (hU : IsAffineOpen U) (hηU : genericPoint X ∈ U) :
    IsLocalization (nonZeroDivisors ↥(carrier (φ := φ) m D U)) ((ambient m φ).obj (op U)) := by
  have hφ : 0 ≤ principalDivisor φ + m • D := h.ge
  have : IsArtinianRing ((ambient m φ).obj (op U)) := isArtinianRing_ambient m U
  have hFR : IsFractionRing Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)) :=
    isFractionRing_rationalFunctions hU hηU
  have hρ : ∀ ρ ∈ nonZeroDivisors Γ(X, U), IsUnit (algebraMap Γ(X, U) ((ambient m φ).obj (op U))
      ρ) := by
    intro ρ hρ
    rw [IsScalarTower.algebraMap_apply Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U))
      ((ambient m φ).obj (op U))]
    exact (IsLocalization.map_units ((rationalFunctionsPresheaf X).obj (op U)) ⟨ρ, hρ⟩).map _
  refine ⟨fun s => ?_, fun z => ?_, fun {x y} hxy => ⟨1, ?_⟩⟩
  · have hnz : ((s : ↥(carrier (φ := φ) m D U)) : (ambient m φ).obj (op U)) ∈
        nonZeroDivisors ((ambient m φ).obj (op U)) := by
      rw [mem_nonZeroDivisors_iff_left]
      intro z hz
      obtain ⟨ρ, hρn, a, ha⟩ : ∃ (ρ : Γ(X, U)) (_ : ρ ∈ nonZeroDivisors Γ(X, U))
        (a : ↥(carrier (φ := φ) m D U)), a.1 = algebraMap Γ(X, U) ((ambient m φ).obj (op U)) ρ *
            z :=
      exists_smul_mem_carrier m D hφ hU hηU z
      have h1 : (s : ↥(carrier (φ := φ) m D U)) * a = 0 := by
        apply Subtype.ext
        change ((s : ↥(carrier (φ := φ) m D U)) : (ambient m φ).obj (op U)) * a.1 = 0
        rw [ha, mul_left_comm, hz, mul_zero]
      have h2 : a = 0 := (mem_nonZeroDivisors_iff_left.mp s.2) a h1
      have h3 : algebraMap Γ(X, U) ((ambient m φ).obj (op U)) ρ * z = 0 := by
        rw [← ha, h2]; rfl
      exact (hρ ρ hρn).mul_right_eq_zero.mp h3
    exact IsArtinianRing.isUnit_of_mem_nonZeroDivisors hnz
  · obtain ⟨ρ, hρn, a, ha⟩ : ∃ (ρ : Γ(X, U)) (_ : ρ ∈ nonZeroDivisors Γ(X, U))
        (a : ↥(carrier (φ := φ) m D U)), a.1 = algebraMap Γ(X, U) ((ambient m φ).obj (op U)) ρ *
            z :=
      exists_smul_mem_carrier m D hφ hU hηU z
    let ρS : ↥(carrier (φ := φ) m D U) := (localSubalgebra m D hφ).algebraMap U ρ
    have hρS : ρS ∈ nonZeroDivisors ↥(carrier (φ := φ) m D U) := by
      rw [mem_nonZeroDivisors_iff_left]
      intro y hy
      have h3 : algebraMap Γ(X, U) ((ambient m φ).obj (op U)) ρ * y.1 = 0 := by
        have := congrArg Subtype.val hy
        change (ρS : (ambient m φ).obj (op U)) * y.1 = 0 at this
        rwa [show (ρS : (ambient m φ).obj (op U)) = algebraMap Γ(X, U) ((ambient m φ).obj (op U)) ρ
          from LocalSubalgebra.coe_algebraMap (localSubalgebra m D hφ) U ρ] at this
      exact Subtype.ext ((hρ ρ hρn).mul_right_eq_zero.mp h3)
    refine ⟨(a, ⟨_, hρS⟩), ?_⟩
    change z * (ρS : (ambient m φ).obj (op U)) = a.1
    rw [show (ρS : (ambient m φ).obj (op U)) = algebraMap Γ(X, U) ((ambient m φ).obj (op U)) ρ
      from LocalSubalgebra.coe_algebraMap (localSubalgebra m D hφ) U ρ, ha, mul_comm]
  · have := Subtype.ext hxy
    rw [this]

/-- `𝒜(U)` is a finite `Γ(X, U)`-module, for `U` affine. -/
private theorem finite_algebraMap_carrier {U : X.Opens} (hU : IsAffineOpen U)
    (hφ : 0 ≤ principalDivisor φ + m • D) :
    ((localSubalgebra m D hφ).algebraMap U).Finite := by
  letI := (localSubalgebra m D hφ).moduleSections U
  have : ∀ i : Fin m, Module.Finite Γ(X, U) Γ((((i : ℕ) • -D)).divisorialSheaf, U) :=
    fun i => finite_divisorialSubmodule _ hU
  exact Module.Finite.equiv (coeffLinearEquiv m D hφ U).symm

/-- **`𝒜(U)` is a normal ring.** -/
private theorem isNormalRing_carrier (hm : ∀ x : X, IsUnit (m : X.presheaf.stalk x))
    (h : principalDivisor φ + m • D = 0) {U : X.Opens} (hU : IsAffineOpen U)
    (hηU : genericPoint X ∈ U) : IsNormalRing ↥(carrier (φ := φ) m D U) := by
  have hφ : 0 ≤ principalDivisor φ + m • D := h.ge
  haveI := isLocalization_carrier m D h hU hηU
  haveI : IsIntegrallyClosed ↥(carrier (φ := φ) m D U) :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn ((ambient m φ).obj (op U))).mpr
      (isIntegrallyClosedIn_carrier m D hm h U)
  haveI : IsReduced ((ambient m φ).obj (op U)) := isReduced_ambient m hm U
  haveI : IsReduced ↥(carrier (φ := φ) m D U) :=
    isReduced_of_injective (carrier (φ := φ) m D U).subtype Subtype.val_injective
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hfin : (minimalPrimes ↥(carrier (φ := φ) m D U)).Finite := by
    letI : Algebra Γ(X, U) ↥(carrier (φ := φ) m D U) :=
      ((localSubalgebra m D hφ).algebraMap U).toAlgebra
    haveI : Module.Finite Γ(X, U) ↥(carrier (φ := φ) m D U) := finite_algebraMap_carrier m D hU hφ
    haveI : IsNoetherian Γ(X, U) ↥(carrier (φ := φ) m D U) :=
      isNoetherian_of_isNoetherianRing_of_finite Γ(X, U) _
    haveI : IsNoetherianRing ↥(carrier (φ := φ) m D U) :=
      isNoetherian_of_tower Γ(X, U) inferInstance
    exact minimalPrimes.finite_of_isNoetherianRing _
  have hic : IsIntegrallyClosed ↥(carrier (φ := φ) m D U) := inferInstance
  exact ((isIntegrallyClosed_tfae_of_finite_minimalPrimes hfin).out 2 1).mp hic

end Normality

section Chart

open CategoryTheory.Limits

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (m : ℕ) [NeZero m] (D : Divisor X) {φ : (RationalFunctions X)ˣ}
  (hφ : 0 ≤ principalDivisor φ + m • D)

/-- `𝒜(U) ≃ Γ(X', p⁻¹U)` over an affine open `U`. -/
private noncomputable def psiEquiv {U : X.Opens} (hU : IsAffineOpen U) :
    (localSubalgebra m D hφ).carrier U ≃+*
      Γ(cover m D hφ, toBase m D hφ ⁻¹ᵁ U) :=
  RingEquiv.ofBijective
    ((Stacks.RelativeSpec.universalAlgebraMap (situation m D hφ)).right.app (op U)).hom (by
      have := Stacks.RelativeSpec.isIso_universalAlgebraMap_app (situation m D hφ) ⟨U, hU⟩
      exact ConcreteCategory.bijective_of_isIso _)

private theorem psiEquiv_algebraMap {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U)) :
    psiEquiv m D hφ hU ((localSubalgebra m D hφ).algebraMap U r) =
      ((toBase m D hφ).appLE U (toBase m D hφ ⁻¹ᵁ U) le_rfl).hom r := by
  rw [Scheme.Hom.appLE_eq_app]
  rw [Stacks.RelativeSpec.toBase_app]
  rfl

private theorem isIso_appLE_of_image_eq {A B : Scheme.{u}} (f : A ⟶ B) [IsOpenImmersion f]
    (U : B.Opens) (V : A.Opens) (hVU : V ≤ f ⁻¹ᵁ U) (h : f ''ᵁ V = U) :
    IsIso (f.appLE U V hVU) := by
  subst h
  have := f.appIso_hom' V
  rw [← this]
  infer_instance

private theorem fst_image_top {X' X T : Scheme.{u}} (p : X' ⟶ X) (g : T ⟶ X)
    [IsOpenImmersion g] : (pullback.fst p g) ''ᵁ ⊤ = p ⁻¹ᵁ (g ''ᵁ ⊤) := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.image_top_eq_opensRange]
  apply SetLike.ext'
  rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_fst]
  rfl

private theorem compat_appLE {X' X T : Scheme.{u}} (p : X' ⟶ X) (g : T ⟶ X)
    (U : X.Opens) (h1 : ⊤ ≤ g ⁻¹ᵁ U) (h2 : ⊤ ≤ (pullback.fst p g) ⁻¹ᵁ (p ⁻¹ᵁ U)) :
    p.appLE U (p ⁻¹ᵁ U) le_rfl ≫ (pullback.fst p g).appLE (p ⁻¹ᵁ U) ⊤ h2 =
      g.appLE U ⊤ h1 ≫ (pullback.snd p g).appLE ⊤ ⊤ le_rfl := by
  have mid : ∀ (f f' : pullback p g ⟶ X) (hf : f = f') (e : ⊤ ≤ f ⁻¹ᵁ U) (e' : ⊤ ≤ f' ⁻¹ᵁ U),
      f.appLE U ⊤ e = f'.appLE U ⊤ e' := by
    rintro f _ rfl e e'
    rfl
  exact (Scheme.Hom.appLE_comp_appLE (pullback.fst p g) p U (p ⁻¹ᵁ U) ⊤ le_rfl h2).trans
    ((mid _ _ pullback.condition _ _).trans
      (Scheme.Hom.appLE_comp_appLE (pullback.snd p g) g U ⊤ ⊤ h1 le_rfl).symm)

include hφ in
/-- The rank of the cyclic cover at the generic point, computed over an affine chart. -/
private theorem finrank_pullback_snd_chart {T : Scheme.{u}} (g : T ⟶ X) [IsOpenImmersion g]
    [IsAffine T] (t : T) (ht : g t = genericPoint X) :
    (pullback.snd (toBase m D hφ) g).appTop.hom.finrank (T.isoSpec.hom t) = m := by
  set p := toBase m D hφ with hp
  set U : X.Opens := g ''ᵁ ⊤ with hUdef
  have hU : IsAffineOpen U := by
    rw [hUdef, Scheme.Hom.image_top_eq_opensRange]
    exact isAffineOpen_opensRange g
  have hηU : genericPoint X ∈ U := ⟨t, trivial, ht⟩
  have h1 : ⊤ ≤ g ⁻¹ᵁ U := fun x _ => ⟨x, trivial, rfl⟩
  have h2 : ⊤ ≤ (pullback.fst p g) ⁻¹ᵁ (p ⁻¹ᵁ U) := by
    rw [← fst_image_top p g]
    exact fun x _ => ⟨x, trivial, rfl⟩
  have i1 : IsIso (g.appLE U ⊤ h1) := isIso_appLE_of_image_eq g U ⊤ h1 rfl
  have i2 : IsIso ((pullback.fst p g).appLE (p ⁻¹ᵁ U) ⊤ h2) :=
    isIso_appLE_of_image_eq _ _ _ h2 (fst_image_top p g)
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have : IsDomain Γ(X, U) := IsIntegral.component_integral U
  have hFR : IsFractionRing Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)) :=
    isFractionRing_rationalFunctions hU hηU
  let ε : Γ(X, U) ≃+* Γ(T, ⊤) :=
    RingEquiv.ofBijective (g.appLE U ⊤ h1).hom (ConcreteCategory.bijective_of_isIso _)
  let Θ : Γ(cover m D hφ, p ⁻¹ᵁ U) ≃+* Γ(pullback p g, ⊤) :=
    RingEquiv.ofBijective ((pullback.fst p g).appLE (p ⁻¹ᵁ U) ⊤ h2).hom
      (ConcreteCategory.bijective_of_isIso _)
  let Φ := (psiEquiv m D hφ hU).trans Θ
  have hΦ : ∀ r : Γ(X, U), Φ ((localSubalgebra m D hφ).algebraMap U r) =
      (pullback.snd p g).appTop.hom (ε r) := by
    intro r
    have h3 : (pullback.snd p g).appLE ⊤ ⊤ le_rfl = (pullback.snd p g).appTop :=
      Scheme.Hom.appLE_eq_app _
    rw [← h3]
    change Θ (psiEquiv m D hφ hU _) = _
    rw [psiEquiv_algebraMap m D hφ hU r]
    have := congrArg (fun f => f.hom r) (compat_appLE p g U h1 h2)
    exact this
  have : Nontrivial Γ(T, ⊤) := ε.toEquiv.symm.nontrivial
  have hD : IsDomain Γ(T, ⊤) := Function.Injective.isDomain ε.symm.toRingHom ε.symm.injective
  have hq : T.isoSpec.hom t = ⟨⊥, Ideal.isPrime_bot⟩ := by
    have hcl : closure ({t} : Set T) = Set.univ := by
      rw [g.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton, ht,
        (genericPoint_spec X).def]
      rfl
    have hs : Function.Surjective T.isoSpec.hom := fun y =>
      ⟨T.isoSpec.inv y, by rw [← Scheme.Hom.comp_apply]; simp⟩
    have hgen : closure ({T.isoSpec.hom t} : Set (Spec Γ(T, ⊤))) = Set.univ := by
      have h := (show IsGenericPoint t Set.univ from hcl).image T.isoSpec.hom.continuous
      rw [Set.image_univ, Set.range_eq_univ.mpr hs, closure_univ] at h
      exact h
    have hmem : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Γ(T, ⊤)) ∈
        closure {T.isoSpec.hom t} := by
      rw [hgen]; trivial
    exact PrimeSpectrum.ext (le_bot_iff.mp ((PrimeSpectrum.le_iff_mem_closure _ _).mpr hmem))
  rw [hq]
  letI : Algebra Γ(X, U) ((localSubalgebra m D hφ).carrier U) :=
    ((localSubalgebra m D hφ).algebraMap U).toAlgebra
  letI : Algebra Γ(T, ⊤) Γ(pullback p g, ⊤) := (pullback.snd p g).appTop.hom.toAlgebra
  have := rankAtStalk_bot_twist (R := Γ(X, U)) (R0 := Γ(T, ⊤))
    (A := (localSubalgebra m D hφ).carrier U) (S := Γ(pullback p g, ⊤))
    (E := (ambient m φ).obj (op U)) (K := (rationalFunctionsPresheaf X).obj (op U))
    (Subring.subtype _) Subtype.val_injective (fun r => rfl)
    (fun z => by
      obtain ⟨s, hs, a, ha⟩ := exists_smul_mem_carrier m D hφ hU hηU z
      exact ⟨s, hs, a, ha⟩) ε Φ hΦ
  rw [finrank_ambient m φ hU hηU] at this
  exact this

end Chart

private theorem exists_smul_eq_smul_of_isFractionRing {R F : Type*} [CommRing R] [IsDomain R]
    [CommRing F]
    [Algebra R F] [IsFractionRing R F] (a n : F) (ha : a ≠ 0) :
    ∃ α β : R, α ≠ 0 ∧ α • n = β • a := by
  have : IsDomain F := IsFractionRing.isDomain R (K := F)
  obtain ⟨⟨x1, s1⟩, h1⟩ := IsLocalization.surj (nonZeroDivisors R) n
  obtain ⟨⟨x2, s2⟩, h2⟩ := IsLocalization.surj (nonZeroDivisors R) a
  simp only [Algebra.smul_def] at *
  have hx2 : x2 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · exact ha h
    · exact (nonZeroDivisors.ne_zero s2.2) ((FaithfulSMul.algebraMap_injective R F)
        (by simpa using h))
  refine ⟨x2 * s1, x1 * s2, mul_ne_zero hx2 (nonZeroDivisors.ne_zero s1.2), ?_⟩
  simp only [Algebra.smul_def, map_mul]
  calc algebraMap R F x2 * algebraMap R F s1 * n
        = algebraMap R F x2 * (n * algebraMap R F s1) := by ring
    _ = algebraMap R F x2 * algebraMap R F x1 := by rw [h1]
    _ = algebraMap R F x1 * (a * algebraMap R F s2) := by rw [h2]; ring
    _ = _ := by ring

private theorem rank_one_identity {R F : Type*} [CommRing R] [IsDomain R] [CommRing F] [Algebra R F]
    [IsFractionRing R F] (N : Submodule R F) (φ : N →ₗ[R] R) (a n : N) :
    φ a • (n : F) = φ n • (a : F) := by
  have : IsDomain F := IsFractionRing.isDomain R (K := F)
  by_cases ha : (a : F) = 0
  · have : a = 0 := Subtype.ext ha
    subst this
    simp
  obtain ⟨α, β, hα, h⟩ := exists_smul_eq_smul_of_isFractionRing (R := R) (a : F) (n : F) ha
  have h1 : (α • n : N) = β • a := Subtype.ext h
  have h2 : α • φ n = β • φ a := by
    rw [← map_smul, ← map_smul, h1]
  have hα0 : algebraMap R F α ≠ 0 := fun h0 =>
    hα ((FaithfulSMul.algebraMap_injective R F) (by simpa using h0))
  have key : algebraMap R F α * (φ a • (n : F)) = algebraMap R F α * (φ n • (a : F)) := by
    simp only [Algebra.smul_def] at h h2 ⊢
    calc _ = algebraMap R F (φ a) * (algebraMap R F α * n) := by ring
      _ = algebraMap R F (φ a) * (algebraMap R F β * a) := by rw [h]
      _ = algebraMap R F (β * φ a) * a := by rw [map_mul]; ring
      _ = algebraMap R F (α * φ n) * a := by
          simp only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] at h2
          rw [h2]
      _ = _ := by rw [map_mul]; ring
  exact mul_left_cancel₀ hα0 key

private theorem exists_principal_of_flat {R F : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing
    R]
    [CommRing F] [Algebra R F] [IsFractionRing R F] (N : Submodule R F) [Module.Finite R N]
    [Module.Flat R N] (hN : N ≠ ⊥) (p : Ideal R) [p.IsPrime] :
    ∃ a ∈ N, a ≠ 0 ∧ ∃ c : R, c ∉ p ∧ ∀ n ∈ N, ∃ r : R, c • n = r • a := by
  have : IsDomain F := IsFractionRing.isDomain R (K := F)
  have : Module.FinitePresentation R N := Module.finitePresentation_of_finite R N
  have : Module.Projective R N := Module.Flat.projective_of_finitePresentation
  obtain ⟨k, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R N
  obtain ⟨n0, hn0, hn0'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  let a : Fin k → N := fun i => f (Pi.single i 1)
  let φ : Fin k → (N →ₗ[R] R) := fun i => (LinearMap.proj i).comp g
  have hsum : ∀ n : N, ∑ i, φ i n • a i = n := by
    intro n
    have := congrArg (fun l => l n) hfg
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    conv_rhs => rw [← this]
    conv_lhs => rw [show ∑ i, φ i n • a i = f (∑ i, φ i n • Pi.single i (1 : R)) by
      simp [a, map_sum]]
    congr 1
    ext j
    simp [φ, Pi.single_apply]
  have hn0N : ((⟨n0, hn0⟩ : N) : F) = n0 := rfl
  have hone : ∑ i, φ i (a i) = 1 := by
    have h1 : (∑ i, φ i (a i)) • n0 = n0 := by
      rw [Finset.sum_smul]
      have := congrArg (fun z : N => (z : F)) (hsum ⟨n0, hn0⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      calc ∑ i, φ i (a i) • n0 = ∑ i, φ i (a i) • ((⟨n0, hn0⟩ : N) : F) := rfl
        _ = ∑ i, φ i ⟨n0, hn0⟩ • (a i : F) :=
          Finset.sum_congr rfl fun i _ => rank_one_identity N (φ i) (a i) ⟨n0, hn0⟩
        _ = n0 := this
    have h2 : ((∑ i, φ i (a i)) - 1) • n0 = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hn0'
  have hex : ∃ i, φ i (a i) ∉ p := by
    by_contra hall
    push Not at hall
    have : (1 : R) ∈ p := hone ▸ Ideal.sum_mem _ fun i _ => hall i
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).mpr this)
  obtain ⟨i, hi⟩ := hex
  refine ⟨(a i : F), (a i).2, fun h0 => hi ?_, φ i (a i), hi, fun n hn => ⟨φ i ⟨n, hn⟩, ?_⟩⟩
  · have : a i = 0 := Subtype.ext h0
    rw [this, map_zero]; exact p.zero_mem
  · exact rank_one_identity N (φ i) (a i) ⟨n, hn⟩

section FlatCartier

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- On an affine open `W`, a prime divisor `E` through `W` has a section of `𝒪_X(D')(W)` whose
order along `E` is exactly `-D'_E`. -/
private theorem exists_mem_divisorialSubmodule_valuation_eq (D' : Divisor X) {W : X.Opens}
    (hW : IsAffineOpen W) (E : MMP.Mori.PrimeDivisor X) (hE : E.genericPoint ∈ W) :
    ∃ s ∈ D'.divisorialSubmodule W,
      E.valuation (s ⟨E.component, E.specializes_genericPoint.mem_open W.isOpen hE⟩) =
        WithZero.exp (-D'.coeff E) := by
  classical
  obtain ⟨U, hU, t, ht, hts⟩ := MMP.Flips.exists_divisorialSection_ord_eq D' E
  have hEU := E.genericPoint_mem_of_nonempty hU
  obtain ⟨b, hbV, hEb⟩ := hW.exists_basicOpen_le (V := U ⊓ W) ⟨E.genericPoint, hEU, hE⟩ hE
  set S : Set (MMP.Mori.PrimeDivisor X) := {P | D'.coeff P ≠ 0 ∨ P.ord t ≠ 0} with hSdef
  have hS : S.Finite := by
    refine ((D'.support.finite_toSet).union (MMP.Mori.finite_ord_ne_zero t)).subset ?_
    rintro P (h | h)
    · exact Or.inl (Finsupp.mem_support_iff.mpr h)
    · exact Or.inr h
  let M : ℕ := hS.toFinset.sup fun P => (-D'.coeff P - P.ord t).toNat
  let T : ToType ((rationalFunctionsPresheaf X).obj (op W)) := fun Z => (t : RationalFunctions X)
      Z.1
  have hgerm : ∀ (P : MMP.Mori.PrimeDivisor X) (hPg : P.genericPoint ∈ W)
      (hηP : componentGenericPoint X P.component ∈ W),
      X.presheaf.germ W _ hηP b = P.toComponent.hom (X.presheaf.germ W _ hPg b) := fun P hPg hηP =>
    (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hPg P.specializes_genericPoint b).symm
  have hcomp : ∀ (P : MMP.Mori.PrimeDivisor X) (hP : (P.support ∩ W).Nonempty),
      (b ^ M • T) ⟨P.component, P.componentGenericPoint_mem_of_nonempty hP⟩ =
        P.toComponent.hom (X.presheaf.germ W _ (P.genericPoint_mem_of_nonempty hP) b) ^ M *
          (t : RationalFunctions X) P.component := by
    intro P hP
    rw [rationalFunctions_smul_apply, map_pow, hgerm P (P.genericPoint_mem_of_nonempty hP)]
  refine ⟨b ^ M • T, ?_, ?_⟩
  · intro P hP
    have hPg := P.genericPoint_mem_of_nonempty hP
    rw [hcomp P hP]
    by_cases hPb : P.genericPoint ∈ X.basicOpen b
    · have hPU : (P.support ∩ U).Nonempty :=
        ⟨P.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support P, (hbV hPb).1⟩
      rw [← map_pow]
      exact (hts P hPU).toComponent_mul _
    · have hmax : X.presheaf.germ W _ hPg b ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk
        P.genericPoint) :=
        fun hunit => hPb ((Scheme.mem_basicOpen X b _ hPg).mpr hunit)
      have hT : P.OrdGE (P.ord t) ((t : RationalFunctions X) P.component) :=
        Or.inr (P.valuation_component t).ge
      refine (((P.ordGE_one_toComponent hmax).pow M).mul hT).mono ?_
      by_cases hPS : P ∈ S
      · have : (-D'.coeff P - P.ord t).toNat ≤ M :=
          Finset.le_sup (f := fun P => (-D'.coeff P - P.ord t).toNat) (hS.mem_toFinset.mpr hPS)
        have := Int.self_le_toNat (-D'.coeff P - P.ord t)
        omega
      · simp only [hSdef, Set.mem_setOf_eq, not_or, not_not] at hPS
        have : (0 : ℤ) ≤ M := Int.natCast_nonneg M
        omega
  · have hEg := E.specializes_genericPoint.mem_open W.isOpen hE
    have hP : (E.support ∩ W).Nonempty :=
      ⟨E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support E, hE⟩
    have := hcomp E hP
    rw [this, map_mul, map_pow, E.valuation_toComponent_of_isUnit
      ((Scheme.mem_basicOpen X b _ hE).mp hEb), one_pow, one_mul, E.valuation_component, ht]

end FlatCartier

section FlatCartier2

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

private theorem mem_basicOpen_iff_notMem {W : X.Opens} (hW : IsAffineOpen W) {x : X} (hx : x ∈ W)
    (c : Γ(X, W)) : x ∈ X.basicOpen c ↔ c ∉ (hW.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h1 := hW.fromSpec_preimage_basicOpen (f := c)
  have h2 := hW.fromSpec_primeIdealOf ⟨x, hx⟩
  have : x ∈ X.basicOpen c ↔ hW.primeIdealOf ⟨x, hx⟩ ∈ hW.fromSpec ⁻¹ᵁ X.basicOpen c := by
    change _ ↔ hW.fromSpec (hW.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen c
    rw [h2]
  rw [this, h1]
  exact PrimeSpectrum.mem_basicOpen _ _

/-- If the module `𝒪_X(-D)(W)` is flat over `Γ(X, W)` on an affine open `W`, then `D` has a local
equation near every point of `W`. -/
private theorem exists_isLocalEquation_of_flat (D : Divisor X) {W : X.Opens} (hW : IsAffineOpen W)
    [Module.Flat Γ(X, W) ((-D).divisorialSubmodule W)] {x : X} (hx : x ∈ W) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ g : (RationalFunctions X)ˣ, D.IsLocalEquation V g := by
  classical
  have hηW : genericPoint X ∈ W := (genericPoint_specializes x).mem_open W.isOpen hx
  haveI : Nonempty W := ⟨⟨x, hx⟩⟩
  haveI := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  haveI := finite_divisorialSubmodule (-D) hW
  haveI := isFractionRing_rationalFunctions hW hηW
  obtain ⟨a₀, hηa₀, ha₀⟩ := exists_regular_divisorialSection (-D) hW hηW
  have hN : (-D).divisorialSubmodule W ≠ ⊥ := by
    intro hbot
    have hmem : (algebraMap Γ(X, W) ((rationalFunctionsPresheaf X).obj (op W)) a₀) ∈
        (-D).divisorialSubmodule W := ha₀
    rw [hbot, Submodule.mem_bot] at hmem
    have : a₀ = 0 := (FaithfulSMul.algebraMap_injective Γ(X, W)
      ((rationalFunctionsPresheaf X).obj (op W))) (hmem.trans (map_zero _).symm)
    rw [this, Scheme.basicOpen_zero] at hηa₀
    exact hηa₀
  haveI : (hW.primeIdealOf ⟨x, hx⟩).asIdeal.IsPrime := (hW.primeIdealOf ⟨x, hx⟩).isPrime
  obtain ⟨a, haN, ha0, c, hc, hca⟩ := exists_principal_of_flat ((-D).divisorialSubmodule W) hN
    (hW.primeIdealOf ⟨x, hx⟩).asIdeal
  obtain ⟨χ, hχ, hineq⟩ := MMP.Fourfold.exists_unit_of_divisorialSubmodule_ne_zero (D := -D)
    (V := W) ⟨x, hx⟩ ⟨a, haN⟩ (fun h0 => ha0 (congrArg Subtype.val h0))
  refine ⟨W ⊓ X.basicOpen c, ⟨hx, (mem_basicOpen_iff_notMem hW hx c).mpr hc⟩, χ, ?_⟩
  intro E hE
  have hEV0 : E.genericPoint ∈ W ⊓ X.basicOpen c := E.genericPoint_mem_of_nonempty hE
  have hEV : E.genericPoint ∈ (W : Set X) ∧ E.genericPoint ∈ (X.basicOpen c : Set X) := hEV0
  have hEW : (E.support ∩ (W : Set X)).Nonempty :=
    ⟨E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support E, hEV.1⟩
  have hηE := E.componentGenericPoint_mem_of_nonempty hEW
  apply le_antisymm
  · have := hineq E hEW
    rw [DivisorWithCoeffs.coeff_neg] at this
    omega
  · obtain ⟨s, hsN, hsv⟩ := exists_mem_divisorialSubmodule_valuation_eq (-D) hW E hEV.1
    obtain ⟨r, hr⟩ := hca s hsN
    have hsm : ∀ (r : Γ(X, W)) (s : ToType ((rationalFunctionsPresheaf X).obj (op W))),
        (r • s) ⟨E.component, hηE⟩ =
          E.toComponent.hom (X.presheaf.germ W _ hEV.1 r) * s ⟨E.component, hηE⟩ := by
      intro r s
      rw [rationalFunctions_smul_apply,
        ← TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hEV.1
          E.specializes_genericPoint r]
      rfl
    have h1 := congrFun hr ⟨E.component, hηE⟩
    have hχ' : a ⟨E.component, hηE⟩ = (χ : RationalFunctions X) E.component :=
      hχ E.component hηE
    rw [hsm, hsm, hχ'] at h1
    have hv := congrArg E.valuation h1
    rw [map_mul, map_mul, E.valuation_toComponent_of_isUnit
      ((Scheme.mem_basicOpen X c _ hEV.1).mp hEV.2), one_mul, hsv, E.valuation_component] at hv
    by_cases hr0 : E.toComponent.hom (X.presheaf.germ W _ hEV.1 r) = 0
    · rw [hr0, map_zero, zero_mul] at hv
      exact absurd hv WithZero.exp_ne_zero
    · have h1le : 1 ≤ E.valuation (E.toComponent.hom (X.presheaf.germ W _ hEV.1 r)) :=
        E.one_le_valuation_toComponent (fun h0 => hr0 (by rw [h0, map_zero]))
      have hle : WithZero.exp (E.ord χ) ≤ WithZero.exp (-(-D).coeff E) := by
        rw [hv]; exact le_mul_of_one_le_left' h1le
      rw [WithZero.exp_le_exp, DivisorWithCoeffs.coeff_neg] at hle
      omega

end FlatCartier2

section CodimOneCartier

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- A divisor has a local equation on an affine open neighbourhood of every point of coheight
`≤ 1`. -/
private theorem exists_affine_isLocalEquation_of_coheight_le_one (D : Divisor X) {x : X}
    (hx : Order.coheight x ≤ 1) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ ∃ g : (RationalFunctions X)ˣ, D.IsLocalEquation V g :=
        by
  obtain ⟨W, hxW, g, hg⟩ : ∃ W : X.Opens, x ∈ W ∧ ∃ g : (RationalFunctions X)ˣ,
      D.IsLocalEquation W g := by
    rcases hx.lt_or_eq with h0 | h1
    · rw [Order.lt_one_iff, Order.coheight_eq_zero] at h0
      have hxη : x = genericPoint X := by
        have : x ≤ genericPoint X :=
          Scheme.le_iff_specializes.mpr ((genericPoint_spec X).specializes (Set.mem_univ x))
        have h2 : genericPoint X ≤ x := h0 this
        exact (Specializes.antisymm (Scheme.le_iff_specializes.mp this)
          (Scheme.le_iff_specializes.mp h2)).eq.symm
      refine ⟨MMP.Flips.divisorSuppCompl D, ?_, 1, fun E hE => ?_⟩
      · rw [hxη]
        exact MMP.Flips.componentGenericPoint_mem_divisorSuppCompl D
          ⟨Set.univ, by simp [irreducibleComponents_eq_singleton]⟩ |> fun h => by
            simpa [componentGenericPoint_eq'] using h
      · rw [MMP.Flips.coeff_eq_zero_of_le_divisorSuppCompl le_rfl hE]
        simp [PrimeDivisor.ord_one]
    · let E : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h1
      have hE : E.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x h1
      obtain ⟨W, g, hEW, hg⟩ := MMP.Positivity.Divisor.exists_isLocalEquation D E
      exact ⟨W, hE ▸ hEW, g, hg⟩
  obtain ⟨V, hV, hxV, hsub⟩ := exists_isAffineOpen_mem_and_subset hxW
  exact ⟨V, hV, hxV, g, hg.mono hsub⟩

end CodimOneCartier

private theorem height_comap_le_of_torsionFree {R S : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing S] [IsNoetherianRing S] [Algebra R S]
        [Module.Finite R S]
    (htf : ∀ r : R, r ≠ 0 → ∀ s : S, algebraMap R S r * s = 0 → s = 0)
    (P : Ideal S) [P.IsPrime] : (P.comap (algebraMap R S)).height ≤ P.height := by
  classical
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal S) ≤ P)
  haveI hQprime : Q.IsPrime := hQ.1.1
  have hdisj := Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hQ
  have hinj : Function.Injective (algebraMap R (S ⧸ Q)) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hmem : algebraMap R S r ∈ Q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply]
      exact hr
    have hnz : algebraMap R S r ∈ nonZeroDivisors S := by
      rw [mem_nonZeroDivisors_iff]
      exact ⟨fun s hs => htf r hr0 s hs, fun s hs => htf r hr0 s (by rw [mul_comm]; exact hs)⟩
    exact Set.disjoint_left.mp hdisj hmem hnz
  haveI : FaithfulSMul R (S ⧸ Q) := (faithfulSMul_iff_algebraMap_injective R (S ⧸ Q)).mpr hinj
  haveI : Module.Finite R (S ⧸ Q) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ R Q).toLinearMap (Ideal.Quotient.mk_surjective)
  haveI : Algebra.IsIntegral R (S ⧸ Q) := Algebra.IsIntegral.of_finite R _
  haveI : Algebra.HasGoingDown R (S ⧸ Q) := inferInstance
  set P' : Ideal (S ⧸ Q) := P.map (Ideal.Quotient.mk Q) with hP'
  haveI hP'prime : P'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hQP)
  have hcomap : P'.comap (Ideal.Quotient.mk Q) = P := by
    rw [hP', Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ←
        RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
    exact sup_eq_left.mpr hQP
  haveI : P'.LiesOver (P.comap (algebraMap R S)) := by
    refine ⟨?_⟩
    rw [Ideal.under_def, IsScalarTower.algebraMap_eq R S (S ⧸ Q), ← Ideal.comap_comap,
      Ideal.Quotient.algebraMap_eq, hcomap]
  haveI : IsNoetherianRing (S ⧸ Q) := inferInstance
  have h1 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (R := R) (S := S ⧸ Q)
    (P.comap (algebraMap R S)) P'
  have h2 : P'.height ≤ P.height := by
    have hf := RingHom.strictMono_comap_of_surjective (f := Ideal.Quotient.mk Q)
      Ideal.Quotient.mk_surjective
    have := Order.height_le_height_apply_of_strictMono
      (PrimeSpectrum.comap (Ideal.Quotient.mk Q)) hf ⟨P', hP'prime⟩
    rw [← PrimeSpectrum.height_eq_orderHeight] at this
    have e : (PrimeSpectrum.comap (Ideal.Quotient.mk Q) ⟨P', hP'prime⟩) = ⟨P, inferInstance⟩ :=
      PrimeSpectrum.ext hcomap
    rw [e, ← PrimeSpectrum.height_eq_orderHeight] at this
    exact this
  exact (le_self_add.trans h1.symm.le).trans h2

section MonomialMem

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (m : ℕ) [NeZero m] (D : Divisor X) {φ : (RationalFunctions X)ˣ}

/-- `g tʲ` lies in `𝒜(V)` as soon as `v_E(g) ≥ j d_E` along every prime divisor `E` meeting `V`. -/
private theorem reduce_monomial_mem_carrier (h : principalDivisor φ + m • D = 0) (V : X.Opens)
    (j : ℕ) (g : ToType ((rationalFunctionsPresheaf X).obj (op V)))
    (hg : ∀ (E : MMP.Mori.PrimeDivisor X) (hE : (E.support ∩ (V : Set X)).Nonempty),
      E.OrdGE (j * D.coeff E) (g ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩)) :
    reduce m φ V (Polynomial.monomial j g) ∈ carrier (φ := φ) m D V := by
  rw [mem_carrier_iff m D h.ge]
  intro n
  rw [coeff_reduce_monomial]
  split_ifs with hn
  · subst hn
    intro E hE
    have hord : E.ord φ + (m : ℤ) * D.coeff E = 0 := by
      have := congrArg (fun F => F.coeff E) h
      simpa [coeff_principalDivisor] using this
    have hφE : E.OrdGE (((j / m : ℕ) : ℤ) * E.ord φ)
        ((phiOn φ V ^ (j / m)) ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩) := by
      have h1 : E.OrdGE (E.ord φ) (phiOn φ V ⟨E.component, E.componentGenericPoint_mem_of_nonempty
          hE⟩) :=
        Or.inr (E.valuation_component φ).ge
      exact h1.pow (j / m)
    have := (hg E hE).mul hφE
    refine this.mono ?_
    rw [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_neg]
    simp only [nsmul_eq_mul]
    have hj : (j : ℤ) = ((j % m : ℕ) : ℤ) + (m : ℤ) * ((j / m : ℕ) : ℤ) := by
      exact_mod_cast (Nat.mod_add_div j m).symm
    have : ((j / m : ℕ) : ℤ) * E.ord φ = -(m : ℤ) * ((j / m : ℕ) : ℤ) * D.coeff E := by
      linear_combination ((j / m : ℕ) : ℤ) * hord
    have key : (j : ℤ) * D.coeff E + ((j / m : ℕ) : ℤ) * E.ord φ =
        ((j % m : ℕ) : ℤ) * D.coeff E := by
      linear_combination D.coeff E * hj + this
    linarith [key]
  · exact Submodule.zero_mem _

end MonomialMem

section LocalEquationUnit

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (m : ℕ) [NeZero m] (D : Divisor X) {φ : (RationalFunctions X)ˣ}

/-- The section of `𝒦_X` over `V` given by a unit of `K(X)`. -/
private def secOf (V : X.Opens) (u : (RationalFunctions X)ˣ) :
    ToType ((rationalFunctionsPresheaf X).obj (op V)) := fun Z => (u : RationalFunctions X) Z.1

/-- Where `D` has a local equation `g`, the element `g t` of `𝓛(V)` is a unit of `𝒜(V)`, with
inverse `(g φ)⁻¹ tᵐ⁻¹`. -/
private theorem isUnit_reduce_monomial_one (h : principalDivisor φ + m • D = 0) {V : X.Opens}
    {g : (RationalFunctions X)ˣ} (hg : D.IsLocalEquation V g) :
    ∃ (a b : carrier (φ := φ) m D V),
      (a : (ambient m φ).obj (op V)) =
        reduce m φ V (Polynomial.monomial 1 (secOf V g)) ∧
      a * b = 1 := by
  have hord : ∀ E : MMP.Mori.PrimeDivisor X, E.ord φ + (m : ℤ) * D.coeff E = 0 := fun E => by
    have := congrArg (fun F => F.coeff E) h
    simpa [coeff_principalDivisor] using this
  have ha := reduce_monomial_mem_carrier m D h V 1 (secOf V g)
    (fun E hE => Or.inr (by
      change _ ≤ E.valuation ((g : RationalFunctions X) E.component)
      rw [E.valuation_component, ← hg E hE]
      simp))
  have hb := reduce_monomial_mem_carrier m D h V (m - 1)
    (secOf V (g⁻¹ * φ⁻¹))
    (fun E hE => Or.inr (by
      change _ ≤ E.valuation (((g⁻¹ * φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)
          E.component)
      rw [E.valuation_component, PrimeDivisor.ord_mul, PrimeDivisor.ord_inv, PrimeDivisor.ord_inv,
        ← hg E hE, WithZero.exp_le_exp]
      have := hord E
      have h1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
        have := NeZero.pos m
        omega
      rw [h1]
      linarith))
  refine ⟨⟨_, ha⟩, ⟨_, hb⟩, rfl, Subtype.ext ?_⟩
  change reduce m φ V (Polynomial.monomial 1 (secOf V g)) *
    reduce m φ V (Polynomial.monomial (m - 1) (secOf V (g⁻¹ * φ⁻¹))) = 1
  rw [reduce_monomial_mul, Nat.add_sub_cancel' (NeZero.pos m),
    reduce_monomial_of_le m φ (le_refl m)]
  rw [Nat.sub_self, ← map_one (reduce m φ V), ← Polynomial.monomial_zero_one]
  congr 2
  funext Z
  change (φ : RationalFunctions X) Z.1 * ((g : RationalFunctions X) Z.1 *
    ((g⁻¹ * φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1) = (1 : RationalFunctions X)
        Z.1
  have h1 : ((φ * (g * (g⁻¹ * φ⁻¹)) : (RationalFunctions X)ˣ) : RationalFunctions X) = 1 := by
    rw [show φ * (g * (g⁻¹ * φ⁻¹)) = 1 by group]; rfl
  have := congrFun h1 Z.1
  simp only [Units.val_mul, Pi.mul_apply] at this ⊢
  exact this

end LocalEquationUnit

section DivisorialToCarrier

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (m : ℕ) [NeZero m] (D : Divisor X) {φ : (RationalFunctions X)ˣ}

/-- A section `s` of `𝒪_X(D)(V)` gives `s t⁻¹ = s φ⁻¹ tᵐ⁻¹ ∈ 𝒜(V)`. -/
private theorem reduce_monomial_pred_mem_carrier (h : principalDivisor φ + m • D = 0) {V : X.Opens}
    {s : ToType ((rationalFunctionsPresheaf X).obj (op V))} (hs : s ∈ D.divisorialSubmodule V) :
    reduce m φ V (Polynomial.monomial (m - 1) (s * secOf V φ⁻¹)) ∈ carrier (φ := φ) m D V := by
  refine reduce_monomial_mem_carrier m D h V (m - 1) _ fun E hE => ?_
  have hord : E.ord φ + (m : ℤ) * D.coeff E = 0 := by
    have := congrArg (fun F => F.coeff E) h
    simpa [coeff_principalDivisor] using this
  have hv : E.valuation (((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) E.component) =
      WithZero.exp ((m : ℤ) * D.coeff E) := by
    rw [E.valuation_component, PrimeDivisor.ord_inv]
    congr 1
    linarith
  have := ordGE_unit_mul E hv (hs E hE)
  have hc : (s * secOf V φ⁻¹) ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩ =
      ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) E.component *
        s ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩ := mul_comm _ _
  rw [hc]
  refine this.mono ?_
  have h1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
    have := NeZero.pos m
    omega
  rw [h1]
  linarith

end DivisorialToCarrier

section WeilSheafOfDivisor

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- `𝒪_X(D)` as an `𝒪_X`-submodule of `𝒦_X`. -/
private noncomputable def divisorialRF (D : Divisor X) :
    MMP.Flips.RationalFunctionsSubmodule X where
  sections := D.divisorialSubmodule
  map_mem := by
    intro U V i s hs
    exact Divisor.IsDivisorialSection.map i hs
  mem_of_locally := by
    intro U s hs E hE
    obtain ⟨x, hxE, hxU⟩ := hE
    obtain ⟨W, i, hxW, hW⟩ := hs x hxU
    exact hW E ⟨x, hxE, hxW⟩

private theorem divisorialRF_isSaturated (D : Divisor X) : (divisorialRF D).IsSaturated := by
  refine MMP.Flips.RationalFunctionsSubmodule.ext fun V => le_antisymm
    ((divisorialRF D).sections_le_saturation V) fun s hs E hE => ?_
  have hEV := E.genericPoint_mem_of_nonempty hE
  obtain ⟨W, i, hxW, hW⟩ := ((divisorialRF D).germ_mem_stalkSet_iff hEV s).mp
    (hs E.genericPoint hEV E.coheight_genericPoint.le)
  exact hW E ⟨E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support E, hxW⟩

private theorem divisorialRF_isCoherent (D : Divisor X) :
    SheafOfModules.IsCoherent (divisorialRF D).toModules := by
  haveI : D.divisorialSheaf.IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn _
      (fun V : X.affineOpens => (V : X.Opens)) (IsOpenCover.mk (iSup_affineOpens_eq_top X))
      (fun V => V.2) fun V =>
        Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isFiniteTildeOn_of_moduleFinite_sections
          _ V (finite_divisorialSubmodule D V.2)
  exact Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType
    D.divisorialSheaf

/-- Multiplying by a local equation `g` of `D` identifies `𝒪_X(D)` with `𝒪_X(0)`. -/
private theorem isDivisorialSection_iff_mul {D : Divisor X} {V W : X.Opens} (hWV : W ≤ V)
    {g : (RationalFunctions X)ˣ} (hg : D.IsLocalEquation V g)
    (φ : ToType ((rationalFunctionsPresheaf X).obj (op W))) :
    D.IsDivisorialSection W φ ↔
      (0 : Divisor X).IsDivisorialSection W (secOf W g * φ) := by
  refine forall_congr' fun E => forall_congr' fun hE => ?_
  have hgE := hg E (hE.mono (Set.inter_subset_inter_right _ hWV))
  have hv : E.valuation ((g : RationalFunctions X) E.component) = WithZero.exp (D.coeff E) := by
    rw [E.valuation_component, hgE]
  have hv' : E.valuation (((g⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) E.component) =
      WithZero.exp (-D.coeff E) := by
    rw [E.valuation_component, PrimeDivisor.ord_inv, hgE]
  have hc : ∀ x : ToType ((rationalFunctionsPresheaf X).obj (op W)),
      (secOf W g * x) ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩ =
        (g : RationalFunctions X) E.component *
          x ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩ := fun x => rfl
  constructor
  · intro h
    rw [hc]
    exact (ordGE_unit_mul E hv h).mono (by simp)
  · intro h
    rw [hc] at h
    have h2 := ordGE_unit_mul E hv' h
    have h1 : ((g⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) E.component *
        (g : RationalFunctions X) E.component = 1 := by
      simpa using congrArg (fun f : RationalFunctions X => f E.component) g.inv_mul
    rw [← mul_assoc, h1, one_mul] at h2
    exact h2.mono (by simp)

/-- The unit of `𝒦_X(V)` given by a unit of `K(X)`. -/
private noncomputable def secUnit (V : X.Opens) (u : (RationalFunctions X)ˣ) :
    ((rationalFunctionsPresheaf X).obj (op V))ˣ where
  val := secOf V u
  inv := secOf V u⁻¹
  val_inv := funext fun Z => congrArg (fun f : RationalFunctions X => f Z.1) u.mul_inv
  inv_val := funext fun Z => congrArg (fun f : RationalFunctions X => f Z.1) u.inv_mul

private theorem divisorialRF_principal (D : Divisor X) (η : X) (hη : Order.coheight η ≤ 1) :
    ∃ f : ((rationalFunctionsPresheaf X).stalk η)ˣ,
      (divisorialRF D).stalkSet η = Set.range fun a : X.presheaf.stalk η =>
        (f : (rationalFunctionsPresheaf X).stalk η) *
          (MMP.Flips.structureStalkToRationalFunctionsStalk X η).hom a := by
  obtain ⟨V, -, hηV, g, hg⟩ := exists_affine_isLocalEquation_of_coheight_le_one D hη
  refine ⟨Units.map ((rationalFunctionsPresheaf X).germ V η hηV).hom.toMonoidHom
    (secUnit V g⁻¹), ?_⟩
  have hf : ∀ (W : X.Opens) (hηW : η ∈ W) (i : W ⟶ V),
      (((Units.map ((rationalFunctionsPresheaf X).germ V η hηV).hom.toMonoidHom
        (secUnit V g⁻¹) : ((rationalFunctionsPresheaf X).stalk η)ˣ)) :
          (rationalFunctionsPresheaf X).stalk η) =
        (rationalFunctionsPresheaf X).germ W η hηW (secOf W g⁻¹) := by
    intro W hηW i
    exact (TopCat.Presheaf.germ_res_apply (rationalFunctionsPresheaf X) i η hηW (secOf V g⁻¹)).symm
  ext z
  constructor
  · rintro ⟨W, hηW, s, hs, rfl⟩
    have hηW' : η ∈ W ⊓ V := ⟨hηW, hηV⟩
    have hs' : (rationalFunctionsPresheaf X).map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op s ∈
        D.divisorialSubmodule (W ⊓ V) := (divisorialRF D).map_mem _ hs
    have h0 := (isDivisorialSection_iff_mul (inf_le_right : W ⊓ V ≤ V) hg _).mp hs'
    obtain ⟨r, hr⟩ := Divisor.IsDivisorialSection.exists_eq h0
    refine ⟨X.presheaf.germ (W ⊓ V) η hηW' r, ?_⟩
    have e1 : (rationalFunctionsPresheaf X).map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op s =
        secOf (W ⊓ V) g⁻¹ * (toRationalFunctionsPresheaf X).app (op (W ⊓ V)) r := by
      rw [hr, ← mul_assoc]
      have : secOf (W ⊓ V) g⁻¹ * secOf (W ⊓ V) g = 1 := (secUnit (W ⊓ V) g).inv_val
      rw [this, one_mul]
    change _ * (MMP.Flips.structureStalkToRationalFunctionsStalk X η).hom _ = _
    have h2 : (MMP.Flips.structureStalkToRationalFunctionsStalk X η).hom
        (X.presheaf.germ (W ⊓ V) η hηW' r) = (rationalFunctionsPresheaf X).germ (W ⊓ V) η hηW'
          ((toRationalFunctionsPresheaf X).app (op (W ⊓ V)) r) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply (W ⊓ V) η hηW' (toRationalFunctionsPresheaf X) r
    rw [hf (W ⊓ V) hηW' (homOfLE inf_le_right), h2, ← map_mul, ← e1,
      TopCat.Presheaf.germ_res_apply]
  · rintro ⟨a, rfl⟩
    obtain ⟨W, hηW, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf a
    have hηW' : η ∈ W ⊓ V := ⟨hηW, hηV⟩
    set r' := X.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op r with hr'
    have hmem : secOf (W ⊓ V) g⁻¹ * (toRationalFunctionsPresheaf X).app (op (W ⊓ V)) r' ∈
        D.divisorialSubmodule (W ⊓ V) := by
      refine (isDivisorialSection_iff_mul (inf_le_right : W ⊓ V ≤ V) hg _).mpr ?_
      have h1 : secOf (W ⊓ V) g * secOf (W ⊓ V) g⁻¹ = 1 := (secUnit (W ⊓ V) g).val_inv
      rw [← mul_assoc, h1, one_mul]
      exact Divisor.isDivisorialSection_algebraMap le_rfl r'
    refine ⟨W ⊓ V, hηW', _, hmem, ?_⟩
    change _ = _ * (MMP.Flips.structureStalkToRationalFunctionsStalk X η).hom _
    have h2 : (MMP.Flips.structureStalkToRationalFunctionsStalk X η).hom
        (X.presheaf.germ (W ⊓ V) η hηW' r') = (rationalFunctionsPresheaf X).germ (W ⊓ V) η hηW'
          ((toRationalFunctionsPresheaf X).app (op (W ⊓ V)) r') :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply (W ⊓ V) η hηW' (toRationalFunctionsPresheaf X) r'
    rw [hf (W ⊓ V) hηW' (homOfLE inf_le_right), map_mul, ← h2, hr',
      TopCat.Presheaf.germ_res_apply X.presheaf]

/-- `𝒪_X(D)` as a Weil divisorial subsheaf. -/
private noncomputable def weilOfDivisor (D : Divisor X) : MMP.Flips.WeilDivisorialSubsheaf X where
  toRationalFunctionsSubmodule := divisorialRF D
  isCoherent := divisorialRF_isCoherent D
  principal_codim_one := divisorialRF_principal D
  isSaturated := divisorialRF_isSaturated D

end WeilSheafOfDivisor

section FiniteDim

/-- A finite morphism preserves heights in the specialization order: it maps strict
specializations to strict specializations, and specializations of the image lift, as the
morphism is closed. -/
private theorem height_apply_eq_of_isFinite {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g]
    (x : X) : height (g x) = height x := by
  have hmono : StrictMono g := fun a b hab => by
    have hba : b ⤳ a := Scheme.le_iff_specializes.mp hab.le
    refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr (hba.map g.continuous)) fun h => ?_
    have heq : g b = g a := ((hba.map g.continuous).antisymm (Scheme.le_iff_specializes.mp h)).eq
    exact hab.ne (MMP.Fourfold.eq_of_specializes_of_isFinite g hba heq).symm
  refine (height_eq_of_strictMono g hmono (fun a b hb => ?_) x).symm
  obtain ⟨a', ha', rfl⟩ := g.isClosedMap.specializingMap (Scheme.le_iff_specializes.mp hb.le)
  refine ⟨a', lt_of_le_not_ge (Scheme.le_iff_specializes.mpr ha') fun h => hb.ne ?_, rfl⟩
  rw [(Specializes.antisymm ha' (Scheme.le_iff_specializes.mp h)).eq]

/-- A finite morphism preserves the dimension of the closure of a point. -/
private theorem topologicalKrullDim_closure_image_singleton_eq {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsFinite g] (x : X) :
    topologicalKrullDim (closure {g x} : Set Y) = topologicalKrullDim (closure {x} : Set X) := by
  rw [topologicalKrullDim_closure_singleton_eq_height,
    topologicalKrullDim_closure_singleton_eq_height, height_apply_eq_of_isFinite]

end FiniteDim

section Dictionary

open CategoryTheory.Limits

section TDef

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (m : ℕ) [NeZero m] (φ : (RationalFunctions X)ˣ)

/-- The class `t` of the variable in `𝓛(V)`. -/
private noncomputable def tV (V : X.Opens) : (ambient m φ).obj (op V) :=
  reduce m φ V (Polynomial.monomial 1 1)

/-- The inverse `φ⁻¹ tᵐ⁻¹` of `t` in `𝓛(V)`. -/
private noncomputable def tInvV (V : X.Opens) : (ambient m φ).obj (op V) :=
  reduce m φ V (Polynomial.monomial (m - 1) (secOf V φ⁻¹))

private theorem tV_mul_tInvV (V : X.Opens) : tV m φ V * tInvV m φ V = 1 := by
  unfold tV tInvV
  rw [reduce_monomial_mul, Nat.add_sub_cancel' (NeZero.pos m),
    reduce_monomial_of_le m φ (le_refl m)]
  rw [Nat.sub_self, ← map_one (reduce m φ V), ← Polynomial.monomial_zero_one]
  congr 2
  funext Z
  change (φ : RationalFunctions X) Z.1 * (1 * ((φ⁻¹ : (RationalFunctions X)ˣ) :
    RationalFunctions X) Z.1) = (1 : RationalFunctions X) Z.1
  have := congrArg (fun f : RationalFunctions X => f Z.1) φ.mul_inv
  simpa using this

private theorem map_tV {V V1 : X.Opens} (i : V1 ⟶ V) :
    ((ambient m φ).map i.op).hom (tV m φ V) = tV m φ V1 := by
  unfold tV
  rw [ambient_map_reduce, Polynomial.map_monomial, map_one]

end TDef

/-- The germ of a nonzerodivisor of an affine open is nonzero in every stalk. -/
private theorem germ_ne_zero_of_mem_nonZeroDivisors {Y : Scheme.{u}} {V : Y.Opens}
    (hV : IsAffineOpen V) {x : Y} (hx : x ∈ V) {s : Γ(Y, V)} (hs : s ∈ nonZeroDivisors Γ(Y, V)) :
    Y.presheaf.germ V x hx s ≠ 0 := by
  letI : Algebra Γ(Y, V) (Y.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨x, hx⟩
  haveI := hV.isLocalization_stalk ⟨x, hx⟩
  intro h0
  have h1 : algebraMap Γ(Y, V) (Y.presheaf.stalk x) s = 0 := h0
  obtain ⟨⟨u, hu⟩, hus⟩ := (IsLocalization.map_eq_zero_iff
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (Y.presheaf.stalk x) s).mp h1
  have hu0 : u = 0 := (mem_nonZeroDivisors_iff_right.mp hs) u hus
  exact hu (by rw [hu0]; exact Ideal.zero_mem _)

/-- The pull-back of the germ of a regular function is the germ of its pull-back. -/
private theorem pullHom_toRationalFunctions {X' X : Scheme.{u}} {p : X' ⟶ X}
    (hp : MMP.Flips.MapsGenericPointsToGenericPoints p) {V : X.Opens} {U' : X'.Opens}
    (hUV : U' ≤ p ⁻¹ᵁ V) (r : Γ(X, V))
    (Z' : {Z' : irreducibleComponents X' // componentGenericPoint X' Z' ∈ U'}) :
    MMP.Flips.rationalFunctionsPullbackHom hp hUV ((toRationalFunctionsPresheaf X).app (op V) r)
        Z' =
      X'.presheaf.germ U' (componentGenericPoint X' Z'.1) Z'.2 (p.appLE V U' hUV r) := by
  change (p.stalkMap (componentGenericPoint X' Z'.1)).hom
      ((X.presheaf.stalkSpecializes (specializes_of_eq (hp Z'.1).choose_spec)).hom
        (X.presheaf.germ V _ _ r)) = _
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  have := congrArg (fun f => f.hom r) (Scheme.Hom.germ_stalkMap p V
    (componentGenericPoint X' Z'.1) (hUV Z'.2))
  have h2 : X'.presheaf.germ U' (componentGenericPoint X' Z'.1) Z'.2 (p.appLE V U' hUV r) =
      X'.presheaf.germ (p ⁻¹ᵁ V) (componentGenericPoint X' Z'.1) (hUV Z'.2) (p.app V r) := by
    rw [Scheme.Hom.appLE]
    exact TopCat.Presheaf.germ_res_apply X'.presheaf (homOfLE hUV) _ _ _
  rw [h2]
  exact this

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (m : ℕ) [NeZero m] (D : Divisor X) {φ : (RationalFunctions X)ˣ}
  (h : principalDivisor φ + m • D = 0)
  [IsFinite (toBase m D h.ge)] [IsReduced (cover m D h.ge)]

/-- The ring map `𝒜(V) → 𝒦_{X'}(p⁻¹V)`. -/
private noncomputable def toRF {V : X.Opens} (hV : IsAffineOpen V) :
    (localSubalgebra m D h.ge).carrier V →+*
      ↑((rationalFunctionsPresheaf (cover m D h.ge)).obj (op (toBase m D h.ge ⁻¹ᵁ V))) :=
  ((toRationalFunctionsPresheaf (cover m D h.ge)).app _).hom.comp
    (psiEquiv m D h.ge hV).toRingHom

private theorem isUnit_toRF {V : X.Opens} (hV : IsAffineOpen V)
    (s : nonZeroDivisors ((localSubalgebra m D h.ge).carrier V)) : IsUnit (toRF m D h hV s) := by
  have hV' : IsAffineOpen (toBase m D h.ge ⁻¹ᵁ V) := hV.preimage _
  refine Pi.isUnit_iff.mpr fun Z' => ?_
  have hF := RationalFunctions.isField_stalk (cover m D h.ge) Z'.1
  suffices hne : toRF m D h hV s Z' ≠ 0 by
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel hne
    exact IsUnit.of_mul_eq_one b hb
  have hs : psiEquiv m D h.ge hV s.1 ∈
      nonZeroDivisors Γ(cover m D h.ge, toBase m D h.ge ⁻¹ᵁ V) := by
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    have h1 : s.1 * (psiEquiv m D h.ge hV).symm y = 0 := by
      apply (psiEquiv m D h.ge hV).injective
      rwa [map_mul, RingEquiv.apply_symm_apply, map_zero, mul_comm]
    have h2 := (mem_nonZeroDivisors_iff_left.mp s.2) _ h1
    rw [← (psiEquiv m D h.ge hV).apply_symm_apply y, h2, map_zero]
  exact germ_ne_zero_of_mem_nonZeroDivisors hV' Z'.2 hs

/-- The extension `𝓛(V) → 𝒦_{X'}(p⁻¹V)` of `toRF`. -/
private noncomputable def phi {V : X.Opens} (hV : IsAffineOpen V) (hηV : genericPoint X ∈ V) :
    (ambient m φ).obj (op V) →+*
      ↑((rationalFunctionsPresheaf (cover m D h.ge)).obj (op (toBase m D h.ge ⁻¹ᵁ V))) :=
  haveI : IsLocalization (nonZeroDivisors ((localSubalgebra m D h.ge).carrier V))
      ((ambient m φ).obj (op V)) := isLocalization_carrier m D h hV hηV
  IsLocalization.lift (M := nonZeroDivisors ((localSubalgebra m D h.ge).carrier V))
    (isUnit_toRF m D h hV)

private theorem phi_coe {V : X.Opens} (hV : IsAffineOpen V) (hηV : genericPoint X ∈ V)
    (a : (localSubalgebra m D h.ge).carrier V) :
    phi m D h hV hηV (a : (ambient m φ).obj (op V)) = toRF m D h hV a := by
  haveI : IsLocalization (nonZeroDivisors ((localSubalgebra m D h.ge).carrier V))
      ((ambient m φ).obj (op V)) := isLocalization_carrier m D h hV hηV
  exact IsLocalization.lift_eq (isUnit_toRF m D h hV) a

private theorem phi_structureMap {V : X.Opens} (hV : IsAffineOpen V) (hηV : genericPoint X ∈ V)
    (r : Γ(X, V)) :
    phi m D h hV hηV (((structureMap m φ).app (op V)).hom r) =
      ((toRationalFunctionsPresheaf (cover m D h.ge)).app _).hom
        (((toBase m D h.ge).appLE V (toBase m D h.ge ⁻¹ᵁ V) le_rfl).hom r) := by
  have h1 : ((structureMap m φ).app (op V)).hom r =
      (((localSubalgebra m D h.ge).algebraMap V r : (localSubalgebra m D h.ge).carrier V) :
        (ambient m φ).obj (op V)) := rfl
  rw [h1, phi_coe, ← psiEquiv_algebraMap m D h.ge hV r]
  rfl

include h in
private theorem phi_ofRationalFunctions
    (hmaps : MMP.Flips.MapsGenericPointsToGenericPoints (toBase m D h.ge))
    {V : X.Opens} (hV : IsAffineOpen V) (hηV : genericPoint X ∈ V)
    (κ : ToType ((rationalFunctionsPresheaf X).obj (op V))) :
    phi m D h hV hηV (((ofRationalFunctions m φ).app (op V)).hom κ) =
      MMP.Flips.rationalFunctionsPullbackHom hmaps (le_refl (toBase m D h.ge ⁻¹ᵁ V)) κ := by
  haveI := isFractionRing_rationalFunctions hV hηV
  have key := IsLocalization.ringHom_ext (nonZeroDivisors Γ(X, V))
    (S := (rationalFunctionsPresheaf X).obj (op V))
    (j := (phi m D h hV hηV).comp ((ofRationalFunctions m φ).app (op V)).hom)
    (k := MMP.Flips.rationalFunctionsPullbackHom hmaps (le_refl (toBase m D h.ge ⁻¹ᵁ V)))
    (RingHom.ext fun r => ?_)
  · exact congrArg (fun f => f κ) key
  · change phi m D h hV hηV (((structureMap m φ).app (op V)).hom r) = _
    rw [phi_structureMap]
    funext Z'
    exact (pullHom_toRationalFunctions hmaps (le_refl _) r Z').symm

private theorem psiEquiv_restrict {V V1 : X.Opens} (hV : IsAffineOpen V) (hV1 : IsAffineOpen V1)
    (hle : V1 ≤ V) (a : (localSubalgebra m D h.ge).carrier V) :
    psiEquiv m D h.ge hV1 ((localSubalgebra m D h.ge).restrict (homOfLE hle) a) =
      (cover m D h.ge).presheaf.map (homOfLE ((toBase m D h.ge).preimage_mono hle)).op
        (psiEquiv m D h.ge hV a) := by
  have := (Stacks.RelativeSpec.universalAlgebraMap (situation m D h.ge)).right.naturality
    (homOfLE hle).op
  exact congrArg (fun f => f.hom a) this

private theorem phi_res {V V1 : X.Opens} (hV : IsAffineOpen V) (hηV : genericPoint X ∈ V)
    (hV1 : IsAffineOpen V1) (hηV1 : genericPoint X ∈ V1) (hle : V1 ≤ V)
    (y : (ambient m φ).obj (op V)) :
    ((rationalFunctionsPresheaf (cover m D h.ge)).map
        (homOfLE ((toBase m D h.ge).preimage_mono hle)).op).hom (phi m D h hV hηV y) =
      phi m D h hV1 hηV1 (((ambient m φ).map (homOfLE hle).op).hom y) := by
  haveI : IsLocalization (nonZeroDivisors ((localSubalgebra m D h.ge).carrier V))
      ((ambient m φ).obj (op V)) := isLocalization_carrier m D h hV hηV
  have key := IsLocalization.ringHom_ext (nonZeroDivisors ((localSubalgebra m D h.ge).carrier V))
    (j := ((rationalFunctionsPresheaf (cover m D h.ge)).map
        (homOfLE ((toBase m D h.ge).preimage_mono hle)).op).hom.comp (phi m D h hV hηV))
    (k := (phi m D h hV1 hηV1).comp ((ambient m φ).map (homOfLE hle).op).hom)
    (RingHom.ext fun a => ?_)
  · exact congrArg (fun f => f y) key
  · change ((rationalFunctionsPresheaf (cover m D h.ge)).map
        (homOfLE ((toBase m D h.ge).preimage_mono hle)).op).hom
        (phi m D h hV hηV (a : (ambient m φ).obj (op V))) =
      phi m D h hV1 hηV1 (((ambient m φ).map (homOfLE hle).op).hom (a : (ambient m φ).obj (op V)))
    have hr : ((ambient m φ).map (homOfLE hle).op).hom (a : (ambient m φ).obj (op V)) =
        (((localSubalgebra m D h.ge).restrict (homOfLE hle) a :
          (localSubalgebra m D h.ge).carrier V1) : (ambient m φ).obj (op V1)) := rfl
    rw [hr, phi_coe, phi_coe]
    change _ = ((toRationalFunctionsPresheaf (cover m D h.ge)).app _).hom
      (psiEquiv m D h.ge hV1 ((localSubalgebra m D h.ge).restrict (homOfLE hle) a))
    rw [psiEquiv_restrict m D h hV hV1 hle a]
    exact (toRationalFunctionsPresheaf_app_map (homOfLE ((toBase m D h.ge).preimage_mono hle))
      (psiEquiv m D h.ge hV a)).symm

variable (hgen : ∀ Z' : irreducibleComponents (cover m D h.ge),
  toBase m D h.ge (componentGenericPoint (cover m D h.ge) Z') = genericPoint X)

include hgen in
private theorem mem_preimage_of_gen {V : X.Opens} (hηV : genericPoint X ∈ V)
    (Z' : irreducibleComponents (cover m D h.ge)) :
    componentGenericPoint (cover m D h.ge) Z' ∈ toBase m D h.ge ⁻¹ᵁ V := by
  change toBase m D h.ge (componentGenericPoint (cover m D h.ge) Z') ∈ V
  rw [hgen Z']
  exact hηV

/-- The rational function `t` of `X'`, from the chart `W₀`. -/
private noncomputable def psiFun {W0 : X.Opens} (hW0 : IsAffineOpen W0)
    (hηW0 : genericPoint X ∈ W0) : RationalFunctions (cover m D h.ge) :=
  fun Z' => phi m D h hW0 hηW0 (tV m φ W0) ⟨Z', mem_preimage_of_gen m D h hgen hηW0 Z'⟩

/-- The rational function `t⁻¹` of `X'`, from the chart `W₀`. -/
private noncomputable def psiInvFun {W0 : X.Opens} (hW0 : IsAffineOpen W0)
    (hηW0 : genericPoint X ∈ W0) : RationalFunctions (cover m D h.ge) :=
  fun Z' => phi m D h hW0 hηW0 (tInvV m φ W0) ⟨Z', mem_preimage_of_gen m D h hgen hηW0 Z'⟩

private theorem psiFun_mul_psiInvFun {W0 : X.Opens} (hW0 : IsAffineOpen W0)
    (hηW0 : genericPoint X ∈ W0) :
    psiFun m D h hgen hW0 hηW0 * psiInvFun m D h hgen hW0 hηW0 = 1 := by
  funext Z'
  change (phi m D h hW0 hηW0 (tV m φ W0) * phi m D h hW0 hηW0 (tInvV m φ W0))
    ⟨Z', mem_preimage_of_gen m D h hgen hηW0 Z'⟩ = 1
  rw [← map_mul, tV_mul_tInvV, map_one]
  rfl

include hgen in
private theorem phi_tV_apply {W0 V : X.Opens} (hW0 : IsAffineOpen W0)
    (hηW0 : genericPoint X ∈ W0) (hV : IsAffineOpen V) (hηV : genericPoint X ∈ V)
    (Z' : irreducibleComponents (cover m D h.ge))
    (h1 : componentGenericPoint (cover m D h.ge) Z' ∈ toBase m D h.ge ⁻¹ᵁ V) :
    phi m D h hV hηV (tV m φ V) ⟨Z', h1⟩ = psiFun m D h hgen hW0 hηW0 Z' := by
  obtain ⟨V1, hV1, hηV1, hsub⟩ := exists_isAffineOpen_mem_and_subset
    (U := V ⊓ W0) (x := genericPoint X) ⟨hηV, hηW0⟩
  have e1 := phi_res m D h hV hηV hV1 hηV1 (hsub.trans inf_le_left) (tV m φ V)
  have e2 := phi_res m D h hW0 hηW0 hV1 hηV1 (hsub.trans inf_le_right) (tV m φ W0)
  rw [map_tV] at e1 e2
  have e3 := congrArg (fun f => f ⟨Z', mem_preimage_of_gen m D h hgen hηV1 Z'⟩) (e1.trans e2.symm)
  exact e3

include hgen in
/-- **The key identity**: if `ρ t = s` in `𝓛(V)`, then the pull-back of `s` is `ψ(ρ)` times `t`. -/
private theorem pullback_eq_mul_psi
    (hmaps : MMP.Flips.MapsGenericPointsToGenericPoints (toBase m D h.ge))
    {W0 V : X.Opens} (hW0 : IsAffineOpen W0)
    (hηW0 : genericPoint X ∈ W0) (hV : IsAffineOpen V) (hηV : genericPoint X ∈ V)
    (ρ : (localSubalgebra m D h.ge).carrier V)
    (s : ToType ((rationalFunctionsPresheaf X).obj (op V)))
    (hρ : (ρ : (ambient m φ).obj (op V)) * tV m φ V =
      ((ofRationalFunctions m φ).app (op V)).hom s)
    (Z' : irreducibleComponents (cover m D h.ge))
    (h1 : componentGenericPoint (cover m D h.ge) Z' ∈ toBase m D h.ge ⁻¹ᵁ V) :
    MMP.Flips.rationalFunctionsPullbackHom hmaps (le_refl (toBase m D h.ge ⁻¹ᵁ V)) s ⟨Z', h1⟩ =
      ((toRationalFunctionsPresheaf (cover m D h.ge)).app _).hom
          (psiEquiv m D h.ge hV ρ) ⟨Z', h1⟩ * psiFun m D h hgen hW0 hηW0 Z' := by
  rw [← phi_ofRationalFunctions m D h hmaps hV hηV s, ← hρ, map_mul, phi_coe]
  change toRF m D h hV ρ ⟨Z', h1⟩ * phi m D h hV hηV (tV m φ V) ⟨Z', h1⟩ = _
  rw [phi_tV_apply m D h hgen hW0 hηW0 hV hηV Z' h1]
  rfl

/-- The restriction of `t` to an open of `X'`. -/
private noncomputable def psiOn {W0 : X.Opens} (hW0 : IsAffineOpen W0)
    (hηW0 : genericPoint X ∈ W0) (U' : (cover m D h.ge).Opens) :
    ToType ((rationalFunctionsPresheaf (cover m D h.ge)).obj (op U')) :=
  fun Z => psiFun m D h hgen hW0 hηW0 Z.1

private theorem ofRat_eq_reduce_C {V : X.Opens} (s : ToType ((rationalFunctionsPresheaf X).obj (op
    V))) :
    ((ofRationalFunctions m φ).app (op V)).hom s = reduce m φ V (Polynomial.C s) := by
  funext Z
  rw [reduce_apply, Polynomial.map_C, AdjoinRoot.mk_C]
  rfl

private theorem pred_mul_tV (V : X.Opens) (s : ToType ((rationalFunctionsPresheaf X).obj (op V))) :
    reduce m φ V (Polynomial.monomial (m - 1) (s * secOf V φ⁻¹)) * tV m φ V =
      ((ofRationalFunctions m φ).app (op V)).hom s := by
  unfold tV
  rw [reduce_monomial_mul, Nat.sub_add_cancel (NeZero.pos m),
    reduce_monomial_of_le m φ (le_refl m), Nat.sub_self, ofRat_eq_reduce_C,
    ← Polynomial.monomial_zero_left]
  congr 2
  funext Z
  change (φ : RationalFunctions X) Z.1 * (s Z * ((φ⁻¹ : (RationalFunctions X)ˣ) :
    RationalFunctions X) Z.1 * 1) = s Z
  have := congrArg (fun f : RationalFunctions X => f Z.1) φ.mul_inv
  simp only [Units.val_mul, Pi.mul_apply, Units.val_one, Pi.one_apply] at this
  calc _ = s Z * ((φ : RationalFunctions X) Z.1 * ((φ⁻¹ : (RationalFunctions X)ˣ) :
        RationalFunctions X) Z.1) := by ring
    _ = s Z := by rw [this, mul_one]

include hgen in
/-- Generators of the pull-back of `𝒪_X(D)` are `ψ`-multiples of regular functions locally. -/
private theorem exists_pull_eq_mul_psi
    (hmaps : MMP.Flips.MapsGenericPointsToGenericPoints (toBase m D h.ge))
    {W0 : X.Opens} (hW0 : IsAffineOpen W0) (hηW0 : genericPoint X ∈ W0)
    {V : X.Opens} {s : ToType ((rationalFunctionsPresheaf X).obj (op V))}
    (hs : s ∈ D.divisorialSubmodule V) {W3 : (cover m D h.ge).Opens}
    (hW3 : W3 ≤ toBase m D h.ge ⁻¹ᵁ V) {x' : cover m D h.ge} (hx' : x' ∈ W3) :
    ∃ (W5 : (cover m D h.ge).Opens) (i : W5 ⟶ W3), x' ∈ W5 ∧
      ∃ a : Γ(cover m D h.ge, W5),
        ((rationalFunctionsPresheaf (cover m D h.ge)).map i.op).hom
            (MMP.Flips.rationalFunctionsPullbackHom hmaps hW3 s) =
          ((toRationalFunctionsPresheaf (cover m D h.ge)).app (op W5)).hom a *
            psiOn m D h hgen hW0 hηW0 W5 := by
  have hpx : toBase m D h.ge x' ∈ V := hW3 hx'
  obtain ⟨V0, hV0, hxV0, hsub⟩ := exists_isAffineOpen_mem_and_subset (U := V)
    (x := toBase m D h.ge x') hpx
  have hηV0 : genericPoint X ∈ V0 :=
    (genericPoint_specializes _).mem_open V0.isOpen hxV0
  set s0 := (rationalFunctionsPresheaf X).map (homOfLE hsub).op s with hs0def
  have hs0 : s0 ∈ D.divisorialSubmodule V0 := Divisor.IsDivisorialSection.map _ hs
  have hρmem := reduce_monomial_pred_mem_carrier m D h hs0
  set ρ : (localSubalgebra m D h.ge).carrier V0 :=
    ⟨reduce m φ V0 (Polynomial.monomial (m - 1) (s0 * secOf V0 φ⁻¹)), hρmem⟩ with hρdef
  have hρ : (ρ : (ambient m φ).obj (op V0)) * tV m φ V0 =
      ((ofRationalFunctions m φ).app (op V0)).hom s0 := pred_mul_tV m (φ := φ) V0 s0
  refine ⟨W3 ⊓ toBase m D h.ge ⁻¹ᵁ V0, homOfLE inf_le_left, ⟨hx', hxV0⟩,
    (cover m D h.ge).presheaf.map (homOfLE (inf_le_right :
      W3 ⊓ toBase m D h.ge ⁻¹ᵁ V0 ≤ toBase m D h.ge ⁻¹ᵁ V0)).op (psiEquiv m D h.ge hV0 ρ), ?_⟩
  funext Z'
  have e := pullback_eq_mul_psi m D h hgen hmaps hW0 hηW0 hV0 hηV0 ρ s0 hρ Z'.1 Z'.2.2
  change MMP.Flips.rationalFunctionsPullbackHom hmaps hW3 s ⟨Z'.1, _⟩ = _
  have e1 : MMP.Flips.rationalFunctionsPullbackHom hmaps hW3 s ⟨Z'.1, Z'.2.1⟩ =
      MMP.Flips.rationalFunctionsPullbackHom hmaps (le_refl (toBase m D h.ge ⁻¹ᵁ V0)) s0
        ⟨Z'.1, Z'.2.2⟩ := rfl
  rw [e1, e]
  refine congrArg (· * psiFun m D h hgen hW0 hηW0 Z'.1) ?_
  exact (TopCat.Presheaf.germ_res_apply (cover m D h.ge).presheaf
    (homOfLE (inf_le_right : W3 ⊓ toBase m D h.ge ⁻¹ᵁ V0 ≤ toBase m D h.ge ⁻¹ᵁ V0))
    (componentGenericPoint (cover m D h.ge) Z'.1) Z'.2 (psiEquiv m D h.ge hV0 ρ)).symm

end Dictionary

section S2Unit

/-- A normal locally Noetherian scheme satisfies Serre's condition `S₂`. -/
private lemma satisfiesS2_of_isNormal' (Y : Scheme.{u}) [IsLocallyNoetherian Y] [IsNormal Y] :
    MMP.Flips.SatisfiesS2 Y :=
  MMP.Flips.satisfiesS2_iff_forall_min_le_depth.mpr
    ((isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one Y).mp inferInstance).1

/-- On a normal locally Noetherian scheme, `𝒪 ⊆ 𝒦` is saturated. -/
private lemma isSaturated_unit (Y : Scheme.{u}) [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] : (MMP.Flips.RationalFunctionsSubmodule.unit Y).IsSaturated := by
  obtain ⟨L, hL⟩ := (MMP.Flips.exists_weilDivisorialSubsheaf_unit_iff_satisfiesS2).mpr
    (satisfiesS2_of_isNormal' Y)
  have := L.isSaturated
  rwa [hL] at this

private theorem structureStalk_germ {Y : Scheme.{u}} {W : Y.Opens} {x : Y} (hx : x ∈ W)
    (r : Γ(Y, W)) :
    (MMP.Flips.structureStalkToRationalFunctionsStalk Y x).hom (Y.presheaf.germ W x hx r) =
      (rationalFunctionsPresheaf Y).germ W x hx ((toRationalFunctionsPresheaf Y).app (op W) r) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply W x hx (toRationalFunctionsPresheaf Y) r

end S2Unit

section Assembly

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (m : ℕ) [NeZero m] (D : Divisor X) {φ : (RationalFunctions X)ˣ}
  (h : principalDivisor φ + m • D = 0)
  [IsFinite (toBase m D h.ge)] [IsReduced (cover m D h.ge)]
  (hgen : ∀ Z' : irreducibleComponents (cover m D h.ge),
    toBase m D h.ge (componentGenericPoint (cover m D h.ge) Z') = genericPoint X)

/-- The restriction of `t⁻¹` to an open of `X'`. -/
private noncomputable def psiInvOn {W0 : X.Opens} (hW0 : IsAffineOpen W0)
    (hηW0 : genericPoint X ∈ W0) (U' : (cover m D h.ge).Opens) :
    ToType ((rationalFunctionsPresheaf (cover m D h.ge)).obj (op U')) :=
  fun Z => psiInvFun m D h hgen hW0 hηW0 Z.1

private theorem psiOn_mul_psiInvOn {W0 : X.Opens} (hW0 : IsAffineOpen W0)
    (hηW0 : genericPoint X ∈ W0) (U' : (cover m D h.ge).Opens) :
    psiOn m D h hgen hW0 hηW0 U' * psiInvOn m D h hgen hW0 hηW0 U' = 1 := by
  funext Z
  exact congrFun (psiFun_mul_psiInvFun m D h hgen hW0 hηW0) Z.1

include hgen in
private theorem sections_weilPullback_le
    {k : Type u} [Field k] {sX : X ⟶ Spec (.of k)} {sX' : cover m D h.ge ⟶ Spec (.of k)}
    (hset : MMP.Flips.IsWeilPullbackSetting k sX sX' (toBase m D h.ge))
    [IsNormal (cover m D h.ge)] [IsLocallyNoetherian (cover m D h.ge)]
    [CompactSpace (cover m D h.ge)]
    {W0 : X.Opens} (hW0 : IsAffineOpen W0) (hηW0 : genericPoint X ∈ W0)
    (U' : (cover m D h.ge).Opens) :
    (MMP.Flips.weilPullback hset (weilOfDivisor D)).sections U' ≤
      Submodule.span Γ(cover m D h.ge, U') {psiOn m D h hgen hW0 hηW0 U'} := by
  intro f hf
  have hmaps := hset.mapsGenericPoints
  have hstalk : ∀ (η' : cover m D h.ge) (hη' : η' ∈ U'), Order.coheight η' ≤ 1 →
      ∃ c : (cover m D h.ge).presheaf.stalk η',
        (rationalFunctionsPresheaf (cover m D h.ge)).germ U' η' hη' f = (rationalFunctionsPresheaf
            (cover m D h.ge)).germ U' η' hη' (psiOn m D h hgen hW0 hηW0 U') *
          (MMP.Flips.structureStalkToRationalFunctionsStalk (cover m D h.ge) η').hom c := by
    intro η' hη' hc
    have h1 := hf η' hη' hc
    obtain ⟨W2, i2, hη2, h2⟩ := ((MMP.Flips.weilPullbackImage hmaps
      (weilOfDivisor D).toRationalFunctionsSubmodule).germ_mem_stalkSet_iff hη' f).mp h1
    obtain ⟨W3, i3, hη3, h3⟩ := (MMP.Flips.RationalFunctionsSubmodule.mem_localClosure_iff.mp h2) η'
        hη2
    have hψ : ∀ (W : (cover m D h.ge).Opens) (i : W ⟶ U') (hW : η' ∈ W),
        (rationalFunctionsPresheaf (cover m D h.ge)).germ W η' hW (psiOn m D h hgen hW0 hηW0 W) =
          (rationalFunctionsPresheaf (cover m D h.ge)).germ U' η' hη' (psiOn m D h hgen hW0 hηW0
              U') := fun W i hW =>
      TopCat.Presheaf.germ_res_apply (rationalFunctionsPresheaf (cover m D h.ge)) i η' hW
        (psiOn m D h hgen hW0 hηW0 U')
    have hQ : ∀ y ∈ MMP.Flips.weilPullbackGenerators hmaps
        (weilOfDivisor D).toRationalFunctionsSubmodule W3,
        ∃ c : (cover m D h.ge).presheaf.stalk η',
          (rationalFunctionsPresheaf (cover m D h.ge)).germ W3 η' hη3 y = (rationalFunctionsPresheaf
              (cover m D h.ge)).germ W3 η' hη3 (psiOn m D h hgen hW0 hηW0 W3) *
            (MMP.Flips.structureStalkToRationalFunctionsStalk (cover m D h.ge) η').hom c := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨V, hUV, s, hs, rfl⟩ := ht
        obtain ⟨W5, i5, hx5, a, ha⟩ := exists_pull_eq_mul_psi m D h hgen hmaps hW0 hηW0 hs hUV hη3
        refine ⟨(cover m D h.ge).presheaf.germ W5 η' hx5 a, ?_⟩
        rw [structureStalk_germ hx5 a, ← TopCat.Presheaf.germ_res_apply (rationalFunctionsPresheaf
            (cover m D h.ge)) i5 η' hx5
          (MMP.Flips.rationalFunctionsPullbackHom hmaps hUV s), ha,
          map_mul, mul_comm]
        congr 1
        exact TopCat.Presheaf.germ_res_apply (rationalFunctionsPresheaf (cover m D h.ge)) i5 η' hx5
          (psiOn m D h hgen hW0 hηW0 W3)
      | zero => exact ⟨0, by rw [map_zero, map_zero, mul_zero]⟩
      | add a b _ _ ha hb =>
        obtain ⟨c1, hc1⟩ := ha
        obtain ⟨c2, hc2⟩ := hb
        exact ⟨c1 + c2, by rw [map_add, hc1, hc2, map_add, mul_add]⟩
      | smul r a _ ha =>
        obtain ⟨c1, hc1⟩ := ha
        refine ⟨(cover m D h.ge).presheaf.germ W3 η' hη3 r * c1, ?_⟩
        rw [Algebra.smul_def, map_mul, hc1, map_mul, structureStalk_germ hη3 r]
        change (rationalFunctionsPresheaf (cover m D h.ge)).germ W3 η' hη3
            ((toRationalFunctionsPresheaf _).app _ r) * _ = _
        ring
    obtain ⟨c, hc'⟩ := hQ _ h3
    refine ⟨c, ?_⟩
    have e1 : (rationalFunctionsPresheaf (cover m D h.ge)).germ W3 η' hη3
        ((rationalFunctionsPresheaf (cover m D h.ge)).map i3.op ((rationalFunctionsPresheaf (cover m
            D h.ge)).map i2.op f)) = (rationalFunctionsPresheaf (cover m D h.ge)).germ U' η' hη'
                f := by
      rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    rw [← e1, hc', hψ W3 (i3 ≫ i2) hη3]
  have hψψ := psiOn_mul_psiInvOn m D h hgen hW0 hηW0 U'
  have hsat : psiInvOn m D h hgen hW0 hηW0 U' * f ∈
      (MMP.Flips.RationalFunctionsSubmodule.unit (cover m D h.ge)).saturation.sections U' := by
    intro η' hη' hc
    obtain ⟨c, hc'⟩ := hstalk η' hη' hc
    rw [MMP.Flips.RationalFunctionsSubmodule.stalkSet_unit]
    refine ⟨c, ?_⟩
    rw [map_mul, hc', ← mul_assoc, ← map_mul, mul_comm (psiInvOn m D h hgen hW0 hηW0 U'),
      hψψ, map_one, one_mul]
  have hsatU := isSaturated_unit (cover m D h.ge)
  have hmem : psiInvOn m D h hgen hW0 hηW0 U' * f ∈
      (MMP.Flips.RationalFunctionsSubmodule.unit (cover m D h.ge)).sections U' := by
    rw [show (MMP.Flips.RationalFunctionsSubmodule.unit (cover m D h.ge)).sections U' =
      (MMP.Flips.RationalFunctionsSubmodule.unit (cover m D h.ge)).saturation.sections U' from
        congrArg (fun F => F.sections U') hsatU]
    exact hsat
  obtain ⟨r, hr⟩ := MMP.Flips.exists_toRationalFunctionsPresheaf_app_eq_of_mem_unit hmem
  refine Submodule.mem_span_singleton.mpr ⟨r, ?_⟩
  have hf2 : f = psiOn m D h hgen hW0 hηW0 U' * (psiInvOn m D h hgen hW0 hηW0 U' * f) := by
    rw [← mul_assoc, hψψ, one_mul]
  conv_rhs => rw [hf2, ← hr]
  funext Z
  rw [rationalFunctions_smul_apply]
  exact mul_comm _ _

private theorem reduce_monomial_one_eq {V : X.Opens}
    (c : ToType ((rationalFunctionsPresheaf X).obj (op V))) :
    reduce m φ V (Polynomial.monomial 1 c) =
      ((ofRationalFunctions m φ).app (op V)).hom c * tV m φ V := by
  rw [ofRat_eq_reduce_C]
  unfold tV
  rw [← map_mul, Polynomial.C_mul_monomial, mul_one]

include hgen in
private theorem psi_mem_sections_weilPullback
    {k : Type u} [Field k] {sX : X ⟶ Spec (.of k)} {sX' : cover m D h.ge ⟶ Spec (.of k)}
    (hset : MMP.Flips.IsWeilPullbackSetting k sX sX' (toBase m D h.ge))
    (hcoh : ∀ x' : cover m D h.ge, Order.coheight x' ≤ 1 →
      Order.coheight (toBase m D h.ge x') ≤ 1)
    {W0 : X.Opens} (hW0 : IsAffineOpen W0) (hηW0 : genericPoint X ∈ W0)
    (U' : (cover m D h.ge).Opens) :
    psiOn m D h hgen hW0 hηW0 U' ∈ (MMP.Flips.weilPullback hset (weilOfDivisor D)).sections U' := by
  intro η' hη' hc
  have hmaps := hset.mapsGenericPoints
  obtain ⟨V, hV, hpV, g, hg⟩ := exists_affine_isLocalEquation_of_coheight_le_one D (hcoh η' hc)
  have hηV : genericPoint X ∈ V := (genericPoint_specializes _).mem_open V.isOpen hpV
  have hη'W : η' ∈ U' ⊓ toBase m D h.ge ⁻¹ᵁ V := ⟨hη', hpV⟩
  refine ((MMP.Flips.weilPullbackImage hmaps
    (weilOfDivisor D).toRationalFunctionsSubmodule).germ_mem_stalkSet_iff hη' _).mpr
    ⟨U' ⊓ toBase m D h.ge ⁻¹ᵁ V, homOfLE inf_le_left, hη'W, ?_⟩
  refine MMP.Flips.RationalFunctionsSubmodule.mem_localClosure_iff.mpr fun x hx =>
    ⟨U' ⊓ toBase m D h.ge ⁻¹ᵁ V, 𝟙 _, hx, ?_⟩
  obtain ⟨a, b, ha, hab⟩ : ∃ a b : (localSubalgebra m D h.ge).carrier V,
      (a : (ambient m φ).obj (op V)) = reduce m φ V (Polynomial.monomial 1 (secOf V g)) ∧
        a * b = 1 := isUnit_reduce_monomial_one m D h hg
  set W := U' ⊓ toBase m D h.ge ⁻¹ᵁ V with hW
  have hUV : W ≤ toBase m D h.ge ⁻¹ᵁ V := inf_le_right
  -- the section `g⁻¹` of `𝒪_X(D)`
  have hs : secOf V g⁻¹ ∈ D.divisorialSubmodule V := by
    refine (isDivisorialSection_iff_mul (le_refl V) hg _).mpr ?_
    have h1 : secOf V g * secOf V g⁻¹ = 1 := (secUnit V g).val_inv
    rw [h1]
    exact Divisor.IsDivisorialSection.one le_rfl V
  -- `b t = g⁻¹`
  have hbt : (b : (ambient m φ).obj (op V)) * tV m φ V =
      ((ofRationalFunctions m φ).app (op V)).hom (secOf V g⁻¹) := by
    have h1 : ((ofRationalFunctions m φ).app (op V)).hom (secOf V g) *
        ((ofRationalFunctions m φ).app (op V)).hom (secOf V g⁻¹) = 1 := by
      have h0 : secOf V g * secOf V g⁻¹ = 1 := (secUnit V g).val_inv
      rw [← map_mul, h0, map_one]
    have h2 : ((ofRationalFunctions m φ).app (op V)).hom (secOf V g) * tV m φ V * b = 1 := by
      have h3 : (a : (ambient m φ).obj (op V)) * b = 1 := congrArg Subtype.val hab
      rwa [ha, reduce_monomial_one_eq] at h3
    calc (b : (ambient m φ).obj (op V)) * tV m φ V
        = b * tV m φ V * (((ofRationalFunctions m φ).app (op V)).hom (secOf V g) *
            ((ofRationalFunctions m φ).app (op V)).hom (secOf V g⁻¹)) := by rw [h1, mul_one]
      _ = (((ofRationalFunctions m φ).app (op V)).hom (secOf V g) * tV m φ V * b) *
            ((ofRationalFunctions m φ).app (op V)).hom (secOf V g⁻¹) := by ring
      _ = _ := by rw [h2, one_mul]
  set c : Γ(cover m D h.ge, W) := (cover m D h.ge).presheaf.map (homOfLE hUV).op
    (psiEquiv m D h.ge hV a) with hc_def
  have key : (rationalFunctionsPresheaf (cover m D h.ge)).map (𝟙 W).op
      ((rationalFunctionsPresheaf (cover m D h.ge)).map (homOfLE (inf_le_left : W ≤ U')).op
        (psiOn m D h hgen hW0 hηW0 U')) =
      c • (show ToType ((rationalFunctionsPresheaf (cover m D h.ge)).obj (op W)) from
        MMP.Flips.rationalFunctionsPullbackHom hmaps hUV (secOf V g⁻¹)) := by
    funext Z'
    rw [rationalFunctions_smul_apply]
    have e := pullback_eq_mul_psi m D h hgen hmaps hW0 hηW0 hV hηV b (secOf V g⁻¹) hbt Z'.1
      (hUV Z'.2)
    have e1 : MMP.Flips.rationalFunctionsPullbackHom hmaps hUV (secOf V g⁻¹) Z' =
        MMP.Flips.rationalFunctionsPullbackHom hmaps (le_refl (toBase m D h.ge ⁻¹ᵁ V))
          (secOf V g⁻¹) ⟨Z'.1, hUV Z'.2⟩ := rfl
    have e2 : (cover m D h.ge).presheaf.germ W (componentGenericPoint (cover m D h.ge) Z'.1) Z'.2 c
        =
        (cover m D h.ge).presheaf.germ (toBase m D h.ge ⁻¹ᵁ V)
          (componentGenericPoint (cover m D h.ge) Z'.1) (hUV Z'.2) (psiEquiv m D h.ge hV a) :=
      TopCat.Presheaf.germ_res_apply (cover m D h.ge).presheaf (homOfLE hUV) _ Z'.2 _
    have hab2 : (cover m D h.ge).presheaf.germ (toBase m D h.ge ⁻¹ᵁ V)
          (componentGenericPoint (cover m D h.ge) Z'.1) (hUV Z'.2) (psiEquiv m D h.ge hV a) *
        (cover m D h.ge).presheaf.germ (toBase m D h.ge ⁻¹ᵁ V)
          (componentGenericPoint (cover m D h.ge) Z'.1) (hUV Z'.2) (psiEquiv m D h.ge hV b) = 1 :=
              by
      rw [← map_mul, ← map_mul, hab, map_one, map_one]
    rw [e1, e, e2]
    change psiFun m D h hgen hW0 hηW0 Z'.1 = _ * (_ * _)
    rw [← mul_assoc]
    change _ = ((cover m D h.ge).presheaf.germ (toBase m D h.ge ⁻¹ᵁ V)
          (componentGenericPoint (cover m D h.ge) Z'.1) (hUV Z'.2) (psiEquiv m D h.ge hV a) *
        (cover m D h.ge).presheaf.germ (toBase m D h.ge ⁻¹ᵁ V)
          (componentGenericPoint (cover m D h.ge) Z'.1) (hUV Z'.2) (psiEquiv m D h.ge hV b)) * _
    rw [hab2, one_mul]
  rw [key]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨V, hUV, secOf V g⁻¹, hs, rfl⟩)

end Assembly

variable (k : Type u) [Field k] [CharZero k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X]
    (m : ℕ) [NeZero m] (D : Divisor X) (φ : (RationalFunctions X)ˣ)
    (h : principalDivisor φ + m • D = 0)

include k h in
/-- Finiteness: `𝒜` is a finite direct sum of coherent divisorial sheaves. -/
private theorem isFinite_toBase : IsFinite (toBase m D h.ge) := by
  haveI := (situation m D h.ge).isQuasicoherent
  have : IsAffineHom (toBase m D h.ge) :=
    Stacks.AffineAlgebraEquivalence.isAffineHom_relativeSpecToBase (situation m D h.ge).algebra
  refine ⟨fun U hU => ?_⟩
  have hI : (((Stacks.RelativeSpec.universalAlgebraMap (situation m D h.ge)).right.app
      (op U)).hom).Finite := by
    have := Stacks.RelativeSpec.isIso_universalAlgebraMap_app (situation m D h.ge) ⟨U, hU⟩
    exact RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso
        ((Stacks.RelativeSpec.universalAlgebraMap (situation m D h.ge)).right.app (op U))).2
  rw [Stacks.RelativeSpec.toBase_app]
  exact hI.comp (finite_algebraMap_carrier m D hU h.ge)

/-- `m` is invertible in every stalk of a scheme over a field of characteristic zero. -/
private theorem isUnit_natCast_stalk (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] (m : ℕ) [NeZero m] (x : X) :
    IsUnit (m : X.presheaf.stalk x) := by
  let ψ : k →+* X.presheaf.stalk x :=
    ((X.presheaf.germ ⊤ x trivial).hom.comp (X ↘ Spec (.of k)).appTop.hom).comp
      (Scheme.ΓSpecIso (.of k)).inv.hom
  have : (m : X.presheaf.stalk x) = ψ (m : k) := by simp
  rw [this]
  exact (IsUnit.mk0 (m : k) (Nat.cast_ne_zero.mpr (NeZero.ne m))).map ψ

include k h in
/-- Normality of `X'`: the local algebra at every height-one prime is `R_P[t]/(tᵐ - u)` with
`u` a unit, and `𝒜(R)` is the intersection of these. -/
private theorem isNormal_cover : IsNormal (cover m D h.ge) := by
  have hm := isUnit_natCast_stalk k X m
  haveI := (situation m D h.ge).isQuasicoherent
  haveI : IsAffineHom (toBase m D h.ge) :=
    Stacks.AffineAlgebraEquivalence.isAffineHom_relativeSpecToBase (situation m D h.ge).algebra
  refine ((isNormal_tfae (cover m D h.ge)).out 3 1).mp ?_
  refine ⟨X.affineOpens, fun U => ⟨toBase m D h.ge ⁻¹ᵁ U.1, U.2.preimage _⟩, ?_, fun U => ?_⟩
  · rw [IsOpenCover, eq_top_iff]
    intro x _
    have hx : (toBase m D h.ge) x ∈ ⨆ U : X.affineOpens, (U : X.Opens) := by
      rw [iSup_affineOpens_eq_top X]; trivial
    obtain ⟨U, hU⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨U, hU⟩
  · by_cases hη : genericPoint X ∈ U.1
    · exact IsNormalRing.congr (psiEquiv m D h.ge U.2) (isNormalRing_carrier m D hm h U.2 hη)
    · have hU0 : U.1 = ⊥ := by
        by_contra hne
        obtain ⟨y, hy⟩ := (Opens.ne_bot_iff_nonempty U.1).mp hne
        exact hη (((genericPoint_spec X).specializes (Set.mem_univ y)).mem_open U.1.isOpen hy)
      have hV : (toBase m D h.ge) ⁻¹ᵁ U.1 = ⊥ := by rw [hU0]; exact Scheme.Hom.preimage_bot _
      have : Subsingleton Γ(cover m D h.ge, (toBase m D h.ge) ⁻¹ᵁ U.1) := by
        rw [hV]; infer_instance
      intro q hq
      exact absurd (Subsingleton.elim q ⊤) hq.ne_top

include k h in
/-- The generic algebra is `K(X)[e]/(eᵐ - φ)`, of dimension `m`. -/
private theorem finrank_toBase_genericPoint :
    (toBase m D h.ge).finrank (genericPoint X) = m := by
  rw [MMP.Mori.finrank_eq_appTop_finrank_chart]
  exact finrank_pullback_snd_chart m D h.ge
    (X.affineOpenCover.f (X.affineOpenCover.idx (genericPoint X)))
    (X.affineOpenCover.covers (genericPoint X)).choose
    (X.affineOpenCover.covers (genericPoint X)).choose_spec

/-- The coefficients of a regular function `r` in the basis `1, t, …, tᵐ⁻¹`: `r` itself in degree
`0`, and `0` in every other degree. -/
private theorem coeff_structureMap (U : X.Opens) (r : Γ(X, U)) (n : ℕ) :
    coeff m φ U n (((structureMap m φ).app (op U)).hom r) =
      if n = 0 then (toRationalFunctionsPresheaf X).app (op U) r else 0 := by
  have h1 : ((structureMap m φ).app (op U)).hom r =
      ((structureMap m φ).app (op U)).hom r * reduce m φ U (Polynomial.monomial 0 1) := by
    rw [Polynomial.monomial_zero_one, map_one, mul_one]
  rw [h1, coeff_structureMap_mul, coeff_reduce_monomial]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [if_pos (Nat.zero_mod m), if_pos rfl, Nat.zero_div, pow_zero, mul_one]
    funext Z
    rw [rationalFunctions_smul_apply, toRationalFunctionsPresheaf_app_apply]
    exact mul_one _
  · rw [if_neg (by rw [Nat.zero_mod]; exact hn.symm), if_neg hn, smul_zero]

/-- The universal map `𝒜(U) → Γ(p⁻¹U, 𝒪_{X'})` is injective (it is an isomorphism). -/
private theorem injective_universalAlgebraMap_app (U : X.Opens) :
    Function.Injective
      ((Stacks.RelativeSpec.universalAlgebraMap (situation m D h.ge)).right.app (op U)).hom := by
  haveI := (situation m D h.ge).isQuasicoherent
  let e := Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso (situation m D h.ge).algebra
  refine Function.LeftInverse.injective (g := (e.hom.right.hom.app (op U)).hom) fun x => ?_
  have := congrArg (fun f => ((f.right.hom).app (op U)).hom x) e.inv_hom_id
  exact this

/-- `p^♯ = (universal map) ∘ (structure map of 𝒜)` on sections. -/
private theorem toBase_app_apply (U : X.Opens) (r : Γ(X, U)) :
    ((toBase m D h.ge).app U).hom r =
      ((Stacks.RelativeSpec.universalAlgebraMap (situation m D h.ge)).right.app (op U)).hom
        ((localSubalgebra m D h.ge).algebraMap U r) := by
  rw [Stacks.RelativeSpec.toBase_app]
  rfl

/-- `p^♯` is injective on every open: `𝒪_X → 𝒜` is injective (the degree-`0` coefficient of `r`
is `r`, and `𝒪_X → 𝒦_X` is injective), and `𝒜 → p_*𝒪_{X'}` is an isomorphism. -/
private theorem injective_toBase_app (U : X.Opens) :
    Function.Injective ((toBase m D h.ge).app U).hom := by
  intro r r' hr
  rw [toBase_app_apply X m D φ h, toBase_app_apply X m D φ h] at hr
  have h0 := injective_universalAlgebraMap_app X m D φ h U hr
  have h1 : coeff m φ U 0 ((localSubalgebra m D h.ge).algebraMap U r).1 =
      coeff m φ U 0 ((localSubalgebra m D h.ge).algebraMap U r').1 := by rw [h0]
  rw [LocalSubalgebra.coe_algebraMap, LocalSubalgebra.coe_algebraMap, coeff_structureMap,
    coeff_structureMap, if_pos rfl, if_pos rfl] at h1
  exact toRationalFunctionsPresheaf_app_injective U h1

include k h in
/-- Surjectivity: every component of `X'` dominates `X` and `p` is closed. -/
private theorem surjective_toBase : Surjective (toBase m D h.ge) := by
  have := isFinite_toBase k X m D φ h
  have hclosed : IsClosed (Set.range (toBase m D h.ge)) :=
    (toBase m D h.ge).isClosedMap.isClosed_range
  have hη : genericPoint X ∈ Set.range (toBase m D h.ge) := by
    by_contra hη
    let V : X.Opens := ⟨(Set.range (toBase m D h.ge))ᶜ, hclosed.isOpen_compl⟩
    have : Nonempty V := ⟨⟨_, hη⟩⟩
    have hV : (toBase m D h.ge) ⁻¹ᵁ V = ⊥ := by
      ext x
      exact ⟨fun hx => absurd ⟨x, rfl⟩ hx, fun hx => (show False from hx).elim⟩
    have : Subsingleton Γ(cover m D h.ge, (toBase m D h.ge) ⁻¹ᵁ V) := by
      rw [hV]
      infer_instance
    exact one_ne_zero (injective_toBase_app X m D φ h V (Subsingleton.elim _ _))
  refine ⟨fun x => ?_⟩
  have hx : x ∈ closure {genericPoint X} := by
    rw [(genericPoint_spec X).def]
    trivial
  exact hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη) hx

/-- `m` is invertible in every ring of sections of a scheme over a field of characteristic zero. -/
private theorem isUnit_natCast_sections (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] (m : ℕ) [NeZero m] (W : X.Opens) :
    IsUnit (m : Γ(X, W)) := by
  let ψ : k →+* Γ(X, W) :=
    ((X ↘ Spec (.of k)).appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have : (m : Γ(X, W)) = ψ (m : k) := by simp
  rw [this]
  exact (IsUnit.mk0 (m : k) (Nat.cast_ne_zero.mpr (NeZero.ne m))).map ψ

/-- A section `v` whose image in `𝒦_X` has trivial divisor on `W` is a unit of `Γ(X, W)`. -/
private theorem isUnit_of_isLocalEquation_zero {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {W : X.Opens} {ψ0 : (RationalFunctions X)ˣ}
    (hloc : (0 : Divisor X).IsLocalEquation W ψ0) {v : Γ(X, W)}
    (hv : (toRationalFunctionsPresheaf X).app (op W) v = phiOn ψ0 W) : IsUnit v := by
  have h1 : (-(0 : Divisor X)).IsLocalEquation W ψ0⁻¹ := hloc.neg
  rw [neg_zero] at h1
  have h2 : (0 : Divisor X).IsDivisorialSection W (phiOn ψ0⁻¹ W) := fun E hE => by
    refine Or.inr ?_
    change _ ≤ E.valuation (((ψ0⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) E.component)
    rw [PrimeDivisor.valuation_component, ← h1 E hE]
    simp
  obtain ⟨s, hs⟩ := h2.exists_eq
  refine IsUnit.of_mul_eq_one s (a := v) (toRationalFunctionsPresheaf_app_injective W ?_)
  rw [map_mul, hv, hs, map_one]
  funext Z
  change ((ψ0 : RationalFunctions X) Z.1) * ((ψ0⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)
      Z.1 = 1
  have := congrFun (congrArg Units.val (mul_inv_cancel ψ0)) Z.1
  rw [Units.val_mul, Pi.mul_apply] at this
  exact this

/-- A divisor whose restriction to an open `V` is Cartier has a local equation near every point
of `V`. -/
private theorem exists_isLocalEquation_of_isCartier_restrictOpen {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {D : Divisor Y} {V : Y.Opens}
    (h : Divisor.IsCartier (D.restrictOpen V)) {x : Y} (hx : x ∈ V) :
    ∃ W : Y.Opens, x ∈ W ∧ ∃ φ : (RationalFunctions Y)ˣ, D.IsLocalEquation W φ := by
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  have : IsDominant V.ι := Opens.isDominant_ι (V.isOpen.dense ⟨x, hx⟩)
  obtain ⟨W, hxW, φ', hφ'⟩ := h ⟨x, hx⟩
  obtain ⟨g', hg', hφg'⟩ := MMP.Positivity.exists_ord_eq_of_units φ'
  obtain ⟨g, rfl⟩ := (functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤
    ⟨⟨x, hx⟩, trivial⟩).2 g'
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (g := g)
    (fun h0 => hg' (by rw [h0, map_zero]))
  refine ⟨V.ι ''ᵁ W, ⟨⟨x, hx⟩, hxW, rfl⟩, φ, fun E hE => ?_⟩
  have hEW : E.genericPoint ∈ V.ι ''ᵁ W := (E.genericPoint_mem_iff _).2 hE
  obtain ⟨y, hyW, hy⟩ := hEW
  obtain ⟨E₀, rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff V.ι E).2 ⟨y, hy⟩
  have hgp : V.ι E₀.genericPoint = V.ι y :=
    (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm.trans hy.symm
  have hE₀ : (E₀.support ∩ (W : Set V)).Nonempty := by
    rw [← PrimeDivisor.genericPoint_mem_iff]
    have : E₀.genericPoint = y := V.ι.isOpenEmbedding.injective hgp
    change E₀.genericPoint ∈ W
    rw [this]
    exact hyW
  have h1 := hφ' E₀ hE₀
  rw [DivisorWithCoeffs.coeff_restrictOpen] at h1
  rw [h1, hφg', hφ, MMP.Positivity.ord_functionFieldMap_of_isIso V.ι E₀ _
    (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm]

/-- A divisor with a local equation on `W` has Cartier restriction to `W`. -/
private theorem isCartier_restrictOpen_of_isLocalEquation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {D : Divisor Y} {W : Y.Opens} {g : (RationalFunctions Y)ˣ}
    (hg : D.IsLocalEquation W g) (hne : Nonempty W) : Divisor.IsCartier (D.restrictOpen W) := by
  have : IsDominant W.ι := Opens.isDominant_ι (W.isOpen.dense (by
    obtain ⟨y⟩ := hne; exact ⟨y.1, y.2⟩))
  intro x
  obtain ⟨g', hg', hφg'⟩ := MMP.Positivity.exists_ord_eq_of_units g
  obtain ⟨φ', hφ'⟩ := MMP.Positivity.exists_units_of_ne_zero
    ((map_ne_zero (functionFieldMap W.ι)).2 hg')
  refine ⟨W.ι ⁻¹ᵁ W, x.2, φ', fun E hE => ?_⟩
  · have hP : ((OpenWeilRestriction.primeDivisorMap W.ι E).support ∩ W).Nonempty := by
      rw [← PrimeDivisor.genericPoint_mem_iff]
      exact (congrArg (· ∈ W) (OpenWeilRestriction.genericPoint_primeDivisorMap W.ι E)).mpr
        ((E.genericPoint_mem_iff _).2 hE)
    rw [DivisorWithCoeffs.coeff_restrictOpen, hg _ hP, hφg', hφ',
      MMP.Positivity.ord_functionFieldMap_of_isIso W.ι E _
        (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm]

include k h in
/-- Over an affine open on which `D` has a local equation, the cover is étale. -/
private theorem etale_restrict_of_isLocalEquation {W : X.Opens} (hW : IsAffineOpen W)
    {g : (RationalFunctions X)ˣ} (hg : D.IsLocalEquation W g) :
    Etale (toBase m D h.ge ∣_ W) := by
  haveI := (situation m D h.ge).isQuasicoherent
  haveI : IsAffineHom (toBase m D h.ge) :=
    Stacks.AffineAlgebraEquivalence.isAffineHom_relativeSpecToBase (situation m D h.ge).algebra
  obtain ⟨v, hv, hloc, e, -⟩ := exists_algEquiv_adjoinRoot_of_isLocalEquation m D h.ge hg
  rw [h] at hloc
  have hvu : IsUnit v := isUnit_of_isLocalEquation_zero hloc hv
  letI := ((localSubalgebra m D h.ge).algebraMap W).toAlgebra
  haveI := algebra_etale_adjoinRoot m (isUnit_natCast_sections k X m W) v hvu
  haveI : Algebra.Etale Γ(X, W) ((localSubalgebra m D h.ge).carrier W) := Algebra.Etale.of_equiv e
  have hq : RingHom.Etale ((localSubalgebra m D h.ge).algebraMap W) :=
    RingHom.etale_algebraMap.mpr inferInstance
  have hp : RingHom.Etale ((toBase m D h.ge).appLE W (toBase m D h.ge ⁻¹ᵁ W) le_rfl).hom := by
    have heq : ((toBase m D h.ge).appLE W (toBase m D h.ge ⁻¹ᵁ W) le_rfl).hom =
        (psiEquiv m D h.ge hW).toRingHom.comp ((localSubalgebra m D h.ge).algebraMap W) :=
      RingHom.ext fun r => (psiEquiv_algebraMap m D h.ge hW r).symm
    rw [heq]
    exact RingHom.Etale.stableUnderComposition _ _ hq
      (RingHom.Etale.of_bijective (psiEquiv m D h.ge hW).bijective)
  have key : ∀ (A : X.Opens) (B : (cover m D h.ge).Opens) (hA : A = W)
      (hB : B = toBase m D h.ge ⁻¹ᵁ W) (e : B ≤ toBase m D h.ge ⁻¹ᵁ A),
      RingHom.Etale ((toBase m D h.ge).appLE A B e).hom := by
    rintro A B rfl rfl e
    exact hp
  haveI : IsAffine W.toScheme := hW
  haveI : IsAffine (toBase m D h.ge ⁻¹ᵁ W).toScheme := hW.preimage _
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
  have h3 : (toBase m D h.ge ∣_ W).appLE ⊤ ⊤ le_rfl = (toBase m D h.ge ∣_ W).appTop :=
    Scheme.Hom.appLE_eq_app _
  have h4 := morphismRestrict_appLE (toBase m D h.ge) W ⊤ ⊤ le_rfl
  rw [← h3, h4]
  exact key _ _ W.ι_image_top (toBase m D h.ge ⁻¹ᵁ W).ι_image_top _

include k h in
/-- Étaleness of `p ∣_ U` gives étaleness of `Γ(X, W) → Γ(X', p⁻¹W)` for affine `W ≤ U`. -/
private theorem etale_appLE_of_etale_restrict {U W : X.Opens}
    (hU : Etale (toBase m D h.ge ∣_ U)) (hW : IsAffineOpen W) (hWU : W ≤ U) :
    RingHom.Etale ((toBase m D h.ge).appLE W (toBase m D h.ge ⁻¹ᵁ W) le_rfl).hom := by
  haveI := (situation m D h.ge).isQuasicoherent
  haveI : IsAffineHom (toBase m D h.ge) :=
    Stacks.AffineAlgebraEquivalence.isAffineHom_relativeSpecToBase (situation m D h.ge).algebra
  have hW' : IsAffineOpen (U.ι ⁻¹ᵁ W) :=
    hW.preimage_of_isOpenImmersion U.ι (by rw [Scheme.Opens.opensRange_ι]; exact hWU)
  have hV : IsAffineOpen (toBase m D h.ge ⁻¹ᵁ W) := hW.preimage _
  have hV' : IsAffineOpen ((toBase m D h.ge ⁻¹ᵁ U).ι ⁻¹ᵁ (toBase m D h.ge ⁻¹ᵁ W)) :=
    hV.preimage_of_isOpenImmersion _ (by
      rw [Scheme.Opens.opensRange_ι]
      exact fun x hx => hWU hx)
  have e : (toBase m D h.ge ⁻¹ᵁ U).ι ⁻¹ᵁ (toBase m D h.ge ⁻¹ᵁ W) ≤
      (toBase m D h.ge ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ W) := by
    intro x hx
    have := congrArg (fun f => f.base x) (morphismRestrict_ι (toBase m D h.ge) U)
    change (toBase m D h.ge ∣_ U ≫ U.ι) x ∈ W
    rw [this]
    exact hx
  have h1 := (HasRingHomProperty.iff_appLE (P := @Etale)).mp hU ⟨_, hW'⟩ ⟨_, hV'⟩ e
  rw [morphismRestrict_appLE] at h1
  have key : ∀ (A : X.Opens) (B : (cover m D h.ge).Opens) (hA : A = W)
      (hB : B = toBase m D h.ge ⁻¹ᵁ W) (e : B ≤ toBase m D h.ge ⁻¹ᵁ A),
      RingHom.Etale ((toBase m D h.ge).appLE A B e).hom →
      RingHom.Etale ((toBase m D h.ge).appLE W (toBase m D h.ge ⁻¹ᵁ W) le_rfl).hom := by
    rintro A B rfl rfl e hh
    exact hh
  refine key _ _ ?_ ?_ _ h1
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hWU
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (fun x hx => hWU hx)

include k h in
/-- Étaleness of `p ∣_ U` makes the summand `𝒪_X(-D)(W)` of `𝒜(W)` flat over `Γ(X, W)`. -/
private theorem flat_divisorialSubmodule_neg_of_etale {U W : X.Opens}
    (hU : Etale (toBase m D h.ge ∣_ U)) (hW : IsAffineOpen W) (hWU : W ≤ U) (hm : 1 < m) :
    Module.Flat Γ(X, W) ((-D).divisorialSubmodule W) := by
  have hp := etale_appLE_of_etale_restrict k X m D φ h hU hW hWU
  letI := ((localSubalgebra m D h.ge).algebraMap W).toAlgebra
  have hq : RingHom.Etale ((localSubalgebra m D h.ge).algebraMap W) := by
    have heq : ((localSubalgebra m D h.ge).algebraMap W) =
        (psiEquiv m D h.ge hW).symm.toRingHom.comp
          ((toBase m D h.ge).appLE W (toBase m D h.ge ⁻¹ᵁ W) le_rfl).hom :=
      RingHom.ext fun r => by
        rw [RingHom.comp_apply, ← psiEquiv_algebraMap m D h.ge hW r]
        exact ((psiEquiv m D h.ge hW).symm_apply_apply _).symm
    rw [heq]
    exact RingHom.Etale.stableUnderComposition _ _ hp
      (RingHom.Etale.of_bijective (psiEquiv m D h.ge hW).symm.bijective)
  haveI : Algebra.Etale Γ(X, W) ((localSubalgebra m D h.ge).carrier W) :=
    RingHom.etale_algebraMap.mp hq
  haveI : Module.Flat Γ(X, W) ((localSubalgebra m D h.ge).carrier W) := inferInstance
  letI := (localSubalgebra m D h.ge).moduleSections W
  have e := coeffLinearEquiv m D h.ge (φ := φ) W
  have hflat : Module.Flat Γ(X, W) (∀ i : Fin m, Γ((((i : Fin m) : ℕ) • -D).divisorialSheaf, W)) :=
    Module.Flat.of_linearEquiv e.symm
  have hi : (⟨1, hm⟩ : Fin m).val = 1 := rfl
  haveI : Module.Flat Γ(X, W) Γ((((⟨1, hm⟩ : Fin m) : ℕ) • -D).divisorialSheaf, W) :=
    Module.Flat.of_retract
      (LinearMap.single Γ(X, W) (fun i : Fin m => Γ((((i : Fin m) : ℕ) • -D).divisorialSheaf, W))
        (⟨1, hm⟩ : Fin m))
      (LinearMap.proj (R := Γ(X, W))
        (φ := fun i : Fin m => Γ((((i : Fin m) : ℕ) • -D).divisorialSheaf, W)) (⟨1, hm⟩ : Fin m))
      (by ext x; simp)
  have e1 : (((⟨1, hm⟩ : Fin m) : ℕ) • -D) = -D := one_nsmul _
  generalize hN : (((⟨1, hm⟩ : Fin m) : ℕ) • -D) = N' at *
  subst e1
  exact this

include k h in
/-- `p` does not lower the codimension: a point of `X'` of coheight `≤ 1` lies over a point of `X`
of coheight `≤ 1` (going down for the integral extension `Γ(X, W) → 𝒜(W)`). -/
private theorem coheight_toBase_le_coheight (x' : cover m D h.ge) :
    Order.coheight (toBase m D h.ge x') ≤ Order.coheight x' := by
  haveI := (situation m D h.ge).isQuasicoherent
  haveI : IsAffineHom (toBase m D h.ge) :=
    Stacks.AffineAlgebraEquivalence.isAffineHom_relativeSpecToBase (situation m D h.ge).algebra
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⊤ : X.Opens)) (x := toBase m D h.ge x') trivial
  have hV : IsAffineOpen (toBase m D h.ge ⁻¹ᵁ W) := hW.preimage _
  have hx'V : x' ∈ toBase m D h.ge ⁻¹ᵁ W := hxW
  haveI : Nonempty W := ⟨⟨_, hxW⟩⟩
  have hηW : genericPoint X ∈ W := (genericPoint_specializes _).mem_open W.isOpen hxW
  haveI : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  haveI : IsIntegrallyClosed Γ(X, W) := by
    have hnorm : IsNormal X := inferInstance
    have h2 : ∀ U : X.affineOpens, IsNormalRing Γ(X, U) := ((isNormal_tfae X).out 1 2).mp hnorm
    exact (h2 ⟨W, hW⟩).isIntegrallyClosed
  letI : Algebra Γ(X, W) Γ(cover m D h.ge, toBase m D h.ge ⁻¹ᵁ W) :=
    ((toBase m D h.ge).appLE W (toBase m D h.ge ⁻¹ᵁ W) le_rfl).hom.toAlgebra
  have heq : ((toBase m D h.ge).appLE W (toBase m D h.ge ⁻¹ᵁ W) le_rfl).hom =
      (psiEquiv m D h.ge hW).toRingHom.comp ((localSubalgebra m D h.ge).algebraMap W) :=
    RingHom.ext fun r => (psiEquiv_algebraMap m D h.ge hW r).symm
  haveI : Module.Finite Γ(X, W) Γ(cover m D h.ge, toBase m D h.ge ⁻¹ᵁ W) := by
    have hfin : RingHom.Finite ((toBase m D h.ge).appLE W (toBase m D h.ge ⁻¹ᵁ W) le_rfl).hom := by
      rw [heq]
      exact RingHom.Finite.comp (RingHom.Finite.of_surjective _ (psiEquiv m D h.ge hW).surjective)
        (finite_algebraMap_carrier m D hW h.ge)
    exact RingHom.finite_algebraMap.mp hfin
  haveI : IsNoetherianRing Γ(cover m D h.ge, toBase m D h.ge ⁻¹ᵁ W) :=
    Algebra.FiniteType.isNoetherianRing Γ(X, W) _
  have htf : ∀ r : Γ(X, W), r ≠ 0 → ∀ s : Γ(cover m D h.ge, toBase m D h.ge ⁻¹ᵁ W),
      algebraMap Γ(X, W) _ r * s = 0 → s = 0 := by
    intro r hr s hs
    set c := (psiEquiv m D h.ge hW).symm s with hc
    have h1 : psiEquiv m D h.ge hW (((localSubalgebra m D h.ge).algebraMap W) r * c) = 0 := by
      rw [map_mul, psiEquiv_algebraMap, hc, RingEquiv.apply_symm_apply]
      exact hs
    have h2 : ((localSubalgebra m D h.ge).algebraMap W r) * c = 0 :=
      (psiEquiv m D h.ge hW).injective (by rw [h1, map_zero])
    have h3 : ((((localSubalgebra m D h.ge).algebraMap W r) * c : (localSubalgebra m D h.ge).carrier
        W) :
        (ambient m φ).obj (op W)) = 0 := by rw [h2]; rfl
    have : IsFractionRing Γ(X, W) ((rationalFunctionsPresheaf X).obj (op W)) :=
      isFractionRing_rationalFunctions hW hηW
    have hu : IsUnit (algebraMap Γ(X, W) ((ambient m φ).obj (op W)) r) := by
      rw [IsScalarTower.algebraMap_apply Γ(X, W) ((rationalFunctionsPresheaf X).obj (op W))]
      exact (IsLocalization.map_units ((rationalFunctionsPresheaf X).obj (op W))
        (⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩ : nonZeroDivisors Γ(X, W))).map _
    have hc0 : c = 0 := Subtype.ext (hu.mul_right_eq_zero.mp h3)
    calc s = psiEquiv m D h.ge hW c := by rw [hc, RingEquiv.apply_symm_apply]
      _ = 0 := by rw [hc0, map_zero]
  have key := height_comap_le_of_torsionFree (R := Γ(X, W)) htf
    (hV.primeIdealOf ⟨x', hx'V⟩).asIdeal
  have hP : (hV.primeIdealOf ⟨x', hx'V⟩).asIdeal.comap (algebraMap Γ(X, W) _) =
      (hW.primeIdealOf ⟨toBase m D h.ge x', hxW⟩).asIdeal :=
    congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE W hW _ hV le_rfl hx'V)
  rw [hP] at key
  letI : Algebra Γ(X, W) (X.presheaf.stalk (toBase m D h.ge x')) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨toBase m D h.ge x', hxW⟩
  letI : Algebra Γ(cover m D h.ge, toBase m D h.ge ⁻¹ᵁ W) ((cover m D h.ge).presheaf.stalk x') :=
    TopCat.Presheaf.algebra_section_stalk (cover m D h.ge).presheaf ⟨x', hx'V⟩
  haveI := hW.isLocalization_stalk ⟨toBase m D h.ge x', hxW⟩
  haveI := hV.isLocalization_stalk ⟨x', hx'V⟩
  have e1 := IsLocalization.AtPrime.ringKrullDim_eq_height
    (hW.primeIdealOf ⟨toBase m D h.ge x', hxW⟩).asIdeal
    (X.presheaf.stalk (toBase m D h.ge x'))
  have e2 := IsLocalization.AtPrime.ringKrullDim_eq_height
    (hV.primeIdealOf ⟨x', hx'V⟩).asIdeal ((cover m D h.ge).presheaf.stalk x')
  rw [ringKrullDim_stalk_eq_coheight, WithBot.coe_inj] at e1 e2
  calc Order.coheight (toBase m D h.ge x') = _ := e1
    _ ≤ _ := key
    _ = Order.coheight x' := e2.symm

include k h in
/-- `p` does not lower the codimension: a point of coheight `≤ 1` lies over one of coheight `≤ 1`.
    -/
private theorem coheight_toBase_le {x' : cover m D h.ge} (hx' : Order.coheight x' ≤ 1) :
    Order.coheight (toBase m D h.ge x') ≤ 1 :=
  (coheight_toBase_le_coheight k X m D φ h x').trans hx'

include k h in
/-- `p` is étale near `x` iff `D` is Cartier at `x`. -/
private theorem etale_iff_isCartierAt (x : X) :
    (∃ U : X.Opens, x ∈ U ∧ Etale (toBase m D h.ge ∣_ U)) ↔ MMP.Flips.IsCartierAt D x := by
  constructor
  · rintro ⟨U, hxU, hU⟩
    obtain ⟨V, hxV, g, hg⟩ : ∃ V : X.Opens, x ∈ V ∧ ∃ g : (RationalFunctions X)ˣ,
        D.IsLocalEquation V g := by
      by_cases hm : 1 < m
      · obtain ⟨W, hW, hxW, hsub⟩ := exists_isAffineOpen_mem_and_subset hxU
        haveI := flat_divisorialSubmodule_neg_of_etale k X m D φ h hU hW hsub hm
        exact exists_isLocalEquation_of_flat D hW hxW
      · have hm1 : m = 1 := by have := NeZero.pos m; omega
        subst hm1
        refine ⟨⊤, trivial, φ⁻¹, fun E _ => ?_⟩
        have := congrArg (fun F => F.coeff E) h
        simp only [DivisorWithCoeffs.coeff_add, coeff_principalDivisor, one_smul] at this
        rw [PrimeDivisor.ord_inv]
        have h0 : DivisorWithCoeffs.coeff (0 : Divisor X) E = 0 := rfl
        omega
    exact ⟨V, hxV, isCartier_restrictOpen_of_isLocalEquation hg ⟨⟨x, hxV⟩⟩⟩
  · rintro ⟨V, hxV, hV⟩
    obtain ⟨W, hxW, g, hg⟩ := exists_isLocalEquation_of_isCartier_restrictOpen hV hxV
    obtain ⟨W', hW', hxW', hsub⟩ := exists_isAffineOpen_mem_and_subset hxW
    exact ⟨W', hxW', etale_restrict_of_isLocalEquation k X m D φ h hW' (hg.mono hsub)⟩

include k h in
/-- The cover maps the generic point of every irreducible component to the generic point of `X`. -/
private theorem toBase_componentGenericPoint (Z' : irreducibleComponents (cover m D h.ge)) :
    IsGenericPoint (toBase m D h.ge (componentGenericPoint (cover m D h.ge) Z'))
      (Set.univ : Set X) := by
  have hmax : IsMax (componentGenericPoint (cover m D h.ge) Z') := by
    intro y hy
    have h1 : (componentGenericPoint _ Z') ∈ closure {y} := specializes_iff_mem_closure.mp hy
    have h2 : Z'.1 ⊆ closure {y} := by
      rw [← (isGenericPoint_componentGenericPoint _ Z').def]
      exact closure_minimal (Set.singleton_subset_iff.mpr h1) isClosed_closure
    have h3 : Z'.1 = closure {y} := Z'.2.eq_of_le (isIrreducible_singleton.closure) h2
    refine specializes_iff_mem_closure.mpr ?_
    rw [(isGenericPoint_componentGenericPoint _ Z').def, h3]
    exact subset_closure rfl
  have h1 := coheight_toBase_le_coheight k X m D φ h (componentGenericPoint _ Z')
  rw [Order.coheight_eq_zero.mpr hmax, le_zero_iff, Order.coheight_eq_zero] at h1
  have h2 : toBase m D h.ge (componentGenericPoint _ Z') ≤ genericPoint X :=
    Scheme.le_iff_specializes.mpr ((genericPoint_spec X).specializes (Set.mem_univ _))
  have h3 : toBase m D h.ge (componentGenericPoint _ Z') = genericPoint X :=
    (Specializes.antisymm (Scheme.le_iff_specializes.mp h2)
      (Scheme.le_iff_specializes.mp (h1 h2))).eq.symm
  rw [h3]
  exact genericPoint_spec X

include k h in
/-- The setting of FA 16.3.5 holds for the cyclic cover. -/
private theorem isWeilPullbackSetting :
    MMP.Flips.IsWeilPullbackSetting k (X ↘ Spec (.of k))
      (toBase m D h.ge ≫ X ↘ Spec (.of k)) (toBase m D h.ge) := by
  haveI : IrreducibleSpace X := inferInstance
  have := isFinite_toBase k X m D φ h
  have := isNormal_cover k X m D φ h
  have hdim : ∀ Z ∈ irreducibleComponents (cover m D h.ge),
      topologicalKrullDim Z = topologicalKrullDim (cover m D h.ge) := by
    intro Z hZ
    have hgen := isGenericPoint_componentGenericPoint (cover m D h.ge) ⟨Z, hZ⟩
    have h1 := topologicalKrullDim_closure_image_singleton_eq (toBase m D h.ge)
      (componentGenericPoint (cover m D h.ge) ⟨Z, hZ⟩)
    rw [(toBase_componentGenericPoint k X m D φ h ⟨Z, hZ⟩).def, hgen.def] at h1
    have h2 := MMP.Fourfold.topologicalKrullDim_le_of_isFinite (toBase m D h.ge)
      (T := (Set.univ : Set X)) fun _ => trivial
    exact le_antisymm (topologicalKrullDim_subspace_le _ Z) (h1 ▸ h2)
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ?_, hdim, rfl, inferInstance, ?_⟩
  · intro Z hZ
    simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst hZ
    exact (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq
  · intro Z'
    have hZ : (Set.univ : Set X) ∈ irreducibleComponents X := by
      simp [irreducibleComponents_eq_singleton]
    exact ⟨⟨Set.univ, hZ⟩, (toBase_componentGenericPoint k X m D φ h Z').eq
      (isGenericPoint_componentGenericPoint X ⟨Set.univ, hZ⟩)⟩

include h in
/-- The reflexive Weil pull-back of `D` is principal. -/
private theorem weilPullback_principal :
    ∃ hp : MMP.Flips.IsWeilPullbackSetting k (X ↘ Spec (.of k))
          (toBase m D h.ge ≫ X ↘ Spec (.of k)) (toBase m D h.ge),
        ∃ L : MMP.Flips.WeilDivisorialSubsheaf X, (∀ U, L.sections U = D.divisorialSubmodule U) ∧
          ∃ ψ : (RationalFunctions (cover m D h.ge))ˣ, ∀ U' : (cover m D h.ge).Opens,
            (MMP.Flips.weilPullback hp L).sections U' =
              Submodule.span Γ(cover m D h.ge, U')
                {show ToType ((rationalFunctionsPresheaf (cover m D h.ge)).obj (op U')) from
                  fun Z => (ψ : RationalFunctions (cover m D h.ge)) Z.1} := by
  haveI : IrreducibleSpace X := inferInstance
  haveI := isFinite_toBase k X m D φ h
  haveI := isNormal_cover k X m D φ h
  haveI : IsLocallyNoetherian (cover m D h.ge) :=
    LocallyOfFiniteType.isLocallyNoetherian (toBase m D h.ge)
  haveI : CompactSpace (cover m D h.ge) :=
    QuasiCompact.compactSpace_of_compactSpace (toBase m D h.ge)
  have hset := isWeilPullbackSetting k X m D φ h
  have hgen : ∀ Z' : irreducibleComponents (cover m D h.ge),
      toBase m D h.ge (componentGenericPoint (cover m D h.ge) Z') = genericPoint X :=
    fun Z' => (toBase_componentGenericPoint k X m D φ h Z').eq (genericPoint_spec X)
  obtain ⟨W0, hW0, hηW0, -⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⊤ : X.Opens)) (x := genericPoint X) trivial
  refine ⟨hset, weilOfDivisor D, fun U => rfl,
    ⟨psiFun m D h hgen hW0 hηW0, psiInvFun m D h hgen hW0 hηW0,
      psiFun_mul_psiInvFun m D h hgen hW0 hηW0,
      (mul_comm _ _).trans (psiFun_mul_psiInvFun m D h hgen hW0 hηW0)⟩, fun U' => ?_⟩
  refine le_antisymm (sections_weilPullback_le m D h hgen hset hW0 hηW0 U') ?_
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact psi_mem_sections_weilPullback m D h hgen hset (fun x' hx' => coheight_toBase_le k X m D φ h
      hx')
    hW0 hηW0 U'

/-- The image of `p^♯` is the degree-`0` part of the grading. -/
private theorem mem_range_toBase_app_iff (U : X.Opens) (a : (localSubalgebra m D h.ge).carrier U) :
    ((Stacks.RelativeSpec.universalAlgebraMap (situation m D h.ge)).right.app (op U)).hom a ∈
            Set.range ((toBase m D h.ge).app U).hom ↔
          ∀ i : Fin m, (i : ℕ) ≠ 0 → coeffEquiv m D h.ge U a i = 0 := by
  constructor
  · rintro ⟨r, hr⟩ i hi
    rw [toBase_app_apply X m D φ h] at hr
    obtain rfl := injective_universalAlgebraMap_app X m D φ h U hr
    refine Subtype.ext ?_
    change coeff m φ U i (((structureMap m φ).app (op U)).hom r) = 0
    rw [coeff_structureMap, if_neg hi]
  · intro ha
    have h0 := (mem_carrier_iff m D h.ge).mp a.2 0
    rw [zero_smul] at h0
    obtain ⟨s, hs⟩ := Divisor.IsDivisorialSection.exists_eq h0
    refine ⟨s, ?_⟩
    rw [toBase_app_apply X m D φ h]
    congr 1
    refine (coeffEquiv m D h.ge U).injective (funext fun i => Subtype.ext ?_)
    change coeff m φ U i (((structureMap m φ).app (op U)).hom s) = coeff m φ U i a.1
    rw [coeff_structureMap]
    split_ifs with hi
    · rw [hs, hi]
    · exact (congrArg Subtype.val (ha i hi)).symm

end CoverNormality

/-- **The divisorial cyclic cover of a trivialized multiple.** Let `X` be a normal variety over a
field `k` of characteristic zero, `D` a Weil divisor, `m ≥ 1` and `φ ∈ K(X)^×` with
`div(φ) + mD = 0`, and let `p : X' → X` be the cyclic cover
`MMP.Mori.DivisorialCyclicCover.toBase` of `(D, m, φ)`. Then
* `p` is finite, `X'` is normal, `p` has degree `m` at the generic point of `X`, and `p` is
  surjective;
* `p` is étale over an open neighbourhood of `x` if and only if `D` is Cartier at `x`;
* `p` satisfies the hypotheses of the Weil pull-back, and `p^w(𝒪_X(D)) = ψ 𝒪_{X'}` for a unit
  `ψ` of `K(X')`;
* `p^♯ : Γ(X, U) → Γ(X', p⁻¹U)` is injective, and its image is the degree-`0` part of the
  grading: the section `ψ_U(a)` of `𝒪_{X'}`, `a ∈ 𝒜(U)`, lies in it if and only if the components
  of `a` in all degrees `i ≠ 0` vanish. -/
@[mmp "lem_mmp_divisorial_cyclic_algebra_normal"]
public theorem isNormal_cover_of_principalDivisor_add_smul_eq_zero
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X]
    (m : ℕ) [NeZero m] (D : Divisor X) (φ : (RationalFunctions X)ˣ)
    (h : principalDivisor φ + m • D = 0) :
    IsFinite (toBase m D h.ge) ∧ IsNormal (cover m D h.ge) ∧
      ((toBase m D h.ge).finrank (genericPoint X) = m) ∧
      Surjective (toBase m D h.ge) ∧
      (∀ x : X, (∃ U : X.Opens, x ∈ U ∧ Etale (toBase m D h.ge ∣_ U)) ↔
        MMP.Flips.IsCartierAt D x) ∧
      (∃ hp : MMP.Flips.IsWeilPullbackSetting k (X ↘ Spec (.of k))
          (toBase m D h.ge ≫ X ↘ Spec (.of k)) (toBase m D h.ge),
        ∃ L : MMP.Flips.WeilDivisorialSubsheaf X, (∀ U, L.sections U = D.divisorialSubmodule U) ∧
          ∃ ψ : (RationalFunctions (cover m D h.ge))ˣ, ∀ U' : (cover m D h.ge).Opens,
            (MMP.Flips.weilPullback hp L).sections U' =
              Submodule.span Γ(cover m D h.ge, U')
                {show ToType ((rationalFunctionsPresheaf (cover m D h.ge)).obj (op U')) from
                  fun Z => (ψ : RationalFunctions (cover m D h.ge)) Z.1}) ∧
      (∀ U : X.Opens, Function.Injective ((toBase m D h.ge).app U).hom) ∧
      ∀ (U : X.Opens) (a : (localSubalgebra m D h.ge).carrier U),
        ((Stacks.RelativeSpec.universalAlgebraMap (situation m D h.ge)).right.app (op U)).hom a ∈
            Set.range ((toBase m D h.ge).app U).hom ↔
          ∀ i : Fin m, (i : ℕ) ≠ 0 → coeffEquiv m D h.ge U a i = 0 := by
  open CoverNormality in
  exact ⟨isFinite_toBase k X m D φ h, isNormal_cover k X m D φ h,
    finrank_toBase_genericPoint k X m D φ h, surjective_toBase k X m D φ h,
    etale_iff_isCartierAt k X m D φ h, weilPullback_principal k X m D φ h,
    injective_toBase_app X m D φ h, mem_range_toBase_app_iff X m D φ h⟩

end MMP.Mori.DivisorialCyclicCover
