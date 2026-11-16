module

public import MMP.RingTheory.Kaehler.FormsTraceDVR
public import Mathlib.RingTheory.DedekindDomain.Instances

/-!
# The tame trace estimate over a height-one prime of a finite extension of domains

Let `A₀ ⊆ B₀` be a finite extension of domains, with fraction fields `K ⊆ L`,
and `𝔭` a prime of `A₀` whose localization `A₀_𝔭` is a discrete valuation ring with uniformizer
`t ∈ A₀`. If `x ∈ L` is such that `t x` lies in `Q (B₀)_Q` for every prime `Q` of `B₀` over `𝔭`,
then `Tr_{L/K}(x) ∈ A₀_𝔭`. This is
`MMP.FourfoldProofs.FractionalLogComplexProof.exists_algebraMap_eq_trace_of_forall_isMaximal` for the
local ring `A₀_𝔭` and the finite free `A₀_𝔭`-algebra `B₀ ⊗ A₀_𝔭`, whose maximal ideals are the
primes of `B₀` over `𝔭`. In the geometric application `A₀` and `B₀` are the rings of functions of
an affine open of `V` and of its preimage under a finite cover, `𝔭` is a prime divisor, and the
primes of `B₀` over `𝔭` are the points of the cover over its generic point.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_mul_trace_eq_of_forall_isPrime`: the estimate.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_mul_formsTrace_repr_eq_of_forall_isPrime`: the
  estimate for the coordinates of the trace of a form.
-/

@[expose] public section

open IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

section HeightOne

variable {A₀ B₀ K L : Type u} [CommRing A₀] [IsDomain A₀] [CommRing B₀] [IsDomain B₀]
  [Algebra A₀ B₀] [Module.Finite A₀ B₀] [Field K] [Algebra A₀ K] [IsFractionRing A₀ K]
  [Field L] [Algebra B₀ L] [IsFractionRing B₀ L] [Algebra K L] [Algebra A₀ L]
  [IsScalarTower A₀ K L] [IsScalarTower A₀ B₀ L]

/-- **The tame trace estimate over a height-one prime.** If `t` generates the maximal ideal of
`A₀_𝔭` and `t x` lies in `Q (B₀)_Q` for every prime `Q` of `B₀` over `𝔭`, then
`Tr_{L/K}(x) ∈ A₀_𝔭`. -/
theorem exists_mul_trace_eq_of_forall_isPrime
    (𝔭 : Ideal A₀) [𝔭.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime 𝔭)] {t : A₀}
    (hm : maximalIdeal (Localization.AtPrime 𝔭) =
      Ideal.span {algebraMap A₀ (Localization.AtPrime 𝔭) t}) (x : L)
    (hx : ∀ Q : Ideal B₀, Q.IsPrime → Q.comap (algebraMap A₀ B₀) = 𝔭 → ∃ b ∈ Q, ∃ c ∉ Q,
      algebraMap B₀ L c * (algebraMap A₀ L t * x) = algebraMap B₀ L b) :
    ∃ a : A₀, ∃ s ∉ 𝔭, algebraMap A₀ K s * Algebra.trace K L x = algebraMap A₀ K a := by
  classical
  let A := Localization.AtPrime 𝔭
  let S := Algebra.algebraMapSubmonoid B₀ 𝔭.primeCompl
  let B := Localization S
  have hA₀K : Function.Injective (algebraMap A₀ K) := IsFractionRing.injective A₀ K
  have hA₀L : Function.Injective (algebraMap A₀ L) := by
    rw [IsScalarTower.algebraMap_eq A₀ K L]
    exact (algebraMap K L).injective.comp hA₀K
  have hinj : Function.Injective (algebraMap A₀ B₀) := fun a b h => hA₀L (by
    rw [IsScalarTower.algebraMap_apply A₀ B₀ L, h, ← IsScalarTower.algebraMap_apply])
  have hne : ∀ s : A₀, s ∉ 𝔭 → s ≠ 0 := fun s hs h0 => hs (h0 ▸ 𝔭.zero_mem)
  let fA : A →+* K := IsLocalization.lift (M := 𝔭.primeCompl) (g := algebraMap A₀ K)
    fun s => isUnit_iff_ne_zero.2 fun h => hne s s.2 (hA₀K (h.trans (map_zero _).symm))
  let : Algebra A K := fA.toAlgebra
  have : IsScalarTower A₀ A K :=
    IsScalarTower.of_algebraMap_eq fun a => (IsLocalization.lift_eq _ a).symm
  have : IsFractionRing A K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl A K
  have hSL : ∀ y : S, IsUnit (algebraMap B₀ L y) := by
    rintro ⟨_, ⟨s, hs, rfl⟩⟩
    refine isUnit_iff_ne_zero.2 fun h => hne s hs (hA₀L ?_)
    rw [IsScalarTower.algebraMap_apply A₀ B₀ L, map_zero]
    exact h
  let fB : B →+* L := IsLocalization.lift (M := S) (g := algebraMap B₀ L) hSL
  let : Algebra B L := fB.toAlgebra
  have : IsScalarTower B₀ B L :=
    IsScalarTower.of_algebraMap_eq fun b => (IsLocalization.lift_eq _ b).symm
  have hSnz : S ≤ nonZeroDivisors B₀ := by
    rintro _ ⟨s, hs, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero fun h => hne s hs (hinj (h.trans (map_zero _).symm))
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hSnz
  have : IsFractionRing B L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S B L
  let : Algebra A L := (fB.comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A K L := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    refine IsLocalization.ringHom_ext 𝔭.primeCompl ?_
    ext a
    change fB (algebraMap A B (algebraMap A₀ A a)) = algebraMap K L (fA (algebraMap A₀ A a))
    rw [← IsScalarTower.algebraMap_apply A₀ A B, IsScalarTower.algebraMap_apply A₀ B₀ B,
      IsLocalization.lift_eq, IsLocalization.lift_eq, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  have : Module.Finite A B := Module.Finite.of_isLocalization A₀ B₀ 𝔭.primeCompl
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have hinjAB : Function.Injective (algebraMap A B) := fun a b h => hAL (by
    rw [IsScalarTower.algebraMap_apply A B L, h, ← IsScalarTower.algebraMap_apply])
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.2 hinjAB
  have : Module.Free A B := Module.free_of_finite_type_torsion_free'
  have ht' : algebraMap A₀ A t ≠ 0 := fun h0 =>
    IsDiscreteValuationRing.not_a_field A (by rw [hm, h0, Ideal.span_singleton_eq_bot])
  have htL : algebraMap A L (algebraMap A₀ A t) = algebraMap A₀ L t := by
    change fB (algebraMap A B (algebraMap A₀ A t)) = _
    rw [← IsScalarTower.algebraMap_apply A₀ A B, IsScalarTower.algebraMap_apply A₀ B₀ B,
      IsLocalization.lift_eq, ← IsScalarTower.algebraMap_apply]
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_trace_of_forall_isMaximal (A := A) (B := B) (K := K)
    (L := L) hinjAB ht' hm x fun Q hQ => by
      let Q₀ := Q.comap (algebraMap B₀ B)
      have hQA : Q.comap (algebraMap A B) = maximalIdeal A :=
        IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) Q)
      have hQ₀ : Q₀.comap (algebraMap A₀ B₀) = 𝔭 := by
        rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
          IsScalarTower.algebraMap_eq A₀ A B, ← Ideal.comap_comap, hQA]
        exact Localization.AtPrime.under_maximalIdeal
      obtain ⟨b, hb, c, hc, hbc⟩ := hx Q₀ (Ideal.comap_isPrime _ _) hQ₀
      refine ⟨algebraMap B₀ B b, hb, algebraMap B₀ B c, hc, ?_⟩
      rwa [htL, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  obtain ⟨⟨a₀, s₀⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl a
  exact ⟨a₀, s₀, s₀.2, ((IsLocalization.lift_mk'_spec _ _ _ _).1 ha).symm⟩

/-- **The tame trace estimate for forms over a height-one prime.** If `t` times every coordinate
of a `p`-form `ω` of `L` in the pulled-back wedges of a basis of `Ω_{K/k}` lies in `Q (B₀)_Q` for
every prime `Q` of `B₀` over `𝔭`, then every coordinate of `Tr ω` lies in `A₀_𝔭`. -/
theorem exists_mul_formsTrace_repr_eq_of_forall_isPrime {k : Type u} [Field k] [Algebra k K]
    [Algebra k L] [IsScalarTower k K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (𝔭 : Ideal A₀) [𝔭.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime 𝔭)] {t : A₀}
    (hm : maximalIdeal (Localization.AtPrime 𝔭) =
      Ideal.span {algebraMap A₀ (Localization.AtPrime 𝔭) t})
    {ι : Type*} [LinearOrder ι] [Finite ι] (b : Module.Basis ι K Ω[K⁄k]) (p : ℕ)
    (ω : ⋀[L]^p (Ω[L⁄k]))
    (hω : ∀ Q : Ideal B₀, Q.IsPrime → Q.comap (algebraMap A₀ B₀) = 𝔭 → ∀ S, ∃ x ∈ Q, ∃ c ∉ Q,
      algebraMap B₀ L c * (algebraMap A₀ L t *
        ((pullbackBasis (L := L) b).exteriorPower p).repr ω S) = algebraMap B₀ L x)
    (S : Set.powersetCard ι p) :
    ∃ a : A₀, ∃ s ∉ 𝔭, algebraMap A₀ K s * (b.exteriorPower p).repr (formsTrace k K L p ω) S =
      algebraMap A₀ K a := by
  rw [formsTrace_repr]
  exact exists_mul_trace_eq_of_forall_isPrime 𝔭 hm _ fun Q hQ hQ' => hω Q hQ hQ' S

end HeightOne

end MMP.FourfoldProofs.FractionalLogComplexProof
