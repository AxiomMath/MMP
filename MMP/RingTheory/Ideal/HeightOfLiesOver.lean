module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.IntegralClosure.GoingDown

/-!
# Primes of a finite extension over a height-one prime

Let `A ⊆ B` be an integral extension of Noetherian domains with `A` integrally closed, and `Q` a
prime of `B` over a prime `𝔭` of `A`. By going down and incomparability `Q` has the height of `𝔭`;
in particular the primes of `B` over a height-one prime of `A` have height one. An element of the
fraction field of `B` which comes from the maximal ideal of the localization `B_Q` is a quotient
`b / c` with `b ∈ Q` and `c ∉ Q`. These are the inputs, at the points of a finite cover over the
generic point of a prime divisor, of the tame trace estimate.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.height_eq_of_liesOver`: `Q` has the height of `𝔭`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_mem_mul_eq_of_mem_maximalIdeal`: quotients from
  the maximal ideal of `B_Q`.
-/

@[expose] public section

open IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

/-- **Primes over `𝔭` in an integral extension have the height of `𝔭`.** In an integral extension
`A → B` of Noetherian domains with `A` integrally closed, a prime `Q` of `B` lying over `𝔭` has
`Q.height = 𝔭.height`. -/
theorem height_eq_of_liesOver {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B] [IsIntegrallyClosed A]
    [IsNoetherianRing A] [IsNoetherianRing B] (𝔭 : Ideal A) [𝔭.IsPrime] (Q : Ideal B) [Q.IsPrime]
    [Q.LiesOver 𝔭] : Q.height = 𝔭.height := by
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown 𝔭 Q]
  set I := 𝔭.map (algebraMap A B)
  suffices h : (Q.map (Ideal.Quotient.mk I)).height = 0 by rw [h, add_zero]
  have hcomap : Q.comap (algebraMap A B) = 𝔭 := (Ideal.LiesOver.over (P := Q) (p := 𝔭)).symm
  have hIQ : I ≤ Q := Ideal.map_le_iff_le_comap.2 hcomap.ge
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ Q := by rw [Ideal.mk_ker]; exact hIQ
  have hQ' : (Q.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  rw [Ideal.height_eq_zero_iff]
  refine ⟨⟨hQ', bot_le⟩, fun J hJ hJQ => ?_⟩
  have hJp : J.IsPrime := hJ.1
  let J' := J.comap (Ideal.Quotient.mk I)
  have hJ'Q : J' ≤ Q := by
    have := Ideal.comap_mono (f := Ideal.Quotient.mk I) hJQ
    rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      sup_eq_left.2 (by
        intro x hx
        exact hker (RingHom.mem_ker.2 (Ideal.mem_bot.1 (Ideal.mem_comap.1 hx))))] at this
  have hIJ' : I ≤ J' := by
    intro x hx
    simp [J', Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx, J.zero_mem]
  have hJ'eq : J' = Q := by
    by_contra hne
    have hlt := Ideal.IsIntegral.comap_lt_comap (R := A) (lt_of_le_of_ne hJ'Q hne)
    rw [show Q.under A = 𝔭 from hcomap] at hlt
    exact (lt_irrefl _) (lt_of_le_of_lt (Ideal.le_comap_of_map_le hIJ') hlt)
  rw [← hJ'eq, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

/-- **Quotients from the maximal ideal of `B_Q`.** An element of a `B_Q`-algebra `L` coming from
the maximal ideal of `B_Q` is `b / c` with `b ∈ Q` and `c ∉ Q`. -/
theorem exists_mem_mul_eq_of_mem_maximalIdeal {B R L : Type*} [CommRing B] [CommRing R]
    [CommRing L] [Algebra B R] [Algebra B L] [Algebra R L] [IsScalarTower B R L] (Q : Ideal B)
    [Q.IsPrime] [IsLocalization.AtPrime R Q] [IsLocalRing R] {x : L} {r : R}
    (hr : r ∈ maximalIdeal R) (hx : algebraMap R L r = x) :
    ∃ b ∈ Q, ∃ c ∉ Q, algebraMap B L c * x = algebraMap B L b := by
  obtain ⟨⟨b, c⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl r
  refine ⟨b, (IsLocalization.AtPrime.mk'_mem_maximal_iff R Q b c).1 hr, c, c.2, ?_⟩
  rw [← hx, IsScalarTower.algebraMap_apply B R L, IsScalarTower.algebraMap_apply B R L b,
    ← map_mul, mul_comm, IsLocalization.mk'_spec]

end MMP.FourfoldProofs.FractionalLogComplexProof
