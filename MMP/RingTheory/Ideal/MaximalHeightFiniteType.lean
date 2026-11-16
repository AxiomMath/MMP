module

public import StacksFrontier.RingTheory.MvPolynomial.MaximalIdeal
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Maximal ideals of a finitely generated domain all have height `dim A`

Let `A` be a domain finitely generated as an algebra over a field `K`. Every maximal ideal `𝔪`
of `A` has height `dim A`; equivalently the local ring `A_𝔪` has Krull dimension `dim A`.
Geometrically: at every closed point of an affine variety the local ring has the dimension of
the variety.

By Noether normalization there is a finite injective `K`-algebra map
`K[x_1, …, x_s] → A`. Over the polynomial ring every maximal ideal has height `s`
(`height_maximal_ideal_eq`). Along an integral extension the height of a prime is at most that
of its contraction (incomparability), and, since `K[x_1, …, x_s]` is integrally closed and `A`
is a domain, at least that height (going down). So every maximal ideal of `A` has height `s`,
and `dim A`, the supremum of these heights, is `s` too.

## Main results

* `MMP.IdealHeight.height_le_height_under_of_isIntegral`: along an integral extension the
  height of a prime is at most the height of its contraction.
* `MMP.IdealHeight.height_eq_ringKrullDim_of_isMaximal_of_finiteType`: in a domain of finite
  type over a field, every maximal ideal has height `dim A`.
* `MMP.IdealHeight.ringKrullDim_localization_atPrime_eq_of_isMaximal_of_finiteType`:
  `dim A_𝔪 = dim A`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Appendix B.1.
* [The Stacks project, Tag 00OP][stacks-project]
-/

@[expose] public section

namespace MMP.IdealHeight

open _root_.Ideal

/-- **Incomparability bounds heights.** Along an integral extension `R → S`, the height of a
prime `P` of `S` is at most the height of its contraction `P ∩ R`: a strict chain of primes
below `P` contracts to a strict chain below `P ∩ R`. -/
theorem height_le_height_under_of_isIntegral {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (P : Ideal S) [P.IsPrime] :
    P.height ≤ (P.under R).height := by
  rw [PrimeSpectrum.height_eq_orderHeight (⟨P, inferInstance⟩ : PrimeSpectrum S),
    PrimeSpectrum.height_eq_orderHeight (⟨P.under R, inferInstance⟩ : PrimeSpectrum R)]
  exact Order.height_le_height_apply_of_strictMono
    (PrimeSpectrum.comap (algebraMap R S))
    (fun I J h ↦ Ideal.IsIntegral.comap_lt_comap (R := R) h) ⟨P, inferInstance⟩

/-- **Maximal ideals of a finitely generated domain have height `dim A`.** If `A` is a domain
of finite type over a field `K`, every maximal ideal of `A` has height equal to the Krull
dimension of `A`. -/
theorem height_eq_ringKrullDim_of_isMaximal_of_finiteType (K : Type*) {A : Type*} [Field K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A)
    [m.IsMaximal] : (m.height : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K A
  letI : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) K) A := hfin
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) A := inferInstance
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  -- every maximal ideal of `A` has height `s`
  have key : ∀ (n : Ideal A) [n.IsMaximal], n.height = s := by
    intro n _
    have hmax : (n.under (MvPolynomial (Fin s) K)).IsMaximal := inferInstance
    refine le_antisymm ?_ ?_
    · exact (height_le_height_under_of_isIntegral n).trans
        (height_maximal_ideal_eq s _ hmax).le
    · rw [← height_maximal_ideal_eq s _ hmax,
        height_eq_height_add_of_liesOver_of_hasGoingDown (n.under (MvPolynomial (Fin s) K)) n]
      exact le_self_add
  refine le_antisymm ?_ ?_
  · exact height_le_ringKrullDim_of_ne_top (IsMaximal.ne_top ‹_›)
  · rw [key m]
    exact (ringKrullDim_le_iff_isMaximal_height_le _).mpr fun n _ ↦ by rw [key n]

/-- **The local ring at a closed point has the dimension of the variety.** If `A` is a domain of
finite type over a field `K` and `𝔪` is a maximal ideal, then `dim A_𝔪 = dim A`. -/
theorem ringKrullDim_localization_atPrime_eq_of_isMaximal_of_finiteType (K : Type*) {A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A)
    [m.IsMaximal] : ringKrullDim (Localization.AtPrime m) = ringKrullDim A := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m),
    height_eq_ringKrullDim_of_isMaximal_of_finiteType K m]

end MMP.IdealHeight
