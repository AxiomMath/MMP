/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.LinearAlgebra.FreeModule.Norm
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Norm.Defs

/-!
# The sum of multiplicities over the zeros of `g` is `[F : k(g)]` (Kollár 1.20.5)

For a `k`-domain `A` with fraction field `F` and `g ∈ A` transcendental over `k` with `A` finite
over `k[g]` (so `A` is finitely generated over `k`): the maximal ideals containing `g` are
finitely many and `∑_{𝔪 ∋ g} dim_k A_𝔪 / g A_𝔪 = [F : k(g)]`.

## Main results

* `MMP.Resolution.sum_finrank_quotient_eq_finrank_adjoin`

## References

* [J. Kollár, *Lectures on resolution of singularities*][KollarResolution], proof of 1.20.5
-/

@[expose] public noncomputable section

open Polynomial

namespace MMP.Resolution

/-- For `g ∈ A` transcendental over `k` with `A` a finite torsion-free module over `k[g] ≅ k[X]`,
the dimension of `A / g A` over `k` is the rank of `A` over `k[X]`. -/
private theorem finrank_quotient_span_eq_finrank_polynomial (k : Type*) [Field k] {A : Type*}
    [CommRing A] [IsDomain A] [Algebra k A] (g : A) (hg : Transcendental k g)
    (hfin : letI := (Polynomial.aeval (R := k) g).toAlgebra; Module.Finite k[X] A) :
    letI := (Polynomial.aeval (R := k) g).toAlgebra
    Module.finrank k (A ⧸ Ideal.span {g}) = Module.finrank k[X] A := by
  let _ : Algebra k[X] A := (Polynomial.aeval (R := k) g).toAlgebra
  have hinj : Function.Injective (algebraMap k[X] A) := transcendental_iff_injective.mp hg
  have : IsScalarTower k k[X] A := IsScalarTower.of_algebraMap_eq fun c => (aeval_C g c).symm
  have : FaithfulSMul k[X] A := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Module.Free k[X] A := Module.free_of_finite_type_torsion_free'
  have hgX : algebraMap k[X] A X = g := aeval_X g
  have hg0 : g ≠ 0 := hgX ▸ (map_ne_zero_iff _ hinj).mpr X_ne_zero
  have hn : Algebra.norm k[X] g = X ^ Module.finrank k[X] A := by
    simpa [hgX] using Algebra.norm_algebraMap (S := A) (X : k[X])
  rw [finrank_quotient_span_eq_natDegree_norm (Module.Free.chooseBasis k[X] A) hg0, hn,
    natDegree_X_pow]

/-- For `g ∈ A` transcendental over `k` with `A` finite over `k[g]`, the dimension of `A / g A`
over `k` is the degree of the fraction field `F` of `A` over `k(g)`. -/
private theorem finrank_quotient_span_eq_finrank_adjoin (k : Type*) [Field k] {A : Type*}
    [CommRing A] [IsDomain A] [Algebra k A]
    (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F] [Algebra k F] [IsScalarTower k A F]
    (g : A) (hg : Transcendental k g)
    (hfin : letI := (Polynomial.aeval (R := k) g).toAlgebra; Module.Finite k[X] A) :
    Module.finrank k (A ⧸ Ideal.span {g}) =
        Module.finrank (IntermediateField.adjoin k {algebraMap A F g}) F := by
  let _ : Algebra k[X] A := (Polynomial.aeval (R := k) g).toAlgebra
  set g' := algebraMap A F g
  set K := IntermediateField.adjoin k {g'}
  have hg' : Transcendental k g' :=
    (transcendental_algebraMap_iff (IsFractionRing.injective A F)).mpr hg
  let φ : k[X] →ₐ[k] K := aeval (IntermediateField.AdjoinSimple.gen k g')
  let : Algebra k[X] K := φ.toAlgebra
  let : Algebra k[X] F := (aeval g').toAlgebra
  have hKF : ∀ p : k[X], algebraMap K F (φ p) = aeval g' p := fun p => by
    simp only [φ]
    rw [← aeval_algebraMap_apply, IntermediateField.AdjoinSimple.algebraMap_gen]
  have : IsScalarTower k[X] K F := IsScalarTower.of_algebraMap_eq fun p => (hKF p).symm
  have : IsScalarTower k[X] A F := IsScalarTower.of_algebraMap_eq fun p => by
    change aeval g' p = algebraMap A F (aeval g p)
    rw [aeval_algebraMap_apply]
  have : FaithfulSMul k[X] K := (faithfulSMul_iff_algebraMap_injective _ _).mpr fun p q h =>
    transcendental_iff_injective.mp hg'
      ((hKF p).symm.trans ((congrArg (algebraMap K F) h).trans (hKF q)))
  have : IsFractionRing k[X] K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨r, hr, s, hs, hz⟩ := IntermediateField.mem_adjoin_iff_div.mp z.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hr hs
    obtain ⟨p, rfl⟩ := hr
    obtain ⟨q, rfl⟩ := hs
    refine ⟨p, q, (algebraMap K F).injective ?_⟩
    rw [map_div₀]
    exact hz.trans (congrArg₂ (· / ·) (hKF p).symm (hKF q).symm)
  rw [finrank_quotient_span_eq_finrank_polynomial k g hg hfin,
    IsFractionRing.finrank_eq k[X] K A F]

/-- If `p` is a prime of `A ⧸ I` whose preimage in `A` is `𝔪`, then the localization of `A ⧸ I`
at `p` has the same `k`-dimension as `A_𝔪 ⧸ I A_𝔪`. -/
private theorem finrank_localization_quotient_eq (k : Type*) [Field k] {A : Type*} [CommRing A]
    [Algebra k A] {I 𝔪 : Ideal A} [𝔪.IsPrime] (p : Ideal (A ⧸ I)) [p.IsPrime]
    (hp : p.comap (Ideal.Quotient.mk I) = 𝔪) :
    Module.finrank k (Localization.AtPrime p) = Module.finrank k
      (Localization.AtPrime 𝔪 ⧸ I.map (algebraMap A (Localization.AtPrime 𝔪))) := by
  have hM : Algebra.algebraMapSubmonoid (A ⧸ I) 𝔪.primeCompl = p.primeCompl :=
    hp ▸ Ideal.map_primeCompl_comap_of_surjective (f := Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective p
  have : IsLocalization p.primeCompl
      (Localization.AtPrime 𝔪 ⧸ I.map (algebraMap A (Localization.AtPrime 𝔪))) :=
    hM ▸ inferInstance
  have : IsScalarTower k (A ⧸ I)
      (Localization.AtPrime 𝔪 ⧸ I.map (algebraMap A (Localization.AtPrime 𝔪))) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k A (A ⧸ I), Ideal.Quotient.algebraMap_eq]
      rfl
  exact ((IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) _).restrictScalars
    k).toLinearEquiv.finrank_eq

/-- **Kollár, proof of Lemma 1.20.5, p. 19.** Let `A` be a domain which is an algebra over a
field `k` (finitely generated and of dimension `1` in the source; neither is needed), with
fraction field `F`, and `g ∈ A` transcendental over `k` such that `A` is a finitely generated
`k[g]`-module. Then the set `Z` of maximal ideals of `A` containing `g` is finite, and
`∑_{𝔪 ∈ Z} dim_k A_𝔪 / g A_𝔪 = [F : k(g)]`. -/
@[mmp "lem_kr1a_sum_of_multiplicities_eq_rank"]
theorem sum_finrank_quotient_eq_finrank_adjoin (k : Type*) [Field k] {A : Type*} [CommRing A]
    [IsDomain A] [Algebra k A]
    (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F] [Algebra k F] [IsScalarTower k A F]
    (g : A) (hg : Transcendental k g)
    (hfin : letI := (Polynomial.aeval (R := k) g).toAlgebra; Module.Finite k[X] A) :
    ∃ hZ : {𝔪 : Ideal A | 𝔪.IsMaximal ∧ g ∈ 𝔪}.Finite,
      ∑ 𝔪 ∈ hZ.toFinset.attach,
        (haveI : 𝔪.1.IsPrime := (hZ.mem_toFinset.mp 𝔪.2).1.isPrime
         Module.finrank k (Localization.AtPrime 𝔪.1 ⧸
            Ideal.span {algebraMap A (Localization.AtPrime 𝔪.1) g})) =
        Module.finrank (IntermediateField.adjoin k {algebraMap A F g}) F := by
  let _ : Algebra k[X] A := (Polynomial.aeval (R := k) g).toAlgebra
  have : FaithfulSMul k[X] A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (transcendental_iff_injective.mp hg)
  set I : Ideal A := Ideal.span {g}
  have : Module.Finite k (A ⧸ I) := Module.finite_of_finrank_pos
    ((finrank_quotient_span_eq_finrank_polynomial k g hg hfin).symm ▸ Module.finrank_pos)
  have : IsArtinianRing (A ⧸ I) := IsArtinianRing.of_finite k (A ⧸ I)
  let _ : Fintype (PrimeSpectrum (A ⧸ I)) := Fintype.ofFinite _
  let c : PrimeSpectrum (A ⧸ I) → Ideal A := fun p => p.asIdeal.comap (Ideal.Quotient.mk I)
  have hc : ∀ p, c p ∈ {𝔪 : Ideal A | 𝔪.IsMaximal ∧ g ∈ 𝔪} := fun p => by
    have := Ideal.IsPrime.isMaximal' p.2
    refine ⟨Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective, ?_⟩
    simp [c, I, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self g)]
  have hcs : ∀ 𝔪 ∈ {𝔪 : Ideal A | 𝔪.IsMaximal ∧ g ∈ 𝔪}, ∃ p, c p = 𝔪 := fun 𝔪 h𝔪 => by
    have := h𝔪.1
    have hI : I ≤ 𝔪 := (Ideal.span_singleton_le_iff_mem _).mpr h𝔪.2
    exact ⟨⟨_, Ideal.isPrime_map_quotientMk_of_isPrime hI⟩, Ideal.comap_map_mk hI⟩
  have hZ : {𝔪 : Ideal A | 𝔪.IsMaximal ∧ g ∈ 𝔪}.Finite := (Set.finite_range c).subset hcs
  refine ⟨hZ, ?_⟩
  rw [← finrank_quotient_span_eq_finrank_adjoin k F g hg hfin,
    IsArtinianRing.finrank_eq_sum_primeSpectrum (A ⧸ I) k]
  symm
  refine Finset.sum_bij (fun p _ => ⟨c p, hZ.mem_toFinset.mpr (hc p)⟩)
    (fun _ _ => Finset.mem_attach _ _) ?_ ?_ ?_
  · intro p _ q _ hpq
    exact PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      (congrArg Subtype.val hpq))
  · intro 𝔪 _
    obtain ⟨p, hp⟩ := hcs 𝔪.1 (hZ.mem_toFinset.mp 𝔪.2)
    exact ⟨p, Finset.mem_univ _, Subtype.ext hp⟩
  · intro p _
    rw [finrank_localization_quotient_eq k p.asIdeal (𝔪 := c p) rfl, Ideal.map_span,
      Set.image_singleton]

end MMP.Resolution
