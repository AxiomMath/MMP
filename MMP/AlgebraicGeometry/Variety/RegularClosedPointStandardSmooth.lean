module

public import StacksFrontier.RingTheory.Smooth.RegularLocalRing
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# A regular closed point has a standard smooth neighbourhood

Let `K` be an algebraically closed field, `S` a finitely generated `K`-algebra and `𝔪 ⊆ S` a
maximal ideal such that the local ring `S_𝔪` is regular. Then `S/K` is smooth at `𝔪`
(Stacks 00TS), so some basic open `D(g) ∋ 𝔪` is standard smooth: `S_g` has a submersive
presentation `S_g = K[x_i]_{i ∈ ι} / (f_j)_{j ∈ σ}`, with `ι, σ` finite and the Jacobian
`(∂f_j/∂x_i)_{i, j ∈ σ}` invertible in `S_g`. Its relative dimension `|ι| - |σ|` is the Krull
dimension of `S_𝔪`: the module `Ω_{S_g/K}` is free of rank `|ι| - |σ|`, and at the closed point
`𝔪 S_g` its fibre has dimension `dim (S_g)_{𝔪} = dim S_𝔪` (Stacks 00TS again, now for `S_g`).

This is the algebraic input of the statement that the regular locus of a complex variety of
dimension `n` is a complex manifold of dimension `n`: near a regular point the variety is cut out
in `ℂ^ι` by `|σ|` equations with independent differentials.

## Main results

* `MMP.exists_submersivePresentation_away_of_isRegularLocalRing`: a regular
  maximal ideal `𝔪` has `g ∉ 𝔪` with `S_g` admitting a submersive presentation of dimension
  `dim S_𝔪`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1 and Appendix B.1.
* [The Stacks project, Tag 00TS][stacks-project]
-/

@[expose] public section

open Algebra TensorProduct

namespace MMP

variable {K S : Type*} [Field K] [IsAlgClosed K] [CommRing S] [Algebra K S]
  [Algebra.FiniteType K S]

/-- If `𝔪` is a maximal ideal of a finitely generated algebra `S` over an algebraically closed
field `K` and `S_𝔪` is a regular local ring, then some `g ∉ 𝔪` makes `S_g` standard smooth over
`K`, through a submersive presentation whose relative dimension is the Krull dimension of
`S_𝔪`. -/
theorem exists_submersivePresentation_away_of_isRegularLocalRing (m : Ideal S) [m.IsMaximal]
    [IsRegularLocalRing (Localization.AtPrime m)] :
    ∃ g ∉ m, ∃ (ι σ : Type) (_ : Finite ι) (_ : Finite σ)
      (P : Algebra.SubmersivePresentation K (Localization.Away g) ι σ),
      (P.dimension : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime m) := by
  have hts := Algebra.isSmoothAt_tfae_of_isAlgClosed (k := K) m (Localization.AtPrime m)
  have hsm : Algebra.IsSmoothAt K m := (hts.out 1 5).mp ‹_›
  have : Algebra.FinitePresentation K S := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  obtain ⟨g, hg, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K m
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hstd.out
  refine ⟨g, hg, ι, σ, ‹_›, ‹_›, P, ?_⟩
  set Sg := Localization.Away g
  have hdisj : Disjoint (Submonoid.powers g : Set S) m := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ hk
    exact hg (‹m.IsMaximal›.isPrime.mem_of_pow_mem k hk)
  set m' : Ideal Sg := m.map (algebraMap S Sg)
  have hm'c : m'.comap (algebraMap S Sg) = m :=
    IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers g) Sg inferInstance hdisj
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := K)
  have hm' : m'.IsMaximal := by
    rw [IsLocalization.isMaximal_iff_isMaximal_disjoint Sg g m', Ideal.under, hm'c]
    exact ⟨inferInstance, hg⟩
  -- Stacks 00TS for `S_g` at `𝔪 S_g`: the fibre of `Ω` there has dimension `dim (S_g)_𝔪`
  have hts' := Algebra.isSmoothAt_tfae_of_isAlgClosed (k := K) m' (Localization.AtPrime m')
  have hsm' : Algebra.IsSmoothAt K m' := inferInstance
  have h3 := (hts'.out 5 3).mp hsm'
  have : Nontrivial (Sg ⧸ m') := Ideal.Quotient.nontrivial_iff.mpr hm'.ne_top
  have : Nontrivial Sg := (Ideal.Quotient.mk m').domain_nontrivial
  -- `Ω_{S_g/K}` is free of rank `dim P`, so its fibre has dimension `dim P`
  have hdimOmega : Module.finrank (Sg ⧸ m') ((Sg ⧸ m') ⊗[Sg] Ω[Sg⁄K]) = P.dimension := by
    rw [Module.finrank_baseChange]
    exact Module.finrank_eq_of_rank_eq P.rank_kaehlerDifferential
  -- `(S_g)_{𝔪 S_g}` is a localization of `S` at `𝔪`
  have hloc : IsLocalization.AtPrime (Localization.AtPrime m') m := by
    have h := IsLocalization.isLocalization_atPrime_localization_atPrime (Submonoid.powers g) m'
    have hc : (m'.comap (algebraMap S Sg)).primeCompl = m.primeCompl := by
      ext x; simp [Ideal.primeCompl, hm'c]
    unfold IsLocalization.AtPrime at h ⊢
    rwa [hc] at h
  have e := IsLocalization.algEquiv m.primeCompl (Localization.AtPrime m) (Localization.AtPrime m')
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv, ← h3, hdimOmega]

end MMP
