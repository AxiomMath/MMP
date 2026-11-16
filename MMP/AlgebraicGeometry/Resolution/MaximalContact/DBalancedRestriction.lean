module
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.DerivativeIdealOrder
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Monomial

/-!
# Restricting a `D`-balanced ideal to a smooth hypersurface

Let `X` be a smooth variety of dimension at least one over a field `k` of characteristic zero,
`μ ≥ 1` and `K ⊆ 𝒪_X` an ideal sheaf with `(D^i K)^μ ⊆ K^(μ-i)` for `0 ≤ i < μ`. If `S ⊆ X` is a
smooth hypersurface none of whose irreducible components lies in the cosupport of the marked
ideal `(K, μ)`, then the restriction `K·𝒪_S` is nonzero at the generic point of every irreducible
component of `S`. Indeed, if `K·𝒪_{S₁} = 0` for a component `S₁`, then `S₁ ⊆ cosupp K`, and
`cosupp K = cosupp (K, μ)` by
`MMP.Resolution.support_eq_cosupport_of_higherDerivativeIdeal_pow_le`.

## Main results

* `MMP.Resolution.isNonzeroAtGenericPoints_comap_of_higherDerivativeIdeal_pow_le`: under the
  balancing condition, `K.comap S.subschemeι` is nonzero at the generic points of `S`.

## Implementation notes

The restriction `K·𝒪_S` is the inverse image ideal `K.comap S.subschemeι` on the closed
subscheme `S.subscheme`, and "nonzero on every irreducible component" is
`MMP.Resolution.IsNonzeroAtGenericPoints`. The irreducible components of `S` are those of the
scheme `S.subscheme`; their images under `S.subschemeι` are the irreducible components of
`S.support ⊆ X`, and the hypothesis compares these images with the cosupport of `(K, μ)`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, proof of Lemma 3.102]
-/

open AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-- On a smooth variety of positive dimension over a field of characteristic zero, let `K` be an
ideal sheaf with `(D^i K)^μ ⊆ K^(μ-i)` for all `i < μ` (with `μ ≥ 1`), and let `S ⊆ X` be a smooth
hypersurface no irreducible component of which is contained in the cosupport of the marked ideal
`(K, μ)`. Then the restriction `K·𝒪_S` is nonzero at the generic point of every irreducible
component of `S`. -/
@[mmp "lem_kr3e_restriction_of_d_balanced_nonzero"]
public theorem isNonzeroAtGenericPoints_comap_of_higherDerivativeIdeal_pow_le {k : Type u}
    [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hX : Mori.IsVariety k sX) (hdim : 1 ≤ topologicalKrullDim X) {μ : ℕ} (hμ : 1 ≤ μ)
    {K : X.IdealSheafData} (hK : ∀ i < μ, higherDerivativeIdeal sX K i ^ μ ≤ K ^ (μ - i))
    {S : X.IdealSheafData} (hS : IsSmoothHypersurface sX S)
    (hcomp : ∀ Z ∈ irreducibleComponents S.subscheme,
      ¬ S.subschemeι '' Z ⊆ (⟨K, μ⟩ : MarkedIdeal X).cosupport) :
    IsNonzeroAtGenericPoints (K.comap S.subschemeι) := by
  intro η hη hbot
  refine hcomp _ hη ?_
  rw [← support_eq_cosupport_of_higherDerivativeIdeal_pow_le sX hX hdim hμ hK,
    Set.image_subset_iff]
  have hmem : η ∈ (K.comap S.subschemeι).support := by
    by_contra h
    exact bot_ne_top (hbot.symm.trans ((IdealSheafData.stalk_eq_top_iff_notMem_support _ η).2 h))
  rw [Scheme.IdealSheafData.support_comap] at hmem
  exact (K.support.isClosed.preimage S.subschemeι.continuous).closure_subset_iff.2
    (Set.singleton_subset_iff.2 hmem)

end MMP.Resolution
