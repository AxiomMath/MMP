module

public import MMP.AlgebraicTopology.PoincareDuality.ManifoldLocal
public import MMP.AlgebraicTopology.PoincareDuality.Box
public import MMP.AlgebraicTopology.PoincareDuality.Punctured
public import MMP.AlgebraicTopology.ThomClass.Basic

/-!
# Borel–Moore homology of a manifold vanishes above its dimension (Fulton, §19.1)

Let `Y` be a real `n`-manifold: a Hausdorff, second countable space modelled on a Hausdorff real
topological vector space `H` with a basis of `n` vectors. Then `H_i Y = 0` for `i > n`. This is
the case `X = Y` of Poincaré–Alexander duality in the degrees above `n`
(`thm_ext_c19_poincare_alexander_duality`: `H_i Y ≅ H^{n-i} Y = 0`), proved directly by the
local-to-global argument of Hatcher (Lemma 3.27) and the passage from local homology to
Borel–Moore homology:

* `H_j(ℝⁿ - 0) = 0` for `j ≥ n ≥ 1` (`MMP.SingularChain.cycleVanishing_compl_zero`),
  hence `H_{k+1}(ℝⁿ, ℝⁿ - Q) = 0` for every closed box `Q` and `k ≥ n`
  (`MMP.SingularChain.relVanishing_Icc`);
* hence `H_{k+1}(Y, Y - K) = 0` for every compact `K ⊆ Y` and `k ≥ n`
  (`MMP.SingularChain.relVanishing_of_isCompact_of_chartedSpace`);
* hence `H_{k+1} Y = 0` for `k ≥ n`
  (`MMP.borelMooreHomology.isZero_of_chartedSpace_of_relVanishing_Icc`).

No orientation and no connectedness is needed. A complex manifold of complex dimension `m` is a
real `2m`-manifold through the real basis `e₁, i e₁, …, e_m, i e_m` of `ℂ^m`, so `H_i M = 0` for
`i > 2m` (Fulton, proof of Lemma 19.1.1); Fulton's hypothesis that `M` is a finite disjoint union
of connected open subsets is not needed.

## Main results

* `MMP.borelMooreHomology.isZero_of_dim_lt`: `H_i Y = 0` for `i > n`.

The complex case (`lem_c19_manifold_homology_vanishing`) is
`MMP.borelMooreHomology.isZero_of_complexManifold` in
`MMP.AlgebraicTopology.FundamentalClass.ComplexOrientation`.

## Implementation notes

The coefficients are a commutative ring `R` (Fulton: `ℤ`, `ℚ`). Second countability is the
standard convention for manifolds; it gives the σ-compactness used to pass from compact sets to
the whole manifold (an exhaustion by compact sets), together with local compactness, which
holds as `Y` is locally homeomorphic to `ℝⁿ`. The Hausdorff property is needed for the
restriction of Borel–Moore homology and the local-to-global argument.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, (3) and the proof of Lemma 19.1.1.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3, Lemma 3.27.
-/

@[expose] public noncomputable section

open Set Topology CategoryTheory Limits

universe u

namespace MMP

namespace borelMooreHomology

variable (R : Type u) [CommRing R] {H : Type*} [AddCommGroup H] [Module ℝ H]
  [TopologicalSpace H] [ContinuousAdd H] [ContinuousSMul ℝ H] [T2Space H]

/-- **The Borel–Moore homology of a real `n`-manifold vanishes above degree `n`** (Fulton, §19.1;
the case `X = Y` of Poincaré–Alexander duality, `H_i Y ≅ H^{n-i} Y`, in degrees `i > n`). -/
theorem isZero_of_dim_lt {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [ChartedSpace H Y] {n : ℕ} (b : Module.Basis (Fin n) ℝ H) {i : ℤ} (hi : (n : ℤ) < i) :
    IsZero (borelMooreHomology R (ModuleCat.of R R) (TopCat.of Y) i) := by
  haveI : LocallyCompactSpace H :=
    (SingularChain.basisHomeomorph b).isOpenEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace Y := ChartedSpace.locallyCompactSpace H Y
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = ((k + 1 : ℕ) : ℤ) := ⟨i.toNat - 1, by omega⟩
  exact isZero_of_chartedSpace_of_relVanishing_Icc (Y := TopCat.of Y) b
    (fun a c k' hk' ↦ SingularChain.relVanishing_Icc
      (fun n' hn' j hj ↦ SingularChain.cycleVanishing_compl_zero n' hn' j hj) n a c k' hk')
    k (by omega)

end borelMooreHomology

end MMP
