module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyAffine
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Compactness of underlying spaces covered by projective-type charts

Let `K` be a normed field and `X` a scheme over `K` covered by opens `U₀, …, Uₙ` carrying
sections `y_{ij} ∈ Γ(X, Uᵢ)` which behave like the affine coordinates `T_j / Tᵢ` of projective
space: `y_{ii} = 1`, a point of `Uᵢ(K)` at which `y_{ik}` does not vanish lies in `U_k(K)`, and
`y_{ij} = y_{ik} · y_{kj}` on `Uᵢ(K) ∩ U_k(K)`. If each closed polydisc
`Bᵢ = {p ∈ Uᵢ(K) : |y_{ij}(p)| ≤ 1 for all j}` is compact, then `X(K)` is compact: a point of
`Uᵢ(K)` lies in `B_k` for an index `k` at which `|y_{ik}(p)|` is largest.

## Main results

* `MMP.UnderlyingSpace.compactSpace_of_charts`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

universe u

namespace MMP

namespace UnderlyingSpace

variable {K : Type u} [NormedField K] {X : Scheme.{u}} [X.Over (Spec (.of K))]

/-- A scheme over a normed field `K` covered by charts with projective-type coordinates whose
closed unit polydiscs are compact has compact underlying space `X(K)`. -/
theorem compactSpace_of_charts {n : ℕ} (U : Fin (n + 1) → X.Opens) (hU : ⨆ i, U i = ⊤)
    (y : ∀ i, Fin (n + 1) → Γ(X, U i))
    (hyy : ∀ i (p : UnderlyingSpace K X) (hp : ⊤ ≤ p.toHom ⁻¹ᵁ U i), eval p hp (y i i) = 1)
    (hmem : ∀ i k (p : UnderlyingSpace K X) (hp : ⊤ ≤ p.toHom ⁻¹ᵁ U i),
      eval p hp (y i k) ≠ 0 → ⊤ ≤ p.toHom ⁻¹ᵁ U k)
    (hrel : ∀ i k j (p : UnderlyingSpace K X) (hpi : ⊤ ≤ p.toHom ⁻¹ᵁ U i)
      (hpk : ⊤ ≤ p.toHom ⁻¹ᵁ U k), eval p hpi (y i j) = eval p hpi (y i k) * eval p hpk (y k j))
    (hB : ∀ i, IsCompact {p : UnderlyingSpace K X |
      ∃ hp : ⊤ ≤ p.toHom ⁻¹ᵁ U i, ∀ j, ‖eval p hp (y i j)‖ ≤ 1}) :
    CompactSpace (UnderlyingSpace K X) := by
  refine ⟨?_⟩
  convert isCompact_iUnion hB
  refine (Set.eq_univ_of_forall fun p ↦ ?_).symm
  have hx : p.toHom (IsLocalRing.closedPoint K) ∈ ⨆ i, U i := by
    rw [hU]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  have hpi : ⊤ ≤ p.toHom ⁻¹ᵁ U i := (top_le_preimage_iff p _).mpr hi
  obtain ⟨k, -, hk⟩ := Set.Finite.exists_maximalFor (fun k ↦ ‖eval p hpi (y i k)‖)
    Set.univ Set.finite_univ ⟨i, trivial⟩
  have hmax : ∀ j, ‖eval p hpi (y i j)‖ ≤ ‖eval p hpi (y i k)‖ := fun j ↦ by
    by_contra h
    exact (not_le.mp h).not_ge (hk trivial (not_le.mp h).le)
  have hone : 1 ≤ ‖eval p hpi (y i k)‖ := by
    simpa [hyy i p hpi] using hmax i
  have hne : eval p hpi (y i k) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hone
    exact absurd hone (by norm_num)
  have hpk := hmem i k p hpi hne
  refine Set.mem_iUnion.mpr ⟨k, hpk, fun j ↦ ?_⟩
  have h := hrel i k j p hpi hpk
  have hpos : 0 < ‖eval p hpi (y i k)‖ := norm_pos_iff.mpr hne
  have := hmax j
  rw [h, norm_mul] at this
  nlinarith [norm_nonneg (eval p hpk (y k j))]

end UnderlyingSpace

end MMP
