module

public import MMP.AlgebraicGeometry.MMP.Fourfold.StepSequence
import MMP.AlgebraicGeometry.MMP.Fourfold.StabilizedTail.BadSurfacesFinite
import MMP.AlgebraicGeometry.Singularities.Surface.MldDenominatorBound
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction

/-!
# Bad surfaces are eventually generically smooth

Let `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` be a stabilized small klt tail of fourfold step
diagrams over `ℂ`, with bad loci `W_i⁻ ⊆ X_i` and `W_i⁺ ⊆ X_{i+1}`. There is an index `i₁` such
that for every `i ≥ i₁`, the generic point of every irreducible surface `V ⊆ W_i⁻` lies in the
smooth locus of `X_i ⟶ Spec ℂ`, and the generic point of every irreducible surface `V ⊆ W_i⁺`
lies in the smooth locus of `X_{i+1} ⟶ Spec ℂ`.

The proof: for `i ≫ 0` the minimal log discrepancy of `(X_i^±, B_i^±)` at such a generic point
exceeds one, while a singular point of coheight two of a pair has minimal log discrepancy at
most one.

## Main results

* `IsStabilizedSmallKltTail.exists_forall_ge_genericPoint_mem_smoothLocus`, in the namespace
  `MMP.Fourfold.StepSequence`: for `i ≫ 0` the generic point of every irreducible surface in
  `W_i⁻` or `W_i⁺` is a smooth point.

## Implementation notes

The two signs `σ = -` and `σ = +` are stated together as a conjunction under one index `i₁`.
On the negative side the variety is `X_i` with bad locus `W_i⁻`; on the positive side it is
`X_{i+1}` with bad locus `W_i⁺`. An irreducible surface is an irreducible closed subset of
topological Krull dimension two, and a smooth point is a point of `MMP.Mori.smoothLocus` of the
structure morphism to `Spec ℂ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold.StepSequence.IsStabilizedSmallKltTail

/-- The generic point of an irreducible closed surface in an integral fourfold of finite type
over `ℂ` has coheight two. -/
private theorem coheight_genericPoint_eq_two {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsIntegral X] [LocallyOfFiniteType sX] (hX : topologicalKrullDim X = 4)
    (V : IrreducibleCloseds X) (hV : topologicalKrullDim (V : Set X) = 2) :
    Order.coheight V.isIrreducible.genericPoint = 2 := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    V.isIrreducible.genericPoint
  rw [V.isIrreducible.isGenericPoint_genericPoint V.isClosed, hV, hX] at h
  exact WithTop.add_left_cancel (by decide) (WithBot.coe_injective h : 2 + _ = (2 + 2 : ℕ∞))

/-- On a fourfold `X_i` of the tail, the generic point of an irreducible closed surface at which
the minimal log discrepancy exceeds one is a smooth point. -/
private theorem genericPoint_mem_smoothLocus {S : StepSequence}
    (hS : S.IsStabilizedSmallKltTail) (i : ℕ) (hX : topologicalKrullDim (S.X i) = 4)
    [IsIntegral (S.X i)] [LocallyOfFiniteType (S.sX i)]
    (V : IrreducibleCloseds (S.X i)) (hV : topologicalKrullDim (V : Set (S.X i)) = 2)
    (hmld : 1 < MMP.Fourfold.minimalLogDiscrepancy (S.sX i) (S.B i)
      V.isIrreducible.genericPoint) :
    V.isIrreducible.genericPoint ∈ MMP.Mori.smoothLocus (S.sX i) := by
  by_contra hsing
  exact (MMP.Threefold.minimalLogDiscrepancy_le_one_of_coheight_eq_two (S.sX i)
    (hS.isKlt i).1 (coheight_genericPoint_eq_two (S.sX i) hX V hV) hsing).not_gt hmld

/-- **Bad surfaces are eventually generically smooth.** For a stabilized small klt tail `S`
there is `i₁` such that for all `i ≥ i₁`, every irreducible closed surface `V ⊆ W_i⁻ ⊆ X_i` has
generic point in the smooth locus of `X_i`, and every irreducible closed surface
`V ⊆ W_i⁺ ⊆ X_{i+1}` has generic point in the smooth locus of `X_{i+1}`. -/
@[mmp "prop_oai4_codim_two_c"]
public theorem exists_forall_ge_genericPoint_mem_smoothLocus {S : StepSequence}
    (hS : S.IsStabilizedSmallKltTail) :
    ∃ i₁ : ℕ, ∀ i ≥ i₁,
      (∀ V : IrreducibleCloseds (S.X i),
        topologicalKrullDim (V : Set (S.X i)) = 2 →
          (V : Set (S.X i)) ⊆ S.badLocusMinusAt i →
          V.isIrreducible.genericPoint ∈ MMP.Mori.smoothLocus (S.sX i)) ∧
      (∀ V : IrreducibleCloseds (S.X (i + 1)),
        topologicalKrullDim (V : Set (S.X (i + 1))) = 2 →
          (V : Set (S.X (i + 1))) ⊆ S.badLocusPlusAt i →
          V.isIrreducible.genericPoint ∈ MMP.Mori.smoothLocus (S.sX (i + 1))) := by
  obtain ⟨i₁, h⟩ := hS.exists_forall_ge_one_lt_minimalLogDiscrepancy
  refine ⟨i₁, fun i hi => ⟨fun V hV hW => ?_, fun V hV hW => ?_⟩⟩
  · have := (S.isFourfoldStepDiagram i).isNormalVariety_minus.1
    exact genericPoint_mem_smoothLocus hS i (S.isFourfoldStepDiagram i).dim_minus V hV
      ((h i hi).1 V hV hW)
  · have := (S.isFourfoldStepDiagram i).isNormalVariety_plus.1
    exact genericPoint_mem_smoothLocus hS (i + 1) (S.isFourfoldStepDiagram i).dim_plus V hV
      ((h i hi).2 V hV hW)

end MMP.Fourfold.StepSequence.IsStabilizedSmallKltTail

end
