module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.ComponentReductionDefs

/-!
# A smooth projective scheme over `ℂ` is a finite disjoint union of integral pieces

A scheme `V` smooth over a field is locally Noetherian, hence locally connected, so its connected
components are open, hence open and closed, and each of them, as an open subscheme, is connected
and smooth over the field, hence integral. If `V` is moreover quasi-compact, for instance proper
over the field, the connected components form a compact discrete space, hence are finitely many.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.componentsDecomp_of_smooth`: a quasi-compact scheme
  smooth over `ℂ` is the disjoint union of finitely many open and closed integral subschemes.
* `MMP.FourfoldProofs.FractionalLogComplexProof.componentsDecomp`: the same for a scheme smooth of
  relative dimension `n` and projective over `ℂ`.

## Implementation notes

The pieces are indexed by `ConnectedComponents V`; the piece of a component `c` is the preimage
of `{c}` under the quotient map, which is the connected component of any point of it.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

namespace MMP.FourfoldProofs.FractionalLogComplexProof

/-- **A quasi-compact scheme smooth over `ℂ` is a finite disjoint union of open and closed
integral subschemes**, its connected components. -/
theorem componentsDecomp_of_smooth {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ)) [Smooth π]
    [CompactSpace V] : ComponentsDecomp π := by
  classical
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian π
  have : LocallyConnectedSpace V := IsLocallyNoetherianSpace.locallyConnectedSpace _
    (isLocallyNoetherianSpace_of_isLocallyNoetherian V)
  have : Finite (ConnectedComponents V) := finite_of_compact_of_discrete
  let U : ConnectedComponents V → V.Opens := fun c =>
    ⟨ConnectedComponents.mk ⁻¹' {c},
      (isOpen_discrete _).preimage ConnectedComponents.continuous_coe⟩
  refine ⟨ConnectedComponents V, Fintype.ofFinite _, U, fun c =>
    (isClopen_discrete {c}).preimage ConnectedComponents.continuous_coe, fun c d hcd => ?_,
    fun x => ⟨ConnectedComponents.mk x, rfl⟩, fun c => ?_⟩
  · rw [disjoint_iff]
    ext x
    simp only [U, Opens.coe_inf, Opens.coe_bot, Set.mem_inter_iff,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro hc hd
    exact hcd (hc.symm.trans hd)
  · obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    have hopen := Stacks.Chow.isOpen_connectedComponent_of_smooth π x
    have hU : U (ConnectedComponents.mk x) = ⟨connectedComponent x, hopen⟩ :=
      Opens.ext (connectedComponents_preimage_singleton (x := x))
    rw [hU]
    exact Stacks.Chow.isIntegral_connectedComponent_of_smooth π x hopen

/-- **A scheme smooth of relative dimension `n` and projective over `ℂ` is a finite disjoint union
of open and closed integral subschemes.** -/
theorem componentsDecomp (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension n π] (hπ : IsProjective π) : ComponentsDecomp π := by
  have : Smooth π := SmoothOfRelativeDimension.smooth n π
  have : IsProper π := hπ.isProper
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace π
  exact componentsDecomp_of_smooth π

end MMP.FourfoldProofs.FractionalLogComplexProof
