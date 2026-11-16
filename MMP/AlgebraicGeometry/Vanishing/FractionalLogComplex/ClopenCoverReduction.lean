module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.ClopenRetractDegeneration
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.ComponentReductionDefs

/-!
# Reduction of the degeneration to the pieces of a finite clopen cover

Let `π : V ⟶ Spec ℂ` be projective, smooth of relative dimension `n`, and let `V = ⨆ᵢ Uᵢ` be a
finite cover by disjoint open and closed subschemes on which `D` restricts to relative simple
normal crossing divisors. If every model of the restricted fractional logarithmic complex on every
`Uᵢ` is a retract of the direct image of a twisted logarithmic de Rham complex along a finite
cover, then every model `K` of the fractional logarithmic complex on `V` degenerates at `E₁`: the
restriction `K|_{Uᵢ}` of a model is a model of the restricted complex, so a retract of
`gᵢ_* Ω^•_{Vᵢ'}(log Sᵢ')(-Sᵢ')`, and the degeneration follows from
`MMP.FourfoldProofs.FractionalLogComplexProof.finrank_hyp_eq_sum_of_retract_pieces`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.componentsReduction_of_restrict`:
  `MMP.FourfoldProofs.FractionalLogComplexProof.ComponentsReduction` from the restriction of models to
  the pieces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.FourfoldProofs.FractionalLogComplexProof

/-- **The degeneration on `V` from the restriction of models to the pieces.** If the restriction
`K|_U` of every model `K` of the fractional logarithmic complex on `V` to an open `U` on which
`D|_U` is relative simple normal crossing is a model of the restricted complex, then
`ComponentsReduction` holds. -/
theorem componentsReduction_of_restrict (n : ℕ) {V : Scheme.{0}}
    (π : V ⟶ Spec (CommRingCat.of ℂ)) [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V]
    [IsNormal V] (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S M : MMP.Mori.Divisor V)
    (N : ℕ) (u : Γ(V, cU' D M))
    (hres : ∀ (U : V.Opens)
      (hDU : MMP.Mori.Divisor.IsRelativeSNC n (U.ι ≫ π) (restrictDivisor U D)) K F e ι,
      IsCModel n π D hD S M N u K F e ι →
      ∃ F' e' ι', IsCModel n (U.ι ≫ π) (restrictDivisor U D) hDU (restrictDivisor U S)
        (restrictDivisor U M) N (restrictSection U D M u)
        (((relRestrict π U).mapHomologicalComplex _).obj K) F' e' ι') :
    ComponentsReduction n π D hD S M N u := by
  intro hπ J _ U hclo hdisj hcov hDU hret K F e ι hK k
  choose F' e' ι' hK' using fun i => hres (U i) (hDU i) K F e ι hK
  choose V' g hg hsm S' hS' hgπ a r har using fun i => hret i _ (F' i) (e' i) (ι' i) (hK' i)
  exact finrank_hyp_eq_sum_of_retract_pieces n π hπ U (fun i => (hclo i).isClosed) hdisj hcov K
    V' g hg hsm S' hS' hgπ a r har k

end MMP.FourfoldProofs.FractionalLogComplexProof
