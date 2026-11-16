module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Retract.Defs
public import MMP.AlgebraicGeometry.Divisor.RestrictOpen
public import MMP.AlgebraicGeometry.Cohomology.HypercohomologyAffineDirectImage

/-!
# Reduction of the degeneration to the connected components

A smooth projective scheme `V` over `ℂ` is the disjoint union of finitely many open and closed
integral subschemes `U_i`, its connected components. The hypercohomology of a complex of sheaves
of `π⁻¹𝒪`-modules on `V`, and the cohomology of its terms, are the direct sums of those of its
restrictions to the `U_i`; a model of the fractional logarithmic complex `C^•` restricts to a model
on each `U_i`, for the restricted data. So the degeneration at `E₁` on `V` follows from that on the
`U_i`.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.ComponentsDecomp`: the decomposition into open and
  closed integral subschemes.
* `MMP.FourfoldProofs.FractionalLogComplexProof.ComponentsReduction`: degeneration on `V` from
  retracts onto direct images of logarithmic complexes of covers of the pieces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.FourfoldProofs.FractionalLogComplexProof

/-- **`V` is a finite disjoint union of open and closed integral subschemes.** -/
def ComponentsDecomp {V : Scheme.{0}} (_π : V ⟶ Spec (CommRingCat.of ℂ)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (U : ι → V.Opens),
    (∀ i, IsClopen (U i : Set V)) ∧ (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
      (∀ x : V, ∃ i, x ∈ U i) ∧ ∀ i, IsIntegral (U i).toScheme

/-- **Degeneration on `V` from retracts on the pieces.** Let `π` be projective. For a
decomposition of `V` into finitely many disjoint open and closed subschemes `U_i` on which the
restriction of `D` is a relative simple normal crossing divisor, if every model of the restricted
fractional logarithmic complex on every `U_i` is a retract of the direct image
`g_* Ω^•_{V'}(log S')(-S')` along a finite cover `g : V' ⟶ U_i` by a smooth projective `V'` with a
relative snc divisor `S'`, then every model on `V` degenerates at `E₁`. -/
def ComponentsReduction (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S M : MMP.Mori.Divisor V) (N : ℕ)
    (u : Γ(V, cU' D M)) : Prop :=
  IsProjective π →
  ∀ (ι : Type) [Fintype ι] (U : ι → V.Opens),
    (∀ i, IsClopen (U i : Set V)) → (∀ i j, i ≠ j → Disjoint (U i) (U j)) →
    (∀ x : V, ∃ i, x ∈ U i) →
    ∀ (hDU : ∀ i, MMP.Mori.Divisor.IsRelativeSNC n ((U i).ι ≫ π) (restrictDivisor (U i) D)),
    (∀ i K F e ι', IsCModel n ((U i).ι ≫ π) (restrictDivisor (U i) D) (hDU i)
        (restrictDivisor (U i) S) (restrictDivisor (U i) M) N (restrictSection (U i) D M u)
        K F e ι' →
      ∃ (V' : Scheme.{0}) (g : V' ⟶ (U i).toScheme) (_ : IsFinite g)
        (_ : SmoothOfRelativeDimension n (g ≫ (U i).ι ≫ π)) (S' : MMP.Mori.Divisor V')
        (hS' : S'.IsRelativeSNC n (g ≫ (U i).ι ≫ π)),
        IsProjective (g ≫ (U i).ι ≫ π) ∧
        ∃ (a : K ⟶ ((relDirectImage g ((U i).ι ≫ π)).mapHomologicalComplex _).obj
            (MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ (U i).ι ≫ π) S' hS'
              S'.suppIdeal))
          (r : ((relDirectImage g ((U i).ι ≫ π)).mapHomologicalComplex _).obj
            (MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ (U i).ι ≫ π) S' hS'
              S'.suppIdeal) ⟶ K),
          a ≫ r = 𝟙 K) →
    FracDegeneration n π D hD S M N u

end MMP.FourfoldProofs.FractionalLogComplexProof
