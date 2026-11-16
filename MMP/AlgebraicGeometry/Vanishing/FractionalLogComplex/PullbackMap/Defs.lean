module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Construction
public import MMP.AlgebraicGeometry.FunctionField.OpenSubscheme
public import MMP.AlgebraicGeometry.DeRham.RationalForms.Basic

/-!
# The pull-back map into the logarithmic complex of the cover

Let `π : V ⟶ Spec ℂ` carry the data of the fractional logarithmic complex
`C^• = 𝒪_V(-M) · Ω^•_V(log D)(-S)`, and let `g : V' ⟶ V` be a finite surjective cover by an
integral smooth variety on which the reduced inverse image `S'` of `S` is a relative simple normal
crossing divisor and `z^N = g^*ψ` in the function field of `V'`. The pull-back
`θ ↦ g^*θ / z` carries the sections of `C^p` over an open `W` of `V` to sections of
`Ω^p_{V'}(log S')(-S')` over `g⁻¹ W`. Sections of both sheaves are forms on dense opens, and are
determined by their rational forms; the statement
`MMP.FourfoldProofs.FractionalLogComplexProof.IMapSpec` below is the existence of the extension, with
the rational form `z⁻¹ · g^*θ`.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.IMapSpec`: the pull-back lands in
  `Ω^p_{V'}(log S')(-S')`.

## Implementation notes

The sections of `C^p` over `W` are the forms on `U ∩ W ∩ U'` (`U = V ∖ D`,
`U' = V ∖ (D ∪ Supp M)`) satisfying `MMP.FourfoldProofs.FractionalLogComplexProof.Cond`. Rational
forms of forms on `U` and on `V' ∖ S'` are compared in the function fields of `V` and `V'`
through `MMP.FourfoldProofs.FractionalLogComplexProof.openFormsMap`, and `k(V) ⊆ k(V')` through
`MMP.Mori.functionFieldMapAlgebra g`. The compatibility of the pull-back with `∇` and `d`, and the
identity `(1/deg) Tr(z · g^*θ / z) = θ`, are identities of rational forms and are proved with the
trace map, not here.

`IMapSpec` is a statement, not a hypothesis-free fact: it holds for the cover of
`MMP.FourfoldProofs.FractionalLogComplexProof.CoverDatum` (`S'` the reduced inverse image of `S`,
`z^N = g^*ψ`) and the data of the fractional logarithmic complex (`N M = Bn + div ψ`,
`0 ≤ Bn < N`, `D = S + Supp Bn` reduced, `S ≥ 0`); a proof takes these as hypotheses.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

/-- **The pull-back `θ ↦ g^*θ / z` lands in `Ω^p_{V'}(log S')(-S')`.** For every open `W` of `V`
and every section `θ` of `C^p` over `W`, a form on `U ∩ W ∩ U'` satisfying `Cond`, there is a
section `θ'` of `Ω^p_{V'}(log S')(-S')` over `g⁻¹ W` whose rational form, on every non-empty affine
open of `(V' ∖ S') ∩ g⁻¹ W`, is `z⁻¹ · g^*` of the rational form of `θ` on any non-empty affine
open of `U ∩ W ∩ U'`. -/
def IMapSpec (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension n π] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S M : MMP.Mori.Divisor V)
    [Nonempty (cU D)]
    {V' : Scheme.{0}} (g : V' ⟶ V) [Surjective g] [IsIntegral V']
    [SmoothOfRelativeDimension n (g ≫ π)]
    (S' : MMP.Mori.Divisor V') (hS' : S'.IsRelativeSNC n (g ≫ π)) [Nonempty (cU S')]
    (z : V'.functionField) : Prop :=
  letI := MMP.Mori.functionFieldAlgebra π
  letI := MMP.Mori.functionFieldAlgebra (g ≫ π)
  letI := MMP.Mori.functionFieldMapAlgebra g
  haveI := MMP.Mori.isScalarTower_functionFieldMap π g
  ∀ (p : ℕ) (W : V.Opens)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W))),
    Cond n π D hD S M p W θ →
    ∃ θ' ∈ MMP.Mori.Divisor.relativeLogForms n (g ≫ π) S' hS' S'.suppIdeal p (g ⁻¹ᵁ W),
      ∀ (O : (cU D).toScheme.affineOpens) (hO : (O : (cU D).toScheme.Opens) ≤ OO D M W)
        [Nonempty (O : (cU D).toScheme.Opens)]
        (O' : (cU S').toScheme.affineOpens)
        (hO' : (O' : (cU S').toScheme.Opens) ≤ (cU S').ι ⁻¹ᵁ (g ⁻¹ᵁ W))
        [Nonempty (O' : (cU S').toScheme.Opens)],
        openFormsMap (cU S') (g ≫ π) p (ratForm ((cU S').ι ≫ g ≫ π) p O'
            ((((cU S').ι ≫ g ≫ π).relativeDifferentialForms (p : ℤ)).presheaf.map
              (homOfLE hO').op θ')) =
          z⁻¹ • KaehlerDifferential.mapExteriorPower ℂ V.functionField V'.functionField p
            (openFormsMap (cU D) π p (ratForm ((cU D).ι ≫ π) p O
              ((((cU D).ι ≫ π).relativeDifferentialForms (p : ℤ)).presheaf.map
                (homOfLE hO).op θ)))

end MMP.FourfoldProofs.FractionalLogComplexProof
