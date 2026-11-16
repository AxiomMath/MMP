module

public import MMP.AlgebraicGeometry.DeRham.RationalForms.OpenFormsConnection

/-!
# Rational forms over `ℂ`

The rational forms of `MMP.FourfoldProofs.FractionalLogComplexProof.openRatForm`, for a scheme over
`Spec ℂ`, stated in the form `openFormsMap U s q (ratForm (U.ι ≫ s) q O θ)` in which the pull-back
and trace maps of the fractional logarithmic complex are stated
(`MMP.FourfoldProofs.FractionalLogComplexProof.IMapSpec`,
`MMP.FourfoldProofs.FractionalLogComplexProof.RMapSpec`).

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.ratV`: the rational form of a form over an open.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.eq_of_ratV_eq`: forms are determined by their
  rational forms.
* `MMP.FourfoldProofs.FractionalLogComplexProof.ratV_nabla`: the rational forms of
  `N u β' = N u dβ - du ∧ β`.

## Implementation notes

The statements over a general field `k` (in `MMP.FourfoldProofs.FractionalLogComplexProof.openRatForm`)
specialize to `k = ℂ` with the ring structure of `ℂ` that comes from its field structure, while
`Spec ℂ` is the spectrum of `ℂ` with its own ring structure; the two agree up to unfolding
instances, and the statements here are those of `Spec ℂ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential

namespace MMP.FourfoldProofs.FractionalLogComplexProof

variable {Y : Scheme.{0}} [IsIntegral Y] (U : Y.Opens) [Nonempty U]
  (sY : Y ⟶ Spec (CommRingCat.of ℂ))

/-- The rational form, in `k(Y)`, of the restriction to a non-empty affine open `O ⊆ Ω` of a form
over an open `Ω` of `U`. -/
noncomputable def ratV (q : ℕ) {Ω : U.toScheme.Opens} (O : U.toScheme.affineOpens)
    (hO : (O : U.toScheme.Opens) ≤ Ω) [Nonempty (O : U.toScheme.Opens)]
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.obj
      (op Ω)) :
    letI := MMP.Mori.functionFieldAlgebra sY
    ⋀[Y.functionField]^q Ω[Y.functionField⁄ℂ] :=
  openFormsMap U sY q (ratForm (U.ι ≫ sY) q O
    (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hO).op θ))

/-- `ratV` is the image under `openFormsMap` of the rational form of the restriction of `θ`
to `O`. -/
theorem ratV_def (q : ℕ) {Ω : U.toScheme.Opens} (O : U.toScheme.affineOpens)
    (hO : (O : U.toScheme.Opens) ≤ Ω) [Nonempty (O : U.toScheme.Opens)]
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.obj
      (op Ω)) :
    ratV U sY q O hO θ = openFormsMap U sY q (ratForm (U.ι ≫ sY) q O
      (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hO).op θ)) := rfl

/-- **Forms are determined by their rational forms**, through `ratV`. -/
theorem eq_of_ratV_eq {m : ℕ} [SmoothOfRelativeDimension m (U.ι ≫ sY)] (q : ℕ)
    {Ω : U.toScheme.Opens}
    (θ θ' : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.obj
      (op Ω))
    (h : ∀ (O : U.toScheme.affineOpens) (hO : (O : U.toScheme.Opens) ≤ Ω)
      [Nonempty (O : U.toScheme.Opens)], ratV U sY q O hO θ = ratV U sY q O hO θ') :
    θ = θ' := by
  unfold ratV at h
  refine eq_of_openRatForm_eq_piece U sY (m := m) q θ θ' ?_
  intro O hO hne
  with_reducible exact @h O hO hne

/-- `ratV` is additive in the form. -/
@[simp]
theorem ratV_add (q : ℕ) {Ω : U.toScheme.Opens} (O : U.toScheme.affineOpens)
    (hO : (O : U.toScheme.Opens) ≤ Ω) [Nonempty (O : U.toScheme.Opens)]
    (θ θ' : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.obj
      (op Ω)) :
    ratV U sY q O hO (θ + θ') = ratV U sY q O hO θ + ratV U sY q O hO θ' := by
  unfold ratV
  have e : ((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hO).op
      (θ + θ') = ((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hO).op θ +
        ((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hO).op θ' :=
    map_add _ θ θ'
  rw [e, map_add, map_add]

/-- The rational form of the restriction of `θ` to `Ω' ⊆ Ω` is the rational form of `θ`. -/
@[simp]
theorem ratV_map (q : ℕ) {Ω Ω' : U.toScheme.Opens} (h : Ω' ≤ Ω) (O : U.toScheme.affineOpens)
    (hO : (O : U.toScheme.Opens) ≤ Ω') [Nonempty (O : U.toScheme.Opens)]
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.obj
      (op Ω)) :
    ratV U sY q O hO
        (((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.map
          (homOfLE h).op θ) = ratV U sY q O (hO.trans h) θ := by
  unfold ratV
  have := openRatForm_map_map U sY q h O hO θ
  with_reducible exact this

/-- `ratV` does not depend on the non-empty affine open `O` through which it is computed. -/
theorem ratV_mono (q : ℕ) {Ω : U.toScheme.Opens} {O O' : U.toScheme.affineOpens}
    (hO : (O : U.toScheme.Opens) ≤ Ω) (h : (O' : U.toScheme.Opens) ≤ O)
    [Nonempty (O : U.toScheme.Opens)] [Nonempty (O' : U.toScheme.Opens)]
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.obj
      (op Ω)) :
    ratV U sY q O' (h.trans hO) θ = ratV U sY q O hO θ := by
  unfold ratV
  have := openRatForm_mono U sY q hO h θ
  with_reducible exact this

/-- `ratV` commutes with the exterior derivative: the rational form of `dθ` is the de Rham
differential of the rational form of `θ`. -/
theorem ratV_d (q : ℕ) {Ω : U.toScheme.Opens} (O : U.toScheme.affineOpens)
    (hO : (O : U.toScheme.Opens) ≤ Ω) [Nonempty (O : U.toScheme.Opens)]
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.obj
      (op Ω)) :
    letI := MMP.Mori.functionFieldAlgebra sY
    ratV U sY (q + 1) O hO ((((U.ι ≫ sY).deRhamComplex).d q (q + 1)).val.app (op Ω) θ) =
      deRhamDifferential (A := ℂ) q (ratV U sY q O hO θ) := by
  unfold ratV
  have := openRatForm_map_d U sY q O hO θ
  with_reducible exact this

/-- If `β₂ = c β` in the total exterior algebra, then the rational form of `β₂` is the image of
`c` in `k(Y)` times the rational form of `β`. -/
theorem ratV_eq_smul_of_incl_eq (q : ℕ) {Ω : U.toScheme.Opens} (O : U.toScheme.affineOpens)
    (hO : (O : U.toScheme.Opens) ≤ Ω) [Nonempty (O : U.toScheme.Opens)] (c : Γ(U.toScheme, Ω))
    (β β₂ : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.obj
      (op Ω))
    (h : (TB (U.ι ≫ sY)).incl (q : ℤ) β₂ =
      (TB (U.ι ≫ sY)).structureMap (op Ω) c * (TB (U.ι ≫ sY)).incl (q : ℤ) β) :
    letI := MMP.Mori.functionFieldAlgebra sY
    ratV U sY q O hO β₂ = openFunctionFieldEquiv U (U.toScheme.germToFunctionField O
      (U.toScheme.presheaf.map (homOfLE hO).op c)) • ratV U sY q O hO β := by
  unfold ratV
  have := openRatForm_eq_smul_of_incl_eq U sY q O hO c β β₂ h
  with_reducible exact this

/-- The rational form of `c • θ` is the image of `c` in `k(Y)` times the rational form of `θ`. -/
theorem ratV_smul (q : ℕ) {Ω : U.toScheme.Opens} (O : U.toScheme.affineOpens)
    (hO : (O : U.toScheme.Opens) ≤ Ω) [Nonempty (O : U.toScheme.Opens)]
    (c : (Stacks.RingedSpace.structureRingSheaf U.toScheme.toRingedSpace).obj.obj (op Ω))
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.obj
      (op Ω)) :
    letI := MMP.Mori.functionFieldAlgebra sY
    ratV U sY q O hO (c • θ) = openFunctionFieldEquiv U (U.toScheme.germToFunctionField O
      (U.toScheme.presheaf.map (homOfLE hO).op c)) • ratV U sY q O hO θ := by
  unfold ratV
  have := openRatForm_map_smul U sY q O hO c θ
  with_reducible exact this

/-- **The rational forms of `N u β' = N u dβ - du ∧ β`**, through `ratV`. -/
theorem ratV_nabla (q N : ℕ) {Ω : U.toScheme.Opens} (O : U.toScheme.affineOpens)
    (hO : (O : U.toScheme.Opens) ≤ Ω) [Nonempty (O : U.toScheme.Opens)] (a : Γ(U.toScheme, Ω))
    (β : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.obj (op Ω))
    (β' : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece
      ((q + 1 : ℕ) : ℤ)).val.obj (op Ω))
    (h : N • ((TB (U.ι ≫ sY)).structureMap (op Ω) a *
        (TB (U.ι ≫ sY)).incl ((q + 1 : ℕ) : ℤ) β') =
      N • ((TB (U.ι ≫ sY)).structureMap (op Ω) a *
        (TB (U.ι ≫ sY)).incl ((q + 1 : ℕ) : ℤ)
          ((((U.ι ≫ sY).deRhamComplex).d q (q + 1)).val.app (op Ω) β)) -
      (TB (U.ι ≫ sY)).incl 1
          ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials (U.ι ≫ sY))).val.app
            (op Ω) ((Scheme.Hom.universalRelativeDerivation (U.ι ≫ sY)).d (X := op Ω) a)) *
        (TB (U.ι ≫ sY)).incl (q : ℤ) β) :
    letI := MMP.Mori.functionFieldAlgebra sY
    N • (openFunctionFieldEquiv U (U.toScheme.germToFunctionField O
          (U.toScheme.presheaf.map (homOfLE hO).op a)) •
        (ratV U sY (q + 1) O hO β' : ExteriorAlgebra Y.functionField Ω[Y.functionField⁄ℂ])) =
      N • (openFunctionFieldEquiv U (U.toScheme.germToFunctionField O
          (U.toScheme.presheaf.map (homOfLE hO).op a)) •
        (deRhamDifferential (A := ℂ) q (ratV U sY q O hO β) :
            ExteriorAlgebra Y.functionField Ω[Y.functionField⁄ℂ])) -
        ExteriorAlgebra.ι Y.functionField (KaehlerDifferential.D ℂ Y.functionField
          (openFunctionFieldEquiv U (U.toScheme.germToFunctionField O
            (U.toScheme.presheaf.map (homOfLE hO).op a)))) *
          (ratV U sY q O hO β : ExteriorAlgebra Y.functionField Ω[Y.functionField⁄ℂ]) := by
  unfold ratV
  have := openRatForm_nabla U sY q N O hO a β β' h
  with_reducible exact this

end MMP.FourfoldProofs.FractionalLogComplexProof
