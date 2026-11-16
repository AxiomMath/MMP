module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.Basic
public import MMP.AlgebraicGeometry.Variety.SmoothEmbedding

/-!
# The blow-up of a complex scheme is a complex scheme

Let `Y` be a complex scheme (Fulton, §19.1), with a closed imbedding `j : Y → M` into a smooth
complex variety `M`, and let `X ⊆ Y` be a closed subscheme. Then `Bl_X Y` is a complex scheme: by
Fulton, Appendix B.8.2 (`MMP.exists_isClosedImmersion_isSmoothVariety_blowUp`), `Bl_X Y` imbeds as
a closed subscheme of a smooth variety (a projective bundle over `M`), and the imbedding lies over
`ℂ`. The blow-up is Stacks' `AlgebraicGeometry.blowUp I`, with projection
`AlgebraicGeometry.blowUpToBase I`.

## Main results

* `MMP.isComplexScheme_blowUp`: the blow-up of a complex scheme along a closed subscheme is a
  complex scheme, for any structure over `ℂ` making `π : Bl_X Y → Y` a morphism over `ℂ`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1 and Appendix B.8.2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MMP

/-- The blow-up `Bl_X Y` of a complex scheme `Y` along a closed subscheme `X` with ideal sheaf `I`
is a complex scheme, for any structure over `ℂ` on `Bl_X Y` making the projection `π : Bl_X Y → Y`
a morphism over `ℂ`. -/
theorem isComplexScheme_blowUp {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))] [IsComplexScheme Y]
    (I : Y.IdealSheafData) [(blowUp I).Over (Spec (.of ℂ))]
    [(blowUpToBase I).IsOver (Spec (.of ℂ))] :
    IsComplexScheme (blowUp I) := by
  obtain ⟨M, _, hM, j, hj, hjc⟩ := (inferInstance : IsComplexScheme Y).exists_isClosedImmersion
  obtain ⟨P, t, g, hP, hg, hgt⟩ :=
    exists_isClosedImmersion_isSmoothVariety_blowUp (M ↘ Spec (.of ℂ)) j I
  have hover : g ≫ t = blowUp I ↘ Spec (.of ℂ) := by
    rw [hgt, hj.comp_over]
    exact (Scheme.Hom.isOver_iff (Spec (.of ℂ))).1 inferInstance
  haveI : LocallyOfFiniteType (blowUp I ↘ Spec (.of ℂ)) :=
    hover ▸ (inferInstance : LocallyOfFiniteType (g ≫ t))
  haveI : QuasiCompact (blowUp I ↘ Spec (.of ℂ)) :=
    hover ▸ (inferInstance : QuasiCompact (g ≫ t))
  letI : P.Over (Spec (.of ℂ)) := ⟨t⟩
  exact { exists_isClosedImmersion := ⟨P, inferInstance, hP, g, ⟨hover⟩, hg⟩ }

end MMP
