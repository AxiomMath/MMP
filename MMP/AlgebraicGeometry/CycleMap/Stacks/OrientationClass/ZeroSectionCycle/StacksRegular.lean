module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ZeroSectionCycle.StacksImage
public import MMP.AlgebraicGeometry.Variety.RegularLocusSmooth

/-!
# The total space of `E|_V` is regular over the regular locus of `V` (Stacks vector bundles)

Let `ℰ` be a quasi-coherent `𝒪_X`-module, finite locally free of rank `r`, on a complex scheme
`X`, with vector bundle `π : 𝐕(ℰ) ⟶ X`, and `V` a subvariety of `X`. The projection
`π⁻¹(V) ≅ 𝐕(ℰ) ×_X V → V` is a base change of the smooth morphism `π`, so
(`MMP.mem_regularLocus_of_smooth`) the total space `π⁻¹(V)` is regular at every complex point
lying over a regular point of `V`.

## Main results

* `MMP.Modules.smooth_proj`: `π` is smooth.
* `MMP.Modules.mem_regularPart_preimageSubvariety`: a complex point of `π⁻¹(V)` over a regular
  complex point of `V` is a regular point of `π⁻¹(V)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Lemma 19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open MMP.UnderlyingSpace

namespace MMP.Modules

open MMP.Intersection.Scheme

variable {X : Scheme.{0}} (E : X.Modules) [E.IsQuasicoherent] (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]

include r in
/-- The projection of the vector bundle of a finite locally free module is smooth. -/
theorem smooth_proj : Smooth (proj E) :=
  have := Stacks.Chow.smoothOfRelativeDimension_of_isAffineSpaceBundle (proj E) r
    (isAffineSpaceBundle_proj E r)
  SmoothOfRelativeDimension.smooth r (proj E)

variable [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme (totalSpace E)]

/-- The total space `E|_V = π⁻¹(V)` of a Stacks vector bundle restricted to a subvariety `V` is
regular at every complex point lying over a regular complex point of `V`. -/
theorem mem_regularPart_preimageSubvariety (V : Subvariety X)
    (p : UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme)
    (q : UnderlyingSpace ℂ V.toScheme) (hq : q ∈ regularPart ℂ V.toScheme)
    (hpq : mapFun (proj E) (mapFun (preimageSubvariety E r V).ι p) = mapFun V.ι q) :
    p ∈ regularPart ℂ (preimageSubvariety E r V).toScheme := by
  rw [mem_regularPart_iff] at hq ⊢
  haveI := smooth_proj E r
  set e := V.ideal.comapIso (proj E)
  set x := p.toHom (IsLocalRing.closedPoint ℂ)
  set z := e.hom x
  have hx : e.inv z = x := by
    change (e.hom ≫ e.inv) x = x
    rw [Iso.hom_inv_id]
    rfl
  have hfst : (Limits.pullback.fst (proj E) V.ideal.subschemeι) z =
      (preimageSubvariety E r V).ι x := by
    change (e.hom ≫ Limits.pullback.fst (proj E) V.ideal.subschemeι) x = _
    rw [Scheme.IdealSheafData.comapIso_hom_fst]
    rfl
  have hsnd : (Limits.pullback.snd (proj E) V.ideal.subschemeι) z =
      q.toHom (IsLocalRing.closedPoint ℂ) := by
    apply V.ι.isClosedEmbedding.injective
    change (Limits.pullback.snd (proj E) V.ideal.subschemeι ≫ V.ι) z = _
    rw [← Limits.pullback.condition]
    change proj E ((Limits.pullback.fst (proj E) V.ideal.subschemeι) z) = _
    rw [hfst]
    have := congrArg (fun w : UnderlyingSpace ℂ X ↦ w.toHom (IsLocalRing.closedPoint ℂ)) hpq
    simp only [toHom_mapFun] at this
    exact this
  have hz : z ∈ regularLocus (Limits.pullback (proj E) V.ideal.subschemeι) :=
    mem_regularLocus_of_smooth ℂ (V.toScheme ↘ Spec (.of ℂ)) _ z (hsnd ▸ hq)
  rw [← hx]
  exact (MMP.mem_regularLocus_iff_of_isOpenImmersion e.inv z).mpr hz

end MMP.Modules
