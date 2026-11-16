module

public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.Basic
public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.LocalExact

/-!
# The trivial twist and composites of relatively locally exact inclusions

The inclusion `C'^• ⟶ C^•` of a twist of the fractional logarithmic complex is read on forms
(`MMP.LcBpf.IsTwistInclusion`), and inclusions compose (`MMP.LcBpf.IsTwistInclusion.comp`). The
identity is the inclusion of the trivial twist, restriction of forms along the identity of an open
being the identity, and it is relatively locally exact.

## Main results

* `MMP.LcBpf.isTwistInclusion_id`: the identity is the inclusion of the trivial twist.
* `MMP.LcBpf.relLocallyExact_id`: the identity is relatively locally exact.
* `MMP.LcBpf.relLocallyExact_comp_of_mono`: relative local exactness composes along a composite
  whose second map is a monomorphism in every degree.

## References

* [H. Esnault, E. Viehweg, *Lectures on vanishing theorems*][EsnaultViehweg1992]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.LcBpf

open MMP.FourfoldProofs.FractionalLogComplexProof

section Mono

variable {X : TopCat.{0}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}

/-- **The identity is relatively locally exact.** -/
theorem relLocallyExact_id (K : CochainComplex (SheafOfModules.{0} R) ℕ) :
    RelLocallyExact (𝟙 K) := by
  intro p W x _ pt hpt
  refine ⟨W, le_rfl, hpt, 0, (K.X p).val.map (homOfLE le_rfl).op x, ?_⟩
  rw [map_zero, zero_add]
  rfl

/-- **Relative local exactness composes** along a composite `K'' ⟶ K' ⟶ K` whose second map is a
monomorphism in every degree. -/
theorem relLocallyExact_comp_of_mono {K'' K' K : CochainComplex (SheafOfModules.{0} R) ℕ}
    (φ' : K'' ⟶ K') (φ : K' ⟶ K) [∀ p, Mono (φ.f p)] (h' : RelLocallyExact φ')
    (h : RelLocallyExact φ) : RelLocallyExact (φ' ≫ φ) :=
  relLocallyExact_comp φ' φ
    (fun p W => PresheafOfModules.injective_of_mono ((SheafOfModules.forget R).map (φ.f p)) (op W))
    h' h

end Mono

section Twist

variable {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))

/-- **The identity is the inclusion of a twist**, for `M' = M`. -/
theorem isTwistInclusion_id (D M : MMP.Mori.Divisor V)
    {K : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
    {F : ℕ → V.Modules}
    (e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p))
    (ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D M W))) :
    IsTwistInclusion π D M M rfl e e ι ι (𝟙 K) := by
  intro p W x
  change ι p W ((e p).hom.val.app (op W) x) = _
  exact (piece_map_id
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val _ _).symm

end Twist

end MMP.LcBpf
