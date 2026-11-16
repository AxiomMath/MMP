module

public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Divisor.LinearSeries
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import MMP.AlgebraicGeometry.Singularities.Slc.NodeResidueForm
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
public import MMP.AlgebraicGeometry.Positivity.VeryAmpleMultiple
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.AmpleRelativeFiniteType.VeryAmple
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.HypersurfaceCohomology
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# A prime divisor cut out by a section of a very ample line bundle is ample

Let `X` be a smooth projective surface over `ℂ`, `A` a very ample Cartier divisor on `X` and
`s` a global section of `𝒪_X(A)`. If the zero scheme `Z(s)` is (the ideal sheaf of) a prime
divisor `P`, then `P` is an ample Cartier divisor.

The proof compares invertible sheaves. Since `P` is a proper closed subset, `s ≠ 0`, so `s` is a
nonzerodivisor section of the invertible sheaf `𝒪_X(A)` on the integral scheme `X`, and
`𝒪_X(A) ≅ ℋom(ℐ_{Z(s)}, 𝒪_X) = ℋom(ℐ_P, 𝒪_X)`. On the other hand, `X` is smooth, so `P` is
Cartier and its divisorial sheaf `𝒪_X(P)` is also `ℋom(ℐ_P, 𝒪_X)`. Hence `𝒪_X(P) ≅ 𝒪_X(A)`,
which is ample because `A` is very ample.

## Main definitions

* `MMP.Analytic.SurfaceHodge.ZeroSchemePrimeDivisorAmple`: the statement that, on a smooth
  projective surface over `ℂ`, a prime divisor which is the zero scheme of a section of a very
  ample line bundle is an ample Cartier divisor.

## Main results

* `MMP.Analytic.SurfaceHodge.zeroSchemePrimeDivisorAmple`: that statement holds.

## References

* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace MMP.Intersection

namespace MMP.Analytic.SurfaceHodge

/-- **(B) The curve is an ample divisor.** If the prime divisor `P` is the zero scheme of a
section of `𝒪_X(A)`, `A` very ample, on a smooth projective surface, then `P` is an ample Cartier
divisor. -/
def ZeroSchemePrimeDivisorAmple : Prop :=
  ∀
    {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (A : X.CartierDivisor),
    IsVeryAmpleDivisor ℂ A → ∀ (s : Γ(MMP.CartierDivisor.sheaf A, ⊤)) (P : Mori.PrimeDivisor X),
    P.idealSheaf = @zeroScheme X (MMP.CartierDivisor.sheaf A)
        (MMP.CartierDivisor.isInvertibleModule_sheaf A) s →
    ∃ h : Mori.Divisor.IsCartier (Finsupp.single P 1 : Mori.Divisor X),
      Mori.Divisor.IsAmple (Finsupp.single P 1 : Mori.Divisor X) h

/-- The ideal sheaf of a prime divisor of an integral scheme is not the zero ideal: its generic
point has coheight one, while the generic point of `X` has coheight zero. -/
private theorem primeDivisor_idealSheaf_ne_bot {Y : Scheme} [IsIntegral Y]
    (D : MMP.Mori.PrimeDivisor Y) : D.idealSheaf ≠ ⊥ := by
  intro h0
  have hsupp : D.support = Set.univ := by
    change ((D.idealSheaf.support : Set Y)) = _
    rw [h0, Scheme.IdealSheafData.support_bot]; rfl
  have hgen : IsGenericPoint D.genericPoint (Set.univ : Set Y) := by
    rw [← hsupp, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isGenericPoint_closure
  have h1 := D.coheight_genericPoint
  have h2 : Order.coheight D.genericPoint = 0 := by
    rw [Order.coheight_eq_zero]
    intro b hb
    have hb' : b ⤳ D.genericPoint := hb
    have hbgen : IsGenericPoint b (Set.univ : Set Y) := by
      refine (isGenericPoint_iff_specializes).mpr fun w => ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
      exact hb'.trans (hgen.specializes (Set.mem_univ w))
    exact (hbgen.eq hgen).symm ▸ le_rfl
  rw [h2] at h1
  exact absurd h1 (by decide)

/-- **The zero scheme of a section of a very ample line bundle, when a prime divisor, is
ample.** -/
theorem zeroSchemePrimeDivisorAmple : ZeroSchemePrimeDivisorAmple := by
  intro X _ _ _ _ _ _ A hA s P hP
  set f := X ↘ Spec (.of ℂ) with hf
  haveI : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have hV : IsVariety ℂ f := inferInstance
  haveI : IsIntegral X := hV.toIsIntegral
  have hsm : MMP.Mori.IsSmoothScheme f := MMP.Flips.isSmoothScheme_of_smooth f
  have hD : Mori.Divisor.IsCartier (Finsupp.single P 1 : Mori.Divisor X) :=
    MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm P
  refine ⟨hD, ?_⟩
  letI hLi : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (MMP.CartierDivisor.sheaf A) :=
    MMP.CartierDivisor.isInvertibleModule_sheaf A
  haveI : Stacks.Ample.IsInvertibleModule X (MMP.CartierDivisor.sheaf A) :=
      MMP.CartierDivisor.isInvertibleModule_sheaf A
  -- the section is nonzero
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact primeDivisor_idealSheaf_ne_bot P (hP.trans (zeroScheme_zero X (MMP.CartierDivisor.sheaf
        A)))
  -- `𝒪_X(A)` is ample
  have hamp : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf A) := by
    have htfae := Stacks.AmpleRelativeFiniteType.tfae_six f (MMP.CartierDivisor.sheaf A)
    have h5 : ∃ d : ℕ, 1 ≤ d ∧ Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver f
        (Stacks.Ample.tensorPowModule X (MMP.CartierDivisor.sheaf A) (d : ℤ)) :=
      ⟨1, le_rfl, MMP.Resolution.Bridges.hasImmersionTwistOver_of_isVeryAmple ℂ
          (MMP.CartierDivisor.sheaf A) _
        hA (Stacks.Ample.tensorPowModuleOneIso _ _)⟩
    exact (htfae.out 5 1).1 h5
  -- `𝒪_X(A) ≅ ℋom(ℐ_P, 𝒪_X)`
  have hreg : ∀ U : X.Opens, Function.Injective fun r : Γ(X, U) =>
      r • (MMP.CartierDivisor.sheaf A).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s :=
    fun U _ _ h => eq_of_smul_map_le_top_eq_of_isIntegral (MMP.CartierDivisor.sheaf A) s hs0 U h
  have eA : (MMP.CartierDivisor.sheaf A) ≅ (Stacks.Divisors.invertibleSheaf' P.idealSheaf :
      X.Modules) :=
    invertibleSheafIsoZeroScheme (MMP.CartierDivisor.sheaf A) s hreg ≪≫ eqToIso (by rw [hP])
  -- `𝒪_X(P) ≅ ℋom(ℐ_P, 𝒪_X)`
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf :=
    hP ▸ isEffectiveCartierDivisor_zeroScheme_of_ne_zero (MMP.CartierDivisor.sheaf A) s hs0
  obtain ⟨eP⟩ :=
    MMP.Threefold.Resolution.nonempty_divisorialSheaf_single_iso_invertibleSheaf' P hcart hD
  haveI := hD.isInvertibleModule_divisorialSheaf
  exact (Stacks.RelativeVeryAmple.isAmple_congr (MMP.CartierDivisor.sheaf A) _ (eA ≪≫ eP.symm)).1
      hamp

end MMP.Analytic.SurfaceHodge
