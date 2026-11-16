module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program

/-!
# Continuable rays

Let `(X, B)` be a projective lc pair and `D = K_X + B`. A `D`-negative extremal ray `R` of
`NE̅(X)` is *continuable* if it has a contraction `f : X ⟶ Z` onto a normal projective variety
with `f_* 𝒪_X = 𝒪_Z`, `ρ(X/Z) = 1` and `-D` `f`-ample, and, in case `f` is birational, there are
`f⁺ : X⁺ ⟶ Z` and `B⁺` with `X ⟶ Z ⟵ X⁺` a permitted step.

## Main definitions

* `MMP.Fourfold.IsContinuableRay`: continuable extremal rays.

## Implementation notes

* The boundary `B⁺` of a permitted step (`MMP.Fourfold.IsPermittedStep`) is fixed there as the
  strict transform of `f_* B`, so it is not a separate witness.
* The canonical divisor `K` is carried explicitly, as in `MMP.Fourfold.IsPermittedStep`, and
  `D = K + B`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Continuable rays -/

section ContinuableRay

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

/-- A `(K_X + B)`-negative extremal ray `R` of `NE̅(X)`, for a projective lc pair `(X, B)` with
canonical divisor `K`, is *continuable* if it has a contraction `f : X ⟶ Z` onto a normal
projective variety (so `f_* 𝒪_X = 𝒪_Z`) with `ρ(X/Z) = 1` and `-(K_X + B)` `f`-ample, and, in case
`f` is birational, there are `f⁺ : X⁺ ⟶ Z` and `B⁺` with `X ⟶ Z ⟵ X⁺` a permitted step (the
boundary `B⁺` of a permitted step being the strict transform of `f_* B`). -/
@[mmp "def_oai4_continuable_ray"]
structure IsContinuableRay (K : Divisor X) (B : QDivisor X) (R : Set (NumericalCurveClasses sX)) :
    Prop where
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety k sX
  isLogCanonicalPair : MMP.Intersection.IsLogCanonicalPair sX B
  isCanonicalDivisor : ∃ n : ℕ, K.IsCanonicalDivisor sX n
  isNegativeExtremalRayOf : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R
  exists_contraction : ∃ (Z : Scheme.{u}) (sZ : Z ⟶ Spec (.of k)) (f : X ⟶ Z),
    IsContractionOfRay sX sZ R f ∧ MMP.Mori.IsProjectiveVariety k sZ ∧
      relativePicardNumberN1 sX f = 1 ∧
      (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple f ∧
      (IsBirationalMorphism f → ∃ (Xp : Scheme.{u}) (_ : IsIntegral Xp) (_ : CompactSpace Xp)
        (_ : IsLocallyNoetherian Xp) (_ : IsNormal Xp) (sXp : Xp ⟶ Spec (.of k)) (fp : Xp ⟶ Z),
        IsPermittedStep sX sZ sXp K B R f fp)

end ContinuableRay

end MMP.Fourfold
