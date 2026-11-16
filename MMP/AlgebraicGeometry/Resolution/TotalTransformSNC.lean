/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
public import MMP.AlgebraicGeometry.Resolution.OneBlowupTotalTransform

/-!
# The total transform of an snc divisor under a blow-up sequence

Let `X` be a smooth scheme of finite type over a field `k` of characteristic `0`, `E ⊆ X` a
divisor with simple normal crossings and `Π : X_r → ⋯ → X_0 = X` a smooth blow-up sequence whose
centres have simple normal crossings with `E`. Then the total transform `Π⁻¹_tot(E) ⊆ X_r` is a
divisor with simple normal crossings.

The proof is an induction on the length of the sequence. For `r = 0` the total transform is `E`.
Otherwise the first centre `Z_0` has simple normal crossings with the sum of the components of
`E`, so the total transform `π_0⁻¹(E ∖ Z_0)‾ ∪ π_0⁻¹(Z_0)` of `E` on `X_1 = B_{Z_0}X` is a divisor
with simple normal crossings; `X_1` is of finite type over `k` (the blow-up of a locally
Noetherian scheme is proper over it) and, when the sequence continues, smooth over `k`, and the
remaining blow-ups form a smooth blow-up sequence of `X_1` whose centres have simple normal
crossings with that total transform.

## Main results

* `MMP.Resolution.ClosedBlowupSequence.isSNCClosedSubset_totalTransform`: the total transform of
  an snc divisor under a smooth blow-up sequence whose centres have snc with it is a divisor with
  simple normal crossings.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Def. 3.25]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori

universe u

namespace MMP.Resolution

namespace ClosedBlowupSequence

variable {k : Type u} [Field k]

/-- **The total transform of an snc divisor under a blow-up sequence is an snc divisor** (Kollár,
Def. 3.25). Let `X` be a smooth scheme of finite type over a field `k` of characteristic `0`,
`E ⊆ X` a divisor with simple normal crossings and `Π : X_r → ⋯ → X_0 = X` a smooth blow-up
sequence whose centres have simple normal crossings with `E`. Then the total transform
`Π⁻¹_tot(E) ⊆ X_r` is a divisor with simple normal crossings. -/
@[mmp "lem_kr3b_total_transform_snc"]
theorem isSNCClosedSubset_totalTransform [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [QuasiCompact sX] (hX : IsSmoothScheme sX) {E : Set X}
    (hE : IsSNCClosedSubset sX E) (B : ClosedBlowupSequence X) (hB : B.IsSmooth sX)
    (hBE : B.CentersHaveSNCWith sX E) :
    IsSNCClosedSubset (B.toBase ≫ sX) (B.totalTransform E) := by
  induction B with
  | nil X =>
    change IsSNCClosedSubset (𝟙 X ≫ sX) E
    rwa [Category.id_comp]
  | @cons X Z B ih =>
    obtain ⟨-, hZ, hBE⟩ := hBE
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    have h₁ := isSNCClosedSubset_totalTransformStep sX hX hE hZ
    cases B with
    | nil _ =>
      change IsSNCClosedSubset (𝟙 _ ≫ blowUpToBase Z ≫ sX) (totalTransformStep Z E)
      rwa [Category.id_comp]
    | cons Z' B' =>
      change IsSNCClosedSubset (((cons Z' B').toBase ≫ blowUpToBase Z) ≫ sX)
        ((cons Z' B').totalTransform (totalTransformStep Z E))
      rw [Category.assoc]
      exact ih (blowUpToBase Z ≫ sX) hB.2.2.1 h₁ hB.2.2 hBE

end ClosedBlowupSequence

end MMP.Resolution
