/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import all Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# The rank of a morphism at a point, computed on an affine chart

`AlgebraicGeometry.Scheme.Hom.finrank f s` is defined through the pullback of `f` to the chart
`S.affineOpenCover.f (S.affineOpenCover.idx s)` of the target containing `s`, but its
definition is not exposed outside Mathlib. This file records the defining formula, with no
flatness hypothesis: the rank at `s` is the rank of `Γ(T, ⊤) → Γ(X ×_S T, ⊤)` at a point `t` of
the chart `T` lying over `s`.

## Main results

* `MMP.Mori.finrank_eq_appTop_finrank_chart`
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace MMP.Mori

/-- The rank of `f : X ⟶ S` at `s` is the rank of the ring map on global sections of the pullback
to the affine chart of `S` containing `s`, at the point of the chart chosen over `s`. -/
theorem finrank_eq_appTop_finrank_chart {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    f.finrank s =
      (pullback.snd f (S.affineOpenCover.f (S.affineOpenCover.idx s))).appTop.hom.finrank
        ((Spec (S.affineOpenCover.X (S.affineOpenCover.idx s))).isoSpec.hom
          (S.affineOpenCover.covers s).choose) := by
  unfold Scheme.Hom.finrank
  rfl

end MMP.Mori
