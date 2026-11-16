module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksQuot
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.Quot.StacksRank
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksExists

/-!
# Existence of orientation classes of regular imbeddings, for Stacks vector bundles

Every regular closed imbedding `i : X → Y` of codimension `d` of complex schemes has an
orientation class `u_{X,Y} ∈ H^{2d}(Y, Y - X)` (Fulton, §19.2): `X` is the zero scheme of a
section `σ` of the vector bundle `𝐕(ℰ)` of a quasi-coherent `𝒪_Y`-module `ℰ`, finite locally free
of rank `≥ d` (Fulton, B.8.1, `Y` being closed in a non-singular variety,
`MMP.Modules.exists_section_zeroLocus_eq_ker_of_le`), which gives orientation data
(`MMP.Modules.RegularImbeddingOrientationDatum.nonempty_of_section`), and orientation data give an
orientation class (Thom class and excision,
`MMP.Modules.RegularImbeddingOrientationDatum.exists_isRegularImbeddingOrientationClass`).

## Main results

* `MMP.Modules.RegularImbeddingOrientationDatum.nonempty_of_isRegularClosedImmersionOfCodim`
* `MMP.Modules.exists_isRegularImbeddingOrientationClass`: the existence half of
  `lem_ext_c19_orientation_class_independent`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace MMP.Modules

open UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsRegularClosedImmersionOfCodim)

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  {i : X ⟶ Y} [i.IsOver (Spec (.of ℂ))] {d : ℕ}

/-- **Orientation data exist** for every regular closed imbedding of complex schemes. -/
theorem RegularImbeddingOrientationDatum.nonempty_of_isRegularClosedImmersionOfCodim
    [IsComplexScheme Y] [IsClosedImmersion i] (hi : IsRegularClosedImmersionOfCodim i d) :
    Nonempty (RegularImbeddingOrientationDatum i d) := by
  obtain ⟨V, _, hV, j, -, hj⟩ := IsComplexScheme.exists_isClosedImmersion (X := Y)
  haveI := hj
  obtain ⟨r, hr, E, _, _, σ, hσ, hs⟩ := exists_section_zeroLocus_eq_ker_of_le ℂ j i d
  haveI : σ.IsOver (Spec (.of ℂ)) :=
    ⟨by change σ ≫ proj E ≫ Y ↘ Spec (.of ℂ) = _; rw [← Category.assoc, hσ, Category.id_comp]⟩
  exact nonempty_of_section hi hr E σ hσ hs

/-- **Existence of orientation classes** (Fulton, §19.2): every regular closed imbedding
`i : X → Y` of codimension `d` of complex schemes has an orientation class
`u_{X,Y} ∈ H^{2d}(Y, Y - X)`. -/
theorem exists_isRegularImbeddingOrientationClass (R : Type) [CommRing R] [IsComplexScheme Y]
    [IsClosedImmersion i] (hi : IsRegularClosedImmersionOfCodim i d) :
    ∃ u, IsRegularImbeddingOrientationClass R i d u := by
  obtain ⟨D⟩ := RegularImbeddingOrientationDatum.nonempty_of_isRegularClosedImmersionOfCodim hi
  exact D.exists_isRegularImbeddingOrientationClass R

end MMP.Modules
