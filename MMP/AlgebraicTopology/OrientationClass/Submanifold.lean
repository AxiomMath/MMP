module

public import MMP.AlgebraicTopology.ThomClass.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.TangentCone.Basic

/-!
# The orientation class of a closed submanifold (Fulton, §19.1)

Let `M ⊆ P` be a closed complex submanifold of complex codimension `d` of a complex manifold `P`,
with normal bundle `N`, and let `φ : N → P` be a tubular neighbourhood: an open imbedding which
restricts to the inclusion `M ⊆ P` on the zero section `0_N ≅ M`. Then `φ⁻¹(M) = 0_N`, so `φ`
is a map of pairs `(N, N - 0_N) → (P, P - M)`, and the composite
`H^{2d}(P, P - M) ≅ H^{2d}(φ(N), φ(N) - M) ≅ H^{2d}(N, N - 0_N)` of excision and `φ^*` is the
pull-back `φ^*` of relative cohomology. The *orientation class* `u_{M,P} ∈ H^{2d}(P, P - M)` is
the class which this map sends to the Thom class `u_N`.

## Main definitions

* `MMP.TubularNeighbourhood`: an open imbedding of the total space of a vector
  bundle on `M ⊆ P` into `P` restricting to the inclusion on the zero section.
* `MMP.TubularNeighbourhood.thomPullback`: the map
  `H^j(P, P - M) → H^j(N, N - 0_N)` it induces.
* `MMP.TubularNeighbourhood.IsOrientationCompatible`: `φ` is compatible with the
  complex orientations: in a chart of the complex manifold `P` at `x ∈ M`, its derivative along the
  fibre `N_x` is injective and complex linear modulo a complex complement of its image.
* `MMP.IsOrientationClass`: `u ∈ H^{2d}(P, P - M)` is the orientation class
  relative to an orientation-compatible `φ`, that is, `φ^* u` is a Thom class of `N`.

## Main results

* `MMP.TubularNeighbourhood.preimage_eq_range_zeroSection`: `φ⁻¹(M) = 0_N`.
* `MMP.isOrientationClass_iff`: `u` is the orientation class exactly when `φ` is
  orientation compatible and the pull-back of `u` to `(N, N - 0_N)` is a Thom class.

## Implementation notes

The definition is stated for an arbitrary subset `M` of a charted space `P` modelled on a
complex normed space `E` and an arbitrary complex topological vector bundle `N` on `M`
(Mathlib's `Bundle.VectorBundle ℂ F N`), with a topological tubular neighbourhood `φ` which is
compatible with the complex orientations (`TubularNeighbourhood.IsOrientationCompatible`); it is
Fulton's when `P` is a complex manifold, `M` a closed complex submanifold, `N` its normal bundle
and `φ` a smooth tubular neighbourhood whose differential along `0_N` induces the identity of `N`
(then the tangent cone `W` of `M` at `x` in a holomorphic chart is the image of `T_x M`). Thom
classes are given by the predicate `MMP.IsThomClass`, so the orientation class is the predicate
`MMP.IsOrientationClass`.

The compatibility condition is needed: for a merely topological `φ`, composing `φ` with complex
conjugation in the fibres multiplies the pull-back of `u` by `(-1)^d`, so for `P = ℙ¹(ℂ)` and a
point `M` the "orientation class" would only be defined up to sign. For a point `M = {t}` and a
model `F = E` the condition says that the derivative of `φ` at `0` is a complex linear
isomorphism in the chart at `t`.

The relative cohomology `H^j(P, P - M)` is `cohomologyWithSupports`, and the composite of
excision and `φ^*` is the pull-back along `φ` followed by the identification
`φ⁻¹(M) = 0_N`; neither excision nor the fact that this map is an isomorphism enters the
definition.

Fulton's remark that `u_{M,P}` does not depend on `φ` (Bott–Tu, §6) is not part of the
definition; it is `MMP.isOrientationClass_iff_of_isOrientationCompatible`
(for a finite-dimensional model `E`).

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [R. Bott, L. Tu, *Differential forms in algebraic topology*][botttu1982], §6.
-/

@[expose] public noncomputable section

open Set Bundle CategoryTheory

universe u

namespace MMP

variable {P : TopCat.{u}} {M : Set P}
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  (N : M → Type u) [∀ x, AddCommGroup (N x)] [∀ x, Module ℂ (N x)] [∀ x, TopologicalSpace (N x)]
  [TopologicalSpace (TotalSpace F N)] [FiberBundle F N] [_root_.VectorBundle ℂ F N]

/-- A *tubular neighbourhood* of `M ⊆ P` modelled on a vector bundle `N` on `M` (Fulton, §19.1):
an open imbedding `φ : N → P` of the total space restricting to the inclusion `M ⊆ P` on the zero
section. -/
structure TubularNeighbourhood where
  /-- The imbedding of the total space into `P`. -/
  toFun : TotalSpace F N → P
  /-- The underlying map is an open embedding. -/
  isOpenEmbedding : Topology.IsOpenEmbedding toFun
  /-- The underlying map restricts to the inclusion `M ⊆ P` on the zero section. -/
  map_zeroSection (x : M) : toFun (zeroSection F N x) = x

namespace TubularNeighbourhood

variable {F N}

/-- A tubular neighbourhood `φ` is applied as its underlying map `N → P`. -/
instance : CoeFun (TubularNeighbourhood F N) fun _ ↦ TotalSpace F N → P :=
  ⟨TubularNeighbourhood.toFun⟩

omit [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F] [∀ x, Module ℂ (N x)]
  [∀ x, TopologicalSpace (N x)] [FiberBundle F N] [_root_.VectorBundle ℂ F N] in
/-- A tubular neighbourhood `φ : N → P` is continuous. -/
theorem continuous (φ : TubularNeighbourhood F N) : Continuous φ :=
  φ.isOpenEmbedding.continuous

/-- `φ` as a continuous map `N → P`. -/
def toHom (φ : TubularNeighbourhood F N) : TopCat.of (TotalSpace F N) ⟶ P :=
  TopCat.ofHom ⟨φ, φ.continuous⟩

omit [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F] [∀ x, Module ℂ (N x)]
  [∀ x, TopologicalSpace (N x)] [FiberBundle F N] [_root_.VectorBundle ℂ F N] in
/-- The continuous map `φ.toHom` agrees with `φ` at every point of `N`. -/
@[simp]
theorem toHom_apply (φ : TubularNeighbourhood F N) (v : TotalSpace F N) : φ.toHom v = φ v :=
  rfl

omit [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F] [∀ x, Module ℂ (N x)]
  [∀ x, TopologicalSpace (N x)] [FiberBundle F N] [_root_.VectorBundle ℂ F N] in
/-- **`φ⁻¹(M) = 0_N`**: the preimage of `M` under a tubular neighbourhood `φ` is the zero
section. -/
theorem preimage_eq_range_zeroSection (φ : TubularNeighbourhood F N) :
    φ ⁻¹' M = range (zeroSection F N) := by
  refine subset_antisymm (fun v hv ↦ ⟨⟨φ v, hv⟩,
    φ.isOpenEmbedding.injective (φ.map_zeroSection ⟨φ v, hv⟩)⟩) ?_
  rintro _ ⟨x, rfl⟩
  change φ.toFun (zeroSection F N x) ∈ M
  rw [φ.map_zeroSection]
  exact x.2

variable (R : Type u) [CommRing R]

/-- The map `H^j(P, P - M) → H^j(N, N - 0_N)` induced by a tubular neighbourhood `φ`: the
composite of excision `H^j(P, P - M) ≅ H^j(φ(N), φ(N) - M)` and `φ^*`, that is, the pull-back
along `φ` followed by the identification `φ⁻¹(M) = 0_N`. -/
def thomPullback (φ : TubularNeighbourhood F N) (j : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) P M j ⟶
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F N))
        (range (zeroSection F N)) j :=
  cohomologyWithSupports.pullback R (ModuleCat.of R R) φ.toHom M j ≫
    cohomologyWithSupports.forget R (ModuleCat.of R R) (TopCat.of (TotalSpace F N))
      (φ.preimage_eq_range_zeroSection.subset) j

end TubularNeighbourhood

section Orientation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E P]

namespace TubularNeighbourhood

variable {F N}

/-- A tubular neighbourhood `φ : N → P` of `M` in a complex manifold `P` modelled on `E` is
*compatible with the complex orientations* (Fulton, §19.1: its differential along the zero section
induces the identity of the normal bundle): at every `x ∈ M`, the tangent cone of `M` at `x` in
the chart `e` at `x` (Mathlib's `tangentConeAt`; for a submanifold, the tangent space `T_x M` in
the chart) is a complex subspace `W` of `E`, and for some complex frame `ψ : ℂ^d ≅ N_x`, the map
`v ↦ e (φ (ψ v))` is differentiable at `0` with an injective derivative `L` whose image is
complementary to `W` and which is complex linear modulo `W`. Thus `L` induces a complex linear
isomorphism `ℂ^d ≅ E / T_x M`, the identification of the fibre `N_x` with the normal space.

Tying `W` to `M` is what fixes the orientation: with `W` merely some complement of the image of
`L`, the homeomorphism `φ(x, v) = (x + v, conj(v)|v|²)` of `ℂ²` (a tubular neighbourhood of
`ℂ × 0` with `W = 0 × ℂ`) would be admitted, and it pulls the class back with the sign
`-1`. -/
def IsOrientationCompatible (φ : TubularNeighbourhood F N) : Prop :=
  ∀ x : M, ∃ ψ : (Fin (Module.finrank ℂ F) → ℂ) ≃L[ℂ] N x,
    ∃ L : (Fin (Module.finrank ℂ F) → ℂ) →L[ℝ] E,
      HasFDerivAt (fun v ↦ chartAt E (x : P) (φ (TotalSpace.mk x (ψ v)))) L 0 ∧
        Function.Injective L ∧
        ∃ W : Submodule ℂ E,
          tangentConeAt ℝ (chartAt E (x : P) '' (M ∩ (chartAt E (x : P)).source))
              (chartAt E (x : P) x) = W ∧
          IsCompl (LinearMap.range (L : (Fin (Module.finrank ℂ F) → ℂ) →ₗ[ℝ] E))
            (W.restrictScalars ℝ) ∧
          ∀ (c : ℂ) (v : Fin (Module.finrank ℂ F) → ℂ), L (c • v) - c • L v ∈ W

end TubularNeighbourhood

variable {F N} (E) (R : Type u) [CommRing R]

/-- The *orientation class* `u_{M,P} ∈ H^{2d}(P, P - M)` of `M ⊆ P` (Fulton, §19.1), for a
tubular neighbourhood `φ : N → P` modelled on a complex vector bundle `N` of rank
`d = dim F` (the normal bundle, for a closed complex submanifold `M` of codimension `d`) and
compatible with the complex orientations (`TubularNeighbourhood.IsOrientationCompatible`): the
class whose image under `H^{2d}(P, P - M) ≅ H^{2d}(φ(N), φ(N) - M) ≅ H^{2d}(N, N - 0_N)`
(excision, then `φ^*`) is the Thom class `u_N`. -/
def IsOrientationClass (φ : TubularNeighbourhood F N)
    (u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)) : Prop :=
  φ.IsOrientationCompatible (E := E) ∧
    IsThomClass (R := R) F N ((φ.thomPullback R (2 * Module.finrank ℂ F : ℕ)).hom u)

omit [FiniteDimensional ℂ F] [_root_.VectorBundle ℂ F N] in
/-- `u` is the orientation class relative to `φ` exactly when `φ` is compatible with the complex
orientations and the pull-back `φ^* u ∈ H^{2d}(N, N - 0_N)` is a Thom class of `N`. -/
theorem isOrientationClass_iff (φ : TubularNeighbourhood F N)
    (u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)) :
    IsOrientationClass E R φ u ↔ φ.IsOrientationCompatible (E := E) ∧
      IsThomClass (R := R) F N ((φ.thomPullback R (2 * Module.finrank ℂ F : ℕ)).hom u) :=
  Iff.rfl

end Orientation

end MMP
