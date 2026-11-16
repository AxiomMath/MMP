module

public import MMP.Attr
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# The complex realization of a scheme over `ℂ`

For a scheme `X` over `ℂ`, with structure morphism `sX : X ⟶ Spec ℂ`, the *complex realization*
`X^an` is the set `X(ℂ)` of `ℂ`-valued points of `X` over `ℂ`, i.e. of sections
`x : Spec ℂ ⟶ X` of `sX`, with the following topology.

* For an affine open `U ⊆ X`, the `ℂ`-points of `U` (those `x` factoring through `U`) carry the
  coarsest topology for which every evaluation `x ↦ x^*(f) ∈ ℂ`, `f ∈ Γ(X, U)`, is continuous.
* `X(ℂ)` carries the final topology for the inclusions of the `ℂ`-points of its affine opens.

The *realized map* of a morphism `g : X ⟶ Y` over `ℂ` sends a `ℂ`-point `x` to `x ≫ g`.

## Main definitions

* `MMP.Analytic.ComplexPoints`: the set `X(ℂ)` of `ℂ`-points of `X` over `ℂ`.
* `MMP.Analytic.ComplexPoints.chart`: the `ℂ`-points of an affine open `U`.
* `MMP.Analytic.ComplexPoints.eval`: the evaluation `x ↦ x^*(f)` of a section on `U(ℂ)`.
* `MMP.Analytic.ComplexPoints.chartTopology`: the topology of `U(ℂ)`, induced by the evaluations.
* `MMP.Analytic.ComplexPoints.instTopologicalSpace`: the topology of `X^an`, final for the charts.
* `MMP.Analytic.ComplexPoints.realize`: the realized map `X(ℂ) → Y(ℂ)` of a morphism over `ℂ`.

## Main results

* `MMP.Analytic.ComplexPoints.isOpen_iff`: a set is open in `X^an` iff its trace on every chart
  `U(ℂ)` is open.
* `MMP.Analytic.ComplexPoints.continuous_chart_val`: the inclusion of each chart is continuous.
* `MMP.Analytic.ComplexPoints.realize_id`, `MMP.Analytic.ComplexPoints.realize_comp`:
  realization is functorial.

## Implementation notes

* The source describes the topology on the chart `Spec (ℂ[z_1, …, z_N]/I)` as the subspace
  topology on the common zero set of `I` in `ℂ^N`. Here it is the initial topology for the
  evaluations at all sections of `U`; for any finite generating family `z_1, …, z_N` of `Γ(X, U)`
  the two agree, because every section is a polynomial in the `z_i` and polynomials are
  continuous. This form does not depend on a choice of generators.
* No finiteness hypothesis is imposed on `X`: the definitions make sense for every scheme over
  `ℂ`, and the finite type hypothesis of the source enters only the later properties of `X^an`.

## References

* [Kollár–Mori, *Birational geometry of algebraic varieties*]
* [Serre, *Géométrie algébrique et géométrie analytique*]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology

namespace MMP.Analytic

/-- The `ℂ`-points of a scheme `X` over `ℂ`: the sections `x : Spec ℂ ⟶ X` of the structure
morphism `sX`. This is the underlying set of the complex realization `X^an`. -/
@[mmp "def_mmp_complex_realization"]
def ComplexPoints {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) : Type :=
  {x : Spec (.of ℂ) ⟶ X // x ≫ sX = 𝟙 _}

namespace ComplexPoints

variable {X Y Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
  {sZ : Z ⟶ Spec (.of ℂ)}

/-- The underlying morphism `Spec ℂ ⟶ X` of a `ℂ`-point. -/
abbrev hom (x : ComplexPoints sX) : Spec (.of ℂ) ⟶ X := x.1

/-- A `ℂ`-point is a section of the structure morphism: `x ≫ sX = 𝟙`. -/
@[simp]
lemma hom_comp_structure (x : ComplexPoints sX) : x.hom ≫ sX = 𝟙 _ := x.2

/-- Two `ℂ`-points with the same underlying morphism `Spec ℂ ⟶ X` are equal. -/
@[ext]
lemma ext {x y : ComplexPoints sX} (h : x.hom = y.hom) : x = y := Subtype.ext h

/-- The `ℂ`-points of `X` lying in the open `U`, i.e. factoring through `U`. -/
def chart (U : X.Opens) : Set (ComplexPoints sX) :=
  {x | x.hom ⁻¹ᵁ U = ⊤}

/-- The value `x^*(f) ∈ ℂ` of a section `f ∈ Γ(X, U)` at a `ℂ`-point `x` of `U`. -/
def eval (U : X.Opens) (f : Γ(X, U)) (x : chart (sX := sX) U) : ℂ :=
  (Scheme.ΓSpecIso (.of ℂ)).hom (x.1.hom.appLE U ⊤ x.2.ge f)

/-- The topology on the `ℂ`-points of an open `U`: the coarsest one for which every evaluation
`x ↦ x^*(f)`, `f ∈ Γ(X, U)`, is continuous. It is used for affine `U`, where it is the subspace
topology of the zero set of the ideal of relations among any finite set of generators. -/
@[mmp "def_mmp_complex_realization", instance_reducible]
def chartTopology (U : X.Opens) : TopologicalSpace (chart (sX := sX) U) :=
  ⨅ f : Γ(X, U), TopologicalSpace.induced (eval U f) inferInstance

/-- The topology of the complex realization `X^an`: the final topology for the inclusions of the
`ℂ`-points of the affine opens of `X`. -/
@[mmp "def_mmp_complex_realization"]
instance instTopologicalSpace : TopologicalSpace (ComplexPoints sX) :=
  ⨆ U : X.affineOpens,
    TopologicalSpace.coinduced (Subtype.val : chart (sX := sX) (U : X.Opens) → _)
      (chartTopology (U : X.Opens))

/-- A set of `ℂ`-points is open in `X^an` iff its preimage in the `ℂ`-points of every affine open
`U` is open for `chartTopology U`. -/
lemma isOpen_iff (s : Set (ComplexPoints sX)) :
    IsOpen s ↔ ∀ U : X.affineOpens,
      IsOpen[chartTopology (U : X.Opens)]
        ((Subtype.val : chart (sX := sX) (U : X.Opens) → _) ⁻¹' s) := by
  change IsOpen[⨆ U : X.affineOpens, _] s ↔ _
  simp only [isOpen_iSup_iff, isOpen_coinduced]

/-- For an affine open `U`, the inclusion of the `ℂ`-points of `U` into `X^an` is continuous. -/
lemma continuous_chart_val (U : X.affineOpens) :
    Continuous[chartTopology (U : X.Opens), instTopologicalSpace]
      (Subtype.val : chart (sX := sX) (U : X.Opens) → ComplexPoints sX) := by
  rw [continuous_iff_coinduced_le]
  exact le_iSup (fun U : X.affineOpens => TopologicalSpace.coinduced
    (Subtype.val : chart (sX := sX) (U : X.Opens) → _) (chartTopology (U : X.Opens))) U

/-- Each evaluation `x ↦ x^*(f)` is continuous on the `ℂ`-points of `U` for `chartTopology U`. -/
lemma continuous_eval (U : X.Opens) (f : Γ(X, U)) :
    Continuous[chartTopology U, _] (eval (sX := sX) U f) := by
  rw [continuous_iff_le_induced]
  exact iInf_le (fun f : Γ(X, U) => TopologicalSpace.induced (eval (sX := sX) U f)
    inferInstance) f

/-- The realized map `X(ℂ) → Y(ℂ)` of a morphism `g : X ⟶ Y` over `ℂ`: composition of
`ℂ`-points with `g`. -/
@[mmp "def_mmp_complex_realization"]
def realize (g : X ⟶ Y) (hg : g ≫ sY = sX) (x : ComplexPoints sX) : ComplexPoints sY :=
  ⟨x.hom ≫ g, by rw [Category.assoc, hg, x.hom_comp_structure]⟩

/-- The underlying morphism of the realized point `realize g hg x` is `x ≫ g`. -/
@[simp]
lemma realize_hom (g : X ⟶ Y) (hg : g ≫ sY = sX) (x : ComplexPoints sX) :
    (realize g hg x).hom = x.hom ≫ g := rfl

/-- The realized map of the identity is the identity. -/
@[simp]
lemma realize_id : realize (𝟙 X) (Category.id_comp sX) = id := by
  funext x; ext1; simp

/-- The realized map of a composite `g ≫ h` is the composite of the realized maps. -/
lemma realize_comp (g : X ⟶ Y) (hg : g ≫ sY = sX) (h : Y ⟶ Z) (hh : h ≫ sZ = sY) :
    realize (g ≫ h) (by rw [Category.assoc, hh, hg]) = realize h hh ∘ realize g hg := by
  funext x; ext1; simp

end ComplexPoints

end MMP.Analytic
