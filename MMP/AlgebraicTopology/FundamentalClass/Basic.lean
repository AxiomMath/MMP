module

public import MMP.AlgebraicTopology.BorelMoore.Restriction
public import MMP.AlgebraicTopology.ThomClass.Basic
public import Mathlib.Geometry.Manifold.IsManifold.Basic
/-!
# The fundamental class of an oriented manifold (Fulton, §19.1)

Let `M` be a real `n`-manifold (without boundary), with an orientation. The *fundamental class*
`μ_M ∈ H_n M` of the orientation is the Borel–Moore class whose restriction to every coordinate
ball `B` is the orientation generator of `H_n B` (Iversen, IX.4).

The orientation generator of `H_n B` is detected locally. A locally finite `n`-cycle `z` of `B`
meets only finitely many simplices through a point `x`, so it pairs with every relative
`n`-cocycle `φ` of `(B, B - x)`: `⟨φ, z⟩ = ∑_σ z_σ φ(σ)`. In a coordinate chart `B ≅ e(B) ⊆ ℝⁿ`
the local orientation at `x` is represented by `e⁻¹ ∘ Δ` for any affine `n`-simplex `Δ` of `e(B)`
around `e(x)` positively oriented for the orientation of `ℝⁿ`; this is a relative cycle of
`(B, B - x)` whose class generates `H_n(B, B - x) ≅ R`. A class of `H_n B` is the orientation
generator exactly when, for every point `x` of `B`, a cycle `z` representing it and every such
`Δ`, the pairings `⟨φ, z⟩` and `⟨φ, e⁻¹ ∘ Δ⟩` agree for all relative cocycles `φ` of
`(B, B - x)`, i.e. `z` and `e⁻¹ ∘ Δ` have the same image in `H_n(B, B - x)` (which `H^n(B, B - x)`
detects, `H_{n-1}(B, B - x)` being free).

A complex manifold of complex dimension `m` is oriented by its complex structure: in a
holomorphic chart with values in `ℂ^m` the oriented real basis is `e₁, i e₁, …, e_m, i e_m`,
and it has a fundamental class `μ_M ∈ H_{2m} M`. A point `P` (the case `n = 0`) has
`μ_P ∈ H_0 P`, the class of the point.

## Main definitions

* `MMP.FundamentalClass.localPairing`: the pairing `⟨φ, z⟩` of a locally finite
  chain with a cochain supported near a point.
* `MMP.FundamentalClass.IsLocallyClassOf`: a class `ν ∈ H_n X` has the same image
  as the simplex `Δ` in `H_n(X, X - x)`.
* `MMP.FundamentalClass.chartOpens`, `MMP.FundamentalClass.chartSimplex`:
  the coordinate ball of a chart, and the simplex `e⁻¹ ∘ Δ` in it.
* `MMP.FundamentalClass.IsChartOrientationClass`: the orientation generator of the
  Borel–Moore homology of a coordinate ball.
* `MMP.IsFundamentalClass`: the fundamental class `μ_M ∈ H_n M` of an oriented
  real `n`-manifold.
* `MMP.IsComplexFundamentalClass`: the fundamental class `μ_M ∈ H_{2m} M` of a
  complex manifold of complex dimension `m`, oriented by its complex structure.

## Implementation notes

The manifold is a charted space `M` over a real vector space `H` of dimension `n`, Hausdorff (so
that restriction of Borel–Moore homology to open subsets is defined); the coordinate balls are
the chart domains, and the orientation is given by a basis `b` of `H` together with the atlas,
the orientation of `M` in a chart being that of `b`. The condition is stated for an arbitrary
atlas; for an oriented atlas (transition maps preserving the orientation of `b`) it is Fulton's
condition on `μ_M`. The coefficients are an arbitrary commutative ring `R`.

Fulton's "the class `μ_M`" is the unique class with this property (Iversen, IX.4.7); following
the convention for "the unique `x` with `P`", the definition is the property `P`.

The orientation generator is described through relative cocycles of `(B, B - x)`, i.e. through
the image of `H_n B` in the local homology `H_n(B, B - x)`, as in Iversen's description of the
orientation sheaf. A complex manifold is modelled on `ℂ^m = Fin m → ℂ`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [B. Iversen, *Cohomology of Sheaves*][iversen1986], IX.4.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology Opposite Simplicial Manifold
open MMP.SingularChain MMP.SingularCochain
  MMP.ThomClass

universe u

namespace MMP

namespace FundamentalClass

section Local

variable {R : Type u} [CommRing R] {X : TopCat.{u}}

/-- The pairing `⟨φ, c⟩ = ∑_σ c_σ φ(σ)` of a (locally finite) `n`-chain `c` of `X` with an
`n`-cochain `φ`. For `c` locally finite and `φ` vanishing on the simplices avoiding a point, the
sum is finite. -/
def localPairing {n : ℕ} (c : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) (φ : Simplex X n → R) :
    R :=
  ∑ᶠ σ, c σ * φ (SingularCochain.simplexEquiv X n σ)

variable (R) in
/-- A Borel–Moore class `ν ∈ H_n X` is *locally the class of the simplex `Δ` at `x`*: for every
locally finite cycle `z` representing `ν` and every relative cocycle `φ` of `(X, X - x)`,
`⟨φ, z⟩ = φ(Δ)`, i.e. `z` and `Δ` have the same image in the local homology `H_n(X, X - x)`. -/
def IsLocallyClassOf {n : ℕ} (ν : borelMooreHomology R (ModuleCat.of R R) X n) (x : X)
    (Δ : Simplex X n) : Prop :=
  ∀ z : (borelMooreChainComplex R (ModuleCat.of R R) X).cycles n,
    (borelMooreChainComplex R (ModuleCat.of R R) X).homologyπ n z =
      (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X n).hom ν →
    ∀ φ ∈ relCocycles R ({x}ᶜ : Set X) n,
      localPairing (((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n z).1) φ = φ Δ

end Local

section Chart

variable {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [ContinuousAdd H]
  [ContinuousSMul ℝ H] {M : Type u} [TopologicalSpace M]

/-- The coordinate ball of a chart `e`: its domain, an open subset of `M`. -/
def chartOpens (e : OpenPartialHomeomorph M H) : TopologicalSpace.Opens (TopCat.of M) :=
  ⟨e.source, e.open_source⟩

/-- A point lies in the coordinate ball of `e` if and only if it lies in the source of `e`. -/
@[simp]
lemma mem_chartOpens {e : OpenPartialHomeomorph M H} {x : M} :
    x ∈ chartOpens e ↔ x ∈ e.source :=
  Iff.rfl

/-- The singular simplex `e⁻¹ ∘ Δ` of the coordinate ball of `e`, for the affine simplex `Δ`
with vertices `v` in the image of `e`. -/
def chartSimplex (e : OpenPartialHomeomorph M H) {n : ℕ} (v : Fin (n + 1) → H)
    (hv : range (affineSimplex v) ⊆ e.target) : Simplex (chartOpens e) n :=
  ⟨fun t ↦ ⟨e.symm (affineSimplex v t), e.map_target (hv ⟨t, rfl⟩)⟩,
    (e.continuousOn_symm.comp_continuous (affineSimplex v).continuous
      fun t ↦ hv ⟨t, rfl⟩).subtype_mk _⟩

/-- The simplex `chartSimplex e v hv` sends `t` to `e.symm (affineSimplex v t)` in `M`. -/
@[simp]
lemma coe_chartSimplex_apply (e : OpenPartialHomeomorph M H) {n : ℕ} (v : Fin (n + 1) → H)
    (hv : range (affineSimplex v) ⊆ e.target) (t : stdSimplex ℝ (Fin (n + 1))) :
    (chartSimplex e v hv t : M) = e.symm (affineSimplex v t) :=
  rfl

/-- The boundary of `e⁻¹ ∘ Δ`, for `Δ` an oriented simplex around `e x`, avoids `x`: the simplex
is a relative cycle of `(B, B - x)`. -/
lemma chartSimplex_ne {e : OpenPartialHomeomorph M H} {n : ℕ} {b : Module.Basis (Fin n) ℝ H}
    {x : chartOpens e} {v : Fin (n + 1) → H}
    (hv : IsOrientedSimplexAroundZero b fun k ↦ v k - e x)
    (hvt : range (affineSimplex v) ⊆ e.target) (t : stdSimplex ℝ (Fin (n + 1)))
    (ht : ∃ i, t i = 0) : chartSimplex e v hvt t ≠ x := by
  intro h
  have h' : affineSimplex v t = e x := by
    have := congrArg (fun y : chartOpens e ↦ e y) h
    simp only at this
    rwa [coe_chartSimplex_apply, e.right_inv (hvt ⟨t, rfl⟩)] at this
  apply hv.affineSimplex_ne_zero t ht
  rw [affineSimplex_apply] at h' ⊢
  have hsum : ∑ k, (t : Fin (n + 1) → ℝ) k = 1 := t.2.2
  simp only [smul_sub, Finset.sum_sub_distrib, h', ← Finset.sum_smul, hsum, one_smul, sub_self]

variable (R : Type u) [CommRing R]

/-- A class `ν ∈ H_n B` of the coordinate ball `B` of the chart `e` is the *orientation
generator* for the orientation of the basis `b`: at every point `x` of `B` it is locally the class
of `e⁻¹ ∘ Δ`, for every affine `n`-simplex `Δ` of `e(B)` around `e(x)` positively oriented for
`b`. -/
def IsChartOrientationClass {n : ℕ} (b : Module.Basis (Fin n) ℝ H)
    (e : OpenPartialHomeomorph M H)
    (ν : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (chartOpens e)) n) : Prop :=
  ∀ (x : chartOpens e) (v : Fin (n + 1) → H) (_ : IsOrientedSimplexAroundZero b fun k ↦ v k - e x)
    (hvt : range (affineSimplex v) ⊆ e.target),
    IsLocallyClassOf R ν x (chartSimplex e v hvt)

end Chart

end FundamentalClass

open FundamentalClass

section Manifold

variable (R : Type u) [CommRing R] {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
  [ContinuousAdd H] [ContinuousSMul ℝ H] {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace H M]

/-- The *fundamental class* `μ_M ∈ H_n M` (Fulton, §19.1; Iversen, IX.4) of a real
`n`-manifold `M`, oriented in its charts by the basis `b` of the model space `H`: the Borel–Moore
class whose restriction to every coordinate ball `B` (the domain of a chart `e`) is the
orientation generator of `H_n B`. -/
def IsFundamentalClass {n : ℕ} (b : Module.Basis (Fin n) ℝ H)
    (μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n) : Prop :=
  ∀ e ∈ atlas H M,
    IsChartOrientationClass R b e (borelMooreHomology.restrict R _ (chartOpens e) n μ)

end Manifold

section Complex

variable (R : Type u) [CommRing R] {m : ℕ} (M : Type u) [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin m → ℂ) M]

/-- The *fundamental class* `μ_M ∈ H_{2m} M` (Fulton, §19.1) of a complex manifold `M` of complex
dimension `m`, oriented by its complex structure: in every holomorphic chart, the orientation of
the real basis `e₁, i e₁, …, e_m, i e_m` of `ℂ^m`. -/
abbrev IsComplexFundamentalClass [IsManifold 𝓘(ℂ, Fin m → ℂ) ⊤ M]
    (μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) (2 * m : ℕ)) : Prop :=
  IsFundamentalClass R (complexOrientationBasis m) μ

end Complex

end MMP
