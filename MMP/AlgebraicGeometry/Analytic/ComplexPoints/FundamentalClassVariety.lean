module

public import MMP.AlgebraicTopology.FundamentalClass.Basic
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartManifold
public import MMP.AlgebraicTopology.FundamentalClass.EuclideanComplexOrientation
/-!
# Fundamental classes of complex varieties (Fulton, §19.1)

Let `V` be a complex variety of dimension `n`. Its regular part `V_reg(ℂ)` is an open subset of
`V(ℂ)` and a complex manifold of complex dimension `n`
(`MMP.UnderlyingSpace.isManifold_regularOpens`), oriented by its complex
structure; it has the Borel–Moore fundamental class `μ_{V_reg} ∈ H_{2n} V_reg`. A class
`c ∈ H_{2n} V` is *a fundamental class of `V`* if its restriction to `V_reg` is `μ_{V_reg}`.
Such a class exists and is unique, and is then written `cl(V)`.

## Main definitions

* `MMP.IsVarietyFundamentalClass`: `c ∈ H_{2n} V` is a fundamental class of the
  complex variety `V` of dimension `n`.

## Implementation notes

The regular part `V_reg(ℂ)` carries the atlas of algebraic charts
(`MMP.UnderlyingSpace.regularChartedSpace`), modelled on the Euclidean space
`EuclideanSpace ℂ (Fin n)`; its orientation is that of the real basis
`e₁, i e₁, …, e_n, i e_n`, which is the complex orientation of `IsComplexFundamentalClass`
transported to the Euclidean model.

Restriction of Borel–Moore homology to open subsets is defined for Hausdorff spaces, so `V(ℂ)` is
assumed Hausdorff; this holds when `V` is separated over `ℂ`
(`MMP.UnderlyingSpace.t2Space_of_isSeparated`), as all of Fulton's schemes are
(Fulton, B.2.3), and is an instance for complex schemes.

The coefficients are an arbitrary commutative ring `R`; Fulton's are `ℤ`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MMP.ThomClass MMP.UnderlyingSpace

namespace MMP

open FundamentalClass

variable (R : Type) [CommRing R] {V : Scheme.{0}} [V.Over (Spec (.of ℂ))] [IsIntegral V]
  [LocallyOfFiniteType (V ↘ Spec (.of ℂ))] [QuasiCompact (V ↘ Spec (.of ℂ))]
  [T2Space (UnderlyingSpace ℂ V)]

/-- A class `c ∈ H_{2n} V` is *a fundamental class* of the complex variety `V` of dimension `n`
(Fulton, §19.1) if its restriction to the regular part `V_reg(ℂ)`, a complex manifold of
complex dimension `n` oriented by its complex structure, is the fundamental class
`μ_{V_reg} ∈ H_{2n} V_reg`. -/
def IsVarietyFundamentalClass {n : ℕ} (hn : (n : WithBot ℕ∞) = topologicalKrullDim V)
    (c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * n : ℕ)) :
    Prop :=
  letI := regularChartedSpace (𝕜 := ℂ) hn
  IsFundamentalClass R (euclideanComplexOrientationBasis n)
    (borelMooreHomology.restrict R _
      (regularOpens ℂ V : Opens (TopCat.of (UnderlyingSpace ℂ V))) (2 * n : ℕ) c)

end MMP
