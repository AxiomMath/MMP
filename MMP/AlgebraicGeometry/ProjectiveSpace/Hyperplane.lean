module

public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneIsProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjSaturation.IdealOfClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.ChartBasicOpen

/-!
# Coordinates and hyperplanes of projective space over a field

Projective space over a field `K` is `Proj K[T₀, …, Tₙ] = Proj (polyGrading K n)` (Stacks'
polynomial model). At every point some homogeneous coordinate does not vanish, and a point lies on
the hyperplane `Stacks.ProjectiveSpace.hyperplane l` of a linear form `l` iff its homogeneous prime
contains `l`.

## Main results

* `MMP.ProjectiveSpace.exists_X_notMem`: some coordinate `Tᵢ` is not in the homogeneous prime of a
  point.
* `MMP.ProjectiveSpace.mem_support_hyperplane_iff`: the support of the hyperplane `{l = 0}`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

universe u

namespace MMP.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {n : ℕ}

/-- At every point of `ℙⁿ` some homogeneous coordinate does not vanish. -/
theorem exists_X_notMem (x : AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading K n)) :
    ∃ i, (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) ∉ x.asHomogeneousIdeal := by
  by_contra! h
  refine x.not_irrelevant_le fun a ha => ?_
  have := Stacks.AlgebraicGeometry.ProjPolyChart.irrelevant_le_span_X K n ha
  exact (Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)) this

/-- The nonvanishing locus of the chart function `l / g` on `{g ≠ 0}` is `{g ≠ 0} ∩ {l ≠ 0}`. -/
theorem basicOpen_degreeOneChartFraction
    (g l : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K 1) :
    (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading K n)).basicOpen
        (Stacks.ProjectiveSpace.degreeOneChartFraction _ g.2 l.2) =
      Proj.basicOpen _ (g : MvPolynomial (Fin (n + 1)) K) ⊓
        Proj.basicOpen _ (l : MvPolynomial (Fin (n + 1)) K) :=
  Stacks.ProjChartBasicOpen.basicOpen_awayToSection_mk _ g.2 Nat.one_pos 1 _ _

/-- **The support of a hyperplane.** A point of `ℙⁿ` lies on the hyperplane `{l = 0}` iff its
homogeneous prime contains `l`. -/
theorem mem_support_hyperplane_iff (l : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K 1)
    (x : AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading K n)) :
    x ∈ (Stacks.ProjectiveSpace.hyperplane l).support ↔
      (l : MvPolynomial (Fin (n + 1)) K) ∈ x.asHomogeneousIdeal := by
  obtain ⟨i, hi⟩ := exists_X_notMem x
  let g : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K 1 :=
    ⟨MvPolynomial.X i, Stacks.AlgebraicGeometry.ProjPolyChart.X_mem_one K n i⟩
  have hxg : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (g : MvPolynomial (Fin (n + 1)) K) := by
    rw [Proj.mem_basicOpen]; exact hi
  have hideal : (Stacks.ProjectiveSpace.hyperplane l).ideal
      ⟨Proj.basicOpen _ (g : MvPolynomial (Fin (n + 1)) K),
        Proj.isAffineOpen_basicOpen _ _ g.2 Nat.one_pos⟩ =
      Ideal.span {(Stacks.ProjectiveSpace.degreeOneChartFraction
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) g.2 l.2)} :=
    ProjectiveSpectrum.Proj.zeroScheme_degreeSection_ideal_basicOpen_of_degree_eq _ g.2
      Nat.one_pos 1 (by simp) l (by simp [l.2])
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem
      (U := ⟨_, Proj.isAffineOpen_basicOpen _ _ g.2 Nat.one_pos⟩) hxg,
    hideal, Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [basicOpen_degreeOneChartFraction]
  simp only [TopologicalSpace.Opens.mem_inf, not_and, Proj.mem_basicOpen, not_not]
  exact ⟨fun h => h hi, fun h _ => h⟩

end MMP.ProjectiveSpace
