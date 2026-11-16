module

public import MMP.AlgebraicGeometry.Variety.ParameterPoint
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ParameterPointFibre
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.HomotopyInfraGeneric
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# The complex point of a parameter point (generic part)

* `MMP.Scheme.Hom.ker_eq_ker_of_range_eq`: closed immersions of reduced schemes with the same
  image have the same kernel.
* `MMP.ParameterPoint.ker_toHom_complexPoint`: the complex point of a parameter point `t` of a
  separated complex scheme locally of finite type cuts out the same closed subscheme as `t`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set

namespace MMP

/-- **Closed immersions of reduced schemes with the same image have the same kernel.** -/
theorem Scheme.Hom.ker_eq_ker_of_range_eq {X X' Y : Scheme.{0}} [IsReduced X] [IsReduced X']
    (f : X ⟶ Y) (g : X' ⟶ Y) [IsClosedImmersion f] [IsClosedImmersion g]
    (h : range f = range g) : f.ker = g.ker := by
  have hf : IsReduced f.ker.subscheme := isReduced_of_isOpenImmersion (inv f.toImage)
  have hg : IsReduced g.ker.subscheme := isReduced_of_isOpenImmersion (inv g.toImage)
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme f.ker f.ker.support rfl,
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme g.ker g.ker.support rfl]
  congr 1
  ext1
  rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker, h]

namespace ParameterPoint

variable {T : Scheme.{0}} [T.Over (Spec (.of ℂ))] [LocallyOfFiniteType (T ↘ Spec (.of ℂ))]
  [IsSeparated (T ↘ Spec (.of ℂ))]

/-- The complex point of a parameter point `t` cuts out the same closed subscheme of `T` as
`t : Spec κ(t) → T`: the reduced point `t`. -/
theorem ker_toHom_complexPoint (t : ParameterPoint T) : t.complexPoint.toHom.ker = t.ι.ker := by
  refine Scheme.Hom.ker_eq_ker_of_range_eq _ _ ?_
  rw [range_ι]
  ext x
  simp only [mem_range, mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl⟩
    rw [Subsingleton.elim y (IsLocalRing.closedPoint ℂ), complexPoint_toHom_closedPoint]
  · rintro rfl
    exact ⟨_, complexPoint_toHom_closedPoint t⟩

end ParameterPoint

end MMP
