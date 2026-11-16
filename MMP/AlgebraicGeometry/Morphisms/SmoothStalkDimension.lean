module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.LocalRing
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalVirtualNormalBundle

/-!
# Dimension of the local rings of a smooth morphism

For a flat morphism `g : Y ⟶ Z`, locally of finite type and of relative dimension `n`, between
locally Noetherian schemes, the dimension of the local ring at a point `y` whose residue field is
that of `g y` is `dim 𝒪_{Z, g y} + n` (Stacks 00ON for flat local maps, with Stacks 02FX for the
fibre). In particular, if `g` is smooth of relative dimension `n` and `i : X ⟶ Y` is a closed
immersion with `i ≫ g` a closed immersion, then `dim 𝒪_{Y, i x} = dim 𝒪_{Z, g (i x)} + n`.

## Main results

* `MMP.ringKrullDim_stalk_eq_add_of_relativeDimension`
* `MMP.ringKrullDim_stalk_eq_add_of_smoothOfRelativeDimension`
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP

variable {X Y Z : Scheme.{u}}

/-- Let `g : Y ⟶ Z` be flat, locally of finite type and of relative dimension `n` between locally
Noetherian schemes, and let `y ∈ Y` be a point whose residue field is that of `g y`. Then
`dim 𝒪_{Y, y} = dim 𝒪_{Z, g y} + n`. -/
theorem ringKrullDim_stalk_eq_add_of_relativeDimension (g : Y ⟶ Z) [Flat g]
    [LocallyOfFiniteType g] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z] {n : ℕ}
    (hn : AlgebraicGeometry.RelativeDimension g n) (y : Y)
    (hy : Function.Surjective (g.residueFieldMap y)) :
    ringKrullDim (Y.presheaf.stalk y) = ringKrullDim (Z.presheaf.stalk (g y)) + n := by
  have hq : LocallyOfFiniteType (g.fiberToSpecResidueField (g y)) :=
    (inferInstance : LocallyOfFiniteType (Limits.pullback.snd g (Z.fromSpecResidueField (g y))))
  obtain ⟨heq, hd⟩ := hn (g y) ⟨g.asFiber y⟩
  have hAt := topologicalKrullDimAt_eq_of_equidimensional (Z.residueField (g y)) (g.fiber (g y))
    (g.fiberToSpecResidueField (g y)) heq hd (g.asFiber y)
  have hfx := topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg g y
  letI := (g.residueFieldMap y).hom.toAlgebra
  have htr : Algebra.trdeg (Z.residueField (g y)) (Y.residueField y) = 0 := by
    have : Algebra.IsAlgebraic (Z.residueField (g y)) (Y.residueField y) :=
      ⟨fun a => by
        obtain ⟨b, rfl⟩ := hy a
        exact isAlgebraic_algebraMap b⟩
    exact trdeg_eq_zero_iff.mpr this
  rw [htr, hAt] at hfx
  simp only [map_zero, WithBot.coe_zero, add_zero] at hfx
  rw [ringKrullDim_stalk_eq_add_ringKrullDim_stalk_fiber_of_flat g y, ← hfx]

/-- Let `g : Y ⟶ Z` be smooth of relative dimension `n` between locally Noetherian schemes and
`i : X ⟶ Y` a closed immersion with `i ≫ g` a closed immersion. Then at every point `x` of `X`,
`dim 𝒪_{Y, i x} = dim 𝒪_{Z, g (i x)} + n`: the residue fields of `i x` and `g (i x)` agree. -/
theorem ringKrullDim_stalk_eq_add_of_smoothOfRelativeDimension (i : X ⟶ Y) (g : Y ⟶ Z)
    [IsLocallyNoetherian Y] [IsLocallyNoetherian Z] [IsClosedImmersion i]
    [IsClosedImmersion (i ≫ g)] {n : ℕ} [SmoothOfRelativeDimension n g] (x : X) :
    ringKrullDim (Y.presheaf.stalk (i x)) =
      ringKrullDim (Z.presheaf.stalk ((i ≫ g) x)) + n := by
  have : Smooth g := SmoothOfRelativeDimension.smooth n g
  have hrel : AlgebraicGeometry.RelativeDimension g n :=
    SmoothOfRelativeDimension.relativeDimension n g
  have hs : Function.Surjective ((i ≫ g).residueFieldMap x) := by
    intro a
    obtain ⟨a, rfl⟩ := X.residue_surjective x a
    obtain ⟨b, rfl⟩ := (i ≫ g).stalkMap_surjective x a
    refine ⟨Z.residue _ b, ?_⟩
    rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]
  rw [Scheme.residueFieldMap_comp] at hs
  have hinj : Function.Injective (i.residueFieldMap x) := (i.residueFieldMap x).hom.injective
  refine ringKrullDim_stalk_eq_add_of_relativeDimension g hrel (i x) fun a => ?_
  obtain ⟨b, hb⟩ := hs (i.residueFieldMap x a)
  exact ⟨b, hinj (by rw [← hb]; rfl)⟩

end MMP
