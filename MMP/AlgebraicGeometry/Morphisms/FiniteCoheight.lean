module

public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationFiniteFibres
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic

/-!
# Dimensions along a finite cover

Let `g : Y ⟶ X` be a finite morphism of integral schemes locally of finite type over a field `k`,
with `dim Y = dim X < ∞`. The residue field extensions of `g` are finite, so the closures of `y`
and of `g y` have the same dimension `trdeg_k κ(y) = trdeg_k κ(g y)`, and `y` and `g y` have the
same codimension. If `X` is smooth of relative dimension `n` over `k` and `g` is moreover
dominant and `Y` smooth over `k`, then `Y` is smooth of relative dimension `n`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.coheight_map_eq_of_isFinite`: finite morphisms of
  varieties of the same dimension preserve codimension.
* `MMP.FourfoldProofs.FractionalLogComplexProof.smoothOfRelativeDimension_comp_of_isFinite`: the
  relative dimension of a smooth finite dominant cover.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

variable {k : Type} [Field k]

/-- **Finite morphisms of varieties of the same dimension preserve codimension.** For a finite
morphism `g : Y ⟶ X` of integral schemes locally of finite type over a field, with
`dim Y = dim X < ∞`, every point `y` has the codimension of `g y`. -/
theorem coheight_map_eq_of_isFinite {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [IsIntegral Y] [LocallyOfFiniteType sX] (g : Y ⟶ X) [IsFinite g]
    (hdim : topologicalKrullDim Y = topologicalKrullDim X) (hfin : topologicalKrullDim X ≠ ⊤)
    (y : Y) : Order.coheight (g y) = Order.coheight y := by
  have hY := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (g ≫ sX) y
  have hX := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (g y)
  have htr := MMP.Flips.trdeg_residueField_add (g ≫ sX) sX g rfl y
  have hfinres : (g.residueFieldMap y).hom.Finite :=
    finite_residueFieldMap_of_surjective_of_locallyOfFiniteType (𝟙 Y) g
      (fun x => ⟨x, rfl⟩) y
  let : Algebra (X.residueField (g y)) (Y.residueField y) := (g.residueFieldMap y).hom.toAlgebra
  have : Module.Finite (X.residueField (g y)) (Y.residueField y) := hfinres
  have halg : Algebra.trdeg (X.residueField (g y)) (Y.residueField y) = 0 :=
    trdeg_eq_zero
  rw [halg, add_zero] at htr
  have hcl : topologicalKrullDim (closure {y} : Set Y) =
      topologicalKrullDim (closure {g y} : Set X) := by
    rw [topologicalKrullDim_closure_singleton_eq_trdeg k Y (g ≫ sX),
      topologicalKrullDim_closure_singleton_eq_trdeg k X sX, ← htr]
  rw [hcl, hdim, ← hX] at hY
  obtain ⟨a, ha⟩ : ∃ a : ℕ∞, topologicalKrullDim (closure {g y} : Set X) = a :=
    WithBot.ne_bot_iff_exists.mp (by
      rw [topologicalKrullDim_closure_singleton_eq_trdeg k X sX]; exact WithBot.coe_ne_bot)
      |>.imp fun a h => h.symm
  rw [ha, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_inj] at hY
  have hatop : a ≠ ⊤ := by
    intro h
    rw [← hX, ha, h, ← WithBot.coe_add, top_add] at hfin
    exact hfin rfl
  exact (WithTop.add_left_cancel hatop hY).symm

/-- **The relative dimension of a smooth finite dominant cover.** Let `π : X ⟶ Spec k` be smooth
of relative dimension `n` with `X` irreducible, and `g : Y ⟶ X` finite dominant with `g ≫ π` a
smooth variety. Then `g ≫ π` is smooth of relative dimension `n`. -/
theorem smoothOfRelativeDimension_comp_of_isFinite {X Y : Scheme.{0}} (π : X ⟶ Spec (.of k))
    (n : ℕ) [SmoothOfRelativeDimension n π] [IrreducibleSpace X] (g : Y ⟶ X) [IsFinite g]
    [IsDominant g] [MMP.Mori.IsVariety k (g ≫ π)] [Smooth (g ≫ π)] :
    SmoothOfRelativeDimension n (g ≫ π) :=
  MMP.Intersection.smoothOfRelativeDimension_of_isVariety (g ≫ π) n (by
    rw [topologicalKrullDim_eq_of_isFinite_of_isDominant g,
      topologicalKrullDim_eq_of_smoothOfRelativeDimension π n])

end MMP.FourfoldProofs.FractionalLogComplexProof
