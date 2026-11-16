module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Intersection.InvertibleSheafCurveDegree
public import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
import MMP.AlgebraicGeometry.Intersection.GenericallyFinitePullback

/-!
# Birational invariance of the intersection number

Let `X` and `X'` be proper schemes over a field `k`, `Z ⊆ X` and `Z' ⊆ X'` closed integral
subschemes of dimension `d`, and `f : X' ⟶ X` a `k`-morphism that restricts to a birational
morphism `h : Z' ⟶ Z`. For invertible sheaves `L₁, …, L_d` on `X` the intersection numbers agree:
`(L₁ ⋯ L_d · Z) = (f^*L₁ ⋯ f^*L_d · Z')`.

## Main results

* `MMP.Mori.sheafIntersectionNumber_pullback_eq_of_isBirationalMorphism`: the intersection
  number `(L₁ ⋯ L_d · Z)` equals `(f^*L₁ ⋯ f^*L_d · Z')`.

## Implementation notes

The intersection number is `MMP.Mori.sheafIntersectionNumber`, stated for invertible sheaves;
Cartier divisors `D_j` enter through their invertible sheaves `𝒪_X(D_j)`, whose pull-backs are
the sheaves `𝒪_{X'}(f^*D_j)`. The restriction of `f` is recorded as a morphism `h : Z' ⟶ Z`
with `h ≫ i = i' ≫ f`, where `i` and `i'` are the closed immersions.

Both sides are computed on `Z` and `Z'` themselves, where they are related by the projection
formula for the proper dominant morphism `h`, whose function-field degree is one.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.35
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

/-- The intersection number depends on the structure morphism only through its value. -/
private theorem sheafIntersectionNumber_congr_structure (k : Type u) [Field k]
    {X Z : Scheme.{u}} {s s' : X ⟶ Spec (.of k)} (hs : s = s') [IsProper s] [IsProper s']
    (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Z ≤ d)
    (L : Fin d → X.Modules) [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    sheafIntersectionNumber k s i d hd L = sheafIntersectionNumber k s' i d hd L := by
  subst hs; rfl

/-- The intersection number `(L₁ ⋯ L_d · Z)` is the top intersection number of the restrictions
`L_j|_Z` on `Z`. -/
private theorem sheafIntersectionNumber_eq_restrict (k : Type u) [Field k] {X Z : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [IsProper s] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (L' : Fin d → Z.Modules) [∀ j, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 (L' j)]
    (e : ∀ j, (Scheme.Modules.pullback i).obj (L j) ≅ L' j) :
    sheafIntersectionNumber k s i d hd L = sheafIntersectionNumber k (i ≫ s) (𝟙 Z) d hd L' := by
  rw [sheafIntersectionNumber_congr_hom k s (Category.id_comp i).symm d hd L]
  exact sheafIntersectionNumber_comp_eq_of_iso k s i (𝟙 Z) d hd L L' e

/-- A birational morphism of integral schemes has function-field degree one. -/
private theorem finrank_functionField_eq_one {Z Z' : Scheme.{u}} [IsIntegral Z]
    [IsIntegral Z'] {h : Z' ⟶ Z} [IsDominant h] (hbir : IsBirationalMorphism h) :
    letI := functionFieldMapAlgebra h; Module.finrank Z.functionField Z'.functionField = 1 := by
  letI := functionFieldMapAlgebra h
  rw [← (AlgEquiv.ofBijective (Algebra.ofId Z.functionField Z'.functionField)
    (hbir.functionFieldMap_bijective :
      Function.Bijective (algebraMap Z.functionField Z'.functionField))).toLinearEquiv.finrank_eq,
    Module.finrank_self]

/-- **Birational invariance of the intersection number.** Let `X`, `X'` be proper `k`-schemes,
`i : Z ⟶ X` and `i' : Z' ⟶ X'` closed integral subschemes of dimension `d`, and `f : X' ⟶ X` a
`k`-morphism restricting to a birational morphism `h : Z' ⟶ Z`. Then for invertible sheaves
`L₁, …, L_d` on `X`, `(L₁ ⋯ L_d · Z) = (f^*L₁ ⋯ f^*L_d · Z')`. -/
@[mmp "lem_mmp_foundation_km_intersection_birational_invariance"]
public theorem sheafIntersectionNumber_pullback_eq_of_isBirationalMorphism (k : Type u) [Field k]
    {X X' Z Z' : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX]
    (sX' : X' ⟶ Spec (.of k)) [IsProper sX'] (f : X' ⟶ X) (hf : f ≫ sX = sX')
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ X') [IsClosedImmersion i']
    [IsIntegral Z] [IsIntegral Z'] (h : Z' ⟶ Z) (hh : h ≫ i = i' ≫ f)
    (hbir : IsBirationalMorphism h) (d : ℕ) (hZ : topologicalKrullDim Z = d)
    (hZ' : topologicalKrullDim Z' = d) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    sheafIntersectionNumber k sX i d hZ.le L =
      sheafIntersectionNumber k sX' i' d hZ'.le fun j => (Scheme.Modules.pullback f).obj (L j) := by
  have hcomp : h ≫ i ≫ sX = i' ≫ sX' := by rw [← Category.assoc, hh, Category.assoc, hf]
  have : IsProper (h ≫ i ≫ sX) := hcomp ▸ inferInstance
  have : IsProper h := .of_comp h (i ≫ sX)
  have : IsDominant h := hbir.isDominant
  -- `i'^* f^* L_j ≅ h^* i^* L_j`, from `h ≫ i = i' ≫ f`
  let e j : (Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback f).obj (L j)) ≅
      (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback i).obj (L j)) :=
    (Scheme.Modules.pullbackComp i' f).app (L j) ≪≫ eqToIso (by rw [← hh]) ≪≫
      ((Scheme.Modules.pullbackComp h i).app (L j)).symm
  rw [sheafIntersectionNumber_eq_restrict k sX i d hZ.le L _ (fun j => Iso.refl _),
    sheafIntersectionNumber_eq_restrict k sX' i' d hZ'.le _ _ e,
    ← sheafIntersectionNumber_congr_structure k hcomp (𝟙 Z') d hZ'.le,
    sheafIntersectionNumber_pullback_eq_finrank_mul k (i ≫ sX) h d hZ hZ',
    finrank_functionField_eq_one hbir, Nat.cast_one, one_mul]

end MMP.Mori
