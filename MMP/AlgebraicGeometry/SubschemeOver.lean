module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed subschemes of a scheme over a base

A closed subscheme `I.subscheme` of a scheme `Y` over `S` is a scheme over `S` through its
inclusion `I.subscheme ⟶ Y ⟶ S`, and that inclusion is then a morphism over `S`. Neither Mathlib
nor the Stacks project registers this. The instances are scoped, since a closed subscheme may carry
another structure of a scheme over `S`: open them with `open scoped MMP.SubschemeOver`.

## Main definitions

* `MMP.SubschemeOver.overSubscheme`: the structure of a scheme over `S` on `I.subscheme`.
* `MMP.SubschemeOver.isOver_subschemeι`: `I.subschemeι` is a morphism over `S`.
* `MMP.SubschemeOver.locallyOfFiniteType_subscheme`: `I.subscheme` is locally of finite type
  over `S` when `Y` is.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP.SubschemeOver

/-- A closed subscheme `I.subscheme` of a scheme `Y` over `S` is a scheme over `S` through its
inclusion `I.subscheme ⟶ Y ⟶ S`. -/
noncomputable scoped instance overSubscheme {S Y : Scheme.{u}} [Y.Over S] (I : Y.IdealSheafData) :
    I.subscheme.Over S :=
  ⟨I.subschemeι ≫ Y ↘ S⟩

/-- The inclusion of a closed subscheme of a scheme over `S` is a morphism over `S`. -/
scoped instance isOver_subschemeι {S Y : Scheme.{u}} [Y.Over S] (I : Y.IdealSheafData) :
    I.subschemeι.IsOver S :=
  ⟨rfl⟩

/-- A closed subscheme of a scheme locally of finite type over `S` is locally of finite type
over `S`. -/
scoped instance locallyOfFiniteType_subscheme {S Y : Scheme.{u}} [Y.Over S]
    [LocallyOfFiniteType (Y ↘ S)] (I : Y.IdealSheafData) :
    LocallyOfFiniteType (I.subscheme ↘ S) :=
  inferInstanceAs (LocallyOfFiniteType (I.subschemeι ≫ Y ↘ S))

end MMP.SubschemeOver
