module

public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Finite morphisms and function fields

* `MMP.moduleFinite_residueField`: a locally quasi-finite morphism locally of finite type has
  finite residue field extensions.
* `MMP.residue_dominantFunctionFieldMap`: for a dominant morphism of integral schemes, the
  function field map agrees with the residue field map at the generic point.
* `MMP.moduleFinite_functionField_of_isFinite`: for a finite dominant morphism `f : X → Y` of
  integral schemes, `R(X)` is a finite extension of `R(Y)` (through Stacks'
  `dominantFunctionFieldMap`).
* `MMP.isIntegral_of_iso`: integrality is invariant under isomorphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP

/-- For a locally quasi-finite morphism `f : X → Y` locally of finite type, the residue field
extension `κ(f x) → κ(x)` is finite at every point `x`. -/
theorem moduleFinite_residueField {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    [LocallyOfFiniteType f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (Y.residueField (f x)) (X.residueField x) :=
  (isClosed_asFiber_iff_finite_residueField f x).mp (isClosed_discrete _)

/-- The function field map of a dominant morphism of integral schemes, read in the residue
fields at the generic points, is the residue field map at the generic point of the source. -/
theorem residue_dominantFunctionFieldMap {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (a : Y.functionField) :
    (X.residue (genericPoint X)).hom (dominantFunctionFieldMap f a) =
      (f.residueFieldMap (genericPoint X)).hom ((Y.residueFieldCongr
        (map_genericPoint_of_isDominant f).symm).hom.hom
          ((Y.residue (genericPoint Y)).hom a)) := by
  have hgen : f (genericPoint X) = genericPoint Y := map_genericPoint_of_isDominant f
  have hcast : dominantFunctionFieldMap f =
      ((Y.presheaf.stalkCongr (.of_eq hgen.symm)).hom ≫ f.stalkMap (genericPoint X)).hom := by
    dsimp [dominantFunctionFieldMap]
    rw [stalkMap_cast_target]
    rfl
  have hmaps : ((Y.residue (genericPoint Y) ≫ (Y.residueFieldCongr hgen.symm).hom) ≫
      f.residueFieldMap (genericPoint X)) =
      ((Y.presheaf.stalkCongr (.of_eq hgen.symm)).hom ≫ f.stalkMap (genericPoint X)) ≫
        X.residue (genericPoint X) := by
    rw [Category.assoc, Scheme.residue_residueFieldCongr_assoc, Scheme.residue_residueFieldMap,
      Category.assoc]
  rw [hcast]
  exact (congrArg (fun k : CommRingCat.Hom _ _ ↦ k.hom a) hmaps).symm

/-- For a finite dominant (e.g. finite surjective) morphism `f : X → Y` of integral schemes, the
function field `R(X)` is a finite extension of `R(Y)` (Fulton, §1.4). -/
theorem moduleFinite_functionField_of_isFinite {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f] :
    letI := (dominantFunctionFieldMap f).toAlgebra
    Module.Finite Y.functionField X.functionField := by
  have hgen : f (genericPoint X) = genericPoint Y := map_genericPoint_of_isDominant f
  have hres : (f.residueFieldMap (genericPoint X)).hom.Finite :=
    moduleFinite_residueField f (genericPoint X)
  let eX : X.functionField ≃+* X.residueField (genericPoint X) :=
    RingEquiv.ofBijective (X.residue (genericPoint X)).hom
      ⟨RingHom.injective _, X.residue_surjective _⟩
  let eY : Y.functionField ≃+* Y.residueField (f (genericPoint X)) :=
    (RingEquiv.ofBijective (Y.residue (genericPoint Y)).hom
      ⟨RingHom.injective _, Y.residue_surjective _⟩).trans
        (Y.residueFieldCongr hgen.symm).commRingCatIsoToRingEquiv
  have heq : dominantFunctionFieldMap f =
      (eX.symm.toRingHom.comp (f.residueFieldMap (genericPoint X)).hom).comp eY.toRingHom := by
    ext a
    apply eX.injective
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, RingEquiv.apply_symm_apply]
    exact residue_dominantFunctionFieldMap f a
  change (dominantFunctionFieldMap f).Finite
  rw [heq]
  exact ((RingHom.Finite.of_surjective _ eX.symm.surjective).comp hres).comp
    (RingHom.Finite.of_surjective _ eY.surjective)

/-- Integrality of schemes is invariant under isomorphism: if `A ≅ B` and `A` is integral, then
so is `B`. -/
theorem isIntegral_of_iso {A B : Scheme.{u}} (e : A ≅ B) [IsIntegral A] : IsIntegral B :=
  .of_isIso e.hom

end MMP
