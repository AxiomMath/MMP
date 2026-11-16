module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Variety.Basic
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.GenericallyFiniteDominant
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Equal-dimensional dominant morphisms are generically finite

Let `f : X ⟶ Y` be a morphism of schemes locally of finite type over a field `K`, `V` a
subvariety of `X` and `W = \overline{f(V)}` its image. If `dim V = dim W`, then the function field
`R(V)` is a finite extension of `f^* R(W)`. Indeed `R(V)` and `R(W)` are the residue fields at the
generic points `ξ` of `V` and `f ξ` of `W`, whose transcendence degrees over `K` are `dim V` and
`dim W`; additivity of transcendence degrees in the tower `K ⊆ R(W) ⊆ R(V)` makes `R(V)` algebraic
over `R(W)`, and an algebraic extension essentially of finite type is finite.

For a dominant morphism `f : Y ⟶ X` of integral schemes locally of finite type over `k` with
`dim Y = dim X`, the same argument shows that `k(Y)` is finite over `k(X)`. If moreover `f` is
quasi-compact (for instance if `Y` is of finite type over `k`), then there is a dense open
`U ⊆ X` such that `f⁻¹(U) → U` is finite: finiteness of `k(Y)/k(X)` forces the generic point of
`Y` to be the only point over the generic point of `X`, and such a morphism is finite over a
nonempty affine open of the target (Stacks 02NX).

## Main results

* `MMP.Intersection.Scheme.Subvariety.finite_functionFieldMap_of_topologicalKrullDim_eq`: for `f`
  locally of finite type, `Y` locally of finite type over `K` and `dim V = dim f(V)`, the embedding
  `f^* : R(f(V)) → R(V)` is finite.
* `MMP.Mori.finite_functionField_of_topologicalKrullDim_eq`: for a dominant morphism `f : Y ⟶ X`
  of integral schemes locally of finite type over `k` with `dim Y = dim X`, `k(Y)` is a finite
  extension of `k(X)`.
* `MMP.Mori.exists_dense_isFinite_restrict_of_topologicalKrullDim_eq`: if moreover `f` is
  quasi-compact, `f⁻¹(U) → U` is finite for some dense open `U ⊆ X`.

## Implementation notes

The source states the second result for complex varieties; it is proved here over an arbitrary
field and for integral schemes locally of finite type, with `f` quasi-compact for the second
assertion. Quasi-compactness cannot be dropped: the affine line with infinitely many doubled
closed points maps to the affine line, dominantly and with equal dimensions, but is finite over no
dense open. The finiteness of `f⁻¹(U) → U` is obtained from the Stacks project's
`AlgebraicGeometry.exists_affineOpen_isFinite_restrict_iff_eq_genericPoint` rather than by the
source's direct denominator-clearing argument; the open produced is moreover affine.

The dimension of a subvariety `V` is `topologicalKrullDim V.support`, the Krull dimension of its
underlying closed set.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Appendix B.1.
* [Stacks Project, Tag 02NX](https://stacks.math.columbia.edu/tag/02NX)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

namespace MMP.Mori

/-- In a tower `k ⊆ A ⊆ B` of fields with `trdeg_k A` finite, if `B` and `A` have the same
transcendence degree over `k`, then `B` has transcendence degree zero over `A`. -/
theorem trdeg_eq_zero_of_toENat_trdeg_eq (k : Type*) {A B : Type v} [Field k] [Field A] [Field B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (hA : Algebra.trdeg k A < Cardinal.aleph0)
    (h : Cardinal.toENat (Algebra.trdeg k B) = Cardinal.toENat (Algebra.trdeg k A)) :
    Algebra.trdeg A B = 0 := by
  have hadd := congrArg Cardinal.toENat (trdeg_add_eq k A (A := B))
  rw [map_add, h] at hadd
  have hne : Cardinal.toENat (Algebra.trdeg k A) ≠ ⊤ :=
    (Cardinal.toENat_lt_top.mpr hA).ne
  have h0 : Cardinal.toENat (Algebra.trdeg A B) = 0 :=
    (WithTop.add_left_inj hne).mp (hadd.trans (add_zero _).symm)
  exact Cardinal.toENat_eq_zero.mp h0

end MMP.Mori

namespace MMP.Intersection.Scheme.Subvariety

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

/-- **Equal-dimensional images give finite extensions of function fields.** Let `f : X ⟶ Y` be
locally of finite type, with `Y` locally of finite type over a field `K`, `V` a subvariety of `X`
and `W = \overline{f(V)}`. If `dim V = dim W`, then `R(V)` is a finite field extension of
`f^* R(W)`: the induced embedding `f^* : R(W) → R(V)` is finite. -/
@[mmp "lem_mmp_foundation_equal_dimension_finite_field_extension"]
theorem finite_functionFieldMap_of_topologicalKrullDim_eq (q : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType q] (f : X ⟶ Y) [LocallyOfFiniteType f] (V : Subvariety X)
    (h : topologicalKrullDim V.support = topologicalKrullDim (V.image f).support) :
    (V.functionFieldMap f).hom.Finite := by
  set ξ := V.genericPoint
  let : Algebra K (X.residueField ξ) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (f ≫ q).appTop ≫ X.Γevaluation ξ).hom.toAlgebra
  let : Algebra K (Y.residueField (f ξ)) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop ≫ Y.Γevaluation (f ξ)).hom.toAlgebra
  let : Algebra (Y.residueField (f ξ)) (X.residueField ξ) := (f.residueFieldMap ξ).hom.toAlgebra
  have : IsScalarTower K (Y.residueField (f ξ)) (X.residueField ξ) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((Scheme.ΓSpecIso (.of K)).inv ≫ (f ≫ q).appTop ≫ X.Γevaluation ξ).hom =
      ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop ≫ Y.Γevaluation (f ξ) ≫
        f.residueFieldMap ξ).hom
    rw [Scheme.Γevaluation_naturality, Scheme.Hom.comp_appTop]
    simp only [Category.assoc]
  have hV : topologicalKrullDim V.support =
      (Cardinal.toENat (Algebra.trdeg K (X.residueField ξ)) : WithBot ℕ∞) := by
    rw [← topologicalKrullDim_closure_singleton_eq_trdeg K X (f ≫ q) ξ,
      V.isGenericPoint_genericPoint.def]
  have hgW : IsGenericPoint (f ξ) (V.image f).support := by
    have := (V.image f).isGenericPoint_genericPoint
    rwa [genericPoint_image] at this
  have hW : topologicalKrullDim (V.image f).support =
      (Cardinal.toENat (Algebra.trdeg K (Y.residueField (f ξ))) : WithBot ℕ∞) := by
    rw [← topologicalKrullDim_closure_singleton_eq_trdeg K Y q (f ξ), hgW.def]
  rw [hV, hW, WithBot.coe_inj] at h
  have : Algebra.EssFiniteType K (Y.residueField (f ξ)) := residueField_essFiniteType K q (f ξ)
  have hzero := MMP.Mori.trdeg_eq_zero_of_toENat_trdeg_eq K
    (trdeg_lt_aleph0 K (Y.residueField (f ξ))) h
  have : Algebra.EssFiniteType (Y.residueField (f ξ)) (X.residueField ξ) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap f ξ)
  have : Algebra.IsAlgebraic (Y.residueField (f ξ)) (X.residueField ξ) :=
    trdeg_eq_zero_iff.mp hzero
  have hfin : (f.residueFieldMap ξ).hom.Finite := Algebra.finite_of_essFiniteType_of_isAlgebraic
  rw [functionFieldMap, CommRingCat.hom_comp]
  exact hfin.comp (RingHom.Finite.of_surjective _
    (Y.residueFieldCongr (V.genericPoint_image f)).commRingCatIsoToRingEquiv.surjective)

end MMP.Intersection.Scheme.Subvariety

namespace MMP.Mori

section GenericallyFinite

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X)
  [IsIntegral X] [IsIntegral Y] [IsDominant f]

/-- Transporting a stalk map along an equality of its target point is precomposition with the
identification of the stalks at the two equal points. -/
private theorem cast_stalkMap_hom_eq {X' Y' : Scheme.{u}} (g : X' ⟶ Y') (x : X') {y : Y'}
    (hxy : g x = y) (hins : Inseparable y (g x)) :
    (hxy ▸ g.stalkMap x).hom = ((Y'.presheaf.stalkCongr hins).hom ≫ g.stalkMap x).hom := by
  cases hxy
  simp

/-- The Stacks project's extension of function fields of a dominant morphism of integral schemes,
`AlgebraicGeometry.dominantFunctionFieldMap`, is `AlgebraicGeometry.functionFieldMap`. -/
theorem dominantFunctionFieldMap_eq_functionFieldMap :
    dominantFunctionFieldMap f = functionFieldMap f :=
  cast_stalkMap_hom_eq f _ _ _

/-- **An equal-dimensional dominant morphism has a finite extension of function fields.** Let
`f : Y ⟶ X` be a dominant morphism of integral schemes locally of finite type over a field `k`
(with the structure `f ≫ s_X` on `Y`). If `dim Y = dim X`, then `k(Y)` is a finite extension of
`k(X)`. -/
@[mmp "lem_mmp_foundation_generically_finite_finite_on_dense_open"]
theorem finite_functionField_of_topologicalKrullDim_eq [LocallyOfFiniteType sX]
    [LocallyOfFiniteType f] (h : topologicalKrullDim Y = topologicalKrullDim X) :
    letI := functionFieldMapAlgebra f
    Module.Finite X.functionField Y.functionField := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have hX := toENat_trdeg_functionField (sX := sX)
  have hY := toENat_trdeg_functionField (sX := f ≫ sX)
  have : Algebra.EssFiniteType k X.functionField := essFiniteType_functionField (sX := sX)
  have : Algebra.EssFiniteType k Y.functionField := essFiniteType_functionField (sX := f ≫ sX)
  rw [← hX, ← hY, WithBot.coe_inj] at h
  have hzero := trdeg_eq_zero_of_toENat_trdeg_eq k (trdeg_lt_aleph0 k X.functionField) h
  have : Algebra.EssFiniteType X.functionField Y.functionField :=
    .of_comp k X.functionField Y.functionField
  have : Algebra.IsAlgebraic X.functionField Y.functionField := trdeg_eq_zero_iff.mp hzero
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

/-- **An equal-dimensional dominant morphism is finite over a dense open.** Let `f : Y ⟶ X` be a
dominant quasi-compact morphism of integral schemes locally of finite type over a field `k`. If
`dim Y = dim X`, then there is a dense (affine) open `U ⊆ X` such that `f⁻¹(U) → U` is finite. -/
@[mmp "lem_mmp_foundation_generically_finite_finite_on_dense_open"]
theorem exists_dense_isFinite_restrict_of_topologicalKrullDim_eq [LocallyOfFiniteType sX]
    [LocallyOfFiniteType f] [QuasiCompact f] (h : topologicalKrullDim Y = topologicalKrullDim X) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (f ∣_ U) := by
  have hfin := finite_functionField_of_topologicalKrullDim_eq sX f h
  let : Algebra X.functionField Y.functionField := (dominantFunctionFieldMap f).toAlgebra
  have h0 : Algebra.trdeg X.functionField Y.functionField = 0 := by
    have : Module.Finite X.functionField Y.functionField := by
      convert hfin using 3
      exact congrArg RingHom.toAlgebra (dominantFunctionFieldMap_eq_functionFieldMap f)
    exact trdeg_eq_zero_iff.mpr (Algebra.IsAlgebraic.of_finite _ _)
  obtain ⟨U, hne, hU⟩ := (exists_affineOpen_isFinite_restrict_iff_eq_genericPoint f
    (Or.inr inferInstance)).mpr (eq_genericPoint_of_trdeg_functionField_eq_zero f h0)
  exact ⟨U.1, U.1.isOpen.dense hne, hU⟩

end GenericallyFinite

end MMP.Mori
