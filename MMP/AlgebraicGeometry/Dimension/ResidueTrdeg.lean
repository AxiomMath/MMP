module

public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality

/-!
# Dimension of the closure of a point and residue transcendence degree

For a scheme `T` locally of finite type over a field `L` and a point `t`, the closure of `t` has
dimension `trdeg_L κ(t)`, written with Stacks' `Stacks.Chow.residueTrdeg` of the structure morphism
(`MMP.topologicalKrullDim_closure_singleton_eq_toENat_residueTrdeg`). Stacks states it with the
`L`-algebra structure on `κ(t)` coming from global sections
(`AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_trdeg`); `MMP.trdegΓFieldExtension`
names that transcendence degree and compares the two.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace MMP

/-- The transcendence degree of `κ(t)` over `L`, for the `L`-algebra structure given by global
sections of a morphism `q : T ⟶ Spec L`. -/
def trdegΓFieldExtension (L : Type u) [Field L] {T : Scheme.{u}}
    (q : T ⟶ Spec (.of L)) (t : T) : Cardinal.{u} :=
  letI : Algebra L (T.residueField t) :=
    ((Scheme.ΓSpecIso (.of L)).inv ≫ q.appTop ≫ T.Γevaluation t).hom.toAlgebra
  Algebra.trdeg L (T.residueField t)

/-- Along a morphism `f : X ⟶ Y` over `Spec L`, `trdegΓFieldExtension` is additive:
`trdeg_L κ(x) = trdeg_L κ(f x) + trdeg_{κ(f x)} κ(x)`. -/
theorem trdegΓFieldExtension_comp (L : Type u) [Field L] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (q : Y ⟶ Spec (.of L)) (x : X) :
    trdegΓFieldExtension L (f ≫ q) x =
      trdegΓFieldExtension L q (f x) + Stacks.Chow.residueTrdeg f x := by
  let : Algebra L (Y.residueField (f x)) :=
    ((Scheme.ΓSpecIso (.of L)).inv ≫ q.appTop ≫ Y.Γevaluation (f x)).hom.toAlgebra
  let : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  let : Algebra L (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of L)).inv ≫ (f ≫ q).appTop ≫ X.Γevaluation x).hom.toAlgebra
  have e : (Scheme.ΓSpecIso (.of L)).inv ≫ (f ≫ q).appTop ≫ X.Γevaluation x =
      ((Scheme.ΓSpecIso (.of L)).inv ≫ q.appTop ≫ Y.Γevaluation (f x)) ≫ f.residueFieldMap x := by
    rw [Scheme.Hom.comp_appTop]
    simp only [Category.assoc, Scheme.Γevaluation_naturality]
  have : IsScalarTower L (Y.residueField (f x)) (X.residueField x) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ congrArg (fun φ ↦ φ.hom a) e
  have : FaithfulSMul L (Y.residueField (f x)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  have : FaithfulSMul (Y.residueField (f x)) (X.residueField x) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  exact (trdeg_add_eq L (Y.residueField (f x)) (A := X.residueField x)).symm

/-- `trdegΓFieldExtension` of the identity of `Spec L` vanishes: the residue field of a point of
`Spec L` has transcendence degree `0` over `L`. -/
theorem trdegΓFieldExtension_id (L : Type u) [Field L] (t : Spec (.of L)) :
    trdegΓFieldExtension L (𝟙 _) t = 0 := by
  have h := topologicalKrullDim_closure_singleton_eq_trdeg L (Spec (.of L)) (𝟙 _) t
  have hle : topologicalKrullDim (closure ({t} : Set (Spec (.of L)))) ≤ 0 := by
    refine (topologicalKrullDim_subspace_le _ _).trans ?_
    have : topologicalKrullDim (PrimeSpectrum L) = 0 := by
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
    exact this.le
  rw [h] at hle
  have : Cardinal.toENat (trdegΓFieldExtension L (𝟙 _) t) = 0 := by
    have h0 : ((Cardinal.toENat (trdegΓFieldExtension L (𝟙 _) t) : ℕ∞) : WithBot ℕ∞) ≤
        ((0 : ℕ∞) : WithBot ℕ∞) := hle
    exact nonpos_iff_eq_zero.mp (WithBot.coe_le_coe.mp h0)
  exact Cardinal.toENat_eq_zero.mp this

/-- `trdegΓFieldExtension` agrees with Stacks' residue transcendence degree of the structure
morphism. -/
theorem trdegΓFieldExtension_eq_residueTrdeg (L : Type u) [Field L] {T : Scheme.{u}}
    (q : T ⟶ Spec (.of L)) (t : T) :
    trdegΓFieldExtension L q t = Stacks.Chow.residueTrdeg q t := by
  have h := trdegΓFieldExtension_comp L q (𝟙 _) t
  rwa [Category.comp_id, trdegΓFieldExtension_id, zero_add] at h

/-- The dimension of the closure of a point `t` of a scheme locally of finite type over a field
is the residue transcendence degree of `t` over that field. -/
theorem topologicalKrullDim_closure_singleton_eq_toENat_residueTrdeg {L : Type u} [Field L]
    {T : Scheme.{u}} (q : T ⟶ Spec (.of L)) [LocallyOfFiniteType q] (t : T) :
    topologicalKrullDim (closure ({t} : Set T)) =
      (Cardinal.toENat (Stacks.Chow.residueTrdeg q t) : WithBot ℕ∞) := by
  rw [← trdegΓFieldExtension_eq_residueTrdeg]
  exact topologicalKrullDim_closure_singleton_eq_trdeg L T q t

end MMP
