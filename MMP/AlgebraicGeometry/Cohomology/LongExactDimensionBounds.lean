module

public import MMP.Attr
public import MMP.AlgebraicGeometry.ProjectiveBundle.VectorBundles
public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.IdealSheafSequence.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaMap.Consequence
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaInvertible.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatDegreeZeroFibres
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry

/-!
# Dimension bounds from the long exact cohomology sequence; the residual sequence

For a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of `𝒪_X`-modules on a scheme over a field `k`,
the long exact sequence of `Hⁿ(X, -)` bounds the dimension of each term by its two neighbours. For
a closed subscheme `i : D ⟶ X` with ideal sheaf `ℐ_D` and an invertible `𝒪_X`-module `L`, the
residual sequence `0 ⟶ L ⊗ ℐ_D ⟶ L ⟶ i_* i^* L ⟶ 0` is short exact. (For an effective Cartier
divisor `D` one has `ℐ_D ≅ 𝒪_X(-D)`, so the first term is `L(-D)`; that identification is not
proved here.)

## Main results

* `MMP.Resolution.Bridges.finrank_cohomologyOverField_two_le`:
  `hⁿ(ℱ₂) ≤ hⁿ(ℱ₁) + hⁿ(ℱ₃)`.
* `MMP.Resolution.Bridges.finrank_cohomologyOverField_one_succ_le`:
  `hⁿ⁺¹(ℱ₁) ≤ hⁿ(ℱ₃) + hⁿ⁺¹(ℱ₂)`.
* `MMP.Resolution.Bridges.finrank_cohomologyOverField_three_le`:
  `hⁿ(ℱ₃) ≤ hⁿ(ℱ₂) + hⁿ⁺¹(ℱ₁)`.
* `MMP.Resolution.Bridges.exists_residualSequence_shortExact`: the residual sequence is short
  exact.

## Implementation notes

* Cohomology is `AlgebraicGeometry.cohomologyOverField k f ℱ n`, a `k`-vector space through the
  structure morphism `f : X ⟶ Spec k`; the bounds assume finite dimensionality of the two
  neighbouring terms (automatic for coherent modules on a proper `X`,
  `AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper`) and conclude it for the
  bounded term, so `Module.finrank` is the actual dimension throughout.
* The residual sequence is `Stacks.IdealSheafSequence.divisorIdeal_shortExact` (Stacks 0C6K)
  tensored with the flat module `L`. Its second arrow is the unit `L ⟶ i_* i^* L` of
  `Scheme.Modules.pullbackPushforwardAdjunction`; the tensor product is
  `MMP.Intersection.Scheme.Modules.monoidalCategory`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace MMP.Resolution.Bridges

section Bounds

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  {S : ShortComplex X.Modules}

private lemma finiteDimensional_and_finrank_le_of_exact {A B C : Type*}
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    (u : A →ₗ[k] B) (v : B →ₗ[k] C) (h : Function.Exact u v)
    [FiniteDimensional k A] [FiniteDimensional k C] :
    FiniteDimensional k B ∧ Module.finrank k B ≤ Module.finrank k A + Module.finrank k C := by
  have hB : FiniteDimensional k B := Module.finiteDimensional_of_exact u v h
  refine ⟨hB, ?_⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker v
  have h2 : LinearMap.ker v = LinearMap.range u := LinearMap.exact_iff.1 h
  have h3 : Module.finrank k (LinearMap.range u) ≤ Module.finrank k A :=
    LinearMap.finrank_range_le u
  have h4 : Module.finrank k (LinearMap.range v) ≤ Module.finrank k C := Submodule.finrank_le _
  rw [h2] at h1
  omega

/-- **The middle term is bounded by the outer terms.** For a short exact sequence
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` with `Hⁿ(X, ℱ₁)` and `Hⁿ(X, ℱ₃)` finite-dimensional, `Hⁿ(X, ℱ₂)` is
finite-dimensional and `hⁿ(ℱ₂) ≤ hⁿ(ℱ₁) + hⁿ(ℱ₃)`. -/
theorem finrank_cohomologyOverField_two_le (hS : S.ShortExact) (n : ℕ)
    [FiniteDimensional k (cohomologyOverField k f S.X₁ n)]
    [FiniteDimensional k (cohomologyOverField k f S.X₃ n)] :
    FiniteDimensional k (cohomologyOverField k f S.X₂ n) ∧
      Module.finrank k (cohomologyOverField k f S.X₂ n) ≤
        Module.finrank k (cohomologyOverField k f S.X₁ n) +
          Module.finrank k (cohomologyOverField k f S.X₃ n) := by
  obtain ⟨-, -, hfg, -, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
  exact finiteDimensional_and_finrank_le_of_exact k (cohomologyOverFieldMap k f S.f n).hom
    (cohomologyOverFieldMap k f S.g n).hom (hfg n)

/-- **The left term in degree `n + 1` is bounded by its neighbours.** For a short exact sequence
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` with `Hⁿ(X, ℱ₃)` and `Hⁿ⁺¹(X, ℱ₂)` finite-dimensional, `Hⁿ⁺¹(X, ℱ₁)`
is finite-dimensional and `hⁿ⁺¹(ℱ₁) ≤ hⁿ(ℱ₃) + hⁿ⁺¹(ℱ₂)`. -/
theorem finrank_cohomologyOverField_one_succ_le (hS : S.ShortExact) (n : ℕ)
    [FiniteDimensional k (cohomologyOverField k f S.X₃ n)]
    [FiniteDimensional k (cohomologyOverField k f S.X₂ (n + 1))] :
    FiniteDimensional k (cohomologyOverField k f S.X₁ (n + 1)) ∧
      Module.finrank k (cohomologyOverField k f S.X₁ (n + 1)) ≤
        Module.finrank k (cohomologyOverField k f S.X₃ n) +
          Module.finrank k (cohomologyOverField k f S.X₂ (n + 1)) := by
  obtain ⟨d, -, -, -, hdf⟩ := exists_cohomologyOverField_longExactSequence k f hS
  exact finiteDimensional_and_finrank_le_of_exact k (d n).hom
    (cohomologyOverFieldMap k f S.f (n + 1)).hom (hdf n)

/-- **The right term is bounded by its neighbours.** For a short exact sequence
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` with `Hⁿ(X, ℱ₂)` and `Hⁿ⁺¹(X, ℱ₁)` finite-dimensional, `Hⁿ(X, ℱ₃)` is
finite-dimensional and `hⁿ(ℱ₃) ≤ hⁿ(ℱ₂) + hⁿ⁺¹(ℱ₁)`. -/
theorem finrank_cohomologyOverField_three_le (hS : S.ShortExact) (n : ℕ)
    [FiniteDimensional k (cohomologyOverField k f S.X₂ n)]
    [FiniteDimensional k (cohomologyOverField k f S.X₁ (n + 1))] :
    FiniteDimensional k (cohomologyOverField k f S.X₃ n) ∧
      Module.finrank k (cohomologyOverField k f S.X₃ n) ≤
        Module.finrank k (cohomologyOverField k f S.X₂ n) +
          Module.finrank k (cohomologyOverField k f S.X₁ (n + 1)) := by
  obtain ⟨d, -, -, hgd, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
  exact finiteDimensional_and_finrank_le_of_exact k (cohomologyOverFieldMap k f S.g n).hom
    (d n).hom (hgd n)

end Bounds

section Residual

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- The ideal sheaf `ℐ_D ⊆ 𝒪_X` of a closed subscheme, as an `𝒪_X`-module. -/
noncomputable abbrev idealSheafModule : X.Modules :=
  Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom

private theorem exists_shortExact_of_iso {C : Type*} [Category C] [Abelian C]
    (S₁ : ShortComplex C) (hS : S₁.ShortExact)
    {A B C' : C} (e₁ : A ≅ S₁.X₁) (φ₂ : S₁.X₂ ≅ B) (φ₃ : S₁.X₃ ≅ C') (η : B ⟶ C')
    (key : S₁.g ≫ φ₃.hom = φ₂.hom ≫ η) :
    ∃ (ι : A ⟶ B) (hz : ι ≫ η = 0), (ShortComplex.mk ι η hz).ShortExact := by
  have hz : (e₁.hom ≫ S₁.f ≫ φ₂.hom) ≫ η = 0 := by
    rw [Category.assoc, Category.assoc, ← key, ← Category.assoc S₁.f, S₁.zero]
    simp
  refine ⟨_, hz, ?_⟩
  refine ShortComplex.shortExact_of_iso ?_ hS
  exact ShortComplex.isoMk e₁.symm φ₂ φ₃ (by simp) key.symm

open Stacks.ProjectionFormula Stacks.RingedSpace RingedSpaceModuleAdjunction in
/-- **The residual sequence.** For a closed subscheme `i : D ⟶ X` with ideal sheaf `ℐ_D` and an
invertible `𝒪_X`-module `L`, there is an arrow `L ⊗ ℐ_D ⟶ L` making
`0 ⟶ L ⊗ ℐ_D ⟶ L ⟶ i_* i^* L ⟶ 0` short exact, the second arrow being the adjunction unit.
(When `D` is an effective Cartier divisor, `ℐ_D ≅ 𝒪_X(-D)` and the first term is `L(-D)`; that
identification is not proved here.) -/
theorem exists_residualSequence_shortExact (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ (ι : L ⊗ idealSheafModule D ⟶ L)
      (hz : ι ≫ (Scheme.Modules.pullbackPushforwardAdjunction D.subschemeι).unit.app L = 0),
      (ShortComplex.mk ι
        ((Scheme.Modules.pullbackPushforwardAdjunction D.subschemeι).unit.app L)
        hz).ShortExact := by
  obtain ⟨_, hS0⟩ := Stacks.IdealSheafSequence.divisorIdeal_shortExact D
  have hinv : Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      (structureRingSheaf X.toRingedSpace).property L := ‹_›
  let F : SheafOfModules (structureSheafRing X.toRingedSpace) ⥤
      SheafOfModules (structureSheafRing X.toRingedSpace) :=
    (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).flip.obj L
  have : F.IsEquivalence :=
    (Stacks.SheafOfModules.Invertible.isInvertible_iff_tensorRightFunctor_isEquivalence
      X.presheaf X.ringCatSheaf.2 L).1 ‹_›
  have : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full F
  have hS1 := hS0.map_of_exact F
  let f := D.subschemeι.toLRSHom.toShHom
  have hiso := isIso_projectionFormulaMap f
    (SheafOfModules.unit (structureRingSheaf D.subscheme.toRingedSpace)) L
  have hcomp := tensorUnitToPushforward_comp_projectionFormulaMap' (f := f) L
  have hsc := isIso_structureComparison f L
  let e₁ : L ⊗ idealSheafModule D ≅
      F.obj (Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom) :=
    ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding ⟨X.presheaf, X.IsSheaf⟩).app L).app _
  let ψi : ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨D.subscheme.toRingedSpace.presheaf, D.subscheme.toRingedSpace.IsSheaf⟩))).obj
        (SheafOfModules.unit (structureRingSheaf D.subscheme.toRingedSpace),
          (pullbackFunctor f).obj L) ≅ (pullbackFunctor f).obj L :=
    (@asIso _ _ _ _ _ hsc).symm ≪≫ (pullbackFunctor f).mapIso (unitTensorIso X.toRingedSpace L)
  let φ₃ := (@asIso _ _ _ _ _ hiso) ≪≫ (pushforwardFunctor f).mapIso ψi
  have key : F.map (Stacks.IdealSheafSequence.divisorQuotientMap D) ≫ φ₃.hom =
      (unitTensorIso X.toRingedSpace L).hom ≫ (pullbackAdjunction f).unit.app L := by
    have h1 : F.map (Stacks.IdealSheafSequence.divisorQuotientMap D) ≫ projectionFormulaMap' f
        (SheafOfModules.unit (structureRingSheaf D.subscheme.toRingedSpace)) L =
        (pullbackAdjunction f).unit.app
          (((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩))).obj
            (SheafOfModules.unit (structureRingSheaf X.toRingedSpace), L)) ≫
        (pushforwardFunctor f).map (structureComparison f L) := by
      rw [← hcomp]
      simp only [F, unitHom_eq, Functor.uncurry_obj_map, Prod.mkHom]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
      rfl
    have h2 := (pullbackAdjunction f).unit.naturality (unitTensorIso X.toRingedSpace L).hom
    have hφ : φ₃.hom = projectionFormulaMap' f
        (SheafOfModules.unit (structureRingSheaf D.subscheme.toRingedSpace)) L ≫
        (pushforwardFunctor f).map ((@asIso _ _ _ _ _ hsc).inv ≫
          (pullbackFunctor f).map (unitTensorIso X.toRingedSpace L).hom) := rfl
    rw [hφ]
    erw [← Category.assoc, h1, Category.assoc, ← CategoryTheory.Functor.map_comp]
    erw [asIso_inv, IsIso.hom_inv_id_assoc]
    exact h2.symm
  exact exists_shortExact_of_iso _ hS1 e₁ (unitTensorIso X.toRingedSpace L) φ₃ _ key

end Residual

end MMP.Resolution.Bridges
