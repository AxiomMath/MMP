module

public import MMP.AlgebraicGeometry.SpreadingOut.LocalEquations

/-!
# The function field of a non-empty open subscheme

Let `Y` be an integral scheme and `U ⊆ Y` a non-empty open. The extension of function fields of
the open immersion `U ⟶ Y` is an isomorphism `k(Y) ≅ k(U)`; its inverse
`MMP.FourfoldProofs.FractionalLogComplexProof.openFunctionFieldEquiv U` sends the germ of the
restriction of a section of `Y` to its germ in `k(Y)`. Over a field `k` it is an isomorphism of
`k`-algebras. Rational forms on `U` are moved to `k(Y)` along it.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.openFunctionFieldEquiv`: the isomorphism
  `k(U) ≅ k(Y)`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.openFormsMap`: rational forms of `U` moved to `k(Y)`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.openFunctionFieldEquiv_germ`: germs of restrictions.
* `MMP.FourfoldProofs.FractionalLogComplexProof.openFunctionFieldEquiv_algebraMap`: `k`-linearity.
* `MMP.FourfoldProofs.FractionalLogComplexProof.openFormsMap_ιMulti_D`: wedges of exact forms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

universe u

/-- The inclusion of a non-empty open of an irreducible scheme is dominant. -/
instance isDominant_opens_ι {Y : Scheme.{u}} [IrreducibleSpace Y] (U : Y.Opens) [Nonempty U] :
    IsDominant U.ι :=
  Opens.isDominant_ι (U.isOpen.dense (by
    obtain ⟨⟨y, hy⟩⟩ := ‹Nonempty U›
    exact ⟨y, hy⟩))

variable {Y : Scheme.{u}} [IsIntegral Y] (U : Y.Opens) [Nonempty U]

/-- The isomorphism `k(U) ≅ k(Y)` of the function field of a non-empty open with that of `Y`. -/
noncomputable def openFunctionFieldEquiv : U.toScheme.functionField ≃+* Y.functionField :=
  (RingEquiv.ofBijective (AlgebraicGeometry.functionFieldMap U.ι)
    (MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤
      (by simp))).symm

/-- The extension `k(Y) → k(U)` of function fields of `U ⟶ Y` inverts `openFunctionFieldEquiv`. -/
theorem functionFieldMap_openFunctionFieldEquiv (a : U.toScheme.functionField) :
    AlgebraicGeometry.functionFieldMap U.ι (openFunctionFieldEquiv U a) = a := by
  unfold openFunctionFieldEquiv
  exact (RingEquiv.ofBijective (AlgebraicGeometry.functionFieldMap U.ι) _).apply_symm_apply a

/-- **Germs of restrictions.** `k(U) ≅ k(Y)` sends the germ of the restriction to `U` of a
section of `Y` over `W` to its germ. -/
theorem openFunctionFieldEquiv_germ (W : Y.Opens) [Nonempty W]
    [Nonempty (U.ι ⁻¹ᵁ W)] (a : Γ(Y, W)) :
    openFunctionFieldEquiv U (U.toScheme.germToFunctionField (U.ι ⁻¹ᵁ W) (U.ι.app W a)) =
      Y.germToFunctionField W a := by
  unfold openFunctionFieldEquiv
  refine (RingEquiv.symm_apply_eq _).2 ?_
  change _ = AlgebraicGeometry.functionFieldMap U.ι (Y.germToFunctionField W a)
  rw [MMP.Spreading.functionFieldMap_germToFunctionField U.ι W (U.ι ⁻¹ᵁ W) le_rfl a,
    Scheme.Hom.app_eq_appLE]

/-- **`k(U) ≅ k(Y)` is `k`-linear.** -/
theorem openFunctionFieldEquiv_algebraMap {k : Type u} [Field k] (sY : Y ⟶ Spec (.of k))
    (c : k) :
    letI := MMP.Mori.functionFieldAlgebra sY
    letI := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
    openFunctionFieldEquiv U (algebraMap k U.toScheme.functionField c) =
      algebraMap k Y.functionField c := by
  let := MMP.Mori.functionFieldAlgebra sY
  let := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
  let := MMP.Mori.functionFieldMapAlgebra U.ι
  have := MMP.Mori.isScalarTower_functionFieldMap sY U.ι
  unfold openFunctionFieldEquiv
  refine (RingEquiv.symm_apply_eq _).2 ?_
  exact (IsScalarTower.algebraMap_apply k Y.functionField U.toScheme.functionField c)

section Forms

variable {k : Type u} [Field k] (sY : Y ⟶ Spec (.of k))

/-- `k(U) ≅ k(Y)` as an algebra structure of `k(Y)` over `k(U)`. -/
@[instance_reducible]
noncomputable def openFunctionFieldAlgebra : Algebra U.toScheme.functionField Y.functionField :=
  (openFunctionFieldEquiv U).toRingHom.toAlgebra

/-- The `k`-algebras `k(U)` and `k(Y)` form a scalar tower `k → k(U) → k(Y)`. -/
theorem isScalarTower_openFunctionField :
    letI := MMP.Mori.functionFieldAlgebra sY
    letI := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
    letI := openFunctionFieldAlgebra U
    IsScalarTower k U.toScheme.functionField Y.functionField := by
  let := MMP.Mori.functionFieldAlgebra sY
  let := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
  let := openFunctionFieldAlgebra U
  exact IsScalarTower.of_algebraMap_eq fun c => (openFunctionFieldEquiv_algebraMap U sY c).symm

/-- **Rational forms of `U` moved to `k(Y)`.** -/
noncomputable def openFormsMap (q : ℕ) :
    letI := MMP.Mori.functionFieldAlgebra sY
    letI := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
    letI := openFunctionFieldAlgebra U
    ⋀[U.toScheme.functionField]^q Ω[U.toScheme.functionField⁄k] →ₗ[U.toScheme.functionField]
      ⋀[Y.functionField]^q Ω[Y.functionField⁄k] :=
  letI := MMP.Mori.functionFieldAlgebra sY
  letI := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
  letI := openFunctionFieldAlgebra U
  haveI := isScalarTower_openFunctionField U sY
  KaehlerDifferential.mapExteriorPower k U.toScheme.functionField Y.functionField q

/-- `openFormsMap` on a wedge of exact forms. -/
theorem openFormsMap_ιMulti_D (q : ℕ) (x : Fin q → U.toScheme.functionField) :
    letI := MMP.Mori.functionFieldAlgebra sY
    letI := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
    openFormsMap U sY q
        (exteriorPower.ιMulti U.toScheme.functionField q
          fun j => KaehlerDifferential.D k U.toScheme.functionField (x j)) =
      exteriorPower.ιMulti Y.functionField q
        fun j => KaehlerDifferential.D k Y.functionField (openFunctionFieldEquiv U (x j)) := by
  let := MMP.Mori.functionFieldAlgebra sY
  let := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
  let := openFunctionFieldAlgebra U
  have := isScalarTower_openFunctionField U sY
  refine (KaehlerDifferential.mapExteriorPower_ιMulti k U.toScheme.functionField Y.functionField
    q _).trans ?_
  congr 1
  funext j
  exact KaehlerDifferential.map_D k k U.toScheme.functionField Y.functionField (x j)

/-- `openFormsMap` is semilinear along `k(U) ≅ k(Y)`. -/
theorem openFormsMap_smul (q : ℕ) (a : U.toScheme.functionField)
    (ω : letI := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
      ⋀[U.toScheme.functionField]^q Ω[U.toScheme.functionField⁄k]) :
    letI := MMP.Mori.functionFieldAlgebra sY
    letI := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
    openFormsMap U sY q (a • ω) = openFunctionFieldEquiv U a • openFormsMap U sY q ω := by
  let := MMP.Mori.functionFieldAlgebra sY
  let := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
  let := openFunctionFieldAlgebra U
  rw [LinearMap.map_smul]
  exact algebra_compatible_smul Y.functionField a _

end Forms

end MMP.FourfoldProofs.FractionalLogComplexProof
