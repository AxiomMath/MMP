module

public import MMP.RingTheory.LocalRing.ResidueField.IntegralSeparable
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness

/-!
# The local homomorphism at a point of a finite cover

For a morphism `f : Y ⟶ X` and a point `y` with `f y = x`, the local homomorphism
`𝒪_{X,x} → 𝒪_{Y,y}` is the stalk map of `f` at `y`, precomposed with the identification of the
stalks at `x` and `f y`. It sends germs of sections to germs of their pull-backs, is compatible
with the maps to the function fields and with the structures over a base field `k`, and, when `f`
is finite, its residue field extension is algebraic, hence separable in characteristic zero.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.placeHom`: the local homomorphism.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.placeHom_rfl`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.placeHom_germ`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.algebraMap_placeHom`: compatibilities.
* `MMP.FourfoldProofs.FractionalLogComplexProof.isSeparable_residueField_placeHom`: the separable
  residue field extension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The local homomorphism `𝒪_{X,x} → 𝒪_{Y,y}` of `f` at a point `y` with `f y = x`. -/
noncomputable def placeHom {y : Y} {x : X} (h : f y = x) :
    X.presheaf.stalk x ⟶ Y.presheaf.stalk y :=
  X.presheaf.stalkSpecializes (Inseparable.of_eq h).specializes ≫ f.stalkMap y

/-- At `x = f y` (with the trivial equality), `placeHom` is the stalk map of `f` at `y`. -/
@[simp]
theorem placeHom_rfl (y : Y) : placeHom f (rfl : f y = f y) = f.stalkMap y := by
  simp [placeHom]

/-- `placeHom` sends the germ of a section to the germ of its pull-back. -/
theorem placeHom_germ {y : Y} {x : X} (h : f y = x) {W : X.Opens} (hx : x ∈ W) (a : Γ(X, W)) :
    (placeHom f h).hom (X.presheaf.germ W x hx a) =
      Y.presheaf.germ (f ⁻¹ᵁ W) y (show f y ∈ W from h ▸ hx) (f.app W a) := by
  change (X.presheaf.germ W x hx ≫ X.presheaf.stalkSpecializes _ ≫ f.stalkMap y).hom a = _
  rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes, Scheme.Hom.germ_stalkMap]
  rfl

/-- `placeHom` is a local homomorphism of local rings. -/
instance isLocalHom_placeHom {y : Y} {x : X} (h : f y = x) : IsLocalHom (placeHom f h).hom := by
  have : IsIso (X.presheaf.stalkSpecializes (Inseparable.of_eq h).specializes) := by
    subst h
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    infer_instance
  change IsLocalHom ((f.stalkMap y).hom.comp
    (X.presheaf.stalkSpecializes (Inseparable.of_eq h).specializes).hom)
  have : IsLocalHom (X.presheaf.stalkSpecializes (Inseparable.of_eq h).specializes).hom :=
    isLocalHom_of_isIso _
  infer_instance

/-- `placeHom` is compatible with the extension of function fields. -/
theorem algebraMap_placeHom [IsIntegral X] [IsIntegral Y] [IsDominant f] {y : Y} {x : X}
    (h : f y = x) (a : X.presheaf.stalk x) :
    algebraMap (Y.presheaf.stalk y) Y.functionField ((placeHom f h).hom a) =
      functionFieldMap f (algebraMap (X.presheaf.stalk x) X.functionField a) := by
  change algebraMap (Y.presheaf.stalk y) Y.functionField ((f.stalkMap y).hom
    ((X.presheaf.stalkSpecializes (Inseparable.of_eq h).specializes).hom a)) = _
  rw [← MMP.Mori.functionFieldMap_algebraMap_stalk, MMP.Mori.algebraMap_stalkSpecializes]

/-- `placeHom` is a homomorphism of `k`-algebras. -/
theorem isScalarTower_placeHom {k : Type u} [Field k] (sX : X ⟶ Spec (.of k)) {y : Y} {x : X}
    (h : f y = x) :
    letI := MMP.Mori.stalkAlgebra sX x
    letI := MMP.Mori.stalkAlgebra (f ≫ sX) y
    letI := (placeHom f h).hom.toAlgebra
    IsScalarTower k (X.presheaf.stalk x) (Y.presheaf.stalk y) := by
  let := MMP.Mori.stalkAlgebra sX x
  let := MMP.Mori.stalkAlgebra (f ≫ sX) y
  let := (placeHom f h).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  have e : (Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ sX).appTop ≫
        Y.presheaf.germ ⊤ y (TopologicalSpace.Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top _)) ≫
        placeHom f h := by
    simp only [placeHom, Scheme.Hom.comp_appTop, Category.assoc,
      TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
    rfl
  exact congrArg CommRingCat.Hom.hom e

/-- **The residue field extension at a point of a finite cover is separable** in characteristic
zero. -/
theorem isSeparable_residueField_placeHom {k : Type u} [Field k] [CharZero k]
    (sX : X ⟶ Spec (.of k)) [IsFinite f] {y : Y} {x : X} (h : f y = x) :
    letI := (placeHom f h).hom.toAlgebra
    haveI : IsLocalHom (algebraMap (X.presheaf.stalk x) (Y.presheaf.stalk y)) :=
      isLocalHom_placeHom f h
    Algebra.IsSeparable (ResidueField (X.presheaf.stalk x))
      (ResidueField (Y.presheaf.stalk y)) := by
  let := (placeHom f h).hom.toAlgebra
  have : IsLocalHom (algebraMap (X.presheaf.stalk x) (Y.presheaf.stalk y)) :=
    isLocalHom_placeHom f h
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hyV : y ∈ f ⁻¹ᵁ W := show f y ∈ W from h ▸ hxW
  have hV : IsAffineOpen (f ⁻¹ᵁ W) := hW.preimage f
  let : Algebra Γ(X, W) Γ(Y, f ⁻¹ᵁ W) := (f.app W).hom.toAlgebra
  have : Module.Finite Γ(X, W) Γ(Y, f ⁻¹ᵁ W) := f.finite_app W hW
  let : Algebra Γ(X, W) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxW⟩
  let : Algebra Γ(Y, f ⁻¹ᵁ W) (Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hyV⟩
  have : IsLocalization.AtPrime (Y.presheaf.stalk y) (hV.primeIdealOf ⟨y, hyV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨y, hyV⟩
  let := MMP.Mori.stalkAlgebra sX x
  let : Algebra k (ResidueField (X.presheaf.stalk x)) :=
    ((residue _).comp (algebraMap k (X.presheaf.stalk x))).toAlgebra
  have : CharZero (ResidueField (X.presheaf.stalk x)) :=
    charZero_of_injective_algebraMap (algebraMap k (ResidueField (X.presheaf.stalk x))).injective
  exact isSeparable_residueField_of_isLocalization (A₀ := Γ(X, W)) (B₀ := Γ(Y, f ⁻¹ᵁ W))
    (hV.primeIdealOf ⟨y, hyV⟩).asIdeal fun a => placeHom_germ f h hxW a

end MMP.FourfoldProofs.FractionalLogComplexProof
