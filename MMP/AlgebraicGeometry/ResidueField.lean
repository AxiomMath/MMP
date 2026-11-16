module

public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Sections pulled back to the spectrum of a residue field

For a point `x` of a scheme `X`, the canonical morphism `Spec κ(x) ⟶ X` acts on sections over an
open `U ∋ x`, after identifying the global sections of `Spec κ(x)` with `κ(x)`, as evaluation at
`x`.

## Main results

* `MMP.Scheme.appLE_fromSpecResidueField_ΓSpecIso`: the statement above.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace MMP.Scheme

variable (X : AlgebraicGeometry.Scheme.{u})

/-- On sections, the canonical morphism `Spec κ(x) ⟶ X`, followed by the identification of the
global sections of `Spec κ(x)` with `κ(x)`, is evaluation at `x`. -/
theorem appLE_fromSpecResidueField_ΓSpecIso {x : X} (f : Spec (X.residueField x) ⟶ X)
    (hf : f = Spec.map (X.residue x) ≫ X.fromSpecStalk x) (U : X.Opens) (hx : x ∈ U)
    (e : ⊤ ≤ f ⁻¹ᵁ U) :
    f.appLE U ⊤ e ≫ (AlgebraicGeometry.Scheme.ΓSpecIso _).hom = X.evaluation U x hx := by
  subst hf
  have e' : ⊤ ≤ Spec.map (X.residue x) ⁻¹ᵁ X.fromSpecStalk x ⁻¹ᵁ U := by
    intro y _
    change (X.fromSpecResidueField x) y ∈ U
    rw [AlgebraicGeometry.Scheme.fromSpecResidueField_apply]
    exact hx
  have key : (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE le_top).op ≫
      (Spec.map (X.residue x)).appLE (X.fromSpecStalk x ⁻¹ᵁ U) ⊤ e' =
      (Spec.map (X.residue x)).appTop :=
    AlgebraicGeometry.Scheme.Hom.map_appLE _ _ _
  rw [AlgebraicGeometry.Scheme.Hom.comp_appLE, AlgebraicGeometry.Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc]
  rw [reassoc_of% key, AlgebraicGeometry.Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc,
    AlgebraicGeometry.Scheme.germ_residue]

end MMP.Scheme
