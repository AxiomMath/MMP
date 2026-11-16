module

public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Stalks of normal schemes of dimension at most one

* `MMP.fromSpecStalk_comp_eq`: a morphism `Spec 𝒪_{X,x} ⟶ X ⟶ Spec R` is `Spec` of the ring
  map `R ≅ Γ(Spec R) → Γ(X) → 𝒪_{X,x}`.
* `MMP.coheight_le_one`: in a scheme of Krull dimension at most one every point has coheight at
  most one.
* `MMP.valuationRing_stalk`: the local ring of a normal locally Noetherian integral scheme at a
  point of coheight at most one is a valuation ring (a field or a discrete valuation ring).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP

/-- A morphism `Spec 𝒪_{X,x} ⟶ X ⟶ Spec R` is `Spec` of the ring map
`R ≅ Γ(Spec R) → Γ(X) → 𝒪_{X,x}`. -/
theorem fromSpecStalk_comp_eq (X : Scheme.{u}) (x : X) {R : CommRingCat.{u}} (g : X ⟶ Spec R) :
    X.fromSpecStalk x ≫ g =
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ X.presheaf.germ ⊤ x trivial) := by
  rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ_assoc]
  simp only [Category.assoc]
  rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- In a scheme of dimension at most one every point has coheight at most one. -/
theorem coheight_le_one {X : Scheme.{u}} (h : Order.krullDim X ≤ 1) (x : X) :
    Order.coheight x ≤ 1 := by
  exact_mod_cast (Order.coheight_le_krullDim x).trans h

/-- A local ring of a normal locally Noetherian integral scheme at a point of coheight at most
one is a valuation ring (a field or a discrete valuation ring). -/
theorem valuationRing_stalk {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {x : X} (hx : Order.coheight x ≤ 1) : ValuationRing (X.presheaf.stalk x) := by
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx
  haveI : IsIntegrallyClosed (X.presheaf.stalk x) := IsNormal.stalk_normal x
  by_cases hF : IsField (X.presheaf.stalk x)
  · letI := hF.toField
    infer_instance
  · have : IsDedekindDomain (X.presheaf.stalk x) :=
      { maximalOfPrime := fun hp h𝔭 => h𝔭.isMaximal_of_ne_bot hp }
    have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
      ((IsDiscreteValuationRing.TFAE _ hF).out 1 3).mpr ‹_›
    infer_instance

end MMP
