module

public import MMP.AlgebraicGeometry.FunctionField.OpenSubscheme
public import MMP.AlgebraicGeometry.DeRham.RationalForms.Basic

/-!
# Rational forms of a non-empty open

For an isomorphism `A ≅ B` of `k`-algebras the pull-back of forms
`⋀^q Ω_{A/k} → ⋀^q Ω_{B/k}` is bijective: the pull-back along the inverse is an inverse, since the
pull-back along the identity is the identity. In particular, for a non-empty open `U` of an
integral scheme `Y` over `k`, moving rational forms from `k(U)` to `k(Y)`
(`MMP.FourfoldProofs.FractionalLogComplexProof.openFormsMap`) is bijective, so a rational form of `Y` is
the rational form of a unique rational form of `U`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.mapExteriorPower_bijective`: pull-backs along
  isomorphisms.
* `MMP.FourfoldProofs.FractionalLogComplexProof.openFormsMap_bijective`: rational forms of a non-empty
  open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

section Self

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- The pull-back of differentials along the identity is the identity. -/
@[simp]
theorem map_self_apply (ω : Ω[A⁄k]) : KaehlerDifferential.map k k A A ω = ω := by
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [KaehlerDifferential.map_D]
    rfl
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [LinearMap.map_smul, hx]

/-- The pull-back of forms along the identity is the identity. -/
@[simp]
theorem mapExteriorPower_self_apply (q : ℕ) (ω : ⋀[A]^q (Ω[A⁄k])) :
    KaehlerDifferential.mapExteriorPower k A A q ω = ω := by
  have hω : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A q (M := Ω[A⁄k]))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [KaehlerDifferential.mapExteriorPower_ιMulti]
    congr 1
    funext i
    exact map_self_apply k A (v i)
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [LinearMap.map_smul, hx]

end Self

/-- **Pull-backs of forms along isomorphisms are bijective.** If `algebraMap A B` is bijective,
then the pull-back of `q`-forms `⋀^q Ω[A⁄k] → ⋀^q Ω[B⁄k]` is bijective. -/
theorem mapExteriorPower_bijective (k A B : Type u) [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (h : Function.Bijective (algebraMap A B)) (q : ℕ) :
    Function.Bijective (KaehlerDifferential.mapExteriorPower k A B q) := by
  let e := RingEquiv.ofBijective (algebraMap A B) h
  let : Algebra B A := e.symm.toRingHom.toAlgebra
  have he : ∀ a, e a = algebraMap A B a := fun _ => rfl
  have : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k A c = e.symm (algebraMap k B c)
    rw [RingEquiv.eq_symm_apply, he, ← IsScalarTower.algebraMap_apply]
  have : IsScalarTower A B A := IsScalarTower.of_algebraMap_eq fun a => by
    change a = e.symm (algebraMap A B a)
    rw [RingEquiv.eq_symm_apply, he]
  have : IsScalarTower B A B := IsScalarTower.of_algebraMap_eq fun b => by
    change b = algebraMap A B (e.symm b)
    rw [← he, RingEquiv.apply_symm_apply]
  refine ⟨fun x y hxy => ?_, fun y => ⟨KaehlerDifferential.mapExteriorPower k B A q y, ?_⟩⟩
  · have hx := mapExteriorPower_comp k A B A q x
    have hy := mapExteriorPower_comp k A B A q y
    rw [mapExteriorPower_self_apply] at hx hy
    rw [← hx, ← hy, hxy]
  · have hy := mapExteriorPower_comp k B A B q y
    rwa [mapExteriorPower_self_apply] at hy

/-- **Rational forms of a non-empty open.** Moving rational forms of a non-empty open `U` of an
integral scheme to its function field is bijective. -/
theorem openFormsMap_bijective {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
    (U : Y.Opens) [Nonempty U] (sY : Y ⟶ Spec (.of k)) (q : ℕ) :
    Function.Bijective (openFormsMap U sY q) := by
  let := MMP.Mori.functionFieldAlgebra sY
  let := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
  let := openFunctionFieldAlgebra U
  have := isScalarTower_openFunctionField U sY
  exact mapExteriorPower_bijective k U.toScheme.functionField Y.functionField
    (openFunctionFieldEquiv U).bijective q

end MMP.FourfoldProofs.FractionalLogComplexProof
