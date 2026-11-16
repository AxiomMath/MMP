module

public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.CartierWeilDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.ConstantGenericStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FunctionFieldSection

/-!
# Rational functions as sections of the sheaf of meromorphic functions

On an integral scheme `X`, Stacks' comparison `functionFieldToTotalQuotientSheaf X` of the sheaf
`𝒦_X` of meromorphic functions with the constant sheaf on the function field gives ring maps
`R(X) → 𝒦_X(U)`, bijective for `U ≠ ∅`.

## Main results

* `MMP.CartierDivisorSheaf.ofFunctionField`: the map `R(X) → 𝒦_X(U)`.
* `MMP.CartierDivisorSheaf.ofFunctionField_bijective`: it is bijective for nonempty `U`.
* `MMP.CartierDivisorSheaf.totalQuotientStalkToFunctionField_germ_top_ofFunctionField`: the
  germ of `r ∈ R(X)` at any point, read in the function field, is `r`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace MMP.CartierDivisorSheaf

variable {X : Scheme.{u}} [IsIntegral X]

attribute [local instance] AlgebraicGeometry.hasSheafifyAddCommGrpCat

/-- On an integral scheme, the map `R(X) → 𝒦_X(U)` comparing `𝒦_X` with the constant sheaf on
the function field. -/
def ofFunctionField (U : X.Opens) : X.functionField →+* X.totalQuotientSheaf.obj.obj (op U) :=
  ((functionFieldToTotalQuotientSheaf X).app (op U)).hom

/-- For `V ≤ U`, restricting `ofFunctionField U r` from `U` to `V` gives `ofFunctionField V r`. -/
theorem resK_ofFunctionField {U V : X.Opens} (h : V ≤ U) (r : X.functionField) :
    resK h (ofFunctionField U r) = ofFunctionField V r :=
  (ConcreteCategory.congr_hom ((functionFieldToTotalQuotientSheaf X).naturality (homOfLE h).op)
    r).symm

/-- On an integral scheme, the map `R(X) → 𝒦_X(U)` is bijective for every nonempty open `U`. -/
theorem ofFunctionField_bijective (U : X.Opens) (hU : (U : Set X).Nonempty) :
    Function.Bijective (ofFunctionField (X := X) U) := by
  refine ⟨functionFieldToTotalQuotientSheaf_app_injective X U hU, fun s ↦ ?_⟩
  obtain ⟨a, ha⟩ := exists_eq_constantSheafOnSpace_section X X.functionField U hU.to_subtype
    (((totalQuotientSheafIsoConstant X).val.hom.hom.app (op U)) s)
  refine ⟨a, ?_⟩
  change ((totalQuotientSheafIsoConstant X).val.inv.hom.app (op U))
    (((toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (op U)) a) = s
  rw [← ha]
  exact ConcreteCategory.congr_hom
    (congrArg (fun φ ↦ φ.hom.app (op U)) (totalQuotientSheafIsoConstant X).val.hom_inv_id) s

/-- On an integral scheme, restricting sections of `𝒦_X` from `U` to `U ∩ U₀`, for a nonempty
open `U₀`, is injective. -/
theorem resK_inf_injective {U₀ : X.Opens} (hU₀ : (U₀ : Set X).Nonempty) (U : X.Opens) :
    Function.Injective (resK (inf_le_left : U ⊓ U₀ ≤ U)) := by
  intro s s' hss'
  refine TopCat.Sheaf.eq_of_locally_eq' X.totalQuotientSheaf (fun _ : U ↦ U) U
    (fun _ ↦ 𝟙 U) (fun x hx ↦ Opens.mem_iSup.2 ⟨⟨x, hx⟩, hx⟩) _ _ fun x ↦ ?_
  change resK (le_refl U) s = resK (le_refl U) s'
  rw [resK_id, resK_id]
  have hU : (U : Set X).Nonempty := ⟨x.1, x.2⟩
  obtain ⟨a, rfl⟩ := (ofFunctionField_bijective U hU).2 s
  obtain ⟨b, rfl⟩ := (ofFunctionField_bijective U hU).2 s'
  rw [resK_ofFunctionField, resK_ofFunctionField] at hss'
  rw [(ofFunctionField_bijective _ (nonempty_preirreducible_inter U.isOpen U₀.isOpen hU hU₀)).1
    hss']

variable [IsLocallyNoetherian X]

/-- The germ at any point `x` of the global section `r` of `𝒦_X`, read in the function field
through the identification of the stalk `𝒦_{X,x}` with `R(X)`, is `r`. -/
theorem totalQuotientStalkToFunctionField_germ_top_ofFunctionField
    (r : X.functionField) (x : X) :
    totalQuotientStalkToFunctionField x
        (X.totalQuotientSheaf.presheaf.germ ⊤ x trivial (ofFunctionField ⊤ r)) = r := by
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (X.presheaf.stalk x)) r
  obtain ⟨W, hxW, a', rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf a
  obtain ⟨W', hW'W, hxW', b', hb'⟩ :=
    TopCat.Presheaf.exists_le_germ_eq X.presheaf (b : X.presheaf.stalk x) hxW
  haveI : Nonempty W' := ⟨⟨x, hxW'⟩⟩
  set a'' := X.presheaf.map (homOfLE hW'W).op a'
  have ha'' : X.presheaf.germ W x hxW a' = X.presheaf.germ W' x hxW' a'' :=
    (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hW'W) x hxW' a').symm
  dsimp only at hab
  rw [ha'', ← hb'] at hab
  rw [Scheme.algebraMap_germ_eq_germToFunctionField, Scheme.algebraMap_germ_eq_germToFunctionField]
    at hab
  have hF : ∀ c : Γ(X, W'), ofFunctionField W' (X.germToFunctionField W' c) =
      X.toTotalQuotientSheaf.hom.app (op W') c := fun c ↦
    functionFieldToTotalQuotientSheaf_germ X W' c
      (((genericPoint_spec X).mem_open_set_iff W'.isOpen).2 ⟨x, trivial, hxW'⟩)
  have key : ofFunctionField W' r * X.toTotalQuotientSheaf.hom.app (op W') b' =
      X.toTotalQuotientSheaf.hom.app (op W') a'' := by
    rw [← hF, ← hF, ← map_mul, hab]
  let g := X.totalQuotientSheaf.presheaf.germ W' x hxW' ≫ totalQuotientStalkToFunctionField x
  have hg : ∀ c : Γ(X, W'), g (X.toTotalQuotientSheaf.hom.app (op W') c) =
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W' x hxW' c) := fun c ↦
    totalQuotientStalkToFunctionField_germ_apply x W' hxW' c
  have hkey := congrArg g key
  rw [map_mul, hg, hg, hb'] at hkey
  have hr : g (ofFunctionField W' r) = r := by
    refine mul_right_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2)
      (hkey.trans ?_)
    rw [← hb', Scheme.algebraMap_germ_eq_germToFunctionField,
      Scheme.algebraMap_germ_eq_germToFunctionField]
    exact hab.symm
  refine Eq.trans ?_ hr
  change _ = totalQuotientStalkToFunctionField x
    (X.totalQuotientSheaf.presheaf.germ W' x hxW' (ofFunctionField W' r))
  rw [← resK_ofFunctionField (le_top : W' ≤ ⊤)]
  exact congrArg _ (TopCat.Presheaf.germ_res_apply X.totalQuotientSheaf.presheaf
    (homOfLE (le_top : W' ≤ ⊤)) x hxW' _).symm

end MMP.CartierDivisorSheaf
