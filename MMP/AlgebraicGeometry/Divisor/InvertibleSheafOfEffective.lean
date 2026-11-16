module

public import MMP.AlgebraicGeometry.Divisor.EffectiveCartierDivisor
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafSpelling

/-!
# The invertible sheaf of an effective Cartier divisor is the Stacks one

For an effective Cartier divisor `D` on a scheme `X`, with closed subscheme `Z` and ideal sheaf
`ℐ_D`, the sheaf `𝒪_X(D) = MMP.CartierDivisor.sheaf D ⊆ 𝒦_X` is the Stacks project's
invertible sheaf `Stacks.Divisors.invertibleSheaf' Z = SheafHom(ℐ_D, 𝒪_X)`.

## Main results

* `MMP.CartierDivisor.idealSheafIsoSheafNeg`: `ℐ_D ≅ 𝒪_X(-D)`.
* `MMP.CartierDivisor.unitIsoSheafZero`: `𝒪_X ≅ 𝒪_X(0)`.
* `MMP.CartierDivisor.sheafIsoInvertibleSheaf`: `𝒪_X(D) ≅ Stacks.Divisors.invertibleSheaf' Z`.

## Implementation notes

`ℐ_D ≅ 𝒪_X(-D)` holds on sections: a section of `𝒪_X` lies in `ℐ_D` exactly when it is a
multiple of the local equation. Then `𝒪_X(D) ⊗ ℐ_D ≅ 𝒪_X(D) ⊗ 𝒪_X(-D) ≅ 𝒪_X(0) ≅ 𝒪_X` by
multiplication in `𝒦_X`, so `𝒪_X(D)` is the tensor inverse, i.e. the dual, of `ℐ_D`.

## References

* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [W. Fulton, *Intersection Theory*][fulton1998], Appendix B.4.4.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MMP.Intersection

universe u

namespace MMP

variable {X : Scheme.{u}}

namespace CartierDivisorSheaf

open CartierDivisor

/-- If `f` is a local equation of `D`, then `f⁻¹` is a local equation of `-D`. -/
theorem isLocalEquationOn_neg {D : X.CartierDivisor} {U : X.Opens}
    {f : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hf : IsLocalEquationOn D U f) :
    IsLocalEquationOn (-D) U f⁻¹ := by
  unfold IsLocalEquationOn at *
  rw [cartierClass_inv, hf]
  simp only [restrictDivisor, map_neg]

/-- `1` is a local equation of the zero divisor on every open. -/
theorem isLocalEquationOn_zero (W : X.Opens) :
    IsLocalEquationOn (0 : X.CartierDivisor) W 1 := by
  rw [IsLocalEquationOn, cartierClass_one]
  simp only [restrictDivisor, map_zero]

/-- A regular local equation `g` of `D` on `U` is, in `𝒦_X`, a section of `𝒪_X(-D)`. -/
theorem mem_neg_toK {D : X.CartierDivisor} {U : X.Opens} {g : Γ(X, U)}
    (hg : IsRegularLocalEquation D g) : Mem (-D) U (toK U g) := by
  obtain ⟨hu, hl⟩ := hg
  have := mem_inv (isLocalEquationOn_neg hl)
  rwa [inv_inv, hu.unit_spec] at this

/-- A section `a` of `𝒪_X` over `V ⊆ U`, `g` a regular local equation of `D` on `U`, lies in
`𝒪_X(-D)` exactly when it is a multiple of `g|_V`. -/
theorem mem_neg_toK_iff {D : X.CartierDivisor} {U V : X.Opens} {g : Γ(X, U)}
    (hg : IsRegularLocalEquation D g) (hVU : V ≤ U) (a : Γ(X, V)) :
    Mem (-D) V (toK V a) ↔ a ∈ Ideal.span {(X.presheaf.map (homOfLE hVU).op).hom g} := by
  have hg' := hg.res hVU
  constructor
  · intro ha
    obtain ⟨hu, hl⟩ := hg'
    obtain ⟨c, hc⟩ := ha V le_rfl _ (isLocalEquationOn_neg hl)
    refine Ideal.mem_span_singleton'.mpr ⟨c, toK_injective V ?_⟩
    rw [map_mul, hc, resK_id, mul_assoc, Units.inv_mul_of_eq hu.unit_spec, mul_one]
  · intro ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul]
    exact (mem_neg_toK hg').mul_toK b

/-- Sections killed by a morphism of schemes restrict to sections killed by it. -/
theorem app_res_eq_zero {Z : Scheme.{u}} (i : Z ⟶ X) {V V' : X.Opens} (h : V' ≤ V)
    {a : Γ(X, V)} (ha : i.app V a = 0) : i.app V' ((X.presheaf.map (homOfLE h).op).hom a) = 0 := by
  have := congr(($(i.naturality (homOfLE h).op)).hom a)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [this, ha, map_zero]

/-- **The ideal sheaf of `D` is `𝒪_X(-D)`, on sections.** A section `a` of `𝒪_X` over `V` is
killed by the closed immersion of the subscheme of the effective divisor `D` exactly when, in
`𝒦_X`, it is a section of `𝒪_X(-D)`. -/
theorem app_subschemeι_eq_zero_iff {D : X.CartierDivisor} (hD : IsEffective D) (V : X.Opens)
    (a : Γ(X, V)) : (subscheme D hD).subschemeι.app V a = 0 ↔ Mem (-D) V (toK V a) := by
  constructor
  · intro ha
    refine Mem.of_locally fun x hx ↦ ?_
    obtain ⟨U, ⟨g, hg⟩, hxU⟩ := exists_affineOpens_isEffectiveOn hD x
    refine ⟨V ⊓ U, inf_le_left, ⟨hx, hxU⟩, ?_⟩
    rw [resK_toK, mem_neg_toK_iff hg inf_le_right, ← ker_subschemeι_app hD hg _ inf_le_right]
    exact app_res_eq_zero _ inf_le_left ha
  · intro ha
    rw [← Stacks.Divisors.mem_kerSubmodule_structureModuleHom_iff]
    refine (SheafOfModules.kerSubmodule (Stacks.Divisors.structureModuleHom
      (subscheme D hD).subschemeι)).isSheaf (X := op V)
        (show (SheafOfModules.unit X.ringCatSheaf).val.obj (op V) from a) fun x hx ↦ ?_
    obtain ⟨U, ⟨g, hg⟩, hxU⟩ := exists_affineOpens_isEffectiveOn hD x
    refine ⟨V ⊓ U, homOfLE inf_le_left, ?_, ⟨hx, hxU⟩⟩
    have h : (subscheme D hD).subschemeι.app (V ⊓ U)
        ((X.presheaf.map (homOfLE (inf_le_left : V ⊓ (U : X.Opens) ≤ V)).op).hom a) = 0 := by
      rw [← RingHom.mem_ker, ker_subschemeι_app hD hg _ inf_le_right,
        ← mem_neg_toK_iff hg inf_le_right, ← resK_toK]
      exact ha.res inf_le_left
    exact (Stacks.Divisors.mem_kerSubmodule_structureModuleHom_iff _ (V ⊓ U) _).mpr h

variable {D : X.CartierDivisor} (hD : IsEffective D)

/-- The sectionwise kernel of `𝒪_X ⟶ i_*𝒪_Z`, `Z` the subscheme of the effective divisor `D`. -/
abbrev idealKer : (SheafOfModules.unit X.ringCatSheaf).Submodule :=
  SheafOfModules.kerSubmodule (Stacks.Divisors.structureModuleHom (subscheme D hD).subschemeι)

include hD in
/-- For effective `D`, every section of `𝒪_X(-D) ⊆ 𝒦_X` is a section of `𝒪_X`. -/
theorem exists_toK_eq_of_mem_neg {V : X.Opens} {s : X.totalQuotientSheaf.obj.obj (op V)}
    (hs : Mem (-D) V s) : ∃ a : Γ(X, V), toK V a = s := by
  refine mem_range_toK_of_locally s fun x hx ↦ ?_
  obtain ⟨U, ⟨g, hg⟩, hxU⟩ := exists_affineOpens_isEffectiveOn hD x
  obtain ⟨hu, hl⟩ := hg.res (inf_le_right : V ⊓ (U : X.Opens) ≤ U)
  obtain ⟨c, hc⟩ := hs (V ⊓ U) inf_le_left _ (isLocalEquationOn_neg hl)
  refine ⟨V ⊓ U, inf_le_left, ⟨hx, hxU⟩, c * (X.presheaf.map (homOfLE inf_le_right).op).hom g, ?_⟩
  rw [map_mul, hc, mul_assoc, Units.inv_mul_of_eq hu.unit_spec, mul_one]

/-- A section of `ℐ_D` over `V`, as a section of `𝒪_X(-D) ⊆ 𝒦_X`. -/
def kerToNeg (V : X.Opens) :
    (idealKer hD).toSheafOfModules.val.obj (op V) →ₗ[X.ringCatSheaf.obj.obj (op V)]
      (CartierDivisor.sheaf (-D)).val.obj (op V) where
  toFun a := (⟨toK V a.1, (app_subschemeι_eq_zero_iff hD V a.1).mp
    ((Stacks.Divisors.mem_kerSubmodule_structureModuleHom_iff _ V a.1).mp a.2)⟩ :
      ↥((CartierDivisor.sheafSubmodule (-D)).obj (op V)))
  map_add' a b := Subtype.ext (map_add (toK V) a.1 b.1)
  map_smul' c a := Subtype.ext (map_mul (toK V) c a.1)

/-- The map `kerToNeg` from sections of `ℐ_D` to sections of `𝒪_X(-D)` over `V` is bijective. -/
theorem kerToNeg_bijective (V : X.Opens) : Function.Bijective (kerToNeg hD V) := by
  refine ⟨fun a b h ↦ Subtype.ext (toK_injective V (congrArg Subtype.val h)), fun s ↦ ?_⟩
  obtain ⟨a, ha⟩ := exists_toK_eq_of_mem_neg hD
    (show ↥((CartierDivisor.sheafSubmodule (-D)).obj (op V)) from s).2
  refine ⟨⟨a, (Stacks.Divisors.mem_kerSubmodule_structureModuleHom_iff _ V a).mpr
    ((app_subschemeι_eq_zero_iff hD V a).mpr
      (ha ▸ (show ↥((CartierDivisor.sheafSubmodule (-D)).obj (op V))
      from s).2))⟩, Subtype.ext ha⟩

/-- The sectionwise kernel of `𝒪_X ⟶ i_*𝒪_Z` is `𝒪_X(-D)`, through `𝒪_X ⊆ 𝒦_X`. -/
def idealKerIsoSheafNeg : (idealKer hD).toSheafOfModules ≅ (CartierDivisor.sheaf (-D)) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun V ↦ (LinearEquiv.ofBijective (kerToNeg hD V.unop)
        (kerToNeg_bijective hD V.unop)).toModuleIso)
      (by
        intro V V' g
        refine ModuleCat.hom_ext (LinearMap.ext fun a ↦ Subtype.ext ?_)
        change toK V'.unop ((X.presheaf.map (homOfLE (leOfHom g.unop)).op).hom a.1) =
          resK (leOfHom g.unop) (toK V.unop a.1)
        exact (resK_toK _ _).symm))

end CartierDivisorSheaf

namespace CartierDivisor

open CartierDivisorSheaf

/-- **`ℐ_D ≅ 𝒪_X(-D)`.** For an effective Cartier divisor `D`, the ideal sheaf of its subscheme
is the invertible sheaf `𝒪_X(-D) ⊆ 𝒦_X`. -/
def idealSheafIsoSheafNeg (D : X.CartierDivisor) (hD : IsEffective D) :
    Stacks.ClosedImmersion.idealSheaf (subscheme D hD).subschemeι.toLRSHom.toShHom ≅
      CartierDivisor.sheaf (-D) :=
  Stacks.Divisors.idealSheafIsoKerSubmodule _ ≪≫ idealKerIsoSheafNeg hD

end CartierDivisor

namespace CartierDivisorSheaf

/-- Every section of `𝒪_X` is a section of `𝒪_X(0)`. -/
theorem mem_zero_toK (V : X.Opens) (a : Γ(X, V)) : Mem (0 : X.CartierDivisor) V (toK V a) := by
  have := (mem_inv (isLocalEquationOn_zero V)).mul_toK a
  rwa [inv_one, Units.val_one, mul_one] at this

/-- The inclusion `𝒪_X ⟶ 𝒪_X(0)` over `V`. -/
def unitToZero (V : X.Opens) :
    X.ringCatSheaf.obj.obj (op V) →ₗ[X.ringCatSheaf.obj.obj (op V)]
      (CartierDivisor.sheaf (0 : X.CartierDivisor)).val.obj (op V) where
  toFun a := (⟨toK V a, mem_zero_toK V a⟩ :
    ↥((CartierDivisor.sheafSubmodule (0 : X.CartierDivisor)).obj (op V)))
  map_add' a b := Subtype.ext (map_add (toK V) a b)
  map_smul' c a := Subtype.ext (map_mul (toK V) c a)

/-- The inclusion `unitToZero` of sections of `𝒪_X` into sections of `𝒪_X(0)` over `V` is
bijective. -/
theorem unitToZero_bijective (V : X.Opens) : Function.Bijective (unitToZero (X := X) V) := by
  refine ⟨fun a b h ↦ toK_injective V (congrArg Subtype.val h), fun s ↦ ?_⟩
  obtain ⟨a, ha⟩ := (mem_iff (isLocalEquationOn_zero ⊤) le_top _).mp
    (show ↥((CartierDivisor.sheafSubmodule (0 : X.CartierDivisor)).obj (op V)) from s).2
  refine ⟨a, Subtype.ext ?_⟩
  rwa [inv_one, Units.val_one, map_one, mul_one] at ha

end CartierDivisorSheaf

namespace CartierDivisor

open CartierDivisorSheaf

/-- **`𝒪_X(0) = 𝒪_X`.** -/
def unitIsoSheafZero (X : Scheme.{u}) :
    SheafOfModules.unit X.ringCatSheaf ≅ (CartierDivisor.sheaf (0 : X.CartierDivisor)) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun V ↦ (LinearEquiv.ofBijective (unitToZero V.unop)
        (unitToZero_bijective V.unop)).toModuleIso)
      (by
        intro V V' g
        refine ModuleCat.hom_ext (LinearMap.ext fun a ↦ Subtype.ext ?_)
        change toK V'.unop ((X.presheaf.map (homOfLE (leOfHom g.unop)).op).hom a) =
          resK (leOfHom g.unop) (toK V.unop a)
        exact (resK_toK _ _).symm))

/-- Multiplication in `𝒦_X`: `𝒪_X(D) ⊗ ℐ_D ≅ 𝒪_X(D) ⊗ 𝒪_X(-D) ≅ 𝒪_X(0) = 𝒪_X`. -/
def tensorIdealSheafIsoUnit (D : X.CartierDivisor) (hD : IsEffective D) :
    Scheme.Modules.tensorObj (CartierDivisor.sheaf D)
        (Stacks.ClosedImmersion.idealSheaf (subscheme D hD).subschemeι.toLRSHom.toShHom) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  CartierDivisorSheaf.tensorIso (Iso.refl _) (idealSheafIsoSheafNeg D hD) ≪≫
    CartierDivisorSheaf.sheafMulIso D (-D) ≪≫
      eqToIso (congrArg CartierDivisor.sheaf (add_neg_cancel D)) ≪≫
      (unitIsoSheafZero X).symm

/-- **`𝒪_X(D) ≅ ℐ_D^∨`**: for an effective Cartier divisor `D`, the invertible sheaf
`𝒪_X(D) ⊆ 𝒦_X` is the Stacks project's invertible sheaf `Stacks.Divisors.invertibleSheaf'` of the
subscheme of `D`, the dual `SheafHom(ℐ_D, 𝒪_X)` of its ideal sheaf (Stacks 01WX). -/
def sheafIsoInvertibleSheaf (D : X.CartierDivisor) (hD : IsEffective D) :
    (CartierDivisor.sheaf D) ≅ Stacks.Divisors.invertibleSheaf' (subscheme D hD) :=
  haveI := isEffectiveCartierDivisor_subscheme hD
  haveI := Stacks.Divisors.isTensorInvertible_negativeTwist (subscheme D hD)
  Stacks.SheafOfModules.isoOfTensorIsoUnit _ _ (Stacks.Divisors.negativeTwist' (subscheme D hD))
    (CartierDivisor.sheaf D) (Stacks.Divisors.invertibleSheaf' (subscheme D hD))
    (tensorIdealSheafIsoUnit D hD)
    (Stacks.SheafOfModules.Scheme.evaluationIso X (Stacks.Divisors.negativeTwist' (subscheme D hD)))

end CartierDivisor

end MMP
