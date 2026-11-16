module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafTensor
public import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.Basic
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
import MMP.AlgebraicGeometry.Singularities.Semismooth.SingularLocus
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent
import MMP.AlgebraicGeometry.Modules.TotalQuotientSheaf

/-!
# Divisorial sheaves, curves on smooth surfaces, and orders along a smooth blow-up

Three local facts used in the resolution of threefolds.

**Divisorial sheaves.** Let `X` be a normal variety over a field `k` and `D = ∑ d_E E` a Weil
divisor on `X`. The divisorial sheaf `𝒪_X(D) ⊆ 𝒦_X` is coherent: on an affine open `Spec A`,
with `g ≠ 0` vanishing to order `≥ d_E` along every `E` with `d_E > 0`, multiplication by `g`
embeds `𝒪_X(D)(Spec A)` into `A`, by algebraic Hartogs, and `A` is Noetherian. If `g` is a local
equation of a divisor `C` on an open `U`, then `𝒪_X(D + C)|_U = g⁻¹ 𝒪_X(D)|_U`. Consequently,
when `C` is Cartier, the multiplication map `𝒪_X(D) ⊗ 𝒪_X(C) ⟶ 𝒪_X(D + C)` is an isomorphism:
it is locally injective and locally surjective, since near a point where `ψ` is a local equation
of `C` every section of `𝒪_X(D + C)` is `(ψ s) ⊗ ψ⁻¹` and every tensor is of the form `a ⊗ ψ⁻¹`.

**Curves on a smooth surface.** Let `Y` be a smooth surface over an algebraically closed field
`k` and `C ⊆ Y` a curve. At `y ∈ C` the local ring `𝒪_{Y,y}` is regular, hence factorial, so the
ideal of `C` at `y` is `(f)` for a prime `f ∈ 𝔪_y`, and `mult_y C = 1` says `f ∉ 𝔪_y²`. This is
exactly when `𝒪_{Y,y}/(f)` is regular, which over the perfect field `k` means that `C` is smooth
over `k` at `y`.

**Orders along a smooth blow-up.** Let `Y` be a smooth variety of dimension `d` over `k`,
`Z = V(I)` a smooth irreducible closed subscheme of codimension `c ≥ 2` with generic point `η_Z`,
`π : Bl_Z Y ⟶ Y` the blow-up and `E` its exceptional prime divisor, with generic point `ξ`.
The local ring at `ξ` is a discrete valuation ring with `𝔪_ξ^s ∩ 𝒪_{Y,η_Z} = 𝔪_Z^s`, so for
nonzero `g ∈ 𝒪_{Y,η_Z}` the order of `π^*g` along `E` is the largest `s` with `g ∈ 𝔪_Z^s`.
If a rational `m`-canonical form `τ` generates `ω_Y^{⊗m}` near `η_Z`, then
`ord_E(π^*τ) = m(c - 1)`: comparing generators of the top forms at `η_Z` and at `ξ`, which differ
by a function of order `c - 1` along `E`, the coefficient of `τ` is a unit at `η_Z`.

## Main results

* `MMP.Threefold.isCoherent_divisorialSheaf_and_isIso_divisorialSheafTensorMul`: coherence of
  `𝒪_X(D)`, the local identification `𝒪_X(D + C)|_U = g⁻¹ 𝒪_X(D)|_U`, and the isomorphism
  `𝒪_X(D) ⊗ 𝒪_X(C) ≅ 𝒪_X(D + C)` for Cartier `C`.
* `MMP.Threefold.Resolution.multiplicityAt_eq_one_iff_exists_mem_smoothLocus`: a curve on a
  smooth surface has multiplicity one at `y` if and only if it is smooth at `y`.
* `MMP.Threefold.Resolution.ord_exceptionalPrimeDivisor_pullback_and_ordForm_pullback`: the
  orders of pulled-back functions and pluricanonical forms along the exceptional divisor.

## Implementation notes

* The tensor isomorphism is stated as `IsIso` of the multiplication map
  `MMP.Mori.Divisor.divisorialSheafTensorMul D C`, so that it is the map induced by the local
  identifications. It is proved without gluing trivializations: a locally bijective morphism
  into a sheaf has invertible adjoint transpose out of the sheafification. The local
  identification is stated on sections of `𝒦_X(V) = ∏_{η_Z ∈ V} 𝒪_{X,η_Z}`.
* A curve `C` is a `MMP.Mori.PrimeDivisor`, regarded as the closed subscheme
  `C.idealSheaf.subscheme`; "smooth at `y`" means that the point of this subscheme over `y`
  lies in the smooth locus of its structure morphism to `Spec k`.
* For the blow-up, `π^*g` is the image of `g` under `AlgebraicGeometry.functionFieldMap`, and
  `ord_E(π^*g) = max {s | g ∈ 𝔪_Z^s}` is stated as `s ≤ ord_E(π^*g) ↔ g ∈ 𝔪_Z^s` for all
  `s : ℕ`. "`τ` generates `ω_Y^{⊗m}` at `η_Z`" is `MMP.Mori.GeneratesOn 0 m U τ` for an open
  `U ∋ η_Z`, with `ω_Y` the sheaf of `d`-forms, `d = dim Y`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4,
  2.29
* [J. Kollár, *Lectures on resolution of singularities*][KollarResolution], 1.36–1.38
* [R. Hartshorne, *Algebraic geometry*][Har77], II.6
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe v u

/-! ### Divisorial sheaves -/

namespace MMP.Threefold

open Opposite
open scoped TensorProduct

section Sheafification

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- A locally bijective morphism from a presheaf of abelian groups to a sheaf has invertible
adjoint transpose out of the sheafification. -/
private theorem isIso_sheafificationAdjunction_homEquiv_symm_of_isLocallyBijective
    {P : Cᵒᵖ ⥤ AddCommGrpCat.{v}} {N : Sheaf J AddCommGrpCat.{v}}
    (f : P ⟶ (sheafToPresheaf J _).obj N)
    (hinj : Presheaf.IsLocallyInjective J f) (hsurj : Presheaf.IsLocallySurjective J f) :
    IsIso (((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv P N).symm f) := by
  set φ := ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv P N).symm f with hφ
  have hcomp : toSheafify J P ≫ φ.hom = f := by
    have := (sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv_unit P N φ
    rw [hφ, Equiv.apply_symm_apply] at this
    exact this.symm
  haveI := GrothendieckTopology.instIsLocallyInjectiveToSheafify (J := J) (A := AddCommGrpCat.{v}) P
  haveI := GrothendieckTopology.instIsLocallySurjectiveToSheafify (J := J)
    (A := AddCommGrpCat.{v}) P
  have h1 : Presheaf.IsLocallyInjective J φ.hom :=
    (Presheaf.comp_isLocallyInjective_iff J _ _).1 (hcomp ▸ hinj)
  have h2 : Presheaf.IsLocallySurjective J φ.hom :=
    (Presheaf.comp_isLocallySurjective_iff J _ _).1 (hcomp ▸ hsurj)
  exact (Sheaf.isLocallyBijective_iff_isIso φ).1 ⟨⟨h1.1⟩, ⟨h2.1⟩⟩

variable {R : Sheaf J RingCat.{v}} [J.HasSheafCompose (forget₂ RingCat.{v} AddCommGrpCat.{v})]

/-- A morphism from a presheaf of modules to a sheaf of modules that is locally injective and
locally surjective has invertible adjoint transpose out of the sheafification. -/
private theorem isIso_sheafificationHomEquiv_symm_of_isLocallyBijective
    {A : PresheafOfModules.{v} R.obj} {N : SheafOfModules.{v} R}
    (ψ : A ⟶ (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj ((SheafOfModules.forget R).obj N))
    (hinj : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R.obj).map ψ))
    (hsurj : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map ψ)) :
    IsIso ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm ψ) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf R),
    PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  exact isIso_sheafificationAdjunction_homEquiv_symm_of_isLocallyBijective _ hinj hsurj

end Sheafification

section

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-- A unit `g` of `K(X)` and its inverse multiply to `1` on every component. -/
private theorem inv_apply_mul_apply (g : (Mori.RationalFunctions X)ˣ)
    (Z : irreducibleComponents X) :
    ((g⁻¹ : (Mori.RationalFunctions X)ˣ) : Mori.RationalFunctions X) Z *
      (g : Mori.RationalFunctions X) Z = 1 := by
  rw [← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Pi.one_apply]

/-- Multiplying by a unit `g` of `K(X)` shifts orders along `E` by `v_E(g)`. -/
private theorem ordGE_iff_ordGE_mul {E : Mori.PrimeDivisor X} (g : (Mori.RationalFunctions X)ˣ)
    (n : ℤ) (f : X.presheaf.stalk (Mori.componentGenericPoint X E.component)) :
    E.OrdGE n f ↔ E.OrdGE (n + E.ord g) ((g : Mori.RationalFunctions X) E.component * f) := by
  have key : ∀ (g : (Mori.RationalFunctions X)ˣ) (n : ℤ) f, E.OrdGE n f →
      E.OrdGE (n + E.ord g) ((g : Mori.RationalFunctions X) E.component * f) :=
    fun g n f hf => (Mori.PrimeDivisor.OrdGE.mul (Or.inr (E.valuation_component g).ge) hf).mono
      (le_of_eq (by ring))
  refine ⟨key g n f, fun h => ?_⟩
  have := key g⁻¹ _ _ h
  rwa [← mul_assoc, inv_apply_mul_apply, one_mul, Mori.PrimeDivisor.ord_inv,
    add_neg_cancel_right] at this

/-- `𝒪_X(D + C)|_U = g⁻¹ 𝒪_X(D)|_U` on sections, for a local equation `g` of `C` on `U`. -/
private theorem isDivisorialSection_add_iff (D C : Mori.Divisor X) {U : X.Opens}
    {g : (Mori.RationalFunctions X)ˣ} (hg : C.IsLocalEquation U g) {V : X.Opens} (hV : V ≤ U)
    (φ : ToType ((Mori.rationalFunctionsPresheaf X).obj (op V))) :
    (D + C).IsDivisorialSection V φ ↔
      D.IsDivisorialSection V (fun Z => (g : Mori.RationalFunctions X) Z.1 * φ Z) := by
  refine forall_congr' fun E => forall_congr' fun hE => ?_
  rw [ordGE_iff_ordGE_mul g, Mori.DivisorWithCoeffs.coeff_add, ← hg E (hE.mono
    (Set.inter_subset_inter_right _ hV)), neg_add, neg_add_cancel_right]

/-- If `ψ` is a local equation of `C` on `W`, then `ψ⁻¹` is a section of `𝒪_X(C)` over `W`. -/
private noncomputable def invSection {C : Mori.Divisor X} {W : X.Opens}
    {ψ : (Mori.RationalFunctions X)ˣ}
    (hψ : C.IsLocalEquation W ψ) : C.divisorialSubmodule W :=
  ⟨fun Z => ((ψ⁻¹ : (Mori.RationalFunctions X)ˣ) : Mori.RationalFunctions X) Z.1, fun E h =>
    Or.inr (le_of_eq (by
      rw [Mori.PrimeDivisor.valuation_component, Mori.PrimeDivisor.ord_inv, hψ E h]))⟩

/-- Near a point where `ψ` is a local equation of `C`, a section `s` of `𝒪_X(D + C)` is the
product of the section `ψ s` of `𝒪_X(D)` and the section `ψ⁻¹` of `𝒪_X(C)`. -/
private theorem isLocallySurjective_divisorialTensorMul {D C : Mori.Divisor X}
    (hC : C.IsCartier) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj).map
        (Mori.Divisor.divisorialTensorMul D C)) := by
  refine (TopCat.Presheaf.isLocallySurjective_iff _).mpr fun V s x hx => ?_
  obtain ⟨U, hxU, ψ, hψ⟩ := hC x
  have hψ' := hψ.mono (inf_le_right : V ⊓ U ≤ U)
  let s' : (D + C).divisorialSubmodule V := s
  let a : D.divisorialSubmodule (V ⊓ U) :=
    ⟨fun Z => (ψ : Mori.RationalFunctions X) Z.1 * s'.1 ⟨Z.1, Z.2.1⟩, fun E h =>
      (Mori.PrimeDivisor.OrdGE.mul (Or.inr (E.valuation_component ψ).ge)
        (s'.2 E (h.mono (Set.inter_subset_inter_right _ inf_le_left)))).mono (le_of_eq (by
          rw [Mori.DivisorWithCoeffs.coeff_add, hψ' E h]; ring))⟩
  let b : C.divisorialSubmodule (V ⊓ U) := invSection hψ'
  refine ⟨V ⊓ U, inf_le_left, ⟨(a : D.divisorialSheaf.val.obj (op (V ⊓ U))) ⊗ₜ
    (b : C.divisorialSheaf.val.obj (op (V ⊓ U))), Subtype.ext (funext fun Z => ?_)⟩, hx, hxU⟩
  change ((ψ : Mori.RationalFunctions X) Z.1 * s'.1 ⟨Z.1, Z.2.1⟩) *
      ((ψ⁻¹ : (Mori.RationalFunctions X)ˣ) : Mori.RationalFunctions X) Z.1 = s'.1 ⟨Z.1, Z.2.1⟩
  rw [mul_comm, ← mul_assoc, inv_apply_mul_apply, one_mul]

/-- On an open `W` where `ψ` is a local equation of `C`, the multiplication map
`𝒪_X(D)(W) ⊗ 𝒪_X(C)(W) → 𝒪_X(D + C)(W)` is injective: every tensor is `a ⊗ ψ⁻¹`, because every
section of `𝒪_X(C)` over `W` is a regular multiple of `ψ⁻¹` by algebraic Hartogs. -/
private theorem injective_divisorialTensorMul_app {D C : Mori.Divisor X} {W : X.Opens}
    {ψ : (Mori.RationalFunctions X)ˣ} (hψ : C.IsLocalEquation W ψ) :
    Function.Injective (((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj).map
        (Mori.Divisor.divisorialTensorMul D C)).app (op W)) := by
  let b : C.divisorialSubmodule W := invSection hψ
  refine (injective_iff_map_eq_zero _).mpr fun t ht => ?_
  obtain ⟨a, rfl⟩ : ∃ a : D.divisorialSubmodule W,
      t = (a : D.divisorialSheaf.val.obj (op W)) ⊗ₜ (b : C.divisorialSheaf.val.obj (op W)) := by
    clear ht
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, (TensorProduct.zero_tmul _ _).symm⟩
    | tmul a c =>
      let c' : C.divisorialSubmodule W := c
      have h0 : (0 : Mori.Divisor X).IsDivisorialSection W
          (fun Z => (ψ : Mori.RationalFunctions X) Z.1 * c'.1 Z) := fun E h =>
        (((ordGE_iff_ordGE_mul ψ _ _).mp (c'.2 E h))).mono (le_of_eq (by
          rw [Mori.DivisorWithCoeffs.coeff_zero, hψ E h]; ring))
      obtain ⟨r, hr⟩ := h0.exists_eq
      refine ⟨r • (a : D.divisorialSubmodule W), ?_⟩
      have hc : c = r • (b : C.divisorialSheaf.val.obj (op W)) := by
        refine Subtype.ext (funext fun Z => ?_)
        change c'.1 Z = X.presheaf.germ W _ Z.2 r *
          ((ψ⁻¹ : (Mori.RationalFunctions X)ˣ) : Mori.RationalFunctions X) Z.1
        rw [← Mori.toRationalFunctionsPresheaf_app_apply, hr]
        change c'.1 Z = (ψ : Mori.RationalFunctions X) Z.1 * c'.1 Z *
          ((ψ⁻¹ : (Mori.RationalFunctions X)ˣ) : Mori.RationalFunctions X) Z.1
        rw [mul_comm, ← mul_assoc, inv_apply_mul_apply, one_mul]
      rw [hc]
      exact (TensorProduct.smul_tmul
        (show ToType ((X.presheaf ⋙ forget₂ CommRingCat RingCat).obj (op W)) from r) _ _).symm
    | add t t' ht ht' =>
      obtain ⟨a, rfl⟩ := ht
      obtain ⟨a', rfl⟩ := ht'
      exact ⟨a + a', (TensorProduct.add_tmul _ _ _).symm⟩
  have ha : a = 0 := by
    refine Subtype.ext (funext fun Z => ?_)
    have h := congrFun (congrArg Subtype.val
      (show Mori.Divisor.divisorialMul W a b = 0 from ht)) Z
    change a.1 Z * ((ψ⁻¹ : (Mori.RationalFunctions X)ˣ) : Mori.RationalFunctions X) Z.1 = 0 at h
    change a.1 Z = 0
    rw [← mul_one (a.1 Z), ← inv_apply_mul_apply ψ Z.1, ← mul_assoc, h, zero_mul]
  rw [ha]
  exact TensorProduct.zero_tmul _ _

/-- The multiplication map `𝒪_X(D) ⊗ 𝒪_X(C) → 𝒪_X(D + C)` of presheaves is locally injective
when `C` is Cartier: it is injective over every open where `C` has a local equation. -/
private theorem isLocallyInjective_divisorialTensorMul {D C : Mori.Divisor X}
    (hC : C.IsCartier) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj).map
        (Mori.Divisor.divisorialTensorMul D C)) := by
  refine ⟨fun {W} x y hxy p hp => ?_⟩
  obtain ⟨U, hpU, ψ, hψ⟩ := hC p
  refine ⟨W.unop ⊓ U, homOfLE inf_le_left, ?_, hp, hpU⟩
  apply injective_divisorialTensorMul_app (hψ.mono inf_le_right)
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]

/-- The germ of a regular function on `U` along the component of a prime divisor `E` meeting
`U` comes from the local ring `𝒪_{X,E}`. -/
private theorem germ_eq_toComponent {U : X.Opens} {E : Mori.PrimeDivisor X}
    (hE : (E.support ∩ U).Nonempty) (r : Γ(X, U)) :
    X.presheaf.germ U _ (E.componentGenericPoint_mem_of_nonempty hE) r =
      E.toComponent.hom (X.presheaf.germ U _ (E.genericPoint_mem_of_nonempty hE) r) :=
  (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf _ E.specializes_genericPoint r).symm

/-- A regular function on `U` has nonnegative order along every prime divisor meeting `U`. -/
private theorem ordGE_zero_germ {U : X.Opens} {E : Mori.PrimeDivisor X}
    (hE : (E.support ∩ U).Nonempty) (r : Γ(X, U)) :
    E.OrdGE 0 (X.presheaf.germ U _ (E.componentGenericPoint_mem_of_nonempty hE) r) := by
  have h1 : E.OrdGE 0 1 := Or.inr (by rw [map_one, WithZero.exp_zero])
  have := h1.toComponent_mul (X.presheaf.germ U _ (E.genericPoint_mem_of_nonempty hE) r)
  rwa [mul_one, ← germ_eq_toComponent hE] at this

/-- On an affine open `U` meeting a prime divisor `E`, some regular function vanishes along `E`
and is invertible at the generic point of the component of `E`. -/
private theorem exists_ordGE_one_germ {U : X.Opens} (hU : IsAffineOpen U)
    {E : Mori.PrimeDivisor X} (hE : (E.support ∩ U).Nonempty) :
    ∃ a : Γ(X, U), IsUnit (X.presheaf.germ U _ (E.componentGenericPoint_mem_of_nonempty hE) a) ∧
      E.OrdGE 1 (X.presheaf.germ U _ (E.componentGenericPoint_mem_of_nonempty hE) a) := by
  have hne : E.genericPoint ≠ Mori.componentGenericPoint X E.component := fun h => by
    have hf := Mori.RationalFunctions.isField_stalk X E.component
    rw [← h] at hf
    have := E.isDiscreteValuationRing_localRing
    exact IsDiscreteValuationRing.not_isField _ hf
  have hns : ¬ E.genericPoint ⤳ Mori.componentGenericPoint X E.component := fun h =>
    hne (h.antisymm E.specializes_genericPoint).eq
  rw [specializes_iff_forall_open] at hns
  push Not at hns
  obtain ⟨s, hs, hηs, hEs⟩ := hns
  have hηU := E.componentGenericPoint_mem_of_nonempty hE
  obtain ⟨a, haV, hηa⟩ := hU.exists_basicOpen_le (V := U ⊓ ⟨s, hs⟩)
    ⟨Mori.componentGenericPoint X E.component, hηU, hηs⟩ hηU
  refine ⟨a, (Scheme.mem_basicOpen X a _ hηU).mp hηa, ?_⟩
  have hEgU := E.genericPoint_mem_of_nonempty hE
  have hmax : X.presheaf.germ U _ hEgU a ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint) := fun hunit =>
    hEs (haV ((Scheme.mem_basicOpen X a _ hEgU).mpr hunit)).2
  rw [germ_eq_toComponent hE]
  exact E.ordGE_one_toComponent hmax

/-- On an affine open `U`, some regular function is invertible at the generic point and vanishes
to order at least `d_E` along every prime divisor `E` meeting `U`. -/
private theorem exists_section_ordGE_coeff [IsIntegral X] (D : Mori.Divisor X) {U : X.Opens}
    (hU : IsAffineOpen U) : ∃ g : Γ(X, U),
      (∀ Z : {Z : irreducibleComponents X // Mori.componentGenericPoint X Z ∈ U},
        IsUnit (X.presheaf.germ U _ Z.2 g)) ∧
      ∀ (E : Mori.PrimeDivisor X) (hE : (E.support ∩ U).Nonempty),
        E.OrdGE (D.coeff E).toNat
          (X.presheaf.germ U _ (E.componentGenericPoint_mem_of_nonempty hE) g) := by
  classical
  choose a ha using fun (E : Mori.PrimeDivisor X) (hE : (E.support ∩ U).Nonempty) =>
    exists_ordGE_one_germ hU hE
  let f : Mori.PrimeDivisor X → Γ(X, U) := fun E =>
    if h : (E.support ∩ U).Nonempty then a E h ^ (D.coeff E).toNat else 1
  let g : Γ(X, U) := ∏ E ∈ D.support, f E
  have hZ : ∀ Z Z' : irreducibleComponents X, Z = Z' := by
    rintro ⟨Z, h1⟩ ⟨Z', h2⟩
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h1 h2
    subst h1 h2
    rfl
  refine ⟨g, ?_, fun E hE => ?_⟩
  · rintro ⟨Z, hZU⟩
    rw [map_prod]
    refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun E _ => ?_
    simp only [f]
    split_ifs with hE
    · obtain rfl := hZ Z E.component
      rw [map_pow]
      exact (ha E hE).1.pow _
    · simp
  by_cases hD : E ∈ D.support
  · rw [show g = f E * ∏ x ∈ D.support.erase E, f x from (Finset.mul_prod_erase _ _ hD).symm,
      map_mul]
    have h1 : E.OrdGE (D.coeff E).toNat
        (X.presheaf.germ U _ (E.componentGenericPoint_mem_of_nonempty hE) (f E)) := by
      simp only [f, dif_pos hE, map_pow]
      simpa using (ha E hE).2.pow (D.coeff E).toNat
    exact (h1.mul (ordGE_zero_germ hE (∏ x ∈ D.support.erase E, f x))).mono (add_zero _).ge
  · have : D.coeff E = 0 := Finsupp.notMem_support_iff.mp hD
    rw [this]
    exact ordGE_zero_germ hE g

/-- The sections of `𝒪_X(D)` over an affine open `U` form a finite `Γ(X, U)`-module. -/
private theorem finite_divisorialSubmodule [IsIntegral X] (D : Mori.Divisor X) {U : X.Opens}
    (hU : IsAffineOpen U) : Module.Finite Γ(X, U) (D.divisorialSubmodule U) := by
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨g, hgu, hgE⟩ := exists_section_ordGE_coeff D hU
  let L := LinearMap.lsmul Γ(X, U) (ToType ((Mori.rationalFunctionsPresheaf X).obj (op U))) g
  have hinj : Function.Injective L := by
    intro φ ψ h
    funext Z
    have := congrFun h Z
    change (g • φ) Z = (g • ψ) Z at this
    rw [Mori.rationalFunctions_smul_apply, Mori.rationalFunctions_smul_apply] at this
    exact (hgu Z).mul_left_cancel this
  have hN : (D.divisorialSubmodule U).map L ≤ Submodule.span Γ(X, U) {1} := by
    rintro _ ⟨φ, hφ, rfl⟩
    have h0 : (0 : Mori.Divisor X).IsDivisorialSection U (L φ) := fun E hE => by
      change E.OrdGE _ ((g • φ) ⟨E.component, _⟩)
      rw [Mori.rationalFunctions_smul_apply]
      refine ((hgE E hE).mul (hφ E hE)).mono ?_
      rw [Mori.DivisorWithCoeffs.coeff_zero]
      have := Int.self_le_toNat (D.coeff E)
      omega
    obtain ⟨r, hr⟩ := h0.exists_eq
    refine Submodule.mem_span_singleton.2 ⟨r, ?_⟩
    rw [← hr, Algebra.smul_def, mul_one]
    rfl
  haveI : IsNoetherian Γ(X, U) (Submodule.span Γ(X, U)
      {(1 : ToType ((Mori.rationalFunctionsPresheaf X).obj (op U)))}) :=
    isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span_singleton 1)
  haveI : IsNoetherian Γ(X, U) ((D.divisorialSubmodule U).map L) := isNoetherian_of_le hN
  haveI : Module.Finite Γ(X, U) ((D.divisorialSubmodule U).map L) := Module.IsNoetherian.finite _ _
  exact Module.Finite.equiv (Submodule.equivMapOfInjective L hinj _).symm

end

/-- **Coherence of a divisorial sheaf.** Let `X` be a normal variety over a field `k`, and `D`,
`C` divisors on `X`. Then
1. `𝒪_X(D)` is a coherent `𝒪_X`-module;
2. if `g` is a local equation of `C` on the open `U`, then for every open `V ⊆ U` a section `φ` of
   `𝒦_X` over `V` lies in `𝒪_X(D + C)` if and only if `g φ` lies in `𝒪_X(D)`, that is,
   `𝒪_X(D + C)|_U = g⁻¹ 𝒪_X(D)|_U`;
3. if `C` is Cartier, the multiplication map `𝒪_X(D) ⊗ 𝒪_X(C) ⟶ 𝒪_X(D + C)` is an
   isomorphism. -/
@[mmp "lem_mmp_threefold_weil_divisor_coherent"]
public theorem isCoherent_divisorialSheaf_and_isIso_divisorialSheafTensorMul {k : Type u}
    [Field k] {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] (f : X ⟶ Spec (.of k))
    (hX : Mori.IsVariety k f) (D C : Mori.Divisor X) :
    SheafOfModules.IsCoherent D.divisorialSheaf ∧
    (∀ (U : X.Opens) (g : (Mori.RationalFunctions X)ˣ), C.IsLocalEquation U g →
      ∀ V ≤ U, ∀ φ : ToType ((Mori.rationalFunctionsPresheaf X).obj (op V)),
        (D + C).IsDivisorialSection V φ ↔
          D.IsDivisorialSection V (fun Z => (g : Mori.RationalFunctions X) Z.1 * φ Z)) ∧
    (C.IsCartier → IsIso (Mori.Divisor.divisorialSheafTensorMul D C)) := by
  haveI : AlgebraicGeometry.IsIntegral X := hX.toIsIntegral
  haveI : QuasiCompact f := hX.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : D.divisorialSheaf.IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn _
      (fun V : X.affineOpens => (V : X.Opens)) (IsOpenCover.mk (iSup_affineOpens_eq_top X))
      (fun V => V.2) fun V =>
        Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isFiniteTildeOn_of_moduleFinite_sections
          _ V (finite_divisorialSubmodule D V.2)
  refine ⟨
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType _,
    fun _ _ hg _ hV φ => isDivisorialSection_add_iff D C hg hV φ, fun hC => ?_⟩
  unfold Mori.Divisor.divisorialSheafTensorMul
  rw [PresheafOfModules.sheafificationAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact isIso_sheafificationHomEquiv_symm_of_isLocallyBijective _
    (isLocallyInjective_divisorialTensorMul hC) (isLocallySurjective_divisorialTensorMul hC)

end MMP.Threefold

/-! ### Curves on a smooth surface -/

namespace MMP.Threefold.Resolution

open MMP.Mori MMP.Resolution

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- An element `g ∈ I` has `I`-adic order `1`, i.e. the largest `m` with `g ∈ I ^ m` is `1`,
exactly when `g ∉ I ^ 2`. -/
private lemma iSup_mem_pow_eq_one_iff {R : Type*} [CommRing R] {I : Ideal R} {g : R}
    (hg : g ∈ I) : (⨆ (m : ℕ) (_ : g ∈ I ^ m), (m : ℕ∞)) = 1 ↔ g ∉ I ^ 2 := by
  let f := fun (m : ℕ) (_ : g ∈ I ^ m) => (m : ℕ∞)
  refine ⟨fun h h2 => absurd (h ▸ le_iSup₂ (f := f) 2 h2 : (2 : ℕ∞) ≤ 1) (by decide),
    fun h2 => le_antisymm (iSup₂_le fun m hm => ?_) (le_iSup₂ (f := f) 1 (by rwa [pow_one]))⟩
  by_contra hlt
  exact h2 (Ideal.pow_le_pow_right (by exact_mod_cast not_le.1 hlt) hm)

/-- Over a perfect field, a point `z` of the closed subscheme cut out by an ideal sheaf `I`
lies in the smooth locus exactly when `𝒪_{X,x} ⧸ I_x` is regular, where `x` is the image
of `z`. -/
private lemma mem_smoothLocus_subschemeι_iff {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    {I : X.IdealSheafData} (z : I.subscheme) :
    z ∈ smoothLocus (I.subschemeι ≫ f) ↔
      IsRegularLocalRing (X.presheaf.stalk (I.subschemeι z) ⧸ I.stalkIdeal (I.subschemeι z)) := by
  rw [smoothLocus_eq_smoothLocus,
    (MMP.mem_smoothLocus_iff_isRegularLocalRing_of_perfectField _).1 z]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · haveI := h
    exact .of_ringEquiv (I.subschemeStalkRingEquiv z).symm
  · exact .of_ringEquiv (R := X.presheaf.stalk (I.subschemeι z) ⧸ I.stalkIdeal (I.subschemeι z))
      (I.subschemeStalkRingEquiv z)

section

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

/-- **Multiplicity one is smoothness for a surface curve.** Let `Y` be a smooth surface over an
algebraically closed field `k`, `C` a curve (prime divisor) on `Y` and `y ∈ Y`. Then
`mult_y C = 1` if and only if `C` is smooth over `k` at `y`. -/
@[mmp "lem_mmp_threefold_surface_curve_multiplicity_one"]
public theorem multiplicityAt_eq_one_iff_exists_mem_smoothLocus [IsAlgClosed k]
    (hY : Mori.IsVariety k sY) (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    (C : Mori.PrimeDivisor Y) {y : Y} (hy : y ∈ C.support) :
    C.multiplicityAt y = 1 ↔
      ∃ z : C.idealSheaf.subscheme, C.idealSheaf.subschemeι z = y ∧
        z ∈ smoothLocus (C.idealSheaf.subschemeι ≫ sY) := by
  haveI : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  haveI : Smooth sY := MMP.Resolution.Aux.smooth_of_isSmoothScheme' sY hYs
  obtain ⟨π, hπ, hspan⟩ := MMP.Resolution.Aux.exists_prime_stalk_idealSheaf sY hYs C hy
  have hst : C.idealSheaf.stalkIdeal y = Ideal.span {π} :=
    (Scheme.IdealSheafData.stalkIdeal_eq_stalk _ _).trans hspan
  haveI := isRegularLocalRing_stalk_of_smooth_over_field sY y
  have hπm : π ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).2 hπ.not_unit
  rw [C.multiplicityAt_eq_localMultiplicity hst, localMultiplicity,
    iSup_mem_pow_eq_one_iff hπm]
  constructor
  · intro h2
    obtain ⟨z, rfl⟩ : y ∈ Set.range C.idealSheaf.subschemeι := by
      rwa [Scheme.IdealSheafData.range_subschemeι]
    refine ⟨z, rfl, (mem_smoothLocus_subschemeι_iff sY z).2 ?_⟩
    rw [hst]
    exact Stacks.RegularLocalRing.DirectedColimit.isRegularLocalRing_quotient_span_singleton hπm h2
  · rintro ⟨z, rfl, hsm⟩ h2
    haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk (C.idealSheaf.subschemeι z))
    rw [mem_smoothLocus_subschemeι_iff, hst] at hsm
    exact Stacks.not_isRegularLocalRing_quotient_span_singleton_of_mem_sq
      (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero) h2 hsm

end

/-! ### Orders along the exceptional divisor of a smooth blow-up -/

open IsLocalRing

/-- Along a prime divisor `F` whose local ring is a discrete valuation ring, `s ≤ v_F(a)` if and
only if `a ∈ 𝔪_F^s`, for `a ≠ 0` in `𝒪_{X,F}`. -/
private theorem natCast_le_ord_algebraMap_iff {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (F : MMP.Mori.PrimeDivisor X)
    [IsDiscreteValuationRing F.localRing] {a : F.localRing} (ha : a ≠ 0) (s : ℕ) :
    (s : ℤ) ≤ X.ord (algebraMap F.localRing X.functionField a) F.genericPoint ↔
      a ∈ maximalIdeal F.localRing ^ s := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible F.localRing
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hϖK : algebraMap F.localRing X.functionField ϖ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ0)
  have hord1 : X.ord (algebraMap F.localRing X.functionField ϖ) F.genericPoint = 1 := by
    rw [Scheme.ord_eq_iff F.coheight_genericPoint hϖK]
    have : Ring.KrullDimLE 1 F.localRing := krullDimLE_of_coheight_le F.coheight_genericPoint.le
    exact Ring.ordFrac_irreducible hϖ
  have hord : X.ord (algebraMap F.localRing X.functionField (u * ϖ ^ n)) F.genericPoint = n := by
    rw [map_mul, Scheme.ord_mul (u.isUnit.map _).ne_zero (by rw [map_pow]; exact pow_ne_zero _ hϖK),
      F.ord_algebraMap_of_isUnit u.isUnit, map_pow, ← zpow_natCast,
      MMP.Mori.ord_zpow _ hϖK, hord1]
    simp
  rw [hord, Nat.cast_le, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, Units.dvd_mul_left]
  exact (pow_dvd_pow_iff hϖ0 hϖ.not_isUnit).symm

/-- **Orders on the exceptional divisor of a smooth-centre blow-up.** Let `Y` be a smooth variety
of dimension `d` over `k`, `Z = V(I)` a smooth irreducible closed subscheme of codimension
`c ≥ 2` with generic point `η_Z`, `π : Bl_Z Y ⟶ Y` the blow-up and `E` its exceptional prime
divisor. For every nonzero `g ∈ 𝒪_{Y,η_Z}` and every `s : ℕ`, `s ≤ ord_E(π^*g)` if and only if
`g ∈ 𝔪_Z^s`; so `ord_E(π^*g) = max {s | g ∈ 𝔪_Z^s}`. If a rational `m`-canonical form `τ`
generates `ω_Y^{⊗m}` on an open neighbourhood of `η_Z`, then `ord_E(π^*τ) = m(c - 1)`. -/
@[mmp "lem_mmp_threefold_smooth_blowup_orders"]
public theorem ord_exceptionalPrimeDivisor_pullback_and_ordForm_pullback
    {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (hY : Mori.IsVariety k sY)
    (I : Y.IdealSheafData) (h : IsSmoothBlowup sY I) (hirr : IsIrreducible (I.support : Set Y))
    {c : ℕ}
    (hc : (c : ℕ∞) = codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (hc2 : 2 ≤ c) {d : ℕ} (hd : topologicalKrullDim Y = d) :
    haveI := hY.toIsIntegral
    haveI := smooth_of_isSmoothScheme h.1
    haveI : IsLocallyNoetherian Y := isLocallyNoetherian_of_smooth sY
    haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
    haveI := AlgebraicGeometry.isNormal_of_smooth sY
    haveI := isIntegral_blowUp_of_one_le_codimension I hirr
      (hc ▸ by exact_mod_cast (by omega : 1 ≤ c))
    haveI := isDominant_blowUpToBase I hirr (hc ▸ by exact_mod_cast (by omega : 1 ≤ c))
    haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
    haveI : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
    let E := exceptionalPrimeDivisor sY I h hirr (hc ▸ by exact_mod_cast (by omega : 1 ≤ c))
    (∀ g : Y.presheaf.stalk hirr.genericPoint, g ≠ 0 → ∀ s : ℕ,
      (s : ℤ) ≤ (blowUp I).ord (functionFieldMap (blowUpToBase I)
          (algebraMap (Y.presheaf.stalk hirr.genericPoint) Y.functionField g)) E.genericPoint ↔
        g ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk hirr.genericPoint) ^ s) ∧
    ∀ (m : ℕ) (τ : RationalPluriForms sY d m),
      (∃ U : Y.Opens, hirr.genericPoint ∈ U ∧ GeneratesOn (0 : QDivisor Y) m U τ) →
        Mori.PrimeDivisor.ordForm E (pullbackRationalPluriForms sY (blowUpToBase I) τ) =
          (m : ℤ) * ((c : ℤ) - 1) := by
  have hc1 : 1 ≤ c := by omega
  have hc1' : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) :=
    hc ▸ by exact_mod_cast hc1
  have := hY.toIsIntegral
  have : Smooth sY := smooth_of_isSmoothScheme h.1
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_smooth sY
  have : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  have := AlgebraicGeometry.isNormal_of_smooth sY
  have := isIntegral_blowUp_of_one_le_codimension I hirr hc1'
  have := isDominant_blowUpToBase I hirr hc1'
  have := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
  have : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
  have := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ sY)
  have := isIntegral_subscheme_of_isIrreducible sY I h.2 hirr
  have : IsIntegral (exceptionalIdeal I).subscheme := isIntegral_exceptionalDivisor sY I h hirr hc1'
  intro E
  set π := blowUpToBase I
  set ξ := E.genericPoint
  -- the generic point of `E` and its image
  have hξ : ξ = (exceptionalIdeal I).subschemeι (genericPoint (exceptionalIdeal I).subscheme) :=
    rfl
  have hEξ : IdealSheafData.stalk (I.comap π) ξ = maximalIdeal ((blowUp I).presheaf.stalk ξ) := by
    rw [hξ]
    exact IdealSheafData.stalk_subschemeι_genericPoint_eq_maximalIdeal (exceptionalIdeal I)
  obtain ⟨-, F', hF'id, -, hFimg⟩ :=
    isSmoothScheme_blowUp_and_exists_primeDivisor_exceptionalIdeal sY I h hirr hc1'
  have hsuppF : E.support = ((exceptionalIdeal I).support : Set (blowUp I)) := rfl
  have hsuppF' : F'.support = ((exceptionalIdeal I).support : Set (blowUp I)) := by
    simp only [AlgebraicGeometry.PrimeDivisor.support, hF'id]
  have hgenπ : IsGenericPoint (π ξ) (I.support : Set Y) := by
    change closure {π ξ} = _
    rw [← Set.image_singleton, π.isClosedMap.closure_image_eq_of_continuous π.continuous,
      ← AlgebraicGeometry.PrimeDivisor.support_eq_closure, hsuppF, ← hsuppF', hFimg]
  have hπξ : π ξ = I.subschemeι (genericPoint I.subscheme) :=
    hgenπ.eq (closure_subschemeι_genericPoint I)
  have hπη : π ξ = hirr.genericPoint :=
    hgenπ.eq (hirr.isGenericPoint_genericPoint_closure.trans I.support.isClosed.closure_eq)
  have hIξ : IdealSheafData.stalk I (π ξ) = maximalIdeal (Y.presheaf.stalk (π ξ)) := by
    rw [hπξ]
    exact IdealSheafData.stalk_subschemeι_genericPoint_eq_maximalIdeal I
  have := MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing E
  refine ⟨?_, ?_⟩
  · -- coordinates adapted to the centre, and a chart containing `ξ`
    obtain ⟨-, U, hU, hηU, n, x, hx, hcut⟩ := exists_isLocalCoordinates_genericPoint I sY h hirr hc
    obtain ⟨cd, hcdU, hηcd, x', hx', hrn, -, hcx⟩ := exists_blowupChartData I sY hU hηU x hx hcut
    obtain ⟨ℓ, hℓ⟩ := exists_mem_chart I cd (p := ξ) (by rw [hπξ]; exact hηcd)
    have hgen : ∀ y ∈ ((I.comap π).support : Set (blowUp I)), ξ ⤳ y := fun y hy => by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hy
    have hm0 : maximalIdeal ((blowUp I).presheaf.stalk ξ) ≠ ⊥ :=
      IsDiscreteValuationRing.not_a_field _
    have hpow := cd.comap_stalkMap_maximalIdeal_pow sY hcdU x' hx' hrn hcx ℓ hℓ hgen hIξ hEξ hm0
    suffices key : ∀ (y : Y) (hy : π ξ = y) (g : Y.presheaf.stalk y), g ≠ 0 → ∀ s : ℕ,
        (s : ℤ) ≤ (blowUp I).ord (functionFieldMap π
          (algebraMap (Y.presheaf.stalk y) Y.functionField g)) ξ ↔
          g ∈ maximalIdeal (Y.presheaf.stalk y) ^ s from key _ hπη
    rintro y rfl g hg s
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk π ξ g]
    have ha : (π.stalkMap ξ).hom g ≠ 0 := fun h0 =>
      (map_ne_zero (functionFieldMap π)).mpr
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hg))
        (by rw [MMP.Mori.functionFieldMap_algebraMap_stalk π ξ g, h0, map_zero])
    rw [natCast_le_ord_algebraMap_iff E ha s, ← hpow s, Ideal.mem_comap]
  · rintro m τ ⟨U, hηU, hτ⟩
    obtain ⟨σA, hσA, h0A, σB, hσB, h0B, g, hrel, hg, hord⟩ :=
      exists_topForms_rel_exceptional I sY h hirr hc hc1 hd E rfl
    let := stalkAlgebra sY (π ξ)
    let := functionFieldAlgebra sY
    have := isScalarTower_stalk_functionField sY (π ξ)
    -- the coefficient of `τ` at `π ξ` has order `0` along every prime divisor through `π ξ`,
    -- so it is a unit of the stalk
    have hu : ∀ Γ : MMP.Mori.PrimeDivisor Y, π ξ ∈ Γ.support →
        Y.ord (formCoeff (k := k) (Y.presheaf.stalk (π ξ)) hσA h0A
          (show PluriForms k Y.functionField d m from τ)) Γ.genericPoint = 0 := by
      intro Γ hΓ
      rw [← ordForm_eq_ord_formCoeff sY (π ξ) Γ hΓ hσA h0A τ]
      exact_mod_cast (by simpa using hτ.2 Γ ⟨π ξ, hΓ, hπη ▸ hηU⟩)
    obtain ⟨r, hr, hra⟩ := MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero
      (π ξ) (fun h0 => hτ.1 ((formCoeff_eq_zero_iff hσA h0A _).mp h0)) hu
    rw [ordForm_pullbackRationalPluriForms_eq sY π E hσA h0A hσB h0B g hrel hg hτ.1, hord, ← hra,
      MMP.Mori.functionFieldMap_algebraMap_stalk π ξ r,
      MMP.Mori.PrimeDivisor.ord_algebraMap_of_isUnit E (hr.map _), zero_add]

end MMP.Threefold.Resolution

end
