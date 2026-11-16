module

public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import MMP.AlgebraicGeometry.Divisor.EffectiveCartierDivisor

/-!
# Sections of the invertible sheaf `𝒪_X(D)` (Lazarsfeld §1.1)

Let `D` be a Cartier divisor on a scheme `X` and `𝒪_X(D) ⊆ 𝓜_X` its sheaf,
`MMP.CartierDivisor.sheaf D`. Its sections over `U` are the `σ ∈ Γ(U, 𝓜_X)` satisfying the
stalkwise condition `MMP.Intersection.lineBundleSections D U`
(`MMP.CartierDivisor.sectionVal_mem_lineBundleSections`). This file proves the properties of
`𝒪_X(D)` of Lazarsfeld §1.1 that are stated through its sections.

## Main definitions

* `MMP.CartierDivisor.invSection`: the local generator `g⁻¹` of `𝒪_X(D)` given by a local
  equation `g`.
* `MMP.CartierDivisor.sheafAddPrincipalIso`: `𝒪_X(D) ≅ 𝒪_X(D + div c)`, multiplication by `c⁻¹`.
* `MMP.CartierDivisor.ratioHom`: division by a regular section `s`, `L ⟶ 𝒪_X(div s)`.

## Main results

* `MMP.CartierDivisor.isTrivializingGenerator_invSection`: `𝒪_X(D)|_U = 𝒪_U · g⁻¹`.
* `MMP.CartierDivisor.isInvertibleModule_sheaf`: `𝒪_X(D)` is invertible.
* `MMP.CartierDivisor.sectionVal_sheafMulIso_hom`: `𝒪_X(D) ⊗ 𝒪_X(D') ≅ 𝒪_X(D + D')` sends
  `s ⊗ t` to `s t`.
* `MMP.CartierDivisor.isDivisorOfSection_canonicalSection`,
  `MMP.CartierDivisor.sectionVal_canonicalSection`,
  `MMP.CartierDivisor.mem_nonvanishingLocus_canonicalSection_iff`,
  `MMP.CartierDivisor.sheafMulIso_hom_canonicalSection`: properties of `s_D`.
* `MMP.CartierDivisor.nonempty_sheaf_iso_iff`: `𝒪_X(D₁) ≅ 𝒪_X(D₂) ↔ D₁ ≡_lin D₂`.
* `MMP.CartierDivisor.exists_sheaf_iso_of_isDivisorOfSection`: `𝒪_X(div s) ≅ L`.

## References

* [R. Lazarsfeld, *Positivity in Algebraic Geometry I*][lazarsfeld2004], §1.1.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry MonoidalCategory

namespace MMP.CartierDivisor

open MMP.Intersection
open MMP.CartierDivisorSheaf

variable {X : Scheme.{u}}

section Sheaf

attribute [local instance] AlgebraicGeometry.hasSheafifyAddCommGrpCat

/-- The value in `Γ(U, 𝓜_X)` of a section of `𝒪_X(D)` satisfies the stalkwise condition
`lineBundleSections D U`. -/
@[mmp "def_p01a_line_bundle_of_divisor"]
theorem sectionVal_mem_lineBundleSections {D : X.CartierDivisor} {U : X.Opens}
    (e : Γ(sheaf D, U)) : sectionVal e ∈ lineBundleSections D U :=
  (mem_lineBundleSections_iff_mem D U _).2 (show ↥((sheafSubmodule D).obj (op U)) from e).2

/-- The section of `𝒪_X(D)` over `U` with value `σ ∈ lineBundleSections D U`. -/
def sectionOfMem {D : X.CartierDivisor} {U : X.Opens} {σ : X.totalQuotientSheaf.obj.obj (op U)}
    (hσ : σ ∈ lineBundleSections D U) : Γ(sheaf D, U) :=
  (⟨σ, (mem_lineBundleSections_iff_mem D U σ).1 hσ⟩ : ↥((sheafSubmodule D).obj (op U)))

/-- The value of `sectionOfMem hσ` in `Γ(U, 𝓜_X)` is `σ`. -/
@[simp]
theorem sectionVal_sectionOfMem {D : X.CartierDivisor} {U : X.Opens}
    {σ : X.totalQuotientSheaf.obj.obj (op U)} (hσ : σ ∈ lineBundleSections D U) :
    sectionVal (sectionOfMem hσ) = σ := rfl

/-- The value of a sum of sections of `𝒪_X(D)` is the sum of their values. -/
theorem sectionVal_add {D : X.CartierDivisor} {U : X.Opens} (e e' : Γ(sheaf D, U)) :
    sectionVal (e + e') = sectionVal e + sectionVal e' := rfl

/-- The value of the zero section of `𝒪_X(D)` is `0`. -/
theorem sectionVal_zero {D : X.CartierDivisor} {U : X.Opens} :
    sectionVal (0 : Γ(sheaf D, U)) = 0 := rfl

/-- The value of `r • e` is the image of `r` in `Γ(U, 𝓜_X)` times the value of `e`. -/
theorem sectionVal_smul {D : X.CartierDivisor} {U : X.Opens} (r : Γ(X, U)) (e : Γ(sheaf D, U)) :
    sectionVal (r • e) = toTotalQuotient U r * sectionVal e := rfl

/-- The section `g⁻¹ ∈ Γ(U, 𝒪_X(D))` for a local equation `g` of `D` on `U`. -/
def invSection {D : X.CartierDivisor} {U : X.Opens}
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hg : IsLocalEquationOn D U g) :
    Γ(sheaf D, U) :=
  (⟨(↑g⁻¹ : X.totalQuotientSheaf.obj.obj (op U)), mem_inv hg⟩ :
    ↥((sheafSubmodule D).obj (op U)))

/-- The value of `invSection hg` in `Γ(U, 𝓜_X)` is `g⁻¹`. -/
@[simp]
theorem sectionVal_invSection {D : X.CartierDivisor} {U : X.Opens}
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hg : IsLocalEquationOn D U g) :
    sectionVal (invSection hg) = ↑g⁻¹ := rfl

/-- For a local equation `g` of `D` on `U`, the section `g⁻¹` trivializes `𝒪_X(D)` on `U`:
`r ↦ r g⁻¹|_V` is a bijection `Γ(V, 𝒪_X) → Γ(V, 𝒪_X(D))` for every open `V ⊆ U`. -/
@[mmp "lem_p01a_line_bundle_of_divisor_invertible"]
theorem isTrivializingGenerator_invSection {D : X.CartierDivisor} {U : X.Opens}
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hg : IsLocalEquationOn D U g) :
    IsTrivializingGenerator (sheaf D) U (invSection hg) := by
  intro V h
  have hval : ∀ r : Γ(X, V),
      sectionVal (r • (sheaf D).presheaf.map (homOfLE h).op (invSection hg)) =
        toTotalQuotient V r * resK h ↑g⁻¹ := fun r => rfl
  have hinv : resK h ↑g⁻¹ * resK h (g : X.totalQuotientSheaf.obj.obj (op U)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  refine ⟨fun r r' hrr' => ?_, fun σ => ?_⟩
  · have := congrArg (fun τ : Γ(sheaf D, V) =>
      sectionVal τ * resK h (g : X.totalQuotientSheaf.obj.obj (op U))) hrr'
    simp only [hval, mul_assoc, hinv, mul_one] at this
    exact injective_toTotalQuotient V this
  · obtain ⟨r, hr⟩ := (mem_iff hg h (sectionVal σ)).1
      (show ↥((sheafSubmodule D).obj (op V)) from σ).2
    exact ⟨r, sectionVal_injective ((hval r).trans hr)⟩

/-- `𝒪_X(D)` is an invertible `𝒪_X`-module. -/
@[mmp "lem_p01a_line_bundle_of_divisor_invertible"]
instance isInvertibleModule_sheaf (D : X.CartierDivisor) :
    Stacks.Ample.IsInvertibleModule X (sheaf D) :=
  (Stacks.SheafOfModules.Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one X
    (sheaf D)).2 inferInstance

/-- **A trivializing generator of `𝒪_X(D)` is the inverse of a local equation.** If
`e ∈ Γ(U, 𝒪_X(D))` trivializes `𝒪_X(D)` on `U`, then `e` is a unit of `Γ(U, 𝓜_X)` and `e⁻¹` is a
local equation of `D` on `U`. -/
theorem isLocalEquationOn_inv_of_isTrivializingGenerator {D : X.CartierDivisor} {U : X.Opens}
    {e : Γ(sheaf D, U)} (he : IsTrivializingGenerator (sheaf D) U e) :
    ∃ h : IsUnit (sectionVal e), IsLocalEquationOn D U h.unit⁻¹ := by
  have key : ∀ x ∈ U, ∃ (W : X.Opens) (i : W ⟶ U), x ∈ W ∧ ∃ (a : Γ(X, W)ˣ)
      (g : (X.totalQuotientSheaf.obj.obj (op W))ˣ), IsLocalEquationOn D W g ∧
        X.totalQuotientSheaf.obj.map i.op (sectionVal e) =
          toTotalQuotient W (a : Γ(X, W)) * ↑g⁻¹ := by
    intro x hx
    obtain ⟨W', hxW', g, hg⟩ := exists_isLocalEquationOn D x
    have hgV := isLocalEquationOn_resUnit (homOfLE (inf_le_right : U ⊓ W' ≤ W')) hg
    obtain ⟨a, ha⟩ := (mem_lineBundleSections_iff_of_isLocalEquationOn' hgV _).1
      (res_mem D (inf_le_left : U ⊓ W' ≤ U) (sectionVal_mem_lineBundleSections e))
    obtain ⟨b, hb⟩ := (he (U ⊓ W') inf_le_left).2 (invSection hgV)
    have hb' := congrArg sectionVal hb
    change toTotalQuotient (U ⊓ W') b *
      X.totalQuotientSheaf.obj.map (homOfLE (inf_le_left : U ⊓ W' ≤ U)).op (sectionVal e) =
        ↑(resUnit (homOfLE (inf_le_right : U ⊓ W' ≤ W')) g)⁻¹ at hb'
    rw [← ha, ← mul_assoc, ← map_mul] at hb'
    have hba : b * a = 1 := by
      apply injective_toTotalQuotient
      have := congrArg (· * (↑(resUnit (homOfLE (inf_le_right : U ⊓ W' ≤ W')) g) :
        X.totalQuotientSheaf.obj.obj (op (U ⊓ W')))) hb'
      simp only [mul_assoc, Units.inv_mul, mul_one] at this
      rw [this, map_one]
    refine ⟨U ⊓ W', homOfLE inf_le_left, ⟨hx, hxW'⟩, (IsUnit.of_mul_eq_one_right b hba).unit,
      _, hgV, ha.symm⟩
  have hunit : IsUnit (sectionVal e) := isUnit_of_locally _ fun x hx => by
    obtain ⟨W, i, hxW, a, g, -, heq⟩ := key x hx
    exact ⟨W, i, hxW, by rw [heq]; exact ((Units.map _ a).isUnit).mul (g⁻¹).isUnit⟩
  refine ⟨hunit, isLocalEquationOn_of_locally fun x hx => ?_⟩
  obtain ⟨W, i, hxW, a, g, hg, heq⟩ := key x hx
  refine ⟨W, i, hxW, ?_⟩
  have h1 : resUnit i hunit.unit = Units.map (toTotalQuotient W).toMonoidHom a * g⁻¹ :=
    Units.ext (by simpa using heq)
  have h2 : resUnit i hunit.unit⁻¹ = Units.map (toTotalQuotient W).toMonoidHom a⁻¹ * g := by
    have h3 : resUnit i hunit.unit⁻¹ = (resUnit i hunit.unit)⁻¹ := map_inv _ _
    rw [h3, h1, mul_inv_rev, inv_inv, ← map_inv, mul_comm]
  rw [h2]
  exact hg.units_mul _

/-! #### `D ↦ 𝒪_X(D)` is a homomorphism (Lazarsfeld (1.2)) -/

/-- **Lazarsfeld (1.2).** The isomorphism `𝒪_X(D) ⊗ 𝒪_X(D') ≅ 𝒪_X(D + D')` is multiplication in
`𝓜_X`: it sends `s ⊗ t` to `s t`. -/
@[mmp "lem_p01a_line_bundle_of_divisor_homomorphism"]
theorem sectionVal_sheafMulIso_hom (D D' : X.CartierDivisor) {V : X.Opens}
    (s : Γ(sheaf D, V)) (t : Γ(sheaf D', V)) :
    sectionVal ((sheafMulIso D D').hom.val.app (op V) (tensorSection s t)) =
      sectionVal s * sectionVal t :=
  sectionVal_sheafMulHom_tmul s t

/-! #### The canonical section `s_D` of an effective divisor -/

/-- **Lazarsfeld §1.1.A.** The section `s_D = 1 ∈ Γ(X, 𝒪_X(D))` of an effective divisor
(`MMP.CartierDivisor.canonicalSection`) is `1 ∈ Γ(X, 𝓜_X)`. -/
@[simp, mmp "lem_p01a_effective_divisor_canonical_section"]
theorem sectionVal_canonicalSection (D : X.CartierDivisor) (hD : IsEffective D) :
    sectionVal (canonicalSection D hD) = 1 := rfl

/-- The restriction of `s_D` to any open `U` has value `1 ∈ Γ(U, 𝓜_X)`. -/
@[mmp "lem_p01a_effective_divisor_canonical_section"]
theorem sectionVal_canonicalSection_res (D : X.CartierDivisor) (hD : IsEffective D)
    {U : X.Opens} :
    sectionVal ((sheaf D).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (canonicalSection D hD)) = 1 := by
  change resK (le_top : U ≤ ⊤) 1 = 1
  rw [map_one]

/-- If `s_D|_U = r e` for a trivializing generator `e`, then `r` is a unit of `𝓜_X` and a local
equation of `D` on `U`. -/
@[mmp "lem_p01a_effective_divisor_canonical_section"]
theorem exists_isLocalEquationOn_of_canonicalSection_eq_smul {D : X.CartierDivisor}
    (hD : IsEffective D) {U : X.Opens} {e : Γ(sheaf D, U)}
    (he : IsTrivializingGenerator (sheaf D) U e) {r : Γ(X, U)}
    (hr : (sheaf D).presheaf.map (homOfLE le_top).op (canonicalSection D hD) = r • e) :
    ∃ h : IsUnit (toTotalQuotient U r), IsLocalEquationOn D U h.unit := by
  obtain ⟨hu, hloc⟩ := isLocalEquationOn_inv_of_isTrivializingGenerator he
  have h1 : toTotalQuotient U r * sectionVal e = 1 := by
    have := congrArg sectionVal hr
    rw [sectionVal_canonicalSection_res] at this
    exact this.symm
  have hrU : IsUnit (toTotalQuotient U r) := IsUnit.of_mul_eq_one _ h1
  refine ⟨hrU, ?_⟩
  have : hrU.unit = hu.unit⁻¹ := eq_inv_of_mul_eq_one_left (Units.ext (by simpa using h1))
  rw [this]
  exact hloc

/-- **Lazarsfeld §1.1.A.** For effective `D`, `s_D` is a regular section of `𝒪_X(D)` and
`div(s_D) = D`. -/
@[mmp "lem_p01a_effective_divisor_canonical_section"]
theorem isDivisorOfSection_canonicalSection (D : X.CartierDivisor) (hD : IsEffective D) :
    IsDivisorOfSection (sheaf D) (canonicalSection D hD) D := by
  refine ⟨fun U e he r hr x hx => ?_, hD,
    fun U e he r hr => exists_isLocalEquationOn_of_canonicalSection_eq_smul hD he hr⟩
  obtain ⟨h, -⟩ := exists_isLocalEquationOn_of_canonicalSection_eq_smul hD he hr
  exact germ_mem_nonZeroDivisors_of_isUnit h x hx

/-- **Lazarsfeld §1.1.A.** For effective `D`, `s_D` is a regular section of `𝒪_X(D)`. -/
@[mmp "lem_p01a_effective_divisor_canonical_section"]
theorem isRegularSection_canonicalSection (D : X.CartierDivisor) (hD : IsEffective D) :
    IsRegularSection (sheaf D) (canonicalSection D hD) :=
  (isDivisorOfSection_canonicalSection D hD).1

/-- **Lazarsfeld §1.1.A.** For effective `D`, `s_D(x) ≠ 0` (the germ of `s_D` is not in
`𝔪_x 𝒪_X(D)_x`) exactly for `x ∉ Supp D`. -/
@[mmp "lem_p01a_effective_divisor_canonical_section"]
theorem mem_nonvanishingLocus_canonicalSection_iff (D : X.CartierDivisor) (hD : IsEffective D)
    (x : X) :
    x ∈ Stacks.Ample.nonvanishingLocus (sheaf D) (canonicalSection D hD) ↔
      x ∉ cartierSupport D := by
  obtain ⟨V, hV, htriv⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) X.ringCatSheaf.2 (sheaf D)
  obtain ⟨z, hz⟩ : ∃ z : X, x ∈ V z := Opens.mem_iSup.mp (hV ▸ Opens.mem_top x)
  obtain ⟨t⟩ := htriv z
  erw [Stacks.NonvanishingOpen.mem_nonvanishingLocus_iff_isUnit t _ hz]
  have hsV := Stacks.NonvanishingOpen.eq_triv_smul_basis t
    ((sheaf D).presheaf.map (homOfLE le_top).op (canonicalSection D hD))
  obtain ⟨h, hloc⟩ :=
    exists_isLocalEquationOn_of_canonicalSection_eq_smul hD (isTrivializingGenerator_basis t) hsV
  exact (notMem_cartierSupport_iff_isUnit_germ h hloc hz).symm

/-- **Lazarsfeld §1.1.A.** For effective `D`, `D'`, `s_D s_{D'} = s_{D+D'}` under
`𝒪_X(D) ⊗ 𝒪_X(D') ≅ 𝒪_X(D + D')`. -/
@[mmp "lem_p01a_effective_divisor_canonical_section"]
theorem sheafMulIso_hom_canonicalSection {D D' : X.CartierDivisor} (hD : IsEffective D)
    (hD' : IsEffective D') :
    (sheafMulIso D D').hom.val.app (op ⊤)
        (tensorSection (canonicalSection D hD) (canonicalSection D' hD')) =
      canonicalSection (D + D') (hD.add hD') :=
  sectionVal_injective (by
    erw [sectionVal_sheafMulIso_hom]
    exact one_mul _)

/-! #### Line bundles of linearly equivalent divisors -/

/-- Multiplication by `c⁻¹` on sections, `Γ(V, 𝒪_X(D)) ≃ Γ(V, 𝒪_X(D + div c))`. -/
def sheafAddPrincipalEquiv (D : X.CartierDivisor) (c : (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ)
    (V : X.Opens) :
    (sheaf D).val.obj (op V) ≃ₗ[X.ringCatSheaf.obj.obj (op V)]
      (sheaf (D + principalDivisor c)).val.obj (op V) where
  toFun σ := sectionOfMem
    (mul_mem_lineBundleSections_add_principalDivisor c (sectionVal_mem_lineBundleSections σ))
  invFun τ := sectionOfMem
    (mul_mem_lineBundleSections_of_add_principalDivisor c (sectionVal_mem_lineBundleSections τ))
  map_add' σ τ := sectionVal_injective (mul_add (R := X.totalQuotientSheaf.obj.obj (op V)) _ _ _)
  map_smul' r σ := sectionVal_injective (mul_left_comm _ _ _)
  left_inv σ := sectionVal_injective (by
    change X.totalQuotientSheaf.obj.map (homOfLE le_top).op _ *
      (X.totalQuotientSheaf.obj.map (homOfLE le_top).op _ * _) = _
    rw [← mul_assoc, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, one_mul])
  right_inv τ := sectionVal_injective (by
    change X.totalQuotientSheaf.obj.map (homOfLE le_top).op _ *
      (X.totalQuotientSheaf.obj.map (homOfLE le_top).op _ * _) = _
    rw [← mul_assoc, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, one_mul])

/-- Multiplication by `c⁻¹` is an isomorphism `𝒪_X(D) ≅ 𝒪_X(D + div c)`. -/
def sheafAddPrincipalIso (D : X.CartierDivisor)
    (c : (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ) :
    sheaf D ≅ sheaf (D + principalDivisor c) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V => (sheafAddPrincipalEquiv D c V.unop).toModuleIso)
      (fun V W i => by
        refine ModuleCat.hom_ext (LinearMap.ext fun σ => sectionVal_injective ?_)
        change X.totalQuotientSheaf.obj.map (homOfLE le_top).op
            (↑c⁻¹ : X.totalQuotientSheaf.obj.obj (op ⊤)) *
              X.totalQuotientSheaf.obj.map i (sectionVal σ) =
          X.totalQuotientSheaf.obj.map i (X.totalQuotientSheaf.obj.map (homOfLE le_top).op
            (↑c⁻¹ : X.totalQuotientSheaf.obj.obj (op ⊤)) * sectionVal σ)
        rw [map_mul]
        congr 1
        exact (totalQuotient_map_map (homOfLE le_top) i.unop _).symm))

section Hom

variable {D₁ D₂ : X.CartierDivisor} (φ : sheaf D₁ ⟶ sheaf D₂)

/-- For a local equation `g` of `D₁` on `W`, the section `φ(g⁻¹) g ∈ Γ(W, 𝓜_X)`. -/
def homFactor {W : X.Opens} {g : (X.totalQuotientSheaf.obj.obj (op W))ˣ}
    (hg : IsLocalEquationOn D₁ W g) : X.totalQuotientSheaf.obj.obj (op W) :=
  sectionVal (φ.val.app (op W) (invSection hg)) * ↑g

/-- On an open `V` inside an open `W` where `g` is a local equation of `D₁`, a morphism
`φ : 𝒪_X(D₁) ⟶ 𝒪_X(D₂)` is multiplication by `φ(g⁻¹) g`. -/
theorem sectionVal_hom_app_eq {W : X.Opens} {g : (X.totalQuotientSheaf.obj.obj (op W))ˣ}
    (hg : IsLocalEquationOn D₁ W g) {V : X.Opens} (h : V ≤ W) (σ : Γ(sheaf D₁, V)) :
    sectionVal (φ.val.app (op V) σ) =
      X.totalQuotientSheaf.obj.map (homOfLE h).op (homFactor φ hg) * sectionVal σ := by
  obtain ⟨a, ha⟩ := (mem_lineBundleSections_iff_of_isLocalEquationOn hg h (sectionVal σ)).1
    (sectionVal_mem_lineBundleSections σ)
  have hσ : σ = a • (sheaf D₁).presheaf.map (homOfLE h).op (invSection hg) :=
    sectionVal_injective ha.symm
  have hφ : φ.val.app (op V) σ = a • (sheaf D₂).presheaf.map (homOfLE h).op
      (φ.val.app (op W) (invSection hg)) := by
    rw [hσ]
    refine ((φ.val.app (op V)).hom.map_smul a _).trans ?_
    congr 1
    exact PresheafOfModules.naturality_apply φ.val (homOfLE h).op _
  rw [hφ]
  change toTotalQuotient V a * X.totalQuotientSheaf.obj.map (homOfLE h).op
    (sectionVal (φ.val.app (op W) (invSection hg))) = _
  rw [homFactor, map_mul, ← ha, smul_totalQuotient_def]
  have hinv : X.totalQuotientSheaf.obj.map (homOfLE h).op
      (↑g : X.totalQuotientSheaf.obj.obj (op W)) *
      X.totalQuotientSheaf.obj.map (homOfLE h).op (↑g⁻¹ : X.totalQuotientSheaf.obj.obj (op W)) =
        1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  linear_combination (-(toTotalQuotient V a * X.totalQuotientSheaf.obj.map (homOfLE h).op
    (sectionVal (φ.val.app (op W) (invSection hg))))) * hinv

/-- For local equations `g` on `W` and `g'` on `W'` of `D₁`, the sections `φ(g⁻¹) g` and
`φ(g'⁻¹) g'` agree on `W ⊓ W'`. -/
theorem homFactor_res_eq {W W' : X.Opens} {g : (X.totalQuotientSheaf.obj.obj (op W))ˣ}
    {g' : (X.totalQuotientSheaf.obj.obj (op W'))ˣ} (hg : IsLocalEquationOn D₁ W g)
    (hg' : IsLocalEquationOn D₁ W' g') :
    X.totalQuotientSheaf.obj.map (homOfLE (inf_le_left : W ⊓ W' ≤ W)).op (homFactor φ hg) =
      X.totalQuotientSheaf.obj.map (homOfLE (inf_le_right : W ⊓ W' ≤ W')).op
        (homFactor φ hg') := by
  have h1 := sectionVal_hom_app_eq φ hg (inf_le_left : W ⊓ W' ≤ W)
    ((sheaf D₁).presheaf.map (homOfLE (inf_le_right : W ⊓ W' ≤ W')).op (invSection hg'))
  have h2 := sectionVal_hom_app_eq φ hg' (inf_le_right : W ⊓ W' ≤ W')
    ((sheaf D₁).presheaf.map (homOfLE (inf_le_right : W ⊓ W' ≤ W')).op (invSection hg'))
  have hu : IsUnit (sectionVal ((sheaf D₁).presheaf.map
      (homOfLE (inf_le_right : W ⊓ W' ≤ W')).op (invSection hg'))) :=
    (g'⁻¹).isUnit.map (X.totalQuotientSheaf.obj.map (homOfLE (inf_le_right : W ⊓ W' ≤ W')).op).hom
  exact hu.mul_right_cancel (h1.symm.trans h2)

/-- **A morphism `𝒪_X(D₁) ⟶ 𝒪_X(D₂)` is multiplication by a global section of `𝓜_X`**: there is
`c ∈ Γ(X, 𝓜_X)` with `c|_W = φ(g⁻¹) g` for every local equation `g` of `D₁` on an open `W`. -/
theorem exists_homFactor_eq : ∃ c : X.totalQuotientSheaf.obj.obj (op ⊤),
    ∀ {W : X.Opens} {g : (X.totalQuotientSheaf.obj.obj (op W))ˣ} (hg : IsLocalEquationOn D₁ W g),
      X.totalQuotientSheaf.obj.map (homOfLE le_top).op c = homFactor φ hg := by
  choose W hxW g hg using exists_isLocalEquationOn D₁
  have hcover : (⊤ : X.Opens) ≤ iSup W := fun x _ => Opens.mem_iSup.mpr ⟨x, hxW x⟩
  obtain ⟨c, hc, -⟩ := X.totalQuotientSheaf.existsUnique_gluing' W ⊤ (fun _ => homOfLE le_top)
    hcover (fun x => homFactor φ (hg x)) (fun x y => homFactor_res_eq φ (hg x) (hg y))
  refine ⟨c, fun {V g'} hg' => TopCat.Sheaf.eq_of_locally_eq' X.totalQuotientSheaf
    (fun x : X => V ⊓ W x) V (fun x => homOfLE inf_le_left)
    (fun y hy => Opens.mem_iSup.mpr ⟨y, hy, hxW y⟩) _ _ fun x => ?_⟩
  have := homFactor_res_eq φ hg' (hg x)
  change X.totalQuotientSheaf.obj.map (homOfLE (inf_le_left : V ⊓ W x ≤ V)).op _ =
    X.totalQuotientSheaf.obj.map (homOfLE (inf_le_left : V ⊓ W x ≤ V)).op _
  rw [this, ← hc x, totalQuotient_map_map, totalQuotient_map_map]
  rfl

end Hom

/-- If `𝒪_X(D₁) ≅ 𝒪_X(D₂)`, then `D₁` and `D₂` are linearly equivalent. -/
@[mmp "lem_p01a_line_bundle_iso_iff_linearly_equivalent"]
theorem linearlyEquivalent_of_sheaf_iso {D₁ D₂ : X.CartierDivisor} (φ : sheaf D₁ ≅ sheaf D₂) :
    LinearlyEquivalent D₁ D₂ := by
  obtain ⟨c, hc⟩ := exists_homFactor_eq φ.hom
  choose W hxW g hg using exists_isLocalEquationOn D₁
  have hgen : ∀ x, IsTrivializingGenerator (sheaf D₂) (W x)
      (φ.hom.val.app (op (W x)) (invSection (hg x))) := fun x =>
    (isTrivializingGenerator_invSection (hg x)).map_iso φ
  choose hu hloc using fun x => isLocalEquationOn_inv_of_isTrivializingGenerator (hgen x)
  have hcu : IsUnit c := isUnit_of_locally c fun x _ =>
    ⟨W x, homOfLE le_top, hxW x, by rw [hc (hg x)]; exact (hu x).mul (g x).isUnit⟩
  have key : ∀ x, IsLocalEquationOn (D₁ + principalDivisor hcu.unit⁻¹) (W x) (hu x).unit⁻¹ :=
    fun x => by
      have := (hg x).mul (isLocalEquationOn_principalDivisor_res hcu.unit⁻¹ (W x))
      convert this using 1
      have e : resUnit (homOfLE le_top) hcu.unit = (hu x).unit * g x :=
        Units.ext (by simpa [homFactor] using hc (hg x))
      have h3 : resUnit (homOfLE (le_top : W x ≤ ⊤)) hcu.unit⁻¹ =
          (resUnit (homOfLE le_top) hcu.unit)⁻¹ := map_inv _ _
      rw [h3, e, mul_inv, mul_left_comm, mul_inv_cancel, mul_one]
  have hD := eq_of_isLocalEquationOn W
    (eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hxW x⟩) _ key hloc
  refine mem_principalSubgroup_iff.2 ⟨hcu.unit, ?_⟩
  rw [← hD, Intersection.principalDivisor_inv]
  abel

/-- If `D₁` and `D₂` are linearly equivalent, then `𝒪_X(D₁) ≅ 𝒪_X(D₂)`. -/
theorem nonempty_iso_of_linearlyEquivalent {D₁ D₂ : X.CartierDivisor}
    (h : LinearlyEquivalent D₁ D₂) : Nonempty (sheaf D₁ ≅ sheaf D₂) := by
  obtain ⟨f, hf⟩ := mem_principalSubgroup_iff.1 h
  have : D₁ = D₂ + principalDivisor f := by rw [hf]; abel
  subst this
  exact ⟨(sheafAddPrincipalIso D₂ f).symm⟩

/-- **Lazarsfeld §1.1.A, p. 10.** `𝒪_X(D₁) ≅ 𝒪_X(D₂)` if and only if `D₁ ≡_lin D₂`. -/
@[mmp "lem_p01a_line_bundle_iso_iff_linearly_equivalent"]
theorem nonempty_sheaf_iso_iff (D₁ D₂ : X.CartierDivisor) :
    Nonempty (sheaf D₁ ≅ sheaf D₂) ↔ LinearlyEquivalent D₁ D₂ :=
  ⟨fun ⟨φ⟩ => linearlyEquivalent_of_sheaf_iso φ, nonempty_iso_of_linearlyEquivalent⟩

/-! #### The line bundle of the divisor of a section -/

section DivisorOfSection

variable {L : X.Modules} {s : Γ(L, ⊤)} {D : X.CartierDivisor}

/-- Division by the regular section `s`: the morphism `L ⟶ 𝒪_X(div s)`, `t ↦ t / s`. -/
def ratioHom [Stacks.Ample.IsInvertibleModule X L]
    (hs : IsDivisorOfSection L s D) : L ⟶ sheaf D :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    { app := fun V => ModuleCat.ofHom
        { toFun := fun t => sectionOfMem ((isRatio_ratio hs (V := V.unop) t).mem hs)
          map_add' := fun t t' => sectionVal_injective
            ((isRatio_ratio hs (V := V.unop) (t + t')).unique hs
              ((isRatio_ratio hs _).add (isRatio_ratio hs _)))
          map_smul' := fun a t => sectionVal_injective
            ((isRatio_ratio hs (V := V.unop) (a • t)).unique hs ((isRatio_ratio hs _).smul a)) }
      naturality := fun {V W} i => by
        refine ModuleCat.hom_ext (LinearMap.ext fun t => sectionVal_injective ?_)
        exact ((isRatio_ratio hs (V := W.unop) (L.presheaf.map (homOfLE i.unop.le).op t)).unique
          hs ((isRatio_ratio hs (V := V.unop) t).res i.unop.le)) }

/-- The value of `(ratioHom hs)(t)` in `Γ(V, 𝓜_X)` is the ratio `t / s`. -/
theorem sectionVal_ratioHom_app [Stacks.Ample.IsInvertibleModule X L]
    (hs : IsDivisorOfSection L s D) {V : X.Opens} (t : Γ(L, V)) :
    sectionVal ((ratioHom hs).val.app (op V) t) = ratio hs t := rfl

/-- `(ratioHom hs)(t) = σ` if and only if the value of `σ` is the ratio of `t` by `s`. -/
theorem ratioHom_app_eq_iff [Stacks.Ample.IsInvertibleModule X L]
    (hs : IsDivisorOfSection L s D) {V : X.Opens} (t : Γ(L, V))
    (σ : Γ(sheaf D, V)) : (ratioHom hs).val.app (op V) t = σ ↔ IsRatio L s t (sectionVal σ) :=
  ⟨fun h => h ▸ isRatio_ratio hs t,
    fun h => sectionVal_injective ((isRatio_ratio hs t).unique hs h)⟩

/-- Division by a regular section `s` with `div(s) = D` is an isomorphism `L ≅ 𝒪_X(D)`. -/
@[mmp "lem_p01a_divisor_of_section_line_bundle"]
instance isIso_ratioHom [Stacks.Ample.IsInvertibleModule X L]
    (hs : IsDivisorOfSection L s D) : IsIso (ratioHom hs) := by
  have hinj : ∀ V : (X.Opens)ᵒᵖ, Function.Injective ((ratioHom hs).val.app V) := by
    intro V t t' htt
    have h0 : (ratioHom hs).val.app V (t - t') = 0 := by rw [map_sub, htt, sub_self]
    have hρ := (ratioHom_app_eq_iff hs (V := V.unop) (t - t') 0).1 h0
    rw [← sub_eq_zero]
    choose U hU e he r b hxU hr hb using
      fun x : V.unop => exists_trivializingData (s := s) (t - t') x.2
    refine TopCat.Sheaf.eq_of_locally_eq' ((SheafOfModules.toSheaf X.ringCatSheaf).obj L) U
      V.unop (fun x => homOfLE (hU x)) (fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxU ⟨y, hy⟩⟩)
      _ _ fun x => ?_
    have := hρ _ (hU x) (e x) (he x) (r x) (b x) (hr x) (hb x)
    rw [sectionVal_zero, map_zero, zero_mul] at this
    have hb0 : b x = 0 := injective_toTotalQuotient _ (by rw [← this, map_zero])
    change L.presheaf.map (homOfLE (hU x)).op (t - t') = L.presheaf.map (homOfLE (hU x)).op 0
    rw [hb x, hb0, zero_smul, map_zero]
  have hsurj : TopCat.Presheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf X.ringCatSheaf).map (ratioHom hs)).hom := by
    refine (TopCat.Presheaf.isLocallySurjective_iff _).2 fun V σ x hx => ?_
    obtain ⟨U, hU, e, he, r, b, hxU, hr, -⟩ := exists_trivializingData (s := s) (0 : Γ(L, V)) hx
    obtain ⟨hu, hloc⟩ := hs.2.2 U e he r hr
    obtain ⟨a, ha⟩ := (mem_lineBundleSections_iff_of_isLocalEquationOn' hloc _).1
      (res_mem D hU (sectionVal_mem_lineBundleSections σ))
    refine ⟨U, hU, ⟨a • e, ?_⟩, hxU⟩
    refine (ratioHom_app_eq_iff hs (a • e) _).2 fun U' hU' e' he' r' b' hr' hb' => ?_
    have hcr := toTotalQuotient_cross_mul_eq (s := s) (a • e) (le_refl U) hU' hU' (le_refl U') he
      hr (modules_map_id L _) hr' hb'
    rw [totalQuotient_map_id, totalQuotient_map_id] at hcr
    have hτ : X.totalQuotientSheaf.obj.map (homOfLE hU).op (sectionVal σ) *
        toTotalQuotient U r = toTotalQuotient U a := by
      rw [← ha, mul_assoc, hu.val_inv_mul, mul_one]
    have h1 := congrArg (X.totalQuotientSheaf.obj.map (homOfLE hU').op) hτ
    rw [map_mul] at h1
    exact mul_eq_of_mul_eq_of_isUnit (hu.map _) h1 hcr.symm
  have hiso := (Sheaf.isLocallyBijective_iff_isIso
    ((SheafOfModules.toSheaf X.ringCatSheaf).map (ratioHom hs))).mp
      ⟨Presheaf.isLocallyInjective_of_injective _ _ hinj, hsurj⟩
  have hrefl : (SheafOfModules.toSheaf X.ringCatSheaf).ReflectsIsomorphisms := inferInstance
  exact @isIso_of_reflects_iso _ _ _ _ _ _ (ratioHom hs) (SheafOfModules.toSheaf X.ringCatSheaf)
    hiso hrefl

/-- **Divisor of a section and its line bundle.** If `s` is a regular section of a line bundle `L`
with divisor `div(s) = D`, then `𝒪_X(D) ≅ L` by an isomorphism carrying `s_D` to `s`. -/
@[mmp "lem_p01a_divisor_of_section_line_bundle"]
theorem exists_sheaf_iso_of_isDivisorOfSection (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {s : Γ(L, ⊤)} {D : X.CartierDivisor}
    (hs : IsDivisorOfSection L s D) :
    ∃ φ : sheaf D ≅ L, φ.hom.val.app (op ⊤) (canonicalSection D hs.2.1) = s := by
  refine ⟨(asIso (ratioHom hs)).symm, ?_⟩
  have h1 : (ratioHom hs).val.app (op ⊤) s = canonicalSection D hs.2.1 :=
    (ratioHom_app_eq_iff hs s _).2 isRatio_one
  rw [← h1]
  exact congrArg (fun f : L ⟶ L => (f.val.app (op ⊤)).hom (s : L.val.obj (op ⊤)))
    (IsIso.hom_inv_id (ratioHom hs))

end DivisorOfSection

end Sheaf

end MMP.CartierDivisor
