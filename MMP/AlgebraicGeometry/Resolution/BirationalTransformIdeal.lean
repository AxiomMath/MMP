/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Basic

/-!
# Birational transforms of ideals along smooth blow-ups are ideal sheaves

Let `X` be a smooth scheme over a field, `Z ⊆ X` a smooth closed subscheme with irreducible
components `Z_1, …, Z_t`, `π : B_ZX → X` the blow-up and `F_j = π⁻¹(Z_j)`. For an ideal sheaf
`I ⊆ 𝒪_X` and natural numbers `a_j ≤ ord_{Z_j} I`, the pull-back `π^*I` is divisible by the
invertible ideal `𝒪_{B_ZX}(-∑_j a_jF_j) = ∏_j I_{F_j}^{a_j}`, so that
`𝒪_{B_ZX}(∑_j a_jF_j)·π^*I ⊆ 𝒪_{B_ZX}` (Kollár 3.48, 3.60). With all `a_j = m` this says that
the first entry of the birational transform `π⁻¹_{Z*}(I, m)` of a marked ideal is an ideal sheaf,
and with `a_j = ord_{Z_j} I` that the controlled transform `π⁻¹_{Z*}I` is one (Kollár 3.58).

## Main definitions

* `MMP.Resolution.exceptionalDivisorIdeal`: the ideal `𝒪_{B_ZX}(-∑_j a_jF_j) = ∏_j I_{F_j}^{a_j}`.

## Main results

* `MMP.Resolution.isEffectiveCartierDivisor_exceptionalDivisorIdeal`: it is invertible.
* `MMP.Resolution.comap_le_exceptionalDivisorIdeal`: `π^*I ⊆ 𝒪_{B_ZX}(-∑_j a_jF_j)` when
  `ord_{Z_j} I ≥ a_j` for all `j`.
* `MMP.Resolution.idealColon_comap_mul_exceptionalDivisorIdeal`: then
  `(π^*I : 𝒪(-∑_j a_jF_j)) · 𝒪(-∑_j a_jF_j) = π^*I`.
* The cases `a_j = m` and `a_j = ord_{Z_j} I` are the theorems
  `MMP.Resolution.MarkedIdeal.birationalTransform_mul_eq` and
  `MMP.Resolution.controlledTransform_mul_eq`, registered here.

## Implementation notes

Ideal sheaves are subsheaves of `𝒪`, so a twist `𝒪(∑_j a_jF_j)·π^*I` is represented by the ideal
quotient `(π^*I : 𝒪(-∑_j a_jF_j))` (`MMP.Resolution.idealColon`), which is always an ideal sheaf;
the content of "`𝒪(∑_j a_jF_j)·π^*I ⊆ 𝒪_{B_ZX}`" is that this quotient multiplied back by the
invertible ideal `𝒪(-∑_j a_jF_j)` returns `π^*I`, i.e. that `π^*I ⊆ 𝒪(-∑_j a_jF_j)`. This is
what is stated.

The proof is stalkwise: at a point `y` of `B_ZX` over `x ∈ Z`, exactly one component `Z_j`
passes through `x`, its reduced ideal has stalk `I_{Z,x}` at `x`, and `ord_{Z_j} I ≥ a_j` gives
`I_x ⊆ I_{Z,x}^{a_j}`; pulling back, `(π^*I)_y ⊆ (π^*I_Z)_y^{a_j} = 𝒪(-∑_j a_jF_j)_y`. This
avoids the divisorial part `Div(π^*I)` and the reduction to one component used in the source, and
it needs neither that the components of `Z` have codimension `≥ 1` nor that `I` be nonzero on the
components of `X`; those hypotheses are dropped. Finite type and quasi-compactness of `X` over
the field are kept, to make the product over the components of `Z` finite.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.48, 3.58, 3.60]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Resolution

variable {X : Scheme.{u}}

/-- The ideal `𝒪_{B_ZX}(-∑_j a_jF_j) = ∏_j I_{F_j}^{a_j}` on the blow-up `π : B_ZX → X`, where
`F_j = π⁻¹(Z_j)` for the irreducible components `Z_j` of `Z` with their reduced structure and
`a_j = a Z_j`. -/
def exceptionalDivisorIdeal (Z : X.IdealSheafData) (a : componentsOf (Z.support : Set X) → ℕ) :
    (blowUp Z).IdealSheafData :=
  ∏ᶠ W : componentsOf (Z.support : Set X),
    (componentsFamily (Z.support : Set X) W).comap (blowUpToBase Z) ^ a W

/-- The controlled-transform divisor ideal of `I` is `exceptionalDivisorIdeal Z a` with
`a_j = ord_{Z_j} I`, i.e. `𝒪_{B_ZX}(-∑_j ord_{Z_j}(I) F_j)`. -/
theorem controlledTransformDivisorIdeal_eq_exceptionalDivisorIdeal (Z I : X.IdealSheafData) :
    controlledTransformDivisorIdeal Z I =
      exceptionalDivisorIdeal Z fun W => (orderAlong I W.2.1.1).toNat :=
  rfl

/-- Stalks of `𝒪(-∑_j a_jF_j)`: at `y ∈ B_ZX` it is `(π^*I_Z)_y^n`, where `n = a_j` for the
component `Z_j` through `π y` if there is one; and `I_{π y} ⊆ I_{Z, π y}^n` when
`ord_{Z_j} I ≥ a_j` for all `j`; and if `π y ∈ Z` then `n = a_j` for some `j`. -/
theorem exists_stalk_exceptionalDivisorIdeal_eq {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (a : componentsOf (Z.support : Set X) → ℕ) (y : blowUp Z) :
    ∃ n : ℕ, IdealSheafData.stalk (exceptionalDivisorIdeal Z a) y =
        IdealSheafData.stalk (Z.comap (blowUpToBase Z)) y ^ n ∧
      (∀ I : X.IdealSheafData, (∀ W, (a W : ℕ∞) ≤ orderAlong I W.2.1.1) →
        IdealSheafData.stalk I (blowUpToBase Z y) ≤
          IdealSheafData.stalk Z (blowUpToBase Z y) ^ n) ∧
      (blowUpToBase Z y ∈ (Z.support : Set X) → ∃ W, n = a W) := by
  classical
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  have : Finite (componentsOf (Z.support : Set X)) :=
    (finite_componentsOf Z.support.2).to_subtype
  let := Fintype.ofFinite (componentsOf (Z.support : Set X))
  set x := blowUpToBase Z y
  have hD : IdealSheafData.stalk (exceptionalDivisorIdeal Z a) y =
      ∏ W : componentsOf (Z.support : Set X), Ideal.map ((blowUpToBase Z).stalkMap y).hom
        (IdealSheafData.stalk (componentsFamily (Z.support : Set X) W) x) ^ a W := by
    unfold exceptionalDivisorIdeal
    rw [finprod_eq_prod_of_fintype, stalk_prod]
    exact Finset.prod_congr rfl fun W _ => by
      rw [IdealSheafData.stalk_pow, IdealSheafData.stalk_comap]
  by_cases hx : x ∈ (Z.support : Set X)
  · obtain ⟨W0, hW0, hxW0, huniq, hstalk, -⟩ := exists_component_through sX hX Z hZ ⊥ x hx
    refine ⟨a ⟨W0, hW0⟩, ?_, fun I ha => ?_, fun _ => ⟨_, rfl⟩⟩
    swap
    · obtain ⟨W1, hW1, hxW1, -, -, hle⟩ := exists_component_through sX hX Z hZ I x hx
      have h01 : W1 = W0 := huniq W1 hW1 hxW1
      subst h01
      exact hle _ (ha ⟨W1, hW1⟩)
    rw [hD, Finset.prod_eq_single (⟨W0, hW0⟩ : componentsOf (Z.support : Set X))]
    · rw [hstalk, ← IdealSheafData.stalk_comap]
    · intro W _ hne
      have : x ∉ (W : Set X) := fun hxW => hne (Subtype.ext (huniq W W.2 hxW))
      rw [stalk_componentsFamily_eq_top Z W.2 this, Ideal.map_top, ← Ideal.one_eq_top, one_pow]
    · intro h; exact absurd (Finset.mem_univ _) h
  · refine ⟨0, ?_, ?_, fun h => absurd h hx⟩
    · rw [pow_zero, hD]
      refine Finset.prod_eq_one fun W _ => ?_
      have : x ∉ (W : Set X) := fun hxW => hx (W.2.1.2 hxW)
      rw [stalk_componentsFamily_eq_top Z W.2 this, Ideal.map_top, ← Ideal.one_eq_top, one_pow]
    · intro I _
      rw [(IdealSheafData.stalk_eq_top_iff_notMem_support Z x).2 hx, pow_zero, Ideal.one_eq_top]
      exact le_top

/-- `𝒪_{B_ZX}(-∑_j a_jF_j)` is an invertible ideal (an effective Cartier divisor). -/
theorem isEffectiveCartierDivisor_exceptionalDivisorIdeal {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (a : componentsOf (Z.support : Set X) → ℕ) :
    Stacks.Divisors.IsEffectiveCartierDivisor (exceptionalDivisorIdeal Z a) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian (blowUp Z) :=
    AlgebraicGeometry.TwoStepTower.isLocallyNoetherian_blowUp
      (AlgebraicGeometry.TwoStepTower.isFiniteType_of_isLocallyNoetherian Z)
  have hZc : Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap (blowUpToBase Z)) :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z
  refine AlgebraicGeometry.isEffectiveCartierDivisor_of_stalk_regular_principal _ fun y _ => ?_
  obtain ⟨n, hn, -, -⟩ := exists_stalk_exceptionalDivisorIdeal_eq sX hX Z hZ a y
  obtain ⟨g, hg, hgs⟩ :=
    AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _ hZc y
  refine ⟨g ^ n, IsRegular.pow n hg, ?_⟩
  rw [hn, hgs, Ideal.span_singleton_pow]

/-- If `ord_{Z_j} I ≥ a_j` for every component `Z_j` of `Z`, then
`π^*I ⊆ 𝒪_{B_ZX}(-∑_j a_jF_j)`. -/
theorem comap_le_exceptionalDivisorIdeal {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (I : X.IdealSheafData) (a : componentsOf (Z.support : Set X) → ℕ)
    (ha : ∀ W, (a W : ℕ∞) ≤ orderAlong I W.2.1.1) :
    I.comap (blowUpToBase Z) ≤ exceptionalDivisorIdeal Z a := by
  refine IdealSheafData.le_of_stalk_le _ _ fun y => ?_
  obtain ⟨n, hn, hle, -⟩ := exists_stalk_exceptionalDivisorIdeal_eq sX hX Z hZ a y
  rw [hn, IdealSheafData.stalk_comap, IdealSheafData.stalk_comap, ← Ideal.map_pow]
  exact Ideal.map_mono (hle I ha)

/-- With all `a_j = m`, `𝒪_{B_ZX}(-∑_j mF_j) = 𝒪_{B_ZX}(-mF) = (π^*I_Z)^m`. -/
theorem exceptionalDivisorIdeal_const {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) (m : ℕ) :
    exceptionalDivisorIdeal Z (fun _ => m) = Z.comap (blowUpToBase Z) ^ m := by
  have key : ∀ y, IdealSheafData.stalk (exceptionalDivisorIdeal Z (fun _ => m)) y =
      IdealSheafData.stalk (Z.comap (blowUpToBase Z) ^ m) y := by
    intro y
    obtain ⟨n, hn, -, hW⟩ := exists_stalk_exceptionalDivisorIdeal_eq sX hX Z hZ (fun _ => m) y
    rw [hn, IdealSheafData.stalk_pow]
    by_cases hx : blowUpToBase Z y ∈ (Z.support : Set X)
    · obtain ⟨_, rfl⟩ := hW hx
      rfl
    · rw [IdealSheafData.stalk_comap,
        (IdealSheafData.stalk_eq_top_iff_notMem_support Z _).2 hx, Ideal.map_top,
        ← Ideal.one_eq_top, one_pow, one_pow]
  exact le_antisymm (IdealSheafData.le_of_stalk_le _ _ fun y => (key y).le)
    (IdealSheafData.le_of_stalk_le _ _ fun y => (key y).ge)

/-- **Kollár 3.48/3.60.** Let `X` be smooth over a field, `Z ⊆ X` a smooth closed subscheme with
irreducible components `Z_j`, `π : B_ZX → X` the blow-up, `F_j = π⁻¹(Z_j)`, and `a_j ∈ ℕ` with
`ord_{Z_j} I ≥ a_j`. Then `𝒪_{B_ZX}(∑_j a_jF_j)·π^*I ⊆ 𝒪_{B_ZX}`: the ideal quotient
`(π^*I : 𝒪(-∑_j a_jF_j))` multiplied by the invertible ideal `𝒪(-∑_j a_jF_j)` is `π^*I`. -/
@[mmp "lem_kr3c_birational_transform_marked_ideal_is_ideal"]
theorem idealColon_comap_mul_exceptionalDivisorIdeal {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (I : X.IdealSheafData) (a : componentsOf (Z.support : Set X) → ℕ)
    (ha : ∀ W, (a W : ℕ∞) ≤ orderAlong I W.2.1.1) :
    idealColon (I.comap (blowUpToBase Z)) (exceptionalDivisorIdeal Z a) *
        exceptionalDivisorIdeal Z a = I.comap (blowUpToBase Z) := by
  have hDc := isEffectiveCartierDivisor_exceptionalDivisorIdeal sX hX Z hZ a
  have hle := comap_le_exceptionalDivisorIdeal sX hX Z hZ I a ha
  have hcol : idealColon (I.comap (blowUpToBase Z)) (exceptionalDivisorIdeal Z a) =
      Scheme.IdealSheafData.colon (I.comap (blowUpToBase Z)) (exceptionalDivisorIdeal Z a)
        (AlgebraicGeometry.fg_ideal_of_isEffectiveCartierDivisor _ hDc) := by
    unfold idealColon
    exact Scheme.IdealSheafData.ofIdeals_ideal
      (Scheme.IdealSheafData.colon (I.comap (blowUpToBase Z)) (exceptionalDivisorIdeal Z a)
        (AlgebraicGeometry.fg_ideal_of_isEffectiveCartierDivisor _ hDc))
  rw [hcol, mul_comm]
  exact AlgebraicGeometry.mul_colon_eq_of_isEffectiveCartierDivisor _ _ hDc hle

attribute [mmp "lem_kr3c_birational_transform_marked_ideal_is_ideal"]
  MarkedIdeal.birationalTransform_mul_eq

attribute [mmp "lem_kr3c_birational_transform_smooth_blowup_is_ideal"] controlledTransform_mul_eq

end MMP.Resolution
