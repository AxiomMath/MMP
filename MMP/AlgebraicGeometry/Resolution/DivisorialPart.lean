/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Basic
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
public import MMP.AlgebraicGeometry.Resolution.OrderRestriction

/-!
# The divisorial part of an ideal sheaf

Let `X` be a smooth scheme and `I ⊆ 𝒪_X` a coherent ideal sheaf nonzero on every irreducible
component of `X`. The divisorial part divisor `Div(I) = ∑_D ord_D(I)·D` runs over the irreducible
components `D` of `cosupp I` of codimension one (Kollár Def. 3.48). Its coefficients are positive
integers: the generic point of such a `D` lies in `cosupp I`, so `ord_D I ≥ 1`, and orders of `I`
are finite. Moreover `I ⊆ 𝒪_X(-Div(I))`: at a point `x`, the components through `x` have pairwise
non-associate prime local equations `u_D` in the factorial ring `𝒪_{x,X}`, every `g ∈ I_x` is
divisible by `u_D^{ord_D I}` because `I_{ξ_D} ⊆ 𝔪_{ξ_D}^{ord_D I}`, and so by unique
factorization `∏_D u_D^{ord_D I}` divides `g`.

## Main results

* `MMP.Resolution.divisorialPart_apply_of_mem_componentsOf`: the coefficient of `Div(I)` along a
  codimension-one component `D` of `cosupp I` is the positive integer `ord_D I`.
* `MMP.Resolution.mem_support_divisorialPart_iff`: the prime divisors occurring in `Div(I)` are
  exactly the codimension-one components of `cosupp I`.
* `MMP.Resolution.le_divisorialPartIdeal`: `I ⊆ 𝒪_X(-Div(I))`.

## Implementation notes

`𝒪_X(-Div(I))` is `MMP.Resolution.divisorialPartIdeal I = ∏ᶠ_D I_D^{ord_D I}`. The coefficient
statements only use that `X` is noetherian; the containment only uses that `X` is smooth over a
field (for the factoriality of its local rings).

## References

* [J. Kollár, *Lectures on resolution of singularities*, Def. 3.48]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

variable {X : Scheme.{u}}

/-- `n ≤ ord(J)` exactly when `J ⊆ 𝔪ⁿ`. -/
theorem natCast_le_idealOrder_iff' {R : Type*} [CommRing R] [IsLocalRing R] (J : Ideal R)
    (n : ℕ) : (n : ℕ∞) ≤ idealOrder J ↔ J ≤ maximalIdeal R ^ n :=
  ⟨le_pow_of_le_idealOrder, fun h => le_iSup₂_of_le n h le_rfl⟩

/-- On a noetherian scheme the coefficients of `Div(I)` are the `divisorialPartCoeff I D`. -/
theorem divisorialPart_apply [IsNoetherian X] (I : X.IdealSheafData)
    (D : AlgebraicGeometry.PrimeDivisor X) :
    divisorialPart I D = divisorialPartCoeff I D := by
  unfold divisorialPart
  rw [dif_pos (finite_support_divisorialPartCoeff I)]
  rfl

/-- If the prime divisor `D` is an irreducible component of `cosupp I`, then `1 ≤ ord_D I`. -/
theorem one_le_multAt_of_mem_componentsOf {I : X.IdealSheafData}
    {D : AlgebraicGeometry.PrimeDivisor X}
    (hD : (D.support : Set X) ∈ componentsOf (I.support : Set X)) :
    1 ≤ multAt I D.genericPoint := by
  have hmem : D.genericPoint ∈ (I.support : Set X) := hD.1.2 <| by
    rw [Aux.support_eq_closure_genericPoint]
    exact subset_closure rfl
  unfold multAt
  rw [← Nat.cast_one, natCast_le_idealOrder_iff', pow_one]
  exact le_maximalIdeal fun h => ((IdealSheafData.stalk_eq_top_iff_notMem_support I _).1 h) hmem

/-- On a noetherian scheme, for `I` nonzero at the generic points of `X`, orders of `I` are
finite. -/
theorem multAt_ne_top_of_isNonzeroAtGenericPoints [IsNoetherian X] {I : X.IdealSheafData}
    (hI : IsNonzeroAtGenericPoints I) (x : X) : multAt I x ≠ ⊤ := by
  refine Kollar.multAt_ne_top_of_stalk_genericPoint_ne_bot (I := I) (fun T hT => hI _ ?_) x
  have hgen := hT.1.isGenericPoint_genericPoint_closure
  rw [(isClosed_of_mem_irreducibleComponents T hT).closure_eq] at hgen
  rwa [hgen.def]

/-- **Kollár, Def. 3.48: the coefficients of `Div(I)` are positive integers.** Let `X` be
noetherian and `I` nonzero at the generic point of every irreducible component of `X`. For a
prime divisor `D` which is an irreducible component of `cosupp I`, the coefficient of `D` in
`Div(I)` is positive and is the order `ord_D I` (which is therefore finite). -/
@[mmp "lem_kr3c_divisorial_part_contains"]
theorem divisorialPart_apply_of_mem_componentsOf [IsNoetherian X] {I : X.IdealSheafData}
    (hI : IsNonzeroAtGenericPoints I) {D : AlgebraicGeometry.PrimeDivisor X}
    (hD : (D.support : Set X) ∈ componentsOf (I.support : Set X)) :
    0 < divisorialPart I D ∧ ((divisorialPart I D).toNat : ℕ∞) = multAt I D.genericPoint := by
  have htop := multAt_ne_top_of_isNonzeroAtGenericPoints hI D.genericPoint
  rw [divisorialPart_apply, divisorialPartCoeff, if_pos hD, Int.toNat_natCast,
    ENat.natCast_toNat htop]
  refine ⟨?_, rfl⟩
  have : 1 ≤ (multAt I D.genericPoint).toNat := by
    rw [← ENat.natCast_le_natCast, ENat.natCast_toNat htop]
    exact_mod_cast one_le_multAt_of_mem_componentsOf hD
  omega

/-- The prime divisors occurring in `Div(I)` are exactly the irreducible components of
`cosupp I` which are prime divisors. -/
theorem mem_support_divisorialPart_iff [IsNoetherian X] {I : X.IdealSheafData}
    (hI : IsNonzeroAtGenericPoints I) {D : AlgebraicGeometry.PrimeDivisor X} :
    D ∈ (divisorialPart I).support ↔ (D.support : Set X) ∈ componentsOf (I.support : Set X) := by
  rw [Finsupp.mem_support_iff]
  refine ⟨fun h => ?_, fun hD => (divisorialPart_apply_of_mem_componentsOf hI hD).1.ne'⟩
  by_contra hD
  exact h (by rw [divisorialPart_apply, divisorialPartCoeff, if_neg hD])

/-- **Kollár, Def. 3.48: `I ⊆ 𝒪_X(-Div(I))`.** On a scheme smooth over a field, every ideal
sheaf `I` is contained in `𝒪_X(-Div(I)) = ∏ᶠ_D I_D^{ord_D I}`. -/
@[mmp "lem_kr3c_divisorial_part_contains"]
theorem le_divisorialPartIdeal {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] (hX : MMP.Mori.IsSmoothScheme sX) (I : X.IdealSheafData) :
    I ≤ divisorialPartIdeal I := by
  classical
  unfold divisorialPartIdeal
  by_cases hfin : (Function.mulSupport fun D : AlgebraicGeometry.PrimeDivisor X =>
      D.idealSheaf ^ (divisorialPartCoeff I D).toNat).Finite
  · rw [finprod_eq_prod _ hfin]
    refine Aux.le_prod_of_stalk_le sX hX (fun D => (divisorialPartCoeff I D).toNat) _ I
      fun D _ => ?_
    rw [← natCast_le_idealOrder_iff']
    change _ ≤ multAt I D.genericPoint
    unfold divisorialPartCoeff
    split_ifs
    · rw [Int.toNat_natCast]
      exact ENat.natCast_toNat_le_self _
    · simp
  · rw [finprod_of_infinite_mulSupport hfin]
    exact le_top

end MMP.Resolution
