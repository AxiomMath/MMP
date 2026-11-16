/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties

/-!
# Discrepancies on a common model (FA (2.23.4))

For proper birational morphisms `p : W ⟶ X`, `q : W ⟶ Y` of normal varieties and `ℝ`-divisors
`B_X`, `B_Y` with `K_X + B_X`, `K_Y + B_Y` `ℝ`-Cartier, compatible canonical divisors give
`p^*(K_X + B_X) - q^*(K_Y + B_Y) = ∑_P [a(ord_P, Y, B_Y) - a(ord_P, X, B_X)] P`.

## Main results

* `MMP.Flips.isDiscrepancy_ordPullback_sub_coeff_pullback`: the discrepancy of a prime divisor
  `P` of a model `W` is `ord_P(p^*ω) - coeff_P(p^*(K_X + D_X))`.
* `MMP.Flips.pullback_sub_pullback_eq_sum_discrepancy`: FA (2.23.4).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (2.23.4)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

namespace MMP.Flips

open MMP.Mori

variable {k : Type u} [Field k] {X Y W : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [LocallyOfFiniteType sX] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
  [LocallyOfFiniteType sY] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
  [LocallyOfFiniteType sY] [CompactSpace W] in
/-- The discrepancy of a prime divisor `P` of a model `p : W ⟶ X` is
`ord_P(p^*ω) - coeff_P(p^*(K_X + D_X))`. -/
theorem isDiscrepancy_ordPullback_sub_coeff_pullback [PerfectField k]
    (hX : IsNormalVariety k sX) {n : ℕ} {D_X : RDivisor X} (ω : RationalPluriForms sX n 1)
    (hω : ω ≠ 0) (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKD : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + D_X))
    (p : W ⟶ X) [IsProper p] (hW : IsNormalVariety k (p ≫ sX)) (hp : IsBirationalMorphism p)
    [LocallyOfFiniteType (p ≫ sX)] {G : RDivisor W}
    (hG : IsRCartierPullback p (Divisor.toRDivisor (divisorOfForm ω) + D_X) G)
    (P : Mori.PrimeDivisor W) :
    IsDiscrepancy sX n (divisorOfForm ω) D_X
      (ProperDivisorOver.mk ⟨W, p, hW, hp, P⟩ inferInstance).valuation
      (((ProperDivisorOver.mk ⟨W, p, hW, hp, P⟩ inferInstance :
        ProperDivisorOver k sX).toDivisorOver.ordPullback ω : ℝ) - G.coeff P) := by
  have : IsDominant p := hp.isDominant
  obtain ⟨m, r, L, L', hLc, hL, hLpb, hGdef⟩ := id hG
  have hGE : G.coeff P = ∑ j, r j * ((L' j).coeff P : ℝ) := by
    change G P = _
    rw [hGdef, Finsupp.finsetSum_apply]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    rfl
  have hdiv : IsDivisorOfFunctionField k sX
      (ProperDivisorOver.mk ⟨W, p, hW, hp, P⟩ inferInstance :
        ProperDivisorOver k sX).valuation := by
    let := functionFieldAlgebra sX
    let := functionFieldAlgebra (p ≫ sX)
    let := functionFieldMapAlgebra p
    have := isScalarTower_functionFieldMap sX p
    exact ⟨W, p ≫ sX, hW, P, AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom k X.functionField W.functionField)
      hp.functionFieldMap_bijective, rfl⟩
  rw [hGE]
  exact ⟨hK, hKD, ⟨hdiv, _, rfl⟩, _, ω, m, r, L, rfl, rfl, hX, hK.topologicalKrullDim_eq, hω,
    hLc, hL, L', hLpb, rfl⟩

/-- **FA (2.23.4), the identity behind 2.23.1–2.23.3 and 2.28.** Let `p : W ⟶ X` and
`q : W ⟶ Y` be proper birational morphisms of normal varieties of dimension `n` over a perfect
field, and `B_X`, `B_Y` `ℝ`-divisors on `X`, `Y` with `K_X + B_X` and `K_Y + B_Y` `ℝ`-Cartier,
where `K_X = div_X ω`, `K_Y = div_Y ω_Y` are canonical divisors for rational `n`-forms with
`div_W(p^*ω) = div_W(q^*ω_Y)` (the compatible canonical divisor `K_W` of the source, for
`ω_Y = (q⁻¹)^*p^*ω`). Then, with `a_X(P) = a(ord_P, X, B_X)` and `a_Y(P) = a(ord_P, Y, B_Y)` the
discrepancies of the prime divisors `P` of `W` (as divisors over `X` through `p` and over `Y`
through `q`), `p^*(K_X + B_X) - q^*(K_Y + B_Y) = ∑_P [a_Y(P) - a_X(P)] P`, a sum with finitely
many nonzero terms. -/
@[mmp "lem_fa2_common_model_identity"]
theorem pullback_sub_pullback_eq_sum_discrepancy [PerfectField k] (hX : IsNormalVariety k sX)
    (hY : IsNormalVariety k sY) {n : ℕ} (p : W ⟶ X) (q : W ⟶ Y) [IsProper p] [IsProper q]
    (hWp : IsNormalVariety k (p ≫ sX)) (hWq : IsNormalVariety k (q ≫ sY))
    (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q) [LocallyOfFiniteType (p ≫ sX)]
    [LocallyOfFiniteType (q ≫ sY)] (ω : RationalPluriForms sX n 1) (ωY : RationalPluriForms sY n 1)
    (hω : ω ≠ 0) (hωY : ωY ≠ 0) (hKX : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKY : (divisorOfForm ωY).IsCanonicalDivisor sY n)
    (hW : haveI : IsDominant p := hp.isDominant
      haveI : IsDominant q := hq.isDominant
      divisorOfForm (pullbackRationalPluriForms sX p ω) =
        divisorOfForm (pullbackRationalPluriForms sY q ωY))
    {B_X : RDivisor X} {B_Y : RDivisor Y}
    (hBX : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B_X))
    (hBY : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ωY) + B_Y))
    {G_X G_Y : RDivisor W}
    (hGX : IsRCartierPullback p (Divisor.toRDivisor (divisorOfForm ω) + B_X) G_X)
    (hGY : IsRCartierPullback q (Divisor.toRDivisor (divisorOfForm ωY) + B_Y) G_Y) :
    ∃ a_X a_Y : Mori.PrimeDivisor W → ℝ,
      (∀ P, IsDiscrepancy sX n (divisorOfForm ω) B_X
        (ProperDivisorOver.mk ⟨W, p, hWp, hp, P⟩ inferInstance).valuation (a_X P)) ∧
      (∀ P, IsDiscrepancy sY n (divisorOfForm ωY) B_Y
        (ProperDivisorOver.mk ⟨W, q, hWq, hq, P⟩ inferInstance).valuation (a_Y P)) ∧
      {P | a_Y P - a_X P ≠ 0}.Finite ∧
      ∀ P, (G_X - G_Y).coeff P = a_Y P - a_X P := by
  have : IsDominant p := hp.isDominant
  have : IsDominant q := hq.isDominant
  let a_X : Mori.PrimeDivisor W → ℝ := fun P =>
    ((ProperDivisorOver.mk ⟨W, p, hWp, hp, P⟩ inferInstance :
      ProperDivisorOver k sX).toDivisorOver.ordPullback ω : ℝ) - G_X.coeff P
  let a_Y : Mori.PrimeDivisor W → ℝ := fun P =>
    ((ProperDivisorOver.mk ⟨W, q, hWq, hq, P⟩ inferInstance :
      ProperDivisorOver k sY).toDivisorOver.ordPullback ωY : ℝ) - G_Y.coeff P
  have hord : ∀ P, ((ProperDivisorOver.mk ⟨W, p, hWp, hp, P⟩ inferInstance :
      ProperDivisorOver k sX).toDivisorOver.ordPullback ω : ℝ) =
      ((ProperDivisorOver.mk ⟨W, q, hWq, hq, P⟩ inferInstance :
      ProperDivisorOver k sY).toDivisorOver.ordPullback ωY : ℝ) := fun P =>
    (congrArg (fun D : Divisor W => ((Divisor.toRDivisor D) P : ℝ)) hW :)
  have hcoeff : ∀ P, (G_X - G_Y).coeff P = a_Y P - a_X P := by
    intro P
    change (G_X - G_Y) P = _
    simp only [a_X, a_Y, Finsupp.sub_apply, hord P]
    change G_X P - G_Y P = (_ - G_Y P) - (_ - G_X P)
    ring
  refine ⟨a_X, a_Y,
    fun P => isDiscrepancy_ordPullback_sub_coeff_pullback hX ω hω hKX hBX p hWp hp hGX P,
    fun P => isDiscrepancy_ordPullback_sub_coeff_pullback hY ωY hωY hKY hBY q hWq hq hGY P,
    (G_X - G_Y).hasFiniteSupport.subset fun P hP => ?_, hcoeff⟩
  rwa [Set.mem_ofPred_eq, ← hcoeff P] at hP

end MMP.Flips
