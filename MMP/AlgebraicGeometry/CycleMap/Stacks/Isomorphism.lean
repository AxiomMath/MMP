module

public import MMP.AlgebraicGeometry.Chow.CycleClassDescent

/-!
# Complex schemes whose cycle class map is an isomorphism (Fulton, Example 19.1.11)

For a complex scheme `X`, *`cl_X : A_* X → H_* X` is an isomorphism* means: for every `k` the
cycle class map `MMP.Chow.chowCycleClass R k : A_k(X) →+ H_{2k}(X(ℂ); R)` on Stacks' Chow group
over `fieldChowSituation ℂ` is bijective, and `H_{2k+1}(X(ℂ); R) = 0` for every `k`.

## Main definitions

* `MMP.Chow.ChowCycleClassIsIso R X`: the property.

## Main results

* `MMP.Chow.ChowCycleClassIsIso.subsingleton_of_odd`: then `H_i X = 0` for every odd integer `i`.

## Implementation notes

The degree `k` is a natural number (Fulton's `k ≥ 0`); in negative degrees `H_j X` vanishes
(`isZero_borelMooreHomology_of_neg`), so the odd-degree condition for `k : ℕ` gives `H_i X = 0`
for every odd integer `i`. `H_{2k+1} X = 0` is stated as `Subsingleton`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Example 19.1.11.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Chow

namespace MMP.Chow

variable (R : Type) [CommRing R] (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- *`cl_X : A_* X → H_* X` is an isomorphism* (Fulton, Example 19.1.11), for a complex scheme
`X`: every cycle class map `A_k(X) →+ H_{2k}(X(ℂ); R)` on Stacks' Chow groups is bijective, and
`H_{2k+1}(X(ℂ); R) = 0` for every `k`. -/
structure ChowCycleClassIsIso : Prop where
  /-- The cycle class map `A_k(X) →+ H_{2k}(X(ℂ); R)` is bijective. -/
  bijective (k : ℕ) : Function.Bijective (chowCycleClass (X := X) R k)
  /-- `H_{2k+1}(X(ℂ); R) = 0`. -/
  subsingleton_odd (k : ℕ) : Subsingleton (BMHomology R X (2 * k + 1))

variable {R X}

/-- If `cl_X` is an isomorphism, then `H_i X = 0` for every odd integer `i`. -/
theorem ChowCycleClassIsIso.subsingleton_of_odd (h : ChowCycleClassIsIso R X) {i : ℤ}
    (hi : Odd i) :
    Subsingleton
      (borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) i) := by
  obtain ⟨j, rfl⟩ := hi
  rcases lt_or_ge j 0 with hj | hj
  · exact ModuleCat.subsingleton_of_isZero
      (isZero_borelMooreHomology_of_neg R _ _ (by omega))
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    convert h.subsingleton_odd k using 3
    push_cast
    ring

end MMP.Chow
