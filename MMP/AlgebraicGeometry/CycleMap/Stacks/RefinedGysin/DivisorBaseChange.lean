module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.DivisorVirtualNormalBundleClass
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import MMP.AlgebraicGeometry.RegularImmersion.CodimOne

/-!
# The base change of a divisor to an integral scheme

Let `f : X ⟶ Y` be a regular closed immersion of codimension one, that is an effective Cartier
divisor `D ⊆ Y`, and let `j : V ⟶ Y` be a morphism from an integral scheme. Then the base change
`pullback.snd f j : X ×_Y V ⟶ V` is either an isomorphism (`V` lies in `D`) or again a regular
closed immersion of codimension one (`V ×_Y D` is an effective Cartier divisor on `V`).

The proof goes through the canonical section: `D` is the zero scheme of the canonical section
`1_D` of `𝒪_Y(D)` (Stacks 01X0), the base change `D ×_Y V` is the zero scheme of the pulled-back
section `j^* 1_D` (Stacks 0B6Y), and on the integral scheme `V` the zero scheme of a section of
an invertible module is the whole of `V` when the section vanishes, and an effective Cartier
divisor otherwise.

## Main results

* `MMP.Chow.isIso_or_isRegularClosedImmersionOfCodim_one_pullback_snd`

## References

* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace MMP.Chow

/-- A closed subscheme cut out by the zero ideal sheaf is the whole scheme. -/
theorem isIso_subschemeι_of_eq_bot {V : Scheme.{u}} (I : V.IdealSheafData) (h : I = ⊥) :
    IsIso I.subschemeι := by
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot, Scheme.IdealSheafData.ker_subschemeι, h]

/-- **The base change of a divisor to an integral scheme.** For an integral `V`, a morphism
`j : V ⟶ Y` and a regular closed immersion `f : X ⟶ Y` of codimension one, the base change
`X ×_Y V ⟶ V` is an isomorphism or a regular closed immersion of codimension one. -/
theorem isIso_or_isRegularClosedImmersionOfCodim_one_pullback_snd {X Y V : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] [IsIntegral V] (j : V ⟶ Y)
    (hf : IsRegularClosedImmersionOfCodim f 1) :
    IsIso (pullback.snd f j) ∨ IsRegularClosedImmersionOfCodim (pullback.snd f j) 1 := by
  have := isEffectiveCartierDivisor_ker_of_isRegularClosedImmersionOfCodim_one f hf
  let L := Stacks.Divisors.divisorSheaf f.ker
  let s := Stacks.Divisors.divisorSheafGlobalSection f.ker
  have hker : f.ker = (gysinTripleInclusion L s).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact (Stacks.Divisors.zeroScheme_canonicalSection f.ker).symm
  let e := IsClosedImmersion.lift (gysinTripleInclusion L s) f hker.ge
  have : IsIso e := IsClosedImmersion.isIso_lift _ _ hker.symm
  let m := pullback.map f j (gysinTripleInclusion L s) j e (𝟙 V) (𝟙 Y)
    (by simp [e, IsClosedImmersion.lift_fac]) (by simp)
  have : IsIso m := by
    dsimp only [m]
    infer_instance
  let ε := asIso m ≪≫ (gysinDivisorBaseChangeIso L s j).symm
  have hsnd : pullback.snd f j = ε.hom ≫ (gysinTripleDivisor L s j).subschemeι := by
    simp only [ε, m, Iso.trans_hom, asIso_hom, Iso.symm_hom]
    rw [← gysinDivisorBaseChangeIso_hom_snd L s j, Category.assoc, Iso.inv_hom_id_assoc]
    simp
  by_cases ht : gysinTripleSection L s j = 0
  · left
    have hbot : gysinTripleDivisor L s j = ⊥ := by
      simp [gysinTripleDivisor, ht, Stacks.Divisors.zeroScheme_zero_eq_bot]
    have := isIso_subschemeι_of_eq_bot _ hbot
    rw [hsnd]
    infer_instance
  · right
    have hD := AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_of_ne_zero
      (gysinTripleModule L j) (gysinTripleSection L s j) ht
    rw [hsnd]
    exact (isRegularClosedImmersionOfCodim_one_of_isEffectiveCartierDivisor
      (gysinTripleDivisor L s j).subschemeι
      (by rwa [Scheme.IdealSheafData.ker_subschemeι])).iso_comp ε _

end MMP.Chow
