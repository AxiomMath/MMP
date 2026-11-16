module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
import MMP.AlgebraicGeometry.MMP.Threefold.AffineBaseLogTerminalModel

/-!
# The birational finite-generation property in dimension three

The property `F(3)` holds: for every normal `ℚ`-factorial complex threefold `S`, projective and
birational over a normal affine complex variety `T`, and every effective real klt boundary `Θ` on
`S`, the floor-section algebra of `K_S + Θ` is finitely generated over `Γ(T, 𝒪_T)` when `Θ` is
rational, the divisorial stable base primes of `K_S + Θ` over `T` persist for all nearby
effective klt boundaries supported on `Θ`, and along the smallest rational affine hull of `Θ`
the relative fixed divisors of the nearby adjoint systems are nonempty systems whose components
are divisorial stable base primes of `K_S + Θ` over `T`.

## Main results

* `MMP.Fourfold.birationalFiniteGenerationProperty_three`: the property
  `MMP.Fourfold.BirationalFiniteGenerationProperty 3`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

section

namespace Proof_thm_fourfold_birational_property_f3

open MMP.Fourfold

private theorem solution : MMP.Fourfold.BirationalFiniteGenerationProperty 3 := by
  refine ⟨by norm_num, ?_⟩
  intro S _ _ _ _ sS T sT f hSQ hdim hT hTa hf hfp hfb Θ hΘ hklt K hK
  have : AlgebraicGeometry.LocallyOfFiniteType sS := hklt.1.1.toLocallyOfFiniteType
  obtain ⟨-, hpers, hfix, hfg⟩ :=
    IsRealKltPair.exists_logTerminalModel_of_isBirationalMorphism_of_isAffine
      hSQ hdim hT hTa hf hfp hfb hΘ hklt hK
  exact ⟨hfg, hpers, hfix⟩

end Proof_thm_fourfold_birational_property_f3

end

namespace MMP.Fourfold

/-- **The property `F(3)`**: the birational finite-generation property
`BirationalFiniteGenerationProperty` holds in dimension three. -/
@[mmp "thm_fourfold_birational_property_f3"]
public theorem birationalFiniteGenerationProperty_three :
    BirationalFiniteGenerationProperty 3 :=
      by first | exact Proof_thm_fourfold_birational_property_f3.solution | exact Proof_thm_fourfold_birational_property_f3.solution _ | exact Proof_thm_fourfold_birational_property_f3.solution _ _ | exact Proof_thm_fourfold_birational_property_f3.solution _ _ _ | exact Proof_thm_fourfold_birational_property_f3.solution _ _ _ _

