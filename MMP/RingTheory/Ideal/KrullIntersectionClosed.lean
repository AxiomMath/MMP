module

public import MMP.Attr
public import Mathlib.RingTheory.Filtration

/-!
# Ideals of a Noetherian local ring are closed in the adic topology

For a Noetherian local ring `(R, 𝔪)` and an ideal `I`, `I = ⋂_{s ≥ 1} (I + 𝔪^s)`. This is the
Krull intersection theorem for the finite `R`-module `R ⧸ I`.

## Main results

* `MMP.Resolution.Bridges.eq_iInf_sup_maximalIdeal_pow`: `I = ⨅ s, I ⊔ 𝔪^(s + 1)`.
-/

@[expose] public section

open IsLocalRing

namespace MMP.Resolution.Bridges

/-- **Ideals of a Noetherian local ring are adically closed.** Let `(R, 𝔪)` be a Noetherian local
ring and `I ⊆ R` an ideal. Then `I = ⋂_{s ≥ 1} (I + 𝔪^s)`. -/
@[mmp "lem_mmp_foundation_ideal_adic_closed"]
theorem eq_iInf_sup_maximalIdeal_pow {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (I : Ideal R) : I = ⨅ s : ℕ, (I ⊔ maximalIdeal R ^ (s + 1)) := by
  refine le_antisymm (le_iInf fun _ => le_sup_left) fun x hx => ?_
  rw [Submodule.mem_iInf] at hx
  have h0 := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := R) (M := R ⧸ I) (maximalIdeal R)
    (maximalIdeal.isMaximal R).ne_top
  have hmem : (Submodule.Quotient.mk x : R ⧸ I) ∈
      ⨅ i : ℕ, (maximalIdeal R ^ i • ⊤ : Submodule R (R ⧸ I)) := by
    rw [Submodule.mem_iInf]
    intro i
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hx i)
    have hab : (Submodule.Quotient.mk (a + b) : R ⧸ I) = Submodule.Quotient.mk b := by
      rw [Submodule.Quotient.eq]; simpa using ha
    have hb' : b ∈ maximalIdeal R ^ i := Ideal.pow_le_pow_right (Nat.le_succ i) hb
    have hb1 : (Submodule.Quotient.mk b : R ⧸ I) = b • Submodule.Quotient.mk 1 := by
      rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
    rw [hab, hb1]
    exact Submodule.smul_mem_smul hb' trivial
  rw [h0, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at hmem
  exact hmem

end MMP.Resolution.Bridges
