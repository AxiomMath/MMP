module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.DecreasedPair
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ExceptionalValuations

/-!
# Models of a prepared chain are terminal

Let `(p_i, Θ_i)_{i ≥ 0}` be a terminal chain over a stabilized small klt tail of complex
fourfolds, and consider a prepared chain, its tail from a junction `Y_{i₀}` on. Every model
`(Y, Θ)` of the prepared chain is an effective terminal pair on a normal projective
`ℚ`-factorial fourfold `Y`, and its boundary is carried by the labels: `Θ = ∑_h b_h S_h`, where
`S_h` runs over the centres on `Y` of the labels of the chain and `b_h ∈ [0, 1)` are the label
coefficients.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.isKltTerminalPair_modelBoundary`: the
  models of a prepared chain are effective terminal pairs on normal projective `ℚ`-factorial
  fourfolds, with boundary supported on the labels and label coefficients in `[0, 1)`.

## Implementation notes

* Normality of `Y` is part of `MMP.Fourfold.IsQFactorial`, which includes
  `MMP.Mori.IsNormalVariety`; "fourfold" is `topologicalKrullDim Y = 4`.
* `Θ = ∑_h b_h S_h` is stated as: every prime divisor of `Y` at which `Θ` has nonzero
  coefficient is the centre `S_h^Y` of a label
  (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelCentre`). Since the label
  coefficient `b_h^Y` is by definition the coefficient of `Θ` at `S_h^Y`
  (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelCoefficient`), this is the
  equality of divisors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

open MMP.Mori

/-- Every coefficient of the boundary of a klt pair on a normal variety is `< 1`. -/
private theorem coeff_lt_one_of_isKltPair {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y}
    (hklt : IsKltPair sY Θ) (Γ : MMP.Mori.PrimeDivisor Y) : Θ.coeff Γ < 1 := by
  obtain ⟨hY, nY, _, hKY, -⟩ := hklt.1.isPair
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hklt.1.isPair hKY
    (DivisorOver.ofPrimeDivisor ℂ hY Γ)
  have hprop : IsProper (DivisorOver.ofPrimeDivisor ℂ hY Γ).f := by
    change IsProper (𝟙 Y)
    infer_instance
  have hpos := hklt.2 nY _ _
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hprop)
  rw [IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hY hc] at hpos
  push_cast at hpos
  exact_mod_cast (by linarith : ((Θ.coeff Γ : ℚ) : ℝ) < 1)

/-- Every model `(Y, Θ)` of a prepared chain is an effective terminal pair on a normal projective
`ℚ`-factorial fourfold `Y`, with `Θ = ∑_h b_h S_h` carried by the labels and every label
coefficient `b_h ∈ [0, 1)`. -/
@[mmp "lem_oai4_c2_chain_models_terminal"]
public theorem isKltTerminalPair_modelBoundary {T : StabilizedSmallKltTail} (Q : PreparedChain T)
    (x : Q.ModelIndex) :
    MMP.Mori.IsProjectiveVariety ℂ (Q.chain.modelStructure x.1) ∧
      IsQFactorial (Q.chain.modelStructure x.1) ∧
      topologicalKrullDim (Q.chain.model x.1) = 4 ∧
      IsKltTerminalPair (Q.chain.modelStructure x.1) (Q.chain.modelBoundary x.1) ∧
      0 ≤ Q.chain.modelBoundary x.1 ∧
      (∀ P : MMP.Mori.PrimeDivisor (Q.chain.model x.1),
        (Q.chain.modelBoundary x.1).coeff P ≠ 0 →
          ∃ S : Q.chain.Label, Q.chain.IsLabelCentre S x.1 P) ∧
      ∀ (S : Q.chain.Label) (b : ℚ), Q.chain.IsLabelCoefficient S x.1 b → b ∈ Set.Ico 0 1 := by
  obtain ⟨hterm, hQ, hproj, hdim⟩ := Q.chain.isKltTerminalPair_modelBoundary x.1
  have hnonneg : ∀ P, 0 ≤ (Q.chain.modelBoundary x.1).coeff P := hterm.1.1.nonneg
  refine ⟨hproj, hQ, hdim, hterm, hnonneg, fun P hP => ?_, fun S b hb => ?_⟩
  · by_contra h
    push Not at h
    choose b hb using fun S => Q.chain.exists_isLabelCoefficient S x.1
    rw [Q.chain.coeff_modelBoundary_eq_finsum x.1 b hb P,
      finsum_eq_zero_of_forall_eq_zero fun S => by
        classical rw [finsum_eq_if, if_neg (h S)]] at hP
    exact hP rfl
  · rcases hb with ⟨P, -, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨hnonneg P, coeff_lt_one_of_isKltPair hterm.1 P⟩
    · exact ⟨le_rfl, zero_lt_one⟩

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain
