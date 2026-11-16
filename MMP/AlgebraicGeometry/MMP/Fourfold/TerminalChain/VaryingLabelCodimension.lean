module

public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.JunctionLabels
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.DecreasedPair
public import MMP.AlgebraicGeometry.MMP.Fourfold.StabilizedTail.BadSurfacesFinite

/-!
# Varying labels have downstairs centre of codimension at least three

Let `(p_i, Θ_i)_{i ≥ 0}`, `p_i : Y_i ⟶ X_i`, be a terminal chain over a stabilized small klt
tail `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` of fourfolds. There is an index `i₁` such that for
every `i ≥ i₁` and every varying label `S_h`, the centre `c_{X_i}(ord_{S_h})` on `X_i` of the
valuation `ord_{S_h}` has codimension at least three in `X_i`.

Take `i₁` such that every irreducible surface `V ⊆ W_j⁻`, `j ≥ i₁`, has
`mld_{η_V}(X_j, B_j) > 1`. A varying label `S_h` is not the strict transform of a component of
`B_0`, since those labels have constant coefficient. So it is an extracted divisor `E_{0,s}`,
`s ∈ I_∞`. Its valuation on `X_i` lies in `I_i`, so it is exceptional over `X_i` and its centre
has codimension at least two. Codimension two is excluded, because the label would then be fixed.

## Main results

* `StabilizedSmallKltTail.TerminalChain.exists_three_le_codimension_of_isVaryingLabel`: from some
  index on, the centre on `X_i` of every varying label has codimension at least three.

## Implementation notes

* The valuation `ord_{S_h}` is `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.labelValuation`,
  a valuation of `k(X_0)`; it is carried to a valuation `w` of `k(X_i)` by
  `MMP.Fourfold.StepSequence.Corresponds`. The centre `c_{X_i}(w)` is an irreducible closed
  subset `Z` of `X_i` with `MMP.Intersection.IsCentre ℂ (T.sX i) w Z`, and the conclusion is
  stated for every such `w` and `Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

namespace StabilizedSmallKltTail

namespace TerminalChain

/-- The valuation of `k(X_j)` corresponding to a valuation of `k(X_0)` is unique. -/
private theorem corresponds_unique {T : StabilizedSmallKltTail}
    {ξ : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))} :
    ∀ {j : ℕ} {η₁ η₂ : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ))},
      T.Corresponds j ξ η₁ → T.Corresponds j ξ η₂ → η₁ = η₂
  | 0, _, _, h₁, h₂ => h₁.trans h₂.symm
  | j + 1, _, _, ⟨ζ₁, h₁, t₁⟩, ⟨ζ₂, h₂, t₂⟩ => by
    obtain rfl := corresponds_unique h₁ h₂
    have hb := (T.isFourfoldStepDiagram j).isSmallMorphism_plus.isBirationalMorphism
    exact MMP.Fourfold.Oai4C1.valuation_eq_of_comap_eq hb.functionFieldMap_bijective.2
      (t₁.trans t₂.symm)

/-- The centre on `X_i` of the valuation corresponding to an extracted label `E_{0,s}`,
`s ∈ I_∞`, has codimension at least two. -/
private theorem two_le_codimension_of_corresponds {T : StabilizedSmallKltTail}
    (C : TerminalChain T) (s : C.I 0) {i : ℕ}
    {w : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))}
    (hw : T.Corresponds i s.1 w) {Z : IrreducibleCloseds (T.X i)}
    (hZ : MMP.Intersection.IsCentre ℂ (T.sX i) w Z) : 2 ≤ codimension Z := by
  obtain ⟨ξ, hξ, hsξ : s.1 = ξ⟩ : s.1 ∈ T.stableLowDiscrepancySetAt 0 := by
    rw [← C.coe_I 0]; exact s.2
  obtain ⟨η, ⟨⟨D, -, hD, hDc⟩, -⟩, hη⟩ := hξ i
  obtain rfl := corresponds_unique (hsξ ▸ hw) hη
  obtain ⟨D', -, hD', rfl⟩ := hZ
  rwa [MMP.Positivity.DivisorOver.center_eq_of_valuation_eq
    (T.isFourfoldStepDiagram i).isNormalVariety_minus.1 (hD.symm.trans hD')] at hDc

variable {T : StabilizedSmallKltTail}

/-- For a terminal chain over a stabilized small klt tail there is `i₁` such that for every
`i ≥ i₁` and every varying label `S_h`, the centre `c_{X_i}(ord_{S_h})` on `X_i` has codimension
at least three. -/
@[mmp "prop_oai4_codim_two"]
public theorem exists_three_le_codimension_of_isVaryingLabel (C : TerminalChain T) :
    ∃ i₁ : ℕ, ∀ i ≥ i₁, ∀ S : C.Label, C.IsVaryingLabel S →
      ∀ w : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)),
        T.Corresponds i (labelValuation S) w →
      ∀ Z : IrreducibleCloseds (T.X i), MMP.Intersection.IsCentre ℂ (T.sX i) w Z →
        3 ≤ codimension Z := by
  obtain ⟨i₁, hi₁⟩ :=
    T.isStabilizedSmallKltTail.exists_forall_ge_one_lt_minimalLogDiscrepancy
  refine ⟨i₁, ?_⟩
  rintro i hi ⟨S, ⟨Γ, hΓ, hΓS⟩ | ⟨s, rfl⟩⟩ hS w hw Z hZ
  · exact (hS ⟨_, 0, fun j _ =>
      isLabelCoefficient_coeff_of_inverseTransformPrimeDivisor_eq_some (C := C)
        ⟨S, Or.inl ⟨Γ, hΓ, hΓS⟩⟩ hΓ hΓS ⟨j, none⟩⟩).elim
  · rw [labelValuation_E] at hw
    exact Order.add_one_le_of_lt ((two_le_codimension_of_corresponds C s hw hZ).lt_of_ne
      fun h2 => hS (C.isFixedLabel_E_of_codimension_eq_two (fun j hj => (hi₁ j hj).1) s hi hw
        hZ h2.symm))

end TerminalChain

end StabilizedSmallKltTail

end MMP.Fourfold
