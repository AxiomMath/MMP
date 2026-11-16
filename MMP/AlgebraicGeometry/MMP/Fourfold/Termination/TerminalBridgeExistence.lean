module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.BridgeEnd
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.DecreasedPair
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.BridgeRelativeProgram

/-!
# Terminal bridges exist

Let `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` be a stabilized small klt tail of fourfolds, with stable
low-discrepancy set `I_∞`, fix `i`, and let `(p_i, Θ_i)` be a crepant junction of `(X_i, B_i)`
extracting `I_∞`. Then there are a crepant junction `(p_{i+1}, Θ_{i+1})` of `(X_{i+1}, B_{i+1})`
extracting `I_∞` and a terminal bridge from `(p_i, Θ_i)` to `(p_{i+1}, Θ_{i+1})`.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.exists_terminalBridge`: every crepant junction of
  `(X_i, B_i)` extracting `I_∞` is the source of a terminal bridge to a crepant junction of
  `(X_{i+1}, B_{i+1})` extracting `I_∞`.

## Implementation notes

A junction of `(X_i, B_i)` extracting `I_∞` is a
`MMP.Fourfold.FourfoldCrepantJunction` extracting a finite set `I` of valuations of `k(X_i)`
equal to `MMP.Fourfold.StabilizedSmallKltTail.stableLowDiscrepancySetAt i`, the image of `I_∞`.
A `MMP.Fourfold.StabilizedSmallKltTail.TerminalBridge` records that both its ends extract `I_∞`,
so the conclusion that the new junction extracts `I_∞` is part of the bridge.
-/

@[expose] public section

section

namespace Proof_lem_oai4_c1_bridge_exists

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold MMP.Fourfold.StabilizedSmallKltTail

/-- Valuations agreeing after pulling back along a surjective ring map agree. -/
private theorem valuation_eq_of_comap_eq {R S Γ : Type*} [Ring R] [Ring S]
    [LinearOrderedCommMonoidWithZero Γ] {g : R →+* S} (hg : Function.Surjective g)
    {v w : Valuation S Γ} (h : v.comap g = w.comap g) : v = w := by
  ext x
  obtain ⟨y, rfl⟩ := hg x
  exact congrArg (fun u : Valuation R Γ => u y) h

/-- The valuation of `k(X_i)` corresponding to a valuation of `k(X_0)` is unique. -/
private theorem corresponds_unique (T : StabilizedSmallKltTail) :
    ∀ (i : ℕ) {ξ : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
      {η η' : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))},
      T.Corresponds i ξ η → T.Corresponds i ξ η' → η = η'
  | 0, _, _, _, h, h' => h.trans h'.symm
  | i + 1, _, _, _, ⟨u, hu, huη⟩, ⟨u', hu', huη'⟩ => by
    obtain rfl := corresponds_unique T i hu hu'
    exact valuation_eq_of_comap_eq
      (T.isFourfoldStepDiagram i).isBirationalMorphism_plus.functionFieldMap_bijective.2
      (huη.trans huη'.symm)

/-- The log discrepancy of a valuation over a pair with a `ℚ`-boundary is rational. -/
private theorem exists_rat_isValuationLogDiscrepancy {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    (hP : MMP.Mori.IsPair sX B) {ξ : Valuation X.functionField (WithZero (Multiplicative ℤ))} {a : ℝ}
    (h : IsValuationLogDiscrepancy sX B ξ a) :
    ∃ q : ℚ, IsValuationLogDiscrepancy sX B ξ q := by
  obtain ⟨n, D, hDp, hv, hD⟩ := h
  obtain ⟨-, -, -, -, ⟨K, hK, -⟩, -⟩ := hD
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  refine ⟨1 + c, n, D, hDp, hv, ?_⟩
  push_cast
  exact MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hDp

/-- A crepant junction extracting `I_∞` has a decreased boundary. -/
private theorem exists_isDecreasedBoundary (T : StabilizedSmallKltTail)
    {i : ℕ} {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (J : FourfoldCrepantJunction (T.sX i) (T.B i) I)
    (hI : (I : Set _) = T.stableLowDiscrepancySetAt i) :
    ∃ Θ' : QDivisor J.Y, IsDecreasedBoundary J Θ' := by
  classical
  have key : ∀ s : I, ∃ q : ℚ, ∃ s' : Valuation (T.X (i + 1)).functionField
      (WithZero (Multiplicative ℤ)),
      T.IsTransportedValuation i s s' ∧ T.IsLogDiscrepancyAt (i + 1) s' q := by
    intro s
    have hs : (s : Valuation _ _) ∈ T.stableLowDiscrepancySetAt i := hI ▸ s.2
    obtain ⟨ξ, hξ, hcs⟩ := hs
    obtain ⟨η, hη, ζ, hcζ, htr⟩ := hξ (i + 1)
    obtain rfl := corresponds_unique T i hcζ hcs
    obtain ⟨-, a, ha, -⟩ := hη
    obtain ⟨q, hq⟩ := exists_rat_isValuationLogDiscrepancy
      (T.isStabilizedSmallKltTail.isKlt (i + 1)).1.isPair ha
    exact ⟨q, η, htr, hq⟩
  choose a s' hs' using key
  exact ⟨_, a, fun s => ⟨s' s, hs' s⟩, rfl⟩

private theorem solution (T : StabilizedSmallKltTail) (i : ℕ)
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (J : FourfoldCrepantJunction (T.sX i) (T.B i) I)
    (hI : (I : Set _) = T.stableLowDiscrepancySetAt i) :
    ∃ (I' : Finset (Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))))
      (J' : FourfoldCrepantJunction (T.sX (i + 1)) (T.B (i + 1)) I'),
      Nonempty (TerminalBridge i J J') := by
  obtain ⟨Θ', hΘ'⟩ := exists_isDecreasedBoundary T J hI
  obtain ⟨-, n, K, hK, -⟩ := (IsDecreasedBoundary.isKltTerminalPair hI hΘ').1.1.isPair
  obtain ⟨P, -, hnef⟩ := IsDecreasedBoundary.exists_relativeFourfoldProgram hI hΘ' K ⟨n, hK⟩
  obtain ⟨q, hq, hB, hpb⟩ := IsDecreasedBoundary.exists_isPullback_of_isRelativelyNef hΘ' P hnef
  obtain ⟨I', hI', J', e, he, hsY, hΘ⟩ :=
    IsDecreasedBoundary.exists_fourfoldCrepantJunction_of_isPullback hI hΘ' P hnef q hq hB hpb
  refine ⟨I', J', ⟨⟨hI, hI', K, Θ', hΘ', P,
    fun k hk ↦ IsDecreasedBoundary.isSmallMorphism_of_isRelativelyNef hΘ' P hnef hk,
    e, hsY, hΘ, ?_⟩⟩⟩
  rw [MMP.Fourfold.Oai4C1.Main.compHom_compHom P.compositeMap e.hom J'.p, he, hq]

end Proof_lem_oai4_c1_bridge_exists

end

namespace MMP.Fourfold.StabilizedSmallKltTail

/-- In a stabilized small klt tail, every crepant junction `(p_i, Θ_i)` of `(X_i, B_i)` extracting
`I_∞` admits a crepant junction `(p_{i+1}, Θ_{i+1})` of `(X_{i+1}, B_{i+1})` extracting `I_∞` and a
terminal bridge from `(p_i, Θ_i)` to `(p_{i+1}, Θ_{i+1})`. -/
@[mmp "lem_oai4_c1_bridge_exists"]
public theorem exists_terminalBridge (T : StabilizedSmallKltTail) (i : ℕ)
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (J : FourfoldCrepantJunction (T.sX i) (T.B i) I)
    (hI : (I : Set _) = T.stableLowDiscrepancySetAt i) :
    ∃ (I' : Finset (Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))))
      (J' : FourfoldCrepantJunction (T.sX (i + 1)) (T.B (i + 1)) I'),
      Nonempty (TerminalBridge i J J') :=
        by revert T i I J hI; first | exact Proof_lem_oai4_c1_bridge_exists.solution | exact Proof_lem_oai4_c1_bridge_exists.solution _ | exact Proof_lem_oai4_c1_bridge_exists.solution _ _ | exact Proof_lem_oai4_c1_bridge_exists.solution _ _ _ | exact Proof_lem_oai4_c1_bridge_exists.solution _ _ _ _

end MMP.Fourfold.StabilizedSmallKltTail

