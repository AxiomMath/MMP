module

public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteRelativeThreefoldProgram

/-!
# Decreased boundaries, terminal bridges and terminal chains

Let `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` be a stabilized tail with common low-discrepancy set
`I_∞`, and let `(p_i, Θ_i)`, `p_i : Y_i ⟶ X_i`, be a crepant junction of `(X_i, B_i)` extracting
`I_∞`, with exceptional divisors `E_{i,s} = c_{Y_i}(s)`, `s ∈ I_∞`. Its *decreased boundary* is
`Θ_i' = (p_i)⁻¹_* B_i + ∑_{s ∈ I_∞} (1 - a_{i+1}(s)) E_{i,s}`, where `a_{i+1}(s)` is the log
discrepancy of `s` over the next model `(X_{i+1}, B_{i+1})`.

A *terminal bridge* from `(p_i, Θ_i)` to a crepant junction `(p_{i+1}, Θ_{i+1})` of
`(X_{i+1}, B_{i+1})` extracting `I_∞` is a finite relative threefold programme over `Z_i` (by
`π₀ = f_i ∘ p_i`) from `(Y_i, Θ_i')` in which every contraction `g_k` is small, ending at
`(Y_{i+1}, Θ_{i+1})` with `π_m = f_i⁺ ∘ p_{i+1}`, and whose composite birational map
`φ : Y_i ⤏ Y_{i+1}` satisfies `p_{i+1} ∘ φ = (f_i⁺)⁻¹ ∘ f_i ∘ p_i`.

A *terminal chain* over the tail is a sequence of crepant junctions `(p_i, Θ_i)` of `(X_i, B_i)`
extracting `I_∞` together with a terminal bridge from each to the next. Its models are, in order,
the junction `(Y_0, Θ_0)`, the decreased pair `(Y_0, Θ_0')`, the further models of the first
bridge, the last of which is the junction `(Y_1, Θ_1)`, then `(Y_1, Θ_1')`, and so on;
consecutive models are related by a coefficient decrease `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` or by a flip
of a bridge, a threefold step diagram in which both contractions are small.

## Main definitions

* `MMP.Fourfold.StabilizedTail.IsDecreasedBoundary`: the decreased boundary `Θ_i'` of a crepant
  junction of `(X_i, B_i)`.
* `MMP.Fourfold.StabilizedTail.TerminalBridge`: terminal bridges between crepant junctions of
  consecutive models of a stabilized tail.
* `MMP.Fourfold.StabilizedTail.TerminalChain`: terminal chains over a stabilized tail.
* `MMP.Fourfold.StabilizedTail.TerminalChain.ModelIndex`,
  `MMP.Fourfold.StabilizedTail.TerminalChain.model`,
  `MMP.Fourfold.StabilizedTail.TerminalChain.modelBoundary`: the models of a terminal chain.

## Implementation notes

* The set `I_∞ = I(X_0, B_0)` is a set of valuations of `k(X_0)`; a junction of `(X_i, B_i)`
  extracts a finite set of valuations of `k(X_i)`. A junction of `(X_i, B_i)` *extracting `I_∞`*
  is one extracting a finite set `I` with `I = I(X_i, B_i)`, which is the image of `I_∞` under the
  identification `k(X_0) ≅ k(X_i)` by the defining property
  `MMP.Fourfold.StabilizedTail.lowDiscrepancySet_eq` of a stabilized tail.
* For `s` a valuation of `k(X_i)`, `a_{i+1}(s)` is the log discrepancy over `(X_{i+1}, B_{i+1})`
  of the valuation `s'` of `k(X_{i+1})` corresponding to `s` under
  `k(X_i) ≅ k(Z_i) ≅ k(X_{i+1})`, that is, with `s'|_{k(Z_i)} = s|_{k(Z_i)}`. As in
  `MMP.Fourfold.CrepantJunction`, log discrepancies enter through the predicate
  `MMP.Fourfold.IsValuationLogDiscrepancy`, so the decreased boundary is a predicate
  `IsDecreasedBoundary J Θ'` on a divisor `Θ'` of `Y_i`; the values `a_{i+1}(s)` are rational
  because `B_{i+1}` is.
* The programme of a bridge is run with a canonical divisor `K` of `Y_i`, carried as data. The end
  `(Y_{i+1}, Θ_{i+1})` of the programme is an identification `e : V_m ≅ Y_{i+1}` carrying `Θ_m` to
  `Θ_{i+1}` (`Θ_m = e⁻¹_* Θ_{i+1}`) and `π_m` to `f_i⁺ ∘ p_{i+1}`.
* The birational map `(g_k⁺)⁻¹ ∘ g_k : V_k ⤏ V_{k+1}` of a flip is, as in
  `MMP.Mori.IsFlipRationalMap`, the rational map `φ_k` with `g_k⁺ ∘ φ_k = g_k`. The composites
  `ψ_k : Y_i = V_0 ⤏ V_k` are accordingly given by `ψ_0 = id` and `g_k⁺ ∘ ψ_{k+1} = g_k ∘ ψ_k`,
  and `φ = e ∘ ψ_m`; likewise `p_{i+1} ∘ φ = (f_i⁺)⁻¹ ∘ f_i ∘ p_i` is stated as
  `f_i⁺ ∘ p_{i+1} ∘ φ = f_i ∘ p_i`. These determine the maps: a rational map `χ` from an integral
  scheme with `h ∘ χ` dominant, `h` birational, is dominant, and is then determined by `h ∘ χ`,
  since `h` is an isomorphism over a dense open containing the generic point.
* The models of a terminal chain are indexed by pairs `(i, none)`, the junction `(Y_i, Θ_i)`, and
  `(i, some k)`, `k < m_i`, the model `(V_k, Θ_k)` of the `i`-th bridge, in lexicographic order;
  `(i, some 0)` is the decreased pair `(Y_i, Θ_i')`, and the end `V_{m_i}` of the `i`-th bridge is
  the junction `(Y_{i+1}, Θ_{i+1})`, so it is not listed again.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-- The source of a crepant junction is quasi-compact: it is projective over `ℂ`. -/
instance CrepantJunction.compactSpace {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}
    (J : CrepantJunction sX B I) : CompactSpace J.Y := by
  have := isProper_of_isProjectiveMorphism _ J.isProjectiveVariety.isProjective
  exact QuasiCompact.compactSpace_of_compactSpace (J.p ≫ sX)

namespace StabilizedTail

variable (T : StabilizedTail)

/-- The valuation `s'` of `k(X_{i+1})` corresponds to the valuation `s` of `k(X_i)` under the
identifications `k(X_i) ≅ k(Z_i) ≅ k(X_{i+1})`: their restrictions to `k(Z_i)` agree. -/
def IsTransportedValuation (i : ℕ)
    (s : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))
    (s' : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))) : Prop :=
  haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
  s'.comap (functionFieldMap (T.fp i)) = s.comap (functionFieldMap (T.f i))

variable {T}

/-- `Θ'` is the *decreased boundary* of a crepant junction `(p_i, Θ_i)` of `(X_i, B_i)`
extracting `I`, `p_i : Y_i ⟶ X_i`, with divisors `E_{i,s} = c_{Y_i}(s)`:
`Θ' = (p_i)⁻¹_* B_i + ∑_{s ∈ I} (1 - a_{i+1}(s)) E_{i,s}`, where `a_{i+1}(s)` is the log
discrepancy `a(s'; X_{i+1}, B_{i+1})` of the valuation `s'` of `k(X_{i+1})` corresponding to `s`
(`MMP.Fourfold.StabilizedTail.IsTransportedValuation`). -/
@[mmp "def_mmp_indexc_decreased_boundary"]
def IsDecreasedBoundary {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (J : CrepantJunction (T.sX i) (T.B i) I) (Θ' : QDivisor J.Y) : Prop :=
  ∃ a : I → ℚ,
    (∀ s : I, ∃ s' : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ)),
      T.IsTransportedValuation i s s' ∧
        IsValuationLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1)) s' (a s)) ∧
    Θ' = inverseTransformDivisor J.p (T.B i) + ∑ s : I, Finsupp.single (J.E s) (1 - a s)

/-- A *terminal bridge* from a crepant junction `(p_i, Θ_i)` of `(X_i, B_i)`, `p_i : Y_i ⟶ X_i`,
to a crepant junction `(p_{i+1}, Θ_{i+1})` of `(X_{i+1}, B_{i+1})`, `p_{i+1} : Y_{i+1} ⟶ X_{i+1}`,
both extracting `I_∞` (that is, extracting `I(X_i, B_i)` and `I(X_{i+1}, B_{i+1})`): a canonical
divisor `K` of `Y_i`, the decreased boundary `Θ_i'` of `(p_i, Θ_i)`, and a finite relative
threefold programme `(V_k, Θ_k) → T_k ← (V_{k+1}, Θ_{k+1})`, `k < m`, over `Z_i` by
`π₀ = f_i ∘ p_i` from `(Y_i, Θ_i')` (`MMP.Fourfold.RelativeThreefoldProgram`), such that

* every contraction `g_k`, `k < m`, is small;
* its end is `(Y_{i+1}, Θ_{i+1})` with `π_m = f_i⁺ ∘ p_{i+1}`: there is an isomorphism
  `e : V_m ≅ Y_{i+1}` with `Θ_m = e⁻¹_* Θ_{i+1}` and `π_m = f_i⁺ ∘ p_{i+1} ∘ e`;
* its composite birational map `φ = e ∘ ψ_m : Y_i ⤏ Y_{i+1}`, where `ψ_k : Y_i ⤏ V_k` are the
  composites of the flips `(g_j⁺)⁻¹ ∘ g_j`, `j < k` (`ψ_0 = id`, `g_k⁺ ∘ ψ_{k+1} = g_k ∘ ψ_k`),
  satisfies `p_{i+1} ∘ φ = (f_i⁺)⁻¹ ∘ f_i ∘ p_i`, that is, `f_i⁺ ∘ p_{i+1} ∘ φ = f_i ∘ p_i`.

Its *moves* are the coefficient decrease `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` followed by the flips
`(V_k, Θ_k) → T_k ← (V_{k+1}, Θ_{k+1})`. -/
@[mmp "def_mmp_indexc_bridge"]
structure TerminalBridge (i : ℕ)
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {I' : Finset (Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ)))}
    (J : CrepantJunction (T.sX i) (T.B i) I) (J' : CrepantJunction (T.sX (i + 1)) (T.B (i + 1)) I')
    where
  coe_source : (I : Set _) = lowDiscrepancySet (T.sX i) (T.B i)
  coe_target : (I' : Set _) = lowDiscrepancySet (T.sX (i + 1)) (T.B (i + 1))
  /-- The canonical divisor of `Y_i` with which the programme is run. -/
  K : Divisor J.Y
  /-- The decreased boundary `Θ_i'` on `Y_i`. -/
  Θ' : QDivisor J.Y
  isDecreasedBoundary : IsDecreasedBoundary J Θ'
  /-- The finite relative programme over `Z_i` from `(Y_i, Θ_i')`. -/
  P : RelativeThreefoldProgram (J.p ≫ T.sX i) (T.sZ i) (J.p ≫ T.f i) K Θ'
  isSmallMorphism : ∀ k < P.m,
    IsSmallMorphism (modelStr (J.p ≫ T.sX i) P.sY k) (P.sT k) (P.g k)
  /-- The identification `e : V_m ≅ Y_{i+1}` of the end of the programme. -/
  e : modelSeq J.Y P.Y P.m ≅ J'.Y
  boundary_eq : P.boundary P.m = inverseTransformDivisor e.hom J'.Θ
  modelMap_eq : modelMap (J.p ≫ T.f i) P.πY P.m = e.hom ≫ J'.p ≫ T.fp i
  /-- The composite birational maps `ψ_k : Y_i ⤏ V_k` of the first `k` flips. -/
  ψ : ∀ k, RationalMap J.Y (modelSeq J.Y P.Y k)
  ψ_zero : ψ 0 = Scheme.RationalMap.id J.Y
  ψ_succ : ∀ k < P.m, (ψ (k + 1)).compHom (P.gp k) = (ψ k).compHom (P.g k)
  compHom_eq : (((ψ P.m).compHom e.hom).compHom J'.p).compHom (T.fp i) =
    (J.p ≫ T.f i).toRationalMap

namespace TerminalBridge

variable {i : ℕ} {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
  {I' : Finset (Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ)))}
  {J : CrepantJunction (T.sX i) (T.B i) I} {J' : CrepantJunction (T.sX (i + 1)) (T.B (i + 1)) I'}
  (β : TerminalBridge i J J')

/-- The composite birational map `φ : Y_i ⤏ Y_{i+1}` of a terminal bridge. -/
def compositeMap : RationalMap J.Y J'.Y := (β.ψ β.P.m).compHom β.e.hom

/-- The composite `Y_i ⤏ Y_{i+1} → X_{i+1} → Z_i` of the composite map of a bridge with
`p_{i+1}` and `f_i⁺` is the morphism `f_i ∘ p_i : Y_i → Z_i`. -/
theorem compHom_compositeMap :
    (β.compositeMap.compHom J'.p).compHom (T.fp i) = (J.p ≫ T.f i).toRationalMap :=
  β.compHom_eq

/-- A flip of a bridge is a threefold step diagram `V_k → T_k ← V_{k+1}` in which both `g_k` and
`g_k⁺` are small. -/
theorem isSmallMorphism_and_isSmallMorphism {k : ℕ} (hk : k < β.P.m) :
    IsSmallMorphism (modelStr (J.p ≫ T.sX i) β.P.sY k) (β.P.sT k) (β.P.g k) ∧
      IsSmallMorphism (β.P.sY k) (β.P.sT k) (β.P.gp k) :=
  ⟨β.isSmallMorphism k hk, (β.P.isThreefoldStepDiagram k hk).isSmallMorphism_plus⟩

end TerminalBridge

variable (T) in
/-- A *terminal chain* over a stabilized tail `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}`: a sequence
`(p_i, Θ_i)_{i ≥ 0}`, `p_i : Y_i ⟶ X_i`, of crepant junctions of `(X_i, B_i)` extracting `I_∞`
(that is, extracting finite sets `I_i = I(X_i, B_i)`), with divisors `E_{i,s} = c_{Y_i}(s)`,
together with, for each `i`, a terminal bridge from `(p_i, Θ_i)` to `(p_{i+1}, Θ_{i+1})`.

Its *models* (`MMP.Fourfold.StabilizedTail.TerminalChain.model`) are, in order, `(Y_0, Θ_0)`,
`(Y_0, Θ_0')`, the further models of the first bridge ending with `(Y_1, Θ_1)`, then
`(Y_1, Θ_1')`, and so on. Consecutive models are related by a *move*: a coefficient decrease
`(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` on the same variety, or a flip of a bridge, a threefold step diagram
`(V_k, Θ_k) → T_k ← (V_{k+1}, Θ_{k+1})` in which both `g_k` and `g_k⁺` are small
(`MMP.Fourfold.StabilizedTail.TerminalBridge.isSmallMorphism_and_isSmallMorphism`). -/
@[mmp "def_mmp_indexc_terminal_chain"]
structure TerminalChain where
  /-- The finite set `I_i = I(X_i, B_i)` extracted by the `i`-th junction. -/
  I : ∀ i, Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))
  /-- The crepant junction `(p_i, Θ_i)` of `(X_i, B_i)`. -/
  junction : ∀ i, CrepantJunction (T.sX i) (T.B i) (I i)
  /-- The terminal bridge from the `i`-th junction to the next. -/
  bridge : ∀ i, TerminalBridge i (junction i) (junction (i + 1))

namespace TerminalChain

variable (C : TerminalChain T)

/-- Every junction of a terminal chain extracts `I_∞`, that is, `I_i = I(X_i, B_i)`. -/
theorem coe_I (i : ℕ) : (C.I i : Set _) = lowDiscrepancySet (T.sX i) (T.B i) :=
  (C.bridge i).coe_source

/-- The indices of the models of a terminal chain: `(i, none)` is the junction `(Y_i, Θ_i)` and
`(i, some k)`, `k < m_i`, is the model `(V_k, Θ_k)` of the `i`-th bridge, `(i, some 0)` being the
decreased pair `(Y_i, Θ_i')`. In the lexicographic order these list the models of the chain. -/
abbrev ModelIndex : Type := Σ i : ℕ, Option (Fin (C.bridge i).P.m)

/-- The variety of a model of a terminal chain. -/
def model : C.ModelIndex → Scheme.{0}
  | ⟨i, none⟩ => (C.junction i).Y
  | ⟨i, some k⟩ => modelSeq (C.junction i).Y (C.bridge i).P.Y k

/-- The boundary of a model of a terminal chain. -/
def modelBoundary : ∀ x : C.ModelIndex, QDivisor (C.model x)
  | ⟨i, none⟩ => (C.junction i).Θ
  | ⟨i, some k⟩ => (C.bridge i).P.boundary k

/-- The structure morphism to `Spec ℂ` of a model of a terminal chain. -/
def modelStructure : ∀ x : C.ModelIndex, C.model x ⟶ Spec (.of ℂ)
  | ⟨i, none⟩ => (C.junction i).p ≫ T.sX i
  | ⟨i, some k⟩ => modelStr ((C.junction i).p ≫ T.sX i) (C.bridge i).P.sY k

/-- The boundary of the decreased pair `(Y_i, Θ_i')` is the decreased boundary of the `i`-th
junction. -/
theorem isDecreasedBoundary_modelBoundary (i : ℕ) (h : 0 < (C.bridge i).P.m) :
    IsDecreasedBoundary (C.junction i) (C.modelBoundary ⟨i, some ⟨0, h⟩⟩) :=
  (C.bridge i).isDecreasedBoundary

end TerminalChain

end StabilizedTail

end MMP.Fourfold
