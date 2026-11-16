module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain

/-!
# Labels and label coefficients of a terminal chain of fourfolds

Let `(p_i, Θ_i)_{i ≥ 0}`, `p_i : Y_i ⟶ X_i`, be a terminal chain over a stabilized small klt
tail `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` of fourfolds with stable low-discrepancy set `I_∞`, and
let `E_{0,s} = c_{Y_0}(s)`, `s ∈ I_∞`. The *labels* of the chain are the prime divisors `S_h` of
`Y_0` that are either strict transforms of components of `B_0` or one of the `E_{0,s}`; a label
is kept even when its coefficient becomes zero. For a model `M` of the chain,
`S_h^M = c_M(ord_{S_h})` is the centre on `M` of the valuation `ord_{S_h}`.

The *label coefficient* `b_h^M` is the coefficient of the boundary `Θ^M` of `M` at `S_h^M`, and
is zero if `S_h^M` is not a prime divisor of `M`. We write `b_h^{(i)} = b_h^{Y_i}` for the
coefficient at the `i`-th junction `(Y_i, Θ_i)`.

## Main definitions

* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabel`,
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.Label`: the labels of a terminal chain.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.labelValuation`: the valuation
  `ord_{S_h}`, regarded as a valuation of `k(X_0)`.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelCentre`: `P = S_h^M` for a model
  `M` and a prime divisor `P` of `M`.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelCoefficient`,
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsJunctionLabelCoefficient`: `b = b_h^M`
  and `b = b_h^{(i)}`.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.finite_label`: a terminal chain has finitely
  many labels.

## Implementation notes

* The valuation `ord_{S_h}` of `k(Y_0)` is regarded as a valuation of `k(X_0)` through the
  birational morphism `p_0`, as the valuations `s ∈ I_∞` are. It is carried to a valuation of
  `k(X_i)` through the identifications `k(X_j) ≅ k(Z_j) ≅ k(X_{j+1})`, `j < i`
  (`MMP.Fourfold.StepSequence.Corresponds`).
* The centre `c_M(ord_{S_h})` on a model `M` is recorded only when it is a prime divisor `P` of
  `M`, as the condition that `ord_P = ord_{S_h}` under the identification of function fields: a
  normalized divisorial valuation whose centre on the normal variety `M` is a prime divisor `P` is
  `ord_P`, and conversely. For the junction `M = Y_i` the function fields are compared in
  `k(X_i)` through `p_i`; for the model `M = V_k` of the `i`-th bridge, in `k(Z_i)` through the
  morphism `π_k : V_k ⟶ Z_i` of the programme of the bridge (which is birational; its
  dominance, needed to compare function fields, enters existentially).
* The label coefficient is accordingly a predicate `IsLabelCoefficient S x b`: either `S_h^M` is a
  prime divisor `P` of `M` and `b` is the coefficient of `Θ^M` at `P`, or no prime divisor of `M`
  is `S_h^M` and `b = 0`. The prime divisor `P` is determined by its valuation, so `b` is
  determined by `S` and `M`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

namespace StabilizedSmallKltTail

namespace TerminalChain

variable {T : StabilizedSmallKltTail} (C : TerminalChain T)

/-- A prime divisor `S` of `Y_0` is a *label* of the terminal chain: it is the strict transform
`p_0⁻¹_* Γ` of a component `Γ` of `B_0` (a prime divisor with nonzero coefficient), or one of the
divisors `E_{0,s} = c_{Y_0}(s)`, `s ∈ I_∞`. -/
@[mmp "def_oai4_boundary_label"]
def IsLabel (S : MMP.Mori.PrimeDivisor (C.junction 0).Y) : Prop :=
  (∃ Γ : MMP.Mori.PrimeDivisor (T.X 0), (T.B 0).coeff Γ ≠ 0 ∧
      inverseTransformPrimeDivisor (C.junction 0).p Γ = some S) ∨
    S ∈ Set.range (C.junction 0).E

/-- The labels `S_h` of a terminal chain. -/
@[mmp "def_oai4_boundary_label"]
abbrev Label : Type := {S : MMP.Mori.PrimeDivisor (C.junction 0).Y // C.IsLabel S}

/-- The divisors `E_{0,s}`, `s ∈ I_∞`, are labels. -/
theorem isLabel_E (s : C.I 0) : C.IsLabel ((C.junction 0).E s) :=
  Or.inr ⟨s, rfl⟩

/-- The strict transform of a component of `B_0` is a label. -/
theorem isLabel_of_inverseTransformPrimeDivisor_eq_some {Γ : MMP.Mori.PrimeDivisor (T.X 0)}
    (hΓ : (T.B 0).coeff Γ ≠ 0) {S : MMP.Mori.PrimeDivisor (C.junction 0).Y}
    (hS : inverseTransformPrimeDivisor (C.junction 0).p Γ = some S) : C.IsLabel S :=
  Or.inl ⟨Γ, hΓ, hS⟩

/-- A terminal chain has finitely many labels: they are strict transforms of the finitely many
components of `B_0`, or among the finitely many `E_{0,s}`, `s ∈ I_∞`. -/
theorem finite_label : Finite C.Label := by
  refine Set.Finite.to_subtype ((((T.B 0).support.finite_toSet.biUnion
    (t := fun Γ => {S | inverseTransformPrimeDivisor (C.junction 0).p Γ = some S})
    fun Γ _ => Set.Subsingleton.finite fun S hS S' hS' =>
      Option.some_injective _ (hS.symm.trans hS')).union
    (Set.finite_range (C.junction 0).E)).subset ?_)
  rintro S (⟨Γ, hΓ, hS⟩ | hS)
  · exact Or.inl (Set.mem_biUnion (Finsupp.mem_support_iff.mpr hΓ) hS)
  · exact Or.inr hS

variable {C}

/-- The valuation `ord_{S_h}` of a label, regarded as a valuation of `k(X_0)` through the
birational morphism `p_0 : Y_0 ⟶ X_0`. -/
@[mmp "def_oai4_boundary_label"]
def labelValuation (S : C.Label) :
    Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ)) :=
  haveI := (C.junction 0).isBirationalMorphism.isDominant
  S.1.valuationOver (C.junction 0).p

/-- The valuation of the label `E_{0,s}` is `s`. -/
@[simp] theorem labelValuation_E (s : C.I 0) :
    labelValuation ⟨(C.junction 0).E s, C.isLabel_E s⟩ = s.1 :=
  (C.junction 0).valuation_eq s

variable (C)

/-- The prime divisor `P` of the model `M` of a terminal chain indexed by `x` is the centre
`S_h^M = c_M(ord_{S_h})` of a label `S_h`: `ord_P = ord_{S_h}` under the identification of
function fields. For the junction `M = Y_i`, `ord_P` regarded in `k(X_i)` through `p_i` is
`ord_{S_h}` carried to `k(X_i)` (`MMP.Fourfold.StepSequence.Corresponds`); for the model
`M = V_k` of the `i`-th bridge, `ord_P` regarded in `k(Z_i)` through the morphism
`π_k : V_k ⟶ Z_i` of the programme of the bridge is `ord_{S_h}` carried to `k(Z_i)` (through
`k(X_i)` and `f_i`). -/
@[mmp "def_oai4_boundary_label"]
def IsLabelCentre (S : C.Label) : ∀ x : C.ModelIndex, MMP.Mori.PrimeDivisor (C.model x) → Prop
  | ⟨i, none⟩ => fun P : MMP.Mori.PrimeDivisor (C.junction i).Y =>
    haveI := (C.junction i).isBirationalMorphism.isDominant
    ∃ w, T.Corresponds i (labelValuation S) w ∧ P.valuationOver (C.junction i).p = w
  | ⟨i, some k⟩ => fun P : MMP.Mori.PrimeDivisor ((C.bridge i).P.model k) =>
    haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
    ∃ w, T.Corresponds i (labelValuation S) w ∧
      ∃ _ : IsDominant ((C.bridge i).P.toBase k),
        P.valuationOver ((C.bridge i).P.toBase k) = w.comap (functionFieldMap (T.f i))

/-- The *label coefficient* `b = b_h^M` of a label `S_h` at the model `M` indexed by `x`: either
the centre `S_h^M` is a prime divisor `P` of `M` and `b` is the coefficient of the boundary
`Θ^M` of `M` at `P`, or `S_h^M` is not a prime divisor of `M` and `b = 0`. -/
@[mmp "def_oai4_label_coefficient"]
def IsLabelCoefficient (S : C.Label) (x : C.ModelIndex) (b : ℚ) : Prop :=
  (∃ P : MMP.Mori.PrimeDivisor (C.model x),
    C.IsLabelCentre S x P ∧ (C.modelBoundary x).coeff P = b) ∨
  ((∀ P : MMP.Mori.PrimeDivisor (C.model x), ¬ C.IsLabelCentre S x P) ∧ b = 0)

/-- The coefficient `b = b_h^{(i)} = b_h^{Y_i}` of a label at the `i`-th junction
`(Y_i, Θ_i)`. -/
@[mmp "def_oai4_label_coefficient"]
abbrev IsJunctionLabelCoefficient (S : C.Label) (i : ℕ) (b : ℚ) : Prop :=
  C.IsLabelCoefficient S ⟨i, none⟩ b

variable {C}

/-- When the centre `S_h^M` is a prime divisor `P`, the coefficient of `Θ^M` at `P` is a label
coefficient. -/
theorem isLabelCoefficient_of_isLabelCentre {S : C.Label} {x : C.ModelIndex}
    {P : MMP.Mori.PrimeDivisor (C.model x)} (hP : C.IsLabelCentre S x P) :
    C.IsLabelCoefficient S x ((C.modelBoundary x).coeff P) :=
  Or.inl ⟨P, hP, rfl⟩

/-- When the centre `S_h^M` is not a prime divisor of `M`, the label coefficient is `0`. -/
theorem isLabelCoefficient_zero_of_forall_not_isLabelCentre {S : C.Label} {x : C.ModelIndex}
    (h : ∀ P : MMP.Mori.PrimeDivisor (C.model x), ¬ C.IsLabelCentre S x P) :
    C.IsLabelCoefficient S x 0 :=
  Or.inr ⟨h, rfl⟩

/-- Every label has a label coefficient at every model. -/
theorem exists_isLabelCoefficient (S : C.Label) (x : C.ModelIndex) :
    ∃ b, C.IsLabelCoefficient S x b := by
  by_cases h : ∃ P, C.IsLabelCentre S x P
  · obtain ⟨P, hP⟩ := h
    exact ⟨_, isLabelCoefficient_of_isLabelCentre hP⟩
  · exact ⟨0, isLabelCoefficient_zero_of_forall_not_isLabelCentre fun P hP => h ⟨P, hP⟩⟩

end TerminalChain

end StabilizedSmallKltTail

end MMP.Fourfold
