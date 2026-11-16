module

public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldTerminalChain

/-!
# Labels of a terminal chain, and pairs over a field of characteristic zero

Let `(p_i, Θ_i)_{i ≥ 0}`, `p_i : Y_i ⟶ X_i`, be a terminal chain over a stabilized tail
`(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` with common low-discrepancy set `I_∞`, and let
`E_{0,s} = c_{Y_0}(s)`, `s ∈ I_∞`. The *labels* of the chain are the prime divisors `S_h` of `Y_0`
that are either strict transforms of components of `B_0` or one of the `E_{0,s}`; a label is kept
even when its coefficient becomes zero. For a model `M` of the chain, `S_h^M = c_M(ord_{S_h})` is
the centre on `M` of the valuation `ord_{S_h}`, and when it is a prime divisor of `M`, the
*label coefficient* `b_h^M` is the coefficient of the boundary `Θ^M` of `M` at `S_h^M`. We write
`b_h^{(i)} = b_h^{Y_i}` for the coefficient at the `i`-th junction `(Y_i, Θ_i)`. A label is
*fixed* if the sequence `(b_h^{(i)})_{i ≥ 0}` is eventually constant, and *varying* otherwise.

Over a field `K` of characteristic zero, not necessarily algebraically closed, a *pair* `(S, B)`
is a normal variety `S` over `K` with an effective `ℚ`-divisor `B` such that `K_S + B` is
`ℚ`-Cartier; it is *klt* if `a(ξ; S, B) > 0` for every normalized divisorial valuation `ξ` of
`K(S)` over `S`. Over an algebraically closed field these are `MMP.Fourfold.IsPair` and
`MMP.Fourfold.IsKltPair`.

## Main definitions

* `MMP.Fourfold.StabilizedTail.TerminalChain.IsLabel`,
  `MMP.Fourfold.StabilizedTail.TerminalChain.Label`: the labels of a terminal chain.
* `MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelCentre`: `P = S_h^M` for a model `M`.
* `MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelCoefficient`,
  `MMP.Fourfold.StabilizedTail.TerminalChain.IsJunctionLabelCoefficient`: `b = b_h^M` and
  `b = b_h^{(i)}`.
* `MMP.Fourfold.StabilizedTail.TerminalChain.IsFixedLabel`,
  `MMP.Fourfold.StabilizedTail.TerminalChain.IsVaryingLabel`: fixed and varying labels.
* `MMP.Fourfold.IsCharZeroPair`, `MMP.Fourfold.IsCharZeroKltPair`: pairs and klt pairs over a
  field of characteristic zero.

## Main results

* `MMP.Fourfold.isPair_iff_isAlgClosed_and_isCharZeroPair`,
  `MMP.Fourfold.isKltPair_iff_isAlgClosed_and_isCharZeroKltPair`: over an algebraically closed
  field, these are the pairs and klt pairs of `MMP.Fourfold.IsPair` and `MMP.Fourfold.IsKltPair`.

## Implementation notes

* The valuation `ord_{S_h}` of `k(Y_0)` is regarded as a valuation of `k(X_0)` through the
  birational morphism `p_0` (`MMP.Fourfold.StabilizedTail.TerminalChain.labelValuation`), as the
  valuations `s ∈ I_∞` are. It is carried to a valuation of `k(X_i)` through the identifications
  `k(X_j) ≅ k(Z_j) ≅ k(X_{j+1})`, `j < i`
  (`MMP.Fourfold.StabilizedTail.IsTransportedValuationFrom`).
* The centre `c_M(ord_{S_h})` of a model `M` is recorded only when it is a prime divisor `P` of
  `M`, as the condition that `ord_P = ord_{S_h}` under the identification of function fields: a
  normalized divisorial valuation whose centre on the normal variety `M` is a prime divisor `P` is
  `ord_P`, and conversely. For the junction `M = Y_i` the function fields are compared in
  `k(X_i)` through `p_i`; for the model `M = V_k` of the `i`-th bridge, in `k(Z_i)` through the
  morphism `π_k : V_k ⟶ Z_i` of the programme of the bridge (which is birational; its
  dominance, needed to compare function fields, enters existentially).
* The label coefficient is accordingly a predicate `IsLabelCoefficient S x b`: `S_h^M` is a prime
  divisor `P` of `M` and `b` is the coefficient of `Θ^M` at `P`. The prime divisor `P` is
  determined by its valuation, so `b` is determined by `S` and `M`. "`(b_h^{(i)})_i` is
  eventually constant" reads: there are `c` and `N` with `b_h^{(i)} = c` for all `i ≥ N`.
* For pairs over a field of characteristic zero, the canonical divisors of all models are cut out
  by one rational top form inside the log discrepancy `MMP.Intersection.IsLogDiscrepancy`; whether
  `K_S + B` is `ℚ`-Cartier does not depend on the canonical divisor chosen
  (`MMP.Mori.QDivisor.isQCartier_add_iff_of_linearlyEquivalent`). A normalized divisorial
  valuation of `K(S)` over `S` is a divisor `(W, g, E)` over `S` with `g` proper, and
  `MMP.Intersection.IsLogDiscrepancy` holds only for such divisors.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Pairs over a field of characteristic zero -/

section CharZeroPair

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A *pair* `(X, B)` over a field `k` of characteristic zero, not necessarily algebraically
closed: `X` is a normal variety over `k` and `B` is an effective `ℚ`-divisor on `X` such that
`K_X + B` is `ℚ`-Cartier. -/
@[mmp "def_mmp_indexc_char_zero_pair"]
structure IsCharZeroPair (B : QDivisor X) : Prop where
  /-- The field `k` has characteristic zero. -/
  charZero : CharZero k
  /-- `(X, B)` is a pair: `X` is a normal variety over `k` and `K_X + B` is `ℚ`-Cartier. -/
  isPair : MMP.Mori.IsPair sX B
  /-- The divisor `B` is effective. -/
  nonneg : ∀ P, 0 ≤ B.coeff P

/-- A pair `(X, B)` over a field of characteristic zero is *klt* if `a(ξ; X, B) > 0` for every
normalized divisorial valuation `ξ` of `k(X)` over `X`, realized as a divisor `(W, g, E)` over `X`
with `g` proper. -/
@[mmp "def_mmp_indexc_char_zero_pair"]
def IsCharZeroKltPair (B : QDivisor X) : Prop :=
  IsCharZeroPair sX B ∧ ∀ (n : ℕ) (D : DivisorOver k sX) (a : ℝ),
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a → 0 < a

variable {sX}

/-- A klt pair over a field of characteristic zero is a pair over that field. -/
theorem IsCharZeroKltPair.isCharZeroPair {B : QDivisor X} (h : IsCharZeroKltPair sX B) :
    IsCharZeroPair sX B :=
  h.1

/-- The log discrepancy of a klt pair over a field of characteristic zero at any divisor over `X`
is positive. -/
theorem IsCharZeroKltPair.pos {B : QDivisor X} (h : IsCharZeroKltPair sX B) {n : ℕ}
    {D : DivisorOver k sX} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a) : 0 < a :=
  h.2 n D a ha

omit [IsIntegral X] in
/-- Over an algebraically closed field, the pairs over a field of characteristic zero are the
pairs `MMP.Fourfold.IsPair`. -/
theorem isPair_iff_isAlgClosed_and_isCharZeroPair {B : QDivisor X} :
    IsPair sX B ↔ IsAlgClosed k ∧ IsCharZeroPair sX B :=
  ⟨fun h => ⟨h.isAlgClosed, h.charZero, h.isPair, h.nonneg⟩,
    fun h => ⟨h.1, h.2.charZero, h.2.isPair, h.2.nonneg⟩⟩

/-- Over an algebraically closed field, the klt pairs over a field of characteristic zero are the
klt pairs `MMP.Fourfold.IsKltPair`. -/
theorem isKltPair_iff_isAlgClosed_and_isCharZeroKltPair {B : QDivisor X} :
    IsKltPair sX B ↔ IsAlgClosed k ∧ IsCharZeroKltPair sX B := by
  unfold IsKltPair IsCharZeroKltPair
  rw [isPair_iff_isAlgClosed_and_isCharZeroPair, and_assoc]

/-- A klt pair over an algebraically closed field is a klt pair over a field of characteristic
zero. -/
theorem IsKltPair.isCharZeroKltPair {B : QDivisor X} (h : IsKltPair sX B) :
    IsCharZeroKltPair sX B :=
  (isKltPair_iff_isAlgClosed_and_isCharZeroKltPair.mp h).2

end CharZeroPair

/-! ### Labels of a terminal chain -/

namespace StabilizedTail

variable (T : StabilizedTail)

/-- The valuation `w` of `k(X_i)` corresponds to the valuation `ν` of `k(X_0)` under the
identifications `k(X_j) ≅ k(Z_j) ≅ k(X_{j+1})`, `j < i`
(`MMP.Fourfold.StabilizedTail.IsTransportedValuation`). -/
def IsTransportedValuationFrom :
    ∀ i, Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ)) →
      Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)) → Prop
  | 0, ν, w => w = ν
  | i + 1, ν, w => ∃ u, IsTransportedValuationFrom i ν u ∧ T.IsTransportedValuation i u w

variable {T}

/-- A valuation of `k(X_0)` is transported to `w` in `k(X_0)` exactly when it equals `w`. -/
@[simp]
theorem isTransportedValuationFrom_zero
    {ν w : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))} :
    T.IsTransportedValuationFrom 0 ν w ↔ w = ν :=
  Iff.rfl

/-- A valuation `ν` of `k(X_0)` is transported to `w` in `k(X_{i+1})` exactly when it is
transported to some `u` in `k(X_i)` corresponding to `w` under `k(X_i) ≅ k(Z_i) ≅ k(X_{i+1})`. -/
theorem isTransportedValuationFrom_succ {i : ℕ}
    {ν : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
    {w : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))} :
    T.IsTransportedValuationFrom (i + 1) ν w ↔
      ∃ u, T.IsTransportedValuationFrom i ν u ∧ T.IsTransportedValuation i u w :=
  Iff.rfl

namespace TerminalChain

variable (C : TerminalChain T)

/-- A prime divisor `S` of `Y_0` is a *label* of the terminal chain: it is the strict transform
`p_0⁻¹_* Γ` of a component `Γ` of `B_0` (a prime divisor with nonzero coefficient), or one of the
divisors `E_{0,s} = c_{Y_0}(s)`, `s ∈ I_∞`. -/
@[mmp "def_mmp_indexc_label"]
def IsLabel (S : MMP.Mori.PrimeDivisor (C.junction 0).Y) : Prop :=
  (∃ Γ : MMP.Mori.PrimeDivisor (T.X 0), (T.B 0).coeff Γ ≠ 0 ∧
      inverseTransformPrimeDivisor (C.junction 0).p Γ = some S) ∨
    S ∈ Set.range (C.junction 0).E

/-- The labels `S_h` of a terminal chain. -/
@[mmp "def_mmp_indexc_label"]
abbrev Label : Type := {S : MMP.Mori.PrimeDivisor (C.junction 0).Y // C.IsLabel S}

/-- The divisors `E_{0,s}`, `s ∈ I_∞`, are labels. -/
theorem isLabel_E (s : C.I 0) : C.IsLabel ((C.junction 0).E s) :=
  Or.inr ⟨s, rfl⟩

/-- The strict transform of a component of `B_0` is a label. -/
theorem isLabel_of_inverseTransformPrimeDivisor_eq_some {Γ : MMP.Mori.PrimeDivisor (T.X 0)}
    (hΓ : (T.B 0).coeff Γ ≠ 0) {S : MMP.Mori.PrimeDivisor (C.junction 0).Y}
    (hS : inverseTransformPrimeDivisor (C.junction 0).p Γ = some S) : C.IsLabel S :=
  Or.inl ⟨Γ, hΓ, hS⟩

variable {C}

/-- The valuation `ord_{S_h}` of a label, regarded as a valuation of `k(X_0)` through the
birational morphism `p_0 : Y_0 ⟶ X_0`. -/
def labelValuation (S : C.Label) :
    Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ)) :=
  haveI := (C.junction 0).isBirationalMorphism.isDominant
  S.1.valuationOver (C.junction 0).p

/-- The valuation of the label `E_{0,s}` is `s`. -/
theorem labelValuation_E (s : C.I 0) :
    labelValuation ⟨(C.junction 0).E s, C.isLabel_E s⟩ = s.1 :=
  (C.junction 0).valuation_eq s

variable (C)

/-- The prime divisor `P` of the model `M` of a terminal chain indexed by `x` is the centre
`S_h^M = c_M(ord_{S_h})` of a label `S_h`: `ord_P = ord_{S_h}` under the identification of
function fields. For the junction `M = Y_i`, `ord_P` regarded in `k(X_i)` through `p_i` is
`ord_{S_h}` carried to `k(X_i)`; for the model `M = V_k` of the `i`-th bridge, `ord_P` regarded
in `k(Z_i)` through the morphism `π_k : V_k ⟶ Z_i` of the programme of the bridge is
`ord_{S_h}` carried to `k(Z_i)` (through `k(X_i)` and `f_i`). -/
@[mmp "def_mmp_indexc_label"]
def IsLabelCentre (S : C.Label) : ∀ x : C.ModelIndex, MMP.Mori.PrimeDivisor (C.model x) → Prop
  | ⟨i, none⟩ => fun P : MMP.Mori.PrimeDivisor (C.junction i).Y =>
    haveI := (C.junction i).isBirationalMorphism.isDominant
    ∃ w, T.IsTransportedValuationFrom i (labelValuation S) w ∧
      P.valuationOver (C.junction i).p = w
  | ⟨i, some k⟩ => fun P : MMP.Mori.PrimeDivisor (modelSeq (C.junction i).Y (C.bridge i).P.Y k) =>
    haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
    ∃ w, T.IsTransportedValuationFrom i (labelValuation S) w ∧
      ∃ _ : IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k),
        P.valuationOver (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k) =
          w.comap (functionFieldMap (T.f i))

/-- The *label coefficient* `b = b_h^M` of a label `S_h` at the model `M` indexed by `x`: the
centre `S_h^M` is a prime divisor `P` of `M`, and `b` is the coefficient of the boundary `Θ^M`
of `M` at `P`. -/
@[mmp "def_mmp_indexc_label_coefficient"]
def IsLabelCoefficient (S : C.Label) (x : C.ModelIndex) (b : ℚ) : Prop :=
  ∃ P : MMP.Mori.PrimeDivisor (C.model x),
    C.IsLabelCentre S x P ∧ (C.modelBoundary x).coeff P = b

/-- The coefficient `b = b_h^{(i)} = b_h^{Y_i}` of a label at the `i`-th junction
`(Y_i, Θ_i)`. -/
@[mmp "def_mmp_indexc_label_coefficient"]
abbrev IsJunctionLabelCoefficient (S : C.Label) (i : ℕ) (b : ℚ) : Prop :=
  C.IsLabelCoefficient S ⟨i, none⟩ b

/-- A label `S_h` of a terminal chain is *fixed* if the sequence `(b_h^{(i)})_{i ≥ 0}` of its
coefficients at the junctions is eventually constant: there are `c` and `N` with `b_h^{(i)} = c`
for every `i ≥ N`. -/
@[mmp "def_mmp_indexc_fixed_label"]
def IsFixedLabel (S : C.Label) : Prop :=
  ∃ (c : ℚ) (N : ℕ), ∀ i ≥ N, C.IsJunctionLabelCoefficient S i c

/-- A label of a terminal chain is *varying* if it is not fixed. -/
@[mmp "def_mmp_indexc_varying_label"]
def IsVaryingLabel (S : C.Label) : Prop :=
  ¬ C.IsFixedLabel S

/-- A label is varying if and only if it is not fixed. -/
theorem isVaryingLabel_iff_not_isFixedLabel (S : C.Label) :
    C.IsVaryingLabel S ↔ ¬ C.IsFixedLabel S :=
  Iff.rfl

/-- A label is not varying if and only if it is fixed. -/
theorem not_isVaryingLabel_iff (S : C.Label) : ¬ C.IsVaryingLabel S ↔ C.IsFixedLabel S :=
  not_not

/-- Every label is fixed or varying. -/
theorem isFixedLabel_or_isVaryingLabel (S : C.Label) :
    C.IsFixedLabel S ∨ C.IsVaryingLabel S :=
  em _

end TerminalChain

end StabilizedTail

end MMP.Fourfold
