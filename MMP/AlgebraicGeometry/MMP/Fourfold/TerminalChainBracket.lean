module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainDifficulty

/-!
# Weights of valuations, surface brackets and weighted bad sets of flips of fourfolds

Let `(p_i, Θ_i)_{i ≥ 0}`, `p_i : Y_i ⟶ X_i`, be a terminal chain over a stabilized small klt
tail `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` of fourfolds, with labels `S_h`, and let `w` be the
weight function `w(u) = ⌈N max{u, 0}⌉` at a scale `N`.

For a model `(Y, Θ)` of the chain and a normalized divisorial valuation `v` of `ℂ(Y)` exceptional
over `Y`, the *weight* of `v` is `w_v(Y, Θ) = w(2 - a(v; Y, Θ))`; only exceptional valuations
over `Y` are given a weight. At a positive scale it vanishes exactly when `a(v; Y, Θ) ≥ 2`.

For a model `(Y, Θ)` of a prepared chain and an irreducible surface `V ⊆ Y`, the *bracket* at `V`
is `β_V(Y, Θ) = ∑_{c_Y(v) = V} w_v - ∑_h r_{V,h} d_h`, the first sum running over the normalized
divisorial valuations with centre `V` (a finitely supported sum, `0` if the support were
infinite) and the second over the finitely many labels, with branch numbers `r_{V,h}` and default
echo weights `d_h`.

For a small terminal flip `(Y⁻, Θ⁻) ⤏ (Y⁺, Θ⁺)` of a bridge of a prepared chain, written as a
step diagram `Y⁻ → Z ← Y⁺` with full bad loci `W^±`, the *weighted bad set* `𝒜₀` is the set of
normalized divisorial valuations `v` exceptional over both `Y⁻` and `Y⁺` with `c_{Y⁻}(v) ⊆ W⁻`
and `w_v(Y⁻, Θ⁻) + w_v(Y⁺, Θ⁺) > 0`.

## Main definitions

* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsValuationWeight`: `w = w_v(Y, Θ)` on a
  model of a terminal chain.
* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.IsSurfaceBracket`: `β = β_V(Y, Θ)` on a
  model of a prepared chain.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.flipTarget`,
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.flipTargetMap`: the model reached by a flip
  of a bridge, and its morphism to the base of the flip.
* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.FlipMove`: the small terminal flips of the
  bridges of a prepared chain.
* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.flipBadSet`: the weighted bad set `𝒜₀` of
  a flip.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsValuationWeight.exists_eq_zero_iff`: at a
  positive scale, `w_v = 0` if and only if `a(v; Y, Θ) ≥ 2`.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.isSmallMorphism_flipSourceMap`: the
  morphism `Y⁻ ⟶ Z` of a flip of a bridge is small (the morphism `Y⁺ ⟶ Z` of a step diagram is
  small by definition).

## Implementation notes

* Log discrepancies, branch numbers and default echo weights on a model are predicates on their
  values, so weights and brackets are too. The weight of `v` at scale `N` is
  `MMP.Fourfold.difficultyWeight N (2 - a)` for `a` the log discrepancy of `v`
  (`MMP.Fourfold.IsValuationLogDiscrepancy`); that `v` is a normalized divisorial valuation
  exceptional over `Y` is `MMP.Intersection.IsExceptionalValuation`. The weight is stated on any
  model of a terminal chain, at any scale; the source takes the fixed admissible scale.
* The bracket is stated at every irreducible closed subset `V` of the model, as the branch number
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelBranchNumber` is; the source
  considers irreducible surfaces, `topologicalKrullDim V = 2`. A valuation has centre `V` when
  `MMP.Intersection.IsCentre` holds for `V`. The first sum is the finitely supported sum `∑ᶠ`
  (`0` if the support were infinite) of chosen weights `w_v`, at the admissible scale of the
  prepared chain, over the valuations with centre `V`; the second is the sum over the labels,
  which are finitely many (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.finite_label`), so
  `∑ᶠ` is the finite sum.
* A flip of a bridge of a prepared chain is the `k`-th flip `V_k → T_k ← V_{k+1}`, `k < m_i`, of
  the `i`-th bridge with `i ≥ i₀`. Its source is the model `(i, some k)` and its target the model
  `(i, some (k + 1))` when `k + 1 < m_i` and the junction `(i + 1, none)` when `k + 1 = m_i`,
  through the identification `e : V_{m_i} ≅ Y_{i+1}` of the bridge. The step diagram
  `Y⁻ → Z ← Y⁺` is `g_k : V_k ⟶ T_k` with `g_k⁺ : V_{k+1} ⟶ T_k`, composed with `e⁻¹` in the
  second case; the full bad loci `W^±` are `MMP.Fourfold.badLocusMinus` and
  `MMP.Fourfold.badLocusPlus` of this pair of morphisms.
* In the weighted bad set the valuations are valuations of `ℂ(Y⁻)`; a valuation `v⁺` of `ℂ(Y⁺)`
  is the same valuation when their restrictions to `ℂ(Z)` agree (both `Y^± ⟶ Z` are birational).
  The weight predicate already contains that the valuation is exceptional over the model. The
  centre condition `c_{Y⁻}(v) ⊆ W⁻` is `MMP.Intersection.IsCentre` for an irreducible closed
  subset contained in `W⁻`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

namespace StabilizedSmallKltTail

namespace TerminalChain

variable {T : StabilizedSmallKltTail} (C : TerminalChain T)

/-! ### Weights of valuations -/

/-- `w` is the *weight* `w_v(Y, Θ) = w(2 - a(v; Y, Θ))` of a normalized divisorial valuation `v`
of `ℂ(Y)` exceptional over `Y`, for the model `(Y, Θ)` of the terminal chain indexed by `x`, at
scale `N` (the fixed admissible scale): `a = a(v; Y, Θ)` is the log discrepancy of `v` and
`w = w(2 - a)` (`MMP.Fourfold.difficultyWeight`). Only valuations exceptional over `Y` are given
a weight. -/
@[mmp "def_oai4_valuation_weight"]
def IsValuationWeight (N : ℕ) (x : C.ModelIndex)
    (v : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ))) (w : ℕ) : Prop :=
  MMP.Intersection.IsExceptionalValuation ℂ (C.modelStructure x) v ∧
    ∃ a : ℝ, IsValuationLogDiscrepancy (C.modelStructure x) (C.modelBoundary x) v a ∧
      w = difficultyWeight N (2 - a)

variable {C}

/-- Only valuations exceptional over the model are given a weight. -/
theorem IsValuationWeight.isExceptionalValuation {N : ℕ} {x : C.ModelIndex}
    {v : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ))} {w : ℕ}
    (hw : C.IsValuationWeight N x v w) :
    MMP.Intersection.IsExceptionalValuation ℂ (C.modelStructure x) v :=
  hw.1

/-- At a positive scale, the weight `w_v` vanishes exactly when the log discrepancy
`a(v; Y, Θ)` it is computed from is at least `2`. -/
theorem IsValuationWeight.exists_eq_zero_iff {N : ℕ} (hN : 0 < N) {x : C.ModelIndex}
    {v : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ))} {w : ℕ}
    (hw : C.IsValuationWeight N x v w) :
    ∃ a : ℝ, IsValuationLogDiscrepancy (C.modelStructure x) (C.modelBoundary x) v a ∧
      (w = 0 ↔ 2 ≤ a) := by
  obtain ⟨-, a, ha, rfl⟩ := hw
  exact ⟨a, ha, by rw [difficultyWeight_eq_zero_iff hN, sub_nonpos]⟩

end TerminalChain

/-! ### Surface brackets -/

namespace PreparedChain

variable {T : StabilizedSmallKltTail} (Q : PreparedChain T)

/-- `β` is the *bracket* `β_V(Y, Θ) = ∑_{c_Y(v) = V} w_v - ∑_h r_{V,h} d_h` at an irreducible
closed subset `V` (an irreducible surface in the source) of the model `(Y, Θ)` of the prepared
chain indexed by `x`: the first sum, over the normalized divisorial valuations `v` of `ℂ(Y)` with
centre `V`, is the finitely supported sum (`0` if the support were infinite) of their weights
`w_v` (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsValuationWeight`) at the fixed
admissible scale, and the second runs over the finitely many labels `S_h`, with branch numbers
`r_{V,h}` (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelBranchNumber`) and default
echo weights `d_h` (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelDefault`). -/
@[mmp "def_oai4_c2_surface_bracket"]
def IsSurfaceBracket (x : Q.ModelIndex) (V : IrreducibleCloseds (Q.chain.model x.1)) (β : ℤ) :
    Prop :=
  ∃ (w : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) → ℕ)
    (r d : Q.chain.Label → ℕ),
    (∀ v, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V →
      Q.chain.IsValuationWeight Q.scale x.1 v (w v)) ∧
    (∀ S, Q.chain.IsLabelBranchNumber S x.1 V (r S)) ∧
    (∀ S, Q.chain.IsLabelDefault Q.scale S x.1 (d S)) ∧
    β = ((∑ᶠ (v) (_ : MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V), w v : ℕ) :
        ℤ) - ((∑ᶠ S, r S * d S : ℕ) : ℤ)

end PreparedChain

/-! ### Flips of bridges -/

namespace TerminalChain

variable {T : StabilizedSmallKltTail} (C : TerminalChain T)

/-- The index of the model `V_{k+1}` reached by the `k`-th flip `V_k → T_k ← V_{k+1}` of the
`i`-th bridge, by cases on the decision of `k + 1 < m_i`. -/
def flipTargetOf (i : ℕ) (k : Fin (C.bridge i).P.m) :
    Decidable (k.1 + 1 < (C.bridge i).P.m) → C.ModelIndex
  | isTrue h => ⟨i, some ⟨k.1 + 1, h⟩⟩
  | isFalse _ => ⟨i + 1, none⟩

/-- The index of the model `V_{k+1}` reached by the `k`-th flip `V_k → T_k ← V_{k+1}` of the
`i`-th bridge: the model `(i, some (k + 1))` if `k + 1 < m_i`, and otherwise the junction
`(i + 1, none)`, the end of the bridge. -/
def flipTarget (i : ℕ) (k : Fin (C.bridge i).P.m) : C.ModelIndex :=
  C.flipTargetOf i k inferInstance

/-- If `k + 1 < m_i`, the `k`-th flip of the `i`-th bridge reaches the model
`(i, some (k + 1))`. -/
theorem flipTarget_of_lt {i : ℕ} {k : Fin (C.bridge i).P.m} (h : k.1 + 1 < (C.bridge i).P.m) :
    C.flipTarget i k = ⟨i, some ⟨k.1 + 1, h⟩⟩ := by
  unfold flipTarget
  generalize (inferInstance : Decidable (k.1 + 1 < (C.bridge i).P.m)) = d
  cases d with
  | isTrue _ => rfl
  | isFalse h' => exact absurd h h'

/-- If `¬ k + 1 < m_i`, the `k`-th flip of the `i`-th bridge reaches the junction
`(i + 1, none)`. -/
theorem flipTarget_of_not_lt {i : ℕ} {k : Fin (C.bridge i).P.m}
    (h : ¬ k.1 + 1 < (C.bridge i).P.m) : C.flipTarget i k = ⟨i + 1, none⟩ := by
  unfold flipTarget
  generalize (inferInstance : Decidable (k.1 + 1 < (C.bridge i).P.m)) = d
  cases d with
  | isTrue h' => exact absurd h' h
  | isFalse _ => rfl

/-- The model reached by the `k`-th flip of the `i`-th bridge lies over an index at least `i`. -/
theorem fst_flipTarget_ge (i : ℕ) (k : Fin (C.bridge i).P.m) : i ≤ (C.flipTarget i k).1 := by
  unfold flipTarget
  generalize (inferInstance : Decidable (k.1 + 1 < (C.bridge i).P.m)) = d
  cases d <;> simp [flipTargetOf]

/-- The morphism `V_{k+1} ⟶ T_k` of the `k`-th flip of the `i`-th bridge, by cases on the
decision of `k + 1 < m_i`. -/
def flipTargetMapOf (i : ℕ) (k : Fin (C.bridge i).P.m) :
    (d : Decidable (k.1 + 1 < (C.bridge i).P.m)) →
      C.model (C.flipTargetOf i k d) ⟶ (C.bridge i).P.T k
  | isTrue _ => (C.bridge i).P.gp k
  | isFalse _ => (C.bridge i).e.inv ≫
      eqToHom (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) (by omega :
        (C.bridge i).P.m = k.1 + 1)) ≫ (C.bridge i).P.gp k

/-- The morphism `g_k⁺ : V_{k+1} ⟶ T_k` of the `k`-th flip of the `i`-th bridge, on the model
`C.flipTarget i k`: `g_k⁺` itself if `k + 1 < m_i`, and `g_k⁺ ∘ e⁻¹ : Y_{i+1} ⟶ T_k` otherwise,
for the identification `e : V_{m_i} ≅ Y_{i+1}` of the bridge. -/
def flipTargetMap (i : ℕ) (k : Fin (C.bridge i).P.m) :
    C.model (C.flipTarget i k) ⟶ (C.bridge i).P.T k :=
  C.flipTargetMapOf i k inferInstance

/-- The morphism `V_{k+1} ⟶ T_k` of the `k`-th flip of the `i`-th bridge is dominant, for either
decision of `k + 1 < m_i`. -/
theorem isDominant_flipTargetMapOf (i : ℕ) (k : Fin (C.bridge i).P.m)
    (d : Decidable (k.1 + 1 < (C.bridge i).P.m)) : IsDominant (C.flipTargetMapOf i k d) := by
  have hD : IsDominant ((C.bridge i).P.gp k) :=
    ((C.bridge i).P.isFourfoldStepDiagram k k.2).isBirationalMorphism_plus.isDominant
  cases d with
  | isTrue _ => exact hD
  | isFalse h =>
    have h1 : IsDominant (C.bridge i).e.inv := inferInstance
    have h2 : IsDominant (eqToHom (congrArg (modelSeq (C.junction i).Y
      (C.bridge i).P.Y) (by omega : (C.bridge i).P.m = k.1 + 1))) := inferInstance
    have h3 : IsDominant (eqToHom (congrArg (modelSeq (C.junction i).Y
        (C.bridge i).P.Y) (by omega : (C.bridge i).P.m = k.1 + 1)) ≫ (C.bridge i).P.gp k) :=
      ⟨hD.denseRange.comp h2.denseRange ((C.bridge i).P.gp k).continuous⟩
    exact ⟨h3.denseRange.comp h1.denseRange (Scheme.Hom.continuous _)⟩

/-- The morphism `V_{k+1} ⟶ T_k` of a flip of a bridge is dominant. -/
theorem isDominant_flipTargetMap (i : ℕ) (k : Fin (C.bridge i).P.m) :
    IsDominant (C.flipTargetMap i k) :=
  C.isDominant_flipTargetMapOf i k _

/-- The base `T_k` of a flip of a bridge is an integral scheme. -/
theorem isIntegral_flipBase (i : ℕ) (k : Fin (C.bridge i).P.m) :
    IsIntegral ((C.bridge i).P.T k) :=
  ((C.bridge i).P.isFourfoldStepDiagram k k.2).isNormalVariety_target.1.toIsIntegral

/-- The morphism `g_k : V_k ⟶ T_k` of a flip of a bridge is dominant. -/
theorem isDominant_flipSourceMap (i : ℕ) (k : Fin (C.bridge i).P.m) :
    IsDominant ((C.bridge i).P.g k) :=
  ((C.bridge i).P.isFourfoldStepDiagram k k.2).isBirationalMorphism_minus.isDominant

/-- The morphism `g_k : V_k ⟶ T_k` of a flip of a bridge is small. -/
theorem isSmallMorphism_flipSourceMap (i : ℕ) (k : Fin (C.bridge i).P.m) :
    IsSmallMorphism ((C.bridge i).P.modelStructure k) ((C.bridge i).P.sT k)
      ((C.bridge i).P.g k) :=
  (C.bridge i).isSmallMorphism k k.2

end TerminalChain

namespace PreparedChain

variable {T : StabilizedSmallKltTail} (Q : PreparedChain T)

/-- The *small terminal flips* of the bridges of a prepared chain: the flips
`V_k → T_k ← V_{k+1}`, `k < m_i`, of the `i`-th bridges with `i ≥ i₀`. Both morphisms of each
are small (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.isSmallMorphism_flipSourceMap`
and `MMP.Fourfold.IsFourfoldStepDiagram.isSmallMorphism_plus`). -/
abbrev FlipMove : Type := {p : Σ i : ℕ, Fin (Q.chain.bridge i).P.m // Q.start ≤ p.1}

namespace FlipMove

variable {Q} (μ : Q.FlipMove)

/-- The source `(Y⁻, Θ⁻) = (V_k, Θ_k)` of a flip, a model of the prepared chain. -/
def source : Q.ModelIndex := ⟨⟨μ.1.1, some μ.1.2⟩, μ.2⟩

/-- The target `(Y⁺, Θ⁺)` of a flip, a model of the prepared chain: `(V_{k+1}, Θ_{k+1})`, which
is the next junction `(Y_{i+1}, Θ_{i+1})` when `k + 1 = m_i`. -/
def target : Q.ModelIndex :=
  ⟨Q.chain.flipTarget μ.1.1 μ.1.2, μ.2.trans (Q.chain.fst_flipTarget_ge _ _)⟩

/-- The base `Z = T_k` of the step diagram `Y⁻ → Z ← Y⁺` of a flip. -/
abbrev base : Scheme.{0} := (Q.chain.bridge μ.1.1).P.T μ.1.2

/-- The morphism `Y⁻ ⟶ Z` of a flip. -/
def sourceMap : Q.chain.model μ.source.1 ⟶ μ.base := (Q.chain.bridge μ.1.1).P.g μ.1.2

/-- The morphism `Y⁺ ⟶ Z` of a flip. -/
def targetMap : Q.chain.model μ.target.1 ⟶ μ.base := Q.chain.flipTargetMap μ.1.1 μ.1.2

/-- The base `Z` of a flip is an integral scheme. -/
instance isIntegral_base : IsIntegral μ.base := Q.chain.isIntegral_flipBase _ _

/-- The morphism `Y⁻ ⟶ Z` of a flip is dominant. -/
instance isDominant_sourceMap : IsDominant μ.sourceMap := Q.chain.isDominant_flipSourceMap _ _

/-- The morphism `Y⁺ ⟶ Z` of a flip is dominant. -/
instance isDominant_targetMap : IsDominant μ.targetMap := Q.chain.isDominant_flipTargetMap _ _

/-- The full bad locus `W⁻ ⊆ Y⁻` of a flip. -/
abbrev badLocusSource : Closeds (Q.chain.model μ.source.1) :=
  badLocusMinus μ.sourceMap μ.targetMap

/-- The full bad locus `W⁺ ⊆ Y⁺` of a flip. -/
abbrev badLocusTarget : Closeds (Q.chain.model μ.target.1) :=
  badLocusPlus μ.sourceMap μ.targetMap

end FlipMove

/-- The *weighted bad set* `𝒜₀` of a small terminal flip `(Y⁻, Θ⁻) ⤏ (Y⁺, Θ⁺)` of a bridge of a
prepared chain, written as a step diagram `Y⁻ → Z ← Y⁺` with full bad loci `W^±`: the set of
normalized divisorial valuations `v` of `ℂ(Y⁻)` which are exceptional over `Y⁻` and over `Y⁺`
(as a valuation `v⁺` of `ℂ(Y⁺)` with the same restriction to `ℂ(Z)`), whose centre `c_{Y⁻}(v)`
lies in `W⁻`, and such that `w_v(Y⁻, Θ⁻) + w_v(Y⁺, Θ⁺) > 0`, for the weights
`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsValuationWeight` at the admissible scale. -/
@[mmp "def_oai4_flip_weighted_bad_set"]
def flipBadSet (μ : Q.FlipMove) :
    Set (Valuation (Q.chain.model μ.source.1).functionField (WithZero (Multiplicative ℤ))) :=
  {v | (∃ Z : IrreducibleCloseds (Q.chain.model μ.source.1),
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure μ.source.1) v Z ∧
        (Z : Set (Q.chain.model μ.source.1)) ⊆ μ.badLocusSource) ∧
    ∃ v' : Valuation (Q.chain.model μ.target.1).functionField (WithZero (Multiplicative ℤ)),
      v'.comap (functionFieldMap μ.targetMap) = v.comap (functionFieldMap μ.sourceMap) ∧
      ∃ w w' : ℕ, Q.chain.IsValuationWeight Q.scale μ.source.1 v w ∧
        Q.chain.IsValuationWeight Q.scale μ.target.1 v' w' ∧ 0 < w + w'}

end PreparedChain

end StabilizedSmallKltTail

end MMP.Fourfold
