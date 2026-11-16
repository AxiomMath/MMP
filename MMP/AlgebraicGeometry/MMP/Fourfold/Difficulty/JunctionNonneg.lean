module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.JunctionVaryingExcessBound
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.EchoSetting
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.WeightSupportFinite
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.FirstDefaultError
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.MultiplicityBound
import MMP.AlgebraicGeometry.Singularities.WeightedMonomialValuation
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoLogDiscrepancy
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleEmbedding
import MMP.AlgebraicGeometry.Analytic.ComplexRealizationCharts
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.BranchMultiplicity
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagramBranches
import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations
import MMP.AlgebraicGeometry.Resolution.DivisorialPart
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
import MMP.AlgebraicGeometry.Divisor.SNC
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso

/-!
# Nonnegativity of the difficulty at the junctions of a prepared chain

Let `(p_i, Θ_i)_{i ≥ i₀}` be a prepared chain over a stabilized tail of threefold flips, with
junctions `p_i : (Y_i, Θ_i) ⟶ (X_i, B_i)`. At every junction the difficulty
`𝒟(Y_i, Θ_i) = ∑_{c_Y(v) a closed point} w_v + ∑_C β_C(Y_i, Θ_i) + ∑_h d_h ρ^□(S_h^ν)`
is nonnegative: the negative contributions of the brackets are paid by the weights of the
valuations with centre a closed point and the boxed ranks of the varying labels, leaving at least
`∑_{h fixed} d_h ρ^□(S_h^ν) ≥ 0`.

## Main results

* `MMP.Fourfold.StabilizedTail.PreparedChain.difficulty_nonneg_of_junction`: `0 ≤ 𝒟(Y_i, Θ_i)`
  for every junction `Y_i`, `i ≥ i₀`, of a prepared chain.

## Implementation notes

* The difficulty is the predicate `MMP.Fourfold.StabilizedTail.PreparedChain.IsDifficulty` on
  its value, so the statement says that every value `D` it admits at the junction is
  nonnegative. The junction `Y_i` is the model `(i, none)` of the terminal chain, a model of the
  prepared chain when `i₀ ≤ i`.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MMP.Mori MMP.Fourfold MMP.Fourfold.StabilizedTail

namespace Proof_prop_mmp_indexb_junction_nonnegative

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Label centres on the models of a terminal chain -/

section LabelCentre

/-- Valuations agreeing after composition with a surjective ring map agree. -/
private theorem valuation_eq_of_comap_eq {K L Γ : Type*} [CommRing K] [CommRing L]
    [LinearOrderedCommMonoidWithZero Γ] {φ : K →+* L} (hφ : Function.Surjective φ)
    {v w : Valuation L Γ} (h : v.comap φ = w.comap φ) : v = w :=
  Valuation.ext fun x => by
    obtain ⟨y, rfl⟩ := hφ x
    exact congrArg (fun u : Valuation K Γ => u y) h

/-- The transport of a valuation of `k(X_0)` to `k(X_i)` is unique. -/
private theorem isTransportedValuationFrom_unique {T : StabilizedTail} :
    ∀ (i : ℕ) {ν : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
      {w w' : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))},
      T.IsTransportedValuationFrom i ν w → T.IsTransportedValuationFrom i ν w' → w = w'
  | 0, _, _, _, h, h' => h.trans h'.symm
  | i + 1, _, _, _, ⟨u, hu, h⟩, ⟨u', hu', h'⟩ => by
    obtain rfl := isTransportedValuationFrom_unique i hu hu'
    haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
    exact valuation_eq_of_comap_eq
      (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective.2
      ((show _ = _ from h).trans (show _ = _ from h').symm)

/-- A prime divisor of a normal variety is determined by its valuation of `k(B)`, for a dominant
morphism `f : Y ⟶ B` inducing a surjection of function fields. -/
private theorem primeDivisor_eq_of_valuationOver_eq {Y B : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral B] {sY : Y ⟶ Spec (.of ℂ)}
    (hY : MMP.Mori.IsNormalVariety ℂ sY) (f : Y ⟶ B) [IsDominant f]
    (hf : Function.Surjective (functionFieldMap f)) {P P' : MMP.Mori.PrimeDivisor Y}
    (h : P.valuationOver f = P'.valuationOver f) : P = P' := by
  have hv : P.divisorialValuation = P'.divisorialValuation := valuation_eq_of_comap_eq hf h
  have := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1
    (D := MMP.Mori.DivisorOver.ofPrimeDivisor ℂ hY P)
    (D' := MMP.Mori.DivisorOver.ofPrimeDivisor ℂ hY P') (by
      change P.divisorialValuation.comap _ = P'.divisorialValuation.comap _
      rw [hv]; rfl)
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective this

/-- The extension of function fields of a composite is the composite of the extensions. -/
private theorem coe_functionFieldMap_comp {A B C : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] :
    ⇑(functionFieldMap (a ≫ b)) = functionFieldMap a ∘ functionFieldMap b :=
  funext fun t => (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply a b t).symm

/-- A composite of dominant morphisms surjective on function fields is surjective on them. -/
private theorem surjective_functionFieldMap_comp {A B C : Scheme.{0}} [IsIntegral A]
    [IsIntegral B] [IsIntegral C] {a : A ⟶ B} {b : B ⟶ C} [IsDominant a] [IsDominant b]
    (ha : Function.Surjective (functionFieldMap a))
    (hb : Function.Surjective (functionFieldMap b)) :
    Function.Surjective (functionFieldMap (a ≫ b)) := by
  rw [coe_functionFieldMap_comp]
  exact ha.comp hb

/-- If `a ≫ b` is surjective on function fields, so is `b` (field maps are injective). -/
private theorem surjective_functionFieldMap_of_comp {A B C : Scheme.{0}} [IsIntegral A]
    [IsIntegral B] [IsIntegral C] {a : A ⟶ B} {b : B ⟶ C} [IsDominant a] [IsDominant b]
    (hab : Function.Surjective (functionFieldMap (a ≫ b))) :
    Function.Surjective (functionFieldMap b) := by
  rw [coe_functionFieldMap_comp] at hab
  exact hab.of_comp_left (functionFieldMap a).injective

/-- If `π : V ⟶ Z` is dominant and induces a surjection of function fields, so does every
morphism `π_k : V_k ⟶ Z`, `k ≤ m`, of a finite relative programme over `Z` from `V`. -/
private theorem surjective_functionFieldMap_modelMap_of_le {V Z : Scheme.{0}} [IsIntegral V]
    [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] {sV : V ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {π : V ⟶ Z} [IsIntegral Z] {K : MMP.Mori.Divisor V}
    {Θ : MMP.Mori.QDivisor V}
    (P : RelativeThreefoldProgram sV sZ π K Θ) [IsDominant π]
    (hπ : Function.Surjective (functionFieldMap π)) :
    ∀ n ≤ P.m, ∃ _ : IsDominant (modelMap π P.πY n),
      Function.Surjective (functionFieldMap (modelMap π P.πY n))
  | 0, _ => ⟨‹_›, hπ⟩
  | n + 1, hn => by
    obtain ⟨hd, hs⟩ := surjective_functionFieldMap_modelMap_of_le P hπ n (by omega)
    have hD := P.isThreefoldStepDiagram n (by omega)
    haveI := hD.isNormalVariety_target.1.toIsIntegral
    haveI := hD.isBirationalMorphism_minus.isDominant
    haveI := hD.isSmallMorphism_plus.isBirationalMorphism.isDominant
    revert hd hs
    rw [P.modelMap_eq n (by omega)]
    intro hd hs
    haveI : IsDominant (P.h n) := IsDominant.of_comp (P.g n) (P.h n)
    change ∃ _ : IsDominant (P.πY n), Function.Surjective (functionFieldMap (P.πY n))
    rw [P.πY_eq n (by omega)]
    exact ⟨inferInstance, surjective_functionFieldMap_comp
      hD.isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective.2
      (surjective_functionFieldMap_of_comp hs)⟩

/-- On the model `V_k` of a bridge, the morphism `π_k : V_k ⟶ Z_i` induces a surjection of
function fields. -/
private theorem surjective_functionFieldMap_modelMap {T : StabilizedTail}
    (C : TerminalChain T) (i : ℕ) (k : Fin (C.bridge i).P.m)
    [IsIntegral (T.Z i)] [IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)] :
    Function.Surjective
      (functionFieldMap (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)) := by
  have hpb := (C.junction i).isBirationalMorphism
  have hfb := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus
  haveI := hpb.isDominant
  haveI := hfb.isDominant
  exact ((surjective_functionFieldMap_modelMap_of_le (C.bridge i).P
    (surjective_functionFieldMap_comp hpb.functionFieldMap_bijective.2
      hfb.functionFieldMap_bijective.2) k k.2.le).2)

/-- The centre of a label on a model of a terminal chain is unique. -/
private theorem isLabelCentre_unique {T : StabilizedTail} (C : TerminalChain T)
    {S : C.Label} {x : C.ModelIndex} {P P' : MMP.Mori.PrimeDivisor (C.model x)}
    (h : C.IsLabelCentre S x P) (h' : C.IsLabelCentre S x P') : P = P' := by
  rcases x with ⟨i, _ | k⟩
  · obtain ⟨w, hw, hPw⟩ := h
    obtain ⟨w', hw', hPw'⟩ := h'
    cases isTransportedValuationFrom_unique i hw hw'
    have hb := (C.junction i).isBirationalMorphism
    haveI := hb.isDominant
    exact primeDivisor_eq_of_valuationOver_eq (C.junction i).isQFactorial.1 (C.junction i).p
      hb.functionFieldMap_bijective.2 (hPw.trans hPw'.symm)
  · obtain ⟨w, hw, hdom, hPw⟩ := h
    obtain ⟨w', hw', _hdom', hPw'⟩ := h'
    cases isTransportedValuationFrom_unique i hw hw'
    haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    exact primeDivisor_eq_of_valuationOver_eq
      ((C.bridge i).P.isQFactorial k (by omega)).1
      (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)
      (surjective_functionFieldMap_modelMap C i k) (hPw.trans hPw'.symm)

end LabelCentre

/-! ### Curves, multiplicities and branch numbers -/

section Curves

/-- The closed subscheme `{x}⁻` has the dimension of the closure of `x`. -/
private theorem topologicalKrullDim_curveSubschemeAt {X : Scheme.{0}} (x : X) :
    topologicalKrullDim (MMP.Mori.curveSubschemeAt x) =
      topologicalKrullDim (closure {x} : Set X) := by
  have hrange : Set.range (MMP.Mori.curveSubschemeAtι x) = closure ({x} : Set X) := by
    change Set.range (Scheme.IdealSheafData.vanishingIdeal _).subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [← hrange]
  exact (MMP.Mori.curveSubschemeAtι x).isClosedEmbedding.isEmbedding.toHomeomorph
    |>.isHomeomorph.topologicalKrullDim_eq

/-- On a threefold, the generic point of a proper curve has coheight two. -/
private theorem coheight_point_eq_two {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y]
    [LocallyOfFiniteType sY] (hY : topologicalKrullDim Y = 3)
    (γ : MMP.Mori.ProperCurve sY) : Order.coheight γ.point = 2 := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY γ.point
  rw [← topologicalKrullDim_curveSubschemeAt, γ.isProperCurve.dim_eq, hY] at h
  have h' : (1 + Order.coheight γ.point : ℕ∞) = 1 + 2 :=
    WithBot.coe_injective (by push_cast; exact h)
  exact (WithTop.add_left_inj ENat.one_ne_top).mp h'

/-- The irreducible closed curve `C = {γ}⁻` of a proper curve `γ`. -/
private def curveCloseds {k : Type} [Field k] {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
    (γ : MMP.Mori.ProperCurve sY) : IrreducibleCloseds Y :=
  ⟨closure {γ.point}, isIrreducible_singleton.closure, isClosed_closure⟩

private theorem genericPoint_curveCloseds {k : Type} [Field k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} (γ : MMP.Mori.ProperCurve sY) :
    (curveCloseds γ).isIrreducible.genericPoint = γ.point :=
  ((curveCloseds γ).isIrreducible.isGenericPoint_genericPoint (curveCloseds γ).isClosed).eq
    isGenericPoint_closure

private theorem topologicalKrullDim_curveCloseds {k : Type} [Field k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} (γ : MMP.Mori.ProperCurve sY) :
    topologicalKrullDim ((curveCloseds γ : Set Y)) = 1 :=
  (topologicalKrullDim_curveSubschemeAt γ.point).symm.trans γ.dim_eq

/-- The multiplicity of a prime divisor along an irreducible closed subset is the multiplicity of
its ideal at the generic point. -/
private theorem multiplicityAlong_eq_multAt {Y : Scheme.{0}} (D : MMP.Mori.PrimeDivisor Y)
    (V : IrreducibleCloseds Y) :
    D.multiplicityAlong V = MMP.Resolution.multAt D.idealSheaf V.isIrreducible.genericPoint := by
  rw [MMP.Mori.PrimeDivisor.multiplicityAlong, Scheme.IdealSheafData.stalkIdeal_eq_stalk]
  rfl

/-- The multiplicity of a prime divisor of an integral locally noetherian scheme at a point is
finite: its ideal is a nonzero ideal of the noetherian local ring there. -/
private theorem multAt_ne_top {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (S : MMP.Mori.PrimeDivisor Y) (y : Y) : MMP.Resolution.multAt S.idealSheaf y ≠ ⊤ := by
  by_cases hy : y ∈ S.support
  · obtain ⟨q, -, hq, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support S hy
    have hne : IdealSheafData.stalk S.idealSheaf y ≠ ⊥ := hq ▸ Ideal.ne_bot_of_height_eq_one hqh
    intro htop
    apply hne
    rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal _)
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top]
    exact le_iInf fun n => (MMP.Resolution.natCast_le_idealOrder_iff' _ n).mp
      (show (n : ℕ∞) ≤ MMP.Resolution.multAt S.idealSheaf y by rw [htop]; exact le_top)
  · rw [MMP.Resolution.multAt, MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support S hy,
      MMP.Threefold.Resolution.idealOrder_top]
    exact ENat.zero_ne_top

/-- On a threefold regular at the generic points of its curves, the prime divisors of the
normalization of a prime divisor `P` mapping onto a proper curve `C` are at most the multiplicity
of `P` at `η_C` in number. -/
private theorem encard_branches_le_multAt {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [LocallyOfFiniteType sY] (hY : topologicalKrullDim Y = 3)
    (hreg : ∀ V : IrreducibleCloseds Y, topologicalKrullDim (V : Set Y) = 1 →
      IsRegularLocalRing (Y.presheaf.stalk V.isIrreducible.genericPoint))
    (γ : MMP.Mori.ProperCurve sY) (P : MMP.Mori.PrimeDivisor Y) :
    {B : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme P) |
        primeDivisorNormalization P '' B.support = closure {γ.point}}.encard ≤
      MMP.Resolution.multAt P.idealSheaf γ.point := by
  have hring : ringKrullDim (Y.presheaf.stalk (curveCloseds γ).isIrreducible.genericPoint) = 2 := by
    rw [ringKrullDim_stalk_eq_coheight, genericPoint_curveCloseds, coheight_point_eq_two _ hY γ]
    rfl
  have h := encard_branches_le_multiplicityAlong sY (curveCloseds γ)
    (hreg _ (topologicalKrullDim_curveCloseds γ)) hring P
  rwa [multiplicityAlong_eq_multAt, genericPoint_curveCloseds] at h

/-- The branch number of `P` at `C` is at most the multiplicity of `P` at `η_C`. -/
private theorem branchNumber_le_multAt {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [LocallyOfFiniteType sY] (hY : topologicalKrullDim Y = 3)
    (hreg : ∀ V : IrreducibleCloseds Y, topologicalKrullDim (V : Set Y) = 1 →
      IsRegularLocalRing (Y.presheaf.stalk V.isIrreducible.genericPoint))
    (γ : MMP.Mori.ProperCurve sY) (P : MMP.Mori.PrimeDivisor Y) :
    (branchNumber P (closure {γ.point}) : ℕ∞) ≤ MMP.Resolution.multAt P.idealSheaf γ.point := by
  rw [branchNumber, Set.ncard_def]
  exact (ENat.coe_toNat_le_self _).trans (encard_branches_le_multAt hY hreg γ P)

end Curves

/-! ### Weights and defaults -/

section Weights

/-- The default splits as `d(b) = w(b) + ∑_{2 ≤ j < ⌈1/(1-b)⌉} w(1 - j(1 - b))`. -/
private theorem defaultWeight_eq_add (N : ℕ) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    defaultWeight N b = difficultyWeight N b +
      ∑ j ∈ Finset.Ico 2 ⌈1 / (1 - b)⌉₊, difficultyWeight N (1 - j * (1 - b)) := by
  rw [(defaultWeight_finite N hb0 hb1).2.1]
  by_cases h : 1 < ⌈1 / (1 - b)⌉₊
  · rw [Finset.sum_eq_sum_Ico_succ_bot h]
    norm_num
  · have hle : ⌈1 / (1 - b)⌉₊ ≤ 1 := by omega
    have hb : b ≤ 0 := by
      have h1 : 1 / (1 - b) ≤ 1 := by exact_mod_cast Nat.ceil_le.mp hle
      have hpos : 0 < 1 - b := by linarith
      rw [div_le_one hpos] at h1
      linarith
    rw [Finset.Ico_eq_empty (by omega), Finset.Ico_eq_empty (by omega), difficultyWeight_of_nonpos hb]
    simp

/-- The higher terms `w(1 - j(1 - b))`, `j ≥ 2`, of the default vanish for `b ≤ 1/2`. -/
private theorem difficultyWeight_eq_zero_of_two_le (N : ℕ) {b : ℝ} (hb : b ≤ 1 / 2) {j : ℕ}
    (hj : 2 ≤ j) : difficultyWeight N (1 - j * (1 - b)) = 0 := by
  apply difficultyWeight_of_nonpos
  have : (2 : ℝ) ≤ j := by exact_mod_cast hj
  nlinarith

/-- For `0 ≤ b ≤ 1/2` the default is the weight: `d(b) = w(b)`. -/
private theorem defaultWeight_eq_of_le_half (N : ℕ) {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 1 / 2) :
    defaultWeight N b = difficultyWeight N b := by
  rw [defaultWeight_eq_add N hb0 (by linarith), Finset.sum_eq_zero fun j hj =>
    difficultyWeight_eq_zero_of_two_le N hb (Finset.mem_Ico.1 hj).1, add_zero]

/-- A valuation weight is the weight of `2 - a` for the log discrepancy `a` of the valuation. -/
private theorem eq_difficultyWeight_of_hasLogDiscrepancy {T : StabilizedTail}
    {C : TerminalChain T} {N : ℕ} {x : C.ModelIndex}
    {v : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ))} {w : ℕ} {a : ℝ}
    (hw : C.IsValuationWeight N x v w)
    (ha : HasLogDiscrepancy (C.modelStructure x) (C.modelBoundary x) v a) :
    w = difficultyWeight N (2 - a) := by
  obtain ⟨-, a', ⟨n', D', -, hD'v, hD'⟩, rfl⟩ := hw
  obtain ⟨n, D, hDv, hD⟩ := ha
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hD hD' (hDv.trans hD'v.symm)]

/-- A finite sum of natural numbers over a finset of points of `p` is at most the finitely
supported sum over `p`. -/
private theorem sum_le_finsum_of_forall {α : Type*} {p : α → Prop} {f : α → ℕ}
    (hfin : {a | p a ∧ f a ≠ 0}.Finite) (F : Finset α) (hF : ∀ a ∈ F, p a) :
    ∑ a ∈ F, f a ≤ ∑ᶠ (a) (_ : p a), f a := by
  classical
  have hfin' : ({a | p a} ∩ Function.support f).Finite := hfin
  change _ ≤ ∑ᶠ a ∈ {a | p a}, f a
  rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin',
    ← Finset.sum_filter_ne_zero]
  refine Finset.sum_le_sum_of_subset fun a ha => ?_
  rw [Finset.mem_filter] at ha
  rw [Set.Finite.mem_toFinset]
  exact ⟨hF a ha.1, ha.2⟩

end Weights

/-! ### Monomial valuations at the generic point of a curve -/

section Monomial

open scoped WithZero

/-- The multiplicative valuation `z ↦ exp (-V z)` attached to an additive valuation `V`. -/
private def expNeg : WithTop ℤ → ℤᵐ⁰
  | ⊤ => 0
  | (n : ℤ) => WithZero.exp (-n)

private lemma expNeg_add (a b : WithTop ℤ) : expNeg (a + b) = expNeg a * expNeg b := by
  cases a <;> cases b <;>
    simp [expNeg, ← WithTop.coe_add, neg_add, WithZero.exp_add, mul_comm]

private lemma expNeg_antitone : Antitone expNeg := by
  intro a b h
  cases b with
  | top => simp [expNeg]
  | coe n =>
    cases a with
    | top => simp at h
    | coe m =>
      simp only [expNeg, WithZero.exp_le_exp, neg_le_neg_iff]
      exact_mod_cast h

/-- The multiplicative valuation `z ↦ exp (-V z)` attached to an additive valuation `V`. -/
private def valuationOfAddValuation {R : Type*} [Ring R] (V : AddValuation R (WithTop ℤ)) :
    Valuation R ℤᵐ⁰ where
  toFun z := expNeg (V z)
  map_zero' := by simp [expNeg]
  map_one' := by simp [← WithTop.coe_zero, expNeg]
  map_mul' a b := by simp [V.map_mul, expNeg_add]
  map_add_le_max' a b := by
    rw [← expNeg_antitone.map_min]
    exact expNeg_antitone (V.map_add a b)

/-- A pair `(x, y)` is a regular system of parameters iff it spans `𝔪` and `dim A = 2`. -/
private lemma isRegularSystemOfParameters_pair_iff {A : Type*} [CommRing A] [IsLocalRing A]
    {x y : A} :
    IsRegularSystemOfParameters ![x, y] ↔
      Ideal.span {x, y} = IsLocalRing.maximalIdeal A ∧ ringKrullDim A = 2 := by
  rw [isRegularSystemOfParameters_iff, Matrix.range_cons, Matrix.range_cons,
    Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl

private lemma isRegularSystemOfParameters_swap {R : Type*} [CommRing R] [IsLocalRing R]
    {x y : R} (hxy : IsRegularSystemOfParameters ![x, y]) :
    IsRegularSystemOfParameters ![y, x] := by
  rw [isRegularSystemOfParameters_pair_iff, Set.pair_comm]
  exact isRegularSystemOfParameters_pair_iff.1 hxy

/-- A generator of an ideal of order one lies in `𝔪 ∖ 𝔪²`. -/
private theorem mem_maximalIdeal_and_notMem_sq_of_idealOrder_eq_one {R : Type*} [CommRing R]
    [IsLocalRing R] {x : R} (h : MMP.Resolution.idealOrder (Ideal.span {x}) = 1) :
    x ∈ IsLocalRing.maximalIdeal R ∧ x ∉ IsLocalRing.maximalIdeal R ^ 2 := by
  refine ⟨?_, fun hx => ?_⟩
  · simpa [Ideal.span_singleton_le_iff_mem] using
      (MMP.Resolution.natCast_le_idealOrder_iff' (Ideal.span {x}) 1).mp (by rw [h]; rfl)
  · have := (MMP.Resolution.natCast_le_idealOrder_iff' (Ideal.span {x}) 2).mpr
      ((Ideal.span_singleton_le_iff_mem _).mpr hx)
    rw [h] at this
    exact absurd this (by decide)

/-- At a point with factorial local ring, the ideal of a prime divisor in the stalk is
principal. -/
private theorem exists_stalk_idealSheaf_eq_span_singleton {Y : Scheme.{0}} [IsIntegral Y] {y : Y}
    [UniqueFactorizationMonoid (Y.presheaf.stalk y)] (P : MMP.Mori.PrimeDivisor Y) :
    ∃ g, IdealSheafData.stalk P.idealSheaf y = Ideal.span {g} := by
  by_cases hP : y ∈ P.support
  · obtain ⟨q, -, hq, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support P hP
    obtain ⟨g, hg⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hqh).principal
    exact ⟨g, hq.trans hg⟩
  · exact ⟨1, by
      rw [Ideal.span_singleton_one]
      exact MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support P hP⟩

/-- In a two-dimensional regular local ring, an element of `𝔪 ∖ 𝔪²` is the first member of a
regular system of parameters. -/
private theorem exists_isRegularSystemOfParameters_pair {R : Type*} [CommRing R]
    [IsRegularLocalRing R] (hdim : ringKrullDim R = 2) {x : R}
    (hxm : x ∈ IsLocalRing.maximalIdeal R) (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    ∃ t : R, IsRegularSystemOfParameters ![x, t] := by
  classical
  obtain ⟨s, hs, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
  have h2 : (IsLocalRing.maximalIdeal R).spanFinrank = 2 := by
    have := (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).trans hdim
    exact_mod_cast this
  obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp (hs.trans h2)
  have hab : Ideal.span {a, b} = IsLocalRing.maximalIdeal R := by simpa using hspan
  have key : ∀ {p q : R}, Ideal.span {p, q} = IsLocalRing.maximalIdeal R → ∀ c₀ c₁ : R,
      x = c₀ * p + c₁ * q → IsUnit c₀ → Ideal.span {x, q} = IsLocalRing.maximalIdeal R := by
    intro p q hpq c₀ c₁ hx hu
    refine le_antisymm (Ideal.span_le.mpr ?_) ?_
    · rintro _ (rfl | rfl)
      exacts [hxm, hpq ▸ Ideal.subset_span (by simp)]
    · have hp : p = ↑hu.unit⁻¹ * x - ↑hu.unit⁻¹ * c₁ * q := by
        rw [hx, mul_add, ← mul_assoc, IsUnit.val_inv_mul, one_mul]; ring
      rw [← hpq]
      refine Ideal.span_le.mpr ?_
      rintro _ (rfl | rfl)
      · rw [hp]
        exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      · exact Ideal.subset_span (by simp)
  have ha : a ∈ IsLocalRing.maximalIdeal R := hab ▸ Ideal.subset_span (by simp)
  have hb : b ∈ IsLocalRing.maximalIdeal R := hab ▸ Ideal.subset_span (by simp)
  obtain ⟨c₀, c₁, hx⟩ := Ideal.mem_span_pair.mp (hab ▸ hxm : x ∈ Ideal.span {a, b})
  have hunit : IsUnit c₀ ∨ IsUnit c₁ := by
    by_contra h
    rw [not_or] at h
    apply hx2
    rw [← hx, pow_two]
    exact add_mem (Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal _).2 h.1) ha)
      (Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal _).2 h.2) hb)
  obtain ⟨t, ht⟩ : ∃ t, Ideal.span {x, t} = IsLocalRing.maximalIdeal R := by
    rcases hunit with hu | hu
    · exact ⟨b, key hab c₀ c₁ hx.symm hu⟩
    · exact ⟨a, key (by rw [Set.pair_comm]; exact hab) c₁ c₀ (by rw [← hx]; ring) hu⟩
  exact ⟨t, isRegularSystemOfParameters_pair_iff.2 ⟨ht, hdim⟩⟩

/-- For `x ∈ 𝔪 ∖ 𝔪²` with `𝔪 = (x, t)` and `j ≥ 1`, the monomial valuation of weights `(j, 1)`
takes the value `j` on `x`. -/
private theorem monomialValuation_self {R : Type*} [CommRing R] [IsLocalRing R] {x t : R}
    (hxt : IsRegularSystemOfParameters ![x, t]) (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2)
    {j : ℕ} (hj : 1 ≤ j) :
    MMP.Resolution.monomialValuation t x j x = j := by
  have hm := (isRegularSystemOfParameters_pair_iff.1 hxt).1
  have hxm : x ∈ IsLocalRing.maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
  have htm : t ∈ IsLocalRing.maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
  rw [MMP.Resolution.monomialValuation]
  refine (isGreatest_iff_iSup_eq ⟨j, ?_⟩).1 ⟨?_, fun n hn => ?_⟩
  · exact Ideal.subset_span ⟨0, 1, by simp, by simp⟩
  · exact Ideal.subset_span ⟨0, 1, by simp, by simp⟩
  · by_contra hlt'
    have hlt := lt_of_not_ge hlt'
    refine hx2 ((Ideal.span_le.mpr ?_ : MMP.Resolution.monomialIdeal t x j n ≤ _) hn)
    rintro _ ⟨a, b, hab, rfl⟩
    have hmem : t ^ a * x ^ b ∈ IsLocalRing.maximalIdeal R ^ (a + b) := by
      rw [pow_add]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow htm a) (Ideal.pow_mem_pow hxm b)
    refine Ideal.pow_le_pow_right ?_ hmem
    rcases b with _ | _ | b
    · simp at hab; omega
    · simp at hab; omega
    · omega

/-- At a regular codimension-two point, the monomial valuation of weights `(j, 1)` exists for
every regular system of parameters and every `j ≥ 1`. -/
private theorem exists_isWeightedMonomialValuation {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [IsLocallyNoetherian Y] (hY : IsNormalVariety ℂ sY) (V : IrreducibleCloseds Y)
    (hcod : codimension V = 2)
    (hreg : IsRegularLocalRing (Y.presheaf.stalk V.isIrreducible.genericPoint))
    {x t : Y.presheaf.stalk V.isIrreducible.genericPoint}
    (ht : IsRegularSystemOfParameters ![x, t]) {j : ℕ} (hj : 1 ≤ j) :
    ∃ v : Valuation Y.functionField ℤᵐ⁰, IsWeightedMonomialValuation sY V x t j v := by
  obtain ⟨hfin, -, -, W, hW, -⟩ := MMP.Resolution.exists_addValuation_monomialValuation
    Y.functionField (isRegularSystemOfParameters_swap ht) hj
  refine ⟨valuationOfAddValuation W, hY, hcod, hreg, ht, hj, fun f hf => ?_⟩
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp (hfin f hf)
  refine ⟨M, hM.symm, ?_⟩
  change expNeg (W _) = _
  rw [hW, ← hM]
  rfl

/-- At the generic point of an irreducible closed curve of a normal complex threefold along which
it is regular, the order of the local ring is a generic blowup valuation. -/
private theorem exists_isGenericBlowupValuation {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] (hX : IsNormalVariety ℂ sX)
    (h3 : topologicalKrullDim X = 3) (V : IrreducibleCloseds X)
    (hV : topologicalKrullDim (V : Set X) = 1)
    (hcoh : Order.coheight V.isIrreducible.genericPoint = 2)
    [hreg : IsRegularLocalRing (X.presheaf.stalk V.isIrreducible.genericPoint)] :
    ∃ v : Valuation X.functionField ℤᵐ⁰, IsGenericBlowupValuation sX V v := by
  have hcodim : codimension V = 2 := by
    rw [MMP.Flips.codimension_eq_coheight_genericPoint, hcoh]
  obtain ⟨n, z, hz⟩ :=
    MMP.Mori.exists_isRegularSystemOfParameters (X.presheaf.stalk V.isIrreducible.genericPoint)
  obtain rfl : n = 2 := by
    have h := hz.2
    rw [ringKrullDim_stalk_eq_coheight, hcoh] at h
    exact_mod_cast h.symm
  have hz' : IsRegularSystemOfParameters ![z 0, z 1] := by
    convert hz using 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨v, hv⟩ := exists_isWeightedMonomialValuation hX V hcodim hreg hz' le_rfl
  exact ⟨v, (isGenericBlowupValuation_iff_isWeightedMonomialValuation h3 hV hcodim hz').mpr hv⟩

/-- A monomial valuation of weights `(j, 1)` for parameters `(x, t)` with `x ∉ 𝔪²` takes the
value `exp (-j)` on `x`. -/
private theorem weightedMonomialValuation_apply_self {Y : Scheme.{0}} [IsIntegral Y] {sY : Y ⟶ Spec (.of ℂ)}
    {V : IrreducibleCloseds Y} {x t : Y.presheaf.stalk V.isIrreducible.genericPoint} {j : ℕ}
    {v : Valuation Y.functionField ℤᵐ⁰} (hv : IsWeightedMonomialValuation sY V x t j v)
    (hx2 : x ∉ IsLocalRing.maximalIdeal _ ^ 2) :
    v (algebraMap _ Y.functionField x) = WithZero.exp (-(j : ℤ)) := by
  obtain ⟨-, -, -, hxt, hj, hv⟩ := hv
  obtain ⟨M, hM, hvM⟩ := hv x fun h => hx2 (h ▸ Ideal.zero_mem _)
  rw [monomialValuation_self hxt hx2 hj] at hM
  rw [hvM, show M = j by exact_mod_cast hM.symm]

/-- A monomial valuation at `η_V` is nonnegative on the local ring `𝒪_{Y,η_V}`. -/
private theorem neg_log_weightedMonomialValuation_nonneg {Y : Scheme.{0}} [IsIntegral Y]
    {sY : Y ⟶ Spec (.of ℂ)} {V : IrreducibleCloseds Y}
    {x t : Y.presheaf.stalk V.isIrreducible.genericPoint} {j : ℕ}
    {v : Valuation Y.functionField ℤᵐ⁰} (hv : IsWeightedMonomialValuation sY V x t j v)
    (f : Y.presheaf.stalk V.isIrreducible.genericPoint) :
    0 ≤ -WithZero.log (v (algebraMap _ Y.functionField f)) := by
  by_cases hf : f = 0
  · simp [hf]
  · obtain ⟨M, -, hvM⟩ := hv.2.2.2.2.2 f hf
    rw [hvM, WithZero.log_exp]
    simp

/-- The sum `∑_h m_h b_h` over the labels is the multiplicity `mult_{η_C} Θ` of the boundary,
since `Θ = ∑_h b_h S_h` for the pairwise distinct centres `S_h` of the labels. -/
private theorem finsum_mul_eq_multiplicityAt {T : StabilizedTail} (Q : PreparedChain T)
    (x : Q.ModelIndex) (γ : ProperCurve (Q.chain.modelStructure x.1))
    (m : Q.chain.Label → ℕ) (b : Q.chain.Label → ℚ)
    (hm : ∀ S, ∃ P : MMP.Mori.PrimeDivisor (Q.chain.model x.1),
      Q.chain.IsLabelCentre S x.1 P ∧ MMP.Resolution.multAt P.idealSheaf γ.point = m S)
    (hb : ∀ S, Q.chain.IsLabelCoefficient S x.1 (b S)) :
    ∑ᶠ S, (m S : ℚ) * b S =
      DivisorWithCoeffs.multiplicityAt (Q.chain.modelBoundary x.1) γ.point := by
  classical
  obtain ⟨-, -, -, -, ⟨c, hc, hcentre, hsupp, -⟩, -⟩ := Q.echoSetting_model x
  set Θ := Q.chain.modelBoundary x.1
  let f : MMP.Mori.PrimeDivisor (Q.chain.model x.1) → ℚ := fun P =>
    ((P.multiplicityAt γ.point).toNat : ℚ) * Θ.coeff P
  have hmb : ∀ S, (m S : ℚ) * b S = f (c S) := fun S => by
    obtain ⟨P, hP, hPb⟩ := hb S
    obtain rfl := isLabelCentre_unique _ hP (hcentre S)
    obtain ⟨P, hP', hPm⟩ := hm S
    obtain rfl := isLabelCentre_unique _ hP' (hcentre S)
    have : (c S).multiplicityAt γ.point = m S := by
      rw [← hPm, PrimeDivisor.multiplicityAt, MMP.Resolution.multAt,
        MMP.Resolution.idealOrder, Scheme.IdealSheafData.stalkIdeal_eq_stalk]
    simp only [f, this, ENat.toNat_coe, Θ, hPb]
  haveI := Q.chain.finite_label
  haveI := Fintype.ofFinite Q.chain.Label
  rw [finsum_eq_sum_of_fintype, DivisorWithCoeffs.multiplicityAt, Finsupp.sum]
  calc ∑ S, (m S : ℚ) * b S = ∑ P ∈ Finset.univ.image c, f P := by
        rw [Finset.sum_image fun S _ S' _ h => hc h]
        exact Finset.sum_congr rfl fun S _ => hmb S
    _ = ∑ P ∈ Finsupp.support Θ, f P := by
      refine (Finset.sum_subset (fun P hP => ?_) fun P _ hP => ?_).symm
      · obtain ⟨S, rfl⟩ := hsupp P (by simpa [DivisorWithCoeffs.coeff_apply] using hP)
        exact Finset.mem_image_of_mem c (Finset.mem_univ S)
      · simp [f, DivisorWithCoeffs.coeff_apply, Finsupp.notMem_support_iff.mp hP]
    _ = _ := Finset.sum_congr rfl fun P _ => by
      simp [f, nsmul_eq_mul, DivisorWithCoeffs.coeff_apply]

end Monomial

/-- **Local ceiling error.** At a curve `γ` of a model of a prepared chain, the bracket satisfies
`β_γ ≥ -max{r_γ^var - 1, 0}`, for the branch numbers `r` of the labels at `γ`. -/
private theorem neg_max_le_of_isCurveBracket {T : StabilizedTail} (Q : PreparedChain T)
    (x : Q.ModelIndex) (γ : ProperCurve (Q.chain.modelStructure x.1)) {β : ℤ}
    (hβ : Q.IsCurveBracket x γ β) :
    ∃ r : Q.chain.Label → ℕ, (∀ S, Q.chain.IsLabelBranchNumber S x.1 γ (r S)) ∧
      -max (((∑ᶠ (S) (_ : Q.chain.IsVaryingLabel S), r S : ℕ) : ℤ) - 1) 0 ≤ β := by
  classical
  obtain ⟨wv, r, d, hwv, hr, hd, rfl⟩ := hβ
  refine ⟨r, hr, ?_⟩
  obtain ⟨hT, hproj, -, hdim, ⟨c, -, hc, hsupp, hcoeff⟩, hreg⟩ := Q.echoSetting_model x
  haveI := Q.chain.finite_label
  letI : Fintype Q.chain.Label := Fintype.ofFinite _
  haveI : LocallyOfFiniteType (Q.chain.modelStructure x.1) := hproj.toLocallyOfFiniteType
  have hY : IsNormalVariety ℂ (Q.chain.modelStructure x.1) := hT.1.1.isPair.1
  set V := curveCloseds γ with hVdef
  have hη : V.isIrreducible.genericPoint = γ.point := genericPoint_curveCloseds γ
  have hV : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 1 :=
    topologicalKrullDim_curveCloseds γ
  have hcoh : Order.coheight V.isIrreducible.genericPoint = 2 := by
    rw [hη]; exact coheight_point_eq_two _ hdim γ
  have hcod : codimension V = 2 := by
    rw [MMP.Flips.codimension_eq_coheight_genericPoint, hcoh]
  haveI hregV : IsRegularLocalRing
      ((Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint) := hreg V hV
  have hdim2 : ringKrullDim
      ((Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint) = 2 := by
    rw [ringKrullDim_stalk_eq_coheight, hcoh]; rfl
  -- coefficients, defaults and multiplicities of the labels
  set b : Q.chain.Label → ℚ := fun S => (Q.chain.modelBoundary x.1).coeff (c S) with hb_def
  have hb : ∀ S, Q.chain.IsLabelCoefficient S x.1 (b S) := fun S => ⟨c S, hc S, rfl⟩
  have hb0 : ∀ S, (0 : ℝ) ≤ b S := fun S => by exact_mod_cast (hcoeff S).1
  have hb1 : ∀ S, (b S : ℝ) < 1 := fun S => by exact_mod_cast (hcoeff S).2
  have hdS : ∀ S, d S = defaultWeight Q.scale (b S) := fun S => by
    obtain ⟨b', ⟨P, hP, hPb⟩, hd'⟩ := hd S
    obtain rfl := isLabelCentre_unique Q.chain hP (hc S)
    rw [hd', ← hPb]
  set m : Q.chain.Label → ℕ := fun S =>
    (MMP.Resolution.multAt (c S).idealSheaf γ.point).toNat with hm_def
  have hm : ∀ S, MMP.Resolution.multAt (c S).idealSheaf γ.point = m S := fun S =>
    (ENat.coe_toNat (multAt_ne_top _ _)).symm
  have hrm : ∀ S, r S ≤ m S := fun S => by
    obtain ⟨P, hP, hrP⟩ := hr S
    obtain rfl := isLabelCentre_unique Q.chain hP (hc S)
    have h := branchNumber_le_multAt hdim hreg γ (c S)
    rw [hm, ← hrP] at h
    exact_mod_cast h
  have hlt : ∑ᶠ S, (m S : ℚ) * b S < 1 :=
    PreparedChain.sum_mul_labelCoefficient_lt_one Q x γ m b
      (fun S => Or.inl ⟨c S, hc S, hm S⟩) hb
  have hlt' : ∑ S, (m S : ℝ) * b S < 1 := by
    rw [finsum_eq_sum_of_fintype] at hlt
    exact_mod_cast hlt
  have hmb0 : ∀ S, (0 : ℝ) ≤ (m S : ℝ) * b S := fun S => mul_nonneg (Nat.cast_nonneg _) (hb0 S)
  have hfde := PreparedChain.difficultyWeight_sum_mul_labelCoefficient_ge Q x γ m b r _
    (fun S => ⟨c S, hc S, hm S⟩) hb hr ⟨r, fun S _ => hr S, rfl⟩
  have e1 : ∑ᶠ S, (r S : ℤ) * (difficultyWeight Q.scale (b S) : ℤ) =
      ∑ S, (r S : ℤ) * (difficultyWeight Q.scale (b S) : ℤ) := finsum_eq_sum_of_fintype _
  have e2 : ∑ᶠ S, (m S : ℝ) * (b S : ℝ) = ∑ S, (m S : ℝ) * (b S : ℝ) :=
    finsum_eq_sum_of_fintype _
  rw [e1, e2] at hfde
  -- the centre-`C` valuations
  set p : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) → Prop :=
    fun v => ∃ Z : IrreducibleCloseds (Q.chain.model x.1),
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧
        (Z : Set (Q.chain.model x.1)) = closure {γ.point} with hp_def
  have hfin : {v | p v ∧ wv v ≠ 0}.Finite :=
    (PreparedChain.finite_setOf_isCentre_closure Q x γ).subset fun v hv =>
      ⟨hv.1, wv v, hwv v hv.1, hv.2⟩
  -- the order valuation has weight `w(∑_h m_h b_h)`
  have hv1 : ∀ v, IsGenericBlowupValuation (Q.chain.modelStructure x.1) V v →
      p v ∧ wv v = difficultyWeight Q.scale (∑ S, (m S : ℝ) * b S) := by
    intro v hv
    obtain ⟨-, hcen, -, hlog⟩ := hv.hasLogDiscrepancy hT.1.1
    have hpv : p v := ⟨V, hcen, rfl⟩
    refine ⟨hpv, ?_⟩
    rw [eq_difficultyWeight_of_hasLogDiscrepancy (hwv v hpv) hlog, hη,
      ← finsum_mul_eq_multiplicityAt Q x γ m b (fun S => ⟨c S, hc S, hm S⟩) hb,
      finsum_eq_sum_of_fintype]
    push_cast
    ring_nf
  -- the main estimate
  obtain ⟨E, hE1, hE2⟩ : ∃ E : ℕ,
      difficultyWeight Q.scale (∑ S, (m S : ℝ) * b S) + E ≤ ∑ᶠ (v) (_ : p v), wv v ∧
      ∑ S, r S * d S ≤ ∑ S, r S * difficultyWeight Q.scale (b S) + E := by
    by_cases hhigh : ∃ h0, 1 ≤ r h0 ∧ (1 / 2 : ℝ) < b h0
    · obtain ⟨h0, hr0, hbh0⟩ := hhigh
      have hsingle : ∀ S, (m S : ℝ) * b S ≤ ∑ S, (m S : ℝ) * b S := fun S =>
        Finset.single_le_sum (fun i _ => hmb0 i) (Finset.mem_univ S)
      have hsum_ge : ∀ S S', S ≠ S' → (m S : ℝ) * b S + m S' * b S' ≤ ∑ S, (m S : ℝ) * b S := by
        intro S S' hne
        have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {S, S'})
          (fun i _ _ => hmb0 i)
        rwa [Finset.sum_pair hne] at this
      have hm0 : m h0 = 1 := by
        have h1 : 1 ≤ m h0 := hr0.trans (hrm h0)
        by_contra hne
        have h2 : (2 : ℝ) ≤ m h0 := by exact_mod_cast (show 2 ≤ m h0 by omega)
        have := hsingle h0
        nlinarith [hb0 h0]
      have hr0' : r h0 = 1 := le_antisymm (hm0 ▸ hrm h0) hr0
      have hother : ∀ S, S ≠ h0 → 1 ≤ r S → (b S : ℝ) ≤ 1 / 2 := by
        intro S hS hrS
        have h1 : (1 : ℝ) ≤ m S := by exact_mod_cast hrS.trans (hrm S)
        have := hsum_ge S h0 hS
        rw [hm0] at this
        push_cast at this
        nlinarith [hb0 S]
      refine ⟨∑ j ∈ Finset.Ico 2 ⌈1 / (1 - (b h0 : ℝ))⌉₊,
        difficultyWeight Q.scale (1 - j * (1 - (b h0 : ℝ))), ?_, ?_⟩
      · -- a local equation `x` of the label `h0` at `η_C`, completed to parameters `(x, t)`
        have hmη : MMP.Resolution.multAt (c h0).idealSheaf V.isIrreducible.genericPoint = 1 := by
          rw [hη, hm h0, hm0]; rfl
        haveI := IsRegularLocalRing.uniqueFactorizationMonoid
          ((Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint)
        choose g hg using fun P => exists_stalk_idealSheaf_eq_span_singleton
          (y := V.isIrreducible.genericPoint) P
        obtain ⟨hxm, hx2⟩ := mem_maximalIdeal_and_notMem_sq_of_idealOrder_eq_one
          (show MMP.Resolution.idealOrder (Ideal.span {g (c h0)}) = 1 from hg (c h0) ▸ hmη)
        obtain ⟨t, ht⟩ := exists_isRegularSystemOfParameters_pair hdim2 hxm hx2
        haveI : Nonempty (Valuation (Q.chain.model x.1).functionField
          (WithZero (Multiplicative ℤ))) := ⟨1⟩
        choose! vj hvj using fun (j : ℕ) (hj : 1 ≤ j) =>
          exists_isWeightedMonomialValuation hY V hcod hregV ht hj
        have hval : ∀ j, 1 ≤ j → vj j (algebraMap _ (Q.chain.model x.1).functionField (g (c h0))) =
            WithZero.exp (-(j : ℤ)) := fun j hj =>
          weightedMonomialValuation_apply_self (hvj j hj) hx2
        have hpj : ∀ j, 1 ≤ j → p (vj j) := fun j hj =>
          ⟨V, (hvj j hj).isNormalizedDivisorialValuation_and_isCentre.2, rfl⟩
        have hinj : Set.InjOn vj (Finset.Ico 1 ⌈1 / (1 - (b h0 : ℝ))⌉₊ : Set ℕ) := by
          intro j hj j' hj' h
          have h1 := hval j (Finset.mem_Ico.1 hj).1
          rw [h, hval j' (Finset.mem_Ico.1 hj').1] at h1
          have := WithZero.exp_injective h1
          omega
        -- the weight of `v_j`, `j ≥ 2`, is at least `w(1 - j(1 - b_{h0}))`
        have hcoeffnonneg : ∀ P, (0 : ℝ) ≤ (Q.chain.modelBoundary x.1).coeff P := by
          intro P
          by_cases hP : (Q.chain.modelBoundary x.1).coeff P = 0
          · simp [hP]
          · obtain ⟨S, rfl⟩ := hsupp P hP
            exact_mod_cast (hcoeff S).1
        have hmemsupp : c h0 ∈ (Q.chain.modelBoundary x.1).support := by
          have hne : (Q.chain.modelBoundary x.1).coeff (c h0) ≠ 0 := by
            intro h
            have : (b h0 : ℝ) = 0 := by simp [hb_def, h]
            rw [this] at hbh0
            norm_num at hbh0
          exact Finsupp.mem_support_iff.mpr (by simpa [DivisorWithCoeffs.coeff_apply] using hne)
        have hwj : ∀ j : ℕ, 2 ≤ j →
            difficultyWeight Q.scale (1 - j * (1 - (b h0 : ℝ))) ≤ wv (vj j) := by
          intro j hj
          have hj1 : 1 ≤ j := by omega
          have hlog := (hvj j hj1).hasLogDiscrepancy hT.1.1 g (fun P _ => hg P)
          rw [eq_difficultyWeight_of_hasLogDiscrepancy (hwv _ (hpj j hj1)) hlog]
          apply difficultyWeight_mono
          have key := Finset.single_le_sum
            (f := fun P => ((Q.chain.modelBoundary x.1).coeff P : ℝ) *
              ((-WithZero.log (vj j (algebraMap _ (Q.chain.model x.1).functionField (g P))) : ℤ) :
                ℝ))
            (fun P _ => mul_nonneg (hcoeffnonneg P)
              (by exact_mod_cast neg_log_weightedMonomialValuation_nonneg (hvj j hj1) (g P)))
            hmemsupp
          simp only [hval j hj1, WithZero.log_exp, neg_neg] at key
          push_cast at key
          have hbb : (b h0 : ℝ) = (Q.chain.modelBoundary x.1).coeff (c h0) := rfl
          rw [hbb]
          push_cast
          linarith
        have hJ1 : 1 < ⌈1 / (1 - (b h0 : ℝ))⌉₊ := by
          rw [Nat.lt_ceil]
          have : 0 < 1 - (b h0 : ℝ) := by linarith [hb1 h0]
          rw [Nat.cast_one, lt_div_iff₀ this]
          linarith
        obtain ⟨-, hw1⟩ := hv1 (vj 1)
          ((isGenericBlowupValuation_iff_isWeightedMonomialValuation hdim hV hcod ht).mpr
            (hvj 1 le_rfl))
        have hsumF := sum_le_finsum_of_forall hfin
          ((Finset.Ico 1 ⌈1 / (1 - (b h0 : ℝ))⌉₊).image vj) (by
            intro v hv
            obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hv
            exact hpj j (Finset.mem_Ico.1 hj).1)
        rw [Finset.sum_image hinj, Finset.sum_eq_sum_Ico_succ_bot hJ1, hw1] at hsumF
        exact le_trans (Nat.add_le_add_left (Finset.sum_le_sum fun j hj =>
          hwj j (Finset.mem_Ico.1 hj).1) _) hsumF
      · have hsplit : ∀ S, r S * d S = r S * difficultyWeight Q.scale (b S) +
            r S * ∑ j ∈ Finset.Ico 2 ⌈1 / (1 - (b S : ℝ))⌉₊,
              difficultyWeight Q.scale (1 - j * (1 - (b S : ℝ))) := fun S => by
          rw [hdS, defaultWeight_eq_add _ (hb0 S) (hb1 S), mul_add]
        rw [Finset.sum_congr rfl fun S _ => hsplit S, Finset.sum_add_distrib]
        refine Nat.add_le_add_left (le_of_eq ?_) _
        rw [Finset.sum_eq_single h0]
        · rw [hr0', one_mul]
        · intro S _ hS
          rcases Nat.eq_zero_or_pos (r S) with h0' | hpos
          · simp [h0']
          · rw [Finset.sum_eq_zero fun j hj => difficultyWeight_eq_zero_of_two_le _
              (hother S hS hpos) (Finset.mem_Ico.1 hj).1, mul_zero]
        · simp
    · push Not at hhigh
      refine ⟨0, ?_, ?_⟩
      · obtain ⟨v1, hv1'⟩ := exists_isGenericBlowupValuation hY hdim V hV hcoh
        obtain ⟨hpv, hwv1⟩ := hv1 v1 hv1'
        have := sum_le_finsum_of_forall hfin {v1} (by simpa using hpv)
        rw [Finset.sum_singleton, hwv1] at this
        simpa using this
      · rw [add_zero]
        refine Finset.sum_le_sum fun S _ => ?_
        rcases Nat.eq_zero_or_pos (r S) with h0 | hpos
        · simp [h0]
        · rw [hdS, defaultWeight_eq_of_le_half _ (hb0 S) (hhigh S hpos)]
  have hE2' : ((∑ᶠ S, r S * d S : ℕ) : ℤ) ≤
      ∑ S, (r S : ℤ) * difficultyWeight Q.scale (b S) + E := by
    rw [finsum_eq_sum_of_fintype]
    exact_mod_cast hE2
  have hE1' : (difficultyWeight Q.scale (∑ S, (m S : ℝ) * b S) : ℤ) + E ≤
      ((∑ᶠ (v) (_ : p v), wv v : ℕ) : ℤ) := by exact_mod_cast hE1
  have hfde' : ∑ S, (r S : ℤ) * difficultyWeight Q.scale (b S) -
      max ((((∑ᶠ (S) (_ : Q.chain.IsVaryingLabel S), r S : ℕ) : ℤ)) - 1) 0 ≤
      difficultyWeight Q.scale (∑ S, (m S : ℝ) * b S) := hfde
  linarith

/-- **Branch positivity.** A curve of a junction contained in the varying union has varying
branch number at least one. -/
private theorem one_le_finsum_of_subset_varyingUnion {T : StabilizedTail} (Q : PreparedChain T)
    {i : ℕ} (hi : Q.start ≤ i) (γ : ProperCurve (Q.chain.modelStructure ⟨i, none⟩))
    (hγ : closure {γ.point} ⊆ Q.chain.varyingUnion i) (r : Q.chain.Label → ℕ)
    (hr : ∀ S, Q.chain.IsLabelBranchNumber S ⟨i, none⟩ γ (r S)) :
    1 ≤ ∑ᶠ (S) (_ : Q.chain.IsVaryingLabel S), r S := by
  classical
  obtain ⟨-, hproj, -, hdim, ⟨c, -, hc, -, -⟩, hreg⟩ := Q.echoSetting_model ⟨⟨i, none⟩, hi⟩
  haveI : LocallyOfFiniteType (Q.chain.modelStructure ⟨i, none⟩) := hproj.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsVariety ℂ (Q.chain.modelStructure ⟨i, none⟩) := hproj.toIsVariety
  have hcod : codimension (curveCloseds γ) = 2 := by
    rw [MMP.Flips.codimension_eq_coheight_genericPoint, genericPoint_curveCloseds,
      coheight_point_eq_two _ hdim γ]
  have hsub : (curveCloseds γ : Set (Q.chain.model ⟨i, none⟩)) ⊆
      ⋃ S : {S : Q.chain.Label // Q.chain.IsVaryingLabel S}, (c S.1).support := by
    intro y hy
    obtain ⟨S, hS, P, hP, hyP⟩ := hγ hy
    obtain rfl := isLabelCentre_unique Q.chain hP (hc S)
    exact Set.mem_iUnion.2 ⟨⟨S, hS⟩, hyP⟩
  obtain ⟨⟨S, hS⟩, B, hB⟩ := exists_primeDivisor_image_primeDivisorNormalization_eq
    (Q.chain.modelStructure ⟨i, none⟩)
    (fun S : {S : Q.chain.Label // Q.chain.IsVaryingLabel S} => c S.1) _ hcod hsub
  have hrS : 1 ≤ r S := by
    obtain ⟨P, hP, hrP⟩ := hr S
    obtain rfl := isLabelCentre_unique Q.chain hP (hc S)
    rw [hrP, branchNumber]
    have hle := encard_branches_le_multAt hdim hreg γ (c S)
    have hfin : {B : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme (c S)) |
        primeDivisorNormalization (c S) '' B.support = closure {γ.point}}.Finite :=
      Set.encard_ne_top_iff.mp (ne_top_of_le_ne_top (multAt_ne_top _ _) hle)
    exact (Set.ncard_pos hfin).2 ⟨B, hB⟩
  haveI := Q.chain.finite_label
  have h : (∑ᶠ (_ : Q.chain.IsVaryingLabel S), r S) ≤
      ∑ᶠ (S) (_ : Q.chain.IsVaryingLabel S), r S :=
    single_le_finsum (f := fun S => ∑ᶠ (_ : Q.chain.IsVaryingLabel S), r S) S
      (Set.toFinite _) (fun _ => Nat.zero_le _)
  rw [finsum_eq_if, if_pos hS] at h
  exact hrS.trans h

/-- A curve of a junction not contained in the varying union has varying branch number zero. -/
private theorem finsum_eq_zero_of_not_subset_varyingUnion {T : StabilizedTail}
    (Q : PreparedChain T) {i : ℕ} (γ : ProperCurve (Q.chain.modelStructure ⟨i, none⟩))
    (hγ : ¬ closure {γ.point} ⊆ Q.chain.varyingUnion i) (r : Q.chain.Label → ℕ)
    (hr : ∀ S, Q.chain.IsLabelBranchNumber S ⟨i, none⟩ γ (r S)) :
    ∑ᶠ (S) (_ : Q.chain.IsVaryingLabel S), r S = 0 := by
  classical
  refine finsum_eq_zero_of_forall_eq_zero fun S => ?_
  rw [finsum_eq_if]
  split_ifs with hS
  swap
  · rfl
  obtain ⟨P, hP, hrP⟩ := hr S
  rw [hrP]
  refine branchNumber_eq_zero_of_not_subset fun hsub => hγ fun y hy => ?_
  exact ⟨S, hS, P, hP, hsub hy⟩

private theorem solution : ∀ {T : StabilizedTail} (Q : PreparedChain T) {i : ℕ} (hi : Q.start ≤ i)
    {D : ℤ} (hD : Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D), 0 ≤ D := by
  intro T Q i hi D hD
  classical
  obtain ⟨w, β, d, ρ, hw, hβ, hd, hρ, rfl⟩ := hD
  choose rb hrb hβge using fun γ => neg_max_le_of_isCurveBracket Q ⟨⟨i, none⟩, hi⟩ γ (hβ γ)
  set rv : ProperCurve (Q.chain.modelStructure ⟨i, none⟩) → ℕ :=
    fun γ => ∑ᶠ (S) (_ : Q.chain.IsVaryingLabel S), rb γ S with hrv_def
  obtain ⟨hfin, hle⟩ := PreparedChain.varyingBranchExcess_le Q hi rv
    (fun γ _ => ⟨rb γ, fun S _ => hrb γ S, rfl⟩) d ρ (fun S _ => hd S) (fun S _ => hρ S) w
    (fun v _ hc => hw v hc)
  -- the point valuations carrying a weight are exceptional, so the two point sums agree
  have hW : (∑ᶠ (v) (_ : MMP.Intersection.IsExceptionalValuation ℂ
      (Q.chain.modelStructure ⟨i, none⟩) v ∧
        ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
            ∃ y : Q.chain.model ⟨i, none⟩, IsClosed ({y} : Set (Q.chain.model ⟨i, none⟩)) ∧
              (Z : Set (Q.chain.model ⟨i, none⟩)) = {y}), w v) =
      ∑ᶠ (v) (_ : ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
            ∃ y : Q.chain.model ⟨i, none⟩, IsClosed ({y} : Set (Q.chain.model ⟨i, none⟩)) ∧
              (Z : Set (Q.chain.model ⟨i, none⟩)) = {y}), w v :=
    finsum_congr fun v => finsum_congr_Prop (propext ⟨And.right, fun h => ⟨(hw v h).1, h⟩⟩)
      fun _ => rfl
  rw [hW] at hle
  -- the varying labels contribute at most all labels
  have hlab : Finite Q.chain.Label := Q.chain.finite_label
  have hvar : (∑ᶠ (S) (_ : Q.chain.IsVaryingLabel S), d S * ρ S) ≤ ∑ᶠ S, d S * ρ S :=
    finsum_le_finsum' (Set.toFinite _) (Set.toFinite _) fun S => by
      rw [finsum_eq_if]
      split_ifs <;> simp
  have hvar' : ((∑ᶠ (S) (_ : Q.chain.IsVaryingLabel S), d S * ρ S : ℕ) : ℤ) ≤
      ((∑ᶠ S, d S * ρ S : ℕ) : ℤ) := by exact_mod_cast hvar
  by_cases hβfin : (Function.support β).Finite
  · set g : ProperCurve (Q.chain.modelStructure ⟨i, none⟩) → ℤ := fun γ =>
      if closure {γ.point} ⊆ Q.chain.varyingUnion i then -((rv γ : ℤ) - 1) else 0 with hg_def
    have hg : ∀ γ, g γ ≤ β γ := fun γ => by
      by_cases h : closure {γ.point} ⊆ Q.chain.varyingUnion i
      · have h1 := one_le_finsum_of_subset_varyingUnion Q hi γ h (rb γ) (hrb γ)
        have h2 := hβge γ
        simp only [hg_def, if_pos h]
        rw [max_eq_left (by omega)] at h2
        exact h2
      · have h0 := finsum_eq_zero_of_not_subset_varyingUnion Q γ h (rb γ) (hrb γ)
        have h2 := hβge γ
        simp only [hg_def, if_neg h]
        rw [h0] at h2
        simpa using h2
    have hgfin : (Function.support g).Finite := by
      refine (hfin.image Subtype.val).subset fun γ hγ => ?_
      by_cases h : closure {γ.point} ⊆ Q.chain.varyingUnion i
      · refine ⟨⟨γ, h⟩, ?_, rfl⟩
        simp only [Function.mem_support, hg_def, if_pos h, ne_eq, neg_eq_zero] at hγ ⊢
        exact hγ
      · exact absurd (by simp [hg_def, if_neg h]) hγ
    have hsum : -(∑ᶠ (γ : ProperCurve (Q.chain.modelStructure ⟨i, none⟩))
        (_ : closure {γ.point} ⊆ Q.chain.varyingUnion i), ((rv γ : ℤ) - 1)) = ∑ᶠ γ, g γ := by
      rw [← finsum_neg_distrib]
      refine finsum_congr fun γ => ?_
      rw [finsum_eq_if]
      simp only [hg_def]
      split_ifs <;> simp
    have hβg : ∑ᶠ γ, g γ ≤ ∑ᶠ γ, β γ := finsum_le_finsum' hgfin hβfin hg
    linarith
  · rw [finsum_of_infinite_support hβfin]
    positivity

end Proof_prop_mmp_indexb_junction_nonnegative

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

namespace StabilizedTail

namespace PreparedChain

variable {T : StabilizedTail}

/-- At every junction `p_i : (Y_i, Θ_i) ⟶ (X_i, B_i)`, `i ≥ i₀`, of a prepared chain, the
difficulty `𝒟(Y_i, Θ_i)` (`MMP.Fourfold.StabilizedTail.PreparedChain.IsDifficulty`) is
nonnegative. -/
@[mmp "prop_mmp_indexb_junction_nonnegative"]
public theorem difficulty_nonneg_of_junction (Q : PreparedChain T) {i : ℕ} (hi : Q.start ≤ i)
    {D : ℤ} (hD : Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D) : 0 ≤ D :=
      by revert Q i hi D hD; first | exact Proof_prop_mmp_indexb_junction_nonnegative.solution | exact Proof_prop_mmp_indexb_junction_nonnegative.solution _ | exact Proof_prop_mmp_indexb_junction_nonnegative.solution _ _ | exact Proof_prop_mmp_indexb_junction_nonnegative.solution _ _ _ | exact Proof_prop_mmp_indexb_junction_nonnegative.solution _ _ _ _

end PreparedChain

end StabilizedTail

end MMP.Fourfold
