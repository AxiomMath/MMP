module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainWeightMonotone
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.WeightUnitDrop
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.MoveMonotone
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.MoveStrictDecrease
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.UnitDropExceptional
import MMP.RingTheory.SerreCondition.ExtSupportCriterion
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoLogDiscrepancy
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleEmbedding
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic

/-!
# Strict drop of the junction difficulty at a positive-side bad curve

Let `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` be a stabilized tail with a terminal chain whose tail
from the junction `Y_{i₀}` is a prepared chain. Let `i ≥ i₀`, and let `V ⊆ X_{i+1}` be an
irreducible curve contained in the positive-side bad locus `W_i⁺` of the `i`-th step, such that
`X_{i+1}` is smooth at the generic point `η_V` and `mld_{η_V}(X_{i+1}, B_{i+1}) > 1`. Then the
difficulty strictly drops between the junctions: `𝒟(Y_{i+1}, Θ_{i+1}) < 𝒟(Y_i, Θ_i)`.

## Main results

* `MMP.Fourfold.StabilizedTail.PreparedChain.lt_of_isDifficulty_junction_succ`: the strict drop
  of the junction difficulty.

## Implementation notes

The junction `(Y_i, Θ_i)` is the model `(i, none)` of the prepared chain
(`MMP.Fourfold.StabilizedTail.PreparedChain.ModelIndex`). Difficulties are values of the
predicate `MMP.Fourfold.StabilizedTail.PreparedChain.IsDifficulty`, so the statement compares
any two values `D` and `D'` of it at the two junctions. Smoothness of `X_{i+1}` at `η_V` is
regularity of the local ring at `η_V`.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.IndexdJunctionStrictDrop

open MMP.Fourfold MMP.Fourfold.StabilizedTail MMP.Fourfold.StabilizedTail.PreparedChain

open MMP.Mori (QDivisor DivisorOver IsRegularSystemOfParameters IsNormalVariety)
open scoped WithZero
open IsLocalRing

/-! ### Valuations along function field maps -/

/-- Pulling back valuations along a surjective map of fields is injective. -/
private theorem comap_injective {K L : Type*} [Field K] [Field L] {φ : K →+* L}
    (hφ : Function.Surjective φ) {u u' : Valuation L (WithZero (Multiplicative ℤ))}
    (h : u.comap φ = u'.comap φ) : u = u' := by
  ext x
  obtain ⟨y, rfl⟩ := hφ x
  simpa using congrArg (fun w => w y) h

/-- Along a surjective map of fields every valuation of the source is a pull-back. -/
private theorem exists_comap_eq {K L : Type*} [Field K] [Field L] {φ : K →+* L}
    (hφ : Function.Surjective φ) (ν : Valuation K (WithZero (Multiplicative ℤ))) :
    ∃ u : Valuation L (WithZero (Multiplicative ℤ)), u.comap φ = ν := by
  let e := RingEquiv.ofBijective φ ⟨φ.injective, hφ⟩
  refine ⟨ν.comap e.symm.toRingHom, ?_⟩
  ext x
  change ν (e.symm (φ x)) = ν x
  rw [show φ x = e x from rfl, RingEquiv.symm_apply_apply]

/-- The pull-back of a valuation along the function field map of a composite. -/
private theorem comap_functionFieldMap_comp {A B C : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)]
    (u : Valuation A.functionField (WithZero (Multiplicative ℤ))) :
    u.comap (functionFieldMap (a ≫ b)) =
      (u.comap (functionFieldMap a)).comap (functionFieldMap b) := by
  ext t
  simp only [Valuation.comap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- The function field map of a composite is surjective when both factors' are. -/
private theorem surjective_functionFieldMap_comp {A B C : Scheme.{0}} [IsIntegral A]
    [IsIntegral B] [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b]
    [IsDominant (a ≫ b)] (ha : Function.Surjective (functionFieldMap a))
    (hb : Function.Surjective (functionFieldMap b)) :
    Function.Surjective (functionFieldMap (a ≫ b)) := by
  intro t
  obtain ⟨s, rfl⟩ := ha t
  obtain ⟨r, rfl⟩ := hb s
  exact ⟨r, (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply a b r).symm⟩

/-- The function field map of the second factor is surjective when those of the first factor
and of the composite are. -/
private theorem surjective_functionFieldMap_right {A B C : Scheme.{0}} [IsIntegral A]
    [IsIntegral B] [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b]
    [IsDominant (a ≫ b)] (hab : Function.Surjective (functionFieldMap (a ≫ b))) :
    Function.Surjective (functionFieldMap b) := by
  intro t
  obtain ⟨r, hr⟩ := hab (functionFieldMap a t)
  refine ⟨r, (functionFieldMap a).injective ?_⟩
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply, hr]

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
    exact ⟨inferInstance, surjective_functionFieldMap_comp _ _
      hD.isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective.2
      (surjective_functionFieldMap_right _ _ hs)⟩

/-- The map `WithTop ℤ → ℤᵐ⁰` sending `n` to `exp (-n)` and `⊤` to `0`. -/
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
      Ideal.span {x, y} = maximalIdeal A ∧ ringKrullDim A = 2 := by
  rw [MMP.Mori.isRegularSystemOfParameters_iff, Matrix.range_cons, Matrix.range_cons,
    Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl

private lemma isRegularSystemOfParameters_swap {R : Type*} [CommRing R] [IsLocalRing R]
    {x y : R} (hxy : IsRegularSystemOfParameters ![x, y]) :
    IsRegularSystemOfParameters ![y, x] := by
  rw [isRegularSystemOfParameters_pair_iff, Set.pair_comm]
  exact isRegularSystemOfParameters_pair_iff.1 hxy

/-- In `WithBot ℕ∞`, `1 + c = 3` forces `c = 2`. -/
private theorem eq_two_of_one_add_eq_three {c : ℕ∞}
    (h : (1 : WithBot ℕ∞) + (c : WithBot ℕ∞) = 3) : c = 2 := by
  have h' : (1 + c : ℕ∞) = 3 := WithBot.coe_injective (by rwa [WithBot.coe_add])
  induction c using ENat.recTopCoe with
  | top => simp at h'
  | coe n =>
    have : 1 + n = 3 := by exact_mod_cast h'
    norm_cast
    omega

/-- On a normal complex threefold, the order of the local ring at the generic point of an
irreducible closed curve along which it is regular is a generic blowup valuation. -/
private theorem exists_isGenericBlowupValuation {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] (hX : IsNormalVariety ℂ sX) (h3 : topologicalKrullDim X = 3)
    (V : IrreducibleCloseds X) (hV : topologicalKrullDim (V : Set X) = 1)
    (hreg : IsRegularLocalRing (X.presheaf.stalk V.isIrreducible.genericPoint)) :
    ∃ v : Valuation X.functionField ℤᵐ⁰, IsGenericBlowupValuation sX V v := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    V.isIrreducible.genericPoint
  rw [(V.isIrreducible.isGenericPoint_genericPoint V.isClosed).def, hV, h3] at h
  have hcoh : Order.coheight V.isIrreducible.genericPoint = 2 := eq_two_of_one_add_eq_three h
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
  obtain ⟨hfin, -, -, W, hW, -⟩ := MMP.Resolution.exists_addValuation_monomialValuation
    X.functionField (isRegularSystemOfParameters_swap hz') le_rfl
  refine ⟨valuationOfAddValuation W,
    (isGenericBlowupValuation_iff_isWeightedMonomialValuation h3 hV hcodim hz').mpr
      ⟨hX, hcodim, hreg, hz', le_rfl, fun f hf => ?_⟩⟩
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp (hfin f hf)
  refine ⟨M, hM.symm, ?_⟩
  change expNeg (W _) = _
  rw [hW, ← hM]
  rfl

/-! ### Log discrepancies and weights -/

/-- A valuation exceptional over a pair has a log discrepancy. -/
private theorem exists_isValuationLogDiscrepancy {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    (hP : MMP.Mori.IsPair sX B) {u : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (hu : MMP.Intersection.IsExceptionalValuation ℂ sX u) :
    ∃ a : ℝ, IsValuationLogDiscrepancy sX B u a := by
  obtain ⟨D, hDp, rfl, -⟩ := hu
  obtain ⟨-, n, K, hK, -⟩ := id hP
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  exact ⟨_, n, D, hDp, rfl, MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hDp⟩

section Weights

variable {T : StabilizedTail} {C : TerminalChain T}

/-- A valuation exceptional over a model which is a pair has a weight. -/
private theorem exists_isValuationWeight (N : ℕ) {x : C.ModelIndex}
    (hP : MMP.Mori.IsPair (C.modelStructure x) (C.modelBoundary x))
    {u : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ))}
    (hu : MMP.Intersection.IsExceptionalValuation ℂ (C.modelStructure x) u) :
    ∃ w, C.IsValuationWeight N x u w := by
  obtain ⟨a, ha⟩ := exists_isValuationLogDiscrepancy hP hu
  exact ⟨_, hu, a, ha, rfl⟩

end Weights

/-! ### Dimension of centres -/

/-- On a threefold of finite type over `ℂ`, an irreducible closed subset of dimension at most one
has codimension at least two. -/
private theorem two_le_codimension_of_topologicalKrullDim_le_one {X : Scheme.{0}} [IsIntegral X]
    (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] (h3 : topologicalKrullDim X = 3)
    (Z : IrreducibleCloseds X) (hZ : topologicalKrullDim (Z : Set X) ≤ 1) :
    2 ≤ codimension Z := by
  rw [MMP.Flips.codimension_eq_coheight_genericPoint]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    Z.isIrreducible.genericPoint
  rw [(Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).def, h3] at h
  have h' : (3 : WithBot ℕ∞) ≤ 1 + (Order.coheight Z.isIrreducible.genericPoint : WithBot ℕ∞) :=
    h ▸ by gcongr
  generalize Order.coheight Z.isIrreducible.genericPoint = c at h'
  induction c using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
    have h'' : (3 : ℕ∞) ≤ 1 + n := WithBot.coe_le_coe.mp (by rwa [WithBot.coe_add])
    have : 3 ≤ 1 + n := by exact_mod_cast h''
    exact_mod_cast (by omega : 2 ≤ n)

/-- The closure of the generic point of a proper curve, as a subspace of `X`, has dimension
one: it is the image of the closed embedding `C ⟶ X`. -/
private theorem topologicalKrullDim_closure_point {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (C : MMP.Mori.ProperCurve sX) :
    topologicalKrullDim (closure {C.point} : Set X) = 1 := by
  have hr : Set.range C.ι = closure {C.point} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [← hr, ← C.dim_eq]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    C.ι.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

/-! ### Difficulties exist -/

/-- On a model of a prepared chain which is a pair on a threefold, the difficulty exists: the
weights of the valuations centred at closed points and at curves are defined, and the labels have
centres on every model of the prepared chain (they have defaults there). -/
private theorem exists_isDifficulty {T : StabilizedTail} (Q : PreparedChain T)
    (x : Q.ModelIndex)
    (hP : MMP.Mori.IsPair (Q.chain.modelStructure x.1) (Q.chain.modelBoundary x.1))
    (h3 : topologicalKrullDim (Q.chain.model x.1) = 3) : ∃ D, Q.IsDifficulty x D := by
  classical
  have : LocallyOfFiniteType (Q.chain.modelStructure x.1) := hP.1.1.toLocallyOfFiniteType
  have hw : ∀ (v : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)))
      (Z : IrreducibleCloseds (Q.chain.model x.1)),
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z →
      topologicalKrullDim (Z : Set (Q.chain.model x.1)) ≤ 1 →
      ∃ w, Q.chain.IsValuationWeight Q.scale x.1 v w := by
    intro v Z hc hZ
    obtain ⟨E, hEp, hEv, hEZ⟩ := hc
    refine exists_isValuationWeight _ hP ⟨E, hEp, hEv, ?_⟩
    rw [← hEZ]
    exact two_le_codimension_of_topologicalKrullDim_le_one (Q.chain.modelStructure x.1) h3 Z hZ
  let w : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) → ℕ :=
    fun v => if h : ∃ w, Q.chain.IsValuationWeight Q.scale x.1 v w then h.choose else 0
  have hwv : ∀ v, (∃ w, Q.chain.IsValuationWeight Q.scale x.1 v w) →
      Q.chain.IsValuationWeight Q.scale x.1 v (w v) := fun v h => by
    simpa only [w, dif_pos h] using h.choose_spec
  have hcen : ∀ S, ∃ P, Q.chain.IsLabelCentre S x.1 P := fun S => by
    obtain ⟨d, hd⟩ := Q.isLabelDefault_const S
    obtain ⟨b, ⟨P, hP, -⟩, -⟩ := hd x.1 x.2
    exact ⟨P, hP⟩
  choose P hPc using hcen
  choose d hd using Q.isLabelDefault_const
  have hβ : ∀ γ, ∃ β, Q.IsCurveBracket x γ β := fun γ =>
    ⟨_, w, fun S => branchNumber (P S) (closure {γ.point}), d,
      fun v ⟨Z, hc, hZ⟩ => hwv v (hw v Z hc (by rw [hZ, topologicalKrullDim_closure_point])),
      fun S => ⟨P S, hPc S, rfl⟩, fun S => hd S x.1 x.2, rfl⟩
  choose β hβ using hβ
  have hρ : ∀ S, ∃ ρ, Q.chain.IsLabelBoxedRank S x.1 ρ := fun S => ⟨_, P S, hPc S, rfl⟩
  choose ρ hρ using hρ
  refine ⟨_, w, β, d, ρ, fun v ⟨Z, hc, y, _, hZ⟩ => hwv v (hw v Z hc ?_), hβ,
    fun S => hd S x.1 x.2, hρ, rfl⟩
  rw [hZ]
  haveI : DiscreteTopology ({y} : Set (Q.chain.model x.1)) := Subsingleton.discreteTopology
  exact (topologicalKrullDim_zero_of_discreteTopology _).trans zero_le_one

/-! ### Moves of the prepared chain inside a bridge -/

/-- Pulling a valuation back along two morphisms whose composite is `c` is pulling it back along
`c`. -/
private theorem comap_comap_functionFieldMap_of_comp_eq {A B Z : Scheme.{0}} [IsIntegral A]
    [IsIntegral B] [IsIntegral Z] (a : A ⟶ B) (b : B ⟶ Z) (c : A ⟶ Z) [IsDominant a]
    [IsDominant b] [hc : IsDominant c] (h : a ≫ b = c)
    (u : Valuation A.functionField (WithZero (Multiplicative ℤ))) :
    (u.comap (functionFieldMap a)).comap (functionFieldMap b) = u.comap (functionFieldMap c) := by
  rw [← comap_functionFieldMap_comp, MMP.Positivity.DivisorOver.functionFieldMap_congr h]

/-- Composing with an `eqToHom` between the members of a family of objects indexed by equal
indices. -/
private theorem eqToHom_congrArg_comp {F : ℕ → Scheme.{0}} {Z : Scheme.{0}} (G : ∀ n, F n ⟶ Z)
    {a b : ℕ} (h : a = b) : eqToHom (congrArg F h) ≫ G b = G a := by
  subst h
  simp

/-- **A flip move of a bridge.** For the `k`-th flip `V_k → T_k ← V_{k+1}` of the `i`-th bridge
and valuations `u`, `u'` of `ℂ(V_k)`, `ℂ(V_{k+1})` agreeing on `ℂ(T_k)`, with weights `w`, `w'`
and difficulties `E`, `E'`: `E' ≤ E`, `w' ≤ w`, and `E' < E` when `w' < w`. The target is
written by cases on the decision of `k + 1 < m_i`. -/
private theorem flip_step {T : StabilizedTail} (Q : PreparedChain T) {i : ℕ} (hi : Q.start ≤ i)
    (k : Fin (Q.chain.bridge i).P.m) (d : Decidable (k.1 + 1 < (Q.chain.bridge i).P.m))
    {u : Valuation (Q.chain.model ⟨i, some k⟩).functionField (WithZero (Multiplicative ℤ))}
    {w : ℕ} {E : ℤ} (hw : Q.chain.IsValuationWeight Q.scale ⟨i, some k⟩ u w)
    (hE : Q.IsDifficulty ⟨⟨i, some k⟩, hi⟩ E)
    {u' : Valuation (Q.chain.model (Q.chain.flipTargetOf i k d)).functionField
      (WithZero (Multiplicative ℤ))}
    (hrel :
      haveI := Q.chain.isIntegral_flipBase i k
      haveI := Q.chain.isDominant_flipTargetMapOf i k d
      haveI := Q.chain.isDominant_flipSourceMap i k
      u'.comap (functionFieldMap (Q.chain.flipTargetMapOf i k d)) =
        u.comap (functionFieldMap ((Q.chain.bridge i).P.g k)))
    {w' : ℕ} {E' : ℤ} (hw' : Q.chain.IsValuationWeight Q.scale (Q.chain.flipTargetOf i k d) u' w')
    (hx' : Q.start ≤ (Q.chain.flipTargetOf i k d).1)
    (hE' : Q.IsDifficulty ⟨Q.chain.flipTargetOf i k d, hx'⟩ E') :
    E' ≤ E ∧ w' ≤ w ∧ (w' < w → E' < E) := by
  obtain rfl : d = Nat.decLt _ _ := Subsingleton.elim _ _
  let μ : Q.FlipMove := ⟨⟨i, k⟩, hi⟩
  exact ⟨difficulty_le_of_move Q (Or.inr (Or.inr ⟨μ, rfl, rfl⟩)) hE hE',
    (le_of_isValuationWeight_of_move Q).2.2 μ u u' w w' hrel hw hw', fun hlt =>
      difficulty_lt_of_valuationWeight_lt Q
        (Or.inr (Or.inr ⟨μ, rfl, rfl, u, u', w, w', hrel, hw, hw', hlt⟩)) hE hE'⟩

/-- Two stretches of moves, along each of which the difficulty and the weight do not increase
and the difficulty drops strictly wherever the weight does, compose to one such stretch. -/
private theorem move_trans {E₀ E₁ E₂ : ℤ} {w₀ w₁ w₂ : ℕ}
    (h₀₁ : E₁ ≤ E₀ ∧ w₁ ≤ w₀ ∧ (w₁ < w₀ → E₁ < E₀))
    (h₁₂ : E₂ ≤ E₁ ∧ w₂ ≤ w₁ ∧ (w₂ < w₁ → E₂ < E₁)) :
    E₂ ≤ E₀ ∧ w₂ ≤ w₀ ∧ (w₂ < w₀ → E₂ < E₀) := by
  obtain ⟨h1, h2, h3⟩ := h₀₁
  obtain ⟨h1', h2', h3'⟩ := h₁₂
  refine ⟨h1'.trans h1, h2'.trans h2, fun hlt => ?_⟩
  rcases h2.lt_or_eq with h | rfl
  · exact h1'.trans_lt (h3 h)
  · exact (h3' hlt).trans_le h1

/-- Let `a ≫ b = c`, where `b` induces a surjection of function fields. If valuations `u` of the
source and `u'` of the middle agree on the function field of the target, then `u'` is the
pull-back of `u` along `a`. -/
private theorem comap_eq_of_comp_eq {A B Z : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    [IsIntegral Z] (a : A ⟶ B) (b : B ⟶ Z) (c : A ⟶ Z) [ha : IsDominant a] [IsDominant b]
    [hc : IsDominant c] (h : a ≫ b = c) (hb : Function.Surjective (functionFieldMap b))
    {u : Valuation A.functionField ℤᵐ⁰} {u' : Valuation B.functionField ℤᵐ⁰}
    (hu : u.comap (functionFieldMap c) = u'.comap (functionFieldMap b)) :
    u.comap (functionFieldMap a) = u' :=
  comap_injective hb ((comap_comap_functionFieldMap_of_comp_eq a b c h u).trans hu)

/-- The models `V_k` of a bridge are pairs. -/
private theorem isPair_bridge_model {T : StabilizedTail} (Q : PreparedChain T) (i : ℕ)
    (k : Fin (Q.chain.bridge i).P.m) : MMP.Mori.IsPair
      (Q.chain.modelStructure ⟨i, some k⟩) (Q.chain.modelBoundary ⟨i, some k⟩) := by
  have hDk := (Q.chain.bridge i).P.isThreefoldStepDiagram k k.2
  obtain ⟨n, hK⟩ := hDk.isCanonicalDivisor
  exact ⟨hDk.isNormalVariety_minus, n, _, hK, hDk.isQCartier_minus⟩

/-- The base map `h_k` of the `k`-th flip of a bridge is dominant and surjective on function
fields, and a valuation of `ℂ(V_k)` over `ν` restricts along `g_k` and `h_k` to `ν`. -/
private theorem bridge_flip {T : StabilizedTail} (Q : PreparedChain T) {i : ℕ}
    [IsIntegral (T.Z i)] [IsDominant ((Q.chain.junction i).p ≫ T.f i)]
    (hsY : Function.Surjective (functionFieldMap ((Q.chain.junction i).p ≫ T.f i)))
    (ν : Valuation (T.Z i).functionField ℤᵐ⁰) (k : ℕ) (hk : k < (Q.chain.bridge i).P.m) :
    haveI := TerminalChain.isDominant_modelMap_bridge Q.chain i k hk
    haveI := Q.chain.isIntegral_flipBase i ⟨k, hk⟩
    haveI := Q.chain.isDominant_flipSourceMap i ⟨k, hk⟩
    ∃ _ : IsDominant ((Q.chain.bridge i).P.h k),
    Function.Surjective (functionFieldMap ((Q.chain.bridge i).P.h k)) ∧
    ∀ uk : Valuation (Q.chain.model ⟨i, some ⟨k, hk⟩⟩).functionField ℤᵐ⁰,
      uk.comap (functionFieldMap
        (modelMap ((Q.chain.junction i).p ≫ T.f i) (Q.chain.bridge i).P.πY k)) = ν →
      (uk.comap (functionFieldMap ((Q.chain.bridge i).P.g k))).comap
        (functionFieldMap ((Q.chain.bridge i).P.h k)) = ν := by
  have hsk := surjective_functionFieldMap_modelMap_of_le (Q.chain.bridge i).P hsY
  haveI := TerminalChain.isDominant_modelMap_bridge Q.chain i k hk
  have hDk := (Q.chain.bridge i).P.isThreefoldStepDiagram k hk
  haveI := hDk.isNormalVariety_target.1.toIsIntegral
  haveI := hDk.isBirationalMorphism_minus.isDominant
  have hmk := (Q.chain.bridge i).P.modelMap_eq k hk
  haveI : IsDominant ((Q.chain.bridge i).P.g k ≫ (Q.chain.bridge i).P.h k) := hmk ▸ inferInstance
  haveI : IsDominant ((Q.chain.bridge i).P.h k) :=
    IsDominant.of_comp ((Q.chain.bridge i).P.g k) ((Q.chain.bridge i).P.h k)
  refine ⟨inferInstance, surjective_functionFieldMap_right ((Q.chain.bridge i).P.g k) _ ?_,
    fun uk huk => ?_⟩
  · rw [← MMP.Positivity.DivisorOver.functionFieldMap_congr hmk]
    exact (hsk k hk.le).2
  · exact (comap_comap_functionFieldMap_of_comp_eq ((Q.chain.bridge i).P.g k)
      ((Q.chain.bridge i).P.h k) _ (hc := (hsk k hk.le).1) hmk.symm uk).trans huk

/-- **A bridge without flips.** When the `i`-th bridge has no flips, the difficulty and the
weight do not increase from `Y_i` to `Y_{i+1}`, and the difficulty drops when the weight does. -/
private theorem bridge_le_of_m_eq_zero {T : StabilizedTail} (Q : PreparedChain T) {i : ℕ}
    (hi : Q.start ≤ i) [IsIntegral (T.Z i)] [IsDominant ((Q.chain.junction i).p ≫ T.f i)]
    [IsDominant ((Q.chain.junction (i + 1)).p ≫ T.fp i)]
    (hsY' : Function.Surjective (functionFieldMap ((Q.chain.junction (i + 1)).p ≫ T.fp i)))
    (h0 : (Q.chain.bridge i).P.m = 0) {ν : Valuation (T.Z i).functionField ℤᵐ⁰}
    {uY : Valuation (Q.chain.model ⟨i, none⟩).functionField ℤᵐ⁰}
    (huY : uY.comap (functionFieldMap ((Q.chain.junction i).p ≫ T.f i)) = ν)
    {uY' : Valuation (Q.chain.model ⟨i + 1, none⟩).functionField ℤᵐ⁰}
    (huY' : uY'.comap (functionFieldMap ((Q.chain.junction (i + 1)).p ≫ T.fp i)) = ν)
    {wY wY' : ℕ} (hwY : Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ uY wY)
    (hwY' : Q.chain.IsValuationWeight Q.scale ⟨i + 1, none⟩ uY' wY')
    {D D' : ℤ} (hD : Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D)
    (hD' : Q.IsDifficulty ⟨⟨i + 1, none⟩, hi.trans i.le_succ⟩ D') :
    D' ≤ D ∧ wY' ≤ wY ∧ (wY' < wY → D' < D) := by
  have heq : (eqToHom (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y)
      h0.symm) ≫ (Q.chain.bridge i).e.hom) ≫ (Q.chain.junction (i + 1)).p ≫ T.fp i =
      (Q.chain.junction i).p ≫ T.f i := by
    rw [Category.assoc, ← (Q.chain.bridge i).modelMap_eq]
    exact eqToHom_congrArg_comp
      (modelMap ((Q.chain.junction i).p ≫ T.f i) (Q.chain.bridge i).P.πY) h0.symm
  have hdom : IsDominant (eqToHom (congrArg
      (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) h0.symm) ≫
        (Q.chain.bridge i).e.hom) := inferInstance
  rw [← comap_eq_of_comp_eq _ _ _ (ha := hdom)
    (hc := ‹IsDominant ((Q.chain.junction i).p ≫ T.f i)›) heq hsY' (huY.trans huY'.symm)] at hwY'
  exact ⟨difficulty_le_of_move Q (Or.inr (Or.inl ⟨i, hi, h0, rfl, rfl⟩)) hD hD',
    (le_of_isValuationWeight_of_move Q).2.1 i hi h0 uY _ wY wY' rfl hwY hwY',
    fun hlt => difficulty_lt_of_valuationWeight_lt Q
      (Or.inr (Or.inl ⟨i, hi, h0, rfl, rfl, uY, _, wY, wY', rfl, hwY, hwY', hlt⟩)) hD hD'⟩

/-- **The difficulty along the models of a bridge.** For a valuation `ν` of `ℂ(Z_i)` exceptional
over every model `V_k` of the `i`-th bridge, the difficulty and the weight of a valuation of
`ℂ(V_k)` over `ν` are at most those at `Y_i`, and the difficulty is smaller when the weight is. -/
private theorem bridge_model_le {T : StabilizedTail} (Q : PreparedChain T) {i : ℕ}
    (hi : Q.start ≤ i) [IsIntegral (T.Z i)] [IsDominant ((Q.chain.junction i).p ≫ T.f i)]
    (hsY : Function.Surjective (functionFieldMap ((Q.chain.junction i).p ≫ T.f i)))
    {ν : Valuation (T.Z i).functionField ℤᵐ⁰}
    (hexk : ∀ k : Fin (Q.chain.bridge i).P.m,
      haveI := TerminalChain.isDominant_modelMap_bridge Q.chain i k.1 k.2
      ∀ u : Valuation (Q.chain.model ⟨i, some k⟩).functionField ℤᵐ⁰,
        u.comap (functionFieldMap (modelMap ((Q.chain.junction i).p ≫ T.f i)
          (Q.chain.bridge i).P.πY k)) = ν →
        MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, some k⟩) u)
    {uY : Valuation (Q.chain.model ⟨i, none⟩).functionField ℤᵐ⁰}
    (huY : uY.comap (functionFieldMap ((Q.chain.junction i).p ≫ T.f i)) = ν)
    {wY : ℕ} (hwY : Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ uY wY)
    {D : ℤ} (hD : Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D) :
    ∀ k (hk : k < (Q.chain.bridge i).P.m)
      (u : Valuation (Q.chain.model ⟨i, some ⟨k, hk⟩⟩).functionField ℤᵐ⁰),
      (haveI := TerminalChain.isDominant_modelMap_bridge Q.chain i k hk;
        u.comap (functionFieldMap
          (modelMap ((Q.chain.junction i).p ≫ T.f i) (Q.chain.bridge i).P.πY k)) = ν) →
      ∀ (w : ℕ) (E : ℤ), Q.chain.IsValuationWeight Q.scale ⟨i, some ⟨k, hk⟩⟩ u w →
        Q.IsDifficulty ⟨⟨i, some ⟨k, hk⟩⟩, hi⟩ E → E ≤ D ∧ w ≤ wY ∧ (w < wY → E < D) := by
  have hsk := surjective_functionFieldMap_modelMap_of_le (Q.chain.bridge i).P hsY
  intro k
  induction k with
  | zero =>
    intro hk u hu w E hw hE
    obtain rfl : u = uY := comap_injective hsY (hu.trans huY.symm)
    exact ⟨difficulty_le_of_move Q (Or.inl ⟨i, hi, hk, rfl, rfl⟩) hD hE,
      (le_of_isValuationWeight_of_move Q).1 i hi hk u wY w hwY hw, fun hlt =>
        difficulty_lt_of_valuationWeight_lt Q
          (Or.inl ⟨i, hi, hk, rfl, rfl, u, wY, w, hwY, hw, hlt⟩) hD hE⟩
  | succ k ih =>
    intro hk u hu w E hw hE
    have hk' : k < (Q.chain.bridge i).P.m := by omega
    haveI := TerminalChain.isDominant_modelMap_bridge Q.chain i k hk'
    haveI := (hsk (k + 1) hk.le).1
    obtain ⟨uk, huk⟩ := exists_comap_eq (hsk k hk'.le).2 ν
    obtain ⟨wk, hwk⟩ := exists_isValuationWeight Q.scale (isPair_bridge_model Q i ⟨k, hk'⟩)
      (hexk ⟨k, hk'⟩ uk huk)
    obtain ⟨Ek, hEk⟩ := exists_isDifficulty Q ⟨⟨i, some ⟨k, hk'⟩⟩, hi⟩
      (isPair_bridge_model Q i ⟨k, hk'⟩)
      ((Q.chain.bridge i).P.isThreefoldStepDiagram k hk').dim_minus
    obtain ⟨_, hsh, hνk⟩ := bridge_flip Q hsY ν k hk'
    have hDk := (Q.chain.bridge i).P.isThreefoldStepDiagram k hk'
    haveI := hDk.isNormalVariety_target.1.toIsIntegral
    haveI := hDk.isBirationalMorphism_minus.isDominant
    haveI := hDk.isSmallMorphism_plus.isBirationalMorphism.isDominant
    have hrel : u.comap (functionFieldMap ((Q.chain.bridge i).P.gp k)) =
        uk.comap (functionFieldMap ((Q.chain.bridge i).P.g k)) :=
      comap_eq_of_comp_eq ((Q.chain.bridge i).P.gp k) ((Q.chain.bridge i).P.h k)
        (modelMap ((Q.chain.junction i).p ≫ T.f i) (Q.chain.bridge i).P.πY (k + 1))
        (hc := (hsk (k + 1) hk.le).1) ((Q.chain.bridge i).P.modelMap_succ_eq hk').symm hsh
        (hu.trans (hνk uk huk).symm)
    exact move_trans (ih hk' uk huk wk Ek hwk hEk)
      (flip_step Q hi ⟨k, hk'⟩ (isTrue hk) hwk hEk (u' := u) hrel hw hi hE)

/-- Through the last flip of a bridge, the map from `Y_{i+1}` to the base `T_k` of the last flip,
followed by `h_k`, is the map from `Y_{i+1}` to `Z_i`. -/
private theorem bridge_last_comp_eq {T : StabilizedTail} (Q : PreparedChain T) {i k : ℕ}
    (hkm : (Q.chain.bridge i).P.m = k + 1) (hk' : k < (Q.chain.bridge i).P.m) :
    ((Q.chain.bridge i).e.inv ≫
      eqToHom (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) hkm) ≫
        (Q.chain.bridge i).P.gp k) ≫ (Q.chain.bridge i).P.h k =
      (Q.chain.junction (i + 1)).p ≫ T.fp i := by
  have e1 : (eqToHom (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) hkm) ≫
      (Q.chain.bridge i).P.gp k) ≫ (Q.chain.bridge i).P.h k =
      modelMap ((Q.chain.junction i).p ≫ T.f i) (Q.chain.bridge i).P.πY
        (Q.chain.bridge i).P.m :=
    (Category.assoc _ _ _).trans ((congrArg (eqToHom (congrArg
      (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) hkm) ≫ ·)
        ((Q.chain.bridge i).P.modelMap_succ_eq hk').symm).trans
      (eqToHom_congrArg_comp (modelMap ((Q.chain.junction i).p ≫ T.f i)
        (Q.chain.bridge i).P.πY) hkm))
  exact (Category.assoc _ _ _).trans
    ((Iso.inv_comp_eq _).2 (e1.trans (Q.chain.bridge i).modelMap_eq))

/-- **The difficulty along a bridge.** Let `ν` be a valuation of `ℂ(Z_i)` which is exceptional
over every model `V_k` of the `i`-th bridge, and let `u`, `u'` be the valuations over `ν` on the
junctions `Y_i`, `Y_{i+1}`, with weights `w`, `w'`. If `D`, `D'` are difficulties of `Y_i`,
`Y_{i+1}`, then `D' ≤ D`, `w' ≤ w`, and `D' < D` when `w' < w`. -/
private theorem bridge_le {T : StabilizedTail} (Q : PreparedChain T) {i : ℕ} (hi : Q.start ≤ i)
    [IsIntegral (T.Z i)] [IsDominant ((Q.chain.junction i).p ≫ T.f i)]
    [IsDominant ((Q.chain.junction (i + 1)).p ≫ T.fp i)]
    (hsY : Function.Surjective (functionFieldMap ((Q.chain.junction i).p ≫ T.f i)))
    (hsY' : Function.Surjective (functionFieldMap ((Q.chain.junction (i + 1)).p ≫ T.fp i)))
    {ν : Valuation (T.Z i).functionField ℤᵐ⁰}
    (hexk : ∀ k : Fin (Q.chain.bridge i).P.m,
      haveI := TerminalChain.isDominant_modelMap_bridge Q.chain i k.1 k.2
      ∀ u : Valuation (Q.chain.model ⟨i, some k⟩).functionField ℤᵐ⁰,
        u.comap (functionFieldMap (modelMap ((Q.chain.junction i).p ≫ T.f i)
          (Q.chain.bridge i).P.πY k)) = ν →
        MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, some k⟩) u)
    {uY : Valuation (Q.chain.model ⟨i, none⟩).functionField ℤᵐ⁰}
    (huY : uY.comap (functionFieldMap ((Q.chain.junction i).p ≫ T.f i)) = ν)
    {uY' : Valuation (Q.chain.model ⟨i + 1, none⟩).functionField ℤᵐ⁰}
    (huY' : uY'.comap (functionFieldMap ((Q.chain.junction (i + 1)).p ≫ T.fp i)) = ν)
    {wY wY' : ℕ} (hwY : Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ uY wY)
    (hwY' : Q.chain.IsValuationWeight Q.scale ⟨i + 1, none⟩ uY' wY')
    {D D' : ℤ} (hD : Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D)
    (hD' : Q.IsDifficulty ⟨⟨i + 1, none⟩, hi.trans i.le_succ⟩ D') :
    D' ≤ D ∧ wY' ≤ wY ∧ (wY' < wY → D' < D) := by
  rcases Nat.eq_zero_or_pos (Q.chain.bridge i).P.m with h0 | hm
  · exact bridge_le_of_m_eq_zero Q hi hsY' h0 huY huY' hwY hwY' hD hD'
  have hsk := surjective_functionFieldMap_modelMap_of_le (Q.chain.bridge i).P hsY
  obtain ⟨k, hkm⟩ : ∃ k, (Q.chain.bridge i).P.m = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hm).symm⟩
  have hk' : k < (Q.chain.bridge i).P.m := by omega
  have hnot : ¬ (k + 1 < (Q.chain.bridge i).P.m) := by omega
  haveI := TerminalChain.isDominant_modelMap_bridge Q.chain i k hk'
  obtain ⟨uk, huk⟩ := exists_comap_eq (hsk k hk'.le).2 ν
  obtain ⟨wk, hwk⟩ := exists_isValuationWeight Q.scale (isPair_bridge_model Q i ⟨k, hk'⟩)
    (hexk ⟨k, hk'⟩ uk huk)
  obtain ⟨Ek, hEk⟩ := exists_isDifficulty Q ⟨⟨i, some ⟨k, hk'⟩⟩, hi⟩
    (isPair_bridge_model Q i ⟨k, hk'⟩)
    ((Q.chain.bridge i).P.isThreefoldStepDiagram k hk').dim_minus
  obtain ⟨_, hsh, hνk⟩ := bridge_flip Q hsY ν k hk'
  have hDk := (Q.chain.bridge i).P.isThreefoldStepDiagram k hk'
  haveI := hDk.isNormalVariety_target.1.toIsIntegral
  haveI := hDk.isBirationalMorphism_minus.isDominant
  haveI := hDk.isSmallMorphism_plus.isBirationalMorphism.isDominant
  haveI : IsDominant ((Q.chain.bridge i).e.inv ≫
      eqToHom (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) hkm) ≫
        (Q.chain.bridge i).P.gp k) :=
    Q.chain.isDominant_flipTargetMapOf i ⟨k, hk'⟩ (isFalse hnot)
  have hrel : uY'.comap (functionFieldMap ((Q.chain.bridge i).e.inv ≫
      eqToHom (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) hkm) ≫
        (Q.chain.bridge i).P.gp k)) =
      uk.comap (functionFieldMap ((Q.chain.bridge i).P.g k)) :=
    comap_eq_of_comp_eq _ ((Q.chain.bridge i).P.h k) ((Q.chain.junction (i + 1)).p ≫ T.fp i)
      (hc := ‹IsDominant ((Q.chain.junction (i + 1)).p ≫ T.fp i)›)
      (bridge_last_comp_eq Q hkm hk') hsh (huY'.trans (hνk uk huk).symm)
  exact move_trans (bridge_model_le Q hi hsY hexk huY hwY hD k hk' uk huk wk Ek hwk hEk)
    (flip_step Q hi ⟨k, hk'⟩ (isFalse hnot) hwk hEk (u' := uY') hrel hwY'
      (hi.trans i.le_succ) hD')

end MMP.IndexdJunctionStrictDrop

namespace MMP.Fourfold.StabilizedTail.PreparedChain

variable {T : StabilizedTail}

open MMP.IndexdJunctionStrictDrop MMP.Fourfold MMP.Fourfold.StabilizedTail IsLocalRing in
/-- **Strict drop at a positive-side bad curve.** On a prepared chain starting at `Y_{i₀}`, let
`i ≥ i₀` and let `V ⊆ X_{i+1}` be an irreducible curve contained in the positive-side bad locus
`W_i⁺` such that `X_{i+1}` is smooth at `η_V` and `mld_{η_V}(X_{i+1}, B_{i+1}) > 1`. Then the
difficulty of the junction `(Y_{i+1}, Θ_{i+1})` is strictly less than that of `(Y_i, Θ_i)`. -/
@[mmp "lem_mmp_indexd_junction_strict_drop"]
public theorem lt_of_isDifficulty_junction_succ (Q : PreparedChain T) {i : ℕ}
    (hi : Q.start ≤ i) (V : IrreducibleCloseds (T.X (i + 1)))
    (hVW : (V : Set (T.X (i + 1))) ⊆ T.badLocusPlusAt i)
    (hV : topologicalKrullDim (V : Set (T.X (i + 1))) = 1)
    (hreg : IsRegularLocalRing ((T.X (i + 1)).presheaf.stalk V.isIrreducible.genericPoint))
    (hmld : 1 < minimalLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1)) V.isIrreducible.genericPoint)
    {D D' : ℤ} (hD : Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D)
    (hD' : Q.IsDifficulty ⟨⟨i + 1, none⟩, hi.trans i.le_succ⟩ D') : D' < D := by
  have hS := T.isThreefoldStepDiagram i
  haveI := hS.isNormalVariety_target.1.toIsIntegral
  haveI := hS.isBirationalMorphism_minus.isDominant
  haveI := hS.isSmallMorphism_plus.isBirationalMorphism.isDominant
  haveI := (Q.chain.junction i).isBirationalMorphism.isDominant
  haveI := (Q.chain.junction (i + 1)).isBirationalMorphism.isDominant
  haveI : IsDominant ((Q.chain.junction i).p ≫ T.f i) := inferInstance
  haveI : IsDominant ((Q.chain.junction (i + 1)).p ≫ T.fp i) := inferInstance
  -- the generic blowup valuation `v = v_V` and its restriction `ν` to `ℂ(Z_i)`
  obtain ⟨v, hv⟩ := exists_isGenericBlowupValuation hS.isNormalVariety_plus hS.dim_plus V hV hreg
  obtain ⟨hexY, hexk, hexY'⟩ :=
    Q.chain.isExceptionalValuation_of_isGenericBlowupValuation i V hVW hV hreg hmld hv
  set ν := v.comap (functionFieldMap (T.fp i))
  have hfp := hS.isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective
  have hsY : Function.Surjective (functionFieldMap ((Q.chain.junction i).p ≫ T.f i)) :=
    surjective_functionFieldMap_comp _ _
      (Q.chain.junction i).isBirationalMorphism.functionFieldMap_bijective.2
      hS.isBirationalMorphism_minus.functionFieldMap_bijective.2
  have hsY' : Function.Surjective (functionFieldMap ((Q.chain.junction (i + 1)).p ≫ T.fp i)) :=
    surjective_functionFieldMap_comp _ _
      (Q.chain.junction (i + 1)).isBirationalMorphism.functionFieldMap_bijective.2 hfp.2
  -- the valuations over `ν` on the junctions and their weights
  obtain ⟨uY, huY⟩ := exists_comap_eq hsY ν
  obtain ⟨wY, hwY⟩ := exists_isValuationWeight (x := ⟨i, none⟩) Q.scale
    (Q.chain.junction i).isCrepant.1.isPair (hexY uY huY)
  obtain ⟨uY', huY'⟩ := exists_comap_eq hsY' ν
  obtain ⟨wY', hwY'⟩ := exists_isValuationWeight (x := ⟨i + 1, none⟩) Q.scale
    (Q.chain.junction (i + 1)).isCrepant.1.isPair (hexY' uY' huY')
  -- the unit drop `w_v(Y_{i+1}) + 1 ≤ w_v(Y_i)`, through the crepant junctions
  have hdrop : wY' + 1 ≤ wY := by
    obtain ⟨-, aY, haY, rfl⟩ := hwY
    obtain ⟨-, aY', haY', rfl⟩ := hwY'
    have hu : T.IsTransportedValuation i
        (uY.comap (functionFieldMap (Q.chain.junction i).p)) v := by
      change v.comap (functionFieldMap (T.fp i)) =
        (uY.comap (functionFieldMap (Q.chain.junction i).p)).comap (functionFieldMap (T.f i))
      rw [comap_comap_functionFieldMap_of_comp_eq _ _ _ rfl, huY]
    refine Q.isAdmissibleScale.difficultyWeight_add_one_le i V hVW hV hreg hv hu
      (((Q.chain.junction i).isCrepant.2.2 uY aY).1 haY) ?_
    rw [← comap_eq_of_comp_eq _ (T.fp i) _ rfl hfp.2 huY']
    exact ((Q.chain.junction (i + 1)).isCrepant.2.2 uY' aY').1 haY'
  exact (bridge_le Q hi hsY hsY' hexk huY huY' hwY hwY' hD hD').2.2 (by omega)

end MMP.Fourfold.StabilizedTail.PreparedChain
