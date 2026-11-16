module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainBracket
public import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.FourfoldDefs
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.CoefficientDecrease
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.SmallTerminalFlipBadSetFinite
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.SmallTerminalFlipDifference
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.MoveWeight
import MMP.AlgebraicGeometry.MMP.Fourfold.StepBranchesUnitDrop
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.DecreasedPair
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization

/-!
# Strict decrease of the difficulty along a move of a bridge

Let `(Y, Θ) ⤏ (Y', Θ')` be a move of a bridge of a prepared chain of fourfolds: either the
coefficient decrease `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` of the `i`-th bridge, or one of its small
terminal flips. If some normalized divisorial valuation `v`, exceptional over both `Y` and `Y'`,
has strictly smaller weight on the target, `w_v(Y', Θ') < w_v(Y, Θ)`, then the difficulty
strictly decreases: `𝒟(Y', Θ') < 𝒟(Y, Θ)`.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.difficulty_lt_of_valuationWeight_lt`:
  the difficulty strictly decreases along every move of a bridge at which the weight of some
  exceptional valuation strictly decreases.

## Implementation notes

* The moves of the `i`-th bridge, `i ≥ i₀`, are the steps from a model of the chain to the next
  one (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.next`). The coefficient decrease
  starts at the junction `⟨i, none⟩`. When the bridge has a flip (`0 < m_i`) it ends at the
  decreased pair `⟨i, some 0⟩`, whose variety is `Y_i` itself, so a valuation of `ℂ(Y_i)` is a
  valuation of both models. When it has none, the decreased pair is identified with the junction
  `⟨i + 1, none⟩`, and a valuation `v'` of `ℂ(Y_{i+1})` is the valuation `v` of `ℂ(Y_i)` when
  their restrictions to `ℂ(Z_i)` agree, through `f_i ∘ p_i` and `f_i⁺ ∘ p_{i+1}`. The flips are
  `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.FlipMove`, written as step diagrams
  `Y⁻ → Z ← Y⁺`, and `v⁺` is `v⁻` when their restrictions to `ℂ(Z)` agree, as in
  `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.flipBadSet`.
* Weights (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsValuationWeight`, which contains
  that the valuation is exceptional over the model) and difficulties
  (`MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.IsDifficulty`) are predicates on their
  values, and the inequality is stated for all values satisfying them.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry

namespace Proof_prop_oai4_difficulty_iii

open MMP.Mori MMP.Fourfold StabilizedSmallKltTail

/-! ### Valuations and function field maps -/

/-- Restricting a valuation along a composite of dominant morphisms is restricting twice. -/
private theorem comap_functionFieldMap_comp {A B C : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] {c : A ⟶ C}
    [IsDominant c] (hc : a ≫ b = c) (v : Valuation A.functionField (WithZero (Multiplicative ℤ))) :
    v.comap (functionFieldMap c) = (v.comap (functionFieldMap a)).comap (functionFieldMap b) := by
  subst hc
  exact Valuation.ext fun t => by
    simp only [Valuation.comap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- Restricting a valuation along the identity does nothing. -/
private theorem comap_functionFieldMap_id {A : Scheme.{0}} [IsIntegral A]
    (v : Valuation A.functionField (WithZero (Multiplicative ℤ))) :
    v.comap (functionFieldMap (𝟙 A)) = v :=
  Valuation.ext fun t => by rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_id_apply]

/-- Valuations with the same pull-back along a surjective ring map are equal. -/
private theorem valuation_eq_of_comap_eq {K L : Type*} [Field K] [Field L] {e : K →+* L}
    (he : Function.Surjective e) {v w : Valuation L (WithZero (Multiplicative ℤ))}
    (h : v.comap e = w.comap e) : v = w := by
  refine Valuation.ext fun x => ?_
  obtain ⟨y, rfl⟩ := he x
  exact congrArg (fun u : Valuation K (WithZero (Multiplicative ℤ)) => u y) h

/-- Along a bijective ring map every valuation of the source is a pull-back. -/
private theorem exists_comap_eq_of_bijective {K L : Type*} [Field K] [Field L] {e : K →+* L}
    (he : Function.Bijective e) (v : Valuation K (WithZero (Multiplicative ℤ))) :
    ∃ w : Valuation L (WithZero (Multiplicative ℤ)), w.comap e = v := by
  let E := RingEquiv.ofBijective e he
  refine ⟨v.comap (E.symm : L →+* K), Valuation.ext fun t => ?_⟩
  simp only [Valuation.comap_apply]
  exact congrArg v (E.symm_apply_apply t)

variable {T : StabilizedSmallKltTail}

/-- Every valuation of `k(X_i)` corresponds to a valuation of `k(X_0)`. -/
private theorem exists_corresponds (T : StabilizedSmallKltTail) :
    ∀ (i : ℕ) (η : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))),
      ∃ ξ, T.Corresponds i ξ η
  | 0, η => ⟨η, rfl⟩
  | i + 1, η' => by
    haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
    haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_plus.isDominant
    obtain ⟨η, hη⟩ := exists_comap_eq_of_bijective
      (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.functionFieldMap_bijective
      (η'.comap (functionFieldMap (T.fp i)))
    obtain ⟨ξ, hξ⟩ := exists_corresponds T i η
    exact ⟨ξ, η, hξ, hη.symm⟩

/-! ### The models of a terminal chain -/

section Chain

variable (C : TerminalChain T)

/-- After the source of a flip of a bridge comes its target. -/
private theorem next_some_eq_flipTarget (i : ℕ) (k : Fin (C.bridge i).P.m) :
    C.next ⟨i, some k⟩ = C.flipTarget i k := by
  by_cases h : k.1 + 1 < (C.bridge i).P.m
  · rw [C.flipTarget_of_lt h]
    simp only [TerminalChain.next, h, ↓reduceDIte]
  · rw [C.flipTarget_of_not_lt h]
    simp only [TerminalChain.next, h, ↓reduceDIte]

/-- After the `n`-th model, a junction `Y_i`, come the models `V_k` of the `i`-th bridge. -/
private theorem modelIndexSeq_add_of_eq_none {i n : ℕ} (hn : C.modelIndexSeq n = ⟨i, none⟩) :
    ∀ (k : ℕ) (hk : k < (C.bridge i).P.m), C.modelIndexSeq (n + 1 + k) = ⟨i, some ⟨k, hk⟩⟩
  | 0, hk => by rw [Nat.add_zero, TerminalChain.modelIndexSeq_succ, hn, C.next_none_of_pos hk]
  | k + 1, hk => by
    rw [show n + 1 + (k + 1) = n + 1 + k + 1 from rfl, TerminalChain.modelIndexSeq_succ,
      modelIndexSeq_add_of_eq_none hn k (by omega)]
    simp only [TerminalChain.next, hk, ↓reduceDIte]

/-- Every junction index `⟨i, none⟩` occurs in `modelIndexSeq`. -/
private theorem exists_modelIndexSeq_eq_none : ∀ i : ℕ, ∃ n, C.modelIndexSeq n = ⟨i, none⟩
  | 0 => ⟨0, rfl⟩
  | i + 1 => by
    obtain ⟨n, hn⟩ := exists_modelIndexSeq_eq_none i
    by_cases h : 0 < (C.bridge i).P.m
    · refine ⟨n + 1 + ((C.bridge i).P.m - 1) + 1, ?_⟩
      rw [TerminalChain.modelIndexSeq_succ, modelIndexSeq_add_of_eq_none C hn _ (by omega)]
      have h' : ¬ (C.bridge i).P.m - 1 + 1 < (C.bridge i).P.m := by omega
      simp only [TerminalChain.next, h', ↓reduceDIte]
    · exact ⟨n + 1, by rw [TerminalChain.modelIndexSeq_succ, hn, C.next_none_of_not_pos (by omega)]⟩

/-- Every model index of the chain occurs in the sequence `modelIndexSeq`. -/
private theorem exists_modelIndexSeq_eq (x : C.ModelIndex) : ∃ n, C.modelIndexSeq n = x := by
  obtain ⟨i, _ | k⟩ := x
  · exact exists_modelIndexSeq_eq_none C i
  · obtain ⟨n, hn⟩ := exists_modelIndexSeq_eq_none C i
    exact ⟨n + 1 + k.1, modelIndexSeq_add_of_eq_none C hn k.1 k.2⟩

/-- The morphisms `π_k : V_k ⟶ Z_i` of a bridge are dominant. -/
private theorem isDominant_toBase (i : ℕ) :
    ∀ k ≤ (C.bridge i).P.m, IsDominant ((C.bridge i).P.toBase k)
  | 0, _ => by
    haveI := (C.junction i).isBirationalMorphism.isDominant
    haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
    change IsDominant ((C.junction i).p ≫ T.f i)
    infer_instance
  | k + 1, hk => by
    have hS := (C.bridge i).P.isFourfoldStepDiagram k hk
    haveI := isDominant_toBase i k (Nat.le_of_succ_le hk)
    haveI : IsDominant ((C.bridge i).P.g k) := hS.isBirationalMorphism_minus.isDominant
    haveI : IsDominant ((C.bridge i).P.gp k) := hS.isBirationalMorphism_plus.isDominant
    haveI : IsDominant ((C.bridge i).P.g k ≫ (C.bridge i).P.h k) := by
      rw [← (C.bridge i).P.modelMap_eq k hk]
      infer_instance
    haveI := IsDominant.of_comp ((C.bridge i).P.g k) ((C.bridge i).P.h k)
    change IsDominant ((C.bridge i).P.πY k)
    rw [(C.bridge i).P.πY_eq k hk]
    infer_instance

end Chain

/-! ### Monotonicity of weights along a move -/

section Monotone

variable (Q : PreparedChain T)

/-- Weights do not increase from a model of the prepared chain to the next one, for two
incarnations of the same valuation of `k(X_0)`. -/
private theorem le_of_next_eq {x y : Q.chain.ModelIndex} (hxy : Q.chain.next x = y)
    (ξ : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ)))
    (v : Valuation (Q.chain.model x).functionField (WithZero (Multiplicative ℤ)))
    (v' : Valuation (Q.chain.model y).functionField (WithZero (Multiplicative ℤ)))
    (hv : Q.chain.IsIncarnation ξ x v) (hv' : Q.chain.IsIncarnation ξ y v') {w w' : ℕ}
    (hw : Q.chain.IsValuationWeight Q.scale x v w)
    (hw' : Q.chain.IsValuationWeight Q.scale y v' w') : w' ≤ w := by
  obtain ⟨n, rfl⟩ := exists_modelIndexSeq_eq Q.chain x
  obtain rfl : Q.chain.modelIndexSeq (n + 1) = y := (Q.chain.modelIndexSeq_succ n).trans hxy
  exact PreparedChain.le_of_isValuationWeight_succ Q n ξ v v' hv hv' hw hw'

end Monotone

/-! ### Exceptional valuations and their weights -/

section Weights

/-- **Exceptionality is transported along an isomorphism.** If `φ : A ≅ X` is an isomorphism
over `ℂ` and `v` is exceptional over `A`, then `v ∘ φ^*` is exceptional over `X`. -/
private theorem isExceptionalValuation_comap_of_iso {A X : Scheme.{0}} [IsIntegral A]
    [IsLocallyNoetherian A] [IsNormal A] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sA : A ⟶ Spec (.of ℂ)} {sX : X ⟶ Spec (.of ℂ)} (φ : A ≅ X) (hφ : φ.hom ≫ sX = sA)
    {v : Valuation A.functionField (WithZero (Multiplicative ℤ))}
    (h : MMP.Intersection.IsExceptionalValuation ℂ sA v) :
    MMP.Intersection.IsExceptionalValuation ℂ sX (v.comap (functionFieldMap φ.hom)) := by
  obtain ⟨D, hDp, rfl, hcod⟩ := h
  haveI := hDp
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  let D' : DivisorOver ℂ sX :=
    { Y := D.Y
      f := D.f ≫ φ.hom
      isNormalVariety := by
        rw [Category.assoc, hφ]
        exact D.isNormalVariety
      isBirationalMorphism := isBirationalMorphism_comp_of_isBirational φ.hom D.f
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
          (isBirationalMorphism_of_isIso _))
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D.isBirationalMorphism)
      E := D.E }
  refine ⟨D', (inferInstance : IsProper (D.f ≫ φ.hom)), ?_, ?_⟩
  · ext t
    change D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap φ.hom t)) =
      D.E.divisorialValuation (functionFieldMap (D.f ≫ φ.hom) t)
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  · rw [MMP.Positivity.DivisorOver.codimension_center] at hcod ⊢
    change 2 ≤ Order.coheight ((D.f ≫ φ.hom) D.E.genericPoint)
    rw [Scheme.Hom.comp_apply, Topology.IsOpenEmbedding.coheight_eq _ φ.hom.isOpenEmbedding]
    exact hcod

variable (Q : PreparedChain T)

/-- Every valuation exceptional over a model of the chain has a weight there. -/
private theorem exists_isValuationWeight (x : Q.chain.ModelIndex)
    {v : Valuation (Q.chain.model x).functionField (WithZero (Multiplicative ℤ))}
    (hv : MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure x) v) :
    ∃ w, Q.chain.IsValuationWeight Q.scale x v w := by
  have hP := (TerminalChain.isKltTerminalPair_modelBoundary Q.chain x).1.1.1.isPair
  obtain ⟨-, n, K, hK, -⟩ := id hP
  obtain ⟨D, hDp, hDv, -⟩ := id hv
  obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  exact ⟨_, hv, _, ⟨n, D, hDp, hDv.symm,
    MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hb hDp⟩, rfl⟩

end Weights

/-- A finite sum of nonnegative differences with one positive summand is positive. -/
private theorem sum_sub_pos_of_le_of_lt {ι : Type*} (F : Finset ι) (f g : ι → ℕ)
    (hle : ∀ u ∈ F, g u ≤ f u) {v : ι} (hv : v ∈ F) (hlt : g v < f v) :
    0 < ∑ u ∈ F, ((f u : ℤ) - g u) :=
  Finset.sum_pos' (fun u hu => by have := hle u hu; omega) ⟨v, hv, by omega⟩

/-! ### The two kinds of moves -/

section Moves

variable (Q : PreparedChain T)

/-- **A coefficient decrease.** Let `(Y_i, Θ_i) ⇝ (Y', Θ')` be the coefficient decrease of the
`i`-th bridge, identified with `(Y_i, Θ_i')` by `φ`, along which weights do not increase. If the
weight of an exceptional valuation drops strictly, so does the difficulty. -/
private theorem difficulty_lt_of_coefficientMove {i : ℕ} (hi : Q.start ≤ i)
    {y : Q.chain.ModelIndex} (hy : Q.chain.next ⟨i, none⟩ = y) (hy' : Q.start ≤ y.1)
    (φ : Q.chain.model ⟨i, none⟩ ≅ Q.chain.model y)
    (hφ : φ.hom ≫ Q.chain.modelStructure y = Q.chain.modelStructure ⟨i, none⟩)
    (hΘ : (Q.chain.bridge i).Θ' = inverseTransformDivisor φ.hom (Q.chain.modelBoundary y))
    (hmono : ∀ u, MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) u →
      ∀ a b : ℕ, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ u a →
        Q.chain.IsValuationWeight Q.scale y (u.comap (functionFieldMap φ.hom)) b → b ≤ a)
    (v : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)))
    {w w' : ℕ} (hw : Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w)
    (hw' : Q.chain.IsValuationWeight Q.scale y (v.comap (functionFieldMap φ.hom)) w')
    (hlt : w' < w) {D D' : ℤ} (hD : Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D)
    (hD' : Q.IsDifficulty ⟨y, hy'⟩ D') : D' < D := by
  classical
  subst hy
  obtain ⟨F, hFexc, hout, hsum⟩ := Q.exists_finset_difficulty_sub_eq_sum hi φ hφ hΘ hy'
  have hvF : v ∈ F := by
    by_contra h
    have := hout v hw.1 h w w' hw hw'
    omega
  have hex : ∀ u ∈ F, ∃ a b : ℕ, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ u a ∧
      Q.chain.IsValuationWeight Q.scale (Q.chain.next ⟨i, none⟩)
        (u.comap (functionFieldMap φ.hom)) b ∧ (u = v → a = w ∧ b = w') := by
    intro u hu
    by_cases huv : u = v
    · subst huv
      exact ⟨w, w', hw, hw', fun _ => ⟨rfl, rfl⟩⟩
    · obtain ⟨a, ha⟩ := exists_isValuationWeight Q _ (hFexc u hu)
      obtain ⟨b, hb⟩ := exists_isValuationWeight Q _
        (isExceptionalValuation_comap_of_iso φ hφ (hFexc u hu))
      exact ⟨a, b, ha, hb, fun h => absurd h huv⟩
  choose! a b ha hb hab using hex
  have hdiff := hsum D D' hD hD' a b ha hb
  have hpos := sum_sub_pos_of_le_of_lt F a b
    (fun u hu => hmono u (hFexc u hu) _ _ (ha u hu) (hb u hu)) hvF
    (by rw [(hab v hvF rfl).1, (hab v hvF rfl).2]; exact hlt)
  linarith

/-- The incarnation of `ξ` on the target of a flip of a bridge, from that on its source. -/
private theorem isIncarnation_flipTargetOf (i : ℕ) (k : Fin (Q.chain.bridge i).P.m)
    (d : Decidable (k.1 + 1 < (Q.chain.bridge i).P.m))
    (ξ : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ)))
    (w₀ : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))
    (hξ : T.Corresponds i ξ w₀)
    (u : Valuation ((Q.chain.bridge i).P.model k).functionField (WithZero (Multiplicative ℤ)))
    (hu : haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
      haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
      haveI := isDominant_toBase Q.chain i k k.2.le
      u.comap (functionFieldMap ((Q.chain.bridge i).P.toBase k)) =
        w₀.comap (functionFieldMap (T.f i)))
    (u' : Valuation (Q.chain.model (Q.chain.flipTargetOf i k d)).functionField
      (WithZero (Multiplicative ℤ)))
    (h : haveI := Q.chain.isIntegral_flipBase i k
      haveI := Q.chain.isDominant_flipTargetMapOf i k d
      haveI := Q.chain.isDominant_flipSourceMap i k
      u'.comap (functionFieldMap (Q.chain.flipTargetMapOf i k d)) =
        u.comap (functionFieldMap ((Q.chain.bridge i).P.g k))) :
    Q.chain.IsIncarnation ξ (Q.chain.flipTargetOf i k d) u' := by
  haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := isDominant_toBase Q.chain i k k.2.le
  haveI := Q.chain.isIntegral_flipBase i k
  haveI := Q.chain.isDominant_flipTargetMapOf i k d
  haveI := Q.chain.isDominant_flipSourceMap i k
  have hS := (Q.chain.bridge i).P.isFourfoldStepDiagram k k.2
  haveI : IsDominant ((Q.chain.bridge i).P.gp k) := hS.isBirationalMorphism_plus.isDominant
  have hgh := ((Q.chain.bridge i).P.modelMap_eq k k.2).symm
  haveI : IsDominant ((Q.chain.bridge i).P.g k ≫ (Q.chain.bridge i).P.h k) := by
    rw [hgh]; infer_instance
  haveI := IsDominant.of_comp ((Q.chain.bridge i).P.g k) ((Q.chain.bridge i).P.h k)
  have hsrc : (u.comap (functionFieldMap ((Q.chain.bridge i).P.g k))).comap
      (functionFieldMap ((Q.chain.bridge i).P.h k)) = w₀.comap (functionFieldMap (T.f i)) := by
    rw [← comap_functionFieldMap_comp _ _ hgh]
    exact hu
  cases d with
  | isTrue hk =>
    haveI : IsDominant ((Q.chain.bridge i).P.πY k) := isDominant_toBase Q.chain i (k.1 + 1) hk.le
    refine ⟨w₀, hξ, (inferInstance : IsDominant ((Q.chain.bridge i).P.πY k)), ?_⟩
    exact (comap_functionFieldMap_comp ((Q.chain.bridge i).P.gp k) ((Q.chain.bridge i).P.h k)
      ((Q.chain.bridge i).P.πY_eq k k.2).symm u').trans
      ((congrArg (fun t => t.comap (functionFieldMap ((Q.chain.bridge i).P.h k))) h).trans hsrc)
  | isFalse hk =>
    haveI := (Q.chain.junction (i + 1)).isBirationalMorphism.isDominant
    haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_plus.isDominant
    have key : ∀ (m : ℕ) (e : (Q.chain.bridge i).P.model m ≅ (Q.chain.junction (i + 1)).Y)
        (hmk : m = k.1 + 1), (Q.chain.bridge i).P.toBase m =
          e.hom ≫ (Q.chain.junction (i + 1)).p ≫ T.fp i →
        (e.inv ≫ eqToHom (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) hmk)
          ≫ (Q.chain.bridge i).P.gp k) ≫ (Q.chain.bridge i).P.h k =
          (Q.chain.junction (i + 1)).p ≫ T.fp i := by
      rintro m e rfl hπ
      simp only [eqToHom_refl, Category.assoc]
      erw [Category.id_comp]
      calc e.inv ≫ (Q.chain.bridge i).P.gp k ≫ (Q.chain.bridge i).P.h k
          = e.inv ≫ (Q.chain.bridge i).P.toBase (k.1 + 1) :=
            congrArg (e.inv ≫ ·) ((Q.chain.bridge i).P.πY_eq k k.2).symm
        _ = _ := by rw [hπ, e.inv_hom_id_assoc]
    have hc := key _ (Q.chain.bridge i).e (by omega) (Q.chain.bridge i).toBase_end_eq
    haveI : IsDominant ((Q.chain.junction (i + 1)).p ≫ T.fp i) :=
      (IsDominant.comp_iff _ _).mpr inferInstance
    have hdom : IsDominant (X := Q.chain.model (Q.chain.flipTargetOf i k (isFalse hk)))
      ((Q.chain.junction (i + 1)).p ≫ T.fp i) := this
    let u'' : Valuation (Q.chain.junction (i + 1)).Y.functionField (WithZero (Multiplicative ℤ)) :=
      u'
    refine ⟨u''.comap (functionFieldMap (Q.chain.junction (i + 1)).p), ⟨w₀, hξ, ?_⟩, rfl⟩
    have h1 := comap_functionFieldMap_comp (Q.chain.junction (i + 1)).p (T.fp i)
      (c := (Q.chain.junction (i + 1)).p ≫ T.fp i) rfl u''
    have h2 := @comap_functionFieldMap_comp _ _ _ _ _ _
      (Q.chain.flipTargetMapOf i k (isFalse hk)) ((Q.chain.bridge i).P.h k) _ _ _ hdom hc u'
    exact h1.symm.trans (h2.trans
      ((congrArg (fun t => t.comap (functionFieldMap ((Q.chain.bridge i).P.h k))) h).trans hsrc))

/-- Weights do not increase under a small terminal flip: if `u'` on the target and `u` on the
source restrict to the same valuation of the base, then `w_{u'} ≤ w_u`. -/
private theorem le_of_flipMove (μ : Q.FlipMove)
    (u : Valuation (Q.chain.model μ.source.1).functionField (WithZero (Multiplicative ℤ)))
    (u' : Valuation (Q.chain.model μ.target.1).functionField (WithZero (Multiplicative ℤ)))
    (h : u'.comap (functionFieldMap μ.targetMap) = u.comap (functionFieldMap μ.sourceMap))
    {a b : ℕ} (ha : Q.chain.IsValuationWeight Q.scale μ.source.1 u a)
    (hb : Q.chain.IsValuationWeight Q.scale μ.target.1 u' b) : b ≤ a := by
  obtain ⟨⟨i, k⟩, _⟩ := μ
  haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := isDominant_toBase Q.chain i k k.2.le
  obtain ⟨w₀, hw₀⟩ := exists_comap_eq_of_bijective
    (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.functionFieldMap_bijective
    ((u : Valuation ((Q.chain.bridge i).P.model k).functionField
      (WithZero (Multiplicative ℤ))).comap (functionFieldMap ((Q.chain.bridge i).P.toBase k)))
  obtain ⟨ξ, hξ⟩ := exists_corresponds T i w₀
  exact le_of_next_eq Q (x := ⟨i, some k⟩) (next_some_eq_flipTarget Q.chain i k) ξ u u'
    ⟨w₀, hξ, inferInstance, hw₀.symm⟩
    (isIncarnation_flipTargetOf Q i k _ ξ w₀ hξ u hw₀.symm u' h) ha hb

end Moves

/-! ### The strict decrease -/

section StrictDecrease

variable (Q : PreparedChain T)

/-- The difficulty strictly decreases along the coefficient decrease of a bridge with a flip,
at which the weight of an exceptional valuation strictly decreases. -/
private theorem difficulty_lt_of_coefficientMove_of_pos :
    ∀ {i : ℕ} (hi : Q.start ≤ i) (hm : 0 < (Q.chain.bridge i).P.m)
        (v : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)))
        (w w' : ℕ), Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w →
        Q.chain.IsValuationWeight Q.scale ⟨i, some ⟨0, hm⟩⟩ v w' → w' < w →
        ∀ D D' : ℤ, Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D →
          Q.IsDifficulty ⟨⟨i, some ⟨0, hm⟩⟩, hi⟩ D' → D' < D := by
  intro i hi hm v w w' hw hw' hlt D D' hD hD'
  refine difficulty_lt_of_coefficientMove Q hi (y := ⟨i, some ⟨0, hm⟩⟩)
    (Q.chain.next_none_of_pos hm) hi (Iso.refl _) (Category.id_comp _)
    (inverseTransformDivisor_id _).symm ?_ v hw ?_ hlt hD hD'
  · intro u _ a b ha hb
    obtain ⟨-, a', ha', rfl⟩ := ha
    obtain ⟨-, b', hb', rfl⟩ := hb
    have hb'' := (congrArg (fun t : Valuation (Q.chain.junction i).Y.functionField
        (WithZero (Multiplicative ℤ)) =>
          IsValuationLogDiscrepancy (Q.chain.junction i).sY (Q.chain.bridge i).Θ' t b')
      (comap_functionFieldMap_id u)).mp hb'
    exact difficultyWeight_mono _ (sub_le_sub_left
      ((Q.chain.bridge i).isDecreasedBoundary.le_of_isValuationLogDiscrepancy ha' hb'') 2)
  · exact (congrArg (fun t : Valuation (Q.chain.model ⟨i, some ⟨0, hm⟩⟩).functionField
        (WithZero (Multiplicative ℤ)) => Q.chain.IsValuationWeight Q.scale ⟨i, some ⟨0, hm⟩⟩ t w')
      (comap_functionFieldMap_id v)).mpr hw'

/-- The difficulty strictly decreases along the coefficient decrease of a bridge without flips,
at which the weight of an exceptional valuation strictly decreases. -/
private theorem difficulty_lt_of_coefficientMove_of_eq_zero :
    ∀ {i : ℕ} (hi : Q.start ≤ i), (Q.chain.bridge i).P.m = 0 →
        haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
        haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
        haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_plus.isDominant
        haveI := (Q.chain.junction i).isBirationalMorphism.isDominant
        haveI := (Q.chain.junction (i + 1)).isBirationalMorphism.isDominant
        ∀ (v : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)))
          (v' : Valuation (Q.chain.model ⟨i + 1, none⟩).functionField
            (WithZero (Multiplicative ℤ))),
          v'.comap (functionFieldMap ((Q.chain.junction (i + 1)).p ≫ T.fp i)) =
            v.comap (functionFieldMap ((Q.chain.junction i).p ≫ T.f i)) →
          ∀ w w' : ℕ, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w →
            Q.chain.IsValuationWeight Q.scale ⟨i + 1, none⟩ v' w' → w' < w →
            ∀ D D' : ℤ, Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D →
              Q.IsDifficulty ⟨⟨i + 1, none⟩, hi.trans (Nat.le_succ i)⟩ D' → D' < D := by
  intro i hi hm0 v v' hvv' w w' hw hw' hlt D D' hD hD'
  haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_plus.isDominant
  haveI := (Q.chain.junction i).isBirationalMorphism.isDominant
  haveI := (Q.chain.junction (i + 1)).isBirationalMorphism.isDominant
  haveI : IsDominant ((Q.chain.junction i).p ≫ T.f i) :=
    (IsDominant.comp_iff _ _).mpr inferInstance
  haveI : IsDominant ((Q.chain.junction (i + 1)).p ≫ T.fp i) :=
    (IsDominant.comp_iff _ _).mpr inferInstance
  have hsurj : Function.Surjective
      (functionFieldMap ((Q.chain.junction (i + 1)).p ≫ T.fp i)) := by
    intro z
    obtain ⟨y, rfl⟩ :=
      (Q.chain.junction (i + 1)).isBirationalMorphism.functionFieldMap_bijective.2 z
    obtain ⟨x, rfl⟩ :=
      (T.isFourfoldStepDiagram i).isBirationalMorphism_plus.functionFieldMap_bijective.2 y
    exact ⟨x, (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply _ _ x).symm⟩
  have key : ∀ (m : ℕ) (e : (Q.chain.bridge i).P.model m ≅ (Q.chain.junction (i + 1)).Y),
      e.hom ≫ (Q.chain.junction (i + 1)).sY = (Q.chain.bridge i).P.modelStructure m →
      (Q.chain.bridge i).P.boundary m =
        inverseTransformDivisor e.hom (Q.chain.junction (i + 1)).Θ →
      (Q.chain.bridge i).P.toBase m = e.hom ≫ (Q.chain.junction (i + 1)).p ≫ T.fp i →
      m = 0 → D' < D := by
    rintro m e he hΘ hπ rfl
    let e' : (Q.chain.junction i).Y ≅ (Q.chain.junction (i + 1)).Y := e
    have hπ' : e'.hom ≫ (Q.chain.junction (i + 1)).p ≫ T.fp i =
        (Q.chain.junction i).p ≫ T.f i := hπ.symm
    have hv' : v' = v.comap (functionFieldMap e'.hom) := by
      refine valuation_eq_of_comap_eq hsurj ?_
      rw [← comap_functionFieldMap_comp e'.hom _ hπ' v]
      exact hvv'
    subst hv'
    refine difficulty_lt_of_coefficientMove Q hi (y := ⟨i + 1, none⟩)
      (Q.chain.next_none_of_not_pos (by omega)) (hi.trans (Nat.le_succ i)) e' he hΘ ?_ v hw hw'
      hlt hD hD'
    intro u _ a b ha hb
    obtain ⟨ξ, hξ⟩ := exists_corresponds T i (u.comap (functionFieldMap (Q.chain.junction i).p))
    refine le_of_next_eq Q (Q.chain.next_none_of_not_pos (by omega)) ξ u _ ⟨_, hξ, rfl⟩ ?_ ha hb
    refine ⟨_, ⟨_, hξ, ?_⟩, rfl⟩
    have h1 := comap_functionFieldMap_comp (Q.chain.junction (i + 1)).p (T.fp i) rfl
      (u.comap (functionFieldMap e'.hom))
    have h2 := comap_functionFieldMap_comp e'.hom _ hπ' u
    have h3 := comap_functionFieldMap_comp (Q.chain.junction i).p (T.f i) rfl u
    exact h1.symm.trans (h2.symm.trans h3)
  exact key _ (Q.chain.bridge i).e (Q.chain.bridge i).comp_sY
    (Q.chain.bridge i).endBoundary_eq (Q.chain.bridge i).toBase_end_eq hm0

/-- The difficulty strictly decreases along a small terminal flip at which the weight of an
exceptional valuation strictly decreases. -/
private theorem difficulty_lt_of_flipMove :
    ∀ (μ : Q.FlipMove)
        (v : Valuation (Q.chain.model μ.source.1).functionField (WithZero (Multiplicative ℤ)))
        (v' : Valuation (Q.chain.model μ.target.1).functionField (WithZero (Multiplicative ℤ))),
        v'.comap (functionFieldMap μ.targetMap) = v.comap (functionFieldMap μ.sourceMap) →
        ∀ w w' : ℕ, Q.chain.IsValuationWeight Q.scale μ.source.1 v w →
          Q.chain.IsValuationWeight Q.scale μ.target.1 v' w' → w' < w →
          ∀ D D' : ℤ, Q.IsDifficulty μ.source D → Q.IsDifficulty μ.target D' → D' < D := by
  intro μ v v' hvv' w w' hw hw' hlt D D' hD hD'
  classical
  have hvA : v ∈ Q.flipBadSet μ := by
    by_contra h
    have := (PreparedChain.isValuationWeight_target_iff_of_notMem_flipBadSet μ h hvv' hw
      w').1 hw'
    omega
  have hfin := Q.finite_flipBadSet μ
  have hex : ∀ u ∈ Q.flipBadSet μ, ∃ (a b : ℕ)
      (u' : Valuation (Q.chain.model μ.target.1).functionField (WithZero (Multiplicative ℤ))),
      u'.comap (functionFieldMap μ.targetMap) = u.comap (functionFieldMap μ.sourceMap) ∧
      Q.chain.IsValuationWeight Q.scale μ.source.1 u a ∧
      Q.chain.IsValuationWeight Q.scale μ.target.1 u' b ∧ (u = v → a = w ∧ b = w') := by
    intro u hu
    by_cases huv : u = v
    · subst huv
      exact ⟨w, w', v', hvv', hw, hw', fun _ => ⟨rfl, rfl⟩⟩
    · obtain ⟨-, u', hu', a, b, ha, hb, -⟩ := hu
      exact ⟨a, b, u', hu', ha, hb, fun h => absurd h huv⟩
  choose! a b u' hu' ha hb hab using hex
  have hdiff := Q.difficulty_sub_eq_finsum_flipBadSet μ D D' hD hD' a b ha
    (fun u hu => ⟨u' u, hu' u hu, hb u hu⟩)
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hdiff
  have hpos := sum_sub_pos_of_le_of_lt hfin.toFinset a b
    (fun u hu => le_of_flipMove Q μ u (u' u) (hu' u (hfin.mem_toFinset.1 hu))
      (ha u (hfin.mem_toFinset.1 hu)) (hb u (hfin.mem_toFinset.1 hu)))
    (hfin.mem_toFinset.2 hvA) (by rw [(hab v hvA rfl).1, (hab v hvA rfl).2]; exact hlt)
  linarith

end StrictDecrease

end Proof_prop_oai4_difficulty_iii

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

variable {T : StabilizedSmallKltTail} (Q : PreparedChain T)

/-- On a prepared chain, let `(Y, Θ) ⤏ (Y', Θ')` be a move of a bridge and let `v` be a
normalized divisorial valuation exceptional over `Y` and over `Y'` with
`w_v(Y', Θ') < w_v(Y, Θ)`. Then `𝒟(Y', Θ') < 𝒟(Y, Θ)`. The three conjuncts are the three shapes
of a move of the `i`-th bridge, `i ≥ i₀`: the coefficient decrease `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` to
the model `⟨i, some 0⟩` when the bridge has a flip; the coefficient decrease to the junction
`(Y_{i+1}, Θ_{i+1})` when it has none, a valuation `v'` of `ℂ(Y_{i+1})` being `v` when both
restrict to the same valuation of `ℂ(Z_i)`; and a small terminal flip
(`MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.FlipMove`) `Y⁻ → Z ← Y⁺`, `v⁺` being `v⁻`
when both restrict to the same valuation of `ℂ(Z)`. -/
@[mmp "prop_oai4_difficulty_iii"]
public theorem difficulty_lt_of_valuationWeight_lt :
    (∀ {i : ℕ} (hi : Q.start ≤ i) (hm : 0 < (Q.chain.bridge i).P.m)
        (v : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)))
        (w w' : ℕ), Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w →
        Q.chain.IsValuationWeight Q.scale ⟨i, some ⟨0, hm⟩⟩ v w' → w' < w →
        ∀ D D' : ℤ, Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D →
          Q.IsDifficulty ⟨⟨i, some ⟨0, hm⟩⟩, hi⟩ D' → D' < D) ∧
    (∀ {i : ℕ} (hi : Q.start ≤ i), (Q.chain.bridge i).P.m = 0 →
        haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
        haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
        haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_plus.isDominant
        haveI := (Q.chain.junction i).isBirationalMorphism.isDominant
        haveI := (Q.chain.junction (i + 1)).isBirationalMorphism.isDominant
        ∀ (v : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)))
          (v' : Valuation (Q.chain.model ⟨i + 1, none⟩).functionField
            (WithZero (Multiplicative ℤ))),
          v'.comap (functionFieldMap ((Q.chain.junction (i + 1)).p ≫ T.fp i)) =
            v.comap (functionFieldMap ((Q.chain.junction i).p ≫ T.f i)) →
          ∀ w w' : ℕ, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w →
            Q.chain.IsValuationWeight Q.scale ⟨i + 1, none⟩ v' w' → w' < w →
            ∀ D D' : ℤ, Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D →
              Q.IsDifficulty ⟨⟨i + 1, none⟩, hi.trans (Nat.le_succ i)⟩ D' → D' < D) ∧
    (∀ (μ : Q.FlipMove)
        (v : Valuation (Q.chain.model μ.source.1).functionField (WithZero (Multiplicative ℤ)))
        (v' : Valuation (Q.chain.model μ.target.1).functionField (WithZero (Multiplicative ℤ))),
        v'.comap (functionFieldMap μ.targetMap) = v.comap (functionFieldMap μ.sourceMap) →
        ∀ w w' : ℕ, Q.chain.IsValuationWeight Q.scale μ.source.1 v w →
          Q.chain.IsValuationWeight Q.scale μ.target.1 v' w' → w' < w →
          ∀ D D' : ℤ, Q.IsDifficulty μ.source D → Q.IsDifficulty μ.target D' → D' < D) :=
  open Proof_prop_oai4_difficulty_iii in
  ⟨difficulty_lt_of_coefficientMove_of_pos Q, difficulty_lt_of_coefficientMove_of_eq_zero Q,
    difficulty_lt_of_flipMove Q⟩

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain
