module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainBracket
public import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.FourfoldDefs
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.CoefficientDecrease
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.SmallTerminalFlipBadSetFinite
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.SmallTerminalFlipDifference
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.MoveWeight
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres

/-!
# Monotonicity of the difficulty along a move of a bridge

Let `(Y, Θ) ⤏ (Y', Θ')` be a move of a bridge of a prepared chain of fourfolds: either the
coefficient decrease `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` of the `i`-th bridge, or one of its small
terminal flips. Then the difficulty does not increase: `𝒟(Y', Θ') ≤ 𝒟(Y, Θ)`.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.difficulty_le_of_eq_next`: the difficulty
  does not increase along any move of a bridge of a prepared chain.

## Implementation notes

* The moves of the bridges of a prepared chain are exactly the steps `x ⤏ y` from a model `x`
  of the prepared chain to the next model `y = next x`
  (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.next`): from the junction `⟨i, none⟩` the
  coefficient decrease, ending at the decreased pair `⟨i, some 0⟩`, or at the junction
  `⟨i + 1, none⟩` when the bridge has no flip; from `⟨i, some k⟩` the `k`-th small terminal flip
  (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.isCoefficientDecrease_or_isFlipMove`).
  The statement quantifies over all such steps at once.
* Difficulties (`MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.IsDifficulty`) are
  predicates on their values; the inequality is stated for all values satisfying them.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Proof_prop_oai4_difficulty_ii

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Fourfold MMP.Fourfold.StabilizedSmallKltTail MMP.Mori
open TerminalChain (IsIncarnation)

/-! ### Function field maps -/

private theorem comap_functionFieldMap_comp {A B C : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] {c : A ⟶ C}
    [IsDominant c] (hc : a ≫ b = c) (v : Valuation A.functionField (WithZero (Multiplicative ℤ))) :
    v.comap (functionFieldMap c) = (v.comap (functionFieldMap a)).comap (functionFieldMap b) := by
  subst hc
  exact Valuation.ext fun t =>
    congrArg v (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply a b t).symm

private theorem comap_functionFieldMap_id {A : Scheme.{0}} [IsIntegral A]
    (v : Valuation A.functionField (WithZero (Multiplicative ℤ))) :
    v.comap (functionFieldMap (𝟙 A)) = v :=
  Valuation.ext fun t => congrArg v (MMP.Mori.functionFieldMap_id_apply t)

/-- Along a bijective ring map every valuation is a pull-back. -/
private theorem exists_comap_eq {K L : Type*} [Field K] [Field L] {e : K →+* L}
    (he : Function.Bijective e) (u : Valuation K (WithZero (Multiplicative ℤ))) :
    ∃ u' : Valuation L (WithZero (Multiplicative ℤ)), u'.comap e = u := by
  refine ⟨u.comap (RingEquiv.ofBijective e he).symm.toRingHom, Valuation.ext fun t => ?_⟩
  rw [Valuation.comap_apply, Valuation.comap_apply]
  congr 1
  exact (RingEquiv.ofBijective e he).symm_apply_apply t

/-! ### Exceptional valuations along an isomorphism -/

private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{0}}
    {f : X ⟶ Y} (hf : IsBirationalMorphism f) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsOpenImmersion (U.ι ≫ f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  refine ⟨W, hW, ?_⟩
  have : W.ι ≫ f = X.homOfLE hWf ≫ f.toPartialMap.hom := by
    change W.ι ≫ f = (X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom) ≫ f
    simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
  rw [this, ← h]
  infer_instance

/-- A normalized divisorial valuation exceptional over `X` stays exceptional over `Y` under an
isomorphism `X ≅ Y` over `ℂ`. -/
private theorem isExceptionalValuation_comap_of_iso {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} (φ : X ≅ Y)
    (hφ : φ.hom ≫ sY = sX) {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (hv : MMP.Intersection.IsExceptionalValuation ℂ sX v) :
    MMP.Intersection.IsExceptionalValuation ℂ sY (v.comap (functionFieldMap φ.hom)) := by
  obtain ⟨D, hp, rfl, hc⟩ := hv
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hbir : IsBirationalMorphism (D.f ≫ φ.hom) := by
    obtain ⟨U, hU, hUi⟩ := exists_isOpenImmersion_of_isBirationalMorphism D.isBirationalMorphism
    haveI : IsOpenImmersion (U.ι ≫ D.f ≫ φ.hom) := by
      rw [← Category.assoc]; infer_instance
    obtain ⟨x₀⟩ := (IrreducibleSpace.isIrreducible_univ D.Y).nonempty
    haveI : Nonempty D.Y := ⟨x₀⟩
    exact MMP.Spreading.isBirationalMorphism_of_isOpenImmersion_ι_comp' _ U hU.nonempty
  let D' : DivisorOver ℂ sY :=
    { Y := D.Y
      f := D.f ≫ φ.hom
      isNormalVariety := by rw [Category.assoc, hφ]; exact D.isNormalVariety
      isBirationalMorphism := hbir
      E := D.E }
  refine ⟨D', inferInstanceAs (IsProper (D.f ≫ φ.hom)), ?_, ?_⟩
  · change (D.E.valuationOver D.f).comap (functionFieldMap φ.hom) =
      D.E.valuationOver (D.f ≫ φ.hom)
    unfold PrimeDivisor.valuationOver
    exact (comap_functionFieldMap_comp D.f φ.hom rfl _).symm
  · rw [MMP.Positivity.DivisorOver.codimension_center] at hc ⊢
    change 2 ≤ Order.coheight ((D.f ≫ φ.hom) D.E.genericPoint)
    rw [Scheme.Hom.comp_apply, coheight_eq_of_isOpenImmersion φ.hom]
    exact hc

/-! ### Incarnations of valuations of `k(X_0)` -/

variable {T : StabilizedSmallKltTail}

/-- Every valuation of `k(X_i)` corresponds to a valuation of `k(X_0)`. -/
private theorem exists_corresponds :
    ∀ (i : ℕ) (η : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))),
      ∃ ξ, T.Corresponds i ξ η
  | 0, η => ⟨η, rfl⟩
  | i + 1, η => by
    haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
    haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_plus.isDominant
    obtain ⟨ζ, hζ⟩ := exists_comap_eq
      (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.functionFieldMap_bijective
      (η.comap (functionFieldMap (T.fp i)))
    obtain ⟨ξ, hξ⟩ := exists_corresponds i ζ
    exact ⟨ξ, ζ, hξ, hζ.symm⟩

variable (C : TerminalChain T)

/-- The morphism `h_k : T_k ⟶ Z_i` from the base of a flip of a bridge is dominant when
`π_k = h_k ∘ g_k` is. -/
private theorem isDominant_h {i k : ℕ} (hk : k < (C.bridge i).P.m)
    (h : IsDominant ((C.bridge i).P.toBase k)) : IsDominant ((C.bridge i).P.h k) := by
  haveI : IsDominant ((C.bridge i).P.g k ≫ (C.bridge i).P.h k) := by
    rw [← (C.bridge i).P.modelMap_eq k hk]; exact h
  exact IsDominant.of_comp ((C.bridge i).P.g k) _

/-- The morphisms `π_k : V_k ⟶ Z_i` of a bridge are dominant. -/
private theorem isDominant_toBase (i : ℕ) :
    ∀ k ≤ (C.bridge i).P.m, IsDominant ((C.bridge i).P.toBase k)
  | 0, _ => by
    haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
    haveI := (C.junction i).isBirationalMorphism.isDominant
    change IsDominant ((C.junction i).p ≫ T.f i)
    infer_instance
  | k + 1, hk => by
    haveI := isDominant_toBase i k (Nat.le_of_succ_le hk)
    have hS := (C.bridge i).P.isFourfoldStepDiagram k hk
    haveI : IsDominant ((C.bridge i).P.gp k) := hS.isBirationalMorphism_plus.isDominant
    haveI := isDominant_h C hk (isDominant_toBase i k (Nat.le_of_succ_le hk))
    change IsDominant ((C.bridge i).P.πY k)
    rw [(C.bridge i).P.πY_eq k hk]
    infer_instance

/-- Every valuation of the function field of a model is the incarnation of a valuation of
`k(X_0)`. -/
private theorem exists_isIncarnation :
    ∀ (x : C.ModelIndex) (v : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ))),
      ∃ ξ, IsIncarnation C ξ x v
  | ⟨i, none⟩, v => by
    haveI := (C.junction i).isBirationalMorphism.isDominant
    obtain ⟨ξ, hξ⟩ := exists_corresponds i
      ((v : Valuation (C.junction i).Y.functionField (WithZero (Multiplicative ℤ))).comap
        (functionFieldMap (C.junction i).p))
    exact ⟨ξ, _, hξ, rfl⟩
  | ⟨i, some k⟩, v => by
    haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
    haveI := isDominant_toBase C i k k.2.le
    obtain ⟨w, hw⟩ := exists_comap_eq
      (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.functionFieldMap_bijective
      ((v : Valuation ((C.bridge i).P.model k).functionField
        (WithZero (Multiplicative ℤ))).comap (functionFieldMap ((C.bridge i).P.toBase k)))
    obtain ⟨ξ, hξ⟩ := exists_corresponds i w
    exact ⟨ξ, w, hξ, inferInstance, hw.symm⟩

/-- Every model `V_j` of the `i`-th bridge is reached from the junction `Y_i`. -/
private theorem exists_modelIndexSeq_eq_some {i n : ℕ} (hn : C.modelIndexSeq n = ⟨i, none⟩) :
    ∀ (j : ℕ) (hj : j < (C.bridge i).P.m), ∃ n', C.modelIndexSeq n' = ⟨i, some ⟨j, hj⟩⟩
  | 0, hj => ⟨n + 1, by
      rw [C.modelIndexSeq_succ, hn]; simp only [TerminalChain.next, hj, ↓reduceDIte]⟩
  | j + 1, hj => by
    obtain ⟨n', hn'⟩ := exists_modelIndexSeq_eq_some hn j (by omega)
    exact ⟨n' + 1, by
        rw [C.modelIndexSeq_succ, hn']; simp only [TerminalChain.next, hj, ↓reduceDIte]⟩

/-- Every junction `Y_i` is one of the models of the chain. -/
private theorem exists_modelIndexSeq_eq_none :
    ∀ i : ℕ, ∃ n, C.modelIndexSeq n = ⟨i, none⟩
  | 0 => ⟨0, rfl⟩
  | i + 1 => by
    obtain ⟨n, hn⟩ := exists_modelIndexSeq_eq_none i
    by_cases h : 0 < (C.bridge i).P.m
    · obtain ⟨n', hn'⟩ := exists_modelIndexSeq_eq_some C hn ((C.bridge i).P.m - 1) (by omega)
      have h' : ¬ (C.bridge i).P.m - 1 + 1 < (C.bridge i).P.m := by omega
      exact ⟨n' + 1, by
          rw [C.modelIndexSeq_succ, hn']; simp only [TerminalChain.next, h', ↓reduceDIte]⟩
    · exact ⟨n + 1, by
        rw [C.modelIndexSeq_succ, hn]; simp only [TerminalChain.next, h, ↓reduceDIte]⟩

/-- Every model of the chain is one of its models in order. -/
private theorem exists_modelIndexSeq_eq : ∀ x : C.ModelIndex, ∃ n, C.modelIndexSeq n = x
  | ⟨i, none⟩ => exists_modelIndexSeq_eq_none C i
  | ⟨i, some k⟩ => by
    obtain ⟨n, hn⟩ := exists_modelIndexSeq_eq_none C i
    exact exists_modelIndexSeq_eq_some C hn k.1 k.2

/-- Every model of a terminal chain is a pair with any boundary: it is `ℚ`-factorial and has a
canonical divisor. -/
private theorem isPair_model (x : C.ModelIndex) (Δ : MMP.Mori.QDivisor (C.model x)) :
    MMP.Mori.IsPair (C.modelStructure x) Δ := by
  rcases x with ⟨i, _ | k⟩
  · have hQ : IsQFactorial (C.junction i).sY := (C.junction i).isQFactorial
    obtain ⟨n, hK⟩ := (C.bridge i).P.isCanonicalDivisor
    exact ⟨hQ.1, n, _, hK, isQCartier_of_isQFactorial _ hQ _⟩
  · have hQ := (C.bridge i).P.isQFactorial k k.2.le
    obtain ⟨n, hK⟩ := ((C.bridge i).P.isFourfoldStepDiagram k k.2).isCanonicalDivisor
    exact ⟨hQ.1, n, _, hK, isQCartier_of_isQFactorial _ hQ _⟩

/-- Every valuation exceptional over a model has a weight there. -/
private theorem exists_isValuationWeight (N : ℕ) (x : C.ModelIndex)
    {v : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ))}
    (hv : MMP.Intersection.IsExceptionalValuation ℂ (C.modelStructure x) v) :
    ∃ w, C.IsValuationWeight N x v w := by
  have hP := isPair_model C x (C.modelBoundary x)
  obtain ⟨D, hp, rfl, -⟩ := id hv
  obtain ⟨-, n, K, hK, -⟩ := id hP
  obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  exact ⟨_, hv, 1 + (b : ℝ), ⟨n, D, hp, rfl,
    MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hb hp⟩, rfl⟩

/-- An incarnation on the junction `Y_i` restricts on `k(Z_i)`, through `π_0 : V_0 = Y_i ⟶ Z_i`,
to the valuation of `k(X_i)` corresponding to `ξ`. -/
private theorem exists_comap_toBase_zero {i : ℕ}
    {ξ : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
    {v : Valuation (C.junction i).Y.functionField (WithZero (Multiplicative ℤ))}
    [IsDominant ((C.bridge i).P.toBase 0)] (hv : IsIncarnation C ξ ⟨i, none⟩ v) :
    haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
    ∃ w, T.Corresponds i ξ w ∧
      v.comap (functionFieldMap ((C.bridge i).P.toBase 0))
        = w.comap (functionFieldMap (T.f i)) := by
  haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := (C.junction i).isBirationalMorphism.isDominant
  obtain ⟨w, hw, hvw⟩ := hv
  exact ⟨w, hw, (comap_functionFieldMap_comp (C.junction i).p (T.f i) rfl v).trans (hvw ▸ rfl)⟩

/-- A valuation of `k(Y_{i+1})` whose restriction to `k(Z_i)`, through `Y_{i+1} ⟶ X_{i+1} ⟶ Z_i`,
is that of the valuation of `k(X_i)` corresponding to `ξ` is an incarnation of `ξ`. -/
private theorem isIncarnation_succ_none {i : ℕ}
    {ξ : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
    {w : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))} (hw : T.Corresponds i ξ w)
    (v : Valuation (C.junction (i + 1)).Y.functionField (WithZero (Multiplicative ℤ))) :
    haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
    haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_plus.isDominant
    haveI := (C.junction (i + 1)).isBirationalMorphism.isDominant
    v.comap (functionFieldMap ((C.junction (i + 1)).p ≫ T.fp i)) =
      w.comap (functionFieldMap (T.f i)) → IsIncarnation C ξ ⟨i + 1, none⟩ v := by
  haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_plus.isDominant
  haveI := (C.junction (i + 1)).isBirationalMorphism.isDominant
  exact fun h => ⟨_, ⟨w, hw, (comap_functionFieldMap_comp _ _ rfl v).symm.trans h⟩, rfl⟩

/-- Along the coefficient decrease `e : Y_i ≅ Y_{i+1}` of a bridge without flips, incarnations
stay incarnations. -/
private theorem isIncarnation_end_zero {i : ℕ}
    (e : (C.bridge i).P.model 0 ≅ (C.junction (i + 1)).Y)
    (hπ : (C.bridge i).P.toBase 0 = e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i)
    {ξ : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
    {v : Valuation (C.junction i).Y.functionField (WithZero (Multiplicative ℤ))}
    (hv : IsIncarnation C ξ ⟨i, none⟩ v) :
    IsIncarnation C ξ ⟨i + 1, none⟩ (v.comap (functionFieldMap e.hom)) := by
  haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_plus.isDominant
  haveI := (C.junction (i + 1)).isBirationalMorphism.isDominant
  haveI := isDominant_toBase C i 0 (Nat.zero_le _)
  obtain ⟨w, hw, hvw⟩ := exists_comap_toBase_zero C hv
  exact isIncarnation_succ_none C hw _
    ((comap_functionFieldMap_comp _ _ hπ.symm v).symm.trans hvw)

private theorem eqToHom_comp_toBase (i k : ℕ) :
    ∀ (m : ℕ) (hm : m = k + 1),
      eqToHom (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hm) ≫
        (C.bridge i).P.toBase (k + 1) = (C.bridge i).P.toBase m := by
  rintro _ rfl
  simp

/-- Over the base of a flip of a bridge, incarnations stay incarnations (both cases of the
decision of `k + 1 < m_i`). -/
private theorem isIncarnation_flipTargetOf (i : ℕ) (k : Fin (C.bridge i).P.m)
    (d : Decidable (k.1 + 1 < (C.bridge i).P.m))
    (ξ : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ)))
    (v : Valuation ((C.bridge i).P.model k).functionField (WithZero (Multiplicative ℤ)))
    (v' : Valuation (C.model (C.flipTargetOf i k d)).functionField (WithZero (Multiplicative ℤ)))
    (hv : IsIncarnation C ξ ⟨i, some k⟩ v)
    (hc : haveI := C.isIntegral_flipBase i k
      haveI := C.isDominant_flipTargetMapOf i k d
      haveI := C.isDominant_flipSourceMap i k
      v'.comap (functionFieldMap (C.flipTargetMapOf i k d)) =
        v.comap (functionFieldMap ((C.bridge i).P.g k))) :
    IsIncarnation C ξ (C.flipTargetOf i k d) v' := by
  haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_plus.isDominant
  haveI := C.isIntegral_flipBase i k
  haveI := C.isDominant_flipSourceMap i k
  haveI := C.isDominant_flipTargetMapOf i k d
  haveI := isDominant_toBase C i k k.2.le
  have hS := (C.bridge i).P.isFourfoldStepDiagram k k.2
  haveI : IsDominant ((C.bridge i).P.gp k) := hS.isBirationalMorphism_plus.isDominant
  have hgh : (C.bridge i).P.g k ≫ (C.bridge i).P.h k = (C.bridge i).P.toBase k :=
    ((C.bridge i).P.modelMap_eq k k.2).symm
  have hgph : (C.bridge i).P.gp k ≫ (C.bridge i).P.h k = (C.bridge i).P.toBase (k + 1) :=
    ((C.bridge i).P.πY_eq k k.2).symm
  haveI := isDominant_h C k.2 inferInstance
  obtain ⟨w, hw, _, hvw⟩ := hv
  have hg : (v.comap (functionFieldMap ((C.bridge i).P.g k))).comap
      (functionFieldMap ((C.bridge i).P.h k)) = w.comap (functionFieldMap (T.f i)) := by
    rw [← comap_functionFieldMap_comp _ _ hgh, hvw]
  cases d with
  | isTrue h =>
    change Valuation ((C.bridge i).P.Y k).functionField (WithZero (Multiplicative ℤ)) at v'
    have hc' : v'.comap (functionFieldMap ((C.bridge i).P.gp k)) =
        v.comap (functionFieldMap ((C.bridge i).P.g k)) := hc
    haveI : IsDominant ((C.bridge i).P.πY k) := isDominant_toBase C i (k + 1) h.le
    refine ⟨w, hw, isDominant_toBase C i (k + 1) h.le, ?_⟩
    exact (congrArg (Valuation.comap · v')
      (MMP.Positivity.DivisorOver.functionFieldMap_congr ((C.bridge i).P.πY_eq k k.2))).trans
      ((comap_functionFieldMap_comp _ _ rfl v').trans (by rw [hc', hg]))
  | isFalse h =>
    have hm : (C.bridge i).P.m = k.1 + 1 := by omega
    let ψ : (C.junction (i + 1)).Y ⟶ (C.bridge i).P.T k := (C.bridge i).e.inv ≫
      eqToHom (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hm) ≫ (C.bridge i).P.gp k
    haveI : IsDominant ψ := C.isDominant_flipTargetMapOf i k (isFalse h)
    change Valuation (C.junction (i + 1)).Y.functionField (WithZero (Multiplicative ℤ)) at v'
    have hc' : v'.comap (functionFieldMap ψ) =
        v.comap (functionFieldMap ((C.bridge i).P.g k)) := hc
    have hψ : ψ ≫ (C.bridge i).P.h k = (C.junction (i + 1)).p ≫ T.fp i := by
      have e1 := (congrArg (eqToHom (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hm) ≫ ·)
        hgph).trans (eqToHom_comp_toBase C i k.1 _ hm)
      refine ((Category.assoc _ _ _).trans
        (congrArg ((C.bridge i).e.inv ≫ ·) ((Category.assoc _ _ _).trans e1))).trans ?_
      rw [(C.bridge i).toBase_end_eq, Iso.inv_hom_id_assoc]
    haveI := (C.junction (i + 1)).isBirationalMorphism.isDominant
    refine isIncarnation_succ_none C hw v' ?_
    rw [comap_functionFieldMap_comp _ _ hψ, hc', hg]

/-- The model following `V_k` is the target of the `k`-th flip. -/
private theorem next_eq_flipTarget (i : ℕ) (k : Fin (C.bridge i).P.m) :
    C.next ⟨i, some k⟩ = C.flipTarget i k := by
  by_cases h : k.1 + 1 < (C.bridge i).P.m
  · rw [C.flipTarget_of_lt h]; simp only [TerminalChain.next, h, ↓reduceDIte]
  · rw [C.flipTarget_of_not_lt h]; simp only [TerminalChain.next, h, ↓reduceDIte]

variable (Q : PreparedChain T)

/-- Weights do not increase from a model of the prepared chain to the next one, for a valuation
incarnated on both. -/
private theorem le_of_isValuationWeight_next {x y : Q.chain.ModelIndex} (hy : Q.chain.next x = y)
    (ξ : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ)))
    (v : Valuation (Q.chain.model x).functionField (WithZero (Multiplicative ℤ)))
    (v' : Valuation (Q.chain.model y).functionField (WithZero (Multiplicative ℤ)))
    (hv : IsIncarnation Q.chain ξ x v) (hv' : IsIncarnation Q.chain ξ y v') {w w' : ℕ}
    (hw : Q.chain.IsValuationWeight Q.scale x v w)
    (hw' : Q.chain.IsValuationWeight Q.scale y v' w') : w' ≤ w := by
  obtain ⟨n, rfl⟩ := exists_modelIndexSeq_eq Q.chain x
  rw [← Q.chain.modelIndexSeq_succ] at hy
  subst hy
  exact PreparedChain.le_of_isValuationWeight_succ Q n ξ v v' hv hv' hw hw'

/-- **A coefficient decrease.** The difference of the difficulties is a finite sum of weight
differences, each nonnegative. -/
private theorem difficulty_le_of_coefficientDecrease {i : ℕ} (hi : Q.start ≤ i)
    {y : Q.chain.ModelIndex} (hyeq : Q.chain.next ⟨i, none⟩ = y)
    (hy : Q.start ≤ (Q.chain.next ⟨i, none⟩).1)
    (φ : Q.chain.model ⟨i, none⟩ ≅ Q.chain.model y)
    (hφ : φ.hom ≫ Q.chain.modelStructure y = Q.chain.modelStructure ⟨i, none⟩)
    (hΘ : (Q.chain.bridge i).Θ' = inverseTransformDivisor φ.hom (Q.chain.modelBoundary y))
    (hinc : ∀ ξ v, IsIncarnation Q.chain ξ ⟨i, none⟩ v →
      IsIncarnation Q.chain ξ y (v.comap (functionFieldMap φ.hom)))
    {D D' : ℤ} (hD : Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D)
    (hD' : Q.IsDifficulty ⟨Q.chain.next ⟨i, none⟩, hy⟩ D') : D' ≤ D := by
  subst hyeq
  obtain ⟨F, hF, -, hsum⟩ := Q.exists_finset_difficulty_sub_eq_sum hi φ hφ hΘ hy
  have hex : ∀ v ∈ F, ∃ n, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v n :=
    fun v hv => exists_isValuationWeight Q.chain Q.scale _ (hF v hv)
  have hex' : ∀ v ∈ F, ∃ n, Q.chain.IsValuationWeight Q.scale (Q.chain.next ⟨i, none⟩)
      (v.comap (functionFieldMap φ.hom)) n :=
    fun v hv => exists_isValuationWeight Q.chain Q.scale _
      (isExceptionalValuation_comap_of_iso φ hφ (hF v hv))
  choose! w hw using hex
  choose! w' hw' using hex'
  have h := hsum D D' hD hD' w w' hw hw'
  have hle : ∀ v ∈ F, ((w' v : ℕ) : ℤ) ≤ w v := fun v hv => by
    obtain ⟨ξ, hξ⟩ := exists_isIncarnation Q.chain ⟨i, none⟩ v
    exact_mod_cast le_of_isValuationWeight_next Q rfl ξ v _ hξ (hinc ξ v hξ) (hw v hv)
      (hw' v hv)
  have h0 : 0 ≤ ∑ v ∈ F, ((w v : ℤ) - w' v) :=
    Finset.sum_nonneg fun v hv => sub_nonneg.2 (hle v hv)
  linarith

/-- **A small terminal flip.** The difference of the difficulties is a sum over the weighted bad
set of weight differences, each nonnegative. -/
private theorem difficulty_le_of_flipMove (μ : Q.FlipMove) {D D' : ℤ}
    (hD : Q.IsDifficulty μ.source D) (hD' : Q.IsDifficulty μ.target D') : D' ≤ D := by
  classical
  haveI : Nonempty (Valuation (Q.chain.model μ.target.1).functionField
      (WithZero (Multiplicative ℤ))) := ⟨1⟩
  have H : ∀ v ∈ Q.flipBadSet μ, ∃ (v' : Valuation (Q.chain.model μ.target.1).functionField
      (WithZero (Multiplicative ℤ))) (n n' : ℕ),
      v'.comap (functionFieldMap μ.targetMap) = v.comap (functionFieldMap μ.sourceMap) ∧
        Q.chain.IsValuationWeight Q.scale μ.source.1 v n ∧
        Q.chain.IsValuationWeight Q.scale μ.target.1 v' n' := by
    rintro v ⟨-, v', hv', n, n', hn, hn', -⟩
    exact ⟨v', n, n', hv', hn, hn'⟩
  choose! v' w w' hc hw hw' using H
  have hsum := Q.difficulty_sub_eq_finsum_flipBadSet μ D D' hD hD' w w' hw
    (fun v hv => ⟨v' v, hc v hv, hw' v hv⟩)
  have h0 : 0 ≤ ∑ᶠ v ∈ Q.flipBadSet μ, ((w v : ℤ) - w' v) := by
    refine finsum_nonneg fun v => finsum_nonneg fun hv => ?_
    obtain ⟨ξ, hξ⟩ := exists_isIncarnation Q.chain μ.source.1 v
    have hinc : IsIncarnation Q.chain ξ μ.target.1 (v' v) :=
      isIncarnation_flipTargetOf Q.chain μ.1.1 μ.1.2 inferInstance ξ v (v' v) hξ (hc v hv)
    have := le_of_isValuationWeight_next Q (next_eq_flipTarget Q.chain μ.1.1 μ.1.2) ξ v (v' v)
      hξ hinc (hw v hv) (hw' v hv)
    exact sub_nonneg.2 (by exact_mod_cast this)
  linarith

end Proof_prop_oai4_difficulty_ii

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

variable {T : StabilizedSmallKltTail} (Q : PreparedChain T)

open MMP.Mori Proof_prop_oai4_difficulty_ii in
/-- On a prepared chain, the difficulty does not increase along a move of a bridge: if `y` is
the model following the model `x` (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.next`),
so that `x ⤏ y` is a coefficient decrease or a small terminal flip, and `D = 𝒟(x)`,
`D' = 𝒟(y)`, then `D' ≤ D`. -/
@[mmp "prop_oai4_difficulty_ii"]
public theorem difficulty_le_of_eq_next {x y : Q.ModelIndex} (hy : y.1 = Q.chain.next x.1)
    {D D' : ℤ} (hD : Q.IsDifficulty x D) (hD' : Q.IsDifficulty y D') : D' ≤ D := by
  obtain ⟨⟨i, _ | k⟩, hs⟩ := x
  · obtain ⟨y, hy1⟩ := y
    dsimp only at hy
    subst hy
    by_cases h : 0 < (Q.chain.bridge i).P.m
    · have hx : Q.chain.next ⟨i, none⟩ = ⟨i, some ⟨0, h⟩⟩ := by
        simp only [TerminalChain.next, h, ↓reduceDIte]
      refine difficulty_le_of_coefficientDecrease Q hs hx hy1
        (Iso.refl (Q.chain.model ⟨i, none⟩)) (Category.id_comp _)
        (inverseTransformDivisor_id _).symm (fun ξ v hv => ?_) hD hD'
      haveI := isDominant_toBase Q.chain i 0 (Nat.zero_le _)
      obtain ⟨w, hw, hvw⟩ := exists_comap_toBase_zero Q.chain hv
      exact ⟨w, hw, inferInstance, (comap_functionFieldMap_id v).symm ▸ hvw⟩
    · have hx : Q.chain.next ⟨i, none⟩ = ⟨i + 1, none⟩ := by
        simp only [TerminalChain.next, h, ↓reduceDIte]
      have key : ∀ (m : ℕ) (e : (Q.chain.bridge i).P.model m ≅ (Q.chain.junction (i + 1)).Y),
          e.hom ≫ (Q.chain.junction (i + 1)).sY = (Q.chain.bridge i).P.modelStructure m →
          (Q.chain.bridge i).P.boundary m =
            MMP.Mori.inverseTransformDivisor e.hom (Q.chain.junction (i + 1)).Θ →
          (Q.chain.bridge i).P.toBase m = e.hom ≫ (Q.chain.junction (i + 1)).p ≫ T.fp i →
          m = 0 → D' ≤ D := by
        rintro m e he hΘ hπ rfl
        refine difficulty_le_of_coefficientDecrease Q hs hx hy1 e he hΘ
          (fun ξ v hv => isIncarnation_end_zero Q.chain e hπ hv) hD hD'
      exact key _ (Q.chain.bridge i).e (Q.chain.bridge i).comp_sY
        (Q.chain.bridge i).endBoundary_eq (Q.chain.bridge i).toBase_end_eq (by omega)
  · obtain ⟨y, hy1⟩ := y
    dsimp only at hy
    subst hy
    let μ : Q.FlipMove := ⟨⟨i, k⟩, hs⟩
    revert hy1 hD'
    rw [next_eq_flipTarget Q.chain i k]
    intro hy1 hD'
    exact difficulty_le_of_flipMove Q μ hD hD'

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain
