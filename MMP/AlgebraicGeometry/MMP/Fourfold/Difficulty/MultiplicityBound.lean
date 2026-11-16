module

public import Mathlib.Algebra.BigOperators.Finprod
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldPreparedChain
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupEmbedded
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.EchoSetting
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoLogDiscrepancy
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank

/-!
# The multiplicity bound at a curve on a model of a prepared chain

Let `(Y, Θ)` be a model of a prepared chain, with labels `S_h` of coefficients `b_h`, and let
`C ⊆ Y` be an irreducible closed curve with generic point `η_C`. Write `m_h` for the
multiplicity of `S_h` at `η_C`, the order of the ideal of `S_h` in the local ring `𝒪_{Y,η_C}`;
it is `0` when `C ⊄ S_h`. Then `∑_h m_h b_h < 1`.

The proof computes the log discrepancy of the order valuation of the two-dimensional regular
local ring `𝒪_{Y,η_C}`, which is `2 - ∑_h m_h b_h`, and compares it with terminality.

## Main results

* `MMP.Fourfold.StabilizedTail.PreparedChain.sum_mul_labelCoefficient_lt_one`: the statement
  above.

## Implementation notes

* The model is `x : MMP.Fourfold.StabilizedTail.PreparedChain.ModelIndex`, and the curve is a
  proper curve `MMP.Mori.ProperCurve` of it, recorded by its generic point, as in
  `MMP.Fourfold.StabilizedTail.PreparedChain.IsCurveBracket`.
* The multiplicity of the label `S_h` at `η_C` is `MMP.Resolution.multAt` of the ideal sheaf of
  the centre of `S_h` on the model (`MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelCentre`)
  at `η_C`, which is `0` exactly when `η_C ∉ S_h`. When the centre of `S_h` on the model is not a
  prime divisor, `m_h` is `0`, matching the corresponding branch of the coefficient predicate.
  The coefficients are those of `MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelCoefficient`.
  Both are predicates on their values, so the statement takes chosen values `m_h`, `b_h`
  characterised by them.
* The labels are finitely many (`MMP.Fourfold.StabilizedTail.TerminalChain.finite_label`), so the
  finitely supported sum `∑ᶠ` is the finite sum.
-/

@[expose] public section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
open MMP.Mori MMP.Fourfold MMP.Fourfold.StabilizedTail
open scoped WithZero

namespace MMP.MultiplicityBound

universe u

/-! ### Uniqueness of the centre of a label -/

/-- Valuations agreeing after composition with a surjective ring map agree. -/
private theorem valuation_eq_of_comap_eq {K L Γ : Type*} [Ring K] [Ring L]
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
    have hb := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism
    haveI := hb.isDominant
    exact valuation_eq_of_comap_eq
      hb.functionFieldMap_bijective.2 ((show _ = _ from h).trans (show _ = _ from h').symm)

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

/-! ### The order valuation at a curve -/

/-- The map `WithTop ℤ → ℤᵐ⁰` sending `⊤` to `0` and `n` to `exp (-n)`. -/
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
  rw [isRegularSystemOfParameters_iff, Matrix.range_cons, Matrix.range_cons,
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
  have h' : (1 + c : ℕ∞) = 3 := WithBot.coe_injective (by rw [WithBot.coe_add]; exact h)
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
  haveI := hreg
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

/-- A divisor over a normal variety whose centre has codimension at least two is exceptional. -/
private theorem isExceptional_of_two_le_codimension_center {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) (h : 2 ≤ codimension D.center) :
    D.IsExceptional := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI : IsSeparated sX := hX.1.toIsSeparated
  have hsep : IsSeparated (X ↘ ⊤_ Scheme) := by
    have : (X ↘ ⊤_ Scheme) = sX ≫ Limits.terminal.from (Spec (.of k)) := Subsingleton.elim _ _
    rw [this]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hc : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := by
    refine Closeds.ext ?_
    rw [Closeds.coe_closure]
    exact D.coe_center.symm
  rw [hc]
  change 2 ≤ closedsCodimension (T := X) ⟨(D.center : Set X), D.center.isClosed⟩
  rw [closedsCodimension_coe]
  exact h

/-! ### The bound -/

/-- **The terminality bound.** At the generic point `η_C` of a proper curve on a model `(Y, Θ)`
of a prepared chain, `mult_{η_C} Θ < 1`. -/
private theorem multiplicityAt_modelBoundary_lt_one {T : StabilizedTail} (Q : PreparedChain T)
    (x : Q.ModelIndex) (γ : ProperCurve (Q.chain.modelStructure x.1)) :
    DivisorWithCoeffs.multiplicityAt (Q.chain.modelBoundary x.1) γ.point < 1 := by
  obtain ⟨hT, -, -, hdim, -, hreg⟩ := Q.echoSetting_model x
  have hY : IsNormalVariety ℂ (Q.chain.modelStructure x.1) := hT.1.1.isPair.1
  let V : IrreducibleCloseds (Q.chain.model x.1) :=
    ⟨closure {γ.point}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hη : V.isIrreducible.genericPoint = γ.point :=
    (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).eq isGenericPoint_closure
  have hV : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 1 :=
    (MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq γ.point).symm.trans γ.dim_eq
  obtain ⟨v, hv⟩ := exists_isGenericBlowupValuation hY hdim V hV (hreg V hV)
  obtain ⟨-, -, ⟨D', -, hvD', hcod⟩, n, D, hDv, hD⟩ := hv.hasLogDiscrepancy hT.1.1
  have hcen : D.center = D'.center :=
    MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hY.1 (hDv.trans hvD')
  have h1 := hT.2 n D _ (isExceptional_of_two_le_codimension_center hY D (hcen ▸ hcod)) hD
  rw [← hη]
  exact_mod_cast (by linarith : ((DivisorWithCoeffs.multiplicityAt (Q.chain.modelBoundary x.1)
    V.isIrreducible.genericPoint : ℚ) : ℝ) < 1)

/-- The sum `∑_h m_h b_h` over the labels is the multiplicity `mult_{η_C} Θ` of the boundary. -/
private theorem finsum_mul_eq_multiplicityAt {T : StabilizedTail} (Q : PreparedChain T)
    (x : Q.ModelIndex) (γ : ProperCurve (Q.chain.modelStructure x.1))
    (m : Q.chain.Label → ℕ) (b : Q.chain.Label → ℚ)
    (hm : ∀ S, (∃ P : MMP.Mori.PrimeDivisor (Q.chain.model x.1),
      Q.chain.IsLabelCentre S x.1 P ∧ MMP.Resolution.multAt P.idealSheaf γ.point = m S) ∨
      ((∀ P : MMP.Mori.PrimeDivisor (Q.chain.model x.1), ¬ Q.chain.IsLabelCentre S x.1 P) ∧
        m S = 0))
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
    rcases hm S with ⟨P, hP', hPm⟩ | ⟨h, -⟩
    · obtain rfl := isLabelCentre_unique _ hP' (hcentre S)
      have : (c S).multiplicityAt γ.point = m S := by
        rw [← hPm, PrimeDivisor.multiplicityAt, MMP.Resolution.multAt,
          MMP.Resolution.idealOrder, Scheme.IdealSheafData.stalkIdeal_eq_stalk]
      simp only [f, this, ENat.toNat_coe, Θ, hPb]
    · exact absurd (hcentre S) (h _)
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

end MMP.MultiplicityBound

namespace MMP.Fourfold.StabilizedTail.PreparedChain

/-- **Multiplicity bound at a curve.** On a model `(Y, Θ)` of a prepared chain, let `γ` be an
irreducible closed curve of `Y`, `m S` the multiplicity at the generic point of `γ` of the label
`S` (`MMP.Resolution.multAt` of the ideal of the centre of `S` on `Y`; it is `0` if `γ ⊄ S`,
and `0` if the centre of `S` on `Y` is not a prime divisor), and `b S` the coefficient of `S` in
`Θ`. Then `∑_S m S * b S < 1`. -/
@[mmp "lem_mmp_indexd_multiplicity_bound"]
theorem sum_mul_labelCoefficient_lt_one {T : StabilizedTail} (Q : PreparedChain T)
    (x : Q.ModelIndex) (γ : ProperCurve (Q.chain.modelStructure x.1))
    (m : Q.chain.Label → ℕ) (b : Q.chain.Label → ℚ)
    (hm : ∀ S, (∃ P : MMP.Mori.PrimeDivisor (Q.chain.model x.1),
      Q.chain.IsLabelCentre S x.1 P ∧ MMP.Resolution.multAt P.idealSheaf γ.point = m S) ∨
      ((∀ P : MMP.Mori.PrimeDivisor (Q.chain.model x.1), ¬ Q.chain.IsLabelCentre S x.1 P) ∧
        m S = 0))
    (hb : ∀ S, Q.chain.IsLabelCoefficient S x.1 (b S)) :
    ∑ᶠ S, (m S : ℚ) * b S < 1 := by
  rw [MMP.MultiplicityBound.finsum_mul_eq_multiplicityAt Q x γ m b hm hb]
  exact MMP.MultiplicityBound.multiplicityAt_modelBoundary_lt_one Q x γ

end MMP.Fourfold.StabilizedTail.PreparedChain

end
