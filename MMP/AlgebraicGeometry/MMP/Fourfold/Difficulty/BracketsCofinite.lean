module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldPreparedChain
import MMP.AlgebraicGeometry.Singularities.TerminalThreefoldEchoCentres
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.EchoSetting
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.WeightSupportFinite
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoLogDiscrepancy
import MMP.AlgebraicGeometry.Singularities.WeightedMonomialValuation
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleEmbedding
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Normalization.IntegralScheme

/-!
# Brackets vanish at almost every curve of a model of a prepared chain

Let `(Y, Θ)` be a model of a prepared chain. The bracket
`β_C(Y, Θ) = ∑_{c_Y(v) = C} w_v - ∑_h r_{C,h} d_h` vanishes for all but finitely many
irreducible closed curves `C ⊆ Y`. Consequently the sum `∑_C β_C(Y, Θ)` in the difficulty
`MMP.Fourfold.StabilizedTail.PreparedChain.IsDifficulty` is a finitely supported sum: for any
choice of brackets, its support lies in the finite set below.

## Main results

* `MMP.Fourfold.StabilizedTail.PreparedChain.finite_setOf_isCurveBracket_ne_zero`: only
  finitely many curves carry a nonzero bracket.

## Implementation notes

* As in `MMP.Fourfold.StabilizedTail.PreparedChain.IsCurveBracket`, an irreducible closed curve
  of `Y` is recorded as a proper curve `MMP.Mori.ProperCurve` by its generic point, and the
  bracket is a predicate on its value. "`β_C = 0` for all but finitely many `C`" reads: the
  curves admitting some nonzero value `β` of the bracket form a finite set, so that off this set
  every value of the bracket is `0`.
* The difficulty is an integer by construction (`D : ℤ`); its first sum, over valuations centred
  at closed points, is finitely supported by
  `MMP.Fourfold.StabilizedTail.PreparedChain.finite_setOf_isCentre_singleton`, and its last sum
  runs over the finitely many labels (`MMP.Fourfold.StabilizedTail.TerminalChain.finite_label`).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold.StabilizedTail.PreparedChain

section Helpers

open MMP.Fourfold MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Valuations -/

/-- Valuations agreeing after composition with a surjective ring map agree. -/
private theorem valuation_eq_of_comap_eq {K L Γ : Type*} [Ring K] [Ring L]
    [LinearOrderedCommMonoidWithZero Γ] {φ : K →+* L} (hφ : Function.Surjective φ)
    {v w : Valuation L Γ} (h : v.comap φ = w.comap φ) : v = w :=
  Valuation.ext fun x => by
    obtain ⟨y, rfl⟩ := hφ x
    exact congrArg (fun u : Valuation K Γ => u y) h

/-- The log discrepancy of a valuation is unique. -/
private theorem HasLogDiscrepancy.unique {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : MMP.Mori.QDivisor X} {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    {a a' : ℝ} (h : HasLogDiscrepancy sX B v a) (h' : HasLogDiscrepancy sX B v a') : a = a' := by
  obtain ⟨n, D, hv, ha⟩ := h
  obtain ⟨n', D', hv', ha'⟩ := h'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha ha' (hv.trans hv'.symm)

/-- The default weight of a label with coefficient zero vanishes. -/
private theorem defaultWeight_zero (N : ℕ) : defaultWeight N 0 = 0 := by
  rw [defaultWeight]
  refine finsum_eq_zero_of_forall_eq_zero fun j => ?_
  rw [finsum_eq_if]
  split_ifs with hj
  · exact difficultyWeight_of_nonpos (by simpa using hj)
  · rfl

/-! ### Dimension arithmetic -/

/-- In `WithBot ℕ∞`, `d + 1 = n + 1` forces `d = n`. -/
private theorem eq_of_add_one_eq {d : WithBot ℕ∞} {n : ℕ} (h : d + 1 = ((n + 1 : ℕ) : ℕ∞)) :
    d = (n : ℕ∞) :=
  ENat.WithBot.add_one_cancel.mp (by rw [h]; norm_cast)

/-- The coheight form of `eq_of_add_one_eq`: `1 + c = n + 1` in `WithBot ℕ∞` forces `c = n`. -/
private theorem eq_of_one_add_eq {c : ℕ∞} {n : ℕ} (h : (1 : WithBot ℕ∞) + c = ((n + 1 : ℕ) : ℕ∞)) :
    c = n :=
  WithBot.coe_injective (eq_of_add_one_eq (by rwa [add_comm] at h))

/-! ### Centres of labels -/

section LabelCentre

variable {T : StabilizedTail}

/-- The valuation of `k(X_i)` transported from a valuation of `k(X_0)` is unique. -/
private theorem isTransportedValuationFrom_unique : ∀ (i : ℕ)
    {ν : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
    {w w' : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))},
    T.IsTransportedValuationFrom i ν w → T.IsTransportedValuationFrom i ν w' → w = w'
  | 0, _, _, _, h, h' => h.trans h'.symm
  | i + 1, _, _, _, ⟨u, hu, ht⟩, ⟨u', hu', ht'⟩ => by
    obtain rfl := isTransportedValuationFrom_unique i hu hu'
    have hd := T.isThreefoldStepDiagram i
    haveI := hd.isNormalVariety_target.1.toIsIntegral
    have hb := hd.isSmallMorphism_plus.isBirationalMorphism
    haveI := hb.isDominant
    exact valuation_eq_of_comap_eq hb.functionFieldMap_bijective.2 (ht.trans ht'.symm)

/-- A prime divisor of a normal variety is determined by its valuation of `k(B)`, for a dominant
morphism `f : Y ⟶ B` inducing a surjection of function fields. -/
private theorem primeDivisor_eq_of_valuationOver_eq {Y B : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral B] {sY : Y ⟶ Spec (.of ℂ)}
    (hY : MMP.Mori.IsNormalVariety ℂ sY) (f : Y ⟶ B) [IsDominant f]
    (hf : Function.Surjective (functionFieldMap f)) {P P' : MMP.Mori.PrimeDivisor Y}
    (h : P.valuationOver f = P'.valuationOver f) : P = P' := by
  have hY' : MMP.Mori.IsNormalVariety ℂ (𝟙 Y ≫ sY) := by rwa [Category.id_comp]
  let D : MMP.Mori.DivisorOver ℂ sY :=
    ⟨Y, 𝟙 Y, hY', MMP.Mori.isBirationalMorphism_of_isIso (𝟙 Y), P⟩
  let D' : MMP.Mori.DivisorOver ℂ sY :=
    ⟨Y, 𝟙 Y, hY', MMP.Mori.isBirationalMorphism_of_isIso (𝟙 Y), P'⟩
  have hD : D.valuation = D'.valuation := by
    change P.divisorialValuation.comap _ = P'.divisorialValuation.comap _
    rw [valuation_eq_of_comap_eq hf h]
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1 hD)

/-- Along the programme of a bridge, every `π_k : V_k ⟶ Z_i` induces a surjection
`k(Z_i) → k(V_k)` of function fields. -/
private theorem surjective_functionFieldMap_modelMap (C : T.TerminalChain) (i : ℕ)
    [IsIntegral (T.Z i)] :
    ∀ k ≤ (C.bridge i).P.m,
      ∀ [IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)],
        Function.Surjective
          (functionFieldMap (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k))
  | 0, _, _ => by
    have hb := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus
    haveI := hb.isDominant
    have hp := (C.junction i).isBirationalMorphism
    haveI := hp.isDominant
    intro z
    obtain ⟨y, rfl⟩ := hp.functionFieldMap_bijective.2 z
    obtain ⟨x, rfl⟩ := hb.functionFieldMap_bijective.2 y
    exact ⟨x, (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply
      (C.junction i).p (T.f i) x).symm⟩
  | k + 1, hk, hdom => by
    have hk' : k < (C.bridge i).P.m := hk
    have hd := (C.bridge i).P.isThreefoldStepDiagram k hk'
    haveI := hd.isNormalVariety_target.1.toIsIntegral
    have hg := hd.isBirationalMorphism_minus
    haveI := hg.isDominant
    have hgp := hd.isSmallMorphism_plus.isBirationalMorphism
    haveI := hgp.isDominant
    have hπ : modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY (k + 1) =
        (C.bridge i).P.gp k ≫ (C.bridge i).P.h k :=
      (C.bridge i).P.πY_eq k hk'
    have hπ' : modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k =
        (C.bridge i).P.g k ≫ (C.bridge i).P.h k :=
      (C.bridge i).P.modelMap_eq k hk'
    haveI hgph : IsDominant ((C.bridge i).P.gp k ≫ (C.bridge i).P.h k) := hπ ▸ hdom
    haveI : IsDominant ((C.bridge i).P.h k) := IsDominant.of_comp ((C.bridge i).P.gp k) _
    haveI : IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k) :=
      hπ' ▸ inferInstance
    have hh : Function.Surjective (functionFieldMap ((C.bridge i).P.h k)) := by
      intro t
      obtain ⟨z, hz⟩ := surjective_functionFieldMap_modelMap C i k hk'.le
        (functionFieldMap ((C.bridge i).P.g k) t)
      refine ⟨z, (functionFieldMap ((C.bridge i).P.g k)).injective ?_⟩
      rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        ← MMP.Positivity.DivisorOver.functionFieldMap_congr hπ', hz]
    intro t
    obtain ⟨y, rfl⟩ := hgp.functionFieldMap_bijective.2 t
    obtain ⟨z, rfl⟩ := hh y
    exact ⟨z, (congrArg (fun φ => φ z)
      (@MMP.Positivity.DivisorOver.functionFieldMap_congr _ _ _ _ _ _ hdom hgph hπ)).trans
      (@MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply _ _ _ _ _ _
        ((C.bridge i).P.gp k) ((C.bridge i).P.h k) hgp.isDominant inferInstance hgph z).symm⟩

/-- The centre of a label on a normal model of a terminal chain is unique. -/
private theorem isLabelCentre_unique (C : T.TerminalChain) (S : C.Label) :
    ∀ (x : C.ModelIndex), MMP.Mori.IsNormalVariety ℂ (C.modelStructure x) →
      ∀ {P P' : MMP.Mori.PrimeDivisor (C.model x)},
        C.IsLabelCentre S x P → C.IsLabelCentre S x P' → P = P'
  | ⟨i, none⟩, hY, P, P', ⟨w, hw, hPw⟩, ⟨w', hw', hPw'⟩ => by
    obtain rfl := isTransportedValuationFrom_unique i hw hw'
    have hb := (C.junction i).isBirationalMorphism
    haveI := hb.isDominant
    exact @primeDivisor_eq_of_valuationOver_eq _ _ _ _ _ _ _ hY (C.junction i).p hb.isDominant
      hb.functionFieldMap_bijective.2 _ _ (hPw.trans hPw'.symm)
  | ⟨i, some k⟩, hY, P, P', ⟨w, hw, hdom, hPw⟩, ⟨w', hw', _, hPw'⟩ => by
    obtain rfl := isTransportedValuationFrom_unique i hw hw'
    haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    exact @primeDivisor_eq_of_valuationOver_eq _ _ _ _ _ _ _ hY _ hdom
      (@surjective_functionFieldMap_modelMap T C i _ k k.2.le hdom) _ _ (hPw.trans hPw'.symm)

end LabelCentre

/-! ### A low-discrepancy valuation along a curve inside a boundary component -/

section MonomialValuation

/-- The order-reversing monoid map `WithTop ℤ → (WithZero (Multiplicative ℤ))`,
`n ↦ exp (-n)`, `⊤ ↦ 0`. -/
private def expNeg : WithTop ℤ → (WithZero (Multiplicative ℤ))
  | ⊤ => 0
  | (n : ℤ) => WithZero.exp (-n)

private theorem expNeg_coe (n : ℤ) : expNeg n = WithZero.exp (-n) := rfl

private theorem expNeg_top : expNeg ⊤ = 0 := rfl

private theorem expNeg_add (a b : WithTop ℤ) : expNeg (a + b) = expNeg a * expNeg b := by
  cases a <;> cases b <;>
    simp [expNeg_top, ← WithTop.coe_add, expNeg_coe, neg_add, WithZero.exp_add, mul_comm]

private theorem expNeg_antitone : Antitone expNeg := by
  intro a b h
  cases b with
  | top => simp [expNeg_top]
  | coe n =>
    cases a with
    | top => simp at h
    | coe m =>
      simp only [expNeg_coe, WithZero.exp_le_exp, neg_le_neg_iff]
      exact_mod_cast h

/-- The multiplicative valuation `z ↦ exp (-V z)` attached to an additive valuation `V`. -/
private def valuationOfAddValuation {R : Type*} [Ring R] (V : AddValuation R (WithTop ℤ)) :
    Valuation R (WithZero (Multiplicative ℤ)) where
  toFun z := expNeg (V z)
  map_zero' := by simp [expNeg_top]
  map_one' := by simp [← WithTop.coe_zero, expNeg_coe]
  map_mul' a b := by simp [V.map_mul, expNeg_add]
  map_add_le_max' a b := by
    rw [← expNeg_antitone.map_min]
    exact expNeg_antitone (V.map_add a b)

private theorem valuationOfAddValuation_apply {R : Type*} [Ring R]
    (V : AddValuation R (WithTop ℤ)) (z : R) :
    valuationOfAddValuation V z = expNeg (V z) := rfl

private theorem isRegularSystemOfParameters_swap {R : Type*} [CommRing R] [IsLocalRing R]
    {x y : R} (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) :
    MMP.Mori.IsRegularSystemOfParameters ![y, x] := by
  refine ⟨?_, hxy.2⟩
  rw [← hxy.1]
  congr 1
  ext
  simp [Matrix.range_cons, Set.pair_comm]

/-- At a point with regular local ring, every prime divisor has a local equation: its stalk
ideal is principal, generated by a nonzero element. -/
private theorem exists_stalk_idealSheaf_eq_span {X : Scheme.{0}} [IsIntegral X] {η : X}
    [IsRegularLocalRing (X.presheaf.stalk η)] (S : MMP.Mori.PrimeDivisor X) :
    ∃ g : X.presheaf.stalk η, g ≠ 0 ∧ IdealSheafData.stalk S.idealSheaf η = Ideal.span {g} := by
  have : IsDomain (X.presheaf.stalk η) := IsRegularLocalRing.isDomain _
  have : UniqueFactorizationMonoid (X.presheaf.stalk η) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  by_cases hS : η ∈ S.support
  · obtain ⟨q, -, hq, hh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support S hS
    obtain ⟨g, hg⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh).principal
    refine ⟨g, ?_, hq.trans hg⟩
    rintro rfl
    exact q.asIdeal.ne_bot_of_height_eq_one hh (by rw [hg, Ideal.span_singleton_eq_bot])
  · exact ⟨1, one_ne_zero, (MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support S hS).trans
      Ideal.span_singleton_one.symm⟩

/-- **A low-discrepancy valuation along a curve in the boundary.** Let `(Y, Θ)` be a pair on a
normal threefold, regular at the generic point `η_V` of an irreducible closed curve `V`, and let
`V ⊆ S` for a prime divisor `S` with `Θ(S) > 0`. Then some valuation with centre `V` has log
discrepancy `a(v; Y, Θ) < 2`. -/
private theorem exists_isCentre_hasLogDiscrepancy_lt_two {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {Θ : MMP.Mori.QDivisor Y} (hΘ : MMP.Fourfold.IsPair sY Θ) (hY : MMP.Mori.IsNormalVariety ℂ sY)
    (hdim : topologicalKrullDim Y = 3) {V : IrreducibleCloseds Y}
    (hV : topologicalKrullDim (V : Set Y) = 1)
    [IsRegularLocalRing (Y.presheaf.stalk V.isIrreducible.genericPoint)]
    {S : MMP.Mori.PrimeDivisor Y} (hVS : (V : Set Y) ⊆ S.support) (hb : 0 < Θ.coeff S) :
    ∃ v : Valuation Y.functionField (WithZero (Multiplicative ℤ)),
      MMP.Intersection.IsCentre ℂ sY v V ∧ ∃ a < 2, HasLogDiscrepancy sY Θ v a := by
  classical
  have hlft : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have hgen := V.isIrreducible.isGenericPoint_genericPoint V.isClosed
  have hdf := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
    V.isIrreducible.genericPoint
  rw [hgen.def, hV, hdim] at hdf
  have hcoh : Order.coheight V.isIrreducible.genericPoint = 2 := eq_of_one_add_eq (n := 2) hdf
  have hdim2 : ringKrullDim (Y.presheaf.stalk V.isIrreducible.genericPoint) = 2 := by
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, hcoh]
    rfl
  obtain ⟨n, z, hz⟩ :=
    MMP.Mori.exists_isRegularSystemOfParameters (Y.presheaf.stalk V.isIrreducible.genericPoint)
  obtain rfl : n = 2 := by
    have h := hz.2
    rw [hdim2] at h
    exact_mod_cast h.symm
  have hxt : MMP.Mori.IsRegularSystemOfParameters ![z 0, z 1] := by
    convert hz using 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨hfin, -, -, W, hW, -⟩ := MMP.Resolution.exists_addValuation_monomialValuation
    Y.functionField (isRegularSystemOfParameters_swap hxt) (le_refl 1)
  have hvalW : ∀ f : Y.presheaf.stalk V.isIrreducible.genericPoint, f ≠ 0 →
      ∃ M : ℕ, MMP.Resolution.monomialValuation (z 1) (z 0) 1 f = M ∧
        valuationOfAddValuation W (algebraMap _ Y.functionField f) =
          WithZero.exp (-(M : ℤ)) := by
    intro f hf
    obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp (hfin f hf)
    refine ⟨M, hM.symm, ?_⟩
    rw [valuationOfAddValuation_apply, hW, ← hM]
    rfl
  have hv : IsWeightedMonomialValuation sY V (z 0) (z 1) 1 (valuationOfAddValuation W) := by
    refine ⟨hY, ?_, inferInstance, hxt, le_rfl, hvalW⟩
    rw [MMP.Flips.codimension_eq_coheight_genericPoint]
    exact hcoh
  choose f hf0 hf using fun P : MMP.Mori.PrimeDivisor Y =>
    exists_stalk_idealSheaf_eq_span (η := V.isIrreducible.genericPoint) P
  refine ⟨_, hv.isNormalizedDivisorialValuation_and_isCentre.2, _, ?_,
    hv.hasLogDiscrepancy hΘ f (fun P _ => hf P)⟩
  -- the order of a local equation is a natural number, at least `1` along `S`
  have hM : ∀ P : MMP.Mori.PrimeDivisor Y,
      0 ≤ -WithZero.log (valuationOfAddValuation W (algebraMap _ Y.functionField (f P))) ∧
        (V.isIrreducible.genericPoint ∈ P.support →
          1 ≤ -WithZero.log (valuationOfAddValuation W (algebraMap _ Y.functionField (f P)))) := by
    intro P
    obtain ⟨M, hMv, hvM⟩ := hvalW (f P) (hf0 P)
    rw [hvM, WithZero.log_exp, neg_neg]
    refine ⟨Int.natCast_nonneg M, fun hP => ?_⟩
    obtain ⟨q, -, hq, -⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support P hP
    have hmem : f P ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk V.isIrreducible.genericPoint) := by
      refine IsLocalRing.le_maximalIdeal q.isPrime.ne_top ?_
      rw [← hq, hf P]
      exact Ideal.mem_span_singleton_self _
    have h1 : (1 : ℕ∞) ≤ M := by
      rw [← hMv, monomialValuation_one_eq_iSup hxt]
      exact le_iSup₂_of_le (f := fun (n : ℕ) (_ : f P ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk V.isIrreducible.genericPoint) ^ n) =>
          (n : ℕ∞)) 1 (by rwa [pow_one]) le_rfl
    exact_mod_cast h1
  have hle : (Θ.coeff S : ℝ) ≤ ∑ P ∈ Θ.support, (Θ.coeff P : ℝ) *
      ((-WithZero.log (valuationOfAddValuation W (algebraMap _ Y.functionField (f P))) : ℤ) :
        ℝ) := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun P => (Θ.coeff P : ℝ) *
      ((-WithZero.log (valuationOfAddValuation W (algebraMap _ Y.functionField (f P))) : ℤ) : ℝ))
      (fun P _ => mul_nonneg (by exact_mod_cast hΘ.nonneg P) (by exact_mod_cast (hM P).1))
      (Finsupp.mem_support_iff.mpr hb.ne'))
    exact le_mul_of_one_le_right (by exact_mod_cast hΘ.nonneg S)
      (by exact_mod_cast (hM S).2 (hVS hgen.mem))
  have hbR : (0 : ℝ) < (Θ.coeff S : ℝ) := by exact_mod_cast hb
  rw [Nat.cast_one]
  linarith

end MonomialValuation

/-! ### Branch numbers at a regular point of a prime divisor -/

section BranchNumber

/-- A point of a prime divisor `S` of a threefold lying over the generic point of an irreducible
closed curve `V ⊆ Y` has coheight one in `S`. -/
private theorem coheight_eq_one_of_subschemeι_eq_genericPoint {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} [AlgebraicGeometry.IsVariety ℂ sY] (hdim : topologicalKrullDim Y = 3)
    (S : MMP.Mori.PrimeDivisor Y) {V : IrreducibleCloseds Y}
    (hV : topologicalKrullDim (V : Set Y) = 1) {s : S.idealSheaf.subscheme}
    (hs : S.idealSheaf.subschemeι s = V.isIrreducible.genericPoint) :
    Order.coheight s = 1 := by
  haveI : IsIntegral Y := (inferInstance : AlgebraicGeometry.IsVariety ℂ sY).toIsIntegral
  haveI := S.integral
  haveI : AlgebraicGeometry.IsVariety ℂ (S.idealSheaf.subschemeι ≫ sY) :=
    (MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  set ι := S.idealSheaf.subschemeι
  have hgen := V.isIrreducible.isGenericPoint_genericPoint V.isClosed
  have hdimS : topologicalKrullDim S.idealSheaf.subscheme = 2 := by
    have hdP := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY S.genericPoint
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, hdim] at hdP
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (ι.isClosedEmbedding.isEmbedding.toHomeomorph.trans
        (Homeomorph.setCongr
          (Scheme.IdealSheafData.range_subschemeι S.idealSheaf))).isHomeomorph).trans
      (eq_of_add_one_eq (n := 2) hdP)
  have hdimCs : topologicalKrullDim (closure ({s} : Set S.idealSheaf.subscheme)) = 1 := by
    rw [← hV]
    have hemb : Topology.IsEmbedding
        (fun p : closure ({s} : Set S.idealSheaf.subscheme) => ι p.1) :=
      ι.isClosedEmbedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    have hrange : Set.range (fun p : closure ({s} : Set S.idealSheaf.subscheme) => ι p.1) =
        (V : Set Y) := by
      rw [show (fun p : closure ({s} : Set S.idealSheaf.subscheme) => ι p.1) = ι ∘ Subtype.val
        from rfl, Set.range_comp, Subtype.range_coe,
        ← ι.isClosedEmbedding.closure_image_eq, Set.image_singleton, hs, hgen.def]
    exact IsHomeomorph.topologicalKrullDim_eq _
      (hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)).isHomeomorph
  have hdS := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (ι ≫ sY) s
  rw [hdimS, hdimCs] at hdS
  exact eq_of_one_add_eq (n := 1) hdS

/-- Over an open `U` on which `ν` restricts to an isomorphism, a point `s ∈ U` has exactly one
preimage, and that preimage has the coheight of `s`. -/
private theorem eq_and_coheight_eq_of_isIso_morphismRestrict {X X' : Scheme} (ν : X' ⟶ X)
    {U : X.Opens} [IsIso (ν ∣_ U)] {s : X} (hsU : s ∈ U) {z₀ : X'} (hz₀ : ν z₀ = s) :
    (∀ z, ν z = s → z = z₀) ∧ Order.coheight z₀ = Order.coheight s := by
  have hcomm : ∀ p, U.ι ((ν ∣_ U) p) = ν ((ν ⁻¹ᵁ U).ι p) := fun p => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hlift : ∀ z, ν z = s → ∃ p, (ν ⁻¹ᵁ U).ι p = z := fun z hz => by
    rw [← Set.mem_range, Scheme.Opens.range_ι, SetLike.mem_coe, Scheme.Hom.mem_preimage, hz]
    exact hsU
  obtain ⟨p₀, hp₀⟩ := hlift z₀ hz₀
  refine ⟨fun z hz => ?_, ?_⟩
  · obtain ⟨p, hp⟩ := hlift z hz
    have h1 : U.ι ((ν ∣_ U) p) = U.ι ((ν ∣_ U) p₀) := by rw [hcomm, hcomm, hp, hp₀, hz, hz₀]
    have h2 := (ν ∣_ U).isOpenEmbedding.injective (U.ι.isOpenEmbedding.injective h1)
    rw [← hp, ← hp₀, h2]
  · calc Order.coheight z₀ = Order.coheight ((ν ⁻¹ᵁ U).ι p₀) := by rw [hp₀]
      _ = Order.coheight p₀ := coheight_eq_of_isOpenImmersion _
      _ = Order.coheight ((ν ∣_ U) p₀) := (coheight_eq_of_isOpenImmersion _).symm
      _ = Order.coheight (U.ι ((ν ∣_ U) p₀)) := (coheight_eq_of_isOpenImmersion _).symm
      _ = Order.coheight s := by rw [hcomm, hp₀, hz₀]

/-- **Branch number one at a regular point.** Let `S` be a prime divisor of a threefold `Y`
and `V ⊆ S` an irreducible closed curve at whose generic point `S` is regular. Then exactly one
prime divisor of the normalization `S^ν` maps onto `V`: `r_{V} = 1`. -/
private theorem branchNumber_eq_one_of_notMem_image_singularLocus {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} [AlgebraicGeometry.IsVariety ℂ sY] (hdim : topologicalKrullDim Y = 3)
    (S : MMP.Mori.PrimeDivisor Y) {V : IrreducibleCloseds Y}
    (hV : topologicalKrullDim (V : Set Y) = 1) (hVS : (V : Set Y) ⊆ S.support)
    (hreg : V.isIrreducible.genericPoint ∉
      S.idealSheaf.subschemeι '' singularLocus S.idealSheaf.subscheme) :
    branchNumber S V = 1 := by
  classical
  haveI : IsIntegral Y := (inferInstance : AlgebraicGeometry.IsVariety ℂ sY).toIsIntegral
  haveI := S.integral
  haveI hvarS : AlgebraicGeometry.IsVariety ℂ (S.idealSheaf.subschemeι ≫ sY) :=
    (MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨⟨-, -, hfinν, hsurj, -⟩, ⟨U, hU, hiso⟩, -⟩ :=
    MMP.Threefold.normalization_spec (S.idealSheaf.subschemeι ≫ sY)
  set ν := S.idealSheaf.subscheme.normalization
    (MMP.finite_irreducibleComponents_of_isIntegral S.idealSheaf.subscheme)
  set ι := S.idealSheaf.subschemeι with hι
  have hgen := V.isIrreducible.isGenericPoint_genericPoint V.isClosed
  -- the point `s` of `S` over `η_V`
  obtain ⟨s, hs⟩ : V.isIrreducible.genericPoint ∈ Set.range ι := by
    rw [hι, Scheme.IdealSheafData.range_subschemeι]
    exact hVS hgen.mem
  have hsreg : IsRegularLocalRing (S.idealSheaf.subscheme.presheaf.stalk s) :=
    not_not.mp fun h => hreg ⟨s, h, hs⟩
  have hsU : s ∈ U := by
    rw [← SetLike.mem_coe, hU]
    haveI := IsRegularLocalRing.isDomain (S.idealSheaf.subscheme.presheaf.stalk s)
    haveI := IsRegularLocalRing.uniqueFactorizationMonoid
      (S.idealSheaf.subscheme.presheaf.stalk s)
    exact (inferInstance : IsIntegrallyClosed (S.idealSheaf.subscheme.presheaf.stalk s))
  have hcohs := coheight_eq_one_of_subschemeι_eq_genericPoint (sY := sY) hdim S hV hs
  -- over `U` the normalization is an isomorphism
  haveI := hsurj
  haveI := hiso
  haveI := hfinν
  obtain ⟨z₀, hz₀⟩ := ν.surjective s
  obtain ⟨huniq, hcoh0⟩ := eq_and_coheight_eq_of_isIso_morphismRestrict ν hsU hz₀
  rw [hcohs] at hcoh0
  -- the images of prime divisors of `S^ν`
  have hfun : ⇑(ν ≫ ι) = ⇑ι ∘ ⇑ν := funext fun _ => rfl
  have hcl : IsClosedMap (ν ≫ ι) := by
    rw [hfun]
    exact ι.isClosedEmbedding.isClosedMap.comp ν.isClosedMap
  have himg : ∀ Q : MMP.Mori.PrimeDivisor (S.idealSheaf.subscheme.normalizationScheme
      (MMP.finite_irreducibleComponents_of_isIntegral S.idealSheaf.subscheme)),
      (ν ≫ ι) '' Q.support = closure {ι (ν Q.genericPoint)} := by
    intro Q
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← hcl.closure_image_eq_of_continuous (ν ≫ ι).continuous, Set.image_singleton]
    rfl
  have hset : {Q : MMP.Mori.PrimeDivisor (S.idealSheaf.subscheme.normalizationScheme
      (MMP.finite_irreducibleComponents_of_isIntegral S.idealSheaf.subscheme)) |
      (ν ≫ ι) '' Q.support = (V : Set Y)} =
        {AlgebraicGeometry.PrimeDivisor.ofCoheightOne z₀ hcoh0} := by
    ext Q
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [himg]
    constructor
    · intro hQ
      have hQη : ι (ν Q.genericPoint) = V.isIrreducible.genericPoint :=
        (inseparable_iff_closure_eq.mpr (hQ.trans hgen.def.symm)).eq
      have hνQ : ν Q.genericPoint = s := ι.isClosedEmbedding.injective (hQη.trans hs.symm)
      apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
      exact huniq _ hνQ
    · rintro rfl
      have hg0 : MMP.Mori.PrimeDivisor.genericPoint
          (AlgebraicGeometry.PrimeDivisor.ofCoheightOne z₀ hcoh0) = z₀ :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      rw [hg0, hz₀, hs, hgen.def]
  change {Q : MMP.Mori.PrimeDivisor (S.idealSheaf.subscheme.normalizationScheme
      (MMP.finite_irreducibleComponents_of_isIntegral S.idealSheaf.subscheme)) |
      (ν ≫ ι) '' Q.support = (V : Set Y)}.ncard = 1
  rw [hset, Set.ncard_singleton]

end BranchNumber

/-! ### Brackets off a finite set of curves -/

/-- A sum over `t` is the sum over `s` along an injection `g : s → t` whose image contains the
support of the summand on `t`. -/
private theorem finsum_mem_eq_finsum_mem_comp {α ι M : Type*} [AddCommMonoid M] {f : α → M}
    {g : ι → α} {s : Set ι} {t : Set α} (hg : Set.InjOn g s) (hst : g '' s ⊆ t)
    (hts : t ∩ Function.support f ⊆ g '' s) :
    ∑ᶠ a ∈ t, f a = ∑ᶠ i ∈ s, f (g i) := by
  rw [← finsum_mem_image hg, ← finsum_mem_inter_support, ← finsum_mem_inter_support (s := g '' s),
    (Set.subset_inter hts Set.inter_subset_right).antisymm
      (Set.inter_subset_inter_left _ hst)]

/-- The closure of the generic point of a proper curve, as a subspace of `X`, has dimension
one: it is the image of the closed embedding `C ⟶ X`. -/
private theorem topologicalKrullDim_closure_point {k : Type*} [Field k] {X : Scheme}
    {sX : X ⟶ Spec (.of k)} (C : MMP.Mori.ProperCurve sX) :
    topologicalKrullDim (closure {C.point} : Set X) = 1 := by
  have hr : Set.range C.ι = closure {C.point} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [← hr, ← C.dim_eq]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    C.ι.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

/-- **Brackets vanish off a finite set of curves.** On a model `(Y, Θ)` of a prepared chain there
is a finite set `𝒮` of irreducible closed subsets such that every bracket value `β_C` at a proper
curve `C` whose closure is not in `𝒮` is `0`. -/
private theorem exists_finite_forall_isCurveBracket_eq_zero {T : StabilizedTail}
    (Q : PreparedChain T) (x : Q.ModelIndex) :
    ∃ 𝒮 : Set (IrreducibleCloseds (Q.chain.model x.1)), 𝒮.Finite ∧
      ∀ γ : MMP.Mori.ProperCurve (Q.chain.modelStructure x.1),
        closure {γ.point} ∉ ((↑) : _ → Set (Q.chain.model x.1)) '' 𝒮 →
        ∀ β : ℤ, Q.IsCurveBracket x γ β → β = 0 := by
  classical
  set Y := Q.chain.model x.1
  set sY := Q.chain.modelStructure x.1
  set Θ := Q.chain.modelBoundary x.1
  obtain ⟨hΘ, hY, hQf, hdim, ⟨c, hcinj, hcc, hcsupp, hccoeff⟩, hreg⟩ := Q.echoSetting_model x
  have hnv : MMP.Mori.IsNormalVariety ℂ sY := hQf.1
  have hpair : MMP.Fourfold.IsPair sY Θ := hΘ.1.1
  have : Finite Q.chain.Label := Q.chain.finite_label
  set L : Finset (MMP.Mori.PrimeDivisor Y) := (Set.finite_range c).toFinset
  have hmemL : ∀ S ∈ L, ∃ h, c h = S := fun S hS => (Set.finite_range c).mem_toFinset.mp hS
  have hcL : ∀ h, c h ∈ L := fun h => (Set.finite_range c).mem_toFinset.mpr ⟨h, rfl⟩
  have hsupp : Θ.support ⊆ L := fun P hP =>
    (Set.finite_range c).mem_toFinset.mpr (hcsupp P (Finsupp.mem_support_iff.mp hP))
  have hlt : ∀ S ∈ L, Θ.coeff S < 1 := fun S hS => by
    obtain ⟨h, rfl⟩ := hmemL S hS
    exact (hccoeff h).2
  obtain ⟨𝒮, h𝒮, -, h𝒮gen⟩ := exists_finite_forall_isEcho_of_isCentre sY hY hQf hdim hΘ hsupp
  refine ⟨𝒮, h𝒮, fun γ hγ β hβ => ?_⟩
  let V : IrreducibleCloseds Y :=
    ⟨closure {γ.point}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hV𝒮 : V ∉ 𝒮 := fun h => hγ ⟨V, h, rfl⟩
  have hVdim : topologicalKrullDim (V : Set Y) = 1 := topologicalKrullDim_closure_point γ
  -- the valuations of the first sum are those with centre `V`
  have hcent : {v | ∃ Z : IrreducibleCloseds Y, MMP.Intersection.IsCentre ℂ sY v Z ∧
      (Z : Set Y) = closure {γ.point}} = {v | MMP.Intersection.IsCentre ℂ sY v V} :=
    Set.ext fun v => ⟨fun ⟨Z, hc, hZ⟩ => by
      obtain rfl : Z = V := IrreducibleCloseds.ext hZ
      exact hc, fun hc => ⟨V, hc, rfl⟩⟩
  obtain ⟨w, r, d, hw, hr, hd, hβeq⟩ := hβ
  change β = ((∑ᶠ v ∈ {v | ∃ Z : IrreducibleCloseds Y, MMP.Intersection.IsCentre ℂ sY v Z ∧
      (Z : Set Y) = closure {γ.point}}, w v : ℕ) : ℤ) - _ at hβeq
  rw [hcent] at hβeq
  have hcen : ∀ S P, Q.chain.IsLabelCentre S x.1 P → P = c S := fun S P h =>
    isLabelCentre_unique Q.chain S x.1 hnv h (hcc S)
  have hr' : ∀ S, r S = branchNumber (c S) (closure {γ.point}) := fun S => by
    obtain ⟨P, hP, h⟩ := hr S
    rw [h, hcen S P hP]
  have hd' : ∀ S, d S = defaultWeight Q.scale ((Θ.coeff (c S) : ℚ) : ℝ) := fun S => by
    obtain ⟨b, ⟨P, hP, hb⟩, h⟩ := hd S
    rw [h, ← hb, hcen S P hP]
  have hw' : ∀ v, MMP.Intersection.IsCentre ℂ sY v V →
      ∃ a, HasLogDiscrepancy sY Θ v a ∧ w v = difficultyWeight Q.scale (2 - a) := fun v hv => by
    obtain ⟨-, a, ⟨n, D, -, hv, ha⟩, h⟩ := hw v ((Set.ext_iff.mp hcent v).mpr hv)
    exact ⟨a, ⟨n, D, hv, ha⟩, h⟩
  have hwpos : ∀ v, MMP.Intersection.IsCentre ℂ sY v V → w v ≠ 0 →
      ∃ a < 2, HasLogDiscrepancy sY Θ v a := fun v hv hne => by
    obtain ⟨a, ha, h⟩ := hw' v hv
    exact ⟨a, lt_of_not_ge fun h2 =>
      hne (h.trans (difficultyWeight_of_nonpos (sub_nonpos.mpr h2))), ha⟩
  rw [hβeq, sub_eq_zero, Nat.cast_inj]
  by_cases hcase : ∃ ξ, MMP.Intersection.IsCentre ℂ sY ξ V ∧ ∃ a < 2, HasLogDiscrepancy sY Θ ξ a
  · -- some valuation at `C` has `a < 2`: the weights at `C` are those of the echoes
    obtain ⟨ξ, hξc, hξa⟩ := hcase
    obtain ⟨hη, S₀, hS₀L, hVS₀, huniq, -⟩ := h𝒮gen V hVdim hV𝒮 ξ hξc hξa
    obtain ⟨h₀, rfl⟩ := hmemL S₀ hS₀L
    obtain ⟨hex, -, hdist⟩ := existsUnique_isEcho hnv hdim hS₀L hVS₀ hVdim hη
    let g : ℕ → Valuation Y.functionField (WithZero (Multiplicative ℤ)) := fun j =>
      if h : 1 ≤ j then (hex j h).exists.choose else (hex 1 le_rfl).exists.choose
    have hg : ∀ j, 1 ≤ j → IsEcho sY L (c h₀) V j (g j) := fun j h => by
      simp only [g, dif_pos h]
      exact (hex j h).exists.choose_spec
    have hgc : ∀ j, 1 ≤ j → MMP.Intersection.IsCentre ℂ sY (g j) V := fun j h =>
      (hg j h).2.2.2.2.2.2.2.1
    have hval : ∑ᶠ v ∈ {v | MMP.Intersection.IsCentre ℂ sY v V}, w v =
        defaultWeight Q.scale ((Θ.coeff (c h₀) : ℚ) : ℝ) := by
      rw [finsum_mem_eq_finsum_mem_comp (g := g) (s := {j | 1 ≤ j})
        (fun j hj j' hj' he => by_contra fun hne => hdist j j' _ _ (hg j hj) (hg j' hj') hne he)
        (by rintro _ ⟨j, hj, rfl⟩; exact hgc j hj)
        (fun v ⟨hv, hwv0⟩ => by
          obtain ⟨-, S', hS'L, hVS', -, j, hj, he, -⟩ := h𝒮gen V hVdim hV𝒮 v hv (hwpos v hv hwv0)
          obtain rfl := huniq S' hS'L hVS'
          exact ⟨j, hj, (hex j hj).unique (hg j hj) he⟩)]
      refine finsum_mem_congr rfl fun j (hj : 1 ≤ j) => ?_
      obtain ⟨a, ha, h⟩ := hw' _ (hgc j hj)
      rw [h, HasLogDiscrepancy.unique ha ((hg j hj).hasLogDiscrepancy hpair hsupp hlt)]
      congr 1
      ring
    rw [hval, finsum_eq_single _ h₀ fun S hS => ?_]
    · haveI : AlgebraicGeometry.IsVariety ℂ sY := hnv.1
      rw [hr', hd', show branchNumber (c h₀) (closure {γ.point}) = 1 from
        branchNumber_eq_one_of_notMem_image_singularLocus (sY := sY) hdim (c h₀) hVdim hVS₀
          ((mem_oneLabelSmoothLocus_iff.mp hη).2.1 (c h₀) (hcL h₀)), one_mul]
    · rw [hr', branchNumber_eq_zero_of_not_subset (Z := closure {γ.point})
        (fun h => hS (hcinj (huniq _ (hcL S) h))), zero_mul]
  · -- no valuation at `C` has `a < 2`: all weights at `C` and all defaults through `C` vanish
    push Not at hcase
    rw [finsum_mem_eq_zero_of_forall_eq_zero (s := {v | MMP.Intersection.IsCentre ℂ sY v V})
        fun v hv => by_contra fun hne =>
        let ⟨a, ha, hla⟩ := hwpos v hv hne; hcase v hv a ha hla,
      finsum_eq_zero_of_forall_eq_zero fun S => ?_]
    by_cases hVS : closure {γ.point} ⊆ (c S).support
    · have hb : Θ.coeff (c S) = 0 := by
        by_contra hb
        haveI := hreg V hVdim
        obtain ⟨v, hvc, a, ha, hla⟩ := exists_isCentre_hasLogDiscrepancy_lt_two hpair hnv hdim
          hVdim hVS (lt_of_le_of_ne (hccoeff S).1 (Ne.symm hb))
        exact hcase v hvc a ha hla
      rw [hd', hb, Rat.cast_zero, defaultWeight_zero, mul_zero]
    · rw [hr', branchNumber_eq_zero_of_not_subset hVS, zero_mul]

end Helpers

/-- **Brackets vanish at almost every curve.** On a model `(Y, Θ)` of a prepared chain, only
finitely many irreducible closed curves `C ⊆ Y` have a nonzero bracket `β_C(Y, Θ)`
(`MMP.Fourfold.StabilizedTail.PreparedChain.IsCurveBracket`). Consequently the first two sums in
the difficulty `MMP.Fourfold.StabilizedTail.PreparedChain.IsDifficulty` have finite support: the
summand of its first sum, `v ↦ w_v` on the valuations centred at a closed point and `0`
elsewhere, has finite support for any weights `w_v`
(`MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight`), and any choice of brackets
`γ ↦ β_γ` has finite support. -/
@[mmp "lem_mmp_indexd_brackets_cofinite"]
public theorem finite_setOf_isCurveBracket_ne_zero {T : StabilizedTail} (Q : PreparedChain T)
    (x : Q.ModelIndex) :
    {γ : MMP.Mori.ProperCurve (Q.chain.modelStructure x.1) |
      ∃ β : ℤ, Q.IsCurveBracket x γ β ∧ β ≠ 0}.Finite ∧
    (∀ w : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) → ℕ,
      (∀ v, (∃ Z : IrreducibleCloseds (Q.chain.model x.1),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧
            ∃ y : Q.chain.model x.1, IsClosed ({y} : Set (Q.chain.model x.1)) ∧
              (Z : Set (Q.chain.model x.1)) = {y}) →
        Q.chain.IsValuationWeight Q.scale x.1 v (w v)) →
      (Function.support fun v => ∑ᶠ (_ : ∃ Z : IrreducibleCloseds (Q.chain.model x.1),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧
            ∃ y : Q.chain.model x.1, IsClosed ({y} : Set (Q.chain.model x.1)) ∧
              (Z : Set (Q.chain.model x.1)) = {y}), w v).Finite) ∧
    (∀ β : MMP.Mori.ProperCurve (Q.chain.modelStructure x.1) → ℤ,
      (∀ γ, Q.IsCurveBracket x γ (β γ)) → (Function.support β).Finite) := by
  have hcurve : {γ : MMP.Mori.ProperCurve (Q.chain.modelStructure x.1) |
      ∃ β : ℤ, Q.IsCurveBracket x γ β ∧ β ≠ 0}.Finite := by
    obtain ⟨𝒮, h𝒮, key⟩ := exists_finite_forall_isCurveBracket_eq_zero Q x
    refine ((h𝒮.image ((↑) : IrreducibleCloseds _ → Set _)).preimage
        fun _ _ _ _ he => MMP.Mori.ProperCurve.ext (inseparable_iff_closure_eq.mpr he).eq).subset
      fun γ ⟨β, hβ, hβ0⟩ => ?_
    by_contra hγ
    exact hβ0 (key γ hγ β hβ)
  refine ⟨hcurve, fun w hw => ?_, fun β hβ => hcurve.subset fun γ hγ => ⟨β γ, hβ γ, hγ⟩⟩
  refine (finite_setOf_isCentre_singleton Q x).subset fun v hv => ?_
  classical
  rw [Function.mem_support, finsum_eq_if] at hv
  split_ifs at hv with hP
  · obtain ⟨Z, hc, y, hy, hZ⟩ := hP
    exact ⟨⟨Z, y, hc, hZ⟩, w v, hw v ⟨Z, hc, y, hy, hZ⟩, hv⟩
  · exact absurd rfl hv

end MMP.Fourfold.StabilizedTail.PreparedChain

end
