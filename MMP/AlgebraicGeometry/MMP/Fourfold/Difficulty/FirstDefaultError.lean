module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupEmbedded
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.EchoSetting
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.BranchMultiplicity
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings

/-!
# The first default error at a curve on a model of a prepared chain

Let `(Y, Θ)` be a model of a prepared chain at the fixed admissible scale `N`, with labels `S_h`
of coefficients `b_h`, and let `C ⊆ Y` be an irreducible closed curve with generic point `η_C`.
Write `m_h` for the multiplicity of `S_h` at `η_C`, `r_{C,h}` for the branch number of `S_h` at
`C` and `r_C^var = ∑_{h varying} r_{C,h}` for the varying branch number. With the weight
`w(u) = ⌈N max{u, 0}⌉`,
`w(∑_h m_h b_h) ≥ ∑_h r_{C,h} w(b_h) - max{r_C^var - 1, 0}`.

The proof uses `r_{C,h} ≤ m_h` in the two-dimensional regular local ring `𝒪_{Y,η_C}`, the
integrality of `N b_h` for the fixed labels, and `⌈x_1 + ⋯ + x_r⌉ ≥ ∑ ⌈x_ℓ⌉ - (r - 1)` for the
varying ones.

## Main results

* `MMP.Fourfold.StabilizedTail.PreparedChain.difficultyWeight_sum_mul_labelCoefficient_ge`: the
  statement above.

## Implementation notes

* The curve is a proper curve `MMP.Mori.ProperCurve` of the model, recorded by its generic point,
  as in `MMP.Fourfold.StabilizedTail.PreparedChain.IsCurveBracket`. The multiplicity of `S_h` at
  `η_C` is `MMP.Resolution.multAt` of the ideal sheaf of the centre of `S_h` on the model, as in
  `MMP.Fourfold.StabilizedTail.PreparedChain.sum_mul_labelCoefficient_lt_one`. Multiplicities,
  coefficients, branch numbers and the varying branch number are characterised by predicates on
  their values, so the statement takes chosen values pinned by those predicates.
* The inequality is stated in `ℤ`; the labels are finitely many, so `∑ᶠ` is a finite sum.
-/

@[expose] public section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold MMP.Fourfold.StabilizedTail
  Order

namespace MMP.Fourfold.FirstDefaultError

/-! ### The elementary ceiling inequality -/

/-- If `y_i` is an integer whenever `¬ p i`, then
`⌈∑ r_i y_i⌉ ≥ ∑ r_i ⌈y_i⌉ - max{∑_{p i} r_i - 1, 0}`. -/
private theorem sum_mul_ceil_sub_le_ceil_sum {ι : Type*} (s : Finset ι) (p : ι → Prop)
    [DecidablePred p] (r : ι → ℕ) (y : ι → ℝ) (hy : ∀ i ∈ s, ¬ p i → ∃ z : ℤ, y i = z) :
    ∑ i ∈ s, (r i : ℤ) * ⌈y i⌉ - max ((∑ i ∈ s with p i, (r i : ℤ)) - 1) 0 ≤
      ⌈∑ i ∈ s, (r i : ℝ) * y i⌉ := by
  set R : ℤ := ∑ i ∈ s with p i, (r i : ℤ) with hRdef
  set A : ℤ := ∑ i ∈ s, (r i : ℤ) * ⌈y i⌉ with hAdef
  set X : ℝ := ∑ i ∈ s, (r i : ℝ) * y i with hXdef
  have hterm : ∀ i ∈ s, (((r i : ℤ) * ⌈y i⌉ : ℤ) : ℝ) ≤
      (r i : ℝ) * y i + if p i then (r i : ℝ) else 0 := by
    intro i hi
    split_ifs with h
    · have := Int.ceil_lt_add_one (y i)
      have hr0 : (0 : ℝ) ≤ r i := Nat.cast_nonneg _
      push_cast
      nlinarith
    · obtain ⟨z, hz⟩ := hy i hi h
      rw [hz, Int.ceil_intCast]
      simp
  have hR : (R : ℝ) = ∑ i ∈ s, if p i then (r i : ℝ) else 0 := by
    rw [hRdef, ← Finset.sum_filter]
    push_cast
    rfl
  have hA : (A : ℝ) ≤ X + R := by
    rw [hR, hXdef, ← Finset.sum_add_distrib, hAdef]
    push_cast
    exact Finset.sum_le_sum fun i hi => by exact_mod_cast hterm i hi
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  rcases hR0.eq_or_lt with h0 | hpos
  · have hAX : (A : ℝ) ≤ X := by simpa [← h0] using hA
    have : A ≤ ⌈X⌉ := Int.cast_le.mp (hAX.trans (Int.le_ceil X))
    omega
  · obtain ⟨i, hi, hpi, hri⟩ : ∃ i ∈ s, p i ∧ 0 < r i := by
      by_contra hne
      push Not at hne
      refine hpos.ne' (Finset.sum_eq_zero fun i hi => ?_)
      obtain ⟨his, hpi⟩ := Finset.mem_filter.mp hi
      exact_mod_cast Nat.le_zero.mp (hne i his hpi)
    have hlt : (A : ℝ) < X + R := by
      rw [hR, hXdef, ← Finset.sum_add_distrib, hAdef]
      push_cast
      refine Finset.sum_lt_sum (fun i hi => by exact_mod_cast hterm i hi) ⟨i, hi, ?_⟩
      rw [if_pos hpi]
      have := Int.ceil_lt_add_one (y i)
      have hr0 : (0 : ℝ) < r i := by exact_mod_cast hri
      nlinarith
    have : A - R < ⌈X⌉ := Int.lt_ceil.mpr (by push_cast; linarith)
    omega

/-! ### Dimensions -/

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
private theorem coheight_point_eq_two {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y]
    [LocallyOfFiniteType sY] (hY : topologicalKrullDim Y = 3)
    (γ : MMP.Mori.ProperCurve sY) : coheight γ.point = 2 := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY γ.point
  rw [← topologicalKrullDim_curveSubschemeAt, γ.isProperCurve.dim_eq, hY] at h
  have h' : (1 + coheight γ.point : ℕ∞) = 1 + 2 := WithBot.coe_injective (by push_cast; exact h)
  exact (WithTop.add_left_inj ENat.one_ne_top).mp h'

/-! ### Label centres on the models of a terminal chain -/

section LabelCentre

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
    have hb := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism
    haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := hb.isDominant
    exact valuation_eq_of_comap_eq hb.functionFieldMap_bijective.2
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
      rw [hv]
      rfl)
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective this

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
    have heq := P.modelMap_eq n (by omega)
    have hpeq := P.πY_eq n (by omega)
    haveI : IsDominant (P.h n) := by
      have : IsDominant (P.g n ≫ P.h n) := heq ▸ hd
      exact IsDominant.of_comp (P.g n) (P.h n)
    change ∃ _ : IsDominant (P.πY n), Function.Surjective (functionFieldMap (P.πY n))
    have hd' : IsDominant (P.πY n) := hpeq ▸ (inferInstance : IsDominant (P.gp n ≫ P.h n))
    refine ⟨hd', ?_⟩
    have hgb := hD.isBirationalMorphism_minus.functionFieldMap_bijective
    have hpb := hD.isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective
    have hh : Function.Surjective (functionFieldMap (P.h n)) := by
      refine Function.Surjective.of_comp_left ?_ hgb.1
      have : (functionFieldMap (P.g n)) ∘ (functionFieldMap (P.h n)) =
          functionFieldMap (modelMap π P.πY n) := by
        funext t
        rw [Function.comp_apply, MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
        exact congrArg (fun φ => φ t)
          (MMP.Positivity.DivisorOver.functionFieldMap_congr heq.symm)
      rwa [this]
    have : functionFieldMap (P.πY n) =
        (functionFieldMap (P.gp n)).comp (functionFieldMap (P.h n)) := by
      ext t
      rw [RingHom.comp_apply, MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
      exact congrArg (fun φ => φ t) (MMP.Positivity.DivisorOver.functionFieldMap_congr hpeq)
    rw [this, RingHom.coe_comp]
    exact hpb.2.comp hh

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
  have hπ : Function.Surjective (functionFieldMap ((C.junction i).p ≫ T.f i)) := by
    have : functionFieldMap ((C.junction i).p ≫ T.f i) =
        (functionFieldMap (C.junction i).p).comp (functionFieldMap (T.f i)) := by
      ext t
      rw [RingHom.comp_apply, MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
    rw [this, RingHom.coe_comp]
    exact hpb.functionFieldMap_bijective.2.comp hfb.functionFieldMap_bijective.2
  exact (surjective_functionFieldMap_modelMap_of_le (C.bridge i).P hπ k k.2.le).snd

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

/-! ### Branch numbers and multiplicities -/

/-- The multiplicity of a prime divisor along an irreducible closed subset is the multiplicity of
its ideal at the generic point. -/
private theorem multiplicityAlong_eq_multAt {Y : Scheme.{0}} (D : MMP.Mori.PrimeDivisor Y)
    (V : IrreducibleCloseds Y) :
    D.multiplicityAlong V = MMP.Resolution.multAt D.idealSheaf V.isIrreducible.genericPoint := by
  rw [MMP.Mori.PrimeDivisor.multiplicityAlong, Scheme.IdealSheafData.stalkIdeal_eq_stalk]
  rfl

/-- On a threefold that is regular at the generic points of its curves, the branch number of a
prime divisor `P` at a proper curve `C` is at most the multiplicity of `P` at `η_C`. -/
private theorem branchNumber_le_multAt {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y]
    [LocallyOfFiniteType sY] (hY : topologicalKrullDim Y = 3)
    (hreg : ∀ V : IrreducibleCloseds Y, topologicalKrullDim (V : Set Y) = 1 →
      IsRegularLocalRing (Y.presheaf.stalk V.isIrreducible.genericPoint))
    (γ : MMP.Mori.ProperCurve sY) (P : MMP.Mori.PrimeDivisor Y) :
    (branchNumber P (closure {γ.point}) : ℕ∞) ≤ MMP.Resolution.multAt P.idealSheaf γ.point := by
  let V : IrreducibleCloseds Y :=
    ⟨closure {γ.point}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hηV : V.isIrreducible.genericPoint = γ.point :=
    V.isIrreducible.isGenericPoint_genericPoint_closure.eq closure_closure.symm
  have hdimV : topologicalKrullDim (V : Set Y) = 1 :=
    (topologicalKrullDim_curveSubschemeAt γ.point).symm.trans γ.isProperCurve.dim_eq
  have hring : ringKrullDim (Y.presheaf.stalk V.isIrreducible.genericPoint) = 2 := by
    rw [ringKrullDim_stalk_eq_coheight, hηV, coheight_point_eq_two hY γ]
    rfl
  have h := encard_branches_le_multiplicityAlong sY V (hreg V hdimV) hring P
  rw [multiplicityAlong_eq_multAt, hηV] at h
  rw [branchNumber, Set.ncard_def]
  exact (ENat.coe_toNat_le_self _).trans h

/-! ### The weight inequality -/

/-- If `r_i ≤ m_i`, `b_i ≥ 0`, and `N b_i` is an integer whenever `¬ p i`, then
`w(∑ m_i b_i) ≥ ∑ r_i w(b_i) - max{∑_{p i} r_i - 1, 0}` for the weight `w = difficultyWeight N`. -/
private theorem sum_mul_difficultyWeight_sub_le {ι : Type*} [Fintype ι] (p : ι → Prop)
    [DecidablePred p] (N : ℕ) {r m : ι → ℕ} {b : ι → ℝ} (hrm : ∀ i, r i ≤ m i)
    (hb : ∀ i, 0 ≤ b i) (hfix : ∀ i, ¬ p i → ∃ z : ℤ, (N : ℝ) * b i = z) :
    ∑ i, (r i : ℤ) * difficultyWeight N (b i) - max ((∑ i with p i, (r i : ℤ)) - 1) 0 ≤
      difficultyWeight N (∑ i, (m i : ℝ) * b i) := by
  have hw : ∀ i, (difficultyWeight N (b i) : ℤ) = ⌈(N : ℝ) * b i⌉ := fun i => by
    rw [natCast_difficultyWeight, max_eq_left (hb i)]
  simp only [hw]
  calc _ ≤ ⌈∑ i, (r i : ℝ) * ((N : ℝ) * b i)⌉ :=
        sum_mul_ceil_sub_le_ceil_sum Finset.univ p r _ fun i _ h => hfix i h
    _ = difficultyWeight N (∑ i, (r i : ℝ) * b i) := by
        rw [natCast_difficultyWeight,
          max_eq_left (Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hb i)),
          Finset.mul_sum]
        simp_rw [mul_left_comm]
    _ ≤ _ := Int.ofNat_le.mpr (difficultyWeight_mono N (Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hrm i)) (hb i)))

end MMP.Fourfold.FirstDefaultError

namespace MMP.Fourfold.StabilizedTail.PreparedChain

open MMP.Mori MMP.Fourfold.FirstDefaultError

/-- **First default error.** On a model `(Y, Θ)` of a prepared chain, let `γ` be an irreducible
closed curve of `Y`, `m S` the multiplicity at the generic point of `γ` of the label `S`
(`MMP.Resolution.multAt` of the ideal of the centre of `S` on `Y`), `b S` the coefficient of `S`
in `Θ`, `r S` the branch number of `S` at `γ` and `rv` the varying branch number at `γ`. With
`w = MMP.Fourfold.difficultyWeight` at the admissible scale of the chain,
`w(∑_S m S * b S) ≥ ∑_S r S * w(b S) - max{rv - 1, 0}`. -/
@[mmp "lem_mmp_indexd_first_default_error"]
public theorem difficultyWeight_sum_mul_labelCoefficient_ge {T : StabilizedTail}
    (Q : PreparedChain T) (x : Q.ModelIndex) (γ : ProperCurve (Q.chain.modelStructure x.1))
    (m : Q.chain.Label → ℕ) (b : Q.chain.Label → ℚ) (r : Q.chain.Label → ℕ) (rv : ℕ)
    (hm : ∀ S, ∃ P : MMP.Mori.PrimeDivisor (Q.chain.model x.1),
      Q.chain.IsLabelCentre S x.1 P ∧ MMP.Resolution.multAt P.idealSheaf γ.point = m S)
    (hb : ∀ S, Q.chain.IsLabelCoefficient S x.1 (b S))
    (hr : ∀ S, Q.chain.IsLabelBranchNumber S x.1 γ (r S))
    (hrv : Q.chain.IsVaryingBranchNumber x.1 γ rv) :
    ∑ᶠ S, (r S : ℤ) * difficultyWeight Q.scale (b S) - max ((rv : ℤ) - 1) 0 ≤
      difficultyWeight Q.scale (∑ᶠ S, (m S : ℝ) * (b S : ℝ)) := by
  classical
  obtain ⟨-, hproj, -, hdim, ⟨c, -, hc, -, hcoeff⟩, hreg⟩ := echoSetting_model Q x
  haveI := Q.chain.finite_label
  letI : Fintype Q.chain.Label := Fintype.ofFinite _
  haveI : LocallyOfFiniteType (Q.chain.modelStructure x.1) := hproj.toLocallyOfFiniteType
  have hrm : ∀ S, r S ≤ m S := fun S => by
    obtain ⟨P, hP, hrP⟩ := hr S
    obtain ⟨P', hP', hmP'⟩ := hm S
    obtain rfl := isLabelCentre_unique Q.chain hP' hP
    have h := branchNumber_le_multAt hdim hreg γ P'
    rw [hmP', ← hrP] at h
    exact_mod_cast h
  have hb0 : ∀ S, (0 : ℝ) ≤ b S := fun S => by
    obtain ⟨P, hP, hPb⟩ := hb S
    rw [← hPb, isLabelCentre_unique Q.chain hP (hc S)]
    exact_mod_cast (hcoeff S).1
  have hfix : ∀ S, ¬ Q.chain.IsVaryingLabel S → ∃ z : ℤ, (Q.scale : ℝ) * b S = z := by
    intro S hS
    obtain ⟨c0, ⟨n, hn⟩, hall⟩ :=
      Q.isLabelCoefficient_of_isFixedLabel S ((Q.chain.not_isVaryingLabel_iff S).1 hS)
    obtain ⟨P, hP, hPc⟩ := hall x.1 x.2
    obtain ⟨P', hP', hP'b⟩ := hb S
    obtain ⟨z, hz⟩ := Q.isAdmissibleScale.exists_intCast_eq_of_eventually hn
    refine ⟨z, ?_⟩
    rw [← hP'b, isLabelCentre_unique Q.chain hP' hP, hPc]
    exact_mod_cast hz
  have hrv' : (rv : ℤ) = ∑ S with Q.chain.IsVaryingLabel S, (r S : ℤ) := by
    obtain ⟨r', hr', rfl⟩ := hrv
    rw [finsum_eq_sum_of_fintype, Finset.sum_filter]
    push_cast
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [finsum_eq_if]
    split_ifs with h
    · obtain ⟨P, hP, h1⟩ := hr' S h
      obtain ⟨P', hP', h2⟩ := hr S
      rw [h1, h2, isLabelCentre_unique Q.chain hP hP']
    · rfl
  rw [hrv', finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  exact sum_mul_difficultyWeight_sub_le _ Q.scale hrm hb0 hfix

end MMP.Fourfold.StabilizedTail.PreparedChain

end
