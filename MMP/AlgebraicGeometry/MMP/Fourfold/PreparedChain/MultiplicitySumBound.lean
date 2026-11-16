module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainBracket
public import Mathlib.Topology.KrullDimension
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.PreparedChainTerminal
import MMP.AlgebraicGeometry.Singularities.Terminal.PairSmoothCodimTwo
import MMP.AlgebraicGeometry.Singularities.WeightedMonomialValuation
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount

/-!
# The weighted multiplicity of the labels at a surface is less than one

Let `(Y, Θ)`, `Θ = ∑_h b_h S_h`, be a model of a prepared chain of fourfolds, and let `V ⊆ Y` be
an irreducible surface. Write `m_h` for the multiplicity at the generic point `η_V` of the
label `S_h` (so `m_h = 0` if `V ⊄ S_h`). Then `∑_h m_h b_h < 1`: the `𝔪_{η_V}`-adic order is an
exceptional divisorial valuation with centre `V` and log discrepancy `2 - ∑_h m_h b_h`, and the
pair is terminal.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.finsum_multiplicityAlong_mul_lt_one`:
  `∑_h m_h b_h < 1` at every irreducible surface of a model of a prepared chain.

## Implementation notes

The label coefficient `b_h` is the predicate
`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelCoefficient`, and the multiplicity of
`S_h` at `η_V` is `MMP.Mori.PrimeDivisor.multiplicityAlong` of the centre `S_h^Y`
(`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelCentre`) along `V`. The result is
stated for all values `m_h`, `b_h` satisfying these predicates. When `S_h^Y` is not a prime
divisor of `Y` its coefficient is `0`, so the value of `m_h` does not matter. The labels are
finitely many, so `∑ᶠ` is the finite sum.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
open MMP.Mori MMP.Fourfold MMP.Fourfold.StabilizedSmallKltTail
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.OAI4C2MultiplicitySumBound

/-! ### Distinct labels have distinct centres -/

/-- Valuations agreeing after composition with a surjective ring map agree. -/
private theorem valuation_eq_of_comap_eq {K L Γ : Type*} [CommRing K] [CommRing L]
    [LinearOrderedCommMonoidWithZero Γ] {φ : K →+* L} (hφ : Function.Surjective φ)
    {v w : Valuation L Γ} (h : v.comap φ = w.comap φ) : v = w :=
  Valuation.ext fun x => by
    obtain ⟨y, rfl⟩ := hφ x
    exact congrArg (fun u : Valuation K Γ => u y) h

/-- A valuation of `k(X_i)` corresponds to at most one valuation of `k(X_0)`. -/
private theorem corresponds_injective (T : StabilizedSmallKltTail) :
    ∀ (i : ℕ) {ξ ξ' : Valuation (T.X 0).functionField ℤᵐ⁰}
      {η : Valuation (T.X i).functionField ℤᵐ⁰},
      T.Corresponds i ξ η → T.Corresponds i ξ' η → ξ = ξ'
  | 0, _, _, _, h, h' => h.symm.trans h'
  | i + 1, _, _, _, ⟨ζ, hζ, h⟩, ⟨ζ', hζ', h'⟩ => by
    have hs := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.functionFieldMap_bijective.2
    obtain rfl : ζ = ζ' := valuation_eq_of_comap_eq hs ((show _ = _ from h).symm.trans h')
    exact corresponds_injective T i hζ hζ'

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

/-- Distinct labels have distinct valuations of `k(X_0)`. -/
private theorem labelValuation_injective {T : StabilizedSmallKltTail} (C : TerminalChain T) :
    Function.Injective (TerminalChain.labelValuation (C := C)) := by
  intro S S' h
  have hb := (C.junction 0).isBirationalMorphism
  haveI := hb.isDominant
  exact Subtype.ext (primeDivisor_eq_of_valuationOver_eq (C.junction 0).isQFactorial.1
    (C.junction 0).p hb.functionFieldMap_bijective.2 h)

/-- A prime divisor of a model of a terminal chain is the centre of at most one label. -/
private theorem isLabelCentre_injective {T : StabilizedSmallKltTail} (C : TerminalChain T)
    {S S' : C.Label} {x : C.ModelIndex} {P : MMP.Mori.PrimeDivisor (C.model x)}
    (h : C.IsLabelCentre S x P) (h' : C.IsLabelCentre S' x P) : S = S' := by
  rcases x with ⟨i, _ | k⟩
  · obtain ⟨w, hw, hPw⟩ := h
    obtain ⟨w', hw', hPw'⟩ := h'
    obtain rfl : w = w' := hPw.symm.trans hPw'
    exact labelValuation_injective C (corresponds_injective T i hw hw')
  · obtain ⟨w, hw, _, hPw⟩ := h
    obtain ⟨w', hw', _, hPw'⟩ := h'
    have hs :=
      (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.functionFieldMap_bijective.2
    obtain rfl : w = w' := valuation_eq_of_comap_eq hs (hPw.symm.trans hPw')
    exact labelValuation_injective C (corresponds_injective T i hw hw')

/-! ### The order valuation at a surface -/

/-- The weighted monomial ideal of weights `(1, 1)` of `(z₀, z₁)` is the monomial ideal of weight
one of `(z₁, z₀)`. -/
private theorem weightedMonomialIdeal_one_eq_monomialIdeal {R : Type*} [CommRing R]
    (z : Fin 2 → R) (m : ℕ) :
    weightedMonomialIdeal z (fun _ => 1) m = MMP.Resolution.monomialIdeal (z 1) (z 0) 1 m := by
  unfold weightedMonomialIdeal MMP.Resolution.monomialIdeal
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, Fin.sum_univ_two, Fin.prod_univ_two, one_mul]
  constructor
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨β 1, β 0, by omega, mul_comm _ _⟩
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨![j, i], by simp; omega, by simp [mul_comm]⟩

/-- A divisor over a normal variety whose centre has codimension at least two is exceptional. -/
private theorem isExceptional_of_two_le_codimension_center {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety ℂ sX) (D : DivisorOver ℂ sX) (h : 2 ≤ codimension D.center) :
    D.IsExceptional := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI : IsSeparated sX := hX.1.toIsSeparated
  have hsep : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
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

/-- On a terminal pair `(X, B)` with `X` a `ℚ`-factorial complex variety, the local ring at the
generic point of an irreducible closed subset of codimension at most two is regular. -/
private theorem isRegularLocalRing_stalk_genericPoint {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X}
    (h : IsKltTerminalPair sX B) (hQ : IsQFactorial sX) (V : IrreducibleCloseds X)
    (hV : codimension V ≤ 2) :
    IsRegularLocalRing (X.presheaf.stalk V.isIrreducible.genericPoint) := by
  obtain ⟨-, n, K, hK, -⟩ := h.1.1.isPair
  have h3 := (h.isTerminalVariety_and_three_le_closedsCodimension_singularLocus
    (isQCartier_of_isQFactorial sX hQ B) hK (isQCartier_of_isQFactorial sX hQ _)).2
  have hη : V.isIrreducible.genericPoint ∈ smoothLocus sX := by
    by_contra hη
    have hsub : (V : Set X) ⊆ (singularLocus sX : Set X) := by
      rw [← (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).def]
      exact (singularLocus sX).isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη)
    exact absurd ((le_closedsCodimension_iff.mp h3 V hsub).trans hV)
      (by decide : ¬ (3 : ℕ∞) ≤ 2)
  obtain ⟨U, hηU, hU⟩ := mem_smoothLocus_iff.mp hη
  haveI : LocallyOfFiniteType sX := hQ.1.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (U.ι ≫ sX) := inferInstance
  have hreg := (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk
    (U.ι ≫ sX)).mp hU ⟨_, hηU⟩
  exact IsRegularLocalRing.of_ringEquiv (U.stalkIso ⟨_, hηU⟩).commRingCatIsoToRingEquiv

/-- At the generic point of an irreducible closed subset `V` of codimension two along which a
normal complex variety is regular, the `𝔪_V`-adic order is the monomial valuation `v_{x,t;1}`
for some regular system of parameters `(x, t)`. -/
private theorem exists_isWeightedMonomialValuation {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] (hX : IsNormalVariety ℂ sX) (V : IrreducibleCloseds X)
    (hcoh : Order.coheight V.isIrreducible.genericPoint = 2)
    (hreg : IsRegularLocalRing (X.presheaf.stalk V.isIrreducible.genericPoint)) :
    ∃ (x t : X.presheaf.stalk V.isIrreducible.genericPoint) (v : Valuation X.functionField ℤᵐ⁰),
      IsWeightedMonomialValuation sX V x t 1 v := by
  haveI : IsLocallyNoetherian X := hX.1.toLocallyOfFiniteType.isLocallyNoetherian
  haveI := IsRegularLocalRing.isDomain (X.presheaf.stalk V.isIrreducible.genericPoint)
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
  obtain ⟨ν, hν, -⟩ := MMP.Fourfold.SNCWeight.WeightedOrder.exists_valuation_weightedOrder' z
    (fun _ => 1) (K := X.functionField) (fun _ => Nat.one_pos) hz.1 (by rw [hz.2]; simp)
  refine ⟨z 0, z 1, ν, hX, hcodim, hreg, hz', le_rfl, fun f hf => ?_⟩
  obtain ⟨M, hM, hνM⟩ := hν f hf
  refine ⟨M, ?_, hνM⟩
  rw [MMP.Resolution.monomialValuation]
  simpa only [Set.mem_setOf_eq, weightedMonomialIdeal_one_eq_monomialIdeal] using
    (isGreatest_iff_iSup_eq ⟨0, by
      rw [Set.mem_setOf_eq, weightedMonomialIdeal_zero]
      trivial⟩).mp hM

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

/-- The monomial valuation `v_{x,t;1}` of a local equation of a prime divisor `S` at `η_V` is the
multiplicity of `S` along `V`. -/
private theorem multiplicityAlong_eq_neg_log {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] {V : IrreducibleCloseds X} {x t : X.presheaf.stalk V.isIrreducible.genericPoint}
    {v : Valuation X.functionField ℤᵐ⁰} (hw : IsWeightedMonomialValuation sX V x t 1 v)
    (S : MMP.Mori.PrimeDivisor X) {g : X.presheaf.stalk V.isIrreducible.genericPoint}
    (hg0 : g ≠ 0) (hg : IdealSheafData.stalk S.idealSheaf V.isIrreducible.genericPoint =
      Ideal.span {g}) :
    ∃ M : ℕ, S.multiplicityAlong V = M ∧
      -WithZero.log (v (algebraMap _ X.functionField g)) = M := by
  obtain ⟨M, hM, hvM⟩ := hw.2.2.2.2.2 g hg0
  refine ⟨M, ?_, by simp [hvM]⟩
  rw [S.multiplicityAlong_eq_of_stalkIdeal_eq_span V
    (by rwa [Scheme.IdealSheafData.stalkIdeal_eq_stalk]), ← hM,
    monomialValuation_one_eq_iSup hw.2.2.2.1]

/-! ### The bound -/

/-- **The terminality bound.** At an irreducible surface `V` of a model `(Y, Θ)` of a prepared
chain, `∑_P Θ(P) mult_V P < 1`: the order valuation of `𝒪_{Y,η_V}` is exceptional of log
discrepancy `2 - ∑_P Θ(P) mult_V P`, and terminality makes this exceed `1`. -/
private theorem exists_sum_coeff_mul_multiplicityAlong_lt_one {T : StabilizedSmallKltTail}
    (Q : PreparedChain T) (x : Q.ModelIndex) (V : IrreducibleCloseds (Q.chain.model x.1))
    (hV : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2) :
    ∃ μ : MMP.Mori.PrimeDivisor (Q.chain.model x.1) → ℕ,
      (∀ P, P.multiplicityAlong V = μ P) ∧
      ∑ P ∈ (Q.chain.modelBoundary x.1).support,
        (Q.chain.modelBoundary x.1).coeff P * (μ P : ℚ) < 1 := by
  obtain ⟨-, hQF, hdim, hterm, -, -, -⟩ := Q.isKltTerminalPair_modelBoundary x
  have hY : IsNormalVariety ℂ (Q.chain.modelStructure x.1) := hQF.1
  haveI : LocallyOfFiniteType (Q.chain.modelStructure x.1) := hY.1.toLocallyOfFiniteType
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight
    (Q.chain.modelStructure x.1) V.isIrreducible.genericPoint
  rw [(V.isIrreducible.isGenericPoint_genericPoint V.isClosed).def, hV, hdim] at h
  have hcoh : Order.coheight V.isIrreducible.genericPoint = 2 := by
    rw [show (4 : WithBot ℕ∞) = 2 + 2 from rfl, ENat.WithBot.ofNat_add_cancel] at h
    exact WithBot.coe_injective h
  have hcodim : codimension V = 2 := by
    rw [MMP.Flips.codimension_eq_coheight_genericPoint, hcoh]
  have hreg := isRegularLocalRing_stalk_genericPoint hterm hQF V hcodim.le
  obtain ⟨_, t, v, hw⟩ := exists_isWeightedMonomialValuation hY V hcoh hreg
  choose f hf0 hf using fun S : MMP.Mori.PrimeDivisor (Q.chain.model x.1) =>
    exists_stalk_idealSheaf_eq_span (η := V.isIrreducible.genericPoint) S
  choose μ hμ hμv using fun S => multiplicityAlong_eq_neg_log hw S (hf0 S) (hf S)
  obtain ⟨n, D, hDv, hD⟩ := hw.hasLogDiscrepancy hterm.1.1 f (fun S _ => hf S)
  obtain ⟨-, D', -, hvD', hVD'⟩ := hw.isNormalizedDivisorialValuation_and_isCentre
  have hc : D.center = D'.center :=
    MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hY.1 (hDv.trans hvD')
  have h1 := hterm.2 n D _
    (isExceptional_of_two_le_codimension_center hY D (by rw [hc, ← hVD', hcodim])) hD
  refine ⟨μ, hμ, ?_⟩
  simp only [hμv] at h1
  have h2 : ((∑ P ∈ (Q.chain.modelBoundary x.1).support,
      (Q.chain.modelBoundary x.1).coeff P * (μ P : ℚ) : ℚ) : ℝ) < 1 := by
    push_cast
    push_cast at h1
    linarith
  exact_mod_cast h2

/-- **Labels inject into the boundary.** On a model `(Y, Θ)` of a terminal chain with `Θ ≥ 0`,
if each label's value `m_h` is the value `μ` of its centre, then `∑_h m_h b_h` is bounded by
`∑_P Θ(P) μ(P)`: a label with `b_h ≠ 0` has a prime-divisor centre in the support of `Θ`, and
distinct labels have distinct centres. -/
private theorem finsum_mul_le_sum_coeff_mul {T : StabilizedSmallKltTail} (C : TerminalChain T)
    (x : C.ModelIndex) (hΘ : 0 ≤ C.modelBoundary x) (μ : MMP.Mori.PrimeDivisor (C.model x) → ℕ)
    (m : C.Label → ℕ) (b : C.Label → ℚ)
    (hm : ∀ S P, C.IsLabelCentre S x P → m S = μ P) (hb : ∀ S, C.IsLabelCoefficient S x (b S)) :
    ∑ᶠ S, (m S : ℚ) * b S ≤
      ∑ P ∈ (C.modelBoundary x).support, (C.modelBoundary x).coeff P * (μ P : ℚ) := by
  classical
  haveI := C.finite_label
  haveI := Fintype.ofFinite C.Label
  choose c hcP hcb using fun S : {S : C.Label // b S ≠ 0} =>
    (hb S.1).resolve_right fun h => S.2 h.2
  have hcinj : Function.Injective c := fun S S' h =>
    Subtype.ext (isLabelCentre_injective C (hcP S) (h ▸ hcP S'))
  rw [finsum_eq_sum_of_fintype]
  calc ∑ S, (m S : ℚ) * b S = ∑ S : {S : C.Label // b S ≠ 0}, (m S.1 : ℚ) * b S.1 := by
        rw [← Finset.sum_filter_of_ne (p := fun S => b S ≠ 0)
          fun S _ h => right_ne_zero_of_mul h]
        exact Finset.sum_subtype _ (by simp) _
    _ = ∑ P ∈ Finset.univ.image c, (C.modelBoundary x).coeff P * (μ P : ℚ) := by
        rw [Finset.sum_image fun S _ S' _ h => hcinj h]
        exact Finset.sum_congr rfl fun S _ => by rw [hcb S, hm S.1 _ (hcP S), mul_comm]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (fun P hP => by
          obtain ⟨S, -, rfl⟩ := Finset.mem_image.mp hP
          exact Finsupp.mem_support_iff.mpr ((hcb S).trans_ne S.2))
        fun P _ _ => mul_nonneg (hΘ P) (Nat.cast_nonneg _)

end MMP.OAI4C2MultiplicitySumBound

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

/-- On a model `(Y, Θ)` of a prepared chain, at an irreducible surface `V ⊆ Y`, the sum over the
labels `S_h` of `m_h b_h` is less than `1`, where `b_h` is the label coefficient
(`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelCoefficient`) and `m_h` the
multiplicity (`MMP.Mori.PrimeDivisor.multiplicityAlong`) of the centre `S_h^Y` along `V`, that
is, at the generic point `η_V`. -/
@[mmp "lem_oai4_c2_multiplicity_sum_bound"]
public theorem finsum_multiplicityAlong_mul_lt_one {T : StabilizedSmallKltTail}
    (Q : PreparedChain T) (x : Q.ModelIndex) (V : IrreducibleCloseds (Q.chain.model x.1))
    (hV : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2)
    (m : Q.chain.Label → ℕ) (b : Q.chain.Label → ℚ)
    (hm : ∀ (S : Q.chain.Label) (P : MMP.Mori.PrimeDivisor (Q.chain.model x.1)),
      Q.chain.IsLabelCentre S x.1 P → P.multiplicityAlong V = m S)
    (hb : ∀ S : Q.chain.Label, Q.chain.IsLabelCoefficient S x.1 (b S)) :
    ∑ᶠ S, (m S : ℚ) * b S < 1 := by
  obtain ⟨μ, hμ, hlt⟩ :=
    MMP.OAI4C2MultiplicitySumBound.exists_sum_coeff_mul_multiplicityAlong_lt_one Q x V hV
  exact (MMP.OAI4C2MultiplicitySumBound.finsum_mul_le_sum_coeff_mul Q.chain x.1
    (Q.isKltTerminalPair_modelBoundary x).2.2.2.2.1 μ m b
    (fun S P hP => by exact_mod_cast (hm S P hP).symm.trans (hμ P)) hb).trans_lt hlt

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain
