module

public import MMP.AlgebraicGeometry.MMP.Fourfold.BadSurface
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.PreparedChainTerminal
import MMP.AlgebraicGeometry.Singularities.Terminal.PairSmoothCodimTwo
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.BranchMultiplicity
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.PrimeDivisorPersistence

/-!
# The first default error at a surface

Let `(Y, Θ)`, `Θ = ∑_h b_h S_h`, be a model of a prepared chain of fourfolds at the admissible
scale `N`, let `V ⊆ Y` be an irreducible surface, and write `m_h` for the multiplicity of the
label `S_h` at the generic point `η_V`, `r_{V,h}` for its branch number at `V` and `r_V^var` for
the varying branch number. With `w(u) = ⌈N max{u, 0}⌉` the weight,
`w(∑_h m_h b_h) ≥ ∑_h r_{V,h} w(b_h) - max{r_V^var - 1, 0}`.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.sum_branchNumber_mul_difficultyWeight_le`:
  the inequality above.

## Implementation notes

The coefficients `b_h`, multiplicities `m_h`, branch numbers `r_{V,h}` and the varying branch
number are given as values satisfying the predicates
`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelCoefficient`,
`MMP.Mori.PrimeDivisor.multiplicityAlong` of the label centre,
`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelBranchNumber` and
`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsVaryingBranchNumber`. The inequality is
stated in `ℤ`. The labels are finitely many, so `∑ᶠ` is the finite sum.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MMP.Mori MMP.Fourfold MMP.Fourfold.StabilizedSmallKltTail

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

/-! ### The elementary ceiling inequality -/

/-- If `y_i ∈ ℤ` whenever `¬ p i`, then `∑ r_i ⌈y_i⌉ - max{∑_{p i} r_i - 1, 0} ≤ ⌈∑ r_i y_i⌉`. -/
private theorem sum_mul_ceil_sub_le_ceil_sum {ι : Type*} [Fintype ι] (p : ι → Prop)
    [DecidablePred p] (r : ι → ℕ) (y : ι → ℝ) (hy : ∀ i, ¬ p i → ∃ z : ℤ, y i = z) :
    ∑ i, (r i : ℤ) * ⌈y i⌉ - max ((∑ i with p i, (r i : ℤ)) - 1) 0 ≤
      ⌈∑ i, (r i : ℝ) * y i⌉ := by
  set R : ℤ := ∑ i with p i, (r i : ℤ)
  have hterm : ∀ i, (((r i : ℤ) * ⌈y i⌉ : ℤ) : ℝ) ≤
      (r i : ℝ) * y i + if p i then (r i : ℝ) else 0 := fun i => by
    split_ifs with h
    · have := Int.ceil_lt_add_one (y i)
      have : (0 : ℝ) ≤ r i := Nat.cast_nonneg _
      push_cast
      nlinarith
    · obtain ⟨z, hz⟩ := hy i h
      simp [hz]
  have hR : (R : ℝ) = ∑ i, if p i then (r i : ℝ) else 0 := by
    simp [R, Finset.sum_filter]
  have hA : ((∑ i, (r i : ℤ) * ⌈y i⌉ : ℤ) : ℝ) ≤ ∑ i, (r i : ℝ) * y i + R := by
    rw [hR, ← Finset.sum_add_distrib]
    push_cast
    exact Finset.sum_le_sum fun i _ => by exact_mod_cast hterm i
  rcases (show 0 ≤ R from Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _).eq_or_lt with h0 | hpos
  · rw [← h0, Int.cast_zero, add_zero] at hA
    have := Int.cast_le.mp (hA.trans (Int.le_ceil _))
    omega
  · obtain ⟨i, hpi, hri⟩ : ∃ i, p i ∧ 0 < r i := by
      by_contra hne
      push Not at hne
      exact hpos.ne' (Finset.sum_eq_zero fun i hi =>
        by exact_mod_cast Nat.le_zero.mp (hne i (Finset.mem_filter.mp hi).2))
    have hlt : ((∑ i, (r i : ℤ) * ⌈y i⌉ : ℤ) : ℝ) < ∑ i, (r i : ℝ) * y i + R := by
      rw [hR, ← Finset.sum_add_distrib]
      push_cast
      refine Finset.sum_lt_sum (fun i _ => by exact_mod_cast hterm i)
        ⟨i, Finset.mem_univ _, ?_⟩
      rw [if_pos hpi]
      have := Int.ceil_lt_add_one (y i)
      have : (0 : ℝ) < r i := by exact_mod_cast hri
      nlinarith
    have : ∑ i, (r i : ℤ) * ⌈y i⌉ - R < ⌈∑ i, (r i : ℝ) * y i⌉ :=
      Int.lt_ceil.mpr (by push_cast at hlt ⊢; linarith)
    omega

/-- If `r_i ≤ m_i`, `b_i ≥ 0`, and `N b_i ∈ ℤ` whenever `¬ p i`, then
`∑ r_i w(b_i) - max{∑_{p i} r_i - 1, 0} ≤ w(∑ m_i b_i)` for `w = difficultyWeight N`. -/
private theorem sum_mul_difficultyWeight_sub_le {ι : Type*} [Fintype ι] (p : ι → Prop)
    [DecidablePred p] (N : ℕ) {r m : ι → ℕ} {b : ι → ℝ} (hrm : ∀ i, r i ≤ m i)
    (hb : ∀ i, 0 ≤ b i) (hfix : ∀ i, ¬ p i → ∃ z : ℤ, (N : ℝ) * b i = z) :
    ∑ i, (r i : ℤ) * difficultyWeight N (b i) - max ((∑ i with p i, (r i : ℤ)) - 1) 0 ≤
      difficultyWeight N (∑ i, (m i : ℝ) * b i) := by
  have hw : ∀ i, (difficultyWeight N (b i) : ℤ) = ⌈(N : ℝ) * b i⌉ := fun i => by
    rw [natCast_difficultyWeight, max_eq_left (hb i)]
  simp only [hw]
  calc _ ≤ ⌈∑ i, (r i : ℝ) * ((N : ℝ) * b i)⌉ := sum_mul_ceil_sub_le_ceil_sum p r _ hfix
    _ = difficultyWeight N (∑ i, (r i : ℝ) * b i) := by
        rw [natCast_difficultyWeight,
          max_eq_left (Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hb i)),
          Finset.mul_sum]
        simp_rw [mul_left_comm]
    _ ≤ _ := Int.ofNat_le.mpr (difficultyWeight_mono N (Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hrm i)) (hb i)))

/-! ### Regularity at the generic point of a surface -/

/-- In `WithBot ℕ∞`, `2 + c = 4` forces `c = 2`. -/
private theorem eq_two_of_two_add_eq_four {c : ℕ∞}
    (h : (2 : WithBot ℕ∞) + (c : WithBot ℕ∞) = 4) : c = 2 := by
  have h' : (2 + c : ℕ∞) = 4 := WithBot.coe_injective (by rw [WithBot.coe_add]; exact h)
  induction c using ENat.recTopCoe with
  | top => simp at h'
  | coe n =>
    have : 2 + n = 4 := by exact_mod_cast h'
    norm_cast
    omega

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
    have : (3 : ℕ∞) ≤ 2 := ((le_closedsCodimension_iff.mp h3) V hsub).trans hV
    exact absurd this (by decide)
  obtain ⟨U, hηU, hU⟩ := mem_smoothLocus_iff.mp hη
  haveI : LocallyOfFiniteType sX := hQ.1.1.toLocallyOfFiniteType
  have hreg := (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk
    (U.ι ≫ sX)).mp hU ⟨_, hηU⟩
  exact IsRegularLocalRing.of_ringEquiv (U.stalkIso ⟨_, hηU⟩).commRingCatIsoToRingEquiv

/-- **Branches are bounded by multiplicities.** At an irreducible surface `V` of a model of a
prepared chain, the branch number `r_{V,h}` of a label is at most its multiplicity `m_h`
at `η_V`. -/
private theorem branchNumber_le_multiplicity {T : StabilizedSmallKltTail} (Q : PreparedChain T)
    (x : Q.ModelIndex) (V : IrreducibleCloseds (Q.chain.model x.1))
    (hV : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2) (S : Q.chain.Label) {m r : ℕ}
    (hm : ∀ P : MMP.Mori.PrimeDivisor (Q.chain.model x.1),
      Q.chain.IsLabelCentre S x.1 P → P.multiplicityAlong V = m)
    (hr : Q.chain.IsLabelBranchNumber S x.1 V r) : r ≤ m := by
  rcases hr with ⟨P, hP, rfl⟩ | ⟨-, rfl⟩
  · obtain ⟨-, hQF, hdim, hterm, -⟩ := Q.isKltTerminalPair_modelBoundary x
    have hY : IsNormalVariety ℂ (Q.chain.modelStructure x.1) := hQF.1
    haveI : LocallyOfFiniteType (Q.chain.modelStructure x.1) := hY.1.toLocallyOfFiniteType
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight
      (Q.chain.modelStructure x.1) V.isIrreducible.genericPoint
    rw [(V.isIrreducible.isGenericPoint_genericPoint V.isClosed).def, hV, hdim] at h
    have hcoh : Order.coheight V.isIrreducible.genericPoint = 2 := eq_two_of_two_add_eq_four h
    have hcodim : codimension V = 2 := by
      rw [MMP.Flips.codimension_eq_coheight_genericPoint, hcoh]
    have hreg := isRegularLocalRing_stalk_genericPoint hterm hQF V hcodim.le
    have hring : ringKrullDim ((Q.chain.model x.1).presheaf.stalk
        V.isIrreducible.genericPoint) = 2 := by
      rw [ringKrullDim_stalk_eq_coheight, hcoh]
      rfl
    have h := encard_branches_le_multiplicityAlong (Q.chain.modelStructure x.1) V hreg hring P
    rw [hm P hP] at h
    rw [branchNumber, Set.ncard_def]
    exact_mod_cast (ENat.coe_toNat_le_self _).trans h
  · exact Nat.zero_le _

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

namespace MMP.Fourfold.StabilizedSmallKltTail.TerminalChain

/-! ### Labels and their centres -/

/-- A label has at most one centre on a model. -/
private theorem isLabelCentre_unique {T : StabilizedSmallKltTail} {C : TerminalChain T}
    {x : C.ModelIndex} {S : C.Label} {P P' : MMP.Mori.PrimeDivisor (C.model x)}
    (hP : C.IsLabelCentre S x P) (hP' : C.IsLabelCentre S x P') : P = P' := by
  rcases x with ⟨i, _ | k⟩ <;> exact IsPrimeDivisorCentre.unique hP hP'

/-- A label has exactly one coefficient on a model. -/
private theorem isLabelCoefficient_unique {T : StabilizedSmallKltTail} {C : TerminalChain T}
    {x : C.ModelIndex} {S : C.Label} {b b' : ℚ} (h : C.IsLabelCoefficient S x b)
    (h' : C.IsLabelCoefficient S x b') : b = b' := by
  rcases h with ⟨P, hP, rfl⟩ | ⟨hn, rfl⟩ <;> rcases h' with ⟨P', hP', rfl⟩ | ⟨hn', rfl⟩
  · rw [isLabelCentre_unique hP hP']
  · exact absurd hP (hn' P)
  · exact absurd hP' (hn P')
  · rfl

/-- A label has exactly one branch number at an irreducible closed subset of a model. -/
private theorem isLabelBranchNumber_unique {T : StabilizedSmallKltTail} {C : TerminalChain T}
    {x : C.ModelIndex} {S : C.Label} {V : IrreducibleCloseds (C.model x)} {r r' : ℕ}
    (h : C.IsLabelBranchNumber S x V r) (h' : C.IsLabelBranchNumber S x V r') : r = r' := by
  rcases h with ⟨P, hP, rfl⟩ | ⟨hn, rfl⟩ <;> rcases h' with ⟨P', hP', rfl⟩ | ⟨hn', rfl⟩
  · rw [isLabelCentre_unique hP hP']
  · exact absurd hP (hn' P)
  · exact absurd hP' (hn P')
  · rfl

/-- The varying branch number is the sum of the branch numbers of the varying labels. -/
private theorem IsVaryingBranchNumber.eq_sum {T : StabilizedSmallKltTail} {C : TerminalChain T}
    [Fintype C.Label] [DecidablePred C.IsVaryingLabel] {x : C.ModelIndex}
    {V : IrreducibleCloseds (C.model x)} {r : C.Label → ℕ} {rv : ℕ}
    (hr : ∀ S, C.IsLabelBranchNumber S x V (r S)) (hrv : C.IsVaryingBranchNumber x V rv) :
    rv = ∑ S with C.IsVaryingLabel S, r S := by
  obtain ⟨r', hr', rfl⟩ := hrv
  rw [finsum_eq_sum_of_fintype]
  simp only [finsum_eq_if]
  rw [← Finset.sum_filter]
  exact Finset.sum_congr rfl fun S hS =>
    isLabelBranchNumber_unique (hr' S (Finset.mem_filter.mp hS).2) (hr S)

end MMP.Fourfold.StabilizedSmallKltTail.TerminalChain

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

/-- On a model of a prepared chain, `N b_h ∈ ℤ` for the coefficient `b_h` of a fixed label. -/
private theorem exists_scale_mul_eq_intCast_of_isFixedLabel {T : StabilizedSmallKltTail}
    (Q : PreparedChain T) (x : Q.ModelIndex) {S : Q.chain.Label} (hS : Q.chain.IsFixedLabel S)
    {b : ℚ} (hb : Q.chain.IsLabelCoefficient S x.1 b) : ∃ z : ℤ, (Q.scale : ℚ) * b = z := by
  obtain ⟨c, hc⟩ := Q.isLabelCoefficient_const_of_isFixedLabel S hS
  obtain ⟨c', n, hc'⟩ := hS
  obtain ⟨z, hz⟩ := Q.isAdmissibleScale.exists_intCast_eq_of_eventually hc'
  have h1 : c' = c :=
    TerminalChain.isLabelCoefficient_unique (hc' (max n Q.start) (le_max_left _ _))
      (hc ⟨max n Q.start, none⟩ (le_max_right _ _))
  have h2 : b = c := TerminalChain.isLabelCoefficient_unique hb (hc x.1 x.2)
  exact ⟨z, by rw [h2, ← h1, hz]⟩

/-- On a model `(Y, Θ)` of a prepared chain, at an irreducible surface `V ⊆ Y`,
`w(∑_h m_h b_h) ≥ ∑_h r_{V,h} w(b_h) - max{r_V^var - 1, 0}`, where `w` is
`MMP.Fourfold.difficultyWeight` at the chain's scale, `b_h` the label coefficient, `m_h` the
multiplicity (`MMP.Mori.PrimeDivisor.multiplicityAlong`) of the centre `S_h^Y` along `V`,
`r_{V,h}` the branch number and `r_V^var` the varying branch number at `V`. -/
@[mmp "lem_oai4_c2_first_default_error"]
public theorem sum_branchNumber_mul_difficultyWeight_le {T : StabilizedSmallKltTail}
    (Q : PreparedChain T) (x : Q.ModelIndex) (V : IrreducibleCloseds (Q.chain.model x.1))
    (hV : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2)
    (m : Q.chain.Label → ℕ) (b : Q.chain.Label → ℚ) (r : Q.chain.Label → ℕ) (rv : ℕ)
    (hm : ∀ (S : Q.chain.Label) (P : MMP.Mori.PrimeDivisor (Q.chain.model x.1)),
      Q.chain.IsLabelCentre S x.1 P → P.multiplicityAlong V = m S)
    (hb : ∀ S : Q.chain.Label, Q.chain.IsLabelCoefficient S x.1 (b S))
    (hr : ∀ S : Q.chain.Label, Q.chain.IsLabelBranchNumber S x.1 V (r S))
    (hrv : Q.chain.IsVaryingBranchNumber x.1 V rv) :
    ∑ᶠ S, (r S : ℤ) * difficultyWeight Q.scale (b S) - max ((rv : ℤ) - 1) 0 ≤
      difficultyWeight Q.scale (∑ᶠ S, (m S : ℝ) * b S) := by
  classical
  haveI := Q.chain.finite_label
  haveI := Fintype.ofFinite Q.chain.Label
  rw [hrv.eq_sum hr, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  push_cast
  refine sum_mul_difficultyWeight_sub_le Q.chain.IsVaryingLabel Q.scale
    (fun S => branchNumber_le_multiplicity Q x V hV S (hm S) (hr S))
    (fun S => by exact_mod_cast ((Q.isKltTerminalPair_modelBoundary x).2.2.2.2.2.2 S _ (hb S)).1)
    fun S hS => ?_
  obtain ⟨z, hz⟩ := exists_scale_mul_eq_intCast_of_isFixedLabel Q x
    ((Q.chain.not_isVaryingLabel_iff S).mp hS) (hb S)
  exact ⟨z, by exact_mod_cast hz⟩

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain
