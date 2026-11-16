module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainDifficulty
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.DefaultWeightEventuallyConst
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.VaryingLabelCodimension
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.PrimeDivisorPersistence
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.Monotonicity

/-!
# Existence of prepared chains

Let `(p_i, Θ_i)_{i ≥ 0}` be a terminal chain over a stabilized small klt tail
`(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` of fourfolds. Fix an admissible scale `N`. The coefficient
of a fixed label is eventually constant, and the default echo weights `d_h` are eventually
constant on all models; a varying label has positive coefficient at every junction, and its
image in `X_i` is eventually of dimension at most one. Hence some tail of the chain, starting at
a junction `Y_{i₀}`, is a prepared chain.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.exists_preparedChain_chain_eq`: every
  terminal chain `C` is the underlying chain of a prepared chain, i.e. it has a tail which is a
  prepared chain.

## Implementation notes

A prepared chain `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain` is recorded by its terminal
chain, the index `i₀` of its first junction and its admissible scale; a tail of `C` which is a
prepared chain is therefore a prepared chain `Q` with `Q.chain = C`.
-/

@[expose] public section

section

namespace Proof_lem_oai4_c2_prepared_chain_exists

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology MMP.Fourfold
  MMP.Fourfold.StabilizedSmallKltTail MMP.Fourfold.StabilizedSmallKltTail.TerminalChain

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A finite union of closed sets of dimension at most `n` has dimension at most `n`. -/
private theorem topologicalKrullDim_iUnion_le {X : Type*} [TopologicalSpace X] {ι : Type*}
    [Finite ι] {F : ι → Set X} (hF : ∀ j, IsClosed (F j)) {n : WithBot ℕ∞}
    (h : ∀ j, topologicalKrullDim (F j) ≤ n) : topologicalKrullDim (⋃ j, F j) ≤ n := by
  classical
  have := Fintype.ofFinite ι
  refine MMP.Flips.topologicalKrullDim_le_of_forall_mem_irreducibleComponents fun Z hZ => ?_
  have hirr : IsIrreducible (Subtype.val '' Z) := hZ.1.image _ continuous_subtype_val.continuousOn
  obtain ⟨W, hW, hsub⟩ := (isIrreducible_iff_sUnion_isClosed.mp hirr) (Finset.univ.image F)
    (by simpa only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff] using hF)
    (by
      rintro _ ⟨z, -, rfl⟩
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp z.2
      exact Set.mem_sUnion.mpr ⟨F j, by simp, hj⟩)
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hW
  have hind : IsInducing (fun z : Z => (z.1.1 : X)) :=
    IsInducing.subtypeVal.comp IsInducing.subtypeVal
  exact ((hind.codRestrict (s := F j) fun z => hsub ⟨z.1, z.2, rfl⟩).topologicalKrullDim_le).trans
    (h j)

/-- If `a + c = 4` with `c ≥ 3`, then `a ≤ 1`. -/
private theorem le_one_of_add_eq_four {a : WithBot ℕ∞} {c : ℕ∞} (h : a + c = 4) (hc : 3 ≤ c) :
    a ≤ 1 := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    rw [← WithBot.coe_add] at h
    have h' : a + c = 4 := WithBot.coe_injective h
    have : a + 3 ≤ 4 := h' ▸ add_le_add_right hc a
    induction a using ENat.recTopCoe with
    | top => simp at this
    | coe a =>
      have : a + 3 ≤ 4 := by exact_mod_cast this
      exact_mod_cast (show a ≤ 1 by omega)

/-- `N q` is an integer when the denominator of `q` divides `N`. -/
private theorem exists_intCast_eq_mul_of_den_dvd {q : ℚ} {N : ℕ} (h : q.den ∣ N) :
    ∃ z : ℤ, (N : ℚ) * q = z := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨k * q.num, ?_⟩
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

variable {T : StabilizedSmallKltTail} (C : TerminalChain T)

/-- The model following `x` lies over the same junction, or is the next junction. -/
private theorem next_eq (x : C.ModelIndex) :
    (C.next x).1 = x.1 ∨ C.next x = ⟨x.1 + 1, none⟩ := by
  rcases x with ⟨i, _ | k⟩ <;> simp only [next] <;> split_ifs <;> simp

/-- The junction index of the models is monotone along the chain. -/
private theorem monotone_modelIndexSeq_fst : Monotone fun n => (C.modelIndexSeq n).1 := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [modelIndexSeq_succ]
  rcases next_eq C (C.modelIndexSeq n) with h | h <;> rw [h] <;> simp

/-- Every model comes after the junction it lies over. -/
private theorem exists_le_modelIndexSeq_eq (n : ℕ) :
    ∃ m ≤ n, C.modelIndexSeq m = ⟨(C.modelIndexSeq n).1, none⟩ := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
    rw [modelIndexSeq_succ]
    rcases next_eq C (C.modelIndexSeq n) with h | h
    · obtain ⟨m, hm, hm'⟩ := ih
      exact ⟨m, by omega, by rwa [h]⟩
    · exact ⟨n + 1, le_rfl, by rw [modelIndexSeq_succ, h]⟩

/-- Every model of the chain occurs in the list of its models. -/
private theorem exists_modelIndexSeq_eq (x : C.ModelIndex) : ∃ n, C.modelIndexSeq n = x := by
  have hbridge : ∀ i n, C.modelIndexSeq n = ⟨i, none⟩ → ∀ k : Fin (C.bridge i).P.m,
      C.modelIndexSeq (n + 1 + k.1) = ⟨i, some k⟩ := by
    intro i n hn k
    obtain ⟨k, hk⟩ := k
    induction k with
    | zero =>
      rw [Nat.add_zero, modelIndexSeq_succ, hn]
      simp only [next, hk, ↓reduceDIte]
    | succ k ih =>
      rw [← Nat.add_assoc, modelIndexSeq_succ, ih (by omega)]
      simp only [next, hk, ↓reduceDIte]
  have hjunction : ∀ i, ∃ n, C.modelIndexSeq n = ⟨i, none⟩ := by
    intro i
    induction i with
    | zero => exact ⟨0, rfl⟩
    | succ i ih =>
      obtain ⟨n, hn⟩ := ih
      by_cases h : 0 < (C.bridge i).P.m
      · refine ⟨n + 1 + ((C.bridge i).P.m - 1) + 1, ?_⟩
        rw [modelIndexSeq_succ, hbridge i n hn ⟨(C.bridge i).P.m - 1, by omega⟩]
        have h' : ¬ (C.bridge i).P.m - 1 + 1 < (C.bridge i).P.m := by omega
        simp only [next, h', ↓reduceDIte]
      · refine ⟨n + 1, ?_⟩
        rw [modelIndexSeq_succ, hn]
        simp only [next, h, ↓reduceDIte]
  rcases x with ⟨i, _ | k⟩
  · exact hjunction i
  · obtain ⟨n, hn⟩ := hjunction i
    exact ⟨_, hbridge i n hn k⟩

/-- On every model, the centres of the labels are given by an equivalence with the prime
divisors of `Y_0`. -/
private theorem exists_equiv_isLabelCentre (x : C.ModelIndex) :
    ∃ e : MMP.Mori.PrimeDivisor (C.junction 0).Y ≃ MMP.Mori.PrimeDivisor (C.model x),
      ∀ (S : C.Label) P, C.IsLabelCentre S x P ↔ e S.1 = P := by
  have he := TerminalChain.isPrimeDivisorCentre_iff_primeDivisorEquivModel_eq C x
  rcases x with ⟨i, _ | k⟩ <;> exact ⟨_, fun S P => he S.1 P⟩

/-- The coefficient of a label is nonincreasing along the models of the chain. -/
private theorem coeff_le_of_le {S : C.Label} {n m : ℕ} (hnm : n ≤ m)
    {Q : MMP.Mori.PrimeDivisor (C.model (C.modelIndexSeq n))}
    {Q' : MMP.Mori.PrimeDivisor (C.model (C.modelIndexSeq m))}
    (hQ : C.IsLabelCentre S _ Q) (hQ' : C.IsLabelCentre S _ Q') :
    (C.modelBoundary (C.modelIndexSeq m)).coeff Q' ≤
      (C.modelBoundary (C.modelIndexSeq n)).coeff Q := by
  apply C.coeff_modelBoundary_le_of_le S.1 hnm Q Q'
  · revert Q hQ
    generalize C.modelIndexSeq n = x
    rintro Q hQ
    rcases x with ⟨i, _ | k⟩ <;> exact hQ
  · revert Q' hQ'
    generalize C.modelIndexSeq m = x
    rintro Q' hQ'
    rcases x with ⟨i, _ | k⟩ <;> exact hQ'

/-- At a junction `Y_i` from which every varying label has centre on `X_i` of codimension at
least three, the image `p_i(P)` of the centre `P` of a varying label is closed of dimension at
most one. -/
private theorem isClosed_and_topologicalKrullDim_image_le {i : ℕ} {S : C.Label}
    {P : MMP.Mori.PrimeDivisor (C.junction i).Y} (hP : C.IsLabelCentre S ⟨i, none⟩ P)
    (h3 : ∀ w : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)),
        T.Corresponds i (labelValuation S) w →
      ∀ Z : IrreducibleCloseds (T.X i), MMP.Intersection.IsCentre ℂ (T.sX i) w Z →
        3 ≤ codimension Z) :
    IsClosed ((C.junction i).p '' P.support) ∧
      topologicalKrullDim ((C.junction i).p '' P.support) ≤ 1 := by
  obtain ⟨w, hw, hPw⟩ := hP
  have hproper := isProper_of_isProjectiveMorphism _ (C.junction i).isProjectiveMorphism
  let D : MMP.Mori.DivisorOver ℂ (T.sX i) :=
    ⟨(C.junction i).Y, (C.junction i).p, (C.junction i).isQFactorial.1,
      (C.junction i).isBirationalMorphism, P⟩
  have hclosed : IsClosed ((C.junction i).p '' P.support) :=
    (C.junction i).p.isClosedMap _ (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure P]
      exact isClosed_closure)
  have hcentre : (D.center : Set (T.X i)) = (C.junction i).p '' P.support := by
    rw [D.coe_center, hclosed.closure_eq]
  set y := D.f D.E.genericPoint
  have hDy : D.center = IrreducibleCloseds.closureSingleton y :=
    IrreducibleCloseds.ext D.center_eq_closure_genericPoint
  have hcodim : 3 ≤ Order.coheight y := by
    rw [← MMP.Flips.codimension_closureSingleton, ← hDy]
    exact h3 w hw _ ⟨D, hproper, hPw.symm, rfl⟩
  have hlft := (C.junction i).isProjectiveVariety_base.1.toLocallyOfFiniteType
  have hdim := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (T.sX i) y
  rw [(C.junction i).dim_base] at hdim
  refine ⟨hclosed, ?_⟩
  rw [← hcentre, D.center_eq_closure_genericPoint]
  exact le_one_of_add_eq_four hdim hcodim

/-- On every model, a label has a centre `P` whose boundary coefficient is its only label
coefficient. -/
private theorem exists_isLabelCentre_and_isLabelCoefficient_iff (S : C.Label)
    (x : C.ModelIndex) : ∃ P, C.IsLabelCentre S x P ∧
      ∀ b, C.IsLabelCoefficient S x b ↔ b = (C.modelBoundary x).coeff P := by
  obtain ⟨e, he⟩ := exists_equiv_isLabelCentre C x
  refine ⟨e S.1, (he S _).mpr rfl, fun b => ⟨?_, fun h => h ▸
    isLabelCoefficient_of_isLabelCentre ((he S _).mpr rfl)⟩⟩
  rintro (⟨P, hP, rfl⟩ | ⟨h, -⟩)
  · rw [(he S P).mp hP]
  · exact (h _ ((he S _).mpr rfl)).elim

/-- A label has only one coefficient on each model. -/
private theorem isLabelCoefficient_unique {S : C.Label} {x : C.ModelIndex} {b b' : ℚ}
    (hb : C.IsLabelCoefficient S x b) (hb' : C.IsLabelCoefficient S x b') : b = b' := by
  obtain ⟨P, -, h⟩ := exists_isLabelCentre_and_isLabelCoefficient_iff C S x
  exact ((h b).mp hb).trans ((h b').mp hb').symm

/-- The label coefficient of a label is nonincreasing along the models of the chain. -/
private theorem isLabelCoefficient_antitone {S : C.Label} {n m : ℕ} (hnm : n ≤ m) {b b' : ℚ}
    (hb : C.IsLabelCoefficient S (C.modelIndexSeq n) b)
    (hb' : C.IsLabelCoefficient S (C.modelIndexSeq m) b') : b' ≤ b := by
  obtain ⟨P, hP, h⟩ := exists_isLabelCentre_and_isLabelCoefficient_iff C S (C.modelIndexSeq n)
  obtain ⟨P', hP', h'⟩ := exists_isLabelCentre_and_isLabelCoefficient_iff C S (C.modelIndexSeq m)
  rw [(h b).mp hb, (h' b').mp hb']
  exact coeff_le_of_le C hnm hP hP'

/-- A label with coefficient `c` at every junction from `Y_n` on has coefficient `c` at every
model from `Y_n` on: a model of the `i`-th bridge lies between the junctions `Y_i` and
`Y_{i+1}`, and the coefficients are nonincreasing along the models. -/
private theorem isLabelCoefficient_of_forall_ge {S : C.Label} {c : ℚ} {n : ℕ}
    (h : ∀ i ≥ n, C.IsJunctionLabelCoefficient S i c) {x : C.ModelIndex} (hx : n ≤ x.1) :
    C.IsLabelCoefficient S x c := by
  obtain ⟨m, rfl⟩ := exists_modelIndexSeq_eq C x
  obtain ⟨m₀, hm₀, hm₀'⟩ := exists_le_modelIndexSeq_eq C m
  obtain ⟨m₁, hm₁⟩ := exists_modelIndexSeq_eq C ⟨(C.modelIndexSeq m).1 + 1, none⟩
  have hmm₁ : m ≤ m₁ := by
    by_contra hlt
    have := monotone_modelIndexSeq_fst C (le_of_not_ge hlt)
    simp only [hm₁] at this
    omega
  have h₀ : C.IsLabelCoefficient S (C.modelIndexSeq m₀) c := by
    rw [hm₀']
    exact h _ hx
  have h₁ : C.IsLabelCoefficient S (C.modelIndexSeq m₁) c := by
    rw [hm₁]
    exact h _ (hx.trans (Nat.le_succ _))
  obtain ⟨b, hb⟩ := exists_isLabelCoefficient S (C.modelIndexSeq m)
  rwa [le_antisymm (isLabelCoefficient_antitone C hm₀ h₀ hb)
    (isLabelCoefficient_antitone C hmm₁ hb h₁)] at hb

/-- The product of the denominators of the coefficients of `B_0` and of the eventual
coefficients `c S` of the fixed labels is an admissible scale. -/
private theorem isAdmissibleScale_prod_den [Fintype C.Label] {c : C.Label → ℚ}
    (hc : ∀ S, C.IsFixedLabel S → ∃ n, ∀ i ≥ n, C.IsJunctionLabelCoefficient S i (c S)) :
    C.IsAdmissibleScale ((∏ P ∈ (T.B 0).support, ((T.B 0).coeff P).den) * ∏ S, (c S).den) := by
  refine ⟨Nat.mul_pos (Finset.prod_pos fun _ _ => Rat.den_pos _)
    (Finset.prod_pos fun _ _ => Rat.den_pos _), fun P => ?_, fun S c' ⟨n', hn'⟩ => ?_⟩
  · by_cases hP : (T.B 0).coeff P = 0
    · exact ⟨0, by simp [hP]⟩
    · exact exists_intCast_eq_mul_of_den_dvd (Dvd.dvd.mul_right
        (Finset.dvd_prod_of_mem _ (Finsupp.mem_support_iff.mpr hP)) _)
  · obtain ⟨n, hn⟩ := hc S ⟨c', n', hn'⟩
    rw [isLabelCoefficient_unique C (hn' _ (le_max_left n' n)) (hn _ (le_max_right n' n))]
    exact exists_intCast_eq_mul_of_den_dvd (Dvd.dvd.mul_left
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ S)) _)

/-- At a junction `Y_i` from which every varying label has centre on `X_i` of codimension at
least three, `p_i` maps the union of the centres of the varying labels onto a closed set of
dimension at most one. -/
private theorem isClosed_and_topologicalKrullDim_image_varyingLabels_le {i : ℕ}
    (h3 : ∀ S : C.Label, C.IsVaryingLabel S →
      ∀ w : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)),
        T.Corresponds i (labelValuation S) w →
      ∀ Z : IrreducibleCloseds (T.X i), MMP.Intersection.IsCentre ℂ (T.sX i) w Z →
        3 ≤ codimension Z) :
    IsClosed ((C.junction i).p ''
        {y : (C.junction i).Y | ∃ S : C.Label, C.IsVaryingLabel S ∧
          ∃ P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩),
            C.IsLabelCentre S ⟨i, none⟩ P ∧ y ∈ P.support}) ∧
      topologicalKrullDim ((C.junction i).p ''
        {y : (C.junction i).Y | ∃ S : C.Label, C.IsVaryingLabel S ∧
          ∃ P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩),
            C.IsLabelCentre S ⟨i, none⟩ P ∧ y ∈ P.support}) ≤ 1 := by
  have := C.finite_label
  obtain ⟨e, he⟩ := exists_equiv_isLabelCentre C ⟨i, none⟩
  have hunion : (C.junction i).p ''
      {y : (C.junction i).Y | ∃ S : C.Label, C.IsVaryingLabel S ∧
        ∃ P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩),
          C.IsLabelCentre S ⟨i, none⟩ P ∧ y ∈ P.support} =
      ⋃ S : {S : C.Label // C.IsVaryingLabel S},
        (C.junction i).p '' (e S.1.1 : MMP.Mori.PrimeDivisor (C.junction i).Y).support := by
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨y, ⟨S, hS, P, hP, hy⟩, rfl⟩
      obtain rfl := (he S P).mp hP
      exact ⟨⟨S, hS⟩, y, hy, rfl⟩
    · rintro ⟨⟨S, hS⟩, y, hy, rfl⟩
      exact ⟨y, ⟨S, hS, _, (he S _).mpr rfl, hy⟩, rfl⟩
  have hS := fun S : {S : C.Label // C.IsVaryingLabel S} =>
    isClosed_and_topologicalKrullDim_image_le C ((he S.1 _).mpr rfl) (h3 S.1 S.2)
  rw [hunion]
  exact ⟨isClosed_iUnion_of_finite fun S => (hS S).1,
    topologicalKrullDim_iUnion_le (fun S => (hS S).1) fun S => (hS S).2⟩

end Proof_lem_oai4_c2_prepared_chain_exists

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold.StabilizedSmallKltTail.TerminalChain

variable {T : StabilizedSmallKltTail}

open Proof_lem_oai4_c2_prepared_chain_exists in
/-- Every terminal chain `C` over a stabilized small klt tail has a tail which is a prepared
chain: there is a prepared chain whose underlying terminal chain is `C`. -/
@[mmp "lem_oai4_c2_prepared_chain_exists"]
public theorem exists_preparedChain_chain_eq (C : TerminalChain T) :
    ∃ Q : PreparedChain T, Q.chain = C := by
  classical
  have := C.finite_label
  have := Fintype.ofFinite C.Label
  choose! c n hcn using fun (S : C.Label) (h : C.IsFixedLabel S) => h
  have hN := isAdmissibleScale_prod_den C fun S hS => ⟨n S, hcn S hS⟩
  obtain ⟨i₁, hi₁⟩ := exists_three_le_codimension_of_isVaryingLabel C
  obtain ⟨i₂, hi₂⟩ := exists_isLabelDefault_const C _
  have hn : ∀ S, n S ≤ Finset.univ.sup n := fun S => Finset.le_sup (Finset.mem_univ S)
  refine ⟨⟨C, max (max (Finset.univ.sup n) i₁) i₂, _, hN,
    fun S hS => ⟨c S, fun x hx => isLabelCoefficient_of_forall_ge C (hcn S hS)
      (by have := hn S; omega)⟩,
    fun i _ S hS => ?_,
    fun i hi => (isClosed_and_topologicalKrullDim_image_varyingLabels_le C
      (hi₁ i (by omega))).1,
    fun i hi => (isClosed_and_topologicalKrullDim_image_varyingLabels_le C
      (hi₁ i (by omega))).2,
    fun S => ?_⟩, rfl⟩
  · obtain ⟨b, hb⟩ := exists_isLabelCoefficient S ⟨i, none⟩
    exact ⟨b, hb, hS.pos_of_isJunctionLabelCoefficient hb⟩
  · obtain ⟨d, hd⟩ := hi₂ S
    exact ⟨d, fun x hx => hd x (by omega)⟩

end MMP.Fourfold.StabilizedSmallKltTail.TerminalChain
