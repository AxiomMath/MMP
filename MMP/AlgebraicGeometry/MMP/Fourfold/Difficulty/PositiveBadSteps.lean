module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.JunctionNonincreasing
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.JunctionStrictDrop
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.PreparedChainExists
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.TerminalChainExists
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.JunctionNonneg
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainAdmissibleScale
import MMP.AlgebraicGeometry.MMP.Fourfold.StabilizedTail.BadCurvesGood
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.EchoSetting
import MMP.AlgebraicGeometry.Divisor.SNC
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty

/-!
# Positive-side bad curves occur finitely often

In a stabilized small klt threefold tail `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}`, only finitely
many steps `i` have an irreducible curve contained in the positive-side bad locus
`W_i⁺ ⊆ X_{i+1}`.

## Main results

* `MMP.Fourfold.StabilizedTail.finite_setOf_exists_curve_subset_badLocusPlusAt`

## Implementation notes

An irreducible curve of `X_{i+1}` is an irreducible closed subset of dimension one; it carries
its reduced structure, so it is recorded as an element of `IrreducibleCloseds`.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold
  MMP.Fourfold.StabilizedTail MMP.Fourfold.StabilizedTail.PreparedChain

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace Proof_lem_mmp_index_positive_bad_steps_finite

/-- On a threefold, an irreducible closed subset of dimension at most one has codimension at
least two. -/
private theorem two_le_codimension {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y]
    [LocallyOfFiniteType sY] (hdim : topologicalKrullDim Y = 3) (V : IrreducibleCloseds Y)
    (hV : topologicalKrullDim (V : Set Y) ≤ 1) : 2 ≤ codimension V := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
    V.isIrreducible.genericPoint
  rw [IsIrreducible.closure_genericPoint V.isIrreducible V.isClosed, hdim] at h
  rw [MMP.Flips.codimension_eq_coheight_genericPoint]
  generalize Order.coheight V.isIrreducible.genericPoint = c at h ⊢
  have h3 : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ((1 + c : ℕ∞) : WithBot ℕ∞) := by
    rw [WithBot.coe_add]; exact h.symm.le.trans (add_le_add_left hV _)
  induction c using ENat.recTopCoe with
  | top => exact le_top
  | coe m => have := WithBot.coe_le_coe.1 h3; norm_cast at this ⊢; omega

/-- The closure of the generic point of a proper curve has dimension one: it is the image of
the closed immersion of the curve. -/
private theorem topologicalKrullDim_closure_point {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) :
    topologicalKrullDim (closure {C.point} : Set X) = 1 := by
  have hr : Set.range C.ι = closure {C.point} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [← hr, ← C.dim_eq]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    C.ι.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

/-- A divisorial valuation centred, on a model of a prepared chain, on an irreducible closed
subset of dimension at most one is exceptional, and so has a weight there. -/
private theorem exists_isValuationWeight {T : StabilizedTail} (Q : PreparedChain T)
    (x : Q.ModelIndex)
    {v : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ))}
    {Z : IrreducibleCloseds (Q.chain.model x.1)}
    (hvZ : MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z)
    (hZ : topologicalKrullDim (Z : Set (Q.chain.model x.1)) ≤ 1) :
    ∃ w, Q.chain.IsValuationWeight Q.scale x.1 v w := by
  obtain ⟨hΘ, -, -, hdim, -, -⟩ := Q.echoSetting_model x
  have hpair := hΘ.1.1.isPair
  haveI : LocallyOfFiniteType (Q.chain.modelStructure x.1) := hpair.1.1.toLocallyOfFiniteType
  have hv : MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure x.1) v := by
    obtain ⟨D, hp, rfl, rfl⟩ := hvZ
    exact ⟨D, hp, rfl, two_le_codimension (Q.chain.modelStructure x.1) hdim _ hZ⟩
  obtain ⟨-, n, K, hK, -⟩ := id hpair
  obtain ⟨D, hDp, rfl, -⟩ := id hv
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair hK D
  exact ⟨_, hv, _, ⟨n, D, hDp, rfl,
    MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hDp⟩, rfl⟩

/-- Every model of a prepared chain has a difficulty. -/
private theorem exists_isDifficulty {T : StabilizedTail} (Q : PreparedChain T)
    (x : Q.ModelIndex) : ∃ D, Q.IsDifficulty x D := by
  classical
  let w : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) → ℕ :=
    fun v => if h : ∃ w, Q.chain.IsValuationWeight Q.scale x.1 v w then h.choose else 0
  have hw : ∀ v (Z : IrreducibleCloseds (Q.chain.model x.1)),
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z →
        topologicalKrullDim (Z : Set (Q.chain.model x.1)) ≤ 1 →
          Q.chain.IsValuationWeight Q.scale x.1 v (w v) := fun v Z hvZ hZ => by
    have h := exists_isValuationWeight Q x hvZ hZ
    simp only [w, dif_pos h]
    exact h.choose_spec
  choose d hd using fun S => Q.isLabelDefault_const S
  have hd' : ∀ S, Q.chain.IsLabelDefault Q.scale S x.1 (d S) := fun S => hd S x.1 x.2
  have hP : ∀ S, ∃ P, Q.chain.IsLabelCentre S x.1 P := fun S => by
    obtain ⟨b, ⟨P, hP, -⟩, -⟩ := hd' S
    exact ⟨P, hP⟩
  choose P hP using hP
  have hβ : ∀ γ : ProperCurve (Q.chain.modelStructure x.1), ∃ β, Q.IsCurveBracket x γ β :=
    fun γ => ⟨_, w, fun S => branchNumber (P S) (closure {γ.point}), d,
      fun v ⟨Z, hvZ, hZ⟩ => hw v Z hvZ (by rw [hZ, topologicalKrullDim_closure_point]),
      fun S => ⟨P S, hP S, rfl⟩, hd', rfl⟩
  choose β hβ using hβ
  have hρ : ∀ S, ∃ ρ, Q.chain.IsLabelBoxedRank S x.1 ρ := fun S => ⟨_, P S, hP S, rfl⟩
  choose ρ hρ using hρ
  exact ⟨_, w, β, d, ρ,
    fun v ⟨Z, hvZ, y, _, hZ⟩ => hw v Z hvZ (by
      rw [hZ]; exact (topologicalKrullDim_zero_of_discreteTopology _).trans (by norm_num)),
    hβ, hd', hρ, rfl⟩

/-- A nonincreasing sequence of nonnegative integers drops strictly only finitely often: it is
eventually constant. -/
private theorem finite_setOf_lt_of_antitone {f : ℕ → ℤ} (hf : ∀ n, f (n + 1) ≤ f n)
    (h0 : ∀ n, 0 ≤ f n) : {n | f (n + 1) < f n}.Finite := by
  have hanti : Antitone f := antitone_nat_of_succ_le hf
  obtain ⟨n₀, hn₀⟩ := WellFoundedLT.antitone_chain_condition
    (f := fun n => (f n).toNat) fun _ _ h => Int.toNat_le_toNat (hanti h)
  refine (Set.finite_Iio n₀).subset fun n hn => Set.mem_Iio.2 <| lt_of_not_ge fun hle => ?_
  have hlt : f (n + 1) < f n := hn
  have h1 := hn₀ n hle
  have h2 := hn₀ (n + 1) (hle.trans n.le_succ)
  have := h0 (n + 1)
  omega

/-- The local ring of a scheme at a point smooth over a field is regular. -/
private theorem isRegularLocalRing_stalk_of_mem_smoothLocus {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {y : X} (hy : y ∈ MMP.Mori.smoothLocus sX) :
    IsRegularLocalRing (X.presheaf.stalk y) := by
  obtain ⟨U, hyU, hU⟩ := MMP.Mori.mem_smoothLocus_iff.mp hy
  have : Smooth (U.ι ≫ sX) := hU
  have := isRegularLocalRing_stalk_of_smooth_over_field (U.ι ≫ sX) ⟨y, hyU⟩
  exact IsRegularLocalRing.of_ringEquiv (U.stalkIso ⟨y, hyU⟩).commRingCatIsoToRingEquiv

private theorem solution : ∀ (T : StabilizedTail),
    {i : ℕ | ∃ V : IrreducibleCloseds (T.X (i + 1)),
      topologicalKrullDim (V : Set (T.X (i + 1))) = 1 ∧
        (V : Set (T.X (i + 1))) ⊆ T.badLocusPlusAt i}.Finite := by
  intro T
  obtain ⟨C⟩ := TerminalChain.nonempty T
  obtain ⟨N, hN⟩ := C.exists_isAdmissibleScale
  obtain ⟨i₂, Q, -, rfl, -⟩ := (C.eventually_exists_preparedChain hN).exists
  obtain ⟨i₁, hi₁⟩ := T.exists_forall_ge_one_lt_minimalLogDiscrepancy_and_mem_smoothLocus
  choose f hf using fun n => exists_isDifficulty Q ⟨⟨Q.start + n, none⟩, Nat.le_add_right _ n⟩
  obtain ⟨n₀, hn₀⟩ := (finite_setOf_lt_of_antitone
    (fun n => le_of_isDifficulty_junction_succ Q _ (hf n) (hf (n + 1)))
    (fun n => difficulty_nonneg_of_junction Q _ (hf n))).bddAbove
  refine (Set.finite_Iio (max i₁ (Q.start + n₀ + 1))).subset
    fun i ⟨V, hV, hVW⟩ => Set.mem_Iio.2 <| lt_of_not_ge fun hge => ?_
  rw [max_le_iff] at hge
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (show Q.start ≤ i by omega)
  obtain ⟨hmld, hsm⟩ := (hi₁ _ hge.1).2 V hV hVW
  have := hn₀ (lt_of_isDifficulty_junction_succ Q _ V hVW hV
    (isRegularLocalRing_stalk_of_mem_smoothLocus hsm) hmld (hf n) (hf (n + 1)))
  omega

end Proof_lem_mmp_index_positive_bad_steps_finite

end

open AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold.StabilizedTail

/-- In a stabilized threefold tail `T`, only finitely many indices `i` have an irreducible curve
`V ⊆ X_{i+1}` contained in the positive-side bad locus `W_i⁺` of the `i`-th step. -/
@[mmp "lem_mmp_index_positive_bad_steps_finite"]
public theorem finite_setOf_exists_curve_subset_badLocusPlusAt (T : StabilizedTail) :
    {i : ℕ | ∃ V : IrreducibleCloseds (T.X (i + 1)),
      topologicalKrullDim (V : Set (T.X (i + 1))) = 1 ∧
        (V : Set (T.X (i + 1))) ⊆ T.badLocusPlusAt i}.Finite :=
          by revert T; first | exact Proof_lem_mmp_index_positive_bad_steps_finite.solution | exact Proof_lem_mmp_index_positive_bad_steps_finite.solution _ | exact Proof_lem_mmp_index_positive_bad_steps_finite.solution _ _ | exact Proof_lem_mmp_index_positive_bad_steps_finite.solution _ _ _ | exact Proof_lem_mmp_index_positive_bad_steps_finite.solution _ _ _ _

end MMP.Fourfold.StabilizedTail
