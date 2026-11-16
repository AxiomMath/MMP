module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.MoveMonotone
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.EchoSetting
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison

/-!
# Junction difficulties of a prepared chain are nonincreasing

On a prepared chain starting at the junction `Y_{i₀}`, the difficulty of the junctions does not
increase: `𝒟(Y_{i+1}, Θ_{i+1}) ≤ 𝒟(Y_i, Θ_i)` for every `i ≥ i₀`. The junctions `Y_i` and
`Y_{i+1}` are joined by finitely many moves (the coefficient decrease and the flips of the
`i`-th bridge), along each of which the difficulty does not increase.

## Main results

* `MMP.Fourfold.StabilizedTail.PreparedChain.le_of_isDifficulty_junction_succ`: the difficulty
  of the junction `(i + 1, none)` is at most that of the junction `(i, none)`.

## Implementation notes

The junction `(Y_i, Θ_i)` is the model `(i, none)` of the prepared chain
(`MMP.Fourfold.StabilizedTail.PreparedChain.ModelIndex`). Difficulties are values of the
predicate `MMP.Fourfold.StabilizedTail.PreparedChain.IsDifficulty`, so the statement compares
any two values `D` and `D'` of it at the two junctions.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold
  MMP.Fourfold.StabilizedTail MMP.Fourfold.StabilizedTail.PreparedChain

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.IndexdJunctionNonincreasing

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
    rw [WithBot.coe_add]
    exact h.symm.le.trans (add_le_add_left hV _)
  induction c using ENat.recTopCoe with
  | top => exact le_top
  | coe m =>
    have := WithBot.coe_le_coe.1 h3
    norm_cast at this ⊢
    omega

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
  have : LocallyOfFiniteType (Q.chain.modelStructure x.1) := hpair.1.1.toLocallyOfFiniteType
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
    simpa only [w, dif_pos h] using h.choose_spec
  choose d hd using Q.isLabelDefault_const
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
      rw [hZ]
      exact (topologicalKrullDim_zero_of_discreteTopology _).trans (by norm_num)),
    hβ, hd', hρ, rfl⟩

/-- Along the `k`-th flip of the `i`-th bridge, the difficulty does not increase. -/
private theorem le_of_isDifficulty_flip {T : StabilizedTail} (Q : PreparedChain T) {i : ℕ}
    (hi : Q.start ≤ i) {k : ℕ} (hk : k < (Q.chain.bridge i).P.m) {x' : Q.ModelIndex}
    (hx' : x'.1 = Q.chain.flipTarget i ⟨k, hk⟩) {E F : ℤ}
    (hE : Q.IsDifficulty ⟨⟨i, some ⟨k, hk⟩⟩, hi⟩ E) (hF : Q.IsDifficulty x' F) : F ≤ E :=
  difficulty_le_of_move Q (Or.inr (Or.inr ⟨⟨⟨i, ⟨k, hk⟩⟩, hi⟩, rfl, Subtype.ext hx'⟩)) hE hF

/-- If the `i`-th bridge has `k + n + 1` flips, the difficulty of the junction `(i + 1, none)` is
at most that of the model `(i, some k)`. -/
private theorem le_of_isDifficulty_bridge {T : StabilizedTail} (Q : PreparedChain T) {i : ℕ}
    (hi : Q.start ≤ i) {D' : ℤ}
    (hD' : Q.IsDifficulty ⟨⟨i + 1, none⟩, hi.trans i.le_succ⟩ D') :
    ∀ (n k : ℕ) (hk : k + n + 1 = (Q.chain.bridge i).P.m) {E : ℤ},
      Q.IsDifficulty ⟨⟨i, some ⟨k, by omega⟩⟩, hi⟩ E → D' ≤ E := by
  intro n
  induction n with
  | zero =>
    intro k hk E hE
    exact le_of_isDifficulty_flip Q hi _
      (Q.chain.flipTarget_of_not_lt (show ¬ k + 1 < _ by omega)).symm hE hD'
  | succ n ih =>
    intro k hk E hE
    have hlt : k + 1 < (Q.chain.bridge i).P.m := by omega
    obtain ⟨F, hF⟩ := exists_isDifficulty Q ⟨⟨i, some ⟨k + 1, hlt⟩⟩, hi⟩
    exact (ih (k + 1) (by omega) hF).trans
      (le_of_isDifficulty_flip Q hi _
        (Q.chain.flipTarget_of_lt (k := ⟨k, by omega⟩) hlt).symm hE hF)

end MMP.IndexdJunctionNonincreasing

namespace MMP.Fourfold.StabilizedTail.PreparedChain

open MMP.IndexdJunctionNonincreasing

variable {T : StabilizedTail}

/-- On a prepared chain starting at `Y_{i₀}`, the difficulty of the junction `(Y_{i+1}, Θ_{i+1})`
is at most that of `(Y_i, Θ_i)`, for every `i ≥ i₀`. -/
@[mmp "lem_mmp_indexd_junction_nonincreasing"]
public theorem le_of_isDifficulty_junction_succ (Q : PreparedChain T) {i : ℕ} (hi : Q.start ≤ i)
    {D D' : ℤ} (hD : Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D)
    (hD' : Q.IsDifficulty ⟨⟨i + 1, none⟩, hi.trans i.le_succ⟩ D') : D' ≤ D := by
  rcases Nat.eq_zero_or_pos (Q.chain.bridge i).P.m with h | h
  · exact difficulty_le_of_move Q (Or.inr (Or.inl ⟨i, hi, h, rfl, rfl⟩)) hD hD'
  · obtain ⟨E, hE⟩ := exists_isDifficulty Q ⟨⟨i, some ⟨0, h⟩⟩, hi⟩
    exact (le_of_isDifficulty_bridge Q hi hD' ((Q.chain.bridge i).P.m - 1) 0 (by omega) hE).trans
      (difficulty_le_of_move Q (Or.inl ⟨i, hi, h, rfl, rfl⟩) hD hE)

end MMP.Fourfold.StabilizedTail.PreparedChain
