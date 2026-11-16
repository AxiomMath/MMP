module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.BranchCounts
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.LocalCohomologyValuations
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.BranchBound
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.MMP.Fourfold.Echoes

/-!
# The branch inequality

Let `p : Y ⟶ X` be a projective birational morphism of normal projective complex fourfolds, with
`Y` `ℚ`-factorial and terminal, and let `(Y, Θ)` be an effective terminal pair. Let
`Q = Q_1 ∪ ⋯ ∪ Q_m` be a reduced union of distinct prime divisors of `Y` with positive
coefficients in `Θ`, such that `p(Q)` has dimension at most one. Then the branch excess of `Q` is
bounded by the divisor cycle ranks of the normalizations of its components and the number of
low-discrepancy valuations centred on curves of `Q`:
`∑_{V ⊆ Q} (r_V - 1) ≤ ∑_j ρ_*(Q_j^ν) + #{v | codim c_Y(v) = 3, c_Y(v) ⊆ Q, a(v; Y, Θ) < 2}`,
where `V` runs over the irreducible surfaces of `Q` and `v` over the normalized divisorial
valuations of `ℂ(Y)`. No crepancy assumption is made on `p`.

## Main results

* `MMP.Fourfold.sum_boundaryBranchCount_sub_one_le`: the branch inequality.

## Implementation notes

* The reduced union `Q` is a finite set of prime divisors of `Y`, as for
  `MMP.Fourfold.boundaryBranchCount`, which is `r_V`; `V ⊆ Q` means containment in the union of
  the supports. The left side is the finitely supported sum `∑ᶠ` over irreducible closed subsets
  of dimension two contained in `Q` (`0` if the support were infinite). Its support is finite by
  `MMP.Fourfold.one_le_boundaryBranchCount_and_finite_setOf_one_lt`.
* `ρ_*(Q_j^ν)` is `MMP.Analytic.divisorCycleRank` of
  `MMP.Fourfold.primeDivisorNormalizationScheme`, over `ℂ` through `Q_j^ν ⟶ Y`, a complex scheme by
  `MMP.Fourfold.isComplexScheme_primeDivisorNormalizationScheme`.
* The count of valuations is `Set.ncard`; the set is finite. Centres are
  `MMP.Intersection.IsCentre` and log discrepancies `MMP.Fourfold.IsValuationLogDiscrepancy`.
* A boundary of a `ℚ`-divisor (`MMP.Mori.QDivisor`) is rational; effectivity is `0 ≤ Θ`.
  Terminality of `Y` is `MMP.Fourfold.IsTerminalVariety`, of `(Y, Θ)`
  `MMP.Fourfold.IsKltTerminalPair`.

## References

* [Termination for projective log canonical fourfolds with rational boundary (OpenAI, 2026)]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Proof_thm_oai4_branch

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Fourfold MMP.Mori

/-- A finitely supported sum of natural numbers, each bounded by the cardinality of one of
pairwise disjoint subsets of a finite set `S`, is bounded by the cardinality of `S`. -/
private lemma finsum_mem_le_ncard {ι α : Type*} {s : Set ι} {b : ι → ℕ} {Ξ : ι → Set α}
    {S : Set α} (hS : S.Finite) (hΞS : ∀ i ∈ s, Ξ i ⊆ S)
    (hb : ∀ i ∈ s, (b i : ℕ∞) ≤ (Ξ i).encard) (hdisj : s.PairwiseDisjoint Ξ) :
    ∑ᶠ i ∈ s, b i ≤ S.ncard := by
  by_cases ht : (s ∩ Function.support b).Finite
  · have hΞ : ∀ i ∈ s, (Ξ i).Finite := fun i hi => hS.subset (hΞS i hi)
    rw [← finsum_mem_inter_support, ← ht.coe_toFinset, finsum_mem_coe_finset]
    calc ∑ i ∈ ht.toFinset, b i ≤ ∑ i ∈ ht.toFinset, (Ξ i).ncard :=
          Finset.sum_le_sum fun i hi => by
            rw [Set.Finite.mem_toFinset] at hi
            exact_mod_cast (hΞ i hi.1).cast_ncard_eq ▸ hb i hi.1
      _ = (⋃ i ∈ (ht.toFinset : Set ι), Ξ i).ncard := by
          rw [Set.Finite.ncard_biUnion (Finset.finite_toSet _)
            (fun i hi => hΞ i (by simp_all)) (hdisj.subset (by simp)), finsum_mem_coe_finset]
      _ ≤ S.ncard := Set.ncard_le_ncard (Set.iUnion₂_subset fun i hi => hΞS i (by simp_all)) hS
  · rw [finsum_mem_eq_zero_of_infinite ht]
    exact Nat.zero_le _

/-- On a variety of dimension four, an irreducible closed curve has codimension three. -/
private lemma codimension_eq_three {Y : Scheme.{0}} [IsIntegral Y] (sY : Y ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sY] (hdim : topologicalKrullDim Y = 4) (V : IrreducibleCloseds Y)
    (hV : topologicalKrullDim (V : Set Y) = 1) : codimension V = 3 := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
    V.isIrreducible.genericPoint
  rw [IsIrreducible.closure_genericPoint V.isIrreducible V.isClosed, hdim, hV] at h
  rw [MMP.Flips.codimension_eq_coheight_genericPoint]
  generalize Order.coheight V.isIrreducible.genericPoint = c at h ⊢
  have h' : 1 + c = 4 := WithBot.coe_injective h
  induction c using ENat.recTopCoe with
  | top => simp at h'
  | coe n => norm_cast at h' ⊢; omega

/-- An irreducible set contained in the union of the supports of finitely many prime divisors is
contained in the support of one of them. -/
private lemma exists_mem_subset_support {Y : Scheme.{0}} (Q : Finset (MMP.Mori.PrimeDivisor Y))
    {T : Set Y} (hT : IsIrreducible T) (hTQ : T ⊆ ⋃ S ∈ Q, (S.support : Set Y)) :
    ∃ D ∈ Q, T ⊆ D.support := by
  classical
  obtain ⟨z, hz, hTz⟩ := (isIrreducible_iff_sUnion_isClosed.mp hT)
    (Q.image fun S => (S.support : Set Y))
    (by
      intro z hz
      obtain ⟨S, -, rfl⟩ := Finset.mem_image.mp hz
      exact S.idealSheaf.support.isClosed)
    (by
      intro y hy
      obtain ⟨S, hS, hyS⟩ := Set.mem_iUnion₂.mp (hTQ hy)
      exact Set.mem_sUnion.mpr ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hS), hyS⟩)
  obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨D, hD, hTz⟩

/-- On a `ℚ`-factorial projective fourfold with a klt-terminal pair `(Y, Θ)`, only finitely many
divisorial valuations with centre of codimension three inside `Q` have log discrepancy `< 2`. -/
private lemma finite_setOf_codimension_eq_three_logDiscrepancy_lt_two {Y : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    (hYproj : MMP.Mori.IsProjectiveVariety ℂ sY) (hYdim : topologicalKrullDim Y = 4)
    (hYQ : IsQFactorial sY) {Θ : QDivisor Y} (hΘ : IsKltTerminalPair sY Θ)
    (Q : Finset (MMP.Mori.PrimeDivisor Y)) :
    {v : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
      (∃ Z : IrreducibleCloseds Y, MMP.Intersection.IsCentre ℂ sY v Z ∧
        codimension Z = 3 ∧ (Z : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y)) ∧
      ∃ a : ℝ, IsValuationLogDiscrepancy sY Θ v a ∧ a < 2}.Finite := by
  refine (IsKltTerminalPair.finite_setOf_three_le_codimension_centre hYproj hYQ hYdim hΘ
    (L := Θ.support) subset_rfl).subset ?_
  rintro v ⟨⟨Z, hZ, hcod, -⟩, a, ⟨n, D, -, hDv, hD⟩, ha⟩
  refine ⟨?_, ⟨a, ha, n, D, hDv, hD⟩, Z, hZ, hcod.ge⟩
  obtain ⟨D', hD', hv, rfl⟩ := hZ
  exact ⟨D', hD', hv, by rw [hcod]; decide⟩

private theorem solution :
    ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
    (hX : IsNormalVariety ℂ sX) (hXproj : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hXdim : topologicalKrullDim X = 4)
    (p : Y ⟶ X) (hp : p ≫ sX = sY) (hpproj : IsProjectiveMorphism p)
    (hpbir : IsBirationalMorphism p)
    (hYproj : MMP.Mori.IsProjectiveVariety ℂ sY) (hYdim : topologicalKrullDim Y = 4)
    (hYQ : IsQFactorial sY) (hYt : IsTerminalVariety sY)
    (Θ : QDivisor Y) (hΘ0 : 0 ≤ Θ) (hΘ : IsKltTerminalPair sY Θ)
    (Q : Finset (MMP.Mori.PrimeDivisor Y)) (hQ : ∀ S ∈ Q, 0 < Θ S)
    (hpQ : topologicalKrullDim (p.base '' ⋃ S ∈ Q, (S.support : Set Y)) ≤ 1),
    ∑ᶠ (V : IrreducibleCloseds Y) (_ : topologicalKrullDim (V : Set Y) = 2 ∧
        (V : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y)), ((boundaryBranchCount Q V : ℤ) - 1) ≤
      ((∑ S ∈ Q,
          letI := primeDivisorNormalizationOver sY S
          haveI := isComplexScheme_primeDivisorNormalizationScheme sY hYproj S
          MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme S) : ℕ) : ℤ) +
        ({v : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
          (∃ Z : IrreducibleCloseds Y, MMP.Intersection.IsCentre ℂ sY v Z ∧
            codimension Z = 3 ∧ (Z : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y)) ∧
          ∃ a : ℝ, IsValuationLogDiscrepancy sY Θ v a ∧ a < 2}.ncard : ℤ) := by
  intro X Y _ _ _ _ _ _ sX sY hX hXproj hXdim p hp hpproj hpbir hYproj hYdim hYQ hYt Θ hΘ0 hΘ
    Q hQ hpQ
  obtain ⟨To, hTo, hbound⟩ := sum_boundaryBranchCount_sub_one_le_sum_curveLocalSystemRank
    sX sY hX hXproj hXdim p hp hpproj hpbir hYproj hYdim hYQ hYt Q hpQ
  refine hbound.trans (add_le_add_right ?_ _)
  have hYv : MMP.Mori.IsVariety ℂ sY := hYQ.1.1
  haveI : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  have key := finsum_mem_le_ncard
    (s := {T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
        topologicalKrullDim (T : Set Y) = 1} | (T.1 : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y)})
    (b := fun T => curveLocalSystemRank sY (To T))
    (Ξ := fun T => {v : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
      MMP.Intersection.IsCentre ℂ sY v T.1 ∧
      IsValuationLogDiscrepancy sY (0 : QDivisor Y) v 2 ∧
      ∃ a : ℝ, IsValuationLogDiscrepancy sY Θ v a ∧ a < 2})
    (finite_setOf_codimension_eq_three_logDiscrepancy_lt_two hYproj hYdim hYQ hΘ Q) ?_ ?_ ?_
  · exact_mod_cast key
  · rintro T hT v ⟨hc, -, ha⟩
    exact ⟨⟨T.1, hc, codimension_eq_three sY hYdim T.1 T.2.2, hT⟩, ha⟩
  · intro T hT
    obtain ⟨D, hD, hTD⟩ := exists_mem_subset_support Q T.1.isIrreducible hT
    exact IsKltTerminalPair.curveLocalSystemRank_le_encard hYQ hYproj hYdim hΘ T.2.2 T.2.1 D
      (hQ D hD) hTD (To T) (hTo T)
  · intro T _ T' _ hne
    refine Set.disjoint_left.mpr fun v hv hv' => hne (Subtype.ext ?_)
    obtain ⟨⟨D, -, hDv, hT⟩, -⟩ := hv
    obtain ⟨⟨D', -, hD'v, hT'⟩, -⟩ := hv'
    rw [hT, hT', MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hYv (hDv.symm.trans hD'v)]

end Proof_thm_oai4_branch

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori

/-- **Branch inequality.** Let `p : Y ⟶ X` be a projective birational morphism of normal
projective complex fourfolds, with `Y` `ℚ`-factorial and terminal and `(Y, Θ)` an effective
terminal pair. Let `Q` be a finite set of prime divisors of `Y` with positive coefficients in
`Θ`, whose union has image of dimension at most one under `p`. Then
`∑_{V ⊆ Q} (r_V - 1) ≤ ∑_{S ∈ Q} ρ_*(S^ν) + #{v | codim c_Y(v) = 3, c_Y(v) ⊆ Q, a(v; Y, Θ) < 2}`,
with `V` over the irreducible surfaces contained in `Q`, `r_V = boundaryBranchCount Q V`,
`ρ_*(S^ν) = MMP.Analytic.divisorCycleRank` of the normalization of `S`, and `v` over the
normalized divisorial valuations of `ℂ(Y)`. -/
@[mmp "thm_oai4_branch"]
public theorem sum_boundaryBranchCount_sub_one_le
    {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
    (hX : IsNormalVariety ℂ sX) (hXproj : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hXdim : topologicalKrullDim X = 4)
    (p : Y ⟶ X) (hp : p ≫ sX = sY) (hpproj : IsProjectiveMorphism p)
    (hpbir : IsBirationalMorphism p)
    (hYproj : MMP.Mori.IsProjectiveVariety ℂ sY) (hYdim : topologicalKrullDim Y = 4)
    (hYQ : IsQFactorial sY) (hYt : IsTerminalVariety sY)
    (Θ : QDivisor Y) (hΘ0 : 0 ≤ Θ) (hΘ : IsKltTerminalPair sY Θ)
    (Q : Finset (MMP.Mori.PrimeDivisor Y)) (hQ : ∀ S ∈ Q, 0 < Θ S)
    (hpQ : topologicalKrullDim (p.base '' ⋃ S ∈ Q, (S.support : Set Y)) ≤ 1) :
    ∑ᶠ (V : IrreducibleCloseds Y) (_ : topologicalKrullDim (V : Set Y) = 2 ∧
        (V : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y)), ((boundaryBranchCount Q V : ℤ) - 1) ≤
      ((∑ S ∈ Q,
          letI := primeDivisorNormalizationOver sY S
          haveI := isComplexScheme_primeDivisorNormalizationScheme sY hYproj S
          MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme S) : ℕ) : ℤ) +
        ({v : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
          (∃ Z : IrreducibleCloseds Y, MMP.Intersection.IsCentre ℂ sY v Z ∧
            codimension Z = 3 ∧ (Z : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y)) ∧
          ∃ a : ℝ, IsValuationLogDiscrepancy sY Θ v a ∧ a < 2}.ncard : ℤ) :=
            by revert X Y sX sY hX hXproj hXdim p hp hpproj hpbir hYproj hYdim hYQ hYt Θ hΘ0 hΘ Q hQ hpQ; first | exact Proof_thm_oai4_branch.solution | exact Proof_thm_oai4_branch.solution _ | exact Proof_thm_oai4_branch.solution _ _ | exact Proof_thm_oai4_branch.solution _ _ _ | exact Proof_thm_oai4_branch.solution _ _ _ _

end MMP.Fourfold

