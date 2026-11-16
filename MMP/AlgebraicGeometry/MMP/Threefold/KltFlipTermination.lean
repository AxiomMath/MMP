module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.PositiveBadSteps
import MMP.AlgebraicGeometry.MMP.Termination.FlipSequenceStabilizedTail
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.ExceptionalCountFinite
import MMP.AlgebraicGeometry.MMP.Threefold.StepDiagram.BadLociTerminalChain

/-!
# Termination of projective klt threefold flips

Every projective termination level `T(e)` holds: a sequence of flips of an effective rational
klt pair `(X, B)` on a normal projective `ℚ`-factorial complex threefold, all of whose models and
contraction targets are projective, is finite. Since `e(X, B)` is finite for a klt pair, this
holds without any condition on `e(X, B)`.

## Main results

* `MMP.Fourfold.forall_projectiveKltTerminationLevel_and_terminates`: `T(e)` holds for every
  `e ∈ ℕ`, and every sequence of flips as above terminates.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 6.6
-/

@[expose] public section

section

namespace Proof_thm_mmp_index_threefold_klt_flip_termination

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Flips MMP.Fourfold

/-- For an isomorphism `f`, `f^* N¹(Z)_ℝ` is all of `N¹(X)_ℝ`. -/
private theorem pullbackNumericalClasses_eq_top {k : Type} [Field k] {X Z : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (f : X ⟶ Z) [IsIso f] :
    pullbackNumericalClasses sX f = ⊤ := by
  refine eq_top_iff.mpr fun d _ => ?_
  obtain ⟨D, rfl⟩ := Submodule.mkQ_surjective _ d
  change numericalDivisorClass sX D ∈ _
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D₁ D₂ h₁ h₂ =>
    rw [map_add]; exact Submodule.add_mem _ (h₁ Submodule.mem_top) (h₂ Submodule.mem_top)
  | single E c =>
    have e : (Finsupp.single E c : KCartierDivisor ℝ X) = c • KCartierDivisor.ofCartier ℝ E := by
      simp [KCartierDivisor.ofCartier]
    rw [e, map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨E, (Scheme.Modules.pullback (inv f)).obj (MMP.CartierDivisor.sheaf E),
      inferInstance, ⟨?_⟩, rfl⟩
    exact ((Scheme.Modules.pullbackId X).app _).symm ≪≫
      (Scheme.Modules.pullbackCongr (IsIso.hom_inv_id f)).symm.app _ ≪≫
      ((Scheme.Modules.pullbackComp f (inv f)).app _).symm

/-- A morphism with `ρ(X/Z) = 1` is not an isomorphism, since an isomorphism has `ρ(X/Z) = 0`. -/
private theorem not_isIso_of_relativePicardNumberN1_eq_one {k : Type} [Field k]
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (f : X ⟶ Z)
    (h : relativePicardNumberN1 sX f = 1) : ¬ IsIso f := by
  intro hf
  rw [relativePicardNumberN1, pullbackNumericalClasses_eq_top] at h
  simp at h

/-- A stabilized tail of three-dimensional flips cannot exist: every step `f_i` is small and
not an isomorphism (it has `ρ = 1`), so carries a curve in its positive bad locus, while only
finitely many steps do. -/
private theorem isEmpty_stabilizedTail : IsEmpty StabilizedTail := by
  refine ⟨fun T => Set.infinite_univ (α := ℕ) ?_⟩
  convert T.finite_setOf_exists_curve_subset_badLocusPlusAt
  refine (Set.eq_univ_of_forall fun i => ?_).symm
  exact (T.isThreefoldStepDiagram i).exists_irreducibleCloseds_subset_badLocusPlus
    (T.isSmallMorphism i)
    (not_isIso_of_relativePicardNumberN1_eq_one _ _ (T.relativePicardNumber_eq_one i))

/-- Every level of projective klt termination holds: an infinite sequence of flips would have a
stabilized tail. -/
private theorem projectiveKltTerminationLevel (e : ℕ) : ProjectiveKltTerminationLevel e := by
  intro X _ _ _ _ sX _ K B hproj hdim hQ hBeff hklt hB _ S hmodel hbase
  by_contra hS
  have hL : S.length = ⊤ := not_lt_top_iff.mp hS
  obtain ⟨_, T, _⟩ := exists_stabilizedTail_of_sequenceOfFlips X sX K B hproj hdim hQ hBeff
    hklt hB S hL (fun i => hmodel i (hL ▸ ENat.coe_lt_top i))
    (fun i => hbase i (hL ▸ ENat.coe_lt_top (i + 1)))
  exact isEmpty_stabilizedTail.false T

private theorem solution :
    (∀ e : ℕ, ProjectiveKltTerminationLevel e) ∧
    ∀ (X : Scheme.{0}) [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
      (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] (K : Divisor X) (B : QDivisor X),
      MMP.Mori.IsProjectiveVariety ℂ sX → topologicalKrullDim X = 3 → IsQFactorial sX →
      B.IsEffective → IsKltPair sX B → IsKawamataLogTerminal sX 3 K (QDivisor.toRDivisor B) →
      ∀ S : SequenceOfFlips sX 3 K B,
        (∀ i : ℕ, (i : ℕ∞) < S.length → MMP.Mori.IsProjectiveVariety ℂ (S.model i).2.1) →
        (∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < S.length →
          MMP.Mori.IsProjectiveVariety ℂ (S.baseStr i)) →
        S.Terminates :=
  ⟨projectiveKltTerminationLevel, fun X _ _ _ _ sX _ K B hproj hdim hQ hBeff hklt hB =>
    projectiveKltTerminationLevel _ X sX K B hproj hdim hQ hBeff hklt hB
      (hB.finite_smallDiscrepancySet sX).cast_ncard_eq.symm⟩

end Proof_thm_mmp_index_threefold_klt_flip_termination

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Termination of projective klt threefold flips.** The projective termination level `T(e)`
holds for every `e ∈ ℕ`. Consequently, for every normal projective `ℚ`-factorial complex threefold
`X` with canonical divisor `K` and every effective `ℚ`-divisor `B` with `(X, B)` klt, every
sequence of flips for `(X, B)` whose models and contraction targets are all projective
terminates. -/
@[mmp "thm_mmp_index_threefold_klt_flip_termination"]
public theorem forall_projectiveKltTerminationLevel_and_terminates :
    (∀ e : ℕ, ProjectiveKltTerminationLevel e) ∧
    ∀ (X : Scheme.{0}) [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
      (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] (K : Divisor X) (B : QDivisor X),
      MMP.Mori.IsProjectiveVariety ℂ sX → topologicalKrullDim X = 3 → IsQFactorial sX →
      B.IsEffective → IsKltPair sX B → IsKawamataLogTerminal sX 3 K (QDivisor.toRDivisor B) →
      ∀ S : SequenceOfFlips sX 3 K B,
        (∀ i : ℕ, (i : ℕ∞) < S.length → MMP.Mori.IsProjectiveVariety ℂ (S.model i).2.1) →
        (∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < S.length →
          MMP.Mori.IsProjectiveVariety ℂ (S.baseStr i)) →
        S.Terminates :=
          by first | exact Proof_thm_mmp_index_threefold_klt_flip_termination.solution | exact Proof_thm_mmp_index_threefold_klt_flip_termination.solution _ | exact Proof_thm_mmp_index_threefold_klt_flip_termination.solution _ _ | exact Proof_thm_mmp_index_threefold_klt_flip_termination.solution _ _ _ | exact Proof_thm_mmp_index_threefold_klt_flip_termination.solution _ _ _ _

end MMP.Fourfold
