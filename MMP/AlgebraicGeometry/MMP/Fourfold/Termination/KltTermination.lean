module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.PositiveBadSurfacesFinite
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagramBranches
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.StepSequenceCycleRank
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ExceptionalValuations
public import MMP.AlgebraicGeometry.MMP.Fourfold.LowDiscrepancySetStabilizes

/-!
# Termination for klt fourfolds

Let `(X, B)` be a projective klt pair over `ℂ`, where `X` has dimension four and `B` is a
`ℚ`-divisor. Every program (`MMP.Fourfold.Program`) from `(X, B)` has finitely many birational
steps. No pseudo-effectivity hypothesis on `K_X + B` is assumed. The proof runs the difficulty
argument along the small, stabilized tail of an infinite step sequence and derives a
contradiction from the bad loci being nonempty.

## Main results

* `MMP.Fourfold.Program.n_ne_top_of_isKltPair`: a program from a projective klt fourfold pair
  over `ℂ` with rational boundary has `n < ∞` birational steps.

## Implementation notes

Projectivity of `X` and the lc condition on `(X, B)` are fields of `MMP.Fourfold.Program`
(`isProjectiveVariety`, `isLogCanonicalPair`), so they are not repeated as hypotheses.
"Rational boundary" is the coefficient ring `ℚ` of `B : QDivisor X`; effectivity of `B` is part
of `MMP.Fourfold.IsKltPair` (through `MMP.Fourfold.IsPair`).
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Proof_thm_oai4_klt_termination

open MMP.Mori MMP.Fourfold

/-- An isomorphism pulls back every numerical divisor class. -/
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

/-- An isomorphism has relative Picard number zero. -/
private theorem relativePicardNumberN1_eq_zero {k : Type} [Field k] {X Z : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (f : X ⟶ Z) [IsIso f] :
    relativePicardNumberN1 sX f = 0 := by
  rw [relativePicardNumberN1, pullbackNumericalClasses_eq_top]
  simp

namespace StepSequence

variable (S : MMP.Fourfold.StepSequence)

/-- `Corresponds i` is functional. -/
private theorem corresponds_right_unique : ∀ {i : ℕ} {ξ} {η ζ},
    S.Corresponds i ξ η → S.Corresponds i ξ ζ → η = ζ
  | 0, _, _, _, h₁, h₂ => h₁.trans h₂.symm
  | i + 1, _, _, _, ⟨_, hc₁, ht₁⟩, ⟨_, hc₂, ht₂⟩ => by
    obtain rfl := corresponds_right_unique hc₁ hc₂
    ext x
    obtain ⟨y, rfl⟩ :=
      (S.isFourfoldStepDiagram i).isBirationalMorphism_plus.functionFieldMap_bijective.2 x
    exact congrArg (fun u : Valuation _ _ => u y) (ht₁.trans ht₂.symm)

/-- `S.Corresponds (i₀ + j)` is `S.Corresponds i₀` followed by `(S.shift i₀).Corresponds j`. -/
private theorem corresponds_add_iff (i₀ : ℕ) : ∀ (j : ℕ) (ξ η),
    S.Corresponds (i₀ + j) ξ η ↔ ∃ ζ, S.Corresponds i₀ ξ ζ ∧ (S.shift i₀).Corresponds j ζ η
  | 0, ξ, η => ⟨fun h => ⟨η, h, rfl⟩, fun ⟨ζ, h, e⟩ => (e : η = ζ) ▸ h⟩
  | j + 1, ξ, η => by
    constructor
    · rintro ⟨ζ', hc, ht⟩
      obtain ⟨ζ, h0, hj⟩ := (corresponds_add_iff i₀ j ξ ζ').1 hc
      exact ⟨ζ, h0, ζ', hj, ht⟩
    · rintro ⟨ζ, h0, ζ', hj, ht⟩
      exact ⟨ζ', (corresponds_add_iff i₀ j ξ ζ').2 ⟨ζ, h0, hj⟩, ht⟩

/-- If the low-discrepancy sets equal `I_∞` from the index `i₀` on, the tail from `i₀` has the
same property from the index `0` on, for its own stable low-discrepancy set. -/
private theorem lowDiscrepancySetAt_shift_eq (i₀ : ℕ)
    (h : ∀ i, i₀ ≤ i → S.lowDiscrepancySetAt i =
      {η | ∃ ξ ∈ S.stableLowDiscrepancySet, S.Corresponds i ξ η}) (j : ℕ) :
    (S.shift i₀).lowDiscrepancySetAt j =
      {η | ∃ ζ ∈ (S.shift i₀).stableLowDiscrepancySet, (S.shift i₀).Corresponds j ζ η} := by
  ext η
  constructor
  · intro hη
    have hη' : η ∈ S.lowDiscrepancySetAt (i₀ + j) := hη
    rw [h _ (Nat.le_add_right _ _)] at hη'
    obtain ⟨ξ, hξ, hc⟩ := hη'
    obtain ⟨ζ, h0, hj⟩ := (corresponds_add_iff S i₀ j ξ η).1 hc
    refine ⟨ζ, fun k => ?_, hj⟩
    obtain ⟨η'', hη'', hc''⟩ := hξ (i₀ + k)
    obtain ⟨ζ', h0', hk⟩ := (corresponds_add_iff S i₀ k ξ η'').1 hc''
    obtain rfl := corresponds_right_unique S h0' h0
    exact ⟨η'', hη'', hk⟩
  · rintro ⟨ζ, hζ, hj⟩
    obtain ⟨η0, hη0, e⟩ := hζ 0
    have e : η0 = ζ := e
    subst e
    have hη0' : η0 ∈ S.lowDiscrepancySetAt i₀ := hη0
    rw [h _ le_rfl] at hη0'
    obtain ⟨ξ, hξ, h0⟩ := hη0'
    show η ∈ S.lowDiscrepancySetAt (i₀ + j)
    rw [h _ (Nat.le_add_right _ _)]
    exact ⟨ξ, hξ, (corresponds_add_iff S i₀ j ξ η).2 ⟨η0, h0, hj⟩⟩

/-- A step sequence is small from some index on: only finitely many steps lose a prime
divisor, and a step that is not small loses one. -/
private theorem exists_isSmallFrom : ∃ i₀, S.IsSmallFrom i₀ := by
  obtain ⟨i₀, hi₀⟩ := S.finite_setOf_exists_primeDivisor_isExceptionalValuation.bddAbove
  refine ⟨i₀ + 1, fun i hi => by_contra fun hns => ?_⟩
  obtain ⟨E, v, hv, heq⟩ :=
    (S.isFourfoldStepDiagram i).exists_isExceptionalValuation_of_not_isSmallMorphism hns
  have := hi₀ ⟨E, v, heq, hv⟩
  omega

/-- In a step sequence of klt pairs, the base bad locus `Σ_i` is empty for all but finitely
many `i`. -/
private theorem eventually_badLocusBaseAt_eq_bot_of_isKlt (hklt : S.IsKlt) :
    ∀ᶠ i in Filter.cofinite, S.badLocusBaseAt i = ⊥ := by
  obtain ⟨is, hsmall⟩ := exists_isSmallFrom S
  obtain ⟨-, i₀, hi₀⟩ :=
    (S.shift is).finite_stableLowDiscrepancySet_and_exists_lowDiscrepancySetAt_eq hsmall.shift
      fun i => hklt _
  let T : StabilizedSmallKltTail :=
    { toStepSequence := (S.shift is).shift i₀
      isStabilizedSmallKltTail :=
        { isSmallFrom_zero := fun i _ => hsmall.shift (i₀ + i) (Nat.zero_le _)
          isKlt := fun i => hklt _
          lowDiscrepancySetAt_eq := lowDiscrepancySetAt_shift_eq _ i₀ hi₀ } }
  obtain ⟨j₀, hj₀⟩ := T.finite_setOf_exists_isPositiveBadSurface.bddAbove
  refine S.eventually_badLocusBaseAt_eq_bot (is + i₀ + (j₀ + 1)) fun i hi _ V hV => ?_
  obtain ⟨m, rfl⟩ : ∃ m, i = is + (i₀ + m) := ⟨i - (is + i₀), by omega⟩
  have := hj₀ (show m ∈ _ from ⟨V, hV⟩)
  omega

/-- A step whose contraction `f_i` has relative Picard number one has nonempty base bad locus
`Σ_i`: otherwise `f_i` is biregular everywhere, hence an isomorphism, and `ρ(X_i/Z_i) = 0`. -/
private theorem badLocusBaseAt_ne_bot (i : ℕ) (h : relativePicardNumberN1 (S.sX i) (S.f i) = 1) :
    S.badLocusBaseAt i ≠ ⊥ := by
  intro hi
  have htop : commonBiregularLocus (S.f i) (S.fp i) = ⊤ :=
    top_unique fun z _ => by_contra fun hz => by
      have hz' : z ∈ (S.badLocusBaseAt i : Set (S.Z i)) := hz
      rwa [hi] at hz'
  have : IsIso (S.f i) :=
    (isBiregular_top_iff _).mp (htop ▸ isBiregular_commonBiregularLocus_left (S.f i) (S.fp i))
  rw [relativePicardNumberN1_eq_zero] at h
  exact zero_ne_one h

end StepSequence

section Program

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [CompactSpace X]
  [IsLocallyNoetherian X] [IsNormal X] {K : Divisor X} {B : QDivisor X}

/-- Every model of an infinite program from a fourfold is a fourfold. -/
private theorem topologicalKrullDim_modelSeq (hdim : topologicalKrullDim X = 4)
    (P : Program sX K B) (hn : P.n = ⊤) : ∀ i, topologicalKrullDim (modelSeq X P.Y i) = 4
  | 0 => hdim
  | i + 1 => ((P.isPermittedStep i (hn ▸ ENat.coe_lt_top i)).isFourfoldStepDiagram
      (topologicalKrullDim_modelSeq hdim P hn i)).dim_plus

/-- The step sequence of an infinite program from a fourfold. -/
private noncomputable def stepSequence (hdim : topologicalKrullDim X = 4) (P : Program sX K B)
    (hn : P.n = ⊤) : StepSequence where
  X := modelSeq X P.Y
  sX := modelStr sX P.sY
  K := divisorSeq K P.KY
  B := divisorSeq B P.BY
  Z := P.Z
  sZ := P.sZ
  f := P.f
  fp := P.fp
  isFourfoldStepDiagram i := (P.isPermittedStep i (hn ▸ ENat.coe_lt_top i)).isFourfoldStepDiagram
    (topologicalKrullDim_modelSeq hdim P hn i)
  K_eq i := P.KY_eq i (hn ▸ ENat.coe_lt_top i)
  B_eq i := P.BY_eq i (hn ▸ ENat.coe_lt_top i)

/-- The step sequence of an infinite program from a klt pair is a step sequence of klt pairs. -/
private theorem isKlt_stepSequence (hdim : topologicalKrullDim X = 4) (hB : IsKltPair sX B)
    (P : Program sX K B) (hn : P.n = ⊤) : (stepSequence hdim P hn).IsKlt
  | 0 => hB
  | i + 1 => (stepSequence hdim P hn).B_eq i ▸
      ((stepSequence hdim P hn).isFourfoldStepDiagram i).isKltPair_flipTransform
        (isKlt_stepSequence hdim hB P hn i)

end Program

private theorem solution : ∀ {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {K : Divisor X} {B : QDivisor X} (hdim : topologicalKrullDim X = 4)
    (hB : IsKltPair sX B) (P : Program sX K B), P.n ≠ ⊤ := by
  intro X sX _ _ _ _ K B hdim hB P hn
  obtain ⟨i, hi⟩ := (StepSequence.eventually_badLocusBaseAt_eq_bot_of_isKlt _
    (isKlt_stepSequence hdim hB P hn)).exists
  exact StepSequence.badLocusBaseAt_ne_bot (stepSequence hdim P hn) i
    (P.isPermittedStep i (hn ▸ ENat.coe_lt_top i)).relativePicardNumber_eq_one hi

end Proof_thm_oai4_klt_termination

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori

/-- **Termination for klt fourfolds.** Let `(X, B)` be a klt pair over `ℂ`, with `X` of
dimension four and `B` a `ℚ`-divisor, and `K` a canonical divisor. Every program `P` from
`(X, B)` (which in particular makes `X` projective) has finitely many birational steps:
`P.n ≠ ⊤`. -/
@[mmp "thm_oai4_klt_termination"]
public theorem Program.n_ne_top_of_isKltPair {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {K : Divisor X} {B : QDivisor X} (hdim : topologicalKrullDim X = 4)
    (hB : IsKltPair sX B) (P : Program sX K B) : P.n ≠ ⊤ :=
      by revert X sX K B hdim hB P; first | exact Proof_thm_oai4_klt_termination.solution | exact Proof_thm_oai4_klt_termination.solution _ | exact Proof_thm_oai4_klt_termination.solution _ _ | exact Proof_thm_oai4_klt_termination.solution _ _ _ | exact Proof_thm_oai4_klt_termination.solution _ _ _ _

end MMP.Fourfold

