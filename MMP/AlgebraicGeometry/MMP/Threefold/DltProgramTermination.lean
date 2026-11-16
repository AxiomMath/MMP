module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
import MMP.AlgebraicGeometry.MMP.Threefold.DltFlipTermination

/-!
# Termination of projective elementary dlt programs of flips on threefolds

Let `π : X ⟶ S` be a morphism of projective complex varieties, with `X` a threefold, and let
`(X, B)` be a `ℚ`-factorial dlt pair with rational boundary. A projective elementary dlt program
from `(X, B)` over `S` whose birational transitions are all flips has finitely many steps.

## Main results

* `MMP.Fourfold.RelativeDltProgram.IsProjective.n_ne_top_of_isFlip`: a projective elementary dlt
  program of flips starting from a threefold is finite.

## Implementation notes

The program is a `MMP.Fourfold.RelativeDltProgram sX sS π K B`, so its starting model `(X, B)`
is already a `ℚ`-factorial dlt pair with rational boundary and `K` is a canonical divisor of `X`
(`RelativeDltProgram.isRelativeDltModel` at `0`). Projectivity of `S` and of all the models is
`RelativeDltProgram.IsProjective`. The phrase "consisting only of flips" means that the flip
alternative of `MMP.Fourfold.IsElementaryDltStep.divisorial_or_flip` holds at every step
`i < n`. Finiteness is `P.n ≠ ⊤`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Proof_thm_mmp_projective_threefold_flip_termination

attribute [local instance] AlgebraicGeometry.IsVariety.toIsIntegral
attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Fourfold MMP.Mori MMP.Flips

/-- Two morphisms `Z ⟶ Spec R` agreeing after `f : X ⟶ Z` agree, when `f` induces an isomorphism
`Γ(Z, 𝒪_Z) ≅ Γ(X, 𝒪_X)`: morphisms into an affine scheme are ring maps into global sections. -/
private theorem eq_of_comp_eq_of_isIso_appTop {X Z : Scheme.{0}} {R : CommRingCat.{0}}
    (f : X ⟶ Z) [IsIso f.appTop] {a b : Z ⟶ Spec R} (h : f ≫ a = f ≫ b) : a = b := by
  apply (ΓSpec.adjunction.homEquiv Z (Opposite.op R)).symm.injective
  have h' := congrArg (ΓSpec.adjunction.homEquiv X (Opposite.op R)).symm h
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_left_symm] at h'
  have : IsIso (Scheme.Γ.rightOp.map f) := by
    change IsIso (f.appTop).op
    infer_instance
  exact (cancel_epi _).mp h'

/-- The target of a contraction `f : X ⟶ Z` (structure morphism `sZ`) of a projective variety
`X`, which is projective over a projective variety `S` by `g` with `g ∘ f = π` and
`π : X ⟶ S` over `ℂ`, is a projective variety. -/
private theorem isProjectiveVariety_target {X Z S : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    {f : X ⟶ Z} {g : Z ⟶ S} {π : X ⟶ S} (hf : IsContraction ℂ sZ sX f)
    (hg : IsProjectiveMorphism g) (hfg : f ≫ g = π) (hπ : π ≫ sS = sX)
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) : MMP.Mori.IsProjectiveVariety ℂ sZ := by
  have : IsIso f.appTop := hf.isIso_app ⊤
  have hsZ : sZ = g ≫ sS :=
    eq_of_comp_eq_of_isIso_appTop f (by rw [hf.comp_eq, ← Category.assoc, hfg, hπ])
  rw [MMP.Mori.IsProjectiveVariety, isProjectiveVariety_iff_isProjective']
  refine ⟨hf.isVariety_target, ?_⟩
  rw [hsZ]
  exact IsProjective.comp hg.isProjective hS.isProjective.isProjective

variable {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {π : X ⟶ S} {K : Divisor X} {B : QDivisor X}

/-- The divisor `K + B` of a program step, written as a log canonical divisor. -/
private theorem toRDivisor_add_eq_logCanonicalDivisor {Y : Scheme.{0}} (K : Divisor Y)
    (B : QDivisor Y) :
    QDivisor.toRDivisor (Divisor.toQDivisor K + B) =
      logCanonicalDivisor K (QDivisor.toRDivisor B) := by
  rw [map_add, QDivisor.toRDivisor_toQDivisor, logCanonicalDivisor]

/-- In an infinite dlt program of flips from a threefold, every model is a threefold: a flip
preserves dimension through the two small contractions to `Z_i`. -/
private theorem topologicalKrullDim_modelSeq {P : RelativeDltProgram sX sS π K B}
    (hdim : topologicalKrullDim X = 3)
    (hflip : ∀ i : ℕ, IsFlip ℂ (modelStr sX P.sY i) (P.sZ i) (P.sY i)
      (QDivisor.toRDivisor (Divisor.toQDivisor (divisorSeq K P.KY i) + divisorSeq B P.BY i))
      (P.f i) (P.fp i) (P.φ i)) (i : ℕ) :
    topologicalKrullDim (modelSeq X P.Y i) = 3 := by
  induction i with
  | zero => exact hdim
  | succ i ih => exact (hflip i).isSmall.dim_eq.trans ((hflip i).isSmall_source.dim_eq.symm.trans ih)

/-- An infinite projective dlt program of flips from a threefold, as a sequence of flips. -/
private noncomputable def toSequenceOfFlips {P : RelativeDltProgram sX sS π K B}
    (hn : P.n = ⊤) (hdim : topologicalKrullDim X = 3)
    (hflip : ∀ i : ℕ, IsFlip ℂ (modelStr sX P.sY i) (P.sZ i) (P.sY i)
      (QDivisor.toRDivisor (Divisor.toQDivisor (divisorSeq K P.KY i) + divisorSeq B P.BY i))
      (P.f i) (P.fp i) (P.φ i)) :
    SequenceOfFlips sX 3 K B :=
  have hlt (i : ℕ) : (i : ℕ∞) < P.n := hn ▸ ENat.coe_lt_top i
  have hcan (i : ℕ) :
      Divisor.IsCanonicalDivisor (modelStr sX P.sY i) 3 (divisorSeq K P.KY i) := by
    obtain ⟨m, hm⟩ := (P.isRelativeDltModel i (hlt i).le).isCanonicalDivisor
    obtain rfl : m = 3 := by
      exact_mod_cast hm.topologicalKrullDim_eq.symm.trans (topologicalKrullDim_modelSeq hdim hflip i)
    exact hm
  { isNormalVariety := (hflip 0).isNormalVariety_source
    isCanonicalDivisor := ⟨inferInstance, inferInstance, hcan 0⟩
    isQCartier := ⟨inferInstance, inferInstance,
      (P.isElementaryDltStep 0 (hlt 0)).isNegativeRelativeRayContraction
        |>.isNegativeRelativeExtremalRayOf.1⟩
    length := ⊤
    one_le_length := le_top
    model := fun i => ⟨modelSeq X P.Y i, modelStr sX P.sY i, divisorSeq K P.KY i,
      divisorSeq B P.BY i⟩
    model_zero := rfl
    isNormalVariety_model := fun i _ => (hflip i).isNormalVariety_source
    isLocallyNoetherian_model := fun _ => inferInstance
    isNormal_model := fun _ => inferInstance
    compactSpace_model := fun _ => inferInstance
    isCanonicalDivisor_model := fun i _ => hcan i
    base := P.Z
    baseStr := P.sZ
    contraction := P.f
    flip := P.fp
    flipMap := P.φ
    isNegativeExtremalContraction := fun i _ => toRDivisor_add_eq_logCanonicalDivisor _ _ ▸
      (P.isElementaryDltStep i (hlt i)).isNegativeRelativeRayContraction.isNegativeExtremalContraction
    isSmall := fun i _ => (hflip i).isSmall_source
    isFlip := fun i _ => toRDivisor_add_eq_logCanonicalDivisor _ _ ▸ hflip i
    transform_eq := fun i _ => P.BY_eq i (hlt i) }

private theorem solution :
    ∀ {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {π : X ⟶ S} {K : Divisor X}
    {B : QDivisor X} {P : RelativeDltProgram sX sS π K B} (hP : P.IsProjective)
    (hdim : topologicalKrullDim X = 3)
    (hflip : ∀ i : ℕ, (i : ℕ∞) < P.n →
      IsFlip ℂ (modelStr sX P.sY i) (P.sZ i) (P.sY i)
        (QDivisor.toRDivisor (Divisor.toQDivisor (divisorSeq K P.KY i) + divisorSeq B P.BY i))
        (P.f i) (P.fp i) (P.φ i)),
    P.n ≠ ⊤ := by
  intro X S _ _ _ _ sX sS π K B P hP hdim hflip hn
  have hle (i : ℕ) : (i : ℕ∞) ≤ P.n := hn ▸ le_top
  have hX : MMP.Mori.IsProjectiveVariety ℂ sX := hP.2 0 (hle 0)
  have := hX.toIsVariety
  have h0 := P.isRelativeDltModel 0 (hle 0)
  refine lt_irrefl _ (SequenceOfFlips.terminates_of_isDltPair hX hdim h0.isQFactorial
    h0.isDltPair.1.2.1 h0.isDltPair
    (toSequenceOfFlips hn hdim fun i => hflip i (hn ▸ ENat.coe_lt_top i))
    (fun i _ => hP.2 i (hle i)) fun i _ => ?_)
  have hstep := (P.isElementaryDltStep i (hn ▸ ENat.coe_lt_top i)).isNegativeRelativeRayContraction
  exact isProjectiveVariety_target hstep.isNegativeExtremalContraction.isContraction
    hstep.isRelativeContractionOfFace.isProjectiveMorphism hstep.isRelativeContractionOfFace.comp_eq
    (P.isRelativeDltModel i (hle i)).comp_eq hP.1

end Proof_thm_mmp_projective_threefold_flip_termination

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Termination of projective threefold dlt flip programs.** Let `π : X ⟶ S` be a morphism of
projective complex varieties with `X` of dimension `3`, and let `P` be a projective elementary dlt
program from the `ℚ`-factorial dlt pair `(X, B)` over `S`. If every transition of `P` is a flip,
then `P` has finitely many steps. -/
@[mmp "thm_mmp_projective_threefold_flip_termination"]
public theorem RelativeDltProgram.IsProjective.n_ne_top_of_isFlip
    {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {π : X ⟶ S} {K : Divisor X}
    {B : QDivisor X} {P : RelativeDltProgram sX sS π K B} (hP : P.IsProjective)
    (hdim : topologicalKrullDim X = 3)
    (hflip : ∀ i : ℕ, (i : ℕ∞) < P.n →
      IsFlip ℂ (modelStr sX P.sY i) (P.sZ i) (P.sY i)
        (QDivisor.toRDivisor (Divisor.toQDivisor (divisorSeq K P.KY i) + divisorSeq B P.BY i))
        (P.f i) (P.fp i) (P.φ i)) :
    P.n ≠ ⊤ :=
      by revert X S sX sS π K B P hP hdim hflip; first | exact Proof_thm_mmp_projective_threefold_flip_termination.solution | exact Proof_thm_mmp_projective_threefold_flip_termination.solution _ | exact Proof_thm_mmp_projective_threefold_flip_termination.solution _ _ | exact Proof_thm_mmp_projective_threefold_flip_termination.solution _ _ _ | exact Proof_thm_mmp_projective_threefold_flip_termination.solution _ _ _ _

end MMP.Fourfold
