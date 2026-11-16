module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepSequence

/-!
# Bad branch counts of fourfold step diagrams

Let `Y⁻ → Z ← Y⁺` (by `f^±`) be a step diagram of fourfolds in which both morphisms are small,
with full bad loci `W^± = (f^±)⁻¹(Σ) ⊆ Y^±`. A prime divisor `S⁻` of `Y⁻` has a strict transform
`S⁺ = (f⁺)⁻¹_* f⁻_* S⁻` on `Y⁺`; with `ν^± : (S^±)^ν ⟶ S^± ⊆ Y^±` the normalizations, the
*bad branch count* `e^ε(S⁻)`, for a sign `ε ∈ {-, +}`, is the number of prime divisors `P` of
`(S^ε)^ν` with `ν^ε(P) ⊆ W^ε`.

## Main definitions

* `MMP.Fourfold.IsFourfoldBadBranchCountMinus`, `MMP.Fourfold.IsFourfoldBadBranchCountPlus`:
  `e = e^-(S⁻)` and `e = e^+(S⁻)` for a fourfold step diagram with both maps small.

## Main results

* `MMP.Fourfold.IsFourfoldBadBranchCountMinus.eq`, `MMP.Fourfold.IsFourfoldBadBranchCountPlus.eq`:
  the bad branch counts are unique.

## Implementation notes

* The two signs are two predicates on the value `e`, which also contain the hypotheses of the
  source: the step diagram `MMP.Fourfold.IsFourfoldStepDiagram` (whose positive morphism is
  small) and the smallness of the negative morphism. The count itself is
  `MMP.Fourfold.badBranchCount`, the `Set.ncard` of the prime divisors of the normalization
  `MMP.Fourfold.primeDivisorNormalization` whose support has image in the given subset (`0` on an
  infinite set); the image `ν(P)` of a prime divisor `P` is the image of its support.
* The strict transform `S⁺` is `MMP.Fourfold.flipTransformPrimeDivisor`, which is `none` when one
  of the two transforms is not a prime divisor. The source asserts that `S⁺` exists when both maps
  are small; `e^+` is stated for a strict transform `S⁺` which exists, so that
  `IsFourfoldBadBranchCountPlus` also asserts this existence.
* The bad loci are the closed sets `MMP.Fourfold.badLocusMinus` and `MMP.Fourfold.badLocusPlus`;
  the condition `ν(P) ⊆ W` only depends on the underlying set of the reduced subscheme.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

section FourfoldBadBranchCount

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- `e` is the *bad branch count* `e^-(S⁻)` of a prime divisor `S⁻` of `Y⁻`, for a fourfold step
diagram `Y⁻ → Z ← Y⁺` (by `f^±`, canonical divisor `K` and boundary `B` of `Y⁻`) in which both
morphisms are small, with full bad loci `W^±`: the number of prime divisors `P` of the
normalization `(S⁻)^ν` with `ν⁻(P) ⊆ W⁻`. -/
@[mmp "def_oai4_bad_branch_count"]
def IsFourfoldBadBranchCountMinus (sXm : Xm ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    (sXp : Xp ⟶ Spec (.of ℂ)) (K : Divisor Xm) (B : QDivisor Xm) (fm : Xm ⟶ Z) (fp : Xp ⟶ Z)
    (S : MMP.Mori.PrimeDivisor Xm) (e : ℕ) : Prop :=
  IsFourfoldStepDiagram sXm sZ sXp K B fm fp ∧ IsSmallMorphism sXm sZ fm ∧
    e = badBranchCount S (badLocusMinus fm fp)

/-- `e` is the *bad branch count* `e^+(S⁻)` of a prime divisor `S⁻` of `Y⁻`, for a fourfold step
diagram `Y⁻ → Z ← Y⁺` (by `f^±`, canonical divisor `K` and boundary `B` of `Y⁻`) in which both
morphisms are small, with full bad loci `W^±`: the strict transform `S⁺ = (f⁺)⁻¹_* f⁻_* S⁻` is a
prime divisor of `Y⁺`, and `e` is the number of prime divisors `P` of its normalization `(S⁺)^ν`
with `ν⁺(P) ⊆ W⁺`. -/
@[mmp "def_oai4_bad_branch_count"]
def IsFourfoldBadBranchCountPlus (sXm : Xm ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    (sXp : Xp ⟶ Spec (.of ℂ)) (K : Divisor Xm) (B : QDivisor Xm) (fm : Xm ⟶ Z) (fp : Xp ⟶ Z)
    (S : MMP.Mori.PrimeDivisor Xm) (e : ℕ) : Prop :=
  IsFourfoldStepDiagram sXm sZ sXp K B fm fp ∧ IsSmallMorphism sXm sZ fm ∧
    ∃ S' : MMP.Mori.PrimeDivisor Xp, flipTransformPrimeDivisor fm fp S = some S' ∧
      e = badBranchCount S' (badLocusPlus fm fp)

variable {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {S : MMP.Mori.PrimeDivisor Xm}

omit [IsIntegral Xm] [IsIntegral Xp] in
/-- The bad branch count `e^-(S⁻)` is unique. -/
theorem IsFourfoldBadBranchCountMinus.eq {e e' : ℕ}
    (h : IsFourfoldBadBranchCountMinus sXm sZ sXp K B fm fp S e)
    (h' : IsFourfoldBadBranchCountMinus sXm sZ sXp K B fm fp S e') : e = e' :=
  h.2.2.trans h'.2.2.symm

omit [IsIntegral Xm] [IsIntegral Xp] in
/-- The bad branch count `e^+(S⁻)` is unique. -/
theorem IsFourfoldBadBranchCountPlus.eq {e e' : ℕ}
    (h : IsFourfoldBadBranchCountPlus sXm sZ sXp K B fm fp S e)
    (h' : IsFourfoldBadBranchCountPlus sXm sZ sXp K B fm fp S e') : e = e' := by
  obtain ⟨-, -, S₁, h₁, rfl⟩ := h
  obtain ⟨-, -, S₂, h₂, rfl⟩ := h'
  cases h₁.symm.trans h₂
  rfl

omit [IsIntegral Xm] [IsIntegral Xp] in
/-- In a fourfold step diagram with `f⁻` small, `e^-(S⁻)` is the bad branch count of `S⁻` along
`W⁻`. -/
theorem isFourfoldBadBranchCountMinus_badBranchCount
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (hm : IsSmallMorphism sXm sZ fm) :
    IsFourfoldBadBranchCountMinus sXm sZ sXp K B fm fp S
      (badBranchCount S (badLocusMinus fm fp)) :=
  ⟨h, hm, rfl⟩

omit [IsIntegral Xm] [IsIntegral Xp] in
/-- In a fourfold step diagram with `f⁻` small, if the strict transform of `S⁻` is the prime
divisor `S⁺`, then `e^+(S⁻)` is the bad branch count of `S⁺` along `W⁺`. -/
theorem isFourfoldBadBranchCountPlus_badBranchCount
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (hm : IsSmallMorphism sXm sZ fm)
    {S' : MMP.Mori.PrimeDivisor Xp} (hS : flipTransformPrimeDivisor fm fp S = some S') :
    IsFourfoldBadBranchCountPlus sXm sZ sXp K B fm fp S
      (badBranchCount S' (badLocusPlus fm fp)) :=
  ⟨h, hm, S', hS, rfl⟩

end FourfoldBadBranchCount

end MMP.Fourfold
