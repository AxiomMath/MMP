module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupEmbedded

/-!
# Blow-up sequences of constant multiplicity (Kollár 1.10)

Let `S₀` be a two-dimensional regular Noetherian scheme, `C₀ ⊆ S₀` a reduced curve, `p₀ ∈ C₀` a
closed point and `m ≥ 2`. A *blow-up sequence of multiplicity `m`* of length `k ∈ ℕ ∪ {∞}`
starting at `p₀` is a sequence `(p₀ ∈ C₀ ⊆ S₀) ← (p₁ ∈ C₁ ⊆ S₁) ← ⋯` of `k + 1` terms such that
`mult_{p_i} C_i = m` for all `i`, `S_{i+1} = B_{p_i} S_i` with `C_{i+1}` the birational transform
of `C_i`, and `p_{i+1}` is the unique singular point of `C_{i+1}` lying over `p_i`.

## Main definitions

* `MMP.Resolution.PointBlowupSequence.IsConstantMultiplicity`: a sequence of point blow-ups is a
  blow-up sequence of multiplicity `m` for `C₀`.

## Implementation notes

The sequence is a `MMP.Resolution.PointBlowupSequence` of length `k`, whose terms `C_i` are the
successive birational transforms `MMP.Resolution.PointBlowupSequence.transformedSubscheme`; its
`k + 1` points are `p_0, …, p_k` (all `p_i` when `k = ∞`). A point `q` of `C_i` is singular when
`𝒪_{C_i,q}` is not a regular local ring. The standing hypotheses on `S₀`, `C₀` and `m` are not
needed to state the definition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Resolution.PointBlowupSequence

variable {S₀ : Scheme.{u}} (s : PointBlowupSequence S₀)

/-- A point `q` of `S_i` is a *singular point* of the `i`-th birational transform `C_i` of `C₀`:
`q ∈ C_i` and `𝒪_{C_i,q}` is not a regular local ring. -/
def IsSingularPointOfTransform (C₀ : S₀.IdealSheafData) (i : ℕ) (q : s.S i) : Prop :=
  q ∈ (s.transformedSubscheme C₀ i).support ∧
    ¬ IsRegularLocalRing ((s.S i).presheaf.stalk q ⧸
      IdealSheafData.stalk (s.transformedSubscheme C₀ i) q)

/-- The sequence of point blow-ups `s` of length `k` is a *blow-up sequence of multiplicity `m`*
for `C₀ ⊆ S₀` starting at `p_0` (Kollár 1.10): (1) `mult_{p_i} C_i = m` for every `i ≤ k`;
(2) `C_{i+1}` is the birational transform of `C_i` in `S_{i+1} = B_{p_i} S_i` (built into
`transformedSubscheme`); (3) for `i < k`, `p_{i+1}` lies over `p_i` and is the unique singular
closed point of `C_{i+1}` lying over `p_i`. -/
@[mmp "def_kr1c_constant_multiplicity_blowup_sequence"]
def IsConstantMultiplicity (C₀ : S₀.IdealSheafData) (m : ℕ) : Prop :=
  (∀ i : ℕ, (i : ℕ∞) ≤ s.length →
      multAt (s.transformedSubscheme C₀ i) (s.p i) = m) ∧
    ∀ (i : ℕ) (hi : (i : ℕ∞) < s.length),
      (s.σ i hi).base (s.p (i + 1)) = s.p i ∧
        s.IsSingularPointOfTransform C₀ (i + 1) (s.p (i + 1)) ∧
        ∀ q : s.S (i + 1), IsClosed ({q} : Set (s.S (i + 1))) →
          (s.σ i hi).base q = s.p i → s.IsSingularPointOfTransform C₀ (i + 1) q →
            q = s.p (i + 1)

end MMP.Resolution.PointBlowupSequence
