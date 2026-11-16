module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Flip.Defs
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs

/-!
# Terminal pairs, extremal real flip sequences and nef weak models

A pair `(X, B)` is *terminal* if it is klt and every exceptional divisorial valuation has log
discrepancy `> 1`. An *extremal real flip sequence* from a normal `ℚ`-factorial complex threefold
`(X₀, B₀)` with real boundary is a sequence of diagrams `X_i ⟶ Z_i ⟵ X_{i+1}` of nontrivial small
projective birational contractions of relative Picard number one, with `-(K_{X_i} + B_i)` ample
over `Z_i` and `K_{X_{i+1}} + B_{i+1}` ample over `Z_i`, the `B_i` being the strict transforms of
`B₀`. A *nef weak model* of a pair `(Y, C)` over `S` is a birational contraction `φ : Y ⤏ Z` over
`S` with `K_Z + φ_* C` `ℝ`-Cartier and nef over `S` such that `p^*(K_Y + C) - q^*(K_Z + φ_* C)`
is effective and `q`-exceptional on a common projective resolution `p : W ⟶ Y`, `q : W ⟶ Z`.
Two nef models over `S` are *equivalent* if their pulled-back adjoints have the same zero-degree
curves over `S` on a common projective resolution.

## Main definitions

* `MMP.Fourfold.IsKltTerminalPair`, `MMP.Fourfold.IsTerminalVariety`: terminal pairs and
  terminal varieties.
* `MMP.Fourfold.IsRealFlipStep`, `MMP.Fourfold.RealFlipSequence`: extremal real flip sequences.
* `MMP.Fourfold.IsNefWeakModel`: nef weak models.
* `MMP.Fourfold.IsNefModelEquivalent`: equivalence of nef real models.

## Implementation notes

* The models of a real flip sequence are indexed as in `MMP.Fourfold.Program`: `X₀ = X`,
  `X_{i+1} = Y i`, with `n ∈ ℕ ∪ {∞}` steps; the data indexed by `i > n` (models) and `i ≥ n`
  (steps) are unconstrained. `B_{i+1} = (f_i⁺)⁻¹_* (f_i)_* B_i`, so that `B_i` is the strict
  transform of `B₀`; the `K_{X_i}` are any canonical divisors of the models. "Nontrivial" means
  that the contraction is not an isomorphism.
* In a nef weak model the canonical divisor of `Z` is `K_Z = φ_* K_Y`, so that `K_Y` and `K_Z`
  are cut out by one rational top form and the difference of the pulled-back adjoints is
  well defined (not only up to a principal divisor). The `ℝ`-Cartier pull-backs are
  `MMP.Flips.IsRCartierPullback`; a resolution is a smooth projective variety `W` with projective
  birational morphisms `p`, `q` such that `q = φ ∘ p`, that is, `q ∘ p⁻¹ = φ`.
* Nefness over `S` of an `ℝ`-Cartier `ℝ`-divisor is `MMP.Flips.IsRelativelyNef`, which records
  a presentation `∑ rⱼ Lⱼ` by Cartier divisors and so also that the divisor is `ℝ`-Cartier.
* The weak-model and equivalence notions are stated over any field `k`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Terminal pairs -/

section Terminal

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A pair `(X, B)` (`MMP.Fourfold.IsPair`) is *terminal* if it is klt and `a(v; X, B) > 1` for
every divisorial valuation `v` of `k(X)` exceptional over `X`, realized as an exceptional divisor
over `X`. -/
@[mmp "def_oai4_bg_terminal_pair"]
def IsKltTerminalPair (B : QDivisor X) : Prop :=
  IsKltPair sX B ∧ ∀ (n : ℕ) (E : DivisorOver k sX) (a : ℝ), E.IsExceptional →
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) E a → 1 < a

/-- A normal variety `X` with `K_X` `ℚ`-Cartier is *terminal* if the pair `(X, 0)` is terminal. -/
@[mmp "def_oai4_bg_terminal_pair"]
def IsTerminalVariety : Prop :=
  IsKltTerminalPair sX 0

end Terminal

/-! ### Extremal real flip sequences -/

section RealFlip

variable {X Z X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (sX' : X' ⟶ Spec (.of ℂ))

/-- A *step of an extremal real flip sequence* `(X, B) ⟶ Z ⟵ (X⁺, B⁺)`, with canonical divisors
`K`, `K⁺` and real boundaries `B`, `B⁺`: `Z` is a normal quasi-projective complex variety and
`f : X ⟶ Z`, `f⁺ : X⁺ ⟶ Z` are nontrivial (not isomorphisms) small projective birational
contractions (so `f_* 𝒪_X = f⁺_* 𝒪_{X⁺} = 𝒪_Z`) with `ρ(X/Z) = ρ(X⁺/Z) = 1`, `-(K + B)`
`f`-ample and `K⁺ + B⁺` `f⁺`-ample, where `B⁺ = (f⁺)⁻¹_* f_* B` is the strict transform of `B`
and `K⁺` is a canonical divisor of `X⁺`. -/
@[mmp "def_fourfold_real_flip_sequence"]
structure IsRealFlipStep (K : Divisor X) (B : RDivisor X) (K' : Divisor X') (B' : RDivisor X')
    (f : X ⟶ Z) (fp : X' ⟶ Z) : Prop where
  isQuasiProjectiveVariety_target : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sZ
  /-- `f` is a `(K + B)`-negative extremal contraction. -/
  isNegativeExtremalContraction :
    MMP.Flips.IsNegativeExtremalContraction ℂ sX sZ (MMP.Flips.logCanonicalDivisor K B) f
  isSmall : MMP.Flips.IsSmall ℂ sZ sX f
  isBirationalMorphism : IsBirationalMorphism f
  isProjectiveMorphism : IsProjectiveMorphism f
  not_isIso : ¬ IsIso f
  isCanonicalDivisor_flip : ∃ m : ℕ, K'.IsCanonicalDivisor sX' m
  isSmall_flip : MMP.Flips.IsSmall ℂ sZ sX' fp
  isBirationalMorphism_flip : IsBirationalMorphism fp
  isProjectiveMorphism_flip : IsProjectiveMorphism fp
  not_isIso_flip : ¬ IsIso fp
  relativePicardNumber_flip : MMP.Flips.relativePicardNumber sX' fp = 1
  isRelativelyAmple_flip : MMP.Flips.IsRelativelyAmple fp (MMP.Flips.logCanonicalDivisor K' B')
  eq_flipTransform : B' = flipTransform f fp B

/-- An *extremal real flip sequence* starting at `(X₀, B₀) = (X, B)`, a normal `ℚ`-factorial
complex threefold with canonical divisor `K` and real boundary `B`: a number `n ∈ ℕ ∪ {∞}` of
steps, models `X₀ = X`, `X_{i+1} = Y i` with canonical divisors `K_i` and real boundaries `B_i`,
`(K₀, B₀) = (K, B)`, such that every `X_i`, `i ≤ n`, is a `ℚ`-factorial normal quasi-projective
complex threefold and, for `i < n`, `X_i ⟶ Z_i ⟵ X_{i+1}` is a step of an extremal real flip
sequence (`MMP.Fourfold.IsRealFlipStep`); in particular `B_{i+1}` is the strict transform of
`B_i`, so that every `B_i` is the strict transform of `B₀`. -/
@[mmp "def_fourfold_real_flip_sequence"]
structure RealFlipSequence (K : Divisor X) (B : RDivisor X) where
  /-- The number of steps. -/
  n : ℕ∞
  /-- The models after the first: `X_{i+1} = Y i`. -/
  Y : ℕ → Scheme.{0}
  /-- The structure morphism of `X_{i+1}` to `Spec ℂ`. -/
  sY : ∀ i, Y i ⟶ Spec (.of ℂ)
  [isIntegral : ∀ i, IsIntegral (Y i)]
  [compactSpace : ∀ i, CompactSpace (Y i)]
  [isLocallyNoetherian : ∀ i, IsLocallyNoetherian (Y i)]
  [isNormal : ∀ i, IsNormal (Y i)]
  /-- The canonical divisor `K_{i+1}` of `X_{i+1}`. -/
  KY : ∀ i, Divisor (Y i)
  /-- The boundary `B_{i+1}` on `X_{i+1}`. -/
  BY : ∀ i, RDivisor (Y i)
  /-- The base `Z_i` of the `i`-th step. -/
  Z : ℕ → Scheme.{0}
  /-- The structure morphism of `Z_i` to `Spec ℂ`. -/
  sZ : ∀ i, Z i ⟶ Spec (.of ℂ)
  /-- The contraction `f_i : X_i ⟶ Z_i`. -/
  f : ∀ i, modelSeq X Y i ⟶ Z i
  /-- The contraction `f_i⁺ : X_{i+1} ⟶ Z_i`. -/
  fp : ∀ i, Y i ⟶ Z i
  isCanonicalDivisor : ∃ m : ℕ, K.IsCanonicalDivisor sX m
  isQFactorial : ∀ i : ℕ, (i : ℕ∞) ≤ n → IsQFactorial (modelStr sX sY i)
  isQuasiProjectiveVariety : ∀ i : ℕ, (i : ℕ∞) ≤ n →
    AlgebraicGeometry.IsQuasiProjectiveVariety ℂ (modelStr sX sY i)
  dim_eq : ∀ i : ℕ, (i : ℕ∞) ≤ n → topologicalKrullDim (modelSeq X Y i) = 3
  isRealFlipStep : ∀ i : ℕ, (i : ℕ∞) < n →
    IsRealFlipStep (modelStr sX sY i) (sZ i) (sY i) (divisorSeq K KY i) (divisorSeq B BY i)
      (KY i) (BY i) (f i) (fp i)

attribute [instance] RealFlipSequence.isIntegral RealFlipSequence.compactSpace
  RealFlipSequence.isLocallyNoetherian RealFlipSequence.isNormal

end RealFlip

/-! ### Nef weak models -/

section WeakModel

variable {k : Type u} [Field k] {Y Z S : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
  (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ] (sS : S ⟶ Spec (.of k))

/-- Let `(Y, C)` be a pair with real boundary `C` on a normal projective variety `Y` over `S`
(by `π_Y`), with canonical divisor `K_Y` and `K_Y + C` `ℝ`-Cartier. A birational map
`φ : Y ⤏ Z` over `S` (with `π_Z : Z ⟶ S`) is a *nef weak model* of `(Y, C)` if `Z` is a normal
projective variety, `φ` is a birational contraction (`φ⁻¹` contracts no prime divisor: no prime
divisor of `Z` is `φ⁻¹`-exceptional), `K_Z + C_Z` is `ℝ`-Cartier and nef over `S`, where
`C_Z = φ_* C` and `K_Z = φ_* K_Y`, and on a common projective resolution `p : W ⟶ Y`,
`q : W ⟶ Z` (`W` smooth projective, `p`, `q` projective birational, `q = φ ∘ p`) the divisor
`p^*(K_Y + C) - q^*(K_Z + C_Z)` is effective and `q`-exceptional. -/
@[mmp "def_fourfold_nef_weak_model"]
structure IsNefWeakModel (πY : Y ⟶ S) (πZ : Z ⟶ S) (KY : Divisor Y) (C : RDivisor Y)
    (φ : Y.RationalMap Z) : Prop where
  isNormalVariety_source : IsNormalVariety k sY
  isProjectiveVariety_source : MMP.Mori.IsProjectiveVariety k sY
  comp_eq_source : πY ≫ sS = sY
  isCanonicalDivisor : ∃ m : ℕ, KY.IsCanonicalDivisor sY m
  isCartierCombination : MMP.Flips.IsCartierCombination (MMP.Flips.logCanonicalDivisor KY C)
  isNormalVariety_target : IsNormalVariety k sZ
  isProjectiveVariety_target : MMP.Mori.IsProjectiveVariety k sZ
  comp_eq_target : πZ ≫ sS = sZ
  isBirational : MMP.Mori.RationalMap.IsBirational φ
  isOver : MMP.Flips.RationalMap.IsOver πY πZ φ
  not_isInverseExceptional : ∀ F : MMP.Mori.PrimeDivisor Z,
    ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F
  isRelativelyNef : MMP.Flips.IsRelativelyNef k sZ πZ
    (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ KY)
      (MMP.Mori.RationalMap.transformDivisor φ C))
  exists_resolution : ∃ (W : Scheme.{u}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
      (_ : IsNormal W) (sW : W ⟶ Spec (.of k)) (p : W ⟶ Y) (q : W ⟶ Z)
      (h : Y.RationalMap W),
    MMP.Mori.IsVariety k sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧ q ≫ sZ = sW ∧
      IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ IsBirationalMorphism p ∧
      IsBirationalMorphism q ∧ MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧
      h.compHom q = φ ∧
      ∃ GY GZ : RDivisor W,
        MMP.Flips.IsRCartierPullback p (MMP.Flips.logCanonicalDivisor KY C) GY ∧
        MMP.Flips.IsRCartierPullback q
          (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ KY)
            (MMP.Mori.RationalMap.transformDivisor φ C)) GZ ∧
        (∀ P, 0 ≤ (GY - GZ).coeff P) ∧
        ∀ P, (GY - GZ).coeff P ≠ 0 → MMP.Flips.IsExceptionalPrimeDivisor sZ q P

end WeakModel

/-! ### Equivalence of nef real models -/

section Equivalence

variable {k : Type u} [Field k] {Z₁ Z₂ S : Scheme.{u}} [IsIntegral Z₁] [IsLocallyNoetherian Z₁]
  [IsNormal Z₁] [IsIntegral Z₂] [IsLocallyNoetherian Z₂] [IsNormal Z₂]
  (s₁ : Z₁ ⟶ Spec (.of k)) (s₂ : Z₂ ⟶ Spec (.of k)) [QuasiCompact s₁] [QuasiCompact s₂]
  (sS : S ⟶ Spec (.of k))

/-- Let `(Z₁, C₁)` and `(Z₂, C₂)` be *nef real models over `S`*: normal projective varieties over
`S` (by `π₁`, `π₂`) with canonical divisors `K₁`, `K₂` and real boundaries `C₁`, `C₂` such that
`K_i + C_i` is `ℝ`-Cartier and nef over `S`, with the same function field through a birational
map `ψ : Z₁ ⤏ Z₂` over `S`. They are *equivalent* if on a common projective resolution
`p₁ : W ⟶ Z₁`, `p₂ : W ⟶ Z₂` (`W` smooth projective, `p_i` projective birational,
`p₂ = ψ ∘ p₁`) the pulled-back nef adjoints `D_i = p_i^*(K_i + C_i)` have exactly the same
zero-degree curves over `S`: an irreducible curve `Γ ⊆ W` mapping to a point of `S` has
`D₁ · Γ = 0` if and only if `D₂ · Γ = 0`. -/
@[mmp "def_fourfold_nef_model_equivalence"]
structure IsNefModelEquivalent (π₁ : Z₁ ⟶ S) (π₂ : Z₂ ⟶ S) (K₁ : Divisor Z₁) (C₁ : RDivisor Z₁)
    (K₂ : Divisor Z₂) (C₂ : RDivisor Z₂) (ψ : Z₁.RationalMap Z₂) : Prop where
  isNormalVariety₁ : IsNormalVariety k s₁
  isProjectiveVariety₁ : MMP.Mori.IsProjectiveVariety k s₁
  comp_eq₁ : π₁ ≫ sS = s₁
  isCanonicalDivisor₁ : ∃ m : ℕ, K₁.IsCanonicalDivisor s₁ m
  isRelativelyNef₁ : MMP.Flips.IsRelativelyNef k s₁ π₁ (MMP.Flips.logCanonicalDivisor K₁ C₁)
  isNormalVariety₂ : IsNormalVariety k s₂
  isProjectiveVariety₂ : MMP.Mori.IsProjectiveVariety k s₂
  comp_eq₂ : π₂ ≫ sS = s₂
  isCanonicalDivisor₂ : ∃ m : ℕ, K₂.IsCanonicalDivisor s₂ m
  isRelativelyNef₂ : MMP.Flips.IsRelativelyNef k s₂ π₂ (MMP.Flips.logCanonicalDivisor K₂ C₂)
  isBirational : MMP.Mori.RationalMap.IsBirational ψ
  isOver : MMP.Flips.RationalMap.IsOver π₁ π₂ ψ
  exists_resolution : ∃ (W : Scheme.{u}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
      (_ : IsNormal W) (sW : W ⟶ Spec (.of k)) (_ : QuasiCompact sW) (p₁ : W ⟶ Z₁)
      (p₂ : W ⟶ Z₂) (h : Z₁.RationalMap W),
    MMP.Mori.IsVariety k sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p₁ ≫ s₁ = sW ∧ p₂ ≫ s₂ = sW ∧
      IsProjectiveMorphism p₁ ∧ IsProjectiveMorphism p₂ ∧ IsBirationalMorphism p₁ ∧
      IsBirationalMorphism p₂ ∧ MMP.Mori.RationalMap.IsInverse p₁.toRationalMap h ∧
      h.compHom p₂ = ψ ∧
      ∃ D₁ D₂ : RDivisor W,
        MMP.Flips.IsRCartierPullback p₁ (MMP.Flips.logCanonicalDivisor K₁ C₁) D₁ ∧
        MMP.Flips.IsRCartierPullback p₂ (MMP.Flips.logCanonicalDivisor K₂ C₂) D₂ ∧
        ∀ Γ : ProperCurve sW, Γ.IsContractedBy (p₁ ≫ π₁) →
          ((∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor W) (x : ℝ),
              MMP.Flips.IsRIntersectionNumber k sW D₁ r L Γ x → x = 0) ↔
            ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor W) (x : ℝ),
              MMP.Flips.IsRIntersectionNumber k sW D₂ r L Γ x → x = 0)

end Equivalence

end MMP.Fourfold
