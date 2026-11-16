module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
public import MMP.AlgebraicGeometry.MMP.Abundance.FiniteRepresentationGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.Preadmissible.StratumRestrictionsFixed
public import MMP.AlgebraicGeometry.MMP.Abundance.PreadmissibleCrepantActionFinite
public import MMP.AlgebraicGeometry.MMP.Abundance.PreadmissibleGenerationSurface

/-!
# Admissible generation for semiample dlt surface collections

Let `(S_i, B_i)`, `i ∈ I`, be a finite collection of `ℚ`-factorial projective dlt pairs on
complex surfaces whose adjoints `K_{S_i} + B_i` are semiample. Then there is `m₀ > 0` such that
in every even degree `m` divisible by `m₀` the admissible section systems
`(s_i) ∈ ⊕ᵢ H⁰(S_i, m(K_{S_i} + B_i))` generate every `𝒪_{S_i}(m(K_{S_i} + B_i))`. A system is
admissible when its residue restrictions to all strata, including the whole surfaces, correspond
under every crepant birational map between their adjunction pairs. Generation means that at every
point `x` of every `S_i` some admissible system has its `i`-th section nonvanishing at `x`.

## Main results

* `MMP.Fourfold.exists_generatesOn_of_mem_admissibleSections`: admissible generation in all
  sufficiently divisible even degrees.

## Implementation notes

"Rational pair" is `MMP.Fourfold.IsPair`, "dlt" is `MMP.Intersection.IsDltPair`,
"rational-factorial" is `MMP.Fourfold.IsQFactorial`. Semiampleness of the adjoint is
`MMP.Fourfold.QDivisor.IsRelativelySemiample` over `Spec ℂ` of `K_{S_i} + B_i`, where `K_{S_i}`
is a canonical divisor. The admissible systems are `MMP.Fourfold.admissibleSections` of any
residue restriction structure `MMP.Fourfold.ResidueRestriction` on the collection in degree `m`.
Local generation is `MMP.Mori.GeneratesOn` on an open neighbourhood.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP MMP.Fourfold
open MMP.Mori

namespace Proof_thm_fourfold_semiample_surface_admissible_systems_generate

private theorem solution
    {I : Type*} [Finite I] {S : I → Scheme.{0}} [∀ i, IsIntegral (S i)]
    [∀ i, CompactSpace (S i)] [∀ i, IsLocallyNoetherian (S i)] [∀ i, IsNormal (S i)]
    {sS : ∀ i, S i ⟶ Spec (.of ℂ)} (hS : ∀ i, Mori.IsProjectiveVariety ℂ (sS i))
    (hdim : ∀ i, topologicalKrullDim (S i) = 2) (hQ : ∀ i, IsQFactorial (sS i))
    {B : ∀ i, QDivisor (S i)} (hB : ∀ i, MMP.Fourfold.IsPair (sS i) (B i))
    (hdlt : ∀ i, MMP.Intersection.IsDltPair (sS i) (B i)) {K : ∀ i, Divisor (S i)}
    (hK : ∀ i, (K i).IsCanonicalDivisor (sS i) 2)
    (hsemi : ∀ i, QDivisor.IsRelativelySemiample (sS i) (Divisor.toQDivisor (K i) + B i)) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, m₀ ∣ m → Even m →
      ∀ (R : ResidueRestriction sS B 2 m) (i : I) (x : S i),
        ∃ s ∈ admissibleSections R, ∃ V : (S i).Opens, x ∈ V ∧
          GeneratesOn (B i) m V
            ((s i : logPluricanonicalSections (sS i) 2 m (B i)) :
              RationalPluriForms (sS i) 2 m) := by
  obtain ⟨m₁, hm₁, hgen⟩ :=
    exists_generatesOn_of_mem_preadmissibleSections hS hdim hQ hB hdlt hK hsemi
  obtain ⟨m₂, hm₂, hfix⟩ :=
    exists_preadmissibleSections_update_pluriformPullback_of_isCrepantBirationalMap
      (k := ℂ) (sX := sS) B (n := 2) (by norm_num)
  obtain ⟨m₃, hm₃, hfin⟩ :=
    exists_finite_range_pluriformPullback_preadmissibleSections hK hsemi
  -- a common even degree `M = 2 m₁ m₂ m₃` in which all three results apply
  set M := 2 * (m₁ * m₂ * m₃)
  have hM₂ : m₂ ∣ M := ⟨2 * m₁ * m₃, by ring⟩
  obtain ⟨⟨R₀⟩, hgen₀⟩ := hgen M (by positivity) ⟨2 * m₂ * m₃, by ring⟩ (even_two_mul _)
  obtain ⟨N, hN, hadm⟩ := (exists_admissibleSections_generatesOn_mul_of_finite R₀ (hgen₀ R₀)
    (hfix M hM₂ R₀).1 (hfix M hM₂ R₀).2 (hfin M ⟨2 * m₁ * m₂, by ring⟩ R₀).1).1
  refine ⟨N * M, Nat.mul_pos hN (by positivity), fun m hm _ R i x => ?_⟩
  obtain ⟨c, rfl⟩ : ∃ c, m = c * (N * M) := ⟨m / (N * M), (Nat.div_mul_cancel hm).symm⟩
  exact hadm c (Nat.pos_of_mul_pos_right R.setting.pos) R i x

end Proof_thm_fourfold_semiample_surface_admissible_systems_generate

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Admissible generation for semiample dlt surfaces.** Let `(S_i, B_i)`, `i ∈ I` finite, be
`ℚ`-factorial projective dlt pairs (`MMP.Fourfold.IsPair`, `MMP.Intersection.IsDltPair`) on
complex surfaces. Let `K_i` be canonical divisors such that `K_i + B_i` is semiample. Then there
is `m₀ > 0` with the following property. For every even `m` divisible by `m₀`, every residue
restriction structure `R` on the collection in degree `m`, every `i` and every point `x ∈ S_i`,
there is an admissible section system `s ∈ admissibleSections R` whose `i`-th section generates
`𝒪_{S_i}(m(K_{S_i} + B_i))` on an open neighbourhood of `x`. -/
@[mmp "thm_fourfold_semiample_surface_admissible_systems_generate"]
public theorem exists_generatesOn_of_mem_admissibleSections
    {I : Type*} [Finite I] {S : I → Scheme.{0}} [∀ i, IsIntegral (S i)]
    [∀ i, CompactSpace (S i)] [∀ i, IsLocallyNoetherian (S i)] [∀ i, IsNormal (S i)]
    {sS : ∀ i, S i ⟶ Spec (.of ℂ)} (hS : ∀ i, Mori.IsProjectiveVariety ℂ (sS i))
    (hdim : ∀ i, topologicalKrullDim (S i) = 2) (hQ : ∀ i, IsQFactorial (sS i))
    {B : ∀ i, QDivisor (S i)} (hB : ∀ i, IsPair (sS i) (B i))
    (hdlt : ∀ i, MMP.Intersection.IsDltPair (sS i) (B i)) {K : ∀ i, Divisor (S i)}
    (hK : ∀ i, (K i).IsCanonicalDivisor (sS i) 2)
    (hsemi : ∀ i, QDivisor.IsRelativelySemiample (sS i) (Divisor.toQDivisor (K i) + B i)) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, m₀ ∣ m → Even m →
      ∀ (R : ResidueRestriction sS B 2 m) (i : I) (x : S i),
        ∃ s ∈ admissibleSections R, ∃ V : (S i).Opens, x ∈ V ∧
          GeneratesOn (B i) m V
            ((s i : logPluricanonicalSections (sS i) 2 m (B i)) :
              RationalPluriForms (sS i) 2 m) :=
                by revert I S sS hS hdim hQ B hB hdlt K hK hsemi; first | exact Proof_thm_fourfold_semiample_surface_admissible_systems_generate.solution | exact Proof_thm_fourfold_semiample_surface_admissible_systems_generate.solution _ | exact Proof_thm_fourfold_semiample_surface_admissible_systems_generate.solution _ _ | exact Proof_thm_fourfold_semiample_surface_admissible_systems_generate.solution _ _ _ | exact Proof_thm_fourfold_semiample_surface_admissible_systems_generate.solution _ _ _ _

end MMP.Fourfold

