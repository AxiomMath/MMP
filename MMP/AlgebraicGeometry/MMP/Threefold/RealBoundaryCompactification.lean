module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.MMP.Threefold.RationalBirationalProgram
import MMP.AlgebraicGeometry.MMP.MinimalModel.RealKltCompactification

/-!
# Compactifying a real klt boundary on a threefold in a rational family

Let `T` be a normal affine complex variety and `f : S ⟶ T` a projective morphism, with `S` normal,
`ℚ`-factorial and of dimension three, and let `Θ` be an effective real boundary on `S` with
`(S, Θ)` klt. There are a normal projective compactification `j : T ⟶ T̄` and a projective
morphism `f̄ : S̄ ⟶ T̄` from a `ℚ`-factorial projective variety `S̄`, with an open immersion
`i : S ⟶ S̄` identifying `S` with `f̄⁻¹(T)`, such that the extension `Θ̄ = i_* Θ` of `Θ`, which
gives each closure `P̄` of a prime divisor `P` of `S` the coefficient of `P` and every prime
divisor of `S̄` outside `S` the coefficient zero, is an effective real klt boundary on `S̄`.

The extension `Φ ↦ i_* Φ` of real divisors is a coordinate embedding defined over `ℚ`, and it
carries the smallest rational affine hull of `Θ` onto the smallest rational affine hull of `Θ̄`.

## Main results

* `MMP.Fourfold.IsRealKltPair.exists_compactification_isInSmallestRationalAffineHull_iff`.

## Implementation notes

`S̄_T = S` is the cartesian square `IsPullback i f f̄ j`. The extension of a real divisor `Φ` on
`S` by closures of primes is `Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Φ`;
its restriction to `S` is again `Φ`, and its coefficient at a prime divisor of `S̄` not meeting
`S` is zero. The smallest rational affine hull is
`MMP.Fourfold.IsInSmallestRationalAffineHull`.

## References

* [OAI4] the fourfold source, *Compactifying a real klt boundary in a rational family*.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Fourfold MMP.Mori

namespace Proof_lem_fourfold_threefold_real_family_compactification

attribute [local instance] AlgebraicGeometry.IsVariety.toIsIntegral
attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

private theorem solution :
    ∀ {T : Scheme.{0}} [IsAffine T] {sT : T ⟶ Spec (.of ℂ)} (hT : IsNormalVariety ℂ sT)
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    {f : S ⟶ T} (hf : IsProjectiveMorphism f) (hSq : IsQFactorial (f ≫ sT))
    (hdim : topologicalKrullDim S = 3)
    {Θ : RDivisor S} (hΘ0 : ∀ P, 0 ≤ Θ.coeff P) (hΘ : IsRealKltPair (f ≫ sT) Θ),
    ∃ (Tbar : Scheme.{0}) (sTbar : Tbar ⟶ Spec (.of ℂ)) (j : T ⟶ Tbar) (_ : IsOpenImmersion j)
      (Sbar : Scheme.{0}) (_ : IsIntegral Sbar) (_ : IsLocallyNoetherian Sbar) (_ : IsNormal Sbar)
      (fbar : Sbar ⟶ Tbar) (i : S ⟶ Sbar) (_ : IsOpenImmersion i),
      IsNormalVariety ℂ sTbar ∧ MMP.Mori.IsProjectiveVariety ℂ sTbar ∧ j ≫ sTbar = sT ∧
      IsProjectiveMorphism fbar ∧ IsPullback i f fbar j ∧
      MMP.Mori.IsProjectiveVariety ℂ (fbar ≫ sTbar) ∧ IsQFactorial (fbar ≫ sTbar) ∧
      IsRealKltPair (fbar ≫ sTbar)
        (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Θ) ∧
      ∀ Φbar : RDivisor Sbar,
        IsInSmallestRationalAffineHull
            (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Θ) Φbar ↔
          ∃ Φ : RDivisor S, IsInSmallestRationalAffineHull Θ Φ ∧
            Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Φ = Φbar := by
  intro T _ sT hT S _ _ _ f hf hSq hdim Θ hΘ0 hΘ
  obtain ⟨Tbar, sTbar, ι, hTp, hTn, hι, hιs, Sbar, h1, h2, h3, sSbar, fbar, j, hj, hSp, hSbarQ,
    hfbar, hfbs, hpb, hk, hhull⟩ :=
    exists_realKltCompactification_of_rationalBirationalProgramProperty (d := 3) (by norm_num)
      rationalBirationalProgramProperty_three sT hT (f ≫ sT) hSq (by rw [hdim]; rfl) f rfl hf
      Θ hΘ0 hΘ
  subst hfbs
  exact ⟨Tbar, sTbar, ι, hι, Sbar, h1, h2, h3, fbar, j, hj, hTn, hTp, hιs, hfbar, hpb, hSp,
    hSbarQ, hk, fun Ψ => (hhull Ψ).trans (exists_congr fun Φ => and_congr_right fun _ => eq_comm)⟩

end Proof_lem_fourfold_threefold_real_family_compactification

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Compactifying a real klt boundary in a rational family.** Let `T` be a normal affine complex
variety, `f : S ⟶ T` a projective morphism with `S` normal, `ℚ`-factorial and of dimension three,
and `Θ` an effective real divisor on `S` with `(S, Θ)` klt. Then there are a normal projective
complex variety `T̄` with an open immersion `j : T ⟶ T̄` over `ℂ`, a projective morphism
`f̄ : S̄ ⟶ T̄` from a `ℚ`-factorial projective complex variety `S̄`, and an open immersion
`i : S ⟶ S̄` with `S = S̄ ×_{T̄} T`, such that, writing `i_* Φ` for the extension of a real divisor
`Φ` on `S` by the closures of its prime components (with coefficient zero on every other prime of
`S̄`), the pair `(S̄, i_* Θ)` is klt, and a real divisor on `S̄` lies in the smallest rational
affine hull of `i_* Θ` exactly when it is `i_* Φ` for some `Φ` in the smallest rational affine
hull of `Θ`. -/
@[mmp "lem_fourfold_threefold_real_family_compactification"]
public theorem IsRealKltPair.exists_compactification_isInSmallestRationalAffineHull_iff
    {T : Scheme.{0}} [IsAffine T] {sT : T ⟶ Spec (.of ℂ)} (hT : IsNormalVariety ℂ sT)
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    {f : S ⟶ T} (hf : IsProjectiveMorphism f) (hSq : IsQFactorial (f ≫ sT))
    (hdim : topologicalKrullDim S = 3)
    {Θ : RDivisor S} (hΘ0 : ∀ P, 0 ≤ Θ.coeff P) (hΘ : IsRealKltPair (f ≫ sT) Θ) :
    ∃ (Tbar : Scheme.{0}) (sTbar : Tbar ⟶ Spec (.of ℂ)) (j : T ⟶ Tbar) (_ : IsOpenImmersion j)
      (Sbar : Scheme.{0}) (_ : IsIntegral Sbar) (_ : IsLocallyNoetherian Sbar) (_ : IsNormal Sbar)
      (fbar : Sbar ⟶ Tbar) (i : S ⟶ Sbar) (_ : IsOpenImmersion i),
      IsNormalVariety ℂ sTbar ∧ MMP.Mori.IsProjectiveVariety ℂ sTbar ∧ j ≫ sTbar = sT ∧
      IsProjectiveMorphism fbar ∧ IsPullback i f fbar j ∧
      MMP.Mori.IsProjectiveVariety ℂ (fbar ≫ sTbar) ∧ IsQFactorial (fbar ≫ sTbar) ∧
      IsRealKltPair (fbar ≫ sTbar)
        (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Θ) ∧
      ∀ Φbar : RDivisor Sbar,
        IsInSmallestRationalAffineHull
            (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Θ) Φbar ↔
          ∃ Φ : RDivisor S, IsInSmallestRationalAffineHull Θ Φ ∧
            Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap i) Φ = Φbar :=
              by revert T sT hT S f hf hSq hdim Θ hΘ0 hΘ; first | exact Proof_lem_fourfold_threefold_real_family_compactification.solution | exact Proof_lem_fourfold_threefold_real_family_compactification.solution _ | exact Proof_lem_fourfold_threefold_real_family_compactification.solution _ _ | exact Proof_lem_fourfold_threefold_real_family_compactification.solution _ _ _ | exact Proof_lem_fourfold_threefold_real_family_compactification.solution _ _ _ _

end MMP.Fourfold
